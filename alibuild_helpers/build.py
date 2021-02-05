"""This module contains the actual build logic."""

import os
import re
import shutil
import socket
import sys
import time

from collections import deque
from datetime import datetime
from glob import glob
from itertools import chain
from os.path import abspath, exists, basename, dirname, join, realpath
try:
  from collections import OrderedDict
except ImportError:
  from ordereddict import OrderedDict
try:
  from commands import getstatusoutput
except ImportError:
  from subprocess import getstatusoutput

import yaml

from alibuild_helpers.analytics import report_event
from alibuild_helpers.cmd import execute, getStatusOutputBash, BASH
from alibuild_helpers.log import (
  debug, error, info, banner, warning,
  dieOnError, logger_handler, LogFormatter, ProgressPrint,
)
from alibuild_helpers.utilities import (
  prunePaths, format, dockerStatusOutput, parseDefaults, readDefaults,
  getPackageList, validateDefaults, Hasher, yamlDump,
)
from alibuild_helpers.git import partialCloneFilter
from alibuild_helpers.sync import chooseRemoteStore
from alibuild_helpers.workarea import updateReferenceRepoSpec


def star():
  """Return the name prefix of this program."""
  return re.sub("build.*$", "", basename(sys.argv[0]).lower())


def gzip():
  """Return gzip executable to use."""
  err, _ = getstatusoutput("which pigz")
  return "gzip" if err else "pigz"


def tar():
  """Return tar command prefix to use."""
  err, _ = getstatusoutput("tar --ignore-failed-read -cvvf /dev/null /dev/zero")
  return "tar" if err else "tar --ignore-failed-read"


def ignoreOSError(func, *args):
  """Call func with args, swallowing any OSError."""
  try:
    return func(*args)
  except OSError:
    pass


def writeAll(filename, txt):
  """Write txt to a file with the given name."""
  openf = open(filename, "w")
  openf.write(txt)
  openf.close()


def readHashFile(filename):
  """Read the hash from the given file, stripping newlines."""
  try:
    openf = open(filename)
    out = openf.read().strip("\n")
    openf.close()
    return out
  except IOError:
    return "0"


def getDirectoryHash(directory):
  """Get the git hash for the directory if possible, else alibuild's hash."""
  err, out = getstatusoutput(
    "GIT_DIR=%s/.git git rev-parse HEAD" % directory
    if exists(join(directory, ".git")) else
    "pip --disable-pip-version-check show alibuild | "
    "sed -n '/^Version:/s/.* //p'")
  dieOnError(err, "Impossible to find reference for %s" % directory)
  return out


def createDistLinks(spec, specs, args, repoType, requiresType):
  """Create symlinks to the package and its dependencies in the store."""
  target = format("TARS/%(a)s/%(rp)s/%(p)s/%(p)s-%(v)s-%(r)s",
                  a=args.architecture,
                  rp=repoType,
                  p=spec["package"],
                  v=spec["version"],
                  r=spec["revision"])
  shutil.rmtree(target, True)
  links = [
    format("ln -sfn ../../../../../TARS/%(a)s/store/%(sh)s/%(h)s/%(p)s-%(v)s-%(r)s.%(a)s.tar.gz %(target)s",
           target=target,
           a=args.architecture,
           sh=specs[x]["hash"][0:2],
           h=specs[x]["hash"],
           p=specs[x]["package"],
           v=specs[x]["version"],
           r=specs[x]["revision"])
    for x in [spec["package"]] + list(spec[requiresType])
  ]
  # We do it in chunks to avoid hitting shell limits but still do more than one
  # symlink at the time, to save the forking cost.
  baseCmd = "cd %s && mkdir -p %s &&" % (args.workDir, target)
  for i in range(0, len(links), 10):
    execute(baseCmd + " && ".join(links[i:i+10]))

  if args.writeStore.startswith("s3://"):
    execute(format(
      r"""
      cd %(w)s || exit 1
      find %(t)s -type l | while read -r x; do
        hashedurl=$(readlink $x | sed -e 's|.*/\.\./TARS|TARS|') || continue
        echo $hashedurl |
          s3cmd put --skip-existing -q -P -s \
                --add-header="x-amz-website-redirect-location:https://s3.cern.ch/swift/v1/%(b)s/$hashedurl" \
                --host s3.cern.ch --host-bucket %(b)s.s3.cern.ch - s3://%(b)s/$x 2>/dev/null
      done
      """, w=args.workDir, t=target, b=re.sub("^s3://", "", args.writeStore)))
  elif args.writeStore:
    execute("cd %s && rsync -avR --ignore-existing %s/ %s/" %
            (args.workDir, target, args.writeStore))


def dockerRunner(dockerImage):
  """Return a function that runs a command in the given Docker image."""
  def runInDocker(_, cmd):
    return dockerStatusOutput(cmd, dockerImage, executor=getStatusOutputBash)
  return runInDocker


def createBuildOrder(specs):
  """Sort packages into the order they should be built in.

  Do topological sort to have the correct build order, even in the case of
  non-tree like dependencies.

  The actual algorithm used can be found at:
  http://www.stoimen.com/blog/2012/10/01/computer-algorithms-topological-sort-of-a-graph/
  """
  # A list of (package, dependency) pairs mapping a package to its dependency.
  # One pair per dependency relation.
  edges = [(spec["package"], dep)
           for spec in specs.values()
           for dep in spec["requires"]]
  # Start with "leaf" packages, i.e. those without dependencies.
  queue = deque(spec for spec in specs.values() if not spec["requires"])
  # Go through all the packages, scheduling dependencies to be built before the
  # packages that depend on them.
  while queue:
    # Schedule the next package for building. All its dependencies (if any)
    # have already been scheduled.
    spec = queue.popleft()
    yield spec["package"]
    # Find all the packages that depend on the one we've just scheduled for
    # building.
    nextVertex = {pkg for pkg, dep in edges if dep == spec["package"]}
    # Keep the dependency relations that don't involve the package we've just
    # scheduled for building.
    edges = [(pkg, dep) for pkg, dep in edges if dep != spec["package"]]
    # Remove those packages that depend on something we haven't built yet.
    nextVertex -= {pkg for pkg, _ in edges if pkg in nextVertex}
    # Queue packages whose dependencies have all been scheduled already.
    queue.extend(specs[m] for m in nextVertex)


class ExternalCommandError(Exception):
  """An external command indicated an error."""


def getCommitRef(spec, develPkgs, args, nowKwds):
  """Resolve the tag to the actual commit ref."""
  spec["commit_hash"] = "0"

  if "source" not in spec:
    return ""

  def cmdInRepo(spec, cmd):
    return "cd %s && %s" % (spec["source"], cmd)

  develPackageBranch = ""
  # Tag may contain date params like %(year)s, %(month)s, %(day)s, %(hour).
  spec["tag"] %= nowKwds
  # By default we assume tag is a commit hash. We then try to find out if
  # the tag is actually a branch and we use the tip of the branch as
  # commit_hash. Finally if the package is a development one, we use the
  # name of the branch as commit_hash.
  spec["commit_hash"] = spec["tag"]

  for head in spec["git_heads"]:
    if not head.endswith("refs/heads/" + spec["tag"]) and \
       spec["package"] not in develPkgs:
      continue

    spec["commit_hash"] = head.split("\t", 1)[0]
    # We are in development mode, we need to rebuild if the commit hash is
    # different, and if there are extra changes on top.
    if spec["package"] in develPkgs:
      # Development package: we get the commit hash from the checked source,
      # not from the remote.
      err, out = getstatusoutput(cmdInRepo(spec, "git rev-parse HEAD"))
      dieOnError(err, "Unable to detect current commit hash.")
      spec["commit_hash"] = out.strip()
      cmd = cmdInRepo(spec, "git diff -r HEAD && git status --porcelain")
      gitStatusHasher = Hasher()
      err = execute(cmd, gitStatusHasher)
      debug("Got %d from %s", err, cmd)
      dieOnError(err, "Unable to detect source code changes.")
      spec["devel_hash"] = spec["commit_hash"] + gitStatusHasher.hexdigest()
      err, out = \
        getstatusoutput(cmdInRepo(spec, "git rev-parse --abbrev-ref HEAD"))
      if out == "HEAD":
        err, out = getstatusoutput(cmdInRepo(spec, "git rev-parse HEAD"))
        out = out[0:10]
      if err:
        raise ExternalCommandError()
      develPackageBranch = out.replace("/", "-")
      spec["tag"] = getattr(args, "develPrefix", develPackageBranch)
      spec["commit_hash"] = "0"
    break

  # Version may contain date params like tag, plus %(commit_hash)s,
  # %(short_hash)s and %(tag)s.
  defaultsUpper = ("_" + args.defaults.upper().replace("-", "_")
                   if args.defaults != "release" else "")
  spec["version"] = format(spec["version"],
                           commit_hash=spec["commit_hash"],
                           short_hash=spec["commit_hash"][0:10],
                           tag=spec["tag"],
                           tag_basename=basename(spec["tag"]),
                           defaults_upper=defaultsUpper,
                           **nowKwds)

  if spec["package"] in develPkgs and "develPrefix" in args and \
     args.develPrefix != "ali-master":
    spec["version"] = args.develPrefix

  return develPackageBranch


def calculateHashes(pkg, specs, develPkgs, architecture):
  """Calculate package and dependency hashes."""
  spec = specs[pkg]
  pkgHasher = Hasher()
  depHasher = Hasher()
  for key in ("recipe", "version", "package", "commit_hash",
              "env", "append_path", "prepend_path"):
    if sys.version_info[0] < 3 and isinstance(spec.get(key), OrderedDict):
      # Python 2: use YAML dict order to prevent changing hashes
      pkgHasher(str(yaml.safe_load(yamlDump(spec[key]))))
    else:
      pkgHasher(str(spec.get(key, "none")))
  # If the commit hash is a real hash, and not a tag, we can safely assume
  # that's unique, and therefore we can avoid putting the repository or the
  # name of the branch in the hash.
  if spec["commit_hash"] == spec.get("tag", "0"):
    pkgHasher(spec.get("source", "none"))
    if "source" in spec:
      pkgHasher(spec["tag"])
  for dep in spec.get("requires", []):
    pkgHasher(specs[dep]["hash"])
    depHasher(specs[dep]["hash"])
    depHasher(specs[dep].get("devel_hash", ""))
  if spec.get("force_rebuild", False):
    pkgHasher(str(time.time()))
  if spec["package"] in develPkgs and "incremental_recipe" in spec:
    pkgHasher(spec["incremental_recipe"])
    spec["incremental_hash"] = Hasher(spec["incremental_recipe"]).hexdigest()
  elif pkg in develPkgs:
    pkgHasher(spec.get("devel_hash"))
  if architecture.startswith("osx") and "relocate_paths" in spec:
    pkgHasher("relocate:")
    pkgHasher(" ".join(sorted(spec["relocate_paths"])))
  spec["hash"] = pkgHasher.hexdigest()
  spec["deps_hash"] = depHasher.hexdigest()


def storePaths(spec, workDir, architecture):
  """Adds to the spec where tarballs and symlinks can be found.

  These paths should work locally and remotely.
  """
  pkgSpec = {
    "workDir": workDir,
    "package": spec["package"],
    "version": spec["version"],
    "hash": spec["hash"],
    "prefix": spec["hash"][0:2],
    "arch": architecture,
  }
  varSpecs = [
    ("storePath", "TARS/%(arch)s/store/%(prefix)s/%(hash)s"),
    ("linksPath", "TARS/%(arch)s/%(package)s"),
    ("tarballHashDir", "%(workDir)s/TARS/%(arch)s/store/%(prefix)s/%(hash)s"),
    ("tarballLinkDir", "%(workDir)s/TARS/%(arch)s/%(package)s"),
    ("buildDir", "%(workDir)s/BUILD/%(hash)s/%(package)s"),
  ]
  spec.update({k: v % pkgSpec for k, v in varSpecs})
  spec["old_devel_hash"] = \
    readHashFile(join(spec["buildDir"], ".build_succeeded"))


def doBuild(args, parser):
  """Build the package specified in the args."""
  syncHelper = chooseRemoteStore(args)
  dockerImage = args.dockerImage if "dockerImage" in args else None
  specs = {}
  workDir = abspath(args.workDir)
  prunePaths(workDir)

  if not exists(args.configDir):
    error('Cannot find %sdist recipes under directory "%s".\n'
          'Maybe you need to "cd" to the right directory or you forgot to run '
          '"%sBuild init"?', star(), args.configDir, star())
    return False

  def defaultsReader():
    return readDefaults(args.configDir, args.defaults,
                        parser.error, args.architecture)
  err, overrides, taps = parseDefaults(args.disable, defaultsReader, debug)
  dieOnError(err, err)
  del err

  specDir = "%s/SPECS" % workDir
  if not exists(specDir):
    os.makedirs(specDir)
  del specDir

  os.environ["ALIBUILD_ALIDIST_HASH"] = getDirectoryHash(args.configDir)

  debug("Building for architecture %s", args.architecture)
  debug("Number of parallel builds: %d", args.jobs)
  debug("Using %(star)sBuild from %(star)sbuild@%(toolHash)s recipes "
        "in %(star)sdist@%(distHash)s",
        star=star(),
        toolHash=getDirectoryHash(dirname(__file__)),
        distHash=os.environ["ALIBUILD_ALIDIST_HASH"])

  systemPackages, ownPackages, failed, validDefaults = getPackageList(
    packages                = args.pkgname,
    specs                   = specs,
    configDir               = args.configDir,
    preferSystem            = args.preferSystem,
    noSystem                = args.noSystem,
    architecture            = args.architecture,
    disable                 = args.disable,
    defaults                = args.defaults,
    dieOnError              = dieOnError,
    performPreferCheck      = dockerRunner(dockerImage),
    performRequirementCheck = dockerRunner(dockerImage),
    performValidateDefaults = lambda spec: validateDefaults(spec, args.defaults),
    overrides               = overrides,
    taps                    = taps,
    log                     = debug)
  del overrides, taps

  if validDefaults and args.defaults not in validDefaults:
    error("Specified default `%s' is not compatible with the packages you want "
          "to build.\nValid defaults:\n\n- %s",
          args.defaults, "\n- ".join(sorted(validDefaults)))
    return False

  if failed:
    error("The following packages are system requirements and could not be "
          "found:\n\n- %s\n\nPlease run:\n\n\taliDoctor %s\n\n"
          "to get a full diagnosis.",
          "\n- ".join(sorted(failed)), args.pkgname.pop())
    return False

  for x in specs.values():
    x["requires"] = [r for r in x["requires"] if not r in args.disable]
    x["build_requires"] = [r for r in x["build_requires"] if not r in args.disable]
    x["runtime_requires"] = [r for r in x["runtime_requires"] if not r in args.disable]

  if systemPackages:
    banner("%sBuild can take the following packages from the system and "
           "will not build them:\n  %s", star(), ", ".join(systemPackages))
  if ownPackages:
    banner("The following packages cannot be taken from the system and "
           "will be built:\n  %s", ", ".join(ownPackages))

  buildOrder = deque(createBuildOrder(specs))

  # Date fields to substitute: they are zero-padded
  now = datetime.now()
  nowKwds = { "year": str(now.year),
              "month": str(now.month).zfill(2),
              "day": str(now.day).zfill(2),
              "hour": str(now.hour).zfill(2) }

  # Check if any of the packages can be picked up from a local checkout
  develCandidates = [basename(d) for d in glob("*") if os.path.isdir(d)]
  develCandidatesUpper = [basename(d).upper() for d in glob("*") if os.path.isdir(d)]
  develPkgs = [p for p in buildOrder
               if p in develCandidates and p not in args.noDevel]
  develPkgsUpper = [(p, p.upper()) for p in buildOrder
                    if p.upper() in develCandidatesUpper and p not in args.noDevel]
  if set(develPkgs) != set(x for x, _ in develPkgsUpper):
    error("The following development packages have wrong spelling: %s.\nPlease"
          " check your local checkout and adapt to the correct one indicated.",
          ", ".join(set(x.strip() for x, _ in develPkgsUpper) - set(develPkgs)))
    return False

  if buildOrder:
    banner("Packages will be built in the following order:\n - %s",
           "\n - ".join((x + " (development package)") if x in develPkgs
                        else "%s@%s" % (x, specs[x]["tag"])
                        for x in buildOrder if x != "defaults-release"))

  if develPkgs:
    banner("You have packages in development mode.\n"
           "This means their source code can be freely modified under:\n\n"
           "  %s/<package_name>\n\n"
           "%sBuild does not automatically update such packages to avoid work loss.\n"
           "In most cases this is achieved by doing in the package source directory:\n\n"
           "  git pull --rebase\n",
           os.getcwd(), star())

  # Clone/update repos
  for p in buildOrder:
    if "source" not in specs[p]:
      continue
    updateReferenceRepoSpec(args.referenceSources, p, specs[p], args.fetchRepos, not args.docker)

    # Retrieve git heads
    cmd = "git ls-remote --heads " + specs[p].get("reference", specs[p]["source"])
    if specs[p]["package"] in develPkgs:
       specs[p]["source"] = join(os.getcwd(), specs[p]["package"])
       cmd = "git ls-remote --heads " + specs[p]["source"]
    debug("Executing %s", cmd)
    res, output = getStatusOutputBash(cmd)
    dieOnError(res, "Error on '%s': %s" % (cmd, output))
    specs[p]["git_heads"] = output.split("\n")

  for pkg in buildOrder:
    try:
      develPackageBranch = getCommitRef(specs[pkg], develPkgs, args, nowKwds)
    except ExternalCommandError:
      error("Error, unable to lookup changes in development package %s. "
            "Is it a git clone?", spec["source"])
      return False

  # Decide what is the main package we are building and at what commit.
  #
  # We emit an event for the main package, when encountered, so that we can use
  # it to index builds of the same hash on different architectures. We also
  # make sure add the main package and it's hash to the debug log, so that we
  # can always extract it from it.
  # If one of the special packages is in the list of packages to be built,
  # we use it as main package, rather than the last one.
  if not buildOrder:
    banner("Nothing to be done.")
    return True
  mainPackage = buildOrder[-1]
  mainHash = specs[mainPackage]["commit_hash"]

  debug("Main package is %s@%s", mainPackage, mainHash)
  if args.debug:
    logger_handler.setFormatter(
        LogFormatter("%%(asctime)s:%%(levelname)s:%s:%s: %%(message)s" %
                     (mainPackage, args.develPrefix if "develPrefix" in args else mainHash[0:8])))

  # Now that we have the main package set, we can print out useful information
  # which we will be able to associate with this build.
  for pkg in buildOrder:
    if "source" in specs[pkg]:
      debug("Commit hash for %s@%s is %s",
            specs[pkg]["source"], specs[pkg]["tag"], specs[pkg]["commit_hash"])

  # Calculate the hashes. We do this in build order so that we can guarantee
  # that the hashes of the dependencies are calculated first.
  debug("Calculating hashes.")
  debug("Development packages: %r", develPkgs)
  for pkg in buildOrder:
    debug("Recipe %s: %r", pkg, dict(specs[pkg]))
    calculateHashes(pkg, specs, develPkgs, args.architecture)
    debug("Hash for recipe %s is %s", pkg, specs[pkg]["hash"])
    storePaths(specs[pkg], workDir, args.architecture)

  # We recursively calculate the full set of requires "full_requires"
  # including build_requires and the subset of them which are needed at
  # runtime "full_runtime_requires".
  for p in buildOrder:
    spec = specs[p]
    todo = [p]
    spec["full_requires"] = []
    spec["full_runtime_requires"] = []
    spec["full_build_requires"] = []
    while todo:
      i = todo.pop(0)
      requires = specs[i].get("requires", [])
      runTimeRequires = specs[i].get("runtime_requires", [])
      buildRequires = specs[i].get("build_requires", [])
      spec["full_requires"] += requires
      spec["full_runtime_requires"] += runTimeRequires
      spec["full_build_requires"] += buildRequires
      todo += requires
    spec["full_requires"] = set(spec["full_requires"])
    spec["full_runtime_requires"] = set(spec["full_runtime_requires"])
    # If something requires or runtime_requires a package, then it's not 
    # a build_requires only anymore, so we drop it from the list.
    spec["full_build_requires"] = set(spec["full_build_requires"]) - spec["full_runtime_requires"]

  debug("We will build packages in the following order: %s",
        " ".join(buildOrder))
  if args.dryRun:
    info("--dry-run / -n specified. Not building.")
    return True

  # We now iterate on all the packages, making sure we build correctly every
  # single one of them. This is done this way so that the second time we run we
  # can check if the build was consistent and if it is, we bail out.
  packageIterations = 0
  report_event("install", "%s disabled=%s devel=%s system=%s own=%s deps=%s" % (
    args.pkgname,
    ",".join(sorted(args.disable)),
    ",".join(sorted(develPkgs)),
    ",".join(sorted(systemPackages)),
    ",".join(sorted(ownPackages)),
    ",".join(tuple(buildOrder)[:-1])
  ), args.architecture)

  while buildOrder:
    packageIterations += 1
    if packageIterations > 20:
      error("Too many attempts at building %s. "
            "Something wrong with the repository?", spec["package"])
      return False
    p = buildOrder[0]
    spec = specs[p]
    if args.debug:
      logger_handler.setFormatter(
          LogFormatter("%%(asctime)s:%%(levelname)s:%s:%s:%s: %%(message)s" %
                       (mainPackage, p, args.develPrefix if "develPrefix" in args else mainHash[0:8])))
    if spec["package"] in develPkgs and getattr(syncHelper, "writeStore", None):
      warning("Disabling remote write store from now since %s is a development package.",
              spec["package"])
      syncHelper.writeStore = ""

    # Since we can execute this multiple times for a given package, in order to
    # ensure consistency, we need to reset things and make them pristine.
    spec.pop("revision", None)

    debug("Updating from tarballs")
    # If we arrived here it really means we have a tarball which was created
    # using the same recipe. We will use it as a cache for the build. This means
    # that while we will still perform the build process, rather than
    # executing the build itself we will:
    #
    # - Unpack it in a temporary place.
    # - Invoke the relocation specifying the correct work_dir and the
    #   correct path which should have been used.
    # - Move the version directory to its final destination, including the
    #   correct revision.
    # - Repack it and put it in the store with the
    #
    # this will result in a new package which has the same binary contents of
    # the old one but where the relocation will work for the new dictory. Here
    # we simply store the fact that we can reuse the contents of cachedTarball.
    syncHelper.syncToLocal(p, spec)

    # Decide how it should be called, based on the hash and what is already
    # available.
    debug("Checking for packages already built.")
    linksGlob = "%(w)s/TARS/%(a)s/%(p)s/%(p)s-%(v)s-*.%(a)s.tar.gz" % {
      "w": workDir, "a": args.architecture, "p": spec["package"],
      "v": spec["version"]}
    debug("Glob pattern used: %s", linksGlob)
    # In case there is no installed software, revision is 1
    # If there is already an installed package:
    # - Remove it if we do not know its hash
    # - Use the latest number in the version, to decide its revision
    debug("Packages already built using this version\n%s", "\n".join(glob(linksGlob)))
    busyRevisions = []

    # Calculate the build_family for the package
    #
    # If the package is a devel package, we need to associate it a devel
    # prefix, either via the -z option or using its checked out branch. This
    # affects its build hash.
    #
    # Moreover we need to define a global "buildFamily" which is used
    # to tag all the packages incurred in the build, this way we can have
    # a latest-<buildFamily> link for all of them an we will not incur in the
    # flip - flopping described in https://github.com/alisw/alibuild/issues/325.
    develPrefix = ""
    possibleDevelPrefix = getattr(args, "develPrefix", develPackageBranch)
    if spec["package"] in develPkgs:
      develPrefix = possibleDevelPrefix

    if possibleDevelPrefix:
      spec["build_family"] = "%s-%s" % (possibleDevelPrefix, args.defaults)
    else:
      spec["build_family"] = args.defaults
    if spec["package"] == mainPackage:
      mainBuildFamily = spec["build_family"]

    for d in glob(linksGlob):
      match = re.match(
        "../../%(a)s/store/[0-9a-f]{2}/([0-9a-f]*)/%(p)s-%(v)s-([0-9]*).%(a)s.tar.gz$" %
        {"a": args.architecture, "p": spec["package"], "v": spec["version"]},
        os.readlink(d))
      if not match:
        continue
      linkHash = match.group(1)
      revision = int(match.group(2))

      # If we have an hash match, we use the old revision for the package
      # and we do not need to build it.
      if linkHash == spec["hash"]:
        spec["revision"] = revision
        if spec["package"] in develPkgs and "incremental_recipe" in spec:
          spec["obsolete_tarball"] = d
        else:
          debug("Package %s with hash %s is already found in %s. Not building.",
                p, linkHash, d)
          src = "%s-%s" % (spec["version"], spec["revision"])
          execute("ln -sfn %s %s/%s/%s/latest-%s" %
                  (src, workDir, args.architecture, spec["package"],
                   spec["build_family"]))
          execute("ln -sfn %s %s/%s/%s/latest" %
                  (src, workDir, args.architecture, spec["package"]))
          info("Using cached build for %s", p)
        break

      busyRevisions.append(revision)

    if "revision" not in spec:
      spec["revision"] = str(
        min(set(range(1, max(busyRevisions) + 2)) - set(busyRevisions))
        if busyRevisions else 1)

    # Recreate symlinks to this development package builds.
    if spec["package"] in develPkgs:
      debug("Creating symlinks to builds of devel package %s", spec["package"])
      cmd = "ln -sfn %s %s/BUILD/%s-latest" % (
        spec["hash"], workDir, spec["package"])
      if develPrefix:
        cmd += " && ln -sfn %s %s/BUILD/%s-latest-%s" % (
          spec["hash"], workDir, spec["package"], develPrefix)
      err = execute(cmd)
      debug("Got %d from %s", err, cmd)
      # Last package built gets a "latest" mark.
      cmd = "ln -sfn %s-%s %s/%s/%s/latest" % (
        spec["version"], spec["revision"], workDir, args.architecture,
        spec["package"])
      # Latest package built for a given devel prefix gets a
      # "latest-%(family)s" mark.
      if spec["build_family"]:
        cmd += " && ln -sfn %s-%s %s/%s/%s/latest-%s" % (
          spec["version"], spec["revision"], workDir, args.architecture,
          spec["package"], spec["build_family"])
      err = execute(cmd)
      debug("Got %d from %s", err, cmd)

      # Check if this development package needs to be rebuilt.
      debug("Checking if devel package %s needs rebuild", spec["package"])
      if spec["devel_hash"] + spec["deps_hash"] == spec["old_devel_hash"]:
        info("Development package %s does not need rebuild", spec["package"])
        buildOrder.popleft()
        continue

    # Now that we have all the information about the package we want to build,
    # let's check if it wasn't built / unpacked already.
    hashFile = "%s/%s/%s/%s-%s/.build-hash" % (
      workDir, args.architecture, spec["package"], spec["version"],
      spec["revision"])
    fileHash = readHashFile(hashFile)
    if fileHash != spec["hash"]:
      if fileHash != "0":
        debug("Mismatch between local area (%s) and the one which I should "
              "build (%s). Redoing.", fileHash, spec["hash"])
      shutil.rmtree(dirname(hashFile), True)
    else:
      # If we get here, we know we are in sync with whatever remote store.  We
      # can therefore create a directory which contains all the packages which
      # were used to compile this one.
      debug("Package %s was correctly compiled. Moving to next one.",
            spec["package"])
      # If using incremental builds, next time we execute the script we need to
      # remove the placeholders which avoid rebuilds.
      if spec["package"] in develPkgs and "incremental_recipe" in spec:
        os.unlink(hashFile)
      if "obsolete_tarball" in spec:
        os.unlink(realpath(spec["obsolete_tarball"]))
        os.unlink(spec["obsolete_tarball"])
      # We need to create 2 sets of links, once with the full requires,
      # once with only direct dependencies, since that's required to
      # register packages in Alien.
      createDistLinks(spec, specs, args, "dist", "full_requires")
      createDistLinks(spec, specs, args, "dist-direct", "requires")
      createDistLinks(spec, specs, args, "dist-runtime", "full_runtime_requires")
      buildOrder.popleft()
      packageIterations = 0
      # We can now delete the INSTALLROOT and BUILD directories,
      # assuming the package is not a development one. We also can
      # delete the SOURCES in case we have aggressive-cleanup enabled.
      if not spec["package"] in develPkgs and args.autoCleanup:
        cleanupDirs = [join(workDir, "BUILD", spec["hash"]),
                       join(workDir, "INSTALLROOT", spec["hash"])]
        if args.aggressiveCleanup:
          cleanupDirs.append(join(workDir, "SOURCES", spec["package"]))
        debug("Cleaning up:\n%s", "\n".join(cleanupDirs))

        for d in cleanupDirs:
          shutil.rmtree(d.encode("utf8"), True)
        ignoreOSError(os.unlink, "%s/BUILD/%s-latest" % (
          workDir, spec["package"]))
        if "develPrefix" in args:
          ignoreOSError(os.unlink, "%s/BUILD/%s-latest-%s" % (
            workDir, spec["package"], args.develPrefix))
        ignoreOSError(os.rmdir, join(workDir, "BUILD"))
        ignoreOSError(os.rmdir, join(workDir, "INSTALLROOT"))
      continue

    debug("Looking for cached tarball in %s", spec["tarballHashDir"])
    # FIXME: I should get the tarballHashDir updated with server at this point.
    #        It does not really matter that the symlinks are ok at this point
    #        as I only used the tarballs as reusable binary blobs.
    spec["cachedTarball"] = ""
    if not spec["package"] in develPkgs:
      tarballs = [x
                  for x in glob("%s/*" % spec["tarballHashDir"])
                  if x.endswith("gz")]
      spec["cachedTarball"] = tarballs[0] if tarballs else ""
      debug("Found tarball in %s" % spec["cachedTarball"]
            if spec["cachedTarball"] else "No cache tarballs found")

    # Generate the part which sources the environment for all the dependencies.
    # Notice that we guarantee that a dependency is always sourced before the
    # parts depending on it, but we do not guaranteed anything for the order in
    # which unrelated components are activated.
    dependencies = "ALIBUILD_ARCH_PREFIX=\"${ALIBUILD_ARCH_PREFIX:-%s}\"\n" % args.architecture
    dependenciesInit = "echo ALIBUILD_ARCH_PREFIX=\"\${ALIBUILD_ARCH_PREFIX:-%s}\" >> $INSTALLROOT/etc/profile.d/init.sh\n" % args.architecture
    for dep in spec.get("requires", []):
      depSpec = specs[dep]
      depInfo = {
        "architecture": args.architecture,
        "package": dep,
        "version": depSpec["version"],
        "revision": depSpec["revision"],
        "bigpackage": dep.upper().replace("-", "_")
      }
      dependencies += (
        '[ -z ${%(bigpackage)s_REVISION+x} ] && '
        'source "$WORK_DIR/$ALIBUILD_ARCH_PREFIX/'
        '%(package)s/%(version)s-%(revision)s/etc/profile.d/init.sh"\n'
      ) % depInfo
      dependenciesInit += (
        r'echo [ -z \${%(bigpackage)s_REVISION+x} ] \&\& '
        r'source \${WORK_DIR}/\${ALIBUILD_ARCH_PREFIX}/'
        '%(package)s/%(version)s-%(revision)s/etc/profile.d/init.sh '
        '>> \"$INSTALLROOT/etc/profile.d/init.sh\"\n'
      ) % depInfo

    # Generate the part which creates the environment for the package.
    # This can be either variable set via the "env" keyword in the metadata
    # or paths which get appended via the "append_path" one.
    # By default we append LD_LIBRARY_PATH, PATH
    for key in ("env", "append_path", "prepend_path"):
      dieOnError(not isinstance(spec.get(key, {}), dict),
                 "Tag `%s' in %s should be a dict." % (key, p))
    # Prepend these paths so that they win against system ones.
    basePath = p.upper().replace("-", "_") + "_ROOT"
    defaultPrependPaths = {"LD_LIBRARY_PATH": "$%s/lib" % basePath,
                           "PATH": "$%s/bin" % basePath}
    prependPaths = {key: value if isinstance(value, list) else [value]
                    for key, value in spec.get("prepend_path", {}).items()}
    prependPaths.update({key: [prepend] + prependPaths.get(key, [])
                         for key, prepend in defaultPrependPaths.items()})

    environment = "".join(chain(
      # Regular environment variables
      ("echo 'export %s=\"%s\"' >> $INSTALLROOT/etc/profile.d/init.sh\n" % (k, v)
       for k, v in spec.get("env", {}).items() if k != "DYLD_LIBRARY_PATH"),

      # Append paths
      ("\ncat << \\EOF >> \"$INSTALLROOT/etc/profile.d/init.sh\""
       "\nexport %(key)s=$%(key)s:%(value)s\nEOF" %
       {"key": k, "value": v if not isinstance(v, list) else ":".join(v)}
       for k, v in spec.get("append_path", {}).items()
       if k != "DYLD_LIBRARY_PATH"),

      # Prepend paths
      ("\ncat << \\EOF >> \"$INSTALLROOT/etc/profile.d/init.sh\""
       "\nexport %(key)s=%(value)s${%(key)s+:$%(key)s}\nEOF" %
       {"key": k, "value": ":".join(v)}
       for k, v in prependPaths.items() if k != "DYLD_LIBRARY_PATH"),
    ))

    # The actual build script.
    partialCloneStatement = ""
    if partialCloneFilter and not args.docker:
      partialCloneStatement = "export GIT_PARTIAL_CLONE_FILTER='--filter=blob:none'"

    debug(spec)

    rawcmd = ""
    try:
      fp = open(join(dirname(realpath(__file__)), "build_template.sh"), "r")
      rawcmd = fp.read()
      fp.close()
    except:
      from pkg_resources import resource_string
      rawcmd = resource_string("alibuild_helpers", "build_template.sh")

    source = spec.get("source", "")
    # Shortend the commit hash in case it's a real commit hash and not simply
    # the tag.
    commit_hash = spec["commit_hash"]
    if spec["tag"] != spec["commit_hash"]:
      commit_hash = spec["commit_hash"][0:10]

    # Split the source in two parts, sourceDir and sourceName.  This is done so
    # that when we use Docker we can replace sourceDir with the correct
    # container path, if required.  No changes for what concerns the standard
    # bash builds, though.
    cachedTarball = (re.sub("^" + workDir, "/sw", spec["cachedTarball"])
                     if args.docker else spec["cachedTarball"])

    scriptDir = "%s/%s/%s/%s/%s-%s" % (workDir, "SPECS", args.architecture,
                                       spec["package"], spec["version"],
                                       spec["revision"])
    err = execute("mkdir -p %s" % scriptDir)
    dieOnError(err, "Could not create directory %s" % scriptDir)
    writeAll("%s/%s.sh" % (scriptDir, spec["package"]), spec["recipe"])
    writeAll("%s/build.sh" % scriptDir, str(rawcmd) % {
      "dependencies": dependencies,
      "dependenciesInit": dependenciesInit,
      "develPrefix": develPrefix,
      "environment": environment,
      "workDir": workDir,
      "configDir": abspath(args.configDir),
      "incremental_recipe": spec.get("incremental_recipe", ":"),
      "sourceDir": (dirname(source) + "/") if source else "",
      "sourceName": basename(source) if source else "",
      "referenceStatement": (
        "export GIT_REFERENCE=${GIT_REFERENCE_OVERRIDE:-%s}/%s" %
        (dirname(spec["reference"]), basename(spec["reference"]))
        if "reference" in spec else ""),
      "partialCloneStatement": partialCloneStatement,
      "requires": " ".join(spec["requires"]),
      "build_requires": " ".join(spec["build_requires"]),
      "runtime_requires": " ".join(spec["runtime_requires"]),
    })

    banner("Building %s@%s", spec["package"],
           args.develPrefix if "develPrefix" in args and
           spec["package"] in develPkgs else spec["version"])
    # Define the environment so that it can be passed up to the
    # actual build script
    buildEnvironment = [
      ("ARCHITECTURE", args.architecture),
      ("BUILD_REQUIRES", " ".join(spec["build_requires"])),
      ("CACHED_TARBALL", cachedTarball),
      ("CAN_DELETE", "1" if args.aggressiveCleanup else ""),
      ("COMMIT_HASH", commit_hash),
      ("DEPS_HASH", spec.get("deps_hash", "")),
      ("DEVEL_HASH", spec.get("devel_hash", "")),
      ("DEVEL_PREFIX", develPrefix),
      ("BUILD_FAMILY", spec["build_family"]),
      ("GIT_COMMITTER_NAME", "unknown"),
      ("GIT_COMMITTER_EMAIL", "unknown"),
      ("GIT_TAG", spec["tag"]),
      ("MY_GZIP", gzip()),
      ("MY_TAR", tar()),
      ("INCREMENTAL_BUILD_HASH", spec.get("incremental_hash", "0")),
      ("JOBS", args.jobs),
      ("PKGHASH", spec["hash"]),
      ("PKGNAME", spec["package"]),
      ("PKGREVISION", spec["revision"]),
      ("PKGVERSION", spec["version"]),
      ("RELOCATE_PATHS", " ".join(spec.get("relocate_paths", []))),
      ("REQUIRES", " ".join(spec["requires"])),
      ("RUNTIME_REQUIRES", " ".join(spec["runtime_requires"])),
      ("FULL_RUNTIME_REQUIRES", " ".join(spec["full_runtime_requires"])),
      ("FULL_BUILD_REQUIRES", " ".join(spec["full_build_requires"])),
      ("FULL_REQUIRES", " ".join(spec["full_requires"])),
      ("WRITE_REPO", spec.get("write_repo", source)),
    ]
    # Add the extra environment as passed from the command line.
    buildEnvironment += [e.partition('=')[::2] for e in args.environment]
    # In case the --docker options is passed, we setup a docker container which
    # will perform the actual build. Otherwise build as usual using bash.
    if args.docker:
      dockerWrapper = (
        "docker run --rm --user $(id -u):$(id -g) -v %(workdir)s:/sw"
        " -v %(scriptDir)s/build.sh:/build.sh:ro %(mirrorVolume)s"
        " %(develVolumes)s %(additionalEnv)s %(additionalVolumes)s"
        " -e GIT_REFERENCE_OVERRIDE=/mirror -e WORK_DIR_OVERRIDE=/sw"
        " %(overrideSource)s %(image)s -c '%(bash)s -ex /build.sh'"
      ) % {
        "bash": BASH,
        "scriptDir": scriptDir,
        "workdir": abspath(args.workDir),
        "image": dockerImage,
        "additionalEnv": " ".join("-e %s='%s'" % env
                                  for env in buildEnvironment),
        "additionalVolumes": " ".join("-v %s" % volume
                                      for volume in args.volumes),
        "develVolumes": " ".join("-v $PWD/`readlink %s || echo %s`:/%s:ro" %
                                 (devel, devel, devel) for devel in develPkgs),
        "mirrorVolume": ("-v %s:/mirror" % dirname(spec["reference"])
                         if "reference" in spec else ""),
        "overrideSource": ("-e SOURCE0_DIR_OVERRIDE=/"
                           if source.startswith("/") else ""),
      }
      debug(dockerWrapper)
      err = execute(dockerWrapper)
    else:
      progress = ProgressPrint("%s is being built (use --debug for full output)" % spec["package"])
      for key, value in buildEnvironment:
        os.environ[key] = str(value)
      err = execute("%s -e -x %s/build.sh 2>&1" % (BASH, scriptDir),
                    printer=debug if args.debug or not sys.stdout.isatty() else progress)
      progress.end("failed" if err else "ok", err)
    report_event("BuildError" if err else "BuildSuccess", spec["package"],
                 " ".join((args.architecture, spec["version"], spec["commit_hash"],
                           os.environ["ALIBUILD_ALIDIST_HASH"][0:10])))

    updatablePkgs = [x for x in spec["requires"] if x in develPkgs]
    if spec["package"] in develPkgs:
      updatablePkgs.append(spec["package"])

    buildErrMsg = format(
      "Error while executing %(sd)s/build.sh on `%(h)s'.\n"
      "Log can be found in %(bd)s/log\n"
      "Please upload it to CERNBox/Dropbox if you intend to request support.\n"
      "Build directory is %(bd)s.",
      h=socket.gethostname(), sd=scriptDir, bd="%s/BUILD/%s-latest%s/%s" % (
        abspath(args.workDir),
        spec["package"],
        "-" + args.develPrefix
        if "develPrefix" in args and spec["package"] in develPkgs else "",
        spec["package"]))
    if updatablePkgs:
      buildErrMsg += (
        "\n\nNote that you have packages in development mode.\n"
        "Devel sources are not updated automatically, you must do it by hand.\n"
        "This problem might be due to one or more outdated devel sources.\n"
        "To update all development packages required for this build "
        "it is usually sufficient to do:\n\n"
      ) + "\n".join("  ( cd %s && git pull --rebase )" % dp
                    for dp in updatablePkgs)

    dieOnError(err, buildErrMsg)

    syncHelper.syncToRemote(p, spec)

  banner("Build of %(mainPackage)s successfully completed on `%(h)s'.\n"
         "Your software installation is at:"
         "\n\n  %(wp)s\n\n"
         "You can use this package by loading the environment:"
         "\n\n  alienv enter %(mainPackage)s/latest-%(buildFamily)s",
         mainPackage=mainPackage,
         buildFamily=mainBuildFamily,
         h=socket.gethostname(),
         defaults=args.defaults,
         wp=abspath(join(args.workDir, args.architecture)))
  for pkg in develPkgs:
    banner("Build directory for devel package %s:\n%s/BUILD/%s-latest%s/%s",
           pkg, abspath(args.workDir), pkg,
           ("-" + args.develPrefipkg) if "develPrefix" in args else "", pkg)
  debug("Everything done")
  return True

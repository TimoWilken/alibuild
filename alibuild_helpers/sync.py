"""Sync helpers for aliBuild."""

import re
import os
from os.path import basename
import time

from requests import get
from requests.exceptions import RequestException

from alibuild_helpers.cmd import execute
from alibuild_helpers.log import debug, error, warning, dieOnError
from alibuild_helpers.utilities import format


class NoRemoteSync:
  """Helper class which does not do anything to sync."""

  def syncToLocal(self, p, spec):
    pass

  def syncToRemote(self, p, spec):
    pass


class PartialDownloadError(Exception):
  """Signals that a download was not completed."""

  def __init__(self, downloaded, size):
    Exception.__init__(self)
    self.downloaded = downloaded
    self.size = size

  def __str__(self):
    return "only %d out of %d bytes downloaded" % (self.downloaded, self.size)


class HttpRemoteSync:

  def __init__(self, remoteStore, architecture, workdir, insecure):
    self.remoteStore = remoteStore
    self.writeStore = ""
    self.architecture = architecture
    self.workdir = workdir
    self.insecure = insecure
    self.httpTimeoutSec = 15
    self.httpConnRetries = 4
    self.httpBackoff = 0.4
    self.doneOrFailed = []

  def getRetry(self, url, dest=None, returnResult=False, log=True):
    for i in range(self.httpConnRetries):
      if i > 0:
        pauseSec = self.httpBackoff * (2 ** (i - 1))
        debug("GET %s failed: retrying in %.2f", url, pauseSec)
        time.sleep(pauseSec)
        # If the download has failed, enable debug output, even if it was
        # disabled before. We disable debug output for e.g. symlink downloads
        # to make sure the output log isn't overwhelmed. If the download
        # failed, we want to know about it, though. Note that aliBuild has to
        # be called with --debug for this to take effect.
        log = True

      try:
        if log:
          debug("GET %s: processing (attempt %d/%d)", url, i+1, self.httpConnRetries)
        if dest or returnResult:
          # Destination specified -- file (dest) or buffer (returnResult).
          # Use requests in stream mode
          resp = get(url, stream=True, verify=not self.insecure, timeout=self.httpTimeoutSec)
          size = int(resp.headers.get("content-length", "-1"))
          downloaded = 0
          reportTime = time.time()
          result = []

          try:
            destFp = open(dest+".tmp", "wb") if dest else None
            for chunk in filter(bool, resp.iter_content(chunk_size=32768)):
              if destFp:
                destFp.write(chunk)
              if returnResult:
                result.append(chunk)
              downloaded += len(chunk)
              if log and size != -1:
                now = time.time()
                if downloaded == size:
                  debug("Download complete")
                elif now - reportTime > 3:
                  debug("%.0f%% downloaded...", 100 * downloaded / size)
                  reportTime = now
          finally:
            if destFp:
              destFp.close()

          if size not in (downloaded, -1):
            raise PartialDownloadError(downloaded, size)
          if dest:
            os.rename(dest+".tmp", dest)  # we should not have errors here
          return b''.join(result) if returnResult else True

        # For CERN S3 we need to construct the JSON ourself...
        s3Request = re.match("https://s3.cern.ch/swift/v1/+([^/]*)/(.*)$", url)
        if s3Request:
          bucket, prefix = s3Request.groups()
          url = "https://s3.cern.ch/swift/v1/%s/?prefix=%s" % (bucket, prefix.strip("/"))
          resp = get(url, verify=not self.insecure, timeout=self.httpTimeoutSec)
          if resp.status_code == 404:
            # No need to retry any further
            return None
          resp.raise_for_status()
          return [{"name": basename(x), "type": "file"} for x in resp.text.split()]

        # No destination specified: JSON request
        resp = get(url, verify=not self.insecure, timeout=self.httpTimeoutSec)
        if resp.status_code == 404:
          # No need to retry any further
          return None
        resp.raise_for_status()
        return resp.json()
      except (RequestException, ValueError, PartialDownloadError) as err:
        if i == self.httpConnRetries-1:
          error("GET %s failed: %s", url, err)
        if dest:
          try:
            os.unlink(dest + ".tmp")
          except OSError:
            pass
    return None

  def syncToLocal(self, p, spec):
    if spec["hash"] in self.doneOrFailed:
      debug("Will not redownload %s with build hash %s", p, spec["hash"])
      return

    debug("Updating remote store for package %s@%s", p, spec["hash"])

    hashList = self.getRetry("%s/%s/" % (self.remoteStore, spec["storePath"]))
    pkgList = None
    if hashList is not None:
      pkgList = self.getRetry("%s/%s/" % (self.remoteStore, spec["linksPath"]))
    if pkgList is None or hashList is None:
      warning("%s (%s) not fetched: have you tried updating the recipes?", p, spec["hash"])
      self.doneOrFailed.append(spec["hash"])
      return

    execute("mkdir -p %s %s" % (spec["tarballHashDir"], spec["tarballLinkDir"]))
    hashList = [x["name"] for x in hashList]

    hasErr = False
    for pkg in hashList:
      destPath = os.path.join(spec["tarballHashDir"], pkg)
      if os.path.isfile(destPath):
        # Do not redownload twice
        continue
      if not self.getRetry("/".join((self.remoteStore, spec["storePath"], pkg)), destPath):
        hasErr = True

    for pkg in pkgList:
      if pkg["name"] in hashList:
        cmd = format("ln -nsf ../../%(a)s/store/%(sh)s/%(h)s/%(n)s %(ld)s/%(n)s\n",
                     a=self.architecture,
                     h=spec["hash"],
                     sh=spec["hash"][0:2],
                     n=pkg["name"],
                     ld=spec["tarballLinkDir"])
        execute(cmd)
      else:
        linkTarget = self.getRetry("/".join((self.remoteStore, spec["linksPath"], pkg["name"])),
                                   returnResult=True, log=False)
        execute(format("ln -nsf %(target)s %(ld)s/%(n)s\n",
                       target=linkTarget.decode("utf-8").rstrip("\r\n"),
                       ld=spec["tarballLinkDir"],
                       n=pkg["name"]))

    if not hasErr:
      self.doneOrFailed.append(spec["hash"])

  def syncToRemote(self, p, spec):
    return

# Helper class to sync package build directory using RSync.
class RsyncRemoteSync:
  def __init__(self, remoteStore, writeStore, architecture, workdir, rsyncOptions):
    self.remoteStore = re.sub("^ssh://", "", remoteStore)
    self.writeStore = re.sub("^ssh://", "", writeStore)
    self.architecture = architecture
    self.rsyncOptions = rsyncOptions
    self.workdir = workdir

  def syncToLocal(self, p, spec):
    debug("Updating remote store for package %s@%s", p, spec["hash"])
    err = execute(format(
      "mkdir -p %(tarballHashDir)s\n"
      "rsync -av %(ro)s %(remoteStore)s/%(storePath)s/ %(tarballHashDir)s/ || true\n"
      "rsync -av --delete %(ro)s %(remoteStore)s/%(linksPath)s/ %(tarballLinkDir)s/ || true\n",
      ro=self.rsyncOptions,
      remoteStore=self.remoteStore,
      storePath=spec["storePath"],
      linksPath=spec["linksPath"],
      tarballHashDir=spec["tarballHashDir"],
      tarballLinkDir=spec["tarballLinkDir"]))
    dieOnError(err, "Unable to update from specified store.")

  def syncToRemote(self, p, spec):
    if not self.writeStore:
      return
    err = execute(format(
      "cd %(workdir)s && "
      "rsync -avR %(rsyncOptions)s --ignore-existing %(storePath)s/%(tarballNameWithRev)s %(remoteStore)s/ &&"
      "rsync -avR %(rsyncOptions)s --ignore-existing %(linksPath)s/%(tarballNameWithRev)s %(remoteStore)s/",
      workdir=self.workdir,
      remoteStore=self.remoteStore,
      rsyncOptions=self.rsyncOptions,
      storePath=spec["storePath"],
      linksPath=spec["linksPath"],
      tarballNameWithRev=format(
        "%(package)s-%(version)s-%(revision)s.%(architecture)s.tar.gz",
        architecture=self.architecture, **spec)))
    dieOnError(err, "Unable to upload tarball.")

class S3RemoteSync:
  def __init__(self, remoteStore, writeStore, architecture, workdir):
    # This will require rclone to be installed in order to actually work
    # The name of the remote is always alibuild
    self.remoteStore = re.sub("^s3://", "", remoteStore)
    self.writeStore = re.sub("^s3://", "", writeStore)
    self.architecture = architecture
    self.workdir = workdir

  def syncToLocal(self, p, spec):
    debug("Updating remote store for package %s@%s", p, spec["hash"])
    err = execute(format(
      "s3cmd --no-check-md5 sync -s -v --host s3.cern.ch --host-bucket %(b)s.s3.cern.ch s3://%(b)s/%(storePath)s/ %(tarballHashDir)s/ 2>&1 || true\n"
      "mkdir -p '%(tarballLinkDir)s'; find '%(tarballLinkDir)s' -type l -delete;\n"
      "for x in `curl -sL https://s3.cern.ch/swift/v1/%(b)s/?prefix=%(linksPath)s/`; do\n"
      "  ln -sf `curl -sL https://s3.cern.ch/swift/v1/%(b)s/$x` %(tarballLinkDir)s/`basename $x` || true\n"
      "done",
      b=self.remoteStore,
      storePath=spec["storePath"],
      linksPath=spec["linksPath"],
      tarballHashDir=spec["tarballHashDir"],
      tarballLinkDir=spec["tarballLinkDir"]))
    dieOnError(err, "Unable to update from specified store.")

  def syncToRemote(self, p, spec):
    if not self.writeStore:
      return
    err = execute(format(
      "cd %(workdir)s && "
      "TARSHA256=`sha256sum %(storePath)s/%(tarballNameWithRev)s | awk '{ print $1 }'` && "
      "s3cmd put -s -v --host s3.cern.ch --host-bucket %(b)s.s3.cern.ch %(storePath)s/%(tarballNameWithRev)s s3://%(b)s/%(storePath)s/ 2>/dev/null || true\n"
      "HASHEDURL=`readlink %(linksPath)s/%(tarballNameWithRev)s | sed -e's|^../../||'` && "
      "echo $HASHEDURL | s3cmd put -s -v --host s3.cern.ch --host-bucket %(b)s.s3.cern.ch - s3://%(b)s/%(linksPath)s/%(tarballNameWithRev)s 2>/dev/null || true\n",
      workdir=self.workdir,
      b=self.remoteStore,
      storePath=spec["storePath"],
      linksPath=spec["linksPath"],
      tarballNameWithRev=format(
        "%(package)s-%(version)s-%(revision)s.%(architecture)s.tar.gz",
        architecture=self.architecture, **spec)))
    dieOnError(err, "Unable to upload tarball.")

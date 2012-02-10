###############################################################
# z3c.pypimirror - A PyPI mirroring solution
# Written by Daniel Kraft, Josip Delic, Gottfried Ganssauge and
# Andreas Jung
#
# Published under the Zope Public License 2.1
################################################################


import re
import os
import xmlrpclib
import sys
import util
import shutil
import httplib
import urllib 
from eventlet.green import urllib2
import time
import datetime
import ConfigParser
import optparse
import zc.lockfile
import socket
import tempfile
import urlparse
import pkg_resources
from BeautifulSoup import BeautifulSoup
from glob import fnmatch
from logger import getLogger
import HTMLParser
from gzip import GzipFile
from bz2 import BZ2File
from zipfile import is_zipfile
try: 
   from hashlib import md5
except ImportError:
   from md5 import md5
from eventlet.greenpool import GreenPool
from random import shuffle

# timeout in seconds
timeout = 10
socket.setdefaulttimeout(timeout)

LOG = None

dev_package_regex = re.compile(r'\ddev[-_]')

def pypimirror_version():
    """
        returns a version string
    """
    version = pkg_resources.working_set.by_key["z3c.pypimirror"].version
    return 'z3c.pypimirror/%s' % version

def urlopen(url):
    """ This behaves exactly like urllib2.urlopen, but injects a header
        User-Agent: z3c.pypimirror/1.0.2
    """
    headers = { 'User-Agent' : pypimirror_version() }
    req = urllib2.Request(url, None, headers)
    return urllib2.urlopen(req)

class Stats(object):
    """ This is just for statistics """
    def __init__(self):
        self._found = []
        self._stored = []
        self._error_404 = []
        self._error_invalid_package = []
        self._error_invalid_url = []
        self._starttime = time.time()

    def runtime(self):
        runtime = time.time() - self._starttime
        if runtime > 60:
            return "%dm%2ds" % (runtime//60, runtime%60)
        return "%ds" % runtime

    def found(self, name):
        self._found.append(name)

    def stored(self, name):
        self._stored.append(name)

    def error_404(self, name):
        self._error_404.append(name)

    def error_invalid_package(self, name):
        self._error_invalid_package.append(name)

    def error_invalid_url(self, name):
        self._error_invalid_url.append(name)

    def getStats(self):
        ret = []
        ret.append("Statistics")
        ret.append("----------")
        ret.append("Found (cached):         %d" % len(self._found))
        ret.append("Stored (downloaded):    %d" % len(self._stored))
        ret.append("Not found (404):        %d" % len(self._error_404))
        ret.append("Invalid packages:       %d" % len(self._error_invalid_package))
        ret.append("Invalid URLs:           %d" % len(self._error_invalid_url))
        ret.append("Runtime:                %s" % self.runtime())
        return ret


class PypiPackageList(object):
    """
        This fetches and represents a package list
    """
    def __init__(self, pypi_xmlrpc_url='http://pypi.python.org/pypi'):
        self._pypi_xmlrpc_url = pypi_xmlrpc_url

    def list(self, base_path, filter_by=None, fetch_since_days=7):
        server = xmlrpclib.Server(self._pypi_xmlrpc_url)
        packages = set(server.list_packages())
        changelog = server.changelog(int(time.time() - fetch_since_days*24*3600))
        changed = dict([(tp[0], tp[2]) for tp in changelog if "file" in tp[3]])
        for package in list(packages):
           if not True in [fnmatch.fnmatch(package, f) for f in filter_by]:
              packages.discard(package)
              continue
           package_path = os.path.join(base_path, package)
           timestamp_path = os.path.join(package_path, "timestamp")
           if package not in changed.keys():
              if os.path.exists(timestamp_path):
                 packages.discard(package)
           else:
              new_timestamp = changed[package]
              if os.path.exists(os.path.join(package_path, "timestamp")):
                 with open(timestamp_path, "rb") as f:
                    timestamp = int(f.read().rstrip())
                    if new_timestamp > timestamp :
                       packages.discard(package)
                       continue
        ret = dict()
        for package in packages:
           timestamp = changed.get(package, None)
           if not timestamp:
              timestamp, _, _ = str(time.time()).partition(".")
              timestamp = int(timestamp)
           ret[package] = timestamp
        return ret


class PackageError(Exception):
    pass
   
class Package(object):
    """
        This handles the list of versions and fetches the
        files
    """
    def __init__(self, package_name, pypi_base_url=["http://pypi.python.org/simple",
                                                    "http://b.pypi.python.org/simple",
                                                    "http://c.pypi.python.org/simple",
                                                    "http://d.pypi.python.org/simple",
                                                    "http://e.pypi.python.org/simple",
                                                    "http://f.pypi.python.org/simple"]):
        self._links_cache = None

        if not util.isASCII(package_name):
            raise PackageError("%s is not a valid package name." % package_name)

        try:
            package_name = urllib.quote(package_name)
        except KeyError:
            raise PackageError("%s is not a valid package name." % package_name)

        self.name = package_name
        self._pypi_base_url = pypi_base_url

    def url(self, filename=None, splittag=True):
        if filename:
            (filename, rest) = urllib.splittag(filename)
            try:
                filename = urllib.quote(filename)
            except KeyError:
                raise PackageError("%s is not a valid filename." % filename)
        urls = self._pypi_base_url[:]
        shuffle(urls)
        for pypi_base_url in urls:
            url = "%s/%s" % (pypi_base_url, self.name)
            if filename:
                url = "%s/%s/" % (url, filename)
            yield url

    def _fetch_index(self, url=None):
        if not url:
            url = self.url()
        try:
            html = urlopen(url).read()
        except urllib2.HTTPError, v:
            if '404' in str(v):             # sigh
                raise PackageError("Package not available (404): %s" % url)
            raise PackageError("Package not available (unknown reason): %s" % url)
        except urllib2.URLError, v:
            raise PackageError("URL Error: %s " % url)
        except Exception, e:
            raise PackageError('Generic error: %s' % e)
        return html

    def _fetch_links(self, html):
        try:
            soup = BeautifulSoup(html)
        except HTMLParser.HTMLParseError, e:
            raise PackageError("HTML parse error: %s" % e)
        links = []
        for link in soup.findAll("a"):
            href = link.get("href")
            if href:
                links.append(href)
        return links

    def _links_external(self, html, filename_matches=None, follow_external_index_pages=False):
        """ pypi has external "download_url"s. We try to get anything
            from there too. This is really ugly and I'm not sure if there's
            a sane way.  The download_url directs either to a website which
            contains many download links or directly to a package.
        """

        download_links = set()
        soup = BeautifulSoup(html)
        links = soup.findAll("a")
        for link in links:
            if link.renderContents().endswith("download_url"):
                # we have a download_url!! Yeah.
                url = link.get("href")
                if not url:
                    continue
                download_links.add(url)

            if link.renderContents().endswith("home_page"):
                # we have a download_url!! Yeah.
                url = link.get("href")
                if not url:
                    continue
                download_links.add(url)

        for link in download_links:
            # check if the link points directly to a file
            # and get it if it matches filename_matches
            if filename_matches:
                if self.matches(link, filename_matches):
                    yield link
                    continue

                # fetch what is behind the link and see if it's html.
                # If it is html, download anything from there.
                # This is extremely unreliable and therefore commented out.

                if follow_external_index_pages:
                    try:
                        site = urlopen(link)
                    except Exception, e:
                        LOG.warn('Unload downloading %s (%s)' % (link, e))
                        continue

                    if site.headers.type != "text/html":
                        continue

                    # we have a valid html page now. Parse links and download them.
                    # They have mostly no md5 hash.
                    html = site.read()
                    real_download_links = self._fetch_links(html)
                    candidates = list()
                    for real_download_link in real_download_links:
                        # build absolute links

                        real_download_link = urllib.basejoin(site.url, real_download_link)
                        if not filename_matches or self.matches(real_download_link, filename_matches):

                            # we're not interested in dev packages
                            if not dev_package_regex.search(real_download_link):

                                # Consider only download links that starts with
                                # the current package name
                                filename = urlparse.urlsplit(real_download_link)[2].split('/')[-1]
                                if not filename.startswith(self.name):
                                    continue

                                candidates.append(real_download_link)

                    def sort_candidates(url1, url2):
                        """ Sort all download links by package version """
                        parts1 = urlparse.urlsplit(url1)[2].split('/')[-1]
                        parts2 = urlparse.urlsplit(url2)[2].split('/')[-1]
                        return cmp(pkg_resources.parse_version(parts1), pkg_resources.parse_version(parts2))

                    # and return the 20 latest files
                    candidates.sort(sort_candidates)
                    for c in candidates[-20:][::-1]:
                        yield c


    def _links(self, filename_matches=None, external_links=False, follow_external_index_pages=False):
        """ This is an iterator which returns useful links on files for
            mirroring
        """
        for url in self.url():
            try:
                remote_index_html = self._fetch_index(url)
            except PackageError as e:
                pass
            else:
                e = None
                break
        if e:
            raise e
        for link in self._fetch_links(remote_index_html):
            # then handle "normal" packages in pypi.
            (url, hash) = urllib.splittag(link)
            if not hash:
                continue
            try:
                (hashname, hash) = hash.split("=")
            except ValueError:
                continue
            if not hashname == "md5":
                continue

            if filename_matches:
                if not self.matches(url, filename_matches):
                    continue

            yield (url, hash)

        if external_links:
            for link in self._links_external(remote_index_html, filename_matches, follow_external_index_pages):
                yield (link, None)

    def matches(self, filename, filename_matches):
        for filename_match in filename_matches:
            if fnmatch.fnmatch(filename, filename_match):
                return True

        # perhaps 'filename' is part of a query string, so 
        # try a regex match 
        for filename_match in filename_matches:
            regex = re.compile(r'\\%s\?' % filename_match)
            if regex.search(filename):
                return True
        
        return False

    def ls(self, filename_matches=None, external_links=False, follow_external_index_pages=False):
        links = self._links(filename_matches=filename_matches, 
                            external_links=external_links, 
                            follow_external_index_pages=follow_external_index_pages)
        results = dict()
        for link, md5sum in links:
            filename = os.path.basename(link)
            result = results.get(filename, dict())
            if "links" not in result:
                result["links"] = []
            if "md5sum" not in result:
                result["md5sum"] = None
            if md5sum:
                if not result["md5sum"]:
                    result["md5sum"] = md5sum
                elif result["md5sum"] != md5sum:
                    continue 
            result["links"].append(link)
            results[filename] = result
        return results

    def _get(self, url, filename, md5_hex=None):
        """ fetches a file and checks for the md5_hex if given
        """

        # since some time in Feb 2009 PyPI uses different and relative URLs
        # -> complete bullshit

        if url.startswith('../../packages'):
            url = 'http://pypi.python.org/' + url[6:]

        try:
            opener = urlopen(url)
            data = opener.read()
        except urllib2.HTTPError, v:
            if '404' in str(v):             # sigh
                raise PackageError("404: %s" % url)
            raise PackageError("Couldn't download (HTTP Error): %s" % url)
        except urllib2.URLError, v:
            raise PackageError("URL Error: %s " % url)
        except:
            raise PackageError("Couldn't download (unknown reason): %s" % url)
        if md5_hex:
            # check for md5 checksum
            data_md5 = md5(data).hexdigest()
            if md5_hex != data_md5:
                raise PackageError("MD5 sum does not match: %s / %s on package %s" % 
                                   (md5_hex, data_md5, url))
        return data

    def get(self, link):
        """ link is a tuple of url, md5_hex
        """
        return self._get(*link)
        
    def content_length(self, link):

        # First try to determine the content-length through
        # HEAD request in order to save bandwidth

        try:
            parts = urlparse.urlsplit(link)
            c = httplib.HTTPConnection(parts[1])
            c.request('HEAD', parts[2])
            response = c.getresponse()
            ct = response.getheader('content-length')
            if ct is not None:
                ct = long(ct)
                return ct
        except Exception, e:
            LOG.warn('Could not obtain content-length through a HEAD request from %s (%s)' % (link, e))

        try:
            return long(urlopen(link).headers.get("content-length"))
        except:
            return 0

class Mirror(object):
    """ This represents the whole mirror directory
    """
    def __init__(self, base_path):
        self.base_path = base_path
        self.mkdir()

    def mkdir(self):
        try:
            os.mkdir(self.base_path)
        except OSError:
            # like "File exists"
            pass

    def package(self, package_name):
        return MirrorPackage(self, package_name)

    def cleanup(self, remote_list, verbose=False):
        local_list = self.ls()
        for local_dir in local_list:
            try:
                if local_dir not in remote_list:
                    if verbose: 
                        LOG.debug("Removing package: %s" % local_dir)
                    self.rmr(os.path.join(self.base_path, local_dir))
            except UnicodeDecodeError:
                if verbose: 
                    LOG.debug("Removing package: %s" % local_dir)
                self.rmr(os.path.join(self.base_path, local_dir))

    def rmr(self, path):
        """ delete a package recursively (not really.)
        """
        shutil.rmtree(path)

    def ls(self):
        filenames = []
        for filename in os.listdir(self.base_path):
            if os.path.isdir(os.path.join(self.base_path, filename)):
                filenames.append(filename)
        filenames.sort()
        return filenames

    def _html_link(self, filename):
        return '<a href="%s/">%s</a>' % (filename, filename)

    def _index_html(self):
        header = "<html><head><title>PyPI Mirror</title></head><body>"
        header += "<h1>PyPI Mirror</h1><h2>Last update: " + \
                  datetime.datetime.utcnow().strftime("%c UTC")+"</h2>\n"
        _ls = self.ls()
        links = "<br />\n".join([self._html_link(link) for link in _ls])
        generator = "<p class='footer'>Generated by %s; %d packages mirrored. For details see the <a href='http://www.coactivate.org/projects/pypi-mirroring'>z3c.pypimirror project page.</a></p>" % (pypimirror_version(), len(_ls))
        footer = "</body></html>\n"
        return "\n".join((header, links, generator, footer))

    def index_html(self):
        content = self._index_html()
        with open(os.path.join(self.base_path, "index.html"), "wb") as f:
            f.write(content)

    def full_html(self, full_list):
        header = "<html><head><title>PyPI Mirror</title></head><body>"  
        header += "<h1>PyPi Mirror</h1><h2>Last update: " + \
                  time.strftime("%c %Z")+"</h2>\n"
        footer = "</body></html>\n"
        fp = file(os.path.join(self.base_path, "full.html"), "wb")
        fp.write(header)
        fp.write("<br />\n".join(full_list))
        fp.write(footer)
        fp.close()

    def _fetch_package(self, filename_matches, verbose, cleanup,
                       create_indexes, external_links,
                       follow_external_index_pages, base_url,
                       package_name, stats, full_list, timestamp):
        try:
            package = Package(package_name)
        except PackageError, v:
            stats.error_invalid_package(package_name)
            LOG.debug("Package is not valid.")
            return False

        try:
            downloadables = package.ls(filename_matches, external_links, 
                                       follow_external_index_pages)
        except PackageError, v:
            stats.error_404(package_name)
            LOG.debug("Package not available: %s" % v)
            return False

        mirror_package = self.package(package)
        successes = 0
        for url_basename, url_data in downloadables.items():
            md5_hash = url_data.get("md5sum", "")
            for url in url_data["links"]:
                try:
                    filename = self._extract_filename(url)
                except PackageError, v:
                    stats.error_invalid_url((url, url_basename, md5_hash))
                    LOG.info("Invalid URL: %s" % v)
                    continue                                
                if mirror_package.is_valid(url_basename=url_basename,
                                           md5_hash=md5_hash):
                    stats.found(filename)
                    full_list.append(mirror_package._html_link(base_url, 
                                                               url_basename, 
                                                               md5_hash))
                    if verbose: 
                        LOG.debug("Found: %s" % filename)
                    continue
                         
                    # we need to download it
                try:
                    data = package.get((url, filename, md5_hash))
                except PackageError, v:
                    stats.error_invalid_url((url, url_basename, md5_hash))
                    LOG.info("Invalid URL: %s" % v)
                    continue
                try:
                    mirror_package.write_package(filename, data, md5_hash, url)
                except PackageError, v:
                    if verbose:
                        LOG.debug(str(v))
                    mirror_package.rm(filename)
                else:
                   stats.stored(filename)
                   full_list.append(mirror_package._html_link(base_url, filename, md5_hash))
                   if verbose:
                      LOG.debug("Stored: %s [%d kB]" % (filename, len(data)//1024))
                   successes += 1
                   break
        if successes == len(downloadables.keys()):
            with open(mirror_package.path("timestamp"), "wb") as f:
                f.write(str(timestamp))
        if create_indexes:
            mirror_package.index_html(base_url)
        
    def mirror(self, 
               package_list, 
               filename_matches, 
               verbose, 
               cleanup, 
               create_indexes, 
               external_links, 
               follow_external_index_pages, 
               base_url):
        stats = Stats()
        full_list = []
        pool = GreenPool()
        for package_name, timestamp in package_list.items():
            LOG.debug('Starting to process package %s' % package_name)
            pool.spawn_n(self._fetch_package, filename_matches, verbose, cleanup, create_indexes,
                         external_links, follow_external_index_pages, base_url,
                         package_name, stats, full_list, timestamp)
        pool.waitall()
        if create_indexes:
            self.index_html()
            full_list.sort()
            self.full_html(full_list)

        for line in stats.getStats():
            LOG.debug(line)

    def _extract_filename(self, url):
        """Get the real filename from an arbitary pypi download url.
        
        Reality sucks, but we need to use heuristics here to avoid a many HEAD
        requests. Use them only if heuristics is not possible. 
        """
        fetch_url = url
        do_again = True
        while do_again:
            # heuristics start
            url_basename = os.path.basename(fetch_url)                
            # do we have GET parameters? 
            # if not, we believe the basename is the filename
            if '?' not in url_basename:
                return url_basename
            # now we have a bunch of crap in get parameters, we need to do a head 
            # request to get the filename
            LOG.debug("Head-Request to get filename for %s." % fetch_url)
            parsed_url = urlparse.urlparse(fetch_url)
            if parsed_url.scheme == 'https':
                port = parsed_url.port or 443
                conn = httplib.HTTPSConnection(parsed_url.netloc, port)
            else:
                port = parsed_url.port or 80
                conn = httplib.HTTPConnection(parsed_url.netloc, port)
            try:
                conn.request('HEAD', fetch_url)
                resp = conn.getresponse()
            except:
                raise PackageError, "Connection %s caused an error" % fetch_url               
            if resp.status in (301, 302):
                fetch_url = resp.getheader("Location", None)
                if fetch_url is not None:
                    continue
                raise PackageError, "Redirect (%s) from %s without location" % \
                                    (resp.status, fetch_url)
            elif resp.status != 200:                
                raise PackageError, "URL %s can't be fetched" % fetch_url
            do_again = False                                    
        content_disposition = resp.getheader("Content-Disposition", None)
        if content_disposition:
            content_disposition = [_.strip() for _ in \
                                   content_disposition.split(';') \
                                   if _.strip().startswith('filename')]
            if len(content_disposition) == 1 and '=' in content_disposition[0]:
                return content_disposition[0].split('=')[1].strip('"')
        # so we followed redirects and no meaningful name came back, last 
        # fallback is to use the basename w/o request parameters.
        # if this is wrong, it has to fail later. 
        return os.path.basename(fetch_url[:fetch_url.find('?')])

class MirrorPackage(object):
    """ This checks for already existing files and creates the index
    """
    def __init__(self, mirror, package):
        self.package = package
        self.package_name = package.name
        self.mirror = mirror
        self.mkdir()

    def mkdir(self):
        try:
            os.mkdir(self.path())
        except OSError:
            # like "File exists"
            pass

    def path(self, filename=None):
        if not filename:
            return os.path.join(self.mirror.base_path, self.package_name)
        return os.path.join(self.mirror.base_path, self.package_name, filename)

    def is_valid(self, url_basename, md5_hash):
        if md5_hash and self.md5_match(url_basename, md5_hash):
            return True
        return False

        
    def md5_match(self, filename, md5):
        file = MirrorFile(self, filename)
        return file.md5 == md5

    def size_match(self, filename, size):
        file = MirrorFile(self, filename)
        return file.size == size

    def write(self, filename, data):
        self.mkdir()
        file = MirrorFile(self, filename)
        file.write(data)

    def write_package(self, filename, data, hash="", url=""):
        self.mkdir()
        file = MirrorFile(self, filename)
        file.write(data)
        if hash:
            file.write_md5(hash)
        else:
            if not url:
                raise PackageError("%s had no hash or url, won't generate md5sum")
            remote_size = self.package.content_length(url)
            if file.size !=  remote_size:
                raise PackageError("%s is wrong size" % filename)
            if filename.endswith(".zip"):
                if not is_zipfile(file.path):
                    raise PackageError("%s is not a zipfile" % filename)
            elif filename.endswith(".tbz2") or filename.endswith(".bz2"):
                try:
                    b = BZ2File(file.path)
                    b.read()
                except IOError:
                    raise PackageError("%s is not a bzip2 file" % filename)
                else:
                   b.close()
            elif filename.endswith(".tgz") or filename.endswith(".gz"):
                try:
                    g = GzipFile(file.path)
                    g.read()
                except IOError:
                    raise PackageError("%s is not a gzip file" % filename)
                else:
                   g.close()
            file.write_md5(file.md5)

    def rm(self, filename):
        MirrorFile(self, filename).rm()

    def ls(self):
        filenames = []
        for filename in os.listdir(self.path()):
            if os.path.isfile(self.path(filename)) and filename != "index.html"\
               and not filename.endswith(".md5"):
                filenames.append(filename)
        filenames.sort()
        return filenames

    def _html_link(self, base_url, filename, md5_hash):
        if not base_url.endswith('/'):
            base_url += '/'
        return '<a href="%s%s/%s#md5=%s">%s</a>' % (base_url, self.package_name, filename, md5_hash, filename)

    def _index_html(self, base_url):
        header = "<html><head><title>%s &ndash; PyPI Mirror</title></head><body>" % self.package_name
        footer = "</body></html>"

        link_list = []
        for link in self.ls():
            file = MirrorFile(self, link)
            md5_hash = file.md5
            link_list.append(self._html_link(base_url, link, md5_hash))
        links = "<br />\n".join(link_list)
        return "%s%s%s" % (header, links, footer)

    def index_html(self, base_url):
        content = self._index_html(base_url)
        self.write("index.html", content)

    def cleanup(self, original_file_list, verbose=False):
        remote_list = [link[1] for link in original_file_list]
        local_list = self.ls()
        for local_file in local_list:
            if not local_file.endswith(".md5") and \
                    local_file not in remote_list:
                if verbose: 
                    LOG.debug("Removing: %s" % local_file)
                self.rm(local_file)


class MirrorFile(object):
    """ This represents a mirrored file. It doesn't have to
        exist.
    """
    def __init__(self, mirror_package, filename):
        self.path = mirror_package.path(filename)

    @property
    def md5(self):
        # use cached md5 sum if available.
        if os.path.exists(self.md5_filename):
            with open(self.md5_filename,"r") as f:
                return f.read()

        if os.path.exists(self.path):
            with open(self.path, "rb") as f:
                return md5(f.read()).hexdigest()
        return None

    @property
    def size(self):
        if os.path.exists(self.path):
            return os.path.getsize(self.path)
        return 0

    def write(self, data):
        with open(self.path, "wb") as f:
            f.write(data)

    def rm(self):
        """ deletes the file
        """
        if os.path.exists(self.path):
            os.unlink(self.path)
        if os.path.exists(self.md5_filename):
            os.unlink(self.md5_filename)

    def write_md5(self, hash):
        md5_filename = ".%s.md5" % os.path.basename(self.path)
        md5_path = os.path.dirname(self.path)
        with open(os.path.join(md5_path, md5_filename),"w") as f:
            f.write(hash)

    @property
    def md5_filename(self):
        md5_filename = ".%s.md5" % os.path.basename(self.path)
        md5_path = os.path.dirname(self.path)
        return os.path.join(md5_path, md5_filename)

################# Config file parser

default_logfile = os.path.join(tempfile.tempdir or '/tmp', 'pypimirror.log')

config_defaults = {
    'base_url': 'http://your-host.com/index/',
    'mirror_file_path': '/tmp/mirror',
    'lock_file_name': 'pypi-poll-access.lock',
    'filename_matches': '*.zip *.tgz *.egg *.tar.gz *.tar.bz2', # may be "" for *
    'package_matches': "zope.app.* plone.app.*", # may be "" for *
    'cleanup': True, # delete local copies that are remotely not available
    'create_indexes': True, # create index.html files
    'verbose': True, # log output
    'log_filename': default_logfile,
    'external_links': False, # experimental external link resolve and download
    'follow_external_index_pages' : False, # experimental, scan index pages for links
}


# ATT: fix the configuration behaviour (with non-existing configuration files,
# etc.)

def get_config_options(config_filename):
    """
    Get options from the DEFAULT section of our config file
    
    @param dest
    Directory configuration file

    @return
    dict containing a key per option
    values are not reformatted - especially multiline options contain
    newlines
    this contains at least the following key/values:
    - include - Glob-Patterns for package names to include
    - suffixes - list of suffixes to mirror
    """
    if not os.path.exists(config_filename):
        return config_defaults

    config = ConfigParser.ConfigParser(config_defaults)
    config.read(config_filename)
    return config.defaults()


def run(args=None):

    global LOG
    usage = "usage: pypimirror [options] <config-file>"
    parser = optparse.OptionParser(usage=usage)
    parser.add_option('-v', '--verbose', dest='verbose', action='store_true',
                      default=False, help='verbose on')
    parser.add_option('-f', '--log-filename', dest='log_filename', action='store',
                      default=False, help='Name of logfile')
    parser.add_option('-u', '--update', dest='update', action='store_true',
                      default=False, help='PyPI mirror fetch')
    parser.add_option('-c', '--log-console', dest='log_console', action='store_true',
                      default=False, help='Also log to console')
    parser.add_option('-i', '--indexes-only', dest='indexes_only', action='store_true',
                      default=False, help='create indexes only (no mirroring)')
    parser.add_option('-e', '--follow-external-links', dest='external_links', action='store_true',
                      default=False, help='Follow and download external links)')
    parser.add_option('-x', '--follow-external-index-pages', dest='follow_external_index_pages', action='store_true',
                      default=False, help='Follow external index pages and scan for links')
    parser.add_option('-d', '--fetch-since-days', dest='fetch_since_days', action='store',
                      default=7, help='Days in past to fetch for incremental update')
    options, args = parser.parse_args()
    if len(args) != 1:
        parser.error("No configuration file specified")
        sys.exit(1)

    config_file_name = os.path.abspath(args[0])
    config = get_config_options(config_file_name)

    # correct things from config
    filename_matches = config["filename_matches"].split()
    package_matches = config["package_matches"].split()
    cleanup = config["cleanup"] in ("True", "1")
    create_indexes = config["create_indexes"] in ("True", "1")
    verbose = config["verbose"] in ("True", "1") or options.verbose
    external_links = config["external_links"] in ("True", "1") or options.external_links
    follow_external_index_pages = config["follow_external_index_pages"] in ("True", "1") or options.follow_external_index_pages
    log_filename = config['log_filename']
    fetch_since_days = int(config.get("fetch_since_days", 0) or options.fetch_since_days)
    if options.log_filename:
        log_filename = options.log_filename

    if options.update:
       package_list = PypiPackageList().list(base_path=config["mirror_file_path"],
                                             filter_by=package_matches,
                                             fetch_since_days=fetch_since_days)
    else: 
        raise ValueError('To update mirror use --update ')

    mirror = Mirror(config["mirror_file_path"])
    lock = zc.lockfile.LockFile(os.path.join(config["mirror_file_path"], config["lock_file_name"]))
    LOG = getLogger(filename=log_filename,
                    log_console=options.log_console)

    if options.indexes_only:
        mirror.index_html()
    else:
        mirror.mirror(package_list, 
                      filename_matches, 
                      verbose, 
                      cleanup, 
                      create_indexes, 
                      external_links, 
                      follow_external_index_pages,
                      config["base_url"])

if __name__ == '__main__':
    sys.exit(run())

################################################################
# z3c.pypimirror - A PyPI mirroring solution
# Written by Daniel Kraft, Josip Delic, Gottfried Ganssauge and
# Andreas Jung
#
# Published under the Zope Public License 2.1
################################################################

"""
A simple logger for z3c.pypymirror
"""

import logging
import logging.handlers

def getLogger(filename='/tmp/pypymirror.log', log_console=False):

    LOG = logging.getLogger()
    LOG.setLevel(logging.DEBUG)
    formatter = logging.Formatter('%(asctime)s %(levelname)-6s %(message)s')
    filehandler = logging.handlers.TimedRotatingFileHandler(filename, 'D', 1, backupCount=14)
    filehandler.setFormatter(formatter)
    LOG.addHandler(filehandler)
    if log_console:
        streamhandler = logging.StreamHandler()
        streamhandler.setFormatter(formatter)
        LOG.addHandler(streamhandler)
    return LOG

if __name__ == '__main__':
    LOG = getLogger()
    LOG.info('hello')
    LOG.error('hello')
    LOG = getLogger(log_console=True)
    LOG.info('hello')
    LOG.error('hello')

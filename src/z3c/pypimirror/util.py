################################################################
# z3c.pypimirror - A PyPI mirroring solution
# Written by Daniel Kraft, Josip Delic, Gottfried Ganssauge and
# Andreas Jung
#
# Published under the Zope Public License 2.1
################################################################

def isASCII(s):
    """ Checks if a string/unicode string contains only ASCII chars.  """

    if isinstance(s, unicode):
        try:
            s.encode('ascii')
            return True
        except UnicodeError:
            return False

    elif isinstance(s, str):
        try:
            unicode(s, 'ascii')
            return True
        except UnicodeError:
            return False

    else:
        raise TypeError('isASCII() requires a string or unicode string')
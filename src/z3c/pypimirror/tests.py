# *-* coding: iso-8859-15 *-*
"""
Test runner for 'z3c.pypimirror'.
"""
__docformat__ = 'restructuredtext'

import unittest
import zc.buildout.tests
import zc.buildout.testing
import interlude

from zope.testing import doctest, renormalizing

optionflags =  (doctest.ELLIPSIS |
                doctest.NORMALIZE_WHITESPACE |
                doctest.REPORT_ONLY_FIRST_FAILURE)
import util


class UtilityTests(unittest.TestCase):

    def testIsAscii(self):

        self.assertEqual(util.isASCII('foo'), True)
        self.assertEqual(util.isASCII(u'foo'), True)
        self.assertEqual(util.isASCII('���'), False)
        self.assertEqual(util.isASCII(u'���'), False)
        self.assertRaises(TypeError, util.isASCII, 2)


def setUp(test):
    zc.buildout.testing.buildoutSetUp(test)

    # Install the recipe in develop mode
    # zc.buildout.testing.install_develop('boing', test)

    # Install any other recipes that should be available in the tests
    #zc.buildout.testing.install('collective.recipe.foobar', test)

def test_suite():
    suite = unittest.TestSuite((
            doctest.DocFileSuite(
                'README.txt',
                setUp=setUp,
                tearDown=zc.buildout.testing.buildoutTearDown,
                optionflags=optionflags,
                checker=renormalizing.RENormalizing([
                        # If want to clean up the doctest output you
                        # can register additional regexp normalizers
                        # here. The format is a two-tuple with the RE
                        # as the first item and the replacement as the
                        # second item, e.g.
                        # (re.compile('my-[rR]eg[eE]ps'), 'my-regexps')
                        zc.buildout.testing.normalize_path,
                        ]),
                globs=dict(interact=interlude.interact),
                ),
            ))
    suite.addTest(unittest.makeSuite(UtilityTests))
    return suite

if __name__ == '__main__':
    unittest.main(defaultTest='test_suite')

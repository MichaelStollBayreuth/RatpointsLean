#!/usr/bin/env python3
"""Tests of the parsers of scripts/difftest.py.

usage: python3 -m unittest discover -s scripts -p 'test_*.py'
"""
import random
import sys
import unittest
from pathlib import Path
from types import SimpleNamespace

sys.path.insert(0, str(Path(__file__).resolve().parent))
import difftest as dt  # noqa: E402
import difftest_cases  # noqa: E402


class SplitTest4(unittest.TestCase):
    def test_runs(self):
        text = ('==== part\n'
                '# <1 2> <20> <-q>\n(0 : 1 : 1)\n(0 : -1 : 1)\n'
                '# <1 2 3> <abc>\n\nIncorrect height argument.\nexit 4\n'
                '----\n'
                '# <1 0 1> <10\r> <-q> | grep x\nfoo\n')
        runs = dt.split_test4(text)
        self.assertEqual([r.args for r in runs],
                         [['1 2', '20', '-q'], ['1 2 3', 'abc'], ['1 0 1', '10\r', '-q']])
        self.assertEqual(runs[0].out, ['(0 : 1 : 1)', '(0 : -1 : 1)'])
        self.assertEqual(runs[1].out, ['', 'Incorrect height argument.', 'exit 4'])
        self.assertEqual(runs[2].filt, 'grep x')

    def test_glued_and_bare(self):
        runs = dt.split_test4('# <1 2> <5> <-fe> <!>\n(0 : 1 : 1)!# <3> <4>\nx\n#\nexit 2\n')
        self.assertEqual(len(runs), 3)
        self.assertEqual(runs[0].out, ['(0 : 1 : 1)!'])
        self.assertTrue(runs[0].nonl)
        self.assertEqual(runs[1].args, ['3', '4'])
        self.assertEqual(runs[2].args, [])


class Outputs(unittest.TestCase):
    def test_points(self):
        self.assertEqual(dt.points('(0 : 1 : 1)\n(-2 : 0 : 3)\n'), [(-2, 0, 3), (0, 1, 1)])
        self.assertIsNone(dt.points('\nToo many coefficients.\n\n'))
        self.assertEqual(dt.points(''), [])
        self.assertEqual(dt.points('This is it.\n(1 : 1 : 0)\n2 points.\n', report=True),
                         [(1, 1, 0)])

    def test_recorded_by_e(self):
        raw = ('\nWrong syntax for optional arguments:\n\n\nThis is ratpoints-x\n\nnotice\n'
               'Usage: ratpoints ...\n                 [-q] [-v]\n\n')
        self.assertEqual(dt.as_recorded_by_e(raw),
                         '\nWrong syntax for optional arguments:\n\n\n\nnotice\n')
        self.assertEqual(dt.as_recorded_by_e(''), '\n')

    def test_agrees(self):
        cfg = SimpleNamespace(lean_usage='\nThis is ratpoints-lean-0.1\nUsage: L\n',
                              c_usage='\nThis is ratpoints-3.1.1\nUsage: C\n')
        error6 = '\nWrong syntax for optional arguments:\n\n'
        self.assertTrue(dt.agrees(cfg, (error6 + cfg.lean_usage, 6), (error6 + cfg.c_usage, 6),
                                  'exact'))
        self.assertFalse(dt.agrees(cfg, (error6 + cfg.lean_usage, 2), (error6 + cfg.c_usage, 6),
                                   'exact'))
        self.assertTrue(dt.agrees(cfg, ('(0 : 1 : 1)\n(0 : -1 : 1)\n', 0),
                                  ('(0 : -1 : 1)\n(0 : 1 : 1)\n', 0), 'points'))
        self.assertFalse(dt.agrees(cfg, ('(0 : 1 : 1)\n', 0), ('(0 : -1 : 1)\n', 0), 'points'))
        self.assertTrue(dt.agrees(cfg, ('', 0), ('\nfound 0 points.\n', 0), 'report'))
        self.assertTrue(dt.agrees(cfg, ('\nToo many coefficients.\n\n', 3),
                                  ('\nToo many coefficients.\n', 3), 'e'))

    def test_read_options(self):
        self.assertEqual(dt.read_options(['-q', '-n', '5', '-j']), (None, True))
        self.assertEqual(dt.read_options(['-n', '5']), (None, False))
        self.assertEqual(dt.read_options(['-q', '-l', '0', '-u', '1']), (1, True))
        self.assertEqual(dt.read_options(['-p', '-k', '-k']), (2, False))
        self.assertEqual(dt.read_options(['-quiet', '-fs', 'x']), (1, True))
        self.assertEqual(dt.read_options(['-fx', '-k']), (None, False))
        self.assertEqual(dt.read_options(['-d', '1', '-dl', '1']), (None, False))
        self.assertEqual(dt.read_options(['-q', 'q', '-k']), (None, True))
        self.assertEqual(dt.read_options([b'-\xff', '-k']), (None, False))


class Curves(unittest.TestCase):
    def test_plain(self):
        header = ('/* comment {1, 2} */\n#define NUM_TEST 2\n'
                  'long testdata[NUM_TEST][3] = {\n {1, -2, 3},\n // {9, 9, 9},\n {4L, 5, 0}\n};\n')
        self.assertEqual(dt.curves(header), [[1, -2, 3], [4, 5, 0]])

    def test_degrees(self):
        header = ('#define TEST_MAX_DEGREE 8\n'
                  'long testdata[2][10] = { {1, 3, 4, 9, 9}, {2, 1, 0, 1, 7} };\n')
        self.assertEqual(dt.curves(header), [[3, 4], [1, 0, 1]])

    def test_cases(self):
        self.assertTrue(all(isinstance(a, list) and isinstance(n, str)
                            for a, n in difftest_cases.CASES))
        lines = difftest_cases.random_command_lines(random.Random(1))
        self.assertEqual(len(lines), 7)
        self.assertEqual(lines, difftest_cases.random_command_lines(random.Random(1)))

    def test_reference(self):
        self.assertEqual(dt.reference_points('{[1,2,0],[1,-2,0],[-3,6,2]}'),
                         [(1, 2, 0), (1, -2, 0), (-3, 6, 2)])
        self.assertEqual(dt.reference_points('{}'), [])


if __name__ == '__main__':
    unittest.main()

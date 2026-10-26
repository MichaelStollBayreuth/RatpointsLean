#!/usr/bin/env python3
"""Tests of the parsers, the comparisons and the skips of scripts/difftest.py.

usage: python3 -m unittest discover -s scripts -p 'test_*.py'
"""
import random
import sys
import unittest
from fractions import Fraction
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
        self.assertEqual(dt.points('(0 : 1 : 1)\n(-2 : 0 : 3)\n'), [(0, 1, 1), (-2, 0, 3)])
        self.assertIsNone(dt.points('\nToo many coefficients.\n\n'))
        self.assertEqual(dt.points(''), [])
        self.assertEqual(dt.point_lines('This is it.\n(1 : 1 : 0)\n(2 : 3)\n2 points.\n'),
                         ['(1 : 1 : 0)', '(2 : 3)'])

    def test_recorded_by_e(self):
        raw = ('\nWrong syntax for optional arguments:\n\n\nThis is ratpoints-x\n\nnotice\n'
               'Usage: ratpoints ...\n                 [-q] [-v]\n\n')
        self.assertEqual(dt.as_recorded_by_e(raw),
                         '\nWrong syntax for optional arguments:\n\n\n\nnotice\n')
        self.assertEqual(dt.as_recorded_by_e(''), '\n')

    def test_agrees(self):
        cfg = SimpleNamespace(lean_usage='\nThis is ratpoints-lean-0.1\nUsage: L\n',
                              c_usage='\nThis is ratpoints-3.1.1\nUsage: C\n',
                              lean_banner='This is ratpoints-lean-0.1\n\nLean\n\n',
                              c_banner='This is ratpoints-3.1.1\n\nC\n\n')
        error6 = '\nWrong syntax for optional arguments:\n\n'
        self.assertTrue(dt.agrees(cfg, (error6 + cfg.lean_usage, 6), (error6 + cfg.c_usage, 6),
                                  'exact'))
        self.assertFalse(dt.agrees(cfg, (error6 + cfg.lean_usage, 2), (error6 + cfg.c_usage, 6),
                                   'exact'))
        self.assertFalse(dt.agrees(cfg, ('(0 : 1 : 1)\n(0 : -1 : 1)\n', 0),
                                   ('(0 : -1 : 1)\n(0 : 1 : 1)\n', 0), 'points'))
        self.assertTrue(dt.agrees(cfg, ('(0 : 1 : 1)\n(0 : -1 : 1)\n', 0),
                                  ('(0 : 1 : 1)\n(0 : -1 : 1)\n', 0), 'points'))
        self.assertFalse(dt.agrees(cfg, ('(0 : 1 : 1)\n', 0), ('(0 : -1 : 1)\n', 0), 'points'))
        self.assertTrue(dt.agrees(cfg, ('1 0%0 1%', 0), ('1 0%0 1%', 0), 'exact'))
        self.assertFalse(dt.agrees(cfg, ('1 0%0 1%\n', 0), ('1 0%0 1%', 0), 'exact'))
        self.assertTrue(dt.agrees(cfg, ('\nToo many coefficients.\n\n', 3),
                                  ('\nToo many coefficients.\n', 3), 'e'))
        report = '\n{}\n\nCurve equation is  y^2 = 5\n\n\nPolynomial is not square-free.\n\n'
        self.assertTrue(dt.agrees(cfg, (report.format(cfg.lean_banner), 8),
                                  (dt.as_recorded_by_e(report.format(cfg.c_banner)), 8), 'e'))

    def test_report(self):
        cfg = SimpleNamespace(lean_banner='This is ratpoints-lean-0.1\n\nLean\n\n',
                              c_banner='This is ratpoints-3.1.1\n\nC\n\n')
        head = '\n{}\n\nCurve equation is  y^2 = x^2 + 1\n\nmax. Height = 5\n\n'
        c = (head.format(cfg.c_banner) + '(1 : 1 : 0)\n\n\n3 moduli used for first stage of '
             'sieving,\n4 moduli used for both stages of sieving together,\n0 further primes '
             'used in the third stage.\nSearch intervals:\n[-5.000000, 5.000000]\n\n'
             '2 rational points found.\n\n')
        lean = (head.format(cfg.lean_banner) + '(1 : 1 : 0)\n\n\nSearch intervals:\n'
                '[-5.000000, 5.000000]\n\n2 rational points found.\n\n')
        self.assertTrue(dt.agrees(cfg, (lean, 0), (c, 0), 'report'))
        # messages 3 and 8 are compared: another search interval, no search region
        self.assertFalse(dt.agrees(cfg, (lean, 0), (c.replace('[-5.000000', '[-4.000000'), 0),
                                   'report'))
        region = 'max. Height = 5\n\nSearch region:\n  [0.000000, 1.000000]\n'
        self.assertFalse(dt.agrees(cfg, (lean, 0), (c.replace('max. Height = 5\n\n', region), 0),
                                   'report'))
        self.assertFalse(dt.agrees(cfg, (lean, 0), (c.replace('2 rational', '3 rational'), 0),
                                   'report'))
        # as test4.sh's m() records it: the first line of the banner and message 4 left out
        m = '\n'.join(l for l in c.split('\n') if not l.startswith('This is ratpoints-') and
                      'used for' not in l and 'further primes' not in l)
        self.assertTrue(dt.agrees(cfg, (lean, 0), (m, 0), 'report'))
        # the lines that ratpoints-lean does not print are dropped from the C program's only
        c_banner = c.replace(cfg.c_banner, cfg.lean_banner)
        self.assertFalse(dt.agrees(cfg, (c_banner, 0), (c, 0), 'report'))
        refusal = '\nPolynomial is not square-free.\n\n'
        self.assertTrue(dt.agrees(cfg, (head.format(cfg.lean_banner) + refusal, 8),
                                  (head.format(cfg.c_banner) + refusal, 8), 'report'))
        self.assertFalse(dt.agrees(cfg, (refusal, 8), (head.format(cfg.c_banner) + refusal, 8),
                                   'report'))

    def test_verbose(self):
        c = ('\nB\n\nCurve equation is  y^2 = x^2 + 1\n\nmax. Height = 5\n\nSE\n\n'
             '7 moduli used for first stage of sieving,\nx\nPolynomial was reversed for better '
             'performance.\nSearch intervals:\n[-5.000000, 5.000000]\n\n4 rational points '
             'found.\n\n')
        v = '\nB\n\nCurve equation is  y^2 = x^2 + 1\n\nSE\n4 rational points found.\n\n'
        self.assertEqual(dt.as_verbose(c), v)
        out = ('\nB\n\nCurve equation is  y^2 = x^2 + 1\n\nlib\n(1 : 1 : 0)\nSE\n'
               '4 rational points found.\n\n')
        exp = ('\nB\n\nCurve equation is  y^2 = x^2 + 1\n\n(1 : 1 : 0)\nSE\n'
               '4 rational points found.\n\n')
        self.assertTrue(dt.verbose_consistent(exp, out))
        # a point dropped, a count changed, lines out of order
        self.assertFalse(dt.verbose_consistent(exp.replace('(1 : 1 : 0)\n', ''), out))
        self.assertFalse(dt.verbose_consistent(exp.replace('4 rational', '1 rational'), out))
        self.assertFalse(dt.verbose_consistent('SE\nlib\n', out))
        # with a format, the library may write into a line of points
        exp, out = 'B\n-x-x-x\n4 found\n', 'B\n-x\nlib\n-x-x\n4 found\n'
        self.assertTrue(dt.verbose_consistent(exp, out, True))
        self.assertFalse(dt.verbose_consistent(exp, out))

    def test_filters(self):
        cfg = SimpleNamespace(lean_usage='', c_usage='', lean_banner='L\n\nl\n',
                              c_banner='C\n\nc\nd\n')
        out = '\nB\n\nCurve equation is  y^2 = x\n(1 : 0 : 0)\n\n2 rational points found.\n\n'
        self.assertTrue(dt.agrees(cfg, (out, 0), ('2 rational points found.\n', 0),
                                  'filter:grep found'))
        self.assertTrue(dt.agrees(cfg, (out, 0), ('Curve equation is  y^2 = x\n', 0),
                                  "filter:grep 'Curve equation'"))
        self.assertTrue(dt.agrees(cfg, ('(0 : 1 : 1)\n(0 : -1 : 1)', 0), ('2\n', 0),
                                  'filter:grep -c .'))
        self.assertTrue(dt.agrees(cfg, ('', 0), ('', 0), 'filter:grep found'))
        # the exit code: every filtered run is a search, which exits with 0
        self.assertFalse(dt.agrees(cfg, (out, -11), ('2 rational points found.\n', 0),
                                   'filter:grep found'))
        # the banner is exchanged before the filter
        self.assertTrue(dt.agrees(cfg, ('\nL\n\nl\n\n(0 : 1 : 1)\n', 0), ('4\n', 0),
                                  'filter:grep -c .'))

    def test_weak(self):
        st = dt.Settings(quiet=True, x=True)
        args = ['1 0 1', '5', '-q', '-x']
        # (1 : 0), (0 : 1) are points of y^2 = x^2 + 1; (2 : 1) and (1 : 2) are not
        self.assertTrue(dt.weak_agrees('(1 : 0)\n(2 : 1)\n(0 : 1)\n', '(1 : 0)\n(0 : 1)\n(1 : 2)\n',
                                       args, st))
        self.assertFalse(dt.weak_agrees('(0 : 1)\n(1 : 0)\n', '(1 : 0)\n(0 : 1)\n', args, st))
        self.assertFalse(dt.weak_agrees('(1 : 0)\n(2 : 2)\n(0 : 1)\n', '(1 : 0)\n(0 : 1)\n',
                                        args, st))
        self.assertFalse(dt.weak_agrees('(1 : 0)\n(6 : 1)\n(0 : 1)\n', '(1 : 0)\n(0 : 1)\n',
                                        args, st))
        # a repeated pair; common pairs in another order
        self.assertFalse(dt.weak_agrees('(1 : 0)\n(2 : 1)\n(2 : 1)\n(0 : 1)\n',
                                        '(1 : 0)\n(0 : 1)\n', args, st))
        self.assertFalse(dt.weak_agrees('(1 : 0)\n(2 : 1)\n(1 : 2)\n(0 : 1)\n',
                                        '(1 : 0)\n(1 : 2)\n(2 : 1)\n(0 : 1)\n', args, st))
        one = dt.Settings(x=True, one=True)
        self.assertTrue(dt.weak_agrees('x\n(2 : 1)\n\n1 rational point pairs found.\n',
                                       'x\n(1 : 2)\n\n1 rational point pairs found.\n', args, one))
        self.assertFalse(dt.weak_agrees('x\n(2 : 1)\n\n2 rational point pairs found.\n',
                                        'x\n(1 : 2)\n\n1 rational point pairs found.\n', args,
                                        dt.Settings(x=True)))
        # under -1: no line against a point, two different points, a count 0 against a point
        q1 = dt.Settings(quiet=True, x=True, one=True)
        self.assertFalse(dt.weak_agrees('', '(1 : 0)\n', args, q1))
        self.assertFalse(dt.weak_agrees('(1 : 0)\n', '(0 : 1)\n', args, q1))
        self.assertTrue(dt.weak_agrees('(2 : 1)\n', '', args, q1))
        self.assertFalse(dt.weak_agrees('x\n\n0 rational point pairs found.\n',
                                        'x\n(1 : 0)\n\n1 rational point pairs found.\n', args, one))
        # the wording of the count, and the place of the pairs and of the count
        self.assertFalse(dt.weak_agrees('x\n(1 : 0)\n\n1 rational points found.\n',
                                        'x\n(1 : 0)\n\n1 rational point pairs found.\n', args,
                                        dt.Settings(x=True)))
        self.assertFalse(dt.weak_agrees('x\n\n(1 : 0)\n1 rational point pairs found.\n',
                                        'x\n(1 : 0)\n\n1 rational point pairs found.\n', args,
                                        dt.Settings(x=True)))
        self.assertFalse(dt.weak_agrees('1 rational point pairs found.\nx\n(1 : 0)\n\n',
                                        'x\n(1 : 0)\n\n1 rational point pairs found.\n', args,
                                        dt.Settings(x=True)))
        self.assertFalse(dt.weak_agrees('(1 : 0)\nx\n(0 : 1)\n', '(1 : 0)\n(0 : 1)\nx\n', args,
                                        st))
        self.assertTrue(dt.is_point([1, 0, 1], 1, 0) and dt.is_point([0, 1, 2], 0, 1) and
                        dt.is_point([-2, 0, 0, 1], 129, 100) and not dt.is_point([1, 0, 1], 2, 1))

    def test_weak_region(self):
        # the pairs must lie in the range of the denominators and in the exact search region
        args = ['1 0 1', '20', '-q', '-x', '-p', '10', '-dl', '5', '-du', '9', '-l', '0', '-u', '1']
        st = dt.settings(args[2:])
        self.assertTrue(dt.weak_agrees('(1 : 0)\n(3 : 5)\n', '(1 : 0)\n', args, st))
        for extra in ['(-7 : 3)\n', '(19 : 2)\n', '(7 : 5)\n', '(-1 : 9)\n']:
            self.assertFalse(dt.weak_agrees('(1 : 0)\n(3 : 5)\n' + extra, '(1 : 0)\n', args, st))
            self.assertFalse(dt.weak_agrees('(1 : 0)\n', '(1 : 0)\n(3 : 5)\n' + extra, args, st))
        # the ends of the command line, exact: an end that is no double, and a missing first -l
        st = dt.settings(['-u', '0.1', '-l', '0x1p-1', '-q'])
        self.assertEqual(dt.exact_region(st),
                         [(-float('inf'), Fraction(1, 10)), (Fraction(1, 2), float('inf'))])
        ivs = dt.exact_region(st)
        self.assertEqual([dt.in_region(Fraction(n, d), ivs) for n, d in
                          [(-10 ** 18, 1), (1, 10), (1, 9), (1, 2), (10 ** 18, 3)]],
                         [True, True, False, True, True])
        self.assertEqual(dt.exact_region(dt.settings(['-q'])), [])
        self.assertFalse(dt.in_region(Fraction(0), [(Fraction(1), Fraction(2))]))

    def test_correction_possible(self):
        def cp(args):
            return dt.correction_possible(args, dt.settings(args[2:]))
        self.assertTrue(cp(['1 0 1', '30000', '-q', '-x']))
        self.assertFalse(cp(['1 0 1', '1000', '-q', '-x']))  # 1000 * 9 * 4 words at most
        self.assertFalse(cp(['1 0 1', '30000', '-q', '-x', '-n', '5']))
        self.assertFalse(cp(['1 0 1', '30000', '-q', '-x', '-N', '0']))
        self.assertTrue(cp(['1 0 1', '30000', '-q', '-x', '-n', '-1']))
        self.assertFalse(cp(['1 0 1', '30000', '-q', '-x', '-A', '0']))
        self.assertTrue(cp(['1 0 1', '30000', '-q', '-x', '-A', '2']))
        self.assertFalse(cp(['1 0 1', '30000', '-q', '-x', '-dl', '1', '-du', '100']))

    def test_tuned(self):
        def tuned(opts):
            return dt.settings(opts).tuned
        self.assertFalse(tuned(['-q', '-x', '-p', '30', '-N', '30', '-F', '5', '-t', '4']))
        self.assertFalse(tuned(['-q', '-x', '-A', '1']))
        self.assertFalse(tuned(['-q', '-x', '-A', '-3']))
        self.assertTrue(tuned(['-q', '-x', '-A', '0']))
        self.assertTrue(tuned(['-q', '-x', '-A', '2']))
        self.assertTrue(tuned(['-q', '-x', '-r', '0.5']))
        self.assertTrue(tuned(['-q', '-x', '-W', '1e6', '-A', '1']))

    def test_stderr(self):
        cfg = SimpleNamespace(lean_usage='U', c_usage='U')
        ok = ('(0 : 1 : 1)\n', 0, '')
        self.assertTrue(dt.verdict(cfg, ok, ('(0 : 1 : 1)\n', 0), 'exact'))
        panic = ('(0 : 1 : 1)\n', 0, 'PANIC at Ratpoints.Sieve.walkWord: index out of bounds\n')
        self.assertFalse(dt.verdict(cfg, panic, ('(0 : 1 : 1)\n', 0), 'exact'))
        self.assertIn('standard error', dt.failure_text('l', ('', 0), panic))

    def test_lean_environment(self):
        cfg = SimpleNamespace(lean='/bin/sh')
        out, code, err = dt.run_lean(cfg, ['-c', 'printf %s "$LEAN_ABORT_ON_PANIC"; echo e >&2'])
        self.assertEqual((out, code, err), ('1', 0, 'e\n'))

    def test_option_words(self):
        def stop(opts):
            return dt.option_words(opts)[1]
        self.assertEqual(stop(['-q', '-n', '5', '-j']), None)
        self.assertEqual(stop(['-q', '-l', '0', '-u', '1']), None)
        self.assertEqual(stop(['-p', '-x', '-u']), 2)  # -u without its argument
        self.assertEqual(stop(['-quiet', '-fs', 'x', '-dl']), 3)
        self.assertEqual(stop(['-fx', '-u']), 0)
        self.assertEqual(stop(['-f', '-u', '-q']), None)
        self.assertEqual(stop(['-d', '1', '-dl', '1']), 0)
        self.assertEqual(stop(['-dlx', '1', '-du', '2', '-q', 'q']), 5)
        self.assertEqual(stop([b'-\xff', '-u']), 0)
        self.assertEqual(stop(['-S', '5', '-l', '-1']), None)
        self.assertEqual(stop(['-S', '-q', '-u', '2']), None)
        self.assertEqual(stop(['-S', ' -1', '-k']), None)
        self.assertEqual(stop(['-lfoo', '1', '-ux', '2']), None)

    def test_settings(self):
        st = dt.settings(['-v', '-x', '-p', ' 30', '-N', '30', '-f', '-q', '-y', '-Y', '-zap'])
        # -f takes -q as its format
        self.assertEqual((st.quiet, st.verbose, st.x, st.y, st.z, st.strings, st.N),
                         (False, True, True, False, True, True, 30))
        self.assertEqual(st.v_words, [0])
        st = dt.settings(['-v', '-xfoo', '-X', '-q', '-1', '-p', '30', '-n', '4', '-A', '0'])
        self.assertEqual((st.quiet, st.verbose, st.x, st.one, st.n, st.A, st.plain),
                         (True, False, False, True, 4, 0, True))
        self.assertEqual(dt.mode_of(dt.settings(['-q', '-y']), 0), 'exact')
        self.assertEqual(dt.mode_of(dt.settings(['-q', '-i', '-1']), 0), 'points')
        self.assertEqual(dt.mode_of(dt.settings(['-x']), 0), 'report')
        self.assertEqual(dt.mode_of(dt.settings(['-x', '-q']), 0), 'exact')
        self.assertEqual(dt.live_mode(dt.mode_of(dt.settings(['-q']), 0)), 'exact')
        self.assertEqual(dt.mode_of(dt.settings([]), 8), 'report')
        self.assertEqual(dt.mode_of(dt.settings(['-q']), 8), 'exact')
        self.assertEqual(dt.mode_of(dt.settings(['-x']), 6), 'exact')
        st = dt.settings(['-l', '0', '-u', '0x1p-3', '-dl', '5', '-du', ' 9', '-q'])
        self.assertEqual((st.ends, st.dl, st.du, st.region, st.quiet),
                         ([('l', '0'), ('u', '0x1p-3')], 5, 9, True, True))
        self.assertFalse(dt.settings(['-q', '-S', '3', '-k']).region)
        self.assertTrue(dt.settings(['-du', '0']).region)


class Skips(unittest.TestCase):
    def test_skips_height(self):
        cfg = SimpleNamespace(max_height=30000)

        def skips(args, out, code):
            return dt.skips_height(cfg, args, out, code, dt.settings(args[2:]))
        self.assertFalse(skips(['2 0 3', '40000', '-q'], '', 0))
        self.assertTrue(skips(['1 0 1', '40000', '-q'], '(0 : 1 : 1)\n', 0))
        self.assertFalse(skips(['1 0 1', '30000', '-q'], '(0 : 1 : 1)\n', 0))
        self.assertFalse(skips(['0 0 1', '40000'], '\nerror\n', 1))
        # a narrow search region at a large height is compared
        self.assertFalse(skips(['1 0 1', '4611686018427387904', '-q', '-dl', '4294967295', '-du',
                                '4294967295', '-l', '9544371.76666664', '-u', '9544371.766689923'],
                               '(1 : 1 : 0)\n', 0))
        # too many denominators, too many numerators
        self.assertTrue(skips(['1 0 1', '1000000', '-q', '-dl', '2'], '(1 : 1 : 0)\n', 0))
        self.assertTrue(skips(['1 0 1', '10000000000000', '-q', '-du', '9000'], '(1 : 1 : 0)\n',
                              0))
        # a search region with an empty output is not exempt
        self.assertTrue(skips(['1 0 1', '100000000', '-q', '-l', '0', '-u', '1'], '', 0))
        # a hexadecimal end beyond the doubles is infinite
        self.assertTrue(skips(['1 0 1', '1000000000', '-q', '-u', '0x1p2000', '-dl', '1', '-du',
                               '1000'], '(1 : 1 : 0)\n', 0))
        self.assertEqual((dt.end_value('0x1p2000'), dt.end_value('-0x1p2000 ')),
                         (float('inf'), -float('inf')))
        # under -1 the numerators up to the stop at the first point: none at a point at infinity,
        # the first numerator of the first denominator, a later denominator; all of them without a
        # point, and when the polynomial may be reversed (the search region is the whole box)
        big = ['1 0 1', '10000000000000', '-q', '-du', '16', '-1']
        self.assertFalse(skips(big, '(1 : 1 : 0)\n', 0))
        self.assertFalse(skips(big, '(-10000000000000 : 5 : 1)\n', 0))
        self.assertFalse(skips(big[:-1] + ['-x', '-1'], '(-10000000000000 : 1)\n', 0))
        self.assertTrue(skips(big, '(-10000000000000 : 5 : 9)\n', 0))
        self.assertTrue(skips(big, '', 0))
        self.assertTrue(skips(['1 0 0 1', '1000000000', '-q', '-dl', '1', '-1'], '(1 : 0 : 0)\n',
                              0))
        self.assertFalse(skips(['1 0 0 1', '1000000000', '-q', '-dl', '2', '-1'], '(1 : 0 : 0)\n',
                               0))

    def test_denominators(self):
        # every denominator; the squares (odd degree, |c_d| = 1); the divisors of c_d = 12 that are
        # squarefree (1, 2, 3, 6) times squares
        self.assertEqual(dt.denominators([1, 0, 1], 1, 100), 100)
        self.assertEqual(dt.denominators([1, 0, 0, -1], 1, 100), 10)
        self.assertEqual(dt.denominators([1, 0, 0, 1, 0], 10, 100), 7)
        self.assertEqual(dt.denominators([5, 0, 0, 12], 1, 100), 10 + 7 + 5 + 4)
        self.assertEqual(dt.denominators([1, 0, 1], 5, 3), 0)
        self.assertEqual(dt.den_shape([5, 0, 0, 12], 100), ('divisors', [1, 2, 3, 6]))
        self.assertEqual((dt.end_value('0x1p-3'), dt.end_value(' -1e400 '), dt.end_value('x')),
                         (0.125, -float('inf'), None))
        # a factorization over the table that is not complete (1052651 = 1021 * 1031) gives every
        # denominator, as Ratpoints.Setup.setupUs1 fails then
        self.assertEqual(dt.factor_lcf(1052651), ([1021], 1031))
        self.assertEqual(dt.factor_lcf(2 ** 5 * 3 * 1031), ([2, 3, 1031], 1))
        self.assertEqual(dt.denominators([1, 0, 0, 1052651], 1, 1000), 1000)
        # 511 squarefree divisors at most 2066 give the divisor shape, 512 at most 2067 every
        # denominator (the guard of Ratpoints.Setup.setupUs1 at the boundary of maxDivisors)
        lcf = 2305567963945518424753102147331756070
        kind, divs = dt.den_shape([1, 0, 0, lcf], 2066)
        self.assertEqual((kind, len(divs)), ('divisors', 511))
        self.assertEqual(dt.den_shape([1, 0, 0, lcf], 2067), ('all', None))
        self.assertEqual(dt.denominators([1, 0, 0, lcf], 1, 2067), 2067)


class StopCases(unittest.TestCase):
    def test_stop_case_timeout(self):
        cfg = SimpleNamespace(c='/bin/true', lean='/bin/sleep', verbose=False)
        tally = dt.Tally()
        timeout, dt.STOP_TIMEOUT = dt.STOP_TIMEOUT, 1
        try:
            dt.stop_case(cfg, tally, 'sleep', ['5'])
        finally:
            dt.STOP_TIMEOUT = timeout
        self.assertEqual((tally.compared, len(tally.failures)), (1, 1))


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
        self.assertTrue(all(isinstance(a, list) and isinstance(n, str)
                            for a, n in difftest_cases.STOP_CASES))
        lines = difftest_cases.random_command_lines(random.Random(1))
        self.assertEqual(len(lines), 8)
        self.assertEqual(lines, difftest_cases.random_command_lines(random.Random(1)))
        self.assertEqual(difftest_cases.random_output_options(random.Random(2)),
                         difftest_cases.random_output_options(random.Random(2)))
        self.assertEqual(difftest_cases.random_region_line(random.Random(3)),
                         difftest_cases.random_region_line(random.Random(3)))
        self.assertEqual(difftest_cases.random_depth_line(random.Random(4)),
                         difftest_cases.random_depth_line(random.Random(4)))
        self.assertEqual([difftest_cases.end_fraction(w) for w in
                          ['0x1.8p-1', '-0x.4p3', '1e-400', '-1e400', 'INF', '2.5']],
                         [Fraction(3, 4), -2, Fraction(1, 10 ** 400), -float('inf'), float('inf'),
                          Fraction(5, 2)])

    def test_reference(self):
        self.assertEqual(dt.reference_points('{[1,2,0],[1,-2,0],[-3,6,2]}'),
                         [(1, 2, 0), (1, -2, 0), (-3, 6, 2)])
        self.assertEqual(dt.reference_points('{}'), [])


if __name__ == '__main__':
    unittest.main()

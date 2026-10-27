#!/usr/bin/env python3
"""Tests of scripts/constants_check.py that need no lake: the variants against the constants of the
repository, the values as Lean writes them, the option --variant, and the removal of the `#guard`
commands, on examples and on every Lean file of the library.

usage: python3 -m unittest discover -s scripts -p 'test_*.py'
"""
import re
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import constants_check as cc  # noqa: E402

REPO = Path(cc.DEFAULT_REPO)
CONSTANTS = (REPO / cc.CONSTANTS_FILE).read_text(encoding='utf-8')


class Variants(unittest.TestCase):
    def test_builtin_variants_fit_the_constants(self):
        cc.check_variants(cc.VARIANTS, CONSTANTS)

    def test_set_constants(self):
        for name, consts in cc.VARIANTS.items():
            text = cc.set_constants(CONSTANTS, consts)
            for key, value in consts.items():
                with self.subTest(variant=name, constant=key):
                    m = cc.const_line_re(key).search(text)
                    self.assertEqual(m.group('value'), cc.lean_value(value))

    def test_set_constants_examples(self):
        text = cc.set_constants(CONSTANTS, cc.VARIANTS['B'])
        for line in ('def chunk : Nat := 17', 'def useLongInPhase2 : Bool := false',
                     'def defaultSturm : Int := 62', 'def blockLen : Option Nat := none',
                     'def costSetup : Float := 0.0', 'def survivorsPerWord : Float := 1e-12'):
            self.assertIn(line + '\n', text)

    def test_unknown_constant(self):
        with self.assertRaises(cc.SetupError):
            cc.check_variants({'X': {'noSuchConstant': 1}}, CONSTANTS)
        with self.assertRaises(cc.SetupError):
            cc.set_constants('def a : Nat := 1\n', {'b': 2})

    def test_wrong_kind(self):
        for consts in ({'useLongInPhase2': 1}, {'chunk': True}, {'chunk': 1.5},
                       {'costSetup': 3}, {'blockLen': 3}, {'chunk': cc.Opt(3)}):
            with self.subTest(consts=consts), self.assertRaises(cc.SetupError):
                cc.check_variants({'X': consts}, CONSTANTS)

    def test_twice(self):
        with self.assertRaises(cc.SetupError):
            cc.set_constants('def a : Nat := 1\ndef a : Nat := 2\n', {'a': 3})


class Values(unittest.TestCase):
    def test_lean_value(self):
        for value, lean in ((True, 'true'), (False, 'false'), (-1, '-1'), (17, '17'),
                            (0.5, '0.5'), (1e9, '1000000000.0'), (1e-12, '1e-12'),
                            (cc.Opt(None), 'none'), (cc.Opt(3), 'some 3')):
            with self.subTest(value=value):
                self.assertEqual(cc.lean_value(value), lean)

    def test_parse_variant(self):
        self.assertEqual(cc.parse_variant('X1:chunk=3, useLongInPhase2=false,costSetup=1e9,'
                                          'defaultSturm=-1,survivorsPerWord=0.25'),
                         ('X1', {'chunk': 3, 'useLongInPhase2': False, 'costSetup': 1e9,
                                 'defaultSturm': -1, 'survivorsPerWord': 0.25}))

    def test_parse_variant_errors(self):
        for spec in ('X', 'X:', ':chunk=1', 'X:chunk', 'X:chunk=1,chunk=2', 'X:chunk=foo',
                     'X:blockLen=none', 'a/b:chunk=1'):
            with self.subTest(spec=spec), self.assertRaises(cc.SetupError):
                cc.parse_variant(spec)


EXAMPLE = '''def f : Nat := 1

#guard f = 1

open Foo in
#guard f
  = 1
theorem t : f = 1 := rfl
/--
info: x
-/
#guard_msgs in
#print axioms t
/-
#guard f = 2
-/
'''


class Guards(unittest.TestCase):
    def test_example(self):
        text, removed, line_map = cc.strip_guards(EXAMPLE, 'Example.lean')
        self.assertEqual(removed, 2)
        self.assertEqual(line_map, [1, 2, 4, 8, 9, 10, 11, 12, 13, 14, 15, 16])
        lines = EXAMPLE.splitlines(keepends=True)
        self.assertEqual(text, ''.join(lines[n - 1] for n in line_map))
        self.assertIn('#guard_msgs in\n', text)
        self.assertIn('/-\n#guard f = 2\n-/\n', text)
        self.assertNotIn('open Foo in', text)

    def test_unclear_end(self):
        with self.assertRaises(cc.SetupError):
            cc.strip_guards('#guard f\n= 1\n', 'Example.lean')

    def test_library(self):
        """Every Lean file of the library loses its `#guard` commands and nothing else that the
        build needs: no `#guard` command is left outside comments, and every `#guard_msgs`
        stays."""
        total = 0
        for path in sorted((REPO / cc.GUARD_DIR).rglob('*.lean')):
            rel = path.relative_to(REPO).as_posix()
            text = path.read_text(encoding='utf-8')
            with self.subTest(file=rel):
                new_text, removed, _ = cc.strip_guards(text, rel)
                total += removed
                self.assertEqual(new_text.count('#guard_msgs'), text.count('#guard_msgs'))
                depth = 0
                for line in new_text.splitlines():
                    if depth == 0:
                        self.assertIsNone(cc.GUARD_RE.match(line), line)
                    depth = cc.block_depth_after(depth, line)
        self.assertGreater(total, 0)


if __name__ == '__main__':
    unittest.main()

#!/usr/bin/env python3
"""Tests of scripts/check_layout.py on a throwaway source tree.

usage: python3 -m unittest discover -s scripts -p 'test_*.py'
"""
import contextlib
import io
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_layout as cl  # noqa: E402

GOOD = {
    'Ratpoints.lean': 'module\npublic import Ratpoints.Model\npublic import Ratpoints.Spec\n'
                      'public import Ratpoints.Proof\n',
    'Ratpoints/Model.lean': 'module\npublic import Ratpoints.Model.A\n',
    'Ratpoints/Model/A.lean': 'module\npublic import Std.Data.HashMap\n'
                              '-- a partial def in a comment\n/-- a docstring: native_decide -/\n'
                              'def f : Nat := 1\n',
    'Ratpoints/Spec.lean': 'module\npublic import Mathlib.Data.Int.GCD\n',
    'Ratpoints/Proof.lean': 'module\npublic import Ratpoints.Model\npublic import Ratpoints.Spec\n'
                            'public import Mathlib.Tactic\n',
    'comparator/Challenge.lean': 'module\npublic import Mathlib.Data.Int.GCD\n'
                                 'public import Ratpoints.Model\n',
    'comparator/Solution.lean': 'module\npublic import Ratpoints\n',
    'Ratpoints/Fast.lean': 'module\npublic import Ratpoints.Fast.Mask\n'
                           'public import Ratpoints.Fast.B\n',
    'Ratpoints/Fast/Mask.lean': 'module\n@[extern c inline "#1"] def f (n : Nat) : Nat := n\n',
    'Ratpoints/Fast/B.lean': 'module\npublic import Ratpoints.Model.A\n',
}


class Layout(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.saved = cl.ROOT
        cl.ROOT = Path(self.tmp.name)

    def tearDown(self):
        cl.ROOT = self.saved
        self.tmp.cleanup()

    def run_with(self, changes):
        files = dict(GOOD, **changes)
        for rel, text in files.items():
            p = cl.ROOT / rel
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(text)
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = cl.main()
        return code, out.getvalue()

    def test_good(self):
        code, out = self.run_with({})
        self.assertEqual(code, 0, out)

    def test_model_imports(self):
        code, out = self.run_with({'Ratpoints/Model/A.lean': 'module\nimport Mathlib.Tactic\n',
                                   'Main.lean': 'import Lean\n'})
        self.assertEqual(code, 1)
        self.assertIn('FAIL import-model Ratpoints/Model/A.lean:2', out)
        self.assertIn('FAIL import-main Main.lean:1', out)

    def test_model_restrictions(self):
        body = ('module\nset_option experimental.vcgen true\npartial def g : Nat → Nat := id\n'
                'unsafe def h : Nat := 0\n@[implemented_by h] def k : Nat := 0\n'
                '@[extern "lean_k"] opaque m : Nat\n')
        code, out = self.run_with({'Ratpoints/Model/A.lean': body})
        self.assertEqual(code, 1)
        for rule in ('experimental', 'partial', 'unsafe', 'implemented_by', 'extern'):
            self.assertIn(f'FAIL {rule} Ratpoints/Model/A.lean', out)

    def test_fast_restrictions(self):
        code, out = self.run_with({
            'Ratpoints/Fast/B.lean': 'module\nimport Mathlib.Tactic\n'
                                     '@[extern "c_g"] def g : Nat := 0\n'
                                     'partial def h : Nat → Nat := id\n',
            'Ratpoints/Fast/C.lean': 'module\n',
            'ModelMain.lean': 'import Lean\n'})
        self.assertEqual(code, 1)
        self.assertIn('FAIL import-fast Ratpoints/Fast/B.lean:2', out)
        self.assertIn('FAIL extern Ratpoints/Fast/B.lean:3', out)
        self.assertIn('FAIL partial Ratpoints/Fast/B.lean:4', out)
        self.assertIn('FAIL root Ratpoints/Fast.lean', out)
        self.assertIn('FAIL import-main ModelMain.lean:1', out)
        self.assertNotIn('Ratpoints/Fast/Mask.lean', out)

    def test_axioms_everywhere(self):
        code, out = self.run_with({
            'Ratpoints/Proof.lean': GOOD['Ratpoints/Proof.lean'] +
            'example : 2 + 2 = 4 := by native_decide\nexample : True := by decide +native\n',
            'comparator/Solution.lean': GOOD['comparator/Solution.lean'] +
            'example (x : BitVec 2) : x = x := by bv_decide\n'})
        self.assertEqual(code, 1)
        self.assertEqual(out.count('FAIL axiom'), 3, out)

    def test_spec_and_challenge_imports(self):
        code, out = self.run_with({
            'Ratpoints/Spec.lean': 'module\npublic import Ratpoints.Model\n'
                                   'public import Ratpoints.Mathlib.Foo\n',
            'Ratpoints/Mathlib/Foo.lean': 'module\npublic import Mathlib.Tactic\n',
            'comparator/Challenge.lean': 'module\npublic import Ratpoints.Spec\n'})
        self.assertEqual(code, 1)
        self.assertIn('FAIL import-spec Ratpoints/Spec.lean:2', out)
        self.assertIn('FAIL import-spec Ratpoints/Spec.lean:3', out)  # Mathlib only
        self.assertIn('FAIL import-challenge comparator/Challenge.lean:2', out)

    def test_roots(self):
        code, out = self.run_with({'Ratpoints/Model/B.lean': 'module\n',
                                   'Ratpoints/Proof/C.lean': 'module\n'})
        self.assertEqual(code, 1)
        self.assertIn('Ratpoints.Model does not import Ratpoints.Model.B', out)
        self.assertIn('Ratpoints.Proof does not import Ratpoints.Proof.C', out)

    def test_import_all(self):
        code, out = self.run_with({
            'Ratpoints/Model.lean': 'module\npublic import Ratpoints.Model.A\n'
                                    'import all Ratpoints.Model.B\n',
            'Ratpoints/Model/B.lean': 'module\n'})
        self.assertEqual(code, 0, out)

    def test_transitive_root(self):
        code, out = self.run_with({
            'Ratpoints/Model/A.lean': 'module\npublic import Ratpoints.Model.B\n',
            'Ratpoints/Model/B.lean': 'module\n'})
        self.assertEqual(code, 0, out)


if __name__ == '__main__':
    unittest.main()

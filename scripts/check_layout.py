#!/usr/bin/env python3
"""Checks the layering of the Lean sources (README.md, Layout) and the restrictions on the model.

usage: scripts/check_layout.py

Prints `FAIL <rule> <file>:<line>: <text>` for every violation and exits 1 if there is one.

- Imports. The model (`Ratpoints/Model`) imports only Lean core and `Std`; the specification
  (`Ratpoints/Spec`) only Mathlib, so that it can be read without the model; the candidates for
  Mathlib (`Ratpoints/Mathlib`) only Mathlib and its dependencies; `comparator/Challenge.lean`
  only Mathlib and the model (it restates the specification); `Main.lean` only the model.
- Roots. The part roots `Ratpoints/Model.lean`, `Ratpoints/Spec.lean` and `Ratpoints/Proof.lean`
  import, directly or not, every module of their folder, so that `lake build RatpointsModel`
  builds the whole model and `scripts/Correspondence.lean` sees every declaration of it.
- The model is plain executable code that the proofs are about: no experimental options, and no
  `partial`, `unsafe`, `implemented_by` or `extern`, which would let the executable run code that
  the proofs do not see.
- Axioms: no `native_decide`, `decide +native`, `bv_decide`, `bv_check` or `ofReduceBool`
  anywhere, since each adds an axiom that comparator rejects.

Comments and docstrings are not checked.
"""
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from style_lint import strip_comments  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
IMPORT = re.compile(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)')

# Allowed import prefixes per part: a module `M` may be imported if `M` is one of the prefixes or
# starts with one of them followed by a dot.
ALLOWED = {
    'model': ['Init', 'Std', 'Ratpoints.Model'],
    'spec': ['Init', 'Std', 'Mathlib', 'Ratpoints.Spec'],
    'mathlib': ['Init', 'Std', 'Lean', 'Batteries', 'Qq', 'Aesop', 'Mathlib', 'Ratpoints.Mathlib'],
    'challenge': ['Init', 'Std', 'Mathlib', 'Ratpoints.Model'],
    'main': ['Init', 'Std', 'Ratpoints.Model'],
}
FORBIDDEN_EVERYWHERE = [
    ('axiom', r'\bnative_decide\b|\bdecide\s*\+native\b|\bbv_decide\b|\bbv_check\b|ofReduceBool'),
]
FORBIDDEN_IN_MODEL = [
    ('experimental', r'\bset_option\s+experimental\.'),
    ('partial', r'\bpartial\s+def\b'),
    ('unsafe', r'\bunsafe\b'),
    ('implemented_by', r'\bimplemented_by\b'),
    ('extern', r'@\[\s*extern\b|\bextern\s+"'),
]


def module_of(path):
    return '.'.join(path.relative_to(ROOT).with_suffix('').parts)


def part_of(path):
    rel = path.relative_to(ROOT).as_posix()
    if rel == 'Ratpoints/Model.lean' or rel.startswith('Ratpoints/Model/'):
        return 'model'
    if rel == 'Ratpoints/Spec.lean' or rel.startswith('Ratpoints/Spec/'):
        return 'spec'
    if rel.startswith('Ratpoints/Mathlib/'):
        return 'mathlib'
    if rel == 'comparator/Challenge.lean':
        return 'challenge'
    if rel == 'Main.lean':
        return 'main'
    return None


def allowed(mod, prefixes):
    return any(mod == p or mod.startswith(p + '.') for p in prefixes)


def main():
    files = sorted([*ROOT.glob('Ratpoints/**/*.lean'), *ROOT.glob('comparator/*.lean')])
    files += [p for p in (ROOT / 'Ratpoints.lean', ROOT / 'Main.lean') if p.exists()]
    fails = []

    def fail(rule, path, i, text):
        fails.append(f'FAIL {rule} {path.relative_to(ROOT)}:{i + 1}: {text.strip()}')

    imports = {}
    for path in files:
        raw = path.read_text(encoding='utf-8').split('\n')
        code = strip_comments(raw)
        part = part_of(path)
        imports[module_of(path)] = []
        for i, line in enumerate(code):
            m = IMPORT.match(line)
            if m:
                imports[module_of(path)].append(m.group(1))
                if part and not allowed(m.group(1), ALLOWED[part]):
                    fail(f'import-{part}', path, i, raw[i])
            rules = FORBIDDEN_EVERYWHERE + (FORBIDDEN_IN_MODEL if part == 'model' else [])
            for rule, pat in rules:
                if re.search(pat, line):
                    fail(rule, path, i, raw[i])
    for root in ('Ratpoints.Model', 'Ratpoints.Spec', 'Ratpoints.Proof'):
        seen, todo = set(), [root]
        while todo:
            mod = todo.pop()
            if mod not in seen:
                seen.add(mod)
                todo += [m for m in imports.get(mod, []) if m in imports]
        path = ROOT / (root.replace('.', '/') + '.lean')
        for mod in sorted(m for m in imports if m.startswith(root + '.') and m not in seen):
            fail('root', path, 0, f'{root} does not import {mod}')
    print('\n'.join(fails))
    print(f'layout: {len(fails)} fails in {len(files)} files')
    return 1 if fails else 0


if __name__ == '__main__':
    sys.exit(main())

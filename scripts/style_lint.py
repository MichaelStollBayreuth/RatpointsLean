#!/usr/bin/env python3
# A copy of the style lint of the author's verification chain for his Lean projects, so that CI
# can run it; keep the two in sync.
"""Project style lint for Lean files: the rules that Lean's and Mathlib's linters do not cover.

usage: style_lint.py <files or directories...>

Prints `FAIL <rule> <file>:<line>: <text>` for every violation of a failing rule and
`NOTE <rule> ...` for the informational ones, then a summary line; exits 1 iff a FAIL was printed.
A justified exception is declared with a comment `-- lint: allow <rule>[: reason]` on the offending
line or the line above; for `long-proof`, anywhere from the line above the declaration to its
`:=` line. Comments and doc/module comments are not linted (only the raw line is searched for the
`lint: allow` marker).
"""
import os, re, sys

FAIL_RULES = [
    ('omega', r'\bomega\b'),
    ('arrow', r'\bfun\b[^↦\n]*=>'),
    ('rintro', r'\brintro\b'),            # allowed on a line with a `rfl` or `|` pattern
    ('by-exact', r'\bby exact\b'),
    ('haveI', r'\b(?:haveI|letI)\b'),
    ('from-by', r'\bfrom by\b'),
    ('exact-mod-cast', r'\bby exact_mod_cast\b'),
    ('unfold', r'\bunfold\b'),
    ('omit', r'^\s*omit\b'),
    ('maxHeartbeats', r'\bmaxHeartbeats\b'),
    ('sorry', r'\bsorry\b'),
]
NOTE_RULES = [
    ('nlinarith', r'\bnlinarith\b'),
    ('field_simp', r'\bfield_simp\b'),
    ('name', r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|nonrec|noncomputable|public)\s+)*'
             r'(?:theorem|lemma|def|instance)\s+\S*(?:[Aa]ux|[Hh]elper|[Kk]ey|[Ss]tep|[Cc]laim|_lemma)\S*'),
]
MAX_PROOF = 20
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|nonrec|noncomputable|public)\s+)*'
                  r'(theorem|lemma|def|instance|example)\b')
OPEN, CLOSE = '([{⟨⦃', ')]}⟩⦄'

def strip_comments(lines):
    """Code-only view of each line: block comments (`/- … -/`, doc/module comments) and `--`
    comments removed."""
    out, depth = [], 0
    for l in lines:
        res, i = [], 0
        while i < len(l):
            if depth == 0 and l.startswith('--', i):
                break
            if l.startswith('/-', i):
                depth += 1; i += 2; continue
            if depth > 0 and l.startswith('-/', i):
                depth -= 1; i += 2; continue
            if depth == 0:
                res.append(l[i])
            i += 1
        out.append(''.join(res))
    return out

def allowed(raw, i, rule, lo=None):
    lo = i - 1 if lo is None else lo
    for j in range(max(lo, 0), i + 1):
        if re.search(r'lint: allow ' + re.escape(rule) + r'\b', raw[j]):
            return True
    return False

def lint_file(path, report):
    raw = open(path, encoding='utf-8').read().split('\n')
    code = strip_comments(raw)
    for i, l in enumerate(code):
        for rule, pat in FAIL_RULES:
            if re.search(pat, l):
                if rule == 'rintro' and re.search(r'\brfl\b|\|', l):
                    continue
                if not allowed(raw, i, rule):
                    report('FAIL', rule, path, i, raw[i])
        for rule, pat in NOTE_RULES:
            if re.search(pat, l) and not allowed(raw, i, rule):
                report('NOTE', rule, path, i, raw[i])
    # proof length
    i = 0
    while i < len(code):
        m = DECL.match(code[i])
        if not m:
            i += 1; continue
        start = i
        # the block ends at the next blank line (declarations contain none)
        end = start
        while end < len(raw) and raw[end].strip() != '':
            end += 1
        # signature end: the first `:=` at bracket depth 0
        depth, sig = 0, None
        for k in range(start, end):
            l = code[k]; j = 0
            while j < len(l):
                c = l[j]
                if c in OPEN: depth += 1
                elif c in CLOSE: depth -= 1
                elif depth == 0 and l.startswith(':=', j):
                    sig = k; break
                j += 1
            if sig is not None: break
        if sig is not None and m.group(1) != 'example' or sig is not None:
            after = code[sig].split(':=', 1)[1].strip()
            n = end - sig - 1 + (1 if after not in ('', 'by') else 0)
            if n > MAX_PROOF and not allowed(raw, sig, 'long-proof', lo=start - 1):
                report('FAIL', 'long-proof', path, start, f'{n} lines: {raw[start].strip()}')
        i = end

def main(paths):
    fails = notes = 0
    def report(kind, rule, path, i, text):
        nonlocal fails, notes
        if kind == 'FAIL': fails += 1
        else: notes += 1
        print(f'{kind} {rule} {path}:{i + 1}: {text.strip()}')
    files = []
    for p in paths:
        if os.path.isdir(p):
            for root, _, names in os.walk(p):
                files += [os.path.join(root, n) for n in names if n.endswith('.lean')]
        else:
            files.append(p)
    for f in sorted(files):
        lint_file(f, report)
    print(f'style lint: {fails} fails, {notes} notes in {len(files)} files')
    return 1 if fails else 0

if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))

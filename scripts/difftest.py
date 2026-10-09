#!/usr/bin/env python3
"""Differential tests of ratpoints-lean against ratpoints at the pinned commit.

usage: scripts/difftest.py [options]

Runs the Lean program ratpoints-lean on the test suites of ratpoints and on further command lines,
and compares it with the recorded outputs and with the C program:

  test4   the invocations of test4.sh, read from testbase4 (split at its announce lines);
  test3   the invocations of test3.sh, run one by one against the C program;
  rptest  the curves of testdata.h, testdata-many.h and testdata-degrees.h at a reduced height h,
          against the lines of testbase, testbase-many and testbase-degrees restricted to
          |a| <= h and b <= h, which is what the C program prints at height h;
  random  random polynomials at small heights against the C program;
  errors  the command lines of scripts/difftest_cases.py, for the checks that main.c makes on
          the coefficients, the height and the options, against the C program;
  fuzz    random command lines (scripts/difftest_cases.py) against the C program.

ratpoints-lean prints the points as ratpoints does with -q. They are compared as sets, until the
model visits the points in the order of the C program, and without -q with the point lines of the
report that the C program prints then. Messages and exit codes are compared exactly, but for the
banner and the usage, which differ by design: in the outputs of errors 2 and 6 they are exchanged
for those of the C program (the outputs of the two programs on an empty command line), and the
errors suite checks the usage of ratpoints-lean against that of ratpoints. On a command line with
an option that ratpoints-lean does not support yet, it must fail as the C program does if that
fails before the option, and else exit with status 12 and a message that names the option.
Skipped: the inputs that the C program refuses as not squarefree (exit 8), which ratpoints-lean
refuses from stage D on, the outputs that the test scripts filter, and searches above
--max-height.

options:
  --lean PATH        the ratpoints-lean executable (default: .lake/build/bin/ratpoints-lean)
  --c PATH           the C program, built at the pinned commit (default: the environment variable
                     RATPOINTS_BIN, else the program ratpoints in the clone of --repo)
  --repo PATH        a clone of ratpoints that contains the pinned commit (default: the
                     environment variable RATPOINTS_REPO); the test files are read at the pin
  --suites LIST      comma-separated suites (default: test4,test3,rptest,random,errors,fuzz)
  --max-height H     the largest height of a search (default: 1000)
  --rptest-height h  the reduced height of the rptest suites (default: 100)
  --random N         the number of random polynomials (default: 300)
  --fuzz N           the number of rounds of random command lines, seven each (default: 100)
  --seed S           the seed of the random suites (default: 1)
  -v                 print every comparison
"""
import argparse
import os
import random
import re
import shlex
import subprocess
import sys
import tomllib
from dataclasses import dataclass, field
from pathlib import Path

import difftest_cases

ROOT = Path(__file__).resolve().parent.parent
RECORD = ROOT / 'correspondence' / 'ratpoints.toml'

# main.c tells its options apart by their second character, and -f and -d by the third too.
# ratpoints-lean reads -q, -v, -j, -J and the tuning options that take an argument, and ignores
# them; the other options of ratpoints it does not support yet; any other word is error 6.
ARG_OPTS = set('pFtnNRAPrUCQW')
FLAGS = set('qvjJ')
UNSUPPORTED = set('lukKxXyYzZ1iIsS')
POINT = re.compile(r'^\((-?\d+) : (-?\d+) : (\d+)\)$')
TIMEOUT = 600


@dataclass
class Run:
    """One invocation of test4.sh as testbase4 records it."""
    line: int
    args: list
    filt: str | None
    out: list = field(default_factory=list)
    nonl: bool = False  # the output does not end with a newline


@dataclass
class Tally:
    """What a suite compared, skipped and found."""
    compared: int = 0
    skipped: dict = field(default_factory=dict)
    failures: list = field(default_factory=list)

    def skip(self, reason):
        self.skipped[reason] = self.skipped.get(reason, 0) + 1


def git_show(repo, commit, path):
    r = subprocess.run(['git', '-C', str(repo), 'show', f'{commit}:{path}'],
                       capture_output=True, check=True)
    return r.stdout.decode('latin-1')


def as_bytes(arg):
    """An argument as the program receives it (an argument is a str or bytes)."""
    return arg if isinstance(arg, bytes) else os.fsencode(arg)


def run(prog, args):
    r = subprocess.run([str(prog), *args], capture_output=True, timeout=TIMEOUT)
    return r.stdout.decode('latin-1'), r.returncode


def read_options(opts):
    """How ratpoints-lean reads the options `opts`, the words after the height: the index of the
    first that it does not support yet (None if it reaches the end or a word that is no option of
    ratpoints first), and whether -q comes before it."""
    quiet, i = False, 0
    while i < len(opts):
        o = as_bytes(opts[i]).decode('latin-1')
        if len(o) < 2 or o[0] != '-':
            return None, quiet
        if o[1] in ARG_OPTS:
            i += 2
        elif o[1] in FLAGS:
            quiet, i = quiet or o[1] == 'q', i + 1
        elif (o[1] in UNSUPPORTED or o[1] == 'f' and o[2:3] in ('', 's', 'm', 'e') or
              o[1] == 'd' and o[2:3] in ('l', 'u')):
            return i, quiet
        else:
            return None, quiet
    return None, quiet


def expected_unsupported(cfg, args, k):
    """What ratpoints-lean is to print and return on the command line `args`, whose option
    args[2 + k] is the first that it does not support yet: what the C program does if it fails
    before that option, else the exit status 12 and a message that names the option."""
    out, code = run(cfg.c, [*args[:2], '-g'])  # -g, an unknown option: nothing is searched
    if code != 6:  # an error in the first two arguments
        return out, code
    out, code = run(cfg.c, [args[0], '1', *args[2:2 + k]])  # height 1: a short search
    if code == 6:  # an option before args[2 + k] is malformed
        return out, code
    word = as_bytes(args[2 + k]).decode('utf-8', 'replace')
    msg = f'\nOption {word} is not supported by ratpoints-lean yet.\n\n'
    return msg.encode().decode('latin-1'), 12


def as_recorded_by_e(raw):
    """What the helper e() of test4.sh records of an output: the trailing newlines dropped, one
    newline added, and the banner line and the usage taken out."""
    lines = (raw.rstrip('\n') + '\n').split('\n')[:-1]
    return ''.join(l + '\n' for l in lines if not re.match(r'This is ratpoints-|Usage: | *\[', l))


def height(arg):
    try:
        return int(arg.strip())
    except ValueError:
        return None


def points(text, report=False):
    """The points of an output that consists of point lines only (else None), or with `report`
    the points among the lines of a report, as a sorted list."""
    lines = text.split('\n')
    if lines and lines[-1] == '':
        lines.pop()
    if not report and not all(POINT.match(l) for l in lines):
        return None
    return sorted(tuple(int(g) for g in m.groups()) for m in map(POINT.match, lines) if m)


def agrees(cfg, lean, expected, mode):
    """Whether the output and exit code `lean` of ratpoints-lean agree with `expected`: in the
    mode 'points' as sets of points (exit 0), in 'report' with the point lines of a report of the
    C program, in 'exact' exactly and in 'e' as test4.sh's e() records them, the banner and the
    usage exchanged for those of the C program."""
    (out, code), (exp, exp_code) = lean, expected
    if mode in ('points', 'report'):
        got = points(out)
        return code == 0 and got is not None and got == points(exp, report=mode == 'report')
    out = out.replace(cfg.lean_usage, cfg.c_usage)
    if mode == 'e':
        out = as_recorded_by_e(out)
    return out == exp and code == exp_code


def check(cfg, tally, label, args, expected, mode):
    """Run ratpoints-lean on `args` and compare it with `expected` (see agrees)."""
    lean = run(cfg.lean, args)
    ok = agrees(cfg, lean, expected, mode)
    tally.compared += 1
    if not ok:
        tally.failures.append(f'{label}: expected exit {expected[1]} and {expected[0][:500]!r}, '
                              f'got exit {lean[1]} and {lean[0][:500]!r}')
    if cfg.verbose:
        print(('ok   ' if ok else 'FAIL ') + label)


def against_c(cfg, tally, label, args):
    """Compare ratpoints-lean with the C program on the command line `args`."""
    k, quiet = read_options(args[2:])
    if len(args) >= 2 and k is not None:
        check(cfg, tally, label, args, expected_unsupported(cfg, args, k), 'exact')
        return
    out, code = run(cfg.c, args)
    if code == 8:
        tally.skip('not squarefree (stage D)')
    elif code == 0 and (height(as_bytes(args[1]).decode('latin-1')) or 0) > cfg.max_height:
        tally.skip(f'height above {cfg.max_height}')
    else:
        mode = 'exact' if code else 'points' if quiet else 'report'
        check(cfg, tally, label, args, (out, code), mode)


def split_test4(text):
    """The invocations recorded in testbase4, split as verify-test4.py splits them."""
    lines = text.split('\n')
    if lines and lines[-1] == '':
        lines.pop()
    runs, cur = [], None
    for no, line in enumerate(lines, 1):
        k = line.find('# <')
        if k > 0 and cur is not None:  # an announce line glued to an output without newline
            cur.out.append(line[:k])
            cur.nonl = True
            line = line[k:]
        m = re.match(r'^#((?: <[^>]*>)*)(?: \| (.*))?$', line)
        if line.startswith('#') and m:
            cur = Run(no, re.findall(r' <([^>]*)>', m.group(1)), m.group(2))
            runs.append(cur)
        elif line.startswith('====') or line.startswith('----'):
            cur = None
        elif cur is not None:
            cur.out.append(line)
    return runs


def suite_test4(cfg, tally):
    for r in split_test4(git_show(cfg.repo, cfg.commit, 'testbase4')):
        label = f'testbase4:{r.line} {r.args}'
        out, code = r.out, None
        if out and re.fullmatch(r'exit \d+', out[-1]):  # recorded by e()
            code, out = int(out[-1].split()[1]), out[:-1]
        text = '\n'.join(out) + ('' if r.nonl else '\n') if out else ''
        if code == 0:  # e() keeps one newline at the end, also of an empty output
            text = text.rstrip('\n') + '\n' if text.strip('\n') else ''
        k, quiet = read_options(r.args[2:])
        if r.filt is not None:
            tally.skip('output filtered')
        elif len(r.args) >= 2 and k is not None:
            check(cfg, tally, label, r.args, expected_unsupported(cfg, r.args, k), 'exact')
        elif code == 8 or 'Polynomial is not square-free.' in text:
            tally.skip('not squarefree (stage D)')
        elif code:
            check(cfg, tally, label, r.args, (text, code), 'e')
        elif (height(r.args[1]) or 0) > cfg.max_height:
            tally.skip(f'height above {cfg.max_height}')
        else:
            check(cfg, tally, label, r.args, (text, 0), 'points' if quiet else 'report')


def suite_test3(cfg, tally):
    script = git_show(cfg.repo, cfg.commit, 'test3.sh')
    for no, line in enumerate(script.split('\n'), 1):
        if not line.startswith('rp '):
            continue
        if '|' in line:
            tally.skip('output filtered')
            continue
        args = shlex.split(line)[1:]
        against_c(cfg, tally, f'test3.sh:{no} {args}', args)


def strip_c_comments(text):
    return re.sub(r'/\*.*?\*/|//[^\n]*', ' ', text, flags=re.S)


def curves(header):
    """The coefficient lists (constant term first) of a testdata*.h file."""
    text = strip_c_comments(header)
    body = text[text.index('{', text.index('testdata')) + 1:text.rindex('}')]
    rows = [[int(x.rstrip('lL')) for x in re.findall(r'-?\d+[lL]*', row)]
            for row in re.findall(r'\{([^{}]*)\}', body)]
    if re.search(r'#\s*define\s+TEST_MAX_DEGREE', text):  # rows: d, c_0, ..., c_d, ...
        return [row[1:row[0] + 2] for row in rows]
    return rows


def reference_points(line):
    return [tuple(int(g) for g in m.groups())
            for m in re.finditer(r'\[(-?\d+),(-?\d+),(-?\d+)\]', line)]


def suite_rptest(cfg, tally):
    h = cfg.rptest_height
    for data, base in (('testdata.h', 'testbase'), ('testdata-many.h', 'testbase-many'),
                       ('testdata-degrees.h', 'testbase-degrees')):
        cs = curves(git_show(cfg.repo, cfg.commit, data))
        refs = git_show(cfg.repo, cfg.commit, base).rstrip('\n').split('\n')
        if len(cs) != len(refs):
            tally.failures.append(f'{data}: {len(cs)} curves, but {len(refs)} lines in {base}')
            continue
        for i, (c, ref) in enumerate(zip(cs, refs), 1):
            pts = sorted(p for p in reference_points(ref) if abs(p[0]) <= h and p[2] <= h)
            expected = ''.join(f'({a} : {y} : {b})\n' for a, y, b in pts)
            args = [' '.join(map(str, c)), str(h), '-q']
            check(cfg, tally, f'{base}:{i} {args}', args, (expected, 0), 'points')


def suite_random(cfg, tally):
    rng = random.Random(cfg.seed)
    for i in range(cfg.random):
        deg = rng.randint(1, 8)
        c = [rng.randint(-10, 10) for _ in range(deg + 1)]
        args = [' '.join(map(str, c)), str(rng.randint(1, 30)), '-q']
        against_c(cfg, tally, f'random {i} {args}', args)


def suite_errors(cfg, tally):
    usage = cfg.c_usage[cfg.c_usage.index('Usage: '):]
    usage = (usage.replace('Usage: ratpoints ', 'Usage: ratpoints-lean ')
             .replace('\n' + ' ' * 17, '\n' + ' ' * 22))
    tally.compared += 1
    if not (cfg.lean_usage.startswith('\nThis is ratpoints-lean-') and
            cfg.lean_usage.endswith(usage)):
        tally.failures.append(f'the banner and the usage of ratpoints-lean: {cfg.lean_usage!r}')
    for args, note in difftest_cases.CASES:
        against_c(cfg, tally, f'{note}: {args}', args)


def suite_fuzz(cfg, tally):
    rng = random.Random(cfg.seed)
    for i in range(cfg.fuzz):
        for j, args in enumerate(difftest_cases.random_command_lines(rng)):
            against_c(cfg, tally, f'fuzz {i}.{j} {args}', args)


SUITES = {'test4': suite_test4, 'test3': suite_test3, 'rptest': suite_rptest,
          'random': suite_random, 'errors': suite_errors, 'fuzz': suite_fuzz}


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--lean', type=Path, default=ROOT / '.lake' / 'build' / 'bin' /
                    'ratpoints-lean')
    ap.add_argument('--c', type=Path)
    ap.add_argument('--repo', type=Path)
    ap.add_argument('--suites', default=','.join(SUITES))
    ap.add_argument('--max-height', type=int, default=1000)
    ap.add_argument('--rptest-height', type=int, default=100)
    ap.add_argument('--random', type=int, default=300)
    ap.add_argument('--fuzz', type=int, default=100)
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('-v', '--verbose', action='store_true')
    cfg = ap.parse_args(argv)
    cfg.repo = cfg.repo or (Path(os.environ['RATPOINTS_REPO'])
                            if os.environ.get('RATPOINTS_REPO') else None)
    if cfg.repo is None:
        print('ERROR no clone of ratpoints given: use --repo PATH or set RATPOINTS_REPO')
        return 1
    cfg.c = cfg.c or Path(os.environ.get('RATPOINTS_BIN') or cfg.repo / 'ratpoints')
    for prog in (cfg.lean, cfg.c):
        if not os.access(prog, os.X_OK):
            print(f'ERROR {prog} is not an executable')
            return 1
    cfg.commit = tomllib.loads(RECORD.read_text())['pin']['commit']
    cfg.c_usage, cfg.lean_usage = run(cfg.c, [])[0], run(cfg.lean, [])[0]
    failed = 0
    for name in cfg.suites.split(','):
        tally = Tally()
        SUITES[name](cfg, tally)
        skipped = ', '.join(f'{k} {v}' for k, v in sorted(tally.skipped.items()))
        print(f'{name}: {tally.compared} compared, {len(tally.failures)} failed'
              + (f'; skipped: {skipped}' if skipped else ''))
        for f in tally.failures:
            print(f'  FAIL {f}')
        failed += len(tally.failures)
    return 1 if failed else 0


if __name__ == '__main__':
    sys.exit(main())

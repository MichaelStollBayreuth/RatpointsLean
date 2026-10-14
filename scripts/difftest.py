#!/usr/bin/env python3
"""Differential tests of ratpoints-lean against ratpoints at the pinned commit.

usage: scripts/difftest.py [options]

Runs the Lean program ratpoints-lean on the test suites of ratpoints and on further command lines,
and compares it with the recorded outputs and with the C program:

  test4   the invocations of test4.sh, read from testbase4 (split at its announce lines);
  test3   the invocations of test3.sh, run one by one against the C program;
  rptest  the curves of testdata.h, testdata-many.h and testdata-degrees.h at a reduced height h,
          against the lines of testbase, testbase-many and testbase-degrees restricted to
          |a| <= h and b <= h, which is what the C program prints at height h, in its order;
  random  random polynomials at small heights against the C program;
  errors  the command lines of scripts/difftest_cases.py, for the checks that main.c makes on
          the coefficients, the height and the options, for the options of the search, -k -K
          -s -S, and for the refusals of forms that are not squarefree, against the C program;
          the usage; and failed writes: a standard output whose reader is gone, which ends the C
          program by SIGPIPE, where ratpoints-lean (the Lean runtime ignores SIGPIPE) is to exit
          quietly with the status 141 that the shell reports for that, and a full device, whose
          failed writes both programs ignore;
  fuzz    random command lines (scripts/difftest_cases.py) against the C program;
  params  the options that set the sieving parameters (-p -n -N -P -F -j), with values that
          give no moduli, all the primes of the default build, the cut points in several
          positions, a third stage, the second and the third stage after few moduli or none in
          the first, and the defaults, on point-rich and on random curves against the C program,
          whose points do not depend on them;
  high    point-rich curves at the heights 2000, 5000 and 30000 against the C program;
  test4high  the invocations of test4.sh that search with a height bound above --max-height and
          at most --test4-max-height, a few minutes in all: run locally, not by default.

ratpoints-lean prints the points as ratpoints does with -q; without -q they are compared with the
point lines of the report that the C program prints then. They are compared in their order, also
where ratpoints visits the denominators divisor by divisor (a polynomial searched of odd degree
whose leading coefficient is not +-1), since the model visits them in the same order.
Messages and exit codes are compared exactly, but for the banner and the usage, which differ by
design: in the outputs of errors 2 and 6 they are exchanged for those of the C program (the outputs
of the two programs on an empty command line), and the errors suite checks the usage of
ratpoints-lean against that of ratpoints; a refusal of a form that is not squarefree (error 8) on a
command line without -q, where the C program prints its report before the message, is compared by
the message at the end of that report. On a command line with an option that ratpoints-lean does
not support yet, it must fail as the C program does if that fails before the option, and else exit
with status 12 and a message that names the option. Skipped: the outputs that the test scripts
filter, and searches above --max-height, which the suites that run the C program compare when it
prints nothing (a search with -q that finds no points, as when no class of the denominators modulo
64 admits a numerator).

options:
  --lean PATH        the ratpoints-lean executable (default: .lake/build/bin/ratpoints-lean)
  --c PATH           the C program, built at the pinned commit (default: the environment variable
                     RATPOINTS_BIN, else the program ratpoints in the clone of --repo)
  --repo PATH        a clone of ratpoints that contains the pinned commit (default: the
                     environment variable RATPOINTS_REPO); the test files are read at the pin
  --suites LIST      comma-separated suites (default: test4,test3,rptest,random,errors,fuzz,
                     params,high)
  --max-height H     the largest height of a search (default: 30000)
  --test4-max-height H  the largest height of a search of the suite test4high (default: 100000)
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
import signal
import subprocess
import sys
import tomllib
from dataclasses import dataclass, field
from pathlib import Path

import difftest_cases

ROOT = Path(__file__).resolve().parent.parent
RECORD = ROOT / 'correspondence' / 'ratpoints.toml'

# main.c tells its options apart by their second character, and -f and -d by the third too.
# ratpoints-lean reads -q, -v, -j, -J, -k, -K, -s, the tuning options that take an argument, and
# -S, whose argument is optional: the next word, if there is one and it does not start with -; the
# other options of ratpoints it does not support yet; any other word is error 6.
ARG_OPTS = set('pFtnNRAPrUCQW')
FLAGS = set('qvjJkKs')
UNSUPPORTED = set('luxXyYzZ1iI')
POINT = re.compile(r'^\((-?\d+) : (-?\d+) : (\d+)\)$')
# The params suite: the options that set the sieving parameters, with values that give no
# moduli, all the primes of the default build and a cap above them, the cut points in several
# positions, a third stage, the second and the third stage after few moduli or none in the first
# (at the small heights of the suite, since most numerators then reach the test of a candidate,
# which the model runs numerator by numerator, as the C program does but more slowly), no Jacobi
# test, no forbidden divisors and many of them, and negative values, which mean the defaults; and
# the point-rich curves it runs them on, with their height bounds.
PARAM_OPTIONS = [['-p', '0'], ['-p', '53'], ['-p', '200'], ['-n', '0'], ['-n', '5', '-N', '10'],
                 ['-N', '3', '-P', '20'], ['-p', '10', '-P', '43'], ['-j'], ['-F', '0'],
                 ['-F', '500'], ['-p', '-5', '-n', '-1', '-N', '-2', '-P', '-3', '-F', '-4'],
                 ['-n', '3', '-N', '5', '-P', '2'], ['-n', '0', '-N', '0'], ['-N', '30'],
                 ['-n', '2', '-N', '20'], ['-N', '10', '-P', '3'], ['-n', '1', '-P', '0']]
PARAM_CURVES = [('1 0 126 0 441', 200), ('-2 0 0 1', 130), ('1 1 1 1 0', 60),
                ('1 2 3 4 5 6 7', 60), ('-1 0 9', 100), ('0 1 1', 40)]
# The high suite: the first four of these curves at larger heights.
HIGH_HEIGHTS = [2000, 5000, 30000]
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
    """What a suite compared, skipped and found, with the number of point lists, each compared in
    its order."""
    compared: int = 0
    in_order: int = 0
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


def closed_pipe(prog, args):
    """The return code (minus the signal that ends the program, if one does) and the standard
    error of `prog` on the command line `args` when its standard output is a pipe that nobody
    reads: its reader was closed before the program started. subprocess restores the default
    action of SIGPIPE in the program."""
    r, w = os.pipe()
    os.close(r)
    try:
        p = subprocess.run([str(prog), *args], stdout=w, stderr=subprocess.PIPE, timeout=TIMEOUT)
    finally:
        os.close(w)
    return p.returncode, p.stderr.decode('latin-1')


def full_device(prog, args):
    """The return code and the standard error of `prog` on the command line `args` when its
    standard output is /dev/full, on which every write fails."""
    with open('/dev/full', 'w') as f:
        p = subprocess.run([str(prog), *args], stdout=f, stderr=subprocess.PIPE, timeout=TIMEOUT)
    return p.returncode, p.stderr.decode('latin-1')


def special(cfg, tally, label, ok, detail):
    """Record a check that is not a comparison of outputs."""
    tally.compared += 1
    if not ok:
        tally.failures.append(f'{label}: {detail}')
    if cfg.verbose:
        print(('ok   ' if ok else 'FAIL ') + label)


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
        elif o[1] == 'S':
            i += 2 if i + 1 < len(opts) and not as_bytes(opts[i + 1]).startswith(b'-') else 1
        elif o[1] in FLAGS:
            quiet = quiet or o[1] == 'q'
            i += 1
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
    the points among the lines of a report, as a list in their order."""
    lines = text.split('\n')
    if lines and lines[-1] == '':
        lines.pop()
    if not report and not all(POINT.match(l) for l in lines):
        return None
    pts = [tuple(int(g) for g in m.groups()) for m in map(POINT.match, lines) if m]
    return pts


def agrees(cfg, lean, expected, mode):
    """Whether the output and exit code `lean` of ratpoints-lean agree with `expected`: in the mode
    'points' as lists of points in their order (exit 0), in 'report' in the same way with the point
    lines of a report of the C program, in 'message' as the message that ends a report of the C
    program, in 'exact' exactly and in 'e' as test4.sh's e() records them, the banner and the usage
    exchanged for those of the C program."""
    (out, code), (exp, exp_code) = lean, expected
    if mode in ('points', 'report'):
        got = points(out)
        return (code == 0 and got is not None and
                got == points(exp, report=mode == 'report'))
    if mode == 'message':
        return (code == exp_code and out.strip() != '' and
                exp.rstrip('\n').endswith(out.rstrip('\n')))
    out = out.replace(cfg.lean_usage, cfg.c_usage)
    if mode == 'e':
        out = as_recorded_by_e(out)
    return out == exp and code == exp_code


def check(cfg, tally, label, args, expected, mode):
    """Run ratpoints-lean on `args` and compare it with `expected` (see agrees)."""
    lean = run(cfg.lean, args)
    ok = agrees(cfg, lean, expected, mode)
    tally.compared += 1
    tally.in_order += mode in ('points', 'report')
    if not ok:
        tally.failures.append(f'{label}: expected exit {expected[1]} and {expected[0][:500]!r}, '
                              f'got exit {lean[1]} and {lean[0][:500]!r}')
    if cfg.verbose:
        print(('ok   ' if ok else 'FAIL ') + label)


def skips_height(cfg, args, out, code):
    """Whether the comparison with the C program, which ended with the output `out` and the exit
    code `code` on the command line `args`, is skipped: a search above --max-height on which the C
    program prints something (one that prints nothing is quick for both and is compared)."""
    return (code == 0 and bool(out) and
            (height(as_bytes(args[1]).decode('latin-1')) or 0) > cfg.max_height)


def against_c(cfg, tally, label, args):
    """Compare ratpoints-lean with the C program on the command line `args`."""
    k, quiet = read_options(args[2:])
    if len(args) >= 2 and k is not None:
        check(cfg, tally, label, args, expected_unsupported(cfg, args, k), 'exact')
        return
    out, code = run(cfg.c, args)
    if skips_height(cfg, args, out, code):
        tally.skip(f'height above {cfg.max_height}')
    elif code == 0:
        check(cfg, tally, label, args, (out, 0), 'points' if quiet else 'report')
    else:  # without -q the C program prints its report before the message of error 8
        check(cfg, tally, label, args, (out, code),
              'message' if code == 8 and not quiet else 'exact')


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


def suite_test4(cfg, tally, window=None):
    """The invocations of test4.sh, a search with a height bound above --max-height skipped; with
    `window = (low, high)`, only the searches with a height bound in (low, high], the rest being
    left to the plain call."""
    for r in split_test4(git_show(cfg.repo, cfg.commit, 'testbase4')):
        label = f'testbase4:{r.line} {r.args}'
        out, code = r.out, None
        if out and re.fullmatch(r'exit \d+', out[-1]):  # recorded by e()
            code, out = int(out[-1].split()[1]), out[:-1]
        text = '\n'.join(out) + ('' if r.nonl else '\n') if out else ''
        if code == 0:  # e() keeps one newline at the end, also of an empty output
            text = text.rstrip('\n') + '\n' if text.strip('\n') else ''
        k, quiet = read_options(r.args[2:])
        mode = 'points' if quiet else 'report'
        if window is not None:
            searches = (r.filt is None and not (len(r.args) >= 2 and k is not None) and
                        not code and 'Polynomial is not square-free.' not in text)
            if searches and window[0] < (height(r.args[1]) or 0) <= window[1]:
                check(cfg, tally, label, r.args, (text, 0), mode)
            continue
        if r.filt is not None:
            tally.skip('output filtered')
        elif len(r.args) >= 2 and k is not None:
            check(cfg, tally, label, r.args, expected_unsupported(cfg, r.args, k), 'exact')
        elif code == 8 or 'Polynomial is not square-free.' in text:
            # error 8, recorded by e() with -q, and without -q at the end of a report
            check(cfg, tally, label, r.args, (text, 8),
                  'message' if not quiet else 'e' if code else 'exact')
        elif code:
            check(cfg, tally, label, r.args, (text, code), 'e')
        elif (height(r.args[1]) or 0) > cfg.max_height:
            tally.skip(f'height above {cfg.max_height}')
        else:
            check(cfg, tally, label, r.args, (text, 0), mode)


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
            pts = [p for p in reference_points(ref) if abs(p[0]) <= h and p[2] <= h]
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
    special(cfg, tally, 'the banner and the usage',
            cfg.lean_usage.startswith('\nThis is ratpoints-lean-') and
            cfg.lean_usage.endswith(usage), repr(cfg.lean_usage))
    # Short and long outputs (ratpoints-lean's write fails in its flush or in the write itself),
    # an error message, and no output at all, where neither program notices the closed pipe.
    for args, writes in ((['1 0 1', '10', '-q'], True), (['1 0 1', '300', '-q'], True),
                         (['1 2 x', '10'], True), (['-1 0 -1', '10', '-q'], False)):
        lean, c = closed_pipe(cfg.lean, args), closed_pipe(cfg.c, args)
        ok = ((c, lean) == ((-signal.SIGPIPE, ''), (128 + signal.SIGPIPE, '')) if writes else
              c == lean == (0, ''))
        special(cfg, tally, f'a closed pipe: {args}', ok,
                f'ratpoints-lean gives {lean}, the C program {c}')
    if os.path.exists('/dev/full'):
        for args in (['1 0 1', '10', '-q'], ['1 0 1', '300', '-q'], ['1 2 x', '10']):
            lean, c = full_device(cfg.lean, args), full_device(cfg.c, args)
            special(cfg, tally, f'a full device: {args}', lean == c and c[1] == '',
                    f'ratpoints-lean gives {lean}, the C program {c}')
    for args, note in difftest_cases.CASES:
        against_c(cfg, tally, f'{note}: {args}', args)


def suite_params(cfg, tally):
    rng = random.Random(cfg.seed)
    curves = PARAM_CURVES + [(' '.join(str(rng.randint(-10, 10)) for _ in range(rng.randint(2, 9))),
                              rng.randint(1, 60)) for _ in range(10)]
    for opts in PARAM_OPTIONS:
        for c, h in curves:
            args = [c, str(h), '-q', *opts]
            against_c(cfg, tally, f'params {args}', args)


def suite_high(cfg, tally):
    for c, _ in PARAM_CURVES[:4]:
        for h in HIGH_HEIGHTS:
            args = [c, str(h), '-q']
            against_c(cfg, tally, f'high {args}', args)


def suite_test4high(cfg, tally):
    suite_test4(cfg, tally, (cfg.max_height, cfg.test4_max_height))


def suite_fuzz(cfg, tally):
    rng = random.Random(cfg.seed)
    for i in range(cfg.fuzz):
        for j, args in enumerate(difftest_cases.random_command_lines(rng)):
            against_c(cfg, tally, f'fuzz {i}.{j} {args}', args)


SUITES = {'test4': suite_test4, 'test3': suite_test3, 'rptest': suite_rptest,
          'random': suite_random, 'errors': suite_errors, 'fuzz': suite_fuzz,
          'params': suite_params, 'high': suite_high, 'test4high': suite_test4high}
# The suites that run by default (in CI): all but test4high.
DEFAULT_SUITES = ['test4', 'test3', 'rptest', 'random', 'errors', 'fuzz', 'params', 'high']


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--lean', type=Path, default=ROOT / '.lake' / 'build' / 'bin' /
                    'ratpoints-lean')
    ap.add_argument('--c', type=Path)
    ap.add_argument('--repo', type=Path)
    ap.add_argument('--suites', default=','.join(DEFAULT_SUITES))
    ap.add_argument('--max-height', type=int, default=30000)
    ap.add_argument('--test4-max-height', type=int, default=100000)
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
        lists = f' (point lists: {tally.in_order} in order)' if tally.in_order else ''
        print(f'{name}: {tally.compared} compared{lists}, {len(tally.failures)} failed'
              + (f'; skipped: {skipped}' if skipped else ''))
        for f in tally.failures:
            print(f'  FAIL {f}')
        failed += len(tally.failures)
    return 1 if failed else 0


if __name__ == '__main__':
    sys.exit(main())

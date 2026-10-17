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
  outputs random polynomials at small heights with random options of the output (-x -X -y -Y -z
          -Z -1 -i -I -q -v, formats and strings), against the C program;
  errors  the command lines of scripts/difftest_cases.py, for the checks that main.c makes on the
          coefficients, the height and the options, for the options of the search, -k -K -s -S, for
          those of the output, -x -X -y -Y -z -Z -1 -i -I and the formats and strings of -f -fs -fm
          -fe, for the report, and for the refusals of forms that are not squarefree, against the C
          program; searches at a large height that both programs stop at once
          (difftest_cases.STOP_CASES); the usage; and failed writes: a standard output whose reader
          is gone, which ends the C program by SIGPIPE, where ratpoints-lean (the Lean runtime
          ignores SIGPIPE) is to exit quietly with the status 141 that the shell reports for that,
          and a full device, whose failed writes both programs ignore;
  fuzz    random command lines (scripts/difftest_cases.py) against the C program;
  params  the options that set the sieving parameters (-p -n -N -P -F -j), with values that
          give no moduli, all the primes of the default build, the cut points in several
          positions, a third stage, the second and the third stage after few moduli or none in
          the first, and the defaults, on point-rich and on random curves against the C program,
          whose points do not depend on them;
  high    point-rich curves at the heights 2000, 5000 and 30000 against the C program;
  test4high  the invocations of test4.sh that search with a height bound above --max-height and
          at most --test4-max-height, a few minutes in all: run locally, not by default.

ratpoints-lean prints the points and the report as ratpoints does; they are compared in their order,
also where ratpoints visits the denominators divisor by divisor (a polynomial searched of odd degree
whose leading coefficient is not +-1), since the model visits them in the same order. An output of
points in the default format with -q is compared as a list of points with a recorded output (test4,
rptest), and exactly, byte for byte, with an output of the C program, as is an output with the
options of the output (-x -y -f -fs -fm -fe), also where it does not end with a newline. A report (a
command line without -q) is compared exactly, but for the banner, which is exchanged for that of the
C program, and for the lines that ratpoints-lean does not print, which are dropped from the report
of the C program only: the messages on the search region and the search intervals (stage H) and on
the moduli used (stage I), as test4.sh's m() drops the latter. Under -v, where the C program prints
the report of its library too, ratpoints-lean is compared with the report of the C program on the
same command line without -v, whose height and messages 4, 7 and 8 are dropped, as main.c does under
-v; the lines of that text must be among the lines of the output of the C program with -v, in their
order, with the same lines of points and pairs (with a format or a string, whose points need not end
their lines, only its characters among those of that output, in their order). The outputs that
test4.sh filters through grep found, grep 'Curve equation' and grep -c . are compared after the same
filter, the banner exchanged first, with the exit status 0. Under -x (no exact check), where the
lines printed are the survivors of the sieve, which depend on the moduli and on the search region:
when the output of ratpoints-lean does not change with the moduli pinned (-p 30 -N 30 appended,
which keeps the moduli of the model, the first 30 odd primes, but puts all of them into the first
two stages, in both programs, with no third stage, where the model without options puts the last 8
into its third stage), exactly with the output of the C program on the command line with -p 30 -N 30
-s appended, which then sieves with the same primes over the whole range of the height, without the
region of its Sturm step, as the model does until stages H and I; and, without a format or a string,
also by a weaker check against the output of the C program on the command line itself (the only
check when the pin changes the output of ratpoints-lean, as with other -p and -N): every line (x :
z) a normalized coprime pair in the range of the height, none repeated, the pairs that are points
the same and in the same order in both outputs, the pairs common to both in the same order, the
pairs in one block at the same place among the other lines, with -1 one line in each output when one
of them is a point (the same if both are) and else at most one, and the other lines equal, a count
line but for its number, which must be that of the pairs printed (unless -z); without -q on reports.
Exit codes are compared exactly, and ratpoints-lean must write nothing to its standard error: it
runs with LEAN_ABORT_ON_PANIC=1, so that a panic of the Lean runtime ends it by SIGABRT. Messages
are compared exactly, but for the banner and the usage, which differ by design: in the outputs of
errors 2 and 6 they are exchanged for those of the C program (the outputs of the two programs on an
empty command line), and the errors suite checks the usage of ratpoints-lean against that of
ratpoints. On a command line with an option that ratpoints-lean does not support yet (-l -u -dl
-du), also one whose output test4.sh filters, it must fail as the C program does if that fails
before the option, and else exit with status 12 and a message that names the option. A few searches
at a large height that both programs stop at a point at infinity before the sieve (-1) are run with
a short timeout and a cap on the memory. Skipped: the outputs that test4.sh filters to look at the
report of the library and those that test3.sh filters; searches under -x with a format or a string
whose output the pin changes; and searches above --max-height, which the suites that run the C
program compare when it prints nothing (a search with -q that finds no points, as when no class of
the denominators modulo 64 admits a numerator).

options:
  --lean PATH        the ratpoints-lean executable (default: .lake/build/bin/ratpoints-lean)
  --c PATH           the C program, built at the pinned commit (default: the environment variable
                     RATPOINTS_BIN, else the program ratpoints in the clone of --repo)
  --repo PATH        a clone of ratpoints that contains the pinned commit (default: the
                     environment variable RATPOINTS_REPO); the test files are read at the pin
  --suites LIST      comma-separated suites (default: test4,test3,rptest,random,outputs,errors,
                     fuzz,params,high)
  --max-height H     the largest height of a search (default: 30000)
  --test4-max-height H  the largest height of a search of the suite test4high (default: 100000)
  --rptest-height h  the reduced height of the rptest suites (default: 100)
  --random N         the number of random polynomials (default: 300)
  --outputs N        the number of random polynomials of the suite outputs (default: 300)
  --fuzz N           the number of rounds of random command lines, eight each (default: 100)
  --seed S           the seed of the random suites (default: 1)
  -v                 print every comparison
"""
import argparse
import math
import os
import random
import re
import resource
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
# ratpoints-lean reads the switches, the tuning options that take an argument, -S, whose argument
# is optional: the next word, if there is one and it does not start with -, and -f, -fs, -fm and
# -fe, which take the next word, whatever it is; the options of the search region and the range of
# the denominators, -l -u -dl -du, it does not support yet; any other word is error 6.
ARG_OPTS = set('pFtnNRAPrUCQW')
FLAGS = set('qvjJkKsxXyYzZ1iI')
UNSUPPORTED = set('lu')
STRING_OPTS = ('', 's', 'm', 'e')  # the third character of -f, -fs, -fm, -fe
POINT = re.compile(r'^\((-?\d+) : (-?\d+) : (\d+)\)$')
PAIR = re.compile(r'^\((-?\d+) : (-?\d+)\)$')
COUNT = re.compile(r'^-?\d+ rational point(?: pair)?s found\.$')
# The filters of test4.sh that ratpoints-lean is compared under; the others look at the report of
# the library, which it does not print.
FILTERS = {'grep found': lambda ls: [l for l in ls if 'found' in l],
           "grep 'Curve equation'": lambda ls: [l for l in ls if 'Curve equation' in l],
           'grep -c .': lambda ls: [str(sum(1 for l in ls if l))]}
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
# The stop cases of the errors suite (difftest_cases.STOP_CASES), searches at a large height that
# both programs stop at a point at infinity before the sieve: ratpoints-lean must end within
# STOP_TIMEOUT seconds with its address space capped at STOP_MEMORY bytes.
STOP_TIMEOUT = 30
STOP_MEMORY = 4 * 10 ** 9
# The parameters that pin the moduli for the exact comparison under -x: the first 30 odd primes,
# the moduli of the model without options, put into the first two stages of both programs, with no
# third stage (the model without options puts the last 8 into its third stage).
PIN = ['-p', '30', '-N', '30']
# The environment of ratpoints-lean: LEAN_ABORT_ON_PANIC=1 turns a panic of the Lean runtime (an
# index out of bounds, after which the program would go on with a default value) into SIGABRT,
# which every comparison of the exit code catches.
LEAN_ENV = {**os.environ, 'LEAN_ABORT_ON_PANIC': '1'}


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
    """What a suite compared, skipped and found: the number of comparisons, among them those of the
    output of a search in its order (`in_order`: a list of points, an exact output or a report),
    and those of a search under -x, exactly against the C program with the moduli pinned and
    without its Sturm step, and by the weaker check against the C program unless a format or a
    string is given (`x_exact`), or by the weaker check only (`x_weak`); the skipped runs by their
    reason; and the failures."""
    compared: int = 0
    in_order: int = 0
    x_exact: int = 0
    x_weak: int = 0
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


def no_core():
    """No core dump for a program that the harness runs (a panic of ratpoints-lean ends it by
    SIGABRT)."""
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))


def run3(prog, args, env=None, timeout=TIMEOUT, limit=None):
    """The standard output, the exit code and the standard error of `prog` on the command line
    `args`, in the environment `env` (by default that of the harness), within `timeout` seconds
    (else subprocess.TimeoutExpired), without a core dump and with the address space capped at
    `limit` bytes if given."""
    def cap():
        no_core()
        if limit:
            resource.setrlimit(resource.RLIMIT_AS, (limit, limit))
    r = subprocess.run([str(prog), *args], capture_output=True, timeout=timeout, env=env,
                       preexec_fn=cap)
    return r.stdout.decode('latin-1'), r.returncode, r.stderr.decode('latin-1')


def run(prog, args):
    """The standard output and the exit code of `prog` on the command line `args` (for the C
    program)."""
    return run3(prog, args)[:2]


def run_lean(cfg, args, timeout=TIMEOUT, limit=None):
    """The standard output, the exit code and the standard error of ratpoints-lean on the command
    line `args`, in LEAN_ENV."""
    return run3(cfg.lean, args, LEAN_ENV, timeout, limit)


def closed_pipe(prog, args, env=None):
    """The return code (minus the signal that ends the program, if one does) and the standard
    error of `prog` on the command line `args` when its standard output is a pipe that nobody
    reads: its reader was closed before the program started. subprocess restores the default
    action of SIGPIPE in the program."""
    r, w = os.pipe()
    os.close(r)
    try:
        p = subprocess.run([str(prog), *args], stdout=w, stderr=subprocess.PIPE, timeout=TIMEOUT,
                           env=env, preexec_fn=no_core)
    finally:
        os.close(w)
    return p.returncode, p.stderr.decode('latin-1')


def full_device(prog, args, env=None):
    """The return code and the standard error of `prog` on the command line `args` when its
    standard output is /dev/full, on which every write fails."""
    with open('/dev/full', 'w') as f:
        p = subprocess.run([str(prog), *args], stdout=f, stderr=subprocess.PIPE, timeout=TIMEOUT,
                           env=env, preexec_fn=no_core)
    return p.returncode, p.stderr.decode('latin-1')


def special(cfg, tally, label, ok, detail):
    """Record a check that is not a comparison of outputs."""
    tally.compared += 1
    if not ok:
        tally.failures.append(f'{label}: {detail}')
    if cfg.verbose:
        print(('ok   ' if ok else 'FAIL ') + label)


def option_words(opts):
    """The options among the words `opts` after the height, as ratpoints-lean reads them: the list
    of (index, word, argument or None) up to the first option that it does not support yet or the
    first word that is no option of ratpoints (or a missing argument), and the index of that word
    (None if it reaches the end) and whether it is an option that it does not support yet."""
    words, i = [], 0
    while i < len(opts):
        o = as_bytes(opts[i]).decode('latin-1')
        if len(o) < 2 or o[0] != '-':
            return words, i, False
        if o[1] in ARG_OPTS or o[1] == 'f' and o[2:3] in STRING_OPTS:
            if i + 1 >= len(opts):
                return words, i, False
            words.append((i, o, opts[i + 1]))
            i += 2
        elif o[1] == 'S':
            takes = i + 1 < len(opts) and not as_bytes(opts[i + 1]).startswith(b'-')
            words.append((i, o, opts[i + 1] if takes else None))
            i += 2 if takes else 1
        elif o[1] in FLAGS:
            words.append((i, o, None))
            i += 1
        elif o[1] in UNSUPPORTED or o[1] == 'd' and o[2:3] in ('l', 'u'):
            return words, i, True
        else:
            return words, i, False
    return words, None, False


def read_options(opts):
    """How ratpoints-lean reads the options `opts`, the words after the height: the index of the
    first that it does not support yet (None if it reaches the end or a word that is no option of
    ratpoints first), and whether -q comes before it."""
    words, stop, unsupported = option_words(opts)
    quiet = any(o[1] == 'q' for _, o, _ in words)
    return (stop if unsupported else None), quiet


def as_long(arg):
    """The C long that the argument of an option gives, or None (for the pins of -x)."""
    try:
        return int(as_bytes(arg).decode('latin-1').strip())
    except ValueError:
        return None


@dataclass
class Settings:
    """The settings of a command line that decide how its output is compared: -q, -v (cancelled
    by -q), -x, -y, -z and -1, the last of each pair winning, whether a format or a string is given,
    the last values of -p and -N, and the indices of the words -v among the options."""
    quiet: bool = False
    verbose: bool = False
    x: bool = False
    y: bool = False
    z: bool = False
    one: bool = False
    strings: bool = False
    p: int | None = None
    N: int | None = None
    v_words: list = field(default_factory=list)

    @property
    def pinned(self):
        """Whether the parameters pin the moduli: -p 30 -N 30, under which both programs sieve with
        the first 30 odd primes in their first two stages and no third stage, so that the survivors
        that -x prints are the same."""
        return self.p == 30 and self.N == 30

    @property
    def plain(self):
        """Whether the output with -q is a list of points in the default format."""
        return not (self.x or self.y or self.strings)


def settings(opts):
    """The settings of the options `opts`, the words after the height, as far as ratpoints-lean
    reads them."""
    st = Settings()
    for i, o, a in option_words(opts)[0]:
        c = o[1]
        if c == 'q':
            st.quiet = True
        elif c == 'v':
            st.verbose = True
            st.v_words.append(i)
        elif c in 'xX':
            st.x = c == 'x'
        elif c in 'yY':
            st.y = c == 'y'
        elif c in 'zZ':
            st.z = c == 'z'
        elif c == '1':
            st.one = True
        elif c == 'f':
            st.strings = True
        elif c == 'p':
            st.p = as_long(a)
        elif c == 'N':
            st.N = as_long(a)
    st.verbose = st.verbose and not st.quiet
    return st


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


def lines_of(text):
    """The lines of an output, the last one also when it does not end with a newline."""
    lines = text.split('\n')
    if lines and lines[-1] == '':
        lines.pop()
    return lines


def points(text):
    """The points of an output that consists of point lines only, as a list in their order (else
    None)."""
    lines = lines_of(text)
    if not all(POINT.match(l) for l in lines):
        return None
    return [tuple(int(g) for g in POINT.match(l).groups()) for l in lines]


def point_lines(text):
    """The lines of an output that are points (x : y : z) or pairs (x : z), in their order."""
    return [l for l in lines_of(text) if POINT.match(l) or PAIR.match(l)]


def banner_of(usage):
    """The banner in the output of a program on an empty command line: what stands between the
    first newline and the newline before the usage."""
    return usage[1:usage.index('Usage: ') - 1]


def report_text(cfg, text, lean=False):
    """A report as it is compared: the first line of the banner, which test4.sh's m() drops, left
    out, for ratpoints-lean (`lean`) after its banner is exchanged for that of the C program; and
    of a report of the C program also the lines that ratpoints-lean does not print, which m() drops
    in part: those on the moduli used (message 4, stage I), and the messages on the search region
    (message 3) and the search intervals (message 8, stage H), each with the line after it."""
    if lean:
        text = text.replace(cfg.lean_banner, cfg.c_banner)
    out, skip = [], False
    for l in text.split('\n'):
        if skip:
            skip = False
        elif l.startswith('This is ratpoints-'):
            continue
        elif lean:
            out.append(l)
        elif l in ('Search region:', 'Search intervals:'):
            skip = True
        elif not re.search('used for|further primes|primes used', l):
            out.append(l)
    return '\n'.join(out)


def as_verbose(text):
    """What main.c prints under -v, but for the report of the library, from its report `text` on
    the same command line without -v: the height bound and the blank line after it, and after the
    points the two newlines and the messages on the moduli used, what the search did and the search
    intervals, left out."""
    text = re.sub(r'max\. Height = \d+\n\n', '', text, count=1)
    return re.sub(r'\n\n-?\d+ moduli used for first stage of sieving,\n.*?'
                  r'(?=\n-?\d+ rational point(?: pair)?s found\.\n\n\Z)', '', text, count=1,
                  flags=re.S)


def verbose_consistent(exp, out, strings=False):
    """Whether the text `exp` that ratpoints-lean is to print under -v is consistent with the output
    `out` of the C program with -v, which holds the report of its library too: the lines of `exp`
    are among the lines of `out`, in their order, and the lines of points and pairs of the two are
    the same, in the same order; with a format or a string (`strings`), whose points need not end
    their lines, so that the library may write into a line of points, only the characters of `exp`
    among those of `out`, in their order."""
    if strings:
        it = iter(out)
        return all(ch in it for ch in exp)
    it = iter(lines_of(out))
    return all(l in it for l in lines_of(exp)) and point_lines(exp) == point_lines(out)


def coefficients(arg):
    """The coefficient list of a command line that the C program accepted, constant term first."""
    return [int(w) for w in as_bytes(arg).decode('latin-1').split()]


def is_point(c, a, b):
    """Whether (a : b) is the x-coordinate of a point of y^2 = F(x, z) for the coefficient list c:
    F(a, b) a square, for the binary form of the even degree d + d % 2, d the degree of c."""
    d = max((i for i, ci in enumerate(c) if ci), default=0)
    v = sum(ci * a ** i * b ** (d + d % 2 - i) for i, ci in enumerate(c[:d + 1]))
    return v >= 0 and math.isqrt(v) ** 2 == v


def weak_agrees(lean_text, exp_text, args, st):
    """The weaker check of an output under -x, whose lines (x : z) are the survivors of the sieve,
    which depend on the moduli and on the search region: every such line a normalized coprime pair
    in the range of the height in both outputs, none repeated; the pairs that are points the same
    and in the same order, and the pairs common to both outputs in the same order; under -1, when
    one of the two lines (if any) is a point, one line in each output, the same if both are points
    (a point survives every sieve), and else at most one line in each; the pairs in one block in
    each output, at the same place among the other lines when both have pairs; the other lines
    equal, the count lines among them with their numbers left out, and each count that of the pairs
    printed (unless -z)."""
    c, H = coefficients(args[0]), height(as_bytes(args[1]).decode('latin-1'))

    def split(text):
        """The pairs of an output, its other lines (the number of a count line masked), the
        number of those before the first pair (None without pairs), whether the pairs are one
        block, and the counts."""
        pairs, rest, before, block, counts, last = [], [], None, True, [], None
        for k, l in enumerate(lines_of(text)):
            m = PAIR.match(l)
            if m:
                block = block and (last is None or last == k - 1)
                before = len(rest) if before is None else before
                pairs.append(tuple(int(g) for g in m.groups()))
                last = k
            else:
                if COUNT.match(l):
                    counts.append(int(l.split()[0]))
                    l = re.sub(r'^-?\d+', '#', l)
                rest.append(l)
        return pairs, rest, before, block, counts

    (lp, lr, lb, lk, lc), (ep, er, eb, ek, ec) = split(lean_text), split(exp_text)
    valid = all((b > 0 and math.gcd(a, b) == 1 or (a, b) == (1, 0)) and abs(a) <= H and b <= H
                for a, b in lp + ep) and len(set(lp)) == len(lp) and len(set(ep)) == len(ep)
    blocks = lk and ek and (lb == eb or lb is None or eb is None)
    common = [p for p in lp if p in set(ep)] == [p for p in ep if p in set(lp)]
    counts = st.z or all(n == len(ps) for ns, ps in ((lc, lp), (ec, ep)) for n in ns)
    lpts, epts = [p for p in lp if is_point(c, *p)], [p for p in ep if is_point(c, *p)]
    if not st.one:
        order = lpts == epts
    elif lpts or epts:
        order = len(lp) == 1 and len(ep) == 1 and (not (lpts and epts) or lp == ep)
    else:
        order = len(lp) <= 1 and len(ep) <= 1
    return valid and lr == er and blocks and common and counts and order


def agrees(cfg, lean, expected, mode, args=None, st=None):
    """Whether the output and exit code `lean` of ratpoints-lean agree with `expected`: in the mode
    'points' as lists of points in their order (exit 0), in 'report' as reports (report_text), in
    'weak' by the weaker check of -x (weak_agrees, on reports when there is no -q), in 'filter:F'
    after the filter F of test4.sh, the banner exchanged first (exit 0), in 'exact' exactly and in
    'e' as test4.sh's e() records them (the banner of a report exchanged for that of the C
    program), the usage exchanged for that of the C program."""
    (out, code), (exp, exp_code) = lean, expected
    if mode == 'points':
        got = points(out)
        return code == 0 and got is not None and got == points(exp)
    if mode == 'report':
        return code == exp_code and report_text(cfg, out, lean=True) == report_text(cfg, exp)
    if mode == 'weak':
        if not st.quiet:
            out, exp = report_text(cfg, out, lean=True), report_text(cfg, exp)
        return code == exp_code and weak_agrees(out, exp, args, st)
    if mode.startswith('filter:'):  # all the filtered runs of test4.sh are searches: exit 0
        out = out.replace(cfg.lean_banner, cfg.c_banner)
        return code == 0 and ''.join(l + '\n' for l in FILTERS[mode[7:]](lines_of(out))) == exp
    out = out.replace(cfg.lean_usage, cfg.c_usage)
    if mode == 'e':  # also an e() record of a report, whose banner is exchanged
        out = as_recorded_by_e(out.replace(cfg.lean_banner, cfg.c_banner))
    return out == exp and code == exp_code


def verdict(cfg, lean, expected, mode, args=None, st=None):
    """Whether the run `lean` of ratpoints-lean, its output, exit code and standard error, agrees
    with `expected` in the mode `mode` (agrees) and wrote nothing to its standard error, as the C
    program never does (ratpoints-lean writes there only when the Lean runtime panics)."""
    return lean[2] == '' and agrees(cfg, lean[:2], expected, mode, args, st)


def failure_text(label, expected, lean):
    """The report of a failed comparison of the run `lean` with `expected`."""
    err = f' and on its standard error {lean[2][:500]!r}' if lean[2] else ''
    return (f'{label}: expected exit {expected[1]} and {expected[0][:500]!r}, '
            f'got exit {lean[1]} and {lean[0][:500]!r}{err}')


def check(cfg, tally, label, args, expected, mode, st=None, lean=None):
    """Run ratpoints-lean on `args` (unless its run `lean` is given) and compare it with `expected`
    (see verdict)."""
    lean = lean or run_lean(cfg, args)
    ok = verdict(cfg, lean, expected, mode, args, st)
    tally.compared += 1
    tally.in_order += mode in ('points', 'report', 'exact') and expected[1] == 0
    if not ok:
        tally.failures.append(failure_text(label, expected, lean))
    if cfg.verbose:
        print(('ok   ' if ok else 'FAIL ') + label)


def mode_of(st, code):
    """How an output of ratpoints-lean is compared with an output of the C program that ends with
    the exit code `code`, for the settings `st` of the command line: a failure before the search
    exactly; error 8 exactly with -q and as a report without; a search under -x without pinned
    moduli by the weaker check; without -q as a report; with -q as a list of points in the default
    format, else exactly."""
    if code not in (0, 8):
        return 'exact'
    if code == 8:
        return 'exact' if st.quiet else 'report'
    if st.x and not st.pinned:
        return 'weak'
    if not st.quiet:
        return 'report'
    return 'points' if st.plain else 'exact'


def skips_height(cfg, args, out, code):
    """Whether the comparison with the C program, which ended with the output `out` and the exit
    code `code` on the command line `args`, is skipped: a search above --max-height on which the C
    program prints something (one that prints nothing is quick for both and is compared)."""
    return (code == 0 and bool(out) and
            (height(as_bytes(args[1]).decode('latin-1')) or 0) > cfg.max_height)


def c_expected(cfg, args, st):
    """The output and the exit code of the C program that ratpoints-lean is compared with on the
    command line `args` with the settings `st`, and whether they are consistent: under -v, its
    report on the command line without the options -v as main.c prints it under -v (as_verbose),
    which must be consistent with its output with -v, which has the report of the library too
    (verbose_consistent)."""
    out, code = run(cfg.c, args)
    if not st.verbose or code not in (0, 8):
        return out, code, True
    plain, plain_code = run(cfg.c, [a for i, a in enumerate(args) if i - 2 not in st.v_words])
    exp = as_verbose(plain)
    return exp, plain_code, plain_code == code and verbose_consistent(exp, out, st.strings)


def live_mode(mode):
    """The mode of a comparison with a live output of the C program: a list of points exactly, also
    its final newline (a recorded output of test4.sh or rptest may lack it)."""
    return 'exact' if mode == 'points' else mode


def check_x(cfg, tally, label, args, st, expected):
    """Compare ratpoints-lean with the C program on a search under -x (no exact check) on the
    command line `args` with the settings `st`, whose lines (x : z) are the survivors of the sieve,
    which depend on the moduli and on the search region, and whose output of the C program is
    `expected`: when the output of ratpoints-lean does not change with the moduli pinned (PIN
    appended), so that they are those of the model, exactly against the C program on the command
    line with PIN and -s appended, which then sieves with the same primes over the whole range of
    the height, without the region of its Sturm step, as the model does until stages H and I; and,
    without a format or a string, whose lines it could not read, also by the weaker check against
    `expected` (weak_agrees). A run with a format or a string whose output changes with the moduli
    pinned is skipped."""
    lean = run_lean(cfg, args)
    exact = lean == run_lean(cfg, [*args, *PIN])
    if not exact and st.strings:
        tally.skip('-x with a format or a string and moduli other than those of the model')
        return
    fails = []
    if not st.strings and not verdict(cfg, lean, expected, 'weak', args, st):
        fails.append(failure_text(f'{label} (the weaker check)', expected, lean))
    if exact:
        tally.x_exact += 1
        pargs = [*args, *PIN, '-s']
        pst = settings(pargs[2:])
        out, code, consistent = c_expected(cfg, pargs, pst)
        if not consistent:
            fails.append(f'{label}: the report of the C program on {pargs} without -v is not '
                         f'consistent with its output with -v')
        elif not verdict(cfg, lean, (out, code), live_mode(mode_of(pst, code)), pargs, pst):
            fails.append(failure_text(f'{label} (exactly against {pargs})', (out, code), lean))
    else:
        tally.x_weak += 1
    tally.compared += 1
    if fails:
        tally.failures.append('; '.join(fails))
    if cfg.verbose:
        print(('FAIL ' if fails else 'ok   ') + label)


def against_c(cfg, tally, label, args):
    """Compare ratpoints-lean with the C program on the command line `args`, a search under -x by
    check_x."""
    k, _ = read_options(args[2:])
    if len(args) >= 2 and k is not None:
        check(cfg, tally, label, args, expected_unsupported(cfg, args, k), 'exact')
        return
    st = settings(args[2:])
    out, code, consistent = c_expected(cfg, args, st)
    if skips_height(cfg, args, out, code):
        tally.skip(f'height above {cfg.max_height}')
    elif not consistent:
        tally.compared += 1
        tally.failures.append(f'{label}: the report of the C program without -v is not consistent '
                              f'with its output with -v')
    elif st.x and code == 0:
        check_x(cfg, tally, label, args, st, (out, code))
    else:
        check(cfg, tally, label, args, (out, code), live_mode(mode_of(st, code)), st)


def stop_case(cfg, tally, label, args):
    """Compare ratpoints-lean exactly with the C program on a search at a large height that both
    stop at a point at infinity before the sieve (difftest_cases.STOP_CASES), ratpoints-lean within
    STOP_TIMEOUT seconds and with its address space capped at STOP_MEMORY bytes; a run that does
    not end in time is a failure."""
    expected = run(cfg.c, args)
    try:
        lean = run_lean(cfg, args, STOP_TIMEOUT, STOP_MEMORY)
    except subprocess.TimeoutExpired:
        tally.compared += 1
        tally.failures.append(f'{label}: ratpoints-lean did not end within {STOP_TIMEOUT} s')
        return
    check(cfg, tally, label, args, expected, 'exact', lean=lean)


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


def compare_search(cfg, tally, label, args, text, st):
    """Compare ratpoints-lean with the output `text` of a search that testbase4 records for the
    command line `args` with the settings `st`: under -v with the C program (whose report of the
    library test4.sh's v() filters), under -x by check_x with `text` as the output of the C program
    on `args`, else with `text`."""
    if st.verbose:
        against_c(cfg, tally, label, args)
    elif st.x:
        check_x(cfg, tally, label, args, st, (text, 0))
    else:
        check(cfg, tally, label, args, (text, 0), mode_of(st, 0), st)


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
        k, _ = read_options(r.args[2:])
        st = settings(r.args[2:])
        unsupported = len(r.args) >= 2 and k is not None
        if window is not None:
            searches = (r.filt is None and not unsupported and not code and
                        'Polynomial is not square-free.' not in text)
            if searches and window[0] < (height(r.args[1]) or 0) <= window[1]:
                compare_search(cfg, tally, label, r.args, text, st)
            continue
        if unsupported:  # also when test4.sh filters the output
            check(cfg, tally, label, r.args, expected_unsupported(cfg, r.args, k), 'exact')
        elif r.filt is not None:
            if r.filt not in FILTERS:
                tally.skip('output filtered')
            else:
                check(cfg, tally, label, r.args, (text, 0), 'filter:' + r.filt, st)
        elif code == 8 or 'Polynomial is not square-free.' in text:
            # error 8, recorded by e() with -q, and without -q at the end of a report
            if st.verbose:
                against_c(cfg, tally, label, r.args)
            else:
                check(cfg, tally, label, r.args, (text, 8),
                      'e' if code else 'exact' if st.quiet else 'report', st)
        elif code:
            check(cfg, tally, label, r.args, (text, code), 'e')
        elif (height(r.args[1]) or 0) > cfg.max_height:
            tally.skip(f'height above {cfg.max_height}')
        else:
            compare_search(cfg, tally, label, r.args, text, st)


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


def suite_outputs(cfg, tally):
    """Random polynomials at small heights with random options of the output, against the C
    program."""
    rng = random.Random(cfg.seed)
    for i in range(cfg.outputs):
        deg = rng.randint(1, 8)
        c = [rng.randint(-10, 10) for _ in range(deg + 1)]
        args = [' '.join(map(str, c)), str(rng.randint(1, 30)),
                *difftest_cases.random_output_options(rng)]
        against_c(cfg, tally, f'outputs {i} {args}', args)


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
        lean, c = closed_pipe(cfg.lean, args, LEAN_ENV), closed_pipe(cfg.c, args)
        ok = ((c, lean) == ((-signal.SIGPIPE, ''), (128 + signal.SIGPIPE, '')) if writes else
              c == lean == (0, ''))
        special(cfg, tally, f'a closed pipe: {args}', ok,
                f'ratpoints-lean gives {lean}, the C program {c}')
    if os.path.exists('/dev/full'):
        for args in (['1 0 1', '10', '-q'], ['1 0 1', '300', '-q'], ['1 2 x', '10']):
            lean, c = full_device(cfg.lean, args, LEAN_ENV), full_device(cfg.c, args)
            special(cfg, tally, f'a full device: {args}', lean == c and c[1] == '',
                    f'ratpoints-lean gives {lean}, the C program {c}')
    for args, note in difftest_cases.CASES:
        against_c(cfg, tally, f'{note}: {args}', args)
    for args, note in difftest_cases.STOP_CASES:
        stop_case(cfg, tally, f'{note}: {args}', args)


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
          'random': suite_random, 'outputs': suite_outputs, 'errors': suite_errors,
          'fuzz': suite_fuzz, 'params': suite_params, 'high': suite_high,
          'test4high': suite_test4high}
# The suites that run by default (in CI): all but test4high.
DEFAULT_SUITES = ['test4', 'test3', 'rptest', 'random', 'outputs', 'errors', 'fuzz', 'params',
                  'high']


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
    ap.add_argument('--outputs', type=int, default=300)
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
    cfg.c_usage, cfg.lean_usage = run(cfg.c, [])[0], run_lean(cfg, [])[0]
    cfg.c_banner, cfg.lean_banner = banner_of(cfg.c_usage), banner_of(cfg.lean_usage)
    failed = 0
    for name in cfg.suites.split(','):
        tally = Tally()
        SUITES[name](cfg, tally)
        skipped = ', '.join(f'{k} {v}' for k, v in sorted(tally.skipped.items()))
        parts = [f'{tally.in_order} outputs of searches in order'] if tally.in_order else []
        if tally.x_exact or tally.x_weak:
            parts.append(f'-x: {tally.x_exact} exactly, {tally.x_weak} by the weaker check only')
        detail = f' ({"; ".join(parts)})' if parts else ''
        print(f'{name}: {tally.compared} compared{detail}, {len(tally.failures)} failed'
              + (f'; skipped: {skipped}' if skipped else ''))
        for f in tally.failures:
            print(f'  FAIL {f}')
        failed += len(tally.failures)
    return 1 if failed else 0


if __name__ == '__main__':
    sys.exit(main())

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
  outputs random polynomials at small heights with random options of the output (-x -X -y -Y -z -Z
          -1 -i -I -q -v, formats and strings, and -s with -x at times), against the C program;
  errors  the command lines of scripts/difftest_cases.py, for the checks that main.c makes on the
          coefficients, the height and the options, for the options of the search, -k -K -s -S, for
          the search region, -l -u -dl -du (errors 7 and 6, the join, the filter of process, the
          suppression of the reversal), for those of the output, -x -X -y -Y -z -Z -1 -i -I and the
          formats and strings of -f -fs -fm -fe, for the report, and for the refusals of forms that
          are not squarefree, against the C program; searches at a large height that both programs
          stop at once (difftest_cases.STOP_CASES); the usage; and failed writes: a standard output
          whose reader is gone, which ends the C program by SIGPIPE, where ratpoints-lean (the Lean
          runtime ignores SIGPIPE) is to exit quietly with the status 141 that the shell reports for
          that, and a full device, whose failed writes both programs ignore;
  fuzz    random command lines (scripts/difftest_cases.py) against the C program;
  params  the options that set the sieving parameters (-p -n -N -P -F -j), with values that
          give no moduli, all the primes of the default build, the cut points in several
          positions, a third stage, the second and the third stage after few moduli or none in
          the first, and the defaults, on point-rich and on random curves against the C program,
          whose points do not depend on them;
  high    point-rich curves at the heights 2000, 5000 and 30000 against the C program, and curves
          at 16383 where the C program corrects its moduli during the run and the correction
          changes the survivors under -x and message 4 (-x without -A and with -A 1 and -A 2, and a
          report with message 4);
  regions random search regions against the C program: intervals with ends of every kind (decimals,
          hexadecimal constants, ends that are no doubles, infinities, numbers beyond the doubles,
          tiny ones, -0, intervals that touch or whose doubles meet, a missing first -l or last -u),
          ranges of denominators of every shape, with random options, at small heights, and at times
          at a large height with a narrow region, whose ends are exact doubles at times, also around
          points of large height and at the ends of the range [-H, H] of the numerators, at times
          under -x, at times with -p 30 -N 30 (scripts/difftest_cases.py);
  depths  random depths of the Sturm step, -S 0 to -S 60 and -s, against the C program, with -q or
          the report (message 8), at times with intervals, -k or -x, at times with -p 30 -N 30,
          then at times -s;
  tuning  random values of the tuning options (-r -R -U -C -A -Q -W, with infinities, zeros, the
          smallest double and huge values) with the cut points (-p -n -N -P) at times, on random
          polynomials at small heights, at times under -x and at times with the report (message 4),
          against the C program;
  threads the C program with -t 4 and -t 7 against ratpoints-lean, which reads -t and sieves on one
          thread: random polynomials at small heights, at times under -x, the point-rich curves at
          30000 under -x, on one of which the C program decides a correction of the moduli without
          an effect on the output, and a curve at 16383 under -x where the correction changes the
          survivors;
  verbose random searches under -v, with the report of the library, against the C program: random
          polynomials with small and at times large coefficients and point-rich curves at heights
          of at most 2000, with random options of the search, the output, the sieve and the tuning
          and at times a search region (scripts/difftest_cases.py);
  test4high  the invocations of test4.sh that search with a height bound above --max-height and
          at most --test4-max-height that the suite test4 does not compare (those without a narrow
          search region), a few minutes in all: run locally, not by default;
  adapt   searches where the C program corrects its moduli during the run (adapt_primes), at the
          heights 16383 to 50000 (18 of its 23 command lines change their output with -A, the
          others are controls), under -x with -A 0, 1 and 2 and without -A, with tuning options at
          times, on point-rich curves and on curves of testdata.h on which a correction takes
          effect, against the C program: run locally, not by default (some minutes).

ratpoints-lean prints the points and the report as ratpoints does; they are compared in their order,
also where ratpoints visits the denominators divisor by divisor (a polynomial searched of odd degree
whose leading coefficient is not +-1), since the model visits them in the same order. An output of
points in the default format with -q is compared as a list of points with a recorded output (test4,
rptest), and exactly, byte for byte, with an output of the C program, as is an output with the
options of the output (-x -y -f -fs -fm -fe), also where it does not end with a newline. A report (a
command line without -q) is compared exactly, with the messages on the moduli used (message 4), the
search region (message 3) and the search intervals (message 8), but for the banner, which is
exchanged for that of the C program. A report of test4.sh, whose m() drops message 4 from the
reports that it records, is compared with the C program on its command line, a disagreement of the C
program with the record (both without the lines that m() drops) being noted apart, not counted as a
failure. Under -v, where the library prints its report between the points, the output is compared
exactly in the same way, byte for byte but for the banner, with the output of the C program on the
same command line, also for the runs of test4.sh's v(), which records the report without the lines
that depend on the build, and for the runs of test3.sh that filter the report, by the whole output
of the command before the filter. The outputs that test4.sh filters through grep found, grep 'Curve
equation', grep -c ., grep 'bits set per word' | sed 's/,.*//' and grep 'iterations for' are
compared after the same filter, the banner exchanged first, with the exit status 0, and also as a
whole with the C program on their command line. Under -x (no exact check), where the lines printed are the survivors of the
sieve, which depend on the moduli and on the search region: exactly with the output of the C program
on the same command line, since the model chooses its moduli from the curve and corrects them during
the run as the C program does, also on the runs of test4.sh under -x, which are compared with the C
program, a disagreement of the C program with the output that testbase4 records being noted apart,
not counted as a failure, the choice of the moduli computing with the log and pow of the platform
(the runs where the C program may correct its choice are counted: neither -n nor -N gives a value >=
0, -A does not give 0, and the run can pass RP_ADAPT_WORDS = 10^6 numerator words, by an upper bound
from the denominators, the search intervals and the height bound); and, without a format or a
string and without -v, whose report of the library comes between the pairs, also by a weaker check
against the output of the C program: every line (x : z) a normalized
coprime pair in the range of the height and, but for (1 : 0), with z in the range of the
denominators and x / z in the exact search region of the command line, none repeated, the pairs that
are points the same and in the same order in both outputs, the pairs common to both in the same
order, the pairs in one block at the same place among the other lines, with -1 one line in each
output when one of them is a point (the same if both are) and else at most one, and the other lines
equal, a count line but for its number, which must be that of the pairs printed (unless -z); without
-q on reports. Exit codes are compared exactly, and ratpoints-lean must write nothing to its
standard error: it runs with LEAN_ABORT_ON_PANIC=1, so that a panic of the Lean runtime ends it by
SIGABRT. Messages are compared exactly, but for the banner and the usage, which differ by design: in
the outputs of errors 2 and 6 they are exchanged for those of the C program (the outputs of the two
programs on an empty command line), and the errors suite checks the usage of ratpoints-lean against
that of ratpoints. A few searches at a large height that both programs stop at a point at infinity
before the sieve (-1) are run with a short timeout and a cap on the memory. A search above
--max-height with a search region is compared, with a timeout and a cap on the memory, when the
model sifts at most 10^5 denominators for it (an upper bound that mirrors the divisor set-up of the
model) and sifts at most 2 * 10^10 numerators (an upper bound from the widths of the intervals, and
under -1 from the first point of the expected output, where the search stops): the searches of
test4.sh at large heights in a narrow region. The runs of test3.sh whose output a pipe filters are
compared with the C program on the whole output of the command before the pipe. Skipped: the other
searches above --max-height, which the suites that run the C program compare when they have no
search region and it prints nothing (a search with -q that finds no points, as when no class of the
denominators modulo 64 admits a numerator).

options:
  --lean PATH        the ratpoints-lean executable (default: .lake/build/bin/ratpoints-lean)
  --c PATH           the C program, built at the pinned commit without a tuning.mk, which the
                     harness refuses (default: the environment variable RATPOINTS_BIN, else the
                     program ratpoints in the clone of --repo)
  --repo PATH        a clone of ratpoints that contains the pinned commit (default: the
                     environment variable RATPOINTS_REPO); the test files are read at the pin
  --suites LIST      comma-separated suites (default: test4,test3,rptest,random,outputs,errors,
                     fuzz,params,high,regions,depths,tuning,threads,verbose)
  --max-height H     the largest height of a search (default: 30000)
  --test4-max-height H  the largest height of a search of the suite test4high (default: 100000)
  --rptest-height h  the reduced height of the rptest suites (default: 100)
  --random N         the number of random polynomials (default: 300)
  --outputs N        the number of random polynomials of the suite outputs (default: 300)
  --fuzz N           the number of rounds of random command lines, eight each (default: 100)
  --regions N        the number of searches of the suite regions (default: 400)
  --depths N         the number of searches of the suite depths (default: 300)
  --tuning N         the number of searches of the suite tuning (default: 300)
  --threads N        the number of random polynomials of the suite threads, run with -t 4 and -t 7
                     (default: 100)
  --verbose-runs N   the number of searches of the suite verbose (default: 300)
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
from fractions import Fraction
from pathlib import Path

import difftest_cases

ROOT = Path(__file__).resolve().parent.parent
RECORD = ROOT / 'correspondence' / 'ratpoints.toml'

# main.c tells its options apart by their second character, and -f and -d by the third too: the
# switches, the tuning options that take an argument, -S, whose argument is optional: the next
# word, if there is one and it does not start with -, -f, -fs, -fm and -fe, which take the next
# word, whatever it is, -dl and -du, which take a long, and -l and -u, which take an end of a
# search interval (a missing one is error 7); any other word is error 6.
ARG_OPTS = set('pFtnNRAPrUCQW')
FLAGS = set('qvjJkKsxXyYzZ1iI')
REGION_OPTS = set('lu')
STRING_OPTS = ('', 's', 'm', 'e')  # the third character of -f, -fs, -fm, -fe
DEN_OPTS = ('l', 'u')  # the third character of -dl, -du
POINT = re.compile(r'^\((-?\d+) : (-?\d+) : (\d+)\)$')
PAIR = re.compile(r'^\((-?\d+) : (-?\d+)\)$')
COUNT = re.compile(r'^-?\d+ rational point(?: pair)?s found\.$')
# The filters of test4.sh, under which ratpoints-lean is compared with the outputs that it records.
FILTERS = {'grep found': lambda ls: [l for l in ls if 'found' in l],
           "grep 'Curve equation'": lambda ls: [l for l in ls if 'Curve equation' in l],
           'grep -c .': lambda ls: [str(sum(1 for l in ls if l))],
           "grep 'bits set per word' | sed 's/,.*//'":
               lambda ls: [l.split(',', 1)[0] for l in ls if 'bits set per word' in l],
           "grep 'iterations for'": lambda ls: [l for l in ls if 'iterations for' in l]}
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
# The high suite also runs these curves of testdata.h at this height, where the C program corrects
# its moduli during the run and the correction changes the survivors under -x and message 4 (about a
# second each): under -x without -A and with -A 1 and -A 2, the first also in a report with
# message 4, and in the threads suite with -t 4.
CORRECTION_CURVES = ['1 4 16 -3 -11 5 4', '9 -5 5 2 2 1 1']
CORRECTION_HEIGHT = 16383
# The threads suite: the first four of these curves at this height under -x, where the C program
# decides a correction of the moduli (on 1 2 3 4 5 6 7).
THREADS_HEIGHT = 30000
# The adapt suite: searches on which the C program corrects its moduli during the run
# (find_points.c:4115-4125, RP_ADAPT_LAG), as (the coefficient list, the height bound, further
# options), each run under -x without -A and with -A 0, 1 and 2: curves of testdata.h,
# testdata-many.h and testdata-degrees.h at 16383 and 50000 on which a correction takes effect (in
# the words shape at 50000 within the last blocks), and point-rich curves of test4.sh, also with
# tuning options. On 18 of the 23 command lines the correction changes the output under -x (with
# -A 0 or -A 2 against the default); the other 5 are controls.
ADAPT_RUNS = [
    ('9 -5 5 2 2 1 1', 16383, []), ('1 4 16 -3 -11 5 4', 16383, []),
    ('25 -118 -49 51 97 -3 1', 16383, []), ('25 4 -38 -46 -22 42 36', 16383, []),
    ('16 20 -131 -109 152 49 4', 16383, []), ('1 -26 87 83 -43 -117 64', 16383, []),
    ('4 -4 220 -445 152 97 1', 16383, []), ('1 -48 -190 -75 254 123 16', 16383, []),
    ('196 812 -297 -1649 627 324 36', 16383, []),
    ('1737139041 -1007386182 -1162123299 136567300 596158596 -79179328 256', 16383, []),
    ('-7 -5 -2 0 -3 -9 2', 50000, []), ('-9 5 -4 -5 4 -4 6', 50000, []),
    ('1 2 -7 -3 -9 -7 2', 50000, []), ('3 3 -8 7 2 6 4', 50000, []),
    ('-8399 -41778 -31133 34122 40972 9240 225', 50000, []),
    ('1737139041 -1007386182 -1162123299 136567300 596158596 -79179328 256', 50000, []),
    ('-1 0 7 -10 -1 10 -10 -8 6', 50000, []),
    ('10 10 5 -7 0 3 -2', 30000, []),
    ('10 10 5 -7 0 3 -2', 30000, ['-r', '0.5', '-R', '1', '-C', '0']),
    ('1 0 126 0 441', 40000, []), ('1 0 126 0 441', 40000, ['-r', '0.5', '-R', '0']),
    ('1 2 3 4 5 6 7', 30000, []), ('1 4 16 -3 -11 5 4', 16383, ['-W', '1e6', '-Q', '0.001']),
]
TIMEOUT = 600
# A search above --max-height is compared when it has a search region (intervals or a range of
# denominators) whose denominators, as the model sifts them, are at most
# BIG_DENOMINATORS, and whose numerators, an upper bound of the sum over these denominators, are at
# most BIG_NUMERATORS, under -1 only those up to the stop at the first point of the expected output,
# with BIG_PIECE more for the piece of bit arrays that holds it, which is sifted in full (the
# default array size 256 plus one bit array of rbaLength = 256 bits, at the largest stride 64):
# ratpoints-lean within BIG_TIMEOUT seconds, its address space capped at BIG_MEMORY bytes, and a
# run that does not end in time is a failure.
BIG_DENOMINATORS = 10 ** 5
BIG_NUMERATORS = 2 * 10 ** 10
BIG_PIECE = 257 * 256 * 64
BIG_TIMEOUT = 600
# The cap is on the address space, not on the memory: the Lean runtime reserves about 1 GiB of
# address space for each of its threads (some 3.4 * 10^9 bytes at the start) while it uses a few
# tens of MB, so that a cap near that would abort the program for reasons outside the model.
BIG_MEMORY = 12 * 10 ** 9
# The odd primes of the table of ratpoints (primes.h, Ratpoints.primeTable) up to 1021, over which
# the divisor set-up of the model factors the leading coefficient (Ratpoints.Setup.factorLcf), and
# the bound on the number of the squarefree divisors (Ratpoints.maxDivisors).
TABLE_PRIMES = [p for p in range(3, 1022, 2) if all(p % q for q in range(3, math.isqrt(p) + 1, 2))]
MAX_DIVISORS = 512
# The stop cases of the errors suite (difftest_cases.STOP_CASES), searches at a large height that
# both programs stop at a point at infinity before the sieve: ratpoints-lean must end within
# STOP_TIMEOUT seconds with its address space capped at STOP_MEMORY bytes.
STOP_TIMEOUT = 30
STOP_MEMORY = 12 * 10 ** 9  # the address space, as BIG_MEMORY
# The numerator words after which the C program may first correct its choice of the moduli
# (RP_ADAPT_WORDS, find_points.c:1354), and the bit arrays of the default build: RBA_LENGTH bits,
# RBA_PACK words each (correction_possible, which counts the runs where a correction may come).
ADAPT_WORDS = 10 ** 6
RBA_LENGTH = 256
RBA_PACK = 4
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
    and those of a search under -x, exactly against the C program on the same command line, and by
    the weaker check unless a format or a string is given or -v (`x_exact`), of these the number
    where the C program may correct its moduli during the run (`x_adapt`); the reports compared with
    message 4 (`msg4`); the outputs compared under -v, with the report of the library (`verbose`);
    the skipped runs by their reason; the failures; and the disagreements of the C program with the
    outputs that testbase4 records for its searches compared with the C program, which are no
    failures (`notes`)."""
    compared: int = 0
    in_order: int = 0
    x_exact: int = 0
    x_adapt: int = 0
    msg4: int = 0
    verbose: int = 0
    skipped: dict = field(default_factory=dict)
    failures: list = field(default_factory=list)
    notes: list = field(default_factory=list)

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
    of (index, word, argument or None) up to the first word that is no option of ratpoints (or an
    option whose argument is missing), and the index of that word (None if it reaches the end)."""
    words, i = [], 0
    while i < len(opts):
        o = as_bytes(opts[i]).decode('latin-1')
        if len(o) < 2 or o[0] != '-':
            return words, i
        if (o[1] in ARG_OPTS or o[1] in REGION_OPTS or o[1] == 'f' and o[2:3] in STRING_OPTS or
                o[1] == 'd' and o[2:3] in DEN_OPTS):
            if i + 1 >= len(opts):
                return words, i
            words.append((i, o, opts[i + 1]))
            i += 2
        elif o[1] == 'S':
            takes = i + 1 < len(opts) and not as_bytes(opts[i + 1]).startswith(b'-')
            words.append((i, o, opts[i + 1] if takes else None))
            i += 2 if takes else 1
        elif o[1] in FLAGS:
            words.append((i, o, None))
            i += 1
        else:
            return words, i
    return words, None


def as_long(arg):
    """The C long that the argument of an option gives, or None (for -n, -N, -A and the range of
    the denominators)."""
    try:
        return int(as_bytes(arg).decode('latin-1').strip())
    except ValueError:
        return None


@dataclass
class Settings:
    """The settings of a command line that decide how its output is compared: -q, -v (cancelled
    by -q), -x, -y, -z and -1, the last of each pair winning, whether a format or a string is given,
    the last values of -n, -N and -A, and the search region: the ends of the intervals of -l and -u
    in their order, as (letter, word), and the last values of -dl and -du."""
    quiet: bool = False
    verbose: bool = False
    x: bool = False
    y: bool = False
    z: bool = False
    one: bool = False
    strings: bool = False
    n: int | None = None
    N: int | None = None
    A: int | None = None
    ends: list = field(default_factory=list)
    dl: int | None = None
    du: int | None = None

    @property
    def plain(self):
        """Whether the output with -q is a list of points in the default format."""
        return not (self.x or self.y or self.strings)

    @property
    def region(self):
        """Whether the command line gives a search region: intervals or a bound of the
        denominators."""
        return bool(self.ends) or self.dl is not None or self.du is not None


def settings(opts):
    """The settings of the options `opts`, the words after the height, as far as ratpoints-lean
    reads them."""
    st = Settings()
    for _, o, a in option_words(opts)[0]:
        c = o[1]
        if c == 'q':
            st.quiet = True
        elif c == 'v':
            st.verbose = True
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
        elif c == 'n':
            st.n = as_long(a)
        elif c == 'N':
            st.N = as_long(a)
        elif c == 'A':
            st.A = as_long(a)
        elif c in 'lu':
            st.ends.append((c, as_bytes(a).decode('latin-1')))
        elif c == 'd':
            if o[2] == 'l':
                st.dl = as_long(a)
            else:
                st.du = as_long(a)
    st.verbose = st.verbose and not st.quiet
    return st


def end_value(word):
    """The value of an end of a search interval as a float, an infinity of the sign of the word for
    a number beyond the doubles (float() gives it for a decimal, float.fromhex raises OverflowError
    for a hexadecimal constant), for the estimate of the numerators of a search; None if it is not
    a number."""
    w = word.strip()
    try:
        return float.fromhex(w) if re.match(r'^[+-]?0[xX]', w) else float(w)
    except OverflowError:
        return -math.inf if w.startswith('-') else math.inf
    except ValueError:
        return None


def factor_lcf(w):
    """The primes of w >= 1 and the cofactor as the divisor set-up of the model finds them
    (Ratpoints.Setup.factorLcf): 2 divided off, then for the odd primes p of the table in turn,
    while the cofactor is not 1, a cofactor below p^2, which has no prime factor below p and so is
    a prime, taken as one (when it is a long) and leaving the cofactor 1, and otherwise p divided
    off when it divides; the factorization is complete exactly when the cofactor is 1."""
    ps = []
    if w % 2 == 0:
        ps.append(2)
        while w % 2 == 0:
            w //= 2
    for p in TABLE_PRIMES:
        if w == 1:
            break
        if w < p * p:
            if w < 2 ** 63:
                ps, w = ps + [w], 1
            break
        if w % p == 0:
            ps.append(p)
            while w % p == 0:
                w //= p
    return ps, w


def den_shape(c, hi):
    """The shape of the denominators that the model lists for the polynomial with the coefficient
    list c (constant term first, not reversed) and the largest denominator hi, as an upper bound on
    them: ('squares', None) for odd degree and |c_d| = 1; ('divisors', divs) for odd degree when
    factor_lcf factors |c_d| completely and fewer than MAX_DIVISORS of its squarefree divisors are
    at most hi (Ratpoints.Setup.setupUs1), divs those divisors; and ('all', None) otherwise, every
    denominator, which bounds the shape of the words for even degree too. All but the divisors are
    listed in increasing order."""
    d = max((i for i, ci in enumerate(c) if ci), default=0)
    lcf = abs(c[d])
    if d % 2 == 0 or lcf == 0:
        return 'all', None
    if lcf == 1:
        return 'squares', None
    ps, w = factor_lcf(lcf)
    if w != 1:
        return 'all', None
    divs = [1]
    for p in ps:
        divs += [s * p for s in divs if s <= hi // p][:MAX_DIVISORS - len(divs)]
        if len(divs) >= MAX_DIVISORS:
            return 'all', None
    return 'divisors', divs


def count_dens(shape, lo, hi):
    """The number of the denominators from lo to hi of the shape `shape` (den_shape)."""
    kind, divs = shape
    if hi < lo:
        return 0
    if kind == 'squares':
        return math.isqrt(hi) - math.isqrt(lo - 1)
    if kind == 'divisors':
        return sum(max(0, math.isqrt(hi // s) - math.isqrt((lo - 1) // s)) for s in divs)
    return hi - lo + 1


def denominators(c, lo, hi):
    """An upper bound on the number of denominators that the model lists for the search of the
    coefficient list c with the denominators from lo to hi (den_shape, count_dens), whether or not
    the polynomial is reversed: case 1 of the reversal makes an even degree odd, for which every
    denominator is counted; case 2 keeps an even degree; and case 3 makes |c_d| = 1, whose squares
    are among the denominators counted for the polynomial before the reversal."""
    return count_dens(den_shape(c, hi), lo, hi)


def first_point(text):
    """The first point (a : y : b) or pair (a : b) of an output, as (a, b), or None."""
    for l in point_lines(text):
        g = (POINT.match(l) or PAIR.match(l)).groups()
        return int(g[0]), int(g[-1])
    return None


def big_search(args, st, out):
    """Whether the search of the command line `args` with the settings `st`, above --max-height,
    is compared (None) or why it is skipped, for the expected output `out`: it must have a search
    region, and its denominators (denominators) and the numerators it sifts must be at most
    BIG_DENOMINATORS and BIG_NUMERATORS: at most the number of the denominators times
    min(2H + 1, hi W + k) for the largest denominator hi and the width W of the k intervals within
    [-H, H]; under -1, when the region suppresses the reversal, so that the points are those of the
    polynomial searched, for the first point (a : y : b) of `out`, where the search stops, none for
    a point at infinity, which comes before the sieve, and else at most the numerators of the
    denominators listed before b (all of them for the divisor shape), those of b up to a, and
    BIG_PIECE more."""
    H = height(as_bytes(args[1]).decode('latin-1')) or 0
    if not st.region:
        return 'height above the largest of the suite, without a search region'
    lo = max(1, st.dl if st.dl is not None else 1)
    hi = st.du if st.du is not None and 1 <= st.du <= H else H
    c = coefficients(args[0])
    shape = den_shape(c, hi)
    n = count_dens(shape, lo, hi)
    if n > BIG_DENOMINATORS:
        return f'more than {BIG_DENOMINATORS} denominators above the largest height of the suite'
    width, k, low = 0.0, 0, -math.inf
    for kind, word in st.ends:
        v = end_value(word)
        if v is None:
            return 'an end of a search interval that the harness cannot read'
        if kind == 'l':
            low = v
        else:
            width += max(0.0, min(v, H) - max(-math.inf if low is None else low, -H))
            k, low = k + 1, None
    if low is not None and st.ends:  # the last interval has no upper end
        width += max(0.0, H - max(low, -H))
        k += 1
    per = min(2 * H + 1, hi * width + k) if st.ends else 2 * H + 1
    numerators = n * per
    # a search region suppresses the reversal unless it is the whole box (find_points.c:4686)
    first = first_point(out) if st.one and (st.ends or lo > 1 or hi < H) else None
    if first is not None and first[1] == 0:
        numerators = 0
    elif first is not None:
        a, b = first
        before = n if shape[0] == 'divisors' else count_dens(shape, lo, b - 1)
        numerators = min(numerators, before * per + min(a + H + 1, per) + BIG_PIECE)
    if numerators > BIG_NUMERATORS:
        return f'more than {BIG_NUMERATORS} numerators above the largest height of the suite'
    return None


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


# The lines of message 4, on the moduli used, as test4.sh's m() finds them.
MODULI_LINES = re.compile('used for|further primes|primes used')


def report_text(cfg, text, lean=False):
    """A report as it is compared: the first line of the banner, which test4.sh's m() drops, left
    out, for ratpoints-lean (`lean`) after its banner is exchanged for that of the C program, the
    message on the moduli used (message 4) included."""
    if lean:
        text = text.replace(cfg.lean_banner, cfg.c_banner)
    return '\n'.join(l for l in text.split('\n') if not l.startswith('This is ratpoints-'))


def as_recorded_by_m(text):
    """An output as test4.sh's m() records it: without the first line of the banner and the lines
    of message 4, on the moduli used."""
    return '\n'.join(l for l in text.split('\n')
                     if not l.startswith('This is ratpoints-') and not MODULI_LINES.search(l))


def coefficients(arg):
    """The coefficient list of a command line that the C program accepted, constant term first."""
    return [int(w) for w in as_bytes(arg).decode('latin-1').split()]


def is_point(c, a, b):
    """Whether (a : b) is the x-coordinate of a point of y^2 = F(x, z) for the coefficient list c:
    F(a, b) a square, for the binary form of the even degree d + d % 2, d the degree of c."""
    d = max((i for i, ci in enumerate(c) if ci), default=0)
    v = sum(ci * a ** i * b ** (d + d % 2 - i) for i, ci in enumerate(c[:d + 1]))
    return v >= 0 and math.isqrt(v) ** 2 == v


def exact_region(st):
    """The search intervals of the command line with the settings `st` as main.c reads them, with
    their exact ends (difftest_cases.end_fraction), -inf for a missing first -l and +inf for a
    missing last -u: a list of pairs, empty for none."""
    ivs, low = [], -math.inf
    for kind, word in st.ends:
        if kind == 'l':
            low = difftest_cases.end_fraction(word)
        else:
            ivs.append((low, difftest_cases.end_fraction(word)))
            low = None
    if low is not None and st.ends:
        ivs.append((low, math.inf))
    return ivs


def in_region(x, ivs):
    """Whether x lies in one of the increasing, disjoint closed intervals `ivs`, as in_region of
    main.c decides it: the first interval that does not end below x, found by a binary search, must
    hold it."""
    lo, hi = 0, len(ivs)
    while lo < hi:
        mid = (lo + hi) // 2
        if ivs[mid][1] < x:
            lo = mid + 1
        else:
            hi = mid
    return lo < len(ivs) and ivs[lo][0] <= x


def weak_agrees(lean_text, exp_text, args, st):
    """The weaker check of an output under -x, whose lines (x : z) are the survivors of the sieve,
    which depend on the moduli and on the search region: every such line a normalized coprime pair
    in the range of the height in both outputs and, but for (1 : 0), with z in the range of the
    denominators (normalized as main.c and the library normalize it) and x / z in the exact search
    region of the command line (exact_region, in_region), as process of main.c passes over every
    other pair, none repeated; the pairs that are points the same and in the same order, and the
    pairs common to both outputs in the same order; under -1, when one of the two lines (if any) is
    a point, one line in each output, the same if both are points (a point survives every sieve),
    and else at most one line in each; the pairs in one block in each output, at the same place
    among the other lines when both have pairs; the other lines equal, the count lines among them
    with their numbers left out, and each count that of the pairs printed (unless -z)."""
    c, H = coefficients(args[0]), height(as_bytes(args[1]).decode('latin-1'))
    lo = max(1, st.dl if st.dl is not None else 1)
    hi = st.du if st.du is not None and 1 <= st.du <= H else H
    ivs = exact_region(st)

    def in_search(a, b):
        return (a, b) == (1, 0) or (b > 0 and math.gcd(a, b) == 1 and lo <= b <= hi and
                                    (not ivs or in_region(Fraction(a, b), ivs)))

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
    sl, se = set(lp), set(ep)
    valid = (all(in_search(a, b) and abs(a) <= H and b <= H for a, b in lp + ep) and
             len(sl) == len(lp) and len(se) == len(ep))
    blocks = lk and ek and (lb == eb or lb is None or eb is None)
    common = [p for p in lp if p in se] == [p for p in ep if p in sl]
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


def lean_or_timeout(cfg, tally, label, args, big):
    """The run of ratpoints-lean on `args`, for a search above --max-height (`big`) within
    BIG_TIMEOUT seconds and with its address space capped at BIG_MEMORY bytes; None, with a
    failure recorded, when it does not end in time."""
    if not big:
        return run_lean(cfg, args)
    try:
        return run_lean(cfg, args, BIG_TIMEOUT, BIG_MEMORY)
    except subprocess.TimeoutExpired:
        tally.compared += 1
        tally.failures.append(f'{label}: ratpoints-lean did not end within {BIG_TIMEOUT} s')
        return None


def check(cfg, tally, label, args, expected, mode, st=None, lean=None, big=False):
    """Run ratpoints-lean on `args` (unless its run `lean` is given; for a search above
    --max-height, `big`, with a timeout and a cap on the memory) and compare it with `expected`
    (see verdict)."""
    lean = lean or lean_or_timeout(cfg, tally, label, args, big)
    if lean is None:
        return
    ok = verdict(cfg, lean, expected, mode, args, st)
    tally.compared += 1
    tally.in_order += mode in ('points', 'report', 'exact') and expected[1] == 0
    tally.msg4 += mode == 'report' and MODULI_LINES.search(expected[0]) is not None
    tally.verbose += st is not None and st.verbose and not mode.startswith('filter:')
    if not ok:
        tally.failures.append(failure_text(label, expected, lean))
    if cfg.verbose:
        print(('ok   ' if ok else 'FAIL ') + label)


def mode_of(st, code):
    """How an output of ratpoints-lean is compared with an output of the C program that ends with
    the exit code `code`, for the settings `st` of the command line: a failure before the search
    exactly; error 8 exactly with -q and as a report without; a search without -q as a report; with
    -q as a list of points in the default format, else exactly."""
    if code not in (0, 8):
        return 'exact'
    if code == 8:
        return 'exact' if st.quiet else 'report'
    if not st.quiet:
        return 'report'
    return 'points' if st.plain else 'exact'


def above(cfg, args):
    """Whether the command line `args` searches above --max-height."""
    return (height(as_bytes(args[1]).decode('latin-1')) or 0) > cfg.max_height


def skips_height(cfg, args, out, code, st):
    """Why the comparison with the C program, which ended with the output `out` and the exit code
    `code` on the command line `args` with the settings `st`, is skipped, or None: a search above
    --max-height with a search region, or without one on which the C program prints something,
    unless big_search admits it. A search without a search region on which the C program prints
    nothing (an exit before the sieve) is quick for both and is compared; one with a search region
    can sift many denominators and find nothing."""
    if code == 0 and above(cfg, args) and (out or st.region):
        return big_search(args, st, out)
    return None


def live_mode(mode):
    """The mode of a comparison with a live output of the C program: a list of points exactly, also
    its final newline (a recorded output of test4.sh or rptest may lack it)."""
    return 'exact' if mode == 'points' else mode


def correction_possible(args, st):
    """Whether the C program may correct its choice of the moduli during the run on the command line
    `args` with the settings `st` (adapt_primes), for the count of such runs: neither -n nor -N
    gives a value >= 0 and -A does not give 0 (find_points.c:2580), and the run can pass
    RP_ADAPT_WORDS = 10^6 numerator words, by an upper bound: the denominators of the range times
    the number of search intervals (at least one) times the words of the bit arrays of the
    numerators of the height bound, two bit arrays more per interval for the rounding."""
    if any(v is not None and v >= 0 for v in (st.n, st.N)) or st.A == 0:
        return False
    H = height(as_bytes(args[1]).decode('latin-1')) or 0
    lo = max(1, st.dl if st.dl is not None else 1)
    hi = st.du if st.du is not None and 1 <= st.du <= H else H
    nint = max(1, sum(1 for kind, _ in st.ends if kind == 'u'))
    return max(0, hi - lo + 1) * nint * ((2 * H + 1) // RBA_LENGTH + 2) * RBA_PACK >= ADAPT_WORDS


def check_x(cfg, tally, label, args, st, expected, big=False):
    """Compare ratpoints-lean with the C program on a search under -x (no exact check) on the
    command line `args` with the settings `st`, whose lines (x : z) are the survivors of the sieve,
    which depend on the moduli and on the search region, and whose output of the C program is
    `expected`: exactly, since the model chooses its moduli from the curve and corrects them during
    the run as the C program does, counting the runs where the C program may correct them
    (correction_possible); and, without a format or a string, whose lines it could not read, and
    without -v, whose report of the library comes between the pairs, also by the weaker check
    against `expected` (weak_agrees)."""
    lean = lean_or_timeout(cfg, tally, label, args, big)
    if lean is None:
        return
    fails = []
    if not verdict(cfg, lean, expected, live_mode(mode_of(st, expected[1])), args, st):
        fails.append(failure_text(f'{label} (exactly)', expected, lean))
    if not st.strings and not st.verbose and not verdict(cfg, lean, expected, 'weak', args, st):
        fails.append(failure_text(f'{label} (the weaker check)', expected, lean))
    tally.compared += 1
    tally.x_exact += 1
    tally.x_adapt += correction_possible(args, st)
    tally.msg4 += not st.quiet and MODULI_LINES.search(expected[0]) is not None
    tally.verbose += st.verbose
    if fails:
        tally.failures.append('; '.join(fails))
    if cfg.verbose:
        print(('FAIL ' if fails else 'ok   ') + label)


def against_c(cfg, tally, label, args):
    """Compare ratpoints-lean with the C program on the command line `args`, a search under -x by
    check_x, and a search above --max-height that big_search admits with a timeout and a cap on
    the memory."""
    st = settings(args[2:])
    out, code = run(cfg.c, args)
    skip = skips_height(cfg, args, out, code, st)
    big = code == 0 and above(cfg, args)
    if skip:
        tally.skip(skip)
    elif st.x and code == 0:
        check_x(cfg, tally, label, args, st, (out, code), big)
    else:
        check(cfg, tally, label, args, (out, code), live_mode(mode_of(st, code)), st, big=big)


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


def compare_search(cfg, tally, label, args, text, st, big=False):
    """Compare ratpoints-lean with the output `text` of a search that testbase4 records for the
    command line `args` with the settings `st` (above --max-height, `big`, with a timeout and a cap
    on the memory): under -v with the C program, whose report of the library test4.sh's v()
    records without the lines that depend on the build; under -x by check_x with the output of the C program on `args`, and without -q, a
    report, with that output too (whose message 4 test4.sh's m() drops), a disagreement of that
    output with `text` noted apart from the failures (the lines that m() drops dropped from both);
    else with `text`."""
    if st.verbose:
        against_c(cfg, tally, label, args)
    elif st.x or not st.quiet:
        out, code = run(cfg.c, args)
        if code != 0 or as_recorded_by_m(out) != as_recorded_by_m(text):
            tally.notes.append(f'{label}: the C program gives exit {code} and {out[:500]!r}, its '
                               f'record {text[:500]!r}')
        if st.x:
            check_x(cfg, tally, label, args, st, (out, code), big)
        else:
            check(cfg, tally, label, args, (out, code), 'report', st, big=big)
    else:
        check(cfg, tally, label, args, (text, 0), mode_of(st, 0), st, big=big)


def suite_test4(cfg, tally, window=None):
    """The invocations of test4.sh, a search with a height bound above --max-height skipped unless
    big_search admits it; with `window = (low, high)`, only the searches with a height bound in
    (low, high] that big_search does not admit, the rest being left to the plain call."""
    for r in split_test4(git_show(cfg.repo, cfg.commit, 'testbase4')):
        label = f'testbase4:{r.line} {r.args}'
        out, code = r.out, None
        if out and re.fullmatch(r'exit \d+', out[-1]):  # recorded by e()
            code, out = int(out[-1].split()[1]), out[:-1]
        text = '\n'.join(out) + ('' if r.nonl else '\n') if out else ''
        if code == 0:  # e() keeps one newline at the end, also of an empty output
            text = text.rstrip('\n') + '\n' if text.strip('\n') else ''
        st = settings(r.args[2:])
        searches = (r.filt is None and not code and 'Polynomial is not square-free.' not in text)
        big = searches and len(r.args) >= 2 and above(cfg, r.args)
        skip = big and big_search(r.args, st, text)
        if window is not None:
            if (searches and window[0] < (height(r.args[1]) or 0) <= window[1] and
                    (skip or not big)):
                compare_search(cfg, tally, label, r.args, text, st)
            continue
        if r.filt is not None:
            if r.filt not in FILTERS:
                tally.skip('output filtered')
            else:
                check(cfg, tally, label, r.args, (text, 0), 'filter:' + r.filt, st)
                against_c(cfg, tally, f'{label} (the whole output)', r.args)
        elif code == 8 or 'Polynomial is not square-free.' in text:
            # error 8, recorded by e() with -q, and without -q at the end of a report
            if st.verbose:
                against_c(cfg, tally, label, r.args)
            else:
                check(cfg, tally, label, r.args, (text, 8),
                      'e' if code else 'exact' if st.quiet else 'report', st)
        elif code:
            check(cfg, tally, label, r.args, (text, code), 'e')
        elif skip:
            tally.skip(skip)
        else:
            compare_search(cfg, tally, label, r.args, text, st, big)


def suite_test3(cfg, tally):
    """The invocations of test3.sh against the C program; one whose output test3.sh filters (lines
    of the report, of the report of the library under -v among them) with its whole output, that of
    the command before the filter, its redirections dropped."""
    script = git_show(cfg.repo, cfg.commit, 'test3.sh')
    for no, line in enumerate(script.split('\n'), 1):
        if not line.startswith('rp '):
            continue
        cmd = line.split('|', 1)[0]
        args = [w for w in shlex.split(cmd)[1:] if not re.fullmatch(r'\d*>&\d+', w)]
        against_c(cfg, tally, f'test3.sh:{no} {args}' + (' (unfiltered)' if '|' in line else ''),
                  args)


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
    """The point-rich curves of the params suite at the heights HIGH_HEIGHTS, with -q; and the runs
    where the C program corrects its moduli with an effect on the output (CORRECTION_CURVES at
    CORRECTION_HEIGHT), under -x without -A and with -A 1 and -A 2, and a report with message 4
    (-z), against the C program."""
    for c, _ in PARAM_CURVES[:4]:
        for h in HIGH_HEIGHTS:
            args = [c, str(h), '-q']
            against_c(cfg, tally, f'high {args}', args)
    for c in CORRECTION_CURVES:
        for a in ([], ['-A', '1'], ['-A', '2']):
            args = [c, str(CORRECTION_HEIGHT), '-q', '-x', *a]
            against_c(cfg, tally, f'high {args}', args)
    args = [CORRECTION_CURVES[0], str(CORRECTION_HEIGHT), '-z']
    against_c(cfg, tally, f'high {args}', args)


def suite_regions(cfg, tally):
    """Searches with random search regions (difftest_cases.random_region_line), against the C
    program."""
    rng = random.Random(cfg.seed)
    for i in range(cfg.regions):
        args = difftest_cases.random_region_line(rng)
        against_c(cfg, tally, f'regions {i} {args}', args)


def suite_depths(cfg, tally):
    """Searches with random depths of the Sturm step, -S 0 to -S 60 and -s
    (difftest_cases.random_depth_line), against the C program."""
    rng = random.Random(cfg.seed)
    for i in range(cfg.depths):
        args = difftest_cases.random_depth_line(rng)
        against_c(cfg, tally, f'depths {i} {args}', args)


def suite_verbose(cfg, tally):
    """Searches under -v, with the report of the library (difftest_cases.random_verbose_line),
    against the C program."""
    rng = random.Random(cfg.seed)
    for i in range(cfg.verbose_runs):
        args = difftest_cases.random_verbose_line(rng)
        against_c(cfg, tally, f'verbose {i} {args}', args)


def suite_test4high(cfg, tally):
    suite_test4(cfg, tally, (cfg.max_height, cfg.test4_max_height))


def suite_tuning(cfg, tally):
    """Searches with random values of the tuning options (difftest_cases.random_tuning_line),
    against the C program."""
    rng = random.Random(cfg.seed)
    for i in range(cfg.tuning):
        args = difftest_cases.random_tuning_line(rng)
        against_c(cfg, tally, f'tuning {i} {args}', args)


def suite_threads(cfg, tally):
    """The C program sieving with a pool of threads, -t 4 and -t 7 (fixed counts, so that the suite
    tests the same on every machine; -t 0 is an errors case), against ratpoints-lean, which reads -t
    and sieves on one thread: random polynomials at small heights, at times under -x, the point-rich
    curves of the high suite at the height THREADS_HEIGHT under -x, and the first of
    CORRECTION_CURVES under -x, where a correction of the moduli changes the survivors."""
    rng = random.Random(cfg.seed)
    for i in range(cfg.threads):
        c = ' '.join(str(rng.randint(-10, 10)) for _ in range(rng.randint(2, 9)))
        args = [c, str(rng.choice([20, 100, 500, 2000])), '-q', *(['-x'] if rng.random() < 0.5
                                                                  else [])]
        for t in ('4', '7'):
            against_c(cfg, tally, f'threads {i} {args + ["-t", t]}', args + ['-t', t])
    for c, _ in PARAM_CURVES[:4]:
        args = [c, str(THREADS_HEIGHT), '-q', '-x', '-t', '4']
        against_c(cfg, tally, f'threads {args}', args)
    args = [CORRECTION_CURVES[0], str(CORRECTION_HEIGHT), '-q', '-x', '-t', '4']
    against_c(cfg, tally, f'threads {args}', args)


def suite_adapt(cfg, tally):
    """Searches where the C program corrects its moduli during the run (adapt_primes), under -x with
    -A 0, 1 and 2 and without -A, at times with tuning options (ADAPT_RUNS), against the C
    program, with a timeout and a cap on the memory, also above --max-height."""
    for c, h, extra in ADAPT_RUNS:
        for a in ([], ['-A', '0'], ['-A', '1'], ['-A', '2']):
            args = [c, str(h), '-q', '-x', *a, *extra]
            out, code = run(cfg.c, args)
            check_x(cfg, tally, f'adapt {args}', args, settings(args[2:]), (out, code), big=True)


def suite_fuzz(cfg, tally):
    rng = random.Random(cfg.seed)
    for i in range(cfg.fuzz):
        for j, args in enumerate(difftest_cases.random_command_lines(rng)):
            against_c(cfg, tally, f'fuzz {i}.{j} {args}', args)


SUITES = {'test4': suite_test4, 'test3': suite_test3, 'rptest': suite_rptest,
          'random': suite_random, 'outputs': suite_outputs, 'errors': suite_errors,
          'fuzz': suite_fuzz, 'params': suite_params, 'high': suite_high,
          'regions': suite_regions, 'depths': suite_depths, 'tuning': suite_tuning,
          'threads': suite_threads, 'verbose': suite_verbose, 'test4high': suite_test4high,
          'adapt': suite_adapt}
# The suites that run by default (in CI): all but test4high and adapt.
DEFAULT_SUITES = ['test4', 'test3', 'rptest', 'random', 'outputs', 'errors', 'fuzz', 'params',
                  'high', 'regions', 'depths', 'tuning', 'threads', 'verbose']


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
    ap.add_argument('--regions', type=int, default=400)
    ap.add_argument('--depths', type=int, default=300)
    ap.add_argument('--tuning', type=int, default=300)
    ap.add_argument('--threads', type=int, default=100)
    ap.add_argument('--verbose-runs', type=int, default=300)
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
    if (Path(cfg.c).resolve().parent / 'tuning.mk').exists():
        print(f'ERROR {cfg.c} is built with a tuning.mk, whose tuning of the choice of the moduli '
              f'the model does not have (it models the default build)')
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
        if tally.x_exact:
            parts.append(f'-x: {tally.x_exact} exactly ({tally.x_adapt} of them where the C '
                         f'program may correct its moduli)')
        if tally.msg4:
            parts.append(f'{tally.msg4} reports with message 4')
        if tally.verbose:
            parts.append(f'{tally.verbose} under -v with the report of the library')
        if tally.notes:
            parts.append(f'{len(tally.notes)} where the C program disagrees with its record')
        detail = f' ({"; ".join(parts)})' if parts else ''
        print(f'{name}: {tally.compared} compared{detail}, {len(tally.failures)} failed'
              + (f'; skipped: {skipped}' if skipped else ''))
        for f in tally.failures:
            print(f'  FAIL {f}')
        for n in tally.notes:
            print(f'  NOTE {n}')
        failed += len(tally.failures)
    return 1 if failed else 0


if __name__ == '__main__':
    sys.exit(main())

#!/usr/bin/env python3
"""Tests of the fast ratpoints-lean against ratpoints at the pinned commit.

usage: scripts/fasttest.py --c PATH --repo DIR [--lean PATH] [--height H] [--ranges N]
                           [--tunings N]

Runs ratpoints-lean (the fast search, Ratpoints.FastMask.fastPoints) and the C program ratpoints on
the curves of the three test suites of ratpoints (testdata.h, testdata-many.h and
testdata-degrees.h in DIR) at the height bound H (default 16383, that of rptest), and on N curves
of testdata.h (default 200) with random bounds -dl and -du of the denominators, and on N curves
of the three suites (default 200) with random values of the tuning options of ratpoints-lean
(-tG -tL -tM -tF -tS -tK, which ratpoints does not get; at a quarter of the height where the values
weaken the first stage of the sieve, which makes a run slow), and compares the points as sets:
ratpoints-lean lists them in an order of its own. Prints the number of runs, the mismatches and
the total times, and exits 1 if a run differs or fails.

  --c PATH       the C program ratpoints
  --repo DIR     the ratpoints repository with the test suites
  --lean PATH    the executable (default: .lake/build/bin/ratpoints-lean)
  --height H     the height bound (default 16383)
  --ranges N     the number of runs with random bounds of the denominators (default 200)
  --tunings N    the number of runs with random tuning options (default 200)
"""
import argparse
import random
import re
import resource
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from difftest import curves  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
MEMORY = 4 << 30
POINT = re.compile(r'\(-?\d+ : -?\d+ : -?\d+\)')
TIMEOUT = 600


def cap():
    resource.setrlimit(resource.RLIMIT_AS, (MEMORY, MEMORY))


# The values that the runs with random tuning options choose from, per option: steps that are not
# powers of 2 or share a factor with a modulus, chunks shorter and longer than the classes, families
# of one modulus and of many, few and many moduli, a shallow and a deep Sturm step, and every
# split of the families between the two stages.
TUNINGS = {
    '-tG': [1, 2, 3, 4, 5, 6, 8, 12, 16, 32, 48],
    '-tL': [64, 100, 500, 1000, 4096, 16384, 100000],
    '-tM': [1, 5, 15, 100, 1500, 5000],
    '-tF': [1, 4, 16, 100],
    '-tS': [1, 5, 10, 20],
    '-tK': [1, 2, 3, 5, 100],
}
# The values that weaken the first stage: families of one modulus, and few families.
WEAK = {'-tM': [1, 5, 15], '-tK': [1, 2, 3, 5]}


def tuning(rng):
    """Random tuning options, each option with probability 1/2 and its value from `TUNINGS`, and
    whether one of the values weakens the first stage."""
    opts = []
    weak = False
    for o, values in TUNINGS.items():
        if rng.random() < 0.5:
            v = rng.choice(values)
            opts += [o, str(v)]
            weak = weak or v in WEAK.get(o, [])
    return opts, weak


def points(cmd):
    """The time, exit code and sorted point lines of the command `cmd`."""
    start = time.perf_counter()
    r = subprocess.run(cmd, capture_output=True, text=True, preexec_fn=cap, timeout=TIMEOUT)
    lines = sorted(line for line in r.stdout.splitlines() if POINT.fullmatch(line))
    return time.perf_counter() - start, r.returncode, lines


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--c', required=True)
    ap.add_argument('--repo', required=True)
    ap.add_argument('--lean', default=str(ROOT / '.lake/build/bin/ratpoints-lean'))
    ap.add_argument('--height', type=int, default=16383)
    ap.add_argument('--ranges', type=int, default=200)
    ap.add_argument('--tunings', type=int, default=200)
    a = ap.parse_args()
    rng = random.Random(1)
    failed = 0
    runs = []
    for name in ['testdata.h', 'testdata-many.h', 'testdata-degrees.h']:
        for c in curves((Path(a.repo) / name).read_text()):
            runs.append((name, ' '.join(map(str, c)), a.height, [], []))
    suites = list(runs)
    first = [r for r in runs if r[0] == 'testdata.h'][:a.ranges]
    for name, coeffs, h, _, _ in first:
        lo = rng.randint(-5, h // 2)
        hi = rng.choice([0, rng.randint(1, h)])
        runs.append((name + ' with -dl/-du', coeffs, h, ['-dl', str(lo), '-du', str(hi)], []))
    for name, coeffs, h, _, _ in rng.sample(suites, min(a.tunings, len(suites))):
        tune, weak = tuning(rng)
        runs.append(('tuning options', coeffs, max(1, h // 4) if weak else h, [], tune))
    totals = {}
    for name, coeffs, h, opts, tune in runs:
        tc, ec, oc = points([a.c, coeffs, str(h), '-q'] + opts)
        tl, el, ol = points([a.lean, coeffs, str(h)] + opts + tune)
        n, bad, sc, sl = totals.get(name, (0, 0, 0.0, 0.0))
        ok = ec == 0 and el == 0 and oc == ol
        if not ok:
            failed += 1
            print(f'MISMATCH {name}: {coeffs!r} {h} {" ".join(opts + tune)}', flush=True)
        totals[name] = (n + 1, bad + (not ok), sc + tc, sl + tl)
    for name, (n, bad, sc, sl) in totals.items():
        print(f'{name}: {n} runs, {bad} mismatches, C {sc:.1f} s, Lean {sl:.1f} s')
    return 1 if failed else 0


if __name__ == '__main__':
    sys.exit(main())

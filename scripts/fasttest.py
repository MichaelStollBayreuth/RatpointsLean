#!/usr/bin/env python3
"""Tests of the fast ratpoints-lean against ratpoints at the pinned commit.

usage: scripts/fasttest.py --c PATH --repo DIR [--lean PATH] [--height H] [--ranges N]

Runs ratpoints-lean (the fast search, Ratpoints.Fast.fastPoints) and the C program ratpoints on
the curves of the three test suites of ratpoints (testdata.h, testdata-many.h and
testdata-degrees.h in DIR) at the height bound H (default 16383, that of rptest), and on N curves
of testdata.h (default 200) with random bounds -dl and -du of the denominators, and compares the
points as sets: ratpoints-lean lists them in an order of its own. Prints the number of runs, the
mismatches and the total times, and exits 1 if a run differs or fails.

  --c PATH       the C program ratpoints
  --repo DIR     the ratpoints repository with the test suites
  --lean PATH    the executable (default: .lake/build/bin/ratpoints-lean)
  --height H     the height bound (default 16383)
  --ranges N     the number of runs with random bounds of the denominators (default 200)
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
    a = ap.parse_args()
    rng = random.Random(1)
    failed = 0
    runs = []
    for name in ['testdata.h', 'testdata-many.h', 'testdata-degrees.h']:
        for c in curves((Path(a.repo) / name).read_text()):
            runs.append((name, ' '.join(map(str, c)), []))
    first = [r for r in runs if r[0] == 'testdata.h'][:a.ranges]
    for name, coeffs, _ in first:
        lo = rng.randint(-5, a.height // 2)
        hi = rng.choice([0, rng.randint(1, a.height)])
        runs.append((name + ' with -dl/-du', coeffs, ['-dl', str(lo), '-du', str(hi)]))
    totals = {}
    for name, coeffs, opts in runs:
        tc, ec, oc = points([a.c, coeffs, str(a.height), '-q'] + opts)
        tl, el, ol = points([a.lean, coeffs, str(a.height)] + opts)
        n, bad, sc, sl = totals.get(name, (0, 0, 0.0, 0.0))
        ok = ec == 0 and el == 0 and oc == ol
        if not ok:
            failed += 1
            print(f'MISMATCH {name}: {coeffs!r} {a.height} {" ".join(opts)}', flush=True)
        totals[name] = (n + 1, bad + (not ok), sc + tc, sl + tl)
    for name, (n, bad, sc, sl) in totals.items():
        print(f'{name}: {n} runs, {bad} mismatches, C {sc:.1f} s, Lean {sl:.1f} s')
    return 1 if failed else 0


if __name__ == '__main__':
    sys.exit(main())

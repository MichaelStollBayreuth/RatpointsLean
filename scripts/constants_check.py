#!/usr/bin/env python3
"""Build copies of RatpointsLean with other values of the compile-time constants of the model.

No proof of the project may depend on the values of the compile-time constants of the model, the
definitions `maxDegree`, `maxBitsInPrime`, `defaultNumPrimes`, `defaultMaxForbidden`, ... of
`Ratpoints/Model/Constants.lean` (`numPrimes` is derived from `maxBitsInPrime` and the table
`primeTable`, which stays as it is, `maxArraySize` from `chunk`, and `maxPrimeEven` and `modWords`
from `maxBitsInPrime`), beyond the facts that this file decides. This script checks that: it
builds copies of the committed project with other values of the constants and reports for each
copy whether the library `Ratpoints` (the model, the specification and all the proofs) still
builds. It builds the project once for each variant, one after the other, so it runs on demand
and not in CI.

Usage:

    python3 scripts/constants_check.py --workdir DIR [--repo DIR]
        [--variant NAME:const=value,...]... [--keep] [--prepare-only] [--lake PATH]
        [--timeout SECONDS]

    --workdir DIR      where the copies and the logs go (required): a folder outside the
                       repository, or one inside its folder tmp/, which git ignores; never
                       elsewhere inside the repository
    --repo DIR         the repository (default: the one this script lies in, as scripts/), only
                       read
    --variant SPEC     NAME:const=value,const=value,...; may be repeated, and replaces the
                       built-in list VARIANTS below, which runs when no --variant is given
    --keep             keep the copies (WORKDIR/NAME); the logs (WORKDIR/logs) always stay
    --prepare-only     stop each variant before its first lake command and keep the copy
    --lake PATH        the lake to run (default: the toolchain's own, run from the elan
                       toolchains folder without the elan proxy, else `lake` on the PATH)
    --timeout SECONDS  stop a build that takes longer (default 7200)

To add a variant for good, add an entry to VARIANTS: a name and a dict from constant names to
values. A constant that a variant names must be a definition `def <name> : Nat := <value>` (or
`: Int`, `: Bool`, `: Float`, `: Option Nat`), on one line, of Constants.lean at HEAD; otherwise
the script stops before it copies anything. The values are integers, natural numbers for a `Nat`,
Python's `True` and `False` for a `Bool`, written `true` and `false` in Lean (and in a --variant),
Python floats for a `Float`, and `Opt(None)` or `Opt(n)` for an `Option Nat` (`none` and `some n`
in Lean; a --variant cannot set these).

What it does for each variant, one after the other (never two builds at a time):

1. It copies the repository's HEAD (`git archive HEAD | tar -x`) into WORKDIR/NAME, fresh each
   run. Only committed work is checked: the working tree of the repository plays no part.
2. It lets the copy use the repository's built dependencies without rebuilding them: the copy's
   `.lake/packages` is a symlink to REPO/.lake/packages. Before any lake command it checks that
   every package of the copy's manifest sits there at the manifest's revision (else lake would
   check out another revision, or even delete and clone the package, inside the repository) and
   that every `[[require]]` of the lakefile is in the manifest (else lake would clone a package
   there). Then `lake build --no-build Mathlib` in the copy must succeed (exit status 0, which
   `--no-build` turns into 3 when a target is out of date, and no `error:` line): Mathlib and its
   dependencies must be up to date, or the variant is aborted, since a rebuild of Mathlib would
   write into the repository's packages and take hours.
3. It sets the variant's values in the copy's Ratpoints/Model/Constants.lean, asserting that each
   `def <name> : Nat := <value>` (or `: Int`, `: Bool`) it replaces occurs exactly once.
4. It removes the `#guard` commands from the copy's Ratpoints/**/*.lean, the examples of the model
   that test the default values against the C program on purpose and are not proofs, and reports
   how many per file. A command is removed from a line that begins with `#guard` followed by white
   space or the end of the line (so never `#guard_msgs`, which the proofs use for their axiom
   guards), outside block comments, up to the next blank line or the next line that starts at
   column 0 (a new command or comment); an `open ... in` or `set_option ... in` line right above
   it goes with it.
5. It builds the library: `LEAN_NUM_THREADS=2 lake build Ratpoints` in the copy, with the output
   in WORKDIR/logs/NAME-build.log, and decides success by the log alone: `Build completed
   successfully` and no line beginning with `error:` (never by an exit status).
6. It checks that nothing under REPO/.lake/packages was modified while the variant ran and that
   the log shows no job built outside the project; a change is reported and makes the exit
   status 1.

At the end it prints one line per variant: OK or FAIL, the times and the log, and for a failure
the first errors with their file, their line (and the line at HEAD where guards were removed above
it) and the declaration they are in. Without --keep each copy is deleted after its variant.

Exit status: 0 if every variant builds, 1 if one does not, 2 for an error in the arguments or the
setup. The script needs only the Python standard library (3.11 or later, for tomllib).
"""

import argparse
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import time
import tomllib
from pathlib import Path

DEFAULT_REPO = str(Path(__file__).resolve().parent.parent)
CONSTANTS_FILE = 'Ratpoints/Model/Constants.lean'
GUARD_DIR = 'Ratpoints'
LIBRARY = 'Ratpoints'
MAX_ERRORS = 5

# The built-in variants: a name and the values of the constants it changes. The constants keep
# the facts that Constants.lean checks by `decide`: `rbaPack`, `chunk` and `defaultArraySize` stay
# positive, and `chunk` at most `2 ^ 20`, so that the derived `maxArraySize = 2 ^ 20 / chunk *
# chunk` is positive, `maxBitsInPrime` at most 10, `mulModLimit` below `2 ^ 32`, `stage3Limit` at
# most `2 ^ 32`, `rbaLength = 2 ^ rbaShift` with `rbaShift < 32`, `2 rowBias - 1 <= mulModLimit`
# (so `rowBias = 0` where `mulModLimit = 0`) and `numStrides >= 1` (`numStrides = 8` reads the
# mask table beyond its seven entries, as the C code would). A new constant joins both variants
# A and B; a Boolean constant takes both values among the variants. Derived
# constants (`numPrimes`, `maxPrimeEven`, `modWords`, `maxArraySize`, ...) are not set: they
# follow the others. The chunk takes the unchunked first stage in A (1) and B (17, above 16, with
# the copies at the end of the rows that the C code makes for any chunk), and the chunked first
# stage in the variants C2, C3, C5 and C12, which change it alone: C2 runs none of the legs over
# the tail that the conditional compilation guards (`chunk > 2`, `> 4`, `> 8`), C3 the first,
# C5 the first two, C12 all three, and 3, 5 and 12 are not powers of 2. A and B change `rbaPack`
# only with chunks outside 2 to 16, so the variants P8, P2 and P1C5 pair the chunked first stage
# with the other widths of the bit arrays of the C builds, each with the `rbaShift` of its
# `rbaPack` (`rbaLength = 64 rbaPack = 2 ^ rbaShift`): P8 the default of USE_AVX512 (`RBA_PACK` 8)
# with the chunk 16, P2 that of USE_AVX128 and USE_SSE (`RBA_PACK` 2) with the chunk 16, and P1C5
# the 64-bit build (`RBA_PACK` 1) with a chunk given by `-DRATPOINTS_CHUNK`, here 5.
class Opt:
    """A value of a constant of type `Option Nat`: `Opt(None)` for `none`, `Opt(n)` for `some n`;
    for `blockLen` never `Opt(0)`, which no build can set (the C code divides by RP_BLOCK_LEN) and
    for which the decided fact `Ratpoints.blockLen_pos` fails."""
    def __init__(self, n):
        self.n = n


VARIANTS = {
    'A': {'maxDegree': 30, 'maxBitsInPrime': 5, 'defaultNumPrimes': 7, 'defaultMaxForbidden': 0,
          'rbaPack': 1, 'chunk': 1, 'defaultArraySize': 3, 'defaultSturm': -1,
          'veryBig': 0, 'maxDivisors': 2, 'jacobiPrimes': 0, 'jacobiTable': 0,
          'mulModLimit': 0, 'stage3Limit': 0, 'useLongInPhase2': True,
          'sp2Extra': 0, 'rowBias': 0, 'numStrides': 1, 'rbaShift': 6,
          'survivorsPerWord': 0.5, 'sp2U0': 0.0, 'sp3PerSurvivor': 0.0, 'sp3PerDenom': 1.0,
          'sp3Coprime': 0.0, 'costTable': 0.0, 'compositeMax': 0, 'costBp': 0.0, 'costSetup': 1e9,
          'costCall': 0.0, 'costLine': 0.0, 'costPhase2': 1.0, 'costSurvivor': 0.0,
          'costCheck': 0.0, 'checkStep': 0.0, 'checkLimb': 0.0, 'checkCall': 0.0,
          'checkRoot': 1e9, 'checkReference': 1.0, 'maxFactors': 1, 'modulusTableMax': 0.0,
          'runShapeSamples': 1, 'adaptWords': 0,
          'adaptArrays': 0, 'adaptBits': 0, 'adaptLag': 0, 'blocksWanted': 1, 'blockMin': 1,
          'blockLen': Opt(1)},
    'B': {'maxDegree': 200, 'maxBitsInPrime': 10, 'defaultNumPrimes': 60,
          'defaultMaxForbidden': 200, 'rbaPack': 8, 'chunk': 17, 'defaultArraySize': 1000,
          'defaultSturm': 62, 'veryBig': 7, 'maxDivisors': 100000,
          'jacobiPrimes': 200, 'jacobiTable': 100000, 'mulModLimit': 2 ** 31 + 11,
          'stage3Limit': 2 ** 31 + 5, 'useLongInPhase2': False,
          'sp2Extra': 40, 'rowBias': 2 ** 30, 'numStrides': 8, 'rbaShift': 9,
          'survivorsPerWord': 1e-12, 'sp2U0': 1e300, 'sp3PerSurvivor': 0.9, 'sp3PerDenom': 0.0,
          'sp3Coprime': 2.5, 'costTable': 1e306, 'compositeMax': 1023, 'costBp': 1e3,
          'costSetup': 0.0, 'costCall': 1e5, 'costLine': 100.0, 'costPhase2': 1e-3,
          'costSurvivor': 1e9, 'costCheck': 7.0, 'checkStep': 1e3, 'checkLimb': 1e3,
          'checkCall': 0.5, 'checkRoot': 0.0, 'checkReference': 1e-9, 'maxFactors': 6,
          'modulusTableMax': 1e300, 'runShapeSamples': 200, 'adaptWords': 2 ** 40,
          'adaptArrays': 2 ** 40, 'adaptBits': 2 ** 40, 'adaptLag': 1000, 'blocksWanted': 10 ** 6,
          'blockMin': 1000, 'blockLen': Opt(None)},
    'C2': {'chunk': 2},
    'C3': {'chunk': 3},
    'C5': {'chunk': 5},
    'C12': {'chunk': 12},
    'P8': {'rbaPack': 8, 'rbaShift': 9},
    'P2': {'rbaPack': 2, 'rbaShift': 7},
    'P1C5': {'rbaPack': 1, 'rbaShift': 6, 'chunk': 5},
    'L1': {'adaptLag': 1, 'blockLen': Opt(3)},
    'W1': {'blocksWanted': 1},
}

# Environment variables that would change what lake does in the copy (package URLs, an artifact
# cache, another search path); they are removed from the environment of the lake commands.
DROPPED_ENV = ('LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT', 'LAKE', 'LAKE_HOME',
               'LAKE_PKG_URL_MAP', 'LAKE_ARTIFACT_CACHE', 'LAKE_CACHE_DIR', 'LAKE_CACHE_KEY',
               'LAKE_NO_CACHE')

_MODIFIERS = r'(?:@\[[^\]\n]*\]\s*)?(?:(?:private|protected|public|noncomputable)\s+)*'
_CONST_TYPE = r'(?:Nat|ℕ|Int|ℤ|Bool|Float|Option Nat)'
DEF_NAT_RE = re.compile(r'^' + _MODIFIERS
                        + r'def\s+(?P<name>[^\s:]+)\s*:\s*' + _CONST_TYPE + r'\s*:=',
                        re.MULTILINE)
GUARD_RE = re.compile(r'#guard(?=[ \t\r\n]|$)')
MODIFIER_IN_RE = re.compile(r'^(?:open|set_option)\b.*\bin\s*$')
COMMAND_START_RE = re.compile(r'(?:[A-Za-z_@#«]|--|/-)')
ANSI_RE = re.compile(r'\x1b\[[0-9;?]*[A-Za-z]')
ERROR_LINE_RE = re.compile(r'^\s*error:', re.MULTILINE)
WARNING_LINE_RE = re.compile(r'^\s*warning:', re.MULTILINE)
LEAN_ERROR_RE = re.compile(
    r'^\s*error:\s*(?:\./)*(?P<file>[^\s:]+\.lean):(?P<line>\d+):(?P<col>\d+):\s*(?P<msg>.*)$')
LOG_ITEM_RE = re.compile(r'^\s*(?:error:|warning:|info:|trace:|[✖⚠✔ℹ•]|Some required|Build )')
DECL_RE = re.compile(
    r'^' + _MODIFIERS + r'(?:(?:partial|unsafe|meta|nonrec)\s+)*'
    r'(?P<kind>theorem|lemma|def|abbrev|instance|example|structure|inductive|class|opaque|axiom)'
    r'\b\s*(?P<name>[^\s:({\[]*)')
COMMAND_RE = re.compile(r'^(?P<cmd>#[A-Za-z_]+)')
BUILT_RE = re.compile(r'^\S*\s*\[\d+/\d+\] Built (\S+)', re.MULTILINE)
VARIANT_NAME_RE = re.compile(r'^[A-Za-z0-9][A-Za-z0-9_.-]*$')


class SetupError(Exception):
    """An error in the arguments or the setup, before or outside a build."""


def log(msg=''):
    print(msg, flush=True)


def fmt_time(seconds):
    seconds = int(round(seconds))
    return f'{seconds // 60}m{seconds % 60:02d}s'


def lean_value(value):
    """A value of a constant as Lean writes it: `true`/`false` for a Boolean, a literal with a
    decimal point or an exponent for a float (`repr`, which Lean reads as the same double)."""
    if isinstance(value, bool):
        return 'true' if value else 'false'
    if isinstance(value, float):
        s = repr(value)
        return s if ('.' in s or 'e' in s) else s + '.0'
    if isinstance(value, Opt):
        return 'none' if value.n is None else f'some {value.n}'
    return str(value)



def fmt_consts(consts):
    return ' '.join(f'{k}={lean_value(v)}' for k, v in consts.items())


# ---------------------------------------------------------------------------------------------
# Arguments and variants


def parse_variant(spec):
    """`NAME:const=value,...` as (name, {const: value})."""
    name, sep, rest = spec.partition(':')
    if not sep or not VARIANT_NAME_RE.match(name):
        raise SetupError(f'--variant {spec!r}: expected NAME:const=value,... with a plain NAME')
    consts = {}
    for item in filter(None, (s.strip() for s in rest.split(','))):
        key, eq, value = item.partition('=')
        key, value = key.strip(), value.strip()
        if not eq or not key or not re.fullmatch(
                r'-?\d+|true|false|\d+\.\d*(?:e-?\d+)?|\d+e-?\d+', value):
            raise SetupError(f'--variant {spec!r}: {item!r} is not const=<integer>, const=<float>, '
                             f'const=true or const=false')
        if key in consts:
            raise SetupError(f'--variant {spec!r}: {key} is set twice')
        consts[key] = (value == 'true' if value in ('true', 'false')
                       else int(value) if re.fullmatch(r'-?\d+', value) else float(value))
    if not consts:
        raise SetupError(f'--variant {spec!r}: no constants')
    return name, consts


def const_line_re(name):
    """The one-line definition `def <name> : Nat := <value>` (or `: Int`, `: Bool`), with the
    value as a group."""
    return re.compile(r'^(?P<head>' + _MODIFIERS + r'def\s+' + re.escape(name)
                      + r'\s*:\s*' + _CONST_TYPE + r'\s*:=[ \t]*)(?P<value>\S[^\n]*?)[ \t]*$',
                      re.MULTILINE)


def check_variants(variants, constants_text):
    """Every constant of every variant is a one-line `def <name> : Nat := <value>` (or `: Int`,
    `: Bool`) at HEAD, a Boolean constant with a Boolean value and the others with integers."""
    known = DEF_NAT_RE.findall(constants_text)
    for name, consts in variants.items():
        for key, value in consts.items():
            if key not in known:
                raise SetupError(f'variant {name}: {key} is not a `def {key} : Nat`, `: Int` or '
                                 f'`: Bool` of {CONSTANTS_FILE} (it has: {", ".join(known)})')
            lines = const_line_re(key).findall(constants_text)
            if len(lines) != 1:
                raise SetupError(f'variant {name}: `def {key} : Nat (or Int, Bool) := <value>` '
                                 f'does not occur exactly once, on one line, in {CONSTANTS_FILE}')
            is_bool = re.search(r':\s*Bool\s*:=', lines[0][0]) is not None
            is_float = re.search(r':\s*Float\s*:=', lines[0][0]) is not None
            is_opt = re.search(r':\s*Option Nat\s*:=', lines[0][0]) is not None
            kind = ('bool' if isinstance(value, bool) else 'option' if isinstance(value, Opt)
                    else type(value).__name__)
            want = 'bool' if is_bool else 'float' if is_float else 'option' if is_opt else 'int'
            if kind != want:
                raise SetupError(f'variant {name}: {key} takes a value of the kind {want}, not '
                                 f'{lean_value(value)}')


def set_constants(text, consts):
    """`text` with the values of `consts`; each definition must occur exactly once."""
    for key, value in consts.items():
        text, count = const_line_re(key).subn(lambda m: m.group('head') + lean_value(value),
                                              text)
        if count != 1:
            raise SetupError(f'`def {key} : Nat (or Int, Bool) := <value>` occurs {count} times in '
                             f'{CONSTANTS_FILE}, not once')
    return text


# ---------------------------------------------------------------------------------------------
# The #guard commands


def block_depth_after(depth, line):
    """The nesting depth of block comments after `line`, given the depth before it."""
    i, n = 0, len(line)
    while i < n:
        if depth > 0:
            if line.startswith('/-', i):
                depth, i = depth + 1, i + 2
            elif line.startswith('-/', i):
                depth, i = depth - 1, i + 2
            else:
                i += 1
            continue
        if line.startswith('--', i):
            break
        if line.startswith('/-', i):
            depth, i = depth + 1, i + 2
        elif line[i] == '"':
            i += 1
            while i < n and line[i] != '"':
                i += 2 if line[i] == '\\' else 1
            i += 1
        elif line[i] == "'" and i + 2 < n and line[i + 2] == "'":
            i += 3
        else:
            i += 1
    return depth


def strip_guards(text, path):
    """`text` without its `#guard` commands: (new text, number removed, line map), where the line
    map gives for each line of the new text its line number in `text`."""
    lines = text.splitlines(keepends=True)
    kept = []
    removed = 0
    depth = 0
    i = 0
    while i < len(lines):
        line = lines[i]
        if depth == 0 and GUARD_RE.match(line):
            if kept and MODIFIER_IN_RE.match(kept[-1][1]):
                kept.pop()
            j = i + 1
            while j < len(lines) and lines[j].strip() and lines[j][0] in ' \t':
                j += 1
            if j < len(lines) and lines[j].strip() and not COMMAND_START_RE.match(lines[j]):
                raise SetupError(f'{path}:{i + 1}: cannot tell where this #guard ends '
                                 f'(line {j + 1} starts at column 0 but begins no command)')
            for k in range(i, j):
                depth = block_depth_after(depth, lines[k])
            if depth != 0:
                raise SetupError(f'{path}:{i + 1}: this #guard leaves a block comment open')
            removed += 1
            i = j
            continue
        kept.append((i + 1, line))
        depth = block_depth_after(depth, line)
        i += 1
    return ''.join(line for _, line in kept), removed, [n for n, _ in kept]


def strip_guards_in_tree(copy):
    """Remove the #guard commands of every Lean file under copy/Ratpoints: the counts per file and
    the line maps of the files that changed."""
    counts, line_maps = {}, {}
    for path in sorted((copy / GUARD_DIR).rglob('*.lean')):
        rel = path.relative_to(copy).as_posix()
        text = path.read_text(encoding='utf-8')
        new_text, removed, line_map = strip_guards(text, rel)
        if removed:
            path.write_text(new_text, encoding='utf-8')
            counts[rel] = removed
            line_maps[rel] = line_map
    return counts, line_maps


# ---------------------------------------------------------------------------------------------
# The copy and the shared packages


def git(repo, *args):
    res = subprocess.run(['git', '-C', str(repo), *args], capture_output=True, text=True)
    if res.returncode != 0:
        raise SetupError(f'git -C {repo} {" ".join(args)}: {res.stderr.strip()}')
    return res.stdout.strip()


def remove_copy(copy, workdir):
    """Delete the copy, never following the symlink to the shared packages."""
    if copy.is_symlink():
        copy.unlink()
        return
    if not copy.exists():
        return
    if copy.resolve().parent != workdir.resolve():
        raise SetupError(f'refusing to delete {copy}: not directly inside {workdir}')
    packages = copy / '.lake' / 'packages'
    if packages.is_symlink():
        packages.unlink()
    shutil.rmtree(copy)


def export_head(repo, dest):
    """`git -C repo archive HEAD | tar -x -C dest`, checking both commands."""
    archive = subprocess.Popen(['git', '-C', str(repo), 'archive', '--format=tar', 'HEAD'],
                               stdout=subprocess.PIPE)
    tar = subprocess.run(['tar', '-x', '-C', str(dest)], stdin=archive.stdout)
    archive.stdout.close()
    if archive.wait() != 0 or tar.returncode != 0:
        raise SetupError(f'git archive HEAD | tar -x into {dest} failed')


def find_lake(copy, override):
    if override:
        return override
    toolchain = (copy / 'lean-toolchain').read_text().strip()
    elan_home = Path(os.environ.get('ELAN_HOME', Path.home() / '.elan'))
    lake = (elan_home / 'toolchains' / toolchain.replace('/', '--').replace(':', '---')
            / 'bin' / 'lake')
    if lake.is_file() and os.access(lake, os.X_OK):
        return str(lake)
    found = shutil.which('lake')
    if not found:
        raise SetupError(f'no lake for the toolchain {toolchain}')
    return found


def check_packages(repo, copy):
    """The shared packages folder, after checking that lake will neither check out, nor delete,
    nor clone a package in it: every package of the copy's manifest is there at the manifest's
    revision, and every `[[require]]` of the lakefile is in the manifest. Returns the folder and
    a list of warnings."""
    manifest = json.loads((copy / 'lake-manifest.json').read_text())
    shared = repo / manifest.get('packagesDir', '.lake/packages')
    if not shared.is_dir():
        raise SetupError(f'{shared} does not exist: build the repository first')
    problems, warnings, names = [], [], set()
    for entry in manifest.get('packages', []):
        name = entry['name']
        if name.startswith('«') and name.endswith('»'):
            name = name[1:-1]
        names.add(name)
        if entry.get('type') != 'git':
            problems.append(f'{name}: a dependency of type {entry.get("type")} is not supported')
            continue
        pkg = shared / name
        if not (pkg / '.git').exists():
            problems.append(f'{name}: no git repository at {pkg}')
            continue
        head = git(pkg, 'rev-parse', '--verify', 'HEAD')
        if head != entry['rev']:
            problems.append(f'{name}: at {head}, but the manifest of HEAD has {entry["rev"]}')
        url = subprocess.run(['git', '-C', str(pkg), 'remote', 'get-url', 'origin'],
                             capture_output=True, text=True).stdout.strip()

        def norm(u):
            u = u.rstrip('/')
            return u[:-4] if u.endswith('.git') else u

        if norm(url) != norm(entry.get('url', '')):
            warnings.append(f'{name}: remote {url!r}, manifest {entry.get("url")!r}')
    lakefile = copy / 'lakefile.toml'
    if lakefile.exists():
        config = tomllib.loads(lakefile.read_text())
        for req in config.get('require', []):
            if req.get('name') not in names:
                problems.append(f'require {req.get("name")!r} of the lakefile is not in the '
                                'manifest')
    else:
        warnings.append('no lakefile.toml: the requirements were not compared with the manifest')
    if problems:
        raise SetupError('the shared packages do not match the manifest of HEAD (lake would '
                         'change them):\n  ' + '\n  '.join(problems))
    return shared, warnings


def changed_since(root, stamp, limit=8):
    """Up to `limit` paths under `root` (symlinks not followed) modified at or after `stamp`."""
    hits = []
    try:
        if os.lstat(root).st_mtime >= stamp:
            hits.append(str(root))
    except FileNotFoundError:
        return hits
    for dirpath, dirnames, filenames in os.walk(root):
        for entry in dirnames + filenames:
            path = os.path.join(dirpath, entry)
            try:
                if os.lstat(path).st_mtime >= stamp:
                    hits.append(path)
                    if len(hits) >= limit:
                        return hits
            except FileNotFoundError:
                pass
    return hits


# ---------------------------------------------------------------------------------------------
# lake


def lake_env():
    env = {k: v for k, v in os.environ.items() if k not in DROPPED_ENV}
    env['LEAN_NUM_THREADS'] = '2'
    return env


def run_logged(cmd, cwd, log_path, timeout):
    """Run `cmd` in `cwd` with its output in `log_path`: the log text, the exit status (None on a
    timeout) and whether it timed out."""
    with open(log_path, 'w', encoding='utf-8') as out:
        out.write(f'# cwd: {cwd}\n# LEAN_NUM_THREADS=2 {" ".join(cmd)}\n')
        out.flush()
        proc = subprocess.Popen(cmd, cwd=cwd, env=lake_env(), stdout=out,
                                stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL,
                                start_new_session=True)
        timed_out = False
        try:
            proc.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            kill_group(proc)
        except BaseException:
            kill_group(proc)
            raise
    text = ANSI_RE.sub('', Path(log_path).read_text(encoding='utf-8', errors='replace'))
    return text, (None if timed_out else proc.returncode), timed_out


def kill_group(proc):
    for sig in (signal.SIGTERM, signal.SIGKILL):
        try:
            os.killpg(proc.pid, sig)
        except ProcessLookupError:
            return
        try:
            proc.wait(timeout=20)
            return
        except subprocess.TimeoutExpired:
            pass


def parse_errors(text, copy, line_maps):
    """The Lean errors of a build log: (file, line, line at HEAD or None, declaration, message
    lines)."""
    lines = text.splitlines()
    errors = []
    for i, line in enumerate(lines):
        m = LEAN_ERROR_RE.match(line)
        if not m:
            continue
        msg = [m.group('msg')]
        for cont in lines[i + 1:i + 4]:
            if LOG_ITEM_RE.match(cont):
                break
            msg.append(cont)
        rel, lineno = m.group('file'), int(m.group('line'))
        rel = os.path.relpath(rel, copy) if os.path.isabs(rel) else os.path.normpath(rel)
        head_line = None
        if rel in line_maps and 0 < lineno <= len(line_maps[rel]):
            head_line = line_maps[rel][lineno - 1]
        errors.append((rel, lineno, head_line, enclosing_decl(copy / rel, lineno), msg))
    return errors


def enclosing_decl(path, lineno):
    """The declaration or command of `path` that contains line `lineno`, as far as one can tell."""
    try:
        lines = path.read_text(encoding='utf-8').splitlines()
    except OSError:
        return '?'
    for k in range(min(lineno, len(lines)) - 1, -1, -1):
        m = DECL_RE.match(lines[k])
        if m:
            return f'{m.group("kind")} {m.group("name")}'.strip()
        m = COMMAND_RE.match(lines[k])
        if m:
            cmd = lines[k].strip()
            if cmd.endswith(' in') and k + 1 < len(lines):
                cmd += ' ' + lines[k + 1].strip()
            return f'`{cmd}` (line {k + 1})'
    return '?'


# ---------------------------------------------------------------------------------------------
# A variant


def run_variant(name, consts, args, workdir, logs_dir, repo):
    """Prepare and build one variant: a result dict."""
    res = {'name': name, 'consts': consts, 'status': 'FAIL', 'errors': [], 'details': [],
           'notes': []}
    t0 = time.monotonic()
    copy = workdir / name
    tag = f'[{name}]'
    log(f'{tag} {fmt_consts(consts)}')
    remove_copy(copy, workdir)
    copy.mkdir(parents=True)
    export_head(repo, copy)

    shared, warnings = check_packages(repo, copy)
    for w in warnings:
        log(f'{tag} warning: {w}')
        res['notes'].append(w)
    (copy / '.lake').mkdir()
    (copy / '.lake' / 'packages').symlink_to(shared.resolve(), target_is_directory=True)

    constants = copy / CONSTANTS_FILE
    constants.write_text(set_constants(constants.read_text(encoding='utf-8'), consts),
                         encoding='utf-8')
    counts, line_maps = strip_guards_in_tree(copy)
    for rel, count in counts.items():
        log(f'{tag}   {rel}: {count} #guard command{"s" if count != 1 else ""} removed')
    log(f'{tag}   {sum(counts.values())} #guard commands removed in {len(counts)} files')
    res['guards'] = counts
    res['setup_time'] = time.monotonic() - t0
    if args.prepare_only:
        res['status'] = 'PREPARED'
        res['total_time'] = time.monotonic() - t0
        return res

    lake = find_lake(copy, args.lake)
    stamp = time.time()
    t1 = time.monotonic()
    nobuild_log = logs_dir / f'{name}-mathlib-nobuild.log'
    log(f'{tag} lake build --no-build Mathlib (log {nobuild_log})')
    text, status, timed_out = run_logged([lake, 'build', '--no-build', 'Mathlib'], copy,
                                         nobuild_log, args.timeout)
    res['nobuild_time'] = time.monotonic() - t1
    res['nobuild_log'] = str(nobuild_log)
    # Not a piped status: lake's own, which `--no-build` sets when a target is out of date.
    if status != 0 or ERROR_LINE_RE.search(text):
        res['log'] = str(nobuild_log)
        res['abort'] = ('aborted: `lake build --no-build Mathlib` in the copy says that Mathlib '
                        'is not up to date in the shared packages; nothing was built')
        lines = [ln.strip() for ln in text.splitlines() if ln.strip() and not ln.startswith('#')]
        res['details'] = [ln for ln in lines if re.match(r'(?:✖|error:)', ln)] or lines[-6:]
        res['total_time'] = time.monotonic() - t0
        res['changed'] = changed_since(shared.resolve(), stamp)
        return res

    t2 = time.monotonic()
    build_log = logs_dir / f'{name}-build.log'
    log(f'{tag} LEAN_NUM_THREADS=2 lake build {LIBRARY} (log {build_log})')
    # Success is judged by the log alone; the exit status is only recorded.
    text, status, timed_out = run_logged([lake, 'build', LIBRARY], copy, build_log, args.timeout)
    res['build_time'] = time.monotonic() - t2
    res['build_status'] = status
    res['log'] = str(build_log)
    res['warnings'] = len(WARNING_LINE_RE.findall(text))
    jobs = re.search(r'Build completed successfully(?: \((\d+) jobs?\))?', text)
    if jobs and not ERROR_LINE_RE.search(text) and not timed_out:
        res['status'] = 'OK'
        res['jobs'] = jobs.group(1)
    else:
        res['errors'] = parse_errors(text, copy, line_maps)
        if timed_out:
            res['notes'].append(f'timed out after {args.timeout} s')
        if not res['errors']:
            res['details'] = [ln.strip() for ln in text.splitlines() if ERROR_LINE_RE.match(ln)]
    # Lake prints a `Built` line for every job it runs: one outside the project means that a
    # dependency was rebuilt, inside the shared packages.
    outside = sorted({m for m in BUILT_RE.findall(text) if not m.startswith(LIBRARY)})
    if outside:
        res['notes'].append('built outside the project: ' + ', '.join(outside[:10]))
    res['changed'] = changed_since(shared.resolve(), stamp)
    res['total_time'] = time.monotonic() - t0
    log(f'{tag} {res["status"]} after {fmt_time(res["total_time"])}')
    return res


def report(results, head):
    log()
    log(f'== constants check of {head}')
    for r in results:
        times = []
        if 'nobuild_time' in r:
            times.append(f'no-build check {fmt_time(r["nobuild_time"])}')
        if 'build_time' in r:
            times.append(f'build {fmt_time(r["build_time"])}')
        if 'total_time' in r:
            times.append(f'total {fmt_time(r["total_time"])}')
        extra = []
        if r['status'] == 'OK':
            extra.append(f'{r.get("jobs") or "?"} jobs, {r.get("warnings", 0)} warning lines')
        if r.get('abort'):
            extra.append(r['abort'])
        if r.get('changed'):
            extra.append('THE SHARED PACKAGES CHANGED')
        log(f'{r["status"]:<5} {r["name"]}  {fmt_consts(r["consts"])}  {", ".join(times)}'
            f'{"  " + "; ".join(extra) if extra else ""}  log: {r.get("log", "-")}')
        for rel, lineno, head_line, decl, msg in r['errors'][:MAX_ERRORS]:
            at_head = f' (line {head_line} at HEAD)' if head_line not in (None, lineno) else ''
            log(f'        {rel}:{lineno}{at_head} in {decl}: {msg[0]}')
            for cont in msg[1:]:
                log(f'            {cont}')
        if len(r['errors']) > MAX_ERRORS:
            log(f'        ... {len(r["errors"]) - MAX_ERRORS} more errors in the log')
        for line in r['details'][:MAX_ERRORS]:
            log(f'        {line}')
        if len(r['details']) > MAX_ERRORS:
            log(f'        ... {len(r["details"]) - MAX_ERRORS} more lines in the log')
        for note in r['notes']:
            log(f'        note: {note}')
        for path in r.get('changed', []):
            log(f'        changed: {path}')


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--repo', default=DEFAULT_REPO, help='the repository (only read)')
    parser.add_argument('--workdir', required=True,
                        help='where the copies and the logs go '
                             '(inside the repository only under tmp/)')
    parser.add_argument('--variant', action='append', default=[],
                        metavar='NAME:const=value,...',
                        help='a variant (may be repeated; replaces the built-in list)')
    parser.add_argument('--keep', action='store_true', help='keep the copies')
    parser.add_argument('--prepare-only', action='store_true',
                        help='stop each variant before its first lake command (implies --keep)')
    parser.add_argument('--lake', help='the lake executable to run')
    parser.add_argument('--timeout', type=int, default=7200,
                        help='stop a build after this many seconds (default 7200)')
    args = parser.parse_args(argv)

    try:
        repo = Path(args.repo).resolve()
        workdir = Path(args.workdir).absolute()
        if (workdir.resolve() == repo or repo in workdir.resolve().parents) and \
                (repo / 'tmp') not in [workdir.resolve(), *workdir.resolve().parents]:
            raise SetupError(f'the workdir {workdir} lies inside the repository {repo} '
                             '(only its untracked tmp/ may hold copies)')
        if args.variant:
            variants = {}
            for spec in args.variant:
                name, consts = parse_variant(spec)
                if name in variants:
                    raise SetupError(f'variant {name} is given twice')
                variants[name] = consts
        else:
            variants = VARIANTS
        head = git(repo, 'rev-parse', '--short', 'HEAD')
        check_variants(variants, git(repo, 'show', f'HEAD:{CONSTANTS_FILE}'))
        workdir.mkdir(parents=True, exist_ok=True)
        logs_dir = workdir / 'logs'
        logs_dir.mkdir(exist_ok=True)
        log(f'repository {repo} at HEAD {head}; workdir {workdir}')
    except SetupError as e:
        print(f'constants_check: {e}', file=sys.stderr)
        return 2
    results = []
    for name, consts in variants.items():
        try:
            results.append(run_variant(name, consts, args, workdir, logs_dir, repo))
        except SetupError as e:
            # A setup that fails (the shared packages, the copy) fails for the later variants too.
            report(results, head)
            print(f'constants_check: variant {name}: {e}', file=sys.stderr)
            return 2
        finally:
            if not (args.keep or args.prepare_only):
                remove_copy(workdir / name, workdir)
    report(results, head)
    return 0 if all(r['status'] in ('OK', 'PREPARED') and not r.get('changed')
                    for r in results) else 1


if __name__ == '__main__':
    sys.exit(main())

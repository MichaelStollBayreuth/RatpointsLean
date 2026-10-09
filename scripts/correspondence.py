#!/usr/bin/env python3
"""The correspondence record between the Lean model and the C code of ratpoints.

usage: scripts/correspondence.py [command] [options]

commands:
  check     run every check (the default); exit 1 on an error
  lock      record the current ranges, with the hash of their text and their owners, and the C
            links of the blueprint in correspondence/lock.json; run it after reviewing what
            `check` reports as new or changed
  table     regenerate the blueprint chapter blueprint/src/generated/correspondence.tex
  coverage  list the stretches of non-comment C lines that lie in no recorded range
  pin       print one field of the pin (--field commit|tag|repository), for CI

options:
  --repo PATH    a git clone of ratpoints that contains the pinned commit (default: the
                 environment variable RATPOINTS_REPO)
  --decls FILE   the JSON file written by scripts/Correspondence.lean; without it, the script
                 builds the model and runs scripts/Correspondence.lean itself
  --complete     (check) also fail when a non-comment line of a C file lies in no range

The record (correspondence/README.md has the details):
- the ranges the model covers are in the docstrings of the public declarations of the model, in
  a paragraph "C: `file:first-last`, ..." (or `file:line`); the ranges excluded from the model
  are the [[excluded]] tables of correspondence/ratpoints.toml, which also holds the pin (the
  ratpoints commit all line numbers refer to) and the list of C files;
- correspondence/lock.json holds, for every range, the SHA-256 of its text at the pin and its
  owners (the Lean declarations that model it, or its exclusion), and the hash of the text of
  every C link of the blueprint; the `lock` command writes it after a review;
- the blueprint links to the C code with \\csource{file}{first}{last}; inside a node of the
  dependency graph that names declarations with \\lean, the links are exactly the ranges of the
  model declarations it names; elsewhere (prose, remarks) any range may be cited.

The checks: the pin exists in the repository (and its tag, if present there, points to it); every
range lies in a listed file and within its lines; no line lies in two different ranges; the
excluded ranges have a known kind and a reason; no private declaration and no copied docstring
carries a record; every range and every C link of the blueprint is in the lock with the same text
and the same owners (after a move of the pin: has the text and the owners of some locked range or
link, so that exactly the new and changed ones are reported); the generated blueprint chapter is
up to date; the blueprint's \\ratpointscommit is the pin; the C links of the nodes are as above;
every model declaration with a range is named by a node; with --complete, every non-comment line
lies in a range.
"""

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tomllib
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
RECORD = ROOT / 'correspondence' / 'ratpoints.toml'
LOCK = ROOT / 'correspondence' / 'lock.json'
BLUEPRINT = ROOT / 'blueprint' / 'src'
TABLE = BLUEPRINT / 'generated' / 'correspondence.tex'
EXCLUDED_KINDS = ('parameters', 'threads', 'memory', 'instrumentation', 'interface', 'other')
# the theorem types plastexdepgraph draws when web.tex gives no `thms=` option
GRAPH_ENVS = ('definition', 'lemma', 'proposition', 'theorem', 'corollary')
ITEM = re.compile(r'^([A-Za-z0-9_.+-]+):(\d+)(?:-(\d+))?$')
SP = r'[ \t]*(?:\n[ \t]*)?'  # what TeX skips between a command and its arguments
CITE = re.compile(r'\\csource' + SP + r'\{([^}]*)\}' + SP + r'\{([^}]*)\}' + SP + r'\{([^}]*)\}')
LEAN = re.compile(r'\\lean' + SP + r'\{([^}]*)\}')


def rel(p):
    """`p` relative to the repository root, for messages (or as it is, if outside)."""
    try:
        return p.relative_to(ROOT)
    except ValueError:
        return p


class RecordError(Exception):
    """A malformed record entry that makes the further checks meaningless."""


# ---------------------------------------------------------------------------------------------
# The C side


def code_lines(text):
    """For each line of a C source text, whether it holds code outside comments (a preprocessor
    line counts as code; a line holding only a comment or white space does not). A `//` comment,
    a string or a character literal whose line ends with a backslash goes on in the next line."""
    lines = text.split('\n')
    if lines and lines[-1] == '':
        lines.pop()
    flags, state = [], 'code'  # 'code', 'block' (/* */), 'line' (//), 'string', 'char'
    for line in lines:
        has_code, i, n = False, 0, len(line)
        while i < n and state != 'line':
            c = line[i]
            if state == 'block':
                if line.startswith('*/', i):
                    state, i = 'code', i + 2
                else:
                    i += 1
            elif state in ('string', 'char'):
                has_code = True
                if c == '\\':
                    i += 2
                    continue
                if c == ('"' if state == 'string' else "'"):
                    state = 'code'
                i += 1
            elif line.startswith('/*', i):
                state, i = 'block', i + 2
            elif line.startswith('//', i):
                state = 'line'
            else:
                if c in '"\'':
                    state = 'string' if c == '"' else 'char'
                if not c.isspace():
                    has_code = True
                i += 1
        if state in ('string', 'char', 'line') and not line.endswith('\\'):
            state = 'code'  # a literal or a // comment ends with its line, unless spliced
        flags.append(has_code)
    return flags


def git(repo, *args):
    return subprocess.run(['git', '-C', str(repo), *args], capture_output=True, text=True)


@dataclass
class CFile:
    path: str
    lines: list    # the text of each line
    code: list     # code_lines of the text


def load_c_files(repo, commit, paths):
    files = {}
    for p in paths:
        r = git(repo, 'show', f'{commit}:{p}')
        if r.returncode != 0:
            raise RecordError(f'{p} does not exist at the pinned commit {commit}')
        lines = r.stdout.split('\n')
        if lines and lines[-1] == '':
            lines.pop()
        files[p] = CFile(p, lines, code_lines(r.stdout))
    return files


def text_hash(files, file, first, last):
    text = '\n'.join(files[file].lines[first - 1:last])
    return hashlib.sha256(text.encode('utf-8')).hexdigest()


# ---------------------------------------------------------------------------------------------
# The ranges


@dataclass
class Range:
    file: str
    first: int
    last: int
    names: list = field(default_factory=list)     # the Lean declarations that model it
    excluded: dict = None                         # the [[excluded]] table, if excluded

    @property
    def key(self):
        return f'{self.file}:{self.first}-{self.last}'

    @property
    def owners(self):
        if self.excluded is not None:
            return [f'excluded ({self.excluded.get("kind")})']
        return sorted(self.names)


def parse_item(item, where, errors):
    m = ITEM.match(item)
    if not m:
        errors.append(f'{where}: malformed range `{item}` (expected `file:first-last` or '
                      f'`file:line`)')
        return None
    first = int(m.group(2))
    last = int(m.group(3)) if m.group(3) else first
    return m.group(1), first, last


def paragraphs(doc):
    """The paragraphs of a docstring, each as a list of stripped lines."""
    paras, cur = [], []
    for line in doc.split('\n'):
        if line.strip():
            cur.append(line.strip())
        elif cur:
            paras.append(cur)
            cur = []
    if cur:
        paras.append(cur)
    return paras


def parse_doc(name, doc, errors):
    """The C ranges and the deviations a docstring records."""
    items, deviations, seen_c = [], [], False
    for para in paragraphs(doc):
        for line in para[1:]:
            if line.startswith(('C:', 'Deviation:')):
                errors.append(f'{name}: `{line.split(":")[0]}:` must begin a paragraph of its own '
                              f'(a blank line before it)')
        text = ' '.join(para)
        if text.startswith('C:'):
            if seen_c:
                errors.append(f'{name}: more than one `C:` paragraph in the docstring')
            seen_c = True
            body = text[2:].strip().rstrip('.')
            parts = [s.strip() for s in body.split(',')]
            for part in parts:
                if not (len(part) > 2 and part[0] == part[-1] == '`'):
                    errors.append(f'{name}: malformed `C:` paragraph, item `{part}` is not a '
                                  f'code span')
                    continue
                it = parse_item(part[1:-1], name, errors)
                if it:
                    items.append(it)
        elif text.startswith('Deviation:'):
            deviations.append(text[len('Deviation:'):].strip())
    if deviations and not seen_c:
        errors.append(f'{name}: a `Deviation:` paragraph without a `C:` paragraph')
    return items, deviations


def collect_ranges(decls, record, files, errors):
    """All ranges, merged by key, with their owners; the deviations by declaration."""
    by_key, deviations, decl_ranges = {}, {}, {}

    def add(file, first, last, where):
        if file not in files:
            errors.append(f'{where}: `{file}` is not one of the C files of the record')
            return None
        n = len(files[file].lines)
        if not 1 <= first <= last <= n:
            errors.append(f'{where}: lines {first}-{last} are not within 1-{n} of {file}')
            return None
        r = Range(file, first, last)
        return by_key.setdefault(r.key, r)

    docs = {}
    for d in decls:
        items, devs = parse_doc(d['name'], d['doc'], errors)
        if not (items or devs):
            continue
        if d.get('private'):
            errors.append(f'{d["name"]} is private but its docstring records C code: make it '
                          f'public (a blueprint node cannot name a private declaration), or cite '
                          f'the lines from its public caller')
            continue
        if d['doc'] in docs:
            errors.append(f'{d["name"]} and {docs[d["doc"]]} have the same docstring with a '
                          f'record (a copied docstring, `inherit_doc`?): record the C code once')
            continue
        docs[d['doc']] = d['name']
        if devs:
            deviations[d['name']] = devs
        for file, first, last in items:
            r = add(file, first, last, d['name'])
            if r is None:
                continue
            if d['name'] in r.names:
                errors.append(f'{d["name"]}: cites {r.key} twice')
                continue
            r.names.append(d['name'])
            decl_ranges.setdefault(d['name'], []).append(r)
    for i, e in enumerate(record.get('excluded', [])):
        where = f'excluded range #{i + 1} of {RECORD.name}'
        unknown = set(e) - {'file', 'lines', 'kind', 'reason'}
        if unknown:
            errors.append(f'{where}: unknown fields {sorted(unknown)}')
        if e.get('kind') not in EXCLUDED_KINDS:
            errors.append(f'{where}: kind must be one of {", ".join(EXCLUDED_KINDS)}')
        if not str(e.get('reason', '')).strip():
            errors.append(f'{where}: no reason given')
        it = parse_item(f'{e.get("file", "")}:{e.get("lines", "")}', where, errors)
        if it is None:
            continue
        r = add(*it, where)
        if r is None:
            continue
        if r.excluded is not None:
            errors.append(f'{where}: {r.key} is excluded twice')
        r.excluded = e
    for r in by_key.values():
        if r.excluded is not None and r.names:
            errors.append(f'{r.key} is both excluded and modelled (by {", ".join(r.names)})')
    return by_key, deviations, decl_ranges


def check_overlaps(ranges, errors):
    by_file = {}
    for r in ranges.values():
        by_file.setdefault(r.file, []).append(r)
    for rs in by_file.values():
        rs.sort(key=lambda r: (r.first, r.last))
        for a, b in zip(rs, rs[1:]):
            if b.first <= a.last:
                errors.append(f'{a.key} and {b.key} overlap: every line must lie in exactly one '
                              f'range')


# ---------------------------------------------------------------------------------------------
# The lock


def lock_data(ranges, citations, files, commit):
    return {'commit': commit,
            'ranges': {k: {'hash': text_hash(files, r.file, r.first, r.last),
                           'owners': r.owners}
                       for k, r in sorted(ranges.items())},
            'citations': {f'{f}:{a}-{b}': text_hash(files, f, a, b)
                          for f, a, b in sorted(citations)}}


def check_lock(ranges, citations, files, commit, errors):
    """At the pin of the lock: every range is locked with the same text and owners, and every
    C link of the blueprint is locked. After a move of the pin: report exactly the ranges whose
    text or owners no locked range has, and the links whose text no locked link has."""
    if not LOCK.exists():
        errors.append(f'{rel(LOCK)} is missing (run `correspondence.py lock`)')
        return
    lock = json.loads(LOCK.read_text())
    now = lock_data(ranges, citations, files, commit)
    locked, locked_cites = lock.get('ranges', {}), lock.get('citations', {})
    if lock.get('commit') == commit:
        for key, cur in now['ranges'].items():
            old = locked.get(key)
            who = ', '.join(cur['owners'])
            if old is None:
                errors.append(f'{key} is not in the lock: review it against {who}, then run '
                              f'`correspondence.py lock`')
            elif old.get('hash') != cur['hash']:
                errors.append(f'{key}: the lock holds another text for it (edited by hand?)')
            elif old.get('owners') != cur['owners']:
                errors.append(f'the counterpart of {key} changed from '
                              f'{", ".join(old.get("owners", []))} to {who}: review it, then run '
                              f'`correspondence.py lock`')
        for key in sorted(set(locked) - set(now['ranges'])):
            errors.append(f'the lock holds {key}, which is no longer a range (run '
                          f'`correspondence.py lock`)')
        for key in sorted(set(now['citations']) - set(locked_cites)):
            errors.append(f'the blueprint links to {key}, which is not in the lock: check the '
                          f'link, then run `correspondence.py lock`')
        for key in sorted(set(locked_cites) - set(now['citations'])):
            errors.append(f'the lock holds the link {key}, which the blueprint no longer has (run '
                          f'`correspondence.py lock`)')
        return
    pool = {(v.get('hash'), tuple(v.get('owners', []))) for v in locked.values()}
    for key, cur in now['ranges'].items():
        if (cur['hash'], tuple(cur['owners'])) not in pool:
            errors.append(f'{key} is new or changed since the review (its text or its counterpart '
                          f'{", ".join(cur["owners"])}): review it')
    for key, h in now['citations'].items():
        if h not in set(locked_cites.values()):
            errors.append(f'the blueprint\'s link to {key} shows a text that no locked link '
                          f'showed: check where it should point')
    errors.append(f'the lock refers to commit {lock.get("commit")}, the pin to {commit}: after '
                  f'the review of the ranges and links reported, run `correspondence.py lock`')


# ---------------------------------------------------------------------------------------------
# Coverage


def free_stretches(cf, ranges_of_file):
    """The maximal stretches of lines of `cf` in no range that hold code, trimmed to their first
    and last line of code, as (first, last, number of code lines)."""
    covered = [False] * len(cf.lines)
    for r in ranges_of_file:
        for i in range(r.first - 1, r.last):
            covered[i] = True
    out, i, n = [], 0, len(cf.lines)
    while i < n:
        if covered[i]:
            i += 1
            continue
        j = i
        while j < n and not covered[j]:
            j += 1
        idx = [k for k in range(i, j) if cf.code[k]]
        if idx:
            out.append((idx[0] + 1, idx[-1] + 1, len(idx)))
        i = j
    return out


def coverage(files, ranges):
    """Per file: (code lines, modelled code lines, excluded code lines, free stretches)."""
    out = {}
    for p, cf in files.items():
        rs = [r for r in ranges.values() if r.file == p]
        modelled = sum(cf.code[i] for r in rs if r.names for i in range(r.first - 1, r.last))
        excluded = sum(cf.code[i] for r in rs if r.excluded for i in range(r.first - 1, r.last))
        out[p] = (sum(cf.code), modelled, excluded, free_stretches(cf, rs))
    return out


# ---------------------------------------------------------------------------------------------
# The generated chapter


def tex_escape(s):
    rep = {'\\': r'\textbackslash{}', '_': r'\_', '&': r'\&', '%': r'\%', '#': r'\#',
           '$': r'\$', '{': r'\{', '}': r'\}', '~': r'\textasciitilde{}',
           '^': r'\textasciicircum{}'}
    out = ''.join(rep.get(c, c) for c in s)
    return re.sub(r'-(?=-)', '-{}', out)  # no en or em dash from `--` or `---`


def tex_code(s):
    """A code span as TeX: \\texttt of the escaped text, with quotes and backticks kept literal
    (plasTeX makes `'` and the backtick typographic even inside \\texttt)."""
    rep = {'-': '-{}', "'": r'\textquotesingle{}', '`': r'\textasciigrave{}'}
    return r'\texttt{' + ''.join(rep.get(ch) or tex_escape(ch) for ch in s) + '}'


def tex_text(s):
    """Docstring text as TeX: escaped, with the Markdown code spans as \\texttt (a run of n
    backticks is closed by the next run of exactly n; an unclosed run is literal text)."""
    runs, out, i, k = list(re.finditer(r'`+', s)), [], 0, 0
    while k < len(runs):
        m = runs[k]
        j = next((j for j in range(k + 1, len(runs)) if len(runs[j].group()) == len(m.group())),
                 None)
        if j is None:
            k += 1
            continue
        code = s[m.end():runs[j].start()]
        if len(code) >= 2 and code[0] == code[-1] == ' ' and code.strip():
            code = code[1:-1]
        out += [tex_escape(s[i:m.start()]), tex_code(code)]
        i, k = runs[j].end(), j + 1
    return ''.join(out) + tex_escape(s[i:])


def csource(p, a, b):
    return rf'\csource{{{p}}}{{{a}}}{{{b}}}'


def render_table(pin, files, ranges, deviations):
    cov = coverage(files, ranges)
    out = ['% Generated by scripts/correspondence.py from the docstrings of the model and',
           '% correspondence/ratpoints.toml. Do not edit: run `scripts/correspondence.py table`.',
           '',
           r'\chapter{The correspondence with the C code}\label{chap:correspondence}',
           '',
           f'The model is checked against ratpoints {tex_escape(pin["tag"])} (commit '
           rf'\texttt{{{pin["commit"][:12]}}}). The C files below are those of the library and '
           '\\texttt{main.c}, whose parts that the command-line program does not mirror are to '
           'be excluded. Every line of '
           'code of them lies in at most one recorded range: a range is either modelled by the '
           'Lean declarations named, or excluded from the model with a reason. Each recorded '
           'range is checked against the text it had when it was reviewed.',
           '',
           r'\begin{center}',
           r'\begin{tabular}{lrrrr}',
           r'file & lines of code & modelled & excluded & not yet recorded \\',
           r'\hline']
    tot = [0, 0, 0]
    for p in files:
        c, m, e, _ = cov[p]
        tot = [tot[0] + c, tot[1] + m, tot[2] + e]
        out.append(rf'\texttt{{{tex_escape(p)}}} & {c} & {m} & {e} & {c - m - e} \\')
    out += [r'\hline',
            rf'total & {tot[0]} & {tot[1]} & {tot[2]} & {tot[0] - tot[1] - tot[2]} \\',
            r'\end{tabular}', r'\end{center}', '']
    for p in files:
        out.append(rf'\section*{{\texttt{{{tex_escape(p)}}}}}')
        rows = [(r.first, 'range', r) for r in ranges.values() if r.file == p]
        rows += [(a, 'free', (a, b, k)) for a, b, k in cov[p][3]]
        if not rows:
            out += ['No line of code.', '']
            continue
        out.append(r'\begin{itemize}')
        for _, kind, x in sorted(rows, key=lambda t: t[0]):
            if kind == 'free':
                a, b, k = x
                out.append(rf'\item {csource(p, a, b)}: not yet recorded ({k} lines of code)')
            elif x.names:
                names = ', '.join(rf'\lname{{{tex_escape(n)}}}' for n in x.names)
                out.append(rf'\item {csource(p, x.first, x.last)}: modelled by {names}')
                for n in x.names:
                    for dv in deviations.get(n, []):
                        out.append(rf'  (deviation of \lname{{{tex_escape(n)}}}: {tex_text(dv)})')
            else:
                out.append(rf'\item {csource(p, x.first, x.last)}: excluded '
                           rf'({tex_escape(x.excluded["kind"])}): {tex_text(x.excluded["reason"])}')
        out += [r'\end{itemize}', '']
    return '\n'.join(out).rstrip('\n') + '\n'


# ---------------------------------------------------------------------------------------------
# The blueprint


# Read from the left, as TeX does: a comment, a `\\verb` span or a control symbol (`\\\\`,
# `\\%`, ...), so that the `%` of `\\\\%` starts a comment and the `%` of `\\%` or `\\verb|%x|`
# does not.
TEX_TOKEN = re.compile(r'%.*|\\verb\*?([^A-Za-z*\s]).*?\1|\\[^A-Za-z]')
VERBATIM = re.compile(r'\\begin\{verbatim\}.*?\\end\{verbatim\}', re.S)


def strip_tex_comments(text):
    """The text without its comments, and with the contents of `verbatim` environments and of
    `\\verb` spans (printed as they are, never commands) blanked."""
    text = VERBATIM.sub(lambda m: '\n' * m.group().count('\n'), text)

    def repl(m):
        s = m.group(0)
        return '' if s[0] == '%' else r'\verb||' if m.group(1) else s
    return '\n'.join(TEX_TOKEN.sub(repl, line) for line in text.split('\n'))


def blueprint_sources():
    return sorted(p for p in BLUEPRINT.rglob('*.tex')
                  if 'generated' not in p.relative_to(BLUEPRINT).parts)


@dataclass
class Blueprint:
    commit: str        # the value of \ratpointscommit, or None
    nodes: list        # (where, names, citations) for each graph node that names declarations
    citations: list    # (where, file, first, last) for every \csource, as written


def read_blueprint():
    texts = {rel(p): strip_tex_comments(p.read_text(encoding='utf-8'))
             for p in blueprint_sources()}
    allt = '\n'.join(texts.values())
    m = re.search(r'\\newcommand\{\\ratpointscommit\}\{([0-9a-f]*)\}', allt)
    opts = re.search(r'\\usepackage\[([^\]]*)\]\{blueprint\}', allt)
    thms = re.search(r'thms=([\w+]+)', opts.group(1)) if opts else None
    envs = thms.group(1).split('+') if thms else GRAPH_ENVS
    node = re.compile(r'\\begin\{(' + '|'.join(map(re.escape, envs)) + r')\}(.*?)\\end\{\1\}',
                      re.S)
    nodes, citations = [], []
    for where, t in texts.items():
        citations += [(where, f, a, b) for f, a, b in CITE.findall(t)]
        for env, body in node.findall(t):
            names = [n.strip() for arg in LEAN.findall(body) for n in arg.split(',') if n.strip()]
            if names:
                label = re.search(r'\\label\{([^}]*)\}', body)
                nodes.append((f'{where}: node {label.group(1) if label else env}', names,
                              CITE.findall(body)))
    return Blueprint(m.group(1) if m else None, nodes, citations)


def valid_citations(bp, files, errors):
    """The C links of the blueprint as (file, first, last), with the malformed ones reported."""
    out = set()
    for where, f, a, b in bp.citations:
        if f not in files:
            errors.append(rf'{where}: \csource names `{f}`, which is not a C file of the record')
        elif not (a.isdigit() and b.isdigit() and 1 <= int(a) <= int(b) <= len(files[f].lines)):
            errors.append(rf'{where}: \csource{{{f}}}{{{a}}}{{{b}}} is not a range of {f}')
        else:
            out.add((f, int(a), int(b)))
    return out


def check_blueprint(pin, bp, decl_ranges, errors):
    if bp.commit is None:
        errors.append(r'the blueprint does not define \ratpointscommit')
    elif bp.commit != pin['commit']:
        errors.append(rf'\ratpointscommit is {bp.commit}, the pin is {pin["commit"]}')
    named = set()
    for where, names, cites in bp.nodes:
        named |= set(names)
        want = {(r.file, r.first, r.last) for n in names for r in decl_ranges.get(n, [])}
        have = {(f, int(a), int(b)) for f, a, b in cites if a.isdigit() and b.isdigit()}
        for f, a, b in sorted(want - have):
            errors.append(rf'{where} lacks \csource{{{f}}}{{{a}}}{{{b}}}, a range of its '
                          rf'declarations')
        for f, a, b in sorted(have - want):
            errors.append(rf'{where} has \csource{{{f}}}{{{a}}}{{{b}}}, which is no range of its '
                          rf'declarations')
    for n in sorted(set(decl_ranges) - named):
        errors.append(rf'{n} models C code but is named by no node of the dependency graph '
                      rf'(\lean{{{n}}})')


# ---------------------------------------------------------------------------------------------
# Driver


def load_decls(args):
    if args.decls:
        return json.loads(Path(args.decls).read_text())
    out = ROOT / '.lake' / 'correspondence-decls.json'
    env = dict(os.environ, CORRESPONDENCE_DECLS=str(out))
    # elan's lake, also when ~/.elan/bin is not on the PATH (as on some CI runners)
    lake = shutil.which('lake') or str(Path.home() / '.elan' / 'bin' / 'lake')
    for cmd in ([lake, 'build', 'RatpointsModel'],
                [lake, 'env', 'lean', 'scripts/Correspondence.lean']):
        r = subprocess.run(cmd, cwd=ROOT, env=env, capture_output=True, text=True)
        if r.returncode != 0:
            sys.exit(f'`{" ".join(cmd)}` failed:\n{r.stdout}{r.stderr}')
    return json.loads(out.read_text())


def check_pin(repo, pin):
    if not re.fullmatch(r'[0-9a-f]{40}', pin.get('commit', '')):
        raise RecordError('the pin needs the full 40-digit commit hash')
    if git(repo, 'cat-file', '-e', f'{pin["commit"]}^{{commit}}').returncode != 0:
        raise RecordError(f'{repo} does not contain the pinned commit {pin["commit"]}')
    r = git(repo, 'rev-parse', '-q', '--verify', f'refs/tags/{pin.get("tag", "")}^{{commit}}')
    if r.returncode == 0 and r.stdout.strip() != pin['commit']:
        raise RecordError(f'tag {pin["tag"]} is {r.stdout.strip()} in {repo}, not the pinned '
                          f'commit {pin["commit"]}')


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('command', nargs='?', default='check',
                    choices=['check', 'lock', 'table', 'coverage', 'pin'])
    ap.add_argument('--repo', type=Path, default=None)
    ap.add_argument('--decls')
    ap.add_argument('--complete', action='store_true')
    ap.add_argument('--field', default='commit')
    args = ap.parse_args(argv)
    record = tomllib.loads(RECORD.read_text())
    pin = record['pin']
    if args.command == 'pin':
        print(pin[args.field])
        return 0
    repo = args.repo or os.environ.get('RATPOINTS_REPO')
    if not repo:
        print('ERROR no clone of ratpoints given: use --repo PATH or set RATPOINTS_REPO')
        return 1
    repo = Path(repo)
    errors = []
    try:
        check_pin(repo, pin)
        files = load_c_files(repo, pin['commit'], record['files']['paths'])
    except RecordError as e:
        print(f'ERROR {e}')
        return 1
    decls = load_decls(args)
    ranges, deviations, decl_ranges = collect_ranges(decls, record, files, errors)
    check_overlaps(ranges, errors)
    bp = read_blueprint()
    citations = valid_citations(bp, files, errors)
    if args.command == 'lock':
        if errors:
            print('\n'.join(f'ERROR {e}' for e in errors))
            return 1
        LOCK.write_text(json.dumps(lock_data(ranges, citations, files, pin['commit']),
                                   indent=2) + '\n')
        print(f'locked {len(ranges)} ranges and {len(citations)} links at {pin["commit"][:12]}')
        return 0
    table = render_table(pin, files, ranges, deviations)
    if args.command == 'table':
        TABLE.parent.mkdir(parents=True, exist_ok=True)
        TABLE.write_text(table)
        print(f'wrote {rel(TABLE)}')
        return 0
    cov = coverage(files, ranges)
    if args.command == 'coverage':
        for p, (c, m, e, free) in cov.items():
            print(f'{p}: {c} lines of code, {m} modelled, {e} excluded, {c - m - e} free')
            for a, b, k in free:
                print(f'  {p}:{a}-{b} ({k} lines of code)')
        return 0
    check_lock(ranges, citations, files, pin['commit'], errors)
    if not TABLE.exists() or TABLE.read_text() != table:
        errors.append(f'{rel(TABLE)} is out of date (run `correspondence.py table`)')
    check_blueprint(pin, bp, decl_ranges, errors)
    free = sum(c - m - e for c, m, e, _ in cov.values())
    if args.complete and free:
        errors.append(f'{free} lines of code lie in no recorded range (see `coverage`)')
    for e in errors:
        print(f'ERROR {e}')
    total = sum(c for c, _, _, _ in cov.values())
    print(f'correspondence: {len(ranges)} ranges, {len(decl_ranges)} declarations, '
          f'{len(citations)} links; {total - free} of {total} lines of code recorded; '
          f'{len(errors)} errors')
    return 1 if errors else 0


if __name__ == '__main__':
    sys.exit(main())

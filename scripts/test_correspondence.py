#!/usr/bin/env python3
"""Tests of scripts/correspondence.py on a throwaway git repository and record.

usage: python3 -m unittest discover -s scripts -p 'test_*.py'
"""
import contextlib
import io
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import correspondence as c  # noqa: E402

C_FILE = """/* header
   comment */
#include <stdio.h>

int f(int x)   /* trailing */
{
  // a line comment
  return x + 1;
}
"""


class CodeLines(unittest.TestCase):
    def test_comments_and_literals(self):
        text = ('a = 1; /* x\n'      # code, then a comment that goes on
                ' still comment */\n'  # comment only
                '/* c */ b = "/*";\n'  # code after a comment; /* inside a string
                's = "//"; // c\n'     # // inside a string
                "q = '\"';\n"          # a quote inside a character literal
                "r = '\\''; /* \n"     # an escaped quote, then a comment that goes on
                '*/\n'
                '#define X 1\n'        # preprocessor lines are code
                '   \n')
        self.assertEqual(c.code_lines(text),
                         [True, False, True, True, True, True, False, True, False])

    def test_fixture(self):
        self.assertEqual(c.code_lines(C_FILE),
                         [False, False, True, False, True, True, False, True, True])

    def test_splices(self):
        text = ('int a; // a comment \\\n'   # a // comment spliced to the next line
                '   that goes on here\n'
                'int b;\n'
                's = "ab\\\n'               # a string spliced to the next line
                'cd";\n')
        self.assertEqual(c.code_lines(text), [True, False, True, True, True])


class ParseDoc(unittest.TestCase):
    def test_items(self):
        errors = []
        doc = ('Summary.\n\nC: `a.c:3-5`, `b.h:7`,\n  `a.c:8-9`.\n\n'
               'Deviation: an `Int` for a `long`.')
        items, devs = c.parse_doc('N', doc, errors)
        self.assertEqual(errors, [])
        self.assertEqual(items, [('a.c', 3, 5), ('b.h', 7, 7), ('a.c', 8, 9)])
        self.assertEqual(devs, ['an `Int` for a `long`.'])

    def test_malformed(self):
        for doc in ('C: a.c:3-5', 'C: `a.c 3-5`', 'C: `a.c:3-`', 'C: `a.c:3-5`\n\nC: `a.c:6`',
                    'Deviation: without a range', 'Summary.\nC: `a.c:1-2`',
                    'C: `a.c:1-2`\n\nText.\nDeviation: inside a paragraph'):
            errors = []
            c.parse_doc('N', doc, errors)
            self.assertTrue(errors, doc)

    def test_no_record(self):
        errors = []
        self.assertEqual(c.parse_doc('N', 'Just prose, mentioning C: in passing.', errors),
                         ([], []))
        self.assertEqual(errors, [])


class TexText(unittest.TestCase):
    def test_code_spans_and_dashes(self):
        self.assertEqual(c.tex_text('`i--` and a--b'), r'\texttt{i-{}-{}} and a-{}-b')
        self.assertEqual(c.tex_text("a ``code with ` and ' inside`` here"),
                         r'a \texttt{code with \textasciigrave{} and \textquotesingle{} inside} '
                         r'here')
        self.assertEqual(c.tex_text('`a_b` `x'), r'\texttt{a\_b} `x')


class EndToEnd(unittest.TestCase):
    """The checks on a temporary C repository with one file, `a.c` (C_FILE), and a temporary
    record, lock and blueprint."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.repo = self.root / 'repo'
        self.repo.mkdir()
        self.git('init', '-q')
        (self.repo / 'a.c').write_text(C_FILE)
        self.commit = self.git_commit('one')
        self.saved = {k: getattr(c, k) for k in ('RECORD', 'LOCK', 'BLUEPRINT', 'TABLE')}
        self.place_blueprint(self.root / 'bp')
        c.RECORD, c.LOCK = self.root / 'ratpoints.toml', self.root / 'lock.json'
        self.decls_path = self.root / 'decls.json'
        self.excluded = ''
        self.decls = []
        self.write_record()
        self.write_blueprint('')

    def tearDown(self):
        for k, v in self.saved.items():
            setattr(c, k, v)
        self.tmp.cleanup()

    def place_blueprint(self, path):
        c.BLUEPRINT = path
        c.TABLE = path / 'generated' / 'correspondence.tex'
        (path / 'macros').mkdir(parents=True, exist_ok=True)

    def git(self, *args):
        return subprocess.run(['git', '-C', str(self.repo), *args], capture_output=True,
                              text=True, check=True).stdout.strip()

    def git_commit(self, msg):
        self.git('add', '-A')
        self.git('-c', 'user.name=t', '-c', 'user.email=t@t', 'commit', '-q', '-m', msg)
        return self.git('rev-parse', 'HEAD')

    def write_record(self, commit=None):
        c.RECORD.write_text(
            f'[pin]\nrepository = "x"\ntag = "v1"\ncommit = "{commit or self.commit}"\n\n'
            f'[files]\npaths = ["a.c"]\n\n{self.excluded}')

    def write_blueprint(self, nodes, commit=None, web=''):
        (c.BLUEPRINT / 'macros' / 'common.tex').write_text(
            '\\newcommand{\\ratpointscommit}{' + (commit or self.commit) + '}\n')
        (c.BLUEPRINT / 'content.tex').write_text(nodes)
        (c.BLUEPRINT / 'web.tex').write_text(web)

    def run_main(self, *args):
        self.decls_path.write_text(json.dumps(self.decls))
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = c.main([*args, '--repo', str(self.repo), '--decls', str(self.decls_path)])
        return code, out.getvalue()

    def decl(self, name, doc, private=False):
        self.decls.append({'name': name, 'private': private, 'module': 'Ratpoints.Model.X',
                           'line': 1, 'doc': doc})

    def lock_and_table(self):
        self.assertEqual(self.run_main('lock')[0], 0)
        self.assertEqual(self.run_main('table')[0], 0)

    def node(self, name, *cites, env='definition'):
        links = ''.join(f'\\csource{{a.c}}{{{a}}}{{{b}}}' for a, b in cites)
        return f'\\begin{{{env}}}\\lean{{{name}}}{links}\\end{{{env}}}\n'

    def test_empty_record(self):
        self.lock_and_table()
        code, out = self.run_main('check')
        self.assertEqual(code, 0, out)
        self.assertIn('0 of 5 lines of code recorded', out)
        code, out = self.run_main('check', '--complete')
        self.assertEqual(code, 1, out)

    def test_complete_record(self):
        self.decl('Ratpoints.Model.f', 'f.\n\nC: `a.c:5-9`')
        self.excluded = ('[[excluded]]\nfile = "a.c"\nlines = "1-3"\nkind = "interface"\n'
                         'reason = "the header"\n')
        self.write_record()
        self.write_blueprint(self.node('Ratpoints.Model.f', (5, 9)))
        self.lock_and_table()
        code, out = self.run_main('check', '--complete')
        self.assertEqual(code, 0, out)
        self.assertIn('5 of 5 lines of code recorded', out)

    def test_unreviewed_range(self):
        self.lock_and_table()
        self.decl('Ratpoints.Model.f', 'C: `a.c:5-9`')
        self.write_blueprint(self.node('Ratpoints.Model.f', (5, 9)))
        self.assertEqual(self.run_main('table')[0], 0)
        code, out = self.run_main('check')
        self.assertEqual(code, 1)
        self.assertIn('a.c:5-9 is not in the lock: review it against Ratpoints.Model.f', out)
        self.assertIn('the blueprint links to a.c:5-9, which is not in the lock', out)

    def test_overlap_bounds_and_files(self):
        self.decl('Ratpoints.Model.f', 'C: `a.c:5-8`')
        self.decl('Ratpoints.Model.g', 'C: `a.c:8-9`, `a.c:9-12`, `b.c:1-2`')
        code, out = self.run_main('check')
        self.assertEqual(code, 1)
        self.assertIn('a.c:5-8 and a.c:8-9 overlap', out)
        self.assertIn('lines 9-12 are not within 1-9 of a.c', out)
        self.assertIn('`b.c` is not one of the C files', out)

    def test_shared_range(self):
        self.decl('Ratpoints.Model.f', 'C: `a.c:5-9`')
        self.decl('Ratpoints.Model.f2', 'f2.\n\nC: `a.c:5-9`')
        self.write_blueprint(self.node('Ratpoints.Model.f, Ratpoints.Model.f2', (5, 9)))
        self.lock_and_table()
        code, out = self.run_main('check')
        self.assertEqual(code, 0, out)

    def test_excluded_and_modelled(self):
        self.decl('Ratpoints.Model.f', 'C: `a.c:5-9`')
        self.excluded = ('[[excluded]]\nfile = "a.c"\nlines = "5-9"\nkind = "threads"\n'
                         'reason = "r"\n[[excluded]]\nfile = "a.c"\nlines = "1-2"\n'
                         'kind = "nonsense"\nreason = ""\n')
        self.write_record()
        code, out = self.run_main('check')
        self.assertEqual(code, 1)
        self.assertIn('a.c:5-9 is both excluded and modelled', out)
        self.assertIn('kind must be one of', out)
        self.assertIn('no reason given', out)

    def test_blueprint_nodes(self):
        self.decl('Ratpoints.Model.f', 'C: `a.c:5-9`')
        self.decl('Ratpoints.Model.g', 'C: `a.c:3`')
        self.write_blueprint(
            '\\begin{lemma}\\label{lem:f}\\lean{Ratpoints.Model.f}'
            '\\csource{a.c}{5}{8}\\end{lemma}\n\\csource{a.c}{4}{20}\n'
            '\\begin{remark}\\lean{Ratpoints.Model.g}\\csource{a.c}{1}{2}\\end{remark}')
        self.assertEqual(self.run_main('lock')[0], 1)  # no lock while a link is malformed
        self.run_main('table')
        code, out = self.run_main('check')
        self.assertEqual(code, 1)
        self.assertIn('node lem:f lacks \\csource{a.c}{5}{9}', out)
        self.assertIn('node lem:f has \\csource{a.c}{5}{8}', out)
        self.assertIn('\\csource{a.c}{4}{20} is not a range of a.c', out)
        # a remark is no node of the graph: it may cite freely, and it names nothing
        self.assertNotIn('a.c}{1}{2}', out)
        self.assertIn('Ratpoints.Model.g models C code but is named by no node', out)

    def test_thms_option(self):
        self.decl('Ratpoints.Model.f', 'C: `a.c:5-9`')
        web = '\\usepackage[showmore, dep_graph, thms=definition+facts]{blueprint}\n'
        self.write_blueprint(self.node('Ratpoints.Model.f', (5, 9), env='facts'), web=web)
        self.lock_and_table()
        code, out = self.run_main('check')
        self.assertEqual(code, 0, out)
        self.write_blueprint(self.node('Ratpoints.Model.f', (5, 9), env='lemma'), web=web)
        code, out = self.run_main('check')
        self.assertIn('Ratpoints.Model.f models C code but is named by no node', out)

    def test_tex_whitespace_and_comments(self):
        self.decl('Ratpoints.Model.f', 'C: `a.c:5-9`')
        self.write_blueprint('\\begin{definition}\\lean {Ratpoints.Model.f}\\csource{a.c}\n'
                             '  {5}{9}, \\\\% \\csource{a.c}{1}{2}\n'
                             '\\csource {a.c}{8}{9}\\end{definition}\n'
                             'See \\csource {a.c}{40}{50}, 50\\% \\csource{a.c}{60}{70}.\n'
                             'Code: \\verb|%x \\csource{a.c}{80}{90}| \\csource{a.c}{91}{92}\n'
                             '\\begin{verbatim}\n\\csource{a.c}{93}{94} % in code\n'
                             '\\end{verbatim}\n')
        self.run_main('table')
        code, out = self.run_main('check')
        self.assertEqual(code, 1)
        self.assertNotIn('lacks', out)
        self.assertNotIn('a.c}{1}{2}', out)  # commented out after \\
        self.assertIn('has \\csource{a.c}{8}{9}', out)
        self.assertIn('\\csource{a.c}{40}{50} is not a range of a.c', out)
        self.assertIn('\\csource{a.c}{60}{70} is not a range', out)  # after \%: live
        self.assertIn('\\csource{a.c}{91}{92} is not a range', out)  # after \verb: live
        self.assertNotIn('{80}{90}', out)                           # inside \verb
        self.assertNotIn('{93}{94}', out)                           # inside verbatim

    def test_owner_change(self):
        self.decl('Ratpoints.Model.f', 'C: `a.c:5-9`')
        self.write_blueprint(self.node('Ratpoints.Model.f', (5, 9)))
        self.lock_and_table()
        self.decls = []
        self.decl('Ratpoints.Model.g', 'C: `a.c:5-9`')
        self.write_blueprint(self.node('Ratpoints.Model.g', (5, 9)))
        self.run_main('table')
        code, out = self.run_main('check')
        self.assertEqual(code, 1)
        self.assertIn('the counterpart of a.c:5-9 changed from Ratpoints.Model.f to '
                      'Ratpoints.Model.g', out)
        self.decls = []
        self.excluded = ('[[excluded]]\nfile = "a.c"\nlines = "5-9"\nkind = "threads"\n'
                         'reason = "r"\n')
        self.write_record()
        self.write_blueprint('')
        self.run_main('table')
        code, out = self.run_main('check')
        self.assertIn('changed from Ratpoints.Model.f to excluded (threads)', out)

    def test_private_and_copied_docstrings(self):
        self.decl('Ratpoints.Model.p', 'C: `a.c:5-9`', private=True)
        self.decl('Ratpoints.Model.q', 'Doc.\n\nC: `a.c:3`')
        self.decl("Ratpoints.Model.«term_+'_»", 'Doc.\n\nC: `a.c:3`')
        code, out = self.run_main('check')
        self.assertEqual(code, 1)
        self.assertIn('Ratpoints.Model.p is private but its docstring records C code', out)
        self.assertIn('have the same docstring with a record', out)

    def test_moved_pin(self):
        self.decl('Ratpoints.Model.f', 'C: `a.c:3-5`')   # the include and the head of f
        self.decl('Ratpoints.Model.g', 'g.\n\nC: `a.c:6-9`')
        self.write_blueprint(self.node('Ratpoints.Model.f', (3, 5)) +
                             self.node('Ratpoints.Model.g', (6, 9)))
        self.lock_and_table()
        # the new release: a line inserted at the top, and the body of g changed
        (self.repo / 'a.c').write_text('/* new */\n' + C_FILE.replace('x + 1', 'x + 2'))
        new = self.git_commit('two')
        self.write_record(new)
        self.decls = []
        self.decl('Ratpoints.Model.f', 'C: `a.c:4-6`')   # both ranges moved by one line
        self.decl('Ratpoints.Model.g', 'g.\n\nC: `a.c:7-10`')
        self.write_blueprint(self.node('Ratpoints.Model.f', (4, 6)) +
                             self.node('Ratpoints.Model.g', (7, 10)), new)
        self.assertEqual(self.run_main('table')[0], 0)
        code, out = self.run_main('check')
        self.assertEqual(code, 1)
        self.assertNotIn('a.c:4-6 is new or changed', out)  # moved, unchanged
        self.assertIn('a.c:7-10 is new or changed since the review', out)
        self.assertIn('link to a.c:7-10 shows a text that no locked link showed', out)
        self.assertNotIn('link to a.c:4-6', out)
        self.assertIn(f'the lock refers to commit {self.commit}', out)
        self.lock_and_table()
        code, out = self.run_main('check')
        self.assertEqual(code, 0, out)

    def test_pin_errors(self):
        self.write_record('0' * 40)
        code, out = self.run_main('check')
        self.assertEqual(code, 1)
        self.assertIn('does not contain the pinned commit', out)
        self.git('tag', 'v1', 'HEAD')
        (self.repo / 'a.c').write_text(C_FILE + '\n')
        new = self.git_commit('two')
        self.write_record(new)
        code, out = self.run_main('check')
        self.assertEqual(code, 1)
        self.assertIn('tag v1 is', out)

    def test_table_mentions_everything(self):
        self.decl('Ratpoints.Model.f_g', 'C: `a.c:5-6`\n\nDeviation: an `Int` for a `long`.')
        self.excluded = ('[[excluded]]\nfile = "a.c"\nlines = "1-3"\nkind = "interface"\n'
                         'reason = "the `stdio` header"\n')
        self.write_record()
        self.run_main('table')
        t = c.TABLE.read_text()
        self.assertIn('\\csource{a.c}{5}{6}: modelled by \\lname{Ratpoints.Model.f\\_g}', t)
        self.assertIn('deviation of \\lname{Ratpoints.Model.f\\_g}: an \\texttt{Int} for a '
                      '\\texttt{long}.', t)
        self.assertIn('excluded (interface): the \\texttt{stdio} header', t)
        self.assertIn('\\csource{a.c}{8}{9}: not yet recorded (2 lines of code)', t)

    def test_checkout_below_a_directory_named_generated(self):
        self.place_blueprint(self.root / 'generated' / 'clone' / 'bp')
        self.decl('Ratpoints.Model.f', 'C: `a.c:5-9`')
        self.write_blueprint(self.node('Ratpoints.Model.f', (5, 9)))
        self.lock_and_table()
        code, out = self.run_main('check')
        self.assertEqual(code, 0, out)


if __name__ == '__main__':
    unittest.main()

# The correspondence with the C code

Lean has no semantics of C, so the link between the model in `Ratpoints/Model` and the C code of
`ratpoints` is a record of which Lean declaration models which lines of C, checked by
`scripts/correspondence.py`, together with the differential tests.

## The pin

Every line number refers to one commit of `ratpoints`, the pin in
[`ratpoints.toml`](ratpoints.toml): release 3.2.0, commit `1763c62`. The project follows the
releases of `ratpoints`, and future changes to the C code come, as far as possible, with their
soundness proofs in the model. The C code is read with `git show <commit>:<file>`, so the working
tree of the C repository may be at any commit.

## The ranges

The record covers the files listed in `ratpoints.toml`: the library and `main.c`. Every line of
code of them (a line that is not blank and not only a comment) lies in exactly one recorded range,
which is either

- **modelled**: the docstring of a public declaration of the model names it in a paragraph of its
  own,

  ```lean
  /-- The helper `mod` of the C code, the remainder of the `long` `a` modulo the `long` `b > 0`: …

  C: `find_points.c:490-505`, `sift.c:370-389`

  Deviation: one definition for the two copies of the function, in `find_points.c` and in `sift.c`,
  …; integers for the `long`s, with the obligations that the values it computes stay in the range
  of a `long` stated as lemmas: … -/
  def modLong (a b : Int) : Int :=
  ```

  with one or more items `` `file:first-last` `` (or `` `file:line` ``) separated by commas. A
  range cited by several declarations (the two arms of the first stage of the sieve, say, which
  share lines of the C code) is one range with several names. An optional `Deviation:` paragraph
  says where the model departs from the C code (an `Int` or a `Nat` for a `long`, with the
  obligations of its range as lemmas, a 64-bit word for the vector code, an index for a pointer,
  the bits of a double with a model function for each operation on it, the sequential order for
  the threads). A private declaration cannot carry the record (a blueprint node cannot name it),
  and `check` reports one that does; a docstring that `@[inherit_doc]` lends to a notation or an
  alias is not the declaration's own and makes no record; or

- **excluded**: an `[[excluded]]` table of `ratpoints.toml` gives the range, a kind (threads,
  memory, instrumentation, interface or other) and the reason.

Two different ranges must not overlap. When a declaration calls another that models part of its
C code, it cites the lines around that part, not the whole function.

## The checks

`scripts/correspondence.py check --complete` (run in CI and in the checks of each commit) builds
the model, reads the docstrings of its declarations with `scripts/Correspondence.lean`, and checks

- that the pinned commit exists (and the tag, where the repository has it, points to it), and
  that every range lies in a listed file and within its lines;
- that no line lies in two different ranges;
- that every range was reviewed with its present text and its present counterpart, and every C
  link of the blueprint with its present text: `lock.json` holds, for each range, the SHA-256 of
  its text at the pin and its owners (the declarations that model it, or its exclusion), and the
  hash of the text of each link; `scripts/correspondence.py lock` writes it after the review of
  what `check` reported. A new range, a range whose counterpart changed (to another declaration,
  from an exclusion to a declaration, or a declaration added to a shared range) and a new link are
  reported until they are locked;
- that the generated blueprint chapter `blueprint/src/generated/correspondence.tex` (the table
  from C to Lean, which also lists any lines of code that no range records) is up to date
  (`scripts/correspondence.py table` regenerates it);
- that the blueprint's `\ratpointscommit` is the pin, that every `\csource{file}{first}{last}`
  is a range of a listed file, and that every C link of a node of the dependency graph (the
  environments of the `thms=` option of the blueprint package in `web.tex`, by default
  definition, lemma, proposition, theorem and corollary) that names declarations with
  `\lean{…}` is a range of one of the model declarations it names. A node need not cite every
  range of its declarations, and a model declaration need not be named by a node: the generated
  chapter lists every range with its owners. Prose and other environments, such as remarks, may
  link to any range;
- with `--complete`, that every line of code lies in a range: every line of code of the files is
  recorded, and a line that no declaration models and no exclusion covers fails the check.
  `scripts/correspondence.py coverage` lists the stretches not recorded, as after a move of the pin
  to a release with new code; without `--complete` the check ignores them.

The script needs a clone of `ratpoints` that contains the pin, given by `--repo PATH` or the
environment variable `RATPOINTS_REPO`.

## Moving the pin

When the project moves to another commit of `ratpoints`, the line numbers move with the C code:

1. `scripts/correspondence.py repin <commit>` sets the new commit and its tag in `ratpoints.toml`
   (the tag is that of `--tag`, or the name that `git describe --tags` gives the commit) and
   `\ratpointscommit` in `blueprint/src/macros/common.tex`, and carries every line reference of
   the tracked files to the lines at the new commit, through `git diff -U0 <old> <new>`: the items
   `` `file:first-last` `` and `` `file:line` `` wherever they stand (the `C:` paragraphs, and
   prose that cites a line of the C code, which therefore always names the file in this form), the
   `lines` of the excluded ranges, and the `\csource` links of the blueprint. Lines inserted next
   to a range belong to neither of its neighbours. The command reports the references whose lines
   no longer have the same text (`CHANGED`) and those of which no line is left (`LOST`, rewritten
   to line 0, which no check accepts), the lines of Lean that the new numbers make longer than 100
   columns, and the places that still name the old commit in words. With `--dry-run` it reports
   and writes nothing;
2. run `scripts/correspondence.py table` and then `check`: since the lock still names the old
   commit, `check` accepts a range whose text and owners some locked range has (it moved but did
   not change) and a link whose text some locked link has, and reports exactly the others, which
   are new or changed;
3. review those against their Lean counterparts (and fix the model where the C code changed),
   with the changed references in prose, which only `repin` reports; record the new lines of
   code, which `scripts/correspondence.py coverage` lists, in the model or as exclusions; and then
   run `scripts/correspondence.py lock`.

Until the last step `check` fails, naming the lock's old commit.

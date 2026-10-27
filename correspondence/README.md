# The correspondence with the C code

Lean has no semantics of C, so the link between the model in `Ratpoints/Model` and the C code of
ratpoints is a record of which Lean declaration models which lines of C, checked by
`scripts/correspondence.py`, together with the differential tests.

## The pin

Every line number refers to one commit of ratpoints, the pin in
[`ratpoints.toml`](ratpoints.toml): release 3.1.1, commit `1a99853`. The project moves to each
ratpoints release, and a new optimization of the C code comes, as far as possible, with its
soundness proof in the model. The C code is read with `git show <commit>:<file>`, so the working tree of the C
repository may be at any commit.

## The ranges

The record covers the files listed in `ratpoints.toml`: the library and `main.c`. Every line of
code of them (a line that is not blank and not only a comment) lies in exactly one recorded range,
which is either

- **modelled**: the docstring of a public declaration of the model names it in a paragraph of its
  own,

  ```lean
  /-- Least non-negative residue of `a` modulo `b`, by the ladder of conditional subtractions
  of the C code.

  C: `sift.c:369-389`

  Deviation: an `Int` for a `long`; the range of the C type is a hypothesis of the contract. -/
  ```

  with one or more items `` `file:first-last` `` (or `` `file:line` ``) separated by commas. A
  range cited by several declarations (a component and its faithful replacement, say) is one range
  with several names. An optional `Deviation:` paragraph says where the model departs from the C
  code (an `Int` for a `long`, exact arithmetic for a double, an index for a pointer, the
  sequential order for the threads, a C defect not yet fixed). A private declaration cannot carry
  the record (a blueprint node cannot name it), and `check` reports one that does; a docstring
  that `@[inherit_doc]` lends to a notation or an alias is not the declaration's own and makes no
  record; or

- **excluded**: an `[[excluded]]` table of `ratpoints.toml` gives the range, a kind (parameter
  selection, threads, memory, instrumentation, interface, other) and the reason.

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
  from C to Lean, with the lines not yet recorded) is up to date (`scripts/correspondence.py
  table` regenerates it);
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

The script needs a clone of ratpoints that contains the pin, given by `--repo PATH` or the
environment variable `RATPOINTS_REPO`.

## Moving the pin

When the project moves to a new ratpoints release, the line numbers move with the C code:

1. set the new commit and tag in `ratpoints.toml` and `\ratpointscommit` in
   `blueprint/src/macros/common.tex`;
2. move every range, in the docstrings and in `ratpoints.toml`, and every `\csource` link of the
   blueprint (nodes, remarks and prose alike) to its lines at the new commit
   (`git diff <old> <new> -- <file>` shows how the lines moved);
3. run `scripts/correspondence.py table` and then `check`: since the lock still names the old
   commit, `check` accepts a range whose text and owners some locked range has (it moved but did
   not change) and a link whose text some locked link has, and reports exactly the others, which
   are new or changed;
4. review those against their Lean counterparts (and fix the model where the C code changed),
   record the new lines of code, which `scripts/correspondence.py coverage` lists, in the model or
   as exclusions, and then run `scripts/correspondence.py lock`.

Until the last step `check` fails, naming the lock's old commit.

# Comparator verification harness

This directory lets [Comparator](https://github.com/leanprover/comparator), "a trustworthy judge
for Lean proofs", certify the main theorems of the project independently of the repository's own
build, using only the permitted axioms (`propext`, `Quot.sound`, `Classical.choice`).

## What is checked

- [`Challenge.lean`](Challenge.lean) may import only Mathlib and the model (`Ratpoints.Model`).
  It restates the specification verbatim (`degree`, `binaryForm` and `IsPoint`; `binaryFormPoly`
  joins with the refusal theorem in stage D, and `points` stays out, as the blueprint explains)
  and states the main theorems with `sorry`. The main theorems speak about the model's
  `findPoints` (and, in stage B, the brute-force reference), which the challenge imports: the
  model is trusted in the sense that it is the code the executable runs, and nothing else. The
  specification, by contrast, is reproduced in the challenge, so a solution whose library changed
  it is rejected.
- [`Solution.lean`](Solution.lean) imports the library and proves the same statements by its
  theorems.

Comparator builds both modules (the solution in a sandbox), exports them with `lean4export`, and
checks that each challenge theorem in the solution

1. proves the **same statement** as in the challenge, comparing the full bodies (not just the
   types) of every definition the statement refers to, so the specification of the library must
   be the challenge's restatement exactly;
2. uses no axioms beyond `permitted_axioms`; in particular a `native_decide` or `bv_decide`
   anywhere below a main theorem makes it fail, and `scripts/check_layout.py` forbids both in the
   project;
3. is accepted by the Lean kernel.

The statements come in stage by stage, as the blueprint describes them: the theorems of stage B
(the brute-force reference finds exactly the points, without duplicates), the membership and
no-duplicates theorems for `findPoints` together with the well-formedness of the default
parameters, which rules out a `P.WF` that nothing satisfies (stage C1), and the refusal theorem
(stage D). The theorems of stage B are in: `challenges.json` lists
`challenge_mem_bruteForce_iff` and `challenge_nodup_bruteForce`, and Comparator accepted the
solution on 2026-10-09.

## Running

Prerequisites (see the Comparator README): a built `comparator` binary, `landrun` built from its
`main` branch, and a `lean4export` built at **the same Lean version as this project** (it loads the
project's `.olean`s; a mismatch fails with `incompatible header`), i.e. the tag matching
`lean-toolchain`. Point Comparator at them via `COMPARATOR_BIN`, `COMPARATOR_LEAN4EXPORT` and
`COMPARATOR_LANDRUN`, or put them on `PATH`. Rebuild `lean4export` at every change of the
toolchain.

From the repository root, inside the `systemd-run` guard that the Comparator README asks for:

```bash
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pipe --wait \
  -E PATH="$PATH" -E HOME="$HOME" --working-directory "$(pwd)" -- scripts/run-comparator.sh
```

The script builds the library and runs `lake env comparator comparator/challenges.json`; it
prints `Your solution is okay!` and exits 0 when the check passes.

On 2026-10-09 the whole pipeline (landrun, `lean4export` v4.35.0-rc4, the kernel check) was
tested on a copy of this layout, with a Mathlib-importing challenge over a model
definition: a faithful solution passed, and a solution whose library defined the restated
predicate differently (equal in meaning, different as a term) was rejected with `Const does not
match between challenge and target`.

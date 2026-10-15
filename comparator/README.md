# Comparator verification harness

This directory lets [Comparator](https://github.com/leanprover/comparator), "a trustworthy judge
for Lean proofs", certify the main theorems of the project independently of the repository's own
build, using only the permitted axioms (`propext`, `Quot.sound`, `Classical.choice`).

## What is checked

- [`Challenge.lean`](Challenge.lean) may import only Mathlib and the model (`Ratpoints.Model`). It
  restates the specification verbatim (`degree`, `binaryForm`, `IsPoint`, and `binaryFormPoly`,
  which the refusal theorems of stage D speak about; `points` stays out, as the blueprint explains)
  and states the main theorems with `sorry`. The main theorems speak about the model's `findPoints`
  (and, in stage B, the brute-force reference), which the challenge imports with `Options`,
  `Params`, `Params.WF`, `SieveOptions`, `sieveParams` and `maxDegree`: the model is trusted in the
  sense that it is the code the executable runs, and nothing else, and a definition of the model,
  which elaborates without Mathlib, is never restated. The specification, by contrast, is
  reproduced in the challenge, so a solution whose library changed it is rejected. The challenge
  imports exactly the public imports of the specification (`Ratpoints/Spec/Basic.lean`), among them
  `Mathlib.Algebra.Squarefree.Basic` for `Squarefree`, so that the restated definitions elaborate to
  the same terms as there.
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

The statements come in stage by stage, as the blueprint describes them: the theorems of stage B (the
brute-force reference finds exactly the points, without duplicates); from stage C1 on, the
membership and no-duplicates theorems for `findPoints` for well-formed parameters, since stage D for
every value of the options of `findPoints`, and the well-formedness of every parameter set that the
options of the program give, which rules out a `P.WF` that nothing satisfies; and, since stage D,
the two refusal theorems: with the Sturm step on, `findPoints` refuses exactly the inputs with fewer
than two or more than `maxDegree + 1` coefficients, the height bound `0` or one of `2 ^ 63` or more,
which is not a `long`, and the binary forms that are not squarefree, and with it off exactly what
the program refuses under `-s`, so that a `findPoints` that refuses every input, with or without the
Sturm step, is ruled out. They replace the refusal theorem of stage C1, which had only the first
three disjuncts. `challenges.json` lists `challenge_mem_bruteForce_iff` and
`challenge_nodup_bruteForce`, which Comparator accepted on 2026-10-09;
`challenge_mem_iff_isPoint_of_findPoints_eq_ok` and `challenge_nodup_of_findPoints_eq_ok`, which
Comparator accepted on 2026-10-10 in their form of stage C1, without the options, and
`challenge_wf_sieveParams`, which it accepted on the same day; and
`challenge_exists_findPoints_eq_error_iff_of_sturm_nonneg` and
`challenge_exists_findPoints_eq_error_iff_of_sturm_neg`, the refusal theorems of stage D. Comparator
accepted all seven, the two main theorems with the options among them, on 2026-10-11, again on the
model of stage E on 2026-10-12, with the parameters of sub-stage F1, whose well-formedness
admits composite moduli, on 2026-10-13, with the refusal of the heights that are not `long`s, which
the refusal theorems state as `2 ^ 63 ≤ H`, and the cut points of sub-stage F2, on 2026-10-14, and
with the packing of the numerators of sub-stage F3 on 2026-10-15.

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

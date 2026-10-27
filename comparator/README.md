# Comparator verification harness

This directory lets [Comparator](https://github.com/leanprover/comparator), "a trustworthy judge
for Lean proofs", built into Lake as `lake comparator` (Lean v4.35.0 and later), certify the main
theorems of the project independently of the repository's own build, using only the permitted
axioms (`propext`, `Quot.sound`, `Classical.choice`).

## What is checked

- [`Challenge.lean`](Challenge.lean) may import only Mathlib and the model (`Ratpoints.Model`);
  `scripts/check_layout.py` checks this. It restates the specification verbatim: of
  `Ratpoints/Spec/Basic.lean`, `degree`, `binaryForm`, `binaryFormPoly` (the binary form over `ℚ`
  that the refusal theorems speak about), `IsNormalizedPair` and `IsPoint` with their decidability
  (`points`, the finite set of the points, stays out, since no statement mentions it); all of
  `Ratpoints/Spec/Order.lean`, the order of the points (`searchedPoly`, `FactorsByTrialDivision`
  with its decidability, `binaryDivisors`, `searchDenominators`, `pointsWithDen`,
  `orderedPoints`); all of `Ratpoints/Spec/Region.lean`, the search region (`IsNaN`,
  `doubleValue`, `AreSearchIntervals`, `IntervalsWF`, `InIntervals`, `InRegion`, `IsFullBox` with
  their decidability, and `denominatorBound`); and `Ratpoints/Spec/Sturm.lean`, Sturm's theorem as
  a proposition (`SturmTheorem`), which the statements with the Sturm step on assume. It states
  the main theorems with `sorry`.
- [`Solution.lean`](Solution.lean) imports the library and proves the same statements by its
  theorems.

The main theorems speak about the model's `findPoints`, `findPointsWith` (with its trailing print
argument at its default, the channel that prints nothing) and the brute-force reference
`bruteForce`, which the challenge imports with `Options`, the doubles `Double` of its search
intervals, `SieveOptions`, `maxDegree`, `maxDivisors`, the result `Outcome` of `findPointsWith`
(whose fields `info` and `total` the protocol reads), and the callback's `Answer` and `Delivery`
with the reference of the delivery `Delivery.deliver`. The model is trusted in the sense that it
is the code the executable runs, and nothing else, and a definition of the model, which
elaborates without Mathlib, is never restated. The specification, by contrast, is reproduced in
the challenge, so a solution whose library changed it is rejected. Of Mathlib, the challenge
imports exactly the Mathlib modules among the public imports of the files of the specification,
among them `Mathlib.Algebra.Squarefree.Basic` for `Squarefree`, `Mathlib.Data.Nat.Factors` for the
prime factors, `Mathlib.Order.WithBotTop` for the values of the doubles, and
`Mathlib.Algebra.Polynomial.Sturm.Sequence` and `Mathlib.Data.List.SignVariations` for Sturm's
theorem, so that the restated definitions elaborate to the same terms as there.

## The eleven statements

`challenges.json` lists eleven statements. They hold for every coefficient list `c`, height bound
`H`, options of the search `o : Options` and options of the sieve `s : SieveOptions`, with no
hypothesis on `s`, from which and from the curve the search chooses its moduli:

- the brute-force reference (`challenge_mem_bruteForce_iff`, `challenge_nodup_bruteForce`):
  `bruteForce c H` lists exactly the points of height at most `H` (`IsPoint`), each once;
- membership (`challenge_mem_iff_isPoint_of_findPoints_eq_ok`): with the exact check on
  (`o.noCheck = false`) and assuming Sturm's theorem when the Sturm step is on
  (`0 ≤ o.sturm → SturmTheorem`), a triple lies in the list of `findPoints` exactly when it is a
  point, with `0 ≤ y` when `o.noY` is set, in the search region (`InRegion`, over the values of the
  ends of the search intervals, `doubleValue`, and the range of the denominators);
- no duplicates (`challenge_nodup_of_findPoints_eq_ok`), for every option, the exact check off
  among them;
- the refusals (`challenge_exists_findPoints_eq_error_iff_of_sturm_nonneg` and
  `challenge_exists_findPoints_eq_error_iff_of_sturm_neg`): with the Sturm step on, `findPoints`
  refuses exactly the inputs with fewer than two or more than `maxDegree + 1` coefficients, the
  height bound `0` or one of `2 ^ 63` or more, which is not a `long`, the binary forms
  `binaryFormPoly c` that are not squarefree, and search intervals that are not well formed
  (`IntervalsWF`); with it off, exactly what the program refuses under `-s`: the same bounds on the
  coefficients and the height, the lists whose degree lies two or more below the even degree of
  their binary form (`degree c + 2 ≤ 2 * (c.length / 2)`), which is then divisible by `z²`, for
  even degree `c₀ = c₁ = 0` when the reversal is allowed and the search region is the whole box
  (`IsFullBox`), and search intervals that are not well formed; so a `findPoints` that refuses
  every input, with or without the Sturm step, is ruled out;
- the order (`challenge_eq_orderedPoints_of_findPoints_eq_ok`): under the hypotheses of
  membership, the list is that of `orderedPoints`, the points in the order of ratpoints (with the
  bound `maxDivisors` of the model on the number of divisors, the reversal only for the whole box
  and the largest denominator `denominatorBound`), filtered by `o.noY` and the search region;
- three statements with the exact check off (`o.noCheck = true`): every element `(x, y, z)` of the
  list has `y = 0`, a normalized pair `(x, z)` of height at most `H` (`IsNormalizedPair`) and lies
  in the search region (`challenge_isNormalizedPair_of_mem_of_findPoints_eq_ok_of_noCheck`); every
  point `(x, y, z)` in the search region gives the element `(x, 0, z)`, assuming Sturm's theorem
  when the Sturm step is on (`challenge_mem_of_isPoint_of_findPoints_eq_ok_of_noCheck`); and the
  list of the same search with the exact check on and `o.noY` set, with `y` replaced by `0`, is a
  sublist of it (`challenge_map_sublist_of_findPoints_eq_ok_of_noCheck`);
- the protocol of the delivery (`challenge_map_findPointsWith_eq_map_findPoints`): the search with
  a callback refuses what `findPoints` refuses and otherwise returns the data of the callback and
  the count of `Delivery.deliver` of the list of `findPoints` to the callback, its calls for the
  points in their order up to and including the first that stops the search.

On 2026-10-27 `lake comparator --paranoid` accepted all eleven statements, with Lean's kernel and
the five external checkers.

Comparator certifies these statements and their proofs; it does not certify that the executable
`ratpoints-lean` runs the model, nor the link between the model and the C code, which is a record
and a test (`correspondence/README.md`). The theorems on what the program prints, on the coverage
of the Sturm step and on the blocks of the run are proved in the library but are not among the
statements.

## How Comparator checks them

`lake comparator` builds and exports both modules inside a `bubblewrap` sandbox (it never loads
the project's `.olean` files into its own process) and checks that each challenge theorem in the
solution

1. proves the **same statement** as in the challenge, comparing the full bodies (not just the
   types) of every definition the statement refers to, so the specification of the library must
   be the challenge's restatement exactly;
2. uses no axioms beyond `permitted_axioms`; in particular a `native_decide` or `bv_decide`
   anywhere below a main theorem makes it fail, and `scripts/check_layout.py` forbids both in the
   project;
3. is accepted by the Lean kernel and, with `--paranoid`, by every external checker bundled with
   Lean (`leanchecker-paranoid`, `lean4lean`, `nanoda`, `con-leche`, `con-ron`).

## Running

Run from the repository root; the only prerequisite besides Lean is `bubblewrap` (`bwrap`) with
unprivileged user namespaces (or installed setuid root):

```bash
scripts/run-comparator.sh --paranoid    # the certification: Lean's kernel and the external checkers
scripts/run-comparator.sh               # Lean's kernel only
```

The script builds the library (`lake build RatpointsModel Ratpoints`) and runs `lake comparator
--config comparator/challenges.json` with the options given. Exit code `0` (and `Your solution is
okay!`) means that the check passed, `1` that it was rejected, `2` that it could not start (no
`bwrap`, no `lake-manifest.json`, a missing or malformed configuration). The library is built
first, outside the sandbox, where the caller's environment applies (the sandbox clears it but for
`PATH`), so that the sandboxed builds of `Challenge` and `Solution` find it current and only replay
it. `lake comparator` writes the exports into the temporary directory of the system (`TMPDIR`).

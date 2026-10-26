# Comparator verification harness

This directory lets [Comparator](https://github.com/leanprover/comparator), "a trustworthy judge
for Lean proofs", built into Lake as `lake comparator` since Lean v4.35.0, certify the main
theorems of the project independently of the repository's own build, using only the permitted
axioms (`propext`, `Quot.sound`, `Classical.choice`).

## What is checked

- [`Challenge.lean`](Challenge.lean) may import only Mathlib and the model (`Ratpoints.Model`). It
  restates the specification verbatim: of `Ratpoints/Spec/Basic.lean` `degree`, `binaryForm`,
  `IsPoint` with its decidability, and `binaryFormPoly`, which the refusal theorems of stage D speak
  about (`points` stays out, as the blueprint explains); since stage G, all of
  `Ratpoints/Spec/Order.lean`, the order of the points (`searchedPoly`, `FactorsByTrialDivision`
  with its decidability, `binaryDivisors`, `searchDenominators`, `pointsWithDen`, `orderedPoints`);
  and since stage H all of `Ratpoints/Spec/Region.lean`, the search region (`IsNaN`, `doubleValue`,
  `AreSearchIntervals`, `IntervalsWF`, `InRegion`, `IsFullBox` with their decidability, and
  `denominatorBound`), and `Ratpoints/Spec/Sturm.lean`, Sturm's theorem as a proposition
  (`SturmTheorem`), which the statements with the Sturm step on assume. It states the main
  theorems with `sorry`. The main theorems speak about the model's `findPoints` and, since stage G,
  `findPointsWith`, since stage I with its trailing print argument at its default, the channel that
  prints nothing (and, in stage B, the brute-force reference), which the challenge imports with
  `Options`, the doubles `Double` of its search intervals, `SieveOptions`, `maxDegree`,
  `maxDivisors`, the result `Outcome` of `findPointsWith` (whose fields `info` and `total` the
  protocol reads), and the callback's `Answer` and `Delivery` with the reference of the delivery
  `Delivery.deliver` (until stage H also `Params`, `Params.WF` and `sieveParams`, which the
  statements of stage I no longer mention): the model is trusted in the sense that it is the
  code the executable runs, and nothing else, and a definition of the model, which elaborates
  without Mathlib, is never restated. The specification, by contrast, is reproduced in the
  challenge, so a solution whose library changed it is rejected. Of Mathlib, the challenge imports
  exactly the Mathlib modules among the public imports of the files of the specification
  (`Ratpoints/Spec/Basic.lean`, `Ratpoints/Spec/Order.lean`, `Ratpoints/Spec/Region.lean` and
  `Ratpoints/Spec/Sturm.lean`), among them `Mathlib.Algebra.Squarefree.Basic` for `Squarefree`,
  `Mathlib.Data.Nat.Factors` for the prime factors, `Mathlib.Order.WithBotTop` for the values of
  the doubles, and `Mathlib.Algebra.Polynomial.Sturm.Sequence` and
  `Mathlib.Data.List.SignVariations` for Sturm's theorem, so that the restated definitions elaborate
  to the same terms as there.
- [`Solution.lean`](Solution.lean) imports the library and proves the same statements by its
  theorems.

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
the refusal theorems state as `2 ^ 63 ≤ H`, and the cut points of sub-stage F2, on 2026-10-14, with
the packing of the numerators of sub-stage F3 on 2026-10-15, and with the chunked first stage and
the rows of sub-stage F4 on 2026-10-16; on Lean and Mathlib v4.35.0, `lake comparator --paranoid`
accepted all seven on the same day, with Lean's kernel and the five external checkers.

Stage G restates the membership theorem for the options of the output: with the exact check on
(`o.noCheck = false`), `p ∈ L` exactly when `p` is a point and, under `o.noY`, `0 ≤ y`; no
duplicates keeps its text and now holds for the options of the output too, the exact check off among
them. With the exact check off (`o.noCheck = true`), three statements, which `challenges.json`
lists, say what the list holds: every element is `(x, 0, z)` for a normalized pair `(x, z)` of
height at most `H` (`challenge_exists_eq_of_mem_of_findPoints_eq_ok_of_noCheck`), every point
`(x, y, z)` of height at most `H` gives the element `(x, 0, z)`
(`challenge_mem_of_isPoint_of_findPoints_eq_ok_of_noCheck`), and the list of the same search with
the exact check on and `o.noY` set, with `y` replaced by `0`, is a sublist of it
(`challenge_map_sublist_of_findPoints_eq_ok_of_noCheck`). It adds the protocol of the delivery,
`challenge_map_findPointsWith_eq_map_findPoints`, which `challenges.json` lists as well: the search
with a callback refuses what `findPoints` refuses and otherwise returns the data of the callback and
the count of `Delivery.deliver` of the list of `findPoints` to the callback, its calls for the
points in their order up to and including the first that stops the search. And it adds the order
theorem, `challenge_eq_orderedPoints_of_findPoints_eq_ok`, which `challenges.json` lists too: with
the exact check on, the list of `findPoints` is that of `orderedPoints`, the points in the order of
ratpoints, with the model's bound `maxDivisors` on the number of divisors, filtered by `o.noY`. So
`challenges.json` lists twelve statements, five of them new with stage G. All five, like the
membership and no-duplicates theorems, are for well-formed parameters (`P.WF`). On 2026-10-17
`lake comparator --paranoid` accepted all twelve, with Lean's kernel and the five external checkers.

Stage H restates six statements for the search region of the options, the search intervals over the
values of their ends (`doubleValue`) and the range of the denominators: membership holds for the
points in the search region (`InRegion`), the order theorem filters `orderedPoints` by it, with the
reversal only for the whole box (`IsFullBox`) and the largest denominator `denominatorBound`, both
assuming Sturm's theorem when the Sturm step is on (`0 ≤ o.sturm → SturmTheorem`); under the exact
check off, every element lies in the search region, and every point in it gives its element, the
latter assuming Sturm's theorem when the Sturm step is on; and both refusal theorems add the refusal
of search intervals that are not well formed (`IntervalsWF`), the refusal of the reversal check
without the Sturm step only for the whole box. No duplicates, the sublist under the exact check off,
the protocol, the brute-force reference and the well-formedness of the parameters of the program
keep their text. So `challenges.json` lists the same twelve statements; the six changes came in with
the theorems that prove them, each checked by Comparator then, and on 2026-10-18
`lake comparator --paranoid` accepted all twelve in their form of stage H, with Lean's kernel and
the five external checkers.

Stage I takes the options of the sieve with no hypothesis, in place of parameters and their
well-formedness, which are internal to the search: the membership, no-duplicates and order theorems,
the three statements under the exact check off and the protocol take `(s : SieveOptions)` in place
of `(P : Params) (hP : P.WF)`, and the two refusal theorems `s` in place of `P`; the theorem on the
well-formedness of the parameters that the options of the program give, `challenge_wf_sieveParams`,
is gone, with the parameters it spoke about. So `challenges.json` lists eleven statements; the two
of the brute-force reference keep their text. On 2026-10-25 `lake comparator --paranoid` accepted
all eleven in their form of stage I, with Lean's kernel and the five external checkers, and on
2026-10-25 `lake comparator` accepted them again with the choice of the moduli by the curve and the
run over the blocks with the correction of the moduli between them, which change their proofs and
not their text.

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

Until 2026-10-16 the check ran on the external tools, a separately built `comparator` binary,
`landrun` and a `lean4export` built at the project's Lean version, inside a `systemd-run` guard,
through an earlier version of the wrapper (see the history of `scripts/run-comparator.sh`);
`lake comparator` replaces all three. On 2026-10-16 both accepted the seven statements on the
same commit, on Lean and Mathlib v4.35.0, in about a minute and a half each, and `lake comparator
--paranoid` accepted them with all six kernels in four and a half minutes.

On 2026-10-09 the whole pipeline of the external tools (landrun, `lean4export` v4.35.0-rc4, the
kernel check) was tested on a copy of this layout, with a Mathlib-importing challenge over a model
definition: a faithful solution passed, and a solution whose library defined the restated predicate
differently (equal in meaning, different as a term) was rejected with `Const does not match between
challenge and target`.

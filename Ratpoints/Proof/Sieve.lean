/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.Sieve
public import Std.WP

import Std.Tactic.Do

/-!
# The contracts of the plain sieve

The contracts of the loops of the plain sieve of one denominator, the reference of the bit arrays of
words, as `@[spec]` theorems proved with `vcgen`, the program logic of Lean core, with loop
invariants that are named definitions.

## Main statements

* `Ratpoints.Sieve.sieveDen_spec`: entry `i` of the sieve of a denominator `b` is the survivor test
  `Ratpoints.Sieve.survives` of the numerator `i - H`.
* `Ratpoints.Sieve.checkDen_spec`: if entry `i` of the array is `keep (i - H)` for every `i`, the
  survivors of the array give the points of the brute-force reference over `b` and the numerators
  that pass `keep`.

## Implementation notes

The file uses Lean core and `Std` only, so that the `grind` calls of the proofs see only the lemmas
of core, untouched by the updates of Mathlib. The lemmas on the brute-force reference that the
contracts need, `Ratpoints.BruteForce.pointsOfDen_nil`, `Ratpoints.BruteForce.pointsOfDen_append`,
`Ratpoints.BruteForce.pointsOfDen_singleton`, `Ratpoints.BruteForce.pointsOfDen_filter` and
`Ratpoints.BruteForce.map_toList_range_eq_numerators`, are stated here, without Mathlib, rather than
with the other lemmas on the reference in `Ratpoints.Proof.BruteForce`.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace Ratpoints

namespace BruteForce

@[simp]
theorem pointsOfDen_nil (c : List Int) (d : Nat) (z : Int) : pointsOfDen c d z [] = [] := rfl

theorem pointsOfDen_append (c : List Int) (d : Nat) (z : Int) (xs ys : List Int) :
    pointsOfDen c d z (xs ++ ys) = pointsOfDen c d z xs ++ pointsOfDen c d z ys := by
  simp [pointsOfDen]

theorem pointsOfDen_singleton (c : List Int) (d : Nat) (z x : Int) :
    pointsOfDen c d z [x] = if Int.gcd x z = 1 then
      pointsAbove x z (horner (scaledCoeffs c d z) x * if d % 2 = 1 then z else 1) else [] := by
  simp [pointsOfDen]

/-- Filtering the numerators by `p` filters the points by `p` of their first components, since the
points of a numerator `x` are triples `(x, y, z)`. -/
theorem pointsOfDen_filter (c : List Int) (d : Nat) (z : Int) (xs : List Int) (p : Int → Bool) :
    pointsOfDen c d z (xs.filter p) = (pointsOfDen c d z xs).filter fun q ↦ p q.1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : p x <;> by_cases hg : Int.gcd x z = 1 <;>
      simp_all [pointsOfDen, pointsAbove, apply_ite (List.filter _)]

theorem map_toList_range_eq_numerators (H : Nat) :
    (ForIn.toList [0:2 * H + 1]).map (fun i : Nat ↦ (i : Int) - H) = numerators H := by
  simp [numerators, List.range_eq_range']

end BruteForce

namespace Sieve

open BruteForce

/-! ### The sieve of one denominator -/

/-- The invariant of the loop of `Ratpoints.Sieve.sieveDen` over the sieve entries: after the
entries `pref`, the entry of each numerator `i - H` is its survivor test for them. -/
def SieveDenInvariant (H b : Nat) (pref : List SieveEntry)
    (surv : Vector Bool (2 * H + 1)) : Prop :=
  ∀ i (hi : i < 2 * H + 1), surv[i] = survives pref b ((i : Int) - H)

/-- The invariant of the loop of `Ratpoints.Sieve.sieveDen` over the numerators for the sieve entry
`e`, after the entries `pref`: after the positions `done`, the entry of each numerator `i - H` is
its survivor test for `pref` followed by `e` if `i` is among them, and for `pref` otherwise. -/
def SieveDenRowInvariant (H b : Nat) (pref : List SieveEntry) (e : SieveEntry) (done : List Nat)
    (surv : Vector Bool (2 * H + 1)) : Prop :=
  ∀ i (hi : i < 2 * H + 1),
    surv[i] = if i ∈ done then survives (pref ++ [e]) b ((i : Int) - H)
      else survives pref b ((i : Int) - H)

@[spec]
theorem sieveDen_spec (H b : Nat) (entries : List SieveEntry) :
    ⦃ True ⦄ sieveDen H b entries
    ⦃ fun surv ↦ ∀ i (hi : i < 2 * H + 1), surv[i] = survives entries b ((i : Int) - H) ⦄ := by
  vcgen [sieveDen] invariants
  | inv1 => fun pref _ surv ↦ SieveDenInvariant H b pref surv
  | inv2 pref e _ _ _ _ => fun done _ surv ↦ SieveDenRowInvariant H b pref e done surv
  all_goals
    try simp only [SieveDenInvariant, SieveDenRowInvariant] at *
    try intro i hi
    try simp only [Vector.getElem_set]
    grind [survives]

/-! ### The survivors of one denominator -/

/-- The invariant of the loop of `Ratpoints.Sieve.checkDen` over the positions: after the positions
`pref`, the points found are those of the brute-force reference over the denominator `b` and the
numerators `i - H`, `i ∈ pref`, that pass `keep`. -/
def CheckDenInvariant (c : List Int) (d H b : Nat) (keep : Int → Bool) (pref : List Nat)
    (out : Array (Int × Int × Int)) : Prop :=
  out.toList = pointsOfDen c d b ((pref.map fun i : Nat ↦ (i : Int) - H).filter keep)

private theorem checkDen_spec_of_eq (c : List Int) (d H b : Nat) (surv : Vector Bool (2 * H + 1))
    (keep : Int → Bool) :
    ⦃ ∀ i (hi : i < 2 * H + 1), surv[i] = keep ((i : Int) - H) ⦄ checkDen c d H b surv
    ⦃ fun out ↦ out.toList = pointsOfDen c d b ((numerators H).filter keep) ⦄ := by
  vcgen [checkDen] invariants
  · fun pref _ out ↦ CheckDenInvariant c d H b keep pref out
  all_goals grind [CheckDenInvariant, pointsOfDen_append, pointsOfDen_singleton, pointsOfDen_nil,
    map_toList_range_eq_numerators]

/-- The test `keep` of the numerators is quantified in the postcondition rather than taken as an
argument, so that every argument occurs in the program and `vcgen` applies the contract at a call
unaided. -/
@[spec]
theorem checkDen_spec (c : List Int) (d H b : Nat) (surv : Vector Bool (2 * H + 1)) :
    ⦃ True ⦄ checkDen c d H b surv
    ⦃ fun out ↦ ∀ keep : Int → Bool, (∀ i (hi : i < 2 * H + 1), surv[i] = keep ((i : Int) - H)) →
        out.toList = pointsOfDen c d b ((numerators H).filter keep) ⦄ :=
  ⟨fun _ keep hkeep ↦ (checkDen_spec_of_eq c d H b surv keep).le_wp hkeep⟩

end Sieve

end Ratpoints

end

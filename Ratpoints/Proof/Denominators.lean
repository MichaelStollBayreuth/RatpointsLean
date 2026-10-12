/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.Denominators
public import Ratpoints.Proof.Words

import Mathlib.Data.List.Basic
import Ratpoints.Mathlib.Data.List.Basic
import Ratpoints.Proof.Sieve
import Std.Tactic.Do

/-!
# The contract of the run over the denominators

The run of the sieve over the denominators of a shape (`Ratpoints.Sieve.sieveRun`) gives, for each
denominator of the shape's list that passes the tests of the shape, the points of its numerators
that pass the word of its class modulo 64 and survive the tables; when these filters are sound, that
is when they let through every denominator and every numerator over which the brute-force reference
finds a point, this is the reference over the shape's list, in its order.

## Main statements

* `Ratpoints.BruteForce.pointsOfDen_filter_of_ne`: a filter of the numerators that every point
  passes does not change what the brute-force reference finds over a denominator.
* `Ratpoints.Sieve.sieveRun_spec`: the run gives, for each denominator `b` of the list of the shape
  that passes its tests (`Ratpoints.Sieve.Shape.dens`, `Ratpoints.Sieve.Shape.keep`), what the
  brute-force reference finds over `b` and the numerators `-H, …, H` that pass the class word
  `nb[b mod 64]` (`Ratpoints.Sieve.classBit`) and survive the tables, mapped by
  `Ratpoints.Sieve.swapPoint` when the flag of the reversal is set;
  `Ratpoints.Sieve.toList_run_sieveRun` states this as an equation.
* `Ratpoints.Sieve.toList_run_sieveRun_eq_flatMap`: when the list of the shape is a list `l`
  filtered by a test that every denominator of a point passes, and the tests of the shape, the
  class words and the tables let through every denominator and numerator of a point, the run gives
  the reference over `l`, mapped when the flag of the reversal is set.

## Implementation notes

The contract is proved with `vcgen`, with a loop invariant that is a named definition, in a file
with Mathlib, like the other contracts of the side of the denominators. The tests of the shape and
the list of its denominators are read as values, `Id.run` of their computations, so that the
contract of the run does not depend on their contracts, which are stated in the files of their
components; their own loops are not unfolded by `vcgen` here.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace Ratpoints

namespace BruteForce

theorem pointsOfDen_filter_of_ne {c : List Int} {d : Nat} {z : Int} {xs : List Int}
    {keep : Int → Bool} (h : ∀ x ∈ xs, pointsOfDen c d z [x] ≠ [] → keep x) :
    pointsOfDen c d z (xs.filter keep) = pointsOfDen c d z xs := by
  simp only [pointsOfDen_singleton] at h
  exact List.flatMap_filter_of_ne h

end BruteForce

namespace Sieve

open BruteForce

-- The list of the denominators of a shape, as a value for the contract of the run.
private theorem dens_value (s : Shape) (db : UInt64) (bLow bHigh : Nat) :
    ⦃ True ⦄ s.dens db bLow bHigh ⦃ fun r ↦ r = Id.run (s.dens db bLow bHigh) ⦄ :=
  ⟨fun _ ↦ rfl⟩

-- The tests of a shape on a denominator, as a value for the contract of the run.
private theorem keep_value (s : Shape) (nb : Vector UInt64 64) (b : Nat) :
    ⦃ True ⦄ s.keep nb b ⦃ fun r ↦ r = Id.run (s.keep nb b) ⦄ :=
  ⟨fun _ ↦ rfl⟩

/-- The invariant of the loop of `Ratpoints.Sieve.sieveRun` over the denominators of a shape: after
the denominators `pref`, the points found are those of the brute-force reference over the
denominators `b` of `pref` that pass the test `keep` and the numerators `-H, …, H` that pass the
class word `nb[b mod 64]` (`Ratpoints.Sieve.classBit`) and survive the tables `entries`, mapped by
`Ratpoints.Sieve.swapPoint` when the flag `rev` of the reversal is set. -/
def SieveRunInvariant (c : List Int) (d H : Nat) (rev : Bool) (entries : List Entry)
    (nb : Vector UInt64 64) (keep : Nat → Bool) (pref : List Nat)
    (out : Array (Int × Int × Int)) : Prop :=
  out.toList = ((pref.filter keep).flatMap fun b : Nat ↦ pointsOfDen c d b
    ((numerators H).filter fun a ↦ classBit nb[b % 64]! a && survives entries b a)).map
      (if rev then swapPoint else id)

/-- The array size `A ≥ 1` makes the loops over the pieces end, and the moduli are positive, as the
first stage over the rows as words needs (`Ratpoints.Sieve.sift_spec`). -/
@[spec]
theorem sieveRun_spec (c : List Int) (d H A : Nat) (rev : Bool) (entries : List Entry)
    (nb : Vector UInt64 64) (db : UInt64) (shape : Shape) (bLow bHigh : Nat) :
    ⦃ 1 ≤ A ∧ ∀ e ∈ entries, 0 < e.p ⦄ sieveRun c d H A rev entries nb db shape bLow bHigh
    ⦃ fun out ↦ out.toList = (((Id.run (shape.dens db bLow bHigh)).filter
        fun b ↦ Id.run (shape.keep nb b)).flatMap fun b : Nat ↦ pointsOfDen c d b
          ((numerators H).filter fun a ↦ classBit nb[b % 64]! a && survives entries b a)).map
            (if rev then swapPoint else id) ⦄ := by
  vcgen [sieveRun, dens_value, keep_value] invariants
  · fun pref _ out ↦
      SieveRunInvariant c d H rev entries nb (fun b ↦ Id.run (shape.keep nb b)) pref out
  all_goals grind [SieveRunInvariant]

/-- `Ratpoints.Sieve.sieveRun_spec` as an equation, which the proofs use without the program
logic. -/
theorem toList_run_sieveRun (c : List Int) (d H : Nat) (rev : Bool) {A : Nat} (hA : 1 ≤ A)
    {entries : List Entry} (hp : ∀ e ∈ entries, 0 < e.p) (nb : Vector UInt64 64) (db : UInt64)
    (shape : Shape) (bLow bHigh : Nat) :
    (Id.run (sieveRun c d H A rev entries nb db shape bLow bHigh)).toList =
      (((Id.run (shape.dens db bLow bHigh)).filter fun b ↦ Id.run (shape.keep nb b)).flatMap
        fun b : Nat ↦ pointsOfDen c d b ((numerators H).filter fun a ↦
          classBit nb[b % 64]! a && survives entries b a)).map (if rev then swapPoint else id) :=
  Std.WP.Id.of_run_eq_wp rfl _
    ((sieveRun_spec c d H A rev entries nb db shape bLow bHigh).le_wp ⟨hA, hp⟩)

/-- The run gives the brute-force reference over the denominators of `l`, in its order, mapped by
`Ratpoints.Sieve.swapPoint` when the flag `rev` of the reversal is set, when its filters are sound:
the list of the shape is `l` filtered by a test `p`, every denominator of `l` over which the
reference finds a point passes `p` and the tests of the shape, and every numerator of such a
point passes the word of its class and the tables (`Ratpoints.Sieve.toList_run_sieveRun`,
`Ratpoints.BruteForce.pointsOfDen_filter_of_ne`, `List.flatMap_filter_of_ne`). -/
theorem toList_run_sieveRun_eq_flatMap {c : List Int} {d H A : Nat} {rev : Bool}
    {entries : List Entry} {nb : Vector UInt64 64} {db : UInt64} {shape : Shape} {bLow bHigh : Nat}
    {l : List Nat} {p : Nat → Bool} (hA : 1 ≤ A) (hp : ∀ e ∈ entries, 0 < e.p)
    (hdens : Id.run (shape.dens db bLow bHigh) = l.filter p)
    (hkeep : ∀ b ∈ l, pointsOfDen c d b (numerators H) ≠ [] →
      p b = true ∧ Id.run (shape.keep nb b) = true)
    (hnum : ∀ b ∈ l, ∀ a, pointsOfDen c d b [a] ≠ [] →
      classBit nb[b % 64]! a = true ∧ survives entries b a = true) :
    (Id.run (sieveRun c d H A rev entries nb db shape bLow bHigh)).toList =
      (l.flatMap fun b : Nat ↦ pointsOfDen c d b (numerators H)).map
        (if rev then swapPoint else id) := by
  rw [toList_run_sieveRun c d H rev hA hp, hdens, List.filter_filter]
  congr 1
  rw [List.flatMap_congr fun b hb ↦ pointsOfDen_filter_of_ne fun a _ ha ↦ by
    simpa using hnum b (List.mem_filter.mp hb).1 a ha]
  exact List.flatMap_filter_of_ne fun b hb hne ↦ by simpa using (hkeep b hb hne).symm

end Sieve

end Ratpoints

end

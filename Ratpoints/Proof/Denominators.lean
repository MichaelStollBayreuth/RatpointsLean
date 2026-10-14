/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.Denominators
public import Ratpoints.Proof.Words

import Ratpoints.Mathlib.Data.List.Basic
import Ratpoints.Proof.BruteForce
import Ratpoints.Proof.Shapes
import Ratpoints.Proof.Sift
import Std.Tactic.Do

/-!
# The contract of the run over the denominators

The run of the sieve over the denominators of a shape (`Ratpoints.Sieve.sieveRun`) gives, for each
denominator of the shape's list that passes the tests of the shape, the points of its numerators
that pass the word of its class modulo 64 and survive the sieve entries; when these filters are
sound, that is when they let through every denominator and every numerator over which the
brute-force reference finds a point, this is the reference over the shape's list, in its order.

## Main statements

* `Ratpoints.Sieve.sieveRun_spec`: for the denominators from `bLow ≥ 1` to `bHigh < 2 ^ 63`, a
  height below `2 ^ 63` and the reciprocals of the moduli, the run gives, for each denominator `b`
  of the list of the shape that passes its tests (`Ratpoints.Sieve.Shape.dens`,
  `Ratpoints.Sieve.Shape.keep`), what the brute-force reference finds over `b` and the numerators
  `-H, …, H` that pass the class word `nb[b mod 64]` (`Ratpoints.Sieve.classBit`) and survive the
  sieve entries, mapped by `Ratpoints.Sieve.swapPoint` when the flag of the reversal is set;
  `Ratpoints.Sieve.toList_run_sieveRun` states this as an equation.
* `Ratpoints.Sieve.toList_run_sieveRun_eq_flatMap`: when the list of the shape is a list `l`
  filtered by a test that every denominator of a point passes, and the tests of the shape, the
  class words and the sieve entries let through every denominator and numerator of a point, the
  run gives the reference over `l`, mapped when the flag of the reversal is set.

## Implementation notes

The contract is proved with `vcgen`, with a loop invariant that is a named definition, in a file
with Mathlib, like the other contracts of the side of the denominators. The tests of the shape and
the list of its denominators are read as values, `Id.run` of their computations, so that the
contract of the run does not depend on their contracts, which are stated in the files of their
components; their own loops are not unfolded by `vcgen` here. The denominators of the shapes lie
between `bLow` and `bHigh` (`Ratpoints.Sieve.Shape.le_and_le_of_mem_dens`), so that the contract of
the sieve of one denominator (`Ratpoints.Sieve.sift_spec`) applies to each of them.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace Ratpoints

namespace Sieve

open BruteForce

-- The list of the denominators of a shape, as a value for the contract of the run.
private theorem dens_value (s : Shape) (db : UInt64) (bLow bHigh : ℕ) :
    ⦃ True ⦄ s.dens db bLow bHigh ⦃ fun r ↦ r = Id.run (s.dens db bLow bHigh) ⦄ :=
  ⟨fun _ ↦ rfl⟩

-- The tests of a shape on a denominator, as a value for the contract of the run.
private theorem keep_value (s : Shape) (nb : Vector UInt64 64) (b : ℕ) :
    ⦃ True ⦄ s.keep nb b ⦃ fun r ↦ r = Id.run (s.keep nb b) ⦄ :=
  ⟨fun _ ↦ rfl⟩

/-- The invariant of the loop of `Ratpoints.Sieve.sieveRun` over the denominators of a shape: after
the denominators `pref`, the points found are those of the brute-force reference over the
denominators `b` of `pref` that pass the test `keep` and the numerators `-H, …, H` that pass the
class word `nb[b mod 64]` (`Ratpoints.Sieve.classBit`) and survive the sieve entries `entries`,
mapped by `Ratpoints.Sieve.swapPoint` when the flag `rev` of the reversal is set. -/
def SieveRunInvariant (c : List ℤ) (d H : ℕ) (rev : Bool) (entries : List SieveEntry)
    (nb : Vector UInt64 64) (keep : ℕ → Bool) (pref : List ℕ)
    (out : Array (ℤ × ℤ × ℤ)) : Prop :=
  out.toList = ((pref.filter keep).flatMap fun b : ℕ ↦ pointsOfDen c d b
    ((numerators H).filter fun a ↦ classBit nb[b % 64]! a && survives entries b a)).map
      (if rev then swapPoint else id)

-- A denominator of the loop over the list of a shape is positive and below `2 ^ 63`.
private theorem pos_and_lt_of_eq_append_cons {s : Shape} {db : UInt64} {bLow bHigh : ℕ}
    (hbLow : 1 ≤ bLow) (hbHigh : bHigh < 2 ^ 63) {dens pref suff : List ℕ} {cur : ℕ}
    (hd : dens = Id.run (s.dens db bLow bHigh)) (h : dens = pref ++ cur :: suff) :
    0 < cur ∧ cur < 2 ^ 63 := by
  have := s.le_and_le_of_mem_dens db hbLow (hd ▸ h ▸ List.mem_append_right pref List.mem_cons_self)
  lia

/-- The array size `A ≥ 1` makes the loops over the pieces end, and the moduli are positive, as the
first stage over the rows as words needs (`Ratpoints.Sieve.sift_spec`); the test for common factors
on the words of the C code needs the denominators, which lie between `bLow ≥ 1` and `bHigh`
(`Ratpoints.Sieve.Shape.le_and_le_of_mem_dens`), and the height below `2 ^ 63`; `magics` holds the
reciprocals of the moduli in the order of the entries, as the third stage reads them. -/
@[spec]
theorem sieveRun_spec (c : List ℤ) (d H A : ℕ) (rev : Bool) (entries : List SieveEntry)
    (magics : Array ℕ) (nb : Vector UInt64 64) (db : UInt64) (shape : Shape) (bLow bHigh : ℕ) :
    ⦃ 1 ≤ A ∧ (∀ e ∈ entries, 0 < e.p) ∧ 1 ≤ bLow ∧ bHigh < 2 ^ 63 ∧ H < 2 ^ 63 ∧
        magics.toList = entries.map fun e ↦ magic e.p ⦄
    sieveRun c d H A rev entries magics nb db shape bLow bHigh
    ⦃ fun out ↦ out.toList = (((Id.run (shape.dens db bLow bHigh)).filter
        fun b ↦ Id.run (shape.keep nb b)).flatMap fun b : ℕ ↦ pointsOfDen c d b
          ((numerators H).filter fun a ↦ classBit nb[b % 64]! a && survives entries b a)).map
            (if rev then swapPoint else id) ⦄ := by
  vcgen [sieveRun, dens_value, keep_value] invariants
  · fun pref _ out ↦
      SieveRunInvariant c d H rev entries nb (fun b ↦ Id.run (shape.keep nb b)) pref out
  all_goals obtain ⟨hA, hp, hbLow, hbHigh, hH, hmg⟩ := ‹1 ≤ A ∧ _›
  all_goals first
    | have := pos_and_lt_of_eq_append_cons hbLow hbHigh ‹_› ‹_›
      exact ⟨hA, this.1, this.2, hH, by simp, by simp [hmg]⟩
    | grind [SieveRunInvariant]

/-- `Ratpoints.Sieve.sieveRun_spec` as an equation, which the proofs use without the program
logic. -/
theorem toList_run_sieveRun (c : List ℤ) (d H : ℕ) (rev : Bool) {A : ℕ} (hA : 1 ≤ A)
    {entries : List SieveEntry} (hp : ∀ e ∈ entries, 0 < e.p) {magics : Array ℕ}
    (hmg : magics.toList = entries.map fun e ↦ magic e.p) (nb : Vector UInt64 64) (db : UInt64)
    (shape : Shape) {bLow bHigh : ℕ} (hbLow : 1 ≤ bLow) (hbHigh : bHigh < 2 ^ 63)
    (hH : H < 2 ^ 63) :
    (Id.run (sieveRun c d H A rev entries magics nb db shape bLow bHigh)).toList =
      (((Id.run (shape.dens db bLow bHigh)).filter fun b ↦ Id.run (shape.keep nb b)).flatMap
        fun b : ℕ ↦ pointsOfDen c d b ((numerators H).filter fun a ↦
          classBit nb[b % 64]! a && survives entries b a)).map (if rev then swapPoint else id) :=
  Std.WP.Id.of_run_eq_wp rfl _
    ((sieveRun_spec c d H A rev entries magics nb db shape bLow bHigh).le_wp
      ⟨hA, hp, hbLow, hbHigh, hH, hmg⟩)

/-- The run gives the brute-force reference over the denominators of `l`, in its order, mapped by
`Ratpoints.Sieve.swapPoint` when the flag `rev` of the reversal is set, when its filters are sound:
the list of the shape is `l` filtered by a test `p`, every denominator of `l` over which the
reference finds a point passes `p` and the tests of the shape, and every numerator of such a point
passes the word of its class and the sieve entries (`Ratpoints.Sieve.toList_run_sieveRun`,
`Ratpoints.BruteForce.pointsOfDen_filter_of_ne`, `List.flatMap_filter_of_ne`); the denominators
from `bLow ≥ 1` to `bHigh` and the height are below `2 ^ 63`, and `magics` holds the reciprocals of
the moduli in the order of the entries. -/
theorem toList_run_sieveRun_eq_flatMap {c : List ℤ} {d H A : ℕ} {rev : Bool}
    {entries : List SieveEntry} {magics : Array ℕ} {nb : Vector UInt64 64} {db : UInt64}
    {shape : Shape} {bLow bHigh : ℕ} {l : List ℕ} {p : ℕ → Bool} (hA : 1 ≤ A)
    (hp : ∀ e ∈ entries, 0 < e.p) (hmg : magics.toList = entries.map fun e ↦ magic e.p)
    (hbLow : 1 ≤ bLow) (hbHigh : bHigh < 2 ^ 63) (hH : H < 2 ^ 63)
    (hdens : Id.run (shape.dens db bLow bHigh) = l.filter p)
    (hkeep : ∀ b ∈ l, pointsOfDen c d b (numerators H) ≠ [] →
      p b = true ∧ Id.run (shape.keep nb b) = true)
    (hnum : ∀ b ∈ l, ∀ a, pointsOfDen c d b [a] ≠ [] →
      classBit nb[b % 64]! a = true ∧ survives entries b a = true) :
    (Id.run (sieveRun c d H A rev entries magics nb db shape bLow bHigh)).toList =
      (l.flatMap fun b : ℕ ↦ pointsOfDen c d b (numerators H)).map
        (if rev then swapPoint else id) := by
  rw [toList_run_sieveRun c d H rev hA hp hmg nb db shape hbLow hbHigh hH, hdens,
    List.filter_filter]
  congr 1
  rw [List.flatMap_congr fun b hb ↦ pointsOfDen_filter_of_ne fun a _ ha ↦ by
    simpa using hnum b (List.mem_filter.mp hb).1 a ha]
  exact List.flatMap_filter_of_ne fun b hb hne ↦ by simpa using (hkeep b hb hne).symm

end Sieve

end Ratpoints

end

/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.Denominators
public import Ratpoints.Proof.Packing
public import Ratpoints.Proof.Stages

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

* `Ratpoints.Sieve.sieveRun_spec`: for any cut points, sieve entries of the first two stages, the
  first `sp2`, with their tables of inverses (`Ratpoints.Sieve.Factor.HasInverses`) and the row
  offsets of the packings of the classes with a pattern (`Ratpoints.Sieve.OffsetsFor`), whose bits
  are those of the word `db`, sieve entries from the cut point `sp2` on of the shape that the third
  stage needs (`Ratpoints.Sieve.SieveEntry.IsPrimeEntry`), the reciprocals of the moduli, the
  denominators from `bLow ≥ 1` to `bHigh < 2 ^ 63` and a height below `2 ^ 63`, the run gives, for
  each denominator `b` of the list of the shape that passes its tests (`Ratpoints.Sieve.Shape.dens`,
  `Ratpoints.Sieve.Shape.keep`), what the brute-force reference finds over `b` and the numerators
  `-H, …, H` that pass the class word `nb[b mod 64]` (`Ratpoints.Sieve.classBit`), for any words
  `nb` that the classes pack (`Ratpoints.Sieve.NumClass.Packs`), and survive the sieve entries of
  all three stages, mapped by `Ratpoints.Sieve.swapPoint` when the flag of the reversal is set;
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
between `bLow` and `bHigh` (`Ratpoints.Sieve.Shape.le_and_le_of_mem_dens`), and the class of each
that passes the tests of the shape has a pattern (`Ratpoints.Sieve.Shape.bits_ne_zero_of_mem_dens`),
so its row offsets, so that the contract of the sieve of one denominator in the packing of its
class (`Ratpoints.Sieve.sift_spec`) applies to each of them; it holds for the rows of any sieve
entries of the first two stages, and the run makes those of the first `sp2`, with the residues of
`fill_bp_list` (`Ratpoints.Sieve.fillBpList_eq_map`,
`Ratpoints.Sieve.SieveRunInvariant.append_of_forall`). The words of the classes are not arguments
of the run, which reads the classes: they are quantified in the postcondition, as in
`Ratpoints.Sieve.SieveRunInvariant`.
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
private theorem keep_value (s : Shape) (cls : Vector NumClass 64) (b : ℕ) :
    ⦃ True ⦄ s.keep cls b ⦃ fun r ↦ r = Id.run (s.keep cls b) ⦄ :=
  ⟨fun _ ↦ rfl⟩

/-- The invariant of the loop of `Ratpoints.Sieve.sieveRun` over the denominators of a shape: after
the denominators `pref`, for words `nb` of the classes modulo 64 that the classes `cls` pack, the
points found are those of the brute-force reference over the denominators `b` of `pref` that pass
the test `keep` and the numerators `-H, …, H` that pass the class word `nb[b mod 64]`
(`Ratpoints.Sieve.classBit`) and survive the sieve entries `entries`, mapped by
`Ratpoints.Sieve.swapPoint` when the flag `rev` of the reversal is set. -/
def SieveRunInvariant (c : List ℤ) (d H : ℕ) (rev : Bool) (entries : List SieveEntry)
    (cls : Vector NumClass 64) (keep : ℕ → Bool) (pref : List ℕ) (out : Array (ℤ × ℤ × ℤ)) :
    Prop :=
  ∀ nb : Vector UInt64 64, (∀ b < 64, cls[b]!.Packs nb[b]!) →
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

-- The entries with the offsets of the packing of a class have what `fill_bp_list` needs.
private theorem forall_mem_of_packedFor {es : List SieveEntry} {cl : NumClass} {offsets : Array ℕ}
    {pos : ℕ} (h : ∀ n (hn : n < es.length), es[n].PackedFor cl offsets[pos + n]!) :
    ∀ e ∈ es, 0 < e.p ∧ e.p ≤ maxPrimeEven ∧ e.dinv[cl.k]! < e.p := fun _ he ↦
  have ⟨n, hn, he⟩ := List.getElem_of_mem he
  he ▸ ⟨(h n hn).pos, (h n hn).le_maxPrimeEven, (h n hn).dinv_lt⟩

/-- The denominator `cur` of the list of the shape that its tests let through appends the points of
its sieve, given the contract of `Ratpoints.Sieve.sift` (`Ratpoints.Sieve.sift_spec`) with the
class `cls[cur mod 64]`, which has a pattern (`Ratpoints.Sieve.Shape.bits_ne_zero_of_mem_dens`) and
so the row of its offsets, the residues of `fill_bp_list` (`Ratpoints.Sieve.fillBpList_eq_map`), the
first `sp2` sieve entries in the first two stages and the others in the third. -/
theorem SieveRunInvariant.append_of_forall {c : List ℤ} {d H : ℕ} {rev : Bool}
    {entries : List SieveEntry} {magics : Array ℕ} {cls : Vector NumClass 64} {offsets : Array ℕ}
    {db : UInt64} {shape : Shape} {bLow bHigh : ℕ} {dens pref suff : List ℕ}
    {out pts : Array (ℤ × ℤ × ℤ)} {cur sp2 : ℕ}
    (hmg : magics.toList = entries.map fun e ↦ magic e.p)
    (hinv : ∀ e ∈ entries.take sp2, ∀ f ∈ e.factors, f.HasInverses e.p)
    (hoff : OffsetsFor cls (entries.take sp2) offsets)
    (hdb : ∀ j < 64, db.toBitVec.getLsbD j = (cls[j]!.bits != 0))
    (hd : dens = Id.run (shape.dens db bLow bHigh)) (hl : dens = pref ++ cur :: suff)
    (h : SieveRunInvariant c d H rev entries cls (fun b ↦ Id.run (shape.keep cls b)) pref out)
    (hk : Id.run (shape.keep cls cur) = true)
    (hpts : ∀ (es : List SieveEntry) (w : UInt64) (pos : ℕ), cls[cur % 64]!.Packs w →
      cls[cur % 64]!.offset = some pos →
      (entries.take sp2).map (fun e ↦ (e.p, e.rows)) = es.map (fun e ↦ (e.p, e.rows)) →
      magics.toList.take sp2 = es.map (magic ·.p) →
      fillBpList cur cls[cur % 64]!.k (entries.take sp2) (magics.toList.take sp2) =
        es.map (fun e ↦ cur * e.dinv[cls[cur % 64]!.k]! % e.p) →
      (∀ e ∈ es, ∀ f ∈ e.factors, f.HasInverses e.p) →
      (∀ n (h : n < es.length), es[n].PackedFor cls[cur % 64]! offsets[pos + n]!) →
      pts.toList = (pointsOfDen c d cur ((numerators H).filter fun a ↦
        classBit w a && survives (es ++ entries.drop sp2) cur a)).map
          (if rev then swapPoint else id)) :
    SieveRunInvariant c d H rev entries cls (fun b ↦ Id.run (shape.keep cls b)) (pref ++ [cur])
      (out ++ pts) := fun nb hnb ↦ by
  have hb := shape.bits_ne_zero_of_mem_dens hdb
    (hd ▸ hl ▸ List.mem_append_right pref List.mem_cons_self) hk
  obtain ⟨pos, hpos, hpf⟩ := hoff (cur % 64) (Nat.mod_lt _ (by decide)) hb
  have hmg' : magics.toList.take sp2 = (entries.take sp2).map (magic ·.p) := by
    rw [hmg, List.map_take]
  have := hpts (entries.take sp2) nb[cur % 64]! pos (hnb _ (Nat.mod_lt _ (by decide))) hpos rfl hmg'
    (hmg' ▸ fillBpList_eq_map (forall_mem_of_packedFor hpf)) hinv hpf
  rw [List.take_append_drop] at this
  rw [Array.toList_append, h nb hnb, this, List.filter_append, List.flatMap_append,
    List.map_append]
  simp [hk]

theorem sieveRunInvariant_nil (c : List ℤ) (d H : ℕ) (rev : Bool) (entries : List SieveEntry)
    (cls : Vector NumClass 64) (keep : ℕ → Bool) :
    SieveRunInvariant c d H rev entries cls keep [] #[] :=
  fun _ _ ↦ by simp

/-- A denominator that the tests of the shape reject appends no points. -/
theorem SieveRunInvariant.append_of_not {c : List ℤ} {d H : ℕ} {rev : Bool}
    {entries : List SieveEntry} {cls : Vector NumClass 64} {keep : ℕ → Bool} {pref : List ℕ}
    {out : Array (ℤ × ℤ × ℤ)} {cur : ℕ} (h : SieveRunInvariant c d H rev entries cls keep pref out)
    (hk : ¬keep cur = true) : SieveRunInvariant c d H rev entries cls keep (pref ++ [cur]) out :=
  fun nb hnb ↦ by
    rw [h nb hnb]
    simp [List.filter_append, hk]

/-- The array size `A ≥ 1` makes the loops over the pieces end; the sieve entries of the first two
stages, the first `sp2`, have their tables of inverses and the row offsets of the packings of the
classes `cls` with a pattern (`Ratpoints.Sieve.OffsetsFor`), whose bits are those of the word `db`
of the word shape, and the sieve entries from position `sp2` on, those of the third stage, have the
shape that it needs (`Ratpoints.Sieve.SieveEntry.IsPrimeEntry`); `magics` holds the reciprocals of
the moduli in the order of the entries, as the stages read them; the test for common factors on the
words of the C code needs the denominators, which lie between `bLow ≥ 1` and `bHigh`
(`Ratpoints.Sieve.Shape.le_and_le_of_mem_dens`), and the height below `2 ^ 63`. The words `nb` of
the classes modulo 64 that the classes pack are quantified in the postcondition, since the program
does not mention them. -/
@[spec]
theorem sieveRun_spec (c : List ℤ) (d H A : ℕ) (rev : Bool) (sp1 sp2 : ℕ)
    (entries : List SieveEntry) (magics : Array ℕ) (cls : Vector NumClass 64) (offsets : Array ℕ)
    (db : UInt64) (shape : Shape) (bLow bHigh : ℕ) :
    ⦃ 1 ≤ A ∧ (∀ e ∈ entries.drop sp2, e.IsPrimeEntry) ∧
        magics.toList = entries.map (fun e ↦ magic e.p) ∧ 1 ≤ bLow ∧ bHigh < 2 ^ 63 ∧ H < 2 ^ 63 ∧
        (∀ e ∈ entries.take sp2, ∀ f ∈ e.factors, f.HasInverses e.p) ∧
        OffsetsFor cls (entries.take sp2) offsets ∧
        ∀ j < 64, db.toBitVec.getLsbD j = (cls[j]!.bits != 0) ⦄
    sieveRun c d H A rev sp1 sp2 entries magics cls offsets db shape bLow bHigh
    ⦃ fun out ↦ ∀ nb : Vector UInt64 64, (∀ b < 64, cls[b]!.Packs nb[b]!) →
        out.toList = (((Id.run (shape.dens db bLow bHigh)).filter
          fun b ↦ Id.run (shape.keep cls b)).flatMap fun b : ℕ ↦ pointsOfDen c d b
            ((numerators H).filter fun a ↦ classBit nb[b % 64]! a && survives entries b a)).map
              (if rev then swapPoint else id) ⦄ := by
  vcgen [sieveRun, dens_value, keep_value] invariants
  · fun pref _ out ↦
      SieveRunInvariant c d H rev entries cls (fun b ↦ Id.run (shape.keep cls b)) pref out
  all_goals obtain ⟨hA, hes, hmg, hbLow, hbHigh, hH, hinv, hoff, hdb⟩ := ‹1 ≤ A ∧ _›
  all_goals first
    | have := pos_and_lt_of_eq_append_cons hbLow hbHigh ‹_› ‹_›
      exact ⟨hA, this.1, this.2, hH, hes, by rw [hmg, List.map_drop]⟩
    | exact SieveRunInvariant.append_of_forall hmg hinv hoff hdb ‹_› ‹_› ‹_› (by simp_all) ‹_›
    | exact sieveRunInvariant_nil c d H rev entries cls _
    | exact SieveRunInvariant.append_of_not ‹_› (by simp_all)
    | (subst_vars; exact ‹SieveRunInvariant _ _ _ _ _ _ _ _ _› _ ‹_›)

/-- `Ratpoints.Sieve.sieveRun_spec` as an equation, which the proofs use without the program
logic. -/
theorem toList_run_sieveRun (c : List ℤ) (d H : ℕ) (rev : Bool) (sp1 sp2 : ℕ) {A : ℕ}
    (hA : 1 ≤ A) {entries : List SieveEntry} (hes : ∀ e ∈ entries.drop sp2, e.IsPrimeEntry)
    {magics : Array ℕ} (hmg : magics.toList = entries.map fun e ↦ magic e.p)
    (hinv : ∀ e ∈ entries.take sp2, ∀ f ∈ e.factors, f.HasInverses e.p) {cls : Vector NumClass 64}
    {offsets : Array ℕ} (hoff : OffsetsFor cls (entries.take sp2) offsets) {db : UInt64}
    (hdb : ∀ j < 64, db.toBitVec.getLsbD j = (cls[j]!.bits != 0)) {nb : Vector UInt64 64}
    (hnb : ∀ b < 64, cls[b]!.Packs nb[b]!) (shape : Shape) {bLow bHigh : ℕ} (hbLow : 1 ≤ bLow)
    (hbHigh : bHigh < 2 ^ 63) (hH : H < 2 ^ 63) :
    (Id.run (sieveRun c d H A rev sp1 sp2 entries magics cls offsets db shape bLow bHigh)).toList =
      (((Id.run (shape.dens db bLow bHigh)).filter fun b ↦ Id.run (shape.keep cls b)).flatMap
        fun b : ℕ ↦ pointsOfDen c d b ((numerators H).filter fun a ↦
          classBit nb[b % 64]! a && survives entries b a)).map (if rev then swapPoint else id) :=
  Std.WP.Id.of_run_eq_wp rfl _
    ((sieveRun_spec c d H A rev sp1 sp2 entries magics cls offsets db shape bLow bHigh).le_wp
      ⟨hA, hes, hmg, hbLow, hbHigh, hH, hinv, hoff, hdb⟩) nb hnb

/-- The run gives the brute-force reference over the denominators of `l`, in its order, mapped by
`Ratpoints.Sieve.swapPoint` when the flag `rev` of the reversal is set, when its filters are sound:
the list of the shape is `l` filtered by a test `p`, every denominator of `l` over which the
reference finds a point passes `p` and the tests of the shape, and every numerator of such a point
passes the word of its class among the words `nb` that the classes `cls` pack and the sieve entries
(`Ratpoints.Sieve.toList_run_sieveRun`, `Ratpoints.BruteForce.pointsOfDen_filter_of_ne`,
`List.flatMap_filter_of_ne`); the sieve entries of the first two stages, the first `sp2`, have
their tables of inverses and the row offsets of the packings of the classes, whose bits are those of
`db`, and those from position `sp2` on, of the third stage, the shape of
`Ratpoints.Sieve.SieveEntry.IsPrimeEntry`; `magics` holds the reciprocals of the moduli in the order
of the entries, and the denominators from `bLow ≥ 1` to `bHigh` and the height are below
`2 ^ 63`. -/
theorem toList_run_sieveRun_eq_flatMap {c : List ℤ} {d H A : ℕ} {rev : Bool} {sp1 sp2 : ℕ}
    {entries : List SieveEntry} {magics : Array ℕ} {cls : Vector NumClass 64} {offsets : Array ℕ}
    {db : UInt64} {nb : Vector UInt64 64} {shape : Shape} {bLow bHigh : ℕ} {l : List ℕ}
    {p : ℕ → Bool} (hA : 1 ≤ A) (hes : ∀ e ∈ entries.drop sp2, e.IsPrimeEntry)
    (hmg : magics.toList = entries.map fun e ↦ magic e.p)
    (hinv : ∀ e ∈ entries.take sp2, ∀ f ∈ e.factors, f.HasInverses e.p)
    (hoff : OffsetsFor cls (entries.take sp2) offsets)
    (hdb : ∀ j < 64, db.toBitVec.getLsbD j = (cls[j]!.bits != 0))
    (hnb : ∀ b < 64, cls[b]!.Packs nb[b]!) (hbLow : 1 ≤ bLow) (hbHigh : bHigh < 2 ^ 63)
    (hH : H < 2 ^ 63) (hdens : Id.run (shape.dens db bLow bHigh) = l.filter p)
    (hkeep : ∀ b ∈ l, pointsOfDen c d b (numerators H) ≠ [] →
      p b = true ∧ Id.run (shape.keep cls b) = true)
    (hnum : ∀ b ∈ l, ∀ a, pointsOfDen c d b [a] ≠ [] →
      classBit nb[b % 64]! a = true ∧ survives entries b a = true) :
    (Id.run (sieveRun c d H A rev sp1 sp2 entries magics cls offsets db shape bLow bHigh)).toList =
      (l.flatMap fun b : ℕ ↦ pointsOfDen c d b (numerators H)).map
        (if rev then swapPoint else id) := by
  rw [toList_run_sieveRun c d H rev sp1 sp2 hA hes hmg hinv hoff hdb hnb shape hbLow hbHigh hH,
    hdens, List.filter_filter]
  congr 1
  rw [List.flatMap_congr fun b hb ↦ pointsOfDen_filter_of_ne fun a _ ha ↦ by
    simpa using hnum b (List.mem_filter.mp hb).1 a ha]
  exact List.flatMap_filter_of_ne fun b hb hne ↦ by simpa using (hkeep b hb hne).symm

end Sieve

end Ratpoints

end

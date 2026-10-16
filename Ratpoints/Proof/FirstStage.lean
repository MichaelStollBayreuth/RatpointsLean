/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Proof.Words

import Ratpoints.Proof.Containers
import Std.Tactic.Do

/-!
# The contract of the chunked first stage

The contracts of the arm of the first stage for a chunk from 2 to 16
(`Ratpoints.Sieve.andRowsChunked`): the starts of the rows at the first word number of a piece
(`Ratpoints.Sieve.chunkStarts`), a start stepped back by the modulus (`Ratpoints.Sieve.wrapStart`),
one chunk in registers (`Ratpoints.Sieve.chunkSieve`), the whole chunks of a piece
(`Ratpoints.Sieve.andChunks`), one leg over the tail (`Ratpoints.Sieve.tailLeg`) and the tail in
legs of 8, 4, 2 and 1 bit arrays (`Ratpoints.Sieve.tailLegs`), as `@[spec]` theorems proved with
`vcgen`, the program logic of Lean core, with loop invariants that are named definitions. The
chunked arm leaves the words of the piece that the arm one row at a time leaves
(`Ratpoints.Sieve.andRowsChunked_spec`, with the postcondition of `Ratpoints.Sieve.andRows_spec`).

The chunked arm reads each row from its start, which it moves on by the chunk after each chunk and
back into the first `p` bit arrays of the row; the words that it reads from the starts
(`Ratpoints.Sieve.andFrom`) are those of the first stage at the word numbers of the piece when the
starts are those of the first word number (`Ratpoints.Sieve.andFrom_map_startAt`), and the registers
read up to `chunk - 1` bit arrays past the first `p` of a row, which repeat its first ones
(`Ratpoints.Sieve.partialReg_eq_andFrom`).

## Main definitions

* `Ratpoints.Sieve.SieveSpec.startAt`, `Ratpoints.Sieve.SieveSpec.advance`: a sieve spec with its
  start at a word number, and with its start moved on.
* `Ratpoints.Sieve.SieveSpec.WalkFits`: what the chunked arm needs of a sieve spec of its local
  array.
* `Ratpoints.Sieve.SieveSpec.wordFrom`, `Ratpoints.Sieve.andFrom`: the words that the chunked arm
  reads from the starts of the rows.
* `Ratpoints.Sieve.partialReg`: the registers of a chunk after some of the moduli.

## Main statements

* `Ratpoints.Sieve.wrapStart_spec`: the start stepped back is the start modulo `p`.
* `Ratpoints.Sieve.chunkStarts_spec`: the starts of the rows at the first word number.
* `Ratpoints.Sieve.chunkSieve_spec`, `Ratpoints.Sieve.andChunks_spec`: one chunk, and the whole
  chunks of a piece.
* `Ratpoints.Sieve.tailLeg_spec`, `Ratpoints.Sieve.tailLegs_spec`: one leg, and the tail.
* `Ratpoints.Sieve.andRowsChunked_spec`: the chunked arm leaves each word of the piece the class
  word and-ed with its row words (`Ratpoints.Sieve.andWords`).

## Implementation notes

The file uses Lean core and `Std` only, as the contracts of the sieve do. The proofs use only that
`Ratpoints.rbaPack` and `Ratpoints.chunk` are positive, never their values; the cover of the tail by
the legs is a fact decided over the tails below 16, which the arm's chunk of at most 16 bounds.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace Ratpoints

namespace Sieve

/-! ### The starts of the rows -/

/-- The sieve spec `s` with its start at the word number `w0`: the bit array `(w0 + offset) mod p`
of the row, which the bit array with the word number `w0` reads. -/
def SieveSpec.startAt (w0 : Int) (s : SieveSpec) : SieveSpec :=
  { s with start := ((w0 + s.offset) % (s.p : Int)).toNat }

/-- The sieve spec `s` with its start moved on by `c` bit arrays and back into the first `p` bit
arrays of the row. -/
def SieveSpec.advance (c : Nat) (s : SieveSpec) : SieveSpec :=
  { s with start := (s.start + c) % s.p }

/-- What the chunked first stage needs of a sieve spec of its local array: a positive modulus, the
end `p` of the walk through the row, a start below `p`, and the row repeating its first bit arrays
after the first `p` (`Ratpoints.Sieve.SieveSpec.Wraps`). -/
structure SieveSpec.WalkFits (s : SieveSpec) : Prop where
  /-- The modulus is positive. -/
  pos : 0 < s.p
  /-- The end of the walk through the row is the modulus. -/
  stop_eq : s.stop = s.p
  /-- The start is below the modulus. -/
  start_lt : s.start < s.p
  /-- The row repeats its first bit arrays after the first `p`. -/
  wraps : s.Wraps

theorem SieveSpec.Fits.walkFits_startAt {s : SieveSpec} (hs : s.Fits) (w0 : Int) :
    (s.startAt w0).WalkFits :=
  ⟨hs.pos, hs.stop_eq, Int.toNat_emod_lt _ hs.pos, hs.wraps⟩

theorem SieveSpec.WalkFits.advance {s : SieveSpec} (h : s.WalkFits) (c : Nat) :
    (s.advance c).WalkFits :=
  ⟨h.pos, h.stop_eq, Nat.mod_lt _ h.pos, h.wraps⟩

theorem SieveSpec.advance_advance (s : SieveSpec) (c c' : Nat) :
    (s.advance c).advance c' = s.advance (c + c') := by
  simp only [SieveSpec.advance, Nat.mod_add_mod, Nat.add_assoc]

theorem SieveSpec.WalkFits.advance_zero {s : SieveSpec} (h : s.WalkFits) : s.advance 0 = s := by
  simp only [SieveSpec.advance, Nat.add_zero, Nat.mod_eq_of_lt h.start_lt]

theorem map_advance_zero {sv : List SieveSpec} (h : ∀ s ∈ sv, s.WalkFits) :
    sv.map (SieveSpec.advance 0) = sv := by
  rw [List.map_congr_left (g := id) fun s hs ↦ (h s hs).advance_zero, List.map_id]

/-- The word of the row of `s` that the chunked first stage ands into word `y` of a piece whose
first bit array reads the row at the start of `s`: word `y mod rbaPack` of bit array
`(start + y / rbaPack) mod p` of the row. -/
def SieveSpec.wordFrom (s : SieveSpec) (y : Nat) : UInt64 :=
  s.row[rbaPack * ((s.start + y / rbaPack) % s.p) + y % rbaPack]!

/-- The word `cw` and-ed in turn with the words of the rows of `sv` at word `y` of a piece from
their starts on (`Ratpoints.Sieve.SieveSpec.wordFrom`). -/
def andFrom (sv : List SieveSpec) (cw : UInt64) (y : Nat) : UInt64 :=
  sv.foldl (fun acc s ↦ acc &&& s.wordFrom y) cw

-- A left fold that ands the words `f s` of the entries of a list is unchanged when `f` is changed
-- only off the list.
private theorem foldl_and_congr {l : List SieveSpec} {f g : SieveSpec → UInt64}
    (h : ∀ s ∈ l, f s = g s) (cw : UInt64) :
    l.foldl (fun acc s ↦ acc &&& f s) cw = l.foldl (fun acc s ↦ acc &&& g s) cw := by
  induction l generalizing cw with
  | nil => rfl
  | cons s l ih =>
    simp only [List.foldl_cons, h s List.mem_cons_self]
    exact ih (fun s hs ↦ h s (List.mem_cons_of_mem _ hs)) _

theorem SieveSpec.wordFrom_startAt (s : SieveSpec) (hp : 0 < s.p) (w0 : Int) (y : Nat) :
    (s.startAt w0).wordFrom y = s.wordAt w0 y := by
  simp only [SieveSpec.wordFrom, SieveSpec.startAt, SieveSpec.wordAt,
    Int.toNat_emod_add_mod _ _ hp]

theorem SieveSpec.wordFrom_advance (s : SieveSpec) (c y : Nat) :
    (s.advance c).wordFrom y = s.wordFrom (rbaPack * c + y) := by
  simp only [SieveSpec.wordFrom, SieveSpec.advance, Nat.mul_add_div rbaPack_pos, Nat.mul_add_mod,
    Nat.mod_add_mod, Nat.add_assoc]

/-- The words that the chunked first stage reads from the starts of the rows at the word number
`w0` are those of the first stage at the word numbers from `w0` on. -/
theorem andFrom_map_startAt {specs : List SieveSpec} (h : ∀ s ∈ specs, 0 < s.p) (cw : UInt64)
    (w0 : Int) (y : Nat) : andFrom (specs.map (·.startAt w0)) cw y = andWords specs cw w0 y := by
  simp only [andFrom, andWords, List.foldl_map]
  exact foldl_and_congr (fun s hs ↦ s.wordFrom_startAt (h s hs) w0 y) cw

theorem andFrom_map_advance (sv : List SieveSpec) (cw : UInt64) (c y : Nat) :
    andFrom (sv.map (·.advance c)) cw y = andFrom sv cw (rbaPack * c + y) := by
  simp only [andFrom, List.foldl_map, SieveSpec.wordFrom_advance]

/-! ### The registers of a chunk -/

/-- The registers of the chunked first stage at word `κ` of bit array `x` after the moduli `l`: the
class word `cw` and-ed in turn with word `κ` of bit array `start + x` of each row, read past the
first `p` bit arrays into the copies of the first ones. -/
def partialReg (l : List SieveSpec) (cw : UInt64) (x κ : Nat) : UInt64 :=
  l.foldl (fun acc s ↦ acc &&& s.row[rbaPack * (s.start + x) + κ]!) cw

theorem partialReg_concat (l : List SieveSpec) (s : SieveSpec) (cw : UInt64) (x κ : Nat) :
    partialReg (l ++ [s]) cw x κ = partialReg l cw x κ &&& s.row[rbaPack * (s.start + x) + κ]! := by
  simp [partialReg]

/-- The registers of a chunk, read from starts below `p` up to `chunk - 1` bit arrays past them,
hold the words that the chunked first stage reads from the starts, since the rows repeat their first
bit arrays after the first `p` (`Ratpoints.Sieve.SieveSpec.Wraps`). -/
theorem partialReg_eq_andFrom {l : List SieveSpec} (h : ∀ s ∈ l, s.WalkFits) (cw : UInt64)
    {x κ : Nat} (hx : x < chunk) (hκ : κ < rbaPack) :
    partialReg l cw x κ = andFrom l cw (rbaPack * x + κ) := by
  refine foldl_and_congr (fun s hs ↦ ?_) cw
  have hw := h s hs
  rw [SieveSpec.wordFrom, Nat.mul_add_div rbaPack_pos, Nat.div_eq_of_lt hκ, Nat.add_zero,
    Nat.mul_add_mod, Nat.mod_eq_of_lt hκ, hw.wraps _ (by lia [hw.start_lt]) κ hκ]

/-! ### The starts at the first word number -/

/-- The invariant of the loop of `Ratpoints.Sieve.chunkStarts` over the moduli and, in step with
them, their reciprocals `mgs`, whose state is the local array of the sieve specs and the
reciprocals still to come: after the moduli `pref`, the reciprocals still to come are those after
the first `pref.length`, and the array holds the sieve specs of `pref` with their starts at the word
number `w0`. -/
def ChunkStartsInvariant (w0 : Int) (mgs : List Nat) (pref : List SieveSpec)
    (st : Array SieveSpec × List Nat) : Prop :=
  st.2 = mgs.drop pref.length ∧ st.1.toList = pref.map (·.startAt w0)

theorem chunkStartsInvariant_nil (w0 : Int) (mgs : List Nat) :
    ChunkStartsInvariant w0 mgs [] (#[], Std.toStream mgs) :=
  ⟨rfl, rfl⟩

/-- A step of the loop of `Ratpoints.Sieve.chunkStarts`: the start of the modulus `s` at `w0` by the
reduction with the reciprocal of the cursor, which is that of `s`
(`Ratpoints.Sieve.SieveSpec.Fits.ite_modMul_modLong_add_eq_emod`). -/
theorem ChunkStartsInvariant.push {w0 : Int} {small : Bool} {specs pref suff : List SieveSpec}
    {s : SieveSpec} {mgs rest rest' : List Nat} {mg : Nat} {sv : Array SieveSpec}
    (pre : (∀ s ∈ specs, s.Fits) ∧ mgs = specs.map (magic ·.p) ∧ SmallFits small w0 w0)
    (hs : specs = pref ++ s :: suff) (h : ChunkStartsInvariant w0 mgs pref (sv, rest))
    (hnext : Std.Stream.next? rest = some (mg, rest')) :
    ChunkStartsInvariant w0 mgs (pref ++ [s])
      (sv.push { s with start := (if small then modMul (w0 + s.offset) s.p mg
        else modLong (w0 + s.offset) s.p).toNat }, rest') := by
  obtain ⟨rfl, -⟩ := eq_magic_and_of_next?_eq_some pre.2.1 hs (fun _ ↦ h.1) hnext
  have hfit := pre.1 s (by simp [hs])
  have hrest : rest = mgs.drop pref.length := h.1
  refine ⟨?_, ?_⟩
  · change rest' = mgs.drop (pref ++ [s]).length
    rw [List.length_append, List.length_singleton, ← List.drop_drop, ← hrest,
      List.eq_cons_of_next?_eq_some hnext]
    rfl
  · rw [hfit.ite_modMul_modLong_add_eq_emod pre.2.2, Array.toList_push, h.2, List.map_append]
    rfl

theorem ChunkStartsInvariant.next?_ne_none {w0 : Int} {small : Bool}
    {specs pref suff : List SieveSpec} {s : SieveSpec} {mgs rest : List Nat} {sv : Array SieveSpec}
    (pre : (∀ s ∈ specs, s.Fits) ∧ mgs = specs.map (magic ·.p) ∧ SmallFits small w0 w0)
    (hs : specs = pref ++ s :: suff) (h : ChunkStartsInvariant w0 mgs pref (sv, rest)) :
    Std.Stream.next? rest ≠ none :=
  next?_ne_none_of_lt pre.2.1 hs fun _ ↦ h.1

theorem ChunkStartsInvariant.toList_eq {w0 : Int} {mgs : List Nat} {specs : List SieveSpec}
    {st : Array SieveSpec × List Nat} (h : ChunkStartsInvariant w0 mgs specs st) :
    st.1.toList = specs.map (·.startAt w0) :=
  h.2

attribute [local irreducible] ChunkStartsInvariant in
/-- The local array of the sieve specs holds them with their starts at the word number `w0`, the
reduction by the reciprocal of the cursor under the test `small` giving the Euclidean remainder of
`w0 + offset`; the reciprocals run in step with the moduli and do not run out before them. -/
@[spec]
theorem chunkStarts_spec (specs : List SieveSpec) (mgs : List Nat) (small : Bool) (w0 : Int) :
    ⦃ (∀ s ∈ specs, s.Fits) ∧ mgs = specs.map (magic ·.p) ∧ SmallFits small w0 w0 ⦄
    chunkStarts specs mgs small w0
    ⦃ fun sv ↦ sv.toList = specs.map (·.startAt w0) ⦄ := by
  vcgen [chunkStarts] invariants
  | inv1 => fun l _ ↦ ChunkStartsInvariant w0 mgs l
  all_goals first
    | exact chunkStartsInvariant_nil w0 mgs
    | exact ChunkStartsInvariant.toList_eq ‹_›
    | exact absurd ‹_› (ChunkStartsInvariant.next?_ne_none ‹_› ‹_› ‹_›)
    | exact ChunkStartsInvariant.push ‹_› ‹_› ‹_› ‹_›

/-! ### The step back of a start -/

/-- The invariant of the loop of `Ratpoints.Sieve.wrapStart`: the start keeps its residue modulo
`p`, and is below `p` at the exit. -/
def WrapStartInvariant (st p : Nat) : Std.WP.WhileInvariant Nat Prop :=
  .mk fun exit s ↦ s % p = st % p ∧ (exit = true → s < p)

theorem WrapStartInvariant.sub {st p stop s mb : Nat}
    (h : s = mb ∧ WrapStartInvariant st p false s)
    (hs : stop ≤ s) (pre : 0 < p ∧ stop = p) :
    s - p < mb ∧ WrapStartInvariant st p false (s - p) := by
  obtain ⟨hp, rfl⟩ := pre
  exact ⟨by lia, by rw [← Nat.mod_eq_sub_mod hs]; exact h.2.1, nofun⟩

theorem WrapStartInvariant.exit {st p stop s mb : Nat} (hs : ¬stop ≤ s) (pre : 0 < p ∧ stop = p)
    (h : s = mb ∧ WrapStartInvariant st p false s) : WrapStartInvariant st p true s :=
  ⟨h.2.1, fun _ ↦ by lia⟩

theorem WrapStartInvariant.post {st p s : Nat} (h : WrapStartInvariant st p true s) :
    s = st % p := by
  rw [← h.1, Nat.mod_eq_of_lt (h.2 rfl)]

open Std.WP Lean.Order in
/-- For the end `stop = p > 0`, the start stepped back is its residue modulo `p`. -/
@[spec]
theorem wrapStart_spec (st stop p : Nat) :
    ⦃ 0 < p ∧ stop = p ⦄ wrapStart st stop p ⦃ fun r ↦ r = st % p ⦄ := by
  vcgen [wrapStart] invariants
  · WrapStartInvariant st p
  · Variant.ofMeasure fun s : Nat ↦ s
  all_goals try simp only [Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure,
    Variant.evalsBelow_ofMeasure_nat, meet_prop_eq_and, ofProp_prop_eq] at *
  all_goals first
    | exact ⟨rfl, nofun⟩
    | exact WrapStartInvariant.post ‹_›
    | exact WrapStartInvariant.sub ‹_› ‹_› ‹_›
    | exact WrapStartInvariant.exit ‹_› ‹_› ‹_›

/-! ### One chunk -/

theorem partialReg_take_succ {sv : Array SieveSpec} {K : Nat} (hK : K < sv.size) (cw : UInt64)
    (x κ : Nat) : partialReg (sv.toList.take (K + 1)) cw x κ =
      partialReg (sv.toList.take K) cw x κ &&& sv[K]!.row[rbaPack * (sv[K]!.start + x) + κ]! := by
  rw [List.take_add_one, Array.getElem?_toList, Array.getElem?_eq_getElem hK, Option.toList_some,
    partialReg_concat, getElem!_pos sv K hK]

/-- The invariant of the loop of `Ratpoints.Sieve.chunkSieve` over the moduli after the first `K`
of the local array `sv`: the registers hold the first `K` moduli, and the starts of those moduli
are moved on by the chunk. -/
def ChunkModInvariant (sv : Array SieveSpec) (cw : UInt64) (K : Nat) (st : Array SieveSpec)
    (regs : Vector UInt64 (chunk * rbaPack)) : Prop :=
  (∀ j < chunk, ∀ κ < rbaPack, regs[rbaPack * j + κ]! = partialReg (sv.toList.take K) cw j κ) ∧
    st.size = sv.size ∧ ∀ k < sv.size, st[k]! = if k < K then sv[k]!.advance chunk else sv[k]!

/-- The invariant of the loop of `Ratpoints.Sieve.chunkSieve` that ands the row of the modulus `K`
into the registers below `c`. -/
def ChunkAndInvariant (sv : Array SieveSpec) (cw : UInt64) (K c : Nat)
    (regs : Vector UInt64 (chunk * rbaPack)) : Prop :=
  ∀ j < chunk, ∀ κ < rbaPack,
    regs[rbaPack * j + κ]! = partialReg (sv.toList.take (if j < c then K + 1 else K)) cw j κ

/-- A load of the first modulus into register `cur`. -/
theorem getElem!_loadBitArray_chunk {sv : Array SieveSpec} {cw : UInt64} {cur : Nat}
    {pref suff : List Nat}
    {regs : Vector UInt64 (chunk * rbaPack)} (pre : 0 < sv.size ∧ ∀ s ∈ sv, 0 < s.p ∧ s.stop = s.p)
    (hl : ForIn.toList [0:chunk] = pref ++ cur :: suff)
    (h : ∀ j < pref.length, ∀ κ < rbaPack,
      regs[rbaPack * j + κ]! = partialReg (sv.toList.take 1) cw j κ) :
    ∀ j < (pref ++ [cur]).length, ∀ κ < rbaPack,
      (loadBitArray regs cur cw sv[0]!.row (sv[0]!.start + cur))[rbaPack * j + κ]! =
        partialReg (sv.toList.take 1) cw j κ := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have hcl := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  intro j hj κ hκ
  rw [List.length_append, List.length_singleton] at hj
  rw [getElem!_loadBitArray _ _ _ _ _ (Nat.mul_add_lt_mul_of_lt_of_lt' (by lia) hκ),
    Nat.mul_add_div rbaPack_pos, Nat.div_eq_of_lt hκ, Nat.add_zero, Nat.mul_add_mod,
    Nat.mod_eq_of_lt hκ]
  split
  · subst_vars
    rw [partialReg_take_succ pre.1]
    rfl
  · exact h j (by lia) κ hκ

theorem chunkSieve_pre_zero {sv : Array SieveSpec}
    (pre : 0 < sv.size ∧ ∀ s ∈ sv, 0 < s.p ∧ s.stop = s.p) :
    0 < sv[0]!.p ∧ sv[0]!.stop = sv[0]!.p :=
  pre.2 _ (Array.getElem!_mem pre.1)

/-- The start of the loop over the further moduli: the registers hold the first modulus, its start
moved on. -/
theorem chunkModInvariant_init {sv : Array SieveSpec} {cw : UInt64} {st : Nat}
    {regs : Vector UInt64 (chunk * rbaPack)}
    (h : ∀ j < (ForIn.toList [0:chunk]).length, ∀ κ < rbaPack,
      regs[rbaPack * j + κ]! = partialReg (sv.toList.take 1) cw j κ)
    (hst : st = (sv[0]!.start + chunk) % sv[0]!.p) :
    ChunkModInvariant sv cw (1 + ([] : List Nat).length) (sv.set! 0 { sv[0]! with start := st })
      regs := by
  refine ⟨fun j hj κ hκ ↦ h j (by simpa using hj) κ hκ, Array.size_set! .., fun k hk ↦ ?_⟩
  rw [Array.getElem!_set! hk]
  by_cases hk0 : k = 0
  · subst hk0 hst
    rfl
  · rw [ite_eq_right (Ne.symm hk0), ite_eq_right (by simp; lia)]

theorem ChunkModInvariant.post {sv : Array SieveSpec} {cw : UInt64} {st : Array SieveSpec}
    {regs : Vector UInt64 (chunk * rbaPack)}
    {N : Nat} (pre : 0 < sv.size ∧ ∀ s ∈ sv, 0 < s.p ∧ s.stop = s.p)
    (h : ChunkModInvariant sv cw (1 + (ForIn.toList [1:N]).length) st regs) (hN : N = sv.size) :
    (∀ j < chunk, ∀ κ < rbaPack, regs[rbaPack * j + κ]! = partialReg sv.toList cw j κ) ∧
      st.toList = sv.toList.map (SieveSpec.advance chunk) := by
  have hK : 1 + (ForIn.toList [1:N]).length = sv.size := by
    rw [Std.Legacy.Range.length_toList]; lia
  rw [hK] at h
  refine ⟨fun j hj κ hκ ↦ by rw [h.1 j hj κ hκ, List.take_of_length_le (by simp)], ?_⟩
  refine List.ext_getElem (by simp [h.2.1]) fun k hk1 hk2 ↦ ?_
  have hk : k < sv.size := by simpa [h.2.1] using hk1
  rw [Array.getElem_toList, List.getElem_map, Array.getElem_toList, ← getElem!_pos st k hk1,
    h.2.2 k hk, ite_eq_left hk, getElem!_pos sv k hk]

theorem ChunkModInvariant.chunkAndInvariant {sv : Array SieveSpec} {cw : UInt64} {cur N : Nat}
    {pref suff : List Nat} {st : Array SieveSpec} {regs : Vector UInt64 (chunk * rbaPack)}
    (hl : ForIn.toList [1:N] = pref ++ cur :: suff)
    (h : ChunkModInvariant sv cw (1 + pref.length) st regs) :
    ChunkAndInvariant sv cw cur ([] : List Nat).length regs := by
  have hc := Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hl
  intro j hj κ hκ
  rw [h.1 j hj κ hκ, hc]
  simp

/-- An and of the modulus `K`, whose start is still where it was. -/
theorem ChunkAndInvariant.append_andBitArray {sv : Array SieveSpec} {cw : UInt64} {K cur N : Nat}
    {pref' suff' pref suff : List Nat} {st : Array SieveSpec}
    {regs regs0 : Vector UInt64 (chunk * rbaPack)}
    (hl' : ForIn.toList [1:N] = pref' ++ K :: suff')
    (hmod : ChunkModInvariant sv cw (1 + pref'.length) st regs0)
    (hl : ForIn.toList [0:chunk] = pref ++ cur :: suff)
    (h : ChunkAndInvariant sv cw K pref.length regs) (hN : N = sv.size) :
    ChunkAndInvariant sv cw K (pref ++ [cur]).length
      (andBitArray regs cur st[K]!.row (st[K]!.start + cur)) := by
  have hK := Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hl'
  have hKs := hN ▸ Std.Legacy.Range.lt_of_toList_eq_append_cons hl'
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have hst : st[K]! = sv[K]! := by rw [hmod.2.2 K hKs, ite_eq_right (by lia)]
  intro j hj κ hκ
  rw [getElem!_andBitArray _ _ _ _ (Nat.mul_add_lt_mul_of_lt_of_lt' hj hκ),
    Nat.mul_add_div rbaPack_pos, Nat.div_eq_of_lt hκ, Nat.add_zero, Nat.mul_add_mod,
    Nat.mod_eq_of_lt hκ, List.length_append, List.length_singleton]
  split
  · subst_vars
    rw [h _ hj κ hκ, hst, ite_eq_right (by lia), ite_eq_left (by lia), partialReg_take_succ hKs]
  · rw [h j hj κ hκ]
    congr 2
    split <;> split <;> first | rfl | lia

theorem chunkSieve_pre_cur {sv st : Array SieveSpec} {cw : UInt64} {cur N : Nat}
    {pref suff : List Nat} {regs : Vector UInt64 (chunk * rbaPack)}
    (pre : 0 < sv.size ∧ ∀ s ∈ sv, 0 < s.p ∧ s.stop = s.p)
    (hl : ForIn.toList [1:N] = pref ++ cur :: suff)
    (hmod : ChunkModInvariant sv cw (1 + pref.length) st regs) (hN : N = sv.size) :
    0 < st[cur]!.p ∧ st[cur]!.stop = st[cur]!.p := by
  have hKs := hN ▸ Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  have hK := Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hl
  rw [hmod.2.2 cur hKs, ite_eq_right (by lia)]
  exact pre.2 _ (Array.getElem!_mem hKs)

/-- The ands of the modulus `cur` done: its start moves on. -/
theorem ChunkAndInvariant.next {sv : Array SieveSpec} {cw : UInt64} {cur st' N : Nat}
    {pref suff : List Nat} {st : Array SieveSpec} {regs regs0 : Vector UInt64 (chunk * rbaPack)}
    (hl : ForIn.toList [1:N] = pref ++ cur :: suff)
    (hmod : ChunkModInvariant sv cw (1 + pref.length) st regs0)
    (h : ChunkAndInvariant sv cw cur (ForIn.toList [0:chunk]).length regs)
    (hst' : st' = (st[cur]!.start + chunk) % st[cur]!.p) (hN : N = sv.size) :
    ChunkModInvariant sv cw (1 + (pref ++ [cur]).length)
      (st.set! cur { st[cur]! with start := st' }) regs := by
  have hK := Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hl
  have hKs := hN ▸ Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  have hcur : st[cur]! = sv[cur]! := by rw [hmod.2.2 cur hKs, ite_eq_right (by lia)]
  rw [List.length_append, List.length_singleton, ← Nat.add_assoc, hK]
  refine ⟨fun j hj κ hκ ↦ ?_, by rw [Array.size_set!, hmod.2.1], fun k hk ↦ ?_⟩
  · rw [h j hj κ hκ, ite_eq_left (by simpa using hj)]
  · rw [Array.getElem!_set! (by rwa [hmod.2.1])]
    by_cases hkc : cur = k
    · subst hkc hst'
      rw [ite_eq_left rfl, ite_eq_left (by lia), hcur]
      rfl
    · rw [ite_eq_right hkc, hmod.2.2 k hk]
      congr 1
      exact propext ⟨fun h ↦ by lia, fun h ↦ by lia⟩

attribute [local irreducible] ChunkModInvariant ChunkAndInvariant in
/-- The registers of a chunk hold the class word and-ed with the rows of all the moduli of the
local array from their starts on (`Ratpoints.Sieve.partialReg`), and the starts move on by the
chunk and back into the first `p` bit arrays of the rows (`Ratpoints.Sieve.wrapStart_spec`). -/
@[spec]
theorem chunkSieve_spec (sv : Array SieveSpec) (cw : UInt64) :
    ⦃ 0 < sv.size ∧ ∀ s ∈ sv, 0 < s.p ∧ s.stop = s.p ⦄ chunkSieve sv cw
    ⦃ fun r ↦ (∀ j < chunk, ∀ κ < rbaPack, r.1[rbaPack * j + κ]! = partialReg sv.toList cw j κ) ∧
      r.2.toList = sv.toList.map (SieveSpec.advance chunk) ⦄ := by
  vcgen [chunkSieve] invariants
  | inv1 => fun done _ regs ↦ ∀ j < done.length, ∀ κ < rbaPack,
      regs[rbaPack * j + κ]! = partialReg (sv.toList.take 1) cw j κ
  | inv2 => fun done _ s ↦ ChunkModInvariant sv cw (1 + done.length) s.1 s.2
  | inv3 _ _ k _ _ _ _ _ => fun done _ regs ↦ ChunkAndInvariant sv cw k done.length regs
  all_goals first
    | exact absurd ‹_ < ([] : List Nat).length› (Nat.not_lt_zero _)
    | exact chunkSieve_pre_zero ‹_›
    | exact chunkModInvariant_init ‹_› ‹_›
    | exact ChunkModInvariant.post ‹_› ‹_› (Array.size_set! ..)
    | exact ChunkModInvariant.chunkAndInvariant ‹_› ‹_›
    | exact chunkSieve_pre_cur ‹_› ‹_› ‹_› (Array.size_set! ..)
    | exact ChunkAndInvariant.next ‹_› ‹_› ‹_› ‹_› (Array.size_set! ..)
    | exact ChunkAndInvariant.append_andBitArray ‹_› ‹_› ‹_› ‹_› (Array.size_set! ..)
    | exact getElem!_loadBitArray_chunk ‹_› ‹_› ‹_›

/-! ### The whole chunks of a piece -/

theorem walkFits_of_toList_eq_map {sv sv' : Array SieveSpec} (h : ∀ s ∈ sv, s.WalkFits) {c : Nat}
    (h' : sv'.toList = sv.toList.map (·.advance c)) : ∀ s ∈ sv', s.WalkFits := by
  intro s hs
  rw [← Array.mem_toList_iff, h', List.mem_map] at hs
  obtain ⟨s0, hs0, rfl⟩ := hs
  exact (h s0 (Array.mem_toList_iff.mp hs0)).advance c

/-- The invariant of the loop of `Ratpoints.Sieve.andChunks` over the chunks, on the local array of
the sieve specs, the words of the piece and the first bit array `c` of the next chunk: `c` a
multiple of the chunk up to `full`, the starts moved on by `c`, and the words of the bit arrays
below `c` those that the first stage reads from the starts of `sv`, the others as in `surv`. -/
def AndChunksInvariant (sv : Array SieveSpec) (cw : UInt64) (full : Nat) {m : Nat}
    (surv : Vector UInt64 m) :
    Std.WP.WhileInvariant (Array SieveSpec × Vector UInt64 m × Nat) Prop :=
  .mk fun exit s ↦ s.2.2 % chunk = 0 ∧ s.2.2 ≤ full ∧ (exit = true → full ≤ s.2.2) ∧
    s.1.toList = sv.toList.map (·.advance s.2.2) ∧
    ∀ y < m, s.2.1[y]! = if y < s.2.2 * rbaPack then andFrom sv.toList cw y else surv[y]!

/-- The invariant of the stores of a chunk from the bit array `c` on into the words of the piece,
after `d` of them. -/
def StoreChunkInvariant (sv : Array SieveSpec) (cw : UInt64) (c d : Nat) {m : Nat}
    (surv surv' : Vector UInt64 m) : Prop :=
  ∀ y < m, surv'[y]! = if y < (c + d) * rbaPack then andFrom sv.toList cw y else surv[y]!

theorem andChunksInvariant_init {sv : Array SieveSpec} {cw : UInt64} {full m : Nat}
    (surv : Vector UInt64 m) (pre : (∀ s ∈ sv, s.WalkFits) ∧ 0 < sv.size ∧ full % chunk = 0) :
    AndChunksInvariant sv cw full surv false (sv, surv, 0) := by
  refine ⟨Nat.zero_mod _, Nat.zero_le _, nofun, ?_, fun y _ ↦ by simp⟩
  exact (map_advance_zero fun s hs ↦ pre.1 s (Array.mem_toList_iff.mp hs)).symm

theorem chunkSieve_pre_of_andChunksInvariant {sv sv' : Array SieveSpec} {cw : UInt64}
    {full m c mb : Nat}
    {surv surv' : Vector UInt64 m} (pre : (∀ s ∈ sv, s.WalkFits) ∧ 0 < sv.size ∧ full % chunk = 0)
    (h : full - c = mb ∧ AndChunksInvariant sv cw full surv false (sv', surv', c)) :
    0 < sv'.size ∧ ∀ s ∈ sv', 0 < s.p ∧ s.stop = s.p := by
  have hl := h.2.2.2.2.1
  have hs : sv'.size = sv.size := by rw [← Array.length_toList, hl]; simp
  exact ⟨hs ▸ pre.2.1, fun s hs ↦ by
    have := walkFits_of_toList_eq_map pre.1 hl s hs
    exact ⟨this.pos, this.stop_eq⟩⟩

theorem storeChunkInvariant_init {sv sv' : Array SieveSpec} {cw : UInt64} {full m c mb : Nat}
    {surv surv' : Vector UInt64 m}
    (h : full - c = mb ∧ AndChunksInvariant sv cw full surv false (sv', surv', c)) :
    StoreChunkInvariant sv cw c ([] : List Nat).length surv surv' :=
  fun y hy ↦ by simpa using h.2.2.2.2.2 y hy

/-- A store of a register of the chunk from the bit array `c` on into the words of the piece. -/
theorem StoreChunkInvariant.append_storeBitArray {sv sv' sv'' : Array SieveSpec} {cw : UInt64}
    {full m c mb cur : Nat}
    {pref suff : List Nat} {surv surv0 surv' : Vector UInt64 m}
    {regs : Vector UInt64 (chunk * rbaPack)}
    (pre : (∀ s ∈ sv, s.WalkFits) ∧ 0 < sv.size ∧ full % chunk = 0)
    (hc : full - c = mb ∧ AndChunksInvariant sv cw full surv false (sv', surv0, c))
    (hr : (∀ j < chunk, ∀ κ < rbaPack, regs[rbaPack * j + κ]! = partialReg sv'.toList cw j κ) ∧
      sv''.toList = sv'.toList.map (SieveSpec.advance chunk))
    (hl : ForIn.toList [0:chunk] = pref ++ cur :: suff)
    (h : StoreChunkInvariant sv cw c pref.length surv surv') :
    StoreChunkInvariant sv cw c (pref ++ [cur]).length surv
      (storeBitArray surv' (c + cur) regs cur) := by
  have hd := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have hdl := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  have hsv : sv'.toList = sv.toList.map (·.advance c) := hc.2.2.2.2.1
  have hw := walkFits_of_toList_eq_map pre.1 hsv
  intro y hy
  have hyq := Nat.div_add_mod y rbaPack
  rw [getElem!_storeBitArray _ _ _ _ hy, h y hy, List.length_append, List.length_singleton]
  split
  · rename_i hyc
    rw [hr.1 cur hdl _ (Nat.mod_lt _ rbaPack_pos),
      partialReg_eq_andFrom (fun s hs ↦ hw s (Array.mem_toList_iff.mp hs)) _ hdl
        (Nat.mod_lt _ rbaPack_pos), hsv, andFrom_map_advance,
      ite_eq_left ((Nat.div_lt_iff_lt_mul rbaPack_pos).mp (by lia))]
    congr 1
    rw [hyc] at hyq
    lia
  · simp only [← Nat.div_lt_iff_lt_mul rbaPack_pos]
    split <;> split <;> first | rfl | lia

/-- A chunk done: the starts move on by the chunk, and the words of its bit arrays are stored. -/
theorem AndChunksInvariant.add_chunk {sv sv' sv'' : Array SieveSpec} {cw : UInt64}
    {full m c mb : Nat}
    {surv surv0 surv' : Vector UInt64 m} {regs : Vector UInt64 (chunk * rbaPack)}
    (pre : (∀ s ∈ sv, s.WalkFits) ∧ 0 < sv.size ∧ full % chunk = 0)
    (hc : full - c = mb ∧ AndChunksInvariant sv cw full surv false (sv', surv0, c))
    (hcl : c < full)
    (hr : (∀ j < chunk, ∀ κ < rbaPack, regs[rbaPack * j + κ]! = partialReg sv'.toList cw j κ) ∧
      sv''.toList = sv'.toList.map (SieveSpec.advance chunk))
    (hs : StoreChunkInvariant sv cw c (ForIn.toList [0:chunk]).length surv surv') :
    full - (c + chunk) < mb ∧
      AndChunksInvariant sv cw full surv false (sv'', surv', c + chunk) := by
  obtain ⟨rfl, hcm, -, -, hsv, -⟩ := hc
  have := Nat.le_of_lt_add_of_dvd (Nat.add_lt_add_right hcl chunk)
    (Nat.dvd_add (Nat.dvd_of_mod_eq_zero hcm) (Nat.dvd_refl chunk)) (Nat.dvd_of_mod_eq_zero pre.2.2)
  refine ⟨by lia [chunk_pos], by rw [Nat.add_mod_right, hcm], this, nofun, ?_,
    fun y hy ↦ by simpa using hs y hy⟩
  change sv''.toList = sv.toList.map (·.advance (c + chunk))
  rw [hr.2, hsv, List.map_map]
  exact List.map_congr_left fun s _ ↦ s.advance_advance c chunk

theorem AndChunksInvariant.exit {sv sv' : Array SieveSpec} {cw : UInt64} {full m c mb : Nat}
    {surv surv' : Vector UInt64 m}
    (h : full - c = mb ∧ AndChunksInvariant sv cw full surv false (sv', surv', c))
    (hcl : ¬c < full) : AndChunksInvariant sv cw full surv true (sv', surv', c) :=
  ⟨h.2.1, h.2.2.1, fun _ ↦ by lia, h.2.2.2.2⟩

theorem AndChunksInvariant.post {sv sv' : Array SieveSpec} {cw : UInt64} {full m c : Nat}
    {surv surv' : Vector UInt64 m} (h : AndChunksInvariant sv cw full surv true (sv', surv', c)) :
    (∀ y < m, surv'[y]! = if y < full * rbaPack then andFrom sv.toList cw y else surv[y]!) ∧
      sv'.toList = sv.toList.map (·.advance full) := by
  obtain ⟨-, hcf, hex, hsv, hs⟩ := h
  obtain rfl : c = full := Nat.le_antisymm hcf (hex rfl)
  exact ⟨hs, hsv⟩

attribute [local irreducible] AndChunksInvariant StoreChunkInvariant in
open Std.WP Lean.Order in
/-- The whole chunks below `full`, a multiple of the chunk, store into the words of their bit arrays
those that the first stage reads from the starts of the local array (`Ratpoints.Sieve.andFrom`),
and move the starts on by `full`; the other words stay as they are. -/
@[spec]
theorem andChunks_spec (sv : Array SieveSpec) (cw : UInt64) (full : Nat) {m : Nat}
    (surv : Vector UInt64 m) :
    ⦃ (∀ s ∈ sv, s.WalkFits) ∧ 0 < sv.size ∧ full % chunk = 0 ⦄ andChunks sv cw full surv
    ⦃ fun r ↦ (∀ y < m, r.1[y]! = if y < full * rbaPack then andFrom sv.toList cw y else surv[y]!) ∧
      r.2.toList = sv.toList.map (·.advance full) ⦄ := by
  vcgen [andChunks] invariants
  | inv1 => AndChunksInvariant sv cw full surv
  | inv2 => Variant.ofMeasure fun s : Array SieveSpec × Vector UInt64 m × Nat ↦ full - s.2.2
  | inv3 _ _ _ c _ _ _ _ => fun done _ surv' ↦ StoreChunkInvariant sv cw c done.length surv surv'
  all_goals try simp only [Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure,
    Variant.evalsBelow_ofMeasure_nat, meet_prop_eq_and, ofProp_prop_eq] at *
  all_goals first
    | exact andChunksInvariant_init surv ‹_›
    | exact AndChunksInvariant.post ‹_›
    | exact chunkSieve_pre_of_andChunksInvariant ‹_› ‹_›
    | exact storeChunkInvariant_init ‹_›
    | exact StoreChunkInvariant.append_storeBitArray ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact AndChunksInvariant.add_chunk ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact AndChunksInvariant.exit ‹_› ‹_›

/-! ### One leg over the tail -/

/-- The invariant of the loop of the ands of the modulus `K` in a leg of `w` registers from `off`
on, after the registers below `c`. -/
def LegAndInvariant (sv : Array SieveSpec) (cw : UInt64) (w off K c : Nat)
    (reg : Vector UInt64 (8 * rbaPack)) : Prop :=
  ∀ i < w, ∀ κ < rbaPack,
    reg[rbaPack * i + κ]! = partialReg (sv.toList.take (if i < c then K + 1 else K)) cw (off + i) κ

/-- The invariant of the stores of a leg after the registers below `c`: the bit arrays
`base + off + i`, `i < c`, of the piece hold the registers. -/
def LegStoreInvariant (sv : Array SieveSpec) (cw : UInt64) {m : Nat} (surv : Vector UInt64 m)
    (base off c : Nat) (surv' : Vector UInt64 m) : Prop :=
  ∀ y < m, surv'[y]! = if base + off ≤ y / rbaPack ∧ y / rbaPack < base + off + c then
    partialReg sv.toList cw (y / rbaPack - base) (y % rbaPack) else surv[y]!

theorem getElem!_loadBitArray_leg {sv : Array SieveSpec} {cw : UInt64} {w off cur : Nat}
    {pref suff : List Nat}
    {reg : Vector UInt64 (8 * rbaPack)} (pre : 0 < sv.size ∧ w ≤ 8)
    (hl : ForIn.toList [0:w] = pref ++ cur :: suff)
    (h : ∀ i < pref.length, ∀ κ < rbaPack,
      reg[rbaPack * i + κ]! = partialReg (sv.toList.take 1) cw (off + i) κ) :
    ∀ i < (pref ++ [cur]).length, ∀ κ < rbaPack,
      (loadBitArray reg cur cw sv[0]!.row (sv[0]!.start + off + cur))[rbaPack * i + κ]! =
        partialReg (sv.toList.take 1) cw (off + i) κ := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have hcl := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  intro i hi κ hκ
  rw [List.length_append, List.length_singleton] at hi
  rw [getElem!_loadBitArray _ _ _ _ _ (Nat.mul_add_lt_mul_of_lt_of_lt' (by lia) hκ),
    Nat.mul_add_div rbaPack_pos, Nat.div_eq_of_lt hκ, Nat.add_zero, Nat.mul_add_mod,
    Nat.mod_eq_of_lt hκ]
  split
  · subst_vars
    rw [partialReg_take_succ pre.1, Nat.add_assoc]
    rfl
  · exact h i (by lia) κ hκ

theorem LegAndInvariant.append_andBitArray {sv : Array SieveSpec} {cw : UInt64} {w off K cur : Nat}
    {pref' suff' pref suff : List Nat} {reg : Vector UInt64 (8 * rbaPack)}
    (pre : 0 < sv.size ∧ w ≤ 8)
    (hl' : ForIn.toList [1:sv.size] = pref' ++ K :: suff')
    (hl : ForIn.toList [0:w] = pref ++ cur :: suff)
    (h : LegAndInvariant sv cw w off K pref.length reg) :
    LegAndInvariant sv cw w off K (pref ++ [cur]).length
      (andBitArray reg cur sv[K]!.row (sv[K]!.start + off + cur)) := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have hKs := Std.Legacy.Range.lt_of_toList_eq_append_cons hl'
  intro i hi κ hκ
  rw [getElem!_andBitArray _ _ _ _ (Nat.mul_add_lt_mul_of_lt_of_lt' (by lia) hκ),
    Nat.mul_add_div rbaPack_pos, Nat.div_eq_of_lt hκ, Nat.add_zero, Nat.mul_add_mod,
    Nat.mod_eq_of_lt hκ, List.length_append, List.length_singleton]
  split
  · subst_vars
    rw [h _ hi κ hκ, ite_eq_right (by lia), ite_eq_left (by lia), partialReg_take_succ hKs,
      Nat.add_assoc]
  · rw [h i hi κ hκ]
    congr 2
    split <;> split <;> first | rfl | lia

theorem LegAndInvariant.next {sv : Array SieveSpec} {cw : UInt64} {w off cur : Nat}
    {pref suff : List Nat} {reg : Vector UInt64 (8 * rbaPack)}
    (hl : ForIn.toList [1:sv.size] = pref ++ cur :: suff)
    (h : LegAndInvariant sv cw w off cur (ForIn.toList [0:w]).length reg) :
    ∀ i < w, ∀ κ < rbaPack, reg[rbaPack * i + κ]! =
      partialReg (sv.toList.take (1 + (pref ++ [cur]).length)) cw (off + i) κ := by
  have hK := Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hl
  intro i hi κ hκ
  rw [h i hi κ hκ, ite_eq_left (by simpa using hi), List.length_append, List.length_singleton,
    ← Nat.add_assoc, hK]

theorem legAndInvariant_init {sv : Array SieveSpec} {cw : UInt64} {w off cur : Nat}
    {pref suff : List Nat} {reg : Vector UInt64 (8 * rbaPack)}
    (hl : ForIn.toList [1:sv.size] = pref ++ cur :: suff)
    (h : ∀ i < w, ∀ κ < rbaPack, reg[rbaPack * i + κ]! =
      partialReg (sv.toList.take (1 + pref.length)) cw (off + i) κ) :
    LegAndInvariant sv cw w off cur ([] : List Nat).length reg := by
  have hK := Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hl
  intro i hi κ hκ
  rw [h i hi κ hκ, hK]
  simp

-- After the load loop of `Ratpoints.Sieve.tailLeg`, the registers hold the class word and-ed with
-- the row of the first modulus, in the form the loop over the further moduli starts from.
private theorem leg_load_done {sv : Array SieveSpec} {cw : UInt64} {w off i κ : Nat}
    {reg : Vector UInt64 (8 * rbaPack)}
    (h : ∀ i < (ForIn.toList [0:w]).length, ∀ κ < rbaPack,
      reg[rbaPack * i + κ]! = partialReg (sv.toList.take 1) cw (off + i) κ) (hi : i < w)
    (hκ : κ < rbaPack) :
    reg[rbaPack * i + κ]! =
      partialReg (sv.toList.take (1 + ([] : List Nat).length)) cw (off + i) κ :=
  h i (by simpa using hi) κ hκ

theorem LegStoreInvariant.append_storeBitArray {sv : Array SieveSpec} {cw : UInt64} {m : Nat}
    {surv surv' : Vector UInt64 m} {reg : Vector UInt64 (8 * rbaPack)} {w off base cur : Nat}
    {pref suff : List Nat}
    (hreg : ∀ i < w, ∀ κ < rbaPack, reg[rbaPack * i + κ]! =
      partialReg (sv.toList.take (1 + (ForIn.toList [1:sv.size]).length)) cw (off + i) κ)
    (pre : 0 < sv.size ∧ w ≤ 8) (hl : ForIn.toList [0:w] = pref ++ cur :: suff)
    (h : LegStoreInvariant sv cw surv base off pref.length surv') :
    LegStoreInvariant sv cw surv base off (pref ++ [cur]).length
      (storeBitArray surv' (base + off + cur) reg cur) := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have hcl := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  have hK : 1 + (ForIn.toList [1:sv.size]).length = sv.size := by
    rw [Std.Legacy.Range.length_toList]; lia
  intro y hy
  rw [getElem!_storeBitArray _ _ _ _ hy, h y hy, List.length_append, List.length_singleton]
  split
  · rw [hreg cur hcl _ (Nat.mod_lt _ rbaPack_pos), hK, List.take_of_length_le (by simp),
      ite_eq_left (by lia)]
    congr 1
    lia
  · split <;> split <;> first | rfl | lia

theorem LegStoreInvariant.post {sv : Array SieveSpec} {cw : UInt64} {m : Nat}
    {surv surv' : Vector UInt64 m} {w base off : Nat}
    (h : LegStoreInvariant sv cw surv base off (ForIn.toList [0:w]).length surv') :
    ∀ y < m, surv'[y]! = if base + off ≤ y / rbaPack ∧ y / rbaPack < base + off + w then
      partialReg sv.toList cw (y / rbaPack - base) (y % rbaPack) else surv[y]! := by
  simpa [LegStoreInvariant, Std.Legacy.Range.length_toList] using h

theorem legStoreInvariant_nil (sv : Array SieveSpec) (cw : UInt64) {m : Nat}
    (surv : Vector UInt64 m) (base off : Nat) :
    LegStoreInvariant sv cw surv base off ([] : List Nat).length surv := fun y _ ↦
  (ite_eq_right (by simp)).symm

attribute [local irreducible] LegAndInvariant LegStoreInvariant in
/-- A leg of `w ≤ 8` registers from `off` on stores into the bit arrays `base + off + i`, `i < w`,
the class word and-ed with the rows of all the moduli of the local array at their starts plus
`off + i`; the other words stay as they are. -/
@[spec]
theorem tailLeg_spec (w off : Nat) {m : Nat} (surv : Vector UInt64 m) (base : Nat) (cw : UInt64)
    (sv : Array SieveSpec) :
    ⦃ 0 < sv.size ∧ w ≤ 8 ⦄ tailLeg w off surv base cw sv
    ⦃ fun surv' ↦ ∀ y < m, surv'[y]! =
        if base + off ≤ y / rbaPack ∧ y / rbaPack < base + off + w then
          partialReg sv.toList cw (y / rbaPack - base) (y % rbaPack)
        else surv[y]! ⦄ := by
  vcgen [tailLeg] invariants
  | inv1 => fun done _ reg ↦ ∀ i < done.length, ∀ κ < rbaPack,
      reg[rbaPack * i + κ]! = partialReg (sv.toList.take 1) cw (off + i) κ
  | inv2 => fun done _ reg ↦ ∀ i < w, ∀ κ < rbaPack,
      reg[rbaPack * i + κ]! = partialReg (sv.toList.take (1 + done.length)) cw (off + i) κ
  | inv3 => fun done _ surv' ↦ LegStoreInvariant sv cw surv base off done.length surv'
  | inv4 _ _ _ _ k _ _ _ _ => fun done _ reg ↦ LegAndInvariant sv cw w off k done.length reg
  all_goals first
    | exact absurd ‹_ < ([] : List Nat).length› (Nat.not_lt_zero _)
    | exact leg_load_done ‹_› ‹_› ‹_›
    | exact legStoreInvariant_nil sv cw surv base off
    | exact LegStoreInvariant.post ‹_› _ ‹_›
    | exact LegStoreInvariant.append_storeBitArray ‹_› ‹_› ‹_› ‹_›
    | exact legAndInvariant_init ‹_› ‹_›
    | exact LegAndInvariant.next ‹_› ‹_›
    | exact LegAndInvariant.append_andBitArray ‹_› ‹_› ‹_› ‹_›
    | exact getElem!_loadBitArray_leg ‹_› ‹_› ‹_›

/-! ### The tail -/

/-- The four guarded legs over the tail as nested conditional values: the first stage over the
tail of `t = n - full` bit arrays, the legs of 8, 4, 2 and 1 bit arrays from the offsets `0`,
`t &&& 8`, `t &&& 12` and `t &&& 14` on. -/
theorem run_tailLegs (sv : Array SieveSpec) (cw : UInt64) (full n : Nat) {m : Nat}
    (surv : Vector UInt64 m) : Id.run (tailLegs sv cw full n surv) =
      let t := n - full
      let s1 := if 8 < chunk ∧ t &&& 8 ≠ 0 then Id.run (tailLeg 8 0 surv full cw sv) else surv
      let s2 := if 4 < chunk ∧ t &&& 4 ≠ 0 then Id.run (tailLeg 4 (t &&& 8) s1 full cw sv) else s1
      let s3 := if 2 < chunk ∧ t &&& 2 ≠ 0 then Id.run (tailLeg 2 (t &&& 12) s2 full cw sv) else s2
      if t &&& 1 ≠ 0 then Id.run (tailLeg 1 (t &&& 14) s3 full cw sv) else s3 := by
  simp only [tailLegs]
  by_cases h1 : 8 < chunk ∧ ¬n - full &&& 8 = 0 <;>
    by_cases h2 : 4 < chunk ∧ ¬n - full &&& 4 = 0 <;>
    by_cases h3 : 2 < chunk ∧ ¬n - full &&& 2 = 0 <;> by_cases h4 : n - full &&& 1 = 0 <;>
    simp only [ne_eq, h1, h2, h3, h4, not_true_eq_false, not_false_eq_true, and_self,
      ↓reduceIte] <;>
    rfl

/-- The words of the bit arrays `full, …, full + u - 1` of the tail are the class word and-ed with
the rows of all the moduli of the local array at their starts plus their place in the tail, and the
other words as in `surv`. -/
def TailDone (sv : Array SieveSpec) (cw : UInt64) (full u : Nat) {m : Nat}
    (surv surv' : Vector UInt64 m) : Prop :=
  ∀ y < m, surv'[y]! = if full ≤ y / rbaPack ∧ y / rbaPack < full + u then
    partialReg sv.toList cw (y / rbaPack - full) (y % rbaPack) else surv[y]!

theorem tailDone_zero (sv : Array SieveSpec) (cw : UInt64) (full : Nat) {m : Nat}
    (surv : Vector UInt64 m) : TailDone sv cw full 0 surv surv :=
  fun y _ ↦ (ite_eq_right (by lia)).symm

/-- A guarded leg of `w` bit arrays from the offset `u` on, which runs exactly when bit `w` of `t`
is set, does the bit arrays from `full + u` on, `t &&& w` of them. -/
theorem TailDone.leg {sv : Array SieveSpec} {cw : UInt64} {full u w t m : Nat}
    {surv s : Vector UInt64 m} {g : Prop} [Decidable g] (h : TailDone sv cw full u surv s)
    (hs : 0 < sv.size) (hw : w ≤ 8) (hg : g ↔ t &&& w ≠ 0) (htw : t &&& w ≠ 0 → t &&& w = w) :
    TailDone sv cw full (u + (t &&& w)) surv
      (if g then Id.run (tailLeg w u s full cw sv) else s) := by
  split
  · rename_i hgt
    have hleg := Std.WP.Id.of_run_eq_wp rfl _ ((tailLeg_spec w u s full cw sv).le_wp ⟨hs, hw⟩)
    rw [htw (hg.mp hgt)]
    intro y hy
    rw [hleg y hy, h y hy]
    by_cases h1 : full + u ≤ y / rbaPack ∧ y / rbaPack < full + u + w
    · rw [ite_eq_left h1, ite_eq_left (by lia)]
    · rw [ite_eq_right h1]
      by_cases h2 : full ≤ y / rbaPack ∧ y / rbaPack < full + u
      · rw [ite_eq_left h2, ite_eq_left (by lia)]
      · rw [ite_eq_right h2, ite_eq_right (by lia)]
  · rename_i hgt
    rwa [(Decidable.of_not_not (mt hg.mpr hgt) : t &&& w = 0), Nat.add_zero]

-- The bits of a tail of `t < 16` bit arrays: each leg that runs has its width, which is at most
-- `t`, and the offsets of the legs are the sums of the widths of those before them.
private theorem tail_bits : ∀ t < 16,
    (t &&& 8 ≠ 0 → 8 ≤ t ∧ t &&& 8 = 8) ∧ (t &&& 4 ≠ 0 → 4 ≤ t ∧ t &&& 4 = 4) ∧
      (t &&& 2 ≠ 0 → 2 ≤ t ∧ t &&& 2 = 2) ∧ (t &&& 1 ≠ 0 → t &&& 1 = 1) ∧
      0 + (t &&& 8) = t &&& 8 ∧ (t &&& 8) + (t &&& 4) = t &&& 12 ∧
      (t &&& 12) + (t &&& 2) = t &&& 14 ∧ (t &&& 14) + (t &&& 1) = t := by
  decide

/-- The legs over the tail of `t = n - full < chunk ≤ 16` bit arrays do its bit arrays
`full, …, n - 1`: the class word and-ed with the rows of all the moduli of the local array at their
starts plus the place in the tail (`Ratpoints.Sieve.partialReg`); the other words stay as they
are. -/
@[spec]
theorem tailLegs_spec (sv : Array SieveSpec) (cw : UInt64) (full n : Nat) {m : Nat}
    (surv : Vector UInt64 m) :
    ⦃ chunk ≤ 16 ∧ n - full < chunk ∧ 0 < sv.size ⦄ tailLegs sv cw full n surv
    ⦃ fun surv' ↦ TailDone sv cw full (n - full) surv surv' ⦄ := ⟨fun pre ↦ by
  obtain ⟨f8, f4, f2, f1, e1, e2, e3, e4⟩ := tail_bits (n - full) (by lia)
  have h1 := (tailDone_zero sv cw full surv).leg pre.2.2 (by decide)
    (and_iff_right_of_imp fun h ↦ Nat.lt_of_le_of_lt (f8 h).1 pre.2.1) (f8 · |>.2)
  rw [e1] at h1
  have h2 := h1.leg pre.2.2 (by decide)
    (and_iff_right_of_imp fun h ↦ Nat.lt_of_le_of_lt (f4 h).1 pre.2.1) (f4 · |>.2)
  rw [e2] at h2
  have h3 := h2.leg pre.2.2 (by decide)
    (and_iff_right_of_imp fun h ↦ Nat.lt_of_le_of_lt (f2 h).1 pre.2.1) (f2 · |>.2)
  rw [e3] at h3
  have h4 := h3.leg (g := n - full &&& 1 ≠ 0) pre.2.2 (by decide) Iff.rfl f1
  rw [e4] at h4
  change TailDone sv cw full (n - full) surv (Id.run (tailLegs sv cw full n surv))
  rw [run_tailLegs]
  exact h4⟩

/-! ### The chunked first stage -/

theorem chunkStarts_pre {specs : List SieveSpec} {mgs : List Nat} {small : Bool} {w0 : Int}
    {n : Nat}
    (pre : chunk ≤ 16 ∧ (∀ s ∈ specs, s.Fits) ∧ mgs = specs.map (magic ·.p) ∧
      SmallFits small w0 (w0 + n)) :
    (∀ s ∈ specs, s.Fits) ∧ mgs = specs.map (magic ·.p) ∧ SmallFits small w0 w0 :=
  ⟨pre.2.1, pre.2.2.1, pre.2.2.2.mono (Int.le_refl _) (by lia)⟩

/-- With no modulus, the bit arrays set to the class word are the words of the first stage. -/
theorem AndRowsFillInvariant.getElem!_eq_andWords {specs : List SieveSpec} {sv : Array SieveSpec}
    {cw : UInt64} {w0 : Int} {n m : Nat} {surv : Vector UInt64 m}
    (hsv : sv.toList = specs.map (·.startAt w0)) (hz : sv.size = 0)
    (h : AndRowsFillInvariant cw n (ForIn.toList [0:n]).length surv) {y : Nat}
    (hy : y < n * rbaPack) : surv[y]! = andWords specs cw w0 y := by
  have : specs = [] := by
    rw [← List.length_eq_zero_iff, ← List.length_map (f := (·.startAt w0)), ← hsv,
      Array.length_toList, hz]
  rw [h y hy (by simp), this]
  rfl

theorem walkFits_of_toList_eq_map_startAt {specs : List SieveSpec} {sv : Array SieveSpec}
    {w0 : Int} (h : ∀ s ∈ specs, s.Fits) (hsv : sv.toList = specs.map (·.startAt w0)) :
    ∀ s ∈ sv, s.WalkFits := by
  intro s hs
  rw [← Array.mem_toList_iff, hsv, List.mem_map] at hs
  obtain ⟨s0, hs0, rfl⟩ := hs
  exact (h s0 hs0).walkFits_startAt w0

theorem andChunks_pre_of_toList_eq {specs : List SieveSpec} {mgs : List Nat} {small : Bool}
    {w0 : Int} {n : Nat} {sv : Array SieveSpec}
    (pre : chunk ≤ 16 ∧ (∀ s ∈ specs, s.Fits) ∧ mgs = specs.map (magic ·.p) ∧
      SmallFits small w0 (w0 + n))
    (hsv : sv.toList = specs.map (·.startAt w0)) (hz : ¬sv.size = 0) :
    (∀ s ∈ sv, s.WalkFits) ∧ 0 < sv.size ∧ (n - n % chunk) % chunk = 0 :=
  ⟨walkFits_of_toList_eq_map_startAt pre.2.1 hsv, Nat.pos_of_ne_zero hz,
    Nat.sub_mod_eq_zero_of_mod_eq (Nat.mod_mod n chunk).symm⟩

theorem tailLegs_pre_of_toList_eq {specs : List SieveSpec} {mgs : List Nat} {small : Bool}
    {w0 : Int} {sv0 sv : Array SieveSpec} {n m : Nat} {cw : UInt64}
    {surv surv' : Vector UInt64 m}
    (pre : chunk ≤ 16 ∧ (∀ s ∈ specs, s.Fits) ∧ mgs = specs.map (magic ·.p) ∧
      SmallFits small w0 (w0 + n)) (hz : ¬sv0.size = 0)
    (hch : (∀ y < m, surv'[y]! = if y < (n - n % chunk) * rbaPack then andFrom sv0.toList cw y
        else surv[y]!) ∧ sv.toList = sv0.toList.map (SieveSpec.advance (n - n % chunk))) :
    chunk ≤ 16 ∧ n - (n - n % chunk) < chunk ∧ 0 < sv.size := by
  have hs : sv.size = sv0.size := by rw [← Array.length_toList, hch.2]; simp
  exact ⟨pre.1, by lia [Nat.mod_lt n chunk_pos], by lia⟩

/-- The bit arrays of the whole chunks and of the tail are those of the first stage. -/
theorem andRowsChunked_post {specs : List SieveSpec} {mgs : List Nat} {small : Bool}
    {cw : UInt64} {w0 : Int} {n : Nat} {sv0 sv : Array SieveSpec}
    {surv surv' surv'' : Vector UInt64 ((n + 1) * rbaPack)}
    (pre : chunk ≤ 16 ∧ (∀ s ∈ specs, s.Fits) ∧ mgs = specs.map (magic ·.p) ∧
      SmallFits small w0 (w0 + n)) (hsv : sv0.toList = specs.map (·.startAt w0))
    (hch : (∀ y < (n + 1) * rbaPack, surv'[y]! = if y < (n - n % chunk) * rbaPack then
        andFrom sv0.toList cw y else surv[y]!) ∧
      sv.toList = sv0.toList.map (SieveSpec.advance (n - n % chunk)))
    (ht : TailDone sv cw (n - n % chunk) (n - (n - n % chunk)) surv' surv'')
    {y : Nat} (hy : y < n * rbaPack) : surv''[y]! = andWords specs cw w0 y := by
  have hfit := pre.2.1
  have hw := walkFits_of_toList_eq_map (walkFits_of_toList_eq_map_startAt hfit hsv) hch.2
  have hyn : y < (n + 1) * rbaPack := Nat.lt_add_one_mul_of_lt_mul hy
  have hyl : y / rbaPack < n := (Nat.div_lt_iff_lt_mul rbaPack_pos).mpr hy
  have := Nat.mod_lt n chunk_pos
  rw [ht y hyn, ← andFrom_map_startAt (fun s hs ↦ (hfit s hs).pos), ← hsv]
  by_cases h1 : n - n % chunk ≤ y / rbaPack
  · rw [ite_eq_left ⟨h1, by lia⟩,
      partialReg_eq_andFrom (fun s hs ↦ hw s (Array.mem_toList_iff.mp hs)) _ (by lia)
        (Nat.mod_lt _ rbaPack_pos), hch.2, andFrom_map_advance, ← Nat.add_assoc,
      ← Nat.mul_add, Nat.add_sub_cancel' h1, Nat.div_add_mod]
  · rw [ite_eq_right (by lia), hch.1 y hyn,
      ite_eq_left ((Nat.div_lt_iff_lt_mul rbaPack_pos).mp (by lia))]

/-- The chunked first stage, for the arm's chunk of at most 16, leaves each word of the piece the
class word `cw` and-ed with its row words (`Ratpoints.Sieve.andWords`), as the first stage one row
at a time does (`Ratpoints.Sieve.andRows_spec`): the whole chunks and the tail read the rows from
their starts at the first word number, into the copies of their first bit arrays
(`Ratpoints.Sieve.SieveSpec.Wraps`), and with no modulus every bit array is the class word. -/
@[spec]
theorem andRowsChunked_spec (specs : List SieveSpec) (mgs : List Nat) (small : Bool)
    (cw : UInt64) (w0 : Int) (n : Nat) (surv : Vector UInt64 ((n + 1) * rbaPack)) :
    ⦃ chunk ≤ 16 ∧ (∀ s ∈ specs, s.Fits) ∧ mgs = specs.map (magic ·.p) ∧
        SmallFits small w0 (w0 + n) ⦄
    andRowsChunked specs mgs small cw w0 n surv
    ⦃ fun surv' ↦ ∀ y < n * rbaPack, surv'[y]! = andWords specs cw w0 y ⦄ := by
  vcgen [andRowsChunked] invariants
  | inv1 => fun done _ surv ↦ AndRowsFillInvariant cw n done.length surv
  all_goals first
    | exact chunkStarts_pre ‹_›
    | exact andRowsFillInvariant_zero cw n surv
    | exact AndRowsFillInvariant.getElem!_eq_andWords ‹_› ‹_› ‹_› ‹_›
    | exact AndRowsFillInvariant.append_fillBitArray ‹_› ‹_›
    | exact andChunks_pre_of_toList_eq ‹_› ‹_› ‹_›
    | exact tailLegs_pre_of_toList_eq ‹_› ‹_› ‹_›
    | exact andRowsChunked_post ‹_› ‹_› ‹_› ‹_› ‹_›

end Sieve

end Ratpoints

end

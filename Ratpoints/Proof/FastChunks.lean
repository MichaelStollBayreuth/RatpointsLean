/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Proof.FastRows

import Ratpoints.Mathlib.Algebra.Order.Field.Basic
import Ratpoints.Proof.BruteForce

/-!
# The chunks, the cut, the region and the loop over the denominators of the fast search

Facts about the loops of the fast search `Ratpoints.FastMask.fastPoints` below
`Ratpoints.FastMask.search`, for a fixed `Ratpoints.FastMask.Context`. The index of a numerator `a`
is `a + H`, a natural number; the chunk `sl` holds the indices `sl.ρ + G (sl.T₀ + t)` for
`t < sl.len`.

* The buffer of the masks changes nothing: on a buffer of size `0` each loop returns a buffer of
  size `0` and the points it adds before the points it is given. The points that a chunk, the cut
  chunks of a denominator and a denominator add (`Ratpoints.FastMask.chunkPoints`,
  `Ratpoints.FastMask.cutPoints`, `Ratpoints.FastMask.denPoints`) are those of the loop on an empty
  buffer and no points (`Ratpoints.FastMask.snd_sieveChunk`, `Ratpoints.FastMask.snd_cutChunks`,
  `Ratpoints.FastMask.snd_denStep`), so the loop over the denominators lists the points of each
  denominator in turn (`Ratpoints.FastMask.densLoop_eq`).
* Every point that a chunk adds comes from the exact check of a numerator of the chunk
  (`Ratpoints.FastMask.exists_mem_pointsOfDen_of_mem_chunkPoints`), each numerator once
  (`Ratpoints.FastMask.nodup_chunkPoints`). For a sound context
  (`Ratpoints.FastMask.Context.IsSound`: its families and tables are those of the coefficients and
  its chunks fit the families, `Ratpoints.FastMask.Slot.IsFit`) the bit of a candidate survives the
  copy of the row of the first family and the AND with the rows of the others
  (`Ratpoints.FastMask.bit_andRows_extract_of_isCandidate`), the second stage lets it pass
  (`Ratpoints.FastMask.passes_of_isCandidate`), and the exact check lists its points
  (`Ratpoints.FastMask.mem_chunkPoints_of_mem_pointsOfDen`).
* The cut of a chunk to the blocks that hold the indices from `q₁ G + r₁` to `q₂ G + r₂` keeps
  every candidate in that range (`Ratpoints.FastMask.mem_cutPoints_of_mem_pointsOfDen`).
* The region: `Ratpoints.FastMask.regionChunks` cuts the chunks to the hull of the indices of the
  intervals (`Ratpoints.FastMask.regionHull`, `Ratpoints.FastMask.regionChunks_eq`), and the hull
  holds the index of every candidate, assuming Sturm's theorem
  (`Ratpoints.FastMask.mem_Icc_regionHull_of_isCandidate`): the ends rounded by
  `Ratpoints.FastMask.roundEnd` enclose the ends of `Ratpoints.Fast.endFrac`, and the first and
  last indices of an interval (`Ratpoints.FastMask.lowIndex`, `Ratpoints.FastMask.highIndex`)
  enclose the index of every numerator `a` with `a / b` between its ends.
* A denominator: its rows are not empty for a candidate
  (`Ratpoints.FastMask.Family.IsSound.size_row_ne_zero`), so that `Ratpoints.FastMask.rowsOf`
  gives them all (`Ratpoints.FastMask.rowsOf_zero_eq_some`), and its points are those of the
  chunks of its class (`Ratpoints.FastMask.exists_mem_pointsOfDen_of_mem_denPoints`,
  `Ratpoints.FastMask.mem_denPoints_of_mem_pointsOfDen`), each once when the chunks are disjoint
  (`Ratpoints.FastMask.nodup_denPoints`).

## Main definitions

* `Ratpoints.FastMask.Context.IsSound`: the context lets every candidate through.
* `Ratpoints.FastMask.denPoints`: the points that the search adds for a denominator.
* `Ratpoints.FastMask.regionHull`: the hull of the indices of the region for a denominator.

## Main statements

* `Ratpoints.FastMask.densLoop_eq`: the loop over the denominators lists the points of each.
* `Ratpoints.FastMask.exists_mem_pointsOfDen_of_mem_denPoints`: the points of a denominator come
  from the exact check of the numerators of its chunks.
* `Ratpoints.FastMask.mem_denPoints_of_mem_pointsOfDen`: for a sound context, the points of a
  candidate of a chunk in the region are found.
* `Ratpoints.FastMask.nodup_flatMap_denPoints`: the points of distinct denominators, each once.
* `Ratpoints.FastMask.mem_Icc_regionHull_of_isCandidate`: assuming Sturm's theorem, the hull of
  the region holds the index of every candidate.
-/

@[expose] public section

/-! ### Lists and natural numbers -/

/-- `List.foldl_flip_append_eq_append` with the result as a `List.flatMap`. -/
theorem List.foldl_append_eq_flatMap_reverse_append {α β : Type*} (f : α → List β) (l : List α)
    (init : List β) : l.foldl (fun acc x ↦ f x ++ acc) init = l.reverse.flatMap f ++ init := by
  rw [List.foldl_flip_append_eq_append, List.flatMap_def, List.map_reverse]

theorem Nat.dvd_add_sub_mod_mod {m : ℕ} (hm : 0 < m) (H : ℕ) : m ∣ H + (m - H % m) % m := by
  rcases Nat.eq_zero_or_pos (H % m) with h0 | h0
  · rw [h0, Nat.sub_zero, Nat.mod_self, add_zero]
    exact Nat.dvd_of_mod_eq_zero h0
  · rw [Nat.mod_eq_of_lt (by lia)]
    exact ⟨H / m + 1, by lia [Nat.mod_lt H hm, Nat.div_add_mod H m]⟩

theorem Nat.le_add_sub_one_div_mul (m : ℕ) {q : ℕ} (hq : 0 < q) : m ≤ (m + q - 1) / q * q := by
  lia [Nat.lt_div_mul_add (a := m + q - 1) hq]

namespace Ratpoints

namespace FastMask

open BruteForce Fast Mask

/-! ### Sound contexts -/

/-- The chunk `sl` fits the families of `ctx`, whose rows are made for masks of `nb` bytes: its
class is a residue modulo the step, its mask of `sl.nb ≤ nb` bytes holds its numerators, and its
offsets are the shifts of the families to its first numerator. -/
structure Slot.IsFit (ctx : Context) (nb : ℕ) (sl : Slot) : Prop where
  /-- The class is a residue modulo the step. -/
  ρ_lt : sl.ρ < ctx.G
  /-- The mask holds the numerators of the chunk. -/
  len_le : sl.len ≤ 8 * sl.nb
  /-- The rows are long enough for the mask. -/
  nb_le : sl.nb ≤ nb
  /-- The byte offset of the row of the first family is its shift to the first numerator, in
  bytes. -/
  sh₀_eq : sl.sh₀ = ctx.fam₀.shift (((sl.ρ + ctx.G * sl.T₀ : ℕ) : ℤ) - ctx.H) / 8
  /-- The shifts of the rows of the other families are their shifts to the first numerator. -/
  sh_eq : sl.sh = ctx.fams.map (Family.shift · (((sl.ρ + ctx.G * sl.T₀ : ℕ) : ℤ) - ctx.H))

/-- The context lets every candidate through, with families made for masks of `nb` bytes: its
degree is that of `ctx.c`, its step is positive, its families and tables are those of `ctx.c`,
and its chunks fit the families. -/
structure Context.IsSound (ctx : Context) (nb : ℕ) : Prop where
  /-- The degree is that of the coefficients. -/
  d_eq : ctx.d = degree ctx.c
  /-- The step is positive. -/
  G_pos : 0 < ctx.G
  /-- The first family is sound. -/
  fam₀ : ctx.fam₀.IsSound ctx.c ctx.G nb
  /-- The other families are sound. -/
  fams : ∀ F ∈ ctx.fams, F.IsSound ctx.c ctx.G nb
  /-- The tables of the second stage are those of `ctx.c`, each with `(-H) % m`. -/
  tabs : ∀ To ∈ ctx.tabs, ∃ m > 0, To = (mkTable ctx.c ctx.d m, (m - ctx.H % m) % m)
  /-- The chunks fit the families. -/
  slots (r : ℕ) : ∀ sl ∈ ctx.slots[r]!, sl.IsFit ctx nb

theorem Family.IsSound.size_row_ne_zero {c : List ℤ} {G nb : ℕ} {F : Family}
    (hF : F.IsSound c G nb) {a : ℤ} {b : ℕ} (hc : IsCandidate c a b) :
    F.rows[b % F.M]!.size ≠ 0 := by
  rw [hF.size_row_of_isCandidate hc]
  lia [hF.odd]

/-! ### The second stage -/

/-- The index `x = a + H` of `a`, shifted by `(-H) % m`, is `a` modulo `m`. -/
theorem add_sub_mod_mod_eq_toNat {m : ℕ} (hm : 0 < m) {H x : ℕ} {a : ℤ}
    (hx : (x : ℤ) = a + H) : (x + (m - H % m) % m) % m = (a % (m : ℤ)).toNat := by
  refine natMod_eq_toNat_of_dvd ?_
  obtain ⟨k, hk⟩ := Nat.dvd_add_sub_mod_mod hm H
  exact ⟨-k, by push_cast; lia⟩

theorem passes_of_isCandidate {ctx : Context} {nb : ℕ} (hctx : ctx.IsSound nb) {a : ℤ}
    {b x : ℕ} (hc : IsCandidate ctx.c a b) (hx : (x : ℤ) = a + ctx.H) :
    passes ctx.tabs x b = true := by
  refine Array.all_eq_true_iff_forall_mem.mpr fun To hTo ↦ ?_
  obtain ⟨m, hm, rfl⟩ := hctx.tabs To hTo
  dsimp only
  rw [m_mkTable, add_sub_mod_mod_eq_toNat hm hx, hctx.d_eq]
  exact admits_mkTable_of_isCandidate hm hc

/-! ### The survivors -/

/-- The points that the bit `t` of a chunk adds in `Ratpoints.FastMask.survivorPoints`: those of
the exact check of the numerator with the index `x₀ + G t`, when `t < lim` and the numerator passes
the second stage and is coprime to `b`. -/
def pointsOfSurvivor (ctx : Context) (b x₀ lim t : ℕ) : List (ℤ × ℤ × ℤ) :=
  if t < lim && passes ctx.tabs (x₀ + ctx.G * t) b &&
      natGcd (((x₀ + ctx.G * t : ℕ) : ℤ) - ctx.H).natAbs b == 1 then
    exactPoints ctx.c ctx.d b (((x₀ + ctx.G * t : ℕ) : ℤ) - ctx.H)
  else []

theorem survivorPoints_eq (ctx : Context) (b x₀ lim : ℕ) (ts : List ℕ)
    (pts : List (ℤ × ℤ × ℤ)) :
    survivorPoints ctx b x₀ lim ts pts =
      ts.reverse.flatMap (pointsOfSurvivor ctx b x₀ lim) ++ pts := by
  rw [survivorPoints, ← List.foldl_append_eq_flatMap_reverse_append]
  congr 1
  funext pts t
  simp only [pointsOfSurvivor]
  split_ifs <;> simp

/-- A survivor adds the points of the exact check of its numerator when it passes the second
stage; that the numerator is coprime to `b` is part of the exact check. -/
theorem mem_pointsOfSurvivor_iff {ctx : Context} {b x₀ lim t : ℕ} {p : ℤ × ℤ × ℤ} :
    p ∈ pointsOfSurvivor ctx b x₀ lim t ↔ t < lim ∧ passes ctx.tabs (x₀ + ctx.G * t) b = true ∧
      p ∈ pointsOfDen ctx.c ctx.d b [((x₀ + ctx.G * t : ℕ) : ℤ) - ctx.H] := by
  simp only [pointsOfSurvivor, exactPoints]
  split_ifs with h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨fun hp ↦ ⟨h.1.1, h.1.2, hp⟩, fun h' ↦ h'.2.2⟩
  · refine iff_of_false List.not_mem_nil fun ⟨hl, hpass, hp⟩ ↦ h ?_
    have hg := (mem_pointsOfDen_iff.mp hp).2.2.1
    rw [List.mem_singleton.mp (mem_pointsOfDen_iff.mp hp).1] at hg
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, natGcd_eq]
    exact ⟨⟨hl, hpass⟩, hg⟩

theorem nodup_pointsOfSurvivor (ctx : Context) (b x₀ lim t : ℕ) :
    (pointsOfSurvivor ctx b x₀ lim t).Nodup := by
  simp only [pointsOfSurvivor, exactPoints]
  split_ifs
  · exact nodup_pointsOfDen _ _ _ (List.nodup_singleton _)
  · exact List.nodup_nil

/-! ### One chunk -/

/-- The points that the chunk `sl` of the denominator `b` adds from the byte `o` of its mask to the
byte `e`, with the rows `r₀` and `rs` (`Ratpoints.FastMask.sieveChunk` on an empty buffer). -/
def chunkPoints (ctx : Context) (b : ℕ) (r₀ : ByteArray) (rs : Array ByteArray) (sl : Slot)
    (o e : ℕ) : List (ℤ × ℤ × ℤ) :=
  (sieveChunk ctx b r₀ rs sl o e .empty []).2

section Chunk

variable (ctx : Context) (b : ℕ) (r₀ : ByteArray) (rs : Array ByteArray) (sl : Slot) (o e : ℕ)

/-- The points of a chunk are those of the survivors among the set bits of its mask, the bytes of
`r₀` from the offset of the chunk on ANDed with the rows `rs`. -/
theorem chunkPoints_eq :
    chunkPoints ctx b r₀ rs sl o e =
      (setBits (andRows (r₀.extract (sl.sh₀ + o) (sl.sh₀ + o + (e - o))) rs sl.sh
        (8 * o))).reverse.flatMap
        (pointsOfSurvivor ctx b (sl.ρ + ctx.G * (sl.T₀ + 8 * o)) (sl.len - 8 * o)) := by
  rw [chunkPoints, sieveChunk, ByteArray.copySlice_eq_extract _ rfl]
  split_ifs with h
  · rw [setBits_of_size_eq_zero (beq_iff_eq.mp h)]
    rfl
  · rw [survivorPoints_eq, List.append_nil]

theorem size_fst_sieveChunk (buf : ByteArray) (pts : List (ℤ × ℤ × ℤ)) :
    (sieveChunk ctx b r₀ rs sl o e buf pts).1.size = 0 := by
  rw [sieveChunk]
  split_ifs with h
  · exact beq_iff_eq.mp h
  · rfl

theorem snd_sieveChunk {buf : ByteArray} (hbuf : buf.size = 0) (pts : List (ℤ × ℤ × ℤ)) :
    (sieveChunk ctx b r₀ rs sl o e buf pts).2 = chunkPoints ctx b r₀ rs sl o e ++ pts := by
  rw [chunkPoints_eq, sieveChunk, ByteArray.copySlice_eq_extract _ hbuf]
  split_ifs with h
  · rw [setBits_of_size_eq_zero (beq_iff_eq.mp h)]
    rfl
  · rw [survivorPoints_eq]

end Chunk

theorem exists_mem_pointsOfDen_of_mem_chunkPoints {ctx : Context} {b : ℕ} {r₀ : ByteArray}
    {rs : Array ByteArray} {sl : Slot} {o e : ℕ} {p : ℤ × ℤ × ℤ}
    (h : p ∈ chunkPoints ctx b r₀ rs sl o e) :
    ∃ t, 8 * o ≤ t ∧ t < sl.len ∧
      p ∈ pointsOfDen ctx.c ctx.d b [((sl.ρ + ctx.G * (sl.T₀ + t) : ℕ) : ℤ) - ctx.H] := by
  rw [chunkPoints_eq, List.mem_flatMap] at h
  obtain ⟨t, -, ht⟩ := h
  obtain ⟨htl, -, hp⟩ := mem_pointsOfSurvivor_iff.mp ht
  refine ⟨8 * o + t, by lia, by lia, ?_⟩
  rwa [show sl.ρ + ctx.G * (sl.T₀ + (8 * o + t)) = sl.ρ + ctx.G * (sl.T₀ + 8 * o) + ctx.G * t by
    ring]

theorem nodup_chunkPoints {ctx : Context} (hG : 0 < ctx.G) (b : ℕ) (r₀ : ByteArray)
    (rs : Array ByteArray) (sl : Slot) (o e : ℕ) : (chunkPoints ctx b r₀ rs sl o e).Nodup := by
  rw [chunkPoints_eq]
  refine List.nodup_flatMap.mpr ⟨fun t _ ↦ nodup_pointsOfSurvivor ..,
    (List.nodup_reverse.mpr (nodup_setBits _)).pairwise_of_forall_ne fun t _ t' _ hne p hp hp' ↦
      hne ?_⟩
  have h := fst_eq_of_mem_pointsOfDen_singleton (mem_pointsOfSurvivor_iff.mp hp).2.2
  rw [fst_eq_of_mem_pointsOfDen_singleton (mem_pointsOfSurvivor_iff.mp hp').2.2] at h
  exact Nat.eq_of_mul_eq_mul_left hG (by lia)

/-- For a sound context, the bit of a candidate of the chunk `sl` survives the copy of the row of
the first family from the offset of the chunk on and the AND with the rows of the others
(`Ratpoints.FastMask.Family.IsSound.bit_shift_add`). -/
theorem bit_andRows_extract_of_isCandidate {ctx : Context} {nb : ℕ} (hctx : ctx.IsSound nb)
    {sl : Slot} (hfit : sl.IsFit ctx nb) {a : ℤ} {b : ℕ} (hc : IsCandidate ctx.c a b) {o e t : ℕ}
    (hot : 8 * o ≤ t) (ht : t < sl.len) (hte : t < 8 * e)
    (hx : a + ctx.H = ((sl.ρ + ctx.G * (sl.T₀ + t) : ℕ) : ℤ)) :
    bit (andRows (ctx.fam₀.rows[b % ctx.fam₀.M]!.extract (sl.sh₀ + o) (sl.sh₀ + o + (e - o)))
      (ctx.fams.map fun F ↦ F.rows[b % F.M]!) sl.sh (8 * o)) (t - 8 * o) = true := by
  have hc' : IsCandidate ctx.c ((((sl.ρ + ctx.G * sl.T₀ : ℕ) : ℤ) - ctx.H) + ctx.G * t) b := by
    convert hc using 1
    push_cast at hx ⊢
    lia
  have htnb : t < 8 * nb := by lia [hfit.len_le, hfit.nb_le]
  refine bit_andRows_eq_true.mpr ⟨?_, fun k hk ↦ ?_⟩
  · rw [bit_extract, decide_eq_true (by lia), Bool.true_and, hfit.sh₀_eq, Nat.mul_add,
      Nat.mul_div_cancel' (Family.eight_dvd_shift hctx.fam₀.odd _), add_assoc,
      show 8 * o + (t - 8 * o) = t by lia]
    exact hctx.fam₀.bit_shift_add htnb hc'
  · simp only [Array.size_map] at hk
    simp only [getElem!_pos, Array.size_map, hk, Array.getElem_map, hfit.sh_eq]
    rw [show ∀ s, t - 8 * o + s + 8 * o = s + t from fun s ↦ by lia]
    exact (hctx.fams _ (Array.getElem_mem hk)).bit_shift_add htnb hc'

/-- For a sound context, a chunk adds the points of every candidate whose index it holds from the
byte `o` of its mask to the byte `e`, with the rows of the denominator in the families of the
context. -/
theorem mem_chunkPoints_of_mem_pointsOfDen {ctx : Context} {nb : ℕ} (hctx : ctx.IsSound nb)
    {sl : Slot} (hfit : sl.IsFit ctx nb) {a : ℤ} {b : ℕ} (hc : IsCandidate ctx.c a b) {o e t : ℕ}
    (hot : 8 * o ≤ t) (ht : t < sl.len) (hte : t < 8 * e)
    (hx : a + ctx.H = ((sl.ρ + ctx.G * (sl.T₀ + t) : ℕ) : ℤ)) {p : ℤ × ℤ × ℤ}
    (hp : p ∈ pointsOfDen ctx.c ctx.d b [a]) :
    p ∈ chunkPoints ctx b ctx.fam₀.rows[b % ctx.fam₀.M]! (ctx.fams.map fun F ↦ F.rows[b % F.M]!)
      sl o e := by
  have hidx : sl.ρ + ctx.G * (sl.T₀ + 8 * o) + ctx.G * (t - 8 * o) =
      sl.ρ + ctx.G * (sl.T₀ + t) := by
    rw [add_assoc, ← Nat.mul_add, add_assoc, Nat.add_sub_cancel' hot]
  rw [chunkPoints_eq, List.mem_flatMap]
  refine ⟨t - 8 * o, List.mem_reverse.mpr (mem_setBits.mpr
    (bit_andRows_extract_of_isCandidate hctx hfit hc hot ht hte hx)),
    mem_pointsOfSurvivor_iff.mpr ⟨by lia, ?_, ?_⟩⟩
  · rw [hidx]
    exact passes_of_isCandidate hctx hc hx.symm
  · rwa [hidx, ← hx, add_sub_cancel_right]

/-! ### The cut -/

/-- `if ρ < r then q + 1 else q`, the first position of the class `ρ` whose index `ρ + G s` is at
least `q G + r`, is at most every such position `s`. -/
theorem ite_le_of_mul_add_le {G ρ q r s : ℕ} (hρ : ρ < G) (h : q * G + r ≤ ρ + G * s) :
    (if ρ < r then q + 1 else q) ≤ s := by
  by_contra! hs
  split_ifs at hs
  · lia [Nat.mul_le_mul_left G (Nat.lt_succ_iff.mp hs)]
  · lia [Nat.mul_le_mul_left G (show s + 1 ≤ q by lia)]

/-- Every position `s` of the class `ρ` whose index `ρ + G s` is at most `q G + r` lies below
`if r < ρ then q else q + 1`, one more than the last such position. -/
theorem lt_ite_of_add_mul_le {G ρ q r s : ℕ} (hr : r < G) (h : ρ + G * s ≤ q * G + r) :
    s < if r < ρ then q else q + 1 := by
  by_contra! hs
  split_ifs at hs
  · lia [Nat.mul_le_mul_left G hs]
  · lia [Nat.mul_le_mul_left G hs]

-- the blocks of `u` bytes from the one that holds the position `t₁` to the one that holds the
-- position `t₂ - 1` hold every position from `t₁` to `t₂ - 1`
private theorem le_and_lt_of_blocks {u t₁ t₂ t : ℕ} (hu : u = 128 ∨ u = 8) (h₁ : t₁ ≤ t)
    (h₂ : t < t₂) : 8 * (u * (t₁ / (8 * u))) ≤ t ∧ t < 8 * (u * ((t₂ - 1) / (8 * u) + 1)) := by
  rcases hu with rfl | rfl <;> lia

/-- The points that `Ratpoints.FastMask.cutChunks` adds for the chunks `sls` (on an empty
buffer). -/
def cutPoints (ctx : Context) (b : ℕ) (r₀ : ByteArray) (rs : Array ByteArray) (q₁ r₁ q₂ r₂ : ℕ)
    (sls : List Slot) : List (ℤ × ℤ × ℤ) :=
  (cutChunks ctx b r₀ rs q₁ r₁ q₂ r₂ sls .empty []).2

section Cut

variable (ctx : Context) (b : ℕ) (r₀ : ByteArray) (rs : Array ByteArray) (q₁ r₁ q₂ r₂ : ℕ)

theorem cutChunks_cons (sl : Slot) (sls : List Slot) (buf : ByteArray)
    (pts : List (ℤ × ℤ × ℤ)) :
    cutChunks ctx b r₀ rs q₁ r₁ q₂ r₂ (sl :: sls) buf pts =
      cutChunks ctx b r₀ rs q₁ r₁ q₂ r₂ sls (cutChunks ctx b r₀ rs q₁ r₁ q₂ r₂ [sl] buf pts).1
        (cutChunks ctx b r₀ rs q₁ r₁ q₂ r₂ [sl] buf pts).2 := by
  simp only [cutChunks]
  split_ifs <;> rfl

/-- `Ratpoints.FastMask.cutChunks` on one chunk either keeps the buffer and the points or is
`Ratpoints.FastMask.sieveChunk` on a part of the chunk. -/
theorem exists_cutChunks_singleton (sl : Slot) :
    ∃ o e, (∀ buf pts, cutChunks ctx b r₀ rs q₁ r₁ q₂ r₂ [sl] buf pts = (buf, pts)) ∨
      ∀ buf pts, cutChunks ctx b r₀ rs q₁ r₁ q₂ r₂ [sl] buf pts =
        sieveChunk ctx b r₀ rs sl o e buf pts := by
  simp only [cutChunks]
  generalize (if sl.ρ < r₁ then q₁ + 1 else q₁) = A
  generalize (if r₂ < sl.ρ then q₂ else q₂ + 1) = B
  generalize (if sl.nb % 128 == 0 then 128 else 8) = u
  by_cases h : A - sl.T₀ < min sl.len (B - sl.T₀)
  · exact ⟨u * ((A - sl.T₀) / (8 * u)),
      min sl.nb (u * ((min sl.len (B - sl.T₀) - 1) / (8 * u) + 1)),
      .inr fun _ _ ↦ by simp only [h, ↓reduceIte]⟩
  · exact ⟨0, 0, .inl fun _ _ ↦ by simp only [h, ↓reduceIte]⟩

variable {ctx b r₀ rs q₁ r₁ q₂ r₂} in
theorem size_fst_cutChunks (sls : List Slot) {buf : ByteArray} (hbuf : buf.size = 0)
    (pts : List (ℤ × ℤ × ℤ)) : (cutChunks ctx b r₀ rs q₁ r₁ q₂ r₂ sls buf pts).1.size = 0 := by
  induction sls generalizing buf pts with
  | nil => exact hbuf
  | cons sl sls ih =>
    rw [cutChunks_cons _ _ _ _ _ _ _ _ sl sls]
    refine ih ?_ _
    obtain ⟨o, e, h | h⟩ := exists_cutChunks_singleton ctx b r₀ rs q₁ r₁ q₂ r₂ sl
    all_goals rw [h]
    · exact hbuf
    · exact size_fst_sieveChunk ..

variable {ctx b r₀ rs q₁ r₁ q₂ r₂} in
theorem snd_cutChunks_singleton (sl : Slot) {buf : ByteArray} (hbuf : buf.size = 0)
    (pts : List (ℤ × ℤ × ℤ)) :
    (cutChunks ctx b r₀ rs q₁ r₁ q₂ r₂ [sl] buf pts).2 =
      cutPoints ctx b r₀ rs q₁ r₁ q₂ r₂ [sl] ++ pts := by
  obtain ⟨o, e, h | h⟩ := exists_cutChunks_singleton ctx b r₀ rs q₁ r₁ q₂ r₂ sl
  all_goals rw [cutPoints, h, h]
  · rfl
  · exact snd_sieveChunk _ _ _ _ _ _ _ hbuf _

variable {ctx b r₀ rs q₁ r₁ q₂ r₂} in
theorem snd_cutChunks (sls : List Slot) {buf : ByteArray} (hbuf : buf.size = 0)
    (pts : List (ℤ × ℤ × ℤ)) :
    (cutChunks ctx b r₀ rs q₁ r₁ q₂ r₂ sls buf pts).2 =
      cutPoints ctx b r₀ rs q₁ r₁ q₂ r₂ sls ++ pts := by
  induction sls generalizing buf pts with
  | nil => rfl
  | cons sl sls ih =>
    rw [cutPoints, cutChunks_cons _ _ _ _ _ _ _ _ sl sls, cutChunks_cons _ _ _ _ _ _ _ _ sl sls,
      ih (size_fst_cutChunks [sl] hbuf pts), ih (size_fst_cutChunks [sl] (buf := .empty) rfl []),
      snd_cutChunks_singleton sl hbuf, snd_cutChunks_singleton sl (buf := .empty) rfl,
      List.append_nil, List.append_assoc]

theorem cutPoints_cons (sl : Slot) (sls : List Slot) :
    cutPoints ctx b r₀ rs q₁ r₁ q₂ r₂ (sl :: sls) =
      cutPoints ctx b r₀ rs q₁ r₁ q₂ r₂ sls ++ cutPoints ctx b r₀ rs q₁ r₁ q₂ r₂ [sl] := by
  rw [cutPoints, cutChunks_cons _ _ _ _ _ _ _ _ sl sls,
    snd_cutChunks sls (size_fst_cutChunks [sl] (buf := .empty) rfl [])]
  rfl

theorem cutPoints_eq_flatMap (sls : List Slot) :
    cutPoints ctx b r₀ rs q₁ r₁ q₂ r₂ sls =
      sls.reverse.flatMap fun sl ↦ cutPoints ctx b r₀ rs q₁ r₁ q₂ r₂ [sl] := by
  induction sls with
  | nil => rfl
  | cons sl sls ih =>
    rw [cutPoints_cons _ _ _ _ _ _ _ _ sl sls, ih, List.reverse_cons, List.flatMap_append,
      List.flatMap_singleton]

end Cut

theorem exists_mem_pointsOfDen_of_mem_cutPoints_singleton {ctx : Context} {b : ℕ}
    {r₀ : ByteArray} {rs : Array ByteArray} {q₁ r₁ q₂ r₂ : ℕ} {sl : Slot} {p : ℤ × ℤ × ℤ}
    (h : p ∈ cutPoints ctx b r₀ rs q₁ r₁ q₂ r₂ [sl]) :
    ∃ t < sl.len,
      p ∈ pointsOfDen ctx.c ctx.d b [((sl.ρ + ctx.G * (sl.T₀ + t) : ℕ) : ℤ) - ctx.H] := by
  obtain ⟨o, e, h' | h'⟩ := exists_cutChunks_singleton ctx b r₀ rs q₁ r₁ q₂ r₂ sl
  all_goals rw [cutPoints, h'] at h
  · simp at h
  · obtain ⟨t, -, ht, hp⟩ := exists_mem_pointsOfDen_of_mem_chunkPoints h
    exact ⟨t, ht, hp⟩

theorem exists_mem_pointsOfDen_of_mem_cutPoints {ctx : Context} {b : ℕ} {r₀ : ByteArray}
    {rs : Array ByteArray} {q₁ r₁ q₂ r₂ : ℕ} {sls : List Slot} {p : ℤ × ℤ × ℤ}
    (h : p ∈ cutPoints ctx b r₀ rs q₁ r₁ q₂ r₂ sls) :
    ∃ sl ∈ sls, ∃ t < sl.len,
      p ∈ pointsOfDen ctx.c ctx.d b [((sl.ρ + ctx.G * (sl.T₀ + t) : ℕ) : ℤ) - ctx.H] := by
  rw [cutPoints_eq_flatMap, List.mem_flatMap] at h
  obtain ⟨sl, hsl, hp⟩ := h
  exact ⟨sl, List.mem_reverse.mp hsl, exists_mem_pointsOfDen_of_mem_cutPoints_singleton hp⟩

/-- For a sound context, the cut of a chunk to the blocks of the indices from `q₁ G + r₁` to
`q₂ G + r₂` keeps the points of every candidate of the chunk in that range. -/
theorem mem_cutPoints_singleton_of_mem_pointsOfDen {ctx : Context} {nb : ℕ}
    (hctx : ctx.IsSound nb) {sl : Slot} (hfit : sl.IsFit ctx nb) {a : ℤ} {b : ℕ}
    (hc : IsCandidate ctx.c a b) {t : ℕ} (ht : t < sl.len)
    (hx : a + ctx.H = ((sl.ρ + ctx.G * (sl.T₀ + t) : ℕ) : ℤ)) {q₁ r₁ q₂ r₂ : ℕ}
    (h₁ : q₁ * ctx.G + r₁ ≤ sl.ρ + ctx.G * (sl.T₀ + t))
    (h₂ : sl.ρ + ctx.G * (sl.T₀ + t) ≤ q₂ * ctx.G + r₂) (hr₂ : r₂ < ctx.G) {p : ℤ × ℤ × ℤ}
    (hp : p ∈ pointsOfDen ctx.c ctx.d b [a]) :
    p ∈ cutPoints ctx b ctx.fam₀.rows[b % ctx.fam₀.M]! (ctx.fams.map fun F ↦ F.rows[b % F.M]!)
      q₁ r₁ q₂ r₂ [sl] := by
  have h₁' := ite_le_of_mul_add_le hfit.ρ_lt h₁
  have h₂' := lt_ite_of_add_mul_le hr₂ h₂
  have hu : (if sl.nb % 128 == 0 then 128 else 8) = 128 ∨
      (if sl.nb % 128 == 0 then 128 else 8) = 8 := ite_eq_or_eq ..
  simp only [cutPoints, cutChunks]
  generalize (if sl.ρ < r₁ then q₁ + 1 else q₁) = A at h₁' ⊢
  generalize (if r₂ < sl.ρ then q₂ else q₂ + 1) = B at h₂' ⊢
  generalize (if sl.nb % 128 == 0 then 128 else 8) = u at hu ⊢
  have hb := le_and_lt_of_blocks hu (show A - sl.T₀ ≤ t by lia)
    (show t < min sl.len (B - sl.T₀) by lia)
  split_ifs
  · exact mem_chunkPoints_of_mem_pointsOfDen hctx hfit hc hb.1 ht (by lia [hfit.len_le]) hx hp
  · lia

theorem mem_cutPoints_of_mem_pointsOfDen {ctx : Context} {nb : ℕ} (hctx : ctx.IsSound nb)
    {sls : List Slot} {sl : Slot} (hsl : sl ∈ sls) (hfit : sl.IsFit ctx nb) {a : ℤ} {b : ℕ}
    (hc : IsCandidate ctx.c a b) {t : ℕ} (ht : t < sl.len)
    (hx : a + ctx.H = ((sl.ρ + ctx.G * (sl.T₀ + t) : ℕ) : ℤ)) {q₁ r₁ q₂ r₂ : ℕ}
    (h₁ : q₁ * ctx.G + r₁ ≤ sl.ρ + ctx.G * (sl.T₀ + t))
    (h₂ : sl.ρ + ctx.G * (sl.T₀ + t) ≤ q₂ * ctx.G + r₂) (hr₂ : r₂ < ctx.G) {p : ℤ × ℤ × ℤ}
    (hp : p ∈ pointsOfDen ctx.c ctx.d b [a]) :
    p ∈ cutPoints ctx b ctx.fam₀.rows[b % ctx.fam₀.M]! (ctx.fams.map fun F ↦ F.rows[b % F.M]!)
      q₁ r₁ q₂ r₂ sls := by
  rw [cutPoints_eq_flatMap, List.mem_flatMap]
  exact ⟨sl, List.mem_reverse.mpr hsl,
    mem_cutPoints_singleton_of_mem_pointsOfDen hctx hfit hc ht hx h₁ h₂ hr₂ hp⟩

/-- The points of chunks with pairwise different indices, each once. -/
theorem nodup_cutPoints {ctx : Context} (hG : 0 < ctx.G) (b : ℕ) (r₀ : ByteArray)
    (rs : Array ByteArray) (q₁ r₁ q₂ r₂ : ℕ) {sls : List Slot}
    (hsls : sls.Pairwise fun s s' ↦ ∀ t < s.len, ∀ t' < s'.len,
      s.ρ + ctx.G * (s.T₀ + t) ≠ s'.ρ + ctx.G * (s'.T₀ + t')) :
    (cutPoints ctx b r₀ rs q₁ r₁ q₂ r₂ sls).Nodup := by
  rw [cutPoints_eq_flatMap]
  refine List.nodup_flatMap.mpr ⟨fun sl _ ↦ ?_,
    List.pairwise_reverse.mpr (hsls.imp fun hne p hp hp' ↦ ?_)⟩
  · obtain ⟨o, e, h | h⟩ := exists_cutChunks_singleton ctx b r₀ rs q₁ r₁ q₂ r₂ sl
    all_goals rw [cutPoints, h]
    · exact List.nodup_nil
    · exact nodup_chunkPoints hG ..
  · obtain ⟨t, ht, hpt⟩ := exists_mem_pointsOfDen_of_mem_cutPoints_singleton hp
    obtain ⟨t', ht', hpt'⟩ := exists_mem_pointsOfDen_of_mem_cutPoints_singleton hp'
    have h := fst_eq_of_mem_pointsOfDen_singleton hpt
    rw [fst_eq_of_mem_pointsOfDen_singleton hpt'] at h
    exact hne t' ht' t ht (by lia)

/-! ### The region -/

/-- The signed numerator `± n` of an end of the region, whose value is `± n / 2 ^ k`. -/
def End.num (l : End) : ℤ := if l.neg then -(l.n : ℤ) else l.n

/-- The first index `a + H` of the numerators `a` of the denominator `b` above the end `l` of an
interval of the region, of value `l.num / 2 ^ k`: `H + ⌈b l⌉`, or `0` when that is negative. -/
def lowIndex (H k b : ℕ) (l : End) : ℕ :=
  if l.neg then H - (b * l.n) >>> k else H + (b * l.n + 2 ^ k - 1) >>> k

/-- One more than the last index `a + H` of the numerators `a` of the denominator `b` below the end
`u` of an interval of the region, of value `u.num / 2 ^ k`: `H + ⌊b u⌋ + 1`, clipped to
`0, …, 2 H + 1`. -/
def highIndex (H k b : ℕ) (u : End) : ℕ :=
  if u.neg then H + 1 - (b * u.n + 2 ^ k - 1) >>> k else min (2 * H) (H + (b * u.n) >>> k) + 1

/-- The hull of the indices `a + H` of the numerators `a` of the denominator `b` in the intervals
`reg` from position `i` on and of the indices from `lo` to `hi` (none when `hi < lo`), as
`Ratpoints.FastMask.regionChunks` computes it. -/
def regionHull (H k b : ℕ) (reg : Array (End × End)) (i lo hi : ℕ) : ℕ × ℕ :=
  if h : i < reg.size then
    if lowIndex H k b reg[i].1 < highIndex H k b reg[i].2 then
      regionHull H k b reg (i + 1) (min lo (lowIndex H k b reg[i].1))
        (max hi (highIndex H k b reg[i].2 - 1))
    else regionHull H k b reg (i + 1) lo hi
  else (lo, hi)
termination_by reg.size - i

/-- `Ratpoints.FastMask.regionChunks` cuts the chunks of the class of `b` to the hull of the
indices of the region (`Ratpoints.FastMask.regionHull`). -/
theorem regionChunks_eq (ctx : Context) (b : ℕ) (r₀ : ByteArray) (rs : Array ByteArray)
    (reg : Array (End × End)) (i lo hi : ℕ) (buf : ByteArray) (pts : List (ℤ × ℤ × ℤ)) :
    regionChunks ctx b r₀ rs reg i lo hi buf pts =
      if (regionHull ctx.H ctx.k b reg i lo hi).2 < (regionHull ctx.H ctx.k b reg i lo hi).1 then
        (buf, pts)
      else cutChunks ctx b r₀ rs ((regionHull ctx.H ctx.k b reg i lo hi).1 / ctx.G)
        ((regionHull ctx.H ctx.k b reg i lo hi).1 % ctx.G)
        ((regionHull ctx.H ctx.k b reg i lo hi).2 / ctx.G)
        ((regionHull ctx.H ctx.k b reg i lo hi).2 % ctx.G) ctx.slots[b % ctx.G]! buf pts := by
  fun_induction regionHull ctx.H ctx.k b reg i lo hi with
  | case1 i lo hi h hlt ih | case2 i lo hi h hlt ih =>
    rw [regionChunks, dite_eq_left h]
    simp only [lowIndex, highIndex] at hlt ih
    simp only [hlt, ↓reduceIte]
    exact ih
  | case3 i lo hi h => rw [regionChunks, dite_eq_right h]

theorem mem_Icc_regionHull_of_mem_Icc {H k b : ℕ} (reg : Array (End × End)) (i : ℕ)
    {lo hi x : ℕ} (h : x ∈ Set.Icc lo hi) :
    x ∈ Set.Icc (regionHull H k b reg i lo hi).1 (regionHull H k b reg i lo hi).2 := by
  fun_induction regionHull H k b reg i lo hi with
  | case1 i lo hi _ _ ih => exact ih ⟨by lia [h.1], by lia [h.2]⟩
  | case2 i lo hi _ _ ih => exact ih h
  | case3 i lo hi _ => exact h

theorem mem_Icc_regionHull_of_mem_Ico {H k b : ℕ} {reg : Array (End × End)} {i j : ℕ}
    (hij : i ≤ j) (hj : j < reg.size) {lo hi x : ℕ}
    (h : x ∈ Set.Ico (lowIndex H k b reg[j].1) (highIndex H k b reg[j].2)) :
    x ∈ Set.Icc (regionHull H k b reg i lo hi).1 (regionHull H k b reg i lo hi).2 := by
  obtain ⟨h₁, h₂⟩ := h
  fun_induction regionHull H k b reg i lo hi with
  | case1 i lo hi _ _ ih =>
    rcases hij.eq_or_lt with rfl | hij
    · exact mem_Icc_regionHull_of_mem_Icc reg _ ⟨by lia, by lia⟩
    · exact ih (by lia)
  | case2 i lo hi _ _ ih =>
    rcases hij.eq_or_lt with rfl | hij
    · lia
    · exact ih (by lia)
  | case3 i lo hi _ => lia

theorem lowIndex_le {H k b x : ℕ} {l : End} (h : l.num * b ≤ ((x : ℤ) - H) * 2 ^ k) :
    lowIndex H k b l ≤ x := by
  simp only [lowIndex, Nat.shiftRight_eq_div_pow]
  simp only [End.num] at h
  split_ifs at h ⊢
  · have : H - x ≤ b * l.n / 2 ^ k := by
      rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos k), Nat.sub_mul]
      lia
    lia
  · have h0 : (0 : ℤ) ≤ l.n * b := by positivity
    have hx := le_of_mul_le_mul_right (a := (2 : ℤ) ^ k) (b := 0) (c := (x : ℤ) - H) (by lia)
      (by positivity)
    have : (b * l.n + 2 ^ k - 1) / 2 ^ k ≤ x - H := by
      rw [Nat.div_le_iff_le_mul_add_pred (Nat.two_pow_pos k), Nat.mul_sub]
      lia [Nat.one_le_two_pow (n := k)]
    lia

theorem lt_highIndex {H k b x : ℕ} {u : End} (hx : x ≤ 2 * H)
    (h : ((x : ℤ) - H) * 2 ^ k ≤ u.num * b) : x < highIndex H k b u := by
  simp only [highIndex, Nat.shiftRight_eq_div_pow]
  simp only [End.num] at h
  split_ifs at h ⊢
  · have h0 : (0 : ℤ) ≤ u.n * b := by positivity
    have hxH := le_of_mul_le_mul_right (a := (2 : ℤ) ^ k) (b := (x : ℤ) - H) (c := 0) (by lia)
      (by positivity)
    have : (b * u.n + 2 ^ k - 1) / 2 ^ k ≤ H - x := by
      rw [Nat.div_le_iff_le_mul_add_pred (Nat.two_pow_pos k), Nat.mul_sub]
      lia [Nat.one_le_two_pow (n := k)]
    lia
  · have : x - H ≤ b * u.n / 2 ^ k := by
      rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos k), Nat.sub_mul]
      lia
    lia

theorem lowIndex_le_of_num_div_le {H k b x : ℕ} (hb : 0 < b) {a : ℤ} (hx : (x : ℤ) = a + H)
    {l : End} (h : (l.num : ℚ) / 2 ^ k ≤ a / b) : lowIndex H k b l ≤ x := by
  rw [div_le_div_iff₀ (by positivity) (mod_cast hb)] at h
  refine lowIndex_le ?_
  rw [show (x : ℤ) - H = a by lia]
  exact_mod_cast h

theorem lt_highIndex_of_div_le {H k b x : ℕ} (hb : 0 < b) {a : ℤ} (hx : (x : ℤ) = a + H)
    (hxH : x ≤ 2 * H) {u : End} (h : (a : ℚ) / b ≤ u.num / 2 ^ k) : x < highIndex H k b u := by
  rw [div_le_div_iff₀ (mod_cast hb) (by positivity)] at h
  refine lt_highIndex hxH ?_
  rw [show (x : ℤ) - H = a by lia]
  exact_mod_cast h

/-- `Ratpoints.FastMask.roundEnd` rounds a lower end `n / q` down to a multiple of `2 ^ (-k)`. -/
theorem num_roundEnd_false_mul_le {k : ℕ} {n : ℤ} {q : ℕ} (hq : 0 < q) (dflt : End) :
    (roundEnd k false (some (n, q)) dflt).num * q ≤ n * 2 ^ k := by
  rcases lt_or_ge n 0 with hn | hn
  · simp only [roundEnd, End.num, decide_eq_true hn, Bool.true_beq, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨m, rfl⟩ := Int.exists_eq_neg_ofNat hn.le
    rw [Int.natAbs_neg, Int.natAbs_natCast]
    have := Nat.le_add_sub_one_div_mul (m * 2 ^ k) hq
    zify at this
    lia
  · simp only [roundEnd, End.num, decide_eq_false (not_lt.mpr hn), Bool.false_beq, Bool.not_false,
      ↓reduceIte, Bool.false_eq_true]
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [Int.natAbs_natCast]
    have := Nat.div_mul_le_self (m * 2 ^ k) q
    zify at this
    lia

/-- `Ratpoints.FastMask.roundEnd` rounds an upper end `n / q` up to a multiple of `2 ^ (-k)`. -/
theorem le_num_roundEnd_true_mul {k : ℕ} {n : ℤ} {q : ℕ} (hq : 0 < q) (dflt : End) :
    n * 2 ^ k ≤ (roundEnd k true (some (n, q)) dflt).num * q := by
  rcases lt_or_ge n 0 with hn | hn
  · simp only [roundEnd, End.num, decide_eq_true hn, Bool.true_beq, ↓reduceIte]
    obtain ⟨m, rfl⟩ := Int.exists_eq_neg_ofNat hn.le
    rw [Int.natAbs_neg, Int.natAbs_natCast]
    have := Nat.div_mul_le_self (m * 2 ^ k) q
    zify at this
    lia
  · simp only [roundEnd, End.num, decide_eq_false (not_lt.mpr hn), Bool.false_beq, Bool.not_true,
      ↓reduceIte, Bool.false_eq_true]
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [Int.natAbs_natCast]
    have := Nat.le_add_sub_one_div_mul (m * 2 ^ k) hq
    zify at this
    lia

/-- The lower end of an interval of the region, as `Ratpoints.Fast.endFrac` bounds it and
`Ratpoints.FastMask.roundEnd` rounds it down, lies below every `a / b` with `|a| ≤ H` above the
end. -/
theorem num_roundEnd_endFrac_div_le {H k b : ℕ} {a : ℤ} (ha : |a| ≤ H) {l : Double}
    (hl : doubleValue l.bits ≤ (((a : ℚ) / b : ℚ) : WithBotTop ℚ)) :
    ((roundEnd k false (endFrac H l) ⟨true, (H + 1) * 2 ^ k⟩).num : ℚ) / 2 ^ k ≤ a / b := by
  have hab := abs_intCast_div_natCast_le (α := ℚ) ha b
  rcases he : endFrac H l with _ | ⟨n, q⟩
  · simp only [roundEnd, End.num, ↓reduceIte]
    push_cast
    rw [neg_div, mul_div_cancel_right₀ _ (by positivity)]
    linarith [(abs_le.mp hab).1]
  · have hq := pos_of_endFrac_eq_some he
    refine le_trans ?_ (div_le_of_endFrac_eq_some he hab hl)
    rw [div_le_div_iff₀ (by positivity) (mod_cast hq)]
    exact_mod_cast num_roundEnd_false_mul_le hq _

/-- The upper end of an interval of the region, as `Ratpoints.Fast.endFrac` bounds it and
`Ratpoints.FastMask.roundEnd` rounds it up, lies above every `a / b` with `|a| ≤ H` below the
end. -/
theorem div_le_num_roundEnd_endFrac_div {H k b : ℕ} {a : ℤ} (ha : |a| ≤ H) {u : Double}
    (hu : (((a : ℚ) / b : ℚ) : WithBotTop ℚ) ≤ doubleValue u.bits) :
    (a : ℚ) / b ≤ (roundEnd k true (endFrac H u) ⟨false, (H + 1) * 2 ^ k⟩).num / 2 ^ k := by
  have hab := abs_intCast_div_natCast_le (α := ℚ) ha b
  rcases he : endFrac H u with _ | ⟨n, q⟩
  · simp only [roundEnd, End.num, Bool.false_eq_true, ↓reduceIte]
    push_cast
    rw [mul_div_cancel_right₀ _ (by positivity)]
    linarith [(abs_le.mp hab).2]
  · have hq := pos_of_endFrac_eq_some he
    refine (le_div_of_endFrac_eq_some he hab hu).trans ?_
    rw [div_le_div_iff₀ (mod_cast hq) (by positivity)]
    exact_mod_cast le_num_roundEnd_true_mul hq _

/-- Assuming Sturm's theorem, the hull of the numerators of the denominator `b` in the region
holds the index `a + H` of every candidate `(a, b)` with `|a| ≤ H`: the region of the search is
that of `Ratpoints.Fast.region` with its ends rounded by `Ratpoints.FastMask.roundEnd`, the lower
ones down and the upper ones up (`f`), and one of its intervals holds `a / b`
(`Ratpoints.Fast.exists_mem_sturmIntervals`). -/
theorem mem_Icc_regionHull_of_isCandidate (hS : SturmTheorem) {c : List ℤ} {H depth k : ℕ}
    {R : Array (Option (ℤ × ℕ) × Option (ℤ × ℕ))} (hR : region c (degree c) H depth = some R)
    {f : Option (ℤ × ℕ) × Option (ℤ × ℕ) → End × End}
    (hf : ∀ lo hi, f (lo, hi) =
      (roundEnd k false lo ⟨true, (H + 1) * 2 ^ k⟩, roundEnd k true hi ⟨false, (H + 1) * 2 ^ k⟩))
    {a : ℤ} {b x : ℕ} (hb : 1 ≤ b) (hc : IsCandidate c a b) (ha : |a| ≤ H)
    (hx : (x : ℤ) = a + H) :
    x ∈ Set.Icc (regionHull H k b (R.map f) 0 (2 * H + 1) 0).1
      (regionHull H k b (R.map f) 0 (2 * H + 1) 0).2 := by
  obtain ⟨ivs, hivs, rfl⟩ := Option.map_eq_some_iff.mp hR
  obtain ⟨-, y, hy⟩ := hc
  obtain ⟨iv, hiv, hl, hu⟩ := exists_mem_sturmIntervals hS hivs hb ha (hy ▸ sq_nonneg y)
  obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp hiv
  refine mem_Icc_regionHull_of_mem_Ico (Nat.zero_le j) (by simpa using hj) ?_
  simp only [Array.getElem_map, hf]
  exact ⟨lowIndex_le_of_num_div_le hb hx (num_roundEnd_endFrac_div_le ha hl),
    lt_highIndex_of_div_le hb hx (by lia [abs_le.mp ha]) (div_le_num_roundEnd_endFrac_div ha hu)⟩

/-! ### The rows of a denominator -/

theorem rowsOf_eq_some {fams : Array Family} {b : ℕ}
    (h : ∀ F ∈ fams, F.rows[b % F.M]!.size ≠ 0) (i : ℕ) (acc : Array ByteArray) :
    rowsOf fams b i acc =
      some ⟨acc.toList ++ (fams.toList.drop i).map fun F ↦ F.rows[b % F.M]!⟩ := by
  fun_induction rowsOf fams b i acc with
  | case1 i acc hi r hr => exact absurd (beq_iff_eq.mp hr) (h _ (Array.getElem_mem hi))
  | case2 i acc hi r hr ih =>
    rw [ih, Array.toList_push,
      List.drop_eq_getElem_cons (show i < fams.toList.length by simpa using hi)]
    simp [r]
  | case3 i acc hi =>
    rw [List.drop_eq_nil_of_le (by simpa using hi)]
    simp

/-- When no row of the denominator `b` in the families is empty, `Ratpoints.FastMask.rowsOf`
gives them all. -/
theorem rowsOf_zero_eq_some {fams : Array Family} {b : ℕ}
    (h : ∀ F ∈ fams, F.rows[b % F.M]!.size ≠ 0) (n : ℕ) :
    rowsOf fams b 0 (Array.emptyWithCapacity n) = some (fams.map fun F ↦ F.rows[b % F.M]!) := by
  rw [rowsOf_eq_some h]
  exact congr(some $(Array.toList_inj.mp (by simp)))

/-! ### A denominator -/

/-- The points that `Ratpoints.FastMask.denStep` adds for the denominator `b` (on an empty
buffer). -/
def denPoints (ctx : Context) (b : ℕ) : List (ℤ × ℤ × ℤ) := (denStep ctx b .empty []).2

/-- `Ratpoints.FastMask.denStep` either keeps the buffer and the points or is
`Ratpoints.FastMask.cutChunks` on the chunks of the class of `b`. -/
theorem exists_denStep (ctx : Context) (b : ℕ) :
    (∀ buf pts, denStep ctx b buf pts = (buf, pts)) ∨ ∃ r₀ rs q₁ r₁ q₂ r₂, ∀ buf pts,
      denStep ctx b buf pts = cutChunks ctx b r₀ rs q₁ r₁ q₂ r₂ ctx.slots[b % ctx.G]! buf pts := by
  simp only [denStep]
  by_cases h0 : (ctx.fam₀.rows[b % ctx.fam₀.M]!.size == 0) = true
  · exact .inl fun _ _ ↦ by simp only [h0, ↓reduceIte]
  simp only [h0, Bool.false_eq_true, ↓reduceIte]
  rcases rowsOf ctx.fams b 0 (Array.emptyWithCapacity ctx.fams.size) with _ | rs
  · exact .inl fun _ _ ↦ rfl
  rcases ctx.reg with _ | reg
  · exact .inr ⟨_, _, _, _, _, _, fun _ _ ↦ rfl⟩
  simp only [regionChunks_eq]
  by_cases h : (regionHull ctx.H ctx.k b reg 0 (2 * ctx.H + 1) 0).2 <
    (regionHull ctx.H ctx.k b reg 0 (2 * ctx.H + 1) 0).1
  · exact .inl fun _ _ ↦ by simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte]
    exact .inr ⟨_, _, _, _, _, _, fun _ _ ↦ rfl⟩

theorem size_fst_denStep (ctx : Context) (b : ℕ) {buf : ByteArray} (hbuf : buf.size = 0)
    (pts : List (ℤ × ℤ × ℤ)) : (denStep ctx b buf pts).1.size = 0 := by
  obtain h | ⟨r₀, rs, q₁, r₁, q₂, r₂, h⟩ := exists_denStep ctx b
  all_goals rw [h]
  · exact hbuf
  · exact size_fst_cutChunks _ hbuf _

theorem snd_denStep (ctx : Context) (b : ℕ) {buf : ByteArray} (hbuf : buf.size = 0)
    (pts : List (ℤ × ℤ × ℤ)) : (denStep ctx b buf pts).2 = denPoints ctx b ++ pts := by
  obtain h | ⟨r₀, rs, q₁, r₁, q₂, r₂, h⟩ := exists_denStep ctx b
  all_goals rw [denPoints, h, h]
  · rfl
  · exact snd_cutChunks _ hbuf _

/-- Every point that the search adds for the denominator `b` comes from the exact check of a
numerator of a chunk of the class of `b`. -/
theorem exists_mem_pointsOfDen_of_mem_denPoints {ctx : Context} {b : ℕ} {p : ℤ × ℤ × ℤ}
    (h : p ∈ denPoints ctx b) :
    ∃ sl ∈ ctx.slots[b % ctx.G]!, ∃ t < sl.len,
      p ∈ pointsOfDen ctx.c ctx.d b [((sl.ρ + ctx.G * (sl.T₀ + t) : ℕ) : ℤ) - ctx.H] := by
  obtain h' | ⟨r₀, rs, q₁, r₁, q₂, r₂, h'⟩ := exists_denStep ctx b
  all_goals rw [denPoints, h'] at h
  · simp at h
  · exact exists_mem_pointsOfDen_of_mem_cutPoints h

theorem snd_snd_eq_of_mem_denPoints {ctx : Context} {b : ℕ} {p : ℤ × ℤ × ℤ}
    (h : p ∈ denPoints ctx b) : p.2.2 = b := by
  obtain ⟨_, _, _, _, hp⟩ := exists_mem_pointsOfDen_of_mem_denPoints h
  exact snd_snd_eq_of_mem_pointsOfDen hp

/-- The points that the search adds for the denominator `b`, each once, when the chunks of its
class have pairwise different indices. -/
theorem nodup_denPoints {ctx : Context} (hG : 0 < ctx.G) (b : ℕ)
    (hsls : ctx.slots[b % ctx.G]!.Pairwise fun s s' ↦ ∀ t < s.len, ∀ t' < s'.len,
      s.ρ + ctx.G * (s.T₀ + t) ≠ s'.ρ + ctx.G * (s'.T₀ + t')) :
    (denPoints ctx b).Nodup := by
  obtain h | ⟨r₀, rs, q₁, r₁, q₂, r₂, h⟩ := exists_denStep ctx b
  all_goals rw [denPoints, h]
  · exact List.nodup_nil
  · exact nodup_cutPoints hG _ _ _ _ _ _ _ hsls

/-- For a sound context, the search adds for the denominator `b` the points of every candidate
`(a, b)` whose index `a + H ≤ 2 H` a chunk of the class of `b` holds, in the hull of the region
when there is one (`Ratpoints.FastMask.mem_Icc_regionHull_of_isCandidate`). -/
theorem mem_denPoints_of_mem_pointsOfDen {ctx : Context} {nb : ℕ} (hctx : ctx.IsSound nb)
    {a : ℤ} {b : ℕ} (hc : IsCandidate ctx.c a b) {sl : Slot} (hsl : sl ∈ ctx.slots[b % ctx.G]!)
    {t : ℕ} (ht : t < sl.len) (hx : a + ctx.H = ((sl.ρ + ctx.G * (sl.T₀ + t) : ℕ) : ℤ))
    (hxH : sl.ρ + ctx.G * (sl.T₀ + t) ≤ 2 * ctx.H)
    (hreg : ∀ reg ∈ ctx.reg, sl.ρ + ctx.G * (sl.T₀ + t) ∈
      Set.Icc (regionHull ctx.H ctx.k b reg 0 (2 * ctx.H + 1) 0).1
        (regionHull ctx.H ctx.k b reg 0 (2 * ctx.H + 1) 0).2)
    {p : ℤ × ℤ × ℤ} (hp : p ∈ pointsOfDen ctx.c ctx.d b [a]) : p ∈ denPoints ctx b := by
  rw [denPoints, denStep]
  simp only [beq_iff_eq, hctx.fam₀.size_row_ne_zero hc, ↓reduceIte,
    rowsOf_zero_eq_some fun F hF ↦ (hctx.fams F hF).size_row_ne_zero hc]
  rcases hr : ctx.reg with _ | reg
  · exact mem_cutPoints_of_mem_pointsOfDen hctx hsl (hctx.slots _ sl hsl) hc ht hx (by lia)
      (by rwa [Nat.div_add_mod']) (Nat.mod_lt _ hctx.G_pos) hp
  · obtain ⟨h₁, h₂⟩ := hreg reg hr
    simp only [regionChunks_eq]
    split_ifs
    · lia
    · exact mem_cutPoints_of_mem_pointsOfDen hctx hsl (hctx.slots _ sl hsl) hc ht hx
        (by rwa [Nat.div_add_mod']) (by rwa [Nat.div_add_mod'])
        (Nat.mod_lt _ hctx.G_pos) hp

/-! ### The loop over the denominators -/

/-- The loop over the denominators `bs`, on a buffer of size `0`, adds the points of each in turn
before `pts`. -/
theorem densLoop_eq (ctx : Context) (bs : List ℕ) {buf : ByteArray} (hbuf : buf.size = 0)
    (pts : List (ℤ × ℤ × ℤ)) :
    densLoop ctx bs buf pts = bs.reverse.flatMap (denPoints ctx) ++ pts := by
  induction bs generalizing buf pts with
  | nil => rfl
  | cons b bs ih =>
    rw [densLoop, ih (size_fst_denStep ctx b hbuf pts), snd_denStep ctx b hbuf pts]
    simp

/-- The points of distinct denominators, each once, when the chunks of the class of each have
pairwise different indices: the points of the denominator `b` have `z = b`
(`Ratpoints.FastMask.snd_snd_eq_of_mem_denPoints`). -/
theorem nodup_flatMap_denPoints {ctx : Context} (hG : 0 < ctx.G) {bs : List ℕ} (hbs : bs.Nodup)
    (hsls : ∀ b ∈ bs, ctx.slots[b % ctx.G]!.Pairwise fun s s' ↦ ∀ t < s.len, ∀ t' < s'.len,
      s.ρ + ctx.G * (s.T₀ + t) ≠ s'.ρ + ctx.G * (s'.T₀ + t')) :
    (bs.flatMap (denPoints ctx)).Nodup :=
  List.nodup_flatMap.mpr ⟨fun b hb ↦ nodup_denPoints hG b (hsls b hb),
    hbs.pairwise_of_forall_ne fun _ _ _ _ hne _ hp hp' ↦
      hne (mod_cast (snd_snd_eq_of_mem_denPoints hp).symm.trans (snd_snd_eq_of_mem_denPoints hp'))⟩

end FastMask

end Ratpoints

end

/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Proof.FastChunks

import Ratpoints.Proof.BruteForce
import Ratpoints.Proof.Containers
import Ratpoints.Proof.Region
import Ratpoints.Proof.Setup

/-!
# The fast search on byte-array masks finds exactly the points

`Ratpoints.FastMask.fastPoints` lists only points of the region
(`Ratpoints.FastMask.isPoint_and_inRegion_of_mem_fastPoints`), each once
(`Ratpoints.FastMask.nodup_fastPoints`), and, assuming Sturm's theorem, all of them
(`Ratpoints.FastMask.mem_fastPoints_iff`). The module `Ratpoints.Proof.FastChunks` describes the
loops of the search for a fixed `Ratpoints.FastMask.Context`; this file shows that the context that
`Ratpoints.FastMask.search` builds is sound and that the parameters of
`Ratpoints.FastMask.choose` are valid.

* The chunks of the residue of a denominator modulo the step are those of the classes that its row
  allows (`Ratpoints.FastMask.mem_getElem!_classSlots_iff`): the index `a + H` of every candidate
  `(a, b)` with `|a| ≤ H` lies in one of them (`Ratpoints.FastMask.exists_mem_getElem!_classSlots`),
  and no index in two (`Ratpoints.FastMask.pairwise_getElem!_classSlots`). Their masks hold their
  numerators and are no longer than those of a chunk of `L` numerators, for which the rows of the
  families are made (`Ratpoints.FastMask.le_eight_mul_maskBytes`,
  `Ratpoints.FastMask.monotone_maskBytes`).
* When the tables of both stages are tables `Ratpoints.Fast.mkTable c d m` of `c` with `m > 0`, the
  families of the first stage are sound, and so is the context
  (`Ratpoints.FastMask.isSound_searchContext`). The tables that `Ratpoints.FastMask.choose` takes
  are of this kind (`Ratpoints.FastMask.exists_pos_eq_mkTable_of_mem_stage₁_choose`,
  `Ratpoints.FastMask.exists_pos_eq_mkTable_of_mem_stage₂_choose`), and its step and its chunk
  length are positive.
* The search lists the points of its denominators in turn (`Ratpoints.FastMask.search_eq`): every
  point comes from the exact check (`Ratpoints.FastMask.exists_mem_pointsOfDen_of_mem_search`), the
  points of every candidate of its denominators are listed, assuming Sturm's theorem
  (`Ratpoints.FastMask.mem_search_of_mem_pointsOfDen`), and each once
  (`Ratpoints.FastMask.nodup_search`).
* `Ratpoints.FastMask.sievePoints` adds the points at infinity and searches the denominators of
  `Ratpoints.Fast.denominators`, which include that of every point
  (`Ratpoints.FastMask.isPoint_and_inRegion_of_mem_sievePoints`,
  `Ratpoints.FastMask.mem_sievePoints_of_isPoint`, `Ratpoints.FastMask.nodup_sievePoints`); when
  the coefficients are reversed, `Ratpoints.Sieve.swapPoint` maps the points of the reversed list
  to those of `c`, one to one.

## Main statements

* `Ratpoints.FastMask.isPoint_and_inRegion_of_mem_fastPoints`: the list holds only points of the
  region.
* `Ratpoints.FastMask.mem_fastPoints_iff`: assuming Sturm's theorem, it holds exactly the points of
  the region.
* `Ratpoints.FastMask.nodup_fastPoints`: each of them once.
-/

@[expose] public section

/-! ### Lists -/

/-- The first component of a fold whose step either takes the new element or keeps the first
component is the initial one or an element of the list. -/
theorem List.fst_foldl_mem_cons {α β : Type*} {f : α × β → α → α × β}
    (hf : ∀ b x, (f b x).1 = x ∨ (f b x).1 = b.1) (l : List α) (init : α × β) :
    (l.foldl f init).1 ∈ init.1 :: l := by
  induction l generalizing init with
  | nil => exact List.mem_cons_self
  | cons x l ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp (ih (f init x)) with h | h
    · rcases hf init x with h' | h' <;> simp [h, h']
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

namespace Ratpoints

namespace FastMask

open BruteForce Fast

/-! ### The chunks of the classes -/

theorem le_eight_mul_maskBytes (len : ℕ) : len ≤ 8 * maskBytes len := by
  rw [maskBytes]
  split_ifs <;> lia

theorem monotone_maskBytes : Monotone maskBytes := fun _ _ _ ↦ by
  simp only [maskBytes]
  split_ifs <;> lia

theorem mem_slotsOf_iff {H G L ρ : ℕ} {fam₀ : Family} {fams : Array Family} {sl : Slot} :
    sl ∈ slotsOf H G L fam₀ fams ρ ↔ sl.ρ = ρ ∧
      (sl.T₀, sl.len) ∈ chunks (classCount (2 * H + 1) G ρ) L ∧ sl.nb = maskBytes sl.len ∧
      sl.sh₀ = fam₀.shift (((ρ + G * sl.T₀ : ℕ) : ℤ) - H) / 8 ∧
      sl.sh = fams.map (Family.shift · (((ρ + G * sl.T₀ : ℕ) : ℤ) - H)) := by
  simp only [slotsOf, List.mem_map, Prod.exists]
  constructor
  · rintro ⟨T₀, len, h, rfl⟩
    exact ⟨rfl, h, rfl, rfl, rfl⟩
  · obtain ⟨ρ', T₀, len, nb, sh₀, sh⟩ := sl
    dsimp only
    rintro ⟨rfl, h, rfl, rfl, rfl⟩
    exact ⟨T₀, len, h, rfl⟩

/-- Every chunk of a class gives a slot. -/
theorem exists_mem_slotsOf {H G L ρ T₀ len : ℕ} (fam₀ : Family) (fams : Array Family)
    (h : (T₀, len) ∈ chunks (classCount (2 * H + 1) G ρ) L) :
    ∃ sl ∈ slotsOf H G L fam₀ fams ρ, sl.ρ = ρ ∧ sl.T₀ = T₀ ∧ sl.len = len :=
  ⟨_, List.mem_map_of_mem h, rfl, rfl, rfl⟩

/-- The indices of a chunk of a class are at most `2 H`. -/
theorem add_mul_add_le_of_mem_slotsOf {H G L ρ : ℕ} (hG : 0 < G) {fam₀ : Family}
    {fams : Array Family} {sl : Slot} (hsl : sl ∈ slotsOf H G L fam₀ fams ρ) {t : ℕ}
    (ht : t < sl.len) : sl.ρ + G * (sl.T₀ + t) ≤ 2 * H := by
  obtain ⟨rfl, hch, -⟩ := mem_slotsOf_iff.mp hsl
  lia [add_mul_lt_of_lt_classCount (n := 2 * H + 1) hG
    (show sl.T₀ + t < classCount (2 * H + 1) G sl.ρ by lia [(le_of_mem_chunks hch).1])]

/-- The chunks of one class have pairwise different indices. -/
theorem pairwise_slotsOf (H : ℕ) {G L : ℕ} (hG : 0 < G) (hL : 0 < L) (fam₀ : Family)
    (fams : Array Family) (ρ : ℕ) :
    (slotsOf H G L fam₀ fams ρ).Pairwise fun s s' ↦ ∀ t < s.len, ∀ t' < s'.len,
      s.ρ + G * (s.T₀ + t) ≠ s'.ρ + G * (s'.T₀ + t') := by
  rw [slotsOf, chunks, List.map_map, List.pairwise_map]
  refine List.nodup_range.pairwise_of_forall_ne fun k _ k' _ hne t ht t' ht' h ↦ hne ?_
  dsimp only [Function.comp_apply] at ht ht' h
  exact eq_of_add_mul_add_eq hG hL (ht.trans_le (min_le_left _ _))
    (ht'.trans_le (min_le_left _ _)) h

/-- The chunks of the residue `r` of the denominator: those of the classes `ρ < G` that the row of
`r` modulo `G` allows. -/
theorem mem_getElem!_classSlots_iff {c : List ℤ} {d H G L : ℕ} {fam₀ : Family}
    {fams : Array Family} {r : ℕ} {sl : Slot} :
    sl ∈ (classSlots c d H G L fam₀ fams)[r]! ↔ r < G ∧ sl.ρ < G ∧
      (admitRow c d G (sqTable G) r)[(((sl.ρ : ℤ) - H) % (G : ℤ)).toNat]! = true ∧
      sl ∈ slotsOf H G L fam₀ fams sl.ρ := by
  by_cases hr : r < G
  · simp only [classSlots, Array.getElem!_map_toArray_range _ hr, List.mem_flatMap,
      List.mem_range, List.mem_ite_nil_right, hr, true_and]
    exact ⟨fun ⟨_, hρ, h, hsl⟩ ↦ (mem_slotsOf_iff.mp hsl).1 ▸ ⟨hρ, h, hsl⟩,
      fun ⟨hρ, h, hsl⟩ ↦ ⟨sl.ρ, hρ, h, hsl⟩⟩
  · rw [getElem!_neg _ _ (by simpa [classSlots] using hr)]
    exact iff_of_false List.not_mem_nil fun h ↦ hr h.1

/-- The chunks of the residue `r` of the denominator have pairwise different indices: those of
different classes differ modulo `G`. -/
theorem pairwise_getElem!_classSlots (c : List ℤ) (d H : ℕ) {G L : ℕ} (hG : 0 < G) (hL : 0 < L)
    (fam₀ : Family) (fams : Array Family) (r : ℕ) :
    (classSlots c d H G L fam₀ fams)[r]!.Pairwise fun s s' ↦ ∀ t < s.len, ∀ t' < s'.len,
      s.ρ + G * (s.T₀ + t) ≠ s'.ρ + G * (s'.T₀ + t') := by
  by_cases hr : r < G
  · simp only [classSlots, Array.getElem!_map_toArray_range _ hr]
    refine List.pairwise_flatMap.mpr ⟨fun ρ _ ↦ ?_, List.nodup_range.pairwise_of_forall_ne
      fun ρ hρ ρ' hρ' hne s hs s' hs' t _ t' _ h ↦ hne ?_⟩
    · split_ifs
      · exact pairwise_slotsOf H hG hL fam₀ fams ρ
      · exact List.Pairwise.nil
    · obtain rfl := (mem_slotsOf_iff.mp (List.mem_ite_nil_right.mp hs).2).1
      obtain rfl := (mem_slotsOf_iff.mp (List.mem_ite_nil_right.mp hs').2).1
      exact eq_of_add_mul_eq (List.mem_range.mp hρ) (List.mem_range.mp hρ') h
  · rw [getElem!_neg _ _ (by simpa [classSlots] using hr)]
    exact List.Pairwise.nil

/-- The index `a + H` of a candidate `(a, b)` with `|a| ≤ H` lies in a chunk of the residue of
`b`: that of its class `(a + H) % G`, which the row of `b` modulo `G` allows. -/
theorem exists_mem_getElem!_classSlots {c : List ℤ} {H G L : ℕ} (hG : 0 < G) (hL : 0 < L)
    (fam₀ : Family) (fams : Array Family) {a : ℤ} {b : ℕ} (hc : IsCandidate c a b)
    (ha : |a| ≤ H) :
    ∃ sl ∈ (classSlots c (BruteForce.degree c) H G L fam₀ fams)[b % G]!, ∃ t < sl.len,
      a + H = ((sl.ρ + G * (sl.T₀ + t) : ℕ) : ℤ) := by
  obtain ⟨i, hi⟩ : ∃ i : ℕ, (i : ℤ) = a + H := ⟨(a + H).toNat, by lia [abs_le.mp ha]⟩
  have hu : i / G < classCount (2 * H + 1) G (i % G) :=
    lt_classCount hG (by lia [Nat.mod_add_div i G, abs_le.mp ha])
  obtain ⟨_, len, hch, rfl, hlen⟩ := exists_mem_chunks hL hu
  obtain ⟨sl, hsl, hρ, hT₀, rfl⟩ := exists_mem_slotsOf fam₀ fams hch
  refine ⟨sl, mem_getElem!_classSlots_iff.mpr ⟨Nat.mod_lt _ hG, hρ ▸ Nat.mod_lt _ hG, ?_,
    hρ ▸ hsl⟩, i / G % L, hlen, ?_⟩
  · rw [hρ, Int.natCast_mod, Int.emod_sub_emod, hi, add_sub_cancel_right]
    exact getElem!_admitRow_of_isCandidate hG hc
  · rw [hρ, hT₀, Nat.div_add_mod', Nat.mod_add_div]
    exact hi.symm

/-! ### The families -/

theorem isSound_of_mem_filterMap_mkFamily {c : List ℤ} {G nb : ℕ} {g₁ : List (List Table)}
    (hg₁ : ∀ g ∈ g₁, ∀ T ∈ g, ∃ m > 0, T = mkTable c (BruteForce.degree c) m) {F : Family}
    (hF : F ∈ g₁.filterMap (mkFamily G nb)) : F.IsSound c G nb := by
  obtain ⟨g, hg, hF⟩ := List.mem_filterMap.mp hF
  exact mkFamily_isSound (hg₁ g hg) hF

theorem isSound_fst_stageFamilies {c : List ℤ} {G nb : ℕ} {g₁ : List (List Table)}
    (hg₁ : ∀ g ∈ g₁, ∀ T ∈ g, ∃ m > 0, T = mkTable c (BruteForce.degree c) m) :
    (stageFamilies G nb g₁).1.IsSound c G nb := by
  rw [stageFamilies]
  split
  · exact trivialFamily_isSound c G nb
  · exact isSound_of_mem_filterMap_mkFamily hg₁ (‹_ = _› ▸ List.mem_cons_self)

theorem isSound_of_mem_snd_stageFamilies {c : List ℤ} {G nb : ℕ} {g₁ : List (List Table)}
    (hg₁ : ∀ g ∈ g₁, ∀ T ∈ g, ∃ m > 0, T = mkTable c (BruteForce.degree c) m) {F : Family}
    (hF : F ∈ (stageFamilies G nb g₁).2) : F.IsSound c G nb := by
  rw [stageFamilies] at hF
  split at hF
  · simp at hF
  · exact isSound_of_mem_filterMap_mkFamily hg₁
      (‹_ = _› ▸ List.mem_cons_of_mem _ (List.mem_toArray.mp hF))

/-! ### The context -/

/-- The chunks of the context of the search fit its families, whose rows are made for the masks of
the chunks of `L` numerators. -/
theorem isFit_of_mem_getElem!_slots_searchContext {c : List ℤ} {d H G L : ℕ}
    {g₁ : List (List Table)} {t₂ : List Table}
    {reg : Option (Array (Option (ℤ × ℕ) × Option (ℤ × ℕ)))} {r : ℕ} {sl : Slot}
    (hsl : sl ∈ (searchContext c d H G L g₁ t₂ reg).slots[r]!) :
    sl.IsFit (searchContext c d H G L g₁ t₂ reg) (maskBytes L) := by
  obtain ⟨-, hρ, -, hsl⟩ := mem_getElem!_classSlots_iff.mp hsl
  obtain ⟨-, hch, hnb, hsh₀, hsh⟩ := mem_slotsOf_iff.mp hsl
  exact ⟨hρ, hnb ▸ le_eight_mul_maskBytes _, hnb ▸ monotone_maskBytes (le_of_mem_chunks hch).2.1,
    hsh₀, hsh⟩

/-- The context of the search is sound when the tables of both stages are tables of `c`. -/
theorem isSound_searchContext {c : List ℤ} {H G L : ℕ} (hG : 0 < G) {g₁ : List (List Table)}
    (hg₁ : ∀ g ∈ g₁, ∀ T ∈ g, ∃ m > 0, T = mkTable c (BruteForce.degree c) m) {t₂ : List Table}
    (ht₂ : ∀ T ∈ t₂, ∃ m > 0, T = mkTable c (BruteForce.degree c) m)
    (reg : Option (Array (Option (ℤ × ℕ) × Option (ℤ × ℕ)))) :
    (searchContext c (BruteForce.degree c) H G L g₁ t₂ reg).IsSound (maskBytes L) where
  d_eq := rfl
  G_pos := hG
  fam₀ := isSound_fst_stageFamilies hg₁
  fams _ hF := isSound_of_mem_snd_stageFamilies hg₁ hF
  tabs To hTo := by
    obtain ⟨T, hT, rfl⟩ := Array.mem_map.mp hTo
    obtain ⟨m, hm, rfl⟩ := ht₂ T (List.mem_toArray.mp hT)
    exact ⟨m, hm, rfl⟩
  slots _ _ hsl := isFit_of_mem_getElem!_slots_searchContext hsl

/-! ### The search -/

/-- The search lists the points of its denominators (`Ratpoints.FastMask.denPoints`), the last one
first, leaving out those whose residue modulo the step allows no class. -/
theorem search_eq (c : List ℤ) (d H G L : ℕ) (g₁ : List (List Table)) (t₂ : List Table)
    (reg : Option (Array (Option (ℤ × ℕ) × Option (ℤ × ℕ)))) (dens : List ℕ) :
    search c d H G L g₁ t₂ reg dens =
      (dens.filter fun b ↦
        !(searchContext c d H G L g₁ t₂ reg).slots[b % G]!.isEmpty).reverse.flatMap
          (denPoints (searchContext c d H G L g₁ t₂ reg)) := by
  simp only [search]
  rw [densLoop_eq _ _ rfl, List.append_nil]

/-- Every point of the search comes from the exact check of a numerator `x - H` with `x ≤ 2 H`
and a denominator of `dens`. -/
theorem exists_mem_pointsOfDen_of_mem_search {c : List ℤ} {d H G L : ℕ} (hG : 0 < G)
    {g₁ : List (List Table)} {t₂ : List Table}
    {reg : Option (Array (Option (ℤ × ℕ) × Option (ℤ × ℕ)))} {dens : List ℕ} {p : ℤ × ℤ × ℤ}
    (h : p ∈ search c d H G L g₁ t₂ reg dens) :
    ∃ b ∈ dens, ∃ x ≤ 2 * H, p ∈ pointsOfDen c d b [(x : ℤ) - H] := by
  rw [search_eq, List.mem_flatMap] at h
  obtain ⟨b, hb, hp⟩ := h
  obtain ⟨sl, hsl, t, ht, hp⟩ := exists_mem_pointsOfDen_of_mem_denPoints hp
  exact ⟨b, (List.mem_filter.mp (List.mem_reverse.mp hb)).1, _,
    add_mul_add_le_of_mem_slotsOf hG (mem_getElem!_classSlots_iff.mp hsl).2.2.2 ht, hp⟩

/-- Assuming Sturm's theorem, the search with tables of `c` lists the points of every candidate
`(a, b)` with `|a| ≤ H` and `b` among its denominators: the index `a + H` lies in a chunk of the
residue of `b` and in the hull of the region
(`Ratpoints.FastMask.mem_Icc_regionHull_of_isCandidate`). -/
theorem mem_search_of_mem_pointsOfDen (hS : SturmTheorem) {c : List ℤ} {H G L : ℕ} (hG : 0 < G)
    (hL : 0 < L) {g₁ : List (List Table)}
    (hg₁ : ∀ g ∈ g₁, ∀ T ∈ g, ∃ m > 0, T = mkTable c (BruteForce.degree c) m) {t₂ : List Table}
    (ht₂ : ∀ T ∈ t₂, ∃ m > 0, T = mkTable c (BruteForce.degree c) m) (depth : ℕ)
    {dens : List ℕ} {a : ℤ} {b : ℕ} (hb : b ∈ dens) (hb₁ : 1 ≤ b) (hc : IsCandidate c a b)
    (ha : |a| ≤ H) {p : ℤ × ℤ × ℤ} (hp : p ∈ pointsOfDen c (BruteForce.degree c) b [a]) :
    p ∈ search c (BruteForce.degree c) H G L g₁ t₂ (region c (BruteForce.degree c) H depth)
      dens := by
  obtain ⟨sl, hsl, t, ht, hx⟩ := exists_mem_getElem!_classSlots hG hL
    (stageFamilies G (maskBytes L) g₁).1 (stageFamilies G (maskBytes L) g₁).2 hc ha
  rw [search_eq, List.mem_flatMap]
  refine ⟨b, List.mem_reverse.mpr (List.mem_filter.mpr ⟨hb, ?_⟩),
    mem_denPoints_of_mem_pointsOfDen (isSound_searchContext hG hg₁ ht₂ _) hc hsl ht hx
      (add_mul_add_le_of_mem_slotsOf hG (mem_getElem!_classSlots_iff.mp hsl).2.2.2 ht)
      (fun R hR ↦ ?_) hp⟩
  · rw [Bool.not_eq_true', List.isEmpty_eq_false_iff]
    exact List.ne_nil_of_mem hsl
  · obtain ⟨R', hR', rfl⟩ := Option.map_eq_some_iff.mp hR
    exact mem_Icc_regionHull_of_isCandidate hS hR' (fun _ _ ↦ rfl) hb₁ hc ha hx.symm

/-- The search lists each point once: the points of different denominators differ in `z`, and
the chunks of one denominator have pairwise different indices. -/
theorem nodup_search (c : List ℤ) (d H : ℕ) {G L : ℕ} (hG : 0 < G) (hL : 0 < L)
    (g₁ : List (List Table)) (t₂ : List Table)
    (reg : Option (Array (Option (ℤ × ℕ) × Option (ℤ × ℕ)))) {dens : List ℕ} (hdens : dens.Nodup) :
    (search c d H G L g₁ t₂ reg dens).Nodup := by
  rw [search_eq]
  exact nodup_flatMap_denPoints hG (List.nodup_reverse.mpr (hdens.filter _))
    fun _ _ ↦ pairwise_getElem!_classSlots _ _ _ hG hL _ _ _

/-! ### The parameters -/

theorem chooseStep_mem (c : List ℤ) (d H L₀ : ℕ) (dens : List ℕ) :
    chooseStep c d H L₀ dens ∈ [16, 8, 4, 2, 1] :=
  List.fst_foldl_mem_cons (fun _ _ ↦ by dsimp only; split_ifs <;> simp) _ _

theorem G_choose_pos (c : List ℤ) (d H : ℕ) (dens : List ℕ) (tu : Tuning) :
    0 < (choose c d H dens tu).G := by
  simp only [choose]
  split_ifs
  · have := chooseStep_mem c d H (orDefault tu.L 16384) dens
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    lia
  · lia

theorem L_choose_pos (c : List ℤ) (d H : ℕ) (dens : List ℕ) (tu : Tuning) :
    0 < (choose c d H dens tu).L :=
  Nat.one_pos.trans_le (le_max_left ..)

/-- The tables of the moduli prime to the step that `Ratpoints.FastMask.choose` takes are tables
`Ratpoints.Fast.mkTable c d m` with `m > 0`. -/
theorem exists_pos_eq_mkTable_of_mem_takeTables {c : List ℤ} {d κ G E : ℕ} {T : Table}
    (hT : T ∈ takeTables c d κ ((candidateModuli ++ furtherModuli).filter fun m ↦
      Nat.gcd m G == 1) E) : ∃ m > 0, T = mkTable c d m := by
  obtain ⟨m, hm, rfl⟩ := exists_mem_eq_mkTable_of_mem_takeTables hT
  exact ⟨m, pos_of_mem_candidateModuli_append_furtherModuli (List.mem_filter.mp hm).1, rfl⟩

theorem exists_pos_eq_mkTable_of_mem_stage₁_choose {c : List ℤ} {d H : ℕ} {dens : List ℕ}
    {tu : Tuning} {g : List Table} (hg : g ∈ (choose c d H dens tu).stage₁) {T : Table}
    (hT : T ∈ g) : ∃ m > 0, T = mkTable c d m := by
  simp only [choose, List.mem_map, List.mem_mergeSort] at hg
  obtain ⟨⟨g', s⟩, hx, rfl⟩ := hg
  obtain ⟨g'', hg'', h⟩ := List.mem_map.mp (List.mem_of_mem_take hx)
  obtain rfl : g'' = g' := congr(Prod.fst $h)
  exact exists_pos_eq_mkTable_of_mem_takeTables (mem_of_mem_groupTables hg'' hT)

theorem exists_pos_eq_mkTable_of_mem_stage₂_choose {c : List ℤ} {d H : ℕ} {dens : List ℕ}
    {tu : Tuning} {T : Table} (hT : T ∈ (choose c d H dens tu).stage₂) :
    ∃ m > 0, T = mkTable c d m := by
  simp only [choose, List.mem_append, List.mem_flatMap] at hT
  rcases hT with hT | ⟨⟨g, s⟩, hx, hT⟩
  · exact ⟨16, by decide, List.mem_singleton.mp (List.mem_ite_nil_left.mp hT).2⟩
  · obtain ⟨g', hg', h⟩ := List.mem_map.mp (List.mem_of_mem_drop hx)
    obtain rfl : g' = g := congr(Prod.fst $h)
    exact exists_pos_eq_mkTable_of_mem_takeTables (mem_of_mem_groupTables hg' hT)

/-! ### The points -/

theorem isPoint_and_inRegion_of_mem_sievePoints {c : List ℤ} {H : ℕ} {bLow bHigh : ℤ}
    {tu : Tuning} {p : ℤ × ℤ × ℤ} (h : p ∈ sievePoints c H bLow bHigh tu) :
    IsPoint c H p ∧ InRegion [] bLow bHigh p := by
  rw [sievePoints, List.mem_append] at h
  rcases h with h | h
  · obtain ⟨hH, h⟩ := List.mem_ite_nil_right.mp h
    obtain ⟨hx, hz, hg, hy⟩ := mem_pointsOfDen_singleton_iff.mp h
    exact ⟨⟨hy, hg, .inr ⟨hz, hx⟩, by simp [hx, hH], by simp [hz]⟩, .inl hz⟩
  · obtain ⟨b, hb, x, hx, hp⟩ := exists_mem_pointsOfDen_of_mem_search (G_choose_pos ..) h
    obtain ⟨hpx, hz, hg, hy⟩ := mem_pointsOfDen_singleton_iff.mp hp
    obtain ⟨h1, h2, h3, h4⟩ := mem_denominators hb
    exact ⟨⟨hy, hg, .inl (by lia), by rw [hpx, abs_le]; lia, by lia⟩,
      .inr ⟨by lia, by lia, .inl rfl⟩⟩

/-- The search without the reversal lists every point of the region, assuming Sturm's theorem, on
which the region of the numerators rests
(`Ratpoints.FastMask.mem_Icc_regionHull_of_isCandidate`). -/
theorem mem_sievePoints_of_isPoint (hS : SturmTheorem) {c : List ℤ} {H : ℕ} {bLow bHigh : ℤ}
    {tu : Tuning} {p : ℤ × ℤ × ℤ} (hp : IsPoint c H p) (hr : InRegion [] bLow bHigh p) :
    p ∈ sievePoints c H bLow bHigh tu := by
  obtain ⟨x, y, z⟩ := p
  obtain ⟨hy, hg, hz | ⟨rfl, rfl⟩, hx, hzH⟩ := hp
  · obtain ⟨b, rfl⟩ : ∃ b : ℕ, z = b := ⟨z.toNat, by lia⟩
    obtain ⟨h3, h4⟩ : bLow ≤ b ∧ (bHigh < 1 ∨ (b : ℤ) ≤ bHigh) := by
      rcases hr with h | ⟨h3, h4, -⟩
      · simp at h
        lia
      · exact ⟨h3, h4⟩
    refine List.mem_append_right _ (mem_search_of_mem_pointsOfDen hS (G_choose_pos ..)
      (L_choose_pos ..) (fun _ ↦ exists_pos_eq_mkTable_of_mem_stage₁_choose)
      (fun _ ↦ exists_pos_eq_mkTable_of_mem_stage₂_choose) _ (mem_denominators_of_isCandidate
        (by lia) (by lia) h3 h4 ⟨hg, y, hy⟩) (by lia) ⟨hg, y, hy⟩ hx
        (mem_pointsOfDen_singleton_iff.mpr ⟨rfl, rfl, hg, hy⟩))
  · refine List.mem_append_left _ ?_
    simp only [show 1 ≤ H by simpa using hx, ↓reduceIte]
    exact mem_pointsOfDen_singleton_iff.mpr ⟨rfl, rfl, hg, hy⟩

theorem nodup_sievePoints (c : List ℤ) (H : ℕ) (bLow bHigh : ℤ) (tu : Tuning) :
    (sievePoints c H bLow bHigh tu).Nodup := by
  rw [sievePoints]
  refine List.Nodup.append ?_ (nodup_search _ _ _ (G_choose_pos ..) (L_choose_pos ..) _ _ _
    (nodup_denominators ..)) fun p hp hp' ↦ ?_
  · split_ifs
    · exact nodup_pointsOfDen _ _ _ (List.nodup_singleton 1)
    · exact List.nodup_nil
  · have h0 : p.2.2 = 0 := snd_snd_eq_of_mem_pointsOfDen (List.mem_ite_nil_right.mp hp).2
    obtain ⟨b, hb, _, -, hq⟩ := exists_mem_pointsOfDen_of_mem_search (G_choose_pos ..) hp'
    lia [(mem_denominators hb).1, snd_snd_eq_of_mem_pointsOfDen hq]

/-- **The fast search lists only points** of height at most `H` with their denominator in the range
of `bLow` and `bHigh`, for every coefficient list, every height bound, every range and every setting
of the parameters: when the coefficients are reversed, the search of the reversed list lists only
points, which `Ratpoints.Sieve.swapPoint` maps to points (`Ratpoints.Sieve.isPoint_swapPoint`), of
the whole box. -/
theorem isPoint_and_inRegion_of_mem_fastPoints {c : List ℤ} {H : ℕ} {bLow bHigh : ℤ}
    {tu : Fast.Tuning} {p : ℤ × ℤ × ℤ} (h : p ∈ fastPoints c H bLow bHigh tu) :
    IsPoint c H p ∧ InRegion [] bLow bHigh p := by
  rw [fastPoints] at h
  split at h
  · obtain ⟨hb, hsw⟩ := isFullBox_and_binaryForm_eq_of_reversed_eq ‹_›
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
    have hp := Sieve.isPoint_swapPoint hsw (isPoint_and_inRegion_of_mem_sievePoints hq).1
    exact ⟨hp, hp.2.inRegion_of_isFullBox hb⟩
  · exact isPoint_and_inRegion_of_mem_sievePoints h

/-- **The fast search lists every point** of height at most `H` with its denominator in the range
of `bLow` and `bHigh`, assuming Sturm's theorem, on which the region of the search rests: when the
coefficients are reversed, the point mapped by `Ratpoints.Sieve.swapPoint` is a point of the
reversed list, of the whole box. -/
theorem mem_fastPoints_of_isPoint (hS : SturmTheorem) {c : List ℤ} {H : ℕ} {bLow bHigh : ℤ}
    {tu : Fast.Tuning} {p : ℤ × ℤ × ℤ} (hp : IsPoint c H p) (hr : InRegion [] bLow bHigh p) :
    p ∈ fastPoints c H bLow bHigh tu := by
  rw [fastPoints]
  split
  · obtain ⟨-, hsw⟩ := isFullBox_and_binaryForm_eq_of_reversed_eq ‹_›
    have hq := Sieve.isPoint_swapPoint (fun x z ↦ (hsw z x).symm) hp
    exact List.mem_map.mpr ⟨_, mem_sievePoints_of_isPoint hS hq
      (hq.2.inRegion_of_isFullBox ⟨rfl, le_rfl, .inl one_pos⟩), Sieve.swapPoint_swapPoint hp.2.2.1⟩
  · exact mem_sievePoints_of_isPoint hS hp hr

/-- **The fast search lists exactly the points** of height at most `H` with their denominator in
the range of `bLow` and `bHigh`, for every coefficient list, every height bound, every range and
every setting of the parameters, assuming Sturm's theorem. -/
theorem mem_fastPoints_iff {c : List ℤ} {H : ℕ} {bLow bHigh : ℤ} {tu : Fast.Tuning}
    {p : ℤ × ℤ × ℤ} (hS : SturmTheorem) :
    p ∈ fastPoints c H bLow bHigh tu ↔ IsPoint c H p ∧ InRegion [] bLow bHigh p :=
  ⟨isPoint_and_inRegion_of_mem_fastPoints, fun ⟨hp, hr⟩ ↦ mem_fastPoints_of_isPoint hS hp hr⟩

/-- **The fast search lists each point once**: when the coefficients are reversed,
`Ratpoints.Sieve.swapPoint` is injective on the points of the reversed list
(`Ratpoints.Sieve.swapPoint_inj`). -/
theorem nodup_fastPoints (c : List ℤ) (H : ℕ) (bLow bHigh : ℤ) (tu : Fast.Tuning) :
    (fastPoints c H bLow bHigh tu).Nodup := by
  rw [fastPoints]
  split
  · refine (nodup_sievePoints ..).map_on fun q hq q' hq' ↦ (Sieve.swapPoint_inj ?_ ?_).mp
    exacts [(isPoint_and_inRegion_of_mem_sievePoints hq).1.2.2.1,
      (isPoint_and_inRegion_of_mem_sievePoints hq').1.2.2.1]
  · exact nodup_sievePoints ..

end FastMask

end Ratpoints

end

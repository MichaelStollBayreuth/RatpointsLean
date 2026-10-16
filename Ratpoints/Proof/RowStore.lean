/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Proof.CompositeRows

import Ratpoints.Proof.Containers
import Ratpoints.Proof.PrimeRows
import Ratpoints.Proof.Words
import Std.Data.HashMap.Lemmas
import Std.Tactic.Do

/-!
# The rows built into the tables of a run

The tables of rows of a run (`Ratpoints.Sieve.RowStore`) as the builders change them: the table of
an entry after a row is stored into it (`Ratpoints.Sieve.RowStore.getD_publish`), which keeps the
size of every table (`Ratpoints.Sieve.RowStore.size_getD_publish`), and the rows of the store after
it, the row at its place and the others as they were (`Ratpoints.Sieve.RowStore.row?_publish`); a
store that grows by rows satisfying a predicate, keeping its tables of rows with their sizes and its
rows (`Ratpoints.Sieve.RowStore.Grows`); and the contracts of the calls of the builders through the
tables of rows, as `@[spec]` theorems: the call through the function pointer of the entry of a
factor (`Ratpoints.Sieve.initFactorRow_spec`), the rows of the factors of a product read from the
tables of rows of their entries or built into them (`Ratpoints.Sieve.factorRows_spec`), the rows of
a product (`Ratpoints.Sieve.sieveInitProduct_spec`), the row of a sieve entry built by its builder
(`Ratpoints.Sieve.SieveEntry.initRow_spec`) and read from its table of rows or built into it
(`Ratpoints.Sieve.SieveEntry.fetchRow_spec`). Every row that they return or store is a closed form
(`Ratpoints.Sieve.closedRow`), and no row is replaced. The invariant of the store of a run comes
with stage F4.

## Main definitions

* `Ratpoints.Sieve.RowStore.Grows`: a store grown from another by rows satisfying a predicate.
* `Ratpoints.Sieve.Factor.Buildable`, `Ratpoints.Sieve.Factor.Builds`: what the builder of the
  rows of a factor needs of its tables, and the residues at which it is called.
* `Ratpoints.Sieve.FactorRow`, `Ratpoints.Sieve.FactorRowsPre`, `Ratpoints.Sieve.ProductRowsPre`,
  `Ratpoints.Sieve.InitRowPre`: the rows that building the rows of the factors of a product adds,
  and what building the rows of the factors, of a product and of an entry needs.

## Main statements

* `Ratpoints.Sieve.RowStore.getD_publish`, `Ratpoints.Sieve.RowStore.size_getD_publish`: the table
  of an entry after a row is stored, and its size.
* `Ratpoints.Sieve.RowStore.row?_publish`: the rows of the store after a row is stored.
* `Ratpoints.Sieve.initFactorRow_spec`, `Ratpoints.Sieve.factorRows_spec`,
  `Ratpoints.Sieve.sieveInitProduct_spec`, `Ratpoints.Sieve.SieveEntry.initRow_spec`,
  `Ratpoints.Sieve.SieveEntry.fetchRow_spec`: the rows built through the tables of rows are closed
  forms.

## Implementation notes

The file uses Lean core and `Std` only, as the contracts of the sieve do.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace Ratpoints

namespace Sieve

/-! ### The tables of rows -/

theorem RowStore.getD_publish (s : RowStore) (ref ref' : EntryRef) (r : Nat) (row : Array UInt64) :
    (s.publish ref r row).getD ref' #[] =
      if ref = ref' then (s.getD ref #[]).set! r (some row) else s.getD ref' #[] := by
  rw [RowStore.publish, Std.HashMap.getD_modify]
  by_cases h : ref = ref'
  · subst h
    cases hs : s[ref]? <;> simp [Std.HashMap.getD_eq_getD_getElem?, hs]
  · simp [h]

theorem RowStore.size_getD_publish (s : RowStore) (ref ref' : EntryRef) (r : Nat)
    (row : Array UInt64) : ((s.publish ref r row).getD ref' #[]).size = (s.getD ref' #[]).size := by
  rw [RowStore.getD_publish]
  split
  · subst_vars
    simp
  · rfl

/-- The rows of the store after a row is stored: the row at its place, when the table has that
place, and the others as they were. -/
theorem RowStore.row?_publish (s : RowStore) (ref ref' : EntryRef) (r r' : Nat)
    (row : Array UInt64) : (s.publish ref r row).row? ref' r' =
      if ref = ref' ∧ r = r' ∧ r < (s.getD ref #[]).size then some row else s.row? ref' r' := by
  simp only [RowStore.row?, RowStore.getD_publish]
  by_cases h : ref = ref'
  · subst h
    simp only [true_and, ↓reduceIte, Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds]
    by_cases hr : r = r'
    · subst hr
      by_cases hs : r < (s.getD ref #[]).size <;> simp [hs]
    · simp [hr]
  · simp [h]

/-- The store `s'` keeps the tables of rows of `s` with their sizes and their rows, and its other
rows, the row `row` at the residue `r` of the table of rows `ref`, satisfy `P ref r row`: what
building rows into the tables of rows does to the store. -/
def RowStore.Grows (s s' : RowStore) (P : EntryRef → Nat → Array UInt64 → Prop) : Prop :=
  (∀ ref, (s'.getD ref #[]).size = (s.getD ref #[]).size) ∧
    (∀ ref r row, s.row? ref r = some row → s'.row? ref r = some row) ∧
    ∀ ref r row, s'.row? ref r = some row → s.row? ref r = some row ∨ P ref r row

theorem RowStore.Grows.refl (s : RowStore) (P : EntryRef → Nat → Array UInt64 → Prop) :
    s.Grows s P :=
  ⟨fun _ ↦ rfl, fun _ _ _ h ↦ h, fun _ _ _ h ↦ .inl h⟩

theorem RowStore.Grows.trans {s1 s2 s3 : RowStore} {P : EntryRef → Nat → Array UInt64 → Prop}
    (h1 : s1.Grows s2 P) (h2 : s2.Grows s3 P) : s1.Grows s3 P := by
  refine ⟨fun ref ↦ by rw [h2.1, h1.1], fun ref r row h ↦ h2.2.1 _ _ _ (h1.2.1 _ _ _ h),
    fun ref r row h ↦ ?_⟩
  rcases h2.2.2 _ _ _ h with h | h
  · exact h1.2.2 _ _ _ h
  · exact .inr h

/-- A row stored at a place where the store has no row. -/
theorem RowStore.grows_publish {s : RowStore} {P : EntryRef → Nat → Array UInt64 → Prop}
    {ref : EntryRef} {r : Nat} {row : Array UInt64} (h : s.row? ref r = none) (hP : P ref r row) :
    s.Grows (s.publish ref r row) P := by
  refine ⟨fun ref' ↦ RowStore.size_getD_publish .., fun ref' r' row' h' ↦ ?_,
    fun ref' r' row' h' ↦ ?_⟩
  · rw [RowStore.row?_publish, ite_eq_right fun ⟨h1, h2, _⟩ ↦ by subst h1 h2; simp [h] at h']
    exact h'
  · rw [RowStore.row?_publish] at h'
    split at h'
    · rename_i hc
      obtain ⟨rfl, rfl, -⟩ := hc
      exact .inr (Option.some.inj h' ▸ hP)
    · exact .inl h'

/-! ### The builder of the entry of a factor -/

/-- What the builder of the rows of a factor needs of its tables: a positive modulus; for a prime
`p` the inverses of its residues below `p`, and `p mod 64 ≠ 0` for a prime of at least 64, whose
builder `CODE_INIT_SIEVE2` shifts by `p mod 64`; for a prime power `m` at most
`64 Ratpoints.modWords` and its inverses below `m`. -/
def Factor.Buildable : Factor → Prop
  | .prime t => 0 < t.p ∧ (64 ≤ t.p → t.p % 64 ≠ 0) ∧ ∀ r < t.p, t.inverses[r]! < t.p
  | .power pw => 0 < pw.m ∧ pw.m ≤ 64 * modWords ∧ ∀ x < pw.m, pw.inv[x]! < pw.m

/-- The residues at which the builder of the rows of a factor is called: below the modulus, and
other than `0` for a prime, whose row of `0` is in its table of rows from the start
(`Ratpoints.Sieve.primeRows`), the builders of a prime being wrong at `0`. -/
def Factor.Builds : Factor → Nat → Prop
  | .prime t, b => 0 < b ∧ b < t.p
  | .power pw, b => b < pw.m

theorem Factor.Builds.lt_modulus {f : Factor} {b : Nat} (h : f.Builds b) : b < f.modulus := by
  cases f with
  | prime t => exact h.2
  | power pw => exact h

theorem initFactorRow_pre_sieve1 {t : Entry} {b : Nat} (hp : t.p < 64)
    (pre : (Factor.prime t).Buildable ∧ (Factor.prime t).Builds b) :
    0 < b ∧ b < t.p ∧ t.p < 64 ∧ t.inverses[b]! < t.p :=
  ⟨pre.2.1, pre.2.2, hp, pre.1.2.2 b pre.2.2⟩

theorem initFactorRow_pre_sieve2 {t : Entry} {b : Nat} (hp : ¬t.p < 64)
    (pre : (Factor.prime t).Buildable ∧ (Factor.prime t).Builds b) :
    0 < b ∧ b < t.p ∧ 64 ≤ t.p ∧ t.p % 64 ≠ 0 ∧ t.inverses[b]! < t.p :=
  ⟨pre.2.1, pre.2.2, by lia, pre.1.2.1 (by lia), pre.1.2.2 b pre.2.2⟩

theorem initFactorRow_pre_power {pw : Power} {b : Nat}
    (pre : (Factor.power pw).Buildable ∧ (Factor.power pw).Builds b) :
    b < pw.m ∧ pw.m ≤ 64 * modWords ∧ pw.inv[b]! < pw.m :=
  ⟨pre.2, pre.1.2.1, pre.1.2.2 b pre.2⟩

/-- The row of the residue `b` built by the builder of the kind of the factor `f`, the call through
the function pointer of the entry of the factor, is the closed form of the row of `b` of the factor,
for the residues at which it is called (`Ratpoints.Sieve.Factor.Builds`), and the builder stores it
into the table of rows `ref`. -/
@[spec]
theorem initFactorRow_spec (f : Factor) (ref : EntryRef) (b : Nat) (store : RowStore) :
    ⦃ f.Buildable ∧ f.Builds b ⦄ initFactorRow f.init ref f b store
    ⦃ fun r ↦ r.1 = closedRow f.admits f.modulus b ∧
        r.2 = store.publish ref b (closedRow f.admits f.modulus b) ⦄ := by
  cases f with
  | prime t =>
    by_cases hp : t.p < 64
    · rw [show (Factor.prime t).init = .sieve1 by simp [Factor.init, sieveInit, hp]]
      vcgen [initFactorRow]
      all_goals first
        | exact initFactorRow_pre_sieve1 hp ‹_›
        | exact ‹_›
    · rw [show (Factor.prime t).init = .sieve2 by simp [Factor.init, sieveInit, hp]]
      vcgen [initFactorRow]
      all_goals first
        | exact initFactorRow_pre_sieve2 hp ‹_›
        | exact ‹_›
  | power pw =>
    rw [show (Factor.power pw).init = .power from rfl]
    vcgen [initFactorRow]
    all_goals first
      | exact initFactorRow_pre_power ‹_›
      | exact ‹_›

/-! ### The rows of the factors of a product -/

/-- A row that building the rows of the factors of `e` adds to the store: at the residue `r` of the
table of rows `ref`, the closed form of the row of `r` of a factor of `e` whose entry is `ref`. -/
def FactorRow (e : SieveEntry) (ref : EntryRef) (r : Nat) (row : Array UInt64) : Prop :=
  ∃ f ∈ e.factors, f.ref = ref ∧ row = closedRow f.admits f.modulus r

/-- What building the rows of the factors of `e` needs of them and of the store: their builders have
what they need, the rows in the tables of rows of their entries are closed forms, a row that is
absent below the modulus is one at which the builder of the factor may be called (for a prime, its
row of `0` is in its table of rows), and two factors with one entry have the same closed forms of
their rows. -/
structure FactorRowsPre (e : SieveEntry) (store : RowStore) : Prop where
  /-- The builders of the factors have what they need. -/
  buildable : ∀ f ∈ e.factors, f.Buildable
  /-- The rows in the tables of rows of the entries of the factors are closed forms. -/
  rows : ∀ f ∈ e.factors, ∀ r row, store.row? f.ref r = some row →
    row = closedRow f.admits f.modulus r
  /-- A row absent below the modulus is one that the builder of the factor may build. -/
  builds : ∀ f ∈ e.factors, ∀ r < f.modulus, store.row? f.ref r = none → f.Builds r
  /-- Two factors with one entry have the same closed forms of their rows. -/
  coherent : ∀ f ∈ e.factors, ∀ f' ∈ e.factors, f.ref = f'.ref →
    closedRow f.admits f.modulus = closedRow f'.admits f'.modulus

/-- The invariant of the loop of `Ratpoints.Sieve.factorRows` over the factors `pref` done, on the
store and the rows: the rows of those factors in closed form at the residues of `b`, and the store
grown by rows of factors. -/
def FactorRowsInvariant (e : SieveEntry) (b : Nat) (store : RowStore) (pref : List Factor)
    (st : RowStore × Array (Array UInt64)) : Prop :=
  st.2.toList = pref.map (fun f ↦ closedRow f.admits f.modulus (b % f.modulus)) ∧
    store.Grows st.1 (FactorRow e)

theorem factorRowsInvariant_nil (e : SieveEntry) (b : Nat) (store : RowStore) :
    FactorRowsInvariant e b store [] (store, #[]) :=
  ⟨rfl, RowStore.Grows.refl _ _⟩

/-- A row of a factor of `e` present in a store grown from one where they were closed forms is the
closed form of the factor: rows are never replaced, and two factors with one entry have the same
closed forms of their rows. -/
theorem FactorRowsPre.eq_closedRow {e : SieveEntry} {store s : RowStore}
    (pre : FactorRowsPre e store) (hs : store.Grows s (FactorRow e)) {f : Factor}
    (hf : f ∈ e.factors) {r : Nat} {row : Array UInt64} (h : s.row? f.ref r = some row) :
    row = closedRow f.admits f.modulus r := by
  rcases hs.2.2 _ _ _ h with h' | ⟨f', hf', href, rfl⟩
  · exact pre.rows f hf r row h'
  · rw [pre.coherent f' hf' f hf href]

/-- A factor whose row is in the store. -/
theorem FactorRowsInvariant.push_some {e : SieveEntry} {b : Nat} {store : RowStore}
    {pref suff : List Factor} {f : Factor} {st : RowStore × Array (Array UInt64)}
    {fr : Array UInt64} (pre : FactorRowsPre e store) (hl : e.factors = pref ++ f :: suff)
    (h : FactorRowsInvariant e b store pref st) (hr : st.1.row? f.ref (b % f.modulus) = some fr) :
    FactorRowsInvariant e b store (pref ++ [f]) (st.1, st.2.push fr) := by
  have hf : f ∈ e.factors := by simp [hl]
  refine ⟨?_, h.2⟩
  rw [Array.toList_push, h.1, List.map_append, List.map_singleton,
    pre.eq_closedRow h.2 hf hr]

/-- A factor whose row the builder of its entry builds into the store. -/
theorem FactorRowsInvariant.push_none {e : SieveEntry} {b : Nat} {store : RowStore}
    {pref suff : List Factor} {f : Factor} {st : RowStore × Array (Array UInt64)}
    {r : Array UInt64 × RowStore} (hl : e.factors = pref ++ f :: suff)
    (h : FactorRowsInvariant e b store pref st) (hr : st.1.row? f.ref (b % f.modulus) = none)
    (hb : r.1 = closedRow f.admits f.modulus (b % f.modulus) ∧
      r.2 = st.1.publish f.ref (b % f.modulus) (closedRow f.admits f.modulus (b % f.modulus))) :
    FactorRowsInvariant e b store (pref ++ [f]) (r.2, st.2.push r.1) := by
  have hf : f ∈ e.factors := by simp [hl]
  refine ⟨by rw [Array.toList_push, h.1, List.map_append, List.map_singleton, hb.1], ?_⟩
  rw [hb.2]
  exact h.2.trans (RowStore.grows_publish hr ⟨f, hf, rfl, rfl⟩)

/-- The builder of the entry of a factor is called at a residue at which it may be. -/
theorem FactorRowsInvariant.pre_none {e : SieveEntry} {b : Nat} {store : RowStore}
    {pref suff : List Factor} {f : Factor} {st : RowStore × Array (Array UInt64)}
    (pre : FactorRowsPre e store) (hl : e.factors = pref ++ f :: suff)
    (h : FactorRowsInvariant e b store pref st) (hr : st.1.row? f.ref (b % f.modulus) = none) :
    f.Buildable ∧ f.Builds (b % f.modulus) := by
  have hf : f ∈ e.factors := by simp [hl]
  have hpos : 0 < f.modulus := by
    have := pre.buildable f hf
    cases f with
    | prime t => exact this.1
    | power pw => exact this.1
  refine ⟨pre.buildable f hf, pre.builds f hf _ (Nat.mod_lt _ hpos) ?_⟩
  cases hs : store.row? f.ref (b % f.modulus) with
  | none => rfl
  | some row => rw [h.2.2.1 _ _ _ hs] at hr; cases hr

theorem FactorRowsInvariant.post {e : SieveEntry} {b : Nat} {store : RowStore}
    {st : RowStore × Array (Array UInt64)} (h : FactorRowsInvariant e b store e.factors st) :
    st.2.toList = e.factors.map (fun f ↦ closedRow f.admits f.modulus (b % f.modulus)) ∧
      store.Grows st.1 (FactorRow e) :=
  h

attribute [local irreducible] FactorRowsInvariant in
/-- The rows of the factors of `e` at the residues of `b` modulo their moduli, read from the tables
of rows of their entries or built into them, are their closed forms, and the store grows by rows of
factors (`Ratpoints.Sieve.FactorRow`), never replacing one. -/
@[spec]
theorem factorRows_spec (e : SieveEntry) (b : Nat) (store : RowStore) :
    ⦃ FactorRowsPre e store ⦄ factorRows e b store
    ⦃ fun r ↦ r.1.toList = e.factors.map (fun f ↦ closedRow f.admits f.modulus (b % f.modulus)) ∧
        store.Grows r.2 (FactorRow e) ⦄ := by
  vcgen [factorRows] invariants
  | inv1 => fun pref _ st ↦ FactorRowsInvariant e b store pref st
  all_goals first
    | exact factorRowsInvariant_nil e b store
    | exact FactorRowsInvariant.post ‹_›
    | exact FactorRowsInvariant.pre_none ‹_› ‹_› ‹_› ‹_›
    | exact FactorRowsInvariant.push_some ‹_› ‹_› ‹_› ‹_›
    | exact FactorRowsInvariant.push_none ‹_› ‹_› ‹_› ‹_›

/-! ### The rows of a product -/

/-- What building the row of a product `e` needs: what building the rows of its factors needs
(`Ratpoints.Sieve.FactorRowsPre`), a positive modulus, at least one factor, and the moduli of the
factors dividing the modulus. -/
structure ProductRowsPre (e : SieveEntry) (store : RowStore) : Prop where
  /-- What building the rows of the factors needs. -/
  factorRows : FactorRowsPre e store
  /-- The modulus is positive. -/
  pos : 0 < e.p
  /-- The product has a factor. -/
  one_le_length : 1 ≤ e.factors.length
  /-- The moduli of the factors divide the modulus. -/
  dvd : ∀ f ∈ e.factors, f.modulus ∣ e.p

theorem ProductRowsPre.factorRowsPre {e : SieveEntry} {store : RowStore}
    (h : ProductRowsPre e store) : FactorRowsPre e store :=
  h.factorRows

theorem sieveInitProduct_pre_copy {e : SieveEntry} {store : RowStore}
    (pre : ProductRowsPre e store) :
    0 < e.factors[0]!.modulus ∧ e.factors[0]!.modulus ∣ e.p ∧
      e.p * rbaPack ≤ (e.p + chunk - 1) * rbaPack := by
  have hmem : e.factors[0]! ∈ e.factors := by
    rw [getElem!_pos e.factors 0 (by lia [pre.one_le_length])]
    exact List.getElem_mem _
  refine ⟨?_, pre.dvd _ hmem, Nat.mul_le_mul_right _ (by lia [chunk_pos])⟩
  have := pre.factorRows.buildable _ hmem
  revert this
  cases e.factors[0]! with
  | prime t => exact fun h ↦ h.1
  | power pw => exact fun h ↦ h.1

theorem ProductRowsPre.pos_and_dvd {e : SieveEntry} {store : RowStore}
    (pre : ProductRowsPre e store) {i : Nat} (hi : i < e.factors.length) :
    0 < e.factors[i]!.modulus ∧ e.factors[i]!.modulus ∣ e.p := by
  have hmem : e.factors[i]! ∈ e.factors := by
    rw [getElem!_pos e.factors i hi]
    exact List.getElem_mem _
  refine ⟨?_, pre.dvd _ hmem⟩
  have := pre.factorRows.buildable _ hmem
  revert this
  cases e.factors[i]! with
  | prime t => exact fun h ↦ h.1
  | power pw => exact fun h ↦ h.1

theorem sieveInitProduct_pre_and {e : SieveEntry} {store : RowStore} {frows : Array (Array UInt64)}
    {row : Vector UInt64 ((e.p + chunk - 1) * rbaPack)}
    (pre : ProductRowsPre e store)
    (h : ∀ y < e.p * rbaPack, row[y]! = factorWord e frows 0 y) :
    (∀ i < e.factors.length, 0 < e.factors[i]!.modulus ∧ e.factors[i]!.modulus ∣ e.p) ∧
      e.p * rbaPack ≤ (e.p + chunk - 1) * rbaPack ∧
      ∀ y < e.p * rbaPack, row[y]! = factorWord e frows 0 y :=
  ⟨fun _ hi ↦ pre.pos_and_dvd hi, (sieveInitProduct_pre_copy pre).2.2, h⟩

theorem productCopies_init {e : SieveEntry} {frows : Array (Array UInt64)} {n : Nat}
    {row : Vector UInt64 n}
    (h : ∀ y < e.p * rbaPack, row[y]! = productWord e frows e.factors.length y) {y : Nat}
    (hy : y < (e.p + ([] : List Nat).length) * rbaPack) :
    row[y]! = productWord e frows e.factors.length (y % (e.p * rbaPack)) := by
  simp only [List.length_nil, Nat.add_zero] at hy
  rw [h y hy, Nat.mod_eq_of_lt hy]

/-- A copy of bit array `cur` of the row of a product after its first `m` bit arrays. -/
theorem productCopies_storeBitArray {e : SieveEntry} {frows : Array (Array UInt64)} {cur : Nat}
    {pref suff : List Nat} {row : Vector UInt64 ((e.p + chunk - 1) * rbaPack)} {store : RowStore}
    (pre : ProductRowsPre e store) (hl : ForIn.toList [0:chunk - 1] = pref ++ cur :: suff)
    (h : ∀ y < (e.p + pref.length) * rbaPack,
      row[y]! = productWord e frows e.factors.length (y % (e.p * rbaPack))) :
    ∀ y < (e.p + (pref ++ [cur]).length) * rbaPack,
      (storeBitArray row (e.p + cur) row cur)[y]! =
        productWord e frows e.factors.length (y % (e.p * rbaPack)) := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have hcl := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  intro y hy
  rw [List.length_append, List.length_singleton] at hy
  have hyl := (Nat.div_lt_iff_lt_mul rbaPack_pos).mpr hy
  have hyq := Nat.div_add_mod y rbaPack
  have hκ := Nat.mod_lt y rbaPack_pos
  rw [getElem!_storeBitArray _ _ _ _ (Nat.lt_of_lt_of_le hy
    (Nat.mul_le_mul_right _ (by lia [chunk_pos])))]
  split
  · rename_i hyc
    rw [h _ (rbaPack_mul_add_lt (show cur < e.p + pref.length by lia [pre.pos]) hκ)]
    congr 1
    have hy' : y = rbaPack * cur + y % rbaPack + e.p * rbaPack := by
      rw [hyc, Nat.mul_add, Nat.mul_comm rbaPack e.p] at hyq
      lia
    generalize y % rbaPack = κ at hy' ⊢
    rw [hy', Nat.add_mod_right]
  · exact h y ((Nat.div_lt_iff_lt_mul rbaPack_pos).mp (by lia))

theorem productCopies_post {e : SieveEntry} {frows : Array (Array UInt64)}
    {row : Vector UInt64 ((e.p + chunk - 1) * rbaPack)}
    (h : ∀ y < (e.p + (ForIn.toList [0:chunk - 1]).length) * rbaPack,
      row[y]! = productWord e frows e.factors.length (y % (e.p * rbaPack)))
    {y : Nat} (hy : y < (e.p + chunk - 1) * rbaPack) :
    row[y]! = productWord e frows e.factors.length (y % (e.p * rbaPack)) :=
  h y (by
    rw [Std.Legacy.Range.length_toList, Nat.sub_zero, ← Nat.add_sub_assoc chunk_pos]
    exact hy)

/-- The row of the product built from the closed forms of the rows of its factors is the closed
form of its row, and so is what the builder stores, into the store grown by the rows of the
factors. -/
theorem sieveInitProduct_post {e : SieveEntry} {b : Nat} {store store' : RowStore}
    {frows : Array (Array UInt64)} {row : Vector UInt64 ((e.p + chunk - 1) * rbaPack)}
    (pre : ProductRowsPre e store)
    (hf : frows.toList = e.factors.map (fun f ↦ closedRow f.admits f.modulus (b % f.modulus)) ∧
      store.Grows store' (FactorRow e))
    (hrow : ∀ y < (e.p + (ForIn.toList [0:chunk - 1]).length) * rbaPack,
      row[y]! = productWord e frows e.factors.length (y % (e.p * rbaPack))) :
    (row, store'.publish e.ref b row.toArray).1.toArray = closedRow e.admits e.p b ∧
      ∃ s, store.Grows s (FactorRow e) ∧
        (row, store'.publish e.ref b row.toArray).2 =
          s.publish e.ref b (closedRow e.admits e.p b) := by
  have h := toArray_eq_closedRow_of_productWord pre.one_le_length (fun _ hi ↦ pre.pos_and_dvd hi)
    (fun i hi ↦ by rw [Array.getElem!_of_toList_eq_map hf.1 hi, getElem!_pos e.factors i hi])
    fun y hy ↦ productCopies_post hrow hy
  exact ⟨h, store', hf.2, by rw [← h]⟩

/-- The row of the residue `b` of the product `e`, of a modulus `m > 0` that the positive moduli of
its factors divide, as `_ratpoints_sieve_init_product` builds it, is the closed form of the row of
`b` of the product, and the builder stores it into the table of rows of the entry of the product,
in the store grown by the rows of the factors that it builds into their tables of rows first
(`Ratpoints.Sieve.factorRows_spec`). -/
@[spec]
theorem sieveInitProduct_spec (e : SieveEntry) (b : Nat) (store : RowStore) :
    ⦃ ProductRowsPre e store ⦄
    sieveInitProduct e b store
    ⦃ fun r ↦ r.1.toArray = closedRow e.admits e.p b ∧ ∃ s, store.Grows s (FactorRow e) ∧
        r.2 = s.publish e.ref b (closedRow e.admits e.p b) ⦄ := by
  vcgen [sieveInitProduct] invariants
  | inv1 => fun done _ row ↦ ∀ y < (e.p + done.length) * rbaPack,
      row[y]! = productWord e frows e.factors.length (y % (e.p * rbaPack))
  all_goals first
    | exact ProductRowsPre.factorRowsPre ‹_›
    | exact sieveInitProduct_pre_copy ‹_›
    | exact sieveInitProduct_pre_and ‹_› ‹_›
    | exact productCopies_init ‹_› ‹_›
    | exact sieveInitProduct_post ‹_› ‹_› ‹_›
    | exact productCopies_storeBitArray ‹_› ‹_› ‹_›

/-! ### The rows of the entries of a run -/

/-- What building the row of the residue `b` of the sieve entry `e` by its builder needs: for a
product, what building its row needs (`Ratpoints.Sieve.ProductRowsPre`); for a prime or a prime
power, its one factor `f`, whose modulus, entry and kind are those of `e`, with a builder that has
what it needs, called at a residue at which it may be. -/
def InitRowPre (e : SieveEntry) (b : Nat) (store : RowStore) : Prop :=
  (e.init = .product ∧ ProductRowsPre e store) ∨
    ∃ f, e.factors = [f] ∧ e.init = f.init ∧ e.ref = f.ref ∧ e.p = f.modulus ∧ f.Buildable ∧
      f.Builds b

theorem Factor.init_ne_product (f : Factor) : f.init ≠ .product := by
  cases f with
  | prime t => simp only [Factor.init, sieveInit]; split <;> nofun
  | power pw => nofun

/-- The row of the residue `b` of the sieve entry `e` built by its builder is the closed form of the
row of `b` of the entry, stored into the table of rows of the entry, in the store grown by the rows
of the factors of a product. -/
@[spec]
theorem SieveEntry.initRow_spec (e : SieveEntry) (b : Nat) (store : RowStore) :
    ⦃ InitRowPre e b store ⦄ e.initRow b store
    ⦃ fun r ↦ r.1 = closedRow e.admits e.p b ∧ ∃ s, store.Grows s (FactorRow e) ∧
        r.2 = s.publish e.ref b (closedRow e.admits e.p b) ⦄ := ⟨fun pre ↦ by
  rcases pre with ⟨hinit, hpre⟩ | ⟨f, hfs, hinit, href, hp, hbd, hbs⟩
  · have h := Std.WP.Id.of_run_eq_wp rfl _ ((sieveInitProduct_spec e b store).le_wp hpre)
    simp only [SieveEntry.initRow, hinit, ↓reduceIte]
    exact h
  · have h := Std.WP.Id.of_run_eq_wp rfl _
      ((initFactorRow_spec f e.ref b store).le_wp ⟨hbd, hbs⟩)
    have he : e.admits = f.admits := SieveEntry.admits_eq_of_factors_eq hfs hp
    have hf0 : e.factors[0]! = f := by rw [hfs]; rfl
    simp only [SieveEntry.initRow, hinit, f.init_ne_product, ↓reduceIte, hf0]
    rw [he, hp]
    exact ⟨h.1, store, RowStore.Grows.refl _ _, h.2⟩⟩

/-- The row of the residue `b` of the sieve entry `e` from the table of rows of its entry, read
there when it is present, a closed form, or built by the builder of the entry: the closed form of
the row of `b` of the entry, and the store as it was or grown by the rows of the factors of a
product with the row stored into the table of rows of the entry. -/
@[spec]
theorem SieveEntry.fetchRow_spec (e : SieveEntry) (b : Nat) (store : RowStore) :
    ⦃ (∀ row, store.row? e.ref b = some row → row = closedRow e.admits e.p b) ∧
        (store.row? e.ref b = none → InitRowPre e b store) ⦄ e.fetchRow b store
    ⦃ fun r ↦ r.1 = closedRow e.admits e.p b ∧ (r.2 = store ∨ ∃ s, store.Grows s (FactorRow e) ∧
        r.2 = s.publish e.ref b (closedRow e.admits e.p b)) ⦄ := ⟨fun pre ↦ by
  change _ ∧ _
  rw [SieveEntry.fetchRow]
  cases hr : store.row? e.ref b with
  | some row => exact ⟨pre.1 row hr, .inl rfl⟩
  | none =>
    have h := Std.WP.Id.of_run_eq_wp rfl _ ((e.initRow_spec b store).le_wp (pre.2 hr))
    exact ⟨h.1, .inr h.2⟩⟩

end Sieve

end Ratpoints

end

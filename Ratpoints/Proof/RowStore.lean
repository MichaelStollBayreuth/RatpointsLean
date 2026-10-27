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
(`Ratpoints.Sieve.closedRow`), and no row is replaced.

The invariant of the store of a run: its rows are those of a function `R` of the reference and the
residue (`Ratpoints.Sieve.RowStore.Holds`), and the table of rows of every prime factor of the sieve
entries has its row of `0` (`Ratpoints.Sieve.StoreHolds`), at which the builders of a prime are
wrong; the entries fit `R` at their positions when their references and the kinds of their builders
are those that `Ratpoints.makeModulus` sets and the closed forms of the rows of the entries and
their factors are the rows of their references (`Ratpoints.Sieve.SieveEntry.RowsFit`), and the store
fits the entries when it holds rows that they fit (`Ratpoints.Sieve.RowStore.Fits`). Every row
fetched keeps the invariant (`Ratpoints.Sieve.StoreHolds.of_fetchRow`), and the sieve specs that
`Ratpoints.Sieve.setRows` makes and `Ratpoints.Sieve.buildRows` completes have the closed forms of
the rows of their entries (`Ratpoints.Sieve.buildRows_setRows_map_spec`), so that below the set-up
of a denominator nothing reads the store; the store still holds the rows for every list of entries
that contains those whose rows are built. The tables of rows made by the loop of the tables and with
the sieve entries (`Ratpoints.Sieve.primeRows`, `Ratpoints.Sieve.SieveEntry.addTables`) keep the
invariant (`Ratpoints.Sieve.RowStore.Holds.addTables`) and the rows of `0` of the primes
(`Ratpoints.Sieve.RowStore.PrimeZeroRows.row?_addTables_ne_none`). For a run, `R` is the function of
the closed forms of the rows of the table of each prime and the tables of each prime power as
`Ratpoints.Sieve.examinePrime` and `Ratpoints.Sieve.examinePower` compute them, and of the entries
of the products at their positions (`Ratpoints.Sieve.runRows`), which every sieve entry made by
`Ratpoints.makeModulus` fits (`Ratpoints.Sieve.SieveEntry.rowsFit_runRows`), and which the store
that the loop over the moduli of `Ratpoints.sievingInfo` makes holds
(`Ratpoints.Sieve.RowStore.MadeFor`).

## Main definitions

* `Ratpoints.Sieve.RowStore.Grows`: a store grown from another by rows satisfying a predicate.
* `Ratpoints.Sieve.Factor.Buildable`, `Ratpoints.Sieve.Factor.Builds`: what the builder of the
  rows of a factor needs of its tables, and the residues at which it is called.
* `Ratpoints.Sieve.FactorRow`, `Ratpoints.Sieve.FactorRowsPre`, `Ratpoints.Sieve.ProductRowsPre`,
  `Ratpoints.Sieve.InitRowPre`: the rows that building the rows of the factors of a product adds,
  and what building the rows of the factors, of a product and of an entry needs.
* `Ratpoints.Sieve.RowStore.Holds`, `Ratpoints.Sieve.StoreHolds`,
  `Ratpoints.Sieve.RowStore.PrimeZeroRows`: the rows of a store are those of a function of the
  reference and the residue, the invariant of the store of a run, and the rows of `0` of the tables
  of rows of the primes.
* `Ratpoints.Sieve.SieveEntry.RefFits`, `Ratpoints.Sieve.SieveEntry.RowsFit`: the reference and the
  kind of the builder of a sieve entry at its position, and what building its rows needs of it.
* `Ratpoints.Sieve.BuildRowsPre`, `Ratpoints.Sieve.BuildRowsInvariant`: what the loop of
  `Ratpoints.Sieve.buildRows` needs, and its invariant.
* `Ratpoints.Sieve.runRows`, `Ratpoints.Sieve.RowStore.MadeFor`: the rows of the references of a
  run, and the store as the loop of the tables and the tables of rows of the first entries of a run
  make it.
* `Ratpoints.Sieve.RowStore.Fits`: the store fits the sieve entries, holding rows that they fit at
  their positions, as the store of a run fits the entries of its first two stages before and after
  each denominator.

## Main statements

* `Ratpoints.Sieve.RowStore.getD_publish`, `Ratpoints.Sieve.RowStore.size_getD_publish`: the table
  of an entry after a row is stored, and its size.
* `Ratpoints.Sieve.RowStore.row?_publish`: the rows of the store after a row is stored.
* `Ratpoints.Sieve.initFactorRow_spec`, `Ratpoints.Sieve.factorRows_spec`,
  `Ratpoints.Sieve.sieveInitProduct_spec`, `Ratpoints.Sieve.SieveEntry.initRow_spec`,
  `Ratpoints.Sieve.SieveEntry.fetchRow_spec`: the rows built through the tables of rows are closed
  forms.
* `Ratpoints.Sieve.StoreHolds.fetchRow_pre`, `Ratpoints.Sieve.StoreHolds.of_fetchRow`: a row of an
  entry that fits can be fetched, and the store still holds after it.
* `Ratpoints.Sieve.buildRows_spec`, `Ratpoints.Sieve.buildRows_setRows_map_spec`: the sieve specs
  of a denominator have the closed forms of the rows of their entries, and the store still holds the
  rows for every list of entries that contains them.
* `Ratpoints.Sieve.RowStore.Holds.addTables`, `Ratpoints.Sieve.RowStore.PrimeZeroRows.addTables`:
  the tables of rows of a sieve entry keep the invariant of the store.
* `Ratpoints.Sieve.SieveEntry.rowsFit_runRows`: a sieve entry as `Ratpoints.makeModulus` makes it
  fits the rows of the references of the run.
* `Ratpoints.Sieve.RowStore.madeFor_nil`, `Ratpoints.Sieve.RowStore.MadeFor.addTables`,
  `Ratpoints.Sieve.RowStore.MadeFor.foldl_addTables`, `Ratpoints.Sieve.RowStore.MadeFor.storeHolds`:
  the store of the loop over the moduli of `Ratpoints.sievingInfo` holds the rows of the references
  of the run.
* `Ratpoints.Sieve.StoreHolds.of_factors`, `Ratpoints.Sieve.SieveEntry.RowsFit.of_eq`,
  `Ratpoints.Sieve.rowsFit_take`, `Ratpoints.Sieve.RowStore.Fits.take`,
  `Ratpoints.Sieve.RowStore.Fits.map_dinv`: the invariant and the fit carry over to the first
  entries, those of the first two stages, and to the entries with the inverses of the strides.
* `Ratpoints.Sieve.RowStore.Fits.buildRows_setRows`: the sieve specs of a denominator have the
  closed forms of the rows of their entries, and the store after them still fits the entries.
* `Ratpoints.Sieve.StoreHolds.buildRows_setRows_take`: a store that holds the rows for all the
  entries of a run still holds them after the rows of the first entries are built.

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
structure RowStore.Grows (s s' : RowStore) (P : EntryRef → Nat → Array UInt64 → Prop) : Prop where
  /-- The tables of rows keep their sizes. -/
  size_eq : ∀ ref, (s'.getD ref #[]).size = (s.getD ref #[]).size
  /-- The rows are kept. -/
  row?_of_row? : ∀ ref r row, s.row? ref r = some row → s'.row? ref r = some row
  /-- The other rows satisfy `P`. -/
  row?_or : ∀ ref r row, s'.row? ref r = some row → s.row? ref r = some row ∨ P ref r row

theorem RowStore.Grows.refl (s : RowStore) (P : EntryRef → Nat → Array UInt64 → Prop) :
    s.Grows s P :=
  ⟨fun _ ↦ rfl, fun _ _ _ h ↦ h, fun _ _ _ h ↦ .inl h⟩

theorem RowStore.Grows.trans {s1 s2 s3 : RowStore} {P : EntryRef → Nat → Array UInt64 → Prop}
    (h1 : s1.Grows s2 P) (h2 : s2.Grows s3 P) : s1.Grows s3 P := by
  refine ⟨fun ref ↦ by rw [h2.size_eq, h1.size_eq],
    fun ref r row h ↦ h2.row?_of_row? _ _ _ (h1.row?_of_row? _ _ _ h), fun ref r row h ↦ ?_⟩
  rcases h2.row?_or _ _ _ h with h | h
  · exact h1.row?_or _ _ _ h
  · exact .inr h

/-- A row stored at a place where the store has no row. -/
theorem RowStore.grows_publish {s : RowStore} {P : EntryRef → Nat → Array UInt64 → Prop}
    {ref : EntryRef} {r : Nat} {row : Array UInt64} (h : s.row? ref r = none) (hP : P ref r row) :
    s.Grows (s.publish ref r row) P := by
  refine ⟨fun ref' ↦ RowStore.size_getD_publish .., fun ref' r' row' h' ↦ ?_,
    fun ref' r' row' h' ↦ ?_⟩
  · rwa [RowStore.row?_publish, ite_eq_right fun ⟨h1, h2, _⟩ ↦ by subst h1 h2; simp [h] at h']
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

theorem Factor.Buildable.modulus_pos {f : Factor} (h : f.Buildable) : 0 < f.modulus := by
  cases f <;> exact h.1

@[simp]
theorem Factor.init_prime (t : Entry) : (Factor.prime t).init = sieveInit t.p := rfl

@[simp]
theorem Factor.init_power (pw : Power) : (Factor.power pw).init = .power := rfl

theorem sieveInit_of_lt {p : Nat} (h : p < 64) : sieveInit p = .sieve1 := by
  simp [sieveInit, h]

theorem sieveInit_of_not_lt {p : Nat} (h : ¬p < 64) : sieveInit p = .sieve2 := by
  simp [sieveInit, h]

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
    · rw [Factor.init_prime, sieveInit_of_lt hp]
      vcgen [initFactorRow]
      all_goals first
        | exact initFactorRow_pre_sieve1 hp ‹_›
        | exact ‹_›
    · rw [Factor.init_prime, sieveInit_of_not_lt hp]
      vcgen [initFactorRow]
      all_goals first
        | exact initFactorRow_pre_sieve2 hp ‹_›
        | exact ‹_›
  | power pw =>
    rw [Factor.init_power]
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
  rcases hs.row?_or _ _ _ h with h' | ⟨f', hf', href, rfl⟩
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
  rw [Array.toList_push, h.1, List.map_append, List.map_singleton, pre.eq_closedRow h.2 hf hr]

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
  refine ⟨pre.buildable f hf, pre.builds f hf _ (Nat.mod_lt _ (pre.buildable f hf).modulus_pos) ?_⟩
  cases hs : store.row? f.ref (b % f.modulus) with
  | none => rfl
  | some row => rw [h.2.row?_of_row? _ _ _ hs] at hr; cases hr

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

theorem ProductRowsPre.pos_and_dvd {e : SieveEntry} {store : RowStore}
    (pre : ProductRowsPre e store) {i : Nat} (hi : i < e.factors.length) :
    0 < e.factors[i]!.modulus ∧ e.factors[i]!.modulus ∣ e.p := by
  have hmem : e.factors[i]! ∈ e.factors := by
    rw [getElem!_pos e.factors i hi]
    exact List.getElem_mem _
  exact ⟨(pre.factorRows.buildable _ hmem).modulus_pos, pre.dvd _ hmem⟩

theorem sieveInitProduct_pre_copy {e : SieveEntry} {store : RowStore}
    (pre : ProductRowsPre e store) :
    0 < e.factors[0]!.modulus ∧ e.factors[0]!.modulus ∣ e.p ∧
      e.p * rbaPack ≤ (e.p + chunk - 1) * rbaPack :=
  ⟨(pre.pos_and_dvd pre.one_le_length).1, (pre.pos_and_dvd pre.one_le_length).2,
    Nat.mul_le_mul_right _ (by lia [chunk_pos])⟩

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
    rw [h _ (Nat.mul_add_lt_mul_of_lt_of_lt' (show cur < e.p + pref.length by lia [pre.pos]) hκ)]
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
  h y (by rwa [Std.Legacy.Range.length_toList, Nat.sub_zero, ← Nat.add_sub_assoc chunk_pos])

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
    | exact ProductRowsPre.factorRows ‹_›
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
  | prime t => rw [Factor.init_prime, sieveInit]; split <;> nofun
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
  · have h := Std.WP.Id.of_run_eq_wp rfl _ ((initFactorRow_spec f e.ref b store).le_wp ⟨hbd, hbs⟩)
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

/-! ### The tables of rows of a run -/

/-- The rows of the store `s` are those of `R`, a row for each reference and residue: every row
present at the residue `r` of the table of rows of `ref` is `R ref r`. -/
def RowStore.Holds (R : EntryRef → Nat → Array UInt64) (s : RowStore) : Prop :=
  ∀ ref r row, s.row? ref r = some row → row = R ref r

theorem RowStore.Holds.publish {R : EntryRef → Nat → Array UInt64} {s : RowStore} (h : s.Holds R)
    {ref : EntryRef} {r : Nat} {row : Array UInt64} (hrow : row = R ref r) :
    (s.publish ref r row).Holds R := by
  intro ref' r' row' h'
  rw [RowStore.row?_publish] at h'
  split at h'
  · rename_i hc
    obtain ⟨rfl, rfl, -⟩ := hc
    rw [← Option.some.inj h', hrow]
  · exact h _ _ _ h'

theorem RowStore.Holds.of_grows {R : EntryRef → Nat → Array UInt64} {s s' : RowStore}
    {P : EntryRef → Nat → Array UInt64 → Prop} (h : s.Holds R) (hs : s.Grows s' P)
    (hP : ∀ ref r row, P ref r row → row = R ref r) : s'.Holds R := fun _ _ _ h' ↦
  (hs.row?_or _ _ _ h').elim (h _ _ _) (hP _ _ _)

theorem RowStore.Grows.row?_ne_none {s s' : RowStore} {P : EntryRef → Nat → Array UInt64 → Prop}
    (hs : s.Grows s' P) {ref : EntryRef} {r : Nat} (h : s.row? ref r ≠ none) :
    s'.row? ref r ≠ none := by
  obtain ⟨row, hrow⟩ := Option.ne_none_iff_exists'.mp h
  rw [hs.row?_of_row? _ _ _ hrow]
  exact Option.some_ne_none row

theorem RowStore.row?_publish_ne_none {s : RowStore} {ref ref' : EntryRef} {r r' : Nat}
    {row : Array UInt64} (h : s.row? ref' r' ≠ none) :
    (s.publish ref r row).row? ref' r' ≠ none := by
  rw [RowStore.row?_publish]
  split
  · exact Option.some_ne_none row
  · exact h

/-- The store `s` of a run holds the rows `R` of the references (`Ratpoints.Sieve.RowStore.Holds`),
and the table of rows of every prime factor of the sieve entries `es` has its row of `0`
(`Ratpoints.Sieve.primeRows`), at which the builders of a prime are wrong: what building the rows
of the entries needs of the store, beside what it needs of each entry
(`Ratpoints.Sieve.SieveEntry.RowsFit`). -/
structure StoreHolds (R : EntryRef → Nat → Array UInt64) (es : List SieveEntry) (s : RowStore) :
    Prop where
  /-- The rows of the store are those of `R`. -/
  holds : s.Holds R
  /-- The table of rows of every prime factor has its row of `0`. -/
  zero : ∀ e ∈ es, ∀ t : Entry, .prime t ∈ e.factors → s.row? (.prime t.p) 0 ≠ none

/-- The sieve entry `e` at the position `n` of the moduli holds the reference to its table of rows
and the kind of its builder as `Ratpoints.makeModulus` sets them
(`Ratpoints.Sieve.SieveEntry.refInit`): for one factor, the modulus, the reference and the kind of
the factor; otherwise the product's own table of rows, by its position, and the builder of the rows
of a product. -/
def SieveEntry.RefFits (e : SieveEntry) (n : Nat) : Prop :=
  match e.factors with
  | [f] => e.p = f.modulus ∧ e.ref = f.ref ∧ e.init = f.init
  | _ => e.ref = .product n ∧ e.init = .product

/-- A sieve entry whose reference and kind of builder are those that
`Ratpoints.Sieve.SieveEntry.refInit` gives at the position `n`, as `Ratpoints.makeModulus` sets
them, and whose modulus is that of its factor when it has one, fits them. -/
theorem SieveEntry.refFits_of_refInit_eq {e : SieveEntry} {n : Nat}
    (h : (e.ref, e.init) = SieveEntry.refInit n e.factors)
    (hp : ∀ f, e.factors = [f] → e.p = f.modulus) : e.RefFits n := by
  rw [SieveEntry.RefFits]
  split
  · rename_i f hf
    rw [hf, SieveEntry.refInit, Prod.mk.injEq] at h
    exact ⟨hp f hf, h⟩
  · rename_i hf
    rw [SieveEntry.refInit] at h
    · exact Prod.mk.inj h
    · exact hf

/-- What building the rows of the sieve entry `e` at the position `n` of the moduli needs of it, for
the rows `R` of the references (`Ratpoints.Sieve.RowStore.Holds`): its reference and kind
(`Ratpoints.Sieve.SieveEntry.RefFits`), a positive modulus, at least one factor, the moduli of the
factors dividing the modulus, builders of the factors that have what they need
(`Ratpoints.Sieve.Factor.Buildable`), and the rows of its reference and of the references of its
factors the closed forms of their rows (`Ratpoints.Sieve.closedRow`). -/
structure SieveEntry.RowsFit (e : SieveEntry) (R : EntryRef → Nat → Array UInt64) (n : Nat) :
    Prop where
  /-- The reference and the kind of the builder are those that `Ratpoints.makeModulus` sets. -/
  refFits : e.RefFits n
  /-- The modulus is positive. -/
  pos : 0 < e.p
  /-- The entry has a factor. -/
  factors_ne_nil : e.factors ≠ []
  /-- The moduli of the factors divide the modulus. -/
  dvd : ∀ f ∈ e.factors, f.modulus ∣ e.p
  /-- The builders of the factors have what they need. -/
  buildable : ∀ f ∈ e.factors, f.Buildable
  /-- The rows of the reference are the closed forms of the rows of the entry. -/
  ref_rows : R e.ref = closedRow e.admits e.p
  /-- The rows of the reference of each factor are the closed forms of the rows of the factor. -/
  factor_rows : ∀ f ∈ e.factors, R f.ref = closedRow f.admits f.modulus

/-- A row absent below the modulus of a factor of an entry is one at which the builder of the factor
may be called (`Ratpoints.Sieve.Factor.Builds`): for a prime, its row of `0` is present. -/
theorem StoreHolds.builds {R : EntryRef → Nat → Array UInt64} {es : List SieveEntry}
    {s : RowStore} (hs : StoreHolds R es s) {e : SieveEntry} (he : e ∈ es) {f : Factor}
    (hf : f ∈ e.factors) {r : Nat} (hr : r < f.modulus) (h : s.row? f.ref r = none) :
    f.Builds r := by
  cases f with
  | prime t =>
    refine ⟨Nat.pos_of_ne_zero fun h0 ↦ hs.zero e he t hf ?_, hr⟩
    rwa [← h0]
  | power pw => exact hr

/-- What building the rows of the factors of an entry needs (`Ratpoints.Sieve.FactorRowsPre`). -/
theorem SieveEntry.RowsFit.factorRowsPre {e : SieveEntry} {R : EntryRef → Nat → Array UInt64}
    {n : Nat} (hfit : e.RowsFit R n) {es : List SieveEntry} {s : RowStore}
    (hs : StoreHolds R es s) (he : e ∈ es) : FactorRowsPre e s :=
  ⟨hfit.buildable, fun f hf r _ h ↦ (hs.holds _ _ _ h).trans (congrFun (hfit.factor_rows f hf) r),
    fun _ hf _ hr h ↦ hs.builds he hf hr h, fun f hf f' hf' href ↦ by
      rw [← hfit.factor_rows f hf, ← hfit.factor_rows f' hf', href]⟩

/-- What building the row of the residue `b < p` of an entry needs (`Ratpoints.Sieve.InitRowPre`),
when the row is absent: for a prime, `b ≠ 0`, since its row of `0` is present. -/
theorem StoreHolds.initRowPre {R : EntryRef → Nat → Array UInt64} {es : List SieveEntry}
    {s : RowStore} (hs : StoreHolds R es s) {e : SieveEntry} (he : e ∈ es) {n : Nat}
    (hfit : e.RowsFit R n) {b : Nat} (hb : b < e.p) (hr : s.row? e.ref b = none) :
    InitRowPre e b s := by
  have hrf := hfit.refFits
  rw [SieveEntry.RefFits] at hrf
  match hfs : e.factors, hrf with
  | [f], ⟨hp, href, hinit⟩ =>
    have hf : f ∈ e.factors := by simp [hfs]
    exact .inr ⟨f, hfs, hinit, href, hp, hfit.buildable f hf,
      hs.builds he hf (hp ▸ hb) (href ▸ hr)⟩
  | [], _ => exact absurd hfs hfit.factors_ne_nil
  | _ :: _ :: _, ⟨_, hinit⟩ =>
    exact .inl ⟨hinit, hfit.factorRowsPre hs he, hfit.pos, by simp [hfs], hfit.dvd⟩

/-- The precondition of `Ratpoints.Sieve.SieveEntry.fetchRow_spec` for the residue `b < p` of an
entry. -/
theorem StoreHolds.fetchRow_pre {R : EntryRef → Nat → Array UInt64} {es : List SieveEntry}
    {s : RowStore} (hs : StoreHolds R es s) {e : SieveEntry} (he : e ∈ es) {n : Nat}
    (hfit : e.RowsFit R n) {b : Nat} (hb : b < e.p) :
    (∀ row, s.row? e.ref b = some row → row = closedRow e.admits e.p b) ∧
      (s.row? e.ref b = none → InitRowPre e b s) :=
  ⟨fun _ h ↦ (hs.holds _ _ _ h).trans (congrFun hfit.ref_rows b), hs.initRowPre he hfit hb⟩

/-- The store after a row of an entry is fetched (`Ratpoints.Sieve.SieveEntry.fetchRow_spec`) still
holds. -/
theorem StoreHolds.of_fetchRow {R : EntryRef → Nat → Array UInt64} {es : List SieveEntry}
    {s s' : RowStore} (hs : StoreHolds R es s) {e : SieveEntry} {n : Nat} (hfit : e.RowsFit R n)
    {b : Nat} (h : s' = s ∨ ∃ s'', s.Grows s'' (FactorRow e) ∧
      s' = s''.publish e.ref b (closedRow e.admits e.p b)) :
    StoreHolds R es s' := by
  rcases h with rfl | ⟨s'', hg, rfl⟩
  · exact hs
  · refine ⟨(hs.holds.of_grows hg fun _ r _ ⟨f, hf, href, hrow⟩ ↦ ?_).publish
      (congrFun hfit.ref_rows b).symm, fun e' he' t ht ↦
        RowStore.row?_publish_ne_none (hg.row?_ne_none (hs.zero e' he' t ht))⟩
    rw [hrow, ← href, hfit.factor_rows f hf]

/-! ### The making of the tables of rows -/

theorem RowStore.row?_insertIfNew (s : RowStore) (k ref : EntryRef)
    (v : Array (Option (Array UInt64))) (r : Nat) :
    RowStore.row? (s.insertIfNew k v) ref r =
      if k = ref ∧ k ∉ s then v.getD r none else s.row? ref r := by
  simp only [RowStore.row?, Std.HashMap.getD_insertIfNew, beq_iff_eq]
  split <;> rfl

theorem RowStore.row?_eq_none_of_not_mem {s : RowStore} {ref : EntryRef} (h : ref ∉ s) (r : Nat) :
    s.row? ref r = none := by
  simp [RowStore.row?, Std.HashMap.getD_eq_fallback h]

/-- A table of rows made where none was keeps the rows of the store. -/
theorem RowStore.row?_insertIfNew_of_ne_none {s : RowStore} {ref : EntryRef} {r : Nat}
    (h : s.row? ref r ≠ none) (k : EntryRef) (v : Array (Option (Array UInt64))) :
    RowStore.row? (s.insertIfNew k v) ref r = s.row? ref r := by
  rw [RowStore.row?_insertIfNew]
  split
  · rename_i hk
    obtain ⟨rfl, hk⟩ := hk
    exact absurd (RowStore.row?_eq_none_of_not_mem hk r) h
  · rfl

theorem RowStore.Holds.insertIfNew {R : EntryRef → Nat → Array UInt64} {s : RowStore}
    (h : s.Holds R) {k : EntryRef} {v : Array (Option (Array UInt64))}
    (hv : ∀ r row, v.getD r none = some row → row = R k r) :
    RowStore.Holds R (s.insertIfNew k v) := by
  intro ref r row h'
  rw [RowStore.row?_insertIfNew] at h'
  split at h'
  · rename_i hk
    obtain ⟨rfl, -⟩ := hk
    exact hv r row h'
  · exact h _ _ _ h'

/-- Every table of rows of a prime in the store has its row of `0`, as the loop of the tables and
the sieve entries make the tables of rows of the primes (`Ratpoints.Sieve.primeRows`). -/
def RowStore.PrimeZeroRows (s : RowStore) : Prop :=
  ∀ p, EntryRef.prime p ∈ s → s.row? (.prime p) 0 ≠ none

theorem RowStore.PrimeZeroRows.insertIfNew {s : RowStore} (h : s.PrimeZeroRows) {k : EntryRef}
    {v : Array (Option (Array UInt64))} (hv : ∀ p, k = .prime p → v.getD 0 none ≠ none) :
    RowStore.PrimeZeroRows (s.insertIfNew k v) := by
  intro p hp
  rw [RowStore.row?_insertIfNew]
  split
  · rename_i hk
    exact hv p hk.1
  · rename_i hk
    rw [Std.HashMap.mem_insertIfNew] at hp
    rcases hp with hp | hp
    · obtain rfl := beq_iff_eq.mp hp
      exact h p (Classical.byContradiction fun hm ↦ hk ⟨rfl, hm⟩)
    · exact h p hp

theorem getD_primeRows (p r : Nat) :
    (primeRows p).getD r none = if r = 0 then some (sieves0 p) else none := by
  cases r with
  | zero => simp [primeRows, Array.getD_eq_getD_getElem?, Array.getElem?_append_left]
  | succ r =>
    simp only [primeRows, Array.getD_eq_getD_getElem?, Nat.add_one_ne_zero, ↓reduceIte]
    rw [Array.getElem?_append_right (by simp), Array.getElem?_replicate]
    split <;> rfl

theorem RowStore.holds_empty (R : EntryRef → Nat → Array UInt64) : RowStore.Holds R {} :=
  fun _ _ _ h ↦ by simp [RowStore.row?] at h

theorem RowStore.primeZeroRows_empty : RowStore.PrimeZeroRows {} :=
  fun _ h ↦ absurd h (Std.HashMap.not_mem_empty)

/-- The table of rows of the prime `p` with its row of `0` (`Ratpoints.Sieve.primeRows`) keeps the
rows of the store those of `R` when the row of `0` of `p` is that of `R`. -/
theorem RowStore.Holds.insertIfNew_primeRows {R : EntryRef → Nat → Array UInt64} {s : RowStore}
    (h : s.Holds R) {p : Nat} (hR : R (.prime p) 0 = sieves0 p) :
    RowStore.Holds R (s.insertIfNew (.prime p) (primeRows p)) :=
  h.insertIfNew fun r row hr ↦ by
    rw [getD_primeRows] at hr
    split at hr
    · rename_i hr0
      subst hr0
      rw [← Option.some.inj hr, hR]
    · cases hr

theorem RowStore.PrimeZeroRows.insertIfNew_primeRows {s : RowStore} (h : s.PrimeZeroRows)
    (p : Nat) : RowStore.PrimeZeroRows (s.insertIfNew (.prime p) (primeRows p)) :=
  h.insertIfNew fun _ _ ↦ by
    rw [getD_primeRows]
    exact Option.some_ne_none _

theorem RowStore.Holds.insertIfNew_replicate_none {R : EntryRef → Nat → Array UInt64}
    {s : RowStore} (h : s.Holds R) (k : EntryRef) (n : Nat) :
    RowStore.Holds R (s.insertIfNew k (.replicate n none)) :=
  h.insertIfNew fun r row hr ↦ by
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate] at hr
    split at hr <;> cases hr

theorem RowStore.PrimeZeroRows.insertIfNew_newRows {s : RowStore} (h : s.PrimeZeroRows) :
    (f : Factor) → RowStore.PrimeZeroRows (s.insertIfNew f.ref f.newRows)
  | .prime t => h.insertIfNew_primeRows t.p
  | .power _ => h.insertIfNew fun _ ↦ nofun

theorem RowStore.Holds.insertIfNew_newRows {R : EntryRef → Nat → Array UInt64} {s : RowStore}
    (h : s.Holds R) {f : Factor} (hR : ∀ t : Entry, f = .prime t → R (.prime t.p) 0 = sieves0 t.p) :
    RowStore.Holds R (s.insertIfNew f.ref f.newRows) :=
  match f, hR with
  | .prime t, hR => h.insertIfNew_primeRows (hR t rfl)
  | .power _, _ => h.insertIfNew_replicate_none _ _

private theorem mem_foldl_insertIfNew (fs : List Factor) (s : RowStore) {f : Factor} (hf : f ∈ fs) :
    f.ref ∈ fs.foldl (fun s f ↦ s.insertIfNew f.ref f.newRows) s := by
  induction fs generalizing s with
  | nil => cases hf
  | cons g fs ih =>
    rcases List.mem_cons.mp hf with rfl | hf
    · exact List.foldlRecOn (motive := (f.ref ∈ ·)) fs _ Std.HashMap.mem_insertIfNew_self
        fun _ h _ _ ↦ Std.HashMap.mem_insertIfNew.mpr (.inr h)
    · exact ih _ hf

/-- A sieve entry whose builder is that of a product has the product's own table of rows. -/
theorem SieveEntry.RefFits.ref_eq_of_init_eq {e : SieveEntry} {n : Nat} (h : e.RefFits n)
    (hinit : e.init = .product) : e.ref = .product n := by
  rw [SieveEntry.RefFits] at h
  split at h
  · exact absurd (h.2.2 ▸ hinit) (Factor.init_ne_product _)
  · exact h.1

/-- The store with the tables of rows of a sieve entry holds the rows `R` of the references when the
store does and the rows of `0` of the primes of the entry are those of `R`. -/
theorem RowStore.Holds.addTables {R : EntryRef → Nat → Array UInt64} {s : RowStore} (h : s.Holds R)
    {e : SieveEntry} (hR : ∀ t : Entry, .prime t ∈ e.factors → R (.prime t.p) 0 = sieves0 t.p) :
    (e.addTables s).Holds R := by
  have hf : RowStore.Holds R (e.factors.foldl (fun s f ↦ s.insertIfNew f.ref f.newRows) s) :=
    List.foldlRecOn (motive := RowStore.Holds R) _ _ h fun _ hs _ hf ↦
      hs.insertIfNew_newRows fun t ht ↦ hR t (ht ▸ hf)
  simp only [SieveEntry.addTables]
  split
  · exact hf.insertIfNew_replicate_none _ _
  · exact hf

theorem RowStore.PrimeZeroRows.addTables {s : RowStore} (h : s.PrimeZeroRows) {e : SieveEntry}
    {n : Nat} (he : e.RefFits n) : (e.addTables s).PrimeZeroRows := by
  have hf : RowStore.PrimeZeroRows (e.factors.foldl (fun s f ↦ s.insertIfNew f.ref f.newRows) s) :=
    List.foldlRecOn (motive := RowStore.PrimeZeroRows) _ _ h fun _ hs f _ ↦ hs.insertIfNew_newRows f
  simp only [SieveEntry.addTables]
  split
  · rename_i hinit
    exact hf.insertIfNew fun p hp ↦ absurd ((he.ref_eq_of_init_eq hinit).symm.trans hp) nofun
  · exact hf

theorem SieveEntry.row?_addTables_of_ne_none {s : RowStore} {ref : EntryRef} {r : Nat}
    (h : s.row? ref r ≠ none) (e : SieveEntry) : (e.addTables s).row? ref r = s.row? ref r := by
  have hf : RowStore.row? (e.factors.foldl (fun s f ↦ s.insertIfNew f.ref f.newRows) s) ref r =
      s.row? ref r :=
    List.foldlRecOn (motive := fun s' : RowStore ↦ s'.row? ref r = s.row? ref r) _ _ rfl
      fun _ hs _ _ ↦ (RowStore.row?_insertIfNew_of_ne_none (hs ▸ h) _ _).trans hs
  simp only [SieveEntry.addTables]
  split
  · exact (RowStore.row?_insertIfNew_of_ne_none (hf ▸ h) _ _).trans hf
  · exact hf

theorem SieveEntry.mem_addTables (e : SieveEntry) (s : RowStore) {f : Factor}
    (hf : f ∈ e.factors) : f.ref ∈ e.addTables s := by
  have hm := mem_foldl_insertIfNew e.factors s hf
  simp only [SieveEntry.addTables]
  split
  · exact Std.HashMap.mem_insertIfNew.mpr (.inr hm)
  · exact hm

/-- The table of rows of a prime factor of a sieve entry has its row of `0` once the tables of rows
of the entry are made, when every table of rows of a prime has it. -/
theorem RowStore.PrimeZeroRows.row?_addTables_ne_none {s : RowStore} (h : s.PrimeZeroRows)
    {e : SieveEntry} {n : Nat} (he : e.RefFits n) {t : Entry} (ht : .prime t ∈ e.factors) :
    (e.addTables s).row? (.prime t.p) 0 ≠ none :=
  h.addTables he t.p (e.mem_addTables s ht)

/-! ### The rows of the sieve specs of a denominator -/

private theorem SieveSpec.eq_with_row_stop {s : SieveSpec} {row : Array UInt64} {stop : Nat}
    (hr : s.row = row) (hs : s.stop = stop) : s = { s with row, stop } := by
  subst hr hs
  rfl

/-- What building the rows of the sieve specs `specs` of the entries `es` at the residues `bp`
(`Ratpoints.Sieve.buildRows`) needs: the store holds the rows `R` for a list `L` of entries that
contains `es`, the entries fit them at their positions, the residues are below the moduli, and each
spec has the end `p` and its row, or none yet, all rows when `missing` says none is missing. -/
structure BuildRowsPre (R : EntryRef → Nat → Array UInt64) (L : List SieveEntry) (missing : Bool)
    (es : List SieveEntry) (bp : List Nat) (specs : List SieveSpec) (store : RowStore) : Prop where
  /-- The store holds the rows `R` for the entries `L`. -/
  holds : StoreHolds R L store
  /-- The entries are among `L`. -/
  subset : es ⊆ L
  /-- The entries fit the rows `R` at their positions. -/
  fit : ∀ n (h : n < es.length), es[n].RowsFit R n
  /-- The residues are below the moduli. -/
  lt : ∀ n (h : n < es.length), bp[n]! < es[n].p
  /-- A spec for each entry. -/
  length_eq : specs.length = es.length
  /-- The specs have the end `p`. -/
  stop_eq : ∀ n < specs.length, specs[n]!.stop = es[n]!.p
  /-- The specs have their rows or none yet. -/
  row_eq : ∀ n < specs.length,
    specs[n]!.row = #[] ∨ specs[n]!.row = closedRow es[n]!.admits es[n]!.p bp[n]!
  /-- The specs have their rows when none is missing. -/
  row_eq_of_missing : missing = false → ∀ n < specs.length,
    specs[n]!.row = closedRow es[n]!.admits es[n]!.p bp[n]!

/-- The invariant of the loop of `Ratpoints.Sieve.buildRows` after the specs below `k`, on the specs
and the store: the store holds the rows `R` for the entries `L`, and each spec has its row and the
end `p`, or for `k ≤ i` none yet. -/
def BuildRowsInvariant (R : EntryRef → Nat → Array UInt64) (L es : List SieveEntry) (bp : List Nat)
    (specs : List SieveSpec) (k : Nat) (st : List SieveSpec × RowStore) : Prop :=
  StoreHolds R L st.2 ∧ st.1.length = specs.length ∧ ∀ i < specs.length,
    st.1[i]! = { specs[i]! with row := closedRow es[i]!.admits es[i]!.p bp[i]!, stop := es[i]!.p } ∨
      k ≤ i ∧ st.1[i]! = { specs[i]! with row := #[], stop := es[i]!.p }

theorem BuildRowsPre.buildRowsInvariant {R : EntryRef → Nat → Array UInt64} {L : List SieveEntry}
    {missing : Bool} {es : List SieveEntry} {bp : List Nat} {specs : List SieveSpec}
    {store : RowStore} (pre : BuildRowsPre R L missing es bp specs store) :
    BuildRowsInvariant R L es bp specs ([] : List Nat).length (specs, store) := by
  refine ⟨pre.holds, rfl, fun i hi ↦ ?_⟩
  rcases pre.row_eq i hi with h | h
  · exact .inr ⟨Nat.zero_le _, SieveSpec.eq_with_row_stop h (pre.stop_eq i hi)⟩
  · exact .inl (SieveSpec.eq_with_row_stop h (pre.stop_eq i hi))

theorem BuildRowsPre.post_of_missing_false {R : EntryRef → Nat → Array UInt64}
    {L : List SieveEntry} {missing : Bool} {es : List SieveEntry} {bp : List Nat}
    {specs : List SieveSpec} {store : RowStore} (pre : BuildRowsPre R L missing es bp specs store)
    (h : ¬missing = true) :
    specs = specs.mapIdx (fun i s ↦
        { s with row := closedRow es[i]!.admits es[i]!.p bp[i]!, stop := es[i]!.p }) ∧
      StoreHolds R L (specs, store).2 := by
  refine ⟨List.ext_getElem (List.length_mapIdx ..).symm fun i h1 _ ↦ ?_, pre.holds⟩
  rw [List.getElem_mapIdx, ← getElem!_pos specs i h1]
  exact SieveSpec.eq_with_row_stop (pre.row_eq_of_missing (by simpa using h) i h1)
    (pre.stop_eq i h1)

theorem BuildRowsInvariant.post {R : EntryRef → Nat → Array UInt64} {L es : List SieveEntry}
    {bp : List Nat} {specs specs' : List SieveSpec} {st : RowStore}
    (h : BuildRowsInvariant R L es bp specs (ForIn.toList [:specs.length]).length (specs', st)) :
    specs' = specs.mapIdx (fun i s ↦
        { s with row := closedRow es[i]!.admits es[i]!.p bp[i]!, stop := es[i]!.p }) ∧
      StoreHolds R L ((specs', st).1, (specs', st).2).2 := by
  obtain ⟨hs, hl, h⟩ := h
  rw [Std.Legacy.Range.length_toList, Nat.sub_zero] at h
  refine ⟨List.ext_getElem (by simp [hl]) fun i h1 h2 ↦ ?_, hs⟩
  have hi : i < specs.length := by rwa [hl] at h1
  rcases h i hi with h' | ⟨h', -⟩
  · rw [← getElem!_pos specs' i h1, h', List.getElem_mapIdx, getElem!_pos specs i hi]
  · exact absurd hi (Nat.not_lt.mpr h')

theorem BuildRowsInvariant.fetchRow_pre {R : EntryRef → Nat → Array UInt64} {L : List SieveEntry}
    {missing : Bool} {es : List SieveEntry} {bp : List Nat} {specs : List SieveSpec}
    {store : RowStore} (pre : BuildRowsPre R L missing es bp specs store) {pref suff : List Nat}
    {cur : Nat} (hl : ForIn.toList [:specs.length] = pref ++ cur :: suff)
    {st : List SieveSpec × RowStore} (h : BuildRowsInvariant R L es bp specs pref.length st) :
    (∀ row, st.2.row? es[cur]!.ref bp[cur]! = some row →
        row = closedRow es[cur]!.admits es[cur]!.p bp[cur]!) ∧
      (st.2.row? es[cur]!.ref bp[cur]! = none → InitRowPre es[cur]! bp[cur]! st.2) := by
  have hce : cur < es.length := pre.length_eq ▸ Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  rw [getElem!_pos es cur hce]
  exact h.1.fetchRow_pre (pre.subset (List.getElem_mem hce)) (pre.fit cur hce) (pre.lt cur hce)

theorem BuildRowsInvariant.set {R : EntryRef → Nat → Array UInt64} {L : List SieveEntry}
    {missing : Bool} {es : List SieveEntry} {bp : List Nat} {specs : List SieveSpec}
    {store : RowStore} (pre : BuildRowsPre R L missing es bp specs store) {pref suff : List Nat}
    {cur : Nat} (hl : ForIn.toList [:specs.length] = pref ++ cur :: suff)
    {st : List SieveSpec × RowStore} (h : BuildRowsInvariant R L es bp specs pref.length st)
    {row : Array UInt64} {st' : RowStore}
    (hr : (row, st').1 = closedRow es[cur]!.admits es[cur]!.p bp[cur]! ∧ ((row, st').2 = st.2 ∨
      ∃ s, st.2.Grows s (FactorRow es[cur]!) ∧
        (row, st').2 =
          s.publish es[cur]!.ref bp[cur]! (closedRow es[cur]!.admits es[cur]!.p bp[cur]!))) :
    BuildRowsInvariant R L es bp specs (pref ++ [cur]).length
      (st.1.set cur { st.1[cur]! with row, stop := es[cur]!.p }, st') := by
  have hc := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  have hce : cur < es.length := pre.length_eq ▸ hc
  obtain ⟨hs, hlen, h⟩ := h
  refine ⟨hs.of_fetchRow (getElem!_pos es cur hce ▸ pre.fit cur hce) hr.2, by simp [hlen],
    fun i hi ↦ ?_⟩
  rw [List.getElem!_set (hlen ▸ hi)]
  rw [Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl] at h
  rw [List.length_append, List.length_singleton,
    Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl]
  split
  · rename_i hci
    subst hci
    refine .inl ?_
    rcases h cur hc with h' | ⟨-, h'⟩ <;> rw [h'] <;> simp only at hr ⊢ <;> rw [hr.1]
  · rename_i hci
    rcases h i hi with h' | ⟨h', h''⟩
    · exact .inl h'
    · exact .inr ⟨by lia, h''⟩

theorem BuildRowsInvariant.skip {R : EntryRef → Nat → Array UInt64} {L es : List SieveEntry}
    {bp : List Nat} {specs : List SieveSpec} {pref suff : List Nat} {cur : Nat}
    (hl : ForIn.toList [:specs.length] = pref ++ cur :: suff) {st : List SieveSpec × RowStore}
    (h : BuildRowsInvariant R L es bp specs pref.length st) (hne : ¬st.1[cur]!.row.isEmpty = true) :
    BuildRowsInvariant R L es bp specs (pref ++ [cur]).length (st.1, st.2) := by
  have hc := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  obtain ⟨hs, hlen, h⟩ := h
  refine ⟨hs, hlen, fun i hi ↦ ?_⟩
  rw [Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl] at h
  rw [List.length_append, List.length_singleton,
    Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl]
  rcases h i hi with h' | ⟨h', h''⟩
  · exact .inl h'
  · refine .inr ⟨Nat.lt_of_le_of_ne h' fun hci ↦ hne ?_, h''⟩
    subst hci
    rw [h'']
    rfl

attribute [local irreducible] BuildRowsInvariant in
/-- The rows that `Ratpoints.Sieve.buildRows` builds into the sieve specs of the entries `es` at the
residues `bp`, read from the tables of rows or built into them, are the closed forms of the rows of
the entries (`Ratpoints.Sieve.closedRow`), each with the end `p`, and the store still holds the rows
`R` for every list `L` of entries that contains `es` and for which it held them. -/
@[spec]
theorem buildRows_spec (R : EntryRef → Nat → Array UInt64) (L : List SieveEntry) (missing : Bool)
    (es : List SieveEntry) (bp : List Nat) (specs : List SieveSpec) (store : RowStore) :
    ⦃ BuildRowsPre R L missing es bp specs store ⦄ buildRows missing es bp specs store
    ⦃ fun r ↦ r.1 = specs.mapIdx (fun i s ↦
        { s with row := closedRow es[i]!.admits es[i]!.p bp[i]!, stop := es[i]!.p }) ∧
      StoreHolds R L r.2 ⦄ := by
  vcgen [buildRows] invariants
  | inv1 => fun pref _ st ↦ BuildRowsInvariant R L es bp specs pref.length st
  all_goals first
    | exact BuildRowsPre.buildRowsInvariant ‹_›
    | exact BuildRowsPre.post_of_missing_false ‹_› ‹_›
    | exact BuildRowsInvariant.post ‹_›
    | exact BuildRowsInvariant.fetchRow_pre ‹_› ‹_› ‹_›
    | exact BuildRowsInvariant.set ‹_› ‹_› ‹_› ‹_›
    | exact BuildRowsInvariant.skip ‹_› ‹_› ‹_›

theorem length_setRows (store : RowStore) {es : List SieveEntry} {bp : List Nat} (cl : NumClass)
    (offsets : Array Nat) (hbp : bp.length = es.length) :
    (setRows store es bp cl offsets).1.length = es.length := by
  simp [setRows, hbp]

theorem getElem!_setRows (store : RowStore) {es : List SieveEntry} {bp : List Nat} (cl : NumClass)
    (offsets : Array Nat) (hbp : bp.length = es.length) {n : Nat} (hn : n < es.length) :
    (setRows store es bp cl offsets).1[n]! =
      ⟨es[n].p, offsets[cl.offset.getD 0 + n]!, (store.row? es[n].ref bp[n]!).getD #[], 0,
        es[n].p⟩ := by
  rw [getElem!_pos _ n (by rwa [length_setRows store cl offsets hbp])]
  simp [setRows, getElem!_pos bp n (hbp ▸ hn)]

theorem row?_ne_none_of_setRows {store : RowStore} {es : List SieveEntry} {bp : List Nat}
    {cl : NumClass} {offsets : Array Nat} (hbp : bp.length = es.length)
    (h : (setRows store es bp cl offsets).2 = false) {n : Nat} (hn : n < es.length) :
    store.row? es[n].ref bp[n]! ≠ none := by
  simp only [setRows, List.any_eq_false] at h
  have hm := h _ (List.getElem_mem (by simp [hbp, hn] : n < ((es.zip bp).map
    fun x ↦ store.row? x.1.ref x.2).length))
  simpa [getElem!_pos bp n (hbp ▸ hn)] using hm

/-- What building the rows of the sieve specs that `Ratpoints.Sieve.setRows` makes needs
(`Ratpoints.Sieve.BuildRowsPre`), for a store that holds the rows `R` for a list of entries that
contains `es`, entries that fit them at their positions and residues below the moduli: a row present
in the store is the closed form of the row of its entry. -/
theorem buildRowsPre_setRows {R : EntryRef → Nat → Array UInt64} {L : List SieveEntry}
    {store : RowStore} {es : List SieveEntry} {bp : List Nat} (cl : NumClass) (offsets : Array Nat)
    (hs : StoreHolds R L store) (hsub : es ⊆ L) (hfit : ∀ n (h : n < es.length), es[n].RowsFit R n)
    (hbp : bp.length = es.length) (hlt : ∀ n (h : n < es.length), bp[n]! < es[n].p) :
    BuildRowsPre R L (setRows store es bp cl offsets).2 es bp (setRows store es bp cl offsets).1
      store := by
  have hl := length_setRows store cl offsets hbp
  have hrow (n : Nat) (hn : n < es.length) (row : Array UInt64)
      (h : store.row? es[n].ref bp[n]! = some row) : row = closedRow es[n].admits es[n].p bp[n]! :=
    (hs.holds _ _ _ h).trans (congrFun (hfit n hn).ref_rows _)
  refine ⟨hs, hsub, hfit, hlt, hl, fun n hn ↦ ?_, fun n hn ↦ ?_, fun hm n hn ↦ ?_⟩ <;>
    rw [hl] at hn <;> rw [getElem!_setRows store cl offsets hbp hn, getElem!_pos es n hn]
  · cases h : store.row? es[n].ref bp[n]! with
    | none => exact .inl rfl
    | some row => exact .inr (hrow n hn row h)
  · obtain ⟨row, h⟩ := Option.ne_none_iff_exists'.mp (row?_ne_none_of_setRows hbp hm hn)
    rw [h]
    exact hrow n hn row h

theorem mapIdx_setRows (store : RowStore) {es : List SieveEntry} {bp : List Nat} (cl : NumClass)
    (offsets : Array Nat) (hbp : bp.length = es.length) :
    (setRows store es bp cl offsets).1.mapIdx (fun i s ↦
        { s with row := closedRow es[i]!.admits es[i]!.p bp[i]!, stop := es[i]!.p }) =
      (es.zip bp).mapIdx fun n eb ↦
        ⟨eb.1.p, offsets[cl.offset.getD 0 + n]!, closedRow eb.1.admits eb.1.p eb.2, 0, eb.1.p⟩ := by
  have hl := length_setRows store cl offsets hbp
  refine List.ext_getElem (by simp [hl, hbp]) fun n h1 _ ↦ ?_
  have hn : n < es.length := by simpa [hl] using h1
  rw [List.getElem_mapIdx, List.getElem_mapIdx, ← getElem!_pos _ n (by simpa [hl] using h1),
    getElem!_setRows store cl offsets hbp hn, List.getElem_zip]
  simp [getElem!_pos es n hn, getElem!_pos bp n (hbp ▸ hn)]

/-- The sieve specs of the first two stages that `Ratpoints.Sieve.setRows` makes and
`Ratpoints.Sieve.buildRows` completes for the residues `g e < p` of the entries, as the run computes
them (`Ratpoints.Sieve.fillBpList_eq_map`), have the closed forms of the rows of their entries at
their residues (`Ratpoints.Sieve.closedRow`), the offsets of the class, the start `0` and the end
`p`, and the store still holds the rows `R` for the entries `L`, for a store that holds them,
entries among `L` that fit them at their positions and residues below the moduli. -/
theorem buildRows_setRows_map_spec (R : EntryRef → Nat → Array UInt64) (L : List SieveEntry)
    (store : RowStore) (es : List SieveEntry) (g : SieveEntry → Nat) (cl : NumClass)
    (offsets : Array Nat) :
    ⦃ StoreHolds R L store ∧ es ⊆ L ∧ (∀ n (h : n < es.length), es[n].RowsFit R n) ∧
        ∀ e ∈ es, g e < e.p ⦄
    buildRows (setRows store es (es.map g) cl offsets).2 es (es.map g)
      (setRows store es (es.map g) cl offsets).1 store
    ⦃ fun r ↦ r.1 = es.mapIdx (fun n e ↦
          ⟨e.p, offsets[cl.offset.getD 0 + n]!, closedRow e.admits e.p (g e), 0, e.p⟩) ∧
        StoreHolds R L r.2 ⦄ := ⟨fun ⟨hs, hsub, hfit, hg⟩ ↦ by
  have h := Std.WP.Id.of_run_eq_wp rfl _ ((buildRows_spec R L _ es (es.map g) _ store).le_wp
    (buildRowsPre_setRows cl offsets hs hsub hfit (List.length_map _) fun n hn ↦ by
      rw [getElem!_pos _ n (by simpa using hn), List.getElem_map]
      exact hg _ (List.getElem_mem hn)))
  refine ⟨(h.1.trans (mapIdx_setRows store cl offsets (List.length_map _))).trans
    (List.ext_getElem (by simp) fun n h1 h2 ↦ ?_), h.2⟩
  simp⟩

/-! ### The rows of the references of a run -/

@[simp]
theorem p_run_examinePower (c : List Int) (d p e : Nat) (u pinf : Bool) :
    (Id.run (examinePower c d p e u pinf)).p = p :=
  rfl

@[simp]
theorem m_run_examinePower (c : List Int) (d p e : Nat) (u pinf : Bool) :
    (Id.run (examinePower c d p e u pinf)).m = p ^ e :=
  rfl

/-- The rows of a prime power do not depend on the flag `pinf`, which only the density reads. -/
theorem admits_run_examinePower (c : List Int) (d p e : Nat) (u pinf : Bool) :
    (Id.run (examinePower c d p e u pinf)).admits =
      (Id.run (examinePower c d p e u false)).admits :=
  rfl

/-- The rows of the references of a run for the polynomial of degree `d` with the coefficient list
`c` and the sieve entries `es` of the moduli in their order: for a prime `p`, the closed forms of
the rows of its table (`Ratpoints.Sieve.examinePrime`); for a prime power `p ^ e`, those of its
tables (`Ratpoints.Sieve.examinePower`); for a product, those of the entry at its position. -/
def runRows (c : List Int) (d : Nat) (es : List SieveEntry) : EntryRef → Nat → Array UInt64
  | .prime p => closedRow (examinePrime c d p).admits p
  | .power p e => closedRow (Id.run (examinePower c d p e false false)).admits (p ^ e)
  | .product n => closedRow es[n]!.admits es[n]!.p

theorem runRows_prime_zero (c : List Int) (d : Nat) (es : List SieveEntry) {p : Nat} (hp : 0 < p) :
    runRows c d es (.prime p) 0 = sieves0 p :=
  (sieves0_eq_closedRow (examinePrime c d p) hp).symm

/-- The rows of the reference of a factor of a run whose table or tables are those that
`Ratpoints.Sieve.examinePrime` and `Ratpoints.Sieve.examinePower` compute are the closed forms of
the rows of the factor. -/
theorem runRows_ref (c : List Int) (d : Nat) (es : List SieveEntry) {f : Factor}
    (hprime : ∀ t : Entry, f = .prime t → t = examinePrime c d t.p)
    (hpower : ∀ pw : Power, f = .power pw →
      ∃ pinf, pw = Id.run (examinePower c d pw.p pw.e false pinf)) :
    runRows c d es f.ref = closedRow f.admits f.modulus := by
  cases f with
  | prime t =>
    change closedRow (examinePrime c d t.p).admits t.p = closedRow t.admits t.p
    rw [← hprime t rfl]
  | power pw =>
    obtain ⟨pinf, h⟩ := hpower pw rfl
    have hm : pw.m = pw.p ^ pw.e := (congrArg Power.m h).trans (m_run_examinePower ..)
    change closedRow (Id.run (examinePower c d pw.p pw.e false false)).admits (pw.p ^ pw.e) =
      closedRow pw.admits pw.m
    rw [← admits_run_examinePower c d pw.p pw.e false pinf, ← h, hm]

/-- A sieve entry at the position `n` of the entries `es` of a run, with the reference and the kind
that `Ratpoints.makeModulus` sets, a positive modulus, at least one factor, the moduli of the
factors dividing the modulus, builders that have what they need and the tables that
`Ratpoints.Sieve.examinePrime` and `Ratpoints.Sieve.examinePower` compute, fits the rows of the
references of the run (`Ratpoints.Sieve.runRows`). -/
theorem SieveEntry.rowsFit_runRows {c : List Int} {d : Nat} {es : List SieveEntry} {n : Nat}
    {e : SieveEntry} (hn : es[n]? = some e) (hrf : e.RefFits n) (hpos : 0 < e.p)
    (hne : e.factors ≠ []) (hdvd : ∀ f ∈ e.factors, f.modulus ∣ e.p)
    (hb : ∀ f ∈ e.factors, f.Buildable)
    (hprime : ∀ t : Entry, .prime t ∈ e.factors → t = examinePrime c d t.p)
    (hpower : ∀ pw : Power, .power pw ∈ e.factors →
      ∃ pinf, pw = Id.run (examinePower c d pw.p pw.e false pinf)) :
    e.RowsFit (runRows c d es) n := by
  have hf (f : Factor) (hf : f ∈ e.factors) : runRows c d es f.ref = closedRow f.admits f.modulus :=
    runRows_ref c d es (fun t ht ↦ hprime t (ht ▸ hf)) fun pw hpw ↦ hpower pw (hpw ▸ hf)
  refine ⟨hrf, hpos, hne, hdvd, hb, ?_, hf⟩
  have hrf' := hrf
  rw [SieveEntry.RefFits] at hrf'
  match hfs : e.factors, hrf' with
  | [f], ⟨hp, href, _⟩ =>
    rw [href, hf f (by simp [hfs]), SieveEntry.admits_eq_of_factors_eq hfs hp, hp]
  | [], _ => exact absurd hfs hne
  | _ :: _ :: _, ⟨href, _⟩ =>
    rw [href, runRows, List.getElem!_eq_getElem?_getD, hn, Option.getD_some]

/-! ### The store of a run and its entries -/

/-- The store `s` as the loop of the tables and the tables of the sieve entries `es` of the first
moduli of a run make it (`Ratpoints.choiceEnd`): it holds the rows of the references of every run
whose entries begin with `es` (`Ratpoints.Sieve.runRows`), every table of rows of a prime in it has
its row of `0`, and so has the table of rows of every prime factor of `es`. -/
structure RowStore.MadeFor (s : RowStore) (c : List Int) (d : Nat) (es : List SieveEntry) :
    Prop where
  /-- The store holds the rows of the references of every run whose entries begin with `es`. -/
  holds : ∀ es', es <+: es' → s.Holds (runRows c d es')
  /-- Every table of rows of a prime has its row of `0`. -/
  primeZeroRows : s.PrimeZeroRows
  /-- The table of rows of every prime factor of `es` has its row of `0`. -/
  zero : ∀ e ∈ es, ∀ t : Entry, .prime t ∈ e.factors → s.row? (.prime t.p) 0 ≠ none

/-- The store of the loop of the tables, which holds the rows of `0` of the primes and no others
(`Ratpoints.Sieve.PrimeStore`), is made for no entries. -/
theorem RowStore.madeFor_nil {s : RowStore} (c : List Int) (d : Nat)
    (h : ∀ R : EntryRef → Nat → Array UInt64, (∀ p, 0 < p → R (.prime p) 0 = sieves0 p) →
      s.Holds R) (hz : s.PrimeZeroRows) : s.MadeFor c d [] :=
  ⟨fun es' _ ↦ h _ fun _ hp ↦ runRows_prime_zero c d es' hp, hz,
    fun _ he ↦ absurd he List.not_mem_nil⟩

/-- The tables of rows of the next sieve entry `e`, with the reference and the kind of builder of
its position and positive primes: the store is made for the entries with `e`. -/
theorem RowStore.MadeFor.addTables {s : RowStore} {c : List Int} {d : Nat} {es : List SieveEntry}
    (h : s.MadeFor c d es) {e : SieveEntry} {n : Nat} (he : e.RefFits n)
    (hp : ∀ t : Entry, .prime t ∈ e.factors → 0 < t.p) : (e.addTables s).MadeFor c d (es ++ [e]) :=
  ⟨fun es' h' ↦ (h.holds es' ((List.prefix_append es [e]).trans h')).addTables fun t ht ↦
      runRows_prime_zero c d es' (hp t ht), h.primeZeroRows.addTables he,
    fun e' he' t ht ↦ by
      rcases List.mem_append.mp he' with he' | he'
      · rw [e.row?_addTables_of_ne_none (h.zero e' he' t ht)]
        exact h.zero e' he' t ht
      · obtain rfl := List.mem_singleton.mp he'
        exact h.primeZeroRows.row?_addTables_ne_none he ht⟩

/-- The tables of rows of the sieve entries `l` added in turn, each with the reference and the kind
of builder of its position after `es` and positive primes: the store is made for `es ++ l`. -/
theorem RowStore.MadeFor.foldl_addTables {s : RowStore} {c : List Int} {d : Nat}
    {es : List SieveEntry} (h : s.MadeFor c d es) (l : List SieveEntry)
    (hfit : ∀ n (hn : n < l.length), l[n].RefFits (es.length + n))
    (hp : ∀ e ∈ l, ∀ t : Entry, .prime t ∈ e.factors → 0 < t.p) :
    (l.foldl (fun s e ↦ e.addTables s) s).MadeFor c d (es ++ l) := by
  induction l generalizing s es with
  | nil => simpa using h
  | cons e l ih =>
    have h' := h.addTables (hfit 0 (by simp)) (hp e List.mem_cons_self)
    have hfit' (n : Nat) (hn : n < l.length) : l[n].RefFits ((es ++ [e]).length + n) := by
      have := hfit (n + 1) (by simpa using hn)
      rw [List.getElem_cons_succ] at this
      rwa [List.length_append, List.length_singleton, Nat.add_assoc, Nat.add_comm 1]
    simpa using ih h' hfit' fun e' he' ↦ hp e' (List.mem_cons_of_mem _ he')

/-- The store made for the entries `es` of a run holds the rows of the references of the run for
them (`Ratpoints.Sieve.StoreHolds`). -/
theorem RowStore.MadeFor.storeHolds {s : RowStore} {c : List Int} {d : Nat} {es : List SieveEntry}
    (h : s.MadeFor c d es) : StoreHolds (runRows c d es) es s :=
  ⟨h.holds es (List.prefix_refl es), h.zero⟩

/-- The invariant of the store holds for entries with the factors of those for which it holds, such
as the entries with the inverses of the strides (`Ratpoints.Sieve.classOffsets`) and those of the
first two stages. -/
theorem StoreHolds.of_factors {R : EntryRef → Nat → Array UInt64} {es es' : List SieveEntry}
    {s : RowStore} (h : StoreHolds R es s) (h' : ∀ e' ∈ es', ∃ e ∈ es, e'.factors = e.factors) :
    StoreHolds R es' s :=
  ⟨h.holds, fun e' he' t ht ↦
    have ⟨e, he, hf⟩ := h' e' he'
    h.zero e he t (hf ▸ ht)⟩

/-- An entry with the modulus, the factors, the reference and the kind of builder of an entry that
fits the rows `R` at its position fits them too, such as the entry with the inverses of the strides
(`Ratpoints.Sieve.classOffsets`). -/
theorem SieveEntry.RowsFit.of_eq {e e' : SieveEntry} {R : EntryRef → Nat → Array UInt64} {n : Nat}
    (h : e.RowsFit R n) (hp : e'.p = e.p) (hf : e'.factors = e.factors) (hr : e'.ref = e.ref)
    (hi : e'.init = e.init) : e'.RowsFit R n := by
  have ha : e'.admits = e.admits := funext fun _ ↦ funext fun _ ↦ by
    simp only [SieveEntry.admits, hp, hf]
  refine ⟨?_, hp ▸ h.pos, hf ▸ h.factors_ne_nil, hf ▸ hp ▸ h.dvd, hf ▸ h.buildable,
    by rw [hr, ha, hp]; exact h.ref_rows, hf ▸ h.factor_rows⟩
  rw [SieveEntry.RefFits, hf, hp, hr, hi]
  exact h.refFits

/-! ### A store that fits the sieve entries -/

/-- The store `s` fits the sieve entries `es`: it holds rows `R` of the references
(`Ratpoints.Sieve.StoreHolds`) that every entry fits at its position
(`Ratpoints.Sieve.SieveEntry.RowsFit`), which is what building the rows of the entries needs. -/
def RowStore.Fits (s : RowStore) (es : List SieveEntry) : Prop :=
  ∃ R : EntryRef → Nat → Array UInt64,
    StoreHolds R es s ∧ ∀ n (h : n < es.length), es[n].RowsFit R n

theorem pos_of_rowsFit_of_mem {R : EntryRef → Nat → Array UInt64} {L : List SieveEntry}
    (hfit : ∀ n (h : n < L.length), L[n].RowsFit R n) {e : SieveEntry} (he : e ∈ L) : 0 < e.p :=
  have ⟨n, hn, he⟩ := List.getElem_of_mem he
  he ▸ (hfit n hn).pos

theorem rowsFit_take {R : EntryRef → Nat → Array UInt64} {L : List SieveEntry}
    (hfit : ∀ n (h : n < L.length), L[n].RowsFit R n) (k : Nat) :
    ∀ n (h : n < (L.take k).length), (L.take k)[n].RowsFit R n := fun n hn ↦ by
  rw [List.getElem_take]
  exact hfit n (Nat.lt_of_lt_of_le hn (List.length_take_le' k L))

theorem RowStore.Fits.pos {s : RowStore} {es : List SieveEntry} (h : s.Fits es) :
    ∀ e ∈ es, 0 < e.p := fun _ he ↦
  have ⟨_, _, hfit⟩ := h
  pos_of_rowsFit_of_mem hfit he

/-- The store of the sieve entries of a run fits their first `k`, those of the first two stages. -/
theorem RowStore.Fits.take {s : RowStore} {es : List SieveEntry} (h : s.Fits es) (k : Nat) :
    s.Fits (es.take k) :=
  have ⟨R, hs, hfit⟩ := h
  ⟨R, hs.of_factors fun e he ↦ ⟨e, List.mem_of_mem_take he, rfl⟩, rowsFit_take hfit k⟩

/-- The store of the sieve entries of a run fits them with the inverses of the strides that
`Ratpoints.Sieve.classOffsets` sets. -/
theorem RowStore.Fits.map_dinv {s : RowStore} {es : List SieveEntry} (h : s.Fits es)
    (dinv : SieveEntry → Array Nat) : s.Fits (es.map fun e ↦ { e with dinv := dinv e }) :=
  have ⟨R, hs, hfit⟩ := h
  ⟨R, hs.of_factors fun _ he ↦ have ⟨e, he, h⟩ := List.mem_map.mp he; ⟨e, he, h ▸ rfl⟩,
    fun n hn ↦ by
      rw [List.getElem_map]
      exact (hfit n (by simpa using hn)).of_eq rfl rfl rfl rfl⟩

/-- The sieve specs of a denominator that `Ratpoints.Sieve.setRows` makes and
`Ratpoints.Sieve.buildRows` completes for the residues `g e < p` of the entries, as the run
computes them (`Ratpoints.Sieve.buildRows_setRows_map_spec`): the closed forms of the rows of the
entries at their residues, with the offsets of the class, the start `0` and the end `p`; and the
store after them still fits the entries. -/
theorem RowStore.Fits.buildRows_setRows {store store' : RowStore} {es : List SieveEntry}
    (h : store.Fits es) {g : SieveEntry → Nat} (hg : ∀ e ∈ es, g e < e.p) {cl : NumClass}
    {offsets : Array Nat} {specs : List SieveSpec}
    (hr : (specs, store') = Id.run (buildRows (setRows store es (es.map g) cl offsets).2 es
      (es.map g) (setRows store es (es.map g) cl offsets).1 store)) :
    specs = es.mapIdx (fun n e ↦
        ⟨e.p, offsets[cl.offset.getD 0 + n]!, closedRow e.admits e.p (g e), 0, e.p⟩) ∧
      store'.Fits es :=
  have ⟨R, hs, hfit⟩ := h
  have h' := Std.WP.Id.of_run_eq_wp hr.symm _
    ((buildRows_setRows_map_spec R es store es g cl offsets).le_wp
      ⟨hs, List.Subset.refl _, hfit, hg⟩)
  ⟨h'.1, R, h'.2, hfit⟩

/-- The sieve specs of the first `k` sieve entries of `L` that `Ratpoints.Sieve.setRows` makes and
`Ratpoints.Sieve.buildRows` completes for their residues `g e < p`, from a store that holds the
rows `R` for all of `L` (`Ratpoints.Sieve.StoreHolds`), whose entries fit them: the store after
them still holds the rows for all of `L` (`Ratpoints.Sieve.buildRows_setRows_map_spec`). -/
theorem StoreHolds.buildRows_setRows_take {R : EntryRef → Nat → Array UInt64}
    {L : List SieveEntry} {store store' : RowStore} (h : StoreHolds R L store)
    (hfit : ∀ n (h : n < L.length), L[n].RowsFit R n) {k : Nat} {g : SieveEntry → Nat}
    (hg : ∀ e ∈ L.take k, g e < e.p) {cl : NumClass} {offsets : Array Nat}
    {specs : List SieveSpec}
    (hr : (specs, store') = Id.run (buildRows (setRows store (L.take k) ((L.take k).map g) cl
      offsets).2 (L.take k) ((L.take k).map g) (setRows store (L.take k) ((L.take k).map g) cl
        offsets).1 store)) :
    StoreHolds R L store' :=
  (Std.WP.Id.of_run_eq_wp hr.symm _ ((buildRows_setRows_map_spec R L store (L.take k) g cl
    offsets).le_wp ⟨h, List.take_subset k L, rowsFit_take hfit k, hg⟩)).2

end Sieve

end Ratpoints

end

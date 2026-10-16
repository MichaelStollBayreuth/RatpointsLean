/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.Rows

import Std.Data.HashMap.Lemmas

/-!
# The rows built into the tables of a run

The tables of rows of a run (`Ratpoints.Sieve.RowStore`) as the builders change them: the table of
an entry after a row is stored into it (`Ratpoints.Sieve.RowStore.getD_publish`), which keeps the
size of every table (`Ratpoints.Sieve.RowStore.size_getD_publish`), and the rows of the store after
it, the row at its place and the others as they were (`Ratpoints.Sieve.RowStore.row?_publish`). The
contracts of the builders through the tables and the invariant of the store of a run come with
stage F4.

## Main statements

* `Ratpoints.Sieve.RowStore.getD_publish`, `Ratpoints.Sieve.RowStore.size_getD_publish`: the table
  of an entry after a row is stored, and its size.
* `Ratpoints.Sieve.RowStore.row?_publish`: the rows of the store after a row is stored.

## Implementation notes

The file uses Lean core and `Std` only, as the contracts of the sieve do.
-/

@[expose] public section

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

end Sieve

end Ratpoints

end

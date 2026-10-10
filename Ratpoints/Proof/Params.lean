/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.Nat.Prime.Defs
public import Ratpoints.Model.Params

import Mathlib.Tactic.NormNum.Prime

/-!
# The sieving parameters: the primes of the table and well-formedness

Every entry of `Ratpoints.primeTable` is a prime, which `norm_num` checks one entry at a time,
every parameter set that the options of the program give is well-formed, and the pieces of the
numerators have at least one bit array.

## Main statements

* `Ratpoints.prime_of_mem_primeTable`: every entry of `Ratpoints.primeTable` is a prime, so that
  the moduli of well-formed parameters are primes (`Ratpoints.Params.WF.prime_of_mem`).
* `Ratpoints.wf_sieveParams`: every parameter set that the options of the program give is
  well-formed; comparator certifies this (`comparator/Challenge.lean`), which also rules out a
  well-formedness that nothing satisfies.
* `Ratpoints.wf_defaultParams`: the parameters of a run without options are well-formed.
* `Ratpoints.Params.one_le_arraySizeAt`: for a height bound `H ≥ 1` a piece of the numerators has
  at least one bit array.
-/

@[expose] public section

namespace Ratpoints

theorem prime_of_mem_primeTable {p : ℕ} (h : p ∈ primeTable) : p.Prime := by
  rw [primeTable, List.mem_toArray] at h
  repeat' obtain rfl | h := List.mem_cons.mp h
  all_goals first | exact absurd h List.not_mem_nil | norm_num

theorem Params.WF.prime_of_mem {P : Params} (hP : P.WF) {p : ℕ} (hp : p ∈ P.moduli) : p.Prime :=
  prime_of_mem_primeTable (hP.mem_primeTable p hp)

theorem numPrimes_le_size_primeTable : numPrimes ≤ primeTable.size :=
  (List.length_filter_le _ _).trans_eq primeTable.length_toList

/-- Every parameter set that the options of the program give is well-formed; comparator certifies
this (`comparator/Challenge.lean`). -/
theorem wf_sieveParams (o : SieveOptions) : (sieveParams o).WF where
  mem_primeTable _ hm := Array.mem_toList_iff.mp (List.mem_of_mem_take hm)
  sp1_le_sp2 := by
    simp only [sieveParams]
    split_ifs <;> lia
  sp2_le_length := by
    have := numPrimes_le_size_primeTable
    simp only [sieveParams, List.length_take, Array.length_toList]
    split_ifs <;> lia

theorem wf_defaultParams : defaultParams.WF := wf_sieveParams {}

/-- The pieces of the numerators are not empty, so that the loop over the pieces of a denominator
advances; this reads off only that `Ratpoints.defaultArraySize` and `Ratpoints.maxArraySize` are
positive. -/
theorem Params.one_le_arraySizeAt (P : Params) {H : ℕ} (hH : 1 ≤ H) : 1 ≤ P.arraySizeAt H := by
  have := defaultArraySize_pos
  have := maxArraySize_pos
  rw [arraySizeAt]
  split <;> lia

/-! ### The axioms of the certified theorem -/

/--
info: 'Ratpoints.wf_sieveParams' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms wf_sieveParams

end Ratpoints

end

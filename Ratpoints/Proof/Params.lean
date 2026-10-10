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

## Main statements

* `Ratpoints.prime_of_mem_primeTable`: every entry of `Ratpoints.primeTable` is a prime.
* `Ratpoints.wf_sieveParams`: every parameter set that the options of the program give is
  well-formed; comparator certifies this (`comparator/Challenge.lean`), which also rules out a
  well-formedness that nothing satisfies.
* `Ratpoints.wf_defaultParams`: the parameters of a run without options are well-formed.
-/

@[expose] public section

namespace Ratpoints

theorem prime_of_mem_primeTable {p : ℕ} (h : p ∈ primeTable) : p.Prime := by
  rw [primeTable, List.mem_toArray] at h
  repeat' obtain rfl | h := List.mem_cons.mp h
  all_goals first | exact absurd h List.not_mem_nil | norm_num

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

/-! ### The axioms of the certified theorem -/

/--
info: 'Ratpoints.wf_sieveParams' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms wf_sieveParams

end Ratpoints

end

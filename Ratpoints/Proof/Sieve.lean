/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.Sieve
public import Std.WP

import Std.Tactic.Do

/-!
# The contracts of the sieve

The contracts of the loops of the plain sieve, as `@[spec]` theorems proved with `vcgen`, the
program logic of Lean core, with loop invariants that are named definitions.

## Main statements

* `Ratpoints.Sieve.sieveDen_spec`: entry `i` of the sieve of a denominator `b` is the survivor test
  `Ratpoints.Sieve.survives` of the numerator `i - H`.

## Implementation notes

The file uses Lean core and `Std` only, so that the `grind` calls of the proofs see only the lemmas
of core, untouched by the updates of Mathlib.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace Ratpoints

namespace Sieve

/-! ### The sieve of one denominator -/

/-- The invariant of the loop of `Ratpoints.Sieve.sieveDen` over the tables: after the tables
`pref`, the entry of each numerator `i - H` is its survivor test for them. -/
def SieveDenInvariant (H b : Nat) (pref : List Entry) (surv : Vector Bool (2 * H + 1)) : Prop :=
  ∀ i (hi : i < 2 * H + 1), surv[i] = survives pref b ((i : Int) - H)

/-- The invariant of the loop of `Ratpoints.Sieve.sieveDen` over the numerators for the table `e`,
after the tables `pref`: after the positions `done`, the entry of each numerator `i - H` is its
survivor test for `pref` followed by `e` if `i` is among them, and for `pref` otherwise. -/
def SieveDenRowInvariant (H b : Nat) (pref : List Entry) (e : Entry) (done : List Nat)
    (surv : Vector Bool (2 * H + 1)) : Prop :=
  ∀ i (hi : i < 2 * H + 1),
    surv[i] = if i ∈ done then survives (pref ++ [e]) b ((i : Int) - H)
      else survives pref b ((i : Int) - H)

@[spec]
theorem sieveDen_spec (H b : Nat) (entries : List Entry) :
    ⦃ True ⦄ sieveDen H b entries
    ⦃ fun surv ↦ ∀ i (hi : i < 2 * H + 1), surv[i] = survives entries b ((i : Int) - H) ⦄ := by
  vcgen [sieveDen] invariants
  | inv1 => fun pref _ surv ↦ SieveDenInvariant H b pref surv
  | inv2 pref e _ _ _ _ => fun done _ surv ↦ SieveDenRowInvariant H b pref e done surv
  all_goals
    try simp only [SieveDenInvariant, SieveDenRowInvariant] at *
    try intro i hi
    try simp only [Vector.getElem_set]
    grind [survives]

end Sieve

end Ratpoints

end

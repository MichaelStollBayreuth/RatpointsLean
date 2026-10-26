/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.Denominators

/-!
# The set-up of the run

The shape of the run that `Ratpoints.Sieve.runSetup` chooses from the flags of the search, and the
bounds of the search intervals that it makes, which the contract of the search reads.

## Main statements

* `Ratpoints.Sieve.fst_run_runSetup`, `Ratpoints.Sieve.snd_run_runSetup`: the shape that
  `Ratpoints.Sieve.runSetup` chooses from the flags of the search, and the bounds of the search
  intervals that it makes.
-/

@[expose] public section

namespace Ratpoints

namespace Sieve

/-- The shape that `Ratpoints.Sieve.runSetup` chooses from the flags of the search. -/
theorem fst_run_runSetup (useSquares : Bool) (us1 : Option (List Setup.DenInfo × List Nat))
    (checkDenom useJacobi : Bool) (forb : List ForbiddenEntry) (forbVal : List ForbiddenVal)
    (lcf : Int) (H bHigh : Nat) (domain : List (Double × Double)) :
    (Id.run (runSetup useSquares us1 checkDenom useJacobi forb forbVal lcf H bHigh domain)).1 =
      if useSquares then .squares else match us1 with
        | some (info, divisors) => .squares1 info divisors
        | none => if checkDenom then .words forb forbVal useJacobi
            (if useJacobi then Id.run (jacobiSetup lcf bHigh) else none) lcf else .all := by
  cases useSquares <;> rcases us1 with _ | ⟨info, divisors⟩ <;> cases checkDenom <;>
    cases useJacobi <;> rfl

/-- The bounds of the search intervals of the run that `Ratpoints.Sieve.runSetup` makes. -/
theorem snd_run_runSetup (useSquares : Bool) (us1 : Option (List Setup.DenInfo × List Nat))
    (checkDenom useJacobi : Bool) (forb : List ForbiddenEntry) (forbVal : List ForbiddenVal)
    (lcf : Int) (H bHigh : Nat) (domain : List (Double × Double)) :
    (Id.run (runSetup useSquares us1 checkDenom useJacobi forb forbVal lcf H bHigh domain)).2 =
      Id.run (exactBounds domain H.toInt64 bHigh.toInt64) := by
  cases useSquares <;> rcases us1 with _ | ⟨info, divisors⟩ <;> cases checkDenom <;>
    cases useJacobi <;> rfl

end Sieve

end Ratpoints

end

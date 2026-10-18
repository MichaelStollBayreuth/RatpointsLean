/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.Nat.Factors
public import Ratpoints.Spec.Basic

import Ratpoints.Spec.Region

/-!
# The order of the points

The list of the points that ratpoints finds, in its order, for a coefficient list `c` and a height
bound `H`. It is the order of the polynomial that ratpoints searches, which its set-up may reverse,
exchanging `x` and `z` in the binary form: the points at infinity first, then the points of each
denominator `z` in turn, in the order of the loop of the search, which visits those that its tests
let through (the others carry no point), by ascending numerator `x`, `(x, y, z)` before
`(x, -y, z)`, each point mapped back to the caller's curve after a reversal. The denominators of the
polynomial searched ascend, except when it has odd degree `d` with `|c_d| ≠ 1` (its own degree and
leading coefficient) and ratpoints factors `|c_d|` completely by trial division and finds fewer than
`maxDiv` of its squarefree divisors up to the largest denominator `B` of the search: then they are
`e k ^ 2`, divisor `e` by divisor in the order of binary counting over the primes of `c_d`, and `k`
ascending. The largest denominator is the height bound `H`, or the bound of the range of the
denominators of a search region (`Ratpoints.denominatorBound`); the other parts of a search region
(the search intervals, the lower bound of the denominators) only filter the list, and a search
region other than the whole box (`Ratpoints.IsFullBox`) forbids the reversal. The specification uses
Mathlib and nothing of the model; the comparator challenge restates its definitions verbatim.

## Main definitions

* `Ratpoints.searchedPoly`: the polynomial searched, and whether it is the reversed one.
* `Ratpoints.FactorsByTrialDivision`: whether ratpoints factors a number completely.
* `Ratpoints.binaryDivisors`: the squarefree divisors up to `H`, in the order of binary counting.
* `Ratpoints.searchDenominators`: the denominators of the search, in its order.
* `Ratpoints.pointsWithDen`: the points of one denominator, in their order.
* `Ratpoints.orderedPoints`: the list of the points, in the order of ratpoints.

## Implementation notes

The file imports `Mathlib.Data.Nat.Factors` for the prime factors of a number
(`Nat.primeFactorsList`, in increasing order with multiplicity), and `Ratpoints.Spec.Region` for the
examples with a search region; the comparator challenge imports the Mathlib modules among the public
imports of the files of the specification that it restates.
-/

@[expose] public section

namespace Ratpoints

/-- The polynomial that ratpoints searches for the coefficient list `c` of degree `d`, and whether
it is reversed, when the switch `reverse` allows a reversal (the option `-k` of the program forbids
it): for even `d`, the list `c_d, …, c₀` when `c₀ = 0` (then `c₁ ≠ 0`, or the binary form is not
squarefree and refused) or when `c_d` is a square and `c₀` is not; for odd `d`, the list
`0, c_d, …, c₁` when `|c_d| ≠ 1`, `c₀ = 0` and `|c₁| = 1`; otherwise `c` itself. The binary form
of a reversed list is that of `c` with `x` and `z` exchanged, except for even `d` with
`c₀ = c₁ = 0`, which ratpoints refuses. -/
def searchedPoly (reverse : Bool) (c : List ℤ) : List ℤ × Bool :=
  let d := degree c
  if reverse ∧ d % 2 = 0 ∧
      (c.getD 0 0 = 0 ∨ IsSquare (c.getD d 0) ∧ ¬IsSquare (c.getD 0 0)) then
    ((c.take (d + 1)).reverse, true)
  else if reverse ∧ d % 2 = 1 ∧ (c.getD d 0).natAbs ≠ 1 ∧ c.getD 0 0 = 0 ∧
      (c.getD 1 0).natAbs = 1 then
    (0 :: (c.take (d + 1)).tail.reverse, true)
  else (c, false)

/-- Whether ratpoints factors `n` completely: it divides off `2` and the odd primes up to `1021` in
turn and takes a cofactor below `p ^ 2`, for the next prime `p`, as a prime, which it is; so it
fails exactly when the part of `n` at the primes from `1021` on is at least `1021 ^ 2` and not a
power of `1021`. -/
def FactorsByTrialDivision (n : ℕ) : Prop :=
  (n.primeFactorsList.filter (1021 ≤ ·)).prod < 1021 ^ 2 ∨ ∀ p ∈ n.primeFactorsList, p ≤ 1021

instance instDecidablePredFactorsByTrialDivision : DecidablePred FactorsByTrialDivision :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- The squarefree divisors of `n` at most `H`, in the order of binary counting over the prime
factors `p₁ < p₂ < ⋯` of `n`: the products of the sublists of the primes,
`1, p₁, p₂, p₁ p₂, p₃, p₁ p₃, …`, those of them at most `H`, in this order (`List.sublists`, `p₁`
the lowest bit). -/
def binaryDivisors (n H : ℕ) : List ℕ :=
  (n.primeFactorsList.dedup.sublists.map List.prod).filter (· ≤ H)

/-- The denominators of the search of the polynomial with the coefficient list `c` of degree `d`,
up to the largest denominator `H` of the search (the height bound, or the bound of the range of the
denominators, `Ratpoints.denominatorBound`): when `d` is odd, `|c_d| ≠ 1`, ratpoints factors
`|c_d|` completely (`Ratpoints.FactorsByTrialDivision`) and it has fewer than `maxDiv` squarefree
divisors at most `H` (`Ratpoints.binaryDivisors`), the numbers `e k ^ 2 ≤ H`, divisor `e` by
divisor in that order and `k = 1, 2, …` for each; otherwise `1, …, H`. This is the order of the
loop of the search, which visits those of them that its tests let through (for `d` odd and
`|c_d| = 1` only the squares); the others carry no point. -/
def searchDenominators (maxDiv : ℕ) (c : List ℤ) (H : ℕ) : List ℕ :=
  let d := degree c
  let n := (c.getD d 0).natAbs
  let divs := binaryDivisors n H
  if d % 2 = 1 ∧ n ≠ 1 ∧ FactorsByTrialDivision n ∧ divs.length < maxDiv then
    (divs.flatMap fun e ↦ (List.range' 1 H).map fun k ↦ e * k ^ 2).filter (· ≤ H)
  else List.range' 1 H

/-- The points of height at most `H` with the denominator `z`: for the numerators `x = -H, …, H`
in turn, with `y = ⌊√F(x, z)⌋` (`Int.sqrt`, which is `0` when `F(x, z) < 0`, where the filter by
`Ratpoints.IsPoint` keeps nothing), the points among `(x, y, z)` and `(x, -y, z)`, in this order
(one point when `y = 0`). The denominator `0` gives the points at infinity, whose numerator is
`1`. -/
def pointsWithDen (c : List ℤ) (H z : ℕ) : List (ℤ × ℤ × ℤ) :=
  ((List.range (2 * H + 1)).map fun i : ℕ ↦ (i : ℤ) - H).flatMap fun x ↦
    let y := Int.sqrt (binaryForm c x z)
    (if y = 0 then [(x, 0, (z : ℤ))] else [(x, y, z), (x, -y, z)]).filter (IsPoint c H)

/-- The points of height at most `H` on `y ^ 2 = F(x, z)` for the coefficient list `c` with
denominators at most `B`, in the order in which ratpoints finds them, for the switch `reverse` of
the reversal and the bound `maxDiv` of the number of divisors: for the polynomial searched
(`Ratpoints.searchedPoly`), its points at infinity, then the points of its denominators up to `B`
(`Ratpoints.searchDenominators`) in turn (`Ratpoints.pointsWithDen`); after a reversal, each point
`(a, y, b)` of that list becomes `(b, y, a)` for `a ≥ 0` and `(-b, y, -a)` for `a < 0`, a point of
the caller's curve. -/
def orderedPoints (maxDiv : ℕ) (reverse : Bool) (c : List ℤ) (H B : ℕ) : List (ℤ × ℤ × ℤ) :=
  let (c', rev) := searchedPoly reverse c
  let L := (0 :: searchDenominators maxDiv c' B).flatMap (pointsWithDen c' H)
  if rev then L.map fun (a, y, b) ↦ if 0 ≤ a then (b, y, a) else (-b, y, -a) else L

/-! ### Examples, checked by `decide` -/

-- `ratpoints '-1 0 9' 10 -q` reverses the polynomial to `9 0 -1` and prints the points of
-- `9 0 -1` in their order, mapped back: `(-3, 0, 1)` becomes `(-1, 0, 3)` and `(0, ±3, 1)` the
-- points `(1, ±3, 0)` at infinity of the caller's curve.
example : orderedPoints 512 true [-1, 0, 9] 10 10 = [(-1, 0, 3), (1, 3, 0), (1, -3, 0), (1, 0, 3),
    (-5, 12, 9), (-5, -12, 9), (5, 12, 9), (5, -12, 9)] := by
  decide +kernel

-- `ratpoints '0 1 0 2' 10 -q` reverses the polynomial of odd degree to `0 2 0 1`.
example : orderedPoints 512 true [0, 1, 0, 2] 10 10 = [(0, 0, 1), (1, 0, 0)] := by
  decide +kernel

-- `ratpoints '-6 5 -3 30' 12 -q` visits the denominator `6` before `5`, in the order of the
-- divisors of `30`: `1, 2, 3, 6, 5, 10, 15, 30`.
example : orderedPoints 512 true [-6, 5, -3, 30] 12 12 =
    [(1, 0, 0), (5, 132, 6), (5, -132, 6), (7, 220, 5), (7, -220, 5)] := by
  decide +kernel

example : binaryDivisors 30 100 = [1, 2, 3, 6, 5, 10, 15, 30] := by
  decide +kernel

-- `ratpoints '0 1031 -11341 30930' 6 -q` factors `30930 = 2 · 3 · 5 · 1031` completely and visits
-- the denominator `6` before `5`; the leading coefficient `30 · 1042451` of
-- `0 1042451 -11466961 31273530` is not factored completely, and its denominators ascend.
example : orderedPoints 512 true [0, 1031, -11341, 30930] 6 6 =
    [(1, 0, 0), (0, 0, 1), (1, 0, 6), (1, 0, 5)] := by
  decide +kernel

example : orderedPoints 512 true [0, 1042451, -11466961, 31273530] 6 6 =
    [(1, 0, 0), (0, 0, 1), (1, 0, 5), (1, 0, 6)] := by
  decide +kernel

-- `3 · 1031` is factored completely, its cofactor `1031 < 37 ^ 2` taken as a prime at `37`;
-- `3 · 1042451` and `1021 · 1031` are not.
example : FactorsByTrialDivision (3 * 1031) ∧ ¬FactorsByTrialDivision (3 * 1042451) ∧
    ¬FactorsByTrialDivision (1021 * 1031) := by
  decide +kernel

/-! ### Examples with a search region, checked by `decide` -/

-- `ratpoints '-6 5 -3 30' 12 -q -dl 5 -du 6`: the divisor order, `6` before `5`, kept.
example : (orderedPoints 512 (true && IsFullBox ([] : List Unit) 5 6 12) [-6, 5, -3, 30] 12
    (denominatorBound 6 12)).filter (fun p ↦ InRegion [] 5 6 p) =
    [(1, 0, 0), (5, 132, 6), (5, -132, 6), (7, 220, 5), (7, -220, 5)] := by
  decide +kernel

-- `ratpoints '-1 0 9' 10 -q -du 9`: no reversal, the range of the denominators not being the whole
-- box.
example : (orderedPoints 512 (true && IsFullBox ([] : List Unit) 1 9 10) [-1, 0, 9] 10
    (denominatorBound 9 10)).filter (fun p ↦ InRegion [] 1 9 p) =
    [(1, 3, 0), (1, -3, 0), (-1, 0, 3), (1, 0, 3), (-5, 12, 9), (-5, -12, 9), (5, 12, 9),
      (5, -12, 9)] := by
  decide +kernel

-- `ratpoints '-1 0 9' 10 -q -dl 0 -du 11`: the whole box, and the reversal.
example : (orderedPoints 512 (true && IsFullBox ([] : List Unit) 0 11 10) [-1, 0, 9] 10
    (denominatorBound 11 10)).filter (fun p ↦ InRegion [] 0 11 p) =
    [(-1, 0, 3), (1, 3, 0), (1, -3, 0), (1, 0, 3), (-5, 12, 9), (-5, -12, 9), (5, 12, 9),
      (5, -12, 9)] := by
  decide +kernel

-- `ratpoints '-1 0 9' 10 -q -du 9 -l -0.2 -u 0.6`, with the doubles that the program passes the
-- library: the double nearest to `-0.2`, which lies below it, and the least double above `0.6`.
example : (orderedPoints 512 (true && IsFullBox [(0xbfc999999999999a, 0x3fe3333333333334)] 1 9 10)
    [-1, 0, 9] 10 (denominatorBound 9 10)).filter (fun p ↦
      InRegion [(doubleValue 0xbfc999999999999a, doubleValue 0x3fe3333333333334)] 1 9 p) =
    [(1, 3, 0), (1, -3, 0), (1, 0, 3), (5, 12, 9), (5, -12, 9)] := by
  decide +kernel

end Ratpoints

end

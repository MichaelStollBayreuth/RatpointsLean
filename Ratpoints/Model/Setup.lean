/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

/-!
# The set-up of a search

What ratpoints does with its input before the sieve, as far as the model has it: the refusals of a
search, each with the error of the program (`Ratpoints.Refusal`), and the reversal check of
`find_points_work_1`, which refuses the binary form when its degree `d` is even and `X ^ 2` divides
it, and otherwise may reverse the polynomial, in three cases, exchanging `x` and `z` in the binary
form (`Ratpoints.Setup.reversal`). `Ratpoints.findPoints` does not run the reversal check yet
(stage D).

## Main definitions

* `Ratpoints.Refusal`: the refusals of a search.
* `Ratpoints.Setup.isSquare`: the squares as GMP decides them.
* `Ratpoints.Setup.reversal`: the reversal check.
-/

@[expose] public section

namespace Ratpoints

/-- The refusals of a search, each with the number of the error with which the program `ratpoints`
refuses the input. The program itself refuses too many or too few coefficients and the height bound
`0`, before it calls the library; the library refuses a binary form that is not squarefree in the
set-up of the search: when the leading zeros of `n + 1` coefficients lower `⌈n / 2⌉`, in the
reversal check (`Ratpoints.Setup.reversal`) and with the remainder chain of the Sturm step
(`Ratpoints.Sturm.chain`). -/
inductive Refusal where
  /-- More than `Ratpoints.maxDegree + 1` coefficients: error 3. -/
  | tooManyCoefficients
  /-- Fewer than two coefficients: error 5. -/
  | tooFewCoefficients
  /-- The height bound `0`: error 4. -/
  | incorrectHeight
  /-- A binary form that is not squarefree: error 8. -/
  | notSquarefree
  deriving DecidableEq, Repr

namespace Setup

/-- Whether `a` is a square, as `mpz_perfect_square_p` of GMP decides it: `0` and the squares of
the positive integers, so that no negative integer is a square. -/
def isSquare (a : Int) : Bool := 0 ≤ a && a.toNat.sqrt * a.toNat.sqrt == a.toNat

/-- The reversal check on the coefficients `c` of degree `d`, the leading zeros dropped, with the
switch `allow` of the reversal: the list that the search goes on with, its degree, and whether it is
reversed. If the switch is off, `c` itself. Otherwise, for even `d` with `c₀ = 0`, the refusal
`Ratpoints.Refusal.notSquarefree` if also `c₁ = 0`, since `X ^ 2` then divides the binary form, and
else the list `c_d, …, c₁, c₀` with the degree `d - 1` (case 1); for even `d` with `c_d` a square
and `c₀` not (`Ratpoints.Setup.isSquare`), the list `c_d, …, c₀` (case 2); for odd `d` with
`|c_d| ≠ 1`, `c₀ = 0` and `|c₁| = 1`, the list `c₀, c_d, …, c₁` (case 3); and otherwise `c`
itself. In each case the reversed list is the reflection of `c` in the even degree `d + d % 2` of
the binary form, so that its binary form is that of `c` with `x` and `z` exchanged
(`Ratpoints.Setup.binaryForm_eq_of_reversal_eq_ok`).

C: `find_points.c:4732-4803`

Deviation: a new list for the reversal in place, and nothing written back to the caller: the
reversed coefficients, the degree and the flag `RATPOINTS_REVERSED` are returned instead; the
switch for the test of the flags `RATPOINTS_NO_REVERSE` and `RATPOINTS_NO_REVERSE_AUTO`, so that
the check runs whenever the switch allows it, without `RATPOINTS_NO_REVERSE_AUTO`, which a search
region or a denominator range sets (stage H); the square test of `c_d` made here, where the C code
reads the flag `lcfsq` that the set-up computes before (line 4634), and no flag `lcfsq` for the
reversed list, which case 2 clears, since `Ratpoints.Sieve.pointsAtInfinity` tests the leading
coefficient of the list it is given; integers and their absolute values for the GMP integers, with
no scratch integers `work[0]` and `work[1]`; no output under `RATPOINTS_VERBOSE`. -/
def reversal (allow : Bool) (c : List Int) (d : Nat) : Except Refusal (List Int × Nat × Bool) :=
  if !allow then .ok (c, d, false)
  else if d % 2 = 0 then
    if c.getD 0 0 = 0 then
      if c.getD 1 0 = 0 then .error .notSquarefree
      else .ok ((c.take (d + 1)).reverse, d - 1, true)
    else if isSquare (c.getD d 0) && !isSquare (c.getD 0 0) then
      .ok ((c.take (d + 1)).reverse, d, true)
    else .ok (c, d, false)
  else if (c.getD d 0).natAbs ≠ 1 ∧ c.getD 0 0 = 0 ∧ (c.getD 1 0).natAbs = 1 then
    .ok (c.getD 0 0 :: ((c.take (d + 1)).drop 1).reverse, d, true)
  else .ok (c, d, false)

/-! ### Examples

What ratpoints 3.1.1 does at the pinned commit: with `-v` it says whether it reverses and in which
case, and prints the coefficients of case 3; `-k` switches the reversal off; and
`ratpoints '0 0 1 1 1' 5 -q -s`, without the Sturm step, which would refuse the form too, ends with
error 8, which `-s -k` does not. -/

#guard [0, 1, 4, 9, 2 ^ 126].all isSquare && !([2, 3, -1, -4, 2 ^ 127].any isSquare)

-- Case 1, for `0 1 0 0 4` and `0 -3 -5`; case 2, for `-1 0 9`; and case 3, for `0 1 0 2` and for
-- `0 1 0 2 0`, its leading zero dropped.
#guard (reversal true [0, 1, 0, 0, 4] 4).toOption == some ([4, 0, 0, 1, 0], 3, true) &&
  (reversal true [0, -3, -5] 2).toOption == some ([-5, -3, 0], 1, true)
#guard (reversal true [-1, 0, 9] 2).toOption == some ([9, 0, -1], 2, true)
#guard (reversal true [0, 1, 0, 2] 3).toOption == some ([0, 2, 0, 1], 3, true) &&
  (reversal true [0, 1, 0, 2, 0] 3).toOption == some ([0, 2, 0, 1], 3, true)

-- `c₀ = c₁ = 0` for even `d`: the refusal, unless the switch is off.
#guard reversal true [0, 0, 1, 1, 1] 4 matches .error .notSquarefree
#guard (reversal false [0, 0, 1, 1, 1] 4).toOption == some ([0, 0, 1, 1, 1], 4, false)

-- The switch off, and lists that meet no case: `c₀` a square, `c_d` not, `|c₁| ≠ 1`,
-- `|c_d| = 1`, `c₀ ≠ 0`.
#guard (reversal false [-1, 0, 9] 2).toOption == some ([-1, 0, 9], 2, false)
#guard ([([4, 0, 9], 2), ([-1, 0, -9], 2), ([0, 2, 0, 3], 3), ([0, 1, 0, -1], 3),
    ([-2, 0, 0, 1], 3), ([1, 2, 3, 4, 5, 6, 7], 6)] : List (List Int × Nat)).all fun (c, d) ↦
  (reversal true c d).toOption == some (c, d, false)

end Setup

end Ratpoints

end

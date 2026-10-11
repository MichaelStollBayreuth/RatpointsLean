/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.Params
public import Ratpoints.Model.Setup
public import Ratpoints.Model.Sieve

-- The `#guard` examples run code of the imported modules at compile time.
meta import Ratpoints.Model.Params
meta import Ratpoints.Model.Sieve

/-!
# The search for the points

`Ratpoints.findPoints c H P` is the model of the library function `find_points` of ratpoints: it
refuses, as the program does (`Ratpoints.Refusal`), more than `Ratpoints.maxDegree + 1`
coefficients, fewer than two and the height bound `0`, and otherwise returns the points of height
at most `H` on `y ^ 2 = F(x, z)`, the points at infinity first and then those of the denominators
`1, …, H`, found by the sieve on the bit arrays of words with the moduli and the array size of the
parameters `P`.

## Main definitions

* `Ratpoints.findPoints`: the points.
-/

@[expose] public section

namespace Ratpoints

open Sieve in
/-- The points of height at most `H` on `y ^ 2 = F(x, z)` for the coefficient list `c`, found by the
sieve with the moduli and the array size of the parameters `P`: more than `Ratpoints.maxDegree + 1`
coefficients, fewer than two, and `H = 0` are refused, in the order of the program; otherwise the
points at infinity (`Ratpoints.Sieve.pointsAtInfinity`) come first, then those of the denominators
`1, …, H` (`Ratpoints.Sieve.sieveRun`) with the tables of the moduli
(`Ratpoints.Sieve.examinePrime`) and pieces of at most `Ratpoints.Params.arraySizeAt P H` bit
arrays.

C: `find_points.c:4557-4558`, `find_points.c:4624-4633`, `find_points.c:4658`

Deviation: the refusals of the program, with its errors (`Ratpoints.Refusal`), for the library's
`RATPOINTS_BAD_ARGS`: fewer than two coefficients are refused on the length of `c`, as the program
refuses them, where the library refuses an empty list as a negative degree and one coefficient as
the degree 0; the degree with the leading zeros dropped is `Ratpoints.BruteForce.degree c`; no
refusal of a form that is not squarefree and no exit when there are no points modulo a prime (stage
D), so that the zero polynomial and the forms that ratpoints refuses get the points of the
specification; no reversal (stage D), no search region (stage H); no failure for lack of memory,
which the model cannot meet. -/
def findPoints (c : List Int) (H : Nat) (P : Params) : Except Refusal (List (Int × Int × Int)) :=
  if maxDegree + 1 < c.length then .error .tooManyCoefficients
  else if c.length < 2 then .error .tooFewCoefficients
  else if H = 0 then .error .incorrectHeight
  else
    let d := BruteForce.degree c
    let entries := P.moduli.map (examinePrime c d)
    .ok (pointsAtInfinity c d ++ (Id.run (sieveRun c d H (P.arraySizeAt H) entries)).toList)

/-! ### Examples

The points that `ratpoints c H -q` prints at the pinned commit, in the same order; the list of the
brute-force reference `Ratpoints.bruteForce` for other parameters, among them pieces of a few bit
arrays, and for inputs that the program refuses; the tables of inverses and squares
(`Ratpoints.Sieve.inversesMod`, `Ratpoints.Sieve.squaresMod`) of the `Ratpoints.numPrimes` primes
among which the moduli are chosen; and the refusals, the coefficients before the height bound. -/

#guard (findPoints [-2, 0, 0, 1] 130 defaultParams).toOption ==
  some [(1, 0, 0), (3, 5, 1), (3, -5, 1), (129, 3830, 100), (129, -3830, 100)]

#guard (findPoints [1, 2, 3, 4, 5, 6, 7] 20 defaultParams).toOption ==
  some [(-1, 2, 1), (-1, -2, 1), (0, 1, 1), (0, -1, 1), (8, 2401, 7), (8, -2401, 7)]

#guard (findPoints [1, 1, 1, 1, 0] 25 defaultParams).toOption ==
  some [(1, 0, 0), (-1, 0, 1), (0, 1, 1), (0, -1, 1), (1, 2, 1), (1, -2, 1), (7, 20, 1),
    (7, -20, 1), (-3, 10, 4), (-3, -10, 4)]

#guard (findPoints [1, 0, 126, 0, 441] 30 defaultParams).toOption ==
  some [(1, 21, 0), (1, -21, 0), (0, 1, 1), (0, -1, 1), (-1, 31, 2), (-1, -31, 2), (1, 31, 2),
    (1, -31, 2), (-2, 651, 21), (-2, -651, 21), (2, 651, 21), (2, -651, 21)]

-- The program reverses this polynomial and prints the points in another order.
#guard ((findPoints [-1, 0, 9] 4 defaultParams).toOption.getD []).isPerm
  [(-1, 0, 3), (1, 3, 0), (1, -3, 0), (1, 0, 3)]

-- No moduli, all 53 primes, the 53 primes in three stages, and moduli in another order.
#guard [⟨[], 0, 0, 64, true, 0⟩, sieveParams { numPrimes := 53 },
    ⟨primeTable.toList.take 53, 10, 40, 64, true, 0⟩,
    ⟨[7, 3, 251, 5], 1, 2, 0, false, 0⟩].all fun P ↦
  [([1, 1, 1, 1, 0], 25), ([-1, 0, 9], 20), ([1, 0, 1], 12), ([0, 0, 1], 15)].all fun (c, H) ↦
    (findPoints c H P).toOption == some (bruteForce c H)

-- Pieces of one, two and three bit arrays, at heights around the multiples of 64 and of
-- `rbaLength`: several pieces, the masks on the same piece and on different ones, and no low mask
-- when `H` is a multiple of `rbaLength`.
#guard [([-2, 0, 0, 1], [63, 64, 65, 255, 256, 257]), ([1, 1, 1, 1, 0], [128, 129])].all
  fun (c, Hs) ↦ Hs.all fun H ↦
    let bf := bruteForce c H
    [1, 2, 3].all fun A ↦
      let P := { defaultParams with moduli := primeTable.toList.take 5, arraySize := A }
      (findPoints c H P).toOption == some bf

-- The zero polynomial and polynomials of degree 0 with two or more coefficients, which the
-- program refuses as not squarefree.
#guard [([0, 0], 7), ([5, 0, 0, 0], 9), ([4, 0], 6)].all fun (c, H) ↦
  (findPoints c H defaultParams).toOption == some (bruteForce c H)

-- The tables of the 53 primes of the default build: each nonzero residue times its entry in the
-- table of inverses is 1, and the table of squares marks `(p + 1) / 2` residues.
#guard (primeTable.toList.take numPrimes).all fun p ↦
  let inv := Sieve.inversesMod p
  (List.range' 1 (p - 1)).all (fun r ↦ inv[r]! * r % p == 1) &&
    (Sieve.squaresMod p).count true == (p + 1) / 2

#guard findPoints (List.replicate (maxDegree + 2) 1) 0 defaultParams matches
  .error .tooManyCoefficients
#guard findPoints (List.replicate (maxDegree + 1) 1) 1 ⟨[], 0, 0, 64, true, 0⟩ matches .ok _
#guard findPoints [1] 0 defaultParams matches .error .tooFewCoefficients
#guard findPoints [1, 0, 1] 0 defaultParams matches .error .incorrectHeight

end Ratpoints

end

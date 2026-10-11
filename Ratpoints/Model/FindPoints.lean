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
meta import Ratpoints.Model.Setup
meta import Ratpoints.Model.Sieve

/-!
# The search for the points

`Ratpoints.findPoints c H P` is the model of the library function `find_points` of ratpoints: it
refuses, as the program does (`Ratpoints.Refusal`), more than `Ratpoints.maxDegree + 1`
coefficients, fewer than two and the height bound `0`, and otherwise runs the search of the
polynomial (`Ratpoints.searchPoints`), which returns no points when the curve has none modulo one
of the moduli of the parameters `P`, and otherwise the points of height at most `H` on
`y ^ 2 = F(x, z)`, the points at infinity first and then those of the denominators `1, …, H`, found
by the sieve on the bit arrays of words with the moduli and the array size of `P`.

## Main definitions

* `Ratpoints.searchPoints`: the search of the polynomial that the set-up hands on.
* `Ratpoints.findPoints`: the points.
-/

@[expose] public section

namespace Ratpoints

open Sieve in
/-- The search of the polynomial with the coefficient list `c` of degree `d` that the set-up hands
on, for the height `H`, the parameters `P` and the flag `rev` of the reversal: the table of each
modulus of `P` with the exit (`Ratpoints.Sieve.examinePrime?`), with the flag of the `long`s
(`Ratpoints.Setup.useCLong`), and no points when one of them is none, since the curve has no points
modulo that prime; otherwise the points at infinity (`Ratpoints.Sieve.pointsAtInfinity`), followed
by those of the denominators `1, …, H` (`Ratpoints.Sieve.sieveRun`) with these tables and pieces of
at most `Ratpoints.Params.arraySizeAt P H` bit arrays, each point mapped by
`Ratpoints.Sieve.swapPoint` when `rev` is set. For well-formed parameters, `H ≥ 1` and `d` the
degree of `c`, these are the points of the brute-force reference, mapped when `rev` is set, also
when the exit is taken (`Ratpoints.run_searchPoints`).

C: `find_points.c:2608-2614`, `find_points.c:2994-2998`, `find_points.c:4992-5012`,
`find_points.c:5106`

Deviation: the primes examined are the moduli of the parameters, where `sieving_info` examines the
first `num_primes` primes of the table, and more when their number was left to the library: the
choice of the moduli is an input of the model, and when the exit is taken there are no points, so
that the output does not depend on the primes examined; the arguments of `sieving_info` that serve
the choice of the moduli (the list of the moduli, the mean number of bits per word, whether the
number of primes was left to the library) and the 2-adic classes (stage E) are not modelled; the
exit gives the empty list, where `sieving_info` returns the prime and `find_points_work_1` the
number `0` of points found; no 2-adic exit (stage E), which ends only searches without points; the
Sturm step does not restrict the search region before stage H, so that the return when it leaves
nothing to search is never taken, and the run always follows the points at infinity; no failure for
lack of memory, which the model cannot meet; no output under `RATPOINTS_VERBOSE` or `DEBUG`. -/
def searchPoints (c : List Int) (d H : Nat) (P : Params) (rev : Bool) :
    Id (List (Int × Int × Int)) := do
  let useCLong := Setup.useCLong c d
  match P.moduli.mapM (examinePrime? c d · useCLong) with
  | none => return []
  | some entries =>
    let pts ← sieveRun c d H (P.arraySizeAt H) rev entries
    return pointsAtInfinity c d rev ++ pts.toList

/-- The points of height at most `H` on `y ^ 2 = F(x, z)` for the coefficient list `c`, found by the
sieve with the moduli and the array size of the parameters `P`: more than `Ratpoints.maxDegree + 1`
coefficients, fewer than two, and `H = 0` are refused, in the order of the program; otherwise the
points of the search of the polynomial of degree `Ratpoints.BruteForce.degree c`
(`Ratpoints.searchPoints`) with the flag of the reversal clear: none when the curve has no points
modulo one of the moduli, and else the points at infinity first, then those of the denominators
`1, …, H`, with the tables of the moduli and pieces of at most `Ratpoints.Params.arraySizeAt P H`
bit arrays.

C: `find_points.c:4557-4558`, `find_points.c:4624-4633`, `find_points.c:4658`

Deviation: the refusals of the program, with its errors (`Ratpoints.Refusal`), for the library's
`RATPOINTS_BAD_ARGS`: fewer than two coefficients are refused on the length of `c`, as the program
refuses them, where the library refuses an empty list as a negative degree and one coefficient as
the degree 0; the degree with the leading zeros dropped is `Ratpoints.BruteForce.degree c`; no
refusal of a form that is not squarefree (stage D), so that the zero polynomial and the forms that
ratpoints refuses get the points of the specification; no reversal (stage D), no search region
(stage H); no failure for lack of memory, which the model cannot meet. -/
def findPoints (c : List Int) (H : Nat) (P : Params) : Except Refusal (List (Int × Int × Int)) :=
  if maxDegree + 1 < c.length then .error .tooManyCoefficients
  else if c.length < 2 then .error .tooFewCoefficients
  else if H = 0 then .error .incorrectHeight
  else .ok (Id.run (searchPoints c (BruteForce.degree c) H P false))

/-! ### Examples

The points that `ratpoints c H -q` prints at the pinned commit, in the same order; the list of the
brute-force reference `Ratpoints.bruteForce` for other parameters, among them pieces of a few bit
arrays, and for inputs that the program refuses; the search with the flag of the reversal, for
polynomials to which ratpoints reverses others, and on curves without points modulo `3`, `5` and
`7`, where it takes the exit; the tables of inverses and squares (`Ratpoints.Sieve.inversesMod`,
`Ratpoints.Sieve.squaresMod`) of the `Ratpoints.numPrimes` primes among which the moduli are chosen;
and the refusals, the coefficients before the height bound. -/

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

-- The search of the polynomials `9 0 -1`, `4 0 0 1 0` and `0 2 0 1`, to which ratpoints reverses
-- `-1 0 9`, `0 1 0 0 4` and `0 1 0 2`, with the flag of the reversal: the points that
-- `ratpoints '-1 0 9' 10 -q`, `ratpoints '0 1 0 0 4' 10 -q` and `ratpoints '0 1 0 2' 10 -q` print,
-- in their order.
#guard
  ([([9, 0, -1], 2, [(-1, 0, 3), (1, 3, 0), (1, -3, 0), (1, 0, 3), (-5, 12, 9), (-5, -12, 9),
      (5, 12, 9), (5, -12, 9)]),
    ([4, 0, 0, 1, 0], 3, [(0, 0, 1), (1, 2, 0), (1, -2, 0)]),
    ([0, 2, 0, 1], 3, [(0, 0, 1), (1, 0, 0)])] :
      List (List Int × Nat × List (Int × Int × Int))).all fun (c, d, pts) ↦
    Id.run (searchPoints c d 10 defaultParams true) == pts

-- Curves without points modulo 3, 5 and 7, for which `ratpoints c 30 -q` prints nothing: the
-- table of one of the default moduli is none, and the search returns no points, with either flag.
#guard [[20, 6, -14, 12, -10], [-2, -20, 7, 15, 2], [20, 7, -18, 0, 3]].all fun c ↦
  (defaultParams.moduli.mapM (Sieve.examinePrime? c 4 · (Setup.useCLong c 4))).isNone &&
    [false, true].all fun rev ↦ Id.run (searchPoints c 4 30 defaultParams rev) == []

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

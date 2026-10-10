/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

/-!
# The plain sieve

The components of the plain sieve, each in the simplest form of its place in the C function
`find_points_work_1`: the table of a prime (`Ratpoints.Sieve.examinePrime`), the rows of a
denominator (`Ratpoints.Sieve.Entry.admits`), whose test of a numerator (`Ratpoints.Sieve.survives`)
is the interface between the sieve and the check, and the sieve of one denominator with one Boolean
per numerator (`Ratpoints.Sieve.sieveDen`). Every row lets every point through. The tables that the
build of ratpoints generates (the squares, the inverses, the row of `0`) are Lean functions here.

## Main definitions

* `Ratpoints.Sieve.squaresMod`, `Ratpoints.Sieve.inversesMod`: the squares and the inverses
  modulo `p`.
* `Ratpoints.Sieve.examinePrime`: the table of a prime.
* `Ratpoints.Sieve.Entry.admits`, `Ratpoints.Sieve.survives`: the rows of a denominator.
* `Ratpoints.Sieve.sieveDen`: the sieve of one denominator.
-/

@[expose] public section

namespace Ratpoints

namespace Sieve

/-! ### The tables of a prime -/

/-- The squares modulo `p`, as a table of Booleans indexed by the residues: zero and the squares
of the odd residues `i < p`, as the generator of the tables of ratpoints marks them; for odd `p`,
the squares of `i` and of `p - i` agree, so these are all the squares.

C: `gen_find_points_h.c:69-88`

Deviation: a function of `p`, computed when it is called, for the row of `p` in the table
`squares` that the build generates. -/
def squaresMod (p : Nat) : Array Bool :=
  (List.range' 1 (p / 2) 2).foldl (fun w i ↦ w.set! (i * i % p) true)
    ((Array.replicate p false).set! 0 true)

/-- The inverses modulo `p`, as a table indexed by the residues: `0` for `0`, and for every other
residue `b` the least `i ≥ 1` with `i b ≡ 1 (mod p)`, found by trial.

C: `gen_find_points_h.c:33-44`, `gen_find_points_h.c:90-100`

Deviation: a function of `p`, computed when it is called, for the row of `p` in the table
`inverses` that the build generates; the trial stops before `p` and gives `0` when it finds
nothing, where `inv_mod_p` would not stop, which never happens for a prime `p` and a residue other
than `0`. -/
def inversesMod (p : Nat) : Array Nat :=
  (Array.range p).map fun b ↦ ((List.range' 1 (p - 1)).find? (· * b % p == 1)).getD 0

/-- Horner's rule modulo `p`: the value modulo `p` at `x` of the polynomial with the coefficient
list `cs`, constant term first, reduced at every step. -/
def evalMod (cs : List Nat) (p x : Nat) : Nat := cs.foldr (fun a v ↦ (a + x * v) % p) 0

/-- What the sieve keeps of a prime `p`: `p`, the table of the residues `x` modulo `p` for which
`f(x)` is a square modulo `p`, and the inverses modulo `p`.

C: `rp-private.h:542-555`

Deviation: only the fields that the rows of a prime read, and no rows: ratpoints keeps the row of
each residue in `sieve`, that of `0` from the build and the others made by `init` when a
denominator first needs one, where `Ratpoints.Sieve.Entry.admits` computes each bit from the
tables; the other fields serve the composite moduli, the packing and the reduction of the sieve
(stage F), and the choice of the moduli. -/
structure Entry where
  /-- The prime. -/
  p : Nat
  /-- For each residue `x` modulo `p`, whether `f(x)` is a square modulo `p`. -/
  isFSquare : Array Bool
  /-- The inverses modulo `p` of the residues. -/
  inverses : Array Nat

/-- The table of the prime `p` for the polynomial `f` of degree `d` with the coefficient list `c`:
for each residue `x` modulo `p`, whether `f(x)` is a square modulo `p`, with `f(x)` by Horner's
rule modulo `p` (`Ratpoints.Sieve.evalMod`) on the coefficients reduced modulo `p`, and the squares
of `Ratpoints.Sieve.squaresMod`; kept, as the sieve entry of ratpoints keeps it, with `p` and the
inverses modulo `p` (`Ratpoints.Sieve.inversesMod`).

C: `find_points.c:1703-1749`, `find_points.c:1761-1765`, `find_points.c:1795-1824`

Deviation: the coefficients are integers, reduced by the Euclidean `%`, for the two paths of
ratpoints through `long`s and GMP integers (stage D), and they are not handed back, where
`examine_prime` leaves them in its caller's array for the test on the forbidden divisors of the
denominators (stage E); Horner's rule reduces at every step, for the reduction on a fixed schedule
(stage F), and also gives `f(0)`, which ratpoints reads off the constant term; the table has no
last entry, whether there are points at infinity modulo `p`, which ratpoints reads only for its
exits, the density, the prime powers and the forbidden divisors, never in a row or in the third
stage; the entry is made for every prime it is given, where `examine_prime` makes none when there
is no point at infinity modulo `p` and `f(x)` is a square for no residue (it returns `-1`, and the
search ends with no points: stage D) or for every residue (it returns `0`, and `p` is never a
modulus: the choice of the moduli, an input of the model), so that the residues with a square value
are not counted either; the entry keeps only `p`, the table and the inverses
(`Ratpoints.Sieve.Entry`), and no rows. -/
def examinePrime (c : List Int) (d p : Nat) : Entry :=
  let cs := (List.range (d + 1)).map fun n ↦ (c.getD n 0 % (p : Int)).toNat
  let sq := squaresMod p
  { p, isFSquare := (Array.range p).map fun x ↦ sq[evalMod cs p x]!, inverses := inversesMod p }

/-! ### The rows of a denominator -/

/-- Whether the row of the denominator `b` in the table `e` admits the numerator `a`: for the
residues `r = b mod p` and `x = a mod p`, the entry of the table at `x r⁻¹ mod p` if `r ≠ 0`, and
whether `x ≠ 0` if `r = 0`.

C: `init.c:42-46`, `init.c:62-83`, `init.c:99-111`, `init.c:118-246`, `gen_find_points_h.c:102-134`,
`gen_init_sieve_h.c:48-62`

Deviation: the bit of `a` in the row of `r`, computed from the tables for each numerator, where
ratpoints builds the row of a residue `r ≠ 0` once, when a denominator first needs it, as a bit
pattern of `p` bits repeated through words, by a function for each prime that the build generates,
and takes the row of `0` from the pattern `sieves0` that the build generates, whose bit `N` is
clear exactly when `p` divides `N`. -/
def Entry.admits (e : Entry) (b : Nat) (a : Int) : Bool :=
  let r := b % e.p
  let x := (a % (e.p : Int)).toNat
  if r = 0 then x != 0 else e.isFSquare[x * e.inverses[r]! % e.p]!

/-- Whether the numerator `a` survives the tables `entries` for the denominator `b`: the row of
`b` in every table admits `a` (`Ratpoints.Sieve.Entry.admits`). This test, a function of the
numerator, is the interface between the sieve and the check. -/
def survives (entries : List Entry) (b : Nat) (a : Int) : Bool := entries.all (·.admits b a)

/-! ### The sieve -/

/-- The sieve of the denominator `b`: an array of `2H + 1` Booleans, one for each numerator
`a = i - H`, all true at the start; for each table of `entries` in turn, every entry is replaced
by its conjunction with the row of `b` at `a` (`Ratpoints.Sieve.Entry.admits`).

C: `sift.c:291-312`, `sift.c:405-431`, `sift.c:943-1022`, `sift.c:1030-1041`, `sift.c:1083-1086`,
`sift.c:1184-1202`

Deviation: one Boolean per numerator, for the bit arrays of words, the pieces of the numerator range
and the masks at their ends (stage C2); every numerator from `-H` to `H`, for the search region
(stage H) and the 2-adic classes (stages E and F); every table applied to every numerator, one after
the other, for the stages of ratpoints with their composite moduli, their packing and their
correction during the run (stage F): the second stage stops when no bit is left, and the third
tests one numerator at a time, only those that pass the test for common factors, stops at the first
prime that rejects it and skips the primes that divide `b`, with the inverses of `b` that
`fill_checks` looks up when the first such numerator of `b` reaches the stage; the cited lines are
the first stage of the build with 64-bit bit arrays, which the default build does in chunks of
registers, its second stage with the masks at the ends of the range, and its third stage. -/
def sieveDen (H b : Nat) (entries : List Entry) : Id (Vector Bool (2 * H + 1)) := do
  let mut surv := Vector.replicate (2 * H + 1) true
  for e in entries do
    for h : i in [0:2 * H + 1] do
      surv := surv.set i (surv[i] && e.admits b ((i : Int) - H))
  return surv

/-! ### Examples -/

-- The rows of 3, 5, 7, 11 and 13 in the tables `squares` and `inverses` that the build of
-- ratpoints generates.
#guard squaresMod 3 == #[true, true, false] &&
  squaresMod 5 == #[true, true, false, false, true] &&
  squaresMod 7 == #[true, true, true, false, true, false, false] &&
  squaresMod 11 == #[true, true, false, true, true, true, false, false, false, true, false] &&
  squaresMod 13 ==
    #[true, true, false, true, true, false, false, false, false, true, true, false, true]

#guard inversesMod 3 == #[0, 1, 2] && inversesMod 5 == #[0, 1, 3, 2, 4] &&
  inversesMod 7 == #[0, 1, 4, 5, 2, 3, 6] &&
  inversesMod 11 == #[0, 1, 6, 4, 3, 9, 2, 8, 7, 5, 10] &&
  inversesMod 13 == #[0, 1, 7, 9, 10, 8, 11, 2, 5, 3, 4, 6, 12]

-- The row of `0`, that of `sieves0`: the numerators not divisible by `p`.
#guard (List.range 41).all fun i ↦
  (examinePrime [1, 2, 3] 2 7).admits 14 ((i : Int) - 20) == (((i : Int) - 20) % 7 != 0)

-- `y ^ 2 = x ^ 2 + 1` modulo 5: `f(x)` is a square for `x = 0, 2, 3` (`f = 1, 0, 0`).
#guard (examinePrime [1, 0, 1] 2 5).isFSquare == #[true, false, true, true, false]

-- The row of `b = 3` modulo 5 admits `a` when `f(a / 3)` is a square modulo 5.
#guard (List.range 5).map (fun a : Nat ↦ (examinePrime [1, 0, 1] 2 5).admits 3 a) ==
  [true, true, false, false, true]

-- The sieve of a denominator is the survivor test of the numerators.
#guard
  let es := [3, 5, 7].map (examinePrime [1, 2, 3, 4, 5, 6, 7] 6)
  (Id.run (sieveDen 20 7 es)).toList ==
    (List.range 41).map fun i : Nat ↦ survives es 7 ((i : Int) - 20)

end Sieve

end Ratpoints

end

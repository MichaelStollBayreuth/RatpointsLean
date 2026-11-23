/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

/-!
# The Jacobi symbol by the binary algorithm

The Jacobi symbol as the C functions `jacobi` and `jacobi1` compute it, by the binary algorithm
(`Ratpoints.Sieve.jacobi`), with the helpers into which the model divides it. Two components of the
search call it: the Jacobi test on the denominators, where the run does not test by tables
(`Ratpoints.Sieve.wordsTest`, in `Ratpoints.Model.Denominators`), and the modular test before the
exact check, on the value of the binary form modulo a large prime (`Ratpoints.Sieve.passesTest`, in
`Ratpoints.Model.Candidate`); so the algorithm stands before both.

## Main definitions

* `Ratpoints.Sieve.jacobi`: the Jacobi symbol by the binary algorithm, with its helpers
  `Ratpoints.Sieve.twoSign`, `Ratpoints.Sieve.jacobiReduce` and `Ratpoints.Sieve.jacobiRound`.
-/

@[expose] public section

namespace Ratpoints

namespace Sieve

/-- The sign `s` times `(2 / m)` for odd `m`: negated when bit 1 of `m` is set (`m ≡ 3, 7 (mod 8)`)
and again when bit 2 is (`m ≡ 5, 7 (mod 8)`), so negated in all exactly for `m ≡ 3, 5 (mod 8)`,
where `(2 / m) = -1`. -/
def twoSign (m : Nat) (s : Int) : Int :=
  let s := if m &&& 2 != 0 then -s else s
  if m &&& 4 != 0 then -s else s

/-- One subtraction loop of the binary algorithm (`Ratpoints.Sieve.jacobi`) on the odd `x` and `y`:
while `x > y`, `x` becomes `x - y` and is then halved until it is odd again, the sign `s` taking the
factor `(2 / y)` at each halving (`Ratpoints.Sieve.twoSign`); the new `x` and the sign. -/
def jacobiReduce (x y : Nat) (s : Int) : Id (Nat × Int) := do
  let mut x := x
  let mut s := s
  while y < x do
    x := x - y
    repeat
      s := twoSign y s
      x := x / 2
      if x % 2 == 1 then break
  return (x, s)

/-- One round of the binary algorithm (`Ratpoints.Sieve.jacobi`) for the symbol `(f / b)`, `f > 0`
and `b` odd: from `n = f` and `m = b`, the factors `2` are taken out of `n` with the sign of
`(2 / m)`; then the two are exchanged, with the sign of the reciprocity when both are `≡ 3 (mod 4)`,
and the larger reduced by the smaller (`Ratpoints.Sieve.jacobiReduce`), in turn, until they are
equal. The common value `g`, the gcd of `f` and `b`, is returned with the sign, which is the symbol
`(f / b)` when `g = 1`. -/
def jacobiRound (f b : Nat) : Id (Nat × Int) := do
  let mut s : Int := 1
  let mut n := f
  let mut m := b
  while n % 2 == 0 do
    s := twoSign m s
    n := n / 2
  repeat
    if n &&& m &&& 2 != 0 then s := -s
    (m, s) ← jacobiReduce m n s
    if m == n then break
    if n &&& m &&& 2 != 0 then s := -s
    (n, s) ← jacobiReduce n m s
    if m == n then break
  return (m, s)

/-- The Jacobi symbol `(lcf / b*)` for `b > 0`, where `b*` is `b` with the prime factors of `2 lcf`
taken out, so that it is `±1`, by the binary algorithm of the C code: the factors `2` are taken out
of `b`, and `f = lcf mod b`; while `f ≠ 0`, a round of the algorithm (`Ratpoints.Sieve.jacobiRound`)
gives the symbol `(f / b)` when `f` and `b` are coprime, and otherwise their gcd, which is divided
out of `b`, `f` being reduced modulo the new `b` when it is not smaller. When `f` is `0`, `b*` is
`1`, and so is the symbol. For `b = 0` the loop does not end.

C: `find_points.c:511-579`, `find_points.c:581-654`

Deviation: one function for `jacobi`, on the GMP integer `lcf`, and `jacobi1`, on a `long`, which
the run calls when all coefficients are `long`s (`use_c_long`), and the modular test before the
exact check with a modulus of the test and a residue modulo it (`Ratpoints.Sieve.passesTest`), with
the steps of `jacobi`: `jacobi1` takes the sign of `lcf` out as `(-1 / b)^neg` and its value
`LONG_MIN` as `LONG_MIN / 4`, so that the negation of a negative `lcf` is a `long`
(`Ratpoints.fitsLong_neg_ite_div_four`), reduces `|lcf|` modulo `b` only for `b < 2^59`, and does
not reduce it after dividing `b` by the gcd, which changes the steps but not the symbol; the round
of the algorithm and its two subtraction loops, which the C code writes out twice each, as helpers
(`Ratpoints.Sieve.jacobiRound`, `Ratpoints.Sieve.jacobiReduce`, `Ratpoints.Sieve.twoSign`); natural
numbers for the `long`s `b`, `f`, `n` and `m`, and integers for the `long` sign `s` and the `long`
`lcf` of `jacobi1`; `f` the Euclidean `lcf % b`, for `mpz_fdiv_r_ui` with its scratch integer `tmp`;
the tests `f = 0` of the C code, at the start and after each division of `b`, as the condition of
the outer loop; the masks of the signs by `&&&` on natural numbers; the symbol as an integer, for
the `int`. -/
def jacobi (b : Nat) (lcf : Int) : Id Int := do
  let mut b := b
  while b % 2 == 0 do
    b := b / 2
  let mut f := (lcf % (b : Int)).toNat
  while f != 0 do
    let (g, s) ← jacobiRound f b
    if g == 1 then return s
    b := b / g
    if b ≤ f then f := f % b
  return 1

-- The Jacobi symbol by the binary algorithm: `(2 / 7) = 1`, `(3 / 7) = -1`, `(-1 / 3) = -1`,
-- `(5 / 21) = 1`, `(10 / 21) = -1`; `b*` without the primes of `2 lcf`: `(6 / 9)` over `b* = 1`,
-- `(3 / 28)` over `b* = 7`, `(-12 / 75)` over `b* = 25`.
#guard [Id.run (jacobi 7 2), Id.run (jacobi 7 3), Id.run (jacobi 3 (-1)), Id.run (jacobi 21 5),
    Id.run (jacobi 21 10), Id.run (jacobi 9 6), Id.run (jacobi 28 3), Id.run (jacobi 75 (-12))] ==
  [1, -1, -1, 1, -1, 1, -1, 1]

-- The binary algorithm against a direct computation of `(lcf / b*)`: the product over the odd
-- primes `q ∤ lcf` of `b`, each as often as it divides `b`, of Euler's criterion
-- `lcf ^ ((q - 1) / 2) mod q`, read as `1` or `-1`, for the denominators up to 300.
#guard
  let primes := (List.range' 3 298).filter fun q ↦ (List.range' 2 (q - 2)).all (q % · != 0)
  [7, -12, 18, 2, -1, 3 * 5 * 7 * 11, -(2 ^ 63)].all fun (lcf : Int) ↦
    let euler (q : Nat) : Int := if (lcf % q).toNat ^ ((q - 1) / 2) % q == 1 then 1 else -1
    (List.range' 1 300).all fun b ↦
      Id.run (jacobi b lcf) == (primes.filter fun q ↦ b % q == 0 && lcf % q != 0).foldl
        (fun s q ↦ s * euler q ^ ((List.range 10).filter fun k ↦ b % q ^ (k + 1) == 0).length) 1

-- The helpers of the binary algorithm: `(2 / m)` for `m = 1, 3, 5, 7`; one subtraction loop on
-- `15` and `3`; the rounds for `(2 / 7)`, which ends at the gcd 1 with the symbol 1, and for
-- `(6 / 9)`, which ends at the gcd 3.
#guard [twoSign 1 1, twoSign 3 1, twoSign 5 1, twoSign 7 1] == [1, -1, -1, 1] &&
  Id.run (jacobiReduce 15 3 1) == (3, 1) && Id.run (jacobiRound 2 7) == (1, 1) &&
  (Id.run (jacobiRound 6 9)).1 == 3

end Sieve

end Ratpoints

end

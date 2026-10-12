/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.Sieve

-- The `#guard` examples run code of the imported modules at compile time.
meta import Ratpoints.Model.Sieve

/-!
# The denominators

The side of the denominators of the sieve, each component in its place in `find_points_work_1`: the
2-adic information, which says for each class of the denominators modulo 64 which numerators modulo
64 it admits (`Ratpoints.Sieve.twoAdic`), the word of a class being the pattern from which ratpoints
starts the first stage (the class word of `Ratpoints.Sieve.andRows`), and which classes admit a
numerator at all (`Ratpoints.Sieve.denBits`). Every class word lets every numerator of a point
through.

## Main definitions

* `Ratpoints.Sieve.squares64`: the squares modulo 64 as a word.
* `Ratpoints.Sieve.coeffsMod64`, `Ratpoints.Sieve.fsq`, `Ratpoints.Sieve.gsq`: the coefficients
  modulo 64 and the residues at which the polynomial and its reversal are squares modulo 64.
* `Ratpoints.Sieve.twoAdic`, `Ratpoints.Sieve.denBits`: the numerators modulo 64 that each class
  of the denominators admits, and the classes that admit one.
-/

@[expose] public section

namespace Ratpoints

namespace Sieve

/-! ### The 2-adic information -/

/-- The squares modulo 64 as a word, `RP_SQUARES64`: bit `s` is set exactly when `s` is a square
modulo 64, for the twelve residues `0, 1, 4, 9, 16, 17, 25, 33, 36, 41, 49, 57`.

C: `find_points.c:981` -/
def squares64 : UInt64 := 0x0202021202030213

/-- The coefficients modulo 64 of the polynomial of degree `d` with the coefficient list `c`, as the
binary form of the even degree `D = d + d % 2` reads them: the non-negative residue of `c_k` for
`k ≤ d`, and `0` for `k = D = d + 1` when `d` is odd.

C: `find_points.c:1002-1004`

Deviation: an array of `D + 1` words, for the array `cm` on the stack; the Euclidean `%` of the
integers, for `mpz_fdiv_ui`. -/
def coeffsMod64 (c : List Int) (d : Nat) : Array UInt64 :=
  (Array.range (d + d % 2 + 1)).map fun k ↦ if k ≤ d then (c.getD k 0 % 64).toNat.toUInt64 else 0

/-- The residues `k` modulo 64 at which the polynomial `f` with the coefficients `cm` modulo 64
(`Ratpoints.Sieve.coeffsMod64`) is a square modulo 64, as a word: bit `k` is set when `f(k) mod 64`
is a square modulo 64 (`Ratpoints.Sieve.squares64`), with `f(k)` by Horner's rule in the arithmetic
of `UInt64`, which is exact modulo `2 ^ 64` and so modulo 64.

C: `find_points.c:1006-1014`

Deviation: Horner's rule from `0`, where the C code starts from `cm[D]`, with the same value. -/
def fsq (cm : Array UInt64) : UInt64 :=
  Nat.fold 64 (fun k _ w ↦
    let s := cm.foldr (fun a s ↦ s * k.toUInt64 + a) 0
    if (squares64 >>> (s &&& 0x3f)) &&& 1 != 0 then w ||| 1 <<< k.toUInt64 else w) 0

/-- The even residues `t` modulo 64 at which the reversed polynomial
`frev(t) = c₀ t^D + c₁ t^(D - 1) + ⋯ + c_D` with the coefficients `cm` modulo 64
(`Ratpoints.Sieve.coeffsMod64`) is a square modulo 64, as a word: bit `t`, for even `t`, is set
when `frev(t) mod 64` is a square modulo 64 (`Ratpoints.Sieve.squares64`), by Horner's rule in the
arithmetic of `UInt64`; the bits of the odd `t` are clear.

C: `find_points.c:1015-1021`

Deviation: Horner's rule from `0`, where the C code starts from `cm[0]`, with the same value. -/
def gsq (cm : Array UInt64) : UInt64 :=
  Nat.fold 32 (fun i _ w ↦
    let t := 2 * i
    let s := cm.foldl (fun s a ↦ s * t.toUInt64 + a) 0
    if (squares64 >>> (s &&& 0x3f)) &&& 1 != 0 then w ||| 1 <<< t.toUInt64 else w) 0

/-- The 2-adic information of the polynomial of degree `d` with the coefficient list `c`: for each
residue `b` modulo 64 the word `nb[b]` of the numerators modulo 64 that the denominators `≡ b`
admit, bit `a` set exactly when `a` or `b` is odd and `F(a, b) mod 64` is a square modulo 64. The
words start at `0`; for each set bit `k` of the word of `f` (`Ratpoints.Sieve.fsq`), lowest first
(`Ratpoints.Sieve.ctz`), bit `k b mod 64` is set in the word of every odd `b`, and for each set bit
`t` of the word of the reversed polynomial (`Ratpoints.Sieve.gsq`), bit `a` in the word of
`t a mod 64` for every odd `a`. The word of the class of a denominator is the pattern from which
ratpoints starts the first stage, the class word of `Ratpoints.Sieve.andRows`, and a denominator
whose class has the word `0` carries no point (`Ratpoints.Sieve.denBits`).

C: `find_points.c:983-994`, `find_points.c:996-1000`, `find_points.c:1023-1050`,
`find_points.c:1106-1115`

Deviation: the words returned, for the classes `cls` and the word `den_bits` that `get_2adic_info`
fills, `den_bits` computed from the words (`Ratpoints.Sieve.denBits`); the stride 1 for every class,
`k = 0` and `a₀ = 0`, so that the pattern of a class is its word itself, for the packing of the
numerators of a class into the residues `a₀ mod 2^k` that hold all of its admissible numerators,
with its row offsets and its packed pattern (stage F); the lowest set bit by the loop of `RP_CTZL`
(`Ratpoints.Sieve.ctz`); remainders for the masks by `0x3f`; natural numbers for the `long`s `k`,
`b`, `t` and `a`; no output under `DEBUG`. -/
def twoAdic (c : List Int) (d : Nat) : Id (Vector UInt64 64) := do
  let cm := coeffsMod64 c d
  let mut nb : Vector UInt64 64 := Vector.replicate 64 0
  let mut w := fsq cm
  while w != 0 do
    let k ← ctz w
    w := w &&& (w - 1)
    for i in [0:32] do
      let b := 2 * i + 1
      nb := nb.set! b (nb[b]! ||| 1 <<< (k * b % 64).toUInt64)
  w := gsq cm
  while w != 0 do
    let t ← ctz w
    w := w &&& (w - 1)
    for i in [0:32] do
      let a := 2 * i + 1
      nb := nb.set! (t * a % 64) (nb[t * a % 64]! ||| 1 <<< a.toUInt64)
  return nb

/-- The classes of the denominators modulo 64 that admit a numerator, for the words `nb` of the
2-adic information (`Ratpoints.Sieve.twoAdic`): bit `b` is set exactly when `nb[b] ≠ 0`. A
denominator whose class has its bit clear carries no point; when no bit is set and there is no
point at infinity, the curve has no point at all, and ratpoints ends the search with none (the
2-adic exit, stage E).

C: `find_points.c:995`, `find_points.c:1064-1065`, `find_points.c:1070`,
`find_points.c:1096-1097`, `find_points.c:1102-1104`

Deviation: computed from the words apart, where `get_2adic_info` sets the bit in the loop that makes
the classes. -/
def denBits (nb : Vector UInt64 64) : UInt64 :=
  Nat.fold 64 (fun b h db ↦ if nb[b] != 0 then db ||| 1 <<< b.toUInt64 else db) 0

/-! ### Examples

The words of the 2-adic information against those that a build of ratpoints at the pinned commit
prints with a dump of the side of the denominators on the standard error (the words `fsq`, `gsq`
and `nb` of `get_2adic_info`, and `den_bits`), and against their rule. -/

-- The squares modulo 64.
#guard (List.range 64).all fun s ↦
  squares64.toBitVec.getLsbD s == (List.range 64).any fun x ↦ x * x % 64 == s

-- The coefficients modulo 64, with the coefficient `c_D = 0` for odd degree.
#guard coeffsMod64 [1, 2] 1 == #[1, 2, 0] && coeffsMod64 [-2, 0, 0, 1] 3 == #[62, 0, 0, 1, 0] &&
  coeffsMod64 [6, -3, 5, 2, 75] 4 == #[6, 61, 5, 2, 11]

-- `fsq`, `gsq` and `den_bits` of the dump for `1 2`, `-2 0 0 1`, `1 0 126 0 441`, `6 -3 5 2 75`,
-- `3 0 3` (no class admits a numerator) and `2 0 0 0 0 0 0 0 1`.
#guard ([([1, 2], 1, 0x1111111111111111, 0x4040010140400101, 0xefeeefefefeeefef),
    ([-2, 0, 0, 1], 3, 0x0808080808080808, 0x0000001000010011, 0xbabbbabababbbabb),
    ([1, 0, 126, 0, 441], 4, 0x5555555555555555, 0x5555555555555555, 0xffffffffffffffff),
    ([6, -3, 5, 2, 75], 4, 0x6024202020246020, 0, 0xaaaaaaaaaaaaaaaa),
    ([3, 0, 3], 2, 0, 0, 0),
    ([2, 0, 0, 0, 0, 0, 0, 0, 1], 8, 0, 0x5555555555555555, 0x5555555555555555)] :
      List (List Int × Nat × UInt64 × UInt64 × UInt64)).all fun (c, d, f, g, db) ↦
  fsq (coeffsMod64 c d) == f && gsq (coeffsMod64 c d) == g && denBits (Id.run (twoAdic c d)) == db

-- The words `nb` of the dump for `1 2 3 4 5 6 7`: `0xdddddddddddddddd` for `b ≡ 1 (mod 4)`,
-- `0x7777777777777777` for `b ≡ 3 (mod 4)`, `0` for even `b`.
#guard (Id.run (twoAdic [1, 2, 3, 4, 5, 6, 7] 6)).toList == (List.range 64).map fun b ↦
  if b % 4 = 1 then 0xdddddddddddddddd else if b % 4 = 3 then 0x7777777777777777 else 0

-- The words against their rule: bit `a` of `nb[b]` is set exactly when `a` or `b` is odd and the
-- binary form `F(a, b)` (by Horner's rule, with the factor `b` for odd degree) is a square modulo
-- 64, over all residues, for curves of degree 3, 4 and 6.
#guard ([([-2, 0, 0, 1], 3), ([1, 0, 126, 0, 441], 4), ([6, -3, 5, 2, 75], 4),
    ([3, -7, 0, 11, 5, -1, 2], 6)] : List (List Int × Nat)).all fun (c, d) ↦
  let nb := Id.run (twoAdic c d)
  (List.range 64).all fun b ↦ (List.range 64).all fun a ↦
    let F := BruteForce.horner (BruteForce.scaledCoeffs c d b) a * (if d % 2 = 1 then b else 1)
    nb[b]!.toBitVec.getLsbD a ==
      ((a % 2 == 1 || b % 2 == 1) && (List.range 64).any fun x ↦ (x * x : Int) % 64 == F % 64)

end Sieve

end Ratpoints

end

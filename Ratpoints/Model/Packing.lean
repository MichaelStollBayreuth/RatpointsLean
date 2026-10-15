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
# The packing of the numerators

The packing of the numerators of the denominators of each class modulo 64 into one class modulo a
power of 2, as `get_2adic_info` makes it: for each class of the denominators modulo 64, with the
word of the numerators modulo 64 that it admits in the 2-adic information
(`Ratpoints.Sieve.twoAdic`), the largest stride `2 ^ k`, `k ≤ 6` and `k < Ratpoints.numStrides`, for
which these numerators lie in one class `a₀ mod 2 ^ k`, and the pattern of the word in that packing,
the starting value of the first stage of the sieve in the packing (stage F), with the word
`den_bits` of the classes that admit a numerator (`Ratpoints.Sieve.numClasses`,
`Ratpoints.Sieve.packPattern`). The classes (`Ratpoints.Sieve.NumClass`) are in
`Ratpoints.Model.Sieve`, the 2-adic information in `Ratpoints.Model.Denominators`; the row offsets
of the packings and the residues of a denominator divided by the stride of its class come with the
packing (stage F).

## Main definitions

* `Ratpoints.Sieve.classMasks`, `Ratpoints.Sieve.packPattern`, `Ratpoints.Sieve.numClasses`: the
  packings of the classes, their strides, residues and patterns.
-/

@[expose] public section

namespace Ratpoints

namespace Sieve

/-! ### The classes -/

/-- The masks of the strides: bit `a < 64` of mask `k` is set exactly when `2 ^ k ∣ a`, for the
seven strides `2 ^ k`, `k ≤ 6`, up to the modulus 64 of the 2-adic information; a mask of a larger
`k` is read as `0`, which ends the loop over the strides of `Ratpoints.Sieve.numClasses` at `k = 7`
at the latest, so that its stride exponent is at most 6 whatever `Ratpoints.numStrides` is.

C: `find_points.c:1058-1062`

Deviation: an array of `UInt64`, for the array of `RP_NUM_STRIDES` `unsigned long`s, which the C
code initializes with these seven words and zeros beyond them, and an array read with the default
`0` beyond its seven entries. -/
def classMasks : Array UInt64 :=
  #[~~~0, 0x5555555555555555, 0x1111111111111111, 0x0101010101010101, 0x0001000100010001,
    0x0000000100000001, 0x0000000000000001]

/-- The pattern of the word `w` of the admissible numerators modulo 64 of a class in the packing of
the stride `2 ^ k`, `1 ≤ k ≤ 6`, and the residue `a₀ < 2 ^ k` of all of its set bits: each set bit
`a` of `w`, lowest first (`Ratpoints.Sieve.ctz`), at the place `((a - a₀) mod 64) / 2 ^ k`, below
`64 / 2 ^ k`; then the word doubled from that period up to 64 bits, `packed ||| packed <<< s` for
`s = 64 / 2 ^ k, …, 32`. Bit `t` of the result is bit `(a₀ + 2 ^ k t) mod 64` of `w`.

C: `find_points.c:1082-1094`

Deviation: a function of its own for the two loops of the packed pattern, which the loop over the
classes of `get_2adic_info` calls for `k ≥ 1` (`Ratpoints.Sieve.numClasses`), as the loop of the
binary algorithm of `relprime` is one (`Ratpoints.Sieve.relprimeOdd`); natural numbers for the
`long`s `a`, `a0`, `t` and the shift `a` of the doubling, `s` here: the difference `a - a₀` of
natural numbers, which `a ≥ a₀` makes the difference of the C code, the remainder by 64 for the
mask by `0x3f`, the same on a non-negative value, and the division by `2 ^ k` for the shift by `k`;
the lowest set bit by the loop of `RP_CTZL` (`Ratpoints.Sieve.ctz`). -/
def packPattern (w : UInt64) (k a0 : Nat) : Id UInt64 := do
  let mut packed : UInt64 := 0
  let mut x := w
  while x != 0 do
    let a ← ctz x
    x := x &&& (x - 1)
    packed := packed ||| 1 <<< ((a - a0) % 64 / 2 ^ k).toUInt64
  let mut s := 64 / 2 ^ k
  while s < 64 do
    packed := packed ||| packed <<< s.toUInt64
    s := 2 * s
  return packed

/-- The packings of the 64 classes of the denominators modulo 64 (`Ratpoints.Sieve.NumClass`) and
the word `den_bits` of the classes that admit a numerator, from the words `nb` of the 2-adic
information (`Ratpoints.Sieve.twoAdic`), as `get_2adic_info` makes them: for each class `b`, with
the word `w = nb[b]`, for `w = 0` the stride 1 (`k = 0`), the residue `a₀ = 0` and the pattern `0`;
otherwise, for the lowest set bit `a` of `w` (`Ratpoints.Sieve.ctz`), the stride exponent `k` the
largest below `Ratpoints.numStrides` and at most 6 for which every set bit of `w` is
`≡ a (mod 2 ^ k)`, found upwards from `1` with the masks of `Ratpoints.Sieve.classMasks` until the
first `k` at which a set bit lies off the mask shifted by `a mod 2 ^ k`, then less one;
`a₀ = a mod 2 ^ k`; the pattern `w` itself for `k = 0` and otherwise the packed pattern
(`Ratpoints.Sieve.packPattern`); and bit `b` set in `den_bits`. No class has row offsets yet. The
word `den_bits` is that of `Ratpoints.Sieve.denBits`.

C: `find_points.c:995`, `find_points.c:1064-1081`, `find_points.c:1095-1097`,
`find_points.c:1099-1104`, `find_points.c:1106-1114`

Deviation: the classes and `den_bits` returned, for the array `cls` and the word `den_bits` that
`get_2adic_info` fills through its pointer arguments, from the words that `Ratpoints.Sieve.twoAdic`
returns; the packed pattern of a class with `k ≥ 1` by a function of its own
(`Ratpoints.Sieve.packPattern`); the pattern of a class as one word, for the vector `RBA(packed)` of
line 1098; natural numbers for the `long`s `k`, `a0` and `a`, and the remainder by `2 ^ k` for the
mask `(1L << k) - 1`; the mask of a stride read from the array of the masks with the default `0`
beyond its seven entries, as the C code reads the zeros that it puts beyond them; the lowest set bit
by the loop of `RP_CTZL` (`Ratpoints.Sieve.ctz`); no output under `DEBUG`. -/
def numClasses (nb : Vector UInt64 64) : Id (Vector NumClass 64 × UInt64) := do
  let mut cls : Vector NumClass 64 := .replicate 64 default
  let mut db : UInt64 := 0
  for h : b in [0:64] do
    let w := nb[b]
    let mut packed : UInt64 := 0
    let mut a0 := 0
    let mut k := 0
    if w != 0 then
      let a ← ctz w
      k := 1
      while k < numStrides do
        if w &&& ~~~(classMasks[k]! <<< (a % 2 ^ k).toUInt64) != 0 then break
        k := k + 1
      k := k - 1
      a0 := a % 2 ^ k
      packed ← if k = 0 then pure w else packPattern w k a0
      db := db ||| 1 <<< b.toUInt64
    cls := cls.set b ⟨packed, k, a0, none⟩
  return (cls, db)

/-! ### Examples

The packings of the classes against those of the loop over the classes of `get_2adic_info`, and
the patterns against their rule. -/

-- The packings of 64 words against those that the loop over the classes of `get_2adic_info`
-- (`find_points.c:1058-1095`, compiled apart at the pinned commit) gives for them: the pattern,
-- the stride exponent `k` and the residue `a₀`, for every `k = 0, …, 6`; no class has row offsets
-- yet, and the word of the classes that admit a numerator has bit `b` set exactly when `nb[b] ≠ 0`,
-- as `Ratpoints.Sieve.denBits` has.
#guard
  let ref : List (UInt64 × UInt64 × Nat × Nat) := [
    (0x0, 0x0, 0, 0), (0xffffffffffffffff, 0xffffffffffffffff, 0, 0), (0x0, 0x0, 0, 0),
    (0x0, 0x0, 0, 0), (0x32b5277ffeed3bdc, 0x32b5277ffeed3bdc, 0, 0),
    (0x5f3f40d5e7b1cfed, 0x5f3f40d5e7b1cfed, 0, 0), (0x0, 0x0, 0, 0), (0x0, 0x0, 0, 0),
    (0xe103486d9d8df5f3, 0xe103486d9d8df5f3, 0, 0), (0xddf6d20ddaf6a2d3, 0xddf6d20ddaf6a2d3, 0, 0),
    (0x4104551105151551, 0x92f5377d92f5377d, 1, 0), (0x5055151545450515, 0xcf77bb37cf77bb37, 1, 0),
    (0x8808a8a80aa2aa22, 0xa2ee3df5a2ee3df5, 1, 1), (0x8a88a08a000aa2aa, 0xbacb03dfbacb03df, 1, 1),
    (0x20000800000000, 0x402000004020000, 1, 1), (0x20000020a02, 0x10013100100131, 1, 1),
    (0x2a088888a080a888, 0x72aac8ea72aac8ea, 1, 1), (0x4545014150555010, 0xbb19cfc4bb19cfc4, 1, 0),
    (0x5411155545445115, 0xe57fbad7e57fbad7, 1, 0), (0x202020200002202, 0x550d550d550d550d, 2, 1),
    (0x110101000110101, 0x6a356a356a356a35, 2, 0), (0x2002002022022022, 0x92db92db92db92db, 2, 1),
    (0x10111110011111, 0x2f9f2f9f2f9f2f9f, 2, 0), (0x888808088888880, 0x7afe7afe7afe7afe, 2, 3),
    (0x440000440440040, 0x61b261b261b261b2, 2, 2), (0x101101011011111, 0x5adf5adf5adf5adf, 2, 0),
    (0x8800888808888088, 0xcf7bcf7bcf7bcf7b, 2, 3), (0x2020222220000220, 0xaf86af86af86af86, 2, 1),
    (0x200000200020200, 0x9696969696969696, 3, 1), (0x20002020000000, 0x5858585858585858, 3, 5),
    (0x200000002020202, 0x8f8f8f8f8f8f8f8f, 3, 1), (0x1010101000000010, 0xf1f1f1f1f1f1f1f1, 3, 4),
    (0x1010001000100000, 0xd4d4d4d4d4d4d4d4, 3, 4), (0x404000004000400, 0xcacacacacacacaca, 3, 2),
    (0x8000008080808080, 0x9f9f9f9f9f9f9f9f, 3, 7), (0x8080800000008000, 0xe2e2e2e2e2e2e2e2, 3, 7),
    (0x1010101010101, 0x7f7f7f7f7f7f7f7f, 3, 0), (0x1000100010, 0x7777777777777777, 4, 4),
    (0x40004000400000, 0xeeeeeeeeeeeeeeee, 4, 6), (0x100000001000100, 0xbbbbbbbbbbbbbbbb, 4, 8),
    (0x800080008000000, 0xeeeeeeeeeeeeeeee, 4, 11), (0x200020000000200, 0xdddddddddddddddd, 4, 9),
    (0x4000400040004, 0xffffffffffffffff, 4, 2), (0x1000100010001, 0xffffffffffffffff, 4, 0),
    (0x40000000400040, 0xbbbbbbbbbbbbbbbb, 4, 6), (0x8000800000000000, 0xcccccccccccccccc, 4, 15),
    (0x400000004000000, 0xffffffffffffffff, 5, 26), (0x100000001000000, 0xffffffffffffffff, 5, 24),
    (0x400000004000000, 0xffffffffffffffff, 5, 26), (0x2000000020000, 0xffffffffffffffff, 5, 17),
    (0x800000008, 0xffffffffffffffff, 5, 3), (0x2000000020, 0xffffffffffffffff, 5, 5),
    (0x400000004000, 0xffffffffffffffff, 5, 14), (0x4000000040000, 0xffffffffffffffff, 5, 18),
    (0x200000002000000, 0xffffffffffffffff, 5, 25), (0x1, 0xffffffffffffffff, 6, 0),
    (0x8000000000000000, 0xffffffffffffffff, 6, 63), (0x100000000000000, 0xffffffffffffffff, 6, 56),
    (0x8000000000000, 0xffffffffffffffff, 6, 51), (0x1000000000000000, 0xffffffffffffffff, 6, 60),
    (0x2000000000, 0xffffffffffffffff, 6, 37), (0x100000, 0xffffffffffffffff, 6, 20),
    (0x8000000000000000, 0xffffffffffffffff, 6, 63), (0x200000000000000, 0xffffffffffffffff, 6, 57)]
  let nb : Vector UInt64 64 := .ofFn fun b ↦ (ref.getD b.val (0, 0, 0, 0)).1
  let (cls, db) := Id.run (numClasses nb)
  (List.range 64).all fun b ↦ db.toBitVec.getLsbD b == (nb[b]! != 0) &&
    let (_, pk, k, a0) := ref.getD b (0, 0, 0, 0)
    cls[b]!.bits == pk && cls[b]!.k == k && cls[b]!.a0 == a0 && cls[b]!.offset == none

-- The pattern of a class: each set bit `a` of the word at `(a - a₀) / 2 ^ k`, then doubled, for
-- words whose set bits lie in one class modulo `2 ^ k`, against its rule, bit `t` the bit
-- `(a₀ + 2 ^ k t) mod 64` of the word.
#guard (List.range' 1 6).all fun k ↦ (List.range (2 ^ k)).all fun a0 ↦
  ([~~~0, 0x0123456789abcdef, 0x8000000000000001, 0xf0f0f0f0f0f0f0f0] : List UInt64).all fun x ↦
    let w := (List.range 64).foldl (fun w a ↦
      if a % 2 ^ k = a0 && x.toBitVec.getLsbD a then w ||| 1 <<< a.toUInt64 else w) 0
    let pk := Id.run (packPattern w k a0)
    (List.range 64).all fun t ↦
      pk.toBitVec.getLsbD t == w.toBitVec.getLsbD ((a0 + 2 ^ k * t) % 64)

end Sieve

end Ratpoints

end

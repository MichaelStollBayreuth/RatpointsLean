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
power of 2, as `get_2adic_info` and `class_offsets` make it: for each class of the denominators
modulo 64, with the word of the numerators modulo 64 that it admits in the 2-adic information
(`Ratpoints.Sieve.twoAdic`), the largest stride `2 ^ k`, `k ≤ 6` and `k < Ratpoints.numStrides`, for
which these numerators lie in one class `a₀ mod 2 ^ k`, and the pattern of the word in that packing,
from which the first stage of the sieve starts (`Ratpoints.Sieve.andRows`), with the word
`den_bits` of the classes that admit a numerator (`Ratpoints.Sieve.numClasses`,
`Ratpoints.Sieve.packPattern`); and, once the moduli are known, the number of the distinct packings
(`Ratpoints.Sieve.numPackings`), and the inverses of the strides modulo the moduli with the row
offsets of each packing, one for each modulus, which shift the rows so that bit `t` of the bit array
with the word number `w` stands for the numerator `a₀ + 2 ^ k (Ratpoints.rbaLength w + t)`
(`Ratpoints.Sieve.classOffsets`); and for a denominator the residues of the denominator divided by
the stride of its class modulo the moduli of the first two stages, as `fill_bp_list` computes them
(`Ratpoints.Sieve.fillBpList`). The classes (`Ratpoints.Sieve.NumClass`) and the sieve of one
denominator in the packing of its class are in `Ratpoints.Model.Sieve`, the 2-adic information and
the run, which reads the row offsets and the residues, in `Ratpoints.Model.Denominators`.

## Main definitions

* `Ratpoints.Sieve.classMasks`, `Ratpoints.Sieve.packPattern`, `Ratpoints.Sieve.numClasses`: the
  packings of the classes, their strides, residues and patterns.
* `Ratpoints.Sieve.numPackings`, `Ratpoints.Sieve.halve`, `Ratpoints.Sieve.classRows`,
  `Ratpoints.Sieve.classOffsets`: the number of the packings, and the row offsets of the packings
  with the inverses of the strides.
* `Ratpoints.Sieve.fillBpList`: the residues of a denominator divided by the stride of its class.
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
(`Ratpoints.Sieve.packPattern`); and bit `b` set in `den_bits`. No class has row offsets yet
(`Ratpoints.Sieve.classOffsets`). The word `den_bits` is that of `Ratpoints.Sieve.denBits`.

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

/-! ### The row offsets -/

/-- The number of the distinct packings `(k, a₀)` of the classes `cls` with a pattern
(`Ratpoints.Sieve.NumClass`), at least 1: the number of the rows of offsets that
`Ratpoints.Sieve.classOffsets` makes, which sizes the array of the offsets of the run
(`Ratpoints.searchPoints`). The packings are told apart by the key `2 ^ k + a₀`, below
`2 ^ Ratpoints.numStrides` and 128, marked in two words.

C: `find_points.c:1119-1130`

Deviation: an array of two words, for the array `seen` of two `unsigned long`s; natural numbers for
the `long`s `key` and `n`, the division by 64 and the remainder by 64 for the shift by 6 and the
mask by 63 of the key; a natural number for the `long` result. -/
def numPackings (cls : Vector NumClass 64) : Id Nat := do
  let mut seen : Array UInt64 := #[0, 0]
  let mut n := 0
  for h : b in [0:64] do
    let key := 2 ^ cls[b].k + cls[b].a0
    if cls[b].bits != 0 && seen[key / 64]! >>> (key % 64).toUInt64 &&& 1 == 0 then
      seen := seen.set! (key / 64) (seen[key / 64]! ||| 1 <<< (key % 64).toUInt64)
      n := n + 1
  return if n > 0 then n else 1

/-- Half of `x` modulo the odd modulus `p`: `x / 2` for even `x` and `(x + p) / 2` for odd `x`, the
step of the chains of halvings of `class_offsets` (`Ratpoints.Sieve.classOffsets`): for `x < p` it
is below `p`, and twice it is `x` modulo `p`.

C: `find_points.c:1159-1160`

Deviation: a function of its own for the expression that the C code writes out for `d` and for `e`;
the remainder by 2 for the mask `& 1` and the division by 2 for the shift `>> 1`; natural numbers
for the `long`s. -/
def halve (x p : Nat) : Nat := if x % 2 = 1 then (x + p) / 2 else x / 2

/-- The rows of offsets of the classes `cls` with a pattern, for the sieve entries `es` of the `np`
moduli of the run and the inverses `rinv[n][k] = (2 ^ k Ratpoints.rbaLength)⁻¹ mod p` of the `n`-th
modulus `p`, written into the array `offsets` of the run: for each class with a pattern, of the
stride `2 ^ k` and the residue `a₀`, with the key `2 ^ k + a₀`, the row of an earlier class with the
same key if there is one, and otherwise a new row of `np` offsets after the rows made so far, at the
position `rows np`, the `n`-th the remainder of `a₀ rinv[n][k]` by a multiplication with the
reciprocal of `p` (`Ratpoints.Sieve.mulMod`, exact since `a₀ rinv[n][k] p < 2 ^ 64`) plus the bias
of `p`; the class gets the position of its row.

C: `find_points.c:1164-1182`

Deviation: a function of its own for the loop over the classes of `class_offsets`
(`Ratpoints.Sieve.classOffsets`); the classes and the array of the offsets returned, for the array
of the classes and the array of the offsets that `class_offsets` writes through its pointer
arguments; the table of the rows by their keys an array of options of positions, for the array
`row_of` of `2 ^ RP_NUM_STRIDES` pointers into the offsets, none for `NULL`, and the row of a class
its position in the array of the offsets, for the pointer `row`; the inverses `rinv` an array of
arrays, for the array of `RP_NUM_STRIDES` `long`s for each modulus on the stack; natural numbers for
the `long`s, the product `a₀ rinv[n][k]` a natural number for the `long` that `RP_MULMOD` converts
to an `unsigned long`, below `2 ^ 63` (`Ratpoints.mul_lt_two_pow_63`); the reciprocal and the bias
read from the sieve entry, as the C code reads them. -/
def classRows (cls : Vector NumClass 64) (es : Array SieveEntry) (rinv : Array (Array Nat))
    (np : Nat) (offsets : Array Nat) : Id (Vector NumClass 64 × Array Nat) := do
  let mut cls := cls
  let mut offsets := offsets
  let mut rowOf : Array (Option Nat) := .replicate (2 ^ numStrides) none
  let mut rows := 0
  for h : b in [0:64] do
    let cl := cls[b]
    let key := 2 ^ cl.k + cl.a0
    if cl.bits == 0 then continue
    if let some row := rowOf[key]! then cls := cls.set b { cl with offset := some row }
    else
      let row := rows * np
      for n in [0:np] do
        let e := es[n]!
        offsets := offsets.set! (row + n) (mulMod (cl.a0 * rinv[n]![cl.k]!) e.p e.magic + e.bias)
      cls := cls.set b { cl with offset := some row }
      rowOf := rowOf.set! key (some row)
      rows := rows + 1
  return (cls, offsets)

/-- The row offsets of the classes `cls`, once the moduli of the run, with their sieve entries `es`,
are known, as `class_offsets` makes them: the largest stride exponent `kmax` among the classes with
a pattern; for each modulus `p`, the chains of halvings modulo `p` (`Ratpoints.Sieve.halve`) from
`1` and from the inverse `rbainv` of `Ratpoints.rbaLength` modulo `p`, for `k = 0, …, kmax`, which
give the inverses `2 ^ (-k) mod p`, which the sieve entry of `p` keeps for `fill_bp_list`
(`Ratpoints.Sieve.SieveEntry.dinv`, `Ratpoints.Sieve.fillBpList`), and the inverses
`(2 ^ k Ratpoints.rbaLength)⁻¹ mod p`; and the rows of offsets of the classes, written into the
array `offsets` of the run, of `Ratpoints.Sieve.numPackings cls` rows of one offset for each modulus
(`Ratpoints.Sieve.classRows`): the offset of a class of the stride `2 ^ k` and the residue `a₀` for
`p` is `a₀ (2 ^ k Ratpoints.rbaLength)⁻¹ mod p` plus the bias of `p`. The classes and the entries
return with their offsets and their inverses, and the array of the offsets filled.

C: `find_points.c:1142-1158`, `find_points.c:1161-1162`, `find_points.c:1183`

Deviation: the classes, the entries and the array of the offsets returned, for the arrays that
`class_offsets` writes through its pointer arguments; the number `np` of the moduli the number of
the sieve entries `es`, for the run those of its three stages (`Ratpoints.searchPoints`), where
`find_points_work_1` passes `sp3_max`, the number with the reserve of further primes that the
correction of the moduli may take into the second stage during the run (stage I); the inverses of
`2 ^ k` an array of `kmax + 1` entries, for the array `dinv` of `RP_NUM_STRIDES` `long`s of the
sieve entry, whose entries beyond `kmax` stay unset and unread; the inverses `rinv` an array of
arrays, for the array on the stack; the loop over the classes by a function of its own
(`Ratpoints.Sieve.classRows`); natural numbers for the `long`s. -/
def classOffsets (cls : Vector NumClass 64) (es : List SieveEntry) (offsets : Array Nat) :
    Id (Vector NumClass 64 × List SieveEntry × Array Nat) := do
  let mut kmax := 0
  for h : b in [0:64] do
    if cls[b].bits != 0 && kmax < cls[b].k then kmax := cls[b].k
  let mut es' : Array SieveEntry := #[]
  let mut rinv : Array (Array Nat) := #[]
  for e in es do
    let mut d := 1
    let mut x := e.rbainv
    let mut dinv := #[]
    let mut ri := #[]
    for _ in [0:kmax + 1] do
      dinv := dinv.push d
      ri := ri.push x
      d := halve d e.p
      x := halve x e.p
    es' := es'.push { e with dinv }
    rinv := rinv.push ri
  let (cls, offsets) ← classRows cls es' rinv es.length offsets
  return (cls, es'.toList, offsets)

/-! ### The residues of a denominator -/

/-- The residues of the denominator `b` divided by the stride `2 ^ k` of its class modulo the moduli
of the sieve entries `es` of the first two stages, `b dinv[k] mod p` for the inverse `dinv[k]` of
`2 ^ k` modulo the modulus `p` (`Ratpoints.Sieve.SieveEntry.dinv`), each by multiplications with the
reciprocal `mg` of `p` from `mgs` (`Ratpoints.Sieve.mulMod`), exact below `2 ^ 64 / p`: for
`b ≤ Ratpoints.mulModLimit / Ratpoints.maxPrimeEven`, the product `b dinv[k]` reduced at once; for
`b ≤ Ratpoints.mulModLimit`, `b` reduced first and then its product with `dinv[k]`; and beyond, `b`
reduced by the helper `mod` of the C code (`Ratpoints.Sieve.modLong`), which divides, and then the
product. The branch is chosen once for `b`. The sieve of the denominator reads the rows of these
residues (`Ratpoints.Sieve.setRows`).

C: `find_points.c:3639-3679`

Deviation: a list, made by a map over the entries and their reciprocals (`List.zipWith`) in the
branch that `b` chooses and returned, for the array `bp_list` that the loops over the positions
`0, …, sp2 - 1` of `sieve_list` and `magics` fill through the pointer argument; the entries of the
first two stages and their reciprocals as arguments, for `wk->sp2` and the arrays `sieve_list` and
`magics` of the arguments; natural numbers for the `long`s, the products natural numbers for the
`long`s that `RP_MULMOD` converts to `unsigned long`s, at most `Ratpoints.mulModLimit` in the first
branch (`Ratpoints.mul_le_mulModLimit_of_le_div`) and below `2 ^ 63` in the others
(`Ratpoints.mul_lt_two_pow_63`); no measurement of its time (`RP_BP_TIC`, `RP_BP_TOC`). -/
def fillBpList (b k : Nat) (es : List SieveEntry) (mgs : List Nat) : List Nat :=
  if b ≤ mulModLimit / maxPrimeEven then
    List.zipWith (fun e mg ↦ mulMod (b * e.dinv[k]!) e.p mg) es mgs
  else if b ≤ mulModLimit then
    List.zipWith (fun e mg ↦ mulMod (mulMod b e.p mg * e.dinv[k]!) e.p mg) es mgs
  else List.zipWith (fun e mg ↦ mulMod ((modLong b e.p).toNat * e.dinv[k]!) e.p mg) es mgs

/-! ### Examples

The packings of the classes against those of the loop over the classes of `get_2adic_info`, and the
patterns and the residues of `fill_bp_list` against their rules; the row offsets, which need the
sieve entries of the moduli, and the sieve of one denominator in the packing of its class are
examples of `Ratpoints.Model.FindPoints`. -/

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

-- The residues of `fill_bp_list` in its three branches, for the denominators up to and above
-- `mulModLimit / maxPrimeEven` and `mulModLimit` and up to the largest `long`, and the strides
-- `2 ^ k`, `k ≤ 6`, with the inverses of the strides that the halvings of `class_offsets` give:
-- `b 2 ^ (-k) mod p`, which times `2 ^ k` is `b` modulo `p`, for primes of the table and composite
-- moduli up to 255.
#guard
  let es : List SieveEntry := ([3, 5, 7, 9, 15, 45, 77, 251, 255] : List Nat).map fun p ↦
    ⟨p, [], magic p, 0, 0, (Array.range 7).map fun k ↦ (List.range k).foldl (fun x _ ↦ halve x p) 1⟩
  ([1, 2, 1000, mulModLimit / maxPrimeEven, mulModLimit / maxPrimeEven + 1, mulModLimit - 1,
      mulModLimit, mulModLimit + 1, 10 ^ 12, 2 ^ 62 + 3, 2 ^ 63 - 1] : List Nat).all fun b ↦
    (List.range 7).all fun k ↦
      let bp := fillBpList b k es (es.map (·.magic))
      bp == es.map (fun e ↦ b * e.dinv[k]! % e.p) &&
        (bp.zip es).all fun (r, e) ↦ 2 ^ k * r % e.p == b % e.p && e.dinv[k]! * 2 ^ k % e.p == 1

end Sieve

end Ratpoints

end

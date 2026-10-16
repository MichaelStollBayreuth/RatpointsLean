/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

/-!
# Lemmas on 64-bit words for the contracts

Lemmas on the 64-bit words, unsigned and signed, that the contracts of the model need and Lean core
lacks, under their names in the namespaces of Lean core: two words with the same bits, the bits of
the word `~~~0` and of the masks `~~~0 <<< n` and `~~~0 >>> n`, the lowest bit and the lowest set
bit of a word, the word `x &&& (x - 1)`, which is `x` with its lowest set bit cleared, the bits of a
word set one at a time, at their own positions or at others, the bits of a word and of a Boolean
shifted by an amount below 64, the 64 bits of two words from a position within the first, the bits
of a word and-ed in turn with the words of a list, the odd part of a number below `2 ^ 64` by the
lowest set bit of its word, the halves of a word, and, for the signed 64-bit words, the arithmetic
shift, the mask `x >>> 63` with the smaller and the distance of two non-negative words that it gives
without a branch, the odd part of a positive word by the lowest set bit of the word read as
unsigned, its lowest bit, the absolute value, and the words of an integer and of a natural number
below `2 ^ 63`. For the classes of the packing: the bits of a word and-ed with the complement of a
mask. For the classes of the packing and the rows of a prime: the bits of a word or-ed with itself
shifted, `x ||| x <<< s`, which doubles a pattern of period `P ∣ s`. For the rows of offsets: the
bit `(x >>> j) &&& 1` of a word, and the 128 bits of two words after one bit is set. For the bits of
an interval: the sums, differences and negations of `long`s that do not overflow, the mask
`(1 <<< k) - 1` and the and with it, the Euclidean remainder modulo `2 ^ k` also of a negative
`long`. The lemmas on vectors, arrays, lists, ranges, natural numbers and integers are in
`Ratpoints.Proof.Containers`.

## Main statements

* `UInt64.eq_of_getLsbD_eq`: two words are equal when their bits are.
* `UInt64.getLsbD_allOnes_shiftLeft`, `UInt64.getLsbD_allOnes_shiftRight`: the bits of the masks.
* `UInt64.getLsbD_and_sub_one`, `UInt64.toNat_and_sub_one_lt`: for `x ≠ 0`, `x &&& (x - 1)` is `x`
  with its lowest set bit cleared, and smaller than `x`.
* `UInt64.getLsbD_fold_or_one_shiftLeft`, `UInt64.getLsbD_fold_or_one_shiftLeft_comp`: the bits of
  a word set one at a time, at their own positions or at the positions that a function gives.
* `UInt64.getLsbD_shiftRight_or_shiftLeft`: the 64 bits from position `r` on of the 128 bits of two
  words, for `0 < r < 64`.
* `UInt64.getLsbD_shiftLeft_ofNat`, `UInt64.getLsbD_shiftRight_ofNat`,
  `UInt64.getLsbD_toUInt64_shiftLeft`: the bits of a word and of a Boolean shifted by an amount
  below 64.
* `UInt64.getLsbD_foldl_and`: the bits of a word and-ed in turn with the words of a list.
* `UInt64.two_pow_ctz_mul_shiftRight_ofNat`, `UInt64.shiftRight_ctz_ofNat_mod_two`: a number
  `0 < b < 2 ^ 64` is `2 ^ t` times the odd number `b >>> t`, for the position `t` of the lowest
  set bit of the word `b`.
* `Int64.toInt_shiftRight_ofNat`, `Int64.shiftRight_63`: the arithmetic shift of a `long` by
  `k < 64`, and the mask `x >>> 63`, `-1` for a negative `x` and `0` otherwise.
* `Int64.toNatClampNeg_add_and_shiftRight_63`, `Int64.toNatClampNeg_xor_shiftRight_63_sub`: for
  `d = m - n`, `n + (d &&& d >>> 63)` and `(d ^^^ d >>> 63) - d >>> 63` are the smaller and the
  distance of two non-negative `long`s.
* `Int64.two_pow_ctz_mul_toNatClampNeg_shiftRight`, `Int64.toNatClampNeg_shiftRight_ctz_mod_two`: a
  positive `long` `x` is `2 ^ t` times the odd number `x >>> t`, for the position `t` of the lowest
  set bit of the word `x` read as unsigned.
* `Int64.toNatClampNeg_ite_neg`: the absolute value of a `long` other than `-2 ^ 63`.
* `Int64.minValue_lt_ofInt`, `Int64.ofNat_pos`: the word of an integer `|a| < 2 ^ 63` is not
  `-2 ^ 63`, and that of a natural number `0 < n < 2 ^ 63` is positive.
* `Int64.toInt_add_of_lt`, `Int64.toInt_sub_of_lt`, `Int64.toInt_neg_of_lt`: the sums, differences
  and negations of `long`s that do not overflow.
* `Int64.toInt_and_ofNat_two_pow_sub_one`: a `long` and-ed with the mask `2 ^ k - 1` is its
  Euclidean remainder modulo `2 ^ k`.

## Implementation notes

The file uses Lean core only, so that the `grind` calls of the proofs see only the lemmas of core,
untouched by the updates of Mathlib.
-/

@[expose] public section

universe u

/-! ### Words -/

namespace UInt64

theorem getLsbD_allOnes (t : Nat) : (~~~0 : UInt64).toBitVec.getLsbD t = decide (t < 64) := by
  simp only [UInt64.toBitVec_not, UInt64.toBitVec_zero, BitVec.not_zero, BitVec.getLsbD_allOnes]

theorem getLsbD_allOnes_shiftLeft (n : UInt64) (t : Nat) :
    ((~~~0 : UInt64) <<< n).toBitVec.getLsbD t =
      (decide (t < 64) && decide (n.toNat % 64 ≤ t)) := by
  simp only [UInt64.toBitVec_shiftLeft, UInt64.toBitVec_not, UInt64.toBitVec_zero, BitVec.not_zero,
    BitVec.shiftLeft_eq', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_allOnes, BitVec.toNat_umod,
    UInt64.toNat_toBitVec, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat]
  grind

theorem getLsbD_allOnes_shiftRight (n : UInt64) (t : Nat) :
    ((~~~0 : UInt64) >>> n).toBitVec.getLsbD t = decide (n.toNat % 64 + t < 64) := by
  simp only [UInt64.toBitVec_shiftRight, UInt64.toBitVec_not, UInt64.toBitVec_zero, BitVec.not_zero,
    BitVec.ushiftRight_eq', BitVec.getLsbD_ushiftRight, BitVec.getLsbD_allOnes, BitVec.toNat_umod,
    UInt64.toNat_toBitVec, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat]

theorem and_one_eq_zero_iff (x : UInt64) : x &&& 1 = 0 ↔ x.toBitVec.getLsbD 0 = false := by
  simp only [← UInt64.toBitVec_inj, UInt64.toBitVec_and, UInt64.toBitVec_one, UInt64.toBitVec_zero,
    BitVec.and_one_eq_setWidth_ofBool_getLsbD]
  cases x.toBitVec.getLsbD 0 <;> decide

theorem toNat_ctz_lt {x : UInt64} (hx : x ≠ 0) : x.toBitVec.ctz.toNat < 64 := by
  simpa [BitVec.lt_def] using BitVec.ctz_lt_iff_ne_zero.mpr (UInt64.toBitVec_ne_of_ne hx)

theorem getLsbD_ctz {x : UInt64} (hx : x ≠ 0) : x.toBitVec.getLsbD x.toBitVec.ctz.toNat = true :=
  BitVec.getLsbD_true_ctz_of_ne_zero (UInt64.toBitVec_ne_of_ne hx)

theorem ne_ctz_of_and_one_eq_zero {w a : UInt64} {t : Nat} (hw : w ≠ 0)
    (ha : a.toBitVec = w.toBitVec >>> t) (h : a &&& 1 = 0) : t ≠ w.toBitVec.ctz.toNat := by
  rintro rfl
  rw [and_one_eq_zero_iff, ha, BitVec.getLsbD_ushiftRight, Nat.add_zero, getLsbD_ctz hw] at h
  exact Bool.noConfusion h

theorem eq_ctz_of_and_one_ne_zero {w a : UInt64} {t : Nat} (ha : a.toBitVec = w.toBitVec >>> t)
    (ht : t ≤ w.toBitVec.ctz.toNat) (h : ¬a &&& 1 = 0) : t = w.toBitVec.ctz.toNat := by
  rw [and_one_eq_zero_iff, ha, BitVec.getLsbD_ushiftRight, Nat.add_zero] at h
  exact Nat.le_antisymm ht (Nat.not_lt.mp fun hlt ↦ h (BitVec.getLsbD_false_of_lt_ctz hlt))

/-- `x &&& (x - 1)` is `x` with its lowest set bit cleared, since `x - 1 = ~~~(-x)` agrees with `x`
above that bit and has the bit clear. -/
theorem getLsbD_and_sub_one {x : UInt64} (hx : x ≠ 0) (t : Nat) :
    (x &&& (x - 1)).toBitVec.getLsbD t = (x.toBitVec.getLsbD t && t != x.toBitVec.ctz.toNat) := by
  rw [UInt64.toBitVec_and, UInt64.toBitVec_sub, UInt64.toBitVec_one, ← BitVec.not_neg]
  grind [BitVec.getLsbD_neg, BitVec.getLsbD_false_of_lt_ctz, getLsbD_ctz]

theorem toNat_and_sub_one_lt {x : UInt64} (hx : x ≠ 0) : (x &&& (x - 1)).toNat < x.toNat := by
  grind [Nat.and_le_right, UInt64.toNat_sub_of_le, UInt64.pos_iff_ne_zero]

/-- Two words are equal when their bits are. -/
theorem eq_of_getLsbD_eq {x y : UInt64}
    (h : ∀ t, x.toBitVec.getLsbD t = y.toBitVec.getLsbD t) : x = y :=
  UInt64.toBitVec_inj.mp (BitVec.eq_of_getLsbD_eq fun t _ ↦ h t)

theorem getLsbD_one_shiftLeft {t : Nat} (ht : t < 64) (s : Nat) :
    ((1 : UInt64) <<< t.toUInt64).toBitVec.getLsbD s = decide (s = t) := by
  grind [UInt64.toBitVec_shiftLeft, UInt64.toBitVec_one]

/-- The bits `i < k` for which `c i` holds, set one after the other in the word `0`. -/
theorem getLsbD_fold_or_one_shiftLeft (c : Nat → Bool) {k : Nat} (hk : k ≤ 64) (t : Nat) :
    (Nat.fold k (fun i _ w ↦ if c i then w ||| (1 : UInt64) <<< i.toUInt64 else w)
      0).toBitVec.getLsbD t = (decide (t < k) && c t) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.fold_succ]
    grind [UInt64.toBitVec_or, getLsbD_one_shiftLeft]

/-- The bits `f i` for the `i < k` for which `c i` holds, set one after the other in the word `0`,
for `f i < 64`: `UInt64.getLsbD_fold_or_one_shiftLeft` with the bit `f i` at step `i`. -/
theorem getLsbD_fold_or_one_shiftLeft_comp (c : Nat → Bool) (f : Nat → Nat) {k : Nat}
    (hf : ∀ i < k, f i < 64) (t : Nat) :
    (Nat.fold k (fun i _ w ↦ if c i then w ||| (1 : UInt64) <<< (f i).toUInt64 else w)
      0).toBitVec.getLsbD t = decide (∃ i < k, c i = true ∧ f i = t) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.fold_succ]
    have := getLsbD_one_shiftLeft (hf k (Nat.lt_succ_self k)) t
    have := ih fun i hi ↦ hf i (Nat.lt_succ_of_lt hi)
    split <;> grind [UInt64.toBitVec_or]

theorem getLsbD_or_one_shiftLeft (x : UInt64) {n : Nat} (hn : n < 64) (t : Nat) :
    (x ||| 1 <<< UInt64.ofNat n).toBitVec.getLsbD t = (x.toBitVec.getLsbD t || decide (t = n)) := by
  rw [UInt64.toBitVec_or, BitVec.getLsbD_or, ← Nat.toUInt64_eq, getLsbD_one_shiftLeft hn]

theorem getLsbD_shiftLeft_ofNat (x : UInt64) {n : Nat} (hn : n < 64) (t : Nat) :
    (x <<< UInt64.ofNat n).toBitVec.getLsbD t =
      (decide (t < 64) && decide (n ≤ t) && x.toBitVec.getLsbD (t - n)) := by
  have : (UInt64.ofNat n).toBitVec.toNat % (64 : BitVec 64).toNat = n := by
    simp [UInt64.toBitVec_ofNat']
    lia
  rw [UInt64.toBitVec_shiftLeft, BitVec.shiftLeft_eq', BitVec.getLsbD_shiftLeft,
    BitVec.toNat_umod, this]
  grind

theorem getLsbD_shiftRight_ofNat (x : UInt64) {n : Nat} (hn : n < 64) (t : Nat) :
    (x >>> UInt64.ofNat n).toBitVec.getLsbD t = x.toBitVec.getLsbD (n + t) := by
  have : (UInt64.ofNat n).toBitVec.toNat % (64 : BitVec 64).toNat = n := by
    simp [UInt64.toBitVec_ofNat']
    lia
  rw [UInt64.toBitVec_shiftRight, BitVec.ushiftRight_eq', BitVec.getLsbD_ushiftRight,
    BitVec.toNat_umod, this]

/-- The bits of a Boolean shifted to the position `n < 64`, as `RP_INIT_BIT` sets a bit. -/
theorem getLsbD_toUInt64_shiftLeft (v : Bool) {n : Nat} (hn : n < 64) (t : Nat) :
    (v.toUInt64 <<< UInt64.ofNat n).toBitVec.getLsbD t = (v && decide (t = n)) := by
  cases v
  · simp [Bool.toUInt64]
  · simpa [Bool.toUInt64] using getLsbD_one_shiftLeft hn t

/-- For `0 < r < 64`, the word made of the bits of `x` from `r` on and the lowest `r` bits of `y`
above them: the 64 bits from position `r` on of the 128 bits of `x` followed by `y`. -/
theorem getLsbD_shiftRight_or_shiftLeft {r : Nat} (hr0 : r ≠ 0) (hr : r < 64) (x y : UInt64)
    (t : Nat) :
    (x >>> r.toUInt64 ||| y <<< (64 - r).toUInt64).toBitVec.getLsbD t =
      (decide (t < 64) && if r + t < 64 then x.toBitVec.getLsbD (r + t)
        else y.toBitVec.getLsbD (r + t - 64)) := by
  simp [BitVec.ushiftRight_eq', BitVec.shiftLeft_eq']
  grind

/-- The bits of a word and-ed in turn with the words `f a` of the entries `a` of a list. -/
theorem getLsbD_foldl_and {α : Type u} (f : α → UInt64) (l : List α) (init : UInt64) (t : Nat) :
    (l.foldl (fun acc a ↦ acc &&& f a) init).toBitVec.getLsbD t =
      (init.toBitVec.getLsbD t && l.all fun a ↦ (f a).toBitVec.getLsbD t) := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih => simp [ih, Bool.and_assoc]

theorem ofNat_ne_zero_of_lt {b : Nat} (hb0 : 0 < b) (hb : b < UInt64.size) :
    UInt64.ofNat b ≠ 0 :=
  fun h ↦ Nat.ne_of_gt hb0 (by simpa [UInt64.toNat_ofNat_of_lt' hb] using congrArg UInt64.toNat h)

/-- For `0 < b < 2 ^ 64`, `b` is `2 ^ t` times `b >>> t`, for the position `t` of the lowest set
bit of the word `b`, since the bits of `b` below it are clear. -/
theorem two_pow_ctz_mul_shiftRight_ofNat {b : Nat} (hb0 : 0 < b) (hb : b < UInt64.size) :
    2 ^ (UInt64.ofNat b).toBitVec.ctz.toNat * b >>> (UInt64.ofNat b).toBitVec.ctz.toNat = b := by
  have hlt := BitVec.lt_def.mp (BitVec.ctz_lt_iff_ne_zero.mpr
    (UInt64.toBitVec_ne_of_ne (ofNat_ne_zero_of_lt hb0 hb)))
  rw [UInt64.toBitVec_ofNat'] at hlt ⊢
  have hmod : b % 2 ^ (BitVec.ofNat 64 b).ctz.toNat = 0 := Nat.eq_of_testBit_eq fun i ↦ by
    have := BitVec.getLsbD_false_of_lt_ctz (x := BitVec.ofNat 64 b) (i := i)
    rw [BitVec.getLsbD_ofNat] at this
    simp only [Nat.testBit_mod_two_pow, Nat.zero_testBit]
    grind
  rw [Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hmod)]

/-- For `0 < b < 2 ^ 64`, `b >>> t` is odd, for the position `t` of the lowest set bit of the word
`b`. -/
theorem shiftRight_ctz_ofNat_mod_two {b : Nat} (hb0 : 0 < b) (hb : b < UInt64.size) :
    b >>> (UInt64.ofNat b).toBitVec.ctz.toNat % 2 = 1 := by
  have ht := BitVec.getLsbD_true_ctz_of_ne_zero
    (UInt64.toBitVec_ne_of_ne (ofNat_ne_zero_of_lt hb0 hb))
  rw [UInt64.toBitVec_ofNat', BitVec.getLsbD_ofNat, Bool.and_eq_true] at ht
  rw [UInt64.toBitVec_ofNat', Nat.shiftRight_eq_div_pow]
  simpa [Nat.testBit_eq_decide_div_mod_eq] using ht.2

theorem toNat_shiftRight_32 (x : UInt64) : (x >>> 32).toNat = x.toNat / 2 ^ 32 := by
  simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]

theorem toNat_and_0xffffffff (x : UInt64) :
    (x &&& 0xffffffff).toNat = x.toNat % 2 ^ 32 := by
  simpa using Nat.and_two_pow_sub_one_eq_mod x.toNat 32

theorem and_not_eq_zero_iff (w m : UInt64) :
    w &&& ~~~m = 0 ↔ ∀ t, w.toBitVec.getLsbD t = true → m.toBitVec.getLsbD t = true := by
  rw [← UInt64.toBitVec_inj]
  constructor
  · intro h t ht
    have := congrArg (·.getLsbD t) h
    simp only [UInt64.toBitVec_and, UInt64.toBitVec_not, BitVec.getLsbD_and, BitVec.getLsbD_not,
      UInt64.toBitVec_zero, BitVec.getLsbD_zero, ht] at this
    simpa [BitVec.lt_of_getLsbD ht] using this
  · intro h
    refine BitVec.eq_of_getLsbD_eq fun t ht ↦ ?_
    simp only [UInt64.toBitVec_and, UInt64.toBitVec_not, BitVec.getLsbD_and, BitVec.getLsbD_not,
      UInt64.toBitVec_zero, BitVec.getLsbD_zero]
    cases hw : w.toBitVec.getLsbD t with
    | false => simp
    | true => simp [h t hw]

theorem getLsbD_or_shiftLeft (x : UInt64) {s : Nat} (hs : s < 64) (t : Nat) :
    (x ||| x <<< UInt64.ofNat s).toBitVec.getLsbD t =
      (x.toBitVec.getLsbD t ||
        (decide (t < 64) && decide (s ≤ t) && x.toBitVec.getLsbD (t - s))) := by
  rw [UInt64.toBitVec_or, BitVec.getLsbD_or, getLsbD_shiftLeft_ofNat _ hs]

/-- One doubling of a pattern `g` of period `P ∣ s`, `s < 64`, that fills the bits below `s`: the
pattern now fills the bits below `min (2 s) 64`. -/
theorem getLsbD_or_shiftLeft_of_dvd {x : UInt64} {g : Nat → Bool} {s P : Nat} (hPs : P ∣ s)
    (hs : s < 64) (hx : ∀ t, x.toBitVec.getLsbD t = (decide (t < s) && g (t % P))) (t : Nat) :
    (x ||| x <<< UInt64.ofNat s).toBitVec.getLsbD t =
      (decide (t < min (2 * s) 64) && g (t % P)) := by
  rw [getLsbD_or_shiftLeft _ hs, hx, hx]
  obtain ⟨q, rfl⟩ := hPs
  grind [Nat.sub_mul_mod]

theorem shiftRight_and_one_beq_zero (x : UInt64) {j : Nat} (hj : j < 64) :
    (x >>> UInt64.ofNat j &&& 1 == 0) = !x.toBitVec.getLsbD j := by
  rw [Bool.eq_iff_iff, beq_iff_eq, and_one_eq_zero_iff, getLsbD_shiftRight_ofNat _ hj, Nat.add_zero]
  simp

/-- Setting bit `K₀` of the 128 bits of the two words `seen` sets the bit `K < 128` exactly when
`K = K₀`, and keeps the others. -/
theorem getLsbD_getElem!_set!_or_one_shiftLeft {seen : Array UInt64} (hs : seen.size = 2)
    {K K0 : Nat} (hK : K < 128) :
    (seen.set! (K0 / 64)
        (seen[K0 / 64]! ||| 1 <<< UInt64.ofNat (K0 % 64)))[K / 64]!.toBitVec.getLsbD (K % 64) =
      (seen[K / 64]!.toBitVec.getLsbD (K % 64) || decide (K = K0)) := by
  by_cases h : K0 / 64 = K / 64
  · rw [h, Array.getElem!_set!_self _ _ _ (by lia), getLsbD_or_one_shiftLeft _ (by lia)]
    grind
  · rw [Array.getElem!_set!_ne _ _ _ _ h]
    grind

end UInt64

/-! ### Signed words -/

namespace Int64

/-- The arithmetic shift `>>>` of a `long` by `k < 64` is the shift of its value, the floor of its
quotient by `2 ^ k`. -/
theorem toInt_shiftRight_ofNat (x : Int64) {k : Nat} (hk : k < 64) :
    (x >>> ofNat k).toInt = x.toInt >>> k := by
  rw [toInt, Int64.toBitVec_shiftRight, BitVec.toInt_sshiftRight']
  have h1 : (BitVec.ofNat 64 k).msb = false := by simp [BitVec.msb_eq_decide]; lia
  have h2 : (64#64).msb = false := by decide
  simp [BitVec.smod, h1, h2, Nat.mod_eq_of_lt hk]

/-- The mask `x >>> 63` of a `long` is `-1` for a negative one and `0` otherwise. -/
theorem shiftRight_63 (x : Int64) : x >>> 63 = if x < 0 then -1 else 0 := by
  have h := toInt_shiftRight_ofNat x (k := 63) (by decide)
  rw [Int.shiftRight_eq_div_pow] at h
  have := x.toInt_lt
  have := x.le_toInt
  refine toInt_inj.mp (h.trans ?_)
  split <;> grind [lt_iff_toInt_lt]

theorem and_shiftRight_63 (x : Int64) : x &&& x >>> 63 = if x < 0 then x else 0 := by
  rw [shiftRight_63]
  split <;> simp

theorem xor_shiftRight_63_sub (x : Int64) :
    (x ^^^ x >>> 63) - x >>> 63 = if x < 0 then -x else x := by
  rw [shiftRight_63]
  split <;> simp [not_eq_neg_sub]

theorem sub_lt_zero_iff_of_nonneg {a b : Int64} (ha : 0 ≤ a) (hb : 0 ≤ b) : a - b < 0 ↔ a < b := by
  have := a.toInt_lt
  have := b.toInt_lt
  grind [lt_iff_toInt_lt, le_iff_toInt_le, toInt_sub, Int.bmod_eq_of_le]

/-- `n + (d &&& d >>> 63)` for `d = m - n` is the smaller of two non-negative `long`s `m` and `n`,
without a branch. -/
theorem toNatClampNeg_add_and_shiftRight_63 {m n : Int64} (hm : 0 ≤ m) (hn : 0 ≤ n) :
    (n + (m - n &&& (m - n) >>> 63)).toNatClampNeg = min m.toNatClampNeg n.toNatClampNeg := by
  rw [and_shiftRight_63]
  have := toInt_eq_toNatClampNeg hm
  have := toInt_eq_toNatClampNeg hn
  have := sub_lt_zero_iff_of_nonneg hm hn
  split <;> grind [lt_iff_toInt_lt]

/-- `(d ^^^ d >>> 63) - d >>> 63` for `d = m - n` is the distance of two non-negative `long`s `m`
and `n`, without a branch. -/
theorem toNatClampNeg_xor_shiftRight_63_sub {m n : Int64} (hm : 0 ≤ m) (hn : 0 ≤ n) :
    ((m - n ^^^ (m - n) >>> 63) - (m - n) >>> 63).toNatClampNeg =
      if m.toNatClampNeg < n.toNatClampNeg then n.toNatClampNeg - m.toNatClampNeg
      else m.toNatClampNeg - n.toNatClampNeg := by
  rw [xor_shiftRight_63_sub]
  have := toInt_eq_toNatClampNeg hm
  have := toInt_eq_toNatClampNeg hn
  have := sub_lt_zero_iff_of_nonneg hm hn
  split <;> grind [lt_iff_toInt_lt, Int64.neg_sub, toNatClampNeg_sub_of_le]

theorem xor_shiftRight_63_sub_pos {m n : Int64} (hm : 0 ≤ m) (hn : 0 ≤ n) (h : m ≠ n) :
    (0 : Int64) < (m - n ^^^ (m - n) >>> 63) - (m - n) >>> 63 := by
  have := ofNat_toNatClampNeg m hm
  have := ofNat_toNatClampNeg n hn
  have hne : m.toNatClampNeg ≠ n.toNatClampNeg := fun h' ↦ h (by grind)
  rw [← toNatClampNeg_pos_iff, toNatClampNeg_xor_shiftRight_63_sub hm hn]
  split <;> lia

theorem toNatClampNeg_shiftRight_ofNat {x : Int64} (hx : 0 ≤ x) {k : Nat} (hk : k < 64) :
    (x >>> ofNat k).toNatClampNeg = x.toNatClampNeg >>> k := by
  rw [← toNat_toInt, toInt_shiftRight_ofNat x hk, toInt_eq_toNatClampNeg hx,
    ← Int.natCast_shiftRight, Int.toNat_natCast]

theorem toUInt64_eq_ofNat_toNatClampNeg {x : Int64} (hx : 0 ≤ x) :
    x.toUInt64 = UInt64.ofNat x.toNatClampNeg := by
  rw [← toNat_toUInt64_of_le hx, UInt64.ofNat_toNat]

theorem toUInt64_ne_zero_of_pos {x : Int64} (hx : 0 < x) : x.toUInt64 ≠ 0 := by
  rw [toUInt64_eq_ofNat_toNatClampNeg (Int64.le_of_lt hx)]
  exact UInt64.ofNat_ne_zero_of_lt ((toNatClampNeg_pos_iff x).mpr hx)
    (Nat.lt_trans x.toNatClampNeg_lt (by decide))

/-- A positive `long` `x` is `2 ^ t` times `x >>> t`, for the position `t` of the lowest set bit of
the word `x` read as unsigned. -/
theorem two_pow_ctz_mul_toNatClampNeg_shiftRight {x : Int64} (hx : 0 < x) :
    2 ^ x.toUInt64.toBitVec.ctz.toNat * (x >>> ofNat x.toUInt64.toBitVec.ctz.toNat).toNatClampNeg =
      x.toNatClampNeg := by
  rw [toNatClampNeg_shiftRight_ofNat (Int64.le_of_lt hx)
    (UInt64.toNat_ctz_lt (toUInt64_ne_zero_of_pos hx)), toUInt64_eq_ofNat_toNatClampNeg
    (Int64.le_of_lt hx)]
  exact UInt64.two_pow_ctz_mul_shiftRight_ofNat ((toNatClampNeg_pos_iff x).mpr hx)
    (Nat.lt_trans x.toNatClampNeg_lt (by decide))

/-- A positive `long` `x` shifted right by the position of the lowest set bit of the word `x` read
as unsigned is odd. -/
theorem toNatClampNeg_shiftRight_ctz_mod_two {x : Int64} (hx : 0 < x) :
    (x >>> ofNat x.toUInt64.toBitVec.ctz.toNat).toNatClampNeg % 2 = 1 := by
  rw [toNatClampNeg_shiftRight_ofNat (Int64.le_of_lt hx)
    (UInt64.toNat_ctz_lt (toUInt64_ne_zero_of_pos hx)), toUInt64_eq_ofNat_toNatClampNeg
    (Int64.le_of_lt hx)]
  exact UInt64.shiftRight_ctz_ofNat_mod_two ((toNatClampNeg_pos_iff x).mpr hx)
    (Nat.lt_trans x.toNatClampNeg_lt (by decide))

theorem and_one_beq_zero_iff {x : Int64} (hx : 0 ≤ x) :
    (x &&& 1 == 0) = true ↔ x.toNatClampNeg % 2 = 0 := by
  rw [beq_iff_eq, ← toNat_toUInt64_of_le hx, ← toNat_toBitVec, ← toBitVec_inj, ← BitVec.toNat_inj]
  simp [Nat.and_one_is_mod]

theorem toNatClampNeg_eq_natAbs {x : Int64} (hx : 0 ≤ x) : x.toNatClampNeg = x.toInt.natAbs := by
  have := le_iff_toInt_le.mp hx
  rw [← toNat_toInt]
  lia

/-- The absolute value of a `long` other than `-2 ^ 63`, whose negation would leave the range. -/
theorem toNatClampNeg_ite_neg {x : Int64} (h : minValue < x) :
    (if x < 0 then -x else x).toNatClampNeg = x.toInt.natAbs := by
  split
  · have h1 := lt_iff_toInt_lt.mp h
    have h2 := lt_iff_toInt_lt.mp ‹x < 0›
    rw [toInt_minValue] at h1
    rw [toInt_zero] at h2
    rw [← toNat_toInt, toInt_neg, Int.bmod_eq_of_le (by lia) (by lia)]
    lia
  · exact toNatClampNeg_eq_natAbs (Int64.not_lt.mp ‹_›)

theorem toNatClampNeg_eq_one_iff (x : Int64) : x.toNatClampNeg = 1 ↔ x = 1 := by
  rw [← toNat_toInt, ← toInt_inj, toInt_one]
  lia

theorem minValue_lt_ofInt {a : Int} (ha : a.natAbs < 2 ^ 63) : minValue < ofInt a := by
  rw [lt_iff_toInt_lt, toInt_minValue, toInt_ofInt_of_le (by lia) (by lia)]
  lia

theorem ofNat_pos {n : Nat} (h0 : 0 < n) (h : n < 2 ^ 63) : 0 < ofNat n := by
  rw [lt_iff_toInt_lt, toInt_zero, toInt_ofNat_of_lt h]
  lia

theorem toInt_add_of_lt {a b : Int64} (h1 : -2 ^ 63 ≤ a.toInt + b.toInt)
    (h2 : a.toInt + b.toInt < 2 ^ 63) : (a + b).toInt = a.toInt + b.toInt := by
  rw [toInt_add, Int.bmod_eq_of_le (by lia) (by lia)]

theorem toInt_sub_of_lt {a b : Int64} (h1 : -2 ^ 63 ≤ a.toInt - b.toInt)
    (h2 : a.toInt - b.toInt < 2 ^ 63) : (a - b).toInt = a.toInt - b.toInt := by
  rw [toInt_sub, Int.bmod_eq_of_le (by lia) (by lia)]

theorem toInt_neg_of_lt {a : Int64} (h : -2 ^ 63 < a.toInt) : (-a).toInt = -a.toInt := by
  have := a.toInt_lt
  rw [toInt_neg, Int.bmod_eq_of_le (by lia) (by lia)]

/-- The mask `(1 <<< k) - 1` of the low `k ≤ 6` bits of a `long`, `2 ^ k - 1`. -/
theorem one_shiftLeft_sub_one {k : Nat} (hk : k ≤ 6) :
    (1 : Int64) <<< ofNat k - 1 = ofNat (2 ^ k - 1) := by
  have h : ∀ k < 7, (1 : Int64) <<< ofNat k - 1 = ofNat (2 ^ k - 1) := by decide
  exact h k (Nat.lt_succ_of_le hk)

/-- A `long` and-ed with the mask `2 ^ k - 1 < 2 ^ 63` is its Euclidean remainder modulo `2 ^ k`,
also for a negative one, in two's complement. -/
theorem toInt_and_ofNat_two_pow_sub_one (x : Int64) {k : Nat} (hk : k < 63) :
    (x &&& ofNat (2 ^ k - 1)).toInt = x.toInt % 2 ^ k := by
  have h2 : 2 ^ k < 2 ^ 63 := Nat.pow_lt_pow_right (by decide) hk
  have hm : (BitVec.ofNat 64 (2 ^ k - 1)).toNat = 2 ^ k - 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by lia)]
  have hd : (2 : Int) ^ k ∣ (2 ^ 64 : Nat) := mod_cast Nat.pow_dvd_pow 2 (by lia : k ≤ 64)
  have := Nat.mod_lt x.toBitVec.toNat (Nat.two_pow_pos k)
  rw [toInt, toInt, Int64.toBitVec_and, BitVec.toInt_and, Int64.toBitVec_ofNat', hm,
    Nat.and_two_pow_sub_one_eq_mod, Int.bmod_eq_of_le (by lia) (by lia),
    BitVec.toInt_eq_toNat_bmod, ← Int.emod_emod_of_dvd _ hd, Int.bmod_emod,
    Int.emod_emod_of_dvd _ hd]
  simp

theorem toInt_ofNat_two_pow_sub_one {k : Nat} (hk : k < 63) :
    (ofNat (2 ^ k - 1)).toInt = 2 ^ k - 1 := by
  have h := Nat.one_le_two_pow (n := k)
  have h2 : 2 ^ k < 2 ^ 63 := Nat.pow_lt_pow_right (by decide) hk
  rw [toInt_ofNat_of_lt (by lia)]
  have h1 : ((2 ^ k - 1 : Nat) : Int) = ((2 ^ k : Nat) : Int) - 1 := by lia
  rw [h1, Int.natCast_pow]
  rfl

end Int64

end

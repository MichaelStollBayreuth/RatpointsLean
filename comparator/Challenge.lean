/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Algebra.Polynomial.Sturm.Sequence
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.List.SignVariations
public import Mathlib.Data.Nat.Factors
public import Mathlib.Order.WithBotTop
public import Ratpoints.Fast
public import Ratpoints.Model

/-!
# Comparator challenge statements

The main theorems of the project, stated with `sorry` for
[leanprover/comparator](https://github.com/leanprover/comparator), over a verbatim restatement of
the specification. The file may import only Mathlib and the model (`scripts/check_layout.py`
checks this): the main theorems speak about the model's `findPoints` and `findPointsWith`, which
are trusted in the sense that they are the code the executable runs, while the specification is
reproduced here, so that a solution that changed it would be rejected.

The file has thirteen statements, which `comparator/challenges.json` lists; `comparator/README.md`
describes them and gives the date on which Comparator last accepted them. Two are about the
brute-force reference: `Ratpoints.bruteForce` finds exactly the points (`Ratpoints.IsPoint`),
without duplicates. Two are about the fast search `Ratpoints.Fast.fastPoints`, which the program
`ratpoints-lean` runs: for every coefficient list, height bound, range of denominators and setting
of its parameters it lists exactly the points of height at most `H` in the range
(`Ratpoints.InRegion` without search intervals), without duplicates. The other nine hold for every
coefficient list `c`, height bound `H`, options of the search `o : Ratpoints.Options` and options of
the sieve `s : Ratpoints.SieveOptions`, with no hypothesis on `s`, with which the search chooses its
moduli from the curve:

* membership: with the exact check on (`o.noCheck = false`) and assuming Sturm's theorem
  (`Ratpoints.SturmTheorem`) when the Sturm step is on, the list of `Ratpoints.findPoints` holds
  exactly the points of height at most `H` in the search region (`Ratpoints.InRegion`, over the
  values of the ends of the search intervals, `Ratpoints.doubleValue`), of each pair `(x, ±y, z)`
  only the one with `y ≥ 0` when `o.noY` is set;
* no duplicates, for every option, the options of the output among them;
* the refusals: with the Sturm step on, `Ratpoints.findPoints` refuses exactly the inputs with fewer
  than two or more than `Ratpoints.maxDegree + 1` coefficients, the height bound `0` or one of
  `2 ^ 63` or more, which is not a `long`, the binary forms `Ratpoints.binaryFormPoly c` that are
  not squarefree, and search intervals that are not well formed (`Ratpoints.IntervalsWF`); with it
  off, it refuses exactly what the program refuses under `-s`, and under `-s -k` when the reversal
  is off, or the search region is not the whole box (`Ratpoints.IsFullBox`); so a
  `Ratpoints.findPoints` that refuses every input, with or without the Sturm step, is ruled out;
* the order: under the hypotheses of membership, the list is that of the points in the order of
  `ratpoints` (`Ratpoints.orderedPoints`, with the bound `Ratpoints.maxDivisors` of the model on the
  number of divisors, the reversal only for the whole box and the largest denominator
  `Ratpoints.denominatorBound`), filtered by `o.noY` and the search region;
* with the exact check off (`o.noCheck = true`): every element `(x, y, z)` of the list has `y = 0`,
  a normalized pair `(x, z)` of height at most `H` (`Ratpoints.IsNormalizedPair`) and lies in the
  search region; every point `(x, y, z)` of height at most `H` in the search region gives the
  element `(x, 0, z)` (assuming Sturm's theorem when the Sturm step is on); and the points with
  `y ≥ 0` of the same search with the exact check on, with `y` replaced by `0`, are a sublist of
  the list, so that they come in the same order;
* the protocol: the search with a callback (`Ratpoints.findPointsWith`, with its trailing print
  argument at its default, the channel that prints nothing) refuses what `Ratpoints.findPoints`
  refuses, and otherwise returns the data of the callback and the count of the delivery of the list
  of `Ratpoints.findPoints` to the callback (`Ratpoints.Delivery.deliver`): the calls of the
  callback for the points of the list in their order, up to and including the first that stops the
  search.

`Ratpoints.bruteForce`, `Ratpoints.Fast.fastPoints`, `Ratpoints.Fast.Tuning`,
`Ratpoints.findPoints`, `Ratpoints.findPointsWith`, `Ratpoints.Outcome`,
`Ratpoints.Answer`, `Ratpoints.Delivery`, `Ratpoints.Delivery.deliver`, `Ratpoints.Options`,
`Ratpoints.Double`, `Ratpoints.SieveOptions`, `Ratpoints.maxDegree` and `Ratpoints.maxDivisors` come
from the model, never restated, since a definition of the model elaborates without Mathlib to other
instance terms. Of Mathlib, the file imports exactly the public imports of the files of the
specification (`Ratpoints/Spec/Basic.lean`, `Ratpoints/Spec/Order.lean`,
`Ratpoints/Spec/Region.lean` and `Ratpoints/Spec/Sturm.lean`), so that the restated definitions
elaborate to the same terms as there.
-/

@[expose] public section

namespace Ratpoints

/-- The degree of the polynomial `∑ cᵢ Xⁱ`: the largest index of a nonzero entry of `c`, or `0`
if there is none. -/
def degree (c : List ℤ) : ℕ := (c.reverse.dropWhile (· == 0)).length - 1

/-- The binary form `F(x, z) = ∑ cᵢ xⁱ z^(D - i)` of even degree `D = d + d % 2` of the
polynomial of degree `d` with coefficient list `c`. -/
def binaryForm (c : List ℤ) (x z : ℤ) : ℤ :=
  ∑ i ∈ Finset.range (degree c + 1), c.getD i 0 * x ^ i * z ^ (degree c + degree c % 2 - i)

/-- The binary form `Φ = ∑ cᵢ Xⁱ Z^(N - i)` over `ℚ` of degree `N = 2 ⌈n / 2⌉`, where `n + 1` is
the length of `c`: the polynomial made homogeneous of the even degree that the length of its
coefficient list allows. The refusals of the program speak about this form; on every input that
is not refused, it agrees with `Ratpoints.binaryForm` (`Ratpoints.eval_binaryFormPoly`). -/
noncomputable def binaryFormPoly (c : List ℤ) : MvPolynomial (Fin 2) ℚ :=
  ∑ i ∈ Finset.range c.length,
    MvPolynomial.C (c.getD i 0 : ℚ) * MvPolynomial.X 0 ^ i *
      MvPolynomial.X 1 ^ (2 * (c.length / 2) - i)

/-- The pair `(x, z)` is normalized and of height at most `H`, as the program prints the points:
`gcd(x, z) = 1`, `0 < z` or `(x, z) = (1, 0)`, `|x| ≤ H` and `z ≤ H`. So is the pair `(x, z)` of
every triple `(x, 0, z)` that the program prints under `RATPOINTS_NO_CHECK`, whether the triple is
a point or not. -/
def IsNormalizedPair (H : ℕ) (x z : ℤ) : Prop :=
  Int.gcd x z = 1 ∧ (0 < z ∨ z = 0 ∧ x = 1) ∧ |x| ≤ H ∧ z ≤ H

instance instDecidableIsNormalizedPair (H : ℕ) (x z : ℤ) : Decidable (IsNormalizedPair H x z) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- `(x, y, z)` is a point of height at most `H` on `y ^ 2 = F(x, z)`, `F = Ratpoints.binaryForm c`,
normalized as the program prints it: the equation holds, and `(x, z)` is normalized and of height
at most `H` (`Ratpoints.IsNormalizedPair`). -/
def IsPoint (c : List ℤ) (H : ℕ) (p : ℤ × ℤ × ℤ) : Prop :=
  p.2.1 ^ 2 = binaryForm c p.1 p.2.2 ∧ IsNormalizedPair H p.1 p.2.2

instance instDecidablePredIsPoint (c : List ℤ) (H : ℕ) : DecidablePred (IsPoint c H) :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- Whether the IEEE binary64 bits `x` are a NaN: the exponent field all ones and the fraction
nonzero. -/
def IsNaN (x : UInt64) : Prop := (x.toNat / 2 ^ 52) % 2 ^ 11 = 2047 ∧ x.toNat % 2 ^ 52 ≠ 0

instance instDecidableIsNaN (x : UInt64) : Decidable (IsNaN x) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The value of the IEEE binary64 double with the bits `x`: `±f 2 ^ (-1074)` for the exponent
field `0` (the zeros and the subnormals, both zeros giving `0`), `±(2 ^ 52 + f) 2 ^ (e - 1075)` for
an exponent field `e` from `1` to `2046`, and `⊥` and `⊤` for the infinities, where `f` is the
fraction and the sign is that of the top bit. The value of a NaN (the exponent field `2047` with a
nonzero fraction) is junk, an infinity: `Ratpoints.IntervalsWF` excludes NaNs. -/
def doubleValue (x : UInt64) : WithBotTop ℚ :=
  let e : ℕ := (x.toNat / 2 ^ 52) % 2 ^ 11
  let f : ℕ := x.toNat % 2 ^ 52
  if e = 2047 then (if 2 ^ 63 ≤ x.toNat then ⊥ else ⊤)
  else
    let a : ℚ := if e = 0 then f * 2 ^ (-1074 : ℤ) else (2 ^ 52 + f) * 2 ^ ((e : ℤ) - 1075)
    ((if 2 ^ 63 ≤ x.toNat then -a else a : ℚ) : WithBotTop ℚ)

/-- Closed intervals `[l, u]` with `l ≤ u`, increasing and strictly apart: the upper end of each
below the lower end of the next. -/
def AreSearchIntervals (dom : List (WithBotTop ℚ × WithBotTop ℚ)) : Prop :=
  (∀ i ∈ dom, i.1 ≤ i.2) ∧ dom.IsChain fun i j ↦ i.2 < j.1

instance instDecidableAreSearchIntervals (dom : List (WithBotTop ℚ × WithBotTop ℚ)) :
    Decidable (AreSearchIntervals dom) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The search intervals with the ends of the bits of doubles that `ratpoints` accepts, the test of
`RATPOINTS_BAD_ARGS`: no end is a NaN, and the values are closed intervals, increasing and strictly
apart (`Ratpoints.AreSearchIntervals`); `-0` and `0` have the same value. -/
def IntervalsWF (dom : List (UInt64 × UInt64)) : Prop :=
  (∀ i ∈ dom, ¬ IsNaN i.1 ∧ ¬ IsNaN i.2) ∧
    AreSearchIntervals (dom.map fun i ↦ (doubleValue i.1, doubleValue i.2))

instance instDecidableIntervalsWF (dom : List (UInt64 × UInt64)) : Decidable (IntervalsWF dom) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The rational number `x` lies in one of the intervals `D`, over the values of their ends, both
ends included. -/
def InIntervals (D : List (WithBotTop ℚ × WithBotTop ℚ)) (x : ℚ) : Prop :=
  ∃ i ∈ D, i.1 ≤ (x : WithBotTop ℚ) ∧ (x : WithBotTop ℚ) ≤ i.2

instance instDecidablePredInIntervals (D : List (WithBotTop ℚ × WithBotTop ℚ)) :
    DecidablePred (InIntervals D) :=
  fun _ ↦ inferInstanceAs (Decidable (∃ _ ∈ D, _))

/-- The triple `p = (x, y, z)` lies in the search region of the intervals `dom` (over the values of
their ends) and the range of the denominators from `bLow` to `bHigh`: `z = 0` (a point at
infinity), or `bLow ≤ z`, `z ≤ bHigh` unless `bHigh < 1` (no bound beyond the height bound), and
`x / z` in one of the intervals (`Ratpoints.InIntervals`), or anywhere when there are none. -/
def InRegion (dom : List (WithBotTop ℚ × WithBotTop ℚ)) (bLow bHigh : ℤ) (p : ℤ × ℤ × ℤ) :
    Prop :=
  p.2.2 = 0 ∨ bLow ≤ p.2.2 ∧ (bHigh < 1 ∨ p.2.2 ≤ bHigh) ∧
    (dom = [] ∨ InIntervals dom (p.1 / p.2.2))

instance instDecidablePredInRegion (dom : List (WithBotTop ℚ × WithBotTop ℚ)) (bLow bHigh : ℤ) :
    DecidablePred (InRegion dom bLow bHigh) :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- The search region of the intervals `dom` and the range of the denominators from `bLow` to
`bHigh` is the whole box of the height bound `H`: no intervals, `bLow ≤ 1` and no bound below `H`
on the denominators (`bHigh < 1` or `H ≤ bHigh`). Only then may `ratpoints` reverse the polynomial
(otherwise it sets `RATPOINTS_NO_REVERSE_AUTO`). -/
def IsFullBox {α : Type*} (dom : List α) (bLow bHigh : ℤ) (H : ℕ) : Prop :=
  dom = [] ∧ bLow ≤ 1 ∧ (bHigh < 1 ∨ H ≤ bHigh)

instance instDecidableIsFullBox {α : Type*} (dom : List α) (bLow bHigh : ℤ) (H : ℕ) :
    Decidable (IsFullBox dom bLow bHigh H) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The largest denominator of the search for the bound `bHigh` and the height bound `H`: `bHigh`
when `1 ≤ bHigh ≤ H`, and `H` otherwise. -/
def denominatorBound (bHigh : ℤ) (H : ℕ) : ℕ :=
  if 1 ≤ bHigh ∧ bHigh ≤ H then bHigh.toNat else H

open Polynomial in
/-- Sturm's theorem: for every squarefree real polynomial `p` and all reals `a ≤ b`, the number of
roots of `p` in `(a, b]` plus the number of sign variations of the Sturm sequence of `p` and its
derivative evaluated at `b` is that number at `a`. A hypothesis of the theorems on the Sturm step,
not an axiom. -/
def SturmTheorem : Prop :=
  ∀ p : ℝ[X], Squarefree p → ∀ a b : ℝ, a ≤ b →
    {x | a < x ∧ x ≤ b ∧ p.IsRoot x}.ncard +
        ((sturmSeq p (derivative p)).map (eval b)).signVariations =
      ((sturmSeq p (derivative p)).map (eval a)).signVariations

/-- The polynomial that `ratpoints` searches for the coefficient list `c` of degree `d`, and whether
it is reversed, when the switch `reverse` allows a reversal (the option `-k` of the program forbids
it): for even `d`, the list `c_d, …, c₀` when `c₀ = 0` (then `c₁ ≠ 0`, or the binary form is not
squarefree and refused) or when `c_d` is a square and `c₀` is not; for odd `d`, the list
`0, c_d, …, c₁` when `|c_d| ≠ 1`, `c₀ = 0` and `|c₁| = 1`; otherwise `c` itself. The binary form
of a reversed list is that of `c` with `x` and `z` exchanged, except for even `d` with
`c₀ = c₁ = 0`, which `ratpoints` refuses. -/
def searchedPoly (reverse : Bool) (c : List ℤ) : List ℤ × Bool :=
  let d := degree c
  if reverse ∧ d % 2 = 0 ∧
      (c.getD 0 0 = 0 ∨ IsSquare (c.getD d 0) ∧ ¬IsSquare (c.getD 0 0)) then
    ((c.take (d + 1)).reverse, true)
  else if reverse ∧ d % 2 = 1 ∧ (c.getD d 0).natAbs ≠ 1 ∧ c.getD 0 0 = 0 ∧
      (c.getD 1 0).natAbs = 1 then
    (0 :: (c.take (d + 1)).tail.reverse, true)
  else (c, false)

/-- Whether `ratpoints` factors `n` completely: it divides off `2` and the odd primes up to `1021`
in turn and takes a cofactor below `p ^ 2`, for the next prime `p`, as a prime, which it is; so it
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
denominators, `Ratpoints.denominatorBound`): when `d` is odd, `|c_d| ≠ 1`, `ratpoints` factors
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
denominators at most `B`, in the order in which `ratpoints` finds them, for the switch `reverse` of
the reversal and the bound `maxDiv` of the number of divisors: for the polynomial searched
(`Ratpoints.searchedPoly`), its points at infinity, then the points of its denominators up to `B`
(`Ratpoints.searchDenominators`) in turn (`Ratpoints.pointsWithDen`); after a reversal, each point
`(a, y, b)` of that list becomes `(b, y, a)` for `a ≥ 0` and `(-b, y, -a)` for `a < 0`, a point of
the caller's curve. -/
def orderedPoints (maxDiv : ℕ) (reverse : Bool) (c : List ℤ) (H B : ℕ) : List (ℤ × ℤ × ℤ) :=
  let (c', rev) := searchedPoly reverse c
  let L := (0 :: searchDenominators maxDiv c' B).flatMap (pointsWithDen c' H)
  if rev then L.map fun (a, y, b) ↦ if 0 ≤ a then (b, y, a) else (-b, y, -a) else L

end Ratpoints

theorem challenge_mem_bruteForce_iff (c : List ℤ) (H : ℕ) (p : ℤ × ℤ × ℤ) :
    p ∈ Ratpoints.bruteForce c H ↔ Ratpoints.IsPoint c H p :=
  sorry

theorem challenge_nodup_bruteForce (c : List ℤ) (H : ℕ) : (Ratpoints.bruteForce c H).Nodup :=
  sorry

theorem challenge_mem_fastPoints_iff (c : List ℤ) (H : ℕ) (bLow bHigh : ℤ)
    (tu : Ratpoints.Fast.Tuning) (p : ℤ × ℤ × ℤ) :
    p ∈ Ratpoints.Fast.fastPoints c H bLow bHigh tu ↔
      Ratpoints.IsPoint c H p ∧ Ratpoints.InRegion [] bLow bHigh p :=
  sorry

theorem challenge_nodup_fastPoints (c : List ℤ) (H : ℕ) (bLow bHigh : ℤ)
    (tu : Ratpoints.Fast.Tuning) : (Ratpoints.Fast.fastPoints c H bLow bHigh tu).Nodup :=
  sorry

theorem challenge_mem_iff_isPoint_of_findPoints_eq_ok (c : List ℤ) (H : ℕ)
    (s : Ratpoints.SieveOptions) (o : Ratpoints.Options) (L : List (ℤ × ℤ × ℤ))
    (hS : 0 ≤ o.sturm → Ratpoints.SturmTheorem) (hc : o.noCheck = false)
    (h : Ratpoints.findPoints c H s o = .ok L) (p : ℤ × ℤ × ℤ) :
    p ∈ L ↔ Ratpoints.IsPoint c H p ∧ (o.noY = true → 0 ≤ p.2.1) ∧
      Ratpoints.InRegion
        (o.domain.map fun i ↦ (Ratpoints.doubleValue i.1.bits, Ratpoints.doubleValue i.2.bits))
        o.bLow o.bHigh p :=
  sorry

theorem challenge_nodup_of_findPoints_eq_ok (c : List ℤ) (H : ℕ) (s : Ratpoints.SieveOptions)
    (o : Ratpoints.Options) (L : List (ℤ × ℤ × ℤ)) (h : Ratpoints.findPoints c H s o = .ok L) :
    L.Nodup :=
  sorry

theorem challenge_exists_findPoints_eq_error_iff_of_sturm_nonneg (c : List ℤ) (H : ℕ)
    (s : Ratpoints.SieveOptions) (o : Ratpoints.Options) (hs : 0 ≤ o.sturm) :
    (∃ e, Ratpoints.findPoints c H s o = .error e) ↔
      c.length < 2 ∨ Ratpoints.maxDegree + 1 < c.length ∨ H = 0 ∨ 2 ^ 63 ≤ H ∨
        ¬ Squarefree (Ratpoints.binaryFormPoly c) ∨
        ¬ Ratpoints.IntervalsWF (o.domain.map fun i ↦ (i.1.bits, i.2.bits)) :=
  sorry

theorem challenge_exists_findPoints_eq_error_iff_of_sturm_neg (c : List ℤ) (H : ℕ)
    (s : Ratpoints.SieveOptions) (o : Ratpoints.Options) (hs : o.sturm < 0) :
    (∃ e, Ratpoints.findPoints c H s o = .error e) ↔
      c.length < 2 ∨ Ratpoints.maxDegree + 1 < c.length ∨ H = 0 ∨ 2 ^ 63 ≤ H ∨
        Ratpoints.degree c + 2 ≤ 2 * (c.length / 2) ∨
        o.reverse = true ∧ Ratpoints.IsFullBox o.domain o.bLow o.bHigh H ∧
          Ratpoints.degree c % 2 = 0 ∧ c.getD 0 0 = 0 ∧ c.getD 1 0 = 0 ∨
        ¬ Ratpoints.IntervalsWF (o.domain.map fun i ↦ (i.1.bits, i.2.bits)) :=
  sorry

theorem challenge_eq_orderedPoints_of_findPoints_eq_ok (c : List ℤ) (H : ℕ)
    (s : Ratpoints.SieveOptions) (o : Ratpoints.Options) (L : List (ℤ × ℤ × ℤ))
    (hS : 0 ≤ o.sturm → Ratpoints.SturmTheorem) (hc : o.noCheck = false)
    (h : Ratpoints.findPoints c H s o = .ok L) :
    L = (Ratpoints.orderedPoints Ratpoints.maxDivisors
        (o.reverse && Ratpoints.IsFullBox o.domain o.bLow o.bHigh H) c H
        (Ratpoints.denominatorBound o.bHigh H)).filter fun p ↦ (!o.noY || 0 ≤ p.2.1) &&
      Ratpoints.InRegion
        (o.domain.map fun i ↦ (Ratpoints.doubleValue i.1.bits, Ratpoints.doubleValue i.2.bits))
        o.bLow o.bHigh p :=
  sorry

theorem challenge_isNormalizedPair_of_mem_of_findPoints_eq_ok_of_noCheck (c : List ℤ) (H : ℕ)
    (s : Ratpoints.SieveOptions) (o : Ratpoints.Options) (L : List (ℤ × ℤ × ℤ))
    (hc : o.noCheck = true) (h : Ratpoints.findPoints c H s o = .ok L) (q : ℤ × ℤ × ℤ)
    (hq : q ∈ L) :
    q.2.1 = 0 ∧ Ratpoints.IsNormalizedPair H q.1 q.2.2 ∧
      Ratpoints.InRegion
        (o.domain.map fun i ↦ (Ratpoints.doubleValue i.1.bits, Ratpoints.doubleValue i.2.bits))
        o.bLow o.bHigh q :=
  sorry

theorem challenge_mem_of_isPoint_of_findPoints_eq_ok_of_noCheck (c : List ℤ) (H : ℕ)
    (s : Ratpoints.SieveOptions) (o : Ratpoints.Options) (L : List (ℤ × ℤ × ℤ))
    (hS : 0 ≤ o.sturm → Ratpoints.SturmTheorem) (hc : o.noCheck = true)
    (h : Ratpoints.findPoints c H s o = .ok L) (p : ℤ × ℤ × ℤ) (hp : Ratpoints.IsPoint c H p)
    (hr : Ratpoints.InRegion
      (o.domain.map fun i ↦ (Ratpoints.doubleValue i.1.bits, Ratpoints.doubleValue i.2.bits))
      o.bLow o.bHigh p) :
    (p.1, 0, p.2.2) ∈ L :=
  sorry

theorem challenge_map_sublist_of_findPoints_eq_ok_of_noCheck (c : List ℤ) (H : ℕ)
    (s : Ratpoints.SieveOptions) (o : Ratpoints.Options) (L L' : List (ℤ × ℤ × ℤ))
    (hc : o.noCheck = true) (h : Ratpoints.findPoints c H s o = .ok L)
    (h' : Ratpoints.findPoints c H s { o with noCheck := false, noY := true } = .ok L') :
    (L'.map fun q ↦ (q.1, 0, q.2.2)).Sublist L :=
  sorry

theorem challenge_map_findPointsWith_eq_map_findPoints {σ : Type} (c : List ℤ) (H : ℕ)
    (s : Ratpoints.SieveOptions) (o : Ratpoints.Options)
    (process : ℤ → ℤ → ℤ → σ → Ratpoints.Answer σ) (info : σ) :
    (Ratpoints.findPointsWith c H s o process info).map (fun r ↦ (r.info, r.total)) =
      (Ratpoints.findPoints c H s o).map fun L ↦
        let r := Ratpoints.Delivery.deliver process ⟨info, 0, false⟩ L; (r.info, r.total) :=
  sorry

end

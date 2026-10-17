/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Nat.Factors
public import Ratpoints.Model

/-!
# Comparator challenge statements

The main theorems of the project, stated with `sorry` for
[leanprover/comparator](https://github.com/leanprover/comparator), over a verbatim restatement of
the specification. The file may import only Mathlib and the model (`scripts/check_layout.py`
checks this): the main theorems speak about the model's `findPoints` and `findPointsWith`, which
are trusted in the sense that they are the code the executable runs, while the specification is
reproduced here, so that a solution that changed it would be rejected.

The statements come in stage by stage, as `comparator/README.md` lists them: the two theorems of
stage B (the brute-force reference finds exactly the points, without duplicates); from stage C1 on,
the membership and no-duplicates theorems for `Ratpoints.findPoints` for well-formed parameters,
since stage D for every option, and the well-formedness of every parameter set that the options of
the program give, which rules out a well-formedness that nothing satisfies; the refusal theorems of
stage D, with the Sturm step on (`Ratpoints.findPoints` refuses exactly the inputs with fewer than
two or more than `Ratpoints.maxDegree + 1` coefficients, the height bound `0` or one of `2 ^ 63` or
more, which is not a `long`, and the binary forms `Ratpoints.binaryFormPoly c` that are not
squarefree) and off (it refuses exactly what the program refuses under `-s`, and under `-s -k` when
the reversal is off), which rule out a `Ratpoints.findPoints` that refuses every input, with or
without the Sturm step; and the theorems of stage G, for well-formed parameters, on the options of
the output, the order and the protocol of the delivery. Since stage G membership holds with the
exact check on (`o.noCheck = false`): the list of `Ratpoints.findPoints` holds exactly the points,
of each pair `(x, ±y, z)` only the one with `y ≥ 0` when `o.noY` is set, and it is the list of the
points in the order of ratpoints (`Ratpoints.orderedPoints`, with the bound `Ratpoints.maxDivisors`
of the model on the number of divisors), filtered by `o.noY`; no duplicates holds for every option,
the options of the output among them. With the exact check off, every element of the list is
`(x, 0, z)` for a normalized coprime pair of height at most `H`, every point `(x, y, z)` of height
at most `H` gives the element `(x, 0, z)`, and the points with `y ≥ 0` of the same search with the
exact check on, with `y` replaced by `0`, are a sublist of it, so that they come in the same order.
The search with a callback (`Ratpoints.findPointsWith`) refuses what `Ratpoints.findPoints` refuses,
and otherwise returns the data of the callback and the count of the delivery of the list of
`Ratpoints.findPoints` to the callback (`Ratpoints.Delivery.deliver`): the calls of the callback for
the points of the list in their order, up to and including the first that stops the search.
`Ratpoints.bruteForce`, `Ratpoints.findPoints`, `Ratpoints.findPointsWith`, `Ratpoints.Outcome`,
`Ratpoints.Answer`, `Ratpoints.Delivery`, `Ratpoints.Delivery.deliver`, `Ratpoints.Options`,
`Ratpoints.Params`, `Ratpoints.Params.WF`, `Ratpoints.SieveOptions`, `Ratpoints.sieveParams`,
`Ratpoints.maxDegree` and `Ratpoints.maxDivisors` come from the model, never restated, since a
definition of the model elaborates without Mathlib to other instance terms. Of Mathlib, the file
imports exactly the public imports of `Ratpoints/Spec/Basic.lean` and of `Ratpoints/Spec/Order.lean`
(`Mathlib.Data.Nat.Factors`, for the prime factors), so that the restated definitions elaborate to
the same terms as there.
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

/-- `(x, y, z)` is a point of height at most `H` on `y ^ 2 = F(x, z)`, `F = Ratpoints.binaryForm c`,
normalized as the program prints it: `gcd(x, z) = 1`, and `0 < z`, or `z = 0` and `x = 1`. -/
def IsPoint (c : List ℤ) (H : ℕ) (p : ℤ × ℤ × ℤ) : Prop :=
  p.2.1 ^ 2 = binaryForm c p.1 p.2.2 ∧ Int.gcd p.1 p.2.2 = 1 ∧
    (0 < p.2.2 ∨ p.2.2 = 0 ∧ p.1 = 1) ∧ |p.1| ≤ H ∧ p.2.2 ≤ H

instance instDecidablePredIsPoint (c : List ℤ) (H : ℕ) : DecidablePred (IsPoint c H) :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- The polynomial that ratpoints searches for the coefficient list `c` of degree `d`, and whether
it is reversed, when the switch `reverse` allows a reversal (the option `-k` of the program forbids
it): for even `d`, the list `c_d, …, c₀` when `c₀ = 0` (then `c₁ ≠ 0`, or the binary form is not
squarefree and refused) or when `c_d` is a square and `c₀` is not; for odd `d`, the list
`0, c_d, …, c₁` when `|c_d| ≠ 1`, `c₀ = 0` and `|c₁| = 1`; otherwise `c` itself. The binary form
of a reversed list is that of `c` with `x` and `z` exchanged, except for even `d` with
`c₀ = c₁ = 0`, which ratpoints refuses. -/
def searchedPoly (reverse : Bool) (c : List ℤ) : List ℤ × Bool :=
  let d := degree c
  if reverse ∧ d % 2 = 0 ∧
      (c.getD 0 0 = 0 ∨ IsSquare (c.getD d 0) ∧ ¬IsSquare (c.getD 0 0)) then
    ((c.take (d + 1)).reverse, true)
  else if reverse ∧ d % 2 = 1 ∧ (c.getD d 0).natAbs ≠ 1 ∧ c.getD 0 0 = 0 ∧
      (c.getD 1 0).natAbs = 1 then
    (0 :: (c.take (d + 1)).tail.reverse, true)
  else (c, false)

/-- Whether ratpoints factors `n` completely: it divides off `2` and the odd primes up to `1021` in
turn and takes a cofactor below `p ^ 2`, for the next prime `p`, as a prime, which it is; so it
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
for the height `H`: when `d` is odd, `|c_d| ≠ 1`, ratpoints factors `|c_d|` completely
(`Ratpoints.FactorsByTrialDivision`) and it has fewer than `maxDiv` squarefree divisors at most
`H` (`Ratpoints.binaryDivisors`), the numbers `e k ^ 2 ≤ H`, divisor `e` by divisor in that order
and `k = 1, 2, …` for each; otherwise `1, …, H`. This is the order of the loop of the search, which
visits those of them that its tests let through (for `d` odd and `|c_d| = 1` only the squares); the
others carry no point. -/
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

/-- The points of height at most `H` on `y ^ 2 = F(x, z)` for the coefficient list `c`, in the order
in which ratpoints finds them, for the switch `reverse` of the reversal and the bound `maxDiv` of
the number of divisors: for the polynomial searched (`Ratpoints.searchedPoly`), its points at
infinity, then the points of its denominators (`Ratpoints.searchDenominators`) in turn
(`Ratpoints.pointsWithDen`); after a reversal, each point `(a, y, b)` of that list becomes
`(b, y, a)` for `a ≥ 0` and `(-b, y, -a)` for `a < 0`, a point of the caller's curve. -/
def orderedPoints (maxDiv : ℕ) (reverse : Bool) (c : List ℤ) (H : ℕ) : List (ℤ × ℤ × ℤ) :=
  let (c', rev) := searchedPoly reverse c
  let L := (0 :: searchDenominators maxDiv c' H).flatMap (pointsWithDen c' H)
  if rev then L.map fun (a, y, b) ↦ if 0 ≤ a then (b, y, a) else (-b, y, -a) else L

end Ratpoints

theorem challenge_mem_bruteForce_iff (c : List ℤ) (H : ℕ) (p : ℤ × ℤ × ℤ) :
    p ∈ Ratpoints.bruteForce c H ↔ Ratpoints.IsPoint c H p :=
  sorry

theorem challenge_nodup_bruteForce (c : List ℤ) (H : ℕ) : (Ratpoints.bruteForce c H).Nodup :=
  sorry

theorem challenge_mem_iff_isPoint_of_findPoints_eq_ok (c : List ℤ) (H : ℕ) (P : Ratpoints.Params)
    (o : Ratpoints.Options) (L : List (ℤ × ℤ × ℤ)) (hP : P.WF) (hc : o.noCheck = false)
    (h : Ratpoints.findPoints c H P o = .ok L) (p : ℤ × ℤ × ℤ) :
    p ∈ L ↔ Ratpoints.IsPoint c H p ∧ (o.noY = true → 0 ≤ p.2.1) :=
  sorry

theorem challenge_nodup_of_findPoints_eq_ok (c : List ℤ) (H : ℕ) (P : Ratpoints.Params)
    (o : Ratpoints.Options) (L : List (ℤ × ℤ × ℤ)) (hP : P.WF)
    (h : Ratpoints.findPoints c H P o = .ok L) : L.Nodup :=
  sorry

theorem challenge_exists_findPoints_eq_error_iff_of_sturm_nonneg (c : List ℤ) (H : ℕ)
    (P : Ratpoints.Params) (o : Ratpoints.Options) (hs : 0 ≤ o.sturm) :
    (∃ e, Ratpoints.findPoints c H P o = .error e) ↔
      c.length < 2 ∨ Ratpoints.maxDegree + 1 < c.length ∨ H = 0 ∨ 2 ^ 63 ≤ H ∨
        ¬ Squarefree (Ratpoints.binaryFormPoly c) :=
  sorry

theorem challenge_exists_findPoints_eq_error_iff_of_sturm_neg (c : List ℤ) (H : ℕ)
    (P : Ratpoints.Params) (o : Ratpoints.Options) (hs : o.sturm < 0) :
    (∃ e, Ratpoints.findPoints c H P o = .error e) ↔
      c.length < 2 ∨ Ratpoints.maxDegree + 1 < c.length ∨ H = 0 ∨ 2 ^ 63 ≤ H ∨
        Ratpoints.degree c + 2 ≤ 2 * (c.length / 2) ∨
        o.reverse = true ∧ Ratpoints.degree c % 2 = 0 ∧ c.getD 0 0 = 0 ∧ c.getD 1 0 = 0 :=
  sorry

theorem challenge_wf_sieveParams (o : Ratpoints.SieveOptions) : (Ratpoints.sieveParams o).WF :=
  sorry

theorem challenge_eq_orderedPoints_of_findPoints_eq_ok (c : List ℤ) (H : ℕ)
    (P : Ratpoints.Params) (o : Ratpoints.Options) (L : List (ℤ × ℤ × ℤ)) (hP : P.WF)
    (hc : o.noCheck = false) (h : Ratpoints.findPoints c H P o = .ok L) :
    L = (Ratpoints.orderedPoints Ratpoints.maxDivisors o.reverse c H).filter
      fun p ↦ !o.noY || 0 ≤ p.2.1 :=
  sorry

theorem challenge_exists_eq_of_mem_of_findPoints_eq_ok_of_noCheck (c : List ℤ) (H : ℕ)
    (P : Ratpoints.Params) (o : Ratpoints.Options) (L : List (ℤ × ℤ × ℤ)) (hP : P.WF)
    (hc : o.noCheck = true) (h : Ratpoints.findPoints c H P o = .ok L) (q : ℤ × ℤ × ℤ)
    (hq : q ∈ L) :
    ∃ x z : ℤ, q = (x, 0, z) ∧ Int.gcd x z = 1 ∧ (0 < z ∨ z = 0 ∧ x = 1) ∧ |x| ≤ H ∧ z ≤ H :=
  sorry

theorem challenge_mem_of_isPoint_of_findPoints_eq_ok_of_noCheck (c : List ℤ) (H : ℕ)
    (P : Ratpoints.Params) (o : Ratpoints.Options) (L : List (ℤ × ℤ × ℤ)) (hP : P.WF)
    (hc : o.noCheck = true) (h : Ratpoints.findPoints c H P o = .ok L) (p : ℤ × ℤ × ℤ)
    (hp : Ratpoints.IsPoint c H p) : (p.1, 0, p.2.2) ∈ L :=
  sorry

theorem challenge_map_sublist_of_findPoints_eq_ok_of_noCheck (c : List ℤ) (H : ℕ)
    (P : Ratpoints.Params) (o : Ratpoints.Options) (L L' : List (ℤ × ℤ × ℤ)) (hP : P.WF)
    (hc : o.noCheck = true) (h : Ratpoints.findPoints c H P o = .ok L)
    (h' : Ratpoints.findPoints c H P { o with noCheck := false, noY := true } = .ok L') :
    (L'.map fun q ↦ (q.1, 0, q.2.2)).Sublist L :=
  sorry

theorem challenge_map_findPointsWith_eq_map_findPoints {σ : Type} (c : List ℤ) (H : ℕ)
    (P : Ratpoints.Params) (o : Ratpoints.Options) (process : ℤ → ℤ → ℤ → σ → Ratpoints.Answer σ)
    (info : σ) (hP : P.WF) :
    (Ratpoints.findPointsWith c H P o process info).map (fun r ↦ (r.info, r.total)) =
      (Ratpoints.findPoints c H P o).map fun L ↦
        let r := Ratpoints.Delivery.deliver process ⟨info, 0, false⟩ L; (r.info, r.total) :=
  sorry

end

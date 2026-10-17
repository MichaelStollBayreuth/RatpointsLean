/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Data.Fin.VecNotation
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
without the Sturm step; and the theorems of stage G on the options of the output and the protocol of
the delivery. Since stage G membership holds with the exact check on (`o.noCheck = false`): the list
of `Ratpoints.findPoints` holds exactly the points, of each pair `(x, ±y, z)` only the one with
`y ≥ 0` when `o.noY` is set; no duplicates holds for every option, the options of the output among
them. The search with a callback (`Ratpoints.findPointsWith`) refuses what `Ratpoints.findPoints`
refuses, and otherwise returns the data of the callback and the count of the delivery of the list of
`Ratpoints.findPoints` to the callback (`Ratpoints.Delivery.deliver`): the calls of the callback for
the points of the list in their order, up to and including the first that stops the search.
`Ratpoints.bruteForce`, `Ratpoints.findPoints`, `Ratpoints.findPointsWith`, `Ratpoints.Answer`,
`Ratpoints.Delivery`, `Ratpoints.Delivery.deliver`, `Ratpoints.Options`, `Ratpoints.Params`,
`Ratpoints.Params.WF`, `Ratpoints.SieveOptions`, `Ratpoints.sieveParams` and `Ratpoints.maxDegree`
come from the model, never restated, since a definition of the model elaborates without Mathlib to
other instance terms. Of Mathlib, the file imports exactly the public imports of
`Ratpoints/Spec/Basic.lean`, so that the restated definitions elaborate to the same terms as there.
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

theorem challenge_map_findPointsWith_eq_map_findPoints {σ : Type} (c : List ℤ) (H : ℕ)
    (P : Ratpoints.Params) (o : Ratpoints.Options) (process : ℤ → ℤ → ℤ → σ → Ratpoints.Answer σ)
    (info : σ) (hP : P.WF) :
    (Ratpoints.findPointsWith c H P o process info).map (fun r ↦ (r.info, r.total)) =
      (Ratpoints.findPoints c H P o).map fun L ↦
        let r := Ratpoints.Delivery.deliver process ⟨info, 0, false⟩ L; (r.info, r.total) :=
  sorry

end

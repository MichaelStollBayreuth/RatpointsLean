/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Fin.VecNotation
public import Ratpoints.Model

/-!
# Comparator challenge statements

The main theorems of the project, stated with `sorry` for
[leanprover/comparator](https://github.com/leanprover/comparator), over a verbatim restatement of
the specification. The file may import only Mathlib and the model (`scripts/check_layout.py`
checks this): the main theorems speak about the model's `findPoints`, which is trusted in the
sense that it is the code the executable runs, while the specification is reproduced here, so
that a solution that changed it would be rejected.

The statements come in stage by stage, as `comparator/README.md` lists them: the two theorems of
stage B (the brute-force reference finds exactly the points, without duplicates); then, from stage
C1 on, the membership and no-duplicates theorems for `findPoints` for well-formed parameters, the
refusal theorem, which rules out a `findPoints` that refuses every input (in its form of stage C1;
stage D adds the refusal of a form that is not squarefree), and the well-formedness of every
parameter set that the options of the program give, which rules out a well-formedness that nothing
satisfies. `findPoints`, `Params`, `Params.WF`, `SieveOptions`, `sieveParams` and `maxDegree` come
from the model, never restated, since a definition of the model elaborates without Mathlib to other
instance terms. The file imports exactly the public imports of `Ratpoints/Spec/Basic.lean`, so that
the restated definitions elaborate to the same terms as there.
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
    (L : List (ℤ × ℤ × ℤ)) (hP : P.WF) (h : Ratpoints.findPoints c H P = .ok L)
    (p : ℤ × ℤ × ℤ) : p ∈ L ↔ Ratpoints.IsPoint c H p :=
  sorry

theorem challenge_nodup_of_findPoints_eq_ok (c : List ℤ) (H : ℕ) (P : Ratpoints.Params)
    (L : List (ℤ × ℤ × ℤ)) (hP : P.WF) (h : Ratpoints.findPoints c H P = .ok L) : L.Nodup :=
  sorry

theorem challenge_exists_findPoints_eq_error_iff (c : List ℤ) (H : ℕ) (P : Ratpoints.Params) :
    (∃ e, Ratpoints.findPoints c H P = .error e) ↔
      c.length < 2 ∨ Ratpoints.maxDegree + 1 < c.length ∨ H = 0 :=
  sorry

theorem challenge_wf_sieveParams (o : Ratpoints.SieveOptions) : (Ratpoints.sieveParams o).WF :=
  sorry

end

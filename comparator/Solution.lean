/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints

/-!
# Comparator solutions

Proofs of the statements of `comparator/Challenge.lean` by the theorems of the library; see
`comparator/README.md`.
-/

@[expose] public section

theorem challenge_mem_bruteForce_iff (c : List ℤ) (H : ℕ) (p : ℤ × ℤ × ℤ) :
    p ∈ Ratpoints.bruteForce c H ↔ Ratpoints.IsPoint c H p :=
  Ratpoints.mem_bruteForce_iff

theorem challenge_nodup_bruteForce (c : List ℤ) (H : ℕ) : (Ratpoints.bruteForce c H).Nodup :=
  Ratpoints.nodup_bruteForce c H

theorem challenge_mem_iff_isPoint_of_findPoints_eq_ok (c : List ℤ) (H : ℕ) (P : Ratpoints.Params)
    (o : Ratpoints.Options) (L : List (ℤ × ℤ × ℤ)) (hP : P.WF)
    (h : Ratpoints.findPoints c H P o = .ok L) (p : ℤ × ℤ × ℤ) : p ∈ L ↔ Ratpoints.IsPoint c H p :=
  Ratpoints.mem_iff_isPoint_of_findPoints_eq_ok hP h

theorem challenge_nodup_of_findPoints_eq_ok (c : List ℤ) (H : ℕ) (P : Ratpoints.Params)
    (o : Ratpoints.Options) (L : List (ℤ × ℤ × ℤ)) (hP : P.WF)
    (h : Ratpoints.findPoints c H P o = .ok L) : L.Nodup :=
  Ratpoints.nodup_of_findPoints_eq_ok hP h

theorem challenge_exists_findPoints_eq_error_iff_of_sturm_nonneg (c : List ℤ) (H : ℕ)
    (P : Ratpoints.Params) (o : Ratpoints.Options) (hs : 0 ≤ o.sturm) :
    (∃ e, Ratpoints.findPoints c H P o = .error e) ↔
      c.length < 2 ∨ Ratpoints.maxDegree + 1 < c.length ∨ H = 0 ∨
        ¬ Squarefree (Ratpoints.binaryFormPoly c) :=
  Ratpoints.exists_findPoints_eq_error_iff_of_sturm_nonneg hs

theorem challenge_exists_findPoints_eq_error_iff_of_sturm_neg (c : List ℤ) (H : ℕ)
    (P : Ratpoints.Params) (o : Ratpoints.Options) (hs : o.sturm < 0) :
    (∃ e, Ratpoints.findPoints c H P o = .error e) ↔
      c.length < 2 ∨ Ratpoints.maxDegree + 1 < c.length ∨ H = 0 ∨
        Ratpoints.degree c + 2 ≤ 2 * (c.length / 2) ∨
        o.reverse = true ∧ Ratpoints.degree c % 2 = 0 ∧ c.getD 0 0 = 0 ∧ c.getD 1 0 = 0 :=
  Ratpoints.exists_findPoints_eq_error_iff_of_sturm_neg hs

theorem challenge_wf_sieveParams (o : Ratpoints.SieveOptions) : (Ratpoints.sieveParams o).WF :=
  Ratpoints.wf_sieveParams o

end

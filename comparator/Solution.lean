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

theorem challenge_mem_fastPoints_iff (c : List ℤ) (H : ℕ) (bLow bHigh : ℤ)
    (tu : Ratpoints.Fast.Tuning) (p : ℤ × ℤ × ℤ) :
    p ∈ Ratpoints.Fast.fastPoints c H bLow bHigh tu ↔
      Ratpoints.IsPoint c H p ∧ Ratpoints.InRegion [] bLow bHigh p :=
  Ratpoints.Fast.mem_fastPoints_iff

theorem challenge_nodup_fastPoints (c : List ℤ) (H : ℕ) (bLow bHigh : ℤ)
    (tu : Ratpoints.Fast.Tuning) : (Ratpoints.Fast.fastPoints c H bLow bHigh tu).Nodup :=
  Ratpoints.Fast.nodup_fastPoints c H bLow bHigh tu

theorem challenge_mem_iff_isPoint_of_findPoints_eq_ok (c : List ℤ) (H : ℕ)
    (s : Ratpoints.SieveOptions) (o : Ratpoints.Options) (L : List (ℤ × ℤ × ℤ))
    (hS : 0 ≤ o.sturm → Ratpoints.SturmTheorem) (hc : o.noCheck = false)
    (h : Ratpoints.findPoints c H s o = .ok L) (p : ℤ × ℤ × ℤ) :
    p ∈ L ↔ Ratpoints.IsPoint c H p ∧ (o.noY = true → 0 ≤ p.2.1) ∧
      Ratpoints.InRegion
        (o.domain.map fun i ↦ (Ratpoints.doubleValue i.1.bits, Ratpoints.doubleValue i.2.bits))
        o.bLow o.bHigh p :=
  Ratpoints.mem_iff_isPoint_of_findPoints_eq_ok hS h hc

theorem challenge_nodup_of_findPoints_eq_ok (c : List ℤ) (H : ℕ) (s : Ratpoints.SieveOptions)
    (o : Ratpoints.Options) (L : List (ℤ × ℤ × ℤ)) (h : Ratpoints.findPoints c H s o = .ok L) :
    L.Nodup :=
  Ratpoints.nodup_of_findPoints_eq_ok h

theorem challenge_exists_findPoints_eq_error_iff_of_sturm_nonneg (c : List ℤ) (H : ℕ)
    (s : Ratpoints.SieveOptions) (o : Ratpoints.Options) (hs : 0 ≤ o.sturm) :
    (∃ e, Ratpoints.findPoints c H s o = .error e) ↔
      c.length < 2 ∨ Ratpoints.maxDegree + 1 < c.length ∨ H = 0 ∨ 2 ^ 63 ≤ H ∨
        ¬ Squarefree (Ratpoints.binaryFormPoly c) ∨
        ¬ Ratpoints.IntervalsWF (o.domain.map fun i ↦ (i.1.bits, i.2.bits)) :=
  Ratpoints.exists_findPoints_eq_error_iff_of_sturm_nonneg hs

theorem challenge_exists_findPoints_eq_error_iff_of_sturm_neg (c : List ℤ) (H : ℕ)
    (s : Ratpoints.SieveOptions) (o : Ratpoints.Options) (hs : o.sturm < 0) :
    (∃ e, Ratpoints.findPoints c H s o = .error e) ↔
      c.length < 2 ∨ Ratpoints.maxDegree + 1 < c.length ∨ H = 0 ∨ 2 ^ 63 ≤ H ∨
        Ratpoints.degree c + 2 ≤ 2 * (c.length / 2) ∨
        o.reverse = true ∧ Ratpoints.IsFullBox o.domain o.bLow o.bHigh H ∧
          Ratpoints.degree c % 2 = 0 ∧ c.getD 0 0 = 0 ∧ c.getD 1 0 = 0 ∨
        ¬ Ratpoints.IntervalsWF (o.domain.map fun i ↦ (i.1.bits, i.2.bits)) :=
  Ratpoints.exists_findPoints_eq_error_iff_of_sturm_neg hs

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
  Ratpoints.eq_orderedPoints_of_findPoints_eq_ok hS h hc

theorem challenge_isNormalizedPair_of_mem_of_findPoints_eq_ok_of_noCheck (c : List ℤ) (H : ℕ)
    (s : Ratpoints.SieveOptions) (o : Ratpoints.Options) (L : List (ℤ × ℤ × ℤ))
    (hc : o.noCheck = true) (h : Ratpoints.findPoints c H s o = .ok L) (q : ℤ × ℤ × ℤ)
    (hq : q ∈ L) :
    q.2.1 = 0 ∧ Ratpoints.IsNormalizedPair H q.1 q.2.2 ∧
      Ratpoints.InRegion
        (o.domain.map fun i ↦ (Ratpoints.doubleValue i.1.bits, Ratpoints.doubleValue i.2.bits))
        o.bLow o.bHigh q :=
  Ratpoints.isNormalizedPair_of_mem_of_findPoints_eq_ok_of_noCheck h hc hq

theorem challenge_mem_of_isPoint_of_findPoints_eq_ok_of_noCheck (c : List ℤ) (H : ℕ)
    (s : Ratpoints.SieveOptions) (o : Ratpoints.Options) (L : List (ℤ × ℤ × ℤ))
    (hS : 0 ≤ o.sturm → Ratpoints.SturmTheorem) (hc : o.noCheck = true)
    (h : Ratpoints.findPoints c H s o = .ok L) (p : ℤ × ℤ × ℤ) (hp : Ratpoints.IsPoint c H p)
    (hr : Ratpoints.InRegion
      (o.domain.map fun i ↦ (Ratpoints.doubleValue i.1.bits, Ratpoints.doubleValue i.2.bits))
      o.bLow o.bHigh p) :
    (p.1, 0, p.2.2) ∈ L :=
  Ratpoints.mem_of_isPoint_of_findPoints_eq_ok_of_noCheck hS h hc hp hr

theorem challenge_map_sublist_of_findPoints_eq_ok_of_noCheck (c : List ℤ) (H : ℕ)
    (s : Ratpoints.SieveOptions) (o : Ratpoints.Options) (L L' : List (ℤ × ℤ × ℤ))
    (hc : o.noCheck = true) (h : Ratpoints.findPoints c H s o = .ok L)
    (h' : Ratpoints.findPoints c H s { o with noCheck := false, noY := true } = .ok L') :
    (L'.map fun q ↦ (q.1, 0, q.2.2)).Sublist L :=
  Ratpoints.map_sublist_of_findPoints_eq_ok_of_noCheck h hc h'

theorem challenge_map_findPointsWith_eq_map_findPoints {σ : Type} (c : List ℤ) (H : ℕ)
    (s : Ratpoints.SieveOptions) (o : Ratpoints.Options)
    (process : ℤ → ℤ → ℤ → σ → Ratpoints.Answer σ) (info : σ) :
    (Ratpoints.findPointsWith c H s o process info).map (fun r ↦ (r.info, r.total)) =
      (Ratpoints.findPoints c H s o).map fun L ↦
        let r := Ratpoints.Delivery.deliver process ⟨info, 0, false⟩ L; (r.info, r.total) :=
  Ratpoints.map_findPointsWith_eq_map_findPoints c H s o process info

end

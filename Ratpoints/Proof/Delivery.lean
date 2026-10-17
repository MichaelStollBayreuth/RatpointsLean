/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.Delivery

/-!
# The delivery of a list of points

The reference of the delivery of a search, `Ratpoints.Delivery.deliver`, the fold over a list of
points that calls the callback for each of them while the flag of the stop is clear: its unfolding
on the empty list, on a point in front and on a concatenation; a delivery whose flag is set is
left as it is, whatever the list, so that the delivery of a list is that of a prefix of it once the
flag is set after the prefix; with the appending callback `Ratpoints.appendPoint` the array of the
data grows by the list and the count by its length; and in general the calls made are those of the
points of a prefix of the list, before each of which the flag is clear, the whole list or the
prefix up to and including the first point whose call sets the flag.

## Main statements

* `Ratpoints.Delivery.deliver_nil`, `Ratpoints.Delivery.deliver_cons`,
  `Ratpoints.Delivery.deliver_append`, `Ratpoints.Delivery.deliver_flatMap`: the unfolding.
* `Ratpoints.Delivery.deliver_of_quit`, `Ratpoints.Delivery.deliver_append_of_quit`,
  `Ratpoints.Delivery.deliver_eq_of_prefix`, `Ratpoints.Delivery.ite_quit_eq_deliver_append`:
  nothing changes once the flag is set.
* `Ratpoints.Delivery.deliver_appendPoint`: the appending callback.
* `Ratpoints.Delivery.exists_prefix_deliver_eq`, `Ratpoints.Delivery.deliver_eq_foldl_call`: the
  calls made are those of a prefix of the list, up to and including the first call that sets the
  flag, and on such a prefix every point gets its call.

## Implementation notes

The file uses Lean core only, so that the contracts of the sieve in the files without Mathlib
(`Ratpoints.Proof.Stages`, `Ratpoints.Proof.Scan`, `Ratpoints.Proof.Sift`) can state what they
deliver with it; the count as the sum of the values that the calls return is in
`Ratpoints.Proof.DeliveryCount`.
-/

@[expose] public section

namespace Ratpoints.Delivery

variable {σ : Type} (process : Int → Int → Int → σ → Answer σ)

/-! ### The unfolding -/

@[simp]
theorem deliver_nil (r : Delivery σ) : r.deliver process [] = r :=
  rfl

theorem deliver_cons (r : Delivery σ) (p : Int × Int × Int) (L : List (Int × Int × Int)) :
    r.deliver process (p :: L) =
      (if r.quit then r else r.call process p.1 p.2.2 p.2.1).deliver process L :=
  rfl

theorem deliver_append (r : Delivery σ) (L₁ L₂ : List (Int × Int × Int)) :
    r.deliver process (L₁ ++ L₂) = (r.deliver process L₁).deliver process L₂ :=
  List.foldl_append

theorem deliver_flatMap {α : Type} (r : Delivery σ) (l : List α)
    (f : α → List (Int × Int × Int)) :
    r.deliver process (l.flatMap f) = l.foldl (fun r a ↦ r.deliver process (f a)) r :=
  List.foldl_flatMap

theorem deliver_cons_of_quit_eq_false {r : Delivery σ} (h : r.quit = false)
    (p : Int × Int × Int) (L : List (Int × Int × Int)) :
    r.deliver process (p :: L) = (r.call process p.1 p.2.2 p.2.1).deliver process L := by
  simp [deliver_cons, h]

theorem deliver_singleton_of_quit_eq_false {r : Delivery σ} (h : r.quit = false)
    (p : Int × Int × Int) :
    r.deliver process [p] = r.call process p.1 p.2.2 p.2.1 := by
  simp [deliver_cons_of_quit_eq_false process h]

/-! ### The stop -/

/-- A delivery whose flag is set is left as it is: the callback is not called again. -/
@[simp]
theorem deliver_of_quit {r : Delivery σ} (h : r.quit = true) (L : List (Int × Int × Int)) :
    r.deliver process L = r := by
  induction L with
  | nil => rfl
  | cons p L ih => simp [deliver_cons, h, ih]

/-- Once a call has set the flag, the points that follow are passed over. -/
theorem deliver_append_of_quit {r : Delivery σ} {L₁ : List (Int × Int × Int)}
    (h : (r.deliver process L₁).quit = true) (L₂ : List (Int × Int × Int)) :
    r.deliver process (L₁ ++ L₂) = r.deliver process L₁ :=
  (deliver_append ..).trans (deliver_of_quit process h _)

/-- Once a call has set the flag, the delivery of a list is that of a prefix of it after which the
flag is set: the points that follow are passed over. -/
theorem deliver_eq_of_prefix {r : Delivery σ} {M L : List (Int × Int × Int)} (h : M <+: L)
    (hq : (r.deliver process M).quit = true) :
    r.deliver process L = r.deliver process M :=
  h.elim fun t ht ↦ ht ▸ deliver_append_of_quit process hq t

/-- `Ratpoints.Delivery.deliver_eq_of_prefix` for the concatenations of the lists `f a` of the
elements `a` of a prefix `l₁` of `l₂`. -/
theorem deliver_flatMap_eq_of_prefix {α : Type} {r : Delivery σ} {l₁ l₂ : List α}
    (h : l₁ <+: l₂) (f : α → List (Int × Int × Int))
    (hq : (r.deliver process (l₁.flatMap f)).quit = true) :
    r.deliver process (l₂.flatMap f) = r.deliver process (l₁.flatMap f) := by
  obtain ⟨t, rfl⟩ := h
  rw [List.flatMap_append]
  exact deliver_append_of_quit process hq _

/-- The delivery `r₁` of the points of `L₁`, followed, unless the callback has stopped the search,
by a delivery `r₂` of the points of `L₂` from `r₁`, is the delivery of the points of `L₁ ++ L₂`. -/
theorem ite_quit_eq_deliver_append {r r₁ r₂ : Delivery σ} {L₁ L₂ : List (Int × Int × Int)}
    (h₁ : r₁ = r.deliver process L₁) (h₂ : r₁.quit = false → r₂ = r₁.deliver process L₂) :
    (if r₁.quit then r₁ else r₂) = r.deliver process (L₁ ++ L₂) := by
  rw [deliver_append, ← h₁]
  cases hq : r₁.quit
  · simp [h₂ hq]
  · simp [deliver_of_quit process hq]

/-! ### The appending callback -/

@[simp]
theorem deliver_appendPoint (arr : Array (Int × Int × Int)) (n : Int)
    (L : List (Int × Int × Int)) :
    (⟨arr, n, false⟩ : Delivery _).deliver appendPoint L =
      ⟨arr ++ L.toArray, n + L.length, false⟩ := by
  induction L generalizing arr n with
  | nil => simp
  | cons p L ih =>
    rw [deliver_cons_of_quit_eq_false appendPoint rfl]
    simp only [call, appendPoint, ih, List.length_cons, Delivery.mk.injEq, and_true]
    exact ⟨by simp, by lia⟩

/-! ### The calls made and the count -/

/-- On a list before each of whose points the flag is clear, every point gets its call. -/
theorem deliver_eq_foldl_call {r : Delivery σ} {M : List (Int × Int × Int)}
    (h : ∀ m < M.length, (r.deliver process (M.take m)).quit = false) :
    r.deliver process M = M.foldl (fun r p ↦ r.call process p.1 p.2.2 p.2.1) r := by
  induction M generalizing r with
  | nil => rfl
  | cons p M ih =>
    have h0 : r.quit = false := h 0 (by simp)
    rw [deliver_cons_of_quit_eq_false process h0, List.foldl_cons]
    refine ih fun m hm ↦ ?_
    simpa [deliver_cons_of_quit_eq_false process h0] using h (m + 1) (by simpa using hm)

/-- The calls that the delivery of `L` makes are those of the points of a prefix `M` of `L`: the
flag is clear before each point of `M`, so that each gets its call
(`Ratpoints.Delivery.deliver_eq_foldl_call`), and unless `M` is all of `L`, the flag is set after
them, by the call of the last point of `M`, or at the start when `M` is empty. -/
theorem exists_prefix_deliver_eq (r : Delivery σ) (L : List (Int × Int × Int)) :
    ∃ M, M <+: L ∧ r.deliver process L = r.deliver process M ∧
      (∀ m < M.length, (r.deliver process (M.take m)).quit = false) ∧
      (M ≠ L → (r.deliver process M).quit = true) := by
  induction L generalizing r with
  | nil => exact ⟨[], List.prefix_rfl, rfl, by simp, by simp⟩
  | cons p L ih =>
    cases h0 : r.quit
    · obtain ⟨M, hML, hL, hM, hq⟩ := ih (r.call process p.1 p.2.2 p.2.1)
      refine ⟨p :: M, List.cons_prefix_cons.mpr ⟨rfl, hML⟩, ?_, fun m hm ↦ ?_, fun hne ↦ ?_⟩
      · simpa [deliver_cons_of_quit_eq_false process h0] using hL
      · cases m with
        | zero => simpa using h0
        | succ m => simpa [deliver_cons_of_quit_eq_false process h0] using hM m (by simpa using hm)
      · simpa [deliver_cons_of_quit_eq_false process h0] using hq (by simpa using hne)
    · exact ⟨[], List.nil_prefix, deliver_of_quit process h0 _, by simp, fun _ ↦ by simpa⟩

end Ratpoints.Delivery

end

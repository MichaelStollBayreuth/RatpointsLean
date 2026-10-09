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

end

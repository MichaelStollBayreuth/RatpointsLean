/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

/-!
# The remainder chain of the Sturm step

The test of the Sturm step of ratpoints for a repeated factor of the polynomial `f`: the remainder
chain of `f` and its derivative `f'`, computed in integers as `sturm.c` computes it, row by row and
with its loops (`Ratpoints.Sturm.chain`). A remainder is zero exactly when `f` has a repeated
factor; the chain is `none` then, and ratpoints refuses the form as not squarefree, as
`Ratpoints.findPoints` does with the Sturm step on. The rest of the Sturm step, which restricts the
numerators to the intervals where `f ≥ 0`, is not modelled yet (stage H).

## Main definitions

* `Ratpoints.Sturm.reduce`: one reduction of a remainder by the row before it, which cancels its
  leading coefficient.
* `Ratpoints.Sturm.chain`: the remainder chain of `f` and `f'`, or `none` when a remainder is zero.
-/

@[expose] public section

namespace Ratpoints

namespace Sturm

/-- One reduction of `t` by `s`, for `deg t ≥ deg s`, each given by the array of its coefficients up
to its degree, constant term first: `u t - v X^(deg t - deg s) s`, where `u` and `v` are the leading
coefficients of `s` and `t` divided by their positive gcd and signed so that `u > 0`; the leading
coefficient of the result is `0`. -/
def reduce (s t : Array Int) : Array Int :=
  let d1 := s.size - 1
  let d2 := t.size - 1
  let g : Int := (Int.gcd s.back! t.back! : Nat)
  let u0 := s.back! / g
  let v0 := t.back! / g
  let u := if u0 < 0 then -u0 else u0
  let v := if u0 < 0 then -v0 else v0
  (Array.range (d2 + 1)).map fun n ↦
    if n < d2 - d1 then u * t[n]! else u * t[n]! - v * s[n - (d2 - d1)]!

/-- The remainder chain of the polynomial `f` of degree `d ≥ 1` with the coefficients
`c₀, …, c_d`, the entries of `c`, and `c_d ≠ 0`, in rows of integers: `s₀ = f`, `s₁ = f'`, and for
`k = 2, …, d` the row `s_k` from the remainder `t` of `s_(k-2)` by `s_(k-1)`. Starting from
`t = s_(k-2)`, while the degree of `t` is at least that of `s_(k-1)`, `t` is reduced by `s_(k-1)`
(`Ratpoints.Sturm.reduce`) and its zero leading coefficients are dropped; the chain is `none` when
`t` becomes zero, which happens exactly when `f` has a repeated factor
(`Ratpoints.Sturm.run_chain_eq_none_iff`). Otherwise `s_k` is `-t` divided by the gcd of its
coefficients, whose loop stops when the gcd is `1`, and the chain ends when `s_k` is constant. Each
row is the array of its coefficients up to its degree, constant term first; for `d = 1` the loop
over `k` does not run, and the chain is `f, f'`.

C: `sturm.c:99-163`

Deviation: the rows as arrays of their coefficients up to their degree, for the table of `(d + 1)^2`
GMP integers and the array of degrees, with no `mpz_init` and `mpz_clear` (a chain has at most
`d + 1` rows, `Ratpoints.Sturm.IsChain.size_le`, and its row `k + 1` at most `d - k` entries,
`Ratpoints.Sturm.IsChain.size_getElem!_add_one_add_le`): an array has one entry more than the degree
of its row, and a remainder that becomes zero is the empty array, where the degree in the C code
reaches `-1`; a reduction step drops the leading coefficient, which it makes `0`, where the C code
lowers the degree; the rows are handed back, and `none` for the return of `-1`, where
`_ratpoints_compute_sturm` keeps them in its table for the rest of the Sturm step (stage H), and the
index of the last row, which the C code leaves in `k` and sets to `d` after the loop for `d = 1`, is
the size of the array less one; a list of integers for the array of GMP integers of the
coefficients, local values for the scratch integers `work[0]`, `work[1]` and `work[2]`, and Lean's
`/` for `mpz_fdiv_q`, which agree on the divisions of the chain, all exact. -/
def chain (c : List Int) (d : Nat) : Id (Option (Array (Array Int))) := do
  let f : Array Int := (Array.range (d + 1)).map (c.getD · 0)
  let df : Array Int := (Array.range d).map fun n ↦ ((n + 1 : Nat) : Int) * c.getD (n + 1) 0
  let mut rows := #[f, df]
  for k in [2:d + 1] do
    let s := rows[k - 1]!
    let mut t := rows[k - 2]!
    while s.size ≤ t.size do
      t := (reduce s t).pop
      while t.back? == some 0 do t := t.pop
      if t.size = 0 then return none
    t := t.map (- ·)
    let mut g := 0
    for a in t do
      g := Nat.gcd g a.natAbs
      if g = 1 then break
    if g ≠ 1 then t := t.map (· / (g : Int))
    rows := rows.push t
    if t.size = 1 then break
  return some rows

/-! ### Examples -/

-- The rows of the chain against those that the C code at the pinned commit computes, printed by a
-- build of it instrumented to write out its table of the chain: for `3 + 2x` and
-- `1 + 2x + 3x ^ 2`; for `x ^ 3 - 2`, whose derivative has zero coefficients below its degree; for
-- `x ^ 12 + 1`, whose first remainder drops eleven zero coefficients after one reduction; for
-- polynomials of degree 6 and 12 with small coefficients; and for a polynomial of degree 4 with
-- coefficients of 70 bits.
#guard Id.run (chain [3, 2] 1) == some #[#[3, 2], #[2]]
#guard Id.run (chain [1, 2, 3] 2) == some #[#[1, 2, 3], #[2, 6], #[-1]]
#guard Id.run (chain [-2, 0, 0, 1] 3) == some #[#[-2, 0, 0, 1], #[0, 0, 3], #[1]]
#guard Id.run (chain [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] 12) ==
  some #[#[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12], #[-1]]
#guard Id.run (chain [1, -3, 0, 5, 2, -1, 4] 6) ==
  some #[#[1, -3, 0, 5, 2, -1, 4], #[-3, 0, 15, 8, -5, 24], #[-141, 360, -15, -368, -91],
    #[-8921, 25356, -7290, -23966], #[496649, -1172729, 269088], #[-49748239, 105235135], #[-1]]
#guard Id.run (chain [2, -1, 3, 0, -4, 1, 1, -2, 5, 0, 3, -1, 2] 12) ==
  some #[#[2, -1, 3, 0, -4, 1, 1, -2, 5, 0, 3, -1, 2],
    #[-1, 6, 0, -16, 5, 6, -14, 40, 0, 30, -11, 24],
    #[-575, 258, -720, 16, 763, -174, -130, 200, -480, -30, -133],
    #[-4297, 7960, -8317, 9084, 5299, -10144, 1803, 500, -5855, 3250],
    #[111239, -88670, 129479, -51258, -188013, 95378, 47239, -37650, 112885],
    #[-2439876, -6091220, 1760054, -19241828, 7067107, 4222068, -6355356, 14786680],
    #[-2424273052, 1406241100, -3746621942, 1084215784, 993254009, -821932394, -422045132],
    #[-130006268140, 135659934684, -236634150598, 156944360512, 24554040017, -70048221478],
    #[68783562254788, -34292889600876, 141878557171874, -37126415186292, 32209855661673],
    #[176570853748085, -3971981398746906, 1122760637623987, -7060821883560798],
    #[-29402021058230050567, 6696486453425578104, -51323577542404194557],
    #[-358926259923835158391, -582835008182379573626], #[1]]
#guard Id.run (chain [1150092013148293430274, -917191792855797489172, 1076517816789853128035,
    -1112533756463107743172, -159651315419584027538] 4) ==
  some #[#[1150092013148293430274, -917191792855797489172, 1076517816789853128035,
      -1112533756463107743172, -159651315419584027538],
    #[-917191792855797489172, 2153035633579706256070, -3337601269389323229516,
      -638605261678336110152],
    #[-494778259343239271161457560331419626137522, 519061916985381776446645105152951960484559,
      -636016745249336385621049668351111547060924],
    #[-1320514644362970048267102006596489210639285984427475928620543058408386120279245622586,
      316321408849073697612788777530870776056936461666231844513276181529277582337567078771], #[1]]

-- The chain is `none`, as in the C code, for `(x + 1) ^ 2` and for
-- `(3x ^ 2 + x - 5) ^ 2 (2x ^ 3 - x + 7)`, whose remainder is zero after six rows.
#guard (Id.run (chain [1, 2, 1] 2)).isNone
#guard (Id.run (chain [175, -95, -193, 121, 37, -67, 12, 18] 7)).isNone

end Sturm

end Ratpoints

end

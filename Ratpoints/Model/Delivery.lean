/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

/-!
# The delivery of the points to the callback

The library function `find_points` of ratpoints hands each point it finds to a callback of the
caller, `int process(long x, long z, const mpz_t y, void *info, int *quit)`: the caller's data
`info` goes along unchanged, the library adds the value that `process` returns to its count `total`,
which `find_points` returns, and `process` stops the search by setting `*quit`, which the library
tests after each call and which is clear at every call. The model gives the callback the coordinates
in the order of the C code, `x`, `z`, `y`, and the data, and the callback returns what the call
gives (`Ratpoints.Answer`): its value, whether it set `*quit`, and the data afterwards. The search
threads a delivery (`Ratpoints.Delivery`), the data, the count and the flag, through the components
that the C code passes `process` and `info` through, and each component tests the flag where the C
code tests `*quit`. What the exact check and the points at infinity read of the flags of the search
to decide what they deliver, the bits `RATPOINTS_REVERSED`, `RATPOINTS_NO_CHECK` and
`RATPOINTS_NO_Y`, is `Ratpoints.CheckFlags`.

## Main definitions

* `Ratpoints.Answer`: what one call of the callback gives.
* `Ratpoints.Delivery`, `Ratpoints.Delivery.call`: the data, the count and the flag of the stop of
  a search, and one call of the callback.
* `Ratpoints.CheckFlags`, `Ratpoints.Delivery.callMapped`: the bits of the flags that decide what
  the exact check and the points at infinity deliver, and one call of the callback with a point of
  the polynomial searched, mapped back to the caller's curve after a reversal.
* `Ratpoints.appendPoint`: the callback that appends each point to an array.
* `Ratpoints.Delivery.deliver`: the calls of the callback for the points of a list, in their order,
  up to the first call that stops the search, the reference of the delivery of a search.
-/

@[expose] public section

namespace Ratpoints

/-- What one call `process(x, z, y, info, &quit)` of the callback of `find_points` gives: the value
`weight` that it returns, which the library adds to its count `total` ("the return value is taken
as a weight for counting the points; usually it will be 1", says the manual), whether it set
`*quit` to stop the search, and the data behind `info` after the call.

C: `ratpoints.h:436-437`, `ratpoints.h:441-442`

Deviation: the result of the call returned as a value, for the `int` that `process` returns, the
`int` that it writes through the pointer `quit`, which the library clears before the search and
tests after each call, so that it is clear at every call and the callback takes no argument for it,
and the data that it may change through the pointer `info`; an integer for the `int`, with no
bound, so that the count of a search has no range obligation (`Ratpoints.Delivery`); a Boolean for
the `int` `*quit`. -/
structure Answer (σ : Type) where
  /-- The value that `process` returns, the weight of the point in the count. -/
  weight : Int
  /-- Whether `process` set `*quit`, to stop the search. -/
  quit : Bool
  /-- The data behind `info` after the call. -/
  info : σ

/-- The state of the delivery of a search: the data `info` of the callback, the count `total`, the
sum of the values that the calls of the callback returned so far, and the flag `quit`, whether a
call has stopped the search. The search starts with `total = 0` and `quit` clear
(`find_points.c:4570-4571`, `find_points.c:3129`), and its components test `quit` after each call of
the callback, where the C code tests `*quit`, and return at once when it is set. One value stands
for what the C code keeps apart: the pointer `info`, which the library hands on unchanged; the
counts `total` that each function of the search keeps from zero and returns, which its caller adds
to its own, as one running count, their sum; and the flag, the local `quit` of `find_points_work_1`
for the points at infinity and the field `quit` of the sieving thread for the sieve (`wk->quit`,
which `worker_init` clears). The count is an integer for the `long` `total`, with no range
obligation, since the weights that the callback returns are arbitrary `int`s (for the callback of
the program, of the weights `0` and `1`, the count is at most the number of calls). -/
structure Delivery (σ : Type) where
  /-- The data of the callback, behind `info`. -/
  info : σ
  /-- The sum of the values that the calls of the callback returned so far. -/
  total : Int
  /-- Whether a call of the callback has stopped the search. -/
  quit : Bool

variable {σ : Type}

/-- One call `total += process(x, z, y, info, &quit)` of the callback `process` with the point
`(x : y : z)`, on the delivery `r`, whose flag `quit` is clear: the count grows by the value that
the call returns, and the flag and the data are those that the call leaves. The callers make the
call only while the flag is clear, as the C code does. -/
def Delivery.call (process : Int → Int → Int → σ → Answer σ) (r : Delivery σ) (x z y : Int) :
    Delivery σ :=
  let a := process x z y r.info
  { info := a.info, total := r.total + a.weight, quit := a.quit }

/-- The bits of the flags of a search (`args->flags`) that decide what the exact check and the
points at infinity deliver: `RATPOINTS_REVERSED`, which the reversal check sets when it reverses the
polynomial, so that each point of the polynomial searched goes to the callback mapped back to the
caller's curve; `RATPOINTS_NO_CHECK`, the option of the caller to have every numerator that passes
the sieve delivered without the exact check, with `y = 0`; and `RATPOINTS_NO_Y`, the option to have
only the point with `y ≥ 0` of a pair `(x : ±y : z)` delivered.

C: `ratpoints.h:414`

Deviation: a structure with a Boolean for each of the three bits, for the bits of the word `flags`
of the arguments, which `_ratpoints_check_point` reads through its worker and `find_points_work_1`
directly; `RATPOINTS_REVERSED` copied from the reversal check (`Ratpoints.Setup.reversal`) and, with
stage G, the bits `RATPOINTS_NO_CHECK` and `RATPOINTS_NO_Y` from the options of the search
(`Ratpoints.Options`). -/
structure CheckFlags where
  /-- `RATPOINTS_REVERSED`: the reversal check has reversed the polynomial. -/
  reversed : Bool := false
  /-- `RATPOINTS_NO_CHECK`: no exact check; every numerator that passes the sieve is delivered,
  with `y = 0`. -/
  noCheck : Bool := false
  /-- `RATPOINTS_NO_Y`: only the point with `y ≥ 0` of a pair is delivered. -/
  noY : Bool := false

/-- One call of the callback `process` with the point `(a : y : b)` of the polynomial searched, on
the delivery `r`, mapped back to the caller's curve when `reversed` is set: with `(b : y : a)` for
`a ≥ 0` and `(-b : y : -a)` for `a < 0` (as `Ratpoints.Sieve.swapPoint` maps the point), and
otherwise with `(a : y : b)` itself. These are the three branches that `_ratpoints_check_point`
writes at each of its calls of `process` (`find_points.c:5312-5316`, `find_points.c:5321-5325`,
`find_points.c:5331-5335`), one definition here; the negations stay `long`s for a numerator and a
denominator of a height bound below `2 ^ 63`. -/
def Delivery.callMapped (process : Int → Int → Int → σ → Answer σ) (r : Delivery σ)
    (reversed : Bool) (a b y : Int) : Delivery σ :=
  if reversed then
    if 0 ≤ a then r.call process b a y else r.call process (-b) (-a) y
  else r.call process a b y

/-- The callback that appends each point `(x, y, z)` to the array of its data, with the weight `1`,
and never stops the search: with it, the data of a search is the list of the points it delivers, in
their order, and its count their number (`Ratpoints.findPoints`). It is a callback of the model: the
program `ratpoints` prints the points in its callback `process` (in `Ratpoints.Cli` with stage G),
and the collector of the threads of the library is another (`collect`, stage I). -/
def appendPoint (x z y : Int) (pts : Array (Int × Int × Int)) : Answer (Array (Int × Int × Int)) :=
  ⟨1, false, pts.push (x, y, z)⟩

/-- The delivery of the points of the list `L`, in their order, to the callback `process` on the
delivery `r`: for each point `(x, y, z)` of `L`, while the flag `quit` is clear, the call with
`(x : y : z)` (`Ratpoints.Delivery.call`); the points after a call that sets the flag, and all of
them when it is set at the start, are passed over. So the calls made are those of the points of `L`
up to and including the first at which the callback stops the search, the count grows by the sum of
the values that they return, and with the callback that appends each point to an array and never
stops the search (`Ratpoints.appendPoint`) the array grows by `L` and the count by its length. It is
a reference of the model, as the brute-force reference `Ratpoints.bruteForce` is, and models no C
code: the search with a callback (`Ratpoints.findPointsWith`) delivers each point where it finds it
and tests the flag where the C code tests `*quit`, and this fold over the list of the points of the
search (`Ratpoints.findPoints`) is what that delivery is compared with. -/
def Delivery.deliver (process : Int → Int → Int → σ → Answer σ) (r : Delivery σ)
    (L : List (Int × Int × Int)) : Delivery σ :=
  L.foldl (fun r p ↦ if r.quit then r else r.call process p.1 p.2.2 p.2.1) r

/-! ### Examples -/

-- One call with the appending callback adds the point, `1` to the count and does not stop; the
-- mapped call after a reversal passes `(b : y : a)` for `a ≥ 0` and `(-b : y : -a)` for `a < 0`.
#guard
  let r : Delivery (Array (Int × Int × Int)) := ⟨#[(1, 0, 0)], 1, false⟩
  (r.call appendPoint 3 1 5).info == #[(1, 0, 0), (3, 5, 1)] &&
    (r.call appendPoint 3 1 5).total == 2 && !(r.call appendPoint 3 1 5).quit &&
    (r.callMapped appendPoint true 2 5 3).info == #[(1, 0, 0), (5, 3, 2)] &&
    (r.callMapped appendPoint true (-2) 5 3).info == #[(1, 0, 0), (-5, 3, 2)] &&
    (r.callMapped appendPoint false (-2) 5 3).info == #[(1, 0, 0), (-2, 3, 5)]

-- A callback that counts its calls, with the weight `2` for each, and stops at the third: the
-- delivery counts `2` per call and keeps the flag that the call sets.
#guard
  let stop3 (_ _ _ : Int) (n : Nat) : Answer Nat := ⟨2, n + 1 == 3, n + 1⟩
  let r := ((⟨0, 0, false⟩ : Delivery Nat).call stop3 1 1 1).call stop3 2 1 1
  r.info == 2 && r.total == 4 && !r.quit &&
    (r.call stop3 3 1 1).quit && (r.call stop3 3 1 1).total == 6

-- The delivery of a list: with the appending callback the points of the list in their order and
-- its length as the count; with a callback that stops at its `k`-th call and has the weight `2`,
-- the first `k` points (all of them for `k = 0`, which never stops, and for `k` beyond the length)
-- and twice their number as the count; and a delivery whose flag is set is left as it is.
#guard
  let L : List (Int × Int × Int) := [(1, 0, 0), (3, 5, 1), (3, -5, 1), (129, 3830, 100)]
  let r₀ : Delivery (Array (Int × Int × Int)) := ⟨#[(0, 1, 1)], 3, false⟩
  let stopAt (k : Nat) (x z y : Int) (pts : Array (Int × Int × Int)) :
      Answer (Array (Int × Int × Int)) := ⟨2, pts.size + 1 == k, pts.push (x, y, z)⟩
  let r := r₀.deliver appendPoint L
  r.info.toList == (0, 1, 1) :: L && r.total == 3 + L.length && !r.quit &&
    (List.range 7).all (fun k ↦
      let r := (⟨#[], 0, false⟩ : Delivery (Array (Int × Int × Int))).deliver (stopAt k) L
      let n := if k = 0 then L.length else min k L.length
      r.info.toList == L.take n && r.total == 2 * n && r.quit == (1 ≤ k && k ≤ L.length)) &&
    ({ r₀ with quit := true }.deliver appendPoint L).info == r₀.info &&
    ({ r₀ with quit := true }.deliver appendPoint L).total == 3

end Ratpoints

end

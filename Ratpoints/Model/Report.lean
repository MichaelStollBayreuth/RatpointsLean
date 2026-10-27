/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.Choice

/-!
# The report of the library

Under the bit `RATPOINTS_VERBOSE` of the flags, which the option `-v` of the program sets, the
library of `ratpoints` prints a report of the search on the standard output, between the points that
the callback of the program prints there: the arguments as the search normalizes them, the reversal
check, the Sturm step, the points at infinity and the tests on the denominators, the packing of the
numerators, the choice of the moduli with the cost of a check and the forbidden divisors, the line
before the points at infinity and the line before the sieve, and the exits on the way. The
definitions here are the texts of these parts, as `printf` prints them, with the conversions `%ld`
(Lean's `toString`), `%3ld` (`Ratpoints.Report.width3`), `%lf` and `%.pf`
(`Ratpoints.Double.printFixed`), each from the data that the C code prints; the search prints each
where the C code prints it, through its print channel into the data of the callback
(`Ratpoints.findPointsWork`, `Ratpoints.searchPoints`, `Ratpoints.chooseAndSearch`).

## Main definitions

* `Ratpoints.Report.arguments`: the arguments of the search.
* `Ratpoints.Report.reversal`, `Ratpoints.Report.sturmStep`: the reversal check and the Sturm step.
* `Ratpoints.Report.setup`, `Ratpoints.Report.packing`: the tests on the denominators and the
  packing of the numerators.
* `Ratpoints.Report.choice`, `Ratpoints.Report.moduli`, `Ratpoints.Report.excluded`: the choice of
  the moduli, the moduli of the stages with the cost of a check, and the forbidden divisors.
* `Ratpoints.Report.sieving`: the lines after the points at infinity.
-/

@[expose] public section

namespace Ratpoints

namespace Report

open Sieve

/-! ### The conversions of `printf` -/

/-- What `printf` prints for the `long` `n` under `%3ld`: its digits, after a `-` when it is
negative, with spaces before them up to the width 3. -/
def width3 (n : Int) : String :=
  let s := toString n
  "".pushn ' ' (3 - s.length) ++ s

/-- What the loops of the report print for the integers `xs`, each under ` %ld`, or as
`printf(" ")` followed by `mpz_out_str` in base 10: each after a space. -/
def longs (xs : List Int) : String := String.join (xs.map fun x ↦ s!" {x}")

/-! ### Before the search -/

/-- The report of the arguments of a search, which `find_points_work_1` prints under
`RATPOINTS_VERBOSE` once it has normalized them, before the reversal check: the degree `d` of the
polynomial, the leading zeros dropped, and its coefficients `c₀, …, c_d` from the list `c`; the
height bound `H`; the range of the denominators from `bLow` to `bHigh`; of the normalized options
of the sieve `s`, the number of the primes to look at under `%3ld`, the ends of the second and of
the first stage, each under `%3ld` or as chosen from the curve when it is negative, and the bound of
the forbidden divisors; the depth `sturm` of the Sturm step, or that there is none for a negative
depth; whether the points are not checked (`noCheck`), whether the polynomial is not reversed
(`reverse` clear) and whether the Jacobi test is off; and a blank line.

C: `find_points.c:4691-4725`

Deviation: the fields of the arguments as arguments, as the search normalizes them: the options of
the sieve as `Ratpoints.SieveOptions.normalize` gives them, the range of the denominators, the
depth and the switch of the reversal as `Ratpoints.Options.normalize` gives them, the switch for
the bits `RATPOINTS_NO_REVERSE` and `RATPOINTS_NO_REVERSE_AUTO` of the flags, and the bits
`RATPOINTS_NO_CHECK` and `RATPOINTS_NO_JACOBI` as Booleans; integers for the `long`s. -/
def arguments (c : List Int) (d H : Nat) (s : SieveOptions) (bLow bHigh sturm : Int)
    (noCheck reverse : Bool) : String :=
  let chosen (n : Int) : String := if n < 0 then "(chosen from the curve)" else width3 n
  s!"\nfind_points:\n  degree:       {d}\n  coefficients:{longs (c.take (d + 1))}\n" ++
    s!"  height bound: {H}\n  denominators from {bLow} to {bHigh}\n" ++
    s!"  number of primes to consider:     {width3 s.numPrimes}\n" ++
    s!"  number of moduli for sieving:     {chosen s.sp2}\n" ++
    s!"  number of moduli for first stage: {chosen s.sp1}\n" ++
    s!"  maximal number of `forbidden divisors': {s.maxForbidden}\n" ++
    (if 0 ≤ sturm then s!"  iterations for isolations of connected components: {sturm}\n"
      else "  no isolation of connected components to be done\n") ++
    (if noCheck then "  do not verify the points\n" else "") ++
    (if reverse then "" else "  do not reverse the polynomial\n") ++
    (if s.jacobi then "" else "  do not perform Jacobi symbol test\n") ++ "\n"

/-- The report of the reversal check with the switch `allow` on the coefficients `c` of degree `d`,
the leading zeros dropped, which gives `r` (`Ratpoints.Setup.reversal`), as `find_points_work_1`
prints it under `RATPOINTS_VERBOSE`: with the switch on, a line that it checks, and nothing more
when it refuses the form; then, when it reverses the polynomial, which of its cases does so, with
the reversed coefficients `c'₀, …, c'_d` for case 3, and otherwise that it does not, also with the
switch off.

C: `find_points.c:4740-4743`, `find_points.c:4757-4758`, `find_points.c:4771-4774`,
`find_points.c:4791-4801`, `find_points.c:4804-4807`

Deviation: one text, from the result of the check, for the messages that the C code prints in its
course, the case of a reversal read from the degree and the constant term as the check decides it:
case 1 for even `d` and `c₀ = 0`, case 2 for even `d` otherwise and case 3 for odd `d`. -/
def reversal (allow : Bool) (c : List Int) (d : Nat) (r : Except Refusal (List Int × Nat × Bool)) :
    String :=
  (if allow then "Check if polynomial should be reversed for better performance:\n" else "") ++
  match r with
  | .error _ => ""
  | .ok (_, _, false) => "  criteria are not met ==> don't reverse\n\n"
  | .ok (c', _, true) =>
    if d % 2 = 1 then
      "  odd degree, leading coefficient not +/-1, zero constant term, coefficient of x is " ++
        s!"+/-1 ==> reverse\n  coefficients now:{longs (c'.take (d + 1))}\n\n"
    else if c.getD 0 0 = 0 then "  even degree, zero constant term ==> reverse\n\n"
    else "  even degree, leading coefficient is a square, constant term is not a square " ++
      "==> reverse\n\n"

/-- The report of the Sturm step with the depth `sturm`, which gives `r` (`Ratpoints.sturmRegion`),
as `find_points_work_1` prints it under `RATPOINTS_VERBOSE`: nothing for a negative depth, when the
step is off; otherwise a line that it runs, and then that the polynomial is not squarefree when the
step refuses it, that it is negative on the search region when the step keeps no interval, and else
the intervals that it keeps, each as `[l, u] `, its ends under `%lf`
(`Ratpoints.Double.printFixed`), and a blank line.

C: `find_points.c:4860-4861`, `find_points.c:4864-4878`

Deviation: one text, from the result of the step, for the line before the step and the message
after it, which the C code decides by the code that `_ratpoints_compute_sturm` returns: negative
for the refusal, `0` when the step keeps no interval, and the number of the intervals kept
otherwise. -/
def sturmStep (sturm : Int) (r : Except Refusal (Option (List (Double × Double) × Bool))) :
    String :=
  if sturm < 0 then "" else
  "Isolate the connected components:\n" ++
  match r with
  | .error _ => "  polynomial is not squarefree ==> stop\n\n"
  | .ok (some (iv@(_ :: _), _)) => "  can restrict to the following intervals:\n  " ++
    String.join (iv.map fun (l, u) ↦ s!"[{l.printFixed 6}, {u.printFixed 6}] ") ++ "\n\n"
  | .ok _ => "  polynomial is negative on the whole search region ==> no affine points\n\n"

/-! ### The denominators and the numerators -/

/-- The report of the tests on the denominators of the search of the polynomial of degree `d` with
the leading coefficient `lcf`, after the Sturm step, as `find_points_work_1` prints it under
`RATPOINTS_VERBOSE`: that there are points at infinity, for odd `d` or `lcf` a square
(`Ratpoints.Setup.isSquare`); for odd `d`, that the denominators are the squares, for `|lcf| = 1`,
and otherwise that they are squares times divisors of `lcf`, with the divisors, each under ` %ld`,
when the divisor set-up `us1` has succeeded (`Ratpoints.Setup.setupUs1`), and that it has not
otherwise; and a line before the 2-adic information.

C: `find_points.c:4897-4898`, `find_points.c:4915-4918`, `find_points.c:4921-4926`,
`find_points.c:4928-4941`, `find_points.c:4946-4947`

Deviation: one text for the messages between the Sturm step and the 2-adic information, the lines
before the divisor set-up printed with those after it, from its result: the set-up prints nothing;
the divisors as a list, for the zero-terminated array `divisors`. -/
def setup (d : Nat) (lcf : Int) (us1 : Option (List Setup.DenInfo × List Nat)) : String :=
  (if d % 2 == 1 || Setup.isSquare lcf then "There are points at infinity\n\n" else "") ++
  (if d % 2 = 0 then ""
    else if lcf.natAbs = 1 then
      "Degree is odd, leading coefficient is +/-1\n" ++
        "  ==> can restrict to squares as denominators\n\n"
    else "Degree is odd, leading coefficient is not +/-1\n  ==> can restrict denominators\n" ++
      "      to squares times certain divisors of the leading coefficient:\n" ++
      match us1 with
      | some (_, divs) => s!"    divisors:{longs (divs.map Int.ofNat)}\n\n"
      | none => "  no complete factorization obtained, or too many divisors\n" ++
        "  ==> cannot use this feature\n\n") ++
  "Obtain information from the polynomial mod 64:\n"

/-- The message of the exit of the search when no class of the denominators modulo 64 admits a
numerator and there is no point at infinity, which `find_points_work_1` prints under
`RATPOINTS_VERBOSE`.

C: `find_points.c:4960-4961` -/
def noClasses : String := "  no denominator admits a numerator mod 64 ==> no points\n\n"

/-- The report of the packing of the numerators, which `find_points_work_1` prints under
`RATPOINTS_VERBOSE` after the 2-adic information, and the line before the choice of the moduli: for
one class of the denominators modulo 64 of each 2-adic valuation, `b ≡ 1, 2, 4, 8, 16, 32, 0`, the
stride `2 ^ k` of the packing of its numerators under ` %ld`, or ` -` when the class admits no
numerator, its pattern being `0`, from the classes `cls` (`Ratpoints.Sieve.NumClass`); then the
number `numPrimes` of the primes to look at.

C: `find_points.c:4969-4985`, `find_points.c:4988-4991`

Deviation: the pattern of a class, one word in the model, for the first word of its bit array
(`EXT0`), which repeats the pattern; a list for the array `rep`. -/
def packing (cls : Vector NumClass 64) (numPrimes : Int) : String :=
  "  the bit arrays hold one numerator in (for b odd, 2 mod 4, 4 mod 8, ..., 32 mod 64, " ++
    "0 mod 64; - = none admissible):" ++
    String.join ([1, 2, 4, 8, 16, 32, 0].map fun b ↦
      if cls[b]!.bits != 0 then s!" {2 ^ cls[b]!.k}" else " -") ++
    s!"\n\nFind the points mod p for the first {numPrimes} odd primes p:\n"

/-! ### The choice of the moduli -/

/-- The message of the exit of the search when the curve has no points modulo the prime `p` that
the choice of the moduli looks at (`Ratpoints.sievingInfo`), which `find_points_work_1` prints under
`RATPOINTS_VERBOSE`.

C: `find_points.c:5007-5009` -/
def noPoints (p : Nat) : String := s!"  no points mod p = {p} ==> no rational points\n\n"

/-- The report at the end of the choice of the moduli `P`, which `sieving_info` prints under
`RATPOINTS_VERBOSE`: the mean bits per word `bpw` of the bit arrays of the run under `%.1f`
(`Ratpoints.meanBitsPerWord`), the number of the primes looked at, the ends of the first two stages
and the length of the third.

C: `find_points.c:3089-3095`

Deviation: the result of the choice as an argument, for the local `pn_lim` and the fields of the
arguments that `sieving_info` prints, which the search prints after it returns, nothing being
printed in between; the double `bpw` a value of Lean's `Float` (`Ratpoints.Double.ofFloat`); the
length of the third stage an integer, for the difference of the `long`s. -/
def choice (bpw : Float) (P : Params) : String :=
  s!"  {(Double.ofFloat bpw).printFixed 1} bits set per word, {P.lookedAt} primes looked at" ++
    s!" ==> use {P.sp1} moduli in the first stage, {P.sp2} altogether,\n" ++
    s!"  and {(P.sp3 : Int) - P.sp2} primes more in the third stage\n"

/-- The valuations at the prime `p` that the mask `mask` excludes, as the report of the forbidden
divisors prints them: with the largest valuation `M` that a denominator up to `bHigh` can have at
`p`, the least `M ≥ 1` with `p ^ M > bHigh / p`, and the start `f` of the tail of excluded
valuations up to `M`, the least `f ≥ 1` with the bits `f, …, M` of `mask` set, or `M + 1` when bit
`M` is clear: the valuations `m < f` excluded, each as ` v_p(b)=m`, and the tail as ` p^f|b` when
`f ≤ M`.

C: `find_points.c:5049-5058`

Deviation: natural numbers for the `long`s and for the mask, a `while` loop for each of the two
loops `for`, the first with the power and the valuation in the order of its body. -/
def excludedValuations (p mask bHigh : Nat) : Id String := do
  let mut mmax := 1
  let mut pm := p
  while pm ≤ bHigh / p do
    pm := pm * p
    mmax := mmax + 1
  let mut first := mmax + 1
  while 1 < first && (mask >>> (first - 1)) % 2 == 1 do
    first := first - 1
  let mut out := ""
  for m in [1:first] do
    if (mask >>> m) % 2 == 1 then out := out ++ s!" v_{p}(b)={m}"
  if first ≤ mmax then out := out ++ s!" {p}^{first}|b"
  return out

/-- The forbidden divisors of the checked loop of the denominators, as the report of the moduli
prints them: after a line, each prime `p` of `forb`, tested with words, as ` p|b`; the valuations
excluded at each prime of `forbVal`, tested by its valuations
(`Ratpoints.Report.excludedValuations`, with the largest denominator `bHigh`); ` (lcf/b) = -1` when
the Jacobi test runs (`useJacobi`); and a line feed.

C: `find_points.c:5043-5048`, `find_points.c:5059-5063`

Deviation: loops over the lists, for the loops over the zero-terminated arrays `forb_ba` and
`forbidden`; the switch of the Jacobi test as a Boolean, for the bit `RATPOINTS_USE_JACOBI` of the
flags. -/
def excluded (forb : List ForbiddenEntry) (forbVal : List ForbiddenVal) (useJacobi : Bool)
    (bHigh : Nat) : Id String := do
  let mut out := "  denominators excluded:\n   "
  for fb in forb do
    out := out ++ s!" {fb.p}|b"
  for fd in forbVal do
    out := out ++ (← excludedValuations fd.p fd.mask bHigh)
  if useJacobi then out := out ++ " (lcf/b) = -1"
  return out ++ "\n"

/-- The report of the moduli of the three stages, which `find_points_work_1` prints under
`RATPOINTS_VERBOSE` after the choice of the moduli `si` (`Ratpoints.sievingInfo`): for each stage
the number of its moduli and its moduli, each under ` %ld`; the cost of one exact check under
`%.0f`, its ratio `checkRel` to `Ratpoints.checkReference` times that reference, and the ratio under
`%.2f`; the forbidden divisors of the checked loop of the denominators when it runs
(`Ratpoints.Report.excluded`, with the switch `useJacobi` of the Jacobi test and the largest
denominator `bHigh`); and a blank line.

C: `find_points.c:5027-5042`, `find_points.c:5064-5066`

Deviation: the moduli of the stages as the moduli of the sieve entries in their order, for the
fields `p` of the entries of `sieve_list`; the doubles as values of Lean's `Float`
(`Ratpoints.Double.ofFloat`), the product with the reference computed in its arithmetic; the
numbers of the moduli of the second and the third stage integers, for the differences of the
`long`s. -/
def moduli (si : SievingInfo) (useJacobi : Bool) (bHigh : Nat) : Id String := do
  let P := si.params
  let ms := si.entries.map fun e ↦ (e.p : Int)
  let stage (a b : Nat) : String := longs ((ms.drop a).take (b - a))
  let cost := (Double.ofFloat (P.checkRel * checkReference)).printFixed 0
  let ex ← if si.checkDenom then excluded si.forb si.forbVal useJacobi bHigh else pure ""
  return s!"  use {P.sp1} moduli for first stage:\n   {stage 0 P.sp1}\n" ++
    s!"  use {(P.sp2 : Int) - P.sp1} moduli for second stage:\n   {stage P.sp1 P.sp2}\n" ++
    s!"  use {(P.sp3 : Int) - P.sp2} primes for third stage:\n   {stage P.sp2 P.sp3}\n" ++
    s!"  one exact check is put at {cost} cycles, " ++
    s!"{(Double.ofFloat P.checkRel).printFixed 2} times what it costs\n" ++
    "    on the curves the third stage was tuned on\n" ++ ex ++ "\n"

/-! ### The points -/

/-- The line before the points at infinity, which `find_points_work_1` prints under
`RATPOINTS_VERBOSE` when there are points at infinity.

C: `find_points.c:5075-5077` -/
def atInfinity : String := "Points at infinity:\n"

/-- The lines after the points at infinity, which `find_points_work_1` prints under
`RATPOINTS_VERBOSE` when the callback has not stopped the search there: a line feed after the points
at infinity, when there are points at infinity (`atInf`), and, unless the Sturm step has left no
interval (`sturmEmpty`), in which case the search returns there, a line before the sieve and a blank
line.

C: `find_points.c:5104`, `find_points.c:5111-5113`

Deviation: one text for the line feed after the points at infinity and the line before the sieve,
between which the C code returns when the Sturm step has left no interval. -/
def sieving (atInf sturmEmpty : Bool) : String :=
  (if atInf then "\n" else "") ++
    if sturmEmpty then "" else "Now start the sieving procedure...\n\n"

/-! ### Examples -/

-- `%3ld` and the loops of ` %ld`.
#guard [width3 30, width3 5, width3 171, width3 1234, width3 (-5)] ==
  [" 30", "  5", "171", "1234", " -5"]
#guard longs [1, 0, -126, 441] == " 1 0 -126 441" && longs [] == ""

-- The valuations excluded at `3` for the masks `0b0110` (`v_3(b) = 1, 2`) and `0b1100` (the
-- valuations from `2` on, the tail `9 | b`) and `0b1010` (`v_3(b) = 1, 3`, the tail at the largest
-- valuation `3` of a denominator up to `30`).
#guard [(0b0110, " v_3(b)=1 v_3(b)=2"), (0b1100, " 3^2|b"), (0b1010, " v_3(b)=1 3^3|b")].all
  fun (m, s) ↦ Id.run (excludedValuations 3 m 30) == s

end Report

end Ratpoints

end

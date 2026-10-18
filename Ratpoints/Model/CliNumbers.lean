/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.Double

-- The `#guard` examples run code of the imported module at compile time.
meta import Ratpoints.Model.Double

/-!
# The numbers and the search intervals of `ratpoints-lean`

`ratpoints-lean` reads the numbers of its command line as `main.c` of ratpoints reads them: the
integers of the coefficient list as `scan_mpz` reads them, the C `long`s of the height bound and of
the options as `scan_long` reads them with `strtol`, the real numbers of the options as
`scan_double` reads them with `strtod`, and the ends of the search intervals of `-l` and `-u` as
`scan_end` reads them: the rational number that the word denotes, or an infinity, and the double
that the library is given for it, outward of it. With these exact ends it decides, as `process` of
`main.c` does, whether a point that the search finds lies in the search region of the command line
(`Ratpoints.Cli.inRegion`); it joins intervals whose doubles meet, as `join_intervals` does before
the library is called; and it prints the doubles of the search intervals as `printf` of glibc
prints them under `%f` (`Ratpoints.Cli.printF`), in message 3 of the report and, with stage H, in
message 8.

## Main definitions

* `Ratpoints.Cli.longOfString?`: a C `long`, as `scan_long` reads it.
* `Ratpoints.Cli.strtod`, `Ratpoints.Cli.scanDouble?`: a real number, as `strtod` and
  `scan_double` read it.
* `Ratpoints.Cli.ExactEnd`, `Ratpoints.Cli.scanEnd`: an end of a search interval of the command
  line, the number it is and the double the library is given for it.
* `Ratpoints.Cli.inRegion`: whether `x = a / b` lies in the intervals of the command line.
* `Ratpoints.Cli.joinIntervals`: the intervals that the library is given.
* `Ratpoints.Cli.printF`: a double as `printf` prints it under `%f`.

## Implementation notes

The numbers are read as `main.c` reads them, by readers of their own: core's `String.toInt?` takes
neither a leading `+` nor white space around the number, and core's `String.toNat?` takes the digit
separator `_`, which `main.c` refuses. The double that `strtod` reads is the double nearest to the
exact value of the word (`Ratpoints.Double.ofRatio`, and `Ratpoints.Double.ofDyadic` for a
hexadecimal word), which glibc computes, whose size is decided by bounds before a power of 10 or 2
is expanded, so that a word with a huge exponent costs no more than another. The components with a
loop are of type `Id α`.
-/

@[expose] public section

namespace Ratpoints

namespace Cli

/-! ### Reading numbers -/

/-- Whether `ch` is white space for `isspace` in the C locale, in which `main.c` runs: a space,
or a character from the tab `\t` to the carriage return `\r` (tab, line feed, vertical tab, form
feed, carriage return). Core's `Char.isWhitespace` leaves out the vertical tab and the form
feed. -/
def isSpace (ch : Char) : Bool := ch == ' ' || '\t' ≤ ch && ch ≤ '\r'

/-- The words of `s`: its maximal runs of characters that are not C white space
(`Ratpoints.Cli.isSpace`), in order. `List.splitBy` cuts `s` into the maximal runs of white space
and of other characters, and the words are the latter. -/
def words (s : List Char) : List (List Char) :=
  (s.splitBy fun a b ↦ isSpace a == isSpace b).filter fun w ↦ !w.any isSpace

/-- Whether `s` is a nonempty list of decimal digits. -/
def isDigits (s : List Char) : Bool := !s.isEmpty && s.all Char.isDigit

/-- The natural number that `ds` denotes, if it is a nonempty list of decimal digits. -/
def natOfDigits? (ds : List Char) : Option Nat :=
  if isDigits ds then some (ds.foldl (fun n ch ↦ 10 * n + (ch.toNat - '0'.toNat)) 0) else none

/-- The characters of `s` after an optional sign `-` or `+`. -/
def dropSign : List Char → List Char
  | '-' :: s | '+' :: s => s
  | s => s

/-- The integer that the word `w` is, as `scan_mpz` of `main.c` reads it: an optional sign `-` or
`+`, then at least one decimal digit and nothing else. There is no bound on its size. `scan_mpz`
also checks that white space or the end of the argument follows the digits, which a word of
`Ratpoints.Cli.words` satisfies.

C: `main.c:700-717` -/
def intOfWord? (w : List Char) : Option Int :=
  (natOfDigits? (dropSign w)).map fun n ↦ if w.head? = some '-' then -(n : Int) else n

/-- The one word of `s`, if `s` has exactly one word (`Ratpoints.Cli.words`): `strtol` and
`strtod` skip the white space before a number, and `only_space_after` of `main.c` checks that
nothing but white space follows it.

C: `main.c:724-728` -/
def onlyWord? (s : String) : Option (List Char) :=
  match words s.toList with
  | [w] => some w
  | _ => none

/-- The C `long` that `s` is, as `scan_long` of `main.c` reads it with `strtol` in base 10: an
integer as `Ratpoints.Cli.intOfWord?` reads it, with nothing but C white space before and after
it (`Ratpoints.Cli.onlyWord?`), from `-2⁶³` to `2⁶³ - 1`; for a value beyond these bounds
`strtol` reports the error `ERANGE`.

C: `main.c:733-740`

Deviation: an `Int` for a `long`. -/
def longOfString? (s : String) : Option Int :=
  ((onlyWord? s).bind intOfWord?).filter fun n ↦ -2 ^ 63 ≤ n && n < 2 ^ 63

/-! ### Real numbers -/

/-- Whether `s` is a floating constant as `strtod` reads it, without its sign and, for a
hexadecimal one, without its prefix `0x`, and nothing else: the mantissa, a maximal run of digits
(those that satisfy `isDigit`) and points with at most one point and at least one digit, and then
optionally the exponent, a character of `exp`, an optional sign and at least one decimal digit. -/
def isFloatBody (isDigit : Char → Bool) (exp : List Char) (s : List Char) : Bool :=
  let (m, e) := s.span fun ch ↦ isDigit ch || ch == '.'
  m.count '.' ≤ 1 && m.any isDigit && match e with
    | [] => true
    | x :: t => exp.contains x && isDigits (dropSign t)

/-- Whether the characters `v`, a word without its sign, are an infinity for `strtod`: `inf` or
`infinity` in any case. -/
def isInfWord (v : List Char) : Bool :=
  ["inf".toList, "infinity".toList].contains (v.map Char.toLower)

/-- Whether the word `w` is a number for `strtod` in the C locale, other than a NaN: an optional
sign, then `inf` or `infinity` in any case (`Ratpoints.Cli.isInfWord`), or a decimal floating
constant with the exponent `e` or `E` (`Ratpoints.Cli.isFloatBody`), or `0x` or `0X` and a
hexadecimal one with the exponent `p` or `P`. -/
def isDoubleWord (w : List Char) : Bool :=
  let v := dropSign w
  isInfWord v ||
    match v with
    | '0' :: x :: t =>
      if x.toLower == 'x' then isFloatBody Char.isHexDigit ['p', 'P'] t
      else isFloatBody Char.isDigit ['e', 'E'] v
    | _ => isFloatBody Char.isDigit ['e', 'E'] v

/-- The value of the hexadecimal digit `ch`: `0` to `9` for the decimal digits, and `10` to `15`
for `a` to `f` and for `A` to `F`, as `mpz_set_str` of GMP reads the digits of base 16 (and of
base 10, which are among them). -/
def digitValue (ch : Char) : Nat :=
  if ch.isDigit then ch.toNat - '0'.toNat
  else if 'a' ≤ ch && ch ≤ 'f' then ch.toNat - 'a'.toNat + 10
  else ch.toNat - 'A'.toNat + 10

/-- The natural number that the digits `ds` give in the base `b`, as `mpz_set_str` of GMP reads
them. -/
def natOfDigitsIn (b : Nat) (ds : List Char) : Nat :=
  ds.foldl (fun n ch ↦ b * n + digitValue ch) 0

/-- The digits of the mantissa at the start of `s`, the characters that satisfy `isDigit` with
points among them, as the loop of `scan_end` of `main.c` reads them, `point` saying whether a
point has been passed: the digits in their order, without the points, the number of those after
a point, and the rest of `s` from the first character that is neither a digit nor a point.

C: `main.c:822-834`

Deviation: a recursion over the characters, for the loop over the C string and the array `digits`,
whose length is the number `n` of the digits. -/
def mantissaDigits (isDigit : Char → Bool) (point : Bool) : List Char → List Char × Nat × List Char
  | '.' :: s => mantissaDigits isDigit true s
  | ch :: s =>
    if isDigit ch then
      let (ds, k, rest) := mantissaDigits isDigit point s
      (ch :: ds, k + if point then 1 else 0, rest)
    else ([], 0, ch :: s)
  | [] => ([], 0, [])

/-- The parts of the floating constant `w` of `Ratpoints.Cli.isDoubleWord` that is not an infinity,
as `scan_end` of `main.c` reads them: whether it is negative (its sign `-`), whether it is
hexadecimal (`0x` or `0X` after the sign), the digits of the mantissa without the point, the
number of them after the point (`Ratpoints.Cli.mantissaDigits`), and what follows them, the
exponent: `e`, `E`, `p` or `P`, an optional sign and decimal digits, or nothing. `strtod` reads the
same parts (`Ratpoints.Cli.strtod`). -/
def floatParts (w : List Char) : Bool × Bool × List Char × Nat × List Char :=
  let neg := w.head? = some '-'
  let v := dropSign w
  match v with
  | '0' :: x :: t =>
    if x == 'x' || x == 'X' then
      let (ds, k, rest) := mantissaDigits Char.isHexDigit false t
      (neg, true, ds, k, rest)
    else
      let (ds, k, rest) := mantissaDigits Char.isDigit false v
      (neg, false, ds, k, rest)
  | _ =>
    let (ds, k, rest) := mantissaDigits Char.isDigit false v
    (neg, false, ds, k, rest)

/-- Whether the exponent `rest` of a floating constant (`Ratpoints.Cli.floatParts`) is negative,
and its decimal digits: after `e`, `E`, `p` or `P`, a sign `-` or `+` and then the digits; for no
exponent, not negative and no digits. -/
def exponentDigits (rest : List Char) : Bool × List Char :=
  match rest with
  | x :: t =>
    if "eEpP".contains x then
      match t with
      | '-' :: ds => (true, ds)
      | '+' :: ds => (false, ds)
      | ds => (false, ds)
    else (false, [])
  | [] => (false, [])

/-- The double nearest to `±m 2 ^ t`, the sign `-` for `neg`, its size decided first by the length
of `m` in bits: an infinity when `m 2 ^ t ≥ 2 ^ 1024`, a zero when `m 2 ^ t < 2 ^ (-1075)`, and
otherwise the rounding of `Ratpoints.Double.ofDyadic`, whose shift is then bounded by the length of
`m` and the range of the doubles. -/
def nearestBinary (neg : Bool) (m : Nat) (t : Int) : Double :=
  if m = 0 then .ofRatio neg 0 1
  else if 1024 ≤ m.log2 + t then (if neg then Double.huge.neg else Double.huge)
  else if m.log2 + 1 + t ≤ -1075 then .ofRatio neg 0 1
  else .ofDyadic neg m t

/-- The double nearest to `±m 10 ^ t`, the sign `-` for `neg` (`Ratpoints.Double.ofRatio`), its
size decided first by the length of `m` in bits and by `2 ^ (3 u) ≤ 10 ^ u`: an infinity when
`m 10 ^ t ≥ 2 ^ 1024`, a zero when `m 10 ^ t < 2 ^ (-1075)`, and otherwise the power of 10
expanded, its exponent then bounded by the length of `m` and the range of the doubles. -/
def nearestDecimal (neg : Bool) (m : Nat) (t : Int) : Double :=
  if m = 0 then .ofRatio neg 0 1
  else if 0 ≤ t then
    if 1024 ≤ m.log2 + 3 * t then (if neg then Double.huge.neg else Double.huge)
    else .ofRatio neg (m * 10 ^ t.toNat) 1
  else if m.log2 + 1076 ≤ 3 * -t then .ofRatio neg 0 1
  else .ofRatio neg m (10 ^ (-t).toNat)

/-- The double that `strtod` of glibc reads from the word `w` of `Ratpoints.Cli.isDoubleWord`, a
floating constant or an infinity, in the C locale: `±∞` for an infinity, and otherwise the double
nearest to the exact value `±m 10 ^ (ex - k)`, or `±m 2 ^ (ex - 4 k)` for a hexadecimal constant,
of the digits `m` of its mantissa, the number `k` of them after the point and its exponent `ex`,
with ties to even (`Ratpoints.Cli.nearestDecimal`, `Ratpoints.Cli.nearestBinary`): a zero of the
sign of `w` for a value of size at most `2 ^ (-1075)`, and an infinity of its sign for one of size
at least `2 ^ 1024 - 2 ^ 970`, as glibc rounds it, correctly. This is what glibc computes, not
how: the size of the value is decided by bounds before a power is expanded, so that a word with a
huge exponent costs no more than another. -/
def strtod (w : List Char) : Double :=
  if isInfWord (dropSign w) then (if w.head? = some '-' then Double.huge.neg else Double.huge)
  else
    let (neg, hex, ds, k, rest) := floatParts w
    let (eneg, eds) := exponentDigits rest
    let ex : Int := if eneg then -(natOfDigitsIn 10 eds : Int) else natOfDigitsIn 10 eds
    if hex then nearestBinary neg (natOfDigitsIn 16 ds) (ex - 4 * k)
    else nearestDecimal neg (natOfDigitsIn 10 ds) (ex - k)

/-- The double that `s` is, as `scan_double` of `main.c` reads it with `strtod`: a word of
`Ratpoints.Cli.isDoubleWord`, with nothing but C white space before and after it
(`Ratpoints.Cli.onlyWord?`), read by `Ratpoints.Cli.strtod`, so that a number beyond the range of
the doubles is read as an infinity or as a zero; none for anything else, among them a NaN.

C: `main.c:746-752`

Deviation: the NaN refused by its syntax, which `Ratpoints.Cli.isDoubleWord` does not accept, for
the test `isnan` of the double that `strtod` reads. -/
def scanDouble? (s : String) : Option Double :=
  (onlyWord? s).bind fun w ↦ if isDoubleWord w then some (strtod w) else none

/-! ### The ends of the search intervals -/

/-- `exact_end` of `main.c`: an end of a search interval of the command line as the number it
denotes, `inf` being `-1` for `-∞`, `1` for `+∞` and `0` for the rational number `q`.

C: `main.c:71`

Deviation: an `Int` for the `int` `inf`, and a rational number of core for the `mpq_t` `q`, `0`
by default as `mpq_init` sets it. -/
structure ExactEnd where
  /-- `inf`: `-1` for `-∞`, `1` for `+∞`, `0` for the rational number `q`. -/
  inf : Int := 0
  /-- `q`: the end, when it is a rational number. -/
  q : Rat := 0
  deriving Inhabited, DecidableEq, Repr

/-- The double that `outward` of `main.c` gives for an end `v` of an interval of the command line,
starting from the double `x` nearest to it, the direction `dir < 0` for a lower end and `dir > 0`
for an upper one: while `x` is finite and lies above `v` (for a lower end) or below it (for an
upper one), the double next to it outward (`Ratpoints.Double.nextDown`, `Ratpoints.Double.nextUp`),
so that the result is the largest double `≤ v`, or the smallest double `≥ v`, when `x` is a double
nearest to `v`, or an infinity on the safe side of `v`.

C: `main.c:761-763`, `main.c:766-773`, `main.c:775-776`

Deviation: the exact value of `x` (`Ratpoints.Double.toRat`) compared with `v` as rational numbers
of core, for the GMP rational `t`, `mpq_set_d` and `mpq_cmp`; no `mpq_init` and `mpq_clear`. -/
def outward (x : Double) (v : Rat) (dir : Int) : Id Double := do
  let mut x := x
  while x.isFinite do
    let t := x.toRat
    if (if dir < 0 then t ≤ v else v ≤ t) then break
    x := if dir < 0 then x.nextDown else x.nextUp
  return x

/-- The end of a search interval that `s` is, as `scan_end` of `main.c` reads it, and the double
that the library is given for it, `dir < 0` for a lower end and `dir > 0` for an upper one; none
when `s` is not a number for `Ratpoints.Cli.scanDouble?`. For an infinite double `x` read by
`strtod`, also for a number beyond the range of the doubles, the infinite end of its sign and `x`
itself. Otherwise the number that `s` denotes, from the parts of its word
(`Ratpoints.Cli.floatParts`): `0` when its digits `m` are `0`; when `strtod` reads `0` for it
although `m ≠ 0`, `2 ^ (-1075)`, half the least positive double, which lies between `0` and every
other `x` of the search as the number itself does; and otherwise `m 2 ^ (ex - 4 k)` for a
hexadecimal number and `m 10 ^ (ex - k)` for a decimal one, for the `k` digits after the point and
the exponent `ex` that `scan_end` accumulates, which stops taking digits once it reaches
`LONG_MAX / 20` (it is then that of a number beyond the range of the doubles or of `0`); negated
for the sign `-`. The double is that of `Ratpoints.Cli.outward` from `x` towards that number.

C: `main.c:798-806`, `main.c:808-819`, `main.c:835-847`, `main.c:849`, `main.c:851-865`,
`main.c:868-873`, `main.c:875-876`, `main.c:878-880`

Deviation: the end and the double returned, or none, for the `exact_end` and the double that
`scan_end` writes through pointers with its return value, the end of an infinity with `q = 0`, which
`scan_end` leaves as it is (it is not read); the parts of the word read by
`Ratpoints.Cli.floatParts` from the word of `Ratpoints.Cli.onlyWord?`, which is `s` without its
white space; rational numbers of core for the GMP integers and rationals `m`, `p` and `e->q`,
without `mpz_init`, `mpz_clear`, `malloc` and `free` (and the error 10 when `malloc` fails, which
the model cannot meet). -/
def scanEnd (s : String) (dir : Int) : Id (Option (ExactEnd × Double)) := do
  let some x := scanDouble? s | return none
  if x.isInf then return some ({ inf := if Double.zero.lt x then 1 else -1 }, x)
  let some w := onlyWord? s | return none
  let (neg, hex, ds, k, rest) := floatParts w
  let (eneg, eds) := exponentDigits rest
  let ex : Int := eds.foldl (fun ex ch ↦
    if ex < (2 ^ 63 - 1) / 20 then 10 * ex + (ch.toNat - '0'.toNat) else ex) 0
  let ex := if eneg then -ex else ex
  let m := natOfDigitsIn (if hex then 16 else 10) ds
  let t := if hex then ex - 4 * k else ex - k
  let q : Rat :=
    if m = 0 then 0
    else if x.beq .zero then Double.zero.nextUp.toRat / 2
    else
      let p := (if hex then 2 else 10) ^ t.natAbs
      if 0 ≤ t then ((m * p : Nat) : Rat) else mkRat m p
  let q := if neg then -q else q
  let d ← outward x q dir
  return some ({ q }, d)

/-- The end that `height_end` of `main.c` gives for a missing first `-l` (negated) and a missing
last `-u`: the double of the height bound `H` (`Ratpoints.Double.ofInt64`), moved up to the
next double when it is below `2 ^ 63` and its value below `H`, so that the interval holds every
`x = a / b` with `|a| ≤ H`, as the default interval of the library does.

C: `main.c:299-305`

Deviation: a natural number for the `long` `height`, at most `2 ^ 63 - 1`. -/
def heightEnd (H : Nat) : Double :=
  let h := Double.ofInt64 H.toInt64
  if h.lt .twoPow63 && h.toInt64 < H.toInt64 then h.nextUp else h

/-- The sign of the end `e` minus the end `f`, as `cmp_end` of `main.c` computes it: `e.inf - f.inf`
when one of them is infinite, so that two infinities of one sign are equal, and else the sign of
`e.q - f.q`.

C: `main.c:309-313`

Deviation: the sign as `-1`, `0` or `1`, for the value of `mpq_cmp`, of which `main.c` reads only
the sign. -/
def cmpEnd (e f : ExactEnd) : Int :=
  if e.inf != 0 || f.inf != 0 then e.inf - f.inf
  else if e.q < f.q then -1 else if f.q < e.q then 1 else 0

/-- The sign of the end `e` minus `x = a / b`, for `b > 0`, as `cmp_end_x` of `main.c` computes it:
`e.inf` when `e` is infinite, and else the sign of `e.q - a / b`.

C: `main.c:116-120`

Deviation: the sign as `-1`, `0` or `1`, for the value of `mpq_cmp_si`, of which `main.c` reads
only the sign; integers for the `long`s. -/
def cmpEndX (e : ExactEnd) (a b : Int) : Int :=
  if e.inf != 0 then e.inf
  else if e.q < Rat.divInt a b then -1 else if Rat.divInt a b < e.q then 1 else 0

/-- Whether `x = a / b`, `b > 0`, lies in one of the `n` intervals of the command line whose ends
are `e[2 i] ≤ x ≤ e[2 i + 1]`, which are increasing and disjoint, as `in_region` of `main.c`
decides it: the binary search finds the first interval that does not end below `x`, which must
hold it.

C: `main.c:126-137`

Deviation: natural numbers for the `long` indices, an array for the pointer `e`. -/
def inRegion (a b : Int) (e : Array ExactEnd) (n : Nat) : Id Bool := do
  let mut lo := 0
  let mut hi := n
  while lo < hi do
    let mid := lo + (hi - lo) / 2
    if cmpEndX e[2 * mid + 1]! a b < 0 then lo := mid + 1 else hi := mid
  return lo < n && cmpEndX e[2 * lo]! a b ≤ 0

/-- The search intervals that `main.c` gives the library for the intervals `dom` of the command
line, as `join_intervals` makes them: in turn from the second, an interval whose lower end is at
most the upper end of the interval it may be joined to is joined to it, the least of the lower ends
and the greatest of the upper ends, and every other interval is the next one, to which the following
may be joined, so that intervals whose doubles meet or overlap become one.

C: `main.c:891-905`

Deviation: a list for the array `args->domain` and the number `args->num_inter` of its intervals,
written back in place by `join_intervals`, and natural numbers for the `long` indices. -/
def joinIntervals (dom : List (Double × Double)) : Id (List (Double × Double)) := do
  if dom.isEmpty then return dom
  let mut iv := dom.toArray
  let mut n := 0
  for i in [1:dom.length] do
    if iv[i]!.1.le iv[n]!.2 then
      if iv[i]!.1.lt iv[n]!.1 then iv := iv.set! n (iv[i]!.1, iv[n]!.2)
      if iv[n]!.2.lt iv[i]!.2 then iv := iv.set! n (iv[n]!.1, iv[i]!.2)
    else
      n := n + 1
      iv := iv.set! n iv[i]!
  return (iv.toList.take (n + 1))

/-! ### Printing doubles -/

/-- What `printf` of glibc prints for the double `x` under the conversion `%f`, which `%lf` is too:
the exact value of `x` rounded to six places after the point, ties to even, in full however large it
is, after a `-` whenever the sign bit is set, also for `-0.0` and for a negative value that rounds
to `0`; `inf` for an infinity and `nan` for a NaN, after a `-` when the sign bit is set. -/
def printF (x : Double) : String :=
  let sign := if x.signBit then "-" else ""
  if x.isNaN then sign ++ "nan"
  else if x.isInf then sign ++ "inf"
  else
    let n := Double.roundShift (x.toDyadic.1.natAbs * 10 ^ 6) (-x.toDyadic.2)
    let f := toString (n % 10 ^ 6)
    sign ++ toString (n / 10 ^ 6) ++ "." ++ "".pushn '0' (6 - f.length) ++ f

/-! ### Examples -/

#guard words " 1\t-2\x0b+3\r".toList == ["1".toList, "-2".toList, "+3".toList]

#guard longOfString? " +7\r" == some 7 && longOfString? "-0" == some 0

#guard longOfString? "9223372036854775807" == some (2 ^ 63 - 1) &&
  longOfString? "-9223372036854775808" == some (-2 ^ 63)

#guard longOfString? "9223372036854775808" == none && longOfString? "1_000" == none

#guard [" 1.5e3 ", "-0x1.8p3", ".5", "1.", "INFINITY", "-inf", "1e400"].all
  (scanDouble? · |>.isSome)

#guard !(["nan", "1e", "0x", ".", "1e+", "0x1p", "1,5", "1 2", "infinit", ""].any
  (scanDouble? · |>.isSome))

-- `strtod` against glibc (the bits of the double that a C program prints for `strtod` of the word):
-- the infinities and zeros beyond the doubles, also for exponents too large to expand, the
-- boundaries `2 ^ (-1075)` and `2 ^ 1024 - 2 ^ 970` with the numbers on either side of them, ties
-- of the rounding, subnormals, hexadecimal constants.
#guard ([
    ("1e400", 0x7ff0000000000000), ("-1e-400", 0x8000000000000000), ("-0", 0x8000000000000000),
    ("0x1p-1075", 0x0000000000000000), ("0x1.0000000000001p-1075", 0x0000000000000001),
    ("2.4703282292062327e-324", 0x0000000000000000),
    ("2.4703282292062328e-324", 0x0000000000000001),
    ("1.7976931348623158e308", 0x7fefffffffffffff),
    ("1.797693134862315807937289714053e308", 0x7fefffffffffffff),
    ("0x1.fffffffffffff8p1023", 0x7ff0000000000000),
    ("0x1.fffffffffffff7p1023", 0x7fefffffffffffff), ("9007199254740993", 0x4340000000000000),
    ("9007199254740995", 0x4340000000000002), ("0.1", 0x3fb999999999999a),
    ("0.3333333333333333", 0x3fd5555555555555), ("0.33333333333333337", 0x3fd5555555555556),
    ("1e99999999999999999999999999", 0x7ff0000000000000),
    ("1e-99999999999999999999999999", 0x0000000000000000),
    ("0e99999999999999999999", 0x0000000000000000),
    ("2.2250738585072011e-308", 0x000fffffffffffff), ("0x.8", 0x3fe0000000000000),
    ("-INFINITY", 0xfff0000000000000), ("123456789012345678901234567890e-30", 0x3fbf9add3746f65f),
    ("7.4109846876186982e-324", 0x0000000000000002), ("1.5e-323", 0x0000000000000003),
    ("0X1P-1", 0x3fe0000000000000)] :
    List (String × UInt64)).all fun (s, b) ↦ (scanDouble? s).map (·.bits) == some b

-- `printf("%f")` against glibc: ties to even at the sixth place, `-` on the sign bit also for
-- `-0.0` and for negative values that round to `0`, the infinities, and large values in full.
#guard ([
    (0x8000000000000000, "-0.000000"), (0x3f80000000000000, "0.007812"),
    (0x3f98000000000000, "0.023438"), (0xbf80000000000000, "-0.007812"),
    (0xbe7ad7f29abcaf48, "-0.000000"), (0x3eb0c6f7a0b5ed8d, "0.000001"),
    (0x7ff0000000000000, "inf"), (0xfff0000000000000, "-inf"),
    (0x43e0000000000000, "9223372036854775808.000000"),
    (0xc3e0000000000000, "-9223372036854775808.000000"), (0x3fe0000000000000, "0.500000"),
    (0x4024000000000000, "10.000000"), (0x0000000000000001, "0.000000"),
    (0x44b52d02c7e14af6, "99999999999999991611392.000000")] :
    List (UInt64 × String)).all fun (x, s) ↦ printF ⟨x⟩ == s

-- `scan_end`: the exact end and the double outward of it, for a lower end (`-1`) and an upper one
-- (`1`): `1 / 10`, `8 / 5`, which no double is, and `-8 / 5`; `3 / 4`, which is one; `-1e-400`,
-- whose double is `-0.0`, taken as `-2 ^ (-1075)`; `0` with a huge exponent, and a tiny number
-- with one; infinities, also beyond the doubles; and words that are no number.
#guard ([("0.1", -1, mkRat 1 10, 0x3fb9999999999999), ("0.1", 1, mkRat 1 10, 0x3fb999999999999a),
    ("1.6", -1, mkRat 8 5, 0x3ff9999999999999), ("1.6", 1, mkRat 8 5, 0x3ff999999999999a),
    (" -1.6", -1, mkRat (-8) 5, 0xbff999999999999a),
    ("-1.6\r", 1, mkRat (-8) 5, 0xbff9999999999999),
    ("0x1.8p-1", -1, mkRat 3 4, 0x3fe8000000000000), ("0x.Cp0", 1, mkRat 3 4, 0x3fe8000000000000),
    ("-1e-400", 1, -mkRat 1 (2 ^ 1075), 0x8000000000000000),
    ("-1e-400", -1, -mkRat 1 (2 ^ 1075), 0x8000000000000001),
    ("0e999999999999999999999", 1, 0, 0), ("-0", 1, 0, 0x8000000000000000),
    ("1e-999999999999999999999", -1, mkRat 1 (2 ^ 1075), 0),
    ("1e-999999999999999999999", 1, mkRat 1 (2 ^ 1075), 1)] :
    List (String × Int × Rat × UInt64)).all fun (s, dir, q, b) ↦
  (Id.run (scanEnd s dir)).map (fun (e, d) ↦ (e, d.bits)) == some ({ q }, b)
#guard ([("1e400", 1, 1, 0x7ff0000000000000), ("-inf", -1, -1, 0xfff0000000000000),
    ("-1e999999999999999999999", 1, -1, 0xfff0000000000000),
    ("Infinity", -1, 1, 0x7ff0000000000000)] :
    List (String × Int × Int × UInt64)).all fun (s, dir, i, b) ↦
  (Id.run (scanEnd s dir)).map (fun (e, d) ↦ (e.inf, d.bits)) == some (i, b)
#guard ["nan", "1 2", "", "0x", "-nan(1)"].all fun s ↦ (Id.run (scanEnd s 1)).isNone

-- The ends of a missing `-l` and `-u` for the heights `1`, `2 ^ 53 + 1` and `2 ^ 63 - 1`.
#guard [(1, 0x3ff0000000000000), (2 ^ 53 + 1, 0x4340000000000001), (2 ^ 63 - 1, 0x43e0000000000000)
    ].all fun (H, b) ↦ (heightEnd H).bits == b

-- `in_region`: the intervals `[-∞, -1]`, `[1 / 3, 1 / 2]` and `[2, +∞]` at the points on and next
-- to their ends.
#guard
  let e : Array ExactEnd := #[{ inf := -1 }, { q := -1 }, { q := mkRat 1 3 }, { q := mkRat 1 2 },
    { q := 2 }, { inf := 1 }]
  [(-5, 1, true), (-1, 1, true), (-2, 3, false), (0, 1, false), (1, 3, true), (2, 5, true),
    (1, 2, true), (5, 9, false), (3, 2, false), (2, 1, true), (7, 1, true)].all fun (a, b, r) ↦
    Id.run (inRegion a b e 3) == r

-- `join_intervals`: intervals that meet or overlap joined, the others kept.
#guard
  let d (n : Int) : Double := .ofInt64 (Int64.ofInt n)
  (Id.run (joinIntervals [(d 0, d 2), (d 2, d 3), (d 5, d 6), (d 4, d 7), (d 9, d 9)])).map
      (fun (l, u) ↦ (l.bits, u.bits)) ==
    [(d 0, d 3), (d 4, d 7), (d 9, d 9)].map fun (l, u) ↦ (l.bits, u.bits)

end Cli

end Ratpoints

end

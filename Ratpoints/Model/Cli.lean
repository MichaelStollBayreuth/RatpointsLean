/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.CliNumbers
public import Ratpoints.Model.FindPoints

-- The `#guard` examples run the sieve at compile time.
meta import Ratpoints.Model.CliNumbers
meta import Ratpoints.Model.FindPoints

/-!
# The command-line program `ratpoints-lean`

`ratpoints-lean` has the command line of ratpoints: the coefficient list `'a_0 a_1 ... a_n'` of
`y ^ 2 = a_n x ^ n + ⋯ + a_0` as one argument (constant term first), the height bound and the
options. It reads them as `main.c` of ratpoints does, with its checks, messages and exit statuses,
in its order, and prints what ratpoints prints: unless `-q` is given, the report, with the banner of
`ratpoints-lean`, the curve, the height bound and the search region of the command line before the
points, and after them what the search did, the search intervals that it searched and the count of
the points found, but for message 4 on the moduli used (stage I) and, under `-v`, the report of the
library; under `-x`, the pairs that pass the sieve of the model, with the moduli that the search
chooses from the curve as ratpoints chooses them (`Ratpoints.sievingInfo`) and corrects between the
blocks of the run (`Ratpoints.Sieve.adaptPrimes`), and over the numerators of the search intervals
that the Sturm step leaves, which are those that ratpoints prints when none of the tuning options
`-r -R -U -C -Q -W`, which the program ignores, is given, and `-A`, which it ignores too, is absent
or gives `1` or a negative value, the default of the correction; and the points, through the
callback `process` of `main.c` (`Ratpoints.Cli.process`), which the search calls for each point it
finds (`Ratpoints.findPointsVerbose`), in the format of `-f` with the strings of `-fs`, `-fm` and
`-fe`, the points at infinity passed over under `-i` (neither printed nor counted), none printed
under `-z`, and the search stopped under `-1` at the first point that `process` does not pass over
(the first point counted, printed or not). It reads `-p -n -N -P -F -j -J` into the options of the
sieve and ignores the other options that tune the sieve of ratpoints (until stage I, but for `-t`
for good); it reads `-k -K -s -S`, `-x -X -y -Y` and `-dl -du` into the options of the search
(`Ratpoints.Options`): whether the polynomial may be reversed, the depth of the Sturm step, whether
the points are checked exactly, whether both points of a pair are delivered, and the range of the
denominators; and it reads the search intervals of `-l` and `-u` as `main.c` does, the ends as the
numbers they are (`Ratpoints.Cli.ExactEnd`) and the doubles outward of them, which it gives the
search, joined where they meet (`Ratpoints.Cli.joinIntervals`), and against whose exact ends
`process` checks each point. It runs the search with these options of the sieve, its array size set
to `Ratpoints.defaultArraySize`, and these options of the search, so that it refuses a binary form
that is not squarefree with error 8 and, after a reversal, prints the points of the reversed
polynomial mapped back to the caller's curve, as ratpoints does with the same options.

## Main definitions

* `Ratpoints.Cli.input`: the coefficients, the height bound and the options of a command line.
* `Ratpoints.Cli.Intervals`: the reading of the search intervals of `-l` and `-u`.
* `Ratpoints.Cli.process`: the callback of the search, which prints the points.
* `Ratpoints.Cli.run`: what the program prints and its exit status, on a command line.
* `Ratpoints.Cli.main`: the program.

## Implementation notes

The numbers and the ends of the search intervals are read in `Ratpoints.Model.CliNumbers`. The text
that `main.c` prints as it goes is collected and written once at the end. The callback
`Ratpoints.Cli.process`, a function, and `Ratpoints.Cli.run`, the pure core of the program, run the
loops of `Ratpoints.Cli.inRegion` and `Ratpoints.Cli.joinIntervals` with `Id.run`.
-/

@[expose] public section

namespace Ratpoints

namespace Cli

/-! ### Messages -/

/-- The version of `ratpoints-lean`, which its banner names. -/
def version : String := "0.1"

/-- The banner of `ratpoints-lean`, which it prints with the usage. Its first line names the
program and its version, as that of ratpoints does, so that the test scripts of ratpoints, which
leave out the line beginning `This is ratpoints-`, leave it out too; the rest says what the
program is, under which licence it is released and where it lives.

C: `main.c:43-48`

Deviation: the text is that of `ratpoints-lean`. -/
def banner : String :=
  s!"This is ratpoints-lean-{version} Copyright (C) 2026 by Michael Stoll.\n\n" ++
    "This program is a model of ratpoints 3.1.1 in Lean:\n" ++
    "https://github.com/MichaelStollBayreuth/RatpointsLean\n" ++
    "It comes with ABSOLUTELY NO WARRANTY. It is free software, released\n" ++
    "under the Apache License 2.0.\n\n"

/-- The usage of `ratpoints-lean`: that of ratpoints, all options included.

C: `main.c:77-88`

Deviation: the program is called `ratpoints-lean`, and the lines below the first are indented to
match. -/
def usage : String :=
  "Usage: ratpoints-lean 'a_0 a_1 ... a_n' max_height\n" ++
  "                      [-dl low_den] [-du up_den]\n" ++
  "                      [-f format] [-fs str] [-fm str] [-fe str] [-y] [-Y]\n" ++
  "                      [[-l low1] -u up1 ... -l lown [-u upn]]\n" ++
  "                      [-n num_primes1] [-N num_primes2] [-p max_primes]\n" ++
  "                      [-r survivors_per_word] [-R extra_primes] [-U words]\n" ++
  "                      [-C table_cost] [-A adapt]\n" ++
  "                      [-P stage3_primes] [-Q stage3_cost] [-W check_cost]\n" ++
  "                      [-F max_forbidden] [-t threads] [-s] [-S [iter]]\n" ++
  "                      [-q] [-v] [-z] [-Z] [-1] [-i] [-I]\n" ++
  "                      [-k] [-K] [-j] [-J] [-x] [-X]\n\n"

/-- The ways in which `ratpoints-lean` refuses its command line: the errors of `main.c` that a
command line can cause, those of the reading of the command line and error 8, which `main.c` gives
for a binary form that the library refuses as not squarefree; and error 9, which `main.c` gives for
the codes of the library other than `RATPOINTS_NON_SQUAREFREE` and `RATPOINTS_NO_MEMORY` (error 10,
which the model cannot return), among them the refusal of search intervals that the command line
never passes. -/
inductive Failure where
  /-- Error 2 of `main.c`: fewer than two arguments. -/
  | tooFewArguments
  /-- Error 3 of `main.c`: more than `Ratpoints.maxDegree + 1` coefficients. -/
  | tooManyCoefficients
  /-- Error 4 of `main.c`: a height bound that is not a C `long` of at least 1. -/
  | incorrectHeight
  /-- Error 5 of `main.c`: fewer than two coefficients. -/
  | tooFewCoefficients
  /-- Error 6 of `main.c`: an option that ratpoints does not have, a word without a leading `-`
  among the options, or an option whose argument is missing or malformed, but for `-l` and `-u`. -/
  | optionSyntax
  /-- Error 7 of `main.c`: an end of a search interval (`-l`, `-u`) that is missing or no number,
  two lower or two upper ends in a row, more than `Ratpoints.maxDegree` intervals, or ends that are
  not ordered. -/
  | intervals
  /-- Error 8 of `main.c`: a binary form that is not squarefree
  (`Ratpoints.Refusal.notSquarefree`). -/
  | notSquarefree
  /-- Error 9 of `main.c`: a code of the library other than `RATPOINTS_NON_SQUAREFREE` and
  `RATPOINTS_NO_MEMORY`, for the model the refusal of search intervals
  (`Ratpoints.Refusal.badArgs`), which no command line causes. -/
  | badArgs
  /-- Error 11 of `main.c`: a coefficient that is not an integer. -/
  | incorrectCoefficients

/-- What `ratpoints-lean` prints on a failure: what the function `error` of `main.c` prints
for the same error, a blank line, the message and a blank line; for error 2 the banner and the
usage instead, which error 6 prints after its message, as its case falls through to that of
error 2.

C: `main.c:1036-1048`, `main.c:1050-1053`

Deviation: the banner and the usage are those of `ratpoints-lean`. -/
def Failure.message : Failure → String
  | .tooFewArguments => s!"\n{banner}\n{usage}"
  | .tooManyCoefficients => "\nToo many coefficients.\n\n"
  | .incorrectHeight => "\nIncorrect height argument.\n\n"
  | .tooFewCoefficients => "\nThe polynomial must have degree at least 1.\n\n"
  | .optionSyntax => s!"\nWrong syntax for optional arguments:\n\n\n{banner}\n{usage}"
  | .intervals =>
    "\nIncorrect interval arguments (not numbers, not alternating, too many, or not ordered).\n\n"
  | .notSquarefree => "\nPolynomial is not square-free.\n\n"
  | .badArgs => "\nBug no. 1 - please report!\n\n"
  | .incorrectCoefficients => "\nIncorrect coefficients (not integers separated by blanks).\n\n"

/-- The exit status of `ratpoints-lean` on a failure: the number of the error of `main.c`,
with which its function `error` exits.

C: `main.c:1054-1056` -/
def Failure.status : Failure → UInt32
  | .tooFewArguments => 2
  | .tooManyCoefficients => 3
  | .incorrectHeight => 4
  | .tooFewCoefficients => 5
  | .optionSyntax => 6
  | .intervals => 7
  | .notSquarefree => 8
  | .badArgs => 9
  | .incorrectCoefficients => 11

/-- The failure of `ratpoints-lean` for a refusal of the search (`Ratpoints.findPointsWith`, whose
refusals are those of `Ratpoints.findPoints`): the error of `main.c` with the number that
`Ratpoints.Refusal` names, as `main.c` turns the code `RATPOINTS_NON_SQUAREFREE` that the library
returns into error 8 and its codes other than `RATPOINTS_NO_MEMORY` (error 10) into error 9, among
them `RATPOINTS_BAD_ARGS` (`Ratpoints.Refusal.badArgs`). The reading of the command line
(`Ratpoints.Cli.input`) refuses the inputs of the other refusals first, and the command line gives
no search intervals that the library refuses, so that of the refusals of `Ratpoints.findPointsWith`,
which `Ratpoints.Cli.run` maps by it, only `Ratpoints.Refusal.notSquarefree` can reach it.

C: `main.c:256-261`

Deviation: no error 10, since the model has no failure for lack of memory; the refusals of the
coefficients and of the height (`Ratpoints.Refusal.tooManyCoefficients`,
`Ratpoints.Refusal.tooFewCoefficients`, `Ratpoints.Refusal.incorrectHeight`) mapped to the errors 3,
5 and 4 with which `read_input` refuses those inputs before the library is called, where line 260
gives error 9 for the code `RATPOINTS_BAD_ARGS` with which the library refuses those it can be given
(lines 4557-4558, 4633 and 4658 of `find_points.c`); no command line reaches them; no
`mpz_clear`. -/
def Failure.ofRefusal : Refusal → Failure
  | .tooManyCoefficients => .tooManyCoefficients
  | .tooFewCoefficients => .tooFewCoefficients
  | .incorrectHeight => .incorrectHeight
  | .notSquarefree => .notSquarefree
  | .badArgs => .badArgs

/-! ### The command line -/

/-- The coefficient list that the first argument `s` of the command line gives, constant term
first, as `main.c` reads it: integers as `Ratpoints.Cli.intOfWord?` reads them, separated by C
white space, which may also stand before the first and after the last. A word that is not an
integer fails with error 11, wherever it stands; then more than `Ratpoints.maxDegree + 1`
integers fail with error 3, and fewer than two with error 5.

C: `main.c:54`, `main.c:318`, `main.c:362-375`

Deviation: a list of `Int`s for the global array `c` of `RATPOINTS_MAX_DEGREE + 1` GMP integers; the
integers beyond these, which `main.c` reads into the variable `fff` only to check them, are read
like the others. -/
def coefficients (s : String) : Except Failure (List Int) := do
  let some c := (words s.toList).mapM intOfWord? | throw .incorrectCoefficients
  if maxDegree + 1 < c.length then throw .tooManyCoefficients
  if c.length ≤ 1 then throw .tooFewCoefficients
  return c

/-- The height bound that the second argument `s` of the command line gives, as `main.c` reads
it: a C `long` as `Ratpoints.Cli.longOfString?` reads it, at least 1, so from 1 to `2⁶³ - 1`;
anything else fails with error 4.

C: `main.c:378-379` -/
def heightBound (s : String) : Except Failure Nat :=
  match (longOfString? s).filter fun h ↦ 1 ≤ h with
  | some h => return h.toNat
  | none => throw .incorrectHeight

/-- The kinds of argument that the options of `ratpoints-lean` take. -/
inductive OptionArg where
  /-- A C `long`, as `Ratpoints.Cli.longOfString?` reads it. -/
  | long
  /-- A C `double`, as `Ratpoints.Cli.scanDouble?` reads it. -/
  | double
  /-- An optional C `long`: the next word, if there is one and it does not start with `-`, which is
  then a C `long` as `Ratpoints.Cli.longOfString?` reads it. -/
  | optionalLong
  /-- A string: the next word, whatever it is, also one that starts with `-`. -/
  | word
  /-- An end of a search interval, as `Ratpoints.Cli.scanEnd` reads it, with the checks of
  `Ratpoints.Cli.Intervals.lower` and `Ratpoints.Cli.Intervals.upper`; a missing or malformed one
  fails with error 7. -/
  | bound

/-- Whether `a` is an argument of the kind `arg`. -/
def OptionArg.accepts (arg : OptionArg) (a : String) : Bool :=
  match arg with
  | .long | .optionalLong => (longOfString? a).isSome
  | .double => (scanDouble? a).isSome
  | .word | .bound => true

/-- The kind of argument that the option `o` takes, or `none` if it takes none, for an option that
`ratpoints-lean` reads. `main.c` tells an option by the character after its `-`, and for `-f` and
`-d` by the one after that, ignoring the rest of the word, so that `-quiet` is `-q` and `-fsx` is
`-fs`. The tuning options `-p -F -t -n -N -R -A -P` take a C `long`, `-r -U -C -Q -W` a C `double`,
`-S` an optional C `long`, the options of the output `-f -fs -fm -fe` a string, the bounds of the
denominators `-dl -du` a C `long`, the ends of the search intervals `-l -u` an end, and
`-q -v -j -J -k -K -s`, the switches of the check and of the pairs `-x -X -y -Y`, and those of the
output `-z -Z -1 -i -I`, nothing. Every other word, among them a word without a leading `-`, a word
`-f…` with a third character other than `s`, `m` and `e` and a word `-d…` with one other than `l`
and `u`, fails with error 6. -/
def optionArg (o : String) : Except Failure (Option OptionArg) :=
  match o.toList with
  | '-' :: ch :: rest =>
    if "pFtnNRAP".contains ch then return some .long
    else if "rUCQW".contains ch then return some .double
    else if ch == 'S' then return some .optionalLong
    else if ch == 'f' && rest.head?.all ("sme".contains ·) then return some .word
    else if ch == 'd' && rest.head?.any ("lu".contains ·) then return some .long
    else if "lu".contains ch then return some .bound
    else if "qvjJkKsxXyYzZ1iI".contains ch then return none
    else throw .optionSyntax
  | _ => throw .optionSyntax

/-- The settings of the output of `ratpoints-lean`, the global variables of `main.c`, with their
defaults, those of a command line without options: whether the report is left out (`-q`), whether
it is the report of `-v` (the bit `RATPOINTS_VERBOSE` of the flags), whether the search stops at
the first point counted (`-1`), whether the points at infinity are kept (`-I`, and not `-i`),
whether no point is printed (`-z`, and not `-Z`), the format of a point (`-f`), none for the default
(`Ratpoints.Cli.defaultFormat`), the strings before, between and after the points (`-fs`,
`-fm`, `-fe`), none for none, and the exact ends of the search intervals of the command line, which
`process` reads (`ends`, as the options `-l` and `-u` fill it: `Ratpoints.Cli.Intervals`).

C: `main.c:57-64`, `main.c:383-390`, `ratpoints.h:407`

Deviation: a structure for the global variables; `Option String` for the strings and the format,
`none` for the null pointer, and Lean strings for the C strings of the command line, which the Lean
runtime decodes as UTF-8 (bytes that do not form UTF-8 are read as U+FFFD, one for each malformed
sequence as the Lean runtime cuts them, where `main.c` copies the bytes); the bit
`RATPOINTS_VERBOSE` of `args->flags` a field here, since the library of the model prints no report
of its own. -/
structure Output where
  /-- `quiet`: whether the report is left out. -/
  quiet : Bool := false
  /-- The bit `RATPOINTS_VERBOSE` of the flags: whether the report is that of `-v`. -/
  verbose : Bool := false
  /-- `one_point`: whether the search stops at the first point that `process` does not pass over
  (the first point counted, printed or not). -/
  onePoint : Bool := false
  /-- `points_at_infty`: whether the points at infinity are kept (counted, able to stop the search
  under `-1`, and printed unless `-z`), not passed over as under `-i`. -/
  pointsAtInfty : Bool := true
  /-- `no_output`: whether no point is printed (they are counted). -/
  noOutput : Bool := false
  /-- `print_format`: the format of a point, none for the default. -/
  printFormat : Option String := none
  /-- `string_before`: the string before the points. -/
  stringBefore : Option String := none
  /-- `string_between`: the string between two points. -/
  stringBetween : Option String := none
  /-- `string_after`: the string after the points. -/
  stringAfter : Option String := none
  /-- `ends`: the exact ends of the search intervals of the command line, `ends[2 i] ≤ x ≤
  ends[2 i + 1]` for the `i`-th, as `Ratpoints.Cli.input` takes them from the reading of the
  options (`Ratpoints.Cli.Intervals.ends`). -/
  ends : Array ExactEnd := #[]

/-- The state of the reading of the search intervals by `read_input` of `main.c`: whether the last
end read is a lower one (`l_seen`), the number of the intervals read (`num_inter`), and the arrays
`domain` and `ends` of `main.c` as the options `-l` and `-u` fill them, of `2 maxDegree` entries,
the doubles of the ends that the library is given and the exact ends,
`ends[2 i] ≤ x ≤ ends[2 i + 1]` for the `i`-th interval.

C: `main.c:66`, `main.c:73`, `main.c:317`, `main.c:319`

Deviation: a structure for the two locals of `read_input` and the two global arrays, whose entries
are zero (the doubles) and `0` (the exact ends, as `mpq_init` sets them, `main.c:205`) at the start;
pairs of doubles for the entries of the type `ratpoints_interval`; a natural number for the `long`
`num_inter`. -/
structure Intervals where
  /-- `l_seen`: whether the last end read is a lower one, whose interval is not complete. -/
  lSeen : Bool := false
  /-- `num_inter`: the number of the complete intervals read. -/
  numInter : Nat := 0
  /-- `domain`: the doubles of the ends of the intervals, the lower and the upper one, that the
  library is given. -/
  domain : Array (Double × Double) := .replicate (2 * maxDegree) (.zero, .zero)
  /-- `ends`: the exact ends of the intervals, `ends[2 i]` the lower and `ends[2 i + 1]` the upper
  end of the `i`-th. -/
  ends : Array ExactEnd := .replicate (2 * maxDegree) {}

/-- The reading `iv` of the search intervals after a lower end `a` (`-l a`), as `read_input` of
`main.c` reads it: error 7 after another lower end (`-l -l`), when `Ratpoints.maxDegree` intervals
have been read, when `a` is not a number (`Ratpoints.Cli.scanEnd` with the direction `-1`), and when
it is not above the upper end of the interval before, compared as the numbers they are
(`Ratpoints.Cli.cmpEnd`); otherwise the exact end and its double as the lower end of the next
interval, which is not complete.

C: `main.c:401-413` -/
def Intervals.lower (iv : Intervals) (a : String) : Except Failure Intervals := do
  if iv.lSeen then throw .intervals
  let n := iv.numInter
  if n = maxDegree then throw .intervals
  let some (e, d) ← scanEnd a (-1) | throw .intervals
  if 0 < n && 0 ≤ cmpEnd iv.ends[2 * n - 1]! e then throw .intervals
  return { iv with
    lSeen := true, ends := iv.ends.set! (2 * n) e, domain := iv.domain.set! n (d, iv.domain[n]!.2) }

/-- The reading `iv` of the search intervals after an upper end `a` (`-u a`), for the height bound
`H`, as `read_input` of `main.c` reads it: without a lower end before it, the lower end of the first
interval is `-∞`, with the double of `-Ratpoints.Cli.heightEnd H`, and the upper end of another one
fails with error 7 (`-u -u`); error 7 when `a` is not a number (`Ratpoints.Cli.scanEnd` with the
direction `1`); its double is the upper one of the interval, whose lower double is `-∞` when the
interval has no lower end and its upper double lies below `-Ratpoints.Cli.heightEnd H` (an interval
that holds no `x` of the search, made `[-∞, u]` rather than turned around); error 7 when the lower
end is above the upper one, compared as the numbers they are (`Ratpoints.Cli.cmpEnd`); otherwise
the interval is complete.

C: `main.c:417-436` -/
def Intervals.upper (iv : Intervals) (H : Nat) (a : String) : Except Failure Intervals := do
  let n := iv.numInter
  let mut iv := iv
  if !iv.lSeen then
    if n = 0 then
      iv := { iv with
        domain := iv.domain.set! 0 ((heightEnd H).neg, iv.domain[0]!.2)
        ends := iv.ends.set! 0 { iv.ends[0]! with inf := -1 } }
    else throw .intervals
  let some (e, d) ← scanEnd a 1 | throw .intervals
  iv := { iv with
    ends := iv.ends.set! (2 * n + 1) e, domain := iv.domain.set! n (iv.domain[n]!.1, d) }
  if !iv.lSeen && iv.domain[n]!.2.lt iv.domain[n]!.1 then
    iv := { iv with domain := iv.domain.set! n (Double.huge.neg, d) }
  if 0 < cmpEnd iv.ends[2 * n]! iv.ends[2 * n + 1]! then throw .intervals
  return { iv with lSeen := false, numInter := n + 1 }

/-- The reading `iv` of the search intervals completed after the options, for the height bound `H`,
as `read_input` of `main.c` completes it: an interval with a lower end and no upper one ends at
`+∞`, with the double `Ratpoints.Cli.heightEnd H`, or `+∞` when that lies below its lower double
(an interval that holds no `x` of the search, made `[l, +∞]` rather than turned around).

C: `main.c:669`, `main.c:673-678` -/
def Intervals.complete (iv : Intervals) (H : Nat) : Intervals :=
  if iv.lSeen then
    let n := iv.numInter
    let up := heightEnd H
    let up := if up.lt iv.domain[n]!.1 then Double.huge else up
    { iv with
      domain := iv.domain.set! n (iv.domain[n]!.1, up)
      ends := iv.ends.set! (2 * n + 1) { iv.ends[2 * n + 1]! with inf := 1 }
      numInter := n + 1 }
  else iv

/-- The settings of the output `u` with the field that the option `o` sets, with its argument `a`
if it takes one: the report left out for `-q` and that of `-v` for `-v`, the format for `-f`, the
strings for `-fs`, `-fm` and `-fe`, no point printed for `-z` and the points printed for `-Z`, one
point for `-1`, the points at infinity passed over for `-i` and kept for `-I`; `u` itself for every
other option. -/
def Output.store (u : Output) (o : String) (a : Option String) : Output :=
  match o.toList with
  | '-' :: 'q' :: _ => { u with quiet := true }
  | '-' :: 'v' :: _ => { u with verbose := true }
  | ['-', 'f'] => { u with printFormat := a }
  | '-' :: 'f' :: 's' :: _ => { u with stringBefore := a }
  | '-' :: 'f' :: 'm' :: _ => { u with stringBetween := a }
  | '-' :: 'f' :: 'e' :: _ => { u with stringAfter := a }
  | '-' :: 'z' :: _ => { u with noOutput := true }
  | '-' :: 'Z' :: _ => { u with noOutput := false }
  | '-' :: '1' :: _ => { u with onePoint := true }
  | '-' :: 'i' :: _ => { u with pointsAtInfty := false }
  | '-' :: 'I' :: _ => { u with pointsAtInfty := true }
  | _ => u

/-- The options `t` of the search with the field that the option `o` sets, with its argument `a` if
it takes one: the reversal forbidden for `-k` and allowed for `-K`; the depth `-1` of the Sturm step
for `-s`, and for `-S` the C `long` of `a`, or `Ratpoints.defaultSturm` if there is none; the C
`long` of `a` as the least denominator for `-dl` and as the largest for `-du`; the exact check off
for `-x` and on for `-X`; one point of each pair for `-y` and both for `-Y`; `t` itself for every
other option. -/
def _root_.Ratpoints.Options.store (t : Options) (o : String) (a : Option String) : Options :=
  match o.toList, a.bind longOfString? with
  | '-' :: 'k' :: _, _ => { t with reverse := false }
  | '-' :: 'K' :: _, _ => { t with reverse := true }
  | '-' :: 's' :: _, _ => { t with sturm := -1 }
  | '-' :: 'S' :: _, v => { t with sturm := v.getD defaultSturm }
  | '-' :: 'd' :: 'l' :: _, some v => { t with bLow := v }
  | '-' :: 'd' :: 'u' :: _, some v => { t with bHigh := v }
  | '-' :: 'x' :: _, _ => { t with noCheck := true }
  | '-' :: 'X' :: _, _ => { t with noCheck := false }
  | '-' :: 'y' :: _, _ => { t with noY := true }
  | '-' :: 'Y' :: _, _ => { t with noY := false }
  | _, _ => t

/-- The values of the options of the command line for the height bound `H`, those that set the
sieving parameters, the options of the search (`Ratpoints.Options`), the settings of the output
(`Ratpoints.Cli.Output`) and the reading of the search intervals (`Ratpoints.Cli.Intervals`),
starting from `s`, or the first failure among the options, the words that follow the coefficients
and the height bound on the command line, read from left to right as `main.c` reads them: an option
that fails by `Ratpoints.Cli.optionArg`, or one whose argument is missing or malformed (error 6, and
error 7 for `-l` and `-u`), fails; `-p`, `-n`, `-N`, `-P` and `-F` set the fields of
`Ratpoints.SieveOptions` to the C `long` that follows them, the last one winning, and `-j` switches
the Jacobi test off and `-J` on again, as `main.c` sets the fields and the flags of its
`ratpoints_args`; `-k` forbids the reversal of the polynomial and `-K` allows it again, `-s` sets
the depth of the Sturm step to `-1`, which switches the step off, and `-S` to the C `long` that the
next word gives if there is one and it does not start with `-`, and else to
`Ratpoints.defaultSturm`, so that the step is on unless that depth is negative; `-dl` and `-du` set
the least and the largest denominator to the C `long` that follows them; `-l` and `-u` read a lower
and an upper end of a search interval (`Ratpoints.Cli.Intervals.lower`,
`Ratpoints.Cli.Intervals.upper`); `-x` switches the exact check off and `-X` on again, `-y` makes
the search deliver one point of each pair and `-Y` both; `-f`, `-fs`, `-fm` and `-fe` take the next
word, whatever it is, as the format or the string, and `-q -v -z -Z -1 -i -I` set the settings of
the output (`Ratpoints.Cli.Output.store`); of each setting the last one wins. It ignores the other
tuning options, which tune only the heuristics of the C program (until stage I) and its threads.

C: `main.c:393-400`, `main.c:414-416`, `main.c:437-532`, `main.c:533-577`, `main.c:578-593`,
`main.c:594-601`, `main.c:602-637`, `main.c:638-649`, `main.c:650-668`

Deviation: the arguments of the tuning options other than `-p -n -N -P -F` are checked and then
ignored: those of `-r -R -U -C -A -Q -W` until stage I, which models the choice of the moduli by the
curve and its correction, and that of `-t`, the number of threads, for good; the strings of `-f`,
`-fs`, `-fm` and `-fe` kept as values, for the copies that `main.c` allocates, with error 10 when
the allocation fails, which the model cannot meet. -/
def checkOptions (H : Nat) (s : SieveOptions × Options × Output × Intervals) :
    List String → Except Failure (SieveOptions × Options × Output × Intervals)
  | [] => return s
  | o :: os =>
    match optionArg o with
    | .error f => throw f
    | .ok none => checkOptions H (store s o none) os
    | .ok (some .bound) =>
      match os, s with
      | a :: os, (s, t, u, iv) => do
        checkOptions H (s, t, u, ← if o.toList[1]? == some 'l' then iv.lower a else iv.upper H a) os
      | [], _ => throw .intervals
    | .ok (some arg) =>
      if arg matches .optionalLong && os.head?.all (·.startsWith "-") then
        checkOptions H (store s o none) os
      else
        match os with
        | a :: os =>
          if arg.accepts a then checkOptions H (store s o (some a)) os
          else throw .optionSyntax
        | [] => throw .optionSyntax
where
  /-- `s` with the field that the option `o` sets, with its argument `a` if it takes one: the C
  `long` of `a` for `-p -n -N -P -F`; the Jacobi test off for `-j` and on for `-J`; the options of
  the search by `Ratpoints.Options.store` and the settings of the output by
  `Ratpoints.Cli.Output.store`. -/
  store (s : SieveOptions × Options × Output × Intervals) (o : String) (a : Option String) :
      SieveOptions × Options × Output × Intervals :=
    let (s, t, u, iv) := s
    let (t, u) := (t.store o a, u.store o a)
    match o.toList, a.bind longOfString? with
    | '-' :: 'p' :: _, some v => ({ s with numPrimes := v }, t, u, iv)
    | '-' :: 'n' :: _, some v => ({ s with sp1 := v }, t, u, iv)
    | '-' :: 'N' :: _, some v => ({ s with sp2 := v }, t, u, iv)
    | '-' :: 'P' :: _, some v => ({ s with sp3Extra := v }, t, u, iv)
    | '-' :: 'F' :: _, some v => ({ s with maxForbidden := v }, t, u, iv)
    | '-' :: 'j' :: _, _ => ({ s with jacobi := false }, t, u, iv)
    | '-' :: 'J' :: _, _ => ({ s with jacobi := true }, t, u, iv)
    | _, _ => (s, t, u, iv)

/-- The format of a point that `main.c` takes when the command line gives none: `(%x : %z)` and a
line feed when the points are not checked exactly or only one point of each pair is delivered
(`Ratpoints.Options.noCheck`, `Ratpoints.Options.noY`), else `(%x : %y : %z)` and a line feed.

C: `main.c:681-685` -/
def defaultFormat (o : Options) : String :=
  if o.noCheck || o.noY then "(%x : %z)\n" else "(%x : %y : %z)\n"

/-- What a command line (the words after the name of the program) gives: the coefficient list, the
height bound and the values of the options, those that set the sieving parameters, the options of
the search and the settings of the output, or the first failure, in the order of `main.c`: fewer
than two words fail with error 2; then come the coefficients (`Ratpoints.Cli.coefficients`), the
height bound (`Ratpoints.Cli.heightBound`) and the options (`Ratpoints.Cli.checkOptions`), read from
the defaults of `Ratpoints.SieveOptions`, `Ratpoints.Options` with the height bound as the largest
denominator, `Ratpoints.Cli.Output` and `Ratpoints.Cli.Intervals`, the values of a command line
without options; then an interval with a lower end and no upper one is completed
(`Ratpoints.Cli.Intervals.complete`), the search intervals of the options are those read, their
doubles, and the exact ends those of the settings of the output, the format is the default
(`Ratpoints.Cli.defaultFormat`) unless an option `-f` gave one, and `-q` cancels `-v`.

C: `main.c:210-214`, `main.c:315-316`, `main.c:333-336`, `main.c:380`, `main.c:679`,
`main.c:688`, `main.c:691-692`

Deviation: `read_input` never returns a value other than 0, so the usage that `main.c` prints
then (lines 212 and 213) has no counterpart; the largest denominator `-1` of line 336, which line
380 replaces by the height bound, not set; the search intervals a list of the intervals read, for
the pointer `args->domain` to the array `domain` and the number `args->num_inter`. -/
def input : List String → Except Failure (List Int × Nat × SieveOptions × Options × Output)
  | s :: h :: os => do
    let c ← coefficients s
    let H ← heightBound h
    let (s, o, u, iv) ← checkOptions H ({}, { bHigh := H }, {}, {}) os
    let iv := iv.complete H
    let o := { o with domain := iv.domain.toList.take iv.numInter }
    let u := { u with
      printFormat := u.printFormat.getD (defaultFormat o)
      verbose := u.verbose && !u.quiet
      ends := iv.ends }
    return (c, H, s, o, u)
  | _ => throw .tooFewArguments

/-! ### The points -/

/-- What `main.c` prints for a backslash followed by the character `ch` in a format or in a string:
a tab for `t`, a line feed for `n`, a backslash for a backslash, a percent sign for `%`, and the
backslash and `ch` as they are for every other character.

C: `main.c:178-182`, `main.c:961-965`

Deviation: one function for the two switches of `process` and `print_string`, which agree. -/
def escape (ch : Char) : String :=
  match ch with
  | 't' => "\t"
  | 'n' => "\n"
  | '\\' => "\\"
  | '%' => "%"
  | ch => "\\".push ch

/-- What `print_string` of `main.c` prints for the string `s`: nothing for none; otherwise its
characters as they are, but a backslash, which `Ratpoints.Cli.escape` prints with the character
after it, and a backslash at the end, which prints itself and ends the string.

C: `main.c:952-960`, `main.c:966-968`

Deviation: a recursion over the characters, for the loop over the C string. -/
def printString (s : Option String) : String :=
  go (s.getD "").toList
where
  /-- What `print_string` prints for the characters `s`. -/
  go : List Char → String
    | [] => ""
    | ['\\'] => "\\"
    | '\\' :: ch :: s => escape ch ++ go s
    | ch :: s => ch.toString ++ go s

/-- What `process` of `main.c` prints for the point `(x : y : z)` in the format `fmt`, character by
character: `%x`, `%y` and `%z` print `x`, `y` and `z` in decimal, but `%y` prints itself when `noY`
is set (the points were not checked exactly or only one point of each pair is delivered), a percent
sign before another character prints both, and one at the end prints itself and ends the format; a
backslash and the character after it print as `Ratpoints.Cli.escape` prints them, and one at the
end prints itself and ends the format; every other character prints itself.

C: `main.c:157-177`, `main.c:183-186`

Deviation: a recursion over the characters, for the loop over the C string; an `Int` for the GMP
integer `y` and for the `long`s `x` and `z`, which print alike. -/
def formatPoint (noY : Bool) (x z y : Int) : List Char → String
  | [] => ""
  | ['%'] => "%"
  | '%' :: ch :: fmt =>
    (match ch with
      | 'x' => toString x
      | 'y' => if noY then "%y" else toString y
      | 'z' => toString z
      | ch => "%".push ch) ++ formatPoint noY x z y fmt
  | ['\\'] => "\\"
  | '\\' :: ch :: fmt => escape ch ++ formatPoint noY x z y fmt
  | ch :: fmt => ch.toString ++ formatPoint noY x z y fmt

/-- The data that `main.c` passes to its callback `process` through `info`: whether it has printed
a point (`print_between`), the settings of the output that it reads, whether `%y` prints itself
(`no_y`), the number of the search intervals of the command line and their exact ends, against
which `process` checks the points, and the text printed so far.

C: `main.c:110-113`

Deviation: the text printed so far, for the standard output, to which `process` prints; an array
for the pointer `ends` and a natural number for the `long` `num_inter`. -/
structure Data where
  /-- `print_between`: whether a point was printed, so that the next one comes after `-fm`. -/
  printBetween : Bool
  /-- `no_output`: whether no point is printed. -/
  noOutput : Bool
  /-- `one_point`: whether the search stops at the first point that `process` does not pass over
  (the first point counted, printed or not). -/
  onePoint : Bool
  /-- `points_at_infty`: whether the points at infinity are kept (counted, able to stop the search
  under `-1`, and printed unless `-z`), not passed over as under `-i`. -/
  pointsAtInfty : Bool
  /-- `no_y`: whether `%y` prints itself. -/
  noY : Bool
  /-- `pf`: the format of a point. -/
  pf : String
  /-- `string_before`: the string before the points. -/
  stringBefore : Option String
  /-- `string_between`: the string between two points. -/
  stringBetween : Option String
  /-- `num_inter`: the number of the search intervals of the command line, `0` for none. -/
  numInter : Nat
  /-- `ends`: the exact ends of the search intervals of the command line. -/
  ends : Array ExactEnd
  /-- The text printed so far. -/
  out : String

/-- The data that `main.c` passes to `process` for the settings of the output `u` and the options
`o` of the search: no point printed yet, the settings of `u`, `%y` printing itself when the points
are not checked exactly or only one point of each pair is delivered, and the number of the search
intervals of the command line, as read before `Ratpoints.Cli.joinIntervals` joins them, with their
exact ends.

C: `main.c:235-242`, `main.c:246-247`

Deviation: the format the one that `Ratpoints.Cli.input` settled, `""` if none. -/
def Data.ofOutput (u : Output) (o : Options) : Data where
  printBetween := false
  noOutput := u.noOutput
  pf := u.printFormat.getD ""
  onePoint := u.onePoint
  pointsAtInfty := u.pointsAtInfty
  stringBefore := u.stringBefore
  stringBetween := u.stringBetween
  noY := o.noCheck || o.noY
  numInter := o.domain.length
  ends := u.ends
  out := ""

/-- The callback `process` of `main.c` on the point `(x : y : z)` with the data `info`: a point at
infinity (`z = 0`) is passed over when the points at infinity are not kept (`-i`), and an affine
point when the command line gives search intervals and `x / z` lies in none of them
(`Ratpoints.Cli.inRegion`), which the library may find just beyond an end, since it searches
intervals whose ends are the doubles outward of those of the command line: such a point has the
weight `0` and leaves the flag clear, so that it is neither counted nor stops the search under
`-1`; every other point stops the search when one point is enough, and has the weight `1`; it is
printed unless no point is printed: after the string before the points if it is the first point
printed, and else after the string between them, in the format (`Ratpoints.Cli.formatPoint`).

C: `main.c:139-142`, `main.c:150-156`, `main.c:187-189`

Deviation: the data a value, for the pointer `info`, and returned with the weight and the flag, for
the `int *quit` that the library passes, which is clear at every call; the text appended to that of
the data, for the standard output, and no `fflush`. -/
def process (x z y : Int) (info : Data) : Answer Data :=
  if z == 0 && !info.pointsAtInfty then ⟨0, false, info⟩
  else if z != 0 && 0 < info.numInter && !Id.run (inRegion x z info.ends info.numInter) then
    ⟨0, false, info⟩
  else if info.noOutput then ⟨1, info.onePoint, info⟩
  else
    let s := printString (if info.printBetween then info.stringBetween else info.stringBefore)
    ⟨1, info.onePoint, { info with
      printBetween := true
      out := info.out ++ s ++ formatPoint info.noY x z y info.pf.toList }⟩

/-! ### The report -/

/-- The polynomial with the coefficient list `c`, constant term first, as `print_poly` of `main.c`
prints it: its terms from the highest degree `c.length - 1` down, the zero ones left out, the first
after `- ` if it is negative and the others after ` + ` or ` - `, each the absolute value of its
coefficient, then `x` for the degree 1 and `x^i` for a degree `i ≥ 2`, the coefficient left out
when it is `1` there; and a line feed.

C: `main.c:913-949`

Deviation: a fold over the coefficients, for the loop; no `fflush`. -/
def printPoly (c : List Int) : String :=
  let term (a : Int) (i : Nat) : String :=
    match i, a.natAbs with
    | 0, n => toString n
    | 1, 1 => "x"
    | 1, n => s!"{n} x"
    | i, 1 => s!"x^{i}"
    | i, n => s!"{n} x^{i}"
  let step (acc : String × Bool) (ai : Int × Nat) : String × Bool :=
    if ai.1 == 0 then acc
    else
      let sign := if 0 < ai.1 then (if acc.2 then " + " else "") else if acc.2 then " - " else "- "
      (acc.1 ++ sign ++ term ai.1 ai.2, true)
  (c.zipIdx.reverse.foldl step ("", false)).1 ++ "\n"

/-- The messages of the report of `main.c` that `ratpoints-lean` prints, with the data they read:
message 0, the banner; message 2, the count of the points found, of the pairs when the points are
not checked exactly or only one point of each pair is delivered; message 3, the search region of
the command line; message 5, the curve; message 6, the height bound; message 7, what the search did:
whether the polynomial was reversed, whether the denominators could be restricted to squares
(`RATPOINTS_USE_SQUARES`) or essentially to squares (`RATPOINTS_USE_SQUARES1`), whether the Jacobi
test was off, and whether the points were not checked exactly; and message 8, the search intervals
as the search leaves them. -/
inductive Message where
  /-- Message 0: the banner. -/
  | banner
  /-- Message 2: the count `total`, of the pairs when `pairs` is set. -/
  | count (total : Int) (pairs : Bool)
  /-- Message 3: the search region of the command line, the doubles `dom` of its intervals before
  they are joined. -/
  | region (dom : List (Double × Double))
  /-- Message 5: the curve of the coefficient list `c`. -/
  | curve (c : List Int)
  /-- Message 6: the height bound `H`. -/
  | height (H : Nat)
  /-- Message 7: the flags of the search. -/
  | flags (reversed useSquares useSquares1 noJacobi noCheck : Bool)
  /-- Message 8: the search intervals `dom` as the search leaves them. -/
  | intervals (dom : List (Double × Double))

/-- The intervals `dom` as messages 3 and 8 of `main.c` print them: each as `[l, u]` with its ends
printed under `%f` (`Ratpoints.Cli.printF`), the intervals separated by ` U `. -/
def showIntervals (dom : List (Double × Double)) : String :=
  " U ".intercalate (dom.map fun (l, u) ↦ s!"[{printF l}, {printF u}]")

/-- The text of a message of the report, as `message` of `main.c` prints it.

C: `main.c:972-976`, `main.c:979-991`, `main.c:999-1033`

Deviation: the banner of `ratpoints-lean` (`Ratpoints.Cli.banner`); a constructor for each message
that `ratpoints-lean` prints, with its data, for the number `n` and the arguments of the library:
message 1, which the program prints when `read_input` fails, which it never does, is left out, and
message 4, on the moduli used, is stage I; the loops over the intervals of messages 3 and 8 as
`Ratpoints.Cli.showIntervals`, the conversion `%lf` of message 8 being `%f`; no `fflush`. -/
def Message.text : Message → String
  | .banner => s!"\n{Cli.banner}\n"
  | .count total pairs =>
    s!"\n{total} rational point{if pairs then " pair" else ""}s found.\n\n"
  | .region dom => s!"Search region:\n  {showIntervals dom}\n"
  | .curve c => s!"\nCurve equation is  y^2 = {printPoly c}\n"
  | .height H => s!"max. Height = {H}\n"
  | .flags rev us us1 nj nc =>
    (if rev then "Polynomial was reversed for better performance.\n" else "") ++
    (if us then "(Reversed) polynomial is +-monic of odd degree:\n" ++
      "  could restrict denominators to squares.\n" else "") ++
    (if us1 then "(Reversed) polynomial has odd degree:\n" ++
      "  could restrict denominators essentially to squares.\n" else "") ++
    (if nj then "Jacobi symbol test was not used.\n" else "") ++
    (if nc then "Points were not checked exactly:\n" ++
      "   some of the printed x-coordinates may not give points.\n" else "")
  | .intervals dom => s!"Search intervals:\n{showIntervals dom}\n"

/-- What `main.c` prints before the search for the settings of the output `u`: nothing when the
report is left out (`-q`); otherwise the banner, the curve of the coefficient list `c`, unless the
report is that of `-v` the height bound `H` and a blank line, and the search region (message 3) when
the command line gives search intervals, their doubles `dom` before they are joined, also under
`-v`.

C: `main.c:215-220`, `main.c:224` -/
def preamble (c : List Int) (H : Nat) (u : Output) (dom : List (Double × Double)) : String :=
  if u.quiet then ""
  else Message.banner.text ++ (Message.curve c).text ++
    (if u.verbose then "" else (Message.height H).text ++ "\n") ++
    if dom.isEmpty then "" else (Message.region dom).text

/-- What `main.c` prints after the points for the settings of the output `u`: nothing when the
report is left out (`-q`); otherwise, unless the report is that of `-v`, two line feeds, what the
search did (message 7), from the flags that the search `r` writes back, the Jacobi switch of the
options `s` and the switch of the exact check of the options `o`, and the search intervals as the
search leaves them (message 8, from `r.domain`); then the count of the points found, the count
`total` of the search, of the pairs under `-x` or `-y` (message 2).

C: `main.c:268-276`

Deviation: message 4 (the moduli used; stage I) is left out. -/
def report {σ : Type} (s : SieveOptions) (o : Options) (u : Output) (r : Outcome σ) : String :=
  let flags := Message.flags r.reversed r.useSquares r.useSquares1 (!s.jacobi) o.noCheck
  if u.quiet then ""
  else (if u.verbose then "" else "\n\n" ++ flags.text ++ (Message.intervals r.domain).text) ++
    (Message.count r.total (o.noCheck || o.noY)).text

/-! ### The program -/

/-- What `ratpoints-lean` does on the command line `args` (the words after the name of the program):
the text it prints on the standard output and its exit status. On the coefficient list `c`, the
height bound `H`, the values `s` of the options that set the sieving parameters, the options `o` of
the search and the settings `u` of the output, as `Ratpoints.Cli.input` reads them, it prints the
head of the report (`Ratpoints.Cli.preamble`, nothing under `-q`), and then runs the search
`Ratpoints.findPointsVerbose` with the options `s` of the sieve, with the array size that the
program sets, `Ratpoints.defaultArraySize`, the options `o` with the search intervals joined
(`Ratpoints.Cli.joinIntervals`), the callback `Ratpoints.Cli.process` on its data
(`Ratpoints.Cli.Data.ofOutput`, with the intervals of the command line before they are joined), and
the print channel that prints nothing: on a refusal it prints what the library printed and the
message of the failure (`Ratpoints.Cli.Failure.ofRefusal`) and exits with its status; otherwise it
prints what the callback and the library printed, the string before the points if the callback
printed no point, the string after the points and the end of the report
(`Ratpoints.Cli.report`, nothing under `-q`), and exits with status 0; on a failure `f` of the
command line it prints `f.message` and exits with `f.status` (`Ratpoints.Cli.Failure.message`,
`Ratpoints.Cli.Failure.status`).

C: `main.c:195-198`, `main.c:221-222`, `main.c:248`, `main.c:251-252`, `main.c:265`, `main.c:267`,
`main.c:284-285`

Deviation: the text written once at the end (`Ratpoints.Cli.main`), where `main.c` prints as it
goes; the print channel that prints nothing passed for the bit `RATPOINTS_VERBOSE` of the flags,
which the program sets under `-v`, the report of the library under it coming with stage I. -/
def run (args : List String) : String × UInt32 :=
  match input args with
  | .error f => (f.message, f.status)
  | .ok (c, H, s, o, u) =>
    let pre := preamble c H u o.domain
    let info := Data.ofOutput u o
    let o := { o with domain := Id.run (joinIntervals o.domain) }
    match findPointsVerbose c H { s with arraySize := defaultArraySize } o process info
        (fun _ d ↦ d) with
    | .error (e, d) => let f := Failure.ofRefusal e; (pre ++ d.out ++ f.message, f.status)
    | .ok r =>
      let before := if r.info.printBetween then "" else printString u.stringBefore
      (pre ++ r.info.out ++ before ++ printString u.stringAfter ++ report s o u r, 0)

/-- The program `ratpoints-lean`: it prints the text of `Ratpoints.Cli.run` on the standard
output, in one write once it is computed, and exits with its status. Like ratpoints, it ignores
a failed write, but for one case: when the reader of the output is gone, the write fails with
`IO.Error.resourceVanished`, since the Lean runtime ignores the signal `SIGPIPE` that ends
ratpoints then, and the program exits quietly with the status 141 that the shell reports for
ratpoints (where `SIGPIPE` has its default action). It flushes the standard output itself, since
a short output waits in the buffer of the C library until the exit, where a failed write goes
unnoticed. -/
def main (args : List String) : IO UInt32 := do
  let (out, status) := run args
  let stdout ← IO.getStdout
  try
    stdout.putStr out
    stdout.flush
  catch
    | .resourceVanished .. => return 141
    | _ => pure ()
  return status

/-! ### Examples

Each of them is what ratpoints 3.1.1 does, but for the banner; and for message 4 of the report
and, under `-v`, the report of the library, which `ratpoints-lean` leaves out. -/

#guard (coefficients " +1\t0  -1 ").toOption == some [1, 0, -1]

-- `maxDegree + 1` coefficients are read, one more fail with error 3.
#guard (coefficients (" ".intercalate (List.replicate (maxDegree + 1) "1"))).toOption.isSome &&
  run [" ".intercalate (List.replicate (maxDegree + 2) "1"), "5"] ==
    ("\nToo many coefficients.\n\n", 3)

#guard run ["1 2 x", "10"] ==
  ("\nIncorrect coefficients (not integers separated by blanks).\n\n", 11)

#guard run ["", "abc"] == ("\nThe polynomial must have degree at least 1.\n\n", 5)

#guard run ["1 0 1", "1_0"] == ("\nIncorrect height argument.\n\n", 4)

-- Error 8, for the refusal of a binary form that is not squarefree: `0 0 1`, which the reversal
-- check refuses, and `1 2 1`, which the remainder chain refuses; without `-q` after the head of the
-- report.
#guard (Failure.ofRefusal .notSquarefree).message == "\nPolynomial is not square-free.\n\n" &&
  (Failure.ofRefusal .notSquarefree).status == 8
#guard ["0 0 1", "1 2 1"].all fun c ↦
  run [c, "5", "-q"] == ("\nPolynomial is not square-free.\n\n", 8)
#guard run ["1 2 1", "5"] == (s!"\n{banner}\n\nCurve equation is  y^2 = x^2 + 2 x + 1\n\n" ++
  "max. Height = 5\n\n\nPolynomial is not square-free.\n\n", 8)

-- Error 9, for the refusal of malformed search intervals, with the message of `main.c`.
#guard (Failure.ofRefusal .badArgs).message == "\nBug no. 1 - please report!\n\n" &&
  (Failure.ofRefusal .badArgs).status == 9

#guard (run ["1 0 1", "5", "-q", "-r", "nan"]).2 == 6 && (run ["1 0 1", "5", "-d", "1"]).2 == 6

-- `-p 10 -n 4 -N 7 -P 3 -j -F 200 -t 2 -p 12`: the last `-p` wins, and `-t` is ignored.
#guard (checkOptions 5 ({}, {}, {}, {}) ["-p", "10", "-n", "4", "-N", "7", "-P", "3", "-j", "-F",
    "200", "-t", "2", "-p", "12"]).toOption.map (fun (o, _) ↦ (o.numPrimes, o.sp1, o.sp2,
    o.sp3Extra, o.maxForbidden, o.jacobi)) == some (12, 4, 7, 3, 200, false)

-- `-j` and `-J`: the last one wins.
#guard [(["-j", "-J"], true), (["-J", "-j"], false)].all fun (os, b) ↦
  (checkOptions 5 ({}, {}, {}, {}) os).toOption.map (·.1.jacobi) == some b

-- `-k` and `-K`, `-s` and `-S`: the last of each pair wins, and `-S` takes the next word as its
-- depth unless it starts with `-`.
#guard [(["-k", "-S", "5", "-K", "-s"], true, -1), (["-s", "-S"], true, defaultSturm),
    (["-k", "-S", "-q"], false, defaultSturm), (["-s", "-S", " 0 "], true, 0)].all
  fun (os, rev, st) ↦ (checkOptions 5 ({}, {}, {}, {}) os).toOption.map
    (fun (_, o, _) ↦ (o.reverse, o.sturm)) == some (rev, st)

-- `-x -X -y -Y -z -Z -i -I`: the last of each pair wins; `-1` has no counterpart; `-xfoo` is `-x`.
#guard (checkOptions 5 ({}, {}, {}, {}) ["-xfoo", "-Y", "-y", "-z", "-Zap", "-I", "-i", "-1x"]
    ).toOption.map (fun (_, o, u, _) ↦
      (o.noCheck, o.noY, u.noOutput, u.pointsAtInfty, u.onePoint)) ==
  some (true, true, false, false, true)

-- `-f`, `-fs`, `-fm` and `-fe` take the next word, whatever it is, the last one winning; `-fsfoo`
-- is `-fs`; `-f` without its argument and `-ffoo` are error 6.
#guard (checkOptions 5 ({}, {}, {}, {})
    ["-f", "-x", "-fsfoo", "S", "-fm", "", "-fe", "-y", "-f", "%x"]).toOption.map
    (fun (_, o, u, _) ↦ (o.noCheck, o.noY, u.printFormat, u.stringBefore,
      u.stringBetween, u.stringAfter)) ==
  some (false, false, some "%x", some "S", some "", some "-y")
#guard [["-q", "-f"], ["-q", "-fs"], ["-q", "-fm"], ["-q", "-fe"], ["-q", "-ffoo", "x"]].all
  fun os ↦ (run (["1 0 1", "5"] ++ os)).2 == 6

-- `-1 0 9`, which ratpoints reverses: its points in the order of the reversed polynomial, mapped
-- back, also after `-k -K`, and with `-k`, which forbids the reversal, in the order of the
-- reference, also after `-K -kfoo`.
#guard [[], ["-k", "-K"]].all fun os ↦ run (["-1 0 9", "4", "-q"] ++ os) ==
  ("(-1 : 0 : 3)\n(1 : 3 : 0)\n(1 : -3 : 0)\n(1 : 0 : 3)\n", 0)
#guard [["-k"], ["-K", "-kfoo"]].all fun os ↦ run (["-1 0 9", "4", "-q"] ++ os) ==
  ("(1 : 3 : 0)\n(1 : -3 : 0)\n(-1 : 0 : 3)\n(1 : 0 : 3)\n", 0)

-- `1 2 1`, which is not squarefree: searched without the Sturm step, the last of `-s` and `-S`
-- winning, also for `-S` with the argument ` -3`, a depth below 0; and refused when `-S` comes
-- last, with or without its argument, also when an option follows it.
#guard [["-s"], ["-S", "-s"], ["-S", " -3"]].all fun os ↦ run (["1 2 1", "1", "-q"] ++ os) ==
  ("(1 : 1 : 0)\n(1 : -1 : 0)\n(-1 : 0 : 1)\n(0 : 1 : 1)\n(0 : -1 : 1)\n(1 : 2 : 1)\n" ++
    "(1 : -2 : 1)\n", 0)
#guard [["-q", "-s", "-S"], ["-q", "-s", "-S", "3"], ["-s", "-S", "-q"]].all fun os ↦
  run (["1 2 1", "1"] ++ os) == ("\nPolynomial is not square-free.\n\n", 8)

-- A malformed argument of `-S`, and `-S` followed by `-3`, which is no option: error 6.
#guard ["x", "", "5x", "-3"].all fun a ↦ (run ["1 0 1", "5", "-q", "-S", a]).2 == 6

-- The points of `ratpoints '-2 0 0 1' 130 -q`, with the default parameters and with others.
#guard [[], ["-p", "0"], ["-p", "53", "-n", "5", "-N", "20", "-j"]].all fun os ↦
  run (["-2 0 0 1", "130", "-q"] ++ os) ==
    ("(1 : 0 : 0)\n(3 : 5 : 1)\n(3 : -5 : 1)\n(129 : 3830 : 100)\n(129 : -3830 : 100)\n", 0)

-- `1 0 126 0 441` at the height 200: `-1` prints the first point, `-1 -i` the first one not at
-- infinity, `-y` one point of each pair, and `-z -1` nothing.
#guard [(["-1"], "(1 : 21 : 0)\n"), (["-1", "-i"], "(0 : 1 : 1)\n"), (["-z", "-1"], ""),
    (["-y"], "(1 : 0)\n(0 : 1)\n(-1 : 2)\n(1 : 2)\n(-2 : 21)\n(2 : 21)\n")].all fun (os, out) ↦
  run (["1 0 126 0 441", "200", "-q"] ++ os) == (out, 0)

-- Formats and strings: a percent sign at the end, `%y` under `-y`, the escapes, a backslash at the
-- end of `-fe`, and `-fs`, `-fm`, `-fe` around no point.
#guard run ["1 0 126 0 441", "200", "-q", "-f", "%x %z%", "-y"] ==
  ("1 0%0 1%-1 2%1 2%-2 21%2 21%", 0)
#guard run ["1 0 126 0 441", "200", "-q", "-f", "%y\\n", "-y", "-1"] == ("%y\n", 0)
#guard run ["1 0 126 0 441", "200", "-q", "-fs", "start\\t\\\\\\%\\n", "-fe", "\\", "-1"] ==
  ("start\t\\%\n(1 : 21 : 0)\n\\", 0)
#guard run ["-1 0 -1", "50", "-q", "-fs", "S", "-fm", "M", "-fe", "E\\n"] == ("SE\n", 0)
#guard formatPoint false 1 2 3 "%%%x\\0\\a\\%\\\\\\t\\n%q".toList == "%%1\\0\\a%\\\t\n%q"

-- `2 0 4`, which ratpoints reverses: `-i` drops the caller's points at infinity, which the search
-- of the reversed polynomial finds at the denominator 1 with the numerator 0, after the numerators
-- -24 and -4 there, the caller's (-1 : ±34 : 24) and (-1 : ±6 : 4).
#guard ((run ["2 0 4", "30", "-q", "-i"]).1.splitOn "\n").take 4 ==
  ["(-1 : 34 : 24)", "(-1 : -34 : 24)", "(-1 : 6 : 4)", "(-1 : -6 : 4)"]

-- Several points with `-fs`, `-fm` and `-fe` (`-y` with the default format of the pairs); the
-- default format `(%x : %z)\n` under `-x` with `-p 30 -N 30`, whose survivors depend on the moduli
-- that the choice makes from the curve with the functions of the C library of the platform: every
-- line a normalized pair `(x : z)` of height at most 5, among them the pairs of the points that
-- `-y` prints; and `-X`, `-Y` and `-I` as the last of their pairs.
#guard run ["1 0 126 0 441", "200", "-q", "-fs", "S", "-fm", "M", "-fe", "E", "-y"] ==
  ("S(1 : 0)\nM(0 : 1)\nM(-1 : 2)\nM(1 : 2)\nM(-2 : 21)\nM(2 : 21)\nE", 0)
#guard
  let lines (out : String) : List String := (out.splitOn "\n").filter (· ≠ "")
  let pair (l : String) : Option (Int × Int) :=
    match ((l.replace "(" "").replace ")" "").splitOn " : " with
    | [x, z] => do pure ((← x.toInt?), (← z.toInt?))
    | _ => none
  let (xs, code) := run ["1 0 1", "5", "-q", "-x", "-p", "30", "-N", "30"]
  code == 0 && (lines (run ["1 0 1", "5", "-q", "-y"]).1).all (lines xs).contains &&
    (lines xs).all fun l ↦ l.startsWith "(" && l.endsWith ")" && match pair l with
      | some (x, z) => x.natAbs ≤ 5 && 0 ≤ z && z ≤ 5 && Int.gcd x z == 1 && (z != 0 || x == 1)
      | none => false
#guard [["-x", "-X"], ["-y", "-Y"], ["-i", "-I"]].all fun os ↦
  run (["1 0 126 0 441", "30", "-q"] ++ os) == run ["1 0 126 0 441", "30", "-q"]
#guard (run ["1 0 126 0 441", "30", "-q"]).1.startsWith "(1 : 21 : 0)\n(1 : -21 : 0)\n(0 : 1 : 1)\n"

-- The report of `ratpoints '1 0 126 0 441' 30 -z` and of `ratpoints '1 0 126 0 441' 30 -v -1 -y`,
-- without message 4 and without the report of the library under `-v`.
#guard run ["1 0 126 0 441", "30", "-z"] ==
  (s!"\n{banner}\n\nCurve equation is  y^2 = 441 x^4 + 126 x^2 + 1\n\nmax. Height = 30\n\n" ++
    "\n\nSearch intervals:\n[-30.000000, 30.000000]\n\n12 rational points found.\n\n", 0)
#guard run ["1 0 126 0 441", "30", "-v", "-1", "-y"] ==
  (s!"\n{banner}\n\nCurve equation is  y^2 = 441 x^4 + 126 x^2 + 1\n\n" ++
    "(1 : 0)\n\n1 rational point pairs found.\n\n", 0)

-- Message 3 under `-v`, as `ratpoints '1 0 1' 10 -v -z -l 0 -u 1` prints it: after the curve, with
-- no height line before it, and neither messages 7 nor 8 after the points.
#guard run ["1 0 1", "10", "-v", "-z", "-l", "0", "-u", "1"] ==
  (s!"\n{banner}\n\nCurve equation is  y^2 = x^2 + 1\n\nSearch region:\n  [0.000000, 1.000000]\n" ++
    "\n6 rational points found.\n\n", 0)

-- `1 0 126 0 441` at the height 200 in the search interval `[0, 1]` (`-l 0 -u 1`): message 3 before
-- the points, the points with `x / z` in `[0, 1]` and the points at infinity, and message 8.
#guard run ["1 0 126 0 441", "200", "-l", "0", "-u", "1"] ==
  (s!"\n{banner}\n\nCurve equation is  y^2 = 441 x^4 + 126 x^2 + 1\n\nmax. Height = 200\n\n" ++
    "Search region:\n  [0.000000, 1.000000]\n(1 : 21 : 0)\n(1 : -21 : 0)\n(0 : 1 : 1)\n" ++
    "(0 : -1 : 1)\n(1 : 31 : 2)\n(1 : -31 : 2)\n(2 : 651 : 21)\n(2 : -651 : 21)\n\n\n" ++
    "Search intervals:\n[0.000000, 1.000000]\n\n8 rational points found.\n\n", 0)

-- Two intervals whose doubles meet, joined for the search (the double nearest to `1 / 3` lies
-- outward of both ends), so that `process` passes over `(1 : 0 : 3)`, which the search finds
-- between them; and the range of the denominators `4, …, 9` (`-dl 4 -du 9`).
#guard run ["-1 0 9", "10", "-q", "-u", "0.3333333333333333", "-l", "0.33333333333333337"] ==
  ("(1 : 3 : 0)\n(1 : -3 : 0)\n(-1 : 0 : 3)\n(-5 : 12 : 9)\n(-5 : -12 : 9)\n(5 : 12 : 9)\n" ++
    "(5 : -12 : 9)\n", 0)
#guard run ["17 0 0 1", "300", "-q", "-dl", "4", "-du", "9"] ==
  ("(1 : 0 : 0)\n(1 : 66 : 4)\n(1 : -66 : 4)\n(-8 : 327 : 9)\n(-8 : -327 : 9)\n" ++
    "(106 : 3291 : 9)\n(106 : -3291 : 9)\n", 0)

-- Messages 3 and 8: `-0.0` and an infinity in message 3, the ends `±2 ^ 63` that the Sturm step
-- leaves for the infinite ones in message 8; a first `-u` below `-H`, whose lower end is `-∞`;
-- two intervals of the command line joined into one search interval; and an interval beyond the
-- doubles, where message 8 has no interval and only the points at infinity are found.
#guard [(["-l", "-0", "-u", "1e400"], ["  [-0.000000, inf]",
      "[-0.000000, 9223372036854775808.000000]", "8 rational points found."]),
    (["-u", "-20"], ["  [-inf, -20.000000]", "[-9223372036854775808.000000, -20.000000]",
      "2 rational points found."]),
    (["-u", "0.74999999999999999", "-l", "0.75", "-u", "1"],
      ["  [-10.000000, 0.750000] U [0.750000, 1.000000]", "[-10.000000, 1.000000]",
        "10 rational points found."]),
    (["-l", "1e400", "-u", "1e500"], ["  [inf, inf]", "2 rational points found."])].all
  fun (os, ls) ↦ (((run (["1 0 1", "10", "-z"] ++ os)).1.splitOn "\n").filter
    (fun l ↦ l ≠ "" && l.front != 'S')).drop 7 == ls

-- Error 7: an end missing or not a number, two lower or two upper ends in a row, ends not
-- ordered (also `-u 0.75 -l 0.75`, though `[1, 1]` is an interval), and more than
-- `Ratpoints.maxDegree` intervals; error 6 for a missing or malformed bound of the denominators.
#guard run ["1 0 1", "5", "-q", "-l"] == (Failure.intervals.message, 7) &&
  Failure.intervals.message ==
    "\nIncorrect interval arguments (not numbers, not alternating, too many, or not ordered).\n\n"
#guard [["-l", "x"], ["-l", "1", "-l", "2"], ["-u", "1", "-u", "2"], ["-l", "2", "-u", "1"],
    ["-u", "0.75", "-l", "0.75"], ["-l", "nan"], ["-l", "1", "-u", "2", "-l", "3", "-l", "4"]].all
  fun os ↦ (run (["1 0 1", "5", "-q"] ++ os)).2 == 7
#guard (run (["1 0 1", "5", "-q", "-z", "-l", "1", "-u", "1"])).2 == 0
#guard
  let os := (List.range maxDegree).flatMap fun i ↦
    ["-l", toString (2 * i), "-u", toString (2 * i + 1)]
  (run (["1 0 1", "5", "-q", "-z"] ++ os)).2 == 0 &&
    (run (["1 0 1", "5", "-q", "-z"] ++ os ++ ["-l", toString (2 * maxDegree + 100)])).2 == 7
#guard [["-dl"], ["-dl", "x"], ["-du", "1.5"]].all fun os ↦
  (run (["1 0 1", "5", "-q"] ++ os)).2 == 6

-- The curves of `ratpoints c 20 | grep 'Curve equation'`.
#guard [("-1 1 -1 1", "x^3 - x^2 + x - 1"), ("0 -2 0 1", "x^3 - 2 x"),
    ("1 0 0 0 0 -1", "- x^5 + 1"), ("-12 0 0 7", "7 x^3 - 12"), ("1 -1", "- x + 1"),
    ("0 1", "x")].all fun (c, s) ↦ printPoly ((coefficients c).toOption.getD []) == s ++ "\n"

-- Message 7: the reversal, the squares, the Jacobi test and the exact check of
-- `ratpoints '0 1 2' 40 -j -x -z -n 15 -N 30 -p 30`, and the divisors of the leading coefficient of
-- `ratpoints '1 0 0 6' 200 -y -z`; the count of the pairs under `-x`, the survivors of the sieve,
-- which depend on the choice of the moduli, masked.
#guard ((((run ["0 1 2", "40", "-j", "-x", "-z", "-n", "15", "-N", "30", "-p", "30"]).1.splitOn
    "\n").filter (· ≠ "")).drop 7).map (fun l ↦ if l.endsWith " rational point pairs found."
      then (l.dropWhile Char.isDigit).copy else l) ==
  ["Polynomial was reversed for better performance.",
    "(Reversed) polynomial is +-monic of odd degree:", "  could restrict denominators to squares.",
    "Jacobi symbol test was not used.", "Points were not checked exactly:",
    "   some of the printed x-coordinates may not give points.", "Search intervals:",
    "[-2.000000, 40.000000]", " rational point pairs found."]
#guard (((run ["1 0 0 6", "200", "-y", "-z"]).1.splitOn "\n").filter (· ≠ "")).drop 7 ==
  ["(Reversed) polynomial has odd degree:", "  could restrict denominators essentially to squares.",
    "Search intervals:", "[-0.550781, 200.000000]", "8 rational point pairs found."]

end Cli

end Ratpoints

end

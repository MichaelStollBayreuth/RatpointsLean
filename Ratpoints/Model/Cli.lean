/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.FindPoints

-- The `#guard` examples run the sieve at compile time.
meta import Ratpoints.Model.FindPoints

/-!
# The command-line program `ratpoints-lean`

`ratpoints-lean` has the command line of ratpoints: the coefficient list `'a_0 a_1 ... a_n'` of
`y ^ 2 = a_n x ^ n + ⋯ + a_0` as one argument (constant term first), the height bound and the
options. It reads them as `main.c` of ratpoints does, with its checks, messages and exit statuses,
in its order, and prints what ratpoints prints: unless `-q` is given, the report, with the banner of
`ratpoints-lean`, the curve and the height bound before the points, and after them what the search
did and the count of the points found, but for message 4 on the moduli used (stage I), message 8 on
the search intervals (stage H) and, under `-v`, the report of the library; under `-x`, the pairs
that pass the sieve of the model, with the moduli of `Ratpoints.sieveParams` and over all numerators
from `-H` to `H`, which are those that ratpoints prints when the moduli are pinned and the Sturm
step is off (`-p 30 -N 30 -s`); and the points, through the callback `process` of `main.c`
(`Ratpoints.Cli.process`), which the search calls for each point it finds
(`Ratpoints.findPointsWith`), in the format of `-f` with the strings of `-fs`, `-fm` and `-fe`, the
points at infinity passed over under `-i` (neither printed nor counted), none printed under `-z`,
and the search stopped under `-1` at the first point that `process` does not pass over (the first
point counted, printed or not). It reads `-p -n -N -P -F -j -J` into the sieving parameters and
ignores the other options that tune the sieve of ratpoints (until stage I, but for `-t` for good);
it reads `-k -K -s -S` and `-x -X -y -Y` into the options of the search (`Ratpoints.Options`):
whether the polynomial may be reversed, the depth of the Sturm step, whether the points are checked
exactly and whether both points of a pair are delivered. It answers the options of the search region
and the range of the denominators, `-l -u -dl -du`, which it does not support yet, with a message
and the exit status 12, which `main.c` does not use. It runs the search with the parameters
`Ratpoints.sieveParams` of these options and these options of the search, so that it refuses a
binary form that is not squarefree with error 8 and, after a reversal, prints the points of the
reversed polynomial mapped back to the caller's curve, as ratpoints does with the same options.

## Main definitions

* `Ratpoints.Cli.input`: the coefficients, the height bound and the options of a command line.
* `Ratpoints.Cli.process`: the callback of the search, which prints the points.
* `Ratpoints.Cli.run`: what the program prints and its exit status, on a command line.
* `Ratpoints.Cli.main`: the program.

## Implementation notes

The numbers are read as `main.c` reads them, by readers of their own: core's `String.toInt?` takes
neither a leading `+` nor white space around the number, and core's `String.toNat?` takes the digit
separator `_`, which `main.c` refuses. The text that `main.c` prints as it goes is collected and
written once at the end.
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

/-- Whether `s` is a floating constant as `strtod` reads it, without its sign and, for a
hexadecimal one, without its prefix `0x`, and nothing else: the mantissa, a maximal run of digits
(those that satisfy `isDigit`) and points with at most one point and at least one digit, and then
optionally the exponent, a character of `exp`, an optional sign and at least one decimal digit. -/
def isFloatBody (isDigit : Char → Bool) (exp : List Char) (s : List Char) : Bool :=
  let (m, e) := s.span fun ch ↦ isDigit ch || ch == '.'
  m.count '.' ≤ 1 && m.any isDigit && match e with
    | [] => true
    | x :: t => exp.contains x && isDigits (dropSign t)

/-- Whether the word `w` is a number for `strtod` in the C locale, other than a NaN: an optional
sign, then `inf` or `infinity` in any case, or a decimal floating constant with the exponent `e`
or `E` (`Ratpoints.Cli.isFloatBody`), or `0x` or `0X` and a hexadecimal one with the exponent `p`
or `P`. -/
def isDoubleWord (w : List Char) : Bool :=
  let v := dropSign w
  ["inf".toList, "infinity".toList].contains (v.map Char.toLower) ||
    match v with
    | '0' :: x :: t =>
      if x.toLower == 'x' then isFloatBody Char.isHexDigit ['p', 'P'] t
      else isFloatBody Char.isDigit ['e', 'E'] v
    | _ => isFloatBody Char.isDigit ['e', 'E'] v

/-- Whether `s` is a real number as `scan_double` of `main.c` reads it with `strtod`: a word of
`Ratpoints.Cli.isDoubleWord`, with nothing but C white space before and after it
(`Ratpoints.Cli.onlyWord?`). A number beyond the range of the doubles is accepted, as an infinity
or as zero, and a NaN is refused.

C: `main.c:746-752`

Deviation: only whether `s` is a number, not the double it denotes, which the options that take a
real number do not need, since they are ignored. -/
def isDouble (s : String) : Bool := (onlyWord? s).any isDoubleWord

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

/-- The usage of `ratpoints-lean`: that of ratpoints, all options included, also those that
`ratpoints-lean` does not support yet.

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
for a binary form that the library refuses as not squarefree, and one of its own, for an option of
ratpoints that `ratpoints-lean` does not support yet. -/
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
  among the options, or an option whose argument is missing or malformed. -/
  | optionSyntax
  /-- Error 8 of `main.c`: a binary form that is not squarefree
  (`Ratpoints.Refusal.notSquarefree`). -/
  | notSquarefree
  /-- Error 11 of `main.c`: a coefficient that is not an integer. -/
  | incorrectCoefficients
  /-- The option `opt`, which ratpoints has and `ratpoints-lean` does not support yet. -/
  | unsupportedOption (opt : String)

/-- What `ratpoints-lean` prints on a failure: what the function `error` of `main.c` prints
for the same error, a blank line, the message and a blank line; for error 2 the banner and the
usage instead, which error 6 prints after its message, as its case falls through to that of
error 2.

C: `main.c:1036-1043`, `main.c:1047`, `main.c:1050-1053`

Deviation: the banner and the usage are those of `ratpoints-lean`, and the message on an option
that `ratpoints-lean` does not support yet is new. -/
def Failure.message : Failure → String
  | .tooFewArguments => s!"\n{banner}\n{usage}"
  | .tooManyCoefficients => "\nToo many coefficients.\n\n"
  | .incorrectHeight => "\nIncorrect height argument.\n\n"
  | .tooFewCoefficients => "\nThe polynomial must have degree at least 1.\n\n"
  | .optionSyntax => s!"\nWrong syntax for optional arguments:\n\n\n{banner}\n{usage}"
  | .notSquarefree => "\nPolynomial is not square-free.\n\n"
  | .incorrectCoefficients => "\nIncorrect coefficients (not integers separated by blanks).\n\n"
  | .unsupportedOption opt => s!"\nOption {opt} is not supported by ratpoints-lean yet.\n\n"

/-- The exit status of `ratpoints-lean` on a failure: the number of the error of `main.c`,
with which its function `error` exits, and 12, which `main.c` does not use, for an option that
`ratpoints-lean` does not support yet.

C: `main.c:1054-1056` -/
def Failure.status : Failure → UInt32
  | .tooFewArguments => 2
  | .tooManyCoefficients => 3
  | .incorrectHeight => 4
  | .tooFewCoefficients => 5
  | .optionSyntax => 6
  | .notSquarefree => 8
  | .incorrectCoefficients => 11
  | .unsupportedOption _ => 12

/-- The failure of `ratpoints-lean` for a refusal of `Ratpoints.findPoints`: the error of `main.c`
with the number that `Ratpoints.Refusal` names, as `main.c` turns the code
`RATPOINTS_NON_SQUAREFREE` that the library returns into error 8. The reading of the command line
(`Ratpoints.Cli.input`) refuses the inputs of the other refusals first, so that of the refusals of
`Ratpoints.findPoints`, which `Ratpoints.Cli.run` maps by it, only
`Ratpoints.Refusal.notSquarefree` can reach it.

C: `main.c:256-261`

Deviation: no error 10, since the model has no failure for lack of memory, and no error 9, which
the program meets only for codes that the library returns on inputs that the program never passes;
no `mpz_clear`. -/
def Failure.ofRefusal : Refusal → Failure
  | .tooManyCoefficients => .tooManyCoefficients
  | .tooFewCoefficients => .tooFewCoefficients
  | .incorrectHeight => .incorrectHeight
  | .notSquarefree => .notSquarefree

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
  /-- A C `double`, as `Ratpoints.Cli.isDouble` reads it. -/
  | double
  /-- An optional C `long`: the next word, if there is one and it does not start with `-`, which is
  then a C `long` as `Ratpoints.Cli.longOfString?` reads it. -/
  | optionalLong
  /-- A string: the next word, whatever it is, also one that starts with `-`. -/
  | word

/-- Whether `a` is an argument of the kind `arg`. -/
def OptionArg.accepts (arg : OptionArg) (a : String) : Bool :=
  match arg with
  | .long | .optionalLong => (longOfString? a).isSome
  | .double => isDouble a
  | .word => true

/-- The kind of argument that the option `o` takes, or `none` if it takes none, for an option that
`ratpoints-lean` reads. `main.c` tells an option by the character after its `-`, and for `-f` and
`-d` by the one after that, ignoring the rest of the word, so that `-quiet` is `-q` and `-fsx` is
`-fs`. The tuning options `-p -F -t -n -N -R -A -P` take a C `long`, `-r -U -C -Q -W` a C `double`,
`-S` an optional C `long`, the options of the output `-f -fs -fm -fe` a string, and
`-q -v -j -J -k -K -s`, the switches of the check and of the pairs `-x -X -y -Y`, and those of the
output `-z -Z -1 -i -I`, nothing. An option of ratpoints that `ratpoints-lean` does not support yet
fails with the exit status 12: those of the search region and the range of the denominators,
`-l -u -dl -du`. Every other word, among them a word without a leading `-` and a word `-f…` with a
third character other than `s`, `m` and `e`, fails with error 6. -/
def optionArg (o : String) : Except Failure (Option OptionArg) :=
  match o.toList with
  | '-' :: ch :: rest =>
    if "pFtnNRAP".contains ch then return some .long
    else if "rUCQW".contains ch then return some .double
    else if ch == 'S' then return some .optionalLong
    else if ch == 'f' && rest.head?.all ("sme".contains ·) then return some .word
    else if "qvjJkKsxXyYzZ1iI".contains ch then return none
    else if "lu".contains ch || ch == 'd' && rest.head?.any ("lu".contains ·) then
      throw (.unsupportedOption o)
    else throw .optionSyntax
  | _ => throw .optionSyntax

/-- The settings of the output of `ratpoints-lean`, the global variables of `main.c`, with their
defaults, those of a command line without options: whether the report is left out (`-q`), whether
it is the report of `-v` (the bit `RATPOINTS_VERBOSE` of the flags), whether the search stops at
the first point counted (`-1`), whether the points at infinity are kept (`-I`, and not `-i`),
whether no point is printed (`-z`, and not `-Z`), the format of a point (`-f`), none for the default
(`Ratpoints.Cli.defaultFormat`), and the strings before, between and after the points (`-fs`,
`-fm`, `-fe`), none for none.

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

/-- The values of the options of the command line, those that set the sieving parameters, the
options of the search (`Ratpoints.Options`) and the settings of the output
(`Ratpoints.Cli.Output`), starting from `s`, or the first failure among the options, the words that
follow the coefficients and the height bound on the command line, read from left to right as
`main.c` reads them: an option that fails by `Ratpoints.Cli.optionArg`, or one whose argument is
missing or malformed (error 6), fails; `-p`, `-n`, `-N`, `-P` and `-F` set the fields of
`Ratpoints.SieveOptions` to the C `long` that follows them, the last one winning, and `-j` switches
the Jacobi test off and `-J` on again, as `main.c` sets the fields and the flags of its
`ratpoints_args`; `-k` forbids the reversal of the polynomial and `-K` allows it again, `-s` sets
the depth of the Sturm step to `-1`, which switches the step off, and `-S` to the C `long` that the
next word gives if there is one and it does not start with `-`, and else to
`Ratpoints.defaultSturm`, so that the step is on unless that depth is negative; `-x` switches the
exact check off and `-X` on again, `-y` makes the search deliver one point of each pair and `-Y`
both; `-f`, `-fs`, `-fm` and `-fe` take the next word, whatever it is, as the format or the string,
and `-q -v -z -Z -1 -i -I` set the settings of the output (`Ratpoints.Cli.Output.store`); of each
setting the last one wins. It ignores the other tuning options, which tune only the heuristics of
the C program (until stage I) and its threads.

C: `main.c:393-397`, `main.c:437-532`, `main.c:533-577`, `main.c:578-593`, `main.c:594-601`,
`main.c:602-637`, `main.c:638-649`, `main.c:667-668`

Deviation: the arguments of the tuning options other than `-p -n -N -P -F` are checked and then
ignored: those of `-r -R -U -C -A -Q -W` until stage I, which models the choice of the moduli by the
curve and its correction, and that of `-t`, the number of threads, for good; the strings of `-f`,
`-fs`, `-fm` and `-fe` kept as values, for the copies that `main.c` allocates, with error 10 when
the allocation fails, which the model cannot meet. An option of ratpoints that `ratpoints-lean` does
not support yet, whose cases are lines 398-436 and 650-666 of `main.c`, ends the reading with the
exit status 12; of these lines, only the error 6 on a word `-d…` that names no option (line 664) is
kept. -/
def checkOptions (s : SieveOptions × Options × Output) :
    List String → Except Failure (SieveOptions × Options × Output)
  | [] => return s
  | o :: os =>
    match optionArg o with
    | .error f => throw f
    | .ok none => checkOptions (store s o none) os
    | .ok (some arg) =>
      if arg matches .optionalLong && os.head?.all (·.startsWith "-") then
        checkOptions (store s o none) os
      else
        match os with
        | a :: os =>
          if arg.accepts a then checkOptions (store s o (some a)) os
          else throw .optionSyntax
        | [] => throw .optionSyntax
where
  /-- `s` with the field that the option `o` sets, with its argument `a` if it takes one: the C
  `long` of `a` for `-p -n -N -P -F`; the Jacobi test off for `-j` and on for `-J`; the reversal
  forbidden for `-k` and allowed for `-K`; the depth `-1` of the Sturm step for `-s`, and for `-S`
  the C `long` of `a`, or `Ratpoints.defaultSturm` if there is none; the exact check off for `-x`
  and on for `-X`; one point of each pair for `-y` and both for `-Y`; and the settings of the
  output by `Ratpoints.Cli.Output.store`. -/
  store (s : SieveOptions × Options × Output) (o : String) (a : Option String) :
      SieveOptions × Options × Output :=
    let (s, t, u) := s
    let u := u.store o a
    match o.toList, a.bind longOfString? with
    | '-' :: 'p' :: _, some v => ({ s with numPrimes := v }, t, u)
    | '-' :: 'n' :: _, some v => ({ s with sp1 := v }, t, u)
    | '-' :: 'N' :: _, some v => ({ s with sp2 := v }, t, u)
    | '-' :: 'P' :: _, some v => ({ s with sp3Extra := v }, t, u)
    | '-' :: 'F' :: _, some v => ({ s with maxForbidden := v }, t, u)
    | '-' :: 'j' :: _, _ => ({ s with jacobi := false }, t, u)
    | '-' :: 'J' :: _, _ => ({ s with jacobi := true }, t, u)
    | '-' :: 'k' :: _, _ => (s, { t with reverse := false }, u)
    | '-' :: 'K' :: _, _ => (s, { t with reverse := true }, u)
    | '-' :: 's' :: _, _ => (s, { t with sturm := -1 }, u)
    | '-' :: 'S' :: _, v => (s, { t with sturm := v.getD defaultSturm }, u)
    | '-' :: 'x' :: _, _ => (s, { t with noCheck := true }, u)
    | '-' :: 'X' :: _, _ => (s, { t with noCheck := false }, u)
    | '-' :: 'y' :: _, _ => (s, { t with noY := true }, u)
    | '-' :: 'Y' :: _, _ => (s, { t with noY := false }, u)
    | _, _ => (s, t, u)

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
the defaults of `Ratpoints.SieveOptions`, `Ratpoints.Options` and `Ratpoints.Cli.Output`, the values
of a command line without options; then the format is the default (`Ratpoints.Cli.defaultFormat`)
unless an option `-f` gave one, and `-q` cancels `-v`.

C: `main.c:210-214`, `main.c:315-316`, `main.c:688`, `main.c:691-692`

Deviation: `read_input` never returns a value other than 0, so the usage that `main.c` prints
then (lines 212 and 213) has no counterpart. -/
def input : List String → Except Failure (List Int × Nat × SieveOptions × Options × Output)
  | s :: h :: os => do
    let c ← coefficients s
    let H ← heightBound h
    let (s, o, u) ← checkOptions ({}, {}, {}) os
    let u := { u with
      printFormat := u.printFormat.getD (defaultFormat o)
      verbose := u.verbose && !u.quiet }
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
(`no_y`), and the text printed so far.

C: `main.c:110-113`

Deviation: no intervals of the search region (`num_inter`, `ends`; stage H); the text printed so
far, for the standard output, to which `process` prints. -/
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
  /-- The text printed so far. -/
  out : String

/-- The data that `main.c` passes to `process` for the settings of the output `u` and the options
`o` of the search: no point printed yet, the settings of `u`, and `%y` printing itself when the
points are not checked exactly or only one point of each pair is delivered.

C: `main.c:235-242`

Deviation: no intervals of the search region (lines 246-247; stage H); the format the one that
`Ratpoints.Cli.input` settled, `""` if none. -/
def Data.ofOutput (u : Output) (o : Options) : Data where
  printBetween := false
  noOutput := u.noOutput
  pf := u.printFormat.getD ""
  onePoint := u.onePoint
  pointsAtInfty := u.pointsAtInfty
  stringBefore := u.stringBefore
  stringBetween := u.stringBetween
  noY := o.noCheck || o.noY
  out := ""

/-- The callback `process` of `main.c` on the point `(x : y : z)` with the data `info`: a point at
infinity (`z = 0`) is passed over when the points at infinity are not kept (`-i`), with the weight
`0`, and leaves the flag clear; every other point stops the search when one point is enough, and has
the weight `1`; it is printed unless no point is printed: after the string before the points if it
is the first point printed, and else after the string between them, in the format
(`Ratpoints.Cli.formatPoint`).

C: `main.c:139-142`, `main.c:153-156`, `main.c:187-189`

Deviation: the test of the search region (lines 150-152) is stage H; the data a value, for the
pointer `info`, and returned with the weight and the flag, for the `int *quit` that the library
passes, which is clear at every call; the text appended to that of the data, for the standard
output, and no `fflush`. -/
def process (x z y : Int) (info : Data) : Answer Data :=
  if z == 0 && !info.pointsAtInfty then ⟨0, false, info⟩
  -- stage H: the test of the search region (`main.c:150-152`) comes here
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
not checked exactly or only one point of each pair is delivered; message 5, the curve; message 6,
the height bound; and message 7, what the search did: whether the polynomial was reversed, whether
the denominators could be restricted to squares (`RATPOINTS_USE_SQUARES`) or essentially to squares
(`RATPOINTS_USE_SQUARES1`), whether the Jacobi test was off, and whether the points were not checked
exactly. -/
inductive Message where
  /-- Message 0: the banner. -/
  | banner
  /-- Message 2: the count `total`, of the pairs when `pairs` is set. -/
  | count (total : Int) (pairs : Bool)
  /-- Message 5: the curve of the coefficient list `c`. -/
  | curve (c : List Int)
  /-- Message 6: the height bound `H`. -/
  | height (H : Nat)
  /-- Message 7: the flags of the search. -/
  | flags (reversed useSquares useSquares1 noJacobi noCheck : Bool)

/-- The text of a message of the report, as `message` of `main.c` prints it.

C: `main.c:972-976`, `main.c:979-983`, `main.c:999-1021`, `main.c:1031-1033`

Deviation: the banner of `ratpoints-lean` (`Ratpoints.Cli.banner`); a constructor for each message
that `ratpoints-lean` prints, with its data, for the number `n` and the arguments of the library:
message 1, which the program prints when `read_input` fails, which it never does, is left out,
messages 3 and 8, on the search region and the search intervals, are stage H, and message 4, on the
moduli used, is stage I; no `fflush`. -/
def Message.text : Message → String
  | .banner => s!"\n{Cli.banner}\n"
  | .count total pairs =>
    s!"\n{total} rational point{if pairs then " pair" else ""}s found.\n\n"
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

/-- What `main.c` prints before the search for the settings of the output `u`: nothing when the
report is left out (`-q`); otherwise the banner, the curve of the coefficient list `c` and, unless
the report is that of `-v`, the height bound `H` and a blank line.

C: `main.c:215-220`

Deviation: message 3 on the search region (line 224) is stage H. -/
def preamble (c : List Int) (H : Nat) (u : Output) : String :=
  if u.quiet then ""
  else Message.banner.text ++ (Message.curve c).text ++
    if u.verbose then "" else (Message.height H).text ++ "\n"

/-- What `main.c` prints after the points for the settings of the output `u`: nothing when the
report is left out (`-q`); otherwise, unless the report is that of `-v`, two line feeds and what
the search did (message 7), from the flags that the search `r` writes back, the Jacobi switch of the
options `s` and the switch of the exact check of the options `o`; then the count of the points
found, the count `total` of the search, of the pairs under `-x` or `-y` (message 2).

C: `main.c:268-276`

Deviation: messages 4 (the moduli used; stage I) and 8 (the search intervals; stage H) are left
out. -/
def report {σ : Type} (s : SieveOptions) (o : Options) (u : Output) (r : Outcome σ) : String :=
  let flags := Message.flags r.reversed r.useSquares r.useSquares1 (!s.jacobi) o.noCheck
  if u.quiet then ""
  else (if u.verbose then "" else "\n\n" ++ flags.text) ++
    (Message.count r.total (o.noCheck || o.noY)).text

/-! ### The program -/

/-- What `ratpoints-lean` does on the command line `args` (the words after the name of the
program): the text it prints on the standard output and its exit status. On the coefficient list
`c`, the height bound `H`, the values `s` of the options that set the sieving parameters, the
options `o` of the search and the settings `u` of the output, as `Ratpoints.Cli.input` reads them,
it prints the head of the report (`Ratpoints.Cli.preamble`, nothing under `-q`), and then runs the
search `Ratpoints.findPointsWith` with the parameters `Ratpoints.sieveParams s`, the options `o` and
the callback `Ratpoints.Cli.process` on its data (`Ratpoints.Cli.Data.ofOutput`): on a refusal it
prints the message of the failure (`Ratpoints.Cli.Failure.ofRefusal`) and exits with its status;
otherwise it prints what the callback printed, the string before the points if it printed no point,
the string after the points and the end of the report (`Ratpoints.Cli.report`, nothing under `-q`),
and exits with status 0; on a failure `f` of the command line it prints `f.message` and exits with
`f.status` (`Ratpoints.Cli.Failure.message`, `Ratpoints.Cli.Failure.status`).

C: `main.c:195-198`, `main.c:251-252`, `main.c:265`, `main.c:267`, `main.c:284-285`

Deviation: the text written once at the end (`Ratpoints.Cli.main`), where `main.c` prints as it
goes; the intervals with `join_intervals` (line 248) are stage H. -/
def run (args : List String) : String × UInt32 :=
  match input args with
  | .error f => (f.message, f.status)
  | .ok (c, H, s, o, u) =>
    let pre := preamble c H u
    match findPointsWith c H (sieveParams s) o process (.ofOutput u o) with
    | .error e => let f := Failure.ofRefusal e; (pre ++ f.message, f.status)
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

Each of them is what ratpoints 3.1.1 does, but for the banner and, in the report, messages 4 and 8,
which `ratpoints-lean` leaves out, and for the exit status 12 on `-lfoo` (that is, `-l`), an option
that ratpoints has and `ratpoints-lean` does not support yet. -/

#guard words " 1\t-2\x0b+3\r".toList == ["1".toList, "-2".toList, "+3".toList]

#guard longOfString? " +7\r" == some 7 && longOfString? "-0" == some 0

#guard longOfString? "9223372036854775807" == some (2 ^ 63 - 1) &&
  longOfString? "-9223372036854775808" == some (-2 ^ 63)

#guard longOfString? "9223372036854775808" == none && longOfString? "1_000" == none

#guard [" 1.5e3 ", "-0x1.8p3", ".5", "1.", "INFINITY", "-inf", "1e400"].all isDouble

#guard !(["nan", "1e", "0x", ".", "1e+", "0x1p", "1,5", "1 2", "infinit", ""].any isDouble)

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

#guard run ["1 0 1", "5", "-quiet", "-p", " 30 ", "-lfoo"] ==
  ("\nOption -lfoo is not supported by ratpoints-lean yet.\n\n", 12)

#guard (run ["1 0 1", "5", "-q", "-r", "nan"]).2 == 6 && (run ["1 0 1", "5", "-d", "1"]).2 == 6

-- `-p 10 -n 4 -N 7 -P 3 -j -F 200 -t 2 -p 12`: the last `-p` wins, and `-t` is ignored.
#guard (checkOptions ({}, {}, {}) ["-p", "10", "-n", "4", "-N", "7", "-P", "3", "-j", "-F", "200",
    "-t", "2", "-p", "12"]).toOption.map (fun (o, _) ↦ (o.numPrimes, o.sp1, o.sp2, o.sp3Extra,
    o.maxForbidden, o.jacobi)) == some (12, 4, 7, 3, 200, false)

-- `-j` and `-J`: the last one wins.
#guard [(["-j", "-J"], true), (["-J", "-j"], false)].all fun (os, b) ↦
  (checkOptions ({}, {}, {}) os).toOption.map (·.1.jacobi) == some b

-- `-k` and `-K`, `-s` and `-S`: the last of each pair wins, and `-S` takes the next word as its
-- depth unless it starts with `-`.
#guard [(["-k", "-S", "5", "-K", "-s"], true, -1), (["-s", "-S"], true, defaultSturm),
    (["-k", "-S", "-q"], false, defaultSturm), (["-s", "-S", " 0 "], true, 0)].all
  fun (os, rev, st) ↦ (checkOptions ({}, {}, {}) os).toOption.map
    (fun (_, o, _) ↦ (o.reverse, o.sturm)) == some (rev, st)

-- `-x -X -y -Y -z -Z -i -I`: the last of each pair wins; `-1` has no counterpart; `-xfoo` is `-x`.
#guard (checkOptions ({}, {}, {}) ["-xfoo", "-Y", "-y", "-z", "-Zap", "-I", "-i", "-1x"]
    ).toOption.map (fun (_, o, u) ↦ (o.noCheck, o.noY, u.noOutput, u.pointsAtInfty, u.onePoint)) ==
  some (true, true, false, false, true)

-- `-f`, `-fs`, `-fm` and `-fe` take the next word, whatever it is, the last one winning; `-fsfoo`
-- is `-fs`; `-f` without its argument and `-ffoo` are error 6.
#guard (checkOptions ({}, {}, {}) ["-f", "-x", "-fsfoo", "S", "-fm", "", "-fe", "-y", "-f", "%x"]
    ).toOption.map (fun (_, o, u) ↦ (o.noCheck, o.noY, u.printFormat, u.stringBefore,
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
-- default format `(%x : %z)\n` under `-x` with the moduli pinned (`-p 30 -N 30`); and `-X`, `-Y`
-- and `-I` as the last of their pairs.
#guard run ["1 0 126 0 441", "200", "-q", "-fs", "S", "-fm", "M", "-fe", "E", "-y"] ==
  ("S(1 : 0)\nM(0 : 1)\nM(-1 : 2)\nM(1 : 2)\nM(-2 : 21)\nM(2 : 21)\nE", 0)
#guard run ["1 0 1", "5", "-q", "-x", "-p", "30", "-N", "30"] ==
  ("(1 : 0)\n(0 : 1)\n(-4 : 3)\n(4 : 3)\n(-3 : 4)\n(3 : 4)\n", 0)
#guard [["-x", "-X"], ["-y", "-Y"], ["-i", "-I"]].all fun os ↦
  run (["1 0 126 0 441", "30", "-q"] ++ os) == run ["1 0 126 0 441", "30", "-q"]
#guard (run ["1 0 126 0 441", "30", "-q"]).1.startsWith "(1 : 21 : 0)\n(1 : -21 : 0)\n(0 : 1 : 1)\n"

-- The report of `ratpoints '1 0 126 0 441' 30 -z` and of `ratpoints '1 0 126 0 441' 30 -v -1 -y`,
-- without messages 4 and 8 and without the report of the library under `-v`.
#guard run ["1 0 126 0 441", "30", "-z"] ==
  (s!"\n{banner}\n\nCurve equation is  y^2 = 441 x^4 + 126 x^2 + 1\n\nmax. Height = 30\n\n" ++
    "\n\n\n12 rational points found.\n\n", 0)
#guard run ["1 0 126 0 441", "30", "-v", "-1", "-y"] ==
  (s!"\n{banner}\n\nCurve equation is  y^2 = 441 x^4 + 126 x^2 + 1\n\n" ++
    "(1 : 0)\n\n1 rational point pairs found.\n\n", 0)

-- The curves of `ratpoints c 20 | grep 'Curve equation'`.
#guard [("-1 1 -1 1", "x^3 - x^2 + x - 1"), ("0 -2 0 1", "x^3 - 2 x"),
    ("1 0 0 0 0 -1", "- x^5 + 1"), ("-12 0 0 7", "7 x^3 - 12"), ("1 -1", "- x + 1"),
    ("0 1", "x")].all fun (c, s) ↦ printPoly ((coefficients c).toOption.getD []) == s ++ "\n"

-- Message 7: the reversal, the squares, the Jacobi test and the exact check of
-- `ratpoints '0 1 2' 40 -j -x -z -n 15 -N 30 -p 30`, and the divisors of the leading coefficient of
-- `ratpoints '1 0 0 6' 200 -y -z`.
#guard (((run ["0 1 2", "40", "-j", "-x", "-z", "-n", "15", "-N", "30", "-p", "30"]).1.splitOn
    "\n").filter (· ≠ "")).drop 7 ==
  ["Polynomial was reversed for better performance.",
    "(Reversed) polynomial is +-monic of odd degree:", "  could restrict denominators to squares.",
    "Jacobi symbol test was not used.", "Points were not checked exactly:",
    "   some of the printed x-coordinates may not give points.", "26 rational point pairs found."]
#guard (((run ["1 0 0 6", "200", "-y", "-z"]).1.splitOn "\n").filter (· ≠ "")).drop 7 ==
  ["(Reversed) polynomial has odd degree:", "  could restrict denominators essentially to squares.",
    "8 rational point pairs found."]

end Cli

end Ratpoints

end

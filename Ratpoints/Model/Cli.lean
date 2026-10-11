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
in its order, and prints the points as ratpoints does with `-q`: one line `(x : y : z)` per point
and nothing else. It accepts `-q` and `-v`, which it ignores, and the options that tune the sieve
of ratpoints: it reads `-p -n -N -P -F -j -J` into the sieving parameters and ignores the others.
It reads `-k -K -s -S` into the options of the search (`Ratpoints.Options`): whether the polynomial
may be reversed, and the depth of the Sturm step. It answers every other option of ratpoints, which
it does not support yet, with a message and the exit status 12, which `main.c` does not use. It
takes the points from the sieve `Ratpoints.findPoints` with the parameters `Ratpoints.sieveParams`
of these options and these options of the search, so that it refuses a binary form that is not
squarefree with error 8 and, after a reversal, prints the points of the reversed polynomial mapped
back to the caller's curve, as ratpoints does with the same options.

## Main definitions

* `Ratpoints.Cli.run`: what the program prints and its exit status, on a command line.
* `Ratpoints.Cli.main`: the program.

## Implementation notes

The numbers are read as `main.c` reads them, by readers of their own: core's `String.toInt?`
takes neither a leading `+` nor white space around the number, and core's `String.toNat?` takes
the digit separator `_`, which `main.c` refuses.
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

C: `main.c:318`, `main.c:362-375`

Deviation: a list of `Int`s for the array of `RATPOINTS_MAX_DEGREE + 1` GMP integers; the
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

/-- Whether `a` is an argument of the kind `arg`. -/
def OptionArg.accepts (arg : OptionArg) (a : String) : Bool :=
  match arg with
  | .long | .optionalLong => (longOfString? a).isSome
  | .double => isDouble a

/-- The kind of argument that the option `o` takes, or `none` if it takes none, for an option that
`ratpoints-lean` reads. `main.c` tells an option by the character after its `-`, and for `-f` and
`-d` by the one after that, ignoring the rest of the word, so that `-quiet` is `-q`. The tuning
options `-p -F -t -n -N -R -A -P` take a C `long`, `-r -U -C -Q -W` a C `double`, `-S` an optional
C `long`, and `-j -J -k -K -s`, like `-q` and `-v`, nothing. An option of ratpoints that
`ratpoints-lean` does not support yet fails with the exit status 12: those of the search region
and the range of the denominators, `-l -u -dl -du`, and those of the output, `-x -X -y -Y -z -Z`,
`-1 -i -I` and `-f -fs -fm -fe`. Every other word, among them a word without a leading `-`, fails
with error 6. -/
def optionArg (o : String) : Except Failure (Option OptionArg) :=
  match o.toList with
  | '-' :: ch :: rest =>
    if "pFtnNRAP".contains ch then return some .long
    else if "rUCQW".contains ch then return some .double
    else if ch == 'S' then return some .optionalLong
    else if "qvjJkKs".contains ch then return none
    else if "luxXyYzZ1iI".contains ch || ch == 'f' && rest.head?.all ("sme".contains ·) ||
        ch == 'd' && rest.head?.any ("lu".contains ·) then
      throw (.unsupportedOption o)
    else throw .optionSyntax
  | _ => throw .optionSyntax

/-- The values of the options of the command line, those that set the sieving parameters and the
options of the search (`Ratpoints.Options`), starting from `s`, or the first failure among the
options, the words that follow the coefficients and the height bound on the command line, read from
left to right as `main.c` reads them: an option that fails by `Ratpoints.Cli.optionArg`, or one
whose argument is missing or malformed (error 6), fails; `-p`, `-n`, `-N`, `-P` and `-F` set the
fields of `Ratpoints.SieveOptions` to the C `long` that follows them, the last one winning, and `-j`
switches the Jacobi test off and `-J` on again, as `main.c` sets the fields and the flags of its
`ratpoints_args`; `-k` forbids the reversal of the polynomial and `-K` allows it again, and `-s`
sets the depth of the Sturm step to `-1`, which switches the step off, and `-S` to the C `long` that
the next word gives if there is one and it does not start with `-`, and else to
`Ratpoints.defaultSturm`, so that the step is on unless that depth is negative; the last of `-k` and
`-K` and the last of `-s` and `-S` winning. Since `ratpoints-lean` always runs as ratpoints does
with `-q`, it ignores `-q` and `-v`, which `-q` cancels in `main.c`; and it ignores the other tuning
options, which tune only the heuristics of the C program and its threads.

C: `main.c:393-397`, `main.c:437-532`, `main.c:578-593`, `main.c:594-601`, `main.c:638-649`,
`main.c:667-668`

Deviation: the arguments of the tuning options other than `-p -n -N -P -F` are checked and then
ignored. An option of ratpoints that `ratpoints-lean` does not support yet, whose cases are lines
398-436, 533-577, 602-637 and 650-666 of `main.c`, ends the reading with the exit status 12; of
these lines, only the error 6 on a word `-f…` or `-d…` that names no option (lines 575 and 664) is
kept. -/
def checkOptions (s : SieveOptions × Options) :
    List String → Except Failure (SieveOptions × Options)
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
          if arg.accepts a then checkOptions (store s o (longOfString? a)) os
          else throw .optionSyntax
        | [] => throw .optionSyntax
where
  /-- `s` with the field that the option `o` sets: the value `v`, if there is one, for
  `-p -n -N -P -F`; the Jacobi test off for `-j` and on for `-J`, whatever `v` is; the reversal
  forbidden for `-k` and allowed for `-K`; the depth `-1` of the Sturm step for `-s`, and for `-S`
  the value `v`, or `Ratpoints.defaultSturm` if there is none; and `s` itself for every other
  option. -/
  store (s : SieveOptions × Options) (o : String) (v : Option Int) : SieveOptions × Options :=
    let (s, t) := s
    match o.toList, v with
    | '-' :: 'p' :: _, some v => ({ s with numPrimes := v }, t)
    | '-' :: 'n' :: _, some v => ({ s with sp1 := v }, t)
    | '-' :: 'N' :: _, some v => ({ s with sp2 := v }, t)
    | '-' :: 'P' :: _, some v => ({ s with sp3Extra := v }, t)
    | '-' :: 'F' :: _, some v => ({ s with maxForbidden := v }, t)
    | '-' :: 'j' :: _, _ => ({ s with jacobi := false }, t)
    | '-' :: 'J' :: _, _ => ({ s with jacobi := true }, t)
    | '-' :: 'k' :: _, _ => (s, { t with reverse := false })
    | '-' :: 'K' :: _, _ => (s, { t with reverse := true })
    | '-' :: 's' :: _, _ => (s, { t with sturm := -1 })
    | '-' :: 'S' :: _, v => (s, { t with sturm := v.getD defaultSturm })
    | _, _ => (s, t)

/-- What a command line (the words after the name of the program) gives: the coefficient list, the
height bound and the values of the options, those that set the sieving parameters and the options of
the search, or the first failure, in the order of `main.c`: fewer than two words fail with error 2;
then come the coefficients (`Ratpoints.Cli.coefficients`), the height bound
(`Ratpoints.Cli.heightBound`) and the options (`Ratpoints.Cli.checkOptions`), read from the defaults
of `Ratpoints.SieveOptions` and `Ratpoints.Options`, the values of a command line without options.

C: `main.c:210-214`

Deviation: `read_input` never returns a value other than 0, so the usage that `main.c` prints
then (lines 212 and 213) has no counterpart. -/
def input : List String → Except Failure (List Int × Nat × SieveOptions × Options)
  | s :: h :: os => do
    let c ← coefficients s
    let H ← heightBound h
    let o ← checkOptions ({}, {}) os
    return (c, H, o)
  | _ => throw .tooFewArguments

/-! ### The program -/

/-- The line that `main.c` prints for the point `(x, y, z)` in its default format
`(%x : %y : %z)\n`: `(x : y : z)` and a line feed.

C: `main.c:681-685`

Deviation: the format is always this one, since `ratpoints-lean` does not support `-f`, `-x` and
`-y` yet, and the line is written directly rather than by the interpreter of formats in
`process`. -/
def pointLine (p : Int × Int × Int) : String := s!"({p.1} : {p.2.1} : {p.2.2})\n"

/-- What `ratpoints-lean` does on the command line `args` (the words after the name of the
program): the text it prints on the standard output and its exit status. On the coefficient list
`c`, the height bound `H`, the values `s` of the options that set the sieving parameters and the
options `o` of the search, as `Ratpoints.Cli.input` reads them, it prints, as ratpoints does with
`-q`, the line `Ratpoints.Cli.pointLine` of each point that the sieve `Ratpoints.findPoints` finds
with the parameters `Ratpoints.sieveParams s` and the options `o`, in its order, and exits with
status 0; on a failure `f`, among them a refusal of `Ratpoints.findPoints`, it prints `f.message`
and exits with `f.status` (`Ratpoints.Cli.Failure.message`, `Ratpoints.Cli.Failure.status`).

C: `main.c:251`, `main.c:284`

Deviation: the callback `process` and its data `info` give way to the list that
`Ratpoints.findPoints` returns, whose points `Ratpoints.Cli.pointLine` prints once the list is
computed, and there is no count `total`; the output data of `info` and `before_printed` are stage G,
and the intervals with `join_intervals` stage H; the report without `-q` is not printed, since
`ratpoints-lean` runs as with `-q`. -/
def run (args : List String) : String × UInt32 :=
  match input args >>= fun (c, H, s, o) ↦
      (findPoints c H (sieveParams s) o).mapError .ofRefusal with
  | .ok pts => (String.join (pts.map pointLine), 0)
  | .error f => (f.message, f.status)

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

Each of them is what ratpoints 3.1.1 does, but for the exit status 12 on `-xfoo` (that is, `-x`),
an option that ratpoints has and `ratpoints-lean` does not support yet. -/

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
-- check refuses, and `1 2 1`, which the remainder chain refuses.
#guard (Failure.ofRefusal .notSquarefree).message == "\nPolynomial is not square-free.\n\n" &&
  (Failure.ofRefusal .notSquarefree).status == 8
#guard ["0 0 1", "1 2 1"].all fun c ↦
  run [c, "5", "-q"] == ("\nPolynomial is not square-free.\n\n", 8)

#guard run ["1 0 1", "5", "-quiet", "-p", " 30 ", "-xfoo"] ==
  ("\nOption -xfoo is not supported by ratpoints-lean yet.\n\n", 12)

#guard (run ["1 0 1", "5", "-q", "-r", "nan"]).2 == 6 && (run ["1 0 1", "5", "-d", "1"]).2 == 6

-- `-p 10 -n 4 -N 7 -P 3 -j -F 200 -t 2 -p 12`: the last `-p` wins, and `-t` is ignored.
#guard (checkOptions ({}, {}) ["-p", "10", "-n", "4", "-N", "7", "-P", "3", "-j", "-F", "200",
    "-t", "2", "-p", "12"]).toOption.map (fun (o, _) ↦ (o.numPrimes, o.sp1, o.sp2, o.sp3Extra,
    o.maxForbidden, o.jacobi)) == some (12, 4, 7, 3, 200, false)

-- `-j` and `-J`: the last one wins.
#guard [(["-j", "-J"], true), (["-J", "-j"], false)].all fun (os, b) ↦
  (checkOptions ({}, {}) os).toOption.map (·.1.jacobi) == some b

-- `-k` and `-K`, `-s` and `-S`: the last of each pair wins, and `-S` takes the next word as its
-- depth unless it starts with `-`.
#guard [(["-k", "-S", "5", "-K", "-s"], true, -1), (["-s", "-S"], true, defaultSturm),
    (["-k", "-S", "-q"], false, defaultSturm), (["-s", "-S", " 0 "], true, 0)].all
  fun (os, rev, st) ↦
    (checkOptions ({}, {}) os).toOption.map (fun (_, o) ↦ (o.reverse, o.sturm)) == some (rev, st)

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

end Cli

end Ratpoints

end

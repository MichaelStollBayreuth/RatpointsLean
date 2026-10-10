/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.BruteForce
public import Ratpoints.Model.Constants

-- The `#guard` examples use the constants at compile time.
meta import Ratpoints.Model.Constants

/-!
# The command-line program `ratpoints-lean`

`ratpoints-lean` has the command line of ratpoints: the coefficient list `'a_0 a_1 ... a_n'` of
`y ^ 2 = a_n x ^ n + ⋯ + a_0` as one argument (constant term first), the height bound and the
options. It reads them as `main.c` of ratpoints does, with its checks, messages and exit statuses,
in its order, and prints the points as ratpoints does with `-q`: one line `(x : y : z)` per point
and nothing else. It accepts `-q` and `-v` and the options that tune the sieve of ratpoints, and
ignores them; it answers every other option of ratpoints, which it does not support yet, with a
message and the exit status 12, which `main.c` does not use. For now it takes the points from the
brute-force reference `Ratpoints.bruteForce`, so that, unlike ratpoints, it does not refuse a
polynomial that is not squarefree.

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

/-- The ways in which `ratpoints-lean` refuses its command line: the errors of `main.c` that it
can meet there, and one of its own, for an option of ratpoints that it does not support yet. -/
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
  /-- Error 11 of `main.c`: a coefficient that is not an integer. -/
  | incorrectCoefficients
  /-- The option `opt`, which ratpoints has and `ratpoints-lean` does not support yet. -/
  | unsupportedOption (opt : String)

/-- What `ratpoints-lean` prints on a failure: what the function `error` of `main.c` prints
for the same error, a blank line, the message and a blank line; for error 2 the banner and the
usage instead, which error 6 prints after its message, as its case falls through to that of
error 2.

C: `main.c:1036-1043`, `main.c:1050-1053`

Deviation: the banner and the usage are those of `ratpoints-lean`, and the message on an option
that `ratpoints-lean` does not support yet is new. -/
def Failure.message : Failure → String
  | .tooFewArguments => s!"\n{banner}\n{usage}"
  | .tooManyCoefficients => "\nToo many coefficients.\n\n"
  | .incorrectHeight => "\nIncorrect height argument.\n\n"
  | .tooFewCoefficients => "\nThe polynomial must have degree at least 1.\n\n"
  | .optionSyntax => s!"\nWrong syntax for optional arguments:\n\n\n{banner}\n{usage}"
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
  | .incorrectCoefficients => 11
  | .unsupportedOption _ => 12

/-! ### The command line -/

/-- The coefficient list that the first argument `s` of the command line gives, constant term
first, as `main.c` reads it: integers as `Ratpoints.Cli.intOfWord?` reads them, separated by C
white space, which may also stand before the first and after the last. A word that is not an
integer fails with error 11, wherever it stands; then more than `Ratpoints.maxDegree + 1`
integers fail with error 3, and fewer than two with error 5.

C: `main.c:362-375`

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

/-- Whether `a` is an argument of the kind `arg`. -/
def OptionArg.accepts (arg : OptionArg) (a : String) : Bool :=
  match arg with
  | .long => (longOfString? a).isSome
  | .double => isDouble a

/-- The kind of argument that the option `o` takes, or `none` if it takes none, for an option that
`ratpoints-lean` reads. `main.c` tells an option by the character after its `-`, and for `-f` and
`-d` by the one after that, ignoring the rest of the word, so that `-quiet` is `-q`. The tuning
options `-p -F -t -n -N -R -A -P` take a C `long`, `-r -U -C -Q -W` a C `double`, and `-j -J`,
like `-q` and `-v`, nothing. An option of ratpoints that `ratpoints-lean` does not support yet,
one of `-l -u -k -K -x -X -y -Y -z -Z -1 -i -I -s -S -f -fs -fm -fe -dl -du`, fails with the
exit status 12, and every other word, among them a word without a leading `-`, with error 6. -/
def optionArg (o : String) : Except Failure (Option OptionArg) :=
  match o.toList with
  | '-' :: ch :: rest =>
    if "pFtnNRAP".contains ch then return some .long
    else if "rUCQW".contains ch then return some .double
    else if "qvjJ".contains ch then return none
    else if "lukKxXyYzZ1iIsS".contains ch || ch == 'f' && rest.head?.all ("sme".contains ·) ||
        ch == 'd' && rest.head?.any ("lu".contains ·) then
      throw (.unsupportedOption o)
    else throw .optionSyntax
  | _ => throw .optionSyntax

/-- The first failure among the options, the words that follow the coefficients and the height
bound on the command line, read from left to right as `main.c` reads them: an option that fails by
`Ratpoints.Cli.optionArg`, or one whose argument is missing or malformed (error 6). Since
`ratpoints-lean` always runs as ratpoints does with `-q`, it ignores `-q` and `-v`, which `-q`
cancels in `main.c`; and it ignores the tuning options, which do not change what ratpoints prints
under `-q`.

C: `main.c:393-397`, `main.c:437-532`, `main.c:578-593`, `main.c:667-668`

Deviation: the arguments of the options are checked and then ignored. An option of ratpoints that
`ratpoints-lean` does not support yet, whose cases are lines 398-436, 533-577 and 594-666 of
`main.c`, ends the reading with the exit status 12; of these lines, only the error 6 on a word
`-f…` or `-d…` that names no option (lines 575 and 664) is kept. -/
def checkOptions : List String → Except Failure Unit
  | [] => return
  | o :: os =>
    match optionArg o with
    | .error f => throw f
    | .ok none => checkOptions os
    | .ok (some arg) =>
      match os with
      | a :: os => if arg.accepts a then checkOptions os else throw .optionSyntax
      | [] => throw .optionSyntax

/-- The coefficient list and the height bound that a command line (the words after the name of
the program) gives, or the first failure, in the order of `main.c`: fewer than two words
fail with error 2; then come the coefficients (`Ratpoints.Cli.coefficients`), the height bound
(`Ratpoints.Cli.heightBound`) and the options (`Ratpoints.Cli.checkOptions`).

C: `main.c:210-214`

Deviation: `read_input` never returns a value other than 0, so the usage that `main.c` prints
then (lines 212 and 213) has no counterpart. -/
def input : List String → Except Failure (List Int × Nat)
  | s :: h :: os => do
    let c ← coefficients s
    let H ← heightBound h
    checkOptions os
    return (c, H)
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
`c` and the height bound `H` of `Ratpoints.Cli.input`, it prints, as ratpoints does with `-q`, the
line `Ratpoints.Cli.pointLine` of each point of `Ratpoints.bruteForce c H`, in the order of that
list, and exits with status 0; on a failure `f`, it prints `f.message` and exits with
`f.status` (`Ratpoints.Cli.Failure.message`, `Ratpoints.Cli.Failure.status`). -/
def run (args : List String) : String × UInt32 :=
  match input args with
  | .ok (c, H) => (String.join ((bruteForce c H).map pointLine), 0)
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

Each of them is what ratpoints 3.1.1 does, but for the exit status 12 on `-kfoo` (that is, `-k`),
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

#guard run ["1 0 1", "5", "-quiet", "-p", " 30 ", "-kfoo"] ==
  ("\nOption -kfoo is not supported by ratpoints-lean yet.\n\n", 12)

#guard (run ["1 0 1", "5", "-q", "-r", "nan"]).2 == 6 && (run ["1 0 1", "5", "-d", "1"]).2 == 6

end Cli

end Ratpoints

end

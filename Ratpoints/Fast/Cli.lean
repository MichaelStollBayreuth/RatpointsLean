/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Fast.Search

/-!
# The command-line program on the fast search

`ratpoints-lean 'a₀ a₁ … aₙ' H [-dl b] [-du b] [-q]` prints the points of height at most `H` on
`y ^ 2 = a₀ zᴰ + a₁ x zᴰ⁻¹ + ⋯ + aₙ xⁿ zᴰ⁻ⁿ` that `Ratpoints.FastMask.fastPoints` lists, one
per line as `(x : y : z)`, the points at infinity included; `-dl` and `-du` bound the denominators
from below and above, and `-q` is accepted and ignored. On an argument that it cannot read it
prints a message on the standard error and exits with status 1.

## Main definitions

* `Ratpoints.FastCli.main`: the program.
-/

@[expose] public section

namespace Ratpoints

namespace FastCli

/-- The arguments of a run: the coefficients, the height bound and the bounds of the
denominators. -/
structure Args where
  /-- The coefficients `a₀, …, aₙ`. -/
  coeffs : List Int
  /-- The height bound. -/
  H : Nat
  /-- The lower bound of the denominators. -/
  bLow : Int := 1
  /-- The upper bound of the denominators; below `1` for none. -/
  bHigh : Int := 0

/-- The options after the height bound, read into `a`. -/
def readOptions (a : Args) : List String → Except String Args
  | [] => .ok a
  | "-q" :: rest => readOptions a rest
  | "-dl" :: v :: rest =>
    match v.toInt? with
    | some b => readOptions { a with bLow := b } rest
    | none => .error s!"-dl needs an integer, not '{v}'"
  | "-du" :: v :: rest =>
    match v.toInt? with
    | some b => readOptions { a with bHigh := b } rest
    | none => .error s!"-du needs an integer, not '{v}'"
  | o :: _ => .error s!"unknown or incomplete option '{o}'"

/-- The arguments of the command line. -/
def readArgs : List String → Except String Args
  | cs :: h :: rest => do
    let words := (cs.splitOn " ").filter (· ≠ "")
    let coeffs ← words.mapM fun w ↦
      match w.toInt? with
      | some n => .ok n
      | none => .error s!"the coefficient '{w}' is not an integer"
    if coeffs.isEmpty then throw "no coefficients"
    let some H := h.toNat? | throw s!"the height bound '{h}' is not a natural number"
    readOptions { coeffs, H } rest
  | _ => .error "usage: ratpoints-lean 'a_0 a_1 ... a_n' H [-dl b] [-du b] [-q]"

/-- The line of a point. -/
def pointLine (p : Int × Int × Int) : String := s!"({p.1} : {p.2.1} : {p.2.2})"

/-- The program: the points of `Ratpoints.FastMask.fastPoints`, one per line. -/
def main (args : List String) : IO UInt32 := do
  match readArgs args with
  | .error e =>
    IO.eprintln e
    return 1
  | .ok a =>
    let out ← IO.getStdout
    for p in FastMask.fastPoints a.coeffs a.H a.bLow a.bHigh do
      out.putStrLn (pointLine p)
    return 0

end FastCli

end Ratpoints

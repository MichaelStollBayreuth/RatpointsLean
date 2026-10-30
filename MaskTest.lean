/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

import Ratpoints.Fast.Mask

/-!
# Differential test of the primitives of `Ratpoints.Mask`

Compares the C code of `Ratpoints.Mask.andShr` and `Ratpoints.Mask.nextSet` with their reference
definitions `Ratpoints.Mask.andShrSpec` and `Ratpoints.Mask.nextSetSpec`, compiled from Lean, on
random masks of every size up to 48 bytes (dense, sparse and empty), every shift up to past the
end of the row and shifts beyond `2 ^ 64`, with `acc` shared and not shared.
-/

open Ratpoints

/-- The next state of a linear congruential generator. -/
def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

/-- `n` random bytes, each bit set with probability `p / 8`, and the next state. -/
def randBytes (s₀ : UInt64) (n p : Nat) : ByteArray × UInt64 := Id.run do
  let mut s := s₀
  let mut a := ByteArray.emptyWithCapacity n
  for _ in [0:n] do
    let mut x : UInt8 := 0
    for j in [0:8] do
      s := lcg s
      if ((s >>> 40) % 8).toNat < p then x := x ||| (1 : UInt8) <<< j.toUInt8
    a := a.push x
  return (a, s)

/-- The test: the number of cases and of failures. -/
def run (rounds : Nat) : IO (Nat × Nat) := do
  let mut s : UInt64 := 2026
  let mut cases := 0
  let mut bad := 0
  for r in [0:rounds] do
    let n := r % 49
    let m := (r / 49) % 49
    let p := [8, 7, 4, 1, 0][(r / 2401) % 5]!
    let (acc, s₁) := randBytes s n p
    let (row, s₂) := randBytes s₁ m 8
    s := s₂
    for sh in (List.range (8 * m + 20)) ++ [2 ^ 62, 2 ^ 63, 2 ^ 64 + 3, 2 ^ 70] do
      cases := cases + 1
      let want := Mask.andShrSpec acc row sh
      -- shared: `acc` is used again below, so the C code must copy it
      let got := Mask.andShr acc row sh
      if got.data != want.data || acc.size != n then
        bad := bad + 1
        IO.println s!"andShr shared: n={n} m={m} s={sh}"
      -- not shared: a fresh copy, worked on in place
      let got' := Mask.andShr (ByteArray.mk acc.data.reverse.reverse) row sh
      if got'.data != want.data then
        bad := bad + 1
        IO.println s!"andShr exclusive: n={n} m={m} s={sh}"
    for j in (List.range (8 * n + 20)) ++ [2 ^ 63, 2 ^ 64 + 1] do
      cases := cases + 1
      if Mask.nextSet acc j != Mask.nextSetSpec acc j then
        bad := bad + 1
        IO.println s!"nextSet: n={n} j={j}"
  return (cases, bad)

/-- Runs the test with the number of rounds of the first argument (default `12005`). -/
public def main (args : List String) : IO UInt32 := do
  let (cases, bad) ← run ((args.headD "12005").toNat?.getD 12005)
  IO.println s!"{cases} cases, {bad} failures"
  return if bad == 0 then 0 else 1

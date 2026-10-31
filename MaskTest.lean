/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

import Ratpoints.Fast.Mask

/-!
# Differential test of the primitives of `Ratpoints.Mask`

Compares the C code of `Ratpoints.Mask.andShr`, `Ratpoints.Mask.andRows` and
`Ratpoints.Mask.nextSet` with their reference definitions `Ratpoints.Mask.andShrSpec`,
`Ratpoints.Mask.andRowsFrom` and `Ratpoints.Mask.nextSetSpec`, compiled from Lean (the reference
`Ratpoints.Mask.andRowsFrom` runs the C code of `Ratpoints.Mask.andShr`, which the first part of
the test checks): `andShr` and `nextSet` on random masks of every size up to 48 bytes (dense,
sparse and empty), every shift up to past the end of the row and shifts beyond `2 ^ 64`; `andRows`
on random masks of up to 1031 bytes with up to 70 rows (more than the 64 of its fast path), rows
long enough for the mask and shorter ones, shifts that are multiples of `8` and others, shifts
beyond `2 ^ 63`, offsets beyond `2 ^ 64`, a shift and an offset below `2 ^ 63` whose sum is not,
and fewer shifts than rows (the missing ones `0`); each with `acc` shared, whose bytes must stay
as they were, and not shared.
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

/-- The bytes of `a`, read by a function of its own: the test compares them after a call that must
leave `a` alone with `a.toList` taken before it, and the compiler would merge two equal reads of a
pure value into one, taken before the call. -/
@[noinline] def bytesAfter (a : ByteArray) : List UInt8 := a.toList

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
      -- shared: `acc` is used again below, so the C code must copy it and leave its bytes alone
      let before := acc.toList
      let got := Mask.andShr acc row sh
      if got.data != want.data || bytesAfter acc != before then
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

/-- The test of `Ratpoints.Mask.andRows`: the number of cases and of failures. -/
def runRows (rounds : Nat) : IO (Nat × Nat) := do
  let mut s : UInt64 := 1031
  let mut cases := 0
  let mut bad := 0
  for r in [0:rounds] do
    s := lcg s
    let n := [0, 1, 7, 8, 9, 64, 127, 128, 129, 255, 256, 300, 384, 400, 1024,
      1031][(s >>> 33).toNat % 16]!
    s := lcg s
    let f := [0, 1, 2, 3, 4, 5, 8, 15, 16, 17, 33, 64, 65, 70][(s >>> 33).toNat % 14]!
    s := lcg s
    let p := [8, 7, 4, 1, 0][(s >>> 33).toNat % 5]!
    let (acc, s₁) := randBytes s n p
    s := s₁
    s := lcg s
    -- in half of the rounds every row is fit for the fast path of the C code
    let clean := (s >>> 40) % 2 == 0
    let o := if clean then [0, 8, 64][(s >>> 33).toNat % 3]!
      else [0, 8, 64, 3, 2 ^ 64 + 8, 2 ^ 62][(s >>> 33).toNat % 6]!
    let mut rs : Array ByteArray := #[]
    let mut sh : Array Nat := #[]
    for j in [0:f] do
      s := lcg s
      let k := (s >>> 33).toNat
      -- mostly multiples of `8`, sometimes not, sometimes beyond `2 ^ 63`, sometimes below
      -- `2 ^ 63` but with a sum beyond it for the offset `2 ^ 62`
      let sj := if clean then 8 * (k % 40) else if k % 13 == 0 then k % 97
        else if k % 29 == 0 then 2 ^ 63 + 8 else if k % 7 == 0 then 2 ^ 62 + 8 else 8 * (k % 40)
      -- mostly long enough for the mask at this shift and the offset, sometimes too short
      let need := if sj + o < 2 ^ 20 then (sj + o) / 8 + n else n
      let m := if !clean && k % 17 == 0 then need / 2 else need + k % 3
      let (row, s₂) := randBytes s m (if j % 5 == 0 then 8 else 7)
      s := s₂
      rs := rs.push row
      -- sometimes no shift for the last row
      if !(j + 1 == f && k % 23 == 0) then sh := sh.push sj
    cases := cases + 1
    -- `sh[i]!` is `0` past the end of `sh` (after a panic message): the reference runs on `sh`
    -- padded with zeros
    let want := Mask.andRowsFrom rs (sh ++ Array.replicate (rs.size - sh.size) 0) o acc 0
    let before := acc.toList
    let got := Mask.andRows acc rs sh o
    if got.data != want.data || bytesAfter acc != before then
      bad := bad + 1
      IO.println s!"andRows shared: round={r} n={n} f={f} o={o}"
    let got' := Mask.andRows (ByteArray.mk acc.data.reverse.reverse) rs sh o
    if got'.data != want.data then
      bad := bad + 1
      IO.println s!"andRows exclusive: round={r} n={n} f={f} o={o}"
  return (cases, bad)

/-- Runs the test with the number of rounds of the first argument (default `12005`) for
`Ratpoints.Mask.andShr` and `Ratpoints.Mask.nextSet`, and four times as many for
`Ratpoints.Mask.andRows`. -/
public def main (args : List String) : IO UInt32 := do
  let rounds := (args.headD "12005").toNat?.getD 12005
  let (cases, bad) ← run rounds
  let (cases', bad') ← runRows (4 * rounds)
  IO.println s!"{cases + cases'} cases, {bad + bad'} failures"
  return if bad + bad' == 0 then 0 else 1

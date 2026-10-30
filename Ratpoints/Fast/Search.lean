/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Fast.Mask
public import Ratpoints.Fast.Sieve

/-!
# The fast search on byte-array masks

`Ratpoints.FastMask.fastPoints` is `Ratpoints.Fast.fastPoints` with the bit masks and the rows of
the families held in byte arrays (`Ratpoints.Mask`) instead of natural numbers: the AND of a chunk
with a row is one call of the primitive `Ratpoints.Mask.andShr`, in place, without the copies and
allocations of an AND of two GMP integers, and the survivors come from the primitive
`Ratpoints.Mask.nextSet`. The parameters, the families, the chunks, the order of the loops and the
exact check are those of `Ratpoints.Fast.fastPoints`; only the order of the points in a chunk may
differ. The shifts of the rows are multiples of `8` when the products of the moduli are odd, as
they are for every even step (`Ratpoints.Fast.Family.shift`), so that `Ratpoints.Mask.andShr`
reads whole bytes, and the rows of a denominator serve all its chunks in turn.

## Main definitions

* `Ratpoints.FastMask.fastPoints`: the points, by the sieve on byte-array masks.
-/

@[expose] public section

namespace Ratpoints

namespace FastMask

open BruteForce Fast

/-- `a` repeated `2 ^ k` times. -/
def repeatBytes (a : ByteArray) : Nat → ByteArray
  | 0 => a
  | k + 1 => let r := repeatBytes a k; r ++ r

/-- Horner's rule by plain recursion (`Ratpoints.BruteForce.horner` with `List.foldr`, which
copies the list into an array at each call). -/
def hornerRec : List Int → Int → Int
  | [], _ => 0
  | a :: w, x => a + x * hornerRec w x

/-- `Ratpoints.BruteForce.pointsOfDen` with `Ratpoints.FastMask.hornerRec`. -/
def pointsOfDen (c : List Int) (d : Nat) (z : Int) (xs : List Int) : List (Int × Int × Int) :=
  let w := scaledCoeffs c d z
  let f := if d % 2 = 1 then z else 1
  xs.flatMap fun x ↦ if Int.gcd x z = 1 then pointsAbove x z (hornerRec w x * f) else []

/-- The byte of the bits `q[o], …, q[o + 7]` (each `0` or `1`). -/
def windowByte (q : ByteArray) (o : Nat) : UInt8 :=
  q[o]! ||| q[o + 1]! <<< 1 ||| q[o + 2]! <<< 2 ||| q[o + 3]! <<< 3 ||| q[o + 4]! <<< 4 |||
    q[o + 5]! <<< 5 ||| q[o + 6]! <<< 6 ||| q[o + 7]! <<< 7

/-- The bytes `1` or `0` of the entries `T'[G * (k % m) % m]` for `k` from `k₀` to `m + 7`, pushed
to `acc`. -/
def patternBits (T' : Array Bool) (m G k : Nat) (acc : ByteArray) : ByteArray :=
  if k < m + 8 then patternBits T' m G (k + 1) (acc.push (if T'[G * (k % m) % m]! then 1 else 0))
  else acc
termination_by m + 8 - k

/-- The bytes `Ratpoints.FastMask.windowByte q o` for `i` from `i₀` to `m - 1`, with `o = 8 i % m`
carried along, pushed to `acc`. -/
def periodBytes (q : ByteArray) (m i o : Nat) (acc : ByteArray) : ByteArray :=
  if i < m then periodBytes q m (i + 1) (if o + 8 < m then o + 8 else (o + 8) % m)
    (acc.push (windowByte q o))
  else acc
termination_by m - i

/-- The row of the modulus `m` for the residue `r` of the denominator, for the numerators
`0, G, 2G, …`, as a mask of `nb` bytes: bit `j` is set when the residues `G j` and `r` modulo `m`
allow a point (`T = Ratpoints.Fast.admitTable c d m`). -/
def baseRow (T : Array (Array Bool)) (m G nb r : Nat) : ByteArray :=
  let q := patternBits T[r]! m G 0 (ByteArray.emptyWithCapacity (m + 8))
  let period := periodBytes q m 0 0 (ByteArray.emptyWithCapacity m)
  (repeatBytes period (Nat.log2 (nb / m) + 1)).extract 0 nb

/-- A family of moduli with product `M`: an inverse `ginv` of the step modulo `M` and the rows
for the residues `r < M` of the denominator, as masks. -/
structure Family where
  /-- The product of the moduli. -/
  M : Nat
  /-- An inverse of the step `G` modulo `M`. -/
  ginv : Nat
  /-- The rows, for the residues `0, …, M - 1` of the denominator. -/
  rows : Array ByteArray

/-- The family of the moduli of the list `ts` of pairs `(m, T)`, for the step `G` and chunks of at
most `L` numerators, with rows of `L + 8 M` bits, `M` the product of the moduli. -/
def mkFamily (G L : Nat) (ts : List (Nat × Array (Array Bool))) : Option Family :=
  if ts.all (0 < ·.1) then
    let M := ts.foldl (· * ·.1) 1
    match (List.range M).find? fun u ↦ G * u % M == 1 % M with
    | none => none
    | some ginv =>
      let N := L + 8 * M
      let nb := 8 * ((N + 63) / 64)
      let base := ts.map fun (m, T) ↦ (m, (List.range m).toArray.map (baseRow T m G nb))
      let full := Mask.ones N
      some { M, ginv, rows := (List.range M).toArray.map fun r ↦
        base.foldl (fun acc (m, B) ↦ Mask.andShr acc B[r % m]! 0) full }
  else none

/-- The shift that aligns the rows of the family `F` with a chunk starting at `a₀`
(`Ratpoints.Fast.Family.shift`). -/
def Family.shift (F : Family) (a₀ : Int) : Nat :=
  let s := (a₀ * F.ginv % (F.M : Int)).toNat
  s + F.M * ((8 - s % 8) * F.M % 8)

/-- The candidates of a chunk: `acc` ANDed with the rows `rs[i]` shifted by `sh[i]` from position
`i` on, until nothing is left. -/
def sieveFrom (rs : Array ByteArray) (sh : Array Nat) (acc : ByteArray) (i : Nat) : ByteArray :=
  if h : i < rs.size then
    let acc := Mask.andShr acc rs[i] sh[i]!
    if acc.size == 0 then acc else sieveFrom rs sh acc (i + 1)
  else acc
termination_by rs.size - i

/-- The points with the denominator `b` in the chunk of the numerators `a₀, a₀ + G, …` with the
mask `mask` (one bit per numerator), by the sieve with the rows `rs` of `b` and the shifts `sh` of
the chunk. -/
def chunkPoints (c : List Int) (d G : Nat) (rs : Array ByteArray) (sh : Array Nat) (a₀ : Int)
    (mask : ByteArray) (b : Nat) : List (Int × Int × Int) :=
  let acc := sieveFrom rs sh mask 0
  if acc.size == 0 then []
  else FastMask.pointsOfDen c d b ((Mask.setBits acc).map fun t ↦ a₀ + (G * t : Nat))

/-- The points with the denominators `dens`, by the sieve (as `Ratpoints.Fast.search`); the rows
that are `0` are found once per family. -/
def search (c : List Int) (d H G L : Nat) (fams : Array Family) (dens : List Nat) :
    List (Int × Int × Int) :=
  let fams := fams.filter fun F ↦ F.rows.size == F.M && 0 < F.M
  let zs := fams.map fun F ↦ (F.M, F.rows.map Mask.isZero)
  let dens := dens.filter fun b ↦ zs.all fun (M, z) ↦ !z[b % M]!
  let TG := admitTable c d G
  let sl := (slots H G L).map fun (r, a₀, len) ↦
    (r, a₀, Mask.ones len, fams.map (Family.shift · a₀))
  let byRes := (List.range G).toArray.map fun g ↦ sl.filter fun (r, _) ↦ TG[g]![r]!
  dens.flatMap fun b ↦
    let rs := fams.map fun F ↦ F.rows[b % F.M]!
    byRes[b % G]!.flatMap fun (_, a₀, mask, sh) ↦ chunkPoints c d G rs sh a₀ mask b

/-- The parameters of the search: step, chunk length, families. -/
structure Config where
  /-- The step. -/
  G : Nat
  /-- The largest chunk length. -/
  L : Nat
  /-- The families. -/
  fams : Array Family

/-- The parameters for the coefficients `c` of degree `d`, the height bound `H` and `B`
denominators (as `Ratpoints.Fast.choose`). -/
def choose (tu : Tuning) (c : List Int) (d H B : Nat) : Config :=
  let G := orDefault tu.G 16
  let cnt := (2 * H + 1 + G - 1) / G
  let L := max 1 (min (orDefault tu.L 8192) cnt)
  { G, L, fams := ((sortedGroups tu c d H B).filterMap (mkFamily G L)).toArray }

/-- The points of height at most `H` with their denominator in the range of `bLow` and
`bHigh`, each once (as `Ratpoints.Fast.fastPoints`). -/
def fastPoints (c : List Int) (H : Nat) (bLow bHigh : Int) (tu : Tuning := {}) :
    List (Int × Int × Int) :=
  let d := BruteForce.degree c
  let dens := denominators c d H bLow bHigh
  let cfg := choose tu c d H dens.length
  (if 1 ≤ H then FastMask.pointsOfDen c d 0 [1] else []) ++
    search c d H cfg.G cfg.L cfg.fams dens

end FastMask

end Ratpoints

/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Fast.Mask
public import Ratpoints.Model.FastSieve

/-!
# The fast search on byte-array masks (prototype)

`Ratpoints.FastMask.fastPoints` is `Ratpoints.Fast.fastPoints` with the bit masks and the rows of
the families held in byte arrays (`Ratpoints.Mask`) instead of natural numbers: the AND of a
chunk with a row is one call of the primitive `Ratpoints.Mask.andShr`, in place, without the
copies and allocations of an AND of two GMP integers.
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

/-- The row of the modulus `m` for the residue `r` of the denominator, for the numerators
`0, G, 2G, …`, as a mask of `nb` bytes: bit `j` is set when the residues `G j` and `r` modulo `m`
allow a point (`T = Ratpoints.Fast.admitTable c d m`). -/
def baseRow (T : Array (Array Bool)) (m G nb r : Nat) : ByteArray :=
  let Tr := T[r]!
  let q : ByteArray := ⟨Array.ofFn (n := m + 8) fun k ↦ if Tr[G * (k.val % m) % m]! then 1 else 0⟩
  let period : ByteArray := ⟨Array.ofFn (n := m) fun i ↦ windowByte q (8 * i.val % m)⟩
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

/-- The family of the moduli of the list `ts` of pairs `(m, T)`, for the step `G` and rows of
`N` bits. -/
def mkFamily (G N : Nat) (ts : List (Nat × Array (Array Bool))) : Option Family :=
  if ts.all (0 < ·.1) then
    let M := ts.foldl (· * ·.1) 1
    match (List.range M).find? fun u ↦ G * u % M == 1 % M with
    | none => none
    | some ginv =>
      let nb := 8 * ((N + 63) / 64)
      let base := ts.map fun (m, T) ↦ (m, (List.range m).toArray.map (baseRow T m G nb))
      let full := Mask.ones N
      some { M, ginv, rows := (List.range M).toArray.map fun r ↦
        base.foldl (fun acc (m, B) ↦ Mask.andShr acc B[r % m]! 0) full }
  else none

/-- The shift that aligns the rows of the family `F` with a chunk starting at `a₀`. -/
def Family.shift (F : Family) (a₀ : Int) : Nat := (a₀ * F.ginv % (F.M : Int)).toNat

/-- An entry of the sieve of a chunk: the modulus, the rows and the shift to apply to them. -/
structure Entry where
  /-- The period of the rows in the denominator. -/
  M : Nat
  /-- The rows. -/
  rows : Array ByteArray
  /-- The shift to apply to a row. -/
  shift : Nat

/-- The candidates of a chunk for the denominator `b`: `acc` ANDed with the rows of the entries
from position `i` on, until nothing is left. -/
def sieveFrom (es : Array Entry) (b : Nat) (acc : ByteArray) (i : Nat) : ByteArray :=
  if h : i < es.size then
    let e := es[i]
    let acc := Mask.andShr acc e.rows[b % e.M]! e.shift
    if acc.size == 0 then acc else sieveFrom es b acc (i + 1)
  else acc
termination_by es.size - i

/-- The entries of the sieve for the chunk of `len` numerators from `a₀`, for `nb`
denominators. -/
def entries (fams : Array Family) (nb : Nat) (a₀ : Int) (len : Nat) : Array Entry :=
  let mask := Mask.ones len
  (fams.zipIdx).map fun (F, i) ↦
    if (i + 1) * F.M ≤ nb then
      { M := F.M, rows := F.rows.map fun R ↦ Mask.andShr mask R (F.shift a₀), shift := 0 }
    else { M := F.M, rows := F.rows, shift := F.shift a₀ }

/-- The points of the chunk of `len` numerators `a₀, a₀ + G, …` for the denominators `bs`. -/
def chunkPoints (c : List Int) (d G : Nat) (es : Array Entry) (a₀ : Int) (len : Nat)
    (bs : List Nat) : List (Int × Int × Int) :=
  let mask := Mask.ones len
  bs.flatMap fun b ↦
    let acc := sieveFrom es b mask 0
    if acc.size == 0 then []
    else FastMask.pointsOfDen c d b ((Mask.setBits acc).map fun t ↦ a₀ + (G * t : Nat))

/-- The points with the denominators `dens`, by the sieve. -/
def search (c : List Int) (d H G L N pre : Nat) (fams : Array Family) (dens : List Nat) :
    List (Int × Int × Int) :=
  let fams := fams.filter fun F ↦ L + F.M ≤ N && F.rows.size == F.M && 0 < F.M
  let dens := dens.filter fun b ↦ fams.all fun F ↦ !Mask.isZero F.rows[b % F.M]!
  let TG := admitTable c d G
  (List.range G).flatMap fun (ρ : Nat) ↦
    let bs := dens.filter fun b ↦ TG[b % G]![(((ρ : Int) - H) % (G : Int)).toNat]!
    (chunks (classCount (2 * H + 1) G ρ) L).flatMap fun (t₀, len) ↦
      let a₀ : Int := ((ρ + G * t₀ : Nat) : Int) - H
      chunkPoints c d G (entries fams (pre * bs.length) a₀ len) a₀ len bs

/-- The parameters of the search: step, chunk length, row length, weight, families. -/
structure Config where
  /-- The step. -/
  G : Nat
  /-- The largest chunk length. -/
  L : Nat
  /-- The length of the rows. -/
  N : Nat
  /-- The weight of the number of denominators in the choice of the pre-cut families. -/
  pre : Nat
  /-- The families. -/
  fams : Array Family

/-- The parameters for the coefficients `c` of degree `d`, the height bound `H` and `B`
denominators (as `Ratpoints.Fast.choose`). -/
def choose (tu : Tuning) (c : List Int) (d H B : Nat) : Config :=
  let G := orDefault tu.G 16
  let cnt := (2 * H + 1 + G - 1) / G
  let L := max 1 (min (orDefault tu.L 8192) cnt)
  let Mmax := orDefault tu.Mmax (max 15 (min 1500 (B / 16)))
  let work := orDefault tu.work 256
  let ms := candidateModuli.filter fun m ↦ m * m * work ≤ (2 * H + 1) * B
  let tabs := ms.map fun m ↦ (m, admitTable c d m)
  let scored := (groupModuli Mmax tabs).map fun g ↦
    (g, g.foldl (fun s (m, T) ↦ s * density m T / 1000) 1000)
  let sorted := (scored.mergeSort fun x y ↦ x.2 ≤ y.2).map (·.1)
  let N := L + sorted.foldl (fun n g ↦ max n (g.foldl (· * ·.1) 1)) 1
  { G, L, N, pre := orDefault tu.pre 1, fams := (sorted.filterMap (mkFamily G N)).toArray }

/-- The points of height at most `H` with their denominator in the range of `bLow` and
`bHigh`, each once (as `Ratpoints.Fast.fastPoints`). -/
def fastPoints (c : List Int) (H : Nat) (bLow bHigh : Int) (tu : Tuning := {}) :
    List (Int × Int × Int) :=
  let d := BruteForce.degree c
  let dens := denominators c d H bLow bHigh
  let cfg := choose tu c d H dens.length
  (if 1 ≤ H then FastMask.pointsOfDen c d 0 [1] else []) ++
    search c d H cfg.G cfg.L cfg.N cfg.pre cfg.fams dens

end FastMask

end Ratpoints

/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.BruteForce

/-!
# A fast search for the points

`Ratpoints.Fast.fastPoints c H bLow bHigh` lists the normalized points of height at most `H` on
`y ^ 2 = F(x, z)` whose denominator `z` lies in the range of `bLow` and `bHigh` (the points at
infinity always), each once, in an order of its own. It is not a model of the C code: it sieves
in the way that suits Lean, with bit masks held in natural numbers, which Lean represents by GMP
integers, so that one `&&&` ANDs thousands of candidates without an allocation per word.

* The numerators `x = -H, …, H` are split into the classes of `x + H` modulo `G = 2 ^ e`; a class
  is searched for the denominator `b` only when the residues of `x` and `b` modulo `G` allow a
  point (`Ratpoints.Fast.admitTable`).
* Each class is searched in chunks of at most `L` numerators `a₀, a₀ + G, a₀ + 2G, …`. A chunk
  is a bit mask with one bit per numerator, ANDed with the rows of the families of moduli
  (`Ratpoints.Fast.Family`): the row of the family of the moduli `m₁, …, mₖ` for `b` has the bit
  of `x` set when for every `mᵢ` the residues of `x` and `b` allow a point. The rows of a family
  depend on `b` modulo `M = m₁ ⋯ mₖ` only, and on `x` modulo `M`: they are made once, for the
  numerators `0, G, 2G, …`, and shifted to the start of a chunk.
* The bits that survive go to the exact check of the brute force,
  `Ratpoints.BruteForce.pointsOfDen`.
* For odd degree only the denominators `s k ^ 2` with `s` dividing the leading coefficient can
  carry a point, and only they are searched.

The choice of `G`, `L` and the families affects the speed only: the proofs hold for every choice.

## Main definitions

* `Ratpoints.Fast.fastPoints`: the points, by the sieve.
-/

@[expose] public section

namespace Ratpoints

namespace Fast

open BruteForce

/-! ### Residues that allow a point -/

/-- The squares modulo `m`: entry `v` is `true` when `v = y * y % m` for some `y < m`. -/
def sqTable (m : Nat) : Array Bool :=
  Array.ofFn (n := m) fun v ↦ (List.range m).any fun y ↦ y * y % m == v.val

/-- Horner's rule modulo `m`: the value `w₀ + x (w₁ + x (w₂ + ⋯))` reduced modulo `m` at each
step. -/
def hornerMod : List Int → Int → Nat → Int
  | [], _, _ => 0
  | a :: w, x, m => (a + x * hornerMod w x m) % (m : Int)

/-- `r ^ e % m`, by repeated multiplication modulo `m`. -/
def powMod (r m : Nat) : Nat → Nat
  | 0 => 1 % m
  | e + 1 => powMod r m e * r % m

/-- The products `cₖ r^(d - k)` of `Ratpoints.BruteForce.scaledCoeffs c d r`, reduced modulo
`m`. -/
def scaledCoeffsMod (c : List Int) (d m r : Nat) : List Int :=
  (List.range (d + 1)).map fun k ↦ c.getD k 0 % (m : Int) * (powMod r m (d - k) : Int)

/-- Whether `x` has no prime factor in common with `g`, quickly when `g = 1`. -/
def coprimeWith (g x : Nat) : Bool := g == 1 || Nat.gcd x g == 1

/-- The residues modulo `m` that allow a point `(a, y, b)` with `gcd(a, b) = 1` of the binary form
of degree `d` of `c`: entry `x` of row `r` (for `r, x < m`) is `true` when `x`, `r` and `m` have no
prime factor in common and `F(x, r)` is a square modulo `m`. -/
def admitTable (c : List Int) (d m : Nat) : Array (Array Bool) :=
  let sq := sqTable m
  (List.range m).toArray.map fun (r : Nat) ↦
    let w := scaledCoeffsMod c d m r
    let f : Int := if d % 2 = 1 then r else 1
    let g := Nat.gcd r m
    (List.range m).toArray.map fun x ↦
      coprimeWith g x && sq[(hornerMod w x m * f % (m : Int)).toNat]!

/-! ### Bit masks -/

/-- The number with bit `j` set for every `j < m` with `f j`. -/
def pattern (m : Nat) (f : Nat → Bool) : Nat :=
  (List.range m).foldl (fun P j ↦ if f j then P ||| 1 <<< j else P) 0

/-- The pattern `P` of `m` bits repeated `2 ^ k` times. -/
def repeatPattern (P m : Nat) : Nat → Nat
  | 0 => P
  | k + 1 => repeatPattern P m k ||| repeatPattern P m k <<< (m * 2 ^ k)

/-- A number `k` of doublings with `N ≤ m * 2 ^ k` for `0 < m`. -/
def doublings (m N : Nat) : Nat := Nat.log2 (N / m) + 1

/-- The positions of the bits set in `n`, from the highest down, one `Nat.log2` at a time. -/
def setBitsSmall (n : Nat) : List Nat :=
  if h : n = 0 then [] else n.log2 :: setBitsSmall (n - 2 ^ n.log2)
termination_by n
decreasing_by exact Nat.sub_lt (Nat.pos_of_ne_zero h) (Nat.two_pow_pos _)

/-- The positions, offset by `o`, of the bits set in `n`: those of `n >>> h` and of `n % 2 ^ h`
for `h = 64 * 2 ^ (k - 1)` in turn, down to `k = 0`, where `Ratpoints.Fast.setBitsSmall` takes all
the bits that are left. -/
def setBitsAux (o n : Nat) : Nat → List Nat
  | 0 => (setBitsSmall n).map (o + ·)
  | k + 1 =>
    if n = 0 then [] else
      let h := 64 * 2 ^ k
      setBitsAux (o + h) (n >>> h) k ++ setBitsAux o (n % 2 ^ h) k

/-- The positions of the bits set in `n`, in descending order. -/
def setBits (n : Nat) : List Nat := setBitsAux 0 n (Nat.log2 (n.log2 / 64 + 1) + 1)

/-! ### Families of moduli -/

/-- The row of the modulus `m` for the residue `r` of the denominator, for the numerators
`0, G, 2G, …` and at least `N` of them, from the table `T = Ratpoints.Fast.admitTable c d m`: bit
`j` is set when the residues `G j` and `r` modulo `m` allow a point. -/
def baseRow (T : Array (Array Bool)) (m G N r : Nat) : Nat :=
  repeatPattern (pattern m fun j ↦ T[r]![G * j % m]!) m (doublings m N)

/-- A family of moduli with product `M`, for the step `G` of the numerators: an inverse `ginv` of
`G` modulo `M` and the rows for the residues `r < M` of the denominator, for the numerators
`0, G, 2G, …`: the AND of the rows of its moduli (`Ratpoints.Fast.baseRow`). -/
structure Family where
  /-- The product of the moduli. -/
  M : Nat
  /-- An inverse of the step `G` modulo `M`. -/
  ginv : Nat
  /-- The rows, for the residues `0, …, M - 1` of the denominator. -/
  rows : Array Nat

/-- The family of the moduli `m` of the list `ts` of pairs `(m, T)`, `T` the table
`Ratpoints.Fast.admitTable c d m`, for the step `G` and rows of `N` bits, if every modulus is
positive and `G` is invertible modulo their product. -/
def mkFamily (G N : Nat) (ts : List (Nat × Array (Array Bool))) : Option Family :=
  if ts.all (0 < ·.1) then
    let M := ts.foldl (· * ·.1) 1
    match (List.range M).find? fun u ↦ G * u % M == 1 % M with
    | none => none
    | some ginv =>
      let base := ts.map fun (m, T) ↦ (m, (List.range m).toArray.map (baseRow T m G N))
      let full := 2 ^ N - 1
      some { M, ginv, rows := (List.range M).toArray.map fun r ↦
        base.foldl (fun acc (m, B) ↦ acc &&& B[r % m]!) full }
  else none

/-- The shift that aligns the rows of the family `F` with a chunk starting at the numerator
`a₀`: `s` with `G s ≡ a₀` modulo `F.M`. -/
def Family.shift (F : Family) (a₀ : Int) : Nat := (a₀ * F.ginv % (F.M : Int)).toNat

/-! ### The sieve -/

/-- An entry of the sieve of a chunk: the modulus `M`, the rows and the shift to apply to them. -/
structure Entry where
  /-- The period of the rows in the denominator. -/
  M : Nat
  /-- The rows. -/
  rows : Array Nat
  /-- The shift to apply to a row. -/
  shift : Nat

/-- The candidates of a chunk for the denominator `b`: the mask ANDed with the row of every entry,
shifted; once nothing is left, the rest is skipped. -/
def sieve (es : Array Entry) (mask b : Nat) : Nat :=
  es.foldl (fun acc e ↦
    if acc == 0 then 0 else
      let row := e.rows[b % e.M]!
      acc &&& if e.shift == 0 then row else row >>> e.shift) mask

/-- The entries of the sieve for the chunk of `len` numerators from `a₀`, for `nb` denominators:
the family at position `i` with its rows shifted and cut to the chunk once when
`(i + 1) M ≤ nb` (it is used often enough), the others shifted for each use. -/
def entries (fams : Array Family) (nb : Nat) (a₀ : Int) (len : Nat) : Array Entry :=
  let mask := 2 ^ len - 1
  (fams.zipIdx).map fun (F, i) ↦
    if (i + 1) * F.M ≤ nb then
      { M := F.M, rows := F.rows.map fun R ↦ (R >>> F.shift a₀) &&& mask, shift := 0 }
    else { M := F.M, rows := F.rows, shift := F.shift a₀ }

/-- The number of the indices `i < n` with `i % G = ρ`. -/
def classCount (n G ρ : Nat) : Nat := (n + G - 1 - ρ) / G

/-- The chunks of `[0, cnt)`: their starts `k L` and lengths `min L (cnt - k L)`. -/
def chunks (cnt L : Nat) : List (Nat × Nat) :=
  (List.range ((cnt + L - 1) / L)).map fun k ↦ (k * L, min L (cnt - k * L))

/-- The points of the chunk of `len` numerators `a₀, a₀ + G, …` for the denominators `bs`. -/
def chunkPoints (c : List Int) (d G : Nat) (es : Array Entry) (a₀ : Int) (len : Nat)
    (bs : List Nat) : List (Int × Int × Int) :=
  let mask := 2 ^ len - 1
  bs.flatMap fun b ↦
    let acc := sieve es mask b
    if acc == 0 then [] else pointsOfDen c d b ((setBits acc).map fun t ↦ a₀ + (G * t : Nat))

/-- The points with the denominators `dens` (all positive), by the sieve with the step `G`, chunks
of `L` numerators and the families `fams` with rows of `N` bits; `pre` weighs the number of
denominators in the choice of the families cut to a chunk (`Ratpoints.Fast.entries`). -/
def search (c : List Int) (d H G L N pre : Nat) (fams : Array Family) (dens : List Nat) :
    List (Int × Int × Int) :=
  let fams := fams.filter fun F ↦ L + F.M ≤ N && F.rows.size == F.M && 0 < F.M
  let dens := dens.filter fun b ↦ fams.all fun F ↦ F.rows[b % F.M]! != 0
  let TG := admitTable c d G
  (List.range G).flatMap fun (ρ : Nat) ↦
    let bs := dens.filter fun b ↦ TG[b % G]![(((ρ : Int) - H) % (G : Int)).toNat]!
    (chunks (classCount (2 * H + 1) G ρ) L).flatMap fun (t₀, len) ↦
      let a₀ : Int := ((ρ + G * t₀ : Nat) : Int) - H
      chunkPoints c d G (entries fams (pre * bs.length) a₀ len) a₀ len bs

/-! ### The denominators -/

/-- Whether `k` is a square. -/
def isSquare (k : Nat) : Bool := k.sqrt * k.sqrt == k

/-- The denominators of the search, for the degree `d`, the height bound `H` and the range of
`bLow` and `bHigh`: those `b` with `max 1 bLow ≤ b ≤ H`, and `b ≤ bHigh` unless `bHigh < 1`; for
odd `d` only those of the form `s k ^ 2` with `s` dividing the leading coefficient. -/
def denominators (c : List Int) (d H : Nat) (bLow bHigh : Int) : List Nat :=
  let lo := max 1 bLow.toNat
  let hi := if bHigh < 1 then H else min H bHigh.toNat
  let bs := List.range' lo (hi + 1 - lo)
  if d % 2 = 1 then
    let n := (c.getD d 0).natAbs
    let divs := (List.range' 1 hi).filter fun s ↦ n % s == 0
    bs.filter fun b ↦ divs.any fun s ↦ b % s == 0 && isSquare (b / s)
  else bs

/-! ### The choice of the parameters -/

/-- The fraction, in thousandths, of the pairs of residues modulo `m` that allow a point, from
the table `T = Ratpoints.Fast.admitTable c d m`. -/
def density (m : Nat) (T : Array (Array Bool)) : Nat :=
  let n := T.foldl (fun n row ↦ row.foldl (fun n b ↦ if b then n + 1 else n) n) 0
  1000 * n / (m * m)

/-- The pairs `(m, T)` grouped into families: in ascending order of `m`, each family taking moduli
while their product stays at most `Mmax`. -/
def groupModuli (Mmax : Nat) :
    List (Nat × Array (Array Bool)) → List (List (Nat × Array (Array Bool)))
  | [] => []
  | t :: ts =>
    match groupModuli Mmax ts with
    | (g :: gs) => if t.1 * g.foldl (· * ·.1) 1 ≤ Mmax then (t :: g) :: gs else [t] :: g :: gs
    | [] => [[t]]

/-- The parameters of the search: the step `G`, the chunk length `L`, the length `N` of the rows,
the number `pre` of families cut to each chunk, and the families, the most selective first. -/
structure Config where
  /-- The step of the numerators in a chunk, a power of `2`. -/
  G : Nat
  /-- The largest number of numerators in a chunk. -/
  L : Nat
  /-- The length of the rows of the families. -/
  N : Nat
  /-- The weight of the number of denominators in the choice of the families cut to a chunk
  (`Ratpoints.Fast.entries`). -/
  pre : Nat
  /-- The families. -/
  fams : Array Family

/-- The moduli that the sieve may use. -/
def candidateModuli : List Nat :=
  [9, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
    101, 103, 107, 109, 113, 127]

/-- Settings of the choice of the parameters (for tuning): the step `G`, the largest chunk
length, the largest product of a family, the number of families cut to each chunk, and the
divisor of the work bound for the moduli; `0` for the default. -/
structure Tuning where
  /-- The step. -/
  G : Nat := 0
  /-- The largest chunk length. -/
  L : Nat := 0
  /-- The largest product of the moduli of a family. -/
  Mmax : Nat := 0
  /-- The weight of the number of denominators in the choice of the families cut to a chunk. -/
  pre : Nat := 0
  /-- A modulus `m` is used when `m ^ 2 * work ≤ n B`. -/
  work : Nat := 0

/-- `x`, or `dflt` when `x = 0`. -/
def orDefault (x dflt : Nat) : Nat := if x = 0 then dflt else x

/-- The parameters for the coefficients `c` of degree `d`, the height bound `H` and `B`
denominators. -/
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

/-! ### The search -/

/-- The normalized points of height at most `H` on `y ^ 2 = F(x, z)` whose denominator `z` is `0`
or lies in the range of `bLow` and `bHigh` (`bLow ≤ z`, and `z ≤ bHigh` unless `bHigh < 1`), each
once: the points at infinity, then those that the sieve finds. -/
def fastPoints (c : List Int) (H : Nat) (bLow bHigh : Int) (tu : Tuning := {}) :
    List (Int × Int × Int) :=
  let d := BruteForce.degree c
  let dens := denominators c d H bLow bHigh
  let cfg := choose tu c d H dens.length
  (if 1 ≤ H then pointsOfDen c d 0 [1] else []) ++
    search c d H cfg.G cfg.L cfg.N cfg.pre cfg.fams dens

end Fast

end Ratpoints

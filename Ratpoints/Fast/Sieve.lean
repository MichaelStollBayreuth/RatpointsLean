/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.BruteForce
public import Ratpoints.Model.Candidate
public import Ratpoints.Model.Setup
public import Ratpoints.Model.Sturm

/-!
# The fast search: tables, region, denominators, parameters

The parts of the fast search `Ratpoints.FastMask.fastPoints` that do not depend on its bit masks.
The search is not a model of the C code: it sieves in the way that suits Lean, with bit masks in
byte arrays that a few primitives AND in bulk (`Ratpoints.Mask`).

* The residues modulo `m` of a numerator `x` and a denominator `r` allow a point when `x`, `r` and
  `m` have no prime factor in common and `F(x, r)` is a square modulo `m`
  (`Ratpoints.Fast.admitRow`). Since `F(x, r) = r ^ D F(x u, 1)` with `D` even when `u` inverts `r`,
  the table of a modulus (`Ratpoints.Fast.Table`) holds row `1`, the inverses, and the rows of the
  residues without an inverse only; `Ratpoints.Fast.Table.admits` reads an entry from it.
* The numerators `-H, …, H` are split into the classes of `x + H` modulo the step `G`, each class
  into chunks (`Ratpoints.Fast.classCount`, `Ratpoints.Fast.chunks`).
* The numerators of a denominator `b` are those `a` with `a / b` in the intervals that the Sturm
  step of `ratpoints` keeps (`Ratpoints.Fast.region`), outside of which `F(a, b) < 0` assuming
  Sturm's theorem.
* For odd degree only the denominators `s k ^ 2` with `s` dividing the leading coefficient can
  carry a point, and only they are searched; for even degree no multiple of an odd `p` with
  `(c_d / p) = -1` can (`Ratpoints.Fast.denominators`).
* Without a range of the denominators the coefficients are reversed where the reversal check of
  `ratpoints` reverses them (`Ratpoints.Fast.reversed`).

The settings `Ratpoints.Fast.Tuning` affect the speed, and the step also the order of the points,
but not which points are listed: the proofs hold for every choice.
-/

@[expose] public section

namespace Ratpoints

namespace Fast

open BruteForce

/-! ### Residues that allow a point -/

/-- The squares modulo `m`: entry `v` is `true` when `v = y * y % m` for some `y < m` (each
`y * y % m` marked in turn). -/
def sqTable (m : Nat) : Array Bool :=
  (List.range m).foldl (fun A y ↦ A.set! (y * y % m) true) (Array.replicate m false)

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

/-- `Nat.gcd a b` by Euclid's algorithm in Lean, which on small numbers is much faster than the
runtime's `Nat.gcd`: that one goes through GMP. -/
def natGcd (a b : Nat) : Nat := if b = 0 then a else natGcd b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero ‹_›)

/-- Whether `x` has no prime factor in common with `g`, quickly when `g = 1`. -/
def coprimeWith (g x : Nat) : Bool := g == 1 || natGcd x g == 1

/-- The residues `x` of the numerator that allow a point with the residue `r` of the denominator
modulo `m`, for the binary form of degree `d` of `c` (`sq` is `Ratpoints.Fast.sqTable m`): entry
`x` is `true` when `x`, `r` and `m` have no prime factor in common and `F(x, r)` is a square modulo
`m`. -/
def admitRow (c : List Int) (d m : Nat) (sq : Array Bool) (r : Nat) : Array Bool :=
  let w := scaledCoeffsMod c d m r
  let f : Int := if d % 2 = 1 then r else 1
  let g := natGcd r m
  (List.range m).toArray.map fun x ↦
    coprimeWith g x && sq[(hornerMod w x m * f % (m : Int)).toNat]!

/-- Candidates for the inverses modulo `m`, entry `i` by `inv i = -(m / i) inv (m % i)`: the
inverses when `m` is prime, and checked where they are used. -/
def invTable (m : Nat) : Array Nat :=
  (List.range m).foldl (fun inv i ↦
    inv.push (if i ≤ 1 then i else (m - m / i * inv[m % i]! % m) % m)) #[]

/-- The table of a modulus `m`: the row `Ratpoints.Fast.admitRow c d m sq 1` as bytes `1` and
`0`, the candidates `inv` for the inverses modulo `m` (`Ratpoints.Fast.invTable`), and for each
residue `r` either the empty array, when `inv[r]` inverts `r`, so that the row of `r` is row `1`
permuted, or the row of `r` as bytes. -/
structure Table where
  /-- The modulus. -/
  m : Nat
  /-- Row `1`. -/
  one : ByteArray
  /-- The candidates for the inverses. -/
  inv : Array Nat
  /-- The rows of the residues `r` that `inv[r]` does not invert, the empty array for the others. -/
  sing : Array ByteArray

/-- The entries of `row` as bytes `1` and `0`. -/
def boolBytes (row : Array Bool) : ByteArray := ⟨row.map (·.toUInt8)⟩

/-- The table of the modulus `m` for the binary form of degree `d` of `c`. -/
def mkTable (c : List Int) (d m : Nat) : Table :=
  let sq := sqTable m
  let inv := invTable m
  { m, one := boolBytes (admitRow c d m sq 1), inv,
    sing := (List.range m).toArray.map fun r ↦
      if r * inv[r]! % m == 1 % m && inv[r]! < m then .empty else boolBytes (admitRow c d m sq r) }

/-- Whether the residues `x` of the numerator and `r` of the denominator modulo `T.m` allow a
point: entry `x` of `Ratpoints.Fast.admitRow` for `r`, read from row `1` at `x u` when `u = inv[r]`
inverts `r`. -/
@[inline] def Table.admits (T : Table) (x r : Nat) : Bool :=
  let s := T.sing[r]!
  if s.size == 0 then T.one.get! (x * T.inv[r]! % T.m) != 0 else s.get! x != 0

/-- The number of nonzero entries of `a`. -/
def countOnes (a : ByteArray) : Nat := a.foldl (fun n x ↦ if x != 0 then n + 1 else n) 0

/-- The fraction, in thousandths, of the pairs of residues modulo `T.m` that allow a point. -/
def Table.density (T : Table) : Nat :=
  let c₁ := countOnes T.one
  1000 * (T.sing.foldl (fun n s ↦ n + if s.size == 0 then c₁ else countOnes s) 0) / (T.m * T.m)

/-! ### Classes and chunks -/

/-- The number of the indices `i < n` with `i % G = ρ`. -/
def classCount (n G ρ : Nat) : Nat := (n + G - 1 - ρ) / G

/-- The chunks of `[0, cnt)`: their starts `k L` and lengths `min L (cnt - k L)`. -/
def chunks (cnt L : Nat) : List (Nat × Nat) :=
  (List.range ((cnt + L - 1) / L)).map fun k ↦ (k * L, min L (cnt - k * L))

/-! ### The region -/

/-- The intervals of `x` that the Sturm step of `ratpoints` (`Ratpoints.Sturm.computeSturm`) keeps
at the depth `depth` of the whole line, outside of which `F(x, 1) < 0` assuming Sturm's theorem;
`none`, no restriction, when the step does not apply (the degree `0` or at least `2 ^ 57`, a height
of at least `2 ^ 63`, a depth beyond `55`, or a polynomial that is not squarefree). -/
def sturmIntervals (c : List Int) (d H depth : Nat) : Option (Array (Double × Double)) :=
  if 1 ≤ d ∧ d < 2 ^ 57 ∧ H < 2 ^ 63 ∧ depth ≤ 55 then
    Id.run (Sturm.computeSturm c d depth #[(Double.huge.neg, Double.huge)])
  else none

/-- An end of an interval of the region, for the numerators of absolute value at most `H`: the
exact value `n / q` of the double in lowest terms (`q` a power of `2`) when it is finite and of
absolute value at most `H`, else `H + 1` or `-(H + 1)` by its sign (an infinity too), which bound
the values `a / b` with `|a| ≤ H` and `b ≥ 1` as the end does, so that an interval beyond `H`
keeps no numerator; `none`, read by `Ratpoints.FastMask.roundEnd` as no bound, only for a NaN. -/
def endFrac (H : Nat) (x : Double) : Option (Int × Nat) :=
  if x.isFinite then
    let (m, e) := x.toDyadic
    let q := 2 ^ (-e).toNat
    let n := m * 2 ^ e.toNat
    let g := Nat.gcd n.natAbs q
    if n.natAbs ≤ H * q then some (n / g, q / g)
    else some (if n < 0 then -((H : Int) + 1) else (H : Int) + 1, 1)
  else if x.isNaN then none
  else some (if x.signBit then -((H : Int) + 1) else (H : Int) + 1, 1)

/-- The region of the search, for the numerators of absolute value at most `H`: the intervals of
`Ratpoints.Fast.sturmIntervals` with their ends as in `Ratpoints.Fast.endFrac`. -/
def region (c : List Int) (d H depth : Nat) :
    Option (Array (Option (Int × Nat) × Option (Int × Nat))) :=
  (sturmIntervals c d H depth).map (·.map fun iv ↦ (endFrac H iv.1, endFrac H iv.2))

/-! ### The denominators -/

/-- Whether `k` is a square. -/
def isSquare (k : Nat) : Bool := k.sqrt * k.sqrt == k

/-- The Jacobi symbol `(a / n)` times `s` for odd `n`, by Euclid's algorithm in at most `fuel`
steps: the factors `2` of `a` are taken out with the sign of `(2 / n)`, and for odd `a` the
symbol becomes `(n % a / a)` with the sign of the reciprocity. The value is `0` when `a` and `n`
have a common factor, and also when the steps run out, which they do not for `n < 2 ^ 64` and
`fuel = 256`; only the value `-1` is used (`Ratpoints.Fast.forbiddenDens`). -/
def jacobiNatAux : Nat → Nat → Nat → Int → Int
  | 0, _, _, _ => 0
  | fuel + 1, a, n, s =>
    if a == 0 then (if n == 1 then s else 0)
    else if a % 2 == 0 then
      jacobiNatAux fuel (a / 2) n (if n % 8 == 3 || n % 8 == 5 then -s else s)
    else jacobiNatAux fuel (n % a) a (if a % 4 == 3 && n % 4 == 3 then -s else s)

/-- The Jacobi symbol `(a / n)` for odd `n` (`Ratpoints.Fast.jacobiNatAux`), or `0`. -/
def jacobiNat (a n : Nat) : Int := jacobiNatAux 256 (a % n) n 1

/-- `a` with the bytes `j, j + n, j + 2 n, …` up to `hi` set to `1`. -/
def markMultiples (a : ByteArray) (n j hi : Nat) : ByteArray :=
  if j ≤ hi ∧ 0 < n then markMultiples (a.set! j 1) n (j + n) hi else a
termination_by hi + 1 - j

/-- The loop of `Ratpoints.Fast.forbiddenDens` over the odd numbers from `p` to `hi`, with the odd
composites marked in `comp` and the forbidden denominators in `forb` so far: an unmarked `p` is a
prime, whose odd multiples from `p ^ 2` on are marked composite, and whose multiples are marked
forbidden when `(lc / p) = -1`. -/
def forbiddenDensFrom (lc : Int) (hi : Nat) (comp forb : ByteArray) (p : Nat) : ByteArray :=
  if p ≤ hi then
    if comp.get! p != 0 then forbiddenDensFrom lc hi comp forb (p + 2)
    else
      let comp := markMultiples comp (2 * p) (p * p) hi
      let r := (lc % (p : Int)).toNat
      let forb := if r != 0 && jacobiNat r p == -1 then markMultiples forb p p hi else forb
      forbiddenDensFrom lc hi comp forb (p + 2)
  else forb
termination_by hi + 1 - p

/-- The denominators up to `hi` that no point of a curve of even degree with the leading
coefficient `lc` can have, marked `1`: the multiples of an odd `p` with `(lc / p) = -1`
(`Ratpoints.Fast.jacobiNat`), `p` running over the odd primes up to `hi`, found by the sieve of
Eratosthenes along the way (which `p` are tried affects the speed only). -/
def forbiddenDens (lc : Int) (hi : Nat) : ByteArray :=
  let z : ByteArray := ⟨Array.replicate (hi + 1) 0⟩
  forbiddenDensFrom lc hi z z 3

/-- The numbers `b` from `max lo 1` to `n` with `m[b] = v`, in ascending order, before `acc`. -/
def collectMarked (m : ByteArray) (v : UInt8) (lo : Nat) : Nat → List Nat → List Nat
  | 0, acc => acc
  | b + 1, acc =>
    if b + 1 < lo then acc
    else collectMarked m v lo b (if m.get! (b + 1) == v then (b + 1) :: acc else acc)

/-- `a` with the bytes `s j ^ 2 ≤ hi` for `j` from `k` on (and `j ≤ hi`) set to `1`. -/
def markSquares (a : ByteArray) (s k hi : Nat) : ByteArray :=
  if k ≤ hi ∧ s * k * k ≤ hi then markSquares (a.set! (s * k * k) 1) s (k + 1) hi else a
termination_by hi + 1 - k

/-- The numbers `s k ^ 2 ≤ hi` with `s` dividing `n` and `k ≥ 1`, marked `1` (for `n ≥ 1`). -/
def squareDens (n hi : Nat) : ByteArray :=
  (List.range' 1 (min n hi)).foldl (fun a s ↦ if n % s == 0 then markSquares a s 1 hi else a)
    ⟨Array.replicate (hi + 1) 0⟩

/-- The denominators of the search, for the degree `d`, the height bound `H` and the range of
`bLow` and `bHigh`: those `b` with `max 1 bLow ≤ b ≤ H`, and `b ≤ bHigh` unless `bHigh < 1`; for
odd `d` only those of the form `s k ^ 2` with `s` dividing the leading coefficient
(`Ratpoints.Fast.squareDens`), for even `d` those that `Ratpoints.Fast.forbiddenDens` does not mark
(all of them when the leading coefficient is a positive square, which
`Ratpoints.Fast.forbiddenDens` would not mark); in ascending order. -/
def denominators (c : List Int) (d H : Nat) (bLow bHigh : Int) : List Nat :=
  let lo := max 1 bLow.toNat
  let hi := if bHigh < 1 then H else min H bHigh.toNat
  if d % 2 = 1 then collectMarked (squareDens (c.getD d 0).natAbs hi) 1 lo hi []
  else if 0 < c.getD d 0 && isSquare (c.getD d 0).toNat then List.range' lo (hi + 1 - lo)
  else collectMarked (forbiddenDens (c.getD d 0) hi) 0 lo hi []

/-! ### The parameters -/

/-- The moduli that the sieve may use. -/
def candidateModuli : List Nat :=
  [9, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
    101, 103, 107, 109, 113, 127]

/-- The further moduli, for the searches in which many candidates are expected to survive the
moduli of `Ratpoints.Fast.candidateModuli` (`Ratpoints.Fast.takeTables`). -/
def furtherModuli : List Nat :=
  [131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229,
    233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347,
    349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457,
    461, 463, 467, 479, 487, 491, 499, 503, 509]

/-- Settings of the choice of the parameters (for tuning; `0` for the default): they affect the
speed, and the step also the order of the points, but not which points are listed. -/
structure Tuning where
  /-- The step `G` of the numerators in a chunk. -/
  G : Nat := 0
  /-- The largest chunk length. -/
  L : Nat := 0
  /-- The largest product of the moduli of a family. -/
  Mmax : Nat := 0
  /-- The weight `κ` of `Ratpoints.Fast.takeTables`. -/
  further : Nat := 0
  /-- The depth of the Sturm step (`Ratpoints.Fast.region`). -/
  sturm : Nat := 0
  /-- The number of families of the first stage. -/
  stage : Nat := 0

/-- `x`, or `dflt` when `x = 0`. -/
def orDefault (x dflt : Nat) : Nat := if x = 0 then dflt else x

/-- The tables of the moduli `m` of `ms`, taken in turn while `m ≤ κ E`, `E` the expected number
of candidates that survive the moduli taken so far (each taken modulus keeps the share of them
given by the density of its table): a modulus pays for its table only while candidates are left
for it to remove. -/
def takeTables (c : List Int) (d κ : Nat) : List Nat → Nat → List Table
  | [], _ => []
  | m :: ms, E =>
    if m ≤ κ * E then
      let T := mkTable c d m
      T :: takeTables c d κ ms (E * T.density / 1000)
    else []

/-- The tables grouped into families, in their order: each family takes moduli while their
product stays at most `Mmax`. -/
def groupTables (Mmax : Nat) : List Table → List (List Table)
  | [] => []
  | t :: ts =>
    match groupTables Mmax ts with
    | g :: gs => if t.m * g.foldl (· * ·.m) 1 ≤ Mmax then (t :: g) :: gs else [t] :: g :: gs
    | [] => [[t]]

/-! ### The reversal -/

/-- The coefficients to search with and whether they are reversed: the reversed coefficients when
the reversal check of `ratpoints` (`Ratpoints.Setup.reversal`) reverses them and no range of the
denominators restricts the search (`bLow ≤ 1`, and `bHigh < 1` or `H ≤ bHigh`); otherwise, the
refusal of the check included, `c` itself. -/
def reversed (c : List Int) (H : Nat) (bLow bHigh : Int) : List Int × Bool :=
  if bLow ≤ 1 ∧ (bHigh < 1 ∨ (H : Int) ≤ bHigh) then
    match Setup.reversal true c (BruteForce.degree c) with
    | .ok (c', _, true) => (c', true)
    | _ => (c, false)
  else (c, false)

end Fast

end Ratpoints

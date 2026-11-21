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

`Ratpoints.FastMask.fastPoints c H bLow bHigh` lists the normalized points of height at most `H`
on `y ^ 2 = F(x, z)` whose denominator `z` lies in the range of `bLow` and `bHigh` (the points at
infinity always), each once, in an order of its own: only such points in any case, and all of them
assuming Sturm's theorem, on which the region of the numerators rests.

* Each class of the numerators modulo the step `G` is searched in chunks
  (`Ratpoints.FastMask.Slot`), for the denominators whose residue modulo `G` allows a point in
  the class. A chunk is a bit mask with one bit per numerator, in whole blocks of `128` bytes
  where it is long enough for that; the bits beyond its numerators are left to themselves and
  dropped among the survivors.
* The first stage ANDs the mask with the rows of families of moduli
  (`Ratpoints.FastMask.Family`): the row of a family for the residue of the denominator `b` has
  the bit of a numerator set when its residue and that of `b` allow a point modulo every modulus
  of the family. The row of the first family is copied into the mask, at the byte offset that
  aligns it with the chunk (`Ratpoints.FastMask.Family.shift`), and the rows of the other families
  are ANDed to it by one call of the primitive `Ratpoints.Mask.andRows`
  (`Ratpoints.FastMask.sieveChunk`). The buffer of the mask is handed from call to call.
* The survivors, which the primitive `Ratpoints.Mask.nextSet` lists, are tested modulo the
  further moduli one by one, by a look-up in their tables (`Ratpoints.FastMask.passes`), then for
  the coprimality of numerator and denominator, and those that are left go to the exact check of
  the brute force, `Ratpoints.BruteForce.pointsOfDen` (`Ratpoints.FastMask.survivorPoints`).
* The denominators are the outer loop: the rows of one denominator serve all its chunks, each cut
  to the blocks that hold its numerators in the region (`Ratpoints.FastMask.regionChunks`,
  `Ratpoints.FastMask.cutChunks`).
* The step, the families and the split into the two stages are chosen by estimates of their cost
  (`Ratpoints.FastMask.choose`, with `Ratpoints.FastMask.chooseStep` and
  `Ratpoints.FastMask.stageOne`).

## Main definitions

* `Ratpoints.FastMask.fastPoints`: the points, by the sieve on byte-array masks.
-/

@[expose] public section

namespace Ratpoints

namespace FastMask

open BruteForce Fast

/-! ### The rows of a table -/

/-- `a` repeated `2 ^ k` times. -/
def repeatBytes (a : ByteArray) : Nat → ByteArray
  | 0 => a
  | k + 1 => let r := repeatBytes a k; r ++ r

/-- `n` bytes of the bits `tab[i], tab[i + g], tab[i + 2 g], …` (the indices modulo `m`, for
`i, g < m`; the entries of `tab` are `0` or `1`), pushed to `acc`. -/
def stepBytes (tab : ByteArray) (m g : Nat) : Nat → Nat → ByteArray → ByteArray
  | 0, _, acc => acc
  | n + 1, i, acc =>
    let i₁ := if i + g < m then i + g else i + g - m
    let i₂ := if i₁ + g < m then i₁ + g else i₁ + g - m
    let i₃ := if i₂ + g < m then i₂ + g else i₂ + g - m
    let i₄ := if i₃ + g < m then i₃ + g else i₃ + g - m
    let i₅ := if i₄ + g < m then i₄ + g else i₄ + g - m
    let i₆ := if i₅ + g < m then i₅ + g else i₅ + g - m
    let i₇ := if i₆ + g < m then i₆ + g else i₆ + g - m
    stepBytes tab m g n (if i₇ + g < m then i₇ + g else i₇ + g - m)
      (acc.push (tab.get! i ||| tab.get! i₁ <<< 1 ||| tab.get! i₂ <<< 2 ||| tab.get! i₃ <<< 3 |||
        tab.get! i₄ <<< 4 ||| tab.get! i₅ <<< 5 ||| tab.get! i₆ <<< 6 ||| tab.get! i₇ <<< 7))

/-- `n` bytes of the bits of the mask `p` from the bit positions `o, o + 8, o + 16, …` on, the
positions reduced modulo `m`, pushed to `acc`: each byte holds the bits `o, …, o + 7` of `p`. -/
def windowBytes (p : ByteArray) (m : Nat) : Nat → Nat → ByteArray → ByteArray
  | 0, _, acc => acc
  | n + 1, o, acc =>
    windowBytes p m n ((o + 8) % m)
      (acc.push (((p.get! (o / 8)).toUInt16 ||| (p.get! (o / 8 + 1)).toUInt16 <<< 8) >>>
        (o % 8).toUInt16).toUInt8)

/-- The row of the table `T` for the residue `r` of the denominator, for the numerators
`0, G, 2G, …`, as a mask of `nb` bytes: bit `j` is set when the residues of `G j` and `r` allow a
point. The first `8 (T.m / 8 + 2)` bits come from `Ratpoints.FastMask.stepBytes`, the `T.m` bytes of
a period from their windows (`Ratpoints.FastMask.windowBytes`), and the row from repeating the
period. -/
def baseRow (T : Table) (G nb r : Nat) : ByteArray :=
  let s := T.sing[r]!
  let k := T.m / 8 + 2
  let bits := if s.size == 0 then stepBytes T.one T.m (G * T.inv[r]! % T.m) k 0
      (ByteArray.emptyWithCapacity k)
    else stepBytes s T.m (G % T.m) k 0 (ByteArray.emptyWithCapacity k)
  let period := windowBytes bits T.m T.m 0 (ByteArray.emptyWithCapacity T.m)
  (repeatBytes period (Nat.log2 (nb / T.m) + 1)).extract 0 nb

/-! ### Families of moduli -/

/-- A family of moduli with the odd product `M`: an inverse `ginv` of the step modulo `M` and the
rows for the residues `r < M` of the denominator, as masks for the numerators `0, G, 2G, …`; a row
without a set bit is the empty array. -/
structure Family where
  /-- The product of the moduli. -/
  M : Nat
  /-- An inverse of the step `G` modulo `M`. -/
  ginv : Nat
  /-- The rows, for the residues `0, …, M - 1` of the denominator. -/
  rows : Array ByteArray

/-- The family of the tables `ts`, for the step `G` and masks of at most `nb` bytes, with rows of
`M + nb` bytes, `M` the product of the moduli, enough for a mask at every byte offset below `M`;
`none` when `M` is even or `G` has no inverse modulo `M`. The row of a residue is the AND of the
rows of the tables (`Ratpoints.FastMask.baseRow`). -/
def mkFamily (G nb : Nat) (ts : List Table) : Option Family :=
  match ts with
  | [] => none
  | T :: rest =>
    let M := ts.foldl (· * ·.m) 1
    if M % 2 = 1 then
      match (List.range M).find? fun u ↦ G * u % M == 1 % M with
      | none => none
      | some ginv =>
        let first := (List.range T.m).toArray.map (baseRow T G (M + nb))
        let others := rest.toArray.map fun T' ↦
          (T'.m, (List.range T'.m).toArray.map (baseRow T' G (M + nb)))
        let zeros := others.map fun _ ↦ 0
        some { M, ginv, rows := (List.range M).toArray.map fun r ↦
          let x := Mask.andRows first[r % T.m]! (others.map fun (m, B) ↦ B[r % m]!) zeros 0
          if Mask.isZero x then .empty else x }
    else none

/-- The family without a modulus: one row, with every bit set. -/
def trivialFamily (nb : Nat) : Family :=
  { M := 1, ginv := 0, rows := #[⟨Array.replicate (nb + 1) 255⟩] }

/-- The shift that aligns the rows of the family `F` with a chunk starting at the numerator `a₀`:
`s < 8 F.M` with `G s ≡ a₀` modulo `F.M`, the least one plus the multiple of `F.M` that makes it
a multiple of `8` (`F.M` is odd, so that `F.M ^ 2 ≡ 1` modulo `8`). -/
def Family.shift (F : Family) (a₀ : Int) : Nat :=
  let s := (a₀ * F.ginv % (F.M : Int)).toNat
  s + F.M * ((8 - s % 8) * F.M % 8)

/-! ### The chunks -/

/-- A chunk of the search: the `len` numerators `-H + ρ + G (T₀ + t)` for `t < len`, with a mask
of `nb` bytes (`len ≤ 8 nb`), the byte offset `sh₀` of the row of the first family and the shifts
`sh` of the rows of the other families of the first stage. -/
structure Slot where
  /-- The residue of `a + H` modulo `G` for the numerators `a` of the chunk. -/
  ρ : Nat
  /-- The index of the first numerator in its class. -/
  T₀ : Nat
  /-- The number of numerators. -/
  len : Nat
  /-- The size of the mask, in bytes. -/
  nb : Nat
  /-- The byte offset of the row of the first family. -/
  sh₀ : Nat
  /-- The shifts of the rows of the other families. -/
  sh : Array Nat

/-- An end of an interval of the region, rounded to a multiple of `2 ^ (-k)`: the value
`± n / 2 ^ k`. -/
structure End where
  /-- Whether the value is negative. -/
  neg : Bool
  /-- The numerator of the absolute value. -/
  n : Nat

/-- The data of a search that does not depend on the denominator. -/
structure Context where
  /-- The coefficients. -/
  c : List Int
  /-- The degree. -/
  d : Nat
  /-- The height bound. -/
  H : Nat
  /-- The step. -/
  G : Nat
  /-- The first family, whose rows start the masks. -/
  fam₀ : Family
  /-- The other families of the first stage. -/
  fams : Array Family
  /-- The tables of the second stage, each with `(-H) % m`. -/
  tabs : Array (Table × Nat)
  /-- The exponent of the denominator of the ends of the region. -/
  k : Nat
  /-- The region: intervals with rounded ends, `none` for no restriction. -/
  reg : Option (Array (End × End))
  /-- The chunks of the classes that each residue of the denominator modulo `G` allows. -/
  slots : Array (List Slot)

/-! ### The second stage and the exact check -/

/-- Whether the numerator `x - H` and the denominator `b` allow a point modulo every modulus of
`tabs`. -/
def passes (tabs : Array (Table × Nat)) (x b : Nat) : Bool :=
  tabs.all fun (T, o) ↦ T.admits ((x + o) % T.m) (b % T.m)

/-- The exact check of one numerator: `Ratpoints.BruteForce.pointsOfDen c d b [a]`, kept out of
line so that none of its work is done before a candidate has passed the second stage. -/
@[noinline] def exactPoints (c : List Int) (d b : Nat) (a : Int) : List (Int × Int × Int) :=
  BruteForce.pointsOfDen c d b [a]

/-- The points with the denominator `b` whose numerator `a` has its index `a + H` among the
`x₀ + G t` for the bit positions `t < lim` of `ts`, added to `pts`: the candidates that pass the
second stage and are coprime to `b` go to the exact check. -/
def survivorPoints (ctx : Context) (b x₀ lim : Nat) (ts : List Nat)
    (pts : List (Int × Int × Int)) : List (Int × Int × Int) :=
  ts.foldl (fun pts t ↦
    if t < lim && passes ctx.tabs (x₀ + ctx.G * t) b &&
        natGcd (((x₀ + ctx.G * t : Nat) : Int) - ctx.H).natAbs b == 1 then
      exactPoints ctx.c ctx.d b (((x₀ + ctx.G * t : Nat) : Int) - ctx.H) ++ pts
    else pts) pts

/-! ### The first stage -/

/-- The chunk `sl` of the denominator `b` from the byte `o` of its mask to the byte `e`, with the
row `r₀` of `b` in the first family and its rows `rs` in the others: the mask is the bytes of `r₀`
from the offset of the chunk on, copied into the buffer `buf`, ANDed with the rows; the
candidates that are left go on to `Ratpoints.FastMask.survivorPoints`. The buffer is returned for
the next chunk when no candidate is left. -/
@[inline] def sieveChunk (ctx : Context) (b : Nat) (r₀ : ByteArray) (rs : Array ByteArray)
    (sl : Slot) (o e : Nat) (buf : ByteArray) (pts : List (Int × Int × Int)) :
    ByteArray × List (Int × Int × Int) :=
  let acc := Mask.andRows (r₀.copySlice (sl.sh₀ + o) buf 0 (e - o)) rs sl.sh (8 * o)
  if acc.size == 0 then (acc, pts)
  else (.empty, survivorPoints ctx b (sl.ρ + ctx.G * (sl.T₀ + 8 * o)) (sl.len - 8 * o)
    (Mask.setBits acc) pts)

/-- The chunks `sls` of the denominator `b`, each cut to the blocks of its mask (of `128` bytes,
or of `8` bytes for a mask that is not made of whole blocks) that hold the numerators `a` with
`q₁ G + r₁ ≤ a + H ≤ q₂ G + r₂`. -/
def cutChunks (ctx : Context) (b : Nat) (r₀ : ByteArray) (rs : Array ByteArray)
    (q₁ r₁ q₂ r₂ : Nat) : List Slot → ByteArray → List (Int × Int × Int) →
    ByteArray × List (Int × Int × Int)
  | [], buf, pts => (buf, pts)
  | sl :: sls, buf, pts =>
    -- the positions `t` of the chunk with `t₁ ≤ t < t₂`
    let t₁ := (if sl.ρ < r₁ then q₁ + 1 else q₁) - sl.T₀
    let t₂ := min sl.len ((if r₂ < sl.ρ then q₂ else q₂ + 1) - sl.T₀)
    if t₁ < t₂ then
      let u := if sl.nb % 128 == 0 then 128 else 8
      let st := sieveChunk ctx b r₀ rs sl (u * (t₁ / (8 * u)))
        (min sl.nb (u * ((t₂ - 1) / (8 * u) + 1))) buf pts
      cutChunks ctx b r₀ rs q₁ r₁ q₂ r₂ sls st.1 st.2
    else cutChunks ctx b r₀ rs q₁ r₁ q₂ r₂ sls buf pts

/-- The chunks of the denominator `b`, cut to the hull of its numerators in the intervals `reg`
from position `i` on and the hull so far, the indices `a + H` from `lo` to `hi` (none when
`hi < lo`): for an interval with the ends `± n / 2 ^ k`, the indices from `H + ⌈b l⌉` to
`H + ⌊b u⌋`, clipped to `0, …, 2 H`. -/
def regionChunks (ctx : Context) (b : Nat) (r₀ : ByteArray) (rs : Array ByteArray)
    (reg : Array (End × End)) (i lo hi : Nat) (buf : ByteArray) (pts : List (Int × Int × Int)) :
    ByteArray × List (Int × Int × Int) :=
  if h : i < reg.size then
    let l := reg[i].1
    let u := reg[i].2
    let x₁ := if l.neg then ctx.H - (b * l.n) >>> ctx.k
      else ctx.H + (b * l.n + 2 ^ ctx.k - 1) >>> ctx.k
    -- one more than the last index
    let x₂ := if u.neg then ctx.H + 1 - (b * u.n + 2 ^ ctx.k - 1) >>> ctx.k
      else min (2 * ctx.H) (ctx.H + (b * u.n) >>> ctx.k) + 1
    if x₁ < x₂ then regionChunks ctx b r₀ rs reg (i + 1) (min lo x₁) (max hi (x₂ - 1)) buf pts
    else regionChunks ctx b r₀ rs reg (i + 1) lo hi buf pts
  else if hi < lo then (buf, pts)
  else cutChunks ctx b r₀ rs (lo / ctx.G) (lo % ctx.G) (hi / ctx.G) (hi % ctx.G)
    ctx.slots[b % ctx.G]! buf pts
termination_by reg.size - i

/-- The rows of the denominator `b` in the families from position `i` on, pushed to `acc`; `none`
when one of them is empty. -/
def rowsOf (fams : Array Family) (b : Nat) (i : Nat) (acc : Array ByteArray) :
    Option (Array ByteArray) :=
  if h : i < fams.size then
    let r := fams[i].rows[b % fams[i].M]!
    if r.size == 0 then none else rowsOf fams b (i + 1) (acc.push r)
  else some acc
termination_by fams.size - i

/-- The chunks of the denominator `b`: none when a row of `b` is empty, since no numerator then
allows a point. -/
def denStep (ctx : Context) (b : Nat) (buf : ByteArray) (pts : List (Int × Int × Int)) :
    ByteArray × List (Int × Int × Int) :=
  let r₀ := ctx.fam₀.rows[b % ctx.fam₀.M]!
  if r₀.size == 0 then (buf, pts) else
  match rowsOf ctx.fams b 0 (Array.emptyWithCapacity ctx.fams.size) with
  | none => (buf, pts)
  | some rs =>
    match ctx.reg with
    | none => cutChunks ctx b r₀ rs 0 0 (2 * ctx.H / ctx.G) (2 * ctx.H % ctx.G)
        ctx.slots[b % ctx.G]! buf pts
    | some reg => regionChunks ctx b r₀ rs reg 0 (2 * ctx.H + 1) 0 buf pts

/-- The denominators `bs` in turn. -/
def densLoop (ctx : Context) : List Nat → ByteArray → List (Int × Int × Int) →
    List (Int × Int × Int)
  | [], _, pts => pts
  | b :: bs, buf, pts =>
    let st := denStep ctx b buf pts
    densLoop ctx bs st.1 st.2

/-! ### The search -/

/-- An end of the region rounded down (`up = false`) or up to a multiple of `2 ^ (-k)`, or `dflt`
without an end. -/
def roundEnd (k : Nat) (up : Bool) (e : Option (Int × Nat)) (dflt : End) : End :=
  match e with
  | none => dflt
  | some (n, q) =>
    -- towards zero exactly when the direction and the sign disagree
    if (n < 0) == up then { neg := n < 0, n := n.natAbs * 2 ^ k / q }
    else { neg := n < 0, n := (n.natAbs * 2 ^ k + q - 1) / q }

/-- The size in bytes of the mask of a chunk of `len` numerators: whole blocks of `128` bytes from
`256` numerators on, else whole 64-bit words. -/
def maskBytes (len : Nat) : Nat :=
  if 256 ≤ len then 128 * ((len + 1023) / 1024) else 8 * ((len + 63) / 64)

/-- The chunks of the class `ρ`, with their shifts for the first family `fam₀` and the others. -/
def slotsOf (H G L : Nat) (fam₀ : Family) (fams : Array Family) (ρ : Nat) : List Slot :=
  (chunks (classCount (2 * H + 1) G ρ) L).map fun (T₀, len) ↦
    { ρ, T₀, len, nb := maskBytes len,
      sh₀ := fam₀.shift (((ρ + G * T₀ : Nat) : Int) - H) / 8,
      sh := fams.map (Family.shift · (((ρ + G * T₀ : Nat) : Int) - H)) }

/-- The families of the first stage, for the step `G` and masks of at most `nb` bytes: those of
the groups `g₁` of tables (`Ratpoints.FastMask.mkFamily`), the first one, whose rows start the
masks, and the others; the family without a modulus when no group gives a family. -/
def stageFamilies (G nb : Nat) (g₁ : List (List Table)) : Family × Array Family :=
  match g₁.filterMap (mkFamily G nb) with
  | [] => (trivialFamily nb, #[])
  | F :: Fs => (F, Fs.toArray)

/-- For each residue `g` of the denominator modulo `G`, the chunks, of at most `L` numerators and
with their shifts for the families, of the classes that `g` allows: the classes `ρ` of `a + H`
modulo `G` whose numerators `a` allow a point modulo `G` together with `g`
(`Ratpoints.Fast.admitRow`). -/
def classSlots (c : List Int) (d H G L : Nat) (fam₀ : Family) (fams : Array Family) :
    Array (List Slot) :=
  let sq := sqTable G
  (List.range G).toArray.map fun g ↦
    let row := admitRow c d G sq g
    (List.range G).flatMap fun (ρ : Nat) ↦
      if row[(((ρ : Int) - H) % (G : Int)).toNat]! then slotsOf H G L fam₀ fams ρ else []

/-- The data of the search with the step `G`, chunks of at most `L` numerators, the families of
the groups `g₁` of tables in the first stage (`Ratpoints.FastMask.stageFamilies`), the tables `t₂`
in the second and the region `reg`. The ends of the region are rounded to multiples of `2 ^ (-k)`
with `H ^ 2 * 2 ^ k < 2 ^ 62`, which keeps the products with a denominator small. -/
def searchContext (c : List Int) (d H G L : Nat) (g₁ : List (List Table)) (t₂ : List Table)
    (reg : Option (Array (Option (Int × Nat) × Option (Int × Nat)))) : Context :=
  let fs := stageFamilies G (maskBytes L) g₁
  let k := 62 - 2 * (Nat.log2 H + 1)
  { c, d, H, G, k, fam₀ := fs.1, fams := fs.2
    tabs := t₂.toArray.map fun T ↦ (T, (T.m - H % T.m) % T.m)
    reg := reg.map (·.map fun (lo, hi) ↦
      (roundEnd k false lo { neg := true, n := (H + 1) * 2 ^ k },
        roundEnd k true hi { neg := false, n := (H + 1) * 2 ^ k }))
    slots := classSlots c d H G L fs.1 fs.2 }

/-- The points with the denominators `dens` (all positive), by the sieve on the data of
`Ratpoints.FastMask.searchContext`: for each denominator `b`, the chunks of the classes that the
residue of `b` modulo `G` allows; a denominator whose residue allows no class is skipped. -/
def search (c : List Int) (d H G L : Nat) (g₁ : List (List Table)) (t₂ : List Table)
    (reg : Option (Array (Option (Int × Nat) × Option (Int × Nat)))) (dens : List Nat) :
    List (Int × Int × Int) :=
  let ctx := searchContext c d H G L g₁ t₂ reg
  densLoop ctx (dens.filter fun b ↦ !ctx.slots[b % G]!.isEmpty) .empty []

/-! ### The choice of the parameters -/

/-- The chunk length for the step `G`: `L₀`, but at most the number of numerators of a class
rounded up to a multiple of `64`. -/
def chunkLength (H G L₀ : Nat) : Nat := max 1 (min L₀ (64 * (((2 * H + G) / G + 63) / 64)))

/-- The work of the first stage with the step `G`: the number of its calls, one for each chunk of
each class that the residue of a denominator allows, and the size of a mask. -/
def work (c : List Int) (d H L₀ : Nat) (dens : List Nat) (G : Nat) : Nat × Nat :=
  let L := chunkLength H G L₀
  let sq := sqTable G
  let cls := (List.range G).toArray.map fun g ↦
    (admitRow c d G sq g).foldl (fun n x ↦ if x then n + 1 else n) 0
  (dens.foldl (fun n b ↦ n + cls[b % G]!) 0 * (((2 * H + G) / G + L - 1) / L), maskBytes L)

/-- The step: `16`, halved while that halves the number of calls of the first stage, which
happens when the classes that a denominator allows come in pairs `ρ, ρ + G / 2`, so that the masks
double and their number halves. -/
def chooseStep (c : List Int) (d H L₀ : Nat) (dens : List Nat) : Nat :=
  ([8, 4, 2, 1].foldl (fun (best : Nat × Nat × Bool) G ↦
    let C := (work c d H L₀ dens G).1
    if best.2.2 && 2 * C ≤ best.2.1 then (G, C, true) else (best.1, best.2.1, false))
    (16, (work c d H L₀ dens 16).1, true)).1

/-- The number of families of the first stage, by an estimate of the costs in cycles: a family
is taken while building its rows and ANDing them (with `C` calls, `blocks` blocks of the masks and
masks of `nb` bytes) costs less than the tests that it saves the second stage, with `S` candidates
expected to survive the families before it. Each group comes with the product of its moduli, the
sum of their squares, their number and the density, in thousandths. -/
def stageOne (C blocks nb : Nat) : List (Nat × Nat × Nat × Nat) → Nat → Nat
  | [], _ => 0
  | (M, sq, n, dn) :: gs, S =>
    if 25 * sq + n * M * (M + nb) / 2 + 7 * C + 6 * min blocks S <
        S * (1000 - dn) / 1000 * (300 + nb / 2) then
      stageOne C blocks nb gs (S * dn / 1000) + 1
    else 0

/-- The parameters of a search. -/
structure Choice where
  /-- The step. -/
  G : Nat
  /-- The largest number of numerators of a chunk. -/
  L : Nat
  /-- The groups of tables of the families of the first stage. -/
  stage₁ : List (List Table)
  /-- The tables of the second stage. -/
  stage₂ : List Table

/-- The parameters of the search with the denominators `dens`, under the settings `tu`: the step
(`Ratpoints.FastMask.chooseStep`) and the chunk length (`Ratpoints.FastMask.chunkLength`); the
tables are those of the moduli prime to the step that the expected number of candidates pays for
(`Ratpoints.Fast.takeTables`, from the bits of all masks; `Ratpoints.FastMask.mkFamily` gives no
family for a modulus that shares a factor with the step), grouped into families
(`Ratpoints.Fast.groupTables`), of which the first stage takes those that
`Ratpoints.FastMask.stageOne` says, the most selective first; the second stage takes the others, and
the table of `16` when the step is not a multiple of it. -/
def choose (c : List Int) (d H : Nat) (dens : List Nat) (tu : Tuning) : Choice :=
  let L₀ := orDefault tu.L 16384
  let G := if tu.G = 0 then chooseStep c d H L₀ dens else tu.G
  let w := work c d H L₀ dens G
  let C := w.1
  let nb := w.2
  let W := C * 8 * nb
  let tabs := takeTables c d (orDefault tu.further 16)
    ((candidateModuli ++ furtherModuli).filter fun m ↦ Nat.gcd m G == 1) W
  let Mmax := orDefault tu.Mmax (max 15 (min 1500 (Nat.sqrt (C * (7 + nb / 20)))))
  let groups := (groupTables Mmax tabs).map fun g ↦
    (g, g.foldl (fun s T ↦ s * T.density / 1000) 1000)
  let k₁ := if tu.stage = 0 then
      max 1 (stageOne C (C * nb / 128) nb (groups.map fun (g, dn) ↦
        (g.foldl (· * ·.m) 1, g.foldl (fun s T ↦ s + T.m * T.m) 0, g.length, dn)) W)
    else tu.stage
  { G, L := chunkLength H G L₀
    stage₁ := ((groups.take k₁).mergeSort fun x y ↦ x.2 ≤ y.2).map (·.1)
    stage₂ := (if G % 16 = 0 then [] else [mkTable c d 16]) ++ (groups.drop k₁).flatMap (·.1) }

/-- The points of height at most `H` with their denominator in the range of `bLow` and `bHigh`,
each once, of the sieve on `c` itself: the points at infinity, then those that the search with
the parameters of `Ratpoints.FastMask.choose` finds (only such points in any case, and all of them
assuming Sturm's theorem, on which the region of the numerators rests). -/
def sievePoints (c : List Int) (H : Nat) (bLow bHigh : Int) (tu : Tuning := {}) :
    List (Int × Int × Int) :=
  let d := BruteForce.degree c
  let dens := denominators c d H bLow bHigh
  let P := choose c d H dens tu
  (if 1 ≤ H then BruteForce.pointsOfDen c d 0 [1] else []) ++
    search c d H P.G P.L P.stage₁ P.stage₂ (region c d H (orDefault tu.sturm 10)) dens

/-- The normalized points of height at most `H` on `y ^ 2 = F(x, z)` whose denominator `z` is `0`
or lies in the range of `bLow` and `bHigh` (`bLow ≤ z`, and `z ≤ bHigh` unless `bHigh < 1`), each
once: those of `Ratpoints.FastMask.sievePoints`, on the coefficients reversed as `ratpoints`
reverses them when no range of the denominators is given (`Ratpoints.Fast.reversed`; the binary
form with `x` and `z` exchanged), with the points mapped back by `Ratpoints.Sieve.swapPoint` (only
such points in any case, and all of them assuming Sturm's theorem, on which the region of the
numerators rests). -/
def fastPoints (c : List Int) (H : Nat) (bLow bHigh : Int) (tu : Tuning := {}) :
    List (Int × Int × Int) :=
  match reversed c H bLow bHigh with
  | (c', true) => (sievePoints c' H 1 0 tu).map Sieve.swapPoint
  | _ => sievePoints c H bLow bHigh tu

end FastMask

end Ratpoints

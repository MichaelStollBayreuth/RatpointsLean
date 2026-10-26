/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.Costs
public import Ratpoints.Model.Params

-- The `#guard` examples run code of the imported modules at compile time.
meta import Ratpoints.Model.Denominators
meta import Ratpoints.Model.Params

/-!
# The blocks of the run and the correction of the moduli

The loop over the denominators of `find_points_work_1`, in blocks, on the calling thread: the steps
of the shape of the run (`Ratpoints.Sieve.Shape`), the `k` of the squares `k ^ 2`, the `k` of each
divisor `s` of the divisor shape, one segment of steps per divisor, the words of 64 denominators, or
the denominators themselves, are cut into blocks of consecutive steps of one length
(`Ratpoints.Sieve.Shape.segments`, `Ratpoints.Sieve.Shape.blockPlan`), about
`Ratpoints.blocksWanted` blocks of at least `Ratpoints.blockMin` steps, the steps of a block found
from the segment that holds it (`Ratpoints.Sieve.BlockPlan.steps`); the loop of each shape goes over
the steps of a block (`Ratpoints.Sieve.Shape.blockLoop`), its denominators in the order of the loop,
each that passes the tests of the shape handed to a step, which sifts it
(`Ratpoints.Sieve.siftDen`), and returns when the callback has stopped the search; each block is
sifted as a whole, with the moduli of the decision of the correction of the moduli in force for it
(`Ratpoints.Sieve.findDecision`), its counters from zero, and reports its counters and that decision
(`Ratpoints.Sieve.runBlock`). The counters of the blocks are added to those of the run
(`Ratpoints.Sieve.RunCounts`, `Ratpoints.Sieve.runFold`), from which the search corrects its choice
of the end of the second stage and of the third stage once the run has swept enough words
(`Ratpoints.Sieve.adaptPrimes`): a decision made at the fold of block `j` is for the blocks from
`j + Ratpoints.adaptLag + 1` on (`Ratpoints.Sieve.Decision`, `Ratpoints.Sieve.Correction`). The run
sifts the blocks in turn, each folded after it, and returns the ends of the second and the third
stage of the last block folded, which the search reports as used (`Ratpoints.Sieve.sieveRun`). The
pool of threads that ratpoints may sieve the blocks with is not modelled: with it, the blocks are
sifted apart and delivered in their order, and the decision of a block is the same, since it depends
only on the folds of the blocks at least `Ratpoints.adaptLag + 1` before it.

## Main definitions

* `Ratpoints.Sieve.Shape.segments`, `Ratpoints.Sieve.BlockPlan`, `Ratpoints.Sieve.blockLength`,
  `Ratpoints.Sieve.Shape.blockPlan`, `Ratpoints.Sieve.BlockPlan.steps`: the segments of steps of the
  shape of the run, the length of the blocks, the first block of each segment, and the steps of a
  block.
* `Ratpoints.Sieve.squaresBlock`, `Ratpoints.Sieve.squares1Block`, `Ratpoints.Sieve.wordsBlock`,
  `Ratpoints.Sieve.allBlock`, with `Ratpoints.Sieve.forbStarts`, `Ratpoints.Sieve.denWord` and
  `Ratpoints.Sieve.walkDens`: the loops of the four shapes over the steps of a block, and their
  dispatch `Ratpoints.Sieve.Shape.blockLoop`.
* `Ratpoints.Sieve.siftDen`: one denominator of a block sifted.
* `Ratpoints.Sieve.Decision`, `Ratpoints.Sieve.findDecision`, `Ratpoints.Sieve.BlockStat`,
  `Ratpoints.Sieve.runBlock`: the decisions of the correction, the one in force for a block, and
  the sieve of one block with what it reports.
* `Ratpoints.Sieve.adaptRates`, `Ratpoints.Sieve.adaptUp`, `Ratpoints.Sieve.adaptDown`,
  `Ratpoints.Sieve.adaptSecond`, `Ratpoints.Sieve.adaptThird`, `Ratpoints.Sieve.adaptPrimes`: the
  correction of the end of the second stage and of the third stage from the counters of the run.
* `Ratpoints.Sieve.RunCounts`, `Ratpoints.Sieve.Correction`, `Ratpoints.Sieve.RunCounts.fold`,
  `Ratpoints.Sieve.Correction.start`, `Ratpoints.Sieve.runFold`: the counters of the run, the state
  of the correction, its start, and the fold of a block into them.
* `Ratpoints.Sieve.sieveRun`: the blocks of the run, sifted in turn, each folded after it, and the
  ends of the second and the third stage of the last block folded.
-/

@[expose] public section

namespace Ratpoints

namespace Sieve

/-! ### The blocks -/

/-- The segments of steps of the shape `s` for the denominators `bLow, …, bHigh`, each from its
first step `lo` to its last `hi`, both included, and the number of the steps of all of them: the
`k` with `bLow ≤ k ^ 2 ≤ bHigh` for the squares, from `⌈√bLow⌉` to `⌊√bHigh⌋`
(`Ratpoints.Sieve.ceilSqrt`, `Ratpoints.Sieve.floorSqrt`); for each divisor `s` of the divisor
shape in turn, a segment of its own, the `k` with `bLow ≤ s k ^ 2 ≤ bHigh`, from
`⌈√(⌊(bLow - 1) / s⌋ + 1)⌉` to `⌊√⌊bHigh / s⌋⌋`; the words `⌊bLow / 64⌋` to `⌊bHigh / 64⌋` of 64
denominators for the word shape; and `bLow, …, bHigh` otherwise. A segment with `hi < lo` has no
steps.

C: `find_points.c:3812-3837`

Deviation: the segments as an array of pairs, for the arrays `seg_lo` and `seg_hi` of the run;
quotients by 64 for the shifts by `LONG_SHIFT`; natural numbers for the `long`s, the steps of a
segment counted only when `lo ≤ hi`, as the C code counts them; the count of the segments read from
the shape, for `nseg`, which `run_setup` counts before (line 3794). -/
def Shape.segments (s : Shape) (bLow bHigh : Nat) : Id (Array (Nat × Nat) × Nat) := do
  let nseg := match s with
    | .squares1 _ divisors => divisors.length
    | _ => 1
  let mut segs := #[]
  let mut steps := 0
  for n in [0:nseg] do
    let (lo, hi) := match s with
      | .squares => (ceilSqrt bLow, floorSqrt bHigh)
      | .squares1 _ divisors =>
        let dv := divisors[n]!
        (ceilSqrt ((bLow - 1) / dv + 1), floorSqrt (bHigh / dv))
      | .words .. => (bLow / 64, bHigh / 64)
      | .all => (bLow, bHigh)
    segs := segs.push (lo, hi)
    if lo ≤ hi then steps := steps + (hi - lo) + 1
  return (segs, steps)

/-- The blocks of a run: its segments of steps, each from its first step to its last
(`Ratpoints.Sieve.Shape.segments`), the length of the blocks (`Ratpoints.Sieve.blockLength`), and
the first block of each segment, with the number of the blocks at the end
(`Ratpoints.Sieve.Shape.blockPlan`): segment `s` holds the blocks from `segBlock[s]` to
`segBlock[s + 1] - 1`, the last of them possibly shorter.

C: `find_points.c:3750-3754`

Deviation: the segments as an array of pairs, for the pointers `seg_lo` and `seg_hi`; the first
blocks with the number of the blocks at the end of the array, for `seg_block` and `nblocks`, which
the C code keeps apart with the same value; no count `nseg` of the segments, an array having its
size; natural numbers for the `long`s. -/
structure BlockPlan where
  /-- The segments, each from its first step to its last. -/
  segs : Array (Nat × Nat)
  /-- The length of the blocks, in steps. -/
  len : Nat
  /-- The first block of each segment, and at the end the number of the blocks. -/
  segBlock : Array Nat

/-- The number of the blocks of the run. -/
def BlockPlan.nblocks (plan : BlockPlan) : Nat := plan.segBlock.back!

/-- The length of the blocks of a run of `steps` steps: `steps / Ratpoints.blocksWanted + 1`, at
least `Ratpoints.blockMin`, and the fixed length of `Ratpoints.blockLen` when the build sets one.

C: `find_points.c:3838-3842`

Deviation: the conditional compilation `#ifdef RP_BLOCK_LEN` a constant of type `Option Nat`
(`Ratpoints.blockLen`), none in the default build. -/
def blockLength (steps : Nat) : Nat :=
  let len := steps / blocksWanted + 1
  let len := if len < blockMin then blockMin else len
  blockLen.getD len

/-- The blocks of the run of the shape `s` for the denominators `bLow, …, bHigh`: its segments
(`Ratpoints.Sieve.Shape.segments`), the length of the blocks for the number of its steps
(`Ratpoints.Sieve.blockLength`), and the first block of each segment, each segment with steps
holding `⌊(hi - lo) / len⌋ + 1` blocks, with the number of the blocks at the end.

C: `find_points.c:3843-3850`

Deviation: the blocks returned as a structure (`Ratpoints.Sieve.BlockPlan`), for the fields of the
run that `run_setup` fills; natural numbers for the `long`s. -/
def Shape.blockPlan (s : Shape) (bLow bHigh : Nat) : Id BlockPlan := do
  let (segs, steps) ← s.segments bLow bHigh
  let len := blockLength steps
  let mut n := 0
  let mut segBlock := #[]
  for (lo, hi) in segs do
    segBlock := segBlock.push n
    if lo ≤ hi then n := n + (hi - lo) / len + 1
  return ⟨segs, len, segBlock.push n⟩

/-- The steps of block `i < plan.nblocks` of the run with the blocks `plan`: the segment `seg` that
holds it, the first with `i < segBlock[seg + 1]`, and its first and last steps `a` and `e`, the
block being the `(i - segBlock[seg])`-th of its segment, of `len` steps or up to the end of the
segment.

C: `find_points.c:3900-3904`

Deviation: the segment and the steps returned, for the locals of `run_block`; natural numbers for
the `long`s, the difference `hi - a` truncated at `0`, where the C code compares a `long` that is
not negative for a block of the run. -/
def BlockPlan.steps (plan : BlockPlan) (i : Nat) : Id (Nat × Nat × Nat) := do
  let mut seg := 0
  while plan.segBlock[seg + 1]! ≤ i do
    seg := seg + 1
  let (lo, hi) := plan.segs[seg]!
  let a := lo + (i - plan.segBlock[seg]!) * plan.len
  return (seg, a, if hi - a < plan.len then hi else a + plan.len - 1)

/-! ### The loops of the shapes over a block -/

/-- What the loop over the denominators of a block carries from one denominator to the next: the
delivery of the search (`Ratpoints.Delivery`), the store of the tables of rows
(`Ratpoints.Sieve.RowStore`) and the counters of the block (`Ratpoints.Sieve.Counters`). -/
abbrev BlockState (σ : Type) := Delivery σ × RowStore × Counters

/-- One denominator `b` of a block, on the state `st` of the block: the residues of `b` divided by
the stride of its class `cls[b mod 64]` modulo the moduli of the first two stages, the entries
`es` with the reciprocals `mgs` (`Ratpoints.Sieve.fillBpList`), and its points
(`Ratpoints.Sieve.sift`, with the entries `es3` and the reciprocals `mgs3` of the third stage, the
row offsets `offsets` of the classes, the bounds `iv` of the search intervals, the height `H`,
pieces of at most `A` bit arrays, the end `sp1` of the first stage and the flags `fl`), delivered
to the callback `process`.

C: `find_points.c:3926-3927`, `find_points.c:3955-3956`, `find_points.c:4042-4043`,
`find_points.c:4066-4067`

Deviation: a function of its own for the two calls that each shape makes for a denominator, the
residues a list for the array `bp_list`, which `sift` reads through its pointer; the state of the
block passed and returned (`Ratpoints.Sieve.BlockState`), for the pointers `info` and `wk->quit`,
the count `total` that `run_block` keeps, the arrays `sieve` of the entries and the counters of the
sieving thread. -/
def siftDen {σ : Type} (process : Int → Int → Int → σ → Answer σ) (c : List Int) (d H A : Nat)
    (fl : CheckFlags) (sp1 : Nat) (es : List SieveEntry) (mgs : List Nat) (es3 : List SieveEntry)
    (mgs3 : List Nat) (cls : Vector NumClass 64) (offsets : Array Nat) (iv : Array IntervalBounds)
    (b : Nat) (st : BlockState σ) : Id (BlockState σ) :=
  let cl := cls[b % 64]!
  sift process c d H A b fl sp1 es mgs (fillBpList b cl.k es mgs) cl offsets es3 mgs3 iv st.2.1
    st.1 st.2.2

/-- The steps `a, …, e` of a block of the square shape, on the state `st` of the block: for each
`k`, the denominator `k ^ 2`, sifted by `step` when the pattern of its class modulo 64 among the
classes `cls` is not `0`, after which the loop returns if the callback has stopped the search.

C: `find_points.c:3919-3925`, `find_points.c:3928-3935`

Deviation: the denominator sifted by the argument `step`, for the two calls of each shape
(`Ratpoints.Sieve.siftDen`); the pattern of the class read as its one word, for `EXT0(cl->bits)`;
the state of the block passed and returned (`Ratpoints.Sieve.BlockState`); natural numbers for the
`long`s; no output under `DEBUG`. -/
def squaresBlock {σ : Type} (step : Nat → BlockState σ → Id (BlockState σ))
    (cls : Vector NumClass 64) (a e : Nat) (st : BlockState σ) : Id (BlockState σ) := do
  let mut st := st
  for k in [a:e + 1] do
    let bb := k * k
    if cls[bb % 64]!.bits != 0 then
      st ← step bb st
      if st.1.quit then return st
  return st

/-- The steps `a, …, e` of a block of the segment of the divisor `dv` of the divisor shape, on the
state `st` of the block: for each `k`, the denominator `dv k ^ 2`, sifted by `step` when the pattern
of its class modulo 64 among the classes `cls` is not `0` and it passes the valuation test with the
primes `info` (`Ratpoints.Sieve.denInfoTest`), after which the loop returns if the callback has
stopped the search.

C: `find_points.c:3937-3943`, `find_points.c:3954`, `find_points.c:3957-3965`

Deviation: the denominator sifted by the argument `step`, for the two calls of each shape
(`Ratpoints.Sieve.siftDen`); the valuation test a function of its own; the pattern of the class read
as its one word; the state of the block passed and returned (`Ratpoints.Sieve.BlockState`); natural
numbers for the `long`s; no output under `DEBUG`. -/
def squares1Block {σ : Type} (step : Nat → BlockState σ → Id (BlockState σ))
    (cls : Vector NumClass 64) (info : List Setup.DenInfo) (dv a e : Nat) (st : BlockState σ) :
    Id (BlockState σ) := do
  let mut st := st
  for k in [a:e + 1] do
    let bb := dv * k * k
    if cls[bb % 64]!.bits != 0 then
      if ← denInfoTest info bb then
        st ← step bb st
        if st.1.quit then return st
  return st

/-- The positions of the forbidden divisors `forb` tested with words at the first word `a` of a
block: `a mod p` for each `p`, by a multiplication with the reciprocal of `p`
(`Ratpoints.Sieve.mulMod`) when `a ≤ Ratpoints.mulModLimit`, and by the helper `mod` of the C code
otherwise (`Ratpoints.Sieve.modLong`).

C: `find_points.c:3981`, `find_points.c:3983-3988`

Deviation: indices into the words of the divisors, for the pointers `cur` into the arrays from
`start` to `end`; a Boolean for the `int` `small`; natural numbers for the `long`s. -/
def forbStarts (forb : Array ForbiddenEntry) (a : Nat) : Array Nat :=
  let small := decide (a ≤ mulModLimit)
  forb.map fun f ↦ if small then mulMod a f.p f.magic else (modLong a f.p).toNat

/-- The word of the denominators `64 w + j` of the word `w` that pass the class test and the
forbidden divisors tested with words, with the positions `cur` of these divisors at `w`: the word
`db` of the classes that admit a numerator (`Ratpoints.Sieve.denBits`), and-ed with the word at the
position of each divisor of `forb`, whose position steps on by one, back to `0` at its prime `p`;
in the first word `lo0` of the run the bits below `bLow mod 64` cleared, and in its last word `hi0`
those above `bHigh mod 64`. Returns the word and the positions at the next word.

C: `find_points.c:3990`, `find_points.c:3993-4006`

Deviation: indices into the words of the divisors, for the pointers `cur`, and the end of the
words of a divisor its prime `p`, for the pointer `end`; the remainders by 64 for the masks by
`LONG_MASK`; the positions returned with the word; natural numbers for the `long`s; no output under
`DEBUG`. -/
def denWord (db : UInt64) (forb : Array ForbiddenEntry) (cur : Array Nat)
    (lo0 hi0 bLow bHigh w : Nat) : Id (UInt64 × Array Nat) := do
  let mut x := db
  let mut cur := cur
  for n in [0:forb.size] do
    x := x &&& forb[n]!.words[cur[n]!]!
    cur := cur.set! n (if cur[n]! + 1 = forb[n]!.p then 0 else cur[n]! + 1)
  if w = lo0 then x := x &&& ~~~0 <<< (bLow % 64).toUInt64
  if w = hi0 then x := x &&& ~~~0 >>> (63 - bHigh % 64).toUInt64
  return (x, cur)

/-- The set bits `j` of the word `x` of the denominators `base + j`, lowest first
(`Ratpoints.Sieve.ctz`), on the state `st` of the block: each bit cleared, and its denominator
sifted by `step` when it passes the tests `test` of the word shape (`Ratpoints.Sieve.wordsTest`),
after which the walk returns if the callback has stopped the search.

C: `find_points.c:4007-4009`, `find_points.c:4012`, `find_points.c:4044-4053`

Deviation: the denominator sifted by the argument `step`, for the two calls of each shape
(`Ratpoints.Sieve.siftDen`), and the tests of the word shape the argument `test`, for the code of
`Ratpoints.Sieve.wordsTest` in the loop; the lowest set bit by the loop of `RP_CTZL`
(`Ratpoints.Sieve.ctz`); the class of the denominator read by `Ratpoints.Sieve.siftDen`; the state
of the block passed and returned (`Ratpoints.Sieve.BlockState`); natural numbers for the `long`s; no
output under `DEBUG`. -/
def walkDens {σ : Type} (step : Nat → BlockState σ → Id (BlockState σ)) (test : Nat → Id Bool)
    (x : UInt64) (base : Nat) (st : BlockState σ) : Id (BlockState σ) := do
  let mut x := x
  let mut st := st
  while x != 0 do
    let b := base + (← ctz x)
    x := x &&& (x - 1)
    if ← test b then
      st ← step b st
      if st.1.quit then return st
  return st

/-- The steps `a, …, e` of a block of the word shape, the words of 64 denominators, on the state
`st` of the block: the positions of the forbidden divisors `forb` tested with words at the first
word `a` (`Ratpoints.Sieve.forbStarts`); then for each word `w`, the word of its denominators that
pass the class test and those divisors, with the masks of the first and the last word `lo0` and
`hi0` of the run for the denominators `bLow, …, bHigh` (`Ratpoints.Sieve.denWord`, with the word
`db` of the classes that admit a numerator), and the walk through its set bits, the denominators
that pass the tests `test` sifted by `step` (`Ratpoints.Sieve.walkDens`), after which the loop
returns if the callback has stopped the search.

C: `find_points.c:3967-3980`, `find_points.c:3982`, `find_points.c:3989`, `find_points.c:3991-3992`,
`find_points.c:4054-4058`

Deviation: the denominator sifted by the argument `step`, for the two calls of each shape, and the
tests of the word shape the argument `test` (`Ratpoints.Sieve.wordsTest`); the forbidden divisors an
array, for the pointer `run->forb_ba` and their count `nfb`; the product `64 w` for the shift by
`LONG_SHIFT`; the state of the block passed and returned (`Ratpoints.Sieve.BlockState`); natural
numbers for the `long`s. -/
def wordsBlock {σ : Type} (step : Nat → BlockState σ → Id (BlockState σ))
    (forb : Array ForbiddenEntry) (test : Nat → Id Bool) (db : UInt64)
    (lo0 hi0 bLow bHigh a e : Nat) (st : BlockState σ) : Id (BlockState σ) := do
  let mut cur := forbStarts forb a
  let mut st := st
  let mut w := a
  repeat
    let (x, cur') ← denWord db forb cur lo0 hi0 bLow bHigh w
    cur := cur'
    st ← walkDens step test x (64 * w) st
    if st.1.quit then return st
    if w = e then break
    w := w + 1
  return st

/-- The steps `a, …, e` of a block of the shape of every denominator, on the state `st` of the
block: each denominator `b`, sifted by `step` when the pattern of its class modulo 64 among the
classes `cls` is not `0`, after which the loop returns if the callback has stopped the search.

C: `find_points.c:4060-4065`, `find_points.c:4068-4074`

Deviation: the denominator sifted by the argument `step`, for the two calls of each shape
(`Ratpoints.Sieve.siftDen`); the pattern of the class read as its one word; the state of the block
passed and returned (`Ratpoints.Sieve.BlockState`); natural numbers for the `long`s; no output under
`DEBUG`. -/
def allBlock {σ : Type} (step : Nat → BlockState σ → Id (BlockState σ)) (cls : Vector NumClass 64)
    (a e : Nat) (st : BlockState σ) : Id (BlockState σ) := do
  let mut st := st
  let mut b := a
  repeat
    if cls[b % 64]!.bits != 0 then
      st ← step b st
      if st.1.quit then return st
    if b = e then break
    b := b + 1
  return st

/-- The loop of the shape `shape` over the steps `a, …, e` of a block in the segment `seg` of the
blocks `plan`, each denominator handed to the step `step` with the state `st`: the squares
(`Ratpoints.Sieve.squaresBlock`), the divisors times squares with the divisor of the segment
(`Ratpoints.Sieve.squares1Block`), the words of 64 denominators with the tests of
`Ratpoints.Sieve.wordsTest` (`Ratpoints.Sieve.wordsBlock`), or every denominator
(`Ratpoints.Sieve.allBlock`), with the classes `cls`, the word `db` of the classes that admit a
numerator and the range `bLow, …, bHigh` of the denominators.

C: `find_points.c:3917-3918`, `find_points.c:3936`, `find_points.c:3966`, `find_points.c:4059`,
`find_points.c:4075-4076`

Deviation: a function of its own for the `switch` of `run_block` over the shapes, the step an
argument, for the two lines of each shape that sift a denominator (`Ratpoints.Sieve.siftDen`); the
first and last words of the run, which the masks of the word shape compare with, read from the first
segment of `plan`, as the C code reads `seg_lo[0]` and `seg_hi[0]`; natural numbers for the
`long`s. -/
def Shape.blockLoop {σ : Type} (shape : Shape) (step : Nat → BlockState σ → Id (BlockState σ))
    (cls : Vector NumClass 64) (db : UInt64) (plan : BlockPlan) (seg a e bLow bHigh : Nat)
    (st : BlockState σ) : Id (BlockState σ) :=
  match shape with
  | .squares => squaresBlock step cls a e st
  | .squares1 info divisors => squares1Block step cls info divisors[seg]! a e st
  | .words forb forbVal useJacobi fast lcf =>
    wordsBlock step forb.toArray (wordsTest forbVal useJacobi fast lcf) db plan.segs[0]!.1
      plan.segs[0]!.2 bLow bHigh a e st
  | .all => allBlock step cls a e st

/-! ### One block -/

/-- A decision of the correction of the moduli: the first block `block` that it is for, and the ends
`sp2` and `sp3` of the second and the third stage that the blocks from it on are sifted with, up to
the next decision. The first is that of the choice, for block `0`
(`Ratpoints.Sieve.Correction.start`).

It models no C code of its own: a structure for the entries of the arrays `dec_block`, `dec_sp2`
and `dec_sp3` of the run (`find_points.c:3761`, `Ratpoints.Sieve.Correction`), with natural numbers
for the `long`s. -/
structure Decision where
  /-- The first block that the decision is for. -/
  block : Nat
  /-- The end of the second stage. -/
  sp2 : Nat
  /-- The end of the third stage. -/
  sp3 : Nat
  deriving Inhabited

/-- The decision in force for block `i`, among the decisions `decs`, whose first is for block `0`:
the last whose first block is at most `i`, found from the last decision back.

C: `find_points.c:3908-3910`, `find_points.c:3912`

Deviation: the decisions an array of structures (`Ratpoints.Sieve.Decision`), for the three arrays
`dec_block`, `dec_sp2` and `dec_sp3` and their count `ndec`, which the C code reads with an acquire
load, for the threads that publish their decisions (`RP_ACQUIRE`), here a plain read; the index
returned, for the local `d`; natural numbers for the `long`s. -/
def findDecision (decs : Array Decision) (i : Nat) : Id Nat := do
  let mut dd := decs.size - 1
  while i < decs[dd]!.block do
    dd := dd - 1
  return dd

/-- What the sieve of one block reports to the fold of the run (`Ratpoints.Sieve.runFold`): its
counters (`Ratpoints.Sieve.Counters`), the index `dec` of the decision that it was sifted with and
the ends `sp2` and `sp3` of the second and the third stage of that decision.

C: `find_points.c:4082-4086`

Deviation: the counters as a structure, for the six fields; natural numbers for the `long`s. -/
structure BlockStat where
  /-- The counters of the block. -/
  cnt : Counters
  /-- The index of the decision that the block was sifted with. -/
  dec : Nat
  /-- The end of the second stage of that decision. -/
  sp2 : Nat
  /-- The end of the third stage of that decision. -/
  sp3 : Nat

/-- Block `i` of the run with the blocks `plan` of the shape `shape`, for the polynomial of degree
`d` with the coefficient list `c`, delivered to the callback `process` on the delivery `r`, with the
store `store` of the tables of rows: its segment and its steps `a, …, e`
(`Ratpoints.Sieve.BlockPlan.steps`), the decision in force for it among `decs`
(`Ratpoints.Sieve.findDecision`), whose ends `sp2` and `sp3` cut the sieve entries `entries` and
their reciprocals `magics` into the first two stages, the first ending at `sp1`, and the third
stage; the counters from zero; and the loop of the shape over the steps
(`Ratpoints.Sieve.Shape.blockLoop`, with the word `db` of the classes that admit a numerator and the
range `bLow, …, bHigh` of the denominators), each denominator sifted by `Ratpoints.Sieve.siftDen`
with the classes `cls`, the row offsets `offsets`, the bounds `iv` of the search intervals, the
height `H`, pieces of at most `A` bit arrays and the flags `fl`. Returns the delivery, the store and
the report of the block (`Ratpoints.Sieve.BlockStat`).

C: `find_points.c:3127-3128`, `find_points.c:3889-3898`, `find_points.c:3911`,
`find_points.c:3913-3915`, `find_points.c:4077-4078`, `find_points.c:4088-4093`, `rp-private.h:582`

Deviation: the decision's entries and reciprocals cut as lists for each block, for the numbers `sp2`
and `sp3` that the sieving thread keeps and through which `sift` and `fill_bp_list` read the arrays
`sieve_list` and `magics`; the report returned with the delivery and the store, for the fields of
the sieving thread that `worker_stat` copies into it after the block; the counters and the index of
the decision, which `worker_init` clears before the run (lines 3127-3128), set only here, for each
block (lines 3911 and 3914-3915), before they are read; the arguments of the run passed explicitly,
for the fields of the run and of the arguments that `run_block` reads; the delivery `r` passed and
returned, for the pointers `info` and `wk->quit` and the count `total` that `run_block` keeps from
zero and returns; the array `bp_list` of `sp3_max` entries on the stack, of which `fill_bp_list`
fills the first `sp2`, a list made by `Ratpoints.Sieve.siftDen`; natural numbers for the `long`s. -/
def runBlock {σ : Type} (process : Int → Int → Int → σ → Answer σ) (c : List Int) (d H A : Nat)
    (fl : CheckFlags) (sp1 : Nat) (entries : List SieveEntry) (magics : Array Nat)
    (cls : Vector NumClass 64) (offsets : Array Nat) (db : UInt64) (shape : Shape)
    (iv : Array IntervalBounds) (bLow bHigh : Nat) (plan : BlockPlan) (decs : Array Decision)
    (i : Nat) (store : RowStore) (r : Delivery σ) : Id (Delivery σ × RowStore × BlockStat) := do
  let (seg, a, e) ← plan.steps i
  let dec ← findDecision decs i
  let sp2 := decs[dec]!.sp2
  let sp3 := decs[dec]!.sp3
  let es3 := (entries.drop sp2).take (sp3 - sp2)
  let mgs3 := (magics.toList.drop sp2).take (sp3 - sp2)
  let step := siftDen process c d H A fl sp1 (entries.take sp2) (magics.toList.take sp2) es3 mgs3
    cls offsets iv
  let (r, store, cnt) ← shape.blockLoop step cls db plan seg a e bLow bHigh (r, store, {})
  return (r, store, ⟨cnt, dec, sp2, sp3⟩)

/-! ### The correction of the moduli -/

/-- The counters of the run, the sums of those of the blocks folded so far in the order of the
blocks (`Ratpoints.Sieve.RunCounts.fold`), with the words swept when the counters of the second
stage on were last restarted, `words2`, and the end `sp2` of the second stage that those were
counted under: they restart when a block sifted with another `sp2` is folded.

C: `find_points.c:1363-1367`

Deviation: the six counters of the sieving thread extended (`Ratpoints.Sieve.Counters`), for the
six fields; a `UInt64` for the `unsigned long` `n_words_2` and a natural number for the `long`
`sp2`. -/
structure RunCounts extends Counters where
  /-- `n_words_2`: the words swept when the counters of the second stage on last restarted. -/
  words2 : UInt64 := 0
  /-- The end of the second stage that those counters were counted under. -/
  sp2 : Nat

/-- The counters of the run `c` after the fold of a block that was sifted with the end `sp2` of the
second stage and counted `k`: when `sp2` is not the end that the counters of the run were counted
under, those of the second stage on (`bits`, `coprime`, `checks`, `sifts`) restart from zero, with
the words swept so far as `words2` and `sp2` as the end; then the counters of the block are added.

C: `find_points.c:4107-4113`

Deviation: a function of its own for this part of `run_fold`; the end `sp2` passed, for the entry
`dec_sp2[st->dec]` that `run_fold` reads; the sums of `UInt64`s, wrapping as the `unsigned long`s
do. -/
def RunCounts.fold (c : RunCounts) (sp2 : Nat) (k : Counters) : RunCounts :=
  let c := if sp2 != c.sp2 then
      { c with bits := 0, coprime := 0, checks := 0, sifts := 0, words2 := c.words, sp2 }
    else c
  { c with words := c.words + k.words, arrays := c.arrays + k.arrays, bits := c.bits + k.bits,
           coprime := c.coprime + k.coprime, checks := c.checks + k.checks,
           sifts := c.sifts + k.sifts }

/-- The rates that the run has shown, from its counters `c` with the end `c.sp2` of the second stage
that they were counted under, the densities of the sieve entries `es` and the end `sp1` of the first
stage, or none when there is too little data: none unless the run swept words, `sp1 ≥ 1`,
`sp1 < c.sp2`, the run counted `Ratpoints.adaptArrays` bit arrays that survived the first stage and
`Ratpoints.adaptBits` numerators that survived the second, and words since the counters of the
second stage restarted; and otherwise the survivors of the first stage per word `s1`, those of the
second per word since the restart `s2`, the product `r1` of the densities of the first stage and
the product `r2` of those of the first two, none unless `r2 < r1` and `s2 < s1`.

C: `find_points.c:1389`, `find_points.c:1400-1420`

Deviation: a function of its own for this part of `adapt_primes`, its returns the result none;
`Float`s for the doubles, in the order of the C code, the conversions of the `UInt64` counters to
`Float` as the C code converts the `unsigned long`s to doubles, and the words since the restart the
difference of the `UInt64`s, wrapping, converted, as the C code computes it; the densities read from
the entries, for `sieve_list[n]->r`; natural numbers for the `long`s, so that `sp1 ≤ 0` is
`sp1 = 0`. -/
def adaptRates (es : Array SieveEntry) (c : RunCounts) (sp1 : Nat) :
    Id (Option (Float × Float × Float × Float)) := do
  let words := c.words.toFloat
  if words ≤ 0.0 || c.sp2 ≤ sp1 || sp1 = 0 then return none
  if c.arrays < adaptArrays.toUInt64 || c.bits < adaptBits.toUInt64 then return none
  let words2 := (c.words - c.words2).toFloat
  if words2 ≤ 0.0 then return none
  let s1 := c.arrays.toFloat / words
  let s2 := c.bits.toFloat / words2
  let mut r1 := 1.0
  for n in [0:sp1] do
    r1 := r1 * es[n]!.r
  let mut r2 := r1
  for n in [sp1:c.sp2] do
    r2 := r2 * es[n]!.r
  if r1 - r2 ≤ 0.0 || s1 ≤ s2 then return none
  return some (s1, s2, r1, r2)

/-- The walk of the correction up from the end `start` of the second stage: for each further sieve
entry of `es` in turn, of the modulus `p` and the density `r`, the survivors per word `next` with
it, `level + chance rate r`, and its cost (`Ratpoints.primeCost` with `Ratpoints.costPhase2 s` per
word, the cost `ct` of a row and the estimates `U` and `D` of the run); the walk stops at the first
entry whose survivors removed, `s - next`, times the cost `costSurv` of a survivor, are not above
its cost, and otherwise takes it: `rate` times `r`, `s` the new survivors per word. Returns the new
end of the second stage, the rate and the survivors per word.

C: `find_points.c:1449-1457`

Deviation: a function of its own for this loop of `adapt_primes`; the entries an array, for
`sieve_list` up to `sp3_max`, its size; `Float`s for the doubles, in the order of the C code;
natural numbers for the `long`s. -/
def adaptUp (es : Array SieveEntry) (start : Nat) (level chance rate s costSurv ct U D : Float) :
    Id (Nat × Float × Float) := do
  let mut want := start
  let mut rate := rate
  let mut s := s
  for n in [start:es.size] do
    let r := es[n]!.r
    let next := level + chance * rate * r
    let cost := primeCost es[n]!.p (costPhase2 * s) true ct U D
    if (s - next) * costSurv ≤ cost then break
    rate := rate * r
    s := next
    want := want + 1
  return (want, rate, s)

/-- The walk of the correction down from the end `sp2` of the second stage, when it takes nothing
more: for the entries of `es` below `sp2` in turn, from the last down, while the position is above
`sp1` and the entry is a prime (its count `nf` of factors `0`), the survivors per word `prev`
without it, `level + chance rate / r`, and its cost (`Ratpoints.primeCost` with
`Ratpoints.costPhase2 prev` per word); the walk stops at the first entry whose survivors removed,
`prev - s`, times the cost `costSurv` of a survivor, are above its cost, and otherwise drops it:
`rate` divided by `r`, `s` the survivors per word without it. Returns the new end of the second
stage and the survivors per word.

C: `find_points.c:1460-1472`

Deviation: a function of its own for this loop of `adapt_primes`; the entries an array, for
`sieve_list`; `Float`s for the doubles, in the order of the C code; natural numbers for the
`long`s, `n` stepping down from `sp2 - 1` while it is above `sp1`. -/
def adaptDown (es : Array SieveEntry) (sp1 sp2 : Nat)
    (level chance rate s costSurv ct U D : Float) : Id (Nat × Float) := do
  let mut want := sp2
  let mut rate := rate
  let mut s := s
  let mut n := sp2 - 1
  while sp1 < n && es[n]!.nf == 0 do
    let r := es[n]!.r
    let prev := level + chance * rate / r
    let cost := primeCost es[n]!.p (costPhase2 * prev) true ct U D
    if (prev - s) * costSurv > cost then break
    rate := rate / r
    s := prev
    want := want - 1
    n := n - 1
  return (want, s)

/-- The correction of the end of the second stage, from the counters `c` of the run with the end
`c.sp2` that they were counted under, the floor `level` and the slope `chance` of the survivors per
word against the product of the densities, the product `r2` of the densities of the first two
stages, the cost `checkRel` of one exact check, the cost `ct` of a row and the estimates `U` and `D`
of the run: the cost of a survivor, `Ratpoints.costSurvivor` plus the share of the survivors that
reach the exact check times `Ratpoints.costCheck (checkRel - 1)`; the walk up
(`Ratpoints.Sieve.adaptUp`), and when it takes nothing, the walk down (`Ratpoints.Sieve.adaptDown`)
from `c.sp2`, never below the end `sp1` of the first stage. Returns the new end of the second stage
and the survivors per word with it.

C: `find_points.c:1439-1448`, `find_points.c:1458-1459`, `find_points.c:1473-1476`

Deviation: a function of its own for this part of `adapt_primes`; `Float`s for the doubles, in the
order of the C code; natural numbers for the `long`s. -/
def adaptSecond (es : Array SieveEntry) (c : RunCounts) (sp1 : Nat)
    (level chance r2 checkRel ct U D : Float) : Id (Nat × Float) := do
  let costSurv := costSurvivor + c.checks.toFloat / c.bits.toFloat * costCheck * (checkRel - 1.0)
  let s := level + chance * r2
  let (want, rate, s) ← adaptUp es c.sp2 level chance r2 s costSurv ct U D
  if want == c.sp2 then adaptDown es sp1 c.sp2 level chance rate s costSurv ct U D
  else return (want, s)

/-- The correction of the third stage, which starts at the end `sp2` of the second, for the value
`q` of `-Q`, the cost `checkRel` of one exact check, the floor `level` and the slope `chance` of the
survivors per word against the product of the densities, the product `r2` of the densities of the
first two stages and the survivors per word `s` with the new second stage: the costs of a prime of
the stage per denominator, `q` when `q ≥ 0` and `Ratpoints.sp3PerDenom` otherwise, and per survivor,
`Ratpoints.sp3PerSurvivor`, each divided by `checkRel`; the survivors that a denominator brings to
the stage, `S`, the share of the run's survivors that pass the test for common factors per
denominator sifted, carried over to the new second stage by the ratio of `s` to the survivors per
word with the old one, `old = level + chance r2` (when `old > 0`); for the entries of `es` from
`sp2` on in turn, the stage stops at the first of density `r` with `S (1 - perSurv - r) ≤ perDenom`,
and otherwise takes it, `S` times `r`. Returns the end of the third stage.

C: `find_points.c:1487-1505`

Deviation: a function of its own for this part of `adapt_primes`, the fields `sp3_per_denom` (its
double read by its bits by the caller) and `check_rel` of the arguments that it reads and the local
variables `level`, `chance`, `r2` and `s` of `adapt_primes` passed as arguments; the end of the
third stage returned, for the field `sp3` of the arguments that it writes; `Float`s for the doubles,
in the order of the C code; natural numbers for the `long`s. -/
def adaptThird (es : Array SieveEntry) (c : RunCounts) (sp2 : Nat)
    (q checkRel level chance r2 s : Float) : Id Nat := do
  let perDenom := (if 0.0 ≤ q then q else sp3PerDenom) / checkRel
  let perSurv := sp3PerSurvivor / checkRel
  let mut S := c.coprime.toFloat / c.sifts.toFloat
  let old := level + chance * r2
  if old > 0.0 then S := S * (s / old)
  let mut sp3 := sp2
  while sp3 < es.size do
    let r := es[sp3]!.r
    if S * (1.0 - perSurv - r) ≤ perDenom then break
    S := S * r
    sp3 := sp3 + 1
  return sp3

/-- The correction of the choice of the moduli from the counters `c` of the run, with the options
`s` (`Ratpoints.SieveOptions`), the result `P` of the choice (`Ratpoints.Params`: its end `sp1` of
the first stage, its estimates of the run and its cost of a check) and the sieve entries `es`, its
reserve included, when the ends of the second and the third stage are `sp2` and `sp3`, the latest
decision: the next correction when twice the words swept so far have been swept, wrapping as the
`unsigned long` does; nothing more when the rates of the run do not tell
(`Ratpoints.Sieve.adaptRates`); otherwise the floor and the slope of the survivors per word, then
with `-A 2` or more the end of the second stage corrected (`Ratpoints.Sieve.adaptSecond`), and
unless `-P` gives the third stage, when the run sifted denominators, the end of the third stage
(`Ratpoints.Sieve.adaptThird`, with the value of `-Q` and the cost of a check), and otherwise the
end of the third stage at least that of the second. Returns the ends of the second and the third
stage and the words of the next correction.

C: `find_points.c:1383-1388`, `find_points.c:1390-1398`, `find_points.c:1421-1438`,
`find_points.c:1477-1486`, `find_points.c:1506-1509`, `find_points.c:1515`

Deviation: the fields of the arguments that `adapt_primes` reads passed as the options, the result
of the choice and the entries, and those that it writes, `sp2`, `sp3` and `adapt_at`, returned; the
doubles of the options by their bits; `Float`s for the doubles, in the order of the C code; integers
for the `long`s `adapt` and `sp3_extra` and natural numbers for the others; no output under
`RP_PRIME_STATS`. -/
def adaptPrimes (s : SieveOptions) (P : Params) (es : Array SieveEntry) (c : RunCounts)
    (sp2 sp3 : Nat) : Id (Nat × Nat × UInt64) := do
  let adaptAt := c.words + c.words
  let some (s1, s2, r1, r2) ← adaptRates es c P.sp1 | return (sp2, sp3, adaptAt)
  let ct := s.costTable.toFloat
  let ct := if 0.0 ≤ ct then ct else costTable
  let chance := (s1 - s2) / (r1 - r2)
  let level := s1 - chance * r1
  let level := if level < 0.0 then 0.0 else level
  let mode : Int := if s.adapt < 0 then 1 else s.adapt
  let (sp2, sv) ← if 2 ≤ mode then
      adaptSecond es c P.sp1 level chance r2 P.checkRel ct P.runWords P.runDenoms
    else pure (sp2, level + chance * r2)
  if s.sp3Extra < 0 && c.sifts > 0 then
    let sp3 ← adaptThird es c sp2 s.sp3PerDenom.toFloat P.checkRel level chance r2 sv
    return (sp2, sp3, adaptAt)
  return (sp2, if sp3 < sp2 then sp2 else sp3, adaptAt)

/-- The state of the correction of the moduli during the run: the counters of the run
(`Ratpoints.Sieve.RunCounts`), the number of the blocks folded, the decisions made
(`Ratpoints.Sieve.Decision`), the ends of the second and the third stage of the last block folded,
and the latest decision of the correction with the words of the next one, which the C code keeps in
the arguments.

C: `find_points.c:3755-3762`

Deviation: the decisions an array of structures, for the three arrays `dec_block`, `dec_sp2` and
`dec_sp3` and their count `ndec`; the fields `sp2`, `sp3` and `adapt_at` of the arguments, which
`adapt_primes` writes and `run_fold` reads, kept here, since they are read only within the run, by
`run_fold` and `adapt_primes`, after which line 5163 overwrites `sp2` and `sp3` with the ends of the
last block folded; natural numbers for the `long`s and a `UInt64` for the `unsigned long`. -/
structure Correction where
  /-- The counters of the run. -/
  cnt : RunCounts
  /-- `nfolded`: the number of the blocks folded. -/
  folded : Nat
  /-- The decisions, the first for block `0`. -/
  decisions : Array Decision
  /-- `last_sp2`: the end of the second stage of the last block folded. -/
  lastSp2 : Nat
  /-- `last_sp3`: the end of the third stage of the last block folded. -/
  lastSp3 : Nat
  /-- `args->sp2`: the end of the second stage of the latest decision. -/
  sp2 : Nat
  /-- `args->sp3`: the end of the third stage of the latest decision. -/
  sp3 : Nat
  /-- `args->adapt_at`: the words swept at which the next correction is made. -/
  adaptAt : UInt64

/-- The correction at the start of the run, for the ends `sp2` and `sp3` of the second and the third
stage of the choice and the words `adaptAt` of the first correction: nothing counted, the counters
of the second stage on counted under `sp2`, no block folded, one decision, that of the choice for
block `0`, and the ends of the choice as those of the last block folded.

C: `find_points.c:3853-3856`, `find_points.c:3861-3863`

Deviation: the state returned, for the fields of the run that `run_setup` sets. -/
def Correction.start (sp2 sp3 : Nat) (adaptAt : UInt64) : Correction :=
  { cnt := { sp2 }, folded := 0, decisions := #[⟨0, sp2, sp3⟩], lastSp2 := sp2, lastSp3 := sp3,
    sp2, sp3, adaptAt }

/-- The fold of the next block of the run, with the report `b` (`Ratpoints.Sieve.BlockStat`), into
the state `st` of the correction, with the options `s`, the result `P` of the choice and the sieve
entries `es`: the block is the `j`-th folded; its counters added to those of the run
(`Ratpoints.Sieve.RunCounts.fold`, with the end of the second stage of its decision); its ends as
those of the last block folded; and when the run has swept the words of the next correction, the
correction (`Ratpoints.Sieve.adaptPrimes`), whose result, when it changes an end, is a decision for
the blocks from `j + Ratpoints.adaptLag + 1` on.

C: `find_points.c:4102-4106`, `find_points.c:4114-4127`

Deviation: the state of the correction passed and returned (`Ratpoints.Sieve.Correction`), for the
fields of the run and of the arguments; the decision appended to the array, for the store into the
three arrays and the release store of their count (`RP_PUBLISH`), for the threads that read them,
here a plain store; natural numbers for the `long`s. -/
def runFold (s : SieveOptions) (P : Params) (es : Array SieveEntry) (st : Correction)
    (b : BlockStat) : Id Correction := do
  let j := st.folded
  let cnt := st.cnt.fold st.decisions[b.dec]!.sp2 b.cnt
  let st := { st with folded := j + 1, cnt, lastSp2 := b.sp2, lastSp3 := b.sp3 }
  if cnt.words < st.adaptAt then return st
  let (sp2, sp3, adaptAt) ← adaptPrimes s P es cnt st.sp2 st.sp3
  let decisions := if sp2 != st.sp2 || sp3 != st.sp3 then
      st.decisions.push ⟨j + adaptLag + 1, sp2, sp3⟩
    else st.decisions
  return { st with sp2, sp3, adaptAt, decisions }

/-! ### The run -/

/-- The points of the denominators from `bLow` to `bHigh` of the shape `shape`, for the polynomial
of degree `d` with the coefficient list `c`, delivered to the callback `process` on the delivery
`r`, whose flag `quit` is clear, with the sieve entries `entries` of the moduli, the reserve of the
correction included, and the reciprocals `magics` of their moduli in their order, as the result `P`
of the choice (`Ratpoints.sievingInfo`) gives them for the options `s`: the blocks of the run
(`Ratpoints.Sieve.Shape.blockPlan`); the correction from the choice
(`Ratpoints.Sieve.Correction.start`, with the ends `P.sp2` and `P.sp3` and the words `P.adaptAt`);
then for each block in turn its points (`Ratpoints.Sieve.runBlock`, with the decision in force for
it, the end `P.sp1` of the first stage, the classes `cls` with their row offsets `offsets`, the word
`db` of the classes that admit a numerator, the bounds `iv` of the search intervals and pieces of at
most `A` bit arrays), the rows that it builds into the store `store` going on to the next block, and
the fold of its report (`Ratpoints.Sieve.runFold`), after which the run returns if the callback has
stopped the search. Returns the delivery and the ends of the second and the third stage of the last
block folded, which the search reports as used.

C: `find_points.c:5120`, `find_points.c:5152-5160`, `find_points.c:5163`

Deviation: the blocks on the calling thread alone, without the pool of threads, which sifts them
apart and delivers them in the same order, the decision of each block depending only on the folds of
the blocks at least `Ratpoints.adaptLag + 1` before it (excluded with the threads); the ends of the
last block returned, for the fields `sp2` and `sp3` of the arguments that line 5163 writes; the
store of the tables of rows passed from one block to the next, for the arrays `sieve` of the entries
of the arguments, its last state not returned, as nothing reads the tables of rows after the run;
the delivery `r` passed and returned, for the pointers `info` and `wk.quit` and the count `total`;
natural numbers for the `long`s. -/
def sieveRun {σ : Type} (process : Int → Int → Int → σ → Answer σ) (c : List Int) (d H A : Nat)
    (fl : CheckFlags) (s : SieveOptions) (P : Params) (entries : List SieveEntry)
    (magics : Array Nat) (cls : Vector NumClass 64) (offsets : Array Nat) (db : UInt64)
    (shape : Shape) (iv : Array IntervalBounds) (bLow bHigh : Nat) (store : RowStore)
    (r : Delivery σ) : Id (Delivery σ × Nat × Nat) := do
  let plan ← shape.blockPlan bLow bHigh
  let es := entries.toArray
  let mut corr := Correction.start P.sp2 P.sp3 P.adaptAt
  let mut r := r
  let mut store := store
  for i in [0:plan.nblocks] do
    let (r', st, b) ← runBlock process c d H A fl P.sp1 entries magics cls offsets db shape iv bLow
      bHigh plan corr.decisions i store r
    r := r'
    store := st
    corr ← runFold s P es corr b
    if r.quit then break
  return (r, corr.lastSp2, corr.lastSp3)

/-! ### Examples

The blocks, the decision in force, the fold of the counters, the correction and the denominators
that the blocks visit against their rule; the shape and the denominators that the run sifts against
those that a build of ratpoints at the pinned commit prints with a dump of the side of the
denominators on the standard error (the dump); and the blocks and the run of the divisor shape
against the points that ratpoints prints. -/

-- The block length: at least 16 steps, about 1024 blocks for a long run.
#guard [0, 1, 16000, 16383, 16384, 1048576].map blockLength == [16, 16, 16, 16, 17, 1025]

-- The segments and blocks of the four shapes: the squares from 5 to 100 (`k = 3, …, 10`), the
-- divisors `1 2` from 1 to 20 (`k = 1, …, 4`, then `k = 1, …, 3`), the words from 1 to 1000 (the
-- words 0 to 15) and every denominator from 10 to 50; and the steps of the blocks of the last.
#guard
  let plan (s : Shape) (lo hi : Nat) : BlockPlan := Id.run (s.blockPlan lo hi)
  let p := plan .all 10 50
  (plan .squares 5 100).segs == #[(3, 10)] && (plan .squares 5 100).segBlock == #[0, 1] &&
    (plan (.squares1 [] [1, 2]) 1 20).segs == #[(1, 4), (1, 3)] &&
    (plan (.squares1 [] [1, 2]) 1 20).segBlock == #[0, 1, 2] &&
    (plan (.words [] [] false none 1) 1 1000).segs == #[(0, 15)] &&
    p.segs == #[(10, 50)] && p.len == 16 && p.nblocks == 3 &&
    (List.range 3).map (fun i ↦ Id.run (p.steps i)) == [(0, 10, 25), (0, 26, 41), (0, 42, 50)]

-- The decision in force: the last whose first block is at most the block.
#guard
  let decs : Array Decision := #[⟨0, 5, 7⟩, ⟨40, 6, 9⟩, ⟨45, 4, 4⟩]
  [0, 39, 40, 44, 45, 1000].map (fun i ↦ Id.run (findDecision decs i)) == [0, 0, 1, 1, 2, 2]

-- The fold of the counters: those of the second stage on restart under a new end of the second
-- stage, with the words swept so far kept.
#guard
  let c : RunCounts :=
    { words := 100, arrays := 10, bits := 5, coprime := 4, checks := 3, sifts := 2, words2 := 7,
      sp2 := 12 }
  let k : Counters := { words := 1, arrays := 1, bits := 1, coprime := 1, checks := 1, sifts := 1 }
  let same := c.fold 12 k
  let other := c.fold 13 k
  same.words == 101 && same.bits == 6 && same.words2 == 7 && same.sp2 == 12 &&
    other.words == 101 && other.arrays == 11 && other.bits == 1 && other.sifts == 1 &&
    other.words2 == 100 && other.sp2 == 13

-- No correction while the rates do not tell: too few words, arrays or numerators, or `sp2 ≤ sp1`;
-- the next correction at twice the words, wrapping.
#guard
  let es : Array SieveEntry := (Array.range 8).map fun n ↦
    { p := 3 + 2 * n, factors := [], magic := 0, bias := 0, rbainv := 0, dinv := #[],
      ref := .prime 0, init := .sieve1, r := 0.5, nf := 0 }
  let c : RunCounts := { words := 2000000, arrays := 999, bits := 300, sp2 := 4 }
  let P : Params :=
    { lookedAt := 0, sp1 := 2, sp2 := 4, sp3 := 6, maxForbidden := 64, jacobi := true
      adaptAt := 0 }
  (Id.run (adaptRates es c 2)).isNone &&
    (Id.run (adaptRates es { c with arrays := 1000, words := 0 } 2)).isNone &&
    (Id.run (adaptRates es { c with arrays := 1000, bits := 199 } 2)).isNone &&
    (Id.run (adaptRates es { c with arrays := 1000, words2 := 2000000 } 2)).isNone &&
    (Id.run (adaptRates es { c with arrays := 1000 } 4)).isNone &&
    (Id.run (adaptRates es { c with arrays := 1000 } 2)).isSome &&
    Id.run (adaptPrimes {} P es c 4 6) == (4, 6, 4000000) &&
    (Id.run (adaptPrimes {} P es { c with words := 2 ^ 63 } 4 6)).2.2 == 0

-- The denominators that the blocks visit, with a step that records them: the squares from 5 to 100
-- whose class admits a numerator, in blocks of 16 steps.
#guard
  let cls : Vector NumClass 64 := .ofFn fun j ↦ ⟨if j.val % 2 = 1 then 1 else 0, 0, 0, none⟩
  let rec' (b : Nat) (st : BlockState (Array Nat)) : Id (BlockState (Array Nat)) :=
    ({ st.1 with info := st.1.info.push b }, st.2)
  (Id.run (squaresBlock rec' cls 3 10 (⟨#[], 0, false⟩, {}, {}))).1.info == #[9, 25, 49, 81] &&
    (Id.run (allBlock rec' cls 10 20 (⟨#[], 0, false⟩, {}, {}))).1.info ==
      #[11, 13, 15, 17, 19]

-- The denominators that the blocks of a run of the shape `s` visit, block by block, as the loops of
-- the shapes reach them (`Ratpoints.Sieve.Shape.blockLoop`), with the tests of the shapes, recorded
-- by a step that sifts nothing.
private def visited (s : Shape) (cls : Vector NumClass 64) (db : UInt64) (bLow bHigh : Nat) :
    Id (List Nat) := do
  let plan ← s.blockPlan bLow bHigh
  let rec' (b : Nat) (st : BlockState (Array Nat)) : Id (BlockState (Array Nat)) :=
    ({ st.1 with info := st.1.info.push b }, st.2)
  let mut st : BlockState (Array Nat) := (⟨#[], 0, false⟩, {}, {})
  for i in [0:plan.nblocks] do
    let (seg, a, e) ← plan.steps i
    st ← s.blockLoop rec' cls db plan seg a e bLow bHigh st
  return st.1.info.toList

-- The denominators of the square shapes, every class admitted: the squares up to 20 and from 5 to
-- 100; for the divisors `1 2` at 20, `1, 4, 9, 16`, then `2, 8, 18`; and for `1 2 1031` at 1300,
-- the squares, twice the squares, then `1031`, the blocks of 16 steps cutting the segments.
#guard
  let cls : Vector NumClass 64 := .replicate 64 ⟨1, 0, 0, none⟩
  Id.run (visited .squares cls 0 1 20) == [1, 4, 9, 16] &&
    Id.run (visited .squares cls 0 5 100) == [9, 16, 25, 36, 49, 64, 81, 100] &&
    Id.run (visited (.squares1 [] [1, 2]) cls 0 1 20) == [1, 4, 9, 16, 2, 8, 18] &&
    Id.run (visited (.squares1 [] [1, 2, 1031]) cls 0 1 1300) ==
      (List.range' 1 36).map (fun k ↦ k * k) ++ (List.range' 1 25).map (fun k ↦ 2 * k * k) ++ [1031]

-- The denominators that the words leave against their rule: `b` from `bLow` to `bHigh`, in
-- increasing order, whose class admits a numerator and which no forbidden divisor tested with words
-- divides, for `1 2 3 4 5 6 7`, with the forbidden divisors that the primes of the table give
-- (`Ratpoints.Sieve.forbidden` from the first prime on), and ranges within one word and over
-- several, with the positions of the divisors set at the first word of each block.
#guard
  let c : List Int := [1, 2, 3, 4, 5, 6, 7]
  let db := denBits (Id.run (twoAdic c 6))
  let forb := (Id.run (forbidden c 6 0 64 1000 #[] #[])).1
  let cls : Vector NumClass 64 := .replicate 64 ⟨1, 0, 0, none⟩
  ([(1, 1000), (1, 63), (64, 64), (5, 70), (130, 520), (1, 20000)] : List (Nat × Nat)).all
    fun (lo, hi) ↦
    Id.run (visited (.words forb [] false none 1) cls db lo hi) ==
      (List.range' lo (hi + 1 - lo)).filter fun b ↦
        db.toBitVec.getLsbD (b % 64) && forb.all fun e ↦ b % e.p != 0

-- The run as ratpoints chooses and runs it under `-p 30`: the shape and the denominators that the
-- dump says the run sifts, for `1 2` at 20 (the divisors), `1 2 3 4 5 6 7` at 100 (the words with
-- the tables of the Jacobi test), `1 0 0 0 -1031` at 100 (the words with the binary algorithm; the
-- first twelve denominators), `1 1 1 1 1 1 1` at 100 with no forbidden divisors (`-F 0`, every
-- denominator) and `-2 0 0 1` at 130 (the squares); the forbidden divisors those that the loop of
-- the tables over the first 30 primes finds while fewer than `F` are found, then those of the
-- further primes (`Ratpoints.Sieve.forbidden`).
#guard
  let forbs (c : List Int) (d F H : Nat) : List ForbiddenEntry × List ForbiddenVal := Id.run do
    let mut ba : Array ForbiddenEntry := #[]
    let mut val : Array ForbiddenVal := #[]
    for p in primeTable.toList.take 30 do
      let some (t, cm, _, _) ← examinePrime? c d p true | return ([], [])
      if ba.size + val.size < F then
        match ← forbiddenOfPrime c d p H cm t.isFSquare[p]! with
        | some (.inl f) => ba := ba.push f
        | some (.inr f) => val := val.push f
        | none => pure ()
    forbidden c d 30 F H ba val
  let sifted (c : List Int) (d H F : Nat) : Nat × List Nat :=
    let lcf := c.getD d 0
    let useJacobi := d % 2 == 0 && !Setup.isSquare lcf
    let us1 := if d % 2 == 1 && lcf.natAbs != 1 then Id.run (Setup.setupUs1 c d H) else none
    let nb := Id.run (twoAdic c d)
    let (forb, forbVal) := if d % 2 == 0 then forbs c d F H else ([], [])
    let checkDenom := d % 2 == 0 && (!forb.isEmpty || !forbVal.isEmpty || useJacobi)
    let shape := (Id.run (runSetup (d % 2 == 1 && lcf.natAbs == 1) us1 checkDenom useJacobi forb
      forbVal lcf H H [])).1
    let code := match shape with | .squares => 0 | .squares1 .. => 1 | .words .. => 2 | .all => 3
    (code, Id.run (visited shape (Id.run (numClasses nb)).1 (denBits nb) 1 H))
  sifted [1, 2] 1 20 64 == (1, [1, 9, 2, 8, 18]) &&
    sifted [1, 2, 3, 4, 5, 6, 7] 6 100 64 ==
      (2, [1, 3, 7, 9, 19, 21, 27, 29, 31, 37, 47, 53, 57, 59, 63, 81, 83, 87, 93]) &&
    (sifted [1, 0, 0, 0, -1031] 4 100 64).1 == 2 &&
    (sifted [1, 0, 0, 0, -1031] 4 100 64).2.take 12 == [1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13] &&
    sifted [1, 1, 1, 1, 1, 1, 1] 6 100 0 == (3, (List.range' 1 100).filter fun b ↦
      b % 2 = 1 || b % 8 = 0) &&
    sifted [-2, 0, 0, 1] 3 130 64 == (0, (List.range' 1 11).map fun k ↦ k * k)

-- The two blocks of `1 2` at 20 in the divisor shape, one after the other, with the first 30 primes
-- of the table: the affine points that `ratpoints '1 2' 20 -q` prints, by the divisors `1` (block
-- `0`, the denominators 1 and 9) and `2` (block `1`, the denominators 2, 8 and 18), so with the
-- denominator 9 before 2; each block reports the decision in force for it and counts its sifts from
-- zero.
#guard
  let c : List Int := [1, 2]
  let (cls, db) := Id.run (numClasses (Id.run (twoAdic c 1)))
  let entries := (primeTable.toList.take 30).filterMap fun p ↦
    (Id.run (examinePrime? c 1 p true)).map fun (e, _) ↦ (⟨p, [.prime e], magic p,
      p * ((rowBias + p - 1) / p), e.inverses[mulMod rbaLength p (magic p)]!, #[], .prime p,
      sieveInit p, 0.0, 0⟩ : SieveEntry)
  let offsets := Array.replicate (Id.run (numPackings cls) * entries.length) 0
  let (cls, entries, offsets) := Id.run (classOffsets cls entries offsets)
  let shape : Shape := .squares1 [⟨2, 1, 2⟩] [1, 2]
  let plan := Id.run (shape.blockPlan 1 20)
  let decs : Array Decision := #[⟨0, 22, entries.length⟩, ⟨1, 15, 20⟩]
  let iv := Id.run (exactBounds [((Double.ofInt64 20).neg, Double.ofInt64 20)] 20 20)
  let block (i : Nat) (st : Delivery (Array (Int × Int × Int)) × RowStore) :=
    Id.run (runBlock appendPoint c 1 20 1 {} 11 entries (entries.toArray.map (·.magic)) cls offsets
      db shape iv 1 20 plan decs i st.2 st.1)
  let (r0, s0, k0) := block 0 (⟨#[], 0, false⟩, entries.foldl (fun s e ↦ e.addTables s) {})
  let (r1, _, k1) := block 1 (r0, s0)
  plan.nblocks == 2 && (k0.dec, k0.sp2, k0.sp3) == (0, 22, entries.length) &&
    (k1.dec, k1.sp2, k1.sp3) == (1, 15, 20) && k0.cnt.sifts == 2 && k1.cnt.sifts == 3 &&
    r1.info.toList ==
      [(0, 1, 1), (0, -1, 1), (4, 3, 1), (4, -3, 1), (12, 5, 1), (12, -5, 1), (-4, 3, 9),
        (-4, -3, 9), (8, 15, 9), (8, -15, 9), (20, 21, 9), (20, -21, 9), (-1, 0, 2), (3, 4, 2),
        (3, -4, 2), (15, 8, 2), (15, -8, 2), (-3, 4, 8), (-3, -4, 8), (5, 12, 8), (5, -12, 8),
        (-5, 12, 18), (-5, -12, 18), (7, 24, 18), (7, -24, 18)]

-- The run of `1 2` at 20 in the divisor shape, its two blocks sifted in turn: the affine points
-- that `ratpoints '1 2' 20 -q` prints, by the divisors `1` and `2`, so with the denominator 9
-- before 2; and the cut points of the choice, which the short run does not correct, as those of the
-- last block folded.
#guard
  let c : List Int := [1, 2]
  let (cls, db) := Id.run (numClasses (Id.run (twoAdic c 1)))
  let entries := (primeTable.toList.take 30).filterMap fun p ↦
    (Id.run (examinePrime? c 1 p true)).map fun (e, _) ↦ (⟨p, [.prime e], magic p,
      p * ((rowBias + p - 1) / p), e.inverses[mulMod rbaLength p (magic p)]!, #[], .prime p,
      sieveInit p, 0.0, 0⟩ : SieveEntry)
  let offsets := Array.replicate (Id.run (numPackings cls) * entries.length) 0
  let (cls, entries, offsets) := Id.run (classOffsets cls entries offsets)
  let P : Params :=
    { lookedAt := 30, sp1 := 11, sp2 := 22, sp3 := entries.length, maxForbidden := 64
      jacobi := true, adaptAt := ~~~0 }
  let (r, sp2, sp3) := Id.run (sieveRun appendPoint c 1 20 1 {} {} P entries
      (entries.toArray.map (·.magic)) cls offsets db (.squares1 [⟨2, 1, 2⟩] [1, 2])
      (Id.run (exactBounds [((Double.ofInt64 20).neg, Double.ofInt64 20)] 20 20)) 1 20
      (entries.foldl (fun s e ↦ e.addTables s) {}) ⟨#[], 0, false⟩)
  sp2 == 22 && sp3 == entries.length && r.info.toList ==
    [(0, 1, 1), (0, -1, 1), (4, 3, 1), (4, -3, 1), (12, 5, 1), (12, -5, 1), (-4, 3, 9), (-4, -3, 9),
      (8, 15, 9), (8, -15, 9), (20, 21, 9), (20, -21, 9), (-1, 0, 2), (3, 4, 2), (3, -4, 2),
      (15, 8, 2), (15, -8, 2), (-3, 4, 8), (-3, -4, 8), (5, 12, 8), (5, -12, 8), (-5, 12, 18),
      (-5, -12, 18), (7, 24, 18), (7, -24, 18)]

end Sieve

end Ratpoints

end

/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.Denominators

-- The `#guard` examples run code of the imported modules at compile time.
meta import Ratpoints.Model.Denominators

/-!
# The blocks of the run

The loop over the denominators of `find_points_work_1`, in blocks: the steps of the shape of the
run (`Ratpoints.Sieve.Shape`), the `k` of the squares `k ^ 2`, the `k` of each divisor `s` of the
divisor shape, one segment of steps per divisor, the words of 64 denominators, or the denominators
themselves, are cut into blocks of consecutive steps of one length
(`Ratpoints.Sieve.Shape.segments`, `Ratpoints.Sieve.Shape.blockPlan`), about
`Ratpoints.blocksWanted` blocks of at least `Ratpoints.blockMin` steps, the steps of a block found
from the segment that holds it (`Ratpoints.Sieve.BlockPlan.steps`); the loop of each shape goes over
the steps of a block (`Ratpoints.Sieve.Shape.blockLoop`), its denominators in the order of the loop,
each that passes the tests of the shape handed to a step, which sifts it
(`Ratpoints.Sieve.siftDen`), and returns when the callback has stopped the search. The run of the
model (`Ratpoints.Sieve.sieveRun`) does not call them yet: until the run over the blocks of stage I,
with one block sifted at a time and the correction of the moduli between the blocks, it lists the
denominators of its shape (`Ratpoints.Sieve.Shape.dens`) and sifts them one after the other.

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

/-! ### Examples -/

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

end Sieve

end Ratpoints

end

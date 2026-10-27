/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.Cli
public import Ratpoints.Proof.CliNumbers
public import Ratpoints.Proof.Region
public import Ratpoints.Spec.Basic
public import Ratpoints.Spec.Sturm

import Ratpoints.Mathlib.Algebra.Order.Field.Basic
import Ratpoints.Proof.Containers
import Ratpoints.Proof.Delivery
import Ratpoints.Proof.Output
import Ratpoints.Proof.Params

/-!
# The output of the program

What the program `ratpoints-lean` prints for the points of a successful search. Its callback
`Ratpoints.Cli.process`, called for the points of a list `L` in turn from the data
`Ratpoints.Cli.Data.ofOutput u o` of the settings `u` of the output and the options `o` of the
search, counts the points of `L` that it keeps (`Ratpoints.Cli.Data.keeps`: all but those at
infinity under `-i` and the affine ones outside the search intervals of the command line), of these
only the first under `-1`, at which it stops the search (`Ratpoints.Cli.countedPoints`), and prints
them unless `-z`, each after the string before the points (`-fs`) if it is the first and else after
the string between them (`-fm`), in the format of `-f`: so the text printed, with the string before
the points when no point was printed, is the string before the points followed by the formatted
points with the string between them in between
(`Ratpoints.Cli.out_append_deliver_process_ofOutput`), and the count is their number
(`Ratpoints.Cli.total_deliver_process`). By the protocol of the delivery
(`Ratpoints.map_findPointsWith_eq_map_findPoints`), which says that for every value of the options
of the sieve the search delivers to a callback the points of `Ratpoints.findPoints` in their order
until a call stops it, this is what `Ratpoints.Cli.run` prints between the head of the report and
its end, without `-v`, whose report of the library comes between the points; under `-q` it is all
that it prints, with the string after the points (`-fe`) at the end, and under `-1` the one point
printed is the first point of the list of `Ratpoints.findPoints` that the callback keeps. The search
runs on the search intervals of the command line joined (`Ratpoints.Cli.joinIntervals`).

The search region of the command line: the reading of `-l` and `-u` keeps an invariant
(`Ratpoints.Cli.Intervals.ReadsWF`: the exact ends are those of increasing and disjoint intervals
`l ≤ u`, checked by error 7, and the doubles of each interval hold it as far as the search goes),
which `Ratpoints.Cli.Intervals.lower`, `Ratpoints.Cli.Intervals.upper` and
`Ratpoints.Cli.Intervals.complete` keep, over the options by `Ratpoints.Cli.checkOptions_preserves`;
so the test of the callback is the exact search region of the command line, and the joined intervals
hold it for the numbers `|x| ≤ H` of the search. For words of fewer than `2 ^ 56` characters, the
doubles of the lower ends after the first are moreover the largest doubles at most their ends
(`Ratpoints.Cli.Intervals.LowerMax`), which makes the joined intervals well formed: the library
never refuses them, and error 9 is unreachable from the command line.

## Main definitions

* `Ratpoints.Cli.Data.keeps`, `Ratpoints.Cli.countedPoints`: the points that the callback keeps, and
  those that it counts.
* `Ratpoints.Cli.IntervalOf`, `Ratpoints.Cli.Intervals.ReadsWF`, `Ratpoints.Cli.Intervals.LowerMax`:
  the invariants of the reading of the search intervals of the command line.

## Main statements

* `Ratpoints.Cli.deliver_process`: the delivery of a list to the callback of the program.
* `Ratpoints.Cli.out_append_deliver_process_ofOutput`, `Ratpoints.Cli.total_deliver_process`: the
  text that the callback prints and the count.
* `Ratpoints.Cli.run_eq_of_findPointsWith_eq_ok`, `Ratpoints.Cli.total_eq_of_findPointsWith_eq_ok`:
  what the program prints for a successful search without `-v`, and the count that its report
  gives.
* `Ratpoints.Cli.findPointsVerbose_eq_ok_of_findPointsWith_eq_ok`,
  `Ratpoints.Cli.verbose_eq_false_of_input_eq_ok`: the search with the print channel that prints
  nothing, which the program runs without `-v`, and `-q` cancels `-v`.
* `Ratpoints.Cli.run_eq_of_findPoints_eq_ok`: what the program prints under `-q`.
* `Ratpoints.Cli.run_eq_of_onePoint`: under `-q -1`, the first point that the callback keeps.
* `Ratpoints.Cli.reads_of_input_eq_ok`: the search intervals of a command line that the program
  accepts.
* `Ratpoints.Cli.inRegion_iff_of_input_eq_ok`,
  `Ratpoints.Cli.inIntervals_joinIntervals_of_inExactRegion`,
  `Ratpoints.Cli.intervalsWF_joinIntervals_of_input_eq_ok`: the test of the callback is the exact
  search region of the command line (`Ratpoints.Cli.InExactRegion`), and the joined search
  intervals hold it for `|x| ≤ H` and, for words of fewer than `2 ^ 56` characters, are well
  formed.
* `Ratpoints.Cli.mem_filter_keeps_iff_of_input_eq_ok`: assuming Sturm's theorem when the Sturm step
  is on, the points that the program prints are exactly the points in the exact search region of
  its command line.
-/

@[expose] public section

namespace Ratpoints.Cli

open Double

/-! ### The points that the callback counts -/

/-- Whether the callback `Ratpoints.Cli.process` of the program with the data `d` keeps the point
`p = (x, y, z)`, counting it, printing it unless `-z` and stopping the search at it under `-1`:
a point at infinity (`z = 0`) unless the points at infinity are passed over (`-i`), and an affine
point when the command line gives no search intervals or `x / z` lies in one of them
(`Ratpoints.Cli.inRegion`). -/
def Data.keeps (d : Data) (p : ℤ × ℤ × ℤ) : Bool :=
  (d.pointsAtInfty || p.2.2 != 0) &&
    (p.2.2 == 0 || d.numInter == 0 || Id.run (inRegion p.1 p.2.2 d.ends d.numInter))

/-- The points of the list `L`, in their order, that the callback `Ratpoints.Cli.process` of the
program counts when it is called for the points of `L` in turn, from data that keeps the points
that pass `keep` (`Ratpoints.Cli.Data.keeps`) and whose setting of one point is `onePoint`, while it
has not stopped the search: the points of `L` that pass `keep`, and of these only the first when
one point is enough (`-1`, `onePoint` set), at which the callback stops the search. -/
def countedPoints (keep : ℤ × ℤ × ℤ → Bool) (onePoint : Bool) (L : List (ℤ × ℤ × ℤ)) :
    List (ℤ × ℤ × ℤ) :=
  let K := L.filter keep
  if onePoint then K.take 1 else K

theorem countedPoints_nil (keep : ℤ × ℤ × ℤ → Bool) (onePoint : Bool) :
    countedPoints keep onePoint [] = [] := by
  cases onePoint <;> rfl

theorem countedPoints_cons_of_not_keep {keep : ℤ × ℤ × ℤ → Bool} {p : ℤ × ℤ × ℤ}
    (h : keep p = false) (onePoint : Bool) (L : List (ℤ × ℤ × ℤ)) :
    countedPoints keep onePoint (p :: L) = countedPoints keep onePoint L := by
  simp [countedPoints, h]

theorem countedPoints_cons_of_keep {keep : ℤ × ℤ × ℤ → Bool} {p : ℤ × ℤ × ℤ}
    (h : keep p = true) (onePoint : Bool) (L : List (ℤ × ℤ × ℤ)) :
    countedPoints keep onePoint (p :: L) =
      if onePoint then [p] else p :: countedPoints keep onePoint L := by
  cases onePoint <;> simp [countedPoints, h]

/-! ### What the callback prints -/

/-- The data `d` of the callback `Ratpoints.Cli.process` after it has printed the point
`p = (x, y, z)`: `d` itself when no point is printed (`-z`), and otherwise `d` with the flag
`printBetween` set and with the text of the point appended to the text printed so far, the string
between the points (`-fm`) if a point was printed before and else the string before the points
(`-fs`), then the point in the format (`Ratpoints.Cli.formatPoint`). This is what a call of the
callback that does not pass over the point does to its data. -/
def Data.printPoint (d : Data) (p : ℤ × ℤ × ℤ) : Data :=
  if d.noOutput then d
  else { d with
    printBetween := true
    out := d.out ++ printString (if d.printBetween then d.stringBetween else d.stringBefore) ++
      formatPoint d.noY p.1 p.2.2 p.2.1 d.pf.toList }

namespace Data

theorem printPoint_of_noOutput {d : Data} (h : d.noOutput = true) (p : ℤ × ℤ × ℤ) :
    d.printPoint p = d := by
  simp [printPoint, h]

theorem printPoint_of_not_noOutput {d : Data} (h : d.noOutput = false) (p : ℤ × ℤ × ℤ) :
    d.printPoint p = { d with
      printBetween := true
      out := d.out ++ printString (if d.printBetween then d.stringBetween else d.stringBefore) ++
        formatPoint d.noY p.1 p.2.2 p.2.1 d.pf.toList } := by
  simp [printPoint, h]

@[simp]
theorem onePoint_printPoint (d : Data) (p : ℤ × ℤ × ℤ) :
    (d.printPoint p).onePoint = d.onePoint := by
  cases h : d.noOutput <;> simp [printPoint, h]

@[simp]
theorem keeps_printPoint (d : Data) (p : ℤ × ℤ × ℤ) : (d.printPoint p).keeps = d.keeps := by
  funext q
  cases h : d.noOutput <;> simp [printPoint, keeps, h]

theorem foldl_printPoint_of_noOutput {d : Data} (h : d.noOutput = true) (K : List (ℤ × ℤ × ℤ)) :
    K.foldl printPoint d = d := by
  induction K with
  | nil => rfl
  | cons p K ih => rwa [List.foldl_cons, printPoint_of_noOutput h]

/-- Once a point was printed, each point printed appends the string between the points and the
point in the format. -/
theorem foldl_printPoint_of_printBetween {d : Data} (hn : d.noOutput = false)
    (hb : d.printBetween = true) (K : List (ℤ × ℤ × ℤ)) :
    K.foldl printPoint d = { d with
      out := d.out ++ String.join (K.map fun p ↦
        printString d.stringBetween ++ formatPoint d.noY p.1 p.2.2 p.2.1 d.pf.toList) } := by
  induction K generalizing d with
  | nil => simp [String.join_nil]
  | cons p K ih =>
    rw [List.foldl_cons, ih (by simp [printPoint_of_not_noOutput hn, hn])
      (by simp [printPoint_of_not_noOutput hn])]
    simp [printPoint_of_not_noOutput hn, hb, String.join_cons, String.append_assoc]

/-- From data that has printed nothing, the text printed for the points of `K`, with the string
before the points when no point was printed, is the string before the points followed by the
points printed in the format, with the string between them in between: none under `-z`. -/
theorem out_append_foldl_printPoint {d : Data} (hb : d.printBetween = false) (ho : d.out = "")
    (K : List (ℤ × ℤ × ℤ)) :
    (K.foldl printPoint d).out ++
      (if (K.foldl printPoint d).printBetween then "" else printString d.stringBefore) =
      printString d.stringBefore ++ (printString d.stringBetween).intercalate
        ((if d.noOutput then [] else K).map fun p ↦
          formatPoint d.noY p.1 p.2.2 p.2.1 d.pf.toList) := by
  cases hn : d.noOutput
  · cases K with
    | nil => simp [hb, ho]
    | cons p K =>
      rw [List.foldl_cons, foldl_printPoint_of_printBetween
        (by simp [printPoint_of_not_noOutput hn, hn]) (by simp [printPoint_of_not_noOutput hn])]
      simp [printPoint_of_not_noOutput hn, hb, ho, String.intercalate_cons_eq_append_join,
        Function.comp_def, String.append_assoc]
  · rw [foldl_printPoint_of_noOutput hn]
    simp [hb, ho]

end Data

/-! ### The delivery to the callback -/

/-- A call of the callback for a point `p = (x, y, z)` that it keeps (`Ratpoints.Cli.Data.keeps`)
prints it (`Ratpoints.Cli.Data.printPoint`), counts it and stops the search under `-1`. -/
theorem call_process_of_keep {r : Delivery Data} {p : ℤ × ℤ × ℤ} (h : r.info.keeps p = true) :
    r.call process p.1 p.2.2 p.2.1 = ⟨r.info.printPoint p, r.total + 1, r.info.onePoint⟩ := by
  simp only [Data.keeps, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  simp only [Delivery.call, process, Data.printPoint]
  split_ifs <;> simp_all [Nat.pos_iff_ne_zero]

theorem call_process_of_not_keep {r : Delivery Data} {p : ℤ × ℤ × ℤ}
    (h : r.info.keeps p = false) :
    r.call process p.1 p.2.2 p.2.1 = ⟨r.info, r.total, false⟩ := by
  simp only [Data.keeps, Bool.and_eq_false_iff, Bool.or_eq_false_iff, bne_eq_false_iff_eq,
    beq_eq_false_iff_ne, ne_eq] at h
  simp only [Delivery.call, process]
  split_ifs <;> grind

/-- The delivery of the points of `L` to the callback of the program from the data `d` and the
count `t`, with the flag of the stop clear: the points that the callback counts
(`Ratpoints.Cli.countedPoints`) are printed in turn and counted, and the search is stopped when one
point is enough and `L` has a point that the callback keeps (`Ratpoints.Cli.Data.keeps`). -/
theorem deliver_process (d : Data) (t : ℤ) (L : List (ℤ × ℤ × ℤ)) :
    (⟨d, t, false⟩ : Delivery Data).deliver process L =
      ⟨(countedPoints d.keeps d.onePoint L).foldl Data.printPoint d,
        t + (countedPoints d.keeps d.onePoint L).length, d.onePoint && L.any d.keeps⟩ := by
  -- The delivery is passed to the lemmas of a call by name: unifying its projection with the data
  -- would unfold `Ratpoints.Cli.Data.keeps` and the loop of `Ratpoints.Cli.inRegion`.
  induction L generalizing d t with
  | nil => simp [countedPoints_nil]
  | cons p L ih =>
    simp only [Delivery.deliver_cons_of_quit_eq_false (r := ⟨d, t, false⟩) process rfl]
    cases hk : d.keeps p
    · simp only [call_process_of_not_keep (r := ⟨d, t, false⟩) hk, ih,
        countedPoints_cons_of_not_keep hk]
      simp [hk]
    · simp only [call_process_of_keep (r := ⟨d, t, false⟩) hk, countedPoints_cons_of_keep hk]
      cases h1 : d.onePoint
      · simp only [ih, Data.keeps_printPoint, Data.onePoint_printPoint, h1]
        simp [hk]
        lia
      · simp only [Delivery.deliver_of_quit (r := ⟨_, _, true⟩) process rfl]
        simp [hk]

theorem total_deliver_process (d : Data) (t : ℤ) (L : List (ℤ × ℤ × ℤ)) :
    ((⟨d, t, false⟩ : Delivery Data).deliver process L).total =
      t + (countedPoints d.keeps d.onePoint L).length := by
  rw [deliver_process]

/-- The text that the callback of the program prints for the points of `L`, from the data of the
settings `u` of the output and the options `o` of the search, with the string before the points
when it printed no point, as the program prints it: the string before the points, then the points
that the callback counts (`Ratpoints.Cli.countedPoints`), in the format, with the string between
the points in between, none under `-z`. -/
theorem out_append_deliver_process_ofOutput (u : Output) (o : Options) (L : List (ℤ × ℤ × ℤ)) :
    ((⟨.ofOutput u o, 0, false⟩ : Delivery Data).deliver process L).info.out ++
      (if ((⟨.ofOutput u o, 0, false⟩ : Delivery Data).deliver process L).info.printBetween
        then "" else printString u.stringBefore) =
      printString u.stringBefore ++ (printString u.stringBetween).intercalate
        ((if u.noOutput then [] else countedPoints (Data.ofOutput u o).keeps u.onePoint L).map
          fun p ↦ formatPoint (o.noCheck || o.noY) p.1 p.2.2 p.2.1
            (u.printFormat.getD "").toList) := by
  rw [deliver_process]
  exact Data.out_append_foldl_printPoint rfl rfl _

/-! ### The program -/

theorem preamble_eq_empty_of_quiet (c : List ℤ) (H : ℕ) {u : Output} (hq : u.quiet = true)
    (dom : List (Double × Double)) :
    preamble c H u dom = "" := by
  simp [preamble, hq]

theorem report_eq_empty_of_quiet {σ : Type} (s : SieveOptions) (o : Options) {u : Output}
    (hq : u.quiet = true) (r : Outcome σ) :
    report s o u r = "" := by
  simp [report, hq]

/-- A search with the print channel that prints nothing returns the outcome of
`Ratpoints.findPointsVerbose` with that channel. -/
theorem findPointsVerbose_eq_ok_of_findPointsWith_eq_ok {c : List ℤ} {H : ℕ} {s : SieveOptions}
    {o : Options} {σ : Type} {process : ℤ → ℤ → ℤ → σ → Answer σ} {info : σ} {r : Outcome σ}
    (hr : findPointsWith c H s o process info = .ok r) :
    findPointsVerbose c H s o process info (fun _ s ↦ s) = .ok r := by
  revert hr
  rw [findPointsWith]
  cases findPointsVerbose c H s o process info (fun _ s ↦ s) <;> simp [Except.mapError]

/-- What the program prints for a command line that it reads as the coefficients `c`, the height
bound `H`, the options `s` of the sieve, the options `o` of the search and the settings `u` of the
output, without `-v`, when the search `Ratpoints.findPoints` with the program's array size on the
search intervals of the command line joined (`Ratpoints.Cli.joinIntervals`) returns the list `L` and
the search with the callback of the program the outcome `r`: the head of the report, the string
before the points, the points of `L` that the callback counts (`Ratpoints.Cli.countedPoints`: those
that it keeps, `Ratpoints.Cli.Data.keeps`, only the first of these under `-1`) in the format, with
the string between them in between, none under `-z`, the string after the points and the end of the
report; the protocol of the delivery holds for every value of the options
(`Ratpoints.map_findPointsWith_eq_map_findPoints`). -/
theorem run_eq_of_findPointsWith_eq_ok {args : List String} {c : List ℤ} {H : ℕ}
    {s : SieveOptions} {o : Options} {u : Output} {r : Outcome Data} {L : List (ℤ × ℤ × ℤ)}
    (hi : input args = .ok (c, H, s, o, u)) (hv : u.verbose = false)
    (hr : findPointsWith c H { s with arraySize := defaultArraySize }
      { o with domain := Id.run (joinIntervals o.domain) } process (.ofOutput u o) = .ok r)
    (hL : findPoints c H { s with arraySize := defaultArraySize }
      { o with domain := Id.run (joinIntervals o.domain) } = .ok L) :
    run args = (preamble c H u o.domain ++ printString u.stringBefore ++
      (printString u.stringBetween).intercalate
        ((if u.noOutput then [] else countedPoints (Data.ofOutput u o).keeps u.onePoint L).map
          fun p ↦ formatPoint (o.noCheck || o.noY) p.1 p.2.2 p.2.1
            (u.printFormat.getD "").toList) ++
      printString u.stringAfter ++
        report s { o with domain := Id.run (joinIntervals o.domain) } u r, 0) := by
  simp only [run, hi, hv, Bool.false_eq_true, ↓reduceIte,
    findPointsVerbose_eq_ok_of_findPointsWith_eq_ok hr]
  rw [(info_total_eq_of_findPointsWith_eq_ok hr hL).1,
    String.append_assoc (s₁ := preamble c H u o.domain), out_append_deliver_process_ofOutput,
    ← String.append_assoc]

/-- The count of the points that the report of the program gives: the number of the points of the
list of `Ratpoints.findPoints` that the callback of the program counts
(`Ratpoints.Cli.countedPoints`), for every value of the options of the sieve. -/
theorem total_eq_of_findPointsWith_eq_ok {c : List ℤ} {H : ℕ} {s : SieveOptions} {o o' : Options}
    {u : Output} {r : Outcome Data} {L : List (ℤ × ℤ × ℤ)}
    (hr : findPointsWith c H s o' process (.ofOutput u o) = .ok r)
    (hL : findPoints c H s o' = .ok L) :
    r.total = (countedPoints (Data.ofOutput u o).keeps u.onePoint L).length := by
  rw [(info_total_eq_of_findPointsWith_eq_ok hr hL).2, total_deliver_process, Int.zero_add]
  rfl

theorem le_and_lt_of_heightBound_eq_ok {h : String} {H : ℕ} (hH : heightBound h = .ok H) :
    1 ≤ H ∧ H < 2 ^ 63 := by
  simp only [heightBound] at hH
  split at hH
  · rename_i n hn
    obtain rfl := Except.ok.inj hH
    simp only [longOfString?, Option.filter_eq_some_iff, Bool.and_eq_true, decide_eq_true_eq] at hn
    lia
  · cases hH

/-- What a command line that the program accepts gives: the options are words of the command line,
the height bound is a positive `long`, the reading of the options from the defaults succeeds, the
search intervals of the options and the exact ends of the settings of the output are those of the
intervals read and completed (`Ratpoints.Cli.Intervals.complete`), and `-q` cancels `-v`. -/
theorem exists_checkOptions_eq_ok_of_input_eq_ok {args : List String} {c : List ℤ} {H : ℕ}
    {s : SieveOptions} {o : Options} {u : Output} (hi : input args = .ok (c, H, s, o, u)) :
    ∃ os iv, (∀ a ∈ os, a ∈ args) ∧ 1 ≤ H ∧ H < 2 ^ 63 ∧
      (∃ s' o' u', checkOptions H ({}, { bHigh := H }, {}, {}) os = .ok (s', o', u', iv)) ∧
      o.domain = (iv.complete H).domain.toList.take (iv.complete H).numInter ∧
      u.ends = (iv.complete H).ends ∧ (u.quiet = true → u.verbose = false) := by
  match args, hi with
  | s0 :: h :: os, hi =>
    obtain ⟨c0, -, hi⟩ := Except.bind_eq_ok hi
    obtain ⟨H0, hH, hi⟩ := Except.bind_eq_ok hi
    obtain ⟨⟨s1, o1, u1, iv⟩, hk, hi⟩ := Except.bind_eq_ok hi
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hi
    obtain ⟨-, rfl, -, rfl, rfl⟩ := hi
    exact ⟨os, iv, fun a ha ↦ .tail _ (.tail _ ha), (le_and_lt_of_heightBound_eq_ok hH).1,
      (le_and_lt_of_heightBound_eq_ok hH).2, ⟨s1, o1, u1, hk⟩, rfl, rfl, fun hq ↦ by simp_all⟩

/-- The program reads `-v` only without `-q`: under `-q` the settings of the output have the flag of
the report of the library clear. -/
theorem verbose_eq_false_of_input_eq_ok {args : List String} {c : List ℤ} {H : ℕ}
    {s : SieveOptions} {o : Options} {u : Output} (hi : input args = .ok (c, H, s, o, u))
    (hq : u.quiet = true) : u.verbose = false := by
  obtain ⟨_, _, -, -, -, -, -, -, h⟩ := exists_checkOptions_eq_ok_of_input_eq_ok hi
  exact h hq

/-- What the program prints under `-q` for a command line on which the search
`Ratpoints.findPoints` on the search intervals of the command line joined returns the list `L`: the
string before the points, the points of `L` that the callback of the program counts
(`Ratpoints.Cli.countedPoints`: those that it keeps, `Ratpoints.Cli.Data.keeps`, only the first of
these under `-1`) in the format, with the string between them in between, none under `-z`, and the
string after the points; it exits with the status `0`. -/
theorem run_eq_of_findPoints_eq_ok {args : List String} {c : List ℤ} {H : ℕ}
    {s : SieveOptions} {o : Options} {u : Output} {L : List (ℤ × ℤ × ℤ)}
    (hi : input args = .ok (c, H, s, o, u)) (hq : u.quiet = true)
    (hL : findPoints c H { s with arraySize := defaultArraySize }
      { o with domain := Id.run (joinIntervals o.domain) } = .ok L) :
    run args = (printString u.stringBefore ++ (printString u.stringBetween).intercalate
        ((if u.noOutput then [] else countedPoints (Data.ofOutput u o).keeps u.onePoint L).map
          fun p ↦ formatPoint (o.noCheck || o.noY) p.1 p.2.2 p.2.1
            (u.printFormat.getD "").toList) ++
      printString u.stringAfter, 0) := by
  obtain ⟨r, hr⟩ := exists_findPointsWith_eq_ok_of_findPoints_eq_ok process (.ofOutput u o) hL
  rw [run_eq_of_findPointsWith_eq_ok hi (verbose_eq_false_of_input_eq_ok hi hq) hr hL,
    preamble_eq_empty_of_quiet c H hq,
    report_eq_empty_of_quiet s _ hq, String.empty_append, String.append_empty]

/-- Under `-q -1`, without `-z`, the program prints the first point `p` of the list of
`Ratpoints.findPoints` on the search intervals of the command line joined that the callback keeps
(`Ratpoints.Cli.Data.keeps`: all of it but the points at infinity under `-i` and the affine points
outside the search intervals of the command line), in the format, between the string before the
points and the string after them. -/
theorem run_eq_of_onePoint {args : List String} {c : List ℤ} {H : ℕ} {s : SieveOptions}
    {o : Options} {u : Output} {L : List (ℤ × ℤ × ℤ)} {p : ℤ × ℤ × ℤ}
    (hi : input args = .ok (c, H, s, o, u)) (hq : u.quiet = true) (h1 : u.onePoint = true)
    (hz : u.noOutput = false)
    (hL : findPoints c H { s with arraySize := defaultArraySize }
      { o with domain := Id.run (joinIntervals o.domain) } = .ok L)
    (hK : (L.filter (Data.ofOutput u o).keeps).head? = some p) :
    run args = (printString u.stringBefore ++
      formatPoint (o.noCheck || o.noY) p.1 p.2.2 p.2.1 (u.printFormat.getD "").toList ++
      printString u.stringAfter, 0) := by
  rw [run_eq_of_findPoints_eq_ok hi hq hL]
  simp [countedPoints, h1, hz, List.take_one, hK, String.intercalate_singleton]

/-! ### The search region of the command line -/

theorem Intervals.eq_of_lower_eq_ok {iv iv' : Intervals} {a : String} (h : iv.lower a = .ok iv') :
    iv.lSeen = false ∧ iv.numInter ≠ maxDegree ∧ ∃ e d, Id.run (scanEnd a (-1)) = some (e, d) ∧
      (0 < iv.numInter → cmpEnd iv.ends[2 * iv.numInter - 1]! e < 0) ∧
      iv' = { iv with
        lSeen := true, ends := iv.ends.set! (2 * iv.numInter) e
        domain := iv.domain.set! iv.numInter (d, iv.domain[iv.numInter]!.2) } := by
  by_cases h1 : iv.lSeen = true
  · rw [Intervals.lower, ite_eq_left h1] at h; cases h
  by_cases h2 : iv.numInter = maxDegree
  · rw [Intervals.lower, ite_eq_right h1, ite_eq_left h2] at h; cases h
  rw [Intervals.lower, ite_eq_right h1, ite_eq_right h2] at h
  rcases hs : Id.run (scanEnd a (-1)) with _ | ⟨e, d⟩
  · have hs' : scanEnd a (-1) = none := hs
    simp only [liftM, monadLift, hs'] at h
    cases h
  have hs' : scanEnd a (-1) = some (e, d) := hs
  simp only [liftM, monadLift, hs', pure_bind, Id.run, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨by simpa using h1, h2, e, d, rfl, ?_⟩
  by_cases h3 : 0 < iv.numInter ∧ 0 ≤ cmpEnd iv.ends[2 * iv.numInter - 1]! e
  · rw [ite_eq_left h3] at h; cases h
  rw [ite_eq_right h3] at h
  exact ⟨fun hn ↦ not_le.mp fun h' ↦ h3 ⟨hn, h'⟩, (Except.ok.inj h).symm⟩

theorem Intervals.eq_of_upper_eq_ok_of_lSeen {iv iv' : Intervals} {H : ℕ} {a : String}
    (hl : iv.lSeen = true) (h : iv.upper H a = .ok iv') :
    ∃ e d, Id.run (scanEnd a 1) = some (e, d) ∧
      ¬0 < cmpEnd (iv.ends.set! (2 * iv.numInter + 1) e)[2 * iv.numInter]!
        (iv.ends.set! (2 * iv.numInter + 1) e)[2 * iv.numInter + 1]! ∧
      iv' = { lSeen := false, numInter := iv.numInter + 1
              domain := iv.domain.set! iv.numInter (iv.domain[iv.numInter]!.1, d)
              ends := iv.ends.set! (2 * iv.numInter + 1) e } := by
  rw [Intervals.upper] at h
  simp only [hl, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.false_and] at h
  rcases hs : Id.run (scanEnd a 1) with _ | ⟨e, d⟩
  · have hs' : scanEnd a 1 = none := hs
    simp only [liftM, monadLift, hs'] at h
    cases h
  have hs' : scanEnd a 1 = some (e, d) := hs
  simp only [liftM, monadLift, hs', pure_bind, Id.run] at h
  refine ⟨e, d, rfl, ?_⟩
  split at h
  · cases h
  exact ⟨‹_›, (Except.ok.inj h).symm⟩

theorem Intervals.eq_of_upper_eq_ok_of_lSeen_eq_false {iv iv' : Intervals} {H : ℕ} {a : String}
    (hl : iv.lSeen = false) (hd : 0 < iv.domain.size) (he : 1 < iv.ends.size)
    (h : iv.upper H a = .ok iv') :
    iv.numInter = 0 ∧ ∃ e d, Id.run (scanEnd a 1) = some (e, d) ∧
      ¬0 < cmpEnd { iv.ends[0]! with inf := -1 } e ∧
      iv' = { lSeen := false, numInter := 1
              domain := iv.domain.set! 0
                (if d.lt (heightEnd H).neg then Double.huge.neg else (heightEnd H).neg, d)
              ends := (iv.ends.set! 0 { iv.ends[0]! with inf := -1 }).set! 1 e } := by
  rw [Intervals.upper] at h
  by_cases h0 : iv.numInter = 0
  swap
  · simp only [hl, Bool.not_false, ↓reduceIte, h0] at h; cases h
  rcases hs : Id.run (scanEnd a 1) with _ | ⟨e, d⟩ <;> have hs' : scanEnd a 1 = _ := hs
  · simp only [hl, Bool.not_false, ↓reduceIte, h0, liftM, monadLift, hs'] at h; cases h
  simp only [hl, Bool.not_false, ↓reduceIte, h0, liftM, monadLift, hs', pure_bind, Id.run,
    Array.getElem!_set!_self _ _ _ hd, Array.getElem!_set!_ne _ _ _ _ (show 1 ≠ 0 by decide),
    Array.getElem!_set!_self _ _ _ (show 1 < (iv.ends.set! 0 { inf := -1, q := iv.ends[0]!.q }).size
      by simpa using he), Array.getElem!_set!_self _ _ _ (show 0 < iv.ends.size by lia),
    Bool.true_and, Nat.mul_zero, Nat.zero_add, Array.set!_set!] at h
  refine ⟨h0, e, d, rfl, ?_⟩
  by_cases hc : d.lt (heightEnd H).neg = true
  all_goals
    simp only [hc, ↓reduceIte, Bool.false_eq_true] at h ⊢
    split at h <;> (try cases h)
    exact ⟨by simpa using ‹¬0 < cmpEnd _ _›, rfl⟩

/-- The interval `d` of doubles holds the exact interval from `el` to `eu` of the command line as
far as the search goes: neither end of `d` is a NaN, the lower end of `d` is at most its upper end,
and every `x` with `|x| ≤ H` between the exact ends lies in `d`. -/
def IntervalOf (H : ℕ) (d : Double × Double) (el eu : ExactEnd) : Prop :=
  d.1.isNaN = false ∧ d.2.isNaN = false ∧ doubleValue d.1.bits ≤ doubleValue d.2.bits ∧
    ∀ x : ℚ, |x| ≤ H → el.value ≤ x → x ≤ eu.value → InPair d x

/-- The reading `iv` of the search intervals of the command line for the height bound `H`, with
`n` complete intervals and a lower end read after them when `l`: the arrays have their
`2 maxDegree` entries and room for the intervals, the exact ends are infinite only as `±1` and are
the ends of increasing and disjoint intervals `l ≤ u`, the double of a pending lower end is below
it, and the doubles of each complete interval hold it as far as the search goes. -/
structure Intervals.ReadsWF (H : ℕ) (iv : Intervals) (n : ℕ) (l : Bool) : Prop where
  /-- The exact ends have their `2 maxDegree` entries. -/
  size_ends : iv.ends.size = 2 * maxDegree
  /-- The doubles of the intervals have their `2 maxDegree` entries. -/
  size_domain : iv.domain.size = 2 * maxDegree
  /-- There is room for the intervals read. -/
  le_maxDegree : n + (if l then 1 else 0) ≤ maxDegree
  /-- An exact end is infinite only as `-1` or `1`. -/
  inf_mem (j : ℕ) : iv.ends[j]!.inf = -1 ∨ iv.ends[j]!.inf = 0 ∨ iv.ends[j]!.inf = 1
  /-- The exact ends read are the ends of increasing and disjoint intervals `l ≤ u`. -/
  chain : ChainEnds (fun j ↦ iv.ends[j]!.value) (2 * n + if l then 1 else 0)
  /-- The double of a pending lower end is not a NaN and lies at or below it. -/
  pending : l = true → iv.domain[n]!.1.isNaN = false ∧
    doubleValue iv.domain[n]!.1.bits ≤ iv.ends[2 * n]!.value
  /-- The doubles of each complete interval hold it as far as the search goes. -/
  interval (j : ℕ) : j < n → IntervalOf H iv.domain[j]! iv.ends[2 * j]! iv.ends[2 * j + 1]!

theorem Intervals.ReadsWF.lt_maxDegree {H n : ℕ} {iv : Intervals} (hw : iv.ReadsWF H n true) :
    n < maxDegree :=
  Nat.lt_of_add_one_le (by simpa using hw.le_maxDegree)

theorem Intervals.ReadsWF.le_maxDegree' {H n : ℕ} {iv : Intervals} (hw : iv.ReadsWF H n false) :
    n ≤ maxDegree := by
  simpa using hw.le_maxDegree

theorem Intervals.ReadsWF.chainEnds_two_mul {H n : ℕ} {iv : Intervals}
    (hw : iv.ReadsWF H n false) : ChainEnds (fun j ↦ iv.ends[j]!.value) (2 * n) := by
  simpa using hw.chain

theorem Intervals.ReadsWF.chainEnds_two_mul_add_one {H n : ℕ} {iv : Intervals}
    (hw : iv.ReadsWF H n true) : ChainEnds (fun j ↦ iv.ends[j]!.value) (2 * n + 1) := by
  simpa using hw.chain

theorem ChainEnds.snoc {v w : ℕ → WithBotTop ℚ} {m : ℕ} (h : ChainEnds v m)
    (hvw : ∀ i < m, w i = v i)
    (hlast : 0 < m → w (m - 1) ≤ w m ∧ ((m - 1) % 2 = 1 → w (m - 1) < w m)) :
    ChainEnds w (m + 1) := by
  intro i hi
  rcases (show i + 1 < m ∨ i + 1 = m by lia) with hi' | hi'
  · rw [hvw i (by lia), hvw (i + 1) hi']; exact h i hi'
  · obtain rfl : i = m - 1 := by lia
    rw [hi']; exact hlast (by lia)

/-- An end set after the ends of increasing and disjoint intervals `l ≤ u` continues them when it
lies at or above the last one, strictly above an upper end. -/
theorem ChainEnds.set! {ends : Array ExactEnd} {m : ℕ} {e : ExactEnd}
    (h : ChainEnds (fun j ↦ ends[j]!.value) m) (hm : m < ends.size)
    (hlink : 0 < m → ends[m - 1]!.value ≤ e.value ∧
      ((m - 1) % 2 = 1 → ends[m - 1]!.value < e.value)) :
    ChainEnds (fun j ↦ (ends.set! m e)[j]!.value) (m + 1) :=
  h.snoc (fun i hi ↦ by simp only [Array.getElem!_set!_ne _ _ _ _ (Nat.ne_of_gt hi)]) fun h0 ↦ by
    rw [Array.getElem!_set!_ne _ _ _ _ (by lia), Array.getElem!_set!_self _ _ _ hm]; exact hlink h0

theorem inf_mem_set! {ends : Array ExactEnd}
    (h : ∀ j : ℕ, ends[j]!.inf = -1 ∨ ends[j]!.inf = 0 ∨ ends[j]!.inf = 1) {e : ExactEnd}
    (he : e.inf = -1 ∨ e.inf = 0 ∨ e.inf = 1) (i j : ℕ) :
    (ends.set! i e)[j]!.inf = -1 ∨ (ends.set! i e)[j]!.inf = 0 ∨ (ends.set! i e)[j]!.inf = 1 := by
  rcases Array.getElem!_set!_eq_or ends i j e with h' | h' <;> rw [h']
  exacts [he, h j]

theorem intervalOf_set! {H n i k : ℕ} {dom : Array (Double × Double)} {ends : Array ExactEnd}
    {p : Double × Double} {e : ExactEnd}
    (h : ∀ j < n, IntervalOf H dom[j]! ends[2 * j]! ends[2 * j + 1]!) (hi : n ≤ i)
    (hk : 2 * n ≤ k) (j : ℕ) (hj : j < n) :
    IntervalOf H (dom.set! i p)[j]! (ends.set! k e)[2 * j]! (ends.set! k e)[2 * j + 1]! := by
  rw [Array.getElem!_set!_ne _ _ _ _ (by lia), Array.getElem!_set!_ne _ _ _ _ (by lia),
    Array.getElem!_set!_ne _ _ _ _ (by lia)]
  exact h j hj

theorem readsWF_default (H : ℕ) : Intervals.ReadsWF H {} 0 false where
  size_ends := by simp
  size_domain := by simp
  le_maxDegree := by simp
  inf_mem j := by
    refine .inr (.inl ?_)
    by_cases hj : j < 2 * maxDegree
    · rw [getElem!_pos _ j (by simpa using hj)]; simp
    · rw [getElem!_neg _ j (by simpa using hj)]; rfl
  chain i hi := absurd hi (by simp)
  pending := nofun
  interval j hj := absurd hj (by lia)

theorem Intervals.ReadsWF.lower {H : ℕ} {iv iv' : Intervals} {a : String}
    (hw : iv.ReadsWF H iv.numInter iv.lSeen) (h : iv.lower a = .ok iv') :
    iv'.ReadsWF H iv'.numInter iv'.lSeen := by
  obtain ⟨hl, hn, e, d, hs, hc, rfl⟩ := Intervals.eq_of_lower_eq_ok h
  obtain ⟨he1, hd1, hd2, -⟩ := inf_mem_and_isNaN_eq_false_and_le_of_run_scanEnd_eq_some hs
  rw [hl] at hw
  have hnm : iv.numInter < maxDegree := by lia [hw.le_maxDegree']
  have hes : 2 * iv.numInter < iv.ends.size := by rw [hw.size_ends]; lia
  have hlt (h0 : 0 < iv.numInter) := (cmpEnd_neg_iff (hw.inf_mem _) he1).mp (hc h0)
  dsimp only
  refine ⟨by simp [hw.size_ends], by simp [hw.size_domain], by simp; lia,
    inf_mem_set! hw.inf_mem he1 _, ?_, fun _ ↦ ?_, intervalOf_set! hw.interval le_rfl (by lia)⟩
  · change ChainEnds _ (2 * iv.numInter + 1)
    exact hw.chainEnds_two_mul.set! hes fun h0 ↦ ⟨(hlt (by lia)).le, fun _ ↦ hlt (by lia)⟩
  · rw [Array.getElem!_set!_self _ _ _ (by rw [hw.size_domain]; lia),
      Array.getElem!_set!_self _ _ _ hes]
    exact ⟨hd1, hd2 (by decide)⟩

theorem intervalOf_of_le {H : ℕ} {l d : Double} {el eu : ExactEnd} (hl : l.isNaN = false)
    (hd : d.isNaN = false) (h1 : doubleValue l.bits ≤ el.value) (h2 : el.value ≤ eu.value)
    (h3 : eu.value ≤ doubleValue d.bits) : IntervalOf H (l, d) el eu :=
  ⟨hl, hd, h1.trans (h2.trans h3), fun _ _ hx1 hx2 ↦ ⟨h1.trans hx1, hx2.trans h3⟩⟩

theorem doubleValue_neg_heightEnd {H : ℕ} (hH : 1 ≤ H) (hH63 : H < 2 ^ 63) :
    doubleValue (heightEnd H).neg.bits = ((-(heightEnd H).toRat : ℚ) : WithBotTop ℚ) := by
  rw [doubleValue_eq_toRat
    (by rw [isFinite_neg]; exact (isFinite_heightEnd_and_le_toRat hH hH63).1), toRat_neg]

theorem doubleValue_neg_heightEnd_le {H : ℕ} (hH : 1 ≤ H) (hH63 : H < 2 ^ 63) {x : ℚ}
    (hx : |x| ≤ H) : doubleValue (heightEnd H).neg.bits ≤ (x : WithBotTop ℚ) := by
  rw [doubleValue_neg_heightEnd hH hH63, WithBotTop.coe_le_coe]
  linarith [(isFinite_heightEnd_and_le_toRat hH hH63).2, neg_abs_le x]

theorem le_doubleValue_heightEnd {H : ℕ} (hH : 1 ≤ H) (hH63 : H < 2 ^ 63) {x : ℚ}
    (hx : |x| ≤ H) : (x : WithBotTop ℚ) ≤ doubleValue (heightEnd H).bits := by
  rw [doubleValue_eq_toRat (isFinite_heightEnd_and_le_toRat hH hH63).1, WithBotTop.coe_le_coe]
  linarith [(isFinite_heightEnd_and_le_toRat hH hH63).2, le_abs_self x]

/-- The first interval of an upper end without a lower one, `[-∞, e]` of the command line, and its
doubles `[-h, d]`, or `[-∞, d]` when `d` lies below `-h`. -/
theorem intervalOf_heightEnd_neg {H : ℕ} (hH : 1 ≤ H) (hH63 : H < 2 ^ 63) {d : Double}
    {e e0 : ExactEnd} (hd : d.isNaN = false) (he : e.value ≤ doubleValue d.bits) :
    IntervalOf H (if d.lt (heightEnd H).neg then Double.huge.neg else (heightEnd H).neg, d)
      { e0 with inf := -1 } e := by
  have hh : (heightEnd H).neg.isNaN = false := by
    rw [isNaN_neg]; exact isNaN_eq_false_of_isFinite (isFinite_heightEnd_and_le_toRat hH hH63).1
  refine ⟨by split <;> simp [isNaN_huge_neg, hh], hd, ?_, fun x hx _ hx2 ↦ ⟨?_, hx2.trans he⟩⟩
  · split_ifs with hc
    · exact doubleValue_huge_neg ▸ bot_le
    · exact not_lt.mp fun h ↦ hc ((lt_eq_true_iff hd hh).mpr h)
  · split_ifs
    · exact doubleValue_huge_neg ▸ bot_le
    · exact doubleValue_neg_heightEnd_le hH hH63 hx

/-- The last interval of a lower end without an upper one, `[el, +∞]` of the command line, and its
doubles `[l, h]`, or `[l, +∞]` when `h` lies below `l`. -/
theorem intervalOf_heightEnd {H : ℕ} (hH : 1 ≤ H) (hH63 : H < 2 ^ 63) {l : Double}
    {el e1 : ExactEnd} (hl : l.isNaN = false) (hle : doubleValue l.bits ≤ el.value) :
    IntervalOf H (l, if (heightEnd H).lt l then Double.huge else heightEnd H) el
      { e1 with inf := 1 } := by
  have hh : (heightEnd H).isNaN = false :=
    isNaN_eq_false_of_isFinite (isFinite_heightEnd_and_le_toRat hH hH63).1
  refine ⟨hl, by split <;> simp [isNaN_huge, hh], ?_, fun x hx hx1 _ ↦ ⟨hle.trans hx1, ?_⟩⟩
  · split_ifs with hc
    · exact doubleValue_huge ▸ le_top
    · exact not_lt.mp fun h ↦ hc ((lt_eq_true_iff hh hl).mpr h)
  · split_ifs
    · exact doubleValue_huge ▸ le_top
    · exact le_doubleValue_heightEnd hH hH63 hx

/-- Closing the pending interval of a reading with the exact upper end `e` and the upper double `u`,
which hold it as far as the search goes, keeps the invariant, whatever the field `lSeen` of the
result, which the invariant does not read: the step of both `Ratpoints.Cli.Intervals.upper` and
`Ratpoints.Cli.Intervals.complete`. -/
theorem Intervals.ReadsWF.close {H : ℕ} {iv : Intervals} {e : ExactEnd} {u : Double} (b : Bool)
    (hw : iv.ReadsWF H iv.numInter true) (he : e.inf = -1 ∨ e.inf = 0 ∨ e.inf = 1)
    (hle : iv.ends[2 * iv.numInter]!.value ≤ e.value)
    (hI : IntervalOf H (iv.domain[iv.numInter]!.1, u) iv.ends[2 * iv.numInter]! e) :
    ReadsWF H
      { lSeen := b, numInter := iv.numInter + 1,
        domain := iv.domain.set! iv.numInter (iv.domain[iv.numInter]!.1, u),
        ends := iv.ends.set! (2 * iv.numInter + 1) e } (iv.numInter + 1) false := by
  have hnm := hw.lt_maxDegree
  have hes : 2 * iv.numInter + 1 < iv.ends.size := by rw [hw.size_ends]; lia
  refine ⟨by simp [hw.size_ends], by simp [hw.size_domain], by simp; lia,
    inf_mem_set! hw.inf_mem he _, ?_, nofun, fun j hj ↦ ?_⟩
  · change ChainEnds _ (2 * iv.numInter + 1 + 1)
    exact hw.chainEnds_two_mul_add_one.set! hes fun _ ↦
      ⟨by simpa using hle, fun h' ↦ absurd h' (by lia)⟩
  · rcases (show j < iv.numInter ∨ j = iv.numInter by lia) with hj | rfl
    · exact intervalOf_set! hw.interval le_rfl (by lia) j hj
    · rw [Array.getElem!_set!_self _ _ _ (by rw [hw.size_domain]; lia),
        Array.getElem!_set!_ne _ _ _ _ (by lia), Array.getElem!_set!_self _ _ _ hes]
      exact hI

theorem Intervals.ReadsWF.upper_of_lSeen {H : ℕ} {iv iv' : Intervals} {a : String}
    (hw : iv.ReadsWF H iv.numInter iv.lSeen) (hl : iv.lSeen = true) (h : iv.upper H a = .ok iv') :
    iv'.ReadsWF H iv'.numInter iv'.lSeen := by
  obtain ⟨e, d, hs, hc, rfl⟩ := Intervals.eq_of_upper_eq_ok_of_lSeen hl h
  obtain ⟨he1, hd1, -, hd2⟩ := inf_mem_and_isNaN_eq_false_and_le_of_run_scanEnd_eq_some hs
  rw [hl] at hw
  have hes : 2 * iv.numInter + 1 < iv.ends.size := by rw [hw.size_ends]; lia [hw.lt_maxDegree]
  rw [Array.getElem!_set!_ne _ _ _ _ (by lia), Array.getElem!_set!_self _ _ _ hes] at hc
  have hle := not_lt.mp fun h' ↦ hc ((cmpEnd_pos_iff (hw.inf_mem _) he1).mpr h')
  exact hw.close false he1 hle
    (intervalOf_of_le (hw.pending rfl).1 hd1 (hw.pending rfl).2 hle (hd2 (by decide)))

theorem Intervals.ReadsWF.upper_of_not_lSeen {H : ℕ} {iv iv' : Intervals} {a : String}
    (hH : 1 ≤ H) (hH63 : H < 2 ^ 63) (hw : iv.ReadsWF H iv.numInter iv.lSeen)
    (hl : iv.lSeen = false) (h : iv.upper H a = .ok iv') :
    iv'.ReadsWF H iv'.numInter iv'.lSeen := by
  have hm := zero_lt_maxDegree
  obtain ⟨hn0, e, d, hs, -, rfl⟩ := Intervals.eq_of_upper_eq_ok_of_lSeen_eq_false hl
    (by rw [hw.size_domain]; lia) (by rw [hw.size_ends]; lia) h
  obtain ⟨he1, hd1, -, hd2⟩ := inf_mem_and_isNaN_eq_false_and_le_of_run_scanEnd_eq_some hs
  have e0 : (iv.ends.set! 0 { iv.ends[0]! with inf := -1 })[0]! = { iv.ends[0]! with inf := -1 } :=
    Array.getElem!_set!_self _ _ _ (by rw [hw.size_ends]; lia)
  have e1 : ((iv.ends.set! 0 { iv.ends[0]! with inf := -1 }).set! 1 e)[1]! = e :=
    Array.getElem!_set!_self _ _ _ (by simp [hw.size_ends]; lia)
  dsimp only
  refine ⟨by simp [hw.size_ends], by simp [hw.size_domain], by simp; lia,
    inf_mem_set! (inf_mem_set! hw.inf_mem (by simp) _) he1 _, ?_, nofun, fun j hj ↦ ?_⟩
  · refine (show ChainEnds _ 1 from fun i hi ↦ absurd hi (by lia)).set!
      (by simp [hw.size_ends]; lia) fun _ ↦ ⟨?_, nofun⟩
    simp only [Nat.sub_self, e0, ExactEnd.value, show (-1 : ℤ) < 0 by decide, ↓reduceIte, bot_le]
  · obtain rfl : j = 0 := by lia
    rw [Array.getElem!_set!_self _ _ _ (by rw [hw.size_domain]; lia), Nat.mul_zero,
      Array.getElem!_set!_ne _ _ _ _ (by decide), e0, e1]
    exact intervalOf_heightEnd_neg hH hH63 hd1 (hd2 (by decide))

theorem Intervals.ReadsWF.upper {H : ℕ} {iv iv' : Intervals} {a : String} (hH : 1 ≤ H)
    (hH63 : H < 2 ^ 63) (hw : iv.ReadsWF H iv.numInter iv.lSeen) (h : iv.upper H a = .ok iv') :
    iv'.ReadsWF H iv'.numInter iv'.lSeen := by
  cases hl : iv.lSeen
  · exact hw.upper_of_not_lSeen hH hH63 hl h
  · exact hw.upper_of_lSeen hl h

theorem Intervals.ReadsWF.complete {H : ℕ} {iv : Intervals} (hH : 1 ≤ H) (hH63 : H < 2 ^ 63)
    (hw : iv.ReadsWF H iv.numInter iv.lSeen) :
    (iv.complete H).ReadsWF H (iv.complete H).numInter false := by
  cases hl : iv.lSeen
  · simp only [Intervals.complete, hl, Bool.false_eq_true, ↓reduceIte]
    rwa [hl] at hw
  rw [hl] at hw
  simp only [Intervals.complete, hl, ↓reduceIte]
  exact hw.close true (by simp) (by simp [ExactEnd.value])
    (intervalOf_heightEnd hH hH63 (hw.pending rfl).1 (hw.pending rfl).2)

/-- The doubles of the lower ends after the first that the reading `iv` of the search intervals has
read, `n` complete intervals and a pending lower end when `l`, are the largest doubles at most their
exact ends, as `outward` from the double that `strtod` reads makes them. -/
def Intervals.LowerMax (iv : Intervals) (n : ℕ) (l : Bool) : Prop :=
  ∀ j, 1 ≤ j → j < n + (if l then 1 else 0) →
    doubleValue iv.domain[j]!.1.bits ≤ iv.ends[2 * j]!.value ∧ ∀ y : Double, y.isNaN = false →
      doubleValue y.bits ≤ iv.ends[2 * j]!.value →
        doubleValue y.bits ≤ doubleValue iv.domain[j]!.1.bits

theorem lowerMax_default : Intervals.LowerMax {} 0 false := fun _ h1 h2 ↦ absurd h2 (by simp)

theorem Intervals.LowerMax.lower {H : ℕ} {iv iv' : Intervals} {a : String}
    (hw : iv.ReadsWF H iv.numInter iv.lSeen) (hm : iv.LowerMax iv.numInter iv.lSeen)
    (hlen : a.length < 2 ^ 56) (h : iv.lower a = .ok iv') :
    iv'.LowerMax iv'.numInter iv'.lSeen := by
  obtain ⟨hl, hn, e, d, hs, -, rfl⟩ := Intervals.eq_of_lower_eq_ok h
  rw [hl] at hw hm
  have hnm := hw.le_maxDegree'
  intro j hj1 hj2
  simp only [↓reduceIte] at hj2
  rcases (show j < iv.numInter ∨ j = iv.numInter by lia) with hj | rfl
  · rw [Array.getElem!_set!_ne _ _ _ _ (by lia), Array.getElem!_set!_ne _ _ _ _ (by lia)]
    exact hm j hj1 hj
  · rw [Array.getElem!_set!_self _ _ _ (by rw [hw.size_domain]; lia),
      Array.getElem!_set!_self _ _ _ (by rw [hw.size_ends]; lia)]
    exact ⟨(inf_mem_and_isNaN_eq_false_and_le_of_run_scanEnd_eq_some hs).2.2.1 (by decide),
      run_scanEnd_isMaxBelow hs hlen⟩

/-- Closing the pending interval of a reading keeps the doubles of the lower ends the largest
doubles at most their exact ends: the lower ends do not change. -/
theorem Intervals.LowerMax.close {iv : Intervals} {e : ExactEnd} {u : Double} (b : Bool)
    (hs : iv.numInter < iv.domain.size) (hm : iv.LowerMax iv.numInter true) :
    LowerMax
      { lSeen := b, numInter := iv.numInter + 1,
        domain := iv.domain.set! iv.numInter (iv.domain[iv.numInter]!.1, u),
        ends := iv.ends.set! (2 * iv.numInter + 1) e } (iv.numInter + 1) false := by
  intro j hj1 hj2
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hj2
  rw [Array.getElem!_set!_ne iv.ends (2 * iv.numInter + 1) (2 * j) e (by lia)]
  rcases (show j < iv.numInter ∨ j = iv.numInter by lia) with hj | rfl
  · rw [Array.getElem!_set!_ne _ _ _ _ (by lia)]; exact hm j hj1 (by simp; lia)
  · rw [Array.getElem!_set!_self _ _ _ hs]
    exact hm _ hj1 (by simp)

theorem Intervals.LowerMax.upper {H : ℕ} {iv iv' : Intervals} {a : String}
    (hw : iv.ReadsWF H iv.numInter iv.lSeen) (hm : iv.LowerMax iv.numInter iv.lSeen)
    (h : iv.upper H a = .ok iv') : iv'.LowerMax iv'.numInter iv'.lSeen := by
  cases hl : iv.lSeen
  · obtain ⟨hn0, -, -, -, -, rfl⟩ := Intervals.eq_of_upper_eq_ok_of_lSeen_eq_false hl
      (by rw [hw.size_domain]; have := zero_lt_maxDegree; lia)
      (by rw [hw.size_ends]; have := zero_lt_maxDegree; lia) h
    exact fun j h1 h2 ↦ absurd h2 (by simp; lia)
  obtain ⟨e, d, -, -, rfl⟩ := Intervals.eq_of_upper_eq_ok_of_lSeen hl h
  rw [hl] at hm hw
  exact hm.close false (by rw [hw.size_domain]; lia [hw.lt_maxDegree])

theorem Intervals.LowerMax.complete {H : ℕ} {iv : Intervals}
    (hw : iv.ReadsWF H iv.numInter iv.lSeen) (hm : iv.LowerMax iv.numInter iv.lSeen) :
    (iv.complete H).LowerMax (iv.complete H).numInter false := by
  cases hl : iv.lSeen
  · simp only [Intervals.complete, hl, Bool.false_eq_true, ↓reduceIte]; rwa [hl] at hm
  rw [hl] at hm hw
  simp only [Intervals.complete, hl, ↓reduceIte]
  exact hm.close true (by rw [hw.size_domain]; lia [hw.lt_maxDegree])

theorem checkOptions_store_intervals (s : SieveOptions × Options × Output × Intervals) (o : String)
    (a : Option String) : (checkOptions.store s o a).2.2.2 = s.2.2.2 := by
  obtain ⟨s, t, u, iv⟩ := s
  simp only [checkOptions.store]

theorem checkOptions_preserves {H : ℕ} {P : Intervals → Prop} {Q : String → Prop}
    (hl : ∀ iv a iv', Q a → P iv → iv.lower a = .ok iv' → P iv')
    (hu : ∀ iv a iv', Q a → P iv → iv.upper H a = .ok iv' → P iv')
    {os : List String} {s s' : SieveOptions × Options × Output × Intervals}
    (hq : ∀ a ∈ os, Q a) (hs : P s.2.2.2) (h : checkOptions H s os = .ok s') : P s'.2.2.2 := by
  fun_induction checkOptions H s os with
  | case1 => cases h; exact hs
  | case2 => cases h
  | case3 _ _ _ _ ih =>
    exact ih (fun a ha ↦ hq a (.tail _ ha)) (by rwa [checkOptions_store_intervals]) h
  | case4 _ _ a os _ _ _ iv _ _ ih =>
    obtain ⟨iv', h1, h2⟩ := Except.bind_eq_ok h
    exact ih iv' (fun b hb ↦ hq b (.tail _ (.tail _ hb))) (hl iv a iv' (hq a (by simp)) hs h1) h2
  | case5 _ _ a os _ _ _ iv _ _ ih =>
    obtain ⟨iv', h1, h2⟩ := Except.bind_eq_ok h
    exact ih iv' (fun b hb ↦ hq b (.tail _ (.tail _ hb))) (hu iv a iv' (hq a (by simp)) hs h1) h2
  | case6 => cases h
  | case7 _ _ _ _ _ _ _ ih =>
    exact ih (fun a ha ↦ hq a (.tail _ ha)) (by rwa [checkOptions_store_intervals]) h
  | case8 _ _ _ _ _ _ _ _ _ ih =>
    exact ih (fun a ha ↦ hq a (.tail _ (.tail _ ha))) (by rwa [checkOptions_store_intervals]) h
  | case9 => cases h
  | case10 => cases h

/-- What a command line that the program accepts gives for its search intervals: the height bound
is a positive `long`, and the reading of the intervals ends with complete intervals that keep the
invariant, the search intervals of the options being their doubles and the exact ends of the
settings of the output their exact ends. -/
theorem reads_of_input_eq_ok {args : List String} {c : List ℤ} {H : ℕ} {s : SieveOptions}
    {o : Options} {u : Output} (hi : input args = .ok (c, H, s, o, u)) :
    1 ≤ H ∧ H < 2 ^ 63 ∧ ∃ iv : Intervals, iv.ReadsWF H iv.numInter false ∧
      o.domain = iv.domain.toList.take iv.numInter ∧ u.ends = iv.ends := by
  obtain ⟨os, iv, -, hH, hH63, ⟨s', o', u', hk⟩, hdom, hends, -⟩ :=
    exists_checkOptions_eq_ok_of_input_eq_ok hi
  refine ⟨hH, hH63, iv.complete H, ?_, hdom, hends⟩
  have hw := checkOptions_preserves (P := fun iv : Intervals ↦ iv.ReadsWF H iv.numInter iv.lSeen)
    (Q := fun _ ↦ True) (fun iv a iv' _ hw h ↦ hw.lower h)
    (fun iv a iv' _ hw h ↦ hw.upper hH hH63 h) (fun _ _ ↦ trivial) (readsWF_default H) hk
  exact hw.complete hH hH63

theorem Intervals.ReadsWF.length_take {H : ℕ} {iv : Intervals}
    (hw : iv.ReadsWF H iv.numInter false) :
    (iv.domain.toList.take iv.numInter).length = iv.numInter := by
  simp [hw.size_domain]; lia [hw.le_maxDegree']

theorem Intervals.ReadsWF.noNaN_take {H : ℕ} {iv : Intervals}
    (hw : iv.ReadsWF H iv.numInter false) :
    NoNaN (iv.domain.toList.take iv.numInter) := fun p hp ↦ by
  obtain ⟨j, hj, -, rfl⟩ := Array.exists_eq_of_mem_take_toList hp
  exact ⟨(hw.interval j hj).1, (hw.interval j hj).2.1⟩

theorem Intervals.ReadsWF.joinsWell_take {H : ℕ} {iv : Intervals}
    (hw : iv.ReadsWF H iv.numInter false) (hm : iv.LowerMax iv.numInter false) :
    JoinsWell (iv.domain.toList.take iv.numInter) := by
  have hs : iv.numInter ≤ iv.domain.size := by rw [hw.size_domain]; lia [hw.le_maxDegree']
  refine ⟨fun p hp ↦ ?_, fun i j hi hij hj ↦ ?_⟩
  · obtain ⟨k, hk, -, rfl⟩ := Array.exists_eq_of_mem_take_toList hp
    exact (hw.interval k hk).2.2.1
  · rw [hw.length_take] at hj
    rw [Array.getElem!_take_toList (by lia) hs, Array.getElem!_take_toList hj hs]
    exact (hm j (by lia) (by simpa using hj)).2 _ (hw.interval i (by lia)).1
      ((hm i hi (by simp; lia)).1.trans (hw.chainEnds_two_mul.le (by lia) (by lia)))

theorem Intervals.ReadsWF.intervalsWF_joinIntervals {H : ℕ} {iv : Intervals}
    (hw : iv.ReadsWF H iv.numInter false) (hm : iv.LowerMax iv.numInter false) :
    IntervalsWF (domainBits (Id.run (joinIntervals (iv.domain.toList.take iv.numInter)))) := by
  obtain ⟨-, hnan, -, hwf⟩ := run_joinIntervals hw.noNaN_take
  refine ⟨fun i hi ↦ ?_,
    by simpa [List.map_map, Function.comp_def] using hwf (hw.joinsWell_take hm)⟩
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hi
  exact ⟨(isNaN_eq_false_iff _).mp (hnan p hp).1, (isNaN_eq_false_iff _).mp (hnan p hp).2⟩

/-- The test of the callback, the binary search of `in_region` over the exact ends of the search
intervals of a command line that the program accepts, which are increasing and disjoint by the
checks of error 7, is the membership of `a / b` in one of them. -/
theorem inRegion_iff_of_input_eq_ok {args : List String} {c : List ℤ} {H : ℕ}
    {s : SieveOptions} {o : Options} {u : Output} (hi : input args = .ok (c, H, s, o, u))
    (a b : ℤ) :
    Id.run (inRegion a b u.ends o.domain.length) = true ↔
      InExactRegion u.ends o.domain.length (a / b) := by
  obtain ⟨-, -, iv, hw, hdom, hends⟩ := reads_of_input_eq_ok hi
  rw [hdom, hw.length_take, hends]
  exact run_inRegion a b hw.chainEnds_two_mul

/-- The search intervals that the program gives the library hold the exact search region of its
command line as far as the search goes, for `|x| ≤ H`: their ends are the doubles outward of the
exact ends (`Ratpoints.Cli.outward`), or `∓h` for a missing first lower or last upper end, which
lie beyond the height bound. -/
theorem inIntervals_joinIntervals_of_inExactRegion {args : List String} {c : List ℤ} {H : ℕ}
    {s : SieveOptions} {o : Options} {u : Output} (hi : input args = .ok (c, H, s, o, u)) {x : ℚ}
    (hx : |x| ≤ H) (hex : InExactRegion u.ends o.domain.length x) :
    InIntervals (domainValues (Id.run (joinIntervals o.domain))) x := by
  obtain ⟨-, -, iv, hw, hdom, hends⟩ := reads_of_input_eq_ok hi
  rw [hdom, hw.length_take, hends] at hex
  obtain ⟨j, hj, h1, h2⟩ := hex
  have hm := hw.le_maxDegree'
  rw [hdom]
  obtain ⟨-, -, hcov, -⟩ := run_joinIntervals hw.noNaN_take
  obtain ⟨p, hp, hpx⟩ := hcov x ⟨_, Array.mem_take_toList_of_lt hj (by rw [hw.size_domain]; lia),
    (hw.interval j hj).2.2.2 x hx h1 h2⟩
  exact ⟨_, List.mem_map_of_mem hp, hpx⟩

theorem keeps_ofOutput_iff (u : Output) (o : Options) (p : ℤ × ℤ × ℤ) :
    (Data.ofOutput u o).keeps p = true ↔ (u.pointsAtInfty = true ∨ p.2.2 ≠ 0) ∧
      (p.2.2 = 0 ∨ o.domain = [] ∨ Id.run (inRegion p.1 p.2.2 u.ends o.domain.length) = true) := by
  simp [Data.keeps, Data.ofOutput, or_assoc]

/-- The search intervals that the program gives the library for a command line that it accepts,
whose words have fewer than `2 ^ 56` characters, are well formed, so that the library never
refuses them (error 9 is unreachable): the doubles of the lower ends after the first are the
largest doubles at most the exact ends, which increase, so that `join_intervals` joins the
intervals whose doubles meet into intervals that are increasing and strictly apart. Without the
bound on the length, a word of `LONG_MAX / 20` digits could make `scan_end` stop taking the digits
of its exponent. -/
theorem intervalsWF_joinIntervals_of_input_eq_ok {args : List String} {c : List ℤ} {H : ℕ}
    {s : SieveOptions} {o : Options} {u : Output} (hlen : ∀ a ∈ args, a.length < 2 ^ 56)
    (hi : input args = .ok (c, H, s, o, u)) :
    IntervalsWF (domainBits (Id.run (joinIntervals o.domain))) := by
  obtain ⟨os, iv, hos, hH, hH63, ⟨_, _, _, hk⟩, hdom, -, -⟩ :=
    exists_checkOptions_eq_ok_of_input_eq_ok hi
  have hP := checkOptions_preserves
    (P := fun iv : Intervals ↦ iv.ReadsWF H iv.numInter iv.lSeen ∧ iv.LowerMax iv.numInter iv.lSeen)
    (Q := fun a ↦ a.length < 2 ^ 56) (fun iv a iv' ha hw h ↦ ⟨hw.1.lower h, hw.2.lower hw.1 ha h⟩)
    (fun iv a iv' _ hw h ↦ ⟨hw.1.upper hH hH63 h, hw.2.upper hw.1 h⟩)
    (fun a ha ↦ hlen a (hos a ha)) ⟨readsWF_default H, lowerMax_default⟩ hk
  rw [hdom]
  exact (hP.1.complete hH hH63).intervalsWF_joinIntervals (hP.2.complete hP.1)

/-- For a point of height at most `H` of a command line that the program accepts, the search
region of the search on the joined intervals is that of the range of the denominators, given that
`x / z` lies in the exact search region of the command line when there is one. -/
theorem inRegion_joinIntervals_iff {args : List String} {c : List ℤ} {H : ℕ}
    {s : SieveOptions} {o : Options} {u : Output} (hi : input args = .ok (c, H, s, o, u))
    {p : ℤ × ℤ × ℤ} (hp : IsPoint c H p)
    (hx : p.2.2 = 0 ∨ o.domain = [] ∨ InExactRegion u.ends o.domain.length (p.1 / p.2.2)) :
    InRegion (domainValues (Id.run (joinIntervals o.domain))) o.bLow o.bHigh p ↔
      InRegion [] o.bLow o.bHigh p := by
  by_cases hz : p.2.2 = 0
  · simp [InRegion, hz]
  simp only [InRegion, hz, false_or, true_or, and_true]
  refine ⟨fun h ↦ ⟨h.1, h.2.1⟩, fun h ↦ ⟨h.1, h.2, ?_⟩⟩
  rcases hx.resolve_left hz with h0 | h0
  · exact .inl (by simp [h0, joinIntervals])
  · exact .inr (inIntervals_joinIntervals_of_inExactRegion hi
      ((abs_intCast_div_intCast_le_abs p.1 p.2.2).trans (mod_cast hp.2.2.2.1)) h0)

/-- Assuming Sturm's theorem when the Sturm step is on (`Ratpoints.SturmTheorem`, which a command
line with `-s` does not need), without `-x`, the points of the list of `Ratpoints.findPoints` on
the joined search intervals of a command line that the callback of the program keeps
(`Ratpoints.Cli.Data.keeps`), which it prints under `-q`
(`Ratpoints.Cli.run_eq_of_findPoints_eq_ok`), are exactly the points of height at most `H` in the
exact search region of the command line, those with `y ≥ 0` under `-y`: the points at infinity
unless `-i`, and the affine points with the denominator in the range of `-dl` and `-du` and `x / z`
in one of the intervals of `-l` and `-u` when there are some. -/
theorem mem_filter_keeps_iff_of_input_eq_ok {args : List String} {c : List ℤ} {H : ℕ}
    {s : SieveOptions} {o : Options} {u : Output} {L : List (ℤ × ℤ × ℤ)}
    (hS : 0 ≤ o.sturm → SturmTheorem) (hi : input args = .ok (c, H, s, o, u))
    (hc : o.noCheck = false)
    (hL : findPoints c H { s with arraySize := defaultArraySize }
      { o with domain := Id.run (joinIntervals o.domain) } = .ok L) {p : ℤ × ℤ × ℤ} :
    p ∈ L.filter (Data.ofOutput u o).keeps ↔ IsPoint c H p ∧ (o.noY = true → 0 ≤ p.2.1) ∧
      (u.pointsAtInfty = true ∨ p.2.2 ≠ 0) ∧ InRegion [] o.bLow o.bHigh p ∧
      (p.2.2 = 0 ∨ o.domain = [] ∨ InExactRegion u.ends o.domain.length (p.1 / p.2.2)) := by
  rw [List.mem_filter, mem_iff_isPoint_of_findPoints_eq_ok
    (o := { o with domain := Id.run (joinIntervals o.domain) }) hS hL hc,
    keeps_ofOutput_iff, inRegion_iff_of_input_eq_ok hi]
  exact ⟨fun ⟨⟨hp, hy, hr⟩, hk1, hx⟩ ↦
      ⟨hp, hy, hk1, (inRegion_joinIntervals_iff hi hp hx).mp hr, hx⟩,
    fun ⟨hp, hy, hk1, hr, hx⟩ ↦ ⟨⟨hp, hy, (inRegion_joinIntervals_iff hi hp hx).mpr hr⟩, hk1, hx⟩⟩

end Ratpoints.Cli

end

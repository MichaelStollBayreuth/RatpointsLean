/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.Cli

import Ratpoints.Proof.Containers
import Ratpoints.Proof.Delivery
import Ratpoints.Proof.Output
import Ratpoints.Proof.Params

/-!
# The output of the program

What the program `ratpoints-lean` prints for the points of a successful search. Its callback
`Ratpoints.Cli.process`, called for the points of a list `L` in turn from the data
`Ratpoints.Cli.Data.ofOutput u o` of the settings `u` of the output and the options `o` of the
search, counts the points of `L` but for those at infinity under `-i`, of these only the first
under `-1`, at which it stops the search (`Ratpoints.Cli.countedPoints`), and prints them unless
`-z`, each after the string before the points (`-fs`) if it is the first and else after the string
between them (`-fm`), in the format of `-f`: so the text printed, with the string before the points
when no point was printed, is the string before the points followed by the formatted points with
the string between them in between (`Ratpoints.Cli.out_append_deliver_process_ofOutput`), and the
count is their number (`Ratpoints.Cli.total_deliver_process`). By the protocol of the delivery
(`Ratpoints.map_findPointsWith_eq_map_findPoints`), which says that for well-formed parameters, as
the program's are (`Ratpoints.wf_sieveParams`), the search delivers to a callback the points of
`Ratpoints.findPoints` in their order until a call stops it, this is what
`Ratpoints.Cli.run` prints between the head of the report and its end; under `-q` it is all that
it prints, with the string after the points (`-fe`) at the end, and under `-1` the one point
printed is the first point of the list of `Ratpoints.findPoints` that `-i` keeps.

## Main statements

* `Ratpoints.Cli.deliver_process`: the delivery of a list to the callback of the program.
* `Ratpoints.Cli.out_append_deliver_process_ofOutput`, `Ratpoints.Cli.total_deliver_process`: the
  text that the callback prints and the count.
* `Ratpoints.Cli.run_eq_of_findPointsWith_eq_ok`, `Ratpoints.Cli.total_eq_of_findPointsWith_eq_ok`:
  what the program prints for a successful search, and the count that its report gives.
* `Ratpoints.Cli.run_eq_of_findPoints_eq_ok`: what the program prints under `-q`.
* `Ratpoints.Cli.run_eq_of_onePoint`: under `-q -1`, the first point that `-i` keeps.
-/

@[expose] public section

namespace Ratpoints.Cli

/-! ### The points that the callback counts -/

/-- The points of the list `L`, in their order, that the callback `Ratpoints.Cli.process` of the
program counts when it is called for the points of `L` in turn, from data whose settings of the
points at infinity and of one point are `pointsAtInfty` and `onePoint` and while it has not
stopped the search: the points of `L` but for those at infinity (`z = 0`) when the points at
infinity are passed over (`-i`, `pointsAtInfty` clear), the list that `-i` keeps; and of these only
the first when one point is enough (`-1`, `onePoint` set), at which the callback stops the
search. -/
def countedPoints (pointsAtInfty onePoint : Bool) (L : List (ℤ × ℤ × ℤ)) : List (ℤ × ℤ × ℤ) :=
  let K := L.filter fun p ↦ pointsAtInfty || p.2.2 != 0
  if onePoint then K.take 1 else K

theorem countedPoints_nil (pointsAtInfty onePoint : Bool) :
    countedPoints pointsAtInfty onePoint [] = [] := by
  cases onePoint <;> rfl

theorem countedPoints_cons_of_not_keep {pointsAtInfty : Bool} {p : ℤ × ℤ × ℤ}
    (h : (pointsAtInfty || p.2.2 != 0) = false) (onePoint : Bool) (L : List (ℤ × ℤ × ℤ)) :
    countedPoints pointsAtInfty onePoint (p :: L) = countedPoints pointsAtInfty onePoint L := by
  simp [countedPoints, h]

theorem countedPoints_cons_of_keep {pointsAtInfty : Bool} {p : ℤ × ℤ × ℤ}
    (h : (pointsAtInfty || p.2.2 != 0) = true) (onePoint : Bool) (L : List (ℤ × ℤ × ℤ)) :
    countedPoints pointsAtInfty onePoint (p :: L) =
      if onePoint then [p] else p :: countedPoints pointsAtInfty onePoint L := by
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
theorem pointsAtInfty_printPoint (d : Data) (p : ℤ × ℤ × ℤ) :
    (d.printPoint p).pointsAtInfty = d.pointsAtInfty := by
  cases h : d.noOutput <;> simp [printPoint, h]

@[simp]
theorem onePoint_printPoint (d : Data) (p : ℤ × ℤ × ℤ) :
    (d.printPoint p).onePoint = d.onePoint := by
  cases h : d.noOutput <;> simp [printPoint, h]

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

/-- A call of the callback that does not pass over the point `(x, y, z)`, which is not at infinity
or the points at infinity are kept, prints it (`Ratpoints.Cli.Data.printPoint`), counts it and
stops the search under `-1`. -/
theorem call_process_of_keep {r : Delivery Data} {x z y : ℤ}
    (h : (r.info.pointsAtInfty || z != 0) = true) :
    r.call process x z y = ⟨r.info.printPoint (x, y, z), r.total + 1, r.info.onePoint⟩ := by
  simp only [Delivery.call, process, Data.printPoint]
  split_ifs <;> simp_all

theorem call_process_of_not_keep {r : Delivery Data} {x z y : ℤ}
    (h : (r.info.pointsAtInfty || z != 0) = false) :
    r.call process x z y = ⟨r.info, r.total, false⟩ := by
  simp_all [Delivery.call, process]

/-- The delivery of the points of `L` to the callback of the program from the data `d` and the
count `t`, with the flag of the stop clear: the points that the callback counts
(`Ratpoints.Cli.countedPoints`) are printed in turn and counted, and the search is stopped when one
point is enough and `L` has a point that the callback does not pass over. -/
theorem deliver_process (d : Data) (t : ℤ) (L : List (ℤ × ℤ × ℤ)) :
    (⟨d, t, false⟩ : Delivery Data).deliver process L =
      ⟨(countedPoints d.pointsAtInfty d.onePoint L).foldl Data.printPoint d,
        t + (countedPoints d.pointsAtInfty d.onePoint L).length,
        d.onePoint && L.any fun p ↦ d.pointsAtInfty || p.2.2 != 0⟩ := by
  induction L generalizing d t with
  | nil => simp [countedPoints_nil]
  | cons p L ih =>
    rw [Delivery.deliver_cons_of_quit_eq_false process rfl]
    cases hk : (d.pointsAtInfty || p.2.2 != 0)
    · rw [call_process_of_not_keep hk, ih, countedPoints_cons_of_not_keep hk]
      simp [hk]
    · rw [call_process_of_keep hk, countedPoints_cons_of_keep hk]
      cases h1 : d.onePoint
      · rw [ih]
        simp [h1, hk]
        lia
      · rw [Delivery.deliver_of_quit process rfl]
        simp [hk]

theorem total_deliver_process (d : Data) (t : ℤ) (L : List (ℤ × ℤ × ℤ)) :
    ((⟨d, t, false⟩ : Delivery Data).deliver process L).total =
      t + (countedPoints d.pointsAtInfty d.onePoint L).length := by
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
        ((if u.noOutput then [] else countedPoints u.pointsAtInfty u.onePoint L).map fun p ↦
          formatPoint (o.noCheck || o.noY) p.1 p.2.2 p.2.1 (u.printFormat.getD "").toList) := by
  rw [deliver_process]
  exact Data.out_append_foldl_printPoint rfl rfl _

/-! ### The program -/

theorem preamble_eq_empty_of_quiet (c : List ℤ) (H : ℕ) {u : Output} (hq : u.quiet = true) :
    preamble c H u = "" := by
  simp [preamble, hq]

theorem report_eq_empty_of_quiet {σ : Type} (s : SieveOptions) (o : Options) {u : Output}
    (hq : u.quiet = true) (r : Outcome σ) :
    report s o u r = "" := by
  simp [report, hq]

/-- What the program prints for a command line that it reads as the coefficients `c`, the height
bound `H`, the options `s` of the sieving parameters, the options `o` of the search and the
settings `u` of the output, when the search `Ratpoints.findPoints` returns the list `L` and the
search with the callback of the program the outcome `r`: the head of the report, the string before
the points, the points of `L` that the callback counts (`Ratpoints.Cli.countedPoints`: all but
those at infinity under `-i`, only the first of these under `-1`) in the format, with the string
between them in between, none under `-z`, the string after the points and the end of the report.
The sieving parameters of the program are well formed (`Ratpoints.wf_sieveParams`), so that the
protocol of the delivery holds (`Ratpoints.map_findPointsWith_eq_map_findPoints`). -/
theorem run_eq_of_findPointsWith_eq_ok {args : List String} {c : List ℤ} {H : ℕ}
    {s : SieveOptions} {o : Options} {u : Output} {r : Outcome Data} {L : List (ℤ × ℤ × ℤ)}
    (hi : input args = .ok (c, H, s, o, u))
    (hr : findPointsWith c H (sieveParams s) o process (.ofOutput u o) = .ok r)
    (hL : findPoints c H (sieveParams s) o = .ok L) :
    run args = (preamble c H u ++ printString u.stringBefore ++
      (printString u.stringBetween).intercalate
        ((if u.noOutput then [] else countedPoints u.pointsAtInfty u.onePoint L).map fun p ↦
          formatPoint (o.noCheck || o.noY) p.1 p.2.2 p.2.1 (u.printFormat.getD "").toList) ++
      printString u.stringAfter ++ report s o u r, 0) := by
  simp only [run, hi, hr]
  rw [(info_total_eq_of_findPointsWith_eq_ok (wf_sieveParams s) hr hL).1,
    String.append_assoc (s₁ := preamble c H u), out_append_deliver_process_ofOutput,
    ← String.append_assoc]

/-- The count of the points that the report of the program gives: the number of the points of the
list of `Ratpoints.findPoints` that the callback of the program counts
(`Ratpoints.Cli.countedPoints`), for well-formed parameters. -/
theorem total_eq_of_findPointsWith_eq_ok {c : List ℤ} {H : ℕ} {P : Params} {o : Options}
    {u : Output} {r : Outcome Data} {L : List (ℤ × ℤ × ℤ)} (hP : P.WF)
    (hr : findPointsWith c H P o process (.ofOutput u o) = .ok r)
    (hL : findPoints c H P o = .ok L) :
    r.total = (countedPoints u.pointsAtInfty u.onePoint L).length := by
  rw [(info_total_eq_of_findPointsWith_eq_ok hP hr hL).2, total_deliver_process, Int.zero_add]
  rfl

/-- What the program prints under `-q` for a command line on which the search
`Ratpoints.findPoints` returns the list `L`: the string before the points, the points of `L` that
the callback of the program counts (`Ratpoints.Cli.countedPoints`: all but those at infinity under
`-i`, only the first of these under `-1`) in the format, with the string between them in between,
none under `-z`, and the string after the points; it exits with the status `0`. -/
theorem run_eq_of_findPoints_eq_ok {args : List String} {c : List ℤ} {H : ℕ}
    {s : SieveOptions} {o : Options} {u : Output} {L : List (ℤ × ℤ × ℤ)}
    (hi : input args = .ok (c, H, s, o, u)) (hq : u.quiet = true)
    (hL : findPoints c H (sieveParams s) o = .ok L) :
    run args = (printString u.stringBefore ++ (printString u.stringBetween).intercalate
        ((if u.noOutput then [] else countedPoints u.pointsAtInfty u.onePoint L).map fun p ↦
          formatPoint (o.noCheck || o.noY) p.1 p.2.2 p.2.1 (u.printFormat.getD "").toList) ++
      printString u.stringAfter, 0) := by
  obtain ⟨r, hr⟩ := exists_findPointsWith_eq_ok_of_findPoints_eq_ok process (.ofOutput u o) hL
  rw [run_eq_of_findPointsWith_eq_ok hi hr hL, preamble_eq_empty_of_quiet c H hq,
    report_eq_empty_of_quiet s o hq, String.empty_append, String.append_empty]

/-- Under `-q -1`, without `-z`, the program prints the first point `p` of the list of
`Ratpoints.findPoints` that `-i` keeps (all of it unless `-i`, which drops the points at infinity),
in the format, between the string before the points and the string after them. -/
theorem run_eq_of_onePoint {args : List String} {c : List ℤ} {H : ℕ} {s : SieveOptions}
    {o : Options} {u : Output} {L : List (ℤ × ℤ × ℤ)} {p : ℤ × ℤ × ℤ}
    (hi : input args = .ok (c, H, s, o, u)) (hq : u.quiet = true) (h1 : u.onePoint = true)
    (hz : u.noOutput = false) (hL : findPoints c H (sieveParams s) o = .ok L)
    (hK : (L.filter fun q ↦ u.pointsAtInfty || q.2.2 != 0).head? = some p) :
    run args = (printString u.stringBefore ++
      formatPoint (o.noCheck || o.noY) p.1 p.2.2 p.2.1 (u.printFormat.getD "").toList ++
      printString u.stringAfter, 0) := by
  rw [run_eq_of_findPoints_eq_ok hi hq hL]
  simp [countedPoints, h1, hz, List.take_one, hK, String.intercalate_singleton]

end Ratpoints.Cli

end

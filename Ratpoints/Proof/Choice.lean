/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Proof.BlockPlan
public import Ratpoints.Proof.ChoiceModuli
public import Ratpoints.Proof.Forbidden

import Ratpoints.Proof.Params
import Ratpoints.Proof.Tables
import Std.Tactic.Do

/-!
# The choice of the moduli

The choice of the moduli and the cut points from the curve (`Ratpoints.sievingInfo`) either exits,
when the curve has no points modulo a prime that it examines, or gives what the run needs
(`Ratpoints.IsSievingInfo`): sound sieve entries with the fields that the packing reads and the
tables of inverses of their factors, prime entries wherever the count of factors is zero, the
reciprocals of the moduli in their order, a first decision whose cut points the run can use
(`Ratpoints.Sieve.DecisionWF`), sound forbidden divisors and a store of the tables of rows that fits
every entry, for any values of the doubles of the cost model.

The loop of the tables (`Ratpoints.tablesLoop`) keeps the tables of the primes looked at at their
positions, prime candidates, sound forbidden divisors and the store of the rows of the primes
(`Ratpoints.TableLoop.WF`); the rest of the choice (`Ratpoints.choiceTail`) offers the composite
moduli, runs the stages and ends with one sieve entry for each candidate of the pool, made for its
position (`Ratpoints.IsChoiceEntries`), whose tables of rows the store then fits.

## Main definitions

* `Ratpoints.Sieve.SieveEntry.IsSound`: a sieve entry that lets the numerator of every point
  through.
* `Ratpoints.IsSievingInfo`: what the run needs of the result of the choice.
* `Ratpoints.TableLoop.WF`: the state of the loop of the tables.
* `Ratpoints.IsChoiceEntries`: the sieve entries of the choice, each made for its position.

## Main statements

* `Ratpoints.SieveOptions.numPrimes_normalize_le`,
  `Ratpoints.SieveOptions.maxForbidden_normalize_nonneg`: the normalized options look at most
  `Ratpoints.numPrimes` primes and test a nonnegative number of forbidden divisors.
* `Ratpoints.IsModulusEntry.isSound`: an entry of a modulus as the choice makes it is sound.
* `Ratpoints.tablesLoop_spec`: the loop of the tables.
* `Ratpoints.isSievingInfo_choiceEnd`, `Ratpoints.choiceTail_spec`: the end of the choice.
* `Ratpoints.sievingInfo_spec`: the contract of the choice.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace Ratpoints

namespace Sieve

/-- A sieve entry that lets the numerator of every point of the curve `y ^ 2 = F(x, z)` with the
coefficient list `c` through: its modulus is positive, and its row of the denominator `b` admits the
numerator `a` of every triple `(a, y, b)` with `gcd(a, b) = 1` and `y ^ 2 = F(a, b)`. The choice of
the moduli makes only such entries (`Ratpoints.sievingInfo_spec`). -/
structure SieveEntry.IsSound (c : List ℤ) (e : SieveEntry) : Prop where
  /-- The modulus is positive. -/
  pos : 0 < e.p
  /-- The row of the denominator of every point admits its numerator. -/
  admits_of_sq_eq {a y : ℤ} {b : ℕ} (hab : Int.gcd a b = 1) (hy : y ^ 2 = binaryForm c a b) :
    e.admits b a = true

end Sieve

open Sieve

/-- A sieve entry of a modulus as the choice makes it is sound. -/
theorem IsModulusEntry.isSound {c : List ℤ} {m : ℕ} {s : SieveEntry} (h : IsModulusEntry c m s) :
    s.IsSound c :=
  ⟨Nat.zero_lt_of_lt h.packable.one_lt, fun hab hy ↦ h.admits_of_sq_eq hab hy⟩

/-- What the run needs of the result `si` of the choice of the moduli for the curve
`y ^ 2 = F(x, z)` with the coefficient list `c` and the largest denominator `bHigh`: sound sieve
entries (`Ratpoints.Sieve.SieveEntry.IsSound`), with the fields that the packing reads
(`Ratpoints.Sieve.SieveEntry.Packable`) and the tables of inverses of their factors
(`Ratpoints.Sieve.Factor.HasInverses`), each with no factors counted a prime entry of the table
(`Ratpoints.Sieve.SieveEntry.IsPrimeEntry`), as the third stage needs; the reciprocals of the moduli
in the order of the entries; the first decision, from the block `0` on, with the cut points of the
parameters, well-formed for the entries (`Ratpoints.Sieve.DecisionWF`); the forbidden divisors among
those that the loops of the tables and of the further primes may record
(`Ratpoints.Sieve.IsForbiddenEntry`, `Ratpoints.Sieve.IsForbiddenVal`); a store of the tables of
rows that fits all the entries, the reserve included (`Ratpoints.Sieve.RowStore.Fits`); and the test
of the denominators only for even degree. -/
structure IsSievingInfo (c : List ℤ) (bHigh : ℕ) (si : SievingInfo) : Prop where
  /-- The sieve entries are sound. -/
  isSound : ∀ e ∈ si.entries, e.IsSound c
  /-- The sieve entries have the fields that the packing reads. -/
  packable : ∀ e ∈ si.entries, e.Packable
  /-- The factors of the sieve entries have their tables of inverses. -/
  hasInverses : ∀ e ∈ si.entries, e.HasInverses
  /-- An entry with no factors counted is a prime entry of the table. -/
  isPrimeEntry_of_nf : ∀ e ∈ si.entries, e.nf = 0 → e.IsPrimeEntry
  /-- The reciprocals of the moduli, in the order of the entries. -/
  magics_eq : si.magics.toList = si.entries.map fun e ↦ magic e.p
  /-- The first decision is well-formed. -/
  decisionWF : DecisionWF si.entries si.params.sp1 ⟨0, si.params.sp2, si.params.sp3⟩
  /-- The forbidden divisors tested with words are sound. -/
  isForbiddenEntry : ∀ e ∈ si.forb, IsForbiddenEntry c (degree c) bHigh e
  /-- The forbidden divisors tested by their valuations are sound. -/
  isForbiddenVal : ∀ e ∈ si.forbVal, IsForbiddenVal c (degree c) bHigh e
  /-- The store of the tables of rows fits all the entries. -/
  fits : si.store.Fits si.entries
  /-- The denominators are tested only for even degree. -/
  degree_mod_two_eq_zero_of_checkDenom : si.checkDenom = true → degree c % 2 = 0

/-- The normalized options look at most `Ratpoints.numPrimes` primes. -/
theorem SieveOptions.numPrimes_normalize_le (s : SieveOptions) :
    s.normalize.numPrimes ≤ (Ratpoints.numPrimes : ℤ) := by
  simp only [SieveOptions.normalize]
  lia

/-- The normalized options test a nonnegative number of forbidden divisors. -/
theorem SieveOptions.maxForbidden_normalize_nonneg (s : SieveOptions) :
    0 ≤ s.normalize.maxForbidden := by
  simp only [SieveOptions.normalize]
  split <;> lia [defaultMaxForbidden]

/-! ### The loop of the tables -/

-- The examination of a prime, as a value: the contracts read it through its own lemmas.
private theorem examinePrime?_value (c : List ℤ) (d p : ℕ) (u : Bool) :
    ⦃ True ⦄ examinePrime? c d p u ⦃ fun r ↦ r = Id.run (examinePrime? c d p u) ⦄ :=
  ⟨fun _ ↦ rfl⟩

/-- The state of the loop of the tables (`Ratpoints.TableLoop`) for the curve with the coefficient
list `c` and the largest denominator `bHigh`: at most `Ratpoints.numPrimes` primes to look at, the
tables of the primes those of `Ratpoints.Sieve.examinePrime` at their positions
(`Ratpoints.IsExaminedPrimeSe`), prime candidates (`Ratpoints.ModulusCandidate.IsPrime`), sound
forbidden divisors and the store of the tables of rows of the primes
(`Ratpoints.Sieve.PrimeStore`). -/
structure TableLoop.WF (c : List ℤ) (bHigh : ℕ) (st : TableLoop) : Prop where
  /-- At most `Ratpoints.numPrimes` primes to look at. -/
  pnLim_le : st.pnLim ≤ numPrimes
  /-- The tables of the primes at their positions. -/
  primeSe : IsExaminedPrimeSe c st.primeSe
  /-- Prime candidates. -/
  isPrime : ∀ e ∈ st.pool, e.IsPrime c
  /-- Sound forbidden divisors tested with words. -/
  ba : ∀ e ∈ st.ba, IsForbiddenEntry c (degree c) bHigh e
  /-- Sound forbidden divisors tested by their valuations. -/
  val : ∀ e ∈ st.val, IsForbiddenVal c (degree c) bHigh e
  /-- The store of the tables of rows of the primes. -/
  store : PrimeStore st.store

theorem IsExaminedPrimeSe.push_none {c : List ℤ} {primeSe : Array (Option (Entry × Float))}
    (h : IsExaminedPrimeSe c primeSe) : IsExaminedPrimeSe c (primeSe.push none) := fun k t r hk ↦ by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push] at hk
  split at hk
  · simp at hk
  · exact h k t r (by simpa [Array.getD_eq_getD_getElem?] using hk)

theorem IsExaminedPrimeSe.set!_push_none {c : List ℤ} {primeSe : Array (Option (Entry × Float))}
    (h : IsExaminedPrimeSe c primeSe) {pn : ℕ} (hpn : pn < numPrimes) (hs : primeSe.size = pn)
    (r : Float) :
    IsExaminedPrimeSe c
      ((primeSe.push none).set! pn (some (examinePrime c (degree c) primeTable[pn]!, r))) :=
  fun k t r' hk ↦ by
    simp only [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds, Array.getElem?_push, Array.size_push] at hk
    split at hk
    · rename_i hk'
      obtain ⟨rfl, -⟩ := hk'
      simp only [show pn < primeSe.size + 1 by lia, ↓reduceIte, Option.getD_some,
        Option.some.injEq, Prod.mk.injEq] at hk
      exact ⟨hpn, hk.1.symm⟩
    · split at hk
      · simp at hk
      · exact h k t r' (by simpa [Array.getD_eq_getD_getElem?] using hk)

-- The forbidden divisor of a prime, as a value: the contracts read it through its own lemmas.
private theorem forbiddenOfPrime_value (c : List ℤ) (d p bHigh : ℕ) (cm : Array ℕ) (atInf : Bool) :
    ⦃ True ⦄ forbiddenOfPrime c d p bHigh cm atInf
    ⦃ fun r ↦ r = Id.run (forbiddenOfPrime c d p bHigh cm atInf) ⦄ :=
  ⟨fun _ ↦ rfl⟩

theorem TableLoop.WF.push_ba {c : List ℤ} {bHigh : ℕ} {st : TableLoop} (h : st.WF c bHigh)
    {f : ForbiddenEntry} (hf : IsForbiddenEntry c (degree c) bHigh f) :
    TableLoop.WF c bHigh { st with ba := st.ba.push f } :=
  ⟨h.pnLim_le, h.primeSe, h.isPrime, Array.forall_mem_push.mpr ⟨hf, h.ba⟩, h.val, h.store⟩

theorem TableLoop.WF.push_val {c : List ℤ} {bHigh : ℕ} {st : TableLoop} (h : st.WF c bHigh)
    {f : ForbiddenVal} (hf : IsForbiddenVal c (degree c) bHigh f) :
    TableLoop.WF c bHigh { st with val := st.val.push f } :=
  ⟨h.pnLim_le, h.primeSe, h.isPrime, h.ba, Array.forall_mem_push.mpr ⟨hf, h.val⟩, h.store⟩

/-- A forbidden divisor tested with words that the prime at the position `pn < numPrimes` gives from
what its table hands back, recorded. -/
theorem TableLoop.WF.push_ba_of_run {c : List ℤ} {bHigh : ℕ} {st : TableLoop} (h : st.WF c bHigh)
    {pn : ℕ} (hpn : pn < numPrimes) {u : Bool} {t : Entry} {cm : Array ℕ} {code : ℕ} {r : Float}
    (he : Id.run (examinePrime? c (degree c) primeTable[pn]! u) = some (t, cm, code, r))
    {f : ForbiddenEntry}
    (hf : Id.run (forbiddenOfPrime c (degree c) primeTable[pn]! bHigh cm
      t.isFSquare[primeTable[pn]!]!) = some (.inl f)) :
    TableLoop.WF c bHigh { st with ba := st.ba.push f } :=
  h.push_ba (isForbiddenEntry_of_run_examinePrime?_eq_some hpn he hf)

/-- A forbidden divisor tested by its valuation that the prime at the position `pn < numPrimes`
gives from what its table hands back, recorded. -/
theorem TableLoop.WF.push_val_of_run {c : List ℤ} {bHigh : ℕ} {st : TableLoop} (h : st.WF c bHigh)
    {pn : ℕ} (hpn : pn < numPrimes) {u : Bool} {t : Entry} {cm : Array ℕ} {code : ℕ} {r : Float}
    (he : Id.run (examinePrime? c (degree c) primeTable[pn]! u) = some (t, cm, code, r))
    {f : ForbiddenVal}
    (hf : Id.run (forbiddenOfPrime c (degree c) primeTable[pn]! bHigh cm
      t.isFSquare[primeTable[pn]!]!) = some (.inr f)) :
    TableLoop.WF c bHigh { st with val := st.val.push f } :=
  h.push_val (isForbiddenVal_of_run_examinePrime?_eq_some hpn he hf)

/-- The state of the loop of the tables after the prime at the position `pn = st.primeSe.size`,
which says something, with its candidate, its table and its table of rows. -/
theorem TableLoop.WF.push_ofPrime {c : List ℤ} {bHigh : ℕ} {st : TableLoop} (h : st.WF c bHigh)
    {pn : ℕ} (hs : st.primeSe.size = pn) (hpn : pn < numPrimes) {u : Bool} {t : Entry}
    {cm : Array ℕ} {code : ℕ} {r : Float}
    (he : Id.run (examinePrime? c (degree c) primeTable[pn]! u) = some (t, cm, code, r))
    (ct U D cc : Float) (atInf : Bool) (nWeak : ℕ) :
    TableLoop.WF c bHigh
      { pool := st.pool.push (phase1Key ct U D cc (ModulusCandidate.ofPrime pn t r code)),
        pnLim := st.pnLim, nWeak, primeSe := (st.primeSe.push none).set! pn (some (t, r)),
        pinf := st.pinf.push atInf, ba := st.ba, val := st.val,
        store := st.store.insertIfNew (.prime primeTable[pn]!) (primeRows primeTable[pn]!) } := by
  have ht := eq_examinePrime_of_lt_numPrimes_of_run_examinePrime?_eq_some hpn he
  refine ⟨h.pnLim_le, ht ▸ h.primeSe.set!_push_none hpn hs r,
    Array.forall_mem_push.mpr ⟨?_, h.isPrime⟩, h.ba, h.val,
    h.store.insertIfNew (one_lt_getElem!_primeTable hpn).le⟩
  exact (isPrime_ofPrime hpn he 0.0 0.0).of_eq rfl rfl rfl

/-- The state of the loop of the tables after the prime at the position `pn`, which says nothing. -/
theorem TableLoop.WF.push_none {c : List ℤ} {bHigh : ℕ} {st : TableLoop} (h : st.WF c bHigh)
    (atInf : Bool) :
    TableLoop.WF c bHigh
      { st with pinf := st.pinf.push atInf, primeSe := st.primeSe.push none } :=
  ⟨h.pnLim_le, h.primeSe.push_none, h.isPrime, h.ba, h.val, h.store⟩

/-- The contract of `Ratpoints.examineInLoop` at the position `pn = st.primeSe.size` below
`Ratpoints.numPrimes`: at none the curve has no points; otherwise the state of the loop of the
tables stays one (`Ratpoints.TableLoop.WF`), with the table of the prime at its
position. -/
theorem examineInLoop_spec (c : List ℤ) (u checkDenom : Bool) (maxForbidden bHigh : ℕ)
    (ct : Float) (est : RunEstimate) (cc : Float) (pn : ℕ) (st : TableLoop) :
    ⦃ st.WF c bHigh ∧ st.primeSe.size = pn ∧ pn < numPrimes ⦄
    examineInLoop c (degree c) u checkDenom maxForbidden bHigh ct est cc pn st
    ⦃ fun r ↦ (r = none → ∀ H q, ¬IsPoint c H q) ∧ ∀ st', r = some st' →
        st'.WF c bHigh ∧ st'.primeSe.size = pn + 1 ∧ st'.pnLim = st.pnLim ⦄ := by
  vcgen [examineInLoop, examinePrime?_value, forbiddenOfPrime_value]
  all_goals simp only [reduceCtorEq, false_implies, implies_true, true_and, and_true,
    Option.some.injEq, forall_eq'] at *
  all_goals obtain ⟨h, hs, hpn⟩ := ‹TableLoop.WF c bHigh st ∧ _›
  all_goals try -- the exit: `examinePrime?` returns none
    exact fun _ ↦ not_isPoint_of_lt_numPrimes_of_run_examinePrime?_eq_none hpn
      (‹_ = Id.run _›.symm.trans (‹_ = _›.trans (Option.eq_none_iff_forall_ne_some.mpr
        fun ⟨t, cm, k, r⟩ ↦ ‹∀ t cm k r, _ = some (t, cm, k, r) → False› t cm k r)))
  all_goals subst ‹_ = some (_, _, _, _)›
  all_goals have he := ‹some (_, _, _, _) = _›.symm
  all_goals refine ⟨?_, by simp [hs]⟩
  all_goals try subst ‹_ = some (Sum.inl _)›
  all_goals try subst ‹_ = some (Sum.inr _)›
  all_goals first
    | exact (h.push_ofPrime hs hpn he ..).push_ba_of_run hpn he ‹some (Sum.inl _) = _›.symm
    | exact (h.push_ofPrime hs hpn he ..).push_val_of_run hpn he ‹some (Sum.inr _) = _›.symm
    | exact h.push_ofPrime hs hpn he ..
    | exact (h.push_none _).push_ba_of_run hpn he ‹some (Sum.inl _) = _›.symm
    | exact (h.push_none _).push_val_of_run hpn he ‹some (Sum.inr _) = _›.symm
    | exact h.push_none _

-- The number of candidates that the rule of the first stage takes, as a value: no contract reads
-- it.
private theorem primesForPhase1_true (pool : Array ModulusCandidate) (bpw target : Float)
    (extra : ℕ) : ⦃ True ⦄ primesForPhase1 pool bpw target extra ⦃ fun _ ↦ True ⦄ :=
  ⟨fun _ ↦ trivial⟩

/-- The contract of `Ratpoints.raiseLimit` while fewer than `Ratpoints.numPrimes` primes are to be
looked at: the state of the loop of the tables stays one, with its tables. -/
theorem raiseLimit_spec (c : List ℤ) (bHigh : ℕ) (s : SieveOptions) (bpws target : Float)
    (sp2e : ℕ) (st : TableLoop) :
    ⦃ st.WF c bHigh ∧ st.pnLim < numPrimes ⦄ raiseLimit s bpws target sp2e st
    ⦃ fun st' ↦ st'.WF c bHigh ∧ st'.primeSe = st.primeSe ⦄ := by
  vcgen [raiseLimit, primesForPhase1_true]
  all_goals obtain ⟨h, hlt⟩ := ‹TableLoop.WF c bHigh st ∧ _›
  all_goals exact ⟨by split <;> lia [h.pnLim_le], h.primeSe,
    fun e he ↦ h.isPrime e (mem_of_mem_sortFrom he), h.ba, h.val, h.store⟩

/-- The state of the loop of the tables at its start, for the number of primes to look at of
options that look at most `Ratpoints.numPrimes` primes. -/
theorem TableLoop.wf_init (c : List ℤ) (bHigh : ℕ) {s : SieveOptions}
    (hs : s.numPrimes ≤ (numPrimes : ℤ)) : TableLoop.WF c bHigh { pnLim := s.numPrimes.toNat } :=
  ⟨by lia, fun _ _ _ h ↦ absurd h (by simp), fun _ h ↦ absurd h (by simp),
    fun _ h ↦ absurd h (by simp), fun _ h ↦ absurd h (by simp), primeStore_empty⟩

/-- The invariant of the loop of `Ratpoints.tablesLoop` over the positions of the table, whose
state is the value of a return and the state of the loop: the state of the loop
(`Ratpoints.TableLoop.WF`), with the tables of the positions looked at while the loop goes on; the
value of a return an exit, at which the curve has no points. -/
def TablesLoopInvariant (c : List ℤ) (bHigh : ℕ) :
    Std.WP.Invariant ℕ (Option (Except ℕ TableLoop) × TableLoop) Prop :=
  Std.WP.Invariant.withEarlyReturnNewDo Prop
    (fun pref suff st ↦ st.WF c bHigh ∧ (suff ≠ [] → st.primeSe.size = pref.length))
    (fun ret _ ↦ (∀ p, ret = .error p → ∀ H q, ¬IsPoint c H q) ∧ ∀ st, ret = .ok st → st.WF c bHigh)

/-- The contract of `Ratpoints.tablesLoop`, for options that look at most `Ratpoints.numPrimes`
primes and any values of the doubles: at an exit the curve has no points; otherwise the state of the
loop is one (`Ratpoints.TableLoop.WF`). -/
theorem tablesLoop_spec (c : List ℤ) (u checkDenom mayExtend : Bool) (s : SieveOptions)
    (bHigh : ℕ) (target ct : Float) (est : RunEstimate) (cc bpws : Float) (sp2e : ℕ) :
    ⦃ s.numPrimes ≤ (numPrimes : ℤ) ⦄
    tablesLoop c (degree c) u checkDenom mayExtend s bHigh target ct est cc bpws sp2e
    ⦃ fun r ↦ (∀ p, r = .error p → ∀ H q, ¬IsPoint c H q) ∧ ∀ st, r = .ok st → st.WF c bHigh ⦄ := by
  vcgen [tablesLoop, examineInLoop_spec, raiseLimit_spec c bHigh] invariants
  | inv1 => TablesLoopInvariant c bHigh
  all_goals simp only [TablesLoopInvariant, Lean.Order.meet_prop_eq_and, Lean.Order.join_prop_eq_or,
    Lean.Order.iSup_prop_eq_exists, Lean.Order.ofProp_prop_eq, reduceCtorEq, false_and, or_false,
    false_or, true_and, and_false, Option.some.injEq, exists_eq_left', exists_false, and_true,
    Except.error.injEq, Except.ok.injEq, forall_eq', false_implies, implies_true,
    ← Option.eq_none_iff_forall_ne_some, ne_eq, List.cons_ne_nil, not_false_eq_true,
    forall_const, List.length_append, List.length_singleton, not_true_eq_false] at *
  all_goals grind [TableLoop.wf_init, TableLoop.WF.pnLim_le,
    Std.Legacy.Range.length_eq_of_toList_eq_append_cons,
    Std.Legacy.Range.lt_of_toList_eq_append_cons]

/-! ### The end of the choice -/

-- The first two stages, as a value: `Ratpoints.firstStages_run` reads it.
private theorem firstStages_value (pool : Array ModulusCandidate) (s : SieveOptions)
    (target ct : Float) (est : RunEstimate) (bpws : Float) (sp2e : ℕ) :
    ⦃ True ⦄ firstStages pool s target ct est bpws sp2e
    ⦃ fun r ↦ r = Id.run (firstStages pool s target ct est bpws sp2e) ⦄ :=
  ⟨fun _ ↦ rfl⟩

theorem ChoicePoolWF.sortFrom {c : List ℤ} {sp2 : ℕ} {pool : Array ModulusCandidate}
    (h : ChoicePoolWF c sp2 pool) (hs : sp2 ≤ pool.size)
    (le : ModulusCandidate → ModulusCandidate → Bool) :
    ChoicePoolWF c sp2 (Ratpoints.sortFrom pool sp2 le) := by
  refine ⟨fun n hn hk ↦ ?_, fun n hn hk ↦ ?_⟩
  · rw [getElem_sortFrom_of_lt hs le hk]
    exact h.exists_isChoiceEntry_of_lt n _ hk
  · obtain ⟨k, hk', hsk, he⟩ := exists_getElem_sortFrom_eq le hk hn
    rw [he]
    exact h.isPrime k hk' hsk

/-- Every candidate of the pool after the stages has its sieve entry, made for its position. -/
theorem ChoicePoolWF.exists_isChoiceEntry {c : List ℤ} {sp2 : ℕ} {pool : Array ModulusCandidate}
    (h : ChoicePoolWF c sp2 pool) (n : ℕ) (hn : n < pool.size) :
    ∃ se, pool[n].ssp = some se ∧ IsChoiceEntry c n se ∧ (sp2 ≤ n → se.nf = 0) := by
  by_cases hk : n < sp2
  · obtain ⟨se, hs, he⟩ := h.exists_isChoiceEntry_of_lt n hn hk
    exact ⟨se, hs, he, fun h' ↦ absurd hk (by lia)⟩
  · obtain ⟨pn, hpn, r, -, hs⟩ := (h.isPrime n hn (by lia)).exists_eq
    exact ⟨_, hs, isChoiceEntry_primeEntry c hpn r n, fun _ ↦ rfl⟩

/-- The sieve entries `es` of the choice, each made for its position (`Ratpoints.IsChoiceEntry`),
those from the end `sp2` of the second stage on with no factors counted. -/
def IsChoiceEntries (c : List ℤ) (sp2 : ℕ) (es : List SieveEntry) : Prop :=
  ∀ n (hn : n < es.length), IsChoiceEntry c n es[n] ∧ (sp2 ≤ n → es[n].nf = 0)

theorem IsChoiceEntries.exists_isChoiceEntry_of_mem {c : List ℤ} {sp2 : ℕ} {es : List SieveEntry}
    (h : IsChoiceEntries c sp2 es) {e : SieveEntry} (he : e ∈ es) : ∃ n, IsChoiceEntry c n e := by
  obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem he
  exact ⟨n, (h n hn).1⟩

/-- The store of the loop of the tables with the tables of rows of the sieve entries of the choice
fits them. -/
theorem IsChoiceEntries.fits_foldl_addTables {c : List ℤ} {sp2 : ℕ} {es : List SieveEntry}
    (h : IsChoiceEntries c sp2 es) {store : RowStore} (hs : PrimeStore store) :
    RowStore.Fits (es.foldl (fun s e ↦ e.addTables s) store) es := by
  have hm := (RowStore.madeFor_nil c (degree c) hs.1 hs.2).foldl_addTables es
    (fun n hn ↦ SieveEntry.refFits_of_refInit_eq ((Nat.zero_add n).symm ▸ (h n hn).1.refInit)
      fun _ ↦ (h n hn).1.isModulusEntry.p_eq_modulus) fun e he t ht ↦
    have ⟨_, he'⟩ := h.exists_isChoiceEntry_of_mem he
    (he'.isModulusEntry.buildable _ ht).1
  exact ⟨_, hm.storeHolds, fun n hn ↦ (h n hn).1.isModulusEntry.rowsFit_runRows (h n hn).1.refInit
    (List.getElem?_eq_getElem hn)⟩

/-- The sieve entries at the end of the choice, after the third stage that ends at `t.sp3`: one for
each candidate of the pool, each made for its position (`Ratpoints.IsChoiceEntries`). -/
theorem isChoiceEntries_choiceEnd {c : List ℤ} {sp2 : ℕ} {t : ThirdState} (ht : t.WF c sp2)
    (store : RowStore) :
    IsChoiceEntries c sp2 (choiceEnd t sp2 store).1 ∧
      (choiceEnd t sp2 store).1.length = t.pool.size := by
  have hp : ChoicePoolWF c sp2 (if sp2 < t.pool.size then sortFrom t.pool sp2 ModulusCandidate.rLe
      else t.pool) ∧ (if sp2 < t.pool.size then sortFrom t.pool sp2 ModulusCandidate.rLe
      else t.pool).size = t.pool.size := by
    split
    · exact ⟨ht.1.sortFrom (ht.2.1.trans ht.2.2) _, size_sortFrom (by lia) _⟩
    · exact ⟨ht.1, rfl⟩
  have h := length_filterMap_ssp_and_forall hp.1.exists_isChoiceEntry
  exact ⟨h.2, h.1.trans hp.2⟩

theorem IsChoiceEntries.nf_eq_zero_of_mem_drop {c : List ℤ} {sp2 : ℕ} {es : List SieveEntry}
    (h : IsChoiceEntries c sp2 es) {e : SieveEntry} (he : e ∈ es.drop sp2) : e.nf = 0 := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
  rw [List.getElem_drop]
  exact (h _ _).2 (Nat.le_add_right _ _)

/-- The result of the choice after its third stage (`Ratpoints.choiceEnd`), with the cut points of
the stages, sound forbidden divisors, the store of the loop of the tables and the test of the
denominators only for even degree: what the run needs (`Ratpoints.IsSievingInfo`). -/
theorem isSievingInfo_choiceEnd {c : List ℤ} {bHigh sp1 sp2 : ℕ} {t : ThirdState}
    (ht : t.WF c sp2) (h12 : sp1 ≤ sp2) {store : RowStore} (hs : PrimeStore store)
    {forb : List ForbiddenEntry} {forbVal : List ForbiddenVal}
    (hforb : ∀ e ∈ forb, IsForbiddenEntry c (degree c) bHigh e)
    (hval : ∀ e ∈ forbVal, IsForbiddenVal c (degree c) bHigh e) {checkDenom : Bool}
    (hcd : checkDenom = true → degree c % 2 = 0) {P : Params} (h1 : P.sp1 = sp1)
    (h2 : P.sp2 = sp2) (h3 : P.sp3 = t.sp3) :
    IsSievingInfo c bHigh
      { params := P, entries := (choiceEnd t sp2 store).1, magics := (choiceEnd t sp2 store).2.1,
        forb, forbVal, store := (choiceEnd t sp2 store).2.2, checkDenom } := by
  obtain ⟨hE, hl⟩ := isChoiceEntries_choiceEnd ht store
  subst h1 h2
  refine ⟨fun e he ↦ (hE.exists_isChoiceEntry_of_mem he).elim fun _ h ↦ h.isModulusEntry.isSound,
    fun e he ↦ (hE.exists_isChoiceEntry_of_mem he).elim fun _ h ↦ h.isModulusEntry.packable,
    fun e he ↦ (hE.exists_isChoiceEntry_of_mem he).elim fun _ h ↦ h.isModulusEntry.hasInverses,
    fun e he ↦ (hE.exists_isChoiceEntry_of_mem he).elim fun _ h ↦ h.isPrimeEntry, ?_,
    ⟨h12, h3 ▸ ht.2.1, h3 ▸ hl ▸ ht.2.2, fun _ he ↦ hE.nf_eq_zero_of_mem_drop he⟩, hforb, hval,
    hE.fits_foldl_addTables hs, hcd⟩
  simp only [choiceEnd, List.toList_toArray]
  exact List.map_congr_left fun e he ↦
    (hE.exists_isChoiceEntry_of_mem he).elim fun _ h ↦ h.isModulusEntry.packable.magic_eq

/-- The contract of `Ratpoints.thirdOf`: `Ratpoints.thirdStage_spec` from the end `sp2` of the
second stage. -/
theorem thirdOf_spec (c : List ℤ) (u mayExtend : Bool) (s : SieveOptions) (checkRel : Float)
    (est : RunEstimate) (bpw : Float) (pool : Array ModulusCandidate) (sp2 pnLim : ℕ) :
    ⦃ ChoicePoolWF c sp2 pool ∧ sp2 ≤ pool.size ⦄
    thirdOf c (degree c) u mayExtend s checkRel est bpw pool sp2 pnLim
    ⦃ fun r ↦ (∀ p, r = .error p → ∀ H q, ¬IsPoint c H q) ∧ ∀ t, r = .ok t → t.WF c sp2 ⦄ := by
  vcgen [thirdOf, thirdStage_spec (sp2 := sp2)]
  exact ⟨‹_ ∧ _›.1, Nat.le_refl _, ‹_ ∧ _›.2⟩

/-- `Ratpoints.firstStages_run` for the candidates of the pool after the composite moduli, sorted by
their keys. -/
theorem firstStages_post {c : List ℤ} {primeSe : Array (Option (Entry × Float))}
    {pws : Array Power} {pool₀ : Array ModulusCandidate}
    (h : ∀ e ∈ pool₀, e.IsPrimeOrComposite c primeSe pws)
    {s : SieveOptions} {target ct : Float} {est : RunEstimate} {bpws : Float} {sp2e : ℕ}
    {pool : Array ModulusCandidate} {sp1 sp2 : ℕ}
    (he : (pool, sp1, sp2) =
      Id.run (firstStages (sortFrom pool₀ 0 ModulusCandidate.keyLe) s target ct est bpws sp2e)) :
    (∀ e ∈ pool, e.IsPrimeOrComposite c primeSe pws) ∧ NfEqZeroFrom pool sp2 ∧ sp1 ≤ sp2 ∧
      sp2 ≤ pool.size :=
  firstStages_run (fun _ he _ ↦ he.of_eq rfl rfl rfl rfl) (fun e he ↦ h e (mem_of_mem_sortFrom he))
    he

/-- The candidates of the primes, keyed for the first stage, are candidates of the pool before the
stages. -/
theorem ModulusCandidate.isPrimeOrComposite_of_mem_map_phase1Key {c : List ℤ}
    {pool : Array ModulusCandidate} (h : ∀ e ∈ pool, e.IsPrime c) {ct U D cc : Float}
    {e : ModulusCandidate} (he : e ∈ pool.map (phase1Key ct U D cc))
    (primeSe : Array (Option (Entry × Float))) (pws : Array Power) :
    e.IsPrimeOrComposite c primeSe pws := by
  obtain ⟨e', he', rfl⟩ := Array.mem_map.mp he
  exact IsPrimeOrComposite.phase1Key (.inl (h e' he')) ct U D cc

-- The estimate of the run, as a value: no contract reads it.
private theorem runShape_true (a : ShapeArgs) (checkDenom : Bool) (forb : List ForbiddenEntry)
    (forbVal : List ForbiddenVal) : ⦃ True ⦄ runShape a checkDenom forb forbVal ⦃ fun _ ↦ True ⦄ :=
  ⟨fun _ ↦ trivial⟩

/-- The contract of `Ratpoints.choiceTail`, after the loop of the tables, with sound forbidden
divisors and the test of the denominators only for even degree: at an exit of the third stage the
curve has no points; otherwise the result is what the run needs (`Ratpoints.IsSievingInfo`). -/
theorem choiceTail_spec (c : List ℤ) (u mayExtend : Bool) (s : SieveOptions) (a : ShapeArgs)
    (bpw checkRel : Float) (checkDenom : Bool) (forb : List ForbiddenEntry)
    (forbVal : List ForbiddenVal) (st : TableLoop) :
    ⦃ st.WF c a.bHigh ∧ (∀ e ∈ forb, IsForbiddenEntry c (degree c) a.bHigh e) ∧
        (∀ e ∈ forbVal, IsForbiddenVal c (degree c) a.bHigh e) ∧
        (checkDenom = true → degree c % 2 = 0) ⦄
    choiceTail c (degree c) u mayExtend s a bpw checkRel checkDenom forb forbVal st
    ⦃ fun r ↦ (∀ p, r = .error p → ∀ H q, ¬IsPoint c H q) ∧
        ∀ si, r = .ok si → IsSievingInfo c a.bHigh si ⦄ := by
  vcgen [choiceTail, runShape_true, addModuli_spec, firstStages_value, stageEntries_spec c,
    thirdOf_spec]
  all_goals obtain ⟨h, hforb, hval, hcd⟩ := ‹TableLoop.WF c a.bHigh st ∧ _›
  · exact ⟨h.primeSe, h.pnLim_le,
      fun _ he ↦ ModulusCandidate.isPrimeOrComposite_of_mem_map_phase1Key h.isPrime he _ _⟩
  · obtain ⟨h1, h2, -, h4⟩ := firstStages_post ‹_› ‹_›
    exact ⟨h1, h2, h4⟩
  · exact ⟨‹_ ∧ _›.1, ‹_ ∧ _›.2 ▸ (firstStages_post ‹_› ‹_›).2.2.2⟩
  · subst ‹_ = Except.error _›
    obtain ⟨he, -⟩ := ‹(∀ p, _ = Except.error p → _) ∧ _›
    exact ⟨fun _ hp ↦ by cases hp; exact he _ rfl, nofun⟩
  · subst ‹_ = Except.ok _›
    obtain ⟨-, ht⟩ := ‹(∀ p, _ = Except.error p → _) ∧ _›
    refine ⟨nofun, fun _ hsi ↦ ?_⟩
    cases hsi
    exact isSievingInfo_choiceEnd (ht _ rfl) (firstStages_post ‹_› ‹_›).2.2.1 h.store hforb
      hval hcd rfl rfl rfl

-- The cost of a check, as a value: no contract reads it.
private theorem checkRelOf_true (c : List ℤ) (d H : ℕ) (s : SieveOptions) :
    ⦃ True ⦄ checkRelOf c d H s ⦃ fun _ ↦ True ⦄ :=
  ⟨fun _ ↦ trivial⟩

/-- The contract of the choice of the moduli and the cut points from the curve, for options that
look at most `Ratpoints.numPrimes` primes and test a nonnegative number of forbidden divisors
(normalized options, `Ratpoints.SieveOptions.numPrimes_normalize_le`,
`Ratpoints.SieveOptions.maxForbidden_normalize_nonneg`), the test of the denominators only for even
degree and any values of the doubles: at an exit, at a prime of the loop of the tables or of the
third stage without points modulo it, the curve has no points; otherwise the result is what the run
needs (`Ratpoints.IsSievingInfo`). -/
@[spec]
theorem sievingInfo_spec (c : List ℤ) (u checkDenom mayExtend : Bool) (s : SieveOptions)
    (a : ShapeArgs) (bpw : Float) :
    ⦃ s.numPrimes ≤ (numPrimes : ℤ) ∧ 0 ≤ s.maxForbidden ∧ (checkDenom = true → degree c % 2 = 0) ⦄
    sievingInfo c (degree c) u checkDenom mayExtend s a bpw
    ⦃ fun r ↦ (∀ p, r = .error p → ∀ H q, ¬IsPoint c H q) ∧
        ∀ si, r = .ok si → IsSievingInfo c a.bHigh si ⦄ := by
  vcgen [sievingInfo, checkRelOf_true, runShape_true, tablesLoop_spec, forbidden_spec,
    choiceTail_spec]
  all_goals obtain ⟨hn, -, hcd⟩ := ‹s.numPrimes ≤ (numPrimes : ℤ) ∧ _›
  · exact hn
  all_goals obtain ⟨he, hok⟩ := ‹(∀ p, _ = Except.error p → _) ∧ _›
  · subst ‹_ = Except.error _›
    exact ⟨fun _ hp ↦ by cases hp; exact he _ rfl, nofun⟩
  all_goals subst ‹_ = Except.ok _›
  · exact ⟨(hok _ rfl).ba, (hok _ rfl).val⟩
  · exact ⟨hok _ rfl, ‹_ ∧ _›.1, ‹_ ∧ _›.2, fun h ↦ hcd (Bool.and_eq_true_iff.mp h).1⟩
  · exact ⟨hok _ rfl, fun e he' ↦ (hok _ rfl).ba e (Array.mem_toList_iff.mp he'),
      fun e he' ↦ (hok _ rfl).val e (Array.mem_toList_iff.mp he'),
      fun h ↦ hcd (Bool.and_eq_true_iff.mp h).1⟩

end Ratpoints

end

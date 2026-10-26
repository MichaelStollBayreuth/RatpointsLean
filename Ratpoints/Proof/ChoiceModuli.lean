/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Proof.ChoicePool
public import Ratpoints.Proof.Containers
public import Ratpoints.Proof.Moduli
public import Ratpoints.Proof.Stages

import Ratpoints.Proof.Params
import Ratpoints.Proof.Tables
import Std.Tactic.Do

/-!
# The moduli of the choice

The candidates of the composite moduli that the choice offers (`Ratpoints.addModuli`) factor over
the primes looked at into factors whose tables the choice holds, with codes that
`Ratpoints.makeModulus` can read (`Ratpoints.IsFactorCode`), and the sieve entries that it makes of
them are sound, each at its position (`Ratpoints.IsChoiceEntry`); the candidates of the primes have
the sieve entries of their primes (`Ratpoints.ModulusCandidate.IsPrime`). After the stages, every
candidate has its sieve entry (`Ratpoints.ChoicePoolWF`), the third stage keeping it so and exiting
only at a prime modulo which the curve has no points (`Ratpoints.thirdStage_spec`).

## Main definitions

* `Ratpoints.IsExaminedPrimeSe`, `Ratpoints.Sieve.Power.IsExamined`: the tables of the primes and
  the records of the prime powers as the choice examines them.
* `Ratpoints.factorOfCode`, `Ratpoints.IsFactorCode`: the factor of a code of a composite modulus.
* `Ratpoints.ModulusCandidate.IsPrime`, `Ratpoints.ModulusCandidate.IsComposite`,
  `Ratpoints.ModulusCandidate.IsPrimeOrComposite`: the candidates before the stages.
* `Ratpoints.PowerTable.WF`, `Ratpoints.FacState.WF`: the state of `Ratpoints.addModuli`.
* `Ratpoints.IsChoiceEntry`: a sieve entry that the choice makes at a position.
* `Ratpoints.ChoicePoolWF`, `Ratpoints.ThirdState.WF`: the pool after the stages.

## Main statements

* `Ratpoints.factorCandidate_spec`, `Ratpoints.offerModulus_spec`, `Ratpoints.addModuli_spec`:
  the composite moduli offered.
* `Ratpoints.isFactorCode_of_getD_eq_some`, `Ratpoints.isFactorCode_add_of_getElem?_eq_some`: the
  codes of the primes and of the prime powers can be read.
* `Ratpoints.isChoiceEntry_primeEntry`, `Ratpoints.makeModulus_spec`: the sieve entries.
* `Ratpoints.stageEntries_spec`, `Ratpoints.thirdStage_spec`: the pool after the stages.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace Ratpoints

open Sieve

/-! ### The codes of the factors -/

/-- The factor of the code `code` of a composite modulus, as `Ratpoints.makeModulus` reads it: a
code below `Ratpoints.numPrimes` the table of the prime at that position from the loop of the tables
(`primeSe`), another the record of the prime power of its index (`pws`). -/
def factorOfCode (primeSe : Array (Option (Entry × Float))) (pws : Array Power) (code : ℕ) :
    Factor :=
  if code < numPrimes then .prime ((primeSe.getD code none).elim default (·.1))
  else .power pws[code - numPrimes]!

/-- The tables and densities of the loop of the tables (`primeSe`) for the curve with the
coefficient list `c`: each table that it holds is that of `Ratpoints.Sieve.examinePrime` for the
prime of the table at its position, one of the first `Ratpoints.numPrimes`. -/
def IsExaminedPrimeSe (c : List ℤ) (primeSe : Array (Option (Entry × Float))) : Prop :=
  ∀ k t r, primeSe.getD k none = some (t, r) →
    k < numPrimes ∧ t = examinePrime c (degree c) primeTable[k]!

/-- The record of a prime power as `Ratpoints.addModuli` examines it: the tables of
`Ratpoints.Sieve.examinePower` of a prime of the table, one of the first `Ratpoints.numPrimes`, with
a positive exponent, for either path of the reduction and either value of the flag `pinf`. -/
def Sieve.Power.IsExamined (c : List ℤ) (pw : Power) : Prop :=
  ∃ pn < numPrimes, ∃ e, 1 ≤ e ∧
    ∃ u pinf, pw = Id.run (examinePower c (degree c) primeTable[pn]! e u pinf)

/-- A code of a factor of a composite modulus that `Ratpoints.makeModulus` can read: a code below
`Ratpoints.numPrimes` of a prime whose table the loop of the tables holds, another the index of a
record of the prime powers. -/
structure IsFactorCode (c : List ℤ) (primeSe : Array (Option (Entry × Float))) (pws : Array Power)
    (code : ℕ) : Prop where
  /-- A code of a prime has its table. -/
  prime : code < numPrimes →
    ∃ r, primeSe.getD code none = some (examinePrime c (degree c) primeTable[code]!, r)
  /-- Another code has its record. -/
  power : numPrimes ≤ code → ∃ pw, pws[code - numPrimes]? = some pw ∧ pw.IsExamined c

/-- The factor of a code that `Ratpoints.makeModulus` can read is sound for every modulus
`0 < m < maxPrimeEven` that its modulus divides. -/
theorem IsFactorCode.isSound {c : List ℤ} {primeSe : Array (Option (Entry × Float))}
    {pws : Array Power} {code : ℕ} (h : IsFactorCode c primeSe pws code) {m : ℕ} (hm0 : 0 < m)
    (hm : m < maxPrimeEven) (hd : (factorOfCode primeSe pws code).modulus ∣ m) :
    (factorOfCode primeSe pws code).IsSound c m := by
  by_cases hc : code < numPrimes
  · obtain ⟨r, hr⟩ := h.prime hc
    simp only [factorOfCode, hc, ↓reduceIte, hr, Option.elim_some] at hd ⊢
    exact isSound_prime_examinePrime hc hd
  · obtain ⟨pw, hpw, pn, hpn, e, he, u, pinf, rfl⟩ := h.power (Nat.le_of_not_lt hc)
    simp only [factorOfCode, hc, ↓reduceIte, Array.getElem!_of_getElem? hpw] at hd ⊢
    exact isSound_power_run_examinePower u pinf hm0 hm hpn he hd

/-- A code that `Ratpoints.makeModulus` can read stays so when the records of the prime powers are
extended. -/
theorem IsFactorCode.extend {c : List ℤ} {primeSe : Array (Option (Entry × Float))}
    {pws pws' : Array Power} {code : ℕ} (h : IsFactorCode c primeSe pws code)
    (hx : pws.Extends pws') : IsFactorCode c primeSe pws' code :=
  ⟨h.prime, fun hc ↦ have ⟨pw, hpw, hok⟩ := h.power hc; ⟨pw, hx _ _ hpw, hok⟩⟩

/-- The factor of a code that `Ratpoints.makeModulus` can read stays the same when the records of
the prime powers are extended. -/
theorem IsFactorCode.factorOfCode_extend {c : List ℤ} {primeSe : Array (Option (Entry × Float))}
    {pws pws' : Array Power} {code : ℕ} (h : IsFactorCode c primeSe pws code)
    (hx : pws.Extends pws') : factorOfCode primeSe pws' code = factorOfCode primeSe pws code := by
  by_cases hc : code < numPrimes
  · simp [factorOfCode, hc]
  · obtain ⟨pw, hpw, -⟩ := h.power (Nat.le_of_not_lt hc)
    simp only [factorOfCode, hc, ↓reduceIte, Array.getElem!_of_getElem? hpw,
      Array.getElem!_of_getElem? (hx _ _ hpw)]

/-! ### The candidates -/

/-- The candidate of a prime as the loop of the tables and the third stage make it for the curve
with the coefficient list `c` (`Ratpoints.ModulusCandidate.ofPrime`): no factors counted or the
count `-1`, a prime of the table, one of the first `Ratpoints.numPrimes`, with its sieve entry
(`Ratpoints.primeEntry`) of the table of `Ratpoints.Sieve.examinePrime`. -/
structure ModulusCandidate.IsPrime (c : List ℤ) (e : ModulusCandidate) : Prop where
  /-- No factors counted, or the count `-1`. -/
  nf_le : e.nf ≤ 0
  /-- A prime of the table with its sieve entry. -/
  exists_eq : ∃ pn < numPrimes, ∃ r, e.p = primeTable[pn]! ∧
    e.ssp = some (primeEntry (examinePrime c (degree c) primeTable[pn]!) r)

/-- A candidate with the count of factors, the modulus and the sieve entry of a prime candidate is
one: the predicate reads neither the density, the key, the cost, the mask nor the codes. -/
theorem ModulusCandidate.IsPrime.of_eq {c : List ℤ} {e e' : ModulusCandidate} (h : e.IsPrime c)
    (hnf : e'.nf = e.nf) (hp : e'.p = e.p) (hs : e'.ssp = e.ssp) : e'.IsPrime c :=
  ⟨hnf ▸ h.nf_le, hp ▸ hs ▸ h.exists_eq⟩

/-- The candidate of a composite modulus as `Ratpoints.addModuli` offers it for the curve with the
coefficient list `c`, the tables of the loop of the tables `primeSe` and the records of the prime
powers `pws`: the count of its factors, with codes that `Ratpoints.makeModulus` can read and whose
moduli multiply to the modulus, odd, between `1` and `Ratpoints.maxPrimeEven`, and no sieve entry
yet. -/
structure ModulusCandidate.IsComposite (c : List ℤ) (primeSe : Array (Option (Entry × Float)))
    (pws : Array Power) (e : ModulusCandidate) : Prop where
  /-- The count of the factors. -/
  nf_eq : e.nf = e.fac.length
  /-- At least one factor. -/
  fac_ne_nil : e.fac ≠ []
  /-- No sieve entry yet. -/
  ssp_eq : e.ssp = none
  /-- The modulus is above `1`. -/
  one_lt : 1 < e.p
  /-- The modulus is below `Ratpoints.maxPrimeEven`. -/
  lt_maxPrimeEven : e.p < maxPrimeEven
  /-- The modulus is odd. -/
  odd : e.p % 2 = 1
  /-- The codes can be read. -/
  isFactorCode : ∀ code ∈ e.fac, IsFactorCode c primeSe pws code
  /-- The moduli of the factors multiply to the modulus. -/
  prod_eq : (e.fac.map fun code ↦ (factorOfCode primeSe pws code).modulus).prod = e.p

theorem ModulusCandidate.IsComposite.extend {c : List ℤ}
    {primeSe : Array (Option (Entry × Float))} {pws pws' : Array Power} {e : ModulusCandidate}
    (h : e.IsComposite c primeSe pws) (hx : pws.Extends pws') : e.IsComposite c primeSe pws' := by
  refine ⟨h.nf_eq, h.fac_ne_nil, h.ssp_eq, h.one_lt, h.lt_maxPrimeEven, h.odd,
    fun code hc ↦ (h.isFactorCode code hc).extend hx, ?_⟩
  rw [← h.prod_eq]
  exact congr(List.prod $(List.map_congr_left fun code hc ↦ by
    rw [(h.isFactorCode code hc).factorOfCode_extend hx]))

/-- A candidate of the pool before the stages: a prime (`Ratpoints.ModulusCandidate.IsPrime`) or a
composite modulus (`Ratpoints.ModulusCandidate.IsComposite`). -/
def ModulusCandidate.IsPrimeOrComposite (c : List ℤ) (primeSe : Array (Option (Entry × Float)))
    (pws : Array Power) (e : ModulusCandidate) : Prop :=
  e.IsPrime c ∨ e.IsComposite c primeSe pws

theorem ModulusCandidate.IsPrimeOrComposite.extend {c : List ℤ}
    {primeSe : Array (Option (Entry × Float))} {pws pws' : Array Power} {e : ModulusCandidate}
    (h : e.IsPrimeOrComposite c primeSe pws) (hx : pws.Extends pws') :
    e.IsPrimeOrComposite c primeSe pws' :=
  h.imp id (·.extend hx)

/-- A candidate with the count of factors, the modulus, the sieve entry and the codes of a candidate
is a candidate: the predicate reads neither the density, the key, the cost nor the mask. -/
theorem ModulusCandidate.IsPrimeOrComposite.of_eq {c : List ℤ}
    {primeSe : Array (Option (Entry × Float))} {pws : Array Power} {e e' : ModulusCandidate}
    (h : e.IsPrimeOrComposite c primeSe pws) (hnf : e'.nf = e.nf) (hp : e'.p = e.p)
    (hs : e'.ssp = e.ssp) (hf : e'.fac = e.fac) : e'.IsPrimeOrComposite c primeSe pws := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  · exact .inl ⟨hnf ▸ h1, hp ▸ hs ▸ h2⟩
  · exact .inr ⟨hnf ▸ hf ▸ h1, hf ▸ h2, hs ▸ h3, hp ▸ h4, hp ▸ h5, hp ▸ h6, hf ▸ h7, hp ▸ hf ▸ h8⟩

/-- A candidate keyed for the first stage is a candidate. -/
theorem ModulusCandidate.IsPrimeOrComposite.phase1Key {c : List ℤ}
    {primeSe : Array (Option (Entry × Float))} {pws : Array Power} {e : ModulusCandidate}
    (h : e.IsPrimeOrComposite c primeSe pws) (ct U D cc : Float) :
    (Ratpoints.phase1Key ct U D cc e).IsPrimeOrComposite c primeSe pws :=
  h.of_eq rfl rfl rfl rfl

/-! ### The prime powers -/

/-- The prime powers examined so far by `Ratpoints.addModuli` for the curve with the coefficient
list `c`: each record that the table holds is that of a prime power of the table, and each index
that it holds for a prime power `p ^ e`, `p` at the position `pn`, is that of a record of the tables
of `Ratpoints.Sieve.examinePower` for it. -/
structure PowerTable.WF (c : List ℤ) (tab : PowerTable) : Prop where
  /-- Each record is that of a prime power of the table. -/
  isExamined : ∀ pw ∈ tab.pws, pw.IsExamined c
  /-- Each index is that of the record of its prime power. -/
  idx : ∀ pn e i, tab.idx.lookup (pn, e) = some (some i) →
    ∃ pw, tab.pws[i]? = some pw ∧
      ∃ u pinf, pw = Id.run (examinePower c (degree c) primeTable[pn]! e u pinf)

-- The tables of a prime power, as a value: the contracts read only that they are its tables.
private theorem examinePower_value (c : List ℤ) (d p e : ℕ) (u pinf : Bool) :
    ⦃ True ⦄ examinePower c d p e u pinf
    ⦃ fun r ↦ r = Id.run (examinePower c d p e u pinf) ⦄ :=
  ⟨fun _ ↦ rfl⟩

theorem PowerTable.WF.push {c : List ℤ} {tab : PowerTable} (h : tab.WF c) {pn e : ℕ}
    (hpn : pn < numPrimes) (he : 1 ≤ e) (u pinf : Bool) (b : Bool) :
    PowerTable.WF c
      { pws := if b then tab.pws.push (Id.run (examinePower c (degree c) primeTable[pn]! e u pinf))
          else tab.pws
        idx := ((pn, e), if b then some tab.pws.size else none) :: tab.idx } := by
  refine ⟨fun pw hpw ↦ ?_, fun pn' e' i hi ↦ ?_⟩
  · split at hpw
    · rcases Array.mem_push.mp hpw with hpw | rfl
      · exact h.isExamined pw hpw
      · exact ⟨pn, hpn, e, he, u, pinf, rfl⟩
    · exact h.isExamined pw hpw
  · simp only [List.lookup_cons] at hi
    split at hi
    · rename_i hk
      obtain ⟨rfl, rfl⟩ : pn' = pn ∧ e' = e := by simpa using hk
      split at hi
      · rename_i hb
        obtain rfl := Option.some.inj (Option.some.inj hi)
        exact ⟨_, by simp [hb], u, pinf, rfl⟩
      · cases hi
    · obtain ⟨pw, hpw, hex⟩ := h.idx pn' e' i hi
      exact ⟨pw, Array.extends_ite_push b _ _ _ _ hpw, hex⟩

-- The prime power found among those examined.
private theorem PowerTable.WF.lookup_post {c : List ℤ} {tab : PowerTable} (h : tab.WF c)
    {pn e : ℕ} {i? : Option ℕ} (hl : tab.idx.lookup (pn, e) = some i?) :
    PowerTable.WF c (i?, tab).2 ∧ tab.pws.Extends (i?, tab).2.pws ∧
      ∀ i, (i?, tab).1 = some i →
      ∃ pw, (i?, tab).2.pws[i]? = some pw ∧
        ∃ u pinf, pw = Id.run (examinePower c (degree c) primeTable[pn]! e u pinf) :=
  ⟨h, .refl _, fun i hi ↦ h.idx pn e i (hi ▸ hl)⟩

/-- The contract of `Ratpoints.powerIndex` for the prime power `p ^ e`, `e ≥ 1`, of the prime
`p = primeTable[pn]`, one of the first `Ratpoints.numPrimes`: the prime powers examined stay those
of the table (`Ratpoints.PowerTable.WF`), the records extended, and the index it returns is
that of a record of the tables of `Ratpoints.Sieve.examinePower` for `p ^ e`. -/
theorem powerIndex_spec (c : List ℤ) (u pinf : Bool) (pn p e : ℕ) (tab : PowerTable) :
    ⦃ PowerTable.WF c tab ∧ pn < numPrimes ∧ 1 ≤ e ∧ p = primeTable[pn]! ⦄
    powerIndex c (degree c) u pinf pn p e tab
    ⦃ fun r ↦ PowerTable.WF c r.2 ∧ tab.pws.Extends r.2.pws ∧ ∀ i, r.1 = some i →
        ∃ pw, r.2.pws[i]? = some pw ∧
          ∃ u pinf, pw = Id.run (examinePower c (degree c) primeTable[pn]! e u pinf) ⦄ := by
  vcgen [powerIndex, examinePower_value]
  all_goals obtain ⟨h, hpn, he, hp⟩ := ‹PowerTable.WF c tab ∧ _›
  · exact h.lookup_post ‹_›
  · rename_i pw hpw
    rw [hp] at hpw
    refine ⟨hpw ▸ h.push hpn he u pinf _, ?_, fun i hi ↦ ?_⟩
    · dsimp only
      split
      · exact Array.extends_push _ _
      · exact .refl _
    · dsimp only at hi ⊢
      split at hi
      · obtain rfl := Option.some.inj hi
        exact ⟨pw, by simp_all, u, pinf, hpw⟩
      · cases hi

/-- The code of a prime whose table the loop of the tables holds can be read. -/
theorem isFactorCode_of_getD_eq_some {c : List ℤ} {primeSe : Array (Option (Entry × Float))}
    (hse : IsExaminedPrimeSe c primeSe) (pws : Array Power) {k : ℕ} {t : Entry} {r : Float}
    (h : primeSe.getD k none = some (t, r)) : IsFactorCode c primeSe pws k := by
  obtain ⟨hk, rfl⟩ := hse k t r h
  exact ⟨fun _ ↦ ⟨r, h⟩, fun hk' ↦ absurd hk (Nat.not_lt.mpr hk')⟩

/-- The factor of the code of a prime whose table the loop of the tables holds has the prime as its
modulus. -/
theorem modulus_factorOfCode_of_getD_eq_some {c : List ℤ}
    {primeSe : Array (Option (Entry × Float))} (hse : IsExaminedPrimeSe c primeSe)
    (pws : Array Power) {k : ℕ} {t : Entry} {r : Float} (h : primeSe.getD k none = some (t, r)) :
    (factorOfCode primeSe pws k).modulus = primeTable[k]! := by
  obtain ⟨hk, rfl⟩ := hse k t r h
  simp [factorOfCode, hk, h, Factor.modulus]

/-- The code `numPrimes + i` of the record `i` of the tables of a prime power of the table can be
read. -/
theorem isFactorCode_add_of_getElem?_eq_some {c : List ℤ}
    (primeSe : Array (Option (Entry × Float))) {pws : Array Power} {i pn e : ℕ} {pw : Power}
    (hpn : pn < numPrimes) (he : 1 ≤ e) (h : pws[i]? = some pw) {u pinf : Bool}
    (hpw : pw = Id.run (examinePower c (degree c) primeTable[pn]! e u pinf)) :
    IsFactorCode c primeSe pws (numPrimes + i) :=
  ⟨fun h' ↦ absurd h' (by lia), fun _ ↦ ⟨pw, by simpa using h, pn, hpn, e, he, u, pinf, hpw⟩⟩

/-- The factor of the code `numPrimes + i` of the record `i` of the tables of a prime power `p ^ e`
of the table has the modulus `p ^ e`. -/
theorem modulus_factorOfCode_add_of_getElem?_eq_some {c : List ℤ}
    (primeSe : Array (Option (Entry × Float))) {pws : Array Power} {i pn e : ℕ} {pw : Power}
    (h : pws[i]? = some pw) {u pinf : Bool}
    (hpw : pw = Id.run (examinePower c (degree c) primeTable[pn]! e u pinf)) :
    (factorOfCode primeSe pws (numPrimes + i)).modulus = primeTable[pn]! ^ e := by
  simp only [factorOfCode, Nat.not_lt.mpr (Nat.le_add_right numPrimes i), ↓reduceIte,
    Nat.add_sub_cancel_left, Array.getElem!_of_getElem? h, Factor.modulus, hpw, m_run_examinePower]

/-- The contract of `Ratpoints.takeFactor` for the factor `p ^ e`, `e ≥ 1`, of the prime
`p = primeTable[st.pn]`, one of the first `Ratpoints.numPrimes`: the prime powers examined stay
those of the table, the records extended, the cofactor kept and the position not lowered,
and while the candidate is possible the code of the factor is appended, one that
`Ratpoints.makeModulus` can read (`Ratpoints.IsFactorCode`), with the modulus `p ^ e`. -/
theorem takeFactor_spec (c : List ℤ) (u : Bool) (primeSe : Array (Option (Entry × Float)))
    (pinf : Array Bool) (p e : ℕ) (st : FacState) :
    ⦃ IsExaminedPrimeSe c primeSe ∧ st.tab.WF c ∧ st.pn < numPrimes ∧ 1 ≤ e ∧
        p = primeTable[st.pn]! ⦄
    takeFactor c (degree c) u primeSe pinf p e st
    ⦃ fun st' ↦ st'.tab.WF c ∧ st.tab.pws.Extends st'.tab.pws ∧ st'.rest = st.rest ∧
        (st'.ok = true → st'.pn = st.pn + 1 ∧ ∃ code, st'.fac = st.fac.push code ∧
          IsFactorCode c primeSe st'.tab.pws code ∧
          (factorOfCode primeSe st'.tab.pws code).modulus = p ^ e) ∧ st.pn ≤ st'.pn ⦄ := by
  vcgen [takeFactor, powerIndex_spec]
  all_goals obtain ⟨hse, hok, hpn, he, hp⟩ := ‹IsExaminedPrimeSe c primeSe ∧ _›
  · exact ⟨hok, .refl _, fun h ↦ absurd h Bool.false_ne_true, Nat.le_refl _⟩
  · exact ⟨hok, .refl _, fun h ↦ absurd h Bool.false_ne_true, Nat.le_refl _⟩
  · exact ⟨hok, .refl _, fun _ ↦ ⟨rfl, st.pn, rfl,
      isFactorCode_of_getD_eq_some hse st.tab.pws ‹_›, by
        rw [modulus_factorOfCode_of_getD_eq_some hse st.tab.pws ‹_›, hp, ‹e = 1›, Nat.pow_one]⟩,
      Nat.le_succ _⟩
  · exact ⟨hok, hpn, he, hp⟩
  · obtain ⟨hok', hl, -⟩ := ‹PowerTable.WF c _ ∧ _›
    exact ⟨hok', hl, fun h ↦ absurd h Bool.false_ne_true, Nat.le_refl _⟩
  · obtain ⟨hok', hl, hi⟩ := ‹PowerTable.WF c _ ∧ _›
    obtain ⟨pw, hpw, u', pinf', hpw'⟩ := hi _ ‹_›
    exact ⟨hok', hl, fun _ ↦ ⟨rfl, _, rfl,
      isFactorCode_add_of_getElem?_eq_some primeSe hpn he hpw hpw',
      by rw [modulus_factorOfCode_add_of_getElem?_eq_some primeSe hpw hpw', hp]⟩, Nat.le_succ _⟩

/-- The state `st` of the factorization of the candidate `m` (`Ratpoints.FacState`) for the curve
with the coefficient list `c` and the tables of the loop of the tables `primeSe`: the prime powers
examined are those of the table (`Ratpoints.PowerTable.WF`), and while the candidate is possible the
cofactor is positive and times the moduli of the factors taken, whose codes
`Ratpoints.makeModulus` can read, makes `m`. -/
structure FacState.WF (c : List ℤ) (primeSe : Array (Option (Entry × Float))) (m : ℕ)
    (st : FacState) : Prop where
  /-- The prime powers examined are those of the table. -/
  tab : st.tab.WF c
  /-- The cofactor is positive. -/
  rest_pos : st.ok = true → 0 < st.rest
  /-- The codes of the factors can be read. -/
  isFactorCode : st.ok = true → ∀ code ∈ st.fac, IsFactorCode c primeSe st.tab.pws code
  /-- The cofactor times the moduli of the factors makes `m`. -/
  mul_prod : st.ok = true →
    st.rest * (st.fac.toList.map fun code ↦ (factorOfCode primeSe st.tab.pws code).modulus).prod = m

/-- A state of the factorization with the cofactor, the flag, the codes and the table of the prime
powers of one of `m` is one of `m`: the predicate reads neither the position of the next prime, the
product of the densities nor the mask. -/
theorem FacState.WF.of_eq {c : List ℤ} {primeSe : Array (Option (Entry × Float))} {m : ℕ}
    {b st : FacState} (h : b.WF c primeSe m) (hr : st.rest = b.rest) (hok : st.ok = b.ok)
    (hf : st.fac = b.fac) (ht : st.tab = b.tab) : st.WF c primeSe m := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨ht ▸ h1, hok ▸ hr ▸ h2, hok ▸ hf ▸ ht ▸ h3, hok ▸ hr ▸ hf ▸ ht ▸ h4⟩

/-- A state of the factorization whose candidate is refused is one of every `m`. -/
theorem FacState.WF.of_ok_eq_false {c : List ℤ} {primeSe : Array (Option (Entry × Float))}
    {m : ℕ} {st : FacState} (ht : st.tab.WF c) (hok : st.ok = false) : st.WF c primeSe m :=
  ⟨ht, nofun ∘ hok.symm.trans, nofun ∘ hok.symm.trans, nofun ∘ hok.symm.trans⟩

/-- The state of the factorization after the factor `p ^ e` of the cofactor `b.rest = rest p ^ e`
is taken (`Ratpoints.takeFactor`), from one of `m` whose candidate is still possible: one of `m`. -/
theorem FacState.WF.of_takeFactor {c : List ℤ} {primeSe : Array (Option (Entry × Float))}
    {m : ℕ} {b st : FacState} (hb : b.WF c primeSe m) (hok : b.ok = true) {rest q : ℕ}
    (hrest : 0 < rest) (hR : rest * q = b.rest) (ht : st.tab.WF c)
    (hx : b.tab.pws.Extends st.tab.pws) (hr : st.rest = rest)
    (hs : st.ok = true → ∃ code, st.fac = b.fac.push code ∧ IsFactorCode c primeSe st.tab.pws code ∧
      (factorOfCode primeSe st.tab.pws code).modulus = q) :
    st.WF c primeSe m := by
  refine ⟨ht, fun h ↦ hr ▸ hrest, fun h ↦ ?_, fun h ↦ ?_⟩ <;> obtain ⟨code, hf, hc, hm⟩ := hs h
  · rw [hf]
    exact Array.forall_mem_push.mpr ⟨hc, fun x hx' ↦ (hb.isFactorCode hok x hx').extend hx⟩
  · rw [hr, hf, Array.toList_push, List.map_append, List.prod_append, List.map_singleton,
      List.prod_singleton, hm, ← hb.mul_prod hok, ← hR,
      List.map_congr_left fun x hx' ↦ by
        rw [(hb.isFactorCode hok x (Array.mem_toList_iff.mp hx')).factorOfCode_extend hx]]
    ac_rfl

local grind_pattern FacState.WF.of_takeFactor => FacState.WF c primeSe m b, st.tab.WF c, rest * q

local grind_pattern Nat.div_lt_and_pos_and_div_mul_pow_succ => a / p, a * p ^ e

/-- The invariant of the loop of `Ratpoints.factorCandidate` over the primes, whose state is the
value of a return and the state of the factorization, from the state `st₀`: both are states of the
factorization of `m` (`Ratpoints.FacState.WF`) with the records of the prime powers of `st₀`
extended. -/
def FactorLoopInvariant (c : List ℤ) (primeSe : Array (Option (Entry × Float))) (m : ℕ)
    (st₀ : FacState) : Std.WP.WhileInvariant (Option FacState × FacState) Prop :=
  .mk fun _ s ↦ (∀ r, s.1 = some r → r.WF c primeSe m ∧ st₀.tab.pws.Extends r.tab.pws) ∧
    s.2.WF c primeSe m ∧ st₀.tab.pws.Extends s.2.tab.pws

/-- The invariant of the loop of `Ratpoints.factorCandidate` that divides the prime `p` off the
cofactor `R`, on the cofactor left and the exponent: the cofactor left is positive and times
`p ^ e` makes `R`, it is `R` before the first division, and `p` does not divide it at the end. -/
def DivideInvariant (R p : ℕ) : Std.WP.WhileInvariant (ℕ × ℕ) Prop :=
  .mk fun exit s ↦ 0 < s.1 ∧ s.1 * p ^ s.2 = R ∧ (s.2 = 0 → s.1 = R) ∧ (exit = true → s.1 % p ≠ 0)

attribute [local irreducible] primeTable in
/-- The contract of `Ratpoints.factorCandidate` over the first `pnLim ≤ numPrimes` primes: the
state of the factorization of `m` stays one (`Ratpoints.FacState.WF`), with the records of the prime
powers extended. The loop ends, since the position of the next prime rises or the candidate is
refused, and the inner loops, since the position rises and the cofactor drops. -/
theorem factorCandidate_spec (c : List ℤ) (u : Bool) (primeSe : Array (Option (Entry × Float)))
    (pinf : Array Bool) (pnLim m : ℕ) (st : FacState) :
    ⦃ IsExaminedPrimeSe c primeSe ∧ pnLim ≤ numPrimes ∧ st.WF c primeSe m ⦄
    factorCandidate c (degree c) u primeSe pinf pnLim st
    ⦃ fun st' ↦ st'.WF c primeSe m ∧ st.tab.pws.Extends st'.tab.pws ⦄ := by
  vcgen [factorCandidate, takeFactor_spec] invariants
  | inv1 => FactorLoopInvariant c primeSe m st
  | inv2 => .ofMeasure fun s : Option FacState × FacState ↦
      2 * (pnLim - s.2.pn) + if s.2.ok then 1 else 0
  | inv3 b _ _ _ _ => .mk fun _ pn ↦ b.pn ≤ pn
  | inv4 => .ofMeasure fun pn ↦ pnLim - pn
  | inv5 b _ _ _ _ _ _ _ _ => DivideInvariant b.rest b.rest
  | inv6 => .ofMeasure fun s : ℕ × ℕ ↦ s.1
  | inv7 b _ _ _ _ _ => DivideInvariant b.rest primeTable[b.pn]!
  | inv8 => .ofMeasure fun s : ℕ × ℕ ↦ s.1
  all_goals simp only [Std.WP.Variant.evalsTo_ofMeasure, Std.WP.Variant.evalsBelow_ofMeasure_nat,
    Std.WP.Assertion.NondetFun.evalsTo_pure, Lean.Order.meet_prop_eq_and,
    Lean.Order.ofProp_prop_eq, Std.WP.WhileInvariant.mk, FactorLoopInvariant, DivideInvariant,
    reduceCtorEq, false_implies, implies_true, true_and, and_true, Option.some.injEq,
    forall_eq'] at *
  all_goals grind [FacState.WF.of_eq, FacState.WF.of_ok_eq_false, Array.Extends.trans,
    Array.Extends.refl, FacState.WF.tab, one_lt_getElem!_primeTable]

/-- The candidate of a composite modulus `1 < m < maxPrimeEven`, odd, from a state of its
factorization that ends with the candidate possible and the cofactor `1`: the codes of its factors,
whose moduli multiply to `m`. -/
theorem FacState.WF.isComposite {c : List ℤ} {primeSe : Array (Option (Entry × Float))} {m : ℕ}
    {st : FacState} (h : st.WF c primeSe m) (hok : st.ok = true) (hr : ¬1 < st.rest)
    (hm : 1 < m ∧ m < maxPrimeEven ∧ m % 2 = 1) {e : ModulusCandidate}
    (hnf : e.nf = st.fac.size) (hf : e.fac = st.fac.toList) (hs : e.ssp = none) (hp : e.p = m) :
    e.IsComposite c primeSe st.tab.pws := by
  have hprod := h.mul_prod hok
  rw [show st.rest = 1 by lia [h.rest_pos hok], Nat.one_mul] at hprod
  refine ⟨by rw [hnf, hf, Array.length_toList], fun h0 ↦ ?_, hs, hp ▸ hm.1, hp ▸ hm.2.1,
    hp ▸ hm.2.2, fun code hc ↦ h.isFactorCode hok code (Array.mem_toList_iff.mp (hf ▸ hc)),
    by rw [hf, hprod, hp]⟩
  rw [hf] at h0
  rw [h0, List.map_nil, List.prod_nil] at hprod
  lia

-- The state of the factorization of `m` at its start.
private theorem FacState.wf_init {c : List ℤ} {primeSe : Array (Option (Entry × Float))}
    {m : ℕ} (hm : 0 < m) {tab : PowerTable} (ht : tab.WF c) :
    FacState.WF c primeSe m { rest := m, tab } :=
  ⟨ht, fun _ ↦ hm, fun _ _ h ↦ absurd h (by simp), fun _ ↦ by simp⟩

/-- The contract of `Ratpoints.offerModulus` for an odd `1 < m < maxPrimeEven`: the prime powers
examined stay those of the table, the records extended, and the candidate it offers is a composite
modulus whose codes `Ratpoints.makeModulus` can read and whose factors multiply to `m`
(`Ratpoints.ModulusCandidate.IsComposite`). -/
theorem offerModulus_spec (c : List ℤ) (u : Bool) (primeSe : Array (Option (Entry × Float)))
    (pinf : Array Bool) (pnLim : ℕ) (ct U D : Float) (m : ℕ) (tab : PowerTable) :
    ⦃ IsExaminedPrimeSe c primeSe ∧ pnLim ≤ numPrimes ∧ tab.WF c ∧ 1 < m ∧ m < maxPrimeEven ∧
        m % 2 = 1 ⦄
    offerModulus c (degree c) u primeSe pinf pnLim ct U D m tab
    ⦃ fun r ↦ r.2.WF c ∧ tab.pws.Extends r.2.pws ∧
        ∀ e, r.1 = some e → e.IsComposite c primeSe r.2.pws ⦄ := by
  vcgen [offerModulus, factorCandidate_spec c u primeSe pinf pnLim m]
  all_goals obtain ⟨hse, hL, ht, hm⟩ := ‹IsExaminedPrimeSe c primeSe ∧ _›
  · exact ⟨ht, .refl _, nofun⟩
  · exact ⟨hse, hL, FacState.wf_init (by lia) ht⟩
  all_goals obtain ⟨h, hx⟩ := ‹FacState.WF c primeSe m _ ∧ _›
  iterate 3 exact ⟨h.tab, hx, nofun⟩
  refine ⟨h.tab, hx, fun e he ↦ ?_⟩
  cases he
  exact h.isComposite (by simp_all) (by simp_all) hm rfl rfl rfl rfl

theorem PowerTable.wf_empty (c : List ℤ) : PowerTable.WF c {} :=
  ⟨fun _ h ↦ absurd h (by simp), fun _ _ _ h ↦ absurd h (by simp)⟩

/-- The invariant of the loop of `Ratpoints.addModuli` over the candidates `m`: the candidates of
the pool (`Ratpoints.ModulusCandidate.IsPrimeOrComposite`) for the records of the prime powers
examined so far, which are those of the table, and `m` odd from 9 on. -/
def AddModuliInvariant (c : List ℤ) (primeSe : Array (Option (Entry × Float))) :
    Std.WP.WhileInvariant (Array ModulusCandidate × PowerTable × ℕ) Prop :=
  .mk fun _ s ↦ (∀ e ∈ s.1, e.IsPrimeOrComposite c primeSe s.2.1.pws) ∧ s.2.1.WF c ∧
    s.2.2 % 2 = 1 ∧ 9 ≤ s.2.2

/-- The contract of `Ratpoints.addModuli`, for any values of the doubles: from a pool of candidates
of the primes, it returns a pool of candidates of primes and composite moduli
(`Ratpoints.ModulusCandidate.IsPrimeOrComposite`) for the records of the prime powers that it
returns. -/
theorem addModuli_spec (c : List ℤ) (u : Bool) (pool : Array ModulusCandidate)
    (primeSe : Array (Option (Entry × Float))) (pinf : Array Bool) (pnLim : ℕ) (ct cc U D : Float) :
    ⦃ IsExaminedPrimeSe c primeSe ∧ pnLim ≤ numPrimes ∧
        ∀ e ∈ pool, e.IsPrimeOrComposite c primeSe #[] ⦄
    addModuli c (degree c) u pool primeSe pinf pnLim ct cc U D
    ⦃ fun r ↦ ∀ e ∈ r.1, e.IsPrimeOrComposite c primeSe r.2 ⦄ := by
  vcgen [addModuli, offerModulus_spec] invariants
  | inv1 => AddModuliInvariant c primeSe
  | inv2 => .ofMeasure fun s : Array ModulusCandidate × PowerTable × ℕ ↦ maxPrimeEven - s.2.2
  all_goals simp only [Std.WP.Variant.evalsTo_ofMeasure, Std.WP.Variant.evalsBelow_ofMeasure_nat,
    Std.WP.Assertion.NondetFun.evalsTo_pure, Lean.Order.meet_prop_eq_and,
    Lean.Order.ofProp_prop_eq, Std.WP.WhileInvariant.mk, AddModuliInvariant] at *
  all_goals grind [ModulusCandidate.IsPrimeOrComposite.extend,
    ModulusCandidate.IsPrimeOrComposite.phase1Key, PowerTable.wf_empty,
    ModulusCandidate.IsPrimeOrComposite]

/-! ### The sieve entries -/

/-- A sieve entry that the choice of the moduli makes for the curve with the coefficient list `c`,
at the position `n` of the entries: an entry of its modulus (`Ratpoints.IsModulusEntry`), with the
reference and the kind of builder of its position (`Ratpoints.Sieve.SieveEntry.refInit`), and a
prime entry of the table (`Ratpoints.Sieve.SieveEntry.IsPrimeEntry`) when it counts no factors. -/
structure IsChoiceEntry (c : List ℤ) (n : ℕ) (se : SieveEntry) : Prop where
  /-- An entry of its modulus. -/
  isModulusEntry : IsModulusEntry c se.p se
  /-- The reference and the kind of builder of its position. -/
  refInit : (se.ref, se.init) = SieveEntry.refInit n se.factors
  /-- A prime entry when it counts no factors. -/
  isPrimeEntry : se.nf = 0 → se.IsPrimeEntry

attribute [local irreducible] primeTable in
/-- The sieve entry of a prime of the table (`Ratpoints.primeEntry`), one of the first
`Ratpoints.numPrimes`, with its table, is one that the choice makes, at every position. -/
theorem isChoiceEntry_primeEntry (c : List ℤ) {pn : ℕ} (hpn : pn < numPrimes) (r : Float) (n : ℕ) :
    IsChoiceEntry c n (primeEntry (examinePrime c (degree c) primeTable[pn]!) r) := by
  have hp := prime_getElem!_primeTable (hpn.trans_le numPrimes_le_size_primeTable)
  have hm : 1 < primeTable[pn]! ∧ primeTable[pn]! < maxPrimeEven ∧ primeTable[pn]! % 2 = 1 :=
    ⟨hp.one_lt, getElem!_primeTable_lt_maxPrimeEven hpn,
      getElem!_primeTable_mod_two_eq_one (hpn.trans_le numPrimes_le_size_primeTable)⟩
  have hs := isSound_prime_examinePrime (c := c) hpn (dvd_refl primeTable[pn]!)
  exact ⟨isModulusEntry_of_forall_isSound hm (by simpa using hs) (by simp [Factor.modulus])
      (inverses_mulMod_rbaLength_of_isSound hm hs rfl) _ _ _ _, rfl,
    fun _ ↦ isPrimeEntry_examinePrime c _ hp (hm.2.1.le.trans maxPrimeEven_le_two_pow_32) rfl rfl
      rfl⟩

/-- The factors of a composite candidate whose codes can be read are sound for its modulus. -/
theorem ModulusCandidate.IsComposite.isSound {c : List ℤ} {primeSe : Array (Option (Entry × Float))}
    {pws : Array Power} {e : ModulusCandidate} (h : e.IsComposite c primeSe pws) :
    ∀ f ∈ e.fac.map (factorOfCode primeSe pws), f.IsSound c e.p := by
  intro f hf
  obtain ⟨code, hc, rfl⟩ := List.mem_map.mp hf
  refine (h.isFactorCode code hc).isSound (by lia [h.one_lt]) h.lt_maxPrimeEven ?_
  rw [← h.prod_eq]
  exact List.dvd_prod (List.mem_map_of_mem hc)

/-- The contract of `Ratpoints.makeModulus`: the sieve entry of a composite candidate whose codes
can be read is one that the choice makes at the position `n` (`Ratpoints.IsChoiceEntry`). -/
theorem makeModulus_spec (c : List ℤ) (e : ModulusCandidate) (n : ℕ)
    (primeSe : Array (Option (Entry × Float))) (pws : Array Power) :
    ⦃ e.IsComposite c primeSe pws ⦄ makeModulus e n primeSe pws
    ⦃ fun se ↦ IsChoiceEntry c n se ⦄ := by
  vcgen [makeModulus]
  all_goals have h := ‹e.IsComposite c primeSe pws›
  · exact one_lt_and_coprime_rbaLength_mod h.one_lt h.odd
  · refine ⟨isModulusEntry_of_forall_isSound ⟨h.one_lt, h.lt_maxPrimeEven, h.odd⟩ h.isSound
      (by rw [List.map_map]; exact h.prod_eq) (mul_rbaLength_mod_and_lt ‹_›) _ _ _ _, rfl,
      fun h0 ↦ absurd (h.nf_eq.symm.trans h0) ?_⟩
    simpa using h.fac_ne_nil

/-- The candidates of the pool `pool` after the stages, whose second ends at `sp2`: those of the
first two stages each with its sieve entry, made for its position (`Ratpoints.IsChoiceEntry`), and
those from `sp2` on primes (`Ratpoints.ModulusCandidate.IsPrime`). -/
structure ChoicePoolWF (c : List ℤ) (sp2 : ℕ) (pool : Array ModulusCandidate) : Prop where
  /-- The candidates of the first two stages have their sieve entries. -/
  exists_isChoiceEntry_of_lt : ∀ n (h : n < pool.size), n < sp2 →
    ∃ se, pool[n].ssp = some se ∧ IsChoiceEntry c n se
  /-- The candidates from `sp2` on are primes. -/
  isPrime : ∀ n (h : n < pool.size), sp2 ≤ n → pool[n].IsPrime c

/-- The invariant of the loop of `Ratpoints.stageEntries` after the positions below `k`, from the
pool `pool₀`: the size kept, the candidates below `k` with their sieve entries made for their
positions, and the others as they were. -/
def StageEntriesInvariant (c : List ℤ) (pool₀ : Array ModulusCandidate) (k : ℕ)
    (pool : Array ModulusCandidate) : Prop :=
  pool.size = pool₀.size ∧
    (∀ n (h : n < pool.size), n < k → ∃ se, pool[n].ssp = some se ∧ IsChoiceEntry c n se) ∧
    ∀ n (h : n < pool.size), k ≤ n → pool[n]! = pool₀[n]!

theorem ModulusCandidate.IsPrimeOrComposite.isPrime_of_ssp_isSome {c : List ℤ}
    {primeSe : Array (Option (Entry × Float))} {pws : Array Power} {e : ModulusCandidate}
    (h : e.IsPrimeOrComposite c primeSe pws) (hs : ¬e.ssp.isNone = true) : e.IsPrime c :=
  h.resolve_right fun hc ↦ hs (by simp [hc.ssp_eq])

theorem ModulusCandidate.IsPrimeOrComposite.isComposite_of_ssp_isNone {c : List ℤ}
    {primeSe : Array (Option (Entry × Float))} {pws : Array Power} {e : ModulusCandidate}
    (h : e.IsPrimeOrComposite c primeSe pws) (hs : e.ssp.isNone = true) :
    e.IsComposite c primeSe pws :=
  h.resolve_left fun hp ↦ by
    obtain ⟨_, _, _, _, h2⟩ := hp.exists_eq
    simp [h2] at hs

/-- A prime candidate has the sieve entry of its prime, which the choice makes, at every
position. -/
theorem ModulusCandidate.IsPrime.exists_isChoiceEntry {c : List ℤ} {e : ModulusCandidate}
    (h : e.IsPrime c) (n : ℕ) : ∃ se, e.ssp = some se ∧ IsChoiceEntry c n se :=
  have ⟨_, hpn, r, _, hs⟩ := h.exists_eq
  ⟨_, hs, isChoiceEntry_primeEntry c hpn r n⟩

theorem stageEntriesInvariant_zero (c : List ℤ) (pool : Array ModulusCandidate) :
    StageEntriesInvariant c pool ([] : List ℕ).length pool :=
  ⟨rfl, fun _ _ h ↦ absurd h (Nat.not_lt_zero _), fun _ _ _ ↦ rfl⟩

-- The candidate at the cursor of the loop of `Ratpoints.stageEntries`, as it was.
private theorem StageEntriesInvariant.lt_size_and_isPrimeOrComposite {c : List ℤ}
    {primeSe : Array (Option (Entry × Float))}
    {pws : Array Power} {pool p : Array ModulusCandidate} {sp2 : ℕ}
    (hpre : (∀ e ∈ pool, e.IsPrimeOrComposite c primeSe pws) ∧ NfEqZeroFrom pool sp2 ∧
      sp2 ≤ pool.size)
    {pref suff : List ℕ} {cur : ℕ} (hl : ForIn.toList [:sp2] = pref ++ cur :: suff)
    (h : StageEntriesInvariant c pool pref.length p) :
    cur < p.size ∧ p[cur]!.IsPrimeOrComposite c primeSe pws := by
  have hc := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  have hcp : cur < p.size := by lia [h.1, hpre.2.2]
  refine ⟨hcp, ?_⟩
  rw [h.2.2 cur hcp (Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl).le,
    getElem!_pos pool cur (by lia [hpre.2.2])]
  exact hpre.1 _ (Array.getElem_mem _)

theorem StageEntriesInvariant.isComposite {c : List ℤ} {primeSe : Array (Option (Entry × Float))}
    {pws : Array Power} {pool p : Array ModulusCandidate} {sp2 : ℕ}
    (hpre : (∀ e ∈ pool, e.IsPrimeOrComposite c primeSe pws) ∧ NfEqZeroFrom pool sp2 ∧
      sp2 ≤ pool.size)
    {pref suff : List ℕ} {cur : ℕ} (hl : ForIn.toList [:sp2] = pref ++ cur :: suff)
    (h : StageEntriesInvariant c pool pref.length p) (hn : p[cur]!.ssp.isNone = true) :
    p[cur]!.IsComposite c primeSe pws :=
  (h.lt_size_and_isPrimeOrComposite hpre hl).2.isComposite_of_ssp_isNone hn

theorem StageEntriesInvariant.set {c : List ℤ} {primeSe : Array (Option (Entry × Float))}
    {pws : Array Power} {pool p : Array ModulusCandidate} {sp2 : ℕ}
    (hpre : (∀ e ∈ pool, e.IsPrimeOrComposite c primeSe pws) ∧ NfEqZeroFrom pool sp2 ∧
      sp2 ≤ pool.size)
    {pref suff : List ℕ} {cur : ℕ} (hl : ForIn.toList [:sp2] = pref ++ cur :: suff)
    (h : StageEntriesInvariant c pool pref.length p) {se : SieveEntry}
    (hse : IsChoiceEntry c cur se) :
    StageEntriesInvariant c pool (pref ++ [cur]).length
      (p.set! cur { p[cur]! with ssp := some se }) := by
  have hcp := (h.lt_size_and_isPrimeOrComposite hpre hl).1
  have hlen := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  rw [List.length_append, List.length_singleton, hlen]
  simp only [Array.set!_eq_setIfInBounds]
  refine ⟨by simp [h.1], fun n hn hk ↦ ?_, fun n hn hk ↦ ?_⟩ <;>
    rw [Array.size_setIfInBounds] at hn
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [Array.getElem_setIfInBounds_ne hn (Nat.ne_of_gt hk)]
      exact h.2.1 n hn (by lia)
    · exact ⟨se, by simp, hse⟩
  · rw [getElem!_pos _ n (by simpa using hn), Array.getElem_setIfInBounds_ne hn (Nat.ne_of_lt hk),
      ← getElem!_pos p n hn]
    exact h.2.2 n hn (by lia)

theorem StageEntriesInvariant.skip {c : List ℤ} {primeSe : Array (Option (Entry × Float))}
    {pws : Array Power} {pool p : Array ModulusCandidate} {sp2 : ℕ}
    (hpre : (∀ e ∈ pool, e.IsPrimeOrComposite c primeSe pws) ∧ NfEqZeroFrom pool sp2 ∧
      sp2 ≤ pool.size)
    {pref suff : List ℕ} {cur : ℕ} (hl : ForIn.toList [:sp2] = pref ++ cur :: suff)
    (h : StageEntriesInvariant c pool pref.length p) (hn : ¬p[cur]!.ssp.isNone = true) :
    StageEntriesInvariant c pool (pref ++ [cur]).length p := by
  obtain ⟨hcp, hok⟩ := h.lt_size_and_isPrimeOrComposite hpre hl
  have hlen := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  rw [List.length_append, List.length_singleton, hlen]
  refine ⟨h.1, fun n hn' hk ↦ ?_, fun n hn' hk ↦ h.2.2 n hn' (by lia)⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
  · exact h.2.1 n hn' (by lia)
  · rw [← getElem!_pos p n hn']
    exact (hok.isPrime_of_ssp_isSome hn).exists_isChoiceEntry n

theorem StageEntriesInvariant.post {c : List ℤ} {primeSe : Array (Option (Entry × Float))}
    {pws : Array Power} {pool p : Array ModulusCandidate} {sp2 : ℕ}
    (hpre : (∀ e ∈ pool, e.IsPrimeOrComposite c primeSe pws) ∧ NfEqZeroFrom pool sp2 ∧
      sp2 ≤ pool.size)
    (h : StageEntriesInvariant c pool (ForIn.toList [:sp2]).length p) :
    ChoicePoolWF c sp2 p ∧ p.size = pool.size := by
  rw [Std.Legacy.Range.length_toList, Nat.sub_zero] at h
  refine ⟨⟨h.2.1, fun n hn hk ↦ ?_⟩, h.1⟩
  have hn' : n < pool.size := h.1 ▸ hn
  rw [← getElem!_pos p n hn, h.2.2 n hn hk, getElem!_pos pool n hn']
  refine (hpre.1 _ (Array.getElem_mem hn')).resolve_right fun hc ↦ ?_
  have := hc.nf_eq.symm.trans (hpre.2.1 n hn' hk)
  simp [hc.fac_ne_nil] at this

attribute [local irreducible] StageEntriesInvariant in
/-- The contract of `Ratpoints.stageEntries`: after the stages, which leave composite moduli only
before `sp2`, every candidate before `sp2` has its sieve entry, made for its position, and those
from `sp2` on are primes (`Ratpoints.ChoicePoolWF`). -/
theorem stageEntries_spec (c : List ℤ) (pool : Array ModulusCandidate) (sp2 : ℕ)
    (primeSe : Array (Option (Entry × Float))) (pws : Array Power) :
    ⦃ (∀ e ∈ pool, e.IsPrimeOrComposite c primeSe pws) ∧ NfEqZeroFrom pool sp2 ∧
        sp2 ≤ pool.size ⦄
    stageEntries pool sp2 primeSe pws
    ⦃ fun r ↦ ChoicePoolWF c sp2 r ∧ r.size = pool.size ⦄ := by
  vcgen [stageEntries, makeModulus_spec c] invariants
  | inv1 => fun pref _ p ↦ StageEntriesInvariant c pool pref.length p
  all_goals first
    | exact stageEntriesInvariant_zero c pool
    | exact StageEntriesInvariant.post ‹_› ‹_›
    | exact StageEntriesInvariant.isComposite ‹_› ‹_› ‹_› ‹_›
    | exact StageEntriesInvariant.set ‹_› ‹_› ‹_› ‹_›
    | exact StageEntriesInvariant.skip ‹_› ‹_› ‹_› ‹_›

theorem ChoicePoolWF.push {c : List ℤ} {sp2 : ℕ} {pool : Array ModulusCandidate}
    (h : ChoicePoolWF c sp2 pool) (hs : sp2 ≤ pool.size) {e : ModulusCandidate} (he : e.IsPrime c) :
    ChoicePoolWF c sp2 (pool.push e) := by
  refine ⟨fun n hn hk ↦ ?_, fun n hn hk ↦ ?_⟩ <;> rw [Array.getElem_push] <;> split
  · exact h.exists_isChoiceEntry_of_lt n _ hk
  · lia
  · exact h.isPrime n _ hk
  · exact he

theorem ChoicePoolWF.swapIfInBounds {c : List ℤ} {sp2 : ℕ} {pool : Array ModulusCandidate}
    (h : ChoicePoolWF c sp2 pool) {i j : ℕ} (hi : sp2 ≤ i) (hj : sp2 ≤ j) :
    ChoicePoolWF c sp2 (pool.swapIfInBounds i j) := by
  refine ⟨fun n hn hk ↦ ?_, fun n hn hk ↦ ?_⟩ <;> rw [Array.getElem_swapIfInBounds] <;>
    repeat' split
  all_goals first | lia | exact h.exists_isChoiceEntry_of_lt n _ hk | exact h.isPrime _ _ (by lia)

-- The examination of a prime, as a value: the contracts read it through its own lemmas.
private theorem examinePrime?_value (c : List ℤ) (d p : ℕ) (u : Bool) :
    ⦃ True ⦄ examinePrime? c d p u ⦃ fun r ↦ r = Id.run (examinePrime? c d p u) ⦄ :=
  ⟨fun _ ↦ rfl⟩

/-- The candidate of a prime of the table, one of the first `Ratpoints.numPrimes`, from its
examination, which says something, is a prime candidate, whatever its key and cost. -/
theorem isPrime_ofPrime {c : List ℤ} {pn : ℕ} (hpn : pn < numPrimes) {u : Bool} {t : Entry}
    {cm : Array ℕ} {code : ℕ} {r : Float}
    (h : Id.run (examinePrime? c (degree c) primeTable[pn]! u) = some (t, cm, code, r))
    (key cost : Float) :
    ({ ModulusCandidate.ofPrime pn t r code with key, cost } : ModulusCandidate).IsPrime c := by
  obtain rfl := eq_examinePrime_of_lt_numPrimes_of_run_examinePrime?_eq_some hpn h
  exact ⟨by simp only [ModulusCandidate.ofPrime]; split <;> lia, pn, hpn, r, rfl, rfl⟩

/-- The contract of `Ratpoints.lookFurther` for a position below `Ratpoints.numPrimes`: at none the
curve has no points; otherwise one more prime is looked at, and the pool gains at most the candidate
of a prime. -/
theorem lookFurther_spec (c : List ℤ) (u : Bool) (st : ThirdState) :
    ⦃ st.pnLim < numPrimes ⦄ lookFurther c (degree c) u st
    ⦃ fun r ↦ (r = none → ∀ H q, ¬IsPoint c H q) ∧ ∀ st', r = some st' →
        st'.pnLim = st.pnLim + 1 ∧ st'.sp3 = st.sp3 ∧
          (st'.pool = st.pool ∨ ∃ e, e.IsPrime c ∧ st'.pool = st.pool.push e) ⦄ := by
  vcgen [lookFurther, examinePrime?_value]
  all_goals try subst ‹_ = none›
  all_goals try subst ‹_ = some _›
  · exact ⟨fun _ ↦ not_isPoint_of_lt_numPrimes_of_run_examinePrime?_eq_none ‹_›
      (‹none = _› : none = Id.run _).symm, nofun⟩
  · exact ⟨nofun, fun _ h ↦ by cases h; exact ⟨rfl, rfl, .inl rfl⟩⟩
  · exact ⟨nofun, fun _ h ↦ by
      cases h
      exact ⟨rfl, rfl, .inr ⟨_, isPrime_ofPrime ‹_› (‹some _ = _› : some _ = Id.run _).symm _ _,
        rfl⟩⟩⟩

-- The mean density of the pool, as a value: no contract reads it.
private theorem rTyp_true (pool : Array ModulusCandidate) : ⦃ True ⦄ rTyp pool ⦃ fun _ ↦ True ⦄ :=
  ⟨fun _ ↦ trivial⟩

/-- The state of the third stage (`Ratpoints.ThirdState`) after the first two stages, which end at
`sp2`: the pool after the stages (`Ratpoints.ChoicePoolWF`), the end of the third stage between
`sp2` and the size of the pool. -/
def ThirdState.WF (c : List ℤ) (sp2 : ℕ) (st : ThirdState) : Prop :=
  ChoicePoolWF c sp2 st.pool ∧ sp2 ≤ st.sp3 ∧ st.sp3 ≤ st.pool.size

/-- The invariant of the loop of `Ratpoints.thirdStage`, whose state is the value of a return and
the state of the stage: the value of a return is an exit, at which the curve has no points; the
state of the stage, from the end `sp2` of the first two (`Ratpoints.ThirdState.WF`). -/
def ThirdStageInvariant (c : List ℤ) (sp2 : ℕ) :
    Std.WP.WhileInvariant (Option (Except ℕ ThirdState) × ThirdState) Prop :=
  .mk fun _ s ↦ (∀ r, s.1 = some r → (∀ p, r = .error p → ∀ H q, ¬IsPoint c H q) ∧
    ∀ t, r = .ok t → t.WF c sp2) ∧ s.2.WF c sp2

attribute [local irreducible] primeTable in
/-- The contract of `Ratpoints.thirdStage`, for any values of the doubles: at an exit the curve has
no points; otherwise the pool stays one after the stages (`Ratpoints.ThirdState.WF`), the end of the
third stage within it. The loop ends, since the stage grows or one more prime is looked at. -/
theorem thirdStage_spec (c : List ℤ) (u mayExtend : Bool) (sp3Extra : ℤ) (sp3Want : ℕ)
    (perSurv perDenom : Float) (sp2 : ℕ) (st : ThirdState) :
    ⦃ st.WF c sp2 ⦄ thirdStage c (degree c) u mayExtend sp3Extra sp3Want perSurv perDenom st
    ⦃ fun r ↦ (∀ p, r = .error p → ∀ H q, ¬IsPoint c H q) ∧ ∀ t, r = .ok t → t.WF c sp2 ⦄ := by
  vcgen [thirdStage, bestByR_spec, rTyp_true, lookFurther_spec] invariants
  | inv1 => ThirdStageInvariant c sp2
  | inv2 => .ofMeasure fun s : Option (Except ℕ ThirdState) × ThirdState ↦
      (numPrimes - s.2.pnLim) + (sp3Want - s.2.sp3)
  all_goals simp only [Std.WP.Variant.evalsTo_ofMeasure, Std.WP.Variant.evalsBelow_ofMeasure_nat,
    Std.WP.Assertion.NondetFun.evalsTo_pure, Lean.Order.meet_prop_eq_and,
    Lean.Order.ofProp_prop_eq, Std.WP.WhileInvariant.mk, ThirdStageInvariant, ThirdState.WF,
    reduceCtorEq, false_implies, implies_true, true_and, and_true, Option.some.injEq,
    Except.error.injEq, Except.ok.injEq, forall_eq', ← Option.eq_none_iff_forall_ne_some] at *
  all_goals grind [ChoicePoolWF.push, ChoicePoolWF.swapIfInBounds]

end Ratpoints

end

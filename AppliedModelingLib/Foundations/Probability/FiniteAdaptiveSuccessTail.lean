import AppliedModelingLib.Foundations.Probability.FiniteExpectation
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# A finite adaptive success-count tail bound

This module proves the multiplicative-supermartingale estimate needed when
opportunities arrive adaptively, but every opportunity succeeds with a fixed
conditional probability lower bound.  No independence between the opportunity
indicators is assumed.

The concrete constants use the HR10 ratio `P(opportunity) ≤ 6 P(success)`.
An opportunity without success receives multiplier `12/11`, a success
receives `6/11`, and a non-opportunity receives `1`.  The conditional expected
multiplier is therefore at most one.
-/

namespace AppliedModelingLib

noncomputable section

/-- A finite adaptive trace generated from a history-dependent next-outcome
PMF. -/
def finiteAdaptiveTraceLaw
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (nextLaw : ∀ round, (Fin round → Outcome) → PMF Outcome) :
    (rounds : ℕ) → PMF (Fin rounds → Outcome)
  | 0 => PMF.pure Fin.elim0
  | rounds + 1 =>
      (finiteAdaptiveTraceLaw nextLaw rounds).bind fun history =>
        (nextLaw rounds history).map (Fin.snoc history)

/-- Appending a specific outcome to a fixed history has a unique preimage
under `Fin.snoc`. -/
theorem finiteAdaptiveTraceLaw_map_snoc_apply
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    {rounds : ℕ} (response : PMF Outcome)
    (history target : Fin rounds → Outcome) (outcome : Outcome) :
    PMF.map (@Fin.snoc rounds (fun _ ↦ Outcome) history) response
      (@Fin.snoc rounds (fun _ ↦ Outcome) target outcome) =
      if target = history then response outcome else 0 := by
  classical
  rw [PMF.map_apply, tsum_fintype]
  by_cases htarget : target = history
  · subst target
    rw [Finset.sum_eq_single outcome]
    · simp
    · intro other _ hother
      rw [if_neg]
      intro hequal
      exact hother (Fin.snoc_inj.mp hequal).2.symm
    · simp
  · have hnoPreimage : ∀ other : Outcome,
        @Fin.snoc rounds (fun _ ↦ Outcome) history other ≠
          @Fin.snoc rounds (fun _ ↦ Outcome) target outcome := by
      intro other hequal
      exact htarget (Fin.snoc_inj.mp hequal).1.symm
    rw [if_neg htarget]
    apply Finset.sum_eq_zero
    intro other _
    rw [if_neg]
    exact (hnoPreimage other).symm

/-- The atom mass of a finite adaptive trace factors into its prefix mass and
its history-conditioned final transition mass. -/
theorem finiteAdaptiveTraceLaw_snoc_apply
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (nextLaw : ∀ round, (Fin round → Outcome) → PMF Outcome)
    {rounds : ℕ} (history : Fin rounds → Outcome) (outcome : Outcome) :
    finiteAdaptiveTraceLaw nextLaw (rounds + 1) (Fin.snoc history outcome) =
      finiteAdaptiveTraceLaw nextLaw rounds history * nextLaw rounds history outcome := by
  classical
  rw [finiteAdaptiveTraceLaw, PMF.bind_apply, tsum_fintype]
  simp_rw [finiteAdaptiveTraceLaw_map_snoc_apply]
  rw [Finset.sum_eq_single history]
  · simp
  · intro other _ hother
    simp [hother.symm]
  · simp

/-- Real atom masses satisfy the same adaptive-prefix factorization. -/
theorem finiteAdaptiveTraceLaw_snoc_apply_toReal
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (nextLaw : ∀ round, (Fin round → Outcome) → PMF Outcome)
    {rounds : ℕ} (history : Fin rounds → Outcome) (outcome : Outcome) :
    (finiteAdaptiveTraceLaw nextLaw (rounds + 1) (Fin.snoc history outcome)).toReal =
      (finiteAdaptiveTraceLaw nextLaw rounds history).toReal *
        (nextLaw rounds history outcome).toReal := by
  rw [finiteAdaptiveTraceLaw_snoc_apply, ENNReal.toReal_mul]

/-- When the next-outcome law is history-independent, the adaptive trace law
is exactly the ordinary finite iid product law. -/
theorem finiteAdaptiveTraceLaw_constant_eq_pmfProduct
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (law : PMF Outcome) (rounds : ℕ) :
    finiteAdaptiveTraceLaw (fun _ _ => law) rounds =
      pmfProduct (Fin rounds) Outcome law := by
  apply PMF.ext
  intro trace
  induction rounds with
  | zero =>
      have htrace : trace = Fin.elim0 := Subsingleton.elim _ _
      subst trace
      simp [finiteAdaptiveTraceLaw]
  | succ rounds ih =>
      cases trace using Fin.snocCases with
      | snoc history outcome =>
          rw [finiteAdaptiveTraceLaw_snoc_apply, ih]
          change (∏ i : Fin rounds, law (history i)) * law outcome =
            ∏ i : Fin (rounds + 1), law
              (@Fin.snoc rounds (fun _ ↦ Outcome) history outcome i)
          rw [Fin.prod_univ_castSucc]
          simp

/-- One-step expectation identity for the adaptive trace law. -/
theorem pmfExp_finiteAdaptiveTraceLaw_succ
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (nextLaw : ∀ round, (Fin round → Outcome) → PMF Outcome)
    (rounds : ℕ) (statistic : (Fin (rounds + 1) → Outcome) → ℝ) :
    pmfExp (finiteAdaptiveTraceLaw nextLaw (rounds + 1)) statistic =
      pmfExp (finiteAdaptiveTraceLaw nextLaw rounds) (fun history =>
        pmfExp (nextLaw rounds history)
          (fun outcome => statistic (Fin.snoc history outcome))) := by
  change pmfExp
      ((finiteAdaptiveTraceLaw nextLaw rounds).bind fun history =>
        (nextLaw rounds history).map (Fin.snoc history)) statistic = _
  rw [pmfExp_bind]
  apply pmfExp_congr
  intro history
  rw [pmfExp_map]

/-- The recursively defined event that at least one history-conditioned
round predicate fails on a finite adaptive trace. -/
def finiteAdaptiveTraceAnyBadEvent
    {Outcome : Type*}
    (bad : ∀ round, (Fin round → Outcome) → Outcome → Prop) :
    ∀ rounds, (Fin rounds → Outcome) → Prop
  | 0, _ => False
  | rounds + 1, trace =>
      finiteAdaptiveTraceAnyBadEvent bad rounds (Fin.init trace) ∨
        bad rounds (Fin.init trace) (trace (Fin.last rounds))

/-- The recursive strict-prefix invariant that no round predicate has failed
on a finite adaptive trace. -/
def finiteAdaptiveTraceAllGood
    {Outcome : Type*}
    (bad : ∀ round, (Fin round → Outcome) → Outcome → Prop) :
    ∀ rounds, (Fin rounds → Outcome) → Prop
  | 0, _ => True
  | rounds + 1, trace =>
      finiteAdaptiveTraceAllGood bad rounds (Fin.init trace) ∧
        ¬ bad rounds (Fin.init trace) (trace (Fin.last rounds))

/-- A history-dependent invariant holds on every positive-mass adaptive trace
when it holds on every positive-mass next outcome.  This support-level form is
useful for structural sampler invariants whose failure probability is exactly
zero, rather than merely small. -/
theorem finiteAdaptiveTraceAllGood_of_support
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (nextLaw : ∀ round, (Fin round → Outcome) → PMF Outcome)
    (bad : ∀ round, (Fin round → Outcome) → Outcome → Prop)
    (hstep : ∀ round history outcome, outcome ∈ (nextLaw round history).support →
      ¬ bad round history outcome) :
    ∀ rounds trace, trace ∈ (finiteAdaptiveTraceLaw nextLaw rounds).support →
      finiteAdaptiveTraceAllGood bad rounds trace := by
  intro rounds
  induction rounds with
  | zero =>
      intro trace _
      simp [finiteAdaptiveTraceAllGood]
  | succ rounds ih =>
      intro trace htrace
      rw [finiteAdaptiveTraceLaw] at htrace
      obtain ⟨history, hhistory, hnext⟩ :=
        (PMF.mem_support_bind_iff _ _ trace).mp htrace
      obtain ⟨outcome, houtcome, hsuffix⟩ :=
        (PMF.mem_support_map_iff _ _ trace).mp hnext
      subst trace
      simp only [finiteAdaptiveTraceAllGood, Fin.init_snoc, Fin.snoc_last]
      exact ⟨ih history hhistory, hstep rounds history outcome houtcome⟩

/-- Extracting the invariant at an arbitrary round of an all-good trace uses
exactly that round's strict prefix. -/
def finiteAdaptiveTracePrefix
    {Outcome : Type*} {rounds : ℕ}
    (trace : Fin rounds → Outcome) (round : Fin rounds) : Fin round → Outcome :=
  fun previous => trace ⟨previous, lt_trans previous.2 round.2⟩

theorem finiteAdaptiveTraceAllGood_not_bad
    {Outcome : Type*}
    (bad : ∀ round, (Fin round → Outcome) → Outcome → Prop) :
    ∀ rounds (trace : Fin rounds → Outcome) (round : Fin rounds),
      finiteAdaptiveTraceAllGood bad rounds trace →
        ¬ bad round (finiteAdaptiveTracePrefix trace round) (trace round) := by
  intro rounds
  induction rounds with
  | zero =>
      intro trace round
      exact Fin.elim0 round
  | succ rounds ih =>
      intro trace round hgood
      rw [finiteAdaptiveTraceAllGood] at hgood
      refine Fin.lastCases ?_ ?_ round
      · simpa [finiteAdaptiveTracePrefix] using hgood.2
      · intro previous
        simpa [finiteAdaptiveTracePrefix] using ih (Fin.init trace) previous hgood.1

/-- The recursively accumulated good invariant is precisely the complement
of the event that a bad one-step predicate occurred. -/
theorem not_finiteAdaptiveTraceAnyBadEvent_iff_allGood
    {Outcome : Type*}
    (bad : ∀ round, (Fin round → Outcome) → Outcome → Prop) :
    ∀ rounds (trace : Fin rounds → Outcome),
      ¬ finiteAdaptiveTraceAnyBadEvent bad rounds trace ↔
        finiteAdaptiveTraceAllGood bad rounds trace := by
  intro rounds
  induction rounds with
  | zero =>
      intro trace
      simp [finiteAdaptiveTraceAnyBadEvent, finiteAdaptiveTraceAllGood]
  | succ rounds ih =>
      intro trace
      simp [finiteAdaptiveTraceAnyBadEvent, finiteAdaptiveTraceAllGood, ih (Fin.init trace)]

/-- The probability of a history-conditioned bad event occurring at any
round of a finite adaptive trace. -/
noncomputable def finiteAdaptiveTraceAnyBadProbability
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (nextLaw : ∀ round, (Fin round → Outcome) → PMF Outcome)
    (bad : ∀ round, (Fin round → Outcome) → Outcome → Prop)
    (rounds : ℕ) : ℝ := by
  classical
  letI : DecidablePred (finiteAdaptiveTraceAnyBadEvent bad rounds) := Classical.decPred _
  exact pmfProb (finiteAdaptiveTraceLaw nextLaw rounds)
    (finiteAdaptiveTraceAnyBadEvent bad rounds)

/-- A one-step extension increases the probability of any bad event by no
more than a uniform conditional bound for the newly sampled outcome. -/
theorem finiteAdaptiveTraceAnyBadProbability_succ_le
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (nextLaw : ∀ round, (Fin round → Outcome) → PMF Outcome)
    (bad : ∀ round, (Fin round → Outcome) → Outcome → Prop)
    (rounds : ℕ) (failure : ℝ)
    [∀ round history, DecidablePred (bad round history)]
    (hfailure : ∀ history,
      pmfProb (nextLaw rounds history) (bad rounds history) ≤ failure) :
    finiteAdaptiveTraceAnyBadProbability nextLaw bad (rounds + 1) ≤
      finiteAdaptiveTraceAnyBadProbability nextLaw bad rounds + failure := by
  classical
  unfold finiteAdaptiveTraceAnyBadProbability
  simp only [finiteAdaptiveTraceAnyBadEvent]
  have hprefix :
      pmfProb (finiteAdaptiveTraceLaw nextLaw (rounds + 1))
        (fun trace => finiteAdaptiveTraceAnyBadEvent bad rounds (Fin.init trace)) =
      pmfProb (finiteAdaptiveTraceLaw nextLaw rounds)
        (finiteAdaptiveTraceAnyBadEvent bad rounds) := by
    unfold pmfProb
    rw [pmfExp_finiteAdaptiveTraceLaw_succ]
    simp
  have hcurrent :
      pmfProb (finiteAdaptiveTraceLaw nextLaw (rounds + 1))
        (fun trace => bad rounds (Fin.init trace) (trace (Fin.last rounds))) ≤ failure := by
    rw [pmfProb]
    rw [pmfExp_finiteAdaptiveTraceLaw_succ]
    calc
      _ ≤ pmfExp (finiteAdaptiveTraceLaw nextLaw rounds) (fun _ => failure) := by
        apply pmfExp_le_pmfExp_of_forall_le
        intro history
        simpa only [Fin.init_snoc, Fin.snoc_last, pmfProb] using hfailure history
      _ = failure := pmfExp_const _ _
  have hunion := pmfProb_or_le
    (finiteAdaptiveTraceLaw nextLaw (rounds + 1))
    (fun trace : Fin (rounds + 1) → Outcome =>
      finiteAdaptiveTraceAnyBadEvent bad rounds (Fin.init trace))
    (fun trace : Fin (rounds + 1) → Outcome =>
      bad rounds (Fin.init trace) (trace (Fin.last rounds)))
  refine (le_trans ?_ hunion).trans ?_
  · unfold pmfProb
    apply le_of_eq
    apply pmfExp_congr
    intro trace
    by_cases hbad : finiteAdaptiveTraceAnyBadEvent bad rounds (Fin.init trace) ∨
      bad rounds (Fin.init trace) (trace (Fin.last rounds)) <;> simp [hbad]
  · calc
      pmfProb (finiteAdaptiveTraceLaw nextLaw (rounds + 1))
          (fun trace => finiteAdaptiveTraceAnyBadEvent bad rounds (Fin.init trace)) +
        pmfProb (finiteAdaptiveTraceLaw nextLaw (rounds + 1))
          (fun trace => bad rounds (Fin.init trace) (trace (Fin.last rounds))) =
        pmfProb (finiteAdaptiveTraceLaw nextLaw rounds)
          (finiteAdaptiveTraceAnyBadEvent bad rounds) +
        pmfProb (finiteAdaptiveTraceLaw nextLaw (rounds + 1))
          (fun trace => bad rounds (Fin.init trace) (trace (Fin.last rounds))) := by
            rw [hprefix]
      _ ≤ pmfProb (finiteAdaptiveTraceLaw nextLaw rounds)
            (finiteAdaptiveTraceAnyBadEvent bad rounds) + failure :=
          add_le_add_right hcurrent _

/-- The finite-horizon union bound for arbitrary events whose one-step law
may depend on the entire strict adaptive trace. -/
theorem finiteAdaptiveTraceAnyBadProbability_le_sum
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (nextLaw : ∀ round, (Fin round → Outcome) → PMF Outcome)
    (bad : ∀ round, (Fin round → Outcome) → Outcome → Prop)
    (rounds : ℕ) (failure : ℕ → ℝ)
    [∀ round history, DecidablePred (bad round history)]
    (hfailure : ∀ round history,
      pmfProb (nextLaw round history) (bad round history) ≤ failure round) :
    finiteAdaptiveTraceAnyBadProbability nextLaw bad rounds ≤
      ∑ round ∈ Finset.range rounds, failure round := by
  induction rounds with
  | zero =>
      classical
      unfold finiteAdaptiveTraceAnyBadProbability
      simp [finiteAdaptiveTraceAnyBadEvent, pmfProb, pmfExp]
  | succ rounds ih =>
      calc
        finiteAdaptiveTraceAnyBadProbability nextLaw bad (rounds + 1) ≤
            finiteAdaptiveTraceAnyBadProbability nextLaw bad rounds + failure rounds :=
          finiteAdaptiveTraceAnyBadProbability_succ_le nextLaw bad rounds
            (failure rounds) (hfailure rounds)
        _ ≤ (∑ round ∈ Finset.range rounds, failure round) + failure rounds :=
          add_le_add_left ih _
        _ = ∑ round ∈ Finset.range (rounds + 1), failure round := by
          rw [Finset.sum_range_succ]

/-- Number of outcomes in a trace selected by a Boolean classifier. -/
def finiteAdaptiveBoolCount
    {Outcome : Type*} (selected : Outcome → Bool)
    {rounds : ℕ} (trace : Fin rounds → Outcome) : ℕ :=
  ∑ round, if selected (trace round) then 1 else 0

/-- Appending one outcome adds its Boolean indicator to the count. -/
theorem finiteAdaptiveBoolCount_snoc
    {Outcome : Type*} (selected : Outcome → Bool)
    {rounds : ℕ} (history : Fin rounds → Outcome) (outcome : Outcome) :
    finiteAdaptiveBoolCount selected (Fin.snoc history outcome) =
      finiteAdaptiveBoolCount selected history +
        (if selected outcome then 1 else 0) := by
  unfold finiteAdaptiveBoolCount
  rw [Fin.sum_univ_castSucc]
  simp

/-- Per-round multiplier for the `1/6` conditional-success argument. -/
def oneSixthSuccessMultiplier
    {Outcome : Type*} (opportunity success : Outcome → Bool)
    (outcome : Outcome) : ℝ :=
  if opportunity outcome then
    if success outcome then 6 / 11 else 12 / 11
  else
    1

/-- The multiplier is pointwise positive. -/
theorem oneSixthSuccessMultiplier_pos
    {Outcome : Type*} (opportunity success : Outcome → Bool)
  (outcome : Outcome) :
    0 < oneSixthSuccessMultiplier opportunity success outcome := by
  by_cases hopportunity : opportunity outcome = true
  · by_cases hsuccess : success outcome = true <;>
      simp [oneSixthSuccessMultiplier, hopportunity, hsuccess]
  · simp [oneSixthSuccessMultiplier, hopportunity]

/-- Algebraic form of the multiplier when every success is an opportunity. -/
theorem oneSixthSuccessMultiplier_eq
    {Outcome : Type*} (opportunity success : Outcome → Bool)
    (hsuccess : ∀ outcome, success outcome = true →
      opportunity outcome = true) (outcome : Outcome) :
    oneSixthSuccessMultiplier opportunity success outcome =
      1 + (if opportunity outcome then (1 : ℝ) else 0) / 11 -
        6 * (if success outcome then (1 : ℝ) else 0) / 11 := by
  by_cases hopportunity : opportunity outcome = true
  · by_cases hsuccessOutcome : success outcome = true <;>
      simp [oneSixthSuccessMultiplier, hopportunity, hsuccessOutcome] <;>
      norm_num
  · have hnotSuccess : success outcome ≠ true := by
      intro hsuccessTrue
      exact hopportunity (hsuccess outcome hsuccessTrue)
    simp [oneSixthSuccessMultiplier, hopportunity, hnotSuccess]

/-- The expected one-round multiplier is at most one whenever conditional
opportunity mass is at most six times conditional success mass. -/
theorem pmfExp_oneSixthSuccessMultiplier_le_one
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (law : PMF Outcome) (opportunity success : Outcome → Bool)
    (hsuccess : ∀ outcome, success outcome = true →
      opportunity outcome = true)
    (hmass : pmfProb law (fun outcome => opportunity outcome = true) ≤
      6 * pmfProb law (fun outcome => success outcome = true)) :
    pmfExp law (oneSixthSuccessMultiplier opportunity success) ≤ 1 := by
  have hpoint :
      oneSixthSuccessMultiplier opportunity success =
        fun outcome =>
          1 + (if opportunity outcome then (1 : ℝ) else 0) / 11 -
            6 * (if success outcome then (1 : ℝ) else 0) / 11 := by
    funext outcome
    exact oneSixthSuccessMultiplier_eq opportunity success hsuccess outcome
  rw [hpoint, pmfExp_sub, pmfExp_add]
  have hopportunity :
      pmfExp law (fun outcome =>
        (if opportunity outcome then (1 : ℝ) else 0) / 11) =
          pmfProb law (fun outcome => opportunity outcome = true) / 11 := by
    have hrewrite : (fun outcome =>
        (if opportunity outcome then (1 : ℝ) else 0) / 11) =
        fun outcome =>
          (if opportunity outcome then (1 : ℝ) else 0) * (1 / 11) := by
      funext outcome
      ring
    rw [hrewrite, pmfExp_mul_const]
    simp [pmfProb]
    ring
  have hsuccessExp :
      pmfExp law (fun outcome =>
        6 * (if success outcome then (1 : ℝ) else 0) / 11) =
          6 * pmfProb law (fun outcome => success outcome = true) / 11 := by
    have hrewrite : (fun outcome =>
        6 * (if success outcome then (1 : ℝ) else 0) / 11) =
        fun outcome => (6 / 11) *
          (if success outcome then (1 : ℝ) else 0) := by
      funext outcome
      ring
    rw [hrewrite, pmfExp_const_mul]
    simp [pmfProb]
    ring
  rw [pmfExp_const, hopportunity, hsuccessExp]
  linarith

/-- Product multiplier accumulated along a finite adaptive trace. -/
def finiteAdaptiveSuccessWeight
    {Outcome : Type*} (opportunity success : Outcome → Bool)
    {rounds : ℕ} (trace : Fin rounds → Outcome) : ℝ :=
  ∏ round, oneSixthSuccessMultiplier opportunity success (trace round)

/-- The accumulated weight is positive. -/
theorem finiteAdaptiveSuccessWeight_pos
    {Outcome : Type*} (opportunity success : Outcome → Bool)
    {rounds : ℕ} (trace : Fin rounds → Outcome) :
    0 < finiteAdaptiveSuccessWeight opportunity success trace := by
  unfold finiteAdaptiveSuccessWeight
  exact Finset.prod_pos fun round _ =>
    oneSixthSuccessMultiplier_pos opportunity success (trace round)

/-- Appending one outcome multiplies the accumulated weight by its one-round
factor. -/
theorem finiteAdaptiveSuccessWeight_snoc
    {Outcome : Type*} (opportunity success : Outcome → Bool)
    {rounds : ℕ} (history : Fin rounds → Outcome) (outcome : Outcome) :
    finiteAdaptiveSuccessWeight opportunity success
        (Fin.snoc history outcome) =
      finiteAdaptiveSuccessWeight opportunity success history *
        oneSixthSuccessMultiplier opportunity success outcome := by
  unfold finiteAdaptiveSuccessWeight
  rw [Fin.prod_univ_castSucc]
  simp

/-- One-round multiplier as an opportunity factor times a success penalty. -/
theorem oneSixthSuccessMultiplier_eq_indicator_powers
    {Outcome : Type*} (opportunity success : Outcome → Bool)
    (hsuccess : ∀ outcome, success outcome = true →
      opportunity outcome = true) (outcome : Outcome) :
    oneSixthSuccessMultiplier opportunity success outcome =
      (12 / 11 : ℝ) ^ (if opportunity outcome then 1 else 0) *
        (1 / 2 : ℝ) ^ (if success outcome then 1 else 0) := by
  by_cases hopportunity : opportunity outcome = true
  · by_cases hsuccessOutcome : success outcome = true <;>
      simp [oneSixthSuccessMultiplier, hopportunity, hsuccessOutcome] <;>
      norm_num
  · have hnotSuccess : success outcome ≠ true := by
      intro hsuccessTrue
      exact hopportunity (hsuccess outcome hsuccessTrue)
    simp [oneSixthSuccessMultiplier, hopportunity, hnotSuccess]

/-- Closed form of the accumulated multiplier in terms of the two counts. -/
theorem finiteAdaptiveSuccessWeight_eq_count_powers
    {Outcome : Type*} (opportunity success : Outcome → Bool)
    (hsuccess : ∀ outcome, success outcome = true →
      opportunity outcome = true)
    {rounds : ℕ} (trace : Fin rounds → Outcome) :
    finiteAdaptiveSuccessWeight opportunity success trace =
      (12 / 11 : ℝ) ^ finiteAdaptiveBoolCount opportunity trace *
        (1 / 2 : ℝ) ^ finiteAdaptiveBoolCount success trace := by
  unfold finiteAdaptiveSuccessWeight finiteAdaptiveBoolCount
  calc
    ∏ round, oneSixthSuccessMultiplier opportunity success (trace round) =
        ∏ round,
          ((12 / 11 : ℝ) ^ (if opportunity (trace round) then 1 else 0) *
            (1 / 2 : ℝ) ^ (if success (trace round) then 1 else 0)) := by
      apply Finset.prod_congr rfl
      intro round _
      exact oneSixthSuccessMultiplier_eq_indicator_powers
        opportunity success hsuccess (trace round)
    _ = (∏ round,
          (12 / 11 : ℝ) ^ (if opportunity (trace round) then 1 else 0)) *
        ∏ round,
          (1 / 2 : ℝ) ^ (if success (trace round) then 1 else 0) := by
      exact Finset.prod_mul_distrib
    _ = (12 / 11 : ℝ) ^
          (∑ round, if opportunity (trace round) then 1 else 0) *
        (1 / 2 : ℝ) ^
          (∑ round, if success (trace round) then 1 else 0) := by
      rw [Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]

/-- Logarithm of the accumulated multiplier. -/
theorem log_finiteAdaptiveSuccessWeight
    {Outcome : Type*} (opportunity success : Outcome → Bool)
    (hsuccess : ∀ outcome, success outcome = true →
      opportunity outcome = true)
    {rounds : ℕ} (trace : Fin rounds → Outcome) :
    Real.log (finiteAdaptiveSuccessWeight opportunity success trace) =
      (finiteAdaptiveBoolCount opportunity trace : ℝ) *
          Real.log (12 / 11 : ℝ) -
        (finiteAdaptiveBoolCount success trace : ℝ) * Real.log 2 := by
  rw [finiteAdaptiveSuccessWeight_eq_count_powers
    opportunity success hsuccess]
  have hbase : (12 / 11 : ℝ) ≠ 0 := by norm_num
  have hhalf : (1 / 2 : ℝ) ≠ 0 := by norm_num
  rw [Real.log_mul (pow_ne_zero _ hbase) (pow_ne_zero _ hhalf),
    Real.log_pow, Real.log_pow]
  have hlogHalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
    ring
  rw [hlogHalf]
  ring

/-- The adaptive accumulated multiplier has expectation at most one. -/
theorem pmfExp_finiteAdaptiveSuccessWeight_le_one
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (nextLaw : ∀ round, (Fin round → Outcome) → PMF Outcome)
    (opportunity success : Outcome → Bool)
    (hsuccess : ∀ outcome, success outcome = true →
      opportunity outcome = true)
    (hmass : ∀ round history,
      pmfProb (nextLaw round history)
          (fun outcome => opportunity outcome = true) ≤
        6 * pmfProb (nextLaw round history)
          (fun outcome => success outcome = true)) :
    ∀ rounds,
      pmfExp (finiteAdaptiveTraceLaw nextLaw rounds)
        (finiteAdaptiveSuccessWeight opportunity success) ≤ 1 := by
  intro rounds
  induction rounds with
  | zero => simp [finiteAdaptiveTraceLaw, finiteAdaptiveSuccessWeight]
  | succ rounds ih =>
      rw [pmfExp_finiteAdaptiveTraceLaw_succ]
      calc
        pmfExp (finiteAdaptiveTraceLaw nextLaw rounds) (fun history =>
            pmfExp (nextLaw rounds history)
              (fun outcome => finiteAdaptiveSuccessWeight opportunity success
                (Fin.snoc history outcome))) =
          pmfExp (finiteAdaptiveTraceLaw nextLaw rounds) (fun history =>
            finiteAdaptiveSuccessWeight opportunity success history *
              pmfExp (nextLaw rounds history)
                (oneSixthSuccessMultiplier opportunity success)) := by
            apply pmfExp_congr
            intro history
            simp_rw [finiteAdaptiveSuccessWeight_snoc]
            exact pmfExp_const_mul _ _ _
        _ ≤ pmfExp (finiteAdaptiveTraceLaw nextLaw rounds)
            (finiteAdaptiveSuccessWeight opportunity success) := by
          apply pmfExp_le_pmfExp_of_forall_le
          intro history
          have hround := pmfExp_oneSixthSuccessMultiplier_le_one
            (nextLaw rounds history) opportunity success hsuccess
            (hmass rounds history)
          exact mul_le_of_le_one_right
            (finiteAdaptiveSuccessWeight_pos opportunity success history).le
            hround
        _ ≤ 1 := ih

/-- A convenient rational lower bound for the logarithmic opportunity
multiplier. -/
theorem one_twelfth_le_log_twelve_elevenths :
    (1 / 12 : ℝ) ≤ Real.log (12 / 11 : ℝ) := by
  have h := Real.one_sub_inv_le_log_of_pos
    (x := (12 / 11 : ℝ)) (by norm_num)
  norm_num at h ⊢
  exact h

/-- A rational lower bound on `log 2`. -/
theorem two_thirds_le_log_two :
    (2 / 3 : ℝ) ≤ Real.log 2 := by
  have h := Real.le_log_one_add_of_nonneg (x := (1 : ℝ)) (by norm_num)
  convert h using 1 <;> norm_num

/-- The elementary upper bound `log 2 < 1`. -/
theorem log_two_lt_one : Real.log 2 < 1 := by
  exact (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)).2
    Real.exp_one_gt_two

/-- The source count threshold forces the adaptive multiplier above the
Markov threshold `2/delta`. -/
theorem finiteAdaptiveSuccessWeight_gt_two_div
    {Outcome : Type*} (opportunity success : Outcome → Bool)
    (hsuccess : ∀ outcome, success outcome = true →
      opportunity outcome = true)
    {rounds maxSuccesses : ℕ} (hmaxSuccesses : 0 < maxSuccesses)
    {delta : ℝ} (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (trace : Fin rounds → Outcome)
    (hopportunityCount :
      32 * (maxSuccesses : ℝ) * Real.log (2 / delta) <
        (finiteAdaptiveBoolCount opportunity trace : ℝ))
    (hsuccessCount :
      finiteAdaptiveBoolCount success trace ≤ maxSuccesses) :
    2 / delta < finiteAdaptiveSuccessWeight opportunity success trace := by
  let opportunityCount : ℝ :=
    finiteAdaptiveBoolCount opportunity trace
  let successCount : ℝ := finiteAdaptiveBoolCount success trace
  let maxCount : ℝ := maxSuccesses
  let confidenceLog : ℝ := Real.log (2 / delta)
  have hratioPos : 0 < (2 / delta : ℝ) := div_pos (by norm_num) hdelta
  have hratioTwo : (2 : ℝ) ≤ 2 / delta := by
    rw [le_div_iff₀ hdelta]
    nlinarith
  have hconfidence : (2 / 3 : ℝ) ≤ confidenceLog := by
    exact two_thirds_le_log_two.trans
      (Real.log_le_log (by norm_num : (0 : ℝ) < 2) hratioTwo)
  have hopportunityNonneg : 0 ≤ opportunityCount := by
    dsimp [opportunityCount]
    positivity
  have hsuccessNonneg : 0 ≤ successCount := by
    dsimp [successCount]
    positivity
  have hmaxOne : 1 ≤ maxCount := by
    dsimp [maxCount]
    exact_mod_cast (show 1 ≤ maxSuccesses by omega)
  have hmaxNonneg : 0 ≤ maxCount := hmaxOne.trans' (by norm_num)
  have hopportunityLog :
      (8 / 3 : ℝ) * maxCount * confidenceLog <
        opportunityCount * Real.log (12 / 11 : ℝ) := by
    have hscaled := mul_lt_mul_of_pos_right hopportunityCount
      (show (0 : ℝ) < 1 / 12 by norm_num)
    have hbase := mul_le_mul_of_nonneg_left
      one_twelfth_le_log_twelve_elevenths hopportunityNonneg
    dsimp [opportunityCount, maxCount, confidenceLog] at hscaled ⊢
    calc
      (8 / 3 : ℝ) * (maxSuccesses : ℝ) * Real.log (2 / delta) =
          (32 * (maxSuccesses : ℝ) * Real.log (2 / delta)) *
            (1 / 12) := by ring
      _ < (finiteAdaptiveBoolCount opportunity trace : ℝ) * (1 / 12) :=
        hscaled
      _ ≤ (finiteAdaptiveBoolCount opportunity trace : ℝ) *
          Real.log (12 / 11 : ℝ) := hbase
  have hsuccessCast : successCount ≤ maxCount := by
    dsimp [successCount, maxCount]
    exact_mod_cast hsuccessCount
  have hlogTwoNonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hsuccessLog : successCount * Real.log 2 ≤ maxCount := by
    calc
      successCount * Real.log 2 ≤ maxCount * Real.log 2 :=
        mul_le_mul_of_nonneg_right hsuccessCast hlogTwoNonneg
      _ ≤ maxCount * 1 :=
        mul_le_mul_of_nonneg_left log_two_lt_one.le hmaxNonneg
      _ = maxCount := by ring
  have hlogWeight :
      (8 / 3 : ℝ) * maxCount * confidenceLog - maxCount <
        Real.log (finiteAdaptiveSuccessWeight opportunity success trace) := by
    rw [log_finiteAdaptiveSuccessWeight opportunity success hsuccess]
    dsimp [opportunityCount, successCount, maxCount] at hopportunityLog
    dsimp [opportunityCount, successCount, maxCount] at hsuccessLog
    dsimp [opportunityCount, successCount, maxCount]
    linarith
  have hcoefficient :
      0 ≤ (8 / 3 : ℝ) * confidenceLog - 1 := by
    nlinarith
  have hproduct :
      0 ≤ (maxCount - 1) * ((8 / 3 : ℝ) * confidenceLog - 1) :=
    mul_nonneg (by linarith) hcoefficient
  have hconfidenceGap :
      confidenceLog <
        (8 / 3 : ℝ) * maxCount * confidenceLog - maxCount := by
    nlinarith
  have hlogThreshold :
      confidenceLog <
        Real.log (finiteAdaptiveSuccessWeight opportunity success trace) :=
    hconfidenceGap.trans hlogWeight
  have hexp := (Real.lt_log_iff_exp_lt
    (finiteAdaptiveSuccessWeight_pos opportunity success trace)).1
      hlogThreshold
  have hexpConfidence : Real.exp confidenceLog = 2 / delta := by
    exact Real.exp_log hratioPos
  rw [hexpConfidence] at hexp
  exact hexp

/-- Adaptive `1/6` success-count tail.  If at most `m` successes can occur,
then more than `32 m log(2/delta)` opportunities has probability at most
`delta/2`. -/
theorem finiteAdaptiveOneSixthOpportunityTail
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (nextLaw : ∀ round, (Fin round → Outcome) → PMF Outcome)
    (opportunity success : Outcome → Bool)
    (hsuccess : ∀ outcome, success outcome = true →
      opportunity outcome = true)
    (hmass : ∀ round history,
      pmfProb (nextLaw round history)
          (fun outcome => opportunity outcome = true) ≤
        6 * pmfProb (nextLaw round history)
          (fun outcome => success outcome = true))
    (rounds maxSuccesses : ℕ) (hmaxSuccesses : 0 < maxSuccesses)
    (delta : ℝ) (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1) :
    pmfProb (finiteAdaptiveTraceLaw nextLaw rounds) (fun trace =>
      32 * (maxSuccesses : ℝ) * Real.log (2 / delta) <
          (finiteAdaptiveBoolCount opportunity trace : ℝ) ∧
        finiteAdaptiveBoolCount success trace ≤ maxSuccesses) ≤
      delta / 2 := by
  let law : PMF (Fin rounds → Outcome) :=
    finiteAdaptiveTraceLaw nextLaw rounds
  let weight : (Fin rounds → Outcome) → ℝ :=
    finiteAdaptiveSuccessWeight opportunity success
  let threshold : ℝ := 2 / delta
  have hweightNonneg : ∀ trace, 0 ≤ weight trace := fun trace =>
    (finiteAdaptiveSuccessWeight_pos opportunity success trace).le
  have hthresholdPos : 0 < threshold := div_pos (by norm_num) hdelta
  have hexpectation : pmfExp law weight ≤ 1 :=
    pmfExp_finiteAdaptiveSuccessWeight_le_one
      nextLaw opportunity success hsuccess hmass rounds
  have hinclusion :
      pmfProb law (fun trace =>
          32 * (maxSuccesses : ℝ) * Real.log (2 / delta) <
              (finiteAdaptiveBoolCount opportunity trace : ℝ) ∧
            finiteAdaptiveBoolCount success trace ≤ maxSuccesses) ≤
        pmfProb law (fun trace => threshold < weight trace) := by
    apply pmfProb_le_of_imp
    intro trace htrace
    exact finiteAdaptiveSuccessWeight_gt_two_div
      opportunity success hsuccess hmaxSuccesses hdelta hdeltaOne trace
      htrace.1 htrace.2
  have hmarkov := pmfExp_ge_of_nonneg_of_tail
    law weight threshold hweightNonneg hthresholdPos.le
  have htailMul :
      threshold * pmfProb law (fun trace => threshold < weight trace) ≤ 1 :=
    hmarkov.trans hexpectation
  have htail :
      pmfProb law (fun trace => threshold < weight trace) ≤ delta / 2 := by
    have hdiv :
        pmfProb law (fun trace => threshold < weight trace) ≤ 1 / threshold := by
      rw [le_div_iff₀ hthresholdPos]
      simpa [mul_comm] using htailMul
    calc
      pmfProb law (fun trace => threshold < weight trace) ≤ 1 / threshold := hdiv
      _ = delta / 2 := by
        dsimp [threshold]
        field_simp [hdelta.ne']
  exact hinclusion.trans htail

end

end AppliedModelingLib

import FalahatgarEtAl2017MaxingRanking.OptMaximizeFallback
import FalahatgarEtAl2017MaxingRanking.OptMaximizeFinal
import AppliedModelingLib.Learning.ReinforcementLearning.Preference.AdaptiveQueryInvariants

/-!
# Fresh finite final checks for OPT-Maximize

Algorithm 3 performs one fresh adaptive-Compare call for each arm retained by
Prune.  This file gives that loop its own finite-PMF execution.  In
particular, it does not reuse the random bits from Pick-Anchor, Prune, or the
fallback Seq-Eliminate call.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL
open MeasureTheory ProbabilityTheory

/-- The candidate examined at a given position in the deterministic Finset enumeration. -/
noncomputable def finsetFinalCheckCandidate {Arm : Type*} [DecidableEq Arm]
    (anchor : Arm) (candidates : Finset Arm) (queryIndex : ℕ) : Arm :=
  candidates.toList.getD queryIndex anchor

/-- Every in-range final-loop position names a retained candidate. -/
theorem finsetFinalCheckCandidate_mem_of_lt {Arm : Type*} [DecidableEq Arm]
    (anchor : Arm) (candidates : Finset Arm) (queryIndex : ℕ)
    (hqueryIndex : queryIndex < candidates.card) :
    finsetFinalCheckCandidate anchor candidates queryIndex ∈ candidates := by
  unfold finsetFinalCheckCandidate
  have hlength : queryIndex < candidates.toList.length := by
    simpa only [Finset.length_toList] using hqueryIndex
  rw [List.getD_eq_getElem _ _ hlength]
  exact Finset.mem_toList.mp (List.getElem_mem _)

/-- A retained arm appears at one in-range position of the final-loop enumeration. -/
theorem exists_finsetFinalCheckCandidate_eq_of_mem {Arm : Type*} [DecidableEq Arm]
    (anchor maximum : Arm) (candidates : Finset Arm) (hmaximumMem : maximum ∈ candidates) :
    ∃ queryIndex < candidates.card,
      finsetFinalCheckCandidate anchor candidates queryIndex = maximum := by
  have hlist : maximum ∈ candidates.toList := Finset.mem_toList.mpr hmaximumMem
  rw [List.mem_iff_getElem] at hlist
  rcases hlist with ⟨queryIndex, hqueryIndex, hvalue⟩
  refine ⟨queryIndex, ?_, ?_⟩
  · simpa only [Finset.length_toList] using hqueryIndex
  · unfold finsetFinalCheckCandidate
    rw [List.getD_eq_getElem _ _ hqueryIndex]
    exact hvalue

/--
The actual fresh batch law for one final-loop comparison.  The loop state is
irrelevant to the next batch distribution, but it records whether an upper
decision has already occurred.
-/
noncomputable def canonicalFreshFinalCheckOutcomeLaw
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (anchor : Arm) (candidates : Finset Arm)
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (lower upper eta : ℝ) :
    AdaptiveOutcomeKernel Bool (Fin (fixedSampleBudget lower upper eta) → Bool) :=
  fun queryIndex _ =>
    canonicalComparisonBatchLaw preferenceGap hprobability
      (finsetFinalCheckCandidate anchor candidates queryIndex) anchor
      (fixedSampleBudget lower upper eta)

/-- Advance the final-loop flag; `true` means that no queried arm has yet won the upper test. -/
noncomputable def canonicalFreshFinalCheckAdvance
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (candidates : Finset Arm) (lower upper eta : ℝ) :
    AdaptiveStateUpdate Bool (Fin (fixedSampleBudget lower upper eta) → Bool) :=
  fun queryIndex noUpper outcome =>
    if _hqueryIndex : queryIndex < candidates.card then
      noUpper && decide (adaptiveCompare
        (canonicalComparisonBatchObservation (fixedSampleBudget lower upper eta))
        (fixedSampleBudget lower upper eta) lower upper eta outcome ≠ .upper)
    else noUpper

/-- The state law of the source final loop after exactly one comparison per retained arm. -/
noncomputable def canonicalFreshFinalCheckNoUpperLaw
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (anchor : Arm) (candidates : Finset Arm)
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (lower upper eta : ℝ) : PMF Bool :=
  adaptiveQueryActiveLaw (PMF.pure true)
    (canonicalFreshFinalCheckOutcomeLaw anchor candidates preferenceGap hprobability lower upper eta)
    (canonicalFreshFinalCheckAdvance candidates lower upper eta)
    candidates.card

/--
The final-loop output on the same execution: return the precomputed fallback
exactly when some retained candidate passes the upper comparison threshold.
-/
noncomputable def canonicalFreshFinalCheckOutputLaw
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (anchor fallback : Arm) (candidates : Finset Arm)
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (lower upper eta : ℝ) : PMF Arm :=
  (canonicalFreshFinalCheckNoUpperLaw anchor candidates preferenceGap hprobability lower upper eta).map
    fun noUpper => if noUpper then anchor else fallback

/--
The literal randomized tail of Algorithm 3 after the anchor and retained set
are fixed: first run Seq-Eliminate on the retained set, then run the fresh
final comparison loop and retain both the fallback and final output.  Keeping
the intermediate fallback visible makes the two conditional failure budgets
auditable without an independence assumption.
-/
noncomputable def canonicalOptMaximizeTailSourceLaw
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (anchor : Arm) (candidates : Finset Arm)
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (epsilon delta : ℝ) : PMF (Arm × Arm) :=
  (canonicalFreshFinsetSeqEliminateOutputLaw anchor candidates preferenceGap hprobability
      epsilon ((delta / 4) / (candidates.card : ℝ))).bind fun fallback =>
    (canonicalFreshFinalCheckOutputLaw anchor fallback candidates preferenceGap hprobability
      (2 * epsilon / 3) epsilon ((delta / 4) / (Fintype.card Arm : ℝ))).map
        fun output => (fallback, output)

/--
If every retained arm is below the lower Compare threshold against the anchor,
then the actual final loop has no upper decision except with the sum of its
fresh per-call failure budgets.
-/
theorem canonicalFreshFinalCheck_noUpper_probability_of_all_lower
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (anchor : Arm) (candidates : Finset Arm)
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (lower upper eta : ℝ)
    (hbelow : ∀ candidate ∈ candidates, preferenceGap candidate anchor ≤ lower)
    (hseparation : lower < upper) (heta : 0 < eta) (hetaLeOne : eta ≤ 1) :
    1 - (candidates.card : ℝ) * eta ≤
      pmfProb (canonicalFreshFinalCheckNoUpperLaw anchor candidates preferenceGap hprobability
        lower upper eta) (fun noUpper => noUpper = true) := by
  classical
  let outcomeLaw : AdaptiveOutcomeKernel Bool (Fin (fixedSampleBudget lower upper eta) → Bool) :=
    canonicalFreshFinalCheckOutcomeLaw anchor candidates preferenceGap hprobability lower upper eta
  let advance : AdaptiveStateUpdate Bool (Fin (fixedSampleBudget lower upper eta) → Bool) :=
    canonicalFreshFinalCheckAdvance candidates lower upper eta
  let bad : ℕ → Bool → (Fin (fixedSampleBudget lower upper eta) → Bool) → Prop :=
    fun queryIndex _ outcome => if hqueryIndex : queryIndex < candidates.card then
      adaptiveCompare (canonicalComparisonBatchObservation (fixedSampleBudget lower upper eta))
        (fixedSampleBudget lower upper eta) lower upper eta outcome ≠ .lower
    else False
  have hfailure : ∀ queryIndex state,
      pmfProb (outcomeLaw queryIndex state) (bad queryIndex state) ≤ eta := by
    intro queryIndex state
    by_cases hqueryIndex : queryIndex < candidates.card
    · simp only [bad, dif_pos hqueryIndex]
      rw [← pmfProbClassical_eq_pmfProb]
      change pmfProbClassical (canonicalComparisonBatchLaw preferenceGap hprobability
        (finsetFinalCheckCandidate anchor candidates queryIndex) anchor
        (fixedSampleBudget lower upper eta)) (fun outcome =>
          adaptiveCompare (canonicalComparisonBatchObservation
            (fixedSampleBudget lower upper eta)) (fixedSampleBudget lower upper eta)
            lower upper eta outcome ≠ .lower) ≤ eta
      rw [pmfProbClassical_eq_pmfProb, AppliedModelingLib.pmfProb_eq_toMeasure_real]
      apply finiteBatchAdaptiveCompare_lower_failure_probability_of_ceilingBudget
        (canonicalComparisonBatchLaw preferenceGap hprobability
          (finsetFinalCheckCandidate anchor candidates queryIndex) anchor
          (fixedSampleBudget lower upper eta)).toMeasure
        (canonicalComparisonBatchObservation (fixedSampleBudget lower upper eta))
        lower upper (preferenceGap (finsetFinalCheckCandidate anchor candidates queryIndex) anchor) eta
      · simpa using iIndepFun_canonicalComparisonBatchObservation preferenceGap hprobability
          (finsetFinalCheckCandidate anchor candidates queryIndex) anchor
          (fixedSampleBudget lower upper eta)
      · intro sampleIndex hsampleIndex
        exact measurable_canonicalComparisonBatchObservation
          (fixedSampleBudget lower upper eta) sampleIndex
      · intro sampleIndex hsampleIndex
        exact ae_canonicalComparisonBatchObservation_mem_Icc preferenceGap hprobability
          (finsetFinalCheckCandidate anchor candidates queryIndex) anchor
          (fixedSampleBudget lower upper eta) sampleIndex
      · intro sampleIndex hsampleIndex
        exact integral_canonicalComparisonBatchObservation_of_lt preferenceGap hprobability
          (finsetFinalCheckCandidate anchor candidates queryIndex) anchor
          (fixedSampleBudget lower upper eta) sampleIndex hsampleIndex
      · exact hbelow (finsetFinalCheckCandidate anchor candidates queryIndex)
          (finsetFinalCheckCandidate_mem_of_lt anchor candidates queryIndex hqueryIndex)
      · exact hseparation
      · exact heta
      · exact hetaLeOne
    · simp only [bad, dif_neg hqueryIndex, pmfProb_false]
      exact le_of_lt heta
  let invariant : ℕ → Bool → Bool → Prop := fun _ noUpper flag =>
    flag = false → noUpper = true
  have hinitial : ∀ state ∈ (PMF.pure true : PMF Bool).support, invariant 0 state false := by
    intro state hstate
    simp only [PMF.mem_support_iff, PMF.pure_apply] at hstate
    simpa [invariant] using hstate
  have hadvance : ∀ queryIndex state flag outcome,
      invariant queryIndex state flag →
      invariant (queryIndex + 1) (advance queryIndex state outcome)
        (flag || decide (bad queryIndex state outcome)) := by
    intro queryIndex state flag outcome hinvariant
    by_cases hqueryIndex : queryIndex < candidates.card
    · simp only [invariant, advance, canonicalFreshFinalCheckAdvance, dif_pos hqueryIndex,
        bad, Bool.or_eq_false_iff, decide_eq_false_iff_not]
      intro hflag
      have hstate : state = true := hinvariant hflag.1
      have hlower : adaptiveCompare
          (canonicalComparisonBatchObservation (fixedSampleBudget lower upper eta))
          (fixedSampleBudget lower upper eta) lower upper eta outcome = .lower :=
        Classical.not_not.mp hflag.2
      simp [hstate, hlower]
    · simp only [invariant, advance, canonicalFreshFinalCheckAdvance, dif_neg hqueryIndex,
        bad, Bool.or_eq_false_iff, decide_false]
      intro hflag
      exact hinvariant hflag.1
  let stateLaw := adaptiveQueryStateLaw (PMF.pure true) outcomeLaw advance bad candidates.card
  have hsuccess := adaptiveQuerySuccessProbability_ge_one_sub_sum
    (PMF.pure true) outcomeLaw advance bad (fun _ => eta) hfailure candidates.card
  have hsuccess' : 1 - (candidates.card : ℝ) * eta ≤
      pmfProb stateLaw (fun stateFailure => stateFailure.2 = false) := by
    simpa only [stateLaw, Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hsuccess
  have hinvariantSupport := adaptiveQueryStateLaw_support_invariant
    (PMF.pure true) outcomeLaw advance bad invariant hinitial hadvance
  have hflagLeState : pmfProb stateLaw (fun stateFailure => stateFailure.2 = false) ≤
      pmfProb stateLaw (fun stateFailure => stateFailure.1 = true) := by
    calc
      pmfProb stateLaw (fun stateFailure => stateFailure.2 = false) =
          pmfProb stateLaw (fun stateFailure =>
            stateFailure.2 = false ∧ stateFailure.1 = true) :=
        pmfProb_eq_of_support_iff stateLaw _ _ (by
          intro stateFailure hsupport
          constructor
          · intro hflag
            exact ⟨hflag, hinvariantSupport candidates.card stateFailure hsupport hflag⟩
          · exact fun hstateFailure => hstateFailure.1)
      _ ≤ pmfProb stateLaw (fun stateFailure => stateFailure.1 = true) := by
        apply pmfProb_le_of_imp
        intro stateFailure hsuccess
        exact hsuccess.2
  have hmap : stateLaw.map Prod.fst =
      canonicalFreshFinalCheckNoUpperLaw anchor candidates preferenceGap hprobability lower upper eta := by
    simpa only [stateLaw, outcomeLaw, advance] using
      (adaptiveQueryStateLaw_map_fst_eq_activeLaw (PMF.pure true) outcomeLaw advance bad
        candidates.card)
  calc
    1 - (candidates.card : ℝ) * eta ≤
        pmfProb stateLaw (fun stateFailure => stateFailure.2 = false) := hsuccess'
    _ ≤ pmfProb stateLaw (fun stateFailure => stateFailure.1 = true) := hflagLeState
    _ = pmfProb (stateLaw.map Prod.fst) (fun noUpper => noUpper = true) := by
      symm
      exact pmfProb_map _ _ _
    _ = pmfProb (canonicalFreshFinalCheckNoUpperLaw anchor candidates preferenceGap hprobability
      lower upper eta) (fun noUpper => noUpper = true) := by rw [hmap]

/-- If all final comparisons should return lower, the concrete final loop
returns the anchor except with the sum of its per-call failure budgets. -/
theorem canonicalFreshFinalCheck_anchor_probability_of_all_lower
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (anchor fallback : Arm) (candidates : Finset Arm)
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (lower upper eta : ℝ)
    (hbelow : ∀ candidate ∈ candidates, preferenceGap candidate anchor ≤ lower)
    (hseparation : lower < upper) (heta : 0 < eta) (hetaLeOne : eta ≤ 1) :
    1 - (candidates.card : ℝ) * eta ≤
      pmfProbClassical
        (canonicalFreshFinalCheckOutputLaw anchor fallback candidates preferenceGap hprobability
          lower upper eta)
        (fun output => output = anchor) := by
  classical
  rw [pmfProbClassical_eq_pmfProb]
  have hnoUpper := canonicalFreshFinalCheck_noUpper_probability_of_all_lower
    anchor candidates preferenceGap hprobability lower upper eta hbelow hseparation heta hetaLeOne
  calc
    1 - (candidates.card : ℝ) * eta ≤
        pmfProb (canonicalFreshFinalCheckNoUpperLaw anchor candidates preferenceGap hprobability
          lower upper eta) (fun noUpper => noUpper = true) := hnoUpper
    _ ≤ pmfProb (canonicalFreshFinalCheckNoUpperLaw anchor candidates preferenceGap hprobability
        lower upper eta) (fun noUpper => (if noUpper then anchor else fallback) = anchor) := by
      apply pmfProb_le_of_imp
      intro noUpper hnoUpper
      simp [hnoUpper]
    _ = pmfProb (canonicalFreshFinalCheckOutputLaw anchor fallback candidates preferenceGap
        hprobability lower upper eta) (fun output => output = anchor) := by
      symm
      exact pmfProb_map _ _ _

/--
If the anchor is already an `ε`-maximum at the final loop's lower threshold,
then the loop returns an `ε'`-maximum whenever no false upper decision is
made.  This is the first branch of Lemma 18.
-/
theorem canonicalFreshFinalCheck_epsilonMaximum_probability_of_anchor
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (anchor fallback : Arm) (candidates : Finset Arm)
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (epsilon lower upper eta : ℝ)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hanchor : EpsilonMaximum preferenceGap lower anchor) (hlowerLeEpsilon : lower ≤ epsilon)
    (hseparation : lower < upper) (heta : 0 < eta) (hetaLeOne : eta ≤ 1) :
    1 - (candidates.card : ℝ) * eta ≤
      pmfProbClassical (canonicalFreshFinalCheckOutputLaw anchor fallback candidates preferenceGap
        hprobability lower upper eta) (EpsilonMaximum preferenceGap epsilon) := by
  classical
  rw [pmfProbClassical_eq_pmfProb]
  have hbelow : ∀ candidate ∈ candidates, preferenceGap candidate anchor ≤ lower := by
    intro candidate hcandidate
    have hanchorBound := hanchor candidate
    rw [hantisymmetric candidate anchor] at hanchorBound
    linarith
  have hnoUpper := canonicalFreshFinalCheck_noUpper_probability_of_all_lower
    anchor candidates preferenceGap hprobability lower upper eta hbelow hseparation heta hetaLeOne
  have hanchorEpsilon : EpsilonMaximum preferenceGap epsilon anchor :=
    epsilonMaximum_mono preferenceGap lower epsilon anchor hanchor hlowerLeEpsilon
  calc
    1 - (candidates.card : ℝ) * eta ≤
        pmfProb (canonicalFreshFinalCheckNoUpperLaw anchor candidates preferenceGap hprobability
          lower upper eta) (fun noUpper => noUpper = true) := hnoUpper
    _ ≤ pmfProb (canonicalFreshFinalCheckNoUpperLaw anchor candidates preferenceGap hprobability
        lower upper eta) (fun noUpper =>
          EpsilonMaximum preferenceGap epsilon (if noUpper then anchor else fallback)) := by
      apply pmfProb_le_of_imp
      intro noUpper hnoUpper
      simp [hnoUpper, hanchorEpsilon]
    _ = pmfProb (canonicalFreshFinalCheckOutputLaw anchor fallback candidates preferenceGap
        hprobability lower upper eta) (EpsilonMaximum preferenceGap epsilon) := by
      symm
      exact pmfProb_map _ _ _

/--
When a retained maximum clears its upper test, the actual final loop selects
the fallback.  Thus a fallback already known to be an `ε`-maximum remains
successful except for the fresh maximum-detection failure event.
-/
theorem canonicalFreshFinalCheck_epsilonMaximum_probability_of_retained_maximum
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (anchor fallback maximum : Arm) (candidates : Finset Arm)
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (epsilon lower upper eta : ℝ)
    (hmaximumMem : maximum ∈ candidates)
    (hfallback : EpsilonMaximum preferenceGap epsilon fallback)
    (hupperGap : upper ≤ preferenceGap maximum anchor)
    (hseparation : lower < upper) (heta : 0 < eta) (hetaLeOne : eta ≤ 1) :
    1 - (candidates.card : ℝ) * eta ≤
      pmfProbClassical (canonicalFreshFinalCheckOutputLaw anchor fallback candidates preferenceGap hprobability
        lower upper eta) (EpsilonMaximum preferenceGap epsilon) := by
  classical
  rw [pmfProbClassical_eq_pmfProb]
  obtain ⟨maximumIndex, hmaximumIndex, hmaximumAtIndex⟩ :=
    exists_finsetFinalCheckCandidate_eq_of_mem anchor maximum candidates hmaximumMem
  let outcomeLaw : AdaptiveOutcomeKernel Bool (Fin (fixedSampleBudget lower upper eta) → Bool) :=
    canonicalFreshFinalCheckOutcomeLaw anchor candidates preferenceGap hprobability lower upper eta
  let advance : AdaptiveStateUpdate Bool (Fin (fixedSampleBudget lower upper eta) → Bool) :=
    canonicalFreshFinalCheckAdvance candidates lower upper eta
  let bad : ℕ → Bool → (Fin (fixedSampleBudget lower upper eta) → Bool) → Prop :=
    fun queryIndex _ outcome => if hqueryIndex : queryIndex < candidates.card then
      finsetFinalCheckCandidate anchor candidates queryIndex = maximum ∧
        adaptiveCompare (canonicalComparisonBatchObservation (fixedSampleBudget lower upper eta))
          (fixedSampleBudget lower upper eta) lower upper eta outcome ≠ .upper
    else False
  have hfailure : ∀ queryIndex state,
      pmfProb (outcomeLaw queryIndex state) (bad queryIndex state) ≤ eta := by
    intro queryIndex state
    by_cases hqueryIndex : queryIndex < candidates.card
    · by_cases hcandidate : finsetFinalCheckCandidate anchor candidates queryIndex = maximum
      · simp only [bad, dif_pos hqueryIndex, hcandidate, true_and]
        rw [← pmfProbClassical_eq_pmfProb]
        change pmfProbClassical (canonicalComparisonBatchLaw preferenceGap hprobability
          (finsetFinalCheckCandidate anchor candidates queryIndex) anchor
          (fixedSampleBudget lower upper eta)) (fun outcome =>
            adaptiveCompare (canonicalComparisonBatchObservation
              (fixedSampleBudget lower upper eta)) (fixedSampleBudget lower upper eta)
              lower upper eta outcome ≠ .upper) ≤ eta
        rw [pmfProbClassical_eq_pmfProb, AppliedModelingLib.pmfProb_eq_toMeasure_real]
        apply finiteBatchAdaptiveCompare_upper_failure_probability_of_ceilingBudget
          (canonicalComparisonBatchLaw preferenceGap hprobability
            (finsetFinalCheckCandidate anchor candidates queryIndex) anchor
            (fixedSampleBudget lower upper eta)).toMeasure
          (canonicalComparisonBatchObservation (fixedSampleBudget lower upper eta))
          lower upper (preferenceGap (finsetFinalCheckCandidate anchor candidates queryIndex) anchor) eta
        · simpa using iIndepFun_canonicalComparisonBatchObservation preferenceGap hprobability
            (finsetFinalCheckCandidate anchor candidates queryIndex) anchor
            (fixedSampleBudget lower upper eta)
        · intro sampleIndex hsampleIndex
          exact measurable_canonicalComparisonBatchObservation
            (fixedSampleBudget lower upper eta) sampleIndex
        · intro sampleIndex hsampleIndex
          exact ae_canonicalComparisonBatchObservation_mem_Icc preferenceGap hprobability
            (finsetFinalCheckCandidate anchor candidates queryIndex) anchor
            (fixedSampleBudget lower upper eta) sampleIndex
        · intro sampleIndex hsampleIndex
          exact integral_canonicalComparisonBatchObservation_of_lt preferenceGap hprobability
            (finsetFinalCheckCandidate anchor candidates queryIndex) anchor
            (fixedSampleBudget lower upper eta) sampleIndex hsampleIndex
        · simpa [hcandidate] using hupperGap
        · exact hseparation
        · exact heta
        · exact hetaLeOne
      · simp only [bad, dif_pos hqueryIndex, hcandidate, false_and, pmfProb_false]
        exact le_of_lt heta
    · simp only [bad, dif_neg hqueryIndex, pmfProb_false]
      exact le_of_lt heta
  let invariant : ℕ → Bool → Bool → Prop := fun queryCount noUpper flag =>
    flag = false → maximumIndex < queryCount → noUpper = false
  have hinitial : ∀ state ∈ (PMF.pure true : PMF Bool).support, invariant 0 state false := by
    intro state hstate hflag hindex
    exact (Nat.not_lt_zero _ hindex).elim
  have hadvance : ∀ queryIndex state flag outcome,
      invariant queryIndex state flag →
      invariant (queryIndex + 1) (advance queryIndex state outcome)
        (flag || decide (bad queryIndex state outcome)) := by
    intro queryIndex state flag outcome hinvariant
    by_cases hqueryIndex : queryIndex < candidates.card
    · simp only [invariant, advance, canonicalFreshFinalCheckAdvance, dif_pos hqueryIndex,
        Bool.or_eq_false_iff, decide_eq_false_iff_not]
      rintro ⟨hflag, hnotBad⟩ hindex
      have hindexLe : maximumIndex ≤ queryIndex := Nat.le_of_lt_succ hindex
      rcases Nat.lt_or_eq_of_le hindexLe with hprior | hcurrent
      · have hstate : state = false := hinvariant hflag hprior
        simp [hstate]
      · have hupper : adaptiveCompare
          (canonicalComparisonBatchObservation (fixedSampleBudget lower upper eta))
          (fixedSampleBudget lower upper eta) lower upper eta outcome = .upper := by
          apply Classical.not_not.mp
          intro hnotUpper
          have hcandidate : finsetFinalCheckCandidate anchor candidates queryIndex = maximum := by
            rw [← hcurrent]
            exact hmaximumAtIndex
          apply hnotBad
          simp [bad, hqueryIndex, hcandidate, hnotUpper]
        simp [hupper]
    · simp only [invariant, advance, canonicalFreshFinalCheckAdvance, dif_neg hqueryIndex,
        Bool.or_eq_false_iff]
      rintro ⟨hflag, _⟩ hindex
      have hcardLe : candidates.card ≤ queryIndex := Nat.le_of_not_gt hqueryIndex
      have hprior : maximumIndex < queryIndex :=
        lt_of_lt_of_le hmaximumIndex hcardLe
      exact hinvariant hflag hprior
  let stateLaw := adaptiveQueryStateLaw (PMF.pure true) outcomeLaw advance bad candidates.card
  have hsuccess := adaptiveQuerySuccessProbability_ge_one_sub_sum
    (PMF.pure true) outcomeLaw advance bad (fun _ => eta) hfailure candidates.card
  have hsuccess' : 1 - (candidates.card : ℝ) * eta ≤
      pmfProb stateLaw (fun stateFailure => stateFailure.2 = false) := by
    simpa only [stateLaw, Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hsuccess
  have hinvariantSupport := adaptiveQueryStateLaw_support_invariant
    (PMF.pure true) outcomeLaw advance bad invariant hinitial hadvance
  have hflagLeNoUpper : pmfProb stateLaw (fun stateFailure => stateFailure.2 = false) ≤
      pmfProb stateLaw (fun stateFailure => stateFailure.1 = false) := by
    calc
      pmfProb stateLaw (fun stateFailure => stateFailure.2 = false) =
          pmfProb stateLaw (fun stateFailure =>
            stateFailure.2 = false ∧ stateFailure.1 = false) :=
        pmfProb_eq_of_support_iff stateLaw _ _ (by
          intro stateFailure hsupport
          constructor
          · intro hflag
            exact ⟨hflag, hinvariantSupport candidates.card stateFailure hsupport hflag
              hmaximumIndex⟩
          · exact fun hstateFailure => hstateFailure.1)
      _ ≤ pmfProb stateLaw (fun stateFailure => stateFailure.1 = false) := by
        apply pmfProb_le_of_imp
        intro stateFailure hsuccess
        exact hsuccess.2
  have hmap : stateLaw.map Prod.fst =
      canonicalFreshFinalCheckNoUpperLaw anchor candidates preferenceGap hprobability lower upper eta := by
    simpa only [stateLaw, outcomeLaw, advance] using
      (adaptiveQueryStateLaw_map_fst_eq_activeLaw (PMF.pure true) outcomeLaw advance bad
        candidates.card)
  calc
    1 - (candidates.card : ℝ) * eta ≤
        pmfProb stateLaw (fun stateFailure => stateFailure.2 = false) := hsuccess'
    _ ≤ pmfProb stateLaw (fun stateFailure => stateFailure.1 = false) := hflagLeNoUpper
    _ = pmfProb (stateLaw.map Prod.fst) (fun noUpper => noUpper = false) := by
      symm
      exact pmfProb_map _ _ _
    _ ≤ pmfProb (stateLaw.map Prod.fst) (fun noUpper =>
        EpsilonMaximum preferenceGap epsilon (if noUpper then anchor else fallback)) := by
      apply pmfProb_le_of_imp
      intro noUpper hnoUpper
      simp [hnoUpper, hfallback]
    _ = pmfProb (canonicalFreshFinalCheckOutputLaw anchor fallback candidates preferenceGap
        hprobability lower upper eta) (EpsilonMaximum preferenceGap epsilon) := by
      rw [hmap]
      symm
      exact pmfProb_map _ _ _

/--
The retained-maximum branch also covers an already adequate anchor: then both
possible final outputs are `ε`-maxima; otherwise SST makes the retained
absolute maximum clear the final upper threshold.
-/
theorem canonicalFreshFinalCheck_epsilonMaximum_probability_of_retained_maximum_or_anchor
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (anchor fallback maximum : Arm) (candidates : Finset Arm)
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (epsilon lower upper eta : ℝ)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap) (hepsilon : 0 ≤ epsilon)
    (hmaximum : AbsoluteMaximum preferenceGap maximum) (hmaximumMem : maximum ∈ candidates)
    (hfallback : EpsilonMaximum preferenceGap epsilon fallback)
    (hupperLeEpsilon : upper ≤ epsilon)
    (hseparation : lower < upper) (heta : 0 < eta) (hetaLeOne : eta ≤ 1) :
    1 - (candidates.card : ℝ) * eta ≤
      pmfProbClassical (canonicalFreshFinalCheckOutputLaw anchor fallback candidates preferenceGap
        hprobability lower upper eta) (EpsilonMaximum preferenceGap epsilon) := by
  classical
  rw [pmfProbClassical_eq_pmfProb]
  by_cases hanchor : EpsilonMaximum preferenceGap epsilon anchor
  · have hallOutputs : ∀ (noUpper : Bool),
        EpsilonMaximum preferenceGap epsilon (if noUpper then anchor else fallback) := by
      intro noUpper
      cases noUpper <;> simp [hanchor, hfallback]
    have hone := pmfProb_eq_one_of_forall
      (canonicalFreshFinalCheckNoUpperLaw anchor candidates preferenceGap hprobability lower upper eta)
      (fun noUpper => EpsilonMaximum preferenceGap epsilon
        (if noUpper then anchor else fallback)) hallOutputs
    calc
      1 - (candidates.card : ℝ) * eta ≤ 1 := by
        have hnonnegative : 0 ≤ (candidates.card : ℝ) * eta :=
          mul_nonneg (Nat.cast_nonneg _) (le_of_lt heta)
        linarith
      _ = pmfProb (canonicalFreshFinalCheckNoUpperLaw anchor candidates preferenceGap hprobability
          lower upper eta) (fun noUpper =>
            EpsilonMaximum preferenceGap epsilon (if noUpper then anchor else fallback)) := hone.symm
      _ = pmfProb (canonicalFreshFinalCheckOutputLaw anchor fallback candidates preferenceGap
          hprobability lower upper eta) (EpsilonMaximum preferenceGap epsilon) := by
        symm
        exact pmfProb_map _ _ _
  · have hgap : upper ≤ preferenceGap maximum anchor := by
      have hstrict := absoluteMaximum_gap_gt_of_not_epsilonMaximum preferenceGap epsilon
        hantisymmetric hsst hepsilon maximum anchor hmaximum hanchor
      exact hupperLeEpsilon.trans (le_of_lt hstrict)
    exact canonicalFreshFinalCheck_epsilonMaximum_probability_of_retained_maximum
      anchor fallback maximum candidates preferenceGap hprobability epsilon lower upper eta
      hmaximumMem hfallback hgap hseparation heta hetaLeOne

/--
Supplement Lemma 18 on the source-shaped conditional tail: if the fixed
anchor is already a `2ε/3`-maximum or the fixed retained set contains an
absolute maximum, the fresh Seq-Eliminate/final-check execution returns an
`ε`-maximum with the two `δ/4` failure allocations.
-/
theorem canonicalOptMaximizeTailSource_epsilonMaximum_probability
    {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (anchor : Arm) (candidates : Finset Arm)
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (epsilon delta : ℝ)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 < epsilon) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (hbranch : EpsilonMaximum preferenceGap (2 * epsilon / 3) anchor ∨
      ∃ maximum, AbsoluteMaximum preferenceGap maximum ∧ maximum ∈ candidates) :
    let _ : DecidableEq Arm := Classical.decEq Arm
    1 - delta / 2 ≤
      pmfProbClassical (canonicalOptMaximizeTailSourceLaw anchor candidates preferenceGap hprobability
        epsilon delta)
        (fun fallbackOutput => EpsilonMaximum preferenceGap epsilon fallbackOutput.2) := by
  classical
  dsimp only
  rw [pmfProbClassical_eq_pmfProb]
  let fallbackLaw : PMF Arm :=
    canonicalFreshFinsetSeqEliminateOutputLaw anchor candidates preferenceGap hprobability
      epsilon ((delta / 4) / (candidates.card : ℝ))
  let finalLaw : Arm → PMF Arm := fun fallback =>
    canonicalFreshFinalCheckOutputLaw anchor fallback candidates preferenceGap hprobability
      (2 * epsilon / 3) epsilon ((delta / 4) / (Fintype.card Arm : ℝ))
  have hcard : 0 < Fintype.card Arm := Fintype.card_pos_iff.mpr inferInstance
  have hcardReal : 0 < (Fintype.card Arm : ℝ) := by exact_mod_cast hcard
  have hfinalEta : 0 < (delta / 4) / (Fintype.card Arm : ℝ) := by positivity
  have hfinalEtaLeOne : (delta / 4) / (Fintype.card Arm : ℝ) ≤ 1 := by
    have hcardGeOne : 1 ≤ (Fintype.card Arm : ℝ) := by
      exact_mod_cast Nat.succ_le_iff.mpr hcard
    calc
      (delta / 4) / (Fintype.card Arm : ℝ) ≤ delta / 4 :=
        div_le_self (by positivity) hcardGeOne
      _ ≤ 1 := by linarith
  have hfinalSpent : (candidates.card : ℝ) *
      ((delta / 4) / (Fintype.card Arm : ℝ)) ≤ delta / 4 := by
    have hcandidates : (candidates.card : ℝ) ≤ (Fintype.card Arm : ℝ) := by
      exact_mod_cast Finset.card_le_univ candidates
    calc
      (candidates.card : ℝ) * ((delta / 4) / (Fintype.card Arm : ℝ)) ≤
          (Fintype.card Arm : ℝ) * ((delta / 4) / (Fintype.card Arm : ℝ)) := by
            gcongr
      _ = delta / 4 := by field_simp
  have hseparation : 2 * epsilon / 3 < epsilon := by linarith
  rcases hbranch with hanchor | ⟨maximum, hmaximum, hmaximumMem⟩
  · have hconditional : ∀ fallback, True →
        1 - delta / 4 ≤ pmfProb (finalLaw fallback)
          (EpsilonMaximum preferenceGap epsilon) := by
      intro fallback _
      have hphase := canonicalFreshFinalCheck_epsilonMaximum_probability_of_anchor
        anchor fallback candidates preferenceGap hprobability epsilon (2 * epsilon / 3) epsilon
        ((delta / 4) / (Fintype.card Arm : ℝ)) hantisymmetric hanchor
        (le_of_lt hseparation) hseparation hfinalEta hfinalEtaLeOne
      rw [pmfProbClassical_eq_pmfProb] at hphase
      change 1 - delta / 4 ≤ pmfProb (finalLaw fallback)
        (EpsilonMaximum preferenceGap epsilon)
      linarith
    have hstate : 1 - 0 ≤ pmfProb fallbackLaw (fun _ => True) := by
      rw [pmfProb_eq_one_of_forall fallbackLaw (fun _ => True) (fun _ => trivial)]
      norm_num
    have hjoint := pmfProb_bind_map_pair_joint_ge_one_sub fallbackLaw finalLaw
      (fun _ => True) (fun _ output => EpsilonMaximum preferenceGap epsilon output)
      0 (delta / 4) (by positivity) (by positivity) (by linarith) hstate hconditional
    change 1 - delta / 2 ≤ pmfProb
      (fallbackLaw.bind fun fallback => (finalLaw fallback).map fun output => (fallback, output))
      (fun fallbackOutput => EpsilonMaximum preferenceGap epsilon fallbackOutput.2)
    calc
      1 - delta / 2 ≤ 1 - (0 + delta / 4) := by linarith
      _ ≤ pmfProb
          (fallbackLaw.bind fun fallback => (finalLaw fallback).map fun output => (fallback, output))
          (fun fallbackOutput => True ∧
            EpsilonMaximum preferenceGap epsilon fallbackOutput.2) := hjoint
      _ ≤ _ := by
        apply pmfProb_le_of_imp
        intro fallbackOutput hsuccess
        exact hsuccess.2
  · have hfallback :=
      canonicalFreshFinsetSeqEliminate_epsilonMaximum_probability_of_sourceSchedule
        anchor candidates preferenceGap hprobability epsilon (delta / 4) hantisymmetric hself hsst
        hepsilon (by positivity) (by linarith) maximum hmaximum hmaximumMem
    unfold canonicalFreshFinsetSeqEliminateEpsilonMaximumProbability at hfallback
    rw [pmfProbClassical_eq_pmfProb] at hfallback
    have hconditional : ∀ fallback, EpsilonMaximum preferenceGap epsilon fallback →
        1 - delta / 4 ≤ pmfProb (finalLaw fallback)
          (EpsilonMaximum preferenceGap epsilon) := by
      intro fallback hfallbackGood
      have hphase :=
        canonicalFreshFinalCheck_epsilonMaximum_probability_of_retained_maximum_or_anchor
          anchor fallback maximum candidates preferenceGap hprobability epsilon (2 * epsilon / 3)
          epsilon ((delta / 4) / (Fintype.card Arm : ℝ)) hantisymmetric hsst
          (le_of_lt hepsilon) hmaximum hmaximumMem hfallbackGood le_rfl hseparation hfinalEta
          hfinalEtaLeOne
      rw [pmfProbClassical_eq_pmfProb] at hphase
      change 1 - delta / 4 ≤ pmfProb (finalLaw fallback)
        (EpsilonMaximum preferenceGap epsilon)
      linarith
    have hjoint := pmfProb_bind_map_pair_joint_ge_one_sub fallbackLaw finalLaw
      (EpsilonMaximum preferenceGap epsilon)
      (fun _ output => EpsilonMaximum preferenceGap epsilon output)
      (delta / 4) (delta / 4) (by positivity) (by positivity) (by linarith)
      (by simpa only [fallbackLaw] using hfallback) hconditional
    change 1 - delta / 2 ≤ pmfProb
      (fallbackLaw.bind fun fallback => (finalLaw fallback).map fun output => (fallback, output))
      (fun fallbackOutput => EpsilonMaximum preferenceGap epsilon fallbackOutput.2)
    calc
      1 - delta / 2 = 1 - (delta / 4 + delta / 4) := by ring
      _ ≤ pmfProb
          (fallbackLaw.bind fun fallback => (finalLaw fallback).map fun output => (fallback, output))
          (fun fallbackOutput => EpsilonMaximum preferenceGap epsilon fallbackOutput.1 ∧
            EpsilonMaximum preferenceGap epsilon fallbackOutput.2) := hjoint
      _ ≤ _ := by
        apply pmfProb_le_of_imp
        intro fallbackOutput hsuccess
        exact hsuccess.2

/--
The four-phase finite PMF for OPT-Maximize.  The first coordinate retains the
realized Pick-Anchor, Prune, and fallback execution; the final coordinate is
the fresh final-check output sampled conditionally on that realized history.
-/
noncomputable def optMaximizeAnchorPruneFallbackFinalLaw
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (anchorLaw : PMF Arm) (pruneLaw : Arm → PMF (Finset Arm))
    (fallbackLaw : Arm → Finset Arm → PMF Arm)
    (finalLaw : Arm → Finset Arm → Arm → PMF Arm) :
    PMF (((Arm × Finset Arm) × Arm) × Arm) :=
  (optMaximizeAnchorPruneFallbackLaw anchorLaw pruneLaw fallbackLaw).bind fun anchorCandidatesFallback =>
    (finalLaw anchorCandidatesFallback.1.1 anchorCandidatesFallback.1.2
      anchorCandidatesFallback.2).map fun output => (anchorCandidatesFallback, output)

/-- Erasing the final output preserves the actual dependent three-phase PMF. -/
theorem optMaximizeAnchorPruneFallbackFinalLaw_map_fst_eq
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (anchorLaw : PMF Arm) (pruneLaw : Arm → PMF (Finset Arm))
    (fallbackLaw : Arm → Finset Arm → PMF Arm)
    (finalLaw : Arm → Finset Arm → Arm → PMF Arm) :
    (optMaximizeAnchorPruneFallbackFinalLaw anchorLaw pruneLaw fallbackLaw finalLaw).map
      (fun anchorCandidatesFallbackOutput => anchorCandidatesFallbackOutput.1) =
      optMaximizeAnchorPruneFallbackLaw anchorLaw pruneLaw fallbackLaw := by
  unfold optMaximizeAnchorPruneFallbackFinalLaw
  rw [PMF.map_bind]
  simp_rw [PMF.map_comp]
  change (optMaximizeAnchorPruneFallbackLaw anchorLaw pruneLaw fallbackLaw).bind
    (fun anchorCandidatesFallback =>
      (finalLaw anchorCandidatesFallback.1.1 anchorCandidatesFallback.1.2
        anchorCandidatesFallback.2).map (Function.const Arm anchorCandidatesFallback)) =
      optMaximizeAnchorPruneFallbackLaw anchorLaw pruneLaw fallbackLaw
  simp

/--
Compose a high-probability prior branch event with a uniform fresh final-check
success guarantee, retaining the dependence of each final law on its realized
prior trajectory.
-/
theorem optMaximizeAnchorPruneFallbackFinalLaw_success_probability_ge_one_sub_add
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (anchorLaw : PMF Arm) (pruneLaw : Arm → PMF (Finset Arm))
    (fallbackLaw : Arm → Finset Arm → PMF Arm)
    (finalLaw : Arm → Finset Arm → Arm → PMF Arm)
    (priorSuccess : (Arm × Finset Arm) × Arm → Prop)
    (outputSuccess : Arm → Finset Arm → Arm → Arm → Prop)
    (priorFailure finalFailure : ℝ) (hfinalFailureNonnegative : 0 ≤ finalFailure)
    [DecidablePred priorSuccess]
    [∀ anchor candidates fallback output,
      Decidable (outputSuccess anchor candidates fallback output)]
    (hprior : 1 - priorFailure ≤
      pmfProb (optMaximizeAnchorPruneFallbackLaw anchorLaw pruneLaw fallbackLaw) priorSuccess)
    (hfinal : ∀ anchorCandidatesFallback,
      priorSuccess anchorCandidatesFallback →
      1 - finalFailure ≤
        pmfProb (finalLaw anchorCandidatesFallback.1.1 anchorCandidatesFallback.1.2
          anchorCandidatesFallback.2)
          (outputSuccess anchorCandidatesFallback.1.1 anchorCandidatesFallback.1.2
            anchorCandidatesFallback.2)) :
    1 - (priorFailure + finalFailure) ≤
      pmfProb (optMaximizeAnchorPruneFallbackFinalLaw anchorLaw pruneLaw fallbackLaw finalLaw)
        (fun anchorCandidatesFallbackOutput =>
          outputSuccess anchorCandidatesFallbackOutput.1.1.1
            anchorCandidatesFallbackOutput.1.1.2 anchorCandidatesFallbackOutput.1.2
            anchorCandidatesFallbackOutput.2) := by
  classical
  let priorLaw := optMaximizeAnchorPruneFallbackLaw anchorLaw pruneLaw fallbackLaw
  let law := optMaximizeAnchorPruneFallbackFinalLaw anchorLaw pruneLaw fallbackLaw finalLaw
  let priorBad : ((Arm × Finset Arm) × Arm) × Arm → Prop :=
    fun anchorCandidatesFallbackOutput => ¬ priorSuccess anchorCandidatesFallbackOutput.1
  let finalBad : ((Arm × Finset Arm) × Arm) × Arm → Prop :=
    fun anchorCandidatesFallbackOutput =>
      priorSuccess anchorCandidatesFallbackOutput.1 ∧
        ¬ outputSuccess anchorCandidatesFallbackOutput.1.1.1
          anchorCandidatesFallbackOutput.1.1.2 anchorCandidatesFallbackOutput.1.2
          anchorCandidatesFallbackOutput.2
  let success : ((Arm × Finset Arm) × Arm) × Arm → Prop :=
    fun anchorCandidatesFallbackOutput =>
      outputSuccess anchorCandidatesFallbackOutput.1.1.1
        anchorCandidatesFallbackOutput.1.1.2 anchorCandidatesFallbackOutput.1.2
        anchorCandidatesFallbackOutput.2
  have hpriorMarg : pmfProb law (fun anchorCandidatesFallbackOutput =>
      priorSuccess anchorCandidatesFallbackOutput.1) = pmfProb priorLaw priorSuccess := by
    calc
      pmfProb law (fun anchorCandidatesFallbackOutput =>
          priorSuccess anchorCandidatesFallbackOutput.1) =
          pmfProb (law.map (fun anchorCandidatesFallbackOutput =>
            anchorCandidatesFallbackOutput.1)) priorSuccess := by
              symm
              exact pmfProb_map _ _ _
      _ = pmfProb priorLaw priorSuccess := by
        dsimp only [law, priorLaw]
        rw [optMaximizeAnchorPruneFallbackFinalLaw_map_fst_eq]
  have hpriorBad : pmfProb law priorBad ≤ priorFailure := by
    change pmfProb law (fun anchorCandidatesFallbackOutput =>
      ¬ priorSuccess anchorCandidatesFallbackOutput.1) ≤ priorFailure
    rw [pmfProb_compl, hpriorMarg]
    linarith
  have hfinalBad : pmfProb law finalBad ≤ finalFailure := by
    change pmfProb
      (priorLaw.bind fun anchorCandidatesFallback =>
        (finalLaw anchorCandidatesFallback.1.1 anchorCandidatesFallback.1.2
          anchorCandidatesFallback.2).map fun output => (anchorCandidatesFallback, output))
      (fun anchorCandidatesFallbackOutput =>
        priorSuccess anchorCandidatesFallbackOutput.1 ∧
          ¬ outputSuccess anchorCandidatesFallbackOutput.1.1.1
            anchorCandidatesFallbackOutput.1.1.2 anchorCandidatesFallbackOutput.1.2
            anchorCandidatesFallbackOutput.2) ≤ finalFailure
    apply pmfProb_adaptiveStep_le_of_historywiseBound priorLaw
      (fun anchorCandidatesFallback => finalLaw anchorCandidatesFallback.1.1
        anchorCandidatesFallback.1.2 anchorCandidatesFallback.2)
      (fun anchorCandidatesFallback output =>
        priorSuccess anchorCandidatesFallback ∧
          ¬ outputSuccess anchorCandidatesFallback.1.1 anchorCandidatesFallback.1.2
            anchorCandidatesFallback.2 output)
      finalFailure
    intro anchorCandidatesFallback
    by_cases hsuccess : priorSuccess anchorCandidatesFallback
    · simp only [hsuccess, true_and]
      rw [pmfProb_compl]
      linarith [hfinal anchorCandidatesFallback hsuccess]
    · simp only [hsuccess, false_and, pmfProb_false]
      exact hfinalFailureNonnegative
  have hunion : pmfProb law (fun anchorCandidatesFallbackOutput =>
      priorBad anchorCandidatesFallbackOutput ∨ finalBad anchorCandidatesFallbackOutput) ≤
      priorFailure + finalFailure :=
    (pmfProb_or_le law priorBad finalBad).trans (add_le_add hpriorBad hfinalBad)
  have hcomplement : pmfProb law (fun anchorCandidatesFallbackOutput =>
      ¬ success anchorCandidatesFallbackOutput) ≤
      pmfProb law (fun anchorCandidatesFallbackOutput =>
        priorBad anchorCandidatesFallbackOutput ∨ finalBad anchorCandidatesFallbackOutput) := by
    apply pmfProb_le_of_imp
    intro anchorCandidatesFallbackOutput hfailure
    by_cases hpriorSuccess : priorSuccess anchorCandidatesFallbackOutput.1 <;>
      by_cases houtputSuccess : outputSuccess anchorCandidatesFallbackOutput.1.1.1
        anchorCandidatesFallbackOutput.1.1.2 anchorCandidatesFallbackOutput.1.2
        anchorCandidatesFallbackOutput.2 <;>
      simp [success, priorBad, finalBad, hpriorSuccess, houtputSuccess] at hfailure ⊢
  have hfailure : pmfProb law (fun anchorCandidatesFallbackOutput =>
      ¬ success anchorCandidatesFallbackOutput) ≤ priorFailure + finalFailure :=
    hcomplement.trans hunion
  change 1 - (priorFailure + finalFailure) ≤ pmfProb law success
  calc
    1 - (priorFailure + finalFailure) ≤
        1 - pmfProb law (fun anchorCandidatesFallbackOutput =>
          ¬ success anchorCandidatesFallbackOutput) := by linarith
    _ = pmfProb law success := by
      rw [pmfProb_compl]
      ring

/--
The concrete four-phase source PMF for Algorithm 3's non-base branch.  The
final Compare loop receives its own fresh Bernoulli batches only after the
realized anchor, retained set, and fallback output are known.
-/
noncomputable def canonicalOptMaximizeFinalSourceLaw
    {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (cutoff : ℕ)
    (anchorDelta pruneDelta fallbackDelta finalDelta pruneLower pruneUpper epsilon : ℝ)
    (maxBatch : ℕ) (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (hcutoff : 0 < cutoff) (hanchorDelta : 0 < anchorDelta)
    (hanchorDeltaLeOne : anchorDelta ≤ 1)
    (hbudget : ∀ round < Fintype.card Arm,
      fixedSampleBudget pruneLower pruneUpper (adaptivePruneRoundDelta pruneDelta round) ≤ maxBatch) :
    PMF (((Arm × Finset Arm) × Arm) × Arm) := by
  classical
  exact optMaximizeAnchorPruneFallbackFinalLaw
    (canonicalFreshPickAnchorSourceOutputLaw cutoff anchorDelta pruneLower preferenceGap hprobability
      hcutoff hanchorDelta hanchorDeltaLeOne)
    (fun anchor => freshStoppedPruneActiveLaw Finset.univ
      (canonicalFreshPruneOutcomeLaw preferenceGap hprobability (Fintype.card Arm) anchor
        pruneLower pruneUpper pruneDelta maxBatch hbudget)
      cutoff
      (canonicalFreshPruneDecision (Fintype.card Arm) pruneLower pruneUpper pruneDelta maxBatch hbudget)
      (Fintype.card Arm))
    (fun anchor candidates => canonicalFreshFinsetSeqEliminateOutputLaw anchor candidates
      preferenceGap hprobability epsilon (fallbackDelta / (candidates.card : ℝ)))
    (fun anchor candidates fallback => canonicalFreshFinalCheckOutputLaw anchor fallback candidates
      preferenceGap hprobability pruneUpper epsilon (finalDelta / (Fintype.card Arm : ℝ)))

/-- The target `ε`-maximum probability of the four-phase source PMF. -/
noncomputable def canonicalOptMaximizeFinalSourceEpsilonMaximumProbability
    {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (cutoff : ℕ)
    (anchorDelta pruneDelta fallbackDelta finalDelta pruneLower pruneUpper epsilon : ℝ)
    (maxBatch : ℕ) (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (hcutoff : 0 < cutoff) (hanchorDelta : 0 < anchorDelta)
    (hanchorDeltaLeOne : anchorDelta ≤ 1)
    (hbudget : ∀ round < Fintype.card Arm,
      fixedSampleBudget pruneLower pruneUpper (adaptivePruneRoundDelta pruneDelta round) ≤ maxBatch) : ℝ := by
  classical
  exact pmfProbClassical
    (canonicalOptMaximizeFinalSourceLaw cutoff anchorDelta pruneDelta fallbackDelta finalDelta
      pruneLower pruneUpper epsilon maxBatch preferenceGap hprobability hcutoff hanchorDelta
      hanchorDeltaLeOne hbudget)
    (fun anchorCandidatesFallbackOutput =>
      EpsilonMaximum preferenceGap epsilon anchorCandidatesFallbackOutput.2)

/--
Lemma 18's finite-PMF probability composition for the non-base branch of
Algorithm 3.  The four failure allocations are explicit and no phase
independence is assumed: each later PMF is sampled conditionally on its full
realized earlier trajectory.
-/
theorem canonicalOptMaximizeFinalSource_epsilonMaximum_probability
    {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (cutoff : ℕ)
    (anchorDelta pruneDelta fallbackDelta finalDelta pruneLower pruneUpper epsilon : ℝ)
    (maxBatch : ℕ) (preferenceGap : Arm → Arm → ℝ) (maximum : Arm)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (ranking : Fin (Fintype.card Arm) → Arm)
    (hranking : PreferenceRanking preferenceGap ranking)
    (hcutoff : 0 < cutoff) (hcutoffLeCard : cutoff ≤ Fintype.card Arm)
    (hanchorDelta : 0 < anchorDelta) (hanchorDeltaLeOne : anchorDelta ≤ 1)
    (hpruneLower : 0 < pruneLower)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hcomplete : PreferenceComplete preferenceGap)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hbudget : ∀ round < Fintype.card Arm,
      fixedSampleBudget pruneLower pruneUpper (adaptivePruneRoundDelta pruneDelta round) ≤ maxBatch)
    (hpruneUpperNonnegative : 0 ≤ pruneUpper)
    (hmaximumAbsolute : AbsoluteMaximum preferenceGap maximum)
    (hpruneSeparation : pruneLower < pruneUpper) (hpruneDelta : 0 < pruneDelta)
    (hpruneDeltaHalf : pruneDelta ≤ 1 / 2)
    (hcard : 2 ≤ Fintype.card Arm)
    (hpruneCutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
      Real.log (Fintype.card Arm : ℝ)) < (cutoff : ℝ))
    (hpruneDeltaLower : (cutoff : ℝ) / (Fintype.card Arm : ℝ) ≤ pruneDelta)
    (hepsilon : 0 < epsilon) (hfallbackDelta : 0 < fallbackDelta)
    (hfallbackDeltaLeOne : fallbackDelta ≤ 1)
    (hfinalSeparation : pruneUpper < epsilon) (hfinalDelta : 0 < finalDelta)
    (hfinalDeltaLeOne : finalDelta ≤ 1) :
    1 - (anchorDelta + pruneDelta + fallbackDelta + finalDelta) ≤
      canonicalOptMaximizeFinalSourceEpsilonMaximumProbability cutoff anchorDelta pruneDelta
        fallbackDelta finalDelta pruneLower pruneUpper epsilon maxBatch preferenceGap hprobability
        hcutoff hanchorDelta hanchorDeltaLeOne hbudget := by
  classical
  let anchorLaw : PMF Arm :=
    canonicalFreshPickAnchorSourceOutputLaw cutoff anchorDelta pruneLower preferenceGap hprobability
      hcutoff hanchorDelta hanchorDeltaLeOne
  let pruneLaw : Arm → PMF (Finset Arm) := fun anchor =>
    freshStoppedPruneActiveLaw Finset.univ
      (canonicalFreshPruneOutcomeLaw preferenceGap hprobability (Fintype.card Arm) anchor
        pruneLower pruneUpper pruneDelta maxBatch hbudget)
      cutoff
      (canonicalFreshPruneDecision (Fintype.card Arm) pruneLower pruneUpper pruneDelta maxBatch hbudget)
      (Fintype.card Arm)
  let fallbackLaw : Arm → Finset Arm → PMF Arm := fun anchor candidates =>
    canonicalFreshFinsetSeqEliminateOutputLaw anchor candidates preferenceGap hprobability epsilon
      (fallbackDelta / (candidates.card : ℝ))
  let finalLaw : Arm → Finset Arm → Arm → PMF Arm := fun anchor candidates fallback =>
    canonicalFreshFinalCheckOutputLaw anchor fallback candidates preferenceGap hprobability pruneUpper
      epsilon (finalDelta / (Fintype.card Arm : ℝ))
  let priorSuccess : (Arm × Finset Arm) × Arm → Prop := fun anchorCandidatesFallback =>
    EpsilonMaximum preferenceGap pruneUpper anchorCandidatesFallback.1.1 ∨
      (maximum ∈ anchorCandidatesFallback.1.2 ∧
        EpsilonMaximum preferenceGap epsilon anchorCandidatesFallback.2)
  let outputSuccess : Arm → Finset Arm → Arm → Arm → Prop :=
    fun _ _ _ output => EpsilonMaximum preferenceGap epsilon output
  have hprior := canonicalOptMaximizeAnchorPruneFallbackSource_branch_success_probability
    cutoff anchorDelta pruneDelta fallbackDelta epsilon pruneLower pruneUpper maxBatch preferenceGap
    maximum hprobability ranking hranking hcutoff hcutoffLeCard hanchorDelta hanchorDeltaLeOne
    hpruneLower hantisymmetric hself hcomplete hsst hbudget hpruneUpperNonnegative
    hmaximumAbsolute hpruneSeparation hpruneDelta hpruneDeltaHalf hcard hpruneCutoff
    hpruneDeltaLower hepsilon hfallbackDelta hfallbackDeltaLeOne
  have hcardPositiveNat : 0 < Fintype.card Arm := Fintype.card_pos_iff.mpr inferInstance
  have hcardPositive : 0 < (Fintype.card Arm : ℝ) := by exact_mod_cast hcardPositiveNat
  have heta : 0 < finalDelta / (Fintype.card Arm : ℝ) := div_pos hfinalDelta hcardPositive
  have hetaLeOne : finalDelta / (Fintype.card Arm : ℝ) ≤ 1 := by
    calc
      finalDelta / (Fintype.card Arm : ℝ) ≤ finalDelta :=
        div_le_self (le_of_lt hfinalDelta) (by
          exact_mod_cast (Nat.succ_le_iff.mpr hcardPositiveNat))
      _ ≤ 1 := hfinalDeltaLeOne
  have hfinalFailureNonnegative : 0 ≤ finalDelta := le_of_lt hfinalDelta
  have hfinal : ∀ anchorCandidatesFallback,
      priorSuccess anchorCandidatesFallback →
      1 - finalDelta ≤
        pmfProb (finalLaw anchorCandidatesFallback.1.1 anchorCandidatesFallback.1.2
          anchorCandidatesFallback.2)
          (outputSuccess anchorCandidatesFallback.1.1 anchorCandidatesFallback.1.2
            anchorCandidatesFallback.2) := by
    intro anchorCandidatesFallback hsuccess
    have hcardLe : anchorCandidatesFallback.1.2.card ≤ Fintype.card Arm :=
      Finset.card_le_univ _
    have hcost : (anchorCandidatesFallback.1.2.card : ℝ) *
        (finalDelta / (Fintype.card Arm : ℝ)) ≤ finalDelta := by
      calc
        (anchorCandidatesFallback.1.2.card : ℝ) *
            (finalDelta / (Fintype.card Arm : ℝ)) ≤
            (Fintype.card Arm : ℝ) * (finalDelta / (Fintype.card Arm : ℝ)) := by
              apply mul_le_mul_of_nonneg_right
                (by exact_mod_cast hcardLe)
                (le_of_lt heta)
        _ = finalDelta := by
          field_simp [ne_of_gt hcardPositive]
    rcases hsuccess with hanchor | ⟨hmaximumMem, hfallback⟩
    · have hphase := canonicalFreshFinalCheck_epsilonMaximum_probability_of_anchor
        anchorCandidatesFallback.1.1 anchorCandidatesFallback.2 anchorCandidatesFallback.1.2
        preferenceGap hprobability epsilon pruneUpper epsilon (finalDelta / (Fintype.card Arm : ℝ))
        hantisymmetric hanchor (le_of_lt hfinalSeparation) hfinalSeparation heta hetaLeOne
      change 1 - finalDelta ≤ pmfProb
        (canonicalFreshFinalCheckOutputLaw anchorCandidatesFallback.1.1 anchorCandidatesFallback.2
          anchorCandidatesFallback.1.2 preferenceGap hprobability pruneUpper epsilon
          (finalDelta / (Fintype.card Arm : ℝ)))
        (EpsilonMaximum preferenceGap epsilon)
      rw [pmfProbClassical_eq_pmfProb] at hphase
      linarith
    · have hphase := canonicalFreshFinalCheck_epsilonMaximum_probability_of_retained_maximum_or_anchor
        anchorCandidatesFallback.1.1 anchorCandidatesFallback.2 maximum anchorCandidatesFallback.1.2
        preferenceGap hprobability epsilon pruneUpper epsilon (finalDelta / (Fintype.card Arm : ℝ))
        hantisymmetric hsst (le_of_lt hepsilon) hmaximumAbsolute hmaximumMem hfallback le_rfl
        hfinalSeparation heta hetaLeOne
      change 1 - finalDelta ≤ pmfProb
        (canonicalFreshFinalCheckOutputLaw anchorCandidatesFallback.1.1 anchorCandidatesFallback.2
          anchorCandidatesFallback.1.2 preferenceGap hprobability pruneUpper epsilon
          (finalDelta / (Fintype.card Arm : ℝ)))
        (EpsilonMaximum preferenceGap epsilon)
      rw [pmfProbClassical_eq_pmfProb] at hphase
      linarith
  have hcompose := optMaximizeAnchorPruneFallbackFinalLaw_success_probability_ge_one_sub_add
    anchorLaw pruneLaw fallbackLaw finalLaw priorSuccess outputSuccess
    (anchorDelta + pruneDelta + fallbackDelta) finalDelta hfinalFailureNonnegative
    (by
      simpa only [priorSuccess, anchorLaw, pruneLaw, fallbackLaw] using hprior)
    hfinal
  unfold canonicalOptMaximizeFinalSourceEpsilonMaximumProbability
  rw [pmfProbClassical_eq_pmfProb]
  change 1 - (anchorDelta + pruneDelta + fallbackDelta + finalDelta) ≤
    pmfProb (optMaximizeAnchorPruneFallbackFinalLaw anchorLaw pruneLaw fallbackLaw finalLaw)
      (fun anchorCandidatesFallbackOutput =>
        EpsilonMaximum preferenceGap epsilon anchorCandidatesFallbackOutput.2)
  linarith

/--
Algorithm 3's `δ ≤ 1/n` base branch is exactly Seq-Eliminate on the whole
finite arm set, with the source's per-call allocation `δ / n`.
-/
noncomputable def canonicalOptMaximizeBaseSourceOutputLaw
    {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (epsilon delta : ℝ) : PMF Arm := by
  classical
  exact canonicalFreshFinsetSeqEliminateOutputLaw (Classical.choice inferInstance) Finset.univ
    preferenceGap hprobability epsilon (delta / (Fintype.card Arm : ℝ))

/-- The base-branch `ε`-maximum probability, kept classical at its public boundary. -/
noncomputable def canonicalOptMaximizeBaseSourceEpsilonMaximumProbability
    {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (epsilon delta : ℝ) : ℝ := by
  classical
  exact pmfProbClassical
    (canonicalOptMaximizeBaseSourceOutputLaw preferenceGap hprobability epsilon delta)
    (EpsilonMaximum preferenceGap epsilon)

/-- The literal `1-δ` source guarantee for Algorithm 3's Seq-Eliminate base branch. -/
theorem canonicalOptMaximizeBaseSource_epsilonMaximum_probability
    {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (epsilon delta : ℝ)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 < epsilon) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (maximum : Arm) (hmaximum : AbsoluteMaximum preferenceGap maximum) :
    1 - delta ≤ canonicalOptMaximizeBaseSourceEpsilonMaximumProbability
      preferenceGap hprobability epsilon delta := by
  classical
  let emptyFallback : Arm := Classical.choice inferInstance
  have hsource := canonicalFreshFinsetSeqEliminate_epsilonMaximum_probability_of_sourceSchedule
    emptyFallback Finset.univ preferenceGap hprobability epsilon delta hantisymmetric hself hsst
    hepsilon hdelta hdeltaLeOne maximum hmaximum (Finset.mem_univ maximum)
  unfold canonicalOptMaximizeBaseSourceEpsilonMaximumProbability
  rw [pmfProbClassical_eq_pmfProb]
  change 1 - delta ≤ pmfProb
    (canonicalFreshFinsetSeqEliminateOutputLaw emptyFallback Finset.univ preferenceGap hprobability
      epsilon (delta / (Fintype.card Arm : ℝ)))
    (EpsilonMaximum preferenceGap epsilon)
  unfold canonicalFreshFinsetSeqEliminateEpsilonMaximumProbability at hsource
  rw [pmfProbClassical_eq_pmfProb] at hsource
  simpa only [Finset.card_univ] using hsource

/--
The source Algorithm 3 as one finite PMF: its low-confidence branch is whole
set Seq-Eliminate, and otherwise it runs the four fresh conditional phases.
-/
noncomputable def canonicalOptMaximizeAlgorithmSourceOutputLaw
    {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (cutoff : ℕ) (pruneLower pruneUpper epsilon delta : ℝ) (maxBatch : ℕ)
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (hcutoff : 0 < cutoff)
    (hbudget : ∀ round < Fintype.card Arm,
      fixedSampleBudget pruneLower pruneUpper (adaptivePruneRoundDelta (delta / 4) round) ≤
        maxBatch) : PMF Arm := by
  classical
  if hbase : delta ≤ 1 / (Fintype.card Arm : ℝ) then
    exact canonicalOptMaximizeBaseSourceOutputLaw preferenceGap hprobability epsilon delta
  else
    exact (canonicalOptMaximizeFinalSourceLaw cutoff (delta / 4) (delta / 4) (delta / 4)
      (delta / 4) pruneLower pruneUpper epsilon maxBatch preferenceGap hprobability hcutoff
      (by linarith) (by linarith) hbudget).map fun anchorCandidatesFallbackOutput =>
        anchorCandidatesFallbackOutput.2

/-- The Algorithm-3 output's `ε`-maximum probability. -/
noncomputable def canonicalOptMaximizeAlgorithmSourceEpsilonMaximumProbability
    {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (cutoff : ℕ) (pruneLower pruneUpper epsilon delta : ℝ) (maxBatch : ℕ)
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (hcutoff : 0 < cutoff)
    (hbudget : ∀ round < Fintype.card Arm,
      fixedSampleBudget pruneLower pruneUpper (adaptivePruneRoundDelta (delta / 4) round) ≤
        maxBatch) : ℝ := by
  classical
  exact pmfProbClassical
    (canonicalOptMaximizeAlgorithmSourceOutputLaw cutoff pruneLower pruneUpper epsilon delta maxBatch
      preferenceGap hprobability hdelta hdeltaLeOne hcutoff hbudget)
    (EpsilonMaximum preferenceGap epsilon)

/--
The source correctness theorem for the one-law Algorithm-3 interface.  The
non-base branch retains the explicit finite stopped-Prune schedule premise
needed by the already formalized Lemma-15 bridge.
-/
theorem canonicalOptMaximizeAlgorithmSource_epsilonMaximum_probability
    {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (cutoff : ℕ) (pruneLower pruneUpper epsilon delta : ℝ) (maxBatch : ℕ)
    (preferenceGap : Arm → Arm → ℝ) (maximum : Arm)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (ranking : Fin (Fintype.card Arm) → Arm)
    (hranking : PreferenceRanking preferenceGap ranking)
    (hcutoff : 0 < cutoff) (hcutoffLeCard : cutoff ≤ Fintype.card Arm)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) (hpruneLower : 0 < pruneLower)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hcomplete : PreferenceComplete preferenceGap)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hbudget : ∀ round < Fintype.card Arm,
      fixedSampleBudget pruneLower pruneUpper (adaptivePruneRoundDelta (delta / 4) round) ≤
        maxBatch)
    (hpruneUpperNonnegative : 0 ≤ pruneUpper)
    (hmaximumAbsolute : AbsoluteMaximum preferenceGap maximum)
    (hpruneSeparation : pruneLower < pruneUpper)
    (hpruneDeltaLower : (cutoff : ℝ) / (Fintype.card Arm : ℝ) ≤ delta / 4)
    (hcard : 2 ≤ Fintype.card Arm)
    (hpruneCutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
      Real.log (Fintype.card Arm : ℝ)) < (cutoff : ℝ))
    (hepsilon : 0 < epsilon) (hfinalSeparation : pruneUpper < epsilon) :
    1 - delta ≤ canonicalOptMaximizeAlgorithmSourceEpsilonMaximumProbability cutoff pruneLower
      pruneUpper epsilon delta maxBatch preferenceGap hprobability hdelta hdeltaLeOne hcutoff hbudget := by
  classical
  unfold canonicalOptMaximizeAlgorithmSourceEpsilonMaximumProbability
  rw [pmfProbClassical_eq_pmfProb]
  unfold canonicalOptMaximizeAlgorithmSourceOutputLaw
  split
  · have hbase := canonicalOptMaximizeBaseSource_epsilonMaximum_probability
      preferenceGap hprobability epsilon delta hantisymmetric hself hsst hepsilon hdelta hdeltaLeOne
      maximum hmaximumAbsolute
    unfold canonicalOptMaximizeBaseSourceEpsilonMaximumProbability at hbase
    rw [pmfProbClassical_eq_pmfProb] at hbase
    exact hbase
  · have hphase := canonicalOptMaximizeFinalSource_epsilonMaximum_probability
      cutoff (delta / 4) (delta / 4) (delta / 4) (delta / 4) pruneLower pruneUpper epsilon
      maxBatch preferenceGap maximum hprobability ranking hranking hcutoff hcutoffLeCard
      (by linarith) (by linarith) hpruneLower hantisymmetric hself hcomplete hsst hbudget
      hpruneUpperNonnegative hmaximumAbsolute hpruneSeparation (by linarith) (by linarith)
      hcard hpruneCutoff hpruneDeltaLower hepsilon (by linarith) (by linarith)
      hfinalSeparation (by linarith) (by linarith)
    unfold canonicalOptMaximizeFinalSourceEpsilonMaximumProbability at hphase
    rw [pmfProbClassical_eq_pmfProb] at hphase
    rw [pmfProb_map]
    norm_num at hphase ⊢
    linarith

end FalahatgarEtAl2017MaxingRanking

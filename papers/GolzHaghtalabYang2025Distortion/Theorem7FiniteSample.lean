import AppliedModelingLib.Alignment.Welfare.PopulationPreferenceGame
import AppliedModelingLib.Foundations.Probability.FiniteKLOptimization
import GolzHaghtalabYang2025Distortion.Lemma10FiniteSample
import GolzHaghtalabYang2025Distortion.Theorem2Expected

/-!
# Finite-sample NLHF welfare bound

This module formalizes the deterministic and probabilistic finite-sample
steps in Appendix F.1 of Gölz--Haghtalab--Yang (2025).  The empirical game is
made antisymmetric directly from its two directed empirical win rates; this
is the exact payoff used in the source's `p_n(x ≻ y) - p_n(y ≻ x)` display.
-/

namespace GolzHaghtalabYang2025Distortion

open AppliedModelingLib
open AppliedModelingLib.Alignment.Welfare
open AppliedModelingLib.GameTheory.PreferenceGame
open AppliedModelingLib.Learning.HumanFeedback

noncomputable section

/-- The antisymmetric preference game induced by arbitrary empirical directed
win rates in `[0,1]`.  Its centered payoff is half the empirical rate
difference, so its constrained maximin policies are exactly the empirical
NLHF policies of Appendix F.1. -/
def theorem7EmpiricalPreference
    {Alternative : Type*}
    (empiricalRate : Alternative → Alternative → ℝ)
    (hempirical_nonneg : ∀ first second, 0 ≤ empiricalRate first second)
    (hempirical_le_one : ∀ first second, empiricalRate first second ≤ 1) :
    PairwisePreference PUnit.{1} Alternative where
  prob _ first second :=
    (1 : ℝ) / 2 + (empiricalRate first second - empiricalRate second first) / 2
  nonneg _ first second := by
    have hleft := hempirical_nonneg first second
    have hright := hempirical_le_one second first
    linarith
  le_one _ first second := by
    have hleft := hempirical_le_one first second
    have hright := hempirical_nonneg second first
    linarith
  complementary _ first second := by ring

/-- The singleton-context payoff of `theorem7EmpiricalPreference` is one half
plus one half of the source empirical directed-rate margin. -/
theorem theorem7_empiricalPreferenceGamePayoff_eq_half_add_half_margin
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (empiricalRate : Alternative → Alternative → ℝ)
    (hempirical_nonneg : ∀ first second, 0 ≤ empiricalRate first second)
    (hempirical_le_one : ∀ first second, empiricalRate first second ≤ 1)
    (firstPolicy secondPolicy : PMF Alternative) :
    preferenceGamePayoff (PMF.pure PUnit.unit.{1})
        (theorem7EmpiricalPreference empiricalRate hempirical_nonneg hempirical_le_one)
        (contextFreeAlternativePolicy firstPolicy)
        (contextFreeAlternativePolicy secondPolicy) =
      (1 : ℝ) / 2 +
        pmfPairExp firstPolicy secondPolicy
          (fun first second => empiricalRate first second - empiricalRate second first) / 2 := by
  unfold preferenceGamePayoff policyPreference
  rw [pmfExp_pure]
  change pmfPairExp firstPolicy secondPolicy
      (fun first second => (1 : ℝ) / 2 +
        (empiricalRate first second - empiricalRate second first) / 2) = _
  have hkernel : (fun first second => (1 : ℝ) / 2 +
      (empiricalRate first second - empiricalRate second first) / 2) =
      fun first second => (1 : ℝ) / 2 + (1 : ℝ) / 2 *
        (empiricalRate first second - empiricalRate second first) := by
    funext first second
    ring
  rw [hkernel]
  calc
    pmfPairExp firstPolicy secondPolicy (fun first second => (1 : ℝ) / 2 +
        (1 : ℝ) / 2 * (empiricalRate first second - empiricalRate second first)) =
      pmfPairExp firstPolicy secondPolicy (fun _ _ => (1 : ℝ) / 2) +
        pmfPairExp firstPolicy secondPolicy (fun first second => (1 : ℝ) / 2 *
          (empiricalRate first second - empiricalRate second first)) := by
        simpa only [Pi.add_apply] using
          (pmfPairExp_add firstPolicy secondPolicy (fun _ _ => (1 : ℝ) / 2)
            (fun first second => (1 : ℝ) / 2 *
              (empiricalRate first second - empiricalRate second first)))
    _ = (1 : ℝ) / 2 +
        pmfPairExp firstPolicy secondPolicy
          (fun first second => empiricalRate first second - empiricalRate second first) / 2 := by
        unfold pmfPairExp
        simp only [pmfExp_const, pmfExp_const_mul, pmfExp_sub]
        ring

/-- Every attained unit-KL maximin policy for the empirical Appendix-F.1 game
has nonnegative empirical directed-rate margin against every feasible
benchmark. -/
theorem theorem7_empiricalMaximin_margin_nonneg
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (empiricalRate : Alternative → Alternative → ℝ)
    (hempirical_nonneg : ∀ first second, 0 ≤ empiricalRate first second)
    (hempirical_le_one : ∀ first second, empiricalRate first second ≤ 1)
    (reference : PMF Alternative) (klBudget : ℝ) (policy benchmark : PMF Alternative)
    (hmaximin : IsFiniteKLPreferenceMaximin
      (theorem7EmpiricalPreference empiricalRate hempirical_nonneg hempirical_le_one)
      reference klBudget policy)
    (hbenchmark : finiteKLDivergence benchmark reference ≤ klBudget) :
    0 ≤ pmfPairExp policy benchmark
      (fun first second => empiricalRate first second - empiricalRate second first) := by
  have hequilibrium := finiteKLPreferenceMaximin_isConstrainedPreferenceGameEquilibrium
    (theorem7EmpiricalPreference empiricalRate hempirical_nonneg hempirical_le_one)
    reference klBudget policy hmaximin
  have hbenchmark_game : InContextAveragedKLBall (PMF.pure PUnit.unit.{1})
      (contextFreeAlternativePolicy reference) klBudget
      (contextFreeAlternativePolicy benchmark) := by
    unfold InContextAveragedKLBall
    rw [contextFree_contextAveragedPolicyKLDivergence]
    exact hbenchmark
  have hwin := hequilibrium.2 (contextFreeAlternativePolicy benchmark)
    (by simpa only [contextFreeAlternativePolicy] using hbenchmark_game)
  change (1 : ℝ) / 2 ≤ preferenceGamePayoff (PMF.pure PUnit.unit.{1})
    (theorem7EmpiricalPreference empiricalRate hempirical_nonneg hempirical_le_one)
    (contextFreeAlternativePolicy policy) (contextFreeAlternativePolicy benchmark) at hwin
  rw [theorem7_empiricalPreferenceGamePayoff_eq_half_add_half_margin
    empiricalRate hempirical_nonneg hempirical_le_one policy benchmark] at hwin
  linarith

/-- On a uniform empirical win-rate event, an attained empirical NLHF policy
has the source Theorem-7 welfare bound with its explicit additive error.  This
is Appendix F.1's deterministic payoff-perturbation step. -/
theorem theorem7_empiricalMaximin_welfare_lower_of_uniform_error
    {User Alternative : Type*} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (hutility : UnitIntervalUtilityProfile utility)
    {btScale : ℝ} (hbtScale : 0 < btScale)
    (empiricalRate : Alternative → Alternative → ℝ)
    (hempirical_nonneg : ∀ first second, 0 ≤ empiricalRate first second)
    (hempirical_le_one : ∀ first second, empiricalRate first second ≤ 1)
    (reference : PMF Alternative) (klBudget : ℝ) (policy benchmark : PMF Alternative)
    (hmaximin : IsFiniteKLPreferenceMaximin
      (theorem7EmpiricalPreference empiricalRate hempirical_nonneg hempirical_le_one)
      reference klBudget policy)
    (hbenchmark : finiteKLDivergence benchmark reference ≤ klBudget)
    (error : ℝ)
    (huniform : ∀ first second,
      |empiricalRate first second -
        (populationBradleyTerryPreference population utility btScale).prob PUnit.unit.{1} first second| ≤
        error) :
    (sigmoidChordSlope btScale / ((1 : ℝ) / 4)) *
        policyAverageUtility population utility benchmark -
        error / (btScale * ((1 : ℝ) / 4)) ≤
      policyAverageUtility population utility policy := by
  have hempirical_nonneg_margin := theorem7_empiricalMaximin_margin_nonneg
    empiricalRate hempirical_nonneg hempirical_le_one reference klBudget policy benchmark
    hmaximin hbenchmark
  have hpoint : ∀ first second,
      empiricalRate first second - empiricalRate second first ≤
        2 * ((populationBradleyTerryPreference population utility btScale).prob
          PUnit.unit.{1} first second - (1 : ℝ) / 2) + 2 * error := by
    intro first second
    have hforward := (abs_le.mp (huniform first second)).2
    have hreverse := (abs_le.mp (huniform second first)).1
    have hcomplementary :=
      (populationBradleyTerryPreference population utility btScale).complementary
        PUnit.unit.{1} first second
    linarith
  have hempirical_upper :
      pmfPairExp policy benchmark
        (fun first second => empiricalRate first second - empiricalRate second first) ≤
      2 * populationBradleyTerryPolicyMargin population utility btScale policy benchmark +
        2 * error := by
    calc
      pmfPairExp policy benchmark
          (fun first second => empiricalRate first second - empiricalRate second first) ≤
        pmfPairExp policy benchmark (fun first second =>
          2 * ((populationBradleyTerryPreference population utility btScale).prob
            PUnit.unit.{1} first second - (1 : ℝ) / 2) + 2 * error) := by
              unfold pmfPairExp
              apply pmfExp_le_pmfExp_of_forall_le
              intro first
              apply pmfExp_le_pmfExp_of_forall_le
              intro second
              exact hpoint first second
      _ = 2 * populationBradleyTerryPolicyMargin population utility btScale policy benchmark +
          2 * error := by
            unfold populationBradleyTerryPolicyMargin pmfPairExp
            simp only [pmfExp_add, pmfExp_const, pmfExp_const_mul]
  have hpopulation_margin :
      -error ≤ populationBradleyTerryPolicyMargin population utility btScale policy benchmark := by
    linarith
  have hlinearization := populationBradleyTerryPolicyMargin_upper_linearization_source
    population utility hutility hbtScale policy benchmark
  have hscaled :
      -error ≤ btScale *
        ((1 : ℝ) / 4 * policyAverageUtility population utility policy -
          sigmoidChordSlope btScale * policyAverageUtility population utility benchmark) :=
    hpopulation_margin.trans hlinearization
  have hlinear :
      sigmoidChordSlope btScale * policyAverageUtility population utility benchmark -
        error / btScale ≤
      (1 : ℝ) / 4 * policyAverageUtility population utility policy := by
    have hdivide : -error / btScale ≤
        (1 : ℝ) / 4 * policyAverageUtility population utility policy -
          sigmoidChordSlope btScale * policyAverageUtility population utility benchmark :=
      (div_le_iff₀ hbtScale).mpr (by
        nlinarith [hscaled])
    have hneg_div : -error / btScale = -(error / btScale) := by ring
    rw [hneg_div] at hdivide
    linarith
  have hquarter : (0 : ℝ) < (1 : ℝ) / 4 := by norm_num
  calc
    (sigmoidChordSlope btScale / ((1 : ℝ) / 4)) *
        policyAverageUtility population utility benchmark -
        error / (btScale * ((1 : ℝ) / 4)) =
      (sigmoidChordSlope btScale * policyAverageUtility population utility benchmark -
        error / btScale) / ((1 : ℝ) / 4) := by
          field_simp
    _ ≤ policyAverageUtility population utility policy :=
      (div_le_iff₀ hquarter).mpr (by simpa [mul_comm] using hlinear)

/-- A concrete empirical NLHF policy is selected from the attained finite
KL-ball maximin set for every literal iid-user sample. -/
noncomputable def theorem7IidUserEmpiricalPolicy
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {users comparisonsPerUser : ℕ}
    (reference : PMF Alternative) (klBudget : ℝ) (hbudget : 0 ≤ klBudget)
    (sample : Fin users →
      (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative))) : PMF Alternative :=
  Classical.choose (exists_finiteKLPreferenceMaximin
    (theorem7EmpiricalPreference
      (fun first second => theorem10IidUserPaperWinRate first second sample)
      (fun first second => theorem10IidUserPaperWinRate_nonneg first second sample)
      (fun first second => theorem10IidUserPaperWinRate_le_one first second sample))
    reference klBudget hbudget)

/-- The selected policy satisfies the literal empirical `argmax min`
condition, with no optimizer certificate left as a hypothesis. -/
theorem theorem7IidUserEmpiricalPolicy_isMaximin
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {users comparisonsPerUser : ℕ}
    (reference : PMF Alternative) (klBudget : ℝ) (hbudget : 0 ≤ klBudget)
    (sample : Fin users →
      (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative))) :
    IsFiniteKLPreferenceMaximin
      (theorem7EmpiricalPreference
        (fun first second => theorem10IidUserPaperWinRate first second sample)
        (fun first second => theorem10IidUserPaperWinRate_nonneg first second sample)
        (fun first second => theorem10IidUserPaperWinRate_le_one first second sample))
      reference klBudget
      (theorem7IidUserEmpiricalPolicy reference klBudget hbudget sample) :=
  Classical.choose_spec (exists_finiteKLPreferenceMaximin
    (theorem7EmpiricalPreference
      (fun first second => theorem10IidUserPaperWinRate first second sample)
      (fun first second => theorem10IidUserPaperWinRate_nonneg first second sample)
      (fun first second => theorem10IidUserPaperWinRate_le_one first second sample))
    reference klBudget hbudget)

/-- The literal iid-user empirical NLHF output obeys the finite Theorem-7
welfare inequality on any uniform empirical win-rate event. -/
theorem theorem7_iidUserEmpiricalPolicy_welfare_lower_of_uniform_error
    {User Alternative : Type*} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative]
    {users comparisonsPerUser : ℕ}
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (hutility : UnitIntervalUtilityProfile utility)
    {btScale : ℝ} (hbtScale : 0 < btScale)
    (reference : PMF Alternative) (klBudget : ℝ) (hbudget : 0 ≤ klBudget)
    (benchmark : PMF Alternative)
    (hbenchmark : finiteKLDivergence benchmark reference ≤ klBudget)
    (sample : Fin users →
      (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative)))
    (error : ℝ)
    (huniform : ∀ first second,
      |theorem10IidUserPaperWinRate first second sample -
        (populationBradleyTerryPreference population utility btScale).prob PUnit.unit.{1} first second| ≤
        error) :
    (sigmoidChordSlope btScale / ((1 : ℝ) / 4)) *
        policyAverageUtility population utility benchmark -
        error / (btScale * ((1 : ℝ) / 4)) ≤
      policyAverageUtility population utility
        (theorem7IidUserEmpiricalPolicy reference klBudget hbudget sample) := by
  exact theorem7_empiricalMaximin_welfare_lower_of_uniform_error
    population utility hutility hbtScale
    (fun first second => theorem10IidUserPaperWinRate first second sample)
    (fun first second => theorem10IidUserPaperWinRate_nonneg first second sample)
    (fun first second => theorem10IidUserPaperWinRate_le_one first second sample)
    reference klBudget (theorem7IidUserEmpiricalPolicy reference klBudget hbudget sample) benchmark
    (theorem7IidUserEmpiricalPolicy_isMaximin reference klBudget hbudget sample)
    hbenchmark error huniform

/-- The literal iid user-batch probability law used by Appendix D and F.1. -/
noncomputable def theorem7IidUserBatchLaw
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (responseLaw : PMF (theorem2UserResponseTable Alternative))
    (sampling : PMF Alternative) (users comparisonsPerUser : ℕ) :
    PMF (Fin users →
      (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative))) :=
  pmfProduct (Fin users)
    (theorem2UserResponseTable Alternative ×
      (Fin comparisonsPerUser → Alternative × Alternative))
    (pmfProd responseLaw
      (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
        (theorem2UserPairLabelLaw sampling)))

/-- The complement of the uniform Lemma-10 event for the empirical game used
by the finite-sample NLHF policy. -/
def theorem7IidUserUniformWinRateFailure
    {User Alternative : Type*} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative]
    {users comparisonsPerUser : ℕ}
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (btScale error : ℝ)
    (sample : Fin users →
      (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative))) : Prop :=
  ∃ pair : Alternative × Alternative,
    error < |theorem10IidUserPaperWinRate pair.1 pair.2 sample -
      (populationBradleyTerryPreference population utility btScale).prob PUnit.unit.{1}
        pair.1 pair.2|

/-- Probability of the literal Appendix-F.1 uniform empirical-rate failure. -/
noncomputable def theorem7IidUserUniformWinRateFailureProbability
    {User Alternative : Type*} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative]
    {users comparisonsPerUser : ℕ}
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (btScale error : ℝ)
    (responseLaw : PMF (theorem2UserResponseTable Alternative))
    (sampling : PMF Alternative) : ℝ := by
  classical
  exact pmfProb (theorem7IidUserBatchLaw responseLaw sampling users comparisonsPerUser)
    (theorem7IidUserUniformWinRateFailure population utility btScale error)

/-- On the complement of its explicit failure event, the finite Lemma-10
event provides the uniform error hypothesis needed by the deterministic
Appendix-F.1 payoff argument. -/
theorem theorem7_uniform_error_of_not_iidUserUniformWinRateFailure
    {User Alternative : Type*} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative]
    {users comparisonsPerUser : ℕ}
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (btScale error : ℝ)
    (sample : Fin users →
      (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative)))
    (hgood : ¬ theorem7IidUserUniformWinRateFailure population utility btScale error sample) :
    ∀ first second,
      |theorem10IidUserPaperWinRate first second sample -
        (populationBradleyTerryPreference population utility btScale).prob PUnit.unit.{1}
          first second| ≤ error := by
  intro first second
  by_contra hnot
  apply hgood
  exact ⟨(first, second), lt_of_not_ge hnot⟩

/-- A source-exact finite expectation step: any bound on the uniform empirical
rate failure event converts the deterministic NLHF inequality into a welfare
guarantee for the concrete empirical-maximin output. -/
theorem theorem7_iidUserExpectedWelfare_lower_of_uniform_tail
    {User Alternative : Type*} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative]
    {users comparisonsPerUser : ℕ}
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (hutility : UnitIntervalUtilityProfile utility)
    {btScale : ℝ} (hbtScale : 0 < btScale)
    (responseLaw : PMF (theorem2UserResponseTable Alternative))
    (sampling : PMF Alternative)
    (reference : PMF Alternative) (klBudget : ℝ) (hbudget : 0 ≤ klBudget)
    (benchmark : PMF Alternative)
    (hbenchmark : finiteKLDivergence benchmark reference ≤ klBudget)
    (error delta : ℝ)
    (htail : theorem7IidUserUniformWinRateFailureProbability
      (users := users) (comparisonsPerUser := comparisonsPerUser)
      population utility btScale error responseLaw sampling ≤ delta)
    (hdelta_le_one : delta ≤ 1) :
    (1 - delta) *
        ((sigmoidChordSlope btScale / ((1 : ℝ) / 4)) *
            policyAverageUtility population utility benchmark -
          error / (btScale * ((1 : ℝ) / 4))) ≤
      pmfExp (theorem7IidUserBatchLaw responseLaw sampling users comparisonsPerUser)
        (fun sample => policyAverageUtility population utility
          (theorem7IidUserEmpiricalPolicy reference klBudget hbudget sample)) := by
  classical
  letI : DecidablePred
      (theorem7IidUserUniformWinRateFailure (users := users)
        (comparisonsPerUser := comparisonsPerUser) population utility btScale error) :=
    Classical.decPred _
  have htail' : pmfProb (theorem7IidUserBatchLaw responseLaw sampling users comparisonsPerUser)
      (theorem7IidUserUniformWinRateFailure (users := users)
        (comparisonsPerUser := comparisonsPerUser) population utility btScale error) ≤ delta := by
    simpa [theorem7IidUserUniformWinRateFailureProbability] using htail
  apply pmfExp_ge_one_sub_prob_mul_of_nonneg_on_good
    (theorem7IidUserBatchLaw responseLaw sampling users comparisonsPerUser)
    (fun sample => ¬ theorem7IidUserUniformWinRateFailure population utility btScale error sample)
    (fun sample => policyAverageUtility population utility
      (theorem7IidUserEmpiricalPolicy reference klBudget hbudget sample))
    _ delta
  · intro sample
    exact policyAverageUtility_nonneg population utility
      (theorem7IidUserEmpiricalPolicy reference klBudget hbudget sample) hutility
  · intro sample hgood
    exact theorem7_iidUserEmpiricalPolicy_welfare_lower_of_uniform_error
      population utility hutility hbtScale reference klBudget hbudget benchmark hbenchmark sample error
      (theorem7_uniform_error_of_not_iidUserUniformWinRateFailure
        population utility btScale error sample hgood)
  · simpa only [not_not] using htail'
  · exact hdelta_le_one

/-- The literal Appendix-D Lemma-10 tail composed with Appendix F.1.  This is
the finite-sample Theorem-7 guarantee before the source's final `O(·)`
notation and confidence-budget choice. -/
theorem theorem7_iidUserExpectedWelfare_lower_of_literal_tail
    {User Alternative : Type*} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative]
    {users comparisonsPerUser : ℕ}
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (hutility : UnitIntervalUtilityProfile utility)
    {btScale : ℝ} (hbtScale : 0 < btScale)
    (responseLaw : PMF (theorem2UserResponseTable Alternative))
    (preference : PairwisePreference PUnit.{1} Alternative)
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (sampling : PMF Alternative)
    (husers_pos : 0 < users) (hcomparisons_pos : 0 < comparisonsPerUser)
    (hsampling_pos : ∀ alternative, 0 < (sampling alternative).toReal)
    (reference : PMF Alternative) (klBudget : ℝ) (hbudget : 0 ≤ klBudget)
    (benchmark : PMF Alternative)
    (hbenchmark : finiteKLDivergence benchmark reference ≤ klBudget)
    (error delta : ℝ) (herror_nonneg : 0 ≤ error)
    (htail_sum : ∑ pair ∈ (Finset.univ : Finset Alternative).offDiag,
      theorem10FixedPairRateTailBound sampling users comparisonsPerUser
        pair.1 pair.2 error ≤ delta)
    (hdelta_le_one : delta ≤ 1)
    (hpreference : preference = populationBradleyTerryPreference population utility btScale) :
    (1 - delta) *
        ((sigmoidChordSlope btScale / ((1 : ℝ) / 4)) *
            policyAverageUtility population utility benchmark -
          error / (btScale * ((1 : ℝ) / 4))) ≤
      pmfExp (theorem7IidUserBatchLaw responseLaw sampling users comparisonsPerUser)
        (fun sample => policyAverageUtility population utility
          (theorem7IidUserEmpiricalPolicy reference klBudget hbudget sample)) := by
  classical
  letI : DecidablePred
      (theorem7IidUserUniformWinRateFailure (users := users)
        (comparisonsPerUser := comparisonsPerUser) population utility btScale error) :=
    Classical.decPred _
  have htail := theorem10_iidUserPaperWinRate_uniform_tail_bound
    hcalibrated sampling users comparisonsPerUser husers_pos hcomparisons_pos hsampling_pos
    error herror_nonneg
  have htail' : theorem7IidUserUniformWinRateFailureProbability
      (users := users) (comparisonsPerUser := comparisonsPerUser)
      population utility btScale error responseLaw sampling ≤ delta := by
    rw [hpreference] at htail
    have htail_failure : theorem7IidUserUniformWinRateFailureProbability
        (users := users) (comparisonsPerUser := comparisonsPerUser)
        population utility btScale error responseLaw sampling ≤
        ∑ pair ∈ (Finset.univ : Finset Alternative).offDiag,
          theorem10FixedPairRateTailBound sampling users comparisonsPerUser
            pair.1 pair.2 error := by
      let law := theorem7IidUserBatchLaw responseLaw sampling users comparisonsPerUser
      have hevent : pmfProb law
          (theorem7IidUserUniformWinRateFailure population utility btScale error) =
          pmfProb law (fun sample => ∃ first second,
            error < |theorem10IidUserPaperWinRate first second sample -
              (populationBradleyTerryPreference population utility btScale).prob
                PUnit.unit.{1} first second|) := by
        apply pmfProb_congr
        intro sample
        constructor
        · rintro ⟨⟨first, second⟩, hbad⟩
          exact ⟨first, second, hbad⟩
        · rintro ⟨first, second, hbad⟩
          exact ⟨(first, second), hbad⟩
      calc
        theorem7IidUserUniformWinRateFailureProbability
            population utility btScale error responseLaw sampling =
            pmfProb law (theorem7IidUserUniformWinRateFailure
              population utility btScale error) := by
                simp [theorem7IidUserUniformWinRateFailureProbability, law]
        _ = pmfProb law (fun sample => ∃ first second,
            error < |theorem10IidUserPaperWinRate first second sample -
              (populationBradleyTerryPreference population utility btScale).prob
                PUnit.unit.{1} first second|) := hevent
        _ ≤ ∑ pair ∈ (Finset.univ : Finset Alternative).offDiag,
            theorem10FixedPairRateTailBound sampling users comparisonsPerUser
              pair.1 pair.2 error := by
                simpa [law, theorem7IidUserBatchLaw] using htail
    exact htail_failure.trans htail_sum
  exact theorem7_iidUserExpectedWelfare_lower_of_uniform_tail
    population utility hutility hbtScale responseLaw sampling reference klBudget hbudget benchmark
    hbenchmark error delta htail' hdelta_le_one

/-- The finite KL ball contains an attained welfare-maximizing benchmark. -/
theorem theorem7_exists_welfareMaximizingBenchmark
    {User Alternative : Type*} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (reference : PMF Alternative) (klBudget : ℝ) (hbudget : 0 ≤ klBudget) :
    ∃ benchmark : PMF Alternative,
      finiteKLDivergence benchmark reference ≤ klBudget ∧
      ∀ other : PMF Alternative, finiteKLDivergence other reference ≤ klBudget →
        policyAverageUtility population utility other ≤
          policyAverageUtility population utility benchmark := by
  obtain ⟨benchmark, hbenchmark, hmax⟩ := exists_finiteKL_maximizer
    reference klBudget hbudget (populationAverageUtility population utility)
  refine ⟨benchmark, ?_, ?_⟩
  · simpa only [finiteKLBall] using hbenchmark
  · intro other hother
    simpa only [policyAverageUtility] using hmax other (by
      simpa only [finiteKLBall] using hother)

/-- Source-facing finite Theorem-7 endpoint before big-O notation: the literal
iid empirical NLHF output is compared to an attained welfare maximum on the
same KL ball, with the explicit Lemma-10 failure probability and error term. -/
theorem theorem7_iidUserExpectedWelfare_exists_optimalBenchmark_lower_of_literal_tail
    {User Alternative : Type*} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative]
    {users comparisonsPerUser : ℕ}
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (hutility : UnitIntervalUtilityProfile utility)
    {btScale : ℝ} (hbtScale : 0 < btScale)
    (responseLaw : PMF (theorem2UserResponseTable Alternative))
    (preference : PairwisePreference PUnit.{1} Alternative)
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (sampling : PMF Alternative)
    (husers_pos : 0 < users) (hcomparisons_pos : 0 < comparisonsPerUser)
    (hsampling_pos : ∀ alternative, 0 < (sampling alternative).toReal)
    (reference : PMF Alternative) (klBudget : ℝ) (hbudget : 0 ≤ klBudget)
    (error delta : ℝ) (herror_nonneg : 0 ≤ error)
    (htail_sum : ∑ pair ∈ (Finset.univ : Finset Alternative).offDiag,
      theorem10FixedPairRateTailBound sampling users comparisonsPerUser
        pair.1 pair.2 error ≤ delta)
    (hdelta_le_one : delta ≤ 1)
    (hpreference : preference = populationBradleyTerryPreference population utility btScale) :
    ∃ benchmark : PMF Alternative,
      finiteKLDivergence benchmark reference ≤ klBudget ∧
      (∀ other : PMF Alternative, finiteKLDivergence other reference ≤ klBudget →
        policyAverageUtility population utility other ≤
          policyAverageUtility population utility benchmark) ∧
      (1 - delta) *
          ((sigmoidChordSlope btScale / ((1 : ℝ) / 4)) *
              policyAverageUtility population utility benchmark -
            error / (btScale * ((1 : ℝ) / 4))) ≤
        pmfExp (theorem7IidUserBatchLaw responseLaw sampling users comparisonsPerUser)
          (fun sample => policyAverageUtility population utility
            (theorem7IidUserEmpiricalPolicy reference klBudget hbudget sample)) := by
  obtain ⟨benchmark, hbenchmark, hmax⟩ :=
    theorem7_exists_welfareMaximizingBenchmark population utility reference klBudget hbudget
  refine ⟨benchmark, hbenchmark, hmax, ?_⟩
  exact theorem7_iidUserExpectedWelfare_lower_of_literal_tail
    population utility hutility hbtScale responseLaw preference hcalibrated sampling
    husers_pos hcomparisons_pos hsampling_pos reference klBudget hbudget benchmark hbenchmark
    error delta herror_nonneg htail_sum hdelta_le_one hpreference

/--
Closed-form finite-sample Theorem 7.  This composes Lemma 10's explicit
minimum-mass rate with the empirical maximin welfare argument, rather than
leaving an arbitrary tail bound as a premise of the source-facing result.
-/
theorem theorem7_iidUserExpectedWelfare_exists_optimalBenchmark_lower_of_sourceRate
    {User Alternative : Type*} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative]
    {users comparisonsPerUser : ℕ}
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (hutility : UnitIntervalUtilityProfile utility)
    {btScale : ℝ} (hbtScale : 0 < btScale)
    (responseLaw : PMF (theorem2UserResponseTable Alternative))
    (preference : PairwisePreference PUnit.{1} Alternative)
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (sampling : PMF Alternative)
    (husers_pos : 0 < users) (hcomparisons_pos : 0 < comparisonsPerUser)
    (minimumMass : ℝ) (hminimumMass_pos : 0 < minimumMass)
    (hminimumMass : ∀ alternative, minimumMass ≤ (sampling alternative).toReal)
    (reference : PMF Alternative) (klBudget : ℝ) (hbudget : 0 ≤ klBudget)
    (delta failureBudget : ℝ)
    (hfailureBudget_pos : 0 < failureBudget)
    (hfailureBudget_le_one : failureBudget ≤ 1)
    (hdenominator_failure : ∀ pair ∈ (Finset.univ : Finset Alternative).offDiag,
      2 * Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) *
        theorem10FixedPairIncidenceProbability sampling pair.1 pair.2 / 8) ≤ failureBudget)
    (hbudget_sum : ∑ pair ∈ (Finset.univ : Finset Alternative).offDiag,
      failureBudget ≤ delta)
    (hdelta_le_one : delta ≤ 1)
    (hpreference : preference = populationBradleyTerryPreference population utility btScale) :
    ∃ benchmark : PMF Alternative,
      finiteKLDivergence benchmark reference ≤ klBudget ∧
      (∀ other : PMF Alternative, finiteKLDivergence other reference ≤ klBudget →
        policyAverageUtility population utility other ≤
          policyAverageUtility population utility benchmark) ∧
      (1 - delta) *
          ((sigmoidChordSlope btScale / ((1 : ℝ) / 4)) *
              policyAverageUtility population utility benchmark -
            theorem10SourceRate users comparisonsPerUser minimumMass failureBudget /
              (btScale * ((1 : ℝ) / 4))) ≤
        pmfExp (theorem7IidUserBatchLaw responseLaw sampling users comparisonsPerUser)
          (fun sample => policyAverageUtility population utility
            (theorem7IidUserEmpiricalPolicy reference klBudget hbudget sample)) := by
  obtain ⟨benchmark, hbenchmark, hmax⟩ :=
    theorem7_exists_welfareMaximizingBenchmark population utility reference klBudget hbudget
  let error := theorem10SourceRate users comparisonsPerUser minimumMass failureBudget
  subst preference
  have htail_raw := theorem10_iidUserPaperWinRate_uniform_minMass_confidence
    hcalibrated sampling users comparisonsPerUser minimumMass delta failureBudget
    husers_pos hcomparisons_pos hminimumMass_pos hminimumMass
    hfailureBudget_pos hfailureBudget_le_one hdenominator_failure hbudget_sum
  have htail : theorem7IidUserUniformWinRateFailureProbability
      (users := users) (comparisonsPerUser := comparisonsPerUser)
      population utility btScale error responseLaw sampling ≤ delta := by
    unfold theorem7IidUserUniformWinRateFailureProbability
      theorem7IidUserUniformWinRateFailure
    simpa [theorem7IidUserBatchLaw, error, theorem10SourceRate] using htail_raw
  refine ⟨benchmark, hbenchmark, hmax, ?_⟩
  exact theorem7_iidUserExpectedWelfare_lower_of_uniform_tail
    population utility hutility hbtScale responseLaw sampling reference klBudget hbudget
    benchmark hbenchmark error delta htail hdelta_le_one

/--
Source-shaped confidence form of finite-sample Theorem 7.  As in source
Lemma 10, the theorem exposes one global failure probability and fixes the
per-pair union-bound allocation internally.
-/
theorem theorem7_iidUserExpectedWelfare_exists_optimalBenchmark_lower_of_sourceConfidence
    {User Alternative : Type*} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative] [Nonempty Alternative]
    {users comparisonsPerUser : ℕ}
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (hutility : UnitIntervalUtilityProfile utility)
    {btScale : ℝ} (hbtScale : 0 < btScale)
    (responseLaw : PMF (theorem2UserResponseTable Alternative))
    (preference : PairwisePreference PUnit.{1} Alternative)
    (hcalibrated : theorem2UserResponseCalibrated responseLaw preference)
    (sampling : PMF Alternative)
    (husers_pos : 0 < users) (hcomparisons_pos : 0 < comparisonsPerUser)
    (minimumMass : ℝ) (hminimumMass_pos : 0 < minimumMass)
    (hminimumMass : ∀ alternative, minimumMass ≤ (sampling alternative).toReal)
    (reference : PMF Alternative) (klBudget : ℝ) (hbudget : 0 ≤ klBudget)
    (delta : ℝ) (hdelta_pos : 0 < delta) (hdelta_le_one : delta ≤ 1)
    (hsource_failure :
      (Fintype.card Alternative : ℝ) ^ 2 *
          Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) * minimumMass ^ 2 / 8) ≤
        delta)
    (hpreference : preference = populationBradleyTerryPreference population utility btScale) :
    let failureBudget := delta / (Fintype.card Alternative : ℝ) ^ 2
    ∃ benchmark : PMF Alternative,
      finiteKLDivergence benchmark reference ≤ klBudget ∧
      (∀ other : PMF Alternative, finiteKLDivergence other reference ≤ klBudget →
        policyAverageUtility population utility other ≤
          policyAverageUtility population utility benchmark) ∧
      (1 - delta) *
          ((sigmoidChordSlope btScale / ((1 : ℝ) / 4)) *
              policyAverageUtility population utility benchmark -
            theorem10SourceRate users comparisonsPerUser minimumMass failureBudget /
              (btScale * ((1 : ℝ) / 4))) ≤
        pmfExp (theorem7IidUserBatchLaw responseLaw sampling users comparisonsPerUser)
          (fun sample => policyAverageUtility population utility
            (theorem7IidUserEmpiricalPolicy reference klBudget hbudget sample)) := by
  let failureBudget := delta / (Fintype.card Alternative : ℝ) ^ 2
  obtain ⟨benchmark, hbenchmark, hmax⟩ :=
    theorem7_exists_welfareMaximizingBenchmark population utility reference klBudget hbudget
  let error := theorem10SourceRate users comparisonsPerUser minimumMass failureBudget
  subst preference
  have htail_raw := theorem10_iidUserPaperWinRate_uniform_source_confidence
    hcalibrated sampling users comparisonsPerUser minimumMass delta
    husers_pos hcomparisons_pos hminimumMass_pos hminimumMass
    hdelta_pos hdelta_le_one hsource_failure
  have htail : theorem7IidUserUniformWinRateFailureProbability
      (users := users) (comparisonsPerUser := comparisonsPerUser)
      population utility btScale error responseLaw sampling ≤ delta := by
    unfold theorem7IidUserUniformWinRateFailureProbability
      theorem7IidUserUniformWinRateFailure
    simpa [theorem7IidUserBatchLaw, error, failureBudget, theorem10SourceRate] using htail_raw
  refine ⟨benchmark, hbenchmark, hmax, ?_⟩
  exact theorem7_iidUserExpectedWelfare_lower_of_uniform_tail
    population utility hutility hbtScale responseLaw sampling reference klBudget hbudget
    benchmark hbenchmark error delta htail hdelta_le_one

end

end GolzHaghtalabYang2025Distortion

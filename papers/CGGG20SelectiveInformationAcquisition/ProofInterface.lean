import CGGG20SelectiveInformationAcquisition.PaperInterface

import CGGG20SelectiveInformationAcquisition.ProofBridge



namespace CGGG20SelectiveInformationAcquisition

namespace PaperInterface

open MeasureTheory
open AppliedModelingLib.Decision
open AppliedModelingLib.Optimization
open AppliedModelingLib.Probability
open CGGG20SelectiveInformationAcquisition.ProofBridge
open scoped BigOperators
noncomputable section

/-! ## Main-text threshold result -/

theorem definition1_threshold_policy_realizes_spec
    {Applicant Outcome Group : Type*} [Fintype Applicant] [Fintype Group]
    [MeasurableSpace Outcome]
    (D : paper_measure_group_allocation_data Applicant Outcome Group)
    (threshold : Group → RealThreshold) (alpha : Group → ℝ)
    (policy : MeasureGroupAllocationData.AllocationPolicy Applicant Outcome) : CGGG20SelectiveInformationAcquisition.ProofBridge.paper_main_text_groupwise_threshold_policy (Applicant := Applicant) (Outcome := Outcome) (Group := Group) (D := D) (threshold := threshold) (alpha := alpha) (policy := policy) ↔ definition1_threshold_policySpec (Applicant := Applicant) (Outcome := Outcome) (Group := Group) (D := D) (threshold := threshold) (alpha := alpha) (policy := policy) := by
  classical
  rfl

private theorem legacy_theorem1_allocation_slice_realizes_spec :
    ∀ {Applicant Outcome Group : Type*} [Fintype Applicant]
      [MeasurableSpace Outcome] [Fintype Group] [DecidableEq Group]
      (D : paper_measure_group_allocation_data Applicant Outcome Group)
      [IsFiniteMeasure D.law]
      (actualUtility : Applicant → Outcome → ℝ)
      (hactual_utility_eq_posterior :
        ∀ policy : MeasureGroupAllocationData.AllocationPolicy Applicant Outcome,
          MeasureGroupAllocationData.AllocationPolicyMeasurable policy →
            (∀ item outcome, 0 ≤ policy item outcome ∧ policy item outcome ≤ 1) →
              (∫ outcome,
                ∑ item : Applicant, policy item outcome * actualUtility item outcome ∂D.law) =
                  D.expectedPosteriorUtility policy)
      (hactual_group_utility_eq_posterior :
        ∀ (g : Group) (policy : MeasureGroupAllocationData.AllocationPolicy Applicant Outcome),
          MeasureGroupAllocationData.AllocationPolicyMeasurable policy →
            (∀ item outcome, 0 ≤ policy item outcome ∧ policy item outcome ≤ 1) →
              (∫ outcome,
                ∑ item : Applicant,
                  if D.group item = g then policy item outcome * actualUtility item outcome else 0 ∂D.law) =
                  D.expectedGroupPosteriorUtility g policy)
      (c : ℝ) (hc : 0 < c) (hcost : ∀ item, D.allocCost item = c)
      (budget : ℝ) (diversityTarget : Group → ℝ)
      (original : MeasureGroupAllocationData.AllocationPolicy Applicant Outcome)
      (horiginal : _),
      legacy_theorem1_allocation_sliceSpec D actualUtility
        hactual_utility_eq_posterior hactual_group_utility_eq_posterior c hc hcost
        budget diversityTarget original horiginal := by
  intro Applicant Outcome Group _ _ _ _ D _ actualUtility hactual_utility_eq_posterior
    hactual_group_utility_eq_posterior c hc hcost budget diversityTarget original horiginal
  have horiginal_source :
      paper_measure_group_allocation_optimal D budget diversityTarget original := by
    change D.SourceOptimal budget diversityTarget original
    refine ⟨?_, ?_⟩
    · refine ⟨horiginal.1, horiginal.2.1, horiginal.2.2.1, ?_⟩
      intro g
      rw [← hactual_group_utility_eq_posterior g original horiginal.2.1 horiginal.1]
      exact horiginal.2.2.2.1 g
    · intro other hother
      rw [← hactual_utility_eq_posterior other hother.2.1 hother.1,
        ← hactual_utility_eq_posterior original horiginal.2.1 horiginal.1]
      apply horiginal.2.2.2.2 other
      refine ⟨hother.1, hother.2.1, hother.2.2.1, ?_⟩
      intro g
      rw [hactual_group_utility_eq_posterior g other hother.2.1 hother.1]
      exact hother.2.2.2 g
  rcases CGGG20SelectiveInformationAcquisition.ProofBridge.paper_main_text_threshold_policies_suffice
      D c hc hcost budget diversityTarget original horiginal_source with
    ⟨threshold, alpha, replacement, hthreshold, hoptimal⟩
  refine ⟨threshold, alpha, replacement, hthreshold,
    hoptimal.1.1, hoptimal.1.2.1, hoptimal.1.2.2.1, ?_, ?_⟩
  · intro g
    rw [hactual_group_utility_eq_posterior g replacement hoptimal.1.2.1 hoptimal.1.1]
    exact hoptimal.1.2.2.2 g
  · intro other hother
    rw [hactual_utility_eq_posterior other hother.2.1 hother.1,
      hactual_utility_eq_posterior replacement hoptimal.1.2.1 hoptimal.1.1]
    apply hoptimal.2 other
    refine ⟨hother.1, hother.2.1, hother.2.2.1, ?_⟩
    intro g
    rw [← hactual_group_utility_eq_posterior g other hother.2.1 hother.1]
    exact hother.2.2.2 g

/-- Theorem 1 realized at the source's full screening-and-allocation pair level. -/
theorem theorem1_threshold_policies_suffice :
    ∀ {Applicant Outcome Group : Type*} [Fintype Applicant]
      [MeasurableSpace Outcome] [Fintype Group]
      (D : paper_screening_allocation_data Applicant Outcome Group)
      (screeningCost : ℝ) (hscreenCost : ∀ item, D.screenCost item = screeningCost)
      (c : ℝ) (hc : 0 < c)
      (budget : ℝ) (hbudget_nonneg : 0 ≤ budget)
      (diversityTarget : Group → ℝ)
      (hdiversityTarget_nonneg : ∀ g, 0 ≤ diversityTarget g)
      (original : paper_screening_allocation_pair D)
      (hcost : ∀ item, D.allocCost item = c)
      (horiginal : _),
      theorem1_threshold_policies_sufficeSpec
        D screeningCost hscreenCost c hc budget hbudget_nonneg diversityTarget
        hdiversityTarget_nonneg original hcost horiginal := by
  intro Applicant Outcome Group _ _ _ D screeningCost hscreenCost c hc budget hbudget_nonneg diversityTarget
    hdiversityTarget_nonneg original hcost horiginal
  classical
  change D.PairActualOptimal budget diversityTarget original at horiginal
  have horiginal_source : D.PairSourceOptimal budget diversityTarget original :=
    (D.pairActualOptimal_iff_pairSourceOptimal budget diversityTarget original).mp horiginal
  rcases paper_main_text_threshold_policy_pairs_suffice
      D c hc budget diversityTarget original hcost horiginal_source with
    ⟨threshold, alpha, replacement, hscreening, hthreshold, hreplaced⟩
  unfold theorem1_threshold_policies_sufficeSpec
  have hactual : D.PairActualOptimal budget diversityTarget replacement :=
    (D.pairActualOptimal_iff_pairSourceOptimal
      budget diversityTarget replacement).mpr hreplaced
  exact ⟨threshold, alpha, replacement, hscreening, hthreshold,
    hactual.1.1, hactual.1.2.1, hactual.1.2.2.1,
    (by simpa only [hscreening] using hactual.1.2.2.2.1),
    (by simpa only [hscreening] using hactual.1.2.2.2.2),
    (by simpa only [hscreening] using hactual.2)⟩

/-! ## Main-text LP formulas -/

theorem equation_obj_fixed_threshold_utility
    {Applicant Group : Type*} [Fintype Applicant]
    (D : paper_fixed_threshold_data Applicant Group) (p : Applicant → ℝ)
    (hprobability : D.screeningProbabilityBounds p) :
    equation_obj_fixed_threshold_utilitySpec
      (Applicant := Applicant) (Group := Group) (D := D) (p := p)
      hprobability := by
  exact CGGG20SelectiveInformationAcquisition.ProofBridge.paper_equation_obj_source_formula (Applicant := Applicant) (Group := Group) (D := D) (p := p)

theorem equation_constr1_fixed_threshold_budget
    {Applicant Group : Type*} [Fintype Applicant]
    (D : paper_fixed_threshold_data Applicant Group) (p : Applicant → ℝ)
    (hprobability : D.screeningProbabilityBounds p) :
    equation_constr1_fixed_threshold_budgetSpec
      (Applicant := Applicant) (Group := Group) (D := D) (p := p)
      hprobability := by
  exact CGGG20SelectiveInformationAcquisition.ProofBridge.paper_equation_constr1_source_formula (Applicant := Applicant) (Group := Group) (D := D) (p := p)

theorem equation_constr2_fixed_threshold_diversity
    {Applicant Group : Type*} [Fintype Applicant] [Fintype Group]
    (D : paper_fixed_threshold_data Applicant Group) (g : Group)
    (p : Applicant → ℝ) (hprobability : D.screeningProbabilityBounds p) :
    equation_constr2_fixed_threshold_diversitySpec
      (Applicant := Applicant) (Group := Group) (D := D) (g := g) (p := p)
      hprobability := by
  classical
  exact CGGG20SelectiveInformationAcquisition.ProofBridge.paper_equation_constr2_source_formula (Applicant := Applicant) (Group := Group) (D := D) (g := g) (p := p)

/-! ## Appendix threshold results -/

theorem definition3_cost_aware_threshold_policy_realizes_spec
    {Applicant Outcome Group : Type*} [Fintype Applicant] [Fintype Group]
    [MeasurableSpace Outcome]
    (D : paper_measure_group_allocation_data Applicant Outcome Group)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (threshold : Group → paper_cost_aware_extended_threshold)
    (alpha : Group → ℝ)
    (policy : MeasureGroupAllocationData.AllocationPolicy Applicant Outcome) : CGGG20SelectiveInformationAcquisition.ProofBridge.paper_cost_aware_groupwise_threshold_policy (Applicant := Applicant) (Outcome := Outcome) (Group := Group) (D := D) (threshold := threshold) (alpha := alpha) (policy := policy) ↔ definition3_cost_aware_threshold_policySpec (Applicant := Applicant) (Outcome := Outcome) (Group := Group) (D := D) hcost_pos threshold alpha policy := by
  classical
  rfl

private theorem expected_single_threshold_uses_full_posterior
    {Applicant Outcome : Type*} [Fintype Applicant]
    (D : ExpectedCostAwareData Applicant Outcome)
    (t alpha : ℝ)
    (threshold : ExpectedCostAwareData.AllocationPolicy Applicant Outcome)
    (hthreshold :
      paper_expected_single_cost_aware_threshold_policy D t alpha threshold) :
    allocationPolicyUsesFullPosterior D.posteriorUtility threshold := by
  intro item x y hvector
  rcases hthreshold with ⟨_, _, hcases⟩
  have hitem : D.posteriorUtility item x = D.posteriorUtility item y :=
    congrFun hvector item
  rcases lt_trichotomy (D.posteriorUtility item x / D.allocCost item) t with hlt | heq | hgt
  · have hylt : D.posteriorUtility item y / D.allocCost item < t := by
      rw [← hitem]
      exact hlt
    rw [(hcases item x).2.2 hlt, (hcases item y).2.2 hylt]
  · have hyeq : D.posteriorUtility item y / D.allocCost item = t := by
      rw [← hitem]
      exact heq
    rw [(hcases item x).2.1 heq, (hcases item y).2.1 hyeq]
  · have hygt : t < D.posteriorUtility item y / D.allocCost item := by
      rw [← hitem]
      exact hgt
    rw [(hcases item x).1 hgt, (hcases item y).1 hygt]

private theorem measure_single_threshold_uses_full_posterior
    {Applicant Outcome : Type*} [Fintype Applicant]
    [MeasurableSpace Outcome]
    (D : MeasureCostAwareData Applicant Outcome)
    (threshold : paper_cost_aware_extended_threshold) (alpha : ℝ)
    (policy : MeasureCostAwareData.AllocationPolicy Applicant Outcome)
    (hthreshold :
      paper_measure_single_cost_aware_threshold_policy D threshold alpha policy) :
    allocationPolicyUsesFullPosterior D.posteriorUtility policy := by
  intro item x y hvector
  rcases hthreshold with ⟨_, _, hcases⟩
  have hitem : D.posteriorUtility item x = D.posteriorUtility item y :=
    congrFun hvector item
  cases threshold with
  | negInf =>
      have hx : policy item x = 1 := by
        simpa using hcases item x
      have hy : policy item y = 1 := by
        simpa using hcases item y
      rw [hx, hy]
  | finite t =>
      rcases lt_trichotomy (D.posteriorUtility item x / D.allocCost item) t with hlt | heq | hgt
      · have hylt : D.posteriorUtility item y / D.allocCost item < t := by
          rw [← hitem]
          exact hlt
        rw [(hcases item x).2.2 hlt, (hcases item y).2.2 hylt]
      · have hyeq : D.posteriorUtility item y / D.allocCost item = t := by
          rw [← hitem]
          exact heq
        rw [(hcases item x).2.1 heq, (hcases item y).2.1 hyeq]
      · have hygt : t < D.posteriorUtility item y / D.allocCost item := by
          rw [← hitem]
          exact hgt
        rw [(hcases item x).1 hgt, (hcases item y).1 hygt]
  | posInf =>
      have hx : policy item x = 0 := by
        simpa using hcases item x
      have hy : policy item y = 0 := by
        simpa using hcases item y
      rw [hx, hy]

theorem lemma1_cost_aware_threshold_non_domination_realizes_spec : lemma1_cost_aware_threshold_non_dominationSpec := by
  unfold lemma1_cost_aware_threshold_non_dominationSpec
  constructor
  · intro Applicant Outcome _ D actualUtility hactual_utility_eq_posterior t alpha threshold other hcost_pos ht hthreshold hother hother_observed hcost
    have hthreshold_bounds :
        ExpectedCostAwareData.AllocationPolicyBounds threshold :=
      D.singleCostAwareThresholdPolicy_bounds t alpha threshold
        ((paper_expected_single_cost_aware_threshold_policy_iff D hcost_pos t alpha threshold).mp hthreshold)
    have hthreshold_observed :
        allocationPolicyUsesFullPosterior D.posteriorUtility threshold :=
      expected_single_threshold_uses_full_posterior D t alpha threshold hthreshold
    rw [hactual_utility_eq_posterior other hother_observed hother,
      hactual_utility_eq_posterior threshold hthreshold_observed hthreshold_bounds]
    exact D.singleCostAwareThreshold_expectedPosteriorUtility_ge_of_expectedCost_eq
      t alpha threshold other
      ((paper_expected_single_cost_aware_threshold_policy_iff D hcost_pos t alpha threshold).mp hthreshold)
      hother hcost
  · intro Applicant Outcome _ D actualUtility hactual_utility_eq_posterior t alpha threshold other hcost_pos ht hthreshold hother hother_observed hutility
    have hthreshold_bounds :
        ExpectedCostAwareData.AllocationPolicyBounds threshold :=
      D.singleCostAwareThresholdPolicy_bounds t alpha threshold
        ((paper_expected_single_cost_aware_threshold_policy_iff D hcost_pos t alpha threshold).mp hthreshold)
    have hthreshold_observed :
        allocationPolicyUsesFullPosterior D.posteriorUtility threshold :=
      expected_single_threshold_uses_full_posterior D t alpha threshold hthreshold
    have hposterior_utility :
        D.expectedPosteriorUtility threshold = D.expectedPosteriorUtility other := by
      rw [← hactual_utility_eq_posterior threshold hthreshold_observed hthreshold_bounds,
        ← hactual_utility_eq_posterior other hother_observed hother]
      exact hutility
    exact D.singleCostAwareThreshold_expectedCost_le_of_expectedPosteriorUtility_eq
      t alpha threshold other ht
      ((paper_expected_single_cost_aware_threshold_policy_iff D hcost_pos t alpha threshold).mp hthreshold)
      hother hposterior_utility

theorem lemma2_full_range_cost_aware_threshold_attainment_realizes_spec : lemma2_full_range_cost_aware_threshold_attainmentSpec := by
  unfold lemma2_full_range_cost_aware_threshold_attainmentSpec
  constructor
  · intro Applicant Outcome _ _ D _ actualUtility hactual_utility_eq_posterior Upsilon hcost_pos hUpsilon_pos hachievable
    rcases hachievable with ⟨original, horiginal_meas, horiginal_observed, horiginal_bounds, horiginal_utility⟩
    have horiginal_posterior_utility : D.expectedPosteriorUtility original = Upsilon := by
      rw [← hactual_utility_eq_posterior original horiginal_observed horiginal_bounds]
      exact horiginal_utility
    have horiginal_utility_nonneg : 0 ≤ D.expectedPosteriorUtility original := by
      rw [horiginal_posterior_utility]
      exact hUpsilon_pos.le
    rcases D.exists_sameUtilityExtendedScoreThresholdPolicy_of_policy_signed_nonnegative_target
        original hcost_pos horiginal_meas horiginal_bounds horiginal_utility_nonneg with
      ⟨threshold, alpha, policy, halpha_nonneg, halpha_le_one, hpolicy_bounds,
        _, hpolicy, hutility, _⟩
    have hpolicy_source :
        paper_measure_single_cost_aware_threshold_policy D threshold alpha policy := by
      rw [hpolicy]
      exact paper_measure_single_cost_aware_threshold_policy_source_definition
        D threshold alpha ⟨halpha_nonneg, halpha_le_one⟩
    have hpolicy_observed : allocationPolicyUsesFullPosterior D.posteriorUtility policy :=
      measure_single_threshold_uses_full_posterior D threshold alpha policy hpolicy_source
    refine ⟨threshold, alpha, policy, halpha_nonneg, halpha_le_one, ?_, ?_⟩
    · exact hpolicy_source.2.2
    · rw [hactual_utility_eq_posterior policy hpolicy_observed hpolicy_bounds, hutility,
        horiginal_posterior_utility]
  · intro Applicant Outcome _ _ D _ C hcost_pos hachievable
    rcases hachievable with ⟨original, horiginal_meas, _horiginal_observed, horiginal_bounds, horiginal_cost⟩
    rcases D.exists_sameCostExtendedScoreThresholdPolicy_of_policy
        original hcost_pos horiginal_meas horiginal_bounds with
      ⟨threshold, alpha, policy, halpha_nonneg, halpha_le_one, _,
        _, hpolicy, hcost, _⟩
    have hpolicy_source :
        paper_measure_single_cost_aware_threshold_policy D threshold alpha policy := by
      rw [hpolicy]
      exact paper_measure_single_cost_aware_threshold_policy_source_definition
        D threshold alpha ⟨halpha_nonneg, halpha_le_one⟩
    refine ⟨threshold, alpha, policy, halpha_nonneg, halpha_le_one, ?_, ?_⟩
    · exact hpolicy_source.2.2
    · rw [hcost, horiginal_cost]

private theorem legacy_appendix_theorem_allocation_slice_realizes_spec :
    ∀ {Applicant Outcome Group : Type*} [Fintype Applicant]
      [MeasurableSpace Outcome] [Fintype Group] [DecidableEq Group]
      (D : paper_measure_group_allocation_data Applicant Outcome Group)
      [IsFiniteMeasure D.law]
      (actualUtility : Applicant → Outcome → ℝ)
      (hactual_utility_eq_posterior :
        ∀ policy : MeasureGroupAllocationData.AllocationPolicy Applicant Outcome,
          MeasureGroupAllocationData.AllocationPolicyMeasurable policy →
            (∀ item outcome, 0 ≤ policy item outcome ∧ policy item outcome ≤ 1) →
              (∫ outcome,
                ∑ item : Applicant, policy item outcome * actualUtility item outcome ∂D.law) =
                  D.expectedPosteriorUtility policy)
      (hactual_group_utility_eq_posterior :
        ∀ (g : Group) (policy : MeasureGroupAllocationData.AllocationPolicy Applicant Outcome),
          MeasureGroupAllocationData.AllocationPolicyMeasurable policy →
            (∀ item outcome, 0 ≤ policy item outcome ∧ policy item outcome ≤ 1) →
              (∫ outcome,
                ∑ item : Applicant,
                  if D.group item = g then policy item outcome * actualUtility item outcome else 0 ∂D.law) =
                  D.expectedGroupPosteriorUtility g policy)
      (budget : ℝ) (diversityTarget : Group → ℝ)
      (original : MeasureGroupAllocationData.AllocationPolicy Applicant Outcome)
      (horiginal : _)
      (hcost_pos : ∀ item, 0 < D.allocCost item),
      legacy_appendix_theorem_allocation_sliceSpec
        D actualUtility hactual_utility_eq_posterior hactual_group_utility_eq_posterior
        budget diversityTarget original horiginal hcost_pos := by
  intro Applicant Outcome Group _ _ _ _ D _ actualUtility hactual_utility_eq_posterior
    hactual_group_utility_eq_posterior budget diversityTarget original horiginal hcost_pos
  have horiginal_source :
      paper_measure_group_allocation_optimal D budget diversityTarget original := by
    change D.SourceOptimal budget diversityTarget original
    refine ⟨?_, ?_⟩
    · refine ⟨horiginal.1, horiginal.2.1, horiginal.2.2.1, ?_⟩
      intro g
      rw [← hactual_group_utility_eq_posterior g original horiginal.2.1 horiginal.1]
      exact horiginal.2.2.2.1 g
    · intro other hother
      rw [← hactual_utility_eq_posterior other hother.2.1 hother.1,
        ← hactual_utility_eq_posterior original horiginal.2.1 horiginal.1]
      apply horiginal.2.2.2.2 other
      refine ⟨hother.1, hother.2.1, hother.2.2.1, ?_⟩
      intro g
      rw [hactual_group_utility_eq_posterior g other hother.2.1 hother.1]
      exact hother.2.2.2 g
  rcases CGGG20SelectiveInformationAcquisition.ProofBridge.paper_theorem1_measure_positive_cost_threshold_source_policy_optimal
      D budget diversityTarget original horiginal_source hcost_pos with
    ⟨threshold, alpha, replacement, halpha, hthreshold, hoptimal⟩
  refine ⟨threshold, alpha, replacement, halpha, hthreshold,
    hoptimal.1.1, hoptimal.1.2.1, hoptimal.1.2.2.1, ?_, ?_⟩
  · intro g
    rw [hactual_group_utility_eq_posterior g replacement hoptimal.1.2.1 hoptimal.1.1]
    exact hoptimal.1.2.2.2 g
  · intro other hother
    rw [hactual_utility_eq_posterior other hother.2.1 hother.1,
      hactual_utility_eq_posterior replacement hoptimal.1.2.1 hoptimal.1.1]
    apply hoptimal.2 other
    refine ⟨hother.1, hother.2.1, hother.2.2.1, ?_⟩
    intro g
    rw [← hactual_group_utility_eq_posterior g other hother.2.1 hother.1]
    exact hother.2.2.2 g

private theorem legacy_lemma3_equality_allocation_slice_realizes_spec :
    ∀ {Applicant Outcome Group : Type*} [Fintype Applicant]
      [MeasurableSpace Outcome] [Fintype Group] [DecidableEq Group]
      (D : paper_measure_group_allocation_data Applicant Outcome Group)
      [IsFiniteMeasure D.law]
      (actualUtility : Applicant → Outcome → ℝ)
      (hactual_utility_eq_posterior :
        ∀ policy : MeasureGroupAllocationData.AllocationPolicy Applicant Outcome,
          MeasureGroupAllocationData.AllocationPolicyMeasurable policy →
            (∀ item outcome, 0 ≤ policy item outcome ∧ policy item outcome ≤ 1) →
              (∫ outcome,
                ∑ item : Applicant, policy item outcome * actualUtility item outcome ∂D.law) =
                  D.expectedPosteriorUtility policy)
      (hactual_group_utility_eq_posterior :
        ∀ (g : Group) (policy : MeasureGroupAllocationData.AllocationPolicy Applicant Outcome),
          MeasureGroupAllocationData.AllocationPolicyMeasurable policy →
            (∀ item outcome, 0 ≤ policy item outcome ∧ policy item outcome ≤ 1) →
              (∫ outcome,
                ∑ item : Applicant,
                  if D.group item = g then policy item outcome * actualUtility item outcome else 0 ∂D.law) =
                  D.expectedGroupPosteriorUtility g policy)
      (c : ℝ) (hc : 0 < c) (hcost : ∀ item, D.allocCost item = c)
      (budget : ℝ) (equalityTarget : Group → ℝ)
      (original : MeasureGroupAllocationData.AllocationPolicy Applicant Outcome)
      (horiginal : _)
      (hequalityTarget_nonneg : ∀ g : Group, 0 ≤ equalityTarget g),
      legacy_lemma3_equality_allocation_sliceSpec
        D actualUtility hactual_utility_eq_posterior hactual_group_utility_eq_posterior
        c hc hcost budget equalityTarget original horiginal hequalityTarget_nonneg := by
  intro Applicant Outcome Group _ _ _ _ D _ actualUtility hactual_utility_eq_posterior
    hactual_group_utility_eq_posterior c hc hcost budget equalityTarget original horiginal
    hequalityTarget_nonneg
  have horiginal_source :
      paper_measure_group_allocation_equality_optimal D budget equalityTarget original := by
    change D.SourceEqualityOptimal budget equalityTarget original
    refine ⟨?_, ?_⟩
    · refine ⟨horiginal.1, horiginal.2.1, horiginal.2.2.1, ?_⟩
      intro g
      rw [← hactual_group_utility_eq_posterior g original horiginal.2.1 horiginal.1]
      exact horiginal.2.2.2.1 g
    · intro other hother
      rw [← hactual_utility_eq_posterior other hother.2.1 hother.1,
        ← hactual_utility_eq_posterior original horiginal.2.1 horiginal.1]
      apply horiginal.2.2.2.2 other
      refine ⟨hother.1, hother.2.1, hother.2.2.1, ?_⟩
      intro g
      rw [hactual_group_utility_eq_posterior g other hother.2.1 hother.1]
      exact hother.2.2.2 g
  rcases CGGG20SelectiveInformationAcquisition.ProofBridge.paper_lemma3_main_text_equality_threshold_sufficiency
      D c hc hcost budget equalityTarget original horiginal_source hequalityTarget_nonneg with
    ⟨threshold, alpha, replacement, hthreshold, hoptimal⟩
  refine ⟨threshold, alpha, replacement, hthreshold.1, hthreshold.2,
    hoptimal.1.1, hoptimal.1.2.1, hoptimal.1.2.2.1, ?_, ?_⟩
  · intro g
    rw [hactual_group_utility_eq_posterior g replacement hoptimal.1.2.1 hoptimal.1.1]
    exact hoptimal.1.2.2.2 g
  · intro other hother
    rw [hactual_utility_eq_posterior other hother.2.1 hother.1,
      hactual_utility_eq_posterior replacement hoptimal.1.2.1 hoptimal.1.1]
    apply hoptimal.2 other
    refine ⟨hother.1, hother.2.1, hother.2.2.1, ?_⟩
    intro g
    rw [← hactual_group_utility_eq_posterior g other hother.2.1 hother.1]
    exact hother.2.2.2 g

/-- Appendix threshold theorem at the source's full policy-pair level. -/
theorem appendix_theorem_cost_aware_threshold_policies_suffice :
    ∀ {Applicant Outcome Group : Type*} [Fintype Applicant]
      [MeasurableSpace Outcome] [Fintype Group]
      (D : paper_screening_allocation_data Applicant Outcome Group)
      (budget : ℝ) (hbudget_nonneg : 0 ≤ budget)
      (diversityTarget : Group → ℝ)
      (hdiversityTarget_nonneg : ∀ g, 0 ≤ diversityTarget g)
      (original : paper_screening_allocation_pair D)
      (hcost_pos : ∀ item, 0 < D.allocCost item)
      (horiginal : _),
      appendix_theorem_cost_aware_threshold_policies_sufficeSpec
        D budget hbudget_nonneg diversityTarget hdiversityTarget_nonneg original hcost_pos horiginal := by
  intro Applicant Outcome Group _ _ _ D budget hbudget_nonneg diversityTarget
    hdiversityTarget_nonneg original hcost_pos horiginal
  classical
  change D.PairActualOptimal budget diversityTarget original at horiginal
  have horiginal_source : D.PairSourceOptimal budget diversityTarget original :=
    (D.pairActualOptimal_iff_pairSourceOptimal budget diversityTarget original).mp horiginal
  rcases paper_cost_aware_threshold_policy_pairs_suffice
      D budget diversityTarget original hcost_pos horiginal_source with
    ⟨threshold, alpha, replacement, hscreening, hthreshold, hreplaced⟩
  unfold appendix_theorem_cost_aware_threshold_policies_sufficeSpec
  have hactual : D.PairActualOptimal budget diversityTarget replacement :=
    (D.pairActualOptimal_iff_pairSourceOptimal
      budget diversityTarget replacement).mpr hreplaced
  exact ⟨threshold, alpha, replacement, hscreening, hthreshold,
    hactual.1.1, hactual.1.2.1, hactual.1.2.2.1,
    (by simpa only [hscreening] using hactual.1.2.2.2.1),
    (by simpa only [hscreening] using hactual.1.2.2.2.2),
    (by simpa only [hscreening] using hactual.2)⟩

/-- Appendix Lemma 3 at the source's full equality-constrained pair level. -/
theorem lemma3_equality_diversity_threshold_sufficiency :
    ∀ {Applicant Outcome Group : Type*} [Fintype Applicant]
      [MeasurableSpace Outcome] [Fintype Group]
      (D : paper_screening_allocation_data Applicant Outcome Group)
      (screeningCost : ℝ)
      (c : ℝ) (hc : 0 < c)
      (budget : ℝ) (hbudget_nonneg : 0 ≤ budget)
      (equalityTarget : Group → ℝ)
      (original : paper_screening_allocation_pair D)
      (hscreeningCost : ∀ item, D.screenCost item = screeningCost)
      (hcost : ∀ item, D.allocCost item = c)
      (hequalityTarget_nonneg : ∀ g : Group, 0 ≤ equalityTarget g)
      (horiginal : _),
      lemma3_equality_diversity_threshold_sufficiencySpec
        D screeningCost c hc budget hbudget_nonneg equalityTarget original hscreeningCost hcost
        hequalityTarget_nonneg horiginal := by
  intro Applicant Outcome Group _ _ _ D screeningCost c hc budget hbudget_nonneg equalityTarget
    original hscreeningCost hcost hequalityTarget_nonneg horiginal
  classical
  change D.PairActualEqualityOptimal budget equalityTarget original at horiginal
  have horiginal_source : D.PairSourceEqualityOptimal budget equalityTarget original :=
    (D.pairActualEqualityOptimal_iff_pairSourceEqualityOptimal
      budget equalityTarget original).mp horiginal
  rcases paper_main_text_equality_threshold_policy_pairs_suffice
      D c hc budget equalityTarget original hcost hequalityTarget_nonneg horiginal_source with
    ⟨threshold, alpha, replacement, hscreening, hthreshold, hreplaced⟩
  unfold lemma3_equality_diversity_threshold_sufficiencySpec
  have hactual : D.PairActualEqualityOptimal budget equalityTarget replacement :=
    (D.pairActualEqualityOptimal_iff_pairSourceEqualityOptimal
      budget equalityTarget replacement).mpr hreplaced
  exact ⟨threshold, alpha, replacement, hscreening, hthreshold,
    hactual.1.1, hactual.1.2.1, hactual.1.2.2.1,
    (by simpa only [hscreening] using hactual.1.2.2.2.1),
    (by simpa only [hscreening] using hactual.1.2.2.2.2),
    (by simpa only [hscreening] using hactual.2)⟩

/-! ## Optimized-procedure formulas -/

theorem equation_lp1_optimized_two_group_objective
    {ScreenApplicant DirectApplicant : Type*}
    [Fintype ScreenApplicant] [Fintype DirectApplicant]
    (D : paper_optimized_two_group_data ScreenApplicant DirectApplicant)
    (p : ScreenApplicant → ℝ) (a : DirectApplicant → ℝ)
    (hprobability : D.probabilityBounds p a) :
    equation_lp1_optimized_two_group_objectiveSpec
      (ScreenApplicant := ScreenApplicant) (DirectApplicant := DirectApplicant)
      (D := D) (p := p) (a := a) hprobability := by
  exact CGGG20SelectiveInformationAcquisition.ProofBridge.paper_equation_lp1_source_formula (ScreenApplicant := ScreenApplicant) (DirectApplicant := DirectApplicant) (D := D) (p := p) (a := a)

theorem equation_lp2_optimized_two_group_budget
    {ScreenApplicant DirectApplicant : Type*}
    [Fintype ScreenApplicant] [Fintype DirectApplicant]
    (D : paper_optimized_two_group_data ScreenApplicant DirectApplicant)
    (p : ScreenApplicant → ℝ) (a : DirectApplicant → ℝ)
    (hprobability : D.probabilityBounds p a) :
    equation_lp2_optimized_two_group_budgetSpec
      (ScreenApplicant := ScreenApplicant) (DirectApplicant := DirectApplicant)
      (D := D) (p := p) (a := a) hprobability := by
  exact CGGG20SelectiveInformationAcquisition.ProofBridge.paper_equation_lp2_source_formula (ScreenApplicant := ScreenApplicant) (DirectApplicant := DirectApplicant) (D := D) (p := p) (a := a)

theorem equation_lp3_optimized_screened_group_equality
    {ScreenApplicant DirectApplicant : Type*}
    [Fintype ScreenApplicant] [Fintype DirectApplicant]
    (D : paper_optimized_two_group_data ScreenApplicant DirectApplicant)
    (p : ScreenApplicant → ℝ) (a : DirectApplicant → ℝ)
    (hprobability : D.probabilityBounds p a) :
    equation_lp3_optimized_screened_group_equalitySpec
      (ScreenApplicant := ScreenApplicant) (DirectApplicant := DirectApplicant)
      (D := D) (p := p) (a := a) hprobability := by
  exact CGGG20SelectiveInformationAcquisition.ProofBridge.paper_equation_lp3_source_formula (ScreenApplicant := ScreenApplicant) (DirectApplicant := DirectApplicant) (D := D) (p := p)

theorem equation_lp4_optimized_direct_group_equality
    {ScreenApplicant DirectApplicant : Type*}
    [Fintype ScreenApplicant] [Fintype DirectApplicant]
    (D : paper_optimized_two_group_data ScreenApplicant DirectApplicant)
    (p : ScreenApplicant → ℝ) (a : DirectApplicant → ℝ)
    (hprobability : D.probabilityBounds p a) :
    equation_lp4_optimized_direct_group_equalitySpec
      (ScreenApplicant := ScreenApplicant) (DirectApplicant := DirectApplicant)
      (D := D) (p := p) (a := a) hprobability := by
  exact CGGG20SelectiveInformationAcquisition.ProofBridge.paper_equation_lp4_source_formula (ScreenApplicant := ScreenApplicant) (DirectApplicant := DirectApplicant) (D := D) (a := a)

end

end PaperInterface
end CGGG20SelectiveInformationAcquisition

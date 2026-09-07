import AppliedModelingLib.Learning.BinaryOutcomeLikelihood
import AppliedModelingLib.Learning.OutcomeMonotoneThreshold

/-!
# Comparative statics for outcome-likelihood thresholds

This module derives the nested-decision and burden monotonicity facts used by
strategic-classification threshold arguments.  The response decision includes
the source's acceptance-favoring tie convention from
`OutcomeMonotoneThreshold`.
-/

namespace AppliedModelingLib

/-- Final accept/reject decision under an acceptance-favoring response to a likelihood threshold. -/
noncomputable def acceptanceFavoringLikelihoodThresholdDecision
    {Feature : Type*} [Fintype Feature]
    (likelihood : Feature → ℝ) (cost : Feature → Feature → ℝ)
    (threshold : ℝ) (initial : Feature) : Bool :=
  let classifier := likelihoodThresholdClassifier likelihood threshold
  classifier (acceptanceFavoringStrategicBestResponse classifier cost initial)

/-- Threshold response accepts exactly when some threshold-accepted action costs at most one. -/
theorem acceptanceFavoringLikelihoodThresholdDecision_eq_true_iff
    {Feature : Type*} [Fintype Feature]
    {likelihood : Feature → ℝ} {cost : Feature → Feature → ℝ}
    (hcost : IsOutcomeMonotoneCost likelihood cost)
    (threshold : ℝ) (initial : Feature) :
    acceptanceFavoringLikelihoodThresholdDecision likelihood cost threshold initial = true ↔
      ∃ action, threshold ≤ likelihood action ∧ cost initial action ≤ 1 := by
  unfold acceptanceFavoringLikelihoodThresholdDecision
  rw [(acceptanceFavoringStrategicBestResponse_spec
    (likelihoodThresholdClassifier likelihood threshold) cost initial
    hcost.cost_nonneg hcost.cost_self).accepted_iff_exists_cost_le_one
      hcost.cost_nonneg hcost.cost_self]
  simp only [likelihoodThresholdClassifier_eq_true_iff]

/-- With a nonempty threshold acceptance set, final acceptance is burden at most one. -/
theorem acceptanceFavoringLikelihoodThresholdDecision_eq_true_iff_individualBurden_le_one
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {likelihood : Feature → ℝ} {cost : Feature → Feature → ℝ}
    (hcost : IsOutcomeMonotoneCost likelihood cost)
    (threshold : ℝ) (initial : Feature)
    (haccepted :
      (acceptedFeatures (likelihoodThresholdClassifier likelihood threshold)).Nonempty) :
    acceptanceFavoringLikelihoodThresholdDecision likelihood cost threshold initial = true ↔
      individualBurden cost (likelihoodThresholdClassifier likelihood threshold)
        initial haccepted ≤ 1 := by
  exact acceptanceFavoringStrategicBestResponse_accepts_iff_individualBurden_le_one
    (likelihoodThresholdClassifier likelihood threshold) cost initial haccepted
    hcost.cost_nonneg hcost.cost_self

/-- Raising the classifier threshold can only remove final acceptances. -/
theorem acceptanceFavoringLikelihoodThresholdDecision_nested
    {Feature : Type*} [Fintype Feature]
    {likelihood : Feature → ℝ} {cost : Feature → Feature → ℝ}
    (hcost : IsOutcomeMonotoneCost likelihood cost)
    {lowerThreshold upperThreshold : ℝ} (hthreshold : lowerThreshold ≤ upperThreshold)
    (initial : Feature)
    (haccepted :
      acceptanceFavoringLikelihoodThresholdDecision
        likelihood cost upperThreshold initial = true) :
    acceptanceFavoringLikelihoodThresholdDecision
      likelihood cost lowerThreshold initial = true := by
  rw [acceptanceFavoringLikelihoodThresholdDecision_eq_true_iff hcost] at haccepted ⊢
  obtain ⟨action, haction, hactionCost⟩ := haccepted
  exact ⟨action, hthreshold.trans haction, hactionCost⟩

/-- Higher-likelihood individuals are weakly more likely to be accepted after response. -/
theorem acceptanceFavoringLikelihoodThresholdDecision_mono_likelihood
    {Feature : Type*} [Fintype Feature]
    {likelihood : Feature → ℝ} {cost : Feature → Feature → ℝ}
    (hcost : IsOutcomeMonotoneCost likelihood cost)
    (threshold : ℝ) {lower higher : Feature}
    (hlikelihood : likelihood lower ≤ likelihood higher)
    (haccepted :
      acceptanceFavoringLikelihoodThresholdDecision
        likelihood cost threshold lower = true) :
    acceptanceFavoringLikelihoodThresholdDecision
      likelihood cost threshold higher = true := by
  rw [acceptanceFavoringLikelihoodThresholdDecision_eq_true_iff hcost] at haccepted ⊢
  obtain ⟨action, haction, hactionCost⟩ := haccepted
  exact ⟨action, haction,
    (hcost.cost_anti_left hlikelihood action).trans hactionCost⟩

/-- Every individual already above the published threshold is accepted after response. -/
theorem acceptanceFavoringLikelihoodThresholdDecision_eq_true_of_threshold_le
    {Feature : Type*} [Fintype Feature]
    {likelihood : Feature → ℝ} {cost : Feature → Feature → ℝ}
    (hcost : IsOutcomeMonotoneCost likelihood cost)
    (threshold : ℝ) (initial : Feature)
    (hthreshold : threshold ≤ likelihood initial) :
    acceptanceFavoringLikelihoodThresholdDecision
      likelihood cost threshold initial = true := by
  rw [acceptanceFavoringLikelihoodThresholdDecision_eq_true_iff hcost]
  exact ⟨initial, hthreshold, by simp [hcost.cost_self initial]⟩

/-- A feature removed by a higher threshold has likelihood strictly below that threshold. -/
theorem likelihood_lt_threshold_of_acceptance_removed
    {Feature : Type*} [Fintype Feature]
    {likelihood : Feature → ℝ} {cost : Feature → Feature → ℝ}
    (hcost : IsOutcomeMonotoneCost likelihood cost)
    {lowerThreshold upperThreshold : ℝ} (initial : Feature)
    (_hlowerAccepted :
      acceptanceFavoringLikelihoodThresholdDecision
        likelihood cost lowerThreshold initial = true)
    (hupperRejected :
      acceptanceFavoringLikelihoodThresholdDecision
        likelihood cost upperThreshold initial = false) :
    likelihood initial < upperThreshold := by
  by_contra hnot
  have haccepted :=
    acceptanceFavoringLikelihoodThresholdDecision_eq_true_of_threshold_le
      hcost upperThreshold initial (le_of_not_gt hnot)
  exact Bool.false_ne_true (hupperRejected.symm.trans haccepted)

/-- Minimum burden is monotone when the feasible acceptance set shrinks. -/
theorem individualBurden_mono_of_acceptedFeatures_subset
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (cost : Feature → Feature → ℝ)
    (largerAcceptance smallerAcceptance : BinaryClassifier Feature)
    (hlarger : (acceptedFeatures largerAcceptance).Nonempty)
    (hsmaller : (acceptedFeatures smallerAcceptance).Nonempty)
    (hsubset : acceptedFeatures smallerAcceptance ⊆
      acceptedFeatures largerAcceptance)
    (initial : Feature) :
    individualBurden cost largerAcceptance initial hlarger ≤
      individualBurden cost smallerAcceptance initial hsmaller := by
  classical
  have hminimumMem :
      ((acceptedFeatures smallerAcceptance).image (cost initial)).min'
          (hsmaller.image (cost initial)) ∈
        (acceptedFeatures smallerAcceptance).image (cost initial) :=
    Finset.min'_mem _ _
  obtain ⟨action, haction, hcostEq⟩ := Finset.mem_image.mp hminimumMem
  calc
    individualBurden cost largerAcceptance initial hlarger ≤ cost initial action := by
      apply Finset.min'_le
      exact Finset.mem_image_of_mem (cost initial) (hsubset haction)
    _ = individualBurden cost smallerAcceptance initial hsmaller := by
      exact hcostEq

/-- Accepted feature sets shrink as the likelihood threshold rises. -/
theorem likelihoodThresholdClassifier_acceptedFeatures_subset
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (likelihood : Feature → ℝ) {lowerThreshold upperThreshold : ℝ}
    (hthreshold : lowerThreshold ≤ upperThreshold) :
    acceptedFeatures (likelihoodThresholdClassifier likelihood upperThreshold) ⊆
      acceptedFeatures (likelihoodThresholdClassifier likelihood lowerThreshold) := by
  intro feature hfeature
  simp [acceptedFeatures] at hfeature ⊢
  exact hthreshold.trans hfeature

/-- Individual burden is nondecreasing in a nonempty likelihood threshold. -/
theorem individualBurden_likelihoodThresholdClassifier_mono
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (likelihood : Feature → ℝ) (cost : Feature → Feature → ℝ)
    {lowerThreshold upperThreshold : ℝ} (hthreshold : lowerThreshold ≤ upperThreshold)
    (hlower :
      (acceptedFeatures (likelihoodThresholdClassifier likelihood lowerThreshold)).Nonempty)
    (hupper :
      (acceptedFeatures (likelihoodThresholdClassifier likelihood upperThreshold)).Nonempty)
    (initial : Feature) :
    individualBurden cost (likelihoodThresholdClassifier likelihood lowerThreshold)
        initial hlower ≤
      individualBurden cost (likelihoodThresholdClassifier likelihood upperThreshold)
        initial hupper :=
  individualBurden_mono_of_acceptedFeatures_subset cost _ _ hlower hupper
    (likelihoodThresholdClassifier_acceptedFeatures_subset likelihood hthreshold) initial

/-- Social burden is nondecreasing in a nonempty likelihood threshold. -/
theorem socialBurden_likelihoodThresholdClassifier_mono
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (population : PMF (Feature × Bool)) (likelihood : Feature → ℝ)
    (cost : Feature → Feature → ℝ)
    {lowerThreshold upperThreshold : ℝ} (hthreshold : lowerThreshold ≤ upperThreshold)
    (hlower :
      (acceptedFeatures (likelihoodThresholdClassifier likelihood lowerThreshold)).Nonempty)
    (hupper :
      (acceptedFeatures (likelihoodThresholdClassifier likelihood upperThreshold)).Nonempty) :
    socialBurden population cost
        (likelihoodThresholdClassifier likelihood lowerThreshold) hlower ≤
      socialBurden population cost
        (likelihoodThresholdClassifier likelihood upperThreshold) hupper :=
  socialBurden_mono_of_forall_individualBurden_le
    population cost _ _ hlower hupper
    (individualBurden_likelihoodThresholdClassifier_mono
      likelihood cost hthreshold hlower hupper)

/--
For positive calibrated outcome likelihoods, unequal strategic accuracies at
two ordered nonempty thresholds imply a strict increase in positive-label
social burden.
-/
theorem socialBurden_likelihoodThresholdClassifier_strict_of_accuracy_ne
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {population : PMF (Feature × Bool)} {likelihood : Feature → ℝ}
    {cost : Feature → Feature → ℝ}
    (hcalibrated : IsBinaryOutcomeLikelihood population likelihood)
    (hlikelihoodPositive : ∀ feature, 0 < likelihood feature)
    (hcost : IsOutcomeMonotoneCost likelihood cost)
    {lowerThreshold upperThreshold : ℝ} (hthreshold : lowerThreshold ≤ upperThreshold)
    (hlower :
      (acceptedFeatures (likelihoodThresholdClassifier likelihood lowerThreshold)).Nonempty)
    (hupper :
      (acceptedFeatures (likelihoodThresholdClassifier likelihood upperThreshold)).Nonempty)
    (haccuracy :
      binaryDecisionAccuracy population
          (acceptanceFavoringLikelihoodThresholdDecision
            likelihood cost lowerThreshold) ≠
        binaryDecisionAccuracy population
          (acceptanceFavoringLikelihoodThresholdDecision
            likelihood cost upperThreshold)) :
    socialBurden population cost
        (likelihoodThresholdClassifier likelihood lowerThreshold) hlower <
      socialBurden population cost
        (likelihoodThresholdClassifier likelihood upperThreshold) hupper := by
  let lowerDecision :=
    acceptanceFavoringLikelihoodThresholdDecision likelihood cost lowerThreshold
  let upperDecision :=
    acceptanceFavoringLikelihoodThresholdDecision likelihood cost upperThreshold
  obtain ⟨feature, hfeatureMass, hdecisionsDiffer⟩ :=
    exists_positive_featureMass_of_binaryDecisionAccuracy_ne
      population lowerDecision upperDecision haccuracy
  have hupperFalse : upperDecision feature = false := by
    by_contra hnot
    have hupperTrue : upperDecision feature = true := Bool.eq_true_of_not_eq_false hnot
    have hlowerTrue : lowerDecision feature = true :=
      acceptanceFavoringLikelihoodThresholdDecision_nested
        hcost hthreshold feature hupperTrue
    exact hdecisionsDiffer (hlowerTrue.trans hupperTrue.symm)
  have hlowerTrue : lowerDecision feature = true := by
    by_contra hnot
    have hlowerFalse : lowerDecision feature = false := Bool.eq_false_of_not_eq_true hnot
    exact hdecisionsDiffer (hlowerFalse.trans hupperFalse.symm)
  have hlowerBurden :
      individualBurden cost
          (likelihoodThresholdClassifier likelihood lowerThreshold)
          feature hlower ≤ 1 :=
    (acceptanceFavoringLikelihoodThresholdDecision_eq_true_iff_individualBurden_le_one
      hcost lowerThreshold feature hlower).mp hlowerTrue
  have hupperBurden :
      1 < individualBurden cost
        (likelihoodThresholdClassifier likelihood upperThreshold)
        feature hupper := by
    apply lt_of_not_ge
    intro hle
    have hupperTrue :=
      (acceptanceFavoringLikelihoodThresholdDecision_eq_true_iff_individualBurden_le_one
        hcost upperThreshold feature hupper).mpr hle
    exact Bool.false_ne_true (hupperFalse.symm.trans hupperTrue)
  have hstrictFeature :
      individualBurden cost
          (likelihoodThresholdClassifier likelihood lowerThreshold)
          feature hlower <
        individualBurden cost
          (likelihoodThresholdClassifier likelihood upperThreshold)
          feature hupper :=
    hlowerBurden.trans_lt hupperBurden
  have htrueMass : 0 < (population (feature, true)).toReal :=
    hcalibrated.trueMass_pos_of_featureMass_pos
      feature (hlikelihoodPositive feature) hfeatureMass
  have hpositiveEvent :
      0 < pmfProb population (fun datum : Feature × Bool => datum.2 = true) :=
    pmfProb_pos_of_mass population (fun datum : Feature × Bool => datum.2 = true)
      (feature, true) rfl htrueMass
  unfold socialBurden
  apply pmfConditionalExp_lt_of_forall_le_exists_pos_lt population
    (fun datum : Feature × Bool => datum.2 = true) hpositiveEvent
  · intro datum _
    exact individualBurden_likelihoodThresholdClassifier_mono
      likelihood cost hthreshold hlower hupper datum.1
  · exact ⟨(feature, true), rfl, htrueMass, hstrictFeature⟩

/-- Below one half, raising the threshold weakly improves calibrated strategic accuracy. -/
theorem binaryDecisionAccuracy_acceptanceFavoringThreshold_mono_below_half
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {population : PMF (Feature × Bool)} {likelihood : Feature → ℝ}
    {cost : Feature → Feature → ℝ}
    (hcalibrated : IsBinaryOutcomeLikelihood population likelihood)
    (hcost : IsOutcomeMonotoneCost likelihood cost)
    {lowerThreshold upperThreshold : ℝ} (hthreshold : lowerThreshold ≤ upperThreshold)
    (hupperHalf : upperThreshold ≤ (1 : ℝ) / 2) :
    binaryDecisionAccuracy population
        (acceptanceFavoringLikelihoodThresholdDecision
          likelihood cost lowerThreshold) ≤
      binaryDecisionAccuracy population
        (acceptanceFavoringLikelihoodThresholdDecision
          likelihood cost upperThreshold) := by
  apply binaryDecisionAccuracy_le_of_nested_of_removed_le_half
    hcalibrated _ _
  · intro feature haccepted
    exact acceptanceFavoringLikelihoodThresholdDecision_nested
      hcost hthreshold feature haccepted
  · intro feature hlowerAccepted hupperRejected
    exact (likelihood_lt_threshold_of_acceptance_removed
      hcost feature hlowerAccepted hupperRejected).le.trans hupperHalf

/--
Any threshold whose calibrated strategic accuracy strictly exceeds the
half-threshold baseline must itself lie strictly above one half.
-/
theorem half_lt_threshold_of_acceptanceFavoringThreshold_accuracy_gt_half
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {population : PMF (Feature × Bool)} {likelihood : Feature → ℝ}
    {cost : Feature → Feature → ℝ}
    (hcalibrated : IsBinaryOutcomeLikelihood population likelihood)
    (hcost : IsOutcomeMonotoneCost likelihood cost)
    {threshold : ℝ}
    (haccuracy :
      binaryDecisionAccuracy population
          (acceptanceFavoringLikelihoodThresholdDecision
            likelihood cost ((1 : ℝ) / 2)) <
        binaryDecisionAccuracy population
          (acceptanceFavoringLikelihoodThresholdDecision
            likelihood cost threshold)) :
    (1 : ℝ) / 2 < threshold := by
  by_contra hnot
  have hthreshold : threshold ≤ (1 : ℝ) / 2 := le_of_not_gt hnot
  have hmono :=
    binaryDecisionAccuracy_acceptanceFavoringThreshold_mono_below_half
      hcalibrated hcost hthreshold (le_refl ((1 : ℝ) / 2))
  exact (not_lt_of_ge hmono) haccuracy

/--
Strictly improving calibrated strategic accuracy over the half-threshold
baseline strictly raises positive-label social burden whenever both real-valued
minimum burdens are defined.
-/
theorem socialBurden_halfThreshold_lt_of_acceptanceFavoringThreshold_accuracy_gt_half
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {population : PMF (Feature × Bool)} {likelihood : Feature → ℝ}
    {cost : Feature → Feature → ℝ}
    (hcalibrated : IsBinaryOutcomeLikelihood population likelihood)
    (hlikelihoodPositive : ∀ feature, 0 < likelihood feature)
    (hcost : IsOutcomeMonotoneCost likelihood cost)
    {threshold : ℝ}
    (hhalfAccepted :
      (acceptedFeatures
        (likelihoodThresholdClassifier likelihood ((1 : ℝ) / 2))).Nonempty)
    (hthresholdAccepted :
      (acceptedFeatures
        (likelihoodThresholdClassifier likelihood threshold)).Nonempty)
    (haccuracy :
      binaryDecisionAccuracy population
          (acceptanceFavoringLikelihoodThresholdDecision
            likelihood cost ((1 : ℝ) / 2)) <
        binaryDecisionAccuracy population
          (acceptanceFavoringLikelihoodThresholdDecision
            likelihood cost threshold)) :
    socialBurden population cost
        (likelihoodThresholdClassifier likelihood ((1 : ℝ) / 2)) hhalfAccepted <
      socialBurden population cost
        (likelihoodThresholdClassifier likelihood threshold) hthresholdAccepted := by
  have hhalfThreshold : (1 : ℝ) / 2 < threshold :=
    half_lt_threshold_of_acceptanceFavoringThreshold_accuracy_gt_half
      hcalibrated hcost haccuracy
  apply socialBurden_likelihoodThresholdClassifier_strict_of_accuracy_ne
    hcalibrated hlikelihoodPositive hcost hhalfThreshold.le hhalfAccepted
      hthresholdAccepted
  exact ne_of_lt haccuracy

/-- Strategic accuracy generated by the acceptance-favoring likelihood-threshold response. -/
noncomputable def acceptanceFavoringLikelihoodThresholdAccuracy
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (population : PMF (Feature × Bool)) (likelihood : Feature → ℝ)
    (cost : Feature → Feature → ℝ) (threshold : ℝ) : ℝ :=
  binaryDecisionAccuracy population
    (acceptanceFavoringLikelihoodThresholdDecision likelihood cost threshold)

/-- Strategic threshold accuracy is quasiconcave in the ternary order sense. -/
theorem acceptanceFavoringLikelihoodThresholdAccuracy_quasiconcave
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {population : PMF (Feature × Bool)} {likelihood : Feature → ℝ}
    {cost : Feature → Feature → ℝ}
    (hcalibrated : IsBinaryOutcomeLikelihood population likelihood)
    (hcost : IsOutcomeMonotoneCost likelihood cost)
    {first middle last : ℝ} (hfirstMiddle : first ≤ middle)
    (hmiddleLast : middle ≤ last) :
    min (acceptanceFavoringLikelihoodThresholdAccuracy
          population likelihood cost first)
        (acceptanceFavoringLikelihoodThresholdAccuracy
          population likelihood cost last) ≤
      acceptanceFavoringLikelihoodThresholdAccuracy
        population likelihood cost middle := by
  apply binaryDecisionAccuracy_quasiconcave_of_nested_upper
    hcalibrated
    (acceptanceFavoringLikelihoodThresholdDecision likelihood cost)
  · intro lower upper hlowerUpper feature haccepted
    exact acceptanceFavoringLikelihoodThresholdDecision_nested
      hcost hlowerUpper feature haccepted
  · intro threshold lower higher hlowerHigher haccepted
    exact acceptanceFavoringLikelihoodThresholdDecision_mono_likelihood
      hcost threshold hlowerHigher haccepted
  · exact hfirstMiddle
  · exact hmiddleLast

/-- The finite range of induced decision rules supplies a maximizing real threshold. -/
theorem exists_maximizing_acceptanceFavoringLikelihoodThresholdAccuracy
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (population : PMF (Feature × Bool)) (likelihood : Feature → ℝ)
    (cost : Feature → Feature → ℝ) :
    ∃ maximizingThreshold : ℝ, ∀ threshold,
      acceptanceFavoringLikelihoodThresholdAccuracy
          population likelihood cost threshold ≤
        acceptanceFavoringLikelihoodThresholdAccuracy
          population likelihood cost maximizingThreshold := by
  classical
  let decision : ℝ → Feature → Bool :=
    acceptanceFavoringLikelihoodThresholdDecision likelihood cost
  let feasible : (Feature → Bool) → Prop := fun candidate =>
    ∃ threshold, decision threshold = candidate
  obtain ⟨optimal, hoptimal⟩ :=
    Optimization.exists_isMaximizerOn_of_finite feasible
      (binaryDecisionAccuracy population) ⟨decision 0, ⟨0, rfl⟩⟩
  obtain ⟨maximizingThreshold, hthreshold⟩ := hoptimal.1
  refine ⟨maximizingThreshold, ?_⟩
  intro threshold
  have hle := hoptimal.2 (decision threshold) ⟨threshold, rfl⟩
  rw [← hthreshold] at hle
  exact hle

/-- A maximizing threshold can always be chosen weakly above one half. -/
theorem exists_half_le_maximizing_acceptanceFavoringLikelihoodThresholdAccuracy
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {population : PMF (Feature × Bool)} {likelihood : Feature → ℝ}
    {cost : Feature → Feature → ℝ}
    (hcalibrated : IsBinaryOutcomeLikelihood population likelihood)
    (hcost : IsOutcomeMonotoneCost likelihood cost) :
    ∃ maximizingThreshold : ℝ,
      (1 : ℝ) / 2 ≤ maximizingThreshold ∧
        ∀ threshold,
          acceptanceFavoringLikelihoodThresholdAccuracy
              population likelihood cost threshold ≤
            acceptanceFavoringLikelihoodThresholdAccuracy
              population likelihood cost maximizingThreshold := by
  obtain ⟨maximizingThreshold, hmaximizing⟩ :=
    exists_maximizing_acceptanceFavoringLikelihoodThresholdAccuracy
      population likelihood cost
  by_cases hhalf : (1 : ℝ) / 2 ≤ maximizingThreshold
  · exact ⟨maximizingThreshold, hhalf, hmaximizing⟩
  · have hthresholdHalf : maximizingThreshold ≤ (1 : ℝ) / 2 := le_of_not_ge hhalf
    have hmaxToHalf :
        acceptanceFavoringLikelihoodThresholdAccuracy
            population likelihood cost maximizingThreshold ≤
          acceptanceFavoringLikelihoodThresholdAccuracy
            population likelihood cost ((1 : ℝ) / 2) := by
      exact binaryDecisionAccuracy_acceptanceFavoringThreshold_mono_below_half
        hcalibrated hcost hthresholdHalf le_rfl
    refine ⟨(1 : ℝ) / 2, le_rfl, ?_⟩
    intro threshold
    exact (hmaximizing threshold).trans hmaxToHalf

/-- The source's one-dimensional weak single-peakedness formulation. -/
def IsWeaklySinglePeakedAt (utility : ℝ → ℝ) (pivot : ℝ) : Prop :=
  (∀ first middle, first ≤ middle → middle ≤ pivot →
      utility first ≤ utility middle) ∧
    (∀ middle last, pivot ≤ middle → middle ≤ last →
      utility last ≤ utility middle)

/-- Ternary quasiconcavity plus a global maximizer gives weak single-peakedness. -/
theorem isWeaklySinglePeakedAt_of_quasiconcave_of_maximizes
    (utility : ℝ → ℝ) (pivot : ℝ)
    (hquasiconcave : ∀ {first middle last : ℝ}, first ≤ middle → middle ≤ last →
      min (utility first) (utility last) ≤ utility middle)
    (hmaximizes : ∀ threshold, utility threshold ≤ utility pivot) :
    IsWeaklySinglePeakedAt utility pivot := by
  constructor
  · intro first middle hfirstMiddle hmiddlePivot
    have hquasi := hquasiconcave hfirstMiddle hmiddlePivot
    simpa [min_eq_left (hmaximizes first)] using hquasi
  · intro middle last hpivotMiddle hmiddleLast
    have hquasi := hquasiconcave hpivotMiddle hmiddleLast
    simpa [min_eq_right (hmaximizes last)] using hquasi

/-- Strategic threshold accuracy is weakly single-peaked at a maximizer above one half. -/
theorem exists_half_le_singlePeaked_maximizing_acceptanceFavoringLikelihoodThresholdAccuracy
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {population : PMF (Feature × Bool)} {likelihood : Feature → ℝ}
    {cost : Feature → Feature → ℝ}
    (hcalibrated : IsBinaryOutcomeLikelihood population likelihood)
    (hcost : IsOutcomeMonotoneCost likelihood cost) :
    ∃ maximizingThreshold : ℝ,
      (1 : ℝ) / 2 ≤ maximizingThreshold ∧
        (∀ threshold,
          acceptanceFavoringLikelihoodThresholdAccuracy
              population likelihood cost threshold ≤
            acceptanceFavoringLikelihoodThresholdAccuracy
              population likelihood cost maximizingThreshold) ∧
        IsWeaklySinglePeakedAt
          (acceptanceFavoringLikelihoodThresholdAccuracy
            population likelihood cost)
          maximizingThreshold := by
  obtain ⟨maximizingThreshold, hhalf, hmaximizes⟩ :=
    exists_half_le_maximizing_acceptanceFavoringLikelihoodThresholdAccuracy
      hcalibrated hcost
  refine ⟨maximizingThreshold, hhalf, hmaximizes, ?_⟩
  apply isWeaklySinglePeakedAt_of_quasiconcave_of_maximizes _ _ _ hmaximizes
  intro first middle last hfirstMiddle hmiddleLast
  exact acceptanceFavoringLikelihoodThresholdAccuracy_quasiconcave
    hcalibrated hcost hfirstMiddle hmiddleLast

end AppliedModelingLib

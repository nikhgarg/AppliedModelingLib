import AppliedModelingLib.Learning.StrategicResponse

/-!
# Calibrated binary outcome likelihoods

This module gives a finite, division-free bridge between a joint law of
features and binary labels and a feature-level outcome likelihood.  The bridge
is useful whenever an accuracy argument needs to replace conditional label
probabilities by a calibrated score.

The identity

`P(X = x, Y = true) = likelihood x * P(X = x)`

remains meaningful at zero-mass features and therefore avoids arbitrary
conditional-probability conventions.
-/

namespace AppliedModelingLib

/-- Marginal probability mass of one feature under a finite binary-labelled population. -/
noncomputable def binaryFeatureMass {Feature : Type*}
    (population : PMF (Feature × Bool)) (feature : Feature) : ℝ :=
  (population (feature, false)).toReal + (population (feature, true)).toReal

/-- A likelihood calibrates the positive-label mass at every feature. -/
def IsBinaryOutcomeLikelihood {Feature : Type*}
    (population : PMF (Feature × Bool)) (likelihood : Feature → ℝ) : Prop :=
  ∀ feature,
    (population (feature, true)).toReal =
      likelihood feature * binaryFeatureMass population feature

/-- Accuracy of a feature-level binary decision under a joint finite population. -/
noncomputable def binaryDecisionAccuracy {Feature : Type*}
    [Fintype Feature] [DecidableEq Feature]
    (population : PMF (Feature × Bool)) (decision : Feature → Bool) : ℝ :=
  pmfExp population fun datum => if decision datum.1 = datum.2 then 1 else 0

/-- Strategic accuracy is binary decision accuracy for the induced post-response decision. -/
theorem strategicAccuracy_eq_binaryDecisionAccuracy
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (population : PMF (Feature × Bool)) (classifier : BinaryClassifier Feature)
    (response : Feature → Feature) :
    strategicAccuracy population classifier response =
      binaryDecisionAccuracy population (fun feature => classifier (response feature)) :=
  rfl

/-- Binary decision accuracy is the sum of the selected label mass at each feature. -/
theorem binaryDecisionAccuracy_eq_sum_feature_mass
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (population : PMF (Feature × Bool)) (decision : Feature → Bool) :
    binaryDecisionAccuracy population decision =
      ∑ feature,
        if decision feature then (population (feature, true)).toReal
        else (population (feature, false)).toReal := by
  classical
  unfold binaryDecisionAccuracy pmfExp
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro feature _
  cases hdecision : decision feature <;> simp [hdecision]

/-- Feature marginal mass is nonnegative. -/
theorem binaryFeatureMass_nonneg {Feature : Type*}
    (population : PMF (Feature × Bool)) (feature : Feature) :
    0 ≤ binaryFeatureMass population feature := by
  unfold binaryFeatureMass
  positivity

/-- Below one half, calibrated positive mass is at most calibrated negative mass. -/
theorem IsBinaryOutcomeLikelihood.trueMass_le_falseMass_of_le_half
    {Feature : Type*} {population : PMF (Feature × Bool)}
    {likelihood : Feature → ℝ}
    (hcalibrated : IsBinaryOutcomeLikelihood population likelihood)
    (feature : Feature) (hlikelihood : likelihood feature ≤ (1 : ℝ) / 2) :
    (population (feature, true)).toReal ≤
      (population (feature, false)).toReal := by
  have hmass := binaryFeatureMass_nonneg population feature
  have hcalibration := hcalibrated feature
  unfold binaryFeatureMass at hmass hcalibration
  nlinarith

/-- Above one half, calibrated negative mass is at most calibrated positive mass. -/
theorem IsBinaryOutcomeLikelihood.falseMass_le_trueMass_of_half_le
    {Feature : Type*} {population : PMF (Feature × Bool)}
    {likelihood : Feature → ℝ}
    (hcalibrated : IsBinaryOutcomeLikelihood population likelihood)
    (feature : Feature) (hlikelihood : (1 : ℝ) / 2 ≤ likelihood feature) :
    (population (feature, false)).toReal ≤
      (population (feature, true)).toReal := by
  have hmass := binaryFeatureMass_nonneg population feature
  have hcalibration := hcalibrated feature
  unfold binaryFeatureMass at hmass hcalibration
  nlinarith

/-- A positive calibrated likelihood turns positive feature mass into positive-label mass. -/
theorem IsBinaryOutcomeLikelihood.trueMass_pos_of_featureMass_pos
    {Feature : Type*} {population : PMF (Feature × Bool)}
    {likelihood : Feature → ℝ}
    (hcalibrated : IsBinaryOutcomeLikelihood population likelihood)
    (feature : Feature) (hlikelihood : 0 < likelihood feature)
    (hmass : 0 < binaryFeatureMass population feature) :
    0 < (population (feature, true)).toReal := by
  rw [hcalibrated feature]
  exact mul_pos hlikelihood hmass

/--
Removing only decisions at likelihood at most one half weakly increases
accuracy.  `later` accepts a subset of the features accepted by `earlier`.
-/
theorem binaryDecisionAccuracy_le_of_nested_of_removed_le_half
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {population : PMF (Feature × Bool)} {likelihood : Feature → ℝ}
    (hcalibrated : IsBinaryOutcomeLikelihood population likelihood)
    (earlier later : Feature → Bool)
    (hnested : ∀ feature, later feature = true → earlier feature = true)
    (hremoved : ∀ feature, earlier feature = true → later feature = false →
      likelihood feature ≤ (1 : ℝ) / 2) :
    binaryDecisionAccuracy population earlier ≤
      binaryDecisionAccuracy population later := by
  rw [binaryDecisionAccuracy_eq_sum_feature_mass,
    binaryDecisionAccuracy_eq_sum_feature_mass]
  apply Finset.sum_le_sum
  intro feature _
  cases hearlier : earlier feature <;> cases hlater : later feature
  · simp
  · have : earlier feature = true := hnested feature hlater
    simp [hearlier] at this
  · simpa [hearlier, hlater] using
      hcalibrated.trueMass_le_falseMass_of_le_half feature
        (hremoved feature hearlier hlater)
  · simp

/--
Removing only decisions at likelihood at least one half weakly decreases
accuracy.
-/
theorem binaryDecisionAccuracy_mono_of_nested_of_half_le_removed
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {population : PMF (Feature × Bool)} {likelihood : Feature → ℝ}
    (hcalibrated : IsBinaryOutcomeLikelihood population likelihood)
    (earlier later : Feature → Bool)
    (hnested : ∀ feature, later feature = true → earlier feature = true)
    (hremoved : ∀ feature, earlier feature = true → later feature = false →
      (1 : ℝ) / 2 ≤ likelihood feature) :
    binaryDecisionAccuracy population later ≤
      binaryDecisionAccuracy population earlier := by
  rw [binaryDecisionAccuracy_eq_sum_feature_mass,
    binaryDecisionAccuracy_eq_sum_feature_mass]
  apply Finset.sum_le_sum
  intro feature _
  cases hearlier : earlier feature <;> cases hlater : later feature
  · simp
  · have : earlier feature = true := hnested feature hlater
    simp [hearlier] at this
  · simpa [hearlier, hlater] using
      hcalibrated.falseMass_le_trueMass_of_half_le feature
        (hremoved feature hearlier hlater)
  · simp

/--
Calibrated accuracy is quasiconcave along any nested chain of likelihood-upper
decision sets.  The ternary formulation does not require the index type itself
to be finite or an optimizer to have been selected.
-/
theorem binaryDecisionAccuracy_quasiconcave_of_nested_upper
    {Feature Index : Type*} [Fintype Feature] [DecidableEq Feature]
    [LinearOrder Index]
    {population : PMF (Feature × Bool)} {likelihood : Feature → ℝ}
    (hcalibrated : IsBinaryOutcomeLikelihood population likelihood)
    (decision : Index → Feature → Bool)
    (hnested : ∀ {lower upper}, lower ≤ upper → ∀ feature,
      decision upper feature = true → decision lower feature = true)
    (hupper : ∀ index {lowerFeature higherFeature},
      likelihood lowerFeature ≤ likelihood higherFeature →
      decision index lowerFeature = true → decision index higherFeature = true)
    {first middle last : Index} (hfirstMiddle : first ≤ middle)
    (hmiddleLast : middle ≤ last) :
    min (binaryDecisionAccuracy population (decision first))
        (binaryDecisionAccuracy population (decision last)) ≤
      binaryDecisionAccuracy population (decision middle) := by
  classical
  by_cases hremovedLow : ∀ feature,
      decision first feature = true → decision middle feature = false →
        likelihood feature ≤ (1 : ℝ) / 2
  · exact (min_le_left _ _).trans
      (binaryDecisionAccuracy_le_of_nested_of_removed_le_half
        hcalibrated (decision first) (decision middle)
        (hnested hfirstMiddle) hremovedLow)
  · push Not at hremovedLow
    obtain ⟨boundary, hfirstAccepted, hmiddleRejected, hboundaryHigh⟩ := hremovedLow
    have hlaterHigh : ∀ feature,
        decision middle feature = true → decision last feature = false →
          (1 : ℝ) / 2 ≤ likelihood feature := by
      intro feature hmiddleAccepted _
      have hboundaryLe : likelihood boundary ≤ likelihood feature := by
        by_contra hnot
        have hfeatureLe : likelihood feature ≤ likelihood boundary := le_of_not_ge hnot
        have := hupper middle hfeatureLe hmiddleAccepted
        exact Bool.false_ne_true (hmiddleRejected.symm.trans this)
      exact hboundaryHigh.le.trans hboundaryLe
    exact (min_le_right _ _).trans
      (binaryDecisionAccuracy_mono_of_nested_of_half_le_removed
        hcalibrated (decision middle) (decision last)
        (hnested hmiddleLast) hlaterHigh)

/-- Decisions agreeing at every positive-mass feature have equal accuracy. -/
theorem binaryDecisionAccuracy_eq_of_eq_on_positive_featureMass
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (population : PMF (Feature × Bool)) (first second : Feature → Bool)
    (hagrees : ∀ feature, 0 < binaryFeatureMass population feature →
      first feature = second feature) :
    binaryDecisionAccuracy population first =
      binaryDecisionAccuracy population second := by
  rw [binaryDecisionAccuracy_eq_sum_feature_mass,
    binaryDecisionAccuracy_eq_sum_feature_mass]
  apply Finset.sum_congr rfl
  intro feature _
  by_cases hmass : 0 < binaryFeatureMass population feature
  · rw [hagrees feature hmass]
  · have hmassZero : binaryFeatureMass population feature = 0 :=
      le_antisymm (le_of_not_gt hmass) (binaryFeatureMass_nonneg population feature)
    have hfalse : (population (feature, false)).toReal = 0 := by
      unfold binaryFeatureMass at hmassZero
      have hfalseNonneg : 0 ≤ (population (feature, false)).toReal := by positivity
      have htrueNonneg : 0 ≤ (population (feature, true)).toReal := by positivity
      linarith
    have htrue : (population (feature, true)).toReal = 0 := by
      unfold binaryFeatureMass at hmassZero
      have hfalseNonneg : 0 ≤ (population (feature, false)).toReal := by positivity
      have htrueNonneg : 0 ≤ (population (feature, true)).toReal := by positivity
      linarith
    simp [hfalse, htrue]

/-- Unequal accuracies expose a positive-mass feature on which the decisions differ. -/
theorem exists_positive_featureMass_of_binaryDecisionAccuracy_ne
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (population : PMF (Feature × Bool)) (first second : Feature → Bool)
    (hne : binaryDecisionAccuracy population first ≠
      binaryDecisionAccuracy population second) :
    ∃ feature, 0 < binaryFeatureMass population feature ∧
      first feature ≠ second feature := by
  classical
  by_contra hnot
  apply hne
  apply binaryDecisionAccuracy_eq_of_eq_on_positive_featureMass
  intro feature hmass
  by_contra hdiff
  exact hnot ⟨feature, hmass, hdiff⟩

end AppliedModelingLib

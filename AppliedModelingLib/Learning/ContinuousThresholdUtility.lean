import AppliedModelingLib.Learning.OutcomeMonotoneThreshold
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Tactic.Linarith

/-!
# Calibrated continuous threshold utility

This module isolates the order argument behind the lower-threshold portion of
strategic-classification utility comparisons.  Under calibration, the accuracy
of accepting an individual of likelihood `l` is `l`, while rejecting them has
accuracy `1 - l`.  If raising a threshold only removes strategic acceptances
and every individual whose *original* likelihood is at least the published
threshold is accepted, then raising a threshold below one half weakly improves
that accuracy.

The result deliberately takes integrability and the calibration realization as
explicit inputs.  They are analytic/model bridges in a continuous population,
not consequences of threshold order alone.

## Reused library result and licence

This proof invokes Mathlib's `integral_mono_ae` and, for the joint
feature/label bridge, `setIntegral_condExp`, `integral_map`, `condExp_mono`,
and `condExp_nonneg`; its regularity lemmas invoke `Measurable.ite` and
`Integrable.of_bound` (rather than
reproducing their measure-theoretic proofs):
<https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean>.
<https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.lean>.
<https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/MeasurableSpace/Basic.lean>.
<https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/IntegrableOn.lean>.
Mathlib is licensed under Apache-2.0:
<https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/LICENSE>.
No external proof text or code is copied here.
-/

namespace AppliedModelingLib

open MeasureTheory

/-- Accuracy of a threshold-indexed decision under a calibrated population
likelihood.  The decision can encode strategic response and therefore need not
be a function of likelihood alone. -/
noncomputable def calibratedDecisionAccuracy {Feature : Type*} [MeasurableSpace Feature]
    (population : Measure Feature) (likelihood : Feature → ℝ) (decision : Feature → Bool) : ℝ :=
  ∫ individual, if decision individual = true then likelihood individual else 1 - likelihood individual
    ∂population

/-- Accuracy of a decision after observing an outcome with a Boolean label. -/
noncomputable def labelledDecisionAccuracy {Ω : Type*} [MeasurableSpace Ω]
    (joint : Measure Ω) (decision label : Ω → Bool) : ℝ :=
  ∫ outcome, if decision outcome = label outcome then 1 else 0 ∂joint

/--
The real indicator of a measurable Boolean label is integrable under a finite
population law.  This discharges the label-integrability premise needed by the
conditional-expectation calibration bridge in ordinary binary classification.
-/
theorem integrable_boolLabelIndicator_of_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (joint : Measure Ω) [IsFiniteMeasure joint] (label : Ω → Bool)
    (hlabel : Measurable label) :
    Integrable (fun outcome => if label outcome = true then (1 : ℝ) else 0) joint := by
  have hpositive : MeasurableSet {outcome | label outcome = true} :=
    hlabel (measurableSet_singleton true)
  have hscoreMeasurable : Measurable
      (fun outcome => if label outcome = true then (1 : ℝ) else 0) :=
    Measurable.ite hpositive measurable_const measurable_const
  apply Integrable.of_bound hscoreMeasurable.aestronglyMeasurable 1
  filter_upwards [] with outcome
  by_cases hpositive : label outcome = true <;> simp [hpositive]

/--
If likelihood is the conditional expectation of a measurable Boolean label
given a feature map, then its feature-marginal values lie in `[0,1]` almost
everywhere.  This is the measure-theoretic probability-range consequence of
`ℓ(x) = P(Y = 1 | X = x)`.
-/
theorem ae_unitInterval_of_featureCondExp_bool
    {Ω Feature : Type*} [mΩ : MeasurableSpace Ω] [mFeature : MeasurableSpace Feature]
    (joint : Measure Ω) [IsFiniteMeasure joint]
    (feature : Ω → Feature) (label : Ω → Bool) (likelihood : Feature → ℝ)
    (hfeature : Measurable feature)
    (hlabel : Measurable label)
    (hlikelihood : Measurable likelihood)
    (hconditional : (fun outcome => likelihood (feature outcome)) =ᵐ[joint]
      joint[(fun observation => if label observation = true then (1 : ℝ) else 0) |
        MeasurableSpace.comap feature mFeature]) :
    ∀ᵐ individual ∂Measure.map feature joint, likelihood individual ∈ Set.Icc (0 : ℝ) 1 := by
  let y : Ω → ℝ := fun outcome => if label outcome = true then 1 else 0
  have hyIntegrable : Integrable y joint :=
    integrable_boolLabelIndicator_of_measurable joint label hlabel
  have hyNonneg : 0 ≤ᵐ[joint] y := by
    filter_upwards [] with outcome
    by_cases hpositive : label outcome = true <;> simp [y, hpositive]
  have hyLeOne : y ≤ᵐ[joint] (fun _ : Ω => (1 : ℝ)) := by
    filter_upwards [] with outcome
    by_cases hpositive : label outcome = true <;> simp [y, hpositive]
  have hcondNonneg : 0 ≤ᵐ[joint]
      joint[y | MeasurableSpace.comap feature mFeature] :=
    condExp_nonneg (m := MeasurableSpace.comap feature mFeature) hyNonneg
  have hcondLe : joint[y | MeasurableSpace.comap feature mFeature] ≤ᵐ[joint]
      (fun _ : Ω => (1 : ℝ)) := by
    have hmon := condExp_mono (m := MeasurableSpace.comap feature mFeature)
      hyIntegrable (integrable_const 1) hyLeOne
    simpa only [condExp_const hfeature.comap_le] using hmon
  have hcomposedRange : ∀ᵐ outcome ∂joint,
      likelihood (feature outcome) ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [hconditional, hcondNonneg, hcondLe] with outcome hconditional hnonneg hle
    rw [hconditional]
    exact ⟨hnonneg, hle⟩
  exact (MeasureTheory.ae_map_iff hfeature.aemeasurable
    (hlikelihood measurableSet_Icc)).mpr hcomposedRange

/--
Law of total probability for a Boolean label: a decision measurable with
respect to a sub-sigma-algebra has the same accuracy when its label is replaced
by that label's conditional expectation on the sub-sigma-algebra.
-/
theorem labelledDecisionAccuracy_eq_conditionalScore
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (joint : Measure Ω) [IsFiniteMeasure joint]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (decision label : Ω → Bool)
    (haccepted : @MeasurableSet Ω m {outcome | decision outcome = true})
    (hlabelIntegrable : Integrable
      (fun outcome => if label outcome = true then (1 : ℝ) else 0) joint) :
    @labelledDecisionAccuracy Ω mΩ joint decision label =
      ∫ outcome,
        if decision outcome = true then
          joint[(fun observation => if label observation = true then (1 : ℝ) else 0) | m] outcome
        else 1 - joint[(fun observation => if label observation = true then (1 : ℝ) else 0) | m] outcome
          ∂joint := by
  let y : Ω → ℝ := fun outcome => if label outcome = true then 1 else 0
  let likelihood : Ω → ℝ := joint[y | m]
  let accepted : Set Ω := {outcome | decision outcome = true}
  have honeIntegrable : Integrable (fun _ : Ω => (1 : ℝ)) joint := integrable_const 1
  have hrejectYIntegrable : Integrable (fun outcome => 1 - y outcome) joint :=
    honeIntegrable.sub hlabelIntegrable
  have hlikelihoodIntegrable : Integrable likelihood joint := integrable_condExp
  have hrejectLikelihoodIntegrable : Integrable (fun outcome => 1 - likelihood outcome) joint :=
    honeIntegrable.sub hlikelihoodIntegrable
  have hacceptedSet : @MeasurableSet Ω m accepted := haccepted
  have hacceptedAmbient : @MeasurableSet Ω mΩ accepted := hm accepted hacceptedSet
  have hscoreY :
      @labelledDecisionAccuracy Ω mΩ joint decision label =
        (∫ outcome in accepted, y outcome ∂joint) +
          ∫ outcome in acceptedᶜ, 1 - y outcome ∂joint := by
    unfold labelledDecisionAccuracy
    calc
      (∫ outcome, if decision outcome = label outcome then 1 else 0 ∂joint) =
          ∫ outcome, accepted.indicator y outcome +
            acceptedᶜ.indicator (fun observation => 1 - y observation) outcome ∂joint := by
              apply integral_congr_ae
              filter_upwards [] with outcome
              by_cases hdecision : decision outcome = true <;>
                by_cases hlabel : label outcome = true <;>
                simp [accepted, y, hdecision, hlabel]
      _ = (∫ outcome, accepted.indicator y outcome ∂joint) +
          ∫ outcome, acceptedᶜ.indicator (fun observation => 1 - y observation) outcome ∂joint :=
        integral_add (hlabelIntegrable.indicator hacceptedAmbient)
          (hrejectYIntegrable.indicator hacceptedAmbient.compl)
      _ = (∫ outcome in accepted, y outcome ∂joint) +
          ∫ outcome in acceptedᶜ, 1 - y outcome ∂joint := by
        rw [integral_indicator hacceptedAmbient, integral_indicator hacceptedAmbient.compl]
  have hscoreLikelihood :
      (∫ outcome,
        if decision outcome = true then likelihood outcome else 1 - likelihood outcome ∂joint) =
        (∫ outcome in accepted, likelihood outcome ∂joint) +
          ∫ outcome in acceptedᶜ, 1 - likelihood outcome ∂joint := by
    calc
      (∫ outcome,
        if decision outcome = true then likelihood outcome else 1 - likelihood outcome ∂joint) =
          ∫ outcome, accepted.indicator likelihood outcome +
            acceptedᶜ.indicator (fun observation => 1 - likelihood observation) outcome ∂joint := by
              apply integral_congr_ae
              filter_upwards [] with outcome
              by_cases hdecision : decision outcome = true <;>
                simp [accepted, hdecision]
      _ = (∫ outcome, accepted.indicator likelihood outcome ∂joint) +
          ∫ outcome, acceptedᶜ.indicator (fun observation => 1 - likelihood observation) outcome ∂joint :=
        integral_add (hlikelihoodIntegrable.indicator hacceptedAmbient)
          (hrejectLikelihoodIntegrable.indicator hacceptedAmbient.compl)
      _ = (∫ outcome in accepted, likelihood outcome ∂joint) +
          ∫ outcome in acceptedᶜ, 1 - likelihood outcome ∂joint := by
        rw [integral_indicator hacceptedAmbient, integral_indicator hacceptedAmbient.compl]
  have hacceptedLikelihood :
      ∫ outcome in accepted, likelihood outcome ∂joint =
        ∫ outcome in accepted, y outcome ∂joint :=
    setIntegral_condExp hm hlabelIntegrable hacceptedSet
  have hrejectedLikelihood :
      ∫ outcome in acceptedᶜ, 1 - likelihood outcome ∂joint =
        ∫ outcome in acceptedᶜ, 1 - y outcome ∂joint := by
    calc
      ∫ outcome in acceptedᶜ, 1 - likelihood outcome ∂joint =
          (∫ _outcome in acceptedᶜ, (1 : ℝ) ∂joint) -
            ∫ outcome in acceptedᶜ, likelihood outcome ∂joint :=
        integral_sub honeIntegrable.integrableOn hlikelihoodIntegrable.integrableOn
      _ = (∫ _outcome in acceptedᶜ, (1 : ℝ) ∂joint) -
            ∫ outcome in acceptedᶜ, y outcome ∂joint := by
        rw [setIntegral_condExp hm hlabelIntegrable hacceptedSet.compl]
      _ = ∫ outcome in acceptedᶜ, 1 - y outcome ∂joint :=
        (integral_sub honeIntegrable.integrableOn hlabelIntegrable.integrableOn).symm
  change @labelledDecisionAccuracy Ω mΩ joint decision label =
    ∫ outcome, if decision outcome = true then likelihood outcome else 1 - likelihood outcome ∂joint
  calc
    @labelledDecisionAccuracy Ω mΩ joint decision label =
        (∫ outcome in accepted, y outcome ∂joint) +
          ∫ outcome in acceptedᶜ, 1 - y outcome ∂joint := hscoreY
    _ = (∫ outcome in accepted, likelihood outcome ∂joint) +
          ∫ outcome in acceptedᶜ, 1 - likelihood outcome ∂joint := by
      rw [hacceptedLikelihood, hrejectedLikelihood]
    _ = ∫ outcome, if decision outcome = true then likelihood outcome
          else 1 - likelihood outcome ∂joint := hscoreLikelihood.symm

/--
A joint feature/label law realizes calibrated decision accuracy when the
likelihood is a version of the conditional expectation of the Boolean label
given the feature sigma-algebra.
-/
theorem labelledDecisionAccuracy_eq_calibratedDecisionAccuracy_of_featureCondExp
    {Ω Feature : Type*} [mΩ : MeasurableSpace Ω] [mFeature : MeasurableSpace Feature]
    (joint : Measure Ω) [IsFiniteMeasure joint]
    (feature : Ω → Feature) (label : Ω → Bool) (decision : Feature → Bool)
    (likelihood : Feature → ℝ)
    (hfeature : Measurable feature)
    (haccepted : @MeasurableSet Ω (MeasurableSpace.comap feature mFeature)
      {outcome | decision (feature outcome) = true})
    (hlabelIntegrable : Integrable
      (fun outcome => if label outcome = true then (1 : ℝ) else 0) joint)
    (hconditional : (fun outcome => likelihood (feature outcome)) =ᵐ[joint]
      joint[(fun observation => if label observation = true then (1 : ℝ) else 0) |
        MeasurableSpace.comap feature mFeature])
    (hscoreMeasurable : AEStronglyMeasurable
      (fun individual => if decision individual = true then likelihood individual
        else 1 - likelihood individual)
      (Measure.map feature joint)) :
    @labelledDecisionAccuracy Ω mΩ joint (decision ∘ feature) label =
      @calibratedDecisionAccuracy Feature mFeature (Measure.map feature joint) likelihood decision := by
  have hconditionalScore := labelledDecisionAccuracy_eq_conditionalScore
    joint (MeasurableSpace.comap feature mFeature) hfeature.comap_le
    (decision ∘ feature) label haccepted hlabelIntegrable
  calc
    @labelledDecisionAccuracy Ω mΩ joint (decision ∘ feature) label =
        ∫ outcome,
          if decision (feature outcome) = true then
            joint[(fun observation => if label observation = true then (1 : ℝ) else 0) |
              MeasurableSpace.comap feature mFeature] outcome
          else 1 - joint[(fun observation => if label observation = true then (1 : ℝ) else 0) |
              MeasurableSpace.comap feature mFeature] outcome ∂joint := hconditionalScore
    _ = ∫ outcome,
          if decision (feature outcome) = true then likelihood (feature outcome)
          else 1 - likelihood (feature outcome) ∂joint := by
      apply integral_congr_ae
      filter_upwards [hconditional] with outcome hlikelihood
      simp [hlikelihood]
    _ = @calibratedDecisionAccuracy Feature mFeature (Measure.map feature joint) likelihood decision := by
      unfold calibratedDecisionAccuracy
      exact (integral_map hfeature.aemeasurable hscoreMeasurable).symm

/--
An institutional-utility comparison stated as joint label accuracy transfers
to calibrated score accuracy whenever the feature likelihood is a conditional
expectation version of the label.  This is the reusable comparison form of
the law-of-total-probability bridge above.
-/
theorem calibratedDecisionAccuracy_lt_of_labelledDecisionAccuracy_lt_of_featureCondExp
    {Ω Feature : Type*} [mΩ : MeasurableSpace Ω] [mFeature : MeasurableSpace Feature]
    (joint : Measure Ω) [IsFiniteMeasure joint]
    (feature : Ω → Feature) (label : Ω → Bool)
    (lowerDecision upperDecision : Feature → Bool) (likelihood : Feature → ℝ)
    (hfeature : Measurable feature)
    (hlowerAccepted : @MeasurableSet Ω (MeasurableSpace.comap feature mFeature)
      {outcome | lowerDecision (feature outcome) = true})
    (hupperAccepted : @MeasurableSet Ω (MeasurableSpace.comap feature mFeature)
      {outcome | upperDecision (feature outcome) = true})
    (hlabelIntegrable : Integrable
      (fun outcome => if label outcome = true then (1 : ℝ) else 0) joint)
    (hconditional : (fun outcome => likelihood (feature outcome)) =ᵐ[joint]
      joint[(fun observation => if label observation = true then (1 : ℝ) else 0) |
        MeasurableSpace.comap feature mFeature])
    (hlowerScoreMeasurable : AEStronglyMeasurable
      (fun individual => if lowerDecision individual = true then likelihood individual
        else 1 - likelihood individual)
      (Measure.map feature joint))
    (hupperScoreMeasurable : AEStronglyMeasurable
      (fun individual => if upperDecision individual = true then likelihood individual
        else 1 - likelihood individual)
      (Measure.map feature joint))
    (himproves :
      labelledDecisionAccuracy joint (lowerDecision ∘ feature) label <
        labelledDecisionAccuracy joint (upperDecision ∘ feature) label) :
    calibratedDecisionAccuracy (Measure.map feature joint) likelihood lowerDecision <
      calibratedDecisionAccuracy (Measure.map feature joint) likelihood upperDecision := by
  have hlower := labelledDecisionAccuracy_eq_calibratedDecisionAccuracy_of_featureCondExp
    joint feature label lowerDecision likelihood hfeature hlowerAccepted hlabelIntegrable
      hconditional hlowerScoreMeasurable
  have hupper := labelledDecisionAccuracy_eq_calibratedDecisionAccuracy_of_featureCondExp
    joint feature label upperDecision likelihood hfeature hupperAccepted hlabelIntegrable
      hconditional hupperScoreMeasurable
  calc
    calibratedDecisionAccuracy (Measure.map feature joint) likelihood lowerDecision =
        labelledDecisionAccuracy joint (lowerDecision ∘ feature) label := hlower.symm
    _ < labelledDecisionAccuracy joint (upperDecision ∘ feature) label := himproves
    _ = calibratedDecisionAccuracy (Measure.map feature joint) likelihood upperDecision := hupper

/--
The calibrated score of a measurable decision is measurable whenever its
likelihood is measurable.  The decision need only be represented by its
measurable accepted set.
-/
theorem measurable_calibratedDecisionScore
    {Feature : Type*} [MeasurableSpace Feature]
    (likelihood : Feature → ℝ) (decision : Feature → Bool)
    (hlikelihood : Measurable likelihood)
    (haccepted : MeasurableSet {individual | decision individual = true}) :
    Measurable (fun individual =>
      if decision individual = true then likelihood individual else 1 - likelihood individual) := by
  exact Measurable.ite haccepted hlikelihood (measurable_const.sub hlikelihood)

/--
A measurable calibrated score is integrable under a finite population when
the likelihood lies in the probability interval.  Thus score integrability is
not an extra analytic assumption in an ordinary measurable probability model.
-/
theorem integrable_calibratedDecisionScore_of_unitInterval
    {Feature : Type*} [MeasurableSpace Feature]
    (population : Measure Feature) [IsFiniteMeasure population]
    (likelihood : Feature → ℝ) (decision : Feature → Bool)
    (hscoreMeasurable : AEStronglyMeasurable
      (fun individual => if decision individual = true then likelihood individual
        else 1 - likelihood individual) population)
    (hlikelihoodUnit : ∀ individual, likelihood individual ∈ Set.Icc (0 : ℝ) 1) :
    Integrable (fun individual => if decision individual = true then likelihood individual
      else 1 - likelihood individual) population := by
  apply Integrable.of_bound hscoreMeasurable 1
  filter_upwards [] with individual
  rcases hlikelihoodUnit individual with ⟨hlower, hupper⟩
  by_cases haccepted : decision individual = true
  · rw [if_pos haccepted, Real.norm_eq_abs, abs_of_nonneg hlower]
    exact hupper
  · have hnonneg : 0 ≤ 1 - likelihood individual := by linarith
    rw [if_neg haccepted, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    linarith

/--
The almost-everywhere probability-range version of
`integrable_calibratedDecisionScore_of_unitInterval`.  This is the form
obtained directly from a conditional-probability likelihood.
-/
theorem integrable_calibratedDecisionScore_of_ae_unitInterval
    {Feature : Type*} [MeasurableSpace Feature]
    (population : Measure Feature) [IsFiniteMeasure population]
    (likelihood : Feature → ℝ) (decision : Feature → Bool)
    (hscoreMeasurable : AEStronglyMeasurable
      (fun individual => if decision individual = true then likelihood individual
        else 1 - likelihood individual) population)
    (hlikelihoodUnit : ∀ᵐ individual ∂population, likelihood individual ∈ Set.Icc (0 : ℝ) 1) :
    Integrable (fun individual => if decision individual = true then likelihood individual
      else 1 - likelihood individual) population := by
  apply Integrable.of_bound hscoreMeasurable 1
  filter_upwards [hlikelihoodUnit] with individual hunit
  rcases hunit with ⟨hlower, hupper⟩
  by_cases haccepted : decision individual = true
  · rw [if_pos haccepted, Real.norm_eq_abs, abs_of_nonneg hlower]
    exact hupper
  · have hnonneg : 0 ≤ 1 - likelihood individual := by linarith
    rw [if_neg haccepted, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    linarith

/--
Pulling a measurable accepted set back along a feature map makes it measurable
for the feature sigma-algebra.  This supplies the conditional-expectation
bridge's sub-sigma-algebra premise from a feature-level classifier.
-/
theorem measurableSet_featurePreimage_of_measurableSet
    {Ω Feature : Type*} [MeasurableSpace Ω] [MeasurableSpace Feature]
    (feature : Ω → Feature) (decision : Feature → Bool)
    (haccepted : MeasurableSet {individual | decision individual = true}) :
    @MeasurableSet Ω (MeasurableSpace.comap feature inferInstance)
      {outcome | decision (feature outcome) = true} := by
  apply MeasurableSpace.measurableSet_comap.mpr
  exact ⟨{individual | decision individual = true}, haccepted, rfl⟩

/-- Final threshold decision induced by a chosen strategic response. This
definition is carrier-general; measurability is supplied separately through
the integrability assumptions on utility. -/
noncomputable def acceptanceFavoringLikelihoodThresholdResponseDecision {Feature : Type*}
    (likelihood : Feature → ℝ) (response : ℝ → Feature → Feature)
    (threshold : ℝ) (individual : Feature) : Bool :=
  likelihoodThresholdClassifier likelihood threshold (response threshold individual)

/--
The accepted-decision set is measurable when both the likelihood and the
selected response at the published threshold are measurable.  This is the
ordinary regularity bridge for a deterministic strategic response.
-/
theorem measurableSet_acceptanceFavoringLikelihoodThresholdResponseDecision
    {Feature : Type*} [MeasurableSpace Feature]
    (likelihood : Feature → ℝ) (response : ℝ → Feature → Feature)
    (threshold : ℝ)
    (hlikelihood : Measurable likelihood)
    (hresponse : Measurable (response threshold)) :
    MeasurableSet {individual |
      acceptanceFavoringLikelihoodThresholdResponseDecision likelihood response threshold individual = true} := by
  simpa only [acceptanceFavoringLikelihoodThresholdResponseDecision,
    likelihoodThresholdClassifier_eq_true_iff] using
    ((hlikelihood.comp hresponse) measurableSet_Ici)

/--
Under the source tie convention, final acceptance is exactly reachability of a
threshold-qualified action at cost at most the unit classification benefit. A
selected response in that convention is already a pointwise global best
response, so the statement works on an arbitrary feature carrier.
-/
theorem acceptanceFavoringLikelihoodThresholdResponseDecision_eq_true_iff
    {Feature : Type*} {likelihood : Feature → ℝ} {cost : Feature → Feature → ℝ}
    (response : ℝ → Feature → Feature)
    (hcost : IsOutcomeMonotoneCost likelihood cost)
    (hresponse : ∀ threshold individual,
      IsAcceptanceFavoringStrategicBestResponse
        (likelihoodThresholdClassifier likelihood threshold) cost individual
        (response threshold individual))
    (threshold : ℝ) (individual : Feature) :
    acceptanceFavoringLikelihoodThresholdResponseDecision likelihood response threshold individual = true ↔
      ∃ action, threshold ≤ likelihood action ∧ cost individual action ≤ 1 := by
  unfold acceptanceFavoringLikelihoodThresholdResponseDecision
  simpa only [likelihoodThresholdClassifier_eq_true_iff] using
    (IsAcceptanceFavoringStrategicBestResponse.accepted_iff_exists_cost_le_one
      (hresponse threshold individual)
      hcost.cost_nonneg hcost.cost_self)

/--
If an upper threshold's accepted individuals are also accepted at a lower
threshold, and an individual whose original likelihood is at least the
published threshold is always accepted, then raising a threshold no higher than
one half weakly raises calibrated decision accuracy.
-/
theorem calibratedDecisionAccuracy_mono_below_half
    {Feature : Type*} [MeasurableSpace Feature]
    (population : Measure Feature) (likelihood : Feature → ℝ) (decision : ℝ → Feature → Bool)
    {lowerThreshold upperThreshold : ℝ}
    (hupperHalf : upperThreshold ≤ (1 : ℝ) / 2)
    (hnested : ∀ individual,
      decision upperThreshold individual = true → decision lowerThreshold individual = true)
    (hselfAccepts : ∀ threshold individual,
      threshold ≤ likelihood individual → decision threshold individual = true)
    (hlowerIntegrable : Integrable
      (fun individual => if decision lowerThreshold individual = true then likelihood individual
        else 1 - likelihood individual) population)
    (hupperIntegrable : Integrable
      (fun individual => if decision upperThreshold individual = true then likelihood individual
        else 1 - likelihood individual) population) :
    calibratedDecisionAccuracy population likelihood (decision lowerThreshold) ≤
      calibratedDecisionAccuracy population likelihood (decision upperThreshold) := by
  unfold calibratedDecisionAccuracy
  apply integral_mono_ae hlowerIntegrable hupperIntegrable
  filter_upwards [] with individual
  by_cases hupper : decision upperThreshold individual = true
  · have hlower := hnested individual hupper
    simp [hupper, hlower]
  by_cases hlower : decision lowerThreshold individual = true
  · have hlikelihoodLtUpper : likelihood individual < upperThreshold := by
      by_contra hnot
      exact hupper (hselfAccepts upperThreshold individual (le_of_not_gt hnot))
    have hlikelihoodHalf : likelihood individual ≤ (1 : ℝ) / 2 :=
      hlikelihoodLtUpper.le.trans hupperHalf
    simp [hupper, hlower]
    linarith
  · simp [hupper, hlower]

/--
A strict improvement over the half-threshold baseline is impossible at or
below one half under calibrated, nested, self-accepting threshold decisions.
-/
theorem half_lt_threshold_of_calibratedDecisionAccuracy_gt_half
    {Feature : Type*} [MeasurableSpace Feature]
    (population : Measure Feature) (likelihood : Feature → ℝ)
    (decision : ℝ → Feature → Bool) (threshold : ℝ)
    (hnested : ∀ {lowerThreshold upperThreshold individual},
      lowerThreshold ≤ upperThreshold →
      decision upperThreshold individual = true → decision lowerThreshold individual = true)
    (hselfAccepts : ∀ threshold individual,
      threshold ≤ likelihood individual → decision threshold individual = true)
    (hhalfIntegrable : Integrable
      (fun individual => if decision ((1 : ℝ) / 2) individual = true then likelihood individual
        else 1 - likelihood individual) population)
    (hthresholdIntegrable : Integrable
      (fun individual => if decision threshold individual = true then likelihood individual
        else 1 - likelihood individual) population)
    (himproves :
      calibratedDecisionAccuracy population likelihood (decision ((1 : ℝ) / 2)) <
        calibratedDecisionAccuracy population likelihood (decision threshold)) :
    (1 : ℝ) / 2 < threshold := by
  by_contra hnot
  have hthresholdHalf : threshold ≤ (1 : ℝ) / 2 := le_of_not_gt hnot
  have hmono := calibratedDecisionAccuracy_mono_below_half
    population likelihood decision (le_rfl)
    (fun individual haccepted => hnested hthresholdHalf haccepted)
    hselfAccepts hthresholdIntegrable hhalfIntegrable
  exact (not_lt_of_ge hmono) himproves

/--
The same half-threshold conclusion when a paper's institutional-utility
functional is explicitly realized by calibrated score accuracy at the two
thresholds under comparison.
-/
theorem half_lt_threshold_of_continuousUtility_gt_half
    {Feature : Type*} [MeasurableSpace Feature]
    (population : Measure Feature) (likelihood : Feature → ℝ) (decision : ℝ → Feature → Bool)
    (utility : ℝ → ℝ) (threshold : ℝ)
    (hnested : ∀ {lowerThreshold upperThreshold individual},
      lowerThreshold ≤ upperThreshold →
      decision upperThreshold individual = true → decision lowerThreshold individual = true)
    (hselfAccepts : ∀ threshold individual,
      threshold ≤ likelihood individual → decision threshold individual = true)
    (hhalfIntegrable : Integrable
      (fun individual => if decision ((1 : ℝ) / 2) individual = true then likelihood individual
        else 1 - likelihood individual) population)
    (hthresholdIntegrable : Integrable
      (fun individual => if decision threshold individual = true then likelihood individual
        else 1 - likelihood individual) population)
    (hhalfUtility : utility ((1 : ℝ) / 2) =
      calibratedDecisionAccuracy population likelihood (decision ((1 : ℝ) / 2)))
    (hthresholdUtility : utility threshold =
      calibratedDecisionAccuracy population likelihood (decision threshold))
    (himproves : utility ((1 : ℝ) / 2) < utility threshold) :
    (1 : ℝ) / 2 < threshold := by
  apply half_lt_threshold_of_calibratedDecisionAccuracy_gt_half
    population likelihood decision threshold hnested hselfAccepts hhalfIntegrable hthresholdIntegrable
  calc
    calibratedDecisionAccuracy population likelihood (decision ((1 : ℝ) / 2)) =
        utility ((1 : ℝ) / 2) := hhalfUtility.symm
    _ < utility threshold := himproves
    _ = calibratedDecisionAccuracy population likelihood (decision threshold) := hthresholdUtility

/--
The utility-to-threshold bridge specialized to the accepted-response formula
used in the strategic-classification source proof. The formula says that an
individual is finally accepted exactly when some threshold-qualified action can
be reached at cost at most the unit classification benefit.

Outcome-monotonicity supplies the zero cost of staying at an already accepted
feature; the formula itself then supplies both nested final acceptances and
self-acceptance. In a nonfinite feature space, establishing the formula from a
selected best response requires an attainment/selection hypothesis, so it is
kept explicit here rather than silently inferred.
-/
theorem half_lt_threshold_of_continuousUtility_gt_half_of_responseCharacterization
    {Feature : Type*} [MeasurableSpace Feature]
    (population : Measure Feature) (likelihood : Feature → ℝ)
    (cost : Feature → Feature → ℝ) (decision : ℝ → Feature → Bool)
    (utility : ℝ → ℝ) (threshold : ℝ)
    (hcost : IsOutcomeMonotoneCost likelihood cost)
    (hdecision : ∀ threshold individual,
      decision threshold individual = true ↔
        ∃ action, threshold ≤ likelihood action ∧ cost individual action ≤ 1)
    (hhalfIntegrable : Integrable
      (fun individual => if decision ((1 : ℝ) / 2) individual = true then likelihood individual
        else 1 - likelihood individual) population)
    (hthresholdIntegrable : Integrable
      (fun individual => if decision threshold individual = true then likelihood individual
        else 1 - likelihood individual) population)
    (hhalfUtility : utility ((1 : ℝ) / 2) =
      calibratedDecisionAccuracy population likelihood (decision ((1 : ℝ) / 2)))
    (hthresholdUtility : utility threshold =
      calibratedDecisionAccuracy population likelihood (decision threshold))
    (himproves : utility ((1 : ℝ) / 2) < utility threshold) :
    (1 : ℝ) / 2 < threshold := by
  apply half_lt_threshold_of_continuousUtility_gt_half
    population likelihood decision utility threshold
  · intro lowerThreshold upperThreshold individual hlowerUpper haccepted
    obtain ⟨action, haction, hcostAction⟩ :=
      (hdecision upperThreshold individual).mp haccepted
    exact (hdecision lowerThreshold individual).mpr
      ⟨action, hlowerUpper.trans haction, hcostAction⟩
  · intro publishedThreshold individual hthreshold
    apply (hdecision publishedThreshold individual).mpr
    refine ⟨individual, hthreshold, ?_⟩
    rw [hcost.cost_self individual]
    norm_num
  · exact hhalfIntegrable
  · exact hthresholdIntegrable
  · exact hhalfUtility
  · exact hthresholdUtility
  · exact himproves

/--
The continuous utility bridge directly from the source's acceptance-favoring
best-response convention. The response premise expresses the source's
pointwise selected `argmax`; utility integrability remains explicit because no
measurable-selection primitive is assumed.
-/
theorem half_lt_threshold_of_continuousUtility_gt_half_of_acceptanceFavoringResponse
    {Feature : Type*} [MeasurableSpace Feature]
    (population : Measure Feature) (likelihood : Feature → ℝ)
    (cost : Feature → Feature → ℝ) (response : ℝ → Feature → Feature)
    (utility : ℝ → ℝ) (threshold : ℝ)
    (hcost : IsOutcomeMonotoneCost likelihood cost)
    (hresponse : ∀ publishedThreshold individual,
      IsAcceptanceFavoringStrategicBestResponse
        (likelihoodThresholdClassifier likelihood publishedThreshold) cost individual
        (response publishedThreshold individual))
    (hhalfIntegrable : Integrable
      (fun individual =>
        if acceptanceFavoringLikelihoodThresholdResponseDecision likelihood response
          ((1 : ℝ) / 2) individual = true then likelihood individual else 1 - likelihood individual)
      population)
    (hthresholdIntegrable : Integrable
      (fun individual =>
        if acceptanceFavoringLikelihoodThresholdResponseDecision likelihood response
          threshold individual = true then likelihood individual else 1 - likelihood individual)
      population)
    (hhalfUtility : utility ((1 : ℝ) / 2) =
      calibratedDecisionAccuracy population likelihood
        (acceptanceFavoringLikelihoodThresholdResponseDecision likelihood response ((1 : ℝ) / 2)))
    (hthresholdUtility : utility threshold =
      calibratedDecisionAccuracy population likelihood
        (acceptanceFavoringLikelihoodThresholdResponseDecision likelihood response threshold))
    (himproves : utility ((1 : ℝ) / 2) < utility threshold) :
    (1 : ℝ) / 2 < threshold := by
  apply half_lt_threshold_of_continuousUtility_gt_half_of_responseCharacterization
    population likelihood cost
    (acceptanceFavoringLikelihoodThresholdResponseDecision likelihood response)
    utility threshold hcost
  · intro publishedThreshold individual
    exact acceptanceFavoringLikelihoodThresholdResponseDecision_eq_true_iff
      response hcost hresponse publishedThreshold individual
  · exact hhalfIntegrable
  · exact hthresholdIntegrable
  · exact hhalfUtility
  · exact hthresholdUtility
  · exact himproves

/--
Removing only low-likelihood individuals from a measurable decision weakly
raises calibrated accuracy.  Unlike the finite-PMF counterpart, this theorem
works over an arbitrary finite measure once both score functions are
integrable.
-/
theorem calibratedDecisionAccuracy_le_of_nested_of_removed_le_half
    {Feature : Type*} [MeasurableSpace Feature]
    (population : Measure Feature) (likelihood : Feature → ℝ)
    (earlier later : Feature → Bool)
    (hnested : ∀ individual, later individual = true → earlier individual = true)
    (hremoved : ∀ individual, earlier individual = true → later individual = false →
      likelihood individual ≤ (1 : ℝ) / 2)
    (hearlierIntegrable : Integrable
      (fun individual => if earlier individual = true then likelihood individual
        else 1 - likelihood individual) population)
    (hlaterIntegrable : Integrable
      (fun individual => if later individual = true then likelihood individual
        else 1 - likelihood individual) population) :
    calibratedDecisionAccuracy population likelihood earlier ≤
      calibratedDecisionAccuracy population likelihood later := by
  unfold calibratedDecisionAccuracy
  apply integral_mono_ae hearlierIntegrable hlaterIntegrable
  filter_upwards [] with individual
  by_cases hlater : later individual = true
  · have hearlier := hnested individual hlater
    simp [hlater, hearlier]
  by_cases hearlier : earlier individual = true
  · have hlaterFalse : later individual = false := Bool.eq_false_of_not_eq_true hlater
    have hlikelihood := hremoved individual hearlier hlaterFalse
    simp [hlater, hearlier]
    linarith
  · simp [hlater, hearlier]

/--
Removing only high-likelihood individuals from a measurable decision weakly
lowers calibrated accuracy on an arbitrary finite measure.
-/
theorem calibratedDecisionAccuracy_mono_of_nested_of_half_le_removed
    {Feature : Type*} [MeasurableSpace Feature]
    (population : Measure Feature) (likelihood : Feature → ℝ)
    (earlier later : Feature → Bool)
    (hnested : ∀ individual, later individual = true → earlier individual = true)
    (hremoved : ∀ individual, earlier individual = true → later individual = false →
      (1 : ℝ) / 2 ≤ likelihood individual)
    (hearlierIntegrable : Integrable
      (fun individual => if earlier individual = true then likelihood individual
        else 1 - likelihood individual) population)
    (hlaterIntegrable : Integrable
      (fun individual => if later individual = true then likelihood individual
        else 1 - likelihood individual) population) :
    calibratedDecisionAccuracy population likelihood later ≤
      calibratedDecisionAccuracy population likelihood earlier := by
  unfold calibratedDecisionAccuracy
  apply integral_mono_ae hlaterIntegrable hearlierIntegrable
  filter_upwards [] with individual
  by_cases hlater : later individual = true
  · have hearlier := hnested individual hlater
    simp [hlater, hearlier]
  by_cases hearlier : earlier individual = true
  · have hlaterFalse : later individual = false := Bool.eq_false_of_not_eq_true hlater
    have hlikelihood := hremoved individual hearlier hlaterFalse
    simp [hlater, hearlier]
    linarith
  · simp [hlater, hearlier]

/--
Calibrated accuracy is quasiconcave along any nested chain of
likelihood-upper measurable decisions.  This is the arbitrary-measure version
of the order argument behind Theorem 3.1; it deliberately does *not* assert
that a maximizing threshold is attained.
-/
theorem calibratedDecisionAccuracy_quasiconcave_of_nested_upper
    {Feature Index : Type*} [MeasurableSpace Feature] [LinearOrder Index]
    (population : Measure Feature) (likelihood : Feature → ℝ)
    (decision : Index → Feature → Bool)
    (hnested : ∀ {lower upper}, lower ≤ upper → ∀ individual,
      decision upper individual = true → decision lower individual = true)
    (hupper : ∀ index {lowerIndividual higherIndividual},
      likelihood lowerIndividual ≤ likelihood higherIndividual →
      decision index lowerIndividual = true → decision index higherIndividual = true)
    (hintegrable : ∀ index, Integrable
      (fun individual => if decision index individual = true then likelihood individual
        else 1 - likelihood individual) population)
    {first middle last : Index} (hfirstMiddle : first ≤ middle)
    (hmiddleLast : middle ≤ last) :
    min (calibratedDecisionAccuracy population likelihood (decision first))
        (calibratedDecisionAccuracy population likelihood (decision last)) ≤
      calibratedDecisionAccuracy population likelihood (decision middle) := by
  by_cases hremovedLow : ∀ individual,
      decision first individual = true → decision middle individual = false →
        likelihood individual ≤ (1 : ℝ) / 2
  · exact (min_le_left _ _).trans
      (calibratedDecisionAccuracy_le_of_nested_of_removed_le_half
        population likelihood (decision first) (decision middle)
        (hnested hfirstMiddle) hremovedLow (hintegrable first) (hintegrable middle))
  · push Not at hremovedLow
    obtain ⟨boundary, hfirstAccepted, hmiddleRejected, hboundaryHigh⟩ := hremovedLow
    have hlateHigh : ∀ individual,
        decision middle individual = true → decision last individual = false →
          (1 : ℝ) / 2 ≤ likelihood individual := by
      intro individual hmiddleAccepted _
      have hboundaryLe : likelihood boundary ≤ likelihood individual := by
        by_contra hnot
        have hindividualLe : likelihood individual ≤ likelihood boundary := le_of_not_ge hnot
        have hboundaryAccepted := hupper middle hindividualLe hmiddleAccepted
        exact Bool.false_ne_true (hmiddleRejected.symm.trans hboundaryAccepted)
      exact hboundaryHigh.le.trans hboundaryLe
    exact (min_le_right _ _).trans
      (calibratedDecisionAccuracy_mono_of_nested_of_half_le_removed
        population likelihood (decision middle) (decision last)
        (hnested hmiddleLast) hlateHigh (hintegrable middle) (hintegrable last))

/--
The selected acceptance-favoring response to an outcome-monotone cost induces
a nested likelihood-upper decision chain.  Consequently its calibrated utility
is quasiconcave on an arbitrary finite measure whenever the score functions
are integrable.  A separate attainment condition is still required to turn
this conclusion into the source's claimed maximizing threshold.
-/
theorem calibratedDecisionAccuracy_acceptanceFavoringResponse_quasiconcave
    {Feature : Type*} [MeasurableSpace Feature]
    (population : Measure Feature) (likelihood : Feature → ℝ)
    (cost : Feature → Feature → ℝ) (response : ℝ → Feature → Feature)
    (hcost : IsOutcomeMonotoneCost likelihood cost)
    (hresponse : ∀ publishedThreshold individual,
      IsAcceptanceFavoringStrategicBestResponse
        (likelihoodThresholdClassifier likelihood publishedThreshold) cost individual
        (response publishedThreshold individual))
    (hintegrable : ∀ threshold, Integrable
      (fun individual =>
        if acceptanceFavoringLikelihoodThresholdResponseDecision likelihood response threshold individual = true
        then likelihood individual else 1 - likelihood individual) population)
    {first middle last : ℝ} (hfirstMiddle : first ≤ middle)
    (hmiddleLast : middle ≤ last) :
    min (calibratedDecisionAccuracy population likelihood
          (acceptanceFavoringLikelihoodThresholdResponseDecision likelihood response first))
        (calibratedDecisionAccuracy population likelihood
          (acceptanceFavoringLikelihoodThresholdResponseDecision likelihood response last)) ≤
      calibratedDecisionAccuracy population likelihood
        (acceptanceFavoringLikelihoodThresholdResponseDecision likelihood response middle) := by
  apply calibratedDecisionAccuracy_quasiconcave_of_nested_upper
    population likelihood
    (acceptanceFavoringLikelihoodThresholdResponseDecision likelihood response)
  · intro lower upper hlowerUpper individual haccepted
    obtain ⟨action, haction, hactionCost⟩ :=
      (acceptanceFavoringLikelihoodThresholdResponseDecision_eq_true_iff
        response hcost hresponse upper individual).mp haccepted
    exact (acceptanceFavoringLikelihoodThresholdResponseDecision_eq_true_iff
      response hcost hresponse lower individual).mpr
      ⟨action, hlowerUpper.trans haction, hactionCost⟩
  · intro threshold lowerIndividual higherIndividual hlowerHigher haccepted
    obtain ⟨action, haction, hactionCost⟩ :=
      (acceptanceFavoringLikelihoodThresholdResponseDecision_eq_true_iff
        response hcost hresponse threshold lowerIndividual).mp haccepted
    exact (acceptanceFavoringLikelihoodThresholdResponseDecision_eq_true_iff
      response hcost hresponse threshold higherIndividual).mpr
      ⟨action, haction, (hcost.cost_anti_left hlowerHigher action).trans hactionCost⟩
  · exact hintegrable
  · exact hfirstMiddle
  · exact hmiddleLast

/--
An arbitrary classifier and the likelihood threshold at its least accepted
likelihood induce the same final acceptance decision under the source's
acceptance-favoring best-response convention.  The theorem is carrier-general;
the least-accepted-likelihood premise is the explicit attainment bridge that
the finite version of Lemma 3.1 obtains automatically.
-/
theorem acceptanceFavoringResponse_accepted_iff_thresholdResponse_accepted_of_leastLikelihood
    {Feature : Type*} {likelihood : Feature → ℝ} {cost : Feature → Feature → ℝ}
    (classifier : BinaryClassifier Feature) (least : Feature)
    (response thresholdResponse : Feature → Feature)
    (hcost : IsOutcomeMonotoneCost likelihood cost)
    (hresponse : ∀ individual,
      IsAcceptanceFavoringStrategicBestResponse classifier cost individual (response individual))
    (hthresholdResponse : ∀ individual,
      IsAcceptanceFavoringStrategicBestResponse
        (likelihoodThresholdClassifier likelihood (likelihood least)) cost individual
        (thresholdResponse individual))
    (hleastAccepted : classifier least = true)
    (hleast : ∀ accepted, classifier accepted = true → likelihood least ≤ likelihood accepted)
    (individual : Feature) :
    classifier (response individual) = true ↔
      likelihoodThresholdClassifier likelihood (likelihood least)
        (thresholdResponse individual) = true := by
  constructor
  · intro haccepted
    obtain ⟨action, haction, hcostAction⟩ :=
      (hresponse individual).accepted_iff_exists_cost_le_one hcost.cost_nonneg hcost.cost_self |>.mp
        haccepted
    apply (hthresholdResponse individual).accepted_iff_exists_cost_le_one
      hcost.cost_nonneg hcost.cost_self |>.mpr
    refine ⟨action, ?_, hcostAction⟩
    rw [likelihoodThresholdClassifier_eq_true_iff]
    exact hleast action haction
  · intro haccepted
    obtain ⟨action, haction, hcostAction⟩ :=
      (hthresholdResponse individual).accepted_iff_exists_cost_le_one
        hcost.cost_nonneg hcost.cost_self |>.mp haccepted
    apply (hresponse individual).accepted_iff_exists_cost_le_one
      hcost.cost_nonneg hcost.cost_self |>.mpr
    refine ⟨least, hleastAccepted, ?_⟩
    have hleastAction : likelihood least ≤ likelihood action := by
      rw [likelihoodThresholdClassifier_eq_true_iff] at haction
      exact haction
    exact (hcost.cost_mono_right individual hleastAction).trans hcostAction

end AppliedModelingLib

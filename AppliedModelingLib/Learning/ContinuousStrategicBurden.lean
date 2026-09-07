import AppliedModelingLib.Learning.OutcomeMonotoneThreshold
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Continuous strategic social burden

This module gives a carrier-general realization of the minimum manipulation
cost and its population average.  The source definition of social burden uses
a minimum over accepted actions.  On a nonfinite feature space that minimum is
not automatic, so `IsMinimumAcceptedCost` records its existence and universal
minimality explicitly rather than silently replacing it by a finite `min'`.

## Reused library result and licence

The expectation monotonicity proof invokes Mathlib's `integral_mono_ae` from
[`MeasureTheory/Integral/Bochner/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean)
at the repository-pinned Mathlib revision.  Mathlib is licensed under
[Apache-2.0](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/LICENSE).
No external proof text or code is copied here.
-/

namespace AppliedModelingLib

open MeasureTheory

/-- `value` is a realized minimum manipulation cost among accepted actions. -/
def IsMinimumAcceptedCost {Feature : Type*}
    (cost : Feature → Feature → ℝ) (accepted : Feature → Bool)
    (initial : Feature) (value : ℝ) : Prop :=
  (∃ final, accepted final = true ∧ cost initial final = value) ∧
    ∀ final, accepted final = true → value ≤ cost initial final

/--
If `least` is an accepted action whose likelihood is no larger than every
accepted action, outcome monotonicity realizes it as the minimum cost among
that classifier's accepted actions on an arbitrary carrier.
-/
theorem isMinimumAcceptedCost_of_leastAcceptedLikelihood
    {Feature : Type*} {likelihood : Feature → ℝ} {cost : Feature → Feature → ℝ}
    (hcost : IsOutcomeMonotoneCost likelihood cost)
    (classifier : BinaryClassifier Feature) (initial least : Feature)
    (hleastAccepted : classifier least = true)
    (hleast : ∀ accepted, classifier accepted = true → likelihood least ≤ likelihood accepted) :
    IsMinimumAcceptedCost cost classifier initial (cost initial least) := by
  refine ⟨⟨least, hleastAccepted, rfl⟩, ?_⟩
  intro accepted haccepted
  exact hcost.cost_mono_right initial (hleast accepted haccepted)

/--
The same least accepted likelihood realizes the minimum cost for the
outcome-likelihood threshold classifier. This is the arbitrary-carrier
minimum-attainment bridge behind source Lemma 3.1.
-/
theorem isMinimumAcceptedCost_likelihoodThreshold_of_leastAcceptedLikelihood
    {Feature : Type*} {likelihood : Feature → ℝ} {cost : Feature → Feature → ℝ}
    (hcost : IsOutcomeMonotoneCost likelihood cost)
    (initial least : Feature) :
    IsMinimumAcceptedCost cost (likelihoodThresholdClassifier likelihood (likelihood least))
      initial (cost initial least) := by
  refine ⟨⟨least, ?_, rfl⟩, ?_⟩
  · exact (likelihoodThresholdClassifier_eq_true_iff
      likelihood (likelihood least) least).mpr le_rfl
  · intro accepted haccepted
    rw [likelihoodThresholdClassifier_eq_true_iff] at haccepted
    exact hcost.cost_mono_right initial haccepted

/--
If the upper acceptance set is contained in the lower one, its realized
minimum manipulation cost is at least the lower realized minimum.
-/
theorem IsMinimumAcceptedCost.le_of_subset
    {Feature : Type*} {cost : Feature → Feature → ℝ}
    {lowerAccepted upperAccepted : Feature → Bool}
    {initial : Feature} {lowerValue upperValue : ℝ}
    (hlower : IsMinimumAcceptedCost cost lowerAccepted initial lowerValue)
    (hupper : IsMinimumAcceptedCost cost upperAccepted initial upperValue)
    (hsubset : ∀ final, upperAccepted final = true → lowerAccepted final = true) :
    lowerValue ≤ upperValue := by
  obtain ⟨final, hfinalAccepted, hfinalValue⟩ := hupper.1
  calc
    lowerValue ≤ cost initial final := hlower.2 final (hsubset final hfinalAccepted)
    _ = upperValue := hfinalValue

/-- Realized minimum accepted costs are unique. -/
theorem IsMinimumAcceptedCost.eq_of
    {Feature : Type*} {cost : Feature → Feature → ℝ}
    {accepted : Feature → Bool} {initial : Feature} {firstValue secondValue : ℝ}
    (hfirst : IsMinimumAcceptedCost cost accepted initial firstValue)
    (hsecond : IsMinimumAcceptedCost cost accepted initial secondValue) :
    firstValue = secondValue := by
  obtain ⟨firstFinal, hfirstAccepted, hfirstValue⟩ := hfirst.1
  obtain ⟨secondFinal, hsecondAccepted, hsecondValue⟩ := hsecond.1
  apply le_antisymm
  · calc
      firstValue ≤ cost initial secondFinal := hfirst.2 secondFinal hsecondAccepted
      _ = secondValue := hsecondValue
  · calc
      secondValue ≤ cost initial firstFinal := hsecond.2 firstFinal hfirstAccepted
      _ = firstValue := hfirstValue

/-- Positive scaling of a cost positively scales each realized minimum burden. -/
theorem IsMinimumAcceptedCost.const_mul
    {Feature : Type*} {costA costB : Feature → Feature → ℝ}
    {accepted : Feature → Bool} {initial : Feature} {value κ : ℝ}
    (hminimum : IsMinimumAcceptedCost costA accepted initial value)
    (hcostScale : ∀ initial final, costB initial final = κ * costA initial final)
    (hκ : 0 < κ) :
    IsMinimumAcceptedCost costB accepted initial (κ * value) := by
  constructor
  · obtain ⟨final, hfinalAccepted, hfinalValue⟩ := hminimum.1
    refine ⟨final, hfinalAccepted, ?_⟩
    rw [hcostScale, hfinalValue]
  · intro final hfinalAccepted
    rw [hcostScale]
    exact mul_le_mul_of_nonneg_left (hminimum.2 final hfinalAccepted) hκ.le

/-- Expected individual burden under a specified positive-population measure. -/
noncomputable def continuousSocialBurden {Feature : Type*} [MeasurableSpace Feature]
    (positivePopulation : Measure Feature) (individualBurden : Feature → ℝ) : ℝ :=
  ∫ individual, individualBurden individual ∂positivePopulation

/-- Pointwise higher burden weakly raises its integrable population average. -/
theorem continuousSocialBurden_mono_of_forall_le
    {Feature : Type*} [MeasurableSpace Feature]
    (positivePopulation : Measure Feature)
    (lowerBurden upperBurden : Feature → ℝ)
    (hlowerIntegrable : Integrable lowerBurden positivePopulation)
    (hupperIntegrable : Integrable upperBurden positivePopulation)
    (hburden : ∀ individual, lowerBurden individual ≤ upperBurden individual) :
    continuousSocialBurden positivePopulation lowerBurden ≤
      continuousSocialBurden positivePopulation upperBurden := by
  unfold continuousSocialBurden
  apply integral_mono_ae hlowerIntegrable hupperIntegrable
  filter_upwards [] with individual
  exact hburden individual

/--
Pointwise burden improvement is strict at the population level when it occurs
on a set of positive measure.  This is the non-atomic replacement for the
source proof's finite-support step that cites one individual with positive
conditional mass.
-/
theorem continuousSocialBurden_lt_of_forall_le_of_measure_setOf_lt_pos
    {Feature : Type*} [MeasurableSpace Feature]
    (positivePopulation : Measure Feature)
    (lowerBurden upperBurden : Feature → ℝ)
    (hlowerIntegrable : Integrable lowerBurden positivePopulation)
    (hupperIntegrable : Integrable upperBurden positivePopulation)
    (hburden : ∀ individual, lowerBurden individual ≤ upperBurden individual)
    (hstrict : 0 < positivePopulation {individual |
      lowerBurden individual < upperBurden individual}) :
    continuousSocialBurden positivePopulation lowerBurden <
      continuousSocialBurden positivePopulation upperBurden := by
  apply lt_of_le_of_ne
  · exact continuousSocialBurden_mono_of_forall_le positivePopulation
      lowerBurden upperBurden hlowerIntegrable hupperIntegrable hburden
  · intro hequal
    have haequal : lowerBurden =ᵐ[positivePopulation] upperBurden :=
      (integral_eq_iff_of_ae_le hlowerIntegrable hupperIntegrable
        (Filter.Eventually.of_forall hburden)).mp hequal
    have hnull : positivePopulation {individual | lowerBurden individual ≠ upperBurden individual} = 0 :=
      MeasureTheory.ae_iff.mp haequal
    have hsubset : {individual | lowerBurden individual < upperBurden individual} ⊆
        {individual | lowerBurden individual ≠ upperBurden individual} := by
      intro individual hindividual
      exact ne_of_lt hindividual
    have hmeasureLe := MeasureTheory.measure_mono (μ := positivePopulation) hsubset
    rw [hnull] at hmeasureLe
    exact (not_lt_of_ge hmeasureLe) hstrict

/-- A pointwise nonnegative individual burden has nonnegative social burden. -/
theorem continuousSocialBurden_nonneg_of_forall_nonneg
    {Feature : Type*} [MeasurableSpace Feature]
    (positivePopulation : Measure Feature) (individualBurden : Feature → ℝ)
    (hnonneg : ∀ individual, 0 ≤ individualBurden individual) :
    0 ≤ continuousSocialBurden positivePopulation individualBurden := by
  unfold continuousSocialBurden
  apply integral_nonneg_of_ae
  filter_upwards [] with individual
  exact hnonneg individual

/--
The social gap generated by two group-indexed burden functions sharing one
positive-feature population measure.
-/
noncomputable def continuousCostIndexedSocialGap {Feature : Type*} [MeasurableSpace Feature]
    (positivePopulation : Measure Feature) (burdenA burdenB : Feature → ℝ) : ℝ :=
  continuousSocialBurden positivePopulation burdenB -
    continuousSocialBurden positivePopulation burdenA

/-- If group-B burden is a factor `κ` of group-A burden, their social gap is
`(κ - 1)` times group-A social burden. -/
theorem continuousCostIndexedSocialGap_eq_sub_one_mul
    {Feature : Type*} [MeasurableSpace Feature]
    (positivePopulation : Measure Feature) (burdenA burdenB : Feature → ℝ) (κ : ℝ)
    (hscale : ∀ individual, burdenB individual = κ * burdenA individual) :
    continuousCostIndexedSocialGap positivePopulation burdenA burdenB =
      (κ - 1) * continuousSocialBurden positivePopulation burdenA := by
  have hburdenScale : continuousSocialBurden positivePopulation burdenB =
      κ * continuousSocialBurden positivePopulation burdenA := by
    unfold continuousSocialBurden
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with individual
    exact hscale individual
  unfold continuousCostIndexedSocialGap
  rw [hburdenScale]
  ring

/-- A cost-scaled social gap is nonnegative when the base burden is pointwise nonnegative. -/
theorem continuousCostIndexedSocialGap_nonneg_of_scale
    {Feature : Type*} [MeasurableSpace Feature]
    (positivePopulation : Measure Feature) (burdenA burdenB : Feature → ℝ) (κ : ℝ)
    (hscale : ∀ individual, burdenB individual = κ * burdenA individual)
    (hκ : 1 ≤ κ) (hnonneg : ∀ individual, 0 ≤ burdenA individual) :
    0 ≤ continuousCostIndexedSocialGap positivePopulation burdenA burdenB := by
  rw [continuousCostIndexedSocialGap_eq_sub_one_mul positivePopulation burdenA burdenB κ hscale]
  apply mul_nonneg
  · linarith
  · exact continuousSocialBurden_nonneg_of_forall_nonneg positivePopulation burdenA hnonneg

/--
When group-B burden is a fixed cost multiple of group-A burden, its social gap
is nondecreasing along any integrable pointwise-nondecreasing burden family.
-/
theorem continuousCostIndexedSocialGap_mono_of_scale
    {Feature : Type*} [MeasurableSpace Feature]
    (positivePopulation : Measure Feature) (burdenA burdenB : ℝ → Feature → ℝ) (κ : ℝ)
    {lowerThreshold upperThreshold : ℝ}
    (hscale : ∀ threshold individual, burdenB threshold individual =
      κ * burdenA threshold individual)
    (hκ : 1 ≤ κ)
    (hburdenMono : ∀ individual,
      burdenA lowerThreshold individual ≤ burdenA upperThreshold individual)
    (hlowerIntegrable : Integrable (burdenA lowerThreshold) positivePopulation)
    (hupperIntegrable : Integrable (burdenA upperThreshold) positivePopulation) :
    continuousCostIndexedSocialGap positivePopulation
        (burdenA lowerThreshold) (burdenB lowerThreshold) ≤
      continuousCostIndexedSocialGap positivePopulation
        (burdenA upperThreshold) (burdenB upperThreshold) := by
  rw [continuousCostIndexedSocialGap_eq_sub_one_mul positivePopulation
    (burdenA lowerThreshold) (burdenB lowerThreshold) κ (hscale lowerThreshold),
    continuousCostIndexedSocialGap_eq_sub_one_mul positivePopulation
      (burdenA upperThreshold) (burdenB upperThreshold) κ (hscale upperThreshold)]
  apply mul_le_mul_of_nonneg_left
  · exact continuousSocialBurden_mono_of_forall_le positivePopulation
      (burdenA lowerThreshold) (burdenA upperThreshold)
      hlowerIntegrable hupperIntegrable hburdenMono
  · linarith

/--
Under explicit realized-minimum witnesses, social burden is nondecreasing as
an outcome-likelihood threshold rises, on an arbitrary positive-population
measure.
-/
theorem continuousSocialBurden_likelihoodThreshold_mono
    {Feature : Type*} [MeasurableSpace Feature]
    (positivePopulation : Measure Feature) (likelihood : Feature → ℝ)
    (cost : Feature → Feature → ℝ) (individualBurden : ℝ → Feature → ℝ)
    {lowerThreshold upperThreshold : ℝ} (hlowerUpper : lowerThreshold ≤ upperThreshold)
    (hminimum : ∀ threshold initial,
      IsMinimumAcceptedCost cost (likelihoodThresholdClassifier likelihood threshold)
        initial (individualBurden threshold initial))
    (hlowerIntegrable : Integrable (individualBurden lowerThreshold) positivePopulation)
    (hupperIntegrable : Integrable (individualBurden upperThreshold) positivePopulation) :
    continuousSocialBurden positivePopulation (individualBurden lowerThreshold) ≤
      continuousSocialBurden positivePopulation (individualBurden upperThreshold) := by
  apply continuousSocialBurden_mono_of_forall_le positivePopulation
    (individualBurden lowerThreshold) (individualBurden upperThreshold)
    hlowerIntegrable hupperIntegrable
  intro initial
  apply IsMinimumAcceptedCost.le_of_subset
    (hminimum lowerThreshold initial) (hminimum upperThreshold initial)
  intro final haccepted
  rw [likelihoodThresholdClassifier_eq_true_iff] at haccepted ⊢
  exact hlowerUpper.trans haccepted

end AppliedModelingLib

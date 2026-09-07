import GHKR22BiasBounties.MeasureCore
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# Arbitrary-distribution boundary in Observation 4

The paper introduces arbitrary distributions (including regression) and then
states a pointwise characterization of Bayes optimality by performance on every
group.  On an atomless feature law, group integrals identify models only almost
everywhere.  They cannot detect a model changed at one support point.  Thus the
printed pointwise `if and only if` needs an almost-everywhere formulation plus
measurability/regular-conditional assumptions; it is not a theorem as written.

This file gives a concrete checked counterexample on the continuous uniform
probability law on `[0,1]`.  It explains why the main source-facing development
uses finite-support PMFs: there every support point has positive mass, so the
paper's pointwise Observation 4 is meaningful and true.
-/

namespace GHKR22BiasBounties

noncomputable section

open MeasureTheory Set

/-! ## The corrected arbitrary-distribution statement -/

/-- Bayes optimality for a pointwise conditional-risk function, stated in the
only distribution-invariant way available on an arbitrary feature law: almost
everywhere.  The countable action assumption in the equivalence below lets us
combine the action-specific null sets into one common null set. -/
def AEBayesOptimalForRisk {X Y : Type*} [MeasurableSpace X]
    (law : Measure X) (risk : X → Y → ℝ) (current : X → Y) : Prop :=
  ∀ᵐ x ∂law, ∀ prediction : Y,
    risk x (current x) ≤ risk x prediction

/-- Optimality on every measurable subgroup, written without conditional
normalization.  Multiplying the source's conditional comparison by group mass
gives exactly this set-integral comparison. -/
def OptimalOnEveryMeasurableGroupForRisk {X Y : Type*} [MeasurableSpace X]
    (law : Measure X) (risk : X → Y → ℝ) (current : X → Y) : Prop :=
  ∀ group : Set X, MeasurableSet group →
    ∀ alternative : X → Y,
      Integrable (fun x ↦ risk x (alternative x)) law →
        (∫ x in group, risk x (current x) ∂law) ≤
          ∫ x in group, risk x (alternative x) ∂law

/-- Bayes optimality against every integrable alternative model, stated
almost everywhere separately for each alternative.  Unlike the common-null-
set actionwise definition, this formulation is meaningful for an arbitrary
prediction space and is exactly what subgroup-integral comparisons identify. -/
def AEOptimalAgainstEveryIntegrableModelForRisk
    {X Y : Type*} [MeasurableSpace X]
    (law : Measure X) (risk : X → Y → ℝ) (current : X → Y) : Prop :=
  ∀ alternative : X → Y,
    Integrable (fun x ↦ risk x (alternative x)) law →
      (fun x ↦ risk x (current x)) ≤ᵐ[law]
        (fun x ↦ risk x (alternative x))

/-- For an arbitrary prediction space, modelwise almost-everywhere Bayes
optimality is equivalent to optimality on every measurable subgroup. -/
theorem aeOptimalAgainstEveryIntegrableModelForRisk_iff_groupwiseOptimal
    {X Y : Type*} [MeasurableSpace X]
    (law : Measure X) (risk : X → Y → ℝ) (current : X → Y)
    (hcurrent : Integrable (fun x ↦ risk x (current x)) law) :
    AEOptimalAgainstEveryIntegrableModelForRisk law risk current ↔
      OptimalOnEveryMeasurableGroupForRisk law risk current := by
  constructor
  · intro hbayes group _ alternative halternative
    exact setIntegral_mono_ae hcurrent.integrableOn halternative.integrableOn
      (hbayes alternative halternative)
  · intro hgroups alternative halternative
    apply ae_le_of_forall_setIntegral_le hcurrent halternative
    intro group hgroup _
    exact hgroups group hgroup alternative halternative

/-- Corrected arbitrary-distribution form of Observation 4.  For a countable
prediction/action space, almost-everywhere pointwise Bayes optimality is
equivalent to optimality on every measurable subgroup.  The only analytic
hypotheses are integrability of the current conditional risk and of each
constant-action conditional risk; bounded measurable losses under a regular
conditional distribution satisfy these automatically.

The reverse implication tests each constant action on every measurable set
and invokes the standard characterization of almost-everywhere inequalities
by set integrals.  Countability of `Y` then produces a common full-measure set
on which all action comparisons hold. -/
theorem aeBayesOptimalForRisk_iff_optimalOnEveryMeasurableGroupForRisk
    {X Y : Type*} [MeasurableSpace X] [Countable Y]
    (law : Measure X) (risk : X → Y → ℝ) (current : X → Y)
    (hcurrent : Integrable (fun x ↦ risk x (current x)) law)
    (hconstant : ∀ prediction : Y,
      Integrable (fun x ↦ risk x prediction) law) :
    AEBayesOptimalForRisk law risk current ↔
      OptimalOnEveryMeasurableGroupForRisk law risk current := by
  constructor
  · intro hbayes group _ alternative halternative
    exact setIntegral_mono_ae hcurrent.integrableOn halternative.integrableOn
      (hbayes.mono fun x hx ↦ hx (alternative x))
  · intro hgroups
    have haction (prediction : Y) :
        (fun x ↦ risk x (current x)) ≤ᵐ[law]
          (fun x ↦ risk x prediction) := by
      apply ae_le_of_forall_setIntegral_le hcurrent (hconstant prediction)
      intro group hgroup _
      exact hgroups group hgroup (fun _ ↦ prediction) (hconstant prediction)
    rw [AEBayesOptimalForRisk]
    exact ae_all_iff.2 haction

/-! ### Conditional-distribution semantics for the paper's loss -/

/-- Conditional risk at feature `x` when action `prediction` is evaluated
against the conditional label kernel `labels`. -/
def kernelConditionalRisk {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] (labels : ProbabilityTheory.Kernel X Y)
    (loss : BoundedLoss Y) (x : X) (prediction : Y) : ℝ :=
  ∫ truth, loss.value prediction truth ∂labels x

/-- A bounded measurable loss integrated against a Markov label kernel gives
an integrable conditional-risk function for every measurable model. -/
theorem integrable_kernelConditionalRisk
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (featureLaw : Measure X) [IsProbabilityMeasure featureLaw]
    (labels : ProbabilityTheory.Kernel X Y)
    [ProbabilityTheory.IsMarkovKernel labels]
    (loss : BoundedLoss Y) (hloss : MeasurableBoundedLoss loss)
    (model : Model X Y) (hmodel : MeasurableModel model) :
    Integrable (fun x ↦ kernelConditionalRisk labels loss x (model x))
      featureLaw := by
  refine Integrable.of_bound ?_ 1 ?_
  · exact (MeasureTheory.StronglyMeasurable.integral_kernel_prod_right'
      ((measurable_datumLoss hloss hmodel).stronglyMeasurable)).aestronglyMeasurable
  · filter_upwards [] with x
    unfold kernelConditionalRisk
    have hbound : ‖∫ truth, loss.value (model x) truth ∂labels x‖ ≤ 1 := by
      simpa using (norm_integral_le_of_norm_le_const
        (μ := labels x) (C := (1 : ℝ)) (f := fun truth ↦
          loss.value (model x) truth) (by
            filter_upwards [] with truth
            rw [Real.norm_eq_abs, abs_of_nonneg (loss.nonneg _ _)]
            exact loss.le_one _ _))
    exact hbound

/-- Source-faithful repaired Observation 4 for an arbitrary feature law and
a Markov conditional label distribution.  When the action/label space is
countable and the loss and current model are measurable, the paper's pointwise
Bayes property is equivalent to every-measurable-group optimality after
replacing pointwise comparison by almost-everywhere comparison. -/
theorem observation4_kernelAEBayesOptimal_iff_groupwiseOptimal
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] [Countable Y]
    (featureLaw : Measure X) [IsProbabilityMeasure featureLaw]
    (labels : ProbabilityTheory.Kernel X Y)
    [ProbabilityTheory.IsMarkovKernel labels]
    (loss : BoundedLoss Y) (hloss : MeasurableBoundedLoss loss)
    (current : Model X Y) (hcurrent : MeasurableModel current) :
    AEBayesOptimalForRisk featureLaw (kernelConditionalRisk labels loss)
        current ↔
      OptimalOnEveryMeasurableGroupForRisk featureLaw
        (kernelConditionalRisk labels loss) current := by
  apply aeBayesOptimalForRisk_iff_optimalOnEveryMeasurableGroupForRisk
  · exact integrable_kernelConditionalRisk featureLaw labels loss hloss
      current hcurrent
  · intro prediction
    exact integrable_kernelConditionalRisk featureLaw labels loss hloss
      (fun _ ↦ prediction) measurable_const

/-- Arbitrary-label form of repaired Observation 4.  The current model is
almost everywhere no worse than each integrable alternative model exactly
when it is no worse on every measurable subgroup.  For countable labels,
`observation4_kernelAEBayesOptimal_iff_groupwiseOptimal` identifies this with
the common-null-set actionwise Bayes formulation. -/
theorem observation4_kernelAEModelwiseOptimal_iff_groupwiseOptimal
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (featureLaw : Measure X) [IsProbabilityMeasure featureLaw]
    (labels : ProbabilityTheory.Kernel X Y)
    [ProbabilityTheory.IsMarkovKernel labels]
    (loss : BoundedLoss Y) (hloss : MeasurableBoundedLoss loss)
    (current : Model X Y) (hcurrent : MeasurableModel current) :
    AEOptimalAgainstEveryIntegrableModelForRisk featureLaw
        (kernelConditionalRisk labels loss) current ↔
      OptimalOnEveryMeasurableGroupForRisk featureLaw
        (kernelConditionalRisk labels loss) current := by
  exact aeOptimalAgainstEveryIntegrableModelForRisk_iff_groupwiseOptimal
    featureLaw (kernelConditionalRisk labels loss) current
      (integrable_kernelConditionalRisk featureLaw labels loss hloss current hcurrent)

/-- Continuous uniform probability law on the unit interval. -/
def observation4UniformFeatureLaw : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) 1)

instance observation4UniformFeatureLaw_isProbabilityMeasure :
    IsProbabilityMeasure observation4UniformFeatureLaw := by
  rw [MeasureTheory.isProbabilityMeasure_iff]
  simp [observation4UniformFeatureLaw, Real.volume_Icc]

/-- A deterministic-false outcome has zero-one pointwise risk `1` exactly
where a Boolean model predicts `true`. -/
def deterministicFalsePointRisk (model : ℝ → Bool) (x : ℝ) : ℝ :=
  if model x then 1 else 0

/-- The Bayes model for the deterministic-false outcome. -/
def observation4FalseModel : ℝ → Bool := fun _ => false

/-- A measurable model differing from the Bayes model only at the support
point `1/2`. -/
def observation4NullSpikeModel : ℝ → Bool := fun x =>
  if x = (1 / 2 : ℝ) then true else false

theorem observation4NullSpikeModel_measurable :
    Measurable observation4NullSpikeModel := by
  exact Measurable.ite (measurableSet_singleton (1 / 2 : ℝ))
    measurable_const measurable_const

theorem observation4FalseModel_measurable :
    Measurable observation4FalseModel := measurable_const

/-- Pointwise Bayes optimality restricted to the topological support, matching
the intended scope of the paper's Definition 3. -/
def PointwiseBayesOnSupport (law : Measure ℝ) (model : ℝ → Bool) : Prop :=
  ∀ x ∈ law.support, ∀ alternative : ℝ → Bool,
    deterministicFalsePointRisk model x ≤
      deterministicFalsePointRisk alternative x

/-- Groupwise optimality against every measurable group and every measurable
alternative model.  Conditional normalization is unnecessary: multiplying by
group mass gives the equivalent joint-integral comparison. -/
def OptimalOnEveryMeasurableGroup (law : Measure ℝ)
    (model : ℝ → Bool) : Prop :=
  ∀ group : Set ℝ, MeasurableSet group →
    ∀ alternative : ℝ → Bool, Measurable alternative →
      (∫ x in group, deterministicFalsePointRisk model x ∂law) ≤
        ∫ x in group, deterministicFalsePointRisk alternative x ∂law

/-- The exceptional point lies in the support of the continuous feature law. -/
theorem observation4_half_mem_support :
    (1 / 2 : ℝ) ∈ observation4UniformFeatureLaw.support := by
  change (1 / 2 : ℝ) ∈ (volume.restrict (Set.Icc (0 : ℝ) 1)).support
  apply Measure.interior_inter_support
  constructor
  · simp only [interior_Icc, mem_Ioo]
    norm_num
  · rw [Measure.support_eq_univ]
    simp

/-- The exceptional support point nevertheless has probability zero. -/
theorem observation4_half_measure_zero :
    observation4UniformFeatureLaw ({1 / 2} : Set ℝ) = 0 := by
  rw [observation4UniformFeatureLaw,
    Measure.restrict_apply (measurableSet_singleton (1 / 2 : ℝ))]
  exact measure_mono_null Set.inter_subset_left (measure_singleton (1 / 2 : ℝ))

/-- The null-spike model is indistinguishable from the Bayes model by every
measurable group integral. -/
theorem observation4_nullSpike_group_integral_eq_zero
    (group : Set ℝ) :
    (∫ x in group, deterministicFalsePointRisk observation4NullSpikeModel x
        ∂observation4UniformFeatureLaw) = 0 := by
  have hnull : (observation4UniformFeatureLaw.restrict group)
      ({1 / 2} : Set ℝ) = 0 := by
    apply le_antisymm ?_ (by simp)
    calc
      (observation4UniformFeatureLaw.restrict group) ({1 / 2} : Set ℝ) ≤
          observation4UniformFeatureLaw ({1 / 2} : Set ℝ) :=
        Measure.restrict_le_self _
      _ = 0 := observation4_half_measure_zero
  have hae : (fun x =>
      deterministicFalsePointRisk observation4NullSpikeModel x) =ᵐ[
        observation4UniformFeatureLaw.restrict group] (fun _ => 0) := by
    apply MeasureTheory.ae_iff.2
    apply measure_mono_null ?_ hnull
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    by_contra hpoint
    have hne : x ≠ (1 / 2 : ℝ) := by simpa using hpoint
    have hne' : x ≠ (2 : ℝ)⁻¹ := by simpa [one_div] using hne
    apply hx
    simp [deterministicFalsePointRisk, observation4NullSpikeModel, hne']
  rw [MeasureTheory.integral_congr_ae hae]
  simp

/-- The null-spike model is optimal on every measurable group against every
measurable alternative, because its group loss is zero. -/
theorem observation4_nullSpike_optimalOnEveryMeasurableGroup :
    OptimalOnEveryMeasurableGroup observation4UniformFeatureLaw
      observation4NullSpikeModel := by
  intro group _ alternative _
  rw [observation4_nullSpike_group_integral_eq_zero]
  apply MeasureTheory.integral_nonneg_of_ae
  filter_upwards [] with x
  simp only [deterministicFalsePointRisk]
  positivity

/-- But the same model is not pointwise Bayes optimal at the null support
point.  This refutes the printed arbitrary-distribution form of Observation 4. -/
theorem observation4_nullSpike_not_pointwiseBayesOnSupport :
    ¬ PointwiseBayesOnSupport observation4UniformFeatureLaw
      observation4NullSpikeModel := by
  intro hbayes
  have hpoint := hbayes (1 / 2 : ℝ) observation4_half_mem_support
    observation4FalseModel
  norm_num [deterministicFalsePointRisk, observation4NullSpikeModel,
    observation4FalseModel] at hpoint

/-- Compact counterexample pair used by the source audit. -/
theorem observation4_arbitraryDistribution_pointwise_iff_counterexample :
    OptimalOnEveryMeasurableGroup observation4UniformFeatureLaw
        observation4NullSpikeModel ∧
      ¬ PointwiseBayesOnSupport observation4UniformFeatureLaw
        observation4NullSpikeModel :=
  ⟨observation4_nullSpike_optimalOnEveryMeasurableGroup,
    observation4_nullSpike_not_pointwiseBayesOnSupport⟩

end

end GHKR22BiasBounties

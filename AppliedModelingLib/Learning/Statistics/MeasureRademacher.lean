import AppliedModelingLib.Foundations.Probability.FiniteIID
import AppliedModelingLib.Foundations.Probability.FiniteIIDPairSwaps
import AppliedModelingLib.Foundations.Probability.MeasureBoundedDifferences
import AppliedModelingLib.Foundations.Probability.UniformHoeffding
import AppliedModelingLib.Learning.Statistics.FiniteRademacher

/-!
# Uniform convergence over arbitrary population laws

This module gives the measure-theoretic finite-class bridge used before a
Rademacher or VC argument removes the cardinality factor.  The population law
is an arbitrary probability measure; only the hypothesis index is finite.

The source-learning papers that use this module often state the subsequent
arbitrary-class Rademacher theorem without a measurability convention.  This
finite-class result needs none beyond measurability of each score, and keeps
the larger countable/separable-class boundary explicit.

The second part of the module supplies the measure-theoretic expected empirical
Rademacher complexity needed at that boundary.  For a countable nonempty
measurable class, it proves the ghost-sample and pair-swap symmetrization
argument over arbitrary population laws, then combines it with the generic
finite-iid bounded-differences theorem in `MeasureBoundedDifferences`.  A
separable extension or an outer-probability convention is still required for
non-countable source classes.
-/

namespace AppliedModelingLib
namespace Statistics
namespace MeasureRademacher

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- The population mean of a score under an arbitrary probability law. -/
noncomputable def populationMean
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) (value : Hypothesis → Outcome → ℝ)
    (hypothesis : Hypothesis) : ℝ :=
  law[value hypothesis]

/-- The normalized empirical mean on a finite iid sample. -/
noncomputable def empiricalMean
    {Outcome Hypothesis : Type*} (sampleCount : ℕ)
    (value : Hypothesis → Outcome → ℝ)
    (sample : Fin sampleCount → Outcome) (hypothesis : Hypothesis) : ℝ :=
  (sampleCount : ℝ)⁻¹ * ∑ index : Fin sampleCount,
    value hypothesis (sample index)

/-- One-sided population-minus-empirical uniform deviation for a possibly
infinite class under an arbitrary population law.  Countability is imposed
only by the measurability and integration theorems below, not by this
definition. -/
noncomputable def upperUniformDeviationSet
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome] [Nonempty Hypothesis]
    (law : Measure Outcome) (sampleCount : ℕ)
    (value : Hypothesis → Outcome → ℝ)
    (sample : Fin sampleCount → Outcome) : ℝ :=
  sSup (Set.range fun hypothesis =>
    populationMean law value hypothesis -
      empiricalMean sampleCount value sample hypothesis)

/-- One-sided empirical-minus-population uniform deviation for a possibly
infinite class under an arbitrary population law.  This is kept separate from
`upperUniformDeviationSet`: the two directions are both needed when an
empirical online-learning comparison is transferred to population gains. -/
noncomputable def lowerUniformDeviationSet
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome] [Nonempty Hypothesis]
    (law : Measure Outcome) (sampleCount : ℕ)
    (value : Hypothesis → Outcome → ℝ)
    (sample : Fin sampleCount → Outcome) : ℝ :=
  sSup (Set.range fun hypothesis =>
    empiricalMean sampleCount value sample hypothesis -
      populationMean law value hypothesis)

/-- The lower deviation of a class is the upper deviation of its pointwise
negation.  This identity is algebraic and does not add a measurability or
boundedness assumption. -/
theorem lowerUniformDeviationSet_eq_upper_negateFunctionClass
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome] [Nonempty Hypothesis]
    (law : Measure Outcome) (sampleCount : ℕ)
    (value : Hypothesis → Outcome → ℝ)
    (sample : Fin sampleCount → Outcome) :
    lowerUniformDeviationSet law sampleCount value sample =
      upperUniformDeviationSet law sampleCount
        (FiniteRademacher.negateFunctionClass value) sample := by
  unfold lowerUniformDeviationSet upperUniformDeviationSet
  apply congrArg sSup
  ext score
  constructor <;> rintro ⟨hypothesis, rfl⟩ <;> refine ⟨hypothesis, ?_⟩ <;>
    unfold populationMean empiricalMean FiniteRademacher.negateFunctionClass <;>
    dsimp <;> rw [integral_neg, Finset.sum_neg_distrib] <;> ring

/-- A measurable `[0,1]` score has population mean in `[0,1]` under an
arbitrary probability law. -/
theorem populationMean_mem_Icc
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) [IsProbabilityMeasure law]
    (value : Hypothesis → Outcome → ℝ)
    (hmeasurable : ∀ hypothesis, Measurable (value hypothesis))
    (hbounded : ∀ hypothesis outcome,
      value hypothesis outcome ∈ Set.Icc (0 : ℝ) 1)
    (hypothesis : Hypothesis) :
    populationMean law value hypothesis ∈ Set.Icc (0 : ℝ) 1 := by
  have hintegrable : Integrable (value hypothesis) law :=
    Integrable.of_mem_Icc 0 1 (hmeasurable hypothesis).aemeasurable
      (Filter.Eventually.of_forall fun outcome => hbounded hypothesis outcome)
  constructor
  · unfold populationMean
    exact integral_nonneg fun outcome => (hbounded hypothesis outcome).1
  · unfold populationMean
    calc
      ∫ outcome, value hypothesis outcome ∂law ≤
          ∫ _outcome : Outcome, (1 : ℝ) ∂law := by
            apply integral_mono hintegrable (integrable_const _)
            intro outcome
            exact (hbounded hypothesis outcome).2
      _ = 1 := by simp

/-- A nonempty empirical mean of `[0,1]` scores lies in `[0,1]`. -/
theorem empiricalMean_mem_Icc
    {Outcome Hypothesis : Type*} (sampleCount : ℕ) (hsampleCount : 0 < sampleCount)
    (value : Hypothesis → Outcome → ℝ)
    (hbounded : ∀ hypothesis outcome,
      value hypothesis outcome ∈ Set.Icc (0 : ℝ) 1)
    (sample : Fin sampleCount → Outcome) (hypothesis : Hypothesis) :
    empiricalMean sampleCount value sample hypothesis ∈ Set.Icc (0 : ℝ) 1 := by
  simpa only [empiricalMean, FiniteRademacher.finiteEmpiricalMean] using
    (FiniteRademacher.finiteEmpiricalMean_mem_Icc sampleCount hsampleCount value
      (fun hypothesis outcome => hbounded hypothesis outcome) sample hypothesis)

/-- The score range defining an arbitrary-class upper deviation is bounded
above under the primitive `[0,1]` range assumption. -/
theorem bddAbove_range_upperUniformDeviationScore
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) [IsProbabilityMeasure law]
    (sampleCount : ℕ) (hsampleCount : 0 < sampleCount)
    (value : Hypothesis → Outcome → ℝ)
    (hmeasurable : ∀ hypothesis, Measurable (value hypothesis))
    (hbounded : ∀ hypothesis outcome,
      value hypothesis outcome ∈ Set.Icc (0 : ℝ) 1)
    (sample : Fin sampleCount → Outcome) :
    BddAbove (Set.range fun hypothesis =>
      populationMean law value hypothesis -
        empiricalMean sampleCount value sample hypothesis) := by
  refine ⟨1, ?_⟩
  rintro score ⟨hypothesis, rfl⟩
  have hpopulation := populationMean_mem_Icc law value hmeasurable hbounded hypothesis
  have hempirical := empiricalMean_mem_Icc sampleCount hsampleCount value hbounded
    sample hypothesis
  linarith [hpopulation.2, hempirical.1]

/-- A countable class of measurable scores has a measurable upper uniform
deviation.  This is the first place the customary countability/permissibility
condition is needed. -/
theorem measurable_upperUniformDeviationSet_comp
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome] [Countable Hypothesis]
    [Nonempty Hypothesis] (law : Measure Outcome) (sampleCount : ℕ)
    (value : Hypothesis → Outcome → ℝ)
    (hmeasurable : ∀ hypothesis, Measurable (value hypothesis)) :
    Measurable (fun sample : Fin sampleCount → Outcome =>
      upperUniformDeviationSet law sampleCount value sample) := by
  unfold upperUniformDeviationSet
  apply Measurable.iSup
  intro hypothesis
  apply measurable_const.sub
  unfold empiricalMean
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro index _
  exact (hmeasurable hypothesis).comp (measurable_pi_apply index)

/-- Replacing one observation changes a `[0,1]` upper uniform deviation by at
most `1/n`; the argument does not need a maximizing hypothesis. -/
theorem abs_upperUniformDeviationSet_sub_update_le_inv
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome] [Nonempty Hypothesis]
    (law : Measure Outcome) [IsProbabilityMeasure law]
    (sampleCount : ℕ) (hsampleCount : 0 < sampleCount)
    (value : Hypothesis → Outcome → ℝ)
    (hmeasurable : ∀ hypothesis, Measurable (value hypothesis))
    (hbounded : ∀ hypothesis outcome,
      value hypothesis outcome ∈ Set.Icc (0 : ℝ) 1)
    (sample : Fin sampleCount → Outcome) (index : Fin sampleCount)
    (replacement : Outcome) :
    |upperUniformDeviationSet law sampleCount value sample -
        upperUniformDeviationSet law sampleCount value
          (Function.update sample index replacement)| ≤ (sampleCount : ℝ)⁻¹ := by
  unfold upperUniformDeviationSet
  apply FiniteRademacher.abs_sSup_range_sub_sSup_range_le_of_forall_abs_sub_le
  · exact bddAbove_range_upperUniformDeviationScore law sampleCount hsampleCount
      value hmeasurable hbounded sample
  · exact bddAbove_range_upperUniformDeviationScore law sampleCount hsampleCount
      value hmeasurable hbounded (Function.update sample index replacement)
  · intro hypothesis
    simpa [sub_sub_sub_cancel_left, abs_sub_comm] using
      (FiniteRademacher.abs_finiteEmpiricalMean_sub_update_le_inv
        sampleCount hsampleCount value
        (fun hypothesis outcome => hbounded hypothesis outcome)
        sample index replacement hypothesis)

/-- A nonempty `[0,1]` class has upper uniform deviation in `[-1,1]` on
every nonempty sample. -/
theorem upperUniformDeviationSet_mem_Icc
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome] [Nonempty Hypothesis]
    (law : Measure Outcome) [IsProbabilityMeasure law]
    (sampleCount : ℕ) (hsampleCount : 0 < sampleCount)
    (value : Hypothesis → Outcome → ℝ)
    (hmeasurable : ∀ hypothesis, Measurable (value hypothesis))
    (hbounded : ∀ hypothesis outcome,
      value hypothesis outcome ∈ Set.Icc (0 : ℝ) 1)
    (sample : Fin sampleCount → Outcome) :
    upperUniformDeviationSet law sampleCount value sample ∈ Set.Icc (-1 : ℝ) 1 := by
  classical
  let score : Hypothesis → ℝ := fun hypothesis =>
    populationMean law value hypothesis - empiricalMean sampleCount value sample hypothesis
  have hscoreBdd : BddAbove (Set.range score) :=
    bddAbove_range_upperUniformDeviationScore law sampleCount hsampleCount
      value hmeasurable hbounded sample
  have hscoreUpper : ∀ hypothesis, score hypothesis ≤ 1 := by
    intro hypothesis
    have hpopulation := populationMean_mem_Icc law value hmeasurable hbounded hypothesis
    have hempirical := empiricalMean_mem_Icc sampleCount hsampleCount value hbounded
      sample hypothesis
    linarith [hpopulation.2, hempirical.1]
  have hscoreLower : ∀ hypothesis, -1 ≤ score hypothesis := by
    intro hypothesis
    have hpopulation := populationMean_mem_Icc law value hmeasurable hbounded hypothesis
    have hempirical := empiricalMean_mem_Icc sampleCount hsampleCount value hbounded
      sample hypothesis
    linarith [hpopulation.1, hempirical.2]
  unfold upperUniformDeviationSet
  change sSup (Set.range score) ∈ Set.Icc (-1 : ℝ) 1
  constructor
  · let hypothesis : Hypothesis := Classical.choice (inferInstance : Nonempty Hypothesis)
    calc
      -1 ≤ score hypothesis := hscoreLower hypothesis
      _ ≤ sSup (Set.range score) := le_csSup hscoreBdd ⟨hypothesis, rfl⟩
  · apply csSup_le (Set.range_nonempty _)
    rintro result ⟨hypothesis, rfl⟩
    exact hscoreUpper hypothesis

/-- Under the countable-class measurability convention, upper uniform
deviation is integrable under the canonical iid sample law. -/
theorem integrable_upperUniformDeviationSet_comp
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome] [Countable Hypothesis]
    [Nonempty Hypothesis] (law : Measure Outcome) [IsProbabilityMeasure law]
    (sampleCount : ℕ) (hsampleCount : 0 < sampleCount)
    (value : Hypothesis → Outcome → ℝ)
    (hmeasurable : ∀ hypothesis, Measurable (value hypothesis))
    (hbounded : ∀ hypothesis outcome,
      value hypothesis outcome ∈ Set.Icc (0 : ℝ) 1) :
    Integrable (fun sample : Fin sampleCount → Outcome =>
      upperUniformDeviationSet law sampleCount value sample)
      (Probability.finiteIIDSampleLaw law sampleCount) := by
  letI : IsProbabilityMeasure (Probability.finiteIIDSampleLaw law sampleCount) := by
    unfold Probability.finiteIIDSampleLaw
    infer_instance
  apply Integrable.of_mem_Icc (-1) 1
    (measurable_upperUniformDeviationSet_comp law sampleCount value hmeasurable).aemeasurable
  filter_upwards with sample
  exact upperUniformDeviationSet_mem_Icc law sampleCount hsampleCount value
    hmeasurable hbounded sample

/-- Countable-class McDiarmid concentration for the one-sided uniform
deviation.  This uses the arbitrary-law finite-product bounded-differences
theorem; no finite-support assumption is made on the observations. -/
theorem measureReal_upperUniformDeviationSet_sub_integral_ge_le_exp
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome] [Countable Hypothesis]
    [Nonempty Hypothesis] (law : Measure Outcome) [IsProbabilityMeasure law]
    (sampleCount : ℕ) (hsampleCount : 0 < sampleCount)
    (value : Hypothesis → Outcome → ℝ)
    (hmeasurable : ∀ hypothesis, Measurable (value hypothesis))
    (hbounded : ∀ hypothesis outcome,
      value hypothesis outcome ∈ Set.Icc (0 : ℝ) 1)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) :
    (Probability.finiteIIDSampleLaw law sampleCount).real
      {sample | epsilon ≤ upperUniformDeviationSet law sampleCount value sample -
        ∫ sample, upperUniformDeviationSet law sampleCount value sample ∂
          Probability.finiteIIDSampleLaw law sampleCount} ≤
      Real.exp (-2 * (sampleCount : ℝ) * epsilon ^ 2) := by
  letI : IsProbabilityMeasure (Probability.finiteIIDSampleLaw law sampleCount) := by
    unfold Probability.finiteIIDSampleLaw
    infer_instance
  have htail :=
    AppliedModelingLib.Probability.MeasureBoundedDifferences.measureReal_finiteIID_sub_integral_ge_le_of_boundedDifferences
      law sampleCount
      (upperUniformDeviationSet law sampleCount value)
      (measurable_upperUniformDeviationSet_comp law sampleCount value hmeasurable)
      (upperUniformDeviationSet_mem_Icc law sampleCount hsampleCount value
        hmeasurable hbounded)
      (fun _ : Fin sampleCount => (sampleCount : ℝ)⁻¹)
      (by
        intro index sample replacement
        exact abs_upperUniformDeviationSet_sub_update_le_inv law sampleCount
          hsampleCount value hmeasurable hbounded sample index replacement)
      hepsilon
  calc
    (Probability.finiteIIDSampleLaw law sampleCount).real
        {sample | epsilon ≤ upperUniformDeviationSet law sampleCount value sample -
          ∫ sample, upperUniformDeviationSet law sampleCount value sample ∂
            Probability.finiteIIDSampleLaw law sampleCount} ≤
        Real.exp (-epsilon ^ 2 /
          (2 * ∑ _index : Fin sampleCount, ((sampleCount : ℝ)⁻¹) ^ 2 / 4)) := htail
    _ = Real.exp (-2 * (sampleCount : ℝ) * epsilon ^ 2) := by
      congr 1
      have hcount : (sampleCount : ℝ) ≠ 0 := by
        exact_mod_cast hsampleCount.ne'
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp [hcount]
      norm_num

/-- Population means commute with an affine score transformation.  The
boundedness assumption supplies the integrability needed for the integral
calculation. -/
theorem populationMean_affine
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) [IsProbabilityMeasure law]
    (value : Hypothesis → Outcome → ℝ)
    (hmeasurable : ∀ hypothesis, Measurable (value hypothesis))
    {lower upper : ℝ}
    (hbounded : ∀ hypothesis outcome,
      value hypothesis outcome ∈ Set.Icc lower upper)
    (scale shift : ℝ) (hypothesis : Hypothesis) :
    populationMean law (fun hypothesis outcome =>
      scale * value hypothesis outcome + shift) hypothesis =
      scale * populationMean law value hypothesis + shift := by
  have hintegrable : Integrable (value hypothesis) law :=
    Integrable.of_mem_Icc lower upper (hmeasurable hypothesis).aemeasurable
      (Filter.Eventually.of_forall fun outcome => hbounded hypothesis outcome)
  unfold populationMean
  rw [integral_add (hintegrable.const_mul scale) (integrable_const shift),
    integral_const_mul, integral_const, smul_eq_mul]
  simp

/-- On a nonempty sample, empirical means commute with an affine score
transformation. -/
theorem empiricalMean_affine
    {Outcome Hypothesis : Type*} {sampleCount : ℕ}
    (hsampleCount : 0 < sampleCount)
    (value : Hypothesis → Outcome → ℝ)
    (sample : Fin sampleCount → Outcome)
    (scale shift : ℝ) (hypothesis : Hypothesis) :
    empiricalMean sampleCount (fun hypothesis outcome =>
      scale * value hypothesis outcome + shift) sample hypothesis =
      scale * empiricalMean sampleCount value sample hypothesis + shift := by
  unfold empiricalMean
  have hcount : (sampleCount : ℝ) ≠ 0 := by
    exact_mod_cast hsampleCount.ne'
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [mul_add]
  calc
    (sampleCount : ℝ)⁻¹ *
        (∑ index : Fin sampleCount,
          scale * value hypothesis (sample index)) +
        (sampleCount : ℝ)⁻¹ * ((sampleCount : ℝ) * shift) =
        (sampleCount : ℝ)⁻¹ *
          (scale * ∑ index : Fin sampleCount,
            value hypothesis (sample index)) +
          (sampleCount : ℝ)⁻¹ * ((sampleCount : ℝ) * shift) := by
            congr 1
            congr 1
            rw [Finset.mul_sum]
    _ = scale * ((sampleCount : ℝ)⁻¹ * ∑ index : Fin sampleCount,
          value hypothesis (sample index)) +
          ((sampleCount : ℝ)⁻¹ * (sampleCount : ℝ)) * shift := by ring
    _ = _ := by rw [inv_mul_cancel₀ hcount, one_mul]

/-- Affinely normalizing a `[-1,1]`-valued class to `[0,1]` halves every
population-minus-empirical deviation. -/
theorem upperUniformDeviationSet_affine_half
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome] [Nonempty Hypothesis]
    (law : Measure Outcome) [IsProbabilityMeasure law]
    (sampleCount : ℕ) (hsampleCount : 0 < sampleCount)
    (value : Hypothesis → Outcome → ℝ)
    (hmeasurable : ∀ hypothesis, Measurable (value hypothesis))
    (hvalue : ∀ hypothesis outcome, |value hypothesis outcome| ≤ 1)
    (sample : Fin sampleCount → Outcome) :
    upperUniformDeviationSet law sampleCount
        (fun hypothesis outcome => (1 / 2 : ℝ) * value hypothesis outcome + 1 / 2) sample =
      (1 / 2 : ℝ) * upperUniformDeviationSet law sampleCount value sample := by
  have hvalueIcc : ∀ hypothesis outcome,
      value hypothesis outcome ∈ Set.Icc (-1 : ℝ) 1 := by
    intro hypothesis outcome
    exact abs_le.mp (hvalue hypothesis outcome)
  unfold upperUniformDeviationSet
  rw [show (fun hypothesis =>
      populationMean law
          (fun hypothesis outcome => (1 / 2 : ℝ) * value hypothesis outcome + 1 / 2)
          hypothesis -
        empiricalMean sampleCount
          (fun hypothesis outcome => (1 / 2 : ℝ) * value hypothesis outcome + 1 / 2)
          sample hypothesis) =
      fun hypothesis => (1 / 2 : ℝ) *
        (populationMean law value hypothesis -
          empiricalMean sampleCount value sample hypothesis) by
        funext hypothesis
        rw [populationMean_affine law value hmeasurable hvalueIcc (1 / 2 : ℝ) (1 / 2 : ℝ),
          empiricalMean_affine hsampleCount value sample (1 / 2 : ℝ) (1 / 2 : ℝ)]
        ring]
  exact FiniteRademacher.sSup_range_const_mul_eq_const_sSup_range
    (1 / 2 : ℝ) (by norm_num) _

/-- Every population-minus-empirical score is bounded by the corresponding
upper uniform deviation.  The primitive `[-1,1]` assumption is used only to
justify the real supremum through affine normalization to `[0,1]`. -/
theorem populationMean_sub_empiricalMean_le_upperUniformDeviationSet_of_abs_le_one
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome] [Nonempty Hypothesis]
    (law : Measure Outcome) [IsProbabilityMeasure law]
    (sampleCount : ℕ) (hsampleCount : 0 < sampleCount)
    (value : Hypothesis → Outcome → ℝ)
    (hmeasurable : ∀ hypothesis, Measurable (value hypothesis))
    (hvalue : ∀ hypothesis outcome, |value hypothesis outcome| ≤ 1)
    (sample : Fin sampleCount → Outcome) (hypothesis : Hypothesis) :
    populationMean law value hypothesis - empiricalMean sampleCount value sample hypothesis ≤
      upperUniformDeviationSet law sampleCount value sample := by
  let normalized : Hypothesis → Outcome → ℝ := fun hypothesis outcome =>
    (1 / 2 : ℝ) * value hypothesis outcome + 1 / 2
  have hnormalizedMeasurable : ∀ hypothesis, Measurable (normalized hypothesis) := by
    intro hypothesis
    exact ((hmeasurable hypothesis).const_mul (1 / 2 : ℝ)).add measurable_const
  have hnormalizedBounded : ∀ hypothesis outcome,
      normalized hypothesis outcome ∈ Set.Icc (0 : ℝ) 1 := by
    intro hypothesis outcome
    have hbounds := abs_le.mp (hvalue hypothesis outcome)
    constructor <;> dsimp [normalized] <;> linarith
  have hboundedRange := bddAbove_range_upperUniformDeviationScore law sampleCount
    hsampleCount normalized hnormalizedMeasurable hnormalizedBounded sample
  have hnormalizedLe : populationMean law normalized hypothesis -
      empiricalMean sampleCount normalized sample hypothesis ≤
        upperUniformDeviationSet law sampleCount normalized sample := by
    unfold upperUniformDeviationSet
    exact le_csSup hboundedRange ⟨hypothesis, rfl⟩
  have hvalueIcc : ∀ hypothesis outcome,
      value hypothesis outcome ∈ Set.Icc (-1 : ℝ) 1 := by
    intro hypothesis outcome
    exact abs_le.mp (hvalue hypothesis outcome)
  have hpopulation : populationMean law normalized hypothesis =
      (1 / 2 : ℝ) * populationMean law value hypothesis + 1 / 2 := by
    exact populationMean_affine law value hmeasurable hvalueIcc (1 / 2) (1 / 2) hypothesis
  have hempirical : empiricalMean sampleCount normalized sample hypothesis =
      (1 / 2 : ℝ) * empiricalMean sampleCount value sample hypothesis + 1 / 2 := by
    exact empiricalMean_affine hsampleCount value sample (1 / 2) (1 / 2) hypothesis
  have hdeviation : upperUniformDeviationSet law sampleCount normalized sample =
      (1 / 2 : ℝ) * upperUniformDeviationSet law sampleCount value sample := by
    exact upperUniformDeviationSet_affine_half law sampleCount hsampleCount value
      hmeasurable hvalue sample
  rw [hpopulation, hempirical, hdeviation] at hnormalizedLe
  linarith

/-- Every empirical-minus-population score is bounded by the lower uniform
deviation.  This is the lower-side companion used in two-sided uniform
generalization events. -/
theorem empiricalMean_sub_populationMean_le_lowerUniformDeviationSet_of_abs_le_one
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome] [Nonempty Hypothesis]
    (law : Measure Outcome) [IsProbabilityMeasure law]
    (sampleCount : ℕ) (hsampleCount : 0 < sampleCount)
    (value : Hypothesis → Outcome → ℝ)
    (hmeasurable : ∀ hypothesis, Measurable (value hypothesis))
    (hvalue : ∀ hypothesis outcome, |value hypothesis outcome| ≤ 1)
    (sample : Fin sampleCount → Outcome) (hypothesis : Hypothesis) :
    empiricalMean sampleCount value sample hypothesis - populationMean law value hypothesis ≤
      lowerUniformDeviationSet law sampleCount value sample := by
  let negatedValue := FiniteRademacher.negateFunctionClass value
  have hnegatedMeasurable : ∀ hypothesis, Measurable (negatedValue hypothesis) := by
    intro hypothesis
    exact (hmeasurable hypothesis).neg
  have hnegatedBounded : ∀ hypothesis outcome, |negatedValue hypothesis outcome| ≤ 1 := by
    intro hypothesis outcome
    simpa [negatedValue, FiniteRademacher.negateFunctionClass] using
      hvalue hypothesis outcome
  have hupper :=
    populationMean_sub_empiricalMean_le_upperUniformDeviationSet_of_abs_le_one
      law sampleCount hsampleCount negatedValue hnegatedMeasurable hnegatedBounded sample hypothesis
  have hidentity : populationMean law negatedValue hypothesis -
      empiricalMean sampleCount negatedValue sample hypothesis =
        empiricalMean sampleCount value sample hypothesis - populationMean law value hypothesis := by
    unfold negatedValue populationMean empiricalMean FiniteRademacher.negateFunctionClass
    rw [integral_neg, Finset.sum_neg_distrib]
    ring
  rw [hidentity, show negatedValue = FiniteRademacher.negateFunctionClass value by rfl,
    ← lowerUniformDeviationSet_eq_upper_negateFunctionClass] at hupper
  exact hupper

/-- On a nonempty finite sample, the local empirical-mean convention agrees
with the generic finite-index convention used by the Hoeffding library. -/
theorem empiricalMean_eq_probability_finiteEmpiricalMean
    {Outcome Hypothesis : Type*} {sampleCount : ℕ} (hsampleCount : 0 < sampleCount)
    (value : Hypothesis → Outcome → ℝ) (sample : Fin sampleCount → Outcome)
    (hypothesis : Hypothesis) :
    empiricalMean sampleCount value sample hypothesis =
      Probability.finiteEmpiricalMean
        (fun hypothesis index sample => value hypothesis (sample index))
        hypothesis sample := by
  unfold empiricalMean Probability.finiteEmpiricalMean
  have hcount : (sampleCount : ℝ) ≠ 0 := by
    exact_mod_cast hsampleCount.ne'
  rw [show (Fintype.card (Fin sampleCount) : ℝ) = sampleCount by simp]
  field_simp

/-- Every coordinate of the canonical iid product sample has the declared
population mean. -/
theorem finiteIID_coordinate_mean_eq_populationMean
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) [IsProbabilityMeasure law] (sampleCount : ℕ)
    (value : Hypothesis → Outcome → ℝ)
    (hmeasurable : ∀ hypothesis, Measurable (value hypothesis))
    (hypothesis : Hypothesis) (index : Fin sampleCount) :
    (Probability.finiteIIDSampleLaw law sampleCount)[fun sample =>
      value hypothesis (sample index)] = populationMean law value hypothesis := by
  unfold populationMean
  calc
    (Probability.finiteIIDSampleLaw law sampleCount)[fun sample =>
        value hypothesis (sample index)] =
        (Measure.map (fun sample => sample index)
          (Probability.finiteIIDSampleLaw law sampleCount))[value hypothesis] := by
            symm
            apply integral_map
            · exact (measurable_pi_apply index).aemeasurable
            · exact (hmeasurable hypothesis).aestronglyMeasurable
    _ = law[value hypothesis] := by
      change ∫ outcome, value hypothesis outcome ∂
        Measure.map (Probability.finiteIIDSampleCoordinate index)
          (Probability.finiteIIDSampleLaw law sampleCount) = law[value hypothesis]
      rw [Probability.map_finiteIIDSampleCoordinate law sampleCount index]

/-- The one-sided empirical difference of two samples, represented by a
coordinatewise paired sample.  The first component is the ghost sample and
the second component is the original sample. -/
noncomputable def pairedUniformDifferenceSet
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome] [Nonempty Hypothesis]
    (sampleCount : ℕ) (value : Hypothesis → Outcome → ℝ)
    (pairedSample : Fin sampleCount → Outcome × Outcome) : ℝ :=
  sSup (Set.range fun hypothesis =>
    empiricalMean sampleCount value (fun index => (pairedSample index).1) hypothesis -
      empiricalMean sampleCount value (fun index => (pairedSample index).2) hypothesis)

/-- The same paired difference after a fixed Rademacher orientation is chosen
at each coordinate. -/
noncomputable def signedPairedUniformDifferenceSet
    {Outcome Hypothesis : Type*} [Nonempty Hypothesis]
    (sampleCount : ℕ) (value : Hypothesis → Outcome → ℝ)
    (signs : Fin sampleCount → Bool)
    (pairedSample : Fin sampleCount → Outcome × Outcome) : ℝ :=
  sSup (Set.range fun hypothesis =>
    (sampleCount : ℝ)⁻¹ * ∑ index : Fin sampleCount,
      AppliedModelingLib.Probability.RademacherMatrix.rademacherSign (signs index) *
        (value hypothesis (pairedSample index).1 -
          value hypothesis (pairedSample index).2))

/-- A difference of empirical means is the normalized sum of coordinatewise
differences. -/
theorem empiricalMean_sub_eq_pairedDifference
    {Outcome Hypothesis : Type*} (sampleCount : ℕ)
    (value : Hypothesis → Outcome → ℝ)
    (first second : Fin sampleCount → Outcome) (hypothesis : Hypothesis) :
    empiricalMean sampleCount value first hypothesis -
        empiricalMean sampleCount value second hypothesis =
      (sampleCount : ℝ)⁻¹ * ∑ index : Fin sampleCount,
        (value hypothesis (first index) - value hypothesis (second index)) := by
  unfold empiricalMean
  rw [Finset.sum_sub_distrib]
  ring

/-- Orienting equal-law pairs by signs turns the unsigned paired difference
into its signed counterpart. -/
theorem pairedUniformDifferenceSet_pairSwap
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome] [Nonempty Hypothesis]
    (sampleCount : ℕ) (value : Hypothesis → Outcome → ℝ)
    (signs : Fin sampleCount → Bool)
    (pairedSample : Fin sampleCount → Outcome × Outcome) :
    pairedUniformDifferenceSet sampleCount value
        (Probability.finiteIIDPairSwap signs pairedSample) =
      signedPairedUniformDifferenceSet sampleCount value signs pairedSample := by
  unfold pairedUniformDifferenceSet signedPairedUniformDifferenceSet
  apply congrArg sSup
  apply congrArg Set.range
  funext hypothesis
  rw [empiricalMean_sub_eq_pairedDifference]
  congr 1
  apply Finset.sum_congr rfl
  intro index _
  cases hsign : signs index <;>
    simp [Probability.finiteIIDPairSwap, hsign,
      AppliedModelingLib.Probability.RademacherMatrix.rademacherSign]

/-- Countability makes the paired ghost-sample supremum measurable. -/
theorem measurable_pairedUniformDifferenceSet_comp
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome] [Countable Hypothesis]
    [Nonempty Hypothesis] (sampleCount : ℕ)
    (value : Hypothesis → Outcome → ℝ)
    (hmeasurable : ∀ hypothesis, Measurable (value hypothesis)) :
    Measurable (fun pairedSample : Fin sampleCount → Outcome × Outcome =>
      pairedUniformDifferenceSet sampleCount value pairedSample) := by
  unfold pairedUniformDifferenceSet empiricalMean
  apply Measurable.iSup
  intro hypothesis
  apply Measurable.sub <;>
    apply Measurable.const_mul <;>
      apply Finset.measurable_sum <;>
        intro index _
  · exact (hmeasurable hypothesis).comp
      (measurable_fst.comp (measurable_pi_apply index))
  · exact (hmeasurable hypothesis).comp
      (measurable_snd.comp (measurable_pi_apply index))

/-- The paired ghost-sample supremum remains in `[-1,1]` under a primitive
`[0,1]` score range. -/
theorem pairedUniformDifferenceSet_mem_Icc
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome] [Nonempty Hypothesis]
    (sampleCount : ℕ) (hsampleCount : 0 < sampleCount)
    (value : Hypothesis → Outcome → ℝ)
    (hbounded : ∀ hypothesis outcome,
      value hypothesis outcome ∈ Set.Icc (0 : ℝ) 1)
    (pairedSample : Fin sampleCount → Outcome × Outcome) :
    pairedUniformDifferenceSet sampleCount value pairedSample ∈
      Set.Icc (-1 : ℝ) 1 := by
  let score : Hypothesis → ℝ := fun hypothesis =>
    empiricalMean sampleCount value (fun index => (pairedSample index).1) hypothesis -
      empiricalMean sampleCount value (fun index => (pairedSample index).2) hypothesis
  have hscoreBdd : BddAbove (Set.range score) := by
    refine ⟨1, ?_⟩
    rintro result ⟨hypothesis, rfl⟩
    have hfirst := empiricalMean_mem_Icc sampleCount hsampleCount value hbounded
      (fun index => (pairedSample index).1) hypothesis
    have hsecond := empiricalMean_mem_Icc sampleCount hsampleCount value hbounded
      (fun index => (pairedSample index).2) hypothesis
    linarith [hfirst.2, hsecond.1]
  have hscoreUpper : ∀ hypothesis, score hypothesis ≤ 1 := by
    intro hypothesis
    have hfirst := empiricalMean_mem_Icc sampleCount hsampleCount value hbounded
      (fun index => (pairedSample index).1) hypothesis
    have hsecond := empiricalMean_mem_Icc sampleCount hsampleCount value hbounded
      (fun index => (pairedSample index).2) hypothesis
    linarith [hfirst.2, hsecond.1]
  have hscoreLower : ∀ hypothesis, -1 ≤ score hypothesis := by
    intro hypothesis
    have hfirst := empiricalMean_mem_Icc sampleCount hsampleCount value hbounded
      (fun index => (pairedSample index).1) hypothesis
    have hsecond := empiricalMean_mem_Icc sampleCount hsampleCount value hbounded
      (fun index => (pairedSample index).2) hypothesis
    linarith [hfirst.1, hsecond.2]
  unfold pairedUniformDifferenceSet
  change sSup (Set.range score) ∈ Set.Icc (-1 : ℝ) 1
  constructor
  · let hypothesis : Hypothesis := Classical.choice (inferInstance : Nonempty Hypothesis)
    calc
      -1 ≤ score hypothesis := hscoreLower hypothesis
      _ ≤ sSup (Set.range score) := le_csSup hscoreBdd ⟨hypothesis, rfl⟩
  · apply csSup_le (Set.range_nonempty _)
    rintro result ⟨hypothesis, rfl⟩
    exact hscoreUpper hypothesis

/-- The signed paired supremum inherits measurability by composing the
unsigned supremum with its measurable coordinatewise orientation map. -/
theorem measurable_signedPairedUniformDifferenceSet_comp
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome] [Countable Hypothesis]
    [Nonempty Hypothesis] (sampleCount : ℕ)
    (value : Hypothesis → Outcome → ℝ)
    (hmeasurable : ∀ hypothesis, Measurable (value hypothesis))
    (signs : Fin sampleCount → Bool) :
    Measurable (fun pairedSample : Fin sampleCount → Outcome × Outcome =>
      signedPairedUniformDifferenceSet sampleCount value signs pairedSample) := by
  have hcomposed : Measurable (fun pairedSample : Fin sampleCount → Outcome × Outcome =>
      pairedUniformDifferenceSet sampleCount value
        (AppliedModelingLib.Probability.finiteIIDPairSwapMeasEquiv sampleCount signs
          pairedSample)) :=
    (measurable_pairedUniformDifferenceSet_comp sampleCount value hmeasurable).comp
      (AppliedModelingLib.Probability.finiteIIDPairSwapMeasEquiv sampleCount signs).measurable
  have hequality : (fun pairedSample : Fin sampleCount → Outcome × Outcome =>
      pairedUniformDifferenceSet sampleCount value
        (AppliedModelingLib.Probability.finiteIIDPairSwapMeasEquiv sampleCount signs
          pairedSample)) =
      fun pairedSample =>
        signedPairedUniformDifferenceSet sampleCount value signs pairedSample := by
    funext pairedSample
    simpa only [AppliedModelingLib.Probability.finiteIIDPairSwapMeasEquiv_apply] using
      pairedUniformDifferenceSet_pairSwap sampleCount value signs pairedSample
  rw [hequality] at hcomposed
  exact hcomposed

/-- The signed paired supremum has the same primitive `[-1,1]` bound as its
unsigned form. -/
theorem signedPairedUniformDifferenceSet_mem_Icc
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome] [Nonempty Hypothesis]
    (sampleCount : ℕ) (hsampleCount : 0 < sampleCount)
    (value : Hypothesis → Outcome → ℝ)
    (hbounded : ∀ hypothesis outcome,
      value hypothesis outcome ∈ Set.Icc (0 : ℝ) 1)
    (signs : Fin sampleCount → Bool)
    (pairedSample : Fin sampleCount → Outcome × Outcome) :
    signedPairedUniformDifferenceSet sampleCount value signs pairedSample ∈
      Set.Icc (-1 : ℝ) 1 := by
  rw [← pairedUniformDifferenceSet_pairSwap sampleCount value signs pairedSample]
  exact pairedUniformDifferenceSet_mem_Icc sampleCount hsampleCount value hbounded
    (Probability.finiteIIDPairSwap signs pairedSample)

/-- The paired ghost-sample supremum is integrable under the iid pair law. -/
theorem integrable_pairedUniformDifferenceSet_comp
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome] [Countable Hypothesis]
    [Nonempty Hypothesis] (law : Measure Outcome) [IsProbabilityMeasure law]
    (sampleCount : ℕ) (hsampleCount : 0 < sampleCount)
    (value : Hypothesis → Outcome → ℝ)
    (hmeasurable : ∀ hypothesis, Measurable (value hypothesis))
    (hbounded : ∀ hypothesis outcome,
      value hypothesis outcome ∈ Set.Icc (0 : ℝ) 1) :
    Integrable (fun pairedSample : Fin sampleCount → Outcome × Outcome =>
      pairedUniformDifferenceSet sampleCount value pairedSample)
      (Probability.finiteIIDSampleLaw (law.prod law) sampleCount) := by
  letI : IsProbabilityMeasure
      (Probability.finiteIIDSampleLaw (law.prod law) sampleCount) := by
    unfold Probability.finiteIIDSampleLaw
    infer_instance
  apply Integrable.of_mem_Icc (-1) 1
    (measurable_pairedUniformDifferenceSet_comp sampleCount value hmeasurable).aemeasurable
  filter_upwards with pairedSample
  exact pairedUniformDifferenceSet_mem_Icc sampleCount hsampleCount value hbounded pairedSample

/-- The signed paired supremum is integrable under the iid pair law. -/
theorem integrable_signedPairedUniformDifferenceSet_comp
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome] [Countable Hypothesis]
    [Nonempty Hypothesis] (law : Measure Outcome) [IsProbabilityMeasure law]
    (sampleCount : ℕ) (hsampleCount : 0 < sampleCount)
    (value : Hypothesis → Outcome → ℝ)
    (hmeasurable : ∀ hypothesis, Measurable (value hypothesis))
    (hbounded : ∀ hypothesis outcome,
      value hypothesis outcome ∈ Set.Icc (0 : ℝ) 1)
    (signs : Fin sampleCount → Bool) :
    Integrable (fun pairedSample : Fin sampleCount → Outcome × Outcome =>
      signedPairedUniformDifferenceSet sampleCount value signs pairedSample)
      (Probability.finiteIIDSampleLaw (law.prod law) sampleCount) := by
  letI : IsProbabilityMeasure
      (Probability.finiteIIDSampleLaw (law.prod law) sampleCount) := by
    unfold Probability.finiteIIDSampleLaw
    infer_instance
  apply Integrable.of_mem_Icc (-1) 1
    (measurable_signedPairedUniformDifferenceSet_comp sampleCount value hmeasurable signs).aemeasurable
  filter_upwards with pairedSample
  exact signedPairedUniformDifferenceSet_mem_Icc sampleCount hsampleCount value hbounded
    signs pairedSample

/-- A bounded empirical mean is integrable under the finite iid sample law. -/
theorem integrable_empiricalMean_comp
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) [IsProbabilityMeasure law]
    (sampleCount : ℕ) (value : Hypothesis → Outcome → ℝ)
    (hmeasurable : ∀ hypothesis, Measurable (value hypothesis))
    (hbounded : ∀ hypothesis outcome,
      value hypothesis outcome ∈ Set.Icc (0 : ℝ) 1)
    (hypothesis : Hypothesis) :
    Integrable (fun sample : Fin sampleCount → Outcome =>
      empiricalMean sampleCount value sample hypothesis)
      (Probability.finiteIIDSampleLaw law sampleCount) := by
  letI : IsProbabilityMeasure (Probability.finiteIIDSampleLaw law sampleCount) := by
    unfold Probability.finiteIIDSampleLaw
    infer_instance
  unfold empiricalMean
  apply (integrable_finset_sum Finset.univ fun index _ => ?_).const_mul
    (sampleCount : ℝ)⁻¹
  apply Integrable.of_mem_Icc 0 1
    ((hmeasurable hypothesis).comp (measurable_pi_apply index)).aemeasurable
  filter_upwards with sample
  exact hbounded hypothesis (sample index)

/-- The expected empirical mean of each bounded measurable score is its
population mean. -/
theorem integral_empiricalMean_comp_eq_populationMean
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) [IsProbabilityMeasure law]
    (sampleCount : ℕ) (hsampleCount : 0 < sampleCount)
    (value : Hypothesis → Outcome → ℝ)
    (hmeasurable : ∀ hypothesis, Measurable (value hypothesis))
    (hbounded : ∀ hypothesis outcome,
      value hypothesis outcome ∈ Set.Icc (0 : ℝ) 1)
    (hypothesis : Hypothesis) :
    (∫ sample : Fin sampleCount → Outcome,
      empiricalMean sampleCount value sample hypothesis ∂
        Probability.finiteIIDSampleLaw law sampleCount) =
      populationMean law value hypothesis := by
  letI : IsProbabilityMeasure (Probability.finiteIIDSampleLaw law sampleCount) := by
    unfold Probability.finiteIIDSampleLaw
    infer_instance
  have hintegrable : ∀ index : Fin sampleCount,
      Integrable (fun sample : Fin sampleCount → Outcome =>
        value hypothesis (sample index))
        (Probability.finiteIIDSampleLaw law sampleCount) := by
    intro index
    apply Integrable.of_mem_Icc 0 1
      ((hmeasurable hypothesis).comp (measurable_pi_apply index)).aemeasurable
    filter_upwards with sample
    exact hbounded hypothesis (sample index)
  calc
    (∫ sample : Fin sampleCount → Outcome,
        empiricalMean sampleCount value sample hypothesis ∂
          Probability.finiteIIDSampleLaw law sampleCount) =
        ∫ sample : Fin sampleCount → Outcome,
          (sampleCount : ℝ)⁻¹ *
            (∑ index : Fin sampleCount, value hypothesis (sample index)) ∂
              Probability.finiteIIDSampleLaw law sampleCount := by
            rfl
    _ = (sampleCount : ℝ)⁻¹ *
          ∫ sample : Fin sampleCount → Outcome,
            ∑ index : Fin sampleCount, value hypothesis (sample index) ∂
              Probability.finiteIIDSampleLaw law sampleCount := by
            rw [integral_const_mul]
    _ = (sampleCount : ℝ)⁻¹ * ∑ index : Fin sampleCount,
          ∫ sample : Fin sampleCount → Outcome,
            value hypothesis (sample index) ∂
              Probability.finiteIIDSampleLaw law sampleCount := by
            rw [integral_finset_sum Finset.univ (fun index _ => hintegrable index)]
    _ = (sampleCount : ℝ)⁻¹ * ∑ _index : Fin sampleCount,
          populationMean law value hypothesis := by
            apply congrArg
            apply Finset.sum_congr rfl
            intro index _
            exact finiteIID_coordinate_mean_eq_populationMean law sampleCount value
              hmeasurable hypothesis index
    _ = populationMean law value hypothesis := by
      have hcount : (sampleCount : ℝ) ≠ 0 := by
        exact_mod_cast hsampleCount.ne'
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp [hcount]

/-- The population--empirical supremum of a fixed sample is dominated by the
expected difference from an independent ghost sample. -/
theorem upperUniformDeviationSet_le_integral_pairedUniformDifferenceSet
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome] [Countable Hypothesis]
    [Nonempty Hypothesis] (law : Measure Outcome) [IsProbabilityMeasure law]
    (sampleCount : ℕ) (hsampleCount : 0 < sampleCount)
    (value : Hypothesis → Outcome → ℝ)
    (hmeasurable : ∀ hypothesis, Measurable (value hypothesis))
    (hbounded : ∀ hypothesis outcome,
      value hypothesis outcome ∈ Set.Icc (0 : ℝ) 1)
    (sample : Fin sampleCount → Outcome) :
    upperUniformDeviationSet law sampleCount value sample ≤
      ∫ ghost : Fin sampleCount → Outcome,
        pairedUniformDifferenceSet sampleCount value
          (fun index => (ghost index, sample index)) ∂
          Probability.finiteIIDSampleLaw law sampleCount := by
  letI : IsProbabilityMeasure (Probability.finiteIIDSampleLaw law sampleCount) := by
    unfold Probability.finiteIIDSampleLaw
    infer_instance
  let pairedWithSample : (Fin sampleCount → Outcome) →
      Fin sampleCount → Outcome × Outcome :=
    fun ghost index => (ghost index, sample index)
  let pairedDifference : (Fin sampleCount → Outcome) → ℝ :=
    fun ghost => pairedUniformDifferenceSet sampleCount value (pairedWithSample ghost)
  have hpairedWithSampleMeasurable : Measurable pairedWithSample := by
    apply measurable_pi_lambda
    intro index
    exact (measurable_pi_apply index).prodMk measurable_const
  have hpairedDifferenceMeasurable : Measurable pairedDifference :=
    (measurable_pairedUniformDifferenceSet_comp sampleCount value hmeasurable).comp
      hpairedWithSampleMeasurable
  have hpairedDifferenceBound : ∀ ghost,
      pairedDifference ghost ∈ Set.Icc (-1 : ℝ) 1 := by
    intro ghost
    exact pairedUniformDifferenceSet_mem_Icc sampleCount hsampleCount value hbounded
      (pairedWithSample ghost)
  have hpairedDifferenceIntegrable : Integrable pairedDifference
      (Probability.finiteIIDSampleLaw law sampleCount) := by
    apply Integrable.of_mem_Icc (-1) 1 hpairedDifferenceMeasurable.aemeasurable
    filter_upwards with ghost
    exact hpairedDifferenceBound ghost
  have hpairedScoreBdd : ∀ pairedSample : Fin sampleCount → Outcome × Outcome,
      BddAbove (Set.range fun hypothesis =>
        empiricalMean sampleCount value (fun index => (pairedSample index).1) hypothesis -
          empiricalMean sampleCount value (fun index => (pairedSample index).2) hypothesis) := by
    intro pairedSample
    refine ⟨1, ?_⟩
    rintro result ⟨hypothesis, rfl⟩
    have hfirst := empiricalMean_mem_Icc sampleCount hsampleCount value hbounded
      (fun index => (pairedSample index).1) hypothesis
    have hsecond := empiricalMean_mem_Icc sampleCount hsampleCount value hbounded
      (fun index => (pairedSample index).2) hypothesis
    linarith [hfirst.2, hsecond.1]
  have hscoreIntegral : ∀ hypothesis,
      populationMean law value hypothesis -
          empiricalMean sampleCount value sample hypothesis =
        ∫ ghost : Fin sampleCount → Outcome,
          (empiricalMean sampleCount value ghost hypothesis -
            empiricalMean sampleCount value sample hypothesis) ∂
            Probability.finiteIIDSampleLaw law sampleCount := by
    intro hypothesis
    have hempirical := integrable_empiricalMean_comp law sampleCount value
      hmeasurable hbounded hypothesis
    have hdifference : Integrable (fun ghost : Fin sampleCount → Outcome =>
        empiricalMean sampleCount value ghost hypothesis -
          empiricalMean sampleCount value sample hypothesis)
        (Probability.finiteIIDSampleLaw law sampleCount) := by
      simpa only [Pi.sub_apply] using hempirical.sub (integrable_const _)
    rw [integral_sub hempirical (integrable_const _)]
    rw [integral_empiricalMean_comp_eq_populationMean law sampleCount hsampleCount
      value hmeasurable hbounded hypothesis, integral_const]
    simp
  have hscoreLe : ∀ hypothesis,
      populationMean law value hypothesis -
          empiricalMean sampleCount value sample hypothesis ≤
        ∫ ghost : Fin sampleCount → Outcome,
          pairedDifference ghost ∂ Probability.finiteIIDSampleLaw law sampleCount := by
    intro hypothesis
    have hempirical := integrable_empiricalMean_comp law sampleCount value
      hmeasurable hbounded hypothesis
    have hdifference : Integrable (fun ghost : Fin sampleCount → Outcome =>
        empiricalMean sampleCount value ghost hypothesis -
          empiricalMean sampleCount value sample hypothesis)
        (Probability.finiteIIDSampleLaw law sampleCount) := by
      simpa only [Pi.sub_apply] using hempirical.sub (integrable_const _)
    rw [hscoreIntegral hypothesis]
    apply integral_mono hdifference hpairedDifferenceIntegrable
    intro ghost
    change empiricalMean sampleCount value ghost hypothesis -
        empiricalMean sampleCount value sample hypothesis ≤
      pairedUniformDifferenceSet sampleCount value (pairedWithSample ghost)
    unfold pairedUniformDifferenceSet
    apply le_csSup (hpairedScoreBdd (pairedWithSample ghost))
    exact ⟨hypothesis, rfl⟩
  unfold upperUniformDeviationSet
  apply csSup_le (Set.range_nonempty _)
  rintro result ⟨hypothesis, rfl⟩
  exact hscoreLe hypothesis

/-- Averaging the ghost-sample inequality and regrouping the two samples as
coordinatewise iid pairs gives the first, measure-theoretic symmetrization
step. -/
theorem integral_upperUniformDeviationSet_le_integral_pairedUniformDifferenceSet
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome] [Countable Hypothesis]
    [Nonempty Hypothesis] (law : Measure Outcome) [IsProbabilityMeasure law]
    (sampleCount : ℕ) (hsampleCount : 0 < sampleCount)
    (value : Hypothesis → Outcome → ℝ)
    (hmeasurable : ∀ hypothesis, Measurable (value hypothesis))
    (hbounded : ∀ hypothesis outcome,
      value hypothesis outcome ∈ Set.Icc (0 : ℝ) 1) :
    (∫ sample : Fin sampleCount → Outcome,
      upperUniformDeviationSet law sampleCount value sample ∂
        Probability.finiteIIDSampleLaw law sampleCount) ≤
      ∫ pairedSample : Fin sampleCount → Outcome × Outcome,
        pairedUniformDifferenceSet sampleCount value pairedSample ∂
          Probability.finiteIIDSampleLaw (law.prod law) sampleCount := by
  let sampleLaw : Measure (Fin sampleCount → Outcome) :=
    Probability.finiteIIDSampleLaw law sampleCount
  let pairedLaw : Measure (Fin sampleCount → Outcome × Outcome) :=
    Probability.finiteIIDSampleLaw (law.prod law) sampleCount
  let pairing := AppliedModelingLib.Probability.finiteIIDPairingMeasEquiv
    (Outcome := Outcome) sampleCount
  let pairedDifference : (Fin sampleCount → Outcome × Outcome) → ℝ :=
    pairedUniformDifferenceSet sampleCount value
  let productDifference :
      (Fin sampleCount → Outcome) × (Fin sampleCount → Outcome) → ℝ :=
    fun samples => pairedDifference (pairing.symm samples)
  letI : IsProbabilityMeasure sampleLaw := by
    unfold sampleLaw Probability.finiteIIDSampleLaw
    infer_instance
  letI : IsProbabilityMeasure pairedLaw := by
    unfold pairedLaw Probability.finiteIIDSampleLaw
    infer_instance
  have hpairedIntegrable : Integrable pairedDifference pairedLaw := by
    exact integrable_pairedUniformDifferenceSet_comp law sampleCount hsampleCount
      value hmeasurable hbounded
  have hpairingPreserving : MeasurePreserving pairing.symm (sampleLaw.prod sampleLaw)
      pairedLaw := by
    rw [← AppliedModelingLib.Probability.map_finiteIIDPairingMeasEquiv law sampleCount]
    exact MeasurableEquiv.measurePreserving_symm pairedLaw pairing
  have hproductIntegrable : Integrable productDifference (sampleLaw.prod sampleLaw) := by
    simpa only [productDifference, Function.comp_apply] using
      hpairingPreserving.integrable_comp_of_integrable hpairedIntegrable
  have hinnerIntegrable : Integrable (fun sample : Fin sampleCount → Outcome =>
      ∫ ghost : Fin sampleCount → Outcome,
        productDifference (ghost, sample) ∂sampleLaw) sampleLaw :=
    hproductIntegrable.integral_prod_right
  have hpointwise : ∀ sample : Fin sampleCount → Outcome,
      upperUniformDeviationSet law sampleCount value sample ≤
        ∫ ghost : Fin sampleCount → Outcome,
          productDifference (ghost, sample) ∂sampleLaw := by
    intro sample
    simpa only [productDifference, pairedDifference, pairing,
      AppliedModelingLib.Probability.finiteIIDPairingMeasEquiv_symm_apply] using
      upperUniformDeviationSet_le_integral_pairedUniformDifferenceSet law sampleCount
        hsampleCount value hmeasurable hbounded sample
  calc
    (∫ sample : Fin sampleCount → Outcome,
        upperUniformDeviationSet law sampleCount value sample ∂sampleLaw) ≤
      ∫ sample : Fin sampleCount → Outcome,
        (∫ ghost : Fin sampleCount → Outcome,
          productDifference (ghost, sample) ∂sampleLaw) ∂sampleLaw := by
        apply integral_mono
          (integrable_upperUniformDeviationSet_comp law sampleCount hsampleCount
            value hmeasurable hbounded)
          hinnerIntegrable
        intro sample
        exact hpointwise sample
    _ = ∫ samples : (Fin sampleCount → Outcome) × (Fin sampleCount → Outcome),
        productDifference samples ∂sampleLaw.prod sampleLaw := by
          exact (integral_prod_symm productDifference hproductIntegrable).symm
    _ = ∫ pairedSample : Fin sampleCount → Outcome × Outcome,
        pairedDifference pairedSample ∂pairedLaw :=
          hpairingPreserving.integral_comp' pairedDifference

/-- A signed paired supremum splits into the two normalized signed empirical
suprema of the coordinate samples, without requiring the class to be finite. -/
theorem signedPairedUniformDifferenceSet_le_add_signedEmpiricalSupSet
    {Outcome Hypothesis : Type*} [Nonempty Hypothesis]
    (sampleCount : ℕ) (value : Hypothesis → Outcome → ℝ)
    (hvalue : ∀ hypothesis outcome, |value hypothesis outcome| ≤ 1)
    (signs : Fin sampleCount → Bool)
    (pairedSample : Fin sampleCount → Outcome × Outcome) :
    signedPairedUniformDifferenceSet sampleCount value signs pairedSample ≤
      FiniteRademacher.signedEmpiricalSupSet sampleCount
          (fun hypothesis index => value hypothesis (pairedSample index).1) signs +
        FiniteRademacher.signedEmpiricalSupSet sampleCount
          (fun hypothesis index => value hypothesis (pairedSample index).2)
          (FiniteRademacher.negateBooleanSigns (Fin sampleCount) signs) := by
  let left : Hypothesis → ℝ := fun hypothesis =>
    (sampleCount : ℝ)⁻¹ * ∑ index : Fin sampleCount,
      AppliedModelingLib.Probability.RademacherMatrix.rademacherSign (signs index) *
        value hypothesis (pairedSample index).1
  let right : Hypothesis → ℝ := fun hypothesis =>
    (sampleCount : ℝ)⁻¹ * ∑ index : Fin sampleCount,
      AppliedModelingLib.Probability.RademacherMatrix.rademacherSign
        ((FiniteRademacher.negateBooleanSigns (Fin sampleCount) signs) index) *
        value hypothesis (pairedSample index).2
  have hleftUnnormalizedBdd : BddAbove (Set.range fun hypothesis =>
      ∑ index : Fin sampleCount,
        AppliedModelingLib.Probability.RademacherMatrix.rademacherSign (signs index) *
          value hypothesis (pairedSample index).1) :=
    FiniteRademacher.bddAbove_range_rademacherScore_of_abs_le_one sampleCount
      (fun hypothesis index => value hypothesis (pairedSample index).1)
      (fun hypothesis index => hvalue hypothesis (pairedSample index).1) signs
  have hrightUnnormalizedBdd : BddAbove (Set.range fun hypothesis =>
      ∑ index : Fin sampleCount,
        AppliedModelingLib.Probability.RademacherMatrix.rademacherSign
          ((FiniteRademacher.negateBooleanSigns (Fin sampleCount) signs) index) *
          value hypothesis (pairedSample index).2) :=
    FiniteRademacher.bddAbove_range_rademacherScore_of_abs_le_one sampleCount
      (fun hypothesis index => value hypothesis (pairedSample index).2)
      (fun hypothesis index => hvalue hypothesis (pairedSample index).2)
      (FiniteRademacher.negateBooleanSigns (Fin sampleCount) signs)
  have hleftBdd : BddAbove (Set.range left) := by
    refine ⟨(sampleCount : ℝ)⁻¹ * sSup (Set.range fun hypothesis =>
      ∑ index : Fin sampleCount,
        AppliedModelingLib.Probability.RademacherMatrix.rademacherSign (signs index) *
          value hypothesis (pairedSample index).1), ?_⟩
    rintro result ⟨hypothesis, rfl⟩
    exact mul_le_mul_of_nonneg_left
      (le_csSup hleftUnnormalizedBdd ⟨hypothesis, rfl⟩)
      (inv_nonneg.mpr (Nat.cast_nonneg _))
  have hrightBdd : BddAbove (Set.range right) := by
    refine ⟨(sampleCount : ℝ)⁻¹ * sSup (Set.range fun hypothesis =>
      ∑ index : Fin sampleCount,
        AppliedModelingLib.Probability.RademacherMatrix.rademacherSign
          ((FiniteRademacher.negateBooleanSigns (Fin sampleCount) signs) index) *
          value hypothesis (pairedSample index).2), ?_⟩
    rintro result ⟨hypothesis, rfl⟩
    exact mul_le_mul_of_nonneg_left
      (le_csSup hrightUnnormalizedBdd ⟨hypothesis, rfl⟩)
      (inv_nonneg.mpr (Nat.cast_nonneg _))
  have hsplit : ∀ hypothesis,
      (sampleCount : ℝ)⁻¹ * ∑ index : Fin sampleCount,
          AppliedModelingLib.Probability.RademacherMatrix.rademacherSign (signs index) *
            (value hypothesis (pairedSample index).1 -
              value hypothesis (pairedSample index).2) =
        left hypothesis + right hypothesis := by
    intro hypothesis
    simp only [left, right, FiniteRademacher.negateBooleanSigns_apply,
      FiniteRademacher.rademacherSign_not]
    simp_rw [mul_sub, Finset.sum_sub_distrib, neg_mul, Finset.sum_neg_distrib]
    ring
  unfold signedPairedUniformDifferenceSet FiniteRademacher.signedEmpiricalSupSet
  rw [show (fun hypothesis =>
      (sampleCount : ℝ)⁻¹ * ∑ index : Fin sampleCount,
        AppliedModelingLib.Probability.RademacherMatrix.rademacherSign (signs index) *
          (value hypothesis (pairedSample index).1 -
            value hypothesis (pairedSample index).2)) =
      fun hypothesis => left hypothesis + right hypothesis by
        funext hypothesis
        exact hsplit hypothesis]
  exact FiniteRademacher.sSup_range_add_le_add_sSup_range left right hleftBdd hrightBdd

/-- Uniformly averaging the signed paired supremum is at most the sum of the
two fixed-sample empirical Rademacher complexities. -/
theorem pmfExp_signedPairedUniformDifferenceSet_le_add_empiricalOneSidedRademacherSet
    {Outcome Hypothesis : Type*} [Nonempty Hypothesis]
    (sampleCount : ℕ) (value : Hypothesis → Outcome → ℝ)
    (hvalue : ∀ hypothesis outcome, |value hypothesis outcome| ≤ 1)
    (pairedSample : Fin sampleCount → Outcome × Outcome) :
    AppliedModelingLib.pmfExp (AppliedModelingLib.uniformPMF (Fin sampleCount → Bool))
        (fun signs => signedPairedUniformDifferenceSet sampleCount value signs pairedSample) ≤
      FiniteRademacher.empiricalOneSidedRademacherSet sampleCount
          (fun hypothesis index => value hypothesis (pairedSample index).1) +
        FiniteRademacher.empiricalOneSidedRademacherSet sampleCount
          (fun hypothesis index => value hypothesis (pairedSample index).2) := by
  calc
    AppliedModelingLib.pmfExp (AppliedModelingLib.uniformPMF (Fin sampleCount → Bool))
        (fun signs => signedPairedUniformDifferenceSet sampleCount value signs pairedSample) ≤
      AppliedModelingLib.pmfExp (AppliedModelingLib.uniformPMF (Fin sampleCount → Bool))
        (fun signs =>
          FiniteRademacher.signedEmpiricalSupSet sampleCount
              (fun hypothesis index => value hypothesis (pairedSample index).1) signs +
            FiniteRademacher.signedEmpiricalSupSet sampleCount
              (fun hypothesis index => value hypothesis (pairedSample index).2)
              (FiniteRademacher.negateBooleanSigns (Fin sampleCount) signs)) := by
            apply AppliedModelingLib.pmfExp_le_pmfExp_of_forall_le
            intro signs
            exact signedPairedUniformDifferenceSet_le_add_signedEmpiricalSupSet
              sampleCount value hvalue signs pairedSample
    _ = AppliedModelingLib.pmfExp (AppliedModelingLib.uniformPMF (Fin sampleCount → Bool))
          (FiniteRademacher.signedEmpiricalSupSet sampleCount
            (fun hypothesis index => value hypothesis (pairedSample index).1)) +
        AppliedModelingLib.pmfExp (AppliedModelingLib.uniformPMF (Fin sampleCount → Bool))
          (fun signs =>
            FiniteRademacher.signedEmpiricalSupSet sampleCount
              (fun hypothesis index => value hypothesis (pairedSample index).2)
              (FiniteRademacher.negateBooleanSigns (Fin sampleCount) signs)) := by
            rw [AppliedModelingLib.pmfExp_add]
    _ = FiniteRademacher.empiricalOneSidedRademacherSet sampleCount
          (fun hypothesis index => value hypothesis (pairedSample index).1) +
        FiniteRademacher.empiricalOneSidedRademacherSet sampleCount
          (fun hypothesis index => value hypothesis (pairedSample index).2) := by
            rw [FiniteRademacher.pmfExp_signedEmpiricalSupSet_eq_empiricalOneSidedRademacherSet]
            rw [FiniteRademacher.pmfExp_uniformPMF_negateBooleanSigns]
            exact congrArg (fun result =>
              FiniteRademacher.empiricalOneSidedRademacherSet sampleCount
                (fun hypothesis index => value hypothesis (pairedSample index).1) + result)
              (FiniteRademacher.pmfExp_signedEmpiricalSupSet_eq_empiricalOneSidedRademacherSet
                sampleCount
                (fun hypothesis index => value hypothesis (pairedSample index).2))

/-- Every fixed sign orientation has the same iid-pair expectation as the
unsigned paired supremum. -/
theorem integral_signedPairedUniformDifferenceSet_eq_integral_pairedUniformDifferenceSet
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome] [Nonempty Hypothesis]
    (law : Measure Outcome) [IsProbabilityMeasure law]
    (sampleCount : ℕ) (value : Hypothesis → Outcome → ℝ)
    (signs : Fin sampleCount → Bool) :
    (∫ pairedSample : Fin sampleCount → Outcome × Outcome,
      signedPairedUniformDifferenceSet sampleCount value signs pairedSample ∂
        Probability.finiteIIDSampleLaw (law.prod law) sampleCount) =
      ∫ pairedSample : Fin sampleCount → Outcome × Outcome,
        pairedUniformDifferenceSet sampleCount value pairedSample ∂
          Probability.finiteIIDSampleLaw (law.prod law) sampleCount := by
  let pairOrientation := AppliedModelingLib.Probability.finiteIIDPairSwapMeasEquiv
    (Outcome := Outcome) sampleCount signs
  have hpreserving : MeasurePreserving pairOrientation
      (Probability.finiteIIDSampleLaw (law.prod law) sampleCount)
      (Probability.finiteIIDSampleLaw (law.prod law) sampleCount) :=
    AppliedModelingLib.Probability.measurePreserving_finiteIIDPairSwapMeasEquiv
      law sampleCount signs
  calc
    (∫ pairedSample : Fin sampleCount → Outcome × Outcome,
        signedPairedUniformDifferenceSet sampleCount value signs pairedSample ∂
          Probability.finiteIIDSampleLaw (law.prod law) sampleCount) =
        ∫ pairedSample : Fin sampleCount → Outcome × Outcome,
          pairedUniformDifferenceSet sampleCount value
            (pairOrientation pairedSample) ∂
            Probability.finiteIIDSampleLaw (law.prod law) sampleCount := by
              apply integral_congr_ae
              filter_upwards with pairedSample
              simpa only [pairOrientation,
                AppliedModelingLib.Probability.finiteIIDPairSwapMeasEquiv_apply] using
                (pairedUniformDifferenceSet_pairSwap sampleCount value signs pairedSample).symm
    _ = ∫ pairedSample : Fin sampleCount → Outcome × Outcome,
          pairedUniformDifferenceSet sampleCount value pairedSample ∂
            Probability.finiteIIDSampleLaw (law.prod law) sampleCount :=
          hpreserving.integral_comp' (pairedUniformDifferenceSet sampleCount value)

/-- The unsigned paired expectation is the uniform average over its signed
pair-orientation versions. -/
theorem integral_pairedUniformDifferenceSet_eq_pmfExp_integral_signedPairedUniformDifferenceSet
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome] [Nonempty Hypothesis]
    (law : Measure Outcome) [IsProbabilityMeasure law]
    (sampleCount : ℕ) (value : Hypothesis → Outcome → ℝ) :
    (∫ pairedSample : Fin sampleCount → Outcome × Outcome,
      pairedUniformDifferenceSet sampleCount value pairedSample ∂
        Probability.finiteIIDSampleLaw (law.prod law) sampleCount) =
      AppliedModelingLib.pmfExp (AppliedModelingLib.uniformPMF (Fin sampleCount → Bool))
        (fun signs =>
          ∫ pairedSample : Fin sampleCount → Outcome × Outcome,
            signedPairedUniformDifferenceSet sampleCount value signs pairedSample ∂
              Probability.finiteIIDSampleLaw (law.prod law) sampleCount) := by
  calc
    (∫ pairedSample : Fin sampleCount → Outcome × Outcome,
        pairedUniformDifferenceSet sampleCount value pairedSample ∂
          Probability.finiteIIDSampleLaw (law.prod law) sampleCount) =
        AppliedModelingLib.pmfExp (AppliedModelingLib.uniformPMF (Fin sampleCount → Bool))
          (fun _signs =>
            ∫ pairedSample : Fin sampleCount → Outcome × Outcome,
              pairedUniformDifferenceSet sampleCount value pairedSample ∂
                Probability.finiteIIDSampleLaw (law.prod law) sampleCount) := by
              rw [AppliedModelingLib.pmfExp_const]
    _ = AppliedModelingLib.pmfExp (AppliedModelingLib.uniformPMF (Fin sampleCount → Bool))
          (fun signs =>
            ∫ pairedSample : Fin sampleCount → Outcome × Outcome,
              signedPairedUniformDifferenceSet sampleCount value signs pairedSample ∂
                Probability.finiteIIDSampleLaw (law.prod law) sampleCount) := by
              apply AppliedModelingLib.pmfExp_congr
              intro signs
              exact (integral_signedPairedUniformDifferenceSet_eq_integral_pairedUniformDifferenceSet
                law sampleCount value signs).symm

/-- Finite uniform sign averaging commutes with integration under the iid
pair law once the bounded signed suprema have been shown integrable. -/
theorem pmfExp_integral_signedPairedUniformDifferenceSet_eq_integral_pmfExp_signedPairedUniformDifferenceSet
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome] [Countable Hypothesis]
    [Nonempty Hypothesis] (law : Measure Outcome) [IsProbabilityMeasure law]
    (sampleCount : ℕ) (hsampleCount : 0 < sampleCount)
    (value : Hypothesis → Outcome → ℝ)
    (hmeasurable : ∀ hypothesis, Measurable (value hypothesis))
    (hbounded : ∀ hypothesis outcome,
      value hypothesis outcome ∈ Set.Icc (0 : ℝ) 1) :
    AppliedModelingLib.pmfExp (AppliedModelingLib.uniformPMF (Fin sampleCount → Bool))
        (fun signs =>
          ∫ pairedSample : Fin sampleCount → Outcome × Outcome,
            signedPairedUniformDifferenceSet sampleCount value signs pairedSample ∂
              Probability.finiteIIDSampleLaw (law.prod law) sampleCount) =
      ∫ pairedSample : Fin sampleCount → Outcome × Outcome,
        AppliedModelingLib.pmfExp (AppliedModelingLib.uniformPMF (Fin sampleCount → Bool))
          (fun signs =>
            signedPairedUniformDifferenceSet sampleCount value signs pairedSample) ∂
          Probability.finiteIIDSampleLaw (law.prod law) sampleCount := by
  classical
  let signLaw := AppliedModelingLib.uniformPMF (Fin sampleCount → Bool)
  let pairedLaw := Probability.finiteIIDSampleLaw (law.prod law) sampleCount
  have hintegrable : ∀ signs : Fin sampleCount → Bool,
      Integrable (fun pairedSample : Fin sampleCount → Outcome × Outcome =>
        signedPairedUniformDifferenceSet sampleCount value signs pairedSample) pairedLaw := by
    intro signs
    exact integrable_signedPairedUniformDifferenceSet_comp law sampleCount hsampleCount
      value hmeasurable hbounded signs
  change (∑ signs : Fin sampleCount → Bool,
      (signLaw signs).toReal *
        ∫ pairedSample : Fin sampleCount → Outcome × Outcome,
          signedPairedUniformDifferenceSet sampleCount value signs pairedSample ∂pairedLaw) =
    ∫ pairedSample : Fin sampleCount → Outcome × Outcome,
      ∑ signs : Fin sampleCount → Bool,
        (signLaw signs).toReal *
          signedPairedUniformDifferenceSet sampleCount value signs pairedSample ∂pairedLaw
  calc
    (∑ signs : Fin sampleCount → Bool,
        (signLaw signs).toReal *
          ∫ pairedSample : Fin sampleCount → Outcome × Outcome,
            signedPairedUniformDifferenceSet sampleCount value signs pairedSample ∂pairedLaw) =
        ∑ signs : Fin sampleCount → Bool,
          ∫ pairedSample : Fin sampleCount → Outcome × Outcome,
            (signLaw signs).toReal *
              signedPairedUniformDifferenceSet sampleCount value signs pairedSample ∂pairedLaw := by
            apply Finset.sum_congr rfl
            intro signs _
            exact (integral_const_mul (signLaw signs).toReal
              (fun pairedSample : Fin sampleCount → Outcome × Outcome =>
                signedPairedUniformDifferenceSet sampleCount value signs pairedSample)).symm
    _ = ∫ pairedSample : Fin sampleCount → Outcome × Outcome,
          ∑ signs : Fin sampleCount → Bool,
            (signLaw signs).toReal *
              signedPairedUniformDifferenceSet sampleCount value signs pairedSample ∂pairedLaw := by
            exact (integral_finset_sum Finset.univ
              (fun signs _ => (hintegrable signs).const_mul (signLaw signs).toReal)).symm

/-- Under the iid pair law, the first coordinate sample has the original iid
law, so its expected empirical Rademacher complexity is unchanged. -/
theorem integral_empiricalOneSidedRademacherSet_comp_fst_eq_integral
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome] [Nonempty Hypothesis]
    (law : Measure Outcome) [IsProbabilityMeasure law]
    (sampleCount : ℕ) (value : Hypothesis → Outcome → ℝ)
    (hcomplexityIntegrable : Integrable (fun sample : Fin sampleCount → Outcome =>
      FiniteRademacher.empiricalOneSidedRademacherSet sampleCount
        (fun hypothesis index => value hypothesis (sample index)))
      (Probability.finiteIIDSampleLaw law sampleCount)) :
    (∫ pairedSample : Fin sampleCount → Outcome × Outcome,
      FiniteRademacher.empiricalOneSidedRademacherSet sampleCount
        (fun hypothesis index => value hypothesis (pairedSample index).1) ∂
          Probability.finiteIIDSampleLaw (law.prod law) sampleCount) =
      ∫ sample : Fin sampleCount → Outcome,
        FiniteRademacher.empiricalOneSidedRademacherSet sampleCount
          (fun hypothesis index => value hypothesis (sample index)) ∂
          Probability.finiteIIDSampleLaw law sampleCount := by
  let sampleLaw : Measure (Fin sampleCount → Outcome) :=
    Probability.finiteIIDSampleLaw law sampleCount
  let pairedLaw : Measure (Fin sampleCount → Outcome × Outcome) :=
    Probability.finiteIIDSampleLaw (law.prod law) sampleCount
  let pairing := AppliedModelingLib.Probability.finiteIIDPairingMeasEquiv
    (Outcome := Outcome) sampleCount
  let complexity : (Fin sampleCount → Outcome) → ℝ := fun sample =>
    FiniteRademacher.empiricalOneSidedRademacherSet sampleCount
      (fun hypothesis index => value hypothesis (sample index))
  let productComplexity :
      (Fin sampleCount → Outcome) × (Fin sampleCount → Outcome) → ℝ :=
    fun samples => complexity samples.1
  letI : IsProbabilityMeasure sampleLaw := by
    unfold sampleLaw Probability.finiteIIDSampleLaw
    infer_instance
  letI : IsProbabilityMeasure pairedLaw := by
    unfold pairedLaw Probability.finiteIIDSampleLaw
    infer_instance
  have hproductIntegrable : Integrable productComplexity (sampleLaw.prod sampleLaw) := by
    exact ((memLp_one_iff_integrable.mpr hcomplexityIntegrable).comp_fst sampleLaw).integrable le_rfl
  have hpairingPreserving : MeasurePreserving pairing pairedLaw (sampleLaw.prod sampleLaw) :=
    ⟨pairing.measurable,
      AppliedModelingLib.Probability.map_finiteIIDPairingMeasEquiv law sampleCount⟩
  calc
    (∫ pairedSample : Fin sampleCount → Outcome × Outcome,
        FiniteRademacher.empiricalOneSidedRademacherSet sampleCount
          (fun hypothesis index => value hypothesis (pairedSample index).1) ∂pairedLaw) =
        ∫ samples : (Fin sampleCount → Outcome) × (Fin sampleCount → Outcome),
          productComplexity samples ∂sampleLaw.prod sampleLaw := by
            simpa only [pairing, productComplexity, complexity,
              AppliedModelingLib.Probability.finiteIIDPairingMeasEquiv_apply] using
              hpairingPreserving.integral_comp' productComplexity
    _ = ∫ sample : Fin sampleCount → Outcome, complexity sample ∂sampleLaw := by
      rw [integral_prod productComplexity hproductIntegrable]
      apply integral_congr_ae
      filter_upwards with sample
      change (∫ _ : Fin sampleCount → Outcome, complexity sample ∂sampleLaw) = complexity sample
      rw [integral_const]
      change (sampleLaw Set.univ).toReal • complexity sample = complexity sample
      rw [IsProbabilityMeasure.measure_univ]
      norm_num
    _ = ∫ sample : Fin sampleCount → Outcome, complexity sample ∂sampleLaw := by
      rfl

/-- The same marginal identity holds for the second coordinate of the iid
pair sample. -/
theorem integral_empiricalOneSidedRademacherSet_comp_snd_eq_integral
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome] [Nonempty Hypothesis]
    (law : Measure Outcome) [IsProbabilityMeasure law]
    (sampleCount : ℕ) (value : Hypothesis → Outcome → ℝ)
    (hcomplexityIntegrable : Integrable (fun sample : Fin sampleCount → Outcome =>
      FiniteRademacher.empiricalOneSidedRademacherSet sampleCount
        (fun hypothesis index => value hypothesis (sample index)))
      (Probability.finiteIIDSampleLaw law sampleCount)) :
    (∫ pairedSample : Fin sampleCount → Outcome × Outcome,
      FiniteRademacher.empiricalOneSidedRademacherSet sampleCount
        (fun hypothesis index => value hypothesis (pairedSample index).2) ∂
          Probability.finiteIIDSampleLaw (law.prod law) sampleCount) =
      ∫ sample : Fin sampleCount → Outcome,
        FiniteRademacher.empiricalOneSidedRademacherSet sampleCount
          (fun hypothesis index => value hypothesis (sample index)) ∂
          Probability.finiteIIDSampleLaw law sampleCount := by
  let sampleLaw : Measure (Fin sampleCount → Outcome) :=
    Probability.finiteIIDSampleLaw law sampleCount
  let pairedLaw : Measure (Fin sampleCount → Outcome × Outcome) :=
    Probability.finiteIIDSampleLaw (law.prod law) sampleCount
  let pairing := AppliedModelingLib.Probability.finiteIIDPairingMeasEquiv
    (Outcome := Outcome) sampleCount
  let complexity : (Fin sampleCount → Outcome) → ℝ := fun sample =>
    FiniteRademacher.empiricalOneSidedRademacherSet sampleCount
      (fun hypothesis index => value hypothesis (sample index))
  let productComplexity :
      (Fin sampleCount → Outcome) × (Fin sampleCount → Outcome) → ℝ :=
    fun samples => complexity samples.2
  letI : IsProbabilityMeasure sampleLaw := by
    unfold sampleLaw Probability.finiteIIDSampleLaw
    infer_instance
  letI : IsProbabilityMeasure pairedLaw := by
    unfold pairedLaw Probability.finiteIIDSampleLaw
    infer_instance
  have hproductIntegrable : Integrable productComplexity (sampleLaw.prod sampleLaw) := by
    exact ((memLp_one_iff_integrable.mpr hcomplexityIntegrable).comp_snd sampleLaw).integrable le_rfl
  have hpairingPreserving : MeasurePreserving pairing pairedLaw (sampleLaw.prod sampleLaw) :=
    ⟨pairing.measurable,
      AppliedModelingLib.Probability.map_finiteIIDPairingMeasEquiv law sampleCount⟩
  calc
    (∫ pairedSample : Fin sampleCount → Outcome × Outcome,
        FiniteRademacher.empiricalOneSidedRademacherSet sampleCount
          (fun hypothesis index => value hypothesis (pairedSample index).2) ∂pairedLaw) =
        ∫ samples : (Fin sampleCount → Outcome) × (Fin sampleCount → Outcome),
          productComplexity samples ∂sampleLaw.prod sampleLaw := by
            simpa only [pairing, productComplexity, complexity,
              AppliedModelingLib.Probability.finiteIIDPairingMeasEquiv_apply] using
              hpairingPreserving.integral_comp' productComplexity
    _ = ∫ sample : Fin sampleCount → Outcome, complexity sample ∂sampleLaw := by
      rw [integral_prod_symm productComplexity hproductIntegrable]
      apply integral_congr_ae
      filter_upwards with sample
      change (∫ _ : Fin sampleCount → Outcome, complexity sample ∂sampleLaw) = complexity sample
      rw [integral_const]
      change (sampleLaw Set.univ).toReal • complexity sample = complexity sample
      rw [IsProbabilityMeasure.measure_univ]
      norm_num
    _ = ∫ sample : Fin sampleCount → Outcome, complexity sample ∂sampleLaw := by
      rfl

/-- Expected one-sided empirical Rademacher complexity under an arbitrary
population law.  The fixed-sample complexity is the shared set-based
supremum; it is measurable and integrable below for a countable uniformly
bounded class. -/
noncomputable def expectedOneSidedRademacherSet
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) (sampleCount : ℕ)
    (value : Hypothesis → Outcome → ℝ) : ℝ :=
  (Probability.finiteIIDSampleLaw law sampleCount)[fun sample =>
    FiniteRademacher.empiricalOneSidedRademacherSet sampleCount
      (fun hypothesis index => value hypothesis (sample index))]

/-- Statistical one-sided Rademacher complexity is halved by the affine
normalization from `[-1,1]` to `[0,1]`.  This is an exact identity: the
constant shift cancels in expectation over the Rademacher signs. -/
theorem expectedOneSidedRademacherSet_affine_half
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome] [Nonempty Hypothesis]
    (law : Measure Outcome) (sampleCount : ℕ)
    (value : Hypothesis → Outcome → ℝ)
    (hvalue : ∀ hypothesis outcome, |value hypothesis outcome| ≤ 1) :
    expectedOneSidedRademacherSet law sampleCount
        (fun hypothesis outcome => (1 / 2 : ℝ) * value hypothesis outcome + 1 / 2) =
      (1 / 2 : ℝ) * expectedOneSidedRademacherSet law sampleCount value := by
  unfold expectedOneSidedRademacherSet
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with sample
  exact FiniteRademacher.empiricalOneSidedRademacherSet_affine_half sampleCount
    (fun hypothesis index => value hypothesis (sample index))
    (fun hypothesis index => hvalue hypothesis (sample index))

/-- Countability makes the fixed-sample real supremum defining one-sided
empirical Rademacher complexity measurable. -/
theorem measurable_empiricalOneSidedRademacherSet_comp
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome] [Countable Hypothesis]
    (sampleCount : ℕ) (value : Hypothesis → Outcome → ℝ)
    (hmeasurable : ∀ hypothesis, Measurable (value hypothesis)) :
    Measurable (fun sample : Fin sampleCount → Outcome =>
      FiniteRademacher.empiricalOneSidedRademacherSet sampleCount
        (fun hypothesis index => value hypothesis (sample index))) := by
  unfold FiniteRademacher.empiricalOneSidedRademacherSet
  apply Measurable.const_mul
  unfold AppliedModelingLib.pmfExp
  apply Finset.measurable_sum
  intro signs _
  apply Measurable.const_mul
  apply Measurable.iSup
  intro hypothesis
  apply Finset.measurable_sum
  intro index _
  exact measurable_const.mul
    ((hmeasurable hypothesis).comp (measurable_pi_apply index))

/-- The one-sided empirical Rademacher complexity of a nonempty `[-1,1]`
class lies in `[-1,1]`, including the zero-sample convention. -/
theorem empiricalOneSidedRademacherSet_mem_Icc
    {Hypothesis : Type*} [Nonempty Hypothesis]
    (sampleCount : ℕ) (value : Hypothesis → Fin sampleCount → ℝ)
    (hvalue : ∀ hypothesis index, |value hypothesis index| ≤ 1) :
    FiniteRademacher.empiricalOneSidedRademacherSet sampleCount value ∈
      Set.Icc (-1 : ℝ) 1 := by
  classical
  by_cases hsampleCount : sampleCount = 0
  · subst sampleCount
    simp [FiniteRademacher.empiricalOneSidedRademacherSet]
  let score : (Fin sampleCount → Bool) → Hypothesis → ℝ := fun signs hypothesis =>
    ∑ index : Fin sampleCount,
      AppliedModelingLib.Probability.RademacherMatrix.rademacherSign (signs index) *
        value hypothesis index
  have hscoreAbs : ∀ signs hypothesis, |score signs hypothesis| ≤ sampleCount := by
    intro signs hypothesis
    calc
      |score signs hypothesis| ≤ ∑ index : Fin sampleCount,
          |AppliedModelingLib.Probability.RademacherMatrix.rademacherSign (signs index) *
            value hypothesis index| := by
            exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ index : Fin sampleCount, |value hypothesis index| := by
            apply Finset.sum_congr rfl
            intro index _
            rw [abs_mul,
              AppliedModelingLib.Probability.RademacherMatrix.abs_rademacherSign, one_mul]
      _ ≤ ∑ _index : Fin sampleCount, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro index _
            exact hvalue hypothesis index
      _ = sampleCount := by simp
  have hscoreBdd : ∀ signs, BddAbove (Set.range (score signs)) := by
    intro signs
    refine ⟨sampleCount, ?_⟩
    rintro result ⟨hypothesis, rfl⟩
    exact (le_abs_self _).trans (hscoreAbs signs hypothesis)
  have hscoreUpper : ∀ signs, sSup (Set.range (score signs)) ≤ sampleCount := by
    intro signs
    apply csSup_le (Set.range_nonempty _)
    rintro result ⟨hypothesis, rfl⟩
    exact (le_abs_self _).trans (hscoreAbs signs hypothesis)
  have hscoreLower : ∀ signs,
      -(sampleCount : ℝ) ≤ sSup (Set.range (score signs)) := by
    intro signs
    let hypothesis : Hypothesis := Classical.choice (inferInstance : Nonempty Hypothesis)
    calc
      -(sampleCount : ℝ) ≤ score signs hypothesis := by
        exact (neg_le_neg (hscoreAbs signs hypothesis)).trans (neg_abs_le _)
      _ ≤ sSup (Set.range (score signs)) := by
        apply le_csSup (hscoreBdd signs)
        exact ⟨hypothesis, rfl⟩
  have havgUpper : AppliedModelingLib.pmfExp
      (AppliedModelingLib.uniformPMF (Fin sampleCount → Bool))
      (fun signs => sSup (Set.range (score signs))) ≤ sampleCount := by
    exact AppliedModelingLib.pmfExp_le_of_forall_le _ _ _ hscoreUpper
  have havgLower : -(sampleCount : ℝ) ≤ AppliedModelingLib.pmfExp
      (AppliedModelingLib.uniformPMF (Fin sampleCount → Bool))
      (fun signs => sSup (Set.range (score signs))) := by
    rw [← AppliedModelingLib.pmfExp_const
      (AppliedModelingLib.uniformPMF (Fin sampleCount → Bool)) (-(sampleCount : ℝ))]
    exact AppliedModelingLib.pmfExp_le_pmfExp_of_forall_le _ _ _ hscoreLower
  have hsampleCountReal : (sampleCount : ℝ) ≠ 0 := by
    exact_mod_cast hsampleCount
  have hinterval : (sampleCount : ℝ)⁻¹ * AppliedModelingLib.pmfExp
      (AppliedModelingLib.uniformPMF (Fin sampleCount → Bool))
      (fun signs => sSup (Set.range (score signs))) ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor
    · calc
        -1 = (sampleCount : ℝ)⁻¹ * (-(sampleCount : ℝ)) := by field_simp
        _ ≤ (sampleCount : ℝ)⁻¹ * AppliedModelingLib.pmfExp
            (AppliedModelingLib.uniformPMF (Fin sampleCount → Bool))
            (fun signs => sSup (Set.range (score signs))) := by
              exact mul_le_mul_of_nonneg_left havgLower
                (inv_nonneg.mpr (Nat.cast_nonneg _))
    · calc
        (sampleCount : ℝ)⁻¹ * AppliedModelingLib.pmfExp
            (AppliedModelingLib.uniformPMF (Fin sampleCount → Bool))
            (fun signs => sSup (Set.range (score signs))) ≤
            (sampleCount : ℝ)⁻¹ * sampleCount := by
              exact mul_le_mul_of_nonneg_left havgUpper
                (inv_nonneg.mpr (Nat.cast_nonneg _))
        _ = 1 := by field_simp
  simpa [FiniteRademacher.empiricalOneSidedRademacherSet, score] using hinterval

/-- A countable nonempty measurable `[-1,1]` class has integrable empirical
one-sided Rademacher complexity under every iid population law. -/
theorem integrable_empiricalOneSidedRademacherSet_comp
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome] [Countable Hypothesis]
    [Nonempty Hypothesis] (law : Measure Outcome) [IsProbabilityMeasure law]
    (sampleCount : ℕ) (value : Hypothesis → Outcome → ℝ)
    (hmeasurable : ∀ hypothesis, Measurable (value hypothesis))
    (hvalue : ∀ hypothesis outcome, |value hypothesis outcome| ≤ 1) :
    Integrable (fun sample : Fin sampleCount → Outcome =>
      FiniteRademacher.empiricalOneSidedRademacherSet sampleCount
        (fun hypothesis index => value hypothesis (sample index)))
      (Probability.finiteIIDSampleLaw law sampleCount) := by
  letI : IsProbabilityMeasure
      (Probability.finiteIIDSampleLaw law sampleCount) := by
    unfold Probability.finiteIIDSampleLaw
    infer_instance
  apply Integrable.of_mem_Icc (-1) 1
    (measurable_empiricalOneSidedRademacherSet_comp sampleCount value hmeasurable).aemeasurable
  filter_upwards with sample
  exact empiricalOneSidedRademacherSet_mem_Icc sampleCount
    (fun hypothesis index => value hypothesis (sample index))
    (fun hypothesis index => hvalue hypothesis (sample index))

/-- Negating a bounded countable class cannot increase its expected one-sided
Rademacher complexity.  The fixed-sample inequality is the usual scalar
contraction argument; this theorem supplies the arbitrary-population
integration step needed for lower uniform deviations. -/
theorem expectedOneSidedRademacherSet_negateFunctionClass_le
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome] [Countable Hypothesis]
    [Nonempty Hypothesis] (law : Measure Outcome) [IsProbabilityMeasure law]
    (sampleCount : ℕ) (value : Hypothesis → Outcome → ℝ)
    (hmeasurable : ∀ hypothesis, Measurable (value hypothesis))
    (hvalue : ∀ hypothesis outcome, |value hypothesis outcome| ≤ 1) :
    expectedOneSidedRademacherSet law sampleCount
        (FiniteRademacher.negateFunctionClass value) ≤
      expectedOneSidedRademacherSet law sampleCount value := by
  unfold expectedOneSidedRademacherSet
  apply integral_mono_ae
  · apply integrable_empiricalOneSidedRademacherSet_comp law sampleCount
      (FiniteRademacher.negateFunctionClass value)
    · intro hypothesis
      exact (hmeasurable hypothesis).neg
    · intro hypothesis outcome
      simpa [FiniteRademacher.negateFunctionClass] using hvalue hypothesis outcome
  · exact integrable_empiricalOneSidedRademacherSet_comp law sampleCount value
      hmeasurable hvalue
  filter_upwards with sample
  exact FiniteRademacher.empiricalOneSidedRademacherSet_negateFunctionClass_le
    sampleCount (fun hypothesis index => value hypothesis (sample index))
    (fun hypothesis index => hvalue hypothesis (sample index))

/-- Replacing one observation changes a bounded class's empirical one-sided
Rademacher complexity by at most `2 / m`.  This is the sensitivity needed for
the empirical-complexity form of the standard Rademacher lemma. -/
theorem abs_empiricalOneSidedRademacherSet_comp_sub_update_le_two_inv
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome] [Nonempty Hypothesis]
    (sampleCount : ℕ) (value : Hypothesis → Outcome → ℝ)
    (hvalue : ∀ hypothesis outcome, |value hypothesis outcome| ≤ 1)
    (sample : Fin sampleCount → Outcome) (index : Fin sampleCount)
    (replacement : Outcome) :
    |FiniteRademacher.empiricalOneSidedRademacherSet sampleCount
        (fun hypothesis coordinate => value hypothesis (sample coordinate)) -
      FiniteRademacher.empiricalOneSidedRademacherSet sampleCount
        (fun hypothesis coordinate =>
          value hypothesis ((Function.update sample index replacement) coordinate))| ≤
      2 * (sampleCount : ℝ)⁻¹ := by
  let score : (Fin sampleCount → Outcome) → (Fin sampleCount → Bool) → Hypothesis → ℝ :=
    fun dataset signs hypothesis => ∑ coordinate : Fin sampleCount,
      AppliedModelingLib.Probability.RademacherMatrix.rademacherSign (signs coordinate) *
        value hypothesis (dataset coordinate)
  have hscoreBdd : ∀ dataset signs, BddAbove (Set.range (score dataset signs)) := by
    intro dataset signs
    exact FiniteRademacher.bddAbove_range_rademacherScore_of_abs_le_one sampleCount
      (fun hypothesis coordinate => value hypothesis (dataset coordinate))
      (fun hypothesis coordinate => hvalue hypothesis (dataset coordinate)) signs
  have hscoreUpdate : ∀ signs hypothesis,
      |score sample signs hypothesis -
          score (Function.update sample index replacement) signs hypothesis| ≤ 2 := by
    intro signs hypothesis
    have hevaluatedUpdate :
        (fun coordinate : Fin sampleCount =>
          AppliedModelingLib.Probability.RademacherMatrix.rademacherSign (signs coordinate) *
            value hypothesis ((Function.update sample index replacement) coordinate)) =
        Function.update
          (fun coordinate : Fin sampleCount =>
            AppliedModelingLib.Probability.RademacherMatrix.rademacherSign (signs coordinate) *
              value hypothesis (sample coordinate))
          index
          (AppliedModelingLib.Probability.RademacherMatrix.rademacherSign (signs index) *
            value hypothesis replacement) := by
      funext coordinate
      by_cases hcoordinate : coordinate = index
      · subst coordinate
        simp
      · simp [Function.update_of_ne hcoordinate]
    have hsumUpdate :
        (∑ coordinate : Fin sampleCount,
          AppliedModelingLib.Probability.RademacherMatrix.rademacherSign (signs coordinate) *
            value hypothesis ((Function.update sample index replacement) coordinate)) =
          (∑ coordinate : Fin sampleCount,
            AppliedModelingLib.Probability.RademacherMatrix.rademacherSign (signs coordinate) *
              value hypothesis (sample coordinate)) -
            AppliedModelingLib.Probability.RademacherMatrix.rademacherSign (signs index) *
              value hypothesis (sample index) +
            AppliedModelingLib.Probability.RademacherMatrix.rademacherSign (signs index) *
              value hypothesis replacement := by
      have horiginal :
          (∑ coordinate : Fin sampleCount,
            AppliedModelingLib.Probability.RademacherMatrix.rademacherSign (signs coordinate) *
              value hypothesis (sample coordinate)) =
            AppliedModelingLib.Probability.RademacherMatrix.rademacherSign (signs index) *
                value hypothesis (sample index) +
              ∑ coordinate ∈ (Finset.univ : Finset (Fin sampleCount)) \ {index},
                AppliedModelingLib.Probability.RademacherMatrix.rademacherSign
                  (signs coordinate) * value hypothesis (sample coordinate) := by
        rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin sampleCount))
          (fun coordinate =>
            AppliedModelingLib.Probability.RademacherMatrix.rademacherSign (signs coordinate) *
              value hypothesis (sample coordinate)) (Finset.mem_univ index)]
        congr 1
        rw [Finset.sdiff_singleton_eq_erase]
      rw [hevaluatedUpdate, Finset.sum_update_of_mem (Finset.mem_univ index), horiginal]
      ring
    have hdifference :
        score sample signs hypothesis -
          score (Function.update sample index replacement) signs hypothesis =
          AppliedModelingLib.Probability.RademacherMatrix.rademacherSign (signs index) *
            (value hypothesis (sample index) - value hypothesis replacement) := by
      dsimp [score]
      rw [hsumUpdate]
      ring
    rw [hdifference, abs_mul,
      AppliedModelingLib.Probability.RademacherMatrix.abs_rademacherSign, one_mul]
    rw [abs_le]
    constructor <;> linarith [((abs_le.mp (hvalue hypothesis (sample index))).1),
      ((abs_le.mp (hvalue hypothesis (sample index))).2),
      ((abs_le.mp (hvalue hypothesis replacement)).1),
      ((abs_le.mp (hvalue hypothesis replacement)).2)]
  have hsupUpdate : ∀ signs,
      |sSup (Set.range (score sample signs)) -
          sSup (Set.range (score (Function.update sample index replacement) signs))| ≤ 2 := by
    intro signs
    apply FiniteRademacher.abs_sSup_range_sub_sSup_range_le_of_forall_abs_sub_le
    · exact hscoreBdd sample signs
    · exact hscoreBdd (Function.update sample index replacement) signs
    · intro hypothesis
      exact hscoreUpdate signs hypothesis
  unfold FiniteRademacher.empiricalOneSidedRademacherSet
  change |(sampleCount : ℝ)⁻¹ * AppliedModelingLib.pmfExp
      (AppliedModelingLib.uniformPMF (Fin sampleCount → Bool))
      (fun signs => sSup (Set.range (score sample signs))) -
    (sampleCount : ℝ)⁻¹ * AppliedModelingLib.pmfExp
      (AppliedModelingLib.uniformPMF (Fin sampleCount → Bool))
      (fun signs => sSup (Set.range
        (score (Function.update sample index replacement) signs)))| ≤
      2 * (sampleCount : ℝ)⁻¹
  rw [← mul_sub, abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  calc
    (sampleCount : ℝ)⁻¹ *
        |AppliedModelingLib.pmfExp (AppliedModelingLib.uniformPMF (Fin sampleCount → Bool))
            (fun signs => sSup (Set.range (score sample signs))) -
          AppliedModelingLib.pmfExp (AppliedModelingLib.uniformPMF (Fin sampleCount → Bool))
            (fun signs => sSup (Set.range
              (score (Function.update sample index replacement) signs)))| ≤
        (sampleCount : ℝ)⁻¹ * 2 := by
          apply mul_le_mul_of_nonneg_left
            (AppliedModelingLib.FiniteCoupling.abs_pmfExp_sub_le_of_forall_abs_sub_le
              (AppliedModelingLib.uniformPMF (Fin sampleCount → Bool)) _ _ 2 hsupUpdate)
          exact inv_nonneg.mpr (Nat.cast_nonneg _)
    _ = 2 * (sampleCount : ℝ)⁻¹ := by ring

/-- Empirical one-sided Rademacher complexity has the same `[-1,1]`
bounded-differences scale as the original score class: its upper tail about
its expectation is at most `exp (-m ε² / 2)`. -/
theorem measureReal_empiricalOneSidedRademacherSet_sub_integral_ge_le_exp_of_abs_le_one
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome] [Countable Hypothesis]
    [Nonempty Hypothesis] (law : Measure Outcome) [IsProbabilityMeasure law]
    (sampleCount : ℕ) (hsampleCount : 0 < sampleCount)
    (value : Hypothesis → Outcome → ℝ)
    (hmeasurable : ∀ hypothesis, Measurable (value hypothesis))
    (hvalue : ∀ hypothesis outcome, |value hypothesis outcome| ≤ 1)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) :
    (Probability.finiteIIDSampleLaw law sampleCount).real
      {sample | epsilon ≤
        FiniteRademacher.empiricalOneSidedRademacherSet sampleCount
          (fun hypothesis index => value hypothesis (sample index)) -
        ∫ sample : Fin sampleCount → Outcome,
          FiniteRademacher.empiricalOneSidedRademacherSet sampleCount
            (fun hypothesis index => value hypothesis (sample index)) ∂
            Probability.finiteIIDSampleLaw law sampleCount} ≤
      Real.exp (-((sampleCount : ℝ) * epsilon ^ 2) / 2) := by
  let empiricalComplexity : (Fin sampleCount → Outcome) → ℝ := fun sample =>
    FiniteRademacher.empiricalOneSidedRademacherSet sampleCount
      (fun hypothesis index => value hypothesis (sample index))
  letI : IsProbabilityMeasure (Probability.finiteIIDSampleLaw law sampleCount) := by
    unfold Probability.finiteIIDSampleLaw
    infer_instance
  have htail :=
    AppliedModelingLib.Probability.MeasureBoundedDifferences.measureReal_finiteIID_sub_integral_ge_le_of_boundedDifferences
      law sampleCount empiricalComplexity
      (measurable_empiricalOneSidedRademacherSet_comp sampleCount value hmeasurable)
      (fun sample => empiricalOneSidedRademacherSet_mem_Icc sampleCount
        (fun hypothesis index => value hypothesis (sample index))
        (fun hypothesis index => hvalue hypothesis (sample index)))
      (fun _ : Fin sampleCount => 2 * (sampleCount : ℝ)⁻¹)
      (by
        intro index sample replacement
        exact abs_empiricalOneSidedRademacherSet_comp_sub_update_le_two_inv
          sampleCount value hvalue sample index replacement)
      hepsilon
  change (Probability.finiteIIDSampleLaw law sampleCount).real
      {sample | epsilon ≤ empiricalComplexity sample -
        ∫ sample : Fin sampleCount → Outcome, empiricalComplexity sample ∂
          Probability.finiteIIDSampleLaw law sampleCount} ≤
      Real.exp (-((sampleCount : ℝ) * epsilon ^ 2) / 2)
  calc
    (Probability.finiteIIDSampleLaw law sampleCount).real
        {sample | epsilon ≤ empiricalComplexity sample -
          ∫ sample : Fin sampleCount → Outcome, empiricalComplexity sample ∂
            Probability.finiteIIDSampleLaw law sampleCount} ≤
        Real.exp (-epsilon ^ 2 /
          (2 * ∑ _index : Fin sampleCount,
            (2 * (sampleCount : ℝ)⁻¹) ^ 2 / 4)) := htail
    _ = Real.exp (-((sampleCount : ℝ) * epsilon ^ 2) / 2) := by
      congr 1
      have hcount : (sampleCount : ℝ) ≠ 0 := by
        exact_mod_cast hsampleCount.ne'
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp [hcount]
      norm_num

/-- The corresponding lower tail for empirical one-sided Rademacher
complexity.  It is stated in the direction used to replace statistical
complexity by its observed empirical value. -/
theorem measureReal_integral_sub_empiricalOneSidedRademacherSet_ge_le_exp_of_abs_le_one
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome] [Countable Hypothesis]
    [Nonempty Hypothesis] (law : Measure Outcome) [IsProbabilityMeasure law]
    (sampleCount : ℕ) (hsampleCount : 0 < sampleCount)
    (value : Hypothesis → Outcome → ℝ)
    (hmeasurable : ∀ hypothesis, Measurable (value hypothesis))
    (hvalue : ∀ hypothesis outcome, |value hypothesis outcome| ≤ 1)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) :
    (Probability.finiteIIDSampleLaw law sampleCount).real
      {sample | epsilon ≤
        (∫ sample : Fin sampleCount → Outcome,
          FiniteRademacher.empiricalOneSidedRademacherSet sampleCount
            (fun hypothesis index => value hypothesis (sample index)) ∂
            Probability.finiteIIDSampleLaw law sampleCount) -
          FiniteRademacher.empiricalOneSidedRademacherSet sampleCount
            (fun hypothesis index => value hypothesis (sample index))} ≤
      Real.exp (-((sampleCount : ℝ) * epsilon ^ 2) / 2) := by
  let empiricalComplexity : (Fin sampleCount → Outcome) → ℝ := fun sample =>
    FiniteRademacher.empiricalOneSidedRademacherSet sampleCount
      (fun hypothesis index => value hypothesis (sample index))
  letI : IsProbabilityMeasure (Probability.finiteIIDSampleLaw law sampleCount) := by
    unfold Probability.finiteIIDSampleLaw
    infer_instance
  have htail :=
    AppliedModelingLib.Probability.MeasureBoundedDifferences.measureReal_finiteIID_sub_integral_ge_le_of_boundedDifferences
      law sampleCount (fun sample => -empiricalComplexity sample)
      ((measurable_empiricalOneSidedRademacherSet_comp sampleCount value hmeasurable).neg)
      (fun sample => by
        have hcomplexity := empiricalOneSidedRademacherSet_mem_Icc sampleCount
          (fun hypothesis index => value hypothesis (sample index))
          (fun hypothesis index => hvalue hypothesis (sample index))
        change empiricalComplexity sample ∈ Set.Icc (-1 : ℝ) 1 at hcomplexity
        change -empiricalComplexity sample ∈ Set.Icc (-1 : ℝ) 1
        constructor <;> linarith [hcomplexity.1, hcomplexity.2])
      (fun _ : Fin sampleCount => 2 * (sampleCount : ℝ)⁻¹)
      (by
        intro index sample replacement
        change |-empiricalComplexity sample -
            -empiricalComplexity (Function.update sample index replacement)| ≤
          2 * (sampleCount : ℝ)⁻¹
        rw [show -empiricalComplexity sample -
            -empiricalComplexity (Function.update sample index replacement) =
          -(empiricalComplexity sample -
            empiricalComplexity (Function.update sample index replacement)) by ring,
          abs_neg]
        exact abs_empiricalOneSidedRademacherSet_comp_sub_update_le_two_inv
          sampleCount value hvalue sample index replacement)
      hepsilon
  have hset :
      {sample | epsilon ≤
        (∫ sample : Fin sampleCount → Outcome, empiricalComplexity sample ∂
          Probability.finiteIIDSampleLaw law sampleCount) - empiricalComplexity sample} =
      {sample | epsilon ≤ -empiricalComplexity sample -
        ∫ sample : Fin sampleCount → Outcome, -empiricalComplexity sample ∂
          Probability.finiteIIDSampleLaw law sampleCount} := by
    ext sample
    rw [integral_neg]
    change (epsilon ≤
      (∫ sample : Fin sampleCount → Outcome, empiricalComplexity sample ∂
        Probability.finiteIIDSampleLaw law sampleCount) - empiricalComplexity sample) ↔
      (epsilon ≤ -empiricalComplexity sample -
        -(∫ sample : Fin sampleCount → Outcome, empiricalComplexity sample ∂
          Probability.finiteIIDSampleLaw law sampleCount))
    constructor <;> intro hmembership <;> linarith
  change (Probability.finiteIIDSampleLaw law sampleCount).real
      {sample | epsilon ≤
        (∫ sample : Fin sampleCount → Outcome, empiricalComplexity sample ∂
          Probability.finiteIIDSampleLaw law sampleCount) - empiricalComplexity sample} ≤
      Real.exp (-((sampleCount : ℝ) * epsilon ^ 2) / 2)
  rw [hset]
  calc
    (Probability.finiteIIDSampleLaw law sampleCount).real
        {sample | epsilon ≤ -empiricalComplexity sample -
          ∫ sample : Fin sampleCount → Outcome, -empiricalComplexity sample ∂
            Probability.finiteIIDSampleLaw law sampleCount} ≤
        Real.exp (-epsilon ^ 2 /
          (2 * ∑ _index : Fin sampleCount,
            (2 * (sampleCount : ℝ)⁻¹) ^ 2 / 4)) := htail
    _ = Real.exp (-((sampleCount : ℝ) * epsilon ^ 2) / 2) := by
      congr 1
      have hcount : (sampleCount : ℝ) ≠ 0 := by
        exact_mod_cast hsampleCount.ne'
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp [hcount]
      norm_num

/-- Confidence-level lower tail for empirical one-sided Rademacher
complexity. -/
theorem measureReal_integral_sub_empiricalOneSidedRademacherSet_ge_sqrt_two_log_div_le_of_abs_le_one
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome] [Countable Hypothesis]
    [Nonempty Hypothesis] (law : Measure Outcome) [IsProbabilityMeasure law]
    (sampleCount : ℕ) (hsampleCount : 0 < sampleCount)
    (value : Hypothesis → Outcome → ℝ)
    (hmeasurable : ∀ hypothesis, Measurable (value hypothesis))
    (hvalue : ∀ hypothesis outcome, |value hypothesis outcome| ≤ 1)
    (delta : ℝ) (hdeltaPositive : 0 < delta) (hdeltaOne : delta < 1) :
    (Probability.finiteIIDSampleLaw law sampleCount).real
      {sample | Real.sqrt (2 * Real.log (1 / delta) / (sampleCount : ℝ)) ≤
        (∫ sample : Fin sampleCount → Outcome,
          FiniteRademacher.empiricalOneSidedRademacherSet sampleCount
            (fun hypothesis index => value hypothesis (sample index)) ∂
            Probability.finiteIIDSampleLaw law sampleCount) -
          FiniteRademacher.empiricalOneSidedRademacherSet sampleCount
            (fun hypothesis index => value hypothesis (sample index))} ≤ delta := by
  let epsilon : ℝ := Real.sqrt (2 * Real.log (1 / delta) / (sampleCount : ℝ))
  have hsampleCountReal : 0 < (sampleCount : ℝ) := by
    exact_mod_cast hsampleCount
  have hinverseAtLeastOne : 1 ≤ 1 / delta := by
    rw [le_div_iff₀ hdeltaPositive]
    linarith
  have hlogNonneg : 0 ≤ Real.log (1 / delta) :=
    Real.log_nonneg hinverseAtLeastOne
  have hepsilonNonneg : 0 ≤ epsilon := Real.sqrt_nonneg _
  have hepsilonSq : epsilon ^ 2 =
      2 * Real.log (1 / delta) / (sampleCount : ℝ) := by
    exact Real.sq_sqrt
      (div_nonneg (mul_nonneg (by norm_num) hlogNonneg) hsampleCountReal.le)
  have htail :=
    measureReal_integral_sub_empiricalOneSidedRademacherSet_ge_le_exp_of_abs_le_one
      law sampleCount hsampleCount value hmeasurable hvalue hepsilonNonneg
  have hexponent : -((sampleCount : ℝ) * epsilon ^ 2) / 2 =
      -Real.log (1 / delta) := by
    rw [hepsilonSq]
    field_simp [hsampleCountReal.ne']
  have hprobability : Real.exp (-Real.log (1 / delta)) = delta := by
    rw [Real.exp_neg, Real.exp_log (one_div_pos.mpr hdeltaPositive)]
    field_simp [hdeltaPositive.ne']
  change (Probability.finiteIIDSampleLaw law sampleCount).real
      {sample | epsilon ≤
        (∫ sample : Fin sampleCount → Outcome,
          FiniteRademacher.empiricalOneSidedRademacherSet sampleCount
            (fun hypothesis index => value hypothesis (sample index)) ∂
            Probability.finiteIIDSampleLaw law sampleCount) -
          FiniteRademacher.empiricalOneSidedRademacherSet sampleCount
            (fun hypothesis index => value hypothesis (sample index))} ≤ delta
  calc
    (Probability.finiteIIDSampleLaw law sampleCount).real
        {sample | epsilon ≤
          (∫ sample : Fin sampleCount → Outcome,
            FiniteRademacher.empiricalOneSidedRademacherSet sampleCount
              (fun hypothesis index => value hypothesis (sample index)) ∂
              Probability.finiteIIDSampleLaw law sampleCount) -
            FiniteRademacher.empiricalOneSidedRademacherSet sampleCount
              (fun hypothesis index => value hypothesis (sample index))} ≤
        Real.exp (-((sampleCount : ℝ) * epsilon ^ 2) / 2) := htail
    _ = Real.exp (-Real.log (1 / delta)) := by rw [hexponent]
    _ = delta := hprobability

/-- The second, signed symmetrization step for a countable measurable
`[0,1]` class over an arbitrary population law. -/
theorem integral_pairedUniformDifferenceSet_le_two_expectedOneSidedRademacherSet
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome] [Countable Hypothesis]
    [Nonempty Hypothesis] (law : Measure Outcome) [IsProbabilityMeasure law]
    (sampleCount : ℕ) (hsampleCount : 0 < sampleCount)
    (value : Hypothesis → Outcome → ℝ)
    (hmeasurable : ∀ hypothesis, Measurable (value hypothesis))
    (hbounded : ∀ hypothesis outcome,
      value hypothesis outcome ∈ Set.Icc (0 : ℝ) 1) :
    (∫ pairedSample : Fin sampleCount → Outcome × Outcome,
      pairedUniformDifferenceSet sampleCount value pairedSample ∂
        Probability.finiteIIDSampleLaw (law.prod law) sampleCount) ≤
      2 * expectedOneSidedRademacherSet law sampleCount value := by
  let pairedLaw : Measure (Fin sampleCount → Outcome × Outcome) :=
    Probability.finiteIIDSampleLaw (law.prod law) sampleCount
  let signLaw := AppliedModelingLib.uniformPMF (Fin sampleCount → Bool)
  let firstComplexity : (Fin sampleCount → Outcome × Outcome) → ℝ :=
    fun pairedSample =>
      FiniteRademacher.empiricalOneSidedRademacherSet sampleCount
        (fun hypothesis index => value hypothesis (pairedSample index).1)
  let secondComplexity : (Fin sampleCount → Outcome × Outcome) → ℝ :=
    fun pairedSample =>
      FiniteRademacher.empiricalOneSidedRademacherSet sampleCount
        (fun hypothesis index => value hypothesis (pairedSample index).2)
  let signAverage : (Fin sampleCount → Outcome × Outcome) → ℝ :=
    fun pairedSample => AppliedModelingLib.pmfExp signLaw (fun signs =>
      signedPairedUniformDifferenceSet sampleCount value signs pairedSample)
  letI : IsProbabilityMeasure pairedLaw := by
    unfold pairedLaw Probability.finiteIIDSampleLaw
    infer_instance
  have habs : ∀ hypothesis outcome, |value hypothesis outcome| ≤ 1 := by
    intro hypothesis outcome
    have hinterval := hbounded hypothesis outcome
    exact abs_le.mpr ⟨by linarith [hinterval.1], hinterval.2⟩
  have hcomplexityIntegrable : Integrable (fun sample : Fin sampleCount → Outcome =>
      FiniteRademacher.empiricalOneSidedRademacherSet sampleCount
        (fun hypothesis index => value hypothesis (sample index)))
      (Probability.finiteIIDSampleLaw law sampleCount) :=
    integrable_empiricalOneSidedRademacherSet_comp law sampleCount value hmeasurable habs
  have hfirstSampleMeasurable : Measurable (fun pairedSample :
      Fin sampleCount → Outcome × Outcome => fun index => (pairedSample index).1) := by
    apply measurable_pi_lambda
    intro index
    exact measurable_fst.comp (measurable_pi_apply index)
  have hsecondSampleMeasurable : Measurable (fun pairedSample :
      Fin sampleCount → Outcome × Outcome => fun index => (pairedSample index).2) := by
    apply measurable_pi_lambda
    intro index
    exact measurable_snd.comp (measurable_pi_apply index)
  have hfirstIntegrable : Integrable firstComplexity pairedLaw := by
    apply Integrable.of_mem_Icc (-1) 1
      ((measurable_empiricalOneSidedRademacherSet_comp sampleCount value hmeasurable).comp
        hfirstSampleMeasurable).aemeasurable
    filter_upwards with pairedSample
    exact empiricalOneSidedRademacherSet_mem_Icc sampleCount
      (fun hypothesis index => value hypothesis (pairedSample index).1)
      (fun hypothesis index => habs hypothesis (pairedSample index).1)
  have hsecondIntegrable : Integrable secondComplexity pairedLaw := by
    apply Integrable.of_mem_Icc (-1) 1
      ((measurable_empiricalOneSidedRademacherSet_comp sampleCount value hmeasurable).comp
        hsecondSampleMeasurable).aemeasurable
    filter_upwards with pairedSample
    exact empiricalOneSidedRademacherSet_mem_Icc sampleCount
      (fun hypothesis index => value hypothesis (pairedSample index).2)
      (fun hypothesis index => habs hypothesis (pairedSample index).2)
  have hsignAverageMeasurable : Measurable signAverage := by
    unfold signAverage signLaw AppliedModelingLib.pmfExp
    apply Finset.measurable_sum
    intro signs _
    apply Measurable.const_mul
    exact measurable_signedPairedUniformDifferenceSet_comp sampleCount value
      hmeasurable signs
  have hsignAverageBound : ∀ pairedSample,
      signAverage pairedSample ∈ Set.Icc (-1 : ℝ) 1 := by
    intro pairedSample
    change AppliedModelingLib.pmfExp signLaw (fun signs =>
      signedPairedUniformDifferenceSet sampleCount value signs pairedSample) ∈
        Set.Icc (-1 : ℝ) 1
    constructor
    · rw [← AppliedModelingLib.pmfExp_const signLaw (-1 : ℝ)]
      apply AppliedModelingLib.pmfExp_le_pmfExp_of_forall_le
      intro signs
      exact (signedPairedUniformDifferenceSet_mem_Icc sampleCount hsampleCount value
        hbounded signs pairedSample).1
    · rw [← AppliedModelingLib.pmfExp_const signLaw (1 : ℝ)]
      apply AppliedModelingLib.pmfExp_le_pmfExp_of_forall_le
      intro signs
      exact (signedPairedUniformDifferenceSet_mem_Icc sampleCount hsampleCount value
        hbounded signs pairedSample).2
  have hsignAverageIntegrable : Integrable signAverage pairedLaw := by
    apply Integrable.of_mem_Icc (-1) 1 hsignAverageMeasurable.aemeasurable
    filter_upwards with pairedSample
    exact hsignAverageBound pairedSample
  have hsignAverageLe : ∀ pairedSample,
      signAverage pairedSample ≤ firstComplexity pairedSample + secondComplexity pairedSample := by
    intro pairedSample
    simpa only [signAverage, firstComplexity, secondComplexity, signLaw] using
      pmfExp_signedPairedUniformDifferenceSet_le_add_empiricalOneSidedRademacherSet
      sampleCount value habs pairedSample
  have hfirstIntegral : (∫ pairedSample : Fin sampleCount → Outcome × Outcome,
      firstComplexity pairedSample ∂pairedLaw) =
      expectedOneSidedRademacherSet law sampleCount value := by
    simpa only [firstComplexity, pairedLaw, expectedOneSidedRademacherSet] using
      integral_empiricalOneSidedRademacherSet_comp_fst_eq_integral law sampleCount value
        hcomplexityIntegrable
  have hsecondIntegral : (∫ pairedSample : Fin sampleCount → Outcome × Outcome,
      secondComplexity pairedSample ∂pairedLaw) =
      expectedOneSidedRademacherSet law sampleCount value := by
    simpa only [secondComplexity, pairedLaw, expectedOneSidedRademacherSet] using
      integral_empiricalOneSidedRademacherSet_comp_snd_eq_integral law sampleCount value
        hcomplexityIntegrable
  calc
    (∫ pairedSample : Fin sampleCount → Outcome × Outcome,
        pairedUniformDifferenceSet sampleCount value pairedSample ∂pairedLaw) =
      AppliedModelingLib.pmfExp signLaw (fun signs =>
        ∫ pairedSample : Fin sampleCount → Outcome × Outcome,
          signedPairedUniformDifferenceSet sampleCount value signs pairedSample ∂pairedLaw) := by
            exact integral_pairedUniformDifferenceSet_eq_pmfExp_integral_signedPairedUniformDifferenceSet
              law sampleCount value
    _ = ∫ pairedSample : Fin sampleCount → Outcome × Outcome,
          signAverage pairedSample ∂pairedLaw := by
            exact pmfExp_integral_signedPairedUniformDifferenceSet_eq_integral_pmfExp_signedPairedUniformDifferenceSet
              law sampleCount hsampleCount value hmeasurable hbounded
    _ ≤ ∫ pairedSample : Fin sampleCount → Outcome × Outcome,
          firstComplexity pairedSample + secondComplexity pairedSample ∂pairedLaw := by
            apply integral_mono hsignAverageIntegrable (hfirstIntegrable.add hsecondIntegrable)
            intro pairedSample
            exact hsignAverageLe pairedSample
    _ = 2 * expectedOneSidedRademacherSet law sampleCount value := by
      rw [integral_add hfirstIntegrable hsecondIntegrable, hfirstIntegral, hsecondIntegral]
      ring

/-- Countable-class ghost and sign symmetrization over an arbitrary iid
population law.  This is the expectation form of the Rademacher bridge. -/
theorem integral_upperUniformDeviationSet_le_two_expectedOneSidedRademacherSet
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome] [Countable Hypothesis]
    [Nonempty Hypothesis] (law : Measure Outcome) [IsProbabilityMeasure law]
    (sampleCount : ℕ) (hsampleCount : 0 < sampleCount)
    (value : Hypothesis → Outcome → ℝ)
    (hmeasurable : ∀ hypothesis, Measurable (value hypothesis))
    (hbounded : ∀ hypothesis outcome,
      value hypothesis outcome ∈ Set.Icc (0 : ℝ) 1) :
    (∫ sample : Fin sampleCount → Outcome,
      upperUniformDeviationSet law sampleCount value sample ∂
        Probability.finiteIIDSampleLaw law sampleCount) ≤
      2 * expectedOneSidedRademacherSet law sampleCount value :=
  (integral_upperUniformDeviationSet_le_integral_pairedUniformDifferenceSet law sampleCount
    hsampleCount value hmeasurable hbounded).trans
    (integral_pairedUniformDifferenceSet_le_two_expectedOneSidedRademacherSet law sampleCount
      hsampleCount value hmeasurable hbounded)

/-- The expectation Rademacher bridge and arbitrary-law McDiarmid theorem
give an explicit one-sided uniform-convergence tail. -/
theorem measureReal_two_expectedOneSidedRademacherSet_add_le_upperUniformDeviationSet_le_exp
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome] [Countable Hypothesis]
    [Nonempty Hypothesis] (law : Measure Outcome) [IsProbabilityMeasure law]
    (sampleCount : ℕ) (hsampleCount : 0 < sampleCount)
    (value : Hypothesis → Outcome → ℝ)
    (hmeasurable : ∀ hypothesis, Measurable (value hypothesis))
    (hbounded : ∀ hypothesis outcome,
      value hypothesis outcome ∈ Set.Icc (0 : ℝ) 1)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) :
    (Probability.finiteIIDSampleLaw law sampleCount).real
      {sample | 2 * expectedOneSidedRademacherSet law sampleCount value + epsilon ≤
        upperUniformDeviationSet law sampleCount value sample} ≤
      Real.exp (-2 * (sampleCount : ℝ) * epsilon ^ 2) := by
  let sampleLaw := Probability.finiteIIDSampleLaw law sampleCount
  letI : IsProbabilityMeasure sampleLaw := by
    unfold sampleLaw Probability.finiteIIDSampleLaw
    infer_instance
  have hmean : (∫ sample : Fin sampleCount → Outcome,
      upperUniformDeviationSet law sampleCount value sample ∂sampleLaw) ≤
      2 * expectedOneSidedRademacherSet law sampleCount value :=
    integral_upperUniformDeviationSet_le_two_expectedOneSidedRademacherSet law sampleCount
      hsampleCount value hmeasurable hbounded
  change (∫ sample : Fin sampleCount → Outcome,
      upperUniformDeviationSet law sampleCount value sample ∂
        Probability.finiteIIDSampleLaw law sampleCount) ≤
      2 * expectedOneSidedRademacherSet law sampleCount value at hmean
  have htail := measureReal_upperUniformDeviationSet_sub_integral_ge_le_exp
    law sampleCount hsampleCount value hmeasurable hbounded hepsilon
  apply le_trans ?_ htail
  apply measureReal_mono
  · intro sample hsample
    change 2 * expectedOneSidedRademacherSet law sampleCount value + epsilon ≤
      upperUniformDeviationSet law sampleCount value sample at hsample
    change epsilon ≤ upperUniformDeviationSet law sampleCount value sample -
      ∫ sample : Fin sampleCount → Outcome,
        upperUniformDeviationSet law sampleCount value sample ∂
          Probability.finiteIIDSampleLaw law sampleCount
    linarith
  · exact measure_ne_top _ _

/-- The source-learning `[-1,1]` form of the expected-Rademacher
uniform-convergence tail.  Relative to the `[0,1]` normalization, the
bounded-differences exponent is necessarily weaker by a factor of four:
`exp (-n * ε² / 2)`. -/
theorem measureReal_two_expectedOneSidedRademacherSet_add_le_upperUniformDeviationSet_le_exp_of_abs_le_one
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome] [Countable Hypothesis]
    [Nonempty Hypothesis] (law : Measure Outcome) [IsProbabilityMeasure law]
    (sampleCount : ℕ) (hsampleCount : 0 < sampleCount)
    (value : Hypothesis → Outcome → ℝ)
    (hmeasurable : ∀ hypothesis, Measurable (value hypothesis))
    (hvalue : ∀ hypothesis outcome, |value hypothesis outcome| ≤ 1)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) :
    (Probability.finiteIIDSampleLaw law sampleCount).real
      {sample | 2 * expectedOneSidedRademacherSet law sampleCount value + epsilon ≤
        upperUniformDeviationSet law sampleCount value sample} ≤
      Real.exp (-(sampleCount : ℝ) * epsilon ^ 2 / 2) := by
  let normalized : Hypothesis → Outcome → ℝ := fun hypothesis outcome =>
    (1 / 2 : ℝ) * value hypothesis outcome + 1 / 2
  have hnormalizedMeasurable : ∀ hypothesis, Measurable (normalized hypothesis) := by
    intro hypothesis
    exact ((hmeasurable hypothesis).const_mul (1 / 2 : ℝ)).add measurable_const
  have hnormalizedBounded : ∀ hypothesis outcome,
      normalized hypothesis outcome ∈ Set.Icc (0 : ℝ) 1 := by
    intro hypothesis outcome
    change (1 / 2 : ℝ) * value hypothesis outcome + 1 / 2 ∈ Set.Icc (0 : ℝ) 1
    have hbounds := abs_le.mp (hvalue hypothesis outcome)
    constructor <;> linarith
  have htail :=
    measureReal_two_expectedOneSidedRademacherSet_add_le_upperUniformDeviationSet_le_exp
      law sampleCount hsampleCount normalized hnormalizedMeasurable hnormalizedBounded
      (epsilon := epsilon / 2) (by linarith)
  have hcomplexity : expectedOneSidedRademacherSet law sampleCount normalized =
      (1 / 2 : ℝ) * expectedOneSidedRademacherSet law sampleCount value := by
    exact expectedOneSidedRademacherSet_affine_half law sampleCount value hvalue
  have hdeviation : ∀ sample,
      upperUniformDeviationSet law sampleCount normalized sample =
        (1 / 2 : ℝ) * upperUniformDeviationSet law sampleCount value sample := by
    intro sample
    exact upperUniformDeviationSet_affine_half law sampleCount hsampleCount value
      hmeasurable hvalue sample
  have hset :
      {sample | 2 * expectedOneSidedRademacherSet law sampleCount value + epsilon ≤
        upperUniformDeviationSet law sampleCount value sample} =
      {sample | 2 * expectedOneSidedRademacherSet law sampleCount normalized + epsilon / 2 ≤
        upperUniformDeviationSet law sampleCount normalized sample} := by
    ext sample
    change (2 * expectedOneSidedRademacherSet law sampleCount value + epsilon ≤
        upperUniformDeviationSet law sampleCount value sample) ↔
      (2 * expectedOneSidedRademacherSet law sampleCount normalized + epsilon / 2 ≤
        upperUniformDeviationSet law sampleCount normalized sample)
    rw [hcomplexity, hdeviation sample]
    constructor <;> intro hmembership <;> linarith
  rw [hset]
  convert htail using 1 <;> ring

/-- The matching lower-deviation Rademacher tail for a countable measurable
`[-1,1]` class.  Its complexity is controlled by the original class rather
than by a separately named negated class, so upper and lower tails can be
combined directly in population-transfer arguments. -/
theorem measureReal_two_expectedOneSidedRademacherSet_add_le_lowerUniformDeviationSet_le_exp_of_abs_le_one
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome] [Countable Hypothesis]
    [Nonempty Hypothesis] (law : Measure Outcome) [IsProbabilityMeasure law]
    (sampleCount : ℕ) (hsampleCount : 0 < sampleCount)
    (value : Hypothesis → Outcome → ℝ)
    (hmeasurable : ∀ hypothesis, Measurable (value hypothesis))
    (hvalue : ∀ hypothesis outcome, |value hypothesis outcome| ≤ 1)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) :
    (Probability.finiteIIDSampleLaw law sampleCount).real
      {sample | 2 * expectedOneSidedRademacherSet law sampleCount value + epsilon ≤
        lowerUniformDeviationSet law sampleCount value sample} ≤
      Real.exp (-(sampleCount : ℝ) * epsilon ^ 2 / 2) := by
  letI : IsProbabilityMeasure (Probability.finiteIIDSampleLaw law sampleCount) := by
    unfold Probability.finiteIIDSampleLaw
    infer_instance
  let negatedValue := FiniteRademacher.negateFunctionClass value
  have hnegatedMeasurable : ∀ hypothesis, Measurable (negatedValue hypothesis) := by
    intro hypothesis
    exact (hmeasurable hypothesis).neg
  have hnegatedBounded : ∀ hypothesis outcome, |negatedValue hypothesis outcome| ≤ 1 := by
    intro hypothesis outcome
    simpa [negatedValue, FiniteRademacher.negateFunctionClass] using
      hvalue hypothesis outcome
  have hcomplexity : expectedOneSidedRademacherSet law sampleCount negatedValue ≤
      expectedOneSidedRademacherSet law sampleCount value := by
    exact expectedOneSidedRademacherSet_negateFunctionClass_le law sampleCount value
      hmeasurable hvalue
  have hupper :=
    measureReal_two_expectedOneSidedRademacherSet_add_le_upperUniformDeviationSet_le_exp_of_abs_le_one
      law sampleCount hsampleCount negatedValue hnegatedMeasurable hnegatedBounded hepsilon
  calc
    (Probability.finiteIIDSampleLaw law sampleCount).real
        {sample | 2 * expectedOneSidedRademacherSet law sampleCount value + epsilon ≤
          lowerUniformDeviationSet law sampleCount value sample} =
      (Probability.finiteIIDSampleLaw law sampleCount).real
        {sample | 2 * expectedOneSidedRademacherSet law sampleCount value + epsilon ≤
          upperUniformDeviationSet law sampleCount negatedValue sample} := by
        congr 1
        ext sample
        simp only [Set.mem_setOf_eq]
        rw [show negatedValue = FiniteRademacher.negateFunctionClass value by rfl,
          lowerUniformDeviationSet_eq_upper_negateFunctionClass]
    _ ≤ (Probability.finiteIIDSampleLaw law sampleCount).real
        {sample | 2 * expectedOneSidedRademacherSet law sampleCount negatedValue + epsilon ≤
          upperUniformDeviationSet law sampleCount negatedValue sample} := by
        apply measureReal_mono
        · intro sample hsample
          change 2 * expectedOneSidedRademacherSet law sampleCount value + epsilon ≤
            upperUniformDeviationSet law sampleCount negatedValue sample at hsample
          change 2 * expectedOneSidedRademacherSet law sampleCount negatedValue + epsilon ≤
            upperUniformDeviationSet law sampleCount negatedValue sample
          linarith
        · exact measure_ne_top _ _
    _ ≤ Real.exp (-(sampleCount : ℝ) * epsilon ^ 2 / 2) := hupper

/-- Confidence-level form of the source's expected-Rademacher lemma for a
countable measurable `[-1,1]` class.  The concentration radius is
`sqrt (2 log (1 / δ) / m)`, the value forced by the preceding sharp
bounded-differences exponent. -/
theorem measureReal_two_expectedOneSidedRademacherSet_add_sqrt_two_log_div_le_upperUniformDeviationSet_le_of_abs_le_one
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome] [Countable Hypothesis]
    [Nonempty Hypothesis] (law : Measure Outcome) [IsProbabilityMeasure law]
    (sampleCount : ℕ) (hsampleCount : 0 < sampleCount)
    (value : Hypothesis → Outcome → ℝ)
    (hmeasurable : ∀ hypothesis, Measurable (value hypothesis))
    (hvalue : ∀ hypothesis outcome, |value hypothesis outcome| ≤ 1)
    (delta : ℝ) (hdeltaPositive : 0 < delta) (hdeltaOne : delta < 1) :
    (Probability.finiteIIDSampleLaw law sampleCount).real
      {sample | 2 * expectedOneSidedRademacherSet law sampleCount value +
          Real.sqrt (2 * Real.log (1 / delta) / (sampleCount : ℝ)) ≤
        upperUniformDeviationSet law sampleCount value sample} ≤ delta := by
  let epsilon : ℝ := Real.sqrt (2 * Real.log (1 / delta) / (sampleCount : ℝ))
  have hsampleCountReal : 0 < (sampleCount : ℝ) := by
    exact_mod_cast hsampleCount
  have hinverseAtLeastOne : 1 ≤ 1 / delta := by
    rw [le_div_iff₀ hdeltaPositive]
    linarith
  have hlogNonneg : 0 ≤ Real.log (1 / delta) :=
    Real.log_nonneg hinverseAtLeastOne
  have hepsilonNonneg : 0 ≤ epsilon := Real.sqrt_nonneg _
  have hepsilonSq : epsilon ^ 2 =
      2 * Real.log (1 / delta) / (sampleCount : ℝ) := by
    exact Real.sq_sqrt
      (div_nonneg (mul_nonneg (by norm_num) hlogNonneg) hsampleCountReal.le)
  have htail :=
    measureReal_two_expectedOneSidedRademacherSet_add_le_upperUniformDeviationSet_le_exp_of_abs_le_one
      law sampleCount hsampleCount value hmeasurable hvalue hepsilonNonneg
  have hexponent : -((sampleCount : ℝ) * epsilon ^ 2) / 2 =
      -Real.log (1 / delta) := by
    rw [hepsilonSq]
    field_simp [hsampleCountReal.ne']
  have hprobability : Real.exp (-Real.log (1 / delta)) = delta := by
    rw [Real.exp_neg, Real.exp_log (one_div_pos.mpr hdeltaPositive)]
    field_simp [hdeltaPositive.ne']
  change (Probability.finiteIIDSampleLaw law sampleCount).real
      {sample | 2 * expectedOneSidedRademacherSet law sampleCount value + epsilon ≤
        upperUniformDeviationSet law sampleCount value sample} ≤ delta
  calc
    (Probability.finiteIIDSampleLaw law sampleCount).real
        {sample | 2 * expectedOneSidedRademacherSet law sampleCount value + epsilon ≤
          upperUniformDeviationSet law sampleCount value sample} ≤
        Real.exp (-((sampleCount : ℝ) * epsilon ^ 2) / 2) := by
          convert htail using 1 <;> ring
    _ = Real.exp (-Real.log (1 / delta)) := by rw [hexponent]
    _ = delta := hprobability

/-- Confidence-level lower-deviation companion to the expected-Rademacher
uniform-convergence theorem.  It has the same sharp `sqrt (2 log(1/δ)/m)`
radius as the upper tail. -/
theorem measureReal_two_expectedOneSidedRademacherSet_add_sqrt_two_log_div_le_lowerUniformDeviationSet_le_of_abs_le_one
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome] [Countable Hypothesis]
    [Nonempty Hypothesis] (law : Measure Outcome) [IsProbabilityMeasure law]
    (sampleCount : ℕ) (hsampleCount : 0 < sampleCount)
    (value : Hypothesis → Outcome → ℝ)
    (hmeasurable : ∀ hypothesis, Measurable (value hypothesis))
    (hvalue : ∀ hypothesis outcome, |value hypothesis outcome| ≤ 1)
    (delta : ℝ) (hdeltaPositive : 0 < delta) (hdeltaOne : delta < 1) :
    (Probability.finiteIIDSampleLaw law sampleCount).real
      {sample | 2 * expectedOneSidedRademacherSet law sampleCount value +
          Real.sqrt (2 * Real.log (1 / delta) / (sampleCount : ℝ)) ≤
        lowerUniformDeviationSet law sampleCount value sample} ≤ delta := by
  letI : IsProbabilityMeasure (Probability.finiteIIDSampleLaw law sampleCount) := by
    unfold Probability.finiteIIDSampleLaw
    infer_instance
  let negatedValue := FiniteRademacher.negateFunctionClass value
  have hnegatedMeasurable : ∀ hypothesis, Measurable (negatedValue hypothesis) := by
    intro hypothesis
    exact (hmeasurable hypothesis).neg
  have hnegatedBounded : ∀ hypothesis outcome, |negatedValue hypothesis outcome| ≤ 1 := by
    intro hypothesis outcome
    simpa [negatedValue, FiniteRademacher.negateFunctionClass] using
      hvalue hypothesis outcome
  have hcomplexity : expectedOneSidedRademacherSet law sampleCount negatedValue ≤
      expectedOneSidedRademacherSet law sampleCount value := by
    exact expectedOneSidedRademacherSet_negateFunctionClass_le law sampleCount value
      hmeasurable hvalue
  have hupper :=
    measureReal_two_expectedOneSidedRademacherSet_add_sqrt_two_log_div_le_upperUniformDeviationSet_le_of_abs_le_one
      law sampleCount hsampleCount negatedValue hnegatedMeasurable hnegatedBounded delta
      hdeltaPositive hdeltaOne
  calc
    (Probability.finiteIIDSampleLaw law sampleCount).real
        {sample | 2 * expectedOneSidedRademacherSet law sampleCount value +
            Real.sqrt (2 * Real.log (1 / delta) / (sampleCount : ℝ)) ≤
          lowerUniformDeviationSet law sampleCount value sample} =
      (Probability.finiteIIDSampleLaw law sampleCount).real
        {sample | 2 * expectedOneSidedRademacherSet law sampleCount value +
            Real.sqrt (2 * Real.log (1 / delta) / (sampleCount : ℝ)) ≤
          upperUniformDeviationSet law sampleCount negatedValue sample} := by
        congr 1
        ext sample
        simp only [Set.mem_setOf_eq]
        rw [show negatedValue = FiniteRademacher.negateFunctionClass value by rfl,
          lowerUniformDeviationSet_eq_upper_negateFunctionClass]
    _ ≤ (Probability.finiteIIDSampleLaw law sampleCount).real
        {sample | 2 * expectedOneSidedRademacherSet law sampleCount negatedValue +
            Real.sqrt (2 * Real.log (1 / delta) / (sampleCount : ℝ)) ≤
          upperUniformDeviationSet law sampleCount negatedValue sample} := by
        apply measureReal_mono
        · intro sample hsample
          change 2 * expectedOneSidedRademacherSet law sampleCount value +
              Real.sqrt (2 * Real.log (1 / delta) / (sampleCount : ℝ)) ≤
            upperUniformDeviationSet law sampleCount negatedValue sample at hsample
          change 2 * expectedOneSidedRademacherSet law sampleCount negatedValue +
              Real.sqrt (2 * Real.log (1 / delta) / (sampleCount : ℝ)) ≤
            upperUniformDeviationSet law sampleCount negatedValue sample
          linarith
        · exact measure_ne_top _ _
    _ ≤ delta := hupper

/-- The empirical-Rademacher confidence form of the standard uniform
convergence lemma for a countable measurable `[-1,1]` class.  Each of the two
McDiarmid steps uses failure budget `δ / 2`, producing the checked radius
`sqrt (2 log (2 / δ) / m)`. -/
theorem measureReal_two_empiricalOneSidedRademacherSet_add_three_sqrt_two_log_div_le_upperUniformDeviationSet_le_of_abs_le_one
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome] [Countable Hypothesis]
    [Nonempty Hypothesis] (law : Measure Outcome) [IsProbabilityMeasure law]
    (sampleCount : ℕ) (hsampleCount : 0 < sampleCount)
    (value : Hypothesis → Outcome → ℝ)
    (hmeasurable : ∀ hypothesis, Measurable (value hypothesis))
    (hvalue : ∀ hypothesis outcome, |value hypothesis outcome| ≤ 1)
    (delta : ℝ) (hdeltaPositive : 0 < delta) (hdeltaOne : delta < 1) :
    (Probability.finiteIIDSampleLaw law sampleCount).real
      {sample |
        2 * FiniteRademacher.empiricalOneSidedRademacherSet sampleCount
            (fun hypothesis index => value hypothesis (sample index)) +
          3 * Real.sqrt (2 * Real.log (2 / delta) / (sampleCount : ℝ)) ≤
          upperUniformDeviationSet law sampleCount value sample} ≤ delta := by
  let sampleLaw : Measure (Fin sampleCount → Outcome) :=
    Probability.finiteIIDSampleLaw law sampleCount
  let empiricalComplexity : (Fin sampleCount → Outcome) → ℝ := fun sample =>
    FiniteRademacher.empiricalOneSidedRademacherSet sampleCount
      (fun hypothesis index => value hypothesis (sample index))
  let statisticalComplexity : ℝ := expectedOneSidedRademacherSet law sampleCount value
  let radius : ℝ := Real.sqrt (2 * Real.log (2 / delta) / (sampleCount : ℝ))
  let upperBad : Set (Fin sampleCount → Outcome) := {sample |
    2 * statisticalComplexity + radius ≤
      upperUniformDeviationSet law sampleCount value sample}
  let complexityBad : Set (Fin sampleCount → Outcome) := {sample |
    radius ≤ statisticalComplexity - empiricalComplexity sample}
  let sourceBad : Set (Fin sampleCount → Outcome) := {sample |
    2 * empiricalComplexity sample + 3 * radius ≤
      upperUniformDeviationSet law sampleCount value sample}
  letI : IsProbabilityMeasure sampleLaw := by
    unfold sampleLaw Probability.finiteIIDSampleLaw
    infer_instance
  have hhalfPositive : 0 < delta / 2 := by linarith
  have hhalfOne : delta / 2 < 1 := by linarith
  have hreciprocal : 1 / (delta / 2) = 2 / delta := by
    field_simp [hdeltaPositive.ne']
  have hupperRaw :=
    measureReal_two_expectedOneSidedRademacherSet_add_sqrt_two_log_div_le_upperUniformDeviationSet_le_of_abs_le_one
      law sampleCount hsampleCount value hmeasurable hvalue (delta / 2)
      hhalfPositive hhalfOne
  have hupper : sampleLaw.real upperBad ≤ delta / 2 := by
    change sampleLaw.real {sample |
      2 * expectedOneSidedRademacherSet law sampleCount value +
        Real.sqrt (2 * Real.log (2 / delta) / (sampleCount : ℝ)) ≤
        upperUniformDeviationSet law sampleCount value sample} ≤ delta / 2
    simpa only [sampleLaw, hreciprocal] using hupperRaw
  have hlowerRaw :=
    measureReal_integral_sub_empiricalOneSidedRademacherSet_ge_sqrt_two_log_div_le_of_abs_le_one
      law sampleCount hsampleCount value hmeasurable hvalue (delta / 2)
      hhalfPositive hhalfOne
  have hlower : sampleLaw.real complexityBad ≤ delta / 2 := by
    change sampleLaw.real {sample |
      Real.sqrt (2 * Real.log (2 / delta) / (sampleCount : ℝ)) ≤
        expectedOneSidedRademacherSet law sampleCount value - empiricalComplexity sample} ≤
      delta / 2
    simpa only [sampleLaw, empiricalComplexity, expectedOneSidedRademacherSet,
      hreciprocal] using hlowerRaw
  have hinclusion : sourceBad ⊆ upperBad ∪ complexityBad := by
    intro sample hsource
    by_cases hcomplexity : sample ∈ complexityBad
    · exact Set.mem_union_right _ hcomplexity
    · apply Set.mem_union_left
      change 2 * statisticalComplexity + radius ≤
        upperUniformDeviationSet law sampleCount value sample
      change 2 * empiricalComplexity sample + 3 * radius ≤
        upperUniformDeviationSet law sampleCount value sample at hsource
      have hstrict : statisticalComplexity - empiricalComplexity sample < radius := by
        exact lt_of_not_ge hcomplexity
      linarith
  change sampleLaw.real sourceBad ≤ delta
  calc
    sampleLaw.real sourceBad ≤ sampleLaw.real (upperBad ∪ complexityBad) :=
      measureReal_mono hinclusion (measure_ne_top _ _)
    _ ≤ sampleLaw.real upperBad + sampleLaw.real complexityBad :=
      measureReal_union_le _ _
    _ ≤ delta / 2 + delta / 2 := add_le_add hupper hlower
    _ = delta := by ring

/-- The expected empirical Rademacher complexity of a bounded product class
is at most twice the sum of the factor complexities, provided the three
fixed-sample complexity functionals are integrable.  The countable theorem
below derives these analytic premises from ordinary score measurability. -/
theorem expectedOneSidedRademacherSet_mul_le_two_add
    {Outcome Left Right : Type*} [MeasurableSpace Outcome]
    [Nonempty Left] [Nonempty Right]
    (law : Measure Outcome) (sampleCount : ℕ)
    (left : Left → Outcome → ℝ) (right : Right → Outcome → ℝ)
    (hleft : ∀ hypothesis outcome, |left hypothesis outcome| ≤ 1)
    (hright : ∀ hypothesis outcome, |right hypothesis outcome| ≤ 1)
    (hleftIntegrable : Integrable (fun sample : Fin sampleCount → Outcome =>
      FiniteRademacher.empiricalOneSidedRademacherSet sampleCount
        (fun hypothesis index => left hypothesis (sample index)))
      (Probability.finiteIIDSampleLaw law sampleCount))
    (hrightIntegrable : Integrable (fun sample : Fin sampleCount → Outcome =>
      FiniteRademacher.empiricalOneSidedRademacherSet sampleCount
        (fun hypothesis index => right hypothesis (sample index)))
      (Probability.finiteIIDSampleLaw law sampleCount))
    (hproductIntegrable : Integrable (fun sample : Fin sampleCount → Outcome =>
      FiniteRademacher.empiricalOneSidedRademacherSet sampleCount
        (fun pair : Left × Right => fun index =>
          left pair.1 (sample index) * right pair.2 (sample index)))
      (Probability.finiteIIDSampleLaw law sampleCount)) :
    expectedOneSidedRademacherSet law sampleCount
        (fun pair : Left × Right => fun outcome => left pair.1 outcome * right pair.2 outcome) ≤
      2 * (expectedOneSidedRademacherSet law sampleCount left +
        expectedOneSidedRademacherSet law sampleCount right) := by
  unfold expectedOneSidedRademacherSet
  calc
    (∫ sample,
        FiniteRademacher.empiricalOneSidedRademacherSet sampleCount
          (fun pair : Left × Right => fun index =>
            left pair.1 (sample index) * right pair.2 (sample index)) ∂
          Probability.finiteIIDSampleLaw law sampleCount) ≤
      (∫ sample, 2 *
        (FiniteRademacher.empiricalOneSidedRademacherSet sampleCount
          (fun hypothesis index => left hypothesis (sample index)) +
        FiniteRademacher.empiricalOneSidedRademacherSet sampleCount
          (fun hypothesis index => right hypothesis (sample index))) ∂
          Probability.finiteIIDSampleLaw law sampleCount) := by
      apply integral_mono_ae hproductIntegrable
        ((hleftIntegrable.add hrightIntegrable).const_mul 2)
      filter_upwards with sample
      exact FiniteRademacher.empiricalOneSidedRademacherSet_mul_le_two_add sampleCount
        (fun hypothesis index => left hypothesis (sample index))
        (fun hypothesis index => right hypothesis (sample index))
        (fun hypothesis index => hleft hypothesis (sample index))
        (fun hypothesis index => hright hypothesis (sample index))
    _ = 2 * ((∫ sample,
          FiniteRademacher.empiricalOneSidedRademacherSet sampleCount
            (fun hypothesis index => left hypothesis (sample index)) ∂
          Probability.finiteIIDSampleLaw law sampleCount) +
        (∫ sample,
          FiniteRademacher.empiricalOneSidedRademacherSet sampleCount
            (fun hypothesis index => right hypothesis (sample index)) ∂
          Probability.finiteIIDSampleLaw law sampleCount)) := by
      rw [integral_const_mul, integral_add hleftIntegrable hrightIntegrable]

/-- The product-complexity inequality has no finite-cardinality factor for
countable measurable bounded factor classes. -/
theorem expectedOneSidedRademacherSet_mul_le_two_add_of_countable
    {Outcome Left Right : Type*} [MeasurableSpace Outcome]
    [Countable Left] [Countable Right] [Nonempty Left] [Nonempty Right]
    (law : Measure Outcome) [IsProbabilityMeasure law] (sampleCount : ℕ)
    (left : Left → Outcome → ℝ) (right : Right → Outcome → ℝ)
    (hleftMeasurable : ∀ hypothesis, Measurable (left hypothesis))
    (hrightMeasurable : ∀ hypothesis, Measurable (right hypothesis))
    (hleft : ∀ hypothesis outcome, |left hypothesis outcome| ≤ 1)
    (hright : ∀ hypothesis outcome, |right hypothesis outcome| ≤ 1) :
    expectedOneSidedRademacherSet law sampleCount
        (fun pair : Left × Right => fun outcome => left pair.1 outcome * right pair.2 outcome) ≤
      2 * (expectedOneSidedRademacherSet law sampleCount left +
        expectedOneSidedRademacherSet law sampleCount right) := by
  apply expectedOneSidedRademacherSet_mul_le_two_add law sampleCount left right hleft hright
  · exact integrable_empiricalOneSidedRademacherSet_comp law sampleCount left
      hleftMeasurable hleft
  · exact integrable_empiricalOneSidedRademacherSet_comp law sampleCount right
      hrightMeasurable hright
  · apply integrable_empiricalOneSidedRademacherSet_comp law sampleCount
      (fun pair : Left × Right => fun outcome => left pair.1 outcome * right pair.2 outcome)
    · rintro ⟨leftHypothesis, rightHypothesis⟩
      exact (hleftMeasurable leftHypothesis).mul (hrightMeasurable rightHypothesis)
    · rintro ⟨leftHypothesis, rightHypothesis⟩ outcome
      rw [abs_mul]
      exact mul_le_one₀ (hleft leftHypothesis outcome) (abs_nonneg _)
        (hright rightHypothesis outcome)

/-- A finite family of measurable `[0,1]` scores has a simultaneous
population--empirical Hoeffding bound under every iid probability law.

This is intentionally a finite-family bridge.  An arbitrary-class extension
requires an explicit measurable-supremum convention (for example a countable
or separable parameterization), rather than merely an arbitrary `Set` of
functions. -/
theorem measureReal_finiteIID_exists_abs_populationMean_sub_empiricalMean_gt_le
    {Outcome Hypothesis : Type*} [MeasurableSpace Outcome] [Fintype Hypothesis]
    (law : Measure Outcome) [IsProbabilityMeasure law]
    (sampleCount : ℕ) (hsampleCount : 0 < sampleCount)
    (value : Hypothesis → Outcome → ℝ)
    (hmeasurable : ∀ hypothesis, Measurable (value hypothesis))
    (hbounded : ∀ hypothesis outcome,
      value hypothesis outcome ∈ Set.Icc (0 : ℝ) 1)
    (error : ℝ) (herror : 0 ≤ error) :
    (Probability.finiteIIDSampleLaw law sampleCount).real {sample |
      ∃ hypothesis,
        error < |populationMean law value hypothesis -
          empiricalMean sampleCount value sample hypothesis|} ≤
      (Fintype.card Hypothesis : ℝ) * 2 *
        Real.exp (-2 * (sampleCount : ℝ) * error ^ 2) := by
  letI : Nonempty (Fin sampleCount) := ⟨⟨0, hsampleCount⟩⟩
  letI : IsProbabilityMeasure (Probability.finiteIIDSampleLaw law sampleCount) := by
    unfold Probability.finiteIIDSampleLaw
    infer_instance
  let observation : Hypothesis → Fin sampleCount →
      (Fin sampleCount → Outcome) → ℝ :=
    fun hypothesis index sample => value hypothesis (sample index)
  have hindependent : ∀ hypothesis, iIndepFun (observation hypothesis)
      (Probability.finiteIIDSampleLaw law sampleCount) := by
    intro hypothesis
    simpa only [observation, Probability.finiteIIDSampleCoordinate,
      Function.comp_apply] using
      (Probability.iIndepFun_finiteIIDSampleCoordinate law sampleCount).comp
        (fun _ outcome => value hypothesis outcome)
        (fun _ => hmeasurable hypothesis)
  have hsameMean : ∀ hypothesis index,
      (Probability.finiteIIDSampleLaw law sampleCount)[observation hypothesis index] =
        populationMean law value hypothesis := by
    intro hypothesis index
    exact finiteIID_coordinate_mean_eq_populationMean law sampleCount value
      hmeasurable hypothesis index
  have hmeasurableObservation : ∀ hypothesis index,
      Measurable (observation hypothesis index) := by
    intro hypothesis index
    exact (hmeasurable hypothesis).comp (measurable_pi_apply index)
  have hboundedObservation : ∀ hypothesis index,
      ∀ᵐ sample ∂Probability.finiteIIDSampleLaw law sampleCount,
        observation hypothesis index sample ∈ Set.Icc (0 : ℝ) 1 := by
    intro hypothesis index
    filter_upwards with sample
    exact hbounded hypothesis (sample index)
  have hempirical : ∀ (sample : Fin sampleCount → Outcome) hypothesis,
      Probability.finiteEmpiricalMean observation hypothesis sample =
        empiricalMean sampleCount value sample hypothesis := by
    intro sample hypothesis
    simpa only [observation] using
      (empiricalMean_eq_probability_finiteEmpiricalMean hsampleCount value sample hypothesis).symm
  have htail := Probability.finite_uniform_finiteEmpiricalMean_abs_gt
    (Probability.finiteIIDSampleLaw law sampleCount) observation hindependent
    (populationMean law value) hsameMean hmeasurableObservation hboundedObservation
    error herror
  have hevent : {sample : Fin sampleCount → Outcome | ∃ hypothesis,
      error < |populationMean law value hypothesis -
        empiricalMean sampleCount value sample hypothesis|} =
      {sample | ∃ hypothesis,
        error < |Probability.finiteEmpiricalMean observation hypothesis sample -
          populationMean law value hypothesis|} := by
    ext sample
    constructor
    · rintro ⟨hypothesis, hsample⟩
      refine ⟨hypothesis, ?_⟩
      rw [hempirical sample hypothesis, abs_sub_comm]
      exact hsample
    · rintro ⟨hypothesis, hsample⟩
      refine ⟨hypothesis, ?_⟩
      rw [← hempirical sample hypothesis, abs_sub_comm]
      exact hsample
  rw [hevent]
  rw [show (Fintype.card (Fin sampleCount) : ℝ) = sampleCount by simp] at htail
  rw [Probability.boundedHoeffdingExponent_eq_neg_two_mul sampleCount
    hsampleCount error] at htail
  exact htail

end MeasureRademacher
end Statistics
end AppliedModelingLib

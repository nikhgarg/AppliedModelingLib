import AppliedModelingLib.Foundations.Probability.FiniteIID
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
Rademacher complexity needed at that boundary.  It proves the fixed-sample
measurability, boundedness, integrability, and bounded-product algebra for a
countable class.  The generic finite-iid measure-product and one-coordinate
Hoeffding infrastructure lives in `MeasureBoundedDifferences`; the general
symmetrization and McDiarmid concentration theorem itself remains to be proved.
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

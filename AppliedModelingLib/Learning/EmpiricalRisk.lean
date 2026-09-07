import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic
import AppliedModelingLib.Foundations.Math.FiniteAverage
import AppliedModelingLib.Foundations.Optimization.Certificate
import AppliedModelingLib.Foundations.Probability.FiniteExpectation
import AppliedModelingLib.Foundations.Probability.FiniteIidEmpiricalFrequency
import AppliedModelingLib.Foundations.Probability.EmpiricalMeasure

/-!
# Finite Empirical-Risk Minimization

Small deterministic transfer lemmas for finite model selection.  Probability
arguments establish a uniform empirical-to-population deviation separately;
these lemmas then turn empirical minimization into a population-risk bound.
-/

namespace AppliedModelingLib

/-- The arithmetic average of a statistic evaluated on a finite sample,
totalized as zero for an empty sample. -/
noncomputable def finiteSampleStatisticMean {Sample Value : Type*}
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {count : ℕ} (sample : Fin count → Sample) (statistic : Sample → Value) : Value :=
  finiteAverage (statistic ∘ sample)

@[simp] theorem finiteSampleStatisticMean_eq_finiteAverage
    {Sample Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {count : ℕ} (sample : Fin count → Sample) (statistic : Sample → Value) :
    finiteSampleStatisticMean sample statistic =
      finiteAverage (statistic ∘ sample) := rfl

/-- For a real-valued statistic, the sample-statistic mean is its evaluated
finite sum divided by the sample count. -/
theorem finiteSampleStatisticMean_real_eq_div
    {Sample : Type*} {count : ℕ} (sample : Fin count → Sample)
    (statistic : Sample → ℝ) :
    finiteSampleStatisticMean sample statistic =
      (∑ index, statistic (sample index)) / (count : ℝ) := by
  rw [finiteSampleStatisticMean_eq_finiteAverage, finiteAverage_real_eq_div_card]
  simp only [Function.comp_apply, Fintype.card_fin]

/-- The empirical PMF atom mass is its literal sample frequency. -/
theorem empiricalSampleLaw_apply_toReal_eq_empiricalCount_div
    {Sample : Type*} [Fintype Sample] [DecidableEq Sample] {count : ℕ}
    [Nonempty (Fin count)] (sample : Fin count → Sample) (datum : Sample) :
    (empiricalSampleLaw sample datum).toReal =
      (Probability.empiricalCount sample datum : ℝ) / (count : ℝ) := by
  classical
  have hcount_pos : 0 < count := Fin.pos_iff_nonempty.mpr inferInstance
  unfold empiricalSampleLaw
  rw [PMF.map_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin]
  rw [ENNReal.toReal_sum]
  · have hsum :
        (∑ index : Fin count, if datum = sample index then (1 : ℝ) else 0) =
          (Probability.empiricalCount sample datum : ℝ) := by
          simp [Probability.empiricalCount, successIndexSet, eq_comm]
    calc
      ∑ index : Fin count,
          (if datum = sample index then (count : ENNReal)⁻¹ else 0).toReal =
          ∑ index : Fin count, if datum = sample index then (count : ℝ)⁻¹ else 0 := by
            apply Finset.sum_congr rfl
            intro index _
            split_ifs
            · rw [ENNReal.toReal_inv]
              norm_cast
            · rfl
      _ = (count : ℝ)⁻¹ *
          ∑ index : Fin count, if datum = sample index then (1 : ℝ) else 0 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro index _
            split_ifs <;> ring
      _ = (Probability.empiricalCount sample datum : ℝ) / (count : ℝ) := by
            rw [hsum]
            field_simp
  · intro index _
    split_ifs
    · exact ENNReal.inv_ne_top.mpr (by exact_mod_cast Nat.ne_of_gt hcount_pos)
    · exact ENNReal.zero_ne_top

/-- A scalar sample mean is expectation under its empirical PMF. -/
theorem pmfExp_empiricalSampleLaw_eq_finiteSampleMean
    {Sample : Type*} [Fintype Sample] [DecidableEq Sample] {count : ℕ}
    [Nonempty (Fin count)] (sample : Fin count → Sample) (statistic : Sample → ℝ) :
    pmfExp (empiricalSampleLaw sample) statistic = finiteSampleStatisticMean sample statistic := by
  classical
  have hcount_pos : 0 < count := Fin.pos_iff_nonempty.mpr inferInstance
  have hcount : count ≠ 0 := Nat.ne_of_gt hcount_pos
  simp only [pmfExp, empiricalSampleLaw, finiteSampleStatisticMean, finiteAverage,
    PMF.map_apply, tsum_fintype]
  have hsum (x : Sample) :
      (∑ a : Fin count, if x = sample a then (count : ENNReal)⁻¹ else 0).toReal =
        ∑ a : Fin count, if x = sample a then (count : ℝ)⁻¹ else 0 := by
    rw [ENNReal.toReal_sum]
    · apply Finset.sum_congr rfl
      intro a ha
      split_ifs
      · rw [ENNReal.toReal_inv]
        norm_cast
      · rfl
    · intro a ha
      split_ifs
      · rw [ENNReal.inv_ne_top]
        exact_mod_cast hcount
      · exact ENNReal.zero_ne_top
  simp_rw [PMF.uniformOfFintype_apply, Fintype.card_fin, hsum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [smul_eq_mul]
  rw [Finset.mul_sum]

/-- A vector sample mean is vector expectation under its empirical PMF. -/
theorem pmfVectorExp_empiricalSampleLaw_eq_finiteSampleMean
    {Sample Value : Type*} [Fintype Sample] [DecidableEq Sample]
    [NormedAddCommGroup Value] [NormedSpace ℝ Value] {count : ℕ}
    [Nonempty (Fin count)] (sample : Fin count → Sample) (statistic : Sample → Value) :
    pmfVectorExp (empiricalSampleLaw sample) statistic = finiteSampleStatisticMean sample statistic := by
  classical
  have hcount_pos : 0 < count := Fin.pos_iff_nonempty.mpr inferInstance
  have hcount : count ≠ 0 := Nat.ne_of_gt hcount_pos
  simp only [pmfVectorExp, empiricalSampleLaw, finiteSampleStatisticMean, finiteAverage,
    PMF.map_apply, tsum_fintype]
  have hsum (x : Sample) :
      (∑ a : Fin count, if x = sample a then (count : ENNReal)⁻¹ else 0).toReal =
        ∑ a : Fin count, if x = sample a then (count : ℝ)⁻¹ else 0 := by
    rw [ENNReal.toReal_sum]
    · apply Finset.sum_congr rfl
      intro a ha
      split_ifs
      · rw [ENNReal.toReal_inv]
        norm_cast
      · rfl
    · intro a ha
      split_ifs
      · rw [ENNReal.inv_ne_top]
        exact_mod_cast hcount
      · exact ENNReal.zero_ne_top
  simp_rw [PMF.uniformOfFintype_apply, Fintype.card_fin, hsum, Finset.sum_smul]
  rw [Finset.sum_comm]
  simp
  rw [Finset.smul_sum]

/-- A selected parameter minimizes empirical risk over a finite candidate set. -/
def IsEmpiricalRiskMinimizer {Parameter : Type*} [DecidableEq Parameter]
    (empiricalRisk : Parameter → ℝ) (candidates : Finset Parameter)
    (selected : Parameter) : Prop :=
  Optimization.IsMinimizerOn (fun candidate => candidate ∈ candidates)
    empiricalRisk selected

/--
Uniform deviation plus empirical-risk minimization bounds the selected
population risk relative to every candidate.
-/
theorem populationRisk_le_of_empiricalRiskMinimizer_and_uniformDeviation
    {Parameter : Type*} [DecidableEq Parameter]
    (populationRisk empiricalRisk : Parameter → ℝ) (candidates : Finset Parameter)
    (selected : Parameter) (deviation : ℝ)
    (hminimizer : IsEmpiricalRiskMinimizer empiricalRisk candidates selected)
    (hdeviation : ∀ candidate ∈ candidates,
      |empiricalRisk candidate - populationRisk candidate| ≤ deviation)
    (candidate : Parameter) (hcandidate : candidate ∈ candidates) :
    populationRisk selected ≤ populationRisk candidate + 2 * deviation := by
  have hselectedDeviation := hdeviation selected hminimizer.1
  have hcandidateDeviation := hdeviation candidate hcandidate
  have hminimizes := hminimizer.2 candidate hcandidate
  have hselectedLower := (abs_le.mp hselectedDeviation).1
  have hcandidateUpper := (abs_le.mp hcandidateDeviation).2
  linarith

end AppliedModelingLib

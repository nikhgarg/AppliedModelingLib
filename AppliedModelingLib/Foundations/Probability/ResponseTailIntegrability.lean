import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Integrating elementary response-tail bounds

These lemmas provide the two analytic pieces used to turn a deterministic-time
tail split into a finite first moment: an integrable nonnegative initial term
and an exponentially decaying remainder.
-/

namespace AppliedModelingLib.Probability

open MeasureTheory Filter
open scoped ENNReal BigOperators

noncomputable section

/-- The tail measures of a nonnegative integrable random variable remain
integrable after a positive linear rescaling of the threshold. -/
theorem lintegral_measure_setOf_le_mul_lt_top
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (initial : Ω → ℝ)
    (hintegrable : Integrable initial μ)
    (hnonnegative : 0 ≤ᵐ[μ] initial) {scale : ℝ} (hscale : 0 < scale) :
    (∫⁻ t in Set.Ioi (0 : ℝ), μ {ω | scale * t ≤ initial ω}) < ∞ := by
  have hscaled : Integrable (fun ω => initial ω / scale) μ :=
    hintegrable.div_const scale
  have hscaled_nonnegative : 0 ≤ᵐ[μ] fun ω => initial ω / scale := by
    filter_upwards [hnonnegative] with ω hω
    exact div_nonneg hω hscale.le
  have hset : ∀ t : ℝ, {ω | scale * t ≤ initial ω} =
      {ω | t ≤ initial ω / scale} := by
    intro t
    ext ω
    constructor
    · intro h
      apply (le_div_iff₀ hscale).2
      simpa [mul_comm] using h
    · intro h
      have h' := (le_div_iff₀ hscale).1 h
      simpa [mul_comm] using h'
  calc
    (∫⁻ t in Set.Ioi (0 : ℝ), μ {ω | scale * t ≤ initial ω}) =
        ∫⁻ t in Set.Ioi (0 : ℝ), μ {ω | t ≤ initial ω / scale} := by
          apply lintegral_congr
          intro t
          rw [hset]
    _ = ∫⁻ ω, ENNReal.ofReal (initial ω / scale) ∂μ := by
          exact (lintegral_eq_lintegral_meas_le μ hscaled_nonnegative
            hscaled.aemeasurable).symm
    _ < ∞ := (hasFiniteIntegral_iff_ofReal hscaled_nonnegative).mp
      hscaled.hasFiniteIntegral

/-- A strictly exponentially decaying real function has finite nonnegative
Lebesgue integral over the positive half-line. -/
theorem lintegral_ofReal_exp_mul_Ioi_lt_top {rate : ℝ} (hrate : rate < 0) :
    (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (rate * t))) < ∞ := by
  have hintegrable : IntegrableOn (fun t : ℝ => Real.exp (rate * t))
      (Set.Ioi 0) := integrableOn_exp_mul_Ioi hrate 0
  have hfinite := hintegrable.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_norm] at hfinite
  simpa [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le] using hfinite

/-- A finite sum of strictly exponentially decaying nonnegative functions has
finite Lebesgue integral over the positive half-line. -/
theorem lintegral_finset_sum_ofReal_exp_mul_Ioi_lt_top
    {ι : Type*} [Fintype ι] (rate : ι → ℝ) (hrate : ∀ i, rate i < 0) :
    (∫⁻ t in Set.Ioi (0 : ℝ), ∑ i, ENNReal.ofReal (Real.exp (rate i * t))) < ∞ := by
  calc
    (∫⁻ t in Set.Ioi (0 : ℝ), ∑ i, ENNReal.ofReal (Real.exp (rate i * t))) =
        ∑ i, ∫⁻ t in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (Real.exp (rate i * t)) := by
            simpa using MeasureTheory.lintegral_finset_sum' (μ :=
              volume.restrict (Set.Ioi (0 : ℝ))) Finset.univ
              (fun i _ =>
                (ENNReal.measurable_ofReal.comp
                  ((measurable_const.mul measurable_id).exp)).aemeasurable)
    _ < ∞ := ENNReal.sum_lt_top.mpr fun i _ =>
      lintegral_ofReal_exp_mul_Ioi_lt_top (hrate i)

/-- A nonnegative response has a finite first moment when its strict tail is
bounded by a positively rescaled integrable initial term plus finitely many
strictly exponentially decaying terms. -/
theorem integrable_of_ae_nonnegative_of_exponential_tail_split
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (response initial : Ω → ℝ)
    (hresponse_measurable : AEMeasurable response μ)
    (hresponse_nonnegative : 0 ≤ᵐ[μ] response)
    (hinitial_integrable : Integrable initial μ)
    (hinitial_nonnegative : 0 ≤ᵐ[μ] initial)
    {initialScale : ℝ} (hinitialScale : 0 < initialScale)
    (exponentialRate : ι → ℝ) (hexponentialRate : ∀ i, exponentialRate i < 0)
    (htail : ∀ t : ℝ, 0 < t →
      μ {ω | t < response ω} ≤ μ {ω | initialScale * t ≤ initial ω} +
        ∑ i, ENNReal.ofReal (Real.exp (exponentialRate i * t))) :
    Integrable response μ := by
  have hinitialTail_measurable : Measurable (fun t : ℝ =>
      μ {ω | initialScale * t ≤ initial ω}) := by
    apply Antitone.measurable
    intro lower upper hlowerUpper
    apply measure_mono
    intro ω hω
    have : initialScale * lower ≤ initialScale * upper :=
      mul_le_mul_of_nonneg_left hlowerUpper hinitialScale.le
    exact this.trans hω
  have htail_ae : (fun t : ℝ => μ {ω | t < response ω}) ≤ᵐ[
      volume.restrict (Set.Ioi (0 : ℝ))]
      fun t => μ {ω | initialScale * t ≤ initial ω} +
        ∑ i, ENNReal.ofReal (Real.exp (exponentialRate i * t)) := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)))]
      with t ht
    exact htail t ht
  refine ⟨hresponse_measurable.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal hresponse_nonnegative]
  rw [lintegral_eq_lintegral_meas_lt μ hresponse_nonnegative hresponse_measurable]
  refine lt_of_le_of_lt (lintegral_mono_ae htail_ae) ?_
  rw [lintegral_add_left (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    hinitialTail_measurable]
  exact ENNReal.add_lt_top.mpr ⟨
    lintegral_measure_setOf_le_mul_lt_top μ initial hinitial_integrable
      hinitial_nonnegative hinitialScale,
    lintegral_finset_sum_ofReal_exp_mul_Ioi_lt_top exponentialRate
      hexponentialRate⟩

end

end AppliedModelingLib.Probability

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Group.Prod

/-!
# Exponential split of a Poisson suspension gap

This module proves the local measure identity behind the equilibrium Poisson
construction: under the normalized Palm suspension law, splitting the gap
that straddles a deterministic origin into its forward residual and backward
age gives two independent exponential variables.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

/-- The physical suspension triangle for one exponential gap and its phase. -/
def exponentialSplitCarrier : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.2 ∧ p.2 < p.1}

theorem measurableSet_exponentialSplitCarrier :
    MeasurableSet exponentialSplitCarrier := by
  exact (measurableSet_le measurable_const measurable_snd).inter
    (measurableSet_lt measurable_snd measurable_fst)

/-- The forward shear sends residual/age coordinates to gap/phase coordinates. -/
def exponentialSplitShear : (ℝ × ℝ) → ℝ × ℝ :=
  fun p => (p.1 + p.2, p.2)

/-- The inverse shear turns a gap/phase pair into residual/age coordinates. -/
def exponentialSplitUnshear : (ℝ × ℝ) → ℝ × ℝ :=
  fun p => (p.1 - p.2, p.2)

theorem measurable_exponentialSplitShear : Measurable exponentialSplitShear := by
  exact measurable_fst.add measurable_snd |>.prodMk measurable_snd

theorem measurable_exponentialSplitUnshear : Measurable exponentialSplitUnshear := by
  exact measurable_fst.sub measurable_snd |>.prodMk measurable_snd

theorem exponentialSplitUnshear_comp_shear :
    exponentialSplitUnshear ∘ exponentialSplitShear = id := by
  funext p
  rcases p with ⟨r, a⟩
  simp [exponentialSplitUnshear, exponentialSplitShear]

theorem exponentialSplitShear_measurePreserving :
    MeasurePreserving exponentialSplitShear (volume.prod volume) (volume.prod volume) := by
  simpa [exponentialSplitShear] using
    (measurePreserving_add_prod (volume : Measure ℝ) (volume : Measure ℝ))

/-- Density of an independent pair of rate-`rate` exponential variables. -/
def exponentialPairDensity (rate : ℝ) : (ℝ × ℝ) → ℝ≥0∞ :=
  fun p => exponentialPDF rate p.1 * exponentialPDF rate p.2

/-- Density of a rate-normalized exponential gap/phase suspension sample. -/
def exponentialSplitDensity (rate : ℝ) : (ℝ × ℝ) → ℝ≥0∞ :=
  fun p => ENNReal.ofReal rate *
    (exponentialSplitCarrier.indicator fun q => exponentialPDF rate q.1) p

theorem measurable_exponentialPDF (rate : ℝ) :
    Measurable (exponentialPDF rate) :=
  (measurable_exponentialPDFReal rate).ennreal_ofReal

theorem measurable_exponentialPairDensity (rate : ℝ) :
    Measurable (exponentialPairDensity rate) := by
  exact ((measurable_exponentialPDF rate).comp measurable_fst).mul
    ((measurable_exponentialPDF rate).comp measurable_snd)

theorem measurable_exponentialSplitDensity (rate : ℝ) :
    Measurable (exponentialSplitDensity rate) := by
  exact measurable_const.mul
    (((measurable_exponentialPDF rate).comp measurable_fst).indicator
      measurableSet_exponentialSplitCarrier)

/-- The product law of independent exponentials has the advertised density
relative to two-dimensional Lebesgue measure. -/
theorem expMeasure_prod_eq_withDensity_pair (rate : ℝ) :
    (expMeasure rate).prod (expMeasure rate) =
      (volume.prod volume).withDensity (exponentialPairDensity rate) := by
  rw [show expMeasure rate = volume.withDensity (exponentialPDF rate) by rfl,
    MeasureTheory.prod_withDensity (measurable_exponentialPDF rate)
      (measurable_exponentialPDF rate)]
  rfl

/-- The unnormalized rate-weighted exponential gap/phase suspension law has
the split density relative to two-dimensional Lebesgue measure. -/
theorem rate_smul_expMeasure_prod_volume_restrict_eq_withDensity_split
    (rate : ℝ) :
    ENNReal.ofReal rate • ((expMeasure rate).prod volume).restrict
        exponentialSplitCarrier =
      (volume.prod volume).withDensity (exponentialSplitDensity rate) := by
  rw [show expMeasure rate = volume.withDensity (exponentialPDF rate) by rfl,
    MeasureTheory.prod_withDensity_left (measurable_exponentialPDF rate),
    MeasureTheory.restrict_withDensity measurableSet_exponentialSplitCarrier,
    ← MeasureTheory.withDensity_indicator measurableSet_exponentialSplitCarrier]
  have hmeas : Measurable
      (exponentialSplitCarrier.indicator fun z : ℝ × ℝ => exponentialPDF rate z.1) :=
    ((measurable_exponentialPDF rate).comp measurable_fst).indicator
      measurableSet_exponentialSplitCarrier
  calc
    ENNReal.ofReal rate •
        (volume.prod volume).withDensity
          (exponentialSplitCarrier.indicator fun z : ℝ × ℝ => exponentialPDF rate z.1) =
        (volume.prod volume).withDensity
          (ENNReal.ofReal rate •
            exponentialSplitCarrier.indicator fun z : ℝ × ℝ => exponentialPDF rate z.1) :=
      (MeasureTheory.withDensity_smul (ENNReal.ofReal rate) hmeas).symm
    _ = (volume.prod volume).withDensity (exponentialSplitDensity rate) := by rfl

/-- Away from the null boundary `residual = 0`, the independent exponential
density is the pullback of the normalized gap/phase density under the shear. -/
theorem exponentialPairDensity_eq_splitDensity_shear_of_ne_first
    {rate : ℝ} (hrate : 0 < rate) (p : ℝ × ℝ) (hp : p.1 ≠ 0) :
    exponentialPairDensity rate p =
      exponentialSplitDensity rate (exponentialSplitShear p) := by
  rcases p with ⟨r, a⟩
  change r ≠ 0 at hp
  simp only [exponentialPairDensity, exponentialSplitDensity,
    exponentialSplitShear]
  by_cases hr : 0 < r
  · by_cases ha : 0 ≤ a
    · have hcarrier : (r + a, a) ∈ exponentialSplitCarrier := by
        change 0 ≤ a ∧ a < r + a
        exact ⟨ha, by linarith⟩
      rw [Set.indicator_of_mem hcarrier]
      rw [exponentialPDF_of_nonneg hr.le, exponentialPDF_of_nonneg ha,
        exponentialPDF_of_nonneg (by linarith : 0 ≤ r + a)]
      rw [← ENNReal.ofReal_mul
        (by positivity : 0 ≤ rate * Real.exp (-(rate * r)))]
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ rate)]
      congr 1
      rw [show -(rate * (r + a)) = -(rate * r) + -(rate * a) by ring,
        Real.exp_add]
      ring
    · have ha' : a < 0 := lt_of_not_ge ha
      have hnot : (r + a, a) ∉ exponentialSplitCarrier := by
        intro h
        exact ha h.1
      rw [Set.indicator_of_notMem hnot]
      rw [exponentialPDF_of_neg ha']
      simp
  · have hr' : r < 0 := lt_of_le_of_ne (le_of_not_gt hr) hp
    have hnot : (r + a, a) ∉ exponentialSplitCarrier := by
      intro h
      linarith [h.2]
    rw [Set.indicator_of_notMem hnot]
    rw [exponentialPDF_of_neg hr']
    simp

/-- The only boundary at which the densities can differ is a vertical
Lebesgue-null line. -/
theorem ae_fst_ne_zero_volume_prod :
    ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume), p.1 ≠ 0 := by
  refine MeasureTheory.ae_of_ae_map (μ := volume.prod volume) (f := Prod.fst)
    (p := fun x : ℝ => x ≠ 0) measurable_fst.aemeasurable ?_
  rw [Measure.map_fst_prod, MeasureTheory.ae_iff]
  have hset : {x : ℝ | ¬ x ≠ 0} = {0} := by
    ext x
    simp
  rw [hset, Measure.smul_apply, Real.volume_singleton]
  simp

theorem ae_exponentialPairDensity_eq_splitDensity_shear
    {rate : ℝ} (hrate : 0 < rate) :
    exponentialPairDensity rate =ᵐ[volume.prod volume]
      exponentialSplitDensity rate ∘ exponentialSplitShear := by
  filter_upwards [ae_fst_ne_zero_volume_prod] with p hp
  exact exponentialPairDensity_eq_splitDensity_shear_of_ne_first hrate p hp

/-- Transport a density along a measurable measure-preserving map. -/
theorem map_withDensity_comp_of_measurePreserving
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {f : α → β}
    (h : MeasurePreserving f μ ν) (g : β → ℝ≥0∞) (hg : Measurable g) :
    Measure.map f (μ.withDensity (g ∘ f)) = ν.withDensity g := by
  apply Measure.ext
  intro s hs
  calc
    Measure.map f (μ.withDensity (g ∘ f)) s =
        (μ.withDensity (g ∘ f)) (f ⁻¹' s) :=
      Measure.map_apply h.measurable hs
    _ = ∫⁻ x in f ⁻¹' s, (g ∘ f) x ∂μ :=
      withDensity_apply _ (h.measurable hs)
    _ = ∫⁻ x, (f ⁻¹' s).indicator (g ∘ f) x ∂μ :=
      (MeasureTheory.lintegral_indicator (h.measurable hs) (g ∘ f)).symm
    _ = ∫⁻ x, (s.indicator g) (f x) ∂μ := by
      congr 1
    _ = ∫⁻ y, s.indicator g y ∂ν := by
      rw [← h.map_eq]
      exact (MeasureTheory.lintegral_map (hg.indicator hs) h.measurable).symm
    _ = ∫⁻ y in s, g y ∂ν :=
      MeasureTheory.lintegral_indicator hs g
    _ = (ν.withDensity g) s := (withDensity_apply g hs).symm

/-- Independent residual and age exponentials shear to a rate-normalized
exponential gap/phase suspension sample. -/
theorem map_exponentialSplitShear_expMeasure_prod
    {rate : ℝ} (hrate : 0 < rate) :
    Measure.map exponentialSplitShear ((expMeasure rate).prod (expMeasure rate)) =
      ENNReal.ofReal rate • ((expMeasure rate).prod volume).restrict
        exponentialSplitCarrier := by
  calc
    Measure.map exponentialSplitShear ((expMeasure rate).prod (expMeasure rate)) =
        Measure.map exponentialSplitShear
          ((volume.prod volume).withDensity (exponentialPairDensity rate)) := by
            rw [expMeasure_prod_eq_withDensity_pair]
    _ = Measure.map exponentialSplitShear
          ((volume.prod volume).withDensity
            (exponentialSplitDensity rate ∘ exponentialSplitShear)) := by
            congr 1
            exact MeasureTheory.withDensity_congr_ae
              (ae_exponentialPairDensity_eq_splitDensity_shear hrate)
    _ = (volume.prod volume).withDensity (exponentialSplitDensity rate) :=
      map_withDensity_comp_of_measurePreserving exponentialSplitShear_measurePreserving
        (exponentialSplitDensity rate) (measurable_exponentialSplitDensity rate)
    _ = ENNReal.ofReal rate • ((expMeasure rate).prod volume).restrict
          exponentialSplitCarrier :=
      (rate_smul_expMeasure_prod_volume_restrict_eq_withDensity_split rate).symm

/-- A rate-weighted Palm gap and uniform-in-gap phase turn into independent
residual and age exponentials. This is the central-gap probability identity
needed to identify the stationary suspension with the origin-split law. -/
theorem map_exponentialSplitUnshear_rate_smul_expMeasure_prod_volume_restrict
    {rate : ℝ} (hrate : 0 < rate) :
    Measure.map exponentialSplitUnshear
        (ENNReal.ofReal rate • ((expMeasure rate).prod volume).restrict
          exponentialSplitCarrier) =
      (expMeasure rate).prod (expMeasure rate) := by
  calc
    Measure.map exponentialSplitUnshear
        (ENNReal.ofReal rate • ((expMeasure rate).prod volume).restrict
          exponentialSplitCarrier) =
        Measure.map exponentialSplitUnshear
          (Measure.map exponentialSplitShear
            ((expMeasure rate).prod (expMeasure rate))) := by
          rw [map_exponentialSplitShear_expMeasure_prod hrate]
    _ = Measure.map (exponentialSplitUnshear ∘ exponentialSplitShear)
          ((expMeasure rate).prod (expMeasure rate)) := by
          rw [Measure.map_map measurable_exponentialSplitUnshear
            measurable_exponentialSplitShear]
    _ = (expMeasure rate).prod (expMeasure rate) := by
          rw [exponentialSplitUnshear_comp_shear]
          exact Measure.map_id

end

end AppliedModelingLib.Probability.PoissonProcess

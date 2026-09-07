import AppliedModelingLib.Foundations.Probability.IidStatePrefixStopping

/-!
# IID rewards selected by an independent external event path

This module gives the Tonelli calculation for a sequence of IID rewards whose
`n`th term is selected by a measurable event of an independent external path.
The selector may depend on the whole external path; it therefore does not
claim a stopping-time or regeneration result.  This is the appropriate
building block when a separately constructed event chain determines which
independent holding-time coordinates are accrued.
-/

namespace AppliedModelingLib.Probability.IIDStream

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

variable {σ α : Type*} [MeasurableSpace σ] [MeasurableSpace α]

/-- Sum IID nonnegative rewards over the coordinates selected by a sequence
of events measurable on an independent external path. -/
noncomputable def externalWeightedENNReward
    (event : ℕ → Set σ) (reward : α → ℝ≥0∞) :
    σ × (ℕ → α) → ℝ≥0∞ :=
  fun z => ∑' n, (Prod.fst ⁻¹' event n).indicator
    (fun z => reward (coordinate n z.2)) z

/-- Each externally selected IID reward summand is measurable. -/
theorem measurable_externalWeightedENNRewardSummand
    (event : ℕ → Set σ) (reward : α → ℝ≥0∞)
    (hevent : ∀ n, MeasurableSet (event n)) (hreward : Measurable reward)
    (n : ℕ) :
    Measurable ((Prod.fst ⁻¹' event n).indicator
      (fun z : σ × (ℕ → α) => reward (coordinate n z.2))) := by
  let E : Set (σ × (ℕ → α)) := Prod.fst ⁻¹' event n
  have hE : MeasurableSet E := (hevent n).preimage measurable_fst
  let f : σ × (ℕ → α) → ℝ≥0∞ :=
    fun z => reward (coordinate n z.2)
  have hf : Measurable f :=
    hreward.comp ((measurable_coordinate (α := α) n).comp measurable_snd)
  simpa [E, f] using hf.indicator hE

/-- The selected reward at one coordinate factors into the external-event
probability and the mean IID reward. -/
theorem lintegral_externalWeightedENNRewardSummand
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (event : ℕ → Set σ) (reward : α → ℝ≥0∞)
    (hevent : ∀ n, MeasurableSet (event n)) (hreward : Measurable reward)
    (n : ℕ) :
    ∫⁻ z : σ × (ℕ → α),
        (Prod.fst ⁻¹' event n).indicator
          (fun z => reward (coordinate n z.2)) z
          ∂(ρ.prod (measure μ)) =
      ρ (event n) * ∫⁻ x, reward x ∂μ := by
  classical
  letI : IsProbabilityMeasure (measure μ) := by
    dsimp [measure]
    infer_instance
  let F : σ → ℝ≥0∞ := (event n).indicator (fun _ => (1 : ℝ≥0∞))
  have hF : Measurable F := measurable_const.indicator (hevent n)
  have hindep := indepFun_state_coordinate ρ μ n
  have hfactor := ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
    (hF.comp measurable_fst)
    (hreward.comp ((measurable_coordinate (α := α) n).comp measurable_snd))
    (hindep.comp hF hreward)
  have hleft :
      (fun z : σ × (ℕ → α) => F z.1 * reward (coordinate n z.2)) =
        (Prod.fst ⁻¹' event n).indicator
          (fun z => reward (coordinate n z.2)) := by
    funext z
    by_cases hz : z.1 ∈ event n <;> simp [F, hz]
  have hprefix :
      (∫⁻ z : σ × (ℕ → α), F z.1 ∂(ρ.prod (measure μ))) =
        ρ (event n) := by
    calc
      (∫⁻ z : σ × (ℕ → α), F z.1 ∂(ρ.prod (measure μ))) =
          ∫⁻ z : σ × (ℕ → α),
            (Prod.fst ⁻¹' event n).indicator (fun _ => (1 : ℝ≥0∞)) z
              ∂(ρ.prod (measure μ)) := by
            apply MeasureTheory.lintegral_congr
            intro z
            by_cases hz : z.1 ∈ event n <;> simp [F, hz]
      _ = (ρ.prod (measure μ)) (Prod.fst ⁻¹' event n) :=
        MeasureTheory.lintegral_indicator_one ((hevent n).preimage measurable_fst)
      _ = ρ (event n) := by
        rw [← Measure.map_apply measurable_fst (hevent n),
          Measure.map_fst_prod, measure_univ, one_smul]
  have hrewardIntegral :
      (∫⁻ z : σ × (ℕ → α), reward (coordinate n z.2)
        ∂(ρ.prod (measure μ))) = ∫⁻ x, reward x ∂μ := by
    exact ((coordinate_measurePreserving μ n).comp
      (measurePreserving_snd : MeasurePreserving Prod.snd
        (ρ.prod (measure μ)) (measure μ))).hasLaw.lintegral_comp hreward.aemeasurable
  calc
    ∫⁻ z : σ × (ℕ → α),
        (Prod.fst ⁻¹' event n).indicator
          (fun z => reward (coordinate n z.2)) z
          ∂(ρ.prod (measure μ)) =
        ∫⁻ z : σ × (ℕ → α), F z.1 * reward (coordinate n z.2)
          ∂(ρ.prod (measure μ)) := by rw [hleft]
    _ = (∫⁻ z : σ × (ℕ → α), F z.1 ∂(ρ.prod (measure μ))) *
          ∫⁻ z : σ × (ℕ → α), reward (coordinate n z.2)
            ∂(ρ.prod (measure μ)) := by
          simpa only [Function.comp_apply] using hfactor
    _ = ρ (event n) * ∫⁻ x, reward x ∂μ := by
          rw [hprefix, hrewardIntegral]

/-- Tonelli factors the expected total externally selected reward into the
summed external-event probabilities and the IID reward mean. -/
theorem lintegral_externalWeightedENNReward
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (event : ℕ → Set σ) (reward : α → ℝ≥0∞)
    (hevent : ∀ n, MeasurableSet (event n)) (hreward : Measurable reward) :
    ∫⁻ z, externalWeightedENNReward event reward z ∂(ρ.prod (measure μ)) =
      (∑' n, ρ (event n)) * ∫⁻ x, reward x ∂μ := by
  calc
    ∫⁻ z, externalWeightedENNReward event reward z ∂(ρ.prod (measure μ)) =
        ∫⁻ z, ∑' n,
          (Prod.fst ⁻¹' event n).indicator
            (fun z => reward (coordinate n z.2)) z
            ∂(ρ.prod (measure μ)) := by rfl
    _ = ∑' n, ∫⁻ z : σ × (ℕ → α),
          (Prod.fst ⁻¹' event n).indicator
            (fun z => reward (coordinate n z.2)) z
            ∂(ρ.prod (measure μ)) := by
          exact MeasureTheory.lintegral_tsum fun n =>
            (measurable_externalWeightedENNRewardSummand event reward hevent hreward n).aemeasurable
    _ = ∑' n, ρ (event n) * ∫⁻ x, reward x ∂μ := by
          apply tsum_congr
          intro n
          exact lintegral_externalWeightedENNRewardSummand
            ρ μ event reward hevent hreward n
    _ = (∑' n, ρ (event n)) * ∫⁻ x, reward x ∂μ := by
          rw [ENNReal.tsum_mul_right]

/-- A summable real probability tail and a finite mean IID reward make the
total externally selected reward finite in extended expectation. -/
theorem lintegral_externalWeightedENNReward_ne_top
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (event : ℕ → Set σ) (reward : α → ℝ≥0∞)
    (hevent : ∀ n, MeasurableSet (event n)) (hreward : Measurable reward)
    (hsummable : Summable fun n => ρ.real (event n))
    (hreward_finite : ∫⁻ x, reward x ∂μ ≠ ⊤) :
    ∫⁻ z, externalWeightedENNReward event reward z ∂(ρ.prod (measure μ)) ≠ ⊤ := by
  rw [lintegral_externalWeightedENNReward ρ μ event reward hevent hreward]
  apply ENNReal.mul_ne_top
  · have hterm : ∀ n, ENNReal.ofReal (ρ.real (event n)) = ρ (event n) := by
      intro n
      exact ENNReal.ofReal_toReal (measure_ne_top ρ (event n))
    rw [← tsum_congr hterm]
    exact hsummable.tsum_ofReal_ne_top
  · exact hreward_finite

/-- Under the finite-expectation hypotheses above, the selected total reward
is finite almost surely. -/
theorem ae_externalWeightedENNReward_lt_top
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (event : ℕ → Set σ) (reward : α → ℝ≥0∞)
    (hevent : ∀ n, MeasurableSet (event n)) (hreward : Measurable reward)
    (hsummable : Summable fun n => ρ.real (event n))
    (hreward_finite : ∫⁻ x, reward x ∂μ ≠ ⊤) :
    ∀ᵐ z ∂(ρ.prod (measure μ)), externalWeightedENNReward event reward z < ⊤ := by
  apply MeasureTheory.ae_lt_top
  · exact Measurable.ennreal_tsum fun n =>
      measurable_externalWeightedENNRewardSummand event reward hevent hreward n
  · exact lintegral_externalWeightedENNReward_ne_top
      ρ μ event reward hevent hreward hsummable hreward_finite

/-- Sum IID nonnegative rewards with nonnegative weights determined by an
independent external path.  Unlike `externalWeightedENNReward`, the weight
need not be an indicator, so this form also records workload or reward areas
accumulated along an externally generated trajectory. -/
noncomputable def externalScaledENNReward
    (weight : ℕ → σ → ℝ≥0∞) (reward : α → ℝ≥0∞) :
    σ × (ℕ → α) → ℝ≥0∞ :=
  fun z => ∑' n, weight n z.1 * reward (coordinate n z.2)

/-- Each externally weighted IID reward summand is measurable. -/
theorem measurable_externalScaledENNRewardSummand
    (weight : ℕ → σ → ℝ≥0∞) (reward : α → ℝ≥0∞)
    (hweight : ∀ n, Measurable (weight n)) (hreward : Measurable reward)
    (n : ℕ) :
    Measurable (fun z : σ × (ℕ → α) =>
      weight n z.1 * reward (coordinate n z.2)) := by
  exact ((hweight n).comp measurable_fst).mul
    (hreward.comp ((measurable_coordinate (α := α) n).comp measurable_snd))

/-- One externally weighted IID reward factors into the external mean weight
and the IID reward mean. -/
theorem lintegral_externalScaledENNRewardSummand
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (weight : ℕ → σ → ℝ≥0∞) (reward : α → ℝ≥0∞)
    (hweight : ∀ n, Measurable (weight n)) (hreward : Measurable reward)
    (n : ℕ) :
    ∫⁻ z : σ × (ℕ → α), weight n z.1 * reward (coordinate n z.2)
      ∂(ρ.prod (measure μ)) =
      (∫⁻ x, weight n x ∂ρ) * ∫⁻ x, reward x ∂μ := by
  letI : IsProbabilityMeasure (measure μ) := by
    dsimp [measure]
    infer_instance
  have hindep := indepFun_state_coordinate ρ μ n
  have hfactor := ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
    ((hweight n).comp measurable_fst)
    (hreward.comp ((measurable_coordinate (α := α) n).comp measurable_snd))
    (hindep.comp (hweight n) hreward)
  have hweightIntegral :
      (∫⁻ z : σ × (ℕ → α), weight n z.1 ∂(ρ.prod (measure μ))) =
        ∫⁻ x, weight n x ∂ρ := by
    exact (measurePreserving_fst : MeasurePreserving Prod.fst
      (ρ.prod (measure μ)) ρ).hasLaw.lintegral_comp (hweight n).aemeasurable
  have hrewardIntegral :
      (∫⁻ z : σ × (ℕ → α), reward (coordinate n z.2)
        ∂(ρ.prod (measure μ))) = ∫⁻ x, reward x ∂μ := by
    exact ((coordinate_measurePreserving μ n).comp
      (measurePreserving_snd : MeasurePreserving Prod.snd
        (ρ.prod (measure μ)) (measure μ))).hasLaw.lintegral_comp hreward.aemeasurable
  calc
    ∫⁻ z : σ × (ℕ → α), weight n z.1 * reward (coordinate n z.2)
        ∂(ρ.prod (measure μ)) =
        (∫⁻ z : σ × (ℕ → α), weight n z.1 ∂(ρ.prod (measure μ))) *
          ∫⁻ z : σ × (ℕ → α), reward (coordinate n z.2)
            ∂(ρ.prod (measure μ)) := by
          simpa only [Function.comp_apply] using hfactor
    _ = (∫⁻ x, weight n x ∂ρ) * ∫⁻ x, reward x ∂μ := by
          rw [hweightIntegral, hrewardIntegral]

/-- Tonelli factors a total externally weighted IID reward into its expected
external weights and the IID reward mean. -/
theorem lintegral_externalScaledENNReward
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (weight : ℕ → σ → ℝ≥0∞) (reward : α → ℝ≥0∞)
    (hweight : ∀ n, Measurable (weight n)) (hreward : Measurable reward) :
    ∫⁻ z, externalScaledENNReward weight reward z ∂(ρ.prod (measure μ)) =
      ∑' n, (∫⁻ x, weight n x ∂ρ) * ∫⁻ x, reward x ∂μ := by
  calc
    ∫⁻ z, externalScaledENNReward weight reward z ∂(ρ.prod (measure μ)) =
        ∫⁻ z, ∑' n, weight n z.1 * reward (coordinate n z.2)
          ∂(ρ.prod (measure μ)) := by rfl
    _ = ∑' n, ∫⁻ z : σ × (ℕ → α), weight n z.1 * reward (coordinate n z.2)
          ∂(ρ.prod (measure μ)) := by
          exact MeasureTheory.lintegral_tsum fun n =>
            (measurable_externalScaledENNRewardSummand weight reward hweight hreward n).aemeasurable
    _ = ∑' n, (∫⁻ x, weight n x ∂ρ) * ∫⁻ x, reward x ∂μ := by
          apply tsum_congr
          intro n
          exact lintegral_externalScaledENNRewardSummand
            ρ μ weight reward hweight hreward n

/-- Finite expected external weight and finite IID reward mean imply finite
expected total externally weighted reward. -/
theorem lintegral_externalScaledENNReward_ne_top
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (weight : ℕ → σ → ℝ≥0∞) (reward : α → ℝ≥0∞)
    (hweight : ∀ n, Measurable (weight n)) (hreward : Measurable reward)
    (hweight_finite : ∑' n, ∫⁻ x, weight n x ∂ρ ≠ ⊤)
    (hreward_finite : ∫⁻ x, reward x ∂μ ≠ ⊤) :
    ∫⁻ z, externalScaledENNReward weight reward z ∂(ρ.prod (measure μ)) ≠ ⊤ := by
  rw [lintegral_externalScaledENNReward ρ μ weight reward hweight hreward,
    ENNReal.tsum_mul_right]
  exact ENNReal.mul_ne_top hweight_finite hreward_finite

/-- A finite expected externally weighted IID reward is finite almost surely. -/
theorem ae_externalScaledENNReward_lt_top
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (weight : ℕ → σ → ℝ≥0∞) (reward : α → ℝ≥0∞)
    (hweight : ∀ n, Measurable (weight n)) (hreward : Measurable reward)
    (hweight_finite : ∑' n, ∫⁻ x, weight n x ∂ρ ≠ ⊤)
    (hreward_finite : ∫⁻ x, reward x ∂μ ≠ ⊤) :
    ∀ᵐ z ∂(ρ.prod (measure μ)), externalScaledENNReward weight reward z < ⊤ := by
  apply MeasureTheory.ae_lt_top
  · exact Measurable.ennreal_tsum fun n =>
      measurable_externalScaledENNRewardSummand weight reward hweight hreward n
  · exact lintegral_externalScaledENNReward_ne_top
      ρ μ weight reward hweight hreward hweight_finite hreward_finite

end

end AppliedModelingLib.Probability.IIDStream

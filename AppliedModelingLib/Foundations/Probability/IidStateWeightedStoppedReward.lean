import AppliedModelingLib.Foundations.Probability.IidStatePrefixStopping

/-!
# Externally weighted rewards through an IID-prefix stop

This module records finite compensation identities for IID rewards whose
coefficient is supplied by an independent external path.  The stopping index
may inspect that external path and the IID coordinates already inspected by
the stop.  This is the finite stopped-reward form needed when a queue state
is independent of the holding-time stream.
-/

namespace AppliedModelingLib.Probability.IIDStream.StatePrefixStoppingIndex

open MeasureTheory ProbabilityTheory

noncomputable section

variable {σ α : Type*} [MeasurableSpace σ] [MeasurableSpace α]

/-- The finite reward through a state-plus-IID prefix stop, with the `n`th
coefficient read from an independent external state. -/
def truncatedExternalWeightedStoppedReward
    (τ : StatePrefixStoppingIndex (σ := σ) (α := α))
    (weight : ℕ → σ → ℝ) (reward : α → ℝ) (cap : ℕ) :
    σ × (ℕ → α) → ℝ :=
  fun z => ∑ n ∈ Finset.range (cap + 1),
    if n ≤ τ z then weight n z.1 * reward (coordinate n z.2) else 0

/-- The finite externally weighted stopped reward is measurable when both
the external weights and the one-coordinate reward are measurable. -/
theorem measurable_truncatedExternalWeightedStoppedReward
    (τ : StatePrefixStoppingIndex (σ := σ) (α := α))
    (weight : ℕ → σ → ℝ) (reward : α → ℝ)
    (hweight : ∀ n, Measurable (weight n)) (hreward : Measurable reward)
    (cap : ℕ) :
    Measurable (truncatedExternalWeightedStoppedReward τ weight reward cap) := by
  unfold truncatedExternalWeightedStoppedReward
  apply Finset.measurable_fun_sum
  intro n _
  exact Measurable.ite (τ.measurableSet_continuationEvent n)
    (((hweight n).comp measurable_fst).mul
      (hreward.comp ((measurable_coordinate (α := α) n).comp measurable_snd)))
    measurable_const

/-- A uniformly bounded external coefficient preserves integrability of an
IID coordinate reward after restriction to any prefix-stop continuation
event. -/
theorem integrable_externalWeighted_continuationEvent_mul_coordinate_of_bound
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (τ : StatePrefixStoppingIndex (σ := σ) (α := α)) (n : ℕ)
    (weight : σ → ℝ) (hweight : Measurable weight)
    (bound : ℝ) (hbound_nonneg : 0 ≤ bound)
    (hbound : ∀ state, ‖weight state‖ ≤ bound)
    (reward : α → ℝ) (hreward : Measurable reward)
    (hintegrable : Integrable reward μ) :
    Integrable (fun z : σ × (ℕ → α) =>
      if n ≤ τ z then weight z.1 * reward (coordinate n z.2) else 0)
      (ρ.prod (measure μ)) := by
  have hmeas : Measurable (fun z : σ × (ℕ → α) =>
      if n ≤ τ z then weight z.1 * reward (coordinate n z.2) else 0) :=
    Measurable.ite (τ.measurableSet_continuationEvent n)
      ((hweight.comp measurable_fst).mul
        (hreward.comp ((measurable_coordinate (α := α) n).comp measurable_snd)))
      measurable_const
  have hcoordinate : Integrable (fun z : σ × (ℕ → α) =>
      reward (coordinate n z.2)) (ρ.prod (measure μ)) :=
    integrable_state_coordinate ρ μ reward hintegrable n
  refine Integrable.mono' (hcoordinate.norm.const_mul bound)
    hmeas.aestronglyMeasurable ?_
  filter_upwards with z
  by_cases hcontinue : n ≤ τ z
  · simp only [hcontinue, ite_true, norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hbound z.1) (abs_nonneg _)
  · simp only [hcontinue, ite_false, norm_zero]
    exact mul_nonneg hbound_nonneg (abs_nonneg _)

/-- At each stopped coordinate, the independent IID reward factors from the
external weight and inspected prefix.  The right-hand factor is the literal
mean external weight on the continuation event, not a deterministic
substitute for it. -/
theorem integral_externalWeighted_continuationEvent_mul_coordinate
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (τ : StatePrefixStoppingIndex (σ := σ) (α := α)) (n : ℕ)
    (weight : σ → ℝ) (hweight : Measurable weight)
    (reward : α → ℝ) (hreward : Measurable reward) :
    ∫ z, (if n ≤ τ z then weight z.1 * reward (coordinate n z.2) else 0)
      ∂(ρ.prod (measure μ)) =
      (∫ z, if n ≤ τ z then weight z.1 else 0 ∂(ρ.prod (measure μ))) *
        ∫ x, reward x ∂μ := by
  letI : IsProbabilityMeasure (measure μ) := by
    dsimp [measure]
    infer_instance
  cases n with
  | zero =>
      have hindep := indepFun_state_coordinate ρ μ 0
      have hfactor := hindep.integral_comp_mul_comp
        measurable_fst.aemeasurable
        ((measurable_coordinate (α := α) 0).comp measurable_snd).aemeasurable
        hweight.aestronglyMeasurable hreward.aestronglyMeasurable
      have hweightIntegral :
          (∫ z : σ × (ℕ → α), weight z.1 ∂(ρ.prod (measure μ))) =
            ∫ x, weight x ∂ρ := by
        exact (measurePreserving_fst : MeasurePreserving Prod.fst
          (ρ.prod (measure μ)) ρ).hasLaw.integral_comp hweight.aestronglyMeasurable
      have hrewardIntegral :
          (∫ z : σ × (ℕ → α), reward (coordinate 0 z.2)
            ∂(ρ.prod (measure μ))) = ∫ x, reward x ∂μ := by
        exact ((coordinate_measurePreserving μ 0).comp
          (measurePreserving_snd : MeasurePreserving Prod.snd
            (ρ.prod (measure μ)) (measure μ))).hasLaw.integral_comp
            hreward.aestronglyMeasurable
      change (∫ z : σ × (ℕ → α), weight z.1 * reward (coordinate 0 z.2)
          ∂(ρ.prod (measure μ))) =
        (∫ z : σ × (ℕ → α), weight z.1 ∂(ρ.prod (measure μ))) * ∫ x, reward x ∂μ
      calc
        (∫ z : σ × (ℕ → α), weight z.1 * reward (coordinate 0 z.2)
            ∂(ρ.prod (measure μ))) =
            (∫ z : σ × (ℕ → α), weight z.1 ∂(ρ.prod (measure μ))) *
              ∫ z : σ × (ℕ → α), reward (coordinate 0 z.2)
                ∂(ρ.prod (measure μ)) := by
              simpa only [Function.comp_apply] using hfactor
        _ = (∫ z : σ × (ℕ → α), weight z.1 ∂(ρ.prod (measure μ))) *
              ∫ x, reward x ∂μ := by rw [hrewardIntegral]
  | succ n =>
      rcases τ.continuationEvent_succ_prefix_measurable n with ⟨u, hu, hpre⟩
      let F : σ × (Finset.range (n + 1) → α) → ℝ := fun visible =>
        u.indicator (fun visible => weight visible.1) visible
      let G : (Fin 1 → α) → ℝ := fun block => reward (block 0)
      have hF : Measurable F := (hweight.comp measurable_fst).indicator hu
      have hG : Measurable G := hreward.comp (measurable_pi_apply 0)
      have hindep := indepFun_state_streamPrefix_block ρ μ n 1
      have hfactor := hindep.integral_comp_mul_comp
        (measurable_stateStreamPrefix (σ := σ) (α := α) n).aemeasurable
        ((measurable_block (α := α) (n + 1) 1).comp measurable_snd).aemeasurable
        hF.aestronglyMeasurable hG.aestronglyMeasurable
      have hleft :
          (fun z : σ × (ℕ → α) => F (stateStreamPrefix (σ := σ) (α := α) n z) *
              G (block (α := α) (n + 1) 1 z.2)) =
            fun z => if n + 1 ≤ τ z then
              weight z.1 * reward (coordinate (n + 1) z.2) else 0 := by
        funext z
        have hmem : stateStreamPrefix (σ := σ) (α := α) n z ∈ u ↔
            z ∈ τ.continuationEvent (n + 1) := by
          change z ∈ stateStreamPrefix (σ := σ) (α := α) n ⁻¹' u ↔
            z ∈ τ.continuationEvent (n + 1)
          rw [hpre]
        by_cases h : stateStreamPrefix (σ := σ) (α := α) n z ∈ u
        · have hcont : n + 1 ≤ τ z := by
            simpa [continuationEvent] using hmem.mp h
          have hvisible : (z.1, streamPrefix (α := α) n z.2) ∈ u := by
            simpa [stateStreamPrefix] using h
          simp [F, G, block, coordinate, stateStreamPrefix, Set.indicator, hvisible, hcont]
        · have hnot : ¬ n + 1 ≤ τ z := by
            intro hcont
            apply h
            apply hmem.mpr
            simpa [continuationEvent] using hcont
          have hvisible : (z.1, streamPrefix (α := α) n z.2) ∉ u := by
            simpa [stateStreamPrefix] using h
          simp [F, G, block, coordinate, stateStreamPrefix, Set.indicator, hvisible, hnot]
      have hprefix :
          (∫ z : σ × (ℕ → α), F (stateStreamPrefix (σ := σ) (α := α) n z)
            ∂(ρ.prod (measure μ))) =
            ∫ z, if n + 1 ≤ τ z then weight z.1 else 0 ∂(ρ.prod (measure μ)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        have hmem : stateStreamPrefix (σ := σ) (α := α) n z ∈ u ↔
            z ∈ τ.continuationEvent (n + 1) := by
          change z ∈ stateStreamPrefix (σ := σ) (α := α) n ⁻¹' u ↔
            z ∈ τ.continuationEvent (n + 1)
          rw [hpre]
        by_cases h : stateStreamPrefix (σ := σ) (α := α) n z ∈ u
        · have hcont : n + 1 ≤ τ z := by
            simpa [continuationEvent] using hmem.mp h
          have hvisible : (z.1, streamPrefix (α := α) n z.2) ∈ u := by
            simpa [stateStreamPrefix] using h
          simp [F, stateStreamPrefix, Set.indicator, hvisible, hcont]
        · have hnot : ¬ n + 1 ≤ τ z := by
            intro hcont
            apply h
            apply hmem.mpr
            simpa [continuationEvent] using hcont
          have hvisible : (z.1, streamPrefix (α := α) n z.2) ∉ u := by
            simpa [stateStreamPrefix] using h
          simp [F, stateStreamPrefix, Set.indicator, hvisible, hnot]
      have hrewardIntegral :
          (∫ z : σ × (ℕ → α), G (block (α := α) (n + 1) 1 z.2)
            ∂(ρ.prod (measure μ))) = ∫ x, reward x ∂μ := by
        exact ((coordinate_measurePreserving μ (n + 1)).comp
          (measurePreserving_snd : MeasurePreserving Prod.snd
            (ρ.prod (measure μ)) (measure μ))).hasLaw.integral_comp
            hreward.aestronglyMeasurable
      calc
        (∫ z, (if n + 1 ≤ τ z then
            weight z.1 * reward (coordinate (n + 1) z.2) else 0)
            ∂(ρ.prod (measure μ))) =
            ∫ z : σ × (ℕ → α), F (stateStreamPrefix (σ := σ) (α := α) n z) *
              G (block (α := α) (n + 1) 1 z.2) ∂(ρ.prod (measure μ)) := by
              rw [hleft]
        _ = (∫ z : σ × (ℕ → α), F (stateStreamPrefix (σ := σ) (α := α) n z)
              ∂(ρ.prod (measure μ))) *
            ∫ z : σ × (ℕ → α), G (block (α := α) (n + 1) 1 z.2)
              ∂(ρ.prod (measure μ)) := by
              simpa only [Function.comp_apply] using hfactor
        _ = (∫ z, if n + 1 ≤ τ z then weight z.1 else 0
              ∂(ρ.prod (measure μ))) * ∫ x, reward x ∂μ := by
              rw [hprefix, hrewardIntegral]

/-- The finite weighted stopped-reward identity.  Integrability of each
summand is stated explicitly, so the lemma applies equally to bounded and
unbounded external state weights. -/
theorem integral_truncatedExternalWeightedStoppedReward
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (τ : StatePrefixStoppingIndex (σ := σ) (α := α))
    (weight : ℕ → σ → ℝ) (reward : α → ℝ)
    (hweight : ∀ n, Measurable (weight n)) (hreward : Measurable reward)
    (hintegrable : ∀ n, Integrable (fun z : σ × (ℕ → α) =>
      if n ≤ τ z then weight n z.1 * reward (coordinate n z.2) else 0)
        (ρ.prod (measure μ))) (cap : ℕ) :
    ∫ z, truncatedExternalWeightedStoppedReward τ weight reward cap z
      ∂(ρ.prod (measure μ)) =
      ∑ n ∈ Finset.range (cap + 1),
        (∫ z, if n ≤ τ z then weight n z.1 else 0 ∂(ρ.prod (measure μ))) *
          ∫ x, reward x ∂μ := by
  unfold truncatedExternalWeightedStoppedReward
  rw [MeasureTheory.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro n _
    exact integral_externalWeighted_continuationEvent_mul_coordinate
      ρ μ τ n (weight n) (hweight n) reward hreward
  · intro n _
    exact hintegrable n

/-- Centered IID rewards have zero mean after every finite externally
weighted prefix stop. -/
theorem integral_truncatedExternalWeightedStoppedReward_eq_zero_of_integral_eq_zero
    (ρ : Measure σ) (μ : Measure α)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
    (τ : StatePrefixStoppingIndex (σ := σ) (α := α))
    (weight : ℕ → σ → ℝ) (reward : α → ℝ)
    (hweight : ∀ n, Measurable (weight n)) (hreward : Measurable reward)
    (hintegrable : ∀ n, Integrable (fun z : σ × (ℕ → α) =>
      if n ≤ τ z then weight n z.1 * reward (coordinate n z.2) else 0)
        (ρ.prod (measure μ))) (cap : ℕ)
    (hcentered : ∫ x, reward x ∂μ = 0) :
    ∫ z, truncatedExternalWeightedStoppedReward τ weight reward cap z
      ∂(ρ.prod (measure μ)) = 0 := by
  rw [integral_truncatedExternalWeightedStoppedReward
    ρ μ τ weight reward hweight hreward hintegrable cap, hcentered]
  simp

end

end AppliedModelingLib.Probability.IIDStream.StatePrefixStoppingIndex

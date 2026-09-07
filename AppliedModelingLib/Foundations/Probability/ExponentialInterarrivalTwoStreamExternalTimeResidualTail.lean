import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalDeterministicResidualTail

/-!
# External-time residual factors with a companion exponential stream

This module begins the product-space bookkeeping required when a clock time
is selected independently of two exponential renewal streams.  It first
factors one literal residual stream while retaining the other stream as an
untouched companion.  A later result can apply the same construction in the
opposite order; no continuous-time strong-Markov assumption is introduced.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory

noncomputable section

/-- Expose the past and residual tail of the left exponential stream at an
external clock value while retaining the right stream literally. -/
def externalTimeLeftPastResidualWithCompanion
    {β : Type*} [MeasurableSpace β] (time : β → ℝ) :
    (β × (ℕ → ℝ)) × (ℕ → ℝ) →
      ((β × (ℕ × (ℕ → ℝ))) × (ℕ → ℝ)) × (ℕ → ℝ) :=
  fun z =>
    ((externalTimePastHistory time z.1, z.2), externalTimeResidualTail time z.1)

/-- Measurability of the left-stream external-time factor with its companion. -/
theorem measurable_externalTimeLeftPastResidualWithCompanion
    {β : Type*} [MeasurableSpace β] (time : β → ℝ) (htime : Measurable time) :
    Measurable (externalTimeLeftPastResidualWithCompanion time) := by
  unfold externalTimeLeftPastResidualWithCompanion
  exact
    (((measurable_externalTimePastHistory time htime).comp measurable_fst).prodMk
      measurable_snd).prodMk
      ((measurable_externalTimeResidualTail time htime).comp measurable_fst)

/-- Reassociate a pair of independent factors so that a companion stream
travels with the exposed history rather than the residual tail. -/
private def leftResidualCompanionRearrange {α β γ : Type*}
    (z : (α × β) × γ) : (α × γ) × β :=
  ((z.1.1, z.2), z.1.2)

private theorem measurable_leftResidualCompanionRearrange {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] :
    Measurable (leftResidualCompanionRearrange (α := α) (β := β) (γ := γ)) := by
  exact ((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
    (measurable_snd.comp measurable_fst)

private theorem map_leftResidualCompanionRearrange
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure β) (ξ : Measure γ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ξ] :
    Measure.map (leftResidualCompanionRearrange (α := α) (β := β) (γ := γ))
      ((μ.prod ν).prod ξ) = (μ.prod ξ).prod ν := by
  have hassocSymm :
      Measure.map (MeasurableEquiv.prodAssoc.symm : α × (γ × β) → (α × γ) × β)
        (μ.prod (ξ.prod ν)) = (μ.prod ξ).prod ν := by
    rw [← Measure.prodAssoc_prod]
    rw [Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
      MeasurableEquiv.prodAssoc.measurable]
    have hcomp :
        (MeasurableEquiv.prodAssoc.symm : α × (γ × β) → (α × γ) × β) ∘
          (MeasurableEquiv.prodAssoc : (α × γ) × β → α × (γ × β)) = id := by
      funext x
      rfl
    rw [hcomp, Measure.map_id]
  calc
    Measure.map (leftResidualCompanionRearrange (α := α) (β := β) (γ := γ))
        ((μ.prod ν).prod ξ) =
      Measure.map (MeasurableEquiv.prodAssoc.symm : α × (γ × β) → (α × γ) × β)
        (Measure.map (Prod.map id Prod.swap)
          (Measure.map (MeasurableEquiv.prodAssoc : (α × β) × γ → α × (β × γ))
            ((μ.prod ν).prod ξ))) := by
          symm
          rw [Measure.map_map (measurable_id.prodMap measurable_swap)
              MeasurableEquiv.prodAssoc.measurable,
            Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
              ((measurable_id.prodMap measurable_swap).comp
                MeasurableEquiv.prodAssoc.measurable)]
          rfl
    _ = Measure.map (MeasurableEquiv.prodAssoc.symm : α × (γ × β) → (α × γ) × β)
        (Measure.map (Prod.map id Prod.swap) (μ.prod (ν.prod ξ))) := by
          rw [Measure.prodAssoc_prod]
    _ = Measure.map (MeasurableEquiv.prodAssoc.symm : α × (γ × β) → (α × γ) × β)
        (μ.prod (ξ.prod ν)) := by
          rw [← Measure.map_prod_map _ _ measurable_id measurable_swap,
            Measure.map_id, Measure.prod_swap]
    _ = (μ.prod ξ).prod ν := hassocSymm

/-- At a nonnegative time chosen by an independent external state, the left
exponential residual tail is fresh and independent of the full exposed left
history *together with* an untouched independent right stream. -/
theorem map_externalTimeLeftPastResidualWithCompanion
    {β : Type*} [MeasurableSpace β] (ν : Measure β) [IsProbabilityMeasure ν]
    {leftRate rightRate : ℝ} (hleft : 0 < leftRate) (hright : 0 < rightRate)
    (time : β → ℝ) (htime : Measurable time) (htime_nonneg : ∀ b, 0 ≤ time b) :
    Measure.map (externalTimeLeftPastResidualWithCompanion time)
      ((ν.prod (exponentialInterarrivalMeasure leftRate)).prod
        (exponentialInterarrivalMeasure rightRate)) =
      ((Measure.map (externalTimePastHistory time)
        (ν.prod (exponentialInterarrivalMeasure leftRate))).prod
          (exponentialInterarrivalMeasure rightRate)).prod
        (exponentialInterarrivalMeasure leftRate) := by
  let leftMeasure : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure leftRate
  let rightMeasure : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rightRate
  let H : β × (ℕ → ℝ) → β × (ℕ × (ℕ → ℝ)) := externalTimePastHistory time
  let R : β × (ℕ → ℝ) → ℕ → ℝ := externalTimeResidualTail time
  let F : β × (ℕ → ℝ) → (β × (ℕ × (ℕ → ℝ))) × (ℕ → ℝ) :=
    fun z => (H z, R z)
  letI : IsProbabilityMeasure leftMeasure := by
    simpa [leftMeasure] using isProbabilityMeasure_exponentialInterarrivalMeasure hleft
  letI : IsProbabilityMeasure rightMeasure := by
    simpa [rightMeasure] using isProbabilityMeasure_exponentialInterarrivalMeasure hright
  letI : IsProbabilityMeasure (Measure.map H (ν.prod leftMeasure)) :=
    Measure.isProbabilityMeasure_map (measurable_externalTimePastHistory time htime).aemeasurable
  have hF : Measurable F := by
    exact (measurable_externalTimePastHistory time htime).prodMk
      (measurable_externalTimeResidualTail time htime)
  have hfactor : Measure.map F (ν.prod leftMeasure) =
      (Measure.map H (ν.prod leftMeasure)).prod leftMeasure := by
    simpa [F, H, R, leftMeasure] using
      map_externalTimePastHistory_residualTail ν hleft time htime htime_nonneg
  rw [show externalTimeLeftPastResidualWithCompanion time =
      leftResidualCompanionRearrange ∘ Prod.map F id by
    funext z
    rfl]
  rw [← Measure.map_map measurable_leftResidualCompanionRearrange
    (hF.prodMap measurable_id)]
  rw [← Measure.map_prod_map _ _ hF measurable_id, hfactor, Measure.map_id]
  exact map_leftResidualCompanionRearrange
    (Measure.map H (ν.prod leftMeasure)) leftMeasure rightMeasure

/-- Expose the left stopped history while grouping the fresh left residual
with the untouched right companion.  This is the product layout used when
the two paths will become state-indexed future holding streams. -/
def externalTimeLeftHistoryResidualCompanionFactor
    {β : Type*} [MeasurableSpace β] (time : β → ℝ) :
    (β × (ℕ → ℝ)) × (ℕ → ℝ) →
      (β × (ℕ × (ℕ → ℝ))) × ((ℕ → ℝ) × (ℕ → ℝ)) :=
  fun z =>
    (externalTimePastHistory time z.1,
      (externalTimeResidualTail time z.1, z.2))

theorem measurable_externalTimeLeftHistoryResidualCompanionFactor
    {β : Type*} [MeasurableSpace β] (time : β → ℝ) (htime : Measurable time) :
    Measurable (externalTimeLeftHistoryResidualCompanionFactor time) := by
  exact (measurable_externalTimePastHistory time htime).comp measurable_fst |>.prodMk
    (((measurable_externalTimeResidualTail time htime).comp measurable_fst).prodMk
      measurable_snd)

private def leftHistoryResidualCompanionRearrange {α β γ : Type*}
    (z : (α × β) × γ) : α × (γ × β) :=
  (z.1.1, (z.2, z.1.2))

private theorem measurable_leftHistoryResidualCompanionRearrange {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] :
    Measurable (leftHistoryResidualCompanionRearrange (α := α) (β := β) (γ := γ)) := by
  exact (measurable_fst.comp measurable_fst).prodMk
    ((measurable_snd.prodMk (measurable_snd.comp measurable_fst)))

private theorem map_leftHistoryResidualCompanionRearrange
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure β) (ξ : Measure γ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ξ] :
    Measure.map (leftHistoryResidualCompanionRearrange (α := α) (β := β) (γ := γ))
      ((μ.prod ν).prod ξ) = μ.prod (ξ.prod ν) := by
  let assoc : (α × β) × γ → α × (β × γ) := MeasurableEquiv.prodAssoc
  let swapRight : α × (β × γ) → α × (γ × β) :=
    fun z => (z.1, (z.2.2, z.2.1))
  have hassoc : Measurable assoc := MeasurableEquiv.prodAssoc.measurable
  have hswapRight : Measurable swapRight := by
    exact measurable_fst.prodMk
      ((measurable_snd.comp measurable_snd).prodMk (measurable_fst.comp measurable_snd))
  have hassocLaw : Measure.map assoc ((μ.prod ν).prod ξ) = μ.prod (ν.prod ξ) := by
    simpa [assoc] using (Measure.prodAssoc_prod :
      Measure.map (MeasurableEquiv.prodAssoc : (α × β) × γ → α × (β × γ))
        ((μ.prod ν).prod ξ) = μ.prod (ν.prod ξ))
  have hswapLaw : Measure.map swapRight (μ.prod (ν.prod ξ)) = μ.prod (ξ.prod ν) := by
    change Measure.map (Prod.map id Prod.swap) (μ.prod (ν.prod ξ)) =
      μ.prod (ξ.prod ν)
    rw [← Measure.map_prod_map _ _ measurable_id measurable_swap,
      Measure.map_id, Measure.prod_swap]
  calc
    Measure.map (leftHistoryResidualCompanionRearrange (α := α) (β := β) (γ := γ))
        ((μ.prod ν).prod ξ) =
      Measure.map swapRight (Measure.map assoc ((μ.prod ν).prod ξ)) := by
        rw [Measure.map_map hswapRight hassoc]
        rfl
    _ = Measure.map swapRight (μ.prod (ν.prod ξ)) := by rw [hassocLaw]
    _ = μ.prod (ξ.prod ν) := hswapLaw

/-- At an external nonnegative time, the exposed left history factors from
the fresh left residual paired with the untouched right exponential stream. -/
theorem map_externalTimeLeftHistory_residualCompanion
    {β : Type*} [MeasurableSpace β] (ν : Measure β) [IsProbabilityMeasure ν]
    {leftRate rightRate : ℝ} (hleft : 0 < leftRate) (hright : 0 < rightRate)
    (time : β → ℝ) (htime : Measurable time) (htime_nonneg : ∀ b, 0 ≤ time b) :
    Measure.map (externalTimeLeftHistoryResidualCompanionFactor time)
      ((ν.prod (exponentialInterarrivalMeasure leftRate)).prod
        (exponentialInterarrivalMeasure rightRate)) =
      (Measure.map (externalTimePastHistory time)
        (ν.prod (exponentialInterarrivalMeasure leftRate))).prod
        ((exponentialInterarrivalMeasure leftRate).prod
          (exponentialInterarrivalMeasure rightRate)) := by
  let leftMeasure : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure leftRate
  let rightMeasure : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rightRate
  let H : β × (ℕ → ℝ) → β × (ℕ × (ℕ → ℝ)) := externalTimePastHistory time
  let R : β × (ℕ → ℝ) → ℕ → ℝ := externalTimeResidualTail time
  let F : (β × (ℕ → ℝ)) × (ℕ → ℝ) →
      ((β × (ℕ × (ℕ → ℝ))) × (ℕ → ℝ)) × (ℕ → ℝ) :=
    externalTimeLeftPastResidualWithCompanion time
  let G : (β × (ℕ → ℝ)) × (ℕ → ℝ) →
      (β × (ℕ × (ℕ → ℝ))) × ((ℕ → ℝ) × (ℕ → ℝ)) :=
    externalTimeLeftHistoryResidualCompanionFactor time
  letI : IsProbabilityMeasure leftMeasure := by
    simpa [leftMeasure] using isProbabilityMeasure_exponentialInterarrivalMeasure hleft
  letI : IsProbabilityMeasure rightMeasure := by
    simpa [rightMeasure] using isProbabilityMeasure_exponentialInterarrivalMeasure hright
  letI : IsProbabilityMeasure (Measure.map H (ν.prod leftMeasure)) :=
    Measure.isProbabilityMeasure_map
      (measurable_externalTimePastHistory time htime).aemeasurable
  have hF : Measurable F := by
    simpa [F] using measurable_externalTimeLeftPastResidualWithCompanion time htime
  have hG : Measurable G := by
    simpa [G] using measurable_externalTimeLeftHistoryResidualCompanionFactor time htime
  have hfactor : Measure.map F ((ν.prod leftMeasure).prod rightMeasure) =
      ((Measure.map H (ν.prod leftMeasure)).prod rightMeasure).prod leftMeasure := by
    simpa [F, H, leftMeasure, rightMeasure] using
      map_externalTimeLeftPastResidualWithCompanion ν hleft hright
        time htime htime_nonneg
  have hcompose : G =
      leftHistoryResidualCompanionRearrange ∘ F := by
    funext z
    rfl
  change Measure.map G ((ν.prod leftMeasure).prod rightMeasure) =
    (Measure.map H (ν.prod leftMeasure)).prod (leftMeasure.prod rightMeasure)
  rw [hcompose, ← Measure.map_map measurable_leftHistoryResidualCompanionRearrange hF,
    hfactor]
  exact map_leftHistoryResidualCompanionRearrange
    (Measure.map H (ν.prod leftMeasure)) rightMeasure leftMeasure

/-- The complete two-stream stopped history at an external clock time. The
right history is taken after retaining the exposed left history as external
data, so both paths are observed at the same literal time. -/
def externalTimeTwoStreamPastHistory
    {β : Type*} [MeasurableSpace β] (time : β → ℝ) :
    (β × (ℕ → ℝ)) × (ℕ → ℝ) →
      (β × (ℕ × (ℕ → ℝ))) × (ℕ × (ℕ → ℝ)) :=
  fun z =>
    externalTimePastHistory (fun h : β × (ℕ × (ℕ → ℝ)) => time h.1)
      (externalTimePastHistory time z.1, z.2)

/-- The two literal residual paths from the same external clock time. -/
def externalTimeTwoStreamResidualTails
    {β : Type*} [MeasurableSpace β] (time : β → ℝ) :
    (β × (ℕ → ℝ)) × (ℕ → ℝ) → (ℕ → ℝ) × (ℕ → ℝ) :=
  fun z =>
    (externalTimeResidualTail time z.1,
      externalTimeResidualTail (fun h : β × (ℕ × (ℕ → ℝ)) => time h.1)
        (externalTimePastHistory time z.1, z.2))

/-- Joint measurability of the complete stopped two-stream history. -/
theorem measurable_externalTimeTwoStreamPastHistory
    {β : Type*} [MeasurableSpace β] (time : β → ℝ) (htime : Measurable time) :
    Measurable (externalTimeTwoStreamPastHistory time) := by
  let H : β × (ℕ → ℝ) → β × (ℕ × (ℕ → ℝ)) := externalTimePastHistory time
  let timeH : β × (ℕ × (ℕ → ℝ)) → ℝ := fun h => time h.1
  have hH : Measurable H := by
    simpa [H] using measurable_externalTimePastHistory time htime
  have htimeH : Measurable timeH := by
    exact htime.comp measurable_fst
  simpa [externalTimeTwoStreamPastHistory, H, timeH] using
    (measurable_externalTimePastHistory timeH htimeH).comp
      ((hH.comp measurable_fst).prodMk measurable_snd)

/-- Joint measurability of the two residual tails selected at an external
clock value. -/
theorem measurable_externalTimeTwoStreamResidualTails
    {β : Type*} [MeasurableSpace β] (time : β → ℝ) (htime : Measurable time) :
    Measurable (externalTimeTwoStreamResidualTails time) := by
  let H : β × (ℕ → ℝ) → β × (ℕ × (ℕ → ℝ)) := externalTimePastHistory time
  let timeH : β × (ℕ × (ℕ → ℝ)) → ℝ := fun h => time h.1
  have hH : Measurable H := by
    simpa [H] using measurable_externalTimePastHistory time htime
  have htimeH : Measurable timeH := by
    exact htime.comp measurable_fst
  have hleft : Measurable (fun z : (β × (ℕ → ℝ)) × (ℕ → ℝ) =>
      externalTimeResidualTail time z.1) :=
    (measurable_externalTimeResidualTail time htime).comp measurable_fst
  have hright : Measurable (fun z : (β × (ℕ → ℝ)) × (ℕ → ℝ) =>
      externalTimeResidualTail timeH (H z.1, z.2)) :=
    (measurable_externalTimeResidualTail timeH htimeH).comp
      ((hH.comp measurable_fst).prodMk measurable_snd)
  simpa [externalTimeTwoStreamResidualTails, H, timeH] using hleft.prodMk hright

/-- Two independent exponential renewal paths, observed at the same
nonnegative time chosen by an independent external state, have fresh joint
residual tails independent of their complete joint stopped history. The proof
factors the left path first, then the right path with the left residual held as
an independent companion; it is not a strong-Markov axiom. -/
theorem map_externalTimeTwoStreamPastHistory_residualTails
    {β : Type*} [MeasurableSpace β] (ν : Measure β) [IsProbabilityMeasure ν]
    {leftRate rightRate : ℝ} (hleft : 0 < leftRate) (hright : 0 < rightRate)
    (time : β → ℝ) (htime : Measurable time) (htime_nonneg : ∀ b, 0 ≤ time b) :
    Measure.map (fun z =>
      (externalTimeTwoStreamPastHistory time z,
        externalTimeTwoStreamResidualTails time z))
      ((ν.prod (exponentialInterarrivalMeasure leftRate)).prod
        (exponentialInterarrivalMeasure rightRate)) =
      (Measure.map (externalTimeTwoStreamPastHistory time)
        ((ν.prod (exponentialInterarrivalMeasure leftRate)).prod
          (exponentialInterarrivalMeasure rightRate))).prod
        ((exponentialInterarrivalMeasure leftRate).prod
          (exponentialInterarrivalMeasure rightRate)) := by
  let leftMeasure : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure leftRate
  let rightMeasure : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rightRate
  let H : β × (ℕ → ℝ) → β × (ℕ × (ℕ → ℝ)) := externalTimePastHistory time
  let timeH : β × (ℕ × (ℕ → ℝ)) → ℝ := fun h => time h.1
  let H₂ : (β × (ℕ × (ℕ → ℝ))) × (ℕ → ℝ) →
      (β × (ℕ × (ℕ → ℝ))) × (ℕ × (ℕ → ℝ)) :=
    externalTimePastHistory timeH
  let F₁ : (β × (ℕ → ℝ)) × (ℕ → ℝ) →
      ((β × (ℕ × (ℕ → ℝ))) × (ℕ → ℝ)) × (ℕ → ℝ) :=
    externalTimeLeftPastResidualWithCompanion time
  let F₂ : ((β × (ℕ × (ℕ → ℝ))) × (ℕ → ℝ)) × (ℕ → ℝ) →
      (((β × (ℕ × (ℕ → ℝ))) × (ℕ × (ℕ → ℝ))) × (ℕ → ℝ)) ×
        (ℕ → ℝ) :=
    externalTimeLeftPastResidualWithCompanion timeH
  let J : (β × (ℕ → ℝ)) × (ℕ → ℝ) →
      (β × (ℕ × (ℕ → ℝ))) × (ℕ → ℝ) :=
    fun z => (H z.1, z.2)
  let A : Measure (β × (ℕ × (ℕ → ℝ))) := Measure.map H (ν.prod leftMeasure)
  let A₂ : Measure ((β × (ℕ × (ℕ → ℝ))) × (ℕ × (ℕ → ℝ))) :=
    Measure.map H₂ (A.prod rightMeasure)
  letI : IsProbabilityMeasure leftMeasure := by
    simpa [leftMeasure] using isProbabilityMeasure_exponentialInterarrivalMeasure hleft
  letI : IsProbabilityMeasure rightMeasure := by
    simpa [rightMeasure] using isProbabilityMeasure_exponentialInterarrivalMeasure hright
  have hH : Measurable H := by
    simpa [H] using measurable_externalTimePastHistory time htime
  have htimeH : Measurable timeH := by
    exact htime.comp measurable_fst
  letI : IsProbabilityMeasure A := by
    dsimp [A]
    exact Measure.isProbabilityMeasure_map hH.aemeasurable
  have hH₂ : Measurable H₂ := by
    simpa [H₂] using measurable_externalTimePastHistory timeH htimeH
  letI : IsProbabilityMeasure A₂ := by
    dsimp [A₂]
    exact Measure.isProbabilityMeasure_map hH₂.aemeasurable
  have hF₁ : Measurable F₁ := by
    simpa [F₁] using measurable_externalTimeLeftPastResidualWithCompanion time htime
  have hF₂ : Measurable F₂ := by
    simpa [F₂] using measurable_externalTimeLeftPastResidualWithCompanion timeH htimeH
  have hfirst : Measure.map F₁ ((ν.prod leftMeasure).prod rightMeasure) =
      (A.prod rightMeasure).prod leftMeasure := by
    simpa [F₁, A, leftMeasure, rightMeasure] using
      map_externalTimeLeftPastResidualWithCompanion ν hleft hright
        time htime htime_nonneg
  have hsecond : Measure.map F₂ ((A.prod rightMeasure).prod leftMeasure) =
      (A₂.prod leftMeasure).prod rightMeasure := by
    simpa [F₂, A₂, leftMeasure, rightMeasure] using
      map_externalTimeLeftPastResidualWithCompanion A hright hleft timeH htimeH
        (fun h => htime_nonneg h.1)
  have hJ : Measurable J := (hH.comp measurable_fst).prodMk measurable_snd
  have hJlaw : Measure.map J ((ν.prod leftMeasure).prod rightMeasure) =
      A.prod rightMeasure := by
    dsimp [J, A]
    change Measure.map (Prod.map H id) ((ν.prod leftMeasure).prod rightMeasure) =
      (Measure.map H (ν.prod leftMeasure)).prod rightMeasure
    rw [← Measure.map_prod_map _ _ hH measurable_id, Measure.map_id]
  have hA₂ : Measure.map (externalTimeTwoStreamPastHistory time)
      ((ν.prod leftMeasure).prod rightMeasure) = A₂ := by
    change Measure.map (H₂ ∘ J) ((ν.prod leftMeasure).prod rightMeasure) = A₂
    rw [← Measure.map_map hH₂ hJ, hJlaw]
  let assoc : (((β × (ℕ × (ℕ → ℝ))) × (ℕ × (ℕ → ℝ))) ×
      (ℕ → ℝ)) × (ℕ → ℝ) →
        ((β × (ℕ × (ℕ → ℝ))) × (ℕ × (ℕ → ℝ))) ×
          ((ℕ → ℝ) × (ℕ → ℝ)) :=
    MeasurableEquiv.prodAssoc
  have hassoc : Measurable assoc := MeasurableEquiv.prodAssoc.measurable
  change Measure.map (assoc ∘ F₂ ∘ F₁)
      ((ν.prod leftMeasure).prod rightMeasure) =
    (Measure.map (externalTimeTwoStreamPastHistory time)
      ((ν.prod leftMeasure).prod rightMeasure)).prod (leftMeasure.prod rightMeasure)
  change Measure.map ((assoc ∘ F₂) ∘ F₁)
      ((ν.prod leftMeasure).prod rightMeasure) = _
  rw [← Measure.map_map (hassoc.comp hF₂) hF₁, ← Measure.map_map hassoc hF₂, hfirst, hsecond,
    Measure.prodAssoc_prod, hA₂]

end

end AppliedModelingLib.Probability.PoissonProcess

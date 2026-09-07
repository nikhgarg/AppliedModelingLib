import AppliedModelingLib.Foundations.Probability.StationaryPoissonWorkFutureRate
import AppliedModelingLib.Foundations.Probability.PoissonSuspensionProductFactors
import AppliedModelingLib.Foundations.Probability.IidPrefixStopping
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalDeterministicResidualTail
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalTimeSliceReconstruction
import AppliedModelingLib.Foundations.Probability.PoissonSuspensionDeterministicTimeContinuation
import Mathlib.Tactic

/-!
# External-state and future-input factors for stationary marked Poisson paths

This module splits a stationary marked Poisson input into the complete data
at and before the origin and the independent sequence of future
interarrival/work pairs.  The result is an input-law factorization only: it
does not define a queue, a stopping time, or a response-time distribution.
-/

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory
open PoissonProcess

noncomputable section

/-- Reorder five independent coordinates so that the second, third, and
fifth form an external state while the first and fourth remain a paired
future input. -/
private def fiveFactorFutureExternalReorder {α β γ δ ε : Type*}
    (x : (α × β) × ((γ × δ) × ε)) : ((β × γ) × ε) × (α × δ) :=
  (((x.1.2, x.2.1.1), x.2.2), (x.1.1, x.2.1.2))

private theorem measurable_fiveFactorFutureExternalReorder
    {α β γ δ ε : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] [MeasurableSpace ε] :
    Measurable (@fiveFactorFutureExternalReorder α β γ δ ε) := by
  exact
    (((measurable_snd.comp measurable_fst).prodMk
      (measurable_fst.comp (measurable_fst.comp measurable_snd))).prodMk
      (measurable_snd.comp measurable_snd)).prodMk
      ((measurable_fst.comp measurable_fst).prodMk
        (measurable_snd.comp (measurable_fst.comp measurable_snd)))

/-- The five-coordinate reordering transports the corresponding product law.
The two displayed output blocks are independent because they use disjoint
input coordinates. -/
private theorem map_fiveFactorFutureExternalReorder_prod
    {α β γ δ ε : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] [MeasurableSpace ε]
    (μa : Measure α) (μb : Measure β) (μc : Measure γ)
    (μd : Measure δ) (μe : Measure ε)
    [IsProbabilityMeasure μa] [IsProbabilityMeasure μb]
    [IsProbabilityMeasure μc] [IsProbabilityMeasure μd]
    [IsProbabilityMeasure μe] :
    Measure.map fiveFactorFutureExternalReorder
      ((μa.prod μb).prod ((μc.prod μd).prod μe)) =
      ((μb.prod μc).prod μe).prod (μa.prod μd) := by
  let hCDE : MeasurePreserving
      (MeasurableEquiv.prodAssoc : (γ × δ) × ε ≃ᵐ γ × (δ × ε))
      ((μc.prod μd).prod μe) (μc.prod (μd.prod μe)) :=
    measurePreserving_prodAssoc μc μd μe
  let hBCDE₁ : MeasurePreserving
      (Prod.map id (MeasurableEquiv.prodAssoc : (γ × δ) × ε ≃ᵐ γ × (δ × ε)))
      (μb.prod ((μc.prod μd).prod μe)) (μb.prod (μc.prod (μd.prod μe))) :=
    (MeasurePreserving.id μb).prod hCDE
  let hBCDE₂ : MeasurePreserving
      (MeasurableEquiv.prodAssoc.symm : β × (γ × (δ × ε)) ≃ᵐ
        (β × γ) × (δ × ε))
      (μb.prod (μc.prod (μd.prod μe))) ((μb.prod μc).prod (μd.prod μe)) :=
    (measurePreserving_prodAssoc μb μc (μd.prod μe)).symm
  let hBCDE₃ : MeasurePreserving
      (Prod.map id Prod.swap : (β × γ) × (δ × ε) → (β × γ) × (ε × δ))
      ((μb.prod μc).prod (μd.prod μe)) ((μb.prod μc).prod (μe.prod μd)) :=
    (MeasurePreserving.id (μb.prod μc)).prod
      (Measure.measurePreserving_swap (μ := μd) (ν := μe))
  let hBCDE₄ : MeasurePreserving
      (MeasurableEquiv.prodAssoc.symm : (β × γ) × (ε × δ) ≃ᵐ
        ((β × γ) × ε) × δ)
      ((μb.prod μc).prod (μe.prod μd)) (((μb.prod μc).prod μe).prod μd) :=
    (measurePreserving_prodAssoc (μb.prod μc) μe μd).symm
  let hBCDE : MeasurePreserving
      (fun x : β × ((γ × δ) × ε) =>
        (((x.1, x.2.1.1), x.2.2), x.2.1.2))
      (μb.prod ((μc.prod μd).prod μe)) (((μb.prod μc).prod μe).prod μd) :=
    hBCDE₄.comp (hBCDE₃.comp (hBCDE₂.comp hBCDE₁))
  let h₁ : MeasurePreserving
      (MeasurableEquiv.prodAssoc : (α × β) × ((γ × δ) × ε) ≃ᵐ
        α × (β × ((γ × δ) × ε)))
      ((μa.prod μb).prod ((μc.prod μd).prod μe))
      (μa.prod (μb.prod ((μc.prod μd).prod μe))) :=
    measurePreserving_prodAssoc μa μb ((μc.prod μd).prod μe)
  let h₂ : MeasurePreserving
      (Prod.map id (fun x : β × ((γ × δ) × ε) =>
        (((x.1, x.2.1.1), x.2.2), x.2.1.2)))
      (μa.prod (μb.prod ((μc.prod μd).prod μe)))
      (μa.prod (((μb.prod μc).prod μe).prod μd)) :=
    (MeasurePreserving.id μa).prod hBCDE
  let h₃ : MeasurePreserving
      (MeasurableEquiv.prodAssoc.symm : α × (((β × γ) × ε) × δ) ≃ᵐ
        (α × ((β × γ) × ε)) × δ)
      (μa.prod (((μb.prod μc).prod μe).prod μd))
      ((μa.prod ((μb.prod μc).prod μe)).prod μd) :=
    (measurePreserving_prodAssoc μa ((μb.prod μc).prod μe) μd).symm
  let h₄ : MeasurePreserving
      (Prod.map Prod.swap id : (α × ((β × γ) × ε)) × δ →
        (((β × γ) × ε) × α) × δ)
      ((μa.prod ((μb.prod μc).prod μe)).prod μd)
      ((((μb.prod μc).prod μe).prod μa).prod μd) :=
    (Measure.measurePreserving_swap (μ := μa) (ν := (μb.prod μc).prod μe)).prod
      (MeasurePreserving.id μd)
  let h₅ : MeasurePreserving
      (MeasurableEquiv.prodAssoc : (((β × γ) × ε) × α) × δ ≃ᵐ
        ((β × γ) × ε) × (α × δ))
      ((((μb.prod μc).prod μe).prod μa).prod μd)
      (((μb.prod μc).prod μe).prod (μa.prod μd)) :=
    measurePreserving_prodAssoc ((μb.prod μc).prod μe) μa μd
  let h := h₅.comp (h₄.comp (h₃.comp (h₂.comp h₁)))
  convert h.map_eq using 1

/-- On the equilibrium marked carrier, retain the complete past input and
the origin work mark as external data, while exposing the literal residual
gap sequence and strictly future work-mark sequence. -/
def equilibriumFutureExternalFactors
    (z : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℤ → ℝ)) :
    (((ℕ → ℝ) × ℝ) × (ℕ → ℝ)) × ((ℕ → ℝ) × (ℕ → ℝ)) :=
  let work := twoSidedHeadPositiveNegative z.2
  (((z.1.2, work.1.1), work.2), (z.1.1, work.1.2))

theorem measurable_equilibriumFutureExternalFactors :
    Measurable equilibriumFutureExternalFactors := by
  exact measurable_fiveFactorFutureExternalReorder.comp
    (measurable_id.prodMap measurable_twoSidedHeadPositiveNegative)

/-- Exact product law of the external marked state and the future marked
renewal input on the equilibrium carrier. -/
theorem map_equilibriumFutureExternalFactors
    {rate : ℝ} (hrate : 0 < rate) :
    Measure.map equilibriumFutureExternalFactors
      ((equilibriumTwoSidedBaseMeasure rate).prod
        (twoSidedInterarrivalMeasure (1 : ℝ))) =
      (((exponentialInterarrivalMeasure rate).prod (expMeasure (1 : ℝ))).prod
        (exponentialInterarrivalMeasure (1 : ℝ))).prod
      ((exponentialInterarrivalMeasure rate).prod
        (exponentialInterarrivalMeasure (1 : ℝ))) := by
  let μa : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  let μc : Measure ℝ := expMeasure (1 : ℝ)
  let μd : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure (1 : ℝ)
  letI : IsProbabilityMeasure μa := by
    simpa [μa] using isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure μc := by
    simpa [μc] using isProbabilityMeasure_expMeasure (by norm_num : 0 < (1 : ℝ))
  letI : IsProbabilityMeasure μd := by
    simpa [μd] using isProbabilityMeasure_exponentialInterarrivalMeasure
      (by norm_num : 0 < (1 : ℝ))
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  have hsplit :
      Measure.map (Prod.map id twoSidedHeadPositiveNegative)
        ((μa.prod μa).prod (twoSidedInterarrivalMeasure (1 : ℝ))) =
        (μa.prod μa).prod ((μc.prod μd).prod μd) := by
    rw [← Measure.map_prod_map _ _ measurable_id
      measurable_twoSidedHeadPositiveNegative, Measure.map_id,
      map_twoSidedHeadPositiveNegative_twoSidedInterarrivalMeasure
        (by norm_num : 0 < (1 : ℝ))]
  change Measure.map equilibriumFutureExternalFactors
      ((μa.prod μa).prod (twoSidedInterarrivalMeasure (1 : ℝ))) = _
  calc
    Measure.map equilibriumFutureExternalFactors
        ((μa.prod μa).prod
          (twoSidedInterarrivalMeasure (1 : ℝ))) =
        Measure.map fiveFactorFutureExternalReorder
          (Measure.map (Prod.map id twoSidedHeadPositiveNegative)
            ((μa.prod μa).prod (twoSidedInterarrivalMeasure (1 : ℝ)))) := by
          symm
          rw [Measure.map_map measurable_fiveFactorFutureExternalReorder
            (measurable_id.prodMap measurable_twoSidedHeadPositiveNegative)]
          rfl
    _ = Measure.map fiveFactorFutureExternalReorder
          ((μa.prod μa).prod ((μc.prod μd).prod μd)) := by rw [hsplit]
    _ = ((μa.prod μc).prod μd).prod (μa.prod μd) := by
          rw [map_fiveFactorFutureExternalReorder_prod]
    _ = (((exponentialInterarrivalMeasure rate).prod (expMeasure (1 : ℝ))).prod
          (exponentialInterarrivalMeasure (1 : ℝ))).prod
        ((exponentialInterarrivalMeasure rate).prod
          (exponentialInterarrivalMeasure (1 : ℝ))) := by rfl

/-- The corresponding external-state/future-input factorization on the
actual stationary marked-Poisson suspension carrier. -/
def stationaryPoissonWorkFutureExternalFactors
    (z : GoodSuspensionState × (ℤ → ℝ)) :
    (((ℕ → ℝ) × ℝ) × (ℕ → ℝ)) × ((ℕ → ℝ) × (ℕ → ℝ)) :=
  equilibriumFutureExternalFactors (stationaryPoissonWorkToEquilibrium z)

theorem measurable_stationaryPoissonWorkFutureExternalFactors :
    Measurable stationaryPoissonWorkFutureExternalFactors := by
  exact measurable_equilibriumFutureExternalFactors.comp
    measurable_stationaryPoissonWorkToEquilibrium

/-- The actual stationary marked-Poisson carrier factors into external data
and an independent literal future arrival/work input. -/
theorem map_stationaryPoissonWorkFutureExternalFactors
    {rate : ℝ} (hrate : 0 < rate) :
    Measure.map stationaryPoissonWorkFutureExternalFactors
      (stationaryPoissonWorkMeasure rate) =
      (((exponentialInterarrivalMeasure rate).prod (expMeasure (1 : ℝ))).prod
        (exponentialInterarrivalMeasure (1 : ℝ))).prod
      ((exponentialInterarrivalMeasure rate).prod
        (exponentialInterarrivalMeasure (1 : ℝ))) := by
  change Measure.map
      (equilibriumFutureExternalFactors ∘ stationaryPoissonWorkToEquilibrium)
      (stationaryPoissonWorkMeasure rate) = _
  rw [← Measure.map_map measurable_equilibriumFutureExternalFactors
    measurable_stationaryPoissonWorkToEquilibrium,
    stationaryPoissonWorkToEquilibrium_measurePreserving hrate |>.map_eq,
    map_equilibriumFutureExternalFactors hrate]

/-- Package the two independent future coordinate paths into the literal IID
stream of arrival-gap/work pairs. -/
def equilibriumFutureExternalIidFactors
    (z : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℤ → ℝ)) :
    (((ℕ → ℝ) × ℝ) × (ℕ → ℝ)) × (ℕ → (ℝ × ℝ)) :=
  let q := equilibriumFutureExternalFactors z
  (q.1, IIDStream.zip q.2)

theorem measurable_equilibriumFutureExternalIidFactors :
    Measurable equilibriumFutureExternalIidFactors := by
  exact (measurable_id.prodMap IIDStream.measurable_zip).comp
    measurable_equilibriumFutureExternalFactors

/-- Exact state-plus-IID factorization of an equilibrium marked Poisson
input.  The IID coordinate law is the product of the displayed arrival-gap
and work-mark laws. -/
theorem map_equilibriumFutureExternalIidFactors
    {rate : ℝ} (hrate : 0 < rate) :
    Measure.map equilibriumFutureExternalIidFactors
      ((equilibriumTwoSidedBaseMeasure rate).prod
        (twoSidedInterarrivalMeasure (1 : ℝ))) =
      (((exponentialInterarrivalMeasure rate).prod (expMeasure (1 : ℝ))).prod
        (exponentialInterarrivalMeasure (1 : ℝ))).prod
      (IIDStream.measure
        ((expMeasure rate).prod (expMeasure (1 : ℝ)))) := by
  let μa : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  let μg : Measure ℝ := expMeasure rate
  let μc : Measure ℝ := expMeasure (1 : ℝ)
  let μd : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure (1 : ℝ)
  letI : IsProbabilityMeasure μa := by
    simpa [μa] using isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure μg := by
    simpa [μg] using isProbabilityMeasure_expMeasure hrate
  letI : IsProbabilityMeasure μc := by
    simpa [μc] using isProbabilityMeasure_expMeasure (by norm_num : 0 < (1 : ℝ))
  letI : IsProbabilityMeasure μd := by
    simpa [μd] using isProbabilityMeasure_exponentialInterarrivalMeasure
      (by norm_num : 0 < (1 : ℝ))
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  letI : IsProbabilityMeasure ((μa.prod μc).prod μd) := by infer_instance
  have hzip : Measure.map IIDStream.zip (μa.prod μd) =
      IIDStream.measure (μg.prod μc) := by
    simpa [μa, μg, μc, μd, IIDStream.measure, exponentialInterarrivalMeasure] using
      (IIDStream.zip_hasLaw μg μc).map_eq
  change Measure.map equilibriumFutureExternalIidFactors
      ((μa.prod μa).prod (twoSidedInterarrivalMeasure (1 : ℝ))) = _
  calc
    Measure.map equilibriumFutureExternalIidFactors
        ((μa.prod μa).prod (twoSidedInterarrivalMeasure (1 : ℝ))) =
        Measure.map (Prod.map id IIDStream.zip)
          (Measure.map equilibriumFutureExternalFactors
            ((μa.prod μa).prod (twoSidedInterarrivalMeasure (1 : ℝ)))) := by
          symm
          rw [Measure.map_map (measurable_id.prodMap IIDStream.measurable_zip)
            measurable_equilibriumFutureExternalFactors]
          rfl
    _ = Measure.map (Prod.map id IIDStream.zip)
          (((μa.prod μc).prod μd).prod (μa.prod μd)) := by
          congr 1
          simpa [μa, μc, μd, equilibriumTwoSidedBaseMeasure] using
            (map_equilibriumFutureExternalFactors hrate)
    _ = ((μa.prod μc).prod μd).prod (IIDStream.measure (μg.prod μc)) := by
          rw [← Measure.map_prod_map _ _ measurable_id IIDStream.measurable_zip,
            Measure.map_id, hzip]
    _ = (((exponentialInterarrivalMeasure rate).prod (expMeasure (1 : ℝ))).prod
          (exponentialInterarrivalMeasure (1 : ℝ))).prod
        (IIDStream.measure ((expMeasure rate).prod (expMeasure (1 : ℝ)))) := by rfl

/-- The equilibrium state-plus-IID factor map is measure preserving. -/
theorem equilibriumFutureExternalIidFactors_measurePreserving
    {rate : ℝ} (hrate : 0 < rate) :
    MeasurePreserving equilibriumFutureExternalIidFactors
      ((equilibriumTwoSidedBaseMeasure rate).prod
        (twoSidedInterarrivalMeasure (1 : ℝ)))
      (
        (((exponentialInterarrivalMeasure rate).prod (expMeasure (1 : ℝ))).prod
          (exponentialInterarrivalMeasure (1 : ℝ))).prod
        (IIDStream.measure ((expMeasure rate).prod (expMeasure (1 : ℝ))))
      ) := by
  exact ⟨measurable_equilibriumFutureExternalIidFactors,
    map_equilibriumFutureExternalIidFactors hrate⟩

/-- State-plus-IID factors on the actual stationary marked-Poisson suspension
carrier. -/
def stationaryPoissonWorkFutureExternalIidFactors
    (z : GoodSuspensionState × (ℤ → ℝ)) :
    (((ℕ → ℝ) × ℝ) × (ℕ → ℝ)) × (ℕ → (ℝ × ℝ)) :=
  equilibriumFutureExternalIidFactors (stationaryPoissonWorkToEquilibrium z)

theorem measurable_stationaryPoissonWorkFutureExternalIidFactors :
    Measurable stationaryPoissonWorkFutureExternalIidFactors := by
  exact measurable_equilibriumFutureExternalIidFactors.comp
    measurable_stationaryPoissonWorkToEquilibrium

/-- The literal stationary marked-Poisson input consists of independent
external data and an IID future sequence of arrival-gap/work pairs. -/
theorem map_stationaryPoissonWorkFutureExternalIidFactors
    {rate : ℝ} (hrate : 0 < rate) :
    Measure.map stationaryPoissonWorkFutureExternalIidFactors
      (stationaryPoissonWorkMeasure rate) =
      (((exponentialInterarrivalMeasure rate).prod (expMeasure (1 : ℝ))).prod
        (exponentialInterarrivalMeasure (1 : ℝ))).prod
      (IIDStream.measure
        ((expMeasure rate).prod (expMeasure (1 : ℝ)))) := by
  change Measure.map
      (equilibriumFutureExternalIidFactors ∘ stationaryPoissonWorkToEquilibrium)
      (stationaryPoissonWorkMeasure rate) = _
  rw [← Measure.map_map measurable_equilibriumFutureExternalIidFactors
    measurable_stationaryPoissonWorkToEquilibrium,
    stationaryPoissonWorkToEquilibrium_measurePreserving hrate |>.map_eq,
    map_equilibriumFutureExternalIidFactors hrate]

/-- The stationary state-plus-IID factor map is measure preserving. -/
theorem stationaryPoissonWorkFutureExternalIidFactors_measurePreserving
    {rate : ℝ} (hrate : 0 < rate) :
    MeasurePreserving stationaryPoissonWorkFutureExternalIidFactors
      (stationaryPoissonWorkMeasure rate)
      (
        (((exponentialInterarrivalMeasure rate).prod (expMeasure (1 : ℝ))).prod
          (exponentialInterarrivalMeasure (1 : ℝ))).prod
        (IIDStream.measure ((expMeasure rate).prod (expMeasure (1 : ℝ))))
      ) := by
  exact ⟨measurable_stationaryPoissonWorkFutureExternalIidFactors,
    map_stationaryPoissonWorkFutureExternalIidFactors hrate⟩

/-- Split one stationary marked-Poisson coordinate so that its full future
arrival-gap path is retained as external data and only its future work marks
remain as the IID stream. -/
def stateStationaryPoissonWorkFutureExternalMarkFactors
    {σ : Type*} [MeasurableSpace σ]
    (x : σ × (GoodSuspensionState × (ℤ → ℝ))) :
    ((σ × (((ℕ → ℝ) × ℝ) × (ℕ → ℝ))) × (ℕ → ℝ)) × (ℕ → ℝ) :=
  let q := stationaryPoissonWorkFutureExternalFactors x.2
  (((x.1, q.1), q.2.1), q.2.2)

theorem measurable_stateStationaryPoissonWorkFutureExternalMarkFactors
    {σ : Type*} [MeasurableSpace σ] :
    Measurable (stateStationaryPoissonWorkFutureExternalMarkFactors (σ := σ)) := by
  let EType : Type := ((ℕ → ℝ) × ℝ) × (ℕ → ℝ)
  let Stream : Type := ℕ → ℝ
  let reassociate₁ : σ × (EType × (Stream × Stream)) ≃ᵐ
      (σ × EType) × (Stream × Stream) :=
    (MeasurableEquiv.prodAssoc :
      (σ × EType) × (Stream × Stream) ≃ᵐ σ × (EType × (Stream × Stream))).symm
  let reassociate₂ : (σ × EType) × (Stream × Stream) ≃ᵐ
      ((σ × EType) × Stream) × Stream :=
    (MeasurableEquiv.prodAssoc :
      ((σ × EType) × Stream) × Stream ≃ᵐ (σ × EType) × (Stream × Stream)).symm
  exact reassociate₂.measurable.comp
    (reassociate₁.measurable.comp
      (measurable_id.prodMap measurable_stationaryPoissonWorkFutureExternalFactors))

/-- Factoring a stationary marked-Poisson coordinate leaves all arrival
timing external and exposes an IID future work-mark stream. -/
theorem map_stateStationaryPoissonWorkFutureExternalMarkFactors
    {σ : Type*} [MeasurableSpace σ] (ρ : Measure σ)
    [IsProbabilityMeasure ρ] {rate : ℝ} (hrate : 0 < rate) :
    Measure.map (stateStationaryPoissonWorkFutureExternalMarkFactors (σ := σ))
      (ρ.prod (stationaryPoissonWorkMeasure rate)) =
      ((ρ.prod
        (((exponentialInterarrivalMeasure rate).prod (expMeasure (1 : ℝ))).prod
          (exponentialInterarrivalMeasure (1 : ℝ)))).prod
        (exponentialInterarrivalMeasure rate)).prod
        (exponentialInterarrivalMeasure (1 : ℝ)) := by
  let E : Measure (((ℕ → ℝ) × ℝ) × (ℕ → ℝ)) :=
    ((exponentialInterarrivalMeasure rate).prod (expMeasure (1 : ℝ))).prod
      (exponentialInterarrivalMeasure (1 : ℝ))
  let G : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  let M : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure (1 : ℝ)
  letI : IsProbabilityMeasure (stationaryPoissonWorkMeasure rate) :=
    isProbabilityMeasure_stationaryPoissonWorkMeasure hrate
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  letI : IsProbabilityMeasure E := by
    dsimp [E]
    infer_instance
  letI : IsProbabilityMeasure G := by
    dsimp [G]
    exact isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure M := by
    dsimp [M]
    exact isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  let EType : Type := ((ℕ → ℝ) × ℝ) × (ℕ → ℝ)
  let Stream : Type := ℕ → ℝ
  let reassociate₁ : σ × (EType × (Stream × Stream)) ≃ᵐ
      (σ × EType) × (Stream × Stream) :=
    (MeasurableEquiv.prodAssoc :
      (σ × EType) × (Stream × Stream) ≃ᵐ σ × (EType × (Stream × Stream))).symm
  let reassociate₂ : (σ × EType) × (Stream × Stream) ≃ᵐ
      ((σ × EType) × Stream) × Stream :=
    (MeasurableEquiv.prodAssoc :
      ((σ × EType) × Stream) × Stream ≃ᵐ (σ × EType) × (Stream × Stream)).symm
  have hfactor :
      Measure.map (Prod.map id stationaryPoissonWorkFutureExternalFactors)
        (ρ.prod (stationaryPoissonWorkMeasure rate)) = ρ.prod (E.prod (G.prod M)) := by
    rw [← Measure.map_prod_map _ _ measurable_id
      measurable_stationaryPoissonWorkFutureExternalFactors, Measure.map_id,
      map_stationaryPoissonWorkFutureExternalFactors hrate]
  change Measure.map (reassociate₂ ∘ reassociate₁ ∘
      Prod.map id stationaryPoissonWorkFutureExternalFactors)
    (ρ.prod (stationaryPoissonWorkMeasure rate)) = ((ρ.prod E).prod G).prod M
  calc
    Measure.map (reassociate₂ ∘ reassociate₁ ∘
        Prod.map id stationaryPoissonWorkFutureExternalFactors)
        (ρ.prod (stationaryPoissonWorkMeasure rate)) =
        Measure.map reassociate₂
          (Measure.map reassociate₁
            (Measure.map (Prod.map id stationaryPoissonWorkFutureExternalFactors)
              (ρ.prod (stationaryPoissonWorkMeasure rate)))) := by
            symm
            rw [Measure.map_map reassociate₂.measurable reassociate₁.measurable,
              Measure.map_map
                (reassociate₂.measurable.comp reassociate₁.measurable)
                (measurable_id.prodMap
                  measurable_stationaryPoissonWorkFutureExternalFactors)]
            rfl
    _ = Measure.map reassociate₂ (Measure.map reassociate₁
          (ρ.prod (E.prod (G.prod M)))) := by rw [hfactor]
    _ = Measure.map reassociate₂ ((ρ.prod E).prod (G.prod M)) := by
          exact congrArg (Measure.map reassociate₂)
            (measurePreserving_prodAssoc ρ E (G.prod M)).symm.map_eq
    _ = ((ρ.prod E).prod G).prod M := by
          exact (measurePreserving_prodAssoc (ρ.prod E) G M).symm.map_eq

/-- The external-timing/future-mark factor map is measure preserving. -/
theorem stateStationaryPoissonWorkFutureExternalMarkFactors_measurePreserving
    {σ : Type*} [MeasurableSpace σ] (ρ : Measure σ)
    [IsProbabilityMeasure ρ] {rate : ℝ} (hrate : 0 < rate) :
    MeasurePreserving
      (stateStationaryPoissonWorkFutureExternalMarkFactors (σ := σ))
      (ρ.prod (stationaryPoissonWorkMeasure rate))
      (((ρ.prod
        (((exponentialInterarrivalMeasure rate).prod (expMeasure (1 : ℝ))).prod
          (exponentialInterarrivalMeasure (1 : ℝ)))).prod
        (exponentialInterarrivalMeasure rate)).prod
        (exponentialInterarrivalMeasure (1 : ℝ))) := by
  exact ⟨measurable_stateStationaryPoissonWorkFutureExternalMarkFactors,
    map_stateStationaryPoissonWorkFutureExternalMarkFactors ρ hrate⟩

/-- Split one stationary marked-Poisson coordinate while retaining arbitrary
independent data as part of the external state. -/
def stateStationaryPoissonWorkFutureExternalIidFactors
    {σ : Type*} [MeasurableSpace σ]
    (x : σ × (GoodSuspensionState × (ℤ → ℝ))) :
    (σ × (((ℕ → ℝ) × ℝ) × (ℕ → ℝ))) × (ℕ → (ℝ × ℝ)) :=
  let q := stationaryPoissonWorkFutureExternalIidFactors x.2
  ((x.1, q.1), q.2)

theorem measurable_stateStationaryPoissonWorkFutureExternalIidFactors
    {σ : Type*} [MeasurableSpace σ] :
    Measurable (stateStationaryPoissonWorkFutureExternalIidFactors (σ := σ)) := by
  exact (MeasurableEquiv.prodAssoc.symm.measurable.comp
    (measurable_id.prodMap
      measurable_stationaryPoissonWorkFutureExternalIidFactors))

/-- Factoring one stationary marked-Poisson coordinate in a product carrier
leaves all pre-existing external data independent of its future IID input. -/
theorem map_stateStationaryPoissonWorkFutureExternalIidFactors
    {σ : Type*} [MeasurableSpace σ] (ρ : Measure σ)
    [IsProbabilityMeasure ρ] {rate : ℝ} (hrate : 0 < rate) :
    Measure.map (stateStationaryPoissonWorkFutureExternalIidFactors (σ := σ))
      (ρ.prod (stationaryPoissonWorkMeasure rate)) =
      (ρ.prod
        (((exponentialInterarrivalMeasure rate).prod (expMeasure (1 : ℝ))).prod
          (exponentialInterarrivalMeasure (1 : ℝ)))).prod
        (IIDStream.measure ((expMeasure rate).prod (expMeasure (1 : ℝ)))) := by
  let external : Measure (((ℕ → ℝ) × ℝ) × (ℕ → ℝ)) :=
    ((exponentialInterarrivalMeasure rate).prod (expMeasure (1 : ℝ))).prod
      (exponentialInterarrivalMeasure (1 : ℝ))
  let future : Measure (ℕ → (ℝ × ℝ)) :=
    IIDStream.measure ((expMeasure rate).prod (expMeasure (1 : ℝ)) )
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure hrate
  letI : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  letI : IsProbabilityMeasure (stationaryPoissonWorkMeasure rate) :=
    isProbabilityMeasure_stationaryPoissonWorkMeasure hrate
  letI : IsProbabilityMeasure external := by
    dsimp [external]
    infer_instance
  letI : IsProbabilityMeasure future := by
    dsimp [future, IIDStream.measure]
    infer_instance
  calc
    Measure.map (stateStationaryPoissonWorkFutureExternalIidFactors (σ := σ))
        (ρ.prod (stationaryPoissonWorkMeasure rate)) =
        Measure.map (MeasurableEquiv.prodAssoc.symm :
          σ × (((ℕ → ℝ) × ℝ) × (ℕ → ℝ)) × (ℕ → (ℝ × ℝ)) →
            (σ × (((ℕ → ℝ) × ℝ) × (ℕ → ℝ))) × (ℕ → (ℝ × ℝ)))
          (Measure.map (Prod.map id stationaryPoissonWorkFutureExternalIidFactors)
            (ρ.prod (stationaryPoissonWorkMeasure rate))) := by
          symm
          rw [Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
            (measurable_id.prodMap
              measurable_stationaryPoissonWorkFutureExternalIidFactors)]
          rfl
    _ = Measure.map (MeasurableEquiv.prodAssoc.symm :
          σ × (((ℕ → ℝ) × ℝ) × (ℕ → ℝ)) × (ℕ → (ℝ × ℝ)) →
            (σ × (((ℕ → ℝ) × ℝ) × (ℕ → ℝ))) × (ℕ → (ℝ × ℝ)))
          (ρ.prod (external.prod future)) := by
          rw [← Measure.map_prod_map _ _ measurable_id
            measurable_stationaryPoissonWorkFutureExternalIidFactors,
            Measure.map_id,
            map_stationaryPoissonWorkFutureExternalIidFactors hrate]
    _ = (ρ.prod external).prod future := by
          exact (measurePreserving_prodAssoc ρ external future).symm.map_eq
    _ =
        (ρ.prod
          (((exponentialInterarrivalMeasure rate).prod (expMeasure (1 : ℝ))).prod
            (exponentialInterarrivalMeasure (1 : ℝ)))).prod
          (IIDStream.measure ((expMeasure rate).prod (expMeasure (1 : ℝ)))) := by rfl

/-- The arbitrary-state extension of the stationary factor map is measure
preserving. -/
theorem stateStationaryPoissonWorkFutureExternalIidFactors_measurePreserving
    {σ : Type*} [MeasurableSpace σ] (ρ : Measure σ)
    [IsProbabilityMeasure ρ] {rate : ℝ} (hrate : 0 < rate) :
    MeasurePreserving
      (stateStationaryPoissonWorkFutureExternalIidFactors (σ := σ))
      (ρ.prod (stationaryPoissonWorkMeasure rate))
      (
        (ρ.prod
          (((exponentialInterarrivalMeasure rate).prod (expMeasure (1 : ℝ))).prod
            (exponentialInterarrivalMeasure (1 : ℝ)))).prod
          (IIDStream.measure ((expMeasure rate).prod (expMeasure (1 : ℝ))))
      ) := by
  exact ⟨measurable_stateStationaryPoissonWorkFutureExternalIidFactors,
    map_stateStationaryPoissonWorkFutureExternalIidFactors ρ hrate⟩

private def externalFutureWorkGapReorder
    {β γ δ : Type*} (x : β × (γ × δ)) : (β × δ) × γ :=
  ((x.1, x.2.2), x.2.1)

private theorem measurable_externalFutureWorkGapReorder
    {β γ δ : Type*} [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ] :
    Measurable (@externalFutureWorkGapReorder β γ δ) := by
  exact ((measurable_fst).prodMk
    (measurable_snd.comp measurable_snd)).prodMk
      (measurable_fst.comp measurable_snd)

private theorem map_externalFutureWorkGapReorder
    {β γ δ : Type*} [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    (ν : Measure β) (μg : Measure γ) (μw : Measure δ)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μg] [IsProbabilityMeasure μw] :
    Measure.map externalFutureWorkGapReorder (ν.prod (μg.prod μw)) =
      (ν.prod μw).prod μg := by
  let h₁ : MeasurePreserving
      (MeasurableEquiv.prodAssoc.symm : β × (γ × δ) ≃ᵐ (β × γ) × δ)
      (ν.prod (μg.prod μw)) ((ν.prod μg).prod μw) :=
    (measurePreserving_prodAssoc ν μg μw).symm
  let h₂ : MeasurePreserving
      (Prod.map Prod.swap id : (β × γ) × δ → (γ × β) × δ)
      ((ν.prod μg).prod μw) ((μg.prod ν).prod μw) :=
    (Measure.measurePreserving_swap (μ := ν) (ν := μg)).prod
      (MeasurePreserving.id μw)
  let h₃ : MeasurePreserving
      (MeasurableEquiv.prodAssoc : (γ × β) × δ ≃ᵐ γ × (β × δ))
      ((μg.prod ν).prod μw) (μg.prod (ν.prod μw)) :=
    measurePreserving_prodAssoc μg ν μw
  let h₄ : MeasurePreserving
      (Prod.swap : γ × (β × δ) → (β × δ) × γ)
      (μg.prod (ν.prod μw)) ((ν.prod μw).prod μg) :=
    Measure.measurePreserving_swap (μ := μg) (ν := ν.prod μw)
  let h := h₄.comp (h₃.comp (h₂.comp h₁))
  convert h.map_eq using 1

/-- The stationary marked-Poisson data predating a deterministic future clock,
apart from the finite arrival history accumulated by that clock. -/
abbrev StationaryPoissonWorkFutureTimeSliceBase :=
  (((ℕ → ℝ) × ℝ) × (ℕ → ℝ)) × (ℕ → ℝ)

/-- The data of a stationary marked Poisson input exposed at a deterministic
future clock, excluding only the fresh residual arrival-gap tail. -/
abbrev StationaryPoissonWorkFutureTimeSliceExternal :=
  StationaryPoissonWorkFutureTimeSliceBase × (ℕ × (ℕ → ℝ))

/-- The law of the stationary marked-Poisson data that predates a deterministic
clock, apart from the clock's finite arrival history. -/
def stationaryPoissonWorkFutureTimeSliceBaseMeasure (rate : ℝ) :
    Measure StationaryPoissonWorkFutureTimeSliceBase :=
  (((exponentialInterarrivalMeasure rate).prod (expMeasure (1 : ℝ))).prod
    (exponentialInterarrivalMeasure (1 : ℝ))).prod
    (exponentialInterarrivalMeasure (1 : ℝ))

/-- Retain a stationary input's external data and entire future work stream,
then split its future arrival path at a deterministic clock into the complete
pre-clock history and a fresh residual tail. -/
def stationaryPoissonWorkFutureTimeSliceFactors
    (s : ℝ) (z : GoodSuspensionState × (ℤ → ℝ)) :
    StationaryPoissonWorkFutureTimeSliceExternal × (ℕ → ℝ) :=
  let q := stationaryPoissonWorkFutureExternalFactors z
  let r := externalFutureWorkGapReorder q
  ((r.1, canonicalRenewalPastHistory s r.2), residualTail s r.2)

theorem measurable_stationaryPoissonWorkFutureTimeSliceFactors (s : ℝ) :
    Measurable (stationaryPoissonWorkFutureTimeSliceFactors s) := by
  let q := stationaryPoissonWorkFutureExternalFactors
  let r := externalFutureWorkGapReorder ∘ q
  have hr : Measurable r :=
    measurable_externalFutureWorkGapReorder.comp
      measurable_stationaryPoissonWorkFutureExternalFactors
  exact ((measurable_fst.comp hr).prodMk
    ((measurable_canonicalRenewalPastHistory s).comp (measurable_snd.comp hr))).prodMk
      ((measurable_residualTail s).comp (measurable_snd.comp hr))

/-- The history and residual components of a stationary deterministic-time
factor reconstruct its complete forward interarrival path. -/
theorem reconstructCanonicalRenewalPath_stationaryPoissonWorkFutureTimeSliceFactors
    (s : ℝ) (z : GoodSuspensionState × (ℤ → ℝ)) :
    reconstructCanonicalRenewalPath s
      (stationaryPoissonWorkFutureTimeSliceFactors s z).1.2
      (stationaryPoissonWorkFutureTimeSliceFactors s z).2 =
      (externalFutureWorkGapReorder (stationaryPoissonWorkFutureExternalFactors z)).2 := by
  simpa [stationaryPoissonWorkFutureTimeSliceFactors] using
    (reconstructCanonicalRenewalPath_apply_timeSlice s
      (externalFutureWorkGapReorder (stationaryPoissonWorkFutureExternalFactors z)).2)

/-- Reconstructing the split forward gap path recovers the forward
equilibrium arrival coordinate. -/
theorem reconstructCanonicalRenewalPath_stationaryPoissonWorkFutureTimeSliceFactors_eqFuture
    (s : ℝ) (z : GoodSuspensionState × (ℤ → ℝ)) :
    reconstructCanonicalRenewalPath s
      (stationaryPoissonWorkFutureTimeSliceFactors s z).1.2
      (stationaryPoissonWorkFutureTimeSliceFactors s z).2 =
      (stationaryPoissonWorkToEquilibrium z).1.1 := by
  rw [reconstructCanonicalRenewalPath_stationaryPoissonWorkFutureTimeSliceFactors]
  rfl

/-- The renewal count of the fresh tail at a deterministic time slice is the
literal count increment of the original stationary forward arrival path.
This is a pointwise renewal identity on the good suspension carrier. -/
theorem canonicalRenewalCount_stationaryPoissonWorkFutureTimeSliceFactors_eq_increment
    (s h : ℝ) (hh : 0 ≤ h) (z : GoodSuspensionState × (ℤ → ℝ)) :
    canonicalRenewalCount h (stationaryPoissonWorkFutureTimeSliceFactors s z).2 =
      canonicalRenewalCount (s + h) (stationaryPoissonWorkToEquilibrium z).1.1 -
        canonicalRenewalCount s (stationaryPoissonWorkToEquilibrium z).1.1 := by
  let ω := (stationaryPoissonWorkToEquilibrium z).1.1
  change canonicalRenewalCount h (residualTail s ω) =
    canonicalRenewalCount (s + h) ω - canonicalRenewalCount s ω
  have hdiv : Filter.Tendsto (fun n : ℕ => arrivalTime n ω)
      Filter.atTop Filter.atTop := by
    simpa [ω, stationaryPoissonWorkToEquilibrium] using
      tendsto_arrivalTime_suspensionToEquilibrium_future_of_goodSuspension z.1
  have hS : ∃ n : ℕ, s < arrivalTime n ω :=
    (hdiv.eventually_gt_atTop s).exists
  have hSH : ∃ n : ℕ, s + h < arrivalTime n ω :=
    (hdiv.eventually_gt_atTop (s + h)).exists
  have hTail : ∃ m : ℕ, h < arrivalTime m (residualTail s ω) :=
    exists_residualTail_arrival_gt_of_tendsto s h ω hdiv
  have hadd := canonicalRenewalCount_add_eq_residualTailCount s h hh ω hS hSH hTail
  omega

/-- The time-slice external data retains the equilibrium-coordinate arrival
history that precedes the origin. -/
theorem stationaryPoissonWorkFutureTimeSliceFactors_pastEquilibrium
    (s : ℝ) (z : GoodSuspensionState × (ℤ → ℝ)) :
    (stationaryPoissonWorkFutureTimeSliceFactors s z).1.1.1.1.1 =
      (stationaryPoissonWorkToEquilibrium z).1.2 := by
  rfl

/-- The time-slice external data retains the service mark at the origin. -/
theorem stationaryPoissonWorkFutureTimeSliceFactors_originWork
    (s : ℝ) (z : GoodSuspensionState × (ℤ → ℝ)) :
    (stationaryPoissonWorkFutureTimeSliceFactors s z).1.1.1.1.2 =
      (twoSidedHeadPositiveNegative z.2).1.1 := by
  rfl

/-- The time-slice external data retains all service marks before the
origin. -/
theorem stationaryPoissonWorkFutureTimeSliceFactors_pastWork
    (s : ℝ) (z : GoodSuspensionState × (ℤ → ℝ)) :
    (stationaryPoissonWorkFutureTimeSliceFactors s z).1.1.1.2 =
      (twoSidedHeadPositiveNegative z.2).2 := by
  rfl

/-- The time-slice external data retains the strictly future service-mark
stream. -/
theorem stationaryPoissonWorkFutureTimeSliceFactors_futureWork
    (s : ℝ) (z : GoodSuspensionState × (ℤ → ℝ)) :
    (stationaryPoissonWorkFutureTimeSliceFactors s z).1.1.2 =
      (twoSidedHeadPositiveNegative z.2).1.2 := by
  rfl

/-- At every nonnegative deterministic clock, a stationary marked Poisson
input factors into all data already exposed by that clock and a fresh future
arrival-gap tail. -/
theorem map_stationaryPoissonWorkFutureTimeSliceFactors
    {rate s : ℝ} (hrate : 0 < rate) (hs : 0 ≤ s) :
    Measure.map (stationaryPoissonWorkFutureTimeSliceFactors s)
      (stationaryPoissonWorkMeasure rate) =
      (((((exponentialInterarrivalMeasure rate).prod (expMeasure (1 : ℝ))).prod
        (exponentialInterarrivalMeasure (1 : ℝ))).prod
        (exponentialInterarrivalMeasure (1 : ℝ))).prod
        (Measure.map (canonicalRenewalPastHistory s)
          (exponentialInterarrivalMeasure rate))).prod
        (exponentialInterarrivalMeasure rate) := by
  let E : Measure (((ℕ → ℝ) × ℝ) × (ℕ → ℝ)) :=
    ((exponentialInterarrivalMeasure rate).prod (expMeasure (1 : ℝ))).prod
      (exponentialInterarrivalMeasure (1 : ℝ))
  let G : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  let W : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure (1 : ℝ)
  let H : (ℕ → ℝ) → ℕ × (ℕ → ℝ) := canonicalRenewalPastHistory s
  let q := stationaryPoissonWorkFutureExternalFactors
  let r : (((ℕ → ℝ) × ℝ) × (ℕ → ℝ)) × ((ℕ → ℝ) × (ℕ → ℝ)) →
      ((((ℕ → ℝ) × ℝ) × (ℕ → ℝ)) × (ℕ → ℝ)) × (ℕ → ℝ) :=
    externalFutureWorkGapReorder
  let f : ((((ℕ → ℝ) × ℝ) × (ℕ → ℝ)) × (ℕ → ℝ)) × (ℕ → ℝ) →
      (((((ℕ → ℝ) × ℝ) × (ℕ → ℝ)) × (ℕ → ℝ)) × (ℕ × (ℕ → ℝ))) × (ℕ → ℝ) :=
    fun x => ((x.1, H x.2), residualTail s x.2)
  letI : IsProbabilityMeasure G := by
    simpa [G] using isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure W := by
    simpa [W] using isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  letI : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  letI : IsProbabilityMeasure E := by
    dsimp [E]
    infer_instance
  letI : IsProbabilityMeasure (E.prod W) := by infer_instance
  have hq : Measurable q := measurable_stationaryPoissonWorkFutureExternalFactors
  have hr : Measurable r := measurable_externalFutureWorkGapReorder
  have hf : Measurable f := by
    exact ((measurable_fst).prodMk
      ((measurable_canonicalRenewalPastHistory s).comp measurable_snd)).prodMk
        ((measurable_residualTail s).comp measurable_snd)
  have hslice := map_external_canonicalRenewalPastHistory_residualTail
    (ν := E.prod W) hrate hs
  change Measure.map (f ∘ r ∘ q) (stationaryPoissonWorkMeasure rate) =
    ((E.prod W).prod (Measure.map H G)).prod G
  rw [← Measure.map_map hf (hr.comp hq), ← Measure.map_map hr hq,
    map_stationaryPoissonWorkFutureExternalFactors hrate]
  rw [map_externalFutureWorkGapReorder E G W]
  simpa [f, H, G] using hslice

/-- Retain arbitrary independent external data while exposing a stationary
marked Poisson input through a deterministic clock and its fresh residual
arrival-gap tail. -/
def externalStationaryPoissonWorkFutureTimeSliceFactors
    {β : Type*} (s : ℝ) (z : β × (GoodSuspensionState × (ℤ → ℝ))) :
    ((β × StationaryPoissonWorkFutureTimeSliceBase) × (ℕ × (ℕ → ℝ))) × (ℕ → ℝ) :=
  let q := stationaryPoissonWorkFutureTimeSliceFactors s z.2
  (((z.1, q.1.1), q.1.2), q.2)

/-- Adjoining arbitrary external data does not alter the exact renewal-count
increment represented by the fresh time-slice tail. -/
theorem canonicalRenewalCount_externalStationaryPoissonWorkFutureTimeSliceFactors_eq_increment
    {β : Type*} (s h : ℝ) (hh : 0 ≤ h)
    (z : β × (GoodSuspensionState × (ℤ → ℝ))) :
    canonicalRenewalCount h (externalStationaryPoissonWorkFutureTimeSliceFactors s z).2 =
      canonicalRenewalCount (s + h) (stationaryPoissonWorkToEquilibrium z.2).1.1 -
        canonicalRenewalCount s (stationaryPoissonWorkToEquilibrium z.2).1.1 := by
  change canonicalRenewalCount h (stationaryPoissonWorkFutureTimeSliceFactors s z.2).2 =
    canonicalRenewalCount (s + h) (stationaryPoissonWorkToEquilibrium z.2).1.1 -
      canonicalRenewalCount s (stationaryPoissonWorkToEquilibrium z.2).1.1
  exact canonicalRenewalCount_stationaryPoissonWorkFutureTimeSliceFactors_eq_increment
    s h hh z.2

theorem measurable_externalStationaryPoissonWorkFutureTimeSliceFactors
    {β : Type*} [MeasurableSpace β] (s : ℝ) :
    Measurable (externalStationaryPoissonWorkFutureTimeSliceFactors (β := β) s) := by
  let q := stationaryPoissonWorkFutureTimeSliceFactors s
  have hq : Measurable q := measurable_stationaryPoissonWorkFutureTimeSliceFactors s
  exact (((measurable_fst.prodMk
    ((measurable_fst.comp (measurable_fst.comp measurable_snd)))).prodMk
      (measurable_snd.comp (measurable_fst.comp measurable_snd))).prodMk
        (measurable_snd.comp measurable_snd)).comp
      (measurable_id.prodMap hq)

/-- Exact law of the external deterministic-time factor.  It exposes an
arbitrary independent state, the complete clock history, and a fresh residual
tail as an explicit product law. -/
theorem map_externalStationaryPoissonWorkFutureTimeSliceFactors
    {β : Type*} [MeasurableSpace β] (ν : Measure β) [IsProbabilityMeasure ν]
    {rate s : ℝ} (hrate : 0 < rate) (hs : 0 ≤ s) :
    Measure.map (externalStationaryPoissonWorkFutureTimeSliceFactors (β := β) s)
      (ν.prod (stationaryPoissonWorkMeasure rate)) =
      ((ν.prod (stationaryPoissonWorkFutureTimeSliceBaseMeasure rate)).prod
        (Measure.map (canonicalRenewalPastHistory s)
          (exponentialInterarrivalMeasure rate))).prod
        (exponentialInterarrivalMeasure rate) := by
  let B : Measure StationaryPoissonWorkFutureTimeSliceBase :=
    stationaryPoissonWorkFutureTimeSliceBaseMeasure rate
  let G : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  let H : (ℕ → ℝ) → ℕ × (ℕ → ℝ) := canonicalRenewalPastHistory s
  let F := stationaryPoissonWorkFutureTimeSliceFactors s
  let Q : β × (GoodSuspensionState × (ℤ → ℝ)) →
      β × (StationaryPoissonWorkFutureTimeSliceExternal × (ℕ → ℝ)) :=
    Prod.map id F
  let r : β × ((StationaryPoissonWorkFutureTimeSliceExternal) × (ℕ → ℝ)) →
      ((β × StationaryPoissonWorkFutureTimeSliceBase) × (ℕ × (ℕ → ℝ))) × (ℕ → ℝ) :=
    fun x => (((x.1, x.2.1.1), x.2.1.2), x.2.2)
  let target : Measure
      (((β × StationaryPoissonWorkFutureTimeSliceBase) × (ℕ × (ℕ → ℝ))) × (ℕ → ℝ)) :=
    ((ν.prod B).prod (Measure.map H G)).prod G
  letI : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  letI : IsProbabilityMeasure G := by
    simpa [G] using isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure B := by
    simp [B, stationaryPoissonWorkFutureTimeSliceBaseMeasure]
    infer_instance
  letI : IsProbabilityMeasure (stationaryPoissonWorkMeasure rate) :=
    isProbabilityMeasure_stationaryPoissonWorkMeasure hrate
  letI : IsProbabilityMeasure (Measure.map H G) :=
    Measure.isProbabilityMeasure_map (measurable_canonicalRenewalPastHistory s).aemeasurable
  have hF : Measurable F := measurable_stationaryPoissonWorkFutureTimeSliceFactors s
  have hQ : Measurable Q := measurable_id.prodMap hF
  have hr : Measurable r := by
    exact (((measurable_fst.prodMk
      (measurable_fst.comp (measurable_fst.comp measurable_snd))).prodMk
        (measurable_snd.comp (measurable_fst.comp measurable_snd))).prodMk
          (measurable_snd.comp measurable_snd))
  have hQmap : Measure.map Q (ν.prod (stationaryPoissonWorkMeasure rate)) =
      ν.prod ((B.prod (Measure.map H G)).prod G) := by
    rw [← Measure.map_prod_map ν (stationaryPoissonWorkMeasure rate)
      measurable_id hF, Measure.map_id,
      map_stationaryPoissonWorkFutureTimeSliceFactors hrate hs]
    rfl
  have hrmap : Measure.map r (ν.prod ((B.prod (Measure.map H G)).prod G)) = target := by
    let h₁ : MeasurePreserving
        (MeasurableEquiv.prodAssoc.symm :
          β × ((StationaryPoissonWorkFutureTimeSliceBase × (ℕ × (ℕ → ℝ))) × (ℕ → ℝ)) ≃ᵐ
            (β × (StationaryPoissonWorkFutureTimeSliceBase × (ℕ × (ℕ → ℝ)))) × (ℕ → ℝ))
        (ν.prod ((B.prod (Measure.map H G)).prod G))
        ((ν.prod (B.prod (Measure.map H G))).prod G) :=
      (measurePreserving_prodAssoc ν (B.prod (Measure.map H G)) G).symm
    let h₂ : MeasurePreserving
        (Prod.map MeasurableEquiv.prodAssoc.symm id :
          (β × (StationaryPoissonWorkFutureTimeSliceBase × (ℕ × (ℕ → ℝ)))) × (ℕ → ℝ) →
            ((β × StationaryPoissonWorkFutureTimeSliceBase) × (ℕ × (ℕ → ℝ))) × (ℕ → ℝ))
        ((ν.prod (B.prod (Measure.map H G))).prod G)
        (((ν.prod B).prod (Measure.map H G)).prod G) :=
      ((measurePreserving_prodAssoc ν B (Measure.map H G)).symm).prod
        (MeasurePreserving.id G)
    let h := h₂.comp h₁
    change Measure.map r (ν.prod ((B.prod (Measure.map H G)).prod G)) = target
    convert h.map_eq using 1
  change Measure.map (r ∘ Q) (ν.prod (stationaryPoissonWorkMeasure rate)) = target
  rw [← Measure.map_map hr hQ, hQmap, hrmap]

/-- Deterministic-interval compensation remains valid after adjoining an
arbitrary independent external state to a stationary marked Poisson input. -/
theorem integral_externalStationaryPoissonWorkFutureTimeSliceSelector_mul_arrivalCount
    {β : Type*} [MeasurableSpace β] (ν : Measure β) [IsProbabilityMeasure ν]
    {rate s h : ℝ} (hrate : 0 < rate) (hs : 0 ≤ s) (hh : 0 ≤ h)
    (f : (β × StationaryPoissonWorkFutureTimeSliceBase) × (ℕ × (ℕ → ℝ)) → ℝ)
    (hf : Measurable f) :
    ∫ z, f (externalStationaryPoissonWorkFutureTimeSliceFactors (β := β) s z).1 *
        (canonicalRenewalCount h
          (externalStationaryPoissonWorkFutureTimeSliceFactors (β := β) s z).2 : ℝ)
        ∂(ν.prod (stationaryPoissonWorkMeasure rate)) =
      (∫ z, f (externalStationaryPoissonWorkFutureTimeSliceFactors (β := β) s z).1
        ∂(ν.prod (stationaryPoissonWorkMeasure rate))) * (rate * h) := by
  let B : Measure StationaryPoissonWorkFutureTimeSliceBase :=
    stationaryPoissonWorkFutureTimeSliceBaseMeasure rate
  let G : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  let H : (ℕ → ℝ) → ℕ × (ℕ → ℝ) := canonicalRenewalPastHistory s
  let R : (ℕ → ℝ) → ℕ → ℝ := residualTail s
  let F := externalStationaryPoissonWorkFutureTimeSliceFactors (β := β) s
  let T : ((β × StationaryPoissonWorkFutureTimeSliceBase) × (ℕ → ℝ)) →
      ((β × StationaryPoissonWorkFutureTimeSliceBase) × (ℕ × (ℕ → ℝ))) × (ℕ → ℝ) :=
    fun z => ((z.1, H z.2), R z.2)
  let target : Measure
      (((β × StationaryPoissonWorkFutureTimeSliceBase) × (ℕ × (ℕ → ℝ))) × (ℕ → ℝ)) :=
    ((ν.prod B).prod (Measure.map H G)).prod G
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  letI : IsProbabilityMeasure G := by
    simpa [G] using isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure B := by
    simp [B, stationaryPoissonWorkFutureTimeSliceBaseMeasure]
    infer_instance
  letI : IsProbabilityMeasure (ν.prod B) := by infer_instance
  letI : IsProbabilityMeasure (stationaryPoissonWorkMeasure rate) :=
    isProbabilityMeasure_stationaryPoissonWorkMeasure hrate
  have hF : Measurable F :=
    measurable_externalStationaryPoissonWorkFutureTimeSliceFactors s
  have hT : Measurable T := by
    exact ((measurable_fst.prodMk
      ((measurable_canonicalRenewalPastHistory s).comp measurable_snd))).prodMk
        ((measurable_residualTail s).comp measurable_snd)
  have hFmap : Measure.map F (ν.prod (stationaryPoissonWorkMeasure rate)) = target := by
    simpa [F, target, B, G, H] using
      map_externalStationaryPoissonWorkFutureTimeSliceFactors ν hrate hs
  have hTmap : Measure.map T ((ν.prod B).prod G) = target := by
    simpa [T, target, H, R, G] using
      (map_external_canonicalRenewalPastHistory_residualTail (ν := ν.prod B) hrate hs)
  let hF_law : ProbabilityTheory.HasLaw F target
      (ν.prod (stationaryPoissonWorkMeasure rate)) := ⟨hF.aemeasurable, hFmap⟩
  let hT_law : ProbabilityTheory.HasLaw T target ((ν.prod B).prod G) :=
    ⟨hT.aemeasurable, hTmap⟩
  have hincrement :
      (fun z : (β × StationaryPoissonWorkFutureTimeSliceBase) × (ℕ → ℝ) =>
        (canonicalRenewalCount h (R z.2) : ℝ)) =ᵐ[(ν.prod B).prod G]
        fun z =>
          ((canonicalRenewalCount (s + h) z.2 - canonicalRenewalCount s z.2 : ℕ) : ℝ) := by
    refine ae_of_ae_map (μ := (ν.prod B).prod G) (f := Prod.snd)
      (p := fun omega : ℕ → ℝ =>
        (canonicalRenewalCount h (residualTail s omega) : ℝ) =
          ((canonicalRenewalCount (s + h) omega - canonicalRenewalCount s omega : ℕ) : ℝ))
      measurable_snd.aemeasurable ?_
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    filter_upwards [ae_canonicalRenewalCount_increment_eq_residualTailCount hrate s h hh]
      with omega homega
    exact_mod_cast homega.symm
  have hgeneric := integral_externalCanonicalRenewalPastHistorySelector_mul_increment
    (ν := ν.prod B) hrate hs hh f hf
  have htargetMeas : Measurable (fun u :
      ((β × StationaryPoissonWorkFutureTimeSliceBase) × (ℕ × (ℕ → ℝ))) × (ℕ → ℝ) =>
      f u.1 * (canonicalRenewalCount h u.2 : ℝ)) :=
    (hf.comp measurable_fst).mul
      ((measurable_of_countable fun n : ℕ => (n : ℝ)).comp
        ((measurable_canonicalRenewalCount h).comp measurable_snd))
  have htargetExternalMeas : Measurable (fun u :
      ((β × StationaryPoissonWorkFutureTimeSliceBase) × (ℕ × (ℕ → ℝ))) × (ℕ → ℝ) =>
      f u.1) := hf.comp measurable_fst
  have hbaseTail_eq_increment :
      (∫ z : (β × StationaryPoissonWorkFutureTimeSliceBase) × (ℕ → ℝ),
        f (z.1, H z.2) * (canonicalRenewalCount h (R z.2) : ℝ) ∂((ν.prod B).prod G)) =
      ∫ z, f (z.1, H z.2) *
        ((canonicalRenewalCount (s + h) z.2 - canonicalRenewalCount s z.2 : ℕ) : ℝ)
        ∂((ν.prod B).prod G) := by
    apply integral_congr_ae
    filter_upwards [hincrement] with z hz
    rw [hz]
  have hbaseToTarget :
      (∫ z : (β × StationaryPoissonWorkFutureTimeSliceBase) × (ℕ → ℝ),
        f (z.1, H z.2) * (canonicalRenewalCount h (R z.2) : ℝ) ∂((ν.prod B).prod G)) =
      ∫ u, f u.1 * (canonicalRenewalCount h u.2 : ℝ) ∂target := by
    simpa [T] using hT_law.integral_comp (f := fun u =>
      f u.1 * (canonicalRenewalCount h u.2 : ℝ)) htargetMeas.aestronglyMeasurable
  have hsourceToTarget :
      (∫ z, f (F z).1 * (canonicalRenewalCount h (F z).2 : ℝ)
        ∂(ν.prod (stationaryPoissonWorkMeasure rate))) =
      ∫ u, f u.1 * (canonicalRenewalCount h u.2 : ℝ) ∂target := by
    simpa using hF_law.integral_comp (f := fun u =>
      f u.1 * (canonicalRenewalCount h u.2 : ℝ)) htargetMeas.aestronglyMeasurable
  have hsourceExternal :
      (∫ z, f (F z).1 ∂(ν.prod (stationaryPoissonWorkMeasure rate)) ) =
      ∫ z : (β × StationaryPoissonWorkFutureTimeSliceBase) × (ℕ → ℝ),
        f (z.1, H z.2) ∂((ν.prod B).prod G) := by
    calc
      (∫ z, f (F z).1 ∂(ν.prod (stationaryPoissonWorkMeasure rate)) ) =
          ∫ u, f u.1 ∂target := by
            simpa using hF_law.integral_comp (f := fun u => f u.1)
              htargetExternalMeas.aestronglyMeasurable
      _ = ∫ z : (β × StationaryPoissonWorkFutureTimeSliceBase) × (ℕ → ℝ),
          f (z.1, H z.2) ∂((ν.prod B).prod G) := by
            symm
            simpa [T] using hT_law.integral_comp (f := fun u => f u.1)
              htargetExternalMeas.aestronglyMeasurable
  change
    (∫ z, f (F z).1 * (canonicalRenewalCount h (F z).2 : ℝ)
      ∂(ν.prod (stationaryPoissonWorkMeasure rate)) ) =
      (∫ z, f (F z).1 ∂(ν.prod (stationaryPoissonWorkMeasure rate)) ) * (rate * h)
  calc
    (∫ z, f (F z).1 * (canonicalRenewalCount h (F z).2 : ℝ)
      ∂(ν.prod (stationaryPoissonWorkMeasure rate)) ) =
        ∫ z : (β × StationaryPoissonWorkFutureTimeSliceBase) × (ℕ → ℝ),
          f (z.1, H z.2) * (canonicalRenewalCount h (R z.2) : ℝ) ∂((ν.prod B).prod G) := by
          rw [hsourceToTarget, ← hbaseToTarget]
    _ = ∫ z, f (z.1, H z.2) *
        ((canonicalRenewalCount (s + h) z.2 - canonicalRenewalCount s z.2 : ℕ) : ℝ)
        ∂((ν.prod B).prod G) := hbaseTail_eq_increment
    _ = (∫ z, f (z.1, H z.2) ∂((ν.prod B).prod G)) * (rate * h) := by
          simpa [B, H, G] using hgeneric
    _ = (∫ z, f (F z).1 ∂(ν.prod (stationaryPoissonWorkMeasure rate)) ) *
          (rate * h) := by
          rw [hsourceExternal]

/-- Deterministic-interval compensation on a stationary marked Poisson input.
Any measurable function of the complete input exposed through `s` is
independent of the fresh arrival count in the following interval. -/
theorem integral_stationaryPoissonWorkFutureTimeSliceSelector_mul_arrivalCount
    {rate s h : ℝ} (hrate : 0 < rate) (hs : 0 ≤ s) (hh : 0 ≤ h)
    (f : StationaryPoissonWorkFutureTimeSliceExternal → ℝ) (hf : Measurable f) :
    ∫ z, f (stationaryPoissonWorkFutureTimeSliceFactors s z).1 *
        (canonicalRenewalCount h (stationaryPoissonWorkFutureTimeSliceFactors s z).2 : ℝ)
        ∂stationaryPoissonWorkMeasure rate =
      (∫ z, f (stationaryPoissonWorkFutureTimeSliceFactors s z).1
        ∂stationaryPoissonWorkMeasure rate) * (rate * h) := by
  let E : Measure (((ℕ → ℝ) × ℝ) × (ℕ → ℝ)) :=
    ((exponentialInterarrivalMeasure rate).prod (expMeasure (1 : ℝ))).prod
      (exponentialInterarrivalMeasure (1 : ℝ))
  let W : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure (1 : ℝ)
  let G : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  let H : (ℕ → ℝ) → ℕ × (ℕ → ℝ) := canonicalRenewalPastHistory s
  let R : (ℕ → ℝ) → ℕ → ℝ := residualTail s
  let ν := E.prod W
  let Ω : Type := ((((ℕ → ℝ) × ℝ) × (ℕ → ℝ)) × (ℕ → ℝ)) × (ℕ → ℝ)
  let F := stationaryPoissonWorkFutureTimeSliceFactors s
  let T : Ω →
      StationaryPoissonWorkFutureTimeSliceExternal × (ℕ → ℝ) :=
    fun z => ((z.1, H z.2), R z.2)
  let target : Measure (StationaryPoissonWorkFutureTimeSliceExternal × (ℕ → ℝ)) :=
    (ν.prod (Measure.map H G)).prod G
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure E := by
    dsimp [E]
    infer_instance
  letI : IsProbabilityMeasure W := by
    simpa [W] using isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  letI : IsProbabilityMeasure G := by
    simpa [G] using isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure ν := by
    dsimp [ν]
    infer_instance
  have hH : Measurable H := by
    simpa [H] using measurable_canonicalRenewalPastHistory s
  have hR : Measurable R := by
    simpa [R] using measurable_residualTail s
  have hF : Measurable F := measurable_stationaryPoissonWorkFutureTimeSliceFactors s
  have hT : Measurable T := by
    exact ((measurable_fst).prodMk (hH.comp measurable_snd)).prodMk
      (hR.comp measurable_snd)
  have hFmap : Measure.map F (stationaryPoissonWorkMeasure rate) = target := by
    simpa [target, ν, E, W, G, H] using
      map_stationaryPoissonWorkFutureTimeSliceFactors hrate hs
  have hTmap : Measure.map T (ν.prod G) = target := by
    simpa [target, T, ν, H, R, G] using
      (map_external_canonicalRenewalPastHistory_residualTail (ν := ν) hrate hs)
  let hF_law : ProbabilityTheory.HasLaw F target (stationaryPoissonWorkMeasure rate) :=
    ⟨hF.aemeasurable, hFmap⟩
  let hT_law : ProbabilityTheory.HasLaw T target (ν.prod G) :=
    ⟨hT.aemeasurable, hTmap⟩
  have hincrement :
      (fun z : Ω =>
        (canonicalRenewalCount h (R z.2) : ℝ)) =ᵐ[ν.prod G]
        fun z =>
          ((canonicalRenewalCount (s + h) z.2 - canonicalRenewalCount s z.2 : ℕ) : ℝ) := by
    refine ae_of_ae_map (μ := ν.prod G) (f := Prod.snd)
      (p := fun omega : ℕ → ℝ =>
        (canonicalRenewalCount h (residualTail s omega) : ℝ) =
          ((canonicalRenewalCount (s + h) omega - canonicalRenewalCount s omega : ℕ) : ℝ))
      measurable_snd.aemeasurable ?_
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    filter_upwards [ae_canonicalRenewalCount_increment_eq_residualTailCount hrate s h hh]
      with omega homega
    exact_mod_cast homega.symm
  have hgeneric := integral_externalCanonicalRenewalPastHistorySelector_mul_increment
    (ν := ν) hrate hs hh f hf
  have htargetMeas : Measurable (fun u :
      StationaryPoissonWorkFutureTimeSliceExternal × (ℕ → ℝ) =>
      f u.1 * (canonicalRenewalCount h u.2 : ℝ)) :=
    (hf.comp measurable_fst).mul
      ((measurable_of_countable fun n : ℕ => (n : ℝ)).comp
        ((measurable_canonicalRenewalCount h).comp measurable_snd))
  have htargetExternalMeas : Measurable (fun u :
      StationaryPoissonWorkFutureTimeSliceExternal × (ℕ → ℝ) => f u.1) :=
    hf.comp measurable_fst
  have hbaseTail_eq_increment :
      (∫ z : Ω,
        f (z.1, H z.2) * (canonicalRenewalCount h (R z.2) : ℝ) ∂(ν.prod G)) =
      ∫ z, f (z.1, H z.2) *
        ((canonicalRenewalCount (s + h) z.2 - canonicalRenewalCount s z.2 : ℕ) : ℝ)
        ∂(ν.prod G) := by
    apply integral_congr_ae
    filter_upwards [hincrement] with z hz
    rw [hz]
  have hbaseToTarget :
      (∫ z : Ω,
        f (z.1, H z.2) * (canonicalRenewalCount h (R z.2) : ℝ) ∂(ν.prod G)) =
      ∫ u, f u.1 * (canonicalRenewalCount h u.2 : ℝ) ∂target := by
    simpa [T] using hT_law.integral_comp (f := fun u =>
      f u.1 * (canonicalRenewalCount h u.2 : ℝ)) htargetMeas.aestronglyMeasurable
  have hsourceToTarget :
      (∫ z, f (F z).1 * (canonicalRenewalCount h (F z).2 : ℝ)
        ∂stationaryPoissonWorkMeasure rate) =
      ∫ u, f u.1 * (canonicalRenewalCount h u.2 : ℝ) ∂target := by
    simpa using hF_law.integral_comp (f := fun u =>
      f u.1 * (canonicalRenewalCount h u.2 : ℝ)) htargetMeas.aestronglyMeasurable
  have hsourceExternal :
      (∫ z, f (F z).1 ∂stationaryPoissonWorkMeasure rate) =
      ∫ z : Ω,
        f (z.1, H z.2) ∂(ν.prod G) := by
    calc
      (∫ z, f (F z).1 ∂stationaryPoissonWorkMeasure rate) =
          ∫ u, f u.1 ∂target := by
            simpa using hF_law.integral_comp (f := fun u => f u.1)
              htargetExternalMeas.aestronglyMeasurable
      _ = ∫ z : Ω,
          f (z.1, H z.2) ∂(ν.prod G) := by
            symm
            simpa [T] using hT_law.integral_comp (f := fun u => f u.1)
              htargetExternalMeas.aestronglyMeasurable
  change
    (∫ z, f (F z).1 * (canonicalRenewalCount h (F z).2 : ℝ)
      ∂stationaryPoissonWorkMeasure rate) =
      (∫ z, f (F z).1 ∂stationaryPoissonWorkMeasure rate) * (rate * h)
  calc
    (∫ z, f (F z).1 * (canonicalRenewalCount h (F z).2 : ℝ)
      ∂stationaryPoissonWorkMeasure rate) =
        ∫ z : Ω,
          f (z.1, H z.2) * (canonicalRenewalCount h (R z.2) : ℝ) ∂(ν.prod G) := by
          rw [hsourceToTarget, ← hbaseToTarget]
    _ = ∫ z, f (z.1, H z.2) *
        ((canonicalRenewalCount (s + h) z.2 - canonicalRenewalCount s z.2 : ℕ) : ℝ)
        ∂(ν.prod G) := hbaseTail_eq_increment
    _ = (∫ z, f (z.1, H z.2) ∂(ν.prod G)) * (rate * h) := by
          simpa [ν, H, G] using hgeneric
    _ = (∫ z, f (F z).1 ∂stationaryPoissonWorkMeasure rate) * (rate * h) := by
          rw [hsourceExternal]

end

end AppliedModelingLib.Probability.Queueing

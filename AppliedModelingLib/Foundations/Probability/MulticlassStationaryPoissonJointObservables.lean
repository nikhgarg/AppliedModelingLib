import AppliedModelingLib.Foundations.Probability.MulticlassStationaryPoisson

/-!
# Joint stationary observables for marked Poisson input

An almost-everywhere measurable observable of a stationary marked-Poisson
input remains almost-everywhere measurable after evaluation along the jointly
measurable real-time flow.  This is the product-space form needed for
time-occupation arguments.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

noncomputable section

variable {Class : Type*} [Fintype Class]

/-- An almost-everywhere measurable stationary observable can be evaluated
jointly along the marked-Poisson real-time flow. -/
theorem aemeasurable_uncurry_comp_multiclassStationaryPoissonWorkFlow
    {β : Type*} [MeasurableSpace β]
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ i, 0 < arrivalRate i)
    (f : (Class → (GoodSuspensionState × (ℤ → ℝ))) → β)
    (hf : AEMeasurable f (multiclassStationaryPoissonWorkMeasure arrivalRate)) :
    AEMeasurable (fun p : ℝ × (Class → (GoodSuspensionState × (ℤ → ℝ))) =>
      f (multiclassStationaryPoissonWorkFlow p.1 p.2))
      (MeasureTheory.volume.prod (multiclassStationaryPoissonWorkMeasure arrivalRate)) := by
  let P := multiclassStationaryPoissonWorkMeasure arrivalRate
  let flow := multiclassStationaryPoissonWorkFlow (Class := Class)
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact isProbabilityMeasure_multiclassStationaryPoissonWorkMeasure
      arrivalRate harrivalRate
  have hskew : MeasurePreserving (fun p : ℝ ×
      (Class → (GoodSuspensionState × (ℤ → ℝ))) => (p.1, flow p.1 p.2))
      (MeasureTheory.volume.prod P) (MeasureTheory.volume.prod P) := by
    simpa [P, flow] using
      (MeasurePreserving.id (MeasureTheory.volume : Measure ℝ)).skew_product
        (measurable_uncurry_multiclassStationaryPoissonWorkFlow (Class := Class))
        (Filter.Eventually.of_forall fun t =>
          (multiclassStationaryPoissonWorkFlow_measurePreserving
            (Class := Class) arrivalRate harrivalRate t).map_eq)
  simpa [P, flow, Function.comp_def] using
    hf.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_snd.comp hskew.quasiMeasurePreserving)

/-- The finite-time occupation integral of an integrable stationary observable
along the marked-Poisson real-time flow is its expectation times the interval
length. -/
theorem integral_uncurry_comp_multiclassStationaryPoissonWorkFlow_Ioc
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ i, 0 < arrivalRate i)
    (f : (Class → (GoodSuspensionState × (ℤ → ℝ))) → ℝ)
    (hf : Integrable f (multiclassStationaryPoissonWorkMeasure arrivalRate))
    (a b : ℝ) (hab : a ≤ b) :
    ∫ p : ℝ × (Class → (GoodSuspensionState × (ℤ → ℝ))),
      f (multiclassStationaryPoissonWorkFlow p.1 p.2)
        ∂((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
          (multiclassStationaryPoissonWorkMeasure arrivalRate)) =
      (b - a) * ∫ ω, f ω ∂(multiclassStationaryPoissonWorkMeasure arrivalRate) := by
  let μI : Measure ℝ := MeasureTheory.volume.restrict (Set.Ioc a b)
  let P := multiclassStationaryPoissonWorkMeasure arrivalRate
  let flow := multiclassStationaryPoissonWorkFlow (Class := Class)
  letI : IsFiniteMeasure μI := by
    dsimp [μI]
    infer_instance
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact isProbabilityMeasure_multiclassStationaryPoissonWorkMeasure
      arrivalRate harrivalRate
  have hskew : MeasurePreserving (fun p : ℝ ×
      (Class → (GoodSuspensionState × (ℤ → ℝ))) => (p.1, flow p.1 p.2))
      (μI.prod P) (μI.prod P) := by
    simpa [μI, P, flow] using
      (MeasurePreserving.id μI).skew_product
        (measurable_uncurry_multiclassStationaryPoissonWorkFlow (Class := Class))
        (Filter.Eventually.of_forall fun t =>
          (multiclassStationaryPoissonWorkFlow_measurePreserving
            (Class := Class) arrivalRate harrivalRate t).map_eq)
  have hsecond : Integrable (fun p : ℝ ×
      (Class → (GoodSuspensionState × (ℤ → ℝ))) => f p.2) (μI.prod P) :=
    hf.comp_snd μI
  calc
    ∫ p : ℝ × (Class → (GoodSuspensionState × (ℤ → ℝ))),
        f (multiclassStationaryPoissonWorkFlow p.1 p.2) ∂(μI.prod P) =
        ∫ p : ℝ × (Class → (GoodSuspensionState × (ℤ → ℝ))), f p.2 ∂(μI.prod P) := by
          change ∫ p, (fun q : ℝ ×
              (Class → (GoodSuspensionState × (ℤ → ℝ))) => f q.2)
                (p.1, flow p.1 p.2) ∂(μI.prod P) = _
          calc
            ∫ p, (fun q : ℝ × (Class →
                (GoodSuspensionState × (ℤ → ℝ))) => f q.2)
                  (p.1, flow p.1 p.2) ∂(μI.prod P) =
                ∫ q, f q.2 ∂Measure.map (fun p : ℝ ×
                    (Class → (GoodSuspensionState × (ℤ → ℝ))) =>
                      (p.1, flow p.1 p.2)) (μI.prod P) :=
              (MeasureTheory.integral_map hskew.aemeasurable
                (by simpa [hskew.map_eq] using hsecond.aestronglyMeasurable)).symm
            _ = ∫ q, f q.2 ∂(μI.prod P) := by rw [hskew.map_eq]
    _ = ∫ t, ∫ ω, f ω ∂P ∂μI := by
          rw [MeasureTheory.integral_prod _ hsecond]
    _ = (b - a) * ∫ ω, f ω ∂P := by
          rw [MeasureTheory.integral_const]
          simp [μI, Real.volume_real_Ioc_of_le hab]

/-- The nonnegative occupation integral of a measurable stationary observable
along the marked-Poisson flow factors into the physical measure of the time
window and its stationary expectation.  Unlike the real-valued interval
version, this form applies to any finite physical-time measure and therefore
also directly to half-open Campbell windows. -/
theorem lintegral_uncurry_comp_multiclassStationaryPoissonWorkFlow
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ i, 0 < arrivalRate i)
    (μI : Measure ℝ) [IsFiniteMeasure μI]
    (f : (Class → (GoodSuspensionState × (ℤ → ℝ))) → ℝ≥0∞)
    (hf : AEMeasurable f (multiclassStationaryPoissonWorkMeasure arrivalRate)) :
    ∫⁻ p : ℝ × (Class → (GoodSuspensionState × (ℤ → ℝ))),
      f (multiclassStationaryPoissonWorkFlow p.1 p.2)
        ∂(μI.prod (multiclassStationaryPoissonWorkMeasure arrivalRate)) =
      μI Set.univ * ∫⁻ ω, f ω ∂multiclassStationaryPoissonWorkMeasure arrivalRate := by
  let P := multiclassStationaryPoissonWorkMeasure arrivalRate
  let flow := multiclassStationaryPoissonWorkFlow (Class := Class)
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact isProbabilityMeasure_multiclassStationaryPoissonWorkMeasure
      arrivalRate harrivalRate
  have hskew : MeasurePreserving (fun p : ℝ ×
      (Class → (GoodSuspensionState × (ℤ → ℝ))) => (p.1, flow p.1 p.2))
      (μI.prod P) (μI.prod P) := by
    simpa [P, flow] using
      (MeasurePreserving.id μI).skew_product
        (measurable_uncurry_multiclassStationaryPoissonWorkFlow (Class := Class))
        (Filter.Eventually.of_forall fun t =>
          (multiclassStationaryPoissonWorkFlow_measurePreserving
            (Class := Class) arrivalRate harrivalRate t).map_eq)
  have hfsnd : AEMeasurable (fun p : ℝ ×
      (Class → (GoodSuspensionState × (ℤ → ℝ))) => f p.2) (μI.prod P) := by
    exact hf.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  calc
    (∫⁻ p : ℝ × (Class → (GoodSuspensionState × (ℤ → ℝ))),
        f (multiclassStationaryPoissonWorkFlow p.1 p.2) ∂(μI.prod P)) =
        ∫⁻ p : ℝ × (Class → (GoodSuspensionState × (ℤ → ℝ))), f p.2 ∂(μI.prod P) := by
          change ∫⁻ p, (fun q : ℝ ×
              (Class → (GoodSuspensionState × (ℤ → ℝ))) => f q.2)
                (p.1, flow p.1 p.2) ∂(μI.prod P) = _
          calc
            _ = ∫⁻ q, f q.2 ∂Measure.map (fun p : ℝ ×
                (Class → (GoodSuspensionState × (ℤ → ℝ))) =>
                  (p.1, flow p.1 p.2)) (μI.prod P) := by
                    simpa only [Function.comp_apply] using
                      (MeasureTheory.lintegral_comp'
                        (μ := μI.prod P)
                        (f := fun q : ℝ ×
                          (Class → (GoodSuspensionState × (ℤ → ℝ))) => f q.2)
                        (g := fun p : ℝ ×
                          (Class → (GoodSuspensionState × (ℤ → ℝ))) =>
                            (p.1, flow p.1 p.2))
                        (by simpa [hskew.map_eq] using hfsnd)
                        hskew.measurable.aemeasurable)
            _ = ∫⁻ q, f q.2 ∂(μI.prod P) := by rw [hskew.map_eq]
    _ = ∫⁻ t, ∫⁻ ω, f ω ∂P ∂μI := by
      rw [MeasureTheory.lintegral_prod (fun p => f p.2)
        hfsnd]
    _ = μI Set.univ * ∫⁻ ω, f ω ∂P := by
      rw [MeasureTheory.lintegral_const]
      ac_rfl

end

end AppliedModelingLib.Probability.PoissonProcess

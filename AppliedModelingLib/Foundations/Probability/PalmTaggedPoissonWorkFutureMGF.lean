import AppliedModelingLib.Foundations.Probability.ExponentialMarkedRenewalWorkMGF
import AppliedModelingLib.Foundations.Probability.PalmTaggedPoissonWorkFutureRate

/-!
# Exponential moments of Palm-tagged Poisson future work

The canonical compound-Poisson calculation is transported to the literal
right-closed future-work ledger of a Palm-selected Poisson arrival.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory Filter

noncomputable section

/-- Literal finite future work after a Palm-selected arrival has an integrable
positive exponential moment below the unit-exponential mark boundary. -/
theorem integrable_exp_mul_palmTaggedPoissonWorkFutureAggregate
    {rate t tilt : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t) (htilt : tilt < 1) :
    Integrable (fun z =>
      Real.exp (tilt * palmTaggedPoissonWorkFutureAggregate z t))
      ((twoSidedInterarrivalMeasure rate).prod
        (twoSidedInterarrivalMeasure (1 : ℝ))) := by
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure rate) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  let F : (ℤ → ℝ) × (ℤ → ℝ) → (ℕ → ℝ) × (ℕ → ℝ) :=
    fun z => (candidateFutureGapPath z.1, candidateFutureUnitWorkPath z.2)
  have hmap : MeasurePreserving F
      ((twoSidedInterarrivalMeasure rate).prod
        (twoSidedInterarrivalMeasure (1 : ℝ)))
      ((exponentialInterarrivalMeasure rate).prod
        (exponentialInterarrivalMeasure (1 : ℝ))) := by
    simpa [F] using (candidateFutureGapPath_measurePreserving hrate).prod
      candidateFutureUnitWorkPath_measurePreserving
  have hgood : ∀ᵐ z ∂(twoSidedInterarrivalMeasure rate).prod
      (twoSidedInterarrivalMeasure (1 : ℝ)), suspensionGoodGapPath z.1 := by
    refine ae_of_ae_map
      (μ := (twoSidedInterarrivalMeasure rate).prod
        (twoSidedInterarrivalMeasure (1 : ℝ)))
      (f := Prod.fst) (p := suspensionGoodGapPath)
      ((measurePreserving_fst : MeasurePreserving Prod.fst
        ((twoSidedInterarrivalMeasure rate).prod
          (twoSidedInterarrivalMeasure (1 : ℝ)))
        (twoSidedInterarrivalMeasure rate)).measurable.aemeasurable) ?_
    rw [Measure.map_fst_prod, measure_univ, one_smul]
    exact ae_suspensionGoodGapPath hrate
  have hcanonical : Integrable (fun z =>
      Real.exp (tilt * canonicalMarkedWork (candidateFutureGapPath z.1)
        (candidateFutureUnitWorkPath z.2) t))
      ((twoSidedInterarrivalMeasure rate).prod
        (twoSidedInterarrivalMeasure (1 : ℝ))) := by
    simpa [F, Function.comp_def] using
      (hmap.integrable_comp
        ((measurable_const.mul (measurable_canonicalMarkedWork t)).exp.aestronglyMeasurable)).mpr
        (integrable_exp_mul_canonicalMarkedWork hrate ht htilt)
  refine hcanonical.congr ?_
  filter_upwards [hgood] with z hz
  rw [palmTaggedPoissonWorkFutureAggregate_eq_canonicalMarkedWork z.1 z.2 hz t]

/-- The literal Palm-tagged future-work MGF is the compound-Poisson MGF at
the same arrival rate and horizon. -/
theorem integral_exp_mul_palmTaggedPoissonWorkFutureAggregate
    {rate t tilt : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t) (htilt : tilt < 1) :
    ∫ z, Real.exp (tilt * palmTaggedPoissonWorkFutureAggregate z t)
      ∂((twoSidedInterarrivalMeasure rate).prod
        (twoSidedInterarrivalMeasure (1 : ℝ))) =
      Real.exp ((rate * t) * (1 / (1 - tilt) - 1)) := by
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure rate) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  let F : (ℤ → ℝ) × (ℤ → ℝ) → (ℕ → ℝ) × (ℕ → ℝ) :=
    fun z => (candidateFutureGapPath z.1, candidateFutureUnitWorkPath z.2)
  have hmap : MeasurePreserving F
      ((twoSidedInterarrivalMeasure rate).prod
        (twoSidedInterarrivalMeasure (1 : ℝ)))
      ((exponentialInterarrivalMeasure rate).prod
        (exponentialInterarrivalMeasure (1 : ℝ))) := by
    simpa [F] using (candidateFutureGapPath_measurePreserving hrate).prod
      candidateFutureUnitWorkPath_measurePreserving
  have hgood : ∀ᵐ z ∂(twoSidedInterarrivalMeasure rate).prod
      (twoSidedInterarrivalMeasure (1 : ℝ)), suspensionGoodGapPath z.1 := by
    refine ae_of_ae_map
      (μ := (twoSidedInterarrivalMeasure rate).prod
        (twoSidedInterarrivalMeasure (1 : ℝ)))
      (f := Prod.fst) (p := suspensionGoodGapPath)
      ((measurePreserving_fst : MeasurePreserving Prod.fst
        ((twoSidedInterarrivalMeasure rate).prod
          (twoSidedInterarrivalMeasure (1 : ℝ)))
        (twoSidedInterarrivalMeasure rate)).measurable.aemeasurable) ?_
    rw [Measure.map_fst_prod, measure_univ, one_smul]
    exact ae_suspensionGoodGapPath hrate
  calc
    ∫ z, Real.exp (tilt * palmTaggedPoissonWorkFutureAggregate z t)
        ∂((twoSidedInterarrivalMeasure rate).prod
          (twoSidedInterarrivalMeasure (1 : ℝ))) =
        ∫ z, Real.exp (tilt * canonicalMarkedWork
          (candidateFutureGapPath z.1) (candidateFutureUnitWorkPath z.2) t)
          ∂((twoSidedInterarrivalMeasure rate).prod
            (twoSidedInterarrivalMeasure (1 : ℝ))) := by
              refine MeasureTheory.integral_congr_ae ?_
              filter_upwards [hgood] with z hz
              rw [palmTaggedPoissonWorkFutureAggregate_eq_canonicalMarkedWork z.1 z.2 hz t]
    _ = ∫ y : (ℕ → ℝ) × (ℕ → ℝ),
        Real.exp (tilt * canonicalMarkedWork y.1 y.2 t)
          ∂((exponentialInterarrivalMeasure rate).prod
            (exponentialInterarrivalMeasure (1 : ℝ))) := by
              simpa [F, Function.comp_def] using hmap.hasLaw.integral_comp
                (f := fun y : (ℕ → ℝ) × (ℕ → ℝ) =>
                  Real.exp (tilt * canonicalMarkedWork y.1 y.2 t))
                ((measurable_const.mul
                  (measurable_canonicalMarkedWork t)).exp.aestronglyMeasurable)
    _ = Real.exp ((rate * t) * (1 / (1 - tilt) - 1)) :=
      integral_exp_mul_canonicalMarkedWork hrate ht htilt

end

end AppliedModelingLib.Probability.PoissonProcess

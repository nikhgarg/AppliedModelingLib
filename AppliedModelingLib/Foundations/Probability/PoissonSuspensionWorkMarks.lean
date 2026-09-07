import AppliedModelingLib.Foundations.Probability.Processes.TimedEmbedded.Campbell

/-!
# Stationary Poisson input with iid service-work marks

This module pairs the verified stationary Poisson suspension with an
independent two-sided iid unit-exponential work-mark path.  The real-time
action reindexes the work marks by exactly the arrival label crossed by the
Poisson flow, so the resulting marked point-process input is genuinely
stationary rather than an origin-only product construction.

It constructs stochastic input and its Campbell/Palm transport.  It does not
construct a queue execution, prove stability, or identify a response time.
-/

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory
open PoissonProcess

noncomputable section

/-- Integer reindexing preserves the iid two-sided exponential path law.
The order convention of `intPathShift` is aligned explicitly with the
Poisson suspension's gap shift. -/
theorem intPathShift_measurePreserving_twoSidedInterarrivalMeasure
    {rate : ℝ} (hrate : 0 < rate) (k : ℤ) :
    MeasurePreserving (intPathShift (α := ℝ) k)
      (twoSidedInterarrivalMeasure rate) (twoSidedInterarrivalMeasure rate) := by
  have hshift : intPathShift (α := ℝ) k = suspensionGapShift k := by
    funext work i
    simp [intPathShift, suspensionGapShift, twoSidedGap, add_comm]
  rw [hshift]
  exact suspensionGapShift_measurePreserving hrate k

/-- A stationary Poisson arrival process of rate `arrivalRate`, together with
an independent iid unit-exponential work-mark path indexed by its arrivals. -/
noncomputable def stationaryPoissonWorkMeasure (arrivalRate : ℝ) :
    Measure (GoodSuspensionState × (ℤ → ℝ)) :=
  timedEmbeddedSuspensionProductMeasure arrivalRate
    (twoSidedInterarrivalMeasure 1)

/-- The marked stationary input is a probability space at positive arrival
rate. -/
theorem isProbabilityMeasure_stationaryPoissonWorkMeasure
    {arrivalRate : ℝ} (harrivalRate : 0 < arrivalRate) :
    IsProbabilityMeasure (stationaryPoissonWorkMeasure arrivalRate) := by
  letI : IsProbabilityMeasure (goodSuspensionMeasure arrivalRate) :=
    isProbabilityMeasure_goodSuspensionMeasure harrivalRate
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  simpa [stationaryPoissonWorkMeasure, timedEmbeddedSuspensionProductMeasure] using
    (inferInstance : IsProbabilityMeasure
      ((goodSuspensionMeasure arrivalRate).prod (twoSidedInterarrivalMeasure 1)))

/-- The time of the `i`th arrival in the untagged stationary marked input. -/
def stationaryPoissonWorkArrival
    (z : GoodSuspensionState × (ℤ → ℝ)) (i : ℤ) : ℝ :=
  timedEmbeddedArrival z i

/-- The service work attached to the `i`th arrival in the untagged stationary
marked input. -/
def stationaryPoissonWorkRequirement
    (z : GoodSuspensionState × (ℤ → ℝ)) (i : ℤ) : ℝ :=
  z.2 i

/-- The arrival configuration and complete work-mark path are independent
factors of the stationary marked input. -/
theorem indepFun_stationaryPoissonWork_arrivals_marks
    {arrivalRate : ℝ} (harrivalRate : 0 < arrivalRate) :
    IndepFun (fun z : GoodSuspensionState × (ℤ → ℝ) => z.1)
      (fun z : GoodSuspensionState × (ℤ → ℝ) => z.2)
      (stationaryPoissonWorkMeasure arrivalRate) := by
  let μa : Measure GoodSuspensionState := goodSuspensionMeasure arrivalRate
  let μw : Measure (ℤ → ℝ) := twoSidedInterarrivalMeasure 1
  letI : IsProbabilityMeasure μa :=
    isProbabilityMeasure_goodSuspensionMeasure harrivalRate
  letI : IsProbabilityMeasure μw :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  simpa [stationaryPoissonWorkMeasure, timedEmbeddedSuspensionProductMeasure,
    μa, μw] using
    (indepFun_prod (μ := μa) (ν := μw) (X := id) (Y := id)
      measurable_id measurable_id)

/-- Each work mark has the source's unit-mean exponential law. -/
theorem stationaryPoissonWorkRequirement_hasLaw
    {arrivalRate : ℝ} (harrivalRate : 0 < arrivalRate) (i : ℤ) :
    HasLaw (fun z : GoodSuspensionState × (ℤ → ℝ) =>
      stationaryPoissonWorkRequirement z i)
      (expMeasure 1) (stationaryPoissonWorkMeasure arrivalRate) := by
  let μa : Measure GoodSuspensionState := goodSuspensionMeasure arrivalRate
  let μw : Measure (ℤ → ℝ) := twoSidedInterarrivalMeasure 1
  letI : IsProbabilityMeasure μa :=
    isProbabilityMeasure_goodSuspensionMeasure harrivalRate
  letI : IsProbabilityMeasure μw :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  have hprojection : MeasurePreserving
      (fun z : GoodSuspensionState × (ℤ → ℝ) => z.2) (μa.prod μw) μw :=
    measurePreserving_snd
  simpa [stationaryPoissonWorkMeasure, timedEmbeddedSuspensionProductMeasure,
    stationaryPoissonWorkRequirement, μa, μw, twoSidedGap] using
    (twoSidedGap_hasLaw (by norm_num : 0 < (1 : ℝ)) i).comp
      hprojection.hasLaw

/-- All service-work marks are strictly positive almost surely. -/
theorem ae_all_stationaryPoissonWorkRequirement_positive
    {arrivalRate : ℝ} (harrivalRate : 0 < arrivalRate) :
    ∀ᵐ z ∂stationaryPoissonWorkMeasure arrivalRate, ∀ i : ℤ,
      0 < stationaryPoissonWorkRequirement z i := by
  let μa : Measure GoodSuspensionState := goodSuspensionMeasure arrivalRate
  let μw : Measure (ℤ → ℝ) := twoSidedInterarrivalMeasure 1
  letI : IsProbabilityMeasure μa :=
    isProbabilityMeasure_goodSuspensionMeasure harrivalRate
  letI : IsProbabilityMeasure μw :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  refine ae_of_ae_map (μ := μa.prod μw) (f := Prod.snd)
    (p := fun work : ℤ → ℝ => ∀ i : ℤ, 0 < work i)
    measurable_snd.aemeasurable ?_
  rw [Measure.map_snd_prod, measure_univ, one_smul]
  simpa [twoSidedGap] using
    (ae_all_twoSidedGap_positive (by norm_num : 0 < (1 : ℝ)))

/-- The marked stationary Poisson input has a verified real-time invariant
law.  At a time shift, marks are reindexed by the same crossed-arrival label
as the Poisson suspension. -/
noncomputable def stationaryPoissonWorkShiftInvariantLaw
    {arrivalRate : ℝ} (harrivalRate : 0 < arrivalRate) :
    Palm.ShiftInvariantProbabilityLaw (GoodSuspensionState × (ℤ → ℝ)) := by
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  exact timedEmbeddedSuspensionShiftInvariantLaw_of_intPathShift harrivalRate
    (twoSidedInterarrivalMeasure 1)
    (fun k => intPathShift_measurePreserving_twoSidedInterarrivalMeasure
      (by norm_num) k)

/-- The selected-arrival law paired with the complete iid work-mark path.
Keeping this as a named construction avoids relying on an implicit
probability-space instance in later theorem signatures. -/
noncomputable def stationaryPoissonWorkTaggedArrivalAtZero
    {arrivalRate : ℝ} (harrivalRate : 0 < arrivalRate) :
    TaggedArrivalAtZero ((ℤ → ℝ) × (ℤ → ℝ)) := by
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  exact timedEmbeddedTaggedArrivalAtZero arrivalRate harrivalRate
    (twoSidedInterarrivalMeasure 1)

/-- The stationary marked input has a genuine Campbell/Palm certificate.
The resulting tagged law contains a selected arrival at zero and the complete
iid work-mark path, without postulating either as a queueing assumption. -/
noncomputable def stationaryPoissonWorkCampbellCertificate
    {arrivalRate : ℝ} (harrivalRate : 0 < arrivalRate) :
    Palm.CampbellPalmTaggedArrivalCertificate
      (stationaryPoissonWorkShiftInvariantLaw harrivalRate)
      (stationaryPoissonWorkTaggedArrivalAtZero harrivalRate) := by
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  simpa only [stationaryPoissonWorkShiftInvariantLaw,
    stationaryPoissonWorkTaggedArrivalAtZero] using
    (timedEmbeddedCampbellCertificate_of_independentPath harrivalRate
    (twoSidedInterarrivalMeasure 1)
    (fun k => intPathShift_measurePreserving_twoSidedInterarrivalMeasure
      (by norm_num) k))

end

end AppliedModelingLib.Probability.Queueing

import AppliedModelingLib.Queueing.NonpreemptivePriorityClassTaggedSelectedMarkInvariance
import AppliedModelingLib.Queueing.MulticlassPalmInput
import AppliedModelingLib.Queueing.NonpreemptivePriorityClassTaggedJointReplayMeasurability

/-!
# Integrability of selected priority waiting rewards

The selected customer's service requirement and queue wait are jointly
integrable under the concrete stable marked-Poisson Palm law.  This makes the
service-weighted waiting reward available to real-valued Campbell and
occupation arguments; it is stronger than merely recording an equality of
possibly undefined Bochner integrals.
-/

namespace AppliedModelingLib.Queueing

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

/-- The class-tagged Palm law obtained by inserting one class-`i` arrival at
time zero into the stationary marked-Poisson input. -/
noncomputable def stationaryPriorityClassTaggedPalmMeasure
    {n : ℕ} (arrivalRate : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j) (i : Fin n) :
    Measure (MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i) :=
  (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag

/-- The nonnegative Borel version of the selected customer's stabilized
finite-replay waiting-work response. -/
noncomputable def stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n) :
    MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ → ENNReal :=
  fun z elapsed => ENNReal.ofReal
    (stationaryPriorityClassTaggedStabilizedWaitingWorkResponse meanService i (z, elapsed))

theorem measurable_stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n) :
    Measurable (Function.uncurry
      (stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN meanService i)) := by
  exact (measurable_stationaryPriorityClassTaggedStabilizedWaitingWorkResponse
    meanService i).ennreal_ofReal

/-- The nonnegative extended-real encoding of a selected customer's service
work times its queue wait.  Its Borel measurability comes from the canonical
finite-replay response, not from a selected-Palm representative. -/
noncomputable def stationaryPriorityClassTaggedWorkQueueWaitRewardNN
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n) :
    MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ENNReal :=
  fun z => ENNReal.ofReal
    (stationaryPriorityClassTaggedWorkRequirement meanService i z *
      stationaryPriorityClassTaggedQueueWait meanService i z)

/-- The service work carried by a selected customer, spread over its literal
waiting interval.  The elapsed-time coordinate is physical time after that
customer's arrival; outside the interval `[0, queueWait)` the contribution is
zero. -/
noncomputable def stationaryPriorityClassTaggedWaitingWorkCoverageNN
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n) :
    MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ → ENNReal :=
  fun z elapsed => if 0 ≤ elapsed ∧
      elapsed < stationaryPriorityClassTaggedQueueWait meanService i z then
    ENNReal.ofReal (stationaryPriorityClassTaggedWorkRequirement meanService i z)
  else 0

/-- Under strict total load, the literal selected-customer waiting-work
coverage is the eventual value of every sufficiently remote strict replay,
simultaneously at all nonnegative elapsed times.  This is a pathwise
stabilization statement; it makes no stationary occupation or Campbell claim.
-/
theorem ae_eventually_forall_stationaryPriorityClassTaggedFiniteReplayWorkWaiting_eq_coverageNN
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      ∀ᶠ horizon : ℕ in Filter.atTop, ∀ elapsed : ℝ, 0 ≤ elapsed →
        ENNReal.ofReal
          (stationaryPriorityClassTaggedWorkRequirement meanService i z *
            stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
              meanService i z (horizon : ℝ) elapsed) =
          stationaryPriorityClassTaggedWaitingWorkCoverageNN meanService i z elapsed := by
  filter_upwards [
    ae_exists_stationaryPriorityClassTaggedFiniteReplayWaitingBeforeHorizon_eq_queueWaitIndicator_all
      arrivalRate meanService harrivalRate hmeanService hstable i] with z hz
  rcases hz with ⟨cutoff, hcutoff, hstableReplay⟩
  apply Filter.eventually_atTop.2
  refine ⟨Nat.ceil cutoff, ?_⟩
  intro horizon hhorizon elapsed helapsed
  have hceil : cutoff ≤ (Nat.ceil cutoff : ℝ) := Nat.le_ceil _
  have hcast : (Nat.ceil cutoff : ℝ) ≤ (horizon : ℝ) := by
    exact_mod_cast hhorizon
  have hlarge : cutoff ≤ (horizon : ℝ) := hceil.trans hcast
  rw [hstableReplay (horizon : ℝ) hlarge elapsed helapsed]
  by_cases hwaiting : elapsed < stationaryPriorityClassTaggedQueueWait meanService i z
  · rw [if_pos hwaiting]
    simp [stationaryPriorityClassTaggedWaitingWorkCoverageNN, helapsed, hwaiting]
  · rw [if_neg hwaiting]
    simp [stationaryPriorityClassTaggedWaitingWorkCoverageNN, helapsed, hwaiting]

/-- The time-spread selected waiting-work reward is Borel on the product of
the full tagged carrier and physical elapsed time. -/
theorem measurable_stationaryPriorityClassTaggedWaitingWorkCoverageNN
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n) :
    Measurable (Function.uncurry
      (stationaryPriorityClassTaggedWaitingWorkCoverageNN meanService i)) := by
  apply Measurable.ite
  · apply measurableSet_setOf.mpr
    simpa only [Function.comp_apply] using
      ((measurable_const.le' measurable_snd).and
      (measurable_snd.lt
        ((measurable_stationaryPriorityClassTaggedQueueWait meanService i).comp
          measurable_fst)))
  · exact ((measurable_stationaryPriorityClassTaggedWorkRequirement meanService i).comp
      measurable_fst).ennreal_ofReal
  · exact measurable_const

/-- The extended-real selected waiting-work coverage agrees almost everywhere
with the `ofReal` image of the canonical jointly Borel finite-replay limit.
This gives Campbell arguments a measurable representative without choosing a
sample-dependent remote-past cutoff. -/
theorem ae_uncurry_stationaryPriorityClassTaggedStabilizedWaitingWorkResponse_eq_coverageNN
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    (fun p : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i × ℝ =>
      ENNReal.ofReal
        (stationaryPriorityClassTaggedStabilizedWaitingWorkResponse meanService i p)) =ᵐ[
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag.prod
          MeasureTheory.volume]
      Function.uncurry (stationaryPriorityClassTaggedWaitingWorkCoverageNN meanService i) := by
  filter_upwards [
    ae_stationaryPriorityClassTaggedStabilizedWaitingWorkResponse_eq_waitingWorkResponse
      arrivalRate meanService harrivalRate hmeanService hstable i] with p hp
  rw [hp]
  change ENNReal.ofReal
      (if 0 ≤ p.2 ∧ p.2 < stationaryPriorityClassTaggedQueueWait meanService i p.1 then
        stationaryPriorityClassTaggedWorkRequirement meanService i p.1
      else 0) =
    (if 0 ≤ p.2 ∧ p.2 < stationaryPriorityClassTaggedQueueWait meanService i p.1 then
      ENNReal.ofReal (stationaryPriorityClassTaggedWorkRequirement meanService i p.1)
    else 0)
  split <;> simp_all [stationaryPriorityClassTaggedWaitingWorkResponse]

/-- Outside a null set of elapsed-time sections, the Palm integral of the
Borel stabilized response equals that of the literal waiting-work coverage. -/
theorem ae_lintegral_stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN_eq_coverageNN
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∀ᵐ elapsed : ℝ ∂MeasureTheory.volume,
      (∫⁻ z, stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN
        meanService i z elapsed ∂
        stationaryPriorityClassTaggedPalmMeasure arrivalRate harrivalRate i) =
      ∫⁻ z, stationaryPriorityClassTaggedWaitingWorkCoverageNN meanService i z elapsed ∂
        stationaryPriorityClassTaggedPalmMeasure arrivalRate harrivalRate i := by
  let P := stationaryPriorityClassTaggedPalmMeasure arrivalRate harrivalRate i
  let g := stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN meanService i
  let coverage := stationaryPriorityClassTaggedWaitingWorkCoverageNN meanService i
  letI : IsProbabilityMeasure P := by
    simpa only [P, stationaryPriorityClassTaggedPalmMeasure] using
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).isProbability
  letI : SFinite P := by infer_instance
  have hcoverage : (fun p : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i × ℝ =>
      g p.1 p.2) =ᵐ[P.prod MeasureTheory.volume] Function.uncurry coverage := by
    simpa only [P, g, coverage, stationaryPriorityClassTaggedPalmMeasure,
      stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN] using
      (ae_uncurry_stationaryPriorityClassTaggedStabilizedWaitingWorkResponse_eq_coverageNN
        arrivalRate meanService harrivalRate hmeanService hstable i)
  have hcoverage' : (fun p : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i × ℝ =>
      g p.1 p.2) =ᵐ[P.prod MeasureTheory.volume]
      fun p => coverage p.1 p.2 := by
    simpa only [Function.uncurry] using hcoverage
  have hsections : ∀ᵐ elapsed : ℝ ∂MeasureTheory.volume,
      ∀ᵐ z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i ∂P,
        g z elapsed = coverage z elapsed := by
    exact Probability.Palm.ae_ae_of_ae_prod_swap P MeasureTheory.volume
      (measurable_stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN meanService i)
      (measurable_stationaryPriorityClassTaggedWaitingWorkCoverageNN meanService i)
      hcoverage'
  filter_upwards [hsections] with elapsed helapsed
  exact MeasureTheory.lintegral_congr_ae helapsed

/-- For a tagged sample with nonnegative service work, integrating its
time-spread waiting contribution recovers its service-work-times-wait reward.
This is the literal length-of-an-interval calculation, before any stochastic
or state-side occupation argument. -/
theorem lintegral_stationaryPriorityClassTaggedWaitingWorkCoverageNN_eq_workQueueWaitRewardNN
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (hwork : 0 ≤ stationaryPriorityClassTaggedWorkRequirement meanService i z) :
    (∫⁻ elapsed : ℝ,
      stationaryPriorityClassTaggedWaitingWorkCoverageNN meanService i z elapsed
        ∂MeasureTheory.volume) =
      stationaryPriorityClassTaggedWorkQueueWaitRewardNN meanService i z := by
  have hrewrite : (fun elapsed : ℝ =>
      stationaryPriorityClassTaggedWaitingWorkCoverageNN meanService i z elapsed) =
      (Set.Ico 0 (stationaryPriorityClassTaggedQueueWait meanService i z)).indicator
        (fun _ : ℝ => ENNReal.ofReal
          (stationaryPriorityClassTaggedWorkRequirement meanService i z)) := by
    funext elapsed
    simp [stationaryPriorityClassTaggedWaitingWorkCoverageNN, Set.indicator,
      Set.mem_Ico]
  rw [hrewrite, MeasureTheory.lintegral_indicator measurableSet_Ico,
    MeasureTheory.setLIntegral_const, Real.volume_Ico]
  simpa [stationaryPriorityClassTaggedWorkQueueWaitRewardNN] using
    (ENNReal.ofReal_mul hwork).symm

/-- Almost surely under the concrete selected-Palm law, the time integral of
the selected waiting-work coverage equals the selected work-times-wait
reward. -/
theorem ae_lintegral_stationaryPriorityClassTaggedWaitingWorkCoverageNN_eq_workQueueWaitRewardNN
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (i : Fin n) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      (∫⁻ elapsed : ℝ,
        stationaryPriorityClassTaggedWaitingWorkCoverageNN meanService i z elapsed
          ∂MeasureTheory.volume) =
        stationaryPriorityClassTaggedWorkQueueWaitRewardNN meanService i z := by
  filter_upwards [
    ae_all_stationaryPriorityClassTaggedWorkRequirementAt_positive
      arrivalRate meanService harrivalRate hmeanService i] with z hpositive
  apply lintegral_stationaryPriorityClassTaggedWaitingWorkCoverageNN_eq_workQueueWaitRewardNN
  rw [stationaryPriorityClassTaggedWorkRequirement_eq_fullCoordinate]
  exact (hpositive i 0).le

/-- Fubini turns the selected-Palm product integral of the time-spread
waiting-work coverage into the already established selected work-times-wait
reward integral. -/
theorem lintegral_stationaryPriorityClassTaggedWaitingWorkCoverageNN_eq_lintegral_workQueueWaitRewardNN
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (i : Fin n) :
    (∫⁻ p : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i × ℝ,
      stationaryPriorityClassTaggedWaitingWorkCoverageNN meanService i p.1 p.2 ∂
        ((Probability.Palm.targetPassiveTaggedArrivalAtZero
          (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
          (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag.prod
            MeasureTheory.volume)) =
      ∫⁻ z, stationaryPriorityClassTaggedWorkQueueWaitRewardNN meanService i z ∂
        (Probability.Palm.targetPassiveTaggedArrivalAtZero
          (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
          (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  let P := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  let g := stationaryPriorityClassTaggedWaitingWorkCoverageNN meanService i
  let reward := stationaryPriorityClassTaggedWorkQueueWaitRewardNN meanService i
  letI : IsProbabilityMeasure P := by
    simpa [P] using (Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).isProbability
  calc
    (∫⁻ p : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i × ℝ,
      g p.1 p.2 ∂(P.prod MeasureTheory.volume)) =
        ∫⁻ z, ∫⁻ elapsed : ℝ, g z elapsed ∂MeasureTheory.volume ∂P := by
          exact MeasureTheory.lintegral_prod (Function.uncurry g)
            (measurable_stationaryPriorityClassTaggedWaitingWorkCoverageNN
              meanService i).aemeasurable
    _ = ∫⁻ z, reward z ∂P := by
      apply MeasureTheory.lintegral_congr_ae
      simpa [P, g, reward] using
        (ae_lintegral_stationaryPriorityClassTaggedWaitingWorkCoverageNN_eq_workQueueWaitRewardNN
          arrivalRate meanService harrivalRate hmeanService i)

/-- Each fixed elapsed-time section of the selected waiting-work coverage has
a finite Palm integral: it is pointwise bounded by the selected service work.
This is the local-finiteness premise for the concrete full-time Campbell
intensity, and does not use a waiting-occupation identity. -/
theorem lintegral_stationaryPriorityClassTaggedWaitingWorkCoverageNN_section_ne_top
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (i : Fin n) (elapsed : ℝ) :
    (∫⁻ z, stationaryPriorityClassTaggedWaitingWorkCoverageNN meanService i z elapsed ∂
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag) ≠ ∞ := by
  let P := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  let work := stationaryPriorityClassTaggedWorkRequirement meanService i
  have hintegrable : Integrable work P := by
    simpa [work, P] using integrable_stationaryPriorityClassTaggedWorkRequirement
      arrivalRate meanService harrivalRate hmeanService i
  have hnonnegative : 0 ≤ᵐ[P] work := by
    filter_upwards [
      ae_all_stationaryPriorityClassTaggedWorkRequirementAt_positive
        arrivalRate meanService harrivalRate hmeanService i] with z hpositive
    change 0 ≤ stationaryPriorityClassTaggedWorkRequirement meanService i z
    rw [stationaryPriorityClassTaggedWorkRequirement_eq_fullCoordinate]
    exact (hpositive i 0).le
  have hworkfinite : (∫⁻ z, ENNReal.ofReal (work z) ∂P) ≠ ∞ := by
    exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      hintegrable.aestronglyMeasurable hnonnegative).mpr hintegrable
  have hbound : ∀ z,
      stationaryPriorityClassTaggedWaitingWorkCoverageNN meanService i z elapsed ≤
        ENNReal.ofReal (work z) := by
    intro z
    unfold stationaryPriorityClassTaggedWaitingWorkCoverageNN
    split_ifs with hwaiting
    · exact le_rfl
    · exact bot_le
  exact (lt_of_le_of_lt (MeasureTheory.lintegral_mono hbound)
    hworkfinite.lt_top).ne

/-- The Borel stabilized response has finite Palm integral on almost every
elapsed-time section. -/
theorem ae_lintegral_stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN_section_ne_top
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∀ᵐ elapsed : ℝ ∂MeasureTheory.volume,
      (∫⁻ z, stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN
        meanService i z elapsed ∂
        stationaryPriorityClassTaggedPalmMeasure arrivalRate harrivalRate i) ≠ ∞ := by
  filter_upwards [
    ae_lintegral_stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN_eq_coverageNN
      arrivalRate meanService harrivalRate hmeanService hstable i] with elapsed helapsed
  rw [helapsed]
  simpa only [stationaryPriorityClassTaggedPalmMeasure] using
    (lintegral_stationaryPriorityClassTaggedWaitingWorkCoverageNN_section_ne_top
      arrivalRate meanService harrivalRate hmeanService i elapsed)

/-- The concrete marked-Poisson input realizes every elapsed-time section of
the selected waiting-work coverage as a full physical-time Campbell measure.
The result follows from the proved input covariance/Haar theorem, not from a
queue-state compensation premise. -/
theorem arrivalTimeCampbellIntensity_stationaryPriorityClassTaggedWaitingWorkCoverageNN_eq_rate_smul_volume
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (i : Fin n) (elapsed : ℝ) :
    Probability.Palm.arrivalTimeCampbellIntensity
      (multiclassStationaryPoissonWorkClassCampbellCertificate
        arrivalRate harrivalRate i)
      (fun z => stationaryPriorityClassTaggedWaitingWorkCoverageNN meanService i z elapsed) =
      (ENNReal.ofReal (arrivalRate i) *
        (∫⁻ z, stationaryPriorityClassTaggedWaitingWorkCoverageNN meanService i z elapsed ∂
          (Probability.Palm.targetPassiveTaggedArrivalAtZero
            (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
            (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag)) •
          (MeasureTheory.volume : Measure ℝ) := by
  apply arrivalTimeCampbellIntensity_multiclassStationaryPoissonWorkClass_eq_rate_smul_volume
    arrivalRate harrivalRate i
  · exact (measurable_stationaryPriorityClassTaggedWaitingWorkCoverageNN
      meanService i).comp (measurable_id.prodMk measurable_const)
  · exact lintegral_stationaryPriorityClassTaggedWaitingWorkCoverageNN_section_ne_top
      arrivalRate meanService harrivalRate hmeanService i elapsed

/-- A finite Borel reward under the class-tagged Palm law has physical-time
Campbell intensity equal to its arrival rate times its Palm mean. -/
theorem arrivalTimeCampbellIntensity_stationaryPriorityClassTagged_eq_rate_smul_volume
    {n : ℕ} (arrivalRate : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j) (i : Fin n)
    (reward : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ≥0∞)
    (hreward : Measurable reward)
    (hfinite : (∫⁻ z, reward z ∂
      stationaryPriorityClassTaggedPalmMeasure arrivalRate harrivalRate i) ≠ ∞) :
    Probability.Palm.arrivalTimeCampbellIntensity
      (multiclassStationaryPoissonWorkClassCampbellCertificate
        arrivalRate harrivalRate i) reward =
      (ENNReal.ofReal (arrivalRate i) * ∫⁻ z, reward z ∂
        stationaryPriorityClassTaggedPalmMeasure arrivalRate harrivalRate i) •
        (MeasureTheory.volume : Measure ℝ) := by
  have hfinite' : (∫⁻ z, reward z ∂
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag) ≠ ∞ := by
    simpa only [stationaryPriorityClassTaggedPalmMeasure] using hfinite
  simpa only [stationaryPriorityClassTaggedPalmMeasure] using
    (arrivalTimeCampbellIntensity_multiclassStationaryPoissonWorkClass_eq_rate_smul_volume
      arrivalRate harrivalRate i reward hreward hfinite')

/-- A jointly Borel class-tagged reward obeys the Campbell intensity formula
on every elapsed-time section where its Palm integral is finite. -/
theorem ae_arrivalTimeCampbellIntensity_stationaryPriorityClassTagged_eq_rate_smul_volume_of_ae_section_ne_top
    {n : ℕ} (arrivalRate : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j) (i : Fin n)
    (response : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ → ℝ≥0∞)
    (hresponse : Measurable (Function.uncurry response))
    (hfinite : ∀ᵐ elapsed : ℝ ∂MeasureTheory.volume,
      (∫⁻ z, response z elapsed ∂
        stationaryPriorityClassTaggedPalmMeasure arrivalRate harrivalRate i) ≠ ∞) :
    ∀ᵐ elapsed : ℝ ∂MeasureTheory.volume,
      Probability.Palm.arrivalTimeCampbellIntensity
        (multiclassStationaryPoissonWorkClassCampbellCertificate
          arrivalRate harrivalRate i) (response · elapsed) =
        (ENNReal.ofReal (arrivalRate i) * ∫⁻ z, response z elapsed ∂
          stationaryPriorityClassTaggedPalmMeasure arrivalRate harrivalRate i) •
          (MeasureTheory.volume : Measure ℝ) := by
  filter_upwards [hfinite] with elapsed helapsed
  exact arrivalTimeCampbellIntensity_stationaryPriorityClassTagged_eq_rate_smul_volume
    arrivalRate harrivalRate i (response · elapsed)
    (hresponse.comp (measurable_id.prodMk measurable_const)) helapsed

/-- The jointly Borel stabilized finite-replay response has the same
arrival-time intensity as the literal selected waiting-work coverage, outside
a null set of elapsed-time sections.  This is the measurable version of the
customer-side waiting reward needed before comparing it with an original-label
stationary trajectory. -/
theorem ae_arrivalTimeCampbellIntensity_stationaryPriorityClassTaggedStabilizedWaitingWorkResponse_eq_rate_smul_volume
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∀ᵐ elapsed : ℝ ∂MeasureTheory.volume,
      Probability.Palm.arrivalTimeCampbellIntensity
        (multiclassStationaryPoissonWorkClassCampbellCertificate
          arrivalRate harrivalRate i)
        (stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN meanService i · elapsed) =
        (ENNReal.ofReal (arrivalRate i) *
          ∫⁻ z, stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN
            meanService i z elapsed ∂
            stationaryPriorityClassTaggedPalmMeasure arrivalRate harrivalRate i) •
          (MeasureTheory.volume : Measure ℝ) := by
  exact
    ae_arrivalTimeCampbellIntensity_stationaryPriorityClassTagged_eq_rate_smul_volume_of_ae_section_ne_top
      arrivalRate harrivalRate i
      (stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN meanService i)
      (measurable_stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN meanService i)
      (ae_lintegral_stationaryPriorityClassTaggedStabilizedWaitingWorkResponseNN_section_ne_top
        arrivalRate meanService harrivalRate hmeanService hstable i)

/-- The Borel stabilized replay response has the same interval Campbell
coverage as the literal work-times-wait reward.  The proof uses only the
almost-everywhere intensity equality above, so it never treats a
sample-dependent remote-past cutoff as a measurable function. -/
theorem arrivalTimeCampbellCoverage_stationaryPriorityClassTaggedStabilizedWaitingWorkResponse_Ico_eq_rate_mul_lintegral_workQueueWaitRewardNN
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) (a b : ℝ) :
    Probability.Palm.arrivalTimeCampbellCoverage
      (multiclassStationaryPoissonWorkClassCampbellCertificate
        arrivalRate harrivalRate i)
      (fun z elapsed => ENNReal.ofReal
        (stationaryPriorityClassTaggedStabilizedWaitingWorkResponse
          meanService i (z, elapsed)))
      (Set.Ico a b) =
      (ENNReal.ofReal (arrivalRate i) * ENNReal.ofReal (b - a)) *
        (∫⁻ z, stationaryPriorityClassTaggedWorkQueueWaitRewardNN meanService i z ∂
          (Probability.Palm.targetPassiveTaggedArrivalAtZero
            (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
              (harrivalRate i))
            (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag) := by
  let P := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  let g : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ → ℝ≥0∞ :=
    fun z elapsed => ENNReal.ofReal
      (stationaryPriorityClassTaggedStabilizedWaitingWorkResponse
        meanService i (z, elapsed))
  let coverage := stationaryPriorityClassTaggedWaitingWorkCoverageNN meanService i
  have hg : Measurable (Function.uncurry g) := by
    simpa [g, Function.uncurry] using
      (measurable_stationaryPriorityClassTaggedStabilizedWaitingWorkResponse
        meanService i).ennreal_ofReal
  have hcoverage : (fun p : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i × ℝ =>
      g p.1 p.2) =ᵐ[P.prod MeasureTheory.volume] Function.uncurry coverage := by
    simpa [P, g, coverage] using
      (ae_uncurry_stationaryPriorityClassTaggedStabilizedWaitingWorkResponse_eq_coverageNN
        arrivalRate meanService harrivalRate hmeanService hstable i)
  rw [Probability.Palm.arrivalTimeCampbellCoverage_Ico_eq_rate_mul_lintegral_ae
    (multiclassStationaryPoissonWorkClassCampbellCertificate arrivalRate harrivalRate i)
    g hg (ENNReal.ofReal (arrivalRate i))
    (ae_arrivalTimeCampbellIntensity_stationaryPriorityClassTaggedStabilizedWaitingWorkResponse_eq_rate_smul_volume
      arrivalRate meanService harrivalRate hmeanService hstable i) a b]
  rw [MeasureTheory.lintegral_congr_ae hcoverage]
  congr 1
  simpa only [Function.uncurry] using
    (lintegral_stationaryPriorityClassTaggedWaitingWorkCoverageNN_eq_lintegral_workQueueWaitRewardNN
      arrivalRate meanService harrivalRate hmeanService i)

/-- The literal physical-time coverage by selected customers' waiting work on
an interval is arrival rate times its length times the Palm work-times-wait
mean.  This is the customer-side half of the priority waiting-occupation
argument; it has no state-side or boundary claim. -/
theorem arrivalTimeCampbellCoverage_stationaryPriorityClassTaggedWaitingWork_Ico_eq_rate_mul_lintegral_workQueueWaitRewardNN
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (i : Fin n) (a b : ℝ) :
    Probability.Palm.arrivalTimeCampbellCoverage
      (multiclassStationaryPoissonWorkClassCampbellCertificate
        arrivalRate harrivalRate i)
      (stationaryPriorityClassTaggedWaitingWorkCoverageNN meanService i)
      (Set.Ico a b) =
      (ENNReal.ofReal (arrivalRate i) * ENNReal.ofReal (b - a)) *
        (∫⁻ z, stationaryPriorityClassTaggedWorkQueueWaitRewardNN meanService i z ∂
          (Probability.Palm.targetPassiveTaggedArrivalAtZero
            (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
            (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag) := by
  rw [Probability.Palm.arrivalTimeCampbellCoverage_Ico_eq_rate_mul_lintegral
    (multiclassStationaryPoissonWorkClassCampbellCertificate arrivalRate harrivalRate i)
    (stationaryPriorityClassTaggedWaitingWorkCoverageNN meanService i)
    (measurable_stationaryPriorityClassTaggedWaitingWorkCoverageNN meanService i)
    (ENNReal.ofReal (arrivalRate i))
    (fun elapsed =>
      arrivalTimeCampbellIntensity_stationaryPriorityClassTaggedWaitingWorkCoverageNN_eq_rate_smul_volume
        arrivalRate meanService harrivalRate hmeanService i elapsed) a b]
  rw [lintegral_stationaryPriorityClassTaggedWaitingWorkCoverageNN_eq_lintegral_workQueueWaitRewardNN
    arrivalRate meanService harrivalRate hmeanService i]

/-- The selected waiting-work Campbell coverage has an explicit
physical-time expansion over every labelled class-`i` arrival.  Each summand
is evaluated at physical time minus that arrival's epoch.  This is the
customer-side surface that will be compared with the stationary labelled
queue-state sum; no such comparison is asserted here. -/
theorem arrivalTimeCampbellCoverage_stationaryPriorityClassTaggedWaitingWork_Ico_eq_tsum_physicalTime
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (i : Fin n) (a b : ℝ) :
    Probability.Palm.arrivalTimeCampbellCoverage
      (multiclassStationaryPoissonWorkClassCampbellCertificate
        arrivalRate harrivalRate i)
      (stationaryPriorityClassTaggedWaitingWorkCoverageNN meanService i)
      (Set.Ico a b) =
      ∑' k : ℤ, ∫⁻ p : ℝ ×
        (StationaryPoissonWorkPath × ({j : Fin n // j ≠ i} → StationaryPoissonWorkPath)),
        if p.1 ∈ Set.Ico a b then
          stationaryPriorityClassTaggedWaitingWorkCoverageNN meanService i
            ((multiclassStationaryPoissonWorkClassCampbellCertificate
              arrivalRate harrivalRate i).recenterAt p.2 k)
            (p.1 - Probability.Queueing.timedEmbeddedArrival p.2.1 k)
        else 0 ∂(MeasureTheory.volume.prod
          (Probability.Palm.targetPassiveProductBaseLaw
            (Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw (harrivalRate i))
            (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Pbase) := by
  simpa using
    (Probability.Palm.arrivalTimeCampbellCoverage_Ico_eq_tsum_physicalTime
      (multiclassStationaryPoissonWorkClassCampbellCertificate
        arrivalRate harrivalRate i)
      (stationaryPriorityClassTaggedWaitingWorkCoverageNN meanService i)
      (measurable_stationaryPriorityClassTaggedWaitingWorkCoverageNN meanService i) a b)

/-- The selected work-times-wait reward is Borel on the full tagged carrier. -/
theorem measurable_stationaryPriorityClassTaggedWorkQueueWaitRewardNN
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n) :
    Measurable (stationaryPriorityClassTaggedWorkQueueWaitRewardNN meanService i) := by
  exact ((measurable_stationaryPriorityClassTaggedWorkRequirement meanService i).mul
    (measurable_stationaryPriorityClassTaggedQueueWait meanService i)).ennreal_ofReal

/-- In every translated unit arrival slab, the literal sum of selected
work-times-wait rewards has the genuine multiclass Campbell intensity. -/
theorem lintegral_sum_multiclassStationaryPoissonWorkClassCampbell_translatedUnit_workQueueWaitReward
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Fin n) (t : ℝ) :
    ∫⁻ x, (∑ j ∈
      (multiclassStationaryPoissonWorkClassCampbellCertificate
        arrivalRate harrivalRate i).arrivalsIn t (t + 1) x,
      stationaryPriorityClassTaggedWorkQueueWaitRewardNN meanService i
        ((multiclassStationaryPoissonWorkClassCampbellCertificate
          arrivalRate harrivalRate i).recenterAt x j)) ∂
        (Probability.Palm.targetPassiveProductBaseLaw
          (Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw (harrivalRate i))
          (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Pbase =
      ENNReal.ofReal (arrivalRate i) *
        (∫⁻ z, stationaryPriorityClassTaggedWorkQueueWaitRewardNN meanService i z ∂
          (Probability.Palm.targetPassiveTaggedArrivalAtZero
            (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
            (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag) := by
  exact lintegral_sum_multiclassStationaryPoissonWorkClassCampbell_translatedUnit
    arrivalRate harrivalRate i t
    (stationaryPriorityClassTaggedWorkQueueWaitRewardNN meanService i)
    (measurable_stationaryPriorityClassTaggedWorkQueueWaitRewardNN meanService i)

/-- The time-intensity measure of literal selected work-times-wait rewards
has the corresponding Campbell mass on every translated unit interval. -/
theorem arrivalTimeCampbellIntensity_stationaryPriorityClassTaggedWorkQueueWaitReward_Ico
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Fin n) (t : ℝ) :
    Probability.Palm.arrivalTimeCampbellIntensity
      (multiclassStationaryPoissonWorkClassCampbellCertificate
        arrivalRate harrivalRate i)
      (stationaryPriorityClassTaggedWorkQueueWaitRewardNN meanService i)
      (Set.Ico t (t + 1)) =
      ENNReal.ofReal (arrivalRate i) *
        (∫⁻ z, stationaryPriorityClassTaggedWorkQueueWaitRewardNN meanService i z ∂
          (Probability.Palm.targetPassiveTaggedArrivalAtZero
            (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
            (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag) := by
  exact arrivalTimeCampbellIntensity_multiclassStationaryPoissonWorkClass_Ico
    arrivalRate harrivalRate i t
    (stationaryPriorityClassTaggedWorkQueueWaitRewardNN meanService i)
    (measurable_stationaryPriorityClassTaggedWorkQueueWaitRewardNN meanService i)

/-- Under strict total load, the selected customer's literal service work
times its literal queue wait has a finite first moment.  The proof separates
the selected exponential mark, uses mark invariance of the queue wait, and
then transports the product-integrability conclusion back to the concrete
Palm carrier. -/
theorem integrable_stationaryPriorityClassTaggedWorkRequirement_mul_queueWait
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    Integrable (fun z => stationaryPriorityClassTaggedWorkRequirement meanService i z *
      stationaryPriorityClassTaggedQueueWait meanService i z)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  let P := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  let E : Measure (MulticlassPalmSelectedMarkExternalCarrier i) :=
    ((Probability.PoissonProcess.twoSidedInterarrivalMeasure (arrivalRate i)).prod
      ((Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)).prod
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)))).prod
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i).Pbase
  let B : Measure ℝ := ProbabilityTheory.expMeasure (1 : ℝ)
  let e := multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalEquiv i
  let w : MulticlassPalmSelectedMarkExternalCarrier i × ℝ → ℝ := fun x =>
    stationaryPriorityClassTaggedQueueWait meanService i
      (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors i x)
  let M := (E.prod B).prod B
  let reorder : (MulticlassPalmSelectedMarkExternalCarrier i × ℝ) × ℝ →
      (MulticlassPalmSelectedMarkExternalCarrier i × ℝ) × ℝ :=
    fun q => ((q.1.1, q.2), q.1.2)
  let F : (MulticlassPalmSelectedMarkExternalCarrier i × ℝ) × ℝ → ℝ := fun q =>
    w q.1 * q.1.2
  let K : (MulticlassPalmSelectedMarkExternalCarrier i × ℝ) × ℝ → ℝ := fun q =>
    w q.1 * q.2
  letI : IsProbabilityMeasure
      (Probability.PoissonProcess.twoSidedInterarrivalMeasure (arrivalRate i)) :=
    Probability.PoissonProcess.isProbabilityMeasure_twoSidedInterarrivalMeasure
      (harrivalRate i)
  letI : IsProbabilityMeasure
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)) :=
    Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (by norm_num)
  letI : IsProbabilityMeasure
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i).Pbase :=
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i).isProbability
  letI : IsProbabilityMeasure E := by
    dsimp [E]
    infer_instance
  letI : IsProbabilityMeasure B :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  have hpres : MeasurePreserving e P (E.prod B) := by
    simpa [e, P, E, B] using
      (multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalEquiv_measurePreserving
        arrivalRate harrivalRate i)
  have hback : MeasurePreserving e.symm (E.prod B) P := by
    exact hpres.symm e
  have hwSource : Integrable (stationaryPriorityClassTaggedQueueWait meanService i) P := by
    simpa [P] using integrable_stationaryPriorityClassTaggedQueueWait_of_totalStable
      arrivalRate meanService harrivalRate hmeanService hstable i
  have hw : Integrable w (E.prod B) := by
    simpa [w, e, Function.comp_def] using hback.integrable_comp_of_integrable hwSource
  have hmark : Integrable (fun x : ℝ => x) B := by
    simpa [B] using AppliedModelingLib.Probability.integrable_id_expMeasure (by norm_num : (0 : ℝ) < 1)
  have hreorder : MeasurePreserving reorder M M := by
    let hassoc := measurePreserving_prodAssoc E B B
    let hswap := (MeasurePreserving.id E).prod
      (Measure.measurePreserving_swap (μ := B) (ν := B))
    let hunassoc := (measurePreserving_prodAssoc E B B).symm
    convert hunassoc.comp (hswap.comp hassoc) using 1
  have hpair : ∀ᵐ q ∂M,
      w q.1 = w (q.1.1, q.2) := by
    simpa [M, E, B, w] using
      (ae_stationaryPriorityClassTaggedQueueWait_eq_of_selectedMarkExternal_pair
        arrivalRate meanService harrivalRate hmeanService hstable i)
  have hFK : F =ᵐ[M] K ∘ reorder := by
    filter_upwards [hpair] with q hq
    simp only [F, K, reorder, Function.comp_apply]
    rw [hq]
  have hK : Integrable K M := by
    simpa [K, M] using hw.mul_prod hmark
  have hF : Integrable F M := by
    exact (hreorder.integrable_comp_of_integrable hK).congr hFK.symm
  let reward : MulticlassPalmSelectedMarkExternalCarrier i × ℝ → ℝ := fun x =>
    w x * x.2
  have hrewardMeas : AEStronglyMeasurable reward (E.prod B) := by
    exact (hw.aestronglyMeasurable.mul measurable_snd.aestronglyMeasurable)
  have hreward : Integrable reward (E.prod B) := by
    have hcomp : Integrable (reward ∘ Prod.fst) M := by
      simpa [reward, F, Function.comp_def] using hF
    exact ((measurePreserving_fst : MeasurePreserving Prod.fst M (E.prod B)).integrable_comp
      hrewardMeas).mp hcomp
  have hrewardPalm : Integrable (reward ∘ e) P := by
    exact hpres.integrable_comp_of_integrable hreward
  have hmarkReward : Integrable (fun z =>
      stationaryPriorityClassTaggedQueueWait meanService i z *
        (multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalFactors i z).2) P := by
    refine hrewardPalm.congr ?_
    filter_upwards with z
    change stationaryPriorityClassTaggedQueueWait meanService i
          (multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors
            i
            (multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalFactors
              i z)) *
          (multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalFactors
            i z).2 =
        stationaryPriorityClassTaggedQueueWait meanService i z *
          (multiclassStationaryPoissonWorkClassTaggedSelectedMarkExternalFactors
            i z).2
    rw [multiclassStationaryPoissonWorkClassTaggedFromSelectedMarkExternalFactors_apply]
  refine hmarkReward.const_mul (meanService i) |>.congr ?_
  filter_upwards with z
  rw [stationaryPriorityClassTaggedWorkRequirement_eq_mean_mul_selectedMarkFactor]
  ring

/-- Under strict total load, the extended-real selected work-times-wait
reward has finite expectation under the concrete Palm law. -/
theorem lintegral_stationaryPriorityClassTaggedWorkQueueWaitRewardNN_ne_top
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    (∫⁻ z, stationaryPriorityClassTaggedWorkQueueWaitRewardNN meanService i z ∂
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag) ≠ ∞ := by
  let P := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  let reward : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ := fun z =>
    stationaryPriorityClassTaggedWorkRequirement meanService i z *
      stationaryPriorityClassTaggedQueueWait meanService i z
  have hintegrable : Integrable reward P := by
    simpa [reward, P] using
      integrable_stationaryPriorityClassTaggedWorkRequirement_mul_queueWait
        arrivalRate meanService harrivalRate hmeanService hstable i
  have hnonnegative : 0 ≤ᵐ[P] reward := by
    filter_upwards [
      ae_all_stationaryPriorityClassTaggedWorkRequirementAt_positive
        arrivalRate meanService harrivalRate hmeanService i,
      ae_nonneg_stationaryPriorityClassTaggedQueueWait
        arrivalRate meanService harrivalRate hmeanService hstable i] with z hwork hwait
    have hwork' : 0 ≤ stationaryPriorityClassTaggedWorkRequirement meanService i z := by
      have hpositive : 0 < stationaryPriorityClassTaggedWorkRequirement meanService i z := by
        simpa [stationaryPriorityClassTaggedWorkRequirement_eq_fullCoordinate] using hwork i 0
      exact hpositive.le
    exact mul_nonneg hwork' hwait
  simpa [stationaryPriorityClassTaggedWorkQueueWaitRewardNN, reward, P] using
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      hintegrable.aestronglyMeasurable hnonnegative).mpr hintegrable

/-- Under strict total load, the literal selected-reward intensity has finite
mass on every translated unit time window. -/
theorem arrivalTimeCampbellIntensity_stationaryPriorityClassTaggedWorkQueueWaitReward_Ico_ne_top
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (t : ℝ) :
    Probability.Palm.arrivalTimeCampbellIntensity
      (multiclassStationaryPoissonWorkClassCampbellCertificate
        arrivalRate harrivalRate i)
      (stationaryPriorityClassTaggedWorkQueueWaitRewardNN meanService i)
      (Set.Ico t (t + 1)) ≠ ∞ := by
  rw [arrivalTimeCampbellIntensity_stationaryPriorityClassTaggedWorkQueueWaitReward_Ico
    arrivalRate meanService harrivalRate i t]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (lintegral_stationaryPriorityClassTaggedWorkQueueWaitRewardNN_ne_top
      arrivalRate meanService harrivalRate hmeanService hstable i)

end

end AppliedModelingLib.Queueing

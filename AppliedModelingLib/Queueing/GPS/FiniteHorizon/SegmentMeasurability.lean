import AppliedModelingLib.Queueing.GPS.FiniteHorizon.Measurability
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.SegmentTrace
import Mathlib.Data.List.GetD
import Mathlib.Tactic

/-!
# Coordinatewise Borel access to finite GPS segment histories

The finite GPS executor emits a variable-length list of concrete execution
segments.  This module does not put a measurable-space structure on that
list.  Instead it exposes a fixed natural-number slot, totalized by a
harmless zero segment, and proves Borel measurability of every scalar segment
coordinate.  This is the appropriate interface for later finite replay
arguments that stratify discrete execution shapes separately.
-/

namespace AppliedModelingLib.Probability.Queueing

noncomputable section

variable {Class Omega : Type*} [Fintype Class] [DecidableEq Class]
  [MeasurableSpace Omega]

/-- A harmless out-of-range value for coordinate access to a finite GPS
segment history.  It is not an execution segment or an arrival event. -/
def finiteGPSExecutionSegmentDefault : FiniteGPSExecutionSegment Class :=
  { startTime := 0
    duration := 0
    startWorkload := fun _ => 0
    classRate := fun _ => 0
    serviceIncrement := fun _ => 0
    preEndpointWorkload := fun _ => 0
    endpointBatch := fun _ => 0
    endpointWorkload := fun _ => 0
    endpointIsExternalBatch := false }

/-- Totalized access to the `slot`-th concrete segment emitted by one bounded
GPS gap.  The definition reads the executable segment list directly; it does
not accept a caller-supplied execution path. -/
def finiteGPSRunGapSegmentAt
    (fuel : Nat) (capacity : ℝ) (weight work batchWork : Class → ℝ)
    (currentTime nextBatchDelay : ℝ) (slot : Nat) :
    FiniteGPSExecutionSegment Class :=
  (finiteGPSRunGapSegments fuel capacity weight work batchWork
    currentTime nextBatchDelay).getD slot finiteGPSExecutionSegmentDefault

/-- Coordinatewise Borel package for a concrete GPS execution segment.  The
record itself deliberately carries no measurable-space instance here. -/
def FiniteGPSExecutionSegmentCoordinatesMeasurable
    (segment : Omega → FiniteGPSExecutionSegment Class) : Prop :=
  Measurable (fun omega => (segment omega).startTime) ∧
    Measurable (fun omega => (segment omega).duration) ∧
      (∀ i, Measurable (fun omega => (segment omega).startWorkload i)) ∧
        (∀ i, Measurable (fun omega => (segment omega).classRate i)) ∧
          (∀ i, Measurable (fun omega => (segment omega).serviceIncrement i)) ∧
            (∀ i, Measurable (fun omega => (segment omega).preEndpointWorkload i)) ∧
              (∀ i, Measurable (fun omega => (segment omega).endpointBatch i)) ∧
                (∀ i, Measurable (fun omega => (segment omega).endpointWorkload i)) ∧
                  Measurable (fun omega => (segment omega).endpointIsExternalBatch)

theorem finiteGPSExecutionSegmentCoordinatesMeasurable_const
    (segment : FiniteGPSExecutionSegment Class) :
    FiniteGPSExecutionSegmentCoordinatesMeasurable (fun _ : Omega => segment) := by
  refine ⟨measurable_const, measurable_const, ?_, ?_, ?_, ?_, ?_, ?_,
    measurable_const⟩ <;> intro i <;> exact measurable_const

theorem FiniteGPSExecutionSegmentCoordinatesMeasurable.ite
    {condition : Set Omega} [DecidablePred (fun omega => omega ∈ condition)]
    (hcondition : MeasurableSet condition)
    {left right : Omega → FiniteGPSExecutionSegment Class}
    (hleft : FiniteGPSExecutionSegmentCoordinatesMeasurable left)
    (hright : FiniteGPSExecutionSegmentCoordinatesMeasurable right) :
    FiniteGPSExecutionSegmentCoordinatesMeasurable
      (fun omega => if omega ∈ condition then left omega else right omega) := by
  rcases hleft with ⟨hleftStart, hleftDuration, hleftWork, hleftRate,
    hleftService, hleftPre, hleftBatch, hleftEndpoint, hleftExternal⟩
  rcases hright with ⟨hrightStart, hrightDuration, hrightWork, hrightRate,
    hrightService, hrightPre, hrightBatch, hrightEndpoint, hrightExternal⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change Measurable (fun omega =>
      (if omega ∈ condition then left omega else right omega).startTime)
    have hformula : (fun omega =>
        (if omega ∈ condition then left omega else right omega).startTime) =
        fun omega => if omega ∈ condition then (left omega).startTime
          else (right omega).startTime := by
      funext omega
      split <;> rfl
    rw [hformula]
    exact Measurable.ite hcondition hleftStart hrightStart
  · change Measurable (fun omega =>
      (if omega ∈ condition then left omega else right omega).duration)
    have hformula : (fun omega =>
        (if omega ∈ condition then left omega else right omega).duration) =
        fun omega => if omega ∈ condition then (left omega).duration
          else (right omega).duration := by
      funext omega
      split <;> rfl
    rw [hformula]
    exact Measurable.ite hcondition hleftDuration hrightDuration
  · intro i
    change Measurable (fun omega =>
      (if omega ∈ condition then left omega else right omega).startWorkload i)
    have hformula : (fun omega =>
        (if omega ∈ condition then left omega else right omega).startWorkload i) =
        fun omega => if omega ∈ condition then (left omega).startWorkload i
          else (right omega).startWorkload i := by
      funext omega
      split <;> rfl
    rw [hformula]
    exact Measurable.ite hcondition (hleftWork i) (hrightWork i)
  · intro i
    change Measurable (fun omega =>
      (if omega ∈ condition then left omega else right omega).classRate i)
    have hformula : (fun omega =>
        (if omega ∈ condition then left omega else right omega).classRate i) =
        fun omega => if omega ∈ condition then (left omega).classRate i
          else (right omega).classRate i := by
      funext omega
      split <;> rfl
    rw [hformula]
    exact Measurable.ite hcondition (hleftRate i) (hrightRate i)
  · intro i
    change Measurable (fun omega =>
      (if omega ∈ condition then left omega else right omega).serviceIncrement i)
    have hformula : (fun omega =>
        (if omega ∈ condition then left omega else right omega).serviceIncrement i) =
        fun omega => if omega ∈ condition then (left omega).serviceIncrement i
          else (right omega).serviceIncrement i := by
      funext omega
      split <;> rfl
    rw [hformula]
    exact Measurable.ite hcondition (hleftService i) (hrightService i)
  · intro i
    change Measurable (fun omega =>
      (if omega ∈ condition then left omega else right omega).preEndpointWorkload i)
    have hformula : (fun omega =>
        (if omega ∈ condition then left omega else right omega).preEndpointWorkload i) =
        fun omega => if omega ∈ condition then (left omega).preEndpointWorkload i
          else (right omega).preEndpointWorkload i := by
      funext omega
      split <;> rfl
    rw [hformula]
    exact Measurable.ite hcondition (hleftPre i) (hrightPre i)
  · intro i
    change Measurable (fun omega =>
      (if omega ∈ condition then left omega else right omega).endpointBatch i)
    have hformula : (fun omega =>
        (if omega ∈ condition then left omega else right omega).endpointBatch i) =
        fun omega => if omega ∈ condition then (left omega).endpointBatch i
          else (right omega).endpointBatch i := by
      funext omega
      split <;> rfl
    rw [hformula]
    exact Measurable.ite hcondition (hleftBatch i) (hrightBatch i)
  · intro i
    change Measurable (fun omega =>
      (if omega ∈ condition then left omega else right omega).endpointWorkload i)
    have hformula : (fun omega =>
        (if omega ∈ condition then left omega else right omega).endpointWorkload i) =
        fun omega => if omega ∈ condition then (left omega).endpointWorkload i
          else (right omega).endpointWorkload i := by
      funext omega
      split <;> rfl
    rw [hformula]
    exact Measurable.ite hcondition (hleftEndpoint i) (hrightEndpoint i)
  · change Measurable (fun omega =>
      (if omega ∈ condition then left omega else right omega).endpointIsExternalBatch)
    have hformula : (fun omega =>
        (if omega ∈ condition then left omega else right omega).endpointIsExternalBatch) =
        fun omega => if omega ∈ condition then (left omega).endpointIsExternalBatch
          else (right omega).endpointIsExternalBatch := by
      funext omega
      split <;> rfl
    rw [hformula]
    exact Measurable.ite hcondition hleftExternal hrightExternal

/-- One executable GPS segment has Borel scalar coordinates whenever its
input workload, pending batch, time, and delay coordinates are Borel. -/
theorem finiteGPSExecutionSegmentCoordinatesMeasurable_build
    (capacity : ℝ) (weight : Class → ℝ)
    (work batchWork : Omega → Class → ℝ)
    (hwork : ∀ i, Measurable (fun omega => work omega i))
    (hbatchWork : ∀ i, Measurable (fun omega => batchWork omega i))
    (currentTime nextBatchDelay : Omega → ℝ)
    (hcurrentTime : Measurable currentTime)
    (hnextBatchDelay : Measurable nextBatchDelay) :
    FiniteGPSExecutionSegmentCoordinatesMeasurable (fun omega =>
      finiteGPSBuildExecutionSegment capacity weight (work omega)
        (batchWork omega) (currentTime omega) (nextBatchDelay omega)) := by
  let duration : Omega → ℝ := fun omega =>
    finiteGPSNextStepDuration capacity weight (work omega) (nextBatchDelay omega)
  have hduration : Measurable duration :=
    measurable_finiteGPSNextStepDuration_apply capacity weight work hwork
      nextBatchDelay hnextBatchDelay
  have hcondition : MeasurableSet {omega | duration omega = nextBatchDelay omega} := by
    have hzero : MeasurableSet {value : ℝ | value = 0} := measurableSet_eq
    convert hzero.preimage (hduration.sub hnextBatchDelay) using 1
    ext omega
    simp [sub_eq_zero]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [finiteGPSBuildExecutionSegment] using hcurrentTime
  · simpa [finiteGPSBuildExecutionSegment, duration] using hduration
  · intro i
    simpa [finiteGPSBuildExecutionSegment] using hwork i
  · intro i
    simpa [finiteGPSBuildExecutionSegment] using
      (measurable_finiteGPSClassRate_apply capacity weight work hwork i)
  · intro i
    simpa [finiteGPSBuildExecutionSegment, duration] using
      (measurable_finiteGPSServiceIncrement_apply capacity weight work hwork
        duration hduration i)
  · intro i
    simpa [finiteGPSBuildExecutionSegment, duration] using
      (measurable_finiteGPSRemainingAfter_apply capacity weight work hwork
        duration hduration i)
  · intro i
    simpa [finiteGPSBuildExecutionSegment] using
      (measurable_finiteGPSBatchApplied_apply capacity weight work batchWork
        hwork hbatchWork nextBatchDelay hnextBatchDelay i)
  · intro i
    simpa [finiteGPSBuildExecutionSegment] using
      (measurable_finiteGPSNextEventState_apply capacity weight work batchWork
        hwork hbatchWork nextBatchDelay hnextBatchDelay i)
  · have hformula : (fun omega =>
        (finiteGPSBuildExecutionSegment capacity weight (work omega)
          (batchWork omega) (currentTime omega)
          (nextBatchDelay omega)).endpointIsExternalBatch) =
        fun omega => if omega ∈ {omega | duration omega = nextBatchDelay omega}
          then true else false := by
      funext omega
      simp [finiteGPSBuildExecutionSegment, duration]
    rw [hformula]
    exact Measurable.ite hcondition measurable_const measurable_const

/-- Every fixed slot of a bounded executable GPS gap has Borel scalar
coordinates.  Out-of-range slots are represented by the explicit default
segment above, so no variable-length-list measurability is used. -/
theorem finiteGPSExecutionSegmentCoordinatesMeasurable_gapSegmentAt
    (fuel : Nat) (capacity : ℝ) (weight : Class → ℝ)
    (work batchWork : Omega → Class → ℝ)
    (hwork : ∀ i, Measurable (fun omega => work omega i))
    (hbatchWork : ∀ i, Measurable (fun omega => batchWork omega i))
    (currentTime nextBatchDelay : Omega → ℝ)
    (hcurrentTime : Measurable currentTime)
    (hnextBatchDelay : Measurable nextBatchDelay)
    (slot : Nat) :
    FiniteGPSExecutionSegmentCoordinatesMeasurable (fun omega =>
      finiteGPSRunGapSegmentAt fuel capacity weight (work omega)
        (batchWork omega) (currentTime omega) (nextBatchDelay omega) slot) := by
  classical
  induction fuel generalizing work currentTime nextBatchDelay slot with
  | zero =>
      simpa [finiteGPSRunGapSegmentAt, finiteGPSRunGapSegments] using
        (finiteGPSExecutionSegmentCoordinatesMeasurable_const
          (Omega := Omega) (finiteGPSExecutionSegmentDefault (Class := Class)))
  | succ fuel ih =>
      let duration : Omega → ℝ := fun omega =>
        finiteGPSNextStepDuration capacity weight (work omega) (nextBatchDelay omega)
      have hduration : Measurable duration :=
        measurable_finiteGPSNextStepDuration_apply capacity weight work hwork
          nextBatchDelay hnextBatchDelay
      let nextWork : Omega → Class → ℝ := fun omega =>
        finiteGPSNextEventState capacity weight (work omega) (batchWork omega)
          (nextBatchDelay omega)
      have hnextWork : ∀ i, Measurable (fun omega => nextWork omega i) := by
        intro i
        exact measurable_finiteGPSNextEventState_apply capacity weight work batchWork
          hwork hbatchWork nextBatchDelay hnextBatchDelay i
      let nextTime : Omega → ℝ := fun omega => currentTime omega + duration omega
      have hnextTime : Measurable nextTime := hcurrentTime.add hduration
      let remainingDelay : Omega → ℝ := fun omega => nextBatchDelay omega - duration omega
      have hremainingDelay : Measurable remainingDelay := hnextBatchDelay.sub hduration
      have hcondition : MeasurableSet {omega | duration omega = nextBatchDelay omega} := by
        have hzero : MeasurableSet {value : ℝ | value = 0} := measurableSet_eq
        convert hzero.preimage (hduration.sub hnextBatchDelay) using 1
        ext omega
        simp [sub_eq_zero]
      cases slot with
      | zero =>
          have hsegment := finiteGPSExecutionSegmentCoordinatesMeasurable_build
            capacity weight work batchWork hwork hbatchWork currentTime nextBatchDelay
            hcurrentTime hnextBatchDelay
          have hformula : (fun omega =>
              finiteGPSRunGapSegmentAt (fuel + 1) capacity weight (work omega)
                (batchWork omega) (currentTime omega) (nextBatchDelay omega) 0) =
              fun omega => finiteGPSBuildExecutionSegment capacity weight (work omega)
                (batchWork omega) (currentTime omega) (nextBatchDelay omega) := by
            funext omega
            by_cases h : finiteGPSNextStepDuration capacity weight (work omega)
                (nextBatchDelay omega) = nextBatchDelay omega
            · simp [finiteGPSRunGapSegmentAt, finiteGPSRunGapSegments, h]
            · simp [finiteGPSRunGapSegmentAt, finiteGPSRunGapSegments, h]
          rw [hformula]
          exact hsegment
      | succ slot =>
          have htail := ih (work := nextWork) hnextWork (currentTime := nextTime)
            (nextBatchDelay := remainingDelay) hnextTime hremainingDelay slot
          have hdefault := finiteGPSExecutionSegmentCoordinatesMeasurable_const
            (Omega := Omega) (finiteGPSExecutionSegmentDefault (Class := Class))
          have hformula : (fun omega =>
              finiteGPSRunGapSegmentAt (fuel + 1) capacity weight (work omega)
                (batchWork omega) (currentTime omega) (nextBatchDelay omega) (slot + 1)) =
              fun omega => if duration omega = nextBatchDelay omega then
                finiteGPSExecutionSegmentDefault
              else finiteGPSRunGapSegmentAt fuel capacity weight (nextWork omega)
                (batchWork omega) (nextTime omega) (remainingDelay omega) slot := by
            funext omega
            by_cases h : finiteGPSNextStepDuration capacity weight (work omega)
                (nextBatchDelay omega) = nextBatchDelay omega
            · simp [finiteGPSRunGapSegmentAt, finiteGPSRunGapSegments, duration,
                h]
            · simp [finiteGPSRunGapSegmentAt, finiteGPSRunGapSegments, duration,
                nextWork, nextTime, remainingDelay, h]
          rw [hformula]
          exact FiniteGPSExecutionSegmentCoordinatesMeasurable.ite hcondition
            hdefault htail

/-- The same coordinate theorem when the finite GPS fuel is a Borel
natural-valued coordinate.  This uses countable gluing over the concrete fuel
value, while retaining the executable slot accessor rather than a measurable
list-valued history. -/
theorem finiteGPSExecutionSegmentCoordinatesMeasurable_gapSegmentAt_of_measurable_fuel
    (fuel : Omega → Nat) (hfuel : Measurable fuel)
    (capacity : ℝ) (weight : Class → ℝ)
    (work batchWork : Omega → Class → ℝ)
    (hwork : ∀ i, Measurable (fun omega => work omega i))
    (hbatchWork : ∀ i, Measurable (fun omega => batchWork omega i))
    (currentTime nextBatchDelay : Omega → ℝ)
    (hcurrentTime : Measurable currentTime)
    (hnextBatchDelay : Measurable nextBatchDelay)
    (slot : Nat) :
    FiniteGPSExecutionSegmentCoordinatesMeasurable (fun omega =>
      finiteGPSRunGapSegmentAt (fuel omega) capacity weight (work omega)
        (batchWork omega) (currentTime omega) (nextBatchDelay omega) slot) := by
  have hfixed : ∀ fixedFuel : Nat,
      FiniteGPSExecutionSegmentCoordinatesMeasurable (fun omega =>
        finiteGPSRunGapSegmentAt fixedFuel capacity weight (work omega)
          (batchWork omega) (currentTime omega) (nextBatchDelay omega) slot) := by
    intro fixedFuel
    exact finiteGPSExecutionSegmentCoordinatesMeasurable_gapSegmentAt fixedFuel
      capacity weight work batchWork hwork hbatchWork currentTime nextBatchDelay
      hcurrentTime hnextBatchDelay slot
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have huncurry : Measurable (fun pair : Nat × Omega =>
        (finiteGPSRunGapSegmentAt pair.1 capacity weight (work pair.2)
          (batchWork pair.2) (currentTime pair.2) (nextBatchDelay pair.2) slot).startTime) :=
      measurable_from_prod_countable_right fun fixedFuel => (hfixed fixedFuel).1
    simpa using huncurry.comp (hfuel.prodMk measurable_id)
  · have huncurry : Measurable (fun pair : Nat × Omega =>
        (finiteGPSRunGapSegmentAt pair.1 capacity weight (work pair.2)
          (batchWork pair.2) (currentTime pair.2) (nextBatchDelay pair.2) slot).duration) :=
      measurable_from_prod_countable_right fun fixedFuel => (hfixed fixedFuel).2.1
    simpa using huncurry.comp (hfuel.prodMk measurable_id)
  · intro i
    have huncurry : Measurable (fun pair : Nat × Omega =>
        (finiteGPSRunGapSegmentAt pair.1 capacity weight (work pair.2)
          (batchWork pair.2) (currentTime pair.2) (nextBatchDelay pair.2) slot).startWorkload i) :=
      measurable_from_prod_countable_right fun fixedFuel => (hfixed fixedFuel).2.2.1 i
    simpa using huncurry.comp (hfuel.prodMk measurable_id)
  · intro i
    have huncurry : Measurable (fun pair : Nat × Omega =>
        (finiteGPSRunGapSegmentAt pair.1 capacity weight (work pair.2)
          (batchWork pair.2) (currentTime pair.2) (nextBatchDelay pair.2) slot).classRate i) :=
      measurable_from_prod_countable_right fun fixedFuel => (hfixed fixedFuel).2.2.2.1 i
    simpa using huncurry.comp (hfuel.prodMk measurable_id)
  · intro i
    have huncurry : Measurable (fun pair : Nat × Omega =>
        (finiteGPSRunGapSegmentAt pair.1 capacity weight (work pair.2)
          (batchWork pair.2) (currentTime pair.2) (nextBatchDelay pair.2) slot).serviceIncrement i) :=
      measurable_from_prod_countable_right fun fixedFuel => (hfixed fixedFuel).2.2.2.2.1 i
    simpa using huncurry.comp (hfuel.prodMk measurable_id)
  · intro i
    have huncurry : Measurable (fun pair : Nat × Omega =>
        (finiteGPSRunGapSegmentAt pair.1 capacity weight (work pair.2)
          (batchWork pair.2) (currentTime pair.2) (nextBatchDelay pair.2) slot).preEndpointWorkload i) :=
      measurable_from_prod_countable_right fun fixedFuel => (hfixed fixedFuel).2.2.2.2.2.1 i
    simpa using huncurry.comp (hfuel.prodMk measurable_id)
  · intro i
    have huncurry : Measurable (fun pair : Nat × Omega =>
        (finiteGPSRunGapSegmentAt pair.1 capacity weight (work pair.2)
          (batchWork pair.2) (currentTime pair.2) (nextBatchDelay pair.2) slot).endpointBatch i) :=
      measurable_from_prod_countable_right fun fixedFuel => (hfixed fixedFuel).2.2.2.2.2.2.1 i
    simpa using huncurry.comp (hfuel.prodMk measurable_id)
  · intro i
    have huncurry : Measurable (fun pair : Nat × Omega =>
        (finiteGPSRunGapSegmentAt pair.1 capacity weight (work pair.2)
          (batchWork pair.2) (currentTime pair.2) (nextBatchDelay pair.2) slot).endpointWorkload i) :=
      measurable_from_prod_countable_right fun fixedFuel => (hfixed fixedFuel).2.2.2.2.2.2.2.1 i
    simpa using huncurry.comp (hfuel.prodMk measurable_id)
  · have huncurry : Measurable (fun pair : Nat × Omega =>
        (finiteGPSRunGapSegmentAt pair.1 capacity weight (work pair.2)
          (batchWork pair.2) (currentTime pair.2) (nextBatchDelay pair.2) slot).endpointIsExternalBatch) :=
      measurable_from_prod_countable_right fun fixedFuel => (hfixed fixedFuel).2.2.2.2.2.2.2.2
    simpa using huncurry.comp (hfuel.prodMk measurable_id)

end

end AppliedModelingLib.Probability.Queueing

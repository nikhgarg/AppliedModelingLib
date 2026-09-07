import AppliedModelingLib.Queueing.GPS.FiniteHorizon.BatchTrace
import Mathlib.Tactic

/-!
# Borel primitives for finite-horizon GPS execution

The executable finite GPS kernel is built from finitely many comparisons,
arithmetic operations, and finite minima.  This module starts the Borel API at
the one-event layer.  It is intentionally independent of any paper source or
arrival enumeration.
-/

namespace AppliedModelingLib.Probability.Queueing

open scoped BigOperators

noncomputable section

variable {Class Ω : Type*} [Fintype Class] [DecidableEq Class]
  [MeasurableSpace Ω]

private theorem measurable_finset_inf'_apply
    (s : Finset Class) (hs : s.Nonempty)
    (f : Ω → Class → ℝ) (hf : ∀ i, Measurable fun ω => f ω i) :
    Measurable fun ω => s.inf' hs (fun i => f ω i) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i =>
      simpa using hf i
  | cons i s hi hs ih =>
      have heq : (fun ω =>
          (Finset.cons i s hi).inf' (Finset.cons_nonempty hi)
            (fun j => f ω j)) =
          fun ω => min (f ω i) (s.inf' hs (fun j => f ω j)) := by
        funext ω
        rw [Finset.inf'_cons hs]
      rw [heq]
      exact (hf i).min ih

/-- The finite GPS backlog Boolean is measurable whenever every workload
coordinate is measurable. -/
theorem measurable_finiteGPSBacklogged_apply
    (work : Ω → Class → ℝ) (hwork : ∀ i, Measurable fun ω => work ω i)
    (t : ℝ) (i : Class) :
    Measurable fun ω => finiteGPSBacklogged (work ω) t i := by
  unfold finiteGPSBacklogged
  exact Measurable.ite
    (measurableSet_lt measurable_const (hwork i))
    measurable_const measurable_const

/-- A finite GPS class rate is measurable as a function of a measurable
workload vector.  The denominator is expanded as a finite sum of measurable
backlog tests, rather than treated as an opaque scheduler statistic. -/
theorem measurable_finiteGPSClassRate_apply
    (capacity : ℝ) (weight : Class → ℝ)
    (work : Ω → Class → ℝ) (hwork : ∀ i, Measurable fun ω => work ω i)
    (i : Class) :
    Measurable fun ω => finiteGPSClassRate capacity weight (work ω) i := by
  have hactive : ∀ j : Class, MeasurableSet {ω | 0 < work ω j} := by
    intro j
    exact measurableSet_lt measurable_const (hwork j)
  have hsum : Measurable (fun ω =>
      (Finset.univ : Finset Class).sum
        (fun j => if 0 < work ω j then weight j else 0)) := by
    exact Finset.measurable_sum Finset.univ fun j _ =>
      Measurable.ite (hactive j) measurable_const measurable_const
  have hweight_sum : Measurable (fun ω =>
      gpsBackloggedWeightSum Class weight
        (finiteGPSBacklogged (work ω)) 0) := by
    convert hsum using 1
    funext ω
    simp [gpsBackloggedWeightSum, gpsBackloggedClasses, finiteGPSBacklogged,
      Finset.sum_filter]
  have hbacklogged_rate : Measurable (fun ω =>
      gpsBackloggedClassRate Class i capacity weight
        (finiteGPSBacklogged (work ω)) 0) := by
    unfold gpsBackloggedClassRate idealGPSClassRate
    exact (measurable_const : Measurable (fun _ : Ω => capacity * weight i)).div
      hweight_sum
  simpa [finiteGPSClassRate] using
    (Measurable.ite (hactive i) hbacklogged_rate measurable_const)

/-- Remaining work after a finite GPS event is measurable in all measurable
workload coordinates and in a measurable duration. -/
theorem measurable_finiteGPSRemainingAfter_apply
    (capacity : ℝ) (weight : Class → ℝ)
    (work : Ω → Class → ℝ) (hwork : ∀ i, Measurable fun ω => work ω i)
    (duration : Ω → ℝ) (hduration : Measurable duration) (i : Class) :
    Measurable fun ω =>
      finiteGPSRemainingAfter capacity weight (work ω) (duration ω) i := by
  unfold finiteGPSRemainingAfter
  exact measurable_const.max
    ((hwork i).sub
      ((measurable_finiteGPSClassRate_apply capacity weight work hwork i).mul
        hduration))

/-- A finite GPS service increment is measurable in the same data as its
remaining-work update. -/
theorem measurable_finiteGPSServiceIncrement_apply
    (capacity : ℝ) (weight : Class → ℝ)
    (work : Ω → Class → ℝ) (hwork : ∀ i, Measurable fun ω => work ω i)
    (duration : Ω → ℝ) (hduration : Measurable duration) (i : Class) :
    Measurable fun ω =>
      finiteGPSServiceIncrement capacity weight (work ω) (duration ω) i := by
  unfold finiteGPSServiceIncrement
  exact (hwork i).sub
    (measurable_finiteGPSRemainingAfter_apply capacity weight work hwork
      duration hduration i)

/-- A single class's hypothetical emptying delay is measurable in a
measurable workload vector. -/
theorem measurable_finiteGPSClassEmptyDelay_apply
    (capacity : ℝ) (weight : Class → ℝ)
    (work : Ω → Class → ℝ) (hwork : ∀ i, Measurable fun ω => work ω i)
    (i : Class) :
    Measurable fun ω => finiteGPSClassEmptyDelay capacity weight (work ω) i := by
  unfold finiteGPSClassEmptyDelay
  exact (hwork i).div
    (measurable_finiteGPSClassRate_apply capacity weight work hwork i)

/-- The earliest finite GPS emptying delay is a finite piecewise minimum of
measurable class delays.  The active-set profile is a finite Boolean state,
so this proof does not assume a measurable finite-set representation. -/
theorem measurable_finiteGPSEarliestEmptyDelay_apply
    (capacity : ℝ) (weight : Class → ℝ)
    (work : Ω → Class → ℝ) (hwork : ∀ i, Measurable fun ω => work ω i) :
    Measurable fun ω => finiteGPSEarliestEmptyDelay capacity weight (work ω) := by
  let profile : Ω → Class → Bool := fun ω i => decide (0 < work ω i)
  have hprofile : Measurable profile := by
    refine measurable_pi_iff.2 fun i => ?_
    exact measurable_finiteGPSBacklogged_apply work hwork 0 i
  let delay : Ω → Class → ℝ := fun ω i =>
    finiteGPSClassEmptyDelay capacity weight (work ω) i
  have hdelay : ∀ i, Measurable fun ω => delay ω i := by
    intro i
    exact measurable_finiteGPSClassEmptyDelay_apply capacity weight work hwork i
  have hfiber : ∀ p : Class → Bool, Measurable (fun ω =>
      if hactive : (Finset.univ.filter fun i => p i = true).Nonempty then
        (Finset.univ.filter fun i => p i = true).inf' hactive (fun i => delay ω i)
      else 0) := by
    intro p
    by_cases hactive : (Finset.univ.filter fun i => p i = true).Nonempty
    · simp only [dif_pos hactive]
      exact measurable_finset_inf'_apply _ hactive delay hdelay
    · simp [hactive]
  have hpiece : Measurable (fun q : (Class → Bool) × Ω =>
      if hactive : (Finset.univ.filter fun i => q.1 i = true).Nonempty then
        (Finset.univ.filter fun i => q.1 i = true).inf' hactive (fun i => delay q.2 i)
      else 0) :=
    measurable_from_prod_countable_right hfiber
  have hcomp := hpiece.comp (hprofile.prodMk measurable_id)
  have heq : (fun ω =>
      if hactive : (Finset.univ.filter fun i => profile ω i = true).Nonempty then
        (Finset.univ.filter fun i => profile ω i = true).inf' hactive
          (fun i => delay ω i)
      else 0) =
      fun ω => finiteGPSEarliestEmptyDelay capacity weight (work ω) := by
    funext ω
    simp [finiteGPSEarliestEmptyDelay, finiteGPSActiveClasses, profile, delay]
  change Measurable (fun ω =>
    if hactive : (Finset.univ.filter fun i => profile ω i = true).Nonempty then
      (Finset.univ.filter fun i => profile ω i = true).inf' hactive
        (fun i => delay ω i)
    else 0) at hcomp
  rw [heq] at hcomp
  exact hcomp

/-- The finite active-set nonemptiness test is measurable in a measurable
workload vector. -/
theorem measurableSet_finiteGPSActiveClasses_nonempty
    (work : Ω → Class → ℝ) (hwork : ∀ i, Measurable fun ω => work ω i) :
    MeasurableSet {ω | (finiteGPSActiveClasses (work ω)).Nonempty} := by
  have hunion : MeasurableSet (⋃ i : Class, {ω | 0 < work ω i}) := by
    exact MeasurableSet.iUnion fun i =>
      measurableSet_lt measurable_const (hwork i)
  convert hunion using 1
  ext ω
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  change (Finset.univ.filter fun i => 0 < work ω i).Nonempty ↔ _
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, (Finset.mem_filter.mp hi).2⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩

/-- The next finite GPS event time is measurable in the workload and the
pending external-batch delay. -/
theorem measurable_finiteGPSNextStepDuration_apply
    (capacity : ℝ) (weight : Class → ℝ)
    (work : Ω → Class → ℝ) (hwork : ∀ i, Measurable fun ω => work ω i)
    (nextBatchDelay : Ω → ℝ) (hnextBatchDelay : Measurable nextBatchDelay) :
    Measurable fun ω =>
      finiteGPSNextStepDuration capacity weight (work ω) (nextBatchDelay ω) := by
  unfold finiteGPSNextStepDuration
  exact Measurable.ite
    (measurableSet_finiteGPSActiveClasses_nonempty work hwork)
    (hnextBatchDelay.min
      (measurable_finiteGPSEarliestEmptyDelay_apply capacity weight work hwork))
    hnextBatchDelay

/-- The external batch applied at the next GPS event is measurable in the
same finite data. -/
theorem measurable_finiteGPSBatchApplied_apply
    (capacity : ℝ) (weight : Class → ℝ)
    (work batchWork : Ω → Class → ℝ)
    (hwork : ∀ i, Measurable fun ω => work ω i)
    (hbatchWork : ∀ i, Measurable fun ω => batchWork ω i)
    (nextBatchDelay : Ω → ℝ) (hnextBatchDelay : Measurable nextBatchDelay)
    (i : Class) :
    Measurable fun ω => finiteGPSBatchApplied capacity weight (work ω)
      (batchWork ω) (nextBatchDelay ω) i := by
  let duration : Ω → ℝ := fun ω =>
    finiteGPSNextStepDuration capacity weight (work ω) (nextBatchDelay ω)
  have hduration : Measurable duration :=
    measurable_finiteGPSNextStepDuration_apply capacity weight work hwork
      nextBatchDelay hnextBatchDelay
  have hcondition : MeasurableSet {ω | duration ω = nextBatchDelay ω} := by
    have hzero : MeasurableSet {x : ℝ | x = 0} := measurableSet_eq
    convert hzero.preimage (hduration.sub hnextBatchDelay) using 1
    ext ω
    simp [sub_eq_zero]
  unfold finiteGPSBatchApplied
  have heq : (fun ω =>
      (if finiteGPSNextStepDuration capacity weight (work ω) (nextBatchDelay ω) =
          nextBatchDelay ω then batchWork ω else fun _ : Class => 0) i) =
      fun ω => if duration ω = nextBatchDelay ω then batchWork ω i else 0 := by
    funext ω
    exact ite_apply _ _ _ _
  rw [heq]
  simpa [duration] using
    (Measurable.ite hcondition (hbatchWork i)
      (measurable_const : Measurable (fun _ : Ω => (0 : ℝ))))

/-- The one-event workload update is measurable in measurable workload,
batch, and delay inputs. -/
theorem measurable_finiteGPSNextEventState_apply
    (capacity : ℝ) (weight : Class → ℝ)
    (work batchWork : Ω → Class → ℝ)
    (hwork : ∀ i, Measurable fun ω => work ω i)
    (hbatchWork : ∀ i, Measurable fun ω => batchWork ω i)
    (nextBatchDelay : Ω → ℝ) (hnextBatchDelay : Measurable nextBatchDelay)
    (i : Class) :
    Measurable fun ω => finiteGPSNextEventState capacity weight (work ω)
      (batchWork ω) (nextBatchDelay ω) i := by
  let duration : Ω → ℝ := fun ω =>
    finiteGPSNextStepDuration capacity weight (work ω) (nextBatchDelay ω)
  have hduration : Measurable duration :=
    measurable_finiteGPSNextStepDuration_apply capacity weight work hwork
      nextBatchDelay hnextBatchDelay
  unfold finiteGPSNextEventState
  exact (measurable_finiteGPSRemainingAfter_apply capacity weight work hwork
    duration hduration i).add
      (measurable_finiteGPSBatchApplied_apply capacity weight work batchWork
        hwork hbatchWork nextBatchDelay hnextBatchDelay i)

/-- Coordinatewise measurability package for a finite GPS gap computation.
Keeping the four output fields explicit avoids inventing a measurable-space
instance for the execution record merely to state the recursive Borel fact. -/
def FiniteGPSGapRunResultMeasurable
    (result : Ω → FiniteGPSGapRunResult Class) : Prop :=
  (∀ i, Measurable fun ω => (result ω).workload i) ∧
    Measurable (fun ω => (result ω).remainingDelay) ∧
      (∀ i, Measurable fun ω => (result ω).service i) ∧
        Measurable (fun ω => (result ω).batchApplied)

/-- A bounded finite GPS gap computation is Borel in its measurable input
workload, batch, and delay coordinates.  The proof follows the executable
fuel recursion, including its actual external-batch test. -/
theorem finiteGPSGapRunResultMeasurable_apply
    (fuel : ℕ) (capacity : ℝ) (weight : Class → ℝ)
    (work batchWork : Ω → Class → ℝ)
    (hwork : ∀ i, Measurable fun ω => work ω i)
    (hbatchWork : ∀ i, Measurable fun ω => batchWork ω i)
    (nextBatchDelay : Ω → ℝ) (hnextBatchDelay : Measurable nextBatchDelay) :
    FiniteGPSGapRunResultMeasurable (fun ω =>
      finiteGPSRunGap fuel capacity weight (work ω) (batchWork ω)
        (nextBatchDelay ω)) := by
  induction fuel generalizing work nextBatchDelay with
  | zero =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i
        simpa [FiniteGPSGapRunResultMeasurable, finiteGPSRunGap] using hwork i
      · simpa [FiniteGPSGapRunResultMeasurable, finiteGPSRunGap] using hnextBatchDelay
      · intro i
        simp [finiteGPSRunGap]
      · simp [finiteGPSRunGap]
  | succ fuel ih =>
      let duration : Ω → ℝ := fun ω =>
        finiteGPSNextStepDuration capacity weight (work ω) (nextBatchDelay ω)
      have hduration : Measurable duration :=
        measurable_finiteGPSNextStepDuration_apply capacity weight work hwork
          nextBatchDelay hnextBatchDelay
      let nextWork : Ω → Class → ℝ := fun ω =>
        finiteGPSNextEventState capacity weight (work ω) (batchWork ω)
          (nextBatchDelay ω)
      have hnextWork : ∀ i, Measurable fun ω => nextWork ω i := by
        intro i
        exact measurable_finiteGPSNextEventState_apply capacity weight work batchWork
          hwork hbatchWork nextBatchDelay hnextBatchDelay i
      let stepService : Ω → Class → ℝ := fun ω =>
        finiteGPSServiceIncrement capacity weight (work ω) (duration ω)
      have hstepService : ∀ i, Measurable fun ω => stepService ω i := by
        intro i
        exact measurable_finiteGPSServiceIncrement_apply capacity weight work hwork
          duration hduration i
      let remainingDelay : Ω → ℝ := fun ω => nextBatchDelay ω - duration ω
      have hremainingDelay : Measurable remainingDelay := hnextBatchDelay.sub hduration
      have htail := ih (work := nextWork) (nextBatchDelay := remainingDelay)
        hnextWork hremainingDelay
      have hcondition : MeasurableSet {ω | duration ω = nextBatchDelay ω} := by
        have hzero : MeasurableSet {x : ℝ | x = 0} := measurableSet_eq
        convert hzero.preimage (hduration.sub hnextBatchDelay) using 1
        ext ω
        simp [sub_eq_zero]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i
        have hformula : (fun ω =>
            (finiteGPSRunGap (fuel + 1) capacity weight (work ω) (batchWork ω)
              (nextBatchDelay ω)).workload i) =
            fun ω => if duration ω = nextBatchDelay ω then nextWork ω i else
              (finiteGPSRunGap fuel capacity weight (nextWork ω) (batchWork ω)
                (remainingDelay ω)).workload i := by
          funext ω
          simp [finiteGPSRunGap, duration, nextWork, remainingDelay]
          split <;> rfl
        rw [hformula]
        exact Measurable.ite hcondition (hnextWork i) ((htail.1) i)
      · have hformula : (fun ω =>
            (finiteGPSRunGap (fuel + 1) capacity weight (work ω) (batchWork ω)
              (nextBatchDelay ω)).remainingDelay) =
            fun ω => if duration ω = nextBatchDelay ω then 0 else
              (finiteGPSRunGap fuel capacity weight (nextWork ω) (batchWork ω)
                (remainingDelay ω)).remainingDelay := by
          funext ω
          simp [finiteGPSRunGap, duration, nextWork, remainingDelay]
          split <;> rfl
        rw [hformula]
        exact Measurable.ite hcondition
          (measurable_const : Measurable fun _ : Ω => (0 : ℝ)) htail.2.1
      · intro i
        have hformula : (fun ω =>
            (finiteGPSRunGap (fuel + 1) capacity weight (work ω) (batchWork ω)
              (nextBatchDelay ω)).service i) =
            fun ω => if duration ω = nextBatchDelay ω then stepService ω i else
              stepService ω i +
                (finiteGPSRunGap fuel capacity weight (nextWork ω) (batchWork ω)
                  (remainingDelay ω)).service i := by
          funext ω
          simp [finiteGPSRunGap, duration, nextWork, stepService, remainingDelay]
          split <;> rfl
        rw [hformula]
        exact Measurable.ite hcondition (hstepService i)
          ((hstepService i).add (htail.2.2.1 i))
      · have hformula : (fun ω =>
            (finiteGPSRunGap (fuel + 1) capacity weight (work ω) (batchWork ω)
              (nextBatchDelay ω)).batchApplied) =
            fun ω => if duration ω = nextBatchDelay ω then true else
              (finiteGPSRunGap fuel capacity weight (nextWork ω) (batchWork ω)
                (remainingDelay ω)).batchApplied := by
          funext ω
          by_cases h : duration ω = nextBatchDelay ω
          · simp [finiteGPSRunGap, duration, h]
          · simp [finiteGPSRunGap, duration, nextWork, remainingDelay, h]
        rw [hformula]
        exact Measurable.ite hcondition
          (measurable_const : Measurable fun _ : Ω => true) htail.2.2.2

/-- The active-class count is a measurable natural-valued function of a
measurable workload vector. -/
theorem measurable_finiteGPSActiveClasses_card_apply
    (work : Ω → Class → ℝ) (hwork : ∀ i, Measurable fun ω => work ω i) :
    Measurable fun ω => (finiteGPSActiveClasses (work ω)).card := by
  have hsum : Measurable (fun ω =>
      (Finset.univ : Finset Class).sum
        (fun i => if 0 < work ω i then 1 else 0)) := by
    exact Finset.measurable_sum Finset.univ fun i _ =>
      Measurable.ite (measurableSet_lt measurable_const (hwork i))
        measurable_const measurable_const
  convert hsum using 1
  funext ω
  unfold finiteGPSActiveClasses
  exact Finset.card_filter _ _

/-- The gap-run Borel package also holds when the finite fuel is a measurable
natural-valued input.  This is the form required by the executable runner,
whose fuel is the current active-class cardinality plus one. -/
theorem finiteGPSGapRunResultMeasurable_apply_of_measurable_fuel
    (fuel : Ω → ℕ) (hfuel : Measurable fuel)
    (capacity : ℝ) (weight : Class → ℝ)
    (work batchWork : Ω → Class → ℝ)
    (hwork : ∀ i, Measurable fun ω => work ω i)
    (hbatchWork : ∀ i, Measurable fun ω => batchWork ω i)
    (nextBatchDelay : Ω → ℝ) (hnextBatchDelay : Measurable nextBatchDelay) :
    FiniteGPSGapRunResultMeasurable (fun ω =>
      finiteGPSRunGap (fuel ω) capacity weight (work ω) (batchWork ω)
        (nextBatchDelay ω)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    have huncurry : Measurable (fun q : ℕ × Ω =>
        (finiteGPSRunGap q.1 capacity weight (work q.2) (batchWork q.2)
          (nextBatchDelay q.2)).workload i) :=
      measurable_from_prod_countable_right fun n =>
        (finiteGPSGapRunResultMeasurable_apply n capacity weight work batchWork
          hwork hbatchWork nextBatchDelay hnextBatchDelay).1 i
    simpa using huncurry.comp (hfuel.prodMk measurable_id)
  · have huncurry : Measurable (fun q : ℕ × Ω =>
        (finiteGPSRunGap q.1 capacity weight (work q.2) (batchWork q.2)
          (nextBatchDelay q.2)).remainingDelay) :=
      measurable_from_prod_countable_right fun n =>
        (finiteGPSGapRunResultMeasurable_apply n capacity weight work batchWork
          hwork hbatchWork nextBatchDelay hnextBatchDelay).2.1
    simpa using huncurry.comp (hfuel.prodMk measurable_id)
  · intro i
    have huncurry : Measurable (fun q : ℕ × Ω =>
        (finiteGPSRunGap q.1 capacity weight (work q.2) (batchWork q.2)
          (nextBatchDelay q.2)).service i) :=
      measurable_from_prod_countable_right fun n =>
        (finiteGPSGapRunResultMeasurable_apply n capacity weight work batchWork
          hwork hbatchWork nextBatchDelay hnextBatchDelay).2.2.1 i
    simpa using huncurry.comp (hfuel.prodMk measurable_id)
  · have huncurry : Measurable (fun q : ℕ × Ω =>
        (finiteGPSRunGap q.1 capacity weight (work q.2) (batchWork q.2)
          (nextBatchDelay q.2)).batchApplied) :=
      measurable_from_prod_countable_right fun n =>
        (finiteGPSGapRunResultMeasurable_apply n capacity weight work batchWork
          hwork hbatchWork nextBatchDelay hnextBatchDelay).2.2.2
    simpa using huncurry.comp (hfuel.prodMk measurable_id)

/-- Coordinatewise measurability package for a finite external-batch GPS
trace result. -/
def FiniteGPSBatchTraceResultMeasurable
    (result : Ω → FiniteGPSBatchTraceResult Class) : Prop :=
  (∀ i, Measurable fun ω => (result ω).workload i) ∧
    Measurable (fun ω => (result ω).currentTime) ∧
      (∀ i, Measurable fun ω => (result ω).service i)

/-- The raw finite GPS batch runner is Borel for a fixed finite list of
measurable batch-time coordinates and a jointly measurable batch-work
kernel.  No chronological or positivity assumption is needed for this
computability fact; those assumptions remain separate semantic obligations. -/
theorem finiteGPSBatchTraceResultMeasurable_apply
    (capacity : ℝ) (weight : Class → ℝ)
    (batchWork : Ω → ℝ → Class → ℝ)
    (hbatchWork : ∀ i, Measurable (fun p : ℝ × Ω => batchWork p.2 p.1 i))
    (currentTime : Ω → ℝ) (hcurrentTime : Measurable currentTime)
    (work : Ω → Class → ℝ) (hwork : ∀ i, Measurable fun ω => work ω i)
    (times : List (Ω → ℝ))
    (htimes : ∀ time ∈ times, Measurable time) :
    FiniteGPSBatchTraceResultMeasurable (fun ω =>
      finiteGPSRunBatchTrace capacity weight (fun t i => batchWork ω t i)
        (currentTime ω) (work ω) (times.map fun time => time ω)) := by
  induction times generalizing currentTime work with
  | nil =>
      refine ⟨?_, ?_, ?_⟩
      · intro i
        simpa [finiteGPSRunBatchTrace] using hwork i
      · simpa [finiteGPSRunBatchTrace] using hcurrentTime
      · intro i
        simp [finiteGPSRunBatchTrace]
  | cons batchTime times ih =>
      have hbatchTime : Measurable batchTime := htimes batchTime (by simp)
      have htimes_tail : ∀ time ∈ times, Measurable time := by
        intro time htime
        exact htimes time (by simp [htime])
      let batchAt : Ω → Class → ℝ := fun ω i => batchWork ω (batchTime ω) i
      have hbatchAt : ∀ i, Measurable fun ω => batchAt ω i := by
        intro i
        exact (hbatchWork i).comp (hbatchTime.prodMk measurable_id)
      let nextBatchDelay : Ω → ℝ := fun ω => batchTime ω - currentTime ω
      have hnextBatchDelay : Measurable nextBatchDelay := hbatchTime.sub hcurrentTime
      let fuel : Ω → ℕ := fun ω => (finiteGPSActiveClasses (work ω)).card + 1
      have hfuel : Measurable fuel :=
        (measurable_finiteGPSActiveClasses_card_apply work hwork).add measurable_const
      let gap : Ω → FiniteGPSGapRunResult Class := fun ω =>
        finiteGPSRunGap (fuel ω) capacity weight (work ω) (batchAt ω)
          (nextBatchDelay ω)
      have hgap : FiniteGPSGapRunResultMeasurable gap := by
        exact finiteGPSGapRunResultMeasurable_apply_of_measurable_fuel fuel hfuel
          capacity weight work batchAt hwork hbatchAt nextBatchDelay hnextBatchDelay
      have htail := ih (currentTime := batchTime) (work := fun ω => (gap ω).workload)
        hbatchTime hgap.1 htimes_tail
      have hcondition : MeasurableSet {ω | (gap ω).batchApplied = true} :=
        (MeasurableSet.singleton true).preimage hgap.2.2.2
      refine ⟨?_, ?_, ?_⟩
      · intro i
        have hformula : (fun ω =>
            (finiteGPSRunBatchTrace capacity weight (fun t j => batchWork ω t j)
              (currentTime ω) (work ω) ((batchTime :: times).map fun time => time ω)).workload i) =
            fun ω => if (gap ω).batchApplied = true then
              (finiteGPSRunBatchTrace capacity weight (fun t j => batchWork ω t j)
                (batchTime ω) (gap ω).workload (times.map fun time => time ω)).workload i
            else (gap ω).workload i := by
          funext ω
          simp [finiteGPSRunBatchTrace, batchAt, nextBatchDelay, fuel, gap]
          split <;> rfl
        rw [hformula]
        exact Measurable.ite hcondition (htail.1 i) (hgap.1 i)
      · have hformula : (fun ω =>
            (finiteGPSRunBatchTrace capacity weight (fun t j => batchWork ω t j)
              (currentTime ω) (work ω) ((batchTime :: times).map fun time => time ω)).currentTime) =
            fun ω => if (gap ω).batchApplied = true then
              (finiteGPSRunBatchTrace capacity weight (fun t j => batchWork ω t j)
                (batchTime ω) (gap ω).workload (times.map fun time => time ω)).currentTime
            else batchTime ω - (gap ω).remainingDelay := by
          funext ω
          simp [finiteGPSRunBatchTrace, batchAt, nextBatchDelay, fuel, gap]
          split <;> rfl
        rw [hformula]
        exact Measurable.ite hcondition htail.2.1 (hbatchTime.sub hgap.2.1)
      · intro i
        have hformula : (fun ω =>
            (finiteGPSRunBatchTrace capacity weight (fun t j => batchWork ω t j)
              (currentTime ω) (work ω) ((batchTime :: times).map fun time => time ω)).service i) =
            fun ω => if (gap ω).batchApplied = true then
              (gap ω).service i +
                (finiteGPSRunBatchTrace capacity weight (fun t j => batchWork ω t j)
                  (batchTime ω) (gap ω).workload (times.map fun time => time ω)).service i
            else (gap ω).service i := by
          funext ω
          simp [finiteGPSRunBatchTrace, batchAt, nextBatchDelay, fuel, gap]
          split <;> rfl
        rw [hformula]
        exact Measurable.ite hcondition ((hgap.2.2.1 i).add (htail.2.2 i))
          (hgap.2.2.1 i)

end

end AppliedModelingLib.Probability.Queueing

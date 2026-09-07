import AppliedModelingLib.Foundations.Probability.ExponentialRateScaling
import AppliedModelingLib.Foundations.Probability.ExponentialMoments
import AppliedModelingLib.Queueing.Lindley.RemotePastCutoff
import AppliedModelingLib.Foundations.Probability.MulticlassStationaryPoisson
import AppliedModelingLib.Foundations.Probability.PalmCampbell
import AppliedModelingLib.Foundations.Probability.PalmTaggedPoissonWorkFutureRate
import AppliedModelingLib.Foundations.Probability.StationaryPoissonWorkPastRate
import AppliedModelingLib.Foundations.Probability.StationaryPoissonWorkPastSquareRate
import AppliedModelingLib.Foundations.Probability.StationaryPoissonWorkFutureRate
import AppliedModelingLib.Queueing.NonpreemptivePriorityClassDependentUniformization
import AppliedModelingLib.Queueing.MulticlassPalmInput

/-!
# Stationary finite-class priority-queue input

This module adapts the existing finite independent stationary marked-Poisson
carrier to class-specific exponential service requirements.  It provides input
laws only: a queue-state evolution and its stationary response law are proved
in later layers.
-/

namespace AppliedModelingLib
namespace Queueing

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

noncomputable section

variable {Class : Type*} [Fintype Class]

local instance stationaryPriorityInputDecidableEq : DecidableEq Class := Classical.decEq Class

/-- The work requirement of a class-labelled arrival when its class has the
given positive mean service requirement.  It scales the concrete unit-rate
exponential mark on the stationary multiclass input carrier. -/
def stationaryPriorityWorkRequirement
    (meanService : Class → ℝ) (i : Class) :
    (Class → (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ))) → ℤ → ℝ :=
  fun omega n => meanService i *
    Probability.PoissonProcess.multiclassStationaryPoissonWorkRequirement i omega n

/-- Total scaled work of class-`i` arrivals in the literal stationary time
window `[-t, 0)`. -/
def stationaryPriorityPastWorkAggregate
    (meanService : Class → ℝ) (i : Class) :
    (Class → (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ))) → ℝ → ℝ :=
  fun omega t =>
    (Probability.PoissonProcess.suspensionBaseArrivalIndices (-t) 0 (omega i).1).sum
      (stationaryPriorityWorkRequirement meanService i omega)

/-- A class's stationary past aggregate is its mean-service scaling times
the underlying literal marked-Poisson past aggregate. -/
theorem stationaryPriorityPastWorkAggregate_eq
    (meanService : Class → ℝ) (i : Class)
    (omega : Class →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ))) (t : ℝ) :
    stationaryPriorityPastWorkAggregate meanService i omega t =
      meanService i * Probability.Queueing.stationaryPoissonWorkPastAggregate (omega i) t := by
  unfold stationaryPriorityPastWorkAggregate
    Probability.Queueing.stationaryPoissonWorkPastAggregate
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp [stationaryPriorityWorkRequirement,
    Probability.PoissonProcess.multiclassStationaryPoissonWorkRequirement,
    Probability.Queueing.stationaryPoissonWorkRequirement]

/-- Total squared scaled work of class-`i` arrivals in the literal stationary
time window `[-t, 0)`. -/
def stationaryPriorityPastSquareWorkAggregate
    (meanService : Class → ℝ) (i : Class) :
    (Class → (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ))) → ℝ → ℝ :=
  fun omega t =>
    (Probability.PoissonProcess.suspensionBaseArrivalIndices (-t) 0 (omega i).1).sum
      (fun n => (stationaryPriorityWorkRequirement meanService i omega n) ^ 2)

/-- A class's scaled squared-mark reward is the square of its service scale
times the underlying unit-mark reward. -/
theorem stationaryPriorityPastSquareWorkAggregate_eq
    (meanService : Class → ℝ) (i : Class)
    (omega : Class →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ))) (t : ℝ) :
    stationaryPriorityPastSquareWorkAggregate meanService i omega t =
      meanService i ^ 2 *
        Probability.Queueing.stationaryPoissonWorkPastSquareAggregate (omega i) t := by
  unfold stationaryPriorityPastSquareWorkAggregate
    Probability.Queueing.stationaryPoissonWorkPastSquareAggregate
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp [stationaryPriorityWorkRequirement,
    Probability.PoissonProcess.multiclassStationaryPoissonWorkRequirement,
    Probability.Queueing.stationaryPoissonWorkRequirement]
  ring

/-- A scaled marked-Poisson input accumulates measurable work over a literal
finite past window, even when the left endpoint is supplied as a coordinate.
The proof represents the random finite arrival set by its two measurable
crossing indices, so it can be composed with either a deterministic or a
random horizon without re-elaborating a multiclass finite sum. -/
theorem measurable_scaledStationaryPoissonWorkWindow
    (meanService : ℝ) :
    Measurable (fun x : ℝ ×
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) =>
        (Probability.PoissonProcess.suspensionBaseArrivalIndices (-x.1) 0 x.2.1).sum
          (fun n => meanService * x.2.2 n)) := by
  classical
  let state : (ℝ ×
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ))) → ℤ × ℤ := fun x =>
    (Probability.PoissonProcess.suspensionCrossingIndexPastClosed (-x.1) x.2.1.1,
      Probability.PoissonProcess.suspensionCrossingIndexPastClosed 0 x.2.1.1)
  let indices : ℤ × ℤ → Finset ℤ := fun n => Finset.Icc n.1 n.2
  have hstate : Measurable state := by
    exact
      (Probability.PoissonProcess.measurable_uncurry_suspensionCrossingIndexPastClosed.comp
        (measurable_fst.neg.prodMk
          (measurable_subtype_coe.comp (measurable_fst.comp measurable_snd)))).prodMk
      ((Probability.PoissonProcess.measurable_suspensionCrossingIndexPastClosed 0).comp
        (measurable_subtype_coe.comp (measurable_fst.comp measurable_snd)))
  let selected : (ℝ ×
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ))) → ℤ → Bool := fun x n =>
    decide (-x.1 ≤ Probability.PoissonProcess.suspensionBaseArrival x.2.1 n ∧
      Probability.PoissonProcess.suspensionBaseArrival x.2.1 n < 0)
  have hselected : Measurable selected := by
    refine measurable_pi_iff.2 fun n => ?_
    change Measurable (fun x : ℝ ×
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) => if
      -x.1 ≤ Probability.PoissonProcess.suspensionBaseArrival x.2.1 n ∧
        Probability.PoissonProcess.suspensionBaseArrival x.2.1 n < 0
      then true else false)
    have harrival : Measurable (fun x : ℝ ×
        (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) =>
        Probability.PoissonProcess.suspensionBaseArrival x.2.1 n) :=
      (Probability.PoissonProcess.measurable_suspensionBaseArrival n).comp
        (measurable_fst.comp measurable_snd)
    have hleft : MeasurableSet {x : ℝ ×
        (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) |
        -x.1 ≤ Probability.PoissonProcess.suspensionBaseArrival x.2.1 n} :=
      measurableSet_le measurable_fst.neg harrival
    have hright : MeasurableSet {x : ℝ ×
        (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) |
        Probability.PoissonProcess.suspensionBaseArrival x.2.1 n < 0} :=
      measurableSet_lt harrival measurable_const
    exact Measurable.ite (hleft.inter hright) measurable_const measurable_const
  let weight : (ℝ ×
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ))) → ℤ → ℝ := fun x n =>
    meanService * x.2.2 n
  have hweight : Measurable weight := by
    refine measurable_pi_iff.2 fun n => ?_
    change Measurable (fun x : ℝ ×
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) =>
        meanService * x.2.2 n)
    exact measurable_const.mul
      ((measurable_pi_apply n).comp (measurable_snd.comp measurable_snd))
  have hsum : Measurable (fun x => ∑ n ∈ indices (state x),
      if selected x n = true then weight x n else 0) :=
    Probability.Palm.measurable_sum_from_countable_parameter
      (Ω := ℝ × (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
      (κ := ℤ × ℤ) state hstate indices selected hselected weight hweight
  convert hsum using 1
  funext x
  simp only [state, indices, selected, weight,
    Probability.PoissonProcess.suspensionBaseArrivalIndices,
    Finset.sum_filter, decide_eq_true_eq]

/-- A class's work aggregate remains measurable when the left endpoint of its
past window is fixed.  This is the stationary-input kernel composed with the
class projection. -/
theorem measurable_stationaryPriorityPastWorkAggregate
    (meanService : Class → ℝ) (i : Class) (t : ℝ) :
    Measurable (fun omega :
      Class → (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) =>
        stationaryPriorityPastWorkAggregate meanService i omega t) := by
  simpa [stationaryPriorityPastWorkAggregate, stationaryPriorityWorkRequirement,
    Probability.PoissonProcess.multiclassStationaryPoissonWorkRequirement,
    Probability.Queueing.stationaryPoissonWorkRequirement] using
    (measurable_scaledStationaryPoissonWorkWindow (meanService i)).comp
      (measurable_const.prodMk (measurable_pi_apply i))

/-- A class's work aggregate remains measurable when the left endpoint of its
past window is a measurable random horizon.  This is the same stationary-input
kernel, composed with the joint horizon and class-input coordinate. -/
theorem measurable_stationaryPriorityPastWorkAggregate_comp
    (meanService : Class → ℝ) (i : Class)
    (horizon : (Class →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ))) → ℝ)
    (hhorizon : Measurable horizon) :
    Measurable (fun omega :
      Class → (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) =>
        stationaryPriorityPastWorkAggregate meanService i omega (horizon omega)) := by
  simpa [stationaryPriorityPastWorkAggregate, stationaryPriorityWorkRequirement,
    Probability.PoissonProcess.multiclassStationaryPoissonWorkRequirement,
    Probability.Queueing.stationaryPoissonWorkRequirement] using
    (measurable_scaledStationaryPoissonWorkWindow (meanService i)).comp
      (hhorizon.prodMk (measurable_pi_apply i))

/-- A scaled stationary marked-Poisson input accumulates measurable work over
a literal finite future window when its right endpoint is supplied as a
coordinate.  The finite ledger is represented by its measurable crossing
labels and the right-closed membership predicate. -/
theorem measurable_scaledStationaryPoissonWorkFutureWindow
    (meanService : ℝ) :
    Measurable (fun x : ℝ ×
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) =>
        (Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0 x.1 x.2.1).sum
          (fun n => meanService * x.2.2 n)) := by
  classical
  let state : (ℝ ×
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ))) → ℤ × ℤ := fun x =>
    (Probability.PoissonProcess.suspensionCrossingIndexPastClosed 0 x.2.1.1,
      Probability.PoissonProcess.suspensionCrossingIndexPastClosed x.1 x.2.1.1)
  let indices : ℤ × ℤ → Finset ℤ := fun n => Finset.Icc n.1 n.2
  have hstate : Measurable state := by
    exact
      ((Probability.PoissonProcess.measurable_suspensionCrossingIndexPastClosed 0).comp
        (measurable_subtype_coe.comp (measurable_fst.comp measurable_snd))).prodMk
      (Probability.PoissonProcess.measurable_uncurry_suspensionCrossingIndexPastClosed.comp
        (measurable_fst.prodMk
          (measurable_subtype_coe.comp (measurable_fst.comp measurable_snd))))
  let selected : (ℝ ×
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ))) → ℤ → Bool := fun x n =>
    decide (0 < Probability.PoissonProcess.suspensionBaseArrival x.2.1 n ∧
      Probability.PoissonProcess.suspensionBaseArrival x.2.1 n ≤ x.1)
  have hselected : Measurable selected := by
    refine measurable_pi_iff.2 fun n => ?_
    change Measurable (fun x : ℝ ×
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) => if
      0 < Probability.PoissonProcess.suspensionBaseArrival x.2.1 n ∧
        Probability.PoissonProcess.suspensionBaseArrival x.2.1 n ≤ x.1
      then true else false)
    have harrival : Measurable (fun x : ℝ ×
        (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) =>
        Probability.PoissonProcess.suspensionBaseArrival x.2.1 n) :=
      (Probability.PoissonProcess.measurable_suspensionBaseArrival n).comp
        (measurable_fst.comp measurable_snd)
    have hleft : MeasurableSet {x : ℝ ×
        (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) |
        0 < Probability.PoissonProcess.suspensionBaseArrival x.2.1 n} :=
      measurableSet_lt measurable_const harrival
    have hright : MeasurableSet {x : ℝ ×
        (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) |
        Probability.PoissonProcess.suspensionBaseArrival x.2.1 n ≤ x.1} :=
      measurableSet_le harrival measurable_fst
    exact Measurable.ite (hleft.inter hright) measurable_const measurable_const
  let weight : (ℝ ×
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ))) → ℤ → ℝ := fun x n =>
    meanService * x.2.2 n
  have hweight : Measurable weight := by
    refine measurable_pi_iff.2 fun n => ?_
    change Measurable (fun x : ℝ ×
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) =>
      meanService * x.2.2 n)
    exact measurable_const.mul
      ((measurable_pi_apply n).comp (measurable_snd.comp measurable_snd))
  have hsum : Measurable (fun x => ∑ n ∈ indices (state x),
      if selected x n = true then weight x n else 0) :=
    Probability.Palm.measurable_sum_from_countable_parameter
      (Ω := ℝ × (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
      (κ := ℤ × ℤ) state hstate indices selected hselected weight hweight
  convert hsum using 1
  funext x
  simp only [state, indices, selected, weight,
    Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed,
    Finset.sum_filter, decide_eq_true_eq]

/-- A class's future marked work is measurable when the horizon is a
measurable observable of the whole stationary multiclass input. -/
theorem measurable_stationaryPriorityFutureWorkAggregate_comp
    (meanService : Class → ℝ) (i : Class)
    (horizon : (Class →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ))) → ℝ)
    (hhorizon : Measurable horizon) :
    Measurable (fun omega :
      Class → (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) =>
      (Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0
        (horizon omega) (omega i).1).sum
        (stationaryPriorityWorkRequirement meanService i omega)) := by
  simpa [stationaryPriorityWorkRequirement,
    Probability.PoissonProcess.multiclassStationaryPoissonWorkRequirement,
    Probability.Queueing.stationaryPoissonWorkRequirement] using
    (measurable_scaledStationaryPoissonWorkFutureWindow (meanService i)).comp
      (hhorizon.prodMk (measurable_pi_apply i))

/-- A class's stationary marked-Poisson past work is integrable over every
deterministic finite horizon. -/
theorem integrable_stationaryPriorityPastWorkAggregate
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (i : Class) (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun omega => stationaryPriorityPastWorkAggregate meanService i omega t)
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate) := by
  let π := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate
  letI : IsProbabilityMeasure π :=
    Probability.PoissonProcess.isProbabilityMeasure_multiclassStationaryPoissonWorkMeasure
      arrivalRate harrivalRate
  have hraw : Integrable (fun z =>
      Probability.Queueing.stationaryPoissonWorkPastAggregate z t)
      (Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate i)) :=
    Probability.Queueing.integrable_stationaryPoissonWorkPastAggregate
      (harrivalRate i) ht
  have hlift : Integrable (fun omega : Class →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) =>
      Probability.Queueing.stationaryPoissonWorkPastAggregate (omega i) t) π := by
    simpa [π, Function.comp_def] using
      ((Probability.PoissonProcess.measurePreserving_multiclassStationaryPoissonWorkPath
        arrivalRate harrivalRate i).integrable_comp hraw.aestronglyMeasurable).mpr hraw
  change Integrable (fun omega => stationaryPriorityPastWorkAggregate meanService i omega t) π
  refine (hlift.const_mul (meanService i)).congr ?_
  filter_upwards with omega
  exact (stationaryPriorityPastWorkAggregate_eq meanService i omega t).symm

/-- The expected stationary past work of a class over `[-t,0)` is its load
times the length of that window. -/
theorem integral_stationaryPriorityPastWorkAggregate
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (i : Class) (t : ℝ) (ht : 0 ≤ t) :
    ∫ omega, stationaryPriorityPastWorkAggregate meanService i omega t
      ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate =
      arrivalRate i * meanService i * t := by
  let π := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate
  letI : IsProbabilityMeasure π :=
    Probability.PoissonProcess.isProbabilityMeasure_multiclassStationaryPoissonWorkMeasure
      arrivalRate harrivalRate
  have hraw : Integrable (fun z =>
      Probability.Queueing.stationaryPoissonWorkPastAggregate z t)
      (Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate i)) :=
    Probability.Queueing.integrable_stationaryPoissonWorkPastAggregate
      (harrivalRate i) ht
  calc
    ∫ omega, stationaryPriorityPastWorkAggregate meanService i omega t ∂π =
        ∫ omega, meanService i *
          Probability.Queueing.stationaryPoissonWorkPastAggregate (omega i) t ∂π := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with omega
            exact stationaryPriorityPastWorkAggregate_eq meanService i omega t
    _ = meanService i * ∫ omega,
        Probability.Queueing.stationaryPoissonWorkPastAggregate (omega i) t ∂π := by
          rw [MeasureTheory.integral_const_mul]
    _ = meanService i * ∫ z,
        Probability.Queueing.stationaryPoissonWorkPastAggregate z t
          ∂Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate i) := by
          congr 1
          simpa [π, Function.comp_def] using
            (Probability.PoissonProcess.measurePreserving_multiclassStationaryPoissonWorkPath
              arrivalRate harrivalRate i).hasLaw.integral_comp
                (f := fun z => Probability.Queueing.stationaryPoissonWorkPastAggregate z t)
                hraw.aestronglyMeasurable
    _ = meanService i * (arrivalRate i * t) := by
          rw [Probability.Queueing.integral_stationaryPoissonWorkPastAggregate
            (harrivalRate i) ht]
    _ = arrivalRate i * meanService i * t := by ring

/-- A class's scaled squared-mark reward is integrable over every deterministic
finite stationary past window. -/
theorem integrable_stationaryPriorityPastSquareWorkAggregate
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (i : Class) (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun omega => stationaryPriorityPastSquareWorkAggregate meanService i omega t)
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate) := by
  let π := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate
  letI : IsProbabilityMeasure π :=
    Probability.PoissonProcess.isProbabilityMeasure_multiclassStationaryPoissonWorkMeasure
      arrivalRate harrivalRate
  have hraw : Integrable (fun z =>
      Probability.Queueing.stationaryPoissonWorkPastSquareAggregate z t)
      (Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate i)) :=
    Probability.Queueing.integrable_stationaryPoissonWorkPastSquareAggregate
      (harrivalRate i) ht
  have hlift : Integrable (fun omega : Class →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) =>
      Probability.Queueing.stationaryPoissonWorkPastSquareAggregate (omega i) t) π := by
    simpa [π, Function.comp_def] using
      ((Probability.PoissonProcess.measurePreserving_multiclassStationaryPoissonWorkPath
        arrivalRate harrivalRate i).integrable_comp hraw.aestronglyMeasurable).mpr hraw
  change Integrable (fun omega => stationaryPriorityPastSquareWorkAggregate meanService i omega t) π
  refine (hlift.const_mul (meanService i ^ 2)).congr ?_
  filter_upwards with omega
  exact (stationaryPriorityPastSquareWorkAggregate_eq meanService i omega t).symm

/-- The expected class-`i` squared service reward in `[-t,0)` equals its
arrival exposure times the second exponential service moment. -/
theorem integral_stationaryPriorityPastSquareWorkAggregate
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (i : Class) (t : ℝ) (ht : 0 ≤ t) :
    ∫ omega, stationaryPriorityPastSquareWorkAggregate meanService i omega t
      ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate =
      2 * arrivalRate i * meanService i ^ 2 * t := by
  let π := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate
  letI : IsProbabilityMeasure π :=
    Probability.PoissonProcess.isProbabilityMeasure_multiclassStationaryPoissonWorkMeasure
      arrivalRate harrivalRate
  have hraw : Integrable (fun z =>
      Probability.Queueing.stationaryPoissonWorkPastSquareAggregate z t)
      (Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate i)) :=
    Probability.Queueing.integrable_stationaryPoissonWorkPastSquareAggregate
      (harrivalRate i) ht
  calc
    ∫ omega, stationaryPriorityPastSquareWorkAggregate meanService i omega t ∂π =
        ∫ omega, meanService i ^ 2 *
          Probability.Queueing.stationaryPoissonWorkPastSquareAggregate (omega i) t ∂π := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with omega
            exact stationaryPriorityPastSquareWorkAggregate_eq meanService i omega t
    _ = meanService i ^ 2 * ∫ omega,
        Probability.Queueing.stationaryPoissonWorkPastSquareAggregate (omega i) t ∂π := by
          rw [MeasureTheory.integral_const_mul]
    _ = meanService i ^ 2 * ∫ z,
        Probability.Queueing.stationaryPoissonWorkPastSquareAggregate z t
          ∂Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate i) := by
          congr 1
          simpa [π, Function.comp_def] using
            (Probability.PoissonProcess.measurePreserving_multiclassStationaryPoissonWorkPath
              arrivalRate harrivalRate i).hasLaw.integral_comp
                (f := fun z =>
                  Probability.Queueing.stationaryPoissonWorkPastSquareAggregate z t)
                hraw.aestronglyMeasurable
    _ = meanService i ^ 2 * (2 * arrivalRate i * t) := by
          rw [Probability.Queueing.integral_stationaryPoissonWorkPastSquareAggregate
            (harrivalRate i) ht]
    _ = 2 * arrivalRate i * meanService i ^ 2 * t := by ring

/-- The scaled stationary marked-Poisson input supplies class-`i` work at its
load rate `arrivalRate i * meanService i`.  This is an input-process result;
it does not yet construct a queue state or a Palm arrival law. -/
theorem ae_tendsto_stationaryPriorityPastWorkAggregate_div_atTop
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (i : Class) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      Tendsto (fun t : ℝ =>
        stationaryPriorityPastWorkAggregate meanService i omega t / t)
        atTop (nhds (arrivalRate i * meanService i)) := by
  have hbase : ∀ᵐ z ∂Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate i),
      Tendsto (fun t : ℝ =>
        meanService i *
          Probability.Queueing.stationaryPoissonWorkPastAggregate z t / t)
        atTop (nhds (arrivalRate i * meanService i)) := by
    filter_upwards [Probability.Queueing.ae_tendsto_stationaryPoissonWorkPastAggregate_div_atTop
      (harrivalRate i)] with z hz
    convert ((tendsto_const_nhds (x := meanService i)).mul hz) using 1 <;> ring_nf
  have hlift : ∀ᵐ omega ∂
      Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      Tendsto (fun t : ℝ =>
        meanService i * Probability.Queueing.stationaryPoissonWorkPastAggregate
          (omega i) t / t)
        atTop (nhds (arrivalRate i * meanService i)) := by
    refine ae_of_ae_map
      (μ := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate)
      (f := Function.eval i)
      (p := fun z : Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ) =>
        Tendsto (fun t : ℝ =>
          meanService i * Probability.Queueing.stationaryPoissonWorkPastAggregate z t / t)
          atTop (nhds (arrivalRate i * meanService i)))
      (Probability.PoissonProcess.measurePreserving_multiclassStationaryPoissonWorkPath
        arrivalRate harrivalRate i).measurable.aemeasurable ?_
    rw [(Probability.PoissonProcess.measurePreserving_multiclassStationaryPoissonWorkPath
      arrivalRate harrivalRate i).map_eq]
    exact hbase
  filter_upwards [hlift] with omega homega
  simpa [stationaryPriorityPastWorkAggregate,
    stationaryPriorityWorkRequirement,
    Probability.PoissonProcess.multiclassStationaryPoissonWorkRequirement,
    Probability.Queueing.stationaryPoissonWorkPastAggregate,
    Finset.mul_sum, div_eq_mul_inv, mul_assoc, mul_comm] using homega

/-- Total work of all finite priority classes arriving in `[-t, 0)`. -/
def stationaryPriorityTotalPastWorkAggregate
    (meanService : Class → ℝ) :
    (Class → (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ))) → ℝ → ℝ :=
  fun omega t => ∑ i, stationaryPriorityPastWorkAggregate meanService i omega t

/-- The total marked work of a finite stationary past window is integrable. -/
theorem integrable_stationaryPriorityTotalPastWorkAggregate
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun omega => stationaryPriorityTotalPastWorkAggregate meanService omega t)
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate) := by
  change Integrable (fun omega => ∑ i,
    stationaryPriorityPastWorkAggregate meanService i omega t) _
  apply MeasureTheory.integrable_finset_sum Finset.univ
  intro i _
  exact integrable_stationaryPriorityPastWorkAggregate
    arrivalRate meanService harrivalRate i t ht

/-- The expected marked work of a finite stationary past window is its total
arrival load times the window length. -/
theorem integral_stationaryPriorityTotalPastWorkAggregate
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (t : ℝ) (ht : 0 ≤ t) :
    ∫ omega, stationaryPriorityTotalPastWorkAggregate meanService omega t
      ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate =
      (∑ i, arrivalRate i * meanService i) * t := by
  let π := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate
  change ∫ omega, ∑ i, stationaryPriorityPastWorkAggregate meanService i omega t ∂π = _
  calc
    ∫ omega, ∑ i, stationaryPriorityPastWorkAggregate meanService i omega t ∂π =
        ∑ i, ∫ omega, stationaryPriorityPastWorkAggregate meanService i omega t ∂π := by
          exact MeasureTheory.integral_finset_sum Finset.univ fun i _ =>
            integrable_stationaryPriorityPastWorkAggregate
              arrivalRate meanService harrivalRate i t ht
    _ = ∑ i, arrivalRate i * meanService i * t := by
          apply Finset.sum_congr rfl
          intro i _
          exact integral_stationaryPriorityPastWorkAggregate
            arrivalRate meanService harrivalRate i t ht
    _ = (∑ i, arrivalRate i * meanService i) * t := by
          rw [Finset.sum_mul]

/-- Total squared service reward of all finite priority classes arriving in
`[-t,0)`. -/
def stationaryPriorityTotalPastSquareWorkAggregate
    (meanService : Class → ℝ) :
    (Class → (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ))) → ℝ → ℝ :=
  fun omega t => ∑ i, stationaryPriorityPastSquareWorkAggregate meanService i omega t

/-- The total squared service reward of a finite stationary past window is
integrable. -/
theorem integrable_stationaryPriorityTotalPastSquareWorkAggregate
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun omega => stationaryPriorityTotalPastSquareWorkAggregate meanService omega t)
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate) := by
  change Integrable (fun omega => ∑ i,
    stationaryPriorityPastSquareWorkAggregate meanService i omega t) _
  apply MeasureTheory.integrable_finset_sum Finset.univ
  intro i _
  exact integrable_stationaryPriorityPastSquareWorkAggregate
    arrivalRate meanService harrivalRate i t ht

/-- The expected squared service reward of a finite stationary past window
is the sum of class arrival rates times their exponential second moments. -/
theorem integral_stationaryPriorityTotalPastSquareWorkAggregate
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (t : ℝ) (ht : 0 ≤ t) :
    ∫ omega, stationaryPriorityTotalPastSquareWorkAggregate meanService omega t
      ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate =
      2 * (∑ i, arrivalRate i * meanService i ^ 2) * t := by
  let π := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate
  change ∫ omega, ∑ i, stationaryPriorityPastSquareWorkAggregate meanService i omega t ∂π = _
  calc
    ∫ omega, ∑ i, stationaryPriorityPastSquareWorkAggregate meanService i omega t ∂π =
        ∑ i, ∫ omega, stationaryPriorityPastSquareWorkAggregate meanService i omega t ∂π := by
          exact MeasureTheory.integral_finset_sum Finset.univ fun i _ =>
            integrable_stationaryPriorityPastSquareWorkAggregate
              arrivalRate meanService harrivalRate i t ht
    _ = ∑ i, 2 * arrivalRate i * meanService i ^ 2 * t := by
          apply Finset.sum_congr rfl
          intro i _
          exact integral_stationaryPriorityPastSquareWorkAggregate
            arrivalRate meanService harrivalRate i t ht
    _ = (∑ i, 2 * (arrivalRate i * meanService i ^ 2)) * t := by
          rw [← Finset.sum_mul]
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = 2 * (∑ i, arrivalRate i * meanService i ^ 2) * t := by
          rw [Finset.mul_sum]

/-- The aggregate work of all finitely many input classes in a fixed past
window is measurable. -/
theorem measurable_stationaryPriorityTotalPastWorkAggregate
    (meanService : Class → ℝ) (t : ℝ) :
    Measurable (fun omega :
      Class → (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) =>
        stationaryPriorityTotalPastWorkAggregate meanService omega t) := by
  change Measurable (fun omega => ∑ i,
    stationaryPriorityPastWorkAggregate meanService i omega t)
  exact Finset.measurable_fun_sum Finset.univ fun i hi =>
    measurable_stationaryPriorityPastWorkAggregate meanService i t

/-- The total work aggregate is measurable at every measurable random past
horizon. -/
theorem measurable_stationaryPriorityTotalPastWorkAggregate_comp
    (meanService : Class → ℝ)
    (horizon : (Class →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ))) → ℝ)
    (hhorizon : Measurable horizon) :
    Measurable (fun omega :
      Class → (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) =>
        stationaryPriorityTotalPastWorkAggregate meanService omega (horizon omega)) := by
  change Measurable (fun omega => ∑ i,
    stationaryPriorityPastWorkAggregate meanService i omega (horizon omega))
  exact Finset.measurable_fun_sum Finset.univ fun i hi =>
    measurable_stationaryPriorityPastWorkAggregate_comp meanService i horizon hhorizon

/-- The total finite-class input work has almost-sure long-run rate equal to
the sum of class loads.  Thus the usual strict-load condition can be matched
to a literal stationary input path before constructing the queue workload. -/
theorem ae_tendsto_stationaryPriorityTotalPastWorkAggregate_div_atTop
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      Tendsto (fun t : ℝ =>
        stationaryPriorityTotalPastWorkAggregate meanService omega t / t)
        atTop (nhds (∑ i, arrivalRate i * meanService i)) := by
  have hclass : ∀ᵐ omega ∂
      Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      ∀ i : Class,
        Tendsto (fun t : ℝ =>
          stationaryPriorityPastWorkAggregate meanService i omega t / t)
          atTop (nhds (arrivalRate i * meanService i)) := by
    rw [ae_all_iff]
    intro i
    exact ae_tendsto_stationaryPriorityPastWorkAggregate_div_atTop
      arrivalRate meanService harrivalRate i
  filter_upwards [hclass] with omega homega
  have hsum : Tendsto (fun t : ℝ => ∑ i,
      stationaryPriorityPastWorkAggregate meanService i omega t / t)
      atTop (nhds (∑ i, arrivalRate i * meanService i)) :=
    tendsto_finset_sum _ fun i _ => homega i
  simpa [stationaryPriorityTotalPastWorkAggregate, Finset.sum_div] using hsum

/-- Cumulative net input over the past interval `[-t, 0)`: arriving work
minus the service capacity available during that interval. -/
def stationaryPriorityNetPastInput
    (meanService : Class → ℝ) :
    (Class → (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ))) → ℝ → ℝ :=
  fun omega t => stationaryPriorityTotalPastWorkAggregate meanService omega t - t

/-- The fixed-horizon cumulative net input is measurable. -/
theorem measurable_stationaryPriorityNetPastInput
    (meanService : Class → ℝ) (t : ℝ) :
    Measurable (fun omega :
      Class → (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) =>
        stationaryPriorityNetPastInput meanService omega t) := by
  exact (measurable_stationaryPriorityTotalPastWorkAggregate meanService t).sub
    measurable_const

/-- Cumulative net input is measurable at every measurable random horizon. -/
theorem measurable_stationaryPriorityNetPastInput_comp
    (meanService : Class → ℝ)
    (horizon : (Class →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ))) → ℝ)
    (hhorizon : Measurable horizon) :
    Measurable (fun omega :
      Class → (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) =>
        stationaryPriorityNetPastInput meanService omega (horizon omega)) := by
  exact (measurable_stationaryPriorityTotalPastWorkAggregate_comp
    meanService horizon hhorizon).sub hhorizon

/-- Net input measured back to a labelled class arrival is measurable.  This
is the random-horizon observable used when a reflected workload is expressed
as the maximum over literal arrival epochs. -/
theorem measurable_stationaryPriorityNetPastInput_at_classArrival
    (meanService : Class → ℝ) (i : Class) (n : ℤ) :
    Measurable (fun omega :
      Class → (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) =>
        stationaryPriorityNetPastInput meanService omega
          (-Probability.PoissonProcess.suspensionBaseArrival (omega i).1 n)) := by
  have harrival : Measurable (fun omega :
      Class → (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) =>
        Probability.PoissonProcess.suspensionBaseArrival (omega i).1 n) :=
    (Probability.PoissonProcess.measurable_suspensionBaseArrival n).comp
      (measurable_fst.comp (measurable_pi_apply i))
  exact measurable_stationaryPriorityNetPastInput_comp meanService
    (fun omega => -Probability.PoissonProcess.suspensionBaseArrival (omega i).1 n)
    harrival.neg

/-- Under strict total load below one, the literal stationary input has
negative cumulative net-work drift into the remote past.  This is the
stability condition required by a causal workload construction. -/
theorem ae_tendsto_stationaryPriorityNetPastInput_atBot
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      Tendsto (fun t : ℝ => stationaryPriorityNetPastInput meanService omega t)
        atTop atBot := by
  filter_upwards [ae_tendsto_stationaryPriorityTotalPastWorkAggregate_div_atTop
    arrivalRate meanService harrivalRate] with omega homega
  have hdiv : Tendsto (fun t : ℝ =>
      (t - stationaryPriorityTotalPastWorkAggregate meanService omega t) / t)
      atTop (nhds (1 - ∑ i, arrivalRate i * meanService i)) := by
    apply (tendsto_const_nhds.sub homega).congr'
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
    field_simp [ht]
  have hpositive : Tendsto (fun t : ℝ =>
      t - stationaryPriorityTotalPastWorkAggregate meanService omega t) atTop atTop :=
    tendsto_id.num (sub_pos.mpr hstable) hdiv
  simpa [stationaryPriorityNetPastInput, Function.comp_def] using
    tendsto_neg_atTop_atBot.comp hpositive

/-- The zero-length past window contains no class-`i` arriving work. -/
theorem stationaryPriorityPastWorkAggregate_zero
    (meanService : Class → ℝ) (i : Class)
    (omega : Class → (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ))) :
    stationaryPriorityPastWorkAggregate meanService i omega 0 = 0 := by
  unfold stationaryPriorityPastWorkAggregate
  apply Finset.sum_eq_zero
  intro n hn
  have hwindow :=
    (Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff
      0 0 (omega i).1 n).mp (by simpa using hn)
  linarith

/-- The zero-length past window contains no total arriving work. -/
theorem stationaryPriorityTotalPastWorkAggregate_zero
    (meanService : Class → ℝ)
    (omega : Class → (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ))) :
    stationaryPriorityTotalPastWorkAggregate meanService omega 0 = 0 := by
  unfold stationaryPriorityTotalPastWorkAggregate
  apply Finset.sum_eq_zero
  intro i _
  exact stationaryPriorityPastWorkAggregate_zero meanService i omega

/-- One unit-width remote-past increment, obtained by differencing literal
past-window work and subtracting one unit of service capacity.  This is an
input discretization for the remote-past workload machinery, not a claim that
all arrivals in a time interval occur simultaneously. -/
def stationaryPriorityRemotePastIncrement
    (meanService : Class → ℝ)
    (omega : Class → (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (N : ℕ) : ℝ :=
  stationaryPriorityTotalPastWorkAggregate meanService omega ((N + 1 : ℕ) : ℝ) -
    stationaryPriorityTotalPastWorkAggregate meanService omega (N : ℝ) - 1

/-- The cumulative remote-past increments telescope exactly to literal past
net input at integer horizons. -/
theorem remotePastCumulativeNetInput_stationaryPriorityRemotePastIncrement
    (meanService : Class → ℝ)
    (omega : Class → (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (N : ℕ) :
    Probability.Queueing.remotePastCumulativeNetInput
        (stationaryPriorityRemotePastIncrement meanService omega) N =
      stationaryPriorityNetPastInput meanService omega (N : ℝ) := by
  induction N with
  | zero =>
      simp [Probability.Queueing.remotePastCumulativeNetInput,
        stationaryPriorityNetPastInput,
        stationaryPriorityTotalPastWorkAggregate_zero]
  | succ N ih =>
      rw [Probability.Queueing.remotePastCumulativeNetInput_succ, ih]
      simp only [stationaryPriorityRemotePastIncrement,
        stationaryPriorityNetPastInput]
      norm_num
      ring

/-- Strict total load makes the remote-past cumulative input of the literal
stationary input discretization tend to `-∞`.  This is the exact deterministic
stability premise consumed by the reusable Lindley remote-past theorems. -/
theorem ae_tendsto_stationaryPriorityRemotePastCumulativeNetInput_atBot
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      Tendsto
        (Probability.Queueing.remotePastCumulativeNetInput
          (stationaryPriorityRemotePastIncrement meanService omega))
        atTop atBot := by
  filter_upwards [ae_tendsto_stationaryPriorityNetPastInput_atBot
    arrivalRate meanService harrivalRate hstable] with omega homega
  apply (homega.comp tendsto_natCast_atTop_atTop).congr'
  exact Filter.Eventually.of_forall fun N =>
    remotePastCumulativeNetInput_stationaryPriorityRemotePastIncrement
      meanService omega N |>.symm

/-- A class-specific scaled work mark has the exponential law whose rate is
the reciprocal of its mean service requirement. -/
theorem stationaryPriorityWorkRequirement_hasLaw
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (i : Class) (n : ℤ) :
    HasLaw (fun omega : Class →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) =>
        stationaryPriorityWorkRequirement meanService i omega n)
      (expMeasure (meanService i)⁻¹)
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate) := by
  have hscale :
      Measure.map (fun x : ℝ => meanService i * x) (expMeasure (1 : ℝ)) =
        expMeasure (meanService i)⁻¹ := by
    calc
      Measure.map (fun x : ℝ => meanService i * x) (expMeasure (1 : ℝ)) =
          Measure.map (fun x : ℝ => x / (meanService i)⁻¹) (expMeasure (1 : ℝ)) := by
            congr 1
            funext x
            field_simp [ne_of_gt (hmeanService i)]
      _ = expMeasure (meanService i)⁻¹ := by
            exact Probability.map_div_unitExpMeasure_eq_expMeasure
              (inv_pos.mpr (hmeanService i))
  exact HasLaw.comp
    ⟨by fun_prop, hscale⟩
    (Probability.PoissonProcess.multiclassStationaryPoissonWorkRequirement_hasLaw
      arrivalRate harrivalRate i n)

/-- The stationary work-mark law uses the same reciprocal service rate as the
class-dependent nonpreemptive-priority event kernel. -/
theorem stationaryPriorityWorkRequirement_hasLaw_exponentialServiceRate
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (i : Class) (n : ℤ) :
    HasLaw (fun omega : Class →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) =>
        stationaryPriorityWorkRequirement meanService i omega n)
      (expMeasure (exponentialServiceRate meanService i))
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate) := by
  simpa [exponentialServiceRate] using
    stationaryPriorityWorkRequirement_hasLaw arrivalRate meanService
      harrivalRate hmeanService i n

/-- The physical arrival epoch of a labelled class customer in the full
multiclass selected-arrival configuration.  The distinguished customer's
class-indexed arrival at zero and every passive class path share this one
interface. -/
def stationaryPriorityClassTaggedArrival
    (i : Class) :
    MulticlassStationaryPoissonWorkClassTaggedSample Class i → Class → ℤ → ℝ :=
  multiclassStationaryPoissonWorkClassTaggedArrival i

/-- A class-specific scaled work requirement in the full multiclass
selected-arrival configuration. -/
def stationaryPriorityClassTaggedWorkRequirementAt
    (meanService : Class → ℝ) (i : Class) :
    MulticlassStationaryPoissonWorkClassTaggedSample Class i → Class → ℤ → ℝ :=
  fun z j k => meanService j *
    multiclassStationaryPoissonWorkClassTaggedRequirementAt i z j k

/-- The finite ledger of class-`j` arrival indices in the literal interval
`[a,b)` under a Palm-selected class-`i` input.  The selected class uses its
tagged renewal path and all passive classes retain their stationary paths. -/
def stationaryPriorityClassTaggedArrivalWindowIndices
    (i : Class) (z : MulticlassStationaryPoissonWorkClassTaggedSample Class i)
    (a b : ℝ) (j : Class) : Finset ℤ :=
  if hji : j = i then
    Probability.PoissonProcess.palmTaggedArrivalIndices a b z.1.1
  else
    Probability.PoissonProcess.suspensionBaseArrivalIndices a b (z.2 ⟨j, hji⟩).1

/-- The selected class has its distinguished arrival at the Palm origin. -/
theorem stationaryPriorityClassTaggedArrival_tag_zero
    (i : Class) (z : MulticlassStationaryPoissonWorkClassTaggedSample Class i) :
    stationaryPriorityClassTaggedArrival i z i 0 = 0 := by
  exact multiclassStationaryPoissonWorkClassTaggedArrival_tag_zero i z

/-- Every fixed class-labelled arrival time is measurable under the full
selected-arrival carrier. -/
theorem measurable_stationaryPriorityClassTaggedArrival
    [MeasurableSpace Class] (i j : Class) (k : ℤ) :
    Measurable (fun z : MulticlassStationaryPoissonWorkClassTaggedSample Class i =>
      stationaryPriorityClassTaggedArrival i z j k) :=
  measurable_multiclassStationaryPoissonWorkClassTaggedArrival i j k

/-- Every passive class keeps the strict chronological order of its stationary
arrival labels on the selected-arrival carrier. -/
theorem strictMono_stationaryPriorityClassTaggedArrival_of_ne
    (i j : Class) (hji : j ≠ i)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample Class i) :
    StrictMono (stationaryPriorityClassTaggedArrival i z j) := by
  intro k l hkl
  simp only [stationaryPriorityClassTaggedArrival,
    multiclassStationaryPoissonWorkClassTaggedArrival, dif_neg hji,
    Probability.Queueing.stationaryPoissonWorkArrival,
    Probability.Queueing.timedEmbeddedArrival]
  exact Probability.PoissonProcess.suspensionBaseArrival_strictMono
    (z.2 ⟨j, hji⟩).1 hkl

/-- Every fixed class-labelled scaled work mark is measurable under the full
selected-arrival carrier. -/
theorem measurable_stationaryPriorityClassTaggedWorkRequirementAt
    [MeasurableSpace Class] (meanService : Class → ℝ) (i j : Class) (k : ℤ) :
    Measurable (fun z : MulticlassStationaryPoissonWorkClassTaggedSample Class i =>
      stationaryPriorityClassTaggedWorkRequirementAt meanService i z j k) := by
  exact measurable_const.mul
    (measurable_multiclassStationaryPoissonWorkClassTaggedRequirementAt i j k)

/-- Under the genuine selected-class Palm law, every class-labelled scaled
work mark is strictly positive almost surely.  This is the mark-positivity
input required when the full tagged carrier is executed as a finite priority
trace. -/
theorem ae_all_stationaryPriorityClassTaggedWorkRequirementAt_positive
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (i : Class) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      ∀ j : Class, ∀ k : ℤ,
        0 < stationaryPriorityClassTaggedWorkRequirementAt meanService i z j k := by
  filter_upwards [
    ae_all_multiclassStationaryPoissonWorkClassTaggedRequirement_positive
      arrivalRate harrivalRate i] with z hz
  intro j k
  exact mul_pos (hmeanService j) (hz j k)

/-- The scaled work requirement of a class-`i` customer pinned at time zero
in the concrete multiclass Palm input. -/
def stationaryPriorityClassTaggedWorkRequirement
    (meanService : Class → ℝ) (i : Class) :
    ((ℤ → ℝ) × (ℤ → ℝ)) ×
      ({j : Class // j ≠ i} → StationaryPoissonWorkPath) → ℝ :=
  fun z => meanService i * multiclassStationaryPoissonWorkClassTaggedRequirement i z

/-- The existing distinguished-work observable is the class-`i`, index-zero
coordinate of the full selected-arrival work path. -/
theorem stationaryPriorityClassTaggedWorkRequirement_eq_fullCoordinate
    (meanService : Class → ℝ) (i : Class)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample Class i) :
    stationaryPriorityClassTaggedWorkRequirement meanService i z =
      stationaryPriorityClassTaggedWorkRequirementAt meanService i z i 0 := by
  simp [stationaryPriorityClassTaggedWorkRequirement,
    stationaryPriorityClassTaggedWorkRequirementAt,
    multiclassStationaryPoissonWorkClassTaggedRequirementAt,
    multiclassStationaryPoissonWorkClassTaggedRequirement]

/-- Total scaled work of a specified class arriving in the literal interval
`[-t, 0)` on the full selected-arrival carrier. -/
def stationaryPriorityTaggedPastWorkAggregate
    (meanService : Class → ℝ) (i : Class)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample Class i)
    (j : Class) (t : ℝ) : ℝ :=
  (stationaryPriorityClassTaggedArrivalWindowIndices i z (-t) 0 j).sum
    (stationaryPriorityClassTaggedWorkRequirementAt meanService i z j)

/-- Total scaled work of the class selected at the Palm origin arriving in
the literal interval `[-t, 0)`. -/
def stationaryPriorityClassTaggedPastWorkAggregate
    (meanService : Class → ℝ) (i : Class)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample Class i) (t : ℝ) : ℝ :=
  stationaryPriorityTaggedPastWorkAggregate meanService i z i t

/-- The selected-class aggregate is exactly its mean-service scaling times
the raw Palm tagged marked-renewal aggregate. -/
theorem stationaryPriorityClassTaggedPastWorkAggregate_eq
    (meanService : Class → ℝ) (i : Class)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample Class i) (t : ℝ) :
    stationaryPriorityClassTaggedPastWorkAggregate meanService i z t =
      meanService i * Probability.PoissonProcess.palmTaggedPoissonWorkPastAggregate z.1 t := by
  unfold stationaryPriorityClassTaggedPastWorkAggregate
    stationaryPriorityTaggedPastWorkAggregate
  rw [show stationaryPriorityClassTaggedArrivalWindowIndices i z (-t) 0 i =
      Probability.PoissonProcess.palmTaggedArrivalIndices (-t) 0 z.1.1 by
        simp [stationaryPriorityClassTaggedArrivalWindowIndices]]
  rw [Probability.PoissonProcess.palmTaggedPoissonWorkPastAggregate, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp [stationaryPriorityClassTaggedWorkRequirementAt,
    multiclassStationaryPoissonWorkClassTaggedRequirementAt]

/-- The Palm-selected class's finite pre-tag work has its exact expected load
over every deterministic horizon.  This is the past-window analogue of the
post-tag input calculation: it compares literal Poisson input exposures only,
not a stationary queue state. -/
theorem integral_stationaryPriorityClassTaggedPastWorkAggregate
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (i : Class) (t : ℝ) (ht : 0 ≤ t) :
    ∫ z, stationaryPriorityClassTaggedPastWorkAggregate meanService i z t
      ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag =
      arrivalRate i * meanService i * t := by
  let tagged := Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
    (harrivalRate i)
  let passive := multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i
  letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
  letI : IsProbabilityMeasure passive.Pbase := passive.isProbability
  have hrawInt : Integrable (fun y : (ℤ → ℝ) × (ℤ → ℝ) =>
      Probability.PoissonProcess.palmTaggedPoissonWorkPastAggregate y t) tagged.Ptag := by
    change Integrable (fun y : (ℤ → ℝ) × (ℤ → ℝ) =>
      Probability.PoissonProcess.palmTaggedPoissonWorkPastAggregate y t)
      ((Probability.PoissonProcess.twoSidedInterarrivalMeasure (arrivalRate i)).prod
        (Probability.PoissonProcess.twoSidedInterarrivalMeasure (1 : ℝ)))
    exact Probability.PoissonProcess.integrable_palmTaggedPoissonWorkPastAggregate
      (harrivalRate i) ht
  have hrawMean : ∫ y : (ℤ → ℝ) × (ℤ → ℝ),
      Probability.PoissonProcess.palmTaggedPoissonWorkPastAggregate y t ∂tagged.Ptag =
      arrivalRate i * t := by
    change ∫ y : (ℤ → ℝ) × (ℤ → ℝ),
      Probability.PoissonProcess.palmTaggedPoissonWorkPastAggregate y t
        ∂((Probability.PoissonProcess.twoSidedInterarrivalMeasure (arrivalRate i)).prod
          (Probability.PoissonProcess.twoSidedInterarrivalMeasure (1 : ℝ))) =
        arrivalRate i * t
    exact Probability.PoissonProcess.integral_palmTaggedPoissonWorkPastAggregate
      (harrivalRate i) ht
  have hliftInt : Integrable (fun z :
      MulticlassStationaryPoissonWorkClassTaggedSample Class i =>
      Probability.PoissonProcess.palmTaggedPoissonWorkPastAggregate z.1 t)
      (tagged.Ptag.prod passive.Pbase) := by
    simpa [Function.comp_def] using hrawInt.comp_fst passive.Pbase
  change ∫ z, stationaryPriorityClassTaggedPastWorkAggregate meanService i z t
    ∂(tagged.Ptag.prod passive.Pbase) =
      arrivalRate i * meanService i * t
  calc
    ∫ z, stationaryPriorityClassTaggedPastWorkAggregate meanService i z t
        ∂(tagged.Ptag.prod passive.Pbase) =
        ∫ z, meanService i *
          Probability.PoissonProcess.palmTaggedPoissonWorkPastAggregate z.1 t
          ∂(tagged.Ptag.prod passive.Pbase) := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with z
            exact stationaryPriorityClassTaggedPastWorkAggregate_eq meanService i z t
    _ = meanService i * ∫ z,
        Probability.PoissonProcess.palmTaggedPoissonWorkPastAggregate z.1 t
        ∂(tagged.Ptag.prod passive.Pbase) := by
          rw [MeasureTheory.integral_const_mul]
    _ = meanService i * ∫ y : (ℤ → ℝ) × (ℤ → ℝ),
        Probability.PoissonProcess.palmTaggedPoissonWorkPastAggregate y t ∂tagged.Ptag := by
          congr 1
          calc
            ∫ z, Probability.PoissonProcess.palmTaggedPoissonWorkPastAggregate z.1 t
                ∂(tagged.Ptag.prod passive.Pbase) =
                ∫ y, ∫ _ : ({j : Class // j ≠ i} → StationaryPoissonWorkPath),
                  Probability.PoissonProcess.palmTaggedPoissonWorkPastAggregate y t
                  ∂passive.Pbase ∂tagged.Ptag := by
                    exact MeasureTheory.integral_prod _ hliftInt
            _ = ∫ y, Probability.PoissonProcess.palmTaggedPoissonWorkPastAggregate y t
                  ∂tagged.Ptag := by simp
    _ = meanService i * (arrivalRate i * t) := by rw [hrawMean]
    _ = arrivalRate i * meanService i * t := by ring

/-- The selected Palm class has integrable literal work in every fixed
pre-origin horizon. -/
theorem integrable_stationaryPriorityClassTaggedPastWorkAggregate
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (i : Class) (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun z => stationaryPriorityClassTaggedPastWorkAggregate meanService i z t)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  let tagged := Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
    (harrivalRate i)
  let passive := multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i
  letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
  letI : IsProbabilityMeasure passive.Pbase := passive.isProbability
  have hraw : Integrable (fun y : (ℤ → ℝ) × (ℤ → ℝ) =>
      Probability.PoissonProcess.palmTaggedPoissonWorkPastAggregate y t) tagged.Ptag := by
    change Integrable (fun y : (ℤ → ℝ) × (ℤ → ℝ) =>
      Probability.PoissonProcess.palmTaggedPoissonWorkPastAggregate y t)
      ((Probability.PoissonProcess.twoSidedInterarrivalMeasure (arrivalRate i)).prod
        (Probability.PoissonProcess.twoSidedInterarrivalMeasure (1 : ℝ)))
    exact Probability.PoissonProcess.integrable_palmTaggedPoissonWorkPastAggregate
      (harrivalRate i) ht
  have hlift : Integrable (fun z : MulticlassStationaryPoissonWorkClassTaggedSample Class i =>
      Probability.PoissonProcess.palmTaggedPoissonWorkPastAggregate z.1 t)
      (tagged.Ptag.prod passive.Pbase) := by
    simpa [Function.comp_def] using hraw.comp_fst passive.Pbase
  change Integrable (fun z => stationaryPriorityClassTaggedPastWorkAggregate meanService i z t)
    (tagged.Ptag.prod passive.Pbase)
  refine (hlift.const_mul (meanService i)).congr ?_
  filter_upwards with z
  exact (stationaryPriorityClassTaggedPastWorkAggregate_eq meanService i z t).symm

/-- A selected class arrival sees the same expected amount of its own input
work in every fixed finite past window as the stationary time-origin view.
This is a concrete finite input-level Palm equality.  It is not a claim that
the remote-past queue state itself has already been identified with a
stationary regenerative law. -/
theorem integral_stationaryPriorityClassTaggedPastWorkAggregate_eq_stationary
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (i : Class) (t : ℝ) (ht : 0 ≤ t) :
    ∫ z, stationaryPriorityClassTaggedPastWorkAggregate meanService i z t
      ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag =
      ∫ omega, stationaryPriorityPastWorkAggregate meanService i omega t
        ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate := by
  rw [integral_stationaryPriorityClassTaggedPastWorkAggregate
    arrivalRate meanService harrivalRate i t ht,
    integral_stationaryPriorityPastWorkAggregate arrivalRate meanService harrivalRate i t ht]

/-- Total scaled work of the class selected at the Palm origin that arrives
strictly after that tag and no later than `t`.  The right-closed interval is
the physical convention of the underlying tagged renewal-count API. -/
def stationaryPriorityClassTaggedFutureWorkAggregate
    (meanService : Class → ℝ) (i : Class)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample Class i) (t : ℝ) : ℝ :=
  (Probability.PoissonProcess.palmTaggedArrivalIndicesRightClosed 0 t z.1.1).sum
    (stationaryPriorityClassTaggedWorkRequirementAt meanService i z i)

/-- The selected-class future aggregate is exactly its mean-service scaling
times the literal selected Palm marked-renewal aggregate. -/
theorem stationaryPriorityClassTaggedFutureWorkAggregate_eq
    (meanService : Class → ℝ) (i : Class)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample Class i) (t : ℝ) :
    stationaryPriorityClassTaggedFutureWorkAggregate meanService i z t =
      meanService i * Probability.PoissonProcess.palmTaggedPoissonWorkFutureAggregate
        z.1 t := by
  unfold stationaryPriorityClassTaggedFutureWorkAggregate
  rw [Probability.PoissonProcess.palmTaggedPoissonWorkFutureAggregate, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp [stationaryPriorityClassTaggedWorkRequirementAt,
    multiclassStationaryPoissonWorkClassTaggedRequirementAt]

/-- The Palm-selected class's finite post-tag work has its exact expected
load over every deterministic horizon.  The passive multiclass environment
remains in the carrier; product integration removes it only after the
selected tagged renewal calculation has been established. -/
theorem integral_stationaryPriorityClassTaggedFutureWorkAggregate
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (i : Class) (t : ℝ) (ht : 0 ≤ t) :
    ∫ z, stationaryPriorityClassTaggedFutureWorkAggregate meanService i z t
      ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag =
      arrivalRate i * meanService i * t := by
  let tagged := Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
    (harrivalRate i)
  let passive := multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i
  letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
  letI : IsProbabilityMeasure passive.Pbase := passive.isProbability
  have hrawInt : Integrable (fun y : (ℤ → ℝ) × (ℤ → ℝ) =>
      Probability.PoissonProcess.palmTaggedPoissonWorkFutureAggregate y t) tagged.Ptag := by
    change Integrable (fun y : (ℤ → ℝ) × (ℤ → ℝ) =>
      Probability.PoissonProcess.palmTaggedPoissonWorkFutureAggregate y t)
      ((Probability.PoissonProcess.twoSidedInterarrivalMeasure (arrivalRate i)).prod
        (Probability.PoissonProcess.twoSidedInterarrivalMeasure (1 : ℝ)))
    exact Probability.PoissonProcess.integrable_palmTaggedPoissonWorkFutureAggregate
      (harrivalRate i) ht
  have hrawMean : ∫ y : (ℤ → ℝ) × (ℤ → ℝ),
      Probability.PoissonProcess.palmTaggedPoissonWorkFutureAggregate y t ∂tagged.Ptag =
      arrivalRate i * t := by
    change ∫ y : (ℤ → ℝ) × (ℤ → ℝ),
      Probability.PoissonProcess.palmTaggedPoissonWorkFutureAggregate y t
        ∂((Probability.PoissonProcess.twoSidedInterarrivalMeasure (arrivalRate i)).prod
          (Probability.PoissonProcess.twoSidedInterarrivalMeasure (1 : ℝ))) =
        arrivalRate i * t
    exact Probability.PoissonProcess.integral_palmTaggedPoissonWorkFutureAggregate
      (harrivalRate i) ht
  have hliftInt : Integrable (fun z :
      MulticlassStationaryPoissonWorkClassTaggedSample Class i =>
      Probability.PoissonProcess.palmTaggedPoissonWorkFutureAggregate z.1 t)
      (tagged.Ptag.prod passive.Pbase) := by
    simpa [Function.comp_def] using hrawInt.comp_fst passive.Pbase
  change ∫ z, stationaryPriorityClassTaggedFutureWorkAggregate meanService i z t
    ∂(tagged.Ptag.prod passive.Pbase) =
      arrivalRate i * meanService i * t
  calc
    ∫ z, stationaryPriorityClassTaggedFutureWorkAggregate meanService i z t
        ∂(tagged.Ptag.prod passive.Pbase) =
        ∫ z, meanService i *
          Probability.PoissonProcess.palmTaggedPoissonWorkFutureAggregate z.1 t
          ∂(tagged.Ptag.prod passive.Pbase) := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with z
            exact stationaryPriorityClassTaggedFutureWorkAggregate_eq meanService i z t
    _ = meanService i * ∫ z,
        Probability.PoissonProcess.palmTaggedPoissonWorkFutureAggregate z.1 t
        ∂(tagged.Ptag.prod passive.Pbase) := by
          rw [MeasureTheory.integral_const_mul]
    _ = meanService i * ∫ y : (ℤ → ℝ) × (ℤ → ℝ),
        Probability.PoissonProcess.palmTaggedPoissonWorkFutureAggregate y t ∂tagged.Ptag := by
          congr 1
          calc
            ∫ z, Probability.PoissonProcess.palmTaggedPoissonWorkFutureAggregate z.1 t
                ∂(tagged.Ptag.prod passive.Pbase) =
                ∫ y, ∫ _ : ({j : Class // j ≠ i} → StationaryPoissonWorkPath),
                  Probability.PoissonProcess.palmTaggedPoissonWorkFutureAggregate y t
                  ∂passive.Pbase ∂tagged.Ptag := by
                    exact MeasureTheory.integral_prod _ hliftInt
            _ = ∫ y, Probability.PoissonProcess.palmTaggedPoissonWorkFutureAggregate y t
                  ∂tagged.Ptag := by simp
    _ = meanService i * (arrivalRate i * t) := by rw [hrawMean]
    _ = arrivalRate i * meanService i * t := by ring

/-- The selected Palm class has integrable literal work in every fixed
post-origin horizon.  This exposes the integrability used by the exact
deterministic-horizon work-rate calculation. -/
theorem integrable_stationaryPriorityClassTaggedFutureWorkAggregate
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (i : Class) (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun z => stationaryPriorityClassTaggedFutureWorkAggregate meanService i z t)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  let tagged := Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
    (harrivalRate i)
  let passive := multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i
  letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
  letI : IsProbabilityMeasure passive.Pbase := passive.isProbability
  have hraw : Integrable (fun y : (ℤ → ℝ) × (ℤ → ℝ) =>
      Probability.PoissonProcess.palmTaggedPoissonWorkFutureAggregate y t) tagged.Ptag := by
    change Integrable (fun y : (ℤ → ℝ) × (ℤ → ℝ) =>
      Probability.PoissonProcess.palmTaggedPoissonWorkFutureAggregate y t)
      ((Probability.PoissonProcess.twoSidedInterarrivalMeasure (arrivalRate i)).prod
        (Probability.PoissonProcess.twoSidedInterarrivalMeasure (1 : ℝ)))
    exact Probability.PoissonProcess.integrable_palmTaggedPoissonWorkFutureAggregate
      (harrivalRate i) ht
  have hlift : Integrable (fun z : MulticlassStationaryPoissonWorkClassTaggedSample Class i =>
      Probability.PoissonProcess.palmTaggedPoissonWorkFutureAggregate z.1 t)
      (tagged.Ptag.prod passive.Pbase) := by
    simpa [Function.comp_def] using hraw.comp_fst passive.Pbase
  change Integrable (fun z => stationaryPriorityClassTaggedFutureWorkAggregate meanService i z t)
    (tagged.Ptag.prod passive.Pbase)
  refine (hlift.const_mul (meanService i)).congr ?_
  filter_upwards with z
  exact (stationaryPriorityClassTaggedFutureWorkAggregate_eq meanService i z t).symm

/-- The selected class's actual post-tag work has its physical load rate
under the multiclass Campbell/Palm law.  This is transported from the literal
selected tagged renewal path while all passive streams stay in the carrier. -/
theorem ae_tendsto_stationaryPriorityClassTaggedFutureWorkAggregate_div_atTop
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (i : Class) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      Tendsto (fun t : ℝ =>
        stationaryPriorityClassTaggedFutureWorkAggregate meanService i z t / t)
        atTop (nhds (arrivalRate i * meanService i)) := by
  let tagged := Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
    (harrivalRate i)
  let passive := multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i
  letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
  letI : IsProbabilityMeasure passive.Pbase := passive.isProbability
  have hraw : ∀ᵐ y ∂tagged.Ptag,
      Tendsto (fun t : ℝ =>
        Probability.PoissonProcess.palmTaggedPoissonWorkFutureAggregate y t / t)
        atTop (nhds (arrivalRate i)) := by
    change ∀ᵐ y ∂(Probability.PoissonProcess.twoSidedInterarrivalMeasure
        (arrivalRate i)).prod
        (Probability.PoissonProcess.twoSidedInterarrivalMeasure (1 : ℝ)),
      Tendsto (fun t : ℝ =>
        Probability.PoissonProcess.palmTaggedPoissonWorkFutureAggregate y t / t)
        atTop (nhds (arrivalRate i))
    exact Probability.PoissonProcess.ae_tendsto_palmTaggedPoissonWorkFutureAggregate_div_atTop
      (harrivalRate i)
  have hselected : ∀ᵐ y ∂tagged.Ptag,
      Tendsto (fun t : ℝ => meanService i *
        Probability.PoissonProcess.palmTaggedPoissonWorkFutureAggregate y t / t)
        atTop (nhds (arrivalRate i * meanService i)) := by
    filter_upwards [hraw] with y hy
    convert (tendsto_const_nhds (x := meanService i)).mul hy using 1 <;> ring_nf
  have hlift : ∀ᵐ z ∂(tagged.Ptag.prod passive.Pbase),
      Tendsto (fun t : ℝ => meanService i *
        Probability.PoissonProcess.palmTaggedPoissonWorkFutureAggregate z.1 t / t)
        atTop (nhds (arrivalRate i * meanService i)) := by
    refine ae_of_ae_map (μ := tagged.Ptag.prod passive.Pbase) (f := Prod.fst)
      (p := fun y : (ℤ → ℝ) × (ℤ → ℝ) =>
        Tendsto (fun t : ℝ => meanService i *
          Probability.PoissonProcess.palmTaggedPoissonWorkFutureAggregate y t / t)
          atTop (nhds (arrivalRate i * meanService i)))
      measurable_fst.aemeasurable ?_
    rw [Measure.map_fst_prod, measure_univ, one_smul]
    exact hselected
  change ∀ᵐ z ∂(tagged.Ptag.prod passive.Pbase),
    Tendsto (fun t : ℝ =>
      stationaryPriorityClassTaggedFutureWorkAggregate meanService i z t / t)
      atTop (nhds (arrivalRate i * meanService i))
  filter_upwards [hlift] with z hz
  refine hz.congr' ?_
  filter_upwards [Filter.Eventually.of_forall (fun t : ℝ =>
    (stationaryPriorityClassTaggedFutureWorkAggregate_eq meanService i z t).symm)]
    with t ht
  exact congrArg (fun x : ℝ => x / t) ht

/-- Total scaled work of a specified class arriving after the selected Palm
tag and no later than `t`.  The selected stream uses its literal Palm ledger;
passive streams use their literal stationary ledgers. -/
def stationaryPriorityTaggedFutureWorkAggregate
    (meanService : Class → ℝ) (i : Class)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample Class i)
    (j : Class) (t : ℝ) : ℝ :=
  if hji : j = i then
    (Probability.PoissonProcess.palmTaggedArrivalIndicesRightClosed 0 t z.1.1).sum
      (stationaryPriorityClassTaggedWorkRequirementAt meanService i z j)
  else
    (Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0 t
      (z.2 ⟨j, hji⟩).1).sum
        (stationaryPriorityClassTaggedWorkRequirementAt meanService i z j)

/-- A class's future marked-work ledger is nonnegative whenever its listed
work requirements are nonnegative. -/
theorem stationaryPriorityTaggedFutureWorkAggregate_nonneg
    (meanService : Class → ℝ) (i : Class)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample Class i)
    (j : Class) (t : ℝ)
    (hwork : ∀ k, 0 ≤ stationaryPriorityClassTaggedWorkRequirementAt
      meanService i z j k) :
    0 ≤ stationaryPriorityTaggedFutureWorkAggregate meanService i z j t := by
  unfold stationaryPriorityTaggedFutureWorkAggregate
  split_ifs <;> exact Finset.sum_nonneg fun k _ => hwork k

/-- On the selected class, the all-class future aggregate is the selected
Palm aggregate. -/
theorem stationaryPriorityTaggedFutureWorkAggregate_self
    (meanService : Class → ℝ) (i : Class)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample Class i) (t : ℝ) :
    stationaryPriorityTaggedFutureWorkAggregate meanService i z i t =
      stationaryPriorityClassTaggedFutureWorkAggregate meanService i z t := by
  simp [stationaryPriorityTaggedFutureWorkAggregate,
    stationaryPriorityClassTaggedFutureWorkAggregate]

/-- On a passive class, the selected-arrival future aggregate is its ordinary
stationary future marked-work aggregate, scaled by its mean service. -/
theorem stationaryPriorityTaggedFutureWorkAggregate_of_ne
    (meanService : Class → ℝ) (i j : Class) (hji : j ≠ i)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample Class i) (t : ℝ) :
    stationaryPriorityTaggedFutureWorkAggregate meanService i z j t =
      meanService j * Probability.Queueing.stationaryPoissonWorkFutureAggregate
        (z.2 ⟨j, hji⟩) t := by
  simp only [stationaryPriorityTaggedFutureWorkAggregate, dif_neg hji]
  rw [Probability.Queueing.stationaryPoissonWorkFutureAggregate, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp [stationaryPriorityClassTaggedWorkRequirementAt,
    multiclassStationaryPoissonWorkClassTaggedRequirementAt, hji,
    Probability.Queueing.stationaryPoissonWorkRequirement]

/-- A passive class's literal post-origin work is Borel when evaluated at a
measurable horizon of the full selected-arrival input.  This is a statement
about the marked input ledger only; no queue-response property is used. -/
theorem measurable_stationaryPriorityTaggedFutureWorkAggregate_of_ne_comp
    (meanService : Class → ℝ) (i j : Class) (hji : j ≠ i)
    (horizon : MulticlassStationaryPoissonWorkClassTaggedSample Class i → ℝ)
    (hhorizon : Measurable horizon) :
    Measurable (fun z : MulticlassStationaryPoissonWorkClassTaggedSample Class i =>
      stationaryPriorityTaggedFutureWorkAggregate meanService i z j (horizon z)) := by
  let passivePath : MulticlassStationaryPoissonWorkClassTaggedSample Class i →
      Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ) :=
    fun z => z.2 ⟨j, hji⟩
  have hpassivePath : Measurable passivePath := by
    exact (measurable_pi_apply
      (X := fun _ : {k : Class // k ≠ i} => StationaryPoissonWorkPath)
      ⟨j, hji⟩).comp measurable_snd
  simpa [stationaryPriorityTaggedFutureWorkAggregate,
    stationaryPriorityClassTaggedWorkRequirementAt,
    multiclassStationaryPoissonWorkClassTaggedRequirementAt, passivePath, hji] using
    (measurable_scaledStationaryPoissonWorkFutureWindow (meanService j)).comp
      (hhorizon.prodMk hpassivePath)

/-- The same passive future-work observable is almost-everywhere measurable
at an almost-everywhere measurable horizon.  This form is suitable for a
random stopping or response time without replacing it by an auxiliary
measurable representative. -/
theorem aemeasurable_stationaryPriorityTaggedFutureWorkAggregate_of_ne_comp
    (meanService : Class → ℝ) (i j : Class) (hji : j ≠ i)
    (horizon : MulticlassStationaryPoissonWorkClassTaggedSample Class i → ℝ)
    (M : Measure (MulticlassStationaryPoissonWorkClassTaggedSample Class i))
    (hhorizon : AEMeasurable horizon M) :
    AEMeasurable (fun z : MulticlassStationaryPoissonWorkClassTaggedSample Class i =>
      stationaryPriorityTaggedFutureWorkAggregate meanService i z j (horizon z)) M := by
  let passivePath : MulticlassStationaryPoissonWorkClassTaggedSample Class i →
      Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ) :=
    fun z => z.2 ⟨j, hji⟩
  have hpassivePath : Measurable passivePath := by
    exact (measurable_pi_apply
      (X := fun _ : {k : Class // k ≠ i} => StationaryPoissonWorkPath)
      ⟨j, hji⟩).comp measurable_snd
  simpa [stationaryPriorityTaggedFutureWorkAggregate,
    stationaryPriorityClassTaggedWorkRequirementAt,
    multiclassStationaryPoissonWorkClassTaggedRequirementAt, passivePath, hji] using
    (measurable_scaledStationaryPoissonWorkFutureWindow (meanService j)).comp_aemeasurable
      (hhorizon.prodMk hpassivePath.aemeasurable)

/-- A passive class retains its exact deterministic-horizon expected work
after the selected class is Palm-recentered. -/
theorem integral_stationaryPriorityTaggedFutureWorkAggregate_of_ne
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i j : Class) (hji : j ≠ i) (t : ℝ) (ht : 0 ≤ t) :
    ∫ z, stationaryPriorityTaggedFutureWorkAggregate meanService i z j t
      ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag =
      arrivalRate j * meanService j * t := by
  let tagged := Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
    (harrivalRate i)
  let passive := multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i
  let restRate : {k : Class // k ≠ i} → ℝ := fun k => arrivalRate k.1
  let selectedPassive : {k : Class // k ≠ i} := ⟨j, hji⟩
  letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
  letI : IsProbabilityMeasure passive.Pbase := passive.isProbability
  have hrawInt := Probability.Queueing.integrable_stationaryPoissonWorkFutureAggregate
    (harrivalRate j) ht
  have hrestInt : Integrable (fun w : {k : Class // k ≠ i} → StationaryPoissonWorkPath =>
      Probability.Queueing.stationaryPoissonWorkFutureAggregate (w selectedPassive) t)
      passive.Pbase := by
    change Integrable (fun w : {k : Class // k ≠ i} → StationaryPoissonWorkPath =>
      Probability.Queueing.stationaryPoissonWorkFutureAggregate (w selectedPassive) t)
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure restRate)
    simpa [restRate, selectedPassive] using
      ((Probability.PoissonProcess.measurePreserving_multiclassStationaryPoissonWorkPath
        restRate (fun k => harrivalRate k.1) selectedPassive).integrable_comp
        hrawInt.aestronglyMeasurable).mpr hrawInt
  have hrestMean : ∫ w : {k : Class // k ≠ i} → StationaryPoissonWorkPath,
      Probability.Queueing.stationaryPoissonWorkFutureAggregate (w selectedPassive) t
        ∂passive.Pbase = arrivalRate j * t := by
    change ∫ w : {k : Class // k ≠ i} → StationaryPoissonWorkPath,
      Probability.Queueing.stationaryPoissonWorkFutureAggregate (w selectedPassive) t
        ∂(Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure restRate) =
        arrivalRate j * t
    calc
      ∫ w : {k : Class // k ≠ i} → StationaryPoissonWorkPath,
          Probability.Queueing.stationaryPoissonWorkFutureAggregate (w selectedPassive) t
          ∂(Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure restRate) =
          ∫ q, Probability.Queueing.stationaryPoissonWorkFutureAggregate q t
            ∂Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate j) := by
              simpa [restRate, selectedPassive, Function.comp_def] using
                (Probability.PoissonProcess.measurePreserving_multiclassStationaryPoissonWorkPath
                  restRate (fun k => harrivalRate k.1) selectedPassive).hasLaw.integral_comp
                  (f := fun q =>
                    Probability.Queueing.stationaryPoissonWorkFutureAggregate q t)
                  hrawInt.aestronglyMeasurable
      _ = arrivalRate j * t :=
        Probability.Queueing.integral_stationaryPoissonWorkFutureAggregate
          (harrivalRate j) ht
  have hliftInt : Integrable (fun z :
      MulticlassStationaryPoissonWorkClassTaggedSample Class i =>
      Probability.Queueing.stationaryPoissonWorkFutureAggregate (z.2 selectedPassive) t)
      (tagged.Ptag.prod passive.Pbase) := by
    simpa [Function.comp_def] using hrestInt.comp_snd tagged.Ptag
  change ∫ z, stationaryPriorityTaggedFutureWorkAggregate meanService i z j t
      ∂(tagged.Ptag.prod passive.Pbase) = arrivalRate j * meanService j * t
  calc
    ∫ z, stationaryPriorityTaggedFutureWorkAggregate meanService i z j t
        ∂(tagged.Ptag.prod passive.Pbase) =
        ∫ z, meanService j *
          Probability.Queueing.stationaryPoissonWorkFutureAggregate
            (z.2 selectedPassive) t ∂(tagged.Ptag.prod passive.Pbase) := by
              refine MeasureTheory.integral_congr_ae ?_
              filter_upwards with z
              simpa [selectedPassive] using
                stationaryPriorityTaggedFutureWorkAggregate_of_ne meanService i j hji z t
    _ = meanService j * ∫ z,
        Probability.Queueing.stationaryPoissonWorkFutureAggregate
          (z.2 selectedPassive) t ∂(tagged.Ptag.prod passive.Pbase) := by
            rw [MeasureTheory.integral_const_mul]
    _ = meanService j * ∫ w : {k : Class // k ≠ i} → StationaryPoissonWorkPath,
        Probability.Queueing.stationaryPoissonWorkFutureAggregate (w selectedPassive) t
          ∂passive.Pbase := by
            congr 1
            calc
              ∫ z, Probability.Queueing.stationaryPoissonWorkFutureAggregate
                  (z.2 selectedPassive) t ∂(tagged.Ptag.prod passive.Pbase) =
                  ∫ _ : (ℤ → ℝ) × (ℤ → ℝ), ∫ w,
                    Probability.Queueing.stationaryPoissonWorkFutureAggregate
                      (w selectedPassive) t ∂passive.Pbase ∂tagged.Ptag := by
                      exact MeasureTheory.integral_prod _ hliftInt
              _ = ∫ _ : (ℤ → ℝ) × (ℤ → ℝ), arrivalRate j * t ∂tagged.Ptag := by
                    refine MeasureTheory.integral_congr_ae ?_
                    filter_upwards with _
                    exact hrestMean
              _ = ∫ w : {k : Class // k ≠ i} → StationaryPoissonWorkPath,
                    Probability.Queueing.stationaryPoissonWorkFutureAggregate
                      (w selectedPassive) t ∂passive.Pbase := by
                    rw [hrestMean]
                    simp
    _ = meanService j * (arrivalRate j * t) := by rw [hrestMean]
    _ = arrivalRate j * meanService j * t := by ring

/-- A passive class has integrable literal work in every fixed post-origin
horizon under the selected-arrival Palm law. -/
theorem integrable_stationaryPriorityTaggedFutureWorkAggregate_of_ne
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i j : Class) (hji : j ≠ i) (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun z => stationaryPriorityTaggedFutureWorkAggregate meanService i z j t)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  let tagged := Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
    (harrivalRate i)
  let passive := multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i
  let restRate : {k : Class // k ≠ i} → ℝ := fun k => arrivalRate k.1
  let selectedPassive : {k : Class // k ≠ i} := ⟨j, hji⟩
  letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
  letI : IsProbabilityMeasure passive.Pbase := passive.isProbability
  have hraw := Probability.Queueing.integrable_stationaryPoissonWorkFutureAggregate
    (harrivalRate j) ht
  have hrest : Integrable (fun w : {k : Class // k ≠ i} → StationaryPoissonWorkPath =>
      Probability.Queueing.stationaryPoissonWorkFutureAggregate (w selectedPassive) t)
      passive.Pbase := by
    change Integrable (fun w : {k : Class // k ≠ i} → StationaryPoissonWorkPath =>
      Probability.Queueing.stationaryPoissonWorkFutureAggregate (w selectedPassive) t)
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure restRate)
    simpa [restRate, selectedPassive] using
      ((Probability.PoissonProcess.measurePreserving_multiclassStationaryPoissonWorkPath
        restRate (fun k => harrivalRate k.1) selectedPassive).integrable_comp
        hraw.aestronglyMeasurable).mpr hraw
  have hlift : Integrable (fun z : MulticlassStationaryPoissonWorkClassTaggedSample Class i =>
      Probability.Queueing.stationaryPoissonWorkFutureAggregate (z.2 selectedPassive) t)
      (tagged.Ptag.prod passive.Pbase) := by
    simpa [Function.comp_def] using hrest.comp_snd tagged.Ptag
  change Integrable (fun z => stationaryPriorityTaggedFutureWorkAggregate meanService i z j t)
    (tagged.Ptag.prod passive.Pbase)
  refine (hlift.const_mul (meanService j)).congr ?_
  filter_upwards with z
  exact (stationaryPriorityTaggedFutureWorkAggregate_of_ne meanService i j hji z t).symm

/-- Every passive class retains its own stationary future-work rate after the
selected class is Palm-recentered. -/
theorem ae_tendsto_stationaryPriorityTaggedFutureWorkAggregate_of_ne_div_atTop
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (i j : Class) (hji : j ≠ i) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      Tendsto (fun t : ℝ =>
        stationaryPriorityTaggedFutureWorkAggregate meanService i z j t / t)
        atTop (nhds (arrivalRate j * meanService j)) := by
  let tagged := Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
    (harrivalRate i)
  let passive := multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i
  let restRate : {k : Class // k ≠ i} → ℝ := fun k => arrivalRate k.1
  let selectedPassive : {k : Class // k ≠ i} := ⟨j, hji⟩
  letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
  letI : IsProbabilityMeasure passive.Pbase := passive.isProbability
  have hraw : ∀ᵐ w ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure restRate,
      Tendsto (fun t : ℝ =>
        Probability.Queueing.stationaryPoissonWorkFutureAggregate
          (w selectedPassive) t / t)
        atTop (nhds (arrivalRate j)) := by
      refine ae_of_ae_map
        (μ := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure restRate)
        (f := Function.eval selectedPassive)
        (p := fun q : Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ) =>
          Tendsto (fun t : ℝ =>
            Probability.Queueing.stationaryPoissonWorkFutureAggregate q t / t)
            atTop (nhds (arrivalRate j)))
        (Probability.PoissonProcess.measurePreserving_multiclassStationaryPoissonWorkPath
          restRate (fun k => harrivalRate k.1) selectedPassive).measurable.aemeasurable ?_
      rw [(Probability.PoissonProcess.measurePreserving_multiclassStationaryPoissonWorkPath
        restRate (fun k => harrivalRate k.1) selectedPassive).map_eq]
      simpa [restRate, selectedPassive] using
        (Probability.Queueing.ae_tendsto_stationaryPoissonWorkFutureAggregate_div_atTop
          (harrivalRate j))
  have hrest : ∀ᵐ w ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure restRate,
      Tendsto (fun t : ℝ => meanService j *
        Probability.Queueing.stationaryPoissonWorkFutureAggregate
          (w selectedPassive) t / t)
        atTop (nhds (arrivalRate j * meanService j)) := by
    filter_upwards [hraw] with w hw
    convert (tendsto_const_nhds (x := meanService j)).mul hw using 1 <;> ring_nf
  have hpassiveBase : ∀ᵐ w ∂passive.Pbase,
      Tendsto (fun t : ℝ => meanService j *
        Probability.Queueing.stationaryPoissonWorkFutureAggregate
          (w selectedPassive) t / t)
        atTop (nhds (arrivalRate j * meanService j)) := by
    simpa [passive, restRate, multiclassStationaryPoissonWorkRestLaw] using hrest
  have hlift : ∀ᵐ z ∂(tagged.Ptag.prod passive.Pbase),
      Tendsto (fun t : ℝ => meanService j *
        Probability.Queueing.stationaryPoissonWorkFutureAggregate
          (z.2 selectedPassive) t / t)
        atTop (nhds (arrivalRate j * meanService j)) := by
    refine ae_of_ae_map (μ := tagged.Ptag.prod passive.Pbase) (f := Prod.snd)
      (p := fun w : {k : Class // k ≠ i} → StationaryPoissonWorkPath =>
        Tendsto (fun t : ℝ => meanService j *
          Probability.Queueing.stationaryPoissonWorkFutureAggregate
            (w selectedPassive) t / t)
          atTop (nhds (arrivalRate j * meanService j)))
      measurable_snd.aemeasurable ?_
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    exact hpassiveBase
  change ∀ᵐ z ∂(tagged.Ptag.prod passive.Pbase),
    Tendsto (fun t : ℝ =>
      stationaryPriorityTaggedFutureWorkAggregate meanService i z j t / t)
      atTop (nhds (arrivalRate j * meanService j))
  filter_upwards [hlift] with z hz
  refine hz.congr' ?_
  filter_upwards [Filter.Eventually.of_forall (fun t : ℝ =>
    (stationaryPriorityTaggedFutureWorkAggregate_of_ne meanService i j hji z t).symm)]
    with t ht
  exact congrArg (fun x : ℝ => x / t) ht

/-- Every class's selected-arrival future work has its physical load rate. -/
theorem ae_tendsto_stationaryPriorityTaggedFutureWorkAggregate_div_atTop
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (i j : Class) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      Tendsto (fun t : ℝ =>
        stationaryPriorityTaggedFutureWorkAggregate meanService i z j t / t)
        atTop (nhds (arrivalRate j * meanService j)) := by
  by_cases hji : j = i
  · subst j
    simpa only [stationaryPriorityTaggedFutureWorkAggregate_self] using
      (ae_tendsto_stationaryPriorityClassTaggedFutureWorkAggregate_div_atTop
        arrivalRate meanService harrivalRate i)
  · exact ae_tendsto_stationaryPriorityTaggedFutureWorkAggregate_of_ne_div_atTop
      arrivalRate meanService harrivalRate i j hji

/-- Total work of all classes arriving after the selected Palm tag and no
later than `t`. -/
def stationaryPriorityTaggedTotalFutureWorkAggregate
    (meanService : Class → ℝ) (i : Class)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample Class i) (t : ℝ) : ℝ :=
  ∑ j, stationaryPriorityTaggedFutureWorkAggregate meanService i z j t

/-- Every class's selected-arrival future-work ledger is integrable at a fixed
horizon. -/
theorem integrable_stationaryPriorityTaggedFutureWorkAggregate
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (i j : Class) (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun z => stationaryPriorityTaggedFutureWorkAggregate meanService i z j t)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  by_cases hji : j = i
  · subst j
    simpa only [stationaryPriorityTaggedFutureWorkAggregate_self] using
      integrable_stationaryPriorityClassTaggedFutureWorkAggregate
        arrivalRate meanService harrivalRate i t ht
  · exact integrable_stationaryPriorityTaggedFutureWorkAggregate_of_ne
      arrivalRate meanService harrivalRate i j hji t ht

/-- Total marked work arriving after the selected Palm tag is integrable at
every deterministic nonnegative horizon. -/
theorem integrable_stationaryPriorityTaggedTotalFutureWorkAggregate
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (i : Class) (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun z => stationaryPriorityTaggedTotalFutureWorkAggregate meanService i z t)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  apply MeasureTheory.integrable_finset_sum Finset.univ
  intro j _
  exact integrable_stationaryPriorityTaggedFutureWorkAggregate
    arrivalRate meanService harrivalRate i j t ht

/-- The total deterministic-horizon post-tag work has expectation equal to
the aggregate offered-work rate times elapsed time. -/
theorem integral_stationaryPriorityTaggedTotalFutureWorkAggregate
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (i : Class) (t : ℝ) (ht : 0 ≤ t) :
    ∫ z, stationaryPriorityTaggedTotalFutureWorkAggregate meanService i z t
      ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag =
      (∑ j, arrivalRate j * meanService j) * t := by
  let tagged := Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
    (harrivalRate i)
  let passive := multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i
  change ∫ z, ∑ j, stationaryPriorityTaggedFutureWorkAggregate meanService i z j t
    ∂(tagged.Ptag.prod passive.Pbase) = _
  calc
    ∫ z, ∑ j, stationaryPriorityTaggedFutureWorkAggregate meanService i z j t
        ∂(tagged.Ptag.prod passive.Pbase) =
        ∑ j, ∫ z, stationaryPriorityTaggedFutureWorkAggregate meanService i z j t
          ∂(tagged.Ptag.prod passive.Pbase) := by
            exact MeasureTheory.integral_finset_sum Finset.univ fun j _ =>
              integrable_stationaryPriorityTaggedFutureWorkAggregate
                arrivalRate meanService harrivalRate i j t ht
    _ = ∑ j, arrivalRate j * meanService j * t := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases hji : j = i
          · subst j
            simpa only [stationaryPriorityTaggedFutureWorkAggregate_self] using
              integral_stationaryPriorityClassTaggedFutureWorkAggregate
                arrivalRate meanService harrivalRate i t ht
          · exact integral_stationaryPriorityTaggedFutureWorkAggregate_of_ne
              arrivalRate meanService harrivalRate i j hji t ht
    _ = (∑ j, arrivalRate j * meanService j) * t := by
          rw [Finset.sum_mul]

/-- The total selected-arrival future input has the sum of class load rates. -/
theorem ae_tendsto_stationaryPriorityTaggedTotalFutureWorkAggregate_div_atTop
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (i : Class) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      Tendsto (fun t : ℝ =>
        stationaryPriorityTaggedTotalFutureWorkAggregate meanService i z t / t)
        atTop (nhds (∑ j, arrivalRate j * meanService j)) := by
  have hclass : ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      ∀ j : Class,
        Tendsto (fun t : ℝ =>
          stationaryPriorityTaggedFutureWorkAggregate meanService i z j t / t)
          atTop (nhds (arrivalRate j * meanService j)) := by
    rw [ae_all_iff]
    intro j
    exact ae_tendsto_stationaryPriorityTaggedFutureWorkAggregate_div_atTop
      arrivalRate meanService harrivalRate i j
  filter_upwards [hclass] with z hz
  have hsum : Tendsto (fun t : ℝ => ∑ j,
      stationaryPriorityTaggedFutureWorkAggregate meanService i z j t / t)
      atTop (nhds (∑ j, arrivalRate j * meanService j)) :=
    tendsto_finset_sum _ fun j _ => hz j
  simpa [stationaryPriorityTaggedTotalFutureWorkAggregate, Finset.sum_div] using hsum

/-- Cumulative net input after the selected Palm arrival: literal arriving
work in `(0,t]` minus the unit-rate service capacity over that interval. -/
def stationaryPriorityTaggedNetFutureInput
    (meanService : Class → ℝ) (i : Class)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample Class i) (t : ℝ) : ℝ :=
  stationaryPriorityTaggedTotalFutureWorkAggregate meanService i z t - t

/-- The literal selected-Palm net input is integrable at every deterministic
nonnegative horizon. -/
theorem integrable_stationaryPriorityTaggedNetFutureInput
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (i : Class) (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun z => stationaryPriorityTaggedNetFutureInput meanService i z t)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  let tagged := Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
    (harrivalRate i)
  let passive := multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i
  letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
  letI : IsProbabilityMeasure passive.Pbase := passive.isProbability
  change Integrable (fun z =>
    stationaryPriorityTaggedTotalFutureWorkAggregate meanService i z t - t)
      (tagged.Ptag.prod passive.Pbase)
  exact (integrable_stationaryPriorityTaggedTotalFutureWorkAggregate
    arrivalRate meanService harrivalRate i t ht).sub
    (integrable_const t : Integrable (fun _ :
      MulticlassStationaryPoissonWorkClassTaggedSample Class i => t)
      (tagged.Ptag.prod passive.Pbase))

/-- The expected deterministic-horizon selected-Palm net input is its strict
load drift times elapsed time. -/
theorem integral_stationaryPriorityTaggedNetFutureInput
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (i : Class) (t : ℝ) (ht : 0 ≤ t) :
    ∫ z, stationaryPriorityTaggedNetFutureInput meanService i z t
      ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag =
      ((∑ j, arrivalRate j * meanService j) - 1) * t := by
  let tagged := Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
    (harrivalRate i)
  let passive := multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i
  letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
  letI : IsProbabilityMeasure passive.Pbase := passive.isProbability
  change ∫ z, stationaryPriorityTaggedTotalFutureWorkAggregate meanService i z t - t
    ∂(tagged.Ptag.prod passive.Pbase) = _
  have htotal :
      ∫ z, stationaryPriorityTaggedTotalFutureWorkAggregate meanService i z t
        ∂(tagged.Ptag.prod passive.Pbase) =
        (∑ j, arrivalRate j * meanService j) * t := by
    simpa only [tagged, passive] using
      integral_stationaryPriorityTaggedTotalFutureWorkAggregate
        arrivalRate meanService harrivalRate i t ht
  rw [MeasureTheory.integral_sub]
  · rw [htotal]
    simp
    ring
  · exact integrable_stationaryPriorityTaggedTotalFutureWorkAggregate
      arrivalRate meanService harrivalRate i t ht
  · exact (integrable_const t : Integrable (fun _ :
      MulticlassStationaryPoissonWorkClassTaggedSample Class i => t)
      (tagged.Ptag.prod passive.Pbase))

/-- Under strict total load, literal cumulative post-tag net input tends to
`-∞` almost surely.  This is an input-path drift statement, before any queue
response or completion argument is invoked. -/
theorem ae_tendsto_stationaryPriorityTaggedNetFutureInput_atBot
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Class) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      Tendsto (fun t : ℝ => stationaryPriorityTaggedNetFutureInput meanService i z t)
        atTop atBot := by
  filter_upwards [ae_tendsto_stationaryPriorityTaggedTotalFutureWorkAggregate_div_atTop
    arrivalRate meanService harrivalRate i] with z hwork
  have hdiv : Tendsto (fun t : ℝ =>
      (t - stationaryPriorityTaggedTotalFutureWorkAggregate meanService i z t) / t)
      atTop (nhds (1 - ∑ j, arrivalRate j * meanService j)) := by
    apply (tendsto_const_nhds.sub hwork).congr'
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
    field_simp [ht]
  have hpositive : Tendsto (fun t : ℝ =>
      t - stationaryPriorityTaggedTotalFutureWorkAggregate meanService i z t) atTop atTop :=
    tendsto_id.num (sub_pos.mpr hstable) hdiv
  simpa [stationaryPriorityTaggedNetFutureInput, Function.comp_def] using
    tendsto_neg_atTop_atBot.comp hpositive

/-- On a passive class, the selected-arrival past aggregate is precisely the
ordinary stationary marked-Poisson past aggregate, scaled by that class's
mean service requirement. -/
theorem stationaryPriorityTaggedPastWorkAggregate_of_ne
    (meanService : Class → ℝ) (i j : Class) (hji : j ≠ i)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample Class i) (t : ℝ) :
    stationaryPriorityTaggedPastWorkAggregate meanService i z j t =
      meanService j * Probability.Queueing.stationaryPoissonWorkPastAggregate
        (z.2 ⟨j, hji⟩) t := by
  unfold stationaryPriorityTaggedPastWorkAggregate
  rw [show stationaryPriorityClassTaggedArrivalWindowIndices i z (-t) 0 j =
      Probability.PoissonProcess.suspensionBaseArrivalIndices (-t) 0
        (z.2 ⟨j, hji⟩).1 by
        simp [stationaryPriorityClassTaggedArrivalWindowIndices, hji]]
  rw [Probability.Queueing.stationaryPoissonWorkPastAggregate, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp [stationaryPriorityClassTaggedWorkRequirementAt,
    multiclassStationaryPoissonWorkClassTaggedRequirementAt, hji,
    Probability.Queueing.stationaryPoissonWorkRequirement]

/-- The selected class's actual past work has its load rate under the
multiclass Campbell/Palm law.  The proof transports the tagged marked-renewal
law through the genuine product lift; passive classes remain on the carrier. -/
theorem ae_tendsto_stationaryPriorityClassTaggedPastWorkAggregate_div_atTop
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (i : Class) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      Tendsto (fun t : ℝ =>
        stationaryPriorityClassTaggedPastWorkAggregate meanService i z t / t)
        atTop (nhds (arrivalRate i * meanService i)) := by
  let tagged := Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
    (harrivalRate i)
  let passive := multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i
  letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
  letI : IsProbabilityMeasure passive.Pbase := passive.isProbability
  have hraw : ∀ᵐ y ∂tagged.Ptag,
      Tendsto (fun t : ℝ =>
        Probability.PoissonProcess.palmTaggedPoissonWorkPastAggregate y t / t)
        atTop (nhds (arrivalRate i)) := by
    change ∀ᵐ y ∂(Probability.PoissonProcess.twoSidedInterarrivalMeasure
        (arrivalRate i)).prod
        (Probability.PoissonProcess.twoSidedInterarrivalMeasure (1 : ℝ)),
      Tendsto (fun t : ℝ =>
        Probability.PoissonProcess.palmTaggedPoissonWorkPastAggregate y t / t)
        atTop (nhds (arrivalRate i))
    exact Probability.PoissonProcess.ae_tendsto_palmTaggedPoissonWorkPastAggregate_div_atTop
      (harrivalRate i)
  have hselected : ∀ᵐ y ∂tagged.Ptag,
      Tendsto (fun t : ℝ => meanService i *
        Probability.PoissonProcess.palmTaggedPoissonWorkPastAggregate y t / t)
        atTop (nhds (arrivalRate i * meanService i)) := by
    filter_upwards [hraw] with y hy
    convert (tendsto_const_nhds (x := meanService i)).mul hy using 1 <;> ring_nf
  have hlift : ∀ᵐ z ∂(tagged.Ptag.prod passive.Pbase),
      Tendsto (fun t : ℝ => meanService i *
        Probability.PoissonProcess.palmTaggedPoissonWorkPastAggregate z.1 t / t)
        atTop (nhds (arrivalRate i * meanService i)) := by
    refine ae_of_ae_map (μ := tagged.Ptag.prod passive.Pbase) (f := Prod.fst)
      (p := fun y : (ℤ → ℝ) × (ℤ → ℝ) =>
        Tendsto (fun t : ℝ => meanService i *
          Probability.PoissonProcess.palmTaggedPoissonWorkPastAggregate y t / t)
          atTop (nhds (arrivalRate i * meanService i)))
      measurable_fst.aemeasurable ?_
    rw [Measure.map_fst_prod, measure_univ, one_smul]
    exact hselected
  change ∀ᵐ z ∂(tagged.Ptag.prod passive.Pbase),
    Tendsto (fun t : ℝ =>
      stationaryPriorityClassTaggedPastWorkAggregate meanService i z t / t)
      atTop (nhds (arrivalRate i * meanService i))
  filter_upwards [hlift] with z hz
  refine hz.congr' ?_
  filter_upwards [Filter.Eventually.of_forall (fun t : ℝ =>
    (stationaryPriorityClassTaggedPastWorkAggregate_eq meanService i z t).symm)]
    with t ht
  exact congrArg (fun x : ℝ => x / t) ht

/-- Every passive class retains its own stationary past-work rate after the
selected class is Palm-recentered. -/
theorem ae_tendsto_stationaryPriorityTaggedPastWorkAggregate_of_ne_div_atTop
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (i j : Class) (hji : j ≠ i) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      Tendsto (fun t : ℝ =>
        stationaryPriorityTaggedPastWorkAggregate meanService i z j t / t)
        atTop (nhds (arrivalRate j * meanService j)) := by
  let tagged := Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
    (harrivalRate i)
  let passive := multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i
  let restRate : {k : Class // k ≠ i} → ℝ := fun k => arrivalRate k.1
  let restMean : {k : Class // k ≠ i} → ℝ := fun k => meanService k.1
  let selectedPassive : {k : Class // k ≠ i} := ⟨j, hji⟩
  letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
  letI : IsProbabilityMeasure passive.Pbase := passive.isProbability
  have hbase := ae_tendsto_stationaryPriorityPastWorkAggregate_div_atTop
      restRate restMean (fun k => harrivalRate k.1) selectedPassive
  have hrest : ∀ᵐ w ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure restRate,
      Tendsto (fun t : ℝ => meanService j *
        Probability.Queueing.stationaryPoissonWorkPastAggregate (w selectedPassive) t / t)
        atTop (nhds (arrivalRate j * meanService j)) := by
    filter_upwards [hbase] with w hw
    simpa [restRate, restMean, selectedPassive,
      stationaryPriorityPastWorkAggregate, stationaryPriorityWorkRequirement,
      Probability.PoissonProcess.multiclassStationaryPoissonWorkRequirement,
      Probability.Queueing.stationaryPoissonWorkPastAggregate,
      Probability.Queueing.stationaryPoissonWorkRequirement,
      Finset.mul_sum, div_eq_mul_inv, mul_assoc, mul_comm] using hw
  have hpassiveBase : ∀ᵐ w ∂passive.Pbase,
      Tendsto (fun t : ℝ => meanService j *
        Probability.Queueing.stationaryPoissonWorkPastAggregate (w selectedPassive) t / t)
        atTop (nhds (arrivalRate j * meanService j)) := by
    simpa [passive, restRate, multiclassStationaryPoissonWorkRestLaw] using hrest
  have hlift : ∀ᵐ z ∂(tagged.Ptag.prod passive.Pbase),
      Tendsto (fun t : ℝ => meanService j *
        Probability.Queueing.stationaryPoissonWorkPastAggregate (z.2 selectedPassive) t / t)
        atTop (nhds (arrivalRate j * meanService j)) := by
    refine ae_of_ae_map (μ := tagged.Ptag.prod passive.Pbase) (f := Prod.snd)
      (p := fun w : {k : Class // k ≠ i} → StationaryPoissonWorkPath =>
        Tendsto (fun t : ℝ => meanService j *
          Probability.Queueing.stationaryPoissonWorkPastAggregate (w selectedPassive) t / t)
          atTop (nhds (arrivalRate j * meanService j)))
      measurable_snd.aemeasurable ?_
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    exact hpassiveBase
  change ∀ᵐ z ∂(tagged.Ptag.prod passive.Pbase),
    Tendsto (fun t : ℝ =>
      stationaryPriorityTaggedPastWorkAggregate meanService i z j t / t)
      atTop (nhds (arrivalRate j * meanService j))
  filter_upwards [hlift] with z hz
  refine hz.congr' ?_
  filter_upwards [Filter.Eventually.of_forall (fun t : ℝ =>
    (stationaryPriorityTaggedPastWorkAggregate_of_ne meanService i j hji z t).symm)]
    with t ht
  exact congrArg (fun x : ℝ => x / t) ht

/-- Every class's actual selected-arrival past work has its physical load
rate: the selected class uses its Palm past renewal, and every other class
uses its stationary passive path. -/
theorem ae_tendsto_stationaryPriorityTaggedPastWorkAggregate_div_atTop
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (i j : Class) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      Tendsto (fun t : ℝ =>
        stationaryPriorityTaggedPastWorkAggregate meanService i z j t / t)
        atTop (nhds (arrivalRate j * meanService j)) := by
  by_cases hji : j = i
  · subst j
    exact ae_tendsto_stationaryPriorityClassTaggedPastWorkAggregate_div_atTop
      arrivalRate meanService harrivalRate i
  · exact ae_tendsto_stationaryPriorityTaggedPastWorkAggregate_of_ne_div_atTop
      arrivalRate meanService harrivalRate i j hji

/-- Total work over all priority classes arriving before the selected Palm
arrival. -/
def stationaryPriorityTaggedTotalPastWorkAggregate
    (meanService : Class → ℝ) (i : Class)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample Class i) (t : ℝ) : ℝ :=
  ∑ j, stationaryPriorityTaggedPastWorkAggregate meanService i z j t

/-- The zero-length selected/Palm past window contains no arriving work. -/
theorem stationaryPriorityTaggedTotalPastWorkAggregate_zero
    (meanService : Class → ℝ) (i : Class)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample Class i) :
    stationaryPriorityTaggedTotalPastWorkAggregate meanService i z 0 = 0 := by
  unfold stationaryPriorityTaggedTotalPastWorkAggregate
    stationaryPriorityTaggedPastWorkAggregate
  apply Finset.sum_eq_zero
  intro j _
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hji : j = i
  · subst j
    simp only [stationaryPriorityClassTaggedArrivalWindowIndices, dif_pos] at hk
    rw [Probability.PoissonProcess.palmTaggedArrivalIndices] at hk
    have hinterval := (Finset.mem_filter.mp hk).2
    linarith
  · simp only [stationaryPriorityClassTaggedArrivalWindowIndices, dif_neg hji] at hk
    rw [Probability.PoissonProcess.suspensionBaseArrivalIndices] at hk
    have hinterval := (Finset.mem_filter.mp hk).2
    linarith

/-- The total selected-arrival past input has the sum of class load rates. -/
theorem ae_tendsto_stationaryPriorityTaggedTotalPastWorkAggregate_div_atTop
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (i : Class) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      Tendsto (fun t : ℝ =>
        stationaryPriorityTaggedTotalPastWorkAggregate meanService i z t / t)
        atTop (nhds (∑ j, arrivalRate j * meanService j)) := by
  have hclass : ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      ∀ j : Class,
        Tendsto (fun t : ℝ =>
          stationaryPriorityTaggedPastWorkAggregate meanService i z j t / t)
          atTop (nhds (arrivalRate j * meanService j)) := by
    rw [ae_all_iff]
    intro j
    exact ae_tendsto_stationaryPriorityTaggedPastWorkAggregate_div_atTop
      arrivalRate meanService harrivalRate i j
  filter_upwards [hclass] with z hz
  have hsum : Tendsto (fun t : ℝ => ∑ j,
      stationaryPriorityTaggedPastWorkAggregate meanService i z j t / t)
      atTop (nhds (∑ j, arrivalRate j * meanService j)) :=
    tendsto_finset_sum _ fun j _ => hz j
  simpa [stationaryPriorityTaggedTotalPastWorkAggregate, Finset.sum_div] using hsum

/-- Cumulative net input before the selected Palm arrival: literal arriving
work minus the unit-rate service capacity over the same physical interval. -/
def stationaryPriorityTaggedNetPastInput
    (meanService : Class → ℝ) (i : Class)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample Class i) (t : ℝ) : ℝ :=
  stationaryPriorityTaggedTotalPastWorkAggregate meanService i z t - t

/-- Under strict total load, literal cumulative net input into the remote
past of a selected Palm arrival tends to `-∞` almost surely. -/
theorem ae_tendsto_stationaryPriorityTaggedNetPastInput_atBot
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Class) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      Tendsto (fun t : ℝ => stationaryPriorityTaggedNetPastInput meanService i z t)
        atTop atBot := by
  filter_upwards [ae_tendsto_stationaryPriorityTaggedTotalPastWorkAggregate_div_atTop
    arrivalRate meanService harrivalRate i] with z hwork
  have hdiv : Tendsto (fun t : ℝ =>
      (t - stationaryPriorityTaggedTotalPastWorkAggregate meanService i z t) / t)
      atTop (nhds (1 - ∑ j, arrivalRate j * meanService j)) := by
    apply (tendsto_const_nhds.sub hwork).congr'
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
    field_simp [ht]
  have hpositive : Tendsto (fun t : ℝ =>
      t - stationaryPriorityTaggedTotalPastWorkAggregate meanService i z t) atTop atTop :=
    tendsto_id.num (sub_pos.mpr hstable) hdiv
  simpa [stationaryPriorityTaggedNetPastInput, Function.comp_def] using
    tendsto_neg_atTop_atBot.comp hpositive

/-- Under the joint selected-class Palm law, the pinned customer's scaled
service requirement has the exponential law with reciprocal mean rate. -/
theorem stationaryPriorityClassTaggedWorkRequirement_hasLaw
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (i : Class) :
    HasLaw (stationaryPriorityClassTaggedWorkRequirement meanService i)
      (expMeasure (meanService i)⁻¹)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  have hscale :
      Measure.map (fun x : ℝ => meanService i * x) (expMeasure (1 : ℝ)) =
        expMeasure (meanService i)⁻¹ := by
    calc
      Measure.map (fun x : ℝ => meanService i * x) (expMeasure (1 : ℝ)) =
          Measure.map (fun x : ℝ => x / (meanService i)⁻¹) (expMeasure (1 : ℝ)) := by
            congr 1
            funext x
            field_simp [ne_of_gt (hmeanService i)]
      _ = expMeasure (meanService i)⁻¹ :=
        Probability.map_div_unitExpMeasure_eq_expMeasure (inv_pos.mpr (hmeanService i))
  exact HasLaw.comp ⟨by fun_prop, hscale⟩
    (multiclassStationaryPoissonWorkClassTaggedRequirement_hasLaw
      arrivalRate harrivalRate i)

/-- The selected Palm customer's service mark has its prescribed mean. -/
theorem integral_stationaryPriorityClassTaggedWorkRequirement
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (i : Class) :
    ∫ z, stationaryPriorityClassTaggedWorkRequirement meanService i z
      ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag =
      meanService i := by
  calc
    ∫ z, stationaryPriorityClassTaggedWorkRequirement meanService i z
        ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
          (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
          (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag =
        ∫ x, x ∂expMeasure (meanService i)⁻¹ :=
      (stationaryPriorityClassTaggedWorkRequirement_hasLaw arrivalRate meanService
        harrivalRate hmeanService i).integral_eq
    _ = meanService i :=
      Probability.integral_id_expMeasure_inv (hmeanService i)

/-- The selected Palm customer's service mark is integrable. -/
theorem integrable_stationaryPriorityClassTaggedWorkRequirement
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (i : Class) :
    Integrable (stationaryPriorityClassTaggedWorkRequirement meanService i)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  let X := stationaryPriorityClassTaggedWorkRequirement meanService i
  let μ := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  have hLaw := stationaryPriorityClassTaggedWorkRequirement_hasLaw arrivalRate meanService
    harrivalRate hmeanService i
  have htarget : Integrable (fun x : ℝ => x) (Measure.map X μ) := by
    rw [hLaw.map_eq]
    exact Probability.integrable_id_expMeasure_inv (hmeanService i)
  exact (integrable_map_measure (f := X) (g := fun x : ℝ => x)
    aestronglyMeasurable_id hLaw.aemeasurable).mp htarget

/-- The selected Palm customer's service mark has second raw moment twice the
square of its prescribed mean. -/
theorem integral_sq_stationaryPriorityClassTaggedWorkRequirement
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (i : Class) :
    ∫ z, (stationaryPriorityClassTaggedWorkRequirement meanService i z) ^ 2
      ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag =
      2 * meanService i ^ 2 := by
  calc
    ∫ z, (stationaryPriorityClassTaggedWorkRequirement meanService i z) ^ 2
        ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
          (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
          (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag =
        ∫ x, x ^ 2 ∂expMeasure (meanService i)⁻¹ := by
      simpa [Function.comp_def] using
        (stationaryPriorityClassTaggedWorkRequirement_hasLaw arrivalRate meanService
          harrivalRate hmeanService i).integral_comp
          (f := fun x : ℝ => x ^ 2) (by fun_prop)
    _ = 2 * meanService i ^ 2 :=
      Probability.integral_sq_expMeasure_inv (hmeanService i)

/-- The square of the selected Palm customer's service mark is integrable. -/
theorem integrable_sq_stationaryPriorityClassTaggedWorkRequirement
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (i : Class) :
    Integrable (fun z => (stationaryPriorityClassTaggedWorkRequirement meanService i z) ^ 2)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  let X := stationaryPriorityClassTaggedWorkRequirement meanService i
  let μ := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  have hLaw := stationaryPriorityClassTaggedWorkRequirement_hasLaw arrivalRate meanService
    harrivalRate hmeanService i
  have htarget : Integrable (fun x : ℝ => x ^ 2) (Measure.map X μ) := by
    rw [hLaw.map_eq]
    exact Probability.integrable_sq_expMeasure_inv (hmeanService i)
  exact (integrable_map_measure (f := X) (g := fun x : ℝ => x ^ 2)
    (by fun_prop) hLaw.aemeasurable).mp htarget

/-- All class-specific scaled work marks are strictly positive almost surely. -/
theorem ae_all_stationaryPriorityWorkRequirement_positive
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      ∀ i : Class, ∀ n : ℤ,
        0 < stationaryPriorityWorkRequirement meanService i omega n := by
  filter_upwards [
    Probability.PoissonProcess.ae_all_multiclassStationaryPoissonWorkRequirement_positive
      arrivalRate harrivalRate] with omega homega
  intro i n
  exact mul_pos (hmeanService i) (homega i n)

/-- A tagged stationary priority-queue work mark has the prescribed mean. -/
theorem integral_stationaryPriorityWorkRequirement
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (i : Class) (n : ℤ) :
    ∫ omega, stationaryPriorityWorkRequirement meanService i omega n
      ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate =
      meanService i := by
  calc
    ∫ omega, stationaryPriorityWorkRequirement meanService i omega n
        ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate =
        ∫ x, x ∂expMeasure (meanService i)⁻¹ :=
      (stationaryPriorityWorkRequirement_hasLaw arrivalRate meanService
        harrivalRate hmeanService i n).integral_eq
    _ = meanService i :=
      Probability.integral_id_expMeasure_inv (hmeanService i)

/-- A tagged stationary priority-queue work mark has second raw moment twice
the squared prescribed mean. -/
theorem integral_sq_stationaryPriorityWorkRequirement
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (i : Class) (n : ℤ) :
    ∫ omega, (stationaryPriorityWorkRequirement meanService i omega n) ^ 2
      ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate =
      2 * meanService i ^ 2 := by
  calc
    ∫ omega, (stationaryPriorityWorkRequirement meanService i omega n) ^ 2
        ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate =
        ∫ x, x ^ 2 ∂expMeasure (meanService i)⁻¹ := by
      simpa [Function.comp_def] using
        (stationaryPriorityWorkRequirement_hasLaw arrivalRate meanService
          harrivalRate hmeanService i n).integral_comp
          (f := fun x : ℝ => x ^ 2) (by fun_prop)
    _ = 2 * meanService i ^ 2 :=
      Probability.integral_sq_expMeasure_inv (hmeanService i)

/-- The tagged stationary work mark is integrable. -/
theorem integrable_stationaryPriorityWorkRequirement
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (i : Class) (n : ℤ) :
    Integrable (fun omega => stationaryPriorityWorkRequirement meanService i omega n)
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate) := by
  let X := fun omega : Class →
    (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) =>
      stationaryPriorityWorkRequirement meanService i omega n
  have hLaw := stationaryPriorityWorkRequirement_hasLaw arrivalRate meanService
    harrivalRate hmeanService i n
  have htarget : Integrable (fun x : ℝ => x)
      (Measure.map X (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure
        arrivalRate)) := by
    rw [hLaw.map_eq]
    exact Probability.integrable_id_expMeasure_inv (hmeanService i)
  have hmap := (integrable_map_measure (f := X) (g := fun x : ℝ => x)
    aestronglyMeasurable_id hLaw.aemeasurable).mp htarget
  simpa [X, Function.comp_def] using hmap

/-- The squared tagged stationary work mark is integrable. -/
theorem integrable_sq_stationaryPriorityWorkRequirement
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (i : Class) (n : ℤ) :
    Integrable (fun omega => (stationaryPriorityWorkRequirement meanService i omega n) ^ 2)
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate) := by
  let X := fun omega : Class →
    (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) =>
      stationaryPriorityWorkRequirement meanService i omega n
  have hLaw := stationaryPriorityWorkRequirement_hasLaw arrivalRate meanService
    harrivalRate hmeanService i n
  have htarget : Integrable (fun x : ℝ => x ^ 2)
      (Measure.map X (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure
        arrivalRate)) := by
    rw [hLaw.map_eq]
    exact Probability.integrable_sq_expMeasure_inv (hmeanService i)
  have hmap := (integrable_map_measure (f := X) (g := fun x : ℝ => x ^ 2)
    (by fun_prop) hLaw.aemeasurable).mp htarget
  simpa [X, Function.comp_def] using hmap

end

end Queueing
end AppliedModelingLib

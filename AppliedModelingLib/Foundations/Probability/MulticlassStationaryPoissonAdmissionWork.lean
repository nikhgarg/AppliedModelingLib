import AppliedModelingLib.Foundations.Probability.PoissonSuspensionAdmissionWorkMarks
import AppliedModelingLib.Foundations.Probability.Processes.TimedEmbedded.JointFlow
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Independent finite-class stationary Poisson admission/work input

This module takes the source-faithful one-class stationary raw Poisson input
with iid `(admission Bool, work Real)` marks and forms its finite independent
product.  It proves diagonal real-time stationarity and independence of the
complete class paths.

It does not yet turn a target class's selected admitted Palm tag into a joint
Palm law with the other classes.  That requires a Campbell product-lift which
recenters every passive class at the selected target arrival time.  A bare
product of a target tag and passive base law is not asserted here.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory ProbabilityTheory
open scoped NNReal

noncomputable section

variable {Class : Type*} [Fintype Class]

/-- One independent stationary raw Poisson admission/work input per class. -/
noncomputable def multiclassStationaryPoissonAdmissionWorkMeasure
    (arrivalRate : Class → ℝ) (admissionProbability : Class → ℝ≥0)
    (hadmissionProbability : ∀ i, admissionProbability i ≤ 1) :
    Measure (Class → (GoodSuspensionState × (ℤ → (Bool × ℝ)))) :=
  Measure.pi fun i =>
    Queueing.stationaryPoissonAdmissionWorkMeasure (arrivalRate i)
      (admissionProbability i) (hadmissionProbability i)

/-- The common real-time translation applied to every complete class input.
Each coordinate reindexes its Boolean/work path by its own crossed-arrival
label. -/
def multiclassStationaryPoissonAdmissionWorkFlow (t : ℝ) :
    (Class → (GoodSuspensionState × (ℤ → (Bool × ℝ)))) →
      Class → (GoodSuspensionState × (ℤ → (Bool × ℝ))) :=
  fun omega i => Queueing.timedEmbeddedSuspensionFlow (α := Bool × ℝ) t (omega i)

omit [Fintype Class] in
/-- The diagonal marked input flow is jointly measurable in translation time
and in the complete finite vector of class paths. -/
theorem measurable_uncurry_multiclassStationaryPoissonAdmissionWorkFlow :
    Measurable (Function.uncurry
      (multiclassStationaryPoissonAdmissionWorkFlow (Class := Class))) := by
  apply measurable_pi_iff.2
  intro i
  change Measurable (fun q : ℝ ×
      (Class → (GoodSuspensionState × (ℤ → (Bool × ℝ)))) =>
    Queueing.timedEmbeddedSuspensionFlow (α := Bool × ℝ) q.1 (q.2 i))
  exact Queueing.measurable_uncurry_timedEmbeddedSuspensionFlow.comp
    (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))

/-- Positive raw rates make the finite product a probability law. -/
theorem isProbabilityMeasure_multiclassStationaryPoissonAdmissionWorkMeasure
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ i, 0 < arrivalRate i)
    (admissionProbability : Class → ℝ≥0)
    (hadmissionProbability : ∀ i, admissionProbability i ≤ 1) :
    IsProbabilityMeasure
      (multiclassStationaryPoissonAdmissionWorkMeasure arrivalRate
        admissionProbability hadmissionProbability) := by
  let μ : Class → Measure (GoodSuspensionState × (ℤ → (Bool × ℝ))) := fun i =>
    Queueing.stationaryPoissonAdmissionWorkMeasure (arrivalRate i)
      (admissionProbability i) (hadmissionProbability i)
  letI : ∀ i, IsProbabilityMeasure (μ i) := fun i =>
    Queueing.isProbabilityMeasure_stationaryPoissonAdmissionWorkMeasure
      (harrivalRate i) (admissionProbability i) (hadmissionProbability i)
  simpa [multiclassStationaryPoissonAdmissionWorkMeasure, μ] using
    (inferInstance : IsProbabilityMeasure (Measure.pi μ))

/-- The diagonal real-time flow preserves the entire independent multiclass
input law.  This is input stationarity only, not a queue-state theorem. -/
theorem multiclassStationaryPoissonAdmissionWorkFlow_measurePreserving
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ i, 0 < arrivalRate i)
    (admissionProbability : Class → ℝ≥0)
    (hadmissionProbability : ∀ i, admissionProbability i ≤ 1) (t : ℝ) :
    MeasurePreserving
      (multiclassStationaryPoissonAdmissionWorkFlow (Class := Class) t)
      (multiclassStationaryPoissonAdmissionWorkMeasure arrivalRate
        admissionProbability hadmissionProbability)
      (multiclassStationaryPoissonAdmissionWorkMeasure arrivalRate
        admissionProbability hadmissionProbability) := by
  let μ : Class → Measure (GoodSuspensionState × (ℤ → (Bool × ℝ))) := fun i =>
    Queueing.stationaryPoissonAdmissionWorkMeasure (arrivalRate i)
      (admissionProbability i) (hadmissionProbability i)
  letI : ∀ i, IsProbabilityMeasure (μ i) := fun i =>
    Queueing.isProbabilityMeasure_stationaryPoissonAdmissionWorkMeasure
      (harrivalRate i) (admissionProbability i) (hadmissionProbability i)
  letI : ∀ i, SigmaFinite (μ i) := fun _ => by infer_instance
  simpa [multiclassStationaryPoissonAdmissionWorkMeasure,
    multiclassStationaryPoissonAdmissionWorkFlow, μ,
    Queueing.stationaryPoissonAdmissionWorkShiftInvariantLaw] using
    (MeasureTheory.measurePreserving_pi μ μ (fun i =>
      (Queueing.stationaryPoissonAdmissionWorkShiftInvariantLaw
        (harrivalRate i) (admissionProbability i)
        (hadmissionProbability i)).shift_preserving t))

/-- A finite family of independent stationary raw Poisson admission/work
inputs under the common real-time clock. -/
noncomputable def multiclassStationaryPoissonAdmissionWorkShiftInvariantLaw
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ i, 0 < arrivalRate i)
    (admissionProbability : Class → ℝ≥0)
    (hadmissionProbability : ∀ i, admissionProbability i ≤ 1) :
    Palm.ShiftInvariantProbabilityLaw
      (Class → (GoodSuspensionState × (ℤ → (Bool × ℝ)))) where
  Pbase := multiclassStationaryPoissonAdmissionWorkMeasure arrivalRate
    admissionProbability hadmissionProbability
  isProbability := isProbabilityMeasure_multiclassStationaryPoissonAdmissionWorkMeasure
    arrivalRate harrivalRate admissionProbability hadmissionProbability
  shift := multiclassStationaryPoissonAdmissionWorkFlow
  shift_zero := by
    funext omega
    funext i
    change Queueing.timedEmbeddedSuspensionFlow (α := Bool × ℝ) 0 (omega i) = omega i
    exact congrFun Queueing.timedEmbeddedSuspensionFlow_zero (omega i)
  shift_add := by
    intro s t
    funext omega
    funext i
    change Queueing.timedEmbeddedSuspensionFlow (α := Bool × ℝ) (s + t) (omega i) =
      Queueing.timedEmbeddedSuspensionFlow (α := Bool × ℝ) s
        (Queueing.timedEmbeddedSuspensionFlow (α := Bool × ℝ) t (omega i))
    simpa [Function.comp_def] using
      congrFun (Queueing.timedEmbeddedSuspensionFlow_add (α := Bool × ℝ) s t) (omega i)
  shift_preserving := fun t =>
    multiclassStationaryPoissonAdmissionWorkFlow_measurePreserving arrivalRate
      harrivalRate admissionProbability hadmissionProbability t

/-- Joint measurability restated through the packaged multiclass stationary
law. -/
theorem measurable_uncurry_multiclassStationaryPoissonAdmissionWorkShift
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ i, 0 < arrivalRate i)
    (admissionProbability : Class → ℝ≥0)
    (hadmissionProbability : ∀ i, admissionProbability i ≤ 1) :
    Measurable (Function.uncurry
      (multiclassStationaryPoissonAdmissionWorkShiftInvariantLaw
        (Class := Class) arrivalRate harrivalRate admissionProbability
          hadmissionProbability).shift) := by
  simpa [multiclassStationaryPoissonAdmissionWorkShiftInvariantLaw] using
    (measurable_uncurry_multiclassStationaryPoissonAdmissionWorkFlow
      (Class := Class))

/-- Complete raw-arrival/admission/work paths of distinct classes are
independent.  This is full-path independence, not merely independence of
some finite count variables. -/
theorem iIndepFun_multiclassStationaryPoissonAdmissionWorkPaths
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ i, 0 < arrivalRate i)
    (admissionProbability : Class → ℝ≥0)
    (hadmissionProbability : ∀ i, admissionProbability i ≤ 1) :
    iIndepFun
      (fun i (omega : Class → (GoodSuspensionState × (ℤ → (Bool × ℝ)))) => omega i)
      (multiclassStationaryPoissonAdmissionWorkMeasure arrivalRate
        admissionProbability hadmissionProbability) := by
  let μ : Class → Measure (GoodSuspensionState × (ℤ → (Bool × ℝ))) := fun i =>
    Queueing.stationaryPoissonAdmissionWorkMeasure (arrivalRate i)
      (admissionProbability i) (hadmissionProbability i)
  letI : ∀ i, IsProbabilityMeasure (μ i) := fun i =>
    Queueing.isProbabilityMeasure_stationaryPoissonAdmissionWorkMeasure
      (harrivalRate i) (admissionProbability i) (hadmissionProbability i)
  simpa [multiclassStationaryPoissonAdmissionWorkMeasure, μ] using
    (iIndepFun_pi (X := fun _ : Class => id)
      (fun _ => aemeasurable_id))

/-- Projection to a complete class input path is measure-preserving. -/
theorem measurePreserving_multiclassStationaryPoissonAdmissionWorkPath
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ i, 0 < arrivalRate i)
    (admissionProbability : Class → ℝ≥0)
    (hadmissionProbability : ∀ i, admissionProbability i ≤ 1) (i : Class) :
    MeasurePreserving (Function.eval i)
      (multiclassStationaryPoissonAdmissionWorkMeasure arrivalRate
        admissionProbability hadmissionProbability)
      (Queueing.stationaryPoissonAdmissionWorkMeasure (arrivalRate i)
        (admissionProbability i) (hadmissionProbability i)) := by
  let μ : Class → Measure (GoodSuspensionState × (ℤ → (Bool × ℝ))) := fun j =>
    Queueing.stationaryPoissonAdmissionWorkMeasure (arrivalRate j)
      (admissionProbability j) (hadmissionProbability j)
  letI : ∀ j, IsProbabilityMeasure (μ j) := fun j =>
    Queueing.isProbabilityMeasure_stationaryPoissonAdmissionWorkMeasure
      (harrivalRate j) (admissionProbability j) (hadmissionProbability j)
  simpa [multiclassStationaryPoissonAdmissionWorkMeasure, μ] using
    (measurePreserving_eval μ i)

/-- The admission/work pair at a labelled raw class arrival. -/
def multiclassStationaryPoissonAdmissionWorkMarkPair (i : Class) :
    (Class → (GoodSuspensionState × (ℤ → (Bool × ℝ)))) → ℤ → (Bool × ℝ) :=
  fun omega n => (omega i).2 n

/-- The work requirement at a labelled raw class arrival. -/
def multiclassStationaryPoissonAdmissionWorkRequirement (i : Class) :
    (Class → (GoodSuspensionState × (ℤ → (Bool × ℝ)))) → ℤ → ℝ :=
  fun omega n => ((omega i).2 n).2

theorem multiclassStationaryPoissonAdmissionWorkMarkPair_hasLaw
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ i, 0 < arrivalRate i)
    (admissionProbability : Class → ℝ≥0)
    (hadmissionProbability : ∀ i, admissionProbability i ≤ 1)
    (i : Class) (n : ℤ) :
    HasLaw (fun omega : Class → (GoodSuspensionState × (ℤ → (Bool × ℝ))) =>
      multiclassStationaryPoissonAdmissionWorkMarkPair i omega n)
      (Queueing.admissionWorkMarkMeasure (admissionProbability i)
        (hadmissionProbability i))
      (multiclassStationaryPoissonAdmissionWorkMeasure arrivalRate
        admissionProbability hadmissionProbability) := by
  let μ : Class → Measure (GoodSuspensionState × (ℤ → (Bool × ℝ))) := fun j =>
    Queueing.stationaryPoissonAdmissionWorkMeasure (arrivalRate j)
      (admissionProbability j) (hadmissionProbability j)
  letI : ∀ j, IsProbabilityMeasure (μ j) := fun j =>
    Queueing.isProbabilityMeasure_stationaryPoissonAdmissionWorkMeasure
      (harrivalRate j) (admissionProbability j) (hadmissionProbability j)
  simpa [multiclassStationaryPoissonAdmissionWorkMeasure,
    multiclassStationaryPoissonAdmissionWorkMarkPair, μ] using
    (Queueing.stationaryPoissonAdmissionWorkMarkPair_hasLaw
      (harrivalRate i) (admissionProbability i) (hadmissionProbability i) n).comp
      (measurePreserving_eval μ i).hasLaw

theorem multiclassStationaryPoissonAdmissionWorkRequirement_hasLaw
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ i, 0 < arrivalRate i)
    (admissionProbability : Class → ℝ≥0)
    (hadmissionProbability : ∀ i, admissionProbability i ≤ 1)
    (i : Class) (n : ℤ) :
    HasLaw (fun omega : Class → (GoodSuspensionState × (ℤ → (Bool × ℝ))) =>
      multiclassStationaryPoissonAdmissionWorkRequirement i omega n)
      (ProbabilityTheory.expMeasure 1)
      (multiclassStationaryPoissonAdmissionWorkMeasure arrivalRate
        admissionProbability hadmissionProbability) := by
  let μ : Class → Measure (GoodSuspensionState × (ℤ → (Bool × ℝ))) := fun j =>
    Queueing.stationaryPoissonAdmissionWorkMeasure (arrivalRate j)
      (admissionProbability j) (hadmissionProbability j)
  letI : ∀ j, IsProbabilityMeasure (μ j) := fun j =>
    Queueing.isProbabilityMeasure_stationaryPoissonAdmissionWorkMeasure
      (harrivalRate j) (admissionProbability j) (hadmissionProbability j)
  simpa [multiclassStationaryPoissonAdmissionWorkMeasure,
    multiclassStationaryPoissonAdmissionWorkRequirement, μ] using
    (Queueing.stationaryPoissonAdmissionWorkRequirement_hasLaw
      (harrivalRate i) (admissionProbability i) (hadmissionProbability i) n).comp
      (measurePreserving_eval μ i).hasLaw

end

end AppliedModelingLib.Probability.PoissonProcess

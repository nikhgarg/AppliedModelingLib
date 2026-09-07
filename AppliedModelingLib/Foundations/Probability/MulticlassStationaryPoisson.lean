import AppliedModelingLib.Foundations.Probability.PoissonSuspensionWorkMarks
import AppliedModelingLib.Foundations.Probability.Processes.TimedEmbedded.JointFlow
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Independent finite-class stationary Poisson input

This module lifts the literal stationary Poisson suspension to a finite
product of independently sampled classes.  It establishes a stationary
*untagged raw-arrival* carrier: every class has a concrete two-sided arrival
ledger, and the diagonal real-time translation preserves their joint product
law.

The first layer is raw arrivals; the second adjoins iid work marks.  Both
intentionally stop before admission/thinning marks, selection of a tagged
class arrival, a multiclass Campbell/Palm identity, queue dynamics, or queue
stationarity.  A product stationary law alone does not supply any of those
facts.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Class : Type*} [Fintype Class]

/-- One independent literal stationary Poisson suspension state per class. -/
def multiclassStationaryPoissonMeasure (rate : Class -> Real) :
    Measure (Class -> GoodSuspensionState) :=
  Measure.pi fun i => goodSuspensionMeasure (rate i)

/-- The common real-time translation applied coordinatewise to every class. -/
def multiclassStationaryPoissonFlow (t : Real) :
    (Class -> GoodSuspensionState) -> Class -> GoodSuspensionState :=
  fun omega i => goodSuspensionFlow t (omega i)

omit [Fintype Class] in
/-- The raw finite-class stationary input action is jointly measurable in
real time and the full class-indexed carrier. -/
theorem measurable_uncurry_multiclassStationaryPoissonFlow :
    Measurable (Function.uncurry
      (multiclassStationaryPoissonFlow (Class := Class))) := by
  apply measurable_pi_iff.2
  intro i
  change Measurable (fun q : Real × (Class -> GoodSuspensionState) =>
    goodSuspensionFlow q.1 (q.2 i))
  exact measurable_uncurry_goodSuspensionFlow.comp
    (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))

/-- Positively rated classes give a probability law on the full finite input
carrier. -/
theorem isProbabilityMeasure_multiclassStationaryPoissonMeasure
    (rate : Class -> Real) (hrate : ∀ i, 0 < rate i) :
    IsProbabilityMeasure (multiclassStationaryPoissonMeasure rate) := by
  let mu : Class -> Measure GoodSuspensionState := fun i =>
    goodSuspensionMeasure (rate i)
  letI : ∀ i, IsProbabilityMeasure (mu i) := fun i =>
    isProbabilityMeasure_goodSuspensionMeasure (hrate i)
  simpa [multiclassStationaryPoissonMeasure, mu] using
    (inferInstance : IsProbabilityMeasure (Measure.pi mu))

/-- The coordinatewise real-time translation preserves the independent
finite-class stationary input law. -/
theorem multiclassStationaryPoissonFlow_measurePreserving
    (rate : Class -> Real) (hrate : ∀ i, 0 < rate i) (t : Real) :
    MeasurePreserving (multiclassStationaryPoissonFlow (Class := Class) t)
      (multiclassStationaryPoissonMeasure rate)
      (multiclassStationaryPoissonMeasure rate) := by
  let mu : Class -> Measure GoodSuspensionState := fun i =>
    goodSuspensionMeasure (rate i)
  letI : ∀ i, IsProbabilityMeasure (mu i) := fun i =>
    isProbabilityMeasure_goodSuspensionMeasure (hrate i)
  letI : ∀ i, SigmaFinite (mu i) := fun i => by infer_instance
  simpa [multiclassStationaryPoissonMeasure, multiclassStationaryPoissonFlow, mu] using
    (MeasureTheory.measurePreserving_pi mu mu (fun i =>
      goodSuspensionFlow_measurePreserving_of_raw (hrate i) t
        (suspensionFlow_measurePreserving_suspensionMeasure (hrate i) t)))

/-- The finite-class product is a real-time stationary untagged input law. -/
noncomputable def multiclassStationaryPoissonShiftInvariantLaw
    (rate : Class -> Real) (hrate : ∀ i, 0 < rate i) :
    Palm.ShiftInvariantProbabilityLaw (Class -> GoodSuspensionState) where
  Pbase := multiclassStationaryPoissonMeasure rate
  isProbability := isProbabilityMeasure_multiclassStationaryPoissonMeasure rate hrate
  shift := multiclassStationaryPoissonFlow
  shift_zero := by
    funext omega
    funext i
    change goodSuspensionFlow 0 (omega i) = omega i
    simpa [id] using congrFun goodSuspensionFlow_zero (omega i)
  shift_add := by
    intro s t
    funext omega
    funext i
    change goodSuspensionFlow (s + t) (omega i) =
      goodSuspensionFlow s (goodSuspensionFlow t (omega i))
    simpa [Function.comp_def] using congrFun (goodSuspensionFlow_add s t) (omega i)
  shift_preserving := fun t =>
    multiclassStationaryPoissonFlow_measurePreserving rate hrate t

/-- Joint measurability stated through the packaged raw stationary law. -/
theorem measurable_uncurry_multiclassStationaryPoissonShift
    (rate : Class -> Real) (hrate : ∀ i, 0 < rate i) :
    Measurable (Function.uncurry
      (multiclassStationaryPoissonShiftInvariantLaw (Class := Class) rate hrate).shift) := by
  simpa [multiclassStationaryPoissonShiftInvariantLaw] using
    (measurable_uncurry_multiclassStationaryPoissonFlow (Class := Class))

/-- The complete stationary suspension states of distinct classes are
independent.  Consequently this is independence of full arrival paths, not
merely of a selected collection of count variables. -/
theorem iIndepFun_multiclassStationaryPoissonPaths
    (rate : Class -> Real) (hrate : ∀ i, 0 < rate i) :
    iIndepFun (fun i (omega : Class -> GoodSuspensionState) => omega i)
      (multiclassStationaryPoissonMeasure rate) := by
  let mu : Class -> Measure GoodSuspensionState := fun i =>
    goodSuspensionMeasure (rate i)
  letI : ∀ i, IsProbabilityMeasure (mu i) := fun i =>
    isProbabilityMeasure_goodSuspensionMeasure (hrate i)
  simpa [multiclassStationaryPoissonMeasure, mu] using
    (iIndepFun_pi (X := fun _ : Class => id)
      (fun _ => aemeasurable_id))

/-- Projection to one class is measure-preserving, so every coordinate has
the already constructed one-class stationary Poisson law. -/
theorem measurePreserving_multiclassStationaryPoissonPath
    (rate : Class -> Real) (hrate : ∀ i, 0 < rate i) (i : Class) :
    MeasurePreserving (Function.eval i)
      (multiclassStationaryPoissonMeasure rate)
      (goodSuspensionMeasure (rate i)) := by
  let mu : Class -> Measure GoodSuspensionState := fun j =>
    goodSuspensionMeasure (rate j)
  letI : ∀ j, IsProbabilityMeasure (mu j) := fun j =>
    isProbabilityMeasure_goodSuspensionMeasure (hrate j)
  simpa [multiclassStationaryPoissonMeasure, mu] using
    (measurePreserving_eval mu i)

/-- The untagged arrival epoch with a class label. -/
def multiclassStationaryPoissonArrival (i : Class) :
    (Class -> GoodSuspensionState) -> Int -> Real :=
  fun omega n => suspensionBaseArrival (omega i) n

/-- The finite set of class-`i` arrival indices with epochs in `[a,b)`. -/
def multiclassStationaryPoissonArrivalIndices (i : Class) (a b : Real) :
    (Class -> GoodSuspensionState) -> Finset Int :=
  fun omega => suspensionBaseArrivalIndices a b (omega i)

omit [Fintype Class] in
/-- Each labelled class arrival path is strictly ordered on every state in the
literal good carrier. -/
theorem multiclassStationaryPoissonArrival_strictMono
    (i : Class) (omega : Class -> GoodSuspensionState) :
    StrictMono (multiclassStationaryPoissonArrival i omega) :=
  suspensionBaseArrival_strictMono (omega i)

omit [Fintype Class] in
/-- The finite class ledger has exactly the intended half-open endpoint
semantics. -/
theorem mem_multiclassStationaryPoissonArrivalIndices_iff
    (i : Class) (a b : Real) (omega : Class -> GoodSuspensionState) (n : Int) :
    n ∈ multiclassStationaryPoissonArrivalIndices i a b omega ↔
      a ≤ multiclassStationaryPoissonArrival i omega n ∧
        multiclassStationaryPoissonArrival i omega n < b :=
  mem_suspensionBaseArrivalIndices_iff a b (omega i) n

omit [Fintype Class] in
/-- The labelled arrival epoch is measurable on the joint finite-class
carrier. -/
theorem measurable_multiclassStationaryPoissonArrival
    (i : Class) (n : Int) :
    Measurable (fun omega : Class -> GoodSuspensionState =>
      multiclassStationaryPoissonArrival i omega n) := by
  exact (measurable_suspensionBaseArrival n).comp (measurable_pi_apply i)

omit [Fintype Class] in
/-- Translation of the joint input carrier translates each class's actual
arrival point set.  The reindexing is internal to the class and is not a
cross-class Palm selection. -/
theorem multiclassStationaryPoissonArrival_range_flow
    (i : Class) (omega : Class -> GoodSuspensionState) (t : Real) :
    Set.range (multiclassStationaryPoissonArrival i
      (multiclassStationaryPoissonFlow (Class := Class) t omega)) =
      (fun u : Real => u - t) ''
        Set.range (multiclassStationaryPoissonArrival i omega) := by
  exact suspensionBaseArrival_range_goodSuspensionFlow (omega i) t

/-- One independently sampled stationary marked-Poisson input per class.
Each coordinate contains both its stationary arrival suspension and a complete
two-sided iid unit-exponential work-mark path. -/
noncomputable def multiclassStationaryPoissonWorkMeasure (arrivalRate : Class -> Real) :
    Measure (Class -> (GoodSuspensionState × (Int -> Real))) :=
  Measure.pi fun i => Queueing.stationaryPoissonWorkMeasure (arrivalRate i)

/-- The diagonal real-time action on the marked finite-class input.  Each
class reindexes its work marks by its own crossed-arrival label. -/
def multiclassStationaryPoissonWorkFlow (t : Real) :
    (Class -> (GoodSuspensionState × (Int -> Real))) ->
      Class -> (GoodSuspensionState × (Int -> Real)) :=
  fun omega i => Queueing.timedEmbeddedSuspensionFlow (α := Real) t (omega i)

omit [Fintype Class] in
/-- The marked finite-class stationary input action is jointly measurable in
real time and the full vector of marked class paths.  This is the
measurability needed before a selected class can recenter the other classes at
its random arrival epoch. -/
theorem measurable_uncurry_multiclassStationaryPoissonWorkFlow :
    Measurable (Function.uncurry
      (multiclassStationaryPoissonWorkFlow (Class := Class))) := by
  apply measurable_pi_iff.2
  intro i
  change Measurable (fun q : Real ×
      (Class -> (GoodSuspensionState × (Int -> Real))) =>
    Queueing.timedEmbeddedSuspensionFlow (α := Real) q.1 (q.2 i))
  exact Queueing.measurable_uncurry_timedEmbeddedSuspensionFlow.comp
    (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))

/-- Positive class arrival rates make the finite marked-input product a
probability law. -/
theorem isProbabilityMeasure_multiclassStationaryPoissonWorkMeasure
    (arrivalRate : Class -> Real) (harrivalRate : ∀ i, 0 < arrivalRate i) :
    IsProbabilityMeasure (multiclassStationaryPoissonWorkMeasure arrivalRate) := by
  let mu : Class -> Measure (GoodSuspensionState × (Int -> Real)) := fun i =>
    Queueing.stationaryPoissonWorkMeasure (arrivalRate i)
  letI : ∀ i, IsProbabilityMeasure (mu i) := fun i =>
    Queueing.isProbabilityMeasure_stationaryPoissonWorkMeasure (harrivalRate i)
  simpa [multiclassStationaryPoissonWorkMeasure, mu] using
    (inferInstance : IsProbabilityMeasure (Measure.pi mu))

/-- The diagonal marked action preserves the full finite-class product law.
This is stationarity of input only; it contains no queue state or service
discipline. -/
theorem multiclassStationaryPoissonWorkFlow_measurePreserving
    (arrivalRate : Class -> Real) (harrivalRate : ∀ i, 0 < arrivalRate i)
    (t : Real) :
    MeasurePreserving (multiclassStationaryPoissonWorkFlow (Class := Class) t)
      (multiclassStationaryPoissonWorkMeasure arrivalRate)
      (multiclassStationaryPoissonWorkMeasure arrivalRate) := by
  let mu : Class -> Measure (GoodSuspensionState × (Int -> Real)) := fun i =>
    Queueing.stationaryPoissonWorkMeasure (arrivalRate i)
  letI : ∀ i, IsProbabilityMeasure (mu i) := fun i =>
    Queueing.isProbabilityMeasure_stationaryPoissonWorkMeasure (harrivalRate i)
  letI : ∀ i, SigmaFinite (mu i) := fun i => by infer_instance
  simpa [multiclassStationaryPoissonWorkMeasure,
    multiclassStationaryPoissonWorkFlow, mu,
    Queueing.stationaryPoissonWorkShiftInvariantLaw] using
    (MeasureTheory.measurePreserving_pi mu mu (fun i =>
      (Queueing.stationaryPoissonWorkShiftInvariantLaw
        (harrivalRate i)).shift_preserving t))

/-- A finite collection of independent stationary marked-Poisson inputs
under a common real-time clock. -/
noncomputable def multiclassStationaryPoissonWorkShiftInvariantLaw
    (arrivalRate : Class -> Real) (harrivalRate : ∀ i, 0 < arrivalRate i) :
    Palm.ShiftInvariantProbabilityLaw
      (Class -> (GoodSuspensionState × (Int -> Real))) where
  Pbase := multiclassStationaryPoissonWorkMeasure arrivalRate
  isProbability :=
    isProbabilityMeasure_multiclassStationaryPoissonWorkMeasure arrivalRate harrivalRate
  shift := multiclassStationaryPoissonWorkFlow
  shift_zero := by
    funext omega
    funext i
    change Queueing.timedEmbeddedSuspensionFlow (α := Real) 0 (omega i) = omega i
    exact congrFun Queueing.timedEmbeddedSuspensionFlow_zero (omega i)
  shift_add := by
    intro s t
    funext omega
    funext i
    change Queueing.timedEmbeddedSuspensionFlow (α := Real) (s + t) (omega i) =
      Queueing.timedEmbeddedSuspensionFlow (α := Real) s
        (Queueing.timedEmbeddedSuspensionFlow (α := Real) t (omega i))
    simpa [Function.comp_def] using
      congrFun (Queueing.timedEmbeddedSuspensionFlow_add (α := Real) s t) (omega i)
  shift_preserving := fun t =>
    multiclassStationaryPoissonWorkFlow_measurePreserving arrivalRate harrivalRate t

/-- Joint measurability stated through the packaged finite-class stationary
marked input law. -/
theorem measurable_uncurry_multiclassStationaryPoissonWorkShift
    (arrivalRate : Class -> Real) (harrivalRate : ∀ i, 0 < arrivalRate i) :
    Measurable (Function.uncurry
      (multiclassStationaryPoissonWorkShiftInvariantLaw
        (Class := Class) arrivalRate harrivalRate).shift) := by
  simpa [multiclassStationaryPoissonWorkShiftInvariantLaw] using
    (measurable_uncurry_multiclassStationaryPoissonWorkFlow (Class := Class))

/-- Complete marked input paths, not merely individual marks or counts, are
independent between the finite family of classes. -/
theorem iIndepFun_multiclassStationaryPoissonWorkPaths
    (arrivalRate : Class -> Real) (harrivalRate : ∀ i, 0 < arrivalRate i) :
    iIndepFun
      (fun i (omega : Class -> (GoodSuspensionState × (Int -> Real))) => omega i)
      (multiclassStationaryPoissonWorkMeasure arrivalRate) := by
  let mu : Class -> Measure (GoodSuspensionState × (Int -> Real)) := fun i =>
    Queueing.stationaryPoissonWorkMeasure (arrivalRate i)
  letI : ∀ i, IsProbabilityMeasure (mu i) := fun i =>
    Queueing.isProbabilityMeasure_stationaryPoissonWorkMeasure (harrivalRate i)
  simpa [multiclassStationaryPoissonWorkMeasure, mu] using
    (iIndepFun_pi (X := fun _ : Class => id)
      (fun _ => aemeasurable_id))

/-- Projection to a class's complete marked input path is
measure-preserving.  It exposes the established one-class stationary marked
Poisson construction without inventing a new marginal law. -/
theorem measurePreserving_multiclassStationaryPoissonWorkPath
    (arrivalRate : Class -> Real) (harrivalRate : ∀ i, 0 < arrivalRate i)
    (i : Class) :
    MeasurePreserving (Function.eval i)
      (multiclassStationaryPoissonWorkMeasure arrivalRate)
      (Queueing.stationaryPoissonWorkMeasure (arrivalRate i)) := by
  let mu : Class -> Measure (GoodSuspensionState × (Int -> Real)) := fun j =>
    Queueing.stationaryPoissonWorkMeasure (arrivalRate j)
  letI : ∀ j, IsProbabilityMeasure (mu j) := fun j =>
    Queueing.isProbabilityMeasure_stationaryPoissonWorkMeasure (harrivalRate j)
  simpa [multiclassStationaryPoissonWorkMeasure, mu] using
    (measurePreserving_eval mu i)

/-- The actual epoch of a labelled class arrival in the joint marked carrier. -/
def multiclassStationaryPoissonWorkArrival (i : Class) :
    (Class -> (GoodSuspensionState × (Int -> Real))) -> Int -> Real :=
  fun omega n => Queueing.stationaryPoissonWorkArrival (omega i) n

/-- The iid work requirement carried by a labelled class arrival. -/
def multiclassStationaryPoissonWorkRequirement (i : Class) :
    (Class -> (GoodSuspensionState × (Int -> Real))) -> Int -> Real :=
  fun omega n => Queueing.stationaryPoissonWorkRequirement (omega i) n

/-- Under the marked input flow, a class-labelled arrival is reindexed by
the class's crossed-arrival label and its physical epoch is translated. -/
theorem multiclassStationaryPoissonWorkArrival_flow
    (omega : Class -> (GoodSuspensionState × (Int -> Real)))
    (t : Real) (i : Class) (j : Int) :
    multiclassStationaryPoissonWorkArrival i
        (multiclassStationaryPoissonWorkFlow (Class := Class) t omega) j =
      multiclassStationaryPoissonWorkArrival i omega
        (suspensionCrossingIndexPastClosed t (omega i).1.1 + j) - t := by
  exact Queueing.timedEmbeddedArrival_flow (omega i) t j

/-- Under the marked input flow, the work mark at a reindexed labelled
arrival is the mark carried by the original label. -/
theorem multiclassStationaryPoissonWorkRequirement_flow
    (omega : Class -> (GoodSuspensionState × (Int -> Real)))
    (t : Real) (i : Class) (j : Int) :
    multiclassStationaryPoissonWorkRequirement i
        (multiclassStationaryPoissonWorkFlow (Class := Class) t omega) j =
      multiclassStationaryPoissonWorkRequirement i omega
        (suspensionCrossingIndexPastClosed t (omega i).1.1 + j) := rfl

/-- Each labelled class work requirement has the unit-exponential marginal
law required by the source's normalized-work input model. -/
theorem multiclassStationaryPoissonWorkRequirement_hasLaw
    (arrivalRate : Class -> Real) (harrivalRate : ∀ i, 0 < arrivalRate i)
    (i : Class) (n : Int) :
    HasLaw (fun omega : Class -> (GoodSuspensionState × (Int -> Real)) =>
      multiclassStationaryPoissonWorkRequirement i omega n)
      (expMeasure 1) (multiclassStationaryPoissonWorkMeasure arrivalRate) := by
  let mu : Class -> Measure (GoodSuspensionState × (Int -> Real)) := fun j =>
    Queueing.stationaryPoissonWorkMeasure (arrivalRate j)
  letI : ∀ j, IsProbabilityMeasure (mu j) := fun j =>
    Queueing.isProbabilityMeasure_stationaryPoissonWorkMeasure (harrivalRate j)
  simpa [multiclassStationaryPoissonWorkMeasure,
    multiclassStationaryPoissonWorkRequirement, mu] using
    (Queueing.stationaryPoissonWorkRequirement_hasLaw (harrivalRate i) n).comp
      (measurePreserving_eval mu i).hasLaw

/-- All marked work requirements of all finitely many classes are positive
almost surely. -/
theorem ae_all_multiclassStationaryPoissonWorkRequirement_positive
    (arrivalRate : Class -> Real) (harrivalRate : ∀ i, 0 < arrivalRate i) :
    ∀ᵐ omega ∂multiclassStationaryPoissonWorkMeasure arrivalRate, ∀ i : Class,
      ∀ n : Int, 0 < multiclassStationaryPoissonWorkRequirement i omega n := by
  let mu : Class -> Measure (GoodSuspensionState × (Int -> Real)) := fun i =>
    Queueing.stationaryPoissonWorkMeasure (arrivalRate i)
  letI : ∀ i, IsProbabilityMeasure (mu i) := fun i =>
    Queueing.isProbabilityMeasure_stationaryPoissonWorkMeasure (harrivalRate i)
  rw [ae_all_iff]
  intro i
  refine ae_of_ae_map (μ := Measure.pi mu) (f := Function.eval i)
    (p := fun z : GoodSuspensionState × (Int -> Real) => ∀ n : Int,
      0 < Queueing.stationaryPoissonWorkRequirement z n)
    (measurePreserving_eval mu i).measurable.aemeasurable ?_
  rw [(measurePreserving_eval mu i).map_eq]
  simpa [multiclassStationaryPoissonWorkMeasure,
    multiclassStationaryPoissonWorkRequirement, mu] using
    Queueing.ae_all_stationaryPoissonWorkRequirement_positive (harrivalRate i)

end

end AppliedModelingLib.Probability.PoissonProcess

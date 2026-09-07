import AppliedModelingLib.Foundations.Probability.MulticlassForwardPoisson
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Independent finite-class queueing primitives

This module extends the finite-class forward Poisson carrier with the actual
independent marks named by a queueing input model: one admission Boolean and
one unit-mean exponential work requirement per raw arrival.  The construction
is intentionally only a primitive-input construction.  In particular, it does
not identify the admitted marked subsequence as a Poisson process, choose a
GPS execution, or claim stationarity.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory
open scoped NNReal

noncomputable section

/-- A countable iid Boolean-mark path. -/
def bernoulliMarkPathMeasure (p : ℝ≥0) (hp : p ≤ 1) : Measure (ℕ → Bool) :=
  Measure.infinitePi fun _ : ℕ => (PMF.bernoulli p hp).toMeasure

/-- The Boolean-mark path carrier is a probability space. -/
theorem isProbabilityMeasure_bernoulliMarkPathMeasure
    (p : ℝ≥0) (hp : p ≤ 1) :
    IsProbabilityMeasure (bernoulliMarkPathMeasure p hp) := by
  let μ : ℕ → Measure Bool := fun _ => (PMF.bernoulli p hp).toMeasure
  letI : ∀ n, IsProbabilityMeasure (μ n) := fun _ => inferInstance
  simpa [bernoulliMarkPathMeasure, μ] using
    (inferInstance : IsProbabilityMeasure (Measure.infinitePi μ))

/-- One raw-arrival path together with its independent admission and work-mark
paths.  The nested product layout keeps all projections measurable by the
standard product-space API. -/
abbrev ForwardQueueingPrimitivePath :=
  (ℕ → ℝ) × ((ℕ → Bool) × (ℕ → ℝ))

/-- The raw interarrival coordinate of a class primitive. -/
def ForwardQueueingPrimitivePath.rawInterarrivals :
    ForwardQueueingPrimitivePath → (ℕ → ℝ) :=
  Prod.fst

/-- The independently sampled admission-mark coordinate of a class primitive. -/
def ForwardQueueingPrimitivePath.admissionMarks :
    ForwardQueueingPrimitivePath → (ℕ → Bool) :=
  fun x => x.2.1

/-- The independently sampled unit-exponential work-mark coordinate of a
class primitive. -/
def ForwardQueueingPrimitivePath.workMarks :
    ForwardQueueingPrimitivePath → (ℕ → ℝ) :=
  fun x => x.2.2

/-- The primitive law for one class: raw Poisson interarrivals, iid admission
marks, and iid unit-mean exponential work marks are independent factors. -/
def forwardQueueingPrimitiveMeasure
    (arrivalRate : ℝ) (admissionProbability : ℝ≥0)
    (hadmissionProbability : admissionProbability ≤ 1) :
    Measure ForwardQueueingPrimitivePath :=
  (exponentialInterarrivalMeasure arrivalRate).prod
    ((bernoulliMarkPathMeasure admissionProbability hadmissionProbability).prod
      (exponentialInterarrivalMeasure 1))

/-- The one-class primitive carrier is a probability space under positive raw
arrival rate. -/
theorem isProbabilityMeasure_forwardQueueingPrimitiveMeasure
    {arrivalRate : ℝ} (harrivalRate : 0 < arrivalRate)
    (admissionProbability : ℝ≥0)
    (hadmissionProbability : admissionProbability ≤ 1) :
    IsProbabilityMeasure
      (forwardQueueingPrimitiveMeasure arrivalRate admissionProbability
        hadmissionProbability) := by
  let μa : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure arrivalRate
  let μm : Measure (ℕ → Bool) :=
    bernoulliMarkPathMeasure admissionProbability hadmissionProbability
  let μw : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure 1
  letI : IsProbabilityMeasure μa :=
    isProbabilityMeasure_exponentialInterarrivalMeasure harrivalRate
  letI : IsProbabilityMeasure μm :=
    isProbabilityMeasure_bernoulliMarkPathMeasure admissionProbability
      hadmissionProbability
  letI : IsProbabilityMeasure μw :=
    isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  simpa [forwardQueueingPrimitiveMeasure, μa, μm, μw] using
    (inferInstance : IsProbabilityMeasure (μa.prod (μm.prod μw)))

/-- Projecting the primitive carrier to raw interarrivals preserves their
canonical exponential-interarrival law. -/
theorem measurePreserving_rawInterarrivals_forwardQueueingPrimitive
    {arrivalRate : ℝ} (harrivalRate : 0 < arrivalRate)
    (admissionProbability : ℝ≥0)
    (hadmissionProbability : admissionProbability ≤ 1) :
    MeasurePreserving ForwardQueueingPrimitivePath.rawInterarrivals
      (forwardQueueingPrimitiveMeasure arrivalRate admissionProbability
        hadmissionProbability)
      (exponentialInterarrivalMeasure arrivalRate) := by
  let μa : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure arrivalRate
  let μm : Measure (ℕ → Bool) :=
    bernoulliMarkPathMeasure admissionProbability hadmissionProbability
  let μw : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure 1
  letI : IsProbabilityMeasure μa :=
    isProbabilityMeasure_exponentialInterarrivalMeasure harrivalRate
  letI : IsProbabilityMeasure μm :=
    isProbabilityMeasure_bernoulliMarkPathMeasure admissionProbability
      hadmissionProbability
  letI : IsProbabilityMeasure μw :=
    isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  simpa [ForwardQueueingPrimitivePath.rawInterarrivals,
    forwardQueueingPrimitiveMeasure, μa, μm, μw] using
    (measurePreserving_fst : MeasurePreserving Prod.fst (μa.prod (μm.prod μw)) μa)

/-- Projecting the primitive carrier to admission marks preserves their iid
Bernoulli path law. -/
theorem measurePreserving_admissionMarks_forwardQueueingPrimitive
    {arrivalRate : ℝ} (harrivalRate : 0 < arrivalRate)
    (admissionProbability : ℝ≥0)
    (hadmissionProbability : admissionProbability ≤ 1) :
    MeasurePreserving ForwardQueueingPrimitivePath.admissionMarks
      (forwardQueueingPrimitiveMeasure arrivalRate admissionProbability
        hadmissionProbability)
      (bernoulliMarkPathMeasure admissionProbability hadmissionProbability) := by
  let μa : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure arrivalRate
  let μm : Measure (ℕ → Bool) :=
    bernoulliMarkPathMeasure admissionProbability hadmissionProbability
  let μw : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure 1
  letI : IsProbabilityMeasure μa :=
    isProbabilityMeasure_exponentialInterarrivalMeasure harrivalRate
  letI : IsProbabilityMeasure μm :=
    isProbabilityMeasure_bernoulliMarkPathMeasure admissionProbability
      hadmissionProbability
  letI : IsProbabilityMeasure μw :=
    isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  simpa [ForwardQueueingPrimitivePath.admissionMarks,
    forwardQueueingPrimitiveMeasure, μa, μm, μw] using
    ((measurePreserving_fst : MeasurePreserving Prod.fst (μm.prod μw) μm).comp
      (measurePreserving_snd : MeasurePreserving Prod.snd (μa.prod (μm.prod μw))
        (μm.prod μw)))

/-- Projecting the primitive carrier to work marks preserves their iid
unit-mean exponential path law. -/
theorem measurePreserving_workMarks_forwardQueueingPrimitive
    {arrivalRate : ℝ} (harrivalRate : 0 < arrivalRate)
    (admissionProbability : ℝ≥0)
    (hadmissionProbability : admissionProbability ≤ 1) :
    MeasurePreserving ForwardQueueingPrimitivePath.workMarks
      (forwardQueueingPrimitiveMeasure arrivalRate admissionProbability
        hadmissionProbability)
      (exponentialInterarrivalMeasure 1) := by
  let μa : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure arrivalRate
  let μm : Measure (ℕ → Bool) :=
    bernoulliMarkPathMeasure admissionProbability hadmissionProbability
  let μw : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure 1
  letI : IsProbabilityMeasure μa :=
    isProbabilityMeasure_exponentialInterarrivalMeasure harrivalRate
  letI : IsProbabilityMeasure μm :=
    isProbabilityMeasure_bernoulliMarkPathMeasure admissionProbability
      hadmissionProbability
  letI : IsProbabilityMeasure μw :=
    isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  simpa [ForwardQueueingPrimitivePath.workMarks,
    forwardQueueingPrimitiveMeasure, μa, μm, μw] using
    ((measurePreserving_snd : MeasurePreserving Prod.snd (μm.prod μw) μw).comp
      (measurePreserving_snd : MeasurePreserving Prod.snd (μa.prod (μm.prod μw))
        (μm.prod μw)))

/-- The raw arrival path and the work-mark path are independent factors of a
single-class primitive carrier.  This is path-level independence, not merely
independence of selected arrival or work coordinates. -/
theorem indepFun_rawInterarrivals_workMarks_forwardQueueingPrimitive
    {arrivalRate : ℝ} (harrivalRate : 0 < arrivalRate)
    (admissionProbability : ℝ≥0)
    (hadmissionProbability : admissionProbability ≤ 1) :
    ProbabilityTheory.IndepFun ForwardQueueingPrimitivePath.rawInterarrivals
      ForwardQueueingPrimitivePath.workMarks
      (forwardQueueingPrimitiveMeasure arrivalRate admissionProbability
        hadmissionProbability) := by
  let μa : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure arrivalRate
  let μm : Measure (ℕ → Bool) :=
    bernoulliMarkPathMeasure admissionProbability hadmissionProbability
  let μw : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure 1
  letI : IsProbabilityMeasure μa :=
    isProbabilityMeasure_exponentialInterarrivalMeasure harrivalRate
  letI : IsProbabilityMeasure μm :=
    isProbabilityMeasure_bernoulliMarkPathMeasure admissionProbability
      hadmissionProbability
  letI : IsProbabilityMeasure μw :=
    isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  simpa [ForwardQueueingPrimitivePath.rawInterarrivals,
    ForwardQueueingPrimitivePath.workMarks, forwardQueueingPrimitiveMeasure,
    μa, μm, μw] using
    (ProbabilityTheory.indepFun_prod
      (μ := μa) (ν := μm.prod μw) (X := id) (Y := Prod.snd)
      measurable_id measurable_snd)

/-- All unit-exponential work marks are strictly positive almost surely.  The
event-driven queue construction may therefore be restricted to a genuine
source-law full-measure carrier instead of assuming positive job work. -/
theorem ae_all_workMarks_positive_forwardQueueingPrimitive
    {arrivalRate : ℝ} (harrivalRate : 0 < arrivalRate)
    (admissionProbability : ℝ≥0)
    (hadmissionProbability : admissionProbability ≤ 1) :
    ∀ᵐ ω ∂forwardQueueingPrimitiveMeasure arrivalRate admissionProbability
      hadmissionProbability, ∀ n : ℕ,
      0 < interarrival n (ForwardQueueingPrimitivePath.workMarks ω) := by
  let μ := forwardQueueingPrimitiveMeasure arrivalRate admissionProbability
    hadmissionProbability
  letI : IsProbabilityMeasure μ :=
    isProbabilityMeasure_forwardQueueingPrimitiveMeasure harrivalRate
      admissionProbability hadmissionProbability
  have hwork : MeasurePreserving ForwardQueueingPrimitivePath.workMarks μ
      (exponentialInterarrivalMeasure 1) := by
    simpa [μ] using
      measurePreserving_workMarks_forwardQueueingPrimitive harrivalRate
        admissionProbability hadmissionProbability
  refine ae_of_ae_map (μ := μ) (f := ForwardQueueingPrimitivePath.workMarks)
    (p := fun ξ : ℕ → ℝ => ∀ n : ℕ, 0 < interarrival n ξ)
    hwork.measurable.aemeasurable ?_
  rw [hwork.map_eq]
  exact ae_all_interarrival_positive (by norm_num)

variable {Class : Type*} [Fintype Class]

/-- Joint primitive law for a finite-class queueing system.  Its product
coordinates are complete per-class arrival/mark/work paths. -/
def multiclassForwardQueueingPrimitiveMeasure
    (arrivalRate : Class → ℝ) (admissionProbability : Class → ℝ≥0)
    (hadmissionProbability : ∀ i, admissionProbability i ≤ 1) :
    Measure (Class → ForwardQueueingPrimitivePath) :=
  Measure.pi fun i =>
    forwardQueueingPrimitiveMeasure (arrivalRate i) (admissionProbability i)
      (hadmissionProbability i)

/-- The finite-class primitive carrier is a probability space when each raw
class rate is positive. -/
theorem isProbabilityMeasure_multiclassForwardQueueingPrimitiveMeasure
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ i, 0 < arrivalRate i)
    (admissionProbability : Class → ℝ≥0)
    (hadmissionProbability : ∀ i, admissionProbability i ≤ 1) :
    IsProbabilityMeasure
      (multiclassForwardQueueingPrimitiveMeasure arrivalRate admissionProbability
        hadmissionProbability) := by
  let μ : Class → Measure ForwardQueueingPrimitivePath := fun i =>
    forwardQueueingPrimitiveMeasure (arrivalRate i) (admissionProbability i)
      (hadmissionProbability i)
  letI : ∀ i, IsProbabilityMeasure (μ i) := fun i =>
    isProbabilityMeasure_forwardQueueingPrimitiveMeasure (harrivalRate i)
      (admissionProbability i) (hadmissionProbability i)
  simpa [multiclassForwardQueueingPrimitiveMeasure, μ] using
    (inferInstance : IsProbabilityMeasure (Measure.pi μ))

/-- The complete primitive paths of distinct classes are independent. -/
theorem iIndepFun_multiclassForwardQueueingPrimitivePaths
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ i, 0 < arrivalRate i)
    (admissionProbability : Class → ℝ≥0)
    (hadmissionProbability : ∀ i, admissionProbability i ≤ 1) :
    ProbabilityTheory.iIndepFun
      (fun i (ω : Class → ForwardQueueingPrimitivePath) => ω i)
      (multiclassForwardQueueingPrimitiveMeasure arrivalRate admissionProbability
        hadmissionProbability) := by
  let μ : Class → Measure ForwardQueueingPrimitivePath := fun i =>
    forwardQueueingPrimitiveMeasure (arrivalRate i) (admissionProbability i)
      (hadmissionProbability i)
  letI : ∀ i, IsProbabilityMeasure (μ i) := fun i =>
    isProbabilityMeasure_forwardQueueingPrimitiveMeasure (harrivalRate i)
      (admissionProbability i) (hadmissionProbability i)
  simpa [multiclassForwardQueueingPrimitiveMeasure, μ] using
    (ProbabilityTheory.iIndepFun_pi (X := fun _ : Class => id)
      (fun _ => aemeasurable_id))

/-- Raw interarrivals of one class, read from the full finite-class primitive
carrier. -/
def multiclassForwardQueueingPrimitiveRawInterarrivals
    (i : Class) :
    (Class → ForwardQueueingPrimitivePath) → (ℕ → ℝ) :=
  fun ω => ForwardQueueingPrimitivePath.rawInterarrivals (ω i)

/-- The full primitive carrier projects measure-preservingly to the raw
interarrival path of each class. -/
theorem measurePreserving_multiclassPrimitiveRawInterarrivals
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ i, 0 < arrivalRate i)
    (admissionProbability : Class → ℝ≥0)
    (hadmissionProbability : ∀ i, admissionProbability i ≤ 1) (i : Class) :
    MeasurePreserving (multiclassForwardQueueingPrimitiveRawInterarrivals i)
      (multiclassForwardQueueingPrimitiveMeasure arrivalRate admissionProbability
        hadmissionProbability)
      (exponentialInterarrivalMeasure (arrivalRate i)) := by
  let μ : Class → Measure ForwardQueueingPrimitivePath := fun j =>
    forwardQueueingPrimitiveMeasure (arrivalRate j) (admissionProbability j)
      (hadmissionProbability j)
  letI : ∀ j, IsProbabilityMeasure (μ j) := fun j =>
    isProbabilityMeasure_forwardQueueingPrimitiveMeasure (harrivalRate j)
      (admissionProbability j) (hadmissionProbability j)
  have hraw : MeasurePreserving ForwardQueueingPrimitivePath.rawInterarrivals
      (μ i) (exponentialInterarrivalMeasure (arrivalRate i)) := by
    simpa [μ] using
      measurePreserving_rawInterarrivals_forwardQueueingPrimitive
        (harrivalRate i) (admissionProbability i) (hadmissionProbability i)
  simpa [multiclassForwardQueueingPrimitiveRawInterarrivals,
    multiclassForwardQueueingPrimitiveMeasure, μ] using
    hraw.comp (measurePreserving_eval μ i)

/-- The finite set of raw-arrival indices of one class by a finite horizon,
read directly from the complete queueing primitive carrier. -/
noncomputable def multiclassForwardQueueingPrimitiveArrivalIndices
    (i : Class) (t : ℝ) (ω : Class → ForwardQueueingPrimitivePath) : Finset ℕ :=
  Finset.range (canonicalRenewalCount t
    (multiclassForwardQueueingPrimitiveRawInterarrivals i ω))

/-- The primitive carrier has a simultaneous exact arrival ledger for every
class, horizon, and index.  This is the bridge from the stochastic input to a
future event-driven queue execution: it concerns the actual raw arrival
coordinate living alongside admission and work marks. -/
theorem ae_mem_multiclassPrimitiveArrivalIndices_iff
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ i, 0 < arrivalRate i)
    (admissionProbability : Class → ℝ≥0)
    (hadmissionProbability : ∀ i, admissionProbability i ≤ 1) :
    ∀ᵐ ω ∂multiclassForwardQueueingPrimitiveMeasure arrivalRate admissionProbability
      hadmissionProbability, ∀ i : Class, ∀ t : ℝ, ∀ n : ℕ,
      n ∈ multiclassForwardQueueingPrimitiveArrivalIndices i t ω ↔
        arrivalTime n (multiclassForwardQueueingPrimitiveRawInterarrivals i ω) ≤ t := by
  rw [ae_all_iff]
  intro i
  have hraw := measurePreserving_multiclassPrimitiveRawInterarrivals
    arrivalRate harrivalRate admissionProbability hadmissionProbability i
  have hcoordinate : ∀ᵐ ω ∂multiclassForwardQueueingPrimitiveMeasure
      arrivalRate admissionProbability hadmissionProbability, ∀ t : ℝ, ∀ n : ℕ,
      n < canonicalRenewalCount t
        (multiclassForwardQueueingPrimitiveRawInterarrivals i ω) ↔
        arrivalTime n (multiclassForwardQueueingPrimitiveRawInterarrivals i ω) ≤ t := by
    refine ae_of_ae_map
      (μ := multiclassForwardQueueingPrimitiveMeasure arrivalRate admissionProbability
        hadmissionProbability)
      (f := multiclassForwardQueueingPrimitiveRawInterarrivals i)
      (p := fun ξ : ℕ → ℝ => ∀ t : ℝ, ∀ n : ℕ,
        n < canonicalRenewalCount t ξ ↔ arrivalTime n ξ ≤ t)
      hraw.measurable.aemeasurable ?_
    rw [hraw.map_eq]
    exact ae_lt_canonicalRenewalCount_iff_arrivalTime_le (harrivalRate i)
  simpa [multiclassForwardQueueingPrimitiveArrivalIndices, Finset.mem_range] using
    hcoordinate

/-- Every raw arrival path in the joint primitive carrier is nonexplosive and
strictly ordered almost surely.  The arrival and work coordinates here are
not assembled after the fact: both are factors of the same carrier. -/
theorem ae_multiclassPrimitiveRawArrivalPaths_nonexplosive_strict
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ i, 0 < arrivalRate i)
    (admissionProbability : Class → ℝ≥0)
    (hadmissionProbability : ∀ i, admissionProbability i ≤ 1) :
    ∀ᵐ ω ∂multiclassForwardQueueingPrimitiveMeasure arrivalRate admissionProbability
      hadmissionProbability, ∀ i : Class,
      Filter.Tendsto
          (fun n : ℕ => arrivalTime n
            (multiclassForwardQueueingPrimitiveRawInterarrivals i ω))
          Filter.atTop Filter.atTop ∧
        StrictMono (fun n : ℕ => arrivalTime n
          (multiclassForwardQueueingPrimitiveRawInterarrivals i ω)) := by
  rw [ae_all_iff]
  intro i
  have hraw := measurePreserving_multiclassPrimitiveRawInterarrivals
    arrivalRate harrivalRate admissionProbability hadmissionProbability i
  refine ae_of_ae_map
    (μ := multiclassForwardQueueingPrimitiveMeasure arrivalRate admissionProbability
      hadmissionProbability)
    (f := multiclassForwardQueueingPrimitiveRawInterarrivals i)
    (p := fun ξ : ℕ → ℝ =>
      Filter.Tendsto (fun n : ℕ => arrivalTime n ξ) Filter.atTop Filter.atTop ∧
        StrictMono (fun n : ℕ => arrivalTime n ξ))
    hraw.measurable.aemeasurable ?_
  rw [hraw.map_eq]
  exact (ae_arrivalTime_tendsto_atTop (harrivalRate i)).and
    (ae_arrivalTime_strictMono (harrivalRate i))

/-- On the nonexplosive primitive carrier, every class has a strictly later
next arrival after every finite time.  Cross-class ties are intentionally not
excluded; a sound GPS scheduler can batch them. -/
theorem ae_multiclassPrimitiveRaw_nextArrival_gt
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ i, 0 < arrivalRate i)
    (admissionProbability : Class → ℝ≥0)
    (hadmissionProbability : ∀ i, admissionProbability i ≤ 1) :
    ∀ᵐ ω ∂multiclassForwardQueueingPrimitiveMeasure arrivalRate admissionProbability
      hadmissionProbability, ∀ i : Class, ∀ t : ℝ,
      t < arrivalTime
        (canonicalRenewalCount t
          (multiclassForwardQueueingPrimitiveRawInterarrivals i ω))
        (multiclassForwardQueueingPrimitiveRawInterarrivals i ω) := by
  filter_upwards [
    ae_multiclassPrimitiveRawArrivalPaths_nonexplosive_strict arrivalRate
      harrivalRate admissionProbability hadmissionProbability] with ω hgood
  intro i t
  exact lt_arrivalTime_canonicalRenewalCount t
    (multiclassForwardQueueingPrimitiveRawInterarrivals i ω)
    (exists_arrivalTime_gt_of_tendsto_atTop
      (multiclassForwardQueueingPrimitiveRawInterarrivals i ω) (hgood i).1 t)

omit [Fintype Class] in
/-- The primitive local arrival ledger has the concrete renewal count as its
cardinality. -/
theorem multiclassForwardQueueingPrimitiveArrivalIndices_card
    (i : Class) (t : ℝ) (ω : Class → ForwardQueueingPrimitivePath) :
    (multiclassForwardQueueingPrimitiveArrivalIndices i t ω).card =
      canonicalRenewalCount t
        (multiclassForwardQueueingPrimitiveRawInterarrivals i ω) := by
  simp [multiclassForwardQueueingPrimitiveArrivalIndices]

/-- Work-mark path of one class, read from the full finite-class primitive
carrier. -/
def multiclassForwardQueueingPrimitiveWorkMarks
    (i : Class) :
    (Class → ForwardQueueingPrimitivePath) → (ℕ → ℝ) :=
  fun ω => ForwardQueueingPrimitivePath.workMarks (ω i)

/-- The full primitive carrier projects measure-preservingly to the iid
unit-exponential work-mark path of each class. -/
theorem measurePreserving_multiclassPrimitiveWorkMarks
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ i, 0 < arrivalRate i)
    (admissionProbability : Class → ℝ≥0)
    (hadmissionProbability : ∀ i, admissionProbability i ≤ 1) (i : Class) :
    MeasurePreserving (multiclassForwardQueueingPrimitiveWorkMarks i)
      (multiclassForwardQueueingPrimitiveMeasure arrivalRate admissionProbability
        hadmissionProbability)
      (exponentialInterarrivalMeasure 1) := by
  let μ : Class → Measure ForwardQueueingPrimitivePath := fun j =>
    forwardQueueingPrimitiveMeasure (arrivalRate j) (admissionProbability j)
      (hadmissionProbability j)
  letI : ∀ j, IsProbabilityMeasure (μ j) := fun j =>
    isProbabilityMeasure_forwardQueueingPrimitiveMeasure (harrivalRate j)
      (admissionProbability j) (hadmissionProbability j)
  have hwork : MeasurePreserving ForwardQueueingPrimitivePath.workMarks
      (μ i) (exponentialInterarrivalMeasure 1) := by
    simpa [μ] using
      measurePreserving_workMarks_forwardQueueingPrimitive
        (harrivalRate i) (admissionProbability i) (hadmissionProbability i)
  simpa [multiclassForwardQueueingPrimitiveWorkMarks,
    multiclassForwardQueueingPrimitiveMeasure, μ] using
    hwork.comp (measurePreserving_eval μ i)

/-- On the joint finite-class carrier, every work requirement is strictly
positive almost surely, simultaneously across all classes and job indices. -/
theorem ae_all_multiclassPrimitiveWorkMarks_positive
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ i, 0 < arrivalRate i)
    (admissionProbability : Class → ℝ≥0)
    (hadmissionProbability : ∀ i, admissionProbability i ≤ 1) :
    ∀ᵐ ω ∂multiclassForwardQueueingPrimitiveMeasure arrivalRate admissionProbability
      hadmissionProbability, ∀ i : Class, ∀ n : ℕ,
      0 < interarrival n (multiclassForwardQueueingPrimitiveWorkMarks i ω) := by
  let μ : Class → Measure ForwardQueueingPrimitivePath := fun i =>
    forwardQueueingPrimitiveMeasure (arrivalRate i) (admissionProbability i)
      (hadmissionProbability i)
  letI : ∀ i, IsProbabilityMeasure (μ i) := fun i =>
    isProbabilityMeasure_forwardQueueingPrimitiveMeasure (harrivalRate i)
      (admissionProbability i) (hadmissionProbability i)
  rw [ae_all_iff]
  intro i
  have hwork : MeasurePreserving (multiclassForwardQueueingPrimitiveWorkMarks i)
      (Measure.pi μ) (exponentialInterarrivalMeasure 1) := by
    simpa [multiclassForwardQueueingPrimitiveWorkMarks,
      multiclassForwardQueueingPrimitiveMeasure, μ] using
      measurePreserving_multiclassPrimitiveWorkMarks arrivalRate harrivalRate
        admissionProbability hadmissionProbability i
  refine ae_of_ae_map (μ := Measure.pi μ)
    (f := multiclassForwardQueueingPrimitiveWorkMarks i)
    (p := fun ξ : ℕ → ℝ => ∀ n : ℕ, 0 < interarrival n ξ)
    hwork.measurable.aemeasurable ?_
  rw [hwork.map_eq]
  exact ae_all_interarrival_positive (by norm_num)

/-- The actual raw Poisson counting process of one class, transported from its
canonical interarrival factor to the joint finite-class primitive carrier. -/
def multiclassForwardQueueingPrimitiveRawPoissonCountingProcess
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ i, 0 < arrivalRate i)
    (admissionProbability : Class → ℝ≥0)
    (hadmissionProbability : ∀ i, admissionProbability i ≤ 1) (i : Class) :
    ForwardHomogeneousPoissonCountingProcessByLaw
      (Class → ForwardQueueingPrimitivePath)
      (multiclassForwardQueueingPrimitiveMeasure arrivalRate admissionProbability
        hadmissionProbability) := by
  simpa using
    (canonicalForwardHomogeneousPoissonCountingProcessByLaw (harrivalRate i)).compMeasurePreserving
      (multiclassForwardQueueingPrimitiveRawInterarrivals i)
      (measurePreserving_multiclassPrimitiveRawInterarrivals arrivalRate harrivalRate
        admissionProbability hadmissionProbability i)

end

end AppliedModelingLib.Probability.PoissonProcess

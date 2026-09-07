import AppliedModelingLib.Foundations.Probability.MulticlassQueueingPrimitives
import AppliedModelingLib.Queueing.GPS.AENormalizedAllocation

/-!
# Finite-horizon multiclass GPS arrival-work semantics

This module is the input and state-balance layer for a real finite-horizon
multiclass GPS execution.  It deliberately does not accept an arbitrary
backlog predicate as the queue model and does not claim to construct a
stationary/Palm queue.

The primitive input is a finite family of raw Poisson arrival paths, iid
admission marks, and iid exponential work marks.  Admitted work is summed
over the actual raw-arrival indices in a time interval.  Any later GPS event
scheduler must satisfy `finiteHorizonGPSStateBalance`, whose equation includes
that arrival-work increment explicitly.
-/

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory
open scoped BigOperators
open scoped NNReal
open PoissonProcess

noncomputable section

variable {Class : Type*} [Fintype Class]

/-- Raw-arrival indices of one class in the half-open time interval `(s, t]`.
The interval is represented by renewal-count indices so it is finite on every
path, even before invoking an almost-sure nonexplosion theorem. -/
def primitiveRawArrivalIndicesBetween
    (i : Class) (s t : ℝ)
    (omega : Class → ForwardQueueingPrimitivePath) : Finset ℕ :=
  Finset.Ico
    (canonicalRenewalCount s
      (multiclassForwardQueueingPrimitiveRawInterarrivals i omega))
    (canonicalRenewalCount t
      (multiclassForwardQueueingPrimitiveRawInterarrivals i omega))

/-- Work contributed by one raw arrival after independent admission thinning.
Dropped requests contribute zero work to the SLA queues. -/
def primitiveAdmittedWorkAtRawIndex
    (i : Class) (omega : Class → ForwardQueueingPrimitivePath) (n : ℕ) : ℝ :=
  if ForwardQueueingPrimitivePath.admissionMarks (omega i) n = true then
    ForwardQueueingPrimitivePath.workMarks (omega i) n
  else 0

/-- Total admitted work of one class arriving in `(s, t]`.  This uses both
the actual arrival path and the sampled admission/work marks; it is not a
synthetic postulated workload increment. -/
def primitiveAdmittedArrivalWorkIncrement
    (i : Class) (s t : ℝ)
    (omega : Class → ForwardQueueingPrimitivePath) : ℝ :=
  ∑ n ∈ primitiveRawArrivalIndicesBetween i s t omega,
    primitiveAdmittedWorkAtRawIndex i omega n

/-- On a path for which the renewal count has its concrete arrival-epoch
meaning, the finite raw ledger for `(s,t]` enumerates exactly those epochs. -/
theorem mem_primitiveRawArrivalIndicesBetween_iff
    {i : Class} {s t : ℝ} {omega : Class → ForwardQueueingPrimitivePath}
    (hledger : ∀ u : ℝ, ∀ n : ℕ,
      n < canonicalRenewalCount u
        (multiclassForwardQueueingPrimitiveRawInterarrivals i omega) ↔
        arrivalTime n
          (multiclassForwardQueueingPrimitiveRawInterarrivals i omega) ≤ u)
    (n : ℕ) :
    n ∈ primitiveRawArrivalIndicesBetween i s t omega ↔
      s < arrivalTime n
        (multiclassForwardQueueingPrimitiveRawInterarrivals i omega) ∧
        arrivalTime n
          (multiclassForwardQueueingPrimitiveRawInterarrivals i omega) ≤ t := by
  simp only [primitiveRawArrivalIndicesBetween, Finset.mem_Ico]
  constructor
  · rintro ⟨hs, ht⟩
    constructor
    · apply lt_of_not_ge
      intro htime
      exact (not_lt_of_ge hs) ((hledger s n).mpr htime)
    · exact (hledger t n).mp ht
  · rintro ⟨hs, ht⟩
    constructor
    · by_contra hnot
      have hcount : n < canonicalRenewalCount s
          (multiclassForwardQueueingPrimitiveRawInterarrivals i omega) :=
        Nat.lt_of_not_ge hnot
      exact (not_le_of_gt hs) ((hledger s n).mp hcount)
    · exact (hledger t n).mpr ht

/-- Nonnegative work marks make every admitted raw-arrival contribution
nonnegative. -/
theorem primitiveAdmittedWorkAtRawIndex_nonneg
    {i : Class} {omega : Class → ForwardQueueingPrimitivePath} {n : ℕ}
    (hwork : 0 ≤ ForwardQueueingPrimitivePath.workMarks (omega i) n) :
    0 ≤ primitiveAdmittedWorkAtRawIndex i omega n := by
  unfold primitiveAdmittedWorkAtRawIndex
  split_ifs <;> simp [hwork]

/-- The actual admitted work increment is nonnegative when its sampled work
marks are nonnegative. -/
theorem primitiveAdmittedArrivalWorkIncrement_nonneg
    (i : Class) (s t : ℝ) (omega : Class → ForwardQueueingPrimitivePath)
    (hwork : ∀ n : ℕ, 0 ≤ ForwardQueueingPrimitivePath.workMarks (omega i) n) :
    0 ≤ primitiveAdmittedArrivalWorkIncrement i s t omega := by
  unfold primitiveAdmittedArrivalWorkIncrement
  exact Finset.sum_nonneg fun n _ =>
    primitiveAdmittedWorkAtRawIndex_nonneg (hwork n)

/-- On the concrete primitive carrier, every finite admitted-work increment is
nonnegative.  This is derived from the joint positive-work carrier fact rather
than assumed of an abstract arrival process. -/
theorem ae_primitiveAdmittedArrivalWorkIncrement_nonneg
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ i, 0 < arrivalRate i)
    (admissionProbability : Class → ℝ≥0)
    (hadmissionProbability : ∀ i, admissionProbability i ≤ 1)
    (s t : ℝ) :
    ∀ᵐ omega ∂multiclassForwardQueueingPrimitiveMeasure arrivalRate
      admissionProbability hadmissionProbability,
      ∀ i : Class, 0 ≤ primitiveAdmittedArrivalWorkIncrement i s t omega := by
  filter_upwards [ae_all_multiclassPrimitiveWorkMarks_positive arrivalRate
    harrivalRate admissionProbability hadmissionProbability] with omega hpositive
  intro i
  apply primitiveAdmittedArrivalWorkIncrement_nonneg
  intro n
  exact le_of_lt (by
    simpa [multiclassForwardQueueingPrimitiveWorkMarks, interarrival] using
      hpositive i n)

/-- Consecutive raw-count intervals partition their admitted work exactly.
This is the finite-sum form of additivity of cumulative admitted work. -/
theorem primitiveAdmittedArrivalWorkIncrement_add
    (i : Class) (s u t : ℝ) (omega : Class → ForwardQueueingPrimitivePath)
    (hsu : canonicalRenewalCount s
        (multiclassForwardQueueingPrimitiveRawInterarrivals i omega) ≤
      canonicalRenewalCount u
        (multiclassForwardQueueingPrimitiveRawInterarrivals i omega))
    (hut : canonicalRenewalCount u
        (multiclassForwardQueueingPrimitiveRawInterarrivals i omega) ≤
      canonicalRenewalCount t
        (multiclassForwardQueueingPrimitiveRawInterarrivals i omega)) :
    primitiveAdmittedArrivalWorkIncrement i s u omega +
      primitiveAdmittedArrivalWorkIncrement i u t omega =
        primitiveAdmittedArrivalWorkIncrement i s t omega := by
  simpa [primitiveAdmittedArrivalWorkIncrement,
    primitiveRawArrivalIndicesBetween] using
    (Finset.sum_Ico_consecutive
      (fun n => primitiveAdmittedWorkAtRawIndex i omega n) hsu hut)

/-- Almost surely, admitted work increments are additive over every fixed
ordered triple of times on the concrete primitive carrier. -/
theorem ae_primitiveAdmittedArrivalWorkIncrement_add
    (arrivalRate : Class → ℝ) (harrivalRate : ∀ i, 0 < arrivalRate i)
    (admissionProbability : Class → ℝ≥0)
    (hadmissionProbability : ∀ i, admissionProbability i ≤ 1)
    (s u t : ℝ) (hsu : s ≤ u) (hut : u ≤ t) :
    ∀ᵐ omega ∂multiclassForwardQueueingPrimitiveMeasure arrivalRate
      admissionProbability hadmissionProbability,
      ∀ i : Class,
        primitiveAdmittedArrivalWorkIncrement i s u omega +
          primitiveAdmittedArrivalWorkIncrement i u t omega =
            primitiveAdmittedArrivalWorkIncrement i s t omega := by
  filter_upwards [ae_multiclassPrimitiveRawArrivalPaths_nonexplosive_strict
    arrivalRate harrivalRate admissionProbability hadmissionProbability] with omega hpaths
  intro i
  exact primitiveAdmittedArrivalWorkIncrement_add i s u t omega
    (canonicalRenewalCount_monotone_of_tendsto
      (multiclassForwardQueueingPrimitiveRawInterarrivals i omega) (hpaths i).1 hsu)
    (canonicalRenewalCount_monotone_of_tendsto
      (multiclassForwardQueueingPrimitiveRawInterarrivals i omega) (hpaths i).1 hut)

/-- The semantic workload balance required of a finite-horizon GPS execution.
`service` is cumulative class service.  Crucially, the balance contains the
actual admitted arrival-work increment, so it cannot describe a drain-only
post-start state.  This predicate is an export target for an event scheduler;
it does not assert that such a scheduler has already been constructed. -/
def finiteHorizonGPSStateBalance
    (start horizon : ℝ) (initialWork : Class → ℝ)
    (workload service : ℝ → Class → ℝ)
    (omega : Class → ForwardQueueingPrimitivePath) : Prop :=
  ∀ i t, t ∈ Set.Icc start horizon →
    workload t i = initialWork i +
      primitiveAdmittedArrivalWorkIncrement i start t omega -
        (service t i - service start i)

/-- A balanced finite-horizon execution has the correct incremental state
equation whenever its actual admitted-work increments are additive. -/
theorem finiteHorizonGPSStateBalance_increment
    {start horizon : ℝ} {initialWork : Class → ℝ}
    {workload service : ℝ → Class → ℝ}
    {omega : Class → ForwardQueueingPrimitivePath}
    (hbalance : finiteHorizonGPSStateBalance start horizon initialWork
      workload service omega)
    {i : Class} {u t : ℝ} (hu : u ∈ Set.Icc start horizon)
    (ht : t ∈ Set.Icc start horizon) (hut : u ≤ t)
    (hwork_add :
      primitiveAdmittedArrivalWorkIncrement i start u omega +
        primitiveAdmittedArrivalWorkIncrement i u t omega =
          primitiveAdmittedArrivalWorkIncrement i start t omega) :
    workload t i = workload u i +
      primitiveAdmittedArrivalWorkIncrement i u t omega -
        (service t i - service u i) := by
  rw [hbalance i t ht, hbalance i u hu, ← hwork_add]
  ring

end

end AppliedModelingLib.Probability.Queueing

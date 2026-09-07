import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-!
# Deterministic FCFS queue comparison

This module records the recurrence-transfer part of a queueing comparison.  If
an application establishes the displayed service-floor recurrence, its
departures are no later than the FCFS work-conserving comparator at that rate
on the same arrivals and work requirements.

The result is deliberately deterministic: Poisson, stationarity, Palm, and
M/M/1 tail laws are not asserted here.  A later application must supply and
verify those properties for its comparator.
-/

namespace AppliedModelingLib
namespace Probability
namespace Queueing

noncomputable section

/-- Departure times of the FCFS single-server comparator with constant rate. -/
def fcfsDeparture
    (arrival work : ℕ → ℝ) (rate : ℝ) : ℕ → ℝ
  | 0 => arrival 0 + work 0 / rate
  | n + 1 =>
      max (arrival (n + 1)) (fcfsDeparture arrival work rate n) +
        work (n + 1) / rate

/-- Tagged-job response time from arrival and departure timestamps. -/
def responseTime (arrival departure : ℕ → ℝ) (n : ℕ) : ℝ :=
  departure n - arrival n

/--
FCFS comparator departure times from a possibly nonempty initial workload.
`initialBusyUntil` is the time at which all work that precedes job zero in the
comparator has cleared.  In a stationary/Palm application, it must be coupled
to the same sample path as the tagged arrival's pre-arrival workload.
-/
def fcfsDepartureFrom
    (initialBusyUntil : ℝ) (arrival work : ℕ → ℝ) (rate : ℝ) : ℕ → ℝ
  | 0 => max (arrival 0) initialBusyUntil + work 0 / rate
  | n + 1 =>
      max (arrival (n + 1)) (fcfsDepartureFrom initialBusyUntil arrival work rate n) +
        work (n + 1) / rate

/-- A higher positive service rate gives a weakly smaller processing time. -/
theorem processingTime_le_of_rate_floor
    {work actualRate floorRate : ℝ}
    (hwork : 0 ≤ work) (hfloor : 0 < floorRate)
    (hactual : floorRate ≤ actualRate) :
    work / actualRate ≤ work / floorRate :=
  div_le_div_of_nonneg_left hwork hfloor hactual

/--
A departure sequence is dominated by the FCFS constant-rate comparator when
its first departure and each successive departure satisfy the comparator
recurrence as upper bounds.

For GPS, deriving this recurrence from fluid service dynamics is a separate
deterministic proof obligation; this structure makes no stochastic claim.
-/
structure FCFSServiceFloorUpperBound
    (arrival work departure : ℕ → ℝ) (rate : ℝ) : Prop where
  zero : departure 0 ≤ arrival 0 + work 0 / rate
  succ : ∀ n : ℕ,
    departure (n + 1) ≤
      max (arrival (n + 1)) (departure n) + work (n + 1) / rate

/--
FCFS service-floor recurrence with an explicit initial workload.  Unlike the
empty-start variant, this can encode the stationary workload seen by a
Palm-tagged arrival once the application supplies the required coupling.
-/
structure FCFSServiceFloorUpperBoundFromInitial
    (initialBusyUntil : ℝ) (arrival work departure : ℕ → ℝ) (rate : ℝ) : Prop where
  zero : departure 0 ≤ max (arrival 0) initialBusyUntil + work 0 / rate
  succ : ∀ n : ℕ,
    departure (n + 1) ≤
      max (arrival (n + 1)) (departure n) + work (n + 1) / rate

namespace FCFSServiceFloorUpperBound

variable {arrival work departure : ℕ → ℝ} {rate : ℝ}

/-- The service-floor recurrence is pointwise bounded by the FCFS comparator. -/
theorem departure_le_fcfsDeparture
    (H : FCFSServiceFloorUpperBound arrival work departure rate) :
    ∀ n : ℕ, departure n ≤ fcfsDeparture arrival work rate n := by
  intro n
  induction n with
  | zero =>
      simpa [fcfsDeparture] using H.zero
  | succ n ih =>
      calc
        departure (n + 1) ≤
            max (arrival (n + 1)) (departure n) + work (n + 1) / rate :=
          H.succ n
        _ ≤ max (arrival (n + 1)) (fcfsDeparture arrival work rate n) +
              work (n + 1) / rate := by
          exact add_le_add_left (max_le_max_left _ ih) _
        _ = fcfsDeparture arrival work rate (n + 1) := by
          rfl

/-- The same service-floor recurrence bounds each tagged response time. -/
theorem responseTime_le_fcfsResponseTime
    (H : FCFSServiceFloorUpperBound arrival work departure rate) (n : ℕ) :
    responseTime arrival departure n ≤
      responseTime arrival (fcfsDeparture arrival work rate) n := by
  unfold responseTime
  exact sub_le_sub_right (H.departure_le_fcfsDeparture n) _

end FCFSServiceFloorUpperBound

namespace FCFSServiceFloorUpperBoundFromInitial

variable {initialBusyUntil : ℝ} {arrival work departure : ℕ → ℝ} {rate : ℝ}

/-- The initial-workload service-floor recurrence is bounded by its FCFS comparator. -/
theorem departure_le_fcfsDepartureFrom
    (H : FCFSServiceFloorUpperBoundFromInitial
      initialBusyUntil arrival work departure rate) :
    ∀ n : ℕ,
      departure n ≤ fcfsDepartureFrom initialBusyUntil arrival work rate n := by
  intro n
  induction n with
  | zero =>
      simpa [fcfsDepartureFrom] using H.zero
  | succ n ih =>
      calc
        departure (n + 1) ≤
            max (arrival (n + 1)) (departure n) + work (n + 1) / rate :=
          H.succ n
        _ ≤ max (arrival (n + 1))
              (fcfsDepartureFrom initialBusyUntil arrival work rate n) +
              work (n + 1) / rate := by
          exact add_le_add_left (max_le_max_left _ ih) _
        _ = fcfsDepartureFrom initialBusyUntil arrival work rate (n + 1) := by
          rfl

/-- The initial-workload recurrence bounds every tagged response time. -/
theorem responseTime_le_fcfsResponseTimeFrom
    (H : FCFSServiceFloorUpperBoundFromInitial
      initialBusyUntil arrival work departure rate) (n : ℕ) :
    responseTime arrival departure n ≤
      responseTime arrival
        (fcfsDepartureFrom initialBusyUntil arrival work rate) n := by
  unfold responseTime
  exact sub_le_sub_right (H.departure_le_fcfsDepartureFrom n) _

end FCFSServiceFloorUpperBoundFromInitial

/-- Pointwise FCFS comparator departure times for random arrival/work paths. -/
def fcfsComparatorDeparture
    {Ω : Type*} (arrival work : Ω → ℕ → ℝ) (rate : ℝ) : Ω → ℕ → ℝ :=
  fun ω => fcfsDeparture (arrival ω) (work ω) rate

/--
Pointwise FCFS comparator with a random initial busy-until time.  In a Palm
application, this input must carry the stationary pre-arrival workload.
-/
def fcfsComparatorDepartureFrom
    {Ω : Type*} (initialBusyUntil : Ω → ℝ)
    (arrival work : Ω → ℕ → ℝ) (rate : ℝ) : Ω → ℕ → ℝ :=
  fun ω => fcfsDepartureFrom (initialBusyUntil ω) (arrival ω) (work ω) rate

/--
Under a pathwise FCFS service floor, every response-tail event is contained in
the response-tail event of the constant-rate FCFS comparator.
-/
theorem responseTailEvent_subset_fcfsComparator
    {Ω : Type*} (arrival work departure : Ω → ℕ → ℝ) (rate z : ℝ) (n : ℕ)
    (H : ∀ ω : Ω,
      FCFSServiceFloorUpperBound (arrival ω) (work ω) (departure ω) rate) :
    {ω | z ≤ responseTime (arrival ω) (departure ω) n} ⊆
      {ω | z ≤ responseTime (arrival ω)
        (fcfsComparatorDeparture arrival work rate ω) n} := by
  intro ω hω
  exact le_trans hω ((H ω).responseTime_le_fcfsResponseTime n)

/--
The deterministic comparison lifts to an arbitrary measure as a tail-mass
upper bound.  A stationary/Palm M/M/1 law is a separate input for evaluating
the comparator mass, and is not inferred from the measure argument here.
-/
theorem measure_responseTail_le_fcfsComparator
    {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (arrival work departure : Ω → ℕ → ℝ) (rate z : ℝ) (n : ℕ)
    (H : ∀ ω : Ω,
      FCFSServiceFloorUpperBound (arrival ω) (work ω) (departure ω) rate) :
    P {ω | z ≤ responseTime (arrival ω) (departure ω) n} ≤
      P {ω | z ≤ responseTime (arrival ω)
        (fcfsComparatorDeparture arrival work rate ω) n} :=
  MeasureTheory.measure_mono
    (responseTailEvent_subset_fcfsComparator arrival work departure rate z n H)

/--
Real-valued version of the FCFS tail comparison under a finite measure.  In a
stationary queueing application, the caller must prove that `Ptag` is the Palm
law of the tagged arrival (or an equivalent stationary customer-average law),
rather than an arbitrary transient initial-state distribution.  This theorem
does not establish that interpretation from its typeclass assumptions.
-/
theorem taggedResponseTailReal_le_fcfsComparator
    {Ω : Type*} [MeasurableSpace Ω] (Ptag : MeasureTheory.Measure Ω)
    [MeasureTheory.IsFiniteMeasure Ptag]
    (arrival work departure : Ω → ℕ → ℝ) (rate z : ℝ) (n : ℕ)
    (H : ∀ ω : Ω,
      FCFSServiceFloorUpperBound (arrival ω) (work ω) (departure ω) rate) :
    Ptag.real {ω | z ≤ responseTime (arrival ω) (departure ω) n} ≤
      Ptag.real {ω | z ≤ responseTime (arrival ω)
        (fcfsComparatorDeparture arrival work rate ω) n} := by
  exact ENNReal.toReal_mono (MeasureTheory.measure_ne_top Ptag _)
    (measure_responseTail_le_fcfsComparator Ptag arrival work departure rate z n H)

/--
If the constant-rate FCFS comparator has a tail bound under `Ptag`, the
service-floor queue has the same bound.  The theorem deliberately does not
supply the comparator law: for GPS this is the separate stationary Palm
`M/M/1` analysis, including tag-at-origin and continuity/no-atom details if a
strict tail event is used there.
-/
theorem taggedResponseTailReal_le_of_fcfsComparatorTail
    {Ω : Type*} [MeasurableSpace Ω] (Ptag : MeasureTheory.Measure Ω)
    [MeasureTheory.IsFiniteMeasure Ptag]
    (arrival work departure : Ω → ℕ → ℝ) (rate z upperBound : ℝ) (n : ℕ)
    (H : ∀ ω : Ω,
      FCFSServiceFloorUpperBound (arrival ω) (work ω) (departure ω) rate)
    (hComparatorTail :
      Ptag.real {ω | z ≤ responseTime (arrival ω)
        (fcfsComparatorDeparture arrival work rate ω) n} ≤ upperBound) :
    Ptag.real {ω | z ≤ responseTime (arrival ω) (departure ω) n} ≤ upperBound :=
  (taggedResponseTailReal_le_fcfsComparator Ptag arrival work departure rate z n H).trans
    hComparatorTail

/-! ## Initial-workload tail comparison -/

/--
With an explicit initial workload, the response-tail event is contained in the
corresponding FCFS comparator event.  A stationary/Palm application must show
that this workload is the correctly coupled pre-tag residual work.
-/
theorem responseTailEvent_subset_fcfsComparatorFromInitial
    {Ω : Type*} (initialBusyUntil : Ω → ℝ)
    (arrival work departure : Ω → ℕ → ℝ) (rate z : ℝ) (n : ℕ)
    (H : ∀ ω : Ω,
      FCFSServiceFloorUpperBoundFromInitial (initialBusyUntil ω)
        (arrival ω) (work ω) (departure ω) rate) :
    {ω | z ≤ responseTime (arrival ω) (departure ω) n} ⊆
      {ω | z ≤ responseTime (arrival ω)
        (fcfsComparatorDepartureFrom initialBusyUntil arrival work rate ω) n} := by
  intro ω hω
  exact le_trans hω ((H ω).responseTime_le_fcfsResponseTimeFrom n)

/-- The initial-workload FCFS comparison lifts to any measure. -/
theorem measure_responseTail_le_fcfsComparatorFromInitial
    {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (initialBusyUntil : Ω → ℝ)
    (arrival work departure : Ω → ℕ → ℝ) (rate z : ℝ) (n : ℕ)
    (H : ∀ ω : Ω,
      FCFSServiceFloorUpperBoundFromInitial (initialBusyUntil ω)
        (arrival ω) (work ω) (departure ω) rate) :
    P {ω | z ≤ responseTime (arrival ω) (departure ω) n} ≤
      P {ω | z ≤ responseTime (arrival ω)
        (fcfsComparatorDepartureFrom initialBusyUntil arrival work rate ω) n} :=
  MeasureTheory.measure_mono
    (responseTailEvent_subset_fcfsComparatorFromInitial initialBusyUntil
      arrival work departure rate z n H)

/--
Real-valued initial-workload comparison under a finite measure.  When the
caller separately establishes that `Ptag` is a stationary Palm law,
`initialBusyUntil` can carry the coupled pre-arrival workload instead of
silently assuming the queue starts empty.
-/
theorem taggedResponseTailReal_le_fcfsComparatorFromInitial
    {Ω : Type*} [MeasurableSpace Ω] (Ptag : MeasureTheory.Measure Ω)
    [MeasureTheory.IsFiniteMeasure Ptag]
    (initialBusyUntil : Ω → ℝ)
    (arrival work departure : Ω → ℕ → ℝ) (rate z : ℝ) (n : ℕ)
    (H : ∀ ω : Ω,
      FCFSServiceFloorUpperBoundFromInitial (initialBusyUntil ω)
        (arrival ω) (work ω) (departure ω) rate) :
    Ptag.real {ω | z ≤ responseTime (arrival ω) (departure ω) n} ≤
      Ptag.real {ω | z ≤ responseTime (arrival ω)
        (fcfsComparatorDepartureFrom initialBusyUntil arrival work rate ω) n} := by
  exact ENNReal.toReal_mono (MeasureTheory.measure_ne_top Ptag _)
    (measure_responseTail_le_fcfsComparatorFromInitial Ptag initialBusyUntil
      arrival work departure rate z n H)

/--
Almost-everywhere initial-workload FCFS comparison.  This is the measure-level
form needed for stochastic path models whose service-floor recurrence may fail
only on null boundary paths.
-/
theorem measure_responseTail_le_fcfsComparatorFromInitial_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (initialBusyUntil : Ω → ℝ)
    (arrival work departure : Ω → ℕ → ℝ) (rate z : ℝ) (n : ℕ)
    (H : ∀ᵐ ω ∂P,
      FCFSServiceFloorUpperBoundFromInitial (initialBusyUntil ω)
        (arrival ω) (work ω) (departure ω) rate) :
    P {ω | z ≤ responseTime (arrival ω) (departure ω) n} ≤
      P {ω | z ≤ responseTime (arrival ω)
        (fcfsComparatorDepartureFrom initialBusyUntil arrival work rate ω) n} := by
  apply MeasureTheory.measure_mono_ae
  filter_upwards [H] with ω hω htail
  exact le_trans htail (hω.responseTime_le_fcfsResponseTimeFrom n)

/--
Real-valued almost-everywhere initial-workload comparison under a finite tagged
measure.
-/
theorem taggedResponseTailReal_le_fcfsComparatorFromInitial_ae
    {Ω : Type*} [MeasurableSpace Ω] (Ptag : MeasureTheory.Measure Ω)
    [MeasureTheory.IsFiniteMeasure Ptag]
    (initialBusyUntil : Ω → ℝ)
    (arrival work departure : Ω → ℕ → ℝ) (rate z : ℝ) (n : ℕ)
    (H : ∀ᵐ ω ∂Ptag,
      FCFSServiceFloorUpperBoundFromInitial (initialBusyUntil ω)
        (arrival ω) (work ω) (departure ω) rate) :
    Ptag.real {ω | z ≤ responseTime (arrival ω) (departure ω) n} ≤
      Ptag.real {ω | z ≤ responseTime (arrival ω)
        (fcfsComparatorDepartureFrom initialBusyUntil arrival work rate ω) n} := by
  exact ENNReal.toReal_mono (MeasureTheory.measure_ne_top Ptag _)
    (measure_responseTail_le_fcfsComparatorFromInitial_ae Ptag initialBusyUntil
      arrival work departure rate z n H)

/--
The initial-workload service-floor queue inherits every FCFS comparator tail
bound under the same finite measure.  Establishing that the measure is the
tagged stationary/Palm law and that the comparator is stationary `M/M/1`
remains a distinct stochastic-process theorem.
-/
theorem taggedResponseTailReal_le_of_fcfsComparatorTailFromInitial
    {Ω : Type*} [MeasurableSpace Ω] (Ptag : MeasureTheory.Measure Ω)
    [MeasureTheory.IsFiniteMeasure Ptag]
    (initialBusyUntil : Ω → ℝ)
    (arrival work departure : Ω → ℕ → ℝ) (rate z upperBound : ℝ) (n : ℕ)
    (H : ∀ ω : Ω,
      FCFSServiceFloorUpperBoundFromInitial (initialBusyUntil ω)
        (arrival ω) (work ω) (departure ω) rate)
    (hComparatorTail :
      Ptag.real {ω | z ≤ responseTime (arrival ω)
        (fcfsComparatorDepartureFrom initialBusyUntil arrival work rate ω) n} ≤
        upperBound) :
    Ptag.real {ω | z ≤ responseTime (arrival ω) (departure ω) n} ≤ upperBound :=
  (taggedResponseTailReal_le_fcfsComparatorFromInitial Ptag initialBusyUntil
    arrival work departure rate z n H).trans hComparatorTail

/--
Almost-everywhere service-floor variant of
`taggedResponseTailReal_le_of_fcfsComparatorTailFromInitial`.
-/
theorem taggedResponseTailReal_le_of_fcfsComparatorTailFromInitial_ae
    {Ω : Type*} [MeasurableSpace Ω] (Ptag : MeasureTheory.Measure Ω)
    [MeasureTheory.IsFiniteMeasure Ptag]
    (initialBusyUntil : Ω → ℝ)
    (arrival work departure : Ω → ℕ → ℝ) (rate z upperBound : ℝ) (n : ℕ)
    (H : ∀ᵐ ω ∂Ptag,
      FCFSServiceFloorUpperBoundFromInitial (initialBusyUntil ω)
        (arrival ω) (work ω) (departure ω) rate)
    (hComparatorTail :
      Ptag.real {ω | z ≤ responseTime (arrival ω)
        (fcfsComparatorDepartureFrom initialBusyUntil arrival work rate ω) n} ≤
        upperBound) :
    Ptag.real {ω | z ≤ responseTime (arrival ω) (departure ω) n} ≤ upperBound :=
  (taggedResponseTailReal_le_fcfsComparatorFromInitial_ae Ptag initialBusyUntil
    arrival work departure rate z n H).trans hComparatorTail

/--
If an actual response time is almost surely bounded by a comparator response
time, then any real-valued tail bound for the comparator transfers to the
actual response.
-/
theorem responseTailReal_le_of_ae_response_le
    {Ω : Type*} [MeasurableSpace Ω] (Ptag : MeasureTheory.Measure Ω)
    [MeasureTheory.IsFiniteMeasure Ptag]
    (actualResponse comparatorResponse : Ω → ℝ) (z upperBound : ℝ)
    (hResponse_le : ∀ᵐ ω ∂Ptag, actualResponse ω ≤ comparatorResponse ω)
    (hComparatorTail :
      Ptag.real {ω | z ≤ comparatorResponse ω} ≤ upperBound) :
    Ptag.real {ω | z ≤ actualResponse ω} ≤ upperBound := by
  have hmeasure :
      Ptag {ω | z ≤ actualResponse ω} ≤
        Ptag {ω | z ≤ comparatorResponse ω} := by
    apply MeasureTheory.measure_mono_ae
    filter_upwards [hResponse_le] with ω hle htail
    exact le_trans htail hle
  exact (ENNReal.toReal_mono (MeasureTheory.measure_ne_top Ptag _) hmeasure).trans
    hComparatorTail

/--
Strict-tail version of `responseTailReal_le_of_ae_response_le`.  This keeps
the event convention explicit when a response law is naturally stated as
`P(t < T)`, as for continuous-time queueing response bounds.  It needs only
almost-sure pointwise domination and does not assume either response has a
continuous distribution.
-/
theorem responseStrictTailReal_le_of_ae_response_le
    {Ω : Type*} [MeasurableSpace Ω] (Ptag : MeasureTheory.Measure Ω)
    [MeasureTheory.IsFiniteMeasure Ptag]
    (actualResponse comparatorResponse : Ω → ℝ) (z upperBound : ℝ)
    (hResponse_le : ∀ᵐ ω ∂Ptag, actualResponse ω ≤ comparatorResponse ω)
    (hComparatorTail :
      Ptag.real {ω | z < comparatorResponse ω} ≤ upperBound) :
    Ptag.real {ω | z < actualResponse ω} ≤ upperBound := by
  have hmeasure :
      Ptag {ω | z < actualResponse ω} ≤
        Ptag {ω | z < comparatorResponse ω} := by
    apply MeasureTheory.measure_mono_ae
    filter_upwards [hResponse_le] with ω hle htail
    exact lt_of_lt_of_le htail hle
  exact (ENNReal.toReal_mono (MeasureTheory.measure_ne_top Ptag _) hmeasure).trans
    hComparatorTail

end
end Queueing
end Probability
end AppliedModelingLib

import AppliedModelingLib.Foundations.Probability.PoissonProcess
import Mathlib.Probability.Process.Stopping

namespace AppliedModelingLib
namespace Probability
namespace PoissonProcess

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

/-!
# Native stopping-time bridges for Poisson process certificates

The Poisson-process likelihood layer historically used a lightweight
real-valued stopping-time predicate.  Mathlib's process API instead represents
stopping times in `WithTop`, so that an arrival which never occurs can be
recorded as `⊤`.  This module preserves the finite-time certificates used by
the paper interfaces while making them immediately usable by Mathlib's
stopping-time results.
-/

/-- View a finite real-valued random time as a `WithTop ℝ`-valued time. -/
def toNativeStoppingTime {Ω : Type*} (τ : Ω → ℝ) : Ω → WithTop ℝ :=
  fun ω => (τ ω : WithTop ℝ)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {𝓕 : Filtration (Ω := Ω) ℝ mΩ}
variable {τ : Ω → ℝ}

/--
The local finite-time predicate implies Mathlib's native `WithTop` stopping
time predicate.
-/
theorem isStoppingTime_toNative
    (hτ : IsStoppingTime 𝓕 τ) :
    MeasureTheory.IsStoppingTime 𝓕 (toNativeStoppingTime τ) := by
  intro t
  simpa [toNativeStoppingTime] using hτ t

/--
Conversely, a native stopping-time proof for a finite-valued random time gives
the local real-valued stopping-time predicate.
-/
theorem isStoppingTime_ofNative
    (hτ : MeasureTheory.IsStoppingTime 𝓕 (toNativeStoppingTime τ)) :
    IsStoppingTime 𝓕 τ := by
  intro t
  simpa [toNativeStoppingTime] using hτ t

/-- The finite-valued and native stopping-time predicates are equivalent. -/
theorem isStoppingTime_iff_native :
    IsStoppingTime 𝓕 τ ↔
      MeasureTheory.IsStoppingTime 𝓕 (toNativeStoppingTime τ) := by
  constructor
  · exact isStoppingTime_toNative
  · exact isStoppingTime_ofNative

namespace CountThresholdEventAdapted

variable {count : ℝ → Ω → ℕ} {threshold : ℕ}

/--
An adapted counting process has measurable threshold events at each time.
This is the Mathlib `Adapted` spelling of `of_measurable_count`.
-/
theorem of_adapted
    (hcount : Adapted 𝓕 count) :
    CountThresholdEventAdapted 𝓕 count threshold :=
  of_measurable_count hcount

end CountThresholdEventAdapted

/--
A homogeneous Poisson counting-process law equipped with a filtration to which
its count coordinates are adapted.

`HomogeneousPoissonCountingProcessByLaw` supplies stationary independent
increments and their Poisson laws; this wrapper adds only the filtration
compatibility needed to turn a separately established first-arrival sublevel
identity into a stopping-time theorem.  It intentionally does not assert that
such a process has been constructed from primitive interarrival paths.
-/
structure FilteredHomogeneousPoissonCountingProcessByLaw
    (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) where
  process : HomogeneousPoissonCountingProcessByLaw Ω P
  filtration : Filtration (Ω := Ω) ℝ inferInstance
  count_adapted : Adapted filtration process.count

namespace FilteredHomogeneousPoissonCountingProcessByLaw

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Adapted count paths have measurable count-threshold events at every time. -/
theorem countThresholdEventAdapted
    (H : FilteredHomogeneousPoissonCountingProcessByLaw Ω P)
    (threshold : ℕ) :
    CountThresholdEventAdapted H.filtration H.process.count threshold :=
  CountThresholdEventAdapted.of_adapted H.count_adapted

/--
Construct the natural filtration of an already specified homogeneous Poisson
count path.  Once coordinate strong measurability is proved for a concrete
path-space construction, adaptedness is automatic; this theorem does not
construct the path or establish its Poisson increment law.
-/
def ofNaturalFiltration
    (process : HomogeneousPoissonCountingProcessByLaw Ω P)
    (hcount : ∀ t : ℝ, StronglyMeasurable (process.count t)) :
    FilteredHomogeneousPoissonCountingProcessByLaw Ω P where
  process := process
  filtration := Filtration.natural process.count hcount
  count_adapted := (Filtration.stronglyAdapted_natural hcount).adapted

/--
Package a finite first-arrival sublevel identity with an adapted homogeneous
Poisson count process.  The remaining input is exactly the path-space fact
that the candidate time reaches level one iff the count has reached one.
-/
def firstCountArrivalCertificate
    (H : FilteredHomogeneousPoissonCountingProcessByLaw Ω P)
    (arrivalTime : Ω → ℝ)
    (hlevel : ∀ t : ℝ,
      {ω | arrivalTime ω ≤ t} = {ω | 1 ≤ H.process.count t ω}) :
    FirstCountArrivalCertificate H.filtration H.process.count arrivalTime where
  count_event_adapted := H.countThresholdEventAdapted 1
  level_sets := hlevel

end FilteredHomogeneousPoissonCountingProcessByLaw

/--
Certificate that a first count-arrival time is observable at every finite time,
while allowing paths on which the first arrival never occurs to take value
`⊤`.  This is a certificate interface only: constructing it from a concrete
counting-process path remains a separate path-space result.
-/
structure FirstCountArrivalWithTopCertificate
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (𝓕 : Filtration (Ω := Ω) ℝ mΩ) (count : ℝ → Ω → ℕ)
    (firstArrival : Ω → WithTop ℝ) where
  count_event_adapted : CountThresholdEventAdapted 𝓕 count 1
  level_sets :
    ∀ t : ℝ, {ω | firstArrival ω ≤ t} = {ω | 1 ≤ count t ω}

namespace FirstCountArrivalWithTopCertificate

variable {count : ℝ → Ω → ℕ} {firstArrival : Ω → WithTop ℝ}

/-- A certified possibly-infinite first arrival is a native Mathlib stopping time. -/
theorem isStoppingTime
    (C : FirstCountArrivalWithTopCertificate 𝓕 count firstArrival) :
    MeasureTheory.IsStoppingTime 𝓕 firstArrival := by
  intro t
  rw [C.level_sets t]
  exact C.count_event_adapted t

end FirstCountArrivalWithTopCertificate

namespace FilteredHomogeneousPoissonCountingProcessByLaw

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/--
Package a possibly-infinite first-arrival sublevel identity with an adapted
homogeneous Poisson count process.  `⊤` represents paths with no first arrival.
-/
def firstCountArrivalWithTopCertificate
    (H : FilteredHomogeneousPoissonCountingProcessByLaw Ω P)
    (firstArrival : Ω → WithTop ℝ)
    (hlevel : ∀ t : ℝ,
      {ω | firstArrival ω ≤ t} = {ω | 1 ≤ H.process.count t ω}) :
    FirstCountArrivalWithTopCertificate H.filtration H.process.count firstArrival where
  count_event_adapted := H.countThresholdEventAdapted 1
  level_sets := hlevel

end FilteredHomogeneousPoissonCountingProcessByLaw

namespace DurationCensoredFirstCountObservationCertificate

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/--
Build the finite duration-censored observation certificate directly from an
adapted homogeneous Poisson process and the remaining endpoint/order facts.
The construction still requires a finite first-arrival sublevel identity; a
future path-space module is responsible for proving that identity.
-/
def ofFilteredHomogeneousPoisson
    (H : FilteredHomogeneousPoissonCountingProcessByLaw Ω P)
    (firstTime endpointOne endpointTwo : Ω → ℝ) (durationCap : ℝ)
    (h_durationCap : 0 ≤ durationCap)
    (h_first_level_sets : ∀ t : ℝ,
      {ω | firstTime ω ≤ t} = {ω | 1 ≤ H.process.count t ω})
    (h_endpointOne_stopping : IsStoppingTime H.filtration endpointOne)
    (h_endpointTwo_stopping : IsStoppingTime H.filtration endpointTwo)
    (h_first_le_endpointOne : ∀ ω, firstTime ω ≤ endpointOne ω)
    (h_first_le_endpointTwo : ∀ ω, firstTime ω ≤ endpointTwo ω) :
    DurationCensoredFirstCountObservationCertificate H.filtration :=
  ofStoppingEndpoints H.process.count firstTime endpointOne endpointTwo
    durationCap h_durationCap H.count_adapted h_first_level_sets
    h_endpointOne_stopping h_endpointTwo_stopping
    h_first_le_endpointOne h_first_le_endpointTwo

end DurationCensoredFirstCountObservationCertificate

namespace FirstCountArrivalCertificate

variable {count : ℝ → Ω → ℕ} {arrivalTime : Ω → ℝ}

/--
A certified first count-arrival time is a native Mathlib stopping time after
the canonical finite-time embedding into `WithTop ℝ`.
-/
theorem isStoppingTime_native
    (C : FirstCountArrivalCertificate 𝓕 count arrivalTime) :
    MeasureTheory.IsStoppingTime 𝓕 (toNativeStoppingTime arrivalTime) :=
  isStoppingTime_toNative C.isStoppingTime

end FirstCountArrivalCertificate

end

end PoissonProcess
end Probability
end AppliedModelingLib

import AppliedModelingLib.Foundations.Probability.ForwardPoisson
import Mathlib.Probability.Process.Stopping

/-!
# Native stopping-time bridges for forward Poisson paths

Forward post-tag count paths live on `ℝ≥0`.  This module adds only the
filtration and first-arrival bookkeeping needed to make a concrete forward
path usable by Mathlib's native stopping-time API; it does not assert a
strong-Markov theorem.
-/

namespace AppliedModelingLib
namespace Probability
namespace PoissonProcess

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

/-- Embed a finite forward time as a native possibly-infinite stopping time. -/
def toNativeForwardStoppingTime {Ω : Type*} (τ : Ω → ℝ≥0) : Ω → WithTop ℝ≥0 :=
  fun ω => (τ ω : WithTop ℝ≥0)

/-- Threshold-event adaptedness for a forward nonnegative-time count path. -/
def ForwardCountThresholdEventAdapted
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (𝓕 : Filtration (Ω := Ω) ℝ≥0 mΩ) (count : ℝ≥0 → Ω → ℕ)
    (threshold : ℕ) : Prop :=
  ∀ t : ℝ≥0, MeasurableSet[𝓕 t] {ω | threshold ≤ count t ω}

namespace ForwardCountThresholdEventAdapted

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {𝓕 : Filtration (Ω := Ω) ℝ≥0 mΩ}
variable {count : ℝ≥0 → Ω → ℕ} {threshold : ℕ}

/-- Adapted forward count coordinates make every count-threshold event observable. -/
theorem of_adapted (hcount : Adapted 𝓕 count) :
    ForwardCountThresholdEventAdapted 𝓕 count threshold := by
  intro t
  exact hcount t measurableSet_Ici

end ForwardCountThresholdEventAdapted

/--
A forward homogeneous Poisson count law together with a compatible
nonnegative-time filtration.
-/
structure FilteredForwardHomogeneousPoissonCountingProcessByLaw
    (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) where
  process : ForwardHomogeneousPoissonCountingProcessByLaw Ω P
  filtration : Filtration (Ω := Ω) ℝ≥0 inferInstance
  count_adapted : Adapted filtration process.count

namespace FilteredForwardHomogeneousPoissonCountingProcessByLaw

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Build the natural forward filtration of an already specified count path. -/
def ofNaturalFiltration
    (process : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (hcount : ∀ t : ℝ≥0, StronglyMeasurable (process.count t)) :
    FilteredForwardHomogeneousPoissonCountingProcessByLaw Ω P where
  process := process
  filtration := Filtration.natural process.count hcount
  count_adapted := (Filtration.stronglyAdapted_natural hcount).adapted

/-- An adapted forward count exposes every count-threshold event in time. -/
theorem countThresholdEventAdapted
    (H : FilteredForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (threshold : ℕ) :
    ForwardCountThresholdEventAdapted H.filtration H.process.count threshold :=
  ForwardCountThresholdEventAdapted.of_adapted H.count_adapted

end FilteredForwardHomogeneousPoissonCountingProcessByLaw

/--
Certificate that a finite forward time is the first arrival of a forward
counting path.  The level-set equality is the sole path-specific input.
-/
structure ForwardFirstCountArrivalCertificate
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (𝓕 : Filtration (Ω := Ω) ℝ≥0 mΩ) (count : ℝ≥0 → Ω → ℕ)
    (firstArrival : Ω → ℝ≥0) where
  count_event_adapted : ForwardCountThresholdEventAdapted 𝓕 count 1
  level_sets : ∀ t : ℝ≥0,
    {ω | firstArrival ω ≤ t} = {ω | 1 ≤ count t ω}

namespace ForwardFirstCountArrivalCertificate

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {𝓕 : Filtration (Ω := Ω) ℝ≥0 mΩ}
variable {count : ℝ≥0 → Ω → ℕ} {firstArrival : Ω → ℝ≥0}

/-- A certified finite forward first arrival is a native Mathlib stopping time. -/
theorem isStoppingTime_native
    (C : ForwardFirstCountArrivalCertificate 𝓕 count firstArrival) :
    MeasureTheory.IsStoppingTime 𝓕 (toNativeForwardStoppingTime firstArrival) := by
  intro t
  have hset :
      {ω | toNativeForwardStoppingTime firstArrival ω ≤ (t : WithTop ℝ≥0)} =
        {ω | firstArrival ω ≤ t} := by
    ext ω
    change ((firstArrival ω : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)) ↔
      firstArrival ω ≤ t
    constructor <;> intro h <;> exact_mod_cast h
  rw [hset, C.level_sets t]
  exact C.count_event_adapted t

end ForwardFirstCountArrivalCertificate

namespace FilteredForwardHomogeneousPoissonCountingProcessByLaw

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Build a first-arrival stopping certificate from the forward path-level identity. -/
def firstCountArrivalCertificate
    (H : FilteredForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (firstArrival : Ω → ℝ≥0)
    (hlevel : ∀ t : ℝ≥0,
      {ω | firstArrival ω ≤ t} = {ω | 1 ≤ H.process.count t ω}) :
    ForwardFirstCountArrivalCertificate H.filtration H.process.count firstArrival where
  count_event_adapted := H.countThresholdEventAdapted 1
  level_sets := hlevel

end FilteredForwardHomogeneousPoissonCountingProcessByLaw

end
end PoissonProcess
end Probability
end AppliedModelingLib

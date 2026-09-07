import AppliedModelingLib.Foundations.Probability.PoissonProcess

/-!
# Tagged-arrival interface

This leaf records an externally constructed arrival path whose distinguished
arrival is recentered to index and time zero.  It does not assert a Palm
identity, stationarity, PASTA, or queue dynamics.
-/

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory

/--
An externally constructed tagged-arrival path, recentered so that its tag has
index zero and occurs at time zero.  This structure is intentionally not named
`Palm`: it records only the path facts common to a Palm construction.  A full
Palm construction must additionally relate `Ptag` to an untagged stationary
law through a Campbell/Palm identity.
-/
structure TaggedArrivalAtZero
    (Ω : Type*) [MeasurableSpace Ω] where
  /-- Probability law of the externally constructed tagged sample. -/
  Ptag : Measure Ω
  /-- The tagged sample law is a probability measure. -/
  isProbability : IsProbabilityMeasure Ptag
  /-- Arrival epochs around the tag, indexed so the tag has index `0`. -/
  arrivals : Ω → ℤ → ℝ
  /-- The tagged arrival is at the reindexed time origin almost surely. -/
  tag_at_zero : ∀ᵐ ω ∂Ptag, arrivals ω 0 = 0
  /-- The arrival epochs are strictly ordered almost surely. -/
  arrivals_strict : ∀ᵐ ω ∂Ptag, StrictMono (arrivals ω)

end AppliedModelingLib.Probability.Queueing

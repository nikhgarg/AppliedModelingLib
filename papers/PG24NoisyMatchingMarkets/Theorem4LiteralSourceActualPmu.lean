import PG24NoisyMatchingMarkets.Theorem4LiteralSourceStableAdapter
import PG24NoisyMatchingMarkets.Theorem4CoalitionSubsetTransport
import Mathlib.Tactic

/-!
# PG24 Theorem 4 Actual-Coalition `p_mu`

The analytic route indexes coalition colleges by `Fin (C + 1)`.  This module
defines the source-facing affordability probability for an actual finite
subset of the global college carrier by pulling that subset back along the
coalition embedding.
-/

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u v w x

/-- Pull an actual global-college subset back to the indexed coalition. -/
noncomputable def theorem4PullbackCoalitionSubset
    {n : ℕ} {GlobalCollege : Type u}
    (embedding : Fin n ↪ GlobalCollege) (actualSubset : Finset GlobalCollege) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun index => embedding index ∈ actualSubset)

/-- Pulling back an embedded indexed subset recovers its exact index set. -/
theorem theorem4PullbackCoalitionSubset_embedded_eq
    {n : ℕ} {GlobalCollege : Type u}
    (embedding : Fin n ↪ GlobalCollege) (indexedSubset : Finset (Fin n)) :
    theorem4PullbackCoalitionSubset embedding
        (theorem4EmbeddedCoalitionSubset embedding indexedSubset) =
      indexedSubset := by
  classical
  ext index
  simp [theorem4PullbackCoalitionSubset, theorem4EmbeddedCoalitionSubset]

namespace PG24LiteralSourceStableData

variable {C : ℕ} {noiseLaw eta : MeasureTheory.Measure ℝ} {totalSupply : ℝ}
variable {StudentType : Type u} [MeasurableSpace StudentType]
variable {Outcome : Type v} [MeasurableSpace Outcome]
variable {GlobalCollege : Type w} [Fintype GlobalCollege]
variable {Cutoff : Type x}

/--
The source-facing `p_mu(v, C')` for an actual subset of the global college
carrier.  Colleges outside the embedded coalition do not contribute to the
coalition probability.
-/
noncomputable def pMuOnActualSubset
    (data :
      PG24LiteralSourceStableData C noiseLaw eta totalSupply
        StudentType Outcome GlobalCollege Cutoff)
    (value : ℝ) (actualSubset : Finset GlobalCollege) : ℝ :=
  (data.toExtendedCoalitionSourceStableInstance).pMu value
    (theorem4PullbackCoalitionSubset data.coalitionEmbedding actualSubset)

/-- The actual-subset `p_mu` agrees with indexed `p_mu` on embedded subsets. -/
theorem pMuOnActualSubset_embedded_eq_indexed
    (data :
      PG24LiteralSourceStableData C noiseLaw eta totalSupply
        StudentType Outcome GlobalCollege Cutoff)
    (value : ℝ) (indexedSubset : Finset (Fin (C + 1))) :
    data.pMuOnActualSubset value
        (theorem4EmbeddedCoalitionSubset data.coalitionEmbedding indexedSubset) =
      (data.toExtendedCoalitionSourceStableInstance).pMu value indexedSubset := by
  rw [pMuOnActualSubset,
    theorem4PullbackCoalitionSubset_embedded_eq]

end PG24LiteralSourceStableData

end

end PG24NoisyMatchingMarkets

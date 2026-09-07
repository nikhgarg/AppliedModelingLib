import GKGMM19IterativeLocalVoting.ProofInterface
import AppliedModelingLib.Foundations.Optimization.FiniteSubgradientCoordinateBounds

/-!
# Appendix Lemma 1: Uniform Direction Bounds

The source quantifies over every sampled-cost subgradient.  These lemmas keep
that quantifier explicit and obtain the finite bound from Lean's subgradient
inequality, rather than selecting a convenient candidate.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace GKGMM19IterativeLocalVoting

noncomputable section

/-- Appendix Lemma 1's `(p,q) = (2,2)` bound for every sampled-cost subgradient. -/
theorem appendixLemma1_l2BallDirection_uniform_gap_all_subgradients
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {center ideal : Coord → ℝ} {r : ℝ} (hr : 0 < r)
    (g : Coord → ℝ)
    (hsub : FiniteSubgradientAt
      (fun y : Coord → ℝ =>
        AppliedModelingLib.FiniteDimensionalNorms.l2 (fun i => y i - ideal i)) center g) :
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq
      (fun i => l2BallDirection center ideal r i - g i) ≤ 4 * Fintype.card Coord := by
  classical
  have hcoordinate : ∀ i, |l2BallDirection center ideal r i - g i| ≤ 2 := by
    intro i
    have hdir : |l2BallDirection center ideal r i| ≤ 1 := by
      exact (AppliedModelingLib.FiniteDimensionalNorms.normL2_coord_abs_le
        (l2BallDirection center ideal r) i).trans
        (l2BallDirection_l2_le_one hr)
    have hsubcoordinate : |g i| ≤ 1 :=
      AppliedModelingLib.Optimization.finiteSubgradientAt_l2Distance_coordinate_abs_le_one hsub i
    calc
      |l2BallDirection center ideal r i - g i| ≤
          |l2BallDirection center ideal r i| + |g i| := by
        simpa using (abs_sub_le (l2BallDirection center ideal r i) 0 (g i))
      _ ≤ 2 := by linarith
  have hnorm := AppliedModelingLib.FiniteDimensionalNorms.normL2Sq_le_card_mul_sq_of_abs_le
    (fun i => l2BallDirection center ideal r i - g i) (by norm_num : (0 : ℝ) ≤ 2)
    hcoordinate
  norm_num at hnorm ⊢
  nlinarith [hnorm]

/-- Appendix Lemma 1's `(p,q) = (1,∞)` bound for every sampled-cost subgradient. -/
theorem appendixLemma1_l1LinfBallDirection_uniform_gap_all_subgradients
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {center ideal : Coord → ℝ} {r : ℝ} (hr : 0 < r)
    (g : Coord → ℝ)
    (hsub : FiniteSubgradientAt
      (fun y : Coord → ℝ =>
        AppliedModelingLib.FiniteDimensionalNorms.l1 (fun i => y i - ideal i)) center g) :
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq
      (fun i => l1LinfBallDirection center ideal r i - g i) ≤ 4 * Fintype.card Coord := by
  classical
  have hcoordinate : ∀ i, |l1LinfBallDirection center ideal r i - g i| ≤ 2 := by
    intro i
    have hdir : |l1LinfBallDirection center ideal r i| ≤ 1 :=
      l1LinfBallDirection_coordinate_abs_le_one (center := center) (ideal := ideal) (i := i) hr
    have hsubcoordinate : |g i| ≤ 1 :=
      AppliedModelingLib.Optimization.finiteSubgradientAt_l1Distance_coordinate_abs_le_one hsub i
    calc
      |l1LinfBallDirection center ideal r i - g i| ≤
          |l1LinfBallDirection center ideal r i| + |g i| := by
        simpa using (abs_sub_le (l1LinfBallDirection center ideal r i) 0 (g i))
      _ ≤ 2 := by linarith
  have hnorm := AppliedModelingLib.FiniteDimensionalNorms.normL2Sq_le_card_mul_sq_of_abs_le
    (fun i => l1LinfBallDirection center ideal r i - g i) (by norm_num : (0 : ℝ) ≤ 2)
    hcoordinate
  norm_num at hnorm ⊢
  nlinarith [hnorm]

/-- Appendix Lemma 1's `(p,q) = (∞,1)` bound for every sampled-cost subgradient. -/
theorem appendixLemma1_linfL1RawDirection_uniform_gap_all_subgradients
    {Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {center ideal raw : Coord → ℝ} {r : ℝ} (hr : 0 < r)
    (hraw : finiteCoordinateDistance SourceNorm.l1 raw center ≤ r)
    (g : Coord → ℝ)
    (hsub : FiniteSubgradientAt
      (fun y : Coord → ℝ =>
        AppliedModelingLib.FiniteDimensionalNorms.linf (fun i => y i - ideal i)) center g) :
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq
      (fun i => linfL1RawDirection center raw r i - g i) ≤ 4 * Fintype.card Coord := by
  have hcoordinate : ∀ i, |linfL1RawDirection center raw r i - g i| ≤ 2 := by
    intro i
    have hdir : |linfL1RawDirection center raw r i| ≤ 1 :=
      linfL1RawDirection_coordinate_abs_le_one (center := center) (raw := raw) (i := i) hr hraw
    have hsubcoordinate : |g i| ≤ 1 :=
      AppliedModelingLib.Optimization.finiteSubgradientAt_linfDistance_coordinate_abs_le_one hsub i
    calc
      |linfL1RawDirection center raw r i - g i| ≤
          |linfL1RawDirection center raw r i| + |g i| := by
        simpa using (abs_sub_le (linfL1RawDirection center raw r i) 0 (g i))
      _ ≤ 2 := by linarith
  have hnorm := AppliedModelingLib.FiniteDimensionalNorms.normL2Sq_le_card_mul_sq_of_abs_le
    (fun i => linfL1RawDirection center raw r i - g i) (by norm_num : (0 : ℝ) ≤ 2)
    hcoordinate
  norm_num at hnorm ⊢
  nlinarith [hnorm]

/-- The source's unsquared finite constant for the `(2,2)` Appendix-Lemma-1 case. -/
theorem appendixLemma1_l2BallDirection_uniform_norm_gap_all_subgradients
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {center ideal : Coord → ℝ} {r : ℝ} (hr : 0 < r)
    (g : Coord → ℝ)
    (hsub : FiniteSubgradientAt
      (fun y : Coord → ℝ =>
        AppliedModelingLib.FiniteDimensionalNorms.l2 (fun i => y i - ideal i)) center g) :
    AppliedModelingLib.FiniteDimensionalNorms.l2
      (fun i => l2BallDirection center ideal r i - g i) ≤ 2 * Fintype.card Coord := by
  classical
  apply AppliedModelingLib.Optimization.normL2_le_two_card_of_normL2Sq_le_four_card
  exact appendixLemma1_l2BallDirection_uniform_gap_all_subgradients hr g hsub

/-- The source's unsquared finite constant for the `(1,∞)` Appendix-Lemma-1 case. -/
theorem appendixLemma1_l1LinfBallDirection_uniform_norm_gap_all_subgradients
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {center ideal : Coord → ℝ} {r : ℝ} (hr : 0 < r)
    (g : Coord → ℝ)
    (hsub : FiniteSubgradientAt
      (fun y : Coord → ℝ =>
        AppliedModelingLib.FiniteDimensionalNorms.l1 (fun i => y i - ideal i)) center g) :
    AppliedModelingLib.FiniteDimensionalNorms.l2
      (fun i => l1LinfBallDirection center ideal r i - g i) ≤ 2 * Fintype.card Coord := by
  classical
  apply AppliedModelingLib.Optimization.normL2_le_two_card_of_normL2Sq_le_four_card
  exact appendixLemma1_l1LinfBallDirection_uniform_gap_all_subgradients hr g hsub

/-- The source's unsquared finite constant for the `(∞,1)` Appendix-Lemma-1 case. -/
theorem appendixLemma1_linfL1RawDirection_uniform_norm_gap_all_subgradients
    {Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {center ideal raw : Coord → ℝ} {r : ℝ} (hr : 0 < r)
    (hraw : finiteCoordinateDistance SourceNorm.l1 raw center ≤ r)
    (g : Coord → ℝ)
    (hsub : FiniteSubgradientAt
      (fun y : Coord → ℝ =>
        AppliedModelingLib.FiniteDimensionalNorms.linf (fun i => y i - ideal i)) center g) :
    AppliedModelingLib.FiniteDimensionalNorms.l2
      (fun i => linfL1RawDirection center raw r i - g i) ≤ 2 * Fintype.card Coord := by
  apply AppliedModelingLib.Optimization.normL2_le_two_card_of_normL2Sq_le_four_card
  exact appendixLemma1_linfL1RawDirection_uniform_gap_all_subgradients hr hraw g hsub

/-!
## Exceptional-event bridges for Appendix Lemmas 2 and 4

The source defines its exceptional events through failure of the realized
Model-A direction to be a sampled-cost subgradient.  The conditional estimates
use Borel envelopes.  These pointwise bridges make the containment explicit:
outside the displayed envelope, the actual direction is a sampled
subgradient.  Consequently a failure is contained in that envelope.
-/

/-- Off the Euclidean-ball envelope, the exact `L2/L2` Model-A direction is a
subgradient of the realized sampled cost. -/
theorem l2BallDirection_subgradient_of_notMem_badEvent
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {center ideal : Coord → ℝ} {r : ℝ} (hr : 0 < r)
    (hgood : ideal ∉ l2BallBadEvent center r) :
    FiniteSubgradientAt
      (fun y : Coord → ℝ =>
        AppliedModelingLib.FiniteDimensionalNorms.l2 (fun i => y i - ideal i))
      center (l2BallDirection center ideal r) := by
  rw [l2BallDirection_eq_l2DistanceNormalizedGradient_of_notMem_badEvent hr hgood]
  apply finiteSubgradientAt_l2DistanceNormalizedGradient
  by_contra hne
  push Not at hne
  have hcenter : center = ideal := by
    funext i
    exact hne i
  have hzero : finiteCoordinateDistance SourceNorm.l2 center ideal = 0 :=
    (finiteCoordinateDistance_l2_eq_zero_iff center ideal).mpr hcenter
  apply hgood
  simpa [l2BallBadEvent, hzero] using hr

/-- Off the coordinate-slab envelope, the exact `L1/L∞` Model-A direction is a
subgradient of the realized sampled cost. -/
theorem l1LinfBallDirection_subgradient_of_notMem_slabBadEvent
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {center ideal : Coord → ℝ} {r : ℝ} (hr : 0 < r)
    (hgood : ideal ∉ l1LinfSlabBadEvent center r) :
    FiniteSubgradientAt
      (fun y : Coord → ℝ =>
        AppliedModelingLib.FiniteDimensionalNorms.l1 (fun i => y i - ideal i))
      center (l1LinfBallDirection center ideal r) := by
  rw [l1LinfBallDirection_eq_lpCostGradientCandidate_one_of_notMem_slabBadEvent
    hr hgood]
  simpa only [AppliedModelingLib.FiniteDimensionalNorms.lp_one] using
    finiteSubgradientAt_lpCostGradientCandidate_one (x := center) (ideal := ideal)
      (fun i => by
        have hseparation : r ≤ |center i - ideal i| :=
          (notMem_l1LinfSlabBadEvent_iff center ideal r).mp hgood i
        intro heq
        have hpositive : 0 < |center i - ideal i| := lt_of_lt_of_le hr hseparation
        simp [heq] at hpositive)

/-- Off the corrected slab-or-near-tie envelope, the exact water-filled
`L∞/L1` Model-A direction is a sampled-cost subgradient. -/
theorem linfL1WaterfillRawDirection_subgradient_of_notMem_correctedEnvelope
    {Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {center ideal : Coord → ℝ} {r : ℝ} (hr : 0 < r)
    (hgood : ideal ∉
      l1LinfSlabBadEvent center r ∪ linfL1NearTieBadEvent center r) :
    FiniteSubgradientAt
      (fun y : Coord → ℝ =>
        AppliedModelingLib.FiniteDimensionalNorms.linf (fun i => y i - ideal i))
      center
      (linfL1RawDirection center (linfL1WaterfillRawResponse center ideal r) r) := by
  have hcorrected : LinfL1CorrectedGood center ideal r := by
    by_contra hbad
    exact hgood (linfL1CorrectedBadEvent_subset_slab_union_nearTie center r hbad)
  rw [linfL1WaterfillRawDirection_eq_symmetricDirection_of_good hr hcorrected]
  exact finiteSubgradientAt_linfL1SymmetricActiveDirection center ideal

/-- Off the Definition-2 block-crossing envelope, every valid selected Model-A
response has a direction that is a subgradient of the realized joint cost. -/
theorem weightedEuclideanJointSampleModelARawDirection_subgradient_of_valid_of_notMem_blockBadEvent
    {Coord Component : Type*} [Fintype Coord] [Fintype Component] [Nonempty Coord]
    {D : WeightedEuclideanJointSampleData Coord Component}
    (A : WeightedEuclideanJointSampleModelAResponseSource D)
    {state : Coord → ℝ} {radius : ℝ} (hradius : 0 < radius)
    (sample : (Component → ℝ) × (Coord → ℝ))
    (hweight : ∀ k, 0 ≤ D.sampleWeight sample k)
    (hweightNorm : 0 < D.sampleWeightNorm2 sample)
    (hgood : sample ∉ weightedEuclideanJointSampleBlockBadEvent D state radius) :
    FiniteSubgradientAt (weightedEuclideanJointSampleCost D sample) state
      (weightedEuclideanJointSampleModelARawDirection A state radius sample) := by
  rw [weightedEuclideanJointSampleModelARawDirection_eq_direction_of_blockGood
    A hradius sample hweight hweightNorm
      ((notMem_weightedEuclideanJointSampleBlockBadEvent_iff D state radius sample).mp hgood)]
  exact weightedEuclideanJointSampleDirection_subgradient_of_blockGood
    D hradius sample (fun k => div_nonneg (hweight k) hweightNorm.le)
    ((notMem_weightedEuclideanJointSampleBlockBadEvent_iff D state radius sample).mp hgood)

end

end GKGMM19IterativeLocalVoting

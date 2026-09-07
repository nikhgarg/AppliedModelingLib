import KR21Monoculture.MallowsSupport
import KR21Monoculture.FiberSigns

open scoped BigOperators
open AppliedModelingLib

namespace KR21Monoculture

namespace MallowsSpec

variable {n : ℕ} (M : MallowsSpec n)

/--
If values weakly decrease down the center ranking, then the center's top-candidate
fiber contributes nonnegatively to the gap-mass decomposition.
-/
theorem centerFirstGapMass_nonneg_of_weaklyOrderedCenter
    {value : Candidate n → ℝ}
    (hvalue : WeaklyOrderedBy M.center value) :
    0 ≤ firstChoiceGapMass M.law value M.centerFirst := by
  simpa [MallowsSpec.centerFirst] using
    firstChoiceGapMass_nonneg_of_referenceTop_weaklyOrdered
      (μ := M.law) (ρ := M.center) (value := value) hvalue

/--
If values strictly decrease down the center ranking, then the center's top-candidate
fiber contributes strictly positively to the gap-mass decomposition.
-/
theorem centerFirstGapMass_pos_of_strictlyOrderedCenter
    {value : Candidate n → ℝ}
    (hvalue : StrictlyOrderedBy M.center value) :
    0 < firstChoiceGapMass M.law value M.centerFirst := by
  simpa [MallowsSpec.centerFirst] using
    firstChoiceGapMass_pos_of_reference_mass_pos_and_strictlyOrderedBy
      (μ := M.law) (ρ := M.center) (value := value)
      M.center_mass_toReal_pos hvalue

end MallowsSpec

namespace MallowsComparison

variable {n : ℕ} (C : MallowsComparison n)

/--
The algorithm's center-top gap mass is automatically positive under a strictly
center-ordered value vector.
-/
theorem algorithm_centerGapMass_pos_of_strictlyCenterOrdered
    {value : Candidate n → ℝ}
    (hvalue : C.StrictlyCenterOrdered value) :
    0 < firstChoiceGapMass C.algorithm.law value C.algorithm.centerFirst :=  C.algorithm.centerFirstGapMass_pos_of_strictlyOrderedCenter hvalue

/--
The human law has the same positive center-top gap mass conclusion because both
Mallows laws share the same center ranking.
-/
theorem human_centerGapMass_pos_of_strictlyCenterOrdered
    {value : Candidate n → ℝ}
    (hvalue : C.StrictlyCenterOrdered value) :
    0 < firstChoiceGapMass C.human.law value C.human.centerFirst := by
  have hhuman : StrictlyOrderedBy C.human.center value := by
    rw [← C.same_center]
    exact hvalue
  exact C.human.centerFirstGapMass_pos_of_strictlyOrderedCenter hhuman

/--
A practical Theorem-3 certificate.

To prove the candidate-sum hypotheses, it is enough to show:
1. all candidatewise summands are nonnegative,
2. the common center's top candidate has strictly positive miss probability for
   each law,
3. the better law puts strictly more first-choice mass on that top candidate,
4. values strictly decrease down the common center ranking.

This packages the exact data needed to convert center-candidate inequalities into
`CandidateSumCertificate`.
-/
structure CenterPositiveCertificate (value : Candidate n → ℝ) : Prop where
  strictly_center_ordered : C.StrictlyCenterOrdered value
  algorithm_nonneg :
    ∀ c : Candidate n,
      0 ≤ firstChoiceMissProb C.algorithm.law c *
        firstChoiceGapMass C.algorithm.law value c
  human_nonneg :
    ∀ c : Candidate n,
      0 ≤ firstChoiceMissProb C.human.law c *
        firstChoiceGapMass C.human.law value c
  weaker_nonneg :
    ∀ c : Candidate n,
      0 ≤ firstChoiceCollisionDiff C.algorithm.law C.human.law c *
        firstChoiceGapMass C.human.law value c
  algorithm_center_miss_pos :
    0 < firstChoiceMissProb C.algorithm.law C.algorithm.centerFirst
  human_center_miss_pos :
    0 < firstChoiceMissProb C.human.law C.human.centerFirst
  center_collision_diff_pos :
    0 < firstChoiceCollisionDiff C.algorithm.law C.human.law C.human.centerFirst

/--
An even closer-to-the-paper version of the center certificate.

This packages the probability inequalities that one would usually try to prove
from explicit Mallows formulas:

- the common center candidate is not chosen first with probability one, under
  either law;
- the better law assigns that candidate strictly more first-choice probability
  than the worse law;
- all candidatewise summands are nonnegative.

The conversion to `CenterPositiveCertificate` is purely algebraic.
-/
structure CenterProbabilityCertificate (value : Candidate n → ℝ) : Prop where
  strictly_center_ordered : C.StrictlyCenterOrdered value
  algorithm_nonneg :
    ∀ c : Candidate n,
      0 ≤ firstChoiceMissProb C.algorithm.law c *
        firstChoiceGapMass C.algorithm.law value c
  human_nonneg :
    ∀ c : Candidate n,
      0 ≤ firstChoiceMissProb C.human.law c *
        firstChoiceGapMass C.human.law value c
  weaker_nonneg :
    ∀ c : Candidate n,
      0 ≤ firstChoiceCollisionDiff C.algorithm.law C.human.law c *
        firstChoiceGapMass C.human.law value c
  algorithm_center_firstProb_lt_one :
    firstChoiceProb C.algorithm.law C.algorithm.centerFirst < 1
  human_center_firstProb_lt_one :
    firstChoiceProb C.human.law C.human.centerFirst < 1
  center_firstProb_comparison :
    firstChoiceProb C.human.law C.human.centerFirst <
      firstChoiceProb C.algorithm.law C.human.centerFirst

/--
The Mallows-specific version of `CenterProbabilityCertificate`.

The two "center probability is below one" fields are now proved from Mallows
support, so this certificate only asks for the comparison and nonnegativity
facts that still depend on the paper's finite Mallows inequalities.
-/
structure CenterMallowsCertificate (value : Candidate n → ℝ) : Prop where
  strictly_center_ordered : C.StrictlyCenterOrdered value
  algorithm_nonneg :
    ∀ c : Candidate n,
      0 ≤ firstChoiceMissProb C.algorithm.law c *
        firstChoiceGapMass C.algorithm.law value c
  human_nonneg :
    ∀ c : Candidate n,
      0 ≤ firstChoiceMissProb C.human.law c *
        firstChoiceGapMass C.human.law value c
  weaker_nonneg :
    ∀ c : Candidate n,
      0 ≤ firstChoiceCollisionDiff C.algorithm.law C.human.law c *
        firstChoiceGapMass C.human.law value c
  center_firstProb_comparison :
    firstChoiceProb C.human.law C.human.centerFirst <
      firstChoiceProb C.algorithm.law C.human.centerFirst

/-- The Mallows support lemmas fill the missing below-one probability fields. -/
theorem centerProbabilityCertificate_of_centerMallowsCertificate
    {value : Candidate n → ℝ} (cert : C.CenterMallowsCertificate value) :
    C.CenterProbabilityCertificate value := by
  constructor
  · exact cert.strictly_center_ordered
  · exact cert.algorithm_nonneg
  · exact cert.human_nonneg
  · exact cert.weaker_nonneg
  · exact C.algorithm.centerFirstProb_lt_one
  · exact C.human.centerFirstProb_lt_one
  · exact cert.center_firstProb_comparison

/--
Build the Mallows certificate from gap-mass sign facts.  The miss-probability
factors are always nonnegative; the remaining hard finite inequalities are the
gap-mass signs and the weaker-competition product signs.
-/
theorem centerMallowsCertificate_of_gapMass_nonneg
    {value : Candidate n → ℝ}
    (hstrict : C.StrictlyCenterOrdered value)
    (halgorithm_gap :
      ∀ c : Candidate n, 0 ≤ firstChoiceGapMass C.algorithm.law value c)
    (hhuman_gap :
      ∀ c : Candidate n, 0 ≤ firstChoiceGapMass C.human.law value c)
    (hweaker :
      ∀ c : Candidate n,
        0 ≤ firstChoiceCollisionDiff C.algorithm.law C.human.law c *
          firstChoiceGapMass C.human.law value c)
    (hcenter :
      firstChoiceProb C.human.law C.human.centerFirst <
        firstChoiceProb C.algorithm.law C.human.centerFirst) :
    C.CenterMallowsCertificate value := by
  constructor
  · exact hstrict
  · intro c
    exact mul_nonneg (firstChoiceMissProb_nonneg (μ := C.algorithm.law) (c := c))
      (halgorithm_gap c)
  · intro c
    exact mul_nonneg (firstChoiceMissProb_nonneg (μ := C.human.law) (c := c))
      (hhuman_gap c)
  · exact hweaker
  · exact hcenter

/--
Stronger but convenient constructor: if the algorithm law has at least as much
first-choice mass as the human law candidatewise, then nonnegative human
gap-mass facts also close the weaker-competition product signs.
-/
theorem centerMallowsCertificate_of_gapMass_nonneg_and_collisionProb_le
    {value : Candidate n → ℝ}
    (hstrict : C.StrictlyCenterOrdered value)
    (halgorithm_gap :
      ∀ c : Candidate n, 0 ≤ firstChoiceGapMass C.algorithm.law value c)
    (hhuman_gap :
      ∀ c : Candidate n, 0 ≤ firstChoiceGapMass C.human.law value c)
    (hcollision :
      ∀ c : Candidate n,
        firstChoiceProb C.human.law c ≤ firstChoiceProb C.algorithm.law c)
    (hcenter :
      firstChoiceProb C.human.law C.human.centerFirst <
        firstChoiceProb C.algorithm.law C.human.centerFirst) :
    C.CenterMallowsCertificate value := by
  refine C.centerMallowsCertificate_of_gapMass_nonneg
    hstrict halgorithm_gap hhuman_gap ?_ hcenter
  intro c
  exact mul_nonneg
    ((firstChoiceCollisionDiff_nonneg_iff
      (μBetter := C.algorithm.law) (μWorse := C.human.law) (c := c)).2
      (hcollision c))
    (hhuman_gap c)

/--
First-choice probability comparisons can be proved at the Mallows
`firstWeight / partition` level.
-/
theorem firstChoiceProb_le_of_firstWeight_div_le
    (c : Candidate n)
    (hweight :
      C.human.firstWeight c / C.human.partition ≤
        C.algorithm.firstWeight c / C.algorithm.partition) :
    firstChoiceProb C.human.law c ≤ firstChoiceProb C.algorithm.law c := by
  rw [C.human.firstChoiceProb_eq_firstWeight_div_partition c]
  rw [C.algorithm.firstChoiceProb_eq_firstWeight_div_partition c]
  exact hweight

/--
The center first-choice strict comparison can also be proved using Mallows
first-choice weights.
-/
theorem centerFirstProb_lt_of_centerFirstWeight_div_lt
    (hweight :
      C.human.firstWeight C.human.centerFirst / C.human.partition <
        C.algorithm.firstWeight C.algorithm.centerFirst /
          C.algorithm.partition) :
    firstChoiceProb C.human.law C.human.centerFirst <
      firstChoiceProb C.algorithm.law C.human.centerFirst := by
  rw [C.human.centerFirstProb_eq]
  rw [C.algorithm.firstChoiceProb_eq_firstWeight_div_partition C.human.centerFirst]
  simpa [C.algorithm_centerFirst_eq_human_centerFirst] using hweight

/--
Mallows finite-sum certificate phrased at the unnormalized-weight level.

This is the right target for explicit finite Mallows algebra: prove
candidatewise gap-mass signs, prove `firstWeight / partition` monotonicity for
all first candidates, and prove strict improvement for the center first
candidate.
-/
structure CenterMallowsWeightCertificate (value : Candidate n → ℝ) : Prop where
  strictly_center_ordered : C.StrictlyCenterOrdered value
  algorithm_gap_nonneg :
    ∀ c : Candidate n, 0 ≤ firstChoiceGapMass C.algorithm.law value c
  human_gap_nonneg :
    ∀ c : Candidate n, 0 ≤ firstChoiceGapMass C.human.law value c
  collision_firstWeight_div_le :
    ∀ c : Candidate n,
      C.human.firstWeight c / C.human.partition ≤
        C.algorithm.firstWeight c / C.algorithm.partition
  center_firstWeight_div_lt :
    C.human.firstWeight C.human.centerFirst / C.human.partition <
      C.algorithm.firstWeight C.algorithm.centerFirst / C.algorithm.partition

/--
Weight-level Mallows finite inequalities instantiate the main Mallows
certificate.
-/
theorem centerMallowsCertificate_of_weightCertificate
    {value : Candidate n → ℝ}
    (cert : C.CenterMallowsWeightCertificate value) :
    C.CenterMallowsCertificate value := by
  refine C.centerMallowsCertificate_of_gapMass_nonneg_and_collisionProb_le
    cert.strictly_center_ordered
    cert.algorithm_gap_nonneg
    cert.human_gap_nonneg
    ?collision
    ?center
  · intro c
    exact C.firstChoiceProb_le_of_firstWeight_div_le c
      (cert.collision_firstWeight_div_le c)
  · exact C.centerFirstProb_lt_of_centerFirstWeight_div_lt
      cert.center_firstWeight_div_lt

/--
A probability-comparison certificate is enough to build the center-positive
certificate, so the remaining proof obligations can be phrased directly as
first-choice probability inequalities.
-/
theorem centerPositiveCertificate_of_centerProbabilityCertificate
    {value : Candidate n → ℝ} (cert : C.CenterProbabilityCertificate value) :
    C.CenterPositiveCertificate value := by
  constructor
  · exact cert.strictly_center_ordered
  · exact cert.algorithm_nonneg
  · exact cert.human_nonneg
  · exact cert.weaker_nonneg
  · exact (firstChoiceMissProb_pos_iff_firstChoiceProb_lt_one
      (μ := C.algorithm.law) (c := C.algorithm.centerFirst)).2
      cert.algorithm_center_firstProb_lt_one
  · exact (firstChoiceMissProb_pos_iff_firstChoiceProb_lt_one
      (μ := C.human.law) (c := C.human.centerFirst)).2
      cert.human_center_firstProb_lt_one
  · exact (firstChoiceCollisionDiff_pos_iff
      (μBetter := C.algorithm.law) (μWorse := C.human.law)
      (c := C.human.centerFirst)).2
      cert.center_firstProb_comparison

/--
The Mallows-specific certificate also yields the center-positive certificate
directly; Mallows support closes the below-one probability fields.
-/
theorem centerPositiveCertificate_of_centerMallowsCertificate
    {value : Candidate n → ℝ} (cert : C.CenterMallowsCertificate value) :
    C.CenterPositiveCertificate value :=
   C.centerPositiveCertificate_of_centerProbabilityCertificate
    (C.centerProbabilityCertificate_of_centerMallowsCertificate cert)

/--
A center-positive certificate is enough to build the candidate-sum certificate
used by the current Mallows Theorem-3 path.
-/
theorem candidateSumCertificate_of_centerPositiveCertificate
    {value : Candidate n → ℝ} (cert : C.CenterPositiveCertificate value) :
    C.CandidateSumCertificate value := by
  constructor
  · apply AppliedModelingLib.sum_univ_pos_of_pos_of_nonneg
      (f := fun c : Candidate n =>
        firstChoiceMissProb C.algorithm.law c *
          firstChoiceGapMass C.algorithm.law value c)
      (a₀ := C.algorithm.centerFirst)
    · exact mul_pos cert.algorithm_center_miss_pos
        (C.algorithm_centerGapMass_pos_of_strictlyCenterOrdered cert.strictly_center_ordered)
    · intro c
      exact cert.algorithm_nonneg c
  · apply AppliedModelingLib.sum_univ_pos_of_pos_of_nonneg
      (f := fun c : Candidate n =>
        firstChoiceMissProb C.human.law c *
          firstChoiceGapMass C.human.law value c)
      (a₀ := C.human.centerFirst)
    · exact mul_pos cert.human_center_miss_pos
        (C.human_centerGapMass_pos_of_strictlyCenterOrdered cert.strictly_center_ordered)
    · intro c
      exact cert.human_nonneg c
  · apply AppliedModelingLib.sum_univ_pos_of_pos_of_nonneg
      (f := fun c : Candidate n =>
        firstChoiceCollisionDiff C.algorithm.law C.human.law c *
          firstChoiceGapMass C.human.law value c)
      (a₀ := C.human.centerFirst)
    · exact mul_pos cert.center_collision_diff_pos
        (C.human_centerGapMass_pos_of_strictlyCenterOrdered cert.strictly_center_ordered)
    · intro c
      exact cert.weaker_nonneg c

/--
The center-positive certificate closes the current fixed-parameter Mallows target.
-/
theorem paperHypotheses_of_centerPositiveCertificate
    {value : Candidate n → ℝ} (cert : C.CenterPositiveCertificate value) :
    Model.PaperHypotheses (C.toModel value) :=
   C.paperHypotheses_of_candidateSumCertificate
    (C.candidateSumCertificate_of_centerPositiveCertificate cert)

/--
A probability-comparison certificate also yields the candidate-sum certificate.
-/
theorem candidateSumCertificate_of_centerProbabilityCertificate
    {value : Candidate n → ℝ} (cert : C.CenterProbabilityCertificate value) :
    C.CandidateSumCertificate value :=
   C.candidateSumCertificate_of_centerPositiveCertificate
    (C.centerPositiveCertificate_of_centerProbabilityCertificate cert)

/--
The Mallows-specific certificate is the preferred paper-facing interface for
the current Theorem-3 formalization path.
-/
theorem candidateSumCertificate_of_centerMallowsCertificate
    {value : Candidate n → ℝ} (cert : C.CenterMallowsCertificate value) :
    C.CandidateSumCertificate value :=
   C.candidateSumCertificate_of_centerPositiveCertificate
    (C.centerPositiveCertificate_of_centerMallowsCertificate cert)

/--
A probability-comparison certificate therefore closes the current fixed-parameter
Mallows target as well.
-/
theorem paperHypotheses_of_centerProbabilityCertificate
    {value : Candidate n → ℝ} (cert : C.CenterProbabilityCertificate value) :
    Model.PaperHypotheses (C.toModel value) :=
   C.paperHypotheses_of_centerPositiveCertificate
    (C.centerPositiveCertificate_of_centerProbabilityCertificate cert)

/--
Mallows-specific paper theorem: once the remaining finite Mallows inequalities
are supplied in `CenterMallowsCertificate`, the imported monoculture model
satisfies the paper hypotheses.
-/
theorem paperHypotheses_of_centerMallowsCertificate
    {value : Candidate n → ℝ} (cert : C.CenterMallowsCertificate value) :
    Model.PaperHypotheses (C.toModel value) :=
   C.paperHypotheses_of_centerPositiveCertificate
    (C.centerPositiveCertificate_of_centerMallowsCertificate cert)

end MallowsComparison

end KR21Monoculture

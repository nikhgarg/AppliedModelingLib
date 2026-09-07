import KR21Monoculture.ThreeFirmCardinalComposition
import Mathlib.Data.Fin.Tuple.Sort

open MeasureTheory
open scoped BigOperators

namespace KR21Monoculture

open AppliedModelingLib.SocialChoice.Ranking

/-!
# Candidate-identity bridge for the KR21 three-firm example

The finite computations use `0,1,2,3` as *true-rank* coordinates, with `0`
the highest value.  The paper instead starts with four IID cardinal values on
named candidates and draws Mallows rankings around the realized true order.

This file makes that relabeling explicit.  It samples raw values at candidate
identities, obtains the descending true-rank permutation from those values,
and transports a canonical relative Mallows ranking through that permutation.
The central pointwise identity is that selecting a true rank in the canonical
model selects the corresponding candidate identity in the source model and
receives the same cardinal value.  The resulting finite-law identities do not
assume an unproved independence statement about sorted values.
-/

/-- The realized descending true-rank order of four candidate identities.
`trueRank values r` is the identity whose cardinal value has rank `r` from
the top.  Ties are deterministically broken by the underlying finite index;
the product Uniform law gives those ties measure zero, but the pointwise
construction is total without using that fact. -/
noncomputable def sourceTrueRankOfValues
    (values : SourceFourCandidate -> ℝ) : Ranking 2 :=
  Fin.revPerm.trans (Tuple.sort values)

/-- Evaluating a raw candidate-identity value at its realized true rank is
exactly the reusable upper order statistic. -/
theorem sourceTrueRankOfValues_value_eq_upperOrderStatistic
    (values : SourceFourCandidate -> ℝ) (rank : SourceFourCandidate) :
    values (sourceTrueRankOfValues values rank) =
      AppliedModelingLib.Probability.upperOrderStatistic values rank := by
  rfl

/-- Transport a canonical relative ranking through a realized true-rank order.
The result is the candidate-identity ranking observed in the source model. -/
noncomputable def sourceObservedRanking
    (trueRank : Ranking 2) (relative : SourceFourRanking) : Ranking 2 :=
  (sourceFourRankingToRanking relative).trans trueRank

/-- The observed candidate-identity ranking reads the relative true rank at
each position and then maps that rank to its candidate identity. -/
theorem sourceObservedRanking_apply
    (trueRank : Ranking 2) (relative : SourceFourRanking)
    (position : SourceFourCandidate) :
    sourceObservedRanking trueRank relative position =
      trueRank (relative position) := by
  rfl

/-- The candidate-identity ranking transformation is a finite equivalence:
every identity ranking is one canonical relative ranking composed on the right
with the realized true-rank order. -/
noncomputable def sourceObservedRankingEquiv
    (trueRank : Ranking 2) : SourceFourRanking ≃ Ranking 2 :=
  sourceFourRankingEquivRanking.trans (rankingRightTransEquiv trueRank)

@[simp] theorem sourceObservedRankingEquiv_apply
    (trueRank : Ranking 2) (relative : SourceFourRanking) :
    sourceObservedRankingEquiv trueRank relative =
      sourceObservedRanking trueRank relative := by
  rfl

/-- Relative and candidate-identity Mallows distances agree exactly after the
true-rank relabeling. -/
theorem sourceObservedRanking_kendallTau
    (trueRank : Ranking 2) (relative : SourceFourRanking) :
    kendallTau trueRank (sourceObservedRanking trueRank relative) =
      sourceExecutableInversionCount relative := by
  rw [sourceObservedRanking, kendallTau_center_trans,
    ← sourceExecutableInversionCount_eq_kendallTau]

/-- The finite Mallows partition is invariant under changing from canonical
true-rank labels to an arbitrary candidate-identity center.  The proof is an
explicit reindexing of all twenty-four rankings. -/
theorem sourceExecutableMallowsPartition_cast_at_center
    (q : ℚ) (trueRank : Ranking 2) :
    ((sourceExecutableMallowsPartition q : ℚ) : ℝ) =
      mallowsPartition (q : ℝ) trueRank := by
  calc
    ((sourceExecutableMallowsPartition q : ℚ) : ℝ) =
        mallowsPartition (q : ℝ) (Equiv.refl (Candidate 2)) :=
      sourceExecutableMallowsPartition_cast q
    _ = ∑ relative : SourceFourRanking,
        mallowsWeight (q : ℝ) (Equiv.refl (Candidate 2))
          (sourceFourRankingToRanking relative) := by
      unfold mallowsPartition
      symm
      exact Equiv.sum_comp sourceFourRankingEquivRanking
        (fun ranking => mallowsWeight (q : ℝ) (Equiv.refl (Candidate 2)) ranking)
    _ = ∑ relative : SourceFourRanking,
        mallowsWeight (q : ℝ) trueRank
          (sourceObservedRanking trueRank relative) := by
      apply Finset.sum_congr rfl
      intro relative _
      unfold mallowsWeight
      rw [sourceObservedRanking, kendallTau_center_trans]
    _ = mallowsPartition (q : ℝ) trueRank := by
      unfold mallowsPartition
      exact Equiv.sum_comp (sourceObservedRankingEquiv trueRank)
        (fun ranking => mallowsWeight (q : ℝ) trueRank ranking)

/-- The actual packaged source PMF, when its relative ranking is transported
to candidate identities, has the normalized Mallows atom formula around the
realized true-rank center. -/
theorem sourceExecutableObservedMallowsPMF_apply_toReal
    (q : ℚ) (hq : 0 < q) (trueRank : Ranking 2)
    (relative : SourceFourRanking) :
    (sourceExecutableMallowsPMF q hq relative).toReal =
      mallowsWeight (q : ℝ) trueRank
        (sourceObservedRanking trueRank relative) /
        mallowsPartition (q : ℝ) trueRank := by
  rw [sourceExecutableMallowsPMF, PMF.ofFintype_apply,
    ENNReal.toReal_ofReal
      (sourceExecutableMallowsMass_cast_nonneg q hq relative)]
  unfold sourceExecutableMallowsMass
  rw [Rat.cast_div, sourceExecutableMallowsWeight_cast,
    sourceExecutableMallowsPartition_cast_at_center q trueRank]
  unfold mallowsWeight
  rw [sourceObservedRanking, kendallTau_center_trans]

/-- A ranking-valued version of the finite best-available selector. -/
def sourceBestAvailableRanking (ranking : Ranking 2)
    (selected : Finset SourceFourCandidate) : SourceFourCandidate :=
  if ranking 0 ∉ selected then ranking 0
  else if ranking 1 ∉ selected then ranking 1
  else if ranking 2 ∉ selected then ranking 2
  else ranking 3

/-- On the canonical source-ranking rows, the ranking-valued selector is the
existing executable selector. -/
theorem sourceBestAvailableRanking_of_sourceFourRanking
    (ranking : SourceFourRanking) (selected : Finset SourceFourCandidate) :
    sourceBestAvailableRanking (sourceFourRankingToRanking ranking) selected =
      sourceBestAvailable ranking selected := by
  rfl

/-- Transporting candidates by a permutation commutes with the best-available
operation.  This is a pointwise finite fact, not a probabilistic symmetry
assumption. -/
theorem sourceBestAvailableRanking_relabel
    (relabel : Ranking 2) (ranking : Ranking 2)
    (selected : Finset SourceFourCandidate) :
    sourceBestAvailableRanking (ranking.trans relabel)
      (selected.map relabel.toEmbedding) =
      relabel (sourceBestAvailableRanking ranking selected) := by
  simp [sourceBestAvailableRanking]
  split_ifs <;> rfl

/-- Sequential focal selection for arbitrary four-candidate permutation
rankings.  This is the candidate-identity version of the existing executable
three-step selector. -/
def sourceFocalSelectedCandidateRanking
    (rankings : SourceThreeFirm -> Ranking 2)
    (order : SourceFirmOrder) : SourceFourCandidate :=
  let c0 := sourceBestAvailableRanking (rankings (order 0)) ∅
  let c1 := sourceBestAvailableRanking (rankings (order 1)) {c0}
  let c2 := sourceBestAvailableRanking (rankings (order 2)) {c0, c1}
  if order 0 = 0 then c0
  else if order 1 = 0 then c1
  else c2

/-- The arbitrary-ranking selector specializes to the existing canonical
true-rank selector. -/
theorem sourceFocalSelectedCandidateRanking_canonical
    (usesAlgorithm : SourceThreeFirm -> Bool)
    (algorithm : SourceFourRanking)
    (human : SourceThreeFirm -> SourceFourRanking)
    (order : SourceFirmOrder) :
    sourceFocalSelectedCandidateRanking
      (fun firm => sourceFourRankingToRanking
        (if usesAlgorithm firm then algorithm else human firm)) order =
      sourceFocalSelectedCandidate usesAlgorithm algorithm human order := by
  simp only [sourceFocalSelectedCandidateRanking,
    sourceFocalSelectedCandidate]
  simp_rw [sourceBestAvailableRanking_of_sourceFourRanking]

/-- Candidate relabeling commutes with the full three-step sequential focal
selection. -/
theorem sourceFocalSelectedCandidateRanking_relabel
    (relabel : Ranking 2)
    (rankings : SourceThreeFirm -> Ranking 2)
    (order : SourceFirmOrder) :
    sourceFocalSelectedCandidateRanking
      (fun firm => (rankings firm).trans relabel) order =
      relabel (sourceFocalSelectedCandidateRanking rankings order) := by
  let c0 := sourceBestAvailableRanking (rankings (order 0)) ∅
  let c1 := sourceBestAvailableRanking (rankings (order 1)) {c0}
  let c2 := sourceBestAvailableRanking (rankings (order 2)) {c0, c1}
  have hc0 :
      sourceBestAvailableRanking ((rankings (order 0)).trans relabel) ∅ =
        relabel c0 := by
    simpa [c0] using
      (sourceBestAvailableRanking_relabel relabel (rankings (order 0)) ∅)
  have hc1 :
      sourceBestAvailableRanking ((rankings (order 1)).trans relabel)
        {relabel c0} = relabel c1 := by
    simpa [c1] using
      (sourceBestAvailableRanking_relabel relabel (rankings (order 1)) {c0})
  have hc2 :
      sourceBestAvailableRanking ((rankings (order 2)).trans relabel)
        {relabel c0, relabel c1} = relabel c2 := by
    simpa [c2] using
      (sourceBestAvailableRanking_relabel relabel (rankings (order 2)) {c0, c1})
  simp only [sourceFocalSelectedCandidateRanking]
  rw [hc0]
  rw [hc1]
  rw [hc2]
  split_ifs <;> rfl

/-- The canonical true-rank rankings used by the executable finite model,
viewed as library permutations. -/
noncomputable def sourceCanonicalProfileRankings
    (usesAlgorithm : SourceThreeFirm -> Bool)
    (algorithm : SourceFourRanking)
    (human : SourceThreeFirm -> SourceFourRanking) :
    SourceThreeFirm -> Ranking 2 :=
  fun firm => sourceFourRankingToRanking
    (if usesAlgorithm firm then algorithm else human firm)

/-- The candidate-identity rankings observed after transporting every relative
Mallows ranking through the realized true-rank order. -/
noncomputable def sourceObservedProfileRankings
    (trueRank : Ranking 2)
    (usesAlgorithm : SourceThreeFirm -> Bool)
    (algorithm : SourceFourRanking)
    (human : SourceThreeFirm -> SourceFourRanking) :
    SourceThreeFirm -> Ranking 2 :=
  fun firm => sourceObservedRanking trueRank
    (if usesAlgorithm firm then algorithm else human firm)

/-- The observed rankings are exactly a common candidate relabeling of the
canonical relative rankings. -/
theorem sourceObservedProfileRankings_eq_relabel
    (trueRank : Ranking 2)
    (usesAlgorithm : SourceThreeFirm -> Bool)
    (algorithm : SourceFourRanking)
    (human : SourceThreeFirm -> SourceFourRanking) :
    sourceObservedProfileRankings trueRank usesAlgorithm algorithm human =
      fun firm => (sourceCanonicalProfileRankings usesAlgorithm algorithm human firm).trans
        trueRank := by
  funext firm
  rfl

/-- Focal candidate identity selected by the paper's sequential procedure:
rankings are centered at the realized order of raw candidate values rather
than at the fixed canonical rank labels. -/
noncomputable def sourceIdentityFocalSelectedCandidate
    (values : SourceFourCandidate -> ℝ)
    (usesAlgorithm : SourceThreeFirm -> Bool)
    (algorithm : SourceFourRanking)
    (human : SourceThreeFirm -> SourceFourRanking)
    (order : SourceFirmOrder) : SourceFourCandidate :=
  sourceFocalSelectedCandidateRanking
    (sourceObservedProfileRankings (sourceTrueRankOfValues values)
      usesAlgorithm algorithm human) order

/-- Selection in the candidate-identity model is the true-rank selection from
the canonical model, transported through the value-induced true-rank order. -/
theorem sourceIdentityFocalSelectedCandidate_eq_relabel
    (values : SourceFourCandidate -> ℝ)
    (usesAlgorithm : SourceThreeFirm -> Bool)
    (algorithm : SourceFourRanking)
    (human : SourceThreeFirm -> SourceFourRanking)
    (order : SourceFirmOrder) :
    sourceIdentityFocalSelectedCandidate values usesAlgorithm algorithm human order =
      sourceTrueRankOfValues values
        (sourceFocalSelectedCandidate usesAlgorithm algorithm human order) := by
  unfold sourceIdentityFocalSelectedCandidate
  rw [sourceObservedProfileRankings_eq_relabel]
  rw [sourceFocalSelectedCandidateRanking_relabel]
  exact congrArg (sourceTrueRankOfValues values)
    (sourceFocalSelectedCandidateRanking_canonical
      usesAlgorithm algorithm human order)

/-- The realized cardinal utility of the candidate-identity selector equals
the upper order statistic of its canonical true-rank selection, pointwise in
the raw IID value sample. -/
noncomputable def sourceIdentityFocalUtility
    (values : SourceFourCandidate -> ℝ)
    (usesAlgorithm : SourceThreeFirm -> Bool)
    (algorithm : SourceFourRanking)
    (human : SourceThreeFirm -> SourceFourRanking)
    (order : SourceFirmOrder) : ℝ :=
  values (sourceIdentityFocalSelectedCandidate values usesAlgorithm algorithm human order)

theorem sourceIdentityFocalUtility_eq_canonical_upperOrderStatistic
    (values : SourceFourCandidate -> ℝ)
    (usesAlgorithm : SourceThreeFirm -> Bool)
    (algorithm : SourceFourRanking)
    (human : SourceThreeFirm -> SourceFourRanking)
    (order : SourceFirmOrder) :
    sourceIdentityFocalUtility values usesAlgorithm algorithm human order =
      AppliedModelingLib.Probability.upperOrderStatistic values
        (sourceFocalSelectedCandidate usesAlgorithm algorithm human order) := by
  unfold sourceIdentityFocalUtility
  rw [sourceIdentityFocalSelectedCandidate_eq_relabel]
  exact sourceTrueRankOfValues_value_eq_upperOrderStatistic values _

/-! ## Raw candidate-identity cardinal products -/

/-- The shared-AAA source utility, expressed with raw IID values at candidate
identities and observed rankings centered at their realized true order. -/
noncomputable def sourceAAACandidateIdentityUtility
    (outcome : (SourceFourRanking × SourceFirmOrder) × (Fin 4 -> ℝ)) : ℝ :=
  sourceIdentityFocalUtility outcome.2 sourceProfileAAA outcome.1.1
    (sourceSharedAlgorithmRankings outcome.1.1) outcome.1.2

/-- The HAA source utility with raw candidate-identity values. -/
noncomputable def sourceHAACandidateIdentityUtility
    (outcome : ((SourceFourRanking × SourceFourRanking) × SourceFirmOrder) ×
      (Fin 4 -> ℝ)) : ℝ :=
  sourceIdentityFocalUtility outcome.2 sourceProfileHAA outcome.1.1.1
    (sourceHumanRankings outcome.1.1.2 .r0123 .r0123) outcome.1.2

/-- The AAH source utility with raw candidate-identity values. -/
noncomputable def sourceAAHCandidateIdentityUtility
    (outcome : ((SourceFourRanking × SourceFourRanking) × SourceFirmOrder) ×
      (Fin 4 -> ℝ)) : ℝ :=
  sourceIdentityFocalUtility outcome.2 sourceProfileAAH outcome.1.1.1
    (sourceHumanRankings .r0123 .r0123 outcome.1.1.2) outcome.1.2

/-- The HAH source utility with raw candidate-identity values. -/
noncomputable def sourceHAHCandidateIdentityUtility
    (outcome : ((SourceFourRanking × (SourceFourRanking × SourceFourRanking)) ×
      SourceFirmOrder) × (Fin 4 -> ℝ)) : ℝ :=
  sourceIdentityFocalUtility outcome.2 sourceProfileHAH outcome.1.1.1
    (sourceHumanRankings outcome.1.1.2.1 .r0123 outcome.1.1.2.2) outcome.1.2

/-- The AHH source utility with raw candidate-identity values. -/
noncomputable def sourceAHHCandidateIdentityUtility
    (outcome : ((SourceFourRanking × (SourceFourRanking × SourceFourRanking)) ×
      SourceFirmOrder) × (Fin 4 -> ℝ)) : ℝ :=
  sourceIdentityFocalUtility outcome.2 sourceProfileAHH outcome.1.1.1
    (sourceHumanRankings .r0123 outcome.1.1.2.1 outcome.1.1.2.2) outcome.1.2

/-- The HHH source utility with raw candidate-identity values. -/
noncomputable def sourceHHHCandidateIdentityUtility
    (outcome : (((SourceFourRanking × SourceFourRanking) × SourceFourRanking) ×
      SourceFirmOrder) × (Fin 4 -> ℝ)) : ℝ :=
  sourceIdentityFocalUtility outcome.2 sourceProfileHHH .r0123
    (sourceHumanRankings outcome.1.1.1.1 outcome.1.1.1.2 outcome.1.1.2) outcome.1.2

/-- The raw candidate-identity AAA utility is pointwise the canonical
upper-order-statistic utility already used by the finite cardinal product. -/
theorem sourceAAACandidateIdentityUtility_eq_cardinalUtility
    (outcome : (SourceFourRanking × SourceFirmOrder) × (Fin 4 -> ℝ)) :
    sourceAAACandidateIdentityUtility outcome = sourceAAACardinalUtility outcome := by
  unfold sourceAAACandidateIdentityUtility sourceAAACardinalUtility
  rw [sourceIdentityFocalUtility_eq_canonical_upperOrderStatistic,
    sourceFourSelectedUniformUtilityOf_eq_upperOrderStatistic]
  rfl

theorem sourceHAACandidateIdentityUtility_eq_cardinalUtility
    (outcome : ((SourceFourRanking × SourceFourRanking) × SourceFirmOrder) ×
      (Fin 4 -> ℝ)) :
    sourceHAACandidateIdentityUtility outcome = sourceHAACardinalUtility outcome := by
  unfold sourceHAACandidateIdentityUtility sourceHAACardinalUtility
  rw [sourceIdentityFocalUtility_eq_canonical_upperOrderStatistic,
    sourceFourSelectedUniformUtilityOf_eq_upperOrderStatistic]
  rfl

theorem sourceAAHCandidateIdentityUtility_eq_cardinalUtility
    (outcome : ((SourceFourRanking × SourceFourRanking) × SourceFirmOrder) ×
      (Fin 4 -> ℝ)) :
    sourceAAHCandidateIdentityUtility outcome = sourceAAHCardinalUtility outcome := by
  unfold sourceAAHCandidateIdentityUtility sourceAAHCardinalUtility
  rw [sourceIdentityFocalUtility_eq_canonical_upperOrderStatistic,
    sourceFourSelectedUniformUtilityOf_eq_upperOrderStatistic]
  rfl

theorem sourceHAHCandidateIdentityUtility_eq_cardinalUtility
    (outcome : ((SourceFourRanking × (SourceFourRanking × SourceFourRanking)) ×
      SourceFirmOrder) × (Fin 4 -> ℝ)) :
    sourceHAHCandidateIdentityUtility outcome = sourceHAHCardinalUtility outcome := by
  unfold sourceHAHCandidateIdentityUtility sourceHAHCardinalUtility
  rw [sourceIdentityFocalUtility_eq_canonical_upperOrderStatistic,
    sourceFourSelectedUniformUtilityOf_eq_upperOrderStatistic]
  rfl

theorem sourceAHHCandidateIdentityUtility_eq_cardinalUtility
    (outcome : ((SourceFourRanking × (SourceFourRanking × SourceFourRanking)) ×
      SourceFirmOrder) × (Fin 4 -> ℝ)) :
    sourceAHHCandidateIdentityUtility outcome = sourceAHHCardinalUtility outcome := by
  unfold sourceAHHCandidateIdentityUtility sourceAHHCardinalUtility
  rw [sourceIdentityFocalUtility_eq_canonical_upperOrderStatistic,
    sourceFourSelectedUniformUtilityOf_eq_upperOrderStatistic]
  rfl

theorem sourceHHHCandidateIdentityUtility_eq_cardinalUtility
    (outcome : (((SourceFourRanking × SourceFourRanking) × SourceFourRanking) ×
      SourceFirmOrder) × (Fin 4 -> ℝ)) :
    sourceHHHCandidateIdentityUtility outcome = sourceHHHCardinalUtility outcome := by
  unfold sourceHHHCandidateIdentityUtility sourceHHHCardinalUtility
  rw [sourceIdentityFocalUtility_eq_canonical_upperOrderStatistic,
    sourceFourSelectedUniformUtilityOf_eq_upperOrderStatistic]
  rfl

/-- Every explicit source identity model has the exact previously computed
focal expected utility.  These are equalities of integrals over raw IID
candidate values and independently sampled relative ranking errors. -/
theorem sourceAAACandidateIdentityUtility_integral_eq_cast_direct :
    (∫ outcome, sourceAAACandidateIdentityUtility outcome
      ∂sourceAAACardinalProductLaw) =
      ((sourceDirectRankMeanExpectedAAA : ℚ) : ℝ) := by
  rw [show sourceAAACandidateIdentityUtility = sourceAAACardinalUtility by
    funext outcome
    exact sourceAAACandidateIdentityUtility_eq_cardinalUtility outcome]
  exact sourceAAACardinalUtility_integral_eq_cast_direct

theorem sourceHAACandidateIdentityUtility_integral_eq_cast_direct :
    (∫ outcome, sourceHAACandidateIdentityUtility outcome
      ∂sourceHAACardinalProductLaw) =
      ((sourceDirectRankMeanExpectedHAA : ℚ) : ℝ) := by
  rw [show sourceHAACandidateIdentityUtility = sourceHAACardinalUtility by
    funext outcome
    exact sourceHAACandidateIdentityUtility_eq_cardinalUtility outcome]
  exact sourceHAACardinalUtility_integral_eq_cast_direct

theorem sourceAAHCandidateIdentityUtility_integral_eq_cast_direct :
    (∫ outcome, sourceAAHCandidateIdentityUtility outcome
      ∂sourceAAHCardinalProductLaw) =
      ((sourceDirectRankMeanExpectedAAH : ℚ) : ℝ) := by
  rw [show sourceAAHCandidateIdentityUtility = sourceAAHCardinalUtility by
    funext outcome
    exact sourceAAHCandidateIdentityUtility_eq_cardinalUtility outcome]
  exact sourceAAHCardinalUtility_integral_eq_cast_direct

theorem sourceHAHCandidateIdentityUtility_integral_eq_cast_direct :
    (∫ outcome, sourceHAHCandidateIdentityUtility outcome
      ∂sourceHAHCardinalProductLaw) =
      ((sourceDirectRankMeanExpectedHAH : ℚ) : ℝ) := by
  rw [show sourceHAHCandidateIdentityUtility = sourceHAHCardinalUtility by
    funext outcome
    exact sourceHAHCandidateIdentityUtility_eq_cardinalUtility outcome]
  exact sourceHAHCardinalUtility_integral_eq_cast_direct

theorem sourceAHHCandidateIdentityUtility_integral_eq_cast_direct :
    (∫ outcome, sourceAHHCandidateIdentityUtility outcome
      ∂sourceAHHCardinalProductLaw) =
      ((sourceDirectRankMeanExpectedAHH : ℚ) : ℝ) := by
  rw [show sourceAHHCandidateIdentityUtility = sourceAHHCardinalUtility by
    funext outcome
    exact sourceAHHCandidateIdentityUtility_eq_cardinalUtility outcome]
  exact sourceAHHCardinalUtility_integral_eq_cast_direct

theorem sourceHHHCandidateIdentityUtility_integral_eq_cast_direct :
    (∫ outcome, sourceHHHCandidateIdentityUtility outcome
      ∂sourceHHHCardinalProductLaw) =
      ((sourceDirectRankMeanExpectedHHH : ℚ) : ℝ) := by
  rw [show sourceHHHCandidateIdentityUtility = sourceHHHCardinalUtility by
    funext outcome
    exact sourceHHHCandidateIdentityUtility_eq_cardinalUtility outcome]
  exact sourceHHHCardinalUtility_integral_eq_cast_direct

/-- In the raw candidate-identity source model, the focal firm strictly
prefers the shared algorithm at the AAA/HAA comparison point. -/
theorem sourceCandidateIdentity_AAA_gt_HAA :
    (∫ outcome, sourceHAACandidateIdentityUtility outcome
      ∂sourceHAACardinalProductLaw) <
      ∫ outcome, sourceAAACandidateIdentityUtility outcome
        ∂sourceAAACardinalProductLaw := by
  rw [sourceHAACandidateIdentityUtility_integral_eq_cast_direct,
    sourceAAACandidateIdentityUtility_integral_eq_cast_direct,
    sourceDirectRankMeanExpectedHAA_eq, sourceDirectRankMeanExpectedAAA_eq]
  norm_num

/-- In the raw candidate-identity source model, the focal firm strictly
prefers the shared algorithm at the AAH/HAH comparison point. -/
theorem sourceCandidateIdentity_AAH_gt_HAH :
    (∫ outcome, sourceHAHCandidateIdentityUtility outcome
      ∂sourceHAHCardinalProductLaw) <
      ∫ outcome, sourceAAHCandidateIdentityUtility outcome
        ∂sourceAAHCardinalProductLaw := by
  rw [sourceHAHCandidateIdentityUtility_integral_eq_cast_direct,
    sourceAAHCandidateIdentityUtility_integral_eq_cast_direct,
    sourceDirectRankMeanExpectedHAH_eq, sourceDirectRankMeanExpectedAAH_eq]
  norm_num

/-- In the raw candidate-identity source model, the focal firm strictly
prefers the shared algorithm at the AHH/HHH comparison point. -/
theorem sourceCandidateIdentity_AHH_gt_HHH :
    (∫ outcome, sourceHHHCandidateIdentityUtility outcome
      ∂sourceHHHCardinalProductLaw) <
      ∫ outcome, sourceAHHCandidateIdentityUtility outcome
        ∂sourceAHHCardinalProductLaw := by
  rw [sourceHHHCandidateIdentityUtility_integral_eq_cast_direct,
    sourceAHHCandidateIdentityUtility_integral_eq_cast_direct,
    sourceDirectRankMeanExpectedHHH_eq, sourceDirectRankMeanExpectedAHH_eq]
  norm_num

/-- The source candidate-identity experiment also has the reported focal
all-human advantage over all-algorithm play.  This is not yet a social-welfare
claim: that lift still needs cardinal firm-label symmetry. -/
theorem sourceCandidateIdentity_AAA_lt_HHH :
    (∫ outcome, sourceAAACandidateIdentityUtility outcome
      ∂sourceAAACardinalProductLaw) <
      ∫ outcome, sourceHHHCandidateIdentityUtility outcome
        ∂sourceHHHCardinalProductLaw := by
  rw [sourceAAACandidateIdentityUtility_integral_eq_cast_direct,
    sourceHHHCandidateIdentityUtility_integral_eq_cast_direct,
    sourceDirectRankMeanExpectedAAA_eq, sourceDirectRankMeanExpectedHHH_eq]
  norm_num

end KR21Monoculture

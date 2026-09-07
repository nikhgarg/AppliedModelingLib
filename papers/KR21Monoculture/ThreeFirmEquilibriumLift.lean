import KR21Monoculture.ThreeFirmCandidateIdentityBridge
import KR21Monoculture.ThreeFirmLabelSymmetry
import Mathlib.Probability.Distributions.Uniform

open MeasureTheory
open scoped BigOperators

namespace KR21Monoculture

open AppliedModelingLib.SocialChoice.Ranking

/-! The finite source input types carry their discrete sigma algebras in the
generic product experiment below. -/
local instance : MeasurableSpace SourceFourRanking := ⊤
local instance : MeasurableSingletonClass SourceFourRanking := ⟨fun _ => trivial⟩
local instance : MeasurableSpace SourceFirmPermutation := ⊤
local instance : MeasurableSingletonClass SourceFirmPermutation := ⟨fun _ => trivial⟩
local instance : MeasurableSpace (SourceThreeFirm -> SourceFourRanking) := ⊤
local instance : MeasurableSingletonClass (SourceThreeFirm -> SourceFourRanking) :=
  ⟨fun _ => trivial⟩

/-!
# Generic three-firm source experiment and profile equivariance

The six finite computations in `ThreeFirmCandidateIdentityBridge` are all
anchored at firm `0`.  This file puts those computations in the actual
three-firm source experiment: a shared algorithmic relative ranking,
independent human relative rankings, a uniform arrival permutation, and four
raw IID cardinal values.  It proves the relabeling facts needed to turn
focal-row certificates into statements about arbitrary firm labels.

The file deliberately separates that structural lift from the finite marginal
identifications which connect the generic experiment to the six already
computed focal rows.  Those identifications must be proved explicitly; profile
names alone are not evidence for them.
-/

/-! ## Arbitrary-firm sequential selection -/

/-- The true-rank selected by an arbitrary labeled firm after a complete
three-step sequential allocation. -/
def sourceFirmSelectedCandidate (focal : SourceThreeFirm)
    (rankings : SourceThreeFirm -> SourceFourRanking)
    (order : SourceFirmPermutation) : SourceFourCandidate :=
  let c0 := sourceBestAvailable (rankings (order 0)) ∅
  let c1 := sourceBestAvailable (rankings (order 1)) {c0}
  let c2 := sourceBestAvailable (rankings (order 2)) {c0, c1}
  if order 0 = focal then c0
  else if order 1 = focal then c1
  else c2

/-- The generic rank-mean evaluator from `ThreeFirmLabelSymmetry` is exactly
the order-statistic table at the selected true rank. -/
theorem sourceFirmUtility_eq_selectedRankMean
    (focal : SourceThreeFirm)
    (rankings : SourceThreeFirm -> SourceFourRanking)
    (order : SourceFirmPermutation) :
    sourceFirmUtility focal rankings order =
      sourceExpectedOrderStatisticValue
        (sourceFirmSelectedCandidate focal rankings order) := by
  by_cases hfirst : order 0 = focal
  · simp [sourceFirmUtility, sourceFirmSelectedCandidate, hfirst]
  · by_cases hsecond : order 1 = focal
    · simp [sourceFirmUtility, sourceFirmSelectedCandidate, hfirst, hsecond]
    · simp [sourceFirmUtility, sourceFirmSelectedCandidate, hfirst, hsecond]

/-- Firm-label relabeling does not change the selected true rank. -/
theorem sourceFirmSelectedCandidate_relabel
    (relabel : SourceFirmPermutation)
    (focal : SourceThreeFirm)
    (rankings : SourceThreeFirm -> SourceFourRanking)
    (order : SourceFirmPermutation) :
    sourceFirmSelectedCandidate (relabel focal)
        (sourceRelabelRankings relabel rankings) (order.trans relabel) =
      sourceFirmSelectedCandidate focal rankings order := by
  simp [sourceFirmSelectedCandidate, sourceRelabelRankings]

/-- A ranking-valued version of arbitrary-firm sequential selection. -/
def sourceFirmSelectedCandidateRanking (focal : SourceThreeFirm)
    (rankings : SourceThreeFirm -> Ranking 2)
    (order : SourceFirmPermutation) : SourceFourCandidate :=
  let c0 := sourceBestAvailableRanking (rankings (order 0)) ∅
  let c1 := sourceBestAvailableRanking (rankings (order 1)) {c0}
  let c2 := sourceBestAvailableRanking (rankings (order 2)) {c0, c1}
  if order 0 = focal then c0
  else if order 1 = focal then c1
  else c2

/-- The ranking-valued selector agrees with the executable relative-ranking
selector after converting the named source rankings. -/
theorem sourceFirmSelectedCandidateRanking_canonical
    (focal : SourceThreeFirm)
    (rankings : SourceThreeFirm -> SourceFourRanking)
    (order : SourceFirmPermutation) :
    sourceFirmSelectedCandidateRanking focal
        (fun firm => sourceFourRankingToRanking (rankings firm)) order =
      sourceFirmSelectedCandidate focal rankings order := by
  simp [sourceFirmSelectedCandidateRanking, sourceFirmSelectedCandidate,
    sourceBestAvailableRanking_of_sourceFourRanking]

/-- Candidate relabeling commutes with arbitrary-firm sequential selection. -/
theorem sourceFirmSelectedCandidateRanking_candidate_relabel
    (candidateRelabel : Ranking 2)
    (focal : SourceThreeFirm)
    (rankings : SourceThreeFirm -> Ranking 2)
    (order : SourceFirmPermutation) :
    sourceFirmSelectedCandidateRanking focal
        (fun firm => (rankings firm).trans candidateRelabel) order =
      candidateRelabel
        (sourceFirmSelectedCandidateRanking focal rankings order) := by
  let c0 := sourceBestAvailableRanking (rankings (order 0)) ∅
  let c1 := sourceBestAvailableRanking (rankings (order 1)) {c0}
  let c2 := sourceBestAvailableRanking (rankings (order 2)) {c0, c1}
  have hc0 :
      sourceBestAvailableRanking ((rankings (order 0)).trans candidateRelabel) ∅ =
        candidateRelabel c0 := by
    simpa [c0] using
      (sourceBestAvailableRanking_relabel candidateRelabel (rankings (order 0)) ∅)
  have hc1 :
      sourceBestAvailableRanking ((rankings (order 1)).trans candidateRelabel)
        {candidateRelabel c0} = candidateRelabel c1 := by
    simpa [c1] using
      (sourceBestAvailableRanking_relabel candidateRelabel (rankings (order 1)) {c0})
  have hc2 :
      sourceBestAvailableRanking ((rankings (order 2)).trans candidateRelabel)
        {candidateRelabel c0, candidateRelabel c1} = candidateRelabel c2 := by
    simpa [c2] using
      (sourceBestAvailableRanking_relabel candidateRelabel (rankings (order 2)) {c0, c1})
  simp only [sourceFirmSelectedCandidateRanking]
  rw [hc0, hc1, hc2]
  split_ifs <;> rfl

/-- The observed candidate-identity rankings for an arbitrary strategy
profile.  Relative Mallows errors are transported through the true ordering of
the raw IID cardinal sample. -/
noncomputable def sourceObservedFirmProfileRankings
    (values : SourceFourCandidate -> ℝ)
    (usesAlgorithm : SourceThreeFirm -> Bool)
    (algorithm : SourceFourRanking)
    (human : SourceThreeFirm -> SourceFourRanking) :
    SourceThreeFirm -> Ranking 2 :=
  fun firm => sourceObservedRanking (sourceTrueRankOfValues values)
    (if usesAlgorithm firm then algorithm else human firm)

/-- The raw candidate identity selected by an arbitrary firm in the source
experiment. -/
noncomputable def sourceIdentityFirmSelectedCandidate
    (values : SourceFourCandidate -> ℝ)
    (focal : SourceThreeFirm)
    (usesAlgorithm : SourceThreeFirm -> Bool)
    (algorithm : SourceFourRanking)
    (human : SourceThreeFirm -> SourceFourRanking)
    (order : SourceFirmPermutation) : SourceFourCandidate :=
  sourceFirmSelectedCandidateRanking focal
    (sourceObservedFirmProfileRankings values usesAlgorithm algorithm human) order

/-- The source candidate-identity selector is exactly the canonical true-rank
selection transported through the realized ordering of raw values. -/
theorem sourceIdentityFirmSelectedCandidate_eq_relabel
    (values : SourceFourCandidate -> ℝ)
    (focal : SourceThreeFirm)
    (usesAlgorithm : SourceThreeFirm -> Bool)
    (algorithm : SourceFourRanking)
    (human : SourceThreeFirm -> SourceFourRanking)
    (order : SourceFirmPermutation) :
    sourceIdentityFirmSelectedCandidate values focal usesAlgorithm algorithm human order =
      sourceTrueRankOfValues values
        (sourceFirmSelectedCandidate focal
          (sourceProfileRankings usesAlgorithm algorithm human) order) := by
  unfold sourceIdentityFirmSelectedCandidate sourceObservedFirmProfileRankings
  rw [show (fun firm =>
      sourceObservedRanking (sourceTrueRankOfValues values)
        (if usesAlgorithm firm then algorithm else human firm)) =
      fun firm => (sourceFourRankingToRanking
        (if usesAlgorithm firm then algorithm else human firm)).trans
          (sourceTrueRankOfValues values) by
      funext firm
      rfl]
  rw [sourceFirmSelectedCandidateRanking_candidate_relabel]
  exact congrArg (sourceTrueRankOfValues values)
    (sourceFirmSelectedCandidateRanking_canonical focal
      (sourceProfileRankings usesAlgorithm algorithm human) order)

/-- Raw cardinal utility received by an arbitrary labeled firm. -/
noncomputable def sourceIdentityFirmUtility
    (values : SourceFourCandidate -> ℝ)
    (focal : SourceThreeFirm)
    (usesAlgorithm : SourceThreeFirm -> Bool)
    (algorithm : SourceFourRanking)
    (human : SourceThreeFirm -> SourceFourRanking)
    (order : SourceFirmPermutation) : ℝ :=
  values (sourceIdentityFirmSelectedCandidate values focal usesAlgorithm algorithm human order)

/-- Pointwise bridge from the actual raw candidate-identity payoff to the
canonical upper-order-statistic payoff. -/
theorem sourceIdentityFirmUtility_eq_canonical_upperOrderStatistic
    (values : SourceFourCandidate -> ℝ)
    (focal : SourceThreeFirm)
    (usesAlgorithm : SourceThreeFirm -> Bool)
    (algorithm : SourceFourRanking)
    (human : SourceThreeFirm -> SourceFourRanking)
    (order : SourceFirmPermutation) :
    sourceIdentityFirmUtility values focal usesAlgorithm algorithm human order =
      AppliedModelingLib.Probability.upperOrderStatistic values
        (sourceFirmSelectedCandidate focal
          (sourceProfileRankings usesAlgorithm algorithm human) order) := by
  unfold sourceIdentityFirmUtility
  rw [sourceIdentityFirmSelectedCandidate_eq_relabel]
  exact sourceTrueRankOfValues_value_eq_upperOrderStatistic values _

/-- Firm-label relabeling preserves raw candidate-identity utility pointwise.
Candidate values and relative ranking draws are not renamed; only the firm
which receives each ranking and the arrival labels are transported. -/
theorem sourceIdentityFirmUtility_relabel
    (relabel : SourceFirmPermutation)
    (values : SourceFourCandidate -> ℝ)
    (focal : SourceThreeFirm)
    (usesAlgorithm : SourceThreeFirm -> Bool)
    (algorithm : SourceFourRanking)
    (human : SourceThreeFirm -> SourceFourRanking)
    (order : SourceFirmPermutation) :
    sourceIdentityFirmUtility values (relabel focal)
        (sourceRelabelProfile relabel usesAlgorithm) algorithm
        (sourceRelabelRankings relabel human) (order.trans relabel) =
      sourceIdentityFirmUtility values focal usesAlgorithm algorithm human order := by
  rw [sourceIdentityFirmUtility_eq_canonical_upperOrderStatistic,
    sourceIdentityFirmUtility_eq_canonical_upperOrderStatistic,
    sourceProfileRankings_relabel,
    sourceFirmSelectedCandidate_relabel]

/-! ## Generic profile source law -/

/-- Placeholder law for an unused human-ranking coordinate.  It is a genuine
point mass, rather than an unmentioned discarded random input. -/
noncomputable def sourceInactiveHumanRankingLaw : PMF SourceFourRanking :=
  PMF.pure .r0123

/-- A firm receives an independent human relative ranking exactly when its
profile entry is `false`; algorithm users carry only the inert placeholder
coordinate because the shared algorithm ranking is sampled separately. -/
noncomputable def sourceProfileHumanCoordinateLaw (usesAlgorithm : Bool) :
    PMF SourceFourRanking :=
  if usesAlgorithm then sourceInactiveHumanRankingLaw else sourceHumanRankingLaw

/-- The independent profile-indexed human-ranking law.  This is the source
law for all three human coordinates, including deterministic placeholders for
firms which select the shared algorithm. -/
noncomputable def sourceProfileHumanRankingLaw
    (usesAlgorithm : SourceThreeFirm -> Bool) :
    PMF (SourceThreeFirm -> SourceFourRanking) :=
  PMF.ofFintype
    (fun human => ∏ firm : SourceThreeFirm,
      sourceProfileHumanCoordinateLaw (usesAlgorithm firm) (human firm))
    (by
      rw [← Fintype.prod_sum]
      apply Finset.prod_eq_one
      intro firm _
      simpa only [tsum_fintype] using
        (sourceProfileHumanCoordinateLaw (usesAlgorithm firm)).tsum_coe)

/-- Explicit equivalence between the tuple presentation used by the existing
finite witnesses and a human-ranking profile indexed by firm label. -/
noncomputable def sourceHumanRankingsEquiv :
    ((SourceFourRanking × SourceFourRanking) × SourceFourRanking) ≃
      (SourceThreeFirm -> SourceFourRanking) where
  toFun h := sourceHumanRankings h.1.1 h.1.2 h.2
  invFun human := ((human 0, human 1), human 2)
  left_inv h := by
    rcases h with ⟨⟨h0, h1⟩, h2⟩
    simp [sourceHumanRankings]
  right_inv human := by
    funext firm
    fin_cases firm <;> simp [sourceHumanRankings]

@[simp] theorem sourceHumanRankingsEquiv_apply
    (h0 h1 h2 : SourceFourRanking) :
    sourceHumanRankingsEquiv ((h0, h1), h2) =
      sourceHumanRankings h0 h1 h2 := rfl

/-- The atom formula for the profile-indexed independent human law. -/
@[simp] theorem sourceProfileHumanRankingLaw_apply
    (usesAlgorithm : SourceThreeFirm -> Bool)
    (human : SourceThreeFirm -> SourceFourRanking) :
    sourceProfileHumanRankingLaw usesAlgorithm human =
      ∏ firm : SourceThreeFirm,
        sourceProfileHumanCoordinateLaw (usesAlgorithm firm) (human firm) := rfl

/-- Tuple-coordinate formula for the profile-indexed human PMF. -/
theorem sourceProfileHumanRankingLaw_apply_sourceHumanRankings
    (usesAlgorithm : SourceThreeFirm -> Bool)
    (h0 h1 h2 : SourceFourRanking) :
    sourceProfileHumanRankingLaw usesAlgorithm
        (sourceHumanRankings h0 h1 h2) =
      sourceProfileHumanCoordinateLaw (usesAlgorithm 0) h0 *
        sourceProfileHumanCoordinateLaw (usesAlgorithm 1) h1 *
          sourceProfileHumanCoordinateLaw (usesAlgorithm 2) h2 := by
  classical
  rw [sourceProfileHumanRankingLaw_apply]
  have huniv : (Finset.univ : Finset SourceThreeFirm) = {0, 1, 2} := by
    ext firm
    fin_cases firm <;> simp
  rw [huniv]
  simp [sourceHumanRankings, mul_assoc]

/-- Reindexing firms transports the actual independent human product law,
not merely the payoff expression. -/
theorem sourceProfileHumanRankingLaw_relabel_apply
    (relabel : SourceFirmPermutation)
    (usesAlgorithm : SourceThreeFirm -> Bool)
    (human : SourceThreeFirm -> SourceFourRanking) :
    sourceProfileHumanRankingLaw (sourceRelabelProfile relabel usesAlgorithm)
        (sourceRelabelRankings relabel human) =
      sourceProfileHumanRankingLaw usesAlgorithm human := by
  simp only [sourceProfileHumanRankingLaw_apply, sourceRelabelProfile,
    sourceRelabelRankings]
  simpa using Equiv.prod_comp relabel.symm
    (fun firm => sourceProfileHumanCoordinateLaw
      (usesAlgorithm firm) (human firm))

/-- Uniform law on the actual six permutations of the three firm labels. -/
noncomputable def sourceUniformFirmPermutationLaw : PMF SourceFirmPermutation :=
  PMF.uniformOfFintype SourceFirmPermutation

/-- Every firm-arrival permutation has literal source mass `1/6`. -/
theorem sourceUniformFirmPermutationLaw_apply
    (order : SourceFirmPermutation) :
    (sourceUniformFirmPermutationLaw order).toReal =
      ((sourceUniformFirmOrderMass : ℚ) : ℝ) := by
  rw [sourceUniformFirmPermutationLaw, PMF.uniformOfFintype_apply]
  norm_num [Fintype.card_perm, sourceUniformFirmOrderMass]

/-- Full finite input law for a strategy profile: one shared algorithmic
relative ranking, the independent profile-indexed human rankings, and an
independent uniform arrival permutation. -/
noncomputable def sourceProfileInputLaw
    (usesAlgorithm : SourceThreeFirm -> Bool) :
    PMF ((SourceFourRanking × (SourceThreeFirm -> SourceFourRanking)) ×
      SourceFirmPermutation) :=
  sourceFinitePMFProduct
    (sourceFinitePMFProduct sourceAlgorithmRankingLaw
      (sourceProfileHumanRankingLaw usesAlgorithm))
    sourceUniformFirmPermutationLaw

/-- The complete source law adds four raw IID Uniform candidate values,
independently of all relative Mallows errors and the arrival permutation. -/
noncomputable def sourceProfileCandidateIdentityLaw
    (usesAlgorithm : SourceThreeFirm -> Bool) :
    Measure (((SourceFourRanking × (SourceThreeFirm -> SourceFourRanking)) ×
      SourceFirmPermutation) × (Fin 4 -> ℝ)) :=
  (sourceProfileInputLaw usesAlgorithm).toMeasure.prod sourceFourUniformValueLaw

/-- The canonical true-rank selected by a firm from one generic finite source
input realization. -/
def sourceProfileSelectedRank
    (usesAlgorithm : SourceThreeFirm -> Bool)
    (focal : SourceThreeFirm)
    (input : (SourceFourRanking × (SourceThreeFirm -> SourceFourRanking)) ×
      SourceFirmPermutation) : SourceFourCandidate :=
  sourceFirmSelectedCandidate focal
    (sourceProfileRankings usesAlgorithm input.1.1 input.1.2) input.2

/-- The actual raw candidate-identity utility in the generic profile source
experiment. -/
noncomputable def sourceProfileCandidateIdentityUtility
    (usesAlgorithm : SourceThreeFirm -> Bool)
    (focal : SourceThreeFirm)
    (outcome : ((SourceFourRanking × (SourceThreeFirm -> SourceFourRanking)) ×
      SourceFirmPermutation) × (Fin 4 -> ℝ)) : ℝ :=
  sourceIdentityFirmUtility outcome.2 focal usesAlgorithm outcome.1.1.1
    outcome.1.1.2 outcome.1.2

/-- Pointwise identification of generic raw source utility with a selected
upper order statistic. -/
theorem sourceProfileCandidateIdentityUtility_eq_selectedUniformUtility
    (usesAlgorithm : SourceThreeFirm -> Bool)
    (focal : SourceThreeFirm)
    (outcome : ((SourceFourRanking × (SourceThreeFirm -> SourceFourRanking)) ×
      SourceFirmPermutation) × (Fin 4 -> ℝ)) :
    sourceProfileCandidateIdentityUtility usesAlgorithm focal outcome =
      sourceFourSelectedUniformUtilityOf
        (sourceProfileSelectedRank usesAlgorithm focal) outcome := by
  unfold sourceProfileCandidateIdentityUtility sourceProfileSelectedRank
  rw [sourceIdentityFirmUtility_eq_canonical_upperOrderStatistic,
    sourceFourSelectedUniformUtilityOf_eq_upperOrderStatistic]

/-- The generic raw candidate-identity expectation has the exact finite
selected-rank mixture form.  This proves the source model's independence
rather than assuming sorted values are independent of ranking errors. -/
theorem sourceProfileCandidateIdentityUtility_integral_eq_weighted_rankMean
    (usesAlgorithm : SourceThreeFirm -> Bool)
    (focal : SourceThreeFirm) :
    (∫ outcome, sourceProfileCandidateIdentityUtility usesAlgorithm focal outcome
      ∂sourceProfileCandidateIdentityLaw usesAlgorithm) =
      ∑ input : (SourceFourRanking × (SourceThreeFirm -> SourceFourRanking)) ×
          SourceFirmPermutation,
        (sourceProfileInputLaw usesAlgorithm input).toReal *
          (sourceExpectedOrderStatisticValue
            (sourceProfileSelectedRank usesAlgorithm focal input) : ℝ) := by
  rw [show sourceProfileCandidateIdentityUtility usesAlgorithm focal =
      sourceFourSelectedUniformUtilityOf
        (sourceProfileSelectedRank usesAlgorithm focal) by
      funext outcome
      exact sourceProfileCandidateIdentityUtility_eq_selectedUniformUtility
        usesAlgorithm focal outcome]
  exact sourceFourSelectedUniformUtilityOf_integral_eq_weighted_table
    (sourceProfileInputLaw usesAlgorithm)
    (sourceProfileSelectedRank usesAlgorithm focal)

/-- The finite equivalence which relabels the human-ranking coordinates and
the arrival permutation while leaving the shared algorithm coordinate fixed. -/
noncomputable def sourceProfileInputRelabelEquiv
    (relabel : SourceFirmPermutation) :
    ((SourceFourRanking × (SourceThreeFirm -> SourceFourRanking)) ×
      SourceFirmPermutation) ≃
      ((SourceFourRanking × (SourceThreeFirm -> SourceFourRanking)) ×
        SourceFirmPermutation) :=
  Equiv.prodCongr
    (Equiv.prodCongr (Equiv.refl SourceFourRanking)
      (sourceRelabelRankingsEquiv relabel))
    (Equiv.mulLeft relabel)

@[simp] theorem sourceProfileInputRelabelEquiv_apply
    (relabel : SourceFirmPermutation)
    (input : (SourceFourRanking × (SourceThreeFirm -> SourceFourRanking)) ×
      SourceFirmPermutation) :
    sourceProfileInputRelabelEquiv relabel input =
      ((input.1.1, sourceRelabelRankings relabel input.1.2),
        input.2.trans relabel) := by
  rfl

/-- The full finite input law is invariant under firm relabeling.  In
particular, this checks both the iid human product and uniform arrival law. -/
theorem sourceProfileInputLaw_relabel_apply
    (relabel : SourceFirmPermutation)
    (usesAlgorithm : SourceThreeFirm -> Bool)
    (input : (SourceFourRanking × (SourceThreeFirm -> SourceFourRanking)) ×
      SourceFirmPermutation) :
    sourceProfileInputLaw (sourceRelabelProfile relabel usesAlgorithm)
        (sourceProfileInputRelabelEquiv relabel input) =
      sourceProfileInputLaw usesAlgorithm input := by
  rcases input with ⟨⟨algorithm, human⟩, order⟩
  simp only [sourceProfileInputRelabelEquiv_apply]
  simp only [sourceProfileInputLaw, sourceFinitePMFProduct_apply]
  rw [sourceProfileHumanRankingLaw_relabel_apply]
  simp [sourceUniformFirmPermutationLaw, PMF.uniformOfFintype_apply]

/-- The selected true rank is equivariant under a firm relabeling of the full
source input. -/
theorem sourceProfileSelectedRank_relabel
    (relabel : SourceFirmPermutation)
    (usesAlgorithm : SourceThreeFirm -> Bool)
    (focal : SourceThreeFirm)
    (input : (SourceFourRanking × (SourceThreeFirm -> SourceFourRanking)) ×
      SourceFirmPermutation) :
    sourceProfileSelectedRank (sourceRelabelProfile relabel usesAlgorithm)
        (relabel focal) (sourceProfileInputRelabelEquiv relabel input) =
      sourceProfileSelectedRank usesAlgorithm focal input := by
  rcases input with ⟨⟨algorithm, human⟩, order⟩
  simp only [sourceProfileInputRelabelEquiv_apply]
  unfold sourceProfileSelectedRank
  rw [sourceProfileRankings_relabel, sourceFirmSelectedCandidate_relabel]

/-- The expected raw cardinal utility of one firm in a complete profile source
experiment, written through its exact finite selected-rank mixture. -/
noncomputable def sourceProfileExpectedUtility
    (usesAlgorithm : SourceThreeFirm -> Bool)
    (focal : SourceThreeFirm) : ℝ :=
  ∑ input : (SourceFourRanking × (SourceThreeFirm -> SourceFourRanking)) ×
      SourceFirmPermutation,
    (sourceProfileInputLaw usesAlgorithm input).toReal *
      (sourceExpectedOrderStatisticValue
        (sourceProfileSelectedRank usesAlgorithm focal input) : ℝ)

/-- The raw candidate-identity integral is precisely the generic profile
expected utility. -/
theorem sourceProfileCandidateIdentityUtility_integral_eq_expectedUtility
    (usesAlgorithm : SourceThreeFirm -> Bool)
    (focal : SourceThreeFirm) :
    (∫ outcome, sourceProfileCandidateIdentityUtility usesAlgorithm focal outcome
      ∂sourceProfileCandidateIdentityLaw usesAlgorithm) =
      sourceProfileExpectedUtility usesAlgorithm focal := by
  exact sourceProfileCandidateIdentityUtility_integral_eq_weighted_rankMean
    usesAlgorithm focal

/-- Exact firm-label symmetry of expected raw candidate-identity utility for
every strategy profile.  This is a change of variables in the actual complete
source input law, not an assumption from the profile's spelling. -/
theorem sourceProfileExpectedUtility_relabel
    (relabel : SourceFirmPermutation)
    (usesAlgorithm : SourceThreeFirm -> Bool)
    (focal : SourceThreeFirm) :
    sourceProfileExpectedUtility (sourceRelabelProfile relabel usesAlgorithm)
        (relabel focal) =
      sourceProfileExpectedUtility usesAlgorithm focal := by
  unfold sourceProfileExpectedUtility
  rw [← Equiv.sum_comp (sourceProfileInputRelabelEquiv relabel)]
  apply Finset.sum_congr rfl
  intro input _
  rw [sourceProfileInputLaw_relabel_apply,
    sourceProfileSelectedRank_relabel]

/-! ## Permutation-indexed dominance and welfare certificates -/

/-- The three source focal comparisons, transported through every firm-label
permutation.  The rows have a direct game-theoretic interpretation:
`AAA/HAA` is a deviation against two algorithm users, `AAH/HAH` against one
algorithm and one human user, and `AHH/HHH` against two human users. -/
def sourcePermutationIndexedAlgorithmDominance : Prop :=
  (forall relabel : SourceFirmPermutation,
    sourceProfileExpectedUtility
        (sourceRelabelProfile relabel sourceProfileAAA) (relabel 0) >
      sourceProfileExpectedUtility
        (sourceRelabelProfile relabel sourceProfileHAA) (relabel 0)) /\
  (forall relabel : SourceFirmPermutation,
    sourceProfileExpectedUtility
        (sourceRelabelProfile relabel sourceProfileAAH) (relabel 0) >
      sourceProfileExpectedUtility
        (sourceRelabelProfile relabel sourceProfileHAH) (relabel 0)) /\
  (forall relabel : SourceFirmPermutation,
    sourceProfileExpectedUtility
        (sourceRelabelProfile relabel sourceProfileAHH) (relabel 0) >
      sourceProfileExpectedUtility
        (sourceRelabelProfile relabel sourceProfileHHH) (relabel 0))

/-- Focal-row strict comparisons are sufficient for all firm labels and all
three opponent-strategy patterns, once source-law equivariance has been
proved.  This theorem does not infer any comparison from the profile names:
each transported profile is stated explicitly. -/
theorem sourcePermutationIndexedAlgorithmDominance_of_focal_rows
    (hAA : sourceProfileExpectedUtility sourceProfileHAA 0 <
      sourceProfileExpectedUtility sourceProfileAAA 0)
    (hAH : sourceProfileExpectedUtility sourceProfileHAH 0 <
      sourceProfileExpectedUtility sourceProfileAAH 0)
    (hHH : sourceProfileExpectedUtility sourceProfileHHH 0 <
      sourceProfileExpectedUtility sourceProfileAHH 0) :
    sourcePermutationIndexedAlgorithmDominance := by
  constructor
  · intro relabel
    rw [sourceProfileExpectedUtility_relabel,
      sourceProfileExpectedUtility_relabel]
    exact hAA
  constructor
  · intro relabel
    rw [sourceProfileExpectedUtility_relabel,
      sourceProfileExpectedUtility_relabel]
    exact hAH
  · intro relabel
    rw [sourceProfileExpectedUtility_relabel,
      sourceProfileExpectedUtility_relabel]
    exact hHH

/-- Expected total selected candidate quality, defined as the sum of the
three firms' expected raw cardinal utilities in the common source experiment. -/
noncomputable def sourceProfileExpectedWelfare
    (usesAlgorithm : SourceThreeFirm -> Bool) : ℝ :=
  ∑ focal : SourceThreeFirm,
    sourceProfileExpectedUtility usesAlgorithm focal

/-- Atom formula for the generic profile input law. -/
theorem sourceProfileInputLaw_apply_toReal
    (usesAlgorithm : SourceThreeFirm -> Bool)
    (algorithm : SourceFourRanking)
    (human : SourceThreeFirm -> SourceFourRanking)
    (order : SourceFirmPermutation) :
    (sourceProfileInputLaw usesAlgorithm ((algorithm, human), order)).toReal =
      (sourceAlgorithmRankingLaw algorithm).toReal *
        (sourceProfileHumanRankingLaw usesAlgorithm human).toReal *
          (sourceUniformFirmPermutationLaw order).toReal := by
  rw [sourceProfileInputLaw, sourceFinitePMFProduct_apply_toReal,
    sourceFinitePMFProduct_apply_toReal]

/-- Expand generic expected utility into its three semantically distinct
finite input coordinates. -/
theorem sourceProfileExpectedUtility_eq_expanded_sum
    (usesAlgorithm : SourceThreeFirm -> Bool)
    (focal : SourceThreeFirm) :
    sourceProfileExpectedUtility usesAlgorithm focal =
      ∑ algorithm : SourceFourRanking,
        ∑ human : SourceThreeFirm -> SourceFourRanking,
          ∑ order : SourceFirmPermutation,
            (sourceAlgorithmRankingLaw algorithm).toReal *
              (sourceProfileHumanRankingLaw usesAlgorithm human).toReal *
                (sourceUniformFirmPermutationLaw order).toReal *
                  (sourceFirmUtility focal
                    (sourceProfileRankings usesAlgorithm algorithm human) order : ℝ) := by
  unfold sourceProfileExpectedUtility
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]
  simp_rw [sourceProfileInputLaw_apply_toReal]
  apply Finset.sum_congr rfl
  intro algorithm _
  apply Finset.sum_congr rfl
  intro human _
  apply Finset.sum_congr rfl
  intro order _
  unfold sourceProfileSelectedRank
  rw [← sourceFirmUtility_eq_selectedRankMean]

/-- For focal firm `0`, the generic permutation-valued arrival sum is exactly
the existing six-named-order source sum. -/
theorem sourceProfileExpectedUtility_zero_eq_namedOrder_sum
    (usesAlgorithm : SourceThreeFirm -> Bool) :
    sourceProfileExpectedUtility usesAlgorithm 0 =
      ∑ algorithm : SourceFourRanking,
        ∑ human : SourceThreeFirm -> SourceFourRanking,
          ∑ order : SourceFirmOrder,
            (sourceAlgorithmRankingLaw algorithm).toReal *
              (sourceProfileHumanRankingLaw usesAlgorithm human).toReal *
                ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                  (sourceFocalUtility usesAlgorithm algorithm human order : ℝ) := by
  rw [sourceProfileExpectedUtility_eq_expanded_sum]
  apply Finset.sum_congr rfl
  intro algorithm _
  apply Finset.sum_congr rfl
  intro human _
  symm
  refine Fintype.sum_bijective sourceFirmOrderToPermutation
    sourceFirmOrderToPermutation_bijective
    (fun order =>
      (sourceAlgorithmRankingLaw algorithm).toReal *
        (sourceProfileHumanRankingLaw usesAlgorithm human).toReal *
          ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
            (sourceFocalUtility usesAlgorithm algorithm human order : ℝ))
    (fun order =>
      (sourceAlgorithmRankingLaw algorithm).toReal *
        (sourceProfileHumanRankingLaw usesAlgorithm human).toReal *
          (sourceUniformFirmPermutationLaw order).toReal *
            (sourceFirmUtility 0
              (sourceProfileRankings usesAlgorithm algorithm human) order : ℝ)) ?_
  intro order
  change
    (sourceAlgorithmRankingLaw algorithm).toReal *
        (sourceProfileHumanRankingLaw usesAlgorithm human).toReal *
          ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
            (sourceFocalUtility usesAlgorithm algorithm human order : ℝ) =
      (sourceAlgorithmRankingLaw algorithm).toReal *
        (sourceProfileHumanRankingLaw usesAlgorithm human).toReal *
          (sourceUniformFirmPermutationLaw
            (sourceFirmOrderToPermutation order)).toReal *
            (sourceFirmUtility 0
              (sourceProfileRankings usesAlgorithm algorithm human)
              (sourceFirmOrderToPermutation order) : ℝ)
  rw [sourceUniformFirmPermutationLaw_apply,
    ← sourceFocalUtility_eq_sourceFirmUtility_zero]

/-! ## Finite inactive-coordinate projection -/

/-- Summing a real-valued finite expression against the inactive human
placeholder PMF evaluates it at the unique placeholder ranking. -/
theorem sourceInactiveHumanRankingLaw_weighted_sum
    (f : SourceFourRanking -> ℝ) :
    (∑ ranking : SourceFourRanking,
      (sourceInactiveHumanRankingLaw ranking).toReal * f ranking) =
      f .r0123 := by
  classical
  simp only [sourceInactiveHumanRankingLaw, PMF.pure_apply]
  rw [Finset.sum_eq_single .r0123]
  · simp
  · intro ranking _ hne
    simp [hne]
  · simp

/-- The profile human law at AAA is the product of three explicit inactive
point masses. -/
theorem sourceProfileHumanRankingLaw_AAA_apply
    (h0 h1 h2 : SourceFourRanking) :
    sourceProfileHumanRankingLaw sourceProfileAAA
        (sourceHumanRankings h0 h1 h2) =
      sourceInactiveHumanRankingLaw h0 * sourceInactiveHumanRankingLaw h1 *
        sourceInactiveHumanRankingLaw h2 := by
  simpa [sourceProfileHumanCoordinateLaw, sourceProfileAAA, mul_assoc] using
    sourceProfileHumanRankingLaw_apply_sourceHumanRankings
      sourceProfileAAA h0 h1 h2

/-- At AAA, no human coordinate affects the focal payoff. -/
theorem sourceFocalUtility_AAA_human_irrelevant
    (algorithm h0 h1 h2 : SourceFourRanking)
    (order : SourceFirmOrder) :
    sourceFocalUtility sourceProfileAAA algorithm
        (sourceHumanRankings h0 h1 h2) order =
      sourceFocalUtility sourceProfileAAA algorithm
        (sourceHumanRankings .r0123 .r0123 .r0123) order := by
  simp [sourceFocalUtility, sourceProfileAAA]

/-- Projection through the three inactive human coordinates at AAA.  The
statement is deliberately function-parametric, so later payoff calculations
cannot silently discard a coordinate without proving that it is inactive. -/
theorem sourceProfileHumanRankingLaw_AAA_weighted_sum
    (f : (SourceThreeFirm -> SourceFourRanking) -> ℝ) :
    (∑ human : SourceThreeFirm -> SourceFourRanking,
      (sourceProfileHumanRankingLaw sourceProfileAAA human).toReal * f human) =
      f (sourceHumanRankings .r0123 .r0123 .r0123) := by
  rw [← Equiv.sum_comp sourceHumanRankingsEquiv]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]
  simp_rw [sourceHumanRankingsEquiv_apply,
    sourceProfileHumanRankingLaw_AAA_apply, ENNReal.toReal_mul]
  calc
    (∑ h0 : SourceFourRanking, ∑ h1 : SourceFourRanking,
      ∑ h2 : SourceFourRanking,
        (sourceInactiveHumanRankingLaw h0).toReal *
            (sourceInactiveHumanRankingLaw h1).toReal *
              (sourceInactiveHumanRankingLaw h2).toReal *
                f (sourceHumanRankings h0 h1 h2)) =
        ∑ h0 : SourceFourRanking, ∑ h1 : SourceFourRanking,
          (sourceInactiveHumanRankingLaw h0).toReal *
            (sourceInactiveHumanRankingLaw h1).toReal *
              f (sourceHumanRankings h0 h1 .r0123) := by
          apply Finset.sum_congr rfl
          intro h0 _
          apply Finset.sum_congr rfl
          intro h1 _
          calc
            (∑ h2 : SourceFourRanking,
              (sourceInactiveHumanRankingLaw h0).toReal *
                  (sourceInactiveHumanRankingLaw h1).toReal *
                    (sourceInactiveHumanRankingLaw h2).toReal *
                      f (sourceHumanRankings h0 h1 h2)) =
                (sourceInactiveHumanRankingLaw h0).toReal *
                  (sourceInactiveHumanRankingLaw h1).toReal *
                    ∑ h2 : SourceFourRanking,
                      (sourceInactiveHumanRankingLaw h2).toReal *
                        f (sourceHumanRankings h0 h1 h2) := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro h2 _
                  ring
            _ = (sourceInactiveHumanRankingLaw h0).toReal *
                  (sourceInactiveHumanRankingLaw h1).toReal *
                    f (sourceHumanRankings h0 h1 .r0123) := by
                  rw [sourceInactiveHumanRankingLaw_weighted_sum]
    _ = ∑ h0 : SourceFourRanking,
          (sourceInactiveHumanRankingLaw h0).toReal *
            f (sourceHumanRankings h0 .r0123 .r0123) := by
          apply Finset.sum_congr rfl
          intro h0 _
          calc
            (∑ h1 : SourceFourRanking,
              (sourceInactiveHumanRankingLaw h0).toReal *
                  (sourceInactiveHumanRankingLaw h1).toReal *
                    f (sourceHumanRankings h0 h1 .r0123)) =
                (sourceInactiveHumanRankingLaw h0).toReal *
                  ∑ h1 : SourceFourRanking,
                    (sourceInactiveHumanRankingLaw h1).toReal *
                      f (sourceHumanRankings h0 h1 .r0123) := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro h1 _
                  ring
            _ = (sourceInactiveHumanRankingLaw h0).toReal *
                  f (sourceHumanRankings h0 .r0123 .r0123) := by
                  rw [sourceInactiveHumanRankingLaw_weighted_sum]
    _ = f (sourceHumanRankings .r0123 .r0123 .r0123) := by
          exact sourceInactiveHumanRankingLaw_weighted_sum
            (fun h0 => f (sourceHumanRankings h0 .r0123 .r0123))

/-- Collapse two inactive coordinates to the right of an arbitrary active
finite coordinate. -/
theorem sourceInactiveHumanRankingLaw_two_right_weighted_sum
    (a : SourceFourRanking -> ℝ)
    (f : SourceFourRanking -> SourceFourRanking -> SourceFourRanking -> ℝ) :
    (∑ h0 : SourceFourRanking, ∑ h1 : SourceFourRanking,
      ∑ h2 : SourceFourRanking,
        a h0 * (sourceInactiveHumanRankingLaw h1).toReal *
          (sourceInactiveHumanRankingLaw h2).toReal * f h0 h1 h2) =
      ∑ h0 : SourceFourRanking, a h0 * f h0 .r0123 .r0123 := by
  calc
    (∑ h0 : SourceFourRanking, ∑ h1 : SourceFourRanking,
      ∑ h2 : SourceFourRanking,
        a h0 * (sourceInactiveHumanRankingLaw h1).toReal *
          (sourceInactiveHumanRankingLaw h2).toReal * f h0 h1 h2) =
        ∑ h0 : SourceFourRanking, ∑ h1 : SourceFourRanking,
          a h0 * (sourceInactiveHumanRankingLaw h1).toReal *
            ∑ h2 : SourceFourRanking,
              (sourceInactiveHumanRankingLaw h2).toReal * f h0 h1 h2 := by
          apply Finset.sum_congr rfl
          intro h0 _
          apply Finset.sum_congr rfl
          intro h1 _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro h2 _
          ring
    _ = ∑ h0 : SourceFourRanking, ∑ h1 : SourceFourRanking,
          a h0 * (sourceInactiveHumanRankingLaw h1).toReal * f h0 h1 .r0123 := by
          apply Finset.sum_congr rfl
          intro h0 _
          apply Finset.sum_congr rfl
          intro h1 _
          rw [sourceInactiveHumanRankingLaw_weighted_sum]
    _ = ∑ h0 : SourceFourRanking,
          a h0 * ∑ h1 : SourceFourRanking,
            (sourceInactiveHumanRankingLaw h1).toReal * f h0 h1 .r0123 := by
          apply Finset.sum_congr rfl
          intro h0 _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro h1 _
          ring
    _ = ∑ h0 : SourceFourRanking, a h0 * f h0 .r0123 .r0123 := by
          apply Finset.sum_congr rfl
          intro h0 _
          rw [sourceInactiveHumanRankingLaw_weighted_sum]

/-- Collapse the inactive middle coordinate while retaining both outside
coordinates. -/
theorem sourceInactiveHumanRankingLaw_middle_weighted_sum
    (a b : SourceFourRanking -> ℝ)
    (f : SourceFourRanking -> SourceFourRanking -> SourceFourRanking -> ℝ) :
    (∑ h0 : SourceFourRanking, ∑ h1 : SourceFourRanking,
      ∑ h2 : SourceFourRanking,
        a h0 * (sourceInactiveHumanRankingLaw h1).toReal * b h2 * f h0 h1 h2) =
      ∑ h0 : SourceFourRanking, ∑ h2 : SourceFourRanking,
        a h0 * b h2 * f h0 .r0123 h2 := by
  calc
    (∑ h0 : SourceFourRanking, ∑ h1 : SourceFourRanking,
      ∑ h2 : SourceFourRanking,
        a h0 * (sourceInactiveHumanRankingLaw h1).toReal * b h2 * f h0 h1 h2) =
        ∑ h0 : SourceFourRanking, ∑ h2 : SourceFourRanking,
          ∑ h1 : SourceFourRanking,
            a h0 * (sourceInactiveHumanRankingLaw h1).toReal * b h2 * f h0 h1 h2 := by
          apply Finset.sum_congr rfl
          intro h0 _
          rw [Finset.sum_comm]
    _ = ∑ h0 : SourceFourRanking, ∑ h2 : SourceFourRanking,
          a h0 * b h2 * ∑ h1 : SourceFourRanking,
            (sourceInactiveHumanRankingLaw h1).toReal * f h0 h1 h2 := by
          apply Finset.sum_congr rfl
          intro h0 _
          apply Finset.sum_congr rfl
          intro h2 _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro h1 _
          ring
    _ = ∑ h0 : SourceFourRanking, ∑ h2 : SourceFourRanking,
          a h0 * b h2 * f h0 .r0123 h2 := by
          apply Finset.sum_congr rfl
          intro h0 _
          apply Finset.sum_congr rfl
          intro h2 _
          rw [sourceInactiveHumanRankingLaw_weighted_sum]

/-- Collapse the inactive left coordinate while retaining the two right
coordinates. -/
theorem sourceInactiveHumanRankingLaw_left_weighted_sum
    (b c : SourceFourRanking -> ℝ)
    (f : SourceFourRanking -> SourceFourRanking -> SourceFourRanking -> ℝ) :
    (∑ h0 : SourceFourRanking, ∑ h1 : SourceFourRanking,
      ∑ h2 : SourceFourRanking,
        (sourceInactiveHumanRankingLaw h0).toReal * b h1 * c h2 * f h0 h1 h2) =
      ∑ h1 : SourceFourRanking, ∑ h2 : SourceFourRanking,
        b h1 * c h2 * f .r0123 h1 h2 := by
  calc
    (∑ h0 : SourceFourRanking, ∑ h1 : SourceFourRanking,
      ∑ h2 : SourceFourRanking,
        (sourceInactiveHumanRankingLaw h0).toReal * b h1 * c h2 * f h0 h1 h2) =
        ∑ h1 : SourceFourRanking, ∑ h2 : SourceFourRanking,
          ∑ h0 : SourceFourRanking,
            (sourceInactiveHumanRankingLaw h0).toReal * b h1 * c h2 * f h0 h1 h2 := by
          calc
            (∑ h0 : SourceFourRanking, ∑ h1 : SourceFourRanking,
              ∑ h2 : SourceFourRanking,
                (sourceInactiveHumanRankingLaw h0).toReal * b h1 * c h2 * f h0 h1 h2) =
                ∑ h0 : SourceFourRanking, ∑ h2 : SourceFourRanking,
                  ∑ h1 : SourceFourRanking,
                    (sourceInactiveHumanRankingLaw h0).toReal * b h1 * c h2 * f h0 h1 h2 := by
                      apply Finset.sum_congr rfl
                      intro h0 _
                      rw [Finset.sum_comm]
            _ = ∑ h2 : SourceFourRanking, ∑ h0 : SourceFourRanking,
                  ∑ h1 : SourceFourRanking,
                    (sourceInactiveHumanRankingLaw h0).toReal * b h1 * c h2 * f h0 h1 h2 := by
                      rw [Finset.sum_comm]
            _ = ∑ h2 : SourceFourRanking, ∑ h1 : SourceFourRanking,
                  ∑ h0 : SourceFourRanking,
                    (sourceInactiveHumanRankingLaw h0).toReal * b h1 * c h2 * f h0 h1 h2 := by
                      apply Finset.sum_congr rfl
                      intro h2 _
                      rw [Finset.sum_comm]
            _ = ∑ h1 : SourceFourRanking, ∑ h2 : SourceFourRanking,
                  ∑ h0 : SourceFourRanking,
                    (sourceInactiveHumanRankingLaw h0).toReal * b h1 * c h2 * f h0 h1 h2 := by
                      rw [Finset.sum_comm]
    _ = ∑ h1 : SourceFourRanking, ∑ h2 : SourceFourRanking,
          b h1 * c h2 * ∑ h0 : SourceFourRanking,
            (sourceInactiveHumanRankingLaw h0).toReal * f h0 h1 h2 := by
          apply Finset.sum_congr rfl
          intro h1 _
          apply Finset.sum_congr rfl
          intro h2 _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro h0 _
          ring
    _ = ∑ h1 : SourceFourRanking, ∑ h2 : SourceFourRanking,
          b h1 * c h2 * f .r0123 h1 h2 := by
          apply Finset.sum_congr rfl
          intro h1 _
          apply Finset.sum_congr rfl
          intro h2 _
          rw [sourceInactiveHumanRankingLaw_weighted_sum]

/-- Collapse the two inactive left coordinates while retaining the right
coordinate. -/
theorem sourceInactiveHumanRankingLaw_two_left_weighted_sum
    (c : SourceFourRanking -> ℝ)
    (f : SourceFourRanking -> SourceFourRanking -> SourceFourRanking -> ℝ) :
    (∑ h0 : SourceFourRanking, ∑ h1 : SourceFourRanking,
      ∑ h2 : SourceFourRanking,
        (sourceInactiveHumanRankingLaw h0).toReal *
          (sourceInactiveHumanRankingLaw h1).toReal * c h2 * f h0 h1 h2) =
      ∑ h2 : SourceFourRanking, c h2 * f .r0123 .r0123 h2 := by
  calc
    (∑ h0 : SourceFourRanking, ∑ h1 : SourceFourRanking,
      ∑ h2 : SourceFourRanking,
        (sourceInactiveHumanRankingLaw h0).toReal *
          (sourceInactiveHumanRankingLaw h1).toReal * c h2 * f h0 h1 h2) =
        ∑ h1 : SourceFourRanking, ∑ h2 : SourceFourRanking,
          (sourceInactiveHumanRankingLaw h1).toReal * c h2 * f .r0123 h1 h2 := by
          simpa using sourceInactiveHumanRankingLaw_left_weighted_sum
            (fun h1 => (sourceInactiveHumanRankingLaw h1).toReal) c f
    _ = ∑ h2 : SourceFourRanking,
          c h2 * ∑ h1 : SourceFourRanking,
            (sourceInactiveHumanRankingLaw h1).toReal * f .r0123 h1 h2 := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro h2 _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro h1 _
          ring
    _ = ∑ h2 : SourceFourRanking, c h2 * f .r0123 .r0123 h2 := by
          apply Finset.sum_congr rfl
          intro h2 _
          rw [sourceInactiveHumanRankingLaw_weighted_sum]

/-- The surviving AAA placeholder profile induces exactly the direct
shared-algorithm conditional payoff used in the finite source witness. -/
theorem sourceFocalUtility_AAA_placeholder_eq_direct
    (algorithm : SourceFourRanking) (order : SourceFirmOrder) :
    sourceFocalUtility sourceProfileAAA algorithm
        (sourceHumanRankings .r0123 .r0123 .r0123) order =
      sourceDirectRankMeanConditionalAAA algorithm order := by
  simp [sourceDirectRankMeanConditionalAAA, sourceFocalUtility, sourceProfileAAA]

/-- The HAA profile law has one active human coordinate at focal firm `0` and
two explicit inactive point masses. -/
theorem sourceProfileHumanRankingLaw_HAA_apply
    (h0 h1 h2 : SourceFourRanking) :
    sourceProfileHumanRankingLaw sourceProfileHAA
        (sourceHumanRankings h0 h1 h2) =
      sourceHumanRankingLaw h0 * sourceInactiveHumanRankingLaw h1 *
        sourceInactiveHumanRankingLaw h2 := by
  simpa [sourceProfileHumanCoordinateLaw, sourceProfileHAA, mul_assoc] using
    sourceProfileHumanRankingLaw_apply_sourceHumanRankings
      sourceProfileHAA h0 h1 h2

/-- Project the two inactive HAA coordinates while retaining the focal human
ranking under its actual Mallows PMF. -/
theorem sourceProfileHumanRankingLaw_HAA_weighted_sum
    (f : (SourceThreeFirm -> SourceFourRanking) -> ℝ) :
    (∑ human : SourceThreeFirm -> SourceFourRanking,
      (sourceProfileHumanRankingLaw sourceProfileHAA human).toReal * f human) =
      ∑ h0 : SourceFourRanking,
        (sourceHumanRankingLaw h0).toReal *
          f (sourceHumanRankings h0 .r0123 .r0123) := by
  rw [← Equiv.sum_comp sourceHumanRankingsEquiv]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]
  simp_rw [sourceHumanRankingsEquiv_apply,
    sourceProfileHumanRankingLaw_HAA_apply, ENNReal.toReal_mul]
  exact sourceInactiveHumanRankingLaw_two_right_weighted_sum
    (fun h0 => (sourceHumanRankingLaw h0).toReal)
    (fun h0 h1 h2 => f (sourceHumanRankings h0 h1 h2))

/-- The generic focal HAA expectation is the existing one-human source PMF
expectation after explicit inactive-coordinate projection. -/
theorem sourceProfileExpectedUtility_HAA_zero_eq_cast_direct :
    sourceProfileExpectedUtility sourceProfileHAA 0 =
      ((sourceDirectRankMeanExpectedHAA : ℚ) : ℝ) := by
  rw [sourceProfileExpectedUtility_zero_eq_namedOrder_sum,
    ← sourceHAAProductLawExpectation_eq_cast_direct]
  unfold sourceHAAProductLawExpectation
  calc
    (∑ algorithm : SourceFourRanking,
      ∑ human : SourceThreeFirm -> SourceFourRanking,
        ∑ order : SourceFirmOrder,
          (sourceAlgorithmRankingLaw algorithm).toReal *
              (sourceProfileHumanRankingLaw sourceProfileHAA human).toReal *
                ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                  (sourceFocalUtility sourceProfileHAA algorithm human order : ℝ)) =
        ∑ algorithm : SourceFourRanking,
          ∑ order : SourceFirmOrder,
            ∑ human : SourceFourRanking,
              (sourceAlgorithmRankingLaw algorithm).toReal *
                ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                  ((sourceHumanRankingLaw human).toReal *
                    (sourceFocalUtility sourceProfileHAA algorithm
                      (sourceHumanRankings human .r0123 .r0123) order : ℝ)) := by
          apply Finset.sum_congr rfl
          intro algorithm _
          calc
            (∑ human : SourceThreeFirm -> SourceFourRanking,
              ∑ order : SourceFirmOrder,
                (sourceAlgorithmRankingLaw algorithm).toReal *
                    (sourceProfileHumanRankingLaw sourceProfileHAA human).toReal *
                      ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                        (sourceFocalUtility sourceProfileHAA algorithm human order : ℝ)) =
                ∑ order : SourceFirmOrder,
                  ∑ human : SourceThreeFirm -> SourceFourRanking,
                    (sourceAlgorithmRankingLaw algorithm).toReal *
                      ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                        ((sourceProfileHumanRankingLaw sourceProfileHAA human).toReal *
                          (sourceFocalUtility sourceProfileHAA algorithm human order : ℝ)) := by
                    rw [Finset.sum_comm]
                    apply Finset.sum_congr rfl
                    intro order _
                    apply Finset.sum_congr rfl
                    intro human _
                    ring
            _ = ∑ order : SourceFirmOrder,
                  ∑ human : SourceFourRanking,
                    (sourceAlgorithmRankingLaw algorithm).toReal *
                      ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                        ((sourceHumanRankingLaw human).toReal *
                          (sourceFocalUtility sourceProfileHAA algorithm
                            (sourceHumanRankings human .r0123 .r0123) order : ℝ)) := by
                    apply Finset.sum_congr rfl
                    intro order _
                    calc
                      (∑ human : SourceThreeFirm -> SourceFourRanking,
                        (sourceAlgorithmRankingLaw algorithm).toReal *
                          ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                          ((sourceProfileHumanRankingLaw sourceProfileHAA human).toReal *
                              (sourceFocalUtility sourceProfileHAA algorithm human order : ℝ))) =
                          (sourceAlgorithmRankingLaw algorithm).toReal *
                            ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                              ∑ human : SourceThreeFirm -> SourceFourRanking,
                                (sourceProfileHumanRankingLaw sourceProfileHAA human).toReal *
                                  (sourceFocalUtility sourceProfileHAA algorithm human order : ℝ) := by
                            exact (Finset.mul_sum
                              (Finset.univ : Finset (SourceThreeFirm -> SourceFourRanking))
                              (fun human =>
                                (sourceProfileHumanRankingLaw sourceProfileHAA human).toReal *
                                  (sourceFocalUtility sourceProfileHAA algorithm human order : ℝ))
                              ((sourceAlgorithmRankingLaw algorithm).toReal *
                                ((sourceUniformFirmOrderMass : ℚ) : ℝ))).symm
                      _ = (sourceAlgorithmRankingLaw algorithm).toReal *
                            ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                              ∑ human : SourceFourRanking,
                                (sourceHumanRankingLaw human).toReal *
                                  (sourceFocalUtility sourceProfileHAA algorithm
                                    (sourceHumanRankings human .r0123 .r0123) order : ℝ) := by
                            rw [sourceProfileHumanRankingLaw_HAA_weighted_sum]
                      _ = ∑ human : SourceFourRanking,
                            (sourceAlgorithmRankingLaw algorithm).toReal *
                              ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                                ((sourceHumanRankingLaw human).toReal *
                                  (sourceFocalUtility sourceProfileHAA algorithm
                                    (sourceHumanRankings human .r0123 .r0123) order : ℝ)) := by
                            exact Finset.mul_sum
                              (Finset.univ : Finset SourceFourRanking)
                              (fun human =>
                                (sourceHumanRankingLaw human).toReal *
                                  (sourceFocalUtility sourceProfileHAA algorithm
                                    (sourceHumanRankings human .r0123 .r0123) order : ℝ))
                              ((sourceAlgorithmRankingLaw algorithm).toReal *
                                ((sourceUniformFirmOrderMass : ℚ) : ℝ))
    _ = ∑ algorithm : SourceFourRanking,
          ∑ order : SourceFirmOrder,
            ∑ human : SourceFourRanking,
              (sourceOneHumanProductLaw ((algorithm, human), order)).toReal *
                (sourceFocalUtility sourceProfileHAA algorithm
                  (sourceHumanRankings human .r0123 .r0123) order : ℝ) := by
          apply Finset.sum_congr rfl
          intro algorithm _
          apply Finset.sum_congr rfl
          intro order _
          apply Finset.sum_congr rfl
          intro human _
          rw [sourceOneHumanProductLaw, sourceFinitePMFProduct_apply_toReal,
            sourceFinitePMFProduct_apply_toReal,
            sourceUniformFirmOrderLaw_apply_toReal]
          ring

/-- The AAH profile law has its one active human coordinate at firm `2`. -/
theorem sourceProfileHumanRankingLaw_AAH_apply
    (h0 h1 h2 : SourceFourRanking) :
    sourceProfileHumanRankingLaw sourceProfileAAH
        (sourceHumanRankings h0 h1 h2) =
      sourceInactiveHumanRankingLaw h0 * sourceInactiveHumanRankingLaw h1 *
        sourceHumanRankingLaw h2 := by
  simpa [sourceProfileHumanCoordinateLaw, sourceProfileAAH, mul_assoc] using
    sourceProfileHumanRankingLaw_apply_sourceHumanRankings
      sourceProfileAAH h0 h1 h2

/-- Project the two inactive AAH coordinates while retaining firm `2`'s human
Mallows ranking. -/
theorem sourceProfileHumanRankingLaw_AAH_weighted_sum
    (f : (SourceThreeFirm -> SourceFourRanking) -> ℝ) :
    (∑ human : SourceThreeFirm -> SourceFourRanking,
      (sourceProfileHumanRankingLaw sourceProfileAAH human).toReal * f human) =
      ∑ h2 : SourceFourRanking,
        (sourceHumanRankingLaw h2).toReal *
          f (sourceHumanRankings .r0123 .r0123 h2) := by
  rw [← Equiv.sum_comp sourceHumanRankingsEquiv]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]
  simp_rw [sourceHumanRankingsEquiv_apply,
    sourceProfileHumanRankingLaw_AAH_apply, ENNReal.toReal_mul]
  exact sourceInactiveHumanRankingLaw_two_left_weighted_sum
    (fun h2 => (sourceHumanRankingLaw h2).toReal)
    (fun h0 h1 h2 => f (sourceHumanRankings h0 h1 h2))

/-- The generic focal AAH expectation is the existing one-human source PMF
expectation after its explicit inactive-coordinate projection. -/
theorem sourceProfileExpectedUtility_AAH_zero_eq_cast_direct :
    sourceProfileExpectedUtility sourceProfileAAH 0 =
      ((sourceDirectRankMeanExpectedAAH : ℚ) : ℝ) := by
  rw [sourceProfileExpectedUtility_zero_eq_namedOrder_sum,
    ← sourceAAHProductLawExpectation_eq_cast_direct]
  unfold sourceAAHProductLawExpectation
  calc
    (∑ algorithm : SourceFourRanking,
      ∑ human : SourceThreeFirm -> SourceFourRanking,
        ∑ order : SourceFirmOrder,
          (sourceAlgorithmRankingLaw algorithm).toReal *
              (sourceProfileHumanRankingLaw sourceProfileAAH human).toReal *
                ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                  (sourceFocalUtility sourceProfileAAH algorithm human order : ℝ)) =
        ∑ algorithm : SourceFourRanking,
          ∑ order : SourceFirmOrder,
            ∑ human : SourceFourRanking,
              (sourceAlgorithmRankingLaw algorithm).toReal *
                ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                  ((sourceHumanRankingLaw human).toReal *
                    (sourceFocalUtility sourceProfileAAH algorithm
                      (sourceHumanRankings .r0123 .r0123 human) order : ℝ)) := by
          apply Finset.sum_congr rfl
          intro algorithm _
          calc
            (∑ human : SourceThreeFirm -> SourceFourRanking,
              ∑ order : SourceFirmOrder,
                (sourceAlgorithmRankingLaw algorithm).toReal *
                    (sourceProfileHumanRankingLaw sourceProfileAAH human).toReal *
                      ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                        (sourceFocalUtility sourceProfileAAH algorithm human order : ℝ)) =
                ∑ order : SourceFirmOrder,
                  ∑ human : SourceThreeFirm -> SourceFourRanking,
                    (sourceAlgorithmRankingLaw algorithm).toReal *
                      ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                        ((sourceProfileHumanRankingLaw sourceProfileAAH human).toReal *
                          (sourceFocalUtility sourceProfileAAH algorithm human order : ℝ)) := by
                    rw [Finset.sum_comm]
                    apply Finset.sum_congr rfl
                    intro order _
                    apply Finset.sum_congr rfl
                    intro human _
                    ring
            _ = ∑ order : SourceFirmOrder,
                  ∑ human : SourceFourRanking,
                    (sourceAlgorithmRankingLaw algorithm).toReal *
                      ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                        ((sourceHumanRankingLaw human).toReal *
                          (sourceFocalUtility sourceProfileAAH algorithm
                            (sourceHumanRankings .r0123 .r0123 human) order : ℝ)) := by
                    apply Finset.sum_congr rfl
                    intro order _
                    calc
                      (∑ human : SourceThreeFirm -> SourceFourRanking,
                        (sourceAlgorithmRankingLaw algorithm).toReal *
                          ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                            ((sourceProfileHumanRankingLaw sourceProfileAAH human).toReal *
                              (sourceFocalUtility sourceProfileAAH algorithm human order : ℝ))) =
                          (sourceAlgorithmRankingLaw algorithm).toReal *
                            ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                              ∑ human : SourceThreeFirm -> SourceFourRanking,
                                (sourceProfileHumanRankingLaw sourceProfileAAH human).toReal *
                                  (sourceFocalUtility sourceProfileAAH algorithm human order : ℝ) := by
                            exact (Finset.mul_sum
                              (Finset.univ : Finset (SourceThreeFirm -> SourceFourRanking))
                              (fun human =>
                                (sourceProfileHumanRankingLaw sourceProfileAAH human).toReal *
                                  (sourceFocalUtility sourceProfileAAH algorithm human order : ℝ))
                              ((sourceAlgorithmRankingLaw algorithm).toReal *
                                ((sourceUniformFirmOrderMass : ℚ) : ℝ))).symm
                      _ = (sourceAlgorithmRankingLaw algorithm).toReal *
                            ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                              ∑ human : SourceFourRanking,
                                (sourceHumanRankingLaw human).toReal *
                                  (sourceFocalUtility sourceProfileAAH algorithm
                                    (sourceHumanRankings .r0123 .r0123 human) order : ℝ) := by
                            rw [sourceProfileHumanRankingLaw_AAH_weighted_sum]
                      _ = ∑ human : SourceFourRanking,
                            (sourceAlgorithmRankingLaw algorithm).toReal *
                              ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                                ((sourceHumanRankingLaw human).toReal *
                                  (sourceFocalUtility sourceProfileAAH algorithm
                                    (sourceHumanRankings .r0123 .r0123 human) order : ℝ)) := by
                            exact Finset.mul_sum
                              (Finset.univ : Finset SourceFourRanking)
                              (fun human =>
                                (sourceHumanRankingLaw human).toReal *
                                  (sourceFocalUtility sourceProfileAAH algorithm
                                    (sourceHumanRankings .r0123 .r0123 human) order : ℝ))
                              ((sourceAlgorithmRankingLaw algorithm).toReal *
                                ((sourceUniformFirmOrderMass : ℚ) : ℝ))
    _ = ∑ algorithm : SourceFourRanking,
          ∑ order : SourceFirmOrder,
            ∑ human : SourceFourRanking,
              (sourceOneHumanProductLaw ((algorithm, human), order)).toReal *
                (sourceFocalUtility sourceProfileAAH algorithm
                  (sourceHumanRankings .r0123 .r0123 human) order : ℝ) := by
          apply Finset.sum_congr rfl
          intro algorithm _
          apply Finset.sum_congr rfl
          intro order _
          apply Finset.sum_congr rfl
          intro human _
          rw [sourceOneHumanProductLaw, sourceFinitePMFProduct_apply_toReal,
            sourceFinitePMFProduct_apply_toReal,
            sourceUniformFirmOrderLaw_apply_toReal]
          ring

/-- The HAH profile law has active human coordinates at firms `0` and `2`,
with the middle algorithm user's coordinate represented by its explicit
inactive point mass. -/
theorem sourceProfileHumanRankingLaw_HAH_apply
    (h0 h1 h2 : SourceFourRanking) :
    sourceProfileHumanRankingLaw sourceProfileHAH
        (sourceHumanRankings h0 h1 h2) =
      sourceHumanRankingLaw h0 * sourceInactiveHumanRankingLaw h1 *
        sourceHumanRankingLaw h2 := by
  simpa [sourceProfileHumanCoordinateLaw, sourceProfileHAH, mul_assoc] using
    sourceProfileHumanRankingLaw_apply_sourceHumanRankings
      sourceProfileHAH h0 h1 h2

/-- Project HAH's one inactive middle coordinate while retaining both actual
independent human Mallows draws. -/
theorem sourceProfileHumanRankingLaw_HAH_weighted_sum
    (f : (SourceThreeFirm -> SourceFourRanking) -> ℝ) :
    (∑ human : SourceThreeFirm -> SourceFourRanking,
      (sourceProfileHumanRankingLaw sourceProfileHAH human).toReal * f human) =
      ∑ h0 : SourceFourRanking, ∑ h2 : SourceFourRanking,
        (sourceHumanRankingLaw h0).toReal *
          (sourceHumanRankingLaw h2).toReal *
            f (sourceHumanRankings h0 .r0123 h2) := by
  rw [← Equiv.sum_comp sourceHumanRankingsEquiv]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]
  simp_rw [sourceHumanRankingsEquiv_apply,
    sourceProfileHumanRankingLaw_HAH_apply, ENNReal.toReal_mul]
  exact sourceInactiveHumanRankingLaw_middle_weighted_sum
    (fun h0 => (sourceHumanRankingLaw h0).toReal)
    (fun h2 => (sourceHumanRankingLaw h2).toReal)
    (fun h0 h1 h2 => f (sourceHumanRankings h0 h1 h2))

/-- The generic focal HAH expectation is the existing two-human source PMF
expectation after explicit projection of its middle inactive coordinate. -/
theorem sourceProfileExpectedUtility_HAH_zero_eq_cast_direct :
    sourceProfileExpectedUtility sourceProfileHAH 0 =
      ((sourceDirectRankMeanExpectedHAH : ℚ) : ℝ) := by
  rw [sourceProfileExpectedUtility_zero_eq_namedOrder_sum,
    ← sourceHAHProductLawExpectation_eq_cast_direct]
  unfold sourceHAHProductLawExpectation
  calc
    (∑ algorithm : SourceFourRanking,
      ∑ human : SourceThreeFirm -> SourceFourRanking,
        ∑ order : SourceFirmOrder,
          (sourceAlgorithmRankingLaw algorithm).toReal *
              (sourceProfileHumanRankingLaw sourceProfileHAH human).toReal *
                ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                  (sourceFocalUtility sourceProfileHAH algorithm human order : ℝ)) =
        ∑ algorithm : SourceFourRanking,
          ∑ order : SourceFirmOrder,
            ∑ h0 : SourceFourRanking, ∑ h2 : SourceFourRanking,
              (sourceAlgorithmRankingLaw algorithm).toReal *
                ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                  ((sourceHumanRankingLaw h0).toReal *
                    (sourceHumanRankingLaw h2).toReal *
                      (sourceFocalUtility sourceProfileHAH algorithm
                        (sourceHumanRankings h0 .r0123 h2) order : ℝ)) := by
          apply Finset.sum_congr rfl
          intro algorithm _
          calc
            (∑ human : SourceThreeFirm -> SourceFourRanking,
              ∑ order : SourceFirmOrder,
                (sourceAlgorithmRankingLaw algorithm).toReal *
                    (sourceProfileHumanRankingLaw sourceProfileHAH human).toReal *
                      ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                        (sourceFocalUtility sourceProfileHAH algorithm human order : ℝ)) =
                ∑ order : SourceFirmOrder,
                  ∑ human : SourceThreeFirm -> SourceFourRanking,
                    (sourceAlgorithmRankingLaw algorithm).toReal *
                      ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                        ((sourceProfileHumanRankingLaw sourceProfileHAH human).toReal *
                          (sourceFocalUtility sourceProfileHAH algorithm human order : ℝ)) := by
                    rw [Finset.sum_comm]
                    apply Finset.sum_congr rfl
                    intro order _
                    apply Finset.sum_congr rfl
                    intro human _
                    ring
            _ = ∑ order : SourceFirmOrder,
                  ∑ h0 : SourceFourRanking, ∑ h2 : SourceFourRanking,
                    (sourceAlgorithmRankingLaw algorithm).toReal *
                      ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                        ((sourceHumanRankingLaw h0).toReal *
                          (sourceHumanRankingLaw h2).toReal *
                            (sourceFocalUtility sourceProfileHAH algorithm
                              (sourceHumanRankings h0 .r0123 h2) order : ℝ)) := by
                    apply Finset.sum_congr rfl
                    intro order _
                    calc
                      (∑ human : SourceThreeFirm -> SourceFourRanking,
                        (sourceAlgorithmRankingLaw algorithm).toReal *
                          ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                            ((sourceProfileHumanRankingLaw sourceProfileHAH human).toReal *
                              (sourceFocalUtility sourceProfileHAH algorithm human order : ℝ))) =
                          (sourceAlgorithmRankingLaw algorithm).toReal *
                            ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                              ∑ human : SourceThreeFirm -> SourceFourRanking,
                                (sourceProfileHumanRankingLaw sourceProfileHAH human).toReal *
                                  (sourceFocalUtility sourceProfileHAH algorithm human order : ℝ) := by
                            exact (Finset.mul_sum
                              (Finset.univ : Finset (SourceThreeFirm -> SourceFourRanking))
                              (fun human =>
                                (sourceProfileHumanRankingLaw sourceProfileHAH human).toReal *
                                  (sourceFocalUtility sourceProfileHAH algorithm human order : ℝ))
                              ((sourceAlgorithmRankingLaw algorithm).toReal *
                                ((sourceUniformFirmOrderMass : ℚ) : ℝ))).symm
                      _ = (sourceAlgorithmRankingLaw algorithm).toReal *
                            ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                              ∑ h0 : SourceFourRanking, ∑ h2 : SourceFourRanking,
                                (sourceHumanRankingLaw h0).toReal *
                                  (sourceHumanRankingLaw h2).toReal *
                                    (sourceFocalUtility sourceProfileHAH algorithm
                                      (sourceHumanRankings h0 .r0123 h2) order : ℝ) := by
                            rw [sourceProfileHumanRankingLaw_HAH_weighted_sum]
                      _ = ∑ h0 : SourceFourRanking,
                            (sourceAlgorithmRankingLaw algorithm).toReal *
                              ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                                ∑ h2 : SourceFourRanking,
                                  (sourceHumanRankingLaw h0).toReal *
                                    (sourceHumanRankingLaw h2).toReal *
                                      (sourceFocalUtility sourceProfileHAH algorithm
                                        (sourceHumanRankings h0 .r0123 h2) order : ℝ) := by
                            exact Finset.mul_sum
                              (Finset.univ : Finset SourceFourRanking)
                              (fun h0 => ∑ h2 : SourceFourRanking,
                                (sourceHumanRankingLaw h0).toReal *
                                  (sourceHumanRankingLaw h2).toReal *
                                    (sourceFocalUtility sourceProfileHAH algorithm
                                      (sourceHumanRankings h0 .r0123 h2) order : ℝ))
                              ((sourceAlgorithmRankingLaw algorithm).toReal *
                                ((sourceUniformFirmOrderMass : ℚ) : ℝ))
                      _ = ∑ h0 : SourceFourRanking, ∑ h2 : SourceFourRanking,
                            (sourceAlgorithmRankingLaw algorithm).toReal *
                              ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                                ((sourceHumanRankingLaw h0).toReal *
                                  (sourceHumanRankingLaw h2).toReal *
                                    (sourceFocalUtility sourceProfileHAH algorithm
                                      (sourceHumanRankings h0 .r0123 h2) order : ℝ)) := by
                            apply Finset.sum_congr rfl
                            intro h0 _
                            exact Finset.mul_sum
                              (Finset.univ : Finset SourceFourRanking)
                              (fun h2 =>
                                (sourceHumanRankingLaw h0).toReal *
                                  (sourceHumanRankingLaw h2).toReal *
                                    (sourceFocalUtility sourceProfileHAH algorithm
                                      (sourceHumanRankings h0 .r0123 h2) order : ℝ))
                              ((sourceAlgorithmRankingLaw algorithm).toReal *
                                ((sourceUniformFirmOrderMass : ℚ) : ℝ))
    _ = ∑ algorithm : SourceFourRanking,
          ∑ order : SourceFirmOrder,
            ∑ h0 : SourceFourRanking, ∑ h2 : SourceFourRanking,
              (sourceTwoHumanProductLaw ((algorithm, (h0, h2)), order)).toReal *
                (sourceFocalUtility sourceProfileHAH algorithm
                  (sourceHumanRankings h0 .r0123 h2) order : ℝ) := by
          apply Finset.sum_congr rfl
          intro algorithm _
          apply Finset.sum_congr rfl
          intro order _
          apply Finset.sum_congr rfl
          intro h0 _
          apply Finset.sum_congr rfl
          intro h2 _
          rw [sourceTwoHumanProductLaw, sourceFinitePMFProduct_apply_toReal,
            sourceFinitePMFProduct_apply_toReal,
            sourceHumanPairRankingLaw, sourceFinitePMFProduct_apply_toReal,
            sourceUniformFirmOrderLaw_apply_toReal]
          ring

/-- The AHH profile law has an inactive algorithm-user coordinate at firm
`0` and active independent human coordinates at firms `1` and `2`. -/
theorem sourceProfileHumanRankingLaw_AHH_apply
    (h0 h1 h2 : SourceFourRanking) :
    sourceProfileHumanRankingLaw sourceProfileAHH
        (sourceHumanRankings h0 h1 h2) =
      sourceInactiveHumanRankingLaw h0 * sourceHumanRankingLaw h1 *
        sourceHumanRankingLaw h2 := by
  simpa [sourceProfileHumanCoordinateLaw, sourceProfileAHH, mul_assoc] using
    sourceProfileHumanRankingLaw_apply_sourceHumanRankings
      sourceProfileAHH h0 h1 h2

/-- Project AHH's inactive left coordinate while retaining both independent
human Mallows rankings. -/
theorem sourceProfileHumanRankingLaw_AHH_weighted_sum
    (f : (SourceThreeFirm -> SourceFourRanking) -> ℝ) :
    (∑ human : SourceThreeFirm -> SourceFourRanking,
      (sourceProfileHumanRankingLaw sourceProfileAHH human).toReal * f human) =
      ∑ h1 : SourceFourRanking, ∑ h2 : SourceFourRanking,
        (sourceHumanRankingLaw h1).toReal *
          (sourceHumanRankingLaw h2).toReal *
            f (sourceHumanRankings .r0123 h1 h2) := by
  rw [← Equiv.sum_comp sourceHumanRankingsEquiv]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]
  simp_rw [sourceHumanRankingsEquiv_apply,
    sourceProfileHumanRankingLaw_AHH_apply, ENNReal.toReal_mul]
  exact sourceInactiveHumanRankingLaw_left_weighted_sum
    (fun h1 => (sourceHumanRankingLaw h1).toReal)
    (fun h2 => (sourceHumanRankingLaw h2).toReal)
    (fun h0 h1 h2 => f (sourceHumanRankings h0 h1 h2))

/-- The generic focal AHH expectation is the existing two-human source PMF
expectation after explicit projection of its inactive left coordinate. -/
theorem sourceProfileExpectedUtility_AHH_zero_eq_cast_direct :
    sourceProfileExpectedUtility sourceProfileAHH 0 =
      ((sourceDirectRankMeanExpectedAHH : ℚ) : ℝ) := by
  rw [sourceProfileExpectedUtility_zero_eq_namedOrder_sum,
    ← sourceAHHProductLawExpectation_eq_cast_direct]
  unfold sourceAHHProductLawExpectation
  calc
    (∑ algorithm : SourceFourRanking,
      ∑ human : SourceThreeFirm -> SourceFourRanking,
        ∑ order : SourceFirmOrder,
          (sourceAlgorithmRankingLaw algorithm).toReal *
              (sourceProfileHumanRankingLaw sourceProfileAHH human).toReal *
                ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                  (sourceFocalUtility sourceProfileAHH algorithm human order : ℝ)) =
        ∑ algorithm : SourceFourRanking,
          ∑ order : SourceFirmOrder,
            ∑ h1 : SourceFourRanking, ∑ h2 : SourceFourRanking,
              (sourceAlgorithmRankingLaw algorithm).toReal *
                ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                  ((sourceHumanRankingLaw h1).toReal *
                    (sourceHumanRankingLaw h2).toReal *
                      (sourceFocalUtility sourceProfileAHH algorithm
                        (sourceHumanRankings .r0123 h1 h2) order : ℝ)) := by
          apply Finset.sum_congr rfl
          intro algorithm _
          calc
            (∑ human : SourceThreeFirm -> SourceFourRanking,
              ∑ order : SourceFirmOrder,
                (sourceAlgorithmRankingLaw algorithm).toReal *
                    (sourceProfileHumanRankingLaw sourceProfileAHH human).toReal *
                      ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                        (sourceFocalUtility sourceProfileAHH algorithm human order : ℝ)) =
                ∑ order : SourceFirmOrder,
                  ∑ human : SourceThreeFirm -> SourceFourRanking,
                    (sourceAlgorithmRankingLaw algorithm).toReal *
                      ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                        ((sourceProfileHumanRankingLaw sourceProfileAHH human).toReal *
                          (sourceFocalUtility sourceProfileAHH algorithm human order : ℝ)) := by
                    rw [Finset.sum_comm]
                    apply Finset.sum_congr rfl
                    intro order _
                    apply Finset.sum_congr rfl
                    intro human _
                    ring
            _ = ∑ order : SourceFirmOrder,
                  ∑ h1 : SourceFourRanking, ∑ h2 : SourceFourRanking,
                    (sourceAlgorithmRankingLaw algorithm).toReal *
                      ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                        ((sourceHumanRankingLaw h1).toReal *
                          (sourceHumanRankingLaw h2).toReal *
                            (sourceFocalUtility sourceProfileAHH algorithm
                              (sourceHumanRankings .r0123 h1 h2) order : ℝ)) := by
                    apply Finset.sum_congr rfl
                    intro order _
                    calc
                      (∑ human : SourceThreeFirm -> SourceFourRanking,
                        (sourceAlgorithmRankingLaw algorithm).toReal *
                          ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                            ((sourceProfileHumanRankingLaw sourceProfileAHH human).toReal *
                              (sourceFocalUtility sourceProfileAHH algorithm human order : ℝ))) =
                          (sourceAlgorithmRankingLaw algorithm).toReal *
                            ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                              ∑ human : SourceThreeFirm -> SourceFourRanking,
                                (sourceProfileHumanRankingLaw sourceProfileAHH human).toReal *
                                  (sourceFocalUtility sourceProfileAHH algorithm human order : ℝ) := by
                            exact (Finset.mul_sum
                              (Finset.univ : Finset (SourceThreeFirm -> SourceFourRanking))
                              (fun human =>
                                (sourceProfileHumanRankingLaw sourceProfileAHH human).toReal *
                                  (sourceFocalUtility sourceProfileAHH algorithm human order : ℝ))
                              ((sourceAlgorithmRankingLaw algorithm).toReal *
                                ((sourceUniformFirmOrderMass : ℚ) : ℝ))).symm
                      _ = (sourceAlgorithmRankingLaw algorithm).toReal *
                            ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                              ∑ h1 : SourceFourRanking, ∑ h2 : SourceFourRanking,
                                (sourceHumanRankingLaw h1).toReal *
                                  (sourceHumanRankingLaw h2).toReal *
                                    (sourceFocalUtility sourceProfileAHH algorithm
                                      (sourceHumanRankings .r0123 h1 h2) order : ℝ) := by
                            rw [sourceProfileHumanRankingLaw_AHH_weighted_sum]
                      _ = ∑ h1 : SourceFourRanking,
                            (sourceAlgorithmRankingLaw algorithm).toReal *
                              ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                                ∑ h2 : SourceFourRanking,
                                  (sourceHumanRankingLaw h1).toReal *
                                    (sourceHumanRankingLaw h2).toReal *
                                      (sourceFocalUtility sourceProfileAHH algorithm
                                        (sourceHumanRankings .r0123 h1 h2) order : ℝ) := by
                            exact Finset.mul_sum
                              (Finset.univ : Finset SourceFourRanking)
                              (fun h1 => ∑ h2 : SourceFourRanking,
                                (sourceHumanRankingLaw h1).toReal *
                                  (sourceHumanRankingLaw h2).toReal *
                                    (sourceFocalUtility sourceProfileAHH algorithm
                                      (sourceHumanRankings .r0123 h1 h2) order : ℝ))
                              ((sourceAlgorithmRankingLaw algorithm).toReal *
                                ((sourceUniformFirmOrderMass : ℚ) : ℝ))
                      _ = ∑ h1 : SourceFourRanking, ∑ h2 : SourceFourRanking,
                            (sourceAlgorithmRankingLaw algorithm).toReal *
                              ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                                ((sourceHumanRankingLaw h1).toReal *
                                  (sourceHumanRankingLaw h2).toReal *
                                    (sourceFocalUtility sourceProfileAHH algorithm
                                      (sourceHumanRankings .r0123 h1 h2) order : ℝ)) := by
                            apply Finset.sum_congr rfl
                            intro h1 _
                            exact Finset.mul_sum
                              (Finset.univ : Finset SourceFourRanking)
                              (fun h2 =>
                                (sourceHumanRankingLaw h1).toReal *
                                  (sourceHumanRankingLaw h2).toReal *
                                    (sourceFocalUtility sourceProfileAHH algorithm
                                      (sourceHumanRankings .r0123 h1 h2) order : ℝ))
                              ((sourceAlgorithmRankingLaw algorithm).toReal *
                                ((sourceUniformFirmOrderMass : ℚ) : ℝ))
    _ = ∑ algorithm : SourceFourRanking,
          ∑ order : SourceFirmOrder,
            ∑ h1 : SourceFourRanking, ∑ h2 : SourceFourRanking,
              (sourceTwoHumanProductLaw ((algorithm, (h1, h2)), order)).toReal *
                (sourceFocalUtility sourceProfileAHH algorithm
                  (sourceHumanRankings .r0123 h1 h2) order : ℝ) := by
          apply Finset.sum_congr rfl
          intro algorithm _
          apply Finset.sum_congr rfl
          intro order _
          apply Finset.sum_congr rfl
          intro h1 _
          apply Finset.sum_congr rfl
          intro h2 _
          rw [sourceTwoHumanProductLaw, sourceFinitePMFProduct_apply_toReal,
            sourceFinitePMFProduct_apply_toReal,
            sourceHumanPairRankingLaw, sourceFinitePMFProduct_apply_toReal,
            sourceUniformFirmOrderLaw_apply_toReal]
          ring

/-- The HHH profile carries all three independent human-ranking coordinates. -/
theorem sourceProfileHumanRankingLaw_HHH_apply
    (h0 h1 h2 : SourceFourRanking) :
    sourceProfileHumanRankingLaw sourceProfileHHH
        (sourceHumanRankings h0 h1 h2) =
      sourceHumanRankingLaw h0 * sourceHumanRankingLaw h1 *
        sourceHumanRankingLaw h2 := by
  simpa [sourceProfileHumanCoordinateLaw, sourceProfileHHH, mul_assoc] using
    sourceProfileHumanRankingLaw_apply_sourceHumanRankings
      sourceProfileHHH h0 h1 h2

/-- Reindex the all-human profile law into its three explicit independent
Mallows coordinates. -/
theorem sourceProfileHumanRankingLaw_HHH_weighted_sum
    (f : (SourceThreeFirm -> SourceFourRanking) -> ℝ) :
    (∑ human : SourceThreeFirm -> SourceFourRanking,
      (sourceProfileHumanRankingLaw sourceProfileHHH human).toReal * f human) =
      ∑ h0 : SourceFourRanking, ∑ h1 : SourceFourRanking,
        ∑ h2 : SourceFourRanking,
          (sourceHumanRankingLaw h0).toReal *
            (sourceHumanRankingLaw h1).toReal *
              (sourceHumanRankingLaw h2).toReal *
                f (sourceHumanRankings h0 h1 h2) := by
  rw [← Equiv.sum_comp sourceHumanRankingsEquiv]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]
  simp_rw [sourceHumanRankingsEquiv_apply,
    sourceProfileHumanRankingLaw_HHH_apply, ENNReal.toReal_mul]

/-- The shared algorithm PMF has unit total real mass. -/
theorem sourceAlgorithmRankingLaw_toReal_sum :
    ∑ algorithm : SourceFourRanking,
      (sourceAlgorithmRankingLaw algorithm).toReal = 1 := by
  have hsum : (∑ algorithm : SourceFourRanking,
      sourceAlgorithmRankingLaw algorithm) = 1 := by
    simpa only [tsum_fintype] using sourceAlgorithmRankingLaw.tsum_coe
  calc
    (∑ algorithm : SourceFourRanking,
      (sourceAlgorithmRankingLaw algorithm).toReal) =
        (∑ algorithm : SourceFourRanking,
          sourceAlgorithmRankingLaw algorithm).toReal := by
          rw [ENNReal.toReal_sum (fun algorithm _ =>
            sourceAlgorithmRankingLaw.apply_ne_top algorithm)]
    _ = 1 := by rw [hsum]; norm_num

/-- Integrating a finite expression independent of the shared algorithm draw
against its source PMF leaves that expression unchanged. -/
theorem sourceAlgorithmRankingLaw_weighted_sum (c : ℝ) :
    (∑ algorithm : SourceFourRanking,
      (sourceAlgorithmRankingLaw algorithm).toReal * c) = c := by
  calc
    (∑ algorithm : SourceFourRanking,
      (sourceAlgorithmRankingLaw algorithm).toReal * c) =
        (∑ algorithm : SourceFourRanking,
          (sourceAlgorithmRankingLaw algorithm).toReal) * c := by
          exact (Finset.sum_mul
            (Finset.univ : Finset SourceFourRanking)
            (fun algorithm => (sourceAlgorithmRankingLaw algorithm).toReal) c).symm
    _ = c := by rw [sourceAlgorithmRankingLaw_toReal_sum, one_mul]

/-- In the all-human profile, the shared algorithm draw is semantically
irrelevant to the focal allocation and utility. -/
theorem sourceFocalUtility_HHH_algorithm_irrelevant
    (algorithm : SourceFourRanking)
    (human : SourceThreeFirm -> SourceFourRanking)
    (order : SourceFirmOrder) :
    sourceFocalUtility sourceProfileHHH algorithm human order =
      sourceFocalUtility sourceProfileHHH .r0123 human order := by
  simp [sourceFocalUtility, sourceProfileHHH]

/-- The generic focal HHH expectation is the existing three-human source PMF
expectation.  In particular, the unused algorithm coordinate is normalized
by its actual PMF rather than silently omitted. -/
theorem sourceProfileExpectedUtility_HHH_zero_eq_cast_direct :
    sourceProfileExpectedUtility sourceProfileHHH 0 =
      ((sourceDirectRankMeanExpectedHHH : ℚ) : ℝ) := by
  rw [sourceProfileExpectedUtility_zero_eq_namedOrder_sum,
    ← sourceHHHProductLawExpectation_eq_cast_direct]
  unfold sourceHHHProductLawExpectation
  calc
    (∑ algorithm : SourceFourRanking,
      ∑ human : SourceThreeFirm -> SourceFourRanking,
        ∑ order : SourceFirmOrder,
          (sourceAlgorithmRankingLaw algorithm).toReal *
              (sourceProfileHumanRankingLaw sourceProfileHHH human).toReal *
                ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                  (sourceFocalUtility sourceProfileHHH algorithm human order : ℝ)) =
        ∑ human : SourceThreeFirm -> SourceFourRanking,
          ∑ algorithm : SourceFourRanking,
            ∑ order : SourceFirmOrder,
              (sourceAlgorithmRankingLaw algorithm).toReal *
                (sourceProfileHumanRankingLaw sourceProfileHHH human).toReal *
                  ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                    (sourceFocalUtility sourceProfileHHH algorithm human order : ℝ) := by
          exact Finset.sum_comm
    _ = ∑ human : SourceThreeFirm -> SourceFourRanking,
          ∑ order : SourceFirmOrder,
            ∑ algorithm : SourceFourRanking,
              (sourceAlgorithmRankingLaw algorithm).toReal *
                (sourceProfileHumanRankingLaw sourceProfileHHH human).toReal *
                  ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                    (sourceFocalUtility sourceProfileHHH algorithm human order : ℝ) := by
          apply Finset.sum_congr rfl
          intro human _
          exact Finset.sum_comm
    _ = ∑ human : SourceThreeFirm -> SourceFourRanking,
          ∑ order : SourceFirmOrder,
            ∑ algorithm : SourceFourRanking,
              (sourceAlgorithmRankingLaw algorithm).toReal *
                ((sourceProfileHumanRankingLaw sourceProfileHHH human).toReal *
                  ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                    (sourceFocalUtility sourceProfileHHH .r0123 human order : ℝ)) := by
          apply Finset.sum_congr rfl
          intro human _
          apply Finset.sum_congr rfl
          intro order _
          apply Finset.sum_congr rfl
          intro algorithm _
          rw [sourceFocalUtility_HHH_algorithm_irrelevant]
          ring
    _ = ∑ human : SourceThreeFirm -> SourceFourRanking,
          ∑ order : SourceFirmOrder,
            (sourceProfileHumanRankingLaw sourceProfileHHH human).toReal *
              ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                (sourceFocalUtility sourceProfileHHH .r0123 human order : ℝ) := by
          apply Finset.sum_congr rfl
          intro human _
          apply Finset.sum_congr rfl
          intro order _
          exact sourceAlgorithmRankingLaw_weighted_sum _
    _ = ∑ order : SourceFirmOrder,
          ∑ human : SourceThreeFirm -> SourceFourRanking,
            (sourceProfileHumanRankingLaw sourceProfileHHH human).toReal *
              ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                (sourceFocalUtility sourceProfileHHH .r0123 human order : ℝ) := by
          simpa only using
            (Finset.sum_comm
              (s := (Finset.univ : Finset
                (SourceThreeFirm -> SourceFourRanking)))
              (t := (Finset.univ : Finset SourceFirmOrder))
              (f := fun human order =>
                (sourceProfileHumanRankingLaw sourceProfileHHH human).toReal *
                  ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                    (sourceFocalUtility sourceProfileHHH .r0123 human order : ℝ)))
    _ = ∑ order : SourceFirmOrder,
          ∑ h0 : SourceFourRanking, ∑ h1 : SourceFourRanking,
            ∑ h2 : SourceFourRanking,
              (sourceHumanRankingLaw h0).toReal *
                (sourceHumanRankingLaw h1).toReal *
                  (sourceHumanRankingLaw h2).toReal *
                    ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                      (sourceFocalUtility sourceProfileHHH .r0123
                        (sourceHumanRankings h0 h1 h2) order : ℝ) := by
          apply Finset.sum_congr rfl
          intro order _
          calc
            (∑ human : SourceThreeFirm -> SourceFourRanking,
              (sourceProfileHumanRankingLaw sourceProfileHHH human).toReal *
                ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                  (sourceFocalUtility sourceProfileHHH .r0123 human order : ℝ)) =
                ∑ human : SourceThreeFirm -> SourceFourRanking,
                  (sourceProfileHumanRankingLaw sourceProfileHHH human).toReal *
                    (((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                      (sourceFocalUtility sourceProfileHHH .r0123 human order : ℝ)) := by
                    apply Finset.sum_congr rfl
                    intro human _
                    ring
            _ = ∑ h0 : SourceFourRanking, ∑ h1 : SourceFourRanking,
                  ∑ h2 : SourceFourRanking,
                    (sourceHumanRankingLaw h0).toReal *
                      (sourceHumanRankingLaw h1).toReal *
                        (sourceHumanRankingLaw h2).toReal *
                          (((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                            (sourceFocalUtility sourceProfileHHH .r0123
                              (sourceHumanRankings h0 h1 h2) order : ℝ)) := by
                    rw [sourceProfileHumanRankingLaw_HHH_weighted_sum]
            _ = ∑ h0 : SourceFourRanking, ∑ h1 : SourceFourRanking,
                  ∑ h2 : SourceFourRanking,
                    (sourceHumanRankingLaw h0).toReal *
                      (sourceHumanRankingLaw h1).toReal *
                        (sourceHumanRankingLaw h2).toReal *
                          ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                            (sourceFocalUtility sourceProfileHHH .r0123
                              (sourceHumanRankings h0 h1 h2) order : ℝ) := by
                    apply Finset.sum_congr rfl
                    intro h0 _
                    apply Finset.sum_congr rfl
                    intro h1 _
                    apply Finset.sum_congr rfl
                    intro h2 _
                    ring
    _ = ∑ order : SourceFirmOrder,
          ∑ h0 : SourceFourRanking, ∑ h1 : SourceFourRanking,
            ∑ h2 : SourceFourRanking,
              (sourceHHHProductLaw (((h0, h1), h2), order)).toReal *
                (sourceFocalUtility sourceProfileHHH .r0123
                  (sourceHumanRankings h0 h1 h2) order : ℝ) := by
          apply Finset.sum_congr rfl
          intro order _
          apply Finset.sum_congr rfl
          intro h0 _
          apply Finset.sum_congr rfl
          intro h1 _
          apply Finset.sum_congr rfl
          intro h2 _
          rw [sourceHHHProductLaw, sourceFinitePMFProduct_apply_toReal,
            sourceHumanTripleRankingLaw, sourceFinitePMFProduct_apply_toReal,
            sourceHumanPairRankingLaw, sourceFinitePMFProduct_apply_toReal,
            sourceUniformFirmOrderLaw_apply_toReal]

/-- The generic raw source experiment's focal AAA utility is the already
computed direct finite AAA expectation.  This is the first explicit
marginal-identification lemma: all three inactive PMF coordinates are
projected by their actual point masses. -/
theorem sourceProfileExpectedUtility_AAA_zero_eq_cast_direct :
    sourceProfileExpectedUtility sourceProfileAAA 0 =
      ((sourceDirectRankMeanExpectedAAA : ℚ) : ℝ) := by
  rw [sourceProfileExpectedUtility_zero_eq_namedOrder_sum,
    ← sourceAAAProductLawExpectation_eq_cast_direct]
  unfold sourceAAAProductLawExpectation
  calc
    (∑ algorithm : SourceFourRanking,
      ∑ human : SourceThreeFirm -> SourceFourRanking,
        ∑ order : SourceFirmOrder,
          (sourceAlgorithmRankingLaw algorithm).toReal *
              (sourceProfileHumanRankingLaw sourceProfileAAA human).toReal *
                ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                  (sourceFocalUtility sourceProfileAAA algorithm human order : ℝ)) =
        ∑ algorithm : SourceFourRanking,
          ∑ order : SourceFirmOrder,
            (sourceAlgorithmRankingLaw algorithm).toReal *
              ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                (sourceFocalUtility sourceProfileAAA algorithm
                  (sourceHumanRankings .r0123 .r0123 .r0123) order : ℝ) := by
          apply Finset.sum_congr rfl
          intro algorithm _
          calc
            (∑ human : SourceThreeFirm -> SourceFourRanking,
              ∑ order : SourceFirmOrder,
                (sourceAlgorithmRankingLaw algorithm).toReal *
                    (sourceProfileHumanRankingLaw sourceProfileAAA human).toReal *
                      ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                        (sourceFocalUtility sourceProfileAAA algorithm human order : ℝ)) =
                ∑ order : SourceFirmOrder,
                  ∑ human : SourceThreeFirm -> SourceFourRanking,
                    (sourceAlgorithmRankingLaw algorithm).toReal *
                      ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                        ((sourceProfileHumanRankingLaw sourceProfileAAA human).toReal *
                          (sourceFocalUtility sourceProfileAAA algorithm human order : ℝ)) := by
                    rw [Finset.sum_comm]
                    apply Finset.sum_congr rfl
                    intro order _
                    apply Finset.sum_congr rfl
                    intro human _
                    ring
            _ = ∑ order : SourceFirmOrder,
                  (sourceAlgorithmRankingLaw algorithm).toReal *
                    ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                      (sourceFocalUtility sourceProfileAAA algorithm
                        (sourceHumanRankings .r0123 .r0123 .r0123) order : ℝ) := by
                    apply Finset.sum_congr rfl
                    intro order _
                    calc
                      (∑ human : SourceThreeFirm -> SourceFourRanking,
                        (sourceAlgorithmRankingLaw algorithm).toReal *
                          ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                            ((sourceProfileHumanRankingLaw sourceProfileAAA human).toReal *
                              (sourceFocalUtility sourceProfileAAA algorithm human order : ℝ))) =
                          (sourceAlgorithmRankingLaw algorithm).toReal *
                            ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                              ∑ human : SourceThreeFirm -> SourceFourRanking,
                                (sourceProfileHumanRankingLaw sourceProfileAAA human).toReal *
                                  (sourceFocalUtility sourceProfileAAA algorithm human order : ℝ) := by
                            rw [Finset.mul_sum]
                      _ = (sourceAlgorithmRankingLaw algorithm).toReal *
                            ((sourceUniformFirmOrderMass : ℚ) : ℝ) *
                              (sourceFocalUtility sourceProfileAAA algorithm
                                (sourceHumanRankings .r0123 .r0123 .r0123) order : ℝ) := by
                            rw [sourceProfileHumanRankingLaw_AAA_weighted_sum]
    _ = ∑ algorithm : SourceFourRanking,
          ∑ order : SourceFirmOrder,
            (sourceAAAProductLaw (algorithm, order)).toReal *
              (sourceDirectRankMeanConditionalAAA algorithm order : ℝ) := by
          apply Finset.sum_congr rfl
          intro algorithm _
          apply Finset.sum_congr rfl
          intro order _
          rw [sourceAAAProductLaw, sourceFinitePMFProduct_apply_toReal,
            sourceUniformFirmOrderLaw_apply_toReal,
            sourceFocalUtility_AAA_placeholder_eq_direct]

/-- All-algorithm play has the same expected utility for every firm. -/
theorem sourceProfileExpectedUtility_AAA_labelInvariant
    (focal : SourceThreeFirm) :
    sourceProfileExpectedUtility sourceProfileAAA focal =
      sourceProfileExpectedUtility sourceProfileAAA 0 := by
  let relabel : SourceFirmPermutation := Equiv.swap 0 focal
  have h := sourceProfileExpectedUtility_relabel relabel sourceProfileAAA 0
  simpa [relabel, sourceRelabelProfile, sourceProfileAAA] using h

/-- All-human play has the same expected utility for every firm. -/
theorem sourceProfileExpectedUtility_HHH_labelInvariant
    (focal : SourceThreeFirm) :
    sourceProfileExpectedUtility sourceProfileHHH focal =
      sourceProfileExpectedUtility sourceProfileHHH 0 := by
  let relabel : SourceFirmPermutation := Equiv.swap 0 focal
  have h := sourceProfileExpectedUtility_relabel relabel sourceProfileHHH 0
  simpa [relabel, sourceRelabelProfile, sourceProfileHHH] using h

/-- A focal all-human advantage lifts to strict expected social-welfare
advantage once the raw source law's firm-label symmetry is explicit. -/
theorem sourceProfileExpectedWelfare_AAA_lt_HHH_of_focal_row
    (h : sourceProfileExpectedUtility sourceProfileAAA 0 <
      sourceProfileExpectedUtility sourceProfileHHH 0) :
    sourceProfileExpectedWelfare sourceProfileAAA <
      sourceProfileExpectedWelfare sourceProfileHHH := by
  unfold sourceProfileExpectedWelfare
  apply Finset.sum_lt_sum
  · intro focal _
    exact (calc
      sourceProfileExpectedUtility sourceProfileAAA focal =
          sourceProfileExpectedUtility sourceProfileAAA 0 :=
        sourceProfileExpectedUtility_AAA_labelInvariant focal
      _ < sourceProfileExpectedUtility sourceProfileHHH 0 := h
      _ = sourceProfileExpectedUtility sourceProfileHHH focal :=
        (sourceProfileExpectedUtility_HHH_labelInvariant focal).symm).le
  · exact ⟨0, Finset.mem_univ _, h⟩

/-- In the complete generic source experiment, a focal firm strictly prefers
the shared algorithm when its two opponents use that algorithm. -/
theorem sourceProfileExpectedUtility_AAA_gt_HAA :
    sourceProfileExpectedUtility sourceProfileHAA 0 <
      sourceProfileExpectedUtility sourceProfileAAA 0 := by
  rw [sourceProfileExpectedUtility_HAA_zero_eq_cast_direct,
    sourceProfileExpectedUtility_AAA_zero_eq_cast_direct,
    sourceDirectRankMeanExpectedHAA_eq, sourceDirectRankMeanExpectedAAA_eq]
  norm_num

/-- In the complete generic source experiment, a focal firm strictly prefers
the shared algorithm when exactly one opponent uses it. -/
theorem sourceProfileExpectedUtility_AAH_gt_HAH :
    sourceProfileExpectedUtility sourceProfileHAH 0 <
      sourceProfileExpectedUtility sourceProfileAAH 0 := by
  rw [sourceProfileExpectedUtility_HAH_zero_eq_cast_direct,
    sourceProfileExpectedUtility_AAH_zero_eq_cast_direct,
    sourceDirectRankMeanExpectedHAH_eq, sourceDirectRankMeanExpectedAAH_eq]
  norm_num

/-- In the complete generic source experiment, a focal firm strictly prefers
the shared algorithm when neither opponent uses it. -/
theorem sourceProfileExpectedUtility_AHH_gt_HHH :
    sourceProfileExpectedUtility sourceProfileHHH 0 <
      sourceProfileExpectedUtility sourceProfileAHH 0 := by
  rw [sourceProfileExpectedUtility_HHH_zero_eq_cast_direct,
    sourceProfileExpectedUtility_AHH_zero_eq_cast_direct,
    sourceDirectRankMeanExpectedHHH_eq, sourceDirectRankMeanExpectedAHH_eq]
  norm_num

/-- In the complete generic source experiment, all-human play has strictly
higher expected total selected value than all-algorithm play. -/
theorem sourceProfileExpectedUtility_AAA_lt_HHH :
    sourceProfileExpectedUtility sourceProfileAAA 0 <
      sourceProfileExpectedUtility sourceProfileHHH 0 := by
  rw [sourceProfileExpectedUtility_AAA_zero_eq_cast_direct,
    sourceProfileExpectedUtility_HHH_zero_eq_cast_direct,
    sourceDirectRankMeanExpectedAAA_eq, sourceDirectRankMeanExpectedHHH_eq]
  norm_num

/-- The full generic raw source model has strict algorithmic best responses
for every firm label and every opponent pattern, while all-human play has
strictly higher expected total selected cardinal value than all-algorithm
play.  Both conclusions are derived from the actual shared-algorithm,
independent-human, uniform-arrival source law. -/
theorem sourceGenericThreeFirmDominanceAndWelfare :
    sourcePermutationIndexedAlgorithmDominance ∧
      sourceProfileExpectedWelfare sourceProfileAAA <
        sourceProfileExpectedWelfare sourceProfileHHH := by
  constructor
  · exact sourcePermutationIndexedAlgorithmDominance_of_focal_rows
      sourceProfileExpectedUtility_AAA_gt_HAA
      sourceProfileExpectedUtility_AAH_gt_HAH
      sourceProfileExpectedUtility_AHH_gt_HHH
  · exact sourceProfileExpectedWelfare_AAA_lt_HHH_of_focal_row
      sourceProfileExpectedUtility_AAA_lt_HHH

end KR21Monoculture

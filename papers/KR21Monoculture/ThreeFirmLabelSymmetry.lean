import KR21Monoculture.DirectRankMeanBridge

open AppliedModelingLib

namespace KR21Monoculture

/-!
# Firm-label symmetry for the finite three-firm rank-mean model

The executable witness enumerates six arrival orders as an inductive type and
defines utility only for firm `0`.  This module gives the same finite sequential
model a permutation-valued arrival order and a genuinely arbitrary focal firm.
It then proves exact equivariance under relabeling firms.  The result concerns
only the rank-mean finite model; it does not identify it with the paper's
cardinal-utility experiment or prove any mixed-profile equality.
-/

/-- A firm arrival order is a permutation from arrival positions to firm labels. -/
abbrev SourceFirmPermutation := Equiv.Perm SourceThreeFirm

/-- The permutation represented by one of the six executable arrival-order atoms. -/
noncomputable def sourceFirmOrderToPermutation
    (order : SourceFirmOrder) : SourceFirmPermutation :=
  Equiv.ofBijective (sourceFirmOrderAt order) (by
    cases order <;> decide)

theorem sourceFirmOrderToPermutation_apply
    (order : SourceFirmOrder) (position : SourceThreeFirm) :
    sourceFirmOrderToPermutation order position = sourceFirmOrderAt order position := by
  rfl

/-- The six named arrival-order atoms enumerate every permutation of three firms. -/
theorem sourceFirmOrderToPermutation_bijective :
    Function.Bijective sourceFirmOrderToPermutation := by
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro order₁ order₂ h
    have hfun : sourceFirmOrderAt order₁ = sourceFirmOrderAt order₂ := by
      funext position
      exact congrFun (congrArg Equiv.toFun h) position
    cases order₁ <;> cases order₂ <;>
      simp [sourceFirmOrderAt] at hfun ⊢
  · rw [Fintype.card_perm]
    decide

/-- The rank-mean payoff of an arbitrary labeled firm after all rankings and
an arrival permutation have been fixed. -/
def sourceFirmUtility (focal : SourceThreeFirm)
    (rankings : SourceThreeFirm → SourceFourRanking)
    (order : SourceFirmPermutation) : ℚ :=
  let c0 := sourceBestAvailable (rankings (order 0)) ∅
  let c1 := sourceBestAvailable (rankings (order 1)) {c0}
  let c2 := sourceBestAvailable (rankings (order 2)) {c0, c1}
  if order 0 = focal then sourceExpectedOrderStatisticValue c0
  else if order 1 = focal then sourceExpectedOrderStatisticValue c1
  else sourceExpectedOrderStatisticValue c2

/-- The ranking map induced by an algorithm/human profile in the executable model. -/
def sourceProfileRankings (usesAlgorithm : SourceThreeFirm → Bool)
    (algorithm : SourceFourRanking)
    (human : SourceThreeFirm → SourceFourRanking) :
    SourceThreeFirm → SourceFourRanking :=
  fun firm => if usesAlgorithm firm then algorithm else human firm

/-- The existing focal-0 evaluator is exactly the generic sequential payoff. -/
theorem sourceFocalUtility_eq_sourceFirmUtility_zero
    (usesAlgorithm : SourceThreeFirm → Bool)
    (algorithm : SourceFourRanking)
    (human : SourceThreeFirm → SourceFourRanking)
    (order : SourceFirmOrder) :
    sourceFocalUtility usesAlgorithm algorithm human order =
      sourceFirmUtility 0
        (sourceProfileRankings usesAlgorithm algorithm human)
        (sourceFirmOrderToPermutation order) := by
  simp only [sourceFocalUtility, sourceFirmUtility, sourceProfileRankings,
    sourceFirmOrderToPermutation_apply]

/-- Relabel a firm-indexed ranking assignment.  The candidate rankings themselves
are unchanged; only the firm that reads each ranking is renamed. -/
def sourceRelabelRankings (relabel : SourceFirmPermutation)
    (rankings : SourceThreeFirm → SourceFourRanking) :
    SourceThreeFirm → SourceFourRanking :=
  fun firm => rankings (relabel.symm firm)

/-- Relabel an algorithm/human profile by transporting its firm index. -/
def sourceRelabelProfile (relabel : SourceFirmPermutation)
    (usesAlgorithm : SourceThreeFirm → Bool) : SourceThreeFirm → Bool :=
  fun firm => usesAlgorithm (relabel.symm firm)

theorem sourceProfileRankings_relabel
    (relabel : SourceFirmPermutation)
    (usesAlgorithm : SourceThreeFirm → Bool)
    (algorithm : SourceFourRanking)
    (human : SourceThreeFirm → SourceFourRanking) :
    sourceProfileRankings (sourceRelabelProfile relabel usesAlgorithm) algorithm
        (sourceRelabelRankings relabel human) =
      sourceRelabelRankings relabel
        (sourceProfileRankings usesAlgorithm algorithm human) := by
  funext firm
  simp [sourceProfileRankings, sourceRelabelProfile, sourceRelabelRankings]

/-- Exact firm-label equivariance of the finite sequential allocation and payoff.
The relabeled arrival order maps each old firm label through `relabel`; hence
the sequence of rankings and selected candidates is unchanged. -/
theorem sourceFirmUtility_relabel
    (relabel : SourceFirmPermutation)
    (focal : SourceThreeFirm)
    (rankings : SourceThreeFirm → SourceFourRanking)
    (order : SourceFirmPermutation) :
    sourceFirmUtility (relabel focal)
        (sourceRelabelRankings relabel rankings)
        (order.trans relabel) =
      sourceFirmUtility focal rankings order := by
  simp [sourceFirmUtility, sourceRelabelRankings]

/-- Profile-level form of exact firm-label equivariance. -/
theorem sourceFirmUtility_profile_relabel
    (relabel : SourceFirmPermutation)
    (focal : SourceThreeFirm)
    (usesAlgorithm : SourceThreeFirm → Bool)
    (algorithm : SourceFourRanking)
    (human : SourceThreeFirm → SourceFourRanking)
    (order : SourceFirmPermutation) :
    sourceFirmUtility (relabel focal)
        (sourceProfileRankings (sourceRelabelProfile relabel usesAlgorithm)
          algorithm (sourceRelabelRankings relabel human))
        (order.trans relabel) =
      sourceFirmUtility focal
        (sourceProfileRankings usesAlgorithm algorithm human)
        order := by
  rw [sourceProfileRankings_relabel]
  exact sourceFirmUtility_relabel relabel focal
    (sourceProfileRankings usesAlgorithm algorithm human) order

/-- Uniform arrival mass on the actual six-element type of firm permutations. -/
def sourceUniformFirmPermutationMass : ℚ := 1 / 6

theorem sourceUniformFirmPermutationMass_sum :
    (∑ order : SourceFirmPermutation, sourceUniformFirmPermutationMass) = 1 := by
  norm_num [sourceUniformFirmPermutationMass, Fintype.card_perm]

/-- Uniform-arrival expected rank-mean payoff of a labeled firm for a fixed
firm-indexed ranking assignment. -/
def sourceUniformArrivalFirmUtility (focal : SourceThreeFirm)
    (rankings : SourceThreeFirm → SourceFourRanking) : ℚ :=
  ∑ order : SourceFirmPermutation,
    sourceUniformFirmPermutationMass * sourceFirmUtility focal rankings order

/-- Uniform arrival is invariant under firm relabeling.  This is a genuine
change-of-variables over all six arrival permutations, not an equality assumed
from profile names. -/
theorem sourceUniformArrivalFirmUtility_relabel
    (relabel : SourceFirmPermutation)
    (focal : SourceThreeFirm)
    (rankings : SourceThreeFirm → SourceFourRanking) :
    sourceUniformArrivalFirmUtility (relabel focal)
        (sourceRelabelRankings relabel rankings) =
      sourceUniformArrivalFirmUtility focal rankings := by
  unfold sourceUniformArrivalFirmUtility
  rw [← Equiv.sum_comp (Equiv.mulLeft relabel)]
  apply Finset.sum_congr rfl
  intro order _
  change sourceUniformFirmPermutationMass *
      sourceFirmUtility (relabel focal)
        (sourceRelabelRankings relabel rankings)
        (order.trans relabel) = _
  rw [sourceFirmUtility_relabel]

/-- The original six named-order average is exactly the permutation-valued
uniform arrival average. -/
theorem sourceUniformArrivalFirmUtility_zero_eq_namedOrderAverage
    (rankings : SourceThreeFirm → SourceFourRanking) :
    sourceUniformArrivalFirmUtility 0 rankings =
      ∑ order : SourceFirmOrder,
        sourceUniformFirmOrderMass *
          sourceFirmUtility 0 rankings (sourceFirmOrderToPermutation order) := by
  unfold sourceUniformArrivalFirmUtility
  symm
  refine Fintype.sum_bijective sourceFirmOrderToPermutation
    sourceFirmOrderToPermutation_bijective
    (fun order => sourceUniformFirmOrderMass *
      sourceFirmUtility 0 rankings (sourceFirmOrderToPermutation order))
    (fun order => sourceUniformFirmPermutationMass *
      sourceFirmUtility 0 rankings order) ?_
  intro order
  rfl

/-- At an all-algorithm profile, every firm has the same uniform-arrival
rank-mean payoff for each fixed algorithm ranking. -/
theorem sourceUniformArrivalFirmUtility_AAA
    (focal : SourceThreeFirm) (algorithm : SourceFourRanking) :
    sourceUniformArrivalFirmUtility focal
        (sourceProfileRankings sourceProfileAAA algorithm
          (fun _ => algorithm)) =
      sourceUniformArrivalFirmUtility 0
        (sourceProfileRankings sourceProfileAAA algorithm
          (fun _ => algorithm)) := by
  let relabel : SourceFirmPermutation := Equiv.swap (0 : SourceThreeFirm) focal
  have hrelabeled :
      sourceRelabelRankings relabel
        (sourceProfileRankings sourceProfileAAA algorithm (fun _ => algorithm)) =
        sourceProfileRankings sourceProfileAAA algorithm (fun _ => algorithm) := by
    funext firm
    simp [sourceRelabelRankings, sourceProfileRankings, sourceProfileAAA]
  have h := sourceUniformArrivalFirmUtility_relabel relabel 0
    (sourceProfileRankings sourceProfileAAA algorithm (fun _ => algorithm))
  simpa [relabel, hrelabeled] using h

/-- At an all-human profile, every firm has the same uniform-arrival expected
rank-mean payoff when the firm-indexed human rankings are relabeled together
with the firm labels. -/
theorem sourceUniformArrivalFirmUtility_HHH_relabel
    (relabel : SourceFirmPermutation)
    (focal : SourceThreeFirm)
    (human : SourceThreeFirm → SourceFourRanking) :
    sourceUniformArrivalFirmUtility (relabel focal)
        (sourceProfileRankings (sourceRelabelProfile relabel sourceProfileHHH)
          .r0123 (sourceRelabelRankings relabel human)) =
      sourceUniformArrivalFirmUtility focal
        (sourceProfileRankings sourceProfileHHH .r0123 human) := by
  rw [sourceProfileRankings_relabel]
  exact sourceUniformArrivalFirmUtility_relabel relabel focal
    (sourceProfileRankings sourceProfileHHH .r0123 human)

/-- Product mass for independently sampled human rankings, indexed directly by
firm labels rather than by a chosen tuple order. -/
def sourceHumanProfileProductMass
    (human : SourceThreeFirm → SourceFourRanking) : ℚ :=
  ∏ firm : SourceThreeFirm, sourceHumanMallowsMass (human firm)

theorem sourceHumanProfileProductMass_sum :
    (∑ human : SourceThreeFirm → SourceFourRanking,
      sourceHumanProfileProductMass human) = 1 := by
  unfold sourceHumanProfileProductMass
  rw [← Fintype.prod_sum]
  simp [sourceHumanMallowsMass_sum]

theorem sourceHumanProfileProductMass_relabel
    (relabel : SourceFirmPermutation)
    (human : SourceThreeFirm → SourceFourRanking) :
    sourceHumanProfileProductMass (sourceRelabelRankings relabel human) =
      sourceHumanProfileProductMass human := by
  unfold sourceHumanProfileProductMass sourceRelabelRankings
  simpa using Equiv.prod_comp relabel.symm
    (fun firm => sourceHumanMallowsMass (human firm))

/-- The equivalence on human-ranking profiles induced by firm relabeling. -/
noncomputable def sourceRelabelRankingsEquiv
    (relabel : SourceFirmPermutation) :
    (SourceThreeFirm → SourceFourRanking) ≃
      (SourceThreeFirm → SourceFourRanking) :=
  Equiv.piCongrLeft' (fun _ : SourceThreeFirm => SourceFourRanking) relabel

theorem sourceRelabelRankingsEquiv_apply
    (relabel : SourceFirmPermutation)
    (human : SourceThreeFirm → SourceFourRanking) :
    sourceRelabelRankingsEquiv relabel human =
      sourceRelabelRankings relabel human := by
  rfl

/-- All-human expected rank-mean utility under independent identical human
ranking draws and a uniform arrival permutation. -/
def sourceUniformArrivalHHHIIDUtility (focal : SourceThreeFirm) : ℚ :=
  ∑ human : SourceThreeFirm → SourceFourRanking,
    sourceHumanProfileProductMass human *
      sourceUniformArrivalFirmUtility focal human

/-- In the iid all-human finite model, every firm has the same uniform-arrival
expected rank-mean payoff.  The proof reindexes the full human-ranking product
law and the full arrival-permutation law, rather than identifying labels by
profile notation. -/
theorem sourceUniformArrivalHHHIIDUtility_labelInvariant
    (relabel : SourceFirmPermutation)
    (focal : SourceThreeFirm) :
    sourceUniformArrivalHHHIIDUtility (relabel focal) =
      sourceUniformArrivalHHHIIDUtility focal := by
  unfold sourceUniformArrivalHHHIIDUtility
  rw [← Equiv.sum_comp (sourceRelabelRankingsEquiv relabel)]
  apply Finset.sum_congr rfl
  intro human _
  change sourceHumanProfileProductMass
      (sourceRelabelRankings relabel human) *
      sourceUniformArrivalFirmUtility (relabel focal)
        (sourceRelabelRankings relabel human) = _
  rw [sourceHumanProfileProductMass_relabel,
    sourceUniformArrivalFirmUtility_relabel]

/-- The direct tuple-indexed human product mass used by the executable bridge
is the same law as the firm-indexed iid profile mass. -/
theorem sourceHumanProfileProductMass_sourceHumanRankings
    (h0 h1 h2 : SourceFourRanking) :
    sourceHumanProfileProductMass (sourceHumanRankings h0 h1 h2) =
      sourceHumanTripleProductMass h0 h1 h2 := by
  classical
  unfold sourceHumanProfileProductMass sourceHumanTripleProductMass
  have huniv : (Finset.univ : Finset SourceThreeFirm) = {0, 1, 2} := by
    ext firm
    fin_cases firm <;> simp
  rw [huniv]
  simp [sourceHumanRankings]
  ring

end KR21Monoculture

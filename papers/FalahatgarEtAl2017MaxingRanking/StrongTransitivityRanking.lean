import FalahatgarEtAl2017MaxingRanking.CoreDefinitions
import AppliedModelingLib.Learning.ReinforcementLearning.Preference.PAC

/-!
# Strong-Transitivity-Ranking

Appendix B.2 estimates every pairwise preference, repeatedly selects an arm
whose estimated comparisons clear the `1 / 2 - ε / 2` threshold, and removes
it.  This file formalizes the deterministic certificate and its finite union
bound.  The executable estimator may be supplied separately.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL

/-- An arm which is at least tied with every member of an active set. -/
def AbsoluteMaximumOn {Arm : Type*} [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ) (active : Finset Arm) (selected : Arm) : Prop :=
  selected ∈ active ∧ ∀ competitor ∈ active, 0 ≤ preferenceGap selected competitor

/-- A candidate clearing Appendix B.2's estimated-gap threshold on an active set. -/
def EstimatedThresholdCandidate {Arm : Type*} [DecidableEq Arm]
    (estimate : Arm → Arm → ℝ) (epsilon : ℝ)
    (active : Finset Arm) (selected : Arm) : Prop :=
  selected ∈ active ∧ ∀ competitor ∈ active,
    -epsilon / 2 ≤ estimate selected competitor

/-- Simultaneous additive accuracy of all estimated centered pairwise preferences. -/
def PairwiseEstimateAccurate {Arm : Type*}
    (preferenceGap estimate : Arm → Arm → ℝ) (epsilon : ℝ) : Prop :=
  ∀ first second, |estimate first second - preferenceGap first second| < epsilon / 2

/--
Under the source's `ε / 2` estimate accuracy, a threshold candidate is an
`ε`-maximum of its active set.
-/
theorem estimatedThresholdCandidate_epsilonMaximumOn_of_accuracy
    {Arm : Type*} [DecidableEq Arm]
    (preferenceGap estimate : Arm → Arm → ℝ) (epsilon : ℝ)
    (active : Finset Arm) (selected : Arm)
    (haccurate : PairwiseEstimateAccurate preferenceGap estimate epsilon)
    (hthreshold : EstimatedThresholdCandidate estimate epsilon active selected) :
    EpsilonMaximumOn preferenceGap epsilon active selected := by
  refine ⟨hthreshold.1, ?_⟩
  intro competitor hcompetitor
  have herrorUpper := (abs_lt.mp (haccurate selected competitor)).2
  have hestimate := hthreshold.2 competitor hcompetitor
  linarith

/--
An absolute maximum of an active set always passes the estimated threshold
when the pairwise estimates are accurate.  This is the existence step in
Appendix B.2.
-/
theorem estimatedThresholdCandidate_of_absoluteMaximumOn_and_accuracy
    {Arm : Type*} [DecidableEq Arm]
    (preferenceGap estimate : Arm → Arm → ℝ) (epsilon : ℝ)
    (active : Finset Arm) (selected : Arm)
    (haccurate : PairwiseEstimateAccurate preferenceGap estimate epsilon)
    (hmaximum : AbsoluteMaximumOn preferenceGap active selected) :
    EstimatedThresholdCandidate estimate epsilon active selected := by
  refine ⟨hmaximum.1, ?_⟩
  intro competitor hcompetitor
  have herrorLower := (abs_lt.mp (haccurate selected competitor)).1
  have hmaximumGap := hmaximum.2 competitor hcompetitor
  linarith

/-- An exact source preference ranking supplies an absolute maximum for every
nonempty active subset: choose the active arm with the least source-ranking
index.  This is the finite-set invariant used by Algorithm 7, rather than an
extra maximal-element assumption at each iteration. -/
theorem exists_absoluteMaximumOn_of_preferenceRanking
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (ranking : Fin (Fintype.card Arm) → Arm)
    (hranking : PreferenceRanking preferenceGap ranking)
    (active : Finset Arm) (hactive : active.Nonempty) :
    ∃ selected, AbsoluteMaximumOn preferenceGap active selected := by
  classical
  let index : Arm → Fin (Fintype.card Arm) := fun arm =>
    Classical.choose (hranking.1.surjective arm)
  have hindex : ∀ arm, ranking (index arm) = arm := by
    intro arm
    exact Classical.choose_spec (hranking.1.surjective arm)
  rcases Finset.exists_min_image active index hactive with ⟨selected, hselected, hminimal⟩
  refine ⟨selected, hselected, ?_⟩
  intro competitor hcompetitor
  rw [← hindex selected, ← hindex competitor]
  exact hranking.2 (index selected) (index competitor) (hminimal competitor hcompetitor)

/-- Consequently, the source threshold set is nonempty at every nonempty
active subset when the pairwise estimates meet Algorithm 7's accuracy event. -/
theorem exists_estimatedThresholdCandidate_of_preferenceRanking_and_accuracy
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap estimate : Arm → Arm → ℝ) (epsilon : ℝ)
    (ranking : Fin (Fintype.card Arm) → Arm)
    (hranking : PreferenceRanking preferenceGap ranking)
    (haccurate : PairwiseEstimateAccurate preferenceGap estimate epsilon)
    (active : Finset Arm) (hactive : active.Nonempty) :
    ∃ selected, EstimatedThresholdCandidate estimate epsilon active selected := by
  rcases exists_absoluteMaximumOn_of_preferenceRanking preferenceGap ranking hranking active hactive
    with ⟨selected, hmaximum⟩
  exact ⟨selected, estimatedThresholdCandidate_of_absoluteMaximumOn_and_accuracy
    preferenceGap estimate epsilon active selected haccurate hmaximum⟩

/-- The finite candidate set checked in one iteration of Algorithm 7.  Its
members are precisely the active arms whose empirical centered comparisons
clear the source threshold against every remaining competitor. -/
noncomputable def estimatedThresholdCandidateSet {Arm : Type*} [DecidableEq Arm]
    (estimate : Arm → Arm → ℝ) (epsilon : ℝ) (active : Finset Arm) : Finset Arm := by
  classical
  exact active.filter fun selected =>
    ∀ competitor ∈ active, -epsilon / 2 ≤ estimate selected competitor

/-- Membership in the Algorithm-7 candidate set is its source threshold
predicate, with no abstract selection certificate hidden in the definition. -/
theorem mem_estimatedThresholdCandidateSet_iff
    {Arm : Type*} [DecidableEq Arm]
    (estimate : Arm → Arm → ℝ) (epsilon : ℝ) (active : Finset Arm) (selected : Arm) :
    selected ∈ estimatedThresholdCandidateSet estimate epsilon active ↔
      EstimatedThresholdCandidate estimate epsilon active selected := by
  classical
  simp [estimatedThresholdCandidateSet, EstimatedThresholdCandidate]

/-- The deterministic tie-break used by Algorithm 7 at one nonempty active
set.  Its fallback makes the function total; the source invariant below
proves that the fallback is never used on the successful accuracy event. -/
noncomputable def selectEstimatedThresholdCandidate {Arm : Type*}
    [Nonempty Arm] [DecidableEq Arm]
    (estimate : Arm → Arm → ℝ) (epsilon : ℝ) (active : Finset Arm) : Arm := by
  classical
  exact if hcandidate : (estimatedThresholdCandidateSet estimate epsilon active).Nonempty then
    hcandidate.choose
  else Classical.choice inferInstance

/-- On any active set containing a source-threshold candidate, the concrete
Algorithm-7 tie-break returns such a candidate. -/
theorem selectEstimatedThresholdCandidate_is_candidate
    {Arm : Type*} [Nonempty Arm] [DecidableEq Arm]
    (estimate : Arm → Arm → ℝ) (epsilon : ℝ) (active : Finset Arm)
    (hexists : ∃ selected, EstimatedThresholdCandidate estimate epsilon active selected) :
    EstimatedThresholdCandidate estimate epsilon active
      (selectEstimatedThresholdCandidate estimate epsilon active) := by
  classical
  rcases hexists with ⟨selected, hselected⟩
  have hcandidate : (estimatedThresholdCandidateSet estimate epsilon active).Nonempty := by
    refine ⟨selected, ?_⟩
    exact (mem_estimatedThresholdCandidateSet_iff estimate epsilon active selected).mpr hselected
  rw [selectEstimatedThresholdCandidate, dif_pos hcandidate]
  exact (mem_estimatedThresholdCandidateSet_iff estimate epsilon active hcandidate.choose).mp
    hcandidate.choose_spec

/-- Algorithm 7's literal active set after a given number of threshold
selections.  Each transition removes exactly the concrete empirical-threshold
candidate selected at the preceding active set. -/
noncomputable def strongTransitivityRankingActiveSet {Arm : Type*}
    [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (estimate : Arm → Arm → ℝ) (epsilon : ℝ) : ℕ → Finset Arm
  | 0 => Finset.univ
  | round + 1 =>
      (strongTransitivityRankingActiveSet estimate epsilon round).erase
        (selectEstimatedThresholdCandidate estimate epsilon
          (strongTransitivityRankingActiveSet estimate epsilon round))

/-- The concrete arm appended at one source Algorithm-7 iteration. -/
noncomputable def strongTransitivityRankingOutput {Arm : Type*}
    [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (estimate : Arm → Arm → ℝ) (epsilon : ℝ)
    (slot : Fin (Fintype.card Arm)) : Arm :=
  selectEstimatedThresholdCandidate estimate epsilon
    (strongTransitivityRankingActiveSet estimate epsilon slot.val)

/-- Later Algorithm-7 active sets are subsets of the preceding active set. -/
theorem strongTransitivityRankingActiveSet_succ_subset
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (estimate : Arm → Arm → ℝ) (epsilon : ℝ) (round : ℕ) :
    strongTransitivityRankingActiveSet estimate epsilon (round + 1) ⊆
      strongTransitivityRankingActiveSet estimate epsilon round := by
  exact Finset.erase_subset _ _

/-- If every nonempty active set has an empirical threshold candidate, the
literal Algorithm-7 active set loses exactly one arm per round. -/
theorem strongTransitivityRankingActiveSet_card_eq_sub_of_candidateExists
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (estimate : Arm → Arm → ℝ) (epsilon : ℝ)
    (hcandidate : ∀ active : Finset Arm, active.Nonempty →
      ∃ selected, EstimatedThresholdCandidate estimate epsilon active selected)
    (round : ℕ) (hround : round ≤ Fintype.card Arm) :
    (strongTransitivityRankingActiveSet estimate epsilon round).card =
      Fintype.card Arm - round := by
  induction round with
  | zero => simp [strongTransitivityRankingActiveSet]
  | succ round ih =>
      have hroundLe : round ≤ Fintype.card Arm := by omega
      have hcardPrev := ih hroundLe
      have hactive : (strongTransitivityRankingActiveSet estimate epsilon round).Nonempty := by
        apply Finset.card_pos.mp
        rw [hcardPrev]
        omega
      have hselection := selectEstimatedThresholdCandidate_is_candidate estimate epsilon
        (strongTransitivityRankingActiveSet estimate epsilon round)
        (hcandidate _ hactive)
      rw [strongTransitivityRankingActiveSet, Finset.card_erase_of_mem hselection.1, hcardPrev]
      omega

/-- The successful source invariant makes every scheduled Algorithm-7
selection an actual active threshold candidate. -/
theorem strongTransitivityRankingActiveSet_selection_is_candidate
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (preferenceGap estimate : Arm → Arm → ℝ) (epsilon : ℝ)
    (ranking : Fin (Fintype.card Arm) → Arm)
    (hranking : PreferenceRanking preferenceGap ranking)
    (haccurate : PairwiseEstimateAccurate preferenceGap estimate epsilon)
    (round : ℕ) (hround : round < Fintype.card Arm) :
    EstimatedThresholdCandidate estimate epsilon
      (strongTransitivityRankingActiveSet estimate epsilon round)
      (selectEstimatedThresholdCandidate estimate epsilon
        (strongTransitivityRankingActiveSet estimate epsilon round)) := by
  apply selectEstimatedThresholdCandidate_is_candidate
  apply exists_estimatedThresholdCandidate_of_preferenceRanking_and_accuracy
    preferenceGap estimate epsilon ranking hranking haccurate
  apply Finset.card_pos.mp
  rw [strongTransitivityRankingActiveSet_card_eq_sub_of_candidateExists estimate epsilon
    (fun active hactive =>
      exists_estimatedThresholdCandidate_of_preferenceRanking_and_accuracy
        preferenceGap estimate epsilon ranking hranking haccurate active hactive)
    round (Nat.le_of_lt hround)]
  omega

/-- Every literal output slot is a threshold candidate for the active set it
actually sees. -/
theorem strongTransitivityRankingOutput_is_candidate
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (preferenceGap estimate : Arm → Arm → ℝ) (epsilon : ℝ)
    (ranking : Fin (Fintype.card Arm) → Arm)
    (hranking : PreferenceRanking preferenceGap ranking)
    (haccurate : PairwiseEstimateAccurate preferenceGap estimate epsilon)
    (slot : Fin (Fintype.card Arm)) :
    EstimatedThresholdCandidate estimate epsilon
      (strongTransitivityRankingActiveSet estimate epsilon slot.val)
      (strongTransitivityRankingOutput estimate epsilon slot) := by
  simpa [strongTransitivityRankingOutput] using
    (strongTransitivityRankingActiveSet_selection_is_candidate
      preferenceGap estimate epsilon ranking hranking haccurate slot.val slot.isLt)

/-- The active set after any later Algorithm-7 round is contained in the
active set at every earlier round. -/
theorem strongTransitivityRankingActiveSet_subset_of_le
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (estimate : Arm → Arm → ℝ) (epsilon : ℝ) (first second : ℕ)
    (hround : first ≤ second) :
    strongTransitivityRankingActiveSet estimate epsilon second ⊆
      strongTransitivityRankingActiveSet estimate epsilon first := by
  induction second, hround using Nat.le_induction with
  | base => exact Finset.Subset.rfl
  | succ second _ ih =>
      exact (strongTransitivityRankingActiveSet_succ_subset estimate epsilon second).trans ih

/-- An arm emitted at a later output slot remains active at every earlier
output slot. -/
theorem strongTransitivityRankingOutput_mem_activeSet_of_le
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (preferenceGap estimate : Arm → Arm → ℝ) (epsilon : ℝ)
    (ranking : Fin (Fintype.card Arm) → Arm)
    (hranking : PreferenceRanking preferenceGap ranking)
    (haccurate : PairwiseEstimateAccurate preferenceGap estimate epsilon)
    (first second : Fin (Fintype.card Arm)) (horder : first.val ≤ second.val) :
    strongTransitivityRankingOutput estimate epsilon second ∈
      strongTransitivityRankingActiveSet estimate epsilon first.val := by
  have hselected := strongTransitivityRankingOutput_is_candidate
    preferenceGap estimate epsilon ranking hranking haccurate second
  exact strongTransitivityRankingActiveSet_subset_of_le estimate epsilon first.val second.val horder
    hselected.1

/-- The literal Algorithm-7 output has no duplicate arms: every selected arm
is erased before the next active state, and later outputs come from that
erased state. -/
theorem strongTransitivityRankingOutput_injective
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (preferenceGap estimate : Arm → Arm → ℝ) (epsilon : ℝ)
    (ranking : Fin (Fintype.card Arm) → Arm)
    (hranking : PreferenceRanking preferenceGap ranking)
    (haccurate : PairwiseEstimateAccurate preferenceGap estimate epsilon) :
    Function.Injective (strongTransitivityRankingOutput estimate epsilon) := by
  intro first second hequal
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hnotMem : strongTransitivityRankingOutput estimate epsilon first ∉
        strongTransitivityRankingActiveSet estimate epsilon (first.val + 1) := by
      simp [strongTransitivityRankingOutput, strongTransitivityRankingActiveSet]
    have hselected := strongTransitivityRankingOutput_is_candidate
      preferenceGap estimate epsilon ranking hranking haccurate second
    have hmember := strongTransitivityRankingActiveSet_subset_of_le estimate epsilon
      (first.val + 1) second.val (by omega) hselected.1
    apply hnotMem
    rw [hequal]
    exact hmember
  · have hnotMem : strongTransitivityRankingOutput estimate epsilon second ∉
        strongTransitivityRankingActiveSet estimate epsilon (second.val + 1) := by
      simp [strongTransitivityRankingOutput, strongTransitivityRankingActiveSet]
    have hselected := strongTransitivityRankingOutput_is_candidate
      preferenceGap estimate epsilon ranking hranking haccurate first
    have hmember := strongTransitivityRankingActiveSet_subset_of_le estimate epsilon
      (second.val + 1) first.val (by omega) hselected.1
    apply hnotMem
    rw [← hequal]
    exact hmember

/-- On the source's simultaneous accuracy event, the concrete Algorithm-7
execution returns an `epsilon`-preference ranking. -/
theorem epsilonPreferenceRanking_strongTransitivityRankingOutput_of_accuracy
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (preferenceGap estimate : Arm → Arm → ℝ) (epsilon : ℝ)
    (ranking : Fin (Fintype.card Arm) → Arm)
    (hranking : PreferenceRanking preferenceGap ranking)
    (haccurate : PairwiseEstimateAccurate preferenceGap estimate epsilon) :
    EpsilonPreferenceRanking preferenceGap epsilon
      (strongTransitivityRankingOutput estimate epsilon) := by
  refine ⟨(Fintype.bijective_iff_injective_and_card _).mpr ⟨
    strongTransitivityRankingOutput_injective preferenceGap estimate epsilon ranking hranking haccurate,
    by simp⟩, ?_⟩
  intro first second horder
  have hcandidate := strongTransitivityRankingOutput_is_candidate
    preferenceGap estimate epsilon ranking hranking haccurate first
  have hmember := strongTransitivityRankingOutput_mem_activeSet_of_le
    preferenceGap estimate epsilon ranking hranking haccurate first second horder
  have herrorUpper := (abs_lt.mp
    (haccurate (strongTransitivityRankingOutput estimate epsilon first)
      (strongTransitivityRankingOutput estimate epsilon second))).2
  have hthreshold := hcandidate.2
    (strongTransitivityRankingOutput estimate epsilon second) hmember
  linarith

/--
A certificate for the output of Strong-Transitivity-Ranking: the output is a
permutation and, at every position, its selected arm clears the estimate
threshold among precisely the arms that remain in the output suffix.
-/
def StrongTransitivityRankingCertificate {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (estimate : Arm → Arm → ℝ) (epsilon : ℝ)
    (ranking : Fin (Fintype.card Arm) → Arm) : Prop :=
  Function.Bijective ranking ∧ ∀ first,
    EstimatedThresholdCandidate estimate epsilon
      (rankingSuffix ranking first.val) (ranking first)

/--
Appendix B.2's deterministic conclusion: a threshold certificate plus uniform
pair-estimate accuracy is an `ε`-ranking.
-/
theorem epsilonPreferenceRanking_of_strongTransitivityRankingCertificate
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap estimate : Arm → Arm → ℝ) (epsilon : ℝ)
    (ranking : Fin (Fintype.card Arm) → Arm)
    (haccurate : PairwiseEstimateAccurate preferenceGap estimate epsilon)
    (hcertificate : StrongTransitivityRankingCertificate estimate epsilon ranking) :
    EpsilonPreferenceRanking preferenceGap epsilon ranking := by
  apply epsilonPreferenceRanking_of_suffixEpsilonMaximum preferenceGap epsilon ranking
    hcertificate.1
  intro first
  exact estimatedThresholdCandidate_epsilonMaximumOn_of_accuracy preferenceGap estimate epsilon
    (rankingSuffix ranking first.val) (ranking first) haccurate (hcertificate.2 first)

/-- The pair-estimation failure event used in the Appendix B.2 union bound. -/
def PairwiseEstimateFailure {Arm Outcome : Type*}
    (preferenceGap : Arm → Arm → ℝ) (estimate : Outcome → Arm → Arm → ℝ)
    (epsilon : ℝ) : Arm × Arm → Outcome → Prop :=
  fun pair outcome => ¬ |estimate outcome pair.1 pair.2 -
    preferenceGap pair.1 pair.2| < epsilon / 2

/--
Lemma 20's finite-probability reduction.  If each of the `n²` pair estimates
has failure mass at most `δ / n²`, then any output with the threshold
certificate is an `ε`-ranking except with mass at most `δ`.
-/
theorem strongTransitivityRanking_success_probability_of_pairEstimateGuarantees
    {Arm Outcome : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    (law : PMF Outcome) (preferenceGap : Arm → Arm → ℝ)
    (estimate : Outcome → Arm → Arm → ℝ) (epsilon delta : ℝ)
    (ranking : Outcome → Fin (Fintype.card Arm) → Arm)
    (hcertificate : ∀ outcome,
      StrongTransitivityRankingCertificate (estimate outcome) epsilon (ranking outcome))
    (hfailure : ∀ pair : Arm × Arm,
      pmfProbClassical law (PairwiseEstimateFailure preferenceGap estimate epsilon pair) ≤
        delta / (Fintype.card (Arm × Arm) : ℝ)) :
    1 - delta ≤ pmfProbClassical law
      (fun outcome => EpsilonPreferenceRanking preferenceGap epsilon (ranking outcome)) := by
  let failure : Arm × Arm → Outcome → Prop :=
    PairwiseEstimateFailure preferenceGap estimate epsilon
  have hsimultaneous :
      1 - delta ≤ pmfProbClassical law (AllPACSucceed failure) :=
    pmfProb_allPACSucceed_ge_one_sub law failure delta (by
      intro pair
      exact hfailure pair)
  calc
    1 - delta ≤ pmfProbClassical law (AllPACSucceed failure) := hsimultaneous
    _ ≤ pmfProbClassical law
        (fun outcome => EpsilonPreferenceRanking preferenceGap epsilon (ranking outcome)) := by
          apply pmfProbClassical_le_of_imp
          intro outcome hsuccess
          apply epsilonPreferenceRanking_of_strongTransitivityRankingCertificate
            preferenceGap (estimate outcome) epsilon (ranking outcome)
          · intro first second
            have hcall := hsuccess (first, second)
            simpa [failure, PairwiseEstimateFailure, AllPACSucceed] using hcall
          · exact hcertificate outcome

/-- Lemma 20 with Algorithm 7's concrete threshold-selection output.  Once
the source's `n²` simultaneous estimate event holds, the returned order is
derived from the literal active-set recursion above; no caller-supplied
ranking certificate remains. -/
theorem strongTransitivityRankingOutput_success_probability_of_pairEstimateGuarantees
    {Arm Outcome : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    (law : PMF Outcome) (preferenceGap : Arm → Arm → ℝ)
    (estimate : Outcome → Arm → Arm → ℝ) (epsilon delta : ℝ)
    (sourceRanking : Fin (Fintype.card Arm) → Arm)
    (hsourceRanking : PreferenceRanking preferenceGap sourceRanking)
    (hfailure : ∀ pair : Arm × Arm,
      pmfProbClassical law (PairwiseEstimateFailure preferenceGap estimate epsilon pair) ≤
        delta / (Fintype.card (Arm × Arm) : ℝ)) :
    1 - delta ≤ pmfProbClassical law
      (fun outcome => EpsilonPreferenceRanking preferenceGap epsilon
        (strongTransitivityRankingOutput (estimate outcome) epsilon)) := by
  let failure : Arm × Arm → Outcome → Prop :=
    PairwiseEstimateFailure preferenceGap estimate epsilon
  have hsimultaneous :
      1 - delta ≤ pmfProbClassical law (AllPACSucceed failure) :=
    pmfProb_allPACSucceed_ge_one_sub law failure delta (by
      intro pair
      exact hfailure pair)
  calc
    1 - delta ≤ pmfProbClassical law (AllPACSucceed failure) := hsimultaneous
    _ ≤ pmfProbClassical law
        (fun outcome => EpsilonPreferenceRanking preferenceGap epsilon
          (strongTransitivityRankingOutput (estimate outcome) epsilon)) := by
      apply pmfProbClassical_le_of_imp
      intro outcome hsuccess
      apply epsilonPreferenceRanking_strongTransitivityRankingOutput_of_accuracy
        preferenceGap (estimate outcome) epsilon sourceRanking hsourceRanking
      intro first second
      have hcall := hsuccess (first, second)
      simpa [failure, PairwiseEstimateFailure, AllPACSucceed] using hcall

end FalahatgarEtAl2017MaxingRanking

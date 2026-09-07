import AppliedModelingLib.Alignment.Axioms.LinearRanking
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Max

/-!
# Finite Kemeny aggregation

Paper-independent finite ranking language for the Kemeny objective: the total
number of ordered-pair disagreements between an output ranking and a profile.
The definitions use `Fin`-indexed voter populations so that concatenation of
two data sets is literal `Fin.addCases`; this is the form needed by ranking
separability arguments.
-/

namespace AppliedModelingLib
namespace Alignment
namespace Axioms

open SocialChoice.Ranking
open scoped BigOperators

noncomputable section

/-- Concatenate two finite voter profiles, preserving the left-to-right order. -/
def rankingProfileAppend {n leftCount rightCount : ℕ}
    (left : RankingProfile (Fin leftCount) n)
    (right : RankingProfile (Fin rightCount) n) :
    RankingProfile (Fin (leftCount + rightCount)) n :=
  Fin.addCases left right

@[simp] theorem rankingProfileAppend_left {n leftCount rightCount : ℕ}
    (left : RankingProfile (Fin leftCount) n)
    (right : RankingProfile (Fin rightCount) n) (voter : Fin leftCount) :
    rankingProfileAppend left right (Fin.castAdd rightCount voter) = left voter :=
  by simp [rankingProfileAppend]

@[simp] theorem rankingProfileAppend_right {n leftCount rightCount : ℕ}
    (left : RankingProfile (Fin leftCount) n)
    (right : RankingProfile (Fin rightCount) n) (voter : Fin rightCount) :
    rankingProfileAppend left right (Fin.natAdd leftCount voter) = right voter :=
  by simp [rankingProfileAppend]

/--
Definition C.1 of Ge et al. (2024), with a rule family indexed by the finite
number of voters.  The conclusion compares the two original equal outputs to
the output on their literal concatenation.
-/
def RankingSeparability {n : ℕ} (feasible : Ranking n → Prop)
    (rule : ∀ voterCount : ℕ, LinearRankAggregationRule (Fin voterCount) n feasible) : Prop :=
  ∀ leftCount rightCount
    (left : RankingProfile (Fin leftCount) n)
    (right : RankingProfile (Fin rightCount) n),
      (rule leftCount).run left = (rule rightCount).run right →
        (rule (leftCount + rightCount)).run (rankingProfileAppend left right) =
          (rule leftCount).run left

/--
The Kemeny disagreement count of an output ranking against a finite profile.
For every ordered candidate pair submitted in one voter's ranking, it charges
one exactly when the output reverses that pair.  This is the source's
`n_{a ≻ b}(π) · 1(b ≻_σ a)` objective written as a direct voter sum.
-/
def kemenyDisagreement {Voter : Type*} [Fintype Voter] {n : ℕ}
    (profile : RankingProfile Voter n) (output : Ranking n) : ℕ :=
  ∑ voter, ∑ first, ∑ second,
    if StrictlyPrefers (profile voter) first second ∧ StrictlyPrefers output second first then 1
    else 0

/-- The contribution to Kemeny disagreement from an arbitrary finite set of ordered pairs. -/
def kemenyDisagreementOnPairs {Voter : Type*} [Fintype Voter] {n : ℕ}
    (profile : RankingProfile Voter n) (output : Ranking n)
    (pairs : Finset (Candidate n × Candidate n)) : ℕ :=
  ∑ voter, ∑ pair ∈ pairs,
    if StrictlyPrefers (profile voter) pair.1 pair.2 ∧
        StrictlyPrefers output pair.2 pair.1 then 1 else 0

/-- Restricted Kemeny disagreement is additive across disjoint ordered-pair sets. -/
theorem kemenyDisagreementOnPairs_union {Voter : Type*} [Fintype Voter] {n : ℕ}
    (profile : RankingProfile Voter n) (output : Ranking n)
    (left right : Finset (Candidate n × Candidate n))
    (hdisjoint : Disjoint left right) :
    kemenyDisagreementOnPairs profile output (left ∪ right) =
      kemenyDisagreementOnPairs profile output left +
        kemenyDisagreementOnPairs profile output right := by
  unfold kemenyDisagreementOnPairs
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro voter _
  rw [Finset.sum_union hdisjoint]

/-- Restricted Kemeny disagreement distributes over a pairwise-disjoint finite family of pair sets. -/
theorem kemenyDisagreementOnPairs_biUnion {ι : Type*} [DecidableEq ι]
    {Voter : Type*} [Fintype Voter] {n : ℕ}
    (profile : RankingProfile Voter n) (output : Ranking n)
    (indices : Finset ι) (blocks : ι → Finset (Candidate n × Candidate n))
    (hdisjoint : ∀ left ∈ indices, ∀ right ∈ indices, left ≠ right →
      Disjoint (blocks left) (blocks right)) :
    kemenyDisagreementOnPairs profile output (indices.biUnion blocks) =
      ∑ index ∈ indices, kemenyDisagreementOnPairs profile output (blocks index) := by
  classical
  unfold kemenyDisagreementOnPairs
  have hpairwise : Set.PairwiseDisjoint (indices : Set ι) blocks := by
    intro left hleft right hright hnequal
    exact hdisjoint left (by simpa using hleft) right (by simpa using hright) hnequal
  calc
    (∑ voter, ∑ pair ∈ indices.biUnion blocks,
      if StrictlyPrefers (profile voter) pair.1 pair.2 ∧
          StrictlyPrefers output pair.2 pair.1 then 1 else 0) =
        ∑ voter, ∑ index ∈ indices, ∑ pair ∈ blocks index,
          if StrictlyPrefers (profile voter) pair.1 pair.2 ∧
              StrictlyPrefers output pair.2 pair.1 then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro voter _
          rw [Finset.sum_biUnion hpairwise]
    _ = ∑ index ∈ indices, ∑ voter, ∑ pair ∈ blocks index,
          if StrictlyPrefers (profile voter) pair.1 pair.2 ∧
              StrictlyPrefers output pair.2 pair.1 then 1 else 0 := by
          rw [Finset.sum_comm]

/-- Restricting to ordered candidate pairs can only lower the Kemeny objective. -/
theorem kemenyDisagreementOnPairs_le_kemenyDisagreement
    {Voter : Type*} [Fintype Voter] {n : ℕ}
    (profile : RankingProfile Voter n) (output : Ranking n)
    (pairs : Finset (Candidate n × Candidate n)) :
    kemenyDisagreementOnPairs profile output pairs ≤ kemenyDisagreement profile output := by
  classical
  unfold kemenyDisagreementOnPairs kemenyDisagreement
  apply Finset.sum_le_sum
  intro voter _
  calc
    (∑ pair ∈ pairs,
      if StrictlyPrefers (profile voter) pair.1 pair.2 ∧
          StrictlyPrefers output pair.2 pair.1 then 1 else 0) ≤
        ∑ pair ∈ (Finset.univ.product Finset.univ),
          if StrictlyPrefers (profile voter) pair.1 pair.2 ∧
              StrictlyPrefers output pair.2 pair.1 then 1 else 0 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro pair _
        exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩
      · intro _ _ _
        omega
    _ = ∑ first, ∑ second,
        if StrictlyPrefers (profile voter) first second ∧ StrictlyPrefers output second first then 1
        else 0 := by
      exact Finset.sum_product Finset.univ Finset.univ _

/-- Number of voters placing `first` strictly above `second`. -/
noncomputable def pairwiseSupport {Voter : Type*} [Fintype Voter] {n : ℕ}
    (profile : RankingProfile Voter n) (first second : Candidate n) : ℕ :=
  (votersSatisfying (fun voter => StrictlyPrefers (profile voter) first second)).card

/-- No voter strictly prefers a candidate to itself. -/
@[simp] theorem pairwiseSupport_self {Voter : Type*} [Fintype Voter] {n : ℕ}
    (profile : RankingProfile Voter n) (candidate : Candidate n) :
    pairwiseSupport profile candidate candidate = 0 := by
  unfold pairwiseSupport votersSatisfying
  simp [not_strictlyPrefers_self]

/--
The direct voter-by-voter Kemeny objective can be collected by ordered
candidate pairs: reversing `first ≻ second` costs exactly the number of
voters supporting that direction.
-/
theorem kemenyDisagreement_eq_pairwiseSupport_sum
    {Voter : Type*} [Fintype Voter] {n : ℕ}
    (profile : RankingProfile Voter n) (output : Ranking n) :
    kemenyDisagreement profile output =
      ∑ first, ∑ second,
        if StrictlyPrefers output second first then pairwiseSupport profile first second else 0 := by
  classical
  unfold kemenyDisagreement
  have hinner (first second : Candidate n) :
      (∑ voter,
        if StrictlyPrefers (profile voter) first second ∧
            StrictlyPrefers output second first then 1 else 0) =
        if StrictlyPrefers output second first then
          pairwiseSupport profile first second else 0 := by
    by_cases hreverse : StrictlyPrefers output second first
    · simp [hreverse, pairwiseSupport, votersSatisfying]
    · simp [hreverse]
  calc
    (∑ voter, ∑ first, ∑ second,
        if StrictlyPrefers (profile voter) first second ∧
            StrictlyPrefers output second first then 1 else 0) =
        ∑ first, ∑ second, ∑ voter,
          if StrictlyPrefers (profile voter) first second ∧
              StrictlyPrefers output second first then 1 else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro first _
      rw [Finset.sum_comm]
    _ = ∑ first, ∑ second,
        if StrictlyPrefers output second first then
          pairwiseSupport profile first second else 0 := by
      apply Finset.sum_congr rfl
      intro first _
      apply Finset.sum_congr rfl
      intro second _
      exact hinner first second

/-- The restricted Kemeny objective can likewise be collected by ordered-pair support. -/
theorem kemenyDisagreementOnPairs_eq_pairwiseSupport_sum
    {Voter : Type*} [Fintype Voter] {n : ℕ}
    (profile : RankingProfile Voter n) (output : Ranking n)
    (pairs : Finset (Candidate n × Candidate n)) :
    kemenyDisagreementOnPairs profile output pairs =
      ∑ pair ∈ pairs,
        if StrictlyPrefers output pair.2 pair.1 then
          pairwiseSupport profile pair.1 pair.2 else 0 := by
  classical
  unfold kemenyDisagreementOnPairs
  have hinner (pair : Candidate n × Candidate n) :
      (∑ voter,
        if StrictlyPrefers (profile voter) pair.1 pair.2 ∧
            StrictlyPrefers output pair.2 pair.1 then 1 else 0) =
        if StrictlyPrefers output pair.2 pair.1 then
          pairwiseSupport profile pair.1 pair.2 else 0 := by
    by_cases hreverse : StrictlyPrefers output pair.2 pair.1
    · simp [hreverse, pairwiseSupport, votersSatisfying]
    · simp [hreverse]
  calc
    (∑ voter, ∑ pair ∈ pairs,
        if StrictlyPrefers (profile voter) pair.1 pair.2 ∧
            StrictlyPrefers output pair.2 pair.1 then 1 else 0) =
        ∑ pair ∈ pairs, ∑ voter,
          if StrictlyPrefers (profile voter) pair.1 pair.2 ∧
              StrictlyPrefers output pair.2 pair.1 then 1 else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ pair ∈ pairs,
        if StrictlyPrefers output pair.2 pair.1 then
          pairwiseSupport profile pair.1 pair.2 else 0 := by
          apply Finset.sum_congr rfl
          intro pair _
          exact hinner pair

/-- The contribution of one ordered candidate pair to the Kemeny objective. -/
noncomputable def kemenyOrderedPairCost {Voter : Type*} [Fintype Voter] {n : ℕ}
    (profile : RankingProfile Voter n) (output : Ranking n)
    (first second : Candidate n) : ℕ :=
  if StrictlyPrefers output second first then pairwiseSupport profile first second else 0

/-- The collected pairwise-support formula in terms of ordered-pair costs. -/
theorem kemenyDisagreement_eq_sum_orderedPairCost
    {Voter : Type*} [Fintype Voter] {n : ℕ}
    (profile : RankingProfile Voter n) (output : Ranking n) :
    kemenyDisagreement profile output =
      ∑ first, ∑ second, kemenyOrderedPairCost profile output first second :=
  kemenyDisagreement_eq_pairwiseSupport_sum profile output

/-- Strict majority is exactly the strict pairwise-support inequality. -/
theorem strictMajorityPrefers_iff_pairwiseSupport {Voter : Type*} [Fintype Voter] {n : ℕ}
    (profile : RankingProfile Voter n) (first second : Candidate n) :
    StrictMajorityPrefers profile first second ↔
      Fintype.card Voter < 2 * pairwiseSupport profile first second := Iff.rfl

/-- Opposite pairwise-support counts partition a finite voter population. -/
theorem pairwiseSupport_add_reverse {Voter : Type*} [Fintype Voter] {n : ℕ}
    (profile : RankingProfile Voter n) {first second : Candidate n}
    (hdistinct : first ≠ second) :
    pairwiseSupport profile first second + pairwiseSupport profile second first = Fintype.card Voter := by
  classical
  let forward := votersSatisfying (fun voter => StrictlyPrefers (profile voter) first second)
  let reverse := votersSatisfying (fun voter => StrictlyPrefers (profile voter) second first)
  have hdisjoint : Disjoint forward reverse := by
    refine Finset.disjoint_left.2 ?_
    intro voter hforward hreverse
    simp only [forward, reverse, votersSatisfying,
      Finset.mem_filter, Finset.mem_univ, true_and] at hforward hreverse
    exact (lt_asymm hforward) hreverse
  have hunion : forward ∪ reverse = Finset.univ := by
    ext voter
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    simp only [forward, reverse, votersSatisfying, Finset.mem_filter, Finset.mem_univ, true_and]
    exact strictlyPrefers_or_reverse_of_ne (profile voter) hdistinct
  change forward.card + reverse.card = Fintype.card Voter
  calc
    forward.card + reverse.card = (forward ∪ reverse).card :=
      (Finset.card_union_of_disjoint hdisjoint).symm
    _ = Fintype.card Voter := by rw [hunion, Finset.card_univ]

/-- A strict pairwise majority has strictly larger support than its reverse. -/
theorem pairwiseSupport_lt_of_strictMajorityPrefers {Voter : Type*} [Fintype Voter] {n : ℕ}
    (profile : RankingProfile Voter n) {first second : Candidate n}
    (hmajority : StrictMajorityPrefers profile first second) :
    pairwiseSupport profile second first < pairwiseSupport profile first second := by
  have hdistinct : first ≠ second := by
    intro hequal
    subst second
    have hself : pairwiseSupport profile first first = 0 := by
      unfold pairwiseSupport votersSatisfying
      simp [not_strictlyPrefers_self]
    rw [strictMajorityPrefers_iff_pairwiseSupport, hself] at hmajority
    omega
  have hcard := pairwiseSupport_add_reverse profile hdistinct
  rw [strictMajorityPrefers_iff_pairwiseSupport] at hmajority
  omega

/--
For a pairwise-majority ranking, changing any other output's decision on one
unordered candidate pair cannot lower the combined ordered-pair Kemeny cost.
-/
theorem kemenyOrderedPairCost_delta_nonnegative_of_pairwiseMajorityRanking
    {Voter : Type*} [Fintype Voter] {n : ℕ}
    (profile : RankingProfile Voter n) (majorityRanking contender : Ranking n)
    (hmajority : IsPairwiseMajorityRanking profile majorityRanking)
    (first second : Candidate n) :
    0 ≤
      ((kemenyOrderedPairCost profile contender first second : ℤ) -
        kemenyOrderedPairCost profile majorityRanking first second) +
      ((kemenyOrderedPairCost profile contender second first : ℤ) -
        kemenyOrderedPairCost profile majorityRanking second first) := by
  classical
  by_cases hdistinct : first = second
  · subst second
    simp [kemenyOrderedPairCost]
  rcases strictlyPrefers_or_reverse_of_ne majorityRanking hdistinct with hmajorityForward |
    hmajorityReverse
  · have hsupport : pairwiseSupport profile second first < pairwiseSupport profile first second :=
      pairwiseSupport_lt_of_strictMajorityPrefers profile
        ((hmajority first second).mp hmajorityForward)
    have hmajorityBackward : ¬ StrictlyPrefers majorityRanking second first :=
      fun h => (lt_asymm hmajorityForward) h
    rcases strictlyPrefers_or_reverse_of_ne contender hdistinct with hcontenderForward |
      hcontenderReverse
    · have hcontenderBackward : ¬ StrictlyPrefers contender second first :=
        fun h => (lt_asymm hcontenderForward) h
      simp [kemenyOrderedPairCost, hcontenderForward, hcontenderBackward,
        hmajorityForward, hmajorityBackward]
    · have hcontenderBackward : ¬ StrictlyPrefers contender first second :=
        fun h => (lt_asymm hcontenderReverse) h
      simp [kemenyOrderedPairCost, hcontenderReverse, hcontenderBackward,
        hmajorityForward, hmajorityBackward]
      omega
  · have hsupport : pairwiseSupport profile first second < pairwiseSupport profile second first :=
      pairwiseSupport_lt_of_strictMajorityPrefers profile
        ((hmajority second first).mp hmajorityReverse)
    have hmajorityForward : ¬ StrictlyPrefers majorityRanking first second :=
      fun h => (lt_asymm hmajorityReverse) h
    rcases strictlyPrefers_or_reverse_of_ne contender hdistinct with hcontenderForward |
      hcontenderReverse
    · have hcontenderBackward : ¬ StrictlyPrefers contender second first :=
        fun h => (lt_asymm hcontenderForward) h
      simp [kemenyOrderedPairCost, hcontenderForward, hcontenderBackward,
        hmajorityForward, hmajorityReverse]
      omega
    · have hcontenderBackward : ¬ StrictlyPrefers contender first second :=
        fun h => (lt_asymm hcontenderReverse) h
      simp [kemenyOrderedPairCost, hcontenderReverse, hcontenderBackward,
        hmajorityForward, hmajorityReverse]

/--
Reversing one strict pairwise-majority comparison strictly raises the combined
ordered-pair Kemeny cost for that pair.
-/
theorem kemenyOrderedPairCost_delta_positive_of_pairwiseMajorityReversal
    {Voter : Type*} [Fintype Voter] {n : ℕ}
    (profile : RankingProfile Voter n) (majorityRanking contender : Ranking n)
    (hmajority : IsPairwiseMajorityRanking profile majorityRanking)
    (first second : Candidate n)
    (hmajorityForward : StrictlyPrefers majorityRanking first second)
    (hcontenderReverse : StrictlyPrefers contender second first) :
    0 <
      ((kemenyOrderedPairCost profile contender first second : ℤ) -
        kemenyOrderedPairCost profile majorityRanking first second) +
      ((kemenyOrderedPairCost profile contender second first : ℤ) -
        kemenyOrderedPairCost profile majorityRanking second first) := by
  have hsupport : pairwiseSupport profile second first < pairwiseSupport profile first second :=
    pairwiseSupport_lt_of_strictMajorityPrefers profile
      ((hmajority first second).mp hmajorityForward)
  have hmajorityBackward : ¬ StrictlyPrefers majorityRanking second first :=
    fun h => (lt_asymm hmajorityForward) h
  have hcontenderForward : ¬ StrictlyPrefers contender first second :=
    fun h => (lt_asymm hcontenderReverse) h
  simp [kemenyOrderedPairCost, hcontenderReverse, hcontenderForward,
    hmajorityForward, hmajorityBackward]
  omega

/-- A feasible ranking attaining the finite Kemeny minimum. -/
def IsKemenyMinimizer {Voter : Type*} [Fintype Voter] {n : ℕ}
    (feasible : Ranking n → Prop) (profile : RankingProfile Voter n)
    (output : Ranking n) : Prop :=
  feasible output ∧ ∀ contender, feasible contender →
    kemenyDisagreement profile output ≤ kemenyDisagreement profile contender

/-- A rule selects a Kemeny minimizer on every finite profile. -/
def IsKemenySelector {Voter : Type*} [Fintype Voter] {n : ℕ}
    (feasible : Ranking n → Prop) (rule : LinearRankAggregationRule Voter n feasible) : Prop :=
  ∀ profile, IsKemenyMinimizer feasible profile (rule.run profile)

/-- Two distinct finite rankings reverse at least one strict candidate pair. -/
theorem exists_strictPreferenceReversal_of_ne {n : ℕ}
    (reference contender : Ranking n) (hdifferent : reference ≠ contender) :
    ∃ first second : Candidate n,
      StrictlyPrefers reference first second ∧ StrictlyPrefers contender second first := by
  classical
  let differing : Finset (Candidate n) :=
    Finset.univ.filter (fun position => reference position ≠ contender position)
  have hexists : ∃ position, reference position ≠ contender position := by
    by_contra hnone
    push_neg at hnone
    apply hdifferent
    exact Equiv.ext (fun position => hnone position)
  obtain ⟨witness, hwitness⟩ := hexists
  have hdiffering : differing.Nonempty := by
    refine ⟨witness, ?_⟩
    simp only [differing, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hwitness
  let position : Candidate n := differing.min' hdiffering
  have hpositionMem : position ∈ differing := Finset.min'_mem differing hdiffering
  have hpositionDiff : reference position ≠ contender position := by
    simpa only [differing, Finset.mem_filter, Finset.mem_univ, true_and] using hpositionMem
  have hprefix : ∀ earlier : Candidate n, earlier < position →
      reference earlier = contender earlier := by
    intro earlier hearlier
    by_contra hdiff
    have hearlierMem : earlier ∈ differing := by
      simp only [differing, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hdiff
    have hposition_le : position ≤ earlier := Finset.min'_le differing earlier hearlierMem
    exact (not_le_of_gt hearlier) hposition_le
  let later : Candidate n := rankOf reference (contender position)
  have hreferenceLater : reference later = contender position := by
    simp only [later, rankOf]
    exact reference.apply_symm_apply _
  have hposition_lt_later : position < later := by
    by_contra hnot
    have hlater_le : later ≤ position := le_of_not_gt hnot
    rcases lt_or_eq_of_le hlater_le with hlater_lt | hlater_eq
    · have hlater_value : reference later = contender later := hprefix later hlater_lt
      have hsame : contender later = contender position :=
        hlater_value.symm.trans hreferenceLater
      exact (ne_of_lt hlater_lt) (contender.injective hsame)
    · apply hpositionDiff
      calc
        reference position = reference later := congrArg reference hlater_eq.symm
        _ = contender position := hreferenceLater
  refine ⟨reference position, contender position, ?_, ?_⟩
  · rw [← hreferenceLater]
    simpa [StrictlyPrefers, rankOf] using hposition_lt_later
  · have hcontender_position : rankOf contender (contender position) = position := by
      simp [rankOf]
    have hcontender_reference_later : position < rankOf contender (reference position) := by
      by_contra hnot
      have hrank_le : rankOf contender (reference position) ≤ position := le_of_not_gt hnot
      rcases lt_or_eq_of_le hrank_le with hlt | heq
      · have hvalue : reference (rankOf contender (reference position)) =
          contender (rankOf contender (reference position)) :=
          hprefix _ hlt
        have hcontender_value : contender (rankOf contender (reference position)) =
            reference position := by
          simp [rankOf]
        have hreference_value : reference (rankOf contender (reference position)) =
            reference position := hvalue.trans hcontender_value
        exact (ne_of_lt hlt) (reference.injective hreference_value)
      · apply hpositionDiff
        calc
          reference position = contender (rankOf contender (reference position)) := by
            simp [rankOf]
          _ = contender position := congrArg contender heq
    simpa [StrictlyPrefers, hcontender_position] using hcontender_reference_later

/--
A feasible ranking that realizes every strict pairwise majority minimizes the
finite Kemeny disagreement objective, even against rankings not themselves
compatible with the majority relation. This is the PMC core of Theorem C.3.
-/
theorem pairwiseMajorityRanking_isKemenyMinimizer
    {Voter : Type*} [Fintype Voter] {n : ℕ}
    (feasible : Ranking n → Prop) (profile : RankingProfile Voter n)
    (majorityRanking : Ranking n) (hfeasible : feasible majorityRanking)
    (hmajority : IsPairwiseMajorityRanking profile majorityRanking) :
    IsKemenyMinimizer feasible profile majorityRanking := by
  refine ⟨hfeasible, ?_⟩
  intro contender _
  let delta : Candidate n → Candidate n → ℤ := fun first second =>
    (kemenyOrderedPairCost profile contender first second : ℤ) -
      kemenyOrderedPairCost profile majorityRanking first second
  have hdelta : ∀ first second, 0 ≤ delta first second + delta second first := by
    intro first second
    exact kemenyOrderedPairCost_delta_nonnegative_of_pairwiseMajorityRanking
      profile majorityRanking contender hmajority first second
  have hdouble :
      0 ≤ ∑ first, ∑ second, (delta first second + delta second first) := by
    apply Finset.sum_nonneg
    intro first _
    apply Finset.sum_nonneg
    intro second _
    exact hdelta first second
  let total : ℤ := ∑ first, ∑ second, delta first second
  have htwice :
      total + total = ∑ first, ∑ second, (delta first second + delta second first) := by
    dsimp only [total]
    calc
      (∑ first, ∑ second, delta first second) + (∑ first, ∑ second, delta first second) =
          (∑ first, ∑ second, delta first second) +
            (∑ first, ∑ second, delta second first) := by
        rw [Finset.sum_comm]
      _ = ∑ first, ∑ second, (delta first second + delta second first) := by
        simp only [Finset.sum_add_distrib]
  have htotal : 0 ≤ total := by
    omega
  have hsum :
      (↑(∑ first, ∑ second,
        kemenyOrderedPairCost profile contender first second) : ℤ) -
        ↑(∑ first, ∑ second,
          kemenyOrderedPairCost profile majorityRanking first second) = total := by
    simp only [Nat.cast_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro first _
    rw [← Finset.sum_sub_distrib]
  have hcast : (kemenyDisagreement profile majorityRanking : ℤ) ≤
      kemenyDisagreement profile contender := by
    rw [kemenyDisagreement_eq_sum_orderedPairCost,
      kemenyDisagreement_eq_sum_orderedPairCost]
    apply sub_nonneg.mp
    rw [hsum]
    exact htotal
  exact_mod_cast hcast

/--
The Kemeny minimizer realizing a strict pairwise-majority ranking is unique:
every distinct contender incurs strictly more disagreement.
-/
theorem pairwiseMajorityRanking_kemenyDisagreement_lt_of_ne
    {Voter : Type*} [Fintype Voter] {n : ℕ}
    (profile : RankingProfile Voter n) (majorityRanking contender : Ranking n)
    (hmajority : IsPairwiseMajorityRanking profile majorityRanking)
    (hdifferent : majorityRanking ≠ contender) :
    kemenyDisagreement profile majorityRanking < kemenyDisagreement profile contender := by
  let delta : Candidate n → Candidate n → ℤ := fun first second =>
    (kemenyOrderedPairCost profile contender first second : ℤ) -
      kemenyOrderedPairCost profile majorityRanking first second
  have hdelta : ∀ first second, 0 ≤ delta first second + delta second first := by
    intro first second
    exact kemenyOrderedPairCost_delta_nonnegative_of_pairwiseMajorityRanking
      profile majorityRanking contender hmajority first second
  obtain ⟨first, second, hmajorityForward, hcontenderReverse⟩ :=
    exists_strictPreferenceReversal_of_ne majorityRanking contender hdifferent
  have hdelta_pos : 0 < delta first second + delta second first := by
    exact kemenyOrderedPairCost_delta_positive_of_pairwiseMajorityReversal
      profile majorityRanking contender hmajority first second
        hmajorityForward hcontenderReverse
  have hrow_nonnegative : ∀ first, 0 ≤ ∑ second, (delta first second + delta second first) := by
    intro first
    apply Finset.sum_nonneg
    intro second _
    exact hdelta first second
  have hrow_pos : 0 < ∑ second, (delta first second + delta second first) :=
    hdelta_pos.trans_le
      (Finset.single_le_sum (fun second _ => hdelta first second) (Finset.mem_univ second))
  have hdouble_pos :
      0 < ∑ first, ∑ second, (delta first second + delta second first) :=
    hrow_pos.trans_le
      (Finset.single_le_sum (fun first _ => hrow_nonnegative first)
        (Finset.mem_univ first))
  let total : ℤ := ∑ first, ∑ second, delta first second
  have htwice :
      total + total = ∑ first, ∑ second, (delta first second + delta second first) := by
    dsimp only [total]
    calc
      (∑ first, ∑ second, delta first second) + (∑ first, ∑ second, delta first second) =
          (∑ first, ∑ second, delta first second) +
            (∑ first, ∑ second, delta second first) := by
        rw [Finset.sum_comm]
      _ = ∑ first, ∑ second, (delta first second + delta second first) := by
        simp only [Finset.sum_add_distrib]
  have htotal_pos : 0 < total := by
    omega
  have hsum :
      (↑(∑ first, ∑ second,
        kemenyOrderedPairCost profile contender first second) : ℤ) -
        ↑(∑ first, ∑ second,
          kemenyOrderedPairCost profile majorityRanking first second) = total := by
    simp only [Nat.cast_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro first _
    rw [← Finset.sum_sub_distrib]
  have hcast : (kemenyDisagreement profile majorityRanking : ℤ) <
      kemenyDisagreement profile contender := by
    rw [kemenyDisagreement_eq_sum_orderedPairCost,
      kemenyDisagreement_eq_sum_orderedPairCost]
    apply sub_pos.mp
    rw [hsum]
    exact htotal_pos
  exact_mod_cast hcast

/-- Kemeny disagreement is additive under concatenation of two voter profiles. -/
theorem kemenyDisagreement_append {n leftCount rightCount : ℕ}
    (left : RankingProfile (Fin leftCount) n)
    (right : RankingProfile (Fin rightCount) n) (output : Ranking n) :
    kemenyDisagreement (rankingProfileAppend left right) output =
      kemenyDisagreement left output + kemenyDisagreement right output := by
  unfold kemenyDisagreement rankingProfileAppend
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right]

/--
If a ranking minimizes the Kemeny score in each profile separately, then it
minimizes their concatenated score.  A deterministic, profile-independent
tie-break is still needed to turn this minimizer statement into a rule-level
separability conclusion.
-/
theorem isKemenyMinimizer_append {n leftCount rightCount : ℕ}
    (feasible : Ranking n → Prop)
    (left : RankingProfile (Fin leftCount) n)
    (right : RankingProfile (Fin rightCount) n) (output : Ranking n)
    (hleft : IsKemenyMinimizer feasible left output)
    (hright : IsKemenyMinimizer feasible right output) :
    IsKemenyMinimizer feasible (rankingProfileAppend left right) output := by
  refine ⟨hleft.1, ?_⟩
  intro contender hcontender
  rw [kemenyDisagreement_append, kemenyDisagreement_append]
  exact Nat.add_le_add (hleft.2 contender hcontender) (hright.2 contender hcontender)

/--
A Kemeny selector with one profile-independent injective tie key.  The source
paper writes “under any consistent tie-breaking rule”; this predicate makes
that consistency mathematically explicit.  The output minimizes Kemeny
disagreement and, among all minimizers, has the least fixed key.
-/
def IsFixedTieKemenySelector {n : ℕ} (feasible : Ranking n → Prop)
    (rule : ∀ voterCount : ℕ, LinearRankAggregationRule (Fin voterCount) n feasible)
    (tieKey : Ranking n → ℕ) : Prop :=
  Function.Injective tieKey ∧
    ∀ voterCount (profile : RankingProfile (Fin voterCount) n),
      IsKemenyMinimizer feasible profile ((rule voterCount).run profile) ∧
        ∀ contender, IsKemenyMinimizer feasible profile contender →
          tieKey ((rule voterCount).run profile) ≤ tieKey contender

/--
Theorem C.3's separability conclusion for finite linear Kemeny, with the
source's implicit consistent tie-breaking made explicit by
`IsFixedTieKemenySelector`.
-/
theorem fixedTieKemenySelector_rankingSeparability {n : ℕ}
    (feasible : Ranking n → Prop)
    (rule : ∀ voterCount : ℕ, LinearRankAggregationRule (Fin voterCount) n feasible)
    (tieKey : Ranking n → ℕ)
    (hselector : IsFixedTieKemenySelector feasible rule tieKey) :
    RankingSeparability feasible rule := by
  intro leftCount rightCount left right hequal
  let output := (rule leftCount).run left
  let combinedOutput := (rule (leftCount + rightCount)).run
    (rankingProfileAppend left right)
  have hleft := hselector.2 leftCount left
  have hright := hselector.2 rightCount right
  have hrightOutput : IsKemenyMinimizer feasible right output := by
    simpa only [output] using hequal ▸ hright.1
  have hcombined := hselector.2 (leftCount + rightCount)
    (rankingProfileAppend left right)
  have houtputCombined : IsKemenyMinimizer feasible
      (rankingProfileAppend left right) output :=
    isKemenyMinimizer_append feasible left right output hleft.1 hrightOutput
  have hleftOutput_le_combined :
      kemenyDisagreement left output ≤ kemenyDisagreement left combinedOutput :=
    hleft.1.2 combinedOutput hcombined.1.1
  have hrightOutput_le_combined :
      kemenyDisagreement right output ≤ kemenyDisagreement right combinedOutput :=
    hrightOutput.2 combinedOutput hcombined.1.1
  have hcombined_le_output :
      kemenyDisagreement (rankingProfileAppend left right) combinedOutput ≤
        kemenyDisagreement (rankingProfileAppend left right) output :=
    hcombined.1.2 output houtputCombined.1
  have hleftCombined_le_output :
      kemenyDisagreement left combinedOutput ≤ kemenyDisagreement left output := by
    rw [kemenyDisagreement_append, kemenyDisagreement_append] at hcombined_le_output
    omega
  have hleftCombined : IsKemenyMinimizer feasible left combinedOutput := by
    refine ⟨hcombined.1.1, ?_⟩
    intro contender hcontender
    exact hleftCombined_le_output.trans (hleft.1.2 contender hcontender)
  have houtputKey_le : tieKey output ≤ tieKey combinedOutput :=
    hleft.2 combinedOutput hleftCombined
  have hcombinedKey_le : tieKey combinedOutput ≤ tieKey output :=
    hcombined.2 output houtputCombined
  have houtput_eq_combined : output = combinedOutput :=
    hselector.1 (le_antisymm houtputKey_le hcombinedKey_le)
  simpa only [output, combinedOutput] using houtput_eq_combined.symm

/-- A fixed, injective finite tie key for complete rankings. -/
noncomputable def rankingTieKey {n : ℕ} (ranking : Ranking n) : ℕ :=
  (Fintype.equivFin (Ranking n) ranking).val

/-- The finite ranking tie key is injective. -/
theorem rankingTieKey_injective {n : ℕ} : Function.Injective (@rankingTieKey n) := by
  intro first second hequal
  apply (Fintype.equivFin (Ranking n)).injective
  apply Fin.ext
  exact hequal

/-- The finite set of feasible Kemeny minimizers for one profile. -/
noncomputable def kemenyMinimizers {Voter : Type*} [Fintype Voter] {n : ℕ}
    (feasible : Ranking n → Prop) (profile : RankingProfile Voter n) :
    Finset (Ranking n) := by
  classical
  exact Finset.univ.filter (IsKemenyMinimizer feasible profile)

/-- Membership in the finite Kemeny minimizer set is the displayed minimizer predicate. -/
theorem mem_kemenyMinimizers_iff {Voter : Type*} [Fintype Voter] {n : ℕ}
    (feasible : Ranking n → Prop) (profile : RankingProfile Voter n)
    (output : Ranking n) :
    output ∈ kemenyMinimizers feasible profile ↔
      IsKemenyMinimizer feasible profile output := by
  classical
  simp only [kemenyMinimizers, Finset.mem_filter, Finset.mem_univ, true_and]

/-- A feasible fallback makes the finite Kemeny minimizer set nonempty. -/
theorem kemenyMinimizers_nonempty {Voter : Type*} [Fintype Voter] {n : ℕ}
    (feasible : Ranking n → Prop) (fallback : Ranking n) (hfallback : feasible fallback)
    (profile : RankingProfile Voter n) :
    (kemenyMinimizers feasible profile).Nonempty := by
  classical
  let candidates := (Finset.univ : Finset (Ranking n)).filter feasible
  have hfallbackMem : fallback ∈ candidates := by
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hfallback
  obtain ⟨output, houtputMem, hminimum⟩ :=
    Finset.exists_min_image candidates (kemenyDisagreement profile) ⟨fallback, hfallbackMem⟩
  refine ⟨output, (mem_kemenyMinimizers_iff feasible profile output).mpr ?_⟩
  refine ⟨?_, ?_⟩
  · simpa only [candidates, Finset.mem_filter, Finset.mem_univ, true_and] using houtputMem
  · intro contender hcontender
    apply hminimum contender
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hcontender

/--
A deterministic finite Kemeny selection: choose the least fixed tie key among
all feasible Kemeny minimizers.  The fallback is used only to certify that the
finite feasible domain is nonempty.
-/
noncomputable def canonicalKemenySelection {Voter : Type*} [Fintype Voter] {n : ℕ}
    (feasible : Ranking n → Prop) (fallback : Ranking n) (hfallback : feasible fallback)
    (profile : RankingProfile Voter n) :
    { output : Ranking n // IsKemenyMinimizer feasible profile output ∧
      ∀ contender, IsKemenyMinimizer feasible profile contender →
        rankingTieKey output ≤ rankingTieKey contender } := by
  classical
  let minimizers := kemenyMinimizers feasible profile
  have hminimizers : minimizers.Nonempty :=
    kemenyMinimizers_nonempty feasible fallback hfallback profile
  let tieKeys := minimizers.image rankingTieKey
  have htieKeys : tieKeys.Nonempty := by
    obtain ⟨output, houtput⟩ := hminimizers
    exact ⟨rankingTieKey output, Finset.mem_image.mpr ⟨output, houtput, rfl⟩⟩
  let key := tieKeys.min' htieKeys
  have hkeyMem : key ∈ tieKeys := Finset.min'_mem tieKeys htieKeys
  let output := Classical.choose (Finset.mem_image.mp hkeyMem)
  have houtput : output ∈ minimizers ∧ rankingTieKey output = key :=
    Classical.choose_spec (Finset.mem_image.mp hkeyMem)
  refine ⟨output, (mem_kemenyMinimizers_iff feasible profile output).mp houtput.1, ?_⟩
  intro contender hcontender
  have hcontenderMem : contender ∈ minimizers :=
    (mem_kemenyMinimizers_iff feasible profile contender).mpr hcontender
  have hcontenderKeyMem : rankingTieKey contender ∈ tieKeys :=
    Finset.mem_image.mpr ⟨contender, hcontenderMem, rfl⟩
  have hkey_le : key ≤ rankingTieKey contender := Finset.min'_le tieKeys _ hcontenderKeyMem
  exact houtput.2.symm ▸ hkey_le

/-- The canonical finite Kemeny rule. -/
noncomputable def canonicalKemenyRule {n : ℕ}
    (feasible : Ranking n → Prop) (fallback : Ranking n) (hfallback : feasible fallback)
    (voterCount : ℕ) : LinearRankAggregationRule (Fin voterCount) n feasible where
  run profile := (canonicalKemenySelection feasible fallback hfallback profile).val
  output_feasible profile :=
    (canonicalKemenySelection feasible fallback hfallback profile).property.1.1

/-- The canonical finite Kemeny rule has the fixed-tie selector property. -/
theorem canonicalKemenyRule_isFixedTieKemenySelector {n : ℕ}
    (feasible : Ranking n → Prop) (fallback : Ranking n) (hfallback : feasible fallback) :
    IsFixedTieKemenySelector feasible
      (canonicalKemenyRule feasible fallback hfallback) rankingTieKey := by
  refine ⟨rankingTieKey_injective, ?_⟩
  intro voterCount profile
  exact (canonicalKemenySelection feasible fallback hfallback profile).property

/--
The canonical finite Kemeny rule returns a feasible ranking that realizes all
strict pairwise majorities whenever one exists; fixed tie breaking is inactive
because that Kemeny minimizer is unique.
-/
theorem canonicalKemenyRule_pairwiseMajorityConsistent {n : ℕ}
    (feasible : Ranking n → Prop) (fallback : Ranking n) (hfallback : feasible fallback) :
    ∀ voterCount : ℕ,
      PairwiseMajorityConsistent feasible
        (canonicalKemenyRule feasible fallback hfallback voterCount) := by
  intro voterCount profile majorityRanking _ hfeasible hmajority
  let output := (canonicalKemenyRule feasible fallback hfallback voterCount).run profile
  have hminimum : IsKemenyMinimizer feasible profile output :=
    (canonicalKemenySelection feasible fallback hfallback profile).property.1
  change output = majorityRanking
  by_contra hdifferent
  have hstrict := pairwiseMajorityRanking_kemenyDisagreement_lt_of_ne
    profile majorityRanking output hmajority (Ne.symm hdifferent)
  exact (not_lt_of_ge (hminimum.2 majorityRanking hfeasible)) hstrict

/-- The canonical finite Kemeny rule satisfies ranking separability. -/
theorem canonicalKemenyRule_rankingSeparability {n : ℕ}
    (feasible : Ranking n → Prop) (fallback : Ranking n) (hfallback : feasible fallback) :
    RankingSeparability feasible (canonicalKemenyRule feasible fallback hfallback) :=
  fixedTieKemenySelector_rankingSeparability feasible
    (canonicalKemenyRule feasible fallback hfallback) rankingTieKey
    (canonicalKemenyRule_isFixedTieKemenySelector feasible fallback hfallback)

end
end Axioms
end Alignment
end AppliedModelingLib

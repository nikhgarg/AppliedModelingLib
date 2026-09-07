import AppliedModelingLib.Alignment.Axioms
import GeEtAl2024AlignmentAxioms.LCPO

/-!
# Source-definition interfaces: Ge et al. (2024)

Alongside the finite definition expansions, this module proves the four
components of the paper's LCPO theorem.  The concrete endpoint uses a fixed,
profile-independent Copeland tie break, making the source's arbitrary
tie-breaking convention deterministic.
-/

namespace GeEtAl2024AlignmentAxioms

open AppliedModelingLib.Alignment.Axioms
open AppliedModelingLib.SocialChoice.Ranking

/-- Definition 2.1 expands to the finite unanimous-pair condition. -/
theorem definition2_1_paretoOptimal_core
    {Voter : Type} {n : ℕ} (feasible : Ranking n → Prop)
    (rule : LinearRankAggregationRule Voter n feasible) :
    ParetoOptimal feasible rule ↔
      ∀ profile first second,
        FeasibleProfile feasible profile → UniversallyPreferred profile first second →
          StrictlyPrefers (rule.run profile) first second := Iff.rfl

/-- Definition 2.2 expands to the feasible PMC-ranking condition. -/
theorem definition2_2_pairwiseMajorityConsistent_core
    {Voter : Type} [Fintype Voter] {n : ℕ} (feasible : Ranking n → Prop)
    (rule : LinearRankAggregationRule Voter n feasible) :
    PairwiseMajorityConsistent feasible rule ↔
      ∀ profile majorityRanking,
        FeasibleProfile feasible profile → feasible majorityRanking →
          IsPairwiseMajorityRanking profile majorityRanking →
            rule.run profile = majorityRanking := Iff.rfl

/-- A complete ranking is determined by its strict pairwise comparisons. -/
theorem ranking_eq_of_strictlyPrefers_iff
    {n : ℕ} (first second : Ranking n)
    (horder : ∀ left right,
      StrictlyPrefers first left right ↔ StrictlyPrefers second left right) :
    first = second := by
  apply Equiv.ext
  intro position
  let candidate := first position
  have hsets : strictPreferenceWinnerSet first candidate =
      strictPreferenceWinnerSet second candidate := by
    classical
    ext opponent
    simp only [strictPreferenceWinnerSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact horder candidate opponent
  have hcounts := congrArg Finset.card hsets
  rw [strictPreferenceWinner_count, strictPreferenceWinner_count] at hcounts
  have hranks : rankOf first candidate = rankOf second candidate := by
    apply Fin.ext
    have hfirstBound : (rankOf first candidate).val < Fintype.card (Candidate n) := by
      simpa [Candidate] using (rankOf first candidate).isLt
    have hsecondBound : (rankOf second candidate).val < Fintype.card (Candidate n) := by
      simpa [Candidate] using (rankOf second candidate).isLt
    omega
  have hfirstRank : rankOf first candidate = position := by
    simp [candidate, rankOf]
  calc
    first position = candidate := rfl
    _ = second (rankOf second candidate) := by simp [rankOf]
    _ = second position := by rw [← hranks, hfirstRank]

/-- The source observation after Definition 2.2: a PMC ranking, when it exists, is unique. -/
theorem pairwiseMajorityRanking_unique
    {Voter : Type*} [Fintype Voter] {n : ℕ}
    (profile : RankingProfile Voter n) (first second : Ranking n)
    (hfirst : IsPairwiseMajorityRanking profile first)
    (hsecond : IsPairwiseMajorityRanking profile second) :
    first = second := by
  apply ranking_eq_of_strictlyPrefers_iff first second
  intro left right
  exact (hfirst left right).trans (hsecond left right).symm

/--
The source observation after Theorem 3.7: any C1 rule satisfying Pareto
optimality must satisfy PMC.  The comparison profile in the proof is the
unanimous profile consisting of the feasible PMC ranking itself.
-/
theorem c1_and_pareto_imply_pairwiseMajorityConsistent
    {Voter : Type*} [Fintype Voter] {n : ℕ}
    (feasible : Ranking n → Prop) (rule : LinearRankAggregationRule Voter n feasible)
    (hC1 : C1LinearRankAggregationRule feasible rule)
    (hPareto : ParetoOptimal feasible rule) :
    PairwiseMajorityConsistent feasible rule := by
  intro profile majorityRanking hprofile hmajorityFeasible hmajority
  have hmajorityComparison :
      StrictMajorityPrefers profile (majorityRanking 0) (majorityRanking 1) := by
    apply (hmajority (majorityRanking 0) (majorityRanking 1)).mp
    simp only [StrictlyPrefers, rankOf, Equiv.symm_apply_apply]
    exact Fin.zero_lt_one
  have hvoterCardPositive : 0 < Fintype.card Voter := by
    unfold StrictMajorityPrefers StrictMajority at hmajorityComparison
    have hfilterCard :
        (votersSatisfying
          (fun voter => StrictlyPrefers (profile voter)
            (majorityRanking 0) (majorityRanking 1))).card ≤ Fintype.card Voter := by
      rw [← Finset.card_univ]
      exact Finset.card_le_card (Finset.filter_subset _ _)
    omega
  letI : Nonempty Voter := Fintype.card_pos_iff.mp hvoterCardPositive
  let unanimous : RankingProfile Voter n := fun _ => majorityRanking
  have hunanimousFeasible : FeasibleProfile feasible unanimous := by
    intro voter
    exact hmajorityFeasible
  have hsameMajority : SamePairwiseMajorityRelation profile unanimous := by
    intro left right
    rw [← hmajority left right]
    constructor
    · intro hpref
      apply strictMajorityPrefers_of_universallyPreferred unanimous
      intro voter
      exact hpref
    · intro hstrict
      by_contra hpref
      by_cases heq : left = right
      · subst right
        exact not_strictMajorityPrefers_self unanimous left hstrict
      · have hreverse : StrictlyPrefers majorityRanking right left :=
          (strictlyPrefers_or_reverse_of_ne majorityRanking heq).resolve_left hpref
        have hreverseMajority : StrictMajorityPrefers unanimous right left :=
          strictMajorityPrefers_of_universallyPreferred unanimous (fun _ => hreverse)
        exact not_strictMajorityPrefers_reverse unanimous hstrict hreverseMajority
  have hunanimousOutput : rule.run unanimous = majorityRanking := by
    apply ranking_eq_of_strictlyPrefers_iff (rule.run unanimous) majorityRanking
    intro left right
    constructor
    · intro houtput
      by_contra hpref
      by_cases heq : left = right
      · subst right
        exact not_strictlyPrefers_self (rule.run unanimous) left houtput
      · have hreverse : StrictlyPrefers majorityRanking right left :=
          (strictlyPrefers_or_reverse_of_ne majorityRanking heq).resolve_left hpref
        have hparetoReverse : StrictlyPrefers (rule.run unanimous) right left :=
          hPareto unanimous right left hunanimousFeasible (fun _ => hreverse)
        exact (lt_asymm houtput) hparetoReverse
    · intro hpref
      exact hPareto unanimous left right hunanimousFeasible (fun _ => hpref)
  calc
    rule.run profile = rule.run unanimous := hC1 profile unanimous hsameMajority
    _ = majorityRanking := hunanimousOutput

/-- Definition 4.1 expands to the strict-majority top-choice condition. -/
theorem definition4_1_majorityConsistent_core
    {Voter : Type} [Fintype Voter] {n : ℕ} (feasible : Ranking n → Prop)
    (rule : LinearRankAggregationRule Voter n feasible) :
    MajorityConsistent feasible rule ↔
      ∀ profile candidate,
        FeasibleProfile feasible profile → MajorityTopChoice profile candidate →
          firstChoice (rule.run profile) = candidate := Iff.rfl

/-- Definition 4.2 expands to preservation of an elevated aggregate winner. -/
theorem definition4_2_winnerMonotonic_core
    {Voter : Type} {n : ℕ} (feasible : Ranking n → Prop)
    (rule : LinearRankAggregationRule Voter n feasible) :
    WinnerMonotonic feasible rule ↔
      ∀ original updated voter candidate,
        FeasibleProfile feasible original → FeasibleProfile feasible updated →
          firstChoice (rule.run original) = candidate →
            ProfileElevatesCandidate original updated voter candidate →
              firstChoice (rule.run updated) = candidate := Iff.rfl

/-- The Pareto-optimality part of Theorem 4.3 for a source-defined LCPO rule. -/
theorem theorem4_3_lcpo_paretoOptimal_core
    {Voter : Type} [Fintype Voter] [Nonempty Voter] {n : ℕ}
    (feasible : Ranking n → Prop) (rule : LinearRankAggregationRule Voter n feasible)
    (hselector : IsLCPOSelector feasible rule) :
    ParetoOptimal feasible rule :=
  lcpoSelector_paretoOptimal feasible rule hselector

/-- The PMC part of Theorem 4.3 for a source-defined LCPO rule. -/
theorem theorem4_3_lcpo_pairwiseMajorityConsistent_core
    {Voter : Type} [Fintype Voter] [Nonempty Voter] {n : ℕ}
    (feasible : Ranking n → Prop) (rule : LinearRankAggregationRule Voter n feasible)
    (hselector : IsLCPOSelector feasible rule) :
    PairwiseMajorityConsistent feasible rule :=
  lcpoSelector_pairwiseMajorityConsistent feasible rule hselector

/-- The majority-consistency part of Theorem 4.3 for a source-defined LCPO rule. -/
theorem theorem4_3_lcpo_majorityConsistent_core
    {Voter : Type} [Fintype Voter] [Nonempty Voter] {n : ℕ}
    (feasible : Ranking n → Prop) (rule : LinearRankAggregationRule Voter n feasible)
    (hselector : IsLCPOSelector feasible rule) :
    MajorityConsistent feasible rule :=
  lcpoSelector_majorityConsistent feasible rule hselector

/--
The finite leximax-Copeland construction satisfies the three completed parts
of source Theorem 4.3 whenever the feasible ranking domain is nonempty.
-/
theorem theorem4_3_constructed_lcpo_threeAxioms_core
    {Voter : Type} [Fintype Voter] [Nonempty Voter] {n : ℕ}
    (feasible : Ranking n → Prop) (fallback : Ranking n) (hfallback : feasible fallback) :
    ParetoOptimal feasible (leximaxCopelandRule (Voter := Voter) feasible fallback hfallback) ∧
      PairwiseMajorityConsistent feasible
        (leximaxCopelandRule (Voter := Voter) feasible fallback hfallback) ∧
        MajorityConsistent feasible
          (leximaxCopelandRule (Voter := Voter) feasible fallback hfallback) := by
  let rule : LinearRankAggregationRule Voter n feasible :=
    leximaxCopelandRule feasible fallback hfallback
  have hselector : IsLCPOSelector feasible rule :=
    leximaxCopelandRule_isLCPOSelector feasible fallback hfallback
  exact ⟨lcpoSelector_paretoOptimal feasible rule hselector,
    lcpoSelector_pairwiseMajorityConsistent feasible rule hselector,
    lcpoSelector_majorityConsistent feasible rule hselector⟩

/--
The finite fixed-tie LCPO construction satisfies all four components of source
Theorem 4.3.  Its candidate-index tie break is fixed independently of the
profile, as required by the winner-monotonicity argument.
-/
theorem theorem4_3_constructed_fixedTieLCPO_core
    {Voter : Type} [Fintype Voter] [Nonempty Voter] {n : ℕ}
    (feasible : Ranking n → Prop) (fallback : Ranking n) (hfallback : feasible fallback) :
    ParetoOptimal feasible (fixedTieLCPO (Voter := Voter) feasible fallback hfallback) ∧
      PairwiseMajorityConsistent feasible
        (fixedTieLCPO (Voter := Voter) feasible fallback hfallback) ∧
        MajorityConsistent feasible
          (fixedTieLCPO (Voter := Voter) feasible fallback hfallback) ∧
          WinnerMonotonic feasible
            (fixedTieLCPO (Voter := Voter) feasible fallback hfallback) := by
  let rule : LinearRankAggregationRule Voter n feasible :=
    fixedTieLCPO feasible fallback hfallback
  have hfixed : IsFixedTieLCPOSelector feasible rule :=
    fixedTieLCPO_isFixedTieLCPOSelector feasible fallback hfallback
  have hselector : IsLCPOSelector feasible rule :=
    isFixedTieLCPOSelector_isLCPOSelector feasible rule hfixed
  exact ⟨lcpoSelector_paretoOptimal feasible rule hselector,
    lcpoSelector_pairwiseMajorityConsistent feasible rule hselector,
    lcpoSelector_majorityConsistent feasible rule hselector,
    fixedTieLCPOSelector_winnerMonotonic feasible rule hfixed⟩

end GeEtAl2024AlignmentAxioms

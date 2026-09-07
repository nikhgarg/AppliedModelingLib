import GeEtAl2024AlignmentAxioms.LCPO
import AppliedModelingLib.Alignment.Axioms.Kemeny
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Copeland and LCPO separability instance

The explicit seven-candidate profiles from Appendix C.1 of Ge et al. (2024).
Candidates `0` through `6` correspond respectively to the source labels
`a` through `g`; each vector lists candidates from first to last position.
-/

namespace GeEtAl2024AlignmentAxioms

open AppliedModelingLib.Alignment.Axioms
open AppliedModelingLib.SocialChoice.Ranking

noncomputable section

abbrev c2Candidate := Candidate 5

/-- The first source ballot: `a ≻ g ≻ d ≻ e ≻ f ≻ b ≻ c`. -/
def c2FirstProfile_v1 : Ranking 5 :=
  { toFun := (![0, 6, 3, 4, 5, 1, 2] : c2Candidate → c2Candidate)
    invFun := (![0, 5, 6, 2, 3, 4, 1] : c2Candidate → c2Candidate)
    left_inv := by decide
    right_inv := by decide }

/-- The second ballot in the first source profile. -/
def c2FirstProfile_v2 : Ranking 5 :=
  { toFun := (![1, 0, 2, 4, 3, 6, 5] : c2Candidate → c2Candidate)
    invFun := (![1, 0, 2, 4, 3, 6, 5] : c2Candidate → c2Candidate)
    left_inv := by decide
    right_inv := by decide }

/-- The third ballot in the first source profile. -/
def c2FirstProfile_v3 : Ranking 5 :=
  { toFun := (![1, 0, 4, 3, 5, 6, 2] : c2Candidate → c2Candidate)
    invFun := (![1, 0, 6, 3, 2, 4, 5] : c2Candidate → c2Candidate)
    left_inv := by decide
    right_inv := by decide }

/-- The fourth ballot in the first source profile. -/
def c2FirstProfile_v4 : Ranking 5 :=
  { toFun := (![2, 4, 5, 6, 1, 0, 3] : c2Candidate → c2Candidate)
    invFun := (![5, 4, 0, 6, 1, 2, 3] : c2Candidate → c2Candidate)
    left_inv := by decide
    right_inv := by decide }

/-- The fifth ballot in the first source profile. -/
def c2FirstProfile_v5 : Ranking 5 :=
  { toFun := (![3, 2, 5, 6, 1, 4, 0] : c2Candidate → c2Candidate)
    invFun := (![6, 4, 1, 0, 5, 2, 3] : c2Candidate → c2Candidate)
    left_inv := by decide
    right_inv := by decide }

/-- The first five-voter profile in Appendix C.1. -/
def c2FirstProfile : RankingProfile (Fin 5) 5 :=
  ![c2FirstProfile_v1, c2FirstProfile_v2, c2FirstProfile_v3,
    c2FirstProfile_v4, c2FirstProfile_v5]

/-- The first ballot in the second source profile. -/
def c2SecondProfile_v1 : Ranking 5 :=
  { toFun := (![0, 3, 1, 5, 2, 6, 4] : c2Candidate → c2Candidate)
    invFun := (![0, 2, 4, 1, 6, 3, 5] : c2Candidate → c2Candidate)
    left_inv := by decide
    right_inv := by decide }

/-- The second ballot in the second source profile. -/
def c2SecondProfile_v2 : Ranking 5 :=
  { toFun := (![1, 0, 4, 3, 2, 6, 5] : c2Candidate → c2Candidate)
    invFun := (![1, 0, 4, 3, 2, 6, 5] : c2Candidate → c2Candidate)
    left_inv := by decide
    right_inv := by decide }

/-- The third ballot in the second source profile. -/
def c2SecondProfile_v3 : Ranking 5 :=
  { toFun := (![2, 0, 4, 1, 5, 6, 3] : c2Candidate → c2Candidate)
    invFun := (![1, 3, 0, 6, 2, 4, 5] : c2Candidate → c2Candidate)
    left_inv := by decide
    right_inv := by decide }

/-- The three-voter profile in Appendix C.1. -/
def c2SecondProfile : RankingProfile (Fin 3) 5 :=
  ![c2SecondProfile_v1, c2SecondProfile_v2, c2SecondProfile_v3]

/-- The source's combined eight-voter profile. -/
def c2CombinedProfile : RankingProfile (Fin 8) 5 :=
  ![c2FirstProfile_v1, c2FirstProfile_v2, c2FirstProfile_v3,
    c2FirstProfile_v4, c2FirstProfile_v5, c2SecondProfile_v1,
    c2SecondProfile_v2, c2SecondProfile_v3]

/-- The direct literal table agrees with the source's profile concatenation. -/
theorem c2CombinedProfile_eq_append :
    c2CombinedProfile = rankingProfileAppend c2FirstProfile c2SecondProfile := by
  funext voter
  fin_cases voter <;> rfl

/-- Every complete ranking is feasible in the source's full-rank C.2 reduction. -/
def c2AllRankingsFeasible : Ranking 5 → Prop := fun _ => True

/-- The fixed candidate-index ranking used as the full-rank fallback. -/
def c2IndexRanking : Ranking 5 := Equiv.refl c2Candidate

/-- The fixed ranking with `b` first and `a` second. -/
def c2BAIndexRanking : Ranking 5 := Equiv.swap (0 : c2Candidate) 1

/--
Two profiles have the same Copeland weak order when every strict comparison
between their Copeland scores agrees.  Since scores are natural numbers, this
also preserves their score-tie classes.
-/
def SameCopelandScoreOrder {leftCount rightCount : ℕ}
    (left : RankingProfile (Fin leftCount) 5)
    (right : RankingProfile (Fin rightCount) 5) : Prop :=
  ∀ first second : c2Candidate,
    copelandScore left first < copelandScore left second ↔
      copelandScore right first < copelandScore right second

/--
A traditional Copeland rule with a profile-independent, consistent tie break.
Strict score comparisons determine the corresponding strict output order, and
identical Copeland weak orders receive identical complete output rankings.
This states precisely the convention used in the source's phrase “under any
consistent tie-breaking rule.”
-/
def IsConsistentlyTieBrokenCopelandSelector
    (rule : ∀ voterCount : ℕ,
      LinearRankAggregationRule (Fin voterCount) 5 c2AllRankingsFeasible) : Prop :=
  (∀ (voterCount : ℕ) (profile : RankingProfile (Fin voterCount) 5)
      (first second : c2Candidate),
      copelandScore profile second < copelandScore profile first →
        StrictlyPrefers ((rule voterCount).run profile) first second) ∧
  (∀ leftCount rightCount
      (left : RankingProfile (Fin leftCount) 5)
      (right : RankingProfile (Fin rightCount) 5),
      SameCopelandScoreOrder left right →
        (rule leftCount).run left = (rule rightCount).run right)

/--
An LCPO family using the same arbitrary but fixed, profile-independent tie
convention as a consistently tied Copeland family.  Each member satisfies the
source LCPO choice condition.  Whenever the tied Copeland output belongs to
LCPO's Pareto-feasible search domain, the shared convention selects that same
output, exactly expressing the source's “LCPO coincides with Copeland” step.
-/
def IsConsistentlyTieBrokenLCPOSelector
    (copelandRule lcpoRule : ∀ voterCount : ℕ,
      LinearRankAggregationRule (Fin voterCount) 5 c2AllRankingsFeasible) : Prop :=
  IsConsistentlyTieBrokenCopelandSelector copelandRule ∧
  (∀ voterCount, IsLCPOSelector c2AllRankingsFeasible (lcpoRule voterCount)) ∧
  (∀ voterCount (profile : RankingProfile (Fin voterCount) 5),
    ParetoFeasibleRanking c2AllRankingsFeasible profile
        ((copelandRule voterCount).run profile) →
      (lcpoRule voterCount).run profile = (copelandRule voterCount).run profile)

theorem c2FirstProfile_indexRanking_respectsPareto :
    RespectsPareto c2FirstProfile c2IndexRanking := by
  decide

theorem c2SecondProfile_indexRanking_respectsPareto :
    RespectsPareto c2SecondProfile c2IndexRanking := by
  decide

theorem c2CombinedProfile_baIndexRanking_respectsPareto :
    RespectsPareto c2CombinedProfile c2BAIndexRanking := by
  decide

/-- The Copeland score table printed for the first source profile. -/
theorem c2FirstProfile_copelandScores :
    copelandScore c2FirstProfile (0 : c2Candidate) = 5 ∧
      copelandScore c2FirstProfile (1 : c2Candidate) = 4 ∧
      copelandScore c2FirstProfile (2 : c2Candidate) = 3 ∧
      copelandScore c2FirstProfile (3 : c2Candidate) = 3 ∧
      copelandScore c2FirstProfile (4 : c2Candidate) = 3 ∧
      copelandScore c2FirstProfile (5 : c2Candidate) = 2 ∧
      copelandScore c2FirstProfile (6 : c2Candidate) = 1 := by
  decide

/-- The Copeland score table printed for the second source profile. -/
theorem c2SecondProfile_copelandScores :
    copelandScore c2SecondProfile (0 : c2Candidate) = 6 ∧
      copelandScore c2SecondProfile (1 : c2Candidate) = 5 ∧
      copelandScore c2SecondProfile (2 : c2Candidate) = 3 ∧
      copelandScore c2SecondProfile (3 : c2Candidate) = 3 ∧
      copelandScore c2SecondProfile (4 : c2Candidate) = 3 ∧
      copelandScore c2SecondProfile (5 : c2Candidate) = 1 ∧
      copelandScore c2SecondProfile (6 : c2Candidate) = 0 := by
  decide

/-- In the combined source profile, `b` has Copeland score six and exceeds `a`. -/
theorem c2CombinedProfile_copelandScore_b_gt_a :
    copelandScore c2CombinedProfile (0 : c2Candidate) = 5 ∧
      copelandScore c2CombinedProfile (1 : c2Candidate) = 6 := by
  decide

/-- The two component profiles have exactly the same Copeland weak order. -/
theorem c2ComponentProfiles_sameCopelandScoreOrder :
    SameCopelandScoreOrder c2FirstProfile c2SecondProfile := by
  intro first second
  fin_cases first <;> fin_cases second <;> decide

/-- Every consistently tied Copeland output respects Pareto on the first C.2 profile. -/
theorem c2FirstProfile_copelandSelector_respectsPareto
    (rule : ∀ voterCount : ℕ,
      LinearRankAggregationRule (Fin voterCount) 5 c2AllRankingsFeasible)
    (hcopeland : IsConsistentlyTieBrokenCopelandSelector rule) :
    RespectsPareto c2FirstProfile ((rule 5).run c2FirstProfile) := by
  intro first second huniversal
  apply hcopeland.1 5 c2FirstProfile first second
  have hscore : ∀ first second : c2Candidate,
      UniversallyPreferred c2FirstProfile first second →
        copelandScore c2FirstProfile second < copelandScore c2FirstProfile first := by
    decide
  exact hscore first second huniversal

/-- Every consistently tied Copeland output respects Pareto on the second C.2 profile. -/
theorem c2SecondProfile_copelandSelector_respectsPareto
    (rule : ∀ voterCount : ℕ,
      LinearRankAggregationRule (Fin voterCount) 5 c2AllRankingsFeasible)
    (hcopeland : IsConsistentlyTieBrokenCopelandSelector rule) :
    RespectsPareto c2SecondProfile ((rule 3).run c2SecondProfile) := by
  intro first second huniversal
  apply hcopeland.1 3 c2SecondProfile first second
  have hscore : ∀ first second : c2Candidate,
      UniversallyPreferred c2SecondProfile first second →
        copelandScore c2SecondProfile second < copelandScore c2SecondProfile first := by
    decide
  exact hscore first second huniversal

theorem c2FirstProfile_a_score_gt_of_ne (candidate : c2Candidate)
    (hcandidate : candidate ≠ 0) :
    copelandScore c2FirstProfile candidate < copelandScore c2FirstProfile 0 := by
  rcases c2FirstProfile_copelandScores with ⟨ha, hb, hc, hd, he, hf, hg⟩
  fin_cases candidate <;> simp_all

theorem c2SecondProfile_a_score_gt_of_ne (candidate : c2Candidate)
    (hcandidate : candidate ≠ 0) :
    copelandScore c2SecondProfile candidate < copelandScore c2SecondProfile 0 := by
  rcases c2SecondProfile_copelandScores with ⟨ha, hb, hc, hd, he, hf, hg⟩
  fin_cases candidate <;> simp_all

theorem c2CombinedProfile_b_score_gt_of_ne (candidate : c2Candidate)
    (hcandidate : candidate ≠ 1) :
    copelandScore c2CombinedProfile candidate < copelandScore c2CombinedProfile 1 := by
  fin_cases candidate <;> simp_all <;> decide

/-- Every LCPO selector starts the first C.2 component profile with `a`. -/
theorem c2FirstProfile_lcpo_firstChoice
    (rule : LinearRankAggregationRule (Fin 5) 5 c2AllRankingsFeasible)
    (hlcpo : IsLCPOSelector c2AllRankingsFeasible rule) :
    firstChoice (rule.run c2FirstProfile) = (0 : c2Candidate) := by
  let outcome := rule.run c2FirstProfile
  have hprofile : FeasibleProfile c2AllRankingsFeasible c2FirstProfile := by
    intro voter
    trivial
  have houtcome : IsLCPOOutcome c2AllRankingsFeasible c2FirstProfile outcome :=
    hlcpo c2FirstProfile hprofile
  have hcanPlace : CanPlaceAt c2AllRankingsFeasible c2FirstProfile outcome 0 0 :=
    canPlaceAt_zero_of_paretoFeasibleRanking c2AllRankingsFeasible c2FirstProfile
      outcome c2IndexRanking 0 ⟨trivial, c2FirstProfile_indexRanking_respectsPareto⟩ (by rfl)
  change firstChoice outcome = 0
  by_contra hnot
  have hscoreLower := isLCPOOutcome_firstScore_maximal
    c2AllRankingsFeasible c2FirstProfile outcome houtcome 0 hcanPlace
  have hstrict := c2FirstProfile_a_score_gt_of_ne (firstChoice outcome) hnot
  exact (not_lt_of_ge hscoreLower) hstrict

/-- Every LCPO selector starts the combined C.2 profile with `b`. -/
theorem c2CombinedProfile_lcpo_firstChoice
    (rule : LinearRankAggregationRule (Fin 8) 5 c2AllRankingsFeasible)
    (hlcpo : IsLCPOSelector c2AllRankingsFeasible rule) :
    firstChoice (rule.run c2CombinedProfile) = (1 : c2Candidate) := by
  let outcome := rule.run c2CombinedProfile
  have hprofile : FeasibleProfile c2AllRankingsFeasible c2CombinedProfile := by
    intro voter
    trivial
  have houtcome : IsLCPOOutcome c2AllRankingsFeasible c2CombinedProfile outcome :=
    hlcpo c2CombinedProfile hprofile
  have hcanPlace : CanPlaceAt c2AllRankingsFeasible c2CombinedProfile outcome 0 1 :=
    canPlaceAt_zero_of_paretoFeasibleRanking c2AllRankingsFeasible c2CombinedProfile
      outcome c2BAIndexRanking 1
      ⟨trivial, c2CombinedProfile_baIndexRanking_respectsPareto⟩ (by rfl)
  change firstChoice outcome = 1
  by_contra hnot
  have hscoreLower := isLCPOOutcome_firstScore_maximal
    c2AllRankingsFeasible c2CombinedProfile outcome houtcome 1 hcanPlace
  have hstrict := c2CombinedProfile_b_score_gt_of_ne (firstChoice outcome) hnot
  exact (not_lt_of_ge hscoreLower) hstrict

/-- In the first source profile, every lower index is better in the fixed Copeland order. -/
theorem c2FirstProfile_indexCopelandBetter :
    ∀ earlier later : c2Candidate, earlier < later →
      CopelandBetter c2FirstProfile earlier later := by
  intro earlier later hlt
  fin_cases earlier <;> fin_cases later <;> simp_all <;> decide

/-- In the second source profile, every lower index is better in the fixed Copeland order. -/
theorem c2SecondProfile_indexCopelandBetter :
    ∀ earlier later : c2Candidate, earlier < later →
      CopelandBetter c2SecondProfile earlier later := by
  intro earlier later hlt
  fin_cases earlier <;> fin_cases later <;> simp_all <;> decide

/-- The fixed-tie LCPO outcome on the first source profile starts with `a`. -/
theorem c2FirstProfile_fixedTieLCPO_firstChoice :
    firstChoice ((fixedTieLCPO (Voter := Fin 5) c2AllRankingsFeasible
      c2IndexRanking (by trivial)).run c2FirstProfile) = (0 : c2Candidate) := by
  let rule := fixedTieLCPO (Voter := Fin 5) c2AllRankingsFeasible
    c2IndexRanking (by trivial)
  let outcome := rule.run c2FirstProfile
  have hprofile : FeasibleProfile c2AllRankingsFeasible c2FirstProfile := by
    intro voter
    trivial
  have houtcome := fixedTieLCPO_isFixedTieLCPOSelector
    (Voter := Fin 5) c2AllRankingsFeasible c2IndexRanking (by trivial)
    c2FirstProfile hprofile
  have hcanPlace : CanPlaceAt c2AllRankingsFeasible c2FirstProfile outcome 0 0 :=
    canPlaceAt_zero_of_paretoFeasibleRanking c2AllRankingsFeasible c2FirstProfile
      outcome c2IndexRanking 0 ⟨trivial, c2FirstProfile_indexRanking_respectsPareto⟩ (by rfl)
  change firstChoice outcome = 0
  by_contra hnot
  have hbetter : CopelandBetter c2FirstProfile 0 (firstChoice outcome) := Or.inl
    (c2FirstProfile_a_score_gt_of_ne (firstChoice outcome) hnot)
  exact houtcome.2 0 0 hcanPlace hbetter

/-- The fixed-tie LCPO outcome on the second source profile starts with `a`. -/
theorem c2SecondProfile_fixedTieLCPO_firstChoice :
    firstChoice ((fixedTieLCPO (Voter := Fin 3) c2AllRankingsFeasible
      c2IndexRanking (by trivial)).run c2SecondProfile) = (0 : c2Candidate) := by
  let rule := fixedTieLCPO (Voter := Fin 3) c2AllRankingsFeasible
    c2IndexRanking (by trivial)
  let outcome := rule.run c2SecondProfile
  have hprofile : FeasibleProfile c2AllRankingsFeasible c2SecondProfile := by
    intro voter
    trivial
  have houtcome := fixedTieLCPO_isFixedTieLCPOSelector
    (Voter := Fin 3) c2AllRankingsFeasible c2IndexRanking (by trivial)
    c2SecondProfile hprofile
  have hcanPlace : CanPlaceAt c2AllRankingsFeasible c2SecondProfile outcome 0 0 :=
    canPlaceAt_zero_of_paretoFeasibleRanking c2AllRankingsFeasible c2SecondProfile
      outcome c2IndexRanking 0 ⟨trivial, c2SecondProfile_indexRanking_respectsPareto⟩ (by rfl)
  change firstChoice outcome = 0
  by_contra hnot
  have hbetter : CopelandBetter c2SecondProfile 0 (firstChoice outcome) := Or.inl
    (c2SecondProfile_a_score_gt_of_ne (firstChoice outcome) hnot)
  exact houtcome.2 0 0 hcanPlace hbetter

/-- The complete fixed-tie LCPO output on the first source profile is `a ≻ ⋯ ≻ g`. -/
theorem c2FirstProfile_fixedTieLCPO_eq_indexRanking :
    (fixedTieLCPO (Voter := Fin 5) c2AllRankingsFeasible
      c2IndexRanking (by trivial)).run c2FirstProfile = c2IndexRanking := by
  apply isFixedTieLCPOOutcome_eq_of_strictCopelandBetter
    c2AllRankingsFeasible c2FirstProfile
  · exact fixedTieLCPO_isFixedTieLCPOSelector
      (Voter := Fin 5) c2AllRankingsFeasible c2IndexRanking (by trivial)
      c2FirstProfile (by intro voter; trivial)
  · exact ⟨trivial, c2FirstProfile_indexRanking_respectsPareto⟩
  · exact c2FirstProfile_indexCopelandBetter

/-- The complete fixed-tie LCPO output on the second source profile is `a ≻ ⋯ ≻ g`. -/
theorem c2SecondProfile_fixedTieLCPO_eq_indexRanking :
    (fixedTieLCPO (Voter := Fin 3) c2AllRankingsFeasible
      c2IndexRanking (by trivial)).run c2SecondProfile = c2IndexRanking := by
  apply isFixedTieLCPOOutcome_eq_of_strictCopelandBetter
    c2AllRankingsFeasible c2SecondProfile
  · exact fixedTieLCPO_isFixedTieLCPOSelector
      (Voter := Fin 3) c2AllRankingsFeasible c2IndexRanking (by trivial)
      c2SecondProfile (by intro voter; trivial)
  · exact ⟨trivial, c2SecondProfile_indexRanking_respectsPareto⟩
  · exact c2SecondProfile_indexCopelandBetter

/-- The combined fixed-tie LCPO outcome starts with `b`, not `a`. -/
theorem c2CombinedProfile_fixedTieLCPO_firstChoice :
    firstChoice ((fixedTieLCPO (Voter := Fin 8) c2AllRankingsFeasible
      c2IndexRanking (by trivial)).run c2CombinedProfile) = (1 : c2Candidate) := by
  let rule := fixedTieLCPO (Voter := Fin 8) c2AllRankingsFeasible
    c2IndexRanking (by trivial)
  let outcome := rule.run c2CombinedProfile
  have hprofile : FeasibleProfile c2AllRankingsFeasible c2CombinedProfile := by
    intro voter
    trivial
  have houtcome := fixedTieLCPO_isFixedTieLCPOSelector
    (Voter := Fin 8) c2AllRankingsFeasible c2IndexRanking (by trivial)
    c2CombinedProfile hprofile
  have hcanPlace : CanPlaceAt c2AllRankingsFeasible c2CombinedProfile outcome 0 1 :=
    canPlaceAt_zero_of_paretoFeasibleRanking c2AllRankingsFeasible c2CombinedProfile
      outcome c2BAIndexRanking 1
      ⟨trivial, c2CombinedProfile_baIndexRanking_respectsPareto⟩ (by rfl)
  change firstChoice outcome = 1
  by_contra hnot
  have hbetter : CopelandBetter c2CombinedProfile 1 (firstChoice outcome) := Or.inl
    (c2CombinedProfile_b_score_gt_of_ne (firstChoice outcome) hnot)
  exact houtcome.2 0 1 hcanPlace hbetter

/-- The fixed-tie LCPO family in the source's full-ranking C.2 reduction. -/
noncomputable def c2FixedTieLCPOFamily (voterCount : ℕ) :
    LinearRankAggregationRule (Fin voterCount) 5 c2AllRankingsFeasible := by
  cases voterCount with
  | zero =>
      exact
        { run := fun _ => c2IndexRanking
          output_feasible := fun _ => trivial }
  | succ voterCount =>
      exact fixedTieLCPO c2AllRankingsFeasible c2IndexRanking (by trivial)

/--
The Appendix-C.1 profiles violate ranking separability for fixed-tie LCPO:
both components output the same full index ranking, while the concatenation
puts `b` rather than `a` first.
-/
theorem theoremC_2_fixedTieLCPO_failsRankingSeparability :
    ¬ RankingSeparability c2AllRankingsFeasible c2FixedTieLCPOFamily := by
  intro hseparable
  have hcomponents :
      (c2FixedTieLCPOFamily 5).run c2FirstProfile =
        (c2FixedTieLCPOFamily 3).run c2SecondProfile := by
    simpa [c2FixedTieLCPOFamily] using
      c2FirstProfile_fixedTieLCPO_eq_indexRanking.trans
        c2SecondProfile_fixedTieLCPO_eq_indexRanking.symm
  have hcombined := hseparable 5 3 c2FirstProfile c2SecondProfile hcomponents
  have hfirst := congrArg firstChoice hcombined
  have hfirstComponent :
      firstChoice ((c2FixedTieLCPOFamily 5).run c2FirstProfile) = (0 : c2Candidate) := by
    simpa [c2FixedTieLCPOFamily] using c2FirstProfile_fixedTieLCPO_firstChoice
  have hfirstCombined :
      firstChoice ((c2FixedTieLCPOFamily (5 + 3)).run
        (rankingProfileAppend c2FirstProfile c2SecondProfile)) = (1 : c2Candidate) := by
    simpa [c2FixedTieLCPOFamily, c2CombinedProfile_eq_append] using
      c2CombinedProfile_fixedTieLCPO_firstChoice
  have hone_eq_zero : (1 : c2Candidate) = 0 :=
    hfirstCombined.symm.trans (hfirst.trans hfirstComponent)
  exact Fin.zero_ne_one hone_eq_zero.symm

/--
The literal source profiles refute ranking separability for LCPO under every
fixed, profile-independent tie convention, not merely the concrete index tie
order used by `c2FixedTieLCPOFamily`.
-/
theorem theoremC_2_consistentlyTieBrokenLCPO_failsRankingSeparability
    (copelandRule lcpoRule : ∀ voterCount : ℕ,
      LinearRankAggregationRule (Fin voterCount) 5 c2AllRankingsFeasible)
    (hlcpo : IsConsistentlyTieBrokenLCPOSelector copelandRule lcpoRule) :
    ¬ RankingSeparability c2AllRankingsFeasible lcpoRule := by
  intro hseparable
  have hcopelandComponents :
      (copelandRule 5).run c2FirstProfile =
        (copelandRule 3).run c2SecondProfile :=
    hlcpo.1.2 5 3 c2FirstProfile c2SecondProfile
      c2ComponentProfiles_sameCopelandScoreOrder
  have hfirstCopelandPareto : ParetoFeasibleRanking c2AllRankingsFeasible
      c2FirstProfile ((copelandRule 5).run c2FirstProfile) :=
    ⟨trivial, c2FirstProfile_copelandSelector_respectsPareto copelandRule hlcpo.1⟩
  have hsecondCopelandPareto : ParetoFeasibleRanking c2AllRankingsFeasible
      c2SecondProfile ((copelandRule 3).run c2SecondProfile) :=
    ⟨trivial, c2SecondProfile_copelandSelector_respectsPareto copelandRule hlcpo.1⟩
  have hcomponents :
      (lcpoRule 5).run c2FirstProfile = (lcpoRule 3).run c2SecondProfile :=
    (hlcpo.2.2 5 c2FirstProfile hfirstCopelandPareto).trans
      (hcopelandComponents.trans
        (hlcpo.2.2 3 c2SecondProfile hsecondCopelandPareto).symm)
  have hcombined := hseparable 5 3 c2FirstProfile c2SecondProfile hcomponents
  have hfirst := congrArg firstChoice hcombined
  have hfirstComponent :
      firstChoice ((lcpoRule 5).run c2FirstProfile) = (0 : c2Candidate) :=
    c2FirstProfile_lcpo_firstChoice (lcpoRule 5) (hlcpo.2.1 5)
  have hfirstCombined :
      firstChoice ((lcpoRule (5 + 3)).run
        (rankingProfileAppend c2FirstProfile c2SecondProfile)) = (1 : c2Candidate) := by
    simpa [c2CombinedProfile_eq_append] using
      c2CombinedProfile_lcpo_firstChoice (lcpoRule 8) (hlcpo.2.1 8)
  have hone_eq_zero : (1 : c2Candidate) = 0 :=
    hfirstCombined.symm.trans (hfirst.trans hfirstComponent)
  exact Fin.zero_ne_one hone_eq_zero.symm

/--
The literal source profiles refute ranking separability for every traditional
Copeland selector whose tie resolution is profile-independent in the precise
score-order sense above.
-/
theorem theoremC_2_consistentlyTieBrokenCopeland_failsRankingSeparability
    (rule : ∀ voterCount : ℕ,
      LinearRankAggregationRule (Fin voterCount) 5 c2AllRankingsFeasible)
    (hcopeland : IsConsistentlyTieBrokenCopelandSelector rule) :
    ¬ RankingSeparability c2AllRankingsFeasible rule := by
  intro hseparable
  have hcomponents :
      (rule 5).run c2FirstProfile = (rule 3).run c2SecondProfile :=
    hcopeland.2 5 3 c2FirstProfile c2SecondProfile
      c2ComponentProfiles_sameCopelandScoreOrder
  have hcombined := hseparable 5 3 c2FirstProfile c2SecondProfile hcomponents
  have hab : StrictlyPrefers ((rule 5).run c2FirstProfile)
      (0 : c2Candidate) 1 :=
    hcopeland.1 5 c2FirstProfile 0 1 (by decide)
  have hba : StrictlyPrefers ((rule 8).run c2CombinedProfile)
      (1 : c2Candidate) 0 :=
    hcopeland.1 8 c2CombinedProfile 1 0 (by decide)
  have hcombined' :
      (rule 8).run c2CombinedProfile = (rule 5).run c2FirstProfile := by
    simpa [c2CombinedProfile_eq_append] using hcombined
  rw [hcombined'] at hba
  exact (lt_asymm hab) hba

end

end GeEtAl2024AlignmentAxioms

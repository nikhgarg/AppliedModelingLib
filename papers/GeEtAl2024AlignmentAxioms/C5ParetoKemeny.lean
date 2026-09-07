import GeEtAl2024AlignmentAxioms.C4LinearKemeny
import GeEtAl2024AlignmentAxioms.LCPO

/-!
# Theorem C.5 source instance: Kemeny subject to Pareto optimality

The second profile is the literal three-voter construction in Appendix C.2:
two copies of the first C.4 ballot and the displayed `2 ≻ 1` ballot.  The
source writes “without loss of generality” for the first profile's Kemeny tie;
we make that choice a single fixed, profile-independent ranking key below.
-/

namespace GeEtAl2024AlignmentAxioms

open AppliedModelingLib.Alignment.Axioms
open AppliedModelingLib.SocialChoice.Ranking

/-- The literal three-voter profile in source Theorem C.5. -/
def c5SecondProfile : RankingProfile (Fin 3) 18 :=
  ![c4Ranking_v1, c4Ranking_v1, c4TwoAboveOneRanking]

/-- The literal combined nine-voter profile in source Theorem C.5. -/
def c5CombinedProfile : RankingProfile (Fin 9) 18 :=
  rankingProfileAppend c4Profile c5SecondProfile

/-- Every submitted ballot in the second profile is feature-linearly feasible. -/
theorem c5SecondProfile_linearFeasible :
    FeasibleProfile (LinearFeasibleRanking c4Features) c5SecondProfile := by
  intro voter
  fin_cases voter
  · exact c4Profile_linearFeasible 0
  · exact c4Profile_linearFeasible 0
  · exact c4TwoAboveOneRanking_linearFeasible

/-- Every submitted ballot in the combined profile is feature-linearly feasible. -/
theorem c5CombinedProfile_linearFeasible :
    FeasibleProfile (LinearFeasibleRanking c4Features) c5CombinedProfile := by
  intro voter
  unfold c5CombinedProfile rankingProfileAppend
  refine Fin.addCases
    (motive := fun index =>
      LinearFeasibleRanking c4Features (Fin.addCases c4Profile c5SecondProfile index)) ?_ ?_ voter
  · intro leftVoter
    simpa using c4Profile_linearFeasible leftVoter
  · intro rightVoter
    simpa using c5SecondProfile_linearFeasible rightVoter

/-- The first ballot realizes every strict pairwise majority in the second profile. -/
theorem c5SecondProfile_v1_isPairwiseMajorityRanking :
    IsPairwiseMajorityRanking c5SecondProfile c4Ranking_v1 := by
  intro first second
  constructor
  · intro hv1
    unfold StrictMajorityPrefers StrictMajority
    have hsubset : ({(0 : Fin 3), 1} : Finset (Fin 3)) ⊆
        votersSatisfying (fun voter => StrictlyPrefers (c5SecondProfile voter) first second) := by
      intro voter hvoter
      simp only [Finset.mem_insert, Finset.mem_singleton] at hvoter
      rcases hvoter with hzero | hone
      · subst voter
        simp only [votersSatisfying, Finset.mem_filter, Finset.mem_univ, true_and]
        simpa [c5SecondProfile] using hv1
      · subst voter
        simp only [votersSatisfying, Finset.mem_filter, Finset.mem_univ, true_and]
        simpa [c5SecondProfile] using hv1
    have hcard := Finset.card_le_card hsubset
    norm_num at hcard ⊢
    omega
  · intro hmajority
    have hne : first ≠ second := by
      intro hequal
      subst second
      unfold StrictMajorityPrefers StrictMajority votersSatisfying at hmajority
      simp at hmajority
    rcases strictlyPrefers_or_reverse_of_ne c4Ranking_v1 hne with hv1 | hreverse
    · exact hv1
    · unfold StrictMajorityPrefers StrictMajority at hmajority
      have hsubset : votersSatisfying (fun voter =>
          StrictlyPrefers (c5SecondProfile voter) first second) ⊆
          ({(2 : Fin 3)} : Finset (Fin 3)) := by
        intro voter hvoter
        fin_cases voter
        · simp
          have hforward : StrictlyPrefers c4Ranking_v1 first second := by
            simpa [votersSatisfying, c5SecondProfile] using hvoter
          exact False.elim ((lt_asymm hreverse) hforward)
        · simp
          have hforward : StrictlyPrefers c4Ranking_v1 first second := by
            simpa [votersSatisfying, c5SecondProfile] using hvoter
          exact False.elim ((lt_asymm hreverse) hforward)
        · simp
      have hcard := Finset.card_le_card hsubset
      norm_num at hcard hmajority
      omega

/-- The first ballot has Kemeny score four in the second profile. -/
theorem c5SecondProfile_v1_kemenyDisagreement :
    kemenyDisagreement c5SecondProfile c4Ranking_v1 = 4 := by
  decide

/-- No ranking has Kemeny disagreement below four in the second profile. -/
theorem c5SecondProfile_kemenyDisagreement_ge_four (output : Ranking 18) :
    4 ≤ kemenyDisagreement c5SecondProfile output := by
  have hminimum := pairwiseMajorityRanking_isKemenyMinimizer (fun _ : Ranking 18 => True)
    c5SecondProfile c4Ranking_v1 trivial c5SecondProfile_v1_isPairwiseMajorityRanking
  calc
    4 = kemenyDisagreement c5SecondProfile c4Ranking_v1 :=
      c5SecondProfile_v1_kemenyDisagreement.symm
    _ ≤ kemenyDisagreement c5SecondProfile output := hminimum.2 output trivial

/-- The combined profile's literal `2 ≻ 1` witness has Kemeny score 32. -/
theorem c5CombinedProfile_twoAboveOne_kemenyDisagreement :
    kemenyDisagreement c5CombinedProfile c4TwoAboveOneRanking = 32 := by
  decide

/--
If a feature-linear ranking retains `1 ≻ 2`, its combined-profile Kemeny
score is at least 34: 30 from C.4 plus the second profile's minimum of four.
-/
theorem c5CombinedProfile_kemenyDisagreement_ge_thirtyFour_of_oneAboveTwo
    (output : Ranking 18) (hfeasible : LinearFeasibleRanking c4Features output)
    (honeAboveTwo : StrictlyPrefers output 0 1) :
    34 ≤ kemenyDisagreement c5CombinedProfile output := by
  rw [c5CombinedProfile, kemenyDisagreement_append]
  have hfirst := c4LinearFeasible_kemenyDisagreement_ge_thirty_of_oneAboveTwo
    output hfeasible honeAboveTwo
  have hsecond := c5SecondProfile_kemenyDisagreement_ge_four output
  omega

/-- A Kemeny minimizer restricted to rankings that also respect this profile's Pareto constraints. -/
def IsParetoKemenyMinimizer {Voter : Type*} [Fintype Voter]
    (profile : RankingProfile Voter 18) (output : Ranking 18) : Prop :=
  ParetoFeasibleRanking (LinearFeasibleRanking c4Features) profile output ∧
    ∀ contender,
      ParetoFeasibleRanking (LinearFeasibleRanking c4Features) profile contender →
        kemenyDisagreement profile output ≤ kemenyDisagreement profile contender

/-- A Kemeny-subject-to-PO selector on every source-feasible profile. -/
def IsParetoKemenySelector
    (rule : ∀ voterCount : ℕ,
      LinearRankAggregationRule (Fin voterCount) 18 (LinearFeasibleRanking c4Features)) : Prop :=
  ∀ voterCount (profile : RankingProfile (Fin voterCount) 18),
      FeasibleProfile (LinearFeasibleRanking c4Features) profile →
        IsParetoKemenyMinimizer profile ((rule voterCount).run profile)

/-- The first C.4 ballot has Kemeny score thirty in the first source profile. -/
theorem c4Ranking_v1_kemenyDisagreement :
    kemenyDisagreement c4Profile c4Ranking_v1 = 30 := by
  decide

/-- The first C.4 ballot is admissible under the first profile's Pareto constraints. -/
theorem c4Ranking_v1_paretoFeasible :
    ParetoFeasibleRanking (LinearFeasibleRanking c4Features) c4Profile c4Ranking_v1 := by
  refine ⟨c4Profile_linearFeasible 0, ?_⟩
  decide

/-- The first C.4 ballot is a Pareto-constrained Kemeny minimizer in the first profile. -/
theorem c4Ranking_v1_isParetoKemenyMinimizer :
    IsParetoKemenyMinimizer c4Profile c4Ranking_v1 := by
  refine ⟨c4Ranking_v1_paretoFeasible, ?_⟩
  intro contender hcontender
  have honeAboveTwo : StrictlyPrefers contender 0 1 :=
    hcontender.2 0 1 c4Profile_universallyPrefersOneTwo
  have hbound := c4LinearFeasible_kemenyDisagreement_ge_thirty_of_oneAboveTwo
    contender hcontender.1 honeAboveTwo
  rw [c4Ranking_v1_kemenyDisagreement]
  exact hbound

/-- The first ballot is admissible under the second profile's Pareto constraints. -/
theorem c5SecondProfile_v1_paretoFeasible :
    ParetoFeasibleRanking (LinearFeasibleRanking c4Features) c5SecondProfile c4Ranking_v1 := by
  refine ⟨c4Profile_linearFeasible 0, ?_⟩
  decide

/-- The first ballot is a Pareto-constrained Kemeny minimizer in the second profile. -/
theorem c5SecondProfile_v1_isParetoKemenyMinimizer :
    IsParetoKemenyMinimizer c5SecondProfile c4Ranking_v1 := by
  refine ⟨c5SecondProfile_v1_paretoFeasible, ?_⟩
  intro contender _
  have hminimum := pairwiseMajorityRanking_isKemenyMinimizer (fun _ : Ranking 18 => True)
    c5SecondProfile c4Ranking_v1 trivial c5SecondProfile_v1_isPairwiseMajorityRanking
  exact hminimum.2 contender trivial

/-- The literal `2 ≻ 1` witness is admissible under the combined Pareto constraints. -/
theorem c5CombinedProfile_twoAboveOne_paretoFeasible :
    ParetoFeasibleRanking (LinearFeasibleRanking c4Features)
      c5CombinedProfile c4TwoAboveOneRanking := by
  refine ⟨c4TwoAboveOneRanking_linearFeasible, ?_⟩
  decide

/-- The second source profile has the first ballot as its unique Pareto-Kemeny output. -/
theorem c5SecondProfile_paretoKemeny_eq_v1
    (rule : ∀ voterCount : ℕ,
      LinearRankAggregationRule (Fin voterCount) 18 (LinearFeasibleRanking c4Features))
    (hselector : IsParetoKemenySelector rule) :
    (rule 3).run c5SecondProfile = c4Ranking_v1 := by
  have hselection := hselector 3 c5SecondProfile c5SecondProfile_linearFeasible
  by_contra hdifferent
  have hstrict := pairwiseMajorityRanking_kemenyDisagreement_lt_of_ne
    c5SecondProfile c4Ranking_v1 ((rule 3).run c5SecondProfile)
    c5SecondProfile_v1_isPairwiseMajorityRanking (Ne.symm hdifferent)
  exact (not_lt_of_ge (hselection.2 c4Ranking_v1 c5SecondProfile_v1_paretoFeasible)) hstrict

/-- Every Pareto-Kemeny output on the combined profile ranks `2` above `1`. -/
theorem c5CombinedProfile_paretoKemeny_ranksTwoAboveOne
    (rule : ∀ voterCount : ℕ,
      LinearRankAggregationRule (Fin voterCount) 18 (LinearFeasibleRanking c4Features))
    (hselector : IsParetoKemenySelector rule) :
    StrictlyPrefers ((rule 9).run c5CombinedProfile) (1 : c4Candidate) 0 := by
  have hselection := hselector 9 c5CombinedProfile c5CombinedProfile_linearFeasible
  have hscore_le : kemenyDisagreement c5CombinedProfile ((rule 9).run c5CombinedProfile) ≤ 32 := by
    calc
      kemenyDisagreement c5CombinedProfile ((rule 9).run c5CombinedProfile) ≤
          kemenyDisagreement c5CombinedProfile c4TwoAboveOneRanking :=
        hselection.2 c4TwoAboveOneRanking c5CombinedProfile_twoAboveOne_paretoFeasible
      _ = 32 := c5CombinedProfile_twoAboveOne_kemenyDisagreement
  rcases strictlyPrefers_or_reverse_of_ne ((rule 9).run c5CombinedProfile)
    (by decide : (1 : c4Candidate) ≠ 0) with h10 | h01
  · exact h10
  · have hscore_ge := c5CombinedProfile_kemenyDisagreement_ge_thirtyFour_of_oneAboveTwo
      ((rule 9).run c5CombinedProfile) hselection.1.1 h01
    omega

/-- Candidate `1` remains the majority top choice in the combined source profile. -/
theorem c5CombinedProfile_majorityTopChoiceOne :
    MajorityTopChoice c5CombinedProfile (0 : c4Candidate) := by
  unfold MajorityTopChoice StrictMajority
  have hleft (voter : Fin 6) :
      c5CombinedProfile (Fin.castAdd 3 voter) = c4Profile voter := by
    simp [c5CombinedProfile, rankingProfileAppend_left]
  change 9 < 2 * (votersSatisfying (fun voter => (c5CombinedProfile voter) 0 = 0)).card
  have hsubset : ({(0 : Fin 9), 1, 2, 3, 4} : Finset (Fin 9)) ⊆
      votersSatisfying (fun voter => (c5CombinedProfile voter) 0 = 0) := by
    intro voter hvoter
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvoter
    rcases hvoter with h0 | h1 | h2 | h3 | h4
    · subst voter
      simp only [votersSatisfying, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [show (0 : Fin 9) = Fin.castAdd 3 (0 : Fin 6) by rfl, hleft]
      simp [c4Profile, c4Ranking_v1, Equiv.swap_apply_def]
    · subst voter
      simp only [votersSatisfying, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [show (1 : Fin 9) = Fin.castAdd 3 (1 : Fin 6) by rfl, hleft]
      simp [c4Profile, c4Ranking_v2, Equiv.swap_apply_def]
    · subst voter
      simp only [votersSatisfying, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [show (2 : Fin 9) = Fin.castAdd 3 (2 : Fin 6) by rfl, hleft]
      simp [c4Profile, c4Ranking_v3, Equiv.swap_apply_def]
    · subst voter
      simp only [votersSatisfying, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [show (3 : Fin 9) = Fin.castAdd 3 (3 : Fin 6) by rfl, hleft]
      simp [c4Profile, c4Ranking_v4, Equiv.swap_apply_def]
    · subst voter
      simp only [votersSatisfying, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [show (4 : Fin 9) = Fin.castAdd 3 (4 : Fin 6) by rfl, hleft]
      simp [c4Profile, c4Ranking_v5, Equiv.swap_apply_def]
  have hcard := Finset.card_le_card hsubset
  have hfive : ({(0 : Fin 9), 1, 2, 3, 4} : Finset (Fin 9)).card = 5 := by
    decide
  rw [hfive] at hcard
  omega

/--
Theorem C.5 on the literal source construction. The source's explicit
without-loss-of-generality selection of `v1` on the first profile is a local
premise; no global tie rule is imposed beyond Pareto-constrained Kemeny
selection.
-/
theorem theoremC_5_paretoKemeny_failsSeparabilityAndMajorityConsistency
    (rule : ∀ voterCount : ℕ,
      LinearRankAggregationRule (Fin voterCount) 18 (LinearFeasibleRanking c4Features))
    (hselector : IsParetoKemenySelector rule)
    (hfirst : (rule 6).run c4Profile = c4Ranking_v1) :
    ¬ RankingSeparability (LinearFeasibleRanking c4Features) rule ∧
      ¬ MajorityConsistent (LinearFeasibleRanking c4Features) (rule 9) := by
  have hsecond := c5SecondProfile_paretoKemeny_eq_v1 rule hselector
  have hcombined := c5CombinedProfile_paretoKemeny_ranksTwoAboveOne rule hselector
  constructor
  · intro hseparable
    have hcomponent : (rule 6).run c4Profile = (rule 3).run c5SecondProfile :=
      hfirst.trans hsecond.symm
    have houtput := hseparable 6 3 c4Profile c5SecondProfile hcomponent
    have houtput' : (rule 9).run c5CombinedProfile = (rule 6).run c4Profile := by
      simpa [c5CombinedProfile] using houtput
    rw [houtput', hfirst] at hcombined
    have hv1 : StrictlyPrefers c4Ranking_v1 (0 : c4Candidate) 1 := by decide
    exact (lt_asymm hv1) hcombined
  · intro hmajority
    have hfirstChoice := hmajority c5CombinedProfile (0 : c4Candidate)
      c5CombinedProfile_linearFeasible c5CombinedProfile_majorityTopChoiceOne
    have honeAboveTwo := strictlyPrefers_firstChoice_of_ne ((rule 9).run c5CombinedProfile)
      (by rw [hfirstChoice]; decide :
        (1 : c4Candidate) ≠ firstChoice ((rule 9).run c5CombinedProfile))
    rw [hfirstChoice] at honeAboveTwo
    exact (lt_asymm honeAboveTwo) hcombined

end GeEtAl2024AlignmentAxioms

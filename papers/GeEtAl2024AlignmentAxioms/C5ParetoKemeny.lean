import GeEtAl2024AlignmentAxioms.C4LinearKemeny
import GeEtAl2024AlignmentAxioms.LCPO

/-!
# Theorem C.5 source instance: Kemeny subject to Pareto optimality

The second profile is the literal three-voter construction in Appendix C.2:
two copies of the first C.4 ballot and the displayed `2 ≻ 1` ballot.  The
source writes “without loss of generality” for the first profile's Kemeny tie.
The finite symmetric appendage family below makes that step precise without
imposing a global, profile-independent ranking key.
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

/--
The source C.5 appendage attached to any one of the six displayed C.4
ballots.  This finite family makes the source's “without loss of generality”
step precise without imposing a global tie key on the rule.
-/
def c5SecondProfileFor (selected : Fin 6) : RankingProfile (Fin 3) 18 :=
  ![c4Profile selected, c4Profile selected, c4TwoAboveOneRanking]

/-- The corresponding nine-voter C.5 profile for a selected source ballot. -/
def c5CombinedProfileFor (selected : Fin 6) : RankingProfile (Fin 9) 18 :=
  rankingProfileAppend c4Profile (c5SecondProfileFor selected)

/-- Every ballot in every symmetric C.5 appendage is feature-linearly feasible. -/
theorem c5SecondProfileFor_linearFeasible (selected : Fin 6) :
    FeasibleProfile (LinearFeasibleRanking c4Features) (c5SecondProfileFor selected) := by
  intro voter
  fin_cases voter
  · exact c4Profile_linearFeasible selected
  · exact c4Profile_linearFeasible selected
  · exact c4TwoAboveOneRanking_linearFeasible

/-- The symmetric combined C.5 profiles remain source-feasible. -/
theorem c5CombinedProfileFor_linearFeasible (selected : Fin 6) :
    FeasibleProfile (LinearFeasibleRanking c4Features) (c5CombinedProfileFor selected) := by
  intro voter
  unfold c5CombinedProfileFor rankingProfileAppend
  refine Fin.addCases
    (motive := fun index =>
      LinearFeasibleRanking c4Features
        (Fin.addCases c4Profile (c5SecondProfileFor selected) index)) ?_ ?_ voter
  · intro leftVoter
    simpa using c4Profile_linearFeasible leftVoter
  · intro rightVoter
    simpa using c5SecondProfileFor_linearFeasible selected rightVoter

/-- Two copies of a ballot make it the strict pairwise-majority ranking. -/
theorem c5SecondProfileFor_selected_isPairwiseMajorityRanking (selected : Fin 6) :
    IsPairwiseMajorityRanking (c5SecondProfileFor selected) (c4Profile selected) := by
  intro first second
  constructor
  · intro hselected
    unfold StrictMajorityPrefers StrictMajority
    have hsubset : ({(0 : Fin 3), 1} : Finset (Fin 3)) ⊆
        votersSatisfying (fun voter =>
          StrictlyPrefers (c5SecondProfileFor selected voter) first second) := by
      intro voter hvoter
      simp only [Finset.mem_insert, Finset.mem_singleton] at hvoter
      rcases hvoter with hzero | hone
      · subst voter
        simp only [votersSatisfying, Finset.mem_filter, Finset.mem_univ, true_and]
        simpa [c5SecondProfileFor] using hselected
      · subst voter
        simp only [votersSatisfying, Finset.mem_filter, Finset.mem_univ, true_and]
        simpa [c5SecondProfileFor] using hselected
    have hcard := Finset.card_le_card hsubset
    norm_num at hcard ⊢
    omega
  · intro hmajority
    have hne : first ≠ second := by
      intro hequal
      subst second
      unfold StrictMajorityPrefers StrictMajority votersSatisfying at hmajority
      simp at hmajority
    rcases strictlyPrefers_or_reverse_of_ne (c4Profile selected) hne with hselected | hreverse
    · exact hselected
    · unfold StrictMajorityPrefers StrictMajority at hmajority
      have hsubset : votersSatisfying (fun voter =>
          StrictlyPrefers (c5SecondProfileFor selected voter) first second) ⊆
          ({(2 : Fin 3)} : Finset (Fin 3)) := by
        intro voter hvoter
        fin_cases voter
        · simp
          have hforward : StrictlyPrefers (c4Profile selected) first second := by
            simpa [votersSatisfying, c5SecondProfileFor] using hvoter
          exact False.elim ((lt_asymm hreverse) hforward)
        · simp
          have hforward : StrictlyPrefers (c4Profile selected) first second := by
            simpa [votersSatisfying, c5SecondProfileFor] using hvoter
          exact False.elim ((lt_asymm hreverse) hforward)
        · simp
      have hcard := Finset.card_le_card hsubset
      norm_num at hcard hmajority
      omega

/-- The selected C.4 ballot has score four in its corresponding C.5 appendage. -/
theorem c5SecondProfileFor_selected_kemenyDisagreement (selected : Fin 6) :
    kemenyDisagreement (c5SecondProfileFor selected) (c4Profile selected) = 4 := by
  fin_cases selected <;> decide

/-- No ranking has C.5 appendage score below the selected ballot's score. -/
theorem c5SecondProfileFor_kemenyDisagreement_ge_four (selected : Fin 6)
    (output : Ranking 18) :
    4 ≤ kemenyDisagreement (c5SecondProfileFor selected) output := by
  have hminimum := pairwiseMajorityRanking_isKemenyMinimizer (fun _ : Ranking 18 => True)
    (c5SecondProfileFor selected) (c4Profile selected) trivial
    (c5SecondProfileFor_selected_isPairwiseMajorityRanking selected)
  calc
    4 = kemenyDisagreement (c5SecondProfileFor selected) (c4Profile selected) :=
      (c5SecondProfileFor_selected_kemenyDisagreement selected).symm
    _ ≤ kemenyDisagreement (c5SecondProfileFor selected) output :=
      hminimum.2 output trivial

/-- The `2 ≻ 1` witness has the same total score in each symmetric C.5 profile. -/
theorem c5CombinedProfileFor_twoAboveOne_kemenyDisagreement (selected : Fin 6) :
    kemenyDisagreement (c5CombinedProfileFor selected) c4TwoAboveOneRanking = 32 := by
  fin_cases selected <;> decide

/-- Every source-ballot appendage forces any `1 ≻ 2` output to score at least 34. -/
theorem c5CombinedProfileFor_kemenyDisagreement_ge_thirtyFour_of_oneAboveTwo
    (selected : Fin 6) (output : Ranking 18)
    (hfeasible : LinearFeasibleRanking c4Features output)
    (honeAboveTwo : StrictlyPrefers output 0 1) :
    34 ≤ kemenyDisagreement (c5CombinedProfileFor selected) output := by
  rw [c5CombinedProfileFor, kemenyDisagreement_append]
  have hfirst := c4LinearFeasible_kemenyDisagreement_ge_thirty_of_oneAboveTwo
    output hfeasible honeAboveTwo
  have hsecond := c5SecondProfileFor_kemenyDisagreement_ge_four selected output
  omega

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

/--
The source proof's displayed first-profile selection fact: the rule chooses
one of the six submitted C.4 ballots. This is weaker than a global tie key
and is exactly what the source's “without loss of generality” sentence needs.
-/
def HasC5SourceBallotOutput
    (rule : ∀ voterCount : ℕ,
      LinearRankAggregationRule (Fin voterCount) 18 (LinearFeasibleRanking c4Features)) : Prop :=
  ∃ selected : Fin 6, (rule 6).run c4Profile = c4Profile selected

/-- The selected ballot is Pareto-feasible for its own two-copy appendage. -/
theorem c5SecondProfileFor_selected_paretoFeasible (selected : Fin 6) :
    ParetoFeasibleRanking (LinearFeasibleRanking c4Features)
      (c5SecondProfileFor selected) (c4Profile selected) := by
  refine ⟨c4Profile_linearFeasible selected, ?_⟩
  simpa [c5SecondProfileFor] using
    submittedRanking_respectsPareto (c5SecondProfileFor selected) (0 : Fin 3)

/-- The `2 ≻ 1` ballot is Pareto-feasible in every symmetric combined profile. -/
theorem c5CombinedProfileFor_twoAboveOne_paretoFeasible (selected : Fin 6) :
    ParetoFeasibleRanking (LinearFeasibleRanking c4Features)
      (c5CombinedProfileFor selected) c4TwoAboveOneRanking := by
  refine ⟨c4TwoAboveOneRanking_linearFeasible, ?_⟩
  simpa [c5CombinedProfileFor, c5SecondProfileFor, rankingProfileAppend] using
    submittedRanking_respectsPareto (c5CombinedProfileFor selected)
      (Fin.natAdd 6 (2 : Fin 3))

/-- The two-copy appendage has the selected source ballot as its unique Pareto-Kemeny output. -/
theorem c5SecondProfileFor_paretoKemeny_eq_selected
    (rule : ∀ voterCount : ℕ,
      LinearRankAggregationRule (Fin voterCount) 18 (LinearFeasibleRanking c4Features))
    (hselector : IsParetoKemenySelector rule) (selected : Fin 6) :
    (rule 3).run (c5SecondProfileFor selected) = c4Profile selected := by
  have hselection := hselector 3 (c5SecondProfileFor selected)
    (c5SecondProfileFor_linearFeasible selected)
  by_contra hdifferent
  have hstrict := pairwiseMajorityRanking_kemenyDisagreement_lt_of_ne
    (c5SecondProfileFor selected) (c4Profile selected)
    ((rule 3).run (c5SecondProfileFor selected))
    (c5SecondProfileFor_selected_isPairwiseMajorityRanking selected) (Ne.symm hdifferent)
  exact (not_lt_of_ge (hselection.2 (c4Profile selected)
    (c5SecondProfileFor_selected_paretoFeasible selected))) hstrict

/-- Every Pareto-Kemeny output on a symmetric combined profile ranks `2` above `1`. -/
theorem c5CombinedProfileFor_paretoKemeny_ranksTwoAboveOne
    (rule : ∀ voterCount : ℕ,
      LinearRankAggregationRule (Fin voterCount) 18 (LinearFeasibleRanking c4Features))
    (hselector : IsParetoKemenySelector rule) (selected : Fin 6) :
    StrictlyPrefers ((rule 9).run (c5CombinedProfileFor selected)) (1 : c4Candidate) 0 := by
  have hselection := hselector 9 (c5CombinedProfileFor selected)
    (c5CombinedProfileFor_linearFeasible selected)
  have hscore_le :
      kemenyDisagreement (c5CombinedProfileFor selected)
        ((rule 9).run (c5CombinedProfileFor selected)) ≤ 32 := by
    calc
      kemenyDisagreement (c5CombinedProfileFor selected)
          ((rule 9).run (c5CombinedProfileFor selected)) ≤
          kemenyDisagreement (c5CombinedProfileFor selected) c4TwoAboveOneRanking :=
        hselection.2 c4TwoAboveOneRanking
          (c5CombinedProfileFor_twoAboveOne_paretoFeasible selected)
      _ = 32 := c5CombinedProfileFor_twoAboveOne_kemenyDisagreement selected
  rcases strictlyPrefers_or_reverse_of_ne ((rule 9).run (c5CombinedProfileFor selected))
    (by decide : (1 : c4Candidate) ≠ 0) with h10 | h01
  · exact h10
  · have hscore_ge := c5CombinedProfileFor_kemenyDisagreement_ge_thirtyFour_of_oneAboveTwo
      selected ((rule 9).run (c5CombinedProfileFor selected)) hselection.1.1 h01
    omega

/-- Every displayed C.4 ballot ranks source candidate `1` above source candidate `2`. -/
theorem c4Profile_selected_prefersOneTwo (selected : Fin 6) :
    StrictlyPrefers (c4Profile selected) (0 : c4Candidate) 1 := by
  fin_cases selected <;> decide

/-- Candidate `1` remains the majority top choice in every symmetric combined profile. -/
theorem c5CombinedProfileFor_majorityTopChoiceOne (selected : Fin 6) :
    MajorityTopChoice (c5CombinedProfileFor selected) (0 : c4Candidate) := by
  unfold MajorityTopChoice StrictMajority
  have hleft (voter : Fin 6) :
      c5CombinedProfileFor selected (Fin.castAdd 3 voter) = c4Profile voter := by
    simp [c5CombinedProfileFor, rankingProfileAppend_left]
  change 9 < 2 * (votersSatisfying (fun voter =>
    (c5CombinedProfileFor selected voter) 0 = 0)).card
  have hsubset : ({(0 : Fin 9), 1, 2, 3, 4} : Finset (Fin 9)) ⊆
      votersSatisfying (fun voter => (c5CombinedProfileFor selected voter) 0 = 0) := by
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

/--
The first C.5 profile has exact objective value thirty under every
Pareto-constrained Kemeny selector. Pareto feasibility supplies `1 ≻ 2`, and
the displayed first ballot supplies the matching upper bound.
-/
theorem c4ParetoKemenySelector_c4Profile_exactObjective
    (rule : ∀ voterCount : ℕ,
      LinearRankAggregationRule (Fin voterCount) 18 (LinearFeasibleRanking c4Features))
    (hselector : IsParetoKemenySelector rule) :
    c4CycleKemenyCost ((rule 6).run c4Profile) = 30 ∧
      kemenyDisagreement c4Profile ((rule 6).run c4Profile) = 30 ∧
        StrictlyPrefers ((rule 6).run c4Profile) (0 : c4Candidate) 1 := by
  have hselection := hselector 6 c4Profile c4Profile_linearFeasible
  have honeAboveTwo : StrictlyPrefers ((rule 6).run c4Profile) (0 : c4Candidate) 1 :=
    hselection.1.2 0 1 c4Profile_universallyPrefersOneTwo
  have hobjective_le :
      kemenyDisagreement c4Profile ((rule 6).run c4Profile) ≤ 30 := by
    calc
      kemenyDisagreement c4Profile ((rule 6).run c4Profile) ≤
          kemenyDisagreement c4Profile c4Ranking_v1 :=
        hselection.2 c4Ranking_v1 c4Ranking_v1_isParetoKemenyMinimizer.1
      _ = 30 := c4Ranking_v1_kemenyDisagreement
  have hcycle_ge := c4CycleKemenyCost_ge_thirty_of_oneAboveTwo
    ((rule 6).run c4Profile) hselection.1.1 honeAboveTwo
  have hcycle_le := c4CycleKemenyCost_le_kemenyDisagreement
    ((rule 6).run c4Profile)
  have hobjective_ge := c4LinearFeasible_kemenyDisagreement_ge_thirty_of_oneAboveTwo
    ((rule 6).run c4Profile) hselection.1.1 honeAboveTwo
  constructor
  · omega
  constructor
  · omega
  · exact honeAboveTwo

/-- The first cycle-break case realizes the first displayed C.4 ballot. -/
theorem c4ParetoKemenySelector_c4Profile_eq_v1_of_break234
    (rule : ∀ voterCount : ℕ,
      LinearRankAggregationRule (Fin voterCount) 18 (LinearFeasibleRanking c4Features))
    (hselector : IsParetoKemenySelector rule)
    (hbreak : StrictlyPrefers ((rule 6).run c4Profile) (4 : c4Candidate) 2) :
    (rule 6).run c4Profile = c4Ranking_v1 := by
  let output := (rule 6).run c4Profile
  have hselection := hselector 6 c4Profile c4Profile_linearFeasible
  have hfeasible : LinearFeasibleRanking c4Features output := by
    simpa [output] using hselection.1.1
  obtain ⟨hcycle, hobjectiveEq, honeAboveTwo⟩ :=
    c4ParetoKemenySelector_c4Profile_exactObjective rule hselector
  have hobjective : kemenyDisagreement c4Profile output ≤ 30 := by
    simpa [output] using hobjectiveEq.le
  have hcycle' : c4CycleKemenyCost output = 30 := by
    simpa [output] using hcycle
  have hbreak' : StrictlyPrefers output (4 : c4Candidate) 2 := by
    simpa [output] using hbreak
  have h01 : StrictlyPrefers output (0 : c4Candidate) 1 := by
    simpa [output] using honeAboveTwo
  rcases c4CycleTripleCosts_ge_three output with
    ⟨h234, h567, h8910, h111213, h141516, h171819⟩
  rcases c4LinearFeasible_fullReverse234 output hfeasible hbreak' with ⟨h32, h43⟩
  have h234eq : c4TripleKemenyCost output 2 3 4 = 15 :=
    c4TripleKemenyCost_eq_fifteen_of_fullReverse output 2 3 4 h32 hbreak' h43
      (by decide) (by decide) (by decide)
  have h567eq : c4TripleKemenyCost output 5 6 7 = 3 := by
    unfold c4CycleKemenyCost at hcycle'
    omega
  have h8910eq : c4TripleKemenyCost output 8 9 10 = 3 := by
    unfold c4CycleKemenyCost at hcycle'
    omega
  have h111213eq : c4TripleKemenyCost output 11 12 13 = 3 := by
    unfold c4CycleKemenyCost at hcycle'
    omega
  have h141516eq : c4TripleKemenyCost output 14 15 16 = 3 := by
    unfold c4CycleKemenyCost at hcycle'
    omega
  have h171819eq : c4TripleKemenyCost output 17 18 19 = 3 := by
    unfold c4CycleKemenyCost at hcycle'
    omega
  rcases c4Triple_forward_of_cost_eq_three output 5 6 7
    (by decide) (by decide) (by decide) h567eq with ⟨h56, h67⟩
  rcases c4Triple_forward_of_cost_eq_three output 8 9 10
    (by decide) (by decide) (by decide) h8910eq with ⟨h89, h910⟩
  rcases c4Triple_forward_of_cost_eq_three output 11 12 13
    (by decide) (by decide) (by decide) h111213eq with ⟨h1112, h1213⟩
  rcases c4Triple_forward_of_cost_eq_three output 14 15 16
    (by decide) (by decide) (by decide) h141516eq with ⟨h1415, h1516⟩
  rcases c4Triple_forward_of_cost_eq_three output 17 18 19
    (by decide) (by decide) (by decide) h171819eq with ⟨h1718, h1819⟩
  have h14 := c4StrictlyPrefers_of_exactCycleAndObjective output 1 4 hcycle' hobjective
    (by decide) (by decide)
  have h25 := c4StrictlyPrefers_of_exactCycleAndObjective output 2 5 hcycle' hobjective
    (by decide) (by decide)
  have h78 := c4StrictlyPrefers_of_exactCycleAndObjective output 7 8 hcycle' hobjective
    (by decide) (by decide)
  have h1011 := c4StrictlyPrefers_of_exactCycleAndObjective output 10 11 hcycle' hobjective
    (by decide) (by decide)
  have h1314 := c4StrictlyPrefers_of_exactCycleAndObjective output 13 14 hcycle' hobjective
    (by decide) (by decide)
  have h1617 := c4StrictlyPrefers_of_exactCycleAndObjective output 16 17 hcycle' hobjective
    (by decide) (by decide)
  apply eq_of_forall_not_adjacent_invertedPair c4Ranking_v1 output
  intro index
  fin_cases index
  · simpa [c4Ranking_v1, Equiv.swap_apply_def] using
      (not_invertedPair_of_strictlyPrefers c4Ranking_v1 output 0 1 h01)
  · simpa [c4Ranking_v1, Equiv.swap_apply_def] using
      (not_invertedPair_of_strictlyPrefers c4Ranking_v1 output 1 4 h14)
  · simpa [c4Ranking_v1, Equiv.swap_apply_def] using
      (not_invertedPair_of_strictlyPrefers c4Ranking_v1 output 4 3 h43)
  · simpa [c4Ranking_v1, Equiv.swap_apply_def] using
      (not_invertedPair_of_strictlyPrefers c4Ranking_v1 output 3 2 h32)
  · simpa [c4Ranking_v1, Equiv.swap_apply_def] using
      (not_invertedPair_of_strictlyPrefers c4Ranking_v1 output 2 5 h25)
  · simpa [c4Ranking_v1, Equiv.swap_apply_def] using
      (not_invertedPair_of_strictlyPrefers c4Ranking_v1 output 5 6 h56)
  · simpa [c4Ranking_v1, Equiv.swap_apply_def] using
      (not_invertedPair_of_strictlyPrefers c4Ranking_v1 output 6 7 h67)
  · simpa [c4Ranking_v1, Equiv.swap_apply_def] using
      (not_invertedPair_of_strictlyPrefers c4Ranking_v1 output 7 8 h78)
  · simpa [c4Ranking_v1, Equiv.swap_apply_def] using
      (not_invertedPair_of_strictlyPrefers c4Ranking_v1 output 8 9 h89)
  · simpa [c4Ranking_v1, Equiv.swap_apply_def] using
      (not_invertedPair_of_strictlyPrefers c4Ranking_v1 output 9 10 h910)
  · simpa [c4Ranking_v1, Equiv.swap_apply_def] using
      (not_invertedPair_of_strictlyPrefers c4Ranking_v1 output 10 11 h1011)
  · simpa [c4Ranking_v1, Equiv.swap_apply_def] using
      (not_invertedPair_of_strictlyPrefers c4Ranking_v1 output 11 12 h1112)
  · simpa [c4Ranking_v1, Equiv.swap_apply_def] using
      (not_invertedPair_of_strictlyPrefers c4Ranking_v1 output 12 13 h1213)
  · simpa [c4Ranking_v1, Equiv.swap_apply_def] using
      (not_invertedPair_of_strictlyPrefers c4Ranking_v1 output 13 14 h1314)
  · simpa [c4Ranking_v1, Equiv.swap_apply_def] using
      (not_invertedPair_of_strictlyPrefers c4Ranking_v1 output 14 15 h1415)
  · simpa [c4Ranking_v1, Equiv.swap_apply_def] using
      (not_invertedPair_of_strictlyPrefers c4Ranking_v1 output 15 16 h1516)
  · simpa [c4Ranking_v1, Equiv.swap_apply_def] using
      (not_invertedPair_of_strictlyPrefers c4Ranking_v1 output 16 17 h1617)
  · simpa [c4Ranking_v1, Equiv.swap_apply_def] using
      (not_invertedPair_of_strictlyPrefers c4Ranking_v1 output 17 18 h1718)
  · simpa [c4Ranking_v1, Equiv.swap_apply_def] using
      (not_invertedPair_of_strictlyPrefers c4Ranking_v1 output 18 19 h1819)

/-- The second cycle-break case realizes the second displayed C.4 ballot. -/
theorem c4ParetoKemenySelector_c4Profile_eq_v2_of_break567
    (rule : ∀ voterCount : ℕ,
      LinearRankAggregationRule (Fin voterCount) 18 (LinearFeasibleRanking c4Features))
    (hselector : IsParetoKemenySelector rule)
    (hbreak : StrictlyPrefers ((rule 6).run c4Profile) (7 : c4Candidate) 5) :
    (rule 6).run c4Profile = c4Ranking_v2 := by
  let output := (rule 6).run c4Profile
  have hselection := hselector 6 c4Profile c4Profile_linearFeasible
  have hfeasible : LinearFeasibleRanking c4Features output := by
    simpa [output] using hselection.1.1
  obtain ⟨hcycle, hobjectiveEq, honeAboveTwo⟩ :=
    c4ParetoKemenySelector_c4Profile_exactObjective rule hselector
  have hobjective : kemenyDisagreement c4Profile output ≤ 30 := by
    simpa [output] using hobjectiveEq.le
  have hcycle' : c4CycleKemenyCost output = 30 := by
    simpa [output] using hcycle
  have hbreak' : StrictlyPrefers output (7 : c4Candidate) 5 := by
    simpa [output] using hbreak
  have h01 : StrictlyPrefers output (0 : c4Candidate) 1 := by
    simpa [output] using honeAboveTwo
  rcases c4CycleTripleCosts_ge_three output with
    ⟨h234, h567, h8910, h111213, h141516, h171819⟩
  rcases c4LinearFeasible_fullReverse567 output hfeasible hbreak' with ⟨h65, h76⟩
  have h567eq : c4TripleKemenyCost output 5 6 7 = 15 :=
    c4TripleKemenyCost_eq_fifteen_of_fullReverse output 5 6 7 h65 hbreak' h76
      (by decide) (by decide) (by decide)
  have h234eq : c4TripleKemenyCost output 2 3 4 = 3 := by
    unfold c4CycleKemenyCost at hcycle'
    omega
  have h8910eq : c4TripleKemenyCost output 8 9 10 = 3 := by
    unfold c4CycleKemenyCost at hcycle'
    omega
  have h111213eq : c4TripleKemenyCost output 11 12 13 = 3 := by
    unfold c4CycleKemenyCost at hcycle'
    omega
  have h141516eq : c4TripleKemenyCost output 14 15 16 = 3 := by
    unfold c4CycleKemenyCost at hcycle'
    omega
  have h171819eq : c4TripleKemenyCost output 17 18 19 = 3 := by
    unfold c4CycleKemenyCost at hcycle'
    omega
  rcases c4Triple_forward_of_cost_eq_three output 2 3 4
    (by decide) (by decide) (by decide) h234eq with ⟨h23, h34⟩
  rcases c4Triple_forward_of_cost_eq_three output 8 9 10
    (by decide) (by decide) (by decide) h8910eq with ⟨h89, h910⟩
  rcases c4Triple_forward_of_cost_eq_three output 11 12 13
    (by decide) (by decide) (by decide) h111213eq with ⟨h1112, h1213⟩
  rcases c4Triple_forward_of_cost_eq_three output 14 15 16
    (by decide) (by decide) (by decide) h141516eq with ⟨h1415, h1516⟩
  rcases c4Triple_forward_of_cost_eq_three output 17 18 19
    (by decide) (by decide) (by decide) h171819eq with ⟨h1718, h1819⟩
  have h12 := c4StrictlyPrefers_of_exactCycleAndObjective output 1 2 hcycle' hobjective
    (by decide) (by decide)
  have h47 := c4StrictlyPrefers_of_exactCycleAndObjective output 4 7 hcycle' hobjective
    (by decide) (by decide)
  have h58 := c4StrictlyPrefers_of_exactCycleAndObjective output 5 8 hcycle' hobjective
    (by decide) (by decide)
  have h1011 := c4StrictlyPrefers_of_exactCycleAndObjective output 10 11 hcycle' hobjective
    (by decide) (by decide)
  have h1314 := c4StrictlyPrefers_of_exactCycleAndObjective output 13 14 hcycle' hobjective
    (by decide) (by decide)
  have h1617 := c4StrictlyPrefers_of_exactCycleAndObjective output 16 17 hcycle' hobjective
    (by decide) (by decide)
  apply ranking_eq_of_forall_adjacentStrictlyPrefers c4Ranking_v2 output
  intro index
  fin_cases index
  · simpa [c4Ranking_v2, Equiv.swap_apply_def] using h01
  · simpa [c4Ranking_v2, Equiv.swap_apply_def] using h12
  · simpa [c4Ranking_v2, Equiv.swap_apply_def] using h23
  · simpa [c4Ranking_v2, Equiv.swap_apply_def] using h34
  · simpa [c4Ranking_v2, Equiv.swap_apply_def] using h47
  · simpa [c4Ranking_v2, Equiv.swap_apply_def] using h76
  · simpa [c4Ranking_v2, Equiv.swap_apply_def] using h65
  · simpa [c4Ranking_v2, Equiv.swap_apply_def] using h58
  · simpa [c4Ranking_v2, Equiv.swap_apply_def] using h89
  · simpa [c4Ranking_v2, Equiv.swap_apply_def] using h910
  · simpa [c4Ranking_v2, Equiv.swap_apply_def] using h1011
  · simpa [c4Ranking_v2, Equiv.swap_apply_def] using h1112
  · simpa [c4Ranking_v2, Equiv.swap_apply_def] using h1213
  · simpa [c4Ranking_v2, Equiv.swap_apply_def] using h1314
  · simpa [c4Ranking_v2, Equiv.swap_apply_def] using h1415
  · simpa [c4Ranking_v2, Equiv.swap_apply_def] using h1516
  · simpa [c4Ranking_v2, Equiv.swap_apply_def] using h1617
  · simpa [c4Ranking_v2, Equiv.swap_apply_def] using h1718
  · simpa [c4Ranking_v2, Equiv.swap_apply_def] using h1819

/-- The third cycle-break case realizes the third displayed C.4 ballot. -/
theorem c4ParetoKemenySelector_c4Profile_eq_v3_of_break8910
    (rule : ∀ voterCount : ℕ,
      LinearRankAggregationRule (Fin voterCount) 18 (LinearFeasibleRanking c4Features))
    (hselector : IsParetoKemenySelector rule)
    (hbreak : StrictlyPrefers ((rule 6).run c4Profile) (10 : c4Candidate) 8) :
    (rule 6).run c4Profile = c4Ranking_v3 := by
  let output := (rule 6).run c4Profile
  have hselection := hselector 6 c4Profile c4Profile_linearFeasible
  have hfeasible : LinearFeasibleRanking c4Features output := by
    simpa [output] using hselection.1.1
  obtain ⟨hcycle, hobjectiveEq, honeAboveTwo⟩ :=
    c4ParetoKemenySelector_c4Profile_exactObjective rule hselector
  have hobjective : kemenyDisagreement c4Profile output ≤ 30 := by
    simpa [output] using hobjectiveEq.le
  have hcycle' : c4CycleKemenyCost output = 30 := by
    simpa [output] using hcycle
  have hbreak' : StrictlyPrefers output (10 : c4Candidate) 8 := by
    simpa [output] using hbreak
  have h01 : StrictlyPrefers output (0 : c4Candidate) 1 := by
    simpa [output] using honeAboveTwo
  rcases c4CycleTripleCosts_ge_three output with
    ⟨h234, h567, h8910, h111213, h141516, h171819⟩
  rcases c4LinearFeasible_fullReverse8910 output hfeasible hbreak' with ⟨h98, h109⟩
  have h8910eq : c4TripleKemenyCost output 8 9 10 = 15 :=
    c4TripleKemenyCost_eq_fifteen_of_fullReverse output 8 9 10 h98 hbreak' h109
      (by decide) (by decide) (by decide)
  have h234eq : c4TripleKemenyCost output 2 3 4 = 3 := by
    unfold c4CycleKemenyCost at hcycle'
    omega
  have h567eq : c4TripleKemenyCost output 5 6 7 = 3 := by
    unfold c4CycleKemenyCost at hcycle'
    omega
  have h111213eq : c4TripleKemenyCost output 11 12 13 = 3 := by
    unfold c4CycleKemenyCost at hcycle'
    omega
  have h141516eq : c4TripleKemenyCost output 14 15 16 = 3 := by
    unfold c4CycleKemenyCost at hcycle'
    omega
  have h171819eq : c4TripleKemenyCost output 17 18 19 = 3 := by
    unfold c4CycleKemenyCost at hcycle'
    omega
  rcases c4Triple_forward_of_cost_eq_three output 2 3 4
    (by decide) (by decide) (by decide) h234eq with ⟨h23, h34⟩
  rcases c4Triple_forward_of_cost_eq_three output 5 6 7
    (by decide) (by decide) (by decide) h567eq with ⟨h56, h67⟩
  rcases c4Triple_forward_of_cost_eq_three output 11 12 13
    (by decide) (by decide) (by decide) h111213eq with ⟨h1112, h1213⟩
  rcases c4Triple_forward_of_cost_eq_three output 14 15 16
    (by decide) (by decide) (by decide) h141516eq with ⟨h1415, h1516⟩
  rcases c4Triple_forward_of_cost_eq_three output 17 18 19
    (by decide) (by decide) (by decide) h171819eq with ⟨h1718, h1819⟩
  have h12 := c4StrictlyPrefers_of_exactCycleAndObjective output 1 2 hcycle' hobjective
    (by decide) (by decide)
  have h45 := c4StrictlyPrefers_of_exactCycleAndObjective output 4 5 hcycle' hobjective
    (by decide) (by decide)
  have h710 := c4StrictlyPrefers_of_exactCycleAndObjective output 7 10 hcycle' hobjective
    (by decide) (by decide)
  have h811 := c4StrictlyPrefers_of_exactCycleAndObjective output 8 11 hcycle' hobjective
    (by decide) (by decide)
  have h1314 := c4StrictlyPrefers_of_exactCycleAndObjective output 13 14 hcycle' hobjective
    (by decide) (by decide)
  have h1617 := c4StrictlyPrefers_of_exactCycleAndObjective output 16 17 hcycle' hobjective
    (by decide) (by decide)
  apply ranking_eq_of_forall_adjacentStrictlyPrefers c4Ranking_v3 output
  intro index
  fin_cases index
  · simpa [c4Ranking_v3, Equiv.swap_apply_def] using h01
  · simpa [c4Ranking_v3, Equiv.swap_apply_def] using h12
  · simpa [c4Ranking_v3, Equiv.swap_apply_def] using h23
  · simpa [c4Ranking_v3, Equiv.swap_apply_def] using h34
  · simpa [c4Ranking_v3, Equiv.swap_apply_def] using h45
  · simpa [c4Ranking_v3, Equiv.swap_apply_def] using h56
  · simpa [c4Ranking_v3, Equiv.swap_apply_def] using h67
  · simpa [c4Ranking_v3, Equiv.swap_apply_def] using h710
  · simpa [c4Ranking_v3, Equiv.swap_apply_def] using h109
  · simpa [c4Ranking_v3, Equiv.swap_apply_def] using h98
  · simpa [c4Ranking_v3, Equiv.swap_apply_def] using h811
  · simpa [c4Ranking_v3, Equiv.swap_apply_def] using h1112
  · simpa [c4Ranking_v3, Equiv.swap_apply_def] using h1213
  · simpa [c4Ranking_v3, Equiv.swap_apply_def] using h1314
  · simpa [c4Ranking_v3, Equiv.swap_apply_def] using h1415
  · simpa [c4Ranking_v3, Equiv.swap_apply_def] using h1516
  · simpa [c4Ranking_v3, Equiv.swap_apply_def] using h1617
  · simpa [c4Ranking_v3, Equiv.swap_apply_def] using h1718
  · simpa [c4Ranking_v3, Equiv.swap_apply_def] using h1819

/-- The fourth cycle-break case realizes the fourth displayed C.4 ballot. -/
theorem c4ParetoKemenySelector_c4Profile_eq_v4_of_break111213
    (rule : ∀ voterCount : ℕ,
      LinearRankAggregationRule (Fin voterCount) 18 (LinearFeasibleRanking c4Features))
    (hselector : IsParetoKemenySelector rule)
    (hbreak : StrictlyPrefers ((rule 6).run c4Profile) (13 : c4Candidate) 11) :
    (rule 6).run c4Profile = c4Ranking_v4 := by
  let output := (rule 6).run c4Profile
  have hselection := hselector 6 c4Profile c4Profile_linearFeasible
  have hfeasible : LinearFeasibleRanking c4Features output := by
    simpa [output] using hselection.1.1
  obtain ⟨hcycle, hobjectiveEq, honeAboveTwo⟩ :=
    c4ParetoKemenySelector_c4Profile_exactObjective rule hselector
  have hobjective : kemenyDisagreement c4Profile output ≤ 30 := by
    simpa [output] using hobjectiveEq.le
  have hcycle' : c4CycleKemenyCost output = 30 := by
    simpa [output] using hcycle
  have hbreak' : StrictlyPrefers output (13 : c4Candidate) 11 := by
    simpa [output] using hbreak
  have h01 : StrictlyPrefers output (0 : c4Candidate) 1 := by
    simpa [output] using honeAboveTwo
  rcases c4CycleTripleCosts_ge_three output with
    ⟨h234, h567, h8910, h111213, h141516, h171819⟩
  rcases c4LinearFeasible_fullReverse111213 output hfeasible hbreak' with ⟨h1211, h1312⟩
  have h111213eq : c4TripleKemenyCost output 11 12 13 = 15 :=
    c4TripleKemenyCost_eq_fifteen_of_fullReverse output 11 12 13 h1211 hbreak' h1312
      (by decide) (by decide) (by decide)
  have h234eq : c4TripleKemenyCost output 2 3 4 = 3 := by
    unfold c4CycleKemenyCost at hcycle'
    omega
  have h567eq : c4TripleKemenyCost output 5 6 7 = 3 := by
    unfold c4CycleKemenyCost at hcycle'
    omega
  have h8910eq : c4TripleKemenyCost output 8 9 10 = 3 := by
    unfold c4CycleKemenyCost at hcycle'
    omega
  have h141516eq : c4TripleKemenyCost output 14 15 16 = 3 := by
    unfold c4CycleKemenyCost at hcycle'
    omega
  have h171819eq : c4TripleKemenyCost output 17 18 19 = 3 := by
    unfold c4CycleKemenyCost at hcycle'
    omega
  rcases c4Triple_forward_of_cost_eq_three output 2 3 4
    (by decide) (by decide) (by decide) h234eq with ⟨h23, h34⟩
  rcases c4Triple_forward_of_cost_eq_three output 5 6 7
    (by decide) (by decide) (by decide) h567eq with ⟨h56, h67⟩
  rcases c4Triple_forward_of_cost_eq_three output 8 9 10
    (by decide) (by decide) (by decide) h8910eq with ⟨h89, h910⟩
  rcases c4Triple_forward_of_cost_eq_three output 14 15 16
    (by decide) (by decide) (by decide) h141516eq with ⟨h1415, h1516⟩
  rcases c4Triple_forward_of_cost_eq_three output 17 18 19
    (by decide) (by decide) (by decide) h171819eq with ⟨h1718, h1819⟩
  have h12 := c4StrictlyPrefers_of_exactCycleAndObjective output 1 2 hcycle' hobjective
    (by decide) (by decide)
  have h45 := c4StrictlyPrefers_of_exactCycleAndObjective output 4 5 hcycle' hobjective
    (by decide) (by decide)
  have h78 := c4StrictlyPrefers_of_exactCycleAndObjective output 7 8 hcycle' hobjective
    (by decide) (by decide)
  have h1013 := c4StrictlyPrefers_of_exactCycleAndObjective output 10 13 hcycle' hobjective
    (by decide) (by decide)
  have h1114 := c4StrictlyPrefers_of_exactCycleAndObjective output 11 14 hcycle' hobjective
    (by decide) (by decide)
  have h1617 := c4StrictlyPrefers_of_exactCycleAndObjective output 16 17 hcycle' hobjective
    (by decide) (by decide)
  apply ranking_eq_of_forall_adjacentStrictlyPrefers c4Ranking_v4 output
  intro index
  fin_cases index
  · simpa [c4Ranking_v4, Equiv.swap_apply_def] using h01
  · simpa [c4Ranking_v4, Equiv.swap_apply_def] using h12
  · simpa [c4Ranking_v4, Equiv.swap_apply_def] using h23
  · simpa [c4Ranking_v4, Equiv.swap_apply_def] using h34
  · simpa [c4Ranking_v4, Equiv.swap_apply_def] using h45
  · simpa [c4Ranking_v4, Equiv.swap_apply_def] using h56
  · simpa [c4Ranking_v4, Equiv.swap_apply_def] using h67
  · simpa [c4Ranking_v4, Equiv.swap_apply_def] using h78
  · simpa [c4Ranking_v4, Equiv.swap_apply_def] using h89
  · simpa [c4Ranking_v4, Equiv.swap_apply_def] using h910
  · simpa [c4Ranking_v4, Equiv.swap_apply_def] using h1013
  · simpa [c4Ranking_v4, Equiv.swap_apply_def] using h1312
  · simpa [c4Ranking_v4, Equiv.swap_apply_def] using h1211
  · simpa [c4Ranking_v4, Equiv.swap_apply_def] using h1114
  · simpa [c4Ranking_v4, Equiv.swap_apply_def] using h1415
  · simpa [c4Ranking_v4, Equiv.swap_apply_def] using h1516
  · simpa [c4Ranking_v4, Equiv.swap_apply_def] using h1617
  · simpa [c4Ranking_v4, Equiv.swap_apply_def] using h1718
  · simpa [c4Ranking_v4, Equiv.swap_apply_def] using h1819

/-- The fifth cycle-break case realizes the fifth displayed C.4 ballot. -/
theorem c4ParetoKemenySelector_c4Profile_eq_v5_of_break141516
    (rule : ∀ voterCount : ℕ,
      LinearRankAggregationRule (Fin voterCount) 18 (LinearFeasibleRanking c4Features))
    (hselector : IsParetoKemenySelector rule)
    (hbreak : StrictlyPrefers ((rule 6).run c4Profile) (16 : c4Candidate) 14) :
    (rule 6).run c4Profile = c4Ranking_v5 := by
  let output := (rule 6).run c4Profile
  have hselection := hselector 6 c4Profile c4Profile_linearFeasible
  have hfeasible : LinearFeasibleRanking c4Features output := by
    simpa [output] using hselection.1.1
  obtain ⟨hcycle, hobjectiveEq, honeAboveTwo⟩ :=
    c4ParetoKemenySelector_c4Profile_exactObjective rule hselector
  have hobjective : kemenyDisagreement c4Profile output ≤ 30 := by
    simpa [output] using hobjectiveEq.le
  have hcycle' : c4CycleKemenyCost output = 30 := by
    simpa [output] using hcycle
  have hbreak' : StrictlyPrefers output (16 : c4Candidate) 14 := by
    simpa [output] using hbreak
  have h01 : StrictlyPrefers output (0 : c4Candidate) 1 := by
    simpa [output] using honeAboveTwo
  rcases c4CycleTripleCosts_ge_three output with
    ⟨h234, h567, h8910, h111213, h141516, h171819⟩
  rcases c4LinearFeasible_fullReverse141516 output hfeasible hbreak' with ⟨h1514, h1615⟩
  have h141516eq : c4TripleKemenyCost output 14 15 16 = 15 :=
    c4TripleKemenyCost_eq_fifteen_of_fullReverse output 14 15 16 h1514 hbreak' h1615
      (by decide) (by decide) (by decide)
  have h234eq : c4TripleKemenyCost output 2 3 4 = 3 := by
    unfold c4CycleKemenyCost at hcycle'
    omega
  have h567eq : c4TripleKemenyCost output 5 6 7 = 3 := by
    unfold c4CycleKemenyCost at hcycle'
    omega
  have h8910eq : c4TripleKemenyCost output 8 9 10 = 3 := by
    unfold c4CycleKemenyCost at hcycle'
    omega
  have h111213eq : c4TripleKemenyCost output 11 12 13 = 3 := by
    unfold c4CycleKemenyCost at hcycle'
    omega
  have h171819eq : c4TripleKemenyCost output 17 18 19 = 3 := by
    unfold c4CycleKemenyCost at hcycle'
    omega
  rcases c4Triple_forward_of_cost_eq_three output 2 3 4
    (by decide) (by decide) (by decide) h234eq with ⟨h23, h34⟩
  rcases c4Triple_forward_of_cost_eq_three output 5 6 7
    (by decide) (by decide) (by decide) h567eq with ⟨h56, h67⟩
  rcases c4Triple_forward_of_cost_eq_three output 8 9 10
    (by decide) (by decide) (by decide) h8910eq with ⟨h89, h910⟩
  rcases c4Triple_forward_of_cost_eq_three output 11 12 13
    (by decide) (by decide) (by decide) h111213eq with ⟨h1112, h1213⟩
  rcases c4Triple_forward_of_cost_eq_three output 17 18 19
    (by decide) (by decide) (by decide) h171819eq with ⟨h1718, h1819⟩
  have h12 := c4StrictlyPrefers_of_exactCycleAndObjective output 1 2 hcycle' hobjective
    (by decide) (by decide)
  have h45 := c4StrictlyPrefers_of_exactCycleAndObjective output 4 5 hcycle' hobjective
    (by decide) (by decide)
  have h78 := c4StrictlyPrefers_of_exactCycleAndObjective output 7 8 hcycle' hobjective
    (by decide) (by decide)
  have h1011 := c4StrictlyPrefers_of_exactCycleAndObjective output 10 11 hcycle' hobjective
    (by decide) (by decide)
  have h1316 := c4StrictlyPrefers_of_exactCycleAndObjective output 13 16 hcycle' hobjective
    (by decide) (by decide)
  have h1417 := c4StrictlyPrefers_of_exactCycleAndObjective output 14 17 hcycle' hobjective
    (by decide) (by decide)
  apply ranking_eq_of_forall_adjacentStrictlyPrefers c4Ranking_v5 output
  intro index
  fin_cases index
  · simpa [c4Ranking_v5, Equiv.swap_apply_def] using h01
  · simpa [c4Ranking_v5, Equiv.swap_apply_def] using h12
  · simpa [c4Ranking_v5, Equiv.swap_apply_def] using h23
  · simpa [c4Ranking_v5, Equiv.swap_apply_def] using h34
  · simpa [c4Ranking_v5, Equiv.swap_apply_def] using h45
  · simpa [c4Ranking_v5, Equiv.swap_apply_def] using h56
  · simpa [c4Ranking_v5, Equiv.swap_apply_def] using h67
  · simpa [c4Ranking_v5, Equiv.swap_apply_def] using h78
  · simpa [c4Ranking_v5, Equiv.swap_apply_def] using h89
  · simpa [c4Ranking_v5, Equiv.swap_apply_def] using h910
  · simpa [c4Ranking_v5, Equiv.swap_apply_def] using h1011
  · simpa [c4Ranking_v5, Equiv.swap_apply_def] using h1112
  · simpa [c4Ranking_v5, Equiv.swap_apply_def] using h1213
  · simpa [c4Ranking_v5, Equiv.swap_apply_def] using h1316
  · simpa [c4Ranking_v5, Equiv.swap_apply_def] using h1615
  · simpa [c4Ranking_v5, Equiv.swap_apply_def] using h1514
  · simpa [c4Ranking_v5, Equiv.swap_apply_def] using h1417
  · simpa [c4Ranking_v5, Equiv.swap_apply_def] using h1718
  · simpa [c4Ranking_v5, Equiv.swap_apply_def] using h1819

/-- The sixth cycle-break case realizes the sixth displayed C.4 ballot. -/
theorem c4ParetoKemenySelector_c4Profile_eq_v6_of_break171819
    (rule : ∀ voterCount : ℕ,
      LinearRankAggregationRule (Fin voterCount) 18 (LinearFeasibleRanking c4Features))
    (hselector : IsParetoKemenySelector rule)
    (hbreak : StrictlyPrefers ((rule 6).run c4Profile) (19 : c4Candidate) 17) :
    (rule 6).run c4Profile = c4Ranking_v6 := by
  let output := (rule 6).run c4Profile
  have hselection := hselector 6 c4Profile c4Profile_linearFeasible
  have hfeasible : LinearFeasibleRanking c4Features output := by
    simpa [output] using hselection.1.1
  obtain ⟨hcycle, hobjectiveEq, honeAboveTwo⟩ :=
    c4ParetoKemenySelector_c4Profile_exactObjective rule hselector
  have hobjective : kemenyDisagreement c4Profile output ≤ 30 := by
    simpa [output] using hobjectiveEq.le
  have hcycle' : c4CycleKemenyCost output = 30 := by
    simpa [output] using hcycle
  have hbreak' : StrictlyPrefers output (19 : c4Candidate) 17 := by
    simpa [output] using hbreak
  have h01 : StrictlyPrefers output (0 : c4Candidate) 1 := by
    simpa [output] using honeAboveTwo
  rcases c4CycleTripleCosts_ge_three output with
    ⟨h234, h567, h8910, h111213, h141516, h171819⟩
  rcases c4LinearFeasible_fullReverse171819 output hfeasible hbreak' with ⟨h1817, h1918⟩
  have h171819eq : c4TripleKemenyCost output 17 18 19 = 15 :=
    c4TripleKemenyCost_eq_fifteen_of_fullReverse output 17 18 19 h1817 hbreak' h1918
      (by decide) (by decide) (by decide)
  have h234eq : c4TripleKemenyCost output 2 3 4 = 3 := by
    unfold c4CycleKemenyCost at hcycle'
    omega
  have h567eq : c4TripleKemenyCost output 5 6 7 = 3 := by
    unfold c4CycleKemenyCost at hcycle'
    omega
  have h8910eq : c4TripleKemenyCost output 8 9 10 = 3 := by
    unfold c4CycleKemenyCost at hcycle'
    omega
  have h111213eq : c4TripleKemenyCost output 11 12 13 = 3 := by
    unfold c4CycleKemenyCost at hcycle'
    omega
  have h141516eq : c4TripleKemenyCost output 14 15 16 = 3 := by
    unfold c4CycleKemenyCost at hcycle'
    omega
  rcases c4Triple_forward_of_cost_eq_three output 2 3 4
    (by decide) (by decide) (by decide) h234eq with ⟨h23, h34⟩
  rcases c4Triple_forward_of_cost_eq_three output 5 6 7
    (by decide) (by decide) (by decide) h567eq with ⟨h56, h67⟩
  rcases c4Triple_forward_of_cost_eq_three output 8 9 10
    (by decide) (by decide) (by decide) h8910eq with ⟨h89, h910⟩
  rcases c4Triple_forward_of_cost_eq_three output 11 12 13
    (by decide) (by decide) (by decide) h111213eq with ⟨h1112, h1213⟩
  rcases c4Triple_forward_of_cost_eq_three output 14 15 16
    (by decide) (by decide) (by decide) h141516eq with ⟨h1415, h1516⟩
  have h12 := c4StrictlyPrefers_of_exactCycleAndObjective output 1 2 hcycle' hobjective
    (by decide) (by decide)
  have h45 := c4StrictlyPrefers_of_exactCycleAndObjective output 4 5 hcycle' hobjective
    (by decide) (by decide)
  have h78 := c4StrictlyPrefers_of_exactCycleAndObjective output 7 8 hcycle' hobjective
    (by decide) (by decide)
  have h1011 := c4StrictlyPrefers_of_exactCycleAndObjective output 10 11 hcycle' hobjective
    (by decide) (by decide)
  have h1314 := c4StrictlyPrefers_of_exactCycleAndObjective output 13 14 hcycle' hobjective
    (by decide) (by decide)
  have h1619 := c4StrictlyPrefers_of_exactCycleAndObjective output 16 19 hcycle' hobjective
    (by decide) (by decide)
  apply ranking_eq_of_forall_adjacentStrictlyPrefers c4Ranking_v6 output
  intro index
  fin_cases index
  · simpa [c4Ranking_v6, Equiv.swap_apply_def] using h01
  · simpa [c4Ranking_v6, Equiv.swap_apply_def] using h12
  · simpa [c4Ranking_v6, Equiv.swap_apply_def] using h23
  · simpa [c4Ranking_v6, Equiv.swap_apply_def] using h34
  · simpa [c4Ranking_v6, Equiv.swap_apply_def] using h45
  · simpa [c4Ranking_v6, Equiv.swap_apply_def] using h56
  · simpa [c4Ranking_v6, Equiv.swap_apply_def] using h67
  · simpa [c4Ranking_v6, Equiv.swap_apply_def] using h78
  · simpa [c4Ranking_v6, Equiv.swap_apply_def] using h89
  · simpa [c4Ranking_v6, Equiv.swap_apply_def] using h910
  · simpa [c4Ranking_v6, Equiv.swap_apply_def] using h1011
  · simpa [c4Ranking_v6, Equiv.swap_apply_def] using h1112
  · simpa [c4Ranking_v6, Equiv.swap_apply_def] using h1213
  · simpa [c4Ranking_v6, Equiv.swap_apply_def] using h1314
  · simpa [c4Ranking_v6, Equiv.swap_apply_def] using h1415
  · simpa [c4Ranking_v6, Equiv.swap_apply_def] using h1516
  · simpa [c4Ranking_v6, Equiv.swap_apply_def] using h1619
  · simpa [c4Ranking_v6, Equiv.swap_apply_def] using h1918
  · simpa [c4Ranking_v6, Equiv.swap_apply_def] using h1817

/--
The finite first-profile classification asserted in the source C.5 proof is a
consequence of Pareto-constrained Kemeny minimality on the displayed C.4
instance: exactly one of the six submitted ballots is selected.
-/
theorem c4ParetoKemenySelector_hasC5SourceBallotOutput
    (rule : ∀ voterCount : ℕ,
      LinearRankAggregationRule (Fin voterCount) 18 (LinearFeasibleRanking c4Features))
    (hselector : IsParetoKemenySelector rule) :
    HasC5SourceBallotOutput rule := by
  have hselection := hselector 6 c4Profile c4Profile_linearFeasible
  have honeAboveTwo := (c4ParetoKemenySelector_c4Profile_exactObjective rule hselector).2.2
  rcases c4LinearFeasible_hasCycleBreak ((rule 6).run c4Profile) hselection.1.1 with
    h10 | h42 | h75 | h108 | h1311 | h1614 | h1917
  · exact (lt_asymm honeAboveTwo h10).elim
  · refine ⟨0, ?_⟩
    simpa [c4Profile] using
      c4ParetoKemenySelector_c4Profile_eq_v1_of_break234 rule hselector h42
  · refine ⟨1, ?_⟩
    simpa [c4Profile] using
      c4ParetoKemenySelector_c4Profile_eq_v2_of_break567 rule hselector h75
  · refine ⟨2, ?_⟩
    simpa [c4Profile] using
      c4ParetoKemenySelector_c4Profile_eq_v3_of_break8910 rule hselector h108
  · refine ⟨3, ?_⟩
    simpa [c4Profile] using
      c4ParetoKemenySelector_c4Profile_eq_v4_of_break111213 rule hselector h1311
  · refine ⟨4, ?_⟩
    simpa [c4Profile] using
      c4ParetoKemenySelector_c4Profile_eq_v5_of_break141516 rule hselector h1614
  · refine ⟨5, ?_⟩
    simpa [c4Profile] using
      c4ParetoKemenySelector_c4Profile_eq_v6_of_break171819 rule hselector h1917

/-!
The source's “without loss of generality” choice of `v1` on the first C.4
profile is not forced by Pareto-constrained Kemeny minimization.  The second
source ballot is a distinct feasible minimizer as well.  This witness records
the minimal tie-selection boundary needed by the C.5 separability argument.
-/
theorem c4Ranking_v2_isParetoKemenyMinimizer :
    IsParetoKemenyMinimizer c4Profile c4Ranking_v2 := by
  refine ⟨?_, ?_⟩
  · refine ⟨c4Profile_linearFeasible 1, ?_⟩
    decide
  · intro contender hcontender
    have honeAboveTwo : StrictlyPrefers contender 0 1 :=
      hcontender.2 0 1 c4Profile_universallyPrefersOneTwo
    have hbound := c4LinearFeasible_kemenyDisagreement_ge_thirty_of_oneAboveTwo
      contender hcontender.1 honeAboveTwo
    rw [show kemenyDisagreement c4Profile c4Ranking_v2 = 30 by decide]
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
theorem theoremC_5_paretoKemeny_failsSeparabilityAndMajorityConsistency_of_v1
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

/--
The C.5 conclusion for every rule whose first C.4 output satisfies the
source's asserted input-ballot selection fact. The selected ballot indexes
the corresponding symmetric appendage, so no particular tie choice or global
tie convention is imposed.
-/
theorem theoremC_5_paretoKemeny_failsSeparabilityAndMajorityConsistency_of_sourceBallot
    (rule : ∀ voterCount : ℕ,
      LinearRankAggregationRule (Fin voterCount) 18 (LinearFeasibleRanking c4Features))
    (hselector : IsParetoKemenySelector rule)
    (hsourceBallot : HasC5SourceBallotOutput rule) :
    ¬ RankingSeparability (LinearFeasibleRanking c4Features) rule ∧
      ¬ MajorityConsistent (LinearFeasibleRanking c4Features) (rule 9) := by
  obtain ⟨selected, hfirst⟩ := hsourceBallot
  have hsecond := c5SecondProfileFor_paretoKemeny_eq_selected rule hselector selected
  have hcombined := c5CombinedProfileFor_paretoKemeny_ranksTwoAboveOne rule hselector selected
  constructor
  · intro hseparable
    have hcomponent : (rule 6).run c4Profile =
        (rule 3).run (c5SecondProfileFor selected) :=
      hfirst.trans hsecond.symm
    have houtput := hseparable 6 3 c4Profile (c5SecondProfileFor selected) hcomponent
    have houtput' : (rule 9).run (c5CombinedProfileFor selected) =
        (rule 6).run c4Profile := by
      simpa [c5CombinedProfileFor] using houtput
    rw [houtput', hfirst] at hcombined
    exact (lt_asymm (c4Profile_selected_prefersOneTwo selected)) hcombined
  · intro hmajority
    have hfirstChoice := hmajority (c5CombinedProfileFor selected) (0 : c4Candidate)
      (c5CombinedProfileFor_linearFeasible selected)
      (c5CombinedProfileFor_majorityTopChoiceOne selected)
    have honeAboveTwo := strictlyPrefers_firstChoice_of_ne
      ((rule 9).run (c5CombinedProfileFor selected))
      (by rw [hfirstChoice]; decide :
        (1 : c4Candidate) ≠ firstChoice ((rule 9).run (c5CombinedProfileFor selected)))
    rw [hfirstChoice] at honeAboveTwo
    exact (lt_asymm honeAboveTwo) hcombined

/--
Theorem C.5 without an extra selector premise: the finite first-profile
classification follows from Pareto-constrained Kemeny minimality.
-/
theorem theoremC_5_paretoKemeny_failsSeparabilityAndMajorityConsistency
    (rule : ∀ voterCount : ℕ,
      LinearRankAggregationRule (Fin voterCount) 18 (LinearFeasibleRanking c4Features))
    (hselector : IsParetoKemenySelector rule) :
    ¬ RankingSeparability (LinearFeasibleRanking c4Features) rule ∧
      ¬ MajorityConsistent (LinearFeasibleRanking c4Features) (rule 9) :=
  theoremC_5_paretoKemeny_failsSeparabilityAndMajorityConsistency_of_sourceBallot
    rule hselector (c4ParetoKemenySelector_hasC5SourceBallotOutput rule hselector)

end GeEtAl2024AlignmentAxioms

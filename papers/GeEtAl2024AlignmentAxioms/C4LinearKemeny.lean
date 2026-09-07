import AppliedModelingLib.Alignment.Axioms.Kemeny
import AppliedModelingLib.Alignment.Axioms.LinearModel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Theorem C.4 source instance: linear Kemeny

This file records the literal twenty-candidate, seven-feature construction in
Appendix C.2 of Ge et al. (2024). Candidates `0` through `19` correspond to
the source labels `1` through `20`. The source proof says only that the
linear-Kemeny output “can be checked”; the executable profile and the claimed
`2 ≻ 1` witness are separated here from the remaining global feasible-region
minimality proof.
-/

namespace GeEtAl2024AlignmentAxioms

noncomputable section

open AppliedModelingLib.Alignment.Axioms
open AppliedModelingLib.SocialChoice.Ranking

abbrev c4Candidate := Candidate 18

/-- The seven-dimensional feature table printed in the proof of Theorem C.4. -/
def c4Features : c4Candidate → FeatureVector 7 :=
  ![![2000000, 0, 0, 0, 0, 0, 0],
    ![0, 2000000, 0, 0, 0, 0, 0],
    ![0, 200000, 0, 0, 0, 0, 0],
    ![0, 100000, 100000, 0, 0, 0, 0],
    ![0, 0, 200000, 0, 0, 0, 0],
    ![0, 0, 20000, 0, 0, 0, 0],
    ![0, 0, 10000, 10000, 0, 0, 0],
    ![0, 0, 0, 20000, 0, 0, 0],
    ![0, 0, 0, 2000, 0, 0, 0],
    ![0, 0, 0, 1000, 1000, 0, 0],
    ![0, 0, 0, 0, 2000, 0, 0],
    ![0, 0, 0, 0, 200, 0, 0],
    ![0, 0, 0, 0, 100, 100, 0],
    ![0, 0, 0, 0, 0, 200, 0],
    ![0, 0, 0, 0, 0, 20, 0],
    ![0, 0, 0, 0, 0, 10, 10],
    ![0, 0, 0, 0, 0, 0, 20],
    ![0, 0, 0, 0, 0, 0, 2],
    ![1, 0, 0, 0, 0, 0, 1],
    ![2, 0, 0, 0, 0, 0, 0]]

/-- The C.4 dot products as symbolic coordinate expressions. -/
def c4SymbolicRewards (parameter : LinearRewardParameter 7) : c4Candidate → ℝ :=
  ![2000000 * parameter 0,
    2000000 * parameter 1,
    200000 * parameter 1,
    100000 * parameter 1 + 100000 * parameter 2,
    200000 * parameter 2,
    20000 * parameter 2,
    10000 * parameter 2 + 10000 * parameter 3,
    20000 * parameter 3,
    2000 * parameter 3,
    1000 * parameter 3 + 1000 * parameter 4,
    2000 * parameter 4,
    200 * parameter 4,
    100 * parameter 4 + 100 * parameter 5,
    200 * parameter 5,
    20 * parameter 5,
    10 * parameter 5 + 10 * parameter 6,
    20 * parameter 6,
    2 * parameter 6,
    parameter 0 + parameter 6,
    2 * parameter 0]

/-- The source feature table has exactly the displayed symbolic dot products. -/
theorem linearReward_c4Features (parameter : LinearRewardParameter 7)
    (candidate : c4Candidate) :
    linearReward parameter c4Features candidate = c4SymbolicRewards parameter candidate := by
  have h3 : Fin.succ (2 : Fin 6) = (3 : Fin 7) := by decide
  have h4 : Fin.succ (Fin.succ (2 : Fin 5)) = (4 : Fin 7) := by decide
  have h5 : Fin.succ (Fin.succ (Fin.succ (2 : Fin 4))) = (5 : Fin 7) := by decide
  have h6 : Fin.succ (Fin.succ (Fin.succ (Fin.succ (2 : Fin 3)))) = (6 : Fin 7) := by decide
  fin_cases candidate <;>
    norm_num [Fin.sum_univ_succ, c4Features, c4SymbolicRewards, linearReward]
  all_goals (try simp only [h3, h4, h5, h6]) <;> ring

/-- The six parameter vectors printed in the proof of Theorem C.4. -/
def c4Parameters : Fin 6 → LinearRewardParameter 7 :=
  ![![2, 1, 7, 6, 5, 4, 3],
    ![3, 2, 1, 7, 6, 5, 4],
    ![4, 3, 2, 1, 7, 6, 5],
    ![5, 4, 3, 2, 1, 7, 6],
    ![6, 5, 4, 3, 2, 1, 7],
    ![7, 6, 5, 4, 3, 2, 1]]

/-- Exact natural-number rewards for the six printed C.4 parameter vectors. -/
def c4ParameterScoresNat : Fin 6 → c4Candidate → ℕ :=
  ![![4000000, 2000000, 200000, 800000, 1400000, 140000, 130000, 120000,
      12000, 11000, 10000, 1000, 900, 800, 80, 70, 60, 6, 5, 4],
    ![6000000, 4000000, 400000, 300000, 200000, 20000, 80000, 140000,
      14000, 13000, 12000, 1200, 1100, 1000, 100, 90, 80, 8, 7, 6],
    ![8000000, 6000000, 600000, 500000, 400000, 40000, 30000, 20000,
      2000, 8000, 14000, 1400, 1300, 1200, 120, 110, 100, 10, 9, 8],
    ![10000000, 8000000, 800000, 700000, 600000, 60000, 50000, 40000,
      4000, 3000, 2000, 200, 800, 1400, 140, 130, 120, 12, 11, 10],
    ![12000000, 10000000, 1000000, 900000, 800000, 80000, 70000, 60000,
      6000, 5000, 4000, 400, 300, 200, 20, 80, 140, 14, 13, 12],
    ![14000000, 12000000, 1200000, 1100000, 1000000, 100000, 90000, 80000,
      8000, 7000, 6000, 600, 500, 400, 40, 30, 20, 2, 8, 14]]

/-- The same exact rewards, viewed in the real scalar field of the linear model. -/
def c4ParameterScores : Fin 6 → c4Candidate → ℝ := fun voter candidate =>
  c4ParameterScoresNat voter candidate

/-- Each displayed score table separates its twenty source candidates. -/
theorem c4ParameterScoresNat_injective (voter : Fin 6) :
    Function.Injective (c4ParameterScoresNat voter) := by
  fin_cases voter <;> decide

/-- The table above is the literal dot product on each source candidate. -/
theorem c4ParameterScores_correct (voter : Fin 6) (candidate : c4Candidate) :
    linearReward (c4Parameters voter) c4Features candidate = c4ParameterScores voter candidate := by
  fin_cases voter <;> fin_cases candidate <;>
    norm_num [Fin.sum_univ_succ, c4Parameters, c4Features, c4ParameterScores,
      c4ParameterScoresNat, linearReward]

/-- The first source ballot. -/
def c4Ranking_v1 : Ranking 18 :=
  Equiv.swap 2 4

/-- The second source ballot. -/
def c4Ranking_v2 : Ranking 18 :=
  Equiv.swap 5 7

/-- The third source ballot. -/
def c4Ranking_v3 : Ranking 18 :=
  Equiv.swap 8 10

/-- The fourth source ballot. -/
def c4Ranking_v4 : Ranking 18 :=
  Equiv.swap 11 13

/-- The fifth source ballot. -/
def c4Ranking_v5 : Ranking 18 :=
  Equiv.swap 14 16

/-- The sixth source ballot. -/
def c4Ranking_v6 : Ranking 18 :=
  Equiv.swap 17 19

/-- The literal six-voter source profile. -/
def c4Profile : RankingProfile (Fin 6) 18 :=
  ![c4Ranking_v1, c4Ranking_v2, c4Ranking_v3,
    c4Ranking_v4, c4Ranking_v5, c4Ranking_v6]

/-- Each printed C.4 score table decreases strictly along its corresponding ballot. -/
theorem c4ParameterScoresNat_inducesProfile (voter : Fin 6) :
    ∀ first second, StrictlyPrefers (c4Profile voter) first second →
      c4ParameterScoresNat voter second < c4ParameterScoresNat voter first := by
  fin_cases voter <;> decide

/--
The displayed feasible ranking with source candidate `2` above `1`.  It is
induced by the positive parameter `(1,7,6,5,4,3,2)`.
-/
def c4TwoAboveOneRanking : Ranking 18 :=
  Equiv.swap 0 1

/-- A positive source-compatible parameter inducing `c4TwoAboveOneRanking`. -/
def c4TwoAboveOneParameter : LinearRewardParameter 7 := ![1, 7, 6, 5, 4, 3, 2]

/-- Exact natural-number rewards for the displayed `2 ≻ 1` witness parameter. -/
def c4TwoAboveOneScoresNat : c4Candidate → ℕ :=
  ![2000000, 14000000, 1400000, 1300000, 1200000, 120000, 110000, 100000,
    10000, 9000, 8000, 800, 700, 600, 60, 50, 40, 4, 3, 2]

/-- The displayed witness scores viewed in the real scalar field. -/
def c4TwoAboveOneScores : c4Candidate → ℝ := fun candidate =>
  c4TwoAboveOneScoresNat candidate

/-- The witness score table separates its twenty source candidates. -/
theorem c4TwoAboveOneScoresNat_injective : Function.Injective c4TwoAboveOneScoresNat := by
  decide

/-- The displayed witness score table is its literal dot product. -/
theorem c4TwoAboveOneScores_correct (candidate : c4Candidate) :
    linearReward c4TwoAboveOneParameter c4Features candidate = c4TwoAboveOneScores candidate := by
  fin_cases candidate <;>
    norm_num [Fin.sum_univ_succ, c4Features, c4TwoAboveOneParameter, c4TwoAboveOneScores,
      c4TwoAboveOneScoresNat, linearReward]

/-- The exact Kemeny disagreement score of the displayed `2 ≻ 1` ranking. -/
theorem c4TwoAboveOneRanking_kemenyDisagreement :
    kemenyDisagreement c4Profile c4TwoAboveOneRanking = 24 := by
  decide

/-- The displayed parameter gives pairwise-distinct rewards on the source table. -/
theorem c4TwoAboveOneParameter_nondegenerate :
    NondegenerateParameter c4Features c4TwoAboveOneParameter := by
  intro first second hdifferent hequal
  rw [c4TwoAboveOneScores_correct first, c4TwoAboveOneScores_correct second] at hequal
  change (c4TwoAboveOneScoresNat first : ℝ) = c4TwoAboveOneScoresNat second at hequal
  have hnat : c4TwoAboveOneScoresNat first = c4TwoAboveOneScoresNat second := by
    exact_mod_cast hequal
  exact hdifferent (c4TwoAboveOneScoresNat_injective hnat)

/-- The displayed parameter induces the literal source `2 ≻ 1` ranking. -/
theorem c4TwoAboveOneParameter_induces :
    InducesRanking c4Features c4TwoAboveOneParameter c4TwoAboveOneRanking := by
  have hscoreOrder : ∀ first second,
      StrictlyPrefers c4TwoAboveOneRanking first second →
        c4TwoAboveOneScoresNat second < c4TwoAboveOneScoresNat first := by
    decide
  intro first second hpreference
  rw [c4TwoAboveOneScores_correct first, c4TwoAboveOneScores_correct second]
  change (c4TwoAboveOneScoresNat second : ℝ) ≤ c4TwoAboveOneScoresNat first
  exact_mod_cast (Nat.le_of_lt (hscoreOrder first second hpreference))

/-- The source's displayed `2 ≻ 1` ranking is feature-linearly feasible. -/
theorem c4TwoAboveOneRanking_linearFeasible :
    LinearFeasibleRanking c4Features c4TwoAboveOneRanking :=
  ⟨c4TwoAboveOneParameter, c4TwoAboveOneParameter_nondegenerate,
    c4TwoAboveOneParameter_induces⟩

/-- Every literal C.4 ballot is induced by its corresponding printed parameter. -/
theorem c4Profile_linearFeasible :
    FeasibleProfile (LinearFeasibleRanking c4Features) c4Profile := by
  have hnondegenerate (voter : Fin 6) : NondegenerateParameter c4Features (c4Parameters voter) := by
    intro first second hdifferent hequal
    rw [c4ParameterScores_correct voter first, c4ParameterScores_correct voter second] at hequal
    change (c4ParameterScoresNat voter first : ℝ) = c4ParameterScoresNat voter second at hequal
    have hnat : c4ParameterScoresNat voter first = c4ParameterScoresNat voter second := by
      exact_mod_cast hequal
    exact hdifferent (c4ParameterScoresNat_injective voter hnat)
  have hinduced (voter : Fin 6) : InducesRanking c4Features (c4Parameters voter) (c4Profile voter) := by
    intro first second hpreference
    rw [c4ParameterScores_correct voter first, c4ParameterScores_correct voter second]
    change (c4ParameterScoresNat voter second : ℝ) ≤ c4ParameterScoresNat voter first
    exact_mod_cast (Nat.le_of_lt
      (c4ParameterScoresNat_inducesProfile voter first second hpreference))
  intro voter
  exact ⟨c4Parameters voter, hnondegenerate voter, hinduced voter⟩

/-- The two ordered source terms belonging to one unordered candidate pair. -/
def c4PairOrderedPairs (first second : c4Candidate) : Finset (c4Candidate × c4Candidate) :=
  {(first, second), (second, first)}

/-- The Kemeny disagreement contributed by one unordered candidate pair. -/
def c4PairKemenyCost (output : Ranking 18)
    (first second : c4Candidate) : ℕ :=
  kemenyDisagreementOnPairs c4Profile output (c4PairOrderedPairs first second)

/-- If the output puts `first` above `second`, this pair costs its reverse support. -/
theorem c4PairKemenyCost_eq_reverseSupport_of_prefers
    (output : Ranking 18) (first second : c4Candidate)
    (hdistinct : first ≠ second)
    (hpreference : StrictlyPrefers output first second) :
    c4PairKemenyCost output first second = pairwiseSupport c4Profile second first := by
  have hreverse : ¬ StrictlyPrefers output second first :=
    fun h => (lt_asymm hpreference) h
  rw [c4PairKemenyCost, kemenyDisagreementOnPairs_eq_pairwiseSupport_sum]
  simp [c4PairOrderedPairs, hdistinct, hpreference, hreverse]

/-- If the output puts `second` above `first`, this pair costs its forward support. -/
theorem c4PairKemenyCost_eq_forwardSupport_of_reversePrefers
    (output : Ranking 18) (first second : c4Candidate)
    (hdistinct : first ≠ second)
    (hpreference : StrictlyPrefers output second first) :
    c4PairKemenyCost output first second = pairwiseSupport c4Profile first second := by
  have hforward : ¬ StrictlyPrefers output first second :=
    fun h => (lt_asymm hpreference) h
  rw [c4PairKemenyCost, kemenyDisagreementOnPairs_eq_pairwiseSupport_sum]
  simp [c4PairOrderedPairs, hdistinct, hforward, hpreference]

/-- Every unordered pair costs at least the smaller of its two voter supports. -/
theorem c4PairKemenyCost_ge_minSupport
    (output : Ranking 18) (first second : c4Candidate)
    (hdistinct : first ≠ second) :
    min (pairwiseSupport c4Profile first second) (pairwiseSupport c4Profile second first) ≤
      c4PairKemenyCost output first second := by
  rcases strictlyPrefers_or_reverse_of_ne output hdistinct with hforward | hreverse
  · rw [c4PairKemenyCost_eq_reverseSupport_of_prefers output first second hdistinct hforward]
    exact min_le_right _ _
  · rw [c4PairKemenyCost_eq_forwardSupport_of_reversePrefers output first second hdistinct hreverse]
    exact min_le_left _ _

/-- The three unordered pairs belonging to one cyclic three-candidate block. -/
def c4TripleKemenyCost (output : Ranking 18)
    (first second third : c4Candidate) : ℕ :=
  c4PairKemenyCost output first second + c4PairKemenyCost output first third +
    c4PairKemenyCost output second third

/-- The six ordered source terms in a three-candidate Kemeny block. -/
def c4TripleOrderedPairs (first second third : c4Candidate) : Finset (c4Candidate × c4Candidate) :=
  c4PairOrderedPairs first second ∪ c4PairOrderedPairs first third ∪
    c4PairOrderedPairs second third

/-- A triple cost is the restricted disagreement on its three disjoint pair blocks. -/
theorem c4TripleKemenyCost_eq_onPairs (output : Ranking 18)
    (first second third : c4Candidate)
    (hfirst : Disjoint (c4PairOrderedPairs first second) (c4PairOrderedPairs first third))
    (hsecond : Disjoint (c4PairOrderedPairs first second ∪ c4PairOrderedPairs first third)
      (c4PairOrderedPairs second third)) :
    c4TripleKemenyCost output first second third =
      kemenyDisagreementOnPairs c4Profile output (c4TripleOrderedPairs first second third) := by
  unfold c4TripleKemenyCost c4TripleOrderedPairs c4PairKemenyCost
  rw [← kemenyDisagreementOnPairs_union c4Profile output
      (c4PairOrderedPairs first second) (c4PairOrderedPairs first third) hfirst]
  rw [← kemenyDisagreementOnPairs_union c4Profile output
      (c4PairOrderedPairs first second ∪ c4PairOrderedPairs first third)
      (c4PairOrderedPairs second third) hsecond]

/-- A cyclic triple has baseline Kemeny cost at least three when each base pair has support 5--1. -/
theorem c4TripleKemenyCost_ge_three_of_minSupport
    (output : Ranking 18) (first second third : c4Candidate)
    (hfirst_second : min (pairwiseSupport c4Profile first second)
      (pairwiseSupport c4Profile second first) = 1)
    (hfirst_third : min (pairwiseSupport c4Profile first third)
      (pairwiseSupport c4Profile third first) = 1)
    (hsecond_third : min (pairwiseSupport c4Profile second third)
      (pairwiseSupport c4Profile third second) = 1) :
    3 ≤ c4TripleKemenyCost output first second third := by
  rw [c4TripleKemenyCost]
  have h12 := c4PairKemenyCost_ge_minSupport output first second (by
    intro heq
    subst second
    simp at hfirst_second)
  have h13 := c4PairKemenyCost_ge_minSupport output first third (by
    intro heq
    subst third
    simp at hfirst_third)
  have h23 := c4PairKemenyCost_ge_minSupport output second third (by
    intro heq
    subst third
    simp at hsecond_third)
  omega

/-- Each of the six cyclic three-candidate blocks has baseline cost at least three. -/
theorem c4CycleTripleCosts_ge_three (output : Ranking 18) :
    3 ≤ c4TripleKemenyCost output 2 3 4 ∧
      3 ≤ c4TripleKemenyCost output 5 6 7 ∧
      3 ≤ c4TripleKemenyCost output 8 9 10 ∧
      3 ≤ c4TripleKemenyCost output 11 12 13 ∧
      3 ≤ c4TripleKemenyCost output 14 15 16 ∧
      3 ≤ c4TripleKemenyCost output 17 18 19 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    apply c4TripleKemenyCost_ge_three_of_minSupport <;> decide

/-- A fully reversed 5--1 cyclic triple costs fifteen. -/
theorem c4TripleKemenyCost_eq_fifteen_of_fullReverse
    (output : Ranking 18) (first second third : c4Candidate)
    (hsecond_first : StrictlyPrefers output second first)
    (hthird_first : StrictlyPrefers output third first)
    (hthird_second : StrictlyPrefers output third second)
    (h12 : pairwiseSupport c4Profile first second = 5)
    (h13 : pairwiseSupport c4Profile first third = 5)
    (h23 : pairwiseSupport c4Profile second third = 5) :
    c4TripleKemenyCost output first second third = 15 := by
  rw [c4TripleKemenyCost,
    c4PairKemenyCost_eq_forwardSupport_of_reversePrefers output first second (by
      intro heq
      subst second
      simp at h12)
      hsecond_first,
    c4PairKemenyCost_eq_forwardSupport_of_reversePrefers output first third (by
      intro heq
      subst third
      simp at h13)
      hthird_first,
    c4PairKemenyCost_eq_forwardSupport_of_reversePrefers output second third (by
      intro heq
      subst third
      simp at h23)
      hthird_second,
    h12, h13, h23]

/--
Every feature-linearly feasible output breaks the source's seven-coordinate
cycle: either it puts candidate `2` above `1`, or it fully reverses the
endpoint direction of one three-candidate block.
-/
theorem c4LinearFeasible_hasCycleBreak (output : Ranking 18)
    (hfeasible : LinearFeasibleRanking c4Features output) :
    StrictlyPrefers output 1 0 ∨ StrictlyPrefers output 4 2 ∨
      StrictlyPrefers output 7 5 ∨ StrictlyPrefers output 10 8 ∨
      StrictlyPrefers output 13 11 ∨ StrictlyPrefers output 16 14 ∨
      StrictlyPrefers output 19 17 := by
  obtain ⟨parameter, hnondegenerate, hinduced⟩ := hfeasible
  by_contra hnoBreak
  have h01 : StrictlyPrefers output 0 1 := by
    rcases strictlyPrefers_or_reverse_of_ne output (by decide : (0 : c4Candidate) ≠ 1) with h | h
    · exact h
    · exact (hnoBreak (Or.inl h)).elim
  have h24 : StrictlyPrefers output 2 4 := by
    rcases strictlyPrefers_or_reverse_of_ne output (by decide : (2 : c4Candidate) ≠ 4) with h | h
    · exact h
    · exact (hnoBreak (Or.inr (Or.inl h))).elim
  have h57 : StrictlyPrefers output 5 7 := by
    rcases strictlyPrefers_or_reverse_of_ne output (by decide : (5 : c4Candidate) ≠ 7) with h | h
    · exact h
    · exact (hnoBreak (Or.inr (Or.inr (Or.inl h)))).elim
  have h810 : StrictlyPrefers output 8 10 := by
    rcases strictlyPrefers_or_reverse_of_ne output (by decide : (8 : c4Candidate) ≠ 10) with h | h
    · exact h
    · exact (hnoBreak (Or.inr (Or.inr (Or.inr (Or.inl h))))).elim
  have h1113 : StrictlyPrefers output 11 13 := by
    rcases strictlyPrefers_or_reverse_of_ne output (by decide : (11 : c4Candidate) ≠ 13) with h | h
    · exact h
    · exact (hnoBreak (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))).elim
  have h1416 : StrictlyPrefers output 14 16 := by
    rcases strictlyPrefers_or_reverse_of_ne output (by decide : (14 : c4Candidate) ≠ 16) with h | h
    · exact h
    · exact (hnoBreak (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))).elim
  have h1719 : StrictlyPrefers output 17 19 := by
    rcases strictlyPrefers_or_reverse_of_ne output (by decide : (17 : c4Candidate) ≠ 19) with h | h
    · exact h
    · exact (hnoBreak (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))).elim
  have hreward01 := inducesRanking_strictReward_of_nondegenerate c4Features parameter output
    hinduced hnondegenerate h01
  have hreward24 := inducesRanking_strictReward_of_nondegenerate c4Features parameter output
    hinduced hnondegenerate h24
  have hreward57 := inducesRanking_strictReward_of_nondegenerate c4Features parameter output
    hinduced hnondegenerate h57
  have hreward810 := inducesRanking_strictReward_of_nondegenerate c4Features parameter output
    hinduced hnondegenerate h810
  have hreward1113 := inducesRanking_strictReward_of_nondegenerate c4Features parameter output
    hinduced hnondegenerate h1113
  have hreward1416 := inducesRanking_strictReward_of_nondegenerate c4Features parameter output
    hinduced hnondegenerate h1416
  have hreward1719 := inducesRanking_strictReward_of_nondegenerate c4Features parameter output
    hinduced hnondegenerate h1719
  rw [linearReward_c4Features, linearReward_c4Features] at hreward01 hreward24 hreward57 hreward810 hreward1113 hreward1416 hreward1719
  change 2000000 * parameter 1 < 2000000 * parameter 0 at hreward01
  change 200000 * parameter 2 < 200000 * parameter 1 at hreward24
  change 20000 * parameter 3 < 20000 * parameter 2 at hreward57
  change 2000 * parameter 4 < 2000 * parameter 3 at hreward810
  change 200 * parameter 5 < 200 * parameter 4 at hreward1113
  change 20 * parameter 6 < 20 * parameter 5 at hreward1416
  change 2 * parameter 0 < 2 * parameter 6 at hreward1719
  linarith

/-- Reversing the endpoints of the first cyclic triple reverses its full order. -/
theorem c4LinearFeasible_fullReverse234 (output : Ranking 18)
    (hfeasible : LinearFeasibleRanking c4Features output)
    (hendpoint : StrictlyPrefers output 4 2) :
    StrictlyPrefers output 3 2 ∧ StrictlyPrefers output 4 3 := by
  obtain ⟨parameter, hnondegenerate, hinduced⟩ := hfeasible
  have hendpointReward := inducesRanking_strictReward_of_nondegenerate c4Features parameter output
    hinduced hnondegenerate hendpoint
  have htheta : parameter 1 < parameter 2 := by
    rw [linearReward_c4Features, linearReward_c4Features] at hendpointReward
    change 200000 * parameter 1 < 200000 * parameter 2 at hendpointReward
    linarith
  have h43 : StrictlyPrefers output 4 3 := by
    rcases strictlyPrefers_or_reverse_of_ne output (by decide : (4 : c4Candidate) ≠ 3) with h | h
    · exact h
    · have hreward := inducesRanking_strictReward_of_nondegenerate c4Features parameter output
        hinduced hnondegenerate h
      rw [linearReward_c4Features, linearReward_c4Features] at hreward
      change 200000 * parameter 2 < 100000 * parameter 1 + 100000 * parameter 2 at hreward
      linarith
  have h32 : StrictlyPrefers output 3 2 := by
    rcases strictlyPrefers_or_reverse_of_ne output (by decide : (3 : c4Candidate) ≠ 2) with h | h
    · exact h
    · have hreward := inducesRanking_strictReward_of_nondegenerate c4Features parameter output
        hinduced hnondegenerate h
      rw [linearReward_c4Features, linearReward_c4Features] at hreward
      change 100000 * parameter 1 + 100000 * parameter 2 < 200000 * parameter 1 at hreward
      linarith
  exact ⟨h32, h43⟩

/-- Reversing the endpoints of the second cyclic triple reverses its full order. -/
theorem c4LinearFeasible_fullReverse567 (output : Ranking 18)
    (hfeasible : LinearFeasibleRanking c4Features output)
    (hendpoint : StrictlyPrefers output 7 5) :
    StrictlyPrefers output 6 5 ∧ StrictlyPrefers output 7 6 := by
  obtain ⟨parameter, hnondegenerate, hinduced⟩ := hfeasible
  have hendpointReward := inducesRanking_strictReward_of_nondegenerate c4Features parameter output
    hinduced hnondegenerate hendpoint
  have htheta : parameter 2 < parameter 3 := by
    rw [linearReward_c4Features, linearReward_c4Features] at hendpointReward
    change 20000 * parameter 2 < 20000 * parameter 3 at hendpointReward
    linarith
  have h76 : StrictlyPrefers output 7 6 := by
    rcases strictlyPrefers_or_reverse_of_ne output (by decide : (7 : c4Candidate) ≠ 6) with h | h
    · exact h
    · have hreward := inducesRanking_strictReward_of_nondegenerate c4Features parameter output
        hinduced hnondegenerate h
      rw [linearReward_c4Features, linearReward_c4Features] at hreward
      change 20000 * parameter 3 < 10000 * parameter 2 + 10000 * parameter 3 at hreward
      linarith
  have h65 : StrictlyPrefers output 6 5 := by
    rcases strictlyPrefers_or_reverse_of_ne output (by decide : (6 : c4Candidate) ≠ 5) with h | h
    · exact h
    · have hreward := inducesRanking_strictReward_of_nondegenerate c4Features parameter output
        hinduced hnondegenerate h
      rw [linearReward_c4Features, linearReward_c4Features] at hreward
      change 10000 * parameter 2 + 10000 * parameter 3 < 20000 * parameter 2 at hreward
      linarith
  exact ⟨h65, h76⟩

/-- Reversing the endpoints of the third cyclic triple reverses its full order. -/
theorem c4LinearFeasible_fullReverse8910 (output : Ranking 18)
    (hfeasible : LinearFeasibleRanking c4Features output)
    (hendpoint : StrictlyPrefers output 10 8) :
    StrictlyPrefers output 9 8 ∧ StrictlyPrefers output 10 9 := by
  obtain ⟨parameter, hnondegenerate, hinduced⟩ := hfeasible
  have hendpointReward := inducesRanking_strictReward_of_nondegenerate c4Features parameter output
    hinduced hnondegenerate hendpoint
  have htheta : parameter 3 < parameter 4 := by
    rw [linearReward_c4Features, linearReward_c4Features] at hendpointReward
    change 2000 * parameter 3 < 2000 * parameter 4 at hendpointReward
    linarith
  have h109 : StrictlyPrefers output 10 9 := by
    rcases strictlyPrefers_or_reverse_of_ne output (by decide : (10 : c4Candidate) ≠ 9) with h | h
    · exact h
    · have hreward := inducesRanking_strictReward_of_nondegenerate c4Features parameter output
        hinduced hnondegenerate h
      rw [linearReward_c4Features, linearReward_c4Features] at hreward
      change 2000 * parameter 4 < 1000 * parameter 3 + 1000 * parameter 4 at hreward
      linarith
  have h98 : StrictlyPrefers output 9 8 := by
    rcases strictlyPrefers_or_reverse_of_ne output (by decide : (9 : c4Candidate) ≠ 8) with h | h
    · exact h
    · have hreward := inducesRanking_strictReward_of_nondegenerate c4Features parameter output
        hinduced hnondegenerate h
      rw [linearReward_c4Features, linearReward_c4Features] at hreward
      change 1000 * parameter 3 + 1000 * parameter 4 < 2000 * parameter 3 at hreward
      linarith
  exact ⟨h98, h109⟩

/-- Reversing the endpoints of the fourth cyclic triple reverses its full order. -/
theorem c4LinearFeasible_fullReverse111213 (output : Ranking 18)
    (hfeasible : LinearFeasibleRanking c4Features output)
    (hendpoint : StrictlyPrefers output 13 11) :
    StrictlyPrefers output 12 11 ∧ StrictlyPrefers output 13 12 := by
  obtain ⟨parameter, hnondegenerate, hinduced⟩ := hfeasible
  have hendpointReward := inducesRanking_strictReward_of_nondegenerate c4Features parameter output
    hinduced hnondegenerate hendpoint
  have htheta : parameter 4 < parameter 5 := by
    rw [linearReward_c4Features, linearReward_c4Features] at hendpointReward
    change 200 * parameter 4 < 200 * parameter 5 at hendpointReward
    linarith
  have h1312 : StrictlyPrefers output 13 12 := by
    rcases strictlyPrefers_or_reverse_of_ne output (by decide : (13 : c4Candidate) ≠ 12) with h | h
    · exact h
    · have hreward := inducesRanking_strictReward_of_nondegenerate c4Features parameter output
        hinduced hnondegenerate h
      rw [linearReward_c4Features, linearReward_c4Features] at hreward
      change 200 * parameter 5 < 100 * parameter 4 + 100 * parameter 5 at hreward
      linarith
  have h1211 : StrictlyPrefers output 12 11 := by
    rcases strictlyPrefers_or_reverse_of_ne output (by decide : (12 : c4Candidate) ≠ 11) with h | h
    · exact h
    · have hreward := inducesRanking_strictReward_of_nondegenerate c4Features parameter output
        hinduced hnondegenerate h
      rw [linearReward_c4Features, linearReward_c4Features] at hreward
      change 100 * parameter 4 + 100 * parameter 5 < 200 * parameter 4 at hreward
      linarith
  exact ⟨h1211, h1312⟩

/-- Reversing the endpoints of the fifth cyclic triple reverses its full order. -/
theorem c4LinearFeasible_fullReverse141516 (output : Ranking 18)
    (hfeasible : LinearFeasibleRanking c4Features output)
    (hendpoint : StrictlyPrefers output 16 14) :
    StrictlyPrefers output 15 14 ∧ StrictlyPrefers output 16 15 := by
  obtain ⟨parameter, hnondegenerate, hinduced⟩ := hfeasible
  have hendpointReward := inducesRanking_strictReward_of_nondegenerate c4Features parameter output
    hinduced hnondegenerate hendpoint
  have htheta : parameter 5 < parameter 6 := by
    rw [linearReward_c4Features, linearReward_c4Features] at hendpointReward
    change 20 * parameter 5 < 20 * parameter 6 at hendpointReward
    linarith
  have h1615 : StrictlyPrefers output 16 15 := by
    rcases strictlyPrefers_or_reverse_of_ne output (by decide : (16 : c4Candidate) ≠ 15) with h | h
    · exact h
    · have hreward := inducesRanking_strictReward_of_nondegenerate c4Features parameter output
        hinduced hnondegenerate h
      rw [linearReward_c4Features, linearReward_c4Features] at hreward
      change 20 * parameter 6 < 10 * parameter 5 + 10 * parameter 6 at hreward
      linarith
  have h1514 : StrictlyPrefers output 15 14 := by
    rcases strictlyPrefers_or_reverse_of_ne output (by decide : (15 : c4Candidate) ≠ 14) with h | h
    · exact h
    · have hreward := inducesRanking_strictReward_of_nondegenerate c4Features parameter output
        hinduced hnondegenerate h
      rw [linearReward_c4Features, linearReward_c4Features] at hreward
      change 10 * parameter 5 + 10 * parameter 6 < 20 * parameter 5 at hreward
      linarith
  exact ⟨h1514, h1615⟩

/-- Reversing the endpoints of the sixth cyclic triple reverses its full order. -/
theorem c4LinearFeasible_fullReverse171819 (output : Ranking 18)
    (hfeasible : LinearFeasibleRanking c4Features output)
    (hendpoint : StrictlyPrefers output 19 17) :
    StrictlyPrefers output 18 17 ∧ StrictlyPrefers output 19 18 := by
  obtain ⟨parameter, hnondegenerate, hinduced⟩ := hfeasible
  have hendpointReward := inducesRanking_strictReward_of_nondegenerate c4Features parameter output
    hinduced hnondegenerate hendpoint
  have htheta : parameter 6 < parameter 0 := by
    rw [linearReward_c4Features, linearReward_c4Features] at hendpointReward
    change 2 * parameter 6 < 2 * parameter 0 at hendpointReward
    linarith
  have h1918 : StrictlyPrefers output 19 18 := by
    rcases strictlyPrefers_or_reverse_of_ne output (by decide : (19 : c4Candidate) ≠ 18) with h | h
    · exact h
    · have hreward := inducesRanking_strictReward_of_nondegenerate c4Features parameter output
        hinduced hnondegenerate h
      rw [linearReward_c4Features, linearReward_c4Features] at hreward
      change 2 * parameter 0 < parameter 0 + parameter 6 at hreward
      linarith
  have h1817 : StrictlyPrefers output 18 17 := by
    rcases strictlyPrefers_or_reverse_of_ne output (by decide : (18 : c4Candidate) ≠ 17) with h | h
    · exact h
    · have hreward := inducesRanking_strictReward_of_nondegenerate c4Features parameter output
        hinduced hnondegenerate h
      rw [linearReward_c4Features, linearReward_c4Features] at hreward
      change parameter 0 + parameter 6 < 2 * parameter 6 at hreward
      linarith
  exact ⟨h1817, h1918⟩

/-- The seven cyclic coordinate-comparison blocks used in the C.4 lower bound. -/
def c4CycleKemenyCost (output : Ranking 18) : ℕ :=
  c4PairKemenyCost output 0 1 +
    c4TripleKemenyCost output 2 3 4 +
    c4TripleKemenyCost output 5 6 7 +
    c4TripleKemenyCost output 8 9 10 +
    c4TripleKemenyCost output 11 12 13 +
    c4TripleKemenyCost output 14 15 16 +
    c4TripleKemenyCost output 17 18 19

/-- Both directions of every pair in the seven cyclic coordinate blocks. -/
def c4CycleOrderedPairs : Finset (c4Candidate × c4Candidate) :=
  c4PairOrderedPairs 0 1 ∪
    c4TripleOrderedPairs 2 3 4 ∪ c4TripleOrderedPairs 5 6 7 ∪
    c4TripleOrderedPairs 8 9 10 ∪ c4TripleOrderedPairs 11 12 13 ∪
    c4TripleOrderedPairs 14 15 16 ∪ c4TripleOrderedPairs 17 18 19

/-- The explicit cyclic-block cost is exactly its restricted ordered-pair sum. -/
theorem c4CycleKemenyCost_eq_onPairs (output : Ranking 18) :
    c4CycleKemenyCost output =
      kemenyDisagreementOnPairs c4Profile output c4CycleOrderedPairs := by
  unfold c4CycleKemenyCost c4PairKemenyCost
  rw [c4TripleKemenyCost_eq_onPairs output 2 3 4 (by decide) (by decide),
    c4TripleKemenyCost_eq_onPairs output 5 6 7 (by decide) (by decide),
    c4TripleKemenyCost_eq_onPairs output 8 9 10 (by decide) (by decide),
    c4TripleKemenyCost_eq_onPairs output 11 12 13 (by decide) (by decide),
    c4TripleKemenyCost_eq_onPairs output 14 15 16 (by decide) (by decide),
    c4TripleKemenyCost_eq_onPairs output 17 18 19 (by decide) (by decide)]
  rw [← kemenyDisagreementOnPairs_union c4Profile output
      (c4PairOrderedPairs 0 1) (c4TripleOrderedPairs 2 3 4) (by decide)]
  rw [← kemenyDisagreementOnPairs_union c4Profile output
      (c4PairOrderedPairs 0 1 ∪ c4TripleOrderedPairs 2 3 4)
      (c4TripleOrderedPairs 5 6 7) (by decide)]
  rw [← kemenyDisagreementOnPairs_union c4Profile output
      (c4PairOrderedPairs 0 1 ∪ c4TripleOrderedPairs 2 3 4 ∪
        c4TripleOrderedPairs 5 6 7)
      (c4TripleOrderedPairs 8 9 10) (by decide)]
  rw [← kemenyDisagreementOnPairs_union c4Profile output
      (c4PairOrderedPairs 0 1 ∪ c4TripleOrderedPairs 2 3 4 ∪
        c4TripleOrderedPairs 5 6 7 ∪ c4TripleOrderedPairs 8 9 10)
      (c4TripleOrderedPairs 11 12 13) (by decide)]
  rw [← kemenyDisagreementOnPairs_union c4Profile output
      (c4PairOrderedPairs 0 1 ∪ c4TripleOrderedPairs 2 3 4 ∪
        c4TripleOrderedPairs 5 6 7 ∪ c4TripleOrderedPairs 8 9 10 ∪
        c4TripleOrderedPairs 11 12 13)
      (c4TripleOrderedPairs 14 15 16) (by decide)]
  rw [← kemenyDisagreementOnPairs_union c4Profile output
      (c4PairOrderedPairs 0 1 ∪ c4TripleOrderedPairs 2 3 4 ∪
        c4TripleOrderedPairs 5 6 7 ∪ c4TripleOrderedPairs 8 9 10 ∪
        c4TripleOrderedPairs 11 12 13 ∪ c4TripleOrderedPairs 14 15 16)
      (c4TripleOrderedPairs 17 18 19) (by decide)]
  rfl

/-- The cyclic-block objective is a transparent lower bound on full Kemeny disagreement. -/
theorem c4CycleKemenyCost_le_kemenyDisagreement (output : Ranking 18) :
    c4CycleKemenyCost output ≤ kemenyDisagreement c4Profile output := by
  rw [c4CycleKemenyCost_eq_onPairs]
  exact kemenyDisagreementOnPairs_le_kemenyDisagreement c4Profile output c4CycleOrderedPairs

/-- Every feature-linearly feasible ranking has cyclic-block Kemeny cost at least 24. -/
theorem c4CycleKemenyCost_ge_twentyFour (output : Ranking 18)
    (hfeasible : LinearFeasibleRanking c4Features output) :
    24 ≤ c4CycleKemenyCost output := by
  rcases c4CycleTripleCosts_ge_three output with ⟨h234, h567, h8910, h111213, h141516, h171819⟩
  rcases c4LinearFeasible_hasCycleBreak output hfeasible with
    h10 | h42 | h75 | h108 | h1311 | h1614 | h1917
  · have hpair : c4PairKemenyCost output 0 1 = 6 := by
      rw [c4PairKemenyCost_eq_forwardSupport_of_reversePrefers output 0 1 (by decide) h10]
      decide
    unfold c4CycleKemenyCost
    omega
  · rcases c4LinearFeasible_fullReverse234 output hfeasible h42 with ⟨h32, h43⟩
    have htriple : c4TripleKemenyCost output 2 3 4 = 15 :=
      c4TripleKemenyCost_eq_fifteen_of_fullReverse output 2 3 4 h32 h42 h43
        (by decide) (by decide) (by decide)
    unfold c4CycleKemenyCost
    omega
  · rcases c4LinearFeasible_fullReverse567 output hfeasible h75 with ⟨h65, h76⟩
    have htriple : c4TripleKemenyCost output 5 6 7 = 15 :=
      c4TripleKemenyCost_eq_fifteen_of_fullReverse output 5 6 7 h65 h75 h76
        (by decide) (by decide) (by decide)
    unfold c4CycleKemenyCost
    omega
  · rcases c4LinearFeasible_fullReverse8910 output hfeasible h108 with ⟨h98, h109⟩
    have htriple : c4TripleKemenyCost output 8 9 10 = 15 :=
      c4TripleKemenyCost_eq_fifteen_of_fullReverse output 8 9 10 h98 h108 h109
        (by decide) (by decide) (by decide)
    unfold c4CycleKemenyCost
    omega
  · rcases c4LinearFeasible_fullReverse111213 output hfeasible h1311 with ⟨h1211, h1312⟩
    have htriple : c4TripleKemenyCost output 11 12 13 = 15 :=
      c4TripleKemenyCost_eq_fifteen_of_fullReverse output 11 12 13 h1211 h1311 h1312
        (by decide) (by decide) (by decide)
    unfold c4CycleKemenyCost
    omega
  · rcases c4LinearFeasible_fullReverse141516 output hfeasible h1614 with ⟨h1514, h1615⟩
    have htriple : c4TripleKemenyCost output 14 15 16 = 15 :=
      c4TripleKemenyCost_eq_fifteen_of_fullReverse output 14 15 16 h1514 h1614 h1615
        (by decide) (by decide) (by decide)
    unfold c4CycleKemenyCost
    omega
  · rcases c4LinearFeasible_fullReverse171819 output hfeasible h1917 with ⟨h1817, h1918⟩
    have htriple : c4TripleKemenyCost output 17 18 19 = 15 :=
      c4TripleKemenyCost_eq_fifteen_of_fullReverse output 17 18 19 h1817 h1917 h1918
        (by decide) (by decide) (by decide)
    unfold c4CycleKemenyCost
    omega

/-- Keeping source candidate `1` above `2` forces a costlier triple-cycle break. -/
theorem c4CycleKemenyCost_ge_thirty_of_oneAboveTwo (output : Ranking 18)
    (hfeasible : LinearFeasibleRanking c4Features output)
    (honeAboveTwo : StrictlyPrefers output 0 1) :
    30 ≤ c4CycleKemenyCost output := by
  rcases c4CycleTripleCosts_ge_three output with ⟨h234, h567, h8910, h111213, h141516, h171819⟩
  rcases c4LinearFeasible_hasCycleBreak output hfeasible with
    h10 | h42 | h75 | h108 | h1311 | h1614 | h1917
  · exact (lt_asymm honeAboveTwo h10).elim
  · rcases c4LinearFeasible_fullReverse234 output hfeasible h42 with ⟨h32, h43⟩
    have htriple : c4TripleKemenyCost output 2 3 4 = 15 :=
      c4TripleKemenyCost_eq_fifteen_of_fullReverse output 2 3 4 h32 h42 h43
        (by decide) (by decide) (by decide)
    unfold c4CycleKemenyCost
    omega
  · rcases c4LinearFeasible_fullReverse567 output hfeasible h75 with ⟨h65, h76⟩
    have htriple : c4TripleKemenyCost output 5 6 7 = 15 :=
      c4TripleKemenyCost_eq_fifteen_of_fullReverse output 5 6 7 h65 h75 h76
        (by decide) (by decide) (by decide)
    unfold c4CycleKemenyCost
    omega
  · rcases c4LinearFeasible_fullReverse8910 output hfeasible h108 with ⟨h98, h109⟩
    have htriple : c4TripleKemenyCost output 8 9 10 = 15 :=
      c4TripleKemenyCost_eq_fifteen_of_fullReverse output 8 9 10 h98 h108 h109
        (by decide) (by decide) (by decide)
    unfold c4CycleKemenyCost
    omega
  · rcases c4LinearFeasible_fullReverse111213 output hfeasible h1311 with ⟨h1211, h1312⟩
    have htriple : c4TripleKemenyCost output 11 12 13 = 15 :=
      c4TripleKemenyCost_eq_fifteen_of_fullReverse output 11 12 13 h1211 h1311 h1312
        (by decide) (by decide) (by decide)
    unfold c4CycleKemenyCost
    omega
  · rcases c4LinearFeasible_fullReverse141516 output hfeasible h1614 with ⟨h1514, h1615⟩
    have htriple : c4TripleKemenyCost output 14 15 16 = 15 :=
      c4TripleKemenyCost_eq_fifteen_of_fullReverse output 14 15 16 h1514 h1614 h1615
        (by decide) (by decide) (by decide)
    unfold c4CycleKemenyCost
    omega
  · rcases c4LinearFeasible_fullReverse171819 output hfeasible h1917 with ⟨h1817, h1918⟩
    have htriple : c4TripleKemenyCost output 17 18 19 = 15 :=
      c4TripleKemenyCost_eq_fifteen_of_fullReverse output 17 18 19 h1817 h1917 h1918
        (by decide) (by decide) (by decide)
    unfold c4CycleKemenyCost
    omega

/-- The cyclic lower bound transfers directly to the full Kemeny objective. -/
theorem c4LinearFeasible_kemenyDisagreement_ge_twentyFour (output : Ranking 18)
    (hfeasible : LinearFeasibleRanking c4Features output) :
    24 ≤ kemenyDisagreement c4Profile output :=
  (c4CycleKemenyCost_ge_twentyFour output hfeasible).trans
    (c4CycleKemenyCost_le_kemenyDisagreement output)

/-- An output retaining `1 ≻ 2` has full Kemeny disagreement at least thirty. -/
theorem c4LinearFeasible_kemenyDisagreement_ge_thirty_of_oneAboveTwo (output : Ranking 18)
    (hfeasible : LinearFeasibleRanking c4Features output)
    (honeAboveTwo : StrictlyPrefers output 0 1) :
    30 ≤ kemenyDisagreement c4Profile output :=
  (c4CycleKemenyCost_ge_thirty_of_oneAboveTwo output hfeasible honeAboveTwo).trans
    (c4CycleKemenyCost_le_kemenyDisagreement output)

/-- Every linear-Kemeny minimizer of the literal C.4 profile ranks `2` above `1`. -/
theorem c4KemenyMinimizer_ranksTwoAboveOne (output : Ranking 18)
    (hminimum : IsKemenyMinimizer (LinearFeasibleRanking c4Features) c4Profile output) :
    StrictlyPrefers output 1 0 := by
  have hscore_le : kemenyDisagreement c4Profile output ≤ 24 := by
    calc
      kemenyDisagreement c4Profile output ≤
          kemenyDisagreement c4Profile c4TwoAboveOneRanking :=
        hminimum.2 c4TwoAboveOneRanking c4TwoAboveOneRanking_linearFeasible
      _ = 24 := c4TwoAboveOneRanking_kemenyDisagreement
  rcases strictlyPrefers_or_reverse_of_ne output (by decide : (1 : c4Candidate) ≠ 0) with h10 | h01
  · exact h10
  · have hscore_ge := c4LinearFeasible_kemenyDisagreement_ge_thirty_of_oneAboveTwo output
      hminimum.1 h01
    omega

/-- Candidate `1` is unanimously above candidate `2` in the literal profile. -/
theorem c4Profile_universallyPrefersOneTwo :
    UniversallyPreferred c4Profile (0 : c4Candidate) 1 := by
  decide

/-- Candidate `1` is the top choice of every source voter, hence a majority top choice. -/
theorem c4Profile_majorityTopChoiceOne :
    MajorityTopChoice c4Profile (0 : c4Candidate) := by
  classical
  have hall (voter : Fin 6) : (c4Profile voter) 0 = (0 : c4Candidate) := by
    fin_cases voter <;>
      simp [c4Profile, c4Ranking_v1, c4Ranking_v2, c4Ranking_v3, c4Ranking_v4,
        c4Ranking_v5, c4Ranking_v6, Equiv.swap_apply_def]
  have hfilter : votersSatisfying (fun voter : Fin 6 => firstChoice (c4Profile voter) =
      (0 : c4Candidate)) = Finset.univ := by
    ext voter
    simpa [votersSatisfying, firstChoice] using hall voter
  unfold MajorityTopChoice StrictMajority
  rw [hfilter, Finset.card_univ]
  norm_num

/--
Theorem C.4 on the literal source instance: every linear-Kemeny selector
violates both Pareto optimality and majority consistency.
-/
theorem theoremC_4_linearKemeny_failsParetoAndMajorityConsistency
    (rule : LinearRankAggregationRule (Fin 6) 18 (LinearFeasibleRanking c4Features))
    (hselector : IsKemenySelector (LinearFeasibleRanking c4Features) rule) :
    ¬ ParetoOptimal (LinearFeasibleRanking c4Features) rule ∧
      ¬ MajorityConsistent (LinearFeasibleRanking c4Features) rule := by
  have hminimum := hselector c4Profile
  have htwoAboveOne := c4KemenyMinimizer_ranksTwoAboveOne (rule.run c4Profile) hminimum
  constructor
  · intro hpareto
    have honeAboveTwo := hpareto c4Profile (0 : c4Candidate) 1
      c4Profile_linearFeasible c4Profile_universallyPrefersOneTwo
    exact (lt_asymm honeAboveTwo) htwoAboveOne
  · intro hmajority
    have hfirst := hmajority c4Profile (0 : c4Candidate)
      c4Profile_linearFeasible c4Profile_majorityTopChoiceOne
    have honeAboveTwo := strictlyPrefers_firstChoice_of_ne (rule.run c4Profile)
      (by rw [hfirst]; decide : (1 : c4Candidate) ≠ firstChoice (rule.run c4Profile))
    rw [hfirst] at honeAboveTwo
    exact (lt_asymm honeAboveTwo) htwoAboveOne

/-- The cyclic-pair portion already accounts for all 24 disagreements of the witness. -/
theorem c4TwoAboveOneRanking_cycleKemenyCost :
    c4CycleKemenyCost c4TwoAboveOneRanking = 24 := by
  decide

end
end GeEtAl2024AlignmentAxioms

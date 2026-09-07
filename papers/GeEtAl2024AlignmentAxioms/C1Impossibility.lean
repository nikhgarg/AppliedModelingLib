import AppliedModelingLib.Alignment.Axioms.LinearModel
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# C1 impossibility: Ge et al. (2024), Theorem 3.7

This module begins the nine-candidate construction in Appendix A.6.  The
source's `C1` condition itself is defined in the reusable finite ranking
library as `C1LinearRankAggregationRule`; here we formalize the special
feature configuration and its geometric obstruction.
-/

namespace GeEtAl2024AlignmentAxioms

open AppliedModelingLib.Alignment.Axioms
open AppliedModelingLib.SocialChoice.Ranking

/-- The nine candidates of Appendix A.6: four positive axes, four negative axes, and `c⋆`. -/
abbrev c1Candidate := Candidate 7

/-- The `i`th positive-axis candidate `c⁺ᵢ`. -/
def c1Plus (index : Fin 4) : c1Candidate :=
  ⟨index, by omega⟩

/-- The `i`th negative-axis candidate `c⁻ᵢ`. -/
def c1Minus (index : Fin 4) : c1Candidate :=
  ⟨index + 4, by omega⟩

/-- The special candidate `c⋆`. -/
def c1Star : c1Candidate := ⟨8, by omega⟩

/-- Source feature vectors: `c⁺ᵢ = eᵢ`, `c⁻ᵢ = -eᵢ`, and `c⋆ = (1/5,…,1/5)`. -/
noncomputable def c1Features : c1Candidate → FeatureVector 4 :=
  fun candidate coordinate =>
    if candidate = c1Plus coordinate then 1 else
    if candidate = c1Minus coordinate then -1 else
    if candidate = c1Star then 1 / 5 else 0

theorem c1Plus_ne_star (index : Fin 4) : c1Plus index ≠ c1Star := by
  intro heq
  have := congrArg Fin.val heq
  dsimp [c1Plus, c1Star] at this
  omega

theorem c1Minus_ne_star (index : Fin 4) : c1Minus index ≠ c1Star := by
  intro heq
  have := congrArg Fin.val heq
  dsimp [c1Minus, c1Star] at this
  omega

/-- On a positive axis, the reward is the corresponding coordinate of `θ`. -/
theorem linearReward_c1Plus
    (parameter : LinearRewardParameter 4) (index : Fin 4) :
    linearReward parameter c1Features (c1Plus index) = parameter index := by
  fin_cases index <;>
    simp [linearReward, c1Features, c1Plus, c1Minus, c1Star, Fin.sum_univ_succ]

/-- On a negative axis, the reward is the negative corresponding coordinate of `θ`. -/
theorem linearReward_c1Minus
    (parameter : LinearRewardParameter 4) (index : Fin 4) :
    linearReward parameter c1Features (c1Minus index) = -parameter index := by
  fin_cases index <;>
    simp [linearReward, c1Features, c1Plus, c1Minus, c1Star, Fin.sum_univ_succ]

/-- The special candidate's reward is one fifth of the sum of the four coordinates. -/
theorem linearReward_c1Star
    (parameter : LinearRewardParameter 4) :
    linearReward parameter c1Features c1Star =
      (parameter 0 + parameter 1 + parameter 2 + parameter 3) / 5 := by
  simp [linearReward, c1Features, c1Plus, c1Minus, c1Star, Fin.sum_univ_succ]
  ring

/-- Relabel the four coordinate pairs according to a permutation of `Fin 4`. -/
def c1CoordinateMap (order : Ranking 2) (candidate : c1Candidate) : c1Candidate :=
  if hplus : candidate.val < 4 then
    c1Plus (order ⟨candidate.val, hplus⟩)
  else if hminus : candidate.val < 8 then
    c1Minus (order ⟨candidate.val - 4, by omega⟩)
  else
    c1Star

/-- The coordinate relabeling is a candidate permutation. -/
def c1CoordinateRelabel (order : Ranking 2) : Equiv.Perm c1Candidate where
  toFun := c1CoordinateMap order
  invFun := c1CoordinateMap order.symm
  left_inv candidate := by
    fin_cases candidate <;>
      simp [c1CoordinateMap, c1Plus, c1Minus, c1Star]
  right_inv candidate := by
    fin_cases candidate <;>
      simp [c1CoordinateMap, c1Plus, c1Minus, c1Star]

/-- The ballot of the source's form (4) for the coordinate order `(1,2,3,4)`. -/
def c1BaseBallot : Ranking 7 :=
  (((((Equiv.swap (1 : c1Candidate) 8).trans (Equiv.swap 1 4)).trans
      (Equiv.swap 1 3)).trans (Equiv.swap 1 2)).trans (Equiv.swap 5 7))

/-- The source ballot (4), parameterized by its displayed positive-coordinate order. -/
def c1Ballot (order : Ranking 2) : Ranking 7 :=
  c1BaseBallot.trans (c1CoordinateRelabel order)

@[simp] theorem c1CoordinateRelabel_plus (order : Ranking 2) (index : Fin 4) :
    c1CoordinateRelabel order (c1Plus index) = c1Plus (order index) := by
  simp [c1CoordinateRelabel, c1CoordinateMap, c1Plus]

@[simp] theorem c1CoordinateRelabel_minus (order : Ranking 2) (index : Fin 4) :
    c1CoordinateRelabel order (c1Minus index) = c1Minus (order index) := by
  have hlt : index.val + 4 < 8 := by omega
  simp [c1CoordinateRelabel, c1CoordinateMap, c1Minus, hlt]

@[simp] theorem c1CoordinateRelabel_star (order : Ranking 2) :
    c1CoordinateRelabel order c1Star = c1Star := by
  simp [c1CoordinateRelabel, c1CoordinateMap, c1Star]

theorem c1BaseBallot_positions :
    c1BaseBallot 0 = c1Plus 0 ∧
    c1BaseBallot 1 = c1Star ∧
    c1BaseBallot 2 = c1Plus 1 ∧
    c1BaseBallot 3 = c1Plus 2 ∧
    c1BaseBallot 4 = c1Plus 3 ∧
    c1BaseBallot 5 = c1Minus 3 ∧
    c1BaseBallot 6 = c1Minus 2 ∧
    c1BaseBallot 7 = c1Minus 1 ∧
    c1BaseBallot 8 = c1Minus 0 := by
  decide

theorem c1Ballot_positions (order : Ranking 2) :
    c1Ballot order 0 = c1Plus (order 0) ∧
    c1Ballot order 1 = c1Star ∧
    c1Ballot order 2 = c1Plus (order 1) ∧
    c1Ballot order 3 = c1Plus (order 2) ∧
    c1Ballot order 4 = c1Plus (order 3) ∧
    c1Ballot order 5 = c1Minus (order 3) ∧
    c1Ballot order 6 = c1Minus (order 2) ∧
    c1Ballot order 7 = c1Minus (order 1) ∧
    c1Ballot order 8 = c1Minus (order 0) := by
  rcases c1BaseBallot_positions with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  simp only [c1Ballot, Equiv.trans_apply]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8]
  simp

/-- Coordinate rewards for the source's voter witness with `ε = 1/10`. -/
noncomputable def c1CoordinateReward (rank : Fin 4) : ℝ :=
  match rank.val with
  | 0 => 1
  | 1 => 3 / 10
  | 2 => 1 / 5
  | _ => 1 / 10

/-- The parameter that realizes the source ballot for a given coordinate order. -/
noncomputable def c1BallotParameter (order : Ranking 2) : LinearRewardParameter 4 :=
  fun coordinate => c1CoordinateReward (order.symm coordinate)

/-- Reward by ballot position for the positive-`ε` source witness. -/
noncomputable def c1BallotPositionReward (position : c1Candidate) : ℝ :=
  match position.val with
  | 0 => 1
  | 1 => 8 / 25
  | 2 => 3 / 10
  | 3 => 1 / 5
  | 4 => 1 / 10
  | 5 => -(1 / 10)
  | 6 => -(1 / 5)
  | 7 => -(3 / 10)
  | _ => -1

theorem c1BallotParameter_sum (order : Ranking 2) :
    c1BallotParameter order 0 + c1BallotParameter order 1 +
        c1BallotParameter order 2 + c1BallotParameter order 3 = 8 / 5 := by
  calc
    c1BallotParameter order 0 + c1BallotParameter order 1 +
        c1BallotParameter order 2 + c1BallotParameter order 3 =
        ∑ coordinate, c1BallotParameter order coordinate := by
          simp [Fin.sum_univ_succ]
          ring
    _ = ∑ rank, c1BallotParameter order (order rank) :=
      (Equiv.sum_comp order (c1BallotParameter order)).symm
    _ = 8 / 5 := by
      norm_num [c1BallotParameter, c1CoordinateReward, Fin.sum_univ_succ]

theorem linearReward_c1Ballot_at_position (order : Ranking 2) (position : c1Candidate) :
    linearReward (c1BallotParameter order) c1Features (c1Ballot order position) =
      c1BallotPositionReward position := by
  rcases c1Ballot_positions order with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  fin_cases position
  · change linearReward (c1BallotParameter order) c1Features (c1Ballot order 0) =
      c1BallotPositionReward 0
    rw [h0, linearReward_c1Plus]
    simp [c1BallotParameter, c1CoordinateReward, c1BallotPositionReward]
  · change linearReward (c1BallotParameter order) c1Features (c1Ballot order 1) =
      c1BallotPositionReward 1
    rw [h1, linearReward_c1Star, c1BallotParameter_sum]
    norm_num [c1BallotPositionReward]
  · change linearReward (c1BallotParameter order) c1Features (c1Ballot order 2) =
      c1BallotPositionReward 2
    rw [h2, linearReward_c1Plus]
    simp [c1BallotParameter, c1CoordinateReward, c1BallotPositionReward]
  · change linearReward (c1BallotParameter order) c1Features (c1Ballot order 3) =
      c1BallotPositionReward 3
    rw [h3, linearReward_c1Plus]
    simp [c1BallotParameter, c1CoordinateReward, c1BallotPositionReward]
  · change linearReward (c1BallotParameter order) c1Features (c1Ballot order 4) =
      c1BallotPositionReward 4
    rw [h4, linearReward_c1Plus]
    simp [c1BallotParameter, c1CoordinateReward, c1BallotPositionReward]
  · change linearReward (c1BallotParameter order) c1Features (c1Ballot order 5) =
      c1BallotPositionReward 5
    rw [h5, linearReward_c1Minus]
    simp [c1BallotParameter, c1CoordinateReward, c1BallotPositionReward]
  · change linearReward (c1BallotParameter order) c1Features (c1Ballot order 6) =
      c1BallotPositionReward 6
    rw [h6, linearReward_c1Minus]
    simp [c1BallotParameter, c1CoordinateReward, c1BallotPositionReward]
  · change linearReward (c1BallotParameter order) c1Features (c1Ballot order 7) =
      c1BallotPositionReward 7
    rw [h7, linearReward_c1Minus]
    simp [c1BallotParameter, c1CoordinateReward, c1BallotPositionReward]
  · change linearReward (c1BallotParameter order) c1Features (c1Ballot order 8) =
      c1BallotPositionReward 8
    rw [h8, linearReward_c1Minus]
    simp [c1BallotParameter, c1CoordinateReward, c1BallotPositionReward]

theorem c1BallotPositionReward_strictAnti {first second : c1Candidate}
    (hposition : first < second) :
    c1BallotPositionReward second < c1BallotPositionReward first := by
  revert hposition
  fin_cases first
  all_goals fin_cases second
  all_goals norm_num [c1BallotPositionReward]
  all_goals decide

/-- The positive-`ε` voter witness is nondegenerate on the nine source candidates. -/
theorem c1BallotParameter_nondegenerate (order : Ranking 2) :
    NondegenerateParameter c1Features (c1BallotParameter order) := by
  intro first second hdistinct
  obtain ⟨firstPosition, hfirst⟩ := (c1Ballot order).surjective first
  obtain ⟨secondPosition, hsecond⟩ := (c1Ballot order).surjective second
  subst first
  subst second
  rw [linearReward_c1Ballot_at_position, linearReward_c1Ballot_at_position]
  intro hequal
  by_cases hpositions : firstPosition = secondPosition
  · apply hdistinct
    simpa [hpositions]
  · rcases lt_or_gt_of_ne hpositions with hforward | hreverse
    · have hstrict := c1BallotPositionReward_strictAnti hforward
      linarith
    · have hstrict := c1BallotPositionReward_strictAnti hreverse
      linarith

/-- The positive-`ε` parameter weakly induces exactly the source ballot order. -/
theorem c1BallotParameter_induces (order : Ranking 2) :
    InducesRanking c1Features (c1BallotParameter order) (c1Ballot order) := by
  intro first second hpreference
  obtain ⟨firstPosition, hfirst⟩ := (c1Ballot order).surjective first
  obtain ⟨secondPosition, hsecond⟩ := (c1Ballot order).surjective second
  subst first
  subst second
  have hpositions : firstPosition < secondPosition := by
    simpa [StrictlyPrefers, rankOf] using hpreference
  rw [linearReward_c1Ballot_at_position, linearReward_c1Ballot_at_position]
  exact (c1BallotPositionReward_strictAnti hpositions).le

/-- Every ballot in the source's form (4) is a nondegenerate feasible linear ranking. -/
theorem c1Ballot_linearFeasibleRanking (order : Ranking 2) :
    LinearFeasibleRanking c1Features (c1Ballot order) :=
  ⟨c1BallotParameter order, c1BallotParameter_nondegenerate order,
    c1BallotParameter_induces order⟩

/-- The coordinate orders occurring in Table 1 of Appendix A.6. -/
def c1Order1234 : Ranking 2 := Equiv.refl _
def c1Order2134 : Ranking 2 := Equiv.swap 0 1
def c1Order3124 : Ranking 2 := (Equiv.swap 0 2).trans (Equiv.swap 0 1)
def c1Order3241 : Ranking 2 := (Equiv.swap 0 2).trans (Equiv.swap 0 3)
def c1Order4123 : Ranking 2 :=
  ((Equiv.swap 0 3).trans (Equiv.swap 0 2)).trans (Equiv.swap 0 1)
def c1Order2341 : Ranking 2 :=
  ((Equiv.swap 0 1).trans (Equiv.swap 0 2)).trans (Equiv.swap 0 3)
def c1Order2413 : Ranking 2 :=
  ((Equiv.swap 0 1).trans (Equiv.swap 0 3)).trans (Equiv.swap 0 2)
def c1Order3412 : Ranking 2 := (Equiv.swap 0 2).trans (Equiv.swap 1 3)

/-- Table 1's five-voter profile that Pareto-dominates `c⁺₁` by `c⋆`. -/
def c1ProfilePlus1 : RankingProfile (Fin 5) 7
  | ⟨0, _⟩ => c1Ballot c1Order2134
  | ⟨1, _⟩ => c1Ballot c1Order3124
  | ⟨2, _⟩ => c1Ballot c1Order3241
  | ⟨3, _⟩ => c1Ballot c1Order4123
  | ⟨4, _⟩ => c1Ballot c1Order4123

/-- Table 1's five-voter profile that Pareto-dominates `c⁺₂` by `c⋆`. -/
def c1ProfilePlus2 : RankingProfile (Fin 5) 7
  | ⟨0, _⟩ => c1Ballot c1Order1234
  | ⟨1, _⟩ => c1Ballot c1Order1234
  | ⟨2, _⟩ => c1Ballot c1Order3241
  | ⟨3, _⟩ => c1Ballot c1Order3241
  | ⟨4, _⟩ => c1Ballot c1Order4123

/-- Table 1's five-voter profile that Pareto-dominates `c⁺₃` by `c⋆`. -/
def c1ProfilePlus3 : RankingProfile (Fin 5) 7
  | ⟨0, _⟩ => c1Ballot c1Order1234
  | ⟨1, _⟩ => c1Ballot c1Order1234
  | ⟨2, _⟩ => c1Ballot c1Order2341
  | ⟨3, _⟩ => c1Ballot c1Order2341
  | ⟨4, _⟩ => c1Ballot c1Order4123

/-- Table 1's five-voter profile that Pareto-dominates `c⁺₄` by `c⋆`. -/
def c1ProfilePlus4 : RankingProfile (Fin 5) 7
  | ⟨0, _⟩ => c1Ballot c1Order1234
  | ⟨1, _⟩ => c1Ballot c1Order1234
  | ⟨2, _⟩ => c1Ballot c1Order2413
  | ⟨3, _⟩ => c1Ballot c1Order2413
  | ⟨4, _⟩ => c1Ballot c1Order3412

/-- Select the corresponding Table-1 profile for each positive-axis candidate. -/
def c1ProfileForPlus (index : Fin 4) : RankingProfile (Fin 5) 7 :=
  match index with
  | ⟨0, _⟩ => c1ProfilePlus1
  | ⟨1, _⟩ => c1ProfilePlus2
  | ⟨2, _⟩ => c1ProfilePlus3
  | ⟨3, _⟩ => c1ProfilePlus4

theorem c1ProfilePlus1_feasible : FeasibleProfile (LinearFeasibleRanking c1Features) c1ProfilePlus1 := by
  intro voter
  fin_cases voter
  all_goals apply c1Ballot_linearFeasibleRanking

theorem c1ProfilePlus2_feasible : FeasibleProfile (LinearFeasibleRanking c1Features) c1ProfilePlus2 := by
  intro voter
  fin_cases voter
  all_goals apply c1Ballot_linearFeasibleRanking

theorem c1ProfilePlus3_feasible : FeasibleProfile (LinearFeasibleRanking c1Features) c1ProfilePlus3 := by
  intro voter
  fin_cases voter
  all_goals apply c1Ballot_linearFeasibleRanking

theorem c1ProfilePlus4_feasible : FeasibleProfile (LinearFeasibleRanking c1Features) c1ProfilePlus4 := by
  intro voter
  fin_cases voter
  all_goals apply c1Ballot_linearFeasibleRanking

theorem c1ProfileForPlus_feasible (index : Fin 4) :
    FeasibleProfile (LinearFeasibleRanking c1Features) (c1ProfileForPlus index) := by
  fin_cases index
  · exact c1ProfilePlus1_feasible
  · exact c1ProfilePlus2_feasible
  · exact c1ProfilePlus3_feasible
  · exact c1ProfilePlus4_feasible

/-- All four Table-1 profiles induce the same directed strict-majority relation. -/
theorem c1ProfileForPlus_samePairwiseMajorityRelation (index : Fin 4) :
    SamePairwiseMajorityRelation c1ProfilePlus1 (c1ProfileForPlus index) := by
  fin_cases index <;> intro first second <;> fin_cases first <;> fin_cases second <;> decide

/--
The Appendix-A.6 majority relation is cyclic, so the displayed Theorem 3.7
profile has no PMC ranking.  In particular, it cannot be the infeasible-PMC
witness claimed by the prose after Theorem 3.7; that separate witness appears
in Appendix B.
-/
theorem c1ProfilePlus1_has_no_pairwiseMajorityRanking :
    ¬ ∃ ranking : Ranking 7,
      IsPairwiseMajorityRanking c1ProfilePlus1 ranking := by
  rintro ⟨ranking, hmajority⟩
  have h01 : StrictlyPrefers ranking (c1Plus 0) (c1Plus 1) :=
    (hmajority (c1Plus 0) (c1Plus 1)).mpr (by decide)
  have h12 : StrictlyPrefers ranking (c1Plus 1) (c1Plus 2) :=
    (hmajority (c1Plus 1) (c1Plus 2)).mpr (by decide)
  have h23 : StrictlyPrefers ranking (c1Plus 2) (c1Plus 3) :=
    (hmajority (c1Plus 2) (c1Plus 3)).mpr (by decide)
  have h30 : StrictlyPrefers ranking (c1Plus 3) (c1Plus 0) :=
    (hmajority (c1Plus 3) (c1Plus 0)).mpr (by decide)
  exact lt_asymm (lt_trans (lt_trans h01 h12) h23) h30

/-- In its designated Table-1 profile, `c⋆` is unanimously above the target positive axis. -/
theorem c1ProfileForPlus_star_universallyPreferred (index : Fin 4) :
    UniversallyPreferred (c1ProfileForPlus index) c1Star (c1Plus index) := by
  fin_cases index <;> intro voter <;> fin_cases voter <;> decide

/-- The first Table-1 profile puts `c⋆` unanimously above every negative axis. -/
theorem c1ProfilePlus1_star_universallyPreferred_minus (index : Fin 4) :
    UniversallyPreferred c1ProfilePlus1 c1Star (c1Minus index) := by
  fin_cases index <;> intro voter <;> fin_cases voter <;> decide

/--
Every non-special candidate has a feasible five-voter profile with the source
majority graph in which `c⋆` is unanimously preferred to it.
-/
theorem exists_c1Profile_of_ne_star (candidate : c1Candidate) (hdistinct : candidate ≠ c1Star) :
    ∃ profile : RankingProfile (Fin 5) 7,
      FeasibleProfile (LinearFeasibleRanking c1Features) profile ∧
      SamePairwiseMajorityRelation c1ProfilePlus1 profile ∧
      UniversallyPreferred profile c1Star candidate := by
  fin_cases candidate
  · exact ⟨c1ProfileForPlus 0, c1ProfileForPlus_feasible 0,
      c1ProfileForPlus_samePairwiseMajorityRelation 0,
      c1ProfileForPlus_star_universallyPreferred 0⟩
  · exact ⟨c1ProfileForPlus 1, c1ProfileForPlus_feasible 1,
      c1ProfileForPlus_samePairwiseMajorityRelation 1,
      c1ProfileForPlus_star_universallyPreferred 1⟩
  · exact ⟨c1ProfileForPlus 2, c1ProfileForPlus_feasible 2,
      c1ProfileForPlus_samePairwiseMajorityRelation 2,
      c1ProfileForPlus_star_universallyPreferred 2⟩
  · exact ⟨c1ProfileForPlus 3, c1ProfileForPlus_feasible 3,
      c1ProfileForPlus_samePairwiseMajorityRelation 3,
      c1ProfileForPlus_star_universallyPreferred 3⟩
  · exact ⟨c1ProfilePlus1, c1ProfilePlus1_feasible,
      samePairwiseMajorityRelation_refl c1ProfilePlus1,
      c1ProfilePlus1_star_universallyPreferred_minus 0⟩
  · exact ⟨c1ProfilePlus1, c1ProfilePlus1_feasible,
      samePairwiseMajorityRelation_refl c1ProfilePlus1,
      c1ProfilePlus1_star_universallyPreferred_minus 1⟩
  · exact ⟨c1ProfilePlus1, c1ProfilePlus1_feasible,
      samePairwiseMajorityRelation_refl c1ProfilePlus1,
      c1ProfilePlus1_star_universallyPreferred_minus 2⟩
  · exact ⟨c1ProfilePlus1, c1ProfilePlus1_feasible,
      samePairwiseMajorityRelation_refl c1ProfilePlus1,
      c1ProfilePlus1_star_universallyPreferred_minus 3⟩
  · exact False.elim (hdistinct rfl)

/--
No feasible ranking of the Appendix-A.6 feature instance can put `c⋆` first.
If it did, strict induction would put every positive and negative axis below
the average reward; the four positive inequalities force that average to be
negative, while one positive/negative pair forces it to be positive.
-/
theorem firstChoice_ne_c1Star_of_linearFeasibleRanking
    (ranking : Ranking 7) (hfeasible : LinearFeasibleRanking c1Features ranking) :
    firstChoice ranking ≠ c1Star := by
  intro hstar_first
  obtain ⟨parameter, hnondegenerate, hinduced⟩ := hfeasible
  have hplus : ∀ index : Fin 4, parameter index <
      linearReward parameter c1Features c1Star := by
    intro index
    have hpreference : StrictlyPrefers ranking c1Star (c1Plus index) := by
      rw [← hstar_first]
      exact strictlyPrefers_firstChoice_of_ne ranking (by
        intro heq
        exact c1Plus_ne_star index (heq.trans hstar_first))
    have hstrict := inducesRanking_strictReward_of_nondegenerate c1Features parameter ranking
      hinduced hnondegenerate hpreference
    simpa only [linearReward_c1Plus] using hstrict
  have hminusZero : -parameter 0 < linearReward parameter c1Features c1Star := by
    have hpreference : StrictlyPrefers ranking c1Star (c1Minus 0) := by
      rw [← hstar_first]
      exact strictlyPrefers_firstChoice_of_ne ranking (by
        intro heq
        exact c1Minus_ne_star 0 (heq.trans hstar_first))
    have hstrict := inducesRanking_strictReward_of_nondegenerate c1Features parameter ranking
      hinduced hnondegenerate hpreference
    simpa only [linearReward_c1Minus] using hstrict
  let starReward : ℝ := linearReward parameter c1Features c1Star
  have hsum : parameter 0 + parameter 1 + parameter 2 + parameter 3 = 5 * starReward := by
    dsimp [starReward]
    rw [linearReward_c1Star]
    ring
  have hzero_lt_star : 0 < starReward := by
    have hplusZero := hplus 0
    change parameter 0 < starReward at hplusZero
    change -parameter 0 < starReward at hminusZero
    linarith
  have hsum_lt : parameter 0 + parameter 1 + parameter 2 + parameter 3 < 4 * starReward := by
    have hplusZero := hplus 0
    have hplusOne := hplus 1
    have hplusTwo := hplus 2
    have hplusThree := hplus 3
    change parameter 0 < starReward at hplusZero
    change parameter 1 < starReward at hplusOne
    change parameter 2 < starReward at hplusTwo
    change parameter 3 < starReward at hplusThree
    linarith
  linarith

/--
Theorem 3.7 of Ge et al. (2024), finite source instance: on the Appendix-A.6
nine-candidate feature instance and five voters, every C1 linear ranking rule
violates Pareto optimality.
-/
theorem theorem3_7_C1_failsPareto_finiteInstance
    (rule : LinearRankAggregationRule (Fin 5) 7 (LinearFeasibleRanking c1Features))
    (hC1 : C1LinearRankAggregationRule (LinearFeasibleRanking c1Features) rule) :
    ¬ ParetoOptimal (LinearFeasibleRanking c1Features) rule := by
  intro hPareto
  have houtputFeasible : LinearFeasibleRanking c1Features (rule.run c1ProfilePlus1) :=
    rule.output_feasible c1ProfilePlus1
  have hstarNotFirst : firstChoice (rule.run c1ProfilePlus1) ≠ c1Star :=
    firstChoice_ne_c1Star_of_linearFeasibleRanking (rule.run c1ProfilePlus1) houtputFeasible
  have houtputAboveStar :
      StrictlyPrefers (rule.run c1ProfilePlus1) (firstChoice (rule.run c1ProfilePlus1)) c1Star :=
    strictlyPrefers_firstChoice_of_ne (rule.run c1ProfilePlus1) hstarNotFirst.symm
  obtain ⟨profile, hprofileFeasible, hsameMajority, hunanimous⟩ :=
    exists_c1Profile_of_ne_star (firstChoice (rule.run c1ProfilePlus1)) hstarNotFirst
  have hsameOutput : rule.run c1ProfilePlus1 = rule.run profile :=
    hC1 c1ProfilePlus1 profile hsameMajority
  have hParetoOutput :
      StrictlyPrefers (rule.run profile) c1Star (firstChoice (rule.run c1ProfilePlus1)) :=
    hPareto profile c1Star (firstChoice (rule.run c1ProfilePlus1)) hprofileFeasible hunanimous
  rw [← hsameOutput] at hParetoOutput
  exact lt_asymm houtputAboveStar hParetoOutput

end GeEtAl2024AlignmentAxioms

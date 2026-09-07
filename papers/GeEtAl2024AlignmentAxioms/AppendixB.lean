import GeEtAl2024AlignmentAxioms.MainTheorems
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Appendix B: an infeasible pairwise-majority ranking

This file formalizes the literal seven-candidate, three-voter construction in
Appendix B.  The three submitted rankings are induced by the source feature
vectors, their strict pairwise-majority relation has the displayed unique PMC
ranking, and no nondegenerate linear parameter induces that ranking.
-/

namespace GeEtAl2024AlignmentAxioms

open AppliedModelingLib.Alignment.Axioms
open AppliedModelingLib.SocialChoice.Ranking

/-- The seven candidates in Appendix B. -/
abbrev appendixBCandidate := Candidate 5

/-- The three positive coordinate candidates `c⁺ᵢ`. -/
def appendixBPlus (index : Fin 3) : appendixBCandidate :=
  ⟨index, by omega⟩

/-- The three negative coordinate candidates `c⁻ᵢ`. -/
def appendixBMinus (index : Fin 3) : appendixBCandidate :=
  ⟨index + 3, by omega⟩

/-- The special candidate `a⋆`. -/
def appendixBStar : appendixBCandidate := ⟨6, by omega⟩

theorem appendixBPlus_ne_star (index : Fin 3) : appendixBPlus index ≠ appendixBStar := by
  intro heq
  have hval := congrArg Fin.val heq
  simp [appendixBPlus, appendixBStar] at hval
  omega

theorem appendixBMinus_ne_star (index : Fin 3) : appendixBMinus index ≠ appendixBStar := by
  intro heq
  have hval := congrArg Fin.val heq
  simp [appendixBMinus, appendixBStar] at hval
  omega

/-- Source features: signed coordinate vectors and `a⋆ = (1/4,1/4,1/4)`. -/
noncomputable def appendixBFeatures : appendixBCandidate → FeatureVector 3 :=
  fun candidate coordinate =>
    if candidate = appendixBPlus coordinate then 1 else
    if candidate = appendixBMinus coordinate then -1 else
    if candidate = appendixBStar then 1 / 4 else 0

/-- First source voter ranking: `c⁺₁ ≻ a⋆ ≻ c⁺₂ ≻ c⁺₃ ≻ c⁻₃ ≻ c⁻₂ ≻ c⁻₁`. -/
def appendixBVoter1Ranking : Ranking 5 :=
  ((((Equiv.refl _).trans (Equiv.swap (1 : appendixBCandidate) 6)).trans
    (Equiv.swap 2 1)).trans (Equiv.swap 3 2)).trans (Equiv.swap 4 5)

/-- Second source voter ranking: `c⁺₂ ≻ a⋆ ≻ c⁺₁ ≻ c⁺₃ ≻ c⁻₃ ≻ c⁻₁ ≻ c⁻₂`. -/
def appendixBVoter2Ranking : Ranking 5 :=
  ((((((Equiv.refl _).trans (Equiv.swap (0 : appendixBCandidate) 1)).trans
    (Equiv.swap 0 6)).trans (Equiv.swap 2 0)).trans (Equiv.swap 3 2)).trans
    (Equiv.swap 4 5)).trans (Equiv.swap 4 3)

/-- Third source voter ranking: `c⁺₃ ≻ a⋆ ≻ c⁺₁ ≻ c⁺₂ ≻ c⁻₂ ≻ c⁻₁ ≻ c⁻₃`. -/
def appendixBVoter3Ranking : Ranking 5 :=
  ((((Equiv.refl _).trans (Equiv.swap (0 : appendixBCandidate) 2)).trans
    (Equiv.swap 1 6)).trans (Equiv.swap 3 1)).trans (Equiv.swap 5 3)

/-- The three-voter profile printed in Appendix B. -/
def appendixBProfile : RankingProfile (Fin 3) 5
  | ⟨0, _⟩ => appendixBVoter1Ranking
  | ⟨1, _⟩ => appendixBVoter2Ranking
  | ⟨2, _⟩ => appendixBVoter3Ranking

/-- The displayed PMC ranking in Appendix B. -/
def appendixBPMCRanking : Ranking 5 :=
  (((((Equiv.refl _).trans (Equiv.swap (0 : appendixBCandidate) 6)).trans
    (Equiv.swap 1 0)).trans (Equiv.swap 2 1)).trans (Equiv.swap 3 2)).trans
    (Equiv.swap 4 5)

/-- The source's first voter parameter, with `ε = 1/10`. -/
noncomputable def appendixBVoter1Parameter : LinearRewardParameter 3 :=
  ![1, 1 / 5, 1 / 10]

/-- The source's second voter parameter, with `ε = 1/10`. -/
noncomputable def appendixBVoter2Parameter : LinearRewardParameter 3 :=
  ![1 / 5, 1, 1 / 10]

/-- The source's third voter parameter, with `ε = 1/10`. -/
noncomputable def appendixBVoter3Parameter : LinearRewardParameter 3 :=
  ![1 / 5, 1 / 10, 1]

theorem linearReward_appendixBPlus
    (parameter : LinearRewardParameter 3) (index : Fin 3) :
    linearReward parameter appendixBFeatures (appendixBPlus index) = parameter index := by
  fin_cases index <;>
    simp [linearReward, appendixBFeatures, appendixBPlus, appendixBMinus,
      appendixBStar, Fin.sum_univ_succ]

theorem linearReward_appendixBMinus
    (parameter : LinearRewardParameter 3) (index : Fin 3) :
    linearReward parameter appendixBFeatures (appendixBMinus index) = -parameter index := by
  fin_cases index <;>
    simp [linearReward, appendixBFeatures, appendixBPlus, appendixBMinus,
      appendixBStar, Fin.sum_univ_succ]

theorem linearReward_appendixBStar
    (parameter : LinearRewardParameter 3) :
    linearReward parameter appendixBFeatures appendixBStar =
      (parameter 0 + parameter 1 + parameter 2) / 4 := by
  simp [linearReward, appendixBFeatures, appendixBPlus, appendixBMinus,
    appendixBStar, Fin.sum_univ_succ]
  ring

theorem appendixBVoter1Parameter_nondegenerate :
    NondegenerateParameter appendixBFeatures appendixBVoter1Parameter := by
  intro first second hne
  fin_cases first
  all_goals fin_cases second
  all_goals try { exact (hne rfl).elim }
  all_goals norm_num [linearReward, appendixBFeatures, appendixBPlus, appendixBMinus,
    appendixBStar, appendixBVoter1Parameter, Fin.sum_univ_succ]

theorem appendixBVoter2Parameter_nondegenerate :
    NondegenerateParameter appendixBFeatures appendixBVoter2Parameter := by
  intro first second hne
  fin_cases first
  all_goals fin_cases second
  all_goals try { exact (hne rfl).elim }
  all_goals norm_num [linearReward, appendixBFeatures, appendixBPlus, appendixBMinus,
    appendixBStar, appendixBVoter2Parameter, Fin.sum_univ_succ]

theorem appendixBVoter3Parameter_nondegenerate :
    NondegenerateParameter appendixBFeatures appendixBVoter3Parameter := by
  intro first second hne
  fin_cases first
  all_goals fin_cases second
  all_goals try { exact (hne rfl).elim }
  all_goals norm_num [linearReward, appendixBFeatures, appendixBPlus, appendixBMinus,
    appendixBStar, appendixBVoter3Parameter, Fin.sum_univ_succ]

theorem appendixBVoter1Parameter_induces :
    InducesRanking appendixBFeatures appendixBVoter1Parameter appendixBVoter1Ranking := by
  intro first second hpref
  fin_cases first
  all_goals fin_cases second
  all_goals try { exact (not_strictlyPrefers_self appendixBVoter1Ranking _ hpref).elim }
  all_goals simp [StrictlyPrefers, rankOf, appendixBVoter1Ranking,
    Equiv.swap_apply_def] at hpref
  all_goals norm_num [linearReward,
    appendixBFeatures, appendixBPlus, appendixBMinus, appendixBStar,
    appendixBVoter1Parameter, Fin.sum_univ_succ]

theorem appendixBVoter2Parameter_induces :
    InducesRanking appendixBFeatures appendixBVoter2Parameter appendixBVoter2Ranking := by
  intro first second hpref
  fin_cases first
  all_goals fin_cases second
  all_goals try { exact (not_strictlyPrefers_self appendixBVoter2Ranking _ hpref).elim }
  all_goals simp [StrictlyPrefers, rankOf, appendixBVoter2Ranking,
    Equiv.swap_apply_def] at hpref
  all_goals norm_num [linearReward,
    appendixBFeatures, appendixBPlus, appendixBMinus, appendixBStar,
    appendixBVoter2Parameter, Fin.sum_univ_succ]

theorem appendixBVoter3Parameter_induces :
    InducesRanking appendixBFeatures appendixBVoter3Parameter appendixBVoter3Ranking := by
  intro first second hpref
  fin_cases first
  all_goals fin_cases second
  all_goals try { exact (not_strictlyPrefers_self appendixBVoter3Ranking _ hpref).elim }
  all_goals simp [StrictlyPrefers, rankOf, appendixBVoter3Ranking,
    Equiv.swap_apply_def] at hpref
  all_goals norm_num [linearReward,
    appendixBFeatures, appendixBPlus, appendixBMinus, appendixBStar,
    appendixBVoter3Parameter, Fin.sum_univ_succ]

/-- Every submitted Appendix-B ranking is feasible in the source linear model. -/
theorem appendixBProfile_feasible :
    FeasibleProfile (LinearFeasibleRanking appendixBFeatures) appendixBProfile := by
  intro voter
  fin_cases voter
  · exact ⟨appendixBVoter1Parameter, appendixBVoter1Parameter_nondegenerate,
      appendixBVoter1Parameter_induces⟩
  · exact ⟨appendixBVoter2Parameter, appendixBVoter2Parameter_nondegenerate,
      appendixBVoter2Parameter_induces⟩
  · exact ⟨appendixBVoter3Parameter, appendixBVoter3Parameter_nondegenerate,
      appendixBVoter3Parameter_induces⟩

/-- The displayed ranking exactly realizes every strict pairwise majority. -/
theorem appendixBPMCRanking_isPairwiseMajorityRanking :
    IsPairwiseMajorityRanking appendixBProfile appendixBPMCRanking := by
  intro first second
  fin_cases first <;> fin_cases second <;> decide

/-- The Appendix-B PMC ranking is the unique PMC ranking for its profile. -/
theorem appendixBPMCRanking_unique
    (ranking : Ranking 5) (hmajority : IsPairwiseMajorityRanking appendixBProfile ranking) :
    ranking = appendixBPMCRanking :=
  pairwiseMajorityRanking_unique appendixBProfile ranking appendixBPMCRanking
    hmajority appendixBPMCRanking_isPairwiseMajorityRanking

/-- No linear parameter can place `a⋆` first in the Appendix-B feature instance. -/
theorem firstChoice_ne_appendixBStar_of_linearFeasibleRanking
    (ranking : Ranking 5) (hfeasible : LinearFeasibleRanking appendixBFeatures ranking) :
    firstChoice ranking ≠ appendixBStar := by
  intro hstarFirst
  obtain ⟨parameter, hnondegenerate, hinduced⟩ := hfeasible
  have hplus : ∀ index : Fin 3, parameter index <
      linearReward parameter appendixBFeatures appendixBStar := by
    intro index
    have hpref : StrictlyPrefers ranking appendixBStar (appendixBPlus index) := by
      rw [← hstarFirst]
      exact strictlyPrefers_firstChoice_of_ne ranking (by
        intro heq
        exact appendixBPlus_ne_star index (heq.trans hstarFirst))
    have hstrict := inducesRanking_strictReward_of_nondegenerate
      appendixBFeatures parameter ranking hinduced hnondegenerate hpref
    simpa only [linearReward_appendixBPlus] using hstrict
  have hminusZero : -parameter 0 <
      linearReward parameter appendixBFeatures appendixBStar := by
    have hpref : StrictlyPrefers ranking appendixBStar (appendixBMinus 0) := by
      rw [← hstarFirst]
      exact strictlyPrefers_firstChoice_of_ne ranking (by
        intro heq
        exact appendixBMinus_ne_star 0 (heq.trans hstarFirst))
    have hstrict := inducesRanking_strictReward_of_nondegenerate
      appendixBFeatures parameter ranking hinduced hnondegenerate hpref
    simpa only [linearReward_appendixBMinus] using hstrict
  let starReward : ℝ := linearReward parameter appendixBFeatures appendixBStar
  have hsum : parameter 0 + parameter 1 + parameter 2 = 4 * starReward := by
    dsimp [starReward]
    rw [linearReward_appendixBStar]
    ring
  have hzeroLt : 0 < starReward := by
    have hplusZero := hplus 0
    change parameter 0 < starReward at hplusZero
    change -parameter 0 < starReward at hminusZero
    linarith
  have hsumLt : parameter 0 + parameter 1 + parameter 2 < 3 * starReward := by
    have h0 := hplus 0
    have h1 := hplus 1
    have h2 := hplus 2
    change parameter 0 < starReward at h0
    change parameter 1 < starReward at h1
    change parameter 2 < starReward at h2
    linarith
  linarith

/-- The unique PMC ranking in Appendix B is not linearly feasible. -/
theorem appendixBPMCRanking_not_linearFeasible :
    ¬ LinearFeasibleRanking appendixBFeatures appendixBPMCRanking := by
  intro hfeasible
  have hfirst : firstChoice appendixBPMCRanking = appendixBStar := by decide
  exact firstChoice_ne_appendixBStar_of_linearFeasibleRanking
    appendixBPMCRanking hfeasible hfirst

/-- The complete exact mathematical content of the Appendix-B example. -/
theorem appendixB_uniquePMC_but_infeasible :
    FeasibleProfile (LinearFeasibleRanking appendixBFeatures) appendixBProfile ∧
      IsPairwiseMajorityRanking appendixBProfile appendixBPMCRanking ∧
      (∀ ranking, IsPairwiseMajorityRanking appendixBProfile ranking →
        ranking = appendixBPMCRanking) ∧
      ¬ LinearFeasibleRanking appendixBFeatures appendixBPMCRanking := by
  exact ⟨appendixBProfile_feasible, appendixBPMCRanking_isPairwiseMajorityRanking,
    appendixBPMCRanking_unique, appendixBPMCRanking_not_linearFeasible⟩

end GeEtAl2024AlignmentAxioms

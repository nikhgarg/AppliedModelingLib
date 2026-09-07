import ZhouChenLi2014OptimalPACMultipleArm.CoreDefinitions

/-!
# Deterministic best-arm certificate

This is the deterministic endpoint shared by the source's QE/AR construction
and by any finite alternative schedule: selecting an empirical maximizer is
epsilon-PAC once all empirical means are within `epsilon / 2` of their true
Bernoulli means.
-/

namespace ZhouChenLi2014OptimalPACMultipleArm

open scoped BigOperators

/-- The largest value attained by a score on a nonempty finite arm set. -/
noncomputable def finiteMaximumScore {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (score : Arm → ℝ) : ℝ := by
  classical
  exact (Finset.univ.image score).max' (Finset.image_nonempty.mpr Finset.univ_nonempty)

/-- A finite maximum score is attained by some arm. -/
theorem exists_score_eq_finiteMaximumScore {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (score : Arm → ℝ) : ∃ arm, score arm = finiteMaximumScore score := by
  classical
  have hmem : finiteMaximumScore score ∈ Finset.univ.image score := by
    unfold finiteMaximumScore
    exact Finset.max'_mem _ (Finset.image_nonempty.mpr Finset.univ_nonempty)
  simpa only [Finset.mem_univ, true_and] using (Finset.mem_image.mp hmem)

/-- A fixed, choice-based maximizer of a real score on a nonempty finite arm set. -/
noncomputable def finiteScoreMaximizer {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (score : Arm → ℝ) : Arm := Classical.choose (exists_score_eq_finiteMaximumScore score)

theorem finiteScoreMaximizer_spec {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (score : Arm → ℝ) : score (finiteScoreMaximizer score) = finiteMaximumScore score := by
  classical
  exact Classical.choose_spec (exists_score_eq_finiteMaximumScore score)

theorem score_le_finiteScoreMaximizer {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (score : Arm → ℝ) (arm : Arm) : score arm ≤ score (finiteScoreMaximizer score) := by
  classical
  rw [finiteScoreMaximizer_spec score]
  unfold finiteMaximumScore
  exact Finset.le_max' (Finset.image score Finset.univ) (score arm)
    (Finset.mem_image.mpr ⟨arm, Finset.mem_univ _, rfl⟩)

/--
Uniform `epsilon / 2` empirical-mean accuracy certifies that the empirical
maximizer is an `epsilon`-PAC best arm.
-/
theorem epsilonPACBestArm_of_uniformEstimate {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (mean estimate : Arm → ℝ) (epsilon : ℝ)
    (huniform : ∀ arm, |estimate arm - mean arm| < epsilon / 2) :
    EpsilonPACBestArm mean epsilon (finiteScoreMaximizer estimate) := by
  intro competitor
  have hcompetitor := (abs_lt.mp (huniform competitor)).1
  have hselected := (abs_lt.mp (huniform (finiteScoreMaximizer estimate))).2
  have hmaximal := score_le_finiteScoreMaximizer estimate competitor
  linarith

/-- The non-strict empirical-accuracy version of the best-arm certificate. -/
theorem epsilonPACBestArm_of_uniformEstimate_le {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (mean estimate : Arm → ℝ) (epsilon : ℝ)
    (huniform : ∀ arm, |estimate arm - mean arm| ≤ epsilon / 2) :
    EpsilonPACBestArm mean epsilon (finiteScoreMaximizer estimate) := by
  intro competitor
  have hcompetitor := (abs_le.mp (huniform competitor)).1
  have hselected := (abs_le.mp (huniform (finiteScoreMaximizer estimate))).2
  have hmaximal := score_le_finiteScoreMaximizer estimate competitor
  linarith

end ZhouChenLi2014OptimalPACMultipleArm

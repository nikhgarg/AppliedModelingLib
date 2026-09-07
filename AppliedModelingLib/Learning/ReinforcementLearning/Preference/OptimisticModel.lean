import AppliedModelingLib.Learning.ReinforcementLearning.Preference.RewardAgnostic
import AppliedModelingLib.Learning.ReinforcementLearning.Preference.Trajectory
import AppliedModelingLib.Foundations.Math.FiniteOptimization
import Mathlib.Tactic

/-!
# Optimistic finite-model regret decompositions

This module isolates the reusable deterministic core of optimistic model-based
RL analyses.  Ground-truth containment and optimistic planning reduce regret
to a transition-law total-variation term plus a reward-model term.  Statistical
confidence, martingale, and eluder arguments can then supply cumulative bounds
for those two explicit quantities.
-/

open scoped BigOperators

namespace AppliedModelingLib

namespace PreferenceRL

/-- Expected trajectory reward for one policy in one finite model. -/
noncomputable def finiteModelPolicyValue
    {Model Policy Trajectory : Type*}
    [Fintype Trajectory] [DecidableEq Trajectory]
    (trajectoryLaw : Model → Policy → TrajectoryDistribution Trajectory)
    (model : Model) (policy : Policy) (reward : Trajectory → ℝ) : ℝ :=
  trajectoryDistributionValue (trajectoryLaw model policy) reward

/-- Expected pairwise preference under two independently generated finite
trajectories. -/
noncomputable def finiteModelPairPreferenceValue
    {Model Policy Trajectory : Type*}
    [Fintype Trajectory] [DecidableEq Trajectory]
    (trajectoryLaw : Model → Policy → TrajectoryDistribution Trajectory)
    (model : Model) (firstPolicy secondPolicy : Policy)
    (preference : Trajectory → Trajectory → ℝ) : ℝ :=
  pmfPairExp (trajectoryLaw model firstPolicy)
    (trajectoryLaw model secondPolicy) preference

/-- Changing only the first trajectory law changes a bounded pairwise payoff
by at most its span times total variation. -/
theorem abs_pmfPairExp_sub_first_le_span_mul_pmfTotalVariation
    {Trajectory : Type*} [Fintype Trajectory] [DecidableEq Trajectory]
    (first second opponent : PMF Trajectory)
    (preference : Trajectory → Trajectory → ℝ) (lower upper : ℝ)
    (hlowerUpper : lower ≤ upper)
    (hlower : ∀ firstTrajectory secondTrajectory,
      lower ≤ preference firstTrajectory secondTrajectory)
    (hupper : ∀ firstTrajectory secondTrajectory,
      preference firstTrajectory secondTrajectory ≤ upper) :
    |pmfPairExp first opponent preference - pmfPairExp second opponent preference| ≤
      (upper - lower) * pmfTotalVariation first second := by
  unfold pmfPairExp
  apply abs_pmfExp_sub_le_span_mul_pmfTotalVariation
  · exact hlowerUpper
  · intro trajectory
    calc
      lower = pmfExp opponent (fun _ ↦ lower) := (pmfExp_const opponent lower).symm
      _ ≤ pmfExp opponent
          (fun secondTrajectory ↦ preference trajectory secondTrajectory) :=
        pmfExp_le_pmfExp_of_forall_le opponent _ _
          (fun secondTrajectory ↦ hlower trajectory secondTrajectory)
  · intro trajectory
    exact pmfExp_le_of_forall_le opponent
      (fun secondTrajectory ↦ preference trajectory secondTrajectory)
      upper (fun secondTrajectory ↦ hupper trajectory secondTrajectory)

/-- Changing both independent trajectory laws costs the sum of their two
total-variation distances, times the payoff span. -/
theorem abs_pmfPairExp_sub_le_span_mul_sum_pmfTotalVariation
    {Trajectory : Type*} [Fintype Trajectory] [DecidableEq Trajectory]
    (firstLeft firstRight secondLeft secondRight : PMF Trajectory)
    (preference : Trajectory → Trajectory → ℝ) (lower upper : ℝ)
    (hlowerUpper : lower ≤ upper)
    (hlower : ∀ firstTrajectory secondTrajectory,
      lower ≤ preference firstTrajectory secondTrajectory)
    (hupper : ∀ firstTrajectory secondTrajectory,
      preference firstTrajectory secondTrajectory ≤ upper) :
    |pmfPairExp firstLeft firstRight preference -
        pmfPairExp secondLeft secondRight preference| ≤
      (upper - lower) *
        (pmfTotalVariation firstLeft secondLeft +
          pmfTotalVariation firstRight secondRight) := by
  let middle := pmfPairExp secondLeft firstRight preference
  have hfirst := abs_pmfPairExp_sub_first_le_span_mul_pmfTotalVariation
    firstLeft secondLeft firstRight preference lower upper hlowerUpper hlower hupper
  have hsecond :
      |middle - pmfPairExp secondLeft secondRight preference| ≤
        (upper - lower) * pmfTotalVariation firstRight secondRight := by
    dsimp [middle]
    rw [pmfPairExp_swap secondLeft firstRight preference,
      pmfPairExp_swap secondLeft secondRight preference]
    exact abs_pmfPairExp_sub_first_le_span_mul_pmfTotalVariation
      firstRight secondRight secondLeft (fun right left ↦ preference left right)
      lower upper hlowerUpper (fun right left ↦ hlower left right)
      (fun right left ↦ hupper left right)
  calc
    |pmfPairExp firstLeft firstRight preference -
        pmfPairExp secondLeft secondRight preference| =
      |(pmfPairExp firstLeft firstRight preference - middle) +
        (middle - pmfPairExp secondLeft secondRight preference)| := by congr 1 <;> ring
    _ ≤ |pmfPairExp firstLeft firstRight preference - middle| +
        |middle - pmfPairExp secondLeft secondRight preference| := abs_add_le _ _
    _ ≤ (upper - lower) * pmfTotalVariation firstLeft secondLeft +
        (upper - lower) * pmfTotalVariation firstRight secondRight :=
      add_le_add hfirst hsecond
    _ = (upper - lower) *
        (pmfTotalVariation firstLeft secondLeft +
          pmfTotalVariation firstRight secondRight) := by ring

/-- Worst-case pairwise value of a policy in one finite model/preference pair. -/
noncomputable def finiteModelWorstCaseValue
    {Model Policy Trajectory : Type*}
    [Fintype Policy] [Nonempty Policy]
    [Fintype Trajectory] [DecidableEq Trajectory]
    (trajectoryLaw : Model → Policy → TrajectoryDistribution Trajectory)
    (model : Model) (preference : Trajectory → Trajectory → ℝ)
    (policy : Policy) : ℝ :=
  finiteMin (fun alternative ↦
    finiteModelPairPreferenceValue trajectoryLaw model policy alternative preference)

/-- Maximin value of a finite model/preference pair. -/
noncomputable def finiteModelMaximinValue
    {Model Policy Trajectory : Type*}
    [Fintype Policy] [Nonempty Policy]
    [Fintype Trajectory] [DecidableEq Trajectory]
    (trajectoryLaw : Model → Policy → TrajectoryDistribution Trajectory)
    (model : Model) (preference : Trajectory → Trajectory → ℝ) : ℝ :=
  finiteMax (finiteModelWorstCaseValue trajectoryLaw model preference)

/-- Algorithm 4's optimistic maximin choice. -/
def IsOptimisticMaximinChoice
    {Model Policy Trajectory : Type*}
    [Fintype Policy] [Nonempty Policy]
    [Fintype Trajectory] [DecidableEq Trajectory]
    (trajectoryLaw : Model → Policy → TrajectoryDistribution Trajectory)
    (confidence : Set ((Trajectory → Trajectory → ℝ) × Model))
    (selectedPolicy : Policy) (selectedPreference : Trajectory → Trajectory → ℝ)
    (selectedModel : Model) : Prop :=
  (selectedPreference, selectedModel) ∈ confidence ∧
    ∀ policy preference model, (preference, model) ∈ confidence →
      finiteModelWorstCaseValue trajectoryLaw model preference policy ≤
        finiteModelWorstCaseValue trajectoryLaw selectedModel selectedPreference
          selectedPolicy

/-- Algorithm 4's optimistic best-response choice minimizes jointly over the
current confidence set and the opponent policy. -/
def IsOptimisticBestResponseChoice
    {Model Policy Trajectory : Type*}
    [Fintype Policy] [Nonempty Policy]
    [Fintype Trajectory] [DecidableEq Trajectory]
    (trajectoryLaw : Model → Policy → TrajectoryDistribution Trajectory)
    (confidence : Set ((Trajectory → Trajectory → ℝ) × Model))
    (fixedPolicy selectedAlternative : Policy)
    (selectedPreference : Trajectory → Trajectory → ℝ)
    (selectedModel : Model) : Prop :=
  (selectedPreference, selectedModel) ∈ confidence ∧
    ∀ alternative preference model, (preference, model) ∈ confidence →
      finiteModelPairPreferenceValue trajectoryLaw selectedModel fixedPolicy
          selectedAlternative selectedPreference ≤
        finiteModelPairPreferenceValue trajectoryLaw model fixedPolicy
          alternative preference

/-- Ground-truth containment and the two optimistic planning steps sandwich
true maximin regret by the upper/lower selected-model value gap. -/
theorem optimisticEquilibriumChoice_regret_le_selectedValueGap
    {Model Policy Trajectory : Type*}
    [Fintype Policy] [Nonempty Policy]
    [Fintype Trajectory] [DecidableEq Trajectory]
    (trajectoryLaw : Model → Policy → TrajectoryDistribution Trajectory)
    (confidence : Set ((Trajectory → Trajectory → ℝ) × Model))
    (trueModel : Model) (truePreference : Trajectory → Trajectory → ℝ)
    (upperPolicy lowerPolicy : Policy)
    (upperPreference lowerPreference : Trajectory → Trajectory → ℝ)
    (upperModel lowerModel : Model)
    (htruth : (truePreference, trueModel) ∈ confidence)
    (hupper : IsOptimisticMaximinChoice trajectoryLaw confidence upperPolicy
      upperPreference upperModel)
    (hlower : IsOptimisticBestResponseChoice trajectoryLaw confidence upperPolicy
      lowerPolicy lowerPreference lowerModel) :
    finiteModelMaximinValue trajectoryLaw trueModel truePreference -
        finiteModelWorstCaseValue trajectoryLaw trueModel truePreference upperPolicy ≤
      finiteModelPairPreferenceValue trajectoryLaw upperModel upperPolicy lowerPolicy
          upperPreference -
        finiteModelPairPreferenceValue trajectoryLaw lowerModel upperPolicy lowerPolicy
          lowerPreference := by
  obtain ⟨optimalPolicy, hoptimal⟩ := exists_finiteMax_eq
    (finiteModelWorstCaseValue trajectoryLaw trueModel truePreference)
  have hoptimism : finiteModelMaximinValue trajectoryLaw trueModel truePreference ≤
      finiteModelWorstCaseValue trajectoryLaw upperModel upperPreference upperPolicy := by
    rw [finiteModelMaximinValue, hoptimal]
    exact hupper.2 optimalPolicy truePreference trueModel htruth
  have hupperPair :
      finiteModelWorstCaseValue trajectoryLaw upperModel upperPreference upperPolicy ≤
        finiteModelPairPreferenceValue trajectoryLaw upperModel upperPolicy lowerPolicy
          upperPreference :=
    finiteMin_le _ lowerPolicy
  have hlowerWorst :
      finiteModelPairPreferenceValue trajectoryLaw lowerModel upperPolicy lowerPolicy
          lowerPreference ≤
        finiteModelWorstCaseValue trajectoryLaw trueModel truePreference upperPolicy := by
    apply le_finiteMin
    intro alternative
    exact hlower.2 alternative truePreference trueModel htruth
  linarith

/-- The selected upper/lower model gap is bounded by four transition-TV terms
plus the true-model preference gap.  The coefficient is the exact payoff span
`1`, repairing the unnecessary outer factor two in the printed appendix. -/
theorem optimisticEquilibriumChoice_selectedValueGap_le
    {Model Policy Trajectory : Type*}
    [Fintype Trajectory] [DecidableEq Trajectory]
    (trajectoryLaw : Model → Policy → TrajectoryDistribution Trajectory)
    (trueModel upperModel lowerModel : Model)
    (upperPolicy lowerPolicy : Policy)
    (upperPreference lowerPreference : Trajectory → Trajectory → ℝ)
    (hupperLower : ∀ first second, 0 ≤ upperPreference first second)
    (hupperUpper : ∀ first second, upperPreference first second ≤ 1)
    (hlowerLower : ∀ first second, 0 ≤ lowerPreference first second)
    (hlowerUpper : ∀ first second, lowerPreference first second ≤ 1) :
    finiteModelPairPreferenceValue trajectoryLaw upperModel upperPolicy lowerPolicy
          upperPreference -
        finiteModelPairPreferenceValue trajectoryLaw lowerModel upperPolicy lowerPolicy
          lowerPreference ≤
      pmfTotalVariation (trajectoryLaw upperModel upperPolicy)
          (trajectoryLaw trueModel upperPolicy) +
        pmfTotalVariation (trajectoryLaw upperModel lowerPolicy)
          (trajectoryLaw trueModel lowerPolicy) +
        pmfTotalVariation (trajectoryLaw lowerModel upperPolicy)
          (trajectoryLaw trueModel upperPolicy) +
        pmfTotalVariation (trajectoryLaw lowerModel lowerPolicy)
          (trajectoryLaw trueModel lowerPolicy) +
        (finiteModelPairPreferenceValue trajectoryLaw trueModel upperPolicy lowerPolicy
            upperPreference -
          finiteModelPairPreferenceValue trajectoryLaw trueModel upperPolicy lowerPolicy
            lowerPreference) := by
  have hupperTV := abs_pmfPairExp_sub_le_span_mul_sum_pmfTotalVariation
    (trajectoryLaw upperModel upperPolicy) (trajectoryLaw upperModel lowerPolicy)
    (trajectoryLaw trueModel upperPolicy) (trajectoryLaw trueModel lowerPolicy)
    upperPreference 0 1 (by norm_num) hupperLower hupperUpper
  have hlowerTV := abs_pmfPairExp_sub_le_span_mul_sum_pmfTotalVariation
    (trajectoryLaw lowerModel upperPolicy) (trajectoryLaw lowerModel lowerPolicy)
    (trajectoryLaw trueModel upperPolicy) (trajectoryLaw trueModel lowerPolicy)
    lowerPreference 0 1 (by norm_num) hlowerLower hlowerUpper
  dsimp [finiteModelPairPreferenceValue] at hupperTV hlowerTV ⊢
  have hupperOne := (abs_le.mp hupperTV).2
  have hlowerOne := (abs_le.mp hlowerTV).1
  linarith

/-- The cumulative deterministic decomposition for Algorithm 4.  The
transition-confidence analysis is used only through the sum of the four
selected-policy TV errors, and the preference-likelihood analysis is used
only through the selected upper/lower preference gap under the true model. -/
theorem optimisticEquilibriumChoices_cumulativeRegret_le
    {Time Model Policy Trajectory : Type*}
    [Fintype Time]
    [Fintype Policy] [Nonempty Policy]
    [Fintype Trajectory] [DecidableEq Trajectory]
    (trajectoryLaw : Model → Policy → TrajectoryDistribution Trajectory)
    (confidence : Time → Set ((Trajectory → Trajectory → ℝ) × Model))
    (trueModel : Model) (truePreference : Trajectory → Trajectory → ℝ)
    (upperPolicy lowerPolicy : Time → Policy)
    (upperPreference lowerPreference : Time → Trajectory → Trajectory → ℝ)
    (upperModel lowerModel : Time → Model)
    (transitionBound preferenceBound : ℝ)
    (hupperLower : ∀ time first second, 0 ≤ upperPreference time first second)
    (hupperUpper : ∀ time first second, upperPreference time first second ≤ 1)
    (hlowerLower : ∀ time first second, 0 ≤ lowerPreference time first second)
    (hlowerUpper : ∀ time first second, lowerPreference time first second ≤ 1)
    (htruth : ∀ time, (truePreference, trueModel) ∈ confidence time)
    (hupper : ∀ time,
      IsOptimisticMaximinChoice trajectoryLaw (confidence time)
        (upperPolicy time) (upperPreference time) (upperModel time))
    (hlower : ∀ time,
      IsOptimisticBestResponseChoice trajectoryLaw (confidence time)
        (upperPolicy time) (lowerPolicy time) (lowerPreference time) (lowerModel time))
    (htransition :
      (∑ time,
        (pmfTotalVariation (trajectoryLaw (upperModel time) (upperPolicy time))
            (trajectoryLaw trueModel (upperPolicy time)) +
          pmfTotalVariation (trajectoryLaw (upperModel time) (lowerPolicy time))
            (trajectoryLaw trueModel (lowerPolicy time)) +
          pmfTotalVariation (trajectoryLaw (lowerModel time) (upperPolicy time))
            (trajectoryLaw trueModel (upperPolicy time)) +
          pmfTotalVariation (trajectoryLaw (lowerModel time) (lowerPolicy time))
            (trajectoryLaw trueModel (lowerPolicy time)))) ≤ transitionBound)
    (hpreference :
      (∑ time,
        (finiteModelPairPreferenceValue trajectoryLaw trueModel
            (upperPolicy time) (lowerPolicy time) (upperPreference time) -
          finiteModelPairPreferenceValue trajectoryLaw trueModel
            (upperPolicy time) (lowerPolicy time) (lowerPreference time))) ≤
        preferenceBound) :
    (∑ time,
      (finiteModelMaximinValue trajectoryLaw trueModel truePreference -
        finiteModelWorstCaseValue trajectoryLaw trueModel truePreference
          (upperPolicy time))) ≤
      transitionBound + preferenceBound := by
  calc
    (∑ time,
      (finiteModelMaximinValue trajectoryLaw trueModel truePreference -
        finiteModelWorstCaseValue trajectoryLaw trueModel truePreference
          (upperPolicy time))) ≤
        ∑ time,
          (finiteModelPairPreferenceValue trajectoryLaw (upperModel time)
              (upperPolicy time) (lowerPolicy time) (upperPreference time) -
            finiteModelPairPreferenceValue trajectoryLaw (lowerModel time)
              (upperPolicy time) (lowerPolicy time) (lowerPreference time)) := by
      apply Finset.sum_le_sum
      intro time _
      exact optimisticEquilibriumChoice_regret_le_selectedValueGap
        trajectoryLaw (confidence time) trueModel truePreference
        (upperPolicy time) (lowerPolicy time) (upperPreference time)
        (lowerPreference time) (upperModel time) (lowerModel time)
        (htruth time) (hupper time) (hlower time)
    _ ≤ ∑ time,
        ((pmfTotalVariation (trajectoryLaw (upperModel time) (upperPolicy time))
              (trajectoryLaw trueModel (upperPolicy time)) +
            pmfTotalVariation (trajectoryLaw (upperModel time) (lowerPolicy time))
              (trajectoryLaw trueModel (lowerPolicy time)) +
            pmfTotalVariation (trajectoryLaw (lowerModel time) (upperPolicy time))
              (trajectoryLaw trueModel (upperPolicy time)) +
            pmfTotalVariation (trajectoryLaw (lowerModel time) (lowerPolicy time))
              (trajectoryLaw trueModel (lowerPolicy time))) +
          (finiteModelPairPreferenceValue trajectoryLaw trueModel
              (upperPolicy time) (lowerPolicy time) (upperPreference time) -
            finiteModelPairPreferenceValue trajectoryLaw trueModel
              (upperPolicy time) (lowerPolicy time) (lowerPreference time))) := by
      apply Finset.sum_le_sum
      intro time _
      exact optimisticEquilibriumChoice_selectedValueGap_le
        trajectoryLaw trueModel (upperModel time) (lowerModel time)
        (upperPolicy time) (lowerPolicy time) (upperPreference time)
        (lowerPreference time) (hupperLower time) (hupperUpper time)
        (hlowerLower time) (hlowerUpper time)
    _ =
        (∑ time,
          (pmfTotalVariation (trajectoryLaw (upperModel time) (upperPolicy time))
              (trajectoryLaw trueModel (upperPolicy time)) +
            pmfTotalVariation (trajectoryLaw (upperModel time) (lowerPolicy time))
              (trajectoryLaw trueModel (lowerPolicy time)) +
            pmfTotalVariation (trajectoryLaw (lowerModel time) (upperPolicy time))
              (trajectoryLaw trueModel (upperPolicy time)) +
            pmfTotalVariation (trajectoryLaw (lowerModel time) (lowerPolicy time))
              (trajectoryLaw trueModel (lowerPolicy time)))) +
          ∑ time,
            (finiteModelPairPreferenceValue trajectoryLaw trueModel
                (upperPolicy time) (lowerPolicy time) (upperPreference time) -
              finiteModelPairPreferenceValue trajectoryLaw trueModel
                (upperPolicy time) (lowerPolicy time) (lowerPreference time)) := by
      rw [Finset.sum_add_distrib]
    _ ≤ transitionBound + preferenceBound := add_le_add htransition hpreference

/-- A confidence-set member and policy that jointly maximize finite-model
value over every policy and every feasible reward/model pair. -/
def IsOptimisticModelChoice
    {Model Policy Trajectory : Type*}
    [Fintype Trajectory] [DecidableEq Trajectory]
    (trajectoryLaw : Model → Policy → TrajectoryDistribution Trajectory)
    (confidence : Set ((Trajectory → ℝ) × Model))
    (selectedPolicy : Policy) (selectedReward : Trajectory → ℝ)
    (selectedModel : Model) : Prop :=
  (selectedReward, selectedModel) ∈ confidence ∧
    ∀ policy reward model, (reward, model) ∈ confidence →
      finiteModelPolicyValue trajectoryLaw model policy reward ≤
        finiteModelPolicyValue trajectoryLaw selectedModel selectedPolicy selectedReward

/-- Ground-truth confidence containment plus optimistic planning bounds one
round's true regret by a model-law term and a reward-model term. -/
theorem optimisticModelChoice_regret_le_transition_add_reward
    {Model Policy Trajectory : Type*}
    [Fintype Trajectory] [DecidableEq Trajectory]
    (trajectoryLaw : Model → Policy → TrajectoryDistribution Trajectory)
    (confidence : Set ((Trajectory → ℝ) × Model))
    (trueModel : Model) (trueReward : Trajectory → ℝ)
    (selectedPolicy competitor : Policy)
    (selectedReward : Trajectory → ℝ) (selectedModel : Model)
    (lower upper : ℝ) (hlowerUpper : lower ≤ upper)
    (hselectedLower : ∀ trajectory, lower ≤ selectedReward trajectory)
    (hselectedUpper : ∀ trajectory, selectedReward trajectory ≤ upper)
    (htruth : (trueReward, trueModel) ∈ confidence)
    (hoptimistic : IsOptimisticModelChoice trajectoryLaw confidence
      selectedPolicy selectedReward selectedModel) :
    finiteModelPolicyValue trajectoryLaw trueModel competitor trueReward -
        finiteModelPolicyValue trajectoryLaw trueModel selectedPolicy trueReward ≤
      (upper - lower) *
          pmfTotalVariation (trajectoryLaw selectedModel selectedPolicy)
            (trajectoryLaw trueModel selectedPolicy) +
        (finiteModelPolicyValue trajectoryLaw trueModel selectedPolicy selectedReward -
          finiteModelPolicyValue trajectoryLaw trueModel selectedPolicy trueReward) := by
  have hoptimism := hoptimistic.2 competitor trueReward trueModel htruth
  have htransitionAbs := abs_pmfExp_sub_le_span_mul_pmfTotalVariation
    (trajectoryLaw selectedModel selectedPolicy)
    (trajectoryLaw trueModel selectedPolicy) selectedReward lower upper
    hlowerUpper hselectedLower hselectedUpper
  have htransition :
      finiteModelPolicyValue trajectoryLaw selectedModel selectedPolicy selectedReward -
          finiteModelPolicyValue trajectoryLaw trueModel selectedPolicy selectedReward ≤
        (upper - lower) *
          pmfTotalVariation (trajectoryLaw selectedModel selectedPolicy)
            (trajectoryLaw trueModel selectedPolicy) := by
    exact (abs_le.mp htransitionAbs).2
  dsimp [finiteModelPolicyValue] at hoptimism htransition ⊢
  linarith

/-- The cumulative deterministic OMLE decomposition.  The two aggregate
premises are exactly where a transition-confidence theorem and a
reward-eluder/martingale theorem enter. -/
theorem optimisticModelChoices_cumulativeRegret_le
    {Time Model Policy Trajectory : Type*}
    [Fintype Time]
    [Fintype Trajectory] [DecidableEq Trajectory]
    (trajectoryLaw : Model → Policy → TrajectoryDistribution Trajectory)
    (confidence : Time → Set ((Trajectory → ℝ) × Model))
    (trueModel : Model) (trueReward : Trajectory → ℝ)
    (selectedPolicy : Time → Policy)
    (selectedReward : Time → Trajectory → ℝ)
    (selectedModel : Time → Model)
    (competitor : Policy) (lower upper transitionBound rewardBound : ℝ)
    (hlowerUpper : lower ≤ upper)
    (hselectedLower : ∀ time trajectory, lower ≤ selectedReward time trajectory)
    (hselectedUpper : ∀ time trajectory, selectedReward time trajectory ≤ upper)
    (htruth : ∀ time, (trueReward, trueModel) ∈ confidence time)
    (hoptimistic : ∀ time, IsOptimisticModelChoice trajectoryLaw (confidence time)
      (selectedPolicy time) (selectedReward time) (selectedModel time))
    (htransition :
      (∑ time, pmfTotalVariation
        (trajectoryLaw (selectedModel time) (selectedPolicy time))
        (trajectoryLaw trueModel (selectedPolicy time))) ≤ transitionBound)
    (hreward :
      (∑ time,
        (finiteModelPolicyValue trajectoryLaw trueModel (selectedPolicy time)
          (selectedReward time) -
        finiteModelPolicyValue trajectoryLaw trueModel (selectedPolicy time) trueReward)) ≤
          rewardBound) :
    (∑ time,
      (finiteModelPolicyValue trajectoryLaw trueModel competitor trueReward -
        finiteModelPolicyValue trajectoryLaw trueModel (selectedPolicy time) trueReward)) ≤
      (upper - lower) * transitionBound + rewardBound := by
  calc
    (∑ time,
      (finiteModelPolicyValue trajectoryLaw trueModel competitor trueReward -
        finiteModelPolicyValue trajectoryLaw trueModel (selectedPolicy time) trueReward)) ≤
      ∑ time,
        ((upper - lower) *
            pmfTotalVariation
              (trajectoryLaw (selectedModel time) (selectedPolicy time))
              (trajectoryLaw trueModel (selectedPolicy time)) +
          (finiteModelPolicyValue trajectoryLaw trueModel (selectedPolicy time)
              (selectedReward time) -
            finiteModelPolicyValue trajectoryLaw trueModel (selectedPolicy time) trueReward)) := by
        apply Finset.sum_le_sum
        intro time _
        exact optimisticModelChoice_regret_le_transition_add_reward
          trajectoryLaw (confidence time) trueModel trueReward
          (selectedPolicy time) competitor (selectedReward time) (selectedModel time)
          lower upper hlowerUpper (hselectedLower time) (hselectedUpper time)
          (htruth time) (hoptimistic time)
    _ = (upper - lower) *
          (∑ time, pmfTotalVariation
            (trajectoryLaw (selectedModel time) (selectedPolicy time))
            (trajectoryLaw trueModel (selectedPolicy time))) +
        ∑ time,
          (finiteModelPolicyValue trajectoryLaw trueModel (selectedPolicy time)
              (selectedReward time) -
            finiteModelPolicyValue trajectoryLaw trueModel (selectedPolicy time) trueReward) := by
        rw [Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ (upper - lower) * transitionBound + rewardBound := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left htransition (sub_nonneg.mpr hlowerUpper)) hreward

/-- The reward component of Algorithm 2's joint confidence set. -/
def UniformPerturbedRewardConfidenceSet
    {Trajectory : Type*} (rewardClass : Set (Trajectory → ℝ))
    (data : List (Trajectory × ℝ)) (tolerance : ℝ) : Set (Trajectory → ℝ) :=
  { reward | reward ∈ rewardClass ∧
    ∀ datum ∈ data, |reward datum.1 - datum.2| ≤ tolerance }

/-- Pointwise-close reward feedback keeps the ground-truth reward in every
finite Algorithm-2 reward confidence set. -/
theorem groundTruth_mem_uniformPerturbedRewardConfidenceSet
    {Trajectory : Type*} (rewardClass : Set (Trajectory → ℝ))
    (truth : Trajectory → ℝ) (data : List (Trajectory × ℝ))
    (tolerance : ℝ) (htruth : truth ∈ rewardClass)
    (hfeedback : ∀ datum ∈ data, |truth datum.1 - datum.2| ≤ tolerance) :
    truth ∈ UniformPerturbedRewardConfidenceSet rewardClass data tolerance :=
  ⟨htruth, hfeedback⟩

/-- A uniformly selected iterate induces the corresponding mixture of finite
trajectory laws. -/
noncomputable def uniformIterateTrajectoryDistribution
    {Time Trajectory : Type*}
    [Fintype Time] [DecidableEq Time] [Nonempty Time]
    [Fintype Trajectory] [DecidableEq Trajectory]
    (trajectoryLaw : Time → TrajectoryDistribution Trajectory) :
    TrajectoryDistribution Trajectory :=
  (uniformPMF Time).bind trajectoryLaw

/-- Value of the uniform iterate mixture is the uniform average of iterate
values. -/
theorem uniformIterateTrajectoryDistribution_value
    {Time Trajectory : Type*}
    [Fintype Time] [DecidableEq Time] [Nonempty Time]
    [Fintype Trajectory] [DecidableEq Trajectory]
    (trajectoryLaw : Time → TrajectoryDistribution Trajectory)
    (reward : Trajectory → ℝ) :
    trajectoryDistributionValue
        (uniformIterateTrajectoryDistribution trajectoryLaw) reward =
      pmfExp (uniformPMF Time)
        (fun time ↦ trajectoryDistributionValue (trajectoryLaw time) reward) := by
  unfold trajectoryDistributionValue uniformIterateTrajectoryDistribution
  exact pmfExp_bind (uniformPMF Time) trajectoryLaw reward

/-- Uniform expectation is the ordinary finite sum divided by cardinality. -/
theorem pmfExp_uniformPMF_eq_sum_div_card
    {Time : Type*} [Fintype Time] [Nonempty Time]
    (value : Time → ℝ) :
    pmfExp (uniformPMF Time) value =
      (∑ time, value time) / (Fintype.card Time : ℝ) := by
  classical
  unfold pmfExp
  simp only [uniformPMF_apply_toReal]
  rw [← Finset.mul_sum]
  field_simp

/-- A cumulative regret bound yields epsilon-optimality of the uniform
iterate mixture. -/
theorem uniformIterateTrajectoryDistribution_epsilonOptimal_of_cumulativeRegret
    {Time Policy Trajectory : Type*}
    [Fintype Time] [DecidableEq Time] [Nonempty Time]
    [Fintype Trajectory] [DecidableEq Trajectory]
    (trajectoryLaw : Policy → TrajectoryDistribution Trajectory)
    (policy : Time → Policy) (reward : Trajectory → ℝ)
    (optimalPolicy : Policy) (epsilon : ℝ)
    (hregret :
      (∑ time,
        (trajectoryDistributionValue (trajectoryLaw optimalPolicy) reward -
          trajectoryDistributionValue (trajectoryLaw (policy time)) reward)) ≤
        (Fintype.card Time : ℝ) * epsilon) :
    trajectoryDistributionValue (trajectoryLaw optimalPolicy) reward ≤
      trajectoryDistributionValue
        (uniformIterateTrajectoryDistribution (fun time ↦ trajectoryLaw (policy time))) reward +
          epsilon := by
  rw [uniformIterateTrajectoryDistribution_value,
    pmfExp_uniformPMF_eq_sum_div_card]
  have hcardPos : 0 < (Fintype.card Time : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hsum :
      ∑ time,
        (trajectoryDistributionValue (trajectoryLaw optimalPolicy) reward -
          trajectoryDistributionValue (trajectoryLaw (policy time)) reward) =
        (Fintype.card Time : ℝ) *
            trajectoryDistributionValue (trajectoryLaw optimalPolicy) reward -
          ∑ time, trajectoryDistributionValue (trajectoryLaw (policy time)) reward := by
    rw [Finset.sum_sub_distrib]
    simp [Finset.sum_const, nsmul_eq_mul]
  rw [hsum] at hregret
  rw [← sub_le_iff_le_add]
  apply (le_div_iff₀ hcardPos).2
  nlinarith

end PreferenceRL

end AppliedModelingLib

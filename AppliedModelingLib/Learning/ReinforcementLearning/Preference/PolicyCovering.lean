import AppliedModelingLib.Learning.ReinforcementLearning.Preference.StageIndexedOccupancy
import AppliedModelingLib.Learning.ReinforcementLearning.Preference.RewardAgnostic
import Mathlib.Data.Nat.Lattice

/-!
# Uniform finite-horizon policy covers

The source metric is the maximum, over states and stages, of the `L1`
distance between action laws.  We state cover membership pointwise, which is
equivalent to bounding that finite maximum and avoids an artificial
nonemptiness condition solely to define `max`.
-/

namespace AppliedModelingLib
namespace PreferenceRL

noncomputable section

/-- A finite family of policies is an internal uniform `L1` cover of a policy
class through the given finite horizon. -/
def IsUniformStageIndexedPolicyL1Cover
    {Policy State Action Index : Type*}
    [Fintype Action] [DecidableEq Action] [Fintype Index]
    (interpret : Policy → StageIndexedPolicy State Action)
    (policyClass : Set Policy) (horizon : ℕ) (epsilon : ℝ)
    (center : Index → Policy) : Prop :=
  (∀ index, center index ∈ policyClass) ∧
    ∀ policy, policy ∈ policyClass →
      ∃ index, ∀ time, time < horizon → ∀ state,
        pmfL1Error (interpret policy time state)
          (interpret (center index) time state) ≤ epsilon

/-- The policy covering number is at most `number` when an internal cover
indexed by `Fin number` exists. -/
def StageIndexedPolicyCoveringNumberAtMost
    {Policy State Action : Type*}
    [Fintype Action] [DecidableEq Action]
    (interpret : Policy → StageIndexedPolicy State Action)
    (policyClass : Set Policy) (horizon : ℕ) (epsilon : ℝ)
    (number : ℕ) : Prop :=
  ∃ center : Fin number → Policy,
    IsUniformStageIndexedPolicyL1Cover interpret policyClass horizon epsilon center

/-- Definition 2's minimum integer. If no finite cover exists, this totalized
definition returns zero; all mathematical uses expose finite cover existence. -/
def stageIndexedPolicyCoveringNumber
    {Policy State Action : Type*}
    [Fintype Action] [DecidableEq Action]
    (interpret : Policy → StageIndexedPolicy State Action)
    (policyClass : Set Policy) (horizon : ℕ) (epsilon : ℝ) : ℕ :=
  sInf {number : ℕ |
    StageIndexedPolicyCoveringNumberAtMost
      interpret policyClass horizon epsilon number}

/-- When a finite cover exists, the minimum covering number is itself
attained. -/
theorem stageIndexedPolicyCoveringNumber_spec
    {Policy State Action : Type*}
    [Fintype Action] [DecidableEq Action]
    (interpret : Policy → StageIndexedPolicy State Action)
    (policyClass : Set Policy) (horizon : ℕ) (epsilon : ℝ)
    (hexists : ∃ number,
      StageIndexedPolicyCoveringNumberAtMost
        interpret policyClass horizon epsilon number) :
    StageIndexedPolicyCoveringNumberAtMost interpret policyClass horizon epsilon
      (stageIndexedPolicyCoveringNumber interpret policyClass horizon epsilon) := by
  exact Nat.sInf_mem hexists

/-- Definition 2's minimality property. -/
theorem stageIndexedPolicyCoveringNumber_le
    {Policy State Action : Type*}
    [Fintype Action] [DecidableEq Action]
    (interpret : Policy → StageIndexedPolicy State Action)
    (policyClass : Set Policy) (horizon : ℕ) (epsilon : ℝ) (number : ℕ)
    (hcover : StageIndexedPolicyCoveringNumberAtMost
      interpret policyClass horizon epsilon number) :
    stageIndexedPolicyCoveringNumber interpret policyClass horizon epsilon ≤ number := by
  exact Nat.sInf_le hcover

/-- Enlarging the allowed error preserves a particular finite policy cover. -/
theorem IsUniformStageIndexedPolicyL1Cover.mono_epsilon
    {Policy State Action Index : Type*}
    [Fintype Action] [DecidableEq Action] [Fintype Index]
    {interpret : Policy → StageIndexedPolicy State Action}
    {policyClass : Set Policy} {horizon : ℕ} {firstEpsilon secondEpsilon : ℝ}
    {center : Index → Policy}
    (hcover : IsUniformStageIndexedPolicyL1Cover interpret policyClass horizon
      firstEpsilon center)
    (hepsilon : firstEpsilon ≤ secondEpsilon) :
    IsUniformStageIndexedPolicyL1Cover interpret policyClass horizon
      secondEpsilon center := by
  refine ⟨hcover.1, ?_⟩
  intro policy hpolicy
  obtain ⟨index, hindex⟩ := hcover.2 policy hpolicy
  exact ⟨index, fun time htime state ↦ (hindex time htime state).trans hepsilon⟩

/-- A finite parameter cover induces a policy cover whenever the policy map
transports the parameter radius to the uniform action-law radius. -/
theorem stageIndexedPolicyCoveringNumberAtMost_of_parameterCover
    {Parameter Policy State Action : Type*}
    [Fintype Action] [DecidableEq Action]
    (parameterClass : Set Parameter) (policyOf : Parameter → Policy)
    (interpret : Policy → StageIndexedPolicy State Action)
    (horizon number : ℕ) (parameterRadius epsilon : ℝ)
    (parameterDistance : Parameter → Parameter → ℝ)
    (center : Fin number → Parameter)
    (hcenter : ∀ index, center index ∈ parameterClass)
    (hparameterCover : ∀ parameter, parameter ∈ parameterClass →
      ∃ index, parameterDistance parameter (center index) ≤ parameterRadius)
    (htransport : ∀ first second,
      first ∈ parameterClass → second ∈ parameterClass →
      parameterDistance first second ≤ parameterRadius →
      ∀ time, time < horizon → ∀ state,
        pmfL1Error (interpret (policyOf first) time state)
          (interpret (policyOf second) time state) ≤ epsilon) :
    StageIndexedPolicyCoveringNumberAtMost interpret
      (policyOf '' parameterClass) horizon epsilon number := by
  refine ⟨fun index ↦ policyOf (center index), ?_, ?_⟩
  · intro index
    exact ⟨center index, hcenter index, rfl⟩
  · intro policy hpolicy
    obtain ⟨parameter, hparameter, rfl⟩ := hpolicy
    obtain ⟨index, hdistance⟩ := hparameterCover parameter hparameter
    exact ⟨index, htransport parameter (center index) hparameter
      (hcenter index) hdistance⟩

end

end PreferenceRL
end AppliedModelingLib

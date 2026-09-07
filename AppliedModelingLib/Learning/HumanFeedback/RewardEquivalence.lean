import AppliedModelingLib.Learning.HumanFeedback.Policy

/-!
# Context-shift equivalence of rewards

Preference models identify a reward only up to an additive constant that may
depend on context but not on the response.  This module records that relation
without assuming any particular preference link function.

## Main declarations

- `RewardEquivalent`
- `rewardEquivalent_refl`
- `rewardEquivalent_symm`
- `rewardEquivalent_trans`
-/

namespace AppliedModelingLib
namespace Learning
namespace HumanFeedback

/-- Two rewards differ only by a context-dependent, response-independent shift. -/
def RewardEquivalent {Context Response : Type*}
    (first second : Context → Response → ℝ) : Prop :=
  ∃ shift : Context → ℝ, ∀ context response,
    second context response = first context response + shift context

/-- Every reward is equivalent to itself. -/
theorem rewardEquivalent_refl {Context Response : Type*}
    (reward : Context → Response → ℝ) :
    RewardEquivalent reward reward := by
  refine ⟨fun _ => 0, ?_⟩
  intro context response
  ring

/-- Context-shift reward equivalence is symmetric. -/
theorem rewardEquivalent_symm {Context Response : Type*}
    {first second : Context → Response → ℝ}
    (h : RewardEquivalent first second) :
    RewardEquivalent second first := by
  rcases h with ⟨shift, hshift⟩
  refine ⟨fun context => -shift context, ?_⟩
  intro context response
  rw [hshift context response]
  ring

/-- Context-shift reward equivalence is transitive. -/
theorem rewardEquivalent_trans {Context Response : Type*}
    {first second third : Context → Response → ℝ}
    (hfirst : RewardEquivalent first second)
    (hsecond : RewardEquivalent second third) :
    RewardEquivalent first third := by
  rcases hfirst with ⟨firstShift, hfirstShift⟩
  rcases hsecond with ⟨secondShift, hsecondShift⟩
  refine ⟨fun context => firstShift context + secondShift context, ?_⟩
  intro context response
  rw [hsecondShift context response, hfirstShift context response]
  ring

end HumanFeedback
end Learning
end AppliedModelingLib

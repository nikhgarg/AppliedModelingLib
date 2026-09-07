import AppliedModelingLib.Learning.ReinforcementLearning.Preference.PolicyComparison

/-!
# Robustness to trajectory-value perturbations

This module states the deterministic transfer used by preference-to-reward
interfaces: an approximate optimizer for uniformly perturbed policy values is
also approximately optimal for the underlying policy values.
-/

namespace AppliedModelingLib

namespace PreferenceRL

/-- `candidate` is within `error` of every competitor under a policy score. -/
def EpsilonOptimal {Policy : Type*} (score : Policy → ℝ)
    (candidate : Policy) (error : ℝ) : Prop :=
  ∀ competitor, score competitor ≤ score candidate + error

/-- Two policy-value functions are uniformly close up to a deterministic error. -/
def UniformScorePerturbation {Policy : Type*}
    (truth perturbed : Policy → ℝ) (error : ℝ) : Prop :=
  ∀ policy, |truth policy - perturbed policy| ≤ error

/--
Approximate optimality transfers from perturbed values to true values.  The
`2 * perturbationError` term accounts for the reference policy and the chosen
policy, respectively.
-/
theorem epsilonOptimal_transfer_of_uniformScorePerturbation {Policy : Type*}
    (truth perturbed : Policy → ℝ) (candidate reference : Policy)
    (optimizationError perturbationError : ℝ)
    (hoptimal : EpsilonOptimal perturbed candidate optimizationError)
    (hperturbation : UniformScorePerturbation truth perturbed perturbationError) :
    truth reference ≤ truth candidate + optimizationError + 2 * perturbationError := by
  have hrefDiff : truth reference - perturbed reference ≤ perturbationError :=
    (abs_le.mp (hperturbation reference)).2
  have href : truth reference ≤ perturbed reference + perturbationError := by
    linarith
  have hcandidate : perturbed candidate ≤ truth candidate + perturbationError := by
    linarith [(abs_le.mp (hperturbation candidate)).1]
  have hoptimal' := hoptimal reference
  linarith

end PreferenceRL

end AppliedModelingLib

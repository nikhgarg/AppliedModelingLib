import AppliedModelingLib.Learning.HumanFeedback.BradleyTerry
import AppliedModelingLib.Learning.HumanFeedback.KLRegularized
import AppliedModelingLib.Learning.HumanFeedback.PreferenceLoss
import AppliedModelingLib.Learning.HumanFeedback.RewardEquivalence
import AppliedModelingLib.Learning.HumanFeedback.PlackettLuce

/-!
# Direct Preference Optimization core

This finite API implements the algebraic core of Direct Preference
Optimization: a policy/reference log ratio defines an implicit reward, whose
Bradley--Terry preference probabilities yield the DPO classification loss.
For a nonzero KL weight, the policy obtained by contextwise exponential tilting
represents the original reward up to a context-only shift.

The paper-specific interface remains separate: this module intentionally uses
finite PMFs and exposes the shared algebra required by DPO, Nash-MD, and
related preference-optimization proofs.

## Main declarations

- `policyLogRatio`
- `dpoImplicitReward`
- `dpoPreferenceModel`
- `dpoDatasetNegativeLogLikelihood`
- `dpoEmpiricalNegativeLogLikelihood`
- `dpoOptimalPolicy`
- `dpoKLRegularizedObjective_globalMax_unique`
- `dpoImplicitReward_tilt_equivalent`
- `dpoPreferenceModel_tilt_eq_bradleyTerry`
- `dpoOptimalPolicy_invariant_under_rewardEquivalent`
-/

namespace AppliedModelingLib
namespace Learning
namespace HumanFeedback

/-- Real log ratio of a candidate policy to a reference policy at one response. -/
noncomputable def policyLogRatio {Context Response : Type*}
    (candidate reference : FinitePolicy Context Response)
    (context : Context) (response : Response) : ℝ :=
  Real.log (candidate context response).toReal -
    Real.log (reference context response).toReal

/-- The DPO implicit reward: KL weight times a policy/reference log ratio. -/
noncomputable def dpoImplicitReward {Context Response : Type*}
    (candidate reference : FinitePolicy Context Response) (klWeight : ℝ) :
    Context → Response → ℝ :=
  fun context response => klWeight * policyLogRatio candidate reference context response

/-- Bradley--Terry preference probabilities induced by a DPO implicit reward. -/
noncomputable def dpoPreferenceModel {Context Response : Type*}
    (candidate reference : FinitePolicy Context Response) (klWeight : ℝ) :
    PairwisePreference Context Response :=
  bradleyTerryPreference (dpoImplicitReward candidate reference klWeight)

/--
Negative DPO log likelihood for a dataset of chosen/rejected response pairs.
Sigmoid positivity supplies the finite-real log-loss support certificate.
-/
noncomputable def dpoDatasetNegativeLogLikelihood
    {Context Response : Type*}
    (candidate reference : FinitePolicy Context Response) (klWeight : ℝ)
    (dataset : PairwiseDataset Context Response) : ℝ :=
  pairwiseDatasetNegativeLogLikelihood
    (dpoPreferenceModel candidate reference klWeight) dataset
    (by
      intro observation _
      change 0 < Real.sigmoid _
      exact Real.sigmoid_pos _)

/-- DPO's finite dataset negative log likelihood is nonnegative. -/
theorem dpoDatasetNegativeLogLikelihood_nonneg
    {Context Response : Type*}
    (candidate reference : FinitePolicy Context Response) (klWeight : ℝ)
    (dataset : PairwiseDataset Context Response) :
    0 ≤ dpoDatasetNegativeLogLikelihood candidate reference klWeight dataset := by
  unfold dpoDatasetNegativeLogLikelihood
  apply pairwiseDatasetNegativeLogLikelihood_nonneg

/--
Empirical DPO negative log likelihood, normalized by the size of a nonempty
dataset as in the finite uniform empirical expectation.
-/
noncomputable def dpoEmpiricalNegativeLogLikelihood
    {Context Response : Type*}
    (candidate reference : FinitePolicy Context Response) (klWeight : ℝ)
    (dataset : PairwiseDataset Context Response) (_hnonempty : dataset ≠ []) : ℝ :=
  (dataset.length : ℝ)⁻¹ *
    dpoDatasetNegativeLogLikelihood candidate reference klWeight dataset

/-- A nonempty empirical DPO negative log likelihood is nonnegative. -/
theorem dpoEmpiricalNegativeLogLikelihood_nonneg
    {Context Response : Type*}
    (candidate reference : FinitePolicy Context Response) (klWeight : ℝ)
    (dataset : PairwiseDataset Context Response) (hnonempty : dataset ≠ []) :
    0 ≤ dpoEmpiricalNegativeLogLikelihood candidate reference klWeight dataset hnonempty := by
  unfold dpoEmpiricalNegativeLogLikelihood
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg dataset.length))
    (dpoDatasetNegativeLogLikelihood_nonneg candidate reference klWeight dataset)

/--
The contextwise KL-regularized optimizer of a reward with respect to a
reference policy, using the source paper's `1 / klWeight` tilt convention.
-/
noncomputable def dpoOptimalPolicy {Context Response : Type*}
    [Fintype Response] [DecidableEq Response]
    (reference : FinitePolicy Context Response)
    (reward : Context → Response → ℝ) (klWeight : ℝ) :
    FinitePolicy Context Response :=
  contextExponentialTiltPolicy reference reward klWeight⁻¹

/--
The source Eq. (8) projection of a reward into its normalized
policy-log-ratio representative.  It removes the context-only log partition
term from the reward, leaving a member of the same reward-equivalence class.
-/
noncomputable def dpoRewardProjection {Context Response : Type*}
    [Fintype Response] [DecidableEq Response]
    (reference : FinitePolicy Context Response)
    (reward : Context → Response → ℝ) (klWeight : ℝ) :
    Context → Response → ℝ :=
  fun context response => reward context response -
    klWeight * Real.log
      (Probability.finiteMGF (reference context) (reward context) klWeight⁻¹)

/--
The source's unscaled finite KL-regularized DPO objective, represented as the
positive KL weight times the shared scaled entropy-regularized objective. For
`klWeight > 0`, this multiplication preserves precisely the argmax used by
the DPO tilt.
-/
noncomputable def dpoKLRegularizedObjective
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context)
    (reference candidate : FinitePolicy Context Response)
    (reward : Context → Response → ℝ) (klWeight : ℝ) : ℝ :=
  klWeight * contextExponentialTiltObjective
    contextLaw reference candidate reward klWeight⁻¹

/--
The source Eq. (3) objective is exactly expected reward minus the KL penalty.
The internally shared entropy objective uses the reciprocal temperature, so the
nonzero-weight hypothesis is the bridge between the two normalizations.
-/
theorem dpoKLRegularizedObjective_eq_reward_sub_kl
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context)
    (reference candidate : FinitePolicy Context Response)
    (reward : Context → Response → ℝ) (klWeight : ℝ)
    (hweight : klWeight ≠ 0) :
    dpoKLRegularizedObjective contextLaw reference candidate reward klWeight =
      policyExpectedScore contextLaw candidate reward -
        klWeight * contextAveragedPolicyKLDivergence contextLaw candidate reference := by
  unfold dpoKLRegularizedObjective contextExponentialTiltObjective
    exponentialTiltObjective policyExpectedScore contextAveragedPolicyKLDivergence
  rw [pmfExp_sub, pmfExp_const_mul]
  have hcancel : klWeight * klWeight⁻¹ = 1 := mul_inv_cancel₀ hweight
  calc
    klWeight *
        (klWeight⁻¹ * pmfExp contextLaw (fun context =>
          pmfExp (candidate context) (reward context)) -
          pmfExp contextLaw (fun context =>
            finiteKLDivergence (candidate context) (reference context))) =
      (klWeight * klWeight⁻¹) *
          pmfExp contextLaw (fun context => pmfExp (candidate context) (reward context)) -
        klWeight * pmfExp contextLaw (fun context =>
          finiteKLDivergence (candidate context) (reference context)) := by ring
    _ = policyExpectedScore contextLaw candidate reward -
        klWeight * contextAveragedPolicyKLDivergence contextLaw candidate reference := by
      rw [hcancel]
      change
        1 * policyExpectedScore contextLaw candidate reward -
          klWeight * pmfExp contextLaw (fun context =>
            finiteKLDivergence (candidate context) (reference context)) =
          policyExpectedScore contextLaw candidate reward -
            klWeight * contextAveragedPolicyKLDivergence contextLaw candidate reference
      rw [one_mul]
      have hkl :
          pmfExp contextLaw (fun context =>
            finiteKLDivergence (candidate context) (reference context)) =
            contextAveragedPolicyKLDivergence contextLaw candidate reference := by
        rfl
      rw [hkl]

/-- A full-support reference policy yields a full-support DPO optimal policy. -/
theorem dpoOptimalPolicy_fullSupport {Context Response : Type*}
    [Fintype Response] [DecidableEq Response]
    (reference : FinitePolicy Context Response)
    (reward : Context → Response → ℝ) (klWeight : ℝ)
    (hreference : PolicyFullSupport reference) :
    PolicyFullSupport (dpoOptimalPolicy reference reward klWeight) := by
  intro context
  exact contextExponentialTiltPolicy_fullSupport reference reward klWeight⁻¹ hreference context

/--
For a positive KL weight and full-support reference/context laws, the finite
DPO tilt is the unique global maximizer of the source KL-regularized policy
objective.
-/
theorem dpoKLRegularizedObjective_globalMax_unique
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context)
    (reference candidate : FinitePolicy Context Response)
    (reward : Context → Response → ℝ) (klWeight : ℝ)
    (hweight : 0 < klWeight) (hcontextLaw : PMFFullSupport contextLaw)
    (hreference : PolicyFullSupport reference)
    (hmax : ∀ other : FinitePolicy Context Response,
      dpoKLRegularizedObjective contextLaw reference other reward klWeight ≤
        dpoKLRegularizedObjective contextLaw reference candidate reward klWeight) :
    candidate = dpoOptimalPolicy reference reward klWeight := by
  unfold dpoKLRegularizedObjective at hmax
  unfold dpoOptimalPolicy
  apply contextExponentialTiltObjective_globalMax_unique
    contextLaw reference candidate reward klWeight⁻¹ hcontextLaw hreference
  intro other
  exact le_of_mul_le_mul_left (hmax other) hweight

/-- Equivalent rewards induce the same finite DPO optimal policy. -/
theorem dpoOptimalPolicy_invariant_under_rewardEquivalent
    {Context Response : Type*} [Fintype Response] [DecidableEq Response]
    (reference : FinitePolicy Context Response)
    (first second : Context → Response → ℝ) (klWeight : ℝ)
    (h : RewardEquivalent first second) :
    dpoOptimalPolicy reference second klWeight =
      dpoOptimalPolicy reference first klWeight := by
  rcases h with ⟨shift, hshift⟩
  have hutilities : second = fun context response => first context response + shift context := by
    funext context response
    exact hshift context response
  unfold dpoOptimalPolicy
  rw [hutilities]
  exact contextExponentialTiltPolicy_add_context_constant reference first shift klWeight⁻¹

/--
The source Eq. (5) identity: a reward equals the policy-log-ratio implicit
reward plus its context-only log-partition term.
-/
theorem dpoReward_eq_implicitReward_tilt_add_logPartition {Context Response : Type*}
    [Fintype Response] [DecidableEq Response]
    (reference : FinitePolicy Context Response)
    (reward : Context → Response → ℝ) (klWeight : ℝ)
    (hweight : klWeight ≠ 0) (hreference : PolicyFullSupport reference)
    (context : Context) (response : Response) :
    reward context response =
      dpoImplicitReward (dpoOptimalPolicy reference reward klWeight) reference klWeight
          context response +
        klWeight * Real.log
          (Probability.finiteMGF (reference context) (reward context) klWeight⁻¹) := by
  unfold dpoImplicitReward policyLogRatio dpoOptimalPolicy contextExponentialTiltPolicy
  rw [exponentialTilt_log_ratio (reference context) (reward context) klWeight⁻¹
    (hreference context) response]
  calc
    reward context response = (klWeight * klWeight⁻¹) * reward context response := by
      rw [mul_inv_cancel₀ hweight, one_mul]
    _ = klWeight *
          (klWeight⁻¹ * reward context response -
            Real.log (Probability.finiteMGF (reference context) (reward context) klWeight⁻¹)) +
          klWeight *
            Real.log (Probability.finiteMGF (reference context) (reward context) klWeight⁻¹) := by
      ring

/--
Source Eq. (8) agrees pointwise with the policy/reference log-ratio implicit
reward of the Gibbs-optimal policy.
-/
theorem dpoRewardProjection_eq_implicitReward_tilt {Context Response : Type*}
    [Fintype Response] [DecidableEq Response]
    (reference : FinitePolicy Context Response)
    (reward : Context → Response → ℝ) (klWeight : ℝ)
    (hweight : klWeight ≠ 0) (hreference : PolicyFullSupport reference) :
    dpoRewardProjection reference reward klWeight =
      dpoImplicitReward (dpoOptimalPolicy reference reward klWeight) reference klWeight := by
  funext context response
  have hsource := dpoReward_eq_implicitReward_tilt_add_logPartition
    reference reward klWeight hweight hreference context response
  unfold dpoRewardProjection
  linarith

/--
The DPO implicit reward of the KL-tilted policy is equivalent to the original
reward: their difference is the context-only log partition term.
-/
theorem dpoImplicitReward_tilt_equivalent {Context Response : Type*}
    [Fintype Response] [DecidableEq Response]
    (reference : FinitePolicy Context Response)
    (reward : Context → Response → ℝ) (klWeight : ℝ)
    (hweight : klWeight ≠ 0) (hreference : PolicyFullSupport reference) :
    RewardEquivalent
      (dpoImplicitReward (dpoOptimalPolicy reference reward klWeight) reference klWeight)
      reward := by
  refine ⟨fun context =>
    klWeight * Real.log (Probability.finiteMGF (reference context) (reward context) klWeight⁻¹), ?_⟩
  intro context response
  exact dpoReward_eq_implicitReward_tilt_add_logPartition reference reward klWeight
    hweight hreference context response

/--
The policy-log-ratio representative selected by the DPO tilt satisfies the
source Eq. (9) normalization condition at every context.
-/
theorem dpoImplicitReward_tilt_partition_normalized {Context Response : Type*}
    [Fintype Response] [DecidableEq Response]
    (reference : FinitePolicy Context Response)
    (reward : Context → Response → ℝ) (klWeight : ℝ)
    (hweight : klWeight ≠ 0) (hreference : PolicyFullSupport reference) :
    ∀ context,
      ∑ response, (reference context response).toReal *
        Real.exp
          (dpoImplicitReward (dpoOptimalPolicy reference reward klWeight) reference
            klWeight context response / klWeight) = 1 := by
  intro context
  have hcandidate : PolicyFullSupport
      (dpoOptimalPolicy reference reward klWeight) :=
    dpoOptimalPolicy_fullSupport reference reward klWeight hreference
  calc
    ∑ response, (reference context response).toReal *
        Real.exp
          (dpoImplicitReward (dpoOptimalPolicy reference reward klWeight) reference
            klWeight context response / klWeight) =
        ∑ response, (dpoOptimalPolicy reference reward klWeight context response).toReal := by
          apply Finset.sum_congr rfl
          intro response _
          have hrefpos : 0 < (reference context response).toReal :=
            hreference context response
          have hcandidatepos : 0 <
              (dpoOptimalPolicy reference reward klWeight context response).toReal :=
            hcandidate context response
          unfold dpoImplicitReward policyLogRatio
          have hdivision :
              klWeight *
                  (Real.log
                    (dpoOptimalPolicy reference reward klWeight context response).toReal -
                    Real.log (reference context response).toReal) / klWeight =
                Real.log
                    (dpoOptimalPolicy reference reward klWeight context response).toReal -
                    Real.log (reference context response).toReal := by
              calc
                klWeight *
                    (Real.log
                      (dpoOptimalPolicy reference reward klWeight context response).toReal -
                      Real.log (reference context response).toReal) / klWeight =
                    (klWeight / klWeight) *
                      (Real.log
                        (dpoOptimalPolicy reference reward klWeight context response).toReal -
                        Real.log (reference context response).toReal) := by ring
                _ = Real.log
                    (dpoOptimalPolicy reference reward klWeight context response).toReal -
                    Real.log (reference context response).toReal := by
                      rw [div_self hweight, one_mul]
          rw [hdivision, Real.exp_sub, Real.exp_log hcandidatepos,
            Real.exp_log hrefpos]
          field_simp
    _ = 1 := pmfToRealSum (dpoOptimalPolicy reference reward klWeight context)

/--
The DPO tilt supplies a finite, normalized policy-log-ratio representative of
the reward's equivalence class.
-/
theorem dpoImplicitReward_tilt_is_normalized_representative {Context Response : Type*}
    [Fintype Response] [DecidableEq Response]
    (reference : FinitePolicy Context Response)
    (reward : Context → Response → ℝ) (klWeight : ℝ)
    (hweight : klWeight ≠ 0) (hreference : PolicyFullSupport reference) :
    RewardEquivalent
        (dpoImplicitReward (dpoOptimalPolicy reference reward klWeight) reference klWeight)
        reward ∧
      ∀ context,
        ∑ response, (reference context response).toReal *
          Real.exp
            (dpoImplicitReward (dpoOptimalPolicy reference reward klWeight) reference
              klWeight context response / klWeight) = 1 :=
  ⟨dpoImplicitReward_tilt_equivalent reference reward klWeight hweight hreference,
    dpoImplicitReward_tilt_partition_normalized reference reward klWeight hweight hreference⟩

/--
At the KL-tilted policy, the DPO Bradley--Terry model is exactly the
Bradley--Terry model of the original reward; the partition term is absent.
-/
theorem dpoPreferenceModel_tilt_eq_bradleyTerry {Context Response : Type*}
    [Fintype Response] [DecidableEq Response]
    (reference : FinitePolicy Context Response)
    (reward : Context → Response → ℝ) (klWeight : ℝ)
    (hweight : klWeight ≠ 0) (hreference : PolicyFullSupport reference) :
    dpoPreferenceModel (dpoOptimalPolicy reference reward klWeight) reference klWeight =
      bradleyTerryPreference reward := by
  unfold dpoPreferenceModel
  exact bradleyTerryPreference_invariant
    (dpoImplicitReward_tilt_equivalent reference reward klWeight hweight hreference)

end HumanFeedback
end Learning
end AppliedModelingLib

import AppliedModelingLib.Foundations.Probability.FiniteKLDuality
import AppliedModelingLib.GameTheory.PreferenceGame.ConstrainedMinimax

/-!
# Finite KL duality for context-free preference games

This module lifts the finite constrained-to-regularized utility duality to a
finite antisymmetric preference game.  The source NLHF proposition is
context-free: fixing a symmetric constrained equilibrium turns the opponent's
best-response problem into one finite KL-constrained linear utility problem.

## Main declarations

- `contextFreeOpponentUtility`
- `IsContextFreeExtendedRegularizedPreferenceGameEquilibrium`
- `finiteKL_constrainedPreferenceGame_is_extended_regularized`
- `finiteKLPreferenceMaximin_is_extended_regularized`
-/

namespace AppliedModelingLib
namespace GameTheory
namespace PreferenceGame

open Learning.HumanFeedback

noncomputable section

/-- The utility maximized by an opponent against a fixed first policy in the
centered context-free preference game. -/
def contextFreeOpponentUtility
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response) (policy : PMF Response) :
    Response → ℝ :=
  fun response =>
    -pmfExp policy (fun selected =>
      preference.prob PUnit.unit selected response - (1 : ℝ) / 2)

/-- The opponent utility expectation is the negative centered game payoff. -/
theorem pmfExp_contextFreeOpponentUtility_eq_neg_centeredPreferencePayoff
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response)
    (policy opponent : PMF Response) :
    pmfExp opponent (contextFreeOpponentUtility preference policy) =
      -contextFreeCenteredPreferencePayoff preference policy opponent := by
  have hleft :
      pmfExp opponent (fun response =>
        pmfExp policy (fun selected =>
          preference.prob PUnit.unit selected response - (1 : ℝ) / 2)) =
        pmfPairExp policy opponent (fun selected response =>
          preference.prob PUnit.unit selected response - (1 : ℝ) / 2) := by
    change pmfPairExp opponent policy (fun response selected =>
      preference.prob PUnit.unit selected response - (1 : ℝ) / 2) = _
    rw [pmfPairExp_swap]
  unfold contextFreeOpponentUtility contextFreeCenteredPreferencePayoff
    centeredPreferenceGamePayoff preferenceGamePayoff
    Learning.HumanFeedback.policyPreference
  rw [pmfExp_pure, pmfExp_neg]
  have hpair :
      pmfPairExp policy opponent
          (fun selected response =>
            preference.prob PUnit.unit selected response - (1 : ℝ) / 2) =
        pmfPairExp policy opponent (preference.prob PUnit.unit) - (1 : ℝ) / 2 := by
    rw [pmfPairExp_sub]
    have hconstant :
        pmfPairExp policy opponent (fun _ _ => (1 : ℝ) / 2) = (1 : ℝ) / 2 := by
      simp [pmfPairExp]
    rw [hconstant]
  rw [hleft, hpair]

/-- A centered context-free preference payoff is zero against itself. -/
theorem contextFreeCenteredPreferencePayoff_self_eq_zero
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response) (policy : PMF Response) :
    contextFreeCenteredPreferencePayoff preference policy policy = 0 := by
  unfold contextFreeCenteredPreferencePayoff
  have hswap := centeredPreferenceGamePayoff_swap_eq_neg
    (PMF.pure PUnit.unit) preference (fun _ => policy) (fun _ => policy)
  linarith

/--
Extended-weight context-free regularized preference-game equilibrium.  A
finite branch is the centered form of Eq. (15); the top branch is the source's
`λ = ∞` zero-radius reference-policy convention.
-/
def IsContextFreeExtendedRegularizedPreferenceGameEquilibrium
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response)
    (reference policy : PMF Response) (klWeight : WithTop ℝ) : Prop :=
  (∃ finiteWeight : ℝ, klWeight = (finiteWeight : WithTop ℝ) ∧ 0 ≤ finiteWeight ∧
    ∀ opponent : PMF Response,
      0 ≤ contextFreeCenteredPreferencePayoff preference policy opponent +
        finiteWeight *
          (finiteKLDivergence opponent reference -
            finiteKLDivergence policy reference)) ∨
  (klWeight = ⊤ ∧ policy = reference)

/-- The context-free centered preference payoff is antisymmetric. -/
theorem contextFreeCenteredPreferencePayoff_swap_eq_neg
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response)
    (first second : PMF Response) :
    contextFreeCenteredPreferencePayoff preference second first =
      -contextFreeCenteredPreferencePayoff preference first second := by
  unfold contextFreeCenteredPreferencePayoff
  exact centeredPreferenceGamePayoff_swap_eq_neg
    (PMF.pure PUnit.unit) preference (fun _ => first) (fun _ => second)

/--
An extended regularized context-free equilibrium is a constrained maximin
policy at the KL radius it attains.  For finite weights the regularized
inequality implies that the policy wins every opponent with no larger KL
divergence.  At infinite weight, full support makes the zero-radius feasible
set the singleton reference policy.  Antisymmetry then lets the policy itself
serve as an attained worst response, yielding the source `argmax min` object
rather than only an equilibrium-shaped surrogate.
-/
theorem contextFreeExtendedRegularizedPreferenceGameEquilibrium_is_finiteKLPreferenceMaximinAtAttainedKL
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response)
    (reference policy : PMF Response) (klWeight : WithTop ℝ)
    (hreference : PMFFullSupport reference)
    (hregularized : IsContextFreeExtendedRegularizedPreferenceGameEquilibrium
      preference reference policy klWeight) :
    IsFiniteKLPreferenceMaximin preference reference
      (finiteKLDivergence policy reference) policy := by
  have hself : contextFreeCenteredPreferencePayoff preference policy policy = 0 :=
    contextFreeCenteredPreferencePayoff_self_eq_zero preference policy
  have hwin : ∀ opponent : PMF Response,
      finiteKLDivergence opponent reference ≤ finiteKLDivergence policy reference →
        0 ≤ contextFreeCenteredPreferencePayoff preference policy opponent := by
    intro opponent hopponent
    rcases hregularized with
      ⟨finiteWeight, _hweight, hfiniteWeight_nonneg, hequilibrium⟩ |
        ⟨_hweight_top, hpolicy_reference⟩
    · have hequilibrium_opponent := hequilibrium opponent
      have hpenalty := mul_le_mul_of_nonneg_left hopponent hfiniteWeight_nonneg
      linarith
    · subst policy
      have hopponent_zero : finiteKLDivergence opponent reference ≤ 0 := by
        simpa using hopponent
      have hopponent_reference :=
        (finiteKLDivergence_le_zero_iff_eq opponent reference hreference).mp hopponent_zero
      subst opponent
      rw [contextFreeCenteredPreferencePayoff_self_eq_zero]
  refine ⟨le_rfl, policy, le_rfl, ?_, ?_⟩
  · intro opponent hopponent
    rw [hself]
    exact hwin opponent hopponent
  · intro candidate hcandidate
    have hpolicy_candidate := hwin candidate hcandidate
    rw [contextFreeCenteredPreferencePayoff_swap_eq_neg, hself]
    linarith

/--
Finite constrained-to-regularized duality for a symmetric context-free
preference game.  The scalar duality theorem is applied to the fixed-policy
opponent utility.  Antisymmetry supplies its zero self-payoff, so the resulting
regularized best-response inequality is exactly the symmetric game condition.
-/
theorem finiteKL_constrainedPreferenceGame_is_extended_regularized
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response)
    (reference policy : PMF Response) (klBudget : ℝ)
    (hreference : PMFFullSupport reference)
    (hfeasible : finiteKLDivergence policy reference ≤ klBudget)
    (hgame : ∀ opponent : PMF Response,
      finiteKLDivergence opponent reference ≤ klBudget →
        0 ≤ contextFreeCenteredPreferencePayoff preference policy opponent) :
    ∃ klWeight : WithTop ℝ,
      IsContextFreeExtendedRegularizedPreferenceGameEquilibrium
        preference reference policy klWeight := by
  have hself : contextFreeCenteredPreferencePayoff preference policy policy = 0 :=
    contextFreeCenteredPreferencePayoff_self_eq_zero preference policy
  have hmax : ∀ opponent : PMF Response,
      finiteKLDivergence opponent reference ≤ klBudget →
        pmfExp opponent (contextFreeOpponentUtility preference policy) ≤
          pmfExp policy (contextFreeOpponentUtility preference policy) := by
    intro opponent hopponent
    rw [pmfExp_contextFreeOpponentUtility_eq_neg_centeredPreferencePayoff,
      pmfExp_contextFreeOpponentUtility_eq_neg_centeredPreferencePayoff, hself]
    have hwin := hgame opponent hopponent
    linarith
  obtain ⟨klWeight, hregularized⟩ :=
    finiteKL_constrainedUtilityMax_is_extended_regularized
      reference policy (contextFreeOpponentUtility preference policy) klBudget
      hreference hfeasible hmax
  refine ⟨klWeight, ?_⟩
  rcases hregularized with ⟨finiteWeight, hweight, hnonneg, hmaxRegularized⟩ |
      ⟨htop, hreferencePolicy⟩
  · left
    refine ⟨finiteWeight, hweight, hnonneg, ?_⟩
    intro opponent
    have hregularizedOpponent := hmaxRegularized opponent
    rw [pmfExp_contextFreeOpponentUtility_eq_neg_centeredPreferencePayoff,
      pmfExp_contextFreeOpponentUtility_eq_neg_centeredPreferencePayoff, hself]
      at hregularizedOpponent
    linarith
  · exact Or.inr ⟨htop, hreferencePolicy⟩

/--
The attained finite source `argmax min` definition of constrained NLHF has an
extended nonnegative regularization weight.  The existing minimax bridge first
turns the source maximin policy into its symmetric constrained equilibrium;
the preceding theorem then supplies the finite duality argument.
-/
theorem finiteKLPreferenceMaximin_is_extended_regularized
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response)
    (reference policy : PMF Response) (klBudget : ℝ)
    (hreference : PMFFullSupport reference)
    (hmaximin : IsFiniteKLPreferenceMaximin preference reference klBudget policy) :
    ∃ klWeight : WithTop ℝ,
      IsContextFreeExtendedRegularizedPreferenceGameEquilibrium
        preference reference policy klWeight := by
  have hequilibrium := finiteKLPreferenceMaximin_isConstrainedPreferenceGameEquilibrium
    preference reference klBudget policy hmaximin
  have hfeasible : finiteKLDivergence policy reference ≤ klBudget := by
    have h := hequilibrium.1
    unfold Learning.HumanFeedback.InContextAveragedKLBall
      Learning.HumanFeedback.contextAveragedPolicyKLDivergence
      Learning.HumanFeedback.pointwisePolicyKLDivergence at h
    simpa using h
  apply finiteKL_constrainedPreferenceGame_is_extended_regularized
    preference reference policy klBudget hreference hfeasible
  intro opponent hopponent
  have hopponentGame : Learning.HumanFeedback.InContextAveragedKLBall
      (PMF.pure PUnit.unit) (fun _ => reference) klBudget (fun _ => opponent) := by
    unfold Learning.HumanFeedback.InContextAveragedKLBall
      Learning.HumanFeedback.contextAveragedPolicyKLDivergence
      Learning.HumanFeedback.pointwisePolicyKLDivergence
    simpa using hopponent
  have hwin := hequilibrium.2 (fun _ => opponent) hopponentGame
  change 0 ≤ preferenceGamePayoff (PMF.pure PUnit.unit) preference
    (fun _ => policy) (fun _ => opponent) - (1 : ℝ) / 2
  linarith

end

end PreferenceGame
end GameTheory
end AppliedModelingLib

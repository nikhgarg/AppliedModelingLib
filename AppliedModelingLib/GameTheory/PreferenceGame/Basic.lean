import AppliedModelingLib.Learning.HumanFeedback.KLRegularized
import AppliedModelingLib.Learning.HumanFeedback.PairwisePreference

/-!
# Finite preference games

This module gives the finite constant-sum game induced by a valid pairwise
preference model.  Its unregularized payoff is the context-averaged probability
that the first policy's response wins against the second policy's response.
Centering at one half yields an antisymmetric zero-sum payoff.  The regularized
payoff matches the symmetric KL correction used by NLHF.

No equilibrium-existence theorem is assumed here; that is a separate finite
minimax obligation.

## Main declarations

- `preferenceGamePayoff`
- `centeredPreferenceGamePayoff`
- `IsPreferenceGameEquilibrium`
- `IsApproximatePreferenceGameEquilibrium`
- `IsMaximalLottery`
- `IsApproximateMaximalLottery`
- `regularizedPreferenceGamePayoff`
- `IsRegularizedPreferenceGameEquilibrium`
-/

namespace AppliedModelingLib
namespace GameTheory
namespace PreferenceGame

/-- The finite probability that the first policy wins a pairwise comparison. -/
noncomputable abbrev preferenceGamePayoff
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (preference : Learning.HumanFeedback.PairwisePreference Context Response)
    (first second : Learning.HumanFeedback.FinitePolicy Context Response) : ℝ :=
  Learning.HumanFeedback.policyPreference contextLaw preference first second

/-- Centered preference-game payoff, whose swap is the additive inverse. -/
noncomputable def centeredPreferenceGamePayoff
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (preference : Learning.HumanFeedback.PairwisePreference Context Response)
    (first second : Learning.HumanFeedback.FinitePolicy Context Response) : ℝ :=
  preferenceGamePayoff contextLaw preference first second - 1 / 2

/-- The unregularized preference-game payoff is constant sum. -/
theorem preferenceGamePayoff_add_swap
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (preference : Learning.HumanFeedback.PairwisePreference Context Response)
    (first second : Learning.HumanFeedback.FinitePolicy Context Response) :
    preferenceGamePayoff contextLaw preference first second +
      preferenceGamePayoff contextLaw preference second first = 1 :=
  Learning.HumanFeedback.policyPreference_add_swap contextLaw preference first second

/-- Every policy ties itself with preference probability one half. -/
theorem preferenceGamePayoff_self
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context)
    (preference : Learning.HumanFeedback.PairwisePreference Context Response)
    (policy : Learning.HumanFeedback.FinitePolicy Context Response) :
    preferenceGamePayoff contextLaw preference policy policy = 1 / 2 := by
  have hsum := preferenceGamePayoff_add_swap contextLaw preference policy policy
  linarith

/-- The preference-game payoff is affine in the first policy under binary mixing. -/
theorem preferenceGamePayoff_binaryMixturePolicy_left
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (preference : Learning.HumanFeedback.PairwisePreference Context Response)
    (p : NNReal) (hp : p ≤ 1)
    (selected unselected opponent : Learning.HumanFeedback.FinitePolicy Context Response) :
    preferenceGamePayoff contextLaw preference
        (Learning.HumanFeedback.binaryMixturePolicy p hp selected unselected) opponent =
      p.toReal * preferenceGamePayoff contextLaw preference selected opponent +
        (1 - p.toReal) * preferenceGamePayoff contextLaw preference unselected opponent :=
  Learning.HumanFeedback.policyPreference_binaryMixturePolicy_left
    contextLaw preference p hp selected unselected opponent

/-- The preference-game payoff is affine in the second policy under binary mixing. -/
theorem preferenceGamePayoff_binaryMixturePolicy_right
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (preference : Learning.HumanFeedback.PairwisePreference Context Response)
    (p : NNReal) (hp : p ≤ 1)
    (first selected unselected : Learning.HumanFeedback.FinitePolicy Context Response) :
    preferenceGamePayoff contextLaw preference first
        (Learning.HumanFeedback.binaryMixturePolicy p hp selected unselected) =
      p.toReal * preferenceGamePayoff contextLaw preference first selected +
        (1 - p.toReal) * preferenceGamePayoff contextLaw preference first unselected :=
  Learning.HumanFeedback.policyPreference_binaryMixturePolicy_right
    contextLaw preference p hp first selected unselected

/-- The centered preference-game payoff is antisymmetric. -/
theorem centeredPreferenceGamePayoff_swap_eq_neg
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (preference : Learning.HumanFeedback.PairwisePreference Context Response)
    (first second : Learning.HumanFeedback.FinitePolicy Context Response) :
    centeredPreferenceGamePayoff contextLaw preference second first =
      -centeredPreferenceGamePayoff contextLaw preference first second := by
  unfold centeredPreferenceGamePayoff
  have hsum := preferenceGamePayoff_add_swap contextLaw preference first second
  linarith

/-- A policy that wins against every alternative policy is a preference-game equilibrium. -/
def IsPreferenceGameEquilibrium
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (preference : Learning.HumanFeedback.PairwisePreference Context Response)
    (policy : Learning.HumanFeedback.FinitePolicy Context Response) : Prop :=
  ∀ alternative, 1 / 2 ≤ preferenceGamePayoff contextLaw preference policy alternative

/--
An additive-approximate preference-game equilibrium.  The approximation is a
win-probability shortfall: every alternative is beaten with probability at
least `1 / 2 - approximation`.
-/
def IsApproximatePreferenceGameEquilibrium
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (approximation : ℝ)
    (contextLaw : PMF Context) (preference : Learning.HumanFeedback.PairwisePreference Context Response)
    (policy : Learning.HumanFeedback.FinitePolicy Context Response) : Prop :=
  ∀ alternative, 1 / 2 - approximation ≤
    preferenceGamePayoff contextLaw preference policy alternative

/--
The maximal-lottery condition for a finite preference game: its centered
win-margin against every alternative policy is nonnegative.  In the
context-free social-choice specialization, this is the usual maximal-lottery
inequality against every lottery over alternatives.
-/
def IsMaximalLottery
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (preference : Learning.HumanFeedback.PairwisePreference Context Response)
    (policy : Learning.HumanFeedback.FinitePolicy Context Response) : Prop :=
  ∀ alternative, 0 ≤ centeredPreferenceGamePayoff contextLaw preference policy alternative

/-- An additive-approximate maximal lottery in the centered game. -/
def IsApproximateMaximalLottery
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (approximation : ℝ)
    (contextLaw : PMF Context) (preference : Learning.HumanFeedback.PairwisePreference Context Response)
    (policy : Learning.HumanFeedback.FinitePolicy Context Response) : Prop :=
  ∀ alternative, -approximation ≤
    centeredPreferenceGamePayoff contextLaw preference policy alternative

/-- A finite preference-game equilibrium is exactly a maximal lottery. -/
theorem isPreferenceGameEquilibrium_iff_isMaximalLottery
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (preference : Learning.HumanFeedback.PairwisePreference Context Response)
    (policy : Learning.HumanFeedback.FinitePolicy Context Response) :
    IsPreferenceGameEquilibrium contextLaw preference policy ↔
      IsMaximalLottery contextLaw preference policy := by
  constructor
  · intro hequilibrium alternative
    unfold IsPreferenceGameEquilibrium at hequilibrium
    unfold centeredPreferenceGamePayoff
    have h := hequilibrium alternative
    linarith
  · intro hmaximal alternative
    unfold IsMaximalLottery at hmaximal
    have h := hmaximal alternative
    unfold centeredPreferenceGamePayoff at h
    linarith

/-- Approximate preference equilibria are exactly approximate maximal lotteries. -/
theorem isApproximatePreferenceGameEquilibrium_iff_isApproximateMaximalLottery
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (approximation : ℝ)
    (contextLaw : PMF Context) (preference : Learning.HumanFeedback.PairwisePreference Context Response)
    (policy : Learning.HumanFeedback.FinitePolicy Context Response) :
    IsApproximatePreferenceGameEquilibrium approximation contextLaw preference policy ↔
      IsApproximateMaximalLottery approximation contextLaw preference policy := by
  constructor
  · intro hequilibrium alternative
    unfold IsApproximatePreferenceGameEquilibrium at hequilibrium
    unfold centeredPreferenceGamePayoff
    have h := hequilibrium alternative
    linarith
  · intro hmaximal alternative
    unfold IsApproximateMaximalLottery at hmaximal
    unfold centeredPreferenceGamePayoff at hmaximal
    have h := hmaximal alternative
    linarith

/--
The regularized NLHF preference-game payoff.  The KL terms are written
explicitly so the antisymmetric constant-sum structure is visible.
-/
noncomputable def regularizedPreferenceGamePayoff
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (preference : Learning.HumanFeedback.PairwisePreference Context Response)
    (reference first second : Learning.HumanFeedback.FinitePolicy Context Response)
    (klRegularization : ℝ) : ℝ :=
  preferenceGamePayoff contextLaw preference first second -
    klRegularization *
      Learning.HumanFeedback.contextAveragedPolicyKLDivergence contextLaw first reference +
    klRegularization *
      Learning.HumanFeedback.contextAveragedPolicyKLDivergence contextLaw second reference

/-- Regularized preference-game payoffs remain constant sum. -/
theorem regularizedPreferenceGamePayoff_add_swap
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (preference : Learning.HumanFeedback.PairwisePreference Context Response)
    (reference first second : Learning.HumanFeedback.FinitePolicy Context Response)
    (klRegularization : ℝ) :
    regularizedPreferenceGamePayoff contextLaw preference reference first second klRegularization +
      regularizedPreferenceGamePayoff contextLaw preference reference second first klRegularization = 1 := by
  unfold regularizedPreferenceGamePayoff
  have hsum := preferenceGamePayoff_add_swap contextLaw preference first second
  linarith

/-- A policy that wins every regularized comparison is a regularized game equilibrium. -/
def IsRegularizedPreferenceGameEquilibrium
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (preference : Learning.HumanFeedback.PairwisePreference Context Response)
    (reference policy : Learning.HumanFeedback.FinitePolicy Context Response)
    (klRegularization : ℝ) : Prop :=
  ∀ alternative, 1 / 2 ≤
    regularizedPreferenceGamePayoff contextLaw preference reference policy alternative
      klRegularization

end PreferenceGame
end GameTheory
end AppliedModelingLib

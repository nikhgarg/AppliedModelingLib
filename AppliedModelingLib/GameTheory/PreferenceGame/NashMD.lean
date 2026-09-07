import AppliedModelingLib.GameTheory.PreferenceGame.Basic
import AppliedModelingLib.Learning.HumanFeedback.GeometricMixture

/-!
# Finite Nash mirror descent for preference games

This module isolates the algebraic update in NLHF: first geometrically mix
the current policy with a reference, then take the KL-regularized best response
to that mixed opponent.  It deliberately proves the one-step variational
maximization only; convergence rates need additional mirror-descent estimates.

## Main declarations

- `responsePreferenceScore`
- `nashMDRegularizedOpponent`
- `nashMDStep`
- `nashMDObjective`
- `nashMDObjective_le_at_step`
- `nashMDStep_kl_three_point`
-/

namespace AppliedModelingLib
namespace GameTheory
namespace PreferenceGame

open Learning.HumanFeedback

/-- Expected probability that one fixed response beats a response from `opponent`. -/
noncomputable def responsePreferenceScore
    {Context Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference Context Response)
    (opponent : FinitePolicy Context Response) : Context → Response → ℝ :=
  fun context response =>
    pmfExp (opponent context) (fun opponentResponse =>
      preference.prob context response opponentResponse)

/-- A response's expected pairwise-preference score is nonnegative. -/
theorem responsePreferenceScore_nonneg
    {Context Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference Context Response)
    (opponent : FinitePolicy Context Response) (context : Context) (response : Response) :
    0 ≤ responsePreferenceScore preference opponent context response := by
  unfold responsePreferenceScore
  exact pmfExp_nonneg_of_forall_nonneg (opponent context) _
    (fun opponentResponse => preference.nonneg context response opponentResponse)

/-- A response's expected pairwise-preference score is at most one. -/
theorem responsePreferenceScore_le_one
    {Context Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference Context Response)
    (opponent : FinitePolicy Context Response) (context : Context) (response : Response) :
    responsePreferenceScore preference opponent context response ≤ 1 := by
  unfold responsePreferenceScore
  exact pmfExp_le_of_forall_le (opponent context) _ 1
    (fun opponentResponse => preference.le_one context response opponentResponse)

/-- The response score used by a Nash-MD step lies in the unit interval. -/
theorem responsePreferenceScore_mem_Icc
    {Context Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference Context Response)
    (opponent : FinitePolicy Context Response) (context : Context) (response : Response) :
    responsePreferenceScore preference opponent context response ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨responsePreferenceScore_nonneg preference opponent context response,
    responsePreferenceScore_le_one preference opponent context response⟩

/-- Policy-level preference payoff is the expected response-level score. -/
theorem policyPreference_eq_policyExpectedScore
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (preference : PairwisePreference Context Response)
    (candidate opponent : FinitePolicy Context Response) :
    policyPreference contextLaw preference candidate opponent =
    policyExpectedScore contextLaw candidate
        (responsePreferenceScore preference opponent) := by
  rfl

/--
The regularized preference payoff, as a function of its first policy, is a
positive multiple of the generic entropy-regularized objective plus a term
independent of that policy.
-/
theorem regularizedPreferenceGamePayoff_eq_scaled_contextExponentialTiltObjective
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (preference : PairwisePreference Context Response)
    (reference candidate opponent : FinitePolicy Context Response)
    (klRegularization : ℝ) (hklRegularization : klRegularization ≠ 0) :
    regularizedPreferenceGamePayoff contextLaw preference reference candidate opponent
        klRegularization =
      klRegularization *
          contextExponentialTiltObjective contextLaw reference candidate
            (responsePreferenceScore preference opponent) klRegularization⁻¹ +
        klRegularization *
          contextAveragedPolicyKLDivergence contextLaw opponent reference := by
  unfold regularizedPreferenceGamePayoff preferenceGamePayoff
    contextExponentialTiltObjective contextAveragedPolicyKLDivergence exponentialTiltObjective
    pointwisePolicyKLDivergence
  rw [policyPreference_eq_policyExpectedScore]
  unfold policyExpectedScore
  rw [pmfExp_sub, pmfExp_const_mul]
  field_simp [hklRegularization]

/--
For positive regularization, a global maximizer of the regularized preference
payoff against a fixed opponent is the corresponding full-support exponential
best response.
-/
theorem regularizedPreferenceGamePayoff_globalMax_unique
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (preference : PairwisePreference Context Response)
    (reference candidate opponent : FinitePolicy Context Response)
    (klRegularization : ℝ) (hcontextLaw : PMFFullSupport contextLaw)
    (hreference : PolicyFullSupport reference) (hklRegularization : 0 < klRegularization)
    (hmax : ∀ other : FinitePolicy Context Response,
      regularizedPreferenceGamePayoff contextLaw preference reference other opponent
        klRegularization ≤
        regularizedPreferenceGamePayoff contextLaw preference reference candidate opponent
          klRegularization) :
    candidate = contextExponentialTiltPolicy reference
      (responsePreferenceScore preference opponent) klRegularization⁻¹ := by
  apply contextExponentialTiltObjective_globalMax_unique
    contextLaw reference candidate (responsePreferenceScore preference opponent)
      klRegularization⁻¹ hcontextLaw hreference
  intro other
  have hpayoff := hmax other
  rw [regularizedPreferenceGamePayoff_eq_scaled_contextExponentialTiltObjective
    contextLaw preference reference other opponent klRegularization hklRegularization.ne',
    regularizedPreferenceGamePayoff_eq_scaled_contextExponentialTiltObjective
      contextLaw preference reference candidate opponent klRegularization hklRegularization.ne'] at hpayoff
  apply (mul_le_mul_iff_of_pos_left hklRegularization).mp
  linarith

/--
A fixed point of the entropy-regularized response map is a global maximizer
against itself.  This is the bridge from a finite-simplex fixed-point theorem
to the regularized preference-game equilibrium predicate.
-/
theorem regularizedPreferenceGamePayoff_le_self_of_exponentialTilt_fixedPoint
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (preference : PairwisePreference Context Response)
    (reference policy alternative : FinitePolicy Context Response)
    (klRegularization : ℝ) (hreference : PolicyFullSupport reference)
    (hklRegularization : 0 < klRegularization)
    (hfixed : policy = contextExponentialTiltPolicy reference
      (responsePreferenceScore preference policy) klRegularization⁻¹) :
    regularizedPreferenceGamePayoff contextLaw preference reference alternative policy
        klRegularization ≤
      regularizedPreferenceGamePayoff contextLaw preference reference policy policy
        klRegularization := by
  have hobjective :
      contextExponentialTiltObjective contextLaw reference alternative
          (responsePreferenceScore preference policy) klRegularization⁻¹ ≤
        contextExponentialTiltObjective contextLaw reference policy
          (responsePreferenceScore preference policy) klRegularization⁻¹ := by
    calc
      contextExponentialTiltObjective contextLaw reference alternative
          (responsePreferenceScore preference policy) klRegularization⁻¹ ≤
        contextExponentialTiltObjective contextLaw reference
          (contextExponentialTiltPolicy reference
            (responsePreferenceScore preference policy) klRegularization⁻¹)
          (responsePreferenceScore preference policy) klRegularization⁻¹ :=
        contextExponentialTiltObjective_le_at_exponentialTilt contextLaw reference alternative
          (responsePreferenceScore preference policy) klRegularization⁻¹ hreference
      _ = contextExponentialTiltObjective contextLaw reference policy
          (responsePreferenceScore preference policy) klRegularization⁻¹ := by
        rw [← hfixed]
  rw [regularizedPreferenceGamePayoff_eq_scaled_contextExponentialTiltObjective
    contextLaw preference reference alternative policy klRegularization hklRegularization.ne',
    regularizedPreferenceGamePayoff_eq_scaled_contextExponentialTiltObjective
      contextLaw preference reference policy policy klRegularization hklRegularization.ne']
  gcongr

/-- The regularized preference payoff of a policy against itself is one half. -/
theorem regularizedPreferenceGamePayoff_self
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (preference : PairwisePreference Context Response)
    (reference policy : FinitePolicy Context Response) (klRegularization : ℝ) :
    regularizedPreferenceGamePayoff contextLaw preference reference policy policy
      klRegularization = 1 / 2 := by
  have hsum := regularizedPreferenceGamePayoff_add_swap
    contextLaw preference reference policy policy klRegularization
  linarith

/--
An entropy-regularized response-map fixed point is a regularized preference
game equilibrium.  Its construction is therefore reduced to a genuine
finite-simplex fixed-point result, not an equilibrium assumption.
-/
theorem regularizedPreferenceGameEquilibrium_of_exponentialTilt_fixedPoint
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (preference : PairwisePreference Context Response)
    (reference policy : FinitePolicy Context Response)
    (klRegularization : ℝ) (hreference : PolicyFullSupport reference)
    (hklRegularization : 0 < klRegularization)
    (hfixed : policy = contextExponentialTiltPolicy reference
      (responsePreferenceScore preference policy) klRegularization⁻¹) :
    IsRegularizedPreferenceGameEquilibrium contextLaw preference reference policy
      klRegularization := by
  intro alternative
  have hle := regularizedPreferenceGamePayoff_le_self_of_exponentialTilt_fixedPoint
    contextLaw preference reference policy alternative klRegularization hreference
      hklRegularization hfixed
  have hself := regularizedPreferenceGamePayoff_self
    contextLaw preference reference policy klRegularization
  have hswap := regularizedPreferenceGamePayoff_add_swap
    contextLaw preference reference policy alternative klRegularization
  linarith

/--
Uniqueness part of NLHF Proposition 1 in the finite contextual model.  A
full-support context law is necessary for literal policy equality at every
context; without it, policies can differ on zero-mass contexts.
-/
theorem regularizedPreferenceGameEquilibrium_unique
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (preference : PairwisePreference Context Response)
    (reference first second : FinitePolicy Context Response)
    (klRegularization : ℝ) (hcontextLaw : PMFFullSupport contextLaw)
    (hreference : PolicyFullSupport reference) (hklRegularization : 0 < klRegularization)
    (hfirst : IsRegularizedPreferenceGameEquilibrium
      contextLaw preference reference first klRegularization)
    (hsecond : IsRegularizedPreferenceGameEquilibrium
      contextLaw preference reference second klRegularization) :
    first = second := by
  have hself : regularizedPreferenceGamePayoff contextLaw preference reference second second
      klRegularization = 1 / 2 :=
    regularizedPreferenceGamePayoff_self contextLaw preference reference second klRegularization
  have hmax_first : ∀ other : FinitePolicy Context Response,
      regularizedPreferenceGamePayoff contextLaw preference reference other second
        klRegularization ≤
        regularizedPreferenceGamePayoff contextLaw preference reference first second
          klRegularization := by
    intro other
    have hsum := regularizedPreferenceGamePayoff_add_swap
      contextLaw preference reference other second klRegularization
    have hother := hsecond other
    have hfirst_second := hfirst second
    linarith
  have hmax_second : ∀ other : FinitePolicy Context Response,
      regularizedPreferenceGamePayoff contextLaw preference reference other second
        klRegularization ≤
        regularizedPreferenceGamePayoff contextLaw preference reference second second
          klRegularization := by
    intro other
    have hsum := regularizedPreferenceGamePayoff_add_swap
      contextLaw preference reference other second klRegularization
    have hother := hsecond other
    linarith
  have hfirst_tilt := regularizedPreferenceGamePayoff_globalMax_unique
    contextLaw preference reference first second klRegularization hcontextLaw hreference
      hklRegularization hmax_first
  have hsecond_tilt := regularizedPreferenceGamePayoff_globalMax_unique
    contextLaw preference reference second second klRegularization hcontextLaw hreference
      hklRegularization hmax_second
  calc
    first = contextExponentialTiltPolicy reference
        (responsePreferenceScore preference second) klRegularization⁻¹ := hfirst_tilt
    _ = second := hsecond_tilt.symm

/-- The geometric-reference opponent used before a Nash-MD best response. -/
noncomputable def nashMDRegularizedOpponent
    {Context Response : Type*} [Fintype Response] [DecidableEq Response]
    (current reference : FinitePolicy Context Response)
    (stepSize klRegularization : ℝ)
    (hcurrent : PolicyFullSupport current) (hreference : PolicyFullSupport reference) :
    FinitePolicy Context Response :=
  geometricMixturePolicy current reference (stepSize * klRegularization)
    hcurrent hreference

/-- The regularized opponent preserves full support. -/
theorem nashMDRegularizedOpponent_fullSupport
    {Context Response : Type*} [Fintype Response] [DecidableEq Response]
    (current reference : FinitePolicy Context Response)
    (stepSize klRegularization : ℝ)
    (hcurrent : PolicyFullSupport current) (hreference : PolicyFullSupport reference) :
    PolicyFullSupport
      (nashMDRegularizedOpponent current reference stepSize klRegularization
        hcurrent hreference) :=
  geometricMixturePolicy_fullSupport current reference (stepSize * klRegularization)
    hcurrent hreference

/-- KL-regularized one-step Nash mirror-descent update. -/
noncomputable def nashMDStep
    {Context Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference Context Response)
    (current reference : FinitePolicy Context Response)
    (stepSize klRegularization : ℝ)
    (hcurrent : PolicyFullSupport current) (hreference : PolicyFullSupport reference) :
    FinitePolicy Context Response :=
  let opponent := nashMDRegularizedOpponent current reference stepSize klRegularization
    hcurrent hreference
  contextExponentialTiltPolicy opponent (responsePreferenceScore preference opponent) stepSize

/-- A Nash-MD iterate has full support when both input policies do. -/
theorem nashMDStep_fullSupport
    {Context Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference Context Response)
    (current reference : FinitePolicy Context Response)
    (stepSize klRegularization : ℝ)
    (hcurrent : PolicyFullSupport current) (hreference : PolicyFullSupport reference) :
    PolicyFullSupport
      (nashMDStep preference current reference stepSize klRegularization hcurrent hreference) := by
  unfold nashMDStep
  exact contextExponentialTiltPolicy_fullSupport _ _ _
    (nashMDRegularizedOpponent_fullSupport current reference stepSize klRegularization
      hcurrent hreference)

/--
The online-mirror-descent comparison update in NLHF Eq. (8). It shares the
geometric KL reference of Nash-MD but evaluates preference against the current
policy rather than against that regularized reference.
-/
noncomputable def omdStep
    {Context Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference Context Response)
    (current reference : FinitePolicy Context Response)
    (stepSize klRegularization : ℝ)
    (hcurrent : PolicyFullSupport current) (hreference : PolicyFullSupport reference) :
    FinitePolicy Context Response :=
  let regularizedReference := nashMDRegularizedOpponent current reference stepSize klRegularization
    hcurrent hreference
  contextExponentialTiltPolicy regularizedReference
    (responsePreferenceScore preference current) stepSize

/-- An OMD Eq. (8) iterate has full support under the source support hypotheses. -/
theorem omdStep_fullSupport
    {Context Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference Context Response)
    (current reference : FinitePolicy Context Response)
    (stepSize klRegularization : ℝ)
    (hcurrent : PolicyFullSupport current) (hreference : PolicyFullSupport reference) :
    PolicyFullSupport (omdStep preference current reference stepSize klRegularization
      hcurrent hreference) := by
  unfold omdStep
  exact contextExponentialTiltPolicy_fullSupport _ _ _
    (nashMDRegularizedOpponent_fullSupport current reference stepSize klRegularization
      hcurrent hreference)

/-- The finite contextual Eq. (8) objective: preference against the current policy minus KL to its geometric reference. -/
noncomputable def omdObjective
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (preference : PairwisePreference Context Response)
    (regularizedReference candidate current : FinitePolicy Context Response)
    (stepSize : ℝ) : ℝ :=
  contextExponentialTiltObjective contextLaw regularizedReference candidate
    (responsePreferenceScore preference current) stepSize

/--
NLHF Eq. (8)'s `arg max` statement in the finite/tabular model: the explicit
OMD update attains at least the Eq. (8) objective value of every candidate.
-/
theorem omdObjective_le_at_step
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (preference : PairwisePreference Context Response)
    (current reference candidate : FinitePolicy Context Response)
    (stepSize klRegularization : ℝ)
    (hcurrent : PolicyFullSupport current) (hreference : PolicyFullSupport reference) :
    omdObjective contextLaw preference
        (nashMDRegularizedOpponent current reference stepSize klRegularization hcurrent hreference)
        candidate current stepSize ≤
      omdObjective contextLaw preference
        (nashMDRegularizedOpponent current reference stepSize klRegularization hcurrent hreference)
        (omdStep preference current reference stepSize klRegularization hcurrent hreference)
        current stepSize := by
  unfold omdObjective omdStep
  exact contextExponentialTiltObjective_le_at_exponentialTilt contextLaw
    (nashMDRegularizedOpponent current reference stepSize klRegularization hcurrent hreference)
    candidate (responsePreferenceScore preference current) stepSize
    (nashMDRegularizedOpponent_fullSupport current reference stepSize klRegularization
      hcurrent hreference)

/-- The source Eq. (7) gradient of `-P_τ(· ≻ current)` in the one-context finite model. -/
noncomputable def omdLinearizedLossGradient
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response)
    (current reference : PMF Response) (klRegularization : ℝ) : Response → ℝ :=
  fun response =>
    -responsePreferenceScore preference (fun _ => current) () response +
      klRegularization *
        (Real.log (current response).toReal - Real.log (reference response).toReal + 1)

/-- The literal finite objective minimized by NLHF Eq. (7). -/
noncomputable def omdLinearizedLossObjective
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response)
    (current reference candidate : PMF Response)
    (stepSize klRegularization : ℝ) : ℝ :=
  stepSize *
      (pmfExp candidate
          (omdLinearizedLossGradient preference current reference klRegularization) -
        pmfExp current
          (omdLinearizedLossGradient preference current reference klRegularization)) +
    finiteKLDivergence candidate current

/-- The literal one-context objective displayed in NLHF Eq. (8). -/
noncomputable def omdEquation8Objective
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response)
    (current reference candidate : PMF Response)
    (stepSize klRegularization : ℝ)
    (hcurrent : PMFFullSupport current) (hreference : PMFFullSupport reference) : ℝ :=
  stepSize * pmfExp candidate (responsePreferenceScore preference (fun _ => current) ()) -
    finiteKLDivergence candidate
      (geometricMixture current reference (stepSize * klRegularization) hcurrent hreference)

/-- The explicit finite PMF update selected by NLHF Eq. (8). -/
noncomputable def omdStepPMF
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response)
    (current reference : PMF Response)
    (stepSize klRegularization : ℝ)
    (hcurrent : PMFFullSupport current) (hreference : PMFFullSupport reference) : PMF Response :=
  exponentialTilt
    (geometricMixture current reference (stepSize * klRegularization) hcurrent hreference)
    (responsePreferenceScore preference (fun _ => current) ()) stepSize

/-- The full-support domain of the one-context Eq. (8) OMD update. -/
theorem omdStepPMF_fullSupport
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response)
    (current reference : PMF Response)
    (stepSize klRegularization : ℝ)
    (hcurrent : PMFFullSupport current) (hreference : PMFFullSupport reference) :
    PMFFullSupport (omdStepPMF preference current reference stepSize klRegularization
      hcurrent hreference) := by
  unfold omdStepPMF
  exact exponentialTilt_fullSupport _ _ _
    (geometricMixture_fullSupport current reference (stepSize * klRegularization)
      hcurrent hreference)

/-- The explicit update is exactly the finite `arg max` in NLHF Eq. (8). -/
theorem omdEquation8Objective_le_at_step
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response)
    (current reference candidate : PMF Response)
    (stepSize klRegularization : ℝ)
    (hcurrent : PMFFullSupport current) (hreference : PMFFullSupport reference) :
    omdEquation8Objective preference current reference candidate stepSize klRegularization
        hcurrent hreference ≤
      omdEquation8Objective preference current reference
        (omdStepPMF preference current reference stepSize klRegularization hcurrent hreference)
        stepSize klRegularization hcurrent hreference := by
  change exponentialTiltObjective
      (geometricMixture current reference (stepSize * klRegularization) hcurrent hreference)
      candidate (responsePreferenceScore preference (fun _ => current) ()) stepSize ≤
    exponentialTiltObjective
      (geometricMixture current reference (stepSize * klRegularization) hcurrent hreference)
      (exponentialTilt
        (geometricMixture current reference (stepSize * klRegularization) hcurrent hreference)
        (responsePreferenceScore preference (fun _ => current) ()) stepSize)
      (responsePreferenceScore preference (fun _ => current) ()) stepSize
  exact exponentialTiltObjective_le_at_exponentialTilt
    (geometricMixture current reference (stepSize * klRegularization) hcurrent hreference)
    candidate (responsePreferenceScore preference (fun _ => current) ()) stepSize
    (geometricMixture_fullSupport current reference (stepSize * klRegularization)
      hcurrent hreference)

/-- Subtracting two KL divergences gives the expected log ratio of their references. -/
theorem finiteKLDivergence_sub_eq_pmfExp_log_ratio
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (candidate current reference : PMF Response) :
    finiteKLDivergence candidate reference - finiteKLDivergence candidate current =
      pmfExp candidate fun response =>
        Real.log (current response).toReal - Real.log (reference response).toReal := by
  unfold finiteKLDivergence pmfExp
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro response _
  ring

/-- The Eq. (7) gradient has the expected score/KL-log-ratio form. -/
theorem pmfExp_omdLinearizedLossGradient
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response)
    (current reference candidate : PMF Response) (klRegularization : ℝ) :
    pmfExp candidate (omdLinearizedLossGradient preference current reference klRegularization) =
      -pmfExp candidate (responsePreferenceScore preference (fun _ => current) ()) +
        klRegularization *
          pmfExp candidate (fun response =>
            Real.log (current response).toReal - Real.log (reference response).toReal) +
          klRegularization := by
  unfold omdLinearizedLossGradient
  rw [show (fun response =>
      -responsePreferenceScore preference (fun _ => current) () response +
        klRegularization *
          (Real.log (current response).toReal - Real.log (reference response).toReal + 1)) =
      fun response =>
        -responsePreferenceScore preference (fun _ => current) () response +
          klRegularization *
            (Real.log (current response).toReal - Real.log (reference response).toReal) +
          klRegularization by
      funext response
      ring]
  rw [pmfExp_add, pmfExp_add, pmfExp_neg, pmfExp_const_mul, pmfExp_const]

/--
The literal Eq. (7) objective difference is the negative of the Eq. (8)
objective difference. This proves the paper's claimed rewrite without hiding
the `+1` term in the KL gradient.
-/
theorem omdLinearizedLossObjective_sub_self_eq_neg_equation8Objective_sub_self
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response)
    (current reference candidate : PMF Response)
    (stepSize klRegularization : ℝ)
    (hcurrent : PMFFullSupport current) (hreference : PMFFullSupport reference) :
    omdLinearizedLossObjective preference current reference candidate stepSize klRegularization -
        omdLinearizedLossObjective preference current reference current stepSize klRegularization =
      -(omdEquation8Objective preference current reference candidate stepSize klRegularization
          hcurrent hreference -
        omdEquation8Objective preference current reference current stepSize klRegularization
          hcurrent hreference) := by
  have hgradient_candidate := pmfExp_omdLinearizedLossGradient
    preference current reference candidate klRegularization
  have hgradient_current := pmfExp_omdLinearizedLossGradient
    preference current reference current klRegularization
  have hratio_candidate := finiteKLDivergence_sub_eq_pmfExp_log_ratio
    candidate current reference
  have hratio_current := finiteKLDivergence_sub_eq_pmfExp_log_ratio
    current current reference
  have hmixture_candidate := finiteKLDivergence_geometricMixture
    candidate current reference (stepSize * klRegularization) hcurrent hreference
  have hmixture_current := finiteKLDivergence_geometricMixture
    current current reference (stepSize * klRegularization) hcurrent hreference
  unfold omdLinearizedLossObjective omdEquation8Objective
  rw [hgradient_candidate, hgradient_current, ← hratio_candidate, ← hratio_current,
    hmixture_candidate, hmixture_current]
  ring

/-- The explicit Eq. (8) update also minimizes the literal linearized-loss objective of Eq. (7). -/
theorem omdLinearizedLossObjective_le_at_step
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response)
    (current reference candidate : PMF Response)
    (stepSize klRegularization : ℝ)
    (hcurrent : PMFFullSupport current) (hreference : PMFFullSupport reference) :
    omdLinearizedLossObjective preference current reference
        (omdStepPMF preference current reference stepSize klRegularization hcurrent hreference)
        stepSize klRegularization ≤
      omdLinearizedLossObjective preference current reference candidate stepSize klRegularization := by
  have hmax := omdEquation8Objective_le_at_step preference current reference candidate
    stepSize klRegularization hcurrent hreference
  have hcandidate := omdLinearizedLossObjective_sub_self_eq_neg_equation8Objective_sub_self
    preference current reference candidate stepSize klRegularization hcurrent hreference
  have hstep := omdLinearizedLossObjective_sub_self_eq_neg_equation8Objective_sub_self
    preference current reference
    (omdStepPMF preference current reference stepSize klRegularization hcurrent hreference)
    stepSize klRegularization hcurrent hreference
  linarith

/--
The source Eq. (5) log-mass form of the finite Nash-MD update.  The displayed
normalization is allowed to depend on context but not on the response.
-/
theorem nashMDStep_log_mass
    {Context Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference Context Response)
    (current reference : FinitePolicy Context Response)
    (stepSize klRegularization : ℝ)
    (hcurrent : PolicyFullSupport current) (hreference : PolicyFullSupport reference) :
    ∃ normalization : Context → ℝ, ∀ context response,
      Real.log
          (nashMDStep preference current reference stepSize klRegularization hcurrent hreference
            context response).toReal =
        (1 - stepSize * klRegularization) * Real.log (current context response).toReal +
          stepSize * klRegularization * Real.log (reference context response).toReal +
          stepSize *
            responsePreferenceScore preference
              (nashMDRegularizedOpponent current reference stepSize klRegularization
                hcurrent hreference) context response +
          normalization context := by
  refine ⟨fun context =>
    -Real.log
        (geometricMixturePartition (current context) (reference context)
          (stepSize * klRegularization)) -
      Real.log
        (Probability.finiteMGF
          (nashMDRegularizedOpponent current reference stepSize klRegularization
            hcurrent hreference context)
          (responsePreferenceScore preference
            (nashMDRegularizedOpponent current reference stepSize klRegularization
              hcurrent hreference) context)
          stepSize), ?_⟩
  intro context response
  have htilt :
      Real.log
          (nashMDStep preference current reference stepSize klRegularization hcurrent hreference
            context response).toReal -
        Real.log
          (nashMDRegularizedOpponent current reference stepSize klRegularization
            hcurrent hreference context response).toReal =
      stepSize *
          responsePreferenceScore preference
            (nashMDRegularizedOpponent current reference stepSize klRegularization
              hcurrent hreference) context response -
        Real.log
          (Probability.finiteMGF
            (nashMDRegularizedOpponent current reference stepSize klRegularization
              hcurrent hreference context)
            (responsePreferenceScore preference
              (nashMDRegularizedOpponent current reference stepSize klRegularization
                hcurrent hreference) context)
            stepSize) := by
    unfold nashMDStep contextExponentialTiltPolicy
    exact exponentialTilt_log_ratio
      (nashMDRegularizedOpponent current reference stepSize klRegularization
        hcurrent hreference context)
      (responsePreferenceScore preference
        (nashMDRegularizedOpponent current reference stepSize klRegularization
          hcurrent hreference) context)
      stepSize
      (nashMDRegularizedOpponent_fullSupport current reference stepSize klRegularization
        hcurrent hreference context)
      response
  have hmixture :
      Real.log
          (nashMDRegularizedOpponent current reference stepSize klRegularization
            hcurrent hreference context response).toReal =
        (1 - stepSize * klRegularization) * Real.log (current context response).toReal +
          stepSize * klRegularization * Real.log (reference context response).toReal -
            Real.log
              (geometricMixturePartition (current context) (reference context)
                (stepSize * klRegularization)) := by
    simpa [nashMDRegularizedOpponent] using
      (geometricMixturePolicy_log_mass current reference (stepSize * klRegularization)
        hcurrent hreference context response)
  rw [hmixture] at htilt
  linarith

/--
Exact one-context KL three-point identity for a Nash-MD exponential mirror
step.  This is the entropy specialization immediately before the bounded
mirror-descent estimate used in NLHF Appendix D; no stability or convergence
bound is asserted here.
-/
theorem nashMDStep_kl_three_point
    {Context Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference Context Response)
    (current reference target : FinitePolicy Context Response)
    (stepSize klRegularization : ℝ)
    (hcurrent : PolicyFullSupport current) (hreference : PolicyFullSupport reference)
    (context : Context) :
    finiteKLDivergence (target context)
      (nashMDStep preference current reference stepSize klRegularization hcurrent hreference
        context) =
      finiteKLDivergence (target context)
          (nashMDRegularizedOpponent current reference stepSize klRegularization
            hcurrent hreference context) +
        stepSize *
          (pmfExp
              (nashMDStep preference current reference stepSize klRegularization
                hcurrent hreference context)
              (responsePreferenceScore preference
                (nashMDRegularizedOpponent current reference stepSize klRegularization
                  hcurrent hreference) context) -
            pmfExp (target context)
              (responsePreferenceScore preference
                (nashMDRegularizedOpponent current reference stepSize klRegularization
                  hcurrent hreference) context)) -
          finiteKLDivergence
            (nashMDStep preference current reference stepSize klRegularization
              hcurrent hreference context)
            (nashMDRegularizedOpponent current reference stepSize klRegularization
              hcurrent hreference context) := by
  simpa [nashMDStep, contextExponentialTiltPolicy] using
    (finiteKLDivergence_exponentialTilt_three_point
      (nashMDRegularizedOpponent current reference stepSize klRegularization
        hcurrent hreference context)
      (target context)
      (responsePreferenceScore preference
        (nashMDRegularizedOpponent current reference stepSize klRegularization
          hcurrent hreference) context)
      stepSize
      (nashMDRegularizedOpponent_fullSupport current reference stepSize klRegularization
        hcurrent hreference context))

/--
The finite form of NLHF Appendix-D Eq. (11), conditional only on the local
finite Pinsker/entropy-stability inequality displayed as
`hentropyStability`. The pointwise `[0,1]` score condition is derived from the
pairwise-preference model, not added as an assumption.
-/
theorem nashMDStep_kl_mirror_bound_of_l1_stability
    {Context Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference Context Response)
    (current reference target : FinitePolicy Context Response)
    (stepSize klRegularization : ℝ)
    (hcurrent : PolicyFullSupport current) (hreference : PolicyFullSupport reference)
    (hstepSize : 0 ≤ stepSize) (context : Context)
    (hentropyStability :
      (1 / 2 : ℝ) *
          (FiniteDimensionalNorms.l1 (fun response =>
            (nashMDStep preference current reference stepSize klRegularization hcurrent hreference
              context response).toReal -
              (nashMDRegularizedOpponent current reference stepSize klRegularization
                hcurrent hreference context response).toReal)) ^ 2 ≤
        finiteKLDivergence
          (nashMDStep preference current reference stepSize klRegularization hcurrent hreference
            context)
          (nashMDRegularizedOpponent current reference stepSize klRegularization
            hcurrent hreference context)) :
    finiteKLDivergence (target context)
      (nashMDStep preference current reference stepSize klRegularization hcurrent hreference
        context) ≤
      finiteKLDivergence (target context)
          (nashMDRegularizedOpponent current reference stepSize klRegularization
            hcurrent hreference context) +
        stepSize *
          (pmfExp
              (nashMDRegularizedOpponent current reference stepSize klRegularization
                hcurrent hreference context)
              (responsePreferenceScore preference
                (nashMDRegularizedOpponent current reference stepSize klRegularization
                  hcurrent hreference) context) -
            pmfExp (target context)
              (responsePreferenceScore preference
                (nashMDRegularizedOpponent current reference stepSize klRegularization
                  hcurrent hreference) context)) +
          2 * stepSize ^ 2 := by
  simpa [nashMDStep, contextExponentialTiltPolicy] using
    (finiteKLDivergence_exponentialTilt_mirror_bound_of_l1_stability
      (nashMDRegularizedOpponent current reference stepSize klRegularization
        hcurrent hreference context)
      (target context)
      (responsePreferenceScore preference
        (nashMDRegularizedOpponent current reference stepSize klRegularization
          hcurrent hreference) context)
      stepSize
      (nashMDRegularizedOpponent_fullSupport current reference stepSize klRegularization
        hcurrent hreference context)
      hstepSize
      (fun response => responsePreferenceScore_nonneg preference
        (nashMDRegularizedOpponent current reference stepSize klRegularization
          hcurrent hreference) context response)
      (fun response => responsePreferenceScore_le_one preference
        (nashMDRegularizedOpponent current reference stepSize klRegularization
          hcurrent hreference) context response)
      hentropyStability)

/--
Unconditional finite form of NLHF Appendix-D Eq. (11).  The local entropy
strong-convexity premise is supplied by the reusable finite Pinsker theorem.
-/
theorem nashMDStep_kl_mirror_bound
    {Context Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference Context Response)
    (current reference target : FinitePolicy Context Response)
    (stepSize klRegularization : ℝ)
    (hcurrent : PolicyFullSupport current) (hreference : PolicyFullSupport reference)
    (hstepSize : 0 ≤ stepSize) (context : Context) :
    finiteKLDivergence (target context)
      (nashMDStep preference current reference stepSize klRegularization hcurrent hreference
        context) ≤
      finiteKLDivergence (target context)
          (nashMDRegularizedOpponent current reference stepSize klRegularization
            hcurrent hreference context) +
        stepSize *
          (pmfExp
              (nashMDRegularizedOpponent current reference stepSize klRegularization
                hcurrent hreference context)
              (responsePreferenceScore preference
                (nashMDRegularizedOpponent current reference stepSize klRegularization
                  hcurrent hreference) context) -
            pmfExp (target context)
              (responsePreferenceScore preference
                (nashMDRegularizedOpponent current reference stepSize klRegularization
                  hcurrent hreference) context)) +
          2 * stepSize ^ 2 := by
  simpa [nashMDStep, contextExponentialTiltPolicy] using
    (finiteKLDivergence_exponentialTilt_mirror_bound
      (nashMDRegularizedOpponent current reference stepSize klRegularization
        hcurrent hreference context)
      (target context)
      (responsePreferenceScore preference
        (nashMDRegularizedOpponent current reference stepSize klRegularization
          hcurrent hreference) context)
      stepSize
      (nashMDRegularizedOpponent_fullSupport current reference stepSize klRegularization
        hcurrent hreference context)
      hstepSize
      (fun response => responsePreferenceScore_nonneg preference
        (nashMDRegularizedOpponent current reference stepSize klRegularization
          hcurrent hreference) context response)
      (fun response => responsePreferenceScore_le_one preference
        (nashMDRegularizedOpponent current reference stepSize klRegularization
          hcurrent hreference) context response))

/--
Context-averaged form of the finite mirror-step estimate used in NLHF Appendix
D.  The only analytic premise is the pointwise finite entropy-stability
inequality; all averaging and preference-payoff bookkeeping are discharged
here.  A finite Pinsker bridge can therefore close this premise without
repeating the Appendix-D algebra.
-/
theorem nashMDStep_contextAveragedKL_mirror_bound_of_l1_stability
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (preference : PairwisePreference Context Response)
    (current reference target : FinitePolicy Context Response)
    (stepSize klRegularization : ℝ)
    (hcurrent : PolicyFullSupport current) (hreference : PolicyFullSupport reference)
    (hstepSize : 0 ≤ stepSize)
    (hentropyStability : ∀ context,
      (1 / 2 : ℝ) *
          (FiniteDimensionalNorms.l1 (fun response =>
            (nashMDStep preference current reference stepSize klRegularization hcurrent hreference
              context response).toReal -
              (nashMDRegularizedOpponent current reference stepSize klRegularization
                hcurrent hreference context response).toReal)) ^ 2 ≤
        finiteKLDivergence
          (nashMDStep preference current reference stepSize klRegularization hcurrent hreference
            context)
          (nashMDRegularizedOpponent current reference stepSize klRegularization
            hcurrent hreference context)) :
    contextAveragedPolicyKLDivergence contextLaw target
      (nashMDStep preference current reference stepSize klRegularization hcurrent hreference) ≤
      contextAveragedPolicyKLDivergence contextLaw target
          (nashMDRegularizedOpponent current reference stepSize klRegularization hcurrent hreference) +
        stepSize *
          (preferenceGamePayoff contextLaw preference
              (nashMDRegularizedOpponent current reference stepSize klRegularization
                hcurrent hreference)
              (nashMDRegularizedOpponent current reference stepSize klRegularization
                hcurrent hreference) -
            preferenceGamePayoff contextLaw preference target
              (nashMDRegularizedOpponent current reference stepSize klRegularization
                hcurrent hreference)) +
          2 * stepSize ^ 2 := by
  have hpointwise : ∀ context,
      finiteKLDivergence (target context)
          (nashMDStep preference current reference stepSize klRegularization hcurrent hreference
            context) ≤
        finiteKLDivergence (target context)
            (nashMDRegularizedOpponent current reference stepSize klRegularization
              hcurrent hreference context) +
          stepSize *
            (pmfExp
                (nashMDRegularizedOpponent current reference stepSize klRegularization
                  hcurrent hreference context)
                (responsePreferenceScore preference
                  (nashMDRegularizedOpponent current reference stepSize klRegularization
                    hcurrent hreference) context) -
              pmfExp (target context)
                (responsePreferenceScore preference
                  (nashMDRegularizedOpponent current reference stepSize klRegularization
                    hcurrent hreference) context)) +
            2 * stepSize ^ 2 := by
    intro context
    exact nashMDStep_kl_mirror_bound_of_l1_stability preference current reference target
      stepSize klRegularization hcurrent hreference hstepSize context
      (hentropyStability context)
  unfold contextAveragedPolicyKLDivergence preferenceGamePayoff policyPreference
  calc
    pmfExp contextLaw (fun context => finiteKLDivergence (target context)
        (nashMDStep preference current reference stepSize klRegularization hcurrent hreference
          context)) ≤
        pmfExp contextLaw (fun context =>
          finiteKLDivergence (target context)
              (nashMDRegularizedOpponent current reference stepSize klRegularization
                hcurrent hreference context) +
            stepSize *
              (pmfExp
                  (nashMDRegularizedOpponent current reference stepSize klRegularization
                    hcurrent hreference context)
                  (responsePreferenceScore preference
                    (nashMDRegularizedOpponent current reference stepSize klRegularization
                      hcurrent hreference) context) -
                pmfExp (target context)
                  (responsePreferenceScore preference
                    (nashMDRegularizedOpponent current reference stepSize klRegularization
                      hcurrent hreference) context)) +
              2 * stepSize ^ 2) :=
        pmfExp_le_pmfExp_of_forall_le contextLaw _ _ hpointwise
    _ = pmfExp contextLaw (fun context => finiteKLDivergence (target context)
          (nashMDRegularizedOpponent current reference stepSize klRegularization
            hcurrent hreference context)) +
        stepSize *
          (pmfExp contextLaw (fun context =>
              pmfExp
                (nashMDRegularizedOpponent current reference stepSize klRegularization
                  hcurrent hreference context)
                (responsePreferenceScore preference
                  (nashMDRegularizedOpponent current reference stepSize klRegularization
                    hcurrent hreference) context)) -
            pmfExp contextLaw (fun context =>
              pmfExp (target context)
                (responsePreferenceScore preference
                  (nashMDRegularizedOpponent current reference stepSize klRegularization
                    hcurrent hreference) context)) ) +
          2 * stepSize ^ 2 := by
        rw [pmfExp_add, pmfExp_add, pmfExp_const_mul, pmfExp_sub, pmfExp_const]

/--
Context-averaged finite form of NLHF Appendix-D Eq. (11), with the local
Pinsker inequality discharged for every response simplex.
-/
theorem nashMDStep_contextAveragedKL_mirror_bound
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (preference : PairwisePreference Context Response)
    (current reference target : FinitePolicy Context Response)
    (stepSize klRegularization : ℝ)
    (hcurrent : PolicyFullSupport current) (hreference : PolicyFullSupport reference)
    (hstepSize : 0 ≤ stepSize) :
    contextAveragedPolicyKLDivergence contextLaw target
      (nashMDStep preference current reference stepSize klRegularization hcurrent hreference) ≤
      contextAveragedPolicyKLDivergence contextLaw target
          (nashMDRegularizedOpponent current reference stepSize klRegularization hcurrent hreference) +
        stepSize *
          (preferenceGamePayoff contextLaw preference
              (nashMDRegularizedOpponent current reference stepSize klRegularization
                hcurrent hreference)
              (nashMDRegularizedOpponent current reference stepSize klRegularization
                hcurrent hreference) -
            preferenceGamePayoff contextLaw preference target
              (nashMDRegularizedOpponent current reference stepSize klRegularization
                hcurrent hreference)) +
          2 * stepSize ^ 2 := by
  apply nashMDStep_contextAveragedKL_mirror_bound_of_l1_stability
    contextLaw preference current reference target stepSize klRegularization
      hcurrent hreference hstepSize
  intro context
  exact finitePinsker_l1_sq_le_finiteKLDivergence
    (nashMDStep preference current reference stepSize klRegularization hcurrent hreference
      context)
    (nashMDRegularizedOpponent current reference stepSize klRegularization
      hcurrent hreference context)
    (nashMDRegularizedOpponent_fullSupport current reference stepSize klRegularization
      hcurrent hreference context)

/--
Context-averaged finite form of NLHF Appendix-D Lemma 1.  It is the direct
policy lift of the reusable pointwise geometric-mixture KL inequality.
-/
theorem contextAveragedPolicyKLDivergence_geometricMixture_le
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context)
    (target current reference : FinitePolicy Context Response) (mixWeight : ℝ)
    (hcurrent : PolicyFullSupport current) (hreference : PolicyFullSupport reference)
    (hmixWeight_nonneg : 0 ≤ mixWeight) (hmixWeight_one : mixWeight ≤ 1) :
    contextAveragedPolicyKLDivergence contextLaw target
        (geometricMixturePolicy current reference mixWeight hcurrent hreference) ≤
      mixWeight * contextAveragedPolicyKLDivergence contextLaw target reference +
        (1 - mixWeight) * contextAveragedPolicyKLDivergence contextLaw target current -
          mixWeight * contextAveragedPolicyKLDivergence contextLaw
            (geometricMixturePolicy current reference mixWeight hcurrent hreference) reference := by
  have hpointwise : ∀ context,
      finiteKLDivergence (target context)
          (geometricMixturePolicy current reference mixWeight hcurrent hreference context) ≤
        mixWeight * finiteKLDivergence (target context) (reference context) +
          (1 - mixWeight) * finiteKLDivergence (target context) (current context) -
            mixWeight * finiteKLDivergence
              (geometricMixturePolicy current reference mixWeight hcurrent hreference context)
              (reference context) := by
    intro context
    exact finiteKLDivergence_geometricMixture_le (target context) (current context)
      (reference context) mixWeight (hcurrent context) (hreference context)
      hmixWeight_nonneg hmixWeight_one
  unfold contextAveragedPolicyKLDivergence
  calc
    pmfExp contextLaw (fun context => finiteKLDivergence (target context)
        (geometricMixturePolicy current reference mixWeight hcurrent hreference context)) ≤
        pmfExp contextLaw (fun context =>
          mixWeight * finiteKLDivergence (target context) (reference context) +
            (1 - mixWeight) * finiteKLDivergence (target context) (current context) -
              mixWeight * finiteKLDivergence
                (geometricMixturePolicy current reference mixWeight hcurrent hreference context)
                (reference context)) :=
      pmfExp_le_pmfExp_of_forall_le contextLaw _ _ hpointwise
    _ = mixWeight * pmfExp contextLaw (fun context =>
          finiteKLDivergence (target context) (reference context)) +
        (1 - mixWeight) * pmfExp contextLaw (fun context =>
          finiteKLDivergence (target context) (current context)) -
          mixWeight * pmfExp contextLaw (fun context => finiteKLDivergence
            (geometricMixturePolicy current reference mixWeight hcurrent hreference context)
            (reference context)) := by
        rw [pmfExp_sub, pmfExp_add, pmfExp_const_mul, pmfExp_const_mul,
          pmfExp_const_mul]

/--
The finite policy-level contraction algebra of NLHF Theorem 1.  This combines
the Appendix-D mirror bound, Appendix-D Lemma 1, and the regularized-equilibrium
inequality.  Its sole remaining analytic input is the pointwise finite
entropy-stability/Pinsker inequality used by the source to establish Eq. (11).
-/
theorem nashMDStep_contextAveragedKL_contraction_of_l1_stability
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (preference : PairwisePreference Context Response)
    (current reference target : FinitePolicy Context Response)
    (stepSize klRegularization : ℝ)
    (hcurrent : PolicyFullSupport current) (hreference : PolicyFullSupport reference)
    (hstepSize : 0 ≤ stepSize)
    (hmixWeight_nonneg : 0 ≤ stepSize * klRegularization)
    (hmixWeight_one : stepSize * klRegularization ≤ 1)
    (hequilibrium : IsRegularizedPreferenceGameEquilibrium
      contextLaw preference reference target klRegularization)
    (hentropyStability : ∀ context,
      (1 / 2 : ℝ) *
          (FiniteDimensionalNorms.l1 (fun response =>
            (nashMDStep preference current reference stepSize klRegularization hcurrent hreference
              context response).toReal -
              (nashMDRegularizedOpponent current reference stepSize klRegularization
                hcurrent hreference context response).toReal)) ^ 2 ≤
        finiteKLDivergence
          (nashMDStep preference current reference stepSize klRegularization hcurrent hreference
            context)
          (nashMDRegularizedOpponent current reference stepSize klRegularization
            hcurrent hreference context)) :
    contextAveragedPolicyKLDivergence contextLaw target
      (nashMDStep preference current reference stepSize klRegularization hcurrent hreference) ≤
      (1 - stepSize * klRegularization) *
          contextAveragedPolicyKLDivergence contextLaw target current +
        2 * stepSize ^ 2 := by
  let opponent := nashMDRegularizedOpponent current reference stepSize klRegularization
    hcurrent hreference
  have hmirror :
      contextAveragedPolicyKLDivergence contextLaw target
          (nashMDStep preference current reference stepSize klRegularization hcurrent hreference) ≤
        contextAveragedPolicyKLDivergence contextLaw target opponent +
          stepSize *
            (preferenceGamePayoff contextLaw preference opponent opponent -
              preferenceGamePayoff contextLaw preference target opponent) +
            2 * stepSize ^ 2 := by
    simpa [opponent] using
      nashMDStep_contextAveragedKL_mirror_bound_of_l1_stability contextLaw preference
        current reference target stepSize klRegularization hcurrent hreference hstepSize
        hentropyStability
  have hmixture :
      contextAveragedPolicyKLDivergence contextLaw target opponent ≤
        (stepSize * klRegularization) *
            contextAveragedPolicyKLDivergence contextLaw target reference +
          (1 - stepSize * klRegularization) *
            contextAveragedPolicyKLDivergence contextLaw target current -
            (stepSize * klRegularization) *
              contextAveragedPolicyKLDivergence contextLaw opponent reference := by
    simpa [opponent, nashMDRegularizedOpponent] using
      contextAveragedPolicyKLDivergence_geometricMixture_le contextLaw target current reference
        (stepSize * klRegularization) hcurrent hreference hmixWeight_nonneg hmixWeight_one
  have hself : preferenceGamePayoff contextLaw preference opponent opponent = 1 / 2 := by
    have hsum := preferenceGamePayoff_add_swap contextLaw preference opponent opponent
    linarith
  have hequilibriumAtOpponent := hequilibrium opponent
  unfold IsRegularizedPreferenceGameEquilibrium regularizedPreferenceGamePayoff at hequilibriumAtOpponent
  have hbracket :
      1 / 2 - preferenceGamePayoff contextLaw preference target opponent +
          klRegularization * contextAveragedPolicyKLDivergence contextLaw target reference -
          klRegularization * contextAveragedPolicyKLDivergence contextLaw opponent reference ≤ 0 := by
    linarith
  have hscaledBracket :
      stepSize *
          (1 / 2 - preferenceGamePayoff contextLaw preference target opponent +
            klRegularization * contextAveragedPolicyKLDivergence contextLaw target reference -
            klRegularization * contextAveragedPolicyKLDivergence contextLaw opponent reference) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hstepSize hbracket
  calc
    contextAveragedPolicyKLDivergence contextLaw target
        (nashMDStep preference current reference stepSize klRegularization hcurrent hreference) ≤
        contextAveragedPolicyKLDivergence contextLaw target opponent +
          stepSize *
            (preferenceGamePayoff contextLaw preference opponent opponent -
              preferenceGamePayoff contextLaw preference target opponent) +
            2 * stepSize ^ 2 := hmirror
    _ ≤ ((stepSize * klRegularization) *
            contextAveragedPolicyKLDivergence contextLaw target reference +
          (1 - stepSize * klRegularization) *
            contextAveragedPolicyKLDivergence contextLaw target current -
            (stepSize * klRegularization) *
              contextAveragedPolicyKLDivergence contextLaw opponent reference) +
          stepSize *
            (preferenceGamePayoff contextLaw preference opponent opponent -
              preferenceGamePayoff contextLaw preference target opponent) +
            2 * stepSize ^ 2 := by
        gcongr
    _ ≤ (1 - stepSize * klRegularization) *
          contextAveragedPolicyKLDivergence contextLaw target current +
        2 * stepSize ^ 2 := by
        rw [hself]
        nlinarith

/--
Finite policy-level form of NLHF Theorem 1's one-step contraction.  Appendix-D
Lemma 2 is discharged through finite Pinsker; the source's regularized
equilibrium is an explicit input because its existence and uniqueness belong
to the separate finite minimax argument.
-/
theorem nashMDStep_contextAveragedKL_contraction
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (preference : PairwisePreference Context Response)
    (current reference target : FinitePolicy Context Response)
    (stepSize klRegularization : ℝ)
    (hcurrent : PolicyFullSupport current) (hreference : PolicyFullSupport reference)
    (hstepSize : 0 ≤ stepSize)
    (hmixWeight_nonneg : 0 ≤ stepSize * klRegularization)
    (hmixWeight_one : stepSize * klRegularization ≤ 1)
    (hequilibrium : IsRegularizedPreferenceGameEquilibrium
      contextLaw preference reference target klRegularization) :
    contextAveragedPolicyKLDivergence contextLaw target
      (nashMDStep preference current reference stepSize klRegularization hcurrent hreference) ≤
      (1 - stepSize * klRegularization) *
          contextAveragedPolicyKLDivergence contextLaw target current +
        2 * stepSize ^ 2 := by
  apply nashMDStep_contextAveragedKL_contraction_of_l1_stability
    contextLaw preference current reference target stepSize klRegularization hcurrent hreference
      hstepSize hmixWeight_nonneg hmixWeight_one hequilibrium
  intro context
  exact finitePinsker_l1_sq_le_finiteKLDivergence
    (nashMDStep preference current reference stepSize klRegularization hcurrent hreference
      context)
    (nashMDRegularizedOpponent current reference stepSize klRegularization
      hcurrent hreference context)
    (nashMDRegularizedOpponent_fullSupport current reference stepSize klRegularization
      hcurrent hreference context)

/--
The deterministic learning-rate induction following NLHF Theorem 1.  Once a
sequence satisfies the source one-step contraction at
`η_t = 2 / (τ (t + 2))`, the displayed `8 / (τ² (t + 1))` last-iterate bound
follows from this scalar recurrence alone.
-/
theorem nashMD_lastIterate_rate_of_contraction
    (klRegularization : ℝ) (hklRegularization : 0 < klRegularization)
    (distance : ℕ → ℝ)
    (hbase : distance 1 ≤ 2 / klRegularization ^ 2)
    (hcontraction : ∀ iteration : ℕ,
      distance (iteration + 1) ≤
        (1 - (2 / (klRegularization * ((iteration : ℝ) + 2))) * klRegularization) *
            distance iteration +
          2 * (2 / (klRegularization * ((iteration : ℝ) + 2))) ^ 2) :
    ∀ iteration : ℕ,
      distance (iteration + 1) ≤
        8 / (klRegularization ^ 2 * ((iteration : ℝ) + 2)) := by
  intro iteration
  induction iteration with
  | zero =>
      norm_num at hbase ⊢
      have hsquare : 0 < klRegularization ^ 2 := sq_pos_of_pos hklRegularization
      have hbaseBound :
          2 / klRegularization ^ 2 ≤ 8 / (klRegularization ^ 2 * 2) := by
        field_simp [ne_of_gt hsquare]
        nlinarith
      exact hbase.trans hbaseBound
  | succ iteration inductionHypothesis =>
      have hrecurrence := hcontraction (iteration + 1)
      have hnat : 0 ≤ (iteration : ℝ) := Nat.cast_nonneg iteration
      have hplusTwo : 0 < (iteration : ℝ) + 2 := by linarith
      have hplusThree : 0 < (iteration : ℝ) + 3 := by linarith
      have hregularizationSq : 0 < klRegularization ^ 2 :=
        sq_pos_of_pos hklRegularization
      have hregularizationPlusTwo :
          klRegularization * ((iteration : ℝ) + 2) ≠ 0 :=
        ne_of_gt (mul_pos hklRegularization hplusTwo)
      have hregularizationPlusThree :
          klRegularization * ((iteration : ℝ) + 3) ≠ 0 :=
        ne_of_gt (mul_pos hklRegularization hplusThree)
      have hcoefficient :
          0 ≤ 1 - (2 / (klRegularization * ((iteration : ℝ) + 3))) *
            klRegularization := by
        rw [show 1 - (2 / (klRegularization * ((iteration : ℝ) + 3))) *
            klRegularization = ((iteration : ℝ) + 1) / ((iteration : ℝ) + 3) by
              field_simp [hregularizationPlusThree]
              ring]
        positivity
      have hscalar :
          (1 - (2 / (klRegularization * ((iteration : ℝ) + 3))) *
              klRegularization) *
              (8 / (klRegularization ^ 2 * ((iteration : ℝ) + 2))) +
            2 * (2 / (klRegularization * ((iteration : ℝ) + 3))) ^ 2 ≤
              8 / (klRegularization ^ 2 * ((iteration : ℝ) + 3)) := by
        have hidentity :
            (1 - (2 / (klRegularization * ((iteration : ℝ) + 3))) *
                klRegularization) *
                (8 / (klRegularization ^ 2 * ((iteration : ℝ) + 2))) +
              2 * (2 / (klRegularization * ((iteration : ℝ) + 3))) ^ 2 +
                8 / (klRegularization ^ 2 * ((iteration : ℝ) + 3) ^ 2 *
                  ((iteration : ℝ) + 2)) =
                8 / (klRegularization ^ 2 * ((iteration : ℝ) + 3)) := by
          field_simp [hregularizationPlusTwo, hregularizationPlusThree,
            ne_of_gt hregularizationSq, ne_of_gt hplusTwo, ne_of_gt hplusThree]
          ring
        rw [← hidentity]
        exact le_add_of_nonneg_right (by positivity)
      calc
        distance (Nat.succ iteration + 1) = distance ((iteration + 1) + 1) := by
          simp [Nat.succ_eq_add_one]
        _ ≤ (1 - (2 / (klRegularization * ((iteration : ℝ) + 3))) *
              klRegularization) * distance (iteration + 1) +
            2 * (2 / (klRegularization * ((iteration : ℝ) + 3))) ^ 2 := by
          convert hrecurrence using 1
          all_goals norm_num [Nat.cast_add, Nat.cast_one]
          all_goals ring
        _ ≤ (1 - (2 / (klRegularization * ((iteration : ℝ) + 3))) *
              klRegularization) *
              (8 / (klRegularization ^ 2 * ((iteration : ℝ) + 2))) +
            2 * (2 / (klRegularization * ((iteration : ℝ) + 3))) ^ 2 := by
          gcongr
        _ ≤ 8 / (klRegularization ^ 2 * ((Nat.succ iteration : ℝ) + 2)) := by
          convert hscalar using 1
          all_goals norm_num [Nat.cast_succ]
          all_goals ring

/--
Finite-tabular last-iterate form of NLHF Theorem 1.  A trajectory is required
to follow the source Nash-MD update at `η_t = 2 / (τ (t + 2))`; finite Pinsker
discharges Appendix-D Lemma 2, while the regularized equilibrium remains an
explicit source-model input.
-/
theorem nashMD_lastIterate_rate
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (preference : PairwisePreference Context Response)
    (reference target : FinitePolicy Context Response)
    (klRegularization : ℝ) (hklRegularization : 0 < klRegularization)
    (trajectory : ℕ → FinitePolicy Context Response)
    (htrajectory : ∀ iteration, PolicyFullSupport (trajectory iteration))
    (hreference : PolicyFullSupport reference)
    (hequilibrium : IsRegularizedPreferenceGameEquilibrium
      contextLaw preference reference target klRegularization)
    (hupdate : ∀ iteration,
      trajectory (iteration + 1) =
        nashMDStep preference (trajectory iteration) reference
          (2 / (klRegularization * ((iteration : ℝ) + 2))) klRegularization
          (htrajectory iteration) hreference) :
    ∀ iteration,
      contextAveragedPolicyKLDivergence contextLaw target (trajectory (iteration + 1)) ≤
        8 / (klRegularization ^ 2 * ((iteration : ℝ) + 2)) := by
  let distance : ℕ → ℝ := fun iteration =>
    contextAveragedPolicyKLDivergence contextLaw target (trajectory iteration)
  have hbase : distance 1 ≤ 2 / klRegularization ^ 2 := by
    have hupdateZero := hupdate 0
    norm_num at hupdateZero
    change contextAveragedPolicyKLDivergence contextLaw target (trajectory 1) ≤
      2 / klRegularization ^ 2
    rw [hupdateZero]
    have hstepZero : 0 ≤ 2 / (klRegularization * 2) := by positivity
    have hweightZero_nonneg :
        0 ≤ (2 / (klRegularization * 2)) * klRegularization := by
      positivity
    have hweightZero_one :
        (2 / (klRegularization * 2)) * klRegularization ≤ 1 := by
      field_simp [hklRegularization.ne']
      norm_num
    have hcontraction := nashMDStep_contextAveragedKL_contraction
      contextLaw preference (trajectory 0) reference target
      (2 / (klRegularization * 2)) klRegularization
      (htrajectory 0) hreference hstepZero hweightZero_nonneg hweightZero_one hequilibrium
    change contextAveragedPolicyKLDivergence contextLaw target
      (nashMDStep preference (trajectory 0) reference
        (2 / (klRegularization * 2)) klRegularization
        (htrajectory 0) hreference) ≤ 2 / klRegularization ^ 2
    have hstepValue :
        2 / (klRegularization * 2) = 1 / klRegularization := by
      field_simp [hklRegularization.ne']
    rw [hstepValue] at hcontraction
    convert hcontraction using 1
    all_goals field_simp [hklRegularization.ne']
    all_goals ring
  have hcontraction : ∀ iteration : ℕ,
      distance (iteration + 1) ≤
        (1 - (2 / (klRegularization * ((iteration : ℝ) + 2))) * klRegularization) *
            distance iteration +
          2 * (2 / (klRegularization * ((iteration : ℝ) + 2))) ^ 2 := by
    intro iteration
    have hiteration_nonneg : 0 ≤ (iteration : ℝ) := Nat.cast_nonneg iteration
    have hiteration_plus_two : 0 < (iteration : ℝ) + 2 := by linarith
    have hstep_nonneg :
        0 ≤ 2 / (klRegularization * ((iteration : ℝ) + 2)) := by positivity
    have hweight :
        (2 / (klRegularization * ((iteration : ℝ) + 2))) * klRegularization =
          2 / ((iteration : ℝ) + 2) := by
      field_simp [hklRegularization.ne', hiteration_plus_two.ne']
    have hweight_nonneg :
        0 ≤ (2 / (klRegularization * ((iteration : ℝ) + 2))) * klRegularization := by
      rw [hweight]
      positivity
    have hweight_one :
        (2 / (klRegularization * ((iteration : ℝ) + 2))) * klRegularization ≤ 1 := by
      rw [hweight]
      exact (div_le_iff₀ hiteration_plus_two).mpr (by linarith)
    have hstep := nashMDStep_contextAveragedKL_contraction
      contextLaw preference (trajectory iteration) reference target
      (2 / (klRegularization * ((iteration : ℝ) + 2))) klRegularization
      (htrajectory iteration) hreference hstep_nonneg hweight_nonneg hweight_one hequilibrium
    change contextAveragedPolicyKLDivergence contextLaw target
        (trajectory (iteration + 1)) ≤ _
    rw [hupdate iteration]
    simpa [distance] using hstep
  simpa [distance] using
    (nashMD_lastIterate_rate_of_contraction klRegularization hklRegularization
      distance hbase hcontraction)

/-- The scaled expected win probability minus KL penalty optimized by the Nash-MD step. -/
noncomputable def nashMDObjective
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (preference : PairwisePreference Context Response)
    (opponent candidate : FinitePolicy Context Response) (stepSize : ℝ) : ℝ :=
  stepSize * policyPreference contextLaw preference candidate opponent -
    contextAveragedPolicyKLDivergence contextLaw candidate opponent

/-- The Nash-MD objective is the generic contextwise exponential-tilt objective. -/
theorem nashMDObjective_eq_contextExponentialTiltObjective
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (preference : PairwisePreference Context Response)
    (opponent candidate : FinitePolicy Context Response) (stepSize : ℝ) :
    nashMDObjective contextLaw preference opponent candidate stepSize =
      contextExponentialTiltObjective contextLaw opponent candidate
        (responsePreferenceScore preference opponent) stepSize := by
  unfold nashMDObjective contextExponentialTiltObjective
  rw [policyPreference_eq_policyExpectedScore]
  unfold contextAveragedPolicyKLDivergence policyExpectedScore
    exponentialTiltObjective responsePreferenceScore
  rw [pmfExp_sub, pmfExp_const_mul]
  rfl

/-- The Nash-MD step maximizes its one-step KL-regularized objective. -/
theorem nashMDObjective_le_at_step
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (preference : PairwisePreference Context Response)
    (current reference candidate : FinitePolicy Context Response)
    (stepSize klRegularization : ℝ)
    (hcurrent : PolicyFullSupport current) (hreference : PolicyFullSupport reference) :
    nashMDObjective contextLaw preference
        (nashMDRegularizedOpponent current reference stepSize klRegularization hcurrent hreference)
        candidate stepSize ≤
      nashMDObjective contextLaw preference
        (nashMDRegularizedOpponent current reference stepSize klRegularization hcurrent hreference)
        (nashMDStep preference current reference stepSize klRegularization hcurrent hreference)
        stepSize := by
  rw [nashMDObjective_eq_contextExponentialTiltObjective,
    nashMDObjective_eq_contextExponentialTiltObjective]
  unfold nashMDStep
  exact contextExponentialTiltObjective_le_at_exponentialTilt contextLaw
    (nashMDRegularizedOpponent current reference stepSize klRegularization hcurrent hreference)
    candidate
    (responsePreferenceScore preference
      (nashMDRegularizedOpponent current reference stepSize klRegularization hcurrent hreference))
    stepSize
    (nashMDRegularizedOpponent_fullSupport current reference stepSize klRegularization
      hcurrent hreference)

end PreferenceGame
end GameTheory
end AppliedModelingLib

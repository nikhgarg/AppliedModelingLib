import AppliedModelingLib.Foundations.Probability.FiniteSimplex
import AppliedModelingLib.Foundations.Math.FiniteSimplexFixedPoint
import AppliedModelingLib.GameTheory.PreferenceGame.NashMD

/-!
# Finite-simplex response maps for regularized preference games

The source model of NLHF has one prompt distributional state.  This module
expresses its entropic best-response map on Mathlib's real standard simplex,
which is the representation required by a finite Brouwer theorem.  A fixed
point is converted back to the existing PMF game model and proved to be a
regularized equilibrium.

## Main declarations

- `finiteRegularizedResponseMap`
- `finiteRegularizedResponseMap_fixedPoint_equilibrium`
-/

namespace AppliedModelingLib
namespace GameTheory
namespace PreferenceGame

open Learning.HumanFeedback

/--
The one-context entropic response map written on the real probability simplex.
Its fixed points are precisely the candidates needed for NLHF Proposition 1.
-/
noncomputable def finiteRegularizedResponseMap
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response) (reference : PMF Response)
    (klRegularization : ℝ) : stdSimplex ℝ Response → stdSimplex ℝ Response :=
  fun policyMass =>
    pmfToStdSimplex
      (exponentialTilt reference
        (responsePreferenceScore preference (fun _ => stdSimplexToPMF policyMass) ())
        klRegularization⁻¹)

/-- The response score against a real-simplex policy is its finite matrix product. -/
theorem responsePreferenceScore_stdSimplex
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response) (policyMass : stdSimplex ℝ Response)
    (response : Response) :
    responsePreferenceScore preference (fun _ => stdSimplexToPMF policyMass) () response =
      ∑ opponent : Response, policyMass.1 opponent * preference.prob () response opponent := by
  unfold responsePreferenceScore pmfExp
  simp only [stdSimplexToPMF_apply_toReal]

/-- The finite real-simplex entropic response map is continuous. -/
theorem finiteRegularizedResponseMap_continuous
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response) (reference : PMF Response)
    (klRegularization : ℝ) :
    Continuous (finiteRegularizedResponseMap preference reference klRegularization) := by
  let score : stdSimplex ℝ Response → Response → ℝ := fun policyMass response =>
    ∑ opponent : Response, policyMass.1 opponent * preference.prob () response opponent
  have hscore : ∀ response : Response, Continuous (fun policyMass => score policyMass response) := by
    intro response
    exact continuous_finset_sum Finset.univ fun opponent _ =>
      (continuous_apply opponent).comp continuous_subtype_val |>.mul continuous_const
  have hden : Continuous (fun policyMass =>
      ∑ response : Response,
        (reference response).toReal * Real.exp (klRegularization⁻¹ * score policyMass response)) :=
    continuous_finset_sum Finset.univ fun response _ =>
      continuous_const.mul (Real.continuous_exp.comp
        (continuous_const.mul (hscore response)))
  apply Continuous.subtype_mk
  apply continuous_pi
  intro response
  change Continuous fun policyMass =>
    (exponentialTilt reference
      (responsePreferenceScore preference (fun _ => stdSimplexToPMF policyMass) ())
      klRegularization⁻¹ response).toReal
  have hcoordinate : (fun policyMass : stdSimplex ℝ Response =>
      (exponentialTilt reference
        (responsePreferenceScore preference (fun _ => stdSimplexToPMF policyMass) ())
        klRegularization⁻¹ response).toReal) =
      fun policyMass =>
        (reference response).toReal *
            Real.exp (klRegularization⁻¹ * score policyMass response) /
          ∑ other : Response,
            (reference other).toReal *
              Real.exp (klRegularization⁻¹ * score policyMass other) := by
    funext policyMass
    rw [exponentialTilt_apply_toReal]
    simp_rw [Probability.finiteMGF, responsePreferenceScore_stdSimplex]
    rfl
  rw [hcoordinate]
  apply Continuous.div
  · exact continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul (hscore response)))
  · exact hden
  · intro policyMass
    exact (Probability.finiteMGF_pos reference (score policyMass) klRegularization⁻¹).ne'

/--
A fixed point of the real-simplex response map gives a regularized equilibrium
in the PMF formulation of the one-context preference game.
-/
theorem finiteRegularizedResponseMap_fixedPoint_equilibrium
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response) (reference : PMF Response)
    (klRegularization : ℝ) (hreference : PMFFullSupport reference)
    (hklRegularization : 0 < klRegularization)
    (policyMass : stdSimplex ℝ Response)
    (hfixed : finiteRegularizedResponseMap preference reference klRegularization policyMass =
      policyMass) :
    IsRegularizedPreferenceGameEquilibrium (PMF.pure ()) preference
      (fun _ => reference) (fun _ => stdSimplexToPMF policyMass) klRegularization := by
  apply regularizedPreferenceGameEquilibrium_of_exponentialTilt_fixedPoint
    (PMF.pure ()) preference (fun _ => reference) (fun _ => stdSimplexToPMF policyMass)
      klRegularization
  · intro context
    rcases context with ⟨⟩
    exact hreference
  · exact hklRegularization
  · apply finitePolicy_ext
    intro context
    rcases context with ⟨⟩
    change
      pmfToStdSimplex
          (exponentialTilt reference
            (responsePreferenceScore preference (fun _ => stdSimplexToPMF policyMass) ())
            klRegularization⁻¹) = policyMass at hfixed
    have hpmf := congrArg stdSimplexToPMF hfixed
    change stdSimplexToPMF policyMass =
      exponentialTilt reference
        (responsePreferenceScore preference (fun _ => stdSimplexToPMF policyMass) ())
        klRegularization⁻¹
    simpa only [stdSimplexToPMF_pmfToStdSimplex] using hpmf.symm

/--
The finite one-context regularized preference game has an equilibrium.  The
proof applies Brouwer to the continuous entropic response map and then uses
the fixed-point-to-equilibrium bridge above.
-/
theorem exists_regularizedPreferenceGameEquilibrium_finite
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response) (reference : PMF Response)
    (klRegularization : ℝ) (hreference : PMFFullSupport reference)
    (hklRegularization : 0 < klRegularization) :
    ∃ policy : FinitePolicy PUnit Response,
      IsRegularizedPreferenceGameEquilibrium (PMF.pure ()) preference
        (fun _ => reference) policy klRegularization := by
  classical
  letI : Nonempty Response :=
    ⟨(Probability.exists_pmf_toReal_pos reference).choose⟩
  obtain ⟨policyMass, hfixed⟩ :=
    exists_fixedPoint_finiteSimplex
      (finiteRegularizedResponseMap preference reference klRegularization)
      (finiteRegularizedResponseMap_continuous preference reference klRegularization)
  exact ⟨fun _ => stdSimplexToPMF policyMass,
    finiteRegularizedResponseMap_fixedPoint_equilibrium preference reference klRegularization
      hreference hklRegularization policyMass hfixed⟩

end PreferenceGame
end GameTheory
end AppliedModelingLib

import KR21Monoculture.Definition1FullW11
import KR21Monoculture.FiniteGaussianMixtureW11
import KR21Monoculture.LaplaceW11Regularity
import KR21Monoculture.ThreeCandidateValueProfile

/-!
# Literal source differentiability for KR21 Theorem 2

The published Theorem 2 calls its Gaussian and Laplacian RUMs ``noisy
permutation families''.  The final named-law endpoints prove every clause of
Definition 1 at their semantic ranking-law surfaces.  This module isolates
the one clause not already supplied there: differentiability of each ranking
atom in the literal iid scaled-noise source construction.

The Gaussian and Laplace constructions below are closed through the corrected
global `W^{1,1}` route.  The latter handles the Laplace kink by an a.e. weak
derivative, rather than claiming a classical derivative at zero.  Exact
source-to-named law transport is proved separately before these source
differentiability results are used in the final endpoints.
-/

open AppliedModelingLib Filter MeasureTheory
open AppliedModelingLib.SocialChoice.Ranking
open scoped ENNReal Topology

namespace KR21Monoculture

/-- Definition 1 exactly at the finite ranking-family level.  `center` is
the source's true ranking.  The `remaining.Nonempty` guard is necessary
because a partial ranking with no candidates left has no top candidate. -/
def SourceDefinition1NoisyPermutationFamily {n : ℕ}
    (F : AccuracyFamily n) (center : Ranking n) : Prop :=
  (∀ theta, 0 < theta → ∀ pi : Ranking n,
    ContinuousAt (fun theta' => ((F.dist theta') pi).toReal) theta ∧
      DifferentiableAt ℝ (fun theta' => ((F.dist theta') pi).toReal) theta) ∧
  Tendsto (fun theta => ((F.dist theta) center).toReal) atTop (nhds 1) ∧
  ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
    (∀ remaining : Finset (Candidate n), remaining.Nonempty →
      expectedBestInSet (F.dist thetaH) F.value remaining ≤
        expectedBestInSet (F.dist thetaA) F.value remaining) ∧
      expectedBestInSet (F.dist thetaH) F.value Finset.univ <
        expectedBestInSet (F.dist thetaA) F.value Finset.univ

/-- The one-component unit-scale Gaussian density, represented through the
finite-mixture infrastructure so its normalization and global `W^{1,1}`
facts are kernel checked rather than assumed. -/
noncomputable def theorem2GaussianBaseDensity : ℝ → ℝ :=
  finiteGaussianMixtureDensity (PMF.pure ()) (fun _ : Unit => 0) 1

/-- The ordinary derivative used for the one-component Gaussian density. -/
noncomputable def theorem2GaussianBaseDerivative : ℝ → ℝ :=
  finiteGaussianMixtureDerivative (PMF.pure ()) (fun _ : Unit => 0) 1

/-- Kernel-checked `W^{1,1}` regularity of the literal standard Gaussian
source noise. -/
theorem theorem2GaussianBase_w11Regularity :
    FiniteGaussianMixtureW11Regularity
      (PMF.pure ()) (fun _ : Unit => 0) 1 := by
  exact finiteGaussianMixture_w11Regularity
    (PMF.pure ()) (fun _ : Unit => 0) 1 (by norm_num)

/-- The literal Gaussian source RUM used for the Definition-1 audit: draw iid
standard Gaussian innovations and rank `x_i + epsilon_i / theta`. -/
noncomputable def theorem2GaussianScaledNoiseFamily
    (x1 x2 x3 : ℝ) : AccuracyFamily 1 :=
  w11CorrectedScaledNoiseFamily theorem2GaussianBaseDensity
    theorem2GaussianBase_w11Regularity.normalized
    (threeCandidateValueProfile x1 x2 x3)

/-- The source order `x₁ > x₂ > x₃` is exactly the adjacent true-order
condition used by the literal finite iid scaled-noise construction. -/
theorem theorem2GaussianScaledNoiseFamily_center_order
    {x1 x2 x3 : ℝ} (hx12 : x2 < x1) (hx23 : x3 < x2) :
    ∀ i : Fin (1 + 1),
      threeCandidateValueProfile x1 x2 x3
          (rum3Ranking012 i.succ) <
        threeCandidateValueProfile x1 x2 x3
          (rum3Ranking012 i.castSucc) := by
  intro i
  fin_cases i <;>
    simp [threeCandidateValueProfile, rum3Ranking012, hx12, hx23]

/-- Every literal iid Gaussian source-ranking atom is differentiable at
positive source accuracy under the corrected global-`W^{1,1}` route. -/
theorem theorem2GaussianScaledNoiseFamily_atom_differentiable
    {x1 x2 x3 : ℝ} (hx12 : x2 < x1) (hx23 : x3 < x2) :
    ∀ theta, 0 < theta → ∀ pi : Ranking 1,
      DifferentiableAt ℝ
        (fun theta' => ((theorem2GaussianScaledNoiseFamily x1 x2 x3).dist theta' pi).toReal)
        theta := by
  let regularity := theorem2GaussianBase_w11Regularity
  rcases correctedW11ScaledNoiseDefinition1_full_of_source
    theorem2GaussianBaseDensity theorem2GaussianBaseDerivative
    regularity.density_integrable regularity.derivative_integrable
    regularity.density_measurable regularity.density_positive
    regularity.absolute_continuity regularity.derivative_ae_eq
    regularity.normalized
    (threeCandidateValueProfile x1 x2 x3) rum3Ranking012
    (theorem2GaussianScaledNoiseFamily_center_order hx12 hx23) with
      ⟨_hcontinuous, hdifferentiable, _hconcentration, _hremoval, _hstrict⟩
  intro theta htheta pi
  simpa [theorem2GaussianScaledNoiseFamily] using hdifferentiable theta htheta pi

/-- The literal Laplace source RUM for Definition 1: draw iid centered
unit-variance Laplace innovations and rank `x_i + epsilon_i / theta`.  Its
source normalization remains in the density, while the later named-law bridge
proves the resulting score rate is `sqrt 2 * theta`. -/
noncomputable def sourceUnitVarianceLaplaceScaledNoiseFamily
    (x1 x2 x3 : ℝ) : AccuracyFamily 1 :=
  w11CorrectedScaledNoiseFamily sourceUnitVarianceLaplaceBaseDensity
    sourceUnitVarianceLaplace_w11Regularity.normalized
    (threeCandidateValueProfile x1 x2 x3)

/-- The literal Laplace source has the same displayed strict center order as
the Gaussian source family. -/
theorem sourceUnitVarianceLaplaceScaledNoiseFamily_center_order
    {x1 x2 x3 : ℝ} (hx12 : x2 < x1) (hx23 : x3 < x2) :
    ∀ i : Fin (1 + 1),
      threeCandidateValueProfile x1 x2 x3
          (rum3Ranking012 i.succ) <
        threeCandidateValueProfile x1 x2 x3
          (rum3Ranking012 i.castSucc) := by
  intro i
  fin_cases i <;>
    simp [threeCandidateValueProfile, rum3Ranking012, hx12, hx23]

/-- Every literal iid unit-variance Laplace source-ranking atom is
differentiable at positive accuracy under the corrected global-`W^{1,1}`
route.  The weak derivative handles the density kink at zero. -/
theorem sourceUnitVarianceLaplaceScaledNoiseFamily_atom_differentiable
    {x1 x2 x3 : ℝ} (hx12 : x2 < x1) (hx23 : x3 < x2) :
    ∀ theta, 0 < theta → ∀ pi : Ranking 1,
      DifferentiableAt ℝ
        (fun theta' =>
          ((sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3).dist theta' pi).toReal)
        theta := by
  let regularity := sourceUnitVarianceLaplace_w11Regularity
  rcases correctedW11ScaledNoiseDefinition1_full_of_source
    sourceUnitVarianceLaplaceBaseDensity sourceUnitVarianceLaplaceBaseWeakDerivative
    regularity.density_integrable regularity.derivative_integrable
    regularity.density_measurable regularity.density_positive
    regularity.absolute_continuity regularity.derivative_ae_eq
    regularity.normalized
    (threeCandidateValueProfile x1 x2 x3) rum3Ranking012
    (sourceUnitVarianceLaplaceScaledNoiseFamily_center_order hx12 hx23) with
      ⟨_hcontinuous, hdifferentiable, _hconcentration, _hremoval, _hstrict⟩
  intro theta htheta pi
  simpa [sourceUnitVarianceLaplaceScaledNoiseFamily] using
    hdifferentiable theta htheta pi

end KR21Monoculture

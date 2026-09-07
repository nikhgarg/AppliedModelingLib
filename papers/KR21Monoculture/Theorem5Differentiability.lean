import KR21Monoculture.RUM
import Mathlib.Analysis.Calculus.ParametricIntegral

open AppliedModelingLib MeasureTheory Filter
open scoped Topology

namespace KR21Monoculture

/-!
# Appendix A, Theorem 5: the missing differentiation step

The source ranks scores `value i + epsilon i / theta`.  If one writes
`z = epsilon / theta`, the density of a single transformed coordinate is
`theta * f (theta * z)` for `theta > 0`; the displayed reciprocal scaling in
the source is a change-of-variables typo.  `scaledIIDDensity` is the algebraic
finite product kernel, and represents that probability density only at positive
accuracy.

Pointwise differentiability of `f` alone does not justify moving a derivative
through the integral. The theorem below is an auxiliary conditional result for
this scaling-coordinate representation: it adds a local dominated
differentiation condition. It is not the selected correction of the false
source theorem, whose W^{1,1} route must instead use score-space L1
translations.
-/

/--
Algebraic scaled-coordinate kernel for `z = epsilon / theta`.  When `theta > 0`
and `f` is a base density, it is the iid transformed density; it is not a
probability density at nonpositive `theta`.
-/
noncomputable def scaledIIDDensity {n : ℕ} (f : ℝ → ℝ)
    (theta : ℝ) (z : Candidate n → ℝ) : ℝ :=
  ∏ i : Candidate n, theta * f (theta * z i)

/-- Algebraic expansion of the scaled-coordinate kernel. -/
theorem scaledIIDDensity_eq_product_theta_mul {n : ℕ} (f : ℝ → ℝ)
    (theta : ℝ) (z : Candidate n → ℝ) :
    scaledIIDDensity f theta z =
      ∏ i : Candidate n, theta * f (theta * z i) :=
  rfl

/-- The noise vectors producing a particular ranking under additive scores. -/
def rankingNoiseRegion {n : ℕ} (value : Candidate n → ℝ)
    (pi : Ranking n) : Set (Candidate n → ℝ) :=
  {z | AppliedModelingLib.SocialChoice.Ranking.rankByScore
      (fun i => value i + z i) = pi}

/-- The scaled-coordinate kernel restricted to the ranking cell for `pi`. -/
noncomputable def rankingDensityIntegrand {n : ℕ} (f : ℝ → ℝ)
    (value : Candidate n → ℝ) (pi : Ranking n)
    (theta : ℝ) (z : Candidate n → ℝ) : ℝ :=
  (rankingNoiseRegion value pi).indicator
    (scaledIIDDensity f theta) z

/-- The kernel integral over a fixed ranking cell. -/
noncomputable def rankingDensityAtom {n : ℕ} (f : ℝ → ℝ)
    (value : Candidate n → ℝ) (pi : Ranking n) (theta : ℝ) : ℝ :=
  ∫ z : Candidate n → ℝ,
    rankingDensityIntegrand f value pi theta z

theorem rankingDensityAtom_eq_integral_over_region {n : ℕ} (f : ℝ → ℝ)
    (value : Candidate n → ℝ) (pi : Ranking n) (theta : ℝ)
    (hregion : MeasurableSet (rankingNoiseRegion value pi)) :
    rankingDensityAtom f value pi theta =
      ∫ z in rankingNoiseRegion value pi, scaledIIDDensity f theta z :=
  integral_indicator hregion

/--
Differentiability of the source density implies pointwise differentiability in
`theta` of the algebraic finite iid product kernel, and hence of its restriction
to any fixed ranking cell.  This auxiliary statement is not a probability-law
claim at nonpositive `theta`.
-/
theorem rankingDensityIntegrand_differentiableAt {n : ℕ}
    (f : ℝ → ℝ) (hf : ∀ x, DifferentiableAt ℝ f x)
    (value : Candidate n → ℝ) (pi : Ranking n)
    (theta : ℝ) (z : Candidate n → ℝ) :
    DifferentiableAt ℝ
      (fun theta' => rankingDensityIntegrand f value pi theta' z) theta := by
  by_cases hz : z ∈ rankingNoiseRegion value pi
  · simp only [rankingDensityIntegrand, Set.indicator_of_mem hz]
    unfold scaledIIDDensity
    have hprod : DifferentiableAt ℝ
        (fun theta' => ∏ i ∈ (Finset.univ : Finset (Candidate n)),
          theta' * f (theta' * z i)) theta := by
      apply DifferentiableAt.fun_finset_prod
      intro i _hi
      exact differentiableAt_id.mul
        ((hf (theta * z i)).comp theta
          (differentiableAt_id.mul
            (differentiableAt_const (c := z i))))
    simpa using hprod
  · simp only [rankingDensityIntegrand, Set.indicator_of_notMem hz]
    exact differentiableAt_const (c := 0)

/-- The pointwise derivative whose domination is required below. -/
noncomputable def rankingDensityDerivative {n : ℕ} (f : ℝ → ℝ)
    (value : Candidate n → ℝ) (pi : Ranking n)
    (theta : ℝ) (z : Candidate n → ℝ) : ℝ :=
  deriv (fun theta' => rankingDensityIntegrand f value pi theta' z) theta

theorem rankingDensityIntegrand_hasDerivAt {n : ℕ}
    (f : ℝ → ℝ) (hf : ∀ x, DifferentiableAt ℝ f x)
    (value : Candidate n → ℝ) (pi : Ranking n)
    (theta : ℝ) (z : Candidate n → ℝ) :
    HasDerivAt
      (fun theta' => rankingDensityIntegrand f value pi theta' z)
      (rankingDensityDerivative f value pi theta z) theta := by
  simpa [rankingDensityDerivative] using
    (rankingDensityIntegrand_differentiableAt
      f hf value pi theta z).hasDerivAt

/--
Sufficient local domination package for this scaling-coordinate theorem.

The derivative is derived above from the paper's differentiability assumption
on `f`; it is not supplied as certificate data.  The same integrable `bound`
must dominate that derivative throughout a fixed neighborhood `s` of `theta0`.
These are the additional hypotheses needed by Mathlib's dominated
parametric-integral theorem. They are not implied by the selected W^{1,1}
corrected-model condition.
-/
structure RankingAtomDominatedDerivativeRegularity {n : ℕ}
    (f : ℝ → ℝ) (value : Candidate n → ℝ) (pi : Ranking n)
    (theta0 : ℝ) : Type where
  neighborhood : Set ℝ
  bound : (Candidate n → ℝ) → ℝ
  neighborhood_mem : neighborhood ∈ 𝓝 theta0
  integrand_aeStronglyMeasurable :
    ∀ᶠ theta in 𝓝 theta0,
      AEStronglyMeasurable
        (rankingDensityIntegrand f value pi theta) volume
  integrand_integrable :
    Integrable (rankingDensityIntegrand f value pi theta0) volume
  derivative_aeStronglyMeasurable :
    AEStronglyMeasurable
      (rankingDensityDerivative f value pi theta0) volume
  derivative_bound :
    ∀ᵐ z ∂(volume : Measure (Candidate n → ℝ)),
      ∀ theta ∈ neighborhood,
        ‖rankingDensityDerivative f value pi theta z‖ ≤ bound z
  bound_integrable : Integrable bound volume

/--
Conditional differentiation-under-the-integral conclusion for the auxiliary
dominated route.
-/
theorem rankingDensityAtom_hasDerivAt_of_dominated {n : ℕ}
    (f : ℝ → ℝ) (hf : ∀ x, DifferentiableAt ℝ f x)
    (value : Candidate n → ℝ) (pi : Ranking n)
    {theta0 : ℝ} (htheta0 : 0 < theta0)
    (regularity :
      RankingAtomDominatedDerivativeRegularity f value pi theta0) :
    HasDerivAt (rankingDensityAtom f value pi)
      (∫ z : Candidate n → ℝ,
        rankingDensityDerivative f value pi theta0 z) theta0 := by
  have hsource :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := (volume : Measure (Candidate n → ℝ)))
      (F := fun theta => rankingDensityIntegrand f value pi theta)
      (F' := rankingDensityDerivative f value pi)
      (bound := regularity.bound)
      regularity.neighborhood_mem
      regularity.integrand_aeStronglyMeasurable
      regularity.integrand_integrable
      regularity.derivative_aeStronglyMeasurable
      regularity.derivative_bound
      regularity.bound_integrable
      (Filter.Eventually.of_forall fun z theta _htheta =>
        rankingDensityIntegrand_hasDerivAt f hf value pi theta z)
  simpa [rankingDensityAtom] using hsource.2

/-- Auxiliary differentiability result under the explicit domination package. -/
theorem rankingDensityAtom_differentiableAt_of_dominated {n : ℕ}
    (f : ℝ → ℝ) (hf : ∀ x, DifferentiableAt ℝ f x)
    (value : Candidate n → ℝ) (pi : Ranking n)
    {theta0 : ℝ} (htheta0 : 0 < theta0)
    (regularity :
      RankingAtomDominatedDerivativeRegularity f value pi theta0) :
    DifferentiableAt ℝ (rankingDensityAtom f value pi) theta0 :=
  (rankingDensityAtom_hasDerivAt_of_dominated
    f hf value pi htheta0 regularity).differentiableAt

end KR21Monoculture

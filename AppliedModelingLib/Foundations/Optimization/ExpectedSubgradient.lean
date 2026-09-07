import Mathlib.MeasureTheory.Integral.Bochner.Basic
import AppliedModelingLib.Foundations.Optimization.ProjectedSubgradient

/-!
# Expected Subgradients

If a random cost `cost θ` admits a subgradient `sampleGradient θ` at a common
point `x` for almost every `θ`, then the expected direction
`∫ θ, sampleGradient θ` is a subgradient of the expected cost
`y ↦ ∫ θ, cost θ y` at `x`.

This is the interchange step quoted by stochastic subgradient papers when they
argue that a sampled direction is, in expectation, a subgradient of the
population objective.  It is a plain consequence of monotonicity and linearity
of the Bochner integral: integrate the pointwise subgradient inequality.

## Main declarations

- `finiteSubgradientAt_integral`: the interchange theorem.
- `ExpectedSubgradientProperty`: the same statement packaged for use as a
  named hypothesis at a paper boundary.
-/

open MeasureTheory
open scoped BigOperators

namespace AppliedModelingLib
namespace Optimization

variable {Coord Theta : Type*} [Fintype Coord] [MeasurableSpace Theta]

/--
Expected-subgradient interchange.

If `sampleGradient θ` is a subgradient of `cost θ` at `x` for a.e. `θ`, the
sampled costs are integrable at `x` and at each comparison point `y`, and each
coordinate of `sampleGradient` is integrable, then the coordinatewise expected
gradient is a subgradient of the expected cost at `x`.
-/
theorem finiteSubgradientAt_integral
    {μ : Measure Theta}
    {cost : Theta → (Coord → ℝ) → ℝ}
    {sampleGradient : Theta → Coord → ℝ}
    {x : Coord → ℝ}
    (hsub : ∀ᵐ θ ∂μ, FiniteSubgradientAt (cost θ) x (sampleGradient θ))
    (hcost : ∀ y, Integrable (fun θ => cost θ y) μ)
    (hgrad : ∀ i, Integrable (fun θ => sampleGradient θ i) μ) :
    FiniteSubgradientAt (fun y => ∫ θ, cost θ y ∂μ) x
      (fun i => ∫ θ, sampleGradient θ i ∂μ) := by
  intro y
  have hlin :
      FiniteDimensionalNorms.coordinateLinearFunctional
          (fun i => ∫ θ, sampleGradient θ i ∂μ) (fun i => y i - x i) =
        ∫ θ, FiniteDimensionalNorms.coordinateLinearFunctional
            (sampleGradient θ) (fun i => y i - x i) ∂μ := by
    simp only [coordinateLinearFunctional_apply]
    rw [integral_finset_sum]
    · exact Finset.sum_congr rfl fun i _ => (integral_mul_const _ _).symm
    · exact fun i _ => (hgrad i).mul_const _
  have hint :
      Integrable
        (fun θ => cost θ x +
          FiniteDimensionalNorms.coordinateLinearFunctional
            (sampleGradient θ) (fun i => y i - x i)) μ := by
    refine (hcost x).add ?_
    simp only [coordinateLinearFunctional_apply]
    exact integrable_finset_sum _ fun i _ => (hgrad i).mul_const _
  have hmono :
      ∫ θ, (cost θ x +
          FiniteDimensionalNorms.coordinateLinearFunctional
            (sampleGradient θ) (fun i => y i - x i)) ∂μ ≤
        ∫ θ, cost θ y ∂μ :=
    integral_mono_ae hint (hcost y) (hsub.mono fun θ hθ => hθ y)
  calc
    (∫ θ, cost θ x ∂μ) +
        FiniteDimensionalNorms.coordinateLinearFunctional
          (fun i => ∫ θ, sampleGradient θ i ∂μ) (fun i => y i - x i)
        = ∫ θ, (cost θ x +
            FiniteDimensionalNorms.coordinateLinearFunctional
              (sampleGradient θ) (fun i => y i - x i)) ∂μ := by
          rw [hlin, ← integral_add (hcost x)]
          simp only [coordinateLinearFunctional_apply]
          exact integrable_finset_sum _ fun i _ => (hgrad i).mul_const _
    _ ≤ ∫ θ, cost θ y ∂μ := hmono

/--
The expected-subgradient property for a fixed sampling measure and cost family,
packaged as a named proposition.

This is the shape a paper needs when it quotes "the expected sampled subgradient
is a subgradient of the expected objective" as a step.  Unlike a free-floating
assumption over unrelated predicates, it is tied to the actual integral, so it
is a theorem rather than a postulate.
-/
def ExpectedSubgradientProperty
    (μ : Measure Theta)
    (cost : Theta → (Coord → ℝ) → ℝ)
    (isSampleSubgradient : (Coord → ℝ) → Theta → (Coord → ℝ) → Prop) : Prop :=
  ∀ (x : Coord → ℝ) (sampleGradient : Theta → Coord → ℝ),
    (∀ᵐ θ ∂μ, isSampleSubgradient x θ (sampleGradient θ)) →
      (∀ y, Integrable (fun θ => cost θ y) μ) →
        (∀ i, Integrable (fun θ => sampleGradient θ i) μ) →
          (∀ᵐ θ ∂μ, ∀ g,
            isSampleSubgradient x θ g → FiniteSubgradientAt (cost θ) x g) →
            FiniteSubgradientAt (fun y => ∫ θ, cost θ y ∂μ) x
              (fun i => ∫ θ, sampleGradient θ i ∂μ)

/-- The expected-subgradient property always holds. -/
theorem expectedSubgradientProperty
    (μ : Measure Theta)
    (cost : Theta → (Coord → ℝ) → ℝ)
    (isSampleSubgradient : (Coord → ℝ) → Theta → (Coord → ℝ) → Prop) :
    ExpectedSubgradientProperty μ cost isSampleSubgradient := by
  intro x sampleGradient hsel hcost hgrad hsound
  refine finiteSubgradientAt_integral ?_ hcost hgrad
  filter_upwards [hsel, hsound] with θ hθ hsoundθ
  exact hsoundθ _ hθ

end Optimization
end AppliedModelingLib

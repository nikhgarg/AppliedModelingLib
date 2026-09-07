import PG24NoisyMatchingMarkets.Theorem2TwoScaleRepair

/-!
# PG24 Theorem 2 two-scale source-package boundary

The small-firm event clause in `proof-amplifying.tex:220-250` has a split
coefficient and an independent-product coefficient.  The current one-scale
package uses the same parameter for both.  This file records the exact
two-scale coefficient and proves both the diagonal specialization that the
old package supplies and the strict off-diagonal gap that it cannot supply.
-/

namespace PG24NoisyMatchingMarkets

noncomputable section

/-- The independent-product loss in the long-tail comparison. -/
def theorem2_twoScaleProductGap (endpoint sigma : ℝ) : ℝ :=
  1 - Real.exp (-(2 * endpoint * sigma))

/--
The small-block coefficient after separating split mass `delta` from the
long-tail endpoint error `endpoint`.  This is the scalar coefficient in the
small matched-event bound derived from `proof-amplifying.tex:220-250`.
-/
def theorem2_twoScaleSmallBlockCoefficient
    (totalSupply delta endpoint sigma : ℝ) : ℝ :=
  Real.sqrt delta *
    (1 - totalSupply - delta - theorem2_twoScaleProductGap endpoint sigma)

/-- The source small-event conclusion, factored to expose its scalar coefficient. -/
def theorem2_twoScaleSmallEventBound
    (totalSupply delta endpoint sigma affordance eventMass : ℝ) : Prop :=
  theorem2_twoScaleSmallBlockCoefficient totalSupply delta endpoint sigma *
      affordance ≤ eventMass

/--
The existing one-parameter package supplies the diagonal `endpoint = delta`
instance of the two-scale event bound, and no more by definitional transport.
-/
theorem theorem2_twoScaleSmallEventBound_diagonal
    {totalSupply delta sigma affordance eventMass : ℝ}
    (h : theorem2_twoScaleSmallEventBound
      totalSupply delta delta sigma affordance eventMass) :
    theorem2_twoScaleSmallEventBound
      totalSupply delta delta sigma affordance eventMass :=
  h

/--
For positive `sigma`, decreasing the long-tail endpoint error strictly
increases the small-event coefficient while holding the split fixed.  Thus a
bound proved with the diagonal product loss is not a bound with the repaired,
smaller endpoint loss.
-/
theorem theorem2_twoScaleSmallBlockCoefficient_strict_mono_endpoint
    {totalSupply delta endpoint sigma : ℝ}
    (hdelta_pos : 0 < delta) (hendpoint_lt : endpoint < delta)
    (hsigma_pos : 0 < sigma) :
    theorem2_twoScaleSmallBlockCoefficient totalSupply delta delta sigma <
      theorem2_twoScaleSmallBlockCoefficient totalSupply delta endpoint sigma := by
  have hproduct : endpoint * sigma < delta * sigma :=
    mul_lt_mul_of_pos_right hendpoint_lt hsigma_pos
  have hscaled : 2 * endpoint * sigma < 2 * delta * sigma := by
    nlinarith
  have hexp :
      Real.exp (-(2 * delta * sigma)) <
        Real.exp (-(2 * endpoint * sigma)) := by
    exact Real.exp_lt_exp.mpr (by linarith)
  have hgap :
      theorem2_twoScaleProductGap endpoint sigma <
        theorem2_twoScaleProductGap delta sigma := by
    unfold theorem2_twoScaleProductGap
    linarith
  have hcoefficient :
      1 - totalSupply - delta - theorem2_twoScaleProductGap delta sigma <
        1 - totalSupply - delta - theorem2_twoScaleProductGap endpoint sigma := by
    linarith
  have hsqrt_pos : 0 < Real.sqrt delta := Real.sqrt_pos.2 hdelta_pos
  unfold theorem2_twoScaleSmallBlockCoefficient
  exact mul_lt_mul_of_pos_left hcoefficient hsqrt_pos

/--
The diagonal one-scale small-event inequality cannot, as a matter of logic,
be upgraded to an off-diagonal endpoint choice.  The witnesses are scalar
versions of the derived small-block event bound, so this rules out a purely
order-theoretic adapter from the current package to the repaired package.
-/
theorem theorem2_twoScaleSmallEventBound_offDiagonal_not_of_diagonal
    {totalSupply delta endpoint sigma : ℝ}
    (hdelta_pos : 0 < delta) (hendpoint_lt : endpoint < delta)
    (hsigma_pos : 0 < sigma) :
    ∃ affordance eventMass : ℝ,
      theorem2_twoScaleSmallEventBound
        totalSupply delta delta sigma affordance eventMass ∧
      ¬ theorem2_twoScaleSmallEventBound
        totalSupply delta endpoint sigma affordance eventMass := by
  let diagonal :=
    theorem2_twoScaleSmallBlockCoefficient totalSupply delta delta sigma
  refine ⟨1, diagonal, ?_, ?_⟩
  · unfold theorem2_twoScaleSmallEventBound
    simp [diagonal]
  · intro hoffDiagonal
    have hstrict := theorem2_twoScaleSmallBlockCoefficient_strict_mono_endpoint
      (totalSupply := totalSupply) hdelta_pos hendpoint_lt hsigma_pos
    unfold theorem2_twoScaleSmallEventBound at hoffDiagonal
    dsimp [diagonal] at hoffDiagonal
    nlinarith

end

end PG24NoisyMatchingMarkets

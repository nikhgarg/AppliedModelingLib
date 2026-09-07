import Mathlib.Tactic

/-!
# PG24 Theorem 3 dense/gap exponents

The extended coalition attenuation proof only needs the dense-cluster and
large-gap errors to vanish.  Unlike the basic attenuation theorem, it does
not use the value-distribution or capacity estimates, so these exponents
depend only on the beta-max-concentration rate.

The declarations below are proof-support arithmetic.  They are not source
assumptions and they do not state a coalition-attentuation conclusion.
-/

namespace PG24NoisyMatchingMarkets

noncomputable section

/-- A beta-only scale in `(0, 1)` used by the coalition dense/gap proof. -/
def theorem3CoalitionScale (beta : ℝ) : ℝ :=
  beta / (1 + beta)

/-- Width exponent for the dense cutoff window. -/
def theorem3DenseWindowExponent (beta : ℝ) : ℝ :=
  -theorem3CoalitionScale beta / 8

/-- Dense-window cardinality exponent. -/
def theorem3DenseClusterExponent (beta : ℝ) : ℝ :=
  1 - theorem3CoalitionScale beta / 4

/-- Early-prefix exponent used in the large-gap branch. -/
def theorem3EarlyCutoffExponent (beta : ℝ) : ℝ :=
  1 - theorem3CoalitionScale beta / 16

/-- Vanishing displacement exponent for the large-gap branch. -/
def theorem3GapDisplacementExponent (beta : ℝ) : ℝ :=
  -theorem3CoalitionScale beta / 4

/-- The positive geometric gap exponent forced by the beta-only choices. -/
def theorem3LargeGapExponent (beta : ℝ) : ℝ :=
  theorem3DenseWindowExponent beta +
    theorem3EarlyCutoffExponent beta -
      theorem3DenseClusterExponent beta

theorem theorem3CoalitionScale_pos {beta : ℝ} (hbeta : 0 < beta) :
    0 < theorem3CoalitionScale beta := by
  unfold theorem3CoalitionScale
  exact div_pos hbeta (by linarith)

theorem theorem3CoalitionScale_lt_one {beta : ℝ} (hbeta : 0 < beta) :
    theorem3CoalitionScale beta < 1 := by
  unfold theorem3CoalitionScale
  have hdenom : 0 < 1 + beta := by linarith
  rw [div_lt_one hdenom]
  linarith

theorem theorem3DenseWindowExponent_neg {beta : ℝ} (hbeta : 0 < beta) :
    theorem3DenseWindowExponent beta < 0 := by
  unfold theorem3DenseWindowExponent
  have hscale := theorem3CoalitionScale_pos hbeta
  linarith

theorem theorem3DenseClusterExponent_pos {beta : ℝ} (hbeta : 0 < beta) :
    0 < theorem3DenseClusterExponent beta := by
  unfold theorem3DenseClusterExponent
  have hscale_lt_one := theorem3CoalitionScale_lt_one hbeta
  linarith

theorem theorem3DenseClusterExponent_lt_one {beta : ℝ} (hbeta : 0 < beta) :
    theorem3DenseClusterExponent beta < 1 := by
  unfold theorem3DenseClusterExponent
  have hscale := theorem3CoalitionScale_pos hbeta
  linarith

theorem theorem3EarlyCutoffExponent_lt_one {beta : ℝ} (hbeta : 0 < beta) :
    theorem3EarlyCutoffExponent beta < 1 := by
  unfold theorem3EarlyCutoffExponent
  have hscale := theorem3CoalitionScale_pos hbeta
  linarith

theorem theorem3EarlyCutoffExponent_pos {beta : ℝ} (hbeta : 0 < beta) :
    0 < theorem3EarlyCutoffExponent beta := by
  unfold theorem3EarlyCutoffExponent
  have hscale_lt_one := theorem3CoalitionScale_lt_one hbeta
  linarith

theorem theorem3DenseCluster_lt_earlyCutoff {beta : ℝ} (hbeta : 0 < beta) :
    theorem3DenseClusterExponent beta < theorem3EarlyCutoffExponent beta := by
  unfold theorem3DenseClusterExponent theorem3EarlyCutoffExponent
  have hscale := theorem3CoalitionScale_pos hbeta
  linarith

theorem theorem3LargeGapExponent_eq_scale_div_sixteen (beta : ℝ) :
    theorem3LargeGapExponent beta = theorem3CoalitionScale beta / 16 := by
  unfold theorem3LargeGapExponent theorem3DenseWindowExponent
    theorem3EarlyCutoffExponent theorem3DenseClusterExponent
  ring

theorem theorem3LargeGapExponent_pos {beta : ℝ} (hbeta : 0 < beta) :
    0 < theorem3LargeGapExponent beta := by
  rw [theorem3LargeGapExponent_eq_scale_div_sixteen]
  exact div_pos (theorem3CoalitionScale_pos hbeta) (by norm_num)

theorem theorem3GapDisplacementExponent_neg {beta : ℝ} (hbeta : 0 < beta) :
    theorem3GapDisplacementExponent beta < 0 := by
  unfold theorem3GapDisplacementExponent
  have hscale := theorem3CoalitionScale_pos hbeta
  linarith

theorem theorem3_neg_half_beta_lt_gapDisplacement {beta : ℝ} (hbeta : 0 < beta) :
    -beta / 2 < theorem3GapDisplacementExponent beta := by
  unfold theorem3GapDisplacementExponent theorem3CoalitionScale
  have hdenom : 0 < 1 + beta := by linarith
  field_simp [ne_of_gt hdenom]
  nlinarith

theorem theorem3GapDisplacement_lt_largeGap {beta : ℝ} (hbeta : 0 < beta) :
    theorem3GapDisplacementExponent beta < theorem3LargeGapExponent beta := by
  rw [theorem3LargeGapExponent_eq_scale_div_sixteen]
  unfold theorem3GapDisplacementExponent
  have hscale := theorem3CoalitionScale_pos hbeta
  linarith

/-- Dense-branch high-endpoint Chebyshev exponent. -/
def theorem3DenseHighErrorExponent (beta : ℝ) : ℝ :=
  -(2 * theorem3DenseWindowExponent beta) -
    beta * theorem3DenseClusterExponent beta

/-- Dense-branch low-endpoint union-bound exponent. -/
def theorem3DenseLowErrorExponent (beta : ℝ) : ℝ :=
  1 - 2 * theorem3DenseWindowExponent beta -
    (1 + beta) * theorem3DenseClusterExponent beta

/-- Large-gap-branch low-endpoint Chebyshev exponent. -/
def theorem3GapLowErrorExponent (beta : ℝ) : ℝ :=
  -beta - 2 * theorem3GapDisplacementExponent beta

/-- Large-gap-branch high-endpoint Chebyshev exponent. -/
def theorem3GapHighErrorExponent (beta : ℝ) : ℝ :=
  -2 * theorem3LargeGapExponent beta

theorem theorem3DenseHighErrorExponent_eq_neg_three_quarters {beta : ℝ}
    (hbeta : 0 < beta) :
    theorem3DenseHighErrorExponent beta = -(3 * beta / 4) := by
  unfold theorem3DenseHighErrorExponent theorem3DenseWindowExponent
    theorem3DenseClusterExponent theorem3CoalitionScale
  have hdenom : 1 + beta ≠ 0 := by linarith
  field_simp [hdenom]
  ring

theorem theorem3DenseHighErrorExponent_neg {beta : ℝ} (hbeta : 0 < beta) :
    theorem3DenseHighErrorExponent beta < 0 := by
  rw [theorem3DenseHighErrorExponent_eq_neg_three_quarters hbeta]
  linarith

theorem theorem3DenseLowErrorExponent_neg {beta : ℝ} (hbeta : 0 < beta) :
    theorem3DenseLowErrorExponent beta < 0 := by
  unfold theorem3DenseLowErrorExponent theorem3DenseWindowExponent
    theorem3DenseClusterExponent theorem3CoalitionScale
  have hdenom : 0 < 1 + beta := by linarith
  field_simp [ne_of_gt hdenom]
  nlinarith

theorem theorem3GapLowErrorExponent_neg {beta : ℝ} (hbeta : 0 < beta) :
    theorem3GapLowErrorExponent beta < 0 := by
  unfold theorem3GapLowErrorExponent theorem3GapDisplacementExponent
    theorem3CoalitionScale
  have hdenom : 0 < 1 + beta := by linarith
  field_simp [ne_of_gt hdenom]
  nlinarith

theorem theorem3GapHighErrorExponent_neg {beta : ℝ} (hbeta : 0 < beta) :
    theorem3GapHighErrorExponent beta < 0 := by
  unfold theorem3GapHighErrorExponent
  linarith [theorem3LargeGapExponent_pos hbeta]

end

end PG24NoisyMatchingMarkets

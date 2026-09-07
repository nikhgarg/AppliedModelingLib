import AppliedModelingLib.Foundations.Optimization.SmoothComposition
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Finite softmax calculus

This module develops the Euclidean first-order bounds for a finite softmax
vector and one labeled negative-log-softmax loss.  The quantitative core is
the elementary covariance inequality for the softmax Jacobian: its operator
norm is at most one.  This gives a reusable smooth output layer for finite
multiclass models.
-/

namespace AppliedModelingLib.Optimization

open scoped BigOperators

noncomputable section

variable {Label : Type*} [Fintype Label] [DecidableEq Label] [Nonempty Label]

/-- Euclidean logit vectors indexed by a finite label type. -/
abbrev FiniteLogitSpace (Label : Type*) [Fintype Label] := EuclideanSpace ℝ Label

/-- The positive exponential normalizer of a finite logit vector. -/
def softmaxNormalizer (logits : FiniteLogitSpace Label) : ℝ :=
  ∑ label : Label, Real.exp (logits label)

/-- One coordinate of the finite softmax vector. -/
def softmaxProbability (logits : FiniteLogitSpace Label) (label : Label) : ℝ :=
  Real.exp (logits label) / softmaxNormalizer logits

/-- The finite softmax probability vector in its Euclidean norm. -/
def softmaxVector (logits : FiniteLogitSpace Label) : FiniteLogitSpace Label :=
  WithLp.toLp 2 fun label => softmaxProbability logits label

/-- The Euclidean coordinate vector for one target label. -/
def oneHot (target : Label) : FiniteLogitSpace Label :=
  WithLp.toLp 2 fun label => if label = target then 1 else 0

/-- Negative log-softmax, written as log-sum-exp minus the target logit. -/
def negativeLogSoftmax (target : Label) (logits : FiniteLogitSpace Label) : ℝ :=
  Real.log (softmaxNormalizer logits) - logits target

/-- The gradient vector of negative log-softmax. -/
def negativeLogSoftmaxGradient (target : Label) (logits : FiniteLogitSpace Label) :
    FiniteLogitSpace Label :=
  softmaxVector logits - oneHot target

theorem softmaxNormalizer_pos (logits : FiniteLogitSpace Label) :
    0 < softmaxNormalizer logits := by
  unfold softmaxNormalizer
  exact Finset.sum_pos (fun _ _ => Real.exp_pos _) (Finset.univ_nonempty)

theorem softmaxProbability_nonneg (logits : FiniteLogitSpace Label) (label : Label) :
    0 ≤ softmaxProbability logits label := by
  exact div_nonneg (Real.exp_pos _).le (softmaxNormalizer_pos logits).le

theorem softmaxProbability_sum (logits : FiniteLogitSpace Label) :
    ∑ label : Label, softmaxProbability logits label = 1 := by
  simp only [softmaxProbability, ← Finset.sum_div]
  exact div_self (softmaxNormalizer_pos logits).ne'

theorem softmaxProbability_le_one (logits : FiniteLogitSpace Label) (label : Label) :
    softmaxProbability logits label ≤ 1 := by
  rw [softmaxProbability, div_le_one (softmaxNormalizer_pos logits)]
  unfold softmaxNormalizer
  exact Finset.single_le_sum (fun other _ => (Real.exp_pos (logits other)).le)
    (Finset.mem_univ label)

theorem softmaxProbability_sq_sum_le_one (logits : FiniteLogitSpace Label) :
    ∑ label : Label, softmaxProbability logits label ^ 2 ≤ 1 := by
  calc
    ∑ label : Label, softmaxProbability logits label ^ 2 ≤
        ∑ label : Label, softmaxProbability logits label := by
      apply Finset.sum_le_sum
      intro label _
      nlinarith [softmaxProbability_nonneg logits label,
        softmaxProbability_le_one logits label]
    _ = 1 := softmaxProbability_sum logits

theorem softmaxVector_norm_sq_le_one (logits : FiniteLogitSpace Label) :
    ‖softmaxVector logits‖ ^ 2 ≤ 1 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simpa only [softmaxVector, PiLp.toLp_apply] using
    softmaxProbability_sq_sum_le_one logits

@[simp] theorem oneHot_apply (target label : Label) :
    oneHot target label = if label = target then 1 else 0 := rfl

@[simp] theorem oneHot_norm_sq (target : Label) : ‖oneHot target‖ ^ 2 = 1 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [oneHot]

theorem negativeLogSoftmaxGradient_norm_sq_le_two
    (target : Label) (logits : FiniteLogitSpace Label) :
    ‖negativeLogSoftmaxGradient target logits‖ ^ 2 ≤ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  have hexpand :
      (∑ label : Label,
        (negativeLogSoftmaxGradient target logits label) ^ 2) =
        (∑ label : Label, softmaxProbability logits label ^ 2) -
          2 * softmaxProbability logits target + 1 := by
    simp only [negativeLogSoftmaxGradient, PiLp.sub_apply, softmaxVector,
      oneHot_apply]
    calc
      (∑ label : Label,
          (softmaxProbability logits label - if label = target then 1 else 0) ^ 2) =
          ∑ label : Label,
            (softmaxProbability logits label ^ 2 -
              2 * softmaxProbability logits label *
                (if label = target then 1 else 0) +
              (if label = target then 1 else 0) ^ 2) := by
            apply Finset.sum_congr rfl
            intro label _
            ring
      _ = (∑ label : Label, softmaxProbability logits label ^ 2) -
          2 * softmaxProbability logits target + 1 := by
            simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hexpand]
  have hprobability := softmaxProbability_nonneg logits target
  linarith [softmaxProbability_sq_sum_le_one logits]

theorem negativeLogSoftmaxGradient_norm_le_sqrt_two
    (target : Label) (logits : FiniteLogitSpace Label) :
    ‖negativeLogSoftmaxGradient target logits‖ ≤ Real.sqrt 2 := by
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [negativeLogSoftmaxGradient_norm_sq_le_two target logits,
    norm_nonneg (negativeLogSoftmaxGradient target logits), Real.sqrt_nonneg 2]

/-- The softmax expectation of a Euclidean direction. -/
def softmaxMean (logits direction : FiniteLogitSpace Label) : ℝ :=
  ∑ label : Label, softmaxProbability logits label * direction label

/-- The action of the softmax Jacobian on a Euclidean direction. -/
def softmaxJacobianAction (logits direction : FiniteLogitSpace Label) :
    FiniteLogitSpace Label :=
  WithLp.toLp 2 fun label =>
    softmaxProbability logits label * (direction label - softmaxMean logits direction)

theorem softmax_weighted_variance_identity
    (logits direction : FiniteLogitSpace Label) :
    (∑ label : Label, softmaxProbability logits label *
        (direction label - softmaxMean logits direction) ^ 2) =
      (∑ label : Label, softmaxProbability logits label * direction label ^ 2) -
        softmaxMean logits direction ^ 2 := by
  let mean := softmaxMean logits direction
  change (∑ label : Label, softmaxProbability logits label *
      (direction label - mean) ^ 2) =
    (∑ label : Label, softmaxProbability logits label * direction label ^ 2) - mean ^ 2
  calc
    (∑ label : Label, softmaxProbability logits label *
        (direction label - mean) ^ 2) =
        ∑ label : Label,
          (softmaxProbability logits label * direction label ^ 2 -
            (2 * mean) * (softmaxProbability logits label * direction label) +
            mean ^ 2 * softmaxProbability logits label) := by
      apply Finset.sum_congr rfl
      intro label _
      ring
    _ = (∑ label : Label, softmaxProbability logits label * direction label ^ 2) -
        (2 * mean) *
          (∑ label : Label, softmaxProbability logits label * direction label) +
        mean ^ 2 * (∑ label : Label, softmaxProbability logits label) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum]
    _ = (∑ label : Label, softmaxProbability logits label * direction label ^ 2) -
        mean ^ 2 := by
      rw [show (∑ label : Label, softmaxProbability logits label * direction label) = mean by
        rfl, softmaxProbability_sum]
      ring

theorem softmaxJacobianAction_norm_sq_le
    (logits direction : FiniteLogitSpace Label) :
    ‖softmaxJacobianAction logits direction‖ ^ 2 ≤ ‖direction‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [softmaxJacobianAction, PiLp.toLp_apply]
  calc
    (∑ label : Label,
        (softmaxProbability logits label *
          (direction label - softmaxMean logits direction)) ^ 2) ≤
        ∑ label : Label, softmaxProbability logits label *
          (direction label - softmaxMean logits direction) ^ 2 := by
      apply Finset.sum_le_sum
      intro label _
      have hp0 := softmaxProbability_nonneg logits label
      have hp1 := softmaxProbability_le_one logits label
      have hsquare : 0 ≤ (direction label - softmaxMean logits direction) ^ 2 := sq_nonneg _
      have hpSquare : softmaxProbability logits label ^ 2 ≤
          softmaxProbability logits label := by nlinarith
      calc
        (softmaxProbability logits label *
            (direction label - softmaxMean logits direction)) ^ 2 =
            softmaxProbability logits label ^ 2 *
              (direction label - softmaxMean logits direction) ^ 2 := by ring
        _ ≤ softmaxProbability logits label *
            (direction label - softmaxMean logits direction) ^ 2 :=
          mul_le_mul_of_nonneg_right hpSquare hsquare
    _ = (∑ label : Label, softmaxProbability logits label * direction label ^ 2) -
          softmaxMean logits direction ^ 2 :=
      softmax_weighted_variance_identity logits direction
    _ ≤ ∑ label : Label, direction label ^ 2 := by
      have hweighted :
          (∑ label : Label, softmaxProbability logits label * direction label ^ 2) ≤
            ∑ label : Label, direction label ^ 2 := by
        apply Finset.sum_le_sum
        intro label _
        have hp0 := softmaxProbability_nonneg logits label
        have hp1 := softmaxProbability_le_one logits label
        nlinarith [sq_nonneg (direction label)]
      nlinarith [sq_nonneg (softmaxMean logits direction)]

theorem softmaxJacobianAction_norm_le
    (logits direction : FiniteLogitSpace Label) :
    ‖softmaxJacobianAction logits direction‖ ≤ ‖direction‖ := by
  nlinarith [softmaxJacobianAction_norm_sq_le logits direction,
    norm_nonneg (softmaxJacobianAction logits direction), norm_nonneg direction]

/-- The derivative of the finite exponential normalizer. -/
def softmaxNormalizerDeriv (logits : FiniteLogitSpace Label) :
    FiniteLogitSpace Label →L[ℝ] ℝ :=
  ∑ label : Label,
    Real.exp (logits label) • (EuclideanSpace.proj (𝕜 := ℝ) label)

theorem hasFDerivAt_softmaxNormalizer (logits : FiniteLogitSpace Label) :
    HasFDerivAt softmaxNormalizer (softmaxNormalizerDeriv logits) logits := by
  unfold softmaxNormalizer softmaxNormalizerDeriv
  rw [← Finset.sum_fn]
  apply HasFDerivAt.sum
  intro label _
  simpa only using
    (Real.hasDerivAt_exp (logits label)).comp_hasFDerivAt logits
      (EuclideanSpace.proj (𝕜 := ℝ) label).hasFDerivAt

theorem softmaxNormalizerDeriv_apply
    (logits direction : FiniteLogitSpace Label) :
    softmaxNormalizerDeriv logits direction =
      softmaxNormalizer logits * softmaxMean logits direction := by
  simp only [softmaxNormalizerDeriv, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, PiLp.proj_apply, smul_eq_mul]
  unfold softmaxNormalizer softmaxMean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro label _
  unfold softmaxProbability
  have hnormalizer := (softmaxNormalizer_pos logits).ne'
  field_simp
  rfl

/-- The scalar derivative of one softmax coordinate. -/
def softmaxProbabilityDeriv (logits : FiniteLogitSpace Label) (label : Label) :
    FiniteLogitSpace Label →L[ℝ] ℝ :=
  softmaxProbability logits label •
    (EuclideanSpace.proj (𝕜 := ℝ) label - innerSL ℝ (softmaxVector logits))

theorem realScalar_inner_eq_mul (first second : ℝ) :
    inner ℝ first second = first * second := by
  calc
    inner ℝ first second = inner ℝ (first • (1 : ℝ)) (second • (1 : ℝ)) := by simp
    _ = first * second := by
      rw [real_inner_smul_left, real_inner_smul_right,
        real_inner_self_eq_norm_sq]
      norm_num

theorem innerSL_softmaxVector_apply_eq_softmaxMean
    (logits direction : FiniteLogitSpace Label) :
    innerSL ℝ (softmaxVector logits) direction = softmaxMean logits direction := by
  rw [innerSL_apply_apply, PiLp.inner_apply]
  unfold softmaxMean softmaxVector
  apply Finset.sum_congr rfl
  intro label _
  rw [realScalar_inner_eq_mul]

theorem normalizer_inv_smul_deriv_eq_innerSL_softmaxVector
    (logits : FiniteLogitSpace Label) :
    (softmaxNormalizer logits)⁻¹ • softmaxNormalizerDeriv logits =
      innerSL ℝ (softmaxVector logits) := by
  ext direction
  simp only [ContinuousLinearMap.smul_apply]
  rw [softmaxNormalizerDeriv_apply]
  change (softmaxNormalizer logits)⁻¹ *
      (softmaxNormalizer logits * softmaxMean logits direction) =
    innerSL ℝ (softmaxVector logits) direction
  rw [← mul_assoc, inv_mul_cancel₀ (softmaxNormalizer_pos logits).ne', one_mul,
    innerSL_softmaxVector_apply_eq_softmaxMean]

theorem softmaxProbability_eq_exp_sub_logNormalizer
    (logits : FiniteLogitSpace Label) (label : Label) :
    softmaxProbability logits label =
      Real.exp (logits label - Real.log (softmaxNormalizer logits)) := by
  rw [Real.exp_sub, Real.exp_log (softmaxNormalizer_pos logits)]
  rfl

theorem hasFDerivAt_softmaxProbability
    (logits : FiniteLogitSpace Label) (label : Label) :
    HasFDerivAt (fun point => softmaxProbability point label)
      (softmaxProbabilityDeriv logits label) logits := by
  have hcoordinate :
      HasFDerivAt (fun point : FiniteLogitSpace Label => point label)
        (EuclideanSpace.proj (𝕜 := ℝ) label) logits :=
    (EuclideanSpace.proj (𝕜 := ℝ) label).hasFDerivAt
  have hlog :
      HasFDerivAt (fun point => Real.log (softmaxNormalizer point))
        ((softmaxNormalizer logits)⁻¹ • softmaxNormalizerDeriv logits) logits :=
    (hasFDerivAt_softmaxNormalizer logits).log (softmaxNormalizer_pos logits).ne'
  have hexp := (hcoordinate.sub hlog).exp
  rw [funext fun point => softmaxProbability_eq_exp_sub_logNormalizer point label]
  convert hexp using 1
  simp only [softmaxProbabilityDeriv,
    normalizer_inv_smul_deriv_eq_innerSL_softmaxVector]
  change softmaxProbability logits label •
      (EuclideanSpace.proj (𝕜 := ℝ) label - innerSL ℝ (softmaxVector logits)) =
    Real.exp (logits label - Real.log (softmaxNormalizer logits)) •
      (EuclideanSpace.proj (𝕜 := ℝ) label - innerSL ℝ (softmaxVector logits))
  rw [softmaxProbability_eq_exp_sub_logNormalizer]

/-- The Euclidean derivative of the complete softmax vector. -/
def softmaxJacobian (logits : FiniteLogitSpace Label) :
    FiniteLogitSpace Label →L[ℝ] FiniteLogitSpace Label :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Label => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun label => softmaxProbabilityDeriv logits label)

theorem softmaxJacobian_apply
    (logits direction : FiniteLogitSpace Label) :
    softmaxJacobian logits direction = softmaxJacobianAction logits direction := by
  ext label
  change softmaxProbability logits label *
      (direction label - innerSL ℝ (softmaxVector logits) direction) =
    softmaxProbability logits label *
      (direction label - softmaxMean logits direction)
  rw [innerSL_softmaxVector_apply_eq_softmaxMean]

theorem hasFDerivAt_softmaxVector (logits : FiniteLogitSpace Label) :
    HasFDerivAt softmaxVector (softmaxJacobian logits) logits := by
  let coordinates : FiniteLogitSpace Label → Label → ℝ :=
    fun point label => softmaxProbability point label
  have hcoordinates :
      HasFDerivAt coordinates
        (ContinuousLinearMap.pi fun label => softmaxProbabilityDeriv logits label) logits :=
    (hasFDerivAt_pi.mpr fun label => hasFDerivAt_softmaxProbability logits label)
  have htoLp := PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 (coordinates logits)
  simpa only [softmaxVector, coordinates, softmaxJacobian] using
    htoLp.comp logits hcoordinates

theorem softmaxJacobian_norm_le_one (logits : FiniteLogitSpace Label) :
    ‖softmaxJacobian logits‖ ≤ 1 := by
  refine (softmaxJacobian logits).opNorm_le_bound (by norm_num) ?_
  intro direction
  rw [softmaxJacobian_apply]
  simpa only [one_mul] using softmaxJacobianAction_norm_le logits direction

theorem softmaxVector_lipschitz (first second : FiniteLogitSpace Label) :
    ‖softmaxVector first - softmaxVector second‖ ≤ ‖first - second‖ := by
  let function : FiniteLogitSpace Label → FiniteLogitSpace Label := softmaxVector
  let derivative : FiniteLogitSpace Label →
      FiniteLogitSpace Label →L[ℝ] FiniteLogitSpace Label := softmaxJacobian
  have hdifferentiable : ∀ point ∈ (Set.univ : Set (FiniteLogitSpace Label)),
      HasFDerivWithinAt function (derivative point) Set.univ point := by
    intro point _
    exact (hasFDerivAt_softmaxVector point).hasFDerivWithinAt
  have hderivative : ∀ point ∈ (Set.univ : Set (FiniteLogitSpace Label)),
      ‖derivative point‖ ≤ (1 : ℝ) := by
    intro point _
    exact softmaxJacobian_norm_le_one point
  have hbound := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    hdifferentiable hderivative convex_univ
    (Set.mem_univ second) (Set.mem_univ first)
  simpa only [function, derivative, one_mul] using hbound

/-- The Fréchet derivative of one labeled negative-log-softmax loss. -/
def negativeLogSoftmaxDeriv (target : Label) (logits : FiniteLogitSpace Label) :
    FiniteLogitSpace Label →L[ℝ] ℝ :=
  innerSL ℝ (negativeLogSoftmaxGradient target logits)

theorem innerSL_oneHot_apply (target : Label) (direction : FiniteLogitSpace Label) :
    innerSL ℝ (oneHot target) direction = direction target := by
  rw [innerSL_apply_apply, PiLp.inner_apply]
  simp only [oneHot, PiLp.toLp_apply]
  calc
    (∑ label : Label, inner ℝ (if label = target then 1 else 0) (direction label)) =
        ∑ label : Label,
          (if label = target then direction label else 0) := by
      apply Finset.sum_congr rfl
      intro label _
      split_ifs <;> simp [realScalar_inner_eq_mul]
    _ = direction target := by simp

theorem hasFDerivAt_negativeLogSoftmax
    (target : Label) (logits : FiniteLogitSpace Label) :
    HasFDerivAt (negativeLogSoftmax target)
      (negativeLogSoftmaxDeriv target logits) logits := by
  have hlog :=
    (hasFDerivAt_softmaxNormalizer logits).log (softmaxNormalizer_pos logits).ne'
  have hcoordinate :
      HasFDerivAt (fun point : FiniteLogitSpace Label => point target)
        (EuclideanSpace.proj (𝕜 := ℝ) target) logits :=
    (EuclideanSpace.proj (𝕜 := ℝ) target).hasFDerivAt
  unfold negativeLogSoftmax negativeLogSoftmaxDeriv
  convert hlog.sub hcoordinate using 1
  rw [normalizer_inv_smul_deriv_eq_innerSL_softmaxVector]
  ext direction
  simp only [ContinuousLinearMap.sub_apply, innerSL_apply_apply]
  unfold negativeLogSoftmaxGradient
  rw [inner_sub_left]
  have honeHot : inner ℝ (oneHot target) direction = direction target := by
    simpa only [innerSL_apply_apply] using innerSL_oneHot_apply target direction
  rw [honeHot]
  rfl

theorem negativeLogSoftmaxGradient_lipschitz
    (target : Label) (first second : FiniteLogitSpace Label) :
    ‖negativeLogSoftmaxGradient target first -
        negativeLogSoftmaxGradient target second‖ ≤ ‖first - second‖ := by
  calc
    ‖negativeLogSoftmaxGradient target first -
        negativeLogSoftmaxGradient target second‖ =
        ‖softmaxVector first - softmaxVector second‖ := by
      unfold negativeLogSoftmaxGradient
      congr 1
      abel
    _ ≤ ‖first - second‖ := softmaxVector_lipschitz first second

theorem negativeLogSoftmaxDeriv_norm_le_sqrt_two
    (target : Label) (logits : FiniteLogitSpace Label) :
    ‖negativeLogSoftmaxDeriv target logits‖ ≤ Real.sqrt 2 := by
  rw [negativeLogSoftmaxDeriv, innerSL_apply_norm]
  exact negativeLogSoftmaxGradient_norm_le_sqrt_two target logits

theorem negativeLogSoftmaxDeriv_lipschitz
    (target : Label) (first second : FiniteLogitSpace Label) :
    ‖negativeLogSoftmaxDeriv target first - negativeLogSoftmaxDeriv target second‖ ≤
      ‖first - second‖ := by
  rw [negativeLogSoftmaxDeriv, negativeLogSoftmaxDeriv, ← map_sub,
    innerSL_apply_norm]
  exact negativeLogSoftmaxGradient_lipschitz target first second

theorem negativeLogSoftmax_lipschitz
    (target : Label) (first second : FiniteLogitSpace Label) :
    ‖negativeLogSoftmax target first - negativeLogSoftmax target second‖ ≤
      Real.sqrt 2 * ‖first - second‖ := by
  let function : FiniteLogitSpace Label → ℝ := negativeLogSoftmax target
  let derivative : FiniteLogitSpace Label → FiniteLogitSpace Label →L[ℝ] ℝ :=
    negativeLogSoftmaxDeriv target
  have hdifferentiable : ∀ point ∈ (Set.univ : Set (FiniteLogitSpace Label)),
      HasFDerivWithinAt function (derivative point) Set.univ point := by
    intro point _
    exact (hasFDerivAt_negativeLogSoftmax target point).hasFDerivWithinAt
  have hderivative : ∀ point ∈ (Set.univ : Set (FiniteLogitSpace Label)),
      ‖derivative point‖ ≤ Real.sqrt 2 := by
    intro point _
    exact negativeLogSoftmaxDeriv_norm_le_sqrt_two target point
  have hbound := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    hdifferentiable hderivative convex_univ
    (Set.mem_univ second) (Set.mem_univ first)
  simpa only [function, derivative] using hbound

/--
One labeled negative-log-softmax loss as a first-order smooth map, with the
dimension-free constants used in neural-network smoothness calculations.
-/
def negativeLogSoftmaxSmoothMap (target : Label) :
    FirstOrderSmoothMap (FiniteLogitSpace Label) ℝ where
  toFun := negativeLogSoftmax target
  deriv := negativeLogSoftmaxDeriv target
  valueLipschitz := Real.sqrt 2
  derivBound := Real.sqrt 2
  derivSmoothness := 1
  valueLipschitz_nonneg := Real.sqrt_nonneg 2
  derivBound_nonneg := Real.sqrt_nonneg 2
  derivSmoothness_nonneg := zero_le_one
  hasFDerivAt := hasFDerivAt_negativeLogSoftmax target
  value_lipschitz := negativeLogSoftmax_lipschitz target
  deriv_bound := negativeLogSoftmaxDeriv_norm_le_sqrt_two target
  deriv_lipschitz := by
    intro first second
    simpa only [one_mul] using negativeLogSoftmaxDeriv_lipschitz target first second

theorem negativeLogSoftmaxSmoothMap_source_constants (target : Label) :
    (negativeLogSoftmaxSmoothMap target).valueLipschitz = Real.sqrt 2 ∧
    (negativeLogSoftmaxSmoothMap target).derivBound = Real.sqrt 2 ∧
    (negativeLogSoftmaxSmoothMap target).derivSmoothness = 1 :=
  ⟨rfl, rfl, rfl⟩

end
end AppliedModelingLib.Optimization

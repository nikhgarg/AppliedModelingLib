import AppliedModelingLib.Foundations.Probability.FinitePinsker
import AppliedModelingLib.Foundations.Optimization.SmoothStrongConvex
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Entropy-regularized finite optimization

This module proves the finite Gibbs variational identity for the scaled
expected-utility-minus-KL objective.  The formulation uses an
`inverseTemperature` directly, avoiding a hidden division by a positive KL
coefficient.  Positive-coefficient DPO, Hedge, and mirror-descent objectives
can specialize it by setting `inverseTemperature` to that coefficient's
inverse.

## Main declarations

- `exponentialTiltObjective`
- `exponentialTiltObjective_eq_logPartition_sub_kl`
- `exponentialTiltObjective_le_at_exponentialTilt`
- `exponentialTiltObjective_globalMax_unique`
- `finiteKLDivergence_exponentialTilt_three_point`
- `exponentialTilt_utility_globalMax_at_attainedKL`
- `exponentialTilt_utility_globalMax_unique_at_attainedKL`
- `exponentialTilt_regularizedUtility_globalMax`
-/

open scoped BigOperators InnerProductSpace

namespace AppliedModelingLib

/-- The shifted coordinate entropy used when an optimization variable is only
known to lie in `[-1, 1]`.  The shift by two keeps the logarithm's argument in
`[1, 3]` on that domain. -/
noncomputable def shiftedCoordinateEntropy (value : ℝ) : ℝ :=
  (value + 2) * Real.log (value + 2)

/-- The derivative of shifted coordinate entropy away from its sole
singularity at `-2`.  On the unit interval this is exactly
`log (u + 2) + 1`, the non-linear part of Algorithm 7's ERM weights. -/
theorem shiftedCoordinateEntropy_hasDerivAt
    (value : ℝ) (hvalue : value + 2 ≠ 0) :
    HasDerivAt shiftedCoordinateEntropy (Real.log (value + 2) + 1) value := by
  unfold shiftedCoordinateEntropy
  have hnonzero : (2 : ℝ) + value ≠ 0 := by simpa [add_comm] using hvalue
  simpa [add_comm] using
    (Real.hasDerivAt_mul_log hnonzero).comp_const_add (2 : ℝ) value

/-- One weighted coordinate of the entropy-regularized ERM objective.  The
linear weight is supplied by accumulated labels, while the entropy term keeps
the optimization smooth on the cube used by Algorithm 7. -/
noncomputable def shiftedEntropyRegularizedCoordinateObjective
    (linearWeight value : ℝ) : ℝ :=
  linearWeight * value + shiftedCoordinateEntropy value

/-- Exact derivative of a weighted shifted-entropy coordinate. -/
theorem shiftedEntropyRegularizedCoordinateObjective_hasDerivAt
    (linearWeight value : ℝ) (hvalue : value + 2 ≠ 0) :
    HasDerivAt (shiftedEntropyRegularizedCoordinateObjective linearWeight)
      (linearWeight + Real.log (value + 2) + 1) value := by
  unfold shiftedEntropyRegularizedCoordinateObjective
  have hlinear : HasDerivAt (fun input : ℝ => linearWeight * input) linearWeight value := by
    simpa only [mul_one] using (hasDerivAt_id value).const_mul linearWeight
  have hentropy := shiftedCoordinateEntropy_hasDerivAt value hvalue
  simpa only [add_assoc] using hlinear.add hentropy

/-- The logarithm is one-Lipschitz on the positive ray beginning at one.
This elementary mean-value estimate is the coordinatewise smoothness input
for the shifted entropy objective. -/
theorem norm_log_sub_le_norm_sub_of_one_le
    {first second : ℝ} (hfirst : 1 ≤ first) (hsecond : 1 ≤ second) :
    ‖Real.log first - Real.log second‖ ≤ ‖first - second‖ := by
  have hderivative : ∀ value ∈ Set.Ici (1 : ℝ),
      HasDerivWithinAt Real.log value⁻¹ (Set.Ici (1 : ℝ)) value := by
    intro value hvalue
    apply (Real.hasDerivAt_log (ne_of_gt (lt_of_lt_of_le zero_lt_one hvalue))).hasDerivWithinAt
  have hderivativeBound : ∀ value ∈ Set.Ici (1 : ℝ), ‖value⁻¹‖ ≤ (1 : ℝ) := by
    intro value hvalue
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (zero_le_one.trans hvalue))]
    exact inv_le_one_of_one_le₀ hvalue
  have hmeanValue := (convex_Ici (1 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderivative hderivativeBound hsecond hfirst
  simpa only [one_mul, Real.norm_eq_abs, abs_sub_comm] using hmeanValue

/-- The gradient coordinate `log (u + 2) + 1` of shifted entropy is
one-Lipschitz on the source's `[-1,1]` cube. -/
theorem shiftedCoordinateEntropyGradient_lipschitzOn_unitInterval
    {first second : ℝ} (hfirst : first ∈ Set.Icc (-1 : ℝ) 1)
    (hsecond : second ∈ Set.Icc (-1 : ℝ) 1) :
    ‖(Real.log (first + 2) + 1) - (Real.log (second + 2) + 1)‖ ≤ ‖first - second‖ := by
  have hfirstShifted : 1 ≤ first + 2 := by linarith [hfirst.1]
  have hsecondShifted : 1 ≤ second + 2 := by linarith [hsecond.1]
  have hlog := norm_log_sub_le_norm_sub_of_one_le hfirstShifted hsecondShifted
  have hleft : (Real.log (first + 2) + 1) - (Real.log (second + 2) + 1) =
      Real.log (first + 2) - Real.log (second + 2) := by ring
  have hright : (first + 2) - (second + 2) = first - second := by ring
  rw [hleft]
  rw [hright] at hlog
  exact hlog

/-- On the shifted interval `[1,3]`, the logarithm has secant slope at least
`1 / 3`.  Written in the original coordinates, this is the scalar curvature
estimate for the shifted entropy regularizer. -/
theorem shiftedCoordinateEntropyGradient_secant_lower_on_unitInterval
    {lower upper : ℝ} (hlower : lower ∈ Set.Icc (-1 : ℝ) 1)
    (hupper : upper ∈ Set.Icc (-1 : ℝ) 1) (hordered : lower ≤ upper) :
    (1 / 3 : ℝ) * (upper - lower) ^ 2 ≤
      (Real.log (upper + 2) - Real.log (lower + 2)) * (upper - lower) := by
  have hlowerShiftedPos : 0 < lower + 2 := by linarith [hlower.1]
  have hupperShiftedPos : 0 < upper + 2 := by linarith [hupper.1]
  have hdifferenceNonneg : 0 ≤ upper - lower := sub_nonneg.mpr hordered
  have hratioPos : 0 < (upper + 2) / (lower + 2) :=
    div_pos hupperShiftedPos hlowerShiftedPos
  have hlogRatio := Real.one_sub_inv_le_log_of_pos hratioPos
  have hleft : 1 - ((upper + 2) / (lower + 2))⁻¹ =
      (upper - lower) / (upper + 2) := by
    field_simp [ne_of_gt hlowerShiftedPos, ne_of_gt hupperShiftedPos]
    ring
  have hright : Real.log ((upper + 2) / (lower + 2)) =
      Real.log (upper + 2) - Real.log (lower + 2) :=
    Real.log_div (ne_of_gt hupperShiftedPos) (ne_of_gt hlowerShiftedPos)
  rw [hleft, hright] at hlogRatio
  have hlogLower : (upper - lower) / 3 ≤
      Real.log (upper + 2) - Real.log (lower + 2) := by
    calc
      (upper - lower) / 3 ≤ (upper - lower) / (upper + 2) :=
        div_le_div_of_nonneg_left hdifferenceNonneg hupperShiftedPos (by linarith [hupper.2])
      _ ≤ Real.log (upper + 2) - Real.log (lower + 2) := hlogRatio
  calc
    (1 / 3 : ℝ) * (upper - lower) ^ 2 =
        ((upper - lower) / 3) * (upper - lower) := by ring
    _ ≤ (Real.log (upper + 2) - Real.log (lower + 2)) * (upper - lower) :=
      mul_le_mul_of_nonneg_right hlogLower hdifferenceNonneg

/-- The derivative of shifted coordinate entropy is `1 / 3` strongly
monotone on the source's unit interval.  The constant is sharp for the
endpoint `u=1`, where the shifted log derivative equals `1/3`. -/
theorem shiftedCoordinateEntropyGradient_strongMonotone_unitInterval
    {first second : ℝ} (hfirst : first ∈ Set.Icc (-1 : ℝ) 1)
    (hsecond : second ∈ Set.Icc (-1 : ℝ) 1) :
    (1 / 3 : ℝ) * (first - second) ^ 2 ≤
      ((Real.log (first + 2) + 1) - (Real.log (second + 2) + 1)) *
        (first - second) := by
  rcases le_total first second with hordered | hordered
  · have hsecant := shiftedCoordinateEntropyGradient_secant_lower_on_unitInterval
      hfirst hsecond hordered
    convert hsecant using 1 <;> ring
  · have hsecant := shiftedCoordinateEntropyGradient_secant_lower_on_unitInterval
      hsecond hfirst hordered
    convert hsecant using 1 <;> ring

/-- The shifted coordinate entropy is nonnegative on the unit interval. -/
theorem shiftedCoordinateEntropy_nonneg_on_unitInterval
    {value : ℝ} (hvalue : value ∈ Set.Icc (-1 : ℝ) 1) :
    0 ≤ shiftedCoordinateEntropy value := by
  unfold shiftedCoordinateEntropy
  have hshiftedLower : 1 ≤ value + 2 := by linarith [hvalue.1]
  exact mul_nonneg (by linarith) (Real.log_nonneg hshiftedLower)

/-- The shifted coordinate entropy is at most `3 log 3` on the unit
interval.  This is the correct endpoint value; omitting the factor three
would not bound the regularizer defined in Algorithm 6. -/
theorem shiftedCoordinateEntropy_le_three_mul_log_three_on_unitInterval
    {value : ℝ} (hvalue : value ∈ Set.Icc (-1 : ℝ) 1) :
    shiftedCoordinateEntropy value ≤ 3 * Real.log 3 := by
  unfold shiftedCoordinateEntropy
  have hshiftedLower : 1 ≤ value + 2 := by linarith [hvalue.1]
  have hshiftedUpper : value + 2 ≤ 3 := by linarith [hvalue.2]
  have hlogNonneg : 0 ≤ Real.log (value + 2) := Real.log_nonneg hshiftedLower
  have hlogUpper : Real.log (value + 2) ≤ Real.log 3 :=
    Real.log_le_log (by linarith) hshiftedUpper
  calc
    (value + 2) * Real.log (value + 2) ≤ 3 * Real.log (value + 2) :=
      mul_le_mul_of_nonneg_right hshiftedUpper hlogNonneg
    _ ≤ 3 * Real.log 3 := mul_le_mul_of_nonneg_left hlogUpper (by norm_num)

/-- A small rational upper bound for `log 3`, sufficient to recover the
source's advertised explicit FTRL constant after using the sharper direct
stability estimate. -/
theorem real_log_three_le_three_halves : Real.log 3 ≤ (3 / 2 : ℝ) := by
  have hthree : (3 : ℝ) = (3 / 2 : ℝ) * 2 := by norm_num
  calc
    Real.log 3 = Real.log ((3 / 2 : ℝ) * 2) := by rw [← hthree]
    _ = Real.log (3 / 2 : ℝ) + Real.log 2 := by
      rw [Real.log_mul (by norm_num) (by norm_num)]
    _ ≤ ((3 / 2 : ℝ) - 1) + (2 - 1) :=
      add_le_add (Real.log_le_sub_one_of_pos (by norm_num))
        (Real.log_le_sub_one_of_pos (by norm_num))
    _ = 3 / 2 := by norm_num
/-- First-order convexity of shifted coordinate entropy on the source's unit
cube.  This is the `a log a` tangent inequality after shifting both arguments
by two into the positive ray. -/
theorem shiftedCoordinateEntropy_tangent_lower_on_unitInterval
    {center candidate : ℝ} (hcenter : center ∈ Set.Icc (-1 : ℝ) 1)
    (hcandidate : candidate ∈ Set.Icc (-1 : ℝ) 1) :
    shiftedCoordinateEntropy candidate ≥ shiftedCoordinateEntropy center +
      (Real.log (center + 2) + 1) * (candidate - center) := by
  have hcandidateNonneg : 0 ≤ candidate + 2 := by linarith [hcandidate.1]
  have hcenterPos : 0 < center + 2 := by linarith [hcenter.1]
  have htangent := mass_sub_le_mul_log_mass_ratio hcandidateNonneg hcenterPos
  unfold shiftedCoordinateEntropy
  nlinarith

/-- Adding the ERM linear term preserves the exact first-order lower model.
The displayed slope is precisely the Algorithm 7 oracle weight. -/
theorem shiftedEntropyRegularizedCoordinateObjective_tangent_lower_on_unitInterval
    {linearWeight center candidate : ℝ}
    (hcenter : center ∈ Set.Icc (-1 : ℝ) 1)
    (hcandidate : candidate ∈ Set.Icc (-1 : ℝ) 1) :
    shiftedEntropyRegularizedCoordinateObjective linearWeight candidate ≥
      shiftedEntropyRegularizedCoordinateObjective linearWeight center +
        (linearWeight + Real.log (center + 2) + 1) * (candidate - center) := by
  have hentropy := shiftedCoordinateEntropy_tangent_lower_on_unitInterval hcenter hcandidate
  unfold shiftedEntropyRegularizedCoordinateObjective
  nlinarith

/-- The finite Euclidean cube containing the prediction vectors used in the
entropy-regularized ERM problem. -/
def finiteEuclideanUnitCube (Index : Type*) : Set (EuclideanSpace ℝ Index) :=
  {vector | ∀ coordinate, vector coordinate ∈ Set.Icc (-1 : ℝ) 1}

/-- The finite-dimensional gradient used in a shifted entropy-regularized ERM
problem.  If the linear weights are `-η z_i`, this is exactly Algorithm 7's
displayed ERM weight vector. -/
noncomputable def finiteShiftedEntropyRegularizedGradient
    {Index : Type*} (linearWeight : Index → ℝ) (vector : EuclideanSpace ℝ Index) :
    EuclideanSpace ℝ Index :=
  WithLp.toLp 2 (fun coordinate =>
    linearWeight coordinate + Real.log (vector coordinate + 2) + 1)

/--
The finite shifted-entropy gradient is measurable in any measurable state on
which both the linear weights and current coordinates are measurable.  This
is the analytic bridge needed when finite FTRL is used inside a stochastic
kernel rather than only as a deterministic optimizer.
-/
theorem measurable_finiteShiftedEntropyRegularizedGradient
    {State Index : Type*} [MeasurableSpace State]
    (linearWeight : Index → State → ℝ)
    (vector : State → EuclideanSpace ℝ Index)
    (hlinearWeight : ∀ coordinate, Measurable (linearWeight coordinate))
    (hvector : Measurable vector) :
    Measurable (fun state =>
      finiteShiftedEntropyRegularizedGradient
        (fun coordinate => linearWeight coordinate state) (vector state)) := by
  have hvectorPi : Measurable (fun state =>
      WithLp.ofLp (vector state) : State → (Index → ℝ)) :=
    (WithLp.measurable_ofLp 2 (Index → ℝ)).comp hvector
  apply (WithLp.measurable_toLp 2 (Index → ℝ)).comp
  apply measurable_pi_lambda
  intro coordinate
  have hcoordinate : Measurable (fun state => vector state coordinate) := by
    simpa using (measurable_pi_apply coordinate).comp hvectorPi
  simpa [finiteShiftedEntropyRegularizedGradient, add_assoc] using
    (hlinearWeight coordinate).add
      ((Real.measurable_log.comp (hcoordinate.add_const 2)).add_const 1)

/-- The finite entropy-regularized ERM objective over a vector of oracle
values.  Algorithm 7 uses `linearWeight i = -η z_i` for its accumulated
label weights. -/
noncomputable def finiteShiftedEntropyRegularizedObjective
    {Index : Type*} [Fintype Index] (linearWeight : Index → ℝ)
    (vector : EuclideanSpace ℝ Index) : ℝ :=
  ∑ coordinate,
    shiftedEntropyRegularizedCoordinateObjective (linearWeight coordinate) (vector coordinate)

/-- At every point of the unit cube, the explicit finite vector is the
gradient of the entropy-regularized ERM objective.  The proof differentiates
the finite coordinate sum directly, so no infinite-dimensional or attainment
assumption is hidden in the Frank--Wolfe specialization. -/
theorem finiteShiftedEntropyRegularizedObjective_hasGradientAt_on_unitCube
    {Index : Type*} [Fintype Index] (linearWeight : Index → ℝ)
    (vector : EuclideanSpace ℝ Index)
    (hvector : vector ∈ finiteEuclideanUnitCube Index) :
    HasGradientAt (finiteShiftedEntropyRegularizedObjective linearWeight)
      (finiteShiftedEntropyRegularizedGradient linearWeight vector) vector := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hsum : HasFDerivAt
      (fun other : EuclideanSpace ℝ Index => ∑ coordinate,
        shiftedEntropyRegularizedCoordinateObjective (linearWeight coordinate) (other coordinate))
      (∑ coordinate, (linearWeight coordinate + Real.log (vector coordinate + 2) + 1) •
        EuclideanSpace.proj (𝕜 := ℝ) coordinate) vector := by
    apply HasFDerivAt.fun_sum
    intro coordinate _
    have hcoordinate : vector coordinate + 2 ≠ 0 := by
      have : 0 < vector coordinate + 2 := by linarith [(hvector coordinate).1]
      exact ne_of_gt this
    have hscalar := shiftedEntropyRegularizedCoordinateObjective_hasDerivAt
      (linearWeight coordinate) (vector coordinate) hcoordinate
    have hevaluation : HasFDerivAt
        (fun other : EuclideanSpace ℝ Index => other coordinate)
        (EuclideanSpace.proj (𝕜 := ℝ) coordinate) vector := by
      exact PiLp.hasFDerivAt_apply 2 vector coordinate
    have hcomposition := HasDerivAt.comp_hasFDerivAt (x := vector)
      (hh := hscalar) (hf := hevaluation)
    simpa only [Function.comp_apply] using
      hcomposition
  convert hsum using 1
  ext direction
  have real_inner_eq_mul (first second : ℝ) : ⟪first, second⟫_ℝ = first * second := by
    change second * star first = first * second
    simp [mul_comm]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    InnerProductSpace.toDual_apply_apply, PiLp.inner_apply,
    finiteShiftedEntropyRegularizedGradient, real_inner_eq_mul,
    EuclideanSpace.coe_proj]
  apply Finset.sum_congr rfl
  intro coordinate _
  ring

/-- The finite shifted-entropy objective is continuous on the prediction cube.
The shift keeps every logarithm argument strictly positive there, so this is
also the compactness bridge used to obtain an exact constrained ERM point. -/
theorem finiteShiftedEntropyRegularizedObjective_continuousOn_unitCube
    {Index : Type*} [Fintype Index] (linearWeight : Index → ℝ) :
    ContinuousOn (finiteShiftedEntropyRegularizedObjective linearWeight)
      (finiteEuclideanUnitCube Index) := by
  intro vector hvector
  exact (finiteShiftedEntropyRegularizedObjective_hasGradientAt_on_unitCube
    linearWeight vector hvector).continuousAt.continuousWithinAt

/-- First-order convexity of the finite entropy-regularized ERM objective on
the unit cube.  Its right-hand linear term is the Euclidean inner product with
the explicit gradient supplied to Algorithm 7's ERM oracle. -/
theorem finiteShiftedEntropyRegularizedObjective_firstOrder_lower_on_unitCube
    {Index : Type*} [Fintype Index] (linearWeight : Index → ℝ)
    (center candidate : EuclideanSpace ℝ Index)
    (hcenter : center ∈ finiteEuclideanUnitCube Index)
    (hcandidate : candidate ∈ finiteEuclideanUnitCube Index) :
    finiteShiftedEntropyRegularizedObjective linearWeight candidate ≥
      finiteShiftedEntropyRegularizedObjective linearWeight center +
        ⟪finiteShiftedEntropyRegularizedGradient linearWeight center,
          candidate - center⟫_ℝ := by
  have hsum :
      (Finset.sum Finset.univ (fun coordinate =>
        shiftedEntropyRegularizedCoordinateObjective (linearWeight coordinate) (center coordinate) +
          (linearWeight coordinate + Real.log (center coordinate + 2) + 1) *
            (candidate coordinate - center coordinate))) ≤
      (Finset.sum Finset.univ (fun coordinate =>
          shiftedEntropyRegularizedCoordinateObjective (linearWeight coordinate) (candidate coordinate))) := by
    apply Finset.sum_le_sum
    intro coordinate _
    exact shiftedEntropyRegularizedCoordinateObjective_tangent_lower_on_unitInterval
      (hcenter coordinate) (hcandidate coordinate)
  rw [Finset.sum_add_distrib] at hsum
  unfold finiteShiftedEntropyRegularizedObjective
  rw [PiLp.inner_apply]
  have real_inner_eq_mul (first second : ℝ) : ⟪first, second⟫_ℝ = first * second := by
    change second * star first = first * second
    simp [mul_comm]
  simpa only [finiteShiftedEntropyRegularizedGradient, PiLp.sub_apply,
    real_inner_eq_mul] using hsum

/-- An exact constrained minimizer of the finite shifted-entropy objective
satisfies its variational first-order inequality.  This is the boundary-safe
bridge from Algorithm 6's literal `argmin` update to the two inequalities
needed by the FTRL stability proof. -/
theorem finiteShiftedEntropyRegularizedObjective_firstOrder_of_minimizer_on_convex
    {Index : Type*} [Fintype Index] (feasible : Set (EuclideanSpace ℝ Index))
    (hconvex : Convex ℝ feasible) (hsubset : feasible ⊆ finiteEuclideanUnitCube Index)
    (linearWeight : Index → ℝ) (minimizer candidate : EuclideanSpace ℝ Index)
    (hminimizer : IsMinOn (finiteShiftedEntropyRegularizedObjective linearWeight)
      feasible minimizer)
    (hminimizerMem : minimizer ∈ feasible)
    (hcandidate : candidate ∈ feasible) :
    0 ≤ ⟪finiteShiftedEntropyRegularizedGradient linearWeight minimizer,
      candidate - minimizer⟫_ℝ := by
  have hgradient := finiteShiftedEntropyRegularizedObjective_hasGradientAt_on_unitCube
    linearWeight minimizer (hsubset hminimizerMem)
  rw [hasGradientAt_iff_hasFDerivAt] at hgradient
  have htangent : candidate - minimizer ∈ posTangentConeAt feasible minimizer := by
    exact sub_mem_posTangentConeAt_of_segment_subset
      (hconvex.segment_subset hminimizerMem hcandidate)
  have hnonneg := hminimizer.localize.hasFDerivWithinAt_nonneg
    hgradient.hasFDerivWithinAt htangent
  simpa only [InnerProductSpace.toDual_apply_apply] using hnonneg

/-- The shifted entropy gradient is one-Lipschitz on the finite unit cube.
The fixed linear term cancels between two gradient evaluations. -/
theorem finiteShiftedEntropyRegularizedGradient_lipschitzOn_unitCube
    {Index : Type*} [Fintype Index] (linearWeight : Index → ℝ)
    (first second : EuclideanSpace ℝ Index)
    (hfirst : first ∈ finiteEuclideanUnitCube Index)
    (hsecond : second ∈ finiteEuclideanUnitCube Index) :
    ‖finiteShiftedEntropyRegularizedGradient linearWeight first -
        finiteShiftedEntropyRegularizedGradient linearWeight second‖ ≤ ‖first - second‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_le_sum
  intro coordinate _
  have hcoordinate := shiftedCoordinateEntropyGradient_lipschitzOn_unitInterval
    (hfirst coordinate) (hsecond coordinate)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hcoordinate
  simp only [finiteShiftedEntropyRegularizedGradient, PiLp.sub_apply]
  have hsquare := (sq_le_sq).mpr hcoordinate
  nlinarith

/-- The finite shifted-entropy gradient is `1 / 3` strongly monotone on the
unit cube.  Linear ERM weights cancel, so this is a property of the actual
entropy regularizer used by Algorithm 6 as well as Algorithm 7. -/
theorem finiteShiftedEntropyRegularizedGradient_strongMonotone_on_unitCube
    {Index : Type*} [Fintype Index] (linearWeight : Index → ℝ)
    (first second : EuclideanSpace ℝ Index)
    (hfirst : first ∈ finiteEuclideanUnitCube Index)
    (hsecond : second ∈ finiteEuclideanUnitCube Index) :
    (1 / 3 : ℝ) * ‖first - second‖ ^ 2 ≤
      ⟪finiteShiftedEntropyRegularizedGradient linearWeight first -
          finiteShiftedEntropyRegularizedGradient linearWeight second,
        first - second⟫_ℝ := by
  rw [EuclideanSpace.real_norm_sq_eq, PiLp.inner_apply]
  have real_inner_eq_mul (left right : ℝ) : ⟪left, right⟫_ℝ = left * right := by
    change right * star left = left * right
    simp [mul_comm]
  simp only [finiteShiftedEntropyRegularizedGradient, PiLp.sub_apply,
    real_inner_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro coordinate _
  have hcoordinate := shiftedCoordinateEntropyGradient_strongMonotone_unitInterval
    (hfirst coordinate) (hsecond coordinate)
  convert hcoordinate using 1 <;> ring

/-- The finite shifted-entropy ERM objective has its one-third strong-convex
quadratic lower model on every convex feasible subset of the prediction cube.
The linear ERM term changes the gradient but not the curvature. -/
theorem finiteShiftedEntropyRegularizedObjective_strongLower_on_convex
    {Index : Type*} [Fintype Index] (linearWeight : Index → ℝ)
    (feasible : Set (EuclideanSpace ℝ Index))
    (hfeasible : Convex ℝ feasible) (hsubset : feasible ⊆ finiteEuclideanUnitCube Index)
    (center candidate : EuclideanSpace ℝ Index)
    (hcenter : center ∈ feasible) (hcandidate : candidate ∈ feasible) :
    finiteShiftedEntropyRegularizedObjective linearWeight candidate ≥
      finiteShiftedEntropyRegularizedObjective linearWeight center +
        ⟪finiteShiftedEntropyRegularizedGradient linearWeight center,
          candidate - center⟫_ℝ +
          (1 / 3 : ℝ) / 2 * ‖candidate - center‖ ^ 2 := by
  apply strong_lower_model_bound_on_convex_of_gradient_strongMonotone
    (finiteShiftedEntropyRegularizedObjective linearWeight)
    (finiteShiftedEntropyRegularizedGradient linearWeight) (1 / 3 : ℝ)
    feasible hfeasible
  · intro first hfirst second hsecond
    exact finiteShiftedEntropyRegularizedGradient_strongMonotone_on_unitCube
      linearWeight first second (hsubset hfirst) (hsubset hsecond)
  · intro point hpoint
    exact finiteShiftedEntropyRegularizedObjective_hasGradientAt_on_unitCube
      linearWeight point (hsubset hpoint)
  · exact hcenter
  · exact hcandidate

/-- The unweighted finite shifted-entropy regularizer is nonnegative on the
prediction cube. -/
theorem finiteShiftedEntropyRegularizer_nonneg_on_unitCube
    {Index : Type*} [Fintype Index] (vector : EuclideanSpace ℝ Index)
    (hvector : vector ∈ finiteEuclideanUnitCube Index) :
    0 ≤ finiteShiftedEntropyRegularizedObjective (fun _ => 0) vector := by
  unfold finiteShiftedEntropyRegularizedObjective
    shiftedEntropyRegularizedCoordinateObjective
  simp only [zero_mul, zero_add]
  apply Finset.sum_nonneg
  intro coordinate _
  exact shiftedCoordinateEntropy_nonneg_on_unitInterval (hvector coordinate)

/-- The finite shifted-entropy regularizer has range at most
`3 m log 3` on the prediction cube.  This endpoint is used in the corrected
explicit-constant FTRL regret calculation. -/
theorem finiteShiftedEntropyRegularizer_le_three_card_mul_log_three_on_unitCube
    {Index : Type*} [Fintype Index] (vector : EuclideanSpace ℝ Index)
    (hvector : vector ∈ finiteEuclideanUnitCube Index) :
    finiteShiftedEntropyRegularizedObjective (fun _ => 0) vector ≤
      3 * (Fintype.card Index : ℝ) * Real.log 3 := by
  unfold finiteShiftedEntropyRegularizedObjective
    shiftedEntropyRegularizedCoordinateObjective
  simp only [zero_mul, zero_add]
  calc
    ∑ coordinate, shiftedCoordinateEntropy (vector coordinate) ≤
        ∑ _ : Index, 3 * Real.log 3 := by
      apply Finset.sum_le_sum
      intro coordinate _
      exact shiftedCoordinateEntropy_le_three_mul_log_three_on_unitInterval
        (hvector coordinate)
    _ = 3 * (Fintype.card Index : ℝ) * Real.log 3 := by
      simp [mul_assoc, mul_left_comm, mul_comm]

/-- The finite Euclidean unit cube is convex. -/
theorem convex_finiteEuclideanUnitCube (Index : Type*) :
    Convex ℝ (finiteEuclideanUnitCube Index) := by
  rw [convex_iff_add_mem]
  intro first hfirst second hsecond firstWeight secondWeight hfirstWeight hsecondWeight hweights coordinate
  rcases hfirst coordinate with ⟨hfirstLower, hfirstUpper⟩
  rcases hsecond coordinate with ⟨hsecondLower, hsecondUpper⟩
  change (firstWeight : ℝ) * first coordinate + secondWeight * second coordinate ∈
    Set.Icc (-1 : ℝ) 1
  constructor <;> nlinarith

/-- The squared Euclidean diameter of the finite unit cube is at most four
times its dimension.  This is the `R² ≤ 4m` input in Algorithm 7's
Frank--Wolfe iteration bound. -/
theorem finiteEuclideanUnitCube_norm_sub_sq_le
    {Index : Type*} [Fintype Index]
    (first second : EuclideanSpace ℝ Index)
    (hfirst : first ∈ finiteEuclideanUnitCube Index)
    (hsecond : second ∈ finiteEuclideanUnitCube Index) :
    ‖first - second‖ ^ 2 ≤ 4 * (Fintype.card Index : ℝ) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    ∑ coordinate, ((first - second) coordinate) ^ 2 ≤ ∑ _ : Index, (4 : ℝ) := by
      apply Finset.sum_le_sum
      intro coordinate _
      rcases hfirst coordinate with ⟨hfirstLower, hfirstUpper⟩
      rcases hsecond coordinate with ⟨hsecondLower, hsecondUpper⟩
      change (first coordinate - second coordinate) ^ 2 ≤ 4
      nlinarith
    _ = 4 * (Fintype.card Index : ℝ) := by simp [mul_comm]

/-- A convex hull of vectors in the finite unit cube inherits the same
squared-diameter bound.  This is the precise geometry needed for the convex
hull of ERM-oracle outputs in Algorithm 7. -/
theorem convexHull_finiteEuclideanUnitCube_norm_sub_sq_le
    {Index : Type*} [Fintype Index] (base : Set (EuclideanSpace ℝ Index))
    (hbase : base ⊆ finiteEuclideanUnitCube Index)
    (first second : EuclideanSpace ℝ Index)
    (hfirst : first ∈ convexHull ℝ base) (hsecond : second ∈ convexHull ℝ base) :
    ‖first - second‖ ^ 2 ≤ 4 * (Fintype.card Index : ℝ) := by
  apply finiteEuclideanUnitCube_norm_sub_sq_le first second
  · exact (convexHull_min hbase (convex_finiteEuclideanUnitCube Index)) hfirst
  · exact (convexHull_min hbase (convex_finiteEuclideanUnitCube Index)) hsecond

/-- Scaled expected utility minus finite KL divergence from a reference PMF. -/
noncomputable def exponentialTiltObjective
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (reference candidate : PMF Outcome) (utility : Outcome → ℝ)
    (inverseTemperature : ℝ) : ℝ :=
  inverseTemperature * pmfExp candidate utility -
    finiteKLDivergence candidate reference

/--
The scaled entropy-regularized objective is log partition minus KL divergence
to the exponential tilt.  The reference full-support hypothesis makes every
log ratio in the finite real API well-defined.
-/
theorem exponentialTiltObjective_eq_logPartition_sub_kl
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (reference candidate : PMF Outcome) (utility : Outcome → ℝ)
    (inverseTemperature : ℝ) (hreference : PMFFullSupport reference) :
    exponentialTiltObjective reference candidate utility inverseTemperature =
      Real.log (Probability.finiteMGF reference utility inverseTemperature) -
        finiteKLDivergence candidate
          (exponentialTilt reference utility inverseTemperature) := by
  have hlog : ∀ outcome : Outcome,
      Real.log (exponentialTilt reference utility inverseTemperature outcome).toReal =
        Real.log (reference outcome).toReal + inverseTemperature * utility outcome -
          Real.log (Probability.finiteMGF reference utility inverseTemperature) := by
    intro outcome
    have hratio := exponentialTilt_log_ratio
      reference utility inverseTemperature hreference outcome
    linarith
  have hkl :
      finiteKLDivergence candidate
          (exponentialTilt reference utility inverseTemperature) =
        finiteKLDivergence candidate reference -
          inverseTemperature * pmfExp candidate utility +
            Real.log (Probability.finiteMGF reference utility inverseTemperature) := by
    unfold finiteKLDivergence pmfExp
    calc
      ∑ outcome : Outcome,
          (candidate outcome).toReal *
            (Real.log (candidate outcome).toReal -
              Real.log (exponentialTilt reference utility inverseTemperature outcome).toReal) =
          ∑ outcome : Outcome,
            (((candidate outcome).toReal *
              (Real.log (candidate outcome).toReal - Real.log (reference outcome).toReal) -
              inverseTemperature * ((candidate outcome).toReal * utility outcome)) +
              (candidate outcome).toReal *
                Real.log (Probability.finiteMGF reference utility inverseTemperature)) := by
              refine Finset.sum_congr rfl fun outcome _ => ?_
              rw [hlog outcome]
              ring
      _ =
          (∑ outcome : Outcome,
            (candidate outcome).toReal *
              (Real.log (candidate outcome).toReal - Real.log (reference outcome).toReal)) -
            inverseTemperature *
              (∑ outcome : Outcome, (candidate outcome).toReal * utility outcome) +
              (∑ outcome : Outcome, (candidate outcome).toReal) *
                Real.log (Probability.finiteMGF reference utility inverseTemperature) := by
              rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
                ← Finset.mul_sum, Finset.sum_mul]
      _ = finiteKLDivergence candidate reference -
          inverseTemperature * pmfExp candidate utility +
            Real.log (Probability.finiteMGF reference utility inverseTemperature) := by
              rw [pmfToRealSum]
              simp only [finiteKLDivergence, pmfExp]
              ring
  unfold exponentialTiltObjective
  rw [hkl]
  ring

/--
The exponential tilt maximizes the scaled entropy-regularized objective over
all finite candidate PMFs.
-/
theorem exponentialTiltObjective_le_at_exponentialTilt
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (reference candidate : PMF Outcome) (utility : Outcome → ℝ)
    (inverseTemperature : ℝ) (hreference : PMFFullSupport reference) :
    exponentialTiltObjective reference candidate utility inverseTemperature ≤
      exponentialTiltObjective reference
        (exponentialTilt reference utility inverseTemperature)
        utility inverseTemperature := by
  rw [exponentialTiltObjective_eq_logPartition_sub_kl
    reference candidate utility inverseTemperature hreference]
  rw [exponentialTiltObjective_eq_logPartition_sub_kl
    reference (exponentialTilt reference utility inverseTemperature)
    utility inverseTemperature hreference]
  rw [finiteKLDivergence_self]
  linarith [finiteKLDivergence_nonneg candidate
    (exponentialTilt reference utility inverseTemperature)
    (exponentialTilt_fullSupport reference utility inverseTemperature hreference)]

/--
Any PMF distinct from the exponential tilt has strictly smaller
entropy-regularized objective. The full-support reference hypothesis yields a
full-support tilt, so strict finite KL positivity applies.
-/
theorem exponentialTiltObjective_lt_at_exponentialTilt_of_ne
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (reference candidate : PMF Outcome) (utility : Outcome → ℝ)
    (inverseTemperature : ℝ) (hreference : PMFFullSupport reference)
    (hne : candidate ≠ exponentialTilt reference utility inverseTemperature) :
    exponentialTiltObjective reference candidate utility inverseTemperature <
      exponentialTiltObjective reference
        (exponentialTilt reference utility inverseTemperature) utility inverseTemperature := by
  rw [exponentialTiltObjective_eq_logPartition_sub_kl
    reference candidate utility inverseTemperature hreference]
  rw [exponentialTiltObjective_eq_logPartition_sub_kl
    reference (exponentialTilt reference utility inverseTemperature)
    utility inverseTemperature hreference]
  rw [finiteKLDivergence_self]
  have hpositive := finiteKLDivergence_pos_of_ne candidate
    (exponentialTilt reference utility inverseTemperature)
    (exponentialTilt_fullSupport reference utility inverseTemperature hreference) hne
  linarith

/--
Equality with the exponential tilt's entropy-regularized objective characterizes
the tilt itself among finite PMFs.
-/
theorem exponentialTiltObjective_eq_at_exponentialTilt_iff
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (reference candidate : PMF Outcome) (utility : Outcome → ℝ)
    (inverseTemperature : ℝ) (hreference : PMFFullSupport reference) :
    exponentialTiltObjective reference candidate utility inverseTemperature =
      exponentialTiltObjective reference
        (exponentialTilt reference utility inverseTemperature) utility inverseTemperature ↔
      candidate = exponentialTilt reference utility inverseTemperature := by
  constructor
  · intro heq
    by_contra hne
    have hlt := exponentialTiltObjective_lt_at_exponentialTilt_of_ne
      reference candidate utility inverseTemperature hreference hne
    linarith
  · intro heq
    subst candidate
    rfl

/--
The full-support exponential tilt is the unique global maximizer of the finite
entropy-regularized objective: any candidate maximizing over all PMFs equals
the tilt.
-/
theorem exponentialTiltObjective_globalMax_unique
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (reference candidate : PMF Outcome) (utility : Outcome → ℝ)
    (inverseTemperature : ℝ) (hreference : PMFFullSupport reference)
    (hmax : ∀ other : PMF Outcome,
      exponentialTiltObjective reference other utility inverseTemperature ≤
        exponentialTiltObjective reference candidate utility inverseTemperature) :
    candidate = exponentialTilt reference utility inverseTemperature := by
  apply (exponentialTiltObjective_eq_at_exponentialTilt_iff
    reference candidate utility inverseTemperature hreference).mp
  apply le_antisymm
  · exact exponentialTiltObjective_le_at_exponentialTilt
      reference candidate utility inverseTemperature hreference
  · exact hmax (exponentialTilt reference utility inverseTemperature)

/--
Exact KL three-point identity for an exponential mirror step.  It is the
finite-entropy specialization underlying the Bregman calculation used in
mirror-descent regret and stability arguments.

No bounded-score or step-size condition is needed for this algebraic identity;
those conditions enter only when its final two terms are further bounded.
-/
theorem finiteKLDivergence_exponentialTilt_three_point
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (reference target : PMF Outcome) (utility : Outcome → ℝ)
    (inverseTemperature : ℝ) (hreference : PMFFullSupport reference) :
    finiteKLDivergence target
        (exponentialTilt reference utility inverseTemperature) =
      finiteKLDivergence target reference +
        inverseTemperature *
          (pmfExp (exponentialTilt reference utility inverseTemperature) utility -
            pmfExp target utility) -
          finiteKLDivergence
            (exponentialTilt reference utility inverseTemperature) reference := by
  have htarget := exponentialTiltObjective_eq_logPartition_sub_kl
    reference target utility inverseTemperature hreference
  have htilt := exponentialTiltObjective_eq_logPartition_sub_kl
    reference (exponentialTilt reference utility inverseTemperature)
    utility inverseTemperature hreference
  rw [finiteKLDivergence_self] at htilt
  unfold exponentialTiltObjective at htarget htilt
  linarith

/--
For a positive inverse temperature, the exponential tilt maximizes expected
utility over the finite KL ball whose radius is its own attained divergence
from the reference PMF.  This is the finite primal bridge behind the
constrained-to-regularized correspondence: no optimizer certificate is
assumed, only the Gibbs three-point identity and KL nonnegativity.
-/
theorem exponentialTilt_utility_globalMax_at_attainedKL
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (reference : PMF Outcome) (utility : Outcome → ℝ) (inverseTemperature : ℝ)
    (hreference : PMFFullSupport reference) (hinverseTemperature : 0 < inverseTemperature) :
    ∀ target : PMF Outcome,
      finiteKLDivergence target reference ≤
        finiteKLDivergence (exponentialTilt reference utility inverseTemperature) reference →
        pmfExp target utility ≤
          pmfExp (exponentialTilt reference utility inverseTemperature) utility := by
  intro target hfeasible
  have hthree := finiteKLDivergence_exponentialTilt_three_point
    reference target utility inverseTemperature hreference
  have hnonneg := finiteKLDivergence_nonneg target
    (exponentialTilt reference utility inverseTemperature)
    (exponentialTilt_fullSupport reference utility inverseTemperature hreference)
  nlinarith

/--
At its attained KL radius, a positive-temperature exponential tilt is the
unique utility maximizer.  Thus, once a KL radius is realized along the Gibbs
curve, the corresponding constrained and regularized solutions coincide as
policies rather than merely sharing an objective value.
-/
theorem exponentialTilt_utility_globalMax_unique_at_attainedKL
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (reference target : PMF Outcome) (utility : Outcome → ℝ) (inverseTemperature : ℝ)
    (hreference : PMFFullSupport reference) (hinverseTemperature : 0 < inverseTemperature)
    (hfeasible : finiteKLDivergence target reference ≤
      finiteKLDivergence (exponentialTilt reference utility inverseTemperature) reference)
    (hscore : pmfExp target utility =
      pmfExp (exponentialTilt reference utility inverseTemperature) utility) :
    target = exponentialTilt reference utility inverseTemperature := by
  apply (finiteKLDivergence_eq_zero_iff target
    (exponentialTilt reference utility inverseTemperature)
    (exponentialTilt_fullSupport reference utility inverseTemperature hreference)).mp
  have hthree := finiteKLDivergence_exponentialTilt_three_point
    reference target utility inverseTemperature hreference
  have hnonneg := finiteKLDivergence_nonneg target
    (exponentialTilt reference utility inverseTemperature)
    (exponentialTilt_fullSupport reference utility inverseTemperature hreference)
  nlinarith

/--
For a positive inverse temperature, the exponential tilt globally maximizes
the unscaled expected-utility-minus-KL objective whose KL coefficient is the
reciprocal inverse temperature.  Together with
`exponentialTilt_utility_globalMax_at_attainedKL`, this gives the finite
positive-weight constrained/regularized correspondence along the Gibbs curve.
-/
theorem exponentialTilt_regularizedUtility_globalMax
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (reference : PMF Outcome) (utility : Outcome → ℝ) (inverseTemperature : ℝ)
    (hreference : PMFFullSupport reference) (hinverseTemperature : 0 < inverseTemperature) :
    ∀ target : PMF Outcome,
      pmfExp target utility - inverseTemperature⁻¹ * finiteKLDivergence target reference ≤
        pmfExp (exponentialTilt reference utility inverseTemperature) utility -
          inverseTemperature⁻¹ *
            finiteKLDivergence (exponentialTilt reference utility inverseTemperature) reference := by
  intro target
  have hmax := exponentialTiltObjective_le_at_exponentialTilt
    reference target utility inverseTemperature hreference
  unfold exponentialTiltObjective at hmax
  apply le_of_mul_le_mul_left ?_ hinverseTemperature
  convert hmax using 1 <;>
    field_simp [ne_of_gt hinverseTemperature]

/--
Finite entropy mirror-step bound from an explicit local Pinsker/stability
premise. The score range is kept pointwise in `[0,1]`; after a finite Pinsker
theorem supplies `hentropyStability`, this gives the `2 * stepSize^2` form
used in the NLHF Appendix-D argument.
-/
theorem finiteKLDivergence_exponentialTilt_mirror_bound_of_l1_stability
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (reference target : PMF Outcome) (utility : Outcome → ℝ)
    (stepSize : ℝ) (hreference : PMFFullSupport reference)
    (hstepSize : 0 ≤ stepSize)
    (hutility_nonneg : ∀ outcome, 0 ≤ utility outcome)
    (hutility_le_one : ∀ outcome, utility outcome ≤ 1)
    (hentropyStability :
      (1 / 2 : ℝ) *
          (FiniteDimensionalNorms.l1 (fun outcome =>
            (exponentialTilt reference utility stepSize outcome).toReal -
              (reference outcome).toReal)) ^ 2 ≤
        finiteKLDivergence (exponentialTilt reference utility stepSize) reference) :
    finiteKLDivergence target (exponentialTilt reference utility stepSize) ≤
      finiteKLDivergence target reference +
        stepSize * (pmfExp reference utility - pmfExp target utility) +
          2 * stepSize ^ 2 := by
  have hthree := finiteKLDivergence_exponentialTilt_three_point
    reference target utility stepSize hreference
  have hscore := pmfExp_sub_le_l1_mass_difference
    (exponentialTilt reference utility stepSize) reference utility
    hutility_nonneg hutility_le_one
  have hscore_scaled :
      stepSize *
          (pmfExp (exponentialTilt reference utility stepSize) utility -
            pmfExp reference utility) ≤
        stepSize * FiniteDimensionalNorms.l1 (fun outcome =>
          (exponentialTilt reference utility stepSize outcome).toReal -
            (reference outcome).toReal) :=
    mul_le_mul_of_nonneg_left hscore hstepSize
  nlinarith [sq_nonneg
    (FiniteDimensionalNorms.l1 (fun outcome =>
      (exponentialTilt reference utility stepSize outcome).toReal -
        (reference outcome).toReal) - stepSize)]

/--
Finite entropy mirror-step bound with the Pinsker premise discharged.  This
is the source's Appendix-D entropy strong-convexity step specialized to a
finite exponential update.
-/
theorem finiteKLDivergence_exponentialTilt_mirror_bound
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (reference target : PMF Outcome) (utility : Outcome → ℝ)
    (stepSize : ℝ) (hreference : PMFFullSupport reference)
    (hstepSize : 0 ≤ stepSize)
    (hutility_nonneg : ∀ outcome, 0 ≤ utility outcome)
    (hutility_le_one : ∀ outcome, utility outcome ≤ 1) :
    finiteKLDivergence target (exponentialTilt reference utility stepSize) ≤
      finiteKLDivergence target reference +
        stepSize * (pmfExp reference utility - pmfExp target utility) +
          2 * stepSize ^ 2 := by
  apply finiteKLDivergence_exponentialTilt_mirror_bound_of_l1_stability
    reference target utility stepSize hreference hstepSize hutility_nonneg hutility_le_one
  exact finitePinsker_l1_sq_le_finiteKLDivergence
    (exponentialTilt reference utility stepSize) reference hreference

end AppliedModelingLib

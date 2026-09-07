import AppliedModelingLib.Foundations.Math.RegularizedLeverage
import AppliedModelingLib.Foundations.Optimization.Argmax
import AppliedModelingLib.Learning.ReinforcementLearning.Preference.RewardAgnostic
import AppliedModelingLib.Learning.ReinforcementLearning.Preference.StageIndexedOccupancy
import Mathlib.Tactic

/-!
# Finite least-squares policy evaluation with optimism

This file implements the backward finite-horizon evaluator used by many
linear-MDP algorithms: a stagewise ridge covariance, least-squares Bellman
weight, elliptical bonus, double clipping, and policy expectation.  The data
model is deterministic because probability enters when one proves that a
randomly generated dataset has the required concentration properties.
-/

namespace AppliedModelingLib

namespace PreferenceRL

open FiniteDimensionalNorms Matrix
open scoped BigOperators

noncomputable section

/-- A finite batch of stage-indexed transition observations. -/
structure LinearPlanningDataset (Index State Action : Type*) where
  indices : Finset Index
  state : Index → ℕ → State
  action : Index → ℕ → Action
  nextState : Index → ℕ → State

/-- All deterministic inputs used by the finite least-squares planner. -/
structure LinearPlanningProblem
    (Index State Action Coordinate : Type*) where
  data : LinearPlanningDataset Index State Action
  feature : ℕ → State → Action → Coordinate → ℝ
  ridge : ℝ
  bonusScale : ℝ

/-- The observed feature vector at a given dataset row and stage. -/
def LinearPlanningProblem.sampleFeature
    {Index State Action Coordinate : Type*}
    (problem : LinearPlanningProblem Index State Action Coordinate)
    (time : ℕ) (index : Index) : Coordinate → ℝ :=
  problem.feature time (problem.data.state index time) (problem.data.action index time)

/-- The stagewise ridge covariance in least-squares planning. -/
def LinearPlanningProblem.covariance
    {Index State Action Coordinate : Type*}
    [Fintype Coordinate] [DecidableEq Coordinate]
    (problem : LinearPlanningProblem Index State Action Coordinate) (time : ℕ) :
    Matrix Coordinate Coordinate ℝ :=
  regularizedGram problem.ridge (problem.sampleFeature time) problem.data.indices

/-- The empirical Bellman-regression signal for a supplied next-stage value. -/
def LinearPlanningProblem.regressionSignal
    {Index State Action Coordinate : Type*}
    (problem : LinearPlanningProblem Index State Action Coordinate)
    (time : ℕ) (nextValue : State → ℝ) : Coordinate → ℝ :=
  ∑ index ∈ problem.data.indices,
    nextValue (problem.data.nextState index time) • problem.sampleFeature time index

/-- The feature-weighted empirical Bellman residual relative to a proposed
linear continuation parameter. -/
def LinearPlanningProblem.regressionResidual
    {Index State Action Coordinate : Type*}
    [Fintype Coordinate]
    (problem : LinearPlanningProblem Index State Action Coordinate)
    (time : ℕ) (nextValue : State → ℝ) (parameter : Coordinate → ℝ) :
    Coordinate → ℝ :=
  ∑ index ∈ problem.data.indices,
    (nextValue (problem.data.nextState index time) -
      dot (problem.sampleFeature time index) parameter) •
        problem.sampleFeature time index

/-- The stagewise ridge least-squares Bellman weight. -/
def LinearPlanningProblem.weight
    {Index State Action Coordinate : Type*}
    [Fintype Coordinate] [DecidableEq Coordinate]
    (problem : LinearPlanningProblem Index State Action Coordinate)
    (time : ℕ) (nextValue : State → ℝ) : Coordinate → ℝ :=
  Matrix.mulVec (problem.covariance time)⁻¹ (problem.regressionSignal time nextValue)

/-- A bounded continuation value and bounded sample features control the
Euclidean norm of the empirical regression signal. -/
theorem LinearPlanningProblem.regressionSignal_l2_le_card_mul
    {Index State Action Coordinate : Type*} [Fintype Coordinate]
    (problem : LinearPlanningProblem Index State Action Coordinate)
    (time : ℕ) (nextValue : State → ℝ) (valueRadius featureRadius : ℝ)
    (hvalueRadius : 0 ≤ valueRadius)
    (hvalue : ∀ state, |nextValue state| ≤ valueRadius)
    (hfeature : ∀ index ∈ problem.data.indices,
      l2 (problem.sampleFeature time index) ≤ featureRadius) :
    l2 (problem.regressionSignal time nextValue) ≤
      (problem.data.indices.card : ℝ) * valueRadius * featureRadius := by
  classical
  have htriangle : l2 (problem.regressionSignal time nextValue) ≤
      ∑ index ∈ problem.data.indices,
        l2 (fun coordinate ↦ nextValue (problem.data.nextState index time) *
          problem.sampleFeature time index coordinate) := by
    unfold LinearPlanningProblem.regressionSignal
    have heq :
        (∑ index ∈ problem.data.indices,
          nextValue (problem.data.nextState index time) •
            problem.sampleFeature time index) =
          (fun coordinate ↦ ∑ index ∈ problem.data.indices,
            nextValue (problem.data.nextState index time) *
              problem.sampleFeature time index coordinate) := by
      funext coordinate
      simp
    rw [heq]
    exact normL2_finset_sum_le problem.data.indices
      (fun index coordinate ↦
        nextValue (problem.data.nextState index time) *
          problem.sampleFeature time index coordinate)
  calc
    l2 (problem.regressionSignal time nextValue) ≤
        ∑ index ∈ problem.data.indices,
          l2 (fun coordinate ↦ nextValue (problem.data.nextState index time) *
            problem.sampleFeature time index coordinate) := htriangle
    _ ≤ ∑ _index ∈ problem.data.indices, valueRadius * featureRadius := by
      apply Finset.sum_le_sum
      intro index hindex
      rw [normL2_smul]
      exact mul_le_mul (hvalue _) (hfeature index hindex)
        (normL2_nonneg _) hvalueRadius
    _ = (problem.data.indices.card : ℝ) * valueRadius * featureRadius := by
      simp
      ring

/-- The ridge inverse turns the signal envelope into a corresponding bound on
the least-squares weight. -/
theorem LinearPlanningProblem.weight_l2_le_card_mul_div_ridge
    {Index State Action Coordinate : Type*}
    [Fintype Coordinate] [DecidableEq Coordinate]
    (problem : LinearPlanningProblem Index State Action Coordinate)
    (time : ℕ) (nextValue : State → ℝ) (valueRadius featureRadius : ℝ)
    (hridge : 0 < problem.ridge)
    (hvalueRadius : 0 ≤ valueRadius)
    (hvalue : ∀ state, |nextValue state| ≤ valueRadius)
    (hfeature : ∀ index ∈ problem.data.indices,
      l2 (problem.sampleFeature time index) ≤ featureRadius) :
    l2 (problem.weight time nextValue) ≤
      ((problem.data.indices.card : ℝ) * valueRadius * featureRadius) /
        problem.ridge := by
  have hsignal := problem.regressionSignal_l2_le_card_mul time nextValue
    valueRadius featureRadius hvalueRadius hvalue hfeature
  have hinverse := regularizedGram_inverse_mulVec_l2_le
    problem.ridge (problem.sampleFeature time) problem.data.indices
    (problem.regressionSignal time nextValue) hridge
  calc
    l2 (problem.weight time nextValue) ≤
        l2 (problem.regressionSignal time nextValue) / problem.ridge := by
      simpa [LinearPlanningProblem.weight, LinearPlanningProblem.covariance] using hinverse
    _ ≤ ((problem.data.indices.card : ℝ) * valueRadius * featureRadius) /
        problem.ridge := div_le_div_of_nonneg_right hsignal hridge.le

/-- The exact ridge normal-equation identity. -/
theorem LinearPlanningProblem.covariance_mulVec_weight_sub_parameter
    {Index State Action Coordinate : Type*}
    [Fintype Coordinate] [DecidableEq Coordinate]
    (problem : LinearPlanningProblem Index State Action Coordinate)
    (time : ℕ) (nextValue : State → ℝ) (parameter : Coordinate → ℝ)
    (hridge : 0 < problem.ridge) :
    Matrix.mulVec (problem.covariance time)
        (problem.weight time nextValue - parameter) =
      problem.regressionResidual time nextValue parameter - problem.ridge • parameter := by
  classical
  have hinvertible : IsUnit (problem.covariance time).det :=
    Matrix.isUnit_iff_isUnit_det (problem.covariance time) |>.mp
      (regularizedGram_posDef problem.ridge (problem.sampleFeature time)
        problem.data.indices hridge).isUnit
  have hweight : Matrix.mulVec (problem.covariance time)
      (problem.weight time nextValue) = problem.regressionSignal time nextValue := by
    unfold LinearPlanningProblem.weight
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hinvertible, Matrix.one_mulVec]
  rw [Matrix.mulVec_sub, hweight]
  unfold LinearPlanningProblem.covariance regularizedGram
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.sum_mulVec]
  unfold LinearPlanningProblem.regressionSignal LinearPlanningProblem.regressionResidual
  ext coordinate
  simp only [Finset.sum_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.vecMulVec_mulVec]
  simp [dot]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  simp only [dotProduct]
  ring

/-- Solving the ridge normal equation explicitly separates the centred
empirical residual from the ridge bias. -/
theorem LinearPlanningProblem.weight_sub_parameter_eq_inverse_mulVec
    {Index State Action Coordinate : Type*}
    [Fintype Coordinate] [DecidableEq Coordinate]
    (problem : LinearPlanningProblem Index State Action Coordinate)
    (time : ℕ) (nextValue : State → ℝ) (parameter : Coordinate → ℝ)
    (hridge : 0 < problem.ridge) :
    problem.weight time nextValue - parameter =
      Matrix.mulVec (problem.covariance time)⁻¹
        (problem.regressionResidual time nextValue parameter -
          problem.ridge • parameter) := by
  have hnormal := problem.covariance_mulVec_weight_sub_parameter
    time nextValue parameter hridge
  have hinvertible : IsUnit (problem.covariance time).det :=
    Matrix.isUnit_iff_isUnit_det (problem.covariance time) |>.mp
      (regularizedGram_posDef problem.ridge (problem.sampleFeature time)
        problem.data.indices hridge).isUnit
  calc
    problem.weight time nextValue - parameter =
        Matrix.mulVec (problem.covariance time)⁻¹
          (Matrix.mulVec (problem.covariance time)
            (problem.weight time nextValue - parameter)) := by
              rw [Matrix.mulVec_mulVec,
                Matrix.nonsing_inv_mul (problem.covariance time) hinvertible,
                Matrix.one_mulVec]
    _ = Matrix.mulVec (problem.covariance time)⁻¹
        (problem.regressionResidual time nextValue parameter -
          problem.ridge • parameter) := by rw [hnormal]

/-- A self-normalized empirical-residual radius plus the exact ridge bias
controls every query prediction.  This is the deterministic regression bridge
used after the probabilistic concentration lemmas in linear-MDP analyses. -/
theorem LinearPlanningProblem.abs_prediction_sub_le_width_mul_residualRadius_add_ridge
    {Index State Action Coordinate : Type*}
    [Fintype Coordinate] [DecidableEq Coordinate]
    (problem : LinearPlanningProblem Index State Action Coordinate)
    (time : ℕ) (nextValue : State → ℝ) (parameter query : Coordinate → ℝ)
    (hridge : 0 < problem.ridge) :
    |dot query (problem.weight time nextValue) - dot query parameter| ≤
      Real.sqrt (dot query
        (Matrix.mulVec (problem.covariance time)⁻¹ query)) *
        (Real.sqrt (dot (problem.regressionResidual time nextValue parameter)
            (Matrix.mulVec (problem.covariance time)⁻¹
              (problem.regressionResidual time nextValue parameter))) +
          Real.sqrt problem.ridge * l2 parameter) := by
  let covariance := problem.covariance time
  let residual := problem.regressionResidual time nextValue parameter
  have hcovariance : covariance.PosDef := by
    simpa [covariance, LinearPlanningProblem.covariance] using
      regularizedGram_posDef problem.ridge (problem.sampleFeature time)
        problem.data.indices hridge
  have hinverse : covariance⁻¹.PosSemidef := hcovariance.inv.posSemidef
  have hqueryResidual := posSemidef_abs_dotProduct_mulVec_le_sqrt_mul_sqrt
    hinverse query residual
  have hqueryParameter := posSemidef_abs_dotProduct_mulVec_le_sqrt_mul_sqrt
    hinverse query parameter
  have hridgeBias :
      problem.ridge * Real.sqrt (dot parameter (covariance⁻¹ *ᵥ parameter)) ≤
        Real.sqrt problem.ridge * l2 parameter := by
    simpa [covariance, LinearPlanningProblem.covariance] using
      regularizedGram_ridge_mul_sqrt_inverseQuadratic_le
        problem.ridge (problem.sampleFeature time) problem.data.indices
        parameter hridge
  have hleft :
      dot query (problem.weight time nextValue) - dot query parameter =
        dot query (problem.weight time nextValue - parameter) := by
    unfold dot
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  have hsolution := problem.weight_sub_parameter_eq_inverse_mulVec
    time nextValue parameter hridge
  rw [hleft, hsolution]
  have hsplit :
      dot query (covariance⁻¹ *ᵥ (residual - problem.ridge • parameter)) =
        dot query (covariance⁻¹ *ᵥ residual) -
          problem.ridge * dot query (covariance⁻¹ *ᵥ parameter) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul]
    unfold dot
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub,
      Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro coordinate _
    ring
  change |dot query (covariance⁻¹ *ᵥ (residual - problem.ridge • parameter))| ≤ _
  rw [hsplit]
  calc
    |dot query (covariance⁻¹ *ᵥ residual) -
        problem.ridge * dot query (covariance⁻¹ *ᵥ parameter)| ≤
        |dot query (covariance⁻¹ *ᵥ residual)| +
          |problem.ridge * dot query (covariance⁻¹ *ᵥ parameter)| :=
      abs_sub _ _
    _ = |dot query (covariance⁻¹ *ᵥ residual)| +
        problem.ridge * |dot query (covariance⁻¹ *ᵥ parameter)| := by
      rw [abs_mul, abs_of_pos hridge]
    _ ≤ Real.sqrt (dot query (covariance⁻¹ *ᵥ query)) *
          Real.sqrt (dot residual (covariance⁻¹ *ᵥ residual)) +
        problem.ridge *
          (Real.sqrt (dot query (covariance⁻¹ *ᵥ query)) *
            Real.sqrt (dot parameter (covariance⁻¹ *ᵥ parameter))) := by
      exact add_le_add hqueryResidual
        (mul_le_mul_of_nonneg_left hqueryParameter hridge.le)
    _ = Real.sqrt (dot query (covariance⁻¹ *ᵥ query)) *
        (Real.sqrt (dot residual (covariance⁻¹ *ᵥ residual)) +
          problem.ridge * Real.sqrt (dot parameter (covariance⁻¹ *ᵥ parameter))) := by
      ring
    _ ≤ Real.sqrt (dot query (covariance⁻¹ *ᵥ query)) *
        (Real.sqrt (dot residual (covariance⁻¹ *ᵥ residual)) +
          Real.sqrt problem.ridge * l2 parameter) := by
      exact mul_le_mul_of_nonneg_left (add_le_add_right hridgeBias _)
        (Real.sqrt_nonneg _)

/-- A query prediction error is bounded by inverse-covariance query width
times the covariance energy of the parameter error. -/
theorem LinearPlanningProblem.abs_prediction_sub_le_width_mul_errorEnergy
    {Index State Action Coordinate : Type*}
    [Fintype Coordinate] [DecidableEq Coordinate]
    (problem : LinearPlanningProblem Index State Action Coordinate)
    (time : ℕ) (nextValue : State → ℝ) (parameter query : Coordinate → ℝ)
    (hridge : 0 < problem.ridge) :
    |dot query (problem.weight time nextValue) - dot query parameter| ≤
      Real.sqrt (dot query (Matrix.mulVec (problem.covariance time)⁻¹ query)) *
        Real.sqrt (dot (problem.weight time nextValue - parameter)
          (Matrix.mulVec (problem.covariance time)
            (problem.weight time nextValue - parameter))) := by
  have hpos : (problem.covariance time).PosDef :=
    regularizedGram_posDef problem.ridge (problem.sampleFeature time)
      problem.data.indices hridge
  have hcs := posDef_abs_dotProduct_le_sqrt_inverse_mul_sqrt
    hpos query (problem.weight time nextValue - parameter)
  have hleft :
      dot query (problem.weight time nextValue) - dot query parameter =
        dot query (problem.weight time nextValue - parameter) := by
    unfold dot
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  rw [hleft]
  exact hcs

/-- The squared inverse-covariance feature width at one state-action pair. -/
def LinearPlanningProblem.widthSq
    {Index State Action Coordinate : Type*}
    [Fintype Coordinate] [DecidableEq Coordinate]
    (problem : LinearPlanningProblem Index State Action Coordinate)
    (time : ℕ) (state : State) (action : Action) : ℝ :=
  dot (problem.feature time state action)
    (Matrix.mulVec (problem.covariance time)⁻¹
      (problem.feature time state action))

/-- The capped elliptical bonus used by the optimistic evaluator. -/
def LinearPlanningProblem.bonus
    {Index State Action Coordinate : Type*}
    [Fintype Coordinate] [DecidableEq Coordinate]
    (problem : LinearPlanningProblem Index State Action Coordinate)
    (remaining time : ℕ) (state : State) (action : Action) : ℝ :=
  min (problem.bonusScale * Real.sqrt (problem.widthSq time state action))
    (2 * (remaining : ℝ))

/-- The exploration version of the bonus, capped by the remaining horizon. -/
def LinearPlanningProblem.explorationBonus
    {Index State Action Coordinate : Type*}
    [Fintype Coordinate] [DecidableEq Coordinate]
    (problem : LinearPlanningProblem Index State Action Coordinate)
    (remaining time : ℕ) (state : State) (action : Action) : ℝ :=
  min (problem.bonusScale * Real.sqrt (problem.widthSq time state action))
    (remaining : ℝ)

/-- Symmetric clipping to `[-radius, radius]`. -/
def linearPlanningClip (radius value : ℝ) : ℝ :=
  max (-radius) (min radius value)

/-- Symmetric clipping is nonexpansive. -/
theorem linearPlanningClip_abs_sub_le
    (radius first second : ℝ) :
    |linearPlanningClip radius first - linearPlanningClip radius second| ≤
      |first - second| := by
  have hlipschitz : LipschitzWith 1 (linearPlanningClip radius) := by
    simpa [linearPlanningClip] using
      ((LipschitzWith.id : LipschitzWith 1 (fun value : ℝ ↦ value)).const_min radius).const_max
        (-radius)
  have hdist := hlipschitz.dist_le_mul first second
  simpa [Real.dist_eq] using hdist

/-- Clipping to a nonnegative symmetric radius gives the advertised range. -/
theorem abs_linearPlanningClip_le (radius value : ℝ) (hradius : 0 ≤ radius) :
    |linearPlanningClip radius value| ≤ radius := by
  rw [abs_le]
  unfold linearPlanningClip
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

/-- Symmetric clipping is inert on its target interval. -/
theorem linearPlanningClip_eq_self
    {radius value : ℝ} (hvalue : |value| ≤ radius) :
    linearPlanningClip radius value = value := by
  rw [abs_le] at hvalue
  unfold linearPlanningClip
  rw [min_eq_right hvalue.2, max_eq_right hvalue.1]

/-- Clipping a prediction cannot leave it farther than the smaller of its
original error and the diameter of the symmetric target interval. -/
theorem abs_linearPlanningClip_sub_le_min_two
    (radius prediction target uncertainty : ℝ)
    (hradius : 0 ≤ radius) (htarget : |target| ≤ radius)
    (hprediction : |prediction - target| ≤ uncertainty) :
    |linearPlanningClip radius prediction - target| ≤
      min uncertainty (2 * radius) := by
  by_cases huncertainty : uncertainty ≤ 2 * radius
  · rw [min_eq_left huncertainty]
    calc
      |linearPlanningClip radius prediction - target| =
          |linearPlanningClip radius prediction - linearPlanningClip radius target| := by
            rw [linearPlanningClip_eq_self htarget]
      _ ≤ |prediction - target| :=
        linearPlanningClip_abs_sub_le radius prediction target
      _ ≤ uncertainty := hprediction
  · rw [min_eq_right (le_of_not_ge huncertainty)]
    have hclip := abs_linearPlanningClip_le radius prediction hradius
    rw [abs_le] at hclip htarget ⊢
    constructor <;> linarith

/-- Symmetric double clipping plus a capped uncertainty bonus is optimistic
and overshoots a target in `[-radius,radius]` by at most twice that bonus. -/
theorem linearPlanningDoubleClip_bounds
    (radius prediction target uncertainty : ℝ)
    (hradius : 0 ≤ radius) (huncertainty : 0 ≤ uncertainty)
    (htarget : |target| ≤ radius)
    (hprediction : |prediction - target| ≤ uncertainty) :
    target ≤
        linearPlanningClip radius
          (linearPlanningClip radius prediction + min uncertainty (2 * radius)) ∧
      linearPlanningClip radius
          (linearPlanningClip radius prediction + min uncertainty (2 * radius)) ≤
        target + 2 * min uncertainty (2 * radius) := by
  let bonus := min uncertainty (2 * radius)
  let inner := linearPlanningClip radius prediction
  have hbonus : 0 ≤ bonus := le_min huncertainty (mul_nonneg (by norm_num) hradius)
  have hinnerError : |inner - target| ≤ bonus := by
    exact abs_linearPlanningClip_sub_le_min_two radius prediction target uncertainty
      hradius htarget hprediction
  have hinnerLower : target ≤ inner + bonus := by
    rw [abs_le] at hinnerError
    linarith
  have hinnerUpper : inner + bonus ≤ target + 2 * bonus := by
    rw [abs_le] at hinnerError
    linarith
  have htargetBounds := abs_le.mp htarget
  constructor
  · unfold linearPlanningClip
    exact le_max_of_le_right (le_min htargetBounds.2 hinnerLower)
  · unfold linearPlanningClip
    apply max_le
    · linarith
    · exact (min_le_right radius (inner + bonus)).trans hinnerUpper

/-- Clipping to `[0, radius]`, as used by reward-free linear exploration. -/
def linearPlanningNonnegativeClip (radius value : ℝ) : ℝ :=
  max 0 (min radius value)

/-- Nonnegative clipping is nonexpansive. -/
theorem linearPlanningNonnegativeClip_abs_sub_le
    (radius first second : ℝ) :
    |linearPlanningNonnegativeClip radius first -
        linearPlanningNonnegativeClip radius second| ≤ |first - second| := by
  have hlipschitz : LipschitzWith 1 (linearPlanningNonnegativeClip radius) := by
    simpa [linearPlanningNonnegativeClip] using
      ((LipschitzWith.id : LipschitzWith 1 (fun value : ℝ ↦ value)).const_min radius).const_max 0
  have hdist := hlipschitz.dist_le_mul first second
  simpa [Real.dist_eq] using hdist

/-- The range of clipping to a nonnegative interval. -/
theorem linearPlanningNonnegativeClip_mem
    (radius value : ℝ) (hradius : 0 ≤ radius) :
    linearPlanningNonnegativeClip radius value ∈ Set.Icc 0 radius := by
  unfold linearPlanningNonnegativeClip
  constructor
  · exact le_max_left _ _
  · exact max_le hradius (min_le_left _ _)

/-- Clipping is inert on its target interval. -/
theorem linearPlanningNonnegativeClip_eq_self
    {radius value : ℝ} (hvalue : value ∈ Set.Icc 0 radius) :
    linearPlanningNonnegativeClip radius value = value := by
  unfold linearPlanningNonnegativeClip
  rw [min_eq_right hvalue.2, max_eq_right hvalue.1]

/-- If a prediction is within an uncapped uncertainty of a target in
`[0,radius]`, then clipping improves the error; capping the uncertainty by the
interval diameter remains valid. -/
theorem abs_linearPlanningNonnegativeClip_sub_le_min
    (radius prediction target uncertainty : ℝ)
    (hradius : 0 ≤ radius) (htarget : target ∈ Set.Icc 0 radius)
    (hprediction : |prediction - target| ≤ uncertainty) :
    |linearPlanningNonnegativeClip radius prediction - target| ≤
      min uncertainty radius := by
  by_cases huncertainty : uncertainty ≤ radius
  · rw [min_eq_left huncertainty]
    calc
      |linearPlanningNonnegativeClip radius prediction - target| =
          |linearPlanningNonnegativeClip radius prediction -
            linearPlanningNonnegativeClip radius target| := by
              rw [linearPlanningNonnegativeClip_eq_self htarget]
      _ ≤ |prediction - target| :=
        linearPlanningNonnegativeClip_abs_sub_le radius prediction target
      _ ≤ uncertainty := hprediction
  · rw [min_eq_right (le_of_not_ge huncertainty)]
    obtain ⟨hclipLower, hclipUpper⟩ :=
      linearPlanningNonnegativeClip_mem radius prediction hradius
    rw [abs_le]
    constructor <;> linarith [htarget.1, htarget.2]

/-- The optimistic double-clipping pattern: adding the capped uncertainty
after the first clip makes the final value optimistic, with at most twice the
bonus overshoot. -/
theorem linearPlanningNonnegativeDoubleClip_bounds
    (radius prediction target uncertainty : ℝ)
    (hradius : 0 ≤ radius) (huncertainty : 0 ≤ uncertainty)
    (htarget : target ∈ Set.Icc 0 radius)
    (hprediction : |prediction - target| ≤ uncertainty) :
    target ≤
        linearPlanningNonnegativeClip radius
          (linearPlanningNonnegativeClip radius prediction + min uncertainty radius) ∧
      linearPlanningNonnegativeClip radius
          (linearPlanningNonnegativeClip radius prediction + min uncertainty radius) ≤
        target + 2 * min uncertainty radius := by
  let bonus := min uncertainty radius
  let inner := linearPlanningNonnegativeClip radius prediction
  have hbonus : 0 ≤ bonus := le_min huncertainty hradius
  have hinnerError : |inner - target| ≤ bonus := by
    exact abs_linearPlanningNonnegativeClip_sub_le_min
      radius prediction target uncertainty hradius htarget hprediction
  have hinnerLower : target ≤ inner + bonus := by
    rw [abs_le] at hinnerError
    linarith
  have hinnerUpper : inner + bonus ≤ target + 2 * bonus := by
    rw [abs_le] at hinnerError
    linarith
  have htargetUpper : target ≤ radius := htarget.2
  have htargetNonneg : 0 ≤ target := htarget.1
  constructor
  · unfold linearPlanningNonnegativeClip
    exact le_max_of_le_right (le_min htargetUpper hinnerLower)
  · unfold linearPlanningNonnegativeClip
    apply max_le
    · linarith
    · exact (min_le_right radius (inner + bonus)).trans hinnerUpper

/-- A canonical maximizer of a real objective over a finite nonempty type. -/
noncomputable def finiteRealArgmax
    {Action : Type*} [Fintype Action] [Nonempty Action]
    (objective : Action → ℝ) : Action :=
  Classical.choose (Decision.exists_maximizingFinite objective)

/-- The canonical finite argmax attains the global maximum. -/
theorem finiteRealArgmax_maximizes
    {Action : Type*} [Fintype Action] [Nonempty Action]
    (objective : Action → ℝ) (action : Action) :
    objective action ≤ objective (finiteRealArgmax objective) :=
  Classical.choose_spec (Decision.exists_maximizingFinite objective) action

/-- The literal backward recursion: the first component is `V` and the second
is `Q`.  The recursion index is remaining horizon, while `time` is the
absolute stage used to read features, data, rewards, and policies. -/
def linearLeastSquaresPlanningResult
    {Index State Action Coordinate : Type*}
    [Fintype Action] [DecidableEq Action]
    [Fintype Coordinate] [DecidableEq Coordinate]
    (problem : LinearPlanningProblem Index State Action Coordinate)
    (policy : StageIndexedPolicy State Action)
    (reward : StageIndexedReward State Action) :
    ℕ → ℕ → (State → ℝ) × (State → Action → ℝ)
  | 0, _time => (fun _state ↦ 0, fun _state _action ↦ 0)
  | remaining + 1, time =>
      let nextValue := (linearLeastSquaresPlanningResult problem policy reward remaining (time + 1)).1
      let weight := problem.weight time nextValue
      let actionValue := fun state action ↦
        linearPlanningClip (remaining + 1 : ℝ)
          (linearPlanningClip (remaining + 1 : ℝ)
              (dot (problem.feature time state action) weight + reward time state action) +
            problem.bonus (remaining + 1) time state action)
      let stateValue := fun state ↦ pmfExp (policy time state) (actionValue state)
      (stateValue, actionValue)

/-- The literal optimistic backward recursion used for reward-free linear
exploration.  Its artificial reward is the capped bonus divided by the full
horizon, and its state value is attained by a finite greedy action. -/
def linearUCBExplorationResult
    {Index State Action Coordinate : Type*}
    [Fintype Action] [Nonempty Action]
    [Fintype Coordinate] [DecidableEq Coordinate]
    (problem : LinearPlanningProblem Index State Action Coordinate)
    (horizon : ℕ) :
    ℕ → ℕ → (State → ℝ) × (State → Action → ℝ)
  | 0, _time => (fun _state ↦ 0, fun _state _action ↦ 0)
  | remaining + 1, time =>
      let nextValue := (linearUCBExplorationResult problem horizon remaining (time + 1)).1
      let weight := problem.weight time nextValue
      let bonus := problem.explorationBonus (remaining + 1) time
      let actionValue := fun state action ↦
        linearPlanningNonnegativeClip (remaining + 1 : ℝ)
          (linearPlanningNonnegativeClip (remaining + 1 : ℝ)
              (dot (problem.feature time state action) weight +
                bonus state action / (horizon : ℝ)) +
            bonus state action)
      let stateValue := fun state ↦
        actionValue state (finiteRealArgmax (actionValue state))
      (stateValue, actionValue)

/-- The state-value component of optimistic reward-free exploration. -/
def linearUCBExplorationValue
    {Index State Action Coordinate : Type*}
    [Fintype Action] [Nonempty Action]
    [Fintype Coordinate] [DecidableEq Coordinate]
    (problem : LinearPlanningProblem Index State Action Coordinate)
    (horizon remaining time : ℕ) (state : State) : ℝ :=
  (linearUCBExplorationResult problem horizon remaining time).1 state

/-- The Q-value component of optimistic reward-free exploration. -/
def linearUCBExplorationQ
    {Index State Action Coordinate : Type*}
    [Fintype Action] [Nonempty Action]
    [Fintype Coordinate] [DecidableEq Coordinate]
    (problem : LinearPlanningProblem Index State Action Coordinate)
    (horizon remaining time : ℕ) (state : State) (action : Action) : ℝ :=
  (linearUCBExplorationResult problem horizon remaining time).2 state action

/-- Algorithm 4's greedy action at one state and stage. -/
def linearUCBExplorationAction
    {Index State Action Coordinate : Type*}
    [Fintype Action] [Nonempty Action]
    [Fintype Coordinate] [DecidableEq Coordinate]
    (problem : LinearPlanningProblem Index State Action Coordinate)
    (horizon remaining time : ℕ) (state : State) : Action :=
  finiteRealArgmax (linearUCBExplorationQ problem horizon remaining time state)

@[simp] theorem linearUCBExplorationValue_zero
    {Index State Action Coordinate : Type*}
    [Fintype Action] [Nonempty Action]
    [Fintype Coordinate] [DecidableEq Coordinate]
    (problem : LinearPlanningProblem Index State Action Coordinate)
    (horizon time : ℕ) (state : State) :
    linearUCBExplorationValue problem horizon 0 time state = 0 := by
  rfl

@[simp] theorem linearUCBExplorationQ_zero
    {Index State Action Coordinate : Type*}
    [Fintype Action] [Nonempty Action]
    [Fintype Coordinate] [DecidableEq Coordinate]
    (problem : LinearPlanningProblem Index State Action Coordinate)
    (horizon time : ℕ) (state : State) (action : Action) :
    linearUCBExplorationQ problem horizon 0 time state action = 0 := by
  rfl

theorem linearUCBExplorationQ_succ
    {Index State Action Coordinate : Type*}
    [Fintype Action] [Nonempty Action]
    [Fintype Coordinate] [DecidableEq Coordinate]
    (problem : LinearPlanningProblem Index State Action Coordinate)
    (horizon remaining time : ℕ) (state : State) (action : Action) :
    linearUCBExplorationQ problem horizon (remaining + 1) time state action =
      linearPlanningNonnegativeClip (remaining + 1 : ℝ)
        (linearPlanningNonnegativeClip (remaining + 1 : ℝ)
            (dot (problem.feature time state action)
                (problem.weight time
                  (linearUCBExplorationValue problem horizon remaining (time + 1))) +
              problem.explorationBonus (remaining + 1) time state action / (horizon : ℝ)) +
          problem.explorationBonus (remaining + 1) time state action) := by
  rfl

theorem linearUCBExplorationValue_succ
    {Index State Action Coordinate : Type*}
    [Fintype Action] [Nonempty Action]
    [Fintype Coordinate] [DecidableEq Coordinate]
    (problem : LinearPlanningProblem Index State Action Coordinate)
    (horizon remaining time : ℕ) (state : State) :
    linearUCBExplorationValue problem horizon (remaining + 1) time state =
      linearUCBExplorationQ problem horizon (remaining + 1) time state
        (linearUCBExplorationAction problem horizon (remaining + 1) time state) := by
  rfl

/-- The selected exploration action globally maximizes the current Q-value. -/
theorem linearUCBExplorationAction_maximizes
    {Index State Action Coordinate : Type*}
    [Fintype Action] [Nonempty Action]
    [Fintype Coordinate] [DecidableEq Coordinate]
    (problem : LinearPlanningProblem Index State Action Coordinate)
    (horizon remaining time : ℕ) (state : State) (action : Action) :
    linearUCBExplorationQ problem horizon remaining time state action ≤
      linearUCBExplorationQ problem horizon remaining time state
        (linearUCBExplorationAction problem horizon remaining time state) :=
  finiteRealArgmax_maximizes _ action

/-- The optimistic exploration Q-values lie in `[0, remaining]`. -/
theorem linearUCBExplorationQ_mem
    {Index State Action Coordinate : Type*}
    [Fintype Action] [Nonempty Action]
    [Fintype Coordinate] [DecidableEq Coordinate]
    (problem : LinearPlanningProblem Index State Action Coordinate)
    (horizon remaining time : ℕ) (state : State) (action : Action) :
    linearUCBExplorationQ problem horizon remaining time state action ∈
      Set.Icc 0 (remaining : ℝ) := by
  cases remaining with
  | zero => simp
  | succ remaining =>
      rw [linearUCBExplorationQ_succ]
      simpa [Nat.cast_add, Nat.cast_one] using
        linearPlanningNonnegativeClip_mem (remaining + 1 : ℝ) _ (by positivity)

/-- The greedy exploration state values lie in `[0, remaining]`. -/
theorem linearUCBExplorationValue_mem
    {Index State Action Coordinate : Type*}
    [Fintype Action] [Nonempty Action]
    [Fintype Coordinate] [DecidableEq Coordinate]
    (problem : LinearPlanningProblem Index State Action Coordinate)
    (horizon remaining time : ℕ) (state : State) :
    linearUCBExplorationValue problem horizon remaining time state ∈
      Set.Icc 0 (remaining : ℝ) := by
  cases remaining with
  | zero => simp
  | succ remaining =>
      rw [linearUCBExplorationValue_succ]
      exact linearUCBExplorationQ_mem problem horizon (remaining + 1) time state _

/-- The state-value component returned by the planner. -/
def linearLeastSquaresPlanningValue
    {Index State Action Coordinate : Type*}
    [Fintype Action] [DecidableEq Action]
    [Fintype Coordinate] [DecidableEq Coordinate]
    (problem : LinearPlanningProblem Index State Action Coordinate)
    (policy : StageIndexedPolicy State Action)
    (reward : StageIndexedReward State Action)
    (remaining time : ℕ) (state : State) : ℝ :=
  (linearLeastSquaresPlanningResult problem policy reward remaining time).1 state

/-- The action-value component returned by the planner. -/
def linearLeastSquaresPlanningQ
    {Index State Action Coordinate : Type*}
    [Fintype Action] [DecidableEq Action]
    [Fintype Coordinate] [DecidableEq Coordinate]
    (problem : LinearPlanningProblem Index State Action Coordinate)
    (policy : StageIndexedPolicy State Action)
    (reward : StageIndexedReward State Action)
    (remaining time : ℕ) (state : State) (action : Action) : ℝ :=
  (linearLeastSquaresPlanningResult problem policy reward remaining time).2 state action

@[simp] theorem linearLeastSquaresPlanningValue_zero
    {Index State Action Coordinate : Type*}
    [Fintype Action] [DecidableEq Action]
    [Fintype Coordinate] [DecidableEq Coordinate]
    (problem : LinearPlanningProblem Index State Action Coordinate)
    (policy : StageIndexedPolicy State Action)
    (reward : StageIndexedReward State Action) (time : ℕ) (state : State) :
    linearLeastSquaresPlanningValue problem policy reward 0 time state = 0 := by
  rfl

@[simp] theorem linearLeastSquaresPlanningQ_zero
    {Index State Action Coordinate : Type*}
    [Fintype Action] [DecidableEq Action]
    [Fintype Coordinate] [DecidableEq Coordinate]
    (problem : LinearPlanningProblem Index State Action Coordinate)
    (policy : StageIndexedPolicy State Action)
    (reward : StageIndexedReward State Action) (time : ℕ) (state : State) (action : Action) :
    linearLeastSquaresPlanningQ problem policy reward 0 time state action = 0 := by
  rfl

theorem linearLeastSquaresPlanningQ_succ
    {Index State Action Coordinate : Type*}
    [Fintype Action] [DecidableEq Action]
    [Fintype Coordinate] [DecidableEq Coordinate]
    (problem : LinearPlanningProblem Index State Action Coordinate)
    (policy : StageIndexedPolicy State Action)
    (reward : StageIndexedReward State Action)
    (remaining time : ℕ) (state : State) (action : Action) :
    linearLeastSquaresPlanningQ problem policy reward (remaining + 1) time state action =
      linearPlanningClip (remaining + 1 : ℝ)
        (linearPlanningClip (remaining + 1 : ℝ)
            (dot (problem.feature time state action)
                (problem.weight time
                  (linearLeastSquaresPlanningValue problem policy reward remaining (time + 1))) +
              reward time state action) +
          problem.bonus (remaining + 1) time state action) := by
  rfl

/-- A one-step prediction interval implies the optimistic Bellman sandwich
for the literal double-clipped least-squares planner. -/
theorem linearLeastSquaresPlanningQ_succ_bounds_of_prediction
    {Index State Action Coordinate : Type*}
    [Fintype Action] [DecidableEq Action]
    [Fintype Coordinate] [DecidableEq Coordinate]
    (problem : LinearPlanningProblem Index State Action Coordinate)
    (policy : StageIndexedPolicy State Action)
    (reward : StageIndexedReward State Action)
    (remaining time : ℕ) (state : State) (action : Action)
    (target : ℝ)
    (hbonusScale : 0 ≤ problem.bonusScale)
    (htarget : |target| ≤ (remaining + 1 : ℝ))
    (hprediction :
      |dot (problem.feature time state action)
          (problem.weight time
            (linearLeastSquaresPlanningValue problem policy reward remaining (time + 1))) +
          reward time state action - target| ≤
        problem.bonusScale * Real.sqrt (problem.widthSq time state action)) :
    target ≤
        linearLeastSquaresPlanningQ problem policy reward (remaining + 1) time state action ∧
      linearLeastSquaresPlanningQ problem policy reward (remaining + 1) time state action ≤
        target + 2 * problem.bonus (remaining + 1) time state action := by
  rw [linearLeastSquaresPlanningQ_succ]
  simpa [LinearPlanningProblem.bonus] using
    linearPlanningDoubleClip_bounds (remaining + 1 : ℝ)
      (dot (problem.feature time state action)
          (problem.weight time
            (linearLeastSquaresPlanningValue problem policy reward remaining (time + 1))) +
        reward time state action)
      target
      (problem.bonusScale * Real.sqrt (problem.widthSq time state action))
      (by positivity)
      (mul_nonneg hbonusScale (Real.sqrt_nonneg _)) htarget hprediction

theorem linearLeastSquaresPlanningValue_succ
    {Index State Action Coordinate : Type*}
    [Fintype Action] [DecidableEq Action]
    [Fintype Coordinate] [DecidableEq Coordinate]
    (problem : LinearPlanningProblem Index State Action Coordinate)
    (policy : StageIndexedPolicy State Action)
    (reward : StageIndexedReward State Action)
    (remaining time : ℕ) (state : State) :
    linearLeastSquaresPlanningValue problem policy reward (remaining + 1) time state =
      pmfExp (policy time state)
        (linearLeastSquaresPlanningQ problem policy reward (remaining + 1) time state) := by
  rfl

/-- Every Q-value returned by the double-clipped planner lies in the source's
stage-dependent range. -/
theorem abs_linearLeastSquaresPlanningQ_le
    {Index State Action Coordinate : Type*}
    [Fintype Action] [DecidableEq Action]
    [Fintype Coordinate] [DecidableEq Coordinate]
    (problem : LinearPlanningProblem Index State Action Coordinate)
    (policy : StageIndexedPolicy State Action)
    (reward : StageIndexedReward State Action)
    (remaining time : ℕ) (state : State) (action : Action) :
    |linearLeastSquaresPlanningQ problem policy reward remaining time state action| ≤
      remaining := by
  cases remaining with
  | zero => simp
  | succ remaining =>
      rw [linearLeastSquaresPlanningQ_succ]
      simpa [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using
        (abs_linearPlanningClip_le (remaining + 1 : ℝ) _ (by positivity))

/-- Every policy expectation returned by the planner lies in the same range. -/
theorem abs_linearLeastSquaresPlanningValue_le
    {Index State Action Coordinate : Type*}
    [Fintype Action] [DecidableEq Action]
    [Fintype Coordinate] [DecidableEq Coordinate]
    (problem : LinearPlanningProblem Index State Action Coordinate)
    (policy : StageIndexedPolicy State Action)
    (reward : StageIndexedReward State Action)
    (remaining time : ℕ) (state : State) :
    |linearLeastSquaresPlanningValue problem policy reward remaining time state| ≤
      remaining := by
  cases remaining with
  | zero => simp
  | succ remaining =>
      rw [linearLeastSquaresPlanningValue_succ]
      exact abs_pmfExp_le_of_forall_abs_le _ _ _ fun action ↦
        abs_linearLeastSquaresPlanningQ_le problem policy reward _ time state action

/-- Expanding the two regression weights turns their query prediction
difference into the samplewise cross-leverage sum used in Lemma 11. -/
theorem LinearPlanningProblem.dot_weight_sub_eq_sum_crossLeverage
    {Index State Action Coordinate : Type*}
    [Fintype Coordinate] [DecidableEq Coordinate]
    (problem : LinearPlanningProblem Index State Action Coordinate)
    (time : ℕ) (query : Coordinate → ℝ) (first second : State → ℝ) :
    dot query (problem.weight time first - problem.weight time second) =
      ∑ index ∈ problem.data.indices,
        dot query
            (Matrix.mulVec (problem.covariance time)⁻¹ (problem.sampleFeature time index)) *
          (first (problem.data.nextState index time) -
            second (problem.data.nextState index time)) := by
  classical
  unfold LinearPlanningProblem.weight LinearPlanningProblem.regressionSignal dot
  rw [← Matrix.mulVec_sub]
  have hsignal :
      (∑ index ∈ problem.data.indices,
          first (problem.data.nextState index time) • problem.sampleFeature time index) -
        ∑ index ∈ problem.data.indices,
          second (problem.data.nextState index time) • problem.sampleFeature time index =
      ∑ index ∈ problem.data.indices,
        (first (problem.data.nextState index time) -
          second (problem.data.nextState index time)) • problem.sampleFeature time index := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro index _
    ext coordinate
    simp
    ring
  rw [hsignal, Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc
    (∑ coordinate, query coordinate *
        ∑ index ∈ problem.data.indices,
          (first (problem.data.nextState index time) -
              second (problem.data.nextState index time)) *
            ((problem.covariance time)⁻¹ *ᵥ problem.sampleFeature time index) coordinate) =
      ∑ coordinate, ∑ index ∈ problem.data.indices,
        query coordinate *
          ((first (problem.data.nextState index time) -
              second (problem.data.nextState index time)) *
            ((problem.covariance time)⁻¹ *ᵥ problem.sampleFeature time index) coordinate) := by
        apply Finset.sum_congr rfl
        intro coordinate _
        rw [Finset.mul_sum]
    _ = ∑ index ∈ problem.data.indices, ∑ coordinate,
        query coordinate *
          ((first (problem.data.nextState index time) -
              second (problem.data.nextState index time)) *
            ((problem.covariance time)⁻¹ *ᵥ problem.sampleFeature time index) coordinate) := by
        rw [Finset.sum_comm]
    _ = ∑ index ∈ problem.data.indices,
        (∑ coordinate, query coordinate *
          ((problem.covariance time)⁻¹ *ᵥ problem.sampleFeature time index) coordinate) *
          (first (problem.data.nextState index time) -
            second (problem.data.nextState index time)) := by
        apply Finset.sum_congr rfl
        intro index _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro coordinate _
        ring

/-- Uniform control of the sample continuation values transfers to a query
prediction through the total absolute cross leverage. -/
theorem LinearPlanningProblem.abs_dot_weight_sub_le_crossLeverage
    {Index State Action Coordinate : Type*}
    [Fintype Coordinate] [DecidableEq Coordinate]
    (problem : LinearPlanningProblem Index State Action Coordinate)
    (time : ℕ) (query : Coordinate → ℝ) (first second : State → ℝ)
    (error : ℝ)
    (hnext : ∀ index ∈ problem.data.indices,
      |first (problem.data.nextState index time) -
        second (problem.data.nextState index time)| ≤ error) :
    |dot query (problem.weight time first - problem.weight time second)| ≤
      error * ∑ index ∈ problem.data.indices,
        |dot query
          (Matrix.mulVec (problem.covariance time)⁻¹ (problem.sampleFeature time index))| := by
  classical
  rw [problem.dot_weight_sub_eq_sum_crossLeverage]
  calc
    |∑ index ∈ problem.data.indices,
        dot query
            (Matrix.mulVec (problem.covariance time)⁻¹ (problem.sampleFeature time index)) *
          (first (problem.data.nextState index time) -
            second (problem.data.nextState index time))| ≤
      ∑ index ∈ problem.data.indices,
        |dot query
            (Matrix.mulVec (problem.covariance time)⁻¹ (problem.sampleFeature time index)) *
          (first (problem.data.nextState index time) -
            second (problem.data.nextState index time))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ index ∈ problem.data.indices,
        |dot query
          (Matrix.mulVec (problem.covariance time)⁻¹ (problem.sampleFeature time index))| *
          |first (problem.data.nextState index time) -
            second (problem.data.nextState index time)| := by
      apply Finset.sum_congr rfl
      intro index _
      rw [abs_mul]
    _ ≤ ∑ index ∈ problem.data.indices,
        |dot query
          (Matrix.mulVec (problem.covariance time)⁻¹ (problem.sampleFeature time index))| *
          error := by
      apply Finset.sum_le_sum
      intro index hindex
      exact mul_le_mul_of_nonneg_left (hnext index hindex) (abs_nonneg _)
    _ = error * ∑ index ∈ problem.data.indices,
        |dot query
          (Matrix.mulVec (problem.covariance time)⁻¹ (problem.sampleFeature time index))| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro index _
      ring

/-- For two policies evaluated on the same data, reward, and bonus, their
current Q difference is controlled only by the next-value regression error.
Both clipping operations are treated literally. -/
theorem linearLeastSquaresPlanningQ_succ_abs_sub_le_crossLeverage
    {Index State Action Coordinate : Type*}
    [Fintype Action] [DecidableEq Action]
    [Fintype Coordinate] [DecidableEq Coordinate]
    (problem : LinearPlanningProblem Index State Action Coordinate)
    (firstPolicy secondPolicy : StageIndexedPolicy State Action)
    (reward : StageIndexedReward State Action)
    (remaining time : ℕ) (state : State) (action : Action)
    (error : ℝ)
    (hnext : ∀ index ∈ problem.data.indices,
      |linearLeastSquaresPlanningValue problem firstPolicy reward remaining (time + 1)
          (problem.data.nextState index time) -
        linearLeastSquaresPlanningValue problem secondPolicy reward remaining (time + 1)
          (problem.data.nextState index time)| ≤ error) :
    |linearLeastSquaresPlanningQ problem firstPolicy reward (remaining + 1) time state action -
        linearLeastSquaresPlanningQ problem secondPolicy reward (remaining + 1) time state action| ≤
      error * ∑ index ∈ problem.data.indices,
        |dot (problem.feature time state action)
          (Matrix.mulVec (problem.covariance time)⁻¹ (problem.sampleFeature time index))| := by
  let firstNext := linearLeastSquaresPlanningValue
    problem firstPolicy reward remaining (time + 1)
  let secondNext := linearLeastSquaresPlanningValue
    problem secondPolicy reward remaining (time + 1)
  let firstPrediction :=
    dot (problem.feature time state action) (problem.weight time firstNext) +
      reward time state action
  let secondPrediction :=
    dot (problem.feature time state action) (problem.weight time secondNext) +
      reward time state action
  have houter := linearPlanningClip_abs_sub_le (remaining + 1 : ℝ)
    (linearPlanningClip (remaining + 1 : ℝ) firstPrediction +
      problem.bonus (remaining + 1) time state action)
    (linearPlanningClip (remaining + 1 : ℝ) secondPrediction +
      problem.bonus (remaining + 1) time state action)
  have hinner := linearPlanningClip_abs_sub_le (remaining + 1 : ℝ)
    firstPrediction secondPrediction
  have hprediction :
      firstPrediction - secondPrediction =
        dot (problem.feature time state action)
          (problem.weight time firstNext - problem.weight time secondNext) := by
    dsimp [firstPrediction, secondPrediction]
    unfold dot
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    ring
  have hregression := problem.abs_dot_weight_sub_le_crossLeverage
    time (problem.feature time state action) firstNext secondNext error (by
      intro index hindex
      simpa [firstNext, secondNext] using hnext index hindex)
  rw [linearLeastSquaresPlanningQ_succ, linearLeastSquaresPlanningQ_succ]
  calc
    |linearPlanningClip (remaining + 1 : ℝ)
          (linearPlanningClip (remaining + 1 : ℝ) firstPrediction +
            problem.bonus (remaining + 1) time state action) -
        linearPlanningClip (remaining + 1 : ℝ)
          (linearPlanningClip (remaining + 1 : ℝ) secondPrediction +
            problem.bonus (remaining + 1) time state action)| ≤
      |linearPlanningClip (remaining + 1 : ℝ) firstPrediction -
        linearPlanningClip (remaining + 1 : ℝ) secondPrediction| := by
          simpa using houter
    _ ≤ |firstPrediction - secondPrediction| := hinner
    _ = |dot (problem.feature time state action)
          (problem.weight time firstNext - problem.weight time secondNext)| := by
      rw [hprediction]
    _ ≤ error * ∑ index ∈ problem.data.indices,
        |dot (problem.feature time state action)
          (Matrix.mulVec (problem.covariance time)⁻¹
            (problem.sampleFeature time index))| := hregression

/-- Two finite expectations may differ both because their integrands differ
and because their probability laws differ. -/
theorem abs_pmfExp_twoFunctions_sub_le_pointwise_add_l1
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (firstLaw secondLaw : PMF Outcome) (firstValue secondValue : Outcome → ℝ)
    (pointwiseBound valueBound : ℝ)
    (hpointwise : ∀ outcome,
      |firstValue outcome - secondValue outcome| ≤ pointwiseBound)
    (hvalue : ∀ outcome, |secondValue outcome| ≤ valueBound) :
    |pmfExp firstLaw firstValue - pmfExp secondLaw secondValue| ≤
      pointwiseBound + valueBound * pmfL1Error firstLaw secondLaw := by
  calc
    |pmfExp firstLaw firstValue - pmfExp secondLaw secondValue| =
        |(pmfExp firstLaw firstValue - pmfExp firstLaw secondValue) +
          (pmfExp firstLaw secondValue - pmfExp secondLaw secondValue)| := by ring_nf
    _ ≤ |pmfExp firstLaw firstValue - pmfExp firstLaw secondValue| +
        |pmfExp firstLaw secondValue - pmfExp secondLaw secondValue| := abs_add_le _ _
    _ ≤ pointwiseBound + valueBound * pmfL1Error firstLaw secondLaw :=
      add_le_add
        (by
          rw [← pmfExp_sub]
          exact abs_pmfExp_le_of_forall_abs_le firstLaw
            (fun outcome ↦ firstValue outcome - secondValue outcome)
            pointwiseBound hpointwise)
        (abs_pmfExp_sub_le_bound_mul_pmfL1Error
          firstLaw secondLaw secondValue valueBound hvalue)

/-- One backward planning step propagates a uniform next-value error through
the regression geometry and adds the policy-law perturbation. -/
theorem linearLeastSquaresPlanningValue_succ_abs_sub_le
    {Index State Action Coordinate : Type*}
    [Fintype Action] [DecidableEq Action]
    [Fintype Coordinate] [DecidableEq Coordinate]
    (problem : LinearPlanningProblem Index State Action Coordinate)
    (firstPolicy secondPolicy : StageIndexedPolicy State Action)
    (reward : StageIndexedReward State Action)
    (remaining time : ℕ) (state : State)
    (nextError amplification policyError : ℝ)
    (hnextError : 0 ≤ nextError)
    (hnext : ∀ index ∈ problem.data.indices,
      |linearLeastSquaresPlanningValue problem firstPolicy reward remaining (time + 1)
          (problem.data.nextState index time) -
        linearLeastSquaresPlanningValue problem secondPolicy reward remaining (time + 1)
          (problem.data.nextState index time)| ≤ nextError)
    (hcross : ∀ action,
      (∑ index ∈ problem.data.indices,
        |dot (problem.feature time state action)
          (Matrix.mulVec (problem.covariance time)⁻¹
            (problem.sampleFeature time index))|) ≤ amplification)
    (hpolicy : pmfL1Error (firstPolicy time state) (secondPolicy time state) ≤ policyError) :
    |linearLeastSquaresPlanningValue problem firstPolicy reward (remaining + 1) time state -
        linearLeastSquaresPlanningValue problem secondPolicy reward (remaining + 1) time state| ≤
      nextError * amplification + (remaining + 1 : ℝ) * policyError := by
  rw [linearLeastSquaresPlanningValue_succ, linearLeastSquaresPlanningValue_succ]
  apply (abs_pmfExp_twoFunctions_sub_le_pointwise_add_l1
    (firstPolicy time state) (secondPolicy time state)
    (linearLeastSquaresPlanningQ problem firstPolicy reward (remaining + 1) time state)
    (linearLeastSquaresPlanningQ problem secondPolicy reward (remaining + 1) time state)
    (nextError * amplification) (remaining + 1 : ℝ) ?_ ?_).trans
  · gcongr
  · intro action
    exact (linearLeastSquaresPlanningQ_succ_abs_sub_le_crossLeverage
      problem firstPolicy secondPolicy reward remaining time state action nextError hnext).trans
        (mul_le_mul_of_nonneg_left (hcross action) hnextError)
  · intro action
    simpa [Nat.cast_add, Nat.cast_one] using
      (abs_linearLeastSquaresPlanningQ_le
        problem secondPolicy reward (remaining + 1) time state action)

end

end PreferenceRL

end AppliedModelingLib

import Mathlib.Algebra.BigOperators.Ring.Finset
import AppliedModelingLib.Foundations.Optimization.SmoothStrongConvex
import Mathlib.Tactic

/-!
# Explicit conditional-gradient mixtures

This module records the finite convex-combination bookkeeping shared by
Frank--Wolfe / conditional-gradient algorithms.  A step replaces an old
mixture by `(1 - γ)` times that mixture plus a new oracle atom with weight
`γ`.  The update preserves nonnegative unit-sum weights and realizes exactly
the advertised affine combination.

The representation is intentionally independent of an optimization objective:
smoothness and linear-oracle arguments can use these invariants without
reimplementing the weight algebra.
-/

open scoped BigOperators InnerProductSpace

namespace AppliedModelingLib

/-- A finite vector of nonnegative weights summing to one. -/
def IsConvexCombinationWeights {count : ℕ} (weight : Fin count → ℝ) : Prop :=
  (∀ index, 0 ≤ weight index) ∧ ∑ index, weight index = 1

/-- Append a new conditional-gradient atom with step size `γ`, scaling every
existing atom by `1 - γ`. -/
def conditionalGradientWeights {count : ℕ} (weight : Fin count → ℝ) (step : ℝ) :
    Fin (count + 1) → ℝ :=
  Fin.snoc (fun index => (1 - step) * weight index) step

/-- One conditional-gradient update preserves nonnegative weights. -/
theorem conditionalGradientWeights_nonneg
    {count : ℕ} (weight : Fin count → ℝ) (step : ℝ)
    (hweight : ∀ index, 0 ≤ weight index) (hstepLower : 0 ≤ step)
    (hstepUpper : step ≤ 1) :
    ∀ index, 0 ≤ conditionalGradientWeights weight step index := by
  intro index
  refine Fin.lastCases ?_ (fun previous => ?_) index
  · simpa [conditionalGradientWeights] using hstepLower
  · simpa [conditionalGradientWeights] using
      mul_nonneg (sub_nonneg.mpr hstepUpper) (hweight previous)

/-- The weights after one conditional-gradient step still sum to one. -/
theorem sum_conditionalGradientWeights
    {count : ℕ} (weight : Fin count → ℝ) (step : ℝ)
    (hweight : ∑ index, weight index = 1) :
    ∑ index, conditionalGradientWeights weight step index = 1 := by
  rw [Fin.sum_univ_castSucc]
  simp only [conditionalGradientWeights, Fin.snoc_castSucc, Fin.snoc_last]
  rw [← Finset.mul_sum, hweight]
  ring

/-- One conditional-gradient step preserves the explicit convex-combination
certificate. -/
theorem isConvexCombinationWeights_conditionalGradientWeights
    {count : ℕ} (weight : Fin count → ℝ) (step : ℝ)
    (hweight : IsConvexCombinationWeights weight) (hstepLower : 0 ≤ step)
    (hstepUpper : step ≤ 1) :
    IsConvexCombinationWeights (conditionalGradientWeights weight step) := by
  constructor
  · exact conditionalGradientWeights_nonneg weight step hweight.1 hstepLower hstepUpper
  · exact sum_conditionalGradientWeights weight step hweight.2

/-- The value represented by a finite real-weighted mixture of atoms in an
arbitrary real module. -/
def conditionalGradientMixture {Value : Type*} [AddCommMonoid Value] [Module ℝ Value]
    {count : ℕ} (atom : Fin count → Value) (weight : Fin count → ℝ) : Value :=
  ∑ index, weight index • atom index

/-- Appending an oracle atom with conditional-gradient weights realizes the
usual update exactly. -/
theorem conditionalGradientMixture_update
    {Value : Type*} [AddCommMonoid Value] [Module ℝ Value]
    {count : ℕ} (atom : Fin count → Value) (weight : Fin count → ℝ)
    (oracleAtom : Value) (step : ℝ) :
    conditionalGradientMixture (Fin.snoc atom oracleAtom)
        (conditionalGradientWeights weight step) =
      (1 - step) • conditionalGradientMixture atom weight + step • oracleAtom := by
  unfold conditionalGradientMixture
  rw [Fin.sum_univ_castSucc]
  simp only [conditionalGradientWeights, Fin.snoc_castSucc, Fin.snoc_last]
  calc
    (∑ index, ((1 - step) * weight index) • atom index) + step • oracleAtom =
        (∑ index, (1 - step) • (weight index • atom index)) + step • oracleAtom := by
          apply congrArg (fun value => value + step • oracleAtom)
          apply Finset.sum_congr rfl
          intro index _
          rw [mul_smul]
    _ = (1 - step) • (∑ index, weight index • atom index) + step • oracleAtom := by
      rw [Finset.smul_sum]

/-- A finite mixture with nonnegative unit-sum coefficients belongs to the
convex hull of its listed atoms. -/
theorem conditionalGradientMixture_mem_convexHull
    {Value : Type*} [AddCommGroup Value] [Module ℝ Value]
    {count : ℕ} (atom : Fin count → Value) (weight : Fin count → ℝ)
    (hweight : IsConvexCombinationWeights weight) :
    conditionalGradientMixture atom weight ∈ convexHull ℝ (Set.range atom) := by
  unfold conditionalGradientMixture
  have hcenter :
      (Finset.univ : Finset (Fin count)).centerMass weight atom ∈
        convexHull ℝ (Set.range atom) := by
    apply Finset.centerMass_mem_convexHull
    · intro index _
      exact hweight.1 index
    · rw [hweight.2]
      norm_num
    · intro index _
      exact ⟨index, rfl⟩
  rw [Finset.centerMass_eq_of_sum_1 Finset.univ atom hweight.2] at hcenter
  exact hcenter

/-- The recursively maintained explicit coefficient vector for a sequence of
conditional-gradient steps.  At stage `n` it has one entry for the initial
atom and one for each of the first `n` linear-oracle atoms. -/
def conditionalGradientWeightTrajectory (step : ℕ → ℝ) :
    ∀ iteration : ℕ, Fin (iteration + 1) → ℝ
  | 0 => fun _ => 1
  | iteration + 1 =>
      conditionalGradientWeights (conditionalGradientWeightTrajectory step iteration)
        (step iteration)

/-- The corresponding list of initial and linear-oracle atoms. -/
def conditionalGradientAtomTrajectory {Value : Type*}
    (initial : Value) (oracle : ℕ → Value) :
    ∀ iteration : ℕ, Fin (iteration + 1) → Value
  | 0 => fun _ => initial
  | iteration + 1 =>
      Fin.snoc (conditionalGradientAtomTrajectory initial oracle iteration) (oracle iteration)

/-- One stage of the recursive weight trajectory is the usual conditional-
gradient weight update. -/
theorem conditionalGradientWeightTrajectory_succ (step : ℕ → ℝ) (iteration : ℕ) :
    conditionalGradientWeightTrajectory step (iteration + 1) =
      conditionalGradientWeights (conditionalGradientWeightTrajectory step iteration)
        (step iteration) := rfl

/-- One stage of the recursive atom trajectory appends the current oracle
atom. -/
theorem conditionalGradientAtomTrajectory_succ {Value : Type*}
    (initial : Value) (oracle : ℕ → Value) (iteration : ℕ) :
    conditionalGradientAtomTrajectory initial oracle (iteration + 1) =
      Fin.snoc (conditionalGradientAtomTrajectory initial oracle iteration) (oracle iteration) := rfl

/-- If the initial atom and every linear-oracle atom are feasible, every atom
recorded by the explicit trajectory is feasible as well. -/
theorem conditionalGradientAtomTrajectory_mem
    {Value : Type*} (initial : Value) (oracle : ℕ → Value) (feasible : Set Value)
    (hinitial : initial ∈ feasible) (horacle : ∀ iteration, oracle iteration ∈ feasible) :
    ∀ iteration index,
      conditionalGradientAtomTrajectory initial oracle iteration index ∈ feasible := by
  intro iteration
  induction iteration with
  | zero =>
      intro index
      fin_cases index
      simpa [conditionalGradientAtomTrajectory] using hinitial
  | succ iteration ih =>
      intro index
      refine Fin.lastCases ?_ (fun previous => ?_) index
      · simpa [conditionalGradientAtomTrajectory] using horacle iteration
      · simpa [conditionalGradientAtomTrajectory] using ih previous

/-- Every stage of an explicit conditional-gradient weight trajectory is a
convex-combination certificate, provided every step lies in `[0,1]`. -/
theorem isConvexCombinationWeights_conditionalGradientWeightTrajectory
    (step : ℕ → ℝ)
    (hstepLower : ∀ iteration, 0 ≤ step iteration)
    (hstepUpper : ∀ iteration, step iteration ≤ 1) :
    ∀ iteration,
      IsConvexCombinationWeights (conditionalGradientWeightTrajectory step iteration) := by
  intro iteration
  induction iteration with
  | zero =>
      constructor
      · intro index
        simp [conditionalGradientWeightTrajectory]
      · simp [conditionalGradientWeightTrajectory]
  | succ iteration ih =>
      rw [conditionalGradientWeightTrajectory_succ]
      exact isConvexCombinationWeights_conditionalGradientWeights
        (conditionalGradientWeightTrajectory step iteration) (step iteration) ih
        (hstepLower iteration) (hstepUpper iteration)

/-- The recursive explicit mixture satisfies the same affine update as the
conditional-gradient iterate. -/
theorem conditionalGradientMixture_trajectory_succ
    {Value : Type*} [AddCommMonoid Value] [Module ℝ Value]
    (initial : Value) (oracle : ℕ → Value) (step : ℕ → ℝ) (iteration : ℕ) :
    conditionalGradientMixture
        (conditionalGradientAtomTrajectory initial oracle (iteration + 1))
        (conditionalGradientWeightTrajectory step (iteration + 1)) =
      (1 - step iteration) •
          conditionalGradientMixture
            (conditionalGradientAtomTrajectory initial oracle iteration)
            (conditionalGradientWeightTrajectory step iteration) +
        step iteration • oracle iteration := by
  rw [conditionalGradientAtomTrajectory_succ, conditionalGradientWeightTrajectory_succ]
  exact conditionalGradientMixture_update
    (conditionalGradientAtomTrajectory initial oracle iteration)
    (conditionalGradientWeightTrajectory step iteration) (oracle iteration) (step iteration)

/-- A trajectory initialized at one atom and following the conditional-
gradient affine update is represented exactly by the recursively maintained
finite convex combination of its oracle atoms. -/
theorem conditionalGradientTrajectory_eq_mixture
    {Value : Type*} [AddCommMonoid Value] [Module ℝ Value]
    (initial : Value) (oracle : ℕ → Value) (step : ℕ → ℝ)
    (trajectory : ℕ → Value)
    (hinitial : trajectory 0 = initial)
    (hupdate : ∀ iteration,
      trajectory (iteration + 1) =
        (1 - step iteration) • trajectory iteration + step iteration • oracle iteration) :
    ∀ iteration,
      trajectory iteration =
        conditionalGradientMixture (conditionalGradientAtomTrajectory initial oracle iteration)
          (conditionalGradientWeightTrajectory step iteration) := by
  intro iteration
  induction iteration with
  | zero =>
      simpa [conditionalGradientAtomTrajectory, conditionalGradientWeightTrajectory,
        conditionalGradientMixture] using hinitial
  | succ iteration ih =>
      calc
        trajectory (iteration + 1) =
            (1 - step iteration) • trajectory iteration + step iteration • oracle iteration :=
          hupdate iteration
        _ = (1 - step iteration) •
              conditionalGradientMixture
                (conditionalGradientAtomTrajectory initial oracle iteration)
                (conditionalGradientWeightTrajectory step iteration) +
              step iteration • oracle iteration := by rw [ih]
        _ = conditionalGradientMixture
              (conditionalGradientAtomTrajectory initial oracle (iteration + 1))
              (conditionalGradientWeightTrajectory step (iteration + 1)) :=
          (conditionalGradientMixture_trajectory_succ initial oracle step iteration).symm

/-- The conventional zero-based conditional-gradient step size.  Its first
step is one, so the first linear-oracle point replaces the arbitrary
initialization exactly. -/
noncomputable def conditionalGradientStepSize (iteration : ℕ) : ℝ :=
  2 / ((iteration : ℝ) + 2)

/-- The first zero-based conditional-gradient step has size one. -/
theorem conditionalGradientStepSize_zero : conditionalGradientStepSize 0 = 1 := by
  norm_num [conditionalGradientStepSize]

/-- Conditional-gradient step sizes are nonnegative. -/
theorem conditionalGradientStepSize_nonneg (iteration : ℕ) :
    0 ≤ conditionalGradientStepSize iteration := by
  unfold conditionalGradientStepSize
  positivity

/-- Conditional-gradient step sizes do not exceed one. -/
theorem conditionalGradientStepSize_le_one (iteration : ℕ) :
    conditionalGradientStepSize iteration ≤ 1 := by
  unfold conditionalGradientStepSize
  have hdenominator : 0 < (iteration : ℝ) + 2 := by positivity
  rw [div_le_one₀ hdenominator]
  have hiteration : 0 ≤ (iteration : ℝ) := Nat.cast_nonneg iteration
  linarith

/-- An exact linear-minimization oracle for one conditional-gradient step.
The oracle atom minimizes the gradient's linearization over the feasible set;
its own feasibility is recorded so that a diameter hypothesis can be applied
to the resulting step. -/
def IsConditionalGradientLinearOracle
    {Value : Type*} [NormedAddCommGroup Value] [InnerProductSpace ℝ Value]
    (feasible : Set Value) (gradient : Value → Value) (current oracleAtom : Value) : Prop :=
  oracleAtom ∈ feasible ∧ ∀ candidate ∈ feasible,
    ⟪gradient current, oracleAtom - current⟫_ℝ ≤
      ⟪gradient current, candidate - current⟫_ℝ

/-- A smooth first-order objective, an exact linear minimization oracle, and
a diameter bound imply the conditional-gradient one-step suboptimality
recurrence.  The quadratic term is `β R² / 2`, with `β` the gradient
smoothness and `R` the Euclidean diameter. -/
theorem conditionalGradient_oneStep_suboptimality_of_smoothness
    {Value : Type*} [NormedAddCommGroup Value] [InnerProductSpace ℝ Value]
    [CompleteSpace Value]
    (objective : Value → ℝ) (gradient : Value → Value) (feasible : Set Value)
    (current oracleAtom optimum : Value) (step smoothness diameter : ℝ)
    (hgradient : ∀ first second,
      ‖gradient first - gradient second‖ ≤ smoothness * ‖first - second‖)
    (hgradientAt : ∀ point, HasGradientAt objective (gradient point) point)
    (hsmoothness : 0 ≤ smoothness)
    (hfirstOrder : ∀ center ∈ feasible, ∀ candidate ∈ feasible,
      objective candidate ≥ objective center +
        ⟪gradient center, candidate - center⟫_ℝ)
    (hdiameter : ∀ first ∈ feasible, ∀ second ∈ feasible,
      ‖first - second‖ ≤ diameter)
    (hcurrent : current ∈ feasible) (hoptimum : optimum ∈ feasible)
    (hstepLower : 0 ≤ step) (hstepUpper : step ≤ 1)
    (horacle : IsConditionalGradientLinearOracle feasible gradient current oracleAtom) :
    objective ((1 - step) • current + step • oracleAtom) - objective optimum ≤
      (1 - step) * (objective current - objective optimum) +
        (smoothness / 2 * diameter ^ 2) * step ^ 2 := by
  rcases horacle with ⟨horacleFeasible, horacleMin⟩
  have hinner : ⟪gradient current, oracleAtom - current⟫_ℝ ≤
      objective optimum - objective current := by
    have horacleOptimal := horacleMin optimum hoptimum
    have hfirstOrderOptimal := hfirstOrder current hcurrent optimum hoptimum
    linarith
  have hmodel := smooth_upper_model_bound objective gradient smoothness hgradient hgradientAt
    current ((1 - step) • current + step • oracleAtom)
  have hdisplacement :
      ((1 - step) • current + step • oracleAtom) - current =
        step • (oracleAtom - current) := by
    module
  rw [hdisplacement, inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hstepLower] at hmodel
  have hnormSquare : (step * ‖oracleAtom - current‖) ^ 2 =
      step ^ 2 * ‖oracleAtom - current‖ ^ 2 := by ring
  rw [hnormSquare] at hmodel
  have hdistance := hdiameter oracleAtom horacleFeasible current hcurrent
  have hdiameterNonneg : 0 ≤ diameter :=
    (norm_nonneg (oracleAtom - current)).trans hdistance
  have hdistanceSquare : ‖oracleAtom - current‖ ^ 2 ≤ diameter ^ 2 := by
    nlinarith [norm_nonneg (oracleAtom - current)]
  have hstepDistanceSquare :
      step ^ 2 * ‖oracleAtom - current‖ ^ 2 ≤ step ^ 2 * diameter ^ 2 :=
    mul_le_mul_of_nonneg_left hdistanceSquare (sq_nonneg step)
  have hquadratic :
      smoothness / 2 * (step ^ 2 * ‖oracleAtom - current‖ ^ 2) ≤
        smoothness / 2 * (step ^ 2 * diameter ^ 2) :=
    mul_le_mul_of_nonneg_left hstepDistanceSquare (by linarith)
  have hscaledInner : step * ⟪gradient current, oracleAtom - current⟫_ℝ ≤
      step * (objective optimum - objective current) :=
    mul_le_mul_of_nonneg_left hinner hstepLower
  nlinarith

/-- Conditional-gradient one-step progress from a quadratic upper model that
holds only on a convex feasible set.  This is the right interface for bounded
entropy objectives: the segment joining the current iterate to the oracle
atom remains feasible, so global smoothness outside the decision set is not
needed. -/
theorem conditionalGradient_oneStep_suboptimality_of_upperModel
    {Value : Type*} [NormedAddCommGroup Value] [InnerProductSpace ℝ Value]
    (objective : Value → ℝ) (gradient : Value → Value) (feasible : Set Value)
    (current oracleAtom comparator : Value) (step smoothness diameter : ℝ)
    (hfeasible : Convex ℝ feasible)
    (hupperModel : ∀ center ∈ feasible, ∀ candidate ∈ feasible,
      objective candidate ≤ objective center +
        ⟪gradient center, candidate - center⟫_ℝ +
          smoothness / 2 * ‖candidate - center‖ ^ 2)
    (hsmoothness : 0 ≤ smoothness)
    (hfirstOrder : ∀ center ∈ feasible, ∀ candidate ∈ feasible,
      objective candidate ≥ objective center +
        ⟪gradient center, candidate - center⟫_ℝ)
    (hdiameter : ∀ first ∈ feasible, ∀ second ∈ feasible,
      ‖first - second‖ ≤ diameter)
    (hcurrent : current ∈ feasible) (hcomparator : comparator ∈ feasible)
    (hstepLower : 0 ≤ step) (hstepUpper : step ≤ 1)
    (horacle : IsConditionalGradientLinearOracle feasible gradient current oracleAtom) :
    objective ((1 - step) • current + step • oracleAtom) - objective comparator ≤
      (1 - step) * (objective current - objective comparator) +
        (smoothness / 2 * diameter ^ 2) * step ^ 2 := by
  rcases horacle with ⟨horacleFeasible, horacleMin⟩
  have hinner : ⟪gradient current, oracleAtom - current⟫_ℝ ≤
      objective comparator - objective current := by
    have horacleOptimal := horacleMin comparator hcomparator
    have hfirstOrderComparator := hfirstOrder current hcurrent comparator hcomparator
    linarith
  have hnext : (1 - step) • current + step • oracleAtom ∈ feasible := by
    simpa only [AffineMap.lineMap_apply_module] using
      hfeasible.lineMap_mem hcurrent horacleFeasible ⟨hstepLower, hstepUpper⟩
  have hmodel := hupperModel current hcurrent
    ((1 - step) • current + step • oracleAtom) hnext
  have hdisplacement :
      ((1 - step) • current + step • oracleAtom) - current =
        step • (oracleAtom - current) := by
    module
  rw [hdisplacement, inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hstepLower] at hmodel
  have hnormSquare : (step * ‖oracleAtom - current‖) ^ 2 =
      step ^ 2 * ‖oracleAtom - current‖ ^ 2 := by ring
  rw [hnormSquare] at hmodel
  have hdistance := hdiameter oracleAtom horacleFeasible current hcurrent
  have hdistanceSquare : ‖oracleAtom - current‖ ^ 2 ≤ diameter ^ 2 := by
    nlinarith [norm_nonneg (oracleAtom - current)]
  have hstepDistanceSquare :
      step ^ 2 * ‖oracleAtom - current‖ ^ 2 ≤ step ^ 2 * diameter ^ 2 :=
    mul_le_mul_of_nonneg_left hdistanceSquare (sq_nonneg step)
  have hquadratic :
      smoothness / 2 * (step ^ 2 * ‖oracleAtom - current‖ ^ 2) ≤
        smoothness / 2 * (step ^ 2 * diameter ^ 2) :=
    mul_le_mul_of_nonneg_left hstepDistanceSquare (by linarith)
  have hscaledInner : step * ⟪gradient current, oracleAtom - current⟫_ℝ ≤
      step * (objective comparator - objective current) :=
    mul_le_mul_of_nonneg_left hinner hstepLower
  nlinarith

/-- Scalar convergence calculation for conditional gradient descent.  A
smoothness and exact-linear-oracle argument supplies the displayed
one-step recurrence with `curvature = β R² / 2`; this lemma then gives the
standard `2 β R² / (t + 1)` error bound after the `t`-th source-indexed
iterate.  Stating the recurrence separately keeps this finite-mixture module
independent of a particular differentiability API. -/
theorem conditionalGradient_suboptimality_le_of_recurrence
    (error : ℕ → ℝ) (curvature : ℝ) (hcurvature : 0 ≤ curvature)
    (hrecurrence : ∀ iteration,
      error (iteration + 1) ≤
        (1 - conditionalGradientStepSize iteration) * error iteration +
          curvature * (conditionalGradientStepSize iteration) ^ 2) :
    ∀ iteration,
      error (iteration + 1) ≤ 4 * curvature / ((iteration : ℝ) + 3) := by
  intro iteration
  induction iteration with
  | zero =>
      have hstep := hrecurrence 0
      norm_num [conditionalGradientStepSize] at hstep ⊢
      nlinarith
  | succ iteration ih =>
      let denominator : ℝ := (iteration : ℝ) + 3
      have hdenominator : 0 < denominator := by
        dsimp [denominator]
        positivity
      have hcoefficient : 0 ≤ 1 - 2 / denominator := by
        apply sub_nonneg.mpr
        rw [div_le_one₀ hdenominator]
        dsimp [denominator]
        have hiteration : 0 ≤ (iteration : ℝ) := Nat.cast_nonneg iteration
        linarith
      have hscaled := mul_le_mul_of_nonneg_left ih hcoefficient
      have hrecurrence' := hrecurrence (iteration + 1)
      have hdenominator_eq : (((iteration + 1 : ℕ) : ℝ) + 2) = denominator := by
        simp only [denominator, Nat.cast_add, Nat.cast_one]
        ring
      rw [conditionalGradientStepSize, hdenominator_eq] at hrecurrence'
      have hquadratic :
          (1 - 2 / denominator) * (4 * curvature / denominator) +
              curvature * (2 / denominator) ^ 2 ≤
            4 * curvature / (denominator + 1) := by
        have hnext : 0 < denominator + 1 := by linarith
        field_simp [ne_of_gt hdenominator, ne_of_gt hnext]
        nlinarith
      calc
        error (Nat.succ iteration + 1) = error (iteration + 1 + 1) := by
          simp [Nat.succ_eq_add_one]
        _ ≤ (1 - 2 / denominator) * error (iteration + 1) +
            curvature * (2 / denominator) ^ 2 := hrecurrence'
        _ ≤ (1 - 2 / denominator) * (4 * curvature / denominator) +
            curvature * (2 / denominator) ^ 2 := by linarith
        _ ≤ 4 * curvature / (denominator + 1) := hquadratic
        _ = 4 * curvature / ((Nat.succ iteration : ℕ) + 3 : ℝ) := by
          simp only [denominator, Nat.cast_succ]
          ring

/-- Full conditional-gradient rate for a smooth first-order objective.  The
trajectory follows exact linear-oracle updates with the standard step sizes;
therefore its suboptimality is at most `4 * (β R² / 2) / (t + 2)` after the
zero-based update `t`.  This is the conventional `O(β R²/t)` Frank--Wolfe
guarantee, with all oracle, smoothness, and diameter assumptions explicit. -/
theorem conditionalGradient_suboptimality_le_of_smoothness
    {Value : Type*} [NormedAddCommGroup Value] [InnerProductSpace ℝ Value]
    [CompleteSpace Value]
    (objective : Value → ℝ) (gradient : Value → Value) (feasible : Set Value)
    (trajectory oracle : ℕ → Value) (optimum : Value) (smoothness diameter : ℝ)
    (hgradient : ∀ first second,
      ‖gradient first - gradient second‖ ≤ smoothness * ‖first - second‖)
    (hgradientAt : ∀ point, HasGradientAt objective (gradient point) point)
    (hsmoothness : 0 ≤ smoothness)
    (hfirstOrder : ∀ center ∈ feasible, ∀ candidate ∈ feasible,
      objective candidate ≥ objective center +
        ⟪gradient center, candidate - center⟫_ℝ)
    (hdiameter : ∀ first ∈ feasible, ∀ second ∈ feasible,
      ‖first - second‖ ≤ diameter)
    (htrajectory : ∀ iteration, trajectory iteration ∈ feasible)
    (hoptimum : optimum ∈ feasible)
    (horacle : ∀ iteration,
      IsConditionalGradientLinearOracle feasible gradient
        (trajectory iteration) (oracle iteration))
    (hupdate : ∀ iteration,
      trajectory (iteration + 1) =
        (1 - conditionalGradientStepSize iteration) • trajectory iteration +
          conditionalGradientStepSize iteration • oracle iteration) :
    ∀ iteration,
      objective (trajectory (iteration + 1)) - objective optimum ≤
        4 * (smoothness / 2 * diameter ^ 2) / ((iteration : ℝ) + 3) := by
  let error : ℕ → ℝ := fun iteration => objective (trajectory iteration) - objective optimum
  have hcurvature : 0 ≤ smoothness / 2 * diameter ^ 2 := by
    exact mul_nonneg (by linarith) (sq_nonneg diameter)
  have hrecurrence : ∀ iteration,
      error (iteration + 1) ≤
        (1 - conditionalGradientStepSize iteration) * error iteration +
          (smoothness / 2 * diameter ^ 2) *
            (conditionalGradientStepSize iteration) ^ 2 := by
    intro iteration
    change objective (trajectory (iteration + 1)) - objective optimum ≤ _
    rw [hupdate iteration]
    exact conditionalGradient_oneStep_suboptimality_of_smoothness
      objective gradient feasible (trajectory iteration) (oracle iteration) optimum
      (conditionalGradientStepSize iteration) smoothness diameter hgradient hgradientAt
      hsmoothness hfirstOrder hdiameter (htrajectory iteration) hoptimum
      (conditionalGradientStepSize_nonneg iteration)
      (conditionalGradientStepSize_le_one iteration) (horacle iteration)
  have hrate := conditionalGradient_suboptimality_le_of_recurrence error
    (smoothness / 2 * diameter ^ 2) hcurvature hrecurrence
  simpa only [error] using hrate

/-- Full `O(β R²/t)` conditional-gradient rate from a quadratic upper model
on a convex feasible set.  The comparison point need only be feasible, not an
attained optimizer; consequently this directly gives approximation relative
to every feasible competitor even when an infimum is not attained. -/
theorem conditionalGradient_suboptimality_le_of_upperModel
    {Value : Type*} [NormedAddCommGroup Value] [InnerProductSpace ℝ Value]
    (objective : Value → ℝ) (gradient : Value → Value) (feasible : Set Value)
    (trajectory oracle : ℕ → Value) (comparator : Value) (smoothness diameter : ℝ)
    (hfeasible : Convex ℝ feasible)
    (hupperModel : ∀ center ∈ feasible, ∀ candidate ∈ feasible,
      objective candidate ≤ objective center +
        ⟪gradient center, candidate - center⟫_ℝ +
          smoothness / 2 * ‖candidate - center‖ ^ 2)
    (hsmoothness : 0 ≤ smoothness)
    (hfirstOrder : ∀ center ∈ feasible, ∀ candidate ∈ feasible,
      objective candidate ≥ objective center +
        ⟪gradient center, candidate - center⟫_ℝ)
    (hdiameter : ∀ first ∈ feasible, ∀ second ∈ feasible,
      ‖first - second‖ ≤ diameter)
    (htrajectory : ∀ iteration, trajectory iteration ∈ feasible)
    (hcomparator : comparator ∈ feasible)
    (horacle : ∀ iteration,
      IsConditionalGradientLinearOracle feasible gradient
        (trajectory iteration) (oracle iteration))
    (hupdate : ∀ iteration,
      trajectory (iteration + 1) =
        (1 - conditionalGradientStepSize iteration) • trajectory iteration +
          conditionalGradientStepSize iteration • oracle iteration) :
    ∀ iteration,
      objective (trajectory (iteration + 1)) - objective comparator ≤
        4 * (smoothness / 2 * diameter ^ 2) / ((iteration : ℝ) + 3) := by
  let error : ℕ → ℝ := fun iteration => objective (trajectory iteration) - objective comparator
  have hcurvature : 0 ≤ smoothness / 2 * diameter ^ 2 := by
    exact mul_nonneg (by linarith) (sq_nonneg diameter)
  have hrecurrence : ∀ iteration,
      error (iteration + 1) ≤
        (1 - conditionalGradientStepSize iteration) * error iteration +
          (smoothness / 2 * diameter ^ 2) *
            (conditionalGradientStepSize iteration) ^ 2 := by
    intro iteration
    change objective (trajectory (iteration + 1)) - objective comparator ≤ _
    rw [hupdate iteration]
    exact conditionalGradient_oneStep_suboptimality_of_upperModel
      objective gradient feasible (trajectory iteration) (oracle iteration) comparator
      (conditionalGradientStepSize iteration) smoothness diameter hfeasible hupperModel hsmoothness hfirstOrder
      hdiameter (htrajectory iteration) hcomparator
      (conditionalGradientStepSize_nonneg iteration)
      (conditionalGradientStepSize_le_one iteration) (horacle iteration)
  have hrate := conditionalGradient_suboptimality_le_of_recurrence error
    (smoothness / 2 * diameter ^ 2) hcurvature hrecurrence
  simpa only [error] using hrate

end AppliedModelingLib

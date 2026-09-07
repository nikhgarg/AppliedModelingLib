import AppliedModelingLib.Foundations.Math.FiniteDimensionalNorms
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Regularized finite-dimensional leverage

This file proves the finite trace identity behind the standard leverage-score
bound for a ridge-regularized Gram matrix.  The result is useful in linear
bandits, linear MDP planning, experimental design, and least-squares analyses.
-/

namespace AppliedModelingLib

open Matrix
open scoped BigOperators

noncomputable section

/-- Cauchy--Schwarz for the seminorm induced by a real positive-semidefinite
matrix.  Keeping this statement at matrix level avoids choosing a square root
or a basis change in downstream leverage arguments. -/
theorem posSemidef_abs_dotProduct_mulVec_le_sqrt_mul_sqrt
    {Coordinate : Type*} [Fintype Coordinate]
    {matrix : Matrix Coordinate Coordinate ℝ}
    (hmatrix : matrix.PosSemidef) (first second : Coordinate → ℝ) :
    |dotProduct first (matrix.mulVec second)| ≤
      Real.sqrt (dotProduct first (matrix.mulVec first)) *
        Real.sqrt (dotProduct second (matrix.mulVec second)) := by
  letI : SeminormedAddCommGroup (Coordinate → ℝ) :=
    matrix.toSeminormedAddCommGroup hmatrix
  letI : InnerProductSpace ℝ (Coordinate → ℝ) :=
    matrix.toInnerProductSpace hmatrix
  have h := abs_real_inner_le_norm first second
  change |(matrix.mulVec second) ⬝ᵥ first| ≤
    Real.sqrt ((matrix.mulVec first) ⬝ᵥ first) *
      Real.sqrt ((matrix.mulVec second) ⬝ᵥ second) at h
  simpa [dotProduct_comm] using h

/-- Dual Cauchy--Schwarz for a positive-definite matrix and its inverse. -/
theorem posDef_abs_dotProduct_le_sqrt_inverse_mul_sqrt
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    {matrix : Matrix Coordinate Coordinate ℝ}
    (hmatrix : matrix.PosDef) (first second : Coordinate → ℝ) :
    |dotProduct first second| ≤
      Real.sqrt (dotProduct first (matrix⁻¹.mulVec first)) *
        Real.sqrt (dotProduct second (matrix.mulVec second)) := by
  have hinvertible : IsUnit matrix.det :=
    Matrix.isUnit_iff_isUnit_det matrix |>.mp hmatrix.isUnit
  have hcs := posSemidef_abs_dotProduct_mulVec_le_sqrt_mul_sqrt
    hmatrix.inv.posSemidef first (matrix.mulVec second)
  have hinverseMul : matrix⁻¹.mulVec (matrix.mulVec second) = second := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul matrix hinvertible, Matrix.one_mulVec]
  have hsecond :
      dotProduct (matrix.mulVec second)
          (matrix⁻¹.mulVec (matrix.mulVec second)) =
        dotProduct second (matrix.mulVec second) := by
    rw [hinverseMul, dotProduct_comm]
  simpa [hinverseMul, hsecond, dotProduct_comm] using hcs

/-- The squared seminorm induced by a positive-semidefinite matrix obeys the
standard two-vector relaxation `‖x+y‖² ≤ 2‖x‖²+2‖y‖²`. -/
theorem posSemidef_add_quadratic_le_two_mul_add_two_mul
    {Coordinate : Type*} [Fintype Coordinate]
    {matrix : Matrix Coordinate Coordinate ℝ}
    (hmatrix : matrix.PosSemidef) (first second : Coordinate → ℝ) :
    dotProduct (first + second) (matrix.mulVec (first + second)) ≤
      2 * dotProduct first (matrix.mulVec first) +
        2 * dotProduct second (matrix.mulVec second) := by
  let firstEnergy := dotProduct first (matrix.mulVec first)
  let secondEnergy := dotProduct second (matrix.mulVec second)
  have hfirstNonneg : 0 ≤ firstEnergy := by
    simpa [firstEnergy] using hmatrix.dotProduct_mulVec_nonneg first
  have hsecondNonneg : 0 ≤ secondEnergy := by
    simpa [secondEnergy] using hmatrix.dotProduct_mulVec_nonneg second
  have hcrossFirst :=
    posSemidef_abs_dotProduct_mulVec_le_sqrt_mul_sqrt hmatrix first second
  have hcrossSecond :=
    posSemidef_abs_dotProduct_mulVec_le_sqrt_mul_sqrt hmatrix second first
  have hrootSquareFirst : (Real.sqrt firstEnergy) ^ 2 = firstEnergy :=
    Real.sq_sqrt hfirstNonneg
  have hrootSquareSecond : (Real.sqrt secondEnergy) ^ 2 = secondEnergy :=
    Real.sq_sqrt hsecondNonneg
  have hroot :
      2 * Real.sqrt firstEnergy * Real.sqrt secondEnergy ≤
        firstEnergy + secondEnergy := by
    simpa [hrootSquareFirst, hrootSquareSecond] using
      two_mul_le_add_sq (Real.sqrt firstEnergy) (Real.sqrt secondEnergy)
  have hexpand :
      dotProduct (first + second) (matrix.mulVec (first + second)) =
        firstEnergy + secondEnergy +
          dotProduct first (matrix.mulVec second) +
          dotProduct second (matrix.mulVec first) := by
    rw [Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add]
    dsimp [firstEnergy, secondEnergy]
    ring
  rw [hexpand]
  calc
    firstEnergy + secondEnergy + dotProduct first (matrix.mulVec second) +
        dotProduct second (matrix.mulVec first) ≤
      firstEnergy + secondEnergy +
        |dotProduct first (matrix.mulVec second)| +
        |dotProduct second (matrix.mulVec first)| := by
          gcongr <;> exact le_abs_self _
    _ ≤ firstEnergy + secondEnergy +
        Real.sqrt firstEnergy * Real.sqrt secondEnergy +
        (Real.sqrt secondEnergy * Real.sqrt firstEnergy) := by
          gcongr
    _ ≤ 2 * firstEnergy + 2 * secondEnergy := by
      nlinarith

/-- A ridge-regularized Gram matrix over a finite collection of vectors. -/
def regularizedGram
    {Index Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    (ridge : ℝ) (vectors : Index → Coordinate → ℝ) (indices : Finset Index) :
    Matrix Coordinate Coordinate ℝ :=
  ridge • 1 + ∑ index ∈ indices, Matrix.vecMulVec (vectors index) (vectors index)

/-- A positive ridge makes every finite regularized Gram matrix positive definite. -/
theorem regularizedGram_posDef
    {Index Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    (ridge : ℝ) (vectors : Index → Coordinate → ℝ) (indices : Finset Index)
    (hridge : 0 < ridge) :
    (regularizedGram ridge vectors indices).PosDef := by
  classical
  unfold regularizedGram
  have hbase : (ridge • (1 : Matrix Coordinate Coordinate ℝ)).PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · apply Matrix.IsHermitian.smul Matrix.isHermitian_one
      simp [isSelfAdjoint_iff]
    · intro vector hvector
      simp only [star_trivial]
      rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul]
      have hsq : 0 < ∑ coordinate, vector coordinate ^ 2 := by
        apply Finset.sum_pos'
        · intro coordinate _
          exact sq_nonneg _
        · by_contra hzero
          push Not at hzero
          apply hvector
          funext coordinate
          apply sq_eq_zero_iff.mp
          exact le_antisymm
            (hzero coordinate (Finset.mem_univ coordinate)) (sq_nonneg _)
      simpa [dotProduct, smul_eq_mul, pow_two] using mul_pos hridge hsq
  apply hbase.add_posSemidef
  apply Matrix.posSemidef_sum
  intro index _
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨?_, ?_⟩
  · ext first second
    simp [Matrix.vecMulVec, mul_comm]
  · intro vector
    rw [Matrix.vecMulVec_mulVec]
    simp [dotProduct]
    change 0 ≤ ∑ coordinate, vector coordinate *
      (vectors index coordinate * ∑ prior, vectors index prior * vector prior)
    calc
      0 ≤ (∑ coordinate, vectors index coordinate * vector coordinate) ^ 2 := sq_nonneg _
      _ = ∑ coordinate, vector coordinate *
          (vectors index coordinate * ∑ prior, vectors index prior * vector prior) := by
        rw [sq, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro coordinate _
        ring

/-- The ridge part of a regularized Gram matrix lower-bounds its quadratic
form in Euclidean energy. -/
theorem regularizedGram_ridge_mul_l2Sq_le_quadraticForm
    {Index Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    (ridge : ℝ) (vectors : Index → Coordinate → ℝ) (indices : Finset Index)
    (vector : Coordinate → ℝ) :
    ridge * FiniteDimensionalNorms.l2Sq vector ≤
      dotProduct vector (Matrix.mulVec (regularizedGram ridge vectors indices) vector) := by
  classical
  let unregularized : Matrix Coordinate Coordinate ℝ :=
    ∑ index ∈ indices, Matrix.vecMulVec (vectors index) (vectors index)
  have hunregularized : unregularized.PosSemidef := by
    dsimp [unregularized]
    apply Matrix.posSemidef_sum
    intro index _
    apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    refine ⟨?_, ?_⟩
    · ext first second
      simp [Matrix.vecMulVec, mul_comm]
    · intro direction
      rw [Matrix.vecMulVec_mulVec]
      simp [dotProduct]
      change 0 ≤ ∑ coordinate, direction coordinate *
        (vectors index coordinate *
          ∑ prior, vectors index prior * direction prior)
      calc
        0 ≤ (∑ coordinate,
            vectors index coordinate * direction coordinate) ^ 2 := sq_nonneg _
        _ = ∑ coordinate, direction coordinate *
            (vectors index coordinate *
              ∑ prior, vectors index prior * direction prior) := by
          rw [sq, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro coordinate _
          ring
  have hnonnegative : 0 ≤ dotProduct vector (unregularized.mulVec vector) :=
    hunregularized.dotProduct_mulVec_nonneg vector
  have hdecomposition :
      regularizedGram ridge vectors indices =
        ridge • (1 : Matrix Coordinate Coordinate ℝ) + unregularized := by
    rfl
  rw [hdecomposition, Matrix.add_mulVec, dotProduct_add]
  have hridgePart :
      dotProduct vector ((ridge • (1 : Matrix Coordinate Coordinate ℝ)).mulVec vector) =
        ridge * FiniteDimensionalNorms.l2Sq vector := by
    rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul]
    simp [FiniteDimensionalNorms.l2Sq, dotProduct, smul_eq_mul, pow_two]
  rw [hridgePart]
  linarith

/-- The inverse of a ridge Gram matrix has Euclidean operator norm at most
`1 / ridge`, stated directly as a bound on every matrix-vector product. -/
theorem regularizedGram_inverse_mulVec_l2_le
    {Index Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    (ridge : ℝ) (vectors : Index → Coordinate → ℝ) (indices : Finset Index)
    (vector : Coordinate → ℝ) (hridge : 0 < ridge) :
    FiniteDimensionalNorms.l2
        (Matrix.mulVec (regularizedGram ridge vectors indices)⁻¹ vector) ≤
      FiniteDimensionalNorms.l2 vector / ridge := by
  let covariance := regularizedGram ridge vectors indices
  let inverseVector := Matrix.mulVec covariance⁻¹ vector
  have hinvertible : IsUnit covariance.det :=
    Matrix.isUnit_iff_isUnit_det covariance |>.mp
      (regularizedGram_posDef ridge vectors indices hridge).isUnit
  have hrecover : Matrix.mulVec covariance inverseVector = vector := by
    dsimp [inverseVector]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv covariance hinvertible,
      Matrix.one_mulVec]
  have hcoercive :
      ridge * FiniteDimensionalNorms.l2Sq inverseVector ≤
        dotProduct inverseVector vector := by
    rw [← hrecover]
    simpa [covariance] using
      regularizedGram_ridge_mul_l2Sq_le_quadraticForm
        ridge vectors indices inverseVector
  have hdot : dotProduct inverseVector vector ≤
      FiniteDimensionalNorms.l2 inverseVector *
        FiniteDimensionalNorms.l2 vector := by
    calc
      dotProduct inverseVector vector ≤ |dotProduct inverseVector vector| := le_abs_self _
      _ ≤ FiniteDimensionalNorms.l2 inverseVector *
          FiniteDimensionalNorms.l2 vector := by
        simpa [FiniteDimensionalNorms.dot] using
          FiniteDimensionalNorms.abs_dot_le_l2_mul_l2 inverseVector vector
  change FiniteDimensionalNorms.l2 inverseVector ≤ _
  by_cases hzero : FiniteDimensionalNorms.l2 inverseVector = 0
  · rw [hzero]
    exact div_nonneg (FiniteDimensionalNorms.normL2_nonneg _) hridge.le
  · have hpositive : 0 < FiniteDimensionalNorms.l2 inverseVector :=
      lt_of_le_of_ne (FiniteDimensionalNorms.normL2_nonneg _) (Ne.symm hzero)
    have hsquare := FiniteDimensionalNorms.normL2_sq_eq_normL2Sq inverseVector
    have hridgeBound :
        ridge * FiniteDimensionalNorms.l2 inverseVector ≤
          FiniteDimensionalNorms.l2 vector := by
      nlinarith [hcoercive.trans hdot]
    exact (le_div_iff₀ hridge).2 (by simpa [mul_comm] using hridgeBound)

/-- Each inverse-Gram quadratic form is the trace of the corresponding
inverse-Gram rank-one product. -/
theorem regularizedGram_single_leverage_eq_trace
    {Index Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    (ridge : ℝ) (vectors : Index → Coordinate → ℝ) (indices : Finset Index)
    (index : Index) :
    dotProduct (vectors index)
        (Matrix.mulVec (regularizedGram ridge vectors indices)⁻¹ (vectors index)) =
      Matrix.trace ((regularizedGram ridge vectors indices)⁻¹ *
        Matrix.vecMulVec (vectors index) (vectors index)) := by
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec]
  exact (dotProduct_comm _ _).symm

/-- The sum of regularized leverage scores is the trace of the inverse Gram
matrix times its unregularized part. -/
theorem regularizedGram_leverage_sum_eq_trace
    {Index Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    (ridge : ℝ) (vectors : Index → Coordinate → ℝ) (indices : Finset Index) :
    (∑ index ∈ indices, dotProduct (vectors index)
        (Matrix.mulVec (regularizedGram ridge vectors indices)⁻¹ (vectors index))) =
      Matrix.trace ((regularizedGram ridge vectors indices)⁻¹ *
        (∑ index ∈ indices, Matrix.vecMulVec (vectors index) (vectors index))) := by
  classical
  rw [Matrix.mul_sum, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro index hindex
  exact regularizedGram_single_leverage_eq_trace ridge vectors indices index

/-- The exact ridge decomposition of the total-leverage matrix. -/
theorem regularizedGram_inverse_mul_unregularized_eq
    {Index Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    (ridge : ℝ) (vectors : Index → Coordinate → ℝ) (indices : Finset Index)
    (hridge : 0 < ridge) :
    (regularizedGram ridge vectors indices)⁻¹ *
        (∑ index ∈ indices, Matrix.vecMulVec (vectors index) (vectors index)) =
      1 - ridge • (regularizedGram ridge vectors indices)⁻¹ := by
  classical
  let covariance := regularizedGram ridge vectors indices
  have hinvertible : IsUnit covariance.det :=
    Matrix.isUnit_iff_isUnit_det covariance |>.mp
      (regularizedGram_posDef ridge vectors indices hridge).isUnit
  have hunregularized :
      (∑ index ∈ indices, Matrix.vecMulVec (vectors index) (vectors index)) =
        covariance - ridge • (1 : Matrix Coordinate Coordinate ℝ) := by
    dsimp [covariance, regularizedGram]
    abel
  rw [hunregularized, Matrix.mul_sub, Matrix.nonsing_inv_mul covariance hinvertible]
  simp

/-- Ridge domination of the inverse-Gram quadratic form.  Equivalently,
`lambda * x' (lambda I + sum_i z_i z_i')⁻¹ x ≤ ‖x‖₂²`.  This is the
deterministic ridge-bias estimate used in regularized least squares. -/
theorem regularizedGram_ridge_mul_inverseQuadratic_le_l2Sq
    {Index Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    (ridge : ℝ) (vectors : Index → Coordinate → ℝ) (indices : Finset Index)
    (vector : Coordinate → ℝ) (hridge : 0 < ridge) :
    ridge * dotProduct vector
        (Matrix.mulVec (regularizedGram ridge vectors indices)⁻¹ vector) ≤
      FiniteDimensionalNorms.l2Sq vector := by
  classical
  let covariance := regularizedGram ridge vectors indices
  let unregularized :=
    ∑ index ∈ indices, Matrix.vecMulVec (vectors index) (vectors index)
  let inverseVector := covariance⁻¹ *ᵥ vector
  have hcovariance : covariance.PosDef := by
    simpa [covariance] using regularizedGram_posDef ridge vectors indices hridge
  have hinvertible : IsUnit covariance.det :=
    Matrix.isUnit_iff_isUnit_det covariance |>.mp hcovariance.isUnit
  have hrecover : covariance *ᵥ inverseVector = vector := by
    dsimp [inverseVector]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv covariance hinvertible,
      Matrix.one_mulVec]
  have hunregularized : unregularized.PosSemidef := by
    dsimp [unregularized]
    apply Matrix.posSemidef_sum
    intro index _
    apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    refine ⟨?_, ?_⟩
    · ext first second
      simp [Matrix.vecMulVec, mul_comm]
    · intro direction
      rw [Matrix.vecMulVec_mulVec]
      simp only [dotProduct]
      calc
        0 ≤ (∑ coordinate, vectors index coordinate * direction coordinate) ^ 2 :=
          sq_nonneg _
        _ = ∑ coordinate, direction coordinate *
            (vectors index coordinate *
              ∑ prior, vectors index prior * direction prior) := by
              rw [sq, Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro coordinate _
              ring
  have hdecomposition :
      covariance = ridge • (1 : Matrix Coordinate Coordinate ℝ) + unregularized := by
    rfl
  have hunregularizedVector :
      unregularized *ᵥ inverseVector = vector - ridge • inverseVector := by
    have := hrecover
    rw [hdecomposition, Matrix.add_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec] at this
    exact eq_sub_of_add_eq (by simpa [add_comm] using this)
  have hnonneg :
      0 ≤ dotProduct inverseVector (unregularized *ᵥ inverseVector) :=
    hunregularized.dotProduct_mulVec_nonneg inverseVector
  have hidentity :
      FiniteDimensionalNorms.l2Sq vector -
          ridge * dotProduct vector inverseVector =
        ridge * dotProduct inverseVector
            (unregularized *ᵥ inverseVector) +
          FiniteDimensionalNorms.l2Sq
            (unregularized *ᵥ inverseVector) := by
    rw [← FiniteDimensionalNorms.dot_self_eq_l2Sq,
      ← FiniteDimensionalNorms.dot_self_eq_l2Sq]
    rw [← hrecover, hdecomposition, Matrix.add_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec]
    simp only [FiniteDimensionalNorms.dot, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, dotProduct, Finset.mul_sum]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro coordinate _
    ring
  have hsquare :
      0 ≤ FiniteDimensionalNorms.l2Sq
        (unregularized *ᵥ inverseVector) :=
    FiniteDimensionalNorms.normL2Sq_nonneg _
  have hdifference :
      0 ≤ FiniteDimensionalNorms.l2Sq vector -
        ridge * dotProduct vector inverseVector := by
    rw [hidentity]
    exact add_nonneg (mul_nonneg hridge.le hnonneg) hsquare
  simpa [covariance, inverseVector] using sub_nonneg.mp hdifference

/-- Square-root form of ridge domination.  In a ridge least-squares normal
equation, the regularization bias has inverse-Gram norm at most
`sqrt ridge * ‖parameter‖₂`. -/
theorem regularizedGram_ridge_mul_sqrt_inverseQuadratic_le
    {Index Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    (ridge : ℝ) (vectors : Index → Coordinate → ℝ) (indices : Finset Index)
    (vector : Coordinate → ℝ) (hridge : 0 < ridge) :
    ridge * Real.sqrt (dotProduct vector
        (Matrix.mulVec (regularizedGram ridge vectors indices)⁻¹ vector)) ≤
      Real.sqrt ridge * FiniteDimensionalNorms.l2 vector := by
  have hquadratic := regularizedGram_ridge_mul_inverseQuadratic_le_l2Sq
    ridge vectors indices vector hridge
  calc
    ridge * Real.sqrt (dotProduct vector
        (Matrix.mulVec (regularizedGram ridge vectors indices)⁻¹ vector)) =
        Real.sqrt ridge * Real.sqrt
          (ridge * dotProduct vector
            (Matrix.mulVec (regularizedGram ridge vectors indices)⁻¹ vector)) := by
          rw [Real.sqrt_mul hridge.le]
          have hridgeSqrt : ridge = Real.sqrt ridge * Real.sqrt ridge :=
            (Real.mul_self_sqrt hridge.le).symm
          calc
            ridge * Real.sqrt (dotProduct vector
                (Matrix.mulVec (regularizedGram ridge vectors indices)⁻¹ vector)) =
                (Real.sqrt ridge * Real.sqrt ridge) *
                  Real.sqrt (dotProduct vector
                    (Matrix.mulVec (regularizedGram ridge vectors indices)⁻¹ vector)) := by
                      exact congrArg (fun scalar : ℝ => scalar *
                        Real.sqrt (dotProduct vector
                          (Matrix.mulVec
                            (regularizedGram ridge vectors indices)⁻¹ vector)))
                        hridgeSqrt
            _ = Real.sqrt ridge *
                (Real.sqrt ridge * Real.sqrt (dotProduct vector
                  (Matrix.mulVec (regularizedGram ridge vectors indices)⁻¹ vector))) := by
                    ring
    _ ≤ Real.sqrt ridge * Real.sqrt (FiniteDimensionalNorms.l2Sq vector) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hquadratic) (Real.sqrt_nonneg _)
    _ = Real.sqrt ridge * FiniteDimensionalNorms.l2 vector := by
      rfl

/-- The standard finite-dimensional leverage-score trace bound:
`sum_i x_iᵀ (λI + sum_j x_j x_jᵀ)⁻¹ x_i ≤ d` for every `λ > 0`. -/
theorem regularizedGram_leverage_sum_le_card
    {Index Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    (ridge : ℝ) (vectors : Index → Coordinate → ℝ) (indices : Finset Index)
    (hridge : 0 < ridge) :
    (∑ index ∈ indices, dotProduct (vectors index)
        (Matrix.mulVec (regularizedGram ridge vectors indices)⁻¹ (vectors index))) ≤
      Fintype.card Coordinate := by
  classical
  rw [regularizedGram_leverage_sum_eq_trace]
  rw [regularizedGram_inverse_mul_unregularized_eq ridge vectors indices hridge]
  simp only [Matrix.trace_sub, Matrix.trace_one, Matrix.trace_smul, smul_eq_mul]
  have hinverseTrace :
      0 ≤ Matrix.trace (regularizedGram ridge vectors indices)⁻¹ :=
    (regularizedGram_posDef ridge vectors indices hridge).inv.posSemidef.trace_nonneg
  have hproduct :
      0 ≤ ridge * Matrix.trace (regularizedGram ridge vectors indices)⁻¹ :=
    mul_nonneg hridge.le hinverseTrace
  norm_num
  linarith

/-- A query vector of leverage at most one has total absolute cross leverage
against the Gram samples at most `sqrt(number of samples * dimension)`. -/
theorem regularizedGram_abs_crossLeverage_sum_le_sqrt_card_mul_dimension
    {Index Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    (ridge : ℝ) (vectors : Index → Coordinate → ℝ) (indices : Finset Index)
    (query : Coordinate → ℝ) (hridge : 0 < ridge)
    (hquery : dotProduct query
        (Matrix.mulVec (regularizedGram ridge vectors indices)⁻¹ query) ≤ 1) :
    (∑ index ∈ indices,
        |dotProduct query
          (Matrix.mulVec (regularizedGram ridge vectors indices)⁻¹ (vectors index))|) ≤
      Real.sqrt ((indices.card : ℝ) * Fintype.card Coordinate) := by
  classical
  let inverse := (regularizedGram ridge vectors indices)⁻¹
  have hinverse : inverse.PosSemidef :=
    (regularizedGram_posDef ridge vectors indices hridge).inv.posSemidef
  have hqueryNonneg : 0 ≤ dotProduct query (inverse.mulVec query) := by
    simpa [inverse] using hinverse.dotProduct_mulVec_nonneg query
  have hsampleNonneg : ∀ index,
      0 ≤ dotProduct (vectors index) (inverse.mulVec (vectors index)) := by
    intro index
    simpa [inverse] using hinverse.dotProduct_mulVec_nonneg (vectors index)
  have hcross : ∀ index,
      |dotProduct query (inverse.mulVec (vectors index))| ≤
        Real.sqrt (dotProduct query (inverse.mulVec query)) *
          Real.sqrt (dotProduct (vectors index) (inverse.mulVec (vectors index))) := by
    intro index
    exact posSemidef_abs_dotProduct_mulVec_le_sqrt_mul_sqrt
      hinverse query (vectors index)
  have hcs := Real.sum_sqrt_mul_sqrt_le
    (f := fun _index => dotProduct query (inverse.mulVec query))
    (g := fun index => dotProduct (vectors index) (inverse.mulVec (vectors index)))
    indices (fun _index => hqueryNonneg) hsampleNonneg
  have hquerySum :
      (∑ _index ∈ indices, dotProduct query (inverse.mulVec query)) ≤
        (indices.card : ℝ) := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    simpa [inverse] using
      (mul_le_mul_of_nonneg_left hquery (Nat.cast_nonneg indices.card))
  have hsampleSum :
      (∑ index ∈ indices,
          dotProduct (vectors index) (inverse.mulVec (vectors index))) ≤
        Fintype.card Coordinate := by
    simpa [inverse] using
      regularizedGram_leverage_sum_le_card ridge vectors indices hridge
  change (∑ index ∈ indices,
      |dotProduct query (inverse.mulVec (vectors index))|) ≤ _
  calc
    (∑ index ∈ indices,
        |dotProduct query (inverse.mulVec (vectors index))|) ≤
        ∑ index ∈ indices,
          Real.sqrt (dotProduct query (inverse.mulVec query)) *
            Real.sqrt (dotProduct (vectors index) (inverse.mulVec (vectors index))) := by
      exact Finset.sum_le_sum fun index _ ↦ hcross index
    _ ≤ Real.sqrt (∑ _index ∈ indices,
          dotProduct query (inverse.mulVec query)) *
        Real.sqrt (∑ index ∈ indices,
          dotProduct (vectors index) (inverse.mulVec (vectors index))) := hcs
    _ ≤ Real.sqrt (indices.card : ℝ) *
        Real.sqrt (Fintype.card Coordinate : ℝ) := by
      exact mul_le_mul
        (Real.sqrt_le_sqrt hquerySum) (Real.sqrt_le_sqrt hsampleSum)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = Real.sqrt ((indices.card : ℝ) * Fintype.card Coordinate) := by
      rw [Real.sqrt_mul (Nat.cast_nonneg indices.card)]

end

end AppliedModelingLib

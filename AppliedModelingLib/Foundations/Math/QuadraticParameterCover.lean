import AppliedModelingLib.Foundations.Math.EuclideanNets
import AppliedModelingLib.Foundations.Math.FiniteDimensionalNorms
import AppliedModelingLib.Foundations.Math.RegularizedLeverage

/-!
# Euclidean covers for quadratic parameters

Paper-neutral deterministic estimates used when a finite-dimensional value
class depends on both a vector parameter and a matrix quadratic form.  The
matrix metric is the Euclidean/Frobenius norm of its entries.
-/

namespace AppliedModelingLib
namespace Math
namespace QuadraticParameterCover

open FiniteDimensionalNorms
open scoped BigOperators

noncomputable section

/-- Exposing a finite Euclidean vector's coordinates preserves its norm. -/
theorem l2_ofLp_eq_norm
    {ι : Type*} [Fintype ι] (vector : EuclideanSpace ℝ ι) :
    l2 vector.ofLp = ‖vector‖ := by
  simpa using normL2_eq_piLp_norm_L2 vector.ofLp

/-- A scale-sensitive volumetric cover of a finite-coordinate Euclidean ball.
The returned net lives in the unit ball; multiplying its coordinates by
`radius` gives centers for the requested ball. -/
theorem exists_finset_l2_ball_scaled_inv_succ_net
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (n : ℕ) (radius : ℝ) (hradius : 0 < radius) :
    ∃ net : Finset (EuclideanSpace ℝ ι),
      net.card ≤ (4 * n + 5) ^ Fintype.card ι ∧
      (∀ center ∈ net, l2 center.ofLp ≤ 1) ∧
      ∀ vector : ι → ℝ, l2 vector ≤ radius →
        ∃ center ∈ net,
          l2 (fun coordinate ↦ vector coordinate - radius * center.ofLp coordinate) <
            radius / (n + 1 : ℝ) := by
  obtain ⟨net, hcard, hunit, hcover⟩ :=
    EuclideanNets.exists_finset_unit_closedBall_inv_succ_net
      (E := EuclideanSpace ℝ ι) n
  refine ⟨net, ?_, ?_, ?_⟩
  · simpa [finrank_euclideanSpace] using hcard
  · intro center hcenter
    rw [l2_ofLp_eq_norm]
    exact hunit center hcenter
  · intro vector hvector
    let normalized : EuclideanSpace ℝ ι :=
      WithLp.toLp 2 (fun coordinate ↦ radius⁻¹ * vector coordinate)
    have hnormalized : ‖normalized‖ ≤ 1 := by
      rw [← l2_ofLp_eq_norm]
      change l2 (fun coordinate ↦ radius⁻¹ * vector coordinate) ≤ 1
      rw [normL2_smul, abs_of_pos (inv_pos.mpr hradius)]
      calc
        radius⁻¹ * l2 vector ≤ radius⁻¹ * radius :=
          mul_le_mul_of_nonneg_left hvector (inv_nonneg.mpr hradius.le)
        _ = 1 := inv_mul_cancel₀ hradius.ne'
    obtain ⟨center, hcenter, hclose⟩ := hcover normalized hnormalized
    refine ⟨center, hcenter, ?_⟩
    have hcoordinateClose :
        l2 (fun coordinate ↦ radius⁻¹ * vector coordinate - center.ofLp coordinate) <
          1 / (n + 1 : ℝ) := by
      calc
        l2 (fun coordinate ↦ radius⁻¹ * vector coordinate - center.ofLp coordinate) =
            l2 (normalized - center).ofLp := by
          rfl
        _ = ‖normalized - center‖ := l2_ofLp_eq_norm _
        _ < 1 / (n + 1 : ℝ) := hclose
    have hrewrite :
        (fun coordinate ↦ vector coordinate - radius * center.ofLp coordinate) =
          (fun coordinate ↦
            radius * (radius⁻¹ * vector coordinate - center.ofLp coordinate)) := by
      funext coordinate
      field_simp
    rw [hrewrite, normL2_smul, abs_of_pos hradius]
    calc
      radius * l2
          (fun coordinate ↦ radius⁻¹ * vector coordinate - center.ofLp coordinate) <
          radius * (1 / (n + 1 : ℝ)) :=
        mul_lt_mul_of_pos_left hcoordinateClose hradius
      _ = radius / (n + 1 : ℝ) := by ring

/-- Frobenius norm written using the repository's explicit finite-coordinate
Euclidean norm. -/
def matrixL2 {ι : Type*} [Fintype ι] (matrix : Matrix ι ι ℝ) : ℝ :=
  l2 (fun index : ι × ι ↦ matrix index.1 index.2)

/-- Interpret a Euclidean vector indexed by coordinate pairs as a matrix. -/
def matrixOfLp {ι : Type*}
    (vector : EuclideanSpace ℝ (ι × ι)) : Matrix ι ι ℝ :=
  fun row column ↦ vector.ofLp (row, column)

/-- The vector-ball construction specialized to entrywise Frobenius matrix
norm, with its `d²` entropy exponent exposed. -/
theorem exists_finset_matrixL2_ball_scaled_inv_succ_net
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (n : ℕ) (radius : ℝ) (hradius : 0 < radius) :
    ∃ net : Finset (EuclideanSpace ℝ (ι × ι)),
      net.card ≤ (4 * n + 5) ^ (Fintype.card ι * Fintype.card ι) ∧
      (∀ center ∈ net, matrixL2 (matrixOfLp center) ≤ 1) ∧
      ∀ matrix : Matrix ι ι ℝ, matrixL2 matrix ≤ radius →
        ∃ center ∈ net,
          matrixL2 (matrix - radius • matrixOfLp center) <
            radius / (n + 1 : ℝ) := by
  obtain ⟨net, hcard, hunit, hcover⟩ :=
    exists_finset_l2_ball_scaled_inv_succ_net
      (ι := ι × ι) n radius hradius
  refine ⟨net, ?_, ?_, ?_⟩
  · simpa [Fintype.card_prod] using hcard
  · intro center hcenter
    simpa [matrixL2, matrixOfLp] using hunit center hcenter
  · intro matrix hmatrix
    obtain ⟨center, hcenter, hclose⟩ :=
      hcover (fun index : ι × ι ↦ matrix index.1 index.2) hmatrix
    refine ⟨center, hcenter, ?_⟩
    simpa [matrixL2, matrixOfLp] using hclose

/-- A `d`-dimensional ridge Gram inverse has entrywise Frobenius norm at most
`d / ridge`.  This deliberately elementary envelope is sufficient for value-
class entropy calculations and avoids choosing a matrix operator norm. -/
theorem regularizedGram_inverse_matrixL2_le_card_div
    {Index ι : Type*} [Fintype ι] [DecidableEq ι]
    (ridge : ℝ) (vectors : Index → ι → ℝ) (indices : Finset Index)
    (hridge : 0 < ridge) :
    matrixL2 (regularizedGram ridge vectors indices)⁻¹ ≤
      (Fintype.card ι : ℝ) / ridge := by
  classical
  let inverse := (regularizedGram ridge vectors indices)⁻¹
  have hentry (row column : ι) : |inverse row column| ≤ 1 / ridge := by
    let basis : ι → ℝ := fun coordinate ↦ if coordinate = column then 1 else 0
    have hbasis : l2 basis = 1 := by
      rw [l2, l2Sq]
      simp [basis]
    have hcolumn := regularizedGram_inverse_mulVec_l2_le
      ridge vectors indices basis hridge
    have hcoordinate := normL2_coord_abs_le (Matrix.mulVec inverse basis) row
    have heq : Matrix.mulVec inverse basis row = inverse row column := by
      simp [Matrix.mulVec, dotProduct, basis]
    rw [heq] at hcoordinate
    calc
      |inverse row column| ≤ l2 (Matrix.mulVec inverse basis) := hcoordinate
      _ ≤ l2 basis / ridge := by simpa [inverse] using hcolumn
      _ = 1 / ridge := by rw [hbasis]
  have hsquared := normL2Sq_le_card_mul_sq_of_abs_le
    (fun index : ι × ι ↦ inverse index.1 index.2)
    (by positivity : 0 ≤ (1 : ℝ) / ridge)
    (fun index ↦ hentry index.1 index.2)
  have htargetNonneg : 0 ≤ (Fintype.card ι : ℝ) / ridge := by positivity
  apply normL2_le_of_normL2Sq_le
    (x := fun index : ι × ι ↦ inverse index.1 index.2) htargetNonneg
  calc
    l2Sq (fun index : ι × ι ↦ inverse index.1 index.2) ≤
        (Fintype.card (ι × ι) : ℝ) * ((1 : ℝ) / ridge) ^ 2 := hsquared
    _ = ((Fintype.card ι : ℝ) / ridge) ^ 2 := by
      rw [Fintype.card_prod]
      push_cast
      field_simp

/-- The Euclidean norm of a rank-one coordinate tensor factors. -/
theorem l2_pair_mul_eq_mul
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (first : ι → ℝ) (second : κ → ℝ) :
    l2 (fun index : ι × κ ↦ first index.1 * second index.2) =
      l2 first * l2 second := by
  have hsquare :
      l2Sq (fun index : ι × κ ↦ first index.1 * second index.2) =
        l2Sq first * l2Sq second := by
    simp only [l2Sq, mul_pow]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro coordinate _
    rw [Finset.mul_sum]
  unfold l2
  rw [hsquare, Real.sqrt_mul (normL2Sq_nonneg first)]

/-- A matrix quadratic form is Lipschitz in the entrywise Frobenius metric. -/
theorem abs_quadraticForm_sub_le_matrixL2_mul_l2Sq
    {ι : Type*} [Fintype ι]
    (first second : Matrix ι ι ℝ) (vector : ι → ℝ) :
    |dot vector (Matrix.mulVec first vector) -
        dot vector (Matrix.mulVec second vector)| ≤
      matrixL2 (first - second) * l2Sq vector := by
  have hrewrite :
      dot vector (Matrix.mulVec first vector) -
          dot vector (Matrix.mulVec second vector) =
        dot
          (fun index : ι × ι ↦ (first - second) index.1 index.2)
          (fun index : ι × ι ↦ vector index.1 * vector index.2) := by
    classical
    simp only [dot, Matrix.mulVec, dotProduct, Matrix.sub_apply]
    rw [Fintype.sum_prod_type]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro coordinate _
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro other _
    ring
  rw [hrewrite]
  calc
    |dot
        (fun index : ι × ι ↦ (first - second) index.1 index.2)
        (fun index : ι × ι ↦ vector index.1 * vector index.2)| ≤
        l2 (fun index : ι × ι ↦ (first - second) index.1 index.2) *
          l2 (fun index : ι × ι ↦ vector index.1 * vector index.2) :=
      abs_dot_le_l2_mul_l2 _ _
    _ = matrixL2 (first - second) * l2Sq vector := by
      rw [l2_pair_mul_eq_mul, ← normL2_sq_eq_normL2Sq]
      unfold matrixL2
      ring

/-- The square-root map is globally `1/2`-Hölder once negative inputs are
interpreted using Lean's totalized real square root. -/
theorem abs_sqrt_sub_sqrt_le_sqrt_abs_sub (first second : ℝ) :
    |Real.sqrt first - Real.sqrt second| ≤ Real.sqrt |first - second| := by
  have hnonnegative {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
      |Real.sqrt x - Real.sqrt y| ≤ Real.sqrt |x - y| := by
    rcases le_total x y with hxy | hyx
    · have hsqrt : Real.sqrt x ≤ Real.sqrt y := Real.sqrt_le_sqrt hxy
      have hdifference : 0 ≤ y - x := sub_nonneg.mpr hxy
      have hsquare : (Real.sqrt y - Real.sqrt x) ^ 2 ≤ y - x := by
        have hproduct : x ≤ Real.sqrt x * Real.sqrt y := by
          calc
            x = Real.sqrt x * Real.sqrt x := by
              rw [← sq, Real.sq_sqrt hx]
            _ ≤ Real.sqrt x * Real.sqrt y :=
              mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg x)
        nlinarith [Real.sq_sqrt hy, Real.sq_sqrt hx]
      rw [abs_of_nonpos (sub_nonpos.mpr hsqrt), abs_of_nonpos (sub_nonpos.mpr hxy)]
      simpa only [neg_sub] using
        (Real.le_sqrt (sub_nonneg.mpr hsqrt) hdifference).2 hsquare
    · have hsqrt : Real.sqrt y ≤ Real.sqrt x := Real.sqrt_le_sqrt hyx
      have hdifference : 0 ≤ x - y := sub_nonneg.mpr hyx
      have hsquare : (Real.sqrt x - Real.sqrt y) ^ 2 ≤ x - y := by
        have hproduct : y ≤ Real.sqrt y * Real.sqrt x := by
          calc
            y = Real.sqrt y * Real.sqrt y := by
              rw [← sq, Real.sq_sqrt hy]
            _ ≤ Real.sqrt y * Real.sqrt x :=
              mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg y)
        nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy]
      rw [abs_of_nonneg (sub_nonneg.mpr hsqrt), abs_of_nonneg (sub_nonneg.mpr hyx)]
      exact (Real.le_sqrt (sub_nonneg.mpr hsqrt) hdifference).2 hsquare
  have hsqrtMax (value : ℝ) :
      Real.sqrt value = Real.sqrt (max value 0) := by
    by_cases hvalue : 0 ≤ value
    · rw [max_eq_left hvalue]
    · have hvalueNonpos : value ≤ 0 := le_of_not_ge hvalue
      rw [(Real.sqrt_eq_zero').2 hvalueNonpos]
      rw [max_eq_right hvalueNonpos, Real.sqrt_zero]
  have hmax : |max first 0 - max second 0| ≤ |first - second| := by
    have hlipschitz : LipschitzWith 1 (fun value : ℝ ↦ max value 0) :=
      (LipschitzWith.id.max_const 0)
    have hdist := hlipschitz.dist_le_mul first second
    simpa [Real.dist_eq] using hdist
  rw [hsqrtMax first, hsqrtMax second]
  calc
    |Real.sqrt (max first 0) - Real.sqrt (max second 0)| ≤
        Real.sqrt |max first 0 - max second 0| :=
      hnonnegative (le_max_right _ _) (le_max_right _ _)
    _ ≤ Real.sqrt |first - second| := Real.sqrt_le_sqrt hmax

/-- Square-root quadratic features are Hölder in a matrix's Frobenius
parameter, with the expected factor `‖x‖₂`. -/
theorem abs_sqrt_quadraticForm_sub_le_l2_mul_sqrt_matrixL2
    {ι : Type*} [Fintype ι]
    (first second : Matrix ι ι ℝ) (vector : ι → ℝ) :
    |Real.sqrt (dot vector (Matrix.mulVec first vector)) -
        Real.sqrt (dot vector (Matrix.mulVec second vector))| ≤
      l2 vector * Real.sqrt (matrixL2 (first - second)) := by
  have hquadratic :=
    abs_quadraticForm_sub_le_matrixL2_mul_l2Sq first second vector
  calc
    |Real.sqrt (dot vector (Matrix.mulVec first vector)) -
        Real.sqrt (dot vector (Matrix.mulVec second vector))| ≤
        Real.sqrt
          |dot vector (Matrix.mulVec first vector) -
            dot vector (Matrix.mulVec second vector)| :=
      abs_sqrt_sub_sqrt_le_sqrt_abs_sub _ _
    _ ≤ Real.sqrt (matrixL2 (first - second) * l2Sq vector) :=
      Real.sqrt_le_sqrt hquadratic
    _ = l2 vector * Real.sqrt (matrixL2 (first - second)) := by
      unfold matrixL2
      rw [Real.sqrt_mul (normL2_nonneg
        (fun index : ι × ι ↦ (first - second) index.1 index.2))]
      unfold l2
      ring

end

end QuadraticParameterCover
end Math
end AppliedModelingLib

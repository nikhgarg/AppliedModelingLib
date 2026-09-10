import AppliedModelingLib.Learning.Prediction.Omniprediction
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Fin.Basic

/-!
# Finite threshold basis for bounded proper calibration

On a finite ordered report grid, a bounded proper loss has an antitone
discrete derivative.  This module builds its exact signed-threshold expansion.
It is the finite, executable counterpart of the V-shaped proper-loss basis
used by proper-calibration algorithms.
-/

namespace AppliedModelingLib.Learning.Prediction

open scoped BigOperators

/-- The predecessor of a nonzero finite grid index, retained in the same
grid.  Keeping the ambient grid is convenient for the threshold expansion. -/
def finiteGridPredecessor {gridSize : ℕ} (level : Fin (gridSize + 1))
    (hlevel : level ≠ 0) : Fin (gridSize + 1) :=
  (level.pred hlevel).castSucc

/-- Coefficients of the signed-threshold expansion of a function on a
nonempty finite ordered grid.  The zero-level coefficient is the mean of the
two endpoint values; every later coefficient is one half of the adjacent
finite difference. -/
noncomputable def finiteThresholdBasisCoefficients {gridSize : ℕ}
    (values : Fin (gridSize + 1) → ℝ) (level : Fin (gridSize + 1)) : ℝ :=
  if hlevel : level = 0 then
    (values 0 + values (Fin.last gridSize)) / 2
  else
    (values level - values (finiteGridPredecessor level hlevel)) / 2

@[simp] theorem finiteGridPredecessor_val {gridSize : ℕ}
    (level : Fin (gridSize + 1)) (hlevel : level ≠ 0) :
    (finiteGridPredecessor level hlevel).val = level.val - 1 := rfl

/-- The constant-threshold coordinate is the mean of the endpoint values. -/
@[simp] theorem finiteThresholdBasisCoefficients_zero
    {gridSize : ℕ} (values : Fin (gridSize + 1) → ℝ) :
    finiteThresholdBasisCoefficients values 0 =
      (values 0 + values (Fin.last gridSize)) / 2 := by
  simp [finiteThresholdBasisCoefficients]

/-- Every nonzero coordinate is half of the preceding finite difference. -/
theorem finiteThresholdBasisCoefficients_nonzero
    {gridSize : ℕ} (values : Fin (gridSize + 1) → ℝ)
    (level : Fin (gridSize + 1)) (hlevel : level ≠ 0) :
    finiteThresholdBasisCoefficients values level =
      (values level - values (finiteGridPredecessor level hlevel)) / 2 := by
  simp [finiteThresholdBasisCoefficients, hlevel]

/-- Extend values on a `gridSize + 1` point grid to natural indices.  The
extension agrees with the grid on its range and is constant thereafter; the
latter convention makes ordinary telescoping identities available. -/
noncomputable def finiteGridValueExtension {gridSize : ℕ}
    (values : Fin (gridSize + 1) → ℝ) (index : ℕ) : ℝ :=
  if hindex : index ≤ gridSize then
    values ⟨index, Nat.lt_succ_of_le hindex⟩
  else values (Fin.last gridSize)

@[simp] theorem finiteGridValueExtension_apply
    {gridSize index : ℕ} (values : Fin (gridSize + 1) → ℝ)
    (hindex : index ≤ gridSize) :
    finiteGridValueExtension values index =
      values ⟨index, Nat.lt_succ_of_le hindex⟩ := by
  simp [finiteGridValueExtension, hindex]

@[simp] theorem finiteGridValueExtension_last
    {gridSize : ℕ} (values : Fin (gridSize + 1) → ℝ) :
    finiteGridValueExtension values gridSize = values (Fin.last gridSize) := by
  rw [finiteGridValueExtension_apply values (Nat.le_refl _)]
  congr 1

/-- Natural-index form of a threshold-basis coefficient. -/
theorem finiteThresholdBasisCoefficients_mk
    {gridSize index : ℕ} (values : Fin (gridSize + 1) → ℝ)
    (hindex : index < gridSize + 1) :
    finiteThresholdBasisCoefficients values ⟨index, hindex⟩ =
      if index = 0 then
        (finiteGridValueExtension values 0 +
          finiteGridValueExtension values gridSize) / 2
      else
        (finiteGridValueExtension values index -
          finiteGridValueExtension values (index - 1)) / 2 := by
  have hle : index ≤ gridSize := by omega
  by_cases hzero : index = 0
  · subst index
    rw [finiteGridValueExtension_last]
    simp [finiteThresholdBasisCoefficients, finiteGridValueExtension]
  · have hfin : (⟨index, hindex⟩ : Fin (gridSize + 1)) ≠ 0 := by
      simpa using hzero
    rw [finiteThresholdBasisCoefficients_nonzero values _ hfin]
    simp only [finiteGridValueExtension_apply values hle]
    have hpred : index - 1 ≤ gridSize := by omega
    rw [finiteGridValueExtension_apply values hpred]
    have hpredecessor :
        finiteGridPredecessor (⟨index, hindex⟩ : Fin (gridSize + 1)) hfin =
          ⟨index - 1, Nat.lt_succ_of_le hpred⟩ := by
      apply Fin.ext
      simp [finiteGridPredecessor]
    rw [hpredecessor]
    simp [hzero]

/-- The threshold-basis coefficients add to the terminal grid value.  This is
the telescoping identity underlying the exact threshold expansion. -/
theorem sum_finiteThresholdBasisCoefficients
    {gridSize : ℕ} (values : Fin (gridSize + 1) → ℝ) :
    (∑ level, finiteThresholdBasisCoefficients values level) =
      values (Fin.last gridSize) := by
  let extension := finiteGridValueExtension values
  let increments : ℕ → ℝ := fun index =>
    if index = 0 then extension 0 else extension index - extension (index - 1)
  let endpoint : ℕ → ℝ := fun index => if index = 0 then extension gridSize else 0
  let coefficientNat : ℕ → ℝ := fun index =>
    if hindex : index < gridSize + 1 then
      finiteThresholdBasisCoefficients values ⟨index, hindex⟩
    else 0
  have htelescopes :
      (∑ index ∈ Finset.range (gridSize + 1), increments index) = extension gridSize := by
    simpa [increments] using (Finset.eq_sum_range_sub' extension gridSize).symm
  have hendpoint :
      (∑ index ∈ Finset.range (gridSize + 1), endpoint index) = extension gridSize := by
    simp [endpoint]
  calc
    (∑ level, finiteThresholdBasisCoefficients values level) =
        ∑ index ∈ Finset.range (gridSize + 1), coefficientNat index := by
      calc
        (∑ level, finiteThresholdBasisCoefficients values level) =
            ∑ level : Fin (gridSize + 1), coefficientNat level := by
          apply Finset.sum_congr rfl
          intro level _
          simp [coefficientNat, level.isLt]
        _ = ∑ index ∈ Finset.range (gridSize + 1), coefficientNat index :=
          Fin.sum_univ_eq_sum_range coefficientNat (gridSize + 1)
    _ =
        ∑ index ∈ Finset.range (gridSize + 1),
          (increments index + endpoint index) / 2 := by
      apply Finset.sum_congr rfl
      intro index hindex
      rw [show coefficientNat index =
          finiteThresholdBasisCoefficients values
            ⟨index, Finset.mem_range.mp hindex⟩ by
        simp [coefficientNat, Finset.mem_range.mp hindex]]
      rw [finiteThresholdBasisCoefficients_mk values (Finset.mem_range.mp hindex)]
      by_cases hzero : index = 0
      · subst index
        rw [finiteGridValueExtension_last]
        simp [increments, endpoint, extension]
        congr 1
      · simp [increments, endpoint, extension, hzero]
    _ = ((∑ index ∈ Finset.range (gridSize + 1), increments index) +
        ∑ index ∈ Finset.range (gridSize + 1), endpoint index) / 2 := by
      rw [← Finset.sum_div, Finset.sum_add_distrib]
    _ = (extension gridSize + extension gridSize) / 2 := by
      rw [htelescopes, hendpoint]
    _ = values (Fin.last gridSize) := by
      rw [show extension gridSize = values (Fin.last gridSize) by
        exact finiteGridValueExtension_last values]
      ring

/-- Evaluate the signed threshold expansion at a grid report. -/
noncomputable def finiteThresholdBasisEvaluation {gridSize : ℕ}
    (values : Fin (gridSize + 1) → ℝ) (report : Fin (gridSize + 1)) : ℝ :=
  ∑ level, finiteThresholdBasisCoefficients values level * finiteGridThreshold level report

/-- The threshold expansion has the correct value at the first grid point. -/
theorem finiteThresholdBasisEvaluation_zero
    {gridSize : ℕ} (values : Fin (gridSize + 1) → ℝ) :
    finiteThresholdBasisEvaluation values 0 = values 0 := by
  unfold finiteThresholdBasisEvaluation
  rw [Fin.sum_univ_succ]
  have hsum := sum_finiteThresholdBasisCoefficients values
  rw [Fin.sum_univ_succ] at hsum
  rw [finiteThresholdBasisCoefficients_zero]
  simp [finiteGridThreshold] at hsum ⊢
  linarith

/-- Advancing a grid report by one flips exactly its own signed threshold. -/
theorem finiteGridThreshold_succ_sub
    {gridSize : ℕ} (level : Fin (gridSize + 1)) (report : Fin gridSize) :
    finiteGridThreshold level report.succ - finiteGridThreshold level report.castSucc =
      if level = report.succ then 2 else 0 := by
  by_cases hlevel : level = report.succ
  · subst level
    have hnot : ¬ report.succ ≤ report.castSucc :=
      Fin.not_le.mpr Fin.castSucc_lt_succ
    simp [finiteGridThreshold, hnot]
    norm_num
  · have hiff : level ≤ report.succ ↔ level ≤ report.castSucc := by
      constructor
      · intro hle
        change level.val ≤ report.val + 1 at hle
        change level.val ≤ report.val
        have hval : level.val ≠ report.val + 1 := by
          intro hval
          apply hlevel
          apply Fin.ext
          simpa using hval
        omega
      · intro hle
        change level.val ≤ report.val at hle
        change level.val ≤ report.val + 1
        omega
    simp [finiteGridThreshold, hiff, hlevel]

/-- Advancing the report changes the expansion by the adjacent finite
difference, hence exactly tracks the value function's adjacent change. -/
theorem finiteThresholdBasisEvaluation_succ
    {gridSize : ℕ} (values : Fin (gridSize + 1) → ℝ) (report : Fin gridSize) :
    finiteThresholdBasisEvaluation values report.succ =
      finiteThresholdBasisEvaluation values report.castSucc +
        (values report.succ - values report.castSucc) := by
  unfold finiteThresholdBasisEvaluation
  have hthreshold (level : Fin (gridSize + 1)) :
      finiteGridThreshold level report.succ = finiteGridThreshold level report.castSucc +
        if level = report.succ then 2 else 0 := by
    linarith [finiteGridThreshold_succ_sub level report]
  calc
    (∑ level, finiteThresholdBasisCoefficients values level *
        finiteGridThreshold level report.succ) =
        ∑ level, finiteThresholdBasisCoefficients values level *
          (finiteGridThreshold level report.castSucc +
            if level = report.succ then 2 else 0) := by
      apply Finset.sum_congr rfl
      intro level _
      rw [hthreshold]
    _ = (∑ level, finiteThresholdBasisCoefficients values level *
        finiteGridThreshold level report.castSucc) +
        ∑ level, finiteThresholdBasisCoefficients values level *
          (if level = report.succ then 2 else 0) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
    _ = (∑ level, finiteThresholdBasisCoefficients values level *
        finiteGridThreshold level report.castSucc) +
        2 * finiteThresholdBasisCoefficients values report.succ := by
      simp [mul_ite]
      ring
    _ = (∑ level, finiteThresholdBasisCoefficients values level *
        finiteGridThreshold level report.castSucc) +
        (values report.succ - values report.castSucc) := by
      have hnonzero : report.succ ≠ (0 : Fin (gridSize + 1)) := by
        exact Fin.succ_ne_zero report
      rw [finiteThresholdBasisCoefficients_nonzero values report.succ hnonzero]
      have hpredecessor : finiteGridPredecessor report.succ hnonzero = report.castSucc := by
        apply Fin.ext
        simp [finiteGridPredecessor]
      rw [hpredecessor]
      ring

/-- Every function on a nonempty finite ordered grid is represented exactly
by its signed-threshold coordinates. -/
theorem finiteThresholdBasisEvaluation_eq
    {gridSize : ℕ} (values : Fin (gridSize + 1) → ℝ)
    (report : Fin (gridSize + 1)) :
    finiteThresholdBasisEvaluation values report = values report := by
  induction report using Fin.induction with
  | zero => exact finiteThresholdBasisEvaluation_zero values
  | succ report ih =>
      rw [finiteThresholdBasisEvaluation_succ values report, ih]
      ring

/-- For an antitone value function, every nonconstant threshold coordinate is
nonpositive. -/
theorem finiteThresholdBasisCoefficients_succ_nonpos
    {gridSize : ℕ} (values : Fin (gridSize + 1) → ℝ) (hantitone : Antitone values)
    (level : Fin gridSize) :
    finiteThresholdBasisCoefficients values level.succ ≤ 0 := by
  have hnonzero : level.succ ≠ (0 : Fin (gridSize + 1)) := Fin.succ_ne_zero level
  rw [finiteThresholdBasisCoefficients_nonzero values level.succ hnonzero]
  have hpredecessor : finiteGridPredecessor level.succ hnonzero = level.castSucc := by
    apply Fin.ext
    simp [finiteGridPredecessor]
  rw [hpredecessor]
  have hvalues : values level.succ ≤ values level.castSucc :=
    hantitone (le_of_lt Fin.castSucc_lt_succ)
  linarith

/-- The signed-threshold expansion of an arbitrary finite-grid function has
coefficient mass bounded by its endpoint magnitude plus one half of its total
adjacent variation.  The half is essential because adjacent signed thresholds
differ by two; it is the normalization needed for the paper's Lipschitz and
bounded-variation basis calculations. -/
theorem sum_abs_finiteThresholdBasisCoefficients_le_endpoint_add_halfVariation
    {gridSize : ℕ} (values : Fin (gridSize + 1) → ℝ) (endpointBound variationBound : ℝ)
    (hbounded : ∀ level, |values level| ≤ endpointBound)
    (hvariation :
      (∑ level : Fin gridSize, |values level.succ - values level.castSucc|) ≤ variationBound) :
    (∑ level, |finiteThresholdBasisCoefficients values level|) ≤
      endpointBound + variationBound / 2 := by
  have hboundNonneg : 0 ≤ endpointBound :=
    (abs_nonneg (values 0)).trans (hbounded 0)
  have hzero : |finiteThresholdBasisCoefficients values 0| ≤ endpointBound := by
    rw [finiteThresholdBasisCoefficients_zero]
    calc
      |(values 0 + values (Fin.last gridSize)) / 2| =
          |values 0 + values (Fin.last gridSize)| / 2 := by
            rw [abs_div]
            norm_num
      _ ≤ (|values 0| + |values (Fin.last gridSize)|) / 2 := by
        exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
      _ ≤ (endpointBound + endpointBound) / 2 := by
        gcongr
        · exact hbounded 0
        · exact hbounded (Fin.last gridSize)
      _ = endpointBound := by ring
  have hsuccess :
      (∑ level : Fin gridSize, |finiteThresholdBasisCoefficients values level.succ|) =
        (∑ level : Fin gridSize, |values level.succ - values level.castSucc|) / 2 := by
    calc
      (∑ level : Fin gridSize, |finiteThresholdBasisCoefficients values level.succ|) =
          ∑ level : Fin gridSize, |values level.succ - values level.castSucc| / 2 := by
            apply Finset.sum_congr rfl
            intro level _
            have hpredecessor :
                finiteGridPredecessor level.succ (Fin.succ_ne_zero level) = level.castSucc := by
              apply Fin.ext
              simp [finiteGridPredecessor]
            rw [finiteThresholdBasisCoefficients_nonzero values level.succ
              (Fin.succ_ne_zero level), hpredecessor, abs_div]
            norm_num
      _ = (∑ level : Fin gridSize, |values level.succ - values level.castSucc|) / 2 := by
        rw [Finset.sum_div]
  rw [Fin.sum_univ_succ, hsuccess]
  linarith

/-- Duplicate the constant signed-threshold coordinate.  This converts the
range-two constant coefficient of a bounded loss derivative into two
coefficients in `[-1,1]`, as required by the paper's approximate-basis
definition, without changing its `ℓ¹` mass. -/
noncomputable def duplicatedZeroFiniteThresholdBasisCoefficients {gridSize : ℕ}
    (values : Fin (gridSize + 1) → ℝ) : Fin (gridSize + 2) → ℝ :=
  Fin.cases (finiteThresholdBasisCoefficients values 0 / 2)
    (fun coordinate => Fin.cases (finiteThresholdBasisCoefficients values 0 / 2)
      (fun level => finiteThresholdBasisCoefficients values level.succ) coordinate)

/-- The corresponding duplicated threshold family on a finite grid. -/
def duplicatedZeroFiniteThresholdBasis {gridSize : ℕ} :
    Fin (gridSize + 2) → Fin (gridSize + 1) → ℝ :=
  Fin.cases (finiteGridThreshold 0)
    (fun coordinate => Fin.cases (finiteGridThreshold 0)
      (fun level => finiteGridThreshold level.succ) coordinate)

/-- Duplicate every signed-threshold coordinate.  This is the appropriate
coefficient splitting for proper loss derivatives, whose individual finite
difference coefficients can have magnitude two even though their total
`ℓ¹` mass is small. -/
noncomputable def doubledFiniteThresholdBasisCoefficients {gridSize : ℕ}
    (values : Fin (gridSize + 1) → ℝ) : Fin (2 * (gridSize + 1)) → ℝ :=
  fun coordinate =>
    finiteThresholdBasisCoefficients values (finProdFinEquiv.symm coordinate).2 / 2

/-- The threshold family corresponding to
`doubledFiniteThresholdBasisCoefficients`. -/
def doubledFiniteThresholdBasis {gridSize : ℕ} :
    Fin (2 * (gridSize + 1)) → Fin (gridSize + 1) → ℝ :=
  fun coordinate => finiteGridThreshold (finProdFinEquiv.symm coordinate).2

/-- Splitting every coordinate into two equal copies preserves the exact
finite threshold expansion. -/
theorem doubledFiniteThresholdBasis_evaluation_eq
    {gridSize : ℕ} (values : Fin (gridSize + 1) → ℝ) :
    (fun report => ∑ coordinate,
      doubledFiniteThresholdBasisCoefficients values coordinate *
        doubledFiniteThresholdBasis coordinate report) =
      finiteThresholdBasisEvaluation values := by
  funext report
  calc
    (∑ coordinate,
        doubledFiniteThresholdBasisCoefficients values coordinate *
          doubledFiniteThresholdBasis coordinate report) =
        ∑ coordinate : Fin 2 × Fin (gridSize + 1),
          (finiteThresholdBasisCoefficients values coordinate.2 / 2) *
            finiteGridThreshold coordinate.2 report := by
          apply Fintype.sum_equiv finProdFinEquiv.symm
          intro coordinate
          simp [doubledFiniteThresholdBasisCoefficients, doubledFiniteThresholdBasis]
    _ = ∑ level, finiteThresholdBasisCoefficients values level *
        finiteGridThreshold level report := by
          rw [Fintype.sum_prod_type, Fin.sum_univ_two, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro level _
          ring
    _ = finiteThresholdBasisEvaluation values report := rfl

/-- If every original coefficient has magnitude at most two, the doubled
representation has every coefficient in `[-1,1]`. -/
theorem abs_doubledFiniteThresholdBasisCoefficients_le_one
    {gridSize : ℕ} (values : Fin (gridSize + 1) → ℝ)
    (hcoefficient : ∀ level, |finiteThresholdBasisCoefficients values level| ≤ 2)
    (coordinate : Fin (2 * (gridSize + 1))) :
    |doubledFiniteThresholdBasisCoefficients values coordinate| ≤ 1 := by
  unfold doubledFiniteThresholdBasisCoefficients
  rw [abs_div]
  calc
    |finiteThresholdBasisCoefficients values (finProdFinEquiv.symm coordinate).2| / |2| ≤
        2 / |2| := by
          exact div_le_div_of_nonneg_right
            (hcoefficient (finProdFinEquiv.symm coordinate).2) (abs_nonneg _)
    _ = 1 := by norm_num

/-- Duplicating every coordinate preserves the `ℓ¹` mass of the finite
threshold coefficients. -/
theorem sum_abs_doubledFiniteThresholdBasisCoefficients
    {gridSize : ℕ} (values : Fin (gridSize + 1) → ℝ) :
    (∑ coordinate, |doubledFiniteThresholdBasisCoefficients values coordinate|) =
      ∑ level, |finiteThresholdBasisCoefficients values level| := by
  calc
    (∑ coordinate, |doubledFiniteThresholdBasisCoefficients values coordinate|) =
        ∑ coordinate : Fin 2 × Fin (gridSize + 1),
          |finiteThresholdBasisCoefficients values coordinate.2 / 2| := by
          apply Fintype.sum_equiv finProdFinEquiv.symm
          intro coordinate
          simp [doubledFiniteThresholdBasisCoefficients]
    _ = ∑ level, |finiteThresholdBasisCoefficients values level| := by
          rw [Fintype.sum_prod_type, Fin.sum_univ_two, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro level _
          rw [abs_div]
          norm_num

/-- A finite threshold coefficient has magnitude at most two when all sampled
values lie in `[-2,2]`. -/
theorem abs_finiteThresholdBasisCoefficients_le_two
    {gridSize : ℕ} (values : Fin (gridSize + 1) → ℝ)
    (hbounded : ∀ level, |values level| ≤ 2)
    (coordinate : Fin (gridSize + 1)) :
    |finiteThresholdBasisCoefficients values coordinate| ≤ 2 := by
  refine Fin.cases ?_ (fun level => ?_) coordinate
  · rw [finiteThresholdBasisCoefficients_zero]
    calc
      |(values 0 + values (Fin.last gridSize)) / 2| =
          |values 0 + values (Fin.last gridSize)| / 2 := by
            rw [abs_div]
            norm_num
      _ ≤ (|values 0| + |values (Fin.last gridSize)|) / 2 := by
            exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
      _ ≤ (2 + 2) / 2 := by
            gcongr
            · exact hbounded 0
            · exact hbounded (Fin.last gridSize)
      _ = 2 := by norm_num
  · have hpredecessor :
        finiteGridPredecessor level.succ (Fin.succ_ne_zero level) = level.castSucc := by
      apply Fin.ext
      simp [finiteGridPredecessor]
    rw [finiteThresholdBasisCoefficients_nonzero values level.succ
      (Fin.succ_ne_zero level), hpredecessor, abs_div]
    calc
      |values level.succ - values level.castSucc| / |2| ≤
          (|values level.succ| + |values level.castSucc|) / |2| := by
            apply div_le_div_of_nonneg_right _ (abs_nonneg _)
            simpa [abs_sub_comm] using
              (abs_sub_le (values level.succ) 0 (values level.castSucc))
      _ ≤ (2 + 2) / |2| := by
            gcongr
            · exact hbounded level.succ
            · exact hbounded level.castSucc
      _ = 2 := by norm_num

/-- Duplicating the constant coordinate preserves the exact finite-grid
threshold expansion. -/
theorem duplicatedZeroFiniteThresholdBasis_evaluation_eq
    {gridSize : ℕ} (values : Fin (gridSize + 1) → ℝ) :
    (fun report => ∑ coordinate,
      duplicatedZeroFiniteThresholdBasisCoefficients values coordinate *
        duplicatedZeroFiniteThresholdBasis coordinate report) =
      finiteThresholdBasisEvaluation values := by
  funext report
  unfold duplicatedZeroFiniteThresholdBasisCoefficients
    duplicatedZeroFiniteThresholdBasis finiteThresholdBasisEvaluation
  rw [Fin.sum_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ]
  rw [Fin.sum_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ]
  rw [Fin.sum_univ_succ]
  have hzero : finiteGridThreshold (0 : Fin (gridSize + 1)) report = 1 := by
    simp [finiteGridThreshold]
  rw [hzero]
  ring

/-- Under the source loss range and a total-variation bound of two, every
duplicated threshold coefficient lies in `[-1,1]`. -/
theorem abs_duplicatedZeroFiniteThresholdBasisCoefficients_le_one
    {gridSize : ℕ} (values : Fin (gridSize + 1) → ℝ)
    (hbounded : ∀ level, |values level| ≤ 2)
    (hvariation :
      (∑ level : Fin gridSize, |values level.succ - values level.castSucc|) ≤ 2)
    (coordinate : Fin (gridSize + 2)) :
    |duplicatedZeroFiniteThresholdBasisCoefficients values coordinate| ≤ 1 := by
  have hzeroCoefficient : |finiteThresholdBasisCoefficients values 0| ≤ 2 := by
    rw [finiteThresholdBasisCoefficients_zero]
    calc
      |(values 0 + values (Fin.last gridSize)) / 2| =
          |values 0 + values (Fin.last gridSize)| / 2 := by
            rw [abs_div]
            norm_num
      _ ≤ (|values 0| + |values (Fin.last gridSize)|) / 2 := by
        exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
      _ ≤ (2 + 2) / 2 := by
        gcongr
        · exact hbounded 0
        · exact hbounded (Fin.last gridSize)
      _ = 2 := by norm_num
  have hsplitZero : |finiteThresholdBasisCoefficients values 0 / 2| ≤ 1 := by
    calc
      |finiteThresholdBasisCoefficients values 0 / 2| =
          |finiteThresholdBasisCoefficients values 0| / 2 := by
            rw [abs_div]
            norm_num
      _ ≤ 2 / 2 := by
        exact div_le_div_of_nonneg_right hzeroCoefficient (by norm_num)
      _ = 1 := by norm_num
  refine Fin.cases (by simpa [duplicatedZeroFiniteThresholdBasisCoefficients] using hsplitZero)
    (fun next => Fin.cases (by
      simpa [duplicatedZeroFiniteThresholdBasisCoefficients] using hsplitZero)
      (fun level => ?_) next) coordinate
  · have hpredecessor :
        finiteGridPredecessor level.succ (Fin.succ_ne_zero level) = level.castSucc := by
      apply Fin.ext
      simp [finiteGridPredecessor]
    have hterm : |values level.succ - values level.castSucc| ≤
        ∑ index : Fin gridSize, |values index.succ - values index.castSucc| := by
      exact Finset.single_le_sum
        (s := Finset.univ)
        (f := fun index : Fin gridSize =>
          |values index.succ - values index.castSucc|)
        (fun index _ => abs_nonneg _) (Finset.mem_univ level)
    have hsuccess : |finiteThresholdBasisCoefficients values level.succ| ≤ 1 := by
      rw [finiteThresholdBasisCoefficients_nonzero values level.succ
        (Fin.succ_ne_zero level), hpredecessor, abs_div]
      norm_num
      linarith [hterm.trans hvariation]
    simpa [duplicatedZeroFiniteThresholdBasisCoefficients] using hsuccess

/-- Duplicating the constant coordinate leaves the threshold coefficient
`ℓ¹` mass unchanged. -/
theorem sum_abs_duplicatedZeroFiniteThresholdBasisCoefficients
    {gridSize : ℕ} (values : Fin (gridSize + 1) → ℝ) :
    (∑ coordinate, |duplicatedZeroFiniteThresholdBasisCoefficients values coordinate|) =
      ∑ level, |finiteThresholdBasisCoefficients values level| := by
  unfold duplicatedZeroFiniteThresholdBasisCoefficients
  rw [Fin.sum_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ]
  rw [Fin.sum_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ]
  rw [Fin.sum_univ_succ]
  simp only [abs_div]
  norm_num
  ring

/-- The repaired finite-grid threshold representation of a bounded-variation
loss derivative has coefficient mass at most three. -/
theorem sum_abs_duplicatedZeroFiniteThresholdBasisCoefficients_le_three
    {gridSize : ℕ} (values : Fin (gridSize + 1) → ℝ)
    (hbounded : ∀ level, |values level| ≤ 2)
    (hvariation :
      (∑ level : Fin gridSize, |values level.succ - values level.castSucc|) ≤ 2) :
    (∑ coordinate, |duplicatedZeroFiniteThresholdBasisCoefficients values coordinate|) ≤ 3 := by
  rw [sum_abs_duplicatedZeroFiniteThresholdBasisCoefficients]
  have hmass := sum_abs_finiteThresholdBasisCoefficients_le_endpoint_add_halfVariation
    values 2 2 hbounded hvariation
  norm_num at hmass ⊢
  exact hmass

/-- A bounded antitone grid function has a signed-threshold representation
whose coefficient `ℓ¹` mass is at most its endpoint bound.  For a source loss
bounded in `[-1,1]`, the discrete derivative has endpoint bound `2`, which is
the constant needed by the finite proper-calibration reduction. -/
theorem sum_abs_finiteThresholdBasisCoefficients_le_two
    {gridSize : ℕ} (values : Fin (gridSize + 1) → ℝ) (hantitone : Antitone values)
    (hbounded : ∀ level, |values level| ≤ 2) :
    (∑ level, |finiteThresholdBasisCoefficients values level|) ≤ 2 := by
  have hnegatives :
      (∑ level : Fin gridSize, |finiteThresholdBasisCoefficients values level.succ|) =
        -(∑ level : Fin gridSize, finiteThresholdBasisCoefficients values level.succ) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro level _
    rw [abs_of_nonpos (finiteThresholdBasisCoefficients_succ_nonpos values hantitone level)]
  have hsum := sum_finiteThresholdBasisCoefficients values
  rw [Fin.sum_univ_succ] at hsum ⊢
  rw [hnegatives]
  rw [finiteThresholdBasisCoefficients_zero] at hsum ⊢
  have hfirst := hbounded (0 : Fin (gridSize + 1))
  have hlast := hbounded (Fin.last gridSize)
  rw [abs_le] at hfirst hlast
  by_cases hmean : 0 ≤ (values 0 + values (Fin.last gridSize)) / 2
  · rw [abs_of_nonneg hmean]
    linarith
  · have hmean' : (values 0 + values (Fin.last gridSize)) / 2 ≤ 0 := le_of_not_ge hmean
    rw [abs_of_nonpos hmean']
    linarith

/-- The discrete derivative of a proper loss remains antitone after
restriction to any monotone grid of valid reports. -/
theorem properDerivative_values_antitone
    {gridSize : ℕ} {loss : BinaryLoss} (grid : Fin (gridSize + 1) → ℝ)
    (hproper : IsProperBinaryLoss loss) (hgrid : Monotone grid)
    (hvalid : ∀ level, grid level ∈ Set.Icc (0 : ℝ) 1) :
    Antitone (fun level => discreteDerivative loss (grid level)) := by
  intro lower upper hlowerUpper
  exact discreteDerivative_antitone_of_proper hproper (hvalid lower) (hvalid upper)
    (hgrid hlowerUpper)

/-- The signed-threshold expansion of a bounded proper loss's derivative on
a valid monotone grid has coefficient mass at most two. -/
theorem properDerivative_thresholdBasis_mass_le_two
    {gridSize : ℕ} {loss : BinaryLoss} (grid : Fin (gridSize + 1) → ℝ)
    (hproper : IsProperBinaryLoss loss) (hbounded : IsUnitBoundedBinaryLoss loss)
    (hgrid : Monotone grid) (hvalid : ∀ level, grid level ∈ Set.Icc (0 : ℝ) 1) :
    (∑ level, |finiteThresholdBasisCoefficients
      (fun level => discreteDerivative loss (grid level)) level|) ≤ 2 := by
  apply sum_abs_finiteThresholdBasisCoefficients_le_two
  · exact properDerivative_values_antitone grid hproper hgrid hvalid
  · intro level
    exact discreteDerivative_abs_le_two_of_unitBounded hbounded (hvalid level)

/-- Any finite signed-threshold expansion whose coefficients have the
proper-loss mass bound is controlled by the largest coordinate correlation.
Unlike `finiteGridValueCorrelation`, the coordinates here are arbitrary real
numbers; this permits the same basis argument after taking conditional
population expectations. -/
theorem abs_thresholdBasisExpansion_le_two_mul
    {gridSize : ℕ} (values scores : Fin (gridSize + 1) → ℝ)
    (hantitone : Antitone values) (hbounded : ∀ level, |values level| ≤ 2)
    (bound : ℝ) (hscores : ∀ level, |scores level| ≤ bound) :
    |∑ level, finiteThresholdBasisCoefficients values level * scores level| ≤ 2 * bound := by
  have hboundNonneg : 0 ≤ bound := by
    exact (abs_nonneg (scores 0)).trans (hscores 0)
  calc
    |∑ level, finiteThresholdBasisCoefficients values level * scores level| ≤
        ∑ level, |finiteThresholdBasisCoefficients values level * scores level| := by
      simpa using (Finset.abs_sum_le_sum_abs
        (fun level => finiteThresholdBasisCoefficients values level * scores level) Finset.univ)
    _ = ∑ level, |finiteThresholdBasisCoefficients values level| * |scores level| := by
      apply Finset.sum_congr rfl
      intro level _
      rw [abs_mul]
    _ ≤ ∑ level, |finiteThresholdBasisCoefficients values level| * bound := by
      apply Finset.sum_le_sum
      intro level _
      exact mul_le_mul_of_nonneg_left (hscores level) (abs_nonneg _)
    _ = bound * ∑ level, |finiteThresholdBasisCoefficients values level| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro level _
      ring
    _ ≤ bound * 2 := by
      exact mul_le_mul_of_nonneg_left
        (sum_abs_finiteThresholdBasisCoefficients_le_two values hantitone hbounded)
        hboundNonneg
    _ = 2 * bound := by ring

/-- Correlation of a grid-indexed value function with an arbitrary residual
sequence. -/
noncomputable def finiteGridValueCorrelation {gridSize horizon : ℕ}
    (values : Fin (gridSize + 1) → ℝ) (reports : Fin horizon → Fin (gridSize + 1))
    (residuals : Fin horizon → ℝ) : ℝ :=
  ∑ round, values (reports round) * residuals round

/-- Correlation of one signed threshold coordinate with the same residual
sequence. -/
noncomputable def finiteGridThresholdCorrelation {gridSize horizon : ℕ}
    (level : Fin (gridSize + 1)) (reports : Fin horizon → Fin (gridSize + 1))
    (residuals : Fin horizon → ℝ) : ℝ :=
  ∑ round, finiteGridThreshold level (reports round) * residuals round

/-- Exact interchange of the threshold-basis expansion with a finite
correlation sum. -/
theorem finiteGridValueCorrelation_eq_thresholdExpansion
    {gridSize horizon : ℕ} (values : Fin (gridSize + 1) → ℝ)
    (reports : Fin horizon → Fin (gridSize + 1)) (residuals : Fin horizon → ℝ) :
    finiteGridValueCorrelation values reports residuals =
      ∑ level, finiteThresholdBasisCoefficients values level *
        finiteGridThresholdCorrelation level reports residuals := by
  unfold finiteGridValueCorrelation finiteGridThresholdCorrelation
  calc
    (∑ round, values (reports round) * residuals round) =
        ∑ round, (∑ level, finiteThresholdBasisCoefficients values level *
          finiteGridThreshold level (reports round)) * residuals round := by
      apply Finset.sum_congr rfl
      intro round _
      rw [← finiteThresholdBasisEvaluation_eq values (reports round)]
      rfl
    _ = ∑ level, finiteThresholdBasisCoefficients values level *
        ∑ round, finiteGridThreshold level (reports round) * residuals round := by
      calc
        (∑ round, (∑ level, finiteThresholdBasisCoefficients values level *
          finiteGridThreshold level (reports round)) * residuals round) =
            ∑ round, ∑ level, (finiteThresholdBasisCoefficients values level *
              finiteGridThreshold level (reports round)) * residuals round := by
          apply Finset.sum_congr rfl
          intro round _
          rw [Finset.sum_mul]
        _ = ∑ level, ∑ round, (finiteThresholdBasisCoefficients values level *
            finiteGridThreshold level (reports round)) * residuals round := Finset.sum_comm
        _ = ∑ level, finiteThresholdBasisCoefficients values level *
            ∑ round, finiteGridThreshold level (reports round) * residuals round := by
          apply Finset.sum_congr rfl
          intro level _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro round _
          ring

/-- Coordinate-wise control of signed threshold correlations controls every
bounded antitone grid value correlation, with the sharp factor two inherited
from the derivative range. -/
theorem abs_finiteGridValueCorrelation_le_two_mul
    {gridSize horizon : ℕ} (values : Fin (gridSize + 1) → ℝ)
    (reports : Fin horizon → Fin (gridSize + 1)) (residuals : Fin horizon → ℝ)
    (hantitone : Antitone values) (hbounded : ∀ level, |values level| ≤ 2)
    (bound : ℝ)
    (hthreshold : ∀ level,
      |finiteGridThresholdCorrelation level reports residuals| ≤ bound) :
    |finiteGridValueCorrelation values reports residuals| ≤ 2 * bound := by
  have hboundNonneg : 0 ≤ bound := by
    exact (abs_nonneg (finiteGridThresholdCorrelation (0 : Fin (gridSize + 1))
      reports residuals)).trans (hthreshold 0)
  rw [finiteGridValueCorrelation_eq_thresholdExpansion]
  calc
    |∑ level, finiteThresholdBasisCoefficients values level *
        finiteGridThresholdCorrelation level reports residuals| ≤
        ∑ level, |finiteThresholdBasisCoefficients values level *
          finiteGridThresholdCorrelation level reports residuals| := by
      simpa using (Finset.abs_sum_le_sum_abs
        (fun level => finiteThresholdBasisCoefficients values level *
          finiteGridThresholdCorrelation level reports residuals) Finset.univ)
    _ = ∑ level, |finiteThresholdBasisCoefficients values level| *
        |finiteGridThresholdCorrelation level reports residuals| := by
      apply Finset.sum_congr rfl
      intro level _
      rw [abs_mul]
    _ ≤ ∑ level, |finiteThresholdBasisCoefficients values level| * bound := by
      apply Finset.sum_le_sum
      intro level _
      exact mul_le_mul_of_nonneg_left (hthreshold level) (abs_nonneg _)
    _ = bound * ∑ level, |finiteThresholdBasisCoefficients values level| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro level _
      ring
    _ ≤ bound * 2 := by
      exact mul_le_mul_of_nonneg_left
        (sum_abs_finiteThresholdBasisCoefficients_le_two values hantitone hbounded)
        hboundNonneg
    _ = 2 * bound := by ring

end AppliedModelingLib.Learning.Prediction

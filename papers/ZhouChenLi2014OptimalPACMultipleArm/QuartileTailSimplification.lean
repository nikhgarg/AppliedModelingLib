import ZhouChenLi2014OptimalPACMultipleArm.QuartileBatch

/-!
# A usable finite tail envelope for Quartile-Elimination

The source proof specializes its two-term one-round Chernoff expression by a
numerical choice of the Hoeffding factor.  This file supplies a transparent
finite version for the tie-broken `K = 1` stage: when that factor is at most
`exp (-2)`, the complete QE failure probability is at most twice it.
-/

namespace ZhouChenLi2014OptimalPACMultipleArm

open AppliedModelingLib
open MeasureTheory ProbabilityTheory

/-- The rounded tie-broken survivor count is at least three quarters of its input. -/
theorem three_quarters_mul_activeCount_le_quartileSurvivorCount
    (activeCount : ℕ) :
    (3 / 4 : ℝ) * (activeCount : ℝ) ≤ (quartileSurvivorCount activeCount : ℝ) := by
  have hnat : 3 * activeCount ≤ 4 * quartileSurvivorCount activeCount := by
    unfold quartileSurvivorCount
    omega
  have hreal : 3 * (activeCount : ℝ) ≤ 4 * (quartileSurvivorCount activeCount : ℝ) := by
    exact_mod_cast hnat
  nlinarith

/--
At an active-set size of at least four, the Chernoff term obtained by setting
`t = -log q` is at most `q` whenever `q ≤ exp (-2)`.
-/
theorem quartileSurvivorChernoffTail_le_hoeffding
    (activeCount : ℕ) (hactiveCount : 4 ≤ activeCount)
    (q : ℝ) (hqpos : 0 < q) (hsmall : q ≤ Real.exp (-2)) :
    Real.exp (-(-Real.log q) * (quartileSurvivorCount activeCount : ℝ) +
      (activeCount : ℝ) * ((Real.exp (-Real.log q) - 1) * q)) ≤ q := by
  let s : ℝ := activeCount
  let k : ℝ := quartileSurvivorCount activeCount
  let L : ℝ := -Real.log q
  have hqnonneg : 0 ≤ q := hqpos.le
  have hlog : Real.log q ≤ -2 := by
    apply (Real.log_le_iff_le_exp hqpos).mpr
    simpa using hsmall
  have hL : 2 ≤ L := by
    dsimp [L]
    linarith
  have hs : 4 ≤ s := by
    dsimp [s]
    exact_mod_cast hactiveCount
  have hsnonneg : 0 ≤ s := by
    dsimp [s]
    positivity
  have hk : (3 / 4 : ℝ) * s ≤ k := by
    dsimp [s, k]
    exact three_quarters_mul_activeCount_le_quartileSurvivorCount activeCount
  have hfactor : (Real.exp (-Real.log q) - 1) * q = 1 - q := by
    rw [Real.exp_neg, Real.exp_log hqpos]
    field_simp [hqpos.ne']
  have hfirstTerm : -L * k ≤ -L * ((3 / 4 : ℝ) * s) := by
    exact mul_le_mul_of_nonpos_left hk (by linarith)
  have hsecondTerm : s * (1 - q) ≤ s := by
    calc
      s * (1 - q) ≤ s * 1 :=
        mul_le_mul_of_nonneg_left (by linarith) hsnonneg
      _ = s := by ring
  have hpre : -L * k + s * (1 - q) ≤ -L * ((3 / 4 : ℝ) * s) + s :=
    add_le_add hfirstTerm hsecondTerm
  have hcoefficientNonneg : 0 ≤ (3 / 4 : ℝ) * L - 1 := by linarith
  have hscale : 4 * ((3 / 4 : ℝ) * L - 1) ≤
      s * ((3 / 4 : ℝ) * L - 1) :=
    mul_le_mul_of_nonneg_right hs hcoefficientNonneg
  have hfinal : -L * ((3 / 4 : ℝ) * s) + s ≤ -L := by
    nlinarith [hscale]
  have hexponent :
      -(-Real.log q) * k + s * ((Real.exp (-Real.log q) - 1) * q) ≤ Real.log q := by
    calc
      -(-Real.log q) * k + s * ((Real.exp (-Real.log q) - 1) * q) =
          -L * k + s * (1 - q) := by rw [hfactor]
      _ ≤ -L * ((3 / 4 : ℝ) * s) + s := hpre
      _ ≤ -L := hfinal
      _ = Real.log q := by simp [L]
  calc
    Real.exp (-(-Real.log q) * (quartileSurvivorCount activeCount : ℝ) +
        (activeCount : ℝ) * ((Real.exp (-Real.log q) - 1) * q)) =
        Real.exp (-(-Real.log q) * k + s * ((Real.exp (-Real.log q) - 1) * q)) := by
          rfl
    _ ≤ Real.exp (Real.log q) := Real.exp_le_exp.mpr hexponent
    _ = q := Real.exp_log hqpos

/--
The source-shaped QE tail has a one-term envelope at every nontrivial active
set once its individual Hoeffding factor is at most `exp (-2)`.
-/
theorem quartileEliminationFromBatch_no_near_maximum_probability_le_two_hoeffding
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean) (active : Finset Arm)
    (reference : active) (hmaximum : ∀ competitor : active, mean competitor.val ≤ mean reference.val)
    (sampleCount : ℕ) (hcount : 0 < sampleCount) (error : ℝ) (herror : 0 ≤ error)
    (hactiveSize : 4 ≤ active.card)
    (hsmall : Real.exp (-((sampleCount : ℝ) * error) ^ 2 /
      (2 * (sampleCount : ℝ) * (1 / 4 : ℝ))) ≤ Real.exp (-2)) :
    (quartileBernoulliBatchLaw mean hmean active sampleCount).toMeasure.real
      {batchTable | ¬ ∃ survivor, survivor ∈
          quartileEliminationFromBatch active sampleCount batchTable ∧
        mean reference.val - 2 * error ≤ mean survivor} ≤
      2 * Real.exp (-((sampleCount : ℝ) * error) ^ 2 /
        (2 * (sampleCount : ℝ) * (1 / 4 : ℝ))) := by
  let q : ℝ := Real.exp (-((sampleCount : ℝ) * error) ^ 2 /
    (2 * (sampleCount : ℝ) * (1 / 4 : ℝ)))
  let s : ℝ := active.card
  let k : ℝ := quartileSurvivorCount active.card
  let L : ℝ := -Real.log q
  have hqpos : 0 < q := Real.exp_pos _
  have hqnonneg : 0 ≤ q := hqpos.le
  have hlog : Real.log q ≤ -2 := by
    apply (Real.log_le_iff_le_exp hqpos).mpr
    simpa [q] using hsmall
  have hL : 2 ≤ L := by
    dsimp [L]
    linarith
  have ht : 0 ≤ -Real.log q := by linarith
  have hs : 4 ≤ s := by
    dsimp [s]
    exact_mod_cast hactiveSize
  have hsnonneg : 0 ≤ s := by
    dsimp [s]
    positivity
  have hk : (3 / 4 : ℝ) * s ≤ k := by
    dsimp [s, k]
    exact three_quarters_mul_activeCount_le_quartileSurvivorCount active.card
  have hfactor : (Real.exp (-Real.log q) - 1) * q = 1 - q := by
    rw [Real.exp_neg, Real.exp_log hqpos]
    field_simp [hqpos.ne']
  have hfirstTerm : -L * k ≤ -L * ((3 / 4 : ℝ) * s) := by
    exact mul_le_mul_of_nonpos_left hk (by linarith)
  have hsecondTerm : s * (1 - q) ≤ s := by
    calc
      s * (1 - q) ≤ s * 1 :=
        mul_le_mul_of_nonneg_left (by linarith) hsnonneg
      _ = s := by ring
  have hpre : -L * k + s * (1 - q) ≤ -L * ((3 / 4 : ℝ) * s) + s :=
    add_le_add hfirstTerm hsecondTerm
  have hcoefficientNonneg : 0 ≤ (3 / 4 : ℝ) * L - 1 := by linarith
  have hscale : 4 * ((3 / 4 : ℝ) * L - 1) ≤
      s * ((3 / 4 : ℝ) * L - 1) :=
    mul_le_mul_of_nonneg_right hs hcoefficientNonneg
  have hfinal : -L * ((3 / 4 : ℝ) * s) + s ≤ -L := by
    nlinarith [hscale]
  have hexponent :
      -(-Real.log q) * k + s * ((Real.exp (-Real.log q) - 1) * q) ≤ Real.log q := by
    calc
      -(-Real.log q) * k + s * ((Real.exp (-Real.log q) - 1) * q) =
          -L * k + s * (1 - q) := by rw [hfactor]
      _ ≤ -L * ((3 / 4 : ℝ) * s) + s := hpre
      _ ≤ -L := hfinal
      _ = Real.log q := by simp [L]
  have hsecond :
      Real.exp (-(-Real.log q) * k + s * ((Real.exp (-Real.log q) - 1) * q)) ≤ q := by
    calc
      Real.exp (-(-Real.log q) * k + s * ((Real.exp (-Real.log q) - 1) * q)) ≤
          Real.exp (Real.log q) := Real.exp_le_exp.mpr hexponent
      _ = q := Real.exp_log hqpos
  have hbase := quartileEliminationFromBatch_no_near_maximum_probability mean hmean active
    reference hmaximum sampleCount hcount error (-Real.log q) herror ht
  calc
    (quartileBernoulliBatchLaw mean hmean active sampleCount).toMeasure.real
        {batchTable | ¬ ∃ survivor, survivor ∈
            quartileEliminationFromBatch active sampleCount batchTable ∧
          mean reference.val - 2 * error ≤ mean survivor} ≤
        q + Real.exp (-(-Real.log q) * k +
          s * ((Real.exp (-Real.log q) - 1) * q)) := by
            simpa [q, s, k] using hbase
    _ ≤ q + q := by linarith
    _ = 2 * q := by ring
    _ = _ := by rfl

end ZhouChenLi2014OptimalPACMultipleArm

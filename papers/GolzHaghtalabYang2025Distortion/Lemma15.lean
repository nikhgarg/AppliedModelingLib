import AppliedModelingLib.Alignment.Welfare.SigmoidBounds
import Mathlib.Analysis.SpecialFunctions.Artanh

open scoped Topology

/-!
# Appendix-G Lemma 15 construction ingredients

This module begins the exact three-user recursive construction in Appendix G.
Its first layer records the analytic increment chosen in the source proof and
proves the strict inequalities that make each recursive welfare decrease and
strict adjacent preference possible.
-/

namespace GolzHaghtalabYang2025Distortion

/--
The source's Appendix-G upward increment `Δ'` as a function of the dropped
coordinate's scaled utility `Δ`.  It is the logarithm displayed immediately
after the recursive definition of `u_A(a_t), u_B(a_t), u_C(a_t)`.
-/
noncomputable def lemma15Increment (delta : ℝ) : ℝ :=
  Real.log ((Real.exp (delta / 2) + 1) ^ 3 /
    (2 * (Real.exp delta + 3)))

/-- Rewriting the full exponential at `delta` through its half exponential. -/
theorem lemma15_exp_eq_exp_half_sq (delta : ℝ) :
    Real.exp delta = Real.exp (delta / 2) ^ 2 := by
  rw [show delta = delta / 2 + delta / 2 by ring, Real.exp_add]
  ring

/-- The Appendix-G increment is strictly positive at every positive gap. -/
theorem lemma15_increment_pos {delta : ℝ} (hdelta : 0 < delta) :
    0 < lemma15Increment delta := by
  let e : ℝ := Real.exp (delta / 2)
  have he_pos : 0 < e := by
    dsimp [e]
    exact Real.exp_pos _
  have he_one : 1 < e := by
    dsimp [e]
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hexp : Real.exp delta = e ^ 2 := by
    simpa [e] using lemma15_exp_eq_exp_half_sq delta
  have hden_pos : 0 < 2 * (Real.exp delta + 3) := by positivity
  have hpoly_pos : 0 < (e - 1) * (e ^ 2 + 2 * e + 5) := by
    apply mul_pos
    · linarith
    · nlinarith [sq_nonneg e]
  have hratio_gt_one :
      1 < (Real.exp (delta / 2) + 1) ^ 3 /
        (2 * (Real.exp delta + 3)) := by
    apply (lt_div_iff₀ hden_pos).2
    rw [hexp]
    dsimp [e] at hpoly_pos ⊢
    nlinarith
  exact Real.log_pos hratio_gt_one

/-- The Appendix-G increment is strictly below half the dropped gap. -/
theorem lemma15_increment_lt_half {delta : ℝ} (hdelta : 0 < delta) :
    lemma15Increment delta < delta / 2 := by
  let e : ℝ := Real.exp (delta / 2)
  have he_pos : 0 < e := by
    dsimp [e]
    exact Real.exp_pos _
  have he_one : 1 < e := by
    dsimp [e]
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hexp : Real.exp delta = e ^ 2 := by
    simpa [e] using lemma15_exp_eq_exp_half_sq delta
  have hden_pos : 0 < 2 * (Real.exp delta + 3) := by positivity
  have hratio_pos : 0 <
      (Real.exp (delta / 2) + 1) ^ 3 /
        (2 * (Real.exp delta + 3)) := by positivity
  have hcube_pos : 0 < (e - 1) ^ 3 := pow_pos (by linarith) _
  have hratio_lt_e :
      (Real.exp (delta / 2) + 1) ^ 3 /
        (2 * (Real.exp delta + 3)) < e := by
    apply (div_lt_iff₀ hden_pos).2
    rw [hexp]
    dsimp [e] at hcube_pos ⊢
    nlinarith
  unfold lemma15Increment
  calc
    Real.log ((Real.exp (delta / 2) + 1) ^ 3 /
        (2 * (Real.exp delta + 3))) < Real.log e :=
      Real.strictMonoOn_log hratio_pos he_pos hratio_lt_e
    _ = delta / 2 := by
      dsimp [e]
      exact Real.log_exp _

/--
The strict lower logarithmic bound on the increment used in the source's
adjacent-preference calculation (its Eq. (21)).
-/
theorem lemma15_log_source_ratio_lt_increment {delta : ℝ} (hdelta : 0 < delta) :
    Real.log ((3 * Real.exp delta + 1) / (Real.exp delta + 3)) <
      lemma15Increment delta := by
  let e : ℝ := Real.exp (delta / 2)
  have he_pos : 0 < e := by
    dsimp [e]
    exact Real.exp_pos _
  have he_one : 1 < e := by
    dsimp [e]
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hexp : Real.exp delta = e ^ 2 := by
    simpa [e] using lemma15_exp_eq_exp_half_sq delta
  have hbase_pos : 0 < Real.exp delta + 3 := by positivity
  have hden_pos : 0 < 2 * (Real.exp delta + 3) := by positivity
  have hleft_pos : 0 < (3 * Real.exp delta + 1) / (Real.exp delta + 3) := by
    positivity
  have hright_pos : 0 <
      (Real.exp (delta / 2) + 1) ^ 3 /
        (2 * (Real.exp delta + 3)) := by positivity
  have hcube_pos : 0 < (e - 1) ^ 3 := pow_pos (by linarith) _
  have hratio_lt :
      (3 * Real.exp delta + 1) / (Real.exp delta + 3) <
        (Real.exp (delta / 2) + 1) ^ 3 /
          (2 * (Real.exp delta + 3)) := by
    have hleft_rewrite :
        (3 * Real.exp delta + 1) / (Real.exp delta + 3) =
          (2 * (3 * Real.exp delta + 1)) /
            (2 * (Real.exp delta + 3)) := by
      field_simp [ne_of_gt hbase_pos, ne_of_gt hden_pos]
    rw [hleft_rewrite]
    apply (div_lt_div_iff₀ hden_pos hden_pos).2
    rw [hexp]
    dsimp [e] at hcube_pos ⊢
    nlinarith
  unfold lemma15Increment
  exact Real.strictMonoOn_log hleft_pos hright_pos hratio_lt

/-- A convenient exponential form of the Bradley--Terry sigmoid. -/
theorem lemma15_sigmoid_eq_exp_div_one_add_exp (z : ℝ) :
    Real.sigmoid z = Real.exp z / (1 + Real.exp z) := by
  rw [Real.sigmoid_def, Real.exp_neg]
  field_simp [ne_of_gt (Real.exp_pos z)]
  ring

/--
The source increment makes the next alternative strictly preferred to the
previous one by the uniform three-user population.  This is the final
algebraic line of Appendix G's Lemma 15 proof, before the recursive sequence
is introduced.
-/
theorem lemma15_adjacent_sigmoid_advantage {delta : ℝ} (hdelta : 0 < delta) :
    (1 : ℝ) / 2 <
      (Real.sigmoid (-delta) + 2 * Real.sigmoid (lemma15Increment delta)) / 3 := by
  let x : ℝ := Real.exp delta
  let q : ℝ := Real.exp (lemma15Increment delta)
  have hx_pos : 0 < x := by
    dsimp [x]
    exact Real.exp_pos _
  have hx_one : 1 < x := by
    dsimp [x]
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr hdelta
  have hx_plus_three_pos : 0 < x + 3 := by positivity
  have hsource_log := lemma15_log_source_ratio_lt_increment hdelta
  have hratio_pos : 0 < (3 * x + 1) / (x + 3) := by positivity
  have hq_gt : (3 * x + 1) / (x + 3) < q := by
    have hsource_ratio_pos : 0 <
        (3 * Real.exp delta + 1) / (Real.exp delta + 3) := by positivity
    have hsource_exp :
        Real.exp (Real.log ((3 * Real.exp delta + 1) /
          (Real.exp delta + 3))) < Real.exp (lemma15Increment delta) :=
      Real.exp_lt_exp.mpr hsource_log
    rw [Real.exp_log hsource_ratio_pos] at hsource_exp
    simpa [x, q] using hsource_exp
  have hq_pos : 0 < q := by
    dsimp [q]
    exact Real.exp_pos _
  have hscaled : 3 * x + 1 < q * (x + 3) :=
    (div_lt_iff₀ hx_plus_three_pos).1 hq_gt
  have hneg_sigmoid : Real.sigmoid (-delta) = 1 / (1 + x) := by
    rw [lemma15_sigmoid_eq_exp_div_one_add_exp, Real.exp_neg]
    dsimp [x]
    field_simp [ne_of_gt hx_pos]
    ring
  have hinc_sigmoid : Real.sigmoid (lemma15Increment delta) = q / (1 + q) := by
    rw [lemma15_sigmoid_eq_exp_div_one_add_exp]
  rw [hneg_sigmoid, hinc_sigmoid]
  apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 3)).2
  field_simp [ne_of_gt hx_pos, ne_of_gt hq_pos]
  nlinarith

/-- A highest coordinate of a three-user utility vector. -/
noncomputable def lemma15Peak (utility : Fin 3 → ℝ) : Fin 3 :=
  Classical.choose (Finset.exists_max_image Finset.univ utility (by simp))

/-- The chosen `lemma15Peak` is at least every coordinate. -/
theorem lemma15_le_peak (utility : Fin 3 → ℝ) (user : Fin 3) :
    utility user ≤ utility (lemma15Peak utility) := by
  classical
  exact (Classical.choose_spec
    (Finset.exists_max_image Finset.univ utility (by simp))).2 user (by simp)

/--
The source update at one alternative: reset a chosen highest coordinate and
increase the other two by a common amount.
-/
def lemma15DropAdd (utility : Fin 3 → ℝ) (peak : Fin 3) (increment : ℝ) :
    Fin 3 → ℝ :=
  fun user => if user = peak then 0 else utility user + increment

/-- The sum after the three-coordinate source update. -/
theorem lemma15_dropAdd_sum (utility : Fin 3 → ℝ) (peak : Fin 3) (increment : ℝ) :
    (∑ user : Fin 3, lemma15DropAdd utility peak increment user) =
      (∑ user : Fin 3, utility user) - utility peak + 2 * increment := by
  fin_cases peak <;>
    simp [lemma15DropAdd, Fin.sum_univ_three] <;>
    ring

/-- Nonnegativity is preserved by the source update with a nonnegative increment. -/
theorem lemma15_dropAdd_nonneg {utility : Fin 3 → ℝ} {peak : Fin 3} {increment : ℝ}
    (hnonneg : ∀ user, 0 ≤ utility user) (hincrement : 0 ≤ increment) :
    ∀ user, 0 ≤ lemma15DropAdd utility peak increment user := by
  intro user
  by_cases huser : user = peak
  · simp [lemma15DropAdd, huser]
  · simp only [lemma15DropAdd, if_neg huser]
    exact add_nonneg (hnonneg user) hincrement

/--
If `peak` is maximal and the three coordinates are nonnegative with total at
most one, either other coordinate is at most one half.
-/
theorem lemma15_other_le_half {utility : Fin 3 → ℝ} {peak user : Fin 3}
    (hnonneg : ∀ coordinate, 0 ≤ utility coordinate)
    (htotal : (∑ coordinate : Fin 3, utility coordinate) ≤ 1)
    (hpeak : ∀ coordinate, utility coordinate ≤ utility peak)
    (huser : user ≠ peak) :
    utility user ≤ (1 : ℝ) / 2 := by
  fin_cases peak <;> fin_cases user <;>
    simp_all [Fin.sum_univ_three] <;>
    nlinarith [hpeak (0 : Fin 3), hpeak (1 : Fin 3), hpeak (2 : Fin 3),
      hnonneg (0 : Fin 3), hnonneg (1 : Fin 3), hnonneg (2 : Fin 3)]

/-- A maximal coordinate is bounded by the total of a nonnegative utility vector. -/
theorem lemma15_peak_le_total {utility : Fin 3 → ℝ} {peak : Fin 3}
    (hnonneg : ∀ coordinate, 0 ≤ utility coordinate) :
    utility peak ≤ ∑ coordinate : Fin 3, utility coordinate := by
  exact Finset.single_le_sum (fun coordinate _ => hnonneg coordinate) (by simp)

/-- A positive total makes every selected maximal coordinate strictly positive. -/
theorem lemma15_peak_pos_of_total_pos {utility : Fin 3 → ℝ} {peak : Fin 3}
    (hnonneg : ∀ coordinate, 0 ≤ utility coordinate)
    (hpeak : ∀ coordinate, utility coordinate ≤ utility peak)
    (htotal : 0 < ∑ coordinate : Fin 3, utility coordinate) :
    0 < utility peak := by
  have hpeak_nonneg : 0 ≤ utility peak := hnonneg peak
  by_contra hnot_pos
  have hpeak_zero : utility peak = 0 := by
    apply le_antisymm (le_of_not_gt hnot_pos) hpeak_nonneg
  have hzero : ∀ coordinate, utility coordinate = 0 := by
    intro coordinate
    apply le_antisymm
    · simpa [hpeak_zero] using hpeak coordinate
    · exact hnonneg coordinate
  simp [hzero] at htotal

/-- An upper-unit bound is preserved when the two raised coordinates start below one half. -/
theorem lemma15_dropAdd_le_one {utility : Fin 3 → ℝ} {peak : Fin 3} {increment : ℝ}
    (hnonneg : ∀ coordinate, 0 ≤ utility coordinate)
    (htotal : (∑ coordinate : Fin 3, utility coordinate) ≤ 1)
    (hpeak : ∀ coordinate, utility coordinate ≤ utility peak)
    (hincrement : increment ≤ (1 : ℝ) / 2) :
    ∀ user, lemma15DropAdd utility peak increment user ≤ 1 := by
  intro user
  by_cases huser : user = peak
  · simp [lemma15DropAdd, huser]
  · rw [lemma15DropAdd, if_neg huser]
    have huser_le_half := lemma15_other_le_half hnonneg htotal hpeak huser
    linarith

/-- The positive source increment after dividing by `β`. -/
theorem lemma15_increment_div_beta_pos {beta value : ℝ}
    (hbeta : 0 < beta) (hvalue : 0 < value) :
    0 < lemma15Increment (beta * value) / beta := by
  exact div_pos (lemma15_increment_pos (mul_pos hbeta hvalue)) hbeta

/-- The source increment is less than half the dropped utility coordinate. -/
theorem lemma15_increment_div_beta_lt_half {beta value : ℝ}
    (hbeta : 0 < beta) (hvalue : 0 < value) :
    lemma15Increment (beta * value) / beta < value / 2 := by
  apply (div_lt_iff₀ hbeta).2
  have hsource := lemma15_increment_lt_half (mul_pos hbeta hvalue)
  nlinarith

/-- The exact source recursion for the three utility vectors. -/
noncomputable def lemma15Step (beta : ℝ) (utility : Fin 3 → ℝ) : Fin 3 → ℝ :=
  let peak := lemma15Peak utility
  lemma15DropAdd utility peak
    (lemma15Increment (beta * utility peak) / beta)

/-- The one-step source recursion, starting from the equal initial utility vector. -/
noncomputable def lemma15Utility (beta : ℝ) : ℕ → Fin 3 → ℝ
  | 0 => fun _ => (1 : ℝ) / 3
  | n + 1 => lemma15Step beta (lemma15Utility beta n)

/-- The total utility after one source step. -/
theorem lemma15_step_sum (beta : ℝ) (utility : Fin 3 → ℝ) :
    (∑ user : Fin 3, lemma15Step beta utility user) =
      (∑ user : Fin 3, utility user) - utility (lemma15Peak utility) +
        2 * (lemma15Increment (beta * utility (lemma15Peak utility)) / beta) := by
  rw [lemma15Step]
  exact lemma15_dropAdd_sum _ _ _

/-- A source step preserves nonnegative utility coordinates. -/
theorem lemma15_step_nonneg {beta : ℝ} (hbeta : 0 < beta)
    {utility : Fin 3 → ℝ}
    (hnonneg : ∀ user, 0 ≤ utility user)
    (htotal_pos : 0 < ∑ user : Fin 3, utility user) :
    ∀ user, 0 ≤ lemma15Step beta utility user := by
  let peak := lemma15Peak utility
  have hpeak : ∀ user, utility user ≤ utility peak := by
    intro user
    exact lemma15_le_peak utility user
  have hpeak_pos : 0 < utility peak :=
    lemma15_peak_pos_of_total_pos hnonneg hpeak htotal_pos
  have hincrement_pos : 0 < lemma15Increment (beta * utility peak) / beta :=
    lemma15_increment_div_beta_pos hbeta hpeak_pos
  change ∀ user, 0 ≤ lemma15DropAdd utility peak
    (lemma15Increment (beta * utility peak) / beta) user
  exact lemma15_dropAdd_nonneg hnonneg hincrement_pos.le

/-- The total utility strictly falls at each source step. -/
theorem lemma15_step_sum_lt {beta : ℝ} (hbeta : 0 < beta)
    {utility : Fin 3 → ℝ}
    (hnonneg : ∀ user, 0 ≤ utility user)
    (htotal_pos : 0 < ∑ user : Fin 3, utility user) :
    (∑ user : Fin 3, lemma15Step beta utility user) < ∑ user : Fin 3, utility user := by
  let peak := lemma15Peak utility
  have hpeak : ∀ user, utility user ≤ utility peak := by
    intro user
    exact lemma15_le_peak utility user
  have hpeak_pos : 0 < utility peak :=
    lemma15_peak_pos_of_total_pos hnonneg hpeak htotal_pos
  have hincrement_lt : lemma15Increment (beta * utility peak) / beta < utility peak / 2 :=
    lemma15_increment_div_beta_lt_half hbeta hpeak_pos
  rw [lemma15_step_sum]
  change (∑ user : Fin 3, utility user) - utility peak +
      2 * (lemma15Increment (beta * utility peak) / beta) <
        ∑ user : Fin 3, utility user
  nlinarith

/-- A source step has strictly positive total utility. -/
theorem lemma15_step_sum_pos {beta : ℝ} (hbeta : 0 < beta)
    {utility : Fin 3 → ℝ}
    (hnonneg : ∀ user, 0 ≤ utility user)
    (htotal_pos : 0 < ∑ user : Fin 3, utility user) :
    0 < ∑ user : Fin 3, lemma15Step beta utility user := by
  let peak := lemma15Peak utility
  have hpeak : ∀ user, utility user ≤ utility peak := by
    intro user
    exact lemma15_le_peak utility user
  have hpeak_pos : 0 < utility peak :=
    lemma15_peak_pos_of_total_pos hnonneg hpeak htotal_pos
  have hincrement_pos : 0 < lemma15Increment (beta * utility peak) / beta :=
    lemma15_increment_div_beta_pos hbeta hpeak_pos
  have hpeak_le_total : utility peak ≤ ∑ user : Fin 3, utility user :=
    lemma15_peak_le_total hnonneg
  rw [lemma15_step_sum]
  change 0 < (∑ user : Fin 3, utility user) - utility peak +
    2 * (lemma15Increment (beta * utility peak) / beta)
  nlinarith

/-- A source step preserves the unit upper bound on every utility coordinate. -/
theorem lemma15_step_le_one {beta : ℝ} (hbeta : 0 < beta)
    {utility : Fin 3 → ℝ}
    (hnonneg : ∀ user, 0 ≤ utility user)
    (htotal_pos : 0 < ∑ user : Fin 3, utility user)
    (htotal : (∑ user : Fin 3, utility user) ≤ 1) :
    ∀ user, lemma15Step beta utility user ≤ 1 := by
  let peak := lemma15Peak utility
  have hpeak : ∀ user, utility user ≤ utility peak := by
    intro user
    exact lemma15_le_peak utility user
  have hpeak_pos : 0 < utility peak :=
    lemma15_peak_pos_of_total_pos hnonneg hpeak htotal_pos
  have hpeak_le_one : utility peak ≤ 1 :=
    (lemma15_peak_le_total hnonneg).trans htotal
  have hincrement_lt : lemma15Increment (beta * utility peak) / beta < utility peak / 2 :=
    lemma15_increment_div_beta_lt_half hbeta hpeak_pos
  have hincrement_le_half : lemma15Increment (beta * utility peak) / beta ≤ (1 : ℝ) / 2 := by
    linarith
  change ∀ user, lemma15DropAdd utility peak
    (lemma15Increment (beta * utility peak) / beta) user ≤ 1
  exact lemma15_dropAdd_le_one hnonneg htotal hpeak hincrement_le_half

/--
Every utility vector in the source recursion is coordinatewise in `[0,1]`,
has positive total utility, and has total utility at most one.
-/
theorem lemma15_utility_invariants {beta : ℝ} (hbeta : 0 < beta) (n : ℕ) :
    (∀ user, 0 ≤ lemma15Utility beta n user) ∧
      (∀ user, lemma15Utility beta n user ≤ 1) ∧
      0 < ∑ user : Fin 3, lemma15Utility beta n user ∧
      (∑ user : Fin 3, lemma15Utility beta n user) ≤ 1 := by
  induction n with
  | zero =>
      constructor
      · intro user
        norm_num [lemma15Utility]
      constructor
      · intro user
        norm_num [lemma15Utility]
      constructor <;> norm_num [lemma15Utility, Fin.sum_univ_three]
  | succ n ih =>
      rcases ih with ⟨hnonneg, hone, htotal_pos, htotal_le_one⟩
      have hnew_nonneg := lemma15_step_nonneg hbeta hnonneg htotal_pos
      have hnew_one := lemma15_step_le_one hbeta hnonneg htotal_pos htotal_le_one
      have hnew_total_pos := lemma15_step_sum_pos hbeta hnonneg htotal_pos
      have hnew_total_lt := lemma15_step_sum_lt hbeta hnonneg htotal_pos
      have hnew_total_le_one :
          (∑ user : Fin 3, lemma15Step beta (lemma15Utility beta n) user) ≤ 1 :=
        hnew_total_lt.le.trans htotal_le_one
      simpa only [lemma15Utility] using
        And.intro hnew_nonneg (And.intro hnew_one
          (And.intro hnew_total_pos hnew_total_le_one))

/-- The source's average utility at a recursion index. -/
noncomputable def lemma15AverageUtility (beta : ℝ) (n : ℕ) : ℝ :=
  (∑ user : Fin 3, lemma15Utility beta n user) / 3

/-- The initial source alternative has average utility one third. -/
theorem lemma15_average_zero (beta : ℝ) : lemma15AverageUtility beta 0 = (1 : ℝ) / 3 := by
  norm_num [lemma15AverageUtility, lemma15Utility, Fin.sum_univ_three]

/-- Each source alternative has strictly positive average utility. -/
theorem lemma15_average_pos {beta : ℝ} (hbeta : 0 < beta) (n : ℕ) :
    0 < lemma15AverageUtility beta n := by
  rw [lemma15AverageUtility]
  exact div_pos (lemma15_utility_invariants hbeta n).2.2.1 (by norm_num)

/-- The source recursion strictly lowers average utility at every step. -/
theorem lemma15_average_succ_lt {beta : ℝ} (hbeta : 0 < beta) (n : ℕ) :
    lemma15AverageUtility beta (n + 1) < lemma15AverageUtility beta n := by
  rw [lemma15AverageUtility]
  apply (div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 3)).2
  simpa only [lemma15Utility] using
    lemma15_step_sum_lt hbeta (lemma15_utility_invariants hbeta n).1
      (lemma15_utility_invariants hbeta n).2.2.1

/-- The uniform three-user sigmoid average after a drop-and-add update. -/
theorem lemma15_dropAdd_sigmoid_average (beta : ℝ) (utility : Fin 3 → ℝ)
    (peak : Fin 3) (increment : ℝ) :
    (∑ user : Fin 3,
      Real.sigmoid (beta * (lemma15DropAdd utility peak increment user - utility user))) / 3 =
      (Real.sigmoid (-beta * utility peak) + 2 * Real.sigmoid (beta * increment)) / 3 := by
  fin_cases peak <;>
    simp [lemma15DropAdd, Fin.sum_univ_three] <;>
    ring

/--
Successive source alternatives have a strict greater-than-one-half Bradley--
Terry preference probability under the uniform three-user population.
-/
theorem lemma15_adjacent_preference {beta : ℝ} (hbeta : 0 < beta) (n : ℕ) :
    (1 : ℝ) / 2 <
      (∑ user : Fin 3,
        Real.sigmoid (beta *
          (lemma15Utility beta (n + 1) user - lemma15Utility beta n user))) / 3 := by
  let utility := lemma15Utility beta n
  let peak := lemma15Peak utility
  have hpeak : ∀ user, utility user ≤ utility peak := by
    intro user
    exact lemma15_le_peak utility user
  have hpeak_pos : 0 < utility peak :=
    lemma15_peak_pos_of_total_pos (lemma15_utility_invariants hbeta n).1 hpeak
      (lemma15_utility_invariants hbeta n).2.2.1
  have hdelta : 0 < beta * utility peak := mul_pos hbeta hpeak_pos
  have hcancel :
      beta * (lemma15Increment (beta * utility peak) / beta) =
        lemma15Increment (beta * utility peak) := by
    field_simp [ne_of_gt hbeta]
  change (1 : ℝ) / 2 <
    (∑ user : Fin 3,
      Real.sigmoid (beta *
        (lemma15Step beta utility user - utility user))) / 3
  rw [lemma15Step, lemma15_dropAdd_sigmoid_average, hcancel]
  convert lemma15_adjacent_sigmoid_advantage hdelta using 1 <;>
    dsimp [peak] <;>
    ring

/-- The hyperbolic-tangent expression in Appendix G through the half exponential. -/
theorem lemma15_tanh_quarter (delta : ℝ) :
    Real.tanh (delta / 4) =
      (Real.exp (delta / 2) - 1) / (Real.exp (delta / 2) + 1) := by
  let e : ℝ := Real.exp (delta / 4)
  have he_pos : 0 < e := by
    dsimp [e]
    exact Real.exp_pos _
  have hhalf : Real.exp (delta / 2) = e ^ 2 := by
    dsimp [e]
    rw [show delta / 2 = delta / 4 + delta / 4 by ring, Real.exp_add]
    ring
  rw [Real.tanh_eq, Real.exp_neg, hhalf]
  dsimp [e] at he_pos ⊢
  field_simp [ne_of_gt he_pos]

/-- The exponential form of the source's welfare-decrement identity. -/
theorem lemma15_exp_increment_eq_half_div_tanh {delta : ℝ} (hdelta : 0 < delta) :
    Real.exp (lemma15Increment delta) =
      Real.exp (delta / 2) / (1 + Real.tanh (delta / 4) ^ 3) := by
  have hhalf_pos : 0 < Real.exp (delta / 2) := Real.exp_pos _
  have hhalf_add_one_pos : 0 < Real.exp (delta / 2) + 1 := by positivity
  have hhalf_square_add_three_pos : 0 < Real.exp (delta / 2) ^ 2 + 3 := by positivity
  have htanh_den : 1 +
      ((Real.exp (delta / 2) - 1) / (Real.exp (delta / 2) + 1)) ^ 3 =
        (2 * Real.exp (delta / 2) * (Real.exp (delta / 2) ^ 2 + 3)) /
          (Real.exp (delta / 2) + 1) ^ 3 := by
    field_simp [ne_of_gt hhalf_add_one_pos]
    ring
  have hratio_pos : 0 <
      (Real.exp (delta / 2) + 1) ^ 3 /
        (2 * (Real.exp delta + 3)) := by positivity
  unfold lemma15Increment
  rw [Real.exp_log hratio_pos, lemma15_tanh_quarter,
    htanh_den, lemma15_exp_eq_exp_half_sq delta]
  field_simp [ne_of_gt hhalf_pos, ne_of_gt hhalf_add_one_pos,
    ne_of_gt hhalf_square_add_three_pos]

/-- The exact Appendix-G expression for the amount by which welfare falls. -/
theorem lemma15_increment_eq_half_sub_log_tanh {delta : ℝ} (hdelta : 0 < delta) :
    lemma15Increment delta = delta / 2 -
      Real.log (1 + Real.tanh (delta / 4) ^ 3) := by
  have hhalf_one : 1 < Real.exp (delta / 2) := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have htanh_pos : 0 < Real.tanh (delta / 4) := by
    rw [lemma15_tanh_quarter]
    apply div_pos <;> linarith
  have htanh_sum_pos : 0 < 1 + Real.tanh (delta / 4) ^ 3 := by positivity
  apply Real.exp_injective
  rw [Real.exp_sub, Real.exp_log htanh_sum_pos]
  exact lemma15_exp_increment_eq_half_div_tanh hdelta

/--
The exact one-step average-utility recurrence of Appendix G, before replacing
the selected maximum by the previous average.
-/
theorem lemma15_average_succ_eq_source_decrement {beta : ℝ} (hbeta : 0 < beta)
    (n : ℕ) :
    lemma15AverageUtility beta (n + 1) = lemma15AverageUtility beta n -
      2 / (3 * beta) *
        Real.log (1 + Real.tanh
          ((beta * lemma15Utility beta n
            (lemma15Peak (lemma15Utility beta n))) / 4) ^ 3) := by
  let utility := lemma15Utility beta n
  let peak := lemma15Peak utility
  have hpeak : ∀ user, utility user ≤ utility peak := by
    intro user
    exact lemma15_le_peak utility user
  have hpeak_pos : 0 < utility peak :=
    lemma15_peak_pos_of_total_pos (lemma15_utility_invariants hbeta n).1 hpeak
      (lemma15_utility_invariants hbeta n).2.2.1
  have hdelta : 0 < beta * utility peak := mul_pos hbeta hpeak_pos
  have hincrement := lemma15_increment_eq_half_sub_log_tanh hdelta
  change (∑ user : Fin 3, lemma15Step beta utility user) / 3 =
    (∑ user : Fin 3, utility user) / 3 -
      2 / (3 * beta) *
        Real.log (1 + Real.tanh ((beta * utility peak) / 4) ^ 3)
  rw [lemma15_step_sum, hincrement]
  field_simp [ne_of_gt hbeta]
  ring

/-- Hyperbolic tangent is monotone, proved through its inverse `artanh`. -/
theorem lemma15_tanh_monotone {x y : ℝ} (hxy : x ≤ y) :
    Real.tanh x ≤ Real.tanh y := by
  by_contra hnot
  have hreverse : Real.tanh y < Real.tanh x := lt_of_not_ge hnot
  have hartanh : Real.artanh (Real.tanh y) < Real.artanh (Real.tanh x) :=
    Real.artanh_lt_artanh (Real.neg_one_lt_tanh y) (Real.tanh_lt_one x) hreverse
  rw [Real.artanh_tanh, Real.artanh_tanh] at hartanh
  exact (not_lt_of_ge hxy) hartanh

/-- The real hyperbolic tangent is continuous at every real argument. -/
theorem lemma15_continuousAt_tanh (x : ℝ) : ContinuousAt Real.tanh x := by
  have htanh : Real.tanh = fun y : ℝ =>
      (Real.exp y - Real.exp (-y)) / (Real.exp y + Real.exp (-y)) := by
    funext y
    exact Real.tanh_eq y
  rw [htanh]
  apply ContinuousAt.div
  · fun_prop
  · fun_prop
  · exact ne_of_gt (add_pos (Real.exp_pos _) (Real.exp_pos _))

/-- The nonnegative half-line is sent to nonnegative values by `tanh`. -/
theorem lemma15_tanh_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.tanh x := by
  calc
    0 = Real.tanh 0 := by simp
    _ ≤ Real.tanh x := lemma15_tanh_monotone hx

/-- The source's logarithmic tanh decrement is monotone on nonnegative gaps. -/
theorem lemma15_log_tanh_cube_monotone {x y : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    Real.log (1 + Real.tanh (x / 4) ^ 3) ≤
      Real.log (1 + Real.tanh (y / 4) ^ 3) := by
  have hquarter_nonneg : 0 ≤ x / 4 := by positivity
  have hquarter_le : x / 4 ≤ y / 4 := by linarith
  have htanh_nonneg : 0 ≤ Real.tanh (x / 4) :=
    lemma15_tanh_nonneg hquarter_nonneg
  have htanh_le : Real.tanh (x / 4) ≤ Real.tanh (y / 4) :=
    lemma15_tanh_monotone hquarter_le
  have hcube_le : Real.tanh (x / 4) ^ 3 ≤ Real.tanh (y / 4) ^ 3 :=
    pow_le_pow_left₀ htanh_nonneg htanh_le _
  have hleft_pos : 0 < 1 + Real.tanh (x / 4) ^ 3 := by positivity
  have hright_pos : 0 < 1 + Real.tanh (y / 4) ^ 3 := by
    have hy_nonneg : 0 ≤ y / 4 := by linarith
    have := lemma15_tanh_nonneg hy_nonneg
    positivity
  exact Real.strictMonoOn_log.monotoneOn hleft_pos hright_pos (by linarith)

/-- A selected maximum is at least the average of three utility coordinates. -/
theorem lemma15_average_le_peak {utility : Fin 3 → ℝ} {peak : Fin 3}
    (hpeak : ∀ user, utility user ≤ utility peak) :
    (∑ user : Fin 3, utility user) / 3 ≤ utility peak := by
  fin_cases peak <;>
    simp only [Fin.sum_univ_three] <;>
    nlinarith [hpeak (0 : Fin 3), hpeak (1 : Fin 3), hpeak (2 : Fin 3)]

/-- The quantitative welfare recurrence stated in Appendix-G Lemma 15. -/
theorem lemma15_average_succ_le_source_rate {beta : ℝ} (hbeta : 0 < beta)
    (n : ℕ) :
    lemma15AverageUtility beta (n + 1) ≤ lemma15AverageUtility beta n -
      2 / (3 * beta) *
        Real.log (1 + Real.tanh
          ((beta * lemma15AverageUtility beta n) / 4) ^ 3) := by
  let utility := lemma15Utility beta n
  let peak := lemma15Peak utility
  let average := lemma15AverageUtility beta n
  have hpeak : ∀ user, utility user ≤ utility peak := by
    intro user
    exact lemma15_le_peak utility user
  have havg_pos : 0 < average := by
    exact lemma15_average_pos hbeta n
  have havg_le_peak : average ≤ utility peak := by
    exact lemma15_average_le_peak hpeak
  have hscaled_nonneg : 0 ≤ beta * average := (mul_pos hbeta havg_pos).le
  have hscaled_le : beta * average ≤ beta * utility peak :=
    mul_le_mul_of_nonneg_left havg_le_peak hbeta.le
  have hlog_le :
      Real.log (1 + Real.tanh ((beta * average) / 4) ^ 3) ≤
        Real.log (1 + Real.tanh ((beta * utility peak) / 4) ^ 3) :=
    lemma15_log_tanh_cube_monotone hscaled_nonneg hscaled_le
  have hcoefficient_pos : 0 < 2 / (3 * beta) := by positivity
  have hscaled_log_le := mul_le_mul_of_nonneg_left hlog_le hcoefficient_pos.le
  rw [lemma15_average_succ_eq_source_decrement hbeta n]
  change average -
      2 / (3 * beta) *
        Real.log (1 + Real.tanh ((beta * utility peak) / 4) ^ 3) ≤
    average -
      2 / (3 * beta) *
        Real.log (1 + Real.tanh ((beta * average) / 4) ^ 3)
  linarith

/-- The average utilities in the Appendix-G construction converge to zero. -/
theorem lemma15_average_tendsto_zero {beta : ℝ} (hbeta : 0 < beta) :
    Filter.Tendsto (lemma15AverageUtility beta) Filter.atTop (𝓝 0) := by
  let average : ℕ → ℝ := lemma15AverageUtility beta
  let limit : ℝ := ⨅ n, average n
  have hanti : Antitone average :=
    antitone_nat_of_succ_le fun n => (lemma15_average_succ_lt hbeta n).le
  have hbounded : BddBelow (Set.range average) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (lemma15_average_pos hbeta n).le
  have hlimit : Filter.Tendsto average Filter.atTop (𝓝 limit) :=
    tendsto_atTop_ciInf hanti hbounded
  have hlimit_nonneg : 0 ≤ limit := by
    apply le_ciInf
    intro n
    exact (lemma15_average_pos hbeta n).le
  let rate : ℝ → ℝ := fun value =>
    2 / (3 * beta) *
      Real.log (1 + Real.tanh ((beta * value) / 4) ^ 3)
  have hrate_le : ∀ n, rate (average n) ≤ average n - average (n + 1) := by
    intro n
    have hsource := lemma15_average_succ_le_source_rate hbeta n
    change average (n + 1) ≤ average n - rate (average n) at hsource
    linarith
  have hlimit_argument_pos : 0 <
      1 + Real.tanh ((beta * limit) / 4) ^ 3 := by
    have hscaled_nonneg : 0 ≤ (beta * limit) / 4 := by positivity
    have htanh_nonneg := lemma15_tanh_nonneg hscaled_nonneg
    positivity
  have hargument_continuous : ContinuousAt
      (fun value : ℝ => 1 + Real.tanh ((beta * value) / 4) ^ 3) limit := by
    have hscaled_continuous : ContinuousAt
        (fun value : ℝ => (beta * value) / 4) limit := by fun_prop
    exact ContinuousAt.add continuousAt_const
      (ContinuousAt.pow ((lemma15_continuousAt_tanh _).comp hscaled_continuous) 3)
  have hlog_tendsto : Filter.Tendsto
      (fun value : ℝ => Real.log (1 + Real.tanh ((beta * value) / 4) ^ 3))
      (𝓝 limit)
      (𝓝 (Real.log (1 + Real.tanh ((beta * limit) / 4) ^ 3))) :=
    (Real.continuousAt_log (ne_of_gt hlimit_argument_pos)).tendsto.comp
      hargument_continuous.tendsto
  have hrate_tendsto : Filter.Tendsto (fun n => rate (average n)) Filter.atTop
      (𝓝 (rate limit)) := by
    exact (tendsto_const_nhds.mul hlog_tendsto).comp hlimit
  have hshift : Filter.Tendsto (fun n : ℕ => average (n + 1)) Filter.atTop
      (𝓝 limit) :=
    hlimit.comp (Filter.tendsto_add_atTop_nat 1)
  have hdifference : Filter.Tendsto (fun n : ℕ => average n - average (n + 1))
      Filter.atTop (𝓝 0) := by
    simpa using hlimit.sub hshift
  have hrate_nonpos : rate limit ≤ 0 :=
    le_of_tendsto_of_tendsto' hrate_tendsto hdifference hrate_le
  have hlimit_nonpos : limit ≤ 0 := by
    by_contra hnot
    have hlimit_pos : 0 < limit := lt_of_not_ge hnot
    have hscaled_pos : 0 < beta * limit := mul_pos hbeta hlimit_pos
    have hhalf_pos : 0 < (beta * limit) / 2 := by linarith
    have hexp_half_gt_one : 1 < Real.exp ((beta * limit) / 2) := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr hhalf_pos
    have htanh_pos : 0 < Real.tanh ((beta * limit) / 4) := by
      rw [lemma15_tanh_quarter]
      apply div_pos
      · rw [← Real.exp_zero]
        exact sub_pos.mpr (by simpa using hexp_half_gt_one)
      · positivity
    have hlog_pos : 0 <
        Real.log (1 + Real.tanh ((beta * limit) / 4) ^ 3) := by
      apply Real.log_pos
      have hcube_pos : 0 < Real.tanh ((beta * limit) / 4) ^ 3 :=
        pow_pos htanh_pos _
      linarith
    have hrate_pos : 0 < rate limit := by
      dsimp [rate]
      exact mul_pos (by positivity) hlog_pos
    linarith
  have hlimit_zero : limit = 0 := le_antisymm hlimit_nonpos hlimit_nonneg
  rw [hlimit_zero] at hlimit
  simpa [average] using hlimit

/--
The full numerical content of Appendix-G Lemma 15 for the explicit uniform
three-user utility construction.  Alternative `n` denotes the source's
`a_{n+1}`.
-/
theorem lemma15_source_construction {beta : ℝ} (hbeta : 0 < beta) :
    lemma15AverageUtility beta 0 = (1 : ℝ) / 3 ∧
      (∀ n : ℕ,
        0 < lemma15AverageUtility beta (n + 1) ∧
          lemma15AverageUtility beta (n + 1) ≤ lemma15AverageUtility beta n -
            2 / (3 * beta) *
              Real.log (1 + Real.tanh
                ((beta * lemma15AverageUtility beta n) / 4) ^ 3) ∧
          lemma15AverageUtility beta (n + 1) < lemma15AverageUtility beta n ∧
          (1 : ℝ) / 2 <
            (∑ user : Fin 3,
              Real.sigmoid (beta *
                (lemma15Utility beta (n + 1) user - lemma15Utility beta n user))) / 3) ∧
      Filter.Tendsto (lemma15AverageUtility beta) Filter.atTop (𝓝 0) := by
  refine ⟨lemma15_average_zero beta, ?_, lemma15_average_tendsto_zero hbeta⟩
  intro n
  exact ⟨lemma15_average_pos hbeta _, lemma15_average_succ_le_source_rate hbeta n,
    lemma15_average_succ_lt hbeta n, lemma15_adjacent_preference hbeta n⟩

/-- The source's uniform three-user population. -/
noncomputable def lemma15Population : PMF (Fin 3) := AppliedModelingLib.uniformPMF (Fin 3)

/-- The source utility profile, with natural-number alternative `n` denoting `a_{n+1}`. -/
noncomputable def lemma15Profile (beta : ℝ) :
    AppliedModelingLib.Alignment.Welfare.FiniteUtilityProfile (Fin 3) ℕ :=
  fun user alternative => lemma15Utility beta alternative user

/-- The explicit source profile is unit-interval valued. -/
theorem lemma15_profile_unitInterval {beta : ℝ} (hbeta : 0 < beta) :
    AppliedModelingLib.Alignment.Welfare.UnitIntervalUtilityProfile (lemma15Profile beta) := by
  intro user alternative
  exact ⟨(lemma15_utility_invariants hbeta alternative).1 user,
    (lemma15_utility_invariants hbeta alternative).2.1 user⟩

/-- The abstract population-average operator agrees with the source's three-user average. -/
theorem lemma15_population_average_eq (beta : ℝ) (alternative : ℕ) :
    AppliedModelingLib.Alignment.Welfare.populationAverageUtility lemma15Population
      (lemma15Profile beta) alternative = lemma15AverageUtility beta alternative := by
  simp [AppliedModelingLib.Alignment.Welfare.populationAverageUtility, AppliedModelingLib.pmfExp,
    lemma15Population, lemma15Profile, lemma15AverageUtility,
    AppliedModelingLib.uniformPMF_apply_toReal, Fin.sum_univ_three]
  ring

/--
The abstract population Bradley--Terry preference agrees with the uniform
three-user sigmoid average used in the source proof.
-/
theorem lemma15_population_preference_eq_sigmoid_average (beta : ℝ) (first second : ℕ) :
    (AppliedModelingLib.Alignment.Welfare.populationBradleyTerryPreference lemma15Population
      (lemma15Profile beta) beta).prob PUnit.unit.{1} first second =
      (∑ user : Fin 3,
        Real.sigmoid (beta *
          (lemma15Utility beta first user - lemma15Utility beta second user))) / 3 := by
  simp [AppliedModelingLib.Alignment.Welfare.populationBradleyTerryPreference,
    AppliedModelingLib.pmfExp, lemma15Population, lemma15Profile,
    AppliedModelingLib.uniformPMF_apply_toReal, Fin.sum_univ_three]
  ring

/-- Every successive source alternative has population Bradley--Terry win probability above one half. -/
theorem lemma15_population_adjacent_preference {beta : ℝ} (hbeta : 0 < beta) (n : ℕ) :
    (1 : ℝ) / 2 <
      (AppliedModelingLib.Alignment.Welfare.populationBradleyTerryPreference lemma15Population
        (lemma15Profile beta) beta).prob PUnit.unit.{1} (n + 1) n := by
  rw [lemma15_population_preference_eq_sigmoid_average]
  exact lemma15_adjacent_preference hbeta n

/-- The typed-population welfare sequence in the source construction tends to zero. -/
theorem lemma15_population_average_tendsto_zero {beta : ℝ} (hbeta : 0 < beta) :
    Filter.Tendsto
      (fun alternative => AppliedModelingLib.Alignment.Welfare.populationAverageUtility lemma15Population
        (lemma15Profile beta) alternative)
      Filter.atTop (𝓝 0) := by
  have heq :
      (fun alternative => AppliedModelingLib.Alignment.Welfare.populationAverageUtility lemma15Population
        (lemma15Profile beta) alternative) = lemma15AverageUtility beta := by
    funext alternative
    exact lemma15_population_average_eq beta alternative
  rw [heq]
  exact lemma15_average_tendsto_zero hbeta

end GolzHaghtalabYang2025Distortion

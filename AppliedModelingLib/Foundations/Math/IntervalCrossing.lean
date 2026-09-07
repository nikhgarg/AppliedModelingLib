import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import AppliedModelingLib.Foundations.Math.EpsilonContinuity

namespace AppliedModelingLib

open Set

/-- Elementary epsilon-delta continuity gives mathlib's `ContinuousAt`. -/
theorem continuousAt_of_epsilonContinuousAt {f : ℝ → ℝ} {x : ℝ}
    (hf : EpsilonContinuousAt f x) :
    ContinuousAt f x := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  rcases hf ε hε with ⟨δ, hδ_pos, hδ⟩
  refine ⟨δ, hδ_pos, ?_⟩
  intro y hy
  simpa [Real.dist_eq] using hδ y (by simpa [Real.dist_eq] using hy)

/-- Pointwise elementary epsilon-delta continuity on a set gives `ContinuousOn`. -/
theorem continuousOn_of_forall_epsilonContinuousAt
    {f : ℝ → ℝ} {s : Set ℝ}
    (hf : ∀ x ∈ s, EpsilonContinuousAt f x) :
    ContinuousOn f s := by
  rw [Metric.continuousOn_iff]
  intro x hx ε hε
  rcases hf x hx ε hε with ⟨δ, hδ_pos, hδ⟩
  refine ⟨δ, hδ_pos, ?_⟩
  intro y hyS hy
  simpa [Real.dist_eq] using hδ y (by simpa [Real.dist_eq] using hy)

/--
A strict real inequality at zero persists at some strictly positive parameter
no larger than one. This is the finite perturbation step used after a
continuous unique-optimizer path has a strict score gap at its base parameter.
-/
theorem exists_pos_le_one_of_continuousAt_of_pos
    {f : ℝ → ℝ} (hcontinuous : ContinuousAt f 0) (hpositive : 0 < f 0) :
    ∃ parameter : ℝ, 0 < parameter ∧ parameter ≤ 1 ∧ 0 < f parameter := by
  obtain ⟨delta, hdelta_positive, hdelta⟩ :=
    (Metric.continuousAt_iff.mp hcontinuous) (f 0 / 2) (half_pos hpositive)
  let parameter : ℝ := min (delta / 2) (1 / 2)
  have hparameter_positive : 0 < parameter := by
    dsimp [parameter]
    exact lt_min (half_pos hdelta_positive) (by norm_num)
  have hparameter_delta : parameter < delta := by
    calc
      parameter ≤ delta / 2 := min_le_left _ _
      _ < delta := by linarith
  have hparameter_one : parameter ≤ 1 := by
    calc
      parameter ≤ 1 / 2 := min_le_right _ _
      _ ≤ 1 := by norm_num
  have hparameter_near : dist parameter 0 < delta := by
    simpa [Real.dist_eq, abs_of_nonneg hparameter_positive.le] using hparameter_delta
  have hvalue_near := hdelta hparameter_near
  rw [Real.dist_eq] at hvalue_near
  have hvalue_lower : -|f parameter - f 0| ≤ f parameter - f 0 := neg_abs_le _
  refine ⟨parameter, hparameter_positive, hparameter_one, ?_⟩
  linarith

/--
A strict positive value at zero persists at an exact positive unit fraction.
This makes a local real-parameter continuity argument compatible with finite
integer data obtained by scaling a rational perturbation.
-/
theorem exists_pos_unitFraction_of_continuousAt_of_pos
    {f : ℝ → ℝ} (hcontinuous : ContinuousAt f 0) (hpositive : 0 < f 0) :
    ∃ denominator : ℕ, 0 < denominator ∧ 1 ≤ denominator ∧
      0 < f ((1 : ℝ) / denominator) := by
  obtain ⟨delta, hdelta_positive, hdelta⟩ :
      ∃ δ > 0, ∀ ⦃x : ℝ⦄, dist x 0 < δ → dist (f x) (f 0) < f 0 / 2 :=
    (Metric.continuousAt_iff.mp hcontinuous) (f 0 / 2) (half_pos hpositive)
  obtain ⟨denominator, hdenominator_positive, hsmall⟩ :
      ∃ denominator : ℕ, 0 < denominator ∧ (1 : ℝ) / denominator < delta := by
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hdelta_positive
    refine ⟨n + 1, Nat.succ_pos n, ?_⟩
    norm_num [Nat.cast_add] at hn ⊢
    exact hn
  have hdenominator_one : 1 ≤ denominator := by omega
  have hparameter_positive : 0 < (1 : ℝ) / denominator := by positivity
  have hnear : dist ((1 : ℝ) / denominator) 0 < delta := by
    simpa [Real.dist_eq, abs_of_pos hparameter_positive] using hsmall
  have hvalueNear := hdelta hnear
  rw [Real.dist_eq] at hvalueNear
  have hvalueLower := (abs_lt.mp hvalueNear).1
  refine ⟨denominator, hdenominator_positive, hdenominator_one, ?_⟩
  linarith

/--
On a compact interval, if a continuous function is nonpositive at the left
endpoint and positive at the right endpoint, then there is a last nonpositive
point. Every later point in the interval is strictly positive.
-/
theorem exists_last_nonpos_with_right_pos_on_Icc
    {d : ℝ → ℝ} {lo hi : ℝ}
    (hlohi : lo < hi)
    (hd : ContinuousOn d (Icc lo hi))
    (hlo_nonpos : d lo ≤ 0)
    (hhi_pos : 0 < d hi) :
    ∃ x : ℝ, lo ≤ x ∧ x < hi ∧ d x ≤ 0 ∧
      ∀ y : ℝ, x < y → y ≤ hi → 0 < d y := by
  let S : Set ℝ := {x | x ∈ Icc lo hi ∧ d x ≤ 0}
  have hS_closed : IsClosed S := by
    dsimp [S]
    exact isClosed_Icc.isClosed_le hd continuousOn_const
  have hS_compact : IsCompact S :=
    isCompact_Icc.of_isClosed_subset hS_closed (by
      intro x hx
      exact hx.1)
  have hS_nonempty : S.Nonempty :=
    ⟨lo, ⟨⟨le_rfl, le_of_lt hlohi⟩, hlo_nonpos⟩⟩
  rcases hS_compact.exists_isMaxOn hS_nonempty continuousOn_id with
    ⟨x, hxS, hxmax⟩
  have hxlo : lo ≤ x := hxS.1.1
  have hxhi_le : x ≤ hi := hxS.1.2
  have hdx_nonpos : d x ≤ 0 := hxS.2
  have hx_ne_hi : x ≠ hi := by
    intro h
    subst x
    linarith
  have hxhi : x < hi := lt_of_le_of_ne hxhi_le hx_ne_hi
  refine ⟨x, hxlo, hxhi, hdx_nonpos, ?_⟩
  intro y hxy hyhi
  have hloy : lo ≤ y := le_trans hxlo (le_of_lt hxy)
  by_contra hy_not_pos
  have hyd_nonpos : d y ≤ 0 := le_of_not_gt hy_not_pos
  have hyS : y ∈ S := ⟨⟨hloy, hyhi⟩, hyd_nonpos⟩
  have hy_le_x : y ≤ x := (isMaxOn_iff.mp hxmax) y hyS
  linarith

end AppliedModelingLib

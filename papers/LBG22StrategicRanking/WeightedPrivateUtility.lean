import LBG22StrategicRanking.MainTheorems
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Weighted private utility: a source-family test of Proposition B.2

This file checks the unresolved maximum step in LBG22 Proposition B.2 against
an explicit instance of the paper's printed primitives.  The instance uses

* capacity `rho = 1/16` and fixed effort budget `B = 1`;
* score technology `g(e) = e`;
* measurable-skill cost `p(e) = e^2`;
* skill quantiles `f_M(t) = 1/(2-t)` and `f_U(t) = t`.

These primitives satisfy the source monotonicity, continuity, concavity, and
convexity requirements.  We derive the correctly normalized conditional
utility formulas and prove that the interior cutoff `7/16` cannot maximize
weighted private utility for any `beta in (0,1)`.  Thus the first-order
balancing argument in the printed proof cannot be recovered from the printed
assumptions alone; a global shape condition such as the marginal-tradeoff
ordering in `MainTheorems.lean` is genuinely needed.

Upstream credit: the elementary integral calculation reuses Mathlib's
`integral_id` from
`Mathlib.Analysis.SpecialFunctions.Integrals.Basic`, and strict convexity of
the square reuses Mathlib's `strictConvexOn_pow` from
`Mathlib.Analysis.Convex.SpecificFunctions.Deriv`.  The pinned Mathlib source
and Apache-2.0 license are recorded in `docs/UPSTREAM_LEAN_SOURCES.md`.
-/

namespace LBG22StrategicRanking

open Set
open MeasureTheory

/-- Capacity in the source-family counterexample. -/
noncomputable def b2CounterexampleRho : ℝ := (1 : ℝ) / 16

/-- Fixed total effort budget in the source-family counterexample. -/
def b2CounterexampleBudget : ℝ := 1

/-- The source score technology `g(e)=e`. -/
def b2CounterexampleScoreTechnology (e : ℝ) : ℝ := e

/-- The source measurable-effort cost `p(e)=e^2`. -/
def b2CounterexampleCost (e : ℝ) : ℝ := e ^ 2

/--
The printed two-skill cost
`p_M(e_M,e_U)=p(e_M)-max(0,B-(e_M+e_U))^2` for the fixed witness.
-/
def b2CounterexampleMultiskillCost (eMeasurable eUnmeasurable : ℝ) : ℝ :=
  b2CounterexampleCost eMeasurable -
    (max 0
      (b2CounterexampleBudget - (eMeasurable + eUnmeasurable))) ^ 2

/-- Measurable-skill quantile `f_M(t)=1/(2-t)`. -/
noncomputable def b2CounterexampleMeasurableSkill (t : ℝ) : ℝ :=
  1 / (2 - t)

/-- Unmeasurable-skill quantile `f_U(t)=t`, as used in the printed proof. -/
def b2CounterexampleUnmeasurableSkill (t : ℝ) : ℝ :=
  t

/--
The least measurable effort whose squared cost reaches the high-level
admission probability `rho/(1-c)`.
-/
noncomputable def b2CounterexampleThresholdEffort (c : ℝ) : ℝ :=
  1 / (4 * Real.sqrt (1 - c))

/--
Measurable effort of an admitted applicant with measurable pre-rank `t`.  This
is the source score-equalizing ratio
`e_tilde(c) f_M(c) / f_M(t)` in simplified form.
-/
noncomputable def b2CounterexampleMeasurableEffort (c t : ℝ) : ℝ :=
  b2CounterexampleThresholdEffort c * (2 - t) / (2 - c)

/-- Fixed-budget unmeasurable effort `B-e_M`. -/
noncomputable def b2CounterexampleUnmeasurableEffort (c t : ℝ) : ℝ :=
  b2CounterexampleBudget - b2CounterexampleMeasurableEffort c t

/-- Conditional measurable-skill utility among admitted applicants. -/
noncomputable def b2CounterexampleMeasurableUtility (c : ℝ) : ℝ :=
  1 / (4 * Real.sqrt (1 - c) * (2 - c))

/-- Correct conditional mean of fixed-budget effort on the unmeasurable skill. -/
noncomputable def b2CounterexampleUnmeasurableEffortTailMean (c : ℝ) : ℝ :=
  1 - b2CounterexampleMeasurableUtility c * (3 - c) / 2

/--
Correctly normalized conditional unmeasurable-skill utility among admitted
applicants.  Independence multiplies the conditional effort mean by the
uniform mean `1/2` of `f_U(t)=t`; the integral derivation is proved below.
-/
noncomputable def b2CounterexampleUnmeasurableUtility (c : ℝ) : ℝ :=
  (1 / 2 : ℝ) * b2CounterexampleUnmeasurableEffortTailMean c

/--
The printed regularity assumptions used by Proposition B.2, collected only to
make the fixed source-family witness auditable as one object.  The cost fields
are stated on nonnegative effort, and the quantile fields on the source rank
interval `[0,1]`.
-/
structure B2SourcePrimitiveRegularity
    (rho budget : ℝ) (g cost fMeasurable fUnmeasurable : ℝ → ℝ) : Prop where
  capacity_pos : 0 < rho
  capacity_lt_one : rho < 1
  budget_pos : 0 < budget
  score_continuous : Continuous g
  score_strictMono : StrictMono g
  score_concaveOn : ConcaveOn ℝ (Set.Ici 0) g
  score_nonnegative : ∀ e ∈ Set.Ici (0 : ℝ), 0 ≤ g e
  cost_monotoneOn : MonotoneOn cost (Set.Ici 0)
  cost_convexOn : ConvexOn ℝ (Set.Ici 0) cost
  cost_nonnegative : ∀ e ∈ Set.Ici (0 : ℝ), 0 ≤ cost e
  measurableSkill_continuousOn : ContinuousOn fMeasurable (Set.Icc 0 1)
  measurableSkill_strictMonoOn : StrictMonoOn fMeasurable (Set.Icc 0 1)
  unmeasurableSkill_continuousOn : ContinuousOn fUnmeasurable (Set.Icc 0 1)
  unmeasurableSkill_strictMonoOn : StrictMonoOn fUnmeasurable (Set.Icc 0 1)

/-- The source score technology is continuous. -/
theorem b2CounterexampleScoreTechnology_continuous :
    Continuous b2CounterexampleScoreTechnology := by
  simpa [b2CounterexampleScoreTechnology] using continuous_id

/-- The source score technology is strictly increasing. -/
theorem b2CounterexampleScoreTechnology_strictMono :
    StrictMono b2CounterexampleScoreTechnology := by
  simpa [b2CounterexampleScoreTechnology] using strictMono_id

/-- The source score technology is concave (indeed, affine). -/
theorem b2CounterexampleScoreTechnology_concaveOn :
    ConcaveOn ℝ Set.univ b2CounterexampleScoreTechnology := by
  simpa [b2CounterexampleScoreTechnology] using
    (concaveOn_id (convex_univ : Convex ℝ (Set.univ : Set ℝ)))

/-- The squared cost is strictly increasing on nonnegative effort. -/
theorem b2CounterexampleCost_strictMonoOn :
    StrictMonoOn b2CounterexampleCost (Set.Ici 0) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  simp only [b2CounterexampleCost]
  nlinarith

/-- The squared cost is strictly convex on nonnegative effort. -/
theorem b2CounterexampleCost_strictConvexOn :
    StrictConvexOn ℝ (Set.Ici 0) b2CounterexampleCost := by
  simpa [b2CounterexampleCost] using
    (strictConvexOn_pow (n := 2) (by norm_num) :
      StrictConvexOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ 2))

/-- The measurable-skill quantile is continuous on the source rank interval. -/
theorem b2CounterexampleMeasurableSkill_continuousOn :
    ContinuousOn b2CounterexampleMeasurableSkill (Set.Icc 0 1) := by
  apply ContinuousOn.div continuousOn_const
    (continuousOn_const.sub continuousOn_id)
  intro t ht
  simp only [Set.mem_Icc] at ht
  simp only [id_eq]
  linarith

/-- The measurable-skill quantile is strictly increasing on `[0,1]`. -/
theorem b2CounterexampleMeasurableSkill_strictMonoOn :
    StrictMonoOn b2CounterexampleMeasurableSkill (Set.Icc 0 1) := by
  intro x hx y hy hxy
  have hden_y : 0 < 2 - y := by
    simp only [Set.mem_Icc] at hy
    linarith
  have hden_order : 2 - y < 2 - x := by linarith
  simpa [b2CounterexampleMeasurableSkill] using
    one_div_lt_one_div_of_lt hden_y hden_order

/-- The unmeasurable-skill quantile is continuous on `[0,1]`. -/
theorem b2CounterexampleUnmeasurableSkill_continuousOn :
    ContinuousOn b2CounterexampleUnmeasurableSkill (Set.Icc 0 1) := by
  exact continuous_id.continuousOn

/-- The unmeasurable-skill quantile is strictly increasing on `[0,1]`. -/
theorem b2CounterexampleUnmeasurableSkill_strictMonoOn :
    StrictMonoOn b2CounterexampleUnmeasurableSkill (Set.Icc 0 1) := by
  intro x _hx y _hy hxy
  simp only [b2CounterexampleUnmeasurableSkill]
  exact hxy

/-- The uniform mean of `f_U(t)=t` on `[0,1]` is `1/2`. -/
theorem b2CounterexampleUnmeasurableSkill_mean :
    (∫ t in (0 : ℝ)..1, b2CounterexampleUnmeasurableSkill t) =
      (1 : ℝ) / 2 := by
  rw [show b2CounterexampleUnmeasurableSkill = fun t : ℝ => t by
    funext t
    rfl]
  rw [integral_id]
  norm_num

/-- All printed primitive regularity requirements hold for the fixed witness. -/
theorem b2Counterexample_sourcePrimitiveRegularity :
    B2SourcePrimitiveRegularity
      b2CounterexampleRho b2CounterexampleBudget
      b2CounterexampleScoreTechnology b2CounterexampleCost
      b2CounterexampleMeasurableSkill b2CounterexampleUnmeasurableSkill := by
  refine
    { capacity_pos := by norm_num [b2CounterexampleRho]
      capacity_lt_one := by norm_num [b2CounterexampleRho]
      budget_pos := by norm_num [b2CounterexampleBudget]
      score_continuous := b2CounterexampleScoreTechnology_continuous
      score_strictMono := b2CounterexampleScoreTechnology_strictMono
      score_concaveOn := ?_
      score_nonnegative := ?_
      cost_monotoneOn := b2CounterexampleCost_strictMonoOn.monotoneOn
      cost_convexOn := b2CounterexampleCost_strictConvexOn.convexOn
      cost_nonnegative := ?_
      measurableSkill_continuousOn :=
        b2CounterexampleMeasurableSkill_continuousOn
      measurableSkill_strictMonoOn :=
        b2CounterexampleMeasurableSkill_strictMonoOn
      unmeasurableSkill_continuousOn :=
        b2CounterexampleUnmeasurableSkill_continuousOn
      unmeasurableSkill_strictMonoOn :=
        b2CounterexampleUnmeasurableSkill_strictMonoOn }
  · simpa [b2CounterexampleScoreTechnology] using
      (concaveOn_id (convex_Ici (0 : ℝ)))
  · intro e he
    simpa [b2CounterexampleScoreTechnology] using he
  · intro e _he
    exact sq_nonneg e

/--
The displayed threshold effort has exactly the squared cost required by the
source high-level admission probability.
-/
theorem b2CounterexampleThresholdEffort_cost_eq_highProbability
    {c : ℝ} (hc : c < 1) :
    b2CounterexampleCost (b2CounterexampleThresholdEffort c) =
      b2CounterexampleRho / (1 - c) := by
  have htail_nonneg : 0 ≤ 1 - c := by linarith
  have htail_ne : 1 - c ≠ 0 := by linarith
  have hsqrt_ne : Real.sqrt (1 - c) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (by linarith))
  have hsqrt_sq : Real.sqrt (1 - c) ^ 2 = 1 - c :=
    Real.sq_sqrt htail_nonneg
  rw [b2CounterexampleCost, b2CounterexampleThresholdEffort,
    b2CounterexampleRho]
  field_simp [hsqrt_ne, htail_ne]
  nlinarith

/-- The simplified effort is exactly the source score-equalizing ratio. -/
theorem b2CounterexampleMeasurableEffort_eq_source_ratio
    {c t : ℝ} (hc : c ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1) :
    b2CounterexampleMeasurableEffort c t =
      b2CounterexampleThresholdEffort c *
        b2CounterexampleMeasurableSkill c /
          b2CounterexampleMeasurableSkill t := by
  have hc_ne : 2 - c ≠ 0 := by
    simp only [Set.mem_Icc] at hc
    linarith
  have ht_ne : 2 - t ≠ 0 := by
    simp only [Set.mem_Icc] at ht
    linarith
  simp only [b2CounterexampleMeasurableEffort,
    b2CounterexampleMeasurableSkill]
  field_simp [hc_ne, ht_ne]

/--
Every admitted measurable type receives the same measurable post-effort score,
which is the conditional measurable utility used below.
-/
theorem b2CounterexampleMeasurableScore_eq_utility
    {c t : ℝ} (hc : c ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1) :
    b2CounterexampleScoreTechnology
        (b2CounterexampleMeasurableEffort c t) *
      b2CounterexampleMeasurableSkill t =
        b2CounterexampleMeasurableUtility c := by
  have hc_ne : 2 - c ≠ 0 := by
    simp only [Set.mem_Icc] at hc
    linarith
  have ht_ne : 2 - t ≠ 0 := by
    simp only [Set.mem_Icc] at ht
    linarith
  simp only [b2CounterexampleScoreTechnology,
    b2CounterexampleMeasurableEffort,
    b2CounterexampleMeasurableSkill,
    b2CounterexampleMeasurableUtility,
    b2CounterexampleThresholdEffort]
  field_simp [hc_ne, ht_ne]

/-- The two source efforts exactly exhaust the fixed budget. -/
theorem b2CounterexampleEffort_sum_eq_budget (c t : ℝ) :
    b2CounterexampleMeasurableEffort c t +
      b2CounterexampleUnmeasurableEffort c t =
        b2CounterexampleBudget := by
  simp [b2CounterexampleUnmeasurableEffort]

/-- On the fixed-budget effort profile, the printed two-skill cost is `p(e_M)`. -/
theorem b2CounterexampleMultiskillCost_at_fixedBudget (c t : ℝ) :
    b2CounterexampleMultiskillCost
      (b2CounterexampleMeasurableEffort c t)
      (b2CounterexampleUnmeasurableEffort c t) =
        b2CounterexampleCost (b2CounterexampleMeasurableEffort c t) := by
  rw [b2CounterexampleMultiskillCost]
  rw [b2CounterexampleEffort_sum_eq_budget]
  simp

/--
For every source-admissible cutoff and admitted measurable type, both effort
components are feasible and lie in the unit fixed-budget interval.
-/
theorem b2CounterexampleEfforts_mem_unit_interval
    {c t : ℝ}
    (hc_pos : 0 < c)
    (hc_hi : c ≤ 1 - b2CounterexampleRho)
    (ht : t ∈ Set.Icc c 1) :
    b2CounterexampleMeasurableEffort c t ∈ Set.Icc 0 1 ∧
      b2CounterexampleUnmeasurableEffort c t ∈ Set.Icc 0 1 := by
  have hc_le_one : c ≤ 1 := by
    norm_num [b2CounterexampleRho] at hc_hi ⊢
    linarith
  have ht_zero : 0 ≤ t := by
    exact le_trans (le_of_lt hc_pos) ht.1
  have htail_pos : 0 < 1 - c := by
    norm_num [b2CounterexampleRho] at hc_hi ⊢
    linarith
  have hsqrt_pos : 0 < Real.sqrt (1 - c) := Real.sqrt_pos.2 htail_pos
  have hsqrt_lower : (1 : ℝ) / 4 ≤ Real.sqrt (1 - c) := by
    apply Real.le_sqrt_of_sq_le
    norm_num [b2CounterexampleRho] at hc_hi ⊢
    linarith
  have hthreshold_nonneg : 0 ≤ b2CounterexampleThresholdEffort c := by
    exact le_of_lt (one_div_pos.mpr (mul_pos (by norm_num) hsqrt_pos))
  have hthreshold_le : b2CounterexampleThresholdEffort c ≤ 1 := by
    rw [b2CounterexampleThresholdEffort]
    rw [div_le_one (mul_pos (by norm_num) hsqrt_pos)]
    nlinarith
  have hden_pos : 0 < 2 - c := by linarith
  have hnum_nonneg : 0 ≤ 2 - t := by linarith [ht.2]
  have hratio_nonneg : 0 ≤ (2 - t) / (2 - c) :=
    div_nonneg hnum_nonneg (le_of_lt hden_pos)
  have hratio_le : (2 - t) / (2 - c) ≤ 1 := by
    rw [div_le_one hden_pos]
    linarith [ht.1]
  have hmeas_nonneg : 0 ≤ b2CounterexampleMeasurableEffort c t := by
    simpa [b2CounterexampleMeasurableEffort, mul_div_assoc] using
      mul_nonneg hthreshold_nonneg hratio_nonneg
  have hmeas_le : b2CounterexampleMeasurableEffort c t ≤ 1 := by
    have hproduct :
        b2CounterexampleThresholdEffort c * ((2 - t) / (2 - c)) ≤ 1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hthreshold_le)
        (sub_nonneg.mpr hratio_le)]
    simpa [b2CounterexampleMeasurableEffort, mul_div_assoc] using hproduct
  constructor
  · exact ⟨hmeas_nonneg, hmeas_le⟩
  · constructor
    · simp only [b2CounterexampleUnmeasurableEffort,
        b2CounterexampleBudget]
      linarith
    · simp only [b2CounterexampleUnmeasurableEffort,
        b2CounterexampleBudget]
      linarith

/-- Integral of the affine fixed-budget unmeasurable effort over a tail. -/
theorem intervalIntegral_one_sub_affine_effort (c a : ℝ) :
    (∫ t in c..1, (1 - a * (2 - t))) =
      (1 - c) - a * ((3 - c) * (1 - c) / 2) := by
  have hlin : IntervalIntegrable (fun t : ℝ => a * (2 - t)) volume c 1 :=
    (continuous_const.mul
      (continuous_const.sub continuous_id)).intervalIntegrable c 1
  rw [intervalIntegral.integral_sub
    (continuous_const.intervalIntegrable c 1) hlin]
  rw [intervalIntegral.integral_const]
  rw [intervalIntegral.integral_const_mul]
  have hsub : (∫ t in c..1, (2 : ℝ) - t) =
      (1 - c) * 2 - (1 ^ 2 - c ^ 2) / 2 := by
    rw [intervalIntegral.integral_sub (f := fun _ : ℝ => (2 : ℝ))
      (g := fun t : ℝ => t)
      (continuous_const.intervalIntegrable c 1)
      (continuous_id.intervalIntegrable c 1)]
    rw [intervalIntegral.integral_const, integral_id]
    rfl
  rw [hsub]
  ring

/--
The source tail integral equals tail mass times the correctly normalized
conditional unmeasurable utility.  This explicitly exposes the factor
`1/(1-c)` absent from the printed appendix calculation.
-/
theorem b2CounterexampleUnmeasurableEffort_tailIntegral
    {c : ℝ} (hc : c < 1) :
    (∫ t in c..1, b2CounterexampleUnmeasurableEffort c t) =
      (1 - c) * b2CounterexampleUnmeasurableEffortTailMean c := by
  have hc_ne : 2 - c ≠ 0 := by linarith
  have hrewrite :
      (fun t : ℝ => b2CounterexampleUnmeasurableEffort c t) =
        (fun t : ℝ =>
          1 - (b2CounterexampleThresholdEffort c / (2 - c)) * (2 - t)) := by
    funext t
    simp only [b2CounterexampleUnmeasurableEffort,
      b2CounterexampleBudget, b2CounterexampleMeasurableEffort]
    ring
  rw [hrewrite]
  rw [intervalIntegral_one_sub_affine_effort]
  simp only [b2CounterexampleUnmeasurableEffortTailMean,
    b2CounterexampleMeasurableUtility,
    b2CounterexampleThresholdEffort]
  field_simp [hc_ne]

/-- Correct conditional normalization of the admitted-tail utility. -/
theorem b2CounterexampleUnmeasurableUtility_eq_normalized_tailIntegral
    {c : ℝ} (hc : c < 1) :
    b2CounterexampleUnmeasurableUtility c =
      (∫ s in (0 : ℝ)..1, b2CounterexampleUnmeasurableSkill s) *
        ((1 / (1 - c)) *
          (∫ t in c..1, b2CounterexampleUnmeasurableEffort c t)) := by
  rw [b2CounterexampleUnmeasurableEffort_tailIntegral hc]
  rw [b2CounterexampleUnmeasurableSkill_mean]
  have htail_ne : 1 - c ≠ 0 := by linarith
  simp only [b2CounterexampleUnmeasurableUtility]
  field_simp [htail_ne]

/-- Left comparison cutoff used in the exact non-support argument. -/
noncomputable def b2CounterexampleLeftCutoff : ℝ := (9 : ℝ) / 25

/-- Target interior cutoff refuting the printed universal claim. -/
noncomputable def b2CounterexampleTargetCutoff : ℝ := (7 : ℝ) / 16

/-- Right comparison cutoff used in the exact non-support argument. -/
noncomputable def b2CounterexampleRightCutoff : ℝ := (5 : ℝ) / 9

/-- All three witness cutoffs lie in the source interval `(0,1-rho)`. -/
theorem b2CounterexampleCutoffs_source_admissible :
    0 < b2CounterexampleLeftCutoff ∧
    b2CounterexampleLeftCutoff < b2CounterexampleTargetCutoff ∧
    b2CounterexampleTargetCutoff < b2CounterexampleRightCutoff ∧
    b2CounterexampleRightCutoff < 1 - b2CounterexampleRho := by
  norm_num [b2CounterexampleLeftCutoff, b2CounterexampleTargetCutoff,
    b2CounterexampleRightCutoff, b2CounterexampleRho]

/-- Exact measurable utilities at the three witness cutoffs. -/
theorem b2CounterexampleMeasurableUtility_values :
    b2CounterexampleMeasurableUtility b2CounterexampleLeftCutoff =
        (125 : ℝ) / 656 ∧
    b2CounterexampleMeasurableUtility b2CounterexampleTargetCutoff =
        (16 : ℝ) / 75 ∧
    b2CounterexampleMeasurableUtility b2CounterexampleRightCutoff =
        (27 : ℝ) / 104 := by
  norm_num [b2CounterexampleMeasurableUtility,
    b2CounterexampleLeftCutoff, b2CounterexampleTargetCutoff,
    b2CounterexampleRightCutoff]

/-- Exact unmeasurable utilities at the three witness cutoffs. -/
theorem b2CounterexampleUnmeasurableUtility_values :
    b2CounterexampleUnmeasurableUtility b2CounterexampleLeftCutoff =
        (491 : ℝ) / 1312 ∧
    b2CounterexampleUnmeasurableUtility b2CounterexampleTargetCutoff =
        (109 : ℝ) / 300 ∧
    b2CounterexampleUnmeasurableUtility b2CounterexampleRightCutoff =
        (71 : ℝ) / 208 := by
  norm_num [b2CounterexampleUnmeasurableUtility,
    b2CounterexampleUnmeasurableEffortTailMean,
    b2CounterexampleMeasurableUtility, b2CounterexampleLeftCutoff,
    b2CounterexampleTargetCutoff, b2CounterexampleRightCutoff]

/--
The target utility vector lies strictly below a convex combination of the two
comparison utility vectors: the measurable coordinate agrees exactly, while
the unmeasurable coordinate is larger by `1/18600`.
-/
theorem b2CounterexampleTarget_below_utility_chord :
    let lam : ℝ := (1558 : ℝ) / 2325
    lam * b2CounterexampleMeasurableUtility b2CounterexampleLeftCutoff +
        (1 - lam) *
          b2CounterexampleMeasurableUtility b2CounterexampleRightCutoff =
      b2CounterexampleMeasurableUtility b2CounterexampleTargetCutoff ∧
    lam * b2CounterexampleUnmeasurableUtility b2CounterexampleLeftCutoff +
        (1 - lam) *
          b2CounterexampleUnmeasurableUtility b2CounterexampleRightCutoff =
      b2CounterexampleUnmeasurableUtility b2CounterexampleTargetCutoff +
        (1 : ℝ) / 18600 := by
  norm_num [b2CounterexampleMeasurableUtility,
    b2CounterexampleUnmeasurableUtility,
    b2CounterexampleUnmeasurableEffortTailMean,
    b2CounterexampleLeftCutoff, b2CounterexampleTargetCutoff,
    b2CounterexampleRightCutoff]

/--
No interior weight supports the target cutoff as a global maximizer.  If both
comparison cutoffs had weakly lower weighted utility, their convex combination
would too; the preceding exact chord calculation makes it strictly higher by
`(1-beta)/18600`.
-/
theorem b2Counterexample_no_weight_maximizes_target :
    ∀ beta : ℝ, 0 < beta → beta < 1 →
      ¬ MaximizesOnInterval
        (weightedPrivateUtility beta
          b2CounterexampleMeasurableUtility
          b2CounterexampleUnmeasurableUtility)
        b2CounterexampleTargetCutoff 0 (1 - b2CounterexampleRho) := by
  intro beta hbeta_pos hbeta_lt hmax
  have hleft := hmax.2.2 b2CounterexampleLeftCutoff
    (by norm_num [b2CounterexampleLeftCutoff])
    (by norm_num [b2CounterexampleLeftCutoff, b2CounterexampleRho])
  have hright := hmax.2.2 b2CounterexampleRightCutoff
    (by norm_num [b2CounterexampleRightCutoff])
    (by norm_num [b2CounterexampleRightCutoff, b2CounterexampleRho])
  norm_num [weightedPrivateUtility,
    b2CounterexampleMeasurableUtility,
    b2CounterexampleUnmeasurableUtility,
    b2CounterexampleUnmeasurableEffortTailMean,
    b2CounterexampleLeftCutoff, b2CounterexampleTargetCutoff,
    b2CounterexampleRightCutoff] at hleft hright
  linarith

/--
Formal source-family refutation of the printed universal conclusion of
Proposition B.2: the target cutoff is source-admissible, yet no
`beta in (0,1)` makes it maximize the correctly normalized private utility.
-/
theorem proposition_B2_printed_conclusion_false_for_source_family :
    B2SourcePrimitiveRegularity
      b2CounterexampleRho b2CounterexampleBudget
      b2CounterexampleScoreTechnology b2CounterexampleCost
      b2CounterexampleMeasurableSkill b2CounterexampleUnmeasurableSkill ∧
    0 < b2CounterexampleTargetCutoff ∧
    b2CounterexampleTargetCutoff < 1 - b2CounterexampleRho ∧
    ∀ beta : ℝ, 0 < beta → beta < 1 →
      ¬ MaximizesOnInterval
        (weightedPrivateUtility beta
          b2CounterexampleMeasurableUtility
          b2CounterexampleUnmeasurableUtility)
        b2CounterexampleTargetCutoff 0 (1 - b2CounterexampleRho) := by
  refine ⟨b2Counterexample_sourcePrimitiveRegularity, ?_, ?_,
    b2Counterexample_no_weight_maximizes_target⟩
  · norm_num [b2CounterexampleTargetCutoff]
  · norm_num [b2CounterexampleTargetCutoff, b2CounterexampleRho]

end LBG22StrategicRanking

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-!
# Bisection Helpers

Small reusable arithmetic lemmas for papers that analyze bisection,
nested-bisection, or branch-and-bound style algorithms.  The statements are
deliberately concrete: they record exact iteration-count and bracket-width
bounds before any asymptotic notation is introduced.
-/

namespace AppliedModelingLib.Optimization

/-! ## Real bracket certificates -/

/--
A real bisection bracket around a target point.  This is the Prop-level
certificate usually maintained by a bisection loop: `lower` and `upper`
bracket `target`, and the remaining bracket width is at most `delta`.
-/
structure RealBisectionBracket
    (target lower upper delta : ℝ) : Prop where
  lower_le_target : lower ≤ target
  target_le_upper : target ≤ upper
  width_le : upper - lower ≤ delta

/-- A bracket's lower endpoint is below its upper endpoint. -/
theorem RealBisectionBracket.lower_le_upper
    {target lower upper delta : ℝ}
    (B : RealBisectionBracket target lower upper delta) :
    lower ≤ upper :=
  B.lower_le_target.trans B.target_le_upper

/-- The upper endpoint of a bracket is at most the target plus its width. -/
theorem RealBisectionBracket.upper_le_target_add_width
    {target lower upper delta : ℝ}
    (B : RealBisectionBracket target lower upper delta) :
    upper ≤ target + (upper - lower) := by
  linarith [B.lower_le_target]

/-- If the bracket width is at most `delta`, its upper endpoint is within `delta`. -/
theorem RealBisectionBracket.upper_le_target_add_delta
    {target lower upper delta : ℝ}
    (B : RealBisectionBracket target lower upper delta) :
    upper ≤ target + delta :=
  B.upper_le_target_add_width.trans
    (by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left B.width_le target)

/-- The lower endpoint of a bracket is at least the target minus its width. -/
theorem RealBisectionBracket.target_sub_width_le_lower
    {target lower upper delta : ℝ}
    (B : RealBisectionBracket target lower upper delta) :
    target - (upper - lower) ≤ lower := by
  linarith [B.target_le_upper]

/-- If the bracket width is at most `delta`, its lower endpoint is within `delta`. -/
theorem RealBisectionBracket.target_sub_delta_le_lower
    {target lower upper delta : ℝ}
    (B : RealBisectionBracket target lower upper delta) :
    target - delta ≤ lower :=
  (sub_le_sub_left B.width_le target).trans B.target_sub_width_le_lower

/--
Updating the upper endpoint preserves a real bisection bracket when the new
upper endpoint still lies above the target and does not increase the old upper
endpoint.
-/
theorem RealBisectionBracket.update_upper
    {target lower upper newUpper delta : ℝ}
    (B : RealBisectionBracket target lower upper delta)
    (htarget : target ≤ newUpper)
    (hnewUpper : newUpper ≤ upper) :
    RealBisectionBracket target lower newUpper delta where
  lower_le_target := B.lower_le_target
  target_le_upper := htarget
  width_le := by
    have hwidth : newUpper - lower ≤ upper - lower :=
      sub_le_sub_right hnewUpper lower
    exact hwidth.trans B.width_le

/--
Updating the lower endpoint preserves a real bisection bracket when the new
lower endpoint still lies below the target and does not decrease the old lower
endpoint.
-/
theorem RealBisectionBracket.update_lower
    {target lower upper newLower delta : ℝ}
    (B : RealBisectionBracket target lower upper delta)
    (hnewLower : lower ≤ newLower)
    (htarget : newLower ≤ target) :
    RealBisectionBracket target newLower upper delta where
  lower_le_target := htarget
  target_le_upper := B.target_le_upper
  width_le := by
    have hwidth : upper - newLower ≤ upper - lower :=
      sub_le_sub_left hnewLower upper
    exact hwidth.trans B.width_le

/-! ## Executable real bisection -/

/-- The midpoint of a real interval. -/
noncomputable def realBisectionMidpoint (lower upper : ℝ) : ℝ :=
  (lower + upper) / 2

/-- The midpoint is above the lower endpoint of a nonempty interval. -/
theorem realBisectionMidpoint_lower_le
    {lower upper : ℝ} (h : lower ≤ upper) :
    lower ≤ realBisectionMidpoint lower upper := by
  unfold realBisectionMidpoint
  nlinarith

/-- The midpoint is below the upper endpoint of a nonempty interval. -/
theorem realBisectionMidpoint_le_upper
    {lower upper : ℝ} (h : lower ≤ upper) :
    realBisectionMidpoint lower upper ≤ upper := by
  unfold realBisectionMidpoint
  nlinarith

/--
One executable bisection step.  The Boolean predicate `above` records whether
the midpoint is known to lie above the target: if so the upper endpoint is
replaced by the midpoint, and otherwise the lower endpoint is replaced.
-/
noncomputable def realBisectionStep
    (above : ℝ → Bool) (lower upper : ℝ) : ℝ × ℝ :=
  let mid := realBisectionMidpoint lower upper
  if above mid then (lower, mid) else (mid, upper)

/-- Pair-valued form of `realBisectionStep`, convenient for iteration. -/
noncomputable def realBisectionStepFn
    (above : ℝ → Bool) (p : ℝ × ℝ) : ℝ × ℝ :=
  realBisectionStep above p.1 p.2

/-- Run `n` executable bisection steps from an initial interval. -/
noncomputable def realBisectionRun
    (above : ℝ → Bool) (n : ℕ) (lower upper : ℝ) : ℝ × ℝ :=
  Nat.iterate (realBisectionStepFn above) n (lower, upper)

/--
Canonical real-threshold classifier for bisection: true exactly when the tested
point is at or above the target.
-/
noncomputable def realBisectionAboveTarget (target x : ℝ) : Bool :=
  if target ≤ x then true else false

theorem realBisectionAboveTarget_true
    {target x : ℝ}
    (h : realBisectionAboveTarget target x = true) :
    target ≤ x := by
  by_cases hx : target ≤ x
  · exact hx
  · simp [realBisectionAboveTarget, hx] at h

theorem realBisectionAboveTarget_false
    {target x : ℝ}
    (h : realBisectionAboveTarget target x = false) :
    x ≤ target := by
  by_cases hx : target ≤ x
  · simp [realBisectionAboveTarget, hx] at h
  · exact le_of_lt (lt_of_not_ge hx)

theorem realBisectionAboveTarget_eq_true_iff
    {target x : ℝ} :
    realBisectionAboveTarget target x = true ↔ target ≤ x := by
  constructor
  · exact realBisectionAboveTarget_true
  · intro h
    simp [realBisectionAboveTarget, h]

theorem realBisectionAboveTarget_eq_false_iff
    {target x : ℝ} :
    realBisectionAboveTarget target x = false ↔ x < target := by
  constructor
  · intro h
    by_cases hx : target ≤ x
    · simp [realBisectionAboveTarget, hx] at h
    · exact lt_of_not_ge hx
  · intro h
    have hx : ¬ target ≤ x := not_le_of_gt h
    simp [realBisectionAboveTarget, hx]

/--
A single executable bisection step preserves a bracket when `above` correctly
classifies midpoint positions relative to the target.
-/
theorem realBisectionStep_bracket
    {target lower upper delta : ℝ} {above : ℝ → Bool}
    (habove : ∀ x, above x = true → target ≤ x)
    (hbelow : ∀ x, above x = false → x ≤ target)
    (B : RealBisectionBracket target lower upper delta) :
    RealBisectionBracket target
      (realBisectionStep above lower upper).1
      (realBisectionStep above lower upper).2 delta := by
  let mid := realBisectionMidpoint lower upper
  have hle : lower ≤ upper := B.lower_le_upper
  by_cases hmid : above mid = true
  · have htarget_mid : target ≤ mid := habove mid hmid
    have hmid_upper : mid ≤ upper := realBisectionMidpoint_le_upper hle
    have B' := B.update_upper htarget_mid hmid_upper
    simpa [realBisectionStep, mid, hmid] using B'
  · have hmid_false : above mid = false := by
      cases h : above mid <;> simp [h] at hmid ⊢
    have hmid_target : mid ≤ target := hbelow mid hmid_false
    have hlower_mid : lower ≤ mid := realBisectionMidpoint_lower_le hle
    have B' := B.update_lower hlower_mid hmid_target
    simpa [realBisectionStep, mid, hmid_false] using B'

/--
The width after one executable bisection step is exactly half the previous
width, for a nonempty interval.
-/
theorem realBisectionStep_width_eq_half
    {lower upper : ℝ} (above : ℝ → Bool) (h : lower ≤ upper) :
    (realBisectionStep above lower upper).2 -
        (realBisectionStep above lower upper).1 =
      (upper - lower) / 2 := by
  by_cases hmid : above (realBisectionMidpoint lower upper) = true
  · simp [realBisectionStep, hmid]
    unfold realBisectionMidpoint
    ring_nf
  · have hmid_false : above (realBisectionMidpoint lower upper) = false := by
      cases h' : above (realBisectionMidpoint lower upper) <;> simp [h'] at hmid ⊢
    simp [realBisectionStep, hmid_false]
    unfold realBisectionMidpoint
    ring_nf

/-- A single executable bisection step preserves interval nonemptiness. -/
theorem realBisectionStep_lower_le_upper
    {lower upper : ℝ} (above : ℝ → Bool) (h : lower ≤ upper) :
    (realBisectionStep above lower upper).1 ≤
      (realBisectionStep above lower upper).2 := by
  by_cases hmid : above (realBisectionMidpoint lower upper) = true
  · simpa [realBisectionStep, hmid] using
      realBisectionMidpoint_lower_le h
  · have hmid_false : above (realBisectionMidpoint lower upper) = false := by
      cases h' : above (realBisectionMidpoint lower upper) <;> simp [h'] at hmid ⊢
    simpa [realBisectionStep, hmid_false] using
      realBisectionMidpoint_le_upper h

/-- A single executable bisection step never raises the upper endpoint. -/
theorem realBisectionStep_upper_le_initial
    {lower upper : ℝ} (above : ℝ → Bool) (h : lower ≤ upper) :
    (realBisectionStep above lower upper).2 ≤ upper := by
  by_cases hmid : above (realBisectionMidpoint lower upper) = true
  · simpa [realBisectionStep, hmid] using
      realBisectionMidpoint_le_upper h
  · have hmid_false : above (realBisectionMidpoint lower upper) = false := by
      cases h' : above (realBisectionMidpoint lower upper) <;> simp [h'] at hmid ⊢
    simp [realBisectionStep, hmid_false]

/-- Finite executable bisection preserves interval nonemptiness. -/
theorem realBisectionRun_lower_le_upper
    {lower upper : ℝ} (above : ℝ → Bool) {n : ℕ}
    (h : lower ≤ upper) :
    (realBisectionRun above n lower upper).1 ≤
      (realBisectionRun above n lower upper).2 := by
  induction n with
  | zero =>
      simpa [realBisectionRun] using h
  | succ n ih =>
      simpa [realBisectionRun, realBisectionStepFn, Function.iterate_succ_apply'] using
        realBisectionStep_lower_le_upper above ih

/-- Finite executable bisection never raises the upper endpoint above its initial value. -/
theorem realBisectionRun_upper_le_initial
    {lower upper : ℝ} (above : ℝ → Bool) {n : ℕ}
    (h : lower ≤ upper) :
    (realBisectionRun above n lower upper).2 ≤ upper := by
  induction n with
  | zero =>
      simp [realBisectionRun]
  | succ n ih =>
      have hrun : (realBisectionRun above n lower upper).1 ≤
          (realBisectionRun above n lower upper).2 :=
        realBisectionRun_lower_le_upper above h
      have hstep :
          (realBisectionStep above
              (realBisectionRun above n lower upper).1
              (realBisectionRun above n lower upper).2).2 ≤
            (realBisectionRun above n lower upper).2 :=
        realBisectionStep_upper_le_initial above hrun
      have hsucc :
          (realBisectionRun above (n + 1) lower upper).2 ≤
            (realBisectionRun above n lower upper).2 := by
        simpa [realBisectionRun, realBisectionStepFn,
          Function.iterate_succ_apply'] using hstep
      exact hsucc.trans ih

/-- The width after `n` executable bisection steps is the initial width divided by `2^n`. -/
theorem realBisectionRun_width_eq
    {lower upper : ℝ} (above : ℝ → Bool) {n : ℕ}
    (h : lower ≤ upper) :
    (realBisectionRun above n lower upper).2 -
        (realBisectionRun above n lower upper).1 =
      (upper - lower) / (2 : ℝ) ^ n := by
  induction n with
  | zero =>
      simp [realBisectionRun]
  | succ n ih =>
      have hrun : (realBisectionRun above n lower upper).1 ≤
          (realBisectionRun above n lower upper).2 :=
        realBisectionRun_lower_le_upper above h
      have hstep :=
        realBisectionStep_width_eq_half
          above hrun
      rw [ih] at hstep
      simpa [realBisectionRun, realBisectionStepFn,
        Function.iterate_succ_apply', pow_succ, div_eq_mul_inv,
        mul_comm, mul_left_comm, mul_assoc] using hstep

/--
Source-shaped bisection arithmetic: if the initial width is at most
`delta * 2^n`, then after `n` bisection steps the exact width
`width / 2^n` is at most `delta`.
-/
theorem width_div_pow_two_le_of_le_delta_mul_pow_two
    {width delta : ℝ} {n : ℕ}
    (h : width ≤ delta * (2 : ℝ) ^ n) :
    width / (2 : ℝ) ^ n ≤ delta := by
  have hpow_pos : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) n
  exact (div_le_iff₀ hpow_pos).2 (by simpa [mul_comm] using h)

/--
The converse arithmetic form for source bisection proofs: if the post-run
width `width / 2^n` is at most `delta`, then the initial width is at most
`delta * 2^n`.
-/
theorem le_delta_mul_pow_two_of_width_div_pow_two_le
    {width delta : ℝ} {n : ℕ}
    (h : width / (2 : ℝ) ^ n ≤ delta) :
    width ≤ delta * (2 : ℝ) ^ n := by
  have hpow_pos : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) n
  exact (div_le_iff₀ hpow_pos).1 h

/--
Source-shaped paired bisection-budget arithmetic.  If a single source depth
choice bounds both the unit inner width and half of the outer width before
`n` bisections, then it bounds the post-run outer width after `n + 1` steps
and the post-run inner width after `n` steps.
-/
theorem max_outer_half_inner_width_div_pow_two_le_of_le_delta_mul_pow_two
    {outerWidth delta : ℝ} {n : ℕ}
    (h : max (outerWidth / 2) 1 ≤ delta * (2 : ℝ) ^ n) :
    max (outerWidth / (2 : ℝ) ^ (n + 1)) (1 / (2 : ℝ) ^ n) ≤ delta := by
  have houter_pre : outerWidth / 2 ≤ delta * (2 : ℝ) ^ n :=
    (le_max_left (outerWidth / 2) (1 : ℝ)).trans h
  have hinner_pre : (1 : ℝ) ≤ delta * (2 : ℝ) ^ n :=
    (le_max_right (outerWidth / 2) (1 : ℝ)).trans h
  have houter :
      outerWidth / (2 : ℝ) ^ (n + 1) ≤ delta := by
    have houter_div :
        (outerWidth / 2) / (2 : ℝ) ^ n ≤ delta :=
      width_div_pow_two_le_of_le_delta_mul_pow_two houter_pre
    have hpow_pos : 0 < (2 : ℝ) ^ n :=
      pow_pos (by norm_num : (0 : ℝ) < 2) n
    have hpow_succ_ne : (2 : ℝ) ^ (n + 1) ≠ 0 :=
      ne_of_gt (pow_pos (by norm_num : (0 : ℝ) < 2) (n + 1))
    have hrewrite :
        outerWidth / (2 : ℝ) ^ (n + 1) =
          (outerWidth / 2) / (2 : ℝ) ^ n := by
      field_simp [pow_succ, hpow_pos.ne', hpow_succ_ne]
      ring
    simpa [hrewrite] using houter_div
  have hinner :
      (1 : ℝ) / (2 : ℝ) ^ n ≤ delta :=
    width_div_pow_two_le_of_le_delta_mul_pow_two hinner_pre
  exact max_le houter hinner

/--
Positive bisection tolerances can be met by a finite dyadic depth.  This is
the exact existence form behind source proofs that say to choose the grid
width small enough.
-/
theorem exists_nat_le_delta_mul_pow_two {budget delta : ℝ}
    (hdelta : 0 < delta) :
    ∃ n : ℕ, budget ≤ delta * (2 : ℝ) ^ n := by
  have hpow :
      Filter.Tendsto (fun n : ℕ => (2 : ℝ) ^ n) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
  have hscaled :
      Filter.Tendsto (fun n : ℕ => delta * (2 : ℝ) ^ n) Filter.atTop Filter.atTop :=
    hpow.const_mul_atTop hdelta
  exact (hscaled.eventually_ge_atTop budget).exists

/--
Logarithmic dyadic-depth choice for bisection budgets.  This packages the
standard source step "choose `n = O(log₂(budget / delta))`" in a finite form:
the chosen `n` meets the dyadic budget and its successor is bounded by
`log₂(max(1, budget / delta)) + 2`.
-/
theorem exists_nat_le_delta_mul_pow_two_and_succ_le_logb_max
    {budget delta : ℝ} (hdelta : 0 < delta) :
    ∃ n : ℕ,
      budget ≤ delta * (2 : ℝ) ^ n ∧
      ((n + 1 : ℕ) : ℝ) ≤
        Real.logb 2 (max 1 (budget / delta)) + 2 := by
  let ratio : ℝ := max 1 (budget / delta)
  let n : ℕ := Nat.ceil (Real.logb 2 ratio)
  have hratio_ge_one : 1 ≤ ratio := by
    dsimp [ratio]
    exact le_max_left 1 (budget / delta)
  have hratio_pos : 0 < ratio :=
    zero_lt_one.trans_le hratio_ge_one
  have hbudget_div_le : budget / delta ≤ ratio := by
    dsimp [ratio]
    exact le_max_right 1 (budget / delta)
  have hlog_le_n :
      Real.logb 2 ratio ≤ (n : ℝ) := by
    dsimp [n]
    exact Nat.le_ceil _
  have hratio_le_pow : ratio ≤ (2 : ℝ) ^ n := by
    have h :=
      (Real.logb_le_iff_le_rpow
        (b := (2 : ℝ)) (x := ratio) (y := (n : ℝ))
        (by norm_num : (1 : ℝ) < 2) hratio_pos).1 hlog_le_n
    simpa [Real.rpow_natCast] using h
  have hbudget_le_delta_ratio : budget ≤ delta * ratio := by
    have h := (div_le_iff₀ hdelta).1 hbudget_div_le
    simpa [mul_comm] using h
  have hbudget_le :
      budget ≤ delta * (2 : ℝ) ^ n :=
    hbudget_le_delta_ratio.trans
      (mul_le_mul_of_nonneg_left hratio_le_pow hdelta.le)
  have hlog_nonneg : 0 ≤ Real.logb 2 ratio :=
    Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hratio_ge_one
  have hn_lt :
      (n : ℝ) < Real.logb 2 ratio + 1 := by
    dsimp [n]
    exact Nat.ceil_lt_add_one hlog_nonneg
  have hsucc_le :
      ((n + 1 : ℕ) : ℝ) ≤ Real.logb 2 ratio + 2 := by
    norm_num
    linarith
  exact ⟨n, hbudget_le, by simpa [ratio] using hsucc_le⟩

/--
Finite executable bisection preserves a bracket when every midpoint
classification is sound.
-/
theorem realBisectionRun_bracket
    {target lower upper delta : ℝ} {above : ℝ → Bool} {n : ℕ}
    (habove : ∀ x, above x = true → target ≤ x)
    (hbelow : ∀ x, above x = false → x ≤ target)
    (B : RealBisectionBracket target lower upper delta) :
    RealBisectionBracket target
      (realBisectionRun above n lower upper).1
      (realBisectionRun above n lower upper).2 delta := by
  induction n with
  | zero =>
      simpa [realBisectionRun] using B
  | succ n ih =>
      simpa [realBisectionRun, realBisectionStepFn, Function.iterate_succ_apply'] using
        realBisectionStep_bracket habove hbelow ih

/--
Executable bisection produces a bracket with a requested final width whenever
the midpoint classifier is sound and the standard `width / 2^n` bound is at
most the requested tolerance.
-/
theorem realBisectionRun_bracket_of_width_le
    {target lower upper delta : ℝ} {above : ℝ → Bool} {n : ℕ}
    (habove : ∀ x, above x = true → target ≤ x)
    (hbelow : ∀ x, above x = false → x ≤ target)
    (hlower : lower ≤ target)
    (htarget : target ≤ upper)
    (hwidth : (upper - lower) / (2 : ℝ) ^ n ≤ delta) :
    RealBisectionBracket target
      (realBisectionRun above n lower upper).1
      (realBisectionRun above n lower upper).2 delta := by
  have hle : lower ≤ upper := hlower.trans htarget
  let B0 : RealBisectionBracket target lower upper (upper - lower) :=
    { lower_le_target := hlower
      target_le_upper := htarget
      width_le := le_rfl }
  have Brun :
      RealBisectionBracket target
        (realBisectionRun above n lower upper).1
        (realBisectionRun above n lower upper).2 (upper - lower) :=
    realBisectionRun_bracket habove hbelow B0
  refine
    { lower_le_target := Brun.lower_le_target
      target_le_upper := Brun.target_le_upper
      width_le := ?_ }
  rw [realBisectionRun_width_eq above hle]
  exact hwidth

/--
Specialization of executable bisection to the canonical threshold classifier
`x ↦ target ≤ x`.
-/
theorem realBisectionRun_bracket_aboveTarget_of_width_le
    {target lower upper delta : ℝ} {n : ℕ}
    (hlower : lower ≤ target)
    (htarget : target ≤ upper)
    (hwidth : (upper - lower) / (2 : ℝ) ^ n ≤ delta) :
    RealBisectionBracket target
      (realBisectionRun (realBisectionAboveTarget target) n lower upper).1
      (realBisectionRun (realBisectionAboveTarget target) n lower upper).2
      delta :=
  realBisectionRun_bracket_of_width_le
    (above := realBisectionAboveTarget target)
    (n := n)
    (fun _ => realBisectionAboveTarget_true)
    (fun _ => realBisectionAboveTarget_false)
    hlower htarget hwidth

/-!
The next two corollaries are useful when a downstream bisection loop returns the
upper endpoint of the final bracket.  They expose the two facts most often
needed by downstream algorithm proofs: the returned upper endpoint still lies
above the target, and it is strictly below the initial upper endpoint once the
final width is smaller than the initial target-to-upper gap.
-/

theorem realBisectionRun_aboveTarget_target_le_upper
    {target lower upper : ℝ} {n : ℕ}
    (hlower : lower ≤ target)
    (htarget : target ≤ upper) :
    target ≤
      (realBisectionRun (realBisectionAboveTarget target) n lower upper).2 := by
  let B0 : RealBisectionBracket target lower upper (upper - lower) :=
    { lower_le_target := hlower
      target_le_upper := htarget
      width_le := le_rfl }
  exact
    (realBisectionRun_bracket
      (above := realBisectionAboveTarget target)
      (n := n)
      (fun _ => realBisectionAboveTarget_true)
      (fun _ => realBisectionAboveTarget_false)
      B0).target_le_upper

/--
If a canonical-threshold bisection interval has upper endpoint exactly the
target, one more step keeps the upper endpoint equal to the target.
-/
theorem realBisectionStep_aboveTarget_upper_eq_target_of_upper_eq
    {target lower upper : ℝ}
    (hlower : lower ≤ target)
    (hupper : upper = target) :
    (realBisectionStep (realBisectionAboveTarget target) lower upper).2 =
      target := by
  let mid := realBisectionMidpoint lower upper
  have hmid_le : mid ≤ target := by
    have hle : lower ≤ upper := by
      simpa [hupper] using hlower
    have hmid_upper : mid ≤ upper := realBisectionMidpoint_le_upper hle
    simpa [hupper, mid] using hmid_upper
  by_cases hmid : realBisectionAboveTarget target mid = true
  · have htarget_mid : target ≤ mid := realBisectionAboveTarget_true hmid
    have hmid_eq : mid = target := le_antisymm hmid_le htarget_mid
    simpa [realBisectionStep, mid, hmid, hmid_eq, realBisectionAboveTarget]
  · have hmid_false : realBisectionAboveTarget target mid = false := by
      cases h : realBisectionAboveTarget target mid <;> simp [h] at hmid ⊢
    have hmid_false' :
        realBisectionAboveTarget target
            (realBisectionMidpoint lower target) = false := by
      simpa [mid, hupper] using hmid_false
    simpa [realBisectionStep, hupper, hmid_false']

/--
If a canonical-threshold bisection step tests the target exactly, that step's
upper endpoint becomes the target.
-/
theorem realBisectionStep_aboveTarget_upper_eq_target_of_midpoint_eq
    {target lower upper : ℝ}
    (hmid :
      realBisectionMidpoint lower upper = target) :
    (realBisectionStep (realBisectionAboveTarget target) lower upper).2 =
      target := by
  have htrue :
      realBisectionAboveTarget target (realBisectionMidpoint lower upper) =
        true := by
    simp [realBisectionAboveTarget, hmid]
  simpa [realBisectionStep, htrue, hmid, realBisectionAboveTarget]

/--
Once a canonical-threshold bisection has tested the target exactly, all later
returned upper endpoints are exactly the target.
-/
theorem realBisectionRun_aboveTarget_upper_eq_target_of_exists_exact_midpoint
    {target lower upper : ℝ} {n : ℕ}
    (hlower : lower ≤ target)
    (htarget : target ≤ upper)
    (hexact :
      ∃ k : ℕ, k < n ∧
        realBisectionMidpoint
            (realBisectionRun (realBisectionAboveTarget target) k lower upper).1
            (realBisectionRun (realBisectionAboveTarget target) k lower upper).2 =
          target) :
    (realBisectionRun (realBisectionAboveTarget target) n lower upper).2 =
      target := by
  induction n with
  | zero =>
      rcases hexact with ⟨k, hk, _⟩
      omega
  | succ n ih =>
      rcases hexact with ⟨k, hk, hmid⟩
      have hrun_lower :
          (realBisectionRun (realBisectionAboveTarget target) n lower upper).1 ≤
            target := by
        let B0 : RealBisectionBracket target lower upper (upper - lower) :=
          { lower_le_target := hlower
            target_le_upper := htarget
            width_le := le_rfl }
        exact
          (realBisectionRun_bracket
            (above := realBisectionAboveTarget target)
            (n := n)
            (fun _ => realBisectionAboveTarget_true)
            (fun _ => realBisectionAboveTarget_false)
            B0).lower_le_target
      by_cases hk_lt : k < n
      · have hupper_eq :
            (realBisectionRun (realBisectionAboveTarget target) n lower upper).2 =
              target := by
          exact ih ⟨k, hk_lt, hmid⟩
        have hstep :
            (realBisectionStep (realBisectionAboveTarget target)
                (realBisectionRun (realBisectionAboveTarget target) n lower upper).1
                (realBisectionRun (realBisectionAboveTarget target) n lower upper).2).2 =
              target :=
          realBisectionStep_aboveTarget_upper_eq_target_of_upper_eq
            hrun_lower hupper_eq
        simpa [realBisectionRun, realBisectionStepFn,
          Function.iterate_succ_apply'] using hstep
      · have hk_eq : k = n := by omega
        have hmid' :
            realBisectionMidpoint
                (realBisectionRun (realBisectionAboveTarget target) n lower upper).1
                (realBisectionRun (realBisectionAboveTarget target) n lower upper).2 =
              target := by
          simpa [hk_eq] using hmid
        have hstep :
            (realBisectionStep (realBisectionAboveTarget target)
                (realBisectionRun (realBisectionAboveTarget target) n lower upper).1
                (realBisectionRun (realBisectionAboveTarget target) n lower upper).2).2 =
              target :=
          realBisectionStep_aboveTarget_upper_eq_target_of_midpoint_eq hmid'
        simpa [realBisectionRun, realBisectionStepFn,
          Function.iterate_succ_apply'] using hstep

/--
For the canonical threshold classifier, the returned upper endpoint stays
strictly above the target provided the initial upper endpoint is strict and no
tested midpoint lands exactly on the target.  This is the reusable form of the
common bisection "no exact hit" convention.
-/
theorem realBisectionRun_aboveTarget_target_lt_upper_of_no_exact_midpoint
    {target lower upper : ℝ} {n : ℕ}
    (hlower : lower ≤ target)
    (hupper : target < upper)
    (hnoExact :
      ∀ k : ℕ, k < n →
        target ≠
          realBisectionMidpoint
            (realBisectionRun (realBisectionAboveTarget target) k lower upper).1
            (realBisectionRun (realBisectionAboveTarget target) k lower upper).2) :
    target <
      (realBisectionRun (realBisectionAboveTarget target) n lower upper).2 := by
  have hbracket :
      ∀ k : ℕ, k ≤ n →
        (realBisectionRun (realBisectionAboveTarget target) k lower upper).1 ≤
          target ∧
        target <
          (realBisectionRun (realBisectionAboveTarget target) k lower upper).2 := by
    intro k hk
    induction k with
    | zero =>
        simp [realBisectionRun, hlower, hupper]
    | succ k ih =>
        have hk_lt : k < n := Nat.lt_of_succ_le hk
        rcases ih (Nat.le_of_succ_le hk) with ⟨hlow, hhigh⟩
        let run :=
          realBisectionRun (realBisectionAboveTarget target) k lower upper
        let mid := realBisectionMidpoint run.1 run.2
        have hrun_nonempty : run.1 ≤ run.2 := hlow.trans hhigh.le
        have hmid_upper : mid ≤ run.2 :=
          realBisectionMidpoint_le_upper hrun_nonempty
        have hlower_mid : run.1 ≤ mid :=
          realBisectionMidpoint_lower_le hrun_nonempty
        by_cases hmid : realBisectionAboveTarget target mid = true
        · have htarget_mid_le : target ≤ mid :=
            realBisectionAboveTarget_true hmid
          have htarget_ne_mid : target ≠ mid := by
            simpa [run, mid] using hnoExact k hk_lt
          have htarget_mid : target < mid :=
            lt_of_le_of_ne htarget_mid_le htarget_ne_mid
          have hstep :
              realBisectionStep (realBisectionAboveTarget target)
                  run.1 run.2 =
                (run.1, mid) := by
            simp [realBisectionStep, mid, hmid]
          have hsucc :
              realBisectionRun (realBisectionAboveTarget target) (k + 1)
                  lower upper =
                (run.1, mid) := by
            simpa [realBisectionRun, realBisectionStepFn,
              Function.iterate_succ_apply', run, hstep]
          rw [hsucc]
          exact ⟨hlow, htarget_mid⟩
        · have hmid_false : realBisectionAboveTarget target mid = false := by
            cases h : realBisectionAboveTarget target mid <;> simp [h] at hmid ⊢
          have hmid_target : mid ≤ target :=
            realBisectionAboveTarget_false hmid_false
          have hstep :
              realBisectionStep (realBisectionAboveTarget target)
                  run.1 run.2 =
                (mid, run.2) := by
            simp [realBisectionStep, mid, hmid_false]
          have hsucc :
              realBisectionRun (realBisectionAboveTarget target) (k + 1)
                  lower upper =
                (mid, run.2) := by
            simpa [realBisectionRun, realBisectionStepFn,
              Function.iterate_succ_apply', run, hstep]
          rw [hsucc]
          exact ⟨hmid_target, hhigh⟩
  exact (hbracket n le_rfl).2

/--
Canonical-threshold bisection returns either the target itself, when an exact
midpoint is tested, or an upper endpoint strictly above the target.
-/
theorem realBisectionRun_aboveTarget_upper_eq_or_target_lt_upper
    {target lower upper : ℝ} {n : ℕ}
    (hlower : lower ≤ target)
    (hupper : target < upper) :
    (realBisectionRun (realBisectionAboveTarget target) n lower upper).2 =
        target ∨
      target <
        (realBisectionRun (realBisectionAboveTarget target) n lower upper).2 := by
  classical
  by_cases hexact :
      ∃ k : ℕ, k < n ∧
        realBisectionMidpoint
            (realBisectionRun (realBisectionAboveTarget target) k lower upper).1
            (realBisectionRun (realBisectionAboveTarget target) k lower upper).2 =
          target
  · exact Or.inl
      (realBisectionRun_aboveTarget_upper_eq_target_of_exists_exact_midpoint
        hlower hupper.le hexact)
  · right
    exact
      realBisectionRun_aboveTarget_target_lt_upper_of_no_exact_midpoint
        (n := n) hlower hupper
        (by
          intro k hk htarget_mid
          exact hexact ⟨k, hk, htarget_mid.symm⟩)

theorem realBisectionRun_aboveTarget_upper_lt_initial_upper_of_width_lt_gap
    {target lower upper : ℝ} {n : ℕ}
    (hlower : lower ≤ target)
    (htarget : target ≤ upper)
    (hwidth :
      (upper - lower) / (2 : ℝ) ^ n < upper - target) :
    (realBisectionRun (realBisectionAboveTarget target) n lower upper).2 <
      upper := by
  have B :
      RealBisectionBracket target
        (realBisectionRun (realBisectionAboveTarget target) n lower upper).1
        (realBisectionRun (realBisectionAboveTarget target) n lower upper).2
        ((upper - lower) / (2 : ℝ) ^ n) :=
    realBisectionRun_bracket_aboveTarget_of_width_le
      (n := n) (lower := lower) (upper := upper) (target := target)
      (delta := (upper - lower) / (2 : ℝ) ^ n)
      hlower htarget le_rfl
  have hupper_le :
      (realBisectionRun (realBisectionAboveTarget target) n lower upper).2 ≤
        target + (upper - lower) / (2 : ℝ) ^ n :=
    B.upper_le_target_add_delta
  linarith

/-! ## Nested-bisection operation counts -/

/--
Concrete operation-count bound for a nested bisection routine.

If the outer loop runs at most `L + 1` iterations and each outer iteration runs
at most `M - 3` inner bisections, each of at most `L` iterations, then the
total number of counted primitive bisection/outer operations is bounded by
`(L + 1) * (1 + (M - 3) * L)`.
-/
def nestedBisectionStepBound (M L : ℕ) : ℕ :=
  (L + 1) * (1 + (M - 3) * L)

/--
If an implementation records concrete outer and inner iteration counts bounded
by `L + 1` and `L`, respectively, then its nested bisection operation count is
bounded by `nestedBisectionStepBound M L`.
-/
theorem nestedBisection_operation_count_le_stepBound
    {M L outerSteps innerSteps : ℕ}
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    outerSteps * (1 + (M - 3) * innerSteps) ≤
      nestedBisectionStepBound M L := by
  unfold nestedBisectionStepBound
  have hfactor :
      1 + (M - 3) * innerSteps ≤ 1 + (M - 3) * L := by
    exact Nat.add_le_add_left (Nat.mul_le_mul_left (M - 3) hinner) 1
  exact Nat.mul_le_mul houter hfactor

/--
Quadratic bound for the nested-bisection closed form. This is the finite
arithmetic step behind the usual `O(M L^2)` runtime statement.
-/
theorem nestedBisectionStepBound_le_mul_succ_sq
    {M L : ℕ} (hM : 0 < M) :
    nestedBisectionStepBound M L ≤ M * (L + 1) ^ 2 := by
  unfold nestedBisectionStepBound
  have hfactor :
      1 + (M - 3) * L ≤ M * (L + 1) := by
    have hone : 1 ≤ M := Nat.succ_le_of_lt hM
    have hmul : (M - 3) * L ≤ M * L :=
      Nat.mul_le_mul_right L (Nat.sub_le M 3)
    calc
      1 + (M - 3) * L ≤ M + M * L := Nat.add_le_add hone hmul
      _ = M * (L + 1) := by rw [Nat.mul_succ, Nat.add_comm]
  calc
    (L + 1) * (1 + (M - 3) * L)
        ≤ (L + 1) * (M * (L + 1)) :=
          Nat.mul_le_mul_left (L + 1) hfactor
    _ = M * (L + 1) ^ 2 := by ring

/--
Operation-count bound in the `O(M L^2)` finite form used by source runtime
analyses.
-/
theorem nestedBisection_operation_count_le_mul_succ_sq
    {M L outerSteps innerSteps : ℕ} (hM : 0 < M)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    outerSteps * (1 + (M - 3) * innerSteps) ≤ M * (L + 1) ^ 2 :=
  (nestedBisection_operation_count_le_stepBound houter hinner).trans
    (nestedBisectionStepBound_le_mul_succ_sq hM)

/--
Real-valued logarithmic wrapper for the finite `O(M L^2)` nested-bisection
bound.  If the iteration depth `L + 1` is bounded by a nonnegative real
quantity `R`, then the concrete operation count is bounded by `M * R^2`.
This is the bridge used by paper proofs that first choose
`L = O(log(1 / delta))` and then report the runtime in big-O notation.
-/
theorem nestedBisection_operation_count_real_le_mul_sq_of_depth_le
    {M L outerSteps innerSteps : ℕ} {R : ℝ} (hM : 0 < M)
    (hdepth : ((L + 1 : ℕ) : ℝ) ≤ R)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    ((outerSteps * (1 + (M - 3) * innerSteps) : ℕ) : ℝ) ≤
      (M : ℝ) * R ^ 2 := by
  have hcount_nat :
      outerSteps * (1 + (M - 3) * innerSteps) ≤ M * (L + 1) ^ 2 :=
    nestedBisection_operation_count_le_mul_succ_sq hM houter hinner
  have hcount :
      ((outerSteps * (1 + (M - 3) * innerSteps) : ℕ) : ℝ) ≤
        (M * (L + 1) ^ 2 : ℕ) := by
    exact_mod_cast hcount_nat
  have hsucc_nonneg : 0 ≤ ((L + 1 : ℕ) : ℝ) := by positivity
  have hR_nonneg : 0 ≤ R := hsucc_nonneg.trans hdepth
  have hsquare :
      (((L + 1 : ℕ) : ℝ) ^ 2) ≤ R ^ 2 :=
    pow_le_pow_left₀ hsucc_nonneg hdepth 2
  have hmul :
      (M : ℝ) * (((L + 1 : ℕ) : ℝ) ^ 2) ≤ (M : ℝ) * R ^ 2 :=
    mul_le_mul_of_nonneg_left hsquare (Nat.cast_nonneg M)
  exact hcount.trans (by simpa using hmul)

/--
The same bound in a source-shaped form: if each outer iteration performs one
outer comparison plus `(M - 3)` inner bisections, and each inner bisection has
at most `L` iterations, the total work is bounded by the closed form used in
runtime analyses.
-/
theorem nestedBisection_operation_count_le
    {M L outerSteps innerSteps : ℕ}
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    outerSteps + outerSteps * ((M - 3) * innerSteps) ≤
      nestedBisectionStepBound M L := by
  simpa [Nat.mul_add, Nat.mul_one, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc] using
    nestedBisection_operation_count_le_stepBound
      (M := M) (L := L) houter hinner

end AppliedModelingLib.Optimization

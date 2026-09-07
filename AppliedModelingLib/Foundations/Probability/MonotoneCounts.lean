import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Centered increments of monotone counts

This module gives a deterministic endpoint estimate for a nondecreasing
counting path.  It is useful when a counting process has exact endpoint
moments but a later argument needs to control its centered values inside a
deterministic time cell.
-/

namespace AppliedModelingLib.Probability

/-- A nondecreasing natural-valued count has every centered increment inside
a time cell bounded by its terminal centered increment plus twice the
deterministic terminal drift. -/
theorem abs_centeredCountIncrement_le_abs_terminalCenteredIncrement_add
    (count : ℝ → ℕ) (hcount : Monotone count)
    {start time duration rate : ℝ}
    (htime : start ≤ time) (htime_end : time ≤ start + duration)
    (hrate : 0 ≤ rate) :
    |((count time - count start : ℕ) : ℝ) - rate * (time - start)| ≤
      |((count (start + duration) - count start : ℕ) : ℝ) - rate * duration| +
        2 * rate * duration := by
  have htime_nonneg : 0 ≤ time - start := sub_nonneg.mpr htime
  have htime_duration : time - start ≤ duration := by linarith
  have hduration_nonneg : 0 ≤ duration := by linarith
  have hrate_time : 0 ≤ rate * (time - start) :=
    mul_nonneg hrate htime_nonneg
  have hrate_duration : 0 ≤ rate * duration :=
    mul_nonneg hrate hduration_nonneg
  have hcount_bound :
      ((count time - count start : ℕ) : ℝ) ≤
        ((count (start + duration) - count start : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_le_sub_right (hcount htime_end) (count start)
  have hrate_bound : rate * (time - start) ≤ rate * duration :=
    mul_le_mul_of_nonneg_left htime_duration hrate
  calc
    |((count time - count start : ℕ) : ℝ) - rate * (time - start)| ≤
        |((count time - count start : ℕ) : ℝ)| + |rate * (time - start)| :=
      abs_sub _ _
    _ = ((count time - count start : ℕ) : ℝ) + rate * (time - start) := by
      rw [abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg hrate_time]
    _ ≤ ((count (start + duration) - count start : ℕ) : ℝ) + rate * duration :=
      add_le_add hcount_bound hrate_bound
    _ = (((count (start + duration) - count start : ℕ) : ℝ) - rate * duration) +
        2 * rate * duration := by ring
    _ ≤ |((count (start + duration) - count start : ℕ) : ℝ) - rate * duration| +
        2 * rate * duration := by
      nlinarith [le_abs_self
        (((count (start + duration) - count start : ℕ) : ℝ) - rate * duration)]

/-- The difference of two centered, normalized monotone count increments is
controlled inside a time cell by the two normalized endpoint increments and
the two deterministic endpoint drifts. -/
theorem abs_centeredCountDifferenceIncrement_div_le
    (first second : ℝ → ℕ) (hfirst : Monotone first) (hsecond : Monotone second)
    {start time duration firstRate secondRate normalizer : ℝ}
    (htime : start ≤ time) (htime_end : time ≤ start + duration)
    (hfirstRate : 0 ≤ firstRate) (hsecondRate : 0 ≤ secondRate)
    (hnormalizer : 0 < normalizer) :
    |((((first time - first start : ℕ) : ℝ) - firstRate * (time - start)) / normalizer) -
      ((((second time - second start : ℕ) : ℝ) - secondRate * (time - start)) / normalizer)| ≤
      |(((first (start + duration) - first start : ℕ) : ℝ) - firstRate * duration) /
        normalizer| +
      |(((second (start + duration) - second start : ℕ) : ℝ) - secondRate * duration) /
        normalizer| +
      2 * firstRate * duration / normalizer +
      2 * secondRate * duration / normalizer := by
  have hfirstRaw := abs_centeredCountIncrement_le_abs_terminalCenteredIncrement_add
    first hfirst htime htime_end hfirstRate
  have hsecondRaw := abs_centeredCountIncrement_le_abs_terminalCenteredIncrement_add
    second hsecond htime htime_end hsecondRate
  have hfirstDiv :
      |(((first time - first start : ℕ) : ℝ) - firstRate * (time - start)) /
        normalizer| ≤
        |(((first (start + duration) - first start : ℕ) : ℝ) - firstRate * duration) /
          normalizer| +
        2 * firstRate * duration / normalizer := by
    calc
      |(((first time - first start : ℕ) : ℝ) - firstRate * (time - start)) /
          normalizer| =
          |((first time - first start : ℕ) : ℝ) - firstRate * (time - start)| / normalizer := by
        rw [abs_div, abs_of_pos hnormalizer]
      |((first time - first start : ℕ) : ℝ) - firstRate * (time - start)| / normalizer ≤
          (|((first (start + duration) - first start : ℕ) : ℝ) - firstRate * duration| +
            2 * firstRate * duration) / normalizer :=
        div_le_div_of_nonneg_right hfirstRaw hnormalizer.le
      _ = |(((first (start + duration) - first start : ℕ) : ℝ) - firstRate * duration) /
          normalizer| + 2 * firstRate * duration / normalizer := by
        rw [abs_div, abs_of_pos hnormalizer]
        ring
  have hsecondDiv :
      |(((second time - second start : ℕ) : ℝ) - secondRate * (time - start)) /
        normalizer| ≤
        |(((second (start + duration) - second start : ℕ) : ℝ) - secondRate * duration) /
          normalizer| +
        2 * secondRate * duration / normalizer := by
    calc
      |(((second time - second start : ℕ) : ℝ) - secondRate * (time - start)) /
          normalizer| =
          |((second time - second start : ℕ) : ℝ) - secondRate * (time - start)| / normalizer := by
        rw [abs_div, abs_of_pos hnormalizer]
      |((second time - second start : ℕ) : ℝ) - secondRate * (time - start)| / normalizer ≤
          (|((second (start + duration) - second start : ℕ) : ℝ) - secondRate * duration| +
            2 * secondRate * duration) / normalizer :=
        div_le_div_of_nonneg_right hsecondRaw hnormalizer.le
      _ = |(((second (start + duration) - second start : ℕ) : ℝ) - secondRate * duration) /
          normalizer| + 2 * secondRate * duration / normalizer := by
        rw [abs_div, abs_of_pos hnormalizer]
        ring
  calc
    |(((first time - first start : ℕ) : ℝ) - firstRate * (time - start)) / normalizer -
        (((second time - second start : ℕ) : ℝ) - secondRate * (time - start)) / normalizer| ≤
        |(((first time - first start : ℕ) : ℝ) - firstRate * (time - start)) / normalizer| +
        |(((second time - second start : ℕ) : ℝ) - secondRate * (time - start)) / normalizer| :=
      abs_sub _ _
    _ ≤ |(((first (start + duration) - first start : ℕ) : ℝ) - firstRate * duration) /
          normalizer| + 2 * firstRate * duration / normalizer +
        (|(((second (start + duration) - second start : ℕ) : ℝ) - secondRate * duration) /
          normalizer| + 2 * secondRate * duration / normalizer) := by
      exact add_le_add hfirstDiv hsecondDiv
    _ = |(((first (start + duration) - first start : ℕ) : ℝ) - firstRate * duration) /
          normalizer| +
        |(((second (start + duration) - second start : ℕ) : ℝ) - secondRate * duration) /
          normalizer| +
        2 * firstRate * duration / normalizer +
        2 * secondRate * duration / normalizer := by ring

end AppliedModelingLib.Probability

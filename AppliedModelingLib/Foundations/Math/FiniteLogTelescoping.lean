import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Finite logarithmic telescoping

Nonnegative increments divided by their updated positive cumulative total
telescope against logarithmic growth.  This is the finite form used in
harmonic-style occupancy and online-learning estimates.
-/

namespace AppliedModelingLib

open Finset

/-- A finite nonnegative-increment sequence has logarithmically bounded
updated-prefix ratios. -/
theorem sum_div_add_updatedPrefix_le_log
    (base : ℝ) (hbase : 0 < base) (increment : ℕ → ℝ)
    (hincrement : ∀ index, 0 ≤ increment index) (length : ℕ) :
    ∑ index ∈ Finset.range length,
      increment index / (base + ∑ previous ∈ Finset.range (index + 1), increment previous) ≤
        Real.log (base + ∑ index ∈ Finset.range length, increment index) - Real.log base := by
  induction length with
  | zero => simp
  | succ length ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have hprefixNonneg : 0 ≤ ∑ index ∈ Finset.range length, increment index := by
        exact Finset.sum_nonneg fun index _ => hincrement index
      have hprefixPos : 0 < base + ∑ index ∈ Finset.range length, increment index := by
        linarith
      have hupdatedPos :
          0 < base + ((∑ index ∈ Finset.range length, increment index) + increment length) := by
        linarith [hincrement length]
      have hlast :
          increment length /
              (base + ((∑ index ∈ Finset.range length, increment index) + increment length)) ≤
            Real.log (base + ((∑ index ∈ Finset.range length, increment index) + increment length)) -
              Real.log (base + ∑ index ∈ Finset.range length, increment index) := by
        calc
          increment length /
              (base + ((∑ index ∈ Finset.range length, increment index) + increment length)) =
              1 - ((base + ((∑ index ∈ Finset.range length, increment index) + increment length)) /
                (base + ∑ index ∈ Finset.range length, increment index))⁻¹ := by
                field_simp
                ring
          _ ≤ Real.log
              ((base + ((∑ index ∈ Finset.range length, increment index) + increment length)) /
                (base + ∑ index ∈ Finset.range length, increment index)) := by
                apply Real.one_sub_inv_le_log_of_pos
                exact div_pos hupdatedPos hprefixPos
          _ = Real.log (base + ((∑ index ∈ Finset.range length, increment index) + increment length)) -
              Real.log (base + ∑ index ∈ Finset.range length, increment index) := by
                rw [Real.log_div hupdatedPos.ne' hprefixPos.ne']
      calc
        _ ≤ (Real.log (base + ∑ index ∈ Finset.range length, increment index) -
            Real.log base) +
            increment length /
              (base + ((∑ index ∈ Finset.range length, increment index) + increment length)) :=
          add_le_add ih (le_refl _)
        _ ≤ (Real.log (base + ∑ index ∈ Finset.range length, increment index) -
            Real.log base) +
            (Real.log (base + ((∑ index ∈ Finset.range length, increment index) + increment length)) -
              Real.log (base + ∑ index ∈ Finset.range length, increment index)) :=
          add_le_add (le_refl _) hlast
        _ = _ := by ring_nf

/-- If a realized count is at least one quarter of its cumulative mass, its
corresponding occupancy ratio is at most four times the updated-mass ratio.
The zero-cumulative-mass case is included explicitly, so this lemma is safe
for count tables that use totalized division. -/
theorem div_le_four_mul_div_of_le_quarter
    {numerator cumulative count : ℝ}
    (hnumerator : 0 ≤ numerator) (hnumerator_le_cumulative : numerator ≤ cumulative)
    (hcount : (1 : ℝ) / 4 * cumulative ≤ count) :
    numerator / count ≤ 4 * (numerator / cumulative) := by
  have hcumulative_nonneg : 0 ≤ cumulative :=
    le_trans hnumerator hnumerator_le_cumulative
  rcases hcumulative_nonneg.eq_or_lt with hcumulative | hcumulative
  · subst cumulative
    have hnumerator_zero : numerator = 0 := by linarith
    simp [hnumerator_zero]
  · have hcount_pos : 0 < count := by
      nlinarith [hcount]
    have hcumulative_le_four_count : cumulative ≤ 4 * count := by
      nlinarith [hcount]
    have hproduct : numerator * cumulative ≤ (4 * numerator) * count := by
      calc
        numerator * cumulative ≤ numerator * (4 * count) :=
          mul_le_mul_of_nonneg_left hcumulative_le_four_count hnumerator
        _ = (4 * numerator) * count := by ring
    rw [show 4 * (numerator / cumulative) = (4 * numerator) / cumulative by ring]
    exact (div_le_div_iff₀ hcount_pos hcumulative).2 hproduct

/-- Once an initial cumulative prefix dominates a positive base, the ratios
over any subsequent consecutive block are bounded by the logarithmic
telescope starting from that base.  This is the finite suffix form of the
standard harmonic-series argument. -/
theorem sum_div_updatedPrefixFrom_le_log_of_base_le_prefix
    (base : ℝ) (hbase : 0 < base) (increment : ℕ → ℝ)
    (hincrement : ∀ index, 0 ≤ increment index) (start length : ℕ)
    (hbase_le_prefix : base ≤ ∑ index ∈ Finset.range start, increment index) :
    ∑ index ∈ Finset.range length,
      increment (start + index) /
        (∑ previous ∈ Finset.range (start + index + 1), increment previous) ≤
      Real.log (base + ∑ index ∈ Finset.range length, increment (start + index)) -
        Real.log base := by
  let shifted : ℕ → ℝ := fun index => increment (start + index)
  have hshifted : ∀ index, 0 ≤ shifted index := by
    intro index
    exact hincrement (start + index)
  have htelescope := sum_div_add_updatedPrefix_le_log base hbase shifted hshifted length
  calc
    ∑ index ∈ Finset.range length,
        increment (start + index) /
          (∑ previous ∈ Finset.range (start + index + 1), increment previous) ≤
        ∑ index ∈ Finset.range length,
          increment (start + index) /
            (base + ∑ previous ∈ Finset.range (index + 1), increment (start + previous)) := by
      apply Finset.sum_le_sum
      intro index _
      have hshiftedPrefixNonneg :
          0 ≤ ∑ previous ∈ Finset.range (index + 1), increment (start + previous) := by
        exact Finset.sum_nonneg fun previous _ => hincrement (start + previous)
      have hprefixDecomposition :
          (∑ previous ∈ Finset.range (start + index + 1), increment previous) =
            (∑ previous ∈ Finset.range start, increment previous) +
              ∑ previous ∈ Finset.range (index + 1), increment (start + previous) := by
        rw [show start + index + 1 = start + (index + 1) by omega]
        exact Finset.sum_range_add increment start (index + 1)
      have hrightPos :
          0 < base + ∑ previous ∈ Finset.range (index + 1),
            increment (start + previous) := by
        linarith
      have hdenom :
          base + ∑ previous ∈ Finset.range (index + 1), increment (start + previous) ≤
            ∑ previous ∈ Finset.range (start + index + 1), increment previous := by
        rw [hprefixDecomposition]
        linarith
      have hleftPos :
          0 < ∑ previous ∈ Finset.range (start + index + 1), increment previous :=
        lt_of_lt_of_le hrightPos hdenom
      exact (div_le_div_iff₀ hleftPos hrightPos).2
        (mul_le_mul_of_nonneg_left hdenom (hincrement (start + index)))
    _ ≤ Real.log (base + ∑ index ∈ Finset.range length, increment (start + index)) -
          Real.log base := by
      simpa only [shifted] using htelescope

/-- A consecutive block of occupancy-to-count ratios is logarithmically
bounded when each count dominates one quarter of its updated cumulative
occupancy.  This packages the counting and telescoping steps commonly used
in visitation-ratio arguments. -/
theorem sum_div_count_le_four_mul_log_of_base_le_prefix
    (base : ℝ) (hbase : 0 < base) (increment count : ℕ → ℝ)
    (hincrement : ∀ index, 0 ≤ increment index) (start length : ℕ)
    (hbase_le_prefix : base ≤ ∑ index ∈ Finset.range start, increment index)
    (hcount : ∀ index < length,
      (1 : ℝ) / 4 *
          (∑ previous ∈ Finset.range (start + index + 1), increment previous) ≤
        count (start + index)) :
    ∑ index ∈ Finset.range length, increment (start + index) / count (start + index) ≤
      4 * (Real.log (base + ∑ index ∈ Finset.range length, increment (start + index)) -
        Real.log base) := by
  have hratio : ∀ index < length,
      increment (start + index) / count (start + index) ≤
        4 * (increment (start + index) /
          ∑ previous ∈ Finset.range (start + index + 1), increment previous) := by
    intro index hindex
    apply div_le_four_mul_div_of_le_quarter
    · exact hincrement (start + index)
    · have hprefixNonneg : 0 ≤ ∑ previous ∈ Finset.range (start + index),
          increment previous := by
        exact Finset.sum_nonneg fun previous _ => hincrement previous
      rw [Finset.sum_range_succ]
      linarith
    · exact hcount index hindex
  have htelescope := sum_div_updatedPrefixFrom_le_log_of_base_le_prefix
    base hbase increment hincrement start length hbase_le_prefix
  calc
    ∑ index ∈ Finset.range length, increment (start + index) / count (start + index) ≤
        ∑ index ∈ Finset.range length,
          4 * (increment (start + index) /
            ∑ previous ∈ Finset.range (start + index + 1), increment previous) := by
      exact Finset.sum_le_sum fun index hindex =>
        hratio index (Finset.mem_range.mp hindex)
    _ = 4 * ∑ index ∈ Finset.range length,
          increment (start + index) /
            ∑ previous ∈ Finset.range (start + index + 1), increment previous := by
      rw [Finset.mul_sum]
    _ ≤ 4 * (Real.log (base + ∑ index ∈ Finset.range length, increment (start + index)) -
          Real.log base) := by
      exact mul_le_mul_of_nonneg_left htelescope (by norm_num)

/-- If every increment is at most the positive base, the preceding ratio
bound is at most four times the logarithm of one plus the block length. -/
theorem sum_div_count_le_four_mul_log_lengthSucc_of_increment_le_base
    (base : ℝ) (hbase : 0 < base) (increment count : ℕ → ℝ)
    (hincrement : ∀ index, 0 ≤ increment index)
    (hincrement_le_base : ∀ index, increment index ≤ base) (start length : ℕ)
    (hbase_le_prefix : base ≤ ∑ index ∈ Finset.range start, increment index)
    (hcount : ∀ index < length,
      (1 : ℝ) / 4 *
          (∑ previous ∈ Finset.range (start + index + 1), increment previous) ≤
        count (start + index)) :
    ∑ index ∈ Finset.range length, increment (start + index) / count (start + index) ≤
      4 * Real.log ((length : ℝ) + 1) := by
  have hratio := sum_div_count_le_four_mul_log_of_base_le_prefix
    base hbase increment count hincrement start length hbase_le_prefix hcount
  have hsum_le : ∑ index ∈ Finset.range length, increment (start + index) ≤
      (length : ℝ) * base := by
    calc
      ∑ index ∈ Finset.range length, increment (start + index) ≤
          ∑ _index ∈ Finset.range length, base := by
        exact Finset.sum_le_sum fun index _ => hincrement_le_base (start + index)
      _ = (length : ℝ) * base := by simp
  have hlog_argument_le :
      base + ∑ index ∈ Finset.range length, increment (start + index) ≤
        ((length : ℝ) + 1) * base := by
    nlinarith
  have hlog_argument_pos :
      0 < base + ∑ index ∈ Finset.range length, increment (start + index) := by
    have hsum_nonneg : 0 ≤ ∑ index ∈ Finset.range length, increment (start + index) := by
      exact Finset.sum_nonneg fun index _ => hincrement (start + index)
    linarith
  have hlog_bound :
      Real.log (base + ∑ index ∈ Finset.range length, increment (start + index)) -
          Real.log base ≤ Real.log ((length : ℝ) + 1) := by
    have hlog_le := Real.log_le_log hlog_argument_pos hlog_argument_le
    rw [Real.log_mul (by positivity) hbase.ne'] at hlog_le
    linarith
  calc
    ∑ index ∈ Finset.range length, increment (start + index) / count (start + index) ≤
        4 * (Real.log (base + ∑ index ∈ Finset.range length, increment (start + index)) -
          Real.log base) := hratio
    _ ≤ 4 * Real.log ((length : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hlog_bound (by norm_num)

/-- On a finite prefix, a monotone predicate which first holds at `start`
selects exactly the suffix beginning there.  This is the finite good-set
partition behind first-crossing arguments. -/
theorem sum_ite_eq_sum_from_first
    (predicate : ℕ → Prop) [DecidablePred predicate] (term : ℕ → ℝ) (start endIndex : ℕ)
    (hstart : start ≤ endIndex)
    (hbefore : ∀ index < start, ¬ predicate index) (hatStart : predicate start)
    (hmono : ∀ {index₁ index₂}, index₁ ≤ index₂ → predicate index₁ → predicate index₂) :
    ∑ index ∈ Finset.range endIndex, (if predicate index then term index else 0) =
      ∑ index ∈ Finset.range (endIndex - start), term (start + index) := by
  classical
  let selected : ℕ → ℝ := fun index => if predicate index then term index else 0
  have hprefixZero : ∑ index ∈ Finset.range start, selected index = 0 := by
    apply Finset.sum_eq_zero
    intro index hindex
    have hnot : ¬ predicate index := hbefore index (Finset.mem_range.mp hindex)
    simp [selected, hnot]
  have hsuffix : ∑ index ∈ Finset.Ico start endIndex, selected index =
      ∑ index ∈ Finset.Ico start endIndex, term index := by
    apply Finset.sum_congr rfl
    intro index hindex
    have hstart_le : start ≤ index := (Finset.mem_Ico.mp hindex).1
    have hselected : predicate index := hmono hstart_le hatStart
    simp [selected, hselected]
  calc
    ∑ index ∈ Finset.range endIndex, (if predicate index then term index else 0) =
        ∑ index ∈ Finset.range endIndex, selected index := by rfl
    _ = (∑ index ∈ Finset.range start, selected index) +
          ∑ index ∈ Finset.Ico start endIndex, selected index := by
      rw [Finset.sum_range_add_sum_Ico _ hstart]
    _ = ∑ index ∈ Finset.Ico start endIndex, selected index := by rw [hprefixZero, zero_add]
    _ = ∑ index ∈ Finset.Ico start endIndex, term index := hsuffix
    _ = ∑ index ∈ Finset.range (endIndex - start), term (start + index) := by
      rw [Finset.sum_Ico_eq_sum_range]

/-- The complement of a monotone predicate which first holds at `start`
selects exactly the prefix before that first crossing. -/
theorem sum_ite_not_eq_sum_prefix_before_first
    (predicate : ℕ → Prop) [DecidablePred predicate] (term : ℕ → ℝ) (start endIndex : ℕ)
    (hstart : start ≤ endIndex)
    (hbefore : ∀ index < start, ¬ predicate index) (hatStart : predicate start)
    (hmono : ∀ {index₁ index₂}, index₁ ≤ index₂ → predicate index₁ → predicate index₂) :
    ∑ index ∈ Finset.range endIndex, (if predicate index then 0 else term index) =
      ∑ index ∈ Finset.range start, term index := by
  classical
  let unselected : ℕ → ℝ := fun index => if predicate index then 0 else term index
  have hprefix : ∑ index ∈ Finset.range start, unselected index =
      ∑ index ∈ Finset.range start, term index := by
    apply Finset.sum_congr rfl
    intro index hindex
    have hnot : ¬ predicate index := hbefore index (Finset.mem_range.mp hindex)
    simp [unselected, hnot]
  have hsuffixZero : ∑ index ∈ Finset.Ico start endIndex, unselected index = 0 := by
    apply Finset.sum_eq_zero
    intro index hindex
    have hstart_le : start ≤ index := (Finset.mem_Ico.mp hindex).1
    have hselected : predicate index := hmono hstart_le hatStart
    simp [unselected, hselected]
  calc
    ∑ index ∈ Finset.range endIndex, (if predicate index then 0 else term index) =
        ∑ index ∈ Finset.range endIndex, unselected index := by rfl
    _ = (∑ index ∈ Finset.range start, unselected index) +
          ∑ index ∈ Finset.Ico start endIndex, unselected index := by
      rw [Finset.sum_range_add_sum_Ico _ hstart]
    _ = ∑ index ∈ Finset.range start, unselected index := by rw [hsuffixZero, add_zero]
    _ = ∑ index ∈ Finset.range start, term index := hprefix

end AppliedModelingLib

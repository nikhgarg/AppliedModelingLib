import PG24NoisyMatchingMarkets.MainTheorems
import Mathlib.Tactic

/-!
# PG24 Theorem 3 dense/gap probability arithmetic

This finite lemma is the source proof's dense-branch group reduction written
without choosing a syntactic ordering of colleges.  It converts a small
crossing probability for the maximum of `m` iid draws into a bound on one
draw's crossing probability.  The remaining affine cutoff and Chebyshev
steps supply the hypothesis `crossing = 1 - base^m`.
-/

namespace PG24NoisyMatchingMarkets

/--
If the iid crossing probability of a block of `m` draws is at most one half,
the one-draw crossing probability is at most twice the block crossing
probability divided by `m`.

Writing the no-crossing probability as `base`, the proof is the finite
geometric identity `1 - base^m = (1 - base) * sum_{i < m} base^i`.
-/
theorem theorem3_singleTail_le_two_mul_blockCrossing_div_card
    {base crossing : ℝ} {m : ℕ}
    (hm : 0 < m)
    (hbase_nonneg : 0 ≤ base) (hbase_le_one : base ≤ 1)
    (hcrossing : crossing = 1 - base ^ m)
    (hcrossing_le_half : crossing ≤ 1 / 2) :
    1 - base ≤ 2 * crossing / (m : ℝ) := by
  have hm_real_pos : 0 < (m : ℝ) := by
    exact_mod_cast hm
  have hpow_lower : (1 : ℝ) / 2 ≤ base ^ m := by
    rw [hcrossing] at hcrossing_le_half
    linarith
  have hsum_lower : (m : ℝ) / 2 ≤ ∑ i ∈ Finset.range m, base ^ i := by
    calc
      (m : ℝ) / 2 = ∑ _i ∈ Finset.range m, (1 : ℝ) / 2 := by
        simp
        ring
      _ ≤ ∑ i ∈ Finset.range m, base ^ i := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have him : i ≤ m := Nat.le_of_lt (Finset.mem_range.mp hi)
        exact hpow_lower.trans (pow_le_pow_of_le_one hbase_nonneg hbase_le_one him)
  have hone_sub_nonneg : 0 ≤ 1 - base := by
    linarith
  have hmul :
      ((m : ℝ) / 2) * (1 - base) ≤
        (∑ i ∈ Finset.range m, base ^ i) * (1 - base) :=
    mul_le_mul_of_nonneg_right hsum_lower hone_sub_nonneg
  have hgeom :
      (∑ i ∈ Finset.range m, base ^ i) * (1 - base) = crossing := by
    rw [geom_sum_mul_of_le_one hbase_le_one]
    exact hcrossing.symm
  rw [hgeom] at hmul
  apply (le_div_iff₀ hm_real_pos).2
  nlinarith

/--
Dense-branch low endpoint without grouping or an index ordering.  If every
active cutoff is above `floor`, a small crossing probability for an iid block
of `m` scores at that floor bounds the whole active set through the ordinary
finite union bound.

This is the corrected form of the source step at
`source_tex/proof-attenuating.tex:159-177`: the one-block upper tail is
bounded *above* by its Chebyshev estimate before the union bound is applied.
-/
theorem theorem3_dense_low_affordance_le_card_mul_blockCrossing
    {n m : ℕ} (noiseLaw : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure noiseLaw]
    (active : Finset (Fin n)) (cutoff : Fin n → ℝ) (floor value crossing : ℝ)
    (hm : 0 < m)
    (hfloor : ∀ c ∈ active, floor ≤ cutoff c)
    (hcrossing :
      crossing = 1 -
        (AppliedModelingLib.Probability.lowerCDFMass noiseLaw (floor - value)) ^ m)
    (hcrossing_le_half : crossing ≤ 1 / 2) :
    cutoffAffordanceProbability
        (MeasureTheory.Measure.pi (fun _ : Fin n => noiseLaw)) active value cutoff ≤
      (active.card : ℝ) * (2 * crossing / (m : ℝ)) := by
  apply cutoffAffordanceProbability_iidProduct_le_card_mul_of_upperTailMass_le
  intro c hc
  have hshift : floor - value ≤ cutoff c - value := by
    linarith [hfloor c hc]
  have htail_eq :
      AppliedModelingLib.Probability.upperTailMass noiseLaw (floor - value) =
        1 - AppliedModelingLib.Probability.lowerCDFMass noiseLaw (floor - value) := by
    have hsum :=
      AppliedModelingLib.Probability.lowerCDFMass_add_upperTailMass_eq_one
        noiseLaw (floor - value)
    linarith
  calc
    AppliedModelingLib.Probability.upperTailMass noiseLaw (cutoff c - value) ≤
        AppliedModelingLib.Probability.upperTailMass noiseLaw (floor - value) :=
      AppliedModelingLib.Probability.upperTailMass_antitone noiseLaw hshift
    _ = 1 - AppliedModelingLib.Probability.lowerCDFMass noiseLaw (floor - value) :=
      htail_eq
    _ ≤ 2 * crossing / (m : ℝ) :=
      theorem3_singleTail_le_two_mul_blockCrossing_div_card hm
        (AppliedModelingLib.Probability.lowerCDFMass_nonneg noiseLaw _)
        (AppliedModelingLib.Probability.lowerCDFMass_le_one noiseLaw _)
        hcrossing hcrossing_le_half

/--
Dense-branch high endpoint.  A cutoff window contained in an active coalition
inherits a constant-cutoff iid block lower bound, so the proof never needs a
named sorted representation of the cutoff vector.
-/
theorem theorem3_dense_high_affordance_gt_one_sub_of_window
    {n : ℕ} (noiseLaw : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure noiseLaw]
    (active window : Finset (Fin n)) (cutoff : Fin n → ℝ)
    (value ceiling epsilon : ℝ)
    (hwindow_subset : window ⊆ active)
    (hceiling : ∀ c ∈ window, cutoff c ≤ ceiling)
    (hblock :
      1 - epsilon <
        1 -
          (AppliedModelingLib.Probability.lowerCDFMass noiseLaw (ceiling - value)) ^
            window.card) :
    1 - epsilon <
      cutoffAffordanceProbability
        (MeasureTheory.Measure.pi (fun _ : Fin n => noiseLaw)) active value cutoff := by
  have hwindow_high :
      1 - epsilon <
        cutoffAffordanceProbability
          (MeasureTheory.Measure.pi (fun _ : Fin n => noiseLaw)) window value cutoff := by
    exact
      AppliedModelingLib.Matching.lt_cutoffCrossingProbability_iidProduct_of_lt_one_sub_lowerCDFMass_pow_card_of_cutoff_le
        noiseLaw window hceiling hblock
  exact lt_of_lt_of_le hwindow_high
    (cutoffAffordanceProbability_mono_active
      (MeasureTheory.Measure.pi (fun _ : Fin n => noiseLaw)) hwindow_subset)

end PG24NoisyMatchingMarkets

import PG24NoisyMatchingMarkets.Theorem3LargeGapTailRepair
import Mathlib.Tactic

/-!
# PG24 Theorem 3 large-gap bridge

The finite cutoff argument and the probability argument are separate proof
obligations.  This module handles only the latter: given a proved eventual
gap between a low and high cutoff, it exposes the required comparison with
the source centering correction and derives high full-coalition affordance.

Thus a caller must supply the finite rank geometry as an explicit eventual
gap inequality, rather than relying on a theorem conclusion or an opaque
source assumption.

The source locations are `source_tex/proof-attenuating.tex:251-357` and its
reuse in `source_tex/proofs-extended.tex:5-17`.
-/

open Filter Topology
open MeasureTheory
open Asymptotics

namespace PG24NoisyMatchingMarkets

noncomputable section

/--
A centering correction that is little-o of a positive diverging gap scale is
eventually negligible relative to that scale.  This is the analytic form of
the source comparison between `E[X^(C)] + C^phi4` and the large cutoff gap;
it does not assume either term is bounded.
-/
theorem theorem3_slack_sub_gap_tendsto_atBot_of_isLittleO
    {gapLower slack : ℕ → ℝ}
    (hgap_toTop : Tendsto gapLower atTop atTop)
    (hslack_little : slack =o[atTop] gapLower) :
    Tendsto (fun C : ℕ => slack C - gapLower C) atTop atBot := by
  refine tendsto_atBot.mpr ?_
  intro bound
  have hsmall := hslack_little.bound (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hsmall,
    tendsto_atTop.mp hgap_toTop (max 0 (-2 * bound))]
    with C hsmall_C hscale_C
  have hscale_nonneg : 0 ≤ gapLower C :=
    le_trans (le_max_left _ _) hscale_C
  have hscale_bound : -2 * bound ≤ gapLower C :=
    le_trans (le_max_right _ _) hscale_C
  have hslack_upper : slack C ≤ gapLower C / 2 := by
    calc
      slack C ≤ |slack C| := le_abs_self _
      _ = ‖slack C‖ := by simp only [Real.norm_eq_abs]
      _ ≤ (1 / 2 : ℝ) * ‖gapLower C‖ := hsmall_C
      _ = gapLower C / 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg hscale_nonneg]
        ring
  linarith

/--
If two selected colleges are separated by an explicit gap, and the value's
displacement below the high cutoff is asymptotically smaller than that gap,
then the low cutoff minus the value tends to minus infinity.

The centering/displacement term is left visible as `slack`; this is the
source obligation behind the use of `E[X^(C)] + C^phi4` at
`proof-attenuating.tex:313-340`.
-/
theorem theorem3_cutoff_sub_value_tendsto_atBot_of_cutoff_gap
    {cutoff : ∀ C : ℕ, Fin (C + 1) → ℝ}
    (lowCollege highCollege : ∀ C : ℕ, Fin (C + 1))
    {gapLower slack value : ℕ → ℝ}
    (hgap : ∀ᶠ C : ℕ in atTop,
      gapLower C < cutoff C (highCollege C) - cutoff C (lowCollege C))
    (hvalue_below_high_rank : ∀ᶠ C : ℕ in atTop,
      cutoff C (highCollege C) - value C ≤ slack C)
    (hslack_dominated : Tendsto (fun C : ℕ => slack C - gapLower C) atTop atBot) :
    Tendsto (fun C : ℕ => cutoff C (lowCollege C) - value C) atTop atBot := by
  refine tendsto_atBot.mpr ?_
  intro bound
  filter_upwards [tendsto_atBot.mp hslack_dominated bound,
    hgap, hvalue_below_high_rank]
    with C hdominated_C hgap_C hvalue_C
  calc
    cutoff C (lowCollege C) - value C ≤ slack C - gapLower C := by
      linarith
    _ ≤ bound := hdominated_C

/--
The preceding cutoff-gap bridge with the source-relevant little-o condition
spelled out, rather than packaged as a preproved `slack - gap` limit.
-/
theorem theorem3_cutoff_sub_value_tendsto_atBot_of_cutoff_gap_of_isLittleO
    {cutoff : ∀ C : ℕ, Fin (C + 1) → ℝ}
    (lowCollege highCollege : ∀ C : ℕ, Fin (C + 1))
    {gapLower slack value : ℕ → ℝ}
    (hgap : ∀ᶠ C : ℕ in atTop,
      gapLower C < cutoff C (highCollege C) - cutoff C (lowCollege C))
    (hvalue_below_high_rank : ∀ᶠ C : ℕ in atTop,
      cutoff C (highCollege C) - value C ≤ slack C)
    (hgap_toTop : Tendsto gapLower atTop atTop)
    (hslack_little : slack =o[atTop] gapLower) :
    Tendsto (fun C : ℕ => cutoff C (lowCollege C) - value C) atTop atBot := by
  apply theorem3_cutoff_sub_value_tendsto_atBot_of_cutoff_gap lowCollege highCollege
  · exact hgap
  · exact hvalue_below_high_rank
  · exact theorem3_slack_sub_gap_tendsto_atBot_of_isLittleO hgap_toTop hslack_little

/--
The complete analytic high-side closure: an explicit low/high cutoff gap and
a visible asymptotic dominance condition imply high full-coalition
affordance.  This uses the probability-measure tail argument from
`Theorem3LargeGapTailRepair`, not the source's single-sample Chebyshev step.
-/
theorem theorem3_fullAffordance_eventually_one_sub_lt_of_cutoff_gap
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {cutoff : ∀ C : ℕ, Fin (C + 1) → ℝ}
    (lowCollege highCollege : ∀ C : ℕ, Fin (C + 1))
    {gapLower slack value : ℕ → ℝ}
    (hgap : ∀ᶠ C : ℕ in atTop,
      gapLower C < cutoff C (highCollege C) - cutoff C (lowCollege C))
    (hvalue_below_high_rank : ∀ᶠ C : ℕ in atTop,
      cutoff C (highCollege C) - value C ≤ slack C)
    (hslack_dominated : Tendsto (fun C : ℕ => slack C - gapLower C) atTop atBot)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ C : ℕ in atTop,
      1 - epsilon <
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1))) (value C) (cutoff C) := by
  apply theorem3_fullAffordance_eventually_one_sub_lt_of_cutoff_sub_valueSeq_tendsto_atBot
    noiseLaw lowCollege value epsilon hepsilon
  apply theorem3_cutoff_sub_value_tendsto_atBot_of_cutoff_gap
    lowCollege highCollege
  · exact hgap
  · exact hvalue_below_high_rank
  · exact hslack_dominated

/--
The high-affordance closure in the direct little-o form used by the source's
large-gap branch.
-/
theorem theorem3_fullAffordance_eventually_one_sub_lt_of_cutoff_gap_of_isLittleO
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {cutoff : ∀ C : ℕ, Fin (C + 1) → ℝ}
    (lowCollege highCollege : ∀ C : ℕ, Fin (C + 1))
    {gapLower slack value : ℕ → ℝ}
    (hgap : ∀ᶠ C : ℕ in atTop,
      gapLower C < cutoff C (highCollege C) - cutoff C (lowCollege C))
    (hvalue_below_high_rank : ∀ᶠ C : ℕ in atTop,
      cutoff C (highCollege C) - value C ≤ slack C)
    (hgap_toTop : Tendsto gapLower atTop atTop)
    (hslack_little : slack =o[atTop] gapLower)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ C : ℕ in atTop,
      1 - epsilon <
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1))) (value C) (cutoff C) := by
  exact theorem3_fullAffordance_eventually_one_sub_lt_of_cutoff_gap
    noiseLaw lowCollege highCollege hgap hvalue_below_high_rank
    (theorem3_slack_sub_gap_tendsto_atBot_of_isLittleO hgap_toTop hslack_little)
    epsilon hepsilon

end

end PG24NoisyMatchingMarkets

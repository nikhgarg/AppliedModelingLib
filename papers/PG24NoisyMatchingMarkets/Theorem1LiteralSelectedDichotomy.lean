import PG24NoisyMatchingMarkets.Theorem1LiteralSelectedCutoffBridge
import Mathlib.Tactic

/-!
# PG24 Theorem 1 literal selected-cutoff dichotomy

The dense-window / large-gap split is a finite fact about the actual selected
cutoff vector.  This isolates that fact from the two analytic branches so a
final source conclusion need not accept a branch label or an ordering of
college names as an assumption.
-/

open Filter MeasureTheory

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u v

/--
For the literal selected cutoff vector, canonical finite ranking gives the
source dense-window / large-gap alternative eventually.  The cutoff vector is
not assumed ordered: `theorem3_ranked_denseWindow_or_rounded_large_gap` orders
it by its verified finite ranking.
-/
theorem theorem1_literal_selected_denseWindow_or_large_gap_eventually
    {StudentType : Type u} [MeasurableSpace StudentType]
    {Cutoff : Type v}
    (noiseLaw eta : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {totalSupply alpha beta gamma : ℝ}
    (inst : ∀ C : ℕ,
      PG24LiteralBasicTwoScaleInstance C noiseLaw eta totalSupply alpha
        StudentType Cutoff)
    (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    ∀ᶠ C : ℕ in atTop,
      (∃ start : ℕ,
        start + theorem3DenseWindowCount C (theorem1TailPhi2 beta gamma) ≤
            theorem3DenseGapBlockCount C
              (theorem1TailPhi2 beta gamma) (theorem1TailPhi3 beta gamma) *
              theorem3DenseWindowCount C (theorem1TailPhi2 beta gamma) ∧
          theorem1TailDenseRankWindow
            (theorem3RankedCutoffNat C (inst C).selectedCutoffVector) start
            (theorem3DenseWindowCount C (theorem1TailPhi2 beta gamma))
            (theorem1DenseDeviationRadius C beta gamma)) ∨
        theorem3RankedCutoffNat C (inst C).selectedCutoffVector 0 +
          (theorem3DenseGapBlockCount C
            (theorem1TailPhi2 beta gamma) (theorem1TailPhi3 beta gamma) : ℝ) *
            theorem1DenseDeviationRadius C beta gamma <
          theorem3RankedCutoffNat C (inst C).selectedCutoffVector
            (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma)) := by
  filter_upwards [eventually_gt_atTop 0,
    theorem1DenseWindowCount_eventually_le_earlyPrefixRank hbeta hgamma]
      with C hC_pos hfit
  exact theorem3_ranked_denseWindow_or_rounded_large_gap
    (inst C).selectedCutoffVector hC_pos hfit

/--
An eventual semantic branch split is enough to close a nonnegative sequence
once each branch supplies a vanishing upper bound.  The alternatives are kept
at the level of their proved bounds, so this lemma does not choose a branch
or encode it in a name-dependent selector.
-/
theorem theorem1_tendsto_zero_of_eventually_branch_bound
    (f denseBound largeGapBound : ℕ → ℝ)
    (hnonneg : ∀ C : ℕ, 0 ≤ f C)
    (hdense_zero : Tendsto denseBound atTop (nhds 0))
    (hlargeGap_zero : Tendsto largeGapBound atTop (nhds 0))
    (hbranch : ∀ᶠ C : ℕ in atTop,
      f C ≤ denseBound C ∨ f C ≤ largeGapBound C) :
    Tendsto f atTop (nhds 0) := by
  have hupper_zero : Tendsto
      (fun C : ℕ => max (denseBound C) (largeGapBound C))
      atTop (nhds 0) := by
    simpa using hdense_zero.max hlargeGap_zero
  have hupper : ∀ᶠ C : ℕ in atTop,
      f C ≤ max (denseBound C) (largeGapBound C) := by
    filter_upwards [hbranch] with C hC
    rcases hC with hdense | hlargeGap
    · exact hdense.trans (le_max_left _ _)
    · exact hlargeGap.trans (le_max_right _ _)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
    hupper_zero (Filter.Eventually.of_forall hnonneg) hupper

/--
The epsilon-form version of the literal branch closure.  It is appropriate
when one branch has only a qualitative tail limit, so the final theorem does
not falsely advertise a shared polynomial rate.
-/
theorem theorem1_tendsto_zero_of_eventually_branch_epsilon
    (f : ℕ → ℝ) (denseCase largeGapCase : ℕ → Prop)
    (hnonneg : ∀ C : ℕ, 0 ≤ f C)
    (hdense : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ C : ℕ in atTop, denseCase C → f C < epsilon)
    (hlargeGap : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ C : ℕ in atTop, largeGapCase C → f C < epsilon)
    (hgeometry : ∀ᶠ C : ℕ in atTop, denseCase C ∨ largeGapCase C) :
    Tendsto f atTop (nhds 0) := by
  rw [tendsto_order]
  constructor
  · intro lower hlower
    filter_upwards with C
    exact lt_of_lt_of_le hlower (hnonneg C)
  · intro upper hupper
    filter_upwards [hdense upper hupper, hlargeGap upper hupper, hgeometry]
      with C hdense_C hlargeGap_C hgeometry_C
    rcases hgeometry_C with hdense_case | hlargeGap_case
    · exact hdense_C hdense_case
    · exact hlargeGap_C hlargeGap_case

end

end PG24NoisyMatchingMarkets

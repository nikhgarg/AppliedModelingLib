import PG24NoisyMatchingMarkets.MainTheorems

/-!
# PG24 Theorem 3 large-gap tail repair

The high-value half of the source large-gap branch
(`source_tex/proof-attenuating.tex:313-357`, reused by
`source_tex/proofs-extended.tex:5-17`) only needs one low-cutoff college to
be crossed with probability tending to one.  That follows from the lower tail
of every probability measure and does not require a finite variance for one
noise draw.  The source instead invokes a single-sample Chebyshev calculation.

This module records the direct probability argument.  It has no capacity,
cutoff-geometry, or theorem-conclusion premise; callers must establish the
growing cutoff/value gap separately.
-/

open Filter Topology
open MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

/--
For iid noise, if one selected cutoff lies arbitrarily far below a sequence
of student values, that college is crossed with probability tending to one.
-/
theorem theorem3_singleCollegeAffordance_tendsto_one_of_cutoff_sub_valueSeq_tendsto_atBot
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {cutoff : ∀ C : ℕ, Fin (C + 1) → ℝ}
    (college : ∀ C : ℕ, Fin (C + 1))
    (value : ℕ → ℝ)
    (hgap : Tendsto (fun C : ℕ => cutoff C (college C) - value C) atTop atBot) :
    Tendsto
      (fun C : ℕ =>
        singleCollegeAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (value C) (cutoff C) (college C))
      atTop (nhds 1) := by
  have htail :=
    AppliedModelingLib.Probability.upperTailMass_tendsto_one_atBot noiseLaw
  refine Tendsto.congr' ?_ (htail.comp hgap)
  filter_upwards with C
  simpa only [singleCollegeAffordanceProbability] using
    (AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_eq_upperTailMass
      noiseLaw (value C) (cutoff C) (college C)).symm

/-- A fixed student value is the constant-sequence specialization. -/
theorem theorem3_singleCollegeAffordance_tendsto_one_of_cutoff_sub_value_tendsto_atBot
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {cutoff : ∀ C : ℕ, Fin (C + 1) → ℝ}
    (college : ∀ C : ℕ, Fin (C + 1))
    (v : ℝ)
    (hgap : Tendsto (fun C : ℕ => cutoff C (college C) - v) atTop atBot) :
    Tendsto
      (fun C : ℕ =>
        singleCollegeAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          v (cutoff C) (college C))
      atTop (nhds 1) := by
  simpa using
    (theorem3_singleCollegeAffordance_tendsto_one_of_cutoff_sub_valueSeq_tendsto_atBot
      noiseLaw college (fun _ : ℕ => v) hgap)

/--
The full coalition affordance probability inherits the high-value endpoint
from any one college whose cutoff/value gap tends to `-infinity`.
-/
theorem theorem3_fullAffordance_eventually_one_sub_lt_of_cutoff_sub_valueSeq_tendsto_atBot
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {cutoff : ∀ C : ℕ, Fin (C + 1) → ℝ}
    (college : ∀ C : ℕ, Fin (C + 1))
    (value : ℕ → ℝ) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hgap : Tendsto (fun C : ℕ => cutoff C (college C) - value C) atTop atBot) :
    ∀ᶠ C : ℕ in atTop,
      1 - epsilon <
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1))) (value C) (cutoff C) := by
  have hsingle :=
    theorem3_singleCollegeAffordance_tendsto_one_of_cutoff_sub_valueSeq_tendsto_atBot
      noiseLaw college value hgap
  have hsingle_high :
      ∀ᶠ C : ℕ in atTop,
        1 - epsilon <
          singleCollegeAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (value C) (cutoff C) (college C) :=
    hsingle (isOpen_Ioi.mem_nhds (by linarith : 1 - epsilon < (1 : ℝ)))
  filter_upwards [hsingle_high] with C hC
  have hsingle_le :
      singleCollegeAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (value C) (cutoff C) (college C) ≤
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1))) (value C) (cutoff C) := by
    simpa only [singleCollegeAffordanceProbability,
      cutoffAffordanceProbability] using
      (AppliedModelingLib.Matching.singleCutoffCrossingProbability_le_cutoffCrossingProbability
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (Finset.univ : Finset (Fin (C + 1))) (by simp)
        (value C) (cutoff C))
  exact lt_of_lt_of_le hC hsingle_le

/-- A fixed student value is the constant-sequence specialization. -/
theorem theorem3_fullAffordance_eventually_one_sub_lt_of_cutoff_sub_value_tendsto_atBot
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {cutoff : ∀ C : ℕ, Fin (C + 1) → ℝ}
    (college : ∀ C : ℕ, Fin (C + 1))
    (v epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hgap : Tendsto (fun C : ℕ => cutoff C (college C) - v) atTop atBot) :
    ∀ᶠ C : ℕ in atTop,
      1 - epsilon <
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1))) v (cutoff C) := by
  simpa using
    (theorem3_fullAffordance_eventually_one_sub_lt_of_cutoff_sub_valueSeq_tendsto_atBot
      noiseLaw college (fun _ : ℕ => v) epsilon hepsilon hgap)

end

end PG24NoisyMatchingMarkets

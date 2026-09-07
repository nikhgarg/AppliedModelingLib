import FalahatgarEtAl2017MaxingRanking.PickAnchorProbability
import Mathlib.Analysis.Complex.Exponential

/-!
# Pick-Anchor hypergeometric tail

The exact miss probability is a falling-factorial ratio.  This file develops
the finite factorwise domination by the corresponding with-replacement power.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL

/-- Sampling without replacement misses no more often than sampling with replacement. -/
theorem descFactorial_ratio_le_complement_pow
    (population topCount sampleCount : ℕ)
    (htop : topCount ≤ population)
    (hsample : sampleCount ≤ population - topCount) :
    ((population - topCount).descFactorial sampleCount : ℝ) /
        (population.descFactorial sampleCount : ℝ) ≤
      (((population - topCount : ℕ) : ℝ) / (population : ℝ)) ^ sampleCount := by
  induction sampleCount with
  | zero => simp
  | succ sampleCount ih =>
      have hprevious : sampleCount ≤ population - topCount := by omega
      have hih := ih hprevious
      have havailable : topCount + sampleCount + 1 ≤ population := by omega
      have hsamplePopulation : sampleCount ≤ population := by omega
      have hpositivePopulation : 0 < (population : ℝ) := by
        exact_mod_cast (Nat.zero_lt_of_lt (lt_of_lt_of_le (Nat.succ_pos _) havailable))
      have hpositiveFactor : 0 < ((population - sampleCount : ℕ) : ℝ) := by
        exact_mod_cast (Nat.sub_pos_of_lt (by omega : sampleCount < population))
      have hpositiveFactorReal : 0 < (population : ℝ) - (sampleCount : ℝ) := by
        rw [← Nat.cast_sub hsamplePopulation]
        exact hpositiveFactor
      have hpositiveDesc : 0 < (population.descFactorial sampleCount : ℝ) := by
        exact_mod_cast (Nat.descFactorial_pos.mpr hsamplePopulation)
      have hfactor :
          ((population - topCount - sampleCount : ℕ) : ℝ) /
              ((population - sampleCount : ℕ) : ℝ) ≤
            ((population - topCount : ℕ) : ℝ) / (population : ℝ) := by
        rw [Nat.cast_sub hprevious, Nat.cast_sub htop,
          Nat.cast_sub hsamplePopulation]
        apply (div_le_div_iff₀ hpositiveFactorReal hpositivePopulation).mpr
        nlinarith [mul_nonneg (show 0 ≤ (topCount : ℝ) by positivity)
          (show 0 ≤ (sampleCount : ℝ) by positivity)]
      have hfactorNonneg : 0 ≤
          ((population - topCount - sampleCount : ℕ) : ℝ) /
              ((population - sampleCount : ℕ) : ℝ) := by positivity
      have hratioNonneg : 0 ≤
          ((population - topCount).descFactorial sampleCount : ℝ) /
              (population.descFactorial sampleCount : ℝ) := by positivity
      rw [Nat.descFactorial_succ, Nat.descFactorial_succ,
        Nat.cast_mul, Nat.cast_mul]
      have hsplit :
          (((population - topCount - sampleCount : ℕ) : ℝ) *
              ((population - topCount).descFactorial sampleCount : ℝ)) /
              (((population - sampleCount : ℕ) : ℝ) *
                (population.descFactorial sampleCount : ℝ)) =
            (((population - topCount - sampleCount : ℕ) : ℝ) /
                ((population - sampleCount : ℕ) : ℝ)) *
              (((population - topCount).descFactorial sampleCount : ℝ) /
                (population.descFactorial sampleCount : ℝ)) := by
        field_simp [ne_of_gt hpositiveFactor, ne_of_gt hpositiveDesc]
      rw [hsplit, pow_succ]
      calc
        (((population - topCount - sampleCount : ℕ) : ℝ) /
            ((population - sampleCount : ℕ) : ℝ)) *
            (((population - topCount).descFactorial sampleCount : ℝ) /
              (population.descFactorial sampleCount : ℝ)) ≤
          (((population - topCount - sampleCount : ℕ) : ℝ) /
              ((population - sampleCount : ℕ) : ℝ)) *
            ((((population - topCount : ℕ) : ℝ) / (population : ℝ)) ^ sampleCount) :=
              mul_le_mul_of_nonneg_left hih hfactorNonneg
        _ ≤ (((population - topCount : ℕ) : ℝ) / (population : ℝ)) *
            ((((population - topCount : ℕ) : ℝ) / (population : ℝ)) ^ sampleCount) :=
              mul_le_mul_of_nonneg_right hfactor (by positivity)
        _ = _ := by ring

/--
The exact Pick-Anchor sampler has no larger top-set miss probability than
independent uniform draws with replacement.  The near-full-sample branch is
handled deterministically.
-/
theorem pickAnchor_miss_probability_le_complement_pow
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (count : ℕ) (hcount : count ≤ Fintype.card Arm) (top : Finset Arm) :
    pmfProbClassical (pickAnchorUniformSampleLaw count hcount)
      (fun sample => ¬ ∃ pivot, pivot ∈ top ∧ pivot ∈ pickAnchorSampleSet sample) ≤
      (((Fintype.card Arm - top.card : ℕ) : ℝ) / (Fintype.card Arm : ℝ)) ^ count := by
  have htop : top.card ≤ Fintype.card Arm := by
    simpa using Finset.card_le_card (Finset.subset_univ top)
  by_cases hspace : count ≤ Fintype.card Arm - top.card
  · rw [pickAnchor_miss_probability_eq_descFactorial_ratio count hcount top]
    exact descFactorial_ratio_le_complement_pow
      (Fintype.card Arm) top.card count htop hspace
  · have hcapacity : Fintype.card Arm < count + top.card := by omega
    rw [pickAnchor_miss_probability_zero_of_card_add_gt_armCount count hcount top hcapacity]
    positivity

/--
The with-replacement top-set-miss probability is at most `δ / 2` once the
sample count reaches the logarithmic Pick-Anchor threshold.  This is the
analytic step used in Appendix A.5 after the exact without-replacement
calculation above.
-/
theorem complement_pow_le_delta_half_of_log_sample_lower_bound
    (population topCount count : ℕ) (delta : ℝ)
    (hpopulation : 0 < population) (htop : 0 < topCount)
    (htopLe : topCount ≤ population) (hdeltaPos : 0 < delta)
    (hdeltaLe : delta ≤ 1)
    (hcount : (population : ℝ) / (topCount : ℝ) * Real.log (2 / delta) ≤ count) :
    (((population - topCount : ℕ) : ℝ) / (population : ℝ)) ^ count ≤ delta / 2 := by
  have hpopulationReal : 0 < (population : ℝ) := by exact_mod_cast hpopulation
  have htopReal : 0 < (topCount : ℝ) := by exact_mod_cast htop
  have hratioGtOne : 1 < 2 / delta := by
    rw [lt_div_iff₀ hdeltaPos]
    nlinarith
  have hlogPos : 0 < Real.log (2 / delta) := Real.log_pos hratioGtOne
  have hrawPos : 0 <
      (population : ℝ) / (topCount : ℝ) * Real.log (2 / delta) := by
    exact mul_pos (div_pos hpopulationReal htopReal) hlogPos
  have hcountRealPos : 0 < (count : ℝ) := lt_of_lt_of_le hrawPos hcount
  have htopLeReal : (topCount : ℝ) ≤ (population : ℝ) := by exact_mod_cast htopLe
  have hratioLeOne : (topCount : ℝ) / (population : ℝ) ≤ 1 := by
    exact (div_le_one₀ hpopulationReal).mpr htopLeReal
  have hscaledLe : (count : ℝ) * ((topCount : ℝ) / (population : ℝ)) ≤ count := by
    simpa using mul_le_mul_of_nonneg_left hratioLeOne (le_of_lt hcountRealPos)
  have hbase :
      1 - ((count : ℝ) * ((topCount : ℝ) / (population : ℝ))) / (count : ℝ) =
        ((population - topCount : ℕ) : ℝ) / (population : ℝ) := by
    rw [Nat.cast_sub htopLe]
    field_simp [ne_of_gt hcountRealPos, ne_of_gt hpopulationReal]
  have hpower :
      (((population - topCount : ℕ) : ℝ) / (population : ℝ)) ^ count ≤
        Real.exp (-((count : ℝ) * ((topCount : ℝ) / (population : ℝ)))) := by
    rw [← hbase]
    exact Real.one_sub_div_pow_le_exp_neg hscaledLe
  have hlogLe : Real.log (2 / delta) ≤
      (count : ℝ) * ((topCount : ℝ) / (population : ℝ)) := by
    calc
      Real.log (2 / delta) =
          ((population : ℝ) / (topCount : ℝ) * Real.log (2 / delta)) *
            ((topCount : ℝ) / (population : ℝ)) := by
              field_simp [ne_of_gt hpopulationReal, ne_of_gt htopReal]
      _ ≤ (count : ℝ) * ((topCount : ℝ) / (population : ℝ)) :=
        mul_le_mul_of_nonneg_right hcount (le_of_lt (div_pos htopReal hpopulationReal))
  have hexpLe :
      Real.exp (-((count : ℝ) * ((topCount : ℝ) / (population : ℝ)))) ≤ delta / 2 := by
    calc
      Real.exp (-((count : ℝ) * ((topCount : ℝ) / (population : ℝ)))) ≤
          Real.exp (-Real.log (2 / delta)) := by
            exact Real.exp_le_exp.mpr (by linarith)
      _ = delta / 2 := by
        rw [Real.exp_neg, Real.exp_log (div_pos (by norm_num) hdeltaPos)]
        field_simp [ne_of_gt hdeltaPos]
  exact hpower.trans hexpLe

/--
The source's ceiling-and-cap Pick-Anchor rule hits every top set of size
`cutoff` with probability at least `1 - δ / 2`.  The capped branch is exact;
the uncapped branch uses the hypergeometric and exponential bounds above.
-/
theorem pickAnchor_miss_probability_le_delta_half
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (cutoff : ℕ) (delta : ℝ) (top : Finset Arm)
    (hcutoff : 0 < cutoff) (htopCard : top.card = cutoff)
    (hdeltaPos : 0 < delta) (hdeltaLe : delta ≤ 1) :
    pmfProbClassical
      (pickAnchorUniformSampleLaw
        (pickAnchorSampleCount (Fintype.card Arm) cutoff delta)
        (pickAnchorSampleCount_le_armCount (Fintype.card Arm) cutoff delta))
      (fun sample => ¬ ∃ pivot, pivot ∈ top ∧ pivot ∈ pickAnchorSampleSet sample) ≤
      delta / 2 := by
  have htop : top.Nonempty := by
    apply Finset.card_pos.mp
    simpa [htopCard] using hcutoff
  have hcutoffLe : cutoff ≤ Fintype.card Arm := by
    rw [← htopCard]
    exact Finset.card_le_card (Finset.subset_univ top)
  by_cases hraw : Fintype.card Arm ≤
      ⌈(Fintype.card Arm : ℝ) / (cutoff : ℝ) * Real.log (2 / delta)⌉₊
  · rw [pickAnchor_miss_probability_zero_of_rawCeiling cutoff delta top htop hraw]
    positivity
  · have hceilLt : ⌈(Fintype.card Arm : ℝ) / (cutoff : ℝ) *
        Real.log (2 / delta)⌉₊ < Fintype.card Arm := by omega
    have hceilLe : ⌈(Fintype.card Arm : ℝ) / (cutoff : ℝ) *
        Real.log (2 / delta)⌉₊ ≤ Fintype.card Arm := hceilLt.le
    have hsampleEq : pickAnchorSampleCount (Fintype.card Arm) cutoff delta =
        ⌈(Fintype.card Arm : ℝ) / (cutoff : ℝ) * Real.log (2 / delta)⌉₊ := by
      rw [pickAnchorSampleCount]
      exact Nat.min_eq_right hceilLe
    have hceilLower : (Fintype.card Arm : ℝ) / (cutoff : ℝ) *
        Real.log (2 / delta) ≤
        (⌈(Fintype.card Arm : ℝ) / (cutoff : ℝ) * Real.log (2 / delta)⌉₊ : ℕ) :=
      Nat.le_ceil _
    have hsampleLower : (Fintype.card Arm : ℝ) / (cutoff : ℝ) *
        Real.log (2 / delta) ≤
        (pickAnchorSampleCount (Fintype.card Arm) cutoff delta : ℕ) := by
      simpa [hsampleEq] using hceilLower
    refine
      (pickAnchor_miss_probability_le_complement_pow
        (pickAnchorSampleCount (Fintype.card Arm) cutoff delta)
        (pickAnchorSampleCount_le_armCount (Fintype.card Arm) cutoff delta) top).trans ?_
    simpa [htopCard] using
      (complement_pow_le_delta_half_of_log_sample_lower_bound
        (Fintype.card Arm) cutoff
        (pickAnchorSampleCount (Fintype.card Arm) cutoff delta) delta
        (by omega) hcutoff hcutoffLe hdeltaPos hdeltaLe hsampleLower)

/--
Appendix A.5's Pick-Anchor union bound, instantiated with the source's
uniform without-replacement sampler.  The remaining hypothesis is precisely
the sampled-winner guarantee supplied by Seq-Eliminate (or another subroutine)
on that same finite sample space.
-/
theorem pickAnchor_goodAnchor_probability_of_uniformSample_and_sampleWinner
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (cutoff : ℕ) (delta epsilon : ℝ) (top : Finset Arm)
    (preferenceGap : Arm → Arm → ℝ)
    (winner : finiteFreshList Arm
      (pickAnchorSampleCount (Fintype.card Arm) cutoff delta) ∅ → Arm)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 ≤ epsilon)
    (hcutoff : 0 < cutoff) (htopCard : top.card = cutoff)
    (htopRank : ∀ pivot ∈ top,
      (strictlyBetterArms preferenceGap pivot).card ≤ cutoff)
    (hdeltaPos : 0 < delta) (hdeltaLe : delta ≤ 1)
    (hwinnerFailure : pmfProbClassical
      (pickAnchorUniformSampleLaw
        (pickAnchorSampleCount (Fintype.card Arm) cutoff delta)
        (pickAnchorSampleCount_le_armCount (Fintype.card Arm) cutoff delta))
      (fun sample => ¬ ∀ arm ∈ pickAnchorSampleSet sample,
        -epsilon ≤ preferenceGap (winner sample) arm) ≤ delta / 2) :
    1 - delta ≤ pmfProbClassical
      (pickAnchorUniformSampleLaw
        (pickAnchorSampleCount (Fintype.card Arm) cutoff delta)
        (pickAnchorSampleCount_le_armCount (Fintype.card Arm) cutoff delta))
      (fun sample => GoodAnchor preferenceGap epsilon cutoff (winner sample)) := by
  apply pickAnchor_goodAnchor_probability_of_topSetHit_and_sampleWinner
    (pickAnchorUniformSampleLaw
      (pickAnchorSampleCount (Fintype.card Arm) cutoff delta)
      (pickAnchorSampleCount_le_armCount (Fintype.card Arm) cutoff delta))
    pickAnchorSampleSet winner top preferenceGap epsilon cutoff
    hantisymmetric hsst hepsilon htopRank delta
  · exact pickAnchor_miss_probability_le_delta_half cutoff delta top hcutoff htopCard
      hdeltaPos hdeltaLe
  · exact hwinnerFailure

end FalahatgarEtAl2017MaxingRanking

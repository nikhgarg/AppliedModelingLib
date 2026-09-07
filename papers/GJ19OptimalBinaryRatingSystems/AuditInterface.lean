import GJ19OptimalBinaryRatingSystems.Theorem32Appendix
import GJ19OptimalBinaryRatingSystems.AppendixB
import GJ19OptimalBinaryRatingSystems.SourceDefinitions
import GJ19OptimalBinaryRatingSystems.ExperimentTheorems
import GJ19OptimalBinaryRatingSystems.ComparativeStatics
import GJ19OptimalBinaryRatingSystems.PartitionTieSelection
import GJ19OptimalBinaryRatingSystems.Assumptions

/-!
# Audited Review Surface: Designing Optimal Binary Rating Systems

This audited review surface exposes the Section 3, Appendix B, and Appendix C
mathematical surface of Garg--Johari (2019), including the finite
equalized-rate optimizer, Theorem 3.1 value/rate decomposition, Theorem 3.2
calculated-grid approximation/runtime certificate, large-deviation
characterization, convergence/learning lemmas, and Kendall/Spearman examples.
-/

namespace GJ19OptimalBinaryRatingSystems

noncomputable section

open AppliedModelingLib.Probability
open Filter Topology
open MeasureTheory

/-- Source object: Bernoulli KL divergence used in the binary-rate formulas. -/
abbrev paperBernoulliKL (a b : ℝ) : ℝ :=
  sourceBernoulliKL a b

/--
Source object, support-safe form: Bernoulli KL is finite only for thresholds
inside the Bernoulli support interval.
-/
abbrev paperBernoulliKLTop (a b : ℝ) : WithTop ℝ :=
  sourceBernoulliKLTop a b

/-- Source object: adjacent binary-rating threshold rate. -/
abbrev paperAdjacentBinaryRatingRate (gHi gLo tHi tLo : ℝ) : ℝ :=
  adjacentBinaryRatingRate gHi gLo tHi tLo

/-- Source object: support-safe adjacent binary-rating threshold rate. -/
abbrev paperAdjacentBinaryRatingRateTop
    (gHi gLo tHi tLo : ℝ) : WithTop ℝ :=
  adjacentBinaryRatingRateTop gHi gLo tHi tLo

/-- Source object: bracketed expression inside Lemma 3.1's closed rate. -/
abbrev paperAdjacentBinaryClosedRateBase
    (gLo gHi tLo tHi : ℝ) : ℝ :=
  adjacentBinaryRatingClosedRateBase gLo gHi tLo tHi

/-- Source object: Lemma 3.1 closed adjacent binary-rate expression. -/
abbrev paperAdjacentBinaryClosedRate
    (gLo gHi tLo tHi : ℝ) : ℝ :=
  adjacentBinaryRatingClosedRate gLo gHi tLo tHi

/-- KL divergence formula displayed below Theorem 3.1. -/
theorem definition_bernoulli_kl_formula (a b : ℝ) :
    paperBernoulliKL a b =
      a * Real.log (a / b) +
        (1 - a) * Real.log ((1 - a) / (1 - b)) :=
  sourceBernoulliKL_eq_formula a b

/--
Support-safe Bernoulli KL convention used when the optimization threshold is
treated as an extended finite-support rate.
-/
theorem definition_bernoulli_kl_top_formula (a b : ℝ) :
    paperBernoulliKLTop a b =
      if 0 ≤ a ∧ a ≤ 1 then
        (paperBernoulliKL a b : WithTop ℝ)
      else
        ⊤ :=
  sourceBernoulliKLTop_eq_source_formula a b

/--
Theorem 3.1 rate expression for adjacent binary-rating levels.

Source status: exact source formula, with the threshold minimization encoded as
an infimum over real thresholds.
-/
theorem theorem31_adjacent_binary_rate_formula
    (gHi gLo tHi tLo : ℝ) :
    paperAdjacentBinaryRatingRate gHi gLo tHi tLo =
      sInf (Set.range fun a : ℝ =>
        gHi * paperBernoulliKL a tHi +
          gLo * paperBernoulliKL a tLo) :=
  adjacentBinaryRatingRate_eq_source_formula gHi gLo tHi tLo

/--
Support-safe Theorem 3.1 adjacent-rate expression. This is the convention to
use for future finite-support LDP endpoints, so thresholds outside `[0,1]`
cannot create misleading real-valued rates.

Source status: support-safe Lean convention for the same source formula.
-/
theorem theorem31_adjacent_binary_rate_top_formula
    (gHi gLo tHi tLo : ℝ) :
    paperAdjacentBinaryRatingRateTop gHi gLo tHi tLo =
      sInf (Set.range fun a : ℝ =>
        withTopRealScale gHi (paperBernoulliKLTop a tHi) +
          withTopRealScale gLo (paperBernoulliKLTop a tLo)) :=
  adjacentBinaryRatingRateTop_eq_source_formula gHi gLo tHi tLo

/-- Lemma 3.1 bracketed base expression inside the closed adjacent rate. -/
theorem lemma31_closed_adjacent_rate_base_formula
    (gLo gHi tLo tHi : ℝ) :
    paperAdjacentBinaryClosedRateBase gLo gHi tLo tHi =
      ((1 - tLo) ^ (gLo / (gLo + gHi))) *
          ((1 - tHi) ^ (gHi / (gLo + gHi))) +
        (tLo ^ (gLo / (gLo + gHi))) *
          (tHi ^ (gHi / (gLo + gHi))) :=
  adjacentBinaryRatingClosedRateBase_eq_source_formula gLo gHi tLo tHi

/--
Lemma 3.1 closed-form adjacent-rate expression.

Source status: exact displayed Lemma 3.1 algebraic formula.
-/
theorem lemma31_closed_adjacent_rate_formula
    (gLo gHi tLo tHi : ℝ) :
    paperAdjacentBinaryClosedRate gLo gHi tLo tHi =
      -(gLo + gHi) *
        Real.log
          (((1 - tLo) ^ (gLo / (gLo + gHi))) *
              ((1 - tHi) ^ (gHi / (gLo + gHi))) +
            (tLo ^ (gLo / (gLo + gHi))) *
              (tHi ^ (gHi / (gLo + gHi)))) :=
  adjacentBinaryRatingClosedRate_eq_source_formula gLo gHi tLo tHi

/--
At the weighted geometric common threshold, the adjacent KL objective equals
the closed expression displayed in Lemma 3.1.

Source status: derived source subclaim used in the proof of Lemma 3.1.
-/
theorem lemma31_closed_adjacent_rate_value_at_weighted_threshold
    {gLo gHi tLo tHi : ℝ} (hG : gHi + gLo ≠ 0)
    (htLo0 : 0 < tLo) (htLo1 : tLo < 1)
    (htHi0 : 0 < tHi) (htHi1 : tHi < 1) :
    twoBernoulliThresholdRate gHi gLo tHi tLo
        (weightedBernoulliCommonThreshold gHi gLo tHi tLo) =
      paperAdjacentBinaryClosedRate gLo gHi tLo tHi :=
  adjacentBinaryThresholdRate_weightedCommonThreshold_eq_closedRate
    hG htLo0 htLo1 htHi0 htHi1

/--
Finite Lemma 3.1 equalization bridge: once adjacent closed rates are all equal,
the worst-adjacent closed-rate objective has that common value.
-/
theorem lemma31_equalized_closed_adjacent_rates_realize_objective {m : ℕ}
    (g t : Fin (m + 2) → ℝ)
    (h : BinaryClosedAdjacentRatesEqualize g t)
    (i : Fin (m + 1)) :
    binaryClosedAdjacentRateObjective g t =
      binaryClosedAdjacentRateAt g t i :=
  binaryClosedAdjacentRateObjective_eq_rate_of_equalizes g t h i

/-- First endpoint branch of the Lemma 3.1 adjacent-rate formula. -/
theorem lemma31_endpoint_aware_adjacent_rate_first_branch {m : ℕ}
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (i : Fin (m + 1)) (hi : i.val = 0) :
    binaryEndpointAwareAdjacentRate successProb sampleRate i =
      sampleRate (adjacentHighIndex i) *
        (-Real.log (1 - successProb (adjacentHighIndex i))) :=
  binaryEndpointAwareAdjacentRate_first successProb sampleRate i hi

/-- Last endpoint branch of the Lemma 3.1 adjacent-rate formula. -/
theorem lemma31_endpoint_aware_adjacent_rate_last_branch {m : ℕ}
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (i : Fin (m + 1)) (hfirst : i.val ≠ 0) (hlast : i.val = m) :
    binaryEndpointAwareAdjacentRate successProb sampleRate i =
      sampleRate (adjacentLowIndex i) *
        (-Real.log (successProb (adjacentLowIndex i))) :=
  binaryEndpointAwareAdjacentRate_last successProb sampleRate i hfirst hlast

/-- Interior branch of the Lemma 3.1 adjacent-rate formula. -/
theorem lemma31_endpoint_aware_adjacent_rate_interior_branch {m : ℕ}
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (i : Fin (m + 1)) (hfirst : i.val ≠ 0) (hlast : i.val ≠ m) :
    binaryEndpointAwareAdjacentRate successProb sampleRate i =
      weightedBernoulliClosedThresholdRate
        (sampleRate (adjacentHighIndex i))
        (sampleRate (adjacentLowIndex i))
        (successProb (adjacentHighIndex i))
        (successProb (adjacentLowIndex i)) :=
  binaryEndpointAwareAdjacentRate_interior successProb sampleRate i hfirst hlast

/--
Interior Lemma 3.1 strict monotonicity: strictly moving an interior lower
endpoint upward while keeping the upper endpoint no higher strictly lowers that
adjacent rate.
-/
theorem lemma31_endpoint_aware_interior_rate_strictly_decreases_of_low_shrink
    {m : ℕ}
    (sampleRate : Fin (m + 2) → ℝ)
    (candidate alt : Fin (m + 2) → ℝ)
    (hcandidate : BinaryEndpointLevelVector candidate)
    (halt : BinaryEndpointLevelVector alt)
    (i : Fin (m + 1)) (hfirst : i.val ≠ 0) (hlast : i.val ≠ m)
    (hsample_high : 0 < sampleRate (adjacentHighIndex i))
    (hsample_low : 0 < sampleRate (adjacentLowIndex i))
    (hlow : candidate (adjacentLowIndex i) < alt (adjacentLowIndex i))
    (hhi_le : alt (adjacentHighIndex i) ≤ candidate (adjacentHighIndex i)) :
    binaryEndpointAwareAdjacentRate alt sampleRate i <
      binaryEndpointAwareAdjacentRate candidate sampleRate i :=
  binaryEndpointAwareAdjacentRate_interior_lt_of_low_strict_shrink
    sampleRate candidate alt hcandidate halt i hfirst hlast
    hsample_high hsample_low hlow hhi_le

/--
Interior Lemma 3.1 strict monotonicity: weakly moving an interior lower endpoint
upward and strictly moving the upper endpoint downward strictly lowers that
adjacent rate.
-/
theorem lemma31_endpoint_aware_interior_rate_strictly_decreases_of_high_shrink
    {m : ℕ}
    (sampleRate : Fin (m + 2) → ℝ)
    (candidate alt : Fin (m + 2) → ℝ)
    (hcandidate : BinaryEndpointLevelVector candidate)
    (halt : BinaryEndpointLevelVector alt)
    (i : Fin (m + 1)) (hfirst : i.val ≠ 0) (hlast : i.val ≠ m)
    (hsample_high : 0 < sampleRate (adjacentHighIndex i))
    (hsample_low : 0 < sampleRate (adjacentLowIndex i))
    (hlow_le : candidate (adjacentLowIndex i) ≤ alt (adjacentLowIndex i))
    (hhi_lt : alt (adjacentHighIndex i) < candidate (adjacentHighIndex i)) :
    binaryEndpointAwareAdjacentRate alt sampleRate i <
      binaryEndpointAwareAdjacentRate candidate sampleRate i :=
  binaryEndpointAwareAdjacentRate_interior_lt_of_high_strict_shrink
    sampleRate candidate alt hcandidate halt i hfirst hlast
    hsample_high hsample_low hlow_le hhi_lt

/-- One-interior-level endpoint vector `0, 1/2, 1` for the finite system. -/
def lemma31_one_interior_half_level : Fin (1 + 2) → ℝ :=
  binaryEndpointOneInteriorHalfLevel

/-- The one-interior-level midpoint vector satisfies the endpoint convention. -/
theorem lemma31_one_interior_half_level_isEndpointLevelVector :
    BinaryEndpointLevelVector lemma31_one_interior_half_level :=
  binaryEndpointOneInteriorHalfLevel_isEndpointLevelVector

/--
For one interior level, the midpoint `1/2` equalizes the two endpoint-aware
adjacent rates.
-/
theorem lemma31_one_interior_half_level_equalizes
    (sampleRate : Fin (1 + 2) → ℝ) :
    BinaryEndpointAwareAdjacentRatesEqualize
      lemma31_one_interior_half_level sampleRate :=
  binaryEndpointOneInteriorHalfLevel_equalizes sampleRate

/-- With one interior level, the endpoint-aware equalized vector exists uniquely. -/
theorem lemma31_one_interior_equalized_rates_exist_unique
    (sampleRate : Fin (1 + 2) → ℝ)
    (hsample_high :
      ∀ i : Fin (1 + 1), 0 < sampleRate (adjacentHighIndex i))
    (hsample_low :
      ∀ i : Fin (1 + 1), 0 < sampleRate (adjacentLowIndex i)) :
    ∃! levels : Fin (1 + 2) → ℝ,
      BinaryEndpointLevelVector levels ∧
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate :=
  binaryEndpointAwareAdjacentRatesEqualize_existsUnique_one
    sampleRate hsample_high hsample_low

/--
For one interior level, the unique equalized vector is also the strict maximin
optimizer of the endpoint-aware adjacent-rate objective.
-/
theorem lemma31_one_interior_equalized_rates_exist_unique_strictMaximizerOn
    (sampleRate : Fin (1 + 2) → ℝ)
    (hsample_high :
      ∀ i : Fin (1 + 1), 0 < sampleRate (adjacentHighIndex i))
    (hsample_low :
      ∀ i : Fin (1 + 1), 0 < sampleRate (adjacentLowIndex i)) :
    ∃! levels : Fin (1 + 2) → ℝ,
      BinaryEndpointLevelVector levels ∧
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate ∧
          AppliedModelingLib.Optimization.IsStrictMaximizerOn
            (BinaryEndpointLevelVector : (Fin (1 + 2) → ℝ) → Prop)
            (fun candidate : Fin (1 + 2) → ℝ =>
              binaryEndpointAwareAdjacentRateObjective candidate sampleRate)
            levels := by
  rcases
    lemma31_one_interior_equalized_rates_exist_unique
      sampleRate hsample_high hsample_low with
    ⟨levels, hlevels, huniq⟩
  refine ⟨levels, ?_, ?_⟩
  · rcases hlevels.2.exists_common_rate with ⟨r, hr⟩
    exact
      ⟨hlevels.1, hlevels.2,
        binaryEndpointAwareAdjacentRateObjective_isStrictMaximizerOn_of_equalized
          (m := 1) (by norm_num) sampleRate levels hlevels.1
          hsample_high hsample_low hr⟩
  · intro alt halt
    exact huniq alt ⟨halt.1, halt.2.1⟩

/-- First endpoint inverse used by the source's rate-shooting construction. -/
def lemma31_first_endpoint_level_of_rate (g r : ℝ) : ℝ :=
  binaryEndpointFirstLevelOfRate g r

/-- Last endpoint inverse used by the source's rate-shooting construction. -/
def lemma31_last_endpoint_level_of_rate (g r : ℝ) : ℝ :=
  binaryEndpointLastLevelOfRate g r

/-- The first endpoint inverse is feasible for positive weight and target rate. -/
theorem lemma31_first_endpoint_level_of_rate_is_interior
    {g r : ℝ} (hg : 0 < g) (hr : 0 < r) :
    lemma31_first_endpoint_level_of_rate g r ∈ Set.Ioo (0 : ℝ) 1 :=
  binaryEndpointFirstLevelOfRate_mem_Ioo hg hr

/-- The last endpoint inverse is feasible for positive weight and target rate. -/
theorem lemma31_last_endpoint_level_of_rate_is_interior
    {g r : ℝ} (hg : 0 < g) (hr : 0 < r) :
    lemma31_last_endpoint_level_of_rate g r ∈ Set.Ioo (0 : ℝ) 1 :=
  binaryEndpointLastLevelOfRate_mem_Ioo hg hr

/-- The first endpoint inverse realizes the requested endpoint-aware rate. -/
theorem lemma31_first_endpoint_level_of_rate_realizes
    {g r : ℝ} (hg : 0 < g) :
    g * (-Real.log (1 - lemma31_first_endpoint_level_of_rate g r)) = r :=
  binaryEndpointFirstLevelOfRate_realizes hg

/-- The last endpoint inverse realizes the requested endpoint-aware rate. -/
theorem lemma31_last_endpoint_level_of_rate_realizes
    {g r : ℝ} (hg : 0 < g) :
    g * (-Real.log (lemma31_last_endpoint_level_of_rate g r)) = r :=
  binaryEndpointLastLevelOfRate_realizes hg

/-- The first endpoint inverse is strictly increasing in the target rate. -/
theorem lemma31_first_endpoint_level_of_rate_strictMono
    {g : ℝ} (hg : 0 < g) :
    StrictMono (lemma31_first_endpoint_level_of_rate g) :=
  binaryEndpointFirstLevelOfRate_strictMono hg

/-- The last endpoint inverse is strictly decreasing in the target rate. -/
theorem lemma31_last_endpoint_level_of_rate_strictAnti
    {g : ℝ} (hg : 0 < g) :
    StrictAnti (lemma31_last_endpoint_level_of_rate g) :=
  binaryEndpointLastLevelOfRate_strictAnti hg

/-- The first endpoint inverse is continuous in the target rate. -/
theorem lemma31_first_endpoint_level_of_rate_continuous (g : ℝ) :
    Continuous (lemma31_first_endpoint_level_of_rate g) :=
  binaryEndpointFirstLevelOfRate_continuous g

/-- The last endpoint inverse is continuous in the target rate. -/
theorem lemma31_last_endpoint_level_of_rate_continuous (g : ℝ) :
    Continuous (lemma31_last_endpoint_level_of_rate g) :=
  binaryEndpointLastLevelOfRate_continuous g

/-- The first endpoint rate is strictly increasing in its endpoint level. -/
theorem lemma31_first_endpoint_rate_strictMonoOn
    {g : ℝ} (hg : 0 < g) :
    StrictMonoOn (fun p : ℝ => g * (-Real.log (1 - p))) (Set.Iio 1) :=
  binaryEndpointFirstRate_strictMonoOn hg

/--
First endpoint inverse comparison: the selected level is below `p` exactly
when the target rate is below the endpoint rate at `p`.
-/
theorem lemma31_first_endpoint_level_of_rate_lt_iff
    {g r p : ℝ} (hg : 0 < g) (hp : p < 1) :
    lemma31_first_endpoint_level_of_rate g r < p ↔
      r < g * (-Real.log (1 - p)) :=
  binaryEndpointFirstLevelOfRate_lt_iff hg hp

/-- The last endpoint rate is strictly decreasing in its endpoint level. -/
theorem lemma31_last_endpoint_rate_strictAntiOn
    {g : ℝ} (hg : 0 < g) :
    StrictAntiOn (fun p : ℝ => g * (-Real.log p)) (Set.Ioi 0) :=
  binaryEndpointLastRate_strictAntiOn hg

/--
Last endpoint inverse comparison: `p` is below the selected level exactly when
the target rate is below the endpoint rate at `p`.
-/
theorem lemma31_lt_last_endpoint_level_of_rate_iff
    {g r p : ℝ} (hg : 0 < g) (hp : 0 < p) :
    p < lemma31_last_endpoint_level_of_rate g r ↔
      r < g * (-Real.log p) :=
  lt_binaryEndpointLastLevelOfRate_iff hg hp

/--
Endpoint-inverse crossing for the finite Lemma 3.1 shooting interval.  The
crossing target rate is positive and is exactly the point where the first and
last endpoint inverse levels meet.
-/
theorem lemma31_endpoint_inverse_crossing_exists_unique
    {gFirst gLast : ℝ} (hgFirst : 0 < gFirst) (hgLast : 0 < gLast) :
    ∃! r : ℝ,
      0 < r ∧ binaryEndpointInverseGap gFirst gLast r = 0 ∧
        ∀ z : ℝ, 0 ≤ binaryEndpointInverseGap gFirst gLast z ↔ r ≤ z :=
  binaryEndpointInverseGap_existsUnique_pos_zero_and_nonneg_iff
    hgFirst hgLast

/--
Below the endpoint-inverse crossing, the first selected endpoint level is
strictly below the last selected endpoint level.
-/
theorem lemma31_first_endpoint_level_lt_last_endpoint_level_of_lt_crossing
    {gFirst gLast crossing r : ℝ}
    (hcross :
      binaryEndpointInverseGap gFirst gLast crossing = 0 ∧
        ∀ z : ℝ, 0 ≤ binaryEndpointInverseGap gFirst gLast z ↔
          crossing ≤ z)
    (hr : r < crossing) :
    lemma31_first_endpoint_level_of_rate gFirst r <
      lemma31_last_endpoint_level_of_rate gLast r :=
  binaryEndpointFirstLevelOfRate_lt_lastLevelOfRate_of_lt_inverseGap_crossing
    hcross hr

/--
At or above the endpoint-inverse crossing, the last selected endpoint level is
no larger than the first selected endpoint level.
-/
theorem lemma31_last_endpoint_level_le_first_endpoint_level_of_crossing_le
    {gFirst gLast crossing r : ℝ}
    (hcross :
      binaryEndpointInverseGap gFirst gLast crossing = 0 ∧
        ∀ z : ℝ, 0 ≤ binaryEndpointInverseGap gFirst gLast z ↔
          crossing ≤ z)
    (hr : crossing ≤ r) :
    lemma31_last_endpoint_level_of_rate gLast r ≤
      lemma31_first_endpoint_level_of_rate gFirst r :=
  binaryEndpointLastLevelOfRate_le_firstLevelOfRate_of_inverseGap_crossing_le
    hcross hr

/--
For two interior levels, the middle adjacent closed rate induced by the two
endpoint inverse levels at target rate `r`.
-/
def lemma31_two_interior_middle_rate (gLo gHi r : ℝ) : ℝ :=
  binaryEndpointTwoInteriorMiddleRate gLo gHi r

/--
For two interior levels, the scalar target-rate gap.  A zero of this gap is
exactly the middle-rate equation needed by the equalized-rate construction.
-/
def lemma31_two_interior_middle_rate_gap (gLo gHi r : ℝ) : ℝ :=
  binaryEndpointTwoInteriorMiddleRateGap gLo gHi r

/-- The two-interior middle-rate function is continuous at positive target rates. -/
theorem lemma31_two_interior_middle_rate_continuousAt
    {gLo gHi r : ℝ} (hgLo : 0 < gLo) (hgHi : 0 < gHi) (hr : 0 < r) :
    ContinuousAt (lemma31_two_interior_middle_rate gLo gHi) r :=
  binaryEndpointTwoInteriorMiddleRate_continuousAt hgLo hgHi hr

/-- The two-interior scalar target-rate gap is continuous at positive target rates. -/
theorem lemma31_two_interior_middle_rate_gap_continuousAt
    {gLo gHi r : ℝ} (hgLo : 0 < gLo) (hgHi : 0 < gHi) (hr : 0 < r) :
    ContinuousAt (lemma31_two_interior_middle_rate_gap gLo gHi) r :=
  binaryEndpointTwoInteriorMiddleRateGap_continuousAt hgLo hgHi hr

/-- The two-interior scalar target-rate gap is continuous on positive rates. -/
theorem lemma31_two_interior_middle_rate_gap_continuousOn_Ioi
    {gLo gHi : ℝ} (hgLo : 0 < gLo) (hgHi : 0 < gHi) :
    ContinuousOn (lemma31_two_interior_middle_rate_gap gLo gHi)
      (Set.Ioi (0 : ℝ)) :=
  binaryEndpointTwoInteriorMiddleRateGap_continuousOn_Ioi hgLo hgHi

/--
At the endpoint-inverse crossing, the two-interior scalar gap is negative.
This supplies the upper sign for the scalar IVT proof.
-/
theorem lemma31_two_interior_middle_rate_gap_negative_at_endpoint_crossing
    {gLo gHi crossing : ℝ}
    (hgLo : 0 < gLo) (hgHi : 0 < gHi) (hcrossing : 0 < crossing)
    (hcross : binaryEndpointInverseGap gLo gHi crossing = 0) :
    lemma31_two_interior_middle_rate_gap gLo gHi crossing < 0 :=
  binaryEndpointTwoInteriorMiddleRateGap_neg_at_inverseGap_crossing
    hgLo hgHi hcrossing hcross

/--
Two-interior-level target-rate bridge for Lemma 3.1.  Once a target rate
solves the scalar middle-rate equation between the two endpoint inverses, it
gives an equalized endpoint-aware level vector.
-/
theorem lemma31_two_interior_equalized_rates_exist_from_target_rate
    (sampleRate : Fin (2 + 2) → ℝ)
    (hsample_high :
      ∀ i : Fin (2 + 1), 0 < sampleRate (adjacentHighIndex i))
    (hsample_low :
      ∀ i : Fin (2 + 1), 0 < sampleRate (adjacentLowIndex i))
    {r : ℝ} (hr : 0 < r)
    (horder :
      lemma31_first_endpoint_level_of_rate
          (sampleRate
            (adjacentHighIndex (firstAdjacentIndex : Fin (2 + 1)))) r <
        lemma31_last_endpoint_level_of_rate
          (sampleRate
            (adjacentLowIndex (lastAdjacentIndex : Fin (2 + 1)))) r)
    (hmiddle :
      weightedBernoulliClosedThresholdRate
          (sampleRate (adjacentHighIndex (1 : Fin (2 + 1))))
          (sampleRate (adjacentLowIndex (1 : Fin (2 + 1))))
          (lemma31_last_endpoint_level_of_rate
            (sampleRate
              (adjacentLowIndex (lastAdjacentIndex : Fin (2 + 1)))) r)
          (lemma31_first_endpoint_level_of_rate
            (sampleRate
              (adjacentHighIndex (firstAdjacentIndex : Fin (2 + 1)))) r) =
        r) :
    ∃ levels : Fin (2 + 2) → ℝ,
      BinaryEndpointLevelVector levels ∧
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate :=
  binaryEndpointAwareAdjacentRatesEqualize_exists_two_of_target_rate
    sampleRate hsample_high hsample_low hr horder hmiddle

/--
Two-interior-level target-rate bridge in unique-existence form.  Once the
scalar middle-rate equation is solved, the source's equalized level vector is
unique.
-/
theorem lemma31_two_interior_equalized_rates_exist_unique_from_target_rate
    (sampleRate : Fin (2 + 2) → ℝ)
    (hsample_high :
      ∀ i : Fin (2 + 1), 0 < sampleRate (adjacentHighIndex i))
    (hsample_low :
      ∀ i : Fin (2 + 1), 0 < sampleRate (adjacentLowIndex i))
    {r : ℝ} (hr : 0 < r)
    (horder :
      lemma31_first_endpoint_level_of_rate
          (sampleRate
            (adjacentHighIndex (firstAdjacentIndex : Fin (2 + 1)))) r <
        lemma31_last_endpoint_level_of_rate
          (sampleRate
            (adjacentLowIndex (lastAdjacentIndex : Fin (2 + 1)))) r)
    (hmiddle :
      weightedBernoulliClosedThresholdRate
          (sampleRate (adjacentHighIndex (1 : Fin (2 + 1))))
          (sampleRate (adjacentLowIndex (1 : Fin (2 + 1))))
          (lemma31_last_endpoint_level_of_rate
            (sampleRate
              (adjacentLowIndex (lastAdjacentIndex : Fin (2 + 1)))) r)
          (lemma31_first_endpoint_level_of_rate
            (sampleRate
              (adjacentHighIndex (firstAdjacentIndex : Fin (2 + 1)))) r) =
        r) :
    ∃! levels : Fin (2 + 2) → ℝ,
      BinaryEndpointLevelVector levels ∧
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate :=
  binaryEndpointAwareAdjacentRatesEqualize_existsUnique_two_of_target_rate
    sampleRate hsample_high hsample_low hr horder hmiddle

/-- Finite Lemma 3.1 for two interior levels: the equalized vector exists uniquely. -/
theorem lemma31_two_interior_equalized_rates_exist_unique
    (sampleRate : Fin (2 + 2) → ℝ)
    (hsample_high :
      ∀ i : Fin (2 + 1), 0 < sampleRate (adjacentHighIndex i))
    (hsample_low :
      ∀ i : Fin (2 + 1), 0 < sampleRate (adjacentLowIndex i)) :
    ∃! levels : Fin (2 + 2) → ℝ,
      BinaryEndpointLevelVector levels ∧
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate :=
  binaryEndpointAwareAdjacentRatesEqualize_existsUnique_two
    sampleRate hsample_high hsample_low

/--
For two interior levels, the unique equalized vector is also the strict
maximin optimizer of the endpoint-aware adjacent-rate objective.
-/
theorem lemma31_two_interior_equalized_rates_exist_unique_strictMaximizerOn
    (sampleRate : Fin (2 + 2) → ℝ)
    (hsample_high :
      ∀ i : Fin (2 + 1), 0 < sampleRate (adjacentHighIndex i))
    (hsample_low :
      ∀ i : Fin (2 + 1), 0 < sampleRate (adjacentLowIndex i)) :
    ∃! levels : Fin (2 + 2) → ℝ,
      BinaryEndpointLevelVector levels ∧
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate ∧
          AppliedModelingLib.Optimization.IsStrictMaximizerOn
            (BinaryEndpointLevelVector : (Fin (2 + 2) → ℝ) → Prop)
            (fun candidate : Fin (2 + 2) → ℝ =>
              binaryEndpointAwareAdjacentRateObjective candidate sampleRate)
            levels := by
  rcases
    lemma31_two_interior_equalized_rates_exist_unique
      sampleRate hsample_high hsample_low with
    ⟨levels, hlevels, huniq⟩
  refine ⟨levels, ?_, ?_⟩
  · rcases hlevels.2.exists_common_rate with ⟨r, hr⟩
    exact
      ⟨hlevels.1, hlevels.2,
        binaryEndpointAwareAdjacentRateObjective_isStrictMaximizerOn_of_equalized
          (m := 2) (by norm_num) sampleRate levels hlevels.1
          hsample_high hsample_low hr⟩
  · intro alt halt
    exact huniq alt ⟨halt.1, halt.2.1⟩

/--
Finite Lemma 3.1 forward-cascade certificate: for more than one interior
level, a feasible clipped shooting cascade whose terminal scalar gap is zero
gives the unique equalized endpoint-aware level vector.
-/
theorem lemma31_forward_clipped_equalized_rates_exist_unique_from_scalar_certificate
    {m : ℕ} (hm : 1 < m)
    (sampleRate : Fin (m + 2) → ℝ) (r : ℝ)
    (hsample_high :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hsample_low :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (hlevels :
      BinaryEndpointLevelVector (binaryEndpointForwardClippedLevels sampleRate r))
    (hfeasible :
      ∀ n : ℕ, n + 2 < m →
        WeightedBernoulliHighEndpointTargetFeasible
          (binaryEndpointSampleRateNat sampleRate (n + 2))
          (binaryEndpointSampleRateNat sampleRate (n + 1))
          (binaryEndpointForwardClippedLevelNat sampleRate
            (binaryEndpointForwardClippedCap sampleRate r) r (n + 1))
          (binaryEndpointForwardClippedCap sampleRate r) r)
    (hgap : binaryEndpointForwardClippedTerminalGap sampleRate r = 0) :
    ∃! levels : Fin (m + 2) → ℝ,
      BinaryEndpointLevelVector levels ∧
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate :=
  binaryEndpointAwareAdjacentRatesEqualize_existsUnique_of_forward_clipped_certificate
    hm sampleRate r hsample_high hsample_low hlevels hfeasible hgap

/--
Finite Lemma 3.1 forward-cascade certificate, with endpoint feasibility derived
from the scalar target rate, feasible nonterminal steps, and terminal order.
-/
theorem lemma31_forward_clipped_equalized_rates_exist_unique_from_terminal_scalar_certificate
    {m : ℕ} (hm : 1 < m)
    (sampleRate : Fin (m + 2) → ℝ) {r : ℝ}
    (hr : 0 < r)
    (hsample_high :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hsample_low :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (hfeasible :
      ∀ n : ℕ, n + 2 < m →
        WeightedBernoulliHighEndpointTargetFeasible
          (binaryEndpointSampleRateNat sampleRate (n + 2))
          (binaryEndpointSampleRateNat sampleRate (n + 1))
          (binaryEndpointForwardClippedLevelNat sampleRate
            (binaryEndpointForwardClippedCap sampleRate r) r (n + 1))
          (binaryEndpointForwardClippedCap sampleRate r) r)
    (hterminal :
      binaryEndpointForwardClippedLevelNat sampleRate
          (binaryEndpointForwardClippedCap sampleRate r) r (m - 1) <
        binaryEndpointForwardClippedCap sampleRate r)
    (hgap : binaryEndpointForwardClippedTerminalGap sampleRate r = 0) :
    ∃! levels : Fin (m + 2) → ℝ,
      BinaryEndpointLevelVector levels ∧
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate :=
  binaryEndpointAwareAdjacentRatesEqualize_existsUnique_of_forward_clipped_scalar_certificate
    hm sampleRate hr hsample_high hsample_low hfeasible hterminal hgap

/--
Finite Lemma 3.1 for more than one interior level: positive adjacent sample
rates determine a unique endpoint-normalized binary level vector whose adjacent
closed rates are all equal.
-/
theorem lemma31_forward_clipped_equalized_rates_exist_unique
    {m : ℕ} (hm : 1 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k) :
    ∃! levels : Fin (m + 2) → ℝ,
      BinaryEndpointLevelVector levels ∧
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate :=
  binaryEndpointAwareAdjacentRatesEqualize_existsUnique_of_forward_clipped
    hm sampleRate hsample_pos

/--
Finite Lemma 3.1 for more than one interior level, in the paper's maximin
form: the unique equalized endpoint-normalized level vector is the strict
maximizer of the finite worst-adjacent rate.
-/
theorem lemma31_forward_clipped_equalized_rates_exist_unique_strictMaximizerOn
    {m : ℕ} (hm : 1 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k) :
    ∃! levels : Fin (m + 2) → ℝ,
      BinaryEndpointLevelVector levels ∧
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate ∧
          AppliedModelingLib.Optimization.IsStrictMaximizerOn
            (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
            (fun candidate : Fin (m + 2) → ℝ =>
              binaryEndpointAwareAdjacentRateObjective candidate sampleRate)
            levels := by
  have hsample_high :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i) :=
    binaryEndpointSampleRateNat_pos_adjacentHigh sampleRate hsample_pos
  have hsample_low :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i) :=
    binaryEndpointSampleRateNat_pos_adjacentLow sampleRate hsample_pos
  rcases
    lemma31_forward_clipped_equalized_rates_exist_unique
      hm sampleRate hsample_pos with
    ⟨levels, hlevels, huniq⟩
  refine ⟨levels, ?_, ?_⟩
  · rcases hlevels.2.exists_common_rate with ⟨r, hr⟩
    exact
      ⟨hlevels.1, hlevels.2,
        binaryEndpointAwareAdjacentRateObjective_isStrictMaximizerOn_of_equalized
          (show 0 < m by omega) sampleRate levels hlevels.1
          hsample_high hsample_low hr⟩
  · intro alt halt
    exact huniq alt ⟨halt.1, halt.2.1⟩

/--
Finite Lemma 3.1 forward-cascade lower sign: for any fixed finite endpoint
chain, the terminal scalar gap is eventually positive as the target rate tends
to zero from above.
-/
theorem lemma31_forward_clipped_terminal_gap_eventually_positive_near_zero
    {m : ℕ} (hm : 1 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k) :
    ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      0 < binaryEndpointForwardClippedTerminalGap sampleRate r :=
  binaryEndpointForwardClippedTerminalGap_eventually_pos_nhdsGT_zero
    hm sampleRate hsample_pos

/-- Finite Lemma 3.1 forward-cascade lower-sign witness. -/
theorem lemma31_forward_clipped_terminal_gap_positive_witness
    {m : ℕ} (hm : 1 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k) :
    ∃ r : ℝ, 0 < r ∧
      0 < binaryEndpointForwardClippedTerminalGap sampleRate r :=
  binaryEndpointForwardClippedTerminalGap_exists_pos
    hm sampleRate hsample_pos

/--
Finite Lemma 3.1 scalar IVT bridge: continuity of the terminal forward-cascade
gap on the shooting interval upgrades the lower and upper signs to a positive
equalizing target rate.
-/
theorem lemma31_forward_clipped_terminal_gap_zero_exists_from_continuity
    {m : ℕ} (hm : 1 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k)
    {crossing : ℝ}
    (hcrossing : 0 < crossing)
    (hcross :
      binaryEndpointInverseGap
        (binaryEndpointSampleRateNat sampleRate 1)
        (binaryEndpointSampleRateNat sampleRate m) crossing = 0)
    (hcont :
      ∀ left : ℝ, 0 < left → left < crossing →
        ContinuousOn (fun r : ℝ =>
          binaryEndpointForwardClippedTerminalGap sampleRate r)
          (Set.Icc left crossing)) :
    ∃ r : ℝ, 0 < r ∧ r < crossing ∧
      binaryEndpointForwardClippedTerminalGap sampleRate r = 0 :=
  binaryEndpointForwardClippedTerminalGap_exists_zero_of_continuousOn
    hm sampleRate hsample_pos hcrossing hcross hcont

/--
Finite Lemma 3.1 scalar shooting theorem: the forward-clipped terminal scalar
gap has a positive zero below the endpoint-inverse crossing.
-/
theorem lemma31_forward_clipped_terminal_gap_zero_exists
    {m : ℕ} (hm : 1 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k)
    {crossing : ℝ}
    (hcrossing : 0 < crossing)
    (hcross :
      binaryEndpointInverseGap
        (binaryEndpointSampleRateNat sampleRate 1)
        (binaryEndpointSampleRateNat sampleRate m) crossing = 0) :
    ∃ r : ℝ, 0 < r ∧ r < crossing ∧
      binaryEndpointForwardClippedTerminalGap sampleRate r = 0 :=
  binaryEndpointForwardClippedTerminalGap_exists_zero
    hm sampleRate hsample_pos hcrossing hcross

/--
Finite Lemma 3.1 forward-cascade upper sign: at the endpoint-inverse crossing,
the terminal scalar gap is negative.
-/
theorem lemma31_forward_clipped_terminal_gap_negative_at_endpoint_crossing
    {m : ℕ} (hm : 1 < m)
    (sampleRate : Fin (m + 2) → ℝ) {r : ℝ}
    (hr : 0 < r)
    (hcross :
      binaryEndpointInverseGap
        (binaryEndpointSampleRateNat sampleRate 1)
        (binaryEndpointSampleRateNat sampleRate m) r = 0)
    (hsample_m : 0 < binaryEndpointSampleRateNat sampleRate m)
    (hsample_m_prev : 0 < binaryEndpointSampleRateNat sampleRate (m - 1)) :
    binaryEndpointForwardClippedTerminalGap sampleRate r < 0 :=
  binaryEndpointForwardClippedTerminalGap_neg_at_inverseGap_crossing
    hm sampleRate hr hcross hsample_m hsample_m_prev

/--
At a positive zero of the forward-cascade terminal gap, the terminal adjacent
interval is genuinely ordered rather than clipped to the cap.
-/
theorem lemma31_forward_clipped_penultimate_level_lt_cap_of_terminal_gap_zero
    {m : ℕ} (hm : 1 < m)
    (sampleRate : Fin (m + 2) → ℝ) {r : ℝ}
    (hr : 0 < r)
    (hgap : binaryEndpointForwardClippedTerminalGap sampleRate r = 0)
    (hsample_m : 0 < binaryEndpointSampleRateNat sampleRate m)
    (hsample_m_prev : 0 < binaryEndpointSampleRateNat sampleRate (m - 1))
    (hcap :
      binaryEndpointForwardClippedCap sampleRate r ∈ Set.Ioo (0 : ℝ) 1)
    (hlevel_le :
      binaryEndpointForwardClippedLevelNat sampleRate
          (binaryEndpointForwardClippedCap sampleRate r) r (m - 1) ≤
        binaryEndpointForwardClippedCap sampleRate r) :
    binaryEndpointForwardClippedLevelNat sampleRate
        (binaryEndpointForwardClippedCap sampleRate r) r (m - 1) <
      binaryEndpointForwardClippedCap sampleRate r :=
  binaryEndpointForwardClippedPenultimate_lt_cap_of_terminal_gap_zero
    hm sampleRate hr hgap hsample_m hsample_m_prev hcap hlevel_le

/--
Interior next-level shooting for Lemma 3.1: fixing a low level and a target
rate below the rate at a right cap uniquely determines an interior high level.
-/
theorem lemma31_interior_next_level_exists_for_target_rate
    {gHi gLo pLo right target : ℝ}
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hpLo0 : 0 < pLo) (hpLo_lt_right : pLo < right)
    (hright1 : right < 1)
    (htarget_pos : 0 < target)
    (htarget_lt_right :
      target <
        weightedBernoulliClosedThresholdRate gHi gLo right pLo) :
    ∃ pHi : ℝ, pHi ∈ Set.Ioo pLo right ∧
      weightedBernoulliClosedThresholdRate gHi gLo pHi pLo = target ∧
      (∀ x ∈ Set.Icc pLo right,
        weightedBernoulliClosedThresholdRate gHi gLo x pLo < target ↔
          x < pHi) ∧
      (∀ x ∈ Set.Icc pLo right,
        target < weightedBernoulliClosedThresholdRate gHi gLo x pLo ↔
          pHi < x) ∧
      (∀ x ∈ Set.Icc pLo right,
        weightedBernoulliClosedThresholdRate gHi gLo x pLo ≤ target ↔
          x ≤ pHi) ∧
      (∀ x ∈ Set.Icc pLo right,
        target ≤ weightedBernoulliClosedThresholdRate gHi gLo x pLo ↔
          pHi ≤ x) :=
  exists_binaryEndpointInteriorHighLevelOfRate
    hgHi hgLo hpLo0 hpLo_lt_right hright1 htarget_pos htarget_lt_right

/-- The interior next level realizing the requested target rate is unique. -/
theorem lemma31_interior_next_level_unique_for_target_rate
    {gHi gLo pLo right target : ℝ}
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hpLo0 : 0 < pLo) (hpLo_lt_right : pLo < right)
    (hright1 : right < 1)
    (htarget_pos : 0 < target)
    (htarget_lt_right :
      target <
        weightedBernoulliClosedThresholdRate gHi gLo right pLo) :
    ∃! pHi : ℝ, pHi ∈ Set.Ioo pLo right ∧
      weightedBernoulliClosedThresholdRate gHi gLo pHi pLo = target :=
  existsUnique_binaryEndpointInteriorHighLevelOfRate
    hgHi hgLo hpLo0 hpLo_lt_right hright1 htarget_pos htarget_lt_right

/--
Interior previous-level shooting for Lemma 3.1: fixing a high level and a
target rate below the rate at a left cap uniquely determines an interior low
level.
-/
theorem lemma31_interior_previous_level_exists_for_target_rate
    {gHi gLo left pHi target : ℝ}
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hleft0 : 0 < left) (hleft_lt_hi : left < pHi)
    (hpHi1 : pHi < 1)
    (htarget_pos : 0 < target)
    (htarget_lt_left :
      target <
        weightedBernoulliClosedThresholdRate gHi gLo pHi left) :
    ∃ pLo : ℝ, pLo ∈ Set.Ioo left pHi ∧
      weightedBernoulliClosedThresholdRate gHi gLo pHi pLo = target ∧
      (∀ x ∈ Set.Icc left pHi,
        target < weightedBernoulliClosedThresholdRate gHi gLo pHi x ↔
          x < pLo) ∧
      (∀ x ∈ Set.Icc left pHi,
        weightedBernoulliClosedThresholdRate gHi gLo pHi x < target ↔
          pLo < x) ∧
      (∀ x ∈ Set.Icc left pHi,
        target ≤ weightedBernoulliClosedThresholdRate gHi gLo pHi x ↔
          x ≤ pLo) ∧
      (∀ x ∈ Set.Icc left pHi,
        weightedBernoulliClosedThresholdRate gHi gLo pHi x ≤ target ↔
          pLo ≤ x) :=
  exists_binaryEndpointInteriorLowLevelOfRate
    hgHi hgLo hleft0 hleft_lt_hi hpHi1 htarget_pos htarget_lt_left

/-- The interior previous level realizing the requested target rate is unique. -/
theorem lemma31_interior_previous_level_unique_for_target_rate
    {gHi gLo left pHi target : ℝ}
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hleft0 : 0 < left) (hleft_lt_hi : left < pHi)
    (hpHi1 : pHi < 1)
    (htarget_pos : 0 < target)
    (htarget_lt_left :
      target <
        weightedBernoulliClosedThresholdRate gHi gLo pHi left) :
    ∃! pLo : ℝ, pLo ∈ Set.Ioo left pHi ∧
      weightedBernoulliClosedThresholdRate gHi gLo pHi pLo = target :=
  existsUnique_binaryEndpointInteriorLowLevelOfRate
    hgHi hgLo hleft0 hleft_lt_hi hpHi1 htarget_pos htarget_lt_left

/-- Feasible endpoint-normalized adjacent rates are strictly positive. -/
theorem lemma31_endpoint_aware_adjacent_rate_positive
    {m : ℕ} (hm : 0 < m)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector successProb)
    (hsample_high :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hsample_low :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (i : Fin (m + 1)) :
    0 < binaryEndpointAwareAdjacentRate successProb sampleRate i :=
  binaryEndpointAwareAdjacentRate_pos
    hm successProb sampleRate hlevels hsample_high hsample_low i

/-- The common rate of a feasible equalized endpoint vector is strictly positive. -/
theorem lemma31_endpoint_aware_common_rate_positive
    {m : ℕ} (hm : 0 < m)
    (successProb sampleRate : Fin (m + 2) → ℝ) {r : ℝ}
    (hlevels : BinaryEndpointLevelVector successProb)
    (hsample_high :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hsample_low :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (heq :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate i = r) :
    0 < r := by
  have heq_pairwise : BinaryEndpointAwareAdjacentRatesEqualize successProb sampleRate := by
    intro i j
    rw [heq i, heq j]
  rcases
    heq_pairwise.exists_pos_common_rate
      hm hlevels hsample_high hsample_low with
    ⟨r', hr'_pos, hr'⟩
  have hrr' : r = r' := by
    rw [← heq (firstAdjacentIndex : Fin (m + 1)),
      hr' (firstAdjacentIndex : Fin (m + 1))]
  rwa [hrr']

/--
Endpoint-aware Lemma 3.1 equalization bridge: when the first/last endpoint
rates and all interior closed rates equalize, the finite worst-adjacent
objective has that common value.
-/
theorem lemma31_equalized_endpoint_aware_adjacent_rates_realize_objective {m : ℕ}
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (h : BinaryEndpointAwareAdjacentRatesEqualize successProb sampleRate)
    (i : Fin (m + 1)) :
    binaryEndpointAwareAdjacentRateObjective successProb sampleRate =
      binaryEndpointAwareAdjacentRate successProb sampleRate i :=
  binaryEndpointAwareAdjacentRateObjective_eq_rate_of_equalizes
    successProb sampleRate h i

/--
Endpoint-aware finite maximin certificate for Lemma 3.1: equalized adjacent
rates are optimal once every feasible alternative has at least one adjacent
rate no larger than the equalized rate.
-/
theorem lemma31_endpoint_aware_equalized_rates_are_maximin
    {m : ℕ}
    (sampleRate : Fin (m + 2) → ℝ)
    (feasible : (Fin (m + 2) → ℝ) → Prop)
    (candidate : Fin (m + 2) → ℝ) {r : ℝ}
    (heq :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate candidate sampleRate i = r)
    (hno_improve :
      ∀ alt : Fin (m + 2) → ℝ, feasible alt →
        ∃ i : Fin (m + 1),
          binaryEndpointAwareAdjacentRate alt sampleRate i ≤ r) :
    ∀ alt : Fin (m + 2) → ℝ, feasible alt →
      binaryEndpointAwareAdjacentRateObjective alt sampleRate ≤
        binaryEndpointAwareAdjacentRateObjective candidate sampleRate :=
  binaryEndpointAwareAdjacentRateObjective_maximal_of_equalized_and_no_simultaneous_improvement
    sampleRate feasible candidate heq hno_improve

/--
Standard optimization-certificate form of the endpoint-aware Lemma 3.1 maximin
bridge.
-/
theorem lemma31_endpoint_aware_equalized_rates_are_isMaximizerOn_of_positive_sample_rates
    {m : ℕ}
    (sampleRate : Fin (m + 2) → ℝ)
    (feasible : (Fin (m + 2) → ℝ) → Prop)
    (candidate : Fin (m + 2) → ℝ) {r : ℝ}
    (hcandidate : feasible candidate)
    (heq :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate candidate sampleRate i = r)
    (hno_improve :
      ∀ alt : Fin (m + 2) → ℝ, feasible alt →
        ∃ i : Fin (m + 1),
          binaryEndpointAwareAdjacentRate alt sampleRate i ≤ r) :
    AppliedModelingLib.Optimization.IsMaximizerOn feasible
      (fun levels : Fin (m + 2) → ℝ =>
        binaryEndpointAwareAdjacentRateObjective levels sampleRate)
      candidate :=
  binaryEndpointAwareAdjacentRateObjective_isMaximizerOn_of_equalized_and_no_simultaneous_improvement
    sampleRate feasible candidate hcandidate heq hno_improve

/--
Lemma 3.1 finite maximin bridge in the source's endpoint-to-endpoint cascade
form: equalized endpoint-aware adjacent rates are optimal once the first,
interior, and last adjacent-rate monotonicity steps rule out improving every
adjacent rate at once.
-/
theorem lemma31_endpoint_aware_equalized_rates_are_isMaximizerOn_from_cascade
    {m : ℕ} (hm : 0 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (feasible : (Fin (m + 2) → ℝ) → Prop)
    (candidate : Fin (m + 2) → ℝ) {r : ℝ}
    (hcandidate : feasible candidate)
    (heq :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate candidate sampleRate i = r)
    (hfirst :
      ∀ alt : Fin (m + 2) → ℝ, feasible alt →
        r < binaryEndpointAwareAdjacentRate alt sampleRate
            (firstAdjacentIndex : Fin (m + 1)) →
          candidate (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) <
            alt (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))))
    (hstep :
      ∀ alt : Fin (m + 2) → ℝ, feasible alt →
        ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
          candidate (adjacentLowIndex i) < alt (adjacentLowIndex i) →
          r < binaryEndpointAwareAdjacentRate alt sampleRate i →
          candidate (adjacentHighIndex i) < alt (adjacentHighIndex i))
    (hlast :
      ∀ alt : Fin (m + 2) → ℝ, feasible alt →
        candidate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) <
            alt (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) →
          binaryEndpointAwareAdjacentRate alt sampleRate
            (lastAdjacentIndex : Fin (m + 1)) ≤ r) :
    AppliedModelingLib.Optimization.IsMaximizerOn feasible
      (fun levels : Fin (m + 2) → ℝ =>
        binaryEndpointAwareAdjacentRateObjective levels sampleRate)
      candidate :=
  binaryEndpointAwareAdjacentRateObjective_isMaximizerOn_of_equalized_and_cascade
    hm sampleRate feasible candidate hcandidate heq hfirst hstep hlast

/--
Lemma 3.1 finite maximin bridge with the endpoint monotonicity steps proved:
for endpoint-normalized strictly increasing level vectors, equalized adjacent
rates are optimal once the interior closed-rate monotonicity step holds.
-/
theorem lemma31_endpoint_aware_equalized_rates_are_isMaximizerOn_from_interior_cascade
    {m : ℕ} (hm : 0 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (candidate : Fin (m + 2) → ℝ) {r : ℝ}
    (hcandidate : BinaryEndpointLevelVector candidate)
    (hsample_first :
      0 < sampleRate
        (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))))
    (hsample_last :
      0 < sampleRate
        (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))))
    (heq :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate candidate sampleRate i = r)
    (hstep :
      ∀ alt : Fin (m + 2) → ℝ, BinaryEndpointLevelVector alt →
        ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
          candidate (adjacentLowIndex i) < alt (adjacentLowIndex i) →
          r < binaryEndpointAwareAdjacentRate alt sampleRate i →
          candidate (adjacentHighIndex i) < alt (adjacentHighIndex i)) :
    AppliedModelingLib.Optimization.IsMaximizerOn
      (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
      (fun levels : Fin (m + 2) → ℝ =>
        binaryEndpointAwareAdjacentRateObjective levels sampleRate)
      candidate :=
  binaryEndpointAwareAdjacentRateObjective_isMaximizerOn_of_equalized_and_interior_cascade
    hm sampleRate candidate hcandidate hsample_first hsample_last heq hstep

/--
Lemma 3.1 finite maximin bridge from the standard interior monotonicity
inequality: raising an interior lower endpoint while keeping its upper endpoint
no higher cannot improve that adjacent interval's rate.
-/
theorem lemma31_endpoint_aware_equalized_rates_are_isMaximizerOn_from_interior_monotone
    {m : ℕ} (hm : 0 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (candidate : Fin (m + 2) → ℝ) {r : ℝ}
    (hcandidate : BinaryEndpointLevelVector candidate)
    (hsample_first :
      0 < sampleRate
        (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))))
    (hsample_last :
      0 < sampleRate
        (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))))
    (heq :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate candidate sampleRate i = r)
    (hinterior_mono :
      ∀ alt : Fin (m + 2) → ℝ, BinaryEndpointLevelVector alt →
        ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
          candidate (adjacentLowIndex i) < alt (adjacentLowIndex i) →
          alt (adjacentHighIndex i) ≤ candidate (adjacentHighIndex i) →
          binaryEndpointAwareAdjacentRate alt sampleRate i ≤ r) :
    AppliedModelingLib.Optimization.IsMaximizerOn
      (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
      (fun levels : Fin (m + 2) → ℝ =>
        binaryEndpointAwareAdjacentRateObjective levels sampleRate)
      candidate :=
  binaryEndpointAwareAdjacentRateObjective_isMaximizerOn_of_equalized_and_interior_monotone
    hm sampleRate candidate hcandidate hsample_first hsample_last heq
    hinterior_mono

/--
Lemma 3.1 finite maximin bridge from a closed-rate-base comparison: for every
interior interval, shrinking the interval must weakly increase the closed-rate
base, hence weakly decrease the closed large-deviation rate.
-/
theorem lemma31_endpoint_aware_equalized_rates_are_isMaximizerOn_from_interior_base_monotone
    {m : ℕ} (hm : 0 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (candidate : Fin (m + 2) → ℝ) {r : ℝ}
    (hcandidate : BinaryEndpointLevelVector candidate)
    (hsample_first :
      0 < sampleRate
        (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))))
    (hsample_last :
      0 < sampleRate
        (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))))
    (hsample_sum_nonneg :
      ∀ i : Fin (m + 1),
        0 ≤ sampleRate (adjacentHighIndex i) +
          sampleRate (adjacentLowIndex i))
    (heq :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate candidate sampleRate i = r)
    (hbase_mono :
      ∀ alt : Fin (m + 2) → ℝ, BinaryEndpointLevelVector alt →
        ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
          candidate (adjacentLowIndex i) < alt (adjacentLowIndex i) →
          alt (adjacentHighIndex i) ≤ candidate (adjacentHighIndex i) →
          weightedBernoulliClosedRateBase
              (sampleRate (adjacentHighIndex i))
              (sampleRate (adjacentLowIndex i))
              (candidate (adjacentHighIndex i))
              (candidate (adjacentLowIndex i)) ≤
            weightedBernoulliClosedRateBase
              (sampleRate (adjacentHighIndex i))
              (sampleRate (adjacentLowIndex i))
              (alt (adjacentHighIndex i))
              (alt (adjacentLowIndex i))) :
    AppliedModelingLib.Optimization.IsMaximizerOn
      (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
      (fun levels : Fin (m + 2) → ℝ =>
        binaryEndpointAwareAdjacentRateObjective levels sampleRate)
      candidate :=
  binaryEndpointAwareAdjacentRateObjective_isMaximizerOn_of_equalized_and_interior_base_monotone
    hm sampleRate candidate hcandidate hsample_first hsample_last
    hsample_sum_nonneg heq hbase_mono

/--
Finite Lemma 3.1 maximin theorem: under the paper's endpoint convention and
positive adjacent sample rates, an endpoint-normalized level vector that
equalizes all adjacent rates maximizes the finite worst-adjacent rate.
-/
theorem lemma31_endpoint_aware_equalized_rates_are_isMaximizerOn
    {m : ℕ} (hm : 0 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (candidate : Fin (m + 2) → ℝ) {r : ℝ}
    (hcandidate : BinaryEndpointLevelVector candidate)
    (hsample_high :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hsample_low :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (heq :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate candidate sampleRate i = r) :
    AppliedModelingLib.Optimization.IsMaximizerOn
      (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
      (fun levels : Fin (m + 2) → ℝ =>
        binaryEndpointAwareAdjacentRateObjective levels sampleRate)
      candidate :=
  binaryEndpointAwareAdjacentRateObjective_isMaximizerOn_of_equalized
    hm sampleRate candidate hcandidate hsample_high hsample_low heq

/--
Source-shaped finite Lemma 3.1 maximin theorem: pairwise equalization of the
endpoint-aware adjacent rates is enough to maximize the finite worst-adjacent
rate.
-/
theorem lemma31_endpoint_aware_pairwise_equalized_rates_are_isMaximizerOn
    {m : ℕ} (hm : 0 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (candidate : Fin (m + 2) → ℝ)
    (hcandidate : BinaryEndpointLevelVector candidate)
    (hsample_high :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hsample_low :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (heq : BinaryEndpointAwareAdjacentRatesEqualize candidate sampleRate) :
    AppliedModelingLib.Optimization.IsMaximizerOn
      (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
      (fun levels : Fin (m + 2) → ℝ =>
        binaryEndpointAwareAdjacentRateObjective levels sampleRate)
      candidate :=
  binaryEndpointAwareAdjacentRateObjective_isMaximizerOn_of_pairwise_equalized
    hm sampleRate candidate hcandidate hsample_high hsample_low heq

/--
Theorem 3.1 finite rate-optimality bridge: a pairwise-equalized
endpoint-normalized level vector has worst-adjacent rate at least that of any
endpoint-normalized alternative.
-/
theorem paper_theorem31_rate_optimal_of_pairwise_equalized
    {m : ℕ} (hm : 0 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (candidate alt : Fin (m + 2) → ℝ)
    (hcandidate : BinaryEndpointLevelVector candidate)
    (halt : BinaryEndpointLevelVector alt)
    (hsample_high :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hsample_low :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (heq : BinaryEndpointAwareAdjacentRatesEqualize candidate sampleRate) :
    binaryEndpointAwareAdjacentRateObjective alt sampleRate ≤
      binaryEndpointAwareAdjacentRateObjective candidate sampleRate :=
  GJ19OptimalBinaryRatingSystems.theorem31_rate_optimal_of_pairwise_equalized
    hm sampleRate candidate alt hcandidate halt hsample_high hsample_low heq

/--
Finite Lemma 3.1 uniqueness component: under the endpoint convention and
positive adjacent sample rates, an endpoint-normalized level vector that
pairwise equalizes all adjacent rates is unique.
-/
theorem lemma31_endpoint_aware_pairwise_equalized_rates_unique
    {m : ℕ} (hm : 0 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (candidate alt : Fin (m + 2) → ℝ)
    (hcandidate : BinaryEndpointLevelVector candidate)
    (halt : BinaryEndpointLevelVector alt)
    (hsample_high :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hsample_low :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (heq_candidate :
      BinaryEndpointAwareAdjacentRatesEqualize candidate sampleRate)
    (heq_alt :
      BinaryEndpointAwareAdjacentRatesEqualize alt sampleRate) :
    candidate = alt :=
  binaryEndpointAwareAdjacentRatesEqualize_unique
    hm sampleRate candidate alt hcandidate halt
    hsample_high hsample_low heq_candidate heq_alt

/--
Finite Lemma 3.1 uniform-optimal uniqueness: every endpoint-normalized
maximizer of the uniform finite adjacent-rate objective is the canonical
uniform equalized endpoint vector.
-/
abbrev paper_canonical_uniform_equalized_endpoint_levels_eq_of_isMaximizerOn :=
  @GJ19OptimalBinaryRatingSystems.canonicalUniformEqualizedEndpointLevels_eq_of_isMaximizerOn

/--
Finite Lemma 3.1 packaged uniqueness: if the endpoint-aware equalized system
has a feasible solution, that solution is unique.
-/
theorem lemma31_endpoint_aware_pairwise_equalized_rates_existsUnique_of_exists
    {m : ℕ} (hm : 0 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_high :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hsample_low :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (hexists :
      ∃ candidate : Fin (m + 2) → ℝ,
        BinaryEndpointLevelVector candidate ∧
          BinaryEndpointAwareAdjacentRatesEqualize candidate sampleRate) :
    ∃! candidate : Fin (m + 2) → ℝ,
      BinaryEndpointLevelVector candidate ∧
        BinaryEndpointAwareAdjacentRatesEqualize candidate sampleRate :=
  binaryEndpointAwareAdjacentRatesEqualize_existsUnique_of_exists
    hm sampleRate hsample_high hsample_low hexists

/--
Finite Lemma 3.1 strict maximin theorem: under the endpoint convention and
positive adjacent sample rates, an endpoint-normalized level vector that
equalizes all adjacent rates is the unique maximizer of the finite
worst-adjacent rate.
-/
theorem lemma31_endpoint_aware_equalized_rates_are_strictMaximizerOn
    {m : ℕ} (hm : 0 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (candidate : Fin (m + 2) → ℝ) {r : ℝ}
    (hcandidate : BinaryEndpointLevelVector candidate)
    (hsample_high :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hsample_low :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (heq :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate candidate sampleRate i = r) :
    AppliedModelingLib.Optimization.IsStrictMaximizerOn
      (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
      (fun levels : Fin (m + 2) → ℝ =>
        binaryEndpointAwareAdjacentRateObjective levels sampleRate)
      candidate :=
  binaryEndpointAwareAdjacentRateObjective_isStrictMaximizerOn_of_equalized
    hm sampleRate candidate hcandidate hsample_high hsample_low heq

/--
Source-shaped finite Lemma 3.1 strict maximin theorem: pairwise equalization
of all endpoint-aware adjacent rates makes the level vector the unique
maximizer of the finite worst-adjacent rate.
-/
theorem lemma31_endpoint_aware_pairwise_equalized_rates_are_strictMaximizerOn
    {m : ℕ} (hm : 0 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (candidate : Fin (m + 2) → ℝ)
    (hcandidate : BinaryEndpointLevelVector candidate)
    (hsample_high :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hsample_low :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (heq : BinaryEndpointAwareAdjacentRatesEqualize candidate sampleRate) :
    AppliedModelingLib.Optimization.IsStrictMaximizerOn
      (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
      (fun levels : Fin (m + 2) → ℝ =>
        binaryEndpointAwareAdjacentRateObjective levels sampleRate)
      candidate := by
  rcases heq.exists_common_rate with ⟨r, hr⟩
  exact
    binaryEndpointAwareAdjacentRateObjective_isStrictMaximizerOn_of_equalized
      hm sampleRate candidate hcandidate hsample_high hsample_low hr

/--
Finite Lemma 3.1 equalization equivalence: once an equalized endpoint vector
exists, a feasible endpoint-normalized vector maximizes the finite
worst-adjacent rate iff it pairwise equalizes all adjacent rates.

Source status: finite endpoint-normalized form of Lemma 3.1's equalization
criterion.
-/
theorem lemma31_endpoint_aware_maximizer_iff_pairwise_equalized
    {m : ℕ} (hm : 0 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (candidate alt : Fin (m + 2) → ℝ)
    (hcandidate : BinaryEndpointLevelVector candidate)
    (halt : BinaryEndpointLevelVector alt)
    (hsample_high :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hsample_low :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (heq_candidate :
      BinaryEndpointAwareAdjacentRatesEqualize candidate sampleRate) :
    AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun levels : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective levels sampleRate)
        alt ↔
      BinaryEndpointAwareAdjacentRatesEqualize alt sampleRate :=
  binaryEndpointAwareAdjacentRateObjective_isMaximizerOn_iff_pairwise_equalized
    hm sampleRate candidate alt hcandidate halt
    hsample_high hsample_low heq_candidate


/--
The source binary-rating model has Bernoulli MGF `(1-t)+t exp z`.

Source status: direct paper-facing binary-rating MGF formula row.
-/
theorem binary_rating_model_mgf_formula {Seller : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (θ : Seller) (z : ℝ) :
    (binaryRatingModel successProb hprob0 hprob1).mgf θ z =
      (1 - successProb θ) + successProb θ * Real.exp z :=
  binaryRatingModel_mgf_eq successProb hprob0 hprob1 θ z


/--
The source binary-rating model has Bernoulli log-MGF formula.

Source status: direct paper-facing binary-rating log-MGF formula row.
-/
theorem binary_rating_model_log_mgf_formula {Seller : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (θ : Seller) (z : ℝ) :
    (binaryRatingModel successProb hprob0 hprob1).logMGF θ z =
      Real.log ((1 - successProb θ) + successProb θ * Real.exp z) :=
  binaryRatingModel_logMGF_eq successProb hprob0 hprob1 θ z


/--
Derivative of the source binary-rating log-MGF.

Source status: direct paper-facing log-MGF derivative formula row.
-/
theorem binary_rating_model_log_mgf_derivative_formula {Seller : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (θ : Seller) (z : ℝ) :
    HasDerivAt
      (fun t : ℝ =>
        (binaryRatingModel successProb hprob0 hprob1).logMGF θ t)
      (successProb θ * Real.exp z /
        ((1 - successProb θ) + successProb θ * Real.exp z)) z :=
  binaryRatingModel_logMGF_hasDerivAt successProb hprob0 hprob1 θ z

/--
Interior binary-model rate function equals the Bernoulli KL formula used in
the paper.

Source status: direct paper-facing Bernoulli-KL rate-function formula row.
-/
theorem binary_rating_model_rate_function_is_bernoulli_kl
    {Seller : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_pos : ∀ θ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ, successProb θ < 1)
    (θ : Seller) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    (binaryRatingModel successProb hprob0 hprob1).rateFunction θ a =
      paperBernoulliKL a (successProb θ) :=
  binaryRatingModel_rateFunction_eq_sourceBernoulliKL
    successProb hprob0 hprob1 hprob_pos hprob_lt_one θ ha0 ha1

/--
Interior support-safe binary-model rate function equals the Bernoulli KL
formula used in the paper.

Source status: direct paper-facing support-safe Bernoulli-KL rate-function formula row.
-/
theorem binary_rating_model_rate_function_top_is_bernoulli_kl
    {Seller : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_pos : ∀ θ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ, successProb θ < 1)
    (θ : Seller) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    (binaryRatingModel successProb hprob0 hprob1).rateFunctionTop θ a =
      (paperBernoulliKL a (successProb θ) : WithTop ℝ) :=
  binaryRatingModel_rateFunctionTop_eq_sourceBernoulliKL
    successProb hprob0 hprob1 hprob_pos hprob_lt_one θ ha0 ha1

/--
Interior pairwise support-safe binary rate objective equals the weighted
two-Bernoulli KL threshold rate.

Source status: direct paper-facing pairwise threshold-rate objective formula row.
-/
theorem binary_rating_pairwise_rate_objective_top_is_threshold_kl_rate
    {Seller : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_pos : ∀ θ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ, successProb θ < 1)
    (sampleRate : Seller → ℝ) (hi lo : Seller)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    (binaryRatingModel successProb hprob0 hprob1).pairwiseRateObjectiveTop
        sampleRate hi lo a =
      (twoBernoulliThresholdRate (sampleRate hi) (sampleRate lo)
        (successProb hi) (successProb lo) a : WithTop ℝ) :=
  binaryRatingModel_pairwiseRateObjectiveTop_eq_source_threshold_rate
    successProb hprob0 hprob1 hprob_pos hprob_lt_one
    sampleRate hi lo ha0 ha1

/--
For two interior binary-rating levels, the support-safe threshold rate equals
the closed weighted Bernoulli rate used in the adjacent-rate analysis.

Source status: direct paper-facing closed weighted threshold-rate formula row.
-/
theorem binary_rating_pairwise_threshold_rate_top_is_closed_weighted_rate
    {Seller : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_pos : ∀ θ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ, successProb θ < 1)
    (sampleRate : Seller → ℝ) (hi lo : Seller)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo)
    (hG : sampleRate hi + sampleRate lo ≠ 0) :
    pairwiseSellerThresholdRateTop
        (binaryRatingModel successProb hprob0 hprob1)
        sampleRate hi lo =
      (weightedBernoulliClosedThresholdRate
        (sampleRate hi) (sampleRate lo)
        (successProb hi) (successProb lo) : WithTop ℝ) :=
  binaryRatingModel_pairwiseThresholdRateTop_eq_closed_weighted_rate
    successProb hprob0 hprob1 hprob_pos hprob_lt_one
    sampleRate hi lo hgHi hgLo hG

/--
Interior binary probabilities give full support, the finite-support
nondegeneracy condition used by the pairwise LDP constructors.
-/
theorem binary_rating_model_full_support_of_interior_probabilities
    {Seller : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_pos : ∀ θ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ, successProb θ < 1) :
    (binaryRatingModel successProb hprob0 hprob1).fullSupport :=
  binaryRatingModel_fullSupport_of_probabilities_interior
    successProb hprob0 hprob1 hprob_pos hprob_lt_one

/--
Pairwise floor-count LDP certificate package for binary rating models, derived
from common log-MGF derivative witnesses.

Source status: direct paper-facing pairwise threshold-rate certificate row.
-/
def binary_rating_pairwise_threshold_rate_certificates_from_derivatives
    {Seller Pair : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_pos : ∀ θ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ, successProb θ < 1)
    (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
    (hpositive_hi : ∀ p : Pair, 0 < sampleRate (pairHi p))
    (hpositive_lo : ∀ p : Pair, 0 < sampleRate (pairLo p))
    (a z : Pair → ℝ)
    (hz : ∀ p : Pair, z p ≤ 0)
    (hderiv_hi :
      ∀ p : Pair,
        HasDerivAt
          (fun t : ℝ =>
            (binaryRatingModel successProb hprob0 hprob1).logMGF
              (pairHi p) t)
          (a p) (z p * (sampleRate (pairHi p))⁻¹))
    (hderiv_lo :
      ∀ p : Pair,
        HasDerivAt
          (fun t : ℝ =>
            (binaryRatingModel successProb hprob0 hprob1).logMGF
              (pairLo p) t)
          (a p) (-(z p * (sampleRate (pairLo p))⁻¹))) :
    PairwiseThresholdRateTopLdpCertificate
      (binaryRatingModel successProb hprob0 hprob1)
      sampleRate pairHi pairLo :=
  binaryRatingModel_pairwiseThresholdRateTopLdpCertificate_of_common_logMGF_derivatives
    successProb hprob0 hprob1 hprob_pos hprob_lt_one
    sampleRate pairHi pairLo hpositive_hi hpositive_lo
    a z hz hderiv_hi hderiv_lo

/--
Pairwise floor-count LDP certificate package for binary rating models, derived
from the explicit Bernoulli derivative equations for a common threshold.
-/
def binary_rating_pairwise_threshold_rate_certificates_from_derivative_formula
    {Seller Pair : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_pos : ∀ θ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ, successProb θ < 1)
    (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
    (hpositive_hi : ∀ p : Pair, 0 < sampleRate (pairHi p))
    (hpositive_lo : ∀ p : Pair, 0 < sampleRate (pairLo p))
    (a z : Pair → ℝ)
    (hz : ∀ p : Pair, z p ≤ 0)
    (hcommon_hi :
      ∀ p : Pair,
        a p =
          successProb (pairHi p) *
              Real.exp (z p * (sampleRate (pairHi p))⁻¹) /
            ((1 - successProb (pairHi p)) +
              successProb (pairHi p) *
                Real.exp (z p * (sampleRate (pairHi p))⁻¹)))
    (hcommon_lo :
      ∀ p : Pair,
        a p =
          successProb (pairLo p) *
              Real.exp (-(z p * (sampleRate (pairLo p))⁻¹)) /
            ((1 - successProb (pairLo p)) +
              successProb (pairLo p) *
                Real.exp (-(z p * (sampleRate (pairLo p))⁻¹)))) :
    PairwiseThresholdRateTopLdpCertificate
      (binaryRatingModel successProb hprob0 hprob1)
      sampleRate pairHi pairLo :=
  binaryRatingModel_pairwiseThresholdRateTopLdpCertificate_of_derivative_formula
    successProb hprob0 hprob1 hprob_pos hprob_lt_one
    sampleRate pairHi pairLo hpositive_hi hpositive_lo
    a z hz hcommon_hi hcommon_lo

/--
Pairwise floor-count LDP certificate package for binary rating models, derived
from a common interior threshold and weighted common-dual equation.
-/
def binary_rating_pairwise_threshold_rate_certificates_from_common_threshold
    {Seller Pair : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_pos : ∀ θ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ, successProb θ < 1)
    (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
    (hpositive_hi : ∀ p : Pair, 0 < sampleRate (pairHi p))
    (hpositive_lo : ∀ p : Pair, 0 < sampleRate (pairLo p))
    (a : Pair → ℝ)
    (ha0 : ∀ p : Pair, 0 < a p)
    (ha1 : ∀ p : Pair, a p < 1)
    (hdual_nonpos :
      ∀ p : Pair,
        sampleRate (pairHi p) *
          binaryLogMGFDerivativeArg (successProb (pairHi p)) (a p) ≤ 0)
    (hdual_eq :
      ∀ p : Pair,
        sampleRate (pairHi p) *
            binaryLogMGFDerivativeArg (successProb (pairHi p)) (a p) =
          -(sampleRate (pairLo p) *
            binaryLogMGFDerivativeArg (successProb (pairLo p)) (a p))) :
    PairwiseThresholdRateTopLdpCertificate
      (binaryRatingModel successProb hprob0 hprob1)
      sampleRate pairHi pairLo :=
  binaryRatingModel_pairwiseThresholdRateTopLdpCertificate_of_common_threshold_inverse
    successProb hprob0 hprob1 hprob_pos hprob_lt_one
    sampleRate pairHi pairLo hpositive_hi hpositive_lo
    a ha0 ha1 hdual_nonpos hdual_eq

/--
Pairwise floor-count LDP certificate package for binary rating models, derived
from a common interior threshold, the weighted common-dual equation, and the
source-shaped order condition that the threshold is no larger than the high
type's success probability.
-/
def binary_rating_pairwise_threshold_rate_certificates_from_ordered_common_threshold
    {Seller Pair : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_pos : ∀ θ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ, successProb θ < 1)
    (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
    (hpositive_hi : ∀ p : Pair, 0 < sampleRate (pairHi p))
    (hpositive_lo : ∀ p : Pair, 0 < sampleRate (pairLo p))
    (a : Pair → ℝ)
    (ha0 : ∀ p : Pair, 0 < a p)
    (ha1 : ∀ p : Pair, a p < 1)
    (ha_le_hi : ∀ p : Pair, a p ≤ successProb (pairHi p))
    (hdual_eq :
      ∀ p : Pair,
        sampleRate (pairHi p) *
            binaryLogMGFDerivativeArg (successProb (pairHi p)) (a p) =
          -(sampleRate (pairLo p) *
            binaryLogMGFDerivativeArg (successProb (pairLo p)) (a p))) :
    PairwiseThresholdRateTopLdpCertificate
      (binaryRatingModel successProb hprob0 hprob1)
      sampleRate pairHi pairLo :=
  binaryRatingModel_pairwiseThresholdRateTopLdpCertificate_of_ordered_common_threshold_inverse
    successProb hprob0 hprob1 hprob_pos hprob_lt_one
    sampleRate pairHi pairLo hpositive_hi hpositive_lo
    a ha0 ha1 ha_le_hi hdual_eq

/--
Pairwise floor-count LDP certificate package for binary rating models, derived
from the weighted geometric common threshold used by the adjacent-rate proof.
-/
def binary_rating_pairwise_threshold_rate_certificates_from_weighted_common_threshold
    {Seller Pair : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_pos : ∀ θ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ, successProb θ < 1)
    (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
    (hpositive_hi : ∀ p : Pair, 0 < sampleRate (pairHi p))
    (hpositive_lo : ∀ p : Pair, 0 < sampleRate (pairLo p))
    (hG :
      ∀ p : Pair,
        sampleRate (pairHi p) + sampleRate (pairLo p) ≠ 0)
    (ha_le_hi :
      ∀ p : Pair,
        weightedBernoulliCommonThreshold
            (sampleRate (pairHi p)) (sampleRate (pairLo p))
            (successProb (pairHi p)) (successProb (pairLo p)) ≤
          successProb (pairHi p)) :
    PairwiseThresholdRateTopLdpCertificate
      (binaryRatingModel successProb hprob0 hprob1)
      sampleRate pairHi pairLo :=
  binaryRatingModel_pairwiseThresholdRateTopLdpCertificate_of_weighted_common_threshold
    successProb hprob0 hprob1 hprob_pos hprob_lt_one
    sampleRate pairHi pairLo hpositive_hi hpositive_lo hG ha_le_hi

/--
Endpoint adjacent-pair LDP bridge for a zero-success low type. This is the
first-boundary case used by Lemma 3.1 when the level chain starts at `0`.
-/
theorem binary_rating_floor_score_gap_left_tail_endpoint_low_zero_rate
    {Seller : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (sampleRate : Seller → ℝ) (hi lo : Seller)
    (hgHi : 0 < sampleRate hi)
    (hpHi0 : 0 < successProb hi)
    (hpHi1 : successProb hi < 1)
    (hpLo_zero : successProb lo = 0) :
    ExponentialRateCertificate
      (twoSampleFloorScoreGapLeftTailProb
        (binaryRatingModel successProb hprob0 hprob1) sampleRate hi lo)
      (sampleRate hi * (-Real.log (1 - successProb hi))) :=
  binaryRatingModel_floorScoreGapLeftTail_exponentialRateCertificate_of_low_success_zero
    successProb hprob0 hprob1 sampleRate hi lo hgHi hpHi0 hpHi1 hpLo_zero

/--
Endpoint adjacent-pair LDP bridge for a one-success high type. This is the
last-boundary case used by Lemma 3.1 when the level chain ends at `1`.
-/
theorem binary_rating_floor_score_gap_left_tail_endpoint_high_one_rate
    {Seller : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (sampleRate : Seller → ℝ) (hi lo : Seller)
    (hgHi : 0 < sampleRate hi)
    (hgLo : 0 < sampleRate lo)
    (hpHi_one : successProb hi = 1)
    (hpLo0 : 0 < successProb lo)
    (hpLo1 : successProb lo < 1) :
    ExponentialRateCertificate
      (twoSampleFloorScoreGapLeftTailProb
        (binaryRatingModel successProb hprob0 hprob1) sampleRate hi lo)
      (sampleRate lo * (-Real.log (successProb lo))) :=
  binaryRatingModel_floorScoreGapLeftTail_exponentialRateCertificate_of_high_success_one
    successProb hprob0 hprob1 sampleRate hi lo hgHi hgLo
    hpHi_one hpLo0 hpLo1

/--
Interior adjacent-pair LDP bridge at the closed weighted Bernoulli rate. This
is the middle-pair companion to the two endpoint bridges above.
-/
theorem binary_rating_floor_score_gap_left_tail_weighted_common_threshold_rate
    {Seller : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (sampleRate : Seller → ℝ) (hi lo : Seller)
    (hgHi : 0 < sampleRate hi)
    (hgLo : 0 < sampleRate lo)
    (hpHi0 : 0 < successProb hi)
    (hpHi1 : successProb hi < 1)
    (hpLo0 : 0 < successProb lo)
    (hpLo1 : successProb lo < 1)
    (hpLo_le_hi : successProb lo ≤ successProb hi) :
    ExponentialRateCertificate
      (twoSampleFloorScoreGapLeftTailProb
        (binaryRatingModel successProb hprob0 hprob1) sampleRate hi lo)
      (weightedBernoulliClosedThresholdRate
        (sampleRate hi) (sampleRate lo)
        (successProb hi) (successProb lo)) :=
  binaryRatingModel_floorScoreGapLeftTail_exponentialRateCertificate_of_weighted_common_threshold_pair
    successProb hprob0 hprob1 sampleRate hi lo hgHi hgLo
    hpHi0 hpHi1 hpLo0 hpLo1 hpLo_le_hi

/--
Finite objective aggregation bridge used by the discrete part of the binary
rating-system analysis.
-/
theorem finite_binary_ranking_error_upper_bound_from_rate_certificates
    {ι : Type*} [Fintype ι]
    (C : FiniteErrorRateCertificate ι)
    {weight : ι → ℝ} {targetRate : ℝ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hrate : ∀ i, targetRate < C.rate i) :
    HasExpUpperBoundWithConst (C.aggregateError weight) targetRate :=
  finiteBinaryRankingError_hasExpUpperBound_of_rate_certificates
    C hweight hrate

/--
Theorem 3.1 Part 1 asymptotic-value bridge: bounded convergence sends the
weighted success integral to the limiting weighted value when pairwise success
probabilities converge to one.

Source status: theorem component proved under explicit measurability,
boundedness, and pointwise-success convergence hypotheses.
-/
theorem paper_theorem31_asymptotic_value_integral_tendsto_of_success_prob_tendsto_one
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [MeasureTheory.IsFiniteMeasure μ]
    (w : Ω → ℝ) (P : ℕ → Ω → ℝ) {B : ℝ}
    (hprod_meas :
      ∀ k, MeasureTheory.AEStronglyMeasurable (fun x => w x * P k x) μ)
    (hprod_bound :
      ∀ k, ∀ᵐ x ∂μ, 0 ≤ w x * P k x ∧ w x * P k x ≤ B)
    (hP_lim : ∀ᵐ x ∂μ, Tendsto (fun k => P k x) Filter.atTop (𝓝 1)) :
    Tendsto (fun k => ∫ x, w x * P k x ∂μ)
      Filter.atTop (𝓝 (∫ x, w x ∂μ)) :=
  GJ19OptimalBinaryRatingSystems.theorem31_asymptotic_value_integral_tendsto_of_success_prob_tendsto_one
    μ w P hprod_meas hprod_bound hP_lim

/--
Theorem 3.1 Part 1 bridge specialized to the binary floor-count paper
objective `P_k`: product measurability and domination are derived internally
from measurable model primitives, bounded weights, and `|P_k| <= 1`.
-/
abbrev paper_theorem31_asymptotic_value_integral_tendsto_of_floorPkObjectiveProb_tendsto_one :=
  @GJ19OptimalBinaryRatingSystems.theorem31_asymptotic_value_integral_tendsto_of_floorPkObjectiveProb_tendsto_one

/--
Theorem 3.1 Part 1 bridge specialized to the binary floor-count paper
objective from positive exponential decay of the complement error.
-/
abbrev paper_theorem31_asymptotic_value_integral_tendsto_of_floorPkObjectiveProb_positive_rate :=
  @GJ19OptimalBinaryRatingSystems.theorem31_asymptotic_value_integral_tendsto_of_floorPkObjectiveProb_positive_rate

/--
Theorem 3.1 Part 1 bridge from a compact-uniform positive-rate certificate on
an almost-sure support set to asymptotic convergence of the binary floor-count
paper objective.
-/
abbrev paper_theorem31_asymptotic_value_integral_tendsto_of_floorPkObjectiveProb_uniform_positive_rate_on :=
  @GJ19OptimalBinaryRatingSystems.theorem31_asymptotic_value_integral_tendsto_of_floorPkObjectiveProb_uniform_positive_rate_on

/--
Theorem 3.1 Part 1 bridge specialized to ordered interior binary pairs:
positive sample rates and strictly ordered interior success probabilities give
the positive exponential-rate certificates needed for asymptotic value.
-/
abbrev paper_theorem31_asymptotic_value_integral_tendsto_of_floorPkObjectiveProb_ordered_interior :=
  @GJ19OptimalBinaryRatingSystems.theorem31_asymptotic_value_integral_tendsto_of_floorPkObjectiveProb_ordered_interior

/--
Theorem 3.1 two-stage optimality logic: maximizing the limiting value and then
maximizing the large-deviation rate on that limiting-value fiber gives
lexicographic optimality for the paper's asymptotic-value/rate criterion.

Source status: exact optimization-ordering logic for the Theorem 3.1
value-then-rate criterion.
-/
theorem paper_theorem31_two_stage_lexicographic_optimality
    {Design : Type*} (feasible : Design → Prop)
    (limitingValue rate : Design → ℝ) (candidate : Design)
    (hvalue :
      AppliedModelingLib.Optimization.IsMaximizerOn feasible limitingValue candidate)
    (hrate :
      ∀ alternative, feasible alternative →
        limitingValue alternative = limitingValue candidate →
          rate alternative ≤ rate candidate) :
    AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
      feasible limitingValue rate candidate :=
  GJ19OptimalBinaryRatingSystems.theorem31_two_stage_lexicographic_optimality
    feasible limitingValue rate candidate hvalue hrate

/--
Theorem 3.1 two-stage source form: maximizing the limiting-value objective,
then maximizing the large-deviation rate on the tied limiting-value fiber,
gives lexicographic optimality for the paper's criterion.
-/
theorem paper_theorem31_two_stage_lexicographic_optimality_of_rate_maximizer_on_value_fiber
    {Design : Type*} (feasible : Design → Prop)
    (limitingValue rate : Design → ℝ) (candidate : Design)
    (hvalue :
      AppliedModelingLib.Optimization.IsMaximizerOn feasible limitingValue candidate)
    (hrate :
      AppliedModelingLib.Optimization.IsMaximizerOn
        (fun alternative =>
          feasible alternative ∧
            limitingValue alternative = limitingValue candidate)
        rate candidate) :
    AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
      feasible limitingValue rate candidate :=
  GJ19OptimalBinaryRatingSystems.theorem31_two_stage_lexicographic_optimality_of_rate_maximizer_on_value_fiber
    feasible limitingValue rate candidate hvalue hrate

/--
Theorem 3.1 two-stage partition/endpoint source form: a value-maximizing
partition `S*` and endpoint levels that dominate the rate on the whole
value-maximizing fiber give a lexicographically optimal `(S*, t*)` design.

Source status: exact source-shaped composition for Theorem 3.1's
partition-first, endpoint-rate-second criterion; the value-tie rate premise is
the explicit condition needed when several partitions maximize the value term.
-/
theorem paper_theorem31_partition_endpoint_two_stage_lexicographic_optimality
    {Partition Endpoint : Type*}
    (partitionFeasible : Partition → Prop)
    (endpointFeasible : Partition → Endpoint → Prop)
    (limitingValue : Partition → ℝ)
    (rate : Partition → Endpoint → ℝ)
    (Sstar : Partition) (tstar : Endpoint)
    (hvalue :
      AppliedModelingLib.Optimization.IsMaximizerOn partitionFeasible limitingValue
        Sstar)
    (htstar : endpointFeasible Sstar tstar)
    (hrate :
      ∀ S t, partitionFeasible S → endpointFeasible S t →
        limitingValue S = limitingValue Sstar →
          rate S t ≤ rate Sstar tstar) :
    AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
      (fun design : Partition × Endpoint =>
        partitionFeasible design.1 ∧ endpointFeasible design.1 design.2)
      (fun design : Partition × Endpoint => limitingValue design.1)
      (fun design : Partition × Endpoint => rate design.1 design.2)
      (Sstar, tstar) :=
  GJ19OptimalBinaryRatingSystems.theorem31_partition_endpoint_two_stage_lexicographic_optimality
    partitionFeasible endpointFeasible limitingValue rate Sstar tstar hvalue
    htstar hrate

/--
Theorem 3.1 compact-domain two-stage source form: compactness and continuity
of the partition-value problem produce an `S*`; a secondary endpoint optimizer
on the value-tie fiber then gives a lexicographically optimal `(S*, t*)`.

Source status: compact-continuous `S*` existence bridge.  The remaining
continuum work is proving the paper's concrete cutpoint feasible set is
compact and its weighted partition objective is continuous under the source
regularity assumptions.
-/
abbrev paper_theorem31_exists_partition_endpoint_two_stage_lexicographic_optimality_of_isCompact_continuousOn :=
  @GJ19OptimalBinaryRatingSystems.theorem31_exists_partition_endpoint_two_stage_lexicographic_optimality_of_isCompact_continuousOn

/--
Theorem 3.1 finite-gap `S*` bridge: a continuous limiting-value objective on
the finite simplex of interval gaps attains a maximizing gap partition; a
secondary endpoint optimizer on the value-tie fiber gives the lexicographic
gap/endpoint design.

Source status: finite-dimensional compact-simplex `S*` existence bridge.  The
remaining continuum work is connecting the paper's weighted cutpoint objective
to this continuous finite-gap objective under the source regularity
assumptions.
-/
abbrev paper_theorem31_exists_gap_partition_endpoint_two_stage_lexicographic_optimality_of_continuousOn_finiteProbabilitySimplex :=
  @GJ19OptimalBinaryRatingSystems.theorem31_exists_gap_partition_endpoint_two_stage_lexicographic_optimality_of_continuousOn_finiteProbabilitySimplex

/--
Theorem 3.1 finite-gap cutpoint-image bridge: the compact finite-simplex
optimizer can be read as an optimizer over interval cutpoints induced by
finite gap vectors.

Source status: finite-dimensional cutpoint-image `S*` bridge.  Concrete
finite-vector and finite ordered-pair objective instantiations are formalized
in `AppendixB`; the remaining continuum work is identifying the paper's
general weighted source objective with that finite cutpoint layer.
-/
abbrev paper_theorem31_exists_finiteGapCutpoint_endpoint_two_stage_lexicographic_optimality_of_continuousOn_finiteProbabilitySimplex :=
  @GJ19OptimalBinaryRatingSystems.theorem31_exists_finiteGapCutpoint_endpoint_two_stage_lexicographic_optimality_of_continuousOn_finiteProbabilitySimplex

/--
Theorem 3.1 monotone-cutpoint bridge: if the endpoint feasibility, value, and
rate predicates depend only on the finite cutpoint range, the compact
finite-simplex optimizer is lexicographically optimal among all monotone
endpoint-feasible cutpoint chains.

Source status: finite-dimensional monotone-cutpoint `S*` bridge with explicit
finite-range extensionality hypotheses.  The remaining continuum work is
identifying the paper's general weighted source objective and rate construction
with the finite cutpoint layer.
-/
abbrev paper_theorem31_exists_cutpoint_endpoint_two_stage_lexicographic_optimality_of_continuousOn_finiteProbabilitySimplex :=
  @GJ19OptimalBinaryRatingSystems.theorem31_exists_cutpoint_endpoint_two_stage_lexicographic_optimality_of_continuousOn_finiteProbabilitySimplex

/--
Theorem 3.1 cutpoint-value `S*` existence bridge: a continuous
finite-simplex objective attains a monotone cutpoint-chain maximizer when the
source limiting-value functional only depends on the displayed finite cutpoint
range.

Source status: formalized source-shaped `S*` existence bridge.  Concrete
finite-vector continuity instantiations are formalized in `AppendixB`; the
remaining continuum work is the source-objective identification theorem for
the paper's general weighted objective.
-/
abbrev paper_theorem31_exists_cutpoint_value_argmax_of_continuousOn_finiteProbabilitySimplex_of_dependsOnlyOnRange :=
  @GJ19OptimalBinaryRatingSystems.theorem31_exists_cutpoint_value_argmax_of_continuousOn_finiteProbabilitySimplex_of_dependsOnlyOnRange

/--
Theorem 3.1 cutpoint-value `S*` existence bridge for continuous finite-vector
objectives: a continuous objective written directly as a function of the
displayed cutpoints `0, ..., M` attains a monotone cutpoint-chain maximizer.

Source status: formalized finite-vector `S*` existence bridge.  This removes
both the separate finite-range dependence premise and the composed finite-gap
continuity premise for objectives already expressed as continuous finite
formulas in the cutpoints; the paper's concrete weighted objective still needs
the corresponding finite-vector continuity instantiation.
-/
theorem paper_theorem31_exists_cutpoint_value_argmax_of_continuous_cutpointRangeFunctional
    {M : ℕ} [Nonempty (Fin M)]
    (finiteFunctional : (Fin (M + 1) → ℝ) → ℝ)
    (hcontinuous : Continuous finiteFunctional) :
    ∃ Sstar : ℕ → ℝ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (monotoneIntervalCutpointsEndpointFeasible M)
        (cutpointRangeFunctional M finiteFunctional) Sstar :=
  GJ19OptimalBinaryRatingSystems.theorem31_exists_cutpoint_value_argmax_of_continuous_cutpointRangeFunctional
    finiteFunctional hcontinuous

/--
Theorem 3.1 finite objective identification: the generic ordered-pair
cutpoint wrapper specializes to the midpoint-weighted finite objective used by
the concrete `S*` optimization branch.
-/
abbrev paper_finiteOrderedPairCutpointObjective_midpointWeightedTerm :=
  @GJ19OptimalBinaryRatingSystems.finiteOrderedPairCutpointObjective_midpointWeightedTerm

/--
Theorem 3.1 source-objective identification: the generic finite ordered-pair
cutpoint wrapper, lifted through the source cutpoint-range functional,
specializes to the midpoint-weighted ordered-pair interval objective.
-/
abbrev paper_cutpointRangeFunctional_finiteOrderedPairCutpointObjective_midpointWeightedTerm :=
  @GJ19OptimalBinaryRatingSystems.cutpointRangeFunctional_finiteOrderedPairCutpointObjective_midpointWeightedTerm

/--
Theorem 3.1 exact equation-(20) limiting-value objective: for fixed cutpoints,
the primary `S*` value is the sum of true weighted integrals over selected
ordered quality-pair cells, not a midpoint approximation.

Source status: formalized source-objective definition for a fixed cutpoint
chain.  The remaining `S*` work is the continuity/argmax bridge for this
cell-integral functional as the cutpoints vary.
-/
abbrev paper_theorem31CellIntegralLimitingValueObjective :=
  @GJ19OptimalBinaryRatingSystems.theorem31CellIntegralLimitingValueObjective

/--
Theorem 3.1 equation-(20) support-integral identity: the selected-cell sum
for the exact limiting-value objective is the integral of the source weight
over the selected ordered-pair support.

Source status: formalized fixed-cutpoint equation-(20) identity.  This names
the exact source primary objective separately from the midpoint-weighted
finite proxy used in existing continuous finite-vector branches.
-/
abbrev paper_theorem31CellIntegralLimitingValueObjective_eq_support_integral :=
  @GJ19OptimalBinaryRatingSystems.theorem31CellIntegralLimitingValueObjective_eq_support_integral

/-- Weight integral over ordered cell pairs excluding the bottom-to-top pair. This is the nontrivial-error component weight, not the full cross-cell primary value. -/
abbrev paper_nontrivialCellWeightFiniteObjective :=
  @GJ19OptimalBinaryRatingSystems.nontrivialCellWeightFiniteObjective

/-- For constant Lebesgue weight, the nontrivial-cell weight equals the sum of its rectangle areas. -/
abbrev paper_nontrivialCellWeightFiniteObjective_volume_const_eq_gapProduct :=
  @GJ19OptimalBinaryRatingSystems.nontrivialCellWeightFiniteObjective_volume_const_eq_gapProduct

/-- The constant-weight nontrivial-cell objective is continuous. -/
abbrev paper_continuous_nontrivialCellWeightFiniteObjective_volume_const :=
  @GJ19OptimalBinaryRatingSystems.continuous_nontrivialCellWeightFiniteObjective_volume_const

/-- An integrable weight gives a continuous nontrivial-cell objective on the finite-gap simplex. -/
abbrev paper_continuousOn_nontrivialCellWeightFiniteObjective_volume_of_integrableOn_Icc :=
  @GJ19OptimalBinaryRatingSystems.continuousOn_nontrivialCellWeightFiniteObjective_volume_of_integrableOn_Icc

/--
Theorem 3.1 exact equation-(20) objective, Spearman linear-weight cell
identity: on each monotone Lebesgue rectangle, the true integral of
`q_2 - q_1` equals midpoint distance times rectangle area.

Source status: formalized source-regularity identity for the Spearman
linear-weight example.  This is a component-level moving-cell integral
identity, not a midpoint approximation assumption.
-/
abbrev paper_spearmanLinearWeight_rectangleIntegral_eq_midpoint_area_of_le :=
  @GJ19OptimalBinaryRatingSystems.spearmanLinearWeight_rectangleIntegral_eq_midpoint_area_of_le

/-- For ordered cells, the nontrivial-cell linear-weight integral equals its midpoint formula. -/
abbrev paper_nontrivialCellWeightFiniteObjective_volume_spearman_eq_midpoint_sum_of_monotone :=
  @GJ19OptimalBinaryRatingSystems.nontrivialCellWeightFiniteObjective_volume_spearman_eq_midpoint_sum_of_monotone

/-- Midpoint formula for linear weights on ordered cell pairs excluding the bottom-to-top pair. -/
abbrev paper_nontrivialCellSpearmanMidpointFiniteObjective :=
  @GJ19OptimalBinaryRatingSystems.nontrivialCellSpearmanMidpointFiniteObjective

/-- The nontrivial-cell linear-weight midpoint formula is continuous. -/
abbrev paper_continuous_nontrivialCellSpearmanMidpointFiniteObjective :=
  @GJ19OptimalBinaryRatingSystems.continuous_nontrivialCellSpearmanMidpointFiniteObjective

/-- The nontrivial-cell linear-weight objective is continuous on the finite-gap simplex. -/
abbrev paper_continuousOn_nontrivialCellWeightFiniteObjective_volume_spearman_finiteGapCutpoint :=
  @GJ19OptimalBinaryRatingSystems.continuousOn_nontrivialCellWeightFiniteObjective_volume_spearman_finiteGapCutpoint

/-- The nontrivial-cell linear-weight objective attains a maximum. -/
abbrev paper_exists_nontrivialCellWeight_volume_spearman_cutpoint_value_argmax :=
  @GJ19OptimalBinaryRatingSystems.exists_nontrivialCellWeight_volume_spearman_cutpoint_value_argmax

/-- The nontrivial-cell integrable-weight objective attains a maximum. -/
abbrev paper_exists_nontrivialCellWeight_volume_weighted_cutpoint_value_argmax_of_integrableOn_Icc :=
  @GJ19OptimalBinaryRatingSystems.exists_nontrivialCellWeight_volume_weighted_cutpoint_value_argmax_of_integrableOn_Icc

/-- Lexicographic optimization of nontrivial-cell linear weight and the uniform-matching adjacent-rate formula. -/
abbrev paper_exists_nontrivialCellWeight_volume_spearman_uniform_endpoint_two_stage_lexicographic_optimality :=
  @GJ19OptimalBinaryRatingSystems.exists_nontrivialCellWeight_volume_spearman_uniform_endpoint_two_stage_lexicographic_optimality

/-- Lexicographic optimization of nontrivial-cell integrable weight and the uniform-matching adjacent-rate formula. -/
abbrev paper_exists_nontrivialCellWeight_volume_weighted_uniform_endpoint_two_stage_lexicographic_optimality_of_integrableOn_Icc :=
  @GJ19OptimalBinaryRatingSystems.exists_nontrivialCellWeight_volume_weighted_uniform_endpoint_two_stage_lexicographic_optimality_of_integrableOn_Icc

/-- A continuous nontrivial-cell objective attains a maximum. -/
abbrev paper_exists_nontrivialCellWeight_cutpoint_value_argmax_of_continuous :=
  @GJ19OptimalBinaryRatingSystems.exists_nontrivialCellWeight_cutpoint_value_argmax_of_continuous

/-- The constant-weight nontrivial-cell objective attains a maximum. -/
abbrev paper_exists_nontrivialCellWeight_volume_const_cutpoint_value_argmax :=
  @GJ19OptimalBinaryRatingSystems.exists_nontrivialCellWeight_volume_const_cutpoint_value_argmax

/-- A continuous nontrivial-cell objective and the uniform-matching adjacent-rate formula admit a lexicographic optimizer. -/
abbrev paper_exists_nontrivialCellWeight_uniform_endpoint_two_stage_lexicographic_optimality_of_continuous :=
  @GJ19OptimalBinaryRatingSystems.exists_nontrivialCellWeight_uniform_endpoint_two_stage_lexicographic_optimality_of_continuous

/-- Lexicographic optimization of constant nontrivial-cell weight and the uniform-matching adjacent-rate formula. -/
abbrev paper_exists_nontrivialCellWeight_volume_const_uniform_endpoint_two_stage_lexicographic_optimality :=
  @GJ19OptimalBinaryRatingSystems.exists_nontrivialCellWeight_volume_const_uniform_endpoint_two_stage_lexicographic_optimality

/--
Theorem 3.1 uniform-matching finite-dimensional `S*` bridge with source-shaped
finite-range dependence: the compact cutpoint optimizer and canonical
equalized endpoint levels give a lexicographically optimal design when the
limiting-value functional only depends on the displayed finite cutpoint range.

Source status: formalized source-shaped finite-dimensional `S*` bridge; the
paper's concrete weighted objective still needs continuity and finite-range
dependence instantiated.
-/
abbrev paper_theorem31_exists_cutpoint_uniform_endpoint_two_stage_lexicographic_optimality_of_continuousOn_finiteProbabilitySimplex_of_dependsOnlyOnRange :=
  @GJ19OptimalBinaryRatingSystems.theorem31_exists_cutpoint_uniform_endpoint_two_stage_lexicographic_optimality_of_continuousOn_finiteProbabilitySimplex_of_dependsOnlyOnRange

/--
Theorem 3.1 uniform-matching finite-vector `S*` bridge: for a continuous
finite-vector cutpoint objective, the compact cutpoint optimizer and canonical
equalized endpoint levels give a lexicographically optimal cutpoint/endpoint
design.

Source status: formalized finite-vector uniform-matching `S*` bridge.  The
implementation now includes concrete Kendall/Spearman, midpoint-weighted, and
generic finite ordered-pair instantiations; the remaining continuum work is
to identify the paper's general weighted source objective with one of those
finite cutpoint formulas.
-/
theorem paper_theorem31_exists_cutpoint_uniform_endpoint_two_stage_lexicographic_optimality_of_continuous_cutpointRangeFunctional
    {m : ℕ}
    (finiteFunctional : (Fin ((m + 2) + 1) → ℝ) → ℝ)
    (hcontinuous : Continuous finiteFunctional) :
    ∃ design : (ℕ → ℝ) × (Fin (m + 2) → ℝ),
      AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          monotoneIntervalCutpointsEndpointFeasible (m + 2) design.1 ∧
            BinaryEndpointLevelVector design.2)
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          cutpointRangeFunctional (m + 2) finiteFunctional design.1)
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          binaryEndpointAwareAdjacentRateObjective design.2
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        design :=
  GJ19OptimalBinaryRatingSystems.theorem31_exists_cutpoint_uniform_endpoint_two_stage_lexicographic_optimality_of_continuous_cutpointRangeFunctional
    finiteFunctional hcontinuous

/--
Theorem 3.1 staged source certificate: if the source discretization `S*` is
represented by a strict cutpoint chain maximizing the limiting-value objective,
then the endpoint levels and source-defined `Wbar_k` rate certificate are
derived by the forward-clipped construction.

Source status: formalized staged decomposition for a source argmax
discretization; cross-discretization rate tie-breaking for nonunique `S*`
remains a separate strengthening.
-/
abbrev paper_theorem31_strict_cutpoint_value_argmax_forward_clipped_endpoint_source_certificate :=
  @GJ19OptimalBinaryRatingSystems.theorem31_strict_cutpoint_value_argmax_forward_clipped_endpoint_source_certificate

/--
Theorem 3.1 nonunique-`S*` source-model theorem: under the weighted
finite-level source convention, Lean constructs the equalized endpoint vector
and exact source-defined `Wbar_k` rate certificate.  If several
discretizations maximize the limiting value, the only remaining input is the
source's secondary-rate tie-breaking comparison across those value-maximizing
discretizations.

Source status: formalized under the explicit weighted finite-level source
convention and the value-tie secondary-rate convention needed for nonunique
`S*`.
-/
abbrev paper_theorem31_appropriate_finite_levels_weighted_value_tie_lexicographic_certificate :=
  @GJ19OptimalBinaryRatingSystems.theorem31_appropriate_finite_levels_weighted_value_tie_lexicographic_certificate

/--
Theorem 3.1 nonunique-`S*` source-model theorem with the tie condition stated
as a standard secondary maximizer on the limiting-value fiber.  This is the
clean value-then-rate convention suggested by the paper prose: among
limiting-value maximizers, choose the endpoint/cutpoint pair maximizing the
displayed large-deviation rate.

Source status: formalized under the weighted finite-level source convention
and an explicit value-fiber secondary-rate maximization convention.
-/
abbrev paper_theorem31_appropriate_finite_levels_weighted_value_fiber_rate_max_lexicographic_certificate :=
  @GJ19OptimalBinaryRatingSystems.theorem31_appropriate_finite_levels_weighted_value_fiber_rate_max_lexicographic_certificate

/--
Theorem C.1 upper-bound bridge: an almost-everywhere exponential rate envelope
for the pointwise error kernel gives the same exponential upper bound for the
integrated error.

This is the upper-bound half of the paper's Laplace-principle step.  The
lower-bound half is the remaining compact near-minimizer/positive-measure
argument.
-/
theorem paper_theoremC1_integral_error_upper_bound_from_rate_envelope
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [MeasureTheory.IsFiniteMeasure μ]
    (errorKernel : ℕ → Ω → ℝ) (rateFunction : Ω → ℝ)
    {targetRate C : ℝ}
    (hCpos : 0 < C)
    (herror_meas :
      ∀ k, MeasureTheory.AEStronglyMeasurable (errorKernel k) μ)
    (hrate :
      ∀ᵐ x ∂μ, targetRate ≤ rateFunction x)
    (herror_bound :
      ∀ k, ∀ᵐ x ∂μ,
        0 ≤ errorKernel k x ∧
          errorKernel k x ≤
            C * Real.exp (-(k : ℝ) * rateFunction x)) :
    HasExpUpperBoundWithConst
      (fun k : ℕ => ∫ x, errorKernel k x ∂μ)
      targetRate :=
  GJ19OptimalBinaryRatingSystems.theoremC1_integral_error_upper_bound_from_rate_envelope
    μ errorKernel rateFunction hCpos herror_meas hrate herror_bound

/--
Theorem C.1 lower-bound near-minimizer bridge: a positive-measure set with a
uniform exponential lower envelope gives the same exponential lower bound for
the set integral over that near-minimizer set.
-/
theorem paper_theoremC1_setIntegral_error_lower_bound_from_near_minimizer_set
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [MeasureTheory.IsFiniteMeasure μ]
    {nearMinimizers : Set Ω}
    (errorKernel : ℕ → Ω → ℝ)
    {rate c : ℝ}
    (hmeasure_pos : 0 < μ.real nearMinimizers)
    (hcpos : 0 < c)
    (herror_int :
      ∀ k, MeasureTheory.IntegrableOn (errorKernel k) nearMinimizers μ)
    (hlower :
      ∀ᶠ k : ℕ in Filter.atTop,
        ∀ᵐ x ∂μ.restrict nearMinimizers,
          c * Real.exp (-(k : ℝ) * rate) ≤ errorKernel k x) :
    HasExpLowerBoundWithConst
      (fun k : ℕ => ∫ x in nearMinimizers, errorKernel k x ∂μ)
      rate :=
  GJ19OptimalBinaryRatingSystems.theoremC1_setIntegral_error_lower_bound_from_near_minimizer_set
    μ errorKernel hmeasure_pos hcpos herror_int hlower

/--
Theorem C.1 exact-rate skeleton: an almost-everywhere rate envelope plus
positive-measure near-minimizer lower sets for every rate above the infimum
implies the integrated error has that exponential decay rate.
-/
theorem paper_theoremC1_integral_error_exponential_rate_from_rate_envelope_and_near_minimizer_sets
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [MeasureTheory.IsFiniteMeasure μ]
    (errorKernel : ℕ → Ω → ℝ) (rateFunction : Ω → ℝ)
    {rate C : ℝ}
    (hCpos : 0 < C)
    (herror_meas :
      ∀ k, MeasureTheory.AEStronglyMeasurable (errorKernel k) μ)
    (herror_int :
      ∀ k, MeasureTheory.Integrable (errorKernel k) μ)
    (hrate :
      ∀ᵐ x ∂μ, rate ≤ rateFunction x)
    (hupper_envelope :
      ∀ k, ∀ᵐ x ∂μ,
        0 ≤ errorKernel k x ∧
          errorKernel k x ≤
            C * Real.exp (-(k : ℝ) * rateFunction x))
    (hlower_sets : ∀ targetRate, rate < targetRate →
      ∃ nearMinimizers : Set Ω, ∃ c : ℝ,
        0 < μ.real nearMinimizers ∧ 0 < c ∧
          (∀ k, MeasureTheory.IntegrableOn
            (errorKernel k) nearMinimizers μ) ∧
            ∀ᶠ k : ℕ in Filter.atTop,
              ∀ᵐ x ∂μ.restrict nearMinimizers,
                c * Real.exp (-(k : ℝ) * targetRate) ≤ errorKernel k x) :
    HasExponentialRate
      (fun k : ℕ => ∫ x, errorKernel k x ∂μ)
      rate :=
  GJ19OptimalBinaryRatingSystems.theoremC1_integral_error_exponential_rate_from_rate_envelope_and_near_minimizer_sets
    μ errorKernel rateFunction hCpos herror_meas herror_int hrate
    hupper_envelope hlower_sets

/--
Theorem C.1 zero-rate skeleton: a fixed positive upper bound on the integrated
nonnegative error, plus positive-measure local lower envelopes at every
positive target rate, implies exact exponential rate zero.
-/
theorem paper_theoremC1_integral_error_zero_rate_from_constant_upper_bound_and_near_minimizer_sets
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [MeasureTheory.IsFiniteMeasure μ]
    (errorKernel : ℕ → Ω → ℝ) {B : ℝ}
    (hBpos : 0 < B)
    (herror_int :
      ∀ k, MeasureTheory.Integrable (errorKernel k) μ)
    (herror_nonneg :
      ∀ k, ∀ᵐ x ∂μ, 0 ≤ errorKernel k x)
    (hupper_const :
      ∀ᶠ k : ℕ in Filter.atTop, (∫ x, errorKernel k x ∂μ) ≤ B)
    (hlower_sets : ∀ targetRate : ℝ, 0 < targetRate →
      ∃ nearMinimizers : Set Ω, ∃ c : ℝ,
        0 < μ.real nearMinimizers ∧ 0 < c ∧
          (∀ k, MeasureTheory.IntegrableOn
            (errorKernel k) nearMinimizers μ) ∧
            ∀ᶠ k : ℕ in Filter.atTop,
              ∀ᵐ x ∂μ.restrict nearMinimizers,
                c * Real.exp (-(k : ℝ) * targetRate) ≤ errorKernel k x) :
    HasExponentialRate
      (fun k : ℕ => ∫ x, errorKernel k x ∂μ)
      0 :=
  GJ19OptimalBinaryRatingSystems.theoremC1_integral_error_zero_rate_from_constant_upper_bound_and_near_minimizer_sets
    μ errorKernel hBpos herror_int herror_nonneg hupper_const hlower_sets

/--
Theorem C.1 weighted-kernel zero-rate skeleton from a normalized-log
certificate plus positive-measure near-rate sets with locally positive weight.
-/
theorem paper_theoremC1_weighted_kernel_zero_rate_from_constant_upper_bound_uniformNormalizedLogRateCertificate_nearRate_sets
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [MeasureTheory.IsFiniteMeasure μ]
    (weight : Ω → ℝ) (kernel : ℕ → Ω → ℝ) (rate : Ω → ℝ)
    {certSet : Set Ω} {B : ℝ}
    (hBpos : 0 < B)
    (hkernel_int :
      ∀ k : ℕ, MeasureTheory.Integrable
        (fun x : Ω => weight x * kernel k x) μ)
    (hkernel_nonneg :
      ∀ k : ℕ, ∀ᵐ x ∂μ, 0 ≤ weight x * kernel k x)
    (hupper_const :
      ∀ᶠ k : ℕ in Filter.atTop,
        (∫ x, weight x * kernel k x ∂μ) ≤ B)
    (hcert : UniformNormalizedLogRateCertificateOn kernel rate certSet)
    (hnear_sets : ∀ targetRate : ℝ, 0 < targetRate →
      ∃ nearMinimizers : Set Ω, ∃ c : ℝ, ∃ δ : ℝ,
        MeasurableSet nearMinimizers ∧
          0 < μ.real nearMinimizers ∧ 0 < c ∧ 0 < δ ∧
            nearMinimizers ⊆ certSet ∧
              (∀ k : ℕ, MeasureTheory.IntegrableOn
                (fun x : Ω => weight x * kernel k x)
                nearMinimizers μ) ∧
                (∀ᵐ x ∂μ.restrict nearMinimizers, c ≤ weight x) ∧
                  ∀ x : Ω, x ∈ nearMinimizers →
                    rate x + δ ≤ targetRate) :
    HasExponentialRate
      (fun k : ℕ => ∫ x, weight x * kernel k x ∂μ)
      0 :=
  GJ19OptimalBinaryRatingSystems.theoremC1_weighted_kernel_zero_rate_from_constant_upper_bound_uniformNormalizedLogRateCertificate_nearRate_sets
    μ weight kernel rate hBpos hkernel_int hkernel_nonneg hupper_const hcert
    hnear_sets

/--
Theorem C.1 weighted-kernel zero-rate skeleton from pointwise exponential-rate
certificates on positive-measure near-rate sets.

Source status: conditional Laplace-skeleton component; pointwise
exponential-rate certificates are visible hypotheses, not hidden paper
assumptions.
-/
theorem paper_theoremC1_weighted_kernel_zero_rate_from_constant_upper_bound_pointwiseExponentialRateCertificate_nearRate_sets
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [MeasureTheory.IsFiniteMeasure μ]
    (weight : Ω → ℝ) (kernel : ℕ → Ω → ℝ) (rate : Ω → ℝ)
    {B : ℝ}
    (hBpos : 0 < B)
    (hkernel_int :
      ∀ k : ℕ, MeasureTheory.Integrable
        (fun x : Ω => weight x * kernel k x) μ)
    (hkernel_nonneg :
      ∀ k : ℕ, ∀ᵐ x ∂μ, 0 ≤ weight x * kernel k x)
    (hupper_const :
      ∀ᶠ k : ℕ in Filter.atTop,
        (∫ x, weight x * kernel k x ∂μ) ≤ B)
    (hkernel_meas : ∀ k : ℕ, Measurable (kernel k))
    (hnear_sets : ∀ targetRate : ℝ, 0 < targetRate →
      ∃ nearMinimizers : Set Ω, ∃ c : ℝ, ∃ δ : ℝ,
        MeasurableSet nearMinimizers ∧
          0 < μ.real nearMinimizers ∧ 0 < c ∧ 0 < δ ∧
            (∀ k : ℕ, MeasureTheory.IntegrableOn
              (fun x : Ω => weight x * kernel k x)
              nearMinimizers μ) ∧
              (∀ᵐ x ∂μ.restrict nearMinimizers, c ≤ weight x) ∧
                (∀ x : Ω, x ∈ nearMinimizers →
                  rate x + δ ≤ targetRate) ∧
                  ∀ x : Ω, x ∈ nearMinimizers →
                    ExponentialRateCertificate
                      (fun k : ℕ => kernel k x) (rate x)) :
    HasExponentialRate
      (fun k : ℕ => ∫ x, weight x * kernel k x ∂μ)
      0 :=
  GJ19OptimalBinaryRatingSystems.theoremC1_weighted_kernel_zero_rate_from_constant_upper_bound_pointwiseExponentialRateCertificate_nearRate_sets
    μ weight kernel rate hBpos hkernel_int hkernel_nonneg hupper_const
    hkernel_meas hnear_sets

/--
Theorem C.1 weighted-kernel zero-rate skeleton from a normalized-log
certificate plus the weighted near-essential-infimum interface at rate zero.
-/
theorem paper_theoremC1_weighted_kernel_zero_rate_from_constant_upper_bound_uniformNormalizedLogRateCertificate_weightedNearInf
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [MeasureTheory.IsFiniteMeasure μ]
    (weight : Ω → ℝ) (kernel : ℕ → Ω → ℝ) (rate : Ω → ℝ)
    {B : ℝ}
    (hBpos : 0 < B)
    (hkernel_int :
      ∀ k : ℕ, MeasureTheory.Integrable
        (fun x : Ω => weight x * kernel k x) μ)
    (hkernel_nonneg :
      ∀ k : ℕ, ∀ᵐ x ∂μ, 0 ≤ weight x * kernel k x)
    (hupper_const :
      ∀ᶠ k : ℕ in Filter.atTop,
        (∫ x, weight x * kernel k x ∂μ) ≤ B)
    (hcert : UniformNormalizedLogRateCertificateOn kernel rate Set.univ)
    (hweighted_near :
      HasPositiveWeightNearAEEssentialInfimum μ weight rate 0) :
    HasExponentialRate
      (fun k : ℕ => ∫ x, weight x * kernel k x ∂μ)
      0 :=
  GJ19OptimalBinaryRatingSystems.theoremC1_weighted_kernel_zero_rate_from_constant_upper_bound_uniformNormalizedLogRateCertificate_weightedNearInf
    μ weight kernel rate hBpos hkernel_int hkernel_nonneg hupper_const hcert
    hweighted_near

/--
Theorem C.1 weighted-kernel zero-rate skeleton from a normalized-log
certificate on an almost-everywhere full set plus the weighted
near-essential-infimum interface at rate zero.
-/
theorem paper_theoremC1_weighted_kernel_zero_rate_from_constant_upper_bound_uniformNormalizedLogRateCertificate_weightedNearInf_of_ae_mem_certSet
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [MeasureTheory.IsFiniteMeasure μ]
    (weight : Ω → ℝ) (kernel : ℕ → Ω → ℝ) (rate : Ω → ℝ)
    {certSet : Set Ω} {B : ℝ}
    (hBpos : 0 < B)
    (hkernel_int :
      ∀ k : ℕ, MeasureTheory.Integrable
        (fun x : Ω => weight x * kernel k x) μ)
    (hkernel_nonneg :
      ∀ k : ℕ, ∀ᵐ x ∂μ, 0 ≤ weight x * kernel k x)
    (hupper_const :
      ∀ᶠ k : ℕ in Filter.atTop,
        (∫ x, weight x * kernel k x ∂μ) ≤ B)
    (hcert : UniformNormalizedLogRateCertificateOn kernel rate certSet)
    (hcertSet_ae : ∀ᵐ x ∂μ, x ∈ certSet)
    (hweighted_near :
      HasPositiveWeightNearAEEssentialInfimum μ weight rate 0) :
    HasExponentialRate
      (fun k : ℕ => ∫ x, weight x * kernel k x ∂μ)
      0 :=
  GJ19OptimalBinaryRatingSystems.theoremC1_weighted_kernel_zero_rate_from_constant_upper_bound_uniformNormalizedLogRateCertificate_weightedNearInf_of_ae_mem_certSet
    μ weight kernel rate hBpos hkernel_int hkernel_nonneg hupper_const hcert
    hcertSet_ae hweighted_near

/--
Theorem C.1 Laplace-principle skeleton: uniform convergence of `phiSeq k` to
`phi`, an almost-everywhere lower bound `rate ≤ phi`, and positive-measure
near-infimum restricted sets imply the exponential rate of
`∫ exp (-(k : ℝ) * phiSeq k x)`.
-/
theorem paper_theoremC1_laplace_integral_exponential_rate_of_uniform_tendsto_nearInf
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [MeasureTheory.IsFiniteMeasure μ]
    (phiSeq : ℕ → Ω → ℝ) (phi : Ω → ℝ) {rate : ℝ}
    (hintegrable :
      ∀ k : ℕ, MeasureTheory.Integrable
        (fun x : Ω => Real.exp (-(k : ℝ) * (phiSeq k x))) μ)
    (hphi_lower : ∀ᵐ x ∂μ, rate ≤ phi x)
    (huniform : ∀ ε > 0,
      ∀ᶠ k : ℕ in Filter.atTop,
        ∀ x : Ω, |phiSeq k x - phi x| ≤ ε)
    (hnear : ∀ ε > 0,
      ∃ nearMinimizers : Set Ω,
        0 < μ.real nearMinimizers ∧
          ∀ᵐ x ∂μ.restrict nearMinimizers, phi x ≤ rate + ε) :
    HasExponentialRate
      (fun k : ℕ => ∫ x, Real.exp (-(k : ℝ) * (phiSeq k x)) ∂μ)
      rate :=
  GJ19OptimalBinaryRatingSystems.theoremC1_laplace_integral_exponential_rate_of_uniform_tendsto_nearInf
    μ phiSeq phi hintegrable hphi_lower huniform hnear

/--
Theorem C.1 Laplace-principle skeleton in source-style essential-infimum
notation: uniform convergence of `phiSeq k` to `phi`, together with the
real-valued almost-everywhere essential infimum condition for `phi`, implies
the exponential rate of `∫ exp (-(k : ℝ) * phiSeq k x)`.
-/
theorem paper_theoremC1_laplace_integral_exponential_rate_of_uniform_tendsto_essentialInf
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [MeasureTheory.IsFiniteMeasure μ]
    (phiSeq : ℕ → Ω → ℝ) (phi : Ω → ℝ) {rate : ℝ}
    (hintegrable :
      ∀ k : ℕ, MeasureTheory.Integrable
        (fun x : Ω => Real.exp (-(k : ℝ) * (phiSeq k x))) μ)
    (hess : HasAEEssentialInfimum μ phi rate)
    (huniform : ∀ ε > 0,
      ∀ᶠ k : ℕ in Filter.atTop,
        ∀ x : Ω, |phiSeq k x - phi x| ≤ ε) :
    HasExponentialRate
      (fun k : ℕ => ∫ x, Real.exp (-(k : ℝ) * (phiSeq k x)) ∂μ)
      rate :=
  GJ19OptimalBinaryRatingSystems.theoremC1_laplace_integral_exponential_rate_of_uniform_tendsto_essentialInf
    μ phiSeq phi hintegrable hess huniform

/--
Weighted Theorem C.1 Laplace-principle skeleton: bounded nonnegative objective
weights preserve the exponential rate of the weighted integral when the
near-essential-minimizer sets contain positive-measure regions where the
weight is uniformly positive.

Source status: conditional weighted Laplace-principle skeleton for Theorem C.1.
-/
theorem paper_theoremC1_weighted_laplace_integral_exponential_rate_of_uniform_tendsto_weightedEssentialInf
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [MeasureTheory.IsFiniteMeasure μ]
    (weight : Ω → ℝ) (phiSeq : ℕ → Ω → ℝ) (phi : Ω → ℝ)
    {rate W : ℝ}
    (hintegrable :
      ∀ k : ℕ, MeasureTheory.Integrable
        (fun x : Ω => weight x * Real.exp (-(k : ℝ) * (phiSeq k x))) μ)
    (hWpos : 0 < W)
    (hweight_nonneg : ∀ᵐ x ∂μ, 0 ≤ weight x)
    (hweight_bound : ∀ᵐ x ∂μ, weight x ≤ W)
    (hess : HasAEEssentialInfimum μ phi rate)
    (hweighted_near :
      HasPositiveWeightNearAEEssentialInfimum μ weight phi rate)
    (huniform : ∀ ε > 0,
      ∀ᶠ k : ℕ in Filter.atTop,
        ∀ x : Ω, |phiSeq k x - phi x| ≤ ε) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x, weight x * Real.exp (-(k : ℝ) * (phiSeq k x)) ∂μ)
      rate :=
  GJ19OptimalBinaryRatingSystems.theoremC1_weighted_laplace_integral_exponential_rate_of_uniform_tendsto_weightedEssentialInf
    μ weight phiSeq phi hintegrable hWpos hweight_nonneg hweight_bound
    hess hweighted_near huniform

/--
Certificate form of the weighted Theorem C.1 Laplace-principle skeleton, ready
to feed finite component aggregation in Lemma C.3.
-/
theorem paper_theoremC1_weighted_laplace_exponentialRateCertificate_of_uniform_tendsto_weightedEssentialInf
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [MeasureTheory.IsFiniteMeasure μ]
    (weight : Ω → ℝ) (phiSeq : ℕ → Ω → ℝ) (phi : Ω → ℝ)
    {rate W : ℝ}
    (hintegrable :
      ∀ k : ℕ, MeasureTheory.Integrable
        (fun x : Ω => weight x * Real.exp (-(k : ℝ) * (phiSeq k x))) μ)
    (hWpos : 0 < W)
    (hweight_nonneg : ∀ᵐ x ∂μ, 0 ≤ weight x)
    (hweight_bound : ∀ᵐ x ∂μ, weight x ≤ W)
    (hess : HasAEEssentialInfimum μ phi rate)
    (hweighted_near :
      HasPositiveWeightNearAEEssentialInfimum μ weight phi rate)
    (huniform : ∀ ε > 0,
      ∀ᶠ k : ℕ in Filter.atTop,
        ∀ x : Ω, |phiSeq k x - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun k : ℕ =>
        ∫ x, weight x * Real.exp (-(k : ℝ) * (phiSeq k x)) ∂μ)
      rate :=
  GJ19OptimalBinaryRatingSystems.theoremC1_weighted_laplace_exponentialRateCertificate_of_uniform_tendsto_weightedEssentialInf
    μ weight phiSeq phi hintegrable hWpos hweight_nonneg hweight_bound
    hess hweighted_near huniform

/--
Positive-kernel Theorem C.1 certificate: when the integrand is a pairwise
error probability kernel and `-log kernel / k` converges uniformly to the
limiting rate function, the weighted error integral has the corresponding
exponential-rate certificate.
-/
theorem paper_theoremC1_weighted_positive_kernel_exponentialRateCertificate_of_uniform_logRate_tendsto_weightedEssentialInf
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [MeasureTheory.IsFiniteMeasure μ]
    (weight : Ω → ℝ) (kernel : ℕ → Ω → ℝ) (phi : Ω → ℝ)
    {rate W : ℝ}
    (hkernel_int :
      ∀ k : ℕ, MeasureTheory.Integrable
        (fun x : Ω => weight x * kernel k x) μ)
    (hweight_int : MeasureTheory.Integrable weight μ)
    (hWpos : 0 < W)
    (hweight_nonneg : ∀ᵐ x ∂μ, 0 ≤ weight x)
    (hweight_bound : ∀ᵐ x ∂μ, weight x ≤ W)
    (hess : HasAEEssentialInfimum μ phi rate)
    (hweighted_near :
      HasPositiveWeightNearAEEssentialInfimum μ weight phi rate)
    (hkernel_pos : ∀ k x, 0 < kernel k x)
    (huniform_log : ∀ ε > 0,
      ∀ᶠ k : ℕ in Filter.atTop,
        ∀ x : Ω, |(-Real.log (kernel k x) / (k : ℝ)) - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun k : ℕ => ∫ x, weight x * kernel k x ∂μ)
      rate :=
  GJ19OptimalBinaryRatingSystems.theoremC1_weighted_positive_kernel_exponentialRateCertificate_of_uniform_logRate_tendsto_weightedEssentialInf
    μ weight kernel phi hkernel_int hweight_int hWpos hweight_nonneg
    hweight_bound hess hweighted_near hkernel_pos huniform_log

/--
Positive-kernel Theorem C.1 certificate with source-style continuous-minimizer
assumptions: a continuous limiting rate with a global minimizer and uniformly
positive bounded weights supplies the Laplace essential-infimum certificates.
-/
theorem paper_theoremC1_weighted_positive_kernel_exponentialRateCertificate_of_uniform_logRate_tendsto_continuous_min_uniformWeightLower
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω]
    (μ : Measure Ω) [MeasureTheory.IsFiniteMeasure μ]
    [Measure.IsOpenPosMeasure μ]
    (weight : Ω → ℝ) (kernel : ℕ → Ω → ℝ) (phi : Ω → ℝ)
    {rate W c : ℝ}
    (hkernel_int :
      ∀ k : ℕ, MeasureTheory.Integrable
        (fun x : Ω => weight x * kernel k x) μ)
    (hweight_int : MeasureTheory.Integrable weight μ)
    (hWpos : 0 < W)
    (hcpos : 0 < c)
    (hweight_lower : ∀ᵐ x ∂μ, c ≤ weight x)
    (hweight_bound : ∀ᵐ x ∂μ, weight x ≤ W)
    (x0 : Ω)
    (hmin : ∀ x : Ω, rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hcont : ContinuousAt phi x0)
    (hkernel_pos : ∀ k x, 0 < kernel k x)
    (huniform_log : ∀ ε > 0,
      ∀ᶠ k : ℕ in Filter.atTop,
        ∀ x : Ω, |(-Real.log (kernel k x) / (k : ℝ)) - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun k : ℕ => ∫ x, weight x * kernel k x ∂μ)
      rate :=
  GJ19OptimalBinaryRatingSystems.theoremC1_weighted_positive_kernel_exponentialRateCertificate_of_uniform_logRate_tendsto_continuous_min_uniformWeightLower
    μ weight kernel phi hkernel_int hweight_int hWpos hcpos hweight_lower
    hweight_bound x0 hmin hx0 hcont hkernel_pos huniform_log

/--
Positive-kernel Theorem C.1 certificate with a local positive-weight
minimizer: a continuous limiting rate with a global minimizer and an objective
weight continuous and positive at that minimizer supply the positive-near-minimum
condition.
-/
theorem paper_theoremC1_weighted_positive_kernel_exponentialRateCertificate_of_uniform_logRate_tendsto_continuous_min_weight_pos
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω]
    (μ : Measure Ω) [MeasureTheory.IsFiniteMeasure μ]
    [Measure.IsOpenPosMeasure μ]
    (weight : Ω → ℝ) (kernel : ℕ → Ω → ℝ) (phi : Ω → ℝ)
    {rate W : ℝ}
    (hkernel_int :
      ∀ k : ℕ, MeasureTheory.Integrable
        (fun x : Ω => weight x * kernel k x) μ)
    (hweight_int : MeasureTheory.Integrable weight μ)
    (hWpos : 0 < W)
    (hweight_nonneg : ∀ᵐ x ∂μ, 0 ≤ weight x)
    (hweight_bound : ∀ᵐ x ∂μ, weight x ≤ W)
    (x0 : Ω)
    (hmin : ∀ x : Ω, rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hphi_cont : ContinuousAt phi x0)
    (hweight_cont : ContinuousAt weight x0)
    (hweight_x0_pos : 0 < weight x0)
    (hkernel_pos : ∀ k x, 0 < kernel k x)
    (huniform_log : ∀ ε > 0,
      ∀ᶠ k : ℕ in Filter.atTop,
        ∀ x : Ω, |(-Real.log (kernel k x) / (k : ℝ)) - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun k : ℕ => ∫ x, weight x * kernel k x ∂μ)
      rate :=
  GJ19OptimalBinaryRatingSystems.theoremC1_weighted_positive_kernel_exponentialRateCertificate_of_uniform_logRate_tendsto_continuous_min_weight_pos
    μ weight kernel phi hkernel_int hweight_int hWpos hweight_nonneg
    hweight_bound x0 hmin hx0 hphi_cont hweight_cont hweight_x0_pos
    hkernel_pos huniform_log

/--
Restricted-cell positive-kernel Theorem C.1 certificate with source-style
continuous-minimizer assumptions.  This is the interval-pair component form for
piecewise-continuum objectives.
-/
theorem paper_theoremC1_weighted_positive_kernel_exponentialRateCertificate_of_uniform_logRate_tendsto_restrict_continuous_min_uniformWeightLower
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω]
    (μ : Measure Ω) [MeasureTheory.IsFiniteMeasure μ] {cell : Set Ω}
    (hcell : MeasurableSet cell)
    (weight : Ω → ℝ) (kernel : ℕ → Ω → ℝ) (phi : Ω → ℝ)
    {rate W c : ℝ}
    (hkernel_int :
      ∀ k : ℕ, MeasureTheory.Integrable
        (fun x : Ω => weight x * kernel k x) (μ.restrict cell))
    (hweight_int : MeasureTheory.Integrable weight (μ.restrict cell))
    (hWpos : 0 < W)
    (hcpos : 0 < c)
    (hweight_lower : ∀ᵐ x ∂μ.restrict cell, c ≤ weight x)
    (hweight_bound : ∀ᵐ x ∂μ.restrict cell, weight x ≤ W)
    (x0 : Ω)
    (hmin : ∀ x : Ω, x ∈ cell → rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hcont : ContinuousAt phi x0)
    (hlocal_pos :
      ∀ U : Set Ω, IsOpen U → x0 ∈ U → 0 < μ (cell ∩ U))
    (hkernel_pos : ∀ k x, 0 < kernel k x)
    (huniform_log : ∀ ε > 0,
      ∀ᶠ k : ℕ in Filter.atTop,
        ∀ x : Ω, |(-Real.log (kernel k x) / (k : ℝ)) - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun k : ℕ => ∫ x, weight x * kernel k x ∂μ.restrict cell)
      rate :=
  GJ19OptimalBinaryRatingSystems.theoremC1_weighted_positive_kernel_exponentialRateCertificate_of_uniform_logRate_tendsto_restrict_continuous_min_uniformWeightLower
    μ hcell weight kernel phi hkernel_int hweight_int hWpos hcpos
    hweight_lower hweight_bound x0 hmin hx0 hcont hlocal_pos hkernel_pos
    huniform_log

/--
Restricted-cell positive-kernel Theorem C.1 certificate with a local
positive-weight minimizer rather than a cell-wide positive lower bound.
-/
theorem paper_theoremC1_weighted_positive_kernel_exponentialRateCertificate_of_uniform_logRate_tendsto_restrict_continuous_min_weight_pos
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω]
    (μ : Measure Ω) [MeasureTheory.IsFiniteMeasure μ] {cell : Set Ω}
    (hcell : MeasurableSet cell)
    (weight : Ω → ℝ) (kernel : ℕ → Ω → ℝ) (phi : Ω → ℝ)
    {rate W : ℝ}
    (hkernel_int :
      ∀ k : ℕ, MeasureTheory.Integrable
        (fun x : Ω => weight x * kernel k x) (μ.restrict cell))
    (hweight_int : MeasureTheory.Integrable weight (μ.restrict cell))
    (hWpos : 0 < W)
    (hweight_nonneg : ∀ᵐ x ∂μ.restrict cell, 0 ≤ weight x)
    (hweight_bound : ∀ᵐ x ∂μ.restrict cell, weight x ≤ W)
    (x0 : Ω)
    (hmin : ∀ x : Ω, x ∈ cell → rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hphi_cont : ContinuousAt phi x0)
    (hweight_cont : ContinuousAt weight x0)
    (hweight_x0_pos : 0 < weight x0)
    (hlocal_pos :
      ∀ U : Set Ω, IsOpen U → x0 ∈ U → 0 < μ (cell ∩ U))
    (hkernel_pos : ∀ k x, 0 < kernel k x)
    (huniform_log : ∀ ε > 0,
      ∀ᶠ k : ℕ in Filter.atTop,
        ∀ x : Ω, |(-Real.log (kernel k x) / (k : ℝ)) - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun k : ℕ => ∫ x, weight x * kernel k x ∂μ.restrict cell)
      rate :=
  GJ19OptimalBinaryRatingSystems.theoremC1_weighted_positive_kernel_exponentialRateCertificate_of_uniform_logRate_tendsto_restrict_continuous_min_weight_pos
    μ hcell weight kernel phi hkernel_int hweight_int hWpos hweight_nonneg
    hweight_bound x0 hmin hx0 hphi_cont hweight_cont hweight_x0_pos
    hlocal_pos hkernel_pos huniform_log

/--
Restricted-cell positive-kernel Theorem C.1 certificate where local positive cell
mass follows from closure/interior support.
-/
theorem paper_theoremC1_weighted_positive_kernel_exponentialRateCertificate_of_uniform_logRate_tendsto_restrict_closure_interior_uniformWeightLower
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω]
    (μ : Measure Ω) [MeasureTheory.IsFiniteMeasure μ]
    [Measure.IsOpenPosMeasure μ] {cell : Set Ω}
    (hcell : MeasurableSet cell)
    (weight : Ω → ℝ) (kernel : ℕ → Ω → ℝ) (phi : Ω → ℝ)
    {rate W c : ℝ}
    (hkernel_int :
      ∀ k : ℕ, MeasureTheory.Integrable
        (fun x : Ω => weight x * kernel k x) (μ.restrict cell))
    (hweight_int : MeasureTheory.Integrable weight (μ.restrict cell))
    (hWpos : 0 < W)
    (hcpos : 0 < c)
    (hweight_lower : ∀ᵐ x ∂μ.restrict cell, c ≤ weight x)
    (hweight_bound : ∀ᵐ x ∂μ.restrict cell, weight x ≤ W)
    (x0 : Ω)
    (hmin : ∀ x : Ω, x ∈ cell → rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hcont : ContinuousAt phi x0)
    (hclosure : x0 ∈ closure (interior cell))
    (hkernel_pos : ∀ k x, 0 < kernel k x)
    (huniform_log : ∀ ε > 0,
      ∀ᶠ k : ℕ in Filter.atTop,
        ∀ x : Ω, |(-Real.log (kernel k x) / (k : ℝ)) - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun k : ℕ => ∫ x, weight x * kernel k x ∂μ.restrict cell)
      rate :=
  GJ19OptimalBinaryRatingSystems.theoremC1_weighted_positive_kernel_exponentialRateCertificate_of_uniform_logRate_tendsto_restrict_closure_interior_uniformWeightLower
    μ hcell weight kernel phi hkernel_int hweight_int hWpos hcpos
    hweight_lower hweight_bound x0 hmin hx0 hcont hclosure hkernel_pos
    huniform_log

/--
Restricted-cell positive-kernel Theorem C.1 certificate with a local
positive-weight minimizer and closure/interior support.
-/
theorem paper_theoremC1_weighted_positive_kernel_exponentialRateCertificate_of_uniform_logRate_tendsto_restrict_closure_interior_weight_pos
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω]
    (μ : Measure Ω) [MeasureTheory.IsFiniteMeasure μ]
    [Measure.IsOpenPosMeasure μ] {cell : Set Ω}
    (hcell : MeasurableSet cell)
    (weight : Ω → ℝ) (kernel : ℕ → Ω → ℝ) (phi : Ω → ℝ)
    {rate W : ℝ}
    (hkernel_int :
      ∀ k : ℕ, MeasureTheory.Integrable
        (fun x : Ω => weight x * kernel k x) (μ.restrict cell))
    (hweight_int : MeasureTheory.Integrable weight (μ.restrict cell))
    (hWpos : 0 < W)
    (hweight_nonneg : ∀ᵐ x ∂μ.restrict cell, 0 ≤ weight x)
    (hweight_bound : ∀ᵐ x ∂μ.restrict cell, weight x ≤ W)
    (x0 : Ω)
    (hmin : ∀ x : Ω, x ∈ cell → rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hphi_cont : ContinuousAt phi x0)
    (hweight_cont : ContinuousAt weight x0)
    (hweight_x0_pos : 0 < weight x0)
    (hclosure : x0 ∈ closure (interior cell))
    (hkernel_pos : ∀ k x, 0 < kernel k x)
    (huniform_log : ∀ ε > 0,
      ∀ᶠ k : ℕ in Filter.atTop,
        ∀ x : Ω, |(-Real.log (kernel k x) / (k : ℝ)) - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun k : ℕ => ∫ x, weight x * kernel k x ∂μ.restrict cell)
      rate :=
  GJ19OptimalBinaryRatingSystems.theoremC1_weighted_positive_kernel_exponentialRateCertificate_of_uniform_logRate_tendsto_restrict_closure_interior_weight_pos
    μ hcell weight kernel phi hkernel_int hweight_int hWpos hweight_nonneg
    hweight_bound x0 hmin hx0 hphi_cont hweight_cont hweight_x0_pos hclosure
    hkernel_pos huniform_log

/--
Restricted-cell positive-kernel Theorem C.1 certificate with a local
positive-weight minimizer and closure/interior support, requiring
normalized-log convergence only on the restricted cell.
-/
theorem paper_theoremC1_weighted_positive_kernel_exponentialRateCertificate_of_uniform_logRate_tendsto_on_restrict_closure_interior_weight_pos
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω]
    (μ : Measure Ω) [MeasureTheory.IsFiniteMeasure μ]
    [Measure.IsOpenPosMeasure μ] {cell : Set Ω}
    (hcell : MeasurableSet cell)
    (weight : Ω → ℝ) (kernel : ℕ → Ω → ℝ) (phi : Ω → ℝ)
    {rate W : ℝ}
    (hkernel_int :
      ∀ k : ℕ, MeasureTheory.Integrable
        (fun x : Ω => weight x * kernel k x) (μ.restrict cell))
    (hweight_int : MeasureTheory.Integrable weight (μ.restrict cell))
    (hWpos : 0 < W)
    (hweight_nonneg : ∀ᵐ x ∂μ.restrict cell, 0 ≤ weight x)
    (hweight_bound : ∀ᵐ x ∂μ.restrict cell, weight x ≤ W)
    (x0 : Ω)
    (hmin : ∀ x : Ω, x ∈ cell → rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hphi_cont : ContinuousAt phi x0)
    (hweight_cont : ContinuousAt weight x0)
    (hweight_x0_pos : 0 < weight x0)
    (hclosure : x0 ∈ closure (interior cell))
    (hkernel_pos : ∀ k x, 0 < kernel k x)
    (huniform_log_on : ∀ ε > 0,
      ∀ᶠ k : ℕ in Filter.atTop,
        ∀ x : Ω, x ∈ cell →
          |(-Real.log (kernel k x) / (k : ℝ)) - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun k : ℕ => ∫ x, weight x * kernel k x ∂μ.restrict cell)
      rate :=
  GJ19OptimalBinaryRatingSystems.theoremC1_weighted_positive_kernel_exponentialRateCertificate_of_uniform_logRate_tendsto_on_restrict_closure_interior_weight_pos
    μ hcell weight kernel phi hkernel_int hweight_int hWpos hweight_nonneg
    hweight_bound x0 hmin hx0 hphi_cont hweight_cont hweight_x0_pos hclosure
    hkernel_pos huniform_log_on

/--
Weighted Theorem C.1 certificate in the source shape `exp (-k * phiSeq k x)`:
uniform convergence to a continuous limiting rate with a global minimizer gives
the weighted integral exponent.
-/
theorem paper_theoremC1_weighted_laplace_exponentialRateCertificate_of_uniform_tendsto_continuous_min_uniformWeightLower
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω]
    (μ : Measure Ω) [MeasureTheory.IsFiniteMeasure μ]
    [Measure.IsOpenPosMeasure μ]
    (weight : Ω → ℝ) (phiSeq : ℕ → Ω → ℝ) (phi : Ω → ℝ)
    {rate W c : ℝ}
    (hintegrable :
      ∀ k : ℕ, MeasureTheory.Integrable
        (fun x : Ω => weight x * Real.exp (-(k : ℝ) * (phiSeq k x))) μ)
    (hWpos : 0 < W)
    (hcpos : 0 < c)
    (hweight_lower : ∀ᵐ x ∂μ, c ≤ weight x)
    (hweight_bound : ∀ᵐ x ∂μ, weight x ≤ W)
    (x0 : Ω)
    (hmin : ∀ x : Ω, rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hcont : ContinuousAt phi x0)
    (huniform : ∀ ε > 0,
      ∀ᶠ k : ℕ in Filter.atTop,
        ∀ x : Ω, |phiSeq k x - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun k : ℕ =>
        ∫ x, weight x * Real.exp (-(k : ℝ) * (phiSeq k x)) ∂μ)
      rate :=
  GJ19OptimalBinaryRatingSystems.theoremC1_weighted_laplace_exponentialRateCertificate_of_uniform_tendsto_continuous_min_uniformWeightLower
    μ weight phiSeq phi hintegrable hWpos hcpos hweight_lower
    hweight_bound x0 hmin hx0 hcont huniform

/--
Weighted Theorem C.1 certificate in the source shape with a local
positive-weight minimizer instead of a global positive lower bound.
-/
theorem paper_theoremC1_weighted_laplace_exponentialRateCertificate_of_uniform_tendsto_continuous_min_weight_pos
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω]
    (μ : Measure Ω) [MeasureTheory.IsFiniteMeasure μ]
    [Measure.IsOpenPosMeasure μ]
    (weight : Ω → ℝ) (phiSeq : ℕ → Ω → ℝ) (phi : Ω → ℝ)
    {rate W : ℝ}
    (hintegrable :
      ∀ k : ℕ, MeasureTheory.Integrable
        (fun x : Ω => weight x * Real.exp (-(k : ℝ) * (phiSeq k x))) μ)
    (hWpos : 0 < W)
    (hweight_nonneg : ∀ᵐ x ∂μ, 0 ≤ weight x)
    (hweight_bound : ∀ᵐ x ∂μ, weight x ≤ W)
    (x0 : Ω)
    (hmin : ∀ x : Ω, rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hphi_cont : ContinuousAt phi x0)
    (hweight_cont : ContinuousAt weight x0)
    (hweight_x0_pos : 0 < weight x0)
    (huniform : ∀ ε > 0,
      ∀ᶠ k : ℕ in Filter.atTop,
        ∀ x : Ω, |phiSeq k x - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun k : ℕ =>
        ∫ x, weight x * Real.exp (-(k : ℝ) * (phiSeq k x)) ∂μ)
      rate :=
  GJ19OptimalBinaryRatingSystems.theoremC1_weighted_laplace_exponentialRateCertificate_of_uniform_tendsto_continuous_min_weight_pos
    μ weight phiSeq phi hintegrable hWpos hweight_nonneg hweight_bound
    x0 hmin hx0 hphi_cont hweight_cont hweight_x0_pos huniform

/--
Restricted-cell weighted Theorem C.1 source-shape certificate, using an
explicit positive-mass condition around the cell minimizer.
-/
theorem paper_theoremC1_weighted_laplace_exponentialRateCertificate_of_uniform_tendsto_restrict_continuous_min_uniformWeightLower
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω]
    (μ : Measure Ω) [MeasureTheory.IsFiniteMeasure μ] {cell : Set Ω}
    (hcell : MeasurableSet cell)
    (weight : Ω → ℝ) (phiSeq : ℕ → Ω → ℝ) (phi : Ω → ℝ)
    {rate W c : ℝ}
    (hintegrable :
      ∀ k : ℕ,
        MeasureTheory.Integrable
          (fun x : Ω => weight x * Real.exp (-(k : ℝ) * (phiSeq k x)))
          (μ.restrict cell))
    (hWpos : 0 < W)
    (hcpos : 0 < c)
    (hweight_lower : ∀ᵐ x ∂μ.restrict cell, c ≤ weight x)
    (hweight_bound : ∀ᵐ x ∂μ.restrict cell, weight x ≤ W)
    (x0 : Ω)
    (hmin : ∀ x : Ω, x ∈ cell → rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hcont : ContinuousAt phi x0)
    (hlocal_pos :
      ∀ U : Set Ω, IsOpen U → x0 ∈ U → 0 < μ (cell ∩ U))
    (huniform : ∀ ε > 0,
      ∀ᶠ k : ℕ in Filter.atTop,
        ∀ x : Ω, |phiSeq k x - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun k : ℕ =>
        ∫ x, weight x * Real.exp (-(k : ℝ) * (phiSeq k x)) ∂μ.restrict cell)
      rate :=
  GJ19OptimalBinaryRatingSystems.theoremC1_weighted_laplace_exponentialRateCertificate_of_uniform_tendsto_restrict_continuous_min_uniformWeightLower
    μ hcell weight phiSeq phi hintegrable hWpos hcpos hweight_lower
    hweight_bound x0 hmin hx0 hcont hlocal_pos huniform

/--
Restricted-cell weighted Theorem C.1 source-shape certificate with a local
positive-weight minimizer instead of a cell-wide positive lower bound.
-/
theorem paper_theoremC1_weighted_laplace_exponentialRateCertificate_of_uniform_tendsto_restrict_continuous_min_weight_pos
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω]
    (μ : Measure Ω) [MeasureTheory.IsFiniteMeasure μ] {cell : Set Ω}
    (hcell : MeasurableSet cell)
    (weight : Ω → ℝ) (phiSeq : ℕ → Ω → ℝ) (phi : Ω → ℝ)
    {rate W : ℝ}
    (hintegrable :
      ∀ k : ℕ,
        MeasureTheory.Integrable
          (fun x : Ω => weight x * Real.exp (-(k : ℝ) * (phiSeq k x)))
          (μ.restrict cell))
    (hWpos : 0 < W)
    (hweight_nonneg : ∀ᵐ x ∂μ.restrict cell, 0 ≤ weight x)
    (hweight_bound : ∀ᵐ x ∂μ.restrict cell, weight x ≤ W)
    (x0 : Ω)
    (hmin : ∀ x : Ω, x ∈ cell → rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hphi_cont : ContinuousAt phi x0)
    (hweight_cont : ContinuousAt weight x0)
    (hweight_x0_pos : 0 < weight x0)
    (hlocal_pos :
      ∀ U : Set Ω, IsOpen U → x0 ∈ U → 0 < μ (cell ∩ U))
    (huniform : ∀ ε > 0,
      ∀ᶠ k : ℕ in Filter.atTop,
        ∀ x : Ω, |phiSeq k x - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun k : ℕ =>
        ∫ x, weight x * Real.exp (-(k : ℝ) * (phiSeq k x)) ∂μ.restrict cell)
      rate :=
  GJ19OptimalBinaryRatingSystems.theoremC1_weighted_laplace_exponentialRateCertificate_of_uniform_tendsto_restrict_continuous_min_weight_pos
    μ hcell weight phiSeq phi hintegrable hWpos hweight_nonneg
    hweight_bound x0 hmin hx0 hphi_cont hweight_cont hweight_x0_pos
    hlocal_pos huniform

/--
Restricted-cell weighted Theorem C.1 source-shape certificate where local
positive mass follows from closure/interior support.
-/
theorem paper_theoremC1_weighted_laplace_exponentialRateCertificate_of_uniform_tendsto_restrict_closure_interior_uniformWeightLower
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω]
    (μ : Measure Ω) [MeasureTheory.IsFiniteMeasure μ]
    [Measure.IsOpenPosMeasure μ] {cell : Set Ω}
    (hcell : MeasurableSet cell)
    (weight : Ω → ℝ) (phiSeq : ℕ → Ω → ℝ) (phi : Ω → ℝ)
    {rate W c : ℝ}
    (hintegrable :
      ∀ k : ℕ,
        MeasureTheory.Integrable
          (fun x : Ω => weight x * Real.exp (-(k : ℝ) * (phiSeq k x)))
          (μ.restrict cell))
    (hWpos : 0 < W)
    (hcpos : 0 < c)
    (hweight_lower : ∀ᵐ x ∂μ.restrict cell, c ≤ weight x)
    (hweight_bound : ∀ᵐ x ∂μ.restrict cell, weight x ≤ W)
    (x0 : Ω)
    (hmin : ∀ x : Ω, x ∈ cell → rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hcont : ContinuousAt phi x0)
    (hclosure : x0 ∈ closure (interior cell))
    (huniform : ∀ ε > 0,
      ∀ᶠ k : ℕ in Filter.atTop,
        ∀ x : Ω, |phiSeq k x - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun k : ℕ =>
        ∫ x, weight x * Real.exp (-(k : ℝ) * (phiSeq k x)) ∂μ.restrict cell)
      rate :=
  GJ19OptimalBinaryRatingSystems.theoremC1_weighted_laplace_exponentialRateCertificate_of_uniform_tendsto_restrict_closure_interior_uniformWeightLower
    μ hcell weight phiSeq phi hintegrable hWpos hcpos hweight_lower
    hweight_bound x0 hmin hx0 hcont hclosure huniform

/--
Restricted-cell weighted Theorem C.1 source-shape certificate with a local
positive-weight minimizer and closure/interior support.
-/
theorem paper_theoremC1_weighted_laplace_exponentialRateCertificate_of_uniform_tendsto_restrict_closure_interior_weight_pos
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω]
    (μ : Measure Ω) [MeasureTheory.IsFiniteMeasure μ]
    [Measure.IsOpenPosMeasure μ] {cell : Set Ω}
    (hcell : MeasurableSet cell)
    (weight : Ω → ℝ) (phiSeq : ℕ → Ω → ℝ) (phi : Ω → ℝ)
    {rate W : ℝ}
    (hintegrable :
      ∀ k : ℕ,
        MeasureTheory.Integrable
          (fun x : Ω => weight x * Real.exp (-(k : ℝ) * (phiSeq k x)))
          (μ.restrict cell))
    (hWpos : 0 < W)
    (hweight_nonneg : ∀ᵐ x ∂μ.restrict cell, 0 ≤ weight x)
    (hweight_bound : ∀ᵐ x ∂μ.restrict cell, weight x ≤ W)
    (x0 : Ω)
    (hmin : ∀ x : Ω, x ∈ cell → rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hphi_cont : ContinuousAt phi x0)
    (hweight_cont : ContinuousAt weight x0)
    (hweight_x0_pos : 0 < weight x0)
    (hclosure : x0 ∈ closure (interior cell))
    (huniform : ∀ ε > 0,
      ∀ᶠ k : ℕ in Filter.atTop,
        ∀ x : Ω, |phiSeq k x - phi x| ≤ ε) :
    ExponentialRateCertificate
      (fun k : ℕ =>
        ∫ x, weight x * Real.exp (-(k : ℝ) * (phiSeq k x)) ∂μ.restrict cell)
      rate :=
  GJ19OptimalBinaryRatingSystems.theoremC1_weighted_laplace_exponentialRateCertificate_of_uniform_tendsto_restrict_closure_interior_weight_pos
    μ hcell weight phiSeq phi hintegrable hWpos hweight_nonneg hweight_bound
    x0 hmin hx0 hphi_cont hweight_cont hweight_x0_pos hclosure huniform

/--
Restricted-cell weighted Theorem C.1 certificate with uniform convergence
required only on the restricted cell.
-/
abbrev paper_theoremC1_weighted_laplace_exponentialRateCertificate_of_uniform_tendsto_on_restrict_continuous_min_uniformWeightLower :=
  @GJ19OptimalBinaryRatingSystems.theoremC1_weighted_laplace_exponentialRateCertificate_of_uniform_tendsto_on_restrict_continuous_min_uniformWeightLower

/--
Restricted-cell weighted Theorem C.1 certificate with local positive weight
and uniform convergence required only on the restricted cell.
-/
abbrev paper_theoremC1_weighted_laplace_exponentialRateCertificate_of_uniform_tendsto_on_restrict_continuous_min_weight_pos :=
  @GJ19OptimalBinaryRatingSystems.theoremC1_weighted_laplace_exponentialRateCertificate_of_uniform_tendsto_on_restrict_continuous_min_weight_pos

/--
Restricted-cell weighted Theorem C.1 certificate with closure/interior support
and uniform convergence required only on the restricted cell.
-/
abbrev paper_theoremC1_weighted_laplace_exponentialRateCertificate_of_uniform_tendsto_on_restrict_closure_interior_uniformWeightLower :=
  @GJ19OptimalBinaryRatingSystems.theoremC1_weighted_laplace_exponentialRateCertificate_of_uniform_tendsto_on_restrict_closure_interior_uniformWeightLower

/--
Restricted-cell weighted Theorem C.1 certificate with local positive weight,
closure/interior support, and uniform convergence required only on the
restricted cell.
-/
abbrev paper_theoremC1_weighted_laplace_exponentialRateCertificate_of_uniform_tendsto_on_restrict_closure_interior_weight_pos :=
  @GJ19OptimalBinaryRatingSystems.theoremC1_weighted_laplace_exponentialRateCertificate_of_uniform_tendsto_on_restrict_closure_interior_weight_pos

/--
Exact-exponential Theorem C.1 certificate with source-style continuous-minimizer
assumptions.  This is the common `exp (-k * phi x)` specialization of the
weighted Laplace principle.
-/
theorem paper_theoremC1_weighted_exact_exponential_exponentialRateCertificate_of_continuous_min_uniformWeightLower
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω]
    (μ : Measure Ω) [MeasureTheory.IsFiniteMeasure μ]
    [Measure.IsOpenPosMeasure μ]
    (weight : Ω → ℝ) (phi : Ω → ℝ) {rate W c : ℝ}
    (hintegrable :
      ∀ k : ℕ, MeasureTheory.Integrable
        (fun x : Ω => weight x * Real.exp (-(k : ℝ) * phi x)) μ)
    (hweight_int : MeasureTheory.Integrable weight μ)
    (hWpos : 0 < W)
    (hcpos : 0 < c)
    (hweight_lower : ∀ᵐ x ∂μ, c ≤ weight x)
    (hweight_bound : ∀ᵐ x ∂μ, weight x ≤ W)
    (x0 : Ω)
    (hmin : ∀ x : Ω, rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hcont : ContinuousAt phi x0) :
    ExponentialRateCertificate
      (fun k : ℕ => ∫ x, weight x * Real.exp (-(k : ℝ) * phi x) ∂μ)
      rate :=
  GJ19OptimalBinaryRatingSystems.theoremC1_weighted_exact_exponential_exponentialRateCertificate_of_continuous_min_uniformWeightLower
    μ weight phi hintegrable hweight_int hWpos hcpos hweight_lower
    hweight_bound x0 hmin hx0 hcont

/--
Restricted-cell exact-exponential Theorem C.1 certificate with source-style
continuous-minimizer assumptions and an explicit local positive-mass condition.
-/
theorem paper_theoremC1_weighted_exact_exponential_exponentialRateCertificate_of_restrict_continuous_min_uniformWeightLower
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω]
    (μ : Measure Ω) [MeasureTheory.IsFiniteMeasure μ] {cell : Set Ω}
    (hcell : MeasurableSet cell)
    (weight : Ω → ℝ) (phi : Ω → ℝ) {rate W c : ℝ}
    (hintegrable :
      ∀ k : ℕ,
        MeasureTheory.Integrable
          (fun x : Ω => weight x * Real.exp (-(k : ℝ) * phi x))
          (μ.restrict cell))
    (hweight_int : MeasureTheory.Integrable weight (μ.restrict cell))
    (hWpos : 0 < W)
    (hcpos : 0 < c)
    (hweight_lower : ∀ᵐ x ∂μ.restrict cell, c ≤ weight x)
    (hweight_bound : ∀ᵐ x ∂μ.restrict cell, weight x ≤ W)
    (x0 : Ω)
    (hmin : ∀ x : Ω, x ∈ cell → rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hcont : ContinuousAt phi x0)
    (hlocal_pos :
      ∀ U : Set Ω, IsOpen U → x0 ∈ U → 0 < μ (cell ∩ U)) :
    ExponentialRateCertificate
      (fun k : ℕ =>
        ∫ x, weight x * Real.exp (-(k : ℝ) * phi x) ∂μ.restrict cell)
      rate :=
  GJ19OptimalBinaryRatingSystems.theoremC1_weighted_exact_exponential_exponentialRateCertificate_of_restrict_continuous_min_uniformWeightLower
    μ hcell weight phi hintegrable hweight_int hWpos hcpos hweight_lower
    hweight_bound x0 hmin hx0 hcont hlocal_pos

/--
Restricted-cell exact-exponential Theorem C.1 certificate where the minimizer
lies in the closure of the interval-cell interior.
-/
theorem paper_theoremC1_weighted_exact_exponential_exponentialRateCertificate_of_restrict_closure_interior_uniformWeightLower
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω]
    (μ : Measure Ω) [MeasureTheory.IsFiniteMeasure μ]
    [Measure.IsOpenPosMeasure μ] {cell : Set Ω}
    (hcell : MeasurableSet cell)
    (weight : Ω → ℝ) (phi : Ω → ℝ) {rate W c : ℝ}
    (hintegrable :
      ∀ k : ℕ,
        MeasureTheory.Integrable
          (fun x : Ω => weight x * Real.exp (-(k : ℝ) * phi x))
          (μ.restrict cell))
    (hweight_int : MeasureTheory.Integrable weight (μ.restrict cell))
    (hWpos : 0 < W)
    (hcpos : 0 < c)
    (hweight_lower : ∀ᵐ x ∂μ.restrict cell, c ≤ weight x)
    (hweight_bound : ∀ᵐ x ∂μ.restrict cell, weight x ≤ W)
    (x0 : Ω)
    (hmin : ∀ x : Ω, x ∈ cell → rate ≤ phi x)
    (hx0 : phi x0 = rate)
    (hcont : ContinuousAt phi x0)
    (hclosure : x0 ∈ closure (interior cell)) :
    ExponentialRateCertificate
      (fun k : ℕ =>
        ∫ x, weight x * Real.exp (-(k : ℝ) * phi x) ∂μ.restrict cell)
      rate :=
  GJ19OptimalBinaryRatingSystems.theoremC1_weighted_exact_exponential_exponentialRateCertificate_of_restrict_closure_interior_uniformWeightLower
    μ hcell weight phi hintegrable hweight_int hWpos hcpos hweight_lower
    hweight_bound x0 hmin hx0 hcont hclosure

/--
Weighted Theorem C.1 convenience wrapper for uniformly positive objective
weights: if the weight is bounded above and below by positive constants almost
everywhere, the weighted integral has the same exponential rate.
-/
theorem paper_theoremC1_weighted_laplace_integral_exponential_rate_of_uniform_tendsto_uniformWeightLower
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [MeasureTheory.IsFiniteMeasure μ]
    (weight : Ω → ℝ) (phiSeq : ℕ → Ω → ℝ) (phi : Ω → ℝ)
    {rate W c : ℝ}
    (hintegrable :
      ∀ k : ℕ, MeasureTheory.Integrable
        (fun x : Ω => weight x * Real.exp (-(k : ℝ) * (phiSeq k x))) μ)
    (hWpos : 0 < W)
    (hcpos : 0 < c)
    (hweight_lower : ∀ᵐ x ∂μ, c ≤ weight x)
    (hweight_bound : ∀ᵐ x ∂μ, weight x ≤ W)
    (hess : HasAEEssentialInfimum μ phi rate)
    (huniform : ∀ ε > 0,
      ∀ᶠ k : ℕ in Filter.atTop,
        ∀ x : Ω, |phiSeq k x - phi x| ≤ ε) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x, weight x * Real.exp (-(k : ℝ) * (phiSeq k x)) ∂μ)
      rate :=
  GJ19OptimalBinaryRatingSystems.theoremC1_weighted_laplace_integral_exponential_rate_of_uniform_tendsto_uniformWeightLower
    μ weight phiSeq phi hintegrable hWpos hcpos hweight_lower
    hweight_bound hess huniform

/--
Lemma C.3 finite-decomposition algebra: if the piecewise-constant objective is
split into finitely many interval-pair error components and each component has
an exact exponential-rate certificate, then the weighted finite sum decays at
the minimum component rate.
-/
theorem paper_lemmaC3_finite_component_weighted_error_sum_hasExponentialRate_of_min_component
    {Component : Type*} [Fintype Component] [DecidableEq Component]
    (componentError : Component → ℕ → ℝ)
    (weight rate : Component → ℝ)
    (hweight_nonneg : ∀ cpt : Component, 0 ≤ weight cpt)
    (hcert :
      ∀ cpt : Component,
        ExponentialRateCertificate (componentError cpt) (rate cpt))
    (minComponent : Component)
    (hweight_pos : 0 < weight minComponent)
    (hrate_ge :
      ∀ cpt : Component, rate minComponent ≤ rate cpt) :
    HasExponentialRate
      (fun k : ℕ => ∑ cpt : Component, weight cpt * componentError cpt k)
      (rate minComponent) :=
  GJ19OptimalBinaryRatingSystems.lemmaC3_finite_component_weighted_error_sum_hasExponentialRate_of_min_component
    componentError weight rate hweight_nonneg hcert minComponent
    hweight_pos hrate_ge

/--
Lemma C.3 adjacent-dominance algebra: if the adjacent interval-pair subfamily
dominates all component rates, the decomposed finite sum decays at the minimum
adjacent exponent.
-/
theorem paper_lemmaC3_finite_component_weighted_error_sum_hasExponentialRate_of_dominating_adjacent_subfamily
    {Component Adjacent : Type*} [Fintype Component] [DecidableEq Component]
    (componentError : Component → ℕ → ℝ)
    (weight rate : Component → ℝ)
    (selectAdjacent : Adjacent → Component)
    (hweight_nonneg : ∀ cpt : Component, 0 ≤ weight cpt)
    (hcert :
      ∀ cpt : Component,
        ExponentialRateCertificate (componentError cpt) (rate cpt))
    (minAdjacent : Adjacent)
    (hweight_pos : 0 < weight (selectAdjacent minAdjacent))
    (hadj_min :
      ∀ adj : Adjacent,
        rate (selectAdjacent minAdjacent) ≤ rate (selectAdjacent adj))
    (hadj_dominates :
      ∀ cpt : Component,
        ∃ adj : Adjacent, rate (selectAdjacent adj) ≤ rate cpt) :
    HasExponentialRate
      (fun k : ℕ => ∑ cpt : Component, weight cpt * componentError cpt k)
      (rate (selectAdjacent minAdjacent)) :=
  GJ19OptimalBinaryRatingSystems.lemmaC3_finite_component_weighted_error_sum_hasExponentialRate_of_dominating_adjacent_subfamily
    componentError weight rate selectAdjacent hweight_nonneg hcert
    minAdjacent hweight_pos hadj_min hadj_dominates

/--
Theorem 3.1 adjacent-dominance algebra: with fixed sample weights, an adjacent
success-probability subinterval has no larger Bernoulli error exponent than
the wider interval containing it.
-/
theorem paper_theorem31_nested_binary_closed_rate_le
    {gHi gLo pHi pLo pHiAdjacent pLoAdjacent : ℝ}
    (hgHi : 0 ≤ gHi) (hgLo : 0 ≤ gLo) (hGpos : 0 < gHi + gLo)
    (hpLo0 : 0 < pLo)
    (hpLo_le_adjLo : pLo ≤ pLoAdjacent)
    (hadjLo_le_adjHi : pLoAdjacent ≤ pHiAdjacent)
    (hadjHi_le_pHi : pHiAdjacent ≤ pHi)
    (hpHi1 : pHi < 1) :
    weightedBernoulliClosedThresholdRate gHi gLo pHiAdjacent pLoAdjacent ≤
      weightedBernoulliClosedThresholdRate gHi gLo pHi pLo :=
  GJ19OptimalBinaryRatingSystems.theorem31_nested_binary_closed_rate_le
    hgHi hgLo hGpos hpLo0 hpLo_le_adjLo hadjLo_le_adjHi
    hadjHi_le_pHi hpHi1

/--
Theorem 3.1 / Lemma C.3 adjacent-dominance step: for monotone matching-rate
lower bounds and monotone binary levels, every wider same-low comparison is
dominated by the adjacent comparison.
-/
theorem paper_theorem31_monotone_chain_adjacent_rate_le_nonadjacent_rate
    {sampleRate successProb : ℕ → ℝ} {i j : ℕ}
    (hsample_pos : ∀ n, 0 < sampleRate n)
    (hsample_mono : Monotone sampleRate)
    (hprob_mono : Monotone successProb)
    (hprob_i_pos : 0 < successProb i)
    (hprob_j_lt_one : successProb j < 1)
    (hij : i + 1 ≤ j) :
    weightedBernoulliClosedThresholdRate (sampleRate (i + 1)) (sampleRate i)
        (successProb (i + 1)) (successProb i) ≤
      weightedBernoulliClosedThresholdRate (sampleRate j) (sampleRate i)
        (successProb j) (successProb i) :=
  GJ19OptimalBinaryRatingSystems.theorem31_monotone_chain_adjacent_rate_le_nonadjacent_rate
    hsample_pos hsample_mono hprob_mono hprob_i_pos hprob_j_lt_one hij

/--
Theorem 3.1 / Lemma C.3 finite-chain adjacent-dominance witness: every
interior ordered pair is dominated by the adjacent pair beginning at the same
lower endpoint.
-/
theorem paper_theorem31_monotone_finite_chain_adjacent_witness_dominates_ordered_pair
    {m : ℕ}
    (sampleRate successProb : Fin (m + 2) → ℝ)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (low high : Fin (m + 2))
    (hordered : low.val + 1 ≤ high.val)
    (hprob_low_pos : 0 < successProb low)
    (hprob_high_lt_one : successProb high < 1) :
    ∃ adj : Fin (m + 1),
      weightedBernoulliClosedThresholdRate
          (sampleRate (adjacentHighIndex adj))
          (sampleRate (adjacentLowIndex adj))
          (successProb (adjacentHighIndex adj))
          (successProb (adjacentLowIndex adj)) ≤
        weightedBernoulliClosedThresholdRate
          (sampleRate high) (sampleRate low)
          (successProb high) (successProb low) :=
  GJ19OptimalBinaryRatingSystems.theorem31_monotone_finite_chain_adjacent_witness_dominates_ordered_pair
    sampleRate successProb hsample_pos hsample_mono hprob_mono low high
    hordered hprob_low_pos hprob_high_lt_one

/--
Theorem 3.1 / Lemma C.3 low-endpoint adjacent-dominance step: the first
adjacent endpoint comparison dominates wider comparisons starting at the
source endpoint.
-/
theorem paper_theorem31_first_endpoint_adjacent_rate_le_nonadjacent_endpoint_rate
    {m : ℕ}
    (sampleRate successProb : Fin (m + 2) → ℝ)
    (hsample_nonneg : ∀ idx, 0 ≤ sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_first_nonneg :
      0 ≤ successProb (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))))
    (high : Fin (m + 2))
    (hhigh : 1 ≤ high.val)
    (hprob_high_lt_one : successProb high < 1) :
    sampleRate (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) *
        (-Real.log
          (1 - successProb
            (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))))) ≤
      sampleRate high * (-Real.log (1 - successProb high)) :=
  GJ19OptimalBinaryRatingSystems.theorem31_first_endpoint_adjacent_rate_le_nonadjacent_endpoint_rate
    sampleRate successProb hsample_nonneg hsample_mono hprob_mono
    hprob_first_nonneg high hhigh hprob_high_lt_one

/--
Theorem 3.1 / Lemma C.3 top-endpoint adjacent-dominance witness: a wider
comparison ending at the source endpoint `1` is dominated by a finite adjacent
comparison, using the endpoint success exponent for the lower level.
-/
theorem paper_theorem31_top_endpoint_adjacent_witness_dominates_nonadjacent_endpoint_rate
    {m : ℕ}
    (sampleRate successProb : Fin (m + 2) → ℝ)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_not_last_lt_one :
      ∀ idx : Fin (m + 2), idx.val < m + 1 → successProb idx < 1)
    (low : Fin (m + 2))
    (hlow_pos : 0 < low.val)
    (hlow_le_last_adjacent : low.val ≤ m)
    (hprob_low_pos : 0 < successProb low) :
    ∃ adj : Fin (m + 1),
      binaryEndpointAwareAdjacentRate successProb sampleRate adj ≤
        sampleRate low * (-Real.log (successProb low)) :=
  GJ19OptimalBinaryRatingSystems.theorem31_top_endpoint_adjacent_witness_dominates_nonadjacent_endpoint_rate
    sampleRate successProb hsample_pos hprob_mono hprob_not_last_lt_one
    low hlow_pos hlow_le_last_adjacent hprob_low_pos

/--
Theorem 3.1 / Lemma C.3 endpoint-aware adjacent-dominance package: every wider
finite real-rate ordered pair, except the pure bottom-to-top source-endpoint
case, is dominated by an adjacent endpoint-aware comparison.
-/
theorem paper_theorem31_endpoint_aware_adjacent_witness_dominates_ordered_pair
    {m : ℕ}
    (sampleRate successProb : Fin (m + 2) → ℝ)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_nonneg : ∀ idx, 0 ≤ successProb idx)
    (hprob_pos_of_not_first :
      ∀ idx : Fin (m + 2), idx.val ≠ 0 → 0 < successProb idx)
    (hprob_lt_one_of_not_last :
      ∀ idx : Fin (m + 2), idx.val ≠ m + 1 → successProb idx < 1)
    (low high : Fin (m + 2))
    (hordered : low.val + 1 ≤ high.val)
    (hnot_bottom_to_top : low.val ≠ 0 ∨ high.val ≠ m + 1) :
    ∃ adj : Fin (m + 1),
      binaryEndpointAwareAdjacentRate successProb sampleRate adj ≤
        binaryEndpointAwarePairRate successProb sampleRate low high :=
  GJ19OptimalBinaryRatingSystems.theorem31_endpoint_aware_adjacent_witness_dominates_ordered_pair
    sampleRate successProb hsample_pos hsample_mono hprob_mono hprob_nonneg
    hprob_pos_of_not_first hprob_lt_one_of_not_last low high hordered
    hnot_bottom_to_top

/-- Theorem 3.1/C.3 selected nontrivial ordered-pair predicate. -/
abbrev paperTheorem31OrderedNontrivialPairSelected {m : ℕ}
    (piece : Fin (m + 2) × Fin (m + 2)) : Prop :=
  theorem31OrderedNontrivialPairSelected (m := m) piece

/-- Theorem 3.1/C.3 subtype of selected nontrivial ordered-pair components. -/
abbrev paperTheorem31OrderedNontrivialPairComponent (m : ℕ) :=
  theorem31OrderedNontrivialPairComponent m

/-- Adjacent selected component used by the endpoint-aware C.3 bridge. -/
abbrev paperTheorem31OrderedAdjacentPiece {m : ℕ} (hm : 0 < m)
    (adj : Fin (m + 1)) :
    paperTheorem31OrderedNontrivialPairComponent m :=
  theorem31OrderedAdjacentPiece hm adj

/-- Adjacent pair-rate and adjacent-rate conventions agree. -/
theorem paper_binaryEndpointAwarePairRate_adjacent_eq_adjacentRate {m : ℕ}
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (adj : Fin (m + 1)) :
    binaryEndpointAwarePairRate successProb sampleRate
        (adjacentLowIndex adj) (adjacentHighIndex adj) =
      binaryEndpointAwareAdjacentRate successProb sampleRate adj :=
  GJ19OptimalBinaryRatingSystems.binaryEndpointAwarePairRate_adjacent_eq_adjacentRate
    successProb sampleRate adj

/--
Theorem 3.1/C.3 selected-pair adjacent-dominance package: every selected
nontrivial ordered-pair component is dominated by an adjacent comparison.
-/
theorem paper_theorem31_endpoint_aware_adjacent_witness_dominates_selected_ordered_pair
    {m : ℕ}
    (sampleRate successProb : Fin (m + 2) → ℝ)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_nonneg : ∀ idx, 0 ≤ successProb idx)
    (hprob_pos_of_not_first :
      ∀ idx : Fin (m + 2), idx.val ≠ 0 → 0 < successProb idx)
    (hprob_lt_one_of_not_last :
      ∀ idx : Fin (m + 2), idx.val ≠ m + 1 → successProb idx < 1)
    (component : paperTheorem31OrderedNontrivialPairComponent m) :
    ∃ adj : Fin (m + 1),
      binaryEndpointAwareAdjacentRate successProb sampleRate adj ≤
        binaryEndpointAwarePairRate successProb sampleRate
          component.val.1 component.val.2 :=
  GJ19OptimalBinaryRatingSystems.theorem31_endpoint_aware_adjacent_witness_dominates_selected_ordered_pair
    sampleRate successProb hsample_pos hsample_mono hprob_mono hprob_nonneg
    hprob_pos_of_not_first hprob_lt_one_of_not_last component

/--
Theorem 3.1/C.3 selected-pair adjacent-dominance package with endpoint
support and monotonicity supplied by `BinaryEndpointLevelVector`.
-/
abbrev paper_theorem31_endpoint_aware_adjacent_witness_dominates_selected_ordered_pair_of_endpointLevelVector
    {m : ℕ} :=
  GJ19OptimalBinaryRatingSystems.theorem31_endpoint_aware_adjacent_witness_dominates_selected_ordered_pair_of_endpointLevelVector
    (m := m)

/--
Theorem 3.1/C.3 selected-pair positivity bridge: every selected nontrivial
ordered-pair floor-count error kernel is eventually positive.
-/
theorem paper_binaryRatingModel_floorPkComplementErrorProb_eventually_pos_of_selected_ordered_pair
    {m : ℕ}
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hprob_pos_of_not_first :
      ∀ idx : Fin (m + 2), idx.val ≠ 0 → 0 < successProb idx)
    (hprob_lt_one_of_not_last :
      ∀ idx : Fin (m + 2), idx.val ≠ m + 1 → successProb idx < 1)
    (component : paperTheorem31OrderedNontrivialPairComponent m) :
    ∀ᶠ k : ℕ in atTop,
      0 <
        twoSampleFloorPkComplementErrorProb
          (binaryRatingModel successProb hprob0 hprob1) sampleRate
          component.val.2 component.val.1 k :=
  GJ19OptimalBinaryRatingSystems.binaryRatingModel_floorPkComplementErrorProb_eventually_pos_of_selected_ordered_pair
    successProb sampleRate hprob0 hprob1 hsample_pos
    hprob_pos_of_not_first hprob_lt_one_of_not_last component

/--
Theorem 3.1/C.3 selected-pair left-tail rate bridge: the endpoint-aware
selected-pair rate is the exact exponential rate of the finite floor-count
left-tail kernel.
-/
theorem paper_binaryEndpointAwarePairRate_leftTail_certificate_of_selected_ordered_pair
    {m : ℕ}
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hfirst_zero : successProb (firstLevelIndex : Fin (m + 2)) = 0)
    (hlast_one : successProb (lastLevelIndex : Fin (m + 2)) = 1)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_pos_of_not_first :
      ∀ θ : Fin (m + 2), θ.val ≠ 0 → 0 < successProb θ)
    (hprob_lt_one_of_not_last :
      ∀ θ : Fin (m + 2), θ.val ≠ m + 1 → successProb θ < 1)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (component : paperTheorem31OrderedNontrivialPairComponent m) :
    ExponentialRateCertificate
      (twoSampleFloorScoreGapLeftTailProb
        (binaryRatingModel successProb hprob0 hprob1) sampleRate
        component.val.2 component.val.1)
      (binaryEndpointAwarePairRate successProb sampleRate
        component.val.1 component.val.2) :=
  GJ19OptimalBinaryRatingSystems.binaryEndpointAwarePairRate_leftTail_certificate_of_selected_ordered_pair
    successProb sampleRate hprob0 hprob1 hfirst_zero hlast_one hprob_mono
    hprob_pos_of_not_first hprob_lt_one_of_not_last hsample_pos component

/--
Theorem 3.1/C.3 selected-pair complement-error rate bridge: the endpoint-aware
selected-pair rate is the exact exponential rate of the finite `1 - P_k`
floor-count kernel.
-/
theorem paper_binaryEndpointAwarePairRate_floorPkComplementError_certificate_of_selected_ordered_pair
    {m : ℕ}
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hfirst_zero : successProb (firstLevelIndex : Fin (m + 2)) = 0)
    (hlast_one : successProb (lastLevelIndex : Fin (m + 2)) = 1)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_pos_of_not_first :
      ∀ θ : Fin (m + 2), θ.val ≠ 0 → 0 < successProb θ)
    (hprob_lt_one_of_not_last :
      ∀ θ : Fin (m + 2), θ.val ≠ m + 1 → successProb θ < 1)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (component : paperTheorem31OrderedNontrivialPairComponent m) :
    ExponentialRateCertificate
      (twoSampleFloorPkComplementErrorProb
        (binaryRatingModel successProb hprob0 hprob1) sampleRate
        component.val.2 component.val.1)
      (binaryEndpointAwarePairRate successProb sampleRate
        component.val.1 component.val.2) :=
  GJ19OptimalBinaryRatingSystems.binaryEndpointAwarePairRate_floorPkComplementError_certificate_of_selected_ordered_pair
    successProb sampleRate hprob0 hprob1 hfirst_zero hlast_one hprob_mono
    hprob_pos_of_not_first hprob_lt_one_of_not_last hsample_pos component

/--
Theorem 3.1/C.3 selected-pair floor-complement exact-rate bridge using
`BinaryEndpointLevelVector` for the finite binary-model side conditions.
-/
abbrev paper_binaryEndpointAwarePairRate_floorPkComplementError_certificate_of_selected_ordered_pair_of_endpointLevelVector
    {m : ℕ} :=
  GJ19OptimalBinaryRatingSystems.binaryEndpointAwarePairRate_floorPkComplementError_certificate_of_selected_ordered_pair_of_endpointLevelVector
    (m := m)

/--
Lemma C.3 selected ordered-pair finite aggregation: once the endpoint-aware
binary-model component certificates are derived, the weighted sum of selected
ordered-pair endpoint errors decays at the minimum adjacent endpoint-aware
rate.
-/
theorem paper_lemmaC3_selected_ordered_pair_weighted_error_sum_hasExponentialRate_of_adjacent_min
    {m : ℕ} (hm : 0 < m)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hfirst_zero : successProb (firstLevelIndex : Fin (m + 2)) = 0)
    (hlast_one : successProb (lastLevelIndex : Fin (m + 2)) = 1)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_pos_of_not_first :
      ∀ θ : Fin (m + 2), θ.val ≠ 0 → 0 < successProb θ)
    (hprob_lt_one_of_not_last :
      ∀ θ : Fin (m + 2), θ.val ≠ m + 1 → successProb θ < 1)
    {weight : paperTheorem31OrderedNontrivialPairComponent m → ℝ}
    (hweight_nonneg :
      ∀ component : paperTheorem31OrderedNontrivialPairComponent m,
        0 ≤ weight component)
    (minAdjacent : Fin (m + 1))
    (hweight_pos :
      0 < weight (theorem31OrderedAdjacentPiece hm minAdjacent))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj) :
    HasExponentialRate
      (fun k : ℕ =>
        ∑ component : paperTheorem31OrderedNontrivialPairComponent m,
          weight component *
            twoSampleFloorPkComplementErrorProb
              (binaryRatingModel successProb hprob0 hprob1) sampleRate
              component.val.2 component.val.1 k)
      (binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) :=
  GJ19OptimalBinaryRatingSystems.lemmaC3_selected_ordered_pair_weighted_error_sum_hasExponentialRate_of_adjacent_min
    hm successProb sampleRate hprob0 hprob1 hfirst_zero hlast_one hsample_pos
    hsample_mono hprob_mono hprob_pos_of_not_first hprob_lt_one_of_not_last
    hweight_nonneg minAdjacent hweight_pos hadj_min

/--
Lemma C.3 selected ordered-pair finite aggregation using
`BinaryEndpointLevelVector` for the endpoint and support facts.
-/
abbrev paper_lemmaC3_selected_ordered_pair_weighted_error_sum_hasExponentialRate_of_adjacent_min_of_endpointLevelVector
    {m : ℕ} :=
  GJ19OptimalBinaryRatingSystems.lemmaC3_selected_ordered_pair_weighted_error_sum_hasExponentialRate_of_adjacent_min_of_endpointLevelVector
    (m := m)

/--
Lemma C.3 selected ordered-pair partition integral: for the endpoint-pair
source convention, the ordered-rectangle piecewise-constant kernel has the
minimum adjacent endpoint-aware exponent.
-/
theorem paper_lemmaC3_ordered_quality_endpoint_piecewiseConstKernel_integral_hasExponentialRate_of_adjacent_min
    (μ : Measure ℝ)
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hfirst_zero : successProb (firstLevelIndex : Fin (m + 2)) = 0)
    (hlast_one : successProb (lastLevelIndex : Fin (m + 2)) = 1)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_pos_of_not_first :
      ∀ θ : Fin (m + 2), θ.val ≠ 0 → 0 < successProb θ)
    (hprob_lt_one_of_not_last :
      ∀ θ : Fin (m + 2), θ.val ≠ m + 1 → successProb θ < 1)
    (weight : ℝ × ℝ → ℝ)
    (hweight_int :
      ∀ component,
        IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_nonneg :
      ∀ component,
        0 ≤
          ∫ x in
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component,
            weight x ∂(μ.prod μ))
    (minAdjacent : Fin (m + 1))
    (hweight_pos :
      0 <
        ∫ x in
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet
              (theorem31OrderedAdjacentPiece hm minAdjacent),
          weight x ∂(μ.prod μ))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (paperTheorem31OrderedNontrivialPairSelected (m := m))).support,
          weight x *
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (paperTheorem31OrderedNontrivialPairSelected (m := m))).piecewiseConstKernel
                (fun component k =>
                  twoSampleFloorPkComplementErrorProb
                    (binaryRatingModel successProb hprob0 hprob1) sampleRate
                    component.val.2 component.val.1 k)
                k x ∂(μ.prod μ))
      (binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) :=
  GJ19OptimalBinaryRatingSystems.lemmaC3_ordered_quality_endpoint_piecewiseConstKernel_integral_hasExponentialRate_of_adjacent_min
    μ hm cut hmono successProb sampleRate hprob0 hprob1 hfirst_zero hlast_one
    hsample_pos hsample_mono hprob_mono hprob_pos_of_not_first
    hprob_lt_one_of_not_last weight hweight_int hweight_nonneg minAdjacent
    hweight_pos hadj_min

/--
Lemma C.3 selected ordered-pair partition integral using
`BinaryEndpointLevelVector` for endpoint/support facts.
-/
abbrev paper_lemmaC3_ordered_quality_endpoint_piecewiseConstKernel_integral_hasExponentialRate_of_adjacent_min_of_endpointLevelVector
    {m : ℕ} :=
  GJ19OptimalBinaryRatingSystems.lemmaC3_ordered_quality_endpoint_piecewiseConstKernel_integral_hasExponentialRate_of_adjacent_min_of_endpointLevelVector
    (m := m)

/--
Lemma C.3 selected ordered-pair partition integral with local positive
objective weights.
-/
abbrev paper_lemmaC3_ordered_quality_endpoint_piecewiseConstKernel_integral_hasExponentialRate_of_adjacent_min_weight_pos :=
  GJ19OptimalBinaryRatingSystems.lemmaC3_ordered_quality_endpoint_piecewiseConstKernel_integral_hasExponentialRate_of_adjacent_min_weight_pos

/--
Lemma C.3 selected ordered-pair partition integral with local positive
objective weights, using `BinaryEndpointLevelVector` for endpoint/support facts.
-/
abbrev paper_lemmaC3_ordered_quality_endpoint_piecewiseConstKernel_integral_hasExponentialRate_of_adjacent_min_weight_pos_of_endpointLevelVector
    (μ : Measure ℝ) [MeasureTheory.IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)] {m : ℕ} :=
  GJ19OptimalBinaryRatingSystems.lemmaC3_ordered_quality_endpoint_piecewiseConstKernel_integral_hasExponentialRate_of_adjacent_min_weight_pos_of_endpointLevelVector
    μ (m := m)

/--
Lemma C.3 selected ordered-pair partition integral with canonical cell
midpoints supplying the local positive-weight witnesses.

Source status: conditional C.3 continuum aggregation bridge with canonical
cell-midpoint witnesses.
-/
abbrev paper_lemmaC3_ordered_quality_endpoint_piecewiseConstKernel_integral_hasExponentialRate_of_adjacent_min_weight_pos_of_cell_midpoints
    (μ : Measure ℝ) [MeasureTheory.IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)] {m : ℕ} :=
  GJ19OptimalBinaryRatingSystems.lemmaC3_ordered_quality_endpoint_piecewiseConstKernel_integral_hasExponentialRate_of_adjacent_min_weight_pos_of_cell_midpoints
    μ (m := m)

/--
Continuum piecewise-constant Lemma C.4 forward direction: equalized endpoint
levels give a positive exponential rate for the selected ordered-rectangle
integral.
-/
abbrev paper_lemmaC4_endpoint_piecewiseConstKernel_has_positive_exponential_rate :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_endpoint_piecewiseConstKernel_has_positive_exponential_rate

/--
Continuum piecewise-constant Lemma C.4 forward direction with success
monotonicity derived from `BinaryEndpointLevelVector`.
-/
abbrev paper_lemmaC4_endpoint_piecewiseConstKernel_has_positive_exponential_rate_of_endpointLevelVector
    (μ : Measure ℝ) [MeasureTheory.IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)] {m : ℕ} :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_endpoint_piecewiseConstKernel_has_positive_exponential_rate_of_endpointLevelVector
    μ (m := m)

/--
Lemma C.4 source-facing forward wrapper: once the source `Wbar_k` sequence is
identified with the selected ordered-rectangle error integral, the
piecewise-constant endpoint construction gives a positive exponential-rate
certificate for `Wbar_k`.
-/
abbrev paper_lemmaC4_sourceWbar_has_positive_exponential_rate_of_endpoint_piecewiseConstKernel
    (μ : Measure ℝ) [MeasureTheory.IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)] {m : ℕ} :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_sourceWbar_has_positive_exponential_rate_of_endpoint_piecewiseConstKernel
    μ (m := m)

/--
Lemma C.4 source-facing forward wrapper with endpoint levels constructed by
the source's forward-clipped shooting argument.
-/
abbrev paper_lemmaC4_sourceWbar_has_positive_exponential_rate_of_forward_clipped_endpoint_piecewiseConstKernel
    (μ : Measure ℝ) [MeasureTheory.IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)] {m : ℕ} :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_sourceWbar_has_positive_exponential_rate_of_forward_clipped_endpoint_piecewiseConstKernel
    μ (m := m)

/--
Lemma C.4 source-facing forward branch under the paper's "appropriate finite
levels" convention.  The model names strict cutpoints and positive monotone
sample rates; the positive source-defined `Wbar_k` exponential-rate
certificate is derived, not assumed.

Source status: formalized forward convention clarified by the source phrase
"piecewise constant with the appropriate number of levels."
-/
abbrev paper_lemmaC4_appropriate_finite_levels_const_weight_rate_certificate
    (μ : Measure ℝ) [MeasureTheory.IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)] :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_appropriate_finite_levels_const_weight_rate_certificate
    μ

/--
Lemma C.4 weighted source finite-level convention.  The model names the
source cutpoints, sample rates, and objective-weight regularity data; the
positive selected ordered-pair `Wbar_k` exponential-rate certificate is
derived from the finite adjacent-rate optimizer and C.3 partition aggregation.

Source status: formalized weighted forward convention clarified by the
source phrase "piecewise constant with the appropriate number of levels."
-/
abbrev paper_lemmaC4_appropriate_finite_levels_weighted_rate_certificate
    (μ : Measure ℝ) [MeasureTheory.IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)] :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_appropriate_finite_levels_weighted_rate_certificate
    μ

/--
Theorem 3.1 fixed-discretization source-model branch: the weighted
finite-level source convention derives endpoint levels with an exact
source-defined `Wbar_k` rate certificate and fixed-partition lexicographic
optimality.

Source status: formalized fixed-discretization weighted source-model branch;
the global continuum optimizer over `S*` remains outside this row.
-/
abbrev paper_theorem31_appropriate_finite_levels_weighted_fixed_value_lexicographic_certificate
    (μ : Measure ℝ) [MeasureTheory.IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)] :=
  GJ19OptimalBinaryRatingSystems.theorem31_appropriate_finite_levels_weighted_fixed_value_lexicographic_certificate
    μ

/--
Lemma C.4 finite-level source convention: the same explicit finite cutpoint
model induces a finite-range success-probability rule and a positive exact
exponential-rate certificate for the selected ordered-pair `Wbar_k`.

Source status: formalized finite-range bridge for the forward convention
clarified by the source phrase "piecewise constant with the appropriate number
of levels."
-/
abbrev paper_lemmaC4_appropriate_finite_levels_const_weight_finiteRange_and_rate_certificate
    (μ : Measure ℝ) [MeasureTheory.IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)] :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_appropriate_finite_levels_const_weight_finiteRange_and_rate_certificate
    μ

/--
Lemma C.4 weighted finite-level source convention: the explicit finite
cutpoint model induces a finite-range success rule and a positive exact
exponential-rate certificate for the selected ordered-pair `Wbar_k`.

Source status: formalized weighted finite-range bridge for the forward
convention clarified by the source phrase "piecewise constant with the
appropriate number of levels."
-/
abbrev paper_lemmaC4_appropriate_finite_levels_weighted_finiteRange_and_rate_certificate
    (μ : Measure ℝ) [MeasureTheory.IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)] :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_appropriate_finite_levels_weighted_finiteRange_and_rate_certificate
    μ

/--
Continuum piecewise-constant Lemma C.4 forward direction with endpoint levels
constructed by the source's forward-clipped shooting argument.
-/
abbrev paper_lemmaC4_forward_clipped_endpoint_piecewiseConstKernel_has_positive_exponential_rate :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_forward_clipped_endpoint_piecewiseConstKernel_has_positive_exponential_rate

/--
Continuum piecewise-constant Lemma C.4 forward direction with canonical cell
midpoints replacing the external ordered-rectangle witness package.
-/
abbrev paper_lemmaC4_forward_clipped_endpoint_piecewiseConstKernel_has_positive_exponential_rate_of_cell_midpoints :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_forward_clipped_endpoint_piecewiseConstKernel_has_positive_exponential_rate_of_cell_midpoints

/--
Lemma C.4 canonical uniform piecewise-constant forward direction: the
canonical equalized endpoint levels with uniform sampling give a positive
exponential rate for the selected ordered-rectangle continuum error integral,
with cell midpoints supplying the local positive-weight witnesses.

Source status: formalized canonical piecewise-constant forward branch.
-/
abbrev paper_lemmaC4_canonical_uniform_endpoint_piecewiseConstKernel_has_positive_exponential_rate_of_cell_midpoints
    (μ : Measure ℝ) [MeasureTheory.IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)] {m : ℕ} :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_canonical_uniform_endpoint_piecewiseConstKernel_has_positive_exponential_rate_of_cell_midpoints
    μ (m := m)

/--
Theorem 3.1/C.4 source-defined canonical branch: the canonical equalized
endpoint levels with uniform sampling give a positive exponential-rate
certificate for the paper's source-defined `Wbar_k` convention.

Source status: formalized canonical source-defined piecewise-constant forward
branch.
-/
abbrev paper_theorem31SourceWbar_canonical_uniform_endpoint_piecewiseConstKernel_rate_certificate_of_cell_midpoints
    (μ : Measure ℝ) [MeasureTheory.IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)] {m : ℕ} :=
  GJ19OptimalBinaryRatingSystems.theorem31SourceWbar_canonical_uniform_endpoint_piecewiseConstKernel_rate_certificate_of_cell_midpoints
    μ (m := m)

/--
Theorem 3.1/C.4 source-defined canonical branch for constant objective weight
`w ≡ 1`.

Source status: formalized canonical constant-weight source-defined
piecewise-constant forward branch.
-/
abbrev paper_theorem31SourceWbar_canonical_uniform_endpoint_const_weight_rate_certificate_of_cell_midpoints
    (μ : Measure ℝ) [MeasureTheory.IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)] {m : ℕ} :=
  GJ19OptimalBinaryRatingSystems.theorem31SourceWbar_canonical_uniform_endpoint_const_weight_rate_certificate_of_cell_midpoints
    μ (m := m)

/--
Theorem 3.1 fixed-discretization bridge: forward-clipped endpoint levels are
finite-rate optimal and the corresponding continuum piecewise-constant
ordered-rectangle error integral has that optimal exponential rate.
-/
abbrev paper_theorem31_forward_clipped_endpoint_piecewiseConstKernel_rate_optimal :=
  GJ19OptimalBinaryRatingSystems.theorem31_forward_clipped_endpoint_piecewiseConstKernel_rate_optimal

/--
Theorem 3.1 source-defined `Wbar_k` convention: integrate the selected
piecewise-constant error kernel over the ordered quality-pair partition.
-/
abbrev paper_theorem31SourceWbar :=
  GJ19OptimalBinaryRatingSystems.theorem31SourceWbar

/-- The source-defined Theorem 3.1 `Wbar_k` is its displayed integral. -/
abbrev paper_theorem31SourceWbar_eventually_eq :=
  GJ19OptimalBinaryRatingSystems.theorem31SourceWbar_eventually_eq

/--
Theorem 3.1 source-defined `Wbar_k` nonnegativity from nonnegative component
weight integrals and nonnegative comparison-error kernels.
-/
abbrev paper_theorem31SourceWbar_nonneg :=
  GJ19OptimalBinaryRatingSystems.theorem31SourceWbar_nonneg

/-- Eventual nonnegativity form of the source-defined Theorem 3.1 `Wbar_k`. -/
abbrev paper_theorem31SourceWbar_eventually_nonneg :=
  GJ19OptimalBinaryRatingSystems.theorem31SourceWbar_eventually_nonneg

/--
Theorem 3.1 source-defined fixed-discretization bridge: forward-clipped
endpoint levels are finite-rate optimal and the source-defined `Wbar_k` has the
corresponding exponential rate.
-/
abbrev paper_theorem31_sourceDefinedWbar_forward_clipped_endpoint_piecewiseConstKernel_rate_optimal :=
  GJ19OptimalBinaryRatingSystems.theorem31_sourceDefinedWbar_forward_clipped_endpoint_piecewiseConstKernel_rate_optimal

/--
Theorem 3.1 source-defined fixed-discretization bridge in exact-certificate
form; nonnegativity of the source-defined `Wbar_k` is derived internally from
the finite partition decomposition.
-/
abbrev paper_theorem31_sourceDefinedWbar_forward_clipped_endpoint_piecewiseConstKernel_rate_certificate :=
  GJ19OptimalBinaryRatingSystems.theorem31_sourceDefinedWbar_forward_clipped_endpoint_piecewiseConstKernel_rate_certificate

/--
Theorem 3.1 fixed-discretization two-stage endpoint: with the interval
partition fixed, the source-defined forward-clipped construction is
lexicographically optimal because every feasible endpoint vector has the same
primary value and the construction maximizes the adjacent-rate objective.
-/
abbrev paper_theorem31_sourceDefinedWbar_forward_clipped_endpoint_piecewiseConstKernel_fixed_value_lexicographic_certificate :=
  GJ19OptimalBinaryRatingSystems.theorem31_sourceDefinedWbar_forward_clipped_endpoint_piecewiseConstKernel_fixed_value_lexicographic_certificate

/--
Theorem 3.1 fixed-discretization two-stage endpoint with canonical
cell-midpoint witnesses: for a fixed weighted interval partition, the
source-defined forward-clipped construction has an exact rate certificate and
is lexicographically optimal among endpoint levels.

Source status: formalized fixed-discretization weighted branch; this does not
claim the remaining global continuum optimizer over `S*`.
-/
abbrev paper_theorem31_sourceDefinedWbar_forward_clipped_endpoint_piecewiseConstKernel_fixed_value_lexicographic_certificate_of_cell_midpoints :=
  GJ19OptimalBinaryRatingSystems.theorem31_sourceDefinedWbar_forward_clipped_endpoint_piecewiseConstKernel_fixed_value_lexicographic_certificate_of_cell_midpoints

/--
Theorem 3.1 source-defined fixed-discretization bridge with canonical cell
midpoints supplying the ordered-rectangle witnesses internally.
-/
abbrev paper_theorem31_sourceDefinedWbar_forward_clipped_endpoint_piecewiseConstKernel_rate_optimal_of_cell_midpoints :=
  GJ19OptimalBinaryRatingSystems.theorem31_sourceDefinedWbar_forward_clipped_endpoint_piecewiseConstKernel_rate_optimal_of_cell_midpoints

/--
Theorem 3.1 source-defined fixed-discretization certificate bridge with
canonical cell midpoints.
-/
abbrev paper_theorem31_sourceDefinedWbar_forward_clipped_endpoint_piecewiseConstKernel_rate_certificate_of_cell_midpoints :=
  GJ19OptimalBinaryRatingSystems.theorem31_sourceDefinedWbar_forward_clipped_endpoint_piecewiseConstKernel_rate_certificate_of_cell_midpoints

/--
Theorem 3.1 source-defined fixed-discretization bridge for the constant
objective weight `w ≡ 1`; all weight and source-`Wbar_k` identification
premises are discharged by definition.
-/
abbrev paper_theorem31_sourceDefinedWbar_forward_clipped_endpoint_piecewiseConstKernel_rate_optimal_const_weight_of_cell_midpoints :=
  GJ19OptimalBinaryRatingSystems.theorem31_sourceDefinedWbar_forward_clipped_endpoint_piecewiseConstKernel_rate_optimal_const_weight_of_cell_midpoints

/--
Theorem 3.1 source-defined fixed-discretization exact-certificate bridge for
the constant objective weight `w ≡ 1`.
-/
abbrev paper_theorem31_sourceDefinedWbar_forward_clipped_endpoint_piecewiseConstKernel_rate_certificate_const_weight_of_cell_midpoints :=
  GJ19OptimalBinaryRatingSystems.theorem31_sourceDefinedWbar_forward_clipped_endpoint_piecewiseConstKernel_rate_certificate_const_weight_of_cell_midpoints

/--
Theorem 3.1 source-facing fixed-discretization bridge: forward-clipped endpoint
levels are finite-rate optimal and the source `Wbar_k` sequence has the
corresponding exponential rate once it is identified with the selected
ordered-rectangle error integral.
-/
abbrev paper_theorem31_sourceWbar_forward_clipped_endpoint_piecewiseConstKernel_rate_optimal
    (μ : Measure ℝ) [MeasureTheory.IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)] {m : ℕ} :=
  GJ19OptimalBinaryRatingSystems.theorem31_sourceWbar_forward_clipped_endpoint_piecewiseConstKernel_rate_optimal
    μ (m := m)

/--
Theorem 3.1 fixed-discretization bridge with canonical cell midpoints:
strictly increasing cutpoints supply the ordered-rectangle witness package
needed by the continuum rate theorem.
-/
abbrev paper_theorem31_forward_clipped_endpoint_piecewiseConstKernel_rate_optimal_of_cell_midpoints :=
  GJ19OptimalBinaryRatingSystems.theorem31_forward_clipped_endpoint_piecewiseConstKernel_rate_optimal_of_cell_midpoints

/--
Theorem 3.1 source-facing fixed-discretization bridge with canonical cell
midpoints supplying the ordered-rectangle witnesses internally.
-/
abbrev paper_theorem31_sourceWbar_forward_clipped_endpoint_piecewiseConstKernel_rate_optimal_of_cell_midpoints
    (μ : Measure ℝ) [MeasureTheory.IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)] {m : ℕ} :=
  GJ19OptimalBinaryRatingSystems.theorem31_sourceWbar_forward_clipped_endpoint_piecewiseConstKernel_rate_optimal_of_cell_midpoints
    μ (m := m)

/--
Theorem 3.1 fixed-discretization bridge for the constant objective weight
`w ≡ 1`; the generic weight integrability, nonnegativity, continuity, and
positive-witness premises are discharged internally.
-/
abbrev paper_theorem31_forward_clipped_endpoint_piecewiseConstKernel_rate_optimal_const_weight_of_cell_midpoints :=
  GJ19OptimalBinaryRatingSystems.theorem31_forward_clipped_endpoint_piecewiseConstKernel_rate_optimal_const_weight_of_cell_midpoints

/--
Theorem 3.1 source-facing fixed-discretization bridge for the constant
objective weight `w ≡ 1`; the remaining source premise is the identification
of `Wbar_k` with the selected ordered-rectangle error integral.
-/
abbrev paper_theorem31_sourceWbar_forward_clipped_endpoint_piecewiseConstKernel_rate_optimal_const_weight_of_cell_midpoints
    (μ : Measure ℝ) [MeasureTheory.IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)] {m : ℕ} :=
  GJ19OptimalBinaryRatingSystems.theorem31_sourceWbar_forward_clipped_endpoint_piecewiseConstKernel_rate_optimal_const_weight_of_cell_midpoints
    μ (m := m)

/--
Lemma C.4 reverse-branch obstruction: a fixed positive error lower bound along
arbitrarily large sample sizes rules out any positive exponential-rate
certificate.
-/
abbrev paper_lemmaC4_no_positive_exponential_rate_certificate_of_frequently_error_ge :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_no_positive_exponential_rate_certificate_of_frequently_error_ge

/--
Lemma C.4 reverse-branch obstruction: a fixed positive error lower bound along
arbitrarily large sample sizes rules out every positive exponential-rate
certificate.
-/
abbrev paper_lemmaC4_no_positive_exponential_rate_certificates_of_frequently_error_ge :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_no_positive_exponential_rate_certificates_of_frequently_error_ge

/--
Lemma C.4 reverse-branch obstruction: subexponential lower-error witnesses
rule out every positive exponential-rate certificate.
-/
abbrev paper_lemmaC4_no_positive_exponential_rate_certificates_of_subexponential_error :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_no_positive_exponential_rate_certificates_of_subexponential_error

/--
Lemma C.4 reverse-branch obstruction: an exact zero continuum error rate rules
out every positive exponential-rate certificate.
-/
abbrev paper_lemmaC4_no_positive_exponential_rate_certificates_of_zero_rate :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_no_positive_exponential_rate_certificates_of_zero_rate

/--
Lemma C.4 source-shaped iff packaging: forward positive-rate certificates and
reverse exact-zero-rate certificates imply the paper's positive-rate iff.
-/
abbrev paper_lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_zero_reverse :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_zero_reverse

/--
Lemma C.4 source-shaped iff packaging: forward positive-rate certificates and
reverse no-positive-rate certificates imply the paper's positive-rate iff.
-/
abbrev paper_lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_no_positive_reverse :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_no_positive_reverse

/--
Lemma C.4 source-shaped iff packaging: forward positive-rate certificates and
the paper's subexponential reverse lower-hit condition imply the positive-rate
iff.
-/
abbrev paper_lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_subexponential_reverse :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_subexponential_reverse

/--
Lemma C.4 source-shaped iff packaging for the concrete floor-complement
integral on a compact quality interval: the non-piecewise reverse direction is
derived from monotone interval regularity and pointwise binary LDP
certificates.

Source status: conditional C.4 reverse branch under the explicit
monotone-interval floor-complement convention.
-/
abbrev paper_lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_monotone_interval_floorPkComplementError :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_monotone_interval_floorPkComplementError

/--
Lemma C.4 source-model bridge: a concrete stepwise-on-interval convention
reduces the non-piecewise reverse branch to an interior probability subinterval
and positive diagonal support primitives.
-/
abbrev paper_lemmaC4_stepwiseOn_iff_exists_positive_exponential_rate_of_rawSourceWError_nonstepwise_prob_interval :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_stepwiseOn_iff_exists_positive_exponential_rate_of_rawSourceWError_nonstepwise_prob_interval

/--
Lemma C.4 source-model bridge: once non-stepwiseness gives an interior
probability interval, monotonicity supplies the continuity point used by the
paper's reverse-direction prose.
-/
abbrev paper_lemmaC4_nonstepwise_interior_continuity_point_witness_of_monotone_prob_interval :=
  @GJ19OptimalBinaryRatingSystems.lemmaC4_nonstepwise_interior_continuity_point_witness_of_monotone_prob_interval

/--
Lemma C.4 source-model bridge: two ordered interior probability values in the
non-stepwise monotone branch supply the interior probability interval used by
the reverse-rate argument.
-/
abbrev paper_lemmaC4_nonstepwise_prob_interval_witness_of_monotone_two_interior_values :=
  @GJ19OptimalBinaryRatingSystems.lemmaC4_nonstepwise_prob_interval_witness_of_monotone_two_interior_values

/--
Lemma C.4 source-model bridge: strict variation on an already-supported
interior interval supplies the two interior values used by the reverse-rate
argument.
-/
abbrev paper_lemmaC4_nonstepwise_two_interior_values_of_monotone_variation :=
  @GJ19OptimalBinaryRatingSystems.lemmaC4_nonstepwise_two_interior_values_of_monotone_variation

/--
Lemma C.4 source-model bridge: if constant interval rules count as stepwise,
then a non-stepwise monotone rule has strict variation on the interval.
-/
abbrev paper_lemmaC4_nonstepwise_monotone_variation_of_constant_on_interval_stepwise :=
  @GJ19OptimalBinaryRatingSystems.lemmaC4_nonstepwise_monotone_variation_of_constant_on_interval_stepwise

/--
Lemma C.4 local strict-variation witness: a monotone Bernoulli rule that is not
constant on any neighborhood of a continuity point has arbitrarily close
ordered qualities with strictly increasing success probabilities.
-/
abbrev paper_lemmaC4_ordered_strict_prob_values_near_of_monotone_not_locally_constant :=
  @GJ19OptimalBinaryRatingSystems.lemmaC4_ordered_strict_prob_values_near_of_monotone_not_locally_constant

/--
Lemma C.4 source-model bridge: two ordered interior probability values in the
non-stepwise monotone branch directly imply the raw global-error positive-rate
iff, given positive diagonal support primitives.
-/
abbrev paper_lemmaC4_stepwiseOn_iff_exists_positive_exponential_rate_of_rawSourceWError_nonstepwise_monotone_two_interior_values :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_stepwiseOn_iff_exists_positive_exponential_rate_of_rawSourceWError_nonstepwise_monotone_two_interior_values

/--
Lemma C.4 source-model bridge: strict variation on an already-supported
interior interval directly implies the raw global-error positive-rate iff,
given positive diagonal support primitives.
-/
abbrev paper_lemmaC4_stepwiseOn_iff_exists_positive_exponential_rate_of_rawSourceWError_nonstepwise_monotone_variation :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_stepwiseOn_iff_exists_positive_exponential_rate_of_rawSourceWError_nonstepwise_monotone_variation

/--
Lemma C.4 source-model bridge: when constant interval rules are stepwise,
non-stepwiseness of a monotone supported rule directly implies the raw
global-error positive-rate iff.
-/
abbrev paper_lemmaC4_stepwiseOn_iff_exists_positive_exponential_rate_of_rawSourceWError_nonstepwise_constant_semantics :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_stepwiseOn_iff_exists_positive_exponential_rate_of_rawSourceWError_nonstepwise_constant_semantics

/--
Lemma C.4 source-model bridge for the source-defined raw global `W^k` error:
when constant interval rules are stepwise, non-stepwiseness of a monotone
supported rule directly implies the positive-rate iff without a separate
raw-error equality premise.
-/
abbrev paper_lemmaC4_stepwiseOn_iff_exists_positive_exponential_rate_of_defined_rawSourceWError_nonstepwise_constant_semantics :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_stepwiseOn_iff_exists_positive_exponential_rate_of_defined_rawSourceWError_nonstepwise_constant_semantics

/--
Lemma C.4 concrete local source convention: the Bernoulli rating rule is
constant on the open quality interval being used by the reverse C.4 argument.
-/
abbrev paper_lemmaC4LocallyConstantOnIoo :=
  GJ19OptimalBinaryRatingSystems.lemmaC4LocallyConstantOnIoo

/--
Lemma C.4 source finite-step convention: on the witness interval, the
Bernoulli rating rule takes only finitely many success-probability values.
-/
abbrev paper_lemmaC4FiniteRangeOnIoo :=
  GJ19OptimalBinaryRatingSystems.lemmaC4FiniteRangeOnIoo

/--
Lemma C.4 source-semantics bridge: a locally constant rule is a one-level
finite-range rule on the same open quality interval.
-/
abbrev paper_lemmaC4FiniteRangeOnIoo_of_locallyConstantOnIoo :=
  GJ19OptimalBinaryRatingSystems.lemmaC4FiniteRangeOnIoo_of_locallyConstantOnIoo

/-- Source-defined tie-erased `Wbar_k` convention for Lemma C.4. -/
abbrev paper_lemmaC4TieErasedSourceWbar :=
  GJ19OptimalBinaryRatingSystems.lemmaC4TieErasedSourceWbar

/-- The source-defined tie-erased `Wbar_k` is the displayed strict-pair integral. -/
abbrev paper_lemmaC4TieErasedSourceWbar_eventually_eq :=
  GJ19OptimalBinaryRatingSystems.lemmaC4TieErasedSourceWbar_eventually_eq

/--
Lemma C.4 concrete local source bridge for the source-defined raw global
`W^k` error: local constancy on the witness interval is equivalent to having a
positive exponential-rate certificate, under the visible monotonicity,
support, continuity, and forward positive-rate hypotheses.
-/
abbrev paper_lemmaC4_locallyConstantOnIoo_iff_exists_positive_exponential_rate_of_defined_rawSourceWError :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_locallyConstantOnIoo_iff_exists_positive_exponential_rate_of_defined_rawSourceWError

/--
Lemma C.4 constant-weight source bridge: with uniform sampling and constant
pair weight, local constancy on the witness interval is equivalent to a
positive exponential-rate certificate under the forward positive-rate
construction.
-/
abbrev paper_lemmaC4_locallyConstantOnIoo_iff_exists_positive_exponential_rate_const_weight_uniform_sampleRate :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_locallyConstantOnIoo_iff_exists_positive_exponential_rate_const_weight_uniform_sampleRate

/--
Lemma C.4 source-model bridge: a concrete stepwise-on-interval convention
reduces the non-piecewise reverse branch to the paper's continuity-point
witness with positive diagonal support primitives.
-/
abbrev paper_lemmaC4_stepwiseOn_iff_exists_positive_exponential_rate_of_rawSourceWError_nonstepwise_continuity_point :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_stepwiseOn_iff_exists_positive_exponential_rate_of_rawSourceWError_nonstepwise_continuity_point

/--
Lemma C.4 source-model bridge on a positive support interval: when the whole
quality interval has positive diagonal support, positive sample rate, and
interior Bernoulli probabilities, the non-stepwise reverse branch uses that
interval directly.
-/
abbrev paper_lemmaC4_stepwiseOn_iff_exists_positive_exponential_rate_of_rawSourceWError_positive_support_interval :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_stepwiseOn_iff_exists_positive_exponential_rate_of_rawSourceWError_positive_support_interval

/--
Lemma C.4 reverse branch on a positive support interval: non-stepwiseness of
the source rating rule gives exact zero exponential rate for the raw `W^k`
error.
-/
abbrev paper_lemmaC4_rawSourceWError_has_zero_rate_of_nonstepwise_positive_support_interval :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_rawSourceWError_has_zero_rate_of_nonstepwise_positive_support_interval

/--
Lemma C.4 reverse branch on a positive support interval, in no-positive-rate
form for the raw source `W^k` error.
-/
abbrev paper_lemmaC4_rawSourceWError_no_positive_exponential_rate_of_nonstepwise_positive_support_interval :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_rawSourceWError_no_positive_exponential_rate_of_nonstepwise_positive_support_interval

/--
Lemma C.4 finite-range reverse branch: a monotone Bernoulli rule with
infinitely many success-probability values on the source interval has exact
zero exponential rate for the source-defined raw `W^k` error.
-/
abbrev paper_lemmaC4RawStrictUpperPairSourceWError_has_zero_rate_of_not_finiteRangeOnIoo :=
  GJ19OptimalBinaryRatingSystems.lemmaC4RawStrictUpperPairSourceWError_has_zero_rate_of_not_finiteRangeOnIoo

/--
Lemma C.4 finite-range reverse branch, no-positive-rate form for the
source-defined raw `W^k` error.
-/
abbrev paper_lemmaC4RawStrictUpperPairSourceWError_no_positive_exponential_rate_of_not_finiteRangeOnIoo :=
  GJ19OptimalBinaryRatingSystems.lemmaC4RawStrictUpperPairSourceWError_no_positive_exponential_rate_of_not_finiteRangeOnIoo

/--
Lemma C.4 finite-range reverse branch in the constant-weight, uniform-sampling
normalization used by the Kendall/Spearman source branch.
-/
abbrev paper_lemmaC4RawStrictUpperPairSourceWError_const_weight_uniform_sampleRate_has_zero_rate_of_not_finiteRangeOnIoo :=
  GJ19OptimalBinaryRatingSystems.lemmaC4RawStrictUpperPairSourceWError_const_weight_uniform_sampleRate_has_zero_rate_of_not_finiteRangeOnIoo

/--
Lemma C.4 finite-range reverse branch in constant-weight, uniform-sampling
normalization, no-positive-rate form.
-/
abbrev paper_lemmaC4RawStrictUpperPairSourceWError_const_weight_uniform_sampleRate_no_positive_exponential_rate_of_not_finiteRangeOnIoo :=
  GJ19OptimalBinaryRatingSystems.lemmaC4RawStrictUpperPairSourceWError_const_weight_uniform_sampleRate_no_positive_exponential_rate_of_not_finiteRangeOnIoo

/--
Lemma C.4 finite-range source convention: finite range on the witness interval
is equivalent to a positive exponential-rate certificate once the finite-step
forward construction is supplied; the reverse direction is derived in Lean.
-/
abbrev paper_lemmaC4_finiteRangeOnIoo_iff_exists_positive_exponential_rate_of_defined_rawSourceWError :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_finiteRangeOnIoo_iff_exists_positive_exponential_rate_of_defined_rawSourceWError

/--
Lemma C.4 finite-range source convention in constant-weight, uniform-sampling
normalization.
-/
abbrev paper_lemmaC4_finiteRangeOnIoo_iff_exists_positive_exponential_rate_const_weight_uniform_sampleRate :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_finiteRangeOnIoo_iff_exists_positive_exponential_rate_const_weight_uniform_sampleRate

/--
Lemma C.4 finite-range source convention in the concrete raw-floor
tie-erased `Wbar_k` form.  Constant weight, uniform sampling, and the concrete
`1 - P_k` source kernel remove the separate arbitrary-kernel certificate
premises; the remaining premise is the finite-step forward positive-rate
construction.
-/
abbrev paper_lemmaC4_finiteRangeOnIoo_iff_exists_positive_exponential_rate_of_defined_tieErasedSourceWbar_raw_floorPkComplementError_const_weight_uniform_sampleRate :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_finiteRangeOnIoo_iff_exists_positive_exponential_rate_of_defined_tieErasedSourceWbar_raw_floorPkComplementError_const_weight_uniform_sampleRate

/--
Lemma C.4 tie-erased source `Wbar_k` reverse bridge: bounded source kernels
with local near-rate normalized-log witnesses have exact zero exponential rate
after applying the paper's strict ordered-pair integral convention.
-/
abbrev paper_lemmaC4_tieErasedSourceWbar_has_zero_rate_of_boundedKernel_localUniformNormalizedLogRateCertificate_nearRate_sets :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_tieErasedSourceWbar_has_zero_rate_of_boundedKernel_localUniformNormalizedLogRateCertificate_nearRate_sets

/--
Lemma C.4 tie-erased source `Wbar_k` reverse bridge: the measurable-kernel
variant derives global strict-pair integrability from boundedness and
AEStronglyMeasurable source kernels.
-/
abbrev paper_lemmaC4_tieErasedSourceWbar_has_zero_rate_of_boundedKernel_localUniformNormalizedLogRateCertificate_nearRate_sets_of_measurableKernel :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_tieErasedSourceWbar_has_zero_rate_of_boundedKernel_localUniformNormalizedLogRateCertificate_nearRate_sets_of_measurableKernel

/--
Lemma C.4 tie-erased source `Wbar_k` reverse bridge, in no-positive-rate form:
the same local near-rate witnesses rule out every positive exact exponential
rate certificate.
-/
abbrev paper_lemmaC4_tieErasedSourceWbar_no_positive_exponential_rate_of_boundedKernel_localUniformNormalizedLogRateCertificate_nearRate_sets :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_tieErasedSourceWbar_no_positive_exponential_rate_of_boundedKernel_localUniformNormalizedLogRateCertificate_nearRate_sets

/--
Lemma C.4 tie-erased source `Wbar_k` measurable-kernel reverse bridge, in
no-positive-rate form.
-/
abbrev paper_lemmaC4_tieErasedSourceWbar_no_positive_exponential_rate_of_boundedKernel_localUniformNormalizedLogRateCertificate_nearRate_sets_of_measurableKernel :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_tieErasedSourceWbar_no_positive_exponential_rate_of_boundedKernel_localUniformNormalizedLogRateCertificate_nearRate_sets_of_measurableKernel

/--
Lemma C.4 tie-erased source `Wbar_k` reverse bridge at a diagonal continuity
point: the local near-rate witnesses are derived from continuity and the
strict-pair normalized-log certificate, so callers no longer supply them
explicitly.
-/
abbrev paper_lemmaC4_tieErasedSourceWbar_has_zero_rate_of_continuity_point_boundedKernel_uniformNormalizedLogRateCertificate_on_strictUpperPair :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_tieErasedSourceWbar_has_zero_rate_of_continuity_point_boundedKernel_uniformNormalizedLogRateCertificate_on_strictUpperPair

/--
Lemma C.4 tie-erased source `Wbar_k` reverse bridge at a diagonal continuity
point, with global strict-pair integrability derived from measurable bounded
source kernels.
-/
abbrev paper_lemmaC4_tieErasedSourceWbar_has_zero_rate_of_continuity_point_boundedKernel_uniformNormalizedLogRateCertificate_on_strictUpperPair_of_measurableKernel :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_tieErasedSourceWbar_has_zero_rate_of_continuity_point_boundedKernel_uniformNormalizedLogRateCertificate_on_strictUpperPair_of_measurableKernel

/--
Lemma C.4 tie-erased source `Wbar_k` reverse bridge at a diagonal continuity
point, in no-positive-rate form.
-/
abbrev paper_lemmaC4_tieErasedSourceWbar_no_positive_exponential_rate_of_continuity_point_boundedKernel_uniformNormalizedLogRateCertificate_on_strictUpperPair :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_tieErasedSourceWbar_no_positive_exponential_rate_of_continuity_point_boundedKernel_uniformNormalizedLogRateCertificate_on_strictUpperPair

/--
Lemma C.4 tie-erased source `Wbar_k` reverse bridge at a diagonal continuity
point, in no-positive-rate form, with measurable bounded source kernels.
-/
abbrev paper_lemmaC4_tieErasedSourceWbar_no_positive_exponential_rate_of_continuity_point_boundedKernel_uniformNormalizedLogRateCertificate_on_strictUpperPair_of_measurableKernel :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_tieErasedSourceWbar_no_positive_exponential_rate_of_continuity_point_boundedKernel_uniformNormalizedLogRateCertificate_on_strictUpperPair_of_measurableKernel

/--
Lemma C.4 tie-erased source `Wbar_k` positive-rate iff with the non-piecewise
reverse branch reduced to a single continuity-point witness rather than an
explicit family of near-rate sets.
-/
abbrev paper_lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_nonpiecewise_continuity_point_witness :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_nonpiecewise_continuity_point_witness

/--
Lemma C.4 tie-erased source `Wbar_k` positive-rate iff with the non-piecewise
reverse branch reduced to a continuity-point witness and measurable bounded
source kernels.
-/
abbrev paper_lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_nonpiecewise_continuity_point_witness_of_measurableKernel :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_nonpiecewise_continuity_point_witness_of_measurableKernel

/--
Lemma C.4 tie-erased source `Wbar_k` positive-rate iff with the non-piecewise
reverse branch reduced to one regular continuity point; the local sample-rate
upper bound is derived from continuity.
-/
abbrev paper_lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_nonpiecewise_regular_point_witness_of_measurableKernel :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_nonpiecewise_regular_point_witness_of_measurableKernel

/--
Lemma C.4 tie-erased source `Wbar_k` positive-rate iff with a stepwise-on
interval convention and a non-stepwise interior continuity-point witness.
-/
abbrev paper_lemmaC4_stepwiseOn_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_nonstepwise_interior_continuity_point_of_measurableKernel :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_stepwiseOn_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_nonstepwise_interior_continuity_point_of_measurableKernel

/--
Lemma C.4 tie-erased source `Wbar_k` positive-rate iff from the paper's
monotone probability-interval source convention.
-/
abbrev paper_lemmaC4_stepwiseOn_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_nonstepwise_prob_interval_of_measurableKernel :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_stepwiseOn_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_nonstepwise_prob_interval_of_measurableKernel

/--
Lemma C.4 tie-erased source `Wbar_k` positive-rate iff under the paper's
local-constancy interval convention.
-/
abbrev paper_lemmaC4_locallyConstantOnIoo_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_measurableKernel :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_locallyConstantOnIoo_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_measurableKernel

/--
Lemma C.4 source-defined tie-erased `Wbar_k` positive-rate iff under the
paper's local-constancy convention.
-/
abbrev paper_lemmaC4_locallyConstantOnIoo_iff_exists_positive_exponential_rate_of_defined_tieErasedSourceWbar_measurableKernel :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_locallyConstantOnIoo_iff_exists_positive_exponential_rate_of_defined_tieErasedSourceWbar_measurableKernel

/--
Lemma C.4 tie-erased source `Wbar_k`: non-local-constancy rules out positive
exponential-rate certificates under the paper's local-constancy convention.
-/
abbrev paper_lemmaC4_tieErasedSourceWbar_no_positive_exponential_rate_of_not_locallyConstantOnIoo_measurableKernel :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_tieErasedSourceWbar_no_positive_exponential_rate_of_not_locallyConstantOnIoo_measurableKernel

/--
Lemma C.4 source-defined tie-erased `Wbar_k`: non-local-constancy rules out
positive exponential-rate certificates.
-/
abbrev paper_lemmaC4TieErasedSourceWbar_no_positive_exponential_rate_of_not_locallyConstantOnIoo_measurableKernel :=
  GJ19OptimalBinaryRatingSystems.lemmaC4TieErasedSourceWbar_no_positive_exponential_rate_of_not_locallyConstantOnIoo_measurableKernel

/--
Lemma C.4 source-defined tie-erased `Wbar_k`: non-finite-range rules rule out
positive exponential-rate certificates under the paper's finite-step
convention.
-/
abbrev paper_lemmaC4TieErasedSourceWbar_no_positive_exponential_rate_of_not_finiteRangeOnIoo_measurableKernel :=
  GJ19OptimalBinaryRatingSystems.lemmaC4TieErasedSourceWbar_no_positive_exponential_rate_of_not_finiteRangeOnIoo_measurableKernel

/--
Lemma C.4 source-defined tie-erased `Wbar_k` positive-rate iff under the
paper's finite-step finite-range convention.
-/
abbrev paper_lemmaC4_finiteRangeOnIoo_iff_exists_positive_exponential_rate_of_defined_tieErasedSourceWbar_measurableKernel :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_finiteRangeOnIoo_iff_exists_positive_exponential_rate_of_defined_tieErasedSourceWbar_measurableKernel

/--
Lemma C.4 tie-erased source `Wbar_k`: constant-weight, uniform-sampling
no-positive-rate obstruction for non-local-constant rules.
-/
abbrev paper_lemmaC4_tieErasedSourceWbar_const_weight_uniform_sampleRate_no_positive_exponential_rate_of_not_locallyConstantOnIoo_measurableKernel :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_tieErasedSourceWbar_const_weight_uniform_sampleRate_no_positive_exponential_rate_of_not_locallyConstantOnIoo_measurableKernel

/--
Lemma C.4 source-defined tie-erased `Wbar_k`: constant-weight, uniform-sampling
no-positive-rate obstruction for non-local-constant rules.
-/
abbrev paper_lemmaC4TieErasedSourceWbar_const_weight_uniform_sampleRate_no_positive_exponential_rate_of_not_locallyConstantOnIoo_measurableKernel :=
  GJ19OptimalBinaryRatingSystems.lemmaC4TieErasedSourceWbar_const_weight_uniform_sampleRate_no_positive_exponential_rate_of_not_locallyConstantOnIoo_measurableKernel

/--
Lemma C.4 source-defined tie-erased `Wbar_k`: constant-weight, uniform-sampling
no-positive-rate obstruction for non-finite-range rules.
-/
abbrev paper_lemmaC4TieErasedSourceWbar_const_weight_uniform_sampleRate_no_positive_exponential_rate_of_not_finiteRangeOnIoo_measurableKernel :=
  GJ19OptimalBinaryRatingSystems.lemmaC4TieErasedSourceWbar_const_weight_uniform_sampleRate_no_positive_exponential_rate_of_not_finiteRangeOnIoo_measurableKernel

/--
Lemma C.4 source-defined tie-erased `Wbar_k`: constant-weight, uniform-sampling
no-positive-rate obstruction for probability kernels.
-/
abbrev paper_lemmaC4TieErasedSourceWbar_const_weight_uniform_sampleRate_no_positive_exponential_rate_of_not_locallyConstantOnIoo_probabilityKernel :=
  GJ19OptimalBinaryRatingSystems.lemmaC4TieErasedSourceWbar_const_weight_uniform_sampleRate_no_positive_exponential_rate_of_not_locallyConstantOnIoo_probabilityKernel

/--
Lemma C.4 source-defined tie-erased `Wbar_k`: constant-weight, uniform-sampling
no-positive-rate obstruction for probability kernels and non-finite-range rules.
-/
abbrev paper_lemmaC4TieErasedSourceWbar_const_weight_uniform_sampleRate_no_positive_exponential_rate_of_not_finiteRangeOnIoo_probabilityKernel :=
  GJ19OptimalBinaryRatingSystems.lemmaC4TieErasedSourceWbar_const_weight_uniform_sampleRate_no_positive_exponential_rate_of_not_finiteRangeOnIoo_probabilityKernel

/--
Lemma C.4 source-defined tie-erased `Wbar_k`: constant-weight, uniform-sampling
no-positive-rate obstruction from a uniform exponential-rate certificate.
-/
abbrev paper_lemmaC4TieErasedSourceWbar_const_weight_uniform_sampleRate_no_positive_exponential_rate_of_not_locallyConstantOnIoo_probabilityKernel_uniformExponentialRateCertificate :=
  GJ19OptimalBinaryRatingSystems.lemmaC4TieErasedSourceWbar_const_weight_uniform_sampleRate_no_positive_exponential_rate_of_not_locallyConstantOnIoo_probabilityKernel_uniformExponentialRateCertificate

/--
Lemma C.4 source-defined tie-erased `Wbar_k`: constant-weight, uniform-sampling
no-positive-rate obstruction from a uniform exponential-rate certificate and a
non-finite-range rule.
-/
abbrev paper_lemmaC4TieErasedSourceWbar_const_weight_uniform_sampleRate_no_positive_exponential_rate_of_not_finiteRangeOnIoo_probabilityKernel_uniformExponentialRateCertificate :=
  GJ19OptimalBinaryRatingSystems.lemmaC4TieErasedSourceWbar_const_weight_uniform_sampleRate_no_positive_exponential_rate_of_not_finiteRangeOnIoo_probabilityKernel_uniformExponentialRateCertificate

/--
Lemma C.4 tie-erased source `Wbar_k` positive-rate iff under constant weight
and uniform sampling.
-/
abbrev paper_lemmaC4_locallyConstantOnIoo_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_const_weight_uniform_sampleRate_measurableKernel :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_locallyConstantOnIoo_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_const_weight_uniform_sampleRate_measurableKernel

/--
Lemma C.4 source-defined tie-erased `Wbar_k` positive-rate iff under constant
weight and uniform sampling.
-/
abbrev paper_lemmaC4_locallyConstantOnIoo_iff_exists_positive_exponential_rate_of_defined_tieErasedSourceWbar_const_weight_uniform_sampleRate_measurableKernel :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_locallyConstantOnIoo_iff_exists_positive_exponential_rate_of_defined_tieErasedSourceWbar_const_weight_uniform_sampleRate_measurableKernel

/--
Lemma C.4 source-defined tie-erased `Wbar_k` positive-rate iff under constant
weight and uniform sampling for probability kernels.
-/
abbrev paper_lemmaC4_locallyConstantOnIoo_iff_exists_positive_exponential_rate_of_defined_tieErasedSourceWbar_const_weight_uniform_sampleRate_probabilityKernel :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_locallyConstantOnIoo_iff_exists_positive_exponential_rate_of_defined_tieErasedSourceWbar_const_weight_uniform_sampleRate_probabilityKernel

/--
Lemma C.4 source-defined tie-erased `Wbar_k` positive-rate iff under constant
weight and uniform sampling from a uniform exponential-rate certificate.
-/
abbrev paper_lemmaC4_locallyConstantOnIoo_iff_exists_positive_exponential_rate_of_defined_tieErasedSourceWbar_const_weight_uniform_sampleRate_probabilityKernel_uniformExponentialRateCertificate :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_locallyConstantOnIoo_iff_exists_positive_exponential_rate_of_defined_tieErasedSourceWbar_const_weight_uniform_sampleRate_probabilityKernel_uniformExponentialRateCertificate

/--
Lemma C.4 tie-erased source `Wbar_k` positive-rate iff: the piecewise forward
construction plus source near-rate witnesses for every non-piecewise branch
gives the paper's `piecewise iff positive exponential rate` conclusion.
-/
abbrev paper_lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_nonpiecewise_nearRate_sets :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_nonpiecewise_nearRate_sets

/--
Lemma C.4 tie-erased source `Wbar_k` positive-rate iff with measurable bounded
source kernels: source near-rate witnesses for every non-piecewise branch give
the paper's `piecewise iff positive exponential rate` conclusion.
-/
abbrev paper_lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_nonpiecewise_nearRate_sets_of_measurableKernel :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_nonpiecewise_nearRate_sets_of_measurableKernel

/--
Lemma C.4 tie-erased source `Wbar_k` reverse bridge: the source kernel may
zero same-rating ties globally, but on a non-tie witness interval where it
agrees with the raw Bernoulli floor-complement kernel, non-piecewise monotone
variation gives exact zero exponential rate for `Wbar_k`.
-/
abbrev paper_lemmaC4_tieErasedSourceWbar_has_zero_rate_of_monotone_interval_nonTie_witness :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_tieErasedSourceWbar_has_zero_rate_of_monotone_interval_nonTie_witness

/--
Lemma C.4 source-defined tie-erased `Wbar_k` reverse bridge: the source kernel
may zero same-rating ties globally, but raw equality on a non-tie interval
witness gives exact zero exponential rate for the displayed `Wbar_k` integral.
-/
abbrev paper_lemmaC4TieErasedSourceWbar_has_zero_rate_of_monotone_interval_nonTie_witness :=
  GJ19OptimalBinaryRatingSystems.lemmaC4TieErasedSourceWbar_has_zero_rate_of_monotone_interval_nonTie_witness

/--
Lemma C.4 source-defined tie-erased `Wbar_k` reverse bridge, in
no-positive-rate form.
-/
abbrev paper_lemmaC4TieErasedSourceWbar_no_positive_exponential_rate_of_monotone_interval_nonTie_witness :=
  GJ19OptimalBinaryRatingSystems.lemmaC4TieErasedSourceWbar_no_positive_exponential_rate_of_monotone_interval_nonTie_witness

/--
Lemma C.4 tie-erased source `Wbar_k` positive-rate iff: the piecewise forward
construction plus a non-tie interval witness for every non-piecewise source
rule gives the paper's `piecewise iff positive exponential rate` conclusion.
-/
abbrev paper_lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_nonpiecewise_nonTie_interval_witness :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_nonpiecewise_nonTie_interval_witness

/--
Lemma C.4 source-defined tie-erased `Wbar_k` positive-rate iff: the displayed
integral convention is built into `Wbar_k`, and the reverse direction consumes
non-tie interval witnesses for non-piecewise source rules.

Source status: formalized Lemma C.4 positive-rate iff in the source-defined
displayed-integral convention.
-/
abbrev paper_lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_defined_tieErasedSourceWbar_nonpiecewise_nonTie_interval_witness :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_defined_tieErasedSourceWbar_nonpiecewise_nonTie_interval_witness

/--
Lemma C.4 tie-erased source `Wbar_k` reverse bridge over a non-tie witness
cell: the source kernel may zero same-rating ties globally, but raw equality on
the supplied near-diagonal witness cell is enough to derive exact zero
exponential rate for `Wbar_k`.
-/
abbrev paper_lemmaC4_tieErasedSourceWbar_has_zero_rate_of_witnessCell_nonTie :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_tieErasedSourceWbar_has_zero_rate_of_witnessCell_nonTie

/--
Lemma C.4 reverse branch for the source-defined raw strict ordered-pair
`W^k` error: non-stepwiseness on a positive support interval gives exact zero
exponential rate.
-/
abbrev paper_lemmaC4RawStrictUpperPairSourceWError_has_zero_rate_of_nonstepwise_positive_support_interval :=
  GJ19OptimalBinaryRatingSystems.lemmaC4RawStrictUpperPairSourceWError_has_zero_rate_of_nonstepwise_positive_support_interval

/--
Lemma C.4 reverse branch for the source-defined raw strict ordered-pair
`W^k` error, in no-positive-rate form.
-/
abbrev paper_lemmaC4RawStrictUpperPairSourceWError_no_positive_exponential_rate_of_nonstepwise_positive_support_interval :=
  GJ19OptimalBinaryRatingSystems.lemmaC4RawStrictUpperPairSourceWError_no_positive_exponential_rate_of_nonstepwise_positive_support_interval

/--
Lemma C.4 local analytic core: at an interior continuity point, locally bounded
positive sample rates force nearby pairwise closed Bernoulli exponents to
vanish.
-/
abbrev paper_lemmaC4_pairwise_closed_rate_tendsto_zero_at_continuity_point :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_pairwise_closed_rate_tendsto_zero_at_continuity_point

/--
Lemma C.4 analytic helper: continuity of the composed closed Bernoulli exponent
from coordinate continuity of the sample-rate and success-probability curves.
-/
abbrev paper_lemmaC4_pairwise_closed_rate_continuousAt_of_coordinate_continuousAt :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_pairwise_closed_rate_continuousAt_of_coordinate_continuousAt

/--
Lemma C.4 compact-uniform certificate constructor: pointwise normalized-log
convergence plus an eventual Lipschitz estimate on a compact superset supplies
the uniform normalized-log certificate used by the reverse Laplace bridge.
-/
abbrev paper_lemmaC4_pairwise_closed_rate_uniformNormalizedLogRateCertificateOn_of_pointwise_tendsto_eventually_lipschitz_on_compact_superset_of_rate_continuousAt :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_pairwise_closed_rate_uniformNormalizedLogRateCertificateOn_of_pointwise_tendsto_eventually_lipschitz_on_compact_superset_of_rate_continuousAt

/--
Lemma C.4 compact-uniform certificate constructor, deriving rate continuity
from coordinate continuity and interior bounds.
-/
abbrev paper_lemmaC4_pairwise_closed_rate_uniformNormalizedLogRateCertificateOn_of_pointwise_tendsto_eventually_lipschitz_on_compact_superset_of_coordinate_continuity :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_pairwise_closed_rate_uniformNormalizedLogRateCertificateOn_of_pointwise_tendsto_eventually_lipschitz_on_compact_superset_of_coordinate_continuity

/--
Lemma C.4 compact-uniform certificate constructor from fixed-pair exact-rate
certificates and an eventual Lipschitz estimate on a compact superset.
-/
abbrev paper_lemmaC4_pairwise_closed_rate_uniformNormalizedLogRateCertificateOn_of_pointwise_certificates_eventually_lipschitz_on_compact_superset_of_rate_continuousAt :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_pairwise_closed_rate_uniformNormalizedLogRateCertificateOn_of_pointwise_certificates_eventually_lipschitz_on_compact_superset_of_rate_continuousAt

/--
Lemma C.4 compact-uniform certificate constructor from fixed-pair exact-rate
certificates, deriving rate continuity from coordinate continuity and interior
bounds.
-/
abbrev paper_lemmaC4_pairwise_closed_rate_uniformNormalizedLogRateCertificateOn_of_pointwise_certificates_eventually_lipschitz_on_compact_superset_of_coordinate_continuity :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_pairwise_closed_rate_uniformNormalizedLogRateCertificateOn_of_pointwise_certificates_eventually_lipschitz_on_compact_superset_of_coordinate_continuity

/--
Lemma C.4 reverse-branch Laplace bridge: a diagonal continuity point with
locally bounded positive sample rates forces the ordered-pair weighted error
integral to have exact exponential rate zero, once the source's uniform-log
kernel convergence and support hypotheses are supplied.
-/
abbrev paper_lemmaC4_weighted_ordered_pair_integral_has_zero_rate_of_continuity_point :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_weighted_ordered_pair_integral_has_zero_rate_of_continuity_point

/--
Lemma C.4 reverse-branch Laplace bridge with normalized-log convergence
required only on the integration cell.
-/
abbrev paper_lemmaC4_weighted_ordered_pair_integral_has_zero_rate_of_continuity_point_on_cell :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_weighted_ordered_pair_integral_has_zero_rate_of_continuity_point_on_cell

/--
Lemma C.4 cell-local zero-rate bridge for bounded kernels, deriving the
uniform certificate from compact pointwise exact-rate certificates and an
eventual Lipschitz estimate.
-/
abbrev paper_lemmaC4_weighted_ordered_pair_integral_has_zero_rate_of_continuity_point_boundedKernel_pointwise_certificates_eventually_lipschitz_on_compact :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_weighted_ordered_pair_integral_has_zero_rate_of_continuity_point_boundedKernel_pointwise_certificates_eventually_lipschitz_on_compact

/--
Lemma C.4 reverse-branch zero-rate bridge with the remaining analytic work
isolated as local lower-envelope witnesses.
-/
abbrev paper_lemmaC4_weighted_ordered_pair_integral_has_zero_rate_of_constant_upper_bound_and_near_minimizer_sets :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_weighted_ordered_pair_integral_has_zero_rate_of_constant_upper_bound_and_near_minimizer_sets

/--
Lemma C.4 reverse-branch zero-rate bridge from a normalized-log certificate and
local positive-measure near-rate sets.
-/
abbrev paper_lemmaC4_weighted_ordered_pair_integral_has_zero_rate_of_uniformNormalizedLogRateCertificate_nearRate_sets :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_weighted_ordered_pair_integral_has_zero_rate_of_uniformNormalizedLogRateCertificate_nearRate_sets

/--
Lemma C.4 reverse-branch zero-rate bridge from local normalized-log
certificates for kernels bounded by a fixed nonnegative constant, covering the
paper's `1 - P_k` convention.
-/
abbrev paper_lemmaC4_weighted_ordered_pair_integral_has_zero_rate_of_boundedKernel_localUniformNormalizedLogRateCertificate_nearRate_sets :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_weighted_ordered_pair_integral_has_zero_rate_of_boundedKernel_localUniformNormalizedLogRateCertificate_nearRate_sets

/--
Lemma C.4 bounded-kernel near-rate bridge with product integrability derived
from restricted kernel measurability and `0 <= kernel <= K`.
-/
abbrev paper_lemmaC4_weighted_ordered_pair_integral_has_zero_rate_of_boundedKernel_localUniformNormalizedLogRateCertificate_nearRate_sets_of_measurableKernel :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_weighted_ordered_pair_integral_has_zero_rate_of_boundedKernel_localUniformNormalizedLogRateCertificate_nearRate_sets_of_measurableKernel

/--
Lemma C.4 reverse-branch zero-rate bridge from compact pointwise exact-rate
certificates and an eventual Lipschitz estimate for bounded kernels.
-/
abbrev paper_lemmaC4_weighted_ordered_pair_integral_has_zero_rate_of_boundedKernel_pointwise_certificates_eventually_lipschitz_on_compact_weightedNearInf :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_weighted_ordered_pair_integral_has_zero_rate_of_boundedKernel_pointwise_certificates_eventually_lipschitz_on_compact_weightedNearInf

/--
Lemma C.4 reverse-branch zero-rate bridge from a normalized-log certificate
and the weighted near-essential-infimum interface on the restricted cell.
-/
abbrev paper_lemmaC4_weighted_ordered_pair_integral_has_zero_rate_of_uniformNormalizedLogRateCertificate_weightedNearInf :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_weighted_ordered_pair_integral_has_zero_rate_of_uniformNormalizedLogRateCertificate_weightedNearInf

/--
Lemma C.4 reverse-branch zero-rate bridge from a normalized-log certificate
on an almost-everywhere full cell-local set and the weighted
near-essential-infimum interface.
-/
abbrev paper_lemmaC4_weighted_ordered_pair_integral_has_zero_rate_of_uniformNormalizedLogRateCertificate_weightedNearInf_of_ae_mem_certSet :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_weighted_ordered_pair_integral_has_zero_rate_of_uniformNormalizedLogRateCertificate_weightedNearInf_of_ae_mem_certSet

/--
Lemma C.4 bounded-kernel weighted-near-infimum bridge with product
integrability and the constant upper bound derived from restricted kernel
measurability and `0 <= kernel <= K`.
-/
abbrev paper_lemmaC4_weighted_ordered_pair_integral_has_zero_rate_of_boundedKernel_uniformNormalizedLogRateCertificate_weightedNearInf_of_ae_mem_certSet_of_measurableKernel :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_weighted_ordered_pair_integral_has_zero_rate_of_boundedKernel_uniformNormalizedLogRateCertificate_weightedNearInf_of_ae_mem_certSet_of_measurableKernel

/--
Lemma C.4 strict ordered-pair zero-rate bridge from a normalized-log
certificate on `θ_2 < θ_1` and the weighted near-essential-infimum interface
for the restricted measure.
-/
abbrev paper_lemmaC4_strictUpperPair_integral_has_zero_rate_of_uniformNormalizedLogRateCertificate_weightedNearInf_on_strictUpperPair :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_strictUpperPair_integral_has_zero_rate_of_uniformNormalizedLogRateCertificate_weightedNearInf_on_strictUpperPair

/--
Lemma C.4 strict ordered-pair zero-rate bridge from local normalized-log
certificates for kernels bounded by a fixed nonnegative constant.
-/
abbrev paper_lemmaC4_strictUpperPair_integral_has_zero_rate_of_boundedKernel_localUniformNormalizedLogRateCertificate_nearRate_sets :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_strictUpperPair_integral_has_zero_rate_of_boundedKernel_localUniformNormalizedLogRateCertificate_nearRate_sets

/--
Lemma C.4 strict ordered-pair zero-rate bridge at a diagonal continuity point:
a constant upper bound and normalized-log certificate on `θ_2 < θ_1` suffice,
with the local near-minimizer witness derived from continuity and positive
diagonal weight.
-/
abbrev paper_lemmaC4_strictUpperPair_integral_has_zero_rate_of_continuity_point_constant_upper_bound_uniformNormalizedLogRateCertificate_on_strictUpperPair :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_strictUpperPair_integral_has_zero_rate_of_continuity_point_constant_upper_bound_uniformNormalizedLogRateCertificate_on_strictUpperPair

/--
Lemma C.4 reverse-branch monotone-interval bridge with a constant upper bound
and a normalized-log certificate on `θ_2 < θ_1`; the continuity point and local
sample-rate bound are derived from monotonicity and continuity.
-/
abbrev paper_lemmaC4_strictUpperPair_integral_has_zero_rate_of_monotone_continuity_interval_constant_upper_bound_uniformNormalizedLogRateCertificate_on_strictUpperPair :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_strictUpperPair_integral_has_zero_rate_of_monotone_continuity_interval_constant_upper_bound_uniformNormalizedLogRateCertificate_on_strictUpperPair

/--
Lemma C.4 strict ordered-pair bridge at a diagonal continuity point for
kernels bounded by a fixed nonnegative constant.
-/
abbrev paper_lemmaC4_strictUpperPair_integral_has_zero_rate_of_continuity_point_boundedKernel_uniformNormalizedLogRateCertificate_on_strictUpperPair :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_strictUpperPair_integral_has_zero_rate_of_continuity_point_boundedKernel_uniformNormalizedLogRateCertificate_on_strictUpperPair

/--
Lemma C.4 strict ordered-pair bounded-kernel bridge with product integrability
derived from restricted kernel measurability and `0 <= kernel <= K`.
-/
abbrev paper_lemmaC4_strictUpperPair_integral_has_zero_rate_of_continuity_point_boundedKernel_uniformNormalizedLogRateCertificate_on_strictUpperPair_of_measurableKernel :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_strictUpperPair_integral_has_zero_rate_of_continuity_point_boundedKernel_uniformNormalizedLogRateCertificate_on_strictUpperPair_of_measurableKernel

/--
Lemma C.4 strict ordered-pair bridge at a diagonal continuity point, deriving
the required uniform certificate from pointwise exact-rate certificates and an
eventual Lipschitz estimate on a compact superset.
-/
abbrev paper_lemmaC4_strictUpperPair_integral_has_zero_rate_of_continuity_point_boundedKernel_pointwise_certificates_eventually_lipschitz_on_compact :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_strictUpperPair_integral_has_zero_rate_of_continuity_point_boundedKernel_pointwise_certificates_eventually_lipschitz_on_compact

/--
Lemma C.4 monotone-interval bridge for kernels bounded by a fixed nonnegative
constant; the continuity point and local sample-rate bound are derived from
monotonicity and continuity.
-/
abbrev paper_lemmaC4_strictUpperPair_integral_has_zero_rate_of_monotone_continuity_interval_boundedKernel_uniformNormalizedLogRateCertificate_on_strictUpperPair :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_strictUpperPair_integral_has_zero_rate_of_monotone_continuity_interval_boundedKernel_uniformNormalizedLogRateCertificate_on_strictUpperPair

/--
Lemma C.4 monotone-interval bridge for bounded kernels, deriving the uniform
certificate from pointwise exact-rate certificates and an eventual Lipschitz
estimate on a compact superset.
-/
abbrev paper_lemmaC4_strictUpperPair_integral_has_zero_rate_of_monotone_continuity_interval_boundedKernel_pointwise_certificates_eventually_lipschitz_on_compact :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_strictUpperPair_integral_has_zero_rate_of_monotone_continuity_interval_boundedKernel_pointwise_certificates_eventually_lipschitz_on_compact

/--
Lemma C.4 reverse-branch strict ordered-pair bridge: the same zero-rate
weighted-integral conclusion on the paper's domain `θ_2 < θ_1`, with the
diagonal closure/interior support condition discharged by the shared
ordered-pair topology library.
-/
abbrev paper_lemmaC4_strictUpperPair_integral_has_zero_rate_of_continuity_point :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_strictUpperPair_integral_has_zero_rate_of_continuity_point

/--
Lemma C.4 reverse-branch strict ordered-pair bridge with normalized-log
convergence required only on the strict ordered-pair domain.
-/
abbrev paper_lemmaC4_strictUpperPair_integral_has_zero_rate_of_continuity_point_on_strictUpperPair :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_strictUpperPair_integral_has_zero_rate_of_continuity_point_on_strictUpperPair

/--
Lemma C.4 reverse-branch strict ordered-pair bridge under global interior
Bernoulli probabilities and positive sample rates; the rate nonnegativity and
local sample positivity hypotheses are derived internally.
-/
abbrev paper_lemmaC4_strictUpperPair_integral_has_zero_rate_of_continuity_point_of_global_interior :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_strictUpperPair_integral_has_zero_rate_of_continuity_point_of_global_interior

/--
Lemma C.4 reverse-branch strict ordered-pair bridge under global interior
regularity, using the shared uniform-normalized-log certificate interface for
the pairwise error kernel.
-/
abbrev paper_lemmaC4_strictUpperPair_integral_has_zero_rate_of_continuity_point_of_global_interior_uniformNormalizedLogRateCertificate :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_strictUpperPair_integral_has_zero_rate_of_continuity_point_of_global_interior_uniformNormalizedLogRateCertificate

/--
Lemma C.4 reverse-branch strict ordered-pair bridge under global interior
regularity, using a uniform-normalized-log certificate only on the strict
ordered-pair domain.
-/
abbrev paper_lemmaC4_strictUpperPair_integral_has_zero_rate_of_continuity_point_of_global_interior_uniformNormalizedLogRateCertificate_on_strictUpperPair :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_strictUpperPair_integral_has_zero_rate_of_continuity_point_of_global_interior_uniformNormalizedLogRateCertificate_on_strictUpperPair

/--
Lemma C.4 reverse-branch strict ordered-pair bridge under monotone
success-probability regularity: the required continuity point and local sample
bound are derived from monotonicity on a nonempty interval and sample-rate
continuity.
-/
abbrev paper_lemmaC4_strictUpperPair_integral_has_zero_rate_of_monotone_continuity_interval :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_strictUpperPair_integral_has_zero_rate_of_monotone_continuity_interval

/--
Lemma C.4 reverse-branch monotone-interval bridge using the shared
uniform-normalized-log certificate interface; this packages the source-shaped
continuity-point and local boundedness witnesses.
-/
abbrev paper_lemmaC4_strictUpperPair_integral_has_zero_rate_of_monotone_continuity_interval_uniformNormalizedLogRateCertificate :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_strictUpperPair_integral_has_zero_rate_of_monotone_continuity_interval_uniformNormalizedLogRateCertificate

/--
Lemma C.4 reverse-branch monotone-interval bridge using a
uniform-normalized-log certificate only on the strict ordered-pair domain.
-/
abbrev paper_lemmaC4_strictUpperPair_integral_has_zero_rate_of_monotone_continuity_interval_uniformNormalizedLogRateCertificate_on_strictUpperPair :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_strictUpperPair_integral_has_zero_rate_of_monotone_continuity_interval_uniformNormalizedLogRateCertificate_on_strictUpperPair

/--
Lemma C.4 bounded strict-pair bridge at a diagonal continuity point: for the
source's compact quality interval, a closed-box uniform normalized-log
certificate implies zero exponential rate on `a ≤ θ₂ < θ₁ ≤ b`.
-/
abbrev paper_lemmaC4_boundedStrictUpperPair_integral_has_zero_rate_of_continuity_point_boundedKernel_uniformNormalizedLogRateCertificate_on_closed_box :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_boundedStrictUpperPair_integral_has_zero_rate_of_continuity_point_boundedKernel_uniformNormalizedLogRateCertificate_on_closed_box

/--
Lemma C.4 bounded strict-pair bridge at a diagonal continuity point using a
uniform normalized-log certificate only on the closed upper triangle of
`[a,b]²`.
-/
abbrev paper_lemmaC4_boundedStrictUpperPair_integral_has_zero_rate_of_continuity_point_boundedKernel_uniformNormalizedLogRateCertificate_on_closed_upper_box :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_boundedStrictUpperPair_integral_has_zero_rate_of_continuity_point_boundedKernel_uniformNormalizedLogRateCertificate_on_closed_upper_box

/--
Lemma C.4 bounded strict-pair closed-upper-triangle bridge with product
integrability derived from restricted kernel measurability and
`0 <= kernel <= K`.
-/
abbrev paper_lemmaC4_boundedStrictUpperPair_integral_has_zero_rate_of_continuity_point_boundedKernel_uniformNormalizedLogRateCertificate_on_closed_upper_box_of_measurableKernel :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_boundedStrictUpperPair_integral_has_zero_rate_of_continuity_point_boundedKernel_uniformNormalizedLogRateCertificate_on_closed_upper_box_of_measurableKernel

/--
Lemma C.4 bounded strict-pair bridge for the concrete floor-complement kernel:
left-tail Lipschitz regularity on the closed upper triangle supplies the
uniform certificate, and kernel measurability is derived from continuity of
the success-probability and sample-rate functions.
-/
abbrev paper_lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_continuity_point_leftTail_eventually_lipschitz_on_closed_upper_box :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_continuity_point_leftTail_eventually_lipschitz_on_closed_upper_box

/--
Lemma C.4 bounded strict-pair bridge with success/sample regularity localized
to the compact quality interval `[a,b]`.
-/
abbrev paper_lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_continuity_point_leftTail_eventually_lipschitz_on_closed_upper_box_of_Icc :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_continuity_point_leftTail_eventually_lipschitz_on_closed_upper_box_of_Icc

/--
Lemma C.4 bounded strict-pair bridge for the concrete floor-complement kernel:
a left-tail uniform exponential certificate on the closed upper triangle
transfers to the paper's `1 - P_k` kernel.
-/
abbrev paper_lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_continuity_point_measurableKernel_leftTail_uniformExponentialRateCertificate_on_closed_upper_box :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_continuity_point_measurableKernel_leftTail_uniformExponentialRateCertificate_on_closed_upper_box

/--
Lemma C.4 bounded strict-pair bridge for the concrete floor-complement kernel:
a left-tail uniform exponential certificate on the closed upper triangle
transfers to `1 - P_k`, and kernel measurability is derived from measurable
success-probability and sample-rate functions.
-/
abbrev paper_lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_continuity_point_leftTail_uniformExponentialRateCertificate_on_closed_upper_box :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_continuity_point_leftTail_uniformExponentialRateCertificate_on_closed_upper_box

/--
Lemma C.4 bounded strict-pair bridge for the concrete floor-complement kernel:
pointwise binary Cramer certificates on the closed upper triangle are enough to
prove the zero-rate integral conclusion; no compact-uniform normalized-log
premise is needed.
-/
abbrev paper_lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_continuity_point_pointwise_on_closed_upper_box :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_continuity_point_pointwise_on_closed_upper_box

/--
Lemma C.4 bounded strict-pair bridge with success/sample regularity localized
to `[a,b]`: pointwise binary Cramer certificates on the closed upper triangle
give the reverse-branch zero-rate conclusion.
-/
abbrev paper_lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_continuity_point_pointwise_on_closed_upper_box_of_Icc :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_continuity_point_pointwise_on_closed_upper_box_of_Icc

/--
Lemma C.4 bounded strict-pair bridge for the concrete floor-complement kernel:
left-tail Lipschitz regularity on the closed upper triangle supplies the
uniform certificate, and the finite-rating sandwich transfers it to `1 - P_k`.
-/
abbrev paper_lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_continuity_point_measurableKernel_leftTail_eventually_lipschitz_on_closed_upper_box :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_continuity_point_measurableKernel_leftTail_eventually_lipschitz_on_closed_upper_box

/--
Lemma C.4 bounded strict-pair monotone-interval bridge for the concrete
floor-complement kernel from left-tail Lipschitz regularity on the closed
upper triangle.
-/
abbrev paper_lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_monotone_continuity_interval_measurableKernel_leftTail_eventually_lipschitz_on_closed_upper_box :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_monotone_continuity_interval_measurableKernel_leftTail_eventually_lipschitz_on_closed_upper_box

/--
Lemma C.4 bounded strict-pair monotone-interval bridge from left-tail
Lipschitz regularity on the closed upper triangle, with kernel measurability
derived from continuity.
-/
abbrev paper_lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_monotone_continuity_interval_leftTail_eventually_lipschitz_on_closed_upper_box :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_monotone_continuity_interval_leftTail_eventually_lipschitz_on_closed_upper_box

/--
Lemma C.4 bounded strict-pair monotone-interval bridge with source regularity
localized to the compact quality interval `[a,b]`.
-/
abbrev paper_lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_monotone_continuity_interval_leftTail_eventually_lipschitz_on_closed_upper_box_of_Icc :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_monotone_continuity_interval_leftTail_eventually_lipschitz_on_closed_upper_box_of_Icc

/--
Lemma C.4 bounded strict-pair monotone-interval bridge for the concrete
floor-complement kernel from a left-tail uniform exponential certificate on
the closed upper triangle.
-/
abbrev paper_lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_monotone_continuity_interval_measurableKernel_leftTail_uniformExponentialRateCertificate_on_closed_upper_box :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_monotone_continuity_interval_measurableKernel_leftTail_uniformExponentialRateCertificate_on_closed_upper_box

/--
Lemma C.4 bounded strict-pair monotone-interval bridge from a left-tail
uniform exponential certificate on the closed upper triangle, with kernel
measurability derived from measurable success-probability and sample-rate
functions.
-/
abbrev paper_lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_monotone_continuity_interval_leftTail_uniformExponentialRateCertificate_on_closed_upper_box :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_monotone_continuity_interval_leftTail_uniformExponentialRateCertificate_on_closed_upper_box

/--
Lemma C.4 bounded strict-pair monotone-interval bridge from a left-tail
uniform exponential certificate, with sample-rate positivity localized to the
interior interval.
-/
abbrev paper_lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_monotone_continuity_interval_leftTail_uniformExponentialRateCertificate_on_closed_upper_box_of_Ioo :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_monotone_continuity_interval_leftTail_uniformExponentialRateCertificate_on_closed_upper_box_of_Ioo

/--
Lemma C.4 bounded strict-pair monotone-interval bridge from pointwise binary
Cramer certificates. Monotonicity supplies the interior continuity point, and
the large-deviation library extracts the needed positive-measure lower-bound
subset.
-/
abbrev paper_lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_monotone_continuity_interval_pointwise_on_closed_upper_box_of_Icc :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_boundedStrictUpperPair_floorPkComplementError_has_zero_rate_of_monotone_continuity_interval_pointwise_on_closed_upper_box_of_Icc

/--
Lemma C.4 witness-cell positivity bridge for the concrete floor-complement
kernel. This discharges the local-positive-mass side condition used by the
source-kernel reverse branch from positivity of the paper weight near the
diagonal witness point.
-/
abbrev paper_lemmaC4_witnessCell_floorPkComplementError_integral_pos_of_weight_pos_closure_interior :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_witnessCell_floorPkComplementError_integral_pos_of_weight_pos_closure_interior

/--
Lemma C.4 source `W^k` reverse bridge on an arbitrary witness cell, with the
local raw floor-complement integral positivity proved internally.
-/
abbrev paper_lemmaC4_sourceWError_has_zero_rate_of_witnessCell_floorPkComplementError_eq_on_witness_weight_pos :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_sourceWError_has_zero_rate_of_witnessCell_floorPkComplementError_eq_on_witness_weight_pos

/--
Lemma C.4 source `W^k` reverse bridge on an arbitrary witness cell, deriving
the global source upper bound from a bounded nonnegative source kernel.
-/
abbrev paper_lemmaC4_sourceWError_has_zero_rate_of_witnessCell_floorPkComplementError_eq_on_witness_weight_pos_of_bounded_sourceKernel :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_sourceWError_has_zero_rate_of_witnessCell_floorPkComplementError_eq_on_witness_weight_pos_of_bounded_sourceKernel

/--
Lemma C.4 source `W^k` reverse bridge on an arbitrary witness cell, deriving
source product integrability and the global upper bound from a measurable
bounded nonnegative source kernel.
-/
abbrev paper_lemmaC4_sourceWError_has_zero_rate_of_witnessCell_floorPkComplementError_eq_on_witness_weight_pos_of_bounded_measurable_sourceKernel :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_sourceWError_has_zero_rate_of_witnessCell_floorPkComplementError_eq_on_witness_weight_pos_of_bounded_measurable_sourceKernel

/--
Lemma C.4 witness-cell source-error bridge for the concrete raw
floor-complement kernel: once the source identifies `W^k` with the strict
ordered-pair integral of the raw `1 - P_k` error, the witness-cell reverse
branch gives exact exponential rate zero. This specializes the source kernel
and discharges the previous auxiliary equality premise on the witness cell.
-/
abbrev paper_lemmaC4_rawSourceWError_has_zero_rate_of_witnessCell_floorPkComplementError_weight_pos :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_rawSourceWError_has_zero_rate_of_witnessCell_floorPkComplementError_weight_pos

/--
Lemma C.4 monotone-interval source bridge: once the source global error kernel
agrees with the raw floor-complement kernel on the witness interval, the
reverse zero-rate conclusion follows without a separate local-positivity
premise.
-/
abbrev paper_lemmaC4_source_strictUpperPair_integral_has_zero_rate_of_monotone_interval_eq_on_witness_weight_pos :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_source_strictUpperPair_integral_has_zero_rate_of_monotone_interval_eq_on_witness_weight_pos

/--
Lemma C.4 monotone-interval source bridge with the source upper bound derived
from a uniformly bounded nonnegative source kernel.
-/
abbrev paper_lemmaC4_source_strictUpperPair_integral_has_zero_rate_of_monotone_interval_eq_on_witness_weight_pos_of_bounded_sourceKernel :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_source_strictUpperPair_integral_has_zero_rate_of_monotone_interval_eq_on_witness_weight_pos_of_bounded_sourceKernel

/--
Lemma C.4 monotone-interval source bridge deriving source product
integrability and the global upper bound from a measurable bounded
nonnegative source kernel.
-/
abbrev paper_lemmaC4_source_strictUpperPair_integral_has_zero_rate_of_monotone_interval_eq_on_witness_weight_pos_of_bounded_measurable_sourceKernel :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_source_strictUpperPair_integral_has_zero_rate_of_monotone_interval_eq_on_witness_weight_pos_of_bounded_measurable_sourceKernel

/--
Lemma C.4 monotone-interval source `W^k` bridge deriving source product
integrability and the global upper bound from a measurable bounded
nonnegative source kernel.
-/
abbrev paper_lemmaC4_sourceWError_has_zero_rate_of_monotone_interval_eq_on_witness_weight_pos_of_bounded_measurable_sourceKernel :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_sourceWError_has_zero_rate_of_monotone_interval_eq_on_witness_weight_pos_of_bounded_measurable_sourceKernel

/--
Lemma C.4 source-error bridge for the concrete raw floor-complement kernel:
once the source identifies `W^k` with the strict ordered-pair integral of the
raw `1 - P_k` error, the non-piecewise monotone interval obstruction gives
exact exponential rate zero. This specializes the source kernel and discharges
the previous auxiliary `sourceKernel = raw floor-complement` premise.
-/
abbrev paper_lemmaC4_rawSourceWError_has_zero_rate_of_monotone_interval_weight_pos :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_rawSourceWError_has_zero_rate_of_monotone_interval_weight_pos

/--
Lemma C.4 raw source-error bridge with local witness-interval weight
integrability and nonnegativity derived from the global strict ordered-pair
source assumptions.
-/
abbrev paper_lemmaC4_rawSourceWError_has_zero_rate_of_monotone_interval_global_weight_pos :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_rawSourceWError_has_zero_rate_of_monotone_interval_global_weight_pos

/--
Lemma C.4 source-facing non-piecewise reverse bridge: once the source's
non-piecewise branch supplies a bounded monotone witness interval, the raw
global `W^k` error has exact exponential rate zero.
-/
abbrev paper_lemmaC4_rawSourceWError_has_zero_rate_of_nonpiecewise_monotone_interval_witness :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_rawSourceWError_has_zero_rate_of_nonpiecewise_monotone_interval_witness

/--
Lemma C.4 source-facing non-piecewise reverse bridge for the source-defined
raw global `W^k` error.
-/
abbrev paper_lemmaC4RawStrictUpperPairSourceWError_has_zero_rate_of_nonpiecewise_monotone_interval_witness :=
  GJ19OptimalBinaryRatingSystems.lemmaC4RawStrictUpperPairSourceWError_has_zero_rate_of_nonpiecewise_monotone_interval_witness

/--
Lemma C.4 reverse branch for the source-defined raw global `W^k` error under
the concrete local-constant interval convention: a monotone rule that is not
locally constant on a positive interior interval has exact exponential rate
zero.
-/
abbrev paper_lemmaC4RawStrictUpperPairSourceWError_has_zero_rate_of_not_locallyConstantOnIoo :=
  GJ19OptimalBinaryRatingSystems.lemmaC4RawStrictUpperPairSourceWError_has_zero_rate_of_not_locallyConstantOnIoo

/--
Lemma C.4 reverse branch for the source-defined raw global `W^k` error under
constant objective weight and uniform sampling rate: local nonconstancy on a
positive interior interval gives exact exponential rate zero.
-/
abbrev paper_lemmaC4RawStrictUpperPairSourceWError_const_weight_uniform_sampleRate_has_zero_rate_of_not_locallyConstantOnIoo :=
  GJ19OptimalBinaryRatingSystems.lemmaC4RawStrictUpperPairSourceWError_const_weight_uniform_sampleRate_has_zero_rate_of_not_locallyConstantOnIoo

/--
Lemma C.4 reverse branch in no-positive-rate form under constant objective
weight and uniform sampling rate: local nonconstancy on a positive interior
interval rules out every positive exponential-rate certificate.
-/
abbrev paper_lemmaC4RawStrictUpperPairSourceWError_const_weight_uniform_sampleRate_no_positive_exponential_rate_of_not_locallyConstantOnIoo :=
  GJ19OptimalBinaryRatingSystems.lemmaC4RawStrictUpperPairSourceWError_const_weight_uniform_sampleRate_no_positive_exponential_rate_of_not_locallyConstantOnIoo

/--
Lemma C.4 source-shrink bridge: a locally regular diagonal point in the
non-piecewise branch yields the bounded monotone witness interval used by the
reverse zero-rate proof.
-/
abbrev paper_lemmaC4_nonpiecewise_monotone_interval_witness_of_eventually_regular_continuity_point :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_nonpiecewise_monotone_interval_witness_of_eventually_regular_continuity_point

/--
Lemma C.4 source-facing non-piecewise reverse bridge with the witness interval
derived from one local regularity point.
-/
abbrev paper_lemmaC4_rawSourceWError_has_zero_rate_of_nonpiecewise_local_regularity_witness :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_rawSourceWError_has_zero_rate_of_nonpiecewise_local_regularity_witness

/--
Lemma C.4 source-facing positive-rate iff for the raw global `W^k` error,
conditional exactly on the source's piecewise forward construction and its
non-piecewise monotone witness-interval convention.
-/
abbrev paper_lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_rawSourceWError_nonpiecewise_witness :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_rawSourceWError_nonpiecewise_witness

/--
Lemma C.4 source-facing positive-rate iff for the source-defined raw global
`W^k` error, conditional exactly on the source's piecewise forward
construction and its non-piecewise monotone witness-interval convention.
-/
abbrev paper_lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_defined_rawSourceWError_nonpiecewise_witness :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_defined_rawSourceWError_nonpiecewise_witness

/--
Lemma C.4 source-facing positive-rate iff with the non-piecewise reverse
branch derived from one local regularity point.
-/
abbrev paper_lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_rawSourceWError_nonpiecewise_local_regularity_witness :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_rawSourceWError_nonpiecewise_local_regularity_witness

/--
Lemma C.4 source-facing positive-rate iff for the source-defined raw global
`W^k` error, with the non-piecewise reverse branch derived from one local
regularity point.
-/
abbrev paper_lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_defined_rawSourceWError_nonpiecewise_local_regularity_witness :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_defined_rawSourceWError_nonpiecewise_local_regularity_witness

/--
Lemma C.4 source-facing positive-rate iff for the source-defined raw global
`W^k` error, with the non-piecewise reverse branch derived from one source
continuity point.
-/
abbrev paper_lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_defined_rawSourceWError_nonpiecewise_continuity_point_witness :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_defined_rawSourceWError_nonpiecewise_continuity_point_witness

/--
Lemma C.4 source-facing positive-rate iff for the source-defined raw global
`W^k` error under the monotone positive-interval witness convention.
-/
abbrev paper_lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_defined_rawSourceWError_nonpiecewise_monotone_positive_interval_witness :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_piecewise_constant_iff_exists_positive_exponential_rate_of_defined_rawSourceWError_nonpiecewise_monotone_positive_interval_witness

/--
Lemma C.4 paper-local positive-support source model: finite range of the
monotone success-probability rule on the supported quality interval is
equivalent to the existence of a positive exponential-rate certificate for the
raw strict-pair `W^k` error.  The reverse direction is derived from the
positive-support interval model rather than assumed as a certificate; the
forward direction is the finite-step positive-rate construction.

Source status: formalized under the explicit positive-support interval source
model and the paper's finite-range reading of piecewise constancy.
-/
abbrev paper_lemmaC4_rawSourcePositiveSupportIntervalModel_finiteRange_iff_exists_positive_exponential_rate :=
  @GJ19OptimalBinaryRatingSystems.lemmaC4_rawSourcePositiveSupportIntervalModel_finiteRange_iff_exists_positive_exponential_rate

/--
Lemma C.4 paper-local positive-support source model in the source-defined
tie-erased `Wbar_k` convention for the concrete raw strict-pair `1 - P_k`
kernel.  This is the same finite-range/positive-rate equivalence as the raw
source-model theorem, packaged under the paper's displayed `Wbar_k` integral
name.

Source status: formalized under the explicit positive-support interval source
model and the paper's finite-range reading of piecewise constancy.
-/
abbrev paper_lemmaC4_rawSourcePositiveSupportIntervalModel_finiteRange_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_raw_floorPkComplementError :=
  @GJ19OptimalBinaryRatingSystems.lemmaC4_rawSourcePositiveSupportIntervalModel_finiteRange_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_raw_floorPkComplementError

/--
Lemma C.4 paper-local positive-support source model with the finite-level
forward branch realized by the explicit endpoint/cutpoint model.  The forward
direction derives the positive rate certificate from source-realization
equality with `theorem31SourceWbar`, rather than assuming an opaque
certificate.

Source status: formalized under the explicit positive-support interval model
and finite-level source-realization equality.
-/
abbrev paper_lemmaC4_rawSourcePositiveSupportIntervalModel_finiteRange_iff_exists_positive_exponential_rate_of_appropriate_finite_levels_rawSourceWError_eq :=
  @GJ19OptimalBinaryRatingSystems.lemmaC4_rawSourcePositiveSupportIntervalModel_finiteRange_iff_exists_positive_exponential_rate_of_appropriate_finite_levels_rawSourceWError_eq

/--
Lemma C.4 selected-source coordinate convention: the source strict-pair
integral uses `(high, low)` ordered pairs, while the finite selected-pair
partition is indexed as `(low, high)`.

Source status: formalized coordinate-map convention for the structured C.4
source-realization interface.
-/
abbrev paper_theorem31_selected_source_coordinate_map :=
  GJ19OptimalBinaryRatingSystems.theorem31SelectedSourceCoordinateMap

/--
Lemma C.4 selected-source coordinate convention preserves product measure
whenever the one-dimensional source measure is s-finite.

Source status: formalized measure-preserving field for the selected-source
coordinate map under the standard s-finiteness hypothesis.
-/
abbrev paper_theorem31_selected_source_coordinate_map_measurePreserving :=
  @GJ19OptimalBinaryRatingSystems.theorem31SelectedSourceCoordinateMap_measurePreserving

/--
Lemma C.4 selected finite-level support is measurable.

Source status: formalized measurability field for the selected-source support.
-/
abbrev paper_theorem31_selected_source_support_measurable :=
  @GJ19OptimalBinaryRatingSystems.theorem31SelectedSourceSupport_measurable

/--
Lemma C.4 selected-support orientation: pulling the finite selected `(low,
high)` support back through the selected-source coordinate map places it
inside the source strict-pair `(high, low)` domain.

Source status: formalized selected-support pullback containment field.
-/
abbrev paper_theorem31_selected_source_coordinate_map_preimage_selectedSourceSupport_subset_strictUpperPairSet :=
  @GJ19OptimalBinaryRatingSystems.theorem31SelectedSourceCoordinateMap_preimage_selectedSourceSupport_subset_strictUpperPairSet

/--
Lemma C.4 source-realization interface: the tie-erased strict-pair source
integral is identified with the selected endpoint/cutpoint integral by visible
facts: the selected support is measurable, its pullback under the source-to-
target coordinate map lies in the strict ordered-pair source region, the source
and target integrands agree on selected cross-level cells after that map, and
the source integrand is zero on remaining strict ordered-pair cells.

Source status: formalized source-identification interface; callers still need
to prove the mapped on-support agreement and zero-off-support fields from
their concrete continuum source model; the support measurability,
s-finite coordinate-map preservation, and selected-support pullback
containment fields are exposed separately above.
-/
abbrev paper_lemmaC4_tieErased_selected_integral_realization :=
  GJ19OptimalBinaryRatingSystems.LemmaC4TieErasedSelectedIntegralRealization

/--
Lemma C.4 source-realization constructor: measure-preserving coordinate-map
data, selected-support pullback containment, pointwise mapped on-support
source/target agreement, and pointwise zero contribution off the selected
support imply the structured selected-integral realization.

Source status: formalized proof-facing constructor for the finite-level
source-identification fields.
-/
abbrev paper_lemmaC4_tieErased_selected_integral_realization_of_pointwise :=
  @GJ19OptimalBinaryRatingSystems.lemmaC4TieErasedSelectedIntegralRealization_of_pointwise

/--
Lemma C.4 selected-source realization constructor specialized to the Theorem
3.1 finite selected-pair support: the coordinate-map, support measurability,
and selected-support pullback-containment fields are discharged, leaving only
mapped on-support integrand agreement and zero-off-support tie-erasure fields.

Source status: formalized proof-facing constructor for the remaining
source-identification fields.
-/
abbrev paper_lemmaC4_tieErased_selected_integral_realization_theorem31_of_pointwise :=
  @GJ19OptimalBinaryRatingSystems.lemmaC4TieErasedSelectedIntegralRealization_theorem31_of_pointwise

/--
Lemma C.4 canonical pullback source weight: target finite-level weights are
transported through the selected-source coordinate map.

Source status: formalized source-convention adapter.
-/
abbrev paper_theorem31_selected_pullback_source_weight :=
  GJ19OptimalBinaryRatingSystems.theorem31SelectedPullbackSourceWeight

/--
Lemma C.4 canonical pullback source kernel: the selected finite-level target
kernel is transported through the selected-source coordinate map and erased
off selected cross-level support.

Source status: formalized source-convention adapter.
-/
abbrev paper_theorem31_selected_pullback_source_kernel :=
  @GJ19OptimalBinaryRatingSystems.theorem31SelectedPullbackSourceKernel

/--
Lemma C.4 canonical pullback source realization: under the pullback source
weight/kernel convention, the structured selected-source realization fields
are all closed.

Source status: formalized for the canonical selected pullback source
convention; relating a separate raw continuum source model to this convention
remains source-model work.
-/
abbrev paper_lemmaC4_tieErased_selected_integral_realization_theorem31_pullback_source :=
  @GJ19OptimalBinaryRatingSystems.lemmaC4TieErasedSelectedIntegralRealization_theorem31_pullback_source

/--
Lemma C.4 selected-source realization from pointwise equality with the
canonical pullback convention: a caller-supplied source model realizes the
selected finite-level source when its weight and kernel equal the selected
pullbacks.

Source status: formalized source-identification reducer; the remaining source
work is proving these pointwise equalities for a raw continuum model.
-/
abbrev paper_lemmaC4_tieErased_selected_integral_realization_theorem31_of_eq_pullback_source :=
  @GJ19OptimalBinaryRatingSystems.lemmaC4TieErasedSelectedIntegralRealization_theorem31_of_eq_pullback_source

/--
Lemma C.4 raw floor-complement realization from pointwise equality with the
canonical pullback convention.

Source status: formalized source-identification reducer for the concrete raw
floor-complement kernel.
-/
abbrev paper_lemmaC4_tieErased_selected_integral_realization_theorem31_raw_floorPkComplementError_of_eq_pullback_source :=
  @GJ19OptimalBinaryRatingSystems.lemmaC4TieErasedSelectedIntegralRealization_theorem31_raw_floorPkComplementError_of_eq_pullback_source

/--
Lemma C.4 source-realization congruence: the structured selected-support
indicator interface implies eventual equality between the paper's tie-erased
source sequence and the selected-support integral.

Source status: formalized integral-congruence bridge.
-/
abbrev paper_lemmaC4_tieErasedSourceWbar_eventually_eq_selectedIntegral_of_realization :=
  @GJ19OptimalBinaryRatingSystems.lemmaC4TieErasedSourceWbar_eventually_eq_selectedIntegral_of_realization

/--
Lemma C.4 source-realization congruence specialized to the finite-level
endpoint/cutpoint `theorem31SourceWbar` convention.

Source status: formalized integral-congruence bridge to the finite-level
source integral.
-/
abbrev paper_lemmaC4_tieErasedSourceWbar_eventually_eq_theorem31SourceWbar_of_selected_realization :=
  @GJ19OptimalBinaryRatingSystems.lemmaC4TieErasedSourceWbar_eventually_eq_theorem31SourceWbar_of_selected_realization

/--
Lemma C.4 canonical pullback source equality: the source-defined tie-erased
sequence for the canonical pullback source convention is eventually exactly
the finite-level `theorem31SourceWbar` sequence.

Source status: formalized for the canonical selected pullback source
convention.
-/
abbrev paper_lemmaC4_tieErasedSourceWbar_eventually_eq_theorem31SourceWbar_of_theorem31_pullback_source :=
  @GJ19OptimalBinaryRatingSystems.lemmaC4TieErasedSourceWbar_eventually_eq_theorem31SourceWbar_of_theorem31_pullback_source

/--
Lemma C.4 finite-level forward branch when the source tie-erased sequence is
the finite selected-source `theorem31SourceWbar` sequence plus an eventually
zero residual.

Source status: formalized residual-erasure bridge; residuals must be exactly
eventually zero, not merely zero-rate.
-/
abbrev paper_lemmaC4_appropriate_finite_levels_weighted_tieErasedSourceWbar_rate_certificate_of_eventually_eq_add_eventually_zero :=
  @GJ19OptimalBinaryRatingSystems.lemmaC4_appropriate_finite_levels_weighted_tieErasedSourceWbar_rate_certificate_of_eventually_eq_add_eventually_zero

/--
Lemma C.4 finite-level forward branch for the canonical selected pullback
source convention: the weighted finite-level source model yields endpoint
levels and a positive exact-rate certificate for the source-defined tie-erased
pullback sequence.

Source status: formalized for the canonical selected pullback source
convention.
-/
abbrev paper_lemmaC4_appropriate_finite_levels_weighted_pullback_source_rate_certificate :=
  @GJ19OptimalBinaryRatingSystems.lemmaC4_appropriate_finite_levels_weighted_pullback_source_rate_certificate

/--
Lemma C.4 finite-level forward branch for the canonical selected pullback
source convention with constant objective weight.

Source status: formalized for the canonical selected pullback source
convention.
-/
abbrev paper_lemmaC4_appropriate_finite_levels_const_weight_pullback_source_rate_certificate :=
  @GJ19OptimalBinaryRatingSystems.lemmaC4_appropriate_finite_levels_const_weight_pullback_source_rate_certificate

/--
Lemma C.4 finite-level forward branch for the paper's source `\bar P_k`
kernel: under the structured selected-realization interface, the source
`W-W_k` sequence has a positive exact-rate certificate without identifying it
with a raw all-strict-pairs complement kernel.

Source status: formalized for arbitrary source kernels once the selected-
support source realization fields are supplied.
-/
abbrev paper_lemmaC4_appropriate_finite_levels_weighted_sourcePbarWbar_rate_certificate_of_selected_realization :=
  @GJ19OptimalBinaryRatingSystems.lemmaC4_appropriate_finite_levels_weighted_sourcePbarWbar_rate_certificate_of_selected_realization

/--
Lemma C.4 paper-local positive-support source model in the tie-erased
`Wbar_k` convention, with the finite-level forward branch realized by
eventual equality with the endpoint/cutpoint `theorem31SourceWbar` integral.

Source status: formalized under the explicit positive-support interval model
and finite-level source-realization equality for the tie-erased source
sequence.
-/
abbrev paper_lemmaC4_rawSourcePositiveSupportIntervalModel_finiteRange_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_appropriate_finite_levels_eq :=
  @GJ19OptimalBinaryRatingSystems.lemmaC4_rawSourcePositiveSupportIntervalModel_finiteRange_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_appropriate_finite_levels_eq

/--
Lemma C.4 paper-local positive-support source model in the tie-erased
`Wbar_k` convention, with the finite-level forward branch realized by the
structured selected-support indicator source-realization interface.

Source status: formalized under the explicit positive-support interval model
and structured finite-level source-realization fields.
-/
abbrev paper_lemmaC4_rawSourcePositiveSupportIntervalModel_finiteRange_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_selected_realization :=
  @GJ19OptimalBinaryRatingSystems.lemmaC4_rawSourcePositiveSupportIntervalModel_finiteRange_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_selected_realization

/--
Lemma C.4 paper-local positive-support source model in the tie-erased
`Wbar_k` convention, with the structured selected realization reduced to
pointwise equality with the canonical pullback weight and raw floor-complement
kernel.

Source status: formalized under explicit pointwise source-identification
equalities.
-/
abbrev paper_lemmaC4_rawSourcePositiveSupportIntervalModel_finiteRange_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_raw_eq_pullback_source :=
  @GJ19OptimalBinaryRatingSystems.lemmaC4_rawSourcePositiveSupportIntervalModel_finiteRange_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_raw_eq_pullback_source

/--
Lemma C.4 source convention: the raw positive-support source model is
identified with the canonical selected finite-level pullback source.  The
kernel field includes the tie-erasure convention outside selected cross-level
support.

Source status: explicit source-model convention; this is the remaining raw
model identification needed to use the selected-pullback C.4 bridge.
-/
abbrev paper_lemmaC4_rawSource_selected_pullback_convention :=
  @GJ19OptimalBinaryRatingSystems.LemmaC4RawSourceSelectedPullbackConvention

/--
Lemma C.4 paper-local positive-support source model under the named selected
pullback convention.

Source status: formalized conditional on the explicit selected-pullback source
convention, which identifies the raw weight and floor-complement kernel with
the selected finite-level pullback source.
-/
abbrev paper_lemmaC4_rawSourcePositiveSupportIntervalModel_finiteRange_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_selected_pullback_convention :=
  @GJ19OptimalBinaryRatingSystems.lemmaC4_rawSourcePositiveSupportIntervalModel_finiteRange_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_selected_pullback_convention

/--
Lemma C.4 paper-local finite-step source model in the tie-erased `Wbar_k`
convention, with the finite-level forward branch realized by eventual equality
with the endpoint/cutpoint `theorem31SourceWbar` integral.

Source status: formalized under the explicit positive-support interval model
and finite-level source-realization equality for the tie-erased source
sequence.
-/
abbrev paper_lemmaC4_rawSourcePositiveSupportIntervalModel_finiteStep_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_appropriate_finite_levels_eq :=
  @GJ19OptimalBinaryRatingSystems.lemmaC4_rawSourcePositiveSupportIntervalModel_finiteStep_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_appropriate_finite_levels_eq

/--
Lemma C.4 paper-local finite-step source model in the tie-erased `Wbar_k`
convention, with the finite-level forward branch realized by the structured
support/integrand a.e. source-realization interface.

Source status: formalized under the explicit positive-support interval model
and structured finite-level source-realization fields.
-/
abbrev paper_lemmaC4_rawSourcePositiveSupportIntervalModel_finiteStep_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_selected_realization :=
  @GJ19OptimalBinaryRatingSystems.lemmaC4_rawSourcePositiveSupportIntervalModel_finiteStep_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_selected_realization

/--
Lemma C.4 paper-local finite-step iff for the paper's source `\bar P_k`
kernel.  The forward direction uses selected-support realization of `W-W_k`;
the reverse direction uses the continuity-point zero-rate obstruction for the
same bounded source kernel.  This is the source-faithful C.4 route that avoids
treating same-bin/tie terms as raw strict-pair errors.

Source status: formalized under visible bounded-source-kernel Cramer-rate and
selected-realization hypotheses.
-/
abbrev paper_lemmaC4_rawSourcePositiveSupportIntervalModel_finiteStep_iff_exists_positive_exponential_rate_of_sourcePbar_selected_realization :=
  @GJ19OptimalBinaryRatingSystems.lemmaC4_rawSourcePositiveSupportIntervalModel_finiteStep_iff_exists_positive_exponential_rate_of_sourcePbar_selected_realization

/--
Lemma C.4 paper-local finite-step positive-support source model in the
tie-erased `Wbar_k` convention, with source realization reduced to pointwise
equality with the canonical pullback source convention.

Source status: formalized under explicit pointwise source-identification
equalities.
-/
abbrev paper_lemmaC4_rawSourcePositiveSupportIntervalModel_finiteStep_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_raw_eq_pullback_source :=
  @GJ19OptimalBinaryRatingSystems.lemmaC4_rawSourcePositiveSupportIntervalModel_finiteStep_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_raw_eq_pullback_source

/--
Lemma C.4 paper-local finite-step positive-support source model under the
named selected-pullback convention.

Source status: formalized conditional on the explicit selected-pullback source
convention, including tie-erasure outside selected cross-level support.
-/
abbrev paper_lemmaC4_rawSourcePositiveSupportIntervalModel_finiteStep_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_selected_pullback_convention :=
  @GJ19OptimalBinaryRatingSystems.lemmaC4_rawSourcePositiveSupportIntervalModel_finiteStep_iff_exists_positive_exponential_rate_of_tieErasedSourceWbar_selected_pullback_convention

/--
Lemma C.4 monotone non-finite-range reverse consequence from explicit
positive-support fields: the source regularity, positivity, and non-finite
range hypotheses build the local positive-support model and rule out every
positive exponential-rate certificate for the tie-erased `Wbar_k` sequence.

Source status: formalized field-level reverse branch.  The remaining global
source-model work is deriving these positive-support fields and the
finite-level source-realization equality from the paper's concrete continuum
objects.
-/
abbrev paper_lemmaC4_global_monotone_nonfiniteRange_tieErasedWbar_no_positive_rate_of_positiveSupportInterval_fields :=
  @GJ19OptimalBinaryRatingSystems.lemmaC4_global_monotone_nonfiniteRange_tieErasedWbar_no_positive_rate_of_positiveSupportInterval_fields

/--
Lemma C.4 exact-zero-rate reverse branch for the concrete raw floor-complement
`Wbar_k` convention from explicit positive-support fields and non-finite
range of the monotone success-probability rule.
-/
abbrev paper_lemmaC4_global_monotone_nonfiniteRange_tieErasedWbar_has_zero_rate_of_positiveSupportInterval_fields_raw_floorPkComplementError :=
  @GJ19OptimalBinaryRatingSystems.lemmaC4_global_monotone_nonfiniteRange_tieErasedWbar_has_zero_rate_of_positiveSupportInterval_fields_raw_floorPkComplementError

/--
Lemma C.4 exact-zero-rate reverse branch for monotone rules under the
finite-step/order-convex-fiber reading of piecewise constancy.  Finite range
implies finite-stepness for monotone functions, so a non-finite-step source
rule forces exact zero rate for the concrete tie-erased raw floor-complement
`Wbar_k`.
-/
abbrev paper_lemmaC4_global_monotone_nonfiniteStep_tieErasedWbar_has_zero_rate_of_positiveSupportInterval_fields_raw_floorPkComplementError :=
  @GJ19OptimalBinaryRatingSystems.lemmaC4_global_monotone_nonfiniteStep_tieErasedWbar_has_zero_rate_of_positiveSupportInterval_fields_raw_floorPkComplementError

/--
No-positive-rate companion to the finite-step exact-zero reverse branch.
-/
abbrev paper_lemmaC4_global_monotone_nonfiniteStep_tieErasedWbar_no_positive_rate_of_positiveSupportInterval_fields_raw_floorPkComplementError :=
  @GJ19OptimalBinaryRatingSystems.lemmaC4_global_monotone_nonfiniteStep_tieErasedWbar_no_positive_rate_of_positiveSupportInterval_fields_raw_floorPkComplementError

/--
Lemma C.4 exact-zero-rate reverse branch from non-finite range under the
primitive one-dimensional positive-mass convention.
-/
abbrev paper_lemmaC4_global_monotone_nonfiniteRange_tieErasedWbar_has_zero_rate_of_theta_openPos_fields_raw_floorPkComplementError :=
  @GJ19OptimalBinaryRatingSystems.lemmaC4_global_monotone_nonfiniteRange_tieErasedWbar_has_zero_rate_of_theta_openPos_fields_raw_floorPkComplementError

/--
No-positive-rate companion to the one-dimensional positive-mass non-finite
range reverse branch.
-/
abbrev paper_lemmaC4_global_monotone_nonfiniteRange_tieErasedWbar_no_positive_rate_of_theta_openPos_fields_raw_floorPkComplementError :=
  @GJ19OptimalBinaryRatingSystems.lemmaC4_global_monotone_nonfiniteRange_tieErasedWbar_no_positive_rate_of_theta_openPos_fields_raw_floorPkComplementError

/--
Lemma C.4 exact-zero-rate reverse branch for the paper's constant-weight,
uniform-sampling source normalization under the primitive one-dimensional
positive-mass convention.
-/
abbrev paper_lemmaC4_global_monotone_nonfiniteRange_tieErasedWbar_const_weight_uniform_sampleRate_has_zero_rate_of_theta_openPos_raw_floorPkComplementError :=
  @GJ19OptimalBinaryRatingSystems.lemmaC4_global_monotone_nonfiniteRange_tieErasedWbar_const_weight_uniform_sampleRate_has_zero_rate_of_theta_openPos_raw_floorPkComplementError

/--
No-positive-rate companion to the constant-weight, uniform-sampling
one-dimensional positive-mass Lemma C.4 reverse branch.
-/
abbrev paper_lemmaC4_global_monotone_nonfiniteRange_tieErasedWbar_const_weight_uniform_sampleRate_no_positive_rate_of_theta_openPos_raw_floorPkComplementError :=
  @GJ19OptimalBinaryRatingSystems.lemmaC4_global_monotone_nonfiniteRange_tieErasedWbar_const_weight_uniform_sampleRate_no_positive_rate_of_theta_openPos_raw_floorPkComplementError

/--
Lemma C.4 exact-zero-rate reverse branch from non-finite-stepness under the
primitive one-dimensional positive-mass convention.
-/
abbrev paper_lemmaC4_global_monotone_nonfiniteStep_tieErasedWbar_has_zero_rate_of_theta_openPos_fields_raw_floorPkComplementError :=
  @GJ19OptimalBinaryRatingSystems.lemmaC4_global_monotone_nonfiniteStep_tieErasedWbar_has_zero_rate_of_theta_openPos_fields_raw_floorPkComplementError

/--
No-positive-rate companion to the one-dimensional positive-mass
non-finite-step reverse branch.
-/
abbrev paper_lemmaC4_global_monotone_nonfiniteStep_tieErasedWbar_no_positive_rate_of_theta_openPos_fields_raw_floorPkComplementError :=
  @GJ19OptimalBinaryRatingSystems.lemmaC4_global_monotone_nonfiniteStep_tieErasedWbar_no_positive_rate_of_theta_openPos_fields_raw_floorPkComplementError

/--
Lemma C.4 exact-zero-rate reverse branch for the paper's constant-weight,
uniform-sampling source normalization from non-finite-stepness.
-/
abbrev paper_lemmaC4_global_monotone_nonfiniteStep_tieErasedWbar_const_weight_uniform_sampleRate_has_zero_rate_of_theta_openPos_raw_floorPkComplementError :=
  @GJ19OptimalBinaryRatingSystems.lemmaC4_global_monotone_nonfiniteStep_tieErasedWbar_const_weight_uniform_sampleRate_has_zero_rate_of_theta_openPos_raw_floorPkComplementError

/--
No-positive-rate companion to the constant-weight, uniform-sampling
non-finite-step C.4 reverse branch.
-/
abbrev paper_lemmaC4_global_monotone_nonfiniteStep_tieErasedWbar_const_weight_uniform_sampleRate_no_positive_rate_of_theta_openPos_raw_floorPkComplementError :=
  @GJ19OptimalBinaryRatingSystems.lemmaC4_global_monotone_nonfiniteStep_tieErasedWbar_const_weight_uniform_sampleRate_no_positive_rate_of_theta_openPos_raw_floorPkComplementError

/--
Lemma C.4 exact-zero-rate reverse branch from explicit positive-support fields
and the paper's non-piecewise source predicate.  The only semantic bridge is
that finite-range source rules count as piecewise constant on the supported
quality interval.
-/
abbrev paper_lemmaC4_global_monotone_nonpiecewise_tieErasedWbar_has_zero_rate_of_positiveSupportInterval_fields_raw_floorPkComplementError :=
  @GJ19OptimalBinaryRatingSystems.lemmaC4_global_monotone_nonpiecewise_tieErasedWbar_has_zero_rate_of_positiveSupportInterval_fields_raw_floorPkComplementError

/--
No-positive-rate companion to the non-piecewise exact-zero reverse branch.
-/
abbrev paper_lemmaC4_global_monotone_nonpiecewise_tieErasedWbar_no_positive_rate_of_positiveSupportInterval_fields_raw_floorPkComplementError :=
  @GJ19OptimalBinaryRatingSystems.lemmaC4_global_monotone_nonpiecewise_tieErasedWbar_no_positive_rate_of_positiveSupportInterval_fields_raw_floorPkComplementError

/--
Lemma C.4 exact-zero-rate reverse branch with the primitive
one-dimensional positive-mass convention: the theta distribution charges every
nonempty open interval, and the product positive-mass condition is supplied by
mathlib.
-/
abbrev paper_lemmaC4_global_monotone_nonpiecewise_tieErasedWbar_has_zero_rate_of_theta_openPos_fields_raw_floorPkComplementError :=
  @GJ19OptimalBinaryRatingSystems.lemmaC4_global_monotone_nonpiecewise_tieErasedWbar_has_zero_rate_of_theta_openPos_fields_raw_floorPkComplementError

/--
No-positive-rate companion to the one-dimensional positive-mass C.4 reverse
branch.
-/
abbrev paper_lemmaC4_global_monotone_nonpiecewise_tieErasedWbar_no_positive_rate_of_theta_openPos_fields_raw_floorPkComplementError :=
  @GJ19OptimalBinaryRatingSystems.lemmaC4_global_monotone_nonpiecewise_tieErasedWbar_no_positive_rate_of_theta_openPos_fields_raw_floorPkComplementError

/--
Lemma C.4 exact-zero-rate reverse branch for the paper's constant-weight,
uniform-sampling source normalization from the non-piecewise source predicate.
-/
abbrev paper_lemmaC4_global_monotone_nonpiecewise_tieErasedWbar_const_weight_uniform_sampleRate_has_zero_rate_of_theta_openPos_raw_floorPkComplementError :=
  @GJ19OptimalBinaryRatingSystems.lemmaC4_global_monotone_nonpiecewise_tieErasedWbar_const_weight_uniform_sampleRate_has_zero_rate_of_theta_openPos_raw_floorPkComplementError

/--
No-positive-rate companion to the constant-weight, uniform-sampling
non-piecewise C.4 reverse branch.
-/
abbrev paper_lemmaC4_global_monotone_nonpiecewise_tieErasedWbar_const_weight_uniform_sampleRate_no_positive_rate_of_theta_openPos_raw_floorPkComplementError :=
  @GJ19OptimalBinaryRatingSystems.lemmaC4_global_monotone_nonpiecewise_tieErasedWbar_const_weight_uniform_sampleRate_no_positive_rate_of_theta_openPos_raw_floorPkComplementError

/--
Lemma C.4 bounded strict-pair monotone-interval bridge: monotonicity supplies
the interior continuity point, and the remaining normalized-log certificate is
localized to the compact closed coordinate box.
-/
abbrev paper_lemmaC4_boundedStrictUpperPair_integral_has_zero_rate_of_monotone_continuity_interval_boundedKernel_uniformNormalizedLogRateCertificate_on_closed_box :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_boundedStrictUpperPair_integral_has_zero_rate_of_monotone_continuity_interval_boundedKernel_uniformNormalizedLogRateCertificate_on_closed_box

/--
Lemma C.4 bounded strict-pair monotone-interval bridge with probability and
sample-rate positivity localized to the interval.
-/
abbrev paper_lemmaC4_boundedStrictUpperPair_integral_has_zero_rate_of_monotone_continuity_interval_boundedKernel_uniformNormalizedLogRateCertificate_on_closed_box_of_Ioo :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_boundedStrictUpperPair_integral_has_zero_rate_of_monotone_continuity_interval_boundedKernel_uniformNormalizedLogRateCertificate_on_closed_box_of_Ioo

/--
Lemma C.4 selected-cell bridge for the concrete binary floor-complement kernel:
finite-rating bounds discharge the bounded-kernel and weighted-integrability
certificates, leaving measurability and the closed-cell Lipschitz/uniformity
estimate as the analytic input.
-/
abbrev paper_lemmaC4_ordered_quality_pair_piece_floorPkComplementError_has_zero_rate_of_continuity_point_measurableKernel_eventually_lipschitz_on_closed_cell_superset :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_ordered_quality_pair_piece_floorPkComplementError_has_zero_rate_of_continuity_point_measurableKernel_eventually_lipschitz_on_closed_cell_superset

/--
Lemma C.4 selected-cell bridge for the concrete binary floor-complement kernel
from a direct uniform normalized-log certificate on the closed-cell superset.
-/
abbrev paper_lemmaC4_ordered_quality_pair_piece_floorPkComplementError_has_zero_rate_of_continuity_point_measurableKernel_uniformNormalizedLogRateCertificate_on_closed_cell_superset :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_ordered_quality_pair_piece_floorPkComplementError_has_zero_rate_of_continuity_point_measurableKernel_uniformNormalizedLogRateCertificate_on_closed_cell_superset

/--
Lemma C.4 selected-cell bridge from a direct uniform exponential-sandwich
certificate for the concrete binary floor-complement kernel.
-/
abbrev paper_lemmaC4_ordered_quality_pair_piece_floorPkComplementError_has_zero_rate_of_continuity_point_measurableKernel_uniformExponentialRateCertificate_on_closed_cell_superset :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_ordered_quality_pair_piece_floorPkComplementError_has_zero_rate_of_continuity_point_measurableKernel_uniformExponentialRateCertificate_on_closed_cell_superset

/--
Lemma C.4 selected-cell bridge from a left-tail uniform exponential-sandwich
certificate; the finite-rating constant-factor sandwich transfers it to the
floor-complement kernel used by the paper.
-/
abbrev paper_lemmaC4_ordered_quality_pair_piece_floorPkComplementError_has_zero_rate_of_continuity_point_measurableKernel_leftTail_uniformExponentialRateCertificate_on_closed_cell_superset :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_ordered_quality_pair_piece_floorPkComplementError_has_zero_rate_of_continuity_point_measurableKernel_leftTail_uniformExponentialRateCertificate_on_closed_cell_superset

/--
Lemma C.4 selected-cell bridge from the source left-tail normalized-log
Lipschitz hypothesis. Pointwise binary left-tail Cramer certificates are
derived internally; the remaining analytic input is compact-cell Lipschitz
regularity of the normalized log left-tail probabilities.
-/
abbrev paper_lemmaC4_ordered_quality_pair_piece_floorPkComplementError_has_zero_rate_of_continuity_point_measurableKernel_leftTail_eventually_lipschitz_on_closed_cell_superset :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_ordered_quality_pair_piece_floorPkComplementError_has_zero_rate_of_continuity_point_measurableKernel_leftTail_eventually_lipschitz_on_closed_cell_superset

/--
Lemma C.4 selected-cell bridge with binary LDP regularity assumptions localized
to the closed compact cell superset.
-/
abbrev paper_lemmaC4_ordered_quality_pair_piece_floorPkComplementError_has_zero_rate_of_continuity_point_measurableKernel_leftTail_eventually_lipschitz_on_closed_cell_superset_of_compact :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_ordered_quality_pair_piece_floorPkComplementError_has_zero_rate_of_continuity_point_measurableKernel_leftTail_eventually_lipschitz_on_closed_cell_superset_of_compact

/--
Lemma C.4 selected-cell bridge from the source left-tail normalized-log
Lipschitz hypothesis, with kernel measurability derived from continuity of
the success-probability and sample-rate functions.
-/
abbrev paper_lemmaC4_ordered_quality_pair_piece_floorPkComplementError_has_zero_rate_of_continuity_point_leftTail_eventually_lipschitz_on_closed_cell_superset :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_ordered_quality_pair_piece_floorPkComplementError_has_zero_rate_of_continuity_point_leftTail_eventually_lipschitz_on_closed_cell_superset

/--
Lemma C.4 selected high-low cell bridge from the source left-tail
normalized-log Lipschitz hypothesis. The closed-cell probability order is
derived from monotonicity of `β` and the high-low index ordering.
-/
abbrev paper_lemmaC4_ordered_quality_pair_piece_floorPkComplementError_has_zero_rate_of_continuity_point_measurableKernel_leftTail_eventually_lipschitz_on_highLow_closed_cell_superset :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_ordered_quality_pair_piece_floorPkComplementError_has_zero_rate_of_continuity_point_measurableKernel_leftTail_eventually_lipschitz_on_highLow_closed_cell_superset

/--
Lemma C.4 selected high-low cell bridge from the source left-tail
normalized-log Lipschitz hypothesis, with both the closed-cell probability
order and kernel measurability derived internally.
-/
abbrev paper_lemmaC4_ordered_quality_pair_piece_floorPkComplementError_has_zero_rate_of_continuity_point_leftTail_eventually_lipschitz_on_highLow_closed_cell_superset :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_ordered_quality_pair_piece_floorPkComplementError_has_zero_rate_of_continuity_point_leftTail_eventually_lipschitz_on_highLow_closed_cell_superset

/--
Theorem 3.1/C.3 selected-pair constant-kernel bridge: the endpoint-pair
finite error kernel induces a uniform normalized-log certificate on any
continuum parameter set.
-/
theorem paper_binaryEndpointAwarePairRate_floorPkComplementError_uniform_constant_kernel_certificate_of_selected_ordered_pair
    {α : Type*} {m : ℕ}
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hfirst_zero : successProb (firstLevelIndex : Fin (m + 2)) = 0)
    (hlast_one : successProb (lastLevelIndex : Fin (m + 2)) = 1)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_pos_of_not_first :
      ∀ θ : Fin (m + 2), θ.val ≠ 0 → 0 < successProb θ)
    (hprob_lt_one_of_not_last :
      ∀ θ : Fin (m + 2), θ.val ≠ m + 1 → successProb θ < 1)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (component : paperTheorem31OrderedNontrivialPairComponent m)
    (s : Set α) :
    UniformNormalizedLogRateCertificateOn
      (fun k (_x : α) =>
        twoSampleFloorPkComplementErrorProb
          (binaryRatingModel successProb hprob0 hprob1) sampleRate
          component.val.2 component.val.1 k)
      (fun _x : α =>
        binaryEndpointAwarePairRate successProb sampleRate
          component.val.1 component.val.2)
      s :=
  GJ19OptimalBinaryRatingSystems.binaryEndpointAwarePairRate_floorPkComplementError_uniform_constant_kernel_certificate_of_selected_ordered_pair
    successProb sampleRate hprob0 hprob1 hfirst_zero hlast_one hprob_mono
    hprob_pos_of_not_first hprob_lt_one_of_not_last hsample_pos component s

/--
Theorem 3.1/C.3 selected-pair constant-kernel normalized-log bridge using
`BinaryEndpointLevelVector` for the finite binary-model side conditions.
-/
abbrev paper_binaryEndpointAwarePairRate_floorPkComplementError_uniform_constant_kernel_certificate_of_selected_ordered_pair_of_endpointLevelVector
    {α : Type*} {m : ℕ} :=
  GJ19OptimalBinaryRatingSystems.binaryEndpointAwarePairRate_floorPkComplementError_uniform_constant_kernel_certificate_of_selected_ordered_pair_of_endpointLevelVector
    (α := α) (m := m)

/--
Lemma C.3 measurable-partition decomposition: after the continuum objective is
split into finitely many measurable components, component integral rate
certificates aggregate to the minimum component exponent.

Source status: conditional C.3 aggregation lemma; component rate certificates
are visible hypotheses.
-/
theorem paper_lemmaC3_partition_integral_hasExponentialRate_of_min_component_certificates
    {Ω Component : Type*} [MeasurableSpace Ω]
    [Fintype Component] [DecidableEq Component]
    (μ : Measure Ω)
    (P : FiniteMeasurableSetPartition μ Component)
    (errorKernel : ℕ → Ω → ℝ)
    (rate : Component → ℝ)
    (hcomponent_int :
      ∀ k component,
        MeasureTheory.IntegrableOn (errorKernel k) (P.pieceSet component) μ)
    (hcert :
      ∀ component,
        ExponentialRateCertificate
          (fun k : ℕ => P.componentIntegral (errorKernel k) component)
          (rate component))
    (minComponent : Component)
    (hrate_ge : ∀ component, rate minComponent ≤ rate component) :
    HasExponentialRate
      (fun k : ℕ => ∫ x in P.support, errorKernel k x ∂μ)
      (rate minComponent) :=
  GJ19OptimalBinaryRatingSystems.lemmaC3_partition_integral_hasExponentialRate_of_min_component_certificates
    μ P errorKernel rate hcomponent_int hcert minComponent hrate_ge

/--
Lemma C.3 measurable-partition adjacent-dominance bridge: if a selected
adjacent subfamily dominates all component rates, it determines the exponent
of the partitioned continuum objective.

Source status: conditional C.3 adjacent-dominance bridge; component rate
certificates are visible hypotheses.
-/
theorem paper_lemmaC3_partition_integral_hasExponentialRate_of_dominating_adjacent_subfamily
    {Ω Component Adjacent : Type*} [MeasurableSpace Ω]
    [Fintype Component] [DecidableEq Component]
    (μ : Measure Ω)
    (P : FiniteMeasurableSetPartition μ Component)
    (errorKernel : ℕ → Ω → ℝ)
    (rate : Component → ℝ)
    (selectAdjacent : Adjacent → Component)
    (hcomponent_int :
      ∀ k component,
        MeasureTheory.IntegrableOn (errorKernel k) (P.pieceSet component) μ)
    (hcert :
      ∀ component,
        ExponentialRateCertificate
          (fun k : ℕ => P.componentIntegral (errorKernel k) component)
          (rate component))
    (minAdjacent : Adjacent)
    (hadj_min :
      ∀ adj : Adjacent,
        rate (selectAdjacent minAdjacent) ≤ rate (selectAdjacent adj))
    (hadj_dominates :
      ∀ component,
        ∃ adj : Adjacent, rate (selectAdjacent adj) ≤ rate component) :
    HasExponentialRate
      (fun k : ℕ => ∫ x in P.support, errorKernel k x ∂μ)
      (rate (selectAdjacent minAdjacent)) :=
  GJ19OptimalBinaryRatingSystems.lemmaC3_partition_integral_hasExponentialRate_of_dominating_adjacent_subfamily
    μ P errorKernel rate selectAdjacent hcomponent_int hcert minAdjacent
    hadj_min hadj_dominates

/--
Lemma C.3 positive-kernel measurable-partition bridge: componentwise uniform
normalized-log rate limits imply that the weighted partitioned continuum
error integral decays at the minimum component exponent.

Source status: formalized C.3 aggregation bridge from uniform log-rate
convergence to the minimum component exponent.
-/
theorem paper_lemmaC3_partition_integral_hasExponentialRate_of_min_component_uniform_logRate
    {Ω Component : Type*} [MeasurableSpace Ω]
    [Fintype Component] [DecidableEq Component]
    (μ : Measure Ω) [MeasureTheory.IsFiniteMeasure μ]
    (P : FiniteMeasurableSetPartition μ Component)
    (weight : Ω → ℝ) (kernel : ℕ → Ω → ℝ)
    (phi : Component → Ω → ℝ) (rate W : Component → ℝ)
    (hkernel_int :
      ∀ k component,
        MeasureTheory.IntegrableOn (fun x : Ω => weight x * kernel k x)
          (P.pieceSet component) μ)
    (hweight_int :
      ∀ component, MeasureTheory.IntegrableOn weight (P.pieceSet component) μ)
    (hWpos : ∀ component, 0 < W component)
    (hweight_nonneg :
      ∀ component, ∀ᵐ x ∂μ.restrict (P.pieceSet component), 0 ≤ weight x)
    (hweight_bound :
      ∀ component, ∀ᵐ x ∂μ.restrict (P.pieceSet component), weight x ≤ W component)
    (hess :
      ∀ component,
        HasAEEssentialInfimum
          (μ.restrict (P.pieceSet component)) (phi component) (rate component))
    (hweighted_near :
      ∀ component,
        HasPositiveWeightNearAEEssentialInfimum
          (μ.restrict (P.pieceSet component)) weight (phi component) (rate component))
    (hkernel_pos : ∀ k x, 0 < kernel k x)
    (huniform_log :
      ∀ component, ∀ ε > 0,
        ∀ᶠ k : ℕ in Filter.atTop,
          ∀ x : Ω,
            |(-Real.log (kernel k x) / (k : ℝ)) - phi component x| ≤ ε)
    (minComponent : Component)
    (hrate_ge : ∀ component, rate minComponent ≤ rate component) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in P.support, weight x * kernel k x ∂μ)
      (rate minComponent) :=
  GJ19OptimalBinaryRatingSystems.lemmaC3_partition_integral_hasExponentialRate_of_min_component_uniform_logRate
    μ P weight kernel phi rate W hkernel_int hweight_int hWpos
    hweight_nonneg hweight_bound hess hweighted_near hkernel_pos
    huniform_log minComponent hrate_ge

/--
Lemma C.3 positive-kernel adjacent-dominance bridge: componentwise uniform
normalized-log rate limits plus adjacent dominance determine the exponent of
the weighted partitioned continuum error integral.

Source status: formalized C.3 adjacent-dominance aggregation bridge from
uniform log-rate convergence.
-/
theorem paper_lemmaC3_partition_integral_hasExponentialRate_of_dominating_adjacent_subfamily_uniform_logRate
    {Ω Component Adjacent : Type*} [MeasurableSpace Ω]
    [Fintype Component] [DecidableEq Component]
    (μ : Measure Ω) [MeasureTheory.IsFiniteMeasure μ]
    (P : FiniteMeasurableSetPartition μ Component)
    (weight : Ω → ℝ) (kernel : ℕ → Ω → ℝ)
    (phi : Component → Ω → ℝ) (rate W : Component → ℝ)
    (selectAdjacent : Adjacent → Component)
    (hkernel_int :
      ∀ k component,
        MeasureTheory.IntegrableOn (fun x : Ω => weight x * kernel k x)
          (P.pieceSet component) μ)
    (hweight_int :
      ∀ component, MeasureTheory.IntegrableOn weight (P.pieceSet component) μ)
    (hWpos : ∀ component, 0 < W component)
    (hweight_nonneg :
      ∀ component, ∀ᵐ x ∂μ.restrict (P.pieceSet component), 0 ≤ weight x)
    (hweight_bound :
      ∀ component, ∀ᵐ x ∂μ.restrict (P.pieceSet component), weight x ≤ W component)
    (hess :
      ∀ component,
        HasAEEssentialInfimum
          (μ.restrict (P.pieceSet component)) (phi component) (rate component))
    (hweighted_near :
      ∀ component,
        HasPositiveWeightNearAEEssentialInfimum
          (μ.restrict (P.pieceSet component)) weight (phi component) (rate component))
    (hkernel_pos : ∀ k x, 0 < kernel k x)
    (huniform_log :
      ∀ component, ∀ ε > 0,
        ∀ᶠ k : ℕ in Filter.atTop,
          ∀ x : Ω,
            |(-Real.log (kernel k x) / (k : ℝ)) - phi component x| ≤ ε)
    (minAdjacent : Adjacent)
    (hadj_min :
      ∀ adj : Adjacent,
        rate (selectAdjacent minAdjacent) ≤ rate (selectAdjacent adj))
    (hadj_dominates :
      ∀ component,
        ∃ adj : Adjacent, rate (selectAdjacent adj) ≤ rate component) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in P.support, weight x * kernel k x ∂μ)
      (rate (selectAdjacent minAdjacent)) :=
  GJ19OptimalBinaryRatingSystems.lemmaC3_partition_integral_hasExponentialRate_of_dominating_adjacent_subfamily_uniform_logRate
    μ P weight kernel phi rate W selectAdjacent hkernel_int hweight_int
    hWpos hweight_nonneg hweight_bound hess hweighted_near hkernel_pos
    huniform_log minAdjacent hadj_min hadj_dominates

/--
Lemma C.3 continuous-minimizer partition bridge: componentwise uniform log-rate
limits, local continuous minimizers in each cell, local positive cell mass, and
uniformly positive bounded weights imply the minimum-component exponent.
-/
theorem paper_lemmaC3_partition_integral_hasExponentialRate_of_min_component_continuous_min_uniformWeightLower
    {Ω Component : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] [Fintype Component] [DecidableEq Component]
    (μ : Measure Ω) [MeasureTheory.IsFiniteMeasure μ]
    (P : FiniteMeasurableSetPartition μ Component)
    (weight : Ω → ℝ) (kernel : ℕ → Ω → ℝ)
    (phi : Component → Ω → ℝ) (rate W c : Component → ℝ)
    (hkernel_int :
      ∀ k component,
        MeasureTheory.IntegrableOn (fun x : Ω => weight x * kernel k x)
          (P.pieceSet component) μ)
    (hweight_int :
      ∀ component, MeasureTheory.IntegrableOn weight (P.pieceSet component) μ)
    (hWpos : ∀ component, 0 < W component)
    (hcpos : ∀ component, 0 < c component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂μ.restrict (P.pieceSet component), c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂μ.restrict (P.pieceSet component), weight x ≤ W component)
    (x0 : Component → Ω)
    (hmin :
      ∀ component x,
        x ∈ P.pieceSet component → rate component ≤ phi component x)
    (hx0 : ∀ component, phi component (x0 component) = rate component)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (hlocal_pos :
      ∀ component U, IsOpen U → x0 component ∈ U →
        0 < μ (P.pieceSet component ∩ U))
    (hkernel_pos : ∀ k x, 0 < kernel k x)
    (huniform_log :
      ∀ component, ∀ ε > 0,
        ∀ᶠ k : ℕ in Filter.atTop,
          ∀ x : Ω,
            |(-Real.log (kernel k x) / (k : ℝ)) - phi component x| ≤ ε)
    (minComponent : Component)
    (hrate_ge : ∀ component, rate minComponent ≤ rate component) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in P.support, weight x * kernel k x ∂μ)
      (rate minComponent) :=
  GJ19OptimalBinaryRatingSystems.lemmaC3_partition_integral_hasExponentialRate_of_min_component_continuous_min_uniformWeightLower
    μ P weight kernel phi rate W c hkernel_int hweight_int hWpos hcpos
    hweight_lower hweight_bound x0 hmin hx0 hcont hlocal_pos hkernel_pos
    huniform_log minComponent hrate_ge

/--
Lemma C.3 continuous-minimizer adjacent-dominance bridge: the componentwise
continuous-minimizer partition bridge plus adjacent dominance determines the
weighted continuum objective exponent from the minimum adjacent component.
-/
theorem paper_lemmaC3_partition_integral_hasExponentialRate_of_dominating_adjacent_subfamily_continuous_min_uniformWeightLower
    {Ω Component Adjacent : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] [Fintype Component] [DecidableEq Component]
    (μ : Measure Ω) [MeasureTheory.IsFiniteMeasure μ]
    (P : FiniteMeasurableSetPartition μ Component)
    (weight : Ω → ℝ) (kernel : ℕ → Ω → ℝ)
    (phi : Component → Ω → ℝ) (rate W c : Component → ℝ)
    (selectAdjacent : Adjacent → Component)
    (hkernel_int :
      ∀ k component,
        MeasureTheory.IntegrableOn (fun x : Ω => weight x * kernel k x)
          (P.pieceSet component) μ)
    (hweight_int :
      ∀ component, MeasureTheory.IntegrableOn weight (P.pieceSet component) μ)
    (hWpos : ∀ component, 0 < W component)
    (hcpos : ∀ component, 0 < c component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂μ.restrict (P.pieceSet component), c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂μ.restrict (P.pieceSet component), weight x ≤ W component)
    (x0 : Component → Ω)
    (hmin :
      ∀ component x,
        x ∈ P.pieceSet component → rate component ≤ phi component x)
    (hx0 : ∀ component, phi component (x0 component) = rate component)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (hlocal_pos :
      ∀ component U, IsOpen U → x0 component ∈ U →
        0 < μ (P.pieceSet component ∩ U))
    (hkernel_pos : ∀ k x, 0 < kernel k x)
    (huniform_log :
      ∀ component, ∀ ε > 0,
        ∀ᶠ k : ℕ in Filter.atTop,
          ∀ x : Ω,
            |(-Real.log (kernel k x) / (k : ℝ)) - phi component x| ≤ ε)
    (minAdjacent : Adjacent)
    (hadj_min :
      ∀ adj : Adjacent,
        rate (selectAdjacent minAdjacent) ≤ rate (selectAdjacent adj))
    (hadj_dominates :
      ∀ component,
        ∃ adj : Adjacent, rate (selectAdjacent adj) ≤ rate component) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in P.support, weight x * kernel k x ∂μ)
      (rate (selectAdjacent minAdjacent)) :=
  GJ19OptimalBinaryRatingSystems.lemmaC3_partition_integral_hasExponentialRate_of_dominating_adjacent_subfamily_continuous_min_uniformWeightLower
    μ P weight kernel phi rate W c selectAdjacent hkernel_int hweight_int
    hWpos hcpos hweight_lower hweight_bound x0 hmin hx0 hcont hlocal_pos
    hkernel_pos huniform_log minAdjacent hadj_min hadj_dominates

/--
Lemma C.3 closure/interior support bridge: when each continuous component
minimizer lies in the closure of its measurable cell interior, open-positive
ambient measure supplies the local positive-mass condition for the Laplace
step.
-/
theorem paper_lemmaC3_partition_integral_hasExponentialRate_of_min_component_closure_interior_uniformWeightLower
    {Ω Component : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] [Fintype Component] [DecidableEq Component]
    (μ : Measure Ω) [MeasureTheory.IsFiniteMeasure μ]
    [Measure.IsOpenPosMeasure μ]
    (P : FiniteMeasurableSetPartition μ Component)
    (weight : Ω → ℝ) (kernel : ℕ → Ω → ℝ)
    (phi : Component → Ω → ℝ) (rate W c : Component → ℝ)
    (hkernel_int :
      ∀ k component,
        MeasureTheory.IntegrableOn (fun x : Ω => weight x * kernel k x)
          (P.pieceSet component) μ)
    (hweight_int :
      ∀ component, MeasureTheory.IntegrableOn weight (P.pieceSet component) μ)
    (hWpos : ∀ component, 0 < W component)
    (hcpos : ∀ component, 0 < c component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂μ.restrict (P.pieceSet component), c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂μ.restrict (P.pieceSet component), weight x ≤ W component)
    (x0 : Component → Ω)
    (hmin :
      ∀ component x,
        x ∈ P.pieceSet component → rate component ≤ phi component x)
    (hx0 : ∀ component, phi component (x0 component) = rate component)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (hclosure :
      ∀ component, x0 component ∈ closure (interior (P.pieceSet component)))
    (hkernel_pos : ∀ k x, 0 < kernel k x)
    (huniform_log :
      ∀ component, ∀ ε > 0,
        ∀ᶠ k : ℕ in Filter.atTop,
          ∀ x : Ω,
            |(-Real.log (kernel k x) / (k : ℝ)) - phi component x| ≤ ε)
    (minComponent : Component)
    (hrate_ge : ∀ component, rate minComponent ≤ rate component) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in P.support, weight x * kernel k x ∂μ)
      (rate minComponent) :=
  GJ19OptimalBinaryRatingSystems.lemmaC3_partition_integral_hasExponentialRate_of_min_component_closure_interior_uniformWeightLower
    μ P weight kernel phi rate W c hkernel_int hweight_int hWpos hcpos
    hweight_lower hweight_bound x0 hmin hx0 hcont hclosure hkernel_pos
    huniform_log minComponent hrate_ge

/--
Lemma C.3 closure/interior adjacent-dominance bridge: the preferred source
shape for reducing the partitioned continuum objective to adjacent components
once each component rate has a continuous minimizer in the topological support
of its cell.
-/
theorem paper_lemmaC3_partition_integral_hasExponentialRate_of_dominating_adjacent_subfamily_closure_interior_uniformWeightLower
    {Ω Component Adjacent : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] [Fintype Component] [DecidableEq Component]
    (μ : Measure Ω) [MeasureTheory.IsFiniteMeasure μ]
    [Measure.IsOpenPosMeasure μ]
    (P : FiniteMeasurableSetPartition μ Component)
    (weight : Ω → ℝ) (kernel : ℕ → Ω → ℝ)
    (phi : Component → Ω → ℝ) (rate W c : Component → ℝ)
    (selectAdjacent : Adjacent → Component)
    (hkernel_int :
      ∀ k component,
        MeasureTheory.IntegrableOn (fun x : Ω => weight x * kernel k x)
          (P.pieceSet component) μ)
    (hweight_int :
      ∀ component, MeasureTheory.IntegrableOn weight (P.pieceSet component) μ)
    (hWpos : ∀ component, 0 < W component)
    (hcpos : ∀ component, 0 < c component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂μ.restrict (P.pieceSet component), c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂μ.restrict (P.pieceSet component), weight x ≤ W component)
    (x0 : Component → Ω)
    (hmin :
      ∀ component x,
        x ∈ P.pieceSet component → rate component ≤ phi component x)
    (hx0 : ∀ component, phi component (x0 component) = rate component)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (hclosure :
      ∀ component, x0 component ∈ closure (interior (P.pieceSet component)))
    (hkernel_pos : ∀ k x, 0 < kernel k x)
    (huniform_log :
      ∀ component, ∀ ε > 0,
        ∀ᶠ k : ℕ in Filter.atTop,
          ∀ x : Ω,
            |(-Real.log (kernel k x) / (k : ℝ)) - phi component x| ≤ ε)
    (minAdjacent : Adjacent)
    (hadj_min :
      ∀ adj : Adjacent,
        rate (selectAdjacent minAdjacent) ≤ rate (selectAdjacent adj))
    (hadj_dominates :
      ∀ component,
        ∃ adj : Adjacent, rate (selectAdjacent adj) ≤ rate component) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in P.support, weight x * kernel k x ∂μ)
      (rate (selectAdjacent minAdjacent)) :=
  GJ19OptimalBinaryRatingSystems.lemmaC3_partition_integral_hasExponentialRate_of_dominating_adjacent_subfamily_closure_interior_uniformWeightLower
    μ P weight kernel phi rate W c selectAdjacent hkernel_int hweight_int
    hWpos hcpos hweight_lower hweight_bound x0 hmin hx0 hcont hclosure
    hkernel_pos huniform_log minAdjacent hadj_min hadj_dominates

/--
Lemma C.3 closure/interior adjacent-dominance bridge with global constant
weight bounds shared by every partition cell.
-/
theorem paper_lemmaC3_partition_integral_hasExponentialRate_of_dominating_adjacent_subfamily_closure_interior_uniformWeightLower_constBounds
    {Ω Component Adjacent : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] [Fintype Component] [DecidableEq Component]
    (μ : Measure Ω) [MeasureTheory.IsFiniteMeasure μ]
    [Measure.IsOpenPosMeasure μ]
    (P : FiniteMeasurableSetPartition μ Component)
    (weight : Ω → ℝ) (kernel : ℕ → Ω → ℝ)
    (phi : Component → Ω → ℝ) (rate : Component → ℝ)
    (selectAdjacent : Adjacent → Component) {W c : ℝ}
    (hkernel_int :
      ∀ k component,
        MeasureTheory.IntegrableOn (fun x : Ω => weight x * kernel k x)
          (P.pieceSet component) μ)
    (hweight_int :
      ∀ component, MeasureTheory.IntegrableOn weight (P.pieceSet component) μ)
    (hWpos : 0 < W)
    (hcpos : 0 < c)
    (hweight_lower : ∀ᵐ x ∂μ, c ≤ weight x)
    (hweight_bound : ∀ᵐ x ∂μ, weight x ≤ W)
    (x0 : Component → Ω)
    (hmin :
      ∀ component x,
        x ∈ P.pieceSet component → rate component ≤ phi component x)
    (hx0 : ∀ component, phi component (x0 component) = rate component)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (hclosure :
      ∀ component, x0 component ∈ closure (interior (P.pieceSet component)))
    (hkernel_pos : ∀ k x, 0 < kernel k x)
    (huniform_log :
      ∀ component, ∀ ε > 0,
        ∀ᶠ k : ℕ in Filter.atTop,
          ∀ x : Ω,
            |(-Real.log (kernel k x) / (k : ℝ)) - phi component x| ≤ ε)
    (minAdjacent : Adjacent)
    (hadj_min :
      ∀ adj : Adjacent,
        rate (selectAdjacent minAdjacent) ≤ rate (selectAdjacent adj))
    (hadj_dominates :
      ∀ component,
        ∃ adj : Adjacent, rate (selectAdjacent adj) ≤ rate component) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in P.support, weight x * kernel k x ∂μ)
      (rate (selectAdjacent minAdjacent)) :=
  GJ19OptimalBinaryRatingSystems.lemmaC3_partition_integral_hasExponentialRate_of_dominating_adjacent_subfamily_closure_interior_uniformWeightLower_constBounds
    μ P weight kernel phi rate selectAdjacent hkernel_int hweight_int
    hWpos hcpos hweight_lower hweight_bound x0 hmin hx0 hcont hclosure
    hkernel_pos huniform_log minAdjacent hadj_min hadj_dominates

/--
Theorem 3.1/C.3 ordered quality partition: monotone cutpoints split the
continuum quality interval into the half-open cells used by a stepwise binary
rating rule.
-/
abbrev paper_theorem31_ordered_quality_interval_partition
    (μ : Measure ℝ) (n : ℕ) (cut : ℕ → ℝ) (hmono : Monotone cut) :
    FiniteMeasurableSetPartition μ (Fin n) :=
  theorem31_ordered_quality_interval_partition μ n cut hmono

/--
Theorem 3.1/C.3 ordered quality-pair partition: selected products of ordered
quality cells form the finite rectangle family used to decompose the pairwise
continuum error integral.
-/
abbrev paper_theorem31_ordered_quality_pair_partition
    (μ : Measure ℝ) (n : ℕ) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (selected : Fin n × Fin n → Prop) [DecidablePred selected] :
    FiniteMeasurableSetPartition (μ.prod μ)
      {piece : Fin n × Fin n // selected piece} :=
  theorem31_ordered_quality_pair_partition μ n cut hmono selected

/--
Theorem 3.1/C.3 ordered interval support: every point of an ordered half-open
quality cell lies in the closure of that cell's interior.
-/
theorem paper_theorem31_ordered_quality_interval_piece_mem_closure_interior
    (μ : Measure ℝ) (n : ℕ) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (piece : Fin n) {x : ℝ}
    (hx :
      x ∈ (theorem31_ordered_quality_interval_partition μ n cut hmono).pieceSet
        piece) :
    x ∈ closure
      (interior
        ((theorem31_ordered_quality_interval_partition μ n cut hmono).pieceSet
          piece)) :=
  GJ19OptimalBinaryRatingSystems.theorem31_ordered_quality_interval_piece_mem_closure_interior
    μ n cut hmono piece hx

/--
Theorem 3.1/C.3 ordered rectangle support: every point of a selected ordered
quality-pair rectangle lies in the closure of that rectangle's interior.
-/
theorem paper_theorem31_ordered_quality_pair_piece_mem_closure_interior
    (μ : Measure ℝ) (n : ℕ) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (selected : Fin n × Fin n → Prop) [DecidablePred selected]
    (piece : {piece : Fin n × Fin n // selected piece}) {x : ℝ × ℝ}
    (hx :
      x ∈ (theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
        piece) :
    x ∈ closure
      (interior
        ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet
          piece)) :=
  GJ19OptimalBinaryRatingSystems.theorem31_ordered_quality_pair_piece_mem_closure_interior
    μ n cut hmono selected piece hx

/--
Lemma C.3 ordered-rectangle decomposition: for a stepwise `β` represented by
monotone quality cutpoints, exact rate certificates on every selected
rectangle aggregate to the minimum selected rectangle exponent.
-/
theorem paper_lemmaC3_ordered_quality_pair_partition_integral_hasExponentialRate_of_min_component_certificates
    (μ : Measure ℝ) (n : ℕ) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (selected : Fin n × Fin n → Prop) [DecidablePred selected]
    (errorKernel : ℕ → ℝ × ℝ → ℝ)
    (rate : {piece : Fin n × Fin n // selected piece} → ℝ)
    (hcomponent_int :
      ∀ k component,
        MeasureTheory.IntegrableOn (errorKernel k)
          ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet component)
          (μ.prod μ))
    (hcert :
      ∀ component,
        ExponentialRateCertificate
          (fun k : ℕ =>
            (theorem31_ordered_quality_pair_partition μ n cut hmono selected).componentIntegral
              (errorKernel k) component)
          (rate component))
    (minComponent : {piece : Fin n × Fin n // selected piece})
    (hrate_ge : ∀ component, rate minComponent ≤ rate component) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in (theorem31_ordered_quality_pair_partition μ n cut hmono selected).support,
          errorKernel k x ∂(μ.prod μ))
      (rate minComponent) :=
  GJ19OptimalBinaryRatingSystems.lemmaC3_ordered_quality_pair_partition_integral_hasExponentialRate_of_min_component_certificates
    μ n cut hmono selected errorKernel rate hcomponent_int hcert
    minComponent hrate_ge

/--
Lemma C.3 ordered-rectangle adjacent-dominance bridge: for a stepwise `β`
represented by monotone quality cutpoints, a selected adjacent rectangle
subfamily that dominates all selected rectangles determines the exponent of
the continuum pairwise error integral over those rectangles.
-/
theorem paper_lemmaC3_ordered_quality_pair_partition_integral_hasExponentialRate_of_dominating_adjacent_subfamily
    {Adjacent : Type*}
    (μ : Measure ℝ) (n : ℕ) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (selected : Fin n × Fin n → Prop) [DecidablePred selected]
    (errorKernel : ℕ → ℝ × ℝ → ℝ)
    (rate : {piece : Fin n × Fin n // selected piece} → ℝ)
    (selectAdjacent : Adjacent → {piece : Fin n × Fin n // selected piece})
    (hcomponent_int :
      ∀ k component,
        MeasureTheory.IntegrableOn (errorKernel k)
          ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet component)
          (μ.prod μ))
    (hcert :
      ∀ component,
        ExponentialRateCertificate
          (fun k : ℕ =>
            (theorem31_ordered_quality_pair_partition μ n cut hmono selected).componentIntegral
              (errorKernel k) component)
          (rate component))
    (minAdjacent : Adjacent)
    (hadj_min :
      ∀ adj : Adjacent,
        rate (selectAdjacent minAdjacent) ≤ rate (selectAdjacent adj))
    (hadj_dominates :
      ∀ component,
        ∃ adj : Adjacent, rate (selectAdjacent adj) ≤ rate component) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in (theorem31_ordered_quality_pair_partition μ n cut hmono selected).support,
          errorKernel k x ∂(μ.prod μ))
      (rate (selectAdjacent minAdjacent)) :=
  GJ19OptimalBinaryRatingSystems.lemmaC3_ordered_quality_pair_partition_integral_hasExponentialRate_of_dominating_adjacent_subfamily
    μ n cut hmono selected errorKernel rate selectAdjacent hcomponent_int
    hcert minAdjacent hadj_min hadj_dominates

/--
Lemma C.3 ordered-rectangle positive-kernel adjacent-dominance bridge with
continuous minimizers.  For selected ordered quality rectangles, minimizers
inside the rectangles automatically satisfy the closure/interior support
condition required by the Laplace step.
-/
theorem paper_lemmaC3_ordered_quality_pair_partition_integral_hasExponentialRate_of_dominating_adjacent_subfamily_continuous_min_uniformWeightLower
    {Adjacent : Type*}
    (μ : Measure ℝ) [MeasureTheory.IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (n : ℕ) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (selected : Fin n × Fin n → Prop) [DecidablePred selected]
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : {piece : Fin n × Fin n // selected piece} → ℝ × ℝ → ℝ)
    (rate W c : {piece : Fin n × Fin n // selected piece} → ℝ)
    (selectAdjacent :
      Adjacent → {piece : Fin n × Fin n // selected piece})
    (hkernel_int :
      ∀ k component,
        MeasureTheory.IntegrableOn (fun x : ℝ × ℝ => weight x * kernel k x)
          ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet component)
          (μ.prod μ))
    (hweight_int :
      ∀ component,
        MeasureTheory.IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet component)
          (μ.prod μ))
    (hWpos : ∀ component, 0 < W component)
    (hcpos : ∀ component, 0 < c component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet component),
          c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet component),
          weight x ≤ W component)
    (x0 : {piece : Fin n × Fin n // selected piece} → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet component)
    (hmin :
      ∀ component x,
        x ∈
            (theorem31_ordered_quality_pair_partition μ n cut hmono selected).pieceSet component →
          rate component ≤ phi component x)
    (hx0 : ∀ component, phi component (x0 component) = rate component)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (hkernel_pos : ∀ k x, 0 < kernel k x)
    (huniform_log :
      ∀ component, ∀ ε > 0,
        ∀ᶠ k : ℕ in Filter.atTop,
          ∀ x : ℝ × ℝ,
            |(-Real.log (kernel k x) / (k : ℝ)) - phi component x| ≤ ε)
    (minAdjacent : Adjacent)
    (hadj_min :
      ∀ adj : Adjacent,
        rate (selectAdjacent minAdjacent) ≤ rate (selectAdjacent adj))
    (hadj_dominates :
      ∀ component,
        ∃ adj : Adjacent, rate (selectAdjacent adj) ≤ rate component) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in (theorem31_ordered_quality_pair_partition μ n cut hmono selected).support,
          weight x * kernel k x ∂(μ.prod μ))
      (rate (selectAdjacent minAdjacent)) :=
  GJ19OptimalBinaryRatingSystems.lemmaC3_ordered_quality_pair_partition_integral_hasExponentialRate_of_dominating_adjacent_subfamily_continuous_min_uniformWeightLower
    μ n cut hmono selected weight kernel phi rate W c selectAdjacent
    hkernel_int hweight_int hWpos hcpos hweight_lower hweight_bound x0
    hx0_mem hmin hx0 hcont hkernel_pos huniform_log minAdjacent hadj_min
    hadj_dominates

/--
Theorem 3.1/C.3 endpoint-aware ordered-rectangle bridge.  For the selected
nontrivial ordered level-pair rectangles, finite endpoint-aware adjacent
dominance supplies the adjacent-dominance input required by the generic
partition/Laplace theorem.
-/
theorem paper_lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_continuous_min_uniformWeightLower
    (μ : Measure ℝ) [MeasureTheory.IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_nonneg : ∀ idx, 0 ≤ successProb idx)
    (hprob_pos_of_not_first :
      ∀ idx : Fin (m + 2), idx.val ≠ 0 → 0 < successProb idx)
    (hprob_lt_one_of_not_last :
      ∀ idx : Fin (m + 2), idx.val ≠ m + 1 → successProb idx < 1)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : paperTheorem31OrderedNontrivialPairComponent m → ℝ × ℝ → ℝ)
    (W c : paperTheorem31OrderedNontrivialPairComponent m → ℝ)
    (hkernel_int :
      ∀ k component,
        MeasureTheory.IntegrableOn (fun x : ℝ × ℝ => weight x * kernel k x)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_int :
      ∀ component,
        MeasureTheory.IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hWpos : ∀ component, 0 < W component)
    (hcpos : ∀ component, 0 < c component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          weight x ≤ W component)
    (x0 : paperTheorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hmin :
      ∀ component x,
        x ∈
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
          binaryEndpointAwarePairRate successProb sampleRate
              component.val.1 component.val.2 ≤
            phi component x)
    (hx0 :
      ∀ component,
        phi component (x0 component) =
          binaryEndpointAwarePairRate successProb sampleRate
            component.val.1 component.val.2)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (hkernel_pos : ∀ k x, 0 < kernel k x)
    (huniform_log :
      ∀ component, ∀ ε > 0,
        ∀ᶠ k : ℕ in Filter.atTop,
          ∀ x : ℝ × ℝ,
            |(-Real.log (kernel k x) / (k : ℝ)) - phi component x| ≤ ε)
    (minAdjacent : Fin (m + 1))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (paperTheorem31OrderedNontrivialPairSelected (m := m))).support,
          weight x * kernel k x ∂(μ.prod μ))
      (binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) :=
  GJ19OptimalBinaryRatingSystems.lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_continuous_min_uniformWeightLower
    μ hm cut hmono successProb sampleRate hsample_pos hsample_mono hprob_mono
    hprob_nonneg hprob_pos_of_not_first hprob_lt_one_of_not_last weight kernel
    phi W c hkernel_int hweight_int hWpos hcpos hweight_lower hweight_bound x0
    hx0_mem hmin hx0 hcont hkernel_pos huniform_log minAdjacent hadj_min

/--
Theorem 3.1/C.3 endpoint-aware ordered-rectangle bridge with locally positive
objective weights.  The selected nontrivial ordered level-pair rectangles
satisfy the required closure/interior support condition, and finite
endpoint-aware adjacent dominance supplies the adjacent-rate reduction.
-/
theorem paper_lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_continuous_min_weight_pos
    (μ : Measure ℝ) [MeasureTheory.IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_nonneg : ∀ idx, 0 ≤ successProb idx)
    (hprob_pos_of_not_first :
      ∀ idx : Fin (m + 2), idx.val ≠ 0 → 0 < successProb idx)
    (hprob_lt_one_of_not_last :
      ∀ idx : Fin (m + 2), idx.val ≠ m + 1 → successProb idx < 1)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : paperTheorem31OrderedNontrivialPairComponent m → ℝ × ℝ → ℝ)
    (W : paperTheorem31OrderedNontrivialPairComponent m → ℝ)
    (hkernel_int :
      ∀ k component,
        MeasureTheory.IntegrableOn (fun x : ℝ × ℝ => weight x * kernel k x)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_int :
      ∀ component,
        MeasureTheory.IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hWpos : ∀ component, 0 < W component)
    (hweight_nonneg :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          0 ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          weight x ≤ W component)
    (x0 : paperTheorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hmin :
      ∀ component x,
        x ∈
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
          binaryEndpointAwarePairRate successProb sampleRate
              component.val.1 component.val.2 ≤
            phi component x)
    (hx0 :
      ∀ component,
        phi component (x0 component) =
          binaryEndpointAwarePairRate successProb sampleRate
            component.val.1 component.val.2)
    (hphi_cont : ∀ component, ContinuousAt (phi component) (x0 component))
    (hweight_cont : ∀ component, ContinuousAt weight (x0 component))
    (hweight_x0_pos : ∀ component, 0 < weight (x0 component))
    (hkernel_pos : ∀ k x, 0 < kernel k x)
    (huniform_log :
      ∀ component, ∀ ε > 0,
        ∀ᶠ k : ℕ in Filter.atTop,
          ∀ x : ℝ × ℝ,
            |(-Real.log (kernel k x) / (k : ℝ)) - phi component x| ≤ ε)
    (minAdjacent : Fin (m + 1))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (paperTheorem31OrderedNontrivialPairSelected (m := m))).support,
          weight x * kernel k x ∂(μ.prod μ))
      (binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) :=
  GJ19OptimalBinaryRatingSystems.lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_continuous_min_weight_pos
    μ hm cut hmono successProb sampleRate hsample_pos hsample_mono hprob_mono
    hprob_nonneg hprob_pos_of_not_first hprob_lt_one_of_not_last weight kernel
    phi W hkernel_int hweight_int hWpos hweight_nonneg hweight_bound x0
    hx0_mem hmin hx0 hphi_cont hweight_cont hweight_x0_pos hkernel_pos
    huniform_log minAdjacent hadj_min

/--
Theorem 3.1/C.3 endpoint-aware ordered-rectangle bridge for kernels that are
exactly exponential on each selected rectangle.
-/
theorem paper_lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_exact_exp_on_cells_continuous_min_uniformWeightLower
    (μ : Measure ℝ) [MeasureTheory.IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_nonneg : ∀ idx, 0 ≤ successProb idx)
    (hprob_pos_of_not_first :
      ∀ idx : Fin (m + 2), idx.val ≠ 0 → 0 < successProb idx)
    (hprob_lt_one_of_not_last :
      ∀ idx : Fin (m + 2), idx.val ≠ m + 1 → successProb idx < 1)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : paperTheorem31OrderedNontrivialPairComponent m → ℝ × ℝ → ℝ)
    (W c : paperTheorem31OrderedNontrivialPairComponent m → ℝ)
    (hkernel_int :
      ∀ k component,
        MeasureTheory.IntegrableOn (fun x : ℝ × ℝ => weight x * kernel k x)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hkernel_eq :
      ∀ k component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          kernel k x = Real.exp (-(k : ℝ) * phi component x))
    (hweight_int :
      ∀ component,
        MeasureTheory.IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hWpos : ∀ component, 0 < W component)
    (hcpos : ∀ component, 0 < c component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          weight x ≤ W component)
    (x0 : paperTheorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hmin :
      ∀ component x,
        x ∈
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
          binaryEndpointAwarePairRate successProb sampleRate
              component.val.1 component.val.2 ≤
            phi component x)
    (hx0 :
      ∀ component,
        phi component (x0 component) =
          binaryEndpointAwarePairRate successProb sampleRate
            component.val.1 component.val.2)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (minAdjacent : Fin (m + 1))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (paperTheorem31OrderedNontrivialPairSelected (m := m))).support,
          weight x * kernel k x ∂(μ.prod μ))
      (binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) :=
  GJ19OptimalBinaryRatingSystems.lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_exact_exp_on_cells_continuous_min_uniformWeightLower
    μ hm cut hmono successProb sampleRate hsample_pos hsample_mono hprob_mono
    hprob_nonneg hprob_pos_of_not_first hprob_lt_one_of_not_last weight kernel
    phi W c hkernel_int hkernel_eq hweight_int hWpos hcpos hweight_lower
    hweight_bound x0 hx0_mem hmin hx0 hcont minAdjacent hadj_min

/--
Theorem 3.1/C.3 endpoint-aware ordered-rectangle bridge for source-shaped
Laplace kernels `exp (-k * phiSeq k x)` on each selected rectangle.
-/
theorem paper_lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_uniform_tendsto_on_cells_continuous_min_uniformWeightLower
    (μ : Measure ℝ) [MeasureTheory.IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_nonneg : ∀ idx, 0 ≤ successProb idx)
    (hprob_pos_of_not_first :
      ∀ idx : Fin (m + 2), idx.val ≠ 0 → 0 < successProb idx)
    (hprob_lt_one_of_not_last :
      ∀ idx : Fin (m + 2), idx.val ≠ m + 1 → successProb idx < 1)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phiSeq :
      paperTheorem31OrderedNontrivialPairComponent m → ℕ → ℝ × ℝ → ℝ)
    (phi : paperTheorem31OrderedNontrivialPairComponent m → ℝ × ℝ → ℝ)
    (W c : paperTheorem31OrderedNontrivialPairComponent m → ℝ)
    (hkernel_int :
      ∀ k component,
        MeasureTheory.IntegrableOn (fun x : ℝ × ℝ => weight x * kernel k x)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hkernel_eq :
      ∀ k component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          kernel k x = Real.exp (-(k : ℝ) * phiSeq component k x))
    (hWpos : ∀ component, 0 < W component)
    (hcpos : ∀ component, 0 < c component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          weight x ≤ W component)
    (x0 : paperTheorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hmin :
      ∀ component x,
        x ∈
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
          binaryEndpointAwarePairRate successProb sampleRate
              component.val.1 component.val.2 ≤
            phi component x)
    (hx0 :
      ∀ component,
        phi component (x0 component) =
          binaryEndpointAwarePairRate successProb sampleRate
            component.val.1 component.val.2)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (huniform :
      ∀ component, ∀ ε > 0,
        ∀ᶠ k : ℕ in Filter.atTop,
          ∀ x : ℝ × ℝ, |phiSeq component k x - phi component x| ≤ ε)
    (minAdjacent : Fin (m + 1))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (paperTheorem31OrderedNontrivialPairSelected (m := m))).support,
          weight x * kernel k x ∂(μ.prod μ))
      (binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) :=
  GJ19OptimalBinaryRatingSystems.lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_uniform_tendsto_on_cells_continuous_min_uniformWeightLower
    μ hm cut hmono successProb sampleRate hsample_pos hsample_mono hprob_mono
    hprob_nonneg hprob_pos_of_not_first hprob_lt_one_of_not_last weight kernel
    phiSeq phi W c hkernel_int hkernel_eq hWpos hcpos hweight_lower
    hweight_bound x0 hx0_mem hmin hx0 hcont huniform minAdjacent hadj_min

/--
Theorem 3.1/C.3 endpoint-aware ordered-rectangle bridge for source-shaped
Laplace kernels with eventual a.e. equality on each selected rectangle.
-/
theorem paper_lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_uniform_tendsto_on_cells_eventually_continuous_min_uniformWeightLower
    (μ : Measure ℝ) [MeasureTheory.IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_nonneg : ∀ idx, 0 ≤ successProb idx)
    (hprob_pos_of_not_first :
      ∀ idx : Fin (m + 2), idx.val ≠ 0 → 0 < successProb idx)
    (hprob_lt_one_of_not_last :
      ∀ idx : Fin (m + 2), idx.val ≠ m + 1 → successProb idx < 1)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phiSeq :
      paperTheorem31OrderedNontrivialPairComponent m → ℕ → ℝ × ℝ → ℝ)
    (phi : paperTheorem31OrderedNontrivialPairComponent m → ℝ × ℝ → ℝ)
    (W c : paperTheorem31OrderedNontrivialPairComponent m → ℝ)
    (hkernel_int :
      ∀ k component,
        MeasureTheory.IntegrableOn (fun x : ℝ × ℝ => weight x * kernel k x)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hlaplace_int :
      ∀ k : ℕ, ∀ component,
        MeasureTheory.IntegrableOn
          (fun x : ℝ × ℝ =>
            weight x * Real.exp (-(k : ℝ) * phiSeq component k x))
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hkernel_eq :
      ∀ component,
        ∀ᶠ k : ℕ in Filter.atTop,
          ∀ᵐ x ∂(μ.prod μ).restrict
              ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
                (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
            kernel k x = Real.exp (-(k : ℝ) * phiSeq component k x))
    (hWpos : ∀ component, 0 < W component)
    (hcpos : ∀ component, 0 < c component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          weight x ≤ W component)
    (x0 : paperTheorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hmin :
      ∀ component x,
        x ∈
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
          binaryEndpointAwarePairRate successProb sampleRate
              component.val.1 component.val.2 ≤
            phi component x)
    (hx0 :
      ∀ component,
        phi component (x0 component) =
          binaryEndpointAwarePairRate successProb sampleRate
            component.val.1 component.val.2)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (huniform :
      ∀ component, ∀ ε > 0,
        ∀ᶠ k : ℕ in Filter.atTop,
          ∀ x : ℝ × ℝ, |phiSeq component k x - phi component x| ≤ ε)
    (minAdjacent : Fin (m + 1))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (paperTheorem31OrderedNontrivialPairSelected (m := m))).support,
          weight x * kernel k x ∂(μ.prod μ))
      (binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) :=
  GJ19OptimalBinaryRatingSystems.lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_uniform_tendsto_on_cells_eventually_continuous_min_uniformWeightLower
    μ hm cut hmono successProb sampleRate hsample_pos hsample_mono hprob_mono
    hprob_nonneg hprob_pos_of_not_first hprob_lt_one_of_not_last weight kernel
    phiSeq phi W c hkernel_int hlaplace_int hkernel_eq hWpos hcpos
    hweight_lower hweight_bound x0 hx0_mem hmin hx0 hcont huniform
    minAdjacent hadj_min

/--
Theorem 3.1/C.3 endpoint-aware ordered-rectangle bridge with the paper's
normalized-log convention `phi_k = -log kernel_k / k`.
-/
theorem paper_lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_normalizedLogRate_tendsto_on_cells_eventually_continuous_min_uniformWeightLower
    (μ : Measure ℝ) [MeasureTheory.IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_nonneg : ∀ idx, 0 ≤ successProb idx)
    (hprob_pos_of_not_first :
      ∀ idx : Fin (m + 2), idx.val ≠ 0 → 0 < successProb idx)
    (hprob_lt_one_of_not_last :
      ∀ idx : Fin (m + 2), idx.val ≠ m + 1 → successProb idx < 1)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : paperTheorem31OrderedNontrivialPairComponent m → ℝ × ℝ → ℝ)
    (W c : paperTheorem31OrderedNontrivialPairComponent m → ℝ)
    (hkernel_int :
      ∀ k component,
        MeasureTheory.IntegrableOn (fun x : ℝ × ℝ => weight x * kernel k x)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hlaplace_int :
      ∀ k : ℕ, ∀ component,
        MeasureTheory.IntegrableOn
          (fun x : ℝ × ℝ =>
            weight x *
              Real.exp (-(k : ℝ) * normalizedLogKernelRate kernel k x))
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hkernel_pos :
      ∀ component,
        ∀ᶠ k : ℕ in Filter.atTop,
          ∀ᵐ x ∂(μ.prod μ).restrict
              ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
                (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
            0 < kernel k x)
    (hWpos : ∀ component, 0 < W component)
    (hcpos : ∀ component, 0 < c component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          weight x ≤ W component)
    (x0 : paperTheorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hmin :
      ∀ component x,
        x ∈
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
          binaryEndpointAwarePairRate successProb sampleRate
              component.val.1 component.val.2 ≤
            phi component x)
    (hx0 :
      ∀ component,
        phi component (x0 component) =
          binaryEndpointAwarePairRate successProb sampleRate
            component.val.1 component.val.2)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (huniform :
      ∀ component, ∀ ε > 0,
        ∀ᶠ k : ℕ in Filter.atTop,
          ∀ x : ℝ × ℝ,
            |normalizedLogKernelRate kernel k x - phi component x| ≤ ε)
    (minAdjacent : Fin (m + 1))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (paperTheorem31OrderedNontrivialPairSelected (m := m))).support,
          weight x * kernel k x ∂(μ.prod μ))
      (binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) :=
  GJ19OptimalBinaryRatingSystems.lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_normalizedLogRate_tendsto_on_cells_eventually_continuous_min_uniformWeightLower
    μ hm cut hmono successProb sampleRate hsample_pos hsample_mono hprob_mono
    hprob_nonneg hprob_pos_of_not_first hprob_lt_one_of_not_last weight kernel
    phi W c hkernel_int hlaplace_int hkernel_pos hWpos hcpos hweight_lower
    hweight_bound x0 hx0_mem hmin hx0 hcont huniform minAdjacent hadj_min

/--
Theorem 3.1/C.3 endpoint-aware ordered-rectangle bridge with the paper's
normalized-log convention and all-index a.e. positivity of the error kernel.
-/
theorem paper_lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_normalizedLogRate_tendsto_on_cells_continuous_min_uniformWeightLower
    (μ : Measure ℝ) [MeasureTheory.IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_nonneg : ∀ idx, 0 ≤ successProb idx)
    (hprob_pos_of_not_first :
      ∀ idx : Fin (m + 2), idx.val ≠ 0 → 0 < successProb idx)
    (hprob_lt_one_of_not_last :
      ∀ idx : Fin (m + 2), idx.val ≠ m + 1 → successProb idx < 1)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : paperTheorem31OrderedNontrivialPairComponent m → ℝ × ℝ → ℝ)
    (W c : paperTheorem31OrderedNontrivialPairComponent m → ℝ)
    (hkernel_int :
      ∀ k component,
        MeasureTheory.IntegrableOn (fun x : ℝ × ℝ => weight x * kernel k x)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_int :
      ∀ component,
        MeasureTheory.IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hkernel_pos :
      ∀ k component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          0 < kernel k x)
    (hWpos : ∀ component, 0 < W component)
    (hcpos : ∀ component, 0 < c component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          weight x ≤ W component)
    (x0 : paperTheorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hmin :
      ∀ component x,
        x ∈
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
          binaryEndpointAwarePairRate successProb sampleRate
              component.val.1 component.val.2 ≤
            phi component x)
    (hx0 :
      ∀ component,
        phi component (x0 component) =
          binaryEndpointAwarePairRate successProb sampleRate
            component.val.1 component.val.2)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (huniform :
      ∀ component, ∀ ε > 0,
        ∀ᶠ k : ℕ in Filter.atTop,
          ∀ x : ℝ × ℝ,
            |normalizedLogKernelRate kernel k x - phi component x| ≤ ε)
    (minAdjacent : Fin (m + 1))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj) :
    HasExponentialRate
      (fun k : ℕ =>
        ∫ x in (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (paperTheorem31OrderedNontrivialPairSelected (m := m))).support,
          weight x * kernel k x ∂(μ.prod μ))
      (binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) :=
  GJ19OptimalBinaryRatingSystems.lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_normalizedLogRate_tendsto_on_cells_continuous_min_uniformWeightLower
    μ hm cut hmono successProb sampleRate hsample_pos hsample_mono hprob_mono
    hprob_nonneg hprob_pos_of_not_first hprob_lt_one_of_not_last weight kernel
    phi W c hkernel_int hweight_int hkernel_pos hWpos hcpos hweight_lower
    hweight_bound x0 hx0_mem hmin hx0 hcont huniform minAdjacent hadj_min

/--
Theorem 3.1/C.3 endpoint-aware ordered-rectangle bridge with the paper's
normalized-log convention and local positive objective weights.
-/
abbrev paper_lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_normalizedLogRate_tendsto_on_cells_continuous_min_weight_pos :=
  GJ19OptimalBinaryRatingSystems.lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_normalizedLogRate_tendsto_on_cells_continuous_min_weight_pos

/--
Theorem 3.1/C.3 endpoint-aware ordered-rectangle bridge with the paper's
normalized-log convention and piece-local uniform convergence on each selected
rectangle.
-/
abbrev paper_lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_normalizedLogRate_tendsto_on_pieces_continuous_min_uniformWeightLower :=
  GJ19OptimalBinaryRatingSystems.lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_normalizedLogRate_tendsto_on_pieces_continuous_min_uniformWeightLower

/--
Theorem 3.1/C.3 endpoint-aware ordered-rectangle bridge where compact-local
normalized-log estimates supply uniform convergence on each selected
rectangle.
-/
abbrev paper_lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_normalizedLogRate_tendsto_of_locally_on_compact_supersets_continuous_min_uniformWeightLower :=
  GJ19OptimalBinaryRatingSystems.lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_normalizedLogRate_tendsto_of_locally_on_compact_supersets_continuous_min_uniformWeightLower

/--
Theorem 3.1/C.3 endpoint-aware ordered-rectangle bridge where compact-local
normalized-log estimates supply uniform convergence on each selected
rectangle, with endpoint support and monotonicity supplied by the
endpoint-level-vector convention.
-/
abbrev paper_lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_normalizedLogRate_tendsto_of_locally_on_compact_supersets_continuous_min_uniformWeightLower_of_endpointLevelVector
    (μ : Measure ℝ) [MeasureTheory.IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)] {m : ℕ} :=
  GJ19OptimalBinaryRatingSystems.lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_normalizedLogRate_tendsto_of_locally_on_compact_supersets_continuous_min_uniformWeightLower_of_endpointLevelVector
    μ (m := m)

/--
Theorem 3.1/C.3 endpoint-aware ordered-rectangle bridge from componentwise
constant-factor exponential sandwiches.
-/
abbrev paper_lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_exp_sandwich_const_on_pieces_continuous_min_uniformWeightLower :=
  GJ19OptimalBinaryRatingSystems.lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_exp_sandwich_const_on_pieces_continuous_min_uniformWeightLower

/--
Theorem 3.1/C.3 endpoint-aware ordered-rectangle bridge from componentwise
constant-factor exponential sandwiches, with endpoint support and monotonicity
supplied by the endpoint-level-vector convention.
-/
abbrev paper_lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_exp_sandwich_const_on_pieces_continuous_min_uniformWeightLower_of_endpointLevelVector
    (μ : Measure ℝ) [MeasureTheory.IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)] {m : ℕ} :=
  GJ19OptimalBinaryRatingSystems.lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_exp_sandwich_const_on_pieces_continuous_min_uniformWeightLower_of_endpointLevelVector
    μ (m := m)

/--
Theorem 3.1/C.3 endpoint-aware ordered-rectangle bridge from uniform
exponential-rate certificates on each selected rectangle.
-/
abbrev paper_lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_uniformExponentialRateCertificate_on_pieces_continuous_min_uniformWeightLower :=
  GJ19OptimalBinaryRatingSystems.lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_uniformExponentialRateCertificate_on_pieces_continuous_min_uniformWeightLower

/--
Theorem 3.1/C.3 endpoint-aware ordered-rectangle bridge from uniform
exponential-rate certificates on each selected rectangle, with endpoint
support and monotonicity supplied by the endpoint-level-vector convention.
-/
abbrev paper_lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_uniformExponentialRateCertificate_on_pieces_continuous_min_uniformWeightLower_of_endpointLevelVector
    (μ : Measure ℝ) [MeasureTheory.IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)] {m : ℕ} :=
  GJ19OptimalBinaryRatingSystems.lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_uniformExponentialRateCertificate_on_pieces_continuous_min_uniformWeightLower_of_endpointLevelVector
    μ (m := m)

/--
Theorem 3.1/C.3 endpoint-aware ordered-rectangle bridge from uniform
exponential-rate certificates, using the eventual-positive normalized-log
Laplace path.
-/
abbrev paper_lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_uniformExponentialRateCertificate_on_pieces_eventually_continuous_min_uniformWeightLower :=
  GJ19OptimalBinaryRatingSystems.lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_uniformExponentialRateCertificate_on_pieces_eventually_continuous_min_uniformWeightLower

/--
Theorem 3.1/C.3 endpoint-aware ordered-rectangle bridge from uniform
exponential-rate certificates, with endpoint support and monotonicity supplied
by the endpoint-level-vector convention.
-/
abbrev paper_lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_uniformExponentialRateCertificate_on_pieces_eventually_continuous_min_uniformWeightLower_of_endpointLevelVector
    (μ : Measure ℝ) [MeasureTheory.IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)] {m : ℕ} :=
  GJ19OptimalBinaryRatingSystems.lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_uniformExponentialRateCertificate_on_pieces_eventually_continuous_min_uniformWeightLower_of_endpointLevelVector
    μ (m := m)

/--
Theorem 3.1/C.3 endpoint-aware ordered-rectangle bridge from uniform
normalized-log rate certificates on each selected rectangle.
-/
abbrev paper_lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_uniformNormalizedLogRateCertificate_on_pieces_eventually_continuous_min_uniformWeightLower :=
  GJ19OptimalBinaryRatingSystems.lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_uniformNormalizedLogRateCertificate_on_pieces_eventually_continuous_min_uniformWeightLower

/--
Theorem 3.1/C.3 endpoint-aware ordered-rectangle bridge from uniform
normalized-log rate certificates, with endpoint support and monotonicity
supplied by the endpoint-level-vector convention.
-/
abbrev paper_lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_uniformNormalizedLogRateCertificate_on_pieces_eventually_continuous_min_uniformWeightLower_of_endpointLevelVector
    (μ : Measure ℝ) [MeasureTheory.IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)] {m : ℕ} :=
  GJ19OptimalBinaryRatingSystems.lemmaC3_ordered_quality_endpoint_pair_partition_integral_hasExponentialRate_of_adjacent_min_uniformNormalizedLogRateCertificate_on_pieces_eventually_continuous_min_uniformWeightLower_of_endpointLevelVector
    μ (m := m)

/--
Lemma C.4 forward direction in the source-shaped continuum setting: if the
minimum adjacent exponent is positive, the piecewise-constant objective has a
positive exponential convergence rate.
-/
theorem paper_lemmaC4_endpoint_piecewise_constant_has_positive_exponential_rate_of_uniform_tendsto_on_cells
    (μ : Measure ℝ) [MeasureTheory.IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_nonneg : ∀ idx, 0 ≤ successProb idx)
    (hprob_pos_of_not_first :
      ∀ idx : Fin (m + 2), idx.val ≠ 0 → 0 < successProb idx)
    (hprob_lt_one_of_not_last :
      ∀ idx : Fin (m + 2), idx.val ≠ m + 1 → successProb idx < 1)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phiSeq :
      paperTheorem31OrderedNontrivialPairComponent m → ℕ → ℝ × ℝ → ℝ)
    (phi : paperTheorem31OrderedNontrivialPairComponent m → ℝ × ℝ → ℝ)
    (W c : paperTheorem31OrderedNontrivialPairComponent m → ℝ)
    (hkernel_int :
      ∀ k component,
        MeasureTheory.IntegrableOn (fun x : ℝ × ℝ => weight x * kernel k x)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hkernel_eq :
      ∀ k component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          kernel k x = Real.exp (-(k : ℝ) * phiSeq component k x))
    (hWpos : ∀ component, 0 < W component)
    (hcpos : ∀ component, 0 < c component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          weight x ≤ W component)
    (x0 : paperTheorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hmin :
      ∀ component x,
        x ∈
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
          binaryEndpointAwarePairRate successProb sampleRate
              component.val.1 component.val.2 ≤
            phi component x)
    (hx0 :
      ∀ component,
        phi component (x0 component) =
          binaryEndpointAwarePairRate successProb sampleRate
            component.val.1 component.val.2)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (huniform :
      ∀ component, ∀ ε > 0,
        ∀ᶠ k : ℕ in Filter.atTop,
          ∀ x : ℝ × ℝ, |phiSeq component k x - phi component x| ≤ ε)
    (minAdjacent : Fin (m + 1))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj)
    (hmin_pos :
      0 < binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) :
    ∃ r : ℝ, 0 < r ∧
      HasExponentialRate
        (fun k : ℕ =>
          ∫ x in (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (paperTheorem31OrderedNontrivialPairSelected (m := m))).support,
            weight x * kernel k x ∂(μ.prod μ))
        r :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_endpoint_piecewise_constant_has_positive_exponential_rate_of_uniform_tendsto_on_cells
    μ hm cut hmono successProb sampleRate hsample_pos hsample_mono hprob_mono
    hprob_nonneg hprob_pos_of_not_first hprob_lt_one_of_not_last weight kernel
    phiSeq phi W c hkernel_int hkernel_eq hWpos hcpos hweight_lower
    hweight_bound x0 hx0_mem hmin hx0 hcont huniform minAdjacent hadj_min
    hmin_pos

/--
Lemma C.4 forward direction with the paper's normalized-log convention:
eventual positivity and uniform convergence of `-log kernel_k / k` on cells
give a positive exponential convergence rate.
-/
theorem paper_lemmaC4_endpoint_piecewise_constant_has_positive_exponential_rate_of_normalizedLogRate_tendsto_on_cells
    (μ : Measure ℝ) [MeasureTheory.IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_nonneg : ∀ idx, 0 ≤ successProb idx)
    (hprob_pos_of_not_first :
      ∀ idx : Fin (m + 2), idx.val ≠ 0 → 0 < successProb idx)
    (hprob_lt_one_of_not_last :
      ∀ idx : Fin (m + 2), idx.val ≠ m + 1 → successProb idx < 1)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : paperTheorem31OrderedNontrivialPairComponent m → ℝ × ℝ → ℝ)
    (W c : paperTheorem31OrderedNontrivialPairComponent m → ℝ)
    (hkernel_int :
      ∀ k component,
        MeasureTheory.IntegrableOn (fun x : ℝ × ℝ => weight x * kernel k x)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hlaplace_int :
      ∀ k : ℕ, ∀ component,
        MeasureTheory.IntegrableOn
          (fun x : ℝ × ℝ =>
            weight x *
              Real.exp (-(k : ℝ) * normalizedLogKernelRate kernel k x))
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hkernel_pos :
      ∀ component,
        ∀ᶠ k : ℕ in Filter.atTop,
          ∀ᵐ x ∂(μ.prod μ).restrict
              ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
                (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
            0 < kernel k x)
    (hWpos : ∀ component, 0 < W component)
    (hcpos : ∀ component, 0 < c component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          weight x ≤ W component)
    (x0 : paperTheorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hmin :
      ∀ component x,
        x ∈
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
          binaryEndpointAwarePairRate successProb sampleRate
              component.val.1 component.val.2 ≤
            phi component x)
    (hx0 :
      ∀ component,
        phi component (x0 component) =
          binaryEndpointAwarePairRate successProb sampleRate
            component.val.1 component.val.2)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (huniform :
      ∀ component, ∀ ε > 0,
        ∀ᶠ k : ℕ in Filter.atTop,
          ∀ x : ℝ × ℝ,
            |normalizedLogKernelRate kernel k x - phi component x| ≤ ε)
    (minAdjacent : Fin (m + 1))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj)
    (hmin_pos :
      0 < binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) :
    ∃ r : ℝ, 0 < r ∧
      HasExponentialRate
        (fun k : ℕ =>
          ∫ x in (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (paperTheorem31OrderedNontrivialPairSelected (m := m))).support,
            weight x * kernel k x ∂(μ.prod μ))
        r :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_endpoint_piecewise_constant_has_positive_exponential_rate_of_normalizedLogRate_tendsto_on_cells
    μ hm cut hmono successProb sampleRate hsample_pos hsample_mono hprob_mono
    hprob_nonneg hprob_pos_of_not_first hprob_lt_one_of_not_last weight kernel
    phi W c hkernel_int hlaplace_int hkernel_pos hWpos hcpos hweight_lower
    hweight_bound x0 hx0_mem hmin hx0 hcont huniform minAdjacent hadj_min
    hmin_pos

/--
Lemma C.4 forward direction with the paper's normalized-log convention and
all-index a.e. positivity of the error kernel.
-/
theorem paper_lemmaC4_endpoint_piecewise_constant_has_positive_exponential_rate_of_normalizedLogRate_tendsto_on_cells_all_positive
    (μ : Measure ℝ) [MeasureTheory.IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) (cut : ℕ → ℝ) (hmono : Monotone cut)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos : ∀ idx, 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hprob_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → successProb a ≤ successProb b)
    (hprob_nonneg : ∀ idx, 0 ≤ successProb idx)
    (hprob_pos_of_not_first :
      ∀ idx : Fin (m + 2), idx.val ≠ 0 → 0 < successProb idx)
    (hprob_lt_one_of_not_last :
      ∀ idx : Fin (m + 2), idx.val ≠ m + 1 → successProb idx < 1)
    (weight : ℝ × ℝ → ℝ) (kernel : ℕ → ℝ × ℝ → ℝ)
    (phi : paperTheorem31OrderedNontrivialPairComponent m → ℝ × ℝ → ℝ)
    (W c : paperTheorem31OrderedNontrivialPairComponent m → ℝ)
    (hkernel_int :
      ∀ k component,
        MeasureTheory.IntegrableOn (fun x : ℝ × ℝ => weight x * kernel k x)
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hweight_int :
      ∀ component,
        MeasureTheory.IntegrableOn weight
          ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
          (μ.prod μ))
    (hkernel_pos :
      ∀ k component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          0 < kernel k x)
    (hWpos : ∀ component, 0 < W component)
    (hcpos : ∀ component, 0 < c component)
    (hweight_lower :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          c component ≤ weight x)
    (hweight_bound :
      ∀ component,
        ∀ᵐ x ∂(μ.prod μ).restrict
            ((theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component),
          weight x ≤ W component)
    (x0 : paperTheorem31OrderedNontrivialPairComponent m → ℝ × ℝ)
    (hx0_mem :
      ∀ component,
        x0 component ∈
          (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
            (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component)
    (hmin :
      ∀ component x,
        x ∈
            (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (paperTheorem31OrderedNontrivialPairSelected (m := m))).pieceSet component →
          binaryEndpointAwarePairRate successProb sampleRate
              component.val.1 component.val.2 ≤
            phi component x)
    (hx0 :
      ∀ component,
        phi component (x0 component) =
          binaryEndpointAwarePairRate successProb sampleRate
            component.val.1 component.val.2)
    (hcont : ∀ component, ContinuousAt (phi component) (x0 component))
    (huniform :
      ∀ component, ∀ ε > 0,
        ∀ᶠ k : ℕ in Filter.atTop,
          ∀ x : ℝ × ℝ,
            |normalizedLogKernelRate kernel k x - phi component x| ≤ ε)
    (minAdjacent : Fin (m + 1))
    (hadj_min :
      ∀ adj : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate adj)
    (hmin_pos :
      0 < binaryEndpointAwareAdjacentRate successProb sampleRate minAdjacent) :
    ∃ r : ℝ, 0 < r ∧
      HasExponentialRate
        (fun k : ℕ =>
          ∫ x in (theorem31_ordered_quality_pair_partition μ (m + 2) cut hmono
              (paperTheorem31OrderedNontrivialPairSelected (m := m))).support,
            weight x * kernel k x ∂(μ.prod μ))
        r :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_endpoint_piecewise_constant_has_positive_exponential_rate_of_normalizedLogRate_tendsto_on_cells_all_positive
    μ hm cut hmono successProb sampleRate hsample_pos hsample_mono hprob_mono
    hprob_nonneg hprob_pos_of_not_first hprob_lt_one_of_not_last weight kernel
    phi W c hkernel_int hweight_int hkernel_pos hWpos hcpos hweight_lower
    hweight_bound x0 hx0_mem hmin hx0 hcont huniform minAdjacent hadj_min
    hmin_pos

/--
Lemma C.4 positive-rate endpoint with normalized-log convergence and local
positive objective weights.
-/
abbrev paper_lemmaC4_endpoint_piecewise_constant_has_positive_exponential_rate_of_normalizedLogRate_tendsto_on_cells_all_positive_weight_pos :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_endpoint_piecewise_constant_has_positive_exponential_rate_of_normalizedLogRate_tendsto_on_cells_all_positive_weight_pos

/--
Lemma C.4 forward direction with the paper's normalized-log convention and
piece-local uniform convergence on each selected rectangle.
-/
abbrev paper_lemmaC4_endpoint_piecewise_constant_has_positive_exponential_rate_of_normalizedLogRate_tendsto_on_pieces_all_positive :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_endpoint_piecewise_constant_has_positive_exponential_rate_of_normalizedLogRate_tendsto_on_pieces_all_positive

/--
Lemma C.4 forward direction where compact-local normalized-log estimates
supply uniform convergence on each selected rectangle.
-/
abbrev paper_lemmaC4_endpoint_piecewise_constant_has_positive_exponential_rate_of_normalizedLogRate_tendsto_of_locally_on_compact_supersets_all_positive :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_endpoint_piecewise_constant_has_positive_exponential_rate_of_normalizedLogRate_tendsto_of_locally_on_compact_supersets_all_positive

/--
Lemma C.4 forward direction from componentwise constant-factor exponential
sandwiches for the selected ordered rectangles.
-/
abbrev paper_lemmaC4_endpoint_piecewise_constant_has_positive_exponential_rate_of_exp_sandwich_const_on_pieces_all_positive :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_endpoint_piecewise_constant_has_positive_exponential_rate_of_exp_sandwich_const_on_pieces_all_positive

/--
Lemma C.4 forward direction from uniform exponential-rate certificates on each
selected ordered rectangle.
-/
abbrev paper_lemmaC4_endpoint_piecewise_constant_has_positive_exponential_rate_of_uniformExponentialRateCertificate_on_pieces_all_positive :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_endpoint_piecewise_constant_has_positive_exponential_rate_of_uniformExponentialRateCertificate_on_pieces_all_positive

/--
Lemma C.4 forward direction from uniform exponential-rate certificates on each
selected ordered rectangle, with endpoint support and monotonicity supplied by
`BinaryEndpointLevelVector`.
-/
abbrev paper_lemmaC4_endpoint_piecewise_constant_has_positive_exponential_rate_of_uniformExponentialRateCertificate_on_pieces_endpointLevelVector :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_endpoint_piecewise_constant_has_positive_exponential_rate_of_uniformExponentialRateCertificate_on_pieces_endpointLevelVector

/--
Lemma C.4 forward direction from uniform exponential-rate certificates, using
the eventual-positive normalized-log Laplace path.
-/
abbrev paper_lemmaC4_endpoint_piecewise_constant_has_positive_exponential_rate_of_uniformExponentialRateCertificate_on_pieces_eventually_all_positive :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_endpoint_piecewise_constant_has_positive_exponential_rate_of_uniformExponentialRateCertificate_on_pieces_eventually_all_positive

/--
Lemma C.4 forward direction from uniform exponential-rate certificates, using
the eventual-positive normalized-log Laplace path, with endpoint support and
monotonicity supplied by `BinaryEndpointLevelVector`.
-/
abbrev paper_lemmaC4_endpoint_piecewise_constant_has_positive_exponential_rate_of_uniformExponentialRateCertificate_on_pieces_eventually_endpointLevelVector :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_endpoint_piecewise_constant_has_positive_exponential_rate_of_uniformExponentialRateCertificate_on_pieces_eventually_endpointLevelVector

/--
Lemma C.4 forward direction from uniform normalized-log rate certificates on
each selected ordered rectangle.
-/
abbrev paper_lemmaC4_endpoint_piecewise_constant_has_positive_exponential_rate_of_uniformNormalizedLogRateCertificate_on_pieces_eventually_all_positive :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_endpoint_piecewise_constant_has_positive_exponential_rate_of_uniformNormalizedLogRateCertificate_on_pieces_eventually_all_positive

/--
Lemma C.4 forward direction from uniform normalized-log certificates, with
endpoint support and monotonicity supplied by `BinaryEndpointLevelVector`.
-/
abbrev paper_lemmaC4_endpoint_piecewise_constant_has_positive_exponential_rate_of_uniformNormalizedLogRateCertificate_on_pieces_eventually_endpointLevelVector :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_endpoint_piecewise_constant_has_positive_exponential_rate_of_uniformNormalizedLogRateCertificate_on_pieces_eventually_endpointLevelVector

/--
Lemma C.4 forward-direction certificate: a positive adjacent minimum exponent
in the finite component decomposition yields a positive exponential rate for
the decomposed objective.
-/
theorem paper_lemmaC4_positive_rate_of_dominating_adjacent_subfamily_positive_min
    {Component Adjacent : Type*} [Fintype Component] [DecidableEq Component]
    (componentError : Component → ℕ → ℝ)
    (weight rate : Component → ℝ)
    (selectAdjacent : Adjacent → Component)
    (hweight_nonneg : ∀ cpt : Component, 0 ≤ weight cpt)
    (hcert :
      ∀ cpt : Component,
        ExponentialRateCertificate (componentError cpt) (rate cpt))
    (minAdjacent : Adjacent)
    (hweight_pos : 0 < weight (selectAdjacent minAdjacent))
    (hadj_min :
      ∀ adj : Adjacent,
        rate (selectAdjacent minAdjacent) ≤ rate (selectAdjacent adj))
    (hadj_dominates :
      ∀ cpt : Component,
        ∃ adj : Adjacent, rate (selectAdjacent adj) ≤ rate cpt)
    (hmin_pos : 0 < rate (selectAdjacent minAdjacent)) :
    ∃ c : ℝ, 0 < c ∧
      HasExponentialRate
        (fun k : ℕ =>
          ∑ cpt : Component, weight cpt * componentError cpt k)
        c :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_positive_rate_of_dominating_adjacent_subfamily_positive_min
    componentError weight rate selectAdjacent hweight_nonneg hcert
    minAdjacent hweight_pos hadj_min hadj_dominates hmin_pos

/--
Finite Theorem 3.1 aggregation bridge in source-objective form: for any finite
comparison family, pairwise threshold-rate LDP certificates imply an
exponential upper bound on the weighted `1 - W_k` error.
-/
theorem finite_binary_ranking_objective_error_upper_bound_from_pairwise_certificates
    {Seller Rating Pair : Type*} [Fintype Rating] [DecidableEq Rating]
    [Fintype Pair]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
    (C : PairwiseThresholdRateTopLdpCertificate M sampleRate pairHi pairLo)
    {weight : Pair → ℝ} {targetRate : ℝ}
    (hweight : ∀ p : Pair, 0 ≤ weight p)
    (hweight_sum : ∑ p : Pair, weight p = 1)
    (hrate : ∀ p : Pair, targetRate < C.rate p) :
    HasExpUpperBoundWithConst
      (fun k : ℕ =>
        1 - finiteFloorPkObjective M sampleRate pairHi pairLo weight k)
      targetRate :=
  finiteBinaryRankingObjective_oneSub_hasExpUpperBound_of_pairwise_rate_certificates
    M sampleRate pairHi pairLo C hweight hweight_sum hrate

/--
Uniform-pair finite Theorem 3.1 aggregation bridge for the source's average
ranking objective.
-/
theorem finite_binary_uniform_ranking_objective_error_upper_bound_from_pairwise_certificates
    {Seller Rating Pair : Type*} [Fintype Rating] [DecidableEq Rating]
    [Fintype Pair] [Nonempty Pair]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
    (C : PairwiseThresholdRateTopLdpCertificate M sampleRate pairHi pairLo)
    {targetRate : ℝ}
    (hrate : ∀ p : Pair, targetRate < C.rate p) :
    HasExpUpperBoundWithConst
      (fun k : ℕ =>
        1 - finiteUniformFloorPkObjective M sampleRate pairHi pairLo k)
      targetRate :=
  finiteBinaryRankingObjective_oneSub_hasExpUpperBound_of_uniform_pairwise_rate_certificates
    M sampleRate pairHi pairLo C hrate

/--
Finite Theorem 3.1 aggregation bridge from explicit pairwise `1 - P_k`
error-rate certificates. This version supports mixed endpoint and interior
adjacent-pair certificates.
-/
theorem finite_binary_ranking_objective_exact_rate_from_error_rate_certificates
    {Seller Rating Pair : Type*} [Fintype Rating] [DecidableEq Rating]
    [Fintype Pair] [DecidableEq Pair]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
    (E : FiniteErrorRateCertificate Pair)
    (herror :
      ∀ p : Pair,
        E.errorProb p =
          twoSampleFloorPkComplementErrorProb M sampleRate (pairHi p) (pairLo p))
    {weight : Pair → ℝ}
    (hweight_nonneg : ∀ p : Pair, 0 ≤ weight p)
    (hweight_sum : ∑ p : Pair, weight p = 1)
    (pMin : Pair)
    (hweight_pos : 0 < weight pMin)
    (hrate_ge : ∀ p : Pair, E.rate pMin ≤ E.rate p) :
    HasExponentialRate
      (fun k : ℕ =>
        1 - finiteFloorPkObjective M sampleRate pairHi pairLo weight k)
      (E.rate pMin) :=
  finiteBinaryRankingObjective_oneSub_hasExponentialRate_of_error_rate_certificate_min
    M sampleRate pairHi pairLo E herror
    hweight_nonneg hweight_sum pMin hweight_pos hrate_ge

/--
Uniform finite Theorem 3.1 aggregation bridge from explicit pairwise `1 - P_k`
error-rate certificates.
-/
theorem finite_binary_uniform_ranking_objective_exact_rate_from_error_rate_certificates
    {Seller Rating Pair : Type*} [Fintype Rating] [DecidableEq Rating]
    [Fintype Pair] [DecidableEq Pair] [Nonempty Pair]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
    (E : FiniteErrorRateCertificate Pair)
    (herror :
      ∀ p : Pair,
        E.errorProb p =
          twoSampleFloorPkComplementErrorProb M sampleRate (pairHi p) (pairLo p))
    (pMin : Pair)
    (hrate_ge : ∀ p : Pair, E.rate pMin ≤ E.rate p) :
    HasExponentialRate
      (fun k : ℕ =>
        1 - finiteUniformFloorPkObjective M sampleRate pairHi pairLo k)
      (E.rate pMin) :=
  finiteBinaryRankingObjective_oneSub_hasExponentialRate_of_uniform_error_rate_certificate_min
    M sampleRate pairHi pairLo E herror pMin hrate_ge

/--
Adjacent-chain finite Theorem 3.1 bridge: adjacent pairwise certificates give
an exponential upper bound on the uniform adjacent objective error.
-/
theorem finite_binary_adjacent_uniform_objective_error_upper_bound_from_pairwise_certificates
    {m : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel (Fin (m + 2)) Rating)
    (sampleRate : Fin (m + 2) → ℝ)
    (C :
      PairwiseThresholdRateTopLdpCertificate M sampleRate
        (fun i : Fin (m + 1) => adjacentHighIndex i)
        (fun i : Fin (m + 1) => adjacentLowIndex i))
    {targetRate : ℝ}
    (hrate : ∀ i : Fin (m + 1), targetRate < C.rate i) :
    HasExpUpperBoundWithConst
      (fun k : ℕ =>
        1 -
          finiteUniformFloorPkObjective M sampleRate
            (fun i : Fin (m + 1) => adjacentHighIndex i)
            (fun i : Fin (m + 1) => adjacentLowIndex i) k)
      targetRate :=
  finiteBinaryAdjacentUniformObjective_oneSub_hasExpUpperBound_of_pairwise_rate_certificates
    M sampleRate C hrate

/--
Adjacent-chain finite Theorem 3.1 exact-rate bridge from explicit pairwise
`1 - P_k` error-rate certificates. This is the source-facing aggregation
surface for mixed endpoint/interior adjacent-pair proofs.
-/
theorem finite_binary_adjacent_uniform_objective_exact_rate_from_error_rate_certificates
    {m : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel (Fin (m + 2)) Rating)
    (sampleRate : Fin (m + 2) → ℝ)
    (E : FiniteErrorRateCertificate (Fin (m + 1)))
    (herror :
      ∀ i : Fin (m + 1),
        E.errorProb i =
          twoSampleFloorPkComplementErrorProb M sampleRate
            (adjacentHighIndex i) (adjacentLowIndex i))
    (iMin : Fin (m + 1))
    (hrate_ge : ∀ i : Fin (m + 1), E.rate iMin ≤ E.rate i) :
    HasExponentialRate
      (fun k : ℕ =>
        1 -
          finiteUniformFloorPkObjective M sampleRate
            (fun i : Fin (m + 1) => adjacentHighIndex i)
            (fun i : Fin (m + 1) => adjacentLowIndex i) k)
      (E.rate iMin) :=
  finiteBinaryAdjacentUniformObjective_oneSub_hasExponentialRate_of_error_rate_certificate_min
    M sampleRate E herror iMin hrate_ge

/--
Adjacent-chain finite Theorem 3.1 exact-rate bridge directly from pairwise
nonpositive score-gap left-tail certificates.
-/
theorem finite_binary_adjacent_uniform_objective_exact_rate_from_left_tail_certificates
    {m : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel (Fin (m + 2)) Rating)
    (sampleRate : Fin (m + 2) → ℝ)
    (rate : Fin (m + 1) → ℝ)
    (leftTail :
      ∀ i : Fin (m + 1),
        ExponentialRateCertificate
          (twoSampleFloorScoreGapLeftTailProb M sampleRate
            (adjacentHighIndex i) (adjacentLowIndex i))
          (rate i))
    (iMin : Fin (m + 1))
    (hrate_ge : ∀ i : Fin (m + 1), rate iMin ≤ rate i) :
    HasExponentialRate
      (fun k : ℕ =>
        1 -
          finiteUniformFloorPkObjective M sampleRate
            (fun i : Fin (m + 1) => adjacentHighIndex i)
            (fun i : Fin (m + 1) => adjacentLowIndex i) k)
      (rate iMin) :=
  finiteBinaryAdjacentUniformObjective_oneSub_hasExponentialRate_of_leftTail_certificates_min
    M sampleRate rate leftTail iMin hrate_ge

/--
Weighted adjacent-chain finite Theorem 3.1 exact-rate bridge directly from
pairwise nonpositive score-gap left-tail certificates.
-/
theorem finite_binary_adjacent_weighted_objective_exact_rate_from_left_tail_certificates
    {m : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel (Fin (m + 2)) Rating)
    (sampleRate : Fin (m + 2) → ℝ)
    (rate : Fin (m + 1) → ℝ)
    (leftTail :
      ∀ i : Fin (m + 1),
        ExponentialRateCertificate
          (twoSampleFloorScoreGapLeftTailProb M sampleRate
            (adjacentHighIndex i) (adjacentLowIndex i))
          (rate i))
    {weight : Fin (m + 1) → ℝ}
    (hweight_nonneg : ∀ i : Fin (m + 1), 0 ≤ weight i)
    (hweight_sum : ∑ i : Fin (m + 1), weight i = 1)
    (iMin : Fin (m + 1))
    (hweight_pos : 0 < weight iMin)
    (hrate_ge : ∀ i : Fin (m + 1), rate iMin ≤ rate i) :
    HasExponentialRate
      (fun k : ℕ =>
        1 -
          finiteFloorPkObjective M sampleRate
            (fun i : Fin (m + 1) => adjacentHighIndex i)
            (fun i : Fin (m + 1) => adjacentLowIndex i) weight k)
      (rate iMin) :=
  finiteBinaryAdjacentWeightedObjective_oneSub_hasExponentialRate_of_leftTail_certificates_min
    M sampleRate rate leftTail hweight_nonneg hweight_sum iMin
    hweight_pos hrate_ge

/--
Endpoint-aware adjacent-chain pairwise left-tail certificates for the paper's
boundary convention `t_0 = 0`, `t_last = 1`.
-/
theorem finite_binary_adjacent_endpoint_left_tail_certificates
    {m : ℕ} (hm : 0 < m)
    (successProb : Fin (m + 2) → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hfirst_zero : successProb (firstLevelIndex : Fin (m + 2)) = 0)
    (hlast_one : successProb (lastLevelIndex : Fin (m + 2)) = 1)
    (hprob_pos_of_not_first :
      ∀ θ : Fin (m + 2), θ.val ≠ 0 → 0 < successProb θ)
    (hprob_lt_one_of_not_last :
      ∀ θ : Fin (m + 2), θ.val ≠ m + 1 → successProb θ < 1)
    (sampleRate : Fin (m + 2) → ℝ)
    (hpositive_hi :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hpositive_lo :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (hordered :
      ∀ i : Fin (m + 1),
        successProb (adjacentLowIndex i) ≤ successProb (adjacentHighIndex i)) :
    ∀ i : Fin (m + 1),
      ExponentialRateCertificate
        (twoSampleFloorScoreGapLeftTailProb
          (binaryRatingModel successProb hprob0 hprob1) sampleRate
          (adjacentHighIndex i) (adjacentLowIndex i))
        (binaryEndpointAwareAdjacentRate successProb sampleRate i) :=
  binaryEndpointAwareAdjacentRate_leftTail_certificates
    hm successProb hprob0 hprob1 hfirst_zero hlast_one
    hprob_pos_of_not_first hprob_lt_one_of_not_last sampleRate
    hpositive_hi hpositive_lo hordered

/--
Endpoint-aware adjacent-chain pairwise left-tail certificates with the
boundary and interior support facts supplied by `BinaryEndpointLevelVector`.
-/
theorem finite_binary_adjacent_endpoint_left_tail_certificates_from_endpoint_level_vector
    {m : ℕ} (hm : 0 < m)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector successProb)
    (hpositive_hi :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hpositive_lo :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i)) :
    ∀ i : Fin (m + 1),
      ExponentialRateCertificate
        (twoSampleFloorScoreGapLeftTailProb
          (binaryRatingModel successProb
            (BinaryEndpointLevelVector_nonneg hlevels)
            (BinaryEndpointLevelVector_le_one hlevels)) sampleRate
          (adjacentHighIndex i) (adjacentLowIndex i))
        (binaryEndpointAwareAdjacentRate successProb sampleRate i) :=
  binaryEndpointAwareAdjacentRate_leftTail_certificates_of_endpointLevelVector
    hm successProb sampleRate hlevels hpositive_hi hpositive_lo

/--
Endpoint-aware finite adjacent-chain exact-rate theorem for weighted adjacent
objectives, with endpoint/support facts supplied by `BinaryEndpointLevelVector`.
-/
abbrev finite_binary_adjacent_weighted_objective_exact_rate_from_endpoint_level_vector_min
    {m : ℕ} :=
  GJ19OptimalBinaryRatingSystems.finiteBinaryAdjacentWeightedObjective_oneSub_hasExponentialRate_of_endpointLevelVector_min
    (m := m)

/--
Endpoint-aware finite adjacent-chain exact-rate theorem for the uniform
adjacent objective, with endpoint/support facts supplied by
`BinaryEndpointLevelVector`.
-/
abbrev finite_binary_adjacent_uniform_objective_exact_rate_from_endpoint_level_vector_min
    {m : ℕ} :=
  GJ19OptimalBinaryRatingSystems.finiteBinaryAdjacentUniformObjective_oneSub_hasExponentialRate_of_endpointLevelVector_min
    (m := m)

/--
Endpoint-aware finite adjacent-chain exact-rate theorem for weighted adjacent
objectives under the paper's boundary convention `t_0 = 0`, `t_last = 1`.
-/
theorem finite_binary_adjacent_weighted_objective_exact_rate_from_endpoint_weighted_common_threshold
    {m : ℕ} (hm : 0 < m)
    (successProb : Fin (m + 2) → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hfirst_zero : successProb (firstLevelIndex : Fin (m + 2)) = 0)
    (hlast_one : successProb (lastLevelIndex : Fin (m + 2)) = 1)
    (hprob_pos_of_not_first :
      ∀ θ : Fin (m + 2), θ.val ≠ 0 → 0 < successProb θ)
    (hprob_lt_one_of_not_last :
      ∀ θ : Fin (m + 2), θ.val ≠ m + 1 → successProb θ < 1)
    (sampleRate : Fin (m + 2) → ℝ)
    (hpositive_hi :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hpositive_lo :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (hordered :
      ∀ i : Fin (m + 1),
        successProb (adjacentLowIndex i) ≤ successProb (adjacentHighIndex i))
    {weight : Fin (m + 1) → ℝ}
    (hweight_nonneg : ∀ i : Fin (m + 1), 0 ≤ weight i)
    (hweight_sum : ∑ i : Fin (m + 1), weight i = 1)
    (iMin : Fin (m + 1))
    (hweight_pos : 0 < weight iMin)
    (hrate_ge :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate iMin ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate i) :
    HasExponentialRate
      (fun k : ℕ =>
        1 -
          finiteFloorPkObjective
            (binaryRatingModel successProb hprob0 hprob1) sampleRate
            (fun i : Fin (m + 1) => adjacentHighIndex i)
            (fun i : Fin (m + 1) => adjacentLowIndex i) weight k)
      (binaryEndpointAwareAdjacentRate successProb sampleRate iMin) :=
  finiteBinaryAdjacentWeightedObjective_oneSub_hasExponentialRate_of_endpoint_weighted_common_threshold_min
    hm successProb hprob0 hprob1 hfirst_zero hlast_one
    hprob_pos_of_not_first hprob_lt_one_of_not_last sampleRate
    hpositive_hi hpositive_lo hordered hweight_nonneg hweight_sum iMin
    hweight_pos hrate_ge

/--
Endpoint-aware finite adjacent-chain exact-rate theorem for the paper's
boundary convention `t_0 = 0`, `t_last = 1`. The first and last adjacent
comparisons use endpoint rates, and every middle adjacent comparison uses the
closed weighted Bernoulli rate.

Source status: finite source-boundary exact-rate theorem for Theorem 3.1's
adjacent-chain model.
-/
theorem finite_binary_adjacent_uniform_objective_exact_rate_from_endpoint_weighted_common_threshold
    {m : ℕ} (hm : 0 < m)
    (successProb : Fin (m + 2) → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hfirst_zero : successProb (firstLevelIndex : Fin (m + 2)) = 0)
    (hlast_one : successProb (lastLevelIndex : Fin (m + 2)) = 1)
    (hprob_pos_of_not_first :
      ∀ θ : Fin (m + 2), θ.val ≠ 0 → 0 < successProb θ)
    (hprob_lt_one_of_not_last :
      ∀ θ : Fin (m + 2), θ.val ≠ m + 1 → successProb θ < 1)
    (sampleRate : Fin (m + 2) → ℝ)
    (hpositive_hi :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hpositive_lo :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (hordered :
      ∀ i : Fin (m + 1),
        successProb (adjacentLowIndex i) ≤ successProb (adjacentHighIndex i))
    (iMin : Fin (m + 1))
    (hrate_ge :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate iMin ≤
          binaryEndpointAwareAdjacentRate successProb sampleRate i) :
    HasExponentialRate
      (fun k : ℕ =>
        1 -
          finiteUniformFloorPkObjective
            (binaryRatingModel successProb hprob0 hprob1) sampleRate
            (fun i : Fin (m + 1) => adjacentHighIndex i)
            (fun i : Fin (m + 1) => adjacentLowIndex i) k)
      (binaryEndpointAwareAdjacentRate successProb sampleRate iMin) :=
  finiteBinaryAdjacentUniformObjective_oneSub_hasExponentialRate_of_endpoint_weighted_common_threshold_min
    hm successProb hprob0 hprob1 hfirst_zero hlast_one
    hprob_pos_of_not_first hprob_lt_one_of_not_last sampleRate
    hpositive_hi hpositive_lo hordered iMin hrate_ge

/--
Finite Theorem 3.1 exact-rate bridge for an equalized endpoint-normalized
binary level vector. This combines the finite Lemma 3.1 maximin certificate
with the adjacent-chain aggregation theorem: the error of the finite uniform
objective decays at the common endpoint-aware adjacent rate.
-/
theorem finite_binary_adjacent_uniform_objective_exact_rate_from_equalized_endpoint_levels
    {m : ℕ} (hm : 0 < m)
    (successProb sampleRate : Fin (m + 2) → ℝ) {r : ℝ}
    (hlevels : BinaryEndpointLevelVector successProb)
    (hpositive_hi :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hpositive_lo :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (heq :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate i = r) :
    HasExponentialRate
      (fun k : ℕ =>
        1 -
          finiteUniformFloorPkObjective
            (binaryRatingModel successProb
              (BinaryEndpointLevelVector_nonneg hlevels)
              (BinaryEndpointLevelVector_le_one hlevels)) sampleRate
            (fun i : Fin (m + 1) => adjacentHighIndex i)
            (fun i : Fin (m + 1) => adjacentLowIndex i) k)
      r :=
  finiteBinaryAdjacentUniformObjective_oneSub_hasExponentialRate_of_equalized_endpoint_levels
    hm successProb sampleRate hlevels hpositive_hi hpositive_lo heq

/--
Source-shaped finite Theorem 3.1 exact-rate bridge: if an endpoint-normalized
binary level vector pairwise equalizes all adjacent rates, the finite uniform
objective error decays at the finite worst-adjacent rate.
-/
theorem finite_binary_adjacent_uniform_objective_exact_rate_from_pairwise_equalized_endpoint_levels
    {m : ℕ} (hm : 0 < m)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector successProb)
    (hpositive_hi :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hpositive_lo :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (heq : BinaryEndpointAwareAdjacentRatesEqualize successProb sampleRate) :
    HasExponentialRate
      (fun k : ℕ =>
        1 -
          finiteUniformFloorPkObjective
            (binaryRatingModel successProb
              (BinaryEndpointLevelVector_nonneg hlevels)
              (BinaryEndpointLevelVector_le_one hlevels)) sampleRate
            (fun i : Fin (m + 1) => adjacentHighIndex i)
            (fun i : Fin (m + 1) => adjacentLowIndex i) k)
      (binaryEndpointAwareAdjacentRateObjective successProb sampleRate) :=
  finiteBinaryAdjacentUniformObjective_oneSub_hasExponentialRate_of_pairwise_equalized_endpoint_levels
    hm successProb sampleRate hlevels hpositive_hi hpositive_lo heq

/--
Weighted finite Theorem 3.1 exact-rate bridge for an equalized
endpoint-normalized binary level vector.
-/
theorem finite_binary_adjacent_weighted_objective_exact_rate_from_equalized_endpoint_levels
    {m : ℕ} (hm : 0 < m)
    (successProb sampleRate : Fin (m + 2) → ℝ) {r : ℝ}
    (hlevels : BinaryEndpointLevelVector successProb)
    (hpositive_hi :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hpositive_lo :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    {weight : Fin (m + 1) → ℝ}
    (hweight_nonneg : ∀ i : Fin (m + 1), 0 ≤ weight i)
    (hweight_sum : ∑ i : Fin (m + 1), weight i = 1)
    (iMin : Fin (m + 1))
    (hweight_pos : 0 < weight iMin)
    (heq :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate successProb sampleRate i = r) :
    HasExponentialRate
      (fun k : ℕ =>
        1 -
          finiteFloorPkObjective
            (binaryRatingModel successProb
              (BinaryEndpointLevelVector_nonneg hlevels)
              (BinaryEndpointLevelVector_le_one hlevels)) sampleRate
            (fun i : Fin (m + 1) => adjacentHighIndex i)
            (fun i : Fin (m + 1) => adjacentLowIndex i) weight k)
      r :=
  finiteBinaryAdjacentWeightedObjective_oneSub_hasExponentialRate_of_equalized_endpoint_levels
    hm successProb sampleRate hlevels hpositive_hi hpositive_lo
    hweight_nonneg hweight_sum iMin hweight_pos heq

/--
Source-shaped weighted finite Theorem 3.1 exact-rate bridge: if an
endpoint-normalized binary level vector pairwise equalizes all adjacent rates,
the weighted adjacent objective error decays at the finite worst-adjacent rate.
-/
theorem finite_binary_adjacent_weighted_objective_exact_rate_from_pairwise_equalized_endpoint_levels
    {m : ℕ} (hm : 0 < m)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector successProb)
    (hpositive_hi :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hpositive_lo :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    {weight : Fin (m + 1) → ℝ}
    (hweight_nonneg : ∀ i : Fin (m + 1), 0 ≤ weight i)
    (hweight_sum : ∑ i : Fin (m + 1), weight i = 1)
    (iMin : Fin (m + 1))
    (hweight_pos : 0 < weight iMin)
    (heq : BinaryEndpointAwareAdjacentRatesEqualize successProb sampleRate) :
    HasExponentialRate
      (fun k : ℕ =>
        1 -
          finiteFloorPkObjective
            (binaryRatingModel successProb
              (BinaryEndpointLevelVector_nonneg hlevels)
              (BinaryEndpointLevelVector_le_one hlevels)) sampleRate
            (fun i : Fin (m + 1) => adjacentHighIndex i)
            (fun i : Fin (m + 1) => adjacentLowIndex i) weight k)
      (binaryEndpointAwareAdjacentRateObjective successProb sampleRate) :=
  finiteBinaryAdjacentWeightedObjective_oneSub_hasExponentialRate_of_pairwise_equalized_endpoint_levels
    hm successProb sampleRate hlevels hpositive_hi hpositive_lo
    hweight_nonneg hweight_sum iMin hweight_pos heq

/--
Lemma C.4 finite forward direction: an endpoint-normalized piecewise-constant
binary level vector with equalized adjacent rates gives a positive exponential
rate for every positive-weight adjacent objective.
-/
theorem paper_lemmaC4_endpoint_piecewise_constant_has_positive_exponential_rate
    {m : ℕ} (hm : 0 < m)
    (successProb sampleRate : Fin (m + 2) → ℝ)
    (hlevels : BinaryEndpointLevelVector successProb)
    (hpositive_hi :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hpositive_lo :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    {weight : Fin (m + 1) → ℝ}
    (hweight_nonneg : ∀ i : Fin (m + 1), 0 ≤ weight i)
    (hweight_sum : ∑ i : Fin (m + 1), weight i = 1)
    (iMin : Fin (m + 1))
    (hweight_pos : 0 < weight iMin)
    (heq : BinaryEndpointAwareAdjacentRatesEqualize successProb sampleRate) :
    ∃ c : ℝ, 0 < c ∧
      HasExponentialRate
        (fun k : ℕ =>
          1 -
            finiteFloorPkObjective
              (binaryRatingModel successProb
                (BinaryEndpointLevelVector_nonneg hlevels)
                (BinaryEndpointLevelVector_le_one hlevels)) sampleRate
              (fun i : Fin (m + 1) => adjacentHighIndex i)
              (fun i : Fin (m + 1) => adjacentLowIndex i) weight k)
        c :=
  GJ19OptimalBinaryRatingSystems.lemmaC4_endpoint_piecewise_constant_has_positive_exponential_rate
    hm successProb sampleRate hlevels hpositive_hi hpositive_lo
    hweight_nonneg hweight_sum iMin hweight_pos heq

/--
Finite Theorem 3.1 for chains with more than one interior level: positive
sample rates determine an endpoint-normalized equalized binary level vector,
and the adjacent uniform objective has exponential rate equal to that vector's
finite worst-adjacent rate.
-/
theorem finite_binary_adjacent_uniform_objective_exact_rate_from_forward_clipped_levels
    {m : ℕ} (hm : 1 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k) :
    ∃ levels : Fin (m + 2) → ℝ,
      ∃ hlevels : BinaryEndpointLevelVector levels,
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate ∧
          HasExponentialRate
            (fun k : ℕ =>
              1 -
                finiteUniformFloorPkObjective
                  (binaryRatingModel levels
                    (BinaryEndpointLevelVector_nonneg hlevels)
                    (BinaryEndpointLevelVector_le_one hlevels)) sampleRate
                  (fun i : Fin (m + 1) => adjacentHighIndex i)
                  (fun i : Fin (m + 1) => adjacentLowIndex i) k)
            (binaryEndpointAwareAdjacentRateObjective levels sampleRate) := by
  have hsample_high :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i) :=
    binaryEndpointSampleRateNat_pos_adjacentHigh sampleRate hsample_pos
  have hsample_low :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i) :=
    binaryEndpointSampleRateNat_pos_adjacentLow sampleRate hsample_pos
  rcases
    lemma31_forward_clipped_equalized_rates_exist_unique
      hm sampleRate hsample_pos with
    ⟨levels, hlevels, _huniq⟩
  refine ⟨levels, hlevels.1, hlevels.2, ?_⟩
  exact
    finite_binary_adjacent_uniform_objective_exact_rate_from_pairwise_equalized_endpoint_levels
      (show 0 < m by omega) levels sampleRate hlevels.1
      hsample_high hsample_low hlevels.2

/--
Weighted finite Theorem 3.1 for chains with more than one interior level:
positive sample rates determine an endpoint-normalized equalized binary level
vector, and every positive-weight adjacent objective has exponential rate
equal to that vector's finite worst-adjacent rate.
-/
theorem finite_binary_adjacent_weighted_objective_exact_rate_from_forward_clipped_levels
    {m : ℕ} (hm : 1 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k)
    {weight : Fin (m + 1) → ℝ}
    (hweight_nonneg : ∀ i : Fin (m + 1), 0 ≤ weight i)
    (hweight_sum : ∑ i : Fin (m + 1), weight i = 1)
    (iMin : Fin (m + 1))
    (hweight_pos : 0 < weight iMin) :
    ∃ levels : Fin (m + 2) → ℝ,
      ∃ hlevels : BinaryEndpointLevelVector levels,
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate ∧
          HasExponentialRate
            (fun k : ℕ =>
              1 -
                finiteFloorPkObjective
                  (binaryRatingModel levels
                    (BinaryEndpointLevelVector_nonneg hlevels)
                    (BinaryEndpointLevelVector_le_one hlevels)) sampleRate
                  (fun i : Fin (m + 1) => adjacentHighIndex i)
                  (fun i : Fin (m + 1) => adjacentLowIndex i) weight k)
            (binaryEndpointAwareAdjacentRateObjective levels sampleRate) :=
  finiteBinaryAdjacentWeightedObjective_oneSub_hasExponentialRate_from_forward_clipped_levels
    hm sampleRate hsample_pos hweight_nonneg hweight_sum iMin hweight_pos

/--
Lemma C.4 finite forward direction with constructed endpoint-normalized
piecewise-constant levels: positive sample rates determine equalized levels
whose positive-weight adjacent objective has a positive exponential rate.
-/
theorem paper_lemmaC4_forward_clipped_endpoint_piecewise_constant_has_positive_exponential_rate
    {m : ℕ} (hm : 1 < m)
    (sampleRate : Fin (m + 2) → ℝ)
    (hsample_pos :
      ∀ k : ℕ, k < m + 2 → 0 < binaryEndpointSampleRateNat sampleRate k)
    {weight : Fin (m + 1) → ℝ}
    (hweight_nonneg : ∀ i : Fin (m + 1), 0 ≤ weight i)
    (hweight_sum : ∑ i : Fin (m + 1), weight i = 1)
    (iMin : Fin (m + 1))
    (hweight_pos : 0 < weight iMin) :
    ∃ levels : Fin (m + 2) → ℝ,
      ∃ hlevels : BinaryEndpointLevelVector levels,
        BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate ∧
          ∃ c : ℝ, 0 < c ∧
            HasExponentialRate
              (fun k : ℕ =>
                1 -
                  finiteFloorPkObjective
                    (binaryRatingModel levels
                      (BinaryEndpointLevelVector_nonneg hlevels)
                      (BinaryEndpointLevelVector_le_one hlevels)) sampleRate
                    (fun i : Fin (m + 1) => adjacentHighIndex i)
                    (fun i : Fin (m + 1) => adjacentLowIndex i) weight k)
              c :=
  lemmaC4_forward_clipped_endpoint_piecewise_constant_has_positive_exponential_rate
    hm sampleRate hsample_pos hweight_nonneg hweight_sum iMin hweight_pos

/--
Lemma C.5 first endpoint split algebra: the source's first refined level
equalizes the endpoint rate from zero with the next uniform closed threshold
rate.
-/
theorem lemmaC5_first_endpoint_split_equalizes_rates
    {pHi : ℝ} (hpHi0 : 0 ≤ pHi) (hpHi1 : pHi ≤ 1) :
    -Real.log (1 - bernoulliFirstEndpointEqualSplit pHi) =
      weightedBernoulliClosedThresholdRate 1 1 pHi
        (bernoulliFirstEndpointEqualSplit pHi) :=
  lemmaC5_uniform_firstEndpointEqualSplit_rate_eq hpHi0 hpHi1

/--
Lemma C.5 interior split algebra: the source's interior refined level
equalizes the two adjacent uniform closed threshold rates.
-/
theorem lemmaC5_interior_split_equalizes_rates
    {pLo pHi : ℝ} (hpLo0 : 0 ≤ pLo) (hpHi1 : pHi ≤ 1)
    (hlt : pLo < pHi) :
    weightedBernoulliClosedThresholdRate 1 1
        (bernoulliInteriorEqualSplit pLo pHi) pLo =
      weightedBernoulliClosedThresholdRate 1 1 pHi
        (bernoulliInteriorEqualSplit pLo pHi) :=
  lemmaC5_uniform_interiorEqualSplit_rate_eq hpLo0 hpHi1 hlt

/--
Lemma C.5 last endpoint split algebra: the source's last refined level
equalizes the preceding uniform closed threshold rate with the endpoint rate
to one.
-/
theorem lemmaC5_last_endpoint_split_equalizes_rates
    {pLo : ℝ} (hpLo0 : 0 ≤ pLo) (hpLo1 : pLo ≤ 1) :
    weightedBernoulliClosedThresholdRate 1 1
        (bernoulliLastEndpointEqualSplit pLo) pLo =
      -Real.log (bernoulliLastEndpointEqualSplit pLo) :=
  lemmaC5_uniform_lastEndpointEqualSplit_rate_eq hpLo0 hpLo1

/-- Lemma C.5 doubled-chain constructor for uniform matching. -/
def lemmaC5_uniform_doubled_endpoint_levels {m : ℕ}
    (oldLevels : Fin (m + 2) → ℝ) : Fin ((2 * m + 1) + 2) → ℝ :=
  uniformDoubledEndpointLevels oldLevels

/-- Lemma C.5 doubled chain: even refined indices copy old levels. -/
theorem lemmaC5_uniform_doubled_endpoint_levels_even
    {m : ℕ} (oldLevels : Fin (m + 2) → ℝ) (i : Fin (m + 2)) :
    lemmaC5_uniform_doubled_endpoint_levels oldLevels
        ⟨2 * i.val, by omega⟩ = oldLevels i :=
  uniformDoubledEndpointLevels_even oldLevels i


/--
Lemma C.5 doubled chain: first odd index has the endpoint split formula.

Source status: direct paper-facing Lemma C.5 first-odd endpoint formula row.
-/
theorem lemmaC5_uniform_doubled_endpoint_levels_first_odd
    {m : ℕ} (oldLevels : Fin (m + 2) → ℝ) :
    lemmaC5_uniform_doubled_endpoint_levels oldLevels
        (⟨1, by omega⟩ : Fin ((2 * m + 1) + 2)) =
      bernoulliFirstEndpointEqualSplit
        (oldLevels (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))) :=
  uniformDoubledEndpointLevels_first_odd oldLevels


/--
Lemma C.5 doubled chain: last odd index has the endpoint split formula.

Source status: direct paper-facing Lemma C.5 last-odd endpoint formula row.
-/
theorem lemmaC5_uniform_doubled_endpoint_levels_last_odd
    {m : ℕ} (hm : 0 < m) (oldLevels : Fin (m + 2) → ℝ) :
    lemmaC5_uniform_doubled_endpoint_levels oldLevels
        (⟨2 * m + 1, by omega⟩ : Fin ((2 * m + 1) + 2)) =
      bernoulliLastEndpointEqualSplit
        (oldLevels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))) :=
  uniformDoubledEndpointLevels_last_odd hm oldLevels

/-- Lemma C.5 doubled chain: middle odd indices use the interior split. -/
theorem lemmaC5_uniform_doubled_endpoint_levels_middle_odd
    {m k : ℕ} (hk0 : 0 < k) (hkm : k < m)
    (oldLevels : Fin (m + 2) → ℝ) :
    lemmaC5_uniform_doubled_endpoint_levels oldLevels
        (⟨2 * k + 1, by omega⟩ : Fin ((2 * m + 1) + 2)) =
      bernoulliInteriorEqualSplit
        (oldLevels ⟨k, by omega⟩)
        (oldLevels ⟨k + 1, by omega⟩) :=
  uniformDoubledEndpointLevels_middle_odd hk0 hkm oldLevels

/--
Lemma C.5 feasibility certificate: the explicit doubled uniform chain is again
an endpoint-normalized increasing level vector.
-/
theorem lemmaC5_uniform_doubled_endpoint_levels_isEndpointLevelVector
    {m : ℕ} (hm : 0 < m)
    {oldLevels : Fin (m + 2) → ℝ}
    (hold : BinaryEndpointLevelVector oldLevels) :
    BinaryEndpointLevelVector (lemmaC5_uniform_doubled_endpoint_levels oldLevels) :=
  uniformDoubledEndpointLevels_isEndpointLevelVector hm hold

/--
Lemma C.5 local rate equalization: each inserted odd level equalizes the two
refined adjacent rates in its source interval.
-/
theorem lemmaC5_uniform_doubled_endpoint_levels_adjacent_pair_rates_equal
    {m k : ℕ} (hm : 0 < m) (hk : k ≤ m)
    {oldLevels : Fin (m + 2) → ℝ}
    (hold : BinaryEndpointLevelVector oldLevels) :
    binaryEndpointAwareAdjacentRate
        (lemmaC5_uniform_doubled_endpoint_levels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
        (⟨2 * k, by omega⟩ : Fin ((2 * m + 1) + 1)) =
      binaryEndpointAwareAdjacentRate
        (lemmaC5_uniform_doubled_endpoint_levels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
        (⟨2 * k + 1, by omega⟩ : Fin ((2 * m + 1) + 1)) :=
  uniformDoubledEndpointLevels_adjacent_pair_rates_equal hm hk hold

/--
Lemma C.5 global equalization certificate: old uniform equalized adjacent rates
imply equalized adjacent rates for the explicit doubled chain.
-/
theorem lemmaC5_uniform_doubled_endpoint_levels_equalizes
    {m : ℕ} (hm : 0 < m)
    {oldLevels : Fin (m + 2) → ℝ}
    (hold : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ))) :
    BinaryEndpointAwareAdjacentRatesEqualize
      (lemmaC5_uniform_doubled_endpoint_levels oldLevels)
      (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) :=
  uniformDoubledEndpointLevels_equalizes hm hold holdEq

/--
Lemma C.6 finite-chain arithmetic core: if the last adjacent interval is no
wider than every adjacent interval, then its width is at most the reciprocal
of the number of adjacent intervals.
-/
theorem lemmaC6_last_interval_width_le_inv_of_width_minimal
    {m : ℕ} {levels : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels)
    (hlast_width :
      ∀ i : Fin (m + 1),
        levels (adjacentHighIndex (lastAdjacentIndex : Fin (m + 1))) -
            levels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) ≤
          levels (adjacentHighIndex i) - levels (adjacentLowIndex i)) :
    levels (adjacentHighIndex (lastAdjacentIndex : Fin (m + 1))) -
        levels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) ≤
      1 / ((m + 1 : ℕ) : ℝ) :=
  BinaryEndpointLevelVector_last_width_le_inv_of_last_width_le_all
    hlevels hlast_width

/--
Lemma C.6 finite-chain endpoint consequence: if the last adjacent interval is
no wider than every adjacent interval, then the penultimate endpoint level is
at least `1 - 1 / (number of adjacent intervals)`.
-/
theorem lemmaC6_penultimate_level_ge_one_sub_inv_of_width_minimal
    {m : ℕ} {levels : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels)
    (hlast_width :
      ∀ i : Fin (m + 1),
        levels (adjacentHighIndex (lastAdjacentIndex : Fin (m + 1))) -
            levels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) ≤
          levels (adjacentHighIndex i) - levels (adjacentLowIndex i)) :
    1 - 1 / ((m + 1 : ℕ) : ℝ) ≤
      levels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) :=
  BinaryEndpointLevelVector_last_low_ge_one_sub_inv_of_last_width_le_all
    hlevels hlast_width

/--
Lemma C.6 rate-comparison bridge: if every interval narrower than the last
would have strictly smaller adjacent rate than the last interval, then
equalized adjacent rates force the last interval to be no wider than every
interval.
-/
theorem lemmaC6_last_interval_width_le_all_of_equalized_rate_strict_of_width_lt
    {m : ℕ} {levels sampleRate : Fin (m + 2) → ℝ}
    (heq : BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate)
    (hrate_strict :
      ∀ i : Fin (m + 1),
        levels (adjacentHighIndex i) - levels (adjacentLowIndex i) <
            levels (adjacentHighIndex (lastAdjacentIndex : Fin (m + 1))) -
              levels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) →
          binaryEndpointAwareAdjacentRate levels sampleRate i <
            binaryEndpointAwareAdjacentRate levels sampleRate
              (lastAdjacentIndex : Fin (m + 1))) :
    ∀ i : Fin (m + 1),
      levels (adjacentHighIndex (lastAdjacentIndex : Fin (m + 1))) -
          levels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) ≤
        levels (adjacentHighIndex i) - levels (adjacentLowIndex i) :=
  BinaryEndpointAwareAdjacentRatesEqualize_last_width_le_all_of_rate_strict_of_width_lt
    heq hrate_strict

/--
Lemma C.6 endpoint lower-bound bridge with the source's rate-comparison step
isolated as a named premise.
-/
theorem lemmaC6_penultimate_level_ge_one_sub_inv_of_equalized_rate_strict_of_width_lt
    {m : ℕ} {levels sampleRate : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels)
    (heq : BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate)
    (hrate_strict :
      ∀ i : Fin (m + 1),
        levels (adjacentHighIndex i) - levels (adjacentLowIndex i) <
            levels (adjacentHighIndex (lastAdjacentIndex : Fin (m + 1))) -
              levels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) →
          binaryEndpointAwareAdjacentRate levels sampleRate i <
            binaryEndpointAwareAdjacentRate levels sampleRate
              (lastAdjacentIndex : Fin (m + 1))) :
    1 - 1 / ((m + 1 : ℕ) : ℝ) ≤
      levels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) :=
  BinaryEndpointLevelVector_last_low_ge_one_sub_inv_of_equalized_rate_strict_of_width_lt
    hlevels heq hrate_strict

/--
Uniform-matching Lemma C.6 width-minimality: equalized adjacent rates under
uniform matching force the last adjacent interval to be no wider than every
adjacent interval.
-/
theorem lemmaC6_uniform_last_interval_width_le_all_of_equalized_rates
    {m : ℕ} (hm : 0 < m)
    {levels : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels)
    (heq :
      BinaryEndpointAwareAdjacentRatesEqualize levels
        (fun _ : Fin (m + 2) => (1 : ℝ))) :
    ∀ i : Fin (m + 1),
      levels (adjacentHighIndex (lastAdjacentIndex : Fin (m + 1))) -
          levels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) ≤
        levels (adjacentHighIndex i) - levels (adjacentLowIndex i) :=
  BinaryEndpointAwareAdjacentRatesEqualize_uniform_last_width_le_all
    hm hlevels heq

/--
Uniform-matching Lemma C.6 endpoint lower bound: equalized adjacent rates under
uniform matching imply the penultimate level is at least
`1 - 1 / (number of adjacent intervals)`.
-/
theorem lemmaC6_uniform_penultimate_level_ge_one_sub_inv_of_equalized_rates
    {m : ℕ} (hm : 0 < m)
    {levels : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels)
    (heq :
      BinaryEndpointAwareAdjacentRatesEqualize levels
        (fun _ : Fin (m + 2) => (1 : ℝ))) :
    1 - 1 / ((m + 1 : ℕ) : ℝ) ≤
      levels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) :=
  BinaryEndpointLevelVector_uniform_equalized_last_low_ge_one_sub_inv
    hm hlevels heq

/--
Corollary C.2 rate consequence: for endpoint-normalized uniform equalized
level vectors with `N+1` adjacent intervals, the common last adjacent rate
tends to zero.
-/
theorem paper_corollaryC2_uniform_equalized_last_rate_tendsto_zero
    (levels : (N : ℕ) → Fin ((N + 1) + 2) → ℝ)
    (hlevels : ∀ N : ℕ, BinaryEndpointLevelVector (levels N))
    (heq : ∀ N : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels N)
        (fun _ : Fin ((N + 1) + 2) => (1 : ℝ))) :
    Tendsto
      (fun N : ℕ =>
        binaryEndpointAwareAdjacentRate (levels N)
          (fun _ : Fin ((N + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((N + 1) + 1)))
      atTop (nhds 0) :=
  GJ19OptimalBinaryRatingSystems.corollaryC2_uniform_equalized_last_rate_tendsto_zero
    levels hlevels heq

/--
Corollary C.2 mesh consequence: for endpoint-normalized uniform equalized
level vectors, the largest adjacent grid width tends to zero.
-/
theorem paper_corollaryC2_uniform_equalized_adjacent_mesh_tendsto_zero
    (levels : (N : ℕ) → Fin ((N + 1) + 2) → ℝ)
    (hlevels : ∀ N : ℕ, BinaryEndpointLevelVector (levels N))
    (heq : ∀ N : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels N)
        (fun _ : Fin ((N + 1) + 2) => (1 : ℝ))) :
    Tendsto
      (fun N : ℕ =>
        binaryEndpointAdjacentMaxWidth (m := N + 1) (levels N))
      atTop (nhds 0) :=
  GJ19OptimalBinaryRatingSystems.corollaryC2_uniform_equalized_adjacent_mesh_tendsto_zero
    levels hlevels heq

/--
Uniform-matching Lemma C.6 half-bound used in Lemma C.7: equalized adjacent
rates imply the penultimate level is at least `1/2`.
-/
theorem lemmaC6_uniform_penultimate_level_ge_one_half_of_equalized_rates
    {m : ℕ} (hm : 0 < m)
    {levels : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels)
    (heq :
      BinaryEndpointAwareAdjacentRatesEqualize levels
        (fun _ : Fin (m + 2) => (1 : ℝ))) :
    (1 / 2 : ℝ) ≤
      levels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) :=
  BinaryEndpointLevelVector_uniform_equalized_last_low_ge_one_half
    hm hlevels heq

/--
Lemma C.7 algebraic endpoint-refinement step: under uniform matching, the
source's refinement endpoint `(1 + sqrt t_last) / 2` has negative-log rate at
least one fifth of the previous equalized last-adjacent rate.
-/
theorem lemmaC7_uniform_refined_last_rate_ge_one_fifth
    {m : ℕ} (hm : 0 < m)
    {levels : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels)
    (heq :
      BinaryEndpointAwareAdjacentRatesEqualize levels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {refinedLastLow : ℝ}
    (hrefined :
      refinedLastLow =
        (1 +
          Real.sqrt
            (levels
              (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))))) / 2) :
    (1 / 5 : ℝ) *
        binaryEndpointAwareAdjacentRate levels
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1)) ≤
      -Real.log refinedLastLow :=
  BinaryEndpointLevelVector_uniform_refined_last_rate_ge_one_fifth
    hm hlevels heq hrefined

/--
Lemma C.7 objective-rate comparison in certificate form: if a refined uniform
equalized chain has the source's refined last endpoint, its worst-adjacent
rate is at least one fifth of the old equalized worst-adjacent rate.
-/
theorem lemmaC7_uniform_refined_objective_rate_ge_one_fifth
    {mOld mNew : ℕ} (hmOld : 0 < mOld) (hmNew : 0 < mNew)
    {oldLevels : Fin (mOld + 2) → ℝ}
    {newLevels : Fin (mNew + 2) → ℝ}
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (hnewLevels : BinaryEndpointLevelVector newLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (mOld + 2) => (1 : ℝ)))
    (hnewEq :
      BinaryEndpointAwareAdjacentRatesEqualize newLevels
        (fun _ : Fin (mNew + 2) => (1 : ℝ)))
    (hrefined :
      newLevels (adjacentLowIndex (lastAdjacentIndex : Fin (mNew + 1))) =
        (1 +
          Real.sqrt
            (oldLevels
              (adjacentLowIndex (lastAdjacentIndex : Fin (mOld + 1))))) / 2) :
    (1 / 5 : ℝ) *
        binaryEndpointAwareAdjacentRateObjective oldLevels
          (fun _ : Fin (mOld + 2) => (1 : ℝ)) ≤
      binaryEndpointAwareAdjacentRateObjective newLevels
        (fun _ : Fin (mNew + 2) => (1 : ℝ)) :=
  BinaryEndpointLevelVector_uniform_refined_objective_rate_ge_one_fifth
    hmOld hmNew holdLevels hnewLevels holdEq hnewEq hrefined

/--
Lemma C.7 objective-rate comparison for the explicit C.5 doubled chain, with
the doubled-chain feasibility and equalization certificates derived internally.
-/
theorem lemmaC7_uniform_doubled_objective_rate_ge_one_fifth_old_objective
    {m : ℕ} (hm : 0 < m)
    {oldLevels : Fin (m + 2) → ℝ}
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ))) :
    (1 / 5 : ℝ) *
        binaryEndpointAwareAdjacentRateObjective oldLevels
          (fun _ : Fin (m + 2) => (1 : ℝ)) ≤
      binaryEndpointAwareAdjacentRateObjective
        (lemmaC5_uniform_doubled_endpoint_levels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) :=
  uniformDoubledEndpointLevels_objective_rate_ge_one_fifth_old_objective_closed
    hm holdLevels holdEq

/--
Lemma C.8 endpoint step: a lower bound on the first endpoint-aware rate gives
a linear lower bound on the first interior level under uniform matching.
-/
theorem lemmaC8_uniform_first_level_ge_half_of_first_rate_lower
    {m : ℕ} (hm : 0 < m)
    {levels : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels)
    {lower : ℝ}
    (hlower0 : 0 ≤ lower) (hlower1 : lower ≤ 1)
    (hlower_le_first :
      lower ≤
        binaryEndpointAwareAdjacentRate levels
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (firstAdjacentIndex : Fin (m + 1))) :
    lower / 2 ≤
      levels (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) :=
  BinaryEndpointLevelVector_uniform_first_level_ge_half_of_first_rate_lower
    hm hlevels hlower0 hlower1 hlower_le_first

/--
Lemma C.8 endpoint step in equalized form: under uniform equalized adjacent
rates, a lower bound on the last adjacent rate gives the same linear lower
bound on the first interior level.
-/
theorem lemmaC8_uniform_first_level_ge_half_of_equalized_last_rate_lower
    {m : ℕ} (hm : 0 < m)
    {levels : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels)
    (heq :
      BinaryEndpointAwareAdjacentRatesEqualize levels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {lower : ℝ}
    (hlower0 : 0 ≤ lower) (hlower1 : lower ≤ 1)
    (hlower_le_last :
      lower ≤
        binaryEndpointAwareAdjacentRate levels
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1))) :
    lower / 2 ≤
      levels (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) :=
  BinaryEndpointLevelVector_uniform_first_level_ge_half_of_equalized_last_rate_lower
    hm hlevels heq hlower0 hlower1 hlower_le_last

/--
Lemma C.8 endpoint step in equalized objective form: under uniform equalized
adjacent rates, a lower bound on the finite worst-adjacent objective gives a
linear lower bound on the first interior level.
-/
theorem lemmaC8_uniform_first_level_ge_half_of_equalized_objective_rate_lower
    {m : ℕ} (hm : 0 < m)
    {levels : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels)
    (heq :
      BinaryEndpointAwareAdjacentRatesEqualize levels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {lower : ℝ}
    (hlower0 : 0 ≤ lower) (hlower1 : lower ≤ 1)
    (hlower_le_objective :
      lower ≤
        binaryEndpointAwareAdjacentRateObjective levels
          (fun _ : Fin (m + 2) => (1 : ℝ))) :
    lower / 2 ≤
      levels (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) :=
  BinaryEndpointLevelVector_uniform_first_level_ge_half_of_equalized_objective_rate_lower
    hm hlevels heq hlower0 hlower1 hlower_le_objective

/--
Corollary C.3 first-level lower bound for monotone match functions after
normalizing the first nonzero type rate to one.
-/
theorem corollaryC3_monotone_scaled_first_level_ge_half_inv_adjacent_count_sq
    {m : ℕ} (hm : 0 < m)
    {levels sampleRate : Fin (m + 2) → ℝ}
    (hlevels : BinaryEndpointLevelVector levels)
    (heq : BinaryEndpointAwareAdjacentRatesEqualize levels sampleRate)
    (hsample_pos : ∀ idx : Fin (m + 2), 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hfirst_sample :
      sampleRate (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) = 1) :
    ((1 / ((m + 1 : ℕ) : ℝ)) ^ 2) / 2 ≤
      levels (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) :=
  BinaryEndpointAwareAdjacentRatesEqualize_monotone_scaled_first_level_ge_half_inv_adjacent_count_sq
    hm hlevels heq hsample_pos hsample_mono hfirst_sample

/--
Lemma C.5/C.7/C.8 combined certificate: if the C.5 doubled uniform chain is
feasible and equalized, then its first refined level receives the one-tenth
old-objective lower bound supplied by C.7 and C.8.
-/
theorem lemmaC5_C7_C8_uniform_doubled_first_level_ge_one_tenth_old_objective
    {m : ℕ} (hm : 0 < m)
    {oldLevels : Fin (m + 2) → ℝ}
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hnewLevels :
      BinaryEndpointLevelVector
        (lemmaC5_uniform_doubled_endpoint_levels oldLevels))
    (hnewEq :
      BinaryEndpointAwareAdjacentRatesEqualize
        (lemmaC5_uniform_doubled_endpoint_levels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))) :
    ((1 / 5 : ℝ) *
        binaryEndpointAwareAdjacentRateObjective oldLevels
          (fun _ : Fin (m + 2) => (1 : ℝ))) / 2 ≤
      lemmaC5_uniform_doubled_endpoint_levels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) :=
  uniformDoubledEndpointLevels_first_level_ge_one_tenth_old_objective
    hm holdLevels holdEq hnewLevels hnewEq
    (BinaryEndpointLevelVector_uniform_equalized_one_fifth_objective_le_one
      hm holdLevels holdEq)

/--
Lemma C.5/C.7/C.8 combined certificate with doubled-chain feasibility proved
from the explicit C.5 construction.  The remaining input is global equalization
of the doubled chain.
-/
theorem lemmaC5_C7_C8_uniform_doubled_first_level_ge_one_tenth_old_objective_of_equalized
    {m : ℕ} (hm : 0 < m)
    {oldLevels : Fin (m + 2) → ℝ}
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hnewEq :
      BinaryEndpointAwareAdjacentRatesEqualize
        (lemmaC5_uniform_doubled_endpoint_levels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))) :
    ((1 / 5 : ℝ) *
        binaryEndpointAwareAdjacentRateObjective oldLevels
          (fun _ : Fin (m + 2) => (1 : ℝ))) / 2 ≤
      lemmaC5_uniform_doubled_endpoint_levels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) :=
  uniformDoubledEndpointLevels_first_level_ge_one_tenth_old_objective_of_equalized
    hm holdLevels holdEq hnewEq
    (BinaryEndpointLevelVector_uniform_equalized_one_fifth_objective_le_one
      hm holdLevels holdEq)

/--
Lemma C.5/C.7/C.8 combined certificate with the C.5 doubled-chain feasibility
and equalization certificates derived from the old uniform equalized chain.
-/
theorem lemmaC5_C7_C8_uniform_doubled_first_level_ge_one_tenth_old_objective_closed
    {m : ℕ} (hm : 0 < m)
    {oldLevels : Fin (m + 2) → ℝ}
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ))) :
    ((1 / 5 : ℝ) *
        binaryEndpointAwareAdjacentRateObjective oldLevels
          (fun _ : Fin (m + 2) => (1 : ℝ))) / 2 ≤
      lemmaC5_uniform_doubled_endpoint_levels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) :=
  uniformDoubledEndpointLevels_first_level_ge_one_tenth_old_objective_closed
    hm holdLevels holdEq
    (BinaryEndpointLevelVector_uniform_equalized_one_fifth_objective_le_one
      hm holdLevels holdEq)

/--
Lemma C.9 runtime core for Algorithm 1: the source-shaped NestedBisection
operation count is bounded by the reusable nested-bisection closed form once
the outer and inner bisection iteration counts are bounded by `L + 1` and `L`.
-/
theorem lemmaC9_nested_bisection_operation_count_le_stepBound
    {M L outerSteps innerSteps : ℕ}
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    nestedBisectionOperationCount M outerSteps innerSteps ≤
      AppliedModelingLib.Optimization.nestedBisectionStepBound M L :=
  nestedBisectionOperationCount_le_stepBound houter hinner

/--
Lemma C.9 runtime core in finite quadratic form: if the outer bisection has at
most `L + 1` iterations and each inner bisection has at most `L` iterations,
then the source-shaped NestedBisection operation count is at most
`M * (L + 1)^2`.
-/
theorem lemmaC9_nested_bisection_operation_count_le_mul_succ_sq
    {M L outerSteps innerSteps : ℕ} (hM : 0 < M)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    nestedBisectionOperationCount M outerSteps innerSteps ≤
      M * (L + 1) ^ 2 :=
  nestedBisectionOperationCount_le_mul_succ_sq hM houter hinner

/--
Theorem 3.2 approximation-certificate core: if a returned level vector keeps
every adjacent rate within additive `eps` of the optimal equalized rate, then
its finite worst-adjacent objective is within additive `eps` of the optimum.
-/
theorem theorem32_rate_loss_le_of_all_adjacent_rates_ge
    {m : ℕ}
    (optimal returned sampleRate : Fin (m + 2) → ℝ)
    {rStar eps : ℝ}
    (hoptimal :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate optimal sampleRate i = rStar)
    (hreturned :
      ∀ i : Fin (m + 1),
        rStar - eps ≤
          binaryEndpointAwareAdjacentRate returned sampleRate i) :
    binaryEndpointAwareAdjacentRateObjective optimal sampleRate -
        binaryEndpointAwareAdjacentRateObjective returned sampleRate ≤
      eps :=
  binaryEndpointAwareAdjacentRateObjective_loss_le_of_all_rates_ge
    optimal returned sampleRate hoptimal hreturned

/--
Theorem 3.2 rate-loss decomposition: the additive loss is bounded by the
last-interval rate loss plus the inner bisection grid loss.
-/
theorem theorem32_rate_loss_le_of_last_rate_and_grid
    {m : ℕ}
    (optimal returned sampleRate : Fin (m + 2) → ℝ)
    {rStar epsLast epsGrid eps : ℝ}
    (hoptimal :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate optimal sampleRate i = rStar)
    (hlast :
      rStar - epsLast ≤
        binaryEndpointAwareAdjacentRate returned sampleRate
          (lastAdjacentIndex : Fin (m + 1)))
    (hgrid :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate returned sampleRate
            (lastAdjacentIndex : Fin (m + 1)) - epsGrid ≤
          binaryEndpointAwareAdjacentRate returned sampleRate i)
    (heps : epsLast + epsGrid ≤ eps) :
    binaryEndpointAwareAdjacentRateObjective optimal sampleRate -
        binaryEndpointAwareAdjacentRateObjective returned sampleRate ≤
      eps :=
  binaryEndpointAwareAdjacentRateObjective_loss_le_of_last_rate_and_grid
    optimal returned sampleRate hoptimal hlast hgrid heps

/--
Theorem 3.2 shifted-last-level loss bound: moving the final optimal level
right by `delta` loses at most the corresponding linearized logarithmic term.
-/
theorem theorem32_last_rate_shift_log_loss_le_linear
    {g tStar delta : ℝ}
    (hg : 0 ≤ g)
    (htStar : 0 < tStar)
    (hdelta : 0 ≤ delta) :
    g * Real.log ((tStar + delta) / tStar) ≤
      g * (delta / tStar) :=
  binaryEndpointAwareLastRateShift_log_loss_le_linear hg htStar hdelta

/--
Theorem 3.2 source-shaped logarithmic certificate: last-level bisection loss
plus inner-grid loss, bounded by the source's two logarithmic shift terms,
implies additive `eps`-optimality of the finite adjacent objective.
-/
theorem theorem32_rate_loss_le_of_shift_log_certificates
    {m : ℕ}
    (optimal returned sampleRate : Fin (m + 2) → ℝ)
    {rStar gLast tFirstStar tLastStar delta eps : ℝ}
    (hgLast : 0 ≤ gLast)
    (htFirstStar : 0 < tFirstStar)
    (htLastStar : 0 < tLastStar)
    (hdelta : 0 ≤ delta)
    (hoptimal :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate optimal sampleRate i = rStar)
    (hlast :
      rStar -
          gLast * Real.log ((tLastStar + delta) / tLastStar) ≤
        binaryEndpointAwareAdjacentRate returned sampleRate
          (lastAdjacentIndex : Fin (m + 1)))
    (hgrid :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate returned sampleRate
            (lastAdjacentIndex : Fin (m + 1)) -
            gLast * Real.log ((tFirstStar + delta) / tFirstStar) ≤
          binaryEndpointAwareAdjacentRate returned sampleRate i)
    (hlinear :
      gLast * (delta / tLastStar) +
          gLast * (delta / tFirstStar) ≤ eps) :
    binaryEndpointAwareAdjacentRateObjective optimal sampleRate -
        binaryEndpointAwareAdjacentRateObjective returned sampleRate ≤
      eps :=
  binaryEndpointAwareAdjacentRateObjective_loss_le_of_shift_log_certificates
    optimal returned sampleRate hgLast htFirstStar htLastStar hdelta
    hoptimal hlast hgrid hlinear

/--
Theorem 3.2 lower-bound bridge: lower bounds on the first and last optimal
levels turn the linearized reciprocal loss into the source's explicit
epsilon budget.
-/
theorem theorem32_shift_linear_loss_le_of_lower_bounds
    {gLast delta tFirstStar tLastStar firstLower lastLower eps : ℝ}
    (hgLast : 0 ≤ gLast)
    (hdelta : 0 ≤ delta)
    (hfirstLower_pos : 0 < firstLower)
    (hlastLower_pos : 0 < lastLower)
    (hfirstLower : firstLower ≤ tFirstStar)
    (hlastLower : lastLower ≤ tLastStar)
    (hbound :
      gLast * (delta / lastLower) +
          gLast * (delta / firstLower) ≤ eps) :
    gLast * (delta / tLastStar) +
        gLast * (delta / tFirstStar) ≤ eps :=
  binaryEndpointAwareAdjacentRateObjective_shift_linear_loss_le_of_lower_bounds
    hgLast hdelta hfirstLower_pos hlastLower_pos hfirstLower hlastLower
    hbound

/--
Theorem 3.2 delta-choice bridge: choosing `delta` by the reciprocal
first/last lower-bound budget makes the linearized Theorem 3.2 loss at most
`eps`.
-/
theorem theorem32_shift_linear_loss_le_of_delta_choice
    {gLast delta tFirstStar tLastStar firstLower lastLower eps : ℝ}
    (hgLast_pos : 0 < gLast)
    (heps : 0 ≤ eps)
    (hfirstLower_pos : 0 < firstLower)
    (hlastLower_pos : 0 < lastLower)
    (hfirstLower : firstLower ≤ tFirstStar)
    (hlastLower : lastLower ≤ tLastStar)
    (hdelta :
      delta =
        eps / (gLast * (lastLower⁻¹ + firstLower⁻¹))) :
    gLast * (delta / tLastStar) +
        gLast * (delta / tFirstStar) ≤ eps :=
  binaryEndpointAwareAdjacentRateObjective_shift_linear_loss_le_of_delta_choice
    hgLast_pos heps hfirstLower_pos hlastLower_pos hfirstLower hlastLower
    hdelta

/--
Theorem 3.2 approximation certificate with the source's delta choice: the
algorithm-facing last-rate and grid-rate certificates, together with the
first/last optimal-level lower bounds, imply additive `eps`-optimality.
-/
theorem theorem32_rate_loss_le_of_nested_bisection_certificates
    {m : ℕ}
    (optimal returned sampleRate : Fin (m + 2) → ℝ)
    {rStar gLast tFirstStar tLastStar firstLower lastLower delta eps : ℝ}
    (hgLast_pos : 0 < gLast)
    (heps : 0 ≤ eps)
    (hfirstLower_pos : 0 < firstLower)
    (hlastLower_pos : 0 < lastLower)
    (hfirstLower : firstLower ≤ tFirstStar)
    (hlastLower : lastLower ≤ tLastStar)
    (hdelta :
      delta =
        eps / (gLast * (lastLower⁻¹ + firstLower⁻¹)))
    (hoptimal :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate optimal sampleRate i = rStar)
    (hlast :
      rStar -
          gLast * Real.log ((tLastStar + delta) / tLastStar) ≤
        binaryEndpointAwareAdjacentRate returned sampleRate
          (lastAdjacentIndex : Fin (m + 1)))
    (hgrid :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate returned sampleRate
            (lastAdjacentIndex : Fin (m + 1)) -
            gLast * Real.log ((tFirstStar + delta) / tFirstStar) ≤
          binaryEndpointAwareAdjacentRate returned sampleRate i) :
    binaryEndpointAwareAdjacentRateObjective optimal sampleRate -
        binaryEndpointAwareAdjacentRateObjective returned sampleRate ≤
      eps :=
  binaryEndpointAwareAdjacentRateObjective_loss_le_of_nested_bisection_certificates
    optimal returned sampleRate hgLast_pos heps hfirstLower_pos hlastLower_pos
    hfirstLower hlastLower hdelta hoptimal hlast hgrid

/--
Theorem 3.2 approximation certificate with the Lemma C.6 last-level lower
bound derived from the width-minimality condition. The remaining explicit
lower-bound input is the first-level bound supplied in the source by
Corollary C.3.
-/
theorem theorem32_rate_loss_le_of_nested_bisection_width_minimal
    {m : ℕ} (hm : 0 < m)
    (optimal returned sampleRate : Fin (m + 2) → ℝ)
    {rStar gLast tFirstStar firstLower delta eps : ℝ}
    (hgLast_pos : 0 < gLast)
    (heps : 0 ≤ eps)
    (hoptimal_levels : BinaryEndpointLevelVector optimal)
    (hlast_width :
      ∀ i : Fin (m + 1),
        optimal (adjacentHighIndex (lastAdjacentIndex : Fin (m + 1))) -
            optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) ≤
          optimal (adjacentHighIndex i) - optimal (adjacentLowIndex i))
    (hfirstLower_pos : 0 < firstLower)
    (hfirstLower : firstLower ≤ tFirstStar)
    (hdelta :
      delta =
        eps /
          (gLast *
            ((1 - 1 / ((m + 1 : ℕ) : ℝ))⁻¹ + firstLower⁻¹)))
    (hoptimal :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate optimal sampleRate i = rStar)
    (hlast :
      rStar -
          gLast *
            Real.log
              ((optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) +
                    delta) /
                optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))) ≤
        binaryEndpointAwareAdjacentRate returned sampleRate
          (lastAdjacentIndex : Fin (m + 1)))
    (hgrid :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate returned sampleRate
            (lastAdjacentIndex : Fin (m + 1)) -
            gLast * Real.log ((tFirstStar + delta) / tFirstStar) ≤
          binaryEndpointAwareAdjacentRate returned sampleRate i) :
    binaryEndpointAwareAdjacentRateObjective optimal sampleRate -
        binaryEndpointAwareAdjacentRateObjective returned sampleRate ≤
      eps :=
  binaryEndpointAwareAdjacentRateObjective_loss_le_of_nested_bisection_width_minimal
    hm optimal returned sampleRate hgLast_pos heps hoptimal_levels
    hlast_width hfirstLower_pos hfirstLower hdelta hoptimal hlast hgrid

/--
Theorem 3.2 Algorithm-1 run certificate: once a run supplies the source's
rate certificates, level lower bounds, delta choice, and iteration bounds, it
is additively `eps`-optimal and satisfies the nested-bisection runtime bound.
-/
theorem theorem32_rate_loss_and_runtime_le_of_nested_bisection_run
    {m M L outerSteps innerSteps : ℕ}
    (optimal returned sampleRate : Fin (m + 2) → ℝ)
    {rStar gLast tFirstStar tLastStar firstLower lastLower delta eps : ℝ}
    (hgLast_pos : 0 < gLast)
    (heps : 0 ≤ eps)
    (hfirstLower_pos : 0 < firstLower)
    (hlastLower_pos : 0 < lastLower)
    (hfirstLower : firstLower ≤ tFirstStar)
    (hlastLower : lastLower ≤ tLastStar)
    (hdelta :
      delta =
        eps / (gLast * (lastLower⁻¹ + firstLower⁻¹)))
    (hoptimal :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate optimal sampleRate i = rStar)
    (hlast :
      rStar -
          gLast * Real.log ((tLastStar + delta) / tLastStar) ≤
        binaryEndpointAwareAdjacentRate returned sampleRate
          (lastAdjacentIndex : Fin (m + 1)))
    (hgrid :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate returned sampleRate
            (lastAdjacentIndex : Fin (m + 1)) -
            gLast * Real.log ((tFirstStar + delta) / tFirstStar) ≤
          binaryEndpointAwareAdjacentRate returned sampleRate i)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    binaryEndpointAwareAdjacentRateObjective optimal sampleRate -
        binaryEndpointAwareAdjacentRateObjective returned sampleRate ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        AppliedModelingLib.Optimization.nestedBisectionStepBound M L :=
  binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_nested_bisection_run
    optimal returned sampleRate hgLast_pos heps hfirstLower_pos hlastLower_pos
    hfirstLower hlastLower hdelta hoptimal hlast hgrid houter hinner

/--
Theorem 3.2 Algorithm-1 run certificate with the Lemma C.6 last-level lower
bound derived from the width-minimality condition.
-/
theorem theorem32_rate_loss_and_runtime_le_of_nested_bisection_width_minimal_run
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (optimal returned sampleRate : Fin (m + 2) → ℝ)
    {rStar gLast tFirstStar firstLower delta eps : ℝ}
    (hgLast_pos : 0 < gLast)
    (heps : 0 ≤ eps)
    (hoptimal_levels : BinaryEndpointLevelVector optimal)
    (hlast_width :
      ∀ i : Fin (m + 1),
        optimal (adjacentHighIndex (lastAdjacentIndex : Fin (m + 1))) -
            optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) ≤
          optimal (adjacentHighIndex i) - optimal (adjacentLowIndex i))
    (hfirstLower_pos : 0 < firstLower)
    (hfirstLower : firstLower ≤ tFirstStar)
    (hdelta :
      delta =
        eps /
          (gLast *
            ((1 - 1 / ((m + 1 : ℕ) : ℝ))⁻¹ + firstLower⁻¹)))
    (hoptimal :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate optimal sampleRate i = rStar)
    (hlast :
      rStar -
          gLast *
            Real.log
              ((optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) +
                    delta) /
                optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))) ≤
        binaryEndpointAwareAdjacentRate returned sampleRate
          (lastAdjacentIndex : Fin (m + 1)))
    (hgrid :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate returned sampleRate
            (lastAdjacentIndex : Fin (m + 1)) -
            gLast * Real.log ((tFirstStar + delta) / tFirstStar) ≤
          binaryEndpointAwareAdjacentRate returned sampleRate i)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    binaryEndpointAwareAdjacentRateObjective optimal sampleRate -
        binaryEndpointAwareAdjacentRateObjective returned sampleRate ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        AppliedModelingLib.Optimization.nestedBisectionStepBound M L :=
  binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_nested_bisection_width_minimal_run
    hm optimal returned sampleRate hgLast_pos heps hoptimal_levels
    hlast_width hfirstLower_pos hfirstLower hdelta hoptimal hlast hgrid
    houter hinner

/--
Theorem 3.2 approximation certificate specialized to the source's uniform
sample-rate case. Equalized optimal adjacent rates supply the Lemma C.6
last-level lower bound, leaving only the first-level lower bound from the
source's Corollary C.3-style argument as an explicit input.
-/
theorem theorem32_rate_loss_le_of_nested_bisection_uniform_equalized
    {m : ℕ} (hm : 0 < m)
    (optimal returned : Fin (m + 2) → ℝ)
    {tFirstStar firstLower delta eps : ℝ}
    (heps : 0 ≤ eps)
    (hoptimal_levels : BinaryEndpointLevelVector optimal)
    (heq :
      BinaryEndpointAwareAdjacentRatesEqualize optimal
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hfirstLower_pos : 0 < firstLower)
    (hfirstLower : firstLower ≤ tFirstStar)
    (hdelta :
      delta =
        eps /
          ((1 - 1 / ((m + 1 : ℕ) : ℝ))⁻¹ + firstLower⁻¹))
    (hlast :
      binaryEndpointAwareAdjacentRate optimal
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1)) -
          Real.log
            ((optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) +
                  delta) /
              optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))) ≤
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1)))
    (hgrid :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin (m + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin (m + 1)) -
            Real.log ((tFirstStar + delta) / tFirstStar) ≤
          binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin (m + 2) => (1 : ℝ)) i) :
    binaryEndpointAwareAdjacentRateObjective optimal
        (fun _ : Fin (m + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin (m + 2) => (1 : ℝ)) ≤
      eps :=
  binaryEndpointAwareAdjacentRateObjective_loss_le_of_nested_bisection_uniform_equalized
    hm optimal returned heps hoptimal_levels heq hfirstLower_pos
    hfirstLower hdelta hlast hgrid

/--
Theorem 3.2 Algorithm-1 run certificate in the uniform sample-rate case. The
equalized optimal rates provide the Lemma C.6 last-level lower bound and the
run certificates provide the additive approximation and iteration bounds.
-/
theorem theorem32_rate_loss_and_runtime_le_of_nested_bisection_uniform_equalized_run
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (optimal returned : Fin (m + 2) → ℝ)
    {tFirstStar firstLower delta eps : ℝ}
    (heps : 0 ≤ eps)
    (hoptimal_levels : BinaryEndpointLevelVector optimal)
    (heq :
      BinaryEndpointAwareAdjacentRatesEqualize optimal
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hfirstLower_pos : 0 < firstLower)
    (hfirstLower : firstLower ≤ tFirstStar)
    (hdelta :
      delta =
        eps /
          ((1 - 1 / ((m + 1 : ℕ) : ℝ))⁻¹ + firstLower⁻¹))
    (hlast :
      binaryEndpointAwareAdjacentRate optimal
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1)) -
          Real.log
            ((optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) +
                  delta) /
              optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))) ≤
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1)))
    (hgrid :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin (m + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin (m + 1)) -
            Real.log ((tFirstStar + delta) / tFirstStar) ≤
          binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin (m + 2) => (1 : ℝ)) i)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    binaryEndpointAwareAdjacentRateObjective optimal
        (fun _ : Fin (m + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin (m + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        AppliedModelingLib.Optimization.nestedBisectionStepBound M L :=
  binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_nested_bisection_uniform_equalized_run
    hm optimal returned heps hoptimal_levels heq hfirstLower_pos hfirstLower
    hdelta hlast hgrid houter hinner

/--
Theorem 3.2 approximation certificate in the uniform sample-rate case with
the first-level lower bound derived from a lower bound on the equalized optimal
rate. This is the source role of Lemma C.7/C.8/Corollary C.3, abstracted as a
rate-lower certificate.
-/
theorem theorem32_rate_loss_le_of_nested_bisection_uniform_equalized_rate_lower
    {m : ℕ} (hm : 0 < m)
    (optimal returned : Fin (m + 2) → ℝ)
    {rateLower tFirstStar delta eps : ℝ}
    (heps : 0 ≤ eps)
    (hrateLower_pos : 0 < rateLower)
    (hrateLower_le_one : rateLower ≤ 1)
    (hoptimal_levels : BinaryEndpointLevelVector optimal)
    (heq :
      BinaryEndpointAwareAdjacentRatesEqualize optimal
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (htFirstStar :
      tFirstStar =
        optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))))
    (hrateLower_le_last :
      rateLower ≤
        binaryEndpointAwareAdjacentRate optimal
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1)))
    (hdelta :
      delta =
        eps /
          ((1 - 1 / ((m + 1 : ℕ) : ℝ))⁻¹ + (rateLower / 2)⁻¹))
    (hlast :
      binaryEndpointAwareAdjacentRate optimal
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1)) -
          Real.log
            ((optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) +
                  delta) /
              optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))) ≤
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1)))
    (hgrid :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin (m + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin (m + 1)) -
            Real.log ((tFirstStar + delta) / tFirstStar) ≤
          binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin (m + 2) => (1 : ℝ)) i) :
    binaryEndpointAwareAdjacentRateObjective optimal
        (fun _ : Fin (m + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin (m + 2) => (1 : ℝ)) ≤
      eps :=
  binaryEndpointAwareAdjacentRateObjective_loss_le_of_nested_bisection_uniform_equalized_rate_lower
    hm optimal returned heps hrateLower_pos hrateLower_le_one
    hoptimal_levels heq htFirstStar hrateLower_le_last hdelta hlast hgrid

/--
Theorem 3.2 Algorithm-1 run certificate in the uniform sample-rate case with
the first-level lower bound derived from a lower bound on the equalized optimal
rate.
-/
theorem theorem32_rate_loss_and_runtime_le_of_nested_bisection_uniform_equalized_rate_lower_run
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (optimal returned : Fin (m + 2) → ℝ)
    {rateLower tFirstStar delta eps : ℝ}
    (heps : 0 ≤ eps)
    (hrateLower_pos : 0 < rateLower)
    (hrateLower_le_one : rateLower ≤ 1)
    (hoptimal_levels : BinaryEndpointLevelVector optimal)
    (heq :
      BinaryEndpointAwareAdjacentRatesEqualize optimal
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (htFirstStar :
      tFirstStar =
        optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))))
    (hrateLower_le_last :
      rateLower ≤
        binaryEndpointAwareAdjacentRate optimal
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1)))
    (hdelta :
      delta =
        eps /
          ((1 - 1 / ((m + 1 : ℕ) : ℝ))⁻¹ + (rateLower / 2)⁻¹))
    (hlast :
      binaryEndpointAwareAdjacentRate optimal
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1)) -
          Real.log
            ((optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) +
                  delta) /
              optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))) ≤
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1)))
    (hgrid :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin (m + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin (m + 1)) -
            Real.log ((tFirstStar + delta) / tFirstStar) ≤
          binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin (m + 2) => (1 : ℝ)) i)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    binaryEndpointAwareAdjacentRateObjective optimal
        (fun _ : Fin (m + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin (m + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        AppliedModelingLib.Optimization.nestedBisectionStepBound M L :=
  binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_nested_bisection_uniform_equalized_rate_lower_run
    hm optimal returned heps hrateLower_pos hrateLower_le_one
    hoptimal_levels heq htFirstStar hrateLower_le_last hdelta hlast hgrid
    houter hinner

/--
Theorem 3.2 approximation certificate in the uniform sample-rate case with
the first-level lower bound derived from a lower bound on the optimal
equalized objective.
-/
theorem theorem32_rate_loss_le_of_nested_bisection_uniform_equalized_objective_rate_lower
    {m : ℕ} (hm : 0 < m)
    (optimal returned : Fin (m + 2) → ℝ)
    {rateLower tFirstStar delta eps : ℝ}
    (heps : 0 ≤ eps)
    (hrateLower_pos : 0 < rateLower)
    (hrateLower_le_one : rateLower ≤ 1)
    (hoptimal_levels : BinaryEndpointLevelVector optimal)
    (heq :
      BinaryEndpointAwareAdjacentRatesEqualize optimal
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (htFirstStar :
      tFirstStar =
        optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))))
    (hrateLower_le_objective :
      rateLower ≤
        binaryEndpointAwareAdjacentRateObjective optimal
          (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hdelta :
      delta =
        eps /
          ((1 - 1 / ((m + 1 : ℕ) : ℝ))⁻¹ + (rateLower / 2)⁻¹))
    (hlast :
      binaryEndpointAwareAdjacentRate optimal
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1)) -
          Real.log
            ((optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) +
                  delta) /
              optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))) ≤
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1)))
    (hgrid :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin (m + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin (m + 1)) -
            Real.log ((tFirstStar + delta) / tFirstStar) ≤
          binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin (m + 2) => (1 : ℝ)) i) :
    binaryEndpointAwareAdjacentRateObjective optimal
        (fun _ : Fin (m + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin (m + 2) => (1 : ℝ)) ≤
      eps :=
  binaryEndpointAwareAdjacentRateObjective_loss_le_of_nested_bisection_uniform_equalized_objective_rate_lower
    hm optimal returned heps hrateLower_pos hrateLower_le_one
    hoptimal_levels heq htFirstStar hrateLower_le_objective hdelta hlast
    hgrid

/--
Theorem 3.2 Algorithm-1 run certificate in the uniform sample-rate case with
the first-level lower bound derived from a lower bound on the optimal
equalized objective.
-/
theorem theorem32_rate_loss_and_runtime_le_of_nested_bisection_uniform_equalized_objective_rate_lower_run
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (optimal returned : Fin (m + 2) → ℝ)
    {rateLower tFirstStar delta eps : ℝ}
    (heps : 0 ≤ eps)
    (hrateLower_pos : 0 < rateLower)
    (hrateLower_le_one : rateLower ≤ 1)
    (hoptimal_levels : BinaryEndpointLevelVector optimal)
    (heq :
      BinaryEndpointAwareAdjacentRatesEqualize optimal
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (htFirstStar :
      tFirstStar =
        optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))))
    (hrateLower_le_objective :
      rateLower ≤
        binaryEndpointAwareAdjacentRateObjective optimal
          (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hdelta :
      delta =
        eps /
          ((1 - 1 / ((m + 1 : ℕ) : ℝ))⁻¹ + (rateLower / 2)⁻¹))
    (hlast :
      binaryEndpointAwareAdjacentRate optimal
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1)) -
          Real.log
            ((optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) +
                  delta) /
              optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))) ≤
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1)))
    (hgrid :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin (m + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin (m + 1)) -
            Real.log ((tFirstStar + delta) / tFirstStar) ≤
          binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin (m + 2) => (1 : ℝ)) i)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    binaryEndpointAwareAdjacentRateObjective optimal
        (fun _ : Fin (m + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin (m + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        AppliedModelingLib.Optimization.nestedBisectionStepBound M L :=
  binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_nested_bisection_uniform_equalized_objective_rate_lower_run
    hm optimal returned heps hrateLower_pos hrateLower_le_one
    hoptimal_levels heq htFirstStar hrateLower_le_objective hdelta hlast
    hgrid houter hinner

/--
Theorem 3.2 approximation certificate for the explicit Lemma C.5 doubled
uniform chain, using the Lemma C.7 objective lower bound derived from the old
equalized chain.
-/
theorem theorem32_rate_loss_le_of_nested_bisection_uniform_doubled_closed
    {m : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    {tFirstStar delta eps : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (htFirstStar :
      tFirstStar =
        lemmaC5_uniform_doubled_endpoint_levels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hdelta :
      delta =
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹))
    (hlast :
      binaryEndpointAwareAdjacentRate
          (lemmaC5_uniform_doubled_endpoint_levels oldLevels)
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) -
          Real.log
            ((lemmaC5_uniform_doubled_endpoint_levels oldLevels
                  (adjacentLowIndex
                    (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) +
                delta) /
              lemmaC5_uniform_doubled_endpoint_levels oldLevels
                (adjacentLowIndex
                  (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))) ≤
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
    (hgrid :
      ∀ i : Fin ((2 * m + 1) + 1),
        binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) -
            Real.log ((tFirstStar + delta) / tFirstStar) ≤
          binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) i) :
    binaryEndpointAwareAdjacentRateObjective
        (lemmaC5_uniform_doubled_endpoint_levels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤
      eps :=
  binaryEndpointAwareAdjacentRateObjective_loss_le_of_nested_bisection_uniform_doubled_closed
    hm oldLevels returned heps holdLevels holdEq
    (BinaryEndpointLevelVector_uniform_equalized_one_fifth_objective_le_one
      hm holdLevels holdEq)
    htFirstStar hdelta hlast hgrid

/--
Theorem 3.2 Algorithm-1 run certificate for the explicit Lemma C.5 doubled
uniform chain, including the nested-bisection operation bound.
-/
theorem theorem32_rate_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    {tFirstStar delta eps : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (htFirstStar :
      tFirstStar =
        lemmaC5_uniform_doubled_endpoint_levels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hdelta :
      delta =
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹))
    (hlast :
      binaryEndpointAwareAdjacentRate
          (lemmaC5_uniform_doubled_endpoint_levels oldLevels)
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) -
          Real.log
            ((lemmaC5_uniform_doubled_endpoint_levels oldLevels
                  (adjacentLowIndex
                    (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) +
                delta) /
              lemmaC5_uniform_doubled_endpoint_levels oldLevels
                (adjacentLowIndex
                  (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))) ≤
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
    (hgrid :
      ∀ i : Fin ((2 * m + 1) + 1),
        binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) -
            Real.log ((tFirstStar + delta) / tFirstStar) ≤
          binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) i)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    binaryEndpointAwareAdjacentRateObjective
        (lemmaC5_uniform_doubled_endpoint_levels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        AppliedModelingLib.Optimization.nestedBisectionStepBound M L :=
  binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run
    hm oldLevels returned heps holdLevels holdEq
    (BinaryEndpointLevelVector_uniform_equalized_one_fifth_objective_le_one
      hm holdLevels holdEq)
    htFirstStar hdelta hlast hgrid houter hinner

/--
Theorem 3.2 Algorithm-1 run certificate with the source's explicit grid-width
choice substituted directly.  The remaining hypotheses are the substantive
NestedBisection rate certificates and loop-count bounds.
-/
theorem theorem32_rate_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run_explicit_delta
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    {eps : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hlast :
      let delta : ℝ :=
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
      binaryEndpointAwareAdjacentRate
          (lemmaC5_uniform_doubled_endpoint_levels oldLevels)
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) -
          Real.log
            ((lemmaC5_uniform_doubled_endpoint_levels oldLevels
                  (adjacentLowIndex
                    (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) +
                delta) /
              lemmaC5_uniform_doubled_endpoint_levels oldLevels
                (adjacentLowIndex
                  (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))) ≤
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
    (hgrid :
      let tFirstStar : ℝ :=
        lemmaC5_uniform_doubled_endpoint_levels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let delta : ℝ :=
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
      ∀ i : Fin ((2 * m + 1) + 1),
        binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) -
            Real.log ((tFirstStar + delta) / tFirstStar) ≤
          binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) i)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    binaryEndpointAwareAdjacentRateObjective
        (lemmaC5_uniform_doubled_endpoint_levels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        AppliedModelingLib.Optimization.nestedBisectionStepBound M L := by
  simpa [lemmaC5_uniform_doubled_endpoint_levels] using
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run_explicit_delta_auto_lower
      hm oldLevels returned heps holdLevels holdEq
      hlast hgrid houter hinner

/--
Theorem 3.2 with the outer bisection invariant exposed directly: a
`RealBisectionBracket` for the final low endpoint implies the source's
last-rate certificate, so only the inner-grid rate certificate and loop-count
bounds remain as run obligations.
-/
theorem theorem32_rate_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run_outer_bracket
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    {eps lastBracketLower : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hlastBracket :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        lemmaC5_uniform_doubled_endpoint_levels oldLevels
      let delta : ℝ :=
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
      AppliedModelingLib.Optimization.RealBisectionBracket
        (optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
        lastBracketLower
        (returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
        delta)
    (hgrid :
      let tFirstStar : ℝ :=
        lemmaC5_uniform_doubled_endpoint_levels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let delta : ℝ :=
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
      ∀ i : Fin ((2 * m + 1) + 1),
        binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) -
            Real.log ((tFirstStar + delta) / tFirstStar) ≤
          binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) i)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    binaryEndpointAwareAdjacentRateObjective
        (lemmaC5_uniform_doubled_endpoint_levels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        AppliedModelingLib.Optimization.nestedBisectionStepBound M L := by
  let run :=
    theorem32_run_certificate_of_last_bisection_bracket
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels returned holdLevels
      (by simpa [lemmaC5_uniform_doubled_endpoint_levels] using hlastBracket)
      (by simpa [lemmaC5_uniform_doubled_endpoint_levels] using hgrid)
      houter hinner
  simpa [lemmaC5_uniform_doubled_endpoint_levels] using
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_run_certificate
      (m := m) (M := M) (L := L)
      hm oldLevels returned heps holdLevels holdEq run

/--
Theorem 3.2 source-shaped Algorithm-1 certificate with exact inner roots:
the canonical threshold outer bisection and the `BisectNextLevel` low-endpoint
bisections imply the finite additive-rate loss and stated nested-bisection
step bound.  The inner assumptions are the source loop invariants: each root
has the target final adjacent rate and is bracketed by the inner bisection
interval.
-/
theorem theorem32_rate_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run_exact_low_bisection
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    {eps levelUpper0 : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hreturnedLevels : BinaryEndpointLevelVector returned)
    (hlevelUpper0 :
      lemmaC5_uniform_doubled_endpoint_levels oldLevels
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤ levelUpper0)
    (hlevelWidth :
      levelUpper0 -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
              (((1 / 5 : ℝ) *
                  binaryEndpointAwareAdjacentRateObjective oldLevels
                    (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (AppliedModelingLib.Optimization.realBisectionRun
          (AppliedModelingLib.Optimization.realBisectionAboveTarget
            (lemmaC5_uniform_doubled_endpoint_levels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          levelUpper0).2 =
        returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (root : Fin ((2 * m + 1) + 1) → ℝ)
    (hroot0 :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        0 < root i)
    (htFirst_le_root :
      let tFirst : ℝ :=
        lemmaC5_uniform_doubled_endpoint_levels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        tFirst ≤ root i)
    (hroot_le_high :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        root i ≤ returned (adjacentHighIndex i))
    (hroot_rate :
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ)
            (returned (adjacentHighIndex i)) (root i) = target)
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
              (((1 / 5 : ℝ) *
                  binaryEndpointAwareAdjacentRateObjective oldLevels
                    (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ innerSteps)
    (hreturnedLow :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (AppliedModelingLib.Optimization.realBisectionRun
          (AppliedModelingLib.Optimization.realBisectionAboveTarget (root i))
          innerSteps 0 (returned (adjacentHighIndex i))).2 =
          returned (adjacentLowIndex i))
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    binaryEndpointAwareAdjacentRateObjective
        (lemmaC5_uniform_doubled_endpoint_levels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        AppliedModelingLib.Optimization.nestedBisectionStepBound M L := by
  simpa [lemmaC5_uniform_doubled_endpoint_levels] using
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_outer_threshold_run_low_bisection_runs_from_source_lower_exact_roots_auto_first
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels returned heps holdLevels holdEq hreturnedLevels
      (by simpa [lemmaC5_uniform_doubled_endpoint_levels] using hlevelUpper0)
      hlevelWidth hreturnedLast root hroot0
      (by simpa [lemmaC5_uniform_doubled_endpoint_levels] using htFirst_le_root)
      hroot_le_high
      (by simpa using hroot_rate)
      hinnerWidth hreturnedLow houter hinner

/--
Theorem 3.2 exact-root source certificate with canonical outer upper endpoint
`1`: the outer upper-bracket condition follows from endpoint feasibility, so
the visible outer bisection assumptions are only the source lower-width budget
and the returned outer endpoint.
-/
theorem theorem32_rate_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run_exact_low_bisection_upper_one
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    {eps : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hreturnedLevels : BinaryEndpointLevelVector returned)
    (hlevelWidth :
      1 -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
              (((1 / 5 : ℝ) *
                  binaryEndpointAwareAdjacentRateObjective oldLevels
                    (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (AppliedModelingLib.Optimization.realBisectionRun
          (AppliedModelingLib.Optimization.realBisectionAboveTarget
            (lemmaC5_uniform_doubled_endpoint_levels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          1).2 =
        returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (root : Fin ((2 * m + 1) + 1) → ℝ)
    (hroot0 :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        0 < root i)
    (htFirst_le_root :
      let tFirst : ℝ :=
        lemmaC5_uniform_doubled_endpoint_levels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        tFirst ≤ root i)
    (hroot_le_high :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        root i ≤ returned (adjacentHighIndex i))
    (hroot_rate :
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ)
            (returned (adjacentHighIndex i)) (root i) = target)
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
              (((1 / 5 : ℝ) *
                  binaryEndpointAwareAdjacentRateObjective oldLevels
                    (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ innerSteps)
    (hreturnedLow :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (AppliedModelingLib.Optimization.realBisectionRun
          (AppliedModelingLib.Optimization.realBisectionAboveTarget (root i))
          innerSteps 0 (returned (adjacentHighIndex i))).2 =
          returned (adjacentLowIndex i))
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    binaryEndpointAwareAdjacentRateObjective
        (lemmaC5_uniform_doubled_endpoint_levels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        AppliedModelingLib.Optimization.nestedBisectionStepBound M L := by
  simpa [lemmaC5_uniform_doubled_endpoint_levels] using
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_outer_threshold_run_low_bisection_runs_from_source_lower_exact_roots_upper_one_auto_first
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels returned heps holdLevels holdEq hreturnedLevels
      hlevelWidth hreturnedLast root hroot0
      (by simpa [lemmaC5_uniform_doubled_endpoint_levels] using htFirst_le_root)
      hroot_le_high
      (by simpa using hroot_rate)
      hinnerWidth hreturnedLow houter hinner

/--
Theorem 3.2 feasible-floor source certificate with canonical outer upper
endpoint `1`: this is the source-shaped inner `BisectNextLevel` form, using
the low-endpoint inverse feasibility certificates from the source's inner
loop instead of explicit exact root witnesses.
-/
theorem theorem32_rate_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run_feasible_low_bisection_upper_one
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    {eps : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hreturnedLevels : BinaryEndpointLevelVector returned)
    (hlevelWidth :
      1 -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
              (((1 / 5 : ℝ) *
                  binaryEndpointAwareAdjacentRateObjective oldLevels
                    (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (AppliedModelingLib.Optimization.realBisectionRun
          (AppliedModelingLib.Optimization.realBisectionAboveTarget
            (lemmaC5_uniform_doubled_endpoint_levels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          1).2 =
        returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hfeasible :
      let tFirst : ℝ :=
        lemmaC5_uniform_doubled_endpoint_levels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        WeightedBernoulliLowEndpointTargetFeasible
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target)
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
              (((1 / 5 : ℝ) *
                  binaryEndpointAwareAdjacentRateObjective oldLevels
                    (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ innerSteps)
    (hreturnedLow :
      let tFirst : ℝ :=
        lemmaC5_uniform_doubled_endpoint_levels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (AppliedModelingLib.Optimization.realBisectionRun
          (AppliedModelingLib.Optimization.realBisectionAboveTarget (root i))
          innerSteps 0 (returned (adjacentHighIndex i))).2 =
          returned (adjacentLowIndex i))
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    binaryEndpointAwareAdjacentRateObjective
        (lemmaC5_uniform_doubled_endpoint_levels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        AppliedModelingLib.Optimization.nestedBisectionStepBound M L := by
  simpa [lemmaC5_uniform_doubled_endpoint_levels] using
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_outer_threshold_run_feasible_low_bisection_runs_from_source_lower_upper_one
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels returned heps holdLevels holdEq hreturnedLevels
      hlevelWidth hreturnedLast
      (by simpa [lemmaC5_uniform_doubled_endpoint_levels] using hfeasible)
      hinnerWidth
      (by simpa [lemmaC5_uniform_doubled_endpoint_levels] using hreturnedLow)
      houter hinner

/--
Theorem 3.2 feasible-floor source certificate with the floor/high ordering
derived from the source first-endpoint lower invariant.  This leaves the
inner fixed-floor rate comparison and executable returned-endpoint equations
as the source-loop obligations.
-/
theorem theorem32_rate_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run_feasible_low_bisection_upper_one_of_first_ge
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    {eps : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hreturnedLevels : BinaryEndpointLevelVector returned)
    (hlevelWidth :
      1 -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
              (((1 / 5 : ℝ) *
                  binaryEndpointAwareAdjacentRateObjective oldLevels
                    (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (AppliedModelingLib.Optimization.realBisectionRun
          (AppliedModelingLib.Optimization.realBisectionAboveTarget
            (lemmaC5_uniform_doubled_endpoint_levels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          1).2 =
        returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hfirst_ge :
      lemmaC5_uniform_doubled_endpoint_levels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        returned
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (htarget_lt_floor_rate :
      let tFirst : ℝ :=
        lemmaC5_uniform_doubled_endpoint_levels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        target <
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ)
            (returned (adjacentHighIndex i)) tFirst)
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
              (((1 / 5 : ℝ) *
                  binaryEndpointAwareAdjacentRateObjective oldLevels
                    (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ innerSteps)
    (hreturnedLow :
      let tFirst : ℝ :=
        lemmaC5_uniform_doubled_endpoint_levels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (AppliedModelingLib.Optimization.realBisectionRun
          (AppliedModelingLib.Optimization.realBisectionAboveTarget (root i))
          innerSteps 0 (returned (adjacentHighIndex i))).2 =
          returned (adjacentLowIndex i))
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    binaryEndpointAwareAdjacentRateObjective
        (lemmaC5_uniform_doubled_endpoint_levels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        AppliedModelingLib.Optimization.nestedBisectionStepBound M L := by
  simpa [lemmaC5_uniform_doubled_endpoint_levels] using
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_outer_threshold_run_low_bisection_runs_from_source_lower_inner_floor_rate_upper_one_of_first_ge
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels returned heps holdLevels holdEq hreturnedLevels
      hlevelWidth hreturnedLast
      (by simpa [lemmaC5_uniform_doubled_endpoint_levels] using hfirst_ge)
      (by simpa [lemmaC5_uniform_doubled_endpoint_levels] using htarget_lt_floor_rate)
      hinnerWidth
      (by simpa [lemmaC5_uniform_doubled_endpoint_levels] using hreturnedLow)
      houter hinner

/--
Theorem 3.2 source-shaped Algorithm-1 certificate: the outer final-level
bracket and executable inner low-endpoint bisection runs imply the finite
additive-rate loss and the stated nested-bisection step bound.  The remaining
mathematical inputs are exactly the source invariants identifying the outer
rate-comparison branch, feasible low-endpoint inverse roots, and executable
returned endpoints.
-/
theorem theorem32_rate_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run_feasible_low_bisection
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    {eps levelUpper0 : ℝ}
    (levelAbove : ℝ → Bool)
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hreturnedLevels : BinaryEndpointLevelVector returned)
    (hlevelAbove :
      ∀ x,
        levelAbove x = true →
          lemmaC5_uniform_doubled_endpoint_levels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤ x)
    (hlevelBelow :
      ∀ x,
        levelAbove x = false →
          x ≤
            lemmaC5_uniform_doubled_endpoint_levels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hlevelUpper0 :
      lemmaC5_uniform_doubled_endpoint_levels oldLevels
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤ levelUpper0)
    (hlevelWidth :
      levelUpper0 -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
              (((1 / 5 : ℝ) *
                  binaryEndpointAwareAdjacentRateObjective oldLevels
                    (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (AppliedModelingLib.Optimization.realBisectionRun
          levelAbove outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          levelUpper0).2 =
        returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hfloor_lt_high :
      let tFirst : ℝ :=
        lemmaC5_uniform_doubled_endpoint_levels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        tFirst < returned (adjacentHighIndex i))
    (htarget_lt_floor_rate :
      let tFirst : ℝ :=
        lemmaC5_uniform_doubled_endpoint_levels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        target <
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ)
            (returned (adjacentHighIndex i)) tFirst)
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
              (((1 / 5 : ℝ) *
                  binaryEndpointAwareAdjacentRateObjective oldLevels
                    (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ innerSteps)
    (hreturnedLow :
      let tFirst : ℝ :=
        lemmaC5_uniform_doubled_endpoint_levels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (AppliedModelingLib.Optimization.realBisectionRun
          (AppliedModelingLib.Optimization.realBisectionAboveTarget (root i))
          innerSteps 0 (returned (adjacentHighIndex i))).2 =
          returned (adjacentLowIndex i))
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    binaryEndpointAwareAdjacentRateObjective
        (lemmaC5_uniform_doubled_endpoint_levels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        AppliedModelingLib.Optimization.nestedBisectionStepBound M L := by
  simpa [lemmaC5_uniform_doubled_endpoint_levels] using
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_outer_level_run_low_bisection_runs_from_source_lower_inner_floor_rate
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels returned levelAbove heps holdLevels holdEq
      hreturnedLevels
      (by simpa [lemmaC5_uniform_doubled_endpoint_levels] using hlevelAbove)
      (by simpa [lemmaC5_uniform_doubled_endpoint_levels] using hlevelBelow)
      (by simpa [lemmaC5_uniform_doubled_endpoint_levels] using hlevelUpper0)
      hlevelWidth hreturnedLast
      (by simpa [lemmaC5_uniform_doubled_endpoint_levels] using hfloor_lt_high)
      (by simpa [lemmaC5_uniform_doubled_endpoint_levels] using htarget_lt_floor_rate)
      hinnerWidth
      (by simpa [lemmaC5_uniform_doubled_endpoint_levels] using hreturnedLow)
      houter hinner

/--
Theorem 3.2 source-grid calculated-recursion endpoint: the inner
`BisectNextLevel` runs start from `[0, high - grid]`, matching the
supplement's `r = j_m - delta` convention.
-/
abbrev theorem32_rate_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run_calculated_grid_low_bisection_upper_one :=
  @GJ19OptimalBinaryRatingSystems.binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_of_feasible_grid

/--
Theorem 3.2 source-grid calculated-recursion endpoint with the per-inner-call
width obligations derived from a single global bisection-depth budget.
-/
abbrev theorem32_rate_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run_calculated_grid_low_bisection_upper_one_width :=
  @GJ19OptimalBinaryRatingSystems.binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_of_feasible_grid_width

/--
Theorem 3.2 source-grid calculated-recursion endpoint with low-endpoint
feasibility derived from the source floor-rate inequality and root placement.
-/
abbrev theorem32_rate_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run_calculated_grid_low_bisection_upper_one_floor_rate_width :=
  @GJ19OptimalBinaryRatingSystems.binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_of_floor_rate_grid_width

/--
Theorem 3.2 source-grid calculated-recursion endpoint with weak clipped
low-endpoint support. This exact-hit-compatible form allows equality at the
fixed-floor rate and keeps the source small-grid condition as the root
placement premise.
-/
abbrev theorem32_rate_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run_calculated_grid_low_bisection_upper_one_sub_grid_weak_floor_rate_width :=
  @GJ19OptimalBinaryRatingSystems.binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_weak_floor_rate_grid_width

/--
Theorem 3.2 source-grid calculated-recursion endpoint where the weak
floor-rate comparison is derived from the exact doubled comparison chain. The
remaining visible inner-loop premise is the source small-grid/root-placement
condition.
-/
abbrev theorem32_rate_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run_calculated_grid_low_bisection_upper_one_sub_grid_weak_root_placement_source_grid :=
  @GJ19OptimalBinaryRatingSystems.binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_weak_root_placement_source_grid

/--
Theorem 3.2 source-grid calculated-recursion endpoint with root placement
derived from the source bisection endpoint-rate condition at `high - grid`.
-/
abbrev theorem32_rate_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run_calculated_grid_low_bisection_upper_one_floor_rate_grid_upper_rate_width :=
  @GJ19OptimalBinaryRatingSystems.binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_of_floor_rate_grid_upper_rate_width

/--
Theorem 3.2 source-grid calculated-recursion endpoint with low-endpoint
feasibility, root placement, and target positivity derived from source-shaped
inner-loop facts and the outer bisection return. The inner grid condition is
weakened from `tFirst <= high - grid` to the separate source facts
`tFirst < high`, `0 < high - grid`, and the right-endpoint rate comparison.
-/
abbrev theorem32_rate_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run_calculated_grid_low_bisection_upper_one_floor_high_grid_upper_rate_width :=
  @GJ19OptimalBinaryRatingSystems.binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_of_floor_high_grid_upper_rate_width

/--
Theorem 3.2 source-grid calculated-recursion endpoint with the per-interior
`high - grid` rate comparison derived from the scalar source-grid condition
`lastLow <= 1 - grid`.
-/
abbrev theorem32_rate_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run_calculated_grid_low_bisection_upper_one_floor_high_grid_width :=
  @GJ19OptimalBinaryRatingSystems.binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_of_floor_high_grid_width

/--
Theorem 3.2 source-grid calculated-recursion endpoint with both the
floor/high support invariant and the `high - grid` rate comparison derived
from scalar source-grid conditions.
-/
abbrev theorem32_rate_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run_calculated_grid_low_bisection_upper_one_lastLow_gt_floor_grid_width :=
  @GJ19OptimalBinaryRatingSystems.binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_of_lastLow_gt_floor_grid_width

/--
Theorem 3.2 source-grid calculated-recursion endpoint with the per-interior
grid interval nonemptiness derived from the scalar small-grid condition
`grid < tFirst`.
-/
abbrev theorem32_rate_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run_calculated_grid_low_bisection_upper_one_lastLow_gt_floor_grid_lt_floor_width :=
  @GJ19OptimalBinaryRatingSystems.binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_of_lastLow_gt_floor_grid_lt_floor_width

/--
Theorem 3.2 source-grid calculated-recursion endpoint with `tFirst < lastLow`
derived from the outer bisection return.
-/
abbrev theorem32_rate_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run_calculated_grid_low_bisection_upper_one_outer_return_grid_lt_floor_width :=
  @GJ19OptimalBinaryRatingSystems.binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_of_outer_return_grid_lt_floor_width

/--
Theorem 3.2 source-grid calculated-recursion endpoint with `lastLow < 1`
derived from the scalar grid-gap condition.
-/
abbrev theorem32_rate_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run_calculated_grid_low_bisection_upper_one_outer_return_grid_gap_width :=
  @GJ19OptimalBinaryRatingSystems.binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_of_outer_return_grid_gap_width

/--
Theorem 3.2 source-grid calculated-recursion endpoint with the inner
floor-rate condition recovered from the clipped selector moving above the
common floor.
-/
abbrev theorem32_rate_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run_calculated_grid_low_bisection_upper_one_outer_return_grid_gap_width_floor_lt_root :=
  @GJ19OptimalBinaryRatingSystems.binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_of_outer_return_grid_gap_width_floor_lt_root

/--
Theorem 3.2 source-grid calculated-recursion endpoint with Algorithm 1's
outer upper endpoint `1 - grid`; the inner source-loop obligation is the exact
selector fact that each clipped low endpoint moves above the fixed first floor.
-/
abbrev theorem32_rate_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run_calculated_grid_low_bisection_upper_one_sub_grid_outer_return_grid_lt_floor_width_floor_lt_root :=
  @GJ19OptimalBinaryRatingSystems.binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_outer_return_grid_lt_floor_width_floor_lt_root

/--
Theorem 3.2 source-grid calculated-recursion endpoint with Algorithm 1's
outer upper endpoint `1 - grid`, using the source floor-rate comparison to
derive the internal clipped low-endpoint selector fact.
-/
abbrev theorem32_rate_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run_calculated_grid_low_bisection_upper_one_sub_grid_outer_return_grid_lt_floor_width_floor_rate :=
  @GJ19OptimalBinaryRatingSystems.binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_outer_return_grid_lt_floor_width_floor_rate

/--
Theorem 3.2 source-grid calculated-recursion endpoint with Algorithm 1's
outer upper endpoint `1 - grid`: the inner root-placement and low-endpoint
feasibility facts are derived by backward induction, and the remaining strict
outer-return comparison is derived from the source no-exact-midpoint
bisection convention.
-/
abbrev theorem32_rate_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run_calculated_grid_low_bisection_upper_one_sub_grid_no_exact_outer_return_source_grid :=
  @GJ19OptimalBinaryRatingSystems.binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_no_exact_outer_return_source_grid

/--
Theorem 3.2 source-grid calculated-recursion endpoint where the source upper
bound `t^*_{M-2} < 1 - grid` supplies the internal small-grid premise.
-/
abbrev theorem32_rate_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run_calculated_grid_low_bisection_upper_one_sub_grid_no_exact_outer_return_source_upper_bound :=
  @GJ19OptimalBinaryRatingSystems.binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_no_exact_outer_return_source_upper_bound

/--
Theorem 3.2 source-grid calculated-recursion endpoint at the source iteration
depths, using the source upper-bound assumption to derive the internal
small-grid premise.
-/
abbrev theorem32_rate_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run_calculated_grid_low_bisection_upper_one_sub_grid_no_exact_outer_return_source_upper_bound_fixed_depths :=
  @GJ19OptimalBinaryRatingSystems.binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_no_exact_outer_return_source_upper_bound_fixed_depths

/--
Theorem 3.2 source-grid calculated-recursion endpoint at the source iteration
depths, using source upper-bound and standard post-bisection width hypotheses.
-/
abbrev theorem32_rate_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run_calculated_grid_low_bisection_upper_one_sub_grid_no_exact_outer_return_source_upper_bound_width_div_fixed_depths :=
  @GJ19OptimalBinaryRatingSystems.binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_no_exact_outer_return_source_upper_bound_width_div_fixed_depths

/--
Theorem 3.2 source-grid calculated-recursion endpoint at the source iteration
depths, with the returned outer endpoint defined by the executable bisection
run and with the width hypotheses stated in post-bisection form.
-/
abbrev theorem32_rate_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run_calculated_grid_low_bisection_upper_one_sub_grid_no_exact_outer_return_source_upper_bound_width_div_fixed_depths_auto_lastLow :=
  @GJ19OptimalBinaryRatingSystems.binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_no_exact_outer_return_source_upper_bound_width_div_fixed_depths_auto_lastLow

/--
Theorem 3.2 source-grid calculated-recursion endpoint without a no-exact-hit
outer-loop convention.  At the source iteration depths, either the outer run
hits the refined penultimate optimum exactly, or the usual additive-rate loss
and runtime certificate holds.
-/
abbrev theorem32_exact_outer_hit_or_rate_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run_calculated_grid_low_bisection_upper_one_sub_grid_source_upper_bound_width_div_fixed_depths_auto_lastLow :=
  @GJ19OptimalBinaryRatingSystems.binaryEndpointAwareAdjacentRateObjective_exact_outer_hit_or_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_source_upper_bound_width_div_fixed_depths_auto_lastLow

/--
Theorem 3.2 source-grid calculated-recursion endpoint with a single
source-shaped width budget: either the outer run hits the refined penultimate
optimum exactly, or the additive-rate loss and runtime certificate holds.
-/
abbrev theorem32_exact_outer_hit_or_rate_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run_calculated_grid_low_bisection_upper_one_sub_grid_source_upper_bound_width_budget_fixed_depths_auto_lastLow :=
  @GJ19OptimalBinaryRatingSystems.binaryEndpointAwareAdjacentRateObjective_exact_outer_hit_or_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_source_upper_bound_width_budget_fixed_depths_auto_lastLow

/--
Theorem 3.2 source-grid calculated-recursion endpoint with the bisection
depth stated in the source pre-run form: either the outer run hits the
refined penultimate optimum exactly, or the additive-rate loss and runtime
certificate holds.
-/
abbrev theorem32_exact_outer_hit_or_rate_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run_calculated_grid_low_bisection_upper_one_sub_grid_source_upper_bound_source_depth_fixed_depths_auto_lastLow :=
  @GJ19OptimalBinaryRatingSystems.binaryEndpointAwareAdjacentRateObjective_exact_outer_hit_or_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_source_upper_bound_source_depth_fixed_depths_auto_lastLow

/--
Theorem 3.2 source-grid calculated-recursion endpoint with positive source
tolerance: for every `eps > 0`, some finite bisection depth yields either an
exact outer hit or the additive-rate loss and runtime certificate.
-/
abbrev theorem32_exists_depth_exact_outer_hit_or_rate_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run_calculated_grid_low_bisection_upper_one_sub_grid_source_upper_bound_of_eps_pos :=
  @GJ19OptimalBinaryRatingSystems.binaryEndpointAwareAdjacentRateObjective_exists_depth_exact_outer_hit_or_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_source_upper_bound_of_eps_pos

/--
Theorem 3.2 source-grid calculated-recursion endpoint with positive source
tolerance and the source objective-bound small-grid condition: some finite
bisection depth yields either an exact outer hit or the additive-rate loss and
runtime certificate.
-/
abbrev theorem32_exists_depth_exact_outer_hit_or_rate_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run_calculated_grid_low_bisection_upper_one_sub_grid_objective_grid_of_eps_pos :=
  @GJ19OptimalBinaryRatingSystems.binaryEndpointAwareAdjacentRateObjective_exists_depth_exact_outer_hit_or_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_objective_grid_of_eps_pos

/--
Theorem 3.2 source-grid calculated-recursion endpoint with finite grid and
depth choices: for every positive source tolerance, Lean constructs a positive
small grid and finite bisection depth that yield either an exact outer hit or
the additive-rate loss and runtime certificate.
-/
abbrev theorem32_exists_grid_depth_exact_outer_hit_or_rate_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run_calculated_grid_low_bisection_upper_one_sub_grid_of_eps_pos :=
  @GJ19OptimalBinaryRatingSystems.binaryEndpointAwareAdjacentRateObjective_exists_grid_depth_exact_outer_hit_or_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_eps_pos

/--
Theorem 3.2 source-grid calculated-recursion endpoint with finite grid and
depth choices, using the exact-hit early-return convention: for every positive
source tolerance, Lean constructs a positive small grid and finite bisection
depth that give the additive-rate loss and runtime certificate.
-/
abbrev theorem32_exists_grid_depth_rate_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run_calculated_grid_low_bisection_upper_one_sub_grid_early_exact_return_of_eps_pos :=
  @GJ19OptimalBinaryRatingSystems.binaryEndpointAwareAdjacentRateObjective_exists_grid_depth_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_early_exact_return_of_eps_pos

/--
Theorem 3.2 source-grid calculated-recursion endpoint in finite quadratic
runtime form: for every positive source tolerance, Lean constructs a positive
small grid and finite bisection depth that give the additive-rate loss and
operation count at most `M * (L + 1)^2`.
-/
abbrev theorem32_exists_grid_depth_rate_loss_and_quadratic_runtime_le_of_nested_bisection_uniform_doubled_closed_run_calculated_grid_low_bisection_upper_one_sub_grid_early_exact_return_of_eps_pos :=
  @GJ19OptimalBinaryRatingSystems.binaryEndpointAwareAdjacentRateObjective_exists_grid_depth_loss_and_runtime_quadratic_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_early_exact_return_of_eps_pos

/--
Theorem 3.2 source-grid calculated-recursion endpoint with an explicit
logarithmic depth witness: the constructed bisection depth is bounded by a
`log₂(max(1, budget / delta)) + 2` expression and the operation count is at
most `M * (L + 1)^2`.
-/
abbrev theorem32_exists_grid_log_depth_rate_loss_and_quadratic_runtime_le_of_nested_bisection_uniform_doubled_closed_run_calculated_grid_low_bisection_upper_one_sub_grid_early_exact_return_of_eps_pos :=
  @GJ19OptimalBinaryRatingSystems.binaryEndpointAwareAdjacentRateObjective_exists_grid_log_depth_loss_and_runtime_quadratic_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_early_exact_return_of_eps_pos

/--
Theorem 3.2 source-grid calculated-recursion endpoint in the paper's
logarithmic runtime form: the constructed depth is bounded by the source log
expression and the real-valued operation count is at most
`M * (log₂(...) + 2)^2`.
-/
abbrev theorem32_exists_grid_log_depth_rate_loss_and_runtime_real_log_quadratic_le_of_nested_bisection_uniform_doubled_closed_run_calculated_grid_low_bisection_upper_one_sub_grid_early_exact_return_of_eps_pos :=
  @GJ19OptimalBinaryRatingSystems.binaryEndpointAwareAdjacentRateObjective_exists_grid_log_depth_loss_and_runtime_real_log_quadratic_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_early_exact_return_of_eps_pos

/--
Theorem 3.2 source-shaped `NestedBisection` output for the uniform doubled
chain: outer bisection chooses the penultimate endpoint, inner bisections fill
the remaining levels backward, and an exact outer hit returns the already
optimal doubled chain.
-/
abbrev theorem32_uniform_doubled_nested_bisection_output :=
  GJ19OptimalBinaryRatingSystems.theorem32UniformDoubledNestedBisectionOutput

/--
Theorem 3.2 for the named uniform source-shaped `NestedBisection` output:
for every positive source tolerance, Lean constructs a positive small grid
and finite bisection depth whose returned chain has additive-rate loss at most
the tolerance and satisfies the nested-bisection runtime bound.
-/
abbrev theorem32_exists_grid_depth_rate_loss_and_runtime_le_of_uniform_doubled_nested_bisection_output_of_eps_pos :=
  @GJ19OptimalBinaryRatingSystems.binaryEndpointAwareAdjacentRateObjective_exists_grid_depth_loss_and_runtime_le_of_theorem32_uniform_doubled_nested_bisection_output_of_eps_pos

/--
Theorem 3.2 for the named uniform source-shaped `NestedBisection` output in the
paper's logarithmic runtime form: for every positive source tolerance, the named
run has additive-rate loss at most the tolerance and real operation count at
most `M * (log₂(...) + 2)^2`.
-/
abbrev theorem32_exists_grid_log_depth_rate_loss_and_runtime_real_log_quadratic_le_of_uniform_doubled_nested_bisection_output_of_eps_pos :=
  @GJ19OptimalBinaryRatingSystems.binaryEndpointAwareAdjacentRateObjective_exists_grid_log_depth_loss_and_runtime_real_log_quadratic_le_of_theorem32_uniform_doubled_nested_bisection_output_of_eps_pos

/--
Theorem 3.2 source-grid calculated-recursion endpoint from finite optimality:
for a nontrivial source-optimal uniform endpoint chain and every positive
source tolerance, Lean constructs a positive small grid and finite bisection
depth that give the additive-rate loss and runtime certificate.  The finite
equalized-rate certificate is derived from optimality by Lemma 3.1.
-/
abbrev theorem32_exists_grid_depth_rate_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run_calculated_grid_low_bisection_upper_one_sub_grid_early_exact_return_of_optimal_of_eps_pos :=
  @GJ19OptimalBinaryRatingSystems.binaryEndpointAwareAdjacentRateObjective_exists_grid_depth_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_early_exact_return_of_optimal_of_eps_pos

/--
Theorem 3.2 for a nontrivial source-optimal uniform endpoint chain, stated
directly for the named source-shaped `NestedBisection` output.  Lemma 3.1
derives the equalized-rate certificate from finite optimality.
-/
abbrev theorem32_exists_grid_depth_rate_loss_and_runtime_le_of_uniform_doubled_nested_bisection_output_of_optimal_of_eps_pos :=
  @GJ19OptimalBinaryRatingSystems.binaryEndpointAwareAdjacentRateObjective_exists_grid_depth_loss_and_runtime_le_of_theorem32_uniform_doubled_nested_bisection_output_of_optimal_of_eps_pos

/--
Theorem 3.2 for a nontrivial source-optimal uniform endpoint chain, stated
directly for the named source-shaped `NestedBisection` output in the paper's
logarithmic runtime form.  Lemma 3.1 derives the equalized-rate certificate from
finite optimality.
-/
abbrev theorem32_exists_grid_log_depth_rate_loss_and_runtime_real_log_quadratic_le_of_uniform_doubled_nested_bisection_output_of_optimal_of_eps_pos :=
  @GJ19OptimalBinaryRatingSystems.binaryEndpointAwareAdjacentRateObjective_exists_grid_log_depth_loss_and_runtime_real_log_quadratic_le_of_theorem32_uniform_doubled_nested_bisection_output_of_optimal_of_eps_pos

/--
Theorem 3.2 runtime Landau bridge: exact operation-count bounds of the form
`runtime ≤ M * runtimeLog^2` imply the paper-style `O(M * runtimeLog^2)`
statement for any family of source-shaped nested-bisection runs.
-/
abbrev paper_theorem32_runtime_isBigO_of_eventually_runtime_real_log_quadratic_le :=
  @GJ19OptimalBinaryRatingSystems.theorem32_runtime_isBigO_of_eventually_runtime_real_log_quadratic_le

/--
Theorem 3.2 source-grid calculated-recursion endpoint with Algorithm 1's
outer upper endpoint `1 - grid`: the strict initial outer bracket is derived
from the source small-grid condition `grid < tFirst`, while the strict
outer-return comparison uses the no-exact-midpoint bisection convention.
-/
abbrev theorem32_rate_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run_calculated_grid_low_bisection_upper_one_sub_grid_no_exact_outer_return_small_grid :=
  @GJ19OptimalBinaryRatingSystems.binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_no_exact_outer_return_small_grid

/--
Theorem 3.2 source-grid calculated-recursion endpoint at the source iteration
depths: the outer bisection uses `L + 1` steps and each inner bisection uses
`L` steps, so the runtime bound is discharged internally.
-/
abbrev theorem32_rate_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run_calculated_grid_low_bisection_upper_one_sub_grid_no_exact_outer_return_small_grid_fixed_depths :=
  @GJ19OptimalBinaryRatingSystems.binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_no_exact_outer_return_small_grid_fixed_depths

/--
Theorem 3.2 source-grid calculated-recursion endpoint at the source iteration
depths, with the small-grid condition stated through the C.5/C.7/C.8
objective-rate lower bound instead of the internal first refined endpoint.
-/
abbrev theorem32_rate_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run_calculated_grid_low_bisection_upper_one_sub_grid_no_exact_outer_return_objective_grid_fixed_depths :=
  @GJ19OptimalBinaryRatingSystems.binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_no_exact_outer_return_objective_grid_fixed_depths

/--
Theorem 3.2 source-grid calculated-recursion endpoint at the source iteration
depths, with the C.7 lower-bound side condition also discharged from the
uniform equalized old chain.
-/
abbrev theorem32_rate_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run_calculated_grid_low_bisection_upper_one_sub_grid_no_exact_outer_return_objective_grid_auto_lower_fixed_depths :=
  @GJ19OptimalBinaryRatingSystems.binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_no_exact_outer_return_objective_grid_auto_lower_fixed_depths

/--
Theorem 3.2 source outer-bisection convention: when Algorithm 1 initializes
the outer upper endpoint at `1 - grid`, the returned penultimate level remains
at most `1 - grid`.
-/
abbrev theorem32_source_outer_return_lastLow_le_one_sub_grid :=
  @GJ19OptimalBinaryRatingSystems.theorem32_calculated_grid_lastLow_le_one_sub_grid_of_source_outer_return

/--
Theorem 3.2 source outer-bisection convention: the source-shaped outer
bisection return remains positive when `1 - grid` brackets the refined
penultimate optimum.
-/
abbrev theorem32_source_outer_return_lastLow_pos :=
  @GJ19OptimalBinaryRatingSystems.theorem32_calculated_grid_lastLow_pos_of_source_outer_return

/--
Theorem 3.2 source outer-bisection convention: the source-shaped outer
bisection return remains above the first refined endpoint.
-/
abbrev theorem32_source_outer_return_tFirst_lt_lastLow :=
  @GJ19OptimalBinaryRatingSystems.theorem32_calculated_grid_tFirst_lt_lastLow_of_source_outer_return

/--
Finite adjacent binary level-chain upper-bound theorem using the weighted
geometric common threshold and the closed adjacent Bernoulli rates.
-/
theorem finite_binary_adjacent_uniform_objective_error_upper_bound_from_weighted_common_threshold
    {m : ℕ}
    (successProb : Fin (m + 2) → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_pos : ∀ θ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ, successProb θ < 1)
    (sampleRate : Fin (m + 2) → ℝ)
    (hpositive_hi :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hpositive_lo :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (hG :
      ∀ i : Fin (m + 1),
        sampleRate (adjacentHighIndex i) +
            sampleRate (adjacentLowIndex i) ≠ 0)
    (ha_le_hi :
      ∀ i : Fin (m + 1),
        weightedBernoulliCommonThreshold
            (sampleRate (adjacentHighIndex i))
            (sampleRate (adjacentLowIndex i))
            (successProb (adjacentHighIndex i))
            (successProb (adjacentLowIndex i)) ≤
          successProb (adjacentHighIndex i))
    {targetRate : ℝ}
    (hrate :
      ∀ i : Fin (m + 1),
        targetRate <
          weightedBernoulliClosedThresholdRate
            (sampleRate (adjacentHighIndex i))
            (sampleRate (adjacentLowIndex i))
            (successProb (adjacentHighIndex i))
            (successProb (adjacentLowIndex i))) :
    HasExpUpperBoundWithConst
      (fun k : ℕ =>
        1 -
          finiteUniformFloorPkObjective
            (binaryRatingModel successProb hprob0 hprob1) sampleRate
            (fun i : Fin (m + 1) => adjacentHighIndex i)
            (fun i : Fin (m + 1) => adjacentLowIndex i) k)
      targetRate :=
  finiteBinaryAdjacentUniformObjective_oneSub_hasExpUpperBound_of_weighted_common_threshold
    successProb hprob0 hprob1 hprob_pos hprob_lt_one sampleRate
    hpositive_hi hpositive_lo hG ha_le_hi hrate

/--
Finite adjacent binary level-chain upper-bound theorem from ordered adjacent
success probabilities and the closed adjacent Bernoulli rates.
-/
theorem finite_binary_adjacent_uniform_objective_error_upper_bound_from_ordered_weighted_common_threshold
    {m : ℕ}
    (successProb : Fin (m + 2) → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_pos : ∀ θ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ, successProb θ < 1)
    (sampleRate : Fin (m + 2) → ℝ)
    (hpositive_hi :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hpositive_lo :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (hordered :
      ∀ i : Fin (m + 1),
        successProb (adjacentLowIndex i) ≤ successProb (adjacentHighIndex i))
    {targetRate : ℝ}
    (hrate :
      ∀ i : Fin (m + 1),
        targetRate <
          weightedBernoulliClosedThresholdRate
            (sampleRate (adjacentHighIndex i))
            (sampleRate (adjacentLowIndex i))
            (successProb (adjacentHighIndex i))
            (successProb (adjacentLowIndex i))) :
    HasExpUpperBoundWithConst
      (fun k : ℕ =>
        1 -
          finiteUniformFloorPkObjective
            (binaryRatingModel successProb hprob0 hprob1) sampleRate
            (fun i : Fin (m + 1) => adjacentHighIndex i)
            (fun i : Fin (m + 1) => adjacentLowIndex i) k)
      targetRate :=
  finiteBinaryAdjacentUniformObjective_oneSub_hasExpUpperBound_of_ordered_weighted_common_threshold
    successProb hprob0 hprob1 hprob_pos hprob_lt_one sampleRate
    hpositive_hi hpositive_lo hordered hrate

/--
Finite adjacent binary level-chain exact-rate theorem using the weighted
geometric common threshold and a chosen minimum adjacent closed rate.
-/
theorem finite_binary_adjacent_uniform_objective_exact_rate_from_weighted_common_threshold_min
    {m : ℕ}
    (successProb : Fin (m + 2) → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_pos : ∀ θ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ, successProb θ < 1)
    (sampleRate : Fin (m + 2) → ℝ)
    (hpositive_hi :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hpositive_lo :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (hG :
      ∀ i : Fin (m + 1),
        sampleRate (adjacentHighIndex i) +
            sampleRate (adjacentLowIndex i) ≠ 0)
    (ha_le_hi :
      ∀ i : Fin (m + 1),
        weightedBernoulliCommonThreshold
            (sampleRate (adjacentHighIndex i))
            (sampleRate (adjacentLowIndex i))
            (successProb (adjacentHighIndex i))
            (successProb (adjacentLowIndex i)) ≤
          successProb (adjacentHighIndex i))
    (iMin : Fin (m + 1))
    (hrate_ge :
      ∀ i : Fin (m + 1),
        weightedBernoulliClosedThresholdRate
            (sampleRate (adjacentHighIndex iMin))
            (sampleRate (adjacentLowIndex iMin))
            (successProb (adjacentHighIndex iMin))
            (successProb (adjacentLowIndex iMin)) ≤
          weightedBernoulliClosedThresholdRate
            (sampleRate (adjacentHighIndex i))
            (sampleRate (adjacentLowIndex i))
            (successProb (adjacentHighIndex i))
            (successProb (adjacentLowIndex i))) :
    HasExponentialRate
      (fun k : ℕ =>
        1 -
          finiteUniformFloorPkObjective
            (binaryRatingModel successProb hprob0 hprob1) sampleRate
            (fun i : Fin (m + 1) => adjacentHighIndex i)
            (fun i : Fin (m + 1) => adjacentLowIndex i) k)
      (weightedBernoulliClosedThresholdRate
        (sampleRate (adjacentHighIndex iMin))
        (sampleRate (adjacentLowIndex iMin))
        (successProb (adjacentHighIndex iMin))
        (successProb (adjacentLowIndex iMin))) :=
  finiteBinaryAdjacentUniformObjective_oneSub_hasExponentialRate_of_weighted_common_threshold_min
    successProb hprob0 hprob1 hprob_pos hprob_lt_one sampleRate
    hpositive_hi hpositive_lo hG ha_le_hi iMin hrate_ge

/--
Finite adjacent binary level-chain exact-rate theorem from ordered adjacent
success probabilities and a chosen minimum adjacent closed rate.
-/
theorem finite_binary_adjacent_uniform_objective_exact_rate_from_ordered_weighted_common_threshold_min
    {m : ℕ}
    (successProb : Fin (m + 2) → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_pos : ∀ θ, 0 < successProb θ)
    (hprob_lt_one : ∀ θ, successProb θ < 1)
    (sampleRate : Fin (m + 2) → ℝ)
    (hpositive_hi :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentHighIndex i))
    (hpositive_lo :
      ∀ i : Fin (m + 1), 0 < sampleRate (adjacentLowIndex i))
    (hordered :
      ∀ i : Fin (m + 1),
        successProb (adjacentLowIndex i) ≤ successProb (adjacentHighIndex i))
    (iMin : Fin (m + 1))
    (hrate_ge :
      ∀ i : Fin (m + 1),
        weightedBernoulliClosedThresholdRate
            (sampleRate (adjacentHighIndex iMin))
            (sampleRate (adjacentLowIndex iMin))
            (successProb (adjacentHighIndex iMin))
            (successProb (adjacentLowIndex iMin)) ≤
          weightedBernoulliClosedThresholdRate
            (sampleRate (adjacentHighIndex i))
            (sampleRate (adjacentLowIndex i))
            (successProb (adjacentHighIndex i))
            (successProb (adjacentLowIndex i))) :
    HasExponentialRate
      (fun k : ℕ =>
        1 -
          finiteUniformFloorPkObjective
            (binaryRatingModel successProb hprob0 hprob1) sampleRate
            (fun i : Fin (m + 1) => adjacentHighIndex i)
            (fun i : Fin (m + 1) => adjacentLowIndex i) k)
      (weightedBernoulliClosedThresholdRate
        (sampleRate (adjacentHighIndex iMin))
        (sampleRate (adjacentLowIndex iMin))
        (successProb (adjacentHighIndex iMin))
        (successProb (adjacentLowIndex iMin))) :=
  finiteBinaryAdjacentUniformObjective_oneSub_hasExponentialRate_of_ordered_weighted_common_threshold_min
    successProb hprob0 hprob1 hprob_pos hprob_lt_one sampleRate
    hpositive_hi hpositive_lo hordered iMin hrate_ge

/--
Definition C.1 source-facing Kendall/Spearman objective formulas: the Kendall
constant-weight and Spearman linear-weight population objectives reduce to the
finite interval-gap objectives used in Lemmas C.11 and C.12.
-/
theorem definitionC1_kendall_spearman_population_objectives
    (M : ℕ) (s : ℕ → ℝ) :
    kendallConstantWeightIntervalObjective M s =
        (1 - ∑ i : Fin M, (s (i.1 + 1) - s i.1) ^ 2) / 2 ∧
      spearmanLinearWeightIntervalObjective M s =
        (1 - ∑ i : Fin M, (s (i.1 + 1) - s i.1) ^ 3) / 6 := by
  constructor <;> rfl

/--
Lemma C.10 Spearman source-integral reduction: for a partition of `[0,1]`,
the ordered interval-pair linear-distance objective equals the cubic gap
objective used in Lemma C.12.

Source status: exact finite source reduction for Lemma C.10.
-/
theorem paper_lemmaC10_spearman_linear_weight_ordered_pair_interval_objective_eq_gap_objective
    (M : ℕ) (s : ℕ → ℝ) (h0 : s 0 = 0) (hM : s M = 1) :
    spearmanLinearWeightOrderedPairIntervalObjective M s =
      spearmanLinearWeightIntervalObjective M s :=
  GJ19OptimalBinaryRatingSystems.lemmaC10_spearman_linear_weight_ordered_pair_interval_objective_eq_gap_objective
    M s h0 hM

/--
Lemma C.11 finite constant-weight Kendall objective: among interval partitions
with endpoints `0` and `1`, the equispaced partition maximizes the equivalent
gap objective `(1 - ∑ gap_i^2) / 2`.
-/
theorem paper_lemmaC11_kendall_constant_weight_interval_objective_le_equispaced
    {M : ℕ} [Nonempty (Fin M)]
    (s : ℕ → ℝ) (h0 : s 0 = 0) (hM : s M = 1) :
    kendallConstantWeightIntervalObjective M s ≤
      (1 - (M : ℝ)⁻¹) / 2 :=
  GJ19OptimalBinaryRatingSystems.lemmaC11_kendall_constant_weight_interval_objective_le_equispaced
    s h0 hM

/--
Lemma C.11 source-sum form: the ordered constant-weight interval-pair sum in
equation (27) is at most the equispaced partition value.

Source status: exact finite source-sum inequality for Lemma C.11.
-/
theorem paper_lemmaC11_kendall_constant_weight_ordered_pair_interval_objective_le_equispaced
    {M : ℕ} [Nonempty (Fin M)]
    (s : ℕ → ℝ) (h0 : s 0 = 0) (hM : s M = 1) :
    (∑ i : Fin M, ∑ j : Fin M,
        if i < j then
          (s (i.1 + 1) - s i.1) * (s (j.1 + 1) - s j.1)
        else 0) ≤
      (1 - (M : ℝ)⁻¹) / 2 :=
  GJ19OptimalBinaryRatingSystems.lemmaC11_kendall_constant_weight_ordered_pair_interval_objective_le_equispaced
    s h0 hM

/--
Lemma C.11 attainment: the equispaced cutpoints attain the Kendall
constant-weight objective value.
-/
theorem paper_lemmaC11_kendall_constant_weight_interval_objective_equispaced_eq
    {M : ℕ} (hM : 0 < M) :
    kendallConstantWeightIntervalObjective M (equispacedIntervalCutpoint M) =
      (1 - (M : ℝ)⁻¹) / 2 :=
  GJ19OptimalBinaryRatingSystems.lemmaC11_kendall_constant_weight_interval_objective_equispaced_eq
    hM

/--
Lemma C.11 optimizer form: the equispaced cutpoints maximize the
constant-weight Kendall ordered-pair interval objective from equation (27).

Source status: exact finite source optimizer certificate for Lemma C.11.
-/
theorem paper_lemmaC11_kendall_constant_weight_ordered_pair_interval_objective_equispaced_isMaximizerOn
    {M : ℕ} [Nonempty (Fin M)] (hM : 0 < M) :
    AppliedModelingLib.Optimization.IsMaximizerOn
      (intervalCutpointsEndpointFeasible M)
      (fun s : ℕ → ℝ =>
        ∑ i : Fin M, ∑ j : Fin M,
          if i < j then
            (s (i.1 + 1) - s i.1) * (s (j.1 + 1) - s j.1)
          else 0)
      (equispacedIntervalCutpoint M) :=
  GJ19OptimalBinaryRatingSystems.lemmaC11_kendall_constant_weight_ordered_pair_interval_objective_equispaced_isMaximizerOn
    hM

/--
Lemma C.12 finite Spearman linear-weight objective: among monotone interval
partitions with endpoints `0` and `1`, the equispaced partition maximizes the
equivalent gap objective `(1 - ∑ gap_i^3) / 6`.
-/
theorem paper_lemmaC12_spearman_linear_weight_interval_objective_le_equispaced
    {M : ℕ} [Nonempty (Fin M)]
    (s : ℕ → ℝ) (hmono : Monotone s) (h0 : s 0 = 0) (hM : s M = 1) :
    spearmanLinearWeightIntervalObjective M s ≤
      (1 - ((M : ℝ)⁻¹) ^ 2) / 6 :=
  GJ19OptimalBinaryRatingSystems.lemmaC12_spearman_linear_weight_interval_objective_le_equispaced
    s hmono h0 hM

/--
Lemma C.12 source-sum form: the ordered linear-distance interval-pair objective
for Spearman's rho is maximized by equispaced cutpoints.
-/
theorem paper_lemmaC12_spearman_linear_weight_ordered_pair_interval_objective_le_equispaced
    {M : ℕ} [Nonempty (Fin M)]
    (s : ℕ → ℝ) (hmono : Monotone s) (h0 : s 0 = 0) (hM : s M = 1) :
    spearmanLinearWeightOrderedPairIntervalObjective M s ≤
      (1 - ((M : ℝ)⁻¹) ^ 2) / 6 :=
  GJ19OptimalBinaryRatingSystems.lemmaC12_spearman_linear_weight_ordered_pair_interval_objective_le_equispaced
    s hmono h0 hM

/--
Lemma C.12 attainment: the equispaced cutpoints attain the Spearman
linear-weight objective value.
-/
theorem paper_lemmaC12_spearman_linear_weight_interval_objective_equispaced_eq
    {M : ℕ} (hM : 0 < M) :
    spearmanLinearWeightIntervalObjective M (equispacedIntervalCutpoint M) =
      (1 - ((M : ℝ)⁻¹) ^ 2) / 6 :=
  GJ19OptimalBinaryRatingSystems.lemmaC12_spearman_linear_weight_interval_objective_equispaced_eq
    hM

/--
Lemma C.12 optimizer form: the equispaced cutpoints maximize the Spearman
ordered-pair interval objective.

Source status: exact finite source optimizer certificate for Lemma C.12.
-/
theorem paper_lemmaC12_spearman_linear_weight_ordered_pair_interval_objective_equispaced_isMaximizerOn
    {M : ℕ} [Nonempty (Fin M)] (hM : 0 < M) :
    AppliedModelingLib.Optimization.IsMaximizerOn
      (monotoneIntervalCutpointsEndpointFeasible M)
      (spearmanLinearWeightOrderedPairIntervalObjective M)
      (equispacedIntervalCutpoint M) :=
  GJ19OptimalBinaryRatingSystems.lemmaC12_spearman_linear_weight_ordered_pair_interval_objective_equispaced_isMaximizerOn
    hM

/--
Theorem 3.1 Kendall example branch: equispaced cutpoints and the canonical
uniform equalized endpoint levels are lexicographically optimal for the finite
constant-weight Kendall value/rate problem.

Source status: formalized finite Kendall branch of the source example.
-/
theorem paper_theorem31_kendall_constant_weight_equispaced_canonical_uniform_endpoint_lexicographic_optimality
    {M : ℕ} [Nonempty (Fin M)] (hM : 0 < M) :
    AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
      (fun design : (ℕ → ℝ) × (Fin (M + 2) → ℝ) =>
        intervalCutpointsEndpointFeasible M design.1 ∧
          BinaryEndpointLevelVector design.2)
      (fun design : (ℕ → ℝ) × (Fin (M + 2) → ℝ) =>
        kendallConstantWeightOrderedPairIntervalObjective M design.1)
      (fun design : (ℕ → ℝ) × (Fin (M + 2) → ℝ) =>
        binaryEndpointAwareAdjacentRateObjective design.2
          (fun _ : Fin (M + 2) => (1 : ℝ)))
      (equispacedIntervalCutpoint M,
        canonicalUniformEqualizedEndpointLevels M) :=
  GJ19OptimalBinaryRatingSystems.theorem31_kendall_constant_weight_equispaced_canonical_uniform_endpoint_lexicographic_optimality
    hM

/--
Theorem 3.1 Spearman example branch: equispaced cutpoints and the canonical
uniform equalized endpoint levels are lexicographically optimal for the finite
linear-weight Spearman value/rate problem.

Source status: formalized finite Spearman branch of the source example.
-/
theorem paper_theorem31_spearman_linear_weight_equispaced_canonical_uniform_endpoint_lexicographic_optimality
    {M : ℕ} [Nonempty (Fin M)] (hM : 0 < M) :
    AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
      (fun design : (ℕ → ℝ) × (Fin (M + 2) → ℝ) =>
        monotoneIntervalCutpointsEndpointFeasible M design.1 ∧
          BinaryEndpointLevelVector design.2)
      (fun design : (ℕ → ℝ) × (Fin (M + 2) → ℝ) =>
        spearmanLinearWeightOrderedPairIntervalObjective M design.1)
      (fun design : (ℕ → ℝ) × (Fin (M + 2) → ℝ) =>
        binaryEndpointAwareAdjacentRateObjective design.2
          (fun _ : Fin (M + 2) => (1 : ℝ)))
      (equispacedIntervalCutpoint M,
        canonicalUniformEqualizedEndpointLevels M) :=
  GJ19OptimalBinaryRatingSystems.theorem31_spearman_linear_weight_equispaced_canonical_uniform_endpoint_lexicographic_optimality
    hM

/--
Theorem 3.1 Kendall source-normalized branch: in the same indexing convention
as the source-defined `Wbar_k`, equispaced cutpoints and canonical uniform
endpoint levels are lexicographically optimal and carry the corresponding
positive exponential-rate certificate.

Source status: formalized source-normalized Kendall branch of Theorem 3.1.
-/
theorem paper_theorem31_kendall_constant_weight_equispaced_source_endpoint_lexicographic_optimality_and_rate_certificate
    (μ : Measure ℝ) [MeasureTheory.IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) :
    ∃ c : ℝ, 0 < c ∧
      ExponentialRateCertificate
        (theorem31SourceWbar μ
          (equispacedIntervalCutpoint (m + 2))
          (monotone_equispacedIntervalCutpoint (m + 2))
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (canonicalUniformEqualizedEndpointLevels m)
          (canonicalUniformEqualizedEndpointLevels_levelVector m)
          (fun _ : ℝ × ℝ => (1 : ℝ)))
        c ∧
      AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          intervalCutpointsEndpointFeasible (m + 2) design.1 ∧
            BinaryEndpointLevelVector design.2)
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          kendallConstantWeightOrderedPairIntervalObjective (m + 2) design.1)
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          binaryEndpointAwareAdjacentRateObjective design.2
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (equispacedIntervalCutpoint (m + 2),
          canonicalUniformEqualizedEndpointLevels m) :=
  GJ19OptimalBinaryRatingSystems.theorem31_kendall_constant_weight_equispaced_source_endpoint_lexicographic_optimality_and_rate_certificate
    μ hm

/--
Theorem 3.1 Spearman source-normalized branch: in the same indexing convention
as the source-defined `Wbar_k`, equispaced cutpoints and canonical uniform
endpoint levels are lexicographically optimal and carry the corresponding
positive exponential-rate certificate.

Source status: formalized source-normalized Spearman branch of Theorem 3.1.
-/
theorem paper_theorem31_spearman_linear_weight_equispaced_source_endpoint_lexicographic_optimality_and_rate_certificate
    (μ : Measure ℝ) [MeasureTheory.IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    {m : ℕ} (hm : 0 < m) :
    ∃ c : ℝ, 0 < c ∧
      ExponentialRateCertificate
        (theorem31SourceWbar μ
          (equispacedIntervalCutpoint (m + 2))
          (monotone_equispacedIntervalCutpoint (m + 2))
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (canonicalUniformEqualizedEndpointLevels m)
          (canonicalUniformEqualizedEndpointLevels_levelVector m)
          (fun _ : ℝ × ℝ => (1 : ℝ)))
        c ∧
      AppliedModelingLib.Optimization.IsLexicographicMaximizerOn
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          monotoneIntervalCutpointsEndpointFeasible (m + 2) design.1 ∧
            BinaryEndpointLevelVector design.2)
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          spearmanLinearWeightOrderedPairIntervalObjective (m + 2) design.1)
        (fun design : (ℕ → ℝ) × (Fin (m + 2) → ℝ) =>
          binaryEndpointAwareAdjacentRateObjective design.2
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (equispacedIntervalCutpoint (m + 2),
          canonicalUniformEqualizedEndpointLevels m) :=
  GJ19OptimalBinaryRatingSystems.theorem31_spearman_linear_weight_equispaced_source_endpoint_lexicographic_optimality_and_rate_certificate
    μ hm

/--
Theorem 3.1/C.4 equispaced application branch: equispaced source cutpoints,
canonical equalized endpoint levels, constant weight, and uniform sampling
give a positive exponential-rate certificate for the source-defined `Wbar_k`.

Source status: formalized canonical equispaced source-rate branch.
-/
abbrev paper_theorem31SourceWbar_canonical_uniform_endpoint_const_weight_rate_certificate_equispacedIntervalCutpoint
    (μ : Measure ℝ) [MeasureTheory.IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)] {m : ℕ} :=
  GJ19OptimalBinaryRatingSystems.theorem31SourceWbar_canonical_uniform_endpoint_const_weight_rate_certificate_equispacedIntervalCutpoint
    μ (m := m)

/--
Theorem 3.1/C.4 equispaced fixed-value branch: equispaced source cutpoints,
constant weight, and uniform sampling admit endpoint levels with a
source-defined rate certificate and fixed-partition lexicographic optimality.

Source status: formalized canonical equispaced fixed-discretization branch.
-/
abbrev paper_theorem31_sourceDefinedWbar_const_weight_uniform_sampleRate_fixed_value_lexicographic_certificate_equispacedIntervalCutpoint
    (μ : Measure ℝ) [MeasureTheory.IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)] {m : ℕ} :=
  GJ19OptimalBinaryRatingSystems.theorem31_sourceDefinedWbar_const_weight_uniform_sampleRate_fixed_value_lexicographic_certificate_equispacedIntervalCutpoint
    μ (m := m)

/--
Corollary C.4 discretization scaffold: the equispaced interval quantile map
`⌊Mθ⌋ / M` converges uniformly to the identity on `[0,1]`.

Source status: canonical equispaced convergence component of Corollary C.4.
-/
theorem paper_corollaryC4_equispaced_interval_quantile_tendstoUniformlyOn_identity :
    TendstoUniformlyOn
      (fun M : ℕ => fun θ : ℝ => equispacedIntervalQuantile M θ)
      (fun θ : ℝ => θ) atTop (Set.Icc (0 : ℝ) 1) :=
  GJ19OptimalBinaryRatingSystems.corollaryC4_equispaced_interval_quantile_tendstoUniformlyOn_identity

/--
Theorem B.1 Cauchy-completeness bridge: a dyadic subsequence with the source's
uniform anchor/mesh envelope has a uniform limit on `[0,1]`.

Source status: conditional B.1 bridge; the anchor/mesh envelope is the explicit
selector-stability premise used in the supplement proof.
-/
theorem paper_theoremB1_uniform_subsequence_principle_of_anchor_bound
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (mesh : ℕ → ℝ)
    (hmesh : Tendsto mesh atTop (nhds 0))
    (hmesh_nonneg : ∀ M : ℕ, 0 ≤ mesh M)
    (hanchor :
      ∀ C M : ℕ, ∃ K : ℕ, ∀ N : ℕ, K ≤ N →
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
          dist
            (betaSeq (theoremB1SubsequenceIndex C N) θ)
            (betaSeq (theoremB1SubsequenceIndex C M) θ) ≤ mesh M) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq :=
  GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrinciple_of_anchor_bound
    betaSeq quantileSeq mesh hmesh hmesh_nonneg hanchor

/--
Theorem B.1 source-facing Cauchy bridge: an anchor envelope with vanishing
mesh gives dyadic subsequence convergence, independent of a named quantile
limit.
-/
abbrev paper_theoremB1_dyadic_subsequence_uniform_convergence_of_anchor_bound :=
  @GJ19OptimalBinaryRatingSystems.theoremB1DyadicSubsequenceUniformConvergence_of_anchor_bound

/--
Theorem B.1 general-limit Cauchy bridge from an anchor envelope.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_to_of_anchor_bound :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrincipleTo_of_anchor_bound

/--
Theorem B.1 source-facing Cauchy bridge with eventual anchors.
-/
abbrev paper_theoremB1_dyadic_subsequence_uniform_convergence_of_eventually_anchor_bound :=
  @GJ19OptimalBinaryRatingSystems.theoremB1DyadicSubsequenceUniformConvergence_of_eventually_anchor_bound

/--
Theorem B.1 general-limit Cauchy bridge with eventual anchors.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_to_of_eventually_anchor_bound :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrincipleTo_of_eventually_anchor_bound

/--
Theorem B.1 source-facing Cauchy bridge with subsequence-dependent eventual
anchors.  This is the value-level non-equispaced route: each dyadic
subsequence may use its own shrinking mesh.
-/
abbrev paper_theoremB1_dyadic_subsequence_uniform_convergence_of_eventually_anchor_bound_by_subsequence :=
  @GJ19OptimalBinaryRatingSystems.theoremB1DyadicSubsequenceUniformConvergence_of_eventually_anchor_bound_by_subsequence

/--
Theorem B.1 bridge with subsequence-dependent eventual anchors.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_of_eventually_anchor_bound_by_subsequence :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrinciple_of_eventually_anchor_bound_by_subsequence

/--
Theorem B.1 general-limit bridge with subsequence-dependent eventual anchors.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_to_of_eventually_anchor_bound_by_subsequence :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrincipleTo_of_eventually_anchor_bound_by_subsequence

/--
Theorem B.1 source-facing conclusion: every dyadic source subsequence has a
uniform limit on `[0,1]`, stated without choosing a quantile limit.
-/
abbrev paper_theoremB1_dyadic_subsequence_uniform_convergence :=
  @GJ19OptimalBinaryRatingSystems.theoremB1DyadicSubsequenceUniformConvergence

/--
Theorem B.1 general-limit statement: the quantile maps may converge uniformly
to an arbitrary limiting coordinate function.  The equispaced
Kendall/Spearman branch instantiates this limit as the identity.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_to :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrincipleTo

/--
Theorem B.1 identity specialization: the original Lean principle is exactly
the general-limit principle with identity quantile limit.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_iff_to_identity :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrinciple_iff_to_identity

/--
Theorem B.1 bridge: the anchor/mesh envelope only needs to hold eventually in
the anchor index.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_of_eventually_anchor_bound :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrinciple_of_eventually_anchor_bound

/--
Theorem B.1 auxiliary bridge: an arbitrary selector satisfying the source
scaled index window places the old and refined selected levels in one old
two-step bracket.
-/
abbrev paper_theoremB1_scaled_selector_window_bracket :=
  @GJ19OptimalBinaryRatingSystems.uniformDoubledEndpointLevelsIterate_old_refined_mem_same_two_step_interval_of_scaled_index_window

/--
Theorem B.1 auxiliary bridge: the scaled selector-window bracket specialized
to a uniform equalized endpoint-level sequence.
-/
abbrev paper_theoremB1_uniform_equalized_scaled_selector_window_bracket :=
  @GJ19OptimalBinaryRatingSystems.uniformEqualizedLevelSequence_iterated_old_refined_mem_same_two_step_interval_of_scaled_index_window

/--
Theorem B.1 auxiliary bridge: the scaled selector-window bracket gives the
two-adjacent-mesh distance bound used in the Cauchy step.
-/
abbrev paper_theoremB1_uniform_equalized_scaled_selector_window_mesh_bound :=
  @GJ19OptimalBinaryRatingSystems.uniformEqualizedLevelSequence_iterated_beta_dist_le_two_maxWidth_of_scaled_index_window

/--
Theorem B.1 auxiliary bridge: a scaled selector-window invariant along a
repeated C.5 chain gives a uniformly convergent subsequence.
-/
abbrev paper_theoremB1_uniform_equalized_scaled_selector_window_subsequence_limit :=
  @GJ19OptimalBinaryRatingSystems.uniformDoubledEndpointIndexIterate_subsequence_exists_uniform_limit_of_scaled_index_window

/--
Theorem B.1 auxiliary bridge: the scaled selector-window invariant only needs
to hold eventually in the anchor index.
-/
abbrev paper_theoremB1_uniform_equalized_eventually_scaled_selector_window_subsequence_limit :=
  @GJ19OptimalBinaryRatingSystems.uniformDoubledEndpointIndexIterate_subsequence_exists_uniform_limit_of_eventually_scaled_index_window

/--
Theorem B.1 auxiliary bridge: the source-style common floor-coordinate
convention along dyadic refinements implies the eventual scaled selector-window
condition.
-/
abbrev paper_theoremB1_common_floor_coordinate_scaled_selector_window :=
  @GJ19OptimalBinaryRatingSystems.uniformDoubledEndpointIndexIterate_eventually_scaled_index_window_of_common_floor_coordinate

/--
Theorem B.1 positive-dyadic bridge: under uniform equalized endpoint levels,
an eventually scaled selector-window invariant gives a uniform limit along each
positive dyadic source subsequence.
-/
abbrev paper_theoremB1_positive_dyadic_uniform_equalized_eventually_scaled_index_window :=
  @GJ19OptimalBinaryRatingSystems.theoremB1SubsequenceIndex_subsequence_exists_uniform_limit_of_uniform_equalized_eventually_scaled_index_window

/--
Theorem B.1 bridge: the source two-step bracket condition supplies the
anchor/mesh envelope needed by the Cauchy-completeness step.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_of_two_step_bracket :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrinciple_of_two_step_bracket

/--
Theorem B.1 bridge: the source two-step bracket condition only needs to hold
eventually in the anchor index.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_of_eventually_two_step_bracket :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrinciple_of_eventually_two_step_bracket

/--
Theorem B.1 bridge with Corollary C.2 discharged by uniform equalized rates;
the only remaining input is the source two-step bracket condition.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_of_uniform_equalized_two_step_bracket :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_two_step_bracket

/--
Theorem B.1 bridge with Corollary C.2 discharged: the source two-step bracket
condition may hold only eventually in the anchor index.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_of_uniform_equalized_eventually_two_step_bracket :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_eventually_two_step_bracket

/--
Theorem B.1 bridge: any eventually common old bracket of fixed index width is
enough for the Cauchy step, since Corollary C.2 makes the old adjacent mesh
vanish.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_of_eventually_fixed_width_bracket :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrinciple_of_eventually_fixed_width_bracket

/--
Theorem B.1 bridge with Corollary C.2 discharged: a fixed-width source bracket
condition suffices under uniform equalized endpoint levels.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_of_uniform_equalized_eventually_fixed_width_bracket :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_eventually_fixed_width_bracket

/--
Theorem B.1 bridge with Corollary C.2 and equalized rates discharged from
finite uniform optimality; the source two-step bracket condition is the only
remaining input.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_of_uniform_optimal_two_step_bracket :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_two_step_bracket

/--
Theorem B.1 bridge with finite uniform optimality: the source two-step bracket
condition may hold only eventually in the anchor index.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_of_uniform_optimal_eventually_two_step_bracket :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_eventually_two_step_bracket

/--
Theorem B.1 bridge with finite uniform optimality: any eventually common old
bracket of fixed index width is enough because the old adjacent mesh vanishes.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_of_uniform_optimal_eventually_fixed_width_bracket :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_eventually_fixed_width_bracket

/--
Theorem B.1 source-index bridge: uniform equalized endpoint levels plus an
eventual scaled selector-window invariant imply the full B.1 dyadic
subsequence principle.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_of_uniform_equalized_eventually_scaled_index_window :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_eventually_scaled_index_window

/--
Theorem B.1 source-index bridge: the common floor-coordinate convention
supplies the eventual scaled selector-window invariant, hence the full B.1
dyadic subsequence principle under uniform equalized endpoint levels.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_of_uniform_equalized_common_floor_coordinate :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_common_floor_coordinate

/--
Theorem B.1 general-limit source-index bridge: uniform equalized endpoint
levels plus an eventual scaled selector-window invariant directly give dyadic
subsequence convergence for any uniform quantile limit.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_to_of_uniform_equalized_eventually_scaled_index_window :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_equalized_eventually_scaled_index_window

/--
Theorem B.1 general-limit source-index bridge: a fixed-width scaled
selector-window invariant gives dyadic subsequence convergence for any uniform
quantile limit.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_to_of_uniform_equalized_eventually_scaled_block_window :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_equalized_eventually_scaled_block_window

/--
Theorem B.1 general-limit bridge: the source common floor-coordinate
convention supplies dyadic selector tracking without requiring the quantile
limit to be the identity.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_to_of_uniform_equalized_common_floor_coordinate :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_equalized_common_floor_coordinate

/--
Theorem B.1 general-limit bridge: a bounded-error common floor-coordinate
convention supplies dyadic selector tracking without requiring the quantile
limit to be the identity.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_to_of_uniform_equalized_common_floor_coordinate_bounded_error :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_equalized_common_floor_coordinate_bounded_error

/--
Theorem B.1 source-index bridge for optimal endpoint chains: finite optimality
supplies equalized rates, while the source common floor-coordinate invariant
supplies dyadic selector tracking.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_of_uniform_optimal_common_floor_coordinate :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_common_floor_coordinate

/--
Theorem B.1 general-limit bridge for optimal endpoint chains: finite optimality
supplies equalized rates, and the source common floor-coordinate invariant
gives dyadic subsequence convergence for an arbitrary uniform quantile limit.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_to_of_uniform_optimal_common_floor_coordinate :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_optimal_common_floor_coordinate

/--
Theorem B.1 general-limit bridge for optimal endpoint chains under a
non-equispaced variable-width selector-window condition.  The selector window
may grow with the dyadic anchor, provided the window width times the old
endpoint mesh tends to zero.

Source status: formalized conditional on the variable-width selector-window
and mesh-product hypotheses; this is the non-equispaced analogue of the
fixed-width/equispaced selector bridges.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_to_of_uniform_optimal_eventually_scaled_block_window_variable_width :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_optimal_eventually_scaled_block_window_variable_width

/--
Theorem B.1 general-limit bridge for optimal endpoint chains under a
non-equispaced variable-width selector-window condition whose squared width is
negligible relative to the dyadic endpoint count.  The C.2 quantitative
max-gap bound derives the mesh-product condition internally.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_to_of_uniform_optimal_eventually_scaled_block_window_subsqrt :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_optimal_eventually_scaled_block_window_subsqrt

/--
Theorem B.1 general-limit bridge for the paper's quantile-floor selector:
a dyadic-tail variable distance envelope to the limiting source coordinate,
with direct control of the selected block width times the old endpoint mesh,
supplies the non-equispaced selector coherence used by the B.1 Cauchy proof.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_to_of_uniform_optimal_quantile_floor_variable_dist_tracking_mesh_width :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_optimal_quantile_floor_variable_dist_tracking_mesh_width

/--
Theorem B.1 general-limit bridge for the paper's quantile-floor selector:
a dyadic-tail variable distance envelope plus a sublinear selected block width
and linear endpoint-mesh bound imply the direct mesh-product condition needed
for the non-equispaced selector coherence proof.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_to_of_uniform_optimal_quantile_floor_variable_dist_tracking_linear_mesh :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_optimal_quantile_floor_variable_dist_tracking_linear_mesh

/--
Theorem B.1 general-limit bridge for the paper's quantile-floor selector:
a dyadic-tail variable distance envelope plus a sublinear selected block width
suffices; the endpoint mesh-product condition is derived internally from the
C.5 geometric refinement recurrence for uniform optimal endpoint levels.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_to_of_uniform_optimal_quantile_floor_variable_dist_tracking_geometric_mesh :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_optimal_quantile_floor_variable_dist_tracking_geometric_mesh

/--
Theorem B.1 general-limit bridge for the paper's quantile-floor selector:
a dyadic-tail variable distance envelope to the limiting source coordinate,
with sub-square-root block width, supplies the non-equispaced selector
coherence used by the B.1 Cauchy proof.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_to_of_uniform_optimal_quantile_floor_variable_dist_tracking_subsqrt :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_optimal_quantile_floor_variable_dist_tracking_subsqrt

/--
Theorem B.1 named assumption wrapper for the variable dyadic quantile-floor
tracking route.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_to_of_quantile_floor_variable_dist_tracking_subsqrt_assumption :=
  @GJ19OptimalBinaryRatingSystems.theoremB1_uniform_subsequence_principle_to_of_quantile_floor_variable_dist_tracking_subsqrt_assumption

/--
Theorem B.1 named assumption wrapper for the linear-mesh variable dyadic
quantile-floor tracking route.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_to_of_quantile_floor_variable_dist_tracking_linear_mesh_assumption :=
  @GJ19OptimalBinaryRatingSystems.theoremB1_uniform_subsequence_principle_to_of_quantile_floor_variable_dist_tracking_linear_mesh_assumption

/--
Theorem B.1 named assumption wrapper for the geometric-mesh variable dyadic
quantile-floor tracking route.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_to_of_quantile_floor_variable_dist_tracking_geometric_mesh_assumption :=
  @GJ19OptimalBinaryRatingSystems.theoremB1_uniform_subsequence_principle_to_of_quantile_floor_variable_dist_tracking_geometric_mesh_assumption

/--
Theorem B.1 constructor for the linear-mesh tracking assumption from a
sublinear old-grid tail cell-error envelope.
-/
abbrev paper_assumption_theoremB1_quantile_floor_variable_dist_tracking_linear_mesh_of_sublinear_tail_cells :=
  @GJ19OptimalBinaryRatingSystems.assumption_theoremB1_quantile_floor_variable_dist_tracking_linear_mesh_of_sublinear_tail_cells

/--
Theorem B.1 constructor for the geometric-mesh tracking assumption from a
sublinear old-grid tail cell-error envelope.
-/
abbrev paper_assumption_theoremB1_quantile_floor_variable_dist_tracking_geometric_mesh_of_sublinear_tail_cells :=
  @GJ19OptimalBinaryRatingSystems.assumption_theoremB1_quantile_floor_variable_dist_tracking_geometric_mesh_of_sublinear_tail_cells

/--
Theorem B.1 constructor for the geometric-mesh tracking assumption from a
real-valued uniform dyadic tail error schedule.  This is the source-facing
Appendix B uniform-convergence route: the real error is rounded into a
sublinear old-grid cell envelope.
-/
abbrev paper_assumption_theoremB1_quantile_floor_variable_dist_tracking_geometric_mesh_of_real_tail_error :=
  @GJ19OptimalBinaryRatingSystems.assumption_theoremB1_quantile_floor_variable_dist_tracking_geometric_mesh_of_real_tail_error

/--
Theorem B.1 constructor for the geometric-mesh tracking assumption from
uniform convergence of the interval-quantile maps.  This is the closest
paper-facing form of the Appendix B.1 selector-coherence proof.
-/
abbrev paper_assumption_theoremB1_quantile_floor_variable_dist_tracking_geometric_mesh_of_tendstoUniformlyOn :=
  @GJ19OptimalBinaryRatingSystems.assumption_theoremB1_quantile_floor_variable_dist_tracking_geometric_mesh_of_tendstoUniformlyOn

/--
Theorem B.1 closeout route from the paper's quantile-floor source
representation, finite optimality, and uniform convergence of interval
quantile maps.  The selector window is derived from uniform convergence and
C.5, rather than assumed separately.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_to_of_quantile_floor_tendstoUniformlyOn_geometric_mesh :=
  @GJ19OptimalBinaryRatingSystems.theoremB1_uniform_subsequence_principle_to_of_quantile_floor_tendstoUniformlyOn_geometric_mesh

/--
Theorem B.1 general-limit bridge for optimal endpoint chains under a
non-equispaced metric selector-window condition.  The source may choose
selector blocks containing many tiny old cells; the checked premise is that
the actual endpoint span of those old blocks tends to zero.

Source status: formalized conditional on the metric selector-window
hypotheses; this is the cleanest non-equispaced B.1 bridge.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_to_of_uniform_optimal_eventually_scaled_metric_block_window :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_optimal_eventually_scaled_metric_block_window

/--
Theorem B.1 named assumption wrapper for the quantile-floor selector route
using actual metric span.  This is the `sqrt m`-scale alternative to the
sub-square-root max-gap bridge: the selected old block may contain many cells,
provided its endpoint-level span tends to zero.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_to_of_quantile_floor_variable_metric_span_assumption :=
  @GJ19OptimalBinaryRatingSystems.theoremB1_uniform_subsequence_principle_to_of_quantile_floor_variable_metric_span_assumption

/--
Theorem B.1 general-limit bridge for optimal endpoint chains under the
paper's quantile-floor selector and bounded dyadic floor-envelope condition.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_to_of_uniform_optimal_quantile_floor_selector_common_coordinate_bounded_error :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_optimal_quantile_floor_selector_common_coordinate_bounded_error

/--
Theorem B.1 general-limit bridge for optimal endpoint chains under the
paper's quantile-floor selector.  The source's informal selector step is
reduced to a raw anchor/tail quantile-distance estimate at the refined
floor-selector scale.

Source status: formalized conditional on the quantitative selector estimate.
This is the current proof target for deriving the printed B.1 statement from
the uniform convergence of the paper quantile maps plus endpoint-level
equicontinuity.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_to_of_uniform_optimal_quantile_floor_eventual_anchor_dist :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_optimal_quantile_floor_eventual_anchor_dist

/--
Theorem B.1 general-limit bridge for optimal endpoint chains when finite
coarse-cell uniqueness keeps refined and anchor quantile-floor selectors in
the same old cell.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_to_of_uniform_optimal_quantile_floor_finite_coarse_cell :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_optimal_quantile_floor_finite_coarse_cell

/--
Theorem B.1 general-limit bridge for optimal endpoint chains under a
real-valued `O(1/m)` source-coordinate/quantile tracking estimate.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_to_of_uniform_optimal_quantile_floor_global_dist_tracking :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_optimal_quantile_floor_global_dist_tracking

/--
Theorem B.1 general-limit bridge for optimal endpoint chains under a
quantitative `O(1/m)` tracking estimate between the paper quantile maps and
their limiting source coordinate.  The limiting-coordinate range and the
fixed-width bookkeeping are derived internally.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_to_of_uniform_optimal_quantile_floor_limit_dist_tracking :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_optimal_quantile_floor_limit_dist_tracking_clean

/--
Theorem B.1 source convention: an optimal finite endpoint chain is represented
by quantile-floor indices that track a single source coordinate at `O(1/m)`
scale.

Source status: explicit source-model convention; finite optimality is
formalized, while this convention records one strong way to supply selector
coherence for arbitrary optimal `β_M` sequences.  The weaker quantitative
anchor-distance bridge above is the preferred target for closing the printed
B.1 statement.
-/
abbrev paper_theoremB1_optimal_quantile_floor_global_dist_tracking_convention :=
  @GJ19OptimalBinaryRatingSystems.TheoremB1OptimalQuantileFloorGlobalDistTrackingConvention

/--
Theorem B.1 source convention constructor: quantitative `O(1/m)` tracking of
the paper quantile maps to their limiting coordinate supplies the named
global-distance selector convention.
-/
abbrev paper_theoremB1_optimal_quantile_floor_global_dist_tracking_convention_of_limit_dist_tracking :=
  @GJ19OptimalBinaryRatingSystems.theoremB1OptimalQuantileFloorGlobalDistTrackingConvention_of_limit_dist_tracking

/--
Theorem B.1 general-limit bridge under the named optimal quantile-floor
global-distance tracking convention.

Source status: formalized conditional on the explicit selector-coherence
convention; prefer the anchor-distance bridge when working from the source's
uniform quantile-convergence hypothesis.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_to_of_optimal_quantile_floor_global_dist_tracking_convention :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrincipleTo_of_optimal_quantile_floor_global_dist_tracking_convention

/--
Theorem B.1 source-index bridge: a global source-coordinate selector supplies
the common floor-coordinate convention, hence the full B.1 dyadic subsequence
principle under uniform equalized endpoint levels.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_of_uniform_equalized_common_floor_coordinate_map :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_common_floor_coordinate_map

/--
Theorem B.1 named source convention: a selector follows the paper's single
floor coordinate `x_θ` through each dyadic refinement tail.
-/
abbrev paper_theoremB1_source_floor_selector_convention :=
  @GJ19OptimalBinaryRatingSystems.theoremB1SourceFloorSelectorConvention

/--
Theorem B.1 source-index bridge: under uniform equalized endpoint levels, the
named source floor-selector convention gives the full dyadic subsequence
principle.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_of_uniform_equalized_source_floor_selector_convention :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_source_floor_selector_convention

/--
Theorem B.1 source-index bridge for optimal uniform endpoint chains: finite
optimality supplies equalized rates, and a global source-coordinate selector
then gives the full dyadic subsequence principle.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_of_uniform_optimal_common_floor_coordinate_map :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_common_floor_coordinate_map

/--
Theorem B.1 source-index bridge for optimal uniform endpoint chains: finite
optimality supplies equalized rates, and the named source floor-selector
convention gives the full dyadic subsequence principle.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_of_uniform_optimal_source_floor_selector_convention :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_source_floor_selector_convention

/--
Theorem B.1 corrected source-index bridge for optimal uniform endpoint chains:
finite optimality supplies equalized rates, while the source quantile-floor
selector is allowed a bounded old-grid error along dyadic refinements.

Source status: formalized corrected B.1 branch.  The printed uniform
quantile-convergence hypothesis is strengthened here to the fixed-width
dyadic selector envelope used by the supplement proof.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_of_uniform_optimal_quantile_floor_selector_common_coordinate_bounded_error :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_quantile_floor_selector_common_coordinate_bounded_error

/--
Theorem B.1 corrected source-index bridge for optimal uniform endpoint chains:
finite optimality supplies equalized rates, while an eventual `B/(m+2)`
real-valued tracking estimate between the source coordinate and quantile
coordinate supplies the bounded floor-selector envelope.

Source status: formalized corrected B.1 branch.  This is the source-facing
tracking form for deriving the dyadic selector envelope from quantitative
uniform coordinate tracking.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_of_uniform_optimal_quantile_floor_global_dist_tracking :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_quantile_floor_global_dist_tracking

/--
Theorem B.1 source-index bridge for optimal uniform endpoint chains, accepting
the source's floor-index formula directly.  Finite optimality supplies
equalized rates, and the floor-value selector normalizes to the common
floor-coordinate convention.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_of_uniform_optimal_floor_value_selector :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_floor_value_selector

/--
Theorem B.1 source-index bridge for optimal uniform endpoint chains under the
equispaced source convention `x_θ = θ`: finite optimality supplies equalized
rates, and the selector is given by the source floor-index value formula.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_of_uniform_optimal_identity_floor_value_selector :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_identity_floor_value_selector

/--
Theorem B.1 equispaced source bridge: finite uniform optimality plus the
Kendall/Spearman quantile-floor selector convention give the full dyadic
subsequence principle.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_of_uniform_optimal_equispaced_floor_selector :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_equispaced_floor_selector

/--
Theorem B.1 level-selector bridge: a source beta sequence represented by
endpoint levels reduces the B.1 argument to a selected-level bracket condition.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_of_uniform_equalized_levelIndex_bracket :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_levelIndex_bracket

/--
Theorem B.1 level-selector bridge: it is enough for the selected-level bracket
condition to hold eventually in the old grid index.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_of_uniform_equalized_eventually_levelIndex_bracket :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_eventually_levelIndex_bracket

/--
Theorem B.1 level-selector bridge with finite uniform optimality: a represented
source beta sequence reduces the proof to a selected-level bracket condition.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_of_uniform_optimal_levelIndex_bracket :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_levelIndex_bracket

/--
Theorem B.1 eventual level-selector bridge with finite uniform optimality: the
selected-level bracket condition only needs to hold eventually in the old grid
index.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_of_uniform_optimal_eventually_levelIndex_bracket :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_eventually_levelIndex_bracket

/--
Theorem B.1 tracking bridge: uniform tracking of a dyadic quantile sequence by
the optimal beta sequence gives a uniform subsequential limit.
-/
abbrev paper_theoremB1_dyadic_subsequence_uniform_limit_of_quantile_tracking :=
  @GJ19OptimalBinaryRatingSystems.theoremB1_dyadic_subsequence_uniform_limit_of_quantile_tracking

/--
Theorem B.1 tracking bridge with arbitrary quantile limit: if beta tracks a
dyadic quantile subsequence and that quantile subsequence has a uniform limit,
then the beta subsequence has the same uniform limit.
-/
abbrev paper_theoremB1_dyadic_subsequence_uniform_limit_of_quantile_tracking_to :=
  @GJ19OptimalBinaryRatingSystems.theoremB1_dyadic_subsequence_uniform_limit_of_quantile_tracking_to

/--
Theorem B.1 tracking bridge: if every positive dyadic subsequence of the
optimal beta sequence uniformly tracks the corresponding quantile sequence
with vanishing error, then the full B.1 subsequence principle follows.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_of_dyadic_quantile_tracking :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrinciple_of_dyadic_quantile_tracking

/--
Theorem B.1 general-limit tracking bridge: if every positive dyadic
subsequence tracks the corresponding quantile sequence with vanishing error,
then beta has dyadic subsequential uniform limits for any uniform quantile
limit.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_to_of_dyadic_quantile_tracking :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrincipleTo_of_dyadic_quantile_tracking

/--
Theorem B.1 tracking bridge with an explicit `O(1/M)` source-selector bound:
if the optimal beta sequence is uniformly within `B / (M + 1)` of the source
quantile map, then the full dyadic subsequence principle follows.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_of_global_quantile_tracking_inv_succ :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrinciple_of_global_quantile_tracking_inv_succ

/--
Theorem B.1 general-limit global tracking bridge: a single eventual uniform
tracking estimate for all source sizes gives dyadic subsequence convergence
for any uniform quantile limit.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_to_of_global_quantile_tracking :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrincipleTo_of_global_quantile_tracking

/--
Theorem B.1 general-limit global tracking bridge with an explicit `O(1/M)`
source-selector bound.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_to_of_global_quantile_tracking_inv_succ :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrincipleTo_of_global_quantile_tracking_inv_succ

/--
Corollary C.4 tracking bridge specialized to equispaced Kendall/Spearman
quantiles with an explicit `O(1/M)` source-selector bound.
-/
abbrev paper_corollaryC4_equispaced_optimal_subsequence_exists_of_global_uniform_tracking_inv_succ :=
  @GJ19OptimalBinaryRatingSystems.corollaryC4_equispaced_optimal_subsequence_exists_of_global_uniform_tracking_inv_succ

/--
Lemma B.2 fixed finite experiment step: for finitely many representative items
and finitely many questions, coordinatewise empirical convergence is uniform
over item-question pairs.
-/
abbrev paper_lemmaB2_knownTypeExperiment_finite_representatives_uniform_of_pointwise :=
  @GJ19OptimalBinaryRatingSystems.lemmaB2_knownTypeExperiment_finite_representatives_uniform_of_pointwise

/--
Lemma B.3 fixed finite experiment step: after fixing the ranked finite item
set, coordinatewise empirical convergence is uniform over ranked item-question
pairs.
-/
abbrev paper_lemmaB3_unknownTypeExperiment_fixed_finite_uniform_of_pointwise :=
  @GJ19OptimalBinaryRatingSystems.lemmaB3_unknownTypeExperiment_fixed_finite_uniform_of_pointwise

/--
Lemma B.2 finite-question product step: per-question uniform convergence on
`[0,1]` gives uniform convergence over all quality-question pairs.
-/
abbrev paper_lemmaB2_knownTypeExperiment_uniform_over_finite_questions_of_each_question :=
  @GJ19OptimalBinaryRatingSystems.lemmaB2_knownTypeExperiment_uniform_over_finite_questions_of_each_question

/--
Lemma B.3 finite-question product step: after the unknown-type ranking stage,
per-question uniform convergence on `[0,1]` gives uniform convergence over all
quality-question pairs.
-/
abbrev paper_lemmaB3_unknownTypeExperiment_uniform_over_finite_questions_of_each_question :=
  @GJ19OptimalBinaryRatingSystems.lemmaB3_unknownTypeExperiment_uniform_over_finite_questions_of_each_question

/--
Lemma B.2 deterministic `KnownTypeExperiment` learning core: empirical
tracking at representative item qualities plus a vanishing representative
mesh and Lipschitz continuity imply uniform convergence of the learned
response function.
-/
abbrev paper_lemmaB2_knownTypeExperiment_uniform_convergence_of_lipschitz_tracking :=
  @GJ19OptimalBinaryRatingSystems.lemmaB2_knownTypeExperiment_uniform_convergence_of_lipschitz_tracking

/--
Lemma B.3 deterministic `UnknownTypeExperiment` learning core: empirical
tracking at rank-selected representatives plus ranking consistency, a
vanishing mesh, and Lipschitz continuity imply uniform convergence of the
learned response function.
-/
abbrev paper_lemmaB3_unknownTypeExperiment_uniform_convergence_of_ranking_tracking :=
  @GJ19OptimalBinaryRatingSystems.lemmaB3_unknownTypeExperiment_uniform_convergence_of_ranking_tracking

/--
Theorem B.1 positive dyadic source-index bridge: under the source
clamped-floor endpoint convention and uniform equalized rates, every positive
dyadic subsequence `C * 2^N + 1` has a uniform limit on `[0,1]`.
-/
theorem paper_theoremB1_positive_dyadic_subsequence_exists_uniform_limit_of_uniform_equalized_clamped_floor
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (clampedFloorLevelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    {C : ℕ} (hC : 0 < C) :
    ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          betaSeq (theoremB1SubsequenceIndex C N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1) :=
  GJ19OptimalBinaryRatingSystems.theoremB1SubsequenceIndex_clampedFloor_subsequence_exists_uniform_limit_of_uniform_equalized
    betaSeq levels hrepr hlevels heq hC

/--
Theorem B.1 source-index bridge: the source clamped-floor endpoint convention
and uniform equalized rates imply the full dyadic subsequence principle.
-/
theorem paper_theoremB1_uniform_subsequence_principle_of_uniform_equalized_clamped_floor
    (betaSeq quantileSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (clampedFloorLevelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ))) :
    theoremB1UniformOptimalSubsequencePrinciple betaSeq quantileSeq :=
  GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrinciple_of_uniform_equalized_clampedFloor
    betaSeq quantileSeq levels hrepr hlevels heq

/--
Theorem B.1 source-index bridge: the source clamped-floor endpoint convention
and finite uniform optimality imply the full dyadic subsequence principle.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_of_uniform_optimal_clamped_floor :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrinciple_of_uniform_optimal_clampedFloor

/--
Theorem B.1 source-index bridge with the canonical uniform equalized
clamped-floor convention discharged: the canonical beta sequence has uniformly
convergent dyadic subsequences.
-/
theorem paper_theoremB1_uniform_subsequence_principle_canonical_uniform_equalized_clamped_floor :
    theoremB1UniformOptimalSubsequencePrinciple
      canonicalUniformEqualizedClampedFloorBetaSeq
      (fun M : ℕ => fun θ : ℝ => equispacedIntervalQuantile M θ) :=
  GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrinciple_canonical_uniform_equalized_clampedFloor

/--
Theorem B.1 representative-transfer bridge: if a reference representative has
uniformly convergent dyadic subsequences, exact eventual pointwise equality on
`[0,1]` transfers that conclusion to another representative.

Source status: proof-facing auxiliary; useful for non-equispaced
representative-normalization routes. This requires exact pointwise equality,
not merely equality up to measure zero.
-/
abbrev paper_theoremB1_dyadic_subsequence_uniform_convergence_of_eventually_eq :=
  @GJ19OptimalBinaryRatingSystems.theoremB1DyadicSubsequenceUniformConvergence_of_eventually_eq

/--
Theorem B.1 general-limit representative-transfer bridge: a B.1 reference
sequence for an arbitrary quantile limit transfers to any eventually pointwise
equal representative on `[0,1]`.

Source status: proof-facing auxiliary for non-equispaced representative
normalization.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_to_of_eventually_eq :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrincipleTo_of_eventually_eq

/--
Theorem B.1 identity-limit representative-transfer bridge specialized to the
paper's main B.1 wrapper.

Source status: proof-facing auxiliary for representative normalization.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_of_eventually_eq :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrinciple_of_eventually_eq

/--
Theorem B.1 transfer from the canonical uniform equalized clamped-floor
representative: if a source representative is eventually pointwise equal to
the canonical representative on `[0,1]`, then every dyadic source subsequence
has a uniform limit. This captures the representative-uniqueness route at the
uniform strength needed by B.1.

Source status: formalized conditional on exact eventual pointwise equality to
the canonical representative; a merely a.e. representative statement is not
enough for this uniform conclusion.
-/
abbrev paper_theoremB1_dyadic_subsequence_uniform_convergence_of_eventually_eq_canonical_uniform_equalized_clamped_floor :=
  @GJ19OptimalBinaryRatingSystems.theoremB1DyadicSubsequenceUniformConvergence_of_eventually_eq_canonical_uniform_equalized_clampedFloor

/--
Theorem B.1 source-facing principle from eventual pointwise equality with the
canonical uniform equalized clamped-floor representative.

Source status: formalized conditional on exact eventual pointwise equality to
the canonical representative.
-/
abbrev paper_theoremB1_uniform_subsequence_principle_of_eventually_eq_canonical_uniform_equalized_clamped_floor :=
  @GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrinciple_of_eventually_eq_canonical_uniform_equalized_clampedFloor

/--
Theorem B.1 canonical optimal equispaced source bridge: the canonical
equispaced endpoint sequence is finite-rate optimal and satisfies the
quantile-floor selector convention used by the source proof.

Source status: formalized canonical Kendall/Spearman representative for the
source's `x_θ = θ` convention.
-/
theorem paper_theoremB1_uniform_subsequence_principle_canonical_uniform_optimal_equispaced_floor_selector :
    theoremB1UniformOptimalSubsequencePrinciple
      canonicalUniformEqualizedClampedFloorBetaSeq
      (fun M : ℕ => fun θ : ℝ => equispacedIntervalQuantile M θ) :=
  GJ19OptimalBinaryRatingSystems.theoremB1UniformOptimalSubsequencePrinciple_canonical_uniform_optimal_equispaced_floor_selector

/--
Corollary C.4 source bridge: for equispaced Kendall/Spearman intervals, the
remaining input is exactly the Theorem B.1 subsequential convergence principle.
-/
theorem paper_corollaryC4_equispaced_optimal_subsequence_exists_of_theoremB1_principle
    (betaSeq : ℕ → ℝ → ℝ)
    (hB1 :
      theoremB1UniformOptimalSubsequencePrinciple
        betaSeq (fun M : ℕ => fun θ : ℝ => equispacedIntervalQuantile M θ))
    (C : ℕ) :
    ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          betaSeq (theoremB1SubsequenceIndex C N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1) :=
  GJ19OptimalBinaryRatingSystems.corollaryC4_equispaced_optimal_subsequence_exists_of_theoremB1_principle
    betaSeq hB1 C

/--
Corollary C.4 positive-dyadic quantile specialization: equispaced interval
quantiles converge uniformly to the identity along every positive B.1
subsequence.
-/
abbrev paper_corollaryC4_equispaced_dyadic_quantile_tendstoUniformlyOn_identity :=
  @GJ19OptimalBinaryRatingSystems.corollaryC4_equispaced_dyadic_quantile_tendstoUniformlyOn_identity

/--
Corollary C.4 tracking bridge: a uniform vanishing-error estimate from the
optimal beta sequence to the equispaced interval quantile sequence gives the
subsequence conclusion directly.
-/
abbrev paper_corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_tracking :=
  @GJ19OptimalBinaryRatingSystems.corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_tracking

/--
Corollary C.4 equispaced selector normalization: the interval quantile
`floor (M θ) / M` selects the same clamped endpoint as the direct coordinate
`θ`.
-/
theorem paper_corollaryC4_clamped_floor_equispaced_interval_quantile_eq
    (m : ℕ) (θ : ℝ) :
    clampedFloorLevelIndex m (equispacedIntervalQuantile (m + 2) θ) =
      clampedFloorLevelIndex m θ :=
  GJ19OptimalBinaryRatingSystems.clampedFloorLevelIndex_equispacedIntervalQuantile_eq
    m θ

/--
Corollary C.4 equispaced selector convention: for Kendall/Spearman equispaced
intervals, the B.1 common-coordinate witness is `x_θ = θ`.
-/
theorem paper_corollaryC4_equispaced_quantile_common_floor_coordinate :
    ∀ C : ℕ, 0 < C →
      let endpointStart : ℕ := 2 * C - 1
      ∀ᶠ M : ℕ in atTop,
        ∀ N : ℕ, M ≤ N →
          ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
            ∃ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 ∧
              clampedFloorLevelIndex
                  (uniformDoubledEndpointIndexIterate endpointStart M)
                  (equispacedIntervalQuantile
                    (uniformDoubledEndpointIndexIterate endpointStart M + 2)
                    θ) =
                clampedFloorLevelIndex
                  (uniformDoubledEndpointIndexIterate endpointStart M) x ∧
              clampedFloorLevelIndex
                  (uniformDoubledEndpointIndexIterate endpointStart N)
                  (equispacedIntervalQuantile
                    (uniformDoubledEndpointIndexIterate endpointStart N + 2)
                    θ) =
                clampedFloorLevelIndex
                  (uniformDoubledEndpointIndexIterate endpointStart N) x :=
  GJ19OptimalBinaryRatingSystems.corollaryC4_equispaced_quantile_common_floor_coordinate

/--
Corollary C.4 equispaced source bridge with B.1 discharged by the source
clamped-floor endpoint convention and uniform equalized rates.
-/
theorem paper_corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_equalized_clamped_floor
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (clampedFloorLevelIndex m θ))
    (hlevels : ∀ m : ℕ, BinaryEndpointLevelVector (levels m))
    (heq : ∀ m : ℕ,
      BinaryEndpointAwareAdjacentRatesEqualize (levels m)
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (C : ℕ) :
    ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          betaSeq (theoremB1SubsequenceIndex C N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1) :=
  GJ19OptimalBinaryRatingSystems.corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_equalized_clampedFloor
    betaSeq levels hrepr hlevels heq C

/--
Corollary C.4 equispaced source bridge: finite uniform optimality plus the
source clamped-floor endpoint convention discharge the B.1 convergence premise.
-/
abbrev paper_corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_optimal_clamped_floor :=
  @GJ19OptimalBinaryRatingSystems.corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_optimal_clampedFloor

/--
Corollary C.4 equispaced source bridge: finite uniform optimality plus the
source common floor-coordinate invariant discharge the B.1 convergence premise.
-/
abbrev paper_corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_optimal_common_floor_coordinate :=
  @GJ19OptimalBinaryRatingSystems.corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_optimal_common_floor_coordinate

/--
Corollary C.4 corrected bounded-selector bridge: finite uniform optimality
plus a bounded dyadic quantile-floor envelope discharge the B.1 convergence
premise for equispaced Kendall/Spearman quantiles.

Source status: formalized corrected branch matching the fixed-width selector
envelope used in the supplement proof.
-/
abbrev paper_corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_optimal_quantile_floor_selector_common_coordinate_bounded_error :=
  @GJ19OptimalBinaryRatingSystems.corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_optimal_quantile_floor_selector_common_coordinate_bounded_error

/--
Corollary C.4 bounded-selector bridge: finite uniform optimality plus the
quantile-floor selector convention and one global floor-tracking premise
discharge the B.1 convergence premise for equispaced Kendall/Spearman
quantiles.

Source status: formalized premise-reduction branch.  The remaining source
work is proving the global floor-tracking premise for arbitrary optimal
`β_M` selectors.
-/
abbrev paper_corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_optimal_quantile_floor_global_floor_tracking :=
  @GJ19OptimalBinaryRatingSystems.corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_optimal_quantile_floor_global_floor_tracking

/--
Corollary C.4 equispaced bridge through quantitative limit tracking: the
equispaced interval quantiles track the identity source coordinate at `1/M`,
so the `O(1/m)` selector-tracking premise is discharged with `B = 1`.
-/
abbrev paper_corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_optimal_quantile_floor_limit_dist_tracking :=
  @GJ19OptimalBinaryRatingSystems.corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_optimal_quantile_floor_limit_dist_tracking

/--
Corollary C.4 equispaced source bridge for optimal uniform endpoint chains:
finite optimality and the source floor-index value formula with `x_θ = θ`
discharge the B.1 convergence premise.
-/
abbrev paper_corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_optimal_identity_floor_value_selector :=
  @GJ19OptimalBinaryRatingSystems.corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_optimal_identity_floor_value_selector

/--
Corollary C.4 equispaced Kendall/Spearman bridge: with the source convention
`x_θ = θ`, every positive dyadic optimal subsequence has a uniform limit.
-/
abbrev paper_corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_optimal_source_floor_selector_convention :=
  @GJ19OptimalBinaryRatingSystems.corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_optimal_source_floor_selector_convention

/--
Corollary C.4 equispaced Kendall/Spearman bridge: finite uniform optimality
and the paper's quantile-floor selector convention imply that every dyadic
optimal subsequence has a uniform limit.
-/
theorem paper_corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_optimal_quantile_floor_selector
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (levelIndex : (m : ℕ) → ℝ → Fin (m + 2))
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m (levelIndex m θ))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (hlevelIndex_val :
      ∀ m θ, θ ∈ Set.Icc (0 : ℝ) 1 →
        (levelIndex m θ).1 =
          min
            (Nat.floor (((m + 2 : ℕ) : ℝ) *
              equispacedIntervalQuantile (m + 2) θ))
            (m + 1))
    (C : ℕ) :
    ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          betaSeq (theoremB1SubsequenceIndex C N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1) :=
  GJ19OptimalBinaryRatingSystems.corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_optimal_quantile_floor_selector
    betaSeq levels levelIndex hrepr hoptimal hlevelIndex_val C

/--
Corollary C.4 equispaced Kendall/Spearman bridge with the source
quantile-floor selector built in: finite uniform optimality and the
equispaced selector convention imply that every dyadic optimal subsequence has
a uniform limit.
-/
theorem paper_corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_optimal_equispaced_floor_selector
    (betaSeq : ℕ → ℝ → ℝ)
    (levels : (m : ℕ) → Fin (m + 2) → ℝ)
    (hrepr : ∀ m θ, betaSeq (m + 2) θ =
      levels m
        (clampedFloorLevelIndex m (equispacedIntervalQuantile (m + 2) θ)))
    (hoptimal : ∀ m : ℕ,
      AppliedModelingLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun xs : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective xs
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        (levels m))
    (C : ℕ) :
    ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          betaSeq (theoremB1SubsequenceIndex C N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1) :=
  GJ19OptimalBinaryRatingSystems.corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_optimal_equispaced_floor_selector
    betaSeq levels hrepr hoptimal C

/--
Corollary C.4 equispaced source bridge: finite uniform optimality plus the
source two-step bracket condition discharge the B.1 convergence premise.
-/
abbrev paper_corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_optimal_two_step_bracket :=
  @GJ19OptimalBinaryRatingSystems.corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_optimal_two_step_bracket

/--
Corollary C.4 equispaced source bridge: finite uniform optimality plus an
eventual source two-step bracket condition discharge the B.1 convergence
premise.
-/
abbrev paper_corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_optimal_eventually_two_step_bracket :=
  @GJ19OptimalBinaryRatingSystems.corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_optimal_eventually_two_step_bracket

/--
Corollary C.4 equispaced source bridge: finite uniform optimality plus an
eventual fixed-width old-grid bracket condition discharge the B.1 convergence
premise.
-/
abbrev paper_corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_optimal_eventually_fixed_width_bracket :=
  @GJ19OptimalBinaryRatingSystems.corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_optimal_eventually_fixed_width_bracket

/--
Corollary C.4 equispaced source bridge: finite uniform optimality plus a
selected-level two-step bracket condition discharge the B.1 convergence
premise.
-/
abbrev paper_corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_optimal_levelIndex_bracket :=
  @GJ19OptimalBinaryRatingSystems.corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_optimal_levelIndex_bracket

/--
Corollary C.4 equispaced source bridge: finite uniform optimality plus an
eventual selected-level bracket condition discharge the B.1 convergence
premise.
-/
abbrev paper_corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_optimal_eventually_levelIndex_bracket :=
  @GJ19OptimalBinaryRatingSystems.corollaryC4_equispaced_optimal_subsequence_exists_of_uniform_optimal_eventually_levelIndex_bracket

/--
Corollary C.4 for the canonical uniform equalized clamped-floor convention:
every dyadic source subsequence of the canonical beta sequence has a uniform
limit on `[0,1]`.
-/
theorem paper_corollaryC4_equispaced_optimal_subsequence_exists_canonical_uniform_equalized_clamped_floor
    (C : ℕ) :
    ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          canonicalUniformEqualizedClampedFloorBetaSeq
            (theoremB1SubsequenceIndex C N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1) :=
  GJ19OptimalBinaryRatingSystems.corollaryC4_equispaced_optimal_subsequence_exists_canonical_uniform_equalized_clampedFloor
    C

/--
Corollary C.4 canonical optimal equispaced branch: for the canonical
finite-rate-optimal Kendall/Spearman representative, every dyadic source
subsequence has a uniform limit on `[0,1]`.

Source status: formalized canonical representative of the existential
Kendall/Spearman Corollary C.4 conclusion.
-/
theorem paper_corollaryC4_equispaced_optimal_subsequence_exists_canonical_uniform_optimal_equispaced_floor_selector
    (C : ℕ) :
    ∃ betaLimit : ℝ → ℝ,
      TendstoUniformlyOn
        (fun N : ℕ => fun θ : ℝ =>
          canonicalUniformEqualizedClampedFloorBetaSeq
            (theoremB1SubsequenceIndex C N) θ)
        betaLimit atTop (Set.Icc (0 : ℝ) 1) :=
  GJ19OptimalBinaryRatingSystems.corollaryC4_equispaced_optimal_subsequence_exists_canonical_uniform_optimal_equispaced_floor_selector
    C

/-! ## Source-model and reopened-audit endpoints -/

/-- Main-paper source model: the normalized unit quality continuum. -/
abbrev paper_sourceQualityDomain := sourceQualityDomain

/-- Main-paper source assumptions on the nondecreasing matching function. -/
abbrev paper_SourceMatchingFunction := SourceMatchingFunction

/-- Main-paper floor match count `n_k(θ) = floor(k g(θ))`. -/
abbrev paper_sourceMatchingCount := sourceMatchingCount

/-- Main-paper empirical fraction of positive binary ratings. -/
abbrev paper_sourceEmpiricalReputationScore := sourceEmpiricalReputationScore

/-- Main-paper state measure on quality and empirical reputation. -/
abbrev paper_SourceSystemState := SourceSystemState

/-- Appendix B.1 active set for the transition from time `k` to `k+1`. -/
abbrev paper_sourceAppendixBActiveSet := sourceAppendixBActiveSet

/-- Appendix B.1 corrected atomic two-branch transition kernel. -/
abbrev paper_sourceAppendixBTransitionKernel := sourceAppendixBTransitionKernel

/-- Appendix B.1 corrected state-update equation on quality-score rectangles. -/
abbrev paper_sourceAppendixBStateUpdateMass := sourceAppendixBStateUpdateMass

/-- Section 4 finite probability distribution over available questions. -/
abbrev paper_SourceQuestionDistribution := @SourceQuestionDistribution

/-- Section 4 induced response `betaTilde(θ) = sum_y psi(θ,y) H(y)`. -/
abbrev paper_sourceInducedBinaryResponse := @sourceInducedBinaryResponse

/-- Section 4 equation-(5) finite representative-item `L1` objective. -/
abbrev paper_sourceQuestionDesignL1Objective := @sourceQuestionDesignL1Objective

/-- Section 4 probability-constrained minimizer predicate for equation (5). -/
abbrev paper_SourceQuestionDesignSolution := @SourceQuestionDesignSolution

/-- Appendix B.5 literal random-question/binary-response experiment records. -/
abbrev paper_SourceRandomQuestionExperiment := SourceRandomQuestionExperiment

/-- Appendix B.5 empirical conditional positive-response frequency. -/
abbrev paper_sourceExperimentEmpiricalQuestionResponse :=
  @sourceExperimentEmpiricalQuestionResponse

/--
Theorem 3.1 source cell-rate identity: the displayed `g_i` infimum is the
matching function at the lower endpoint of an ordered cell.
-/
abbrev paper_sourceCellMatchingRate_eq_lower_cutpoint :=
  @sourceCellMatchingRate_eq_lower_cutpoint

/--
Theorem 3.1 source assembly for a selected value-maximizing discretization:
the cell rates, endpoint optimizer, and exact `Wbar_k` rate certificate are
derived from primitive `g` and the source model.
-/
abbrev paper_theorem31_source_matching_function_weighted_value_argmax_certificate :=
  @theorem31_source_matching_function_weighted_value_argmax_certificate

/-- Appendix B.3 Lemma B.1 two-optimizer matching-rate comparative statics. -/
abbrev paper_lemmaB1_matching_rate_shift := @lemmaB1_matching_rate_shift

/--
Lemma B.2 SLLN from the literal random-question experiment: positive question
mass yields consistent conditional response frequencies for every fixed
finite item-question coordinate.
-/
abbrev paper_lemmaB2_knownTypeExperiment_ae_question_response_of_iid :=
  @lemmaB2_knownTypeExperiment_ae_question_response_of_iid

/--
Corrected Lemma B.3: random-question response learning and empirical ranking
hold jointly under explicit strict aggregate-score identifiability.
-/
abbrev paper_lemmaB3_unknownTypeExperiment_ae_random_question_response_and_rank_of_iid :=
  @lemmaB3_unknownTypeExperiment_ae_random_question_response_and_rank_of_iid

/--
Lemma C.6 for general positive nondecreasing matching rates, with the last
width comparison derived rather than assumed.
-/
abbrev paper_lemmaC6_monotone_matching_penultimate_level_bound :=
  @BinaryEndpointLevelVector_monotone_equalized_last_low_ge_one_sub_inv

/--
Theorem 3.2's literal ideal-real weighted nested-bisection output: both the
direct inner rate tests and the outer source classifier are independent of the
optimum.
-/
abbrev paper_theorem32WeightedNestedBisectionOutput :=
  @theorem32WeightedNestedBisectionOutput

/--
Theorem 3.2 rate-loss and runtime certificate for the literal direct-rate
runner with the finite source grid and dyadic depth constructed internally.
-/
abbrev paper_theorem32WeightedNestedBisectionOutput_loss_and_runtime :=
  @theorem32WeightedNestedBisectionOutput_exists_source_depth_of_eps_pos

end

end GJ19OptimalBinaryRatingSystems

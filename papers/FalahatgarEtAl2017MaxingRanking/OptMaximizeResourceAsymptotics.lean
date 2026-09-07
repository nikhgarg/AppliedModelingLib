import FalahatgarEtAl2017MaxingRanking.OptMaximizeResourceTrace
import FalahatgarEtAl2017MaxingRanking.PickAnchorAsymptotics
import FalahatgarEtAl2017MaxingRanking.SourceOptMaximizeAsymptotics
import FalahatgarEtAl2017MaxingRanking.SeqEliminateAsymptotics

/-!
# OPT-Maximize Algorithm-3 resource asymptotics

This module connects the literal `delta / 4` execution proved in the finite
trace theorem to one population-only envelope and proves the paper's fixed-
parameter linear comparison-rate shape. The probability proof and this rate
proof therefore use the same algorithm rather than a rescaled surrogate.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL
open MeasureTheory ProbabilityTheory
open Asymptotics

/-- Population-only comparison envelope for Algorithm 3's literal non-base branch. -/
noncomputable def sourceOptMaximizeAlgorithm3RateEnvelope
    (armCount : ℕ) (lower upper epsilon delta : ℝ) : ℝ :=
  sourceOptMaximizePickAnchorComparisonEnvelope armCount lower (delta / 4) +
    sourceLemma5PruneComparisonRateBound armCount lower upper (delta / 4) +
    2 * (sourceOptMaximizeCutoff armCount : ℝ) *
        (2 / (upper - lower) ^ 2 *
          (Real.log (8 / delta) + Real.log (armCount : ℝ)) + 1) +
      2 * (sourceOptMaximizeCutoff armCount : ℝ) *
        (2 / epsilon ^ 2 *
          (Real.log (8 / delta) + Real.log (armCount : ℝ)) + 1)

/-- The exact retained-set resource bound is below the population envelope. -/
theorem optMaximizeAlgorithm3SourceBudget_le_rateEnvelope
    {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (candidates : Finset Arm) (lower upper epsilon delta : ℝ)
    (hcard : candidates.card ≤ 2 * sourceOptMaximizeCutoff (Fintype.card Arm))
    (hepsilon : 0 < epsilon) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    (optMaximizePickAnchorComparisonCap (Arm := Arm)
          (sourceOptMaximizeCutoff (Fintype.card Arm)) (delta / 4) lower : ℝ) +
        sourceLemma5PruneComparisonRateBound (Fintype.card Arm) lower upper (delta / 4) +
        optMaximizeFinalTailAlgorithm3SourceBudget candidates lower upper epsilon delta ≤
      sourceOptMaximizeAlgorithm3RateEnvelope
        (Fintype.card Arm) lower upper epsilon delta := by
  have hcutoff : 0 < sourceOptMaximizeCutoff (Fintype.card Arm) :=
    sourceOptMaximizeCutoff_pos (Fintype.card Arm) Fintype.card_pos
  have hanchor := optMaximizePickAnchorComparisonCap_real_le_sourceCountEnvelope_generic
    (Arm := Arm) (sourceOptMaximizeCutoff (Fintype.card Arm)) lower (delta / 4)
    hcutoff (by positivity) (by linarith)
  have htail := optMaximizeFinalTailAlgorithm3SourceBudget_le_cardEnvelope
    candidates (sourceOptMaximizeCutoff (Fintype.card Arm)) lower upper epsilon delta
    hcard hepsilon hdelta hdeltaLeOne
  unfold sourceOptMaximizeAlgorithm3RateEnvelope
    sourceOptMaximizePickAnchorComparisonEnvelope
  linarith

/--
Theorem 6's joint success event with the literal execution count bounded by
the population-only envelope whose asymptotics are proved below.
-/
noncomputable def canonicalOptMaximizeAlgorithm3SourcePopulationJointEnvelopeProbability
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (lower upper epsilon delta : ℝ) (maxBatch : ℕ)
    (preferenceGap : Arm → Arm → ℝ) (maximum : Arm)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta (delta / 4) round) ≤ maxBatch) : ℝ := by
  classical
  let cutoff := sourceOptMaximizeCutoff (Fintype.card Arm)
  if delta ≤ 1 / (Fintype.card Arm : ℝ) then
    exact canonicalOptMaximizeBaseSourceJointResourceProbability
      preferenceGap hprobability epsilon delta
  else
    exact pmfProb
      (canonicalOptMaximizeTraceFallbackFinalTraceSourceLaw cutoff (delta / 4) (delta / 4)
        (delta / 4) (delta / 4) lower upper epsilon maxBatch preferenceGap maximum hprobability
        (sourceOptMaximizeCutoff_pos (Fintype.card Arm) Fintype.card_pos)
        (by linarith) (by linarith) hbudget)
      (fun traceFallbackFinalTrace =>
        EpsilonMaximum preferenceGap epsilon
            (if traceFallbackFinalTrace.2.2 then traceFallbackFinalTrace.1.1.1 else
              traceFallbackFinalTrace.1.2) ∧
          GoodAnchor preferenceGap lower cutoff traceFallbackFinalTrace.1.1.1 ∧
            traceFallbackFinalTrace.1.1.2.2 = false ∧
              traceFallbackFinalTrace.1.1.2.1.1.card ≤ 2 * cutoff ∧
              (EpsilonMaximum preferenceGap upper traceFallbackFinalTrace.1.1.1 ∨
                maximum ∈ traceFallbackFinalTrace.1.1.2.1.1) ∧
              (optMaximizeTraceFallbackFinalTraceComparisonCount cutoff (delta / 4) (delta / 4)
                lower upper ((delta / 4) / (Fintype.card Arm : ℝ)) epsilon (delta / 4)
                traceFallbackFinalTrace : ℝ) ≤
                sourceOptMaximizeAlgorithm3RateEnvelope
                  (Fintype.card Arm) lower upper epsilon delta)

/-- The literal Algorithm-3 population event has probability at least `1 - delta`. -/
theorem canonicalOptMaximizeAlgorithm3SourcePopulationJointEnvelopeProbability_ge
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (lower upper epsilon delta : ℝ) (maxBatch : ℕ)
    (preferenceGap : Arm → Arm → ℝ) (maximum : Arm)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (ranking : Fin (Fintype.card Arm) → Arm)
    (hranking : PreferenceRanking preferenceGap ranking)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) (hlower : 0 < lower)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hcomplete : PreferenceComplete preferenceGap)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta (delta / 4) round) ≤ maxBatch)
    (hupperNonnegative : 0 ≤ upper)
    (hmaximumAbsolute : AbsoluteMaximum preferenceGap maximum)
    (hseparation : lower < upper)
    (hepsilon : 0 < epsilon) (hfinalSeparation : upper < epsilon) :
    1 - delta ≤
      canonicalOptMaximizeAlgorithm3SourcePopulationJointEnvelopeProbability
        lower upper epsilon delta maxBatch preferenceGap maximum hprobability
        hdelta hdeltaLeOne hbudget := by
  classical
  unfold canonicalOptMaximizeAlgorithm3SourcePopulationJointEnvelopeProbability
  dsimp only
  split
  · exact canonicalOptMaximizeBaseSource_joint_resource_probability preferenceGap hprobability
      epsilon delta hantisymmetric hself hsst hepsilon hdelta hdeltaLeOne maximum hmaximumAbsolute
  · rename_i hnonbase
    let cutoff := sourceOptMaximizeCutoff (Fintype.card Arm)
    have hsource :=
      canonicalOptMaximizeTraceFallbackFinalTraceAlgorithm3SourceJointEnvelopeProbability_ge_nonbase
        lower upper epsilon delta maxBatch preferenceGap maximum hprobability ranking hranking
        hdelta hdeltaLeOne hlower hantisymmetric hself hcomplete hsst hbudget hupperNonnegative
        hmaximumAbsolute hseparation hepsilon hfinalSeparation (lt_of_not_ge hnonbase)
    dsimp only at hsource ⊢
    unfold canonicalOptMaximizeTraceFallbackFinalTraceAlgorithm3SourceJointEnvelopeProbability at hsource
    apply hsource.trans
    apply pmfProb_le_of_imp
    intro traceFallbackFinalTrace hsuccess
    rcases hsuccess with ⟨houtput, hgood, hstopped, hcard, hmaximum, hcount⟩
    refine ⟨houtput, hgood, hstopped, hcard, hmaximum, ?_⟩
    exact hcount.trans (optMaximizeAlgorithm3SourceBudget_le_rateEnvelope
      traceFallbackFinalTrace.1.1.2.1.1 lower upper epsilon delta hcard
      hepsilon hdelta hdeltaLeOne)

/-- The literal non-base envelope divided by population has a finite limit. -/
theorem tendsto_sourceOptMaximizeAlgorithm3RateEnvelope_div_nat
    {lower upper epsilon delta : ℝ}
    (hlower : 0 < lower) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    Filter.Tendsto
      (fun armCount : ℕ =>
        sourceOptMaximizeAlgorithm3RateEnvelope armCount lower upper epsilon delta /
          (armCount : ℝ))
      Filter.atTop
      (nhds (16 * (2 / (upper - lower) ^ 2 + 1) *
        (1 + Real.log (1 / (delta / 4))))) := by
  let pruneLimit : ℝ :=
    16 * (2 / (upper - lower) ^ 2 + 1) * (1 + Real.log (1 / (delta / 4)))
  have hpopulationRatio :
      Filter.Tendsto (fun armCount : ℕ => (armCount : ℝ) / (armCount : ℝ))
        Filter.atTop (nhds 1) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_gt_atTop 0] with armCount harmCount
    field_simp [ne_of_gt (show 0 < (armCount : ℝ) by exact_mod_cast harmCount)]
  have hanchor :=
    tendsto_sourceOptMaximizePickAnchorComparisonEnvelope_div_nat_nhds_zero
      (lower := lower) (anchorDelta := delta / 4) hlower (by positivity) (by linarith)
  have hprune :
      Filter.Tendsto
        (fun armCount : ℕ =>
          sourceLemma5PruneComparisonRateBound armCount lower upper (delta / 4) /
            (armCount : ℝ))
        Filter.atTop (nhds pruneLimit) := by
    have hscaled := hpopulationRatio.const_mul pruneLimit
    refine Filter.Tendsto.congr' ?_ (by simpa using hscaled)
    filter_upwards with armCount
    dsimp [pruneLimit, sourceLemma5PruneComparisonRateBound]
    ring
  have hcutoff := tendsto_sourceOptMaximizeCutoff_div_nat_nhds_zero
  have hcutoffLog := tendsto_sourceOptMaximizeCutoff_mul_log_div_nat_nhds_zero
  have htailCore :
      Filter.Tendsto
        (fun armCount : ℕ =>
          (sourceOptMaximizeCutoff armCount : ℝ) *
            (Real.log (8 / delta) + Real.log (armCount : ℝ)) /
              (armCount : ℝ))
        Filter.atTop (nhds 0) := by
    have hsum := hcutoff.const_mul (Real.log (8 / delta)) |>.add hcutoffLog
    refine Filter.Tendsto.congr' ?_ (by simpa using hsum)
    filter_upwards with armCount
    ring
  have hupperTail :
      Filter.Tendsto
        (fun armCount : ℕ =>
          2 * (sourceOptMaximizeCutoff armCount : ℝ) *
              (2 / (upper - lower) ^ 2 *
                (Real.log (8 / delta) + Real.log (armCount : ℝ)) + 1) /
            (armCount : ℝ))
        Filter.atTop (nhds 0) := by
    have hsum := (htailCore.const_mul (4 / (upper - lower) ^ 2)).add
      (hcutoff.const_mul (2 : ℝ))
    refine Filter.Tendsto.congr' ?_ (by simpa using hsum)
    filter_upwards with armCount
    ring
  have hepsilonTail :
      Filter.Tendsto
        (fun armCount : ℕ =>
          2 * (sourceOptMaximizeCutoff armCount : ℝ) *
              (2 / epsilon ^ 2 *
                (Real.log (8 / delta) + Real.log (armCount : ℝ)) + 1) /
            (armCount : ℝ))
        Filter.atTop (nhds 0) := by
    have hsum := (htailCore.const_mul (4 / epsilon ^ 2)).add
      (hcutoff.const_mul (2 : ℝ))
    refine Filter.Tendsto.congr' ?_ (by simpa using hsum)
    filter_upwards with armCount
    ring
  have htotal := ((hanchor.add hprune).add hupperTail).add hepsilonTail
  refine Filter.Tendsto.congr' ?_ (by simpa [pruneLimit] using htotal)
  filter_upwards with armCount
  unfold sourceOptMaximizeAlgorithm3RateEnvelope
  ring

/-- The literal non-base envelope is linear for fixed valid parameters. -/
theorem sourceOptMaximizeAlgorithm3RateEnvelope_isBigO_linear
    {lower upper epsilon delta : ℝ}
    (hlower : 0 < lower) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    IsBigO Filter.atTop
      (fun armCount : ℕ =>
        sourceOptMaximizeAlgorithm3RateEnvelope armCount lower upper epsilon delta)
      (fun armCount : ℕ => (armCount : ℝ)) := by
  let rateLimit : ℝ :=
    16 * (2 / (upper - lower) ^ 2 + 1) * (1 + Real.log (1 / (delta / 4)))
  have hlimit := tendsto_sourceOptMaximizeAlgorithm3RateEnvelope_div_nat
    (upper := upper) (epsilon := epsilon) hlower hdelta hdeltaLeOne
  have hbound : ∀ᶠ armCount : ℕ in Filter.atTop,
      |sourceOptMaximizeAlgorithm3RateEnvelope armCount lower upper epsilon delta /
        (armCount : ℝ)| ≤ |rateLimit| + 1 := by
    have hupper := hlimit.eventually
      (eventually_lt_nhds (by norm_num : rateLimit < rateLimit + 1))
    have hlower := hlimit.eventually
      (eventually_gt_nhds (by norm_num : rateLimit - 1 < rateLimit))
    filter_upwards [hupper, hlower] with armCount hu hl
    rw [abs_le]
    constructor
    · nlinarith [neg_abs_le rateLimit]
    · nlinarith [le_abs_self rateLimit]
  rw [isBigO_iff]
  refine ⟨|rateLimit| + 1, ?_⟩
  filter_upwards [hbound, Filter.eventually_gt_atTop 0] with armCount hratio harmCount
  have hn : 0 < (armCount : ℝ) := by exact_mod_cast harmCount
  rw [abs_div] at hratio
  have hscaled := (div_le_iff₀ hn).mp (by simpa [abs_of_pos hn] using hratio)
  simpa [Real.norm_eq_abs, abs_of_pos hn] using hscaled

/-- The literal non-base envelope has the paper's fixed-parameter rate shape. -/
theorem sourceOptMaximizeAlgorithm3RateEnvelope_isBigO_sourceRateShape
    {epsilon delta : ℝ} (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    IsBigO Filter.atTop
      (fun armCount : ℕ => sourceOptMaximizeAlgorithm3RateEnvelope armCount
        (epsilon / 3) (2 * epsilon / 3) epsilon delta)
      (fun armCount : ℕ =>
        (armCount : ℝ) * (1 + Real.log (1 / delta)) / epsilon ^ 2) := by
  have hlinear := sourceOptMaximizeAlgorithm3RateEnvelope_isBigO_linear
    (lower := epsilon / 3) (upper := 2 * epsilon / 3) (epsilon := epsilon)
    (delta := delta) (by linarith) hdelta hdeltaLeOne
  have hlog : 0 ≤ Real.log (1 / delta) := by
    apply Real.log_nonneg
    exact (one_le_div₀ hdelta).mpr hdeltaLeOne
  have hfactor : 0 < (1 + Real.log (1 / delta)) / epsilon ^ 2 :=
    div_pos (by linarith) (sq_pos_of_pos hepsilon)
  have hscale : IsBigO Filter.atTop
      (fun armCount : ℕ => (armCount : ℝ))
      (fun armCount : ℕ =>
        (armCount : ℝ) * (1 + Real.log (1 / delta)) / epsilon ^ 2) := by
    apply AppliedModelingLib.Math.isBigO_of_eventually_pos_mul_le hfactor
    · filter_upwards with armCount
      exact_mod_cast Nat.zero_le armCount
    · filter_upwards with armCount
      positivity
    · filter_upwards with armCount
      ring_nf
      exact le_rfl
  exact hlinear.trans hscale

/-- Algorithm 3's complete branchwise finite envelope. -/
noncomputable def sourceOptMaximizeAlgorithm3TotalRateEnvelope
    (armCount : ℕ) (epsilon delta : ℝ) : ℝ :=
  if delta ≤ 1 / (armCount : ℝ) then
    seqEliminateSourceComparisonEnvelope armCount epsilon delta
  else
    sourceOptMaximizeAlgorithm3RateEnvelope armCount
      (epsilon / 3) (2 * epsilon / 3) epsilon delta

/-- The complete branchwise envelope has the paper's fixed-parameter rate shape. -/
theorem sourceOptMaximizeAlgorithm3TotalRateEnvelope_isBigO_sourceRateShape
    {epsilon delta : ℝ} (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    IsBigO Filter.atTop
      (fun armCount : ℕ =>
        sourceOptMaximizeAlgorithm3TotalRateEnvelope armCount epsilon delta)
      (fun armCount : ℕ =>
        (armCount : ℝ) * (1 + Real.log (1 / delta)) / epsilon ^ 2) := by
  have hnonbase := sourceOptMaximizeAlgorithm3RateEnvelope_isBigO_sourceRateShape
    hepsilon hdelta hdeltaLeOne
  have hreciprocal : Filter.Tendsto (fun armCount : ℕ => 1 / (armCount : ℝ))
      Filter.atTop (nhds 0) := tendsto_const_div_atTop_nhds_zero_nat 1
  have hbranch : ∀ᶠ armCount : ℕ in Filter.atTop, 1 / (armCount : ℝ) < delta :=
    hreciprocal.eventually (eventually_lt_nhds hdelta)
  have heq : (fun armCount : ℕ =>
      sourceOptMaximizeAlgorithm3RateEnvelope armCount
        (epsilon / 3) (2 * epsilon / 3) epsilon delta) =ᶠ[Filter.atTop]
      fun armCount => sourceOptMaximizeAlgorithm3TotalRateEnvelope armCount epsilon delta := by
    filter_upwards [hbranch] with armCount hnonbaseBranch
    unfold sourceOptMaximizeAlgorithm3TotalRateEnvelope
    rw [if_neg (not_le_of_gt hnonbaseBranch)]
  exact hnonbase.congr' heq (Filter.Eventually.of_forall (fun _ => rfl))

end FalahatgarEtAl2017MaxingRanking

import PRPKG24AccuracyDiversity.SeparableAsymptotic
import AppliedModelingLib.Foundations.Math.GammaAsymptotics
import AppliedModelingLib.Foundations.Probability.Pareto
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace PRPKG24AccuracyDiversity

open scoped BigOperators

/--
Expected maximum of `q` draws from a distribution with tail index α.
Instead of calculating the integral, we define the target marginal behavior.
-/
def HasTailIndex (f : ℕ → ℝ) (index : ℝ) : Prop := ∃ C > 0, ∀ q, 0 < q → f (q + 1) - f q = C * (q : ℝ) ^ (index - 1)

/--
A model where every type has conditional item values with the same tail index.
-/
def HasTypeTailIndex (M : ConsumptionModel T) (index : ℝ) : Prop := ∀ t, HasTailIndex (M.valueOfCount t) index

/--
The γ-homogeneity profile for a Pareto distribution with tail index α.
The target weights are proportional to `likelihood ^ α`.
-/
noncomputable def paretoProfile {T : ℕ} (likelihood : ItemType T → ℝ) (α : ℝ) :
    GammaHomogeneityProfile T where
  gamma := 1 - 1/α
  targetWeight := fun t => (likelihood t) ^ α

/--
A Top-k oracle for a model where every type has item values following a Pareto
distribution with tail index α.
-/
noncomputable def ParetoTopKOracle {T : ℕ} (α : ℝ) : TopKValueOracle T where
  expectedTopSum _ _ q := (q : ℝ) ^ (1/α)

/-- Marginal decay exponent for the Pareto branch's power-law oracle. -/
noncomputable def paretoMarginalExponent (α : ℝ) : ℝ := (α - 1) / α

theorem paretoMarginalExponent_pos {α : ℝ} (hα_gt_one : 1 < α) :
    0 < paretoMarginalExponent α := by
  unfold paretoMarginalExponent
  exact div_pos (sub_pos.mpr hα_gt_one) (lt_trans zero_lt_one hα_gt_one)

theorem paretoMarginalExponent_one_div_eq_gamma
    {α : ℝ} (hα_gt_one : 1 < α) :
    1 / paretoMarginalExponent α = α / (α - 1) := by
  have hα_pos : 0 < α := lt_trans zero_lt_one hα_gt_one
  have hsub_pos : 0 < α - 1 := sub_pos.mpr hα_gt_one
  unfold paretoMarginalExponent
  field_simp [ne_of_gt hα_pos, ne_of_gt hsub_pos]

/--
Exact power-marginal value used as a source-faithful Pareto asymptotic
checkpoint.

The paper's Pareto branch uses marginal decay proportional to
`q^-((α-1)/α)`, which yields the target exponent `α/(α-1)`. This value
function records that marginal law exactly, leaving the full order-statistic
derivation as the remaining probability step.
-/
noncomputable def paretoPowerMarginalValue (α : ℝ) (q : ℕ) : ℝ :=
  ∑ j ∈ Finset.range q,
    (((j + 1 : ℕ) : ℝ) ^ (-(paretoMarginalExponent α)))

/-- Common top-one oracle with exact Pareto power-law marginals. -/
noncomputable def paretoPowerMarginalOracle (T : ℕ) (α : ℝ) :
    TopKValueOracle T := TopKValueOracle.common T (paretoPowerMarginalValue α)

theorem paretoPowerMarginalValue_zero (α : ℝ) :
    paretoPowerMarginalValue α 0 = 0 := by
  simp [paretoPowerMarginalValue]

theorem paretoPowerMarginalValue_forward_marginal
    (α : ℝ) (q : ℕ) :
    paretoPowerMarginalValue α (q + 1) -
        paretoPowerMarginalValue α q =
      (((q + 1 : ℕ) : ℝ) ^ (-(paretoMarginalExponent α))) := by
  simp [paretoPowerMarginalValue, Finset.sum_range_succ]

/-- Exact scaled marginal used by the Pareto power-marginal oracle. -/
noncomputable def paretoPowerMarginalScale (α : ℝ) (q : ℕ) : ℝ := (((q + 1 : ℕ) : ℝ) ^ (-(paretoMarginalExponent α)))

theorem paretoPowerMarginalScale_pos (α : ℝ) (q : ℕ) :
    0 < paretoPowerMarginalScale α q := by
  unfold paretoPowerMarginalScale
  exact Real.rpow_pos_of_pos (by positivity) _

/-- Concrete iid product measure for the paper's scale-one Pareto source law. -/
noncomputable def paretoIidSampleMeasure (α : ℝ) (q : ℕ) :
    MeasureTheory.Measure (Fin q → ℝ) :=
  AppliedModelingLib.Probability.Pareto.iidProductMeasure 1 α q

theorem paretoIidSampleMeasure_isProbabilityMeasure
    {α : ℝ} (hα_pos : 0 < α) (q : ℕ) :
    MeasureTheory.IsProbabilityMeasure (paretoIidSampleMeasure α q) := by
  simpa [paretoIidSampleMeasure] using
    AppliedModelingLib.Probability.Pareto.isProbabilityMeasure_iidProductMeasure
      (t := 1) (r := α) (by norm_num) hα_pos q

theorem paretoIidSampleMeasure_isProbabilityMeasure_of_gt_one
    {α : ℝ} (hα : 1 < α) (q : ℕ) :
    MeasureTheory.IsProbabilityMeasure (paretoIidSampleMeasure α q) :=
  paretoIidSampleMeasure_isProbabilityMeasure (lt_trans zero_lt_one hα) q

/--
The actual paper-source order-statistic mean sequence for iid scale-one Pareto
samples.  Lemma D.4 identifies this sequence with the cited gamma-ratio formula
at every fixed distance from the top order statistic.
-/
noncomputable def paretoIidOrderStatisticMeanSeq (α : ℝ) : ℕ → ℕ → ℝ :=
  expectedOrderStatisticMeanSeq (paretoIidSampleMeasure α)

/-- Top-`k` oracle induced by the concrete scale-one iid Pareto sample law. -/
noncomputable def paretoIidOrderStatisticOracle (T : ℕ) (α : ℝ) :
    TopKValueOracle T :=
  TopKValueOracle.ofOrderStatisticMean T (paretoIidOrderStatisticMeanSeq α)

/-- Consumption model induced by the concrete scale-one iid Pareto source law. -/
noncomputable def paretoIidOrderStatisticConsumptionModel {T : ℕ}
    (likelihood : ItemType T → ℝ) (k : ℕ) (α : ℝ) :
    ConsumptionModel T :=
  (paretoIidOrderStatisticOracle T α).toConsumptionModel likelihood k

/--
Count-level FOC package for the Pareto iid order-statistic optimization bridge.

This remains useful as an intermediate certificate interface.  The direct
Theorem 1(iv) iid Pareto endpoint below now derives the large-gap version from
Gamma-ratio bounds, so callers of the paper-facing theorem do not provide this
certificate explicitly.
-/
structure ParetoIidOrderStatisticEventualFOCCertificate {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (k : ℕ) (α : ℝ) where
  base_error : ℕ → ℝ
  base_error_nonneg : ∀ N, 0 ≤ base_error N
  base_error_tends_to_zero : AppliedModelingLib.Math.TendsToZero base_error
  floor : ℕ
  count_floor_eventually :
    ∀ᶠ N in Filter.atTop,
      ∀ a : CountAllocation T, 0 < N →
        (paretoIidOrderStatisticConsumptionModel likelihood k α).IsOptimalAtTotal N a →
        ∀ t, floor < a.count t
  large_gap_count :
    ∀ᶠ N in Filter.atTop,
      ∀ src dst qsrc qdst,
        qsrc ≤ N →
        qdst ≤ N →
        floor < qsrc →
        floor < qdst →
        base_error N * (N : ℝ) <
          (qsrc : ℝ) / likelihood src ^ (α / (α - 1)) -
            (qdst : ℝ) / likelihood dst ^ (α / (α - 1)) →
        (paretoIidOrderStatisticConsumptionModel likelihood k α).weightedBackwardMarginal
            src qsrc <
          (paretoIidOrderStatisticConsumptionModel likelihood k α).weightedForwardMarginal
            dst qdst

namespace ParetoIidOrderStatisticEventualFOCCertificate

noncomputable def toPairwiseScaledEventualSublinearFOCCertificate
    {T : ℕ} [NeZero T]
    {likelihood : ItemType T → ℝ} {k : ℕ} {α : ℝ}
    (hcert : ParetoIidOrderStatisticEventualFOCCertificate likelihood k α)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t) :
    PairwiseScaledEventualSublinearFOCCertificate
      (fun _ => paretoIidOrderStatisticConsumptionModel likelihood k α)
      (fun t : ItemType T => likelihood t ^ (α / (α - 1)))
      (gammaLikelihoodProfile likelihood (α / (α - 1))) := by
  refine
    PairwiseScaledEventualSublinearFOCCertificate.of_count_gap
      (Mseq := fun _ => paretoIidOrderStatisticConsumptionModel likelihood k α)
      (weight := fun t : ItemType T => likelihood t ^ (α / (α - 1)))
      (G := gammaLikelihoodProfile likelihood (α / (α - 1)))
      ?_ ?_ hcert.base_error hcert.base_error_nonneg
      hcert.base_error_tends_to_zero hcert.floor
      hcert.count_floor_eventually hcert.large_gap_count
  · intro t
    exact Real.rpow_pos_of_pos (hlike_pos t) (α / (α - 1))
  · intro t
    have hnorm_pos :
        0 < ∑ i : ItemType T, likelihood i ^ (α / (α - 1)) :=
      Finset.sum_pos
        (fun i _ => Real.rpow_pos_of_pos
          (hlike_pos i) (α / (α - 1)))
        Finset.univ_nonempty
    exact gammaLikelihoodProfile_targetShare_eq likelihood
      (α / (α - 1)) t (ne_of_gt hnorm_pos)

end ParetoIidOrderStatisticEventualFOCCertificate

/-- A number in `(0,1)` is not an integer pole of `Gamma` after negation. -/
private theorem gamma_neg_delta_ne_zero_of_pos_lt_one
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1) :
    Real.Gamma (-δ) ≠ 0 := AppliedModelingLib.Math.gamma_neg_delta_ne_zero_of_pos_lt_one hδ_pos hδ_lt_one

/--
Finite gamma recurrence product for a shift `-δ` with `0 < δ < 1`.

This is the algebraic identity that rewrites Euler's `GammaSeq (-δ)` into the
gamma-ratio form needed for Pareto order-statistic tails.
-/
theorem gamma_neg_delta_prod_range_eq_gamma_div
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1) (q : ℕ) :
    (∏ j ∈ Finset.range (q + 1), (-δ + (j : ℝ))) =
      Real.Gamma ((q : ℝ) + 1 - δ) / Real.Gamma (-δ) := AppliedModelingLib.Math.gamma_neg_delta_prod_range_eq_gamma_div hδ_pos hδ_lt_one q

/--
Gamma-ratio asymptotic for the Pareto rank calculation:
`Γ(q+1) / Γ(q+1-δ) ~ q^δ`.
-/
theorem gamma_ratio_nat_add_one_sub_asymptoticEquivalent
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun q : ℕ =>
        Real.Gamma ((q : ℝ) + 1) / Real.Gamma ((q : ℝ) + 1 - δ))
      (fun q : ℕ => (q : ℝ) ^ δ) := AppliedModelingLib.Math.gamma_ratio_nat_add_one_sub_asymptoticEquivalent hδ_pos hδ_lt_one

/--
Finite-difference bridge for the Pareto order-statistic rank calculation.

For a fixed rank, the Pareto source proof often first identifies the value
asymptotic `μ (q-r) q ~ C q^(1/α)` and then proves the explicit scaled-drop
limit.  This theorem converts those two source obligations into the marginal
limit expected by `ParetoOrderStatisticScaledMarginalCertificate`.
-/
theorem pareto_rank_scaled_limit_of_value_asymptotic_and_scaled_drop
    {μ : ℕ → ℕ → ℝ} {α C : ℝ} {r : ℕ}
    (hα : 1 < α) (hC : 0 < C)
    (hvalue :
      AppliedModelingLib.Math.AsymptoticEquivalent
        (fun q : ℕ => μ (q - r) q)
        (fun q : ℕ => C * ((q : ℝ) ^ (1 / α))))
    (hdrop :
      Filter.Tendsto
        (fun q : ℕ =>
          (((q + 1 : ℕ) : ℝ) *
            ((μ (q + 1 - r) (q + 1) - μ (q - r) q) /
              μ (q - r) q)))
        Filter.atTop (nhds (1 / α))) :
    Filter.Tendsto
      (fun q : ℕ =>
        (μ (q + 1 - r) (q + 1) - μ (q - r) q) /
          paretoPowerMarginalScale α q)
      Filter.atTop (nhds (C / α)) := by
  have hα_pos : 0 < α := lt_trans zero_lt_one hα
  have hα_ne : α ≠ 0 := ne_of_gt hα_pos
  have hbase :
      Filter.Tendsto
        (fun q : ℕ =>
          (μ (q + 1 - r) (q + 1) - μ (q - r) q) /
            (((q + 1 : ℕ) : ℝ) ^ (-(1 - 1 / α))))
        Filter.atTop (nhds (C * (1 / α))) :=
    AppliedModelingLib.Math.scaled_difference_limit_of_value_asymptotic_and_scaled_drop
      (value := fun q : ℕ => μ (q - r) q)
      (δ := 1 / α) (C := C) hC.ne' hvalue hdrop
  have htarget : C * (1 / α) = C / α := by ring
  rw [← htarget]
  refine Filter.Tendsto.congr' ?_ hbase
  filter_upwards with q
  have hscale_eq :
      (((q + 1 : ℕ) : ℝ) ^ (-(1 - 1 / α))) =
        paretoPowerMarginalScale α q := by
    unfold paretoPowerMarginalScale paretoMarginalExponent
    congr 1
    field_simp [hα_ne]
  rw [hscale_eq]

/--
Fixed-rank coefficient in the Pareto order-statistic marginal asymptotic.

The remaining Lemma D.4 probability calculation should prove that the rank
`r` contribution, scaled by `paretoPowerMarginalScale α`, tends to this value.
-/
noncomputable def paretoRankMarginalCoeff (α : ℝ) (r : ℕ) : ℝ :=
  (Real.Gamma ((r : ℝ) + 1 - 1 / α) /
      Real.Gamma ((r : ℝ) + 1)) / α

theorem paretoRankMarginalCoeff_pos {α : ℝ} (hα : 1 < α) (r : ℕ) :
    0 < paretoRankMarginalCoeff α r := by
  have hα_pos : 0 < α := lt_trans zero_lt_one hα
  have hinv_lt_one : 1 / α < 1 := by
    rw [div_lt_one hα_pos]
    exact hα
  have hnum_arg_pos : 0 < (r : ℝ) + 1 - 1 / α := by
    have hr_nonneg : 0 ≤ (r : ℝ) := by positivity
    linarith
  have hden_arg_pos : 0 < (r : ℝ) + 1 := by positivity
  unfold paretoRankMarginalCoeff
  exact div_pos
    (div_pos
      (Real.Gamma_pos_of_pos hnum_arg_pos)
      (Real.Gamma_pos_of_pos hden_arg_pos))
    hα_pos

/-- Fixed-rank value coefficient before taking the marginal finite difference. -/
noncomputable def paretoRankValueCoeff (α : ℝ) (r : ℕ) : ℝ := Real.Gamma ((r : ℝ) + 1 - 1 / α) / Real.Gamma ((r : ℝ) + 1)

theorem paretoRankValueCoeff_pos {α : ℝ} (hα : 1 < α) (r : ℕ) :
    0 < paretoRankValueCoeff α r := by
  have hα_pos : 0 < α := lt_trans zero_lt_one hα
  have hinv_lt_one : 1 / α < 1 := by
    rw [div_lt_one hα_pos]
    exact hα
  have hnum_arg_pos : 0 < (r : ℝ) + 1 - 1 / α := by
    have hr_nonneg : 0 ≤ (r : ℝ) := by positivity
    linarith
  have hden_arg_pos : 0 < (r : ℝ) + 1 := by positivity
  unfold paretoRankValueCoeff
  exact div_pos
    (Real.Gamma_pos_of_pos hnum_arg_pos)
    (Real.Gamma_pos_of_pos hden_arg_pos)

theorem paretoRankMarginalCoeff_eq_valueCoeff_div
    (α : ℝ) (r : ℕ) :
    paretoRankMarginalCoeff α r = paretoRankValueCoeff α r / α := by
  rfl

/-- Common `q`-dependent factor in all fixed-rank Pareto forward marginals. -/
noncomputable def paretoCommonMarginalFactor (α : ℝ) (q : ℕ) : ℝ :=
  Real.Gamma ((q : ℝ) + 1) / Real.Gamma ((q : ℝ) + 2 - 1 / α)

theorem paretoCommonMarginal_den_eq
    {α : ℝ} (hα : 1 < α) (q : ℕ) :
    (q : ℝ) + 2 - 1 / α =
      ((q : ℝ) + 1) + paretoMarginalExponent α := by
  have hα_ne : α ≠ 0 := ne_of_gt (lt_trans zero_lt_one hα)
  unfold paretoMarginalExponent
  field_simp [hα_ne]
  ring

theorem paretoCommonMarginalFactor_pos
    {α : ℝ} (hα : 1 < α) (q : ℕ) :
    0 < paretoCommonMarginalFactor α q := by
  have hα_pos : 0 < α := lt_trans zero_lt_one hα
  have hden_pos : 0 < (q : ℝ) + 2 - 1 / α := by
    have hδ_lt_one : 1 / α < 1 := by
      rw [div_lt_one hα_pos]
      exact hα
    have hq_nonneg : 0 ≤ (q : ℝ) := by positivity
    linarith
  unfold paretoCommonMarginalFactor
  exact div_pos (Real.Gamma_pos_of_pos (by positivity))
    (Real.Gamma_pos_of_pos hden_pos)

/-- Wendel lower bound for the common Pareto marginal factor. -/
theorem paretoCommonMarginalFactor_rpow_neg_le
    {α : ℝ} (hα : 1 < α) (q : ℕ) :
    (((q + 1 : ℕ) : ℝ) ^ (-(paretoMarginalExponent α))) ≤
      paretoCommonMarginalFactor α q := by
  let x : ℝ := ((q + 1 : ℕ) : ℝ)
  let η : ℝ := paretoMarginalExponent α
  have hη_pos : 0 < η := by
    dsimp [η]
    exact paretoMarginalExponent_pos hα
  have hη_lt_one : η < 1 := by
    have hα_pos : 0 < α := lt_trans zero_lt_one hα
    dsimp [η, paretoMarginalExponent]
    rw [div_lt_one hα_pos]
    linarith
  have hx_pos : 0 < x := by dsimp [x]; positivity
  have hden_eq : (q : ℝ) + 2 - 1 / α = x + η := by
    dsimp [x, η]
    simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm]
      using paretoCommonMarginal_den_eq hα q
  have hΓx_pos : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx_pos
  have hΓxη_pos : 0 < Real.Gamma (x + η) :=
    Real.Gamma_pos_of_pos (add_pos hx_pos hη_pos)
  have hratio_pos : 0 < Real.Gamma (x + η) / Real.Gamma x :=
    div_pos hΓxη_pos hΓx_pos
  have hpow_pos : 0 < x ^ η := Real.rpow_pos_of_pos hx_pos η
  have hupper :
      Real.Gamma (x + η) / Real.Gamma x ≤ x ^ η :=
    AppliedModelingLib.Math.gamma_add_ratio_le_rpow hx_pos hη_pos hη_lt_one
  have hinv := one_div_le_one_div_of_le hratio_pos hupper
  calc
    (((q + 1 : ℕ) : ℝ) ^ (-(paretoMarginalExponent α)))
        = 1 / x ^ η := by
            dsimp [x, η]
            rw [Real.rpow_neg (by positivity : 0 ≤ (((q + 1 : ℕ) : ℝ)))]
            rw [one_div]
    _ ≤ 1 / (Real.Gamma (x + η) / Real.Gamma x) := hinv
    _ = Real.Gamma x / Real.Gamma (x + η) := by
            field_simp [hΓx_pos.ne', hΓxη_pos.ne']
    _ = paretoCommonMarginalFactor α q := by
            rw [← hden_eq]
            simp [paretoCommonMarginalFactor, x]

/-- Wendel upper bound for the common Pareto marginal factor with one-count shift. -/
theorem paretoCommonMarginalFactor_le_pred_rpow_neg
    {α : ℝ} (hα : 1 < α) {q : ℕ} (hq : 0 < q) :
    paretoCommonMarginalFactor α q ≤
      ((q : ℝ) ^ (-(paretoMarginalExponent α))) := by
  let x : ℝ := ((q + 1 : ℕ) : ℝ)
  let η : ℝ := paretoMarginalExponent α
  have hη_pos : 0 < η := by
    dsimp [η]
    exact paretoMarginalExponent_pos hα
  have hη_lt_one : η < 1 := by
    have hα_pos : 0 < α := lt_trans zero_lt_one hα
    dsimp [η, paretoMarginalExponent]
    rw [div_lt_one hα_pos]
    linarith
  have hx_gt_one : 1 < x := by
    dsimp [x]
    exact_mod_cast Nat.succ_lt_succ hq
  have hden_eq : (q : ℝ) + 2 - 1 / α = x + η := by
    dsimp [x, η]
    simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm]
      using paretoCommonMarginal_den_eq hα q
  have hbound :
      Real.Gamma x / Real.Gamma (x + η) ≤ (x - 1) ^ (-η) :=
    AppliedModelingLib.Math.gamma_div_gamma_add_le_pred_rpow_neg
      hx_gt_one hη_pos hη_lt_one
  calc
    paretoCommonMarginalFactor α q
        = Real.Gamma x / Real.Gamma (x + η) := by
            rw [← hden_eq]
            simp [paretoCommonMarginalFactor, x]
    _ ≤ (x - 1) ^ (-η) := hbound
    _ = ((q : ℝ) ^ (-(paretoMarginalExponent α))) := by
            dsimp [x, η]
            have hcast : (((q + 1 : ℕ) : ℝ) - 1) = (q : ℝ) := by
              norm_num
            rw [hcast]

/--
Exact fixed-rank gamma-ratio sequence cited in Lemma D.4 before connecting it
to a concrete Pareto order-statistic law.
-/
noncomputable def paretoRankGammaRatioMean (α : ℝ) (r q : ℕ) : ℝ :=
  paretoRankValueCoeff α r *
    (Real.Gamma ((q : ℝ) + 1) / Real.Gamma ((q : ℝ) + 1 - 1 / α))

/--
Bottom-indexed Pareto order-statistic mean sequence obtained from the
gamma-ratio formula cited in the source proof of Lemma D.4.

For valid ranks, `rank = q - r` means this is the expected `rank`-th smallest
order statistic among `q` draws, with fixed distance `r` from the top.  The
definition is total on natural-number indices so it can be passed directly to
`TopKValueOracle.ofOrderStatisticMean`.
-/
noncomputable def paretoCitedOrderStatisticMean (α : ℝ)
    (rank sampleSize : ℕ) : ℝ :=
  paretoRankGammaRatioMean α (sampleSize - rank) sampleSize

/--
The exact gamma-ratio rank sequence has the fixed-rank value asymptotic cited
by Lemma D.4.
-/
theorem paretoRankGammaRatioMean_value_asymptoticEquivalent
    {α : ℝ} (hα : 1 < α) (r : ℕ) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun q : ℕ => paretoRankGammaRatioMean α r q)
      (fun q : ℕ => paretoRankValueCoeff α r * ((q : ℝ) ^ (1 / α))) := by
  have hα_pos : 0 < α := lt_trans zero_lt_one hα
  have hδ_pos : 0 < 1 / α := one_div_pos.mpr hα_pos
  have hδ_lt_one : 1 / α < 1 := by
    rw [div_lt_one hα_pos]
    exact hα
  have hcoeff_ne : paretoRankValueCoeff α r ≠ 0 :=
    (paretoRankValueCoeff_pos hα r).ne'
  have hgamma :=
    gamma_ratio_nat_add_one_sub_asymptoticEquivalent hδ_pos hδ_lt_one
  rw [AppliedModelingLib.Math.AsymptoticEquivalent] at hgamma ⊢
  refine Filter.Tendsto.congr' ?_ hgamma
  filter_upwards [Filter.eventually_gt_atTop 0] with q hq
  have hq_pos : 0 < (q : ℝ) := by exact_mod_cast hq
  have hqpow_ne : (q : ℝ) ^ (1 / α) ≠ 0 :=
    (Real.rpow_pos_of_pos hq_pos (1 / α)).ne'
  unfold paretoRankGammaRatioMean
  field_simp [hcoeff_ne, hqpow_ne]

/-- Exact recurrence for the fixed-rank gamma-ratio sequence. -/
theorem paretoRankGammaRatioMean_succ_div_self
    {α : ℝ} (hα : 1 < α) (r q : ℕ) :
    paretoRankGammaRatioMean α r (q + 1) /
        paretoRankGammaRatioMean α r q =
      (((q + 1 : ℕ) : ℝ) / ((q : ℝ) + 1 - 1 / α)) := by
  have hα_pos : 0 < α := lt_trans zero_lt_one hα
  have hδ_lt_one : 1 / α < 1 := by
    rw [div_lt_one hα_pos]
    exact hα
  have hcoeff_ne : paretoRankValueCoeff α r ≠ 0 :=
    (paretoRankValueCoeff_pos hα r).ne'
  have hq1_pos : 0 < ((q : ℝ) + 1) := by positivity
  have hq1_ne : ((q : ℝ) + 1) ≠ 0 := ne_of_gt hq1_pos
  have harg_pos : 0 < (q : ℝ) + 1 - 1 / α := by
    have hq_nonneg : 0 ≤ (q : ℝ) := by positivity
    linarith
  have harg_ne : (q : ℝ) + 1 - 1 / α ≠ 0 := ne_of_gt harg_pos
  have hgamma_q1_ne : Real.Gamma ((q : ℝ) + 1) ≠ 0 :=
    (Real.Gamma_pos_of_pos hq1_pos).ne'
  have hgamma_arg_ne : Real.Gamma ((q : ℝ) + 1 - 1 / α) ≠ 0 :=
    (Real.Gamma_pos_of_pos harg_pos).ne'
  have harg_succ_pos : 0 < ((q + 1 : ℕ) : ℝ) + 1 - 1 / α := by
    have hq_succ_nonneg : 0 ≤ (((q + 1 : ℕ) : ℝ)) := by positivity
    linarith
  have hgamma_arg_succ_ne :
      Real.Gamma (((q + 1 : ℕ) : ℝ) + 1 - 1 / α) ≠ 0 :=
    (Real.Gamma_pos_of_pos harg_succ_pos).ne'
  have hgamma_num_succ :
      Real.Gamma (((q + 1 : ℕ) : ℝ) + 1) =
        (((q + 1 : ℕ) : ℝ) * Real.Gamma (((q + 1 : ℕ) : ℝ))) :=
    Real.Gamma_add_one (by positivity : (((q + 1 : ℕ) : ℝ)) ≠ 0)
  have hgamma_den_succ :
      Real.Gamma (((q + 1 : ℕ) : ℝ) + 1 - 1 / α) =
        (((q : ℝ) + 1 - 1 / α) *
          Real.Gamma ((q : ℝ) + 1 - 1 / α)) := by
    rw [show (((q + 1 : ℕ) : ℝ) + 1 - 1 / α) =
          ((q : ℝ) + 1 - 1 / α) + 1 by
        rw [Nat.cast_add, Nat.cast_one]
        ring]
    exact Real.Gamma_add_one harg_ne
  unfold paretoRankGammaRatioMean
  rw [hgamma_num_succ, hgamma_den_succ]
  rw [show (((q + 1 : ℕ) : ℝ)) = (q : ℝ) + 1 by
    rw [Nat.cast_add, Nat.cast_one]]
  field_simp [hcoeff_ne, hq1_ne, harg_ne, hgamma_q1_ne,
    hgamma_arg_ne, hgamma_arg_succ_ne]
  rw [show (((q : ℝ) + 1) * α - 1) / α =
      (q : ℝ) + 1 - 1 / α by
        field_simp [ne_of_gt hα_pos]]
  have halg_ne : ((q : ℝ) + 1) * α - 1 ≠ 0 := by
    intro hzero
    apply harg_ne
    field_simp [ne_of_gt hα_pos]
    linarith
  field_simp [hgamma_arg_ne, halg_ne]
  rw [show (((q : ℝ) + 1) * α - 1) / α =
      (q : ℝ) + 1 - 1 / α by
        field_simp [ne_of_gt hα_pos]]
  exact div_self hgamma_arg_ne

theorem paretoRankGammaRatioMean_pos
    {α : ℝ} (hα : 1 < α) (r q : ℕ) :
    0 < paretoRankGammaRatioMean α r q := by
  have hα_pos : 0 < α := lt_trans zero_lt_one hα
  have hδ_lt_one : 1 / α < 1 := by
    rw [div_lt_one hα_pos]
    exact hα
  have hnum_pos : 0 < (q : ℝ) + 1 := by positivity
  have hden_pos : 0 < (q : ℝ) + 1 - 1 / α := by
    have hq_nonneg : 0 ≤ (q : ℝ) := by positivity
    linarith
  unfold paretoRankGammaRatioMean
  exact mul_pos (paretoRankValueCoeff_pos hα r)
    (div_pos (Real.Gamma_pos_of_pos hnum_pos)
      (Real.Gamma_pos_of_pos hden_pos))

/--
Exact first difference for the fixed-rank gamma-ratio sequence.  It is the
recurrence form used to prove the strict concavity/diminishing-marginal
checkpoint cited in Lemma D.4.
-/
theorem paretoRankGammaRatioMean_forward_marginal
    {α : ℝ} (hα : 1 < α) (r q : ℕ) :
    paretoRankGammaRatioMean α r (q + 1) -
        paretoRankGammaRatioMean α r q =
      paretoRankGammaRatioMean α r q *
        ((1 / α) / ((q : ℝ) + 1 - 1 / α)) := by
  have hα_pos : 0 < α := lt_trans zero_lt_one hα
  have hδ_lt_one : 1 / α < 1 := by
    rw [div_lt_one hα_pos]
    exact hα
  have hden_pos : 0 < (q : ℝ) + 1 - 1 / α := by
    have hq_nonneg : 0 ≤ (q : ℝ) := by positivity
    linarith
  have hden_ne : (q : ℝ) + 1 - 1 / α ≠ 0 := ne_of_gt hden_pos
  have hmean_ne : paretoRankGammaRatioMean α r q ≠ 0 :=
    (paretoRankGammaRatioMean_pos hα r q).ne'
  have hrec := paretoRankGammaRatioMean_succ_div_self hα r q
  have hsucc :
      paretoRankGammaRatioMean α r (q + 1) =
        (((q + 1 : ℕ) : ℝ) / ((q : ℝ) + 1 - 1 / α)) *
          paretoRankGammaRatioMean α r q :=
    (div_eq_iff hmean_ne).1 hrec
  rw [hsucc]
  have halg_ne : ((q : ℝ) + 1) * α - 1 ≠ 0 := by
    intro hzero
    apply hden_ne
    field_simp [ne_of_gt hα_pos]
    linarith
  field_simp [hden_ne, ne_of_gt hα_pos, halg_ne]
  rw [Nat.cast_add, Nat.cast_one]
  ring

/--
Every fixed-rank Pareto gamma-ratio marginal is a positive rank coefficient
times the same common `q`-dependent gamma factor.
-/
theorem paretoRankGammaRatioMean_forward_marginal_eq_coeff_mul_common
    {α : ℝ} (hα : 1 < α) (r q : ℕ) :
    paretoRankGammaRatioMean α r (q + 1) -
        paretoRankGammaRatioMean α r q =
      paretoRankMarginalCoeff α r * paretoCommonMarginalFactor α q := by
  have hα_pos : 0 < α := lt_trans zero_lt_one hα
  have hα_ne : α ≠ 0 := ne_of_gt hα_pos
  have hden_pos : 0 < (q : ℝ) + 1 - 1 / α := by
    have hδ_lt_one : 1 / α < 1 := by
      rw [div_lt_one hα_pos]
      exact hα
    have hq_nonneg : 0 ≤ (q : ℝ) := by positivity
    linarith
  have hden_ne : (q : ℝ) + 1 - 1 / α ≠ 0 := ne_of_gt hden_pos
  have hgamma_den_ne : Real.Gamma ((q : ℝ) + 1 - 1 / α) ≠ 0 :=
    (Real.Gamma_pos_of_pos hden_pos).ne'
  have hgamma_succ :
      Real.Gamma ((q : ℝ) + 2 - 1 / α) =
        ((q : ℝ) + 1 - 1 / α) *
          Real.Gamma ((q : ℝ) + 1 - 1 / α) := by
    rw [show (q : ℝ) + 2 - 1 / α =
        ((q : ℝ) + 1 - 1 / α) + 1 by ring]
    exact Real.Gamma_add_one hden_ne
  rw [paretoRankGammaRatioMean_forward_marginal hα r q]
  unfold paretoRankGammaRatioMean paretoRankMarginalCoeff
    paretoRankValueCoeff paretoCommonMarginalFactor
  rw [hgamma_succ]
  field_simp [hα_ne, hden_ne, hgamma_den_ne]

/-- The exact fixed-rank Pareto gamma-ratio sequence has positive marginals. -/
theorem paretoRankGammaRatioMean_forward_marginal_pos
    {α : ℝ} (hα : 1 < α) (r q : ℕ) :
    0 <
      paretoRankGammaRatioMean α r (q + 1) -
        paretoRankGammaRatioMean α r q := by
  rw [paretoRankGammaRatioMean_forward_marginal hα r q]
  have hα_pos : 0 < α := lt_trans zero_lt_one hα
  have hδ_pos : 0 < 1 / α := one_div_pos.mpr hα_pos
  have hden_pos : 0 < (q : ℝ) + 1 - 1 / α := by
    have hq_nonneg : 0 ≤ (q : ℝ) := by positivity
    have hδ_lt_one : 1 / α < 1 := by
      rw [div_lt_one hα_pos]
      exact hα
    linarith
  exact mul_pos (paretoRankGammaRatioMean_pos hα r q)
    (div_pos hδ_pos hden_pos)

/--
The fixed-rank gamma-ratio sequence has strictly decreasing first
differences.  This closes the cited-sequence version of the paper's
strict-concavity/diminishing-marginal checkpoint; the concrete iid Pareto source
identification later transfers the same fact to the actual order-statistic
means.
-/
theorem paretoRankGammaRatioMean_forward_marginal_strict_antitone
    {α : ℝ} (hα : 1 < α) (r q : ℕ) :
    paretoRankGammaRatioMean α r (q + 2) -
        paretoRankGammaRatioMean α r (q + 1) <
      paretoRankGammaRatioMean α r (q + 1) -
        paretoRankGammaRatioMean α r q := by
  have hα_pos : 0 < α := lt_trans zero_lt_one hα
  have hδ_pos : 0 < 1 / α := one_div_pos.mpr hα_pos
  have hδ_lt_one : 1 / α < 1 := by
    rw [div_lt_one hα_pos]
    exact hα
  have hden0_pos : 0 < (q : ℝ) + 1 - 1 / α := by
    have hq_nonneg : 0 ≤ (q : ℝ) := by positivity
    linarith
  have hden1_pos : 0 < (q : ℝ) + 2 - 1 / α := by
    have hq_nonneg : 0 ≤ (q : ℝ) := by positivity
    linarith
  have hden0_ne : (q : ℝ) + 1 - 1 / α ≠ 0 := ne_of_gt hden0_pos
  have hden1_ne : (q : ℝ) + 2 - 1 / α ≠ 0 := ne_of_gt hden1_pos
  have hmean_pos : 0 < paretoRankGammaRatioMean α r q :=
    paretoRankGammaRatioMean_pos hα r q
  have hmean_ne : paretoRankGammaRatioMean α r q ≠ 0 := hmean_pos.ne'
  have hrec := paretoRankGammaRatioMean_succ_div_self hα r q
  have hsucc :
      paretoRankGammaRatioMean α r (q + 1) =
        (((q + 1 : ℕ) : ℝ) / ((q : ℝ) + 1 - 1 / α)) *
          paretoRankGammaRatioMean α r q :=
    (div_eq_iff hmean_ne).1 hrec
  rw [paretoRankGammaRatioMean_forward_marginal hα r (q + 1),
    paretoRankGammaRatioMean_forward_marginal hα r q]
  rw [hsucc]
  have hbase_pos :
      0 <
        paretoRankGammaRatioMean α r q *
          ((1 / α) / ((q : ℝ) + 1 - 1 / α)) :=
    mul_pos hmean_pos (div_pos hδ_pos hden0_pos)
  have hfactor_lt_one :
      (((q + 1 : ℕ) : ℝ) / ((q : ℝ) + 2 - 1 / α)) < 1 := by
    rw [div_lt_one hden1_pos]
    rw [Nat.cast_add, Nat.cast_one]
    linarith
  calc
    ((((q + 1 : ℕ) : ℝ) / ((q : ℝ) + 1 - 1 / α)) *
          paretoRankGammaRatioMean α r q) *
        ((1 / α) / (((q + 1 : ℕ) : ℝ) + 1 - 1 / α))
        =
      (paretoRankGammaRatioMean α r q *
          ((1 / α) / ((q : ℝ) + 1 - 1 / α))) *
        (((q + 1 : ℕ) : ℝ) / ((q : ℝ) + 2 - 1 / α)) := by
          rw [Nat.cast_add, Nat.cast_one]
          field_simp [hden0_ne, hden1_ne]
          ring
    _ <
      (paretoRankGammaRatioMean α r q *
          ((1 / α) / ((q : ℝ) + 1 - 1 / α))) * 1 :=
        mul_lt_mul_of_pos_left hfactor_lt_one hbase_pos
    _ =
      paretoRankGammaRatioMean α r q *
        ((1 / α) / ((q : ℝ) + 1 - 1 / α)) := by ring

/-- The exact gamma-ratio rank sequence satisfies the Pareto scaled-drop law. -/
theorem paretoRankGammaRatioMean_scaled_drop
    {α : ℝ} (hα : 1 < α) (r : ℕ) :
    Filter.Tendsto
      (fun q : ℕ =>
        (((q + 1 : ℕ) : ℝ) *
          ((paretoRankGammaRatioMean α r (q + 1) -
              paretoRankGammaRatioMean α r q) /
            paretoRankGammaRatioMean α r q)))
      Filter.atTop (nhds (1 / α)) := by
  have hα_pos : 0 < α := lt_trans zero_lt_one hα
  have hratio :
      Filter.Tendsto
        (fun q : ℕ =>
          (((q + 1 : ℕ) : ℝ) / ((q : ℝ) + 1 - 1 / α)))
        Filter.atTop (nhds 1) := by
    have hbase :=
      tendsto_add_mul_div_add_mul_atTop_nhds
        (𝕜 := ℝ) (1 : ℝ) (1 - 1 / α) (1 : ℝ) (d := 1)
        (by norm_num : (1 : ℝ) ≠ 0)
    simpa [one_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
      Nat.cast_add, Nat.cast_one] using hbase
  have hlim :
      Filter.Tendsto
        (fun q : ℕ =>
          (1 / α) *
            (((q + 1 : ℕ) : ℝ) / ((q : ℝ) + 1 - 1 / α)))
        Filter.atTop (nhds (1 / α)) := by
    simpa using hratio.const_mul (1 / α)
  refine Filter.Tendsto.congr' ?_ hlim
  filter_upwards with q
  have hcoeff_ne : paretoRankValueCoeff α r ≠ 0 :=
    (paretoRankValueCoeff_pos hα r).ne'
  have hq1_pos : 0 < (q : ℝ) + 1 := by positivity
  have harg_pos : 0 < (q : ℝ) + 1 - 1 / α := by
    have hq_nonneg : 0 ≤ (q : ℝ) := by positivity
    have hδ_lt_one : 1 / α < 1 := by
      rw [div_lt_one hα_pos]
      exact hα
    linarith
  have harg_ne : (q : ℝ) + 1 - 1 / α ≠ 0 := ne_of_gt harg_pos
  have hmean_ne : paretoRankGammaRatioMean α r q ≠ 0 := by
    unfold paretoRankGammaRatioMean
    exact mul_ne_zero hcoeff_ne
      (div_ne_zero
        (Real.Gamma_pos_of_pos hq1_pos).ne'
        (Real.Gamma_pos_of_pos harg_pos).ne')
  have hrec := paretoRankGammaRatioMean_succ_div_self hα r q
  symm
  calc
    (((q + 1 : ℕ) : ℝ) *
        ((paretoRankGammaRatioMean α r (q + 1) -
            paretoRankGammaRatioMean α r q) /
          paretoRankGammaRatioMean α r q))
        =
      (((q + 1 : ℕ) : ℝ) *
        (paretoRankGammaRatioMean α r (q + 1) /
            paretoRankGammaRatioMean α r q - 1)) := by
          field_simp [hmean_ne]
    _ =
      (((q + 1 : ℕ) : ℝ) *
        ((((q + 1 : ℕ) : ℝ) / ((q : ℝ) + 1 - 1 / α)) - 1)) := by
          rw [hrec]
    _ =
      (1 / α) *
        (((q + 1 : ℕ) : ℝ) / ((q : ℝ) + 1 - 1 / α)) := by
          have halg_ne : -1 + α + α * (q : ℝ) ≠ 0 := by
            intro hzero
            apply harg_ne
            field_simp [ne_of_gt hα_pos]
            linarith
          have halg2_ne : ((q : ℝ) + 1) * α - 1 ≠ 0 := by
            intro hzero
            apply harg_ne
            field_simp [ne_of_gt hα_pos]
            linarith
          field_simp [harg_ne, ne_of_gt hα_pos, halg_ne]
          field_simp [halg2_ne]
          rw [Nat.cast_add, Nat.cast_one]
          ring

/--
The exact gamma-ratio rank sequence gives the canonical per-rank Pareto
scaled marginal limit.
-/
theorem paretoRankGammaRatioMean_scaled_limit
    {α : ℝ} (hα : 1 < α) (r : ℕ) :
    Filter.Tendsto
      (fun q : ℕ =>
        (paretoRankGammaRatioMean α r (q + 1) -
            paretoRankGammaRatioMean α r q) /
          paretoPowerMarginalScale α q)
      Filter.atTop (nhds (paretoRankMarginalCoeff α r)) := by
  have h :=
    pareto_rank_scaled_limit_of_value_asymptotic_and_scaled_drop
      (μ := fun _ q => paretoRankGammaRatioMean α r q)
      (α := α) (C := paretoRankValueCoeff α r) (r := r)
      hα (paretoRankValueCoeff_pos hα r)
      (paretoRankGammaRatioMean_value_asymptoticEquivalent hα r)
      (paretoRankGammaRatioMean_scaled_drop hα r)
  simpa [paretoRankMarginalCoeff, paretoRankValueCoeff] using h

/--
The bottom-indexed cited Pareto order-statistic mean has the canonical
fixed-rank scaled marginal limit.
-/
theorem paretoCitedOrderStatisticMean_fixed_rank_scaled_limit
    {α : ℝ} (hα : 1 < α) (r : ℕ) :
    Filter.Tendsto
      (fun q : ℕ =>
        (paretoCitedOrderStatisticMean α (q + 1 - r) (q + 1) -
            paretoCitedOrderStatisticMean α (q - r) q) /
          paretoPowerMarginalScale α q)
      Filter.atTop (nhds (paretoRankMarginalCoeff α r)) := by
  refine Filter.Tendsto.congr' ?_ (paretoRankGammaRatioMean_scaled_limit hα r)
  filter_upwards [Filter.eventually_atTop.2 ⟨r, fun q hq => hq⟩] with q hq
  have hsucc_sub : q + 1 - (q + 1 - r) = r := by omega
  have hsub_sub : q - (q - r) = r := by omega
  simp [paretoCitedOrderStatisticMean, hsucc_sub, hsub_sub]

/-- Fixed-distance-from-top specialization of the cited bottom-indexed mean. -/
theorem paretoCitedOrderStatisticMean_eq_rankGammaRatio_of_rank_from_top
    (α : ℝ) {r q : ℕ} (hrq : r ≤ q) :
    paretoCitedOrderStatisticMean α (q - r) q =
      paretoRankGammaRatioMean α r q := by
  have hsub_sub : q - (q - r) = r := by omega
  simp [paretoCitedOrderStatisticMean, hsub_sub]

/--
For the cited Pareto gamma-ratio source sequence, the top-`k` forward marginal
is the finite sum of the fixed-rank forward marginals once the sample size is
at least `k`.
-/
theorem paretoCitedOrderStatisticMean_topK_forward_marginal_eq_fin_sum
    (α : ℝ) {k q : ℕ} (hq : k ≤ q) :
    orderStatisticTopKSumFromMean (paretoCitedOrderStatisticMean α) k (q + 1) -
        orderStatisticTopKSumFromMean (paretoCitedOrderStatisticMean α) k q =
      ∑ i : Fin k,
        (paretoRankGammaRatioMean α i.val (q + 1) -
          paretoRankGammaRatioMean α i.val q) := by
  have hq_succ : k ≤ q + 1 := by omega
  rw [orderStatisticTopKSumFromMean_eq_fin_sum_of_le
      (paretoCitedOrderStatisticMean α) hq_succ,
    orderStatisticTopKSumFromMean_eq_fin_sum_of_le
      (paretoCitedOrderStatisticMean α) hq]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  have hiq : i.val ≤ q := by omega
  have hiq_succ : i.val ≤ q + 1 := by omega
  rw [paretoCitedOrderStatisticMean_eq_rankGammaRatio_of_rank_from_top
      α hiq_succ,
    paretoCitedOrderStatisticMean_eq_rankGammaRatio_of_rank_from_top
      α hiq]

/--
For valid sample counts, the cited Pareto top-`k` marginal is one positive
coefficient sum times the common gamma marginal factor.
-/
theorem paretoCitedOrderStatisticMean_topK_forward_marginal_eq_coeff_sum_mul_common
    {α : ℝ} (hα : 1 < α) {k q : ℕ} (hq : k ≤ q) :
    orderStatisticTopKSumFromMean (paretoCitedOrderStatisticMean α) k (q + 1) -
        orderStatisticTopKSumFromMean (paretoCitedOrderStatisticMean α) k q =
      (∑ i : Fin k, paretoRankMarginalCoeff α i.val) *
        paretoCommonMarginalFactor α q := by
  rw [paretoCitedOrderStatisticMean_topK_forward_marginal_eq_fin_sum α hq]
  calc
    ∑ i : Fin k,
        (paretoRankGammaRatioMean α i.val (q + 1) -
          paretoRankGammaRatioMean α i.val q)
        =
      ∑ i : Fin k,
        paretoRankMarginalCoeff α i.val *
          paretoCommonMarginalFactor α q := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            exact paretoRankGammaRatioMean_forward_marginal_eq_coeff_mul_common
              hα i.val q
    _ = (∑ i : Fin k, paretoRankMarginalCoeff α i.val) *
        paretoCommonMarginalFactor α q := by
          rw [Finset.sum_mul]

/--
The cited Pareto top-`k` gamma-ratio source sequence has strictly decreasing
top-`k` forward marginals, eventually in the sample size.  This is the
cited-sequence strict-concavity checkpoint for Lemma D.4.
-/
theorem paretoCitedOrderStatisticMean_topK_forward_marginal_strict_antitone_eventually
    {α : ℝ} (hα : 1 < α) {k : ℕ} (hk : 0 < k) :
    ∀ᶠ q in Filter.atTop,
      orderStatisticTopKSumFromMean (paretoCitedOrderStatisticMean α) k (q + 2) -
          orderStatisticTopKSumFromMean (paretoCitedOrderStatisticMean α) k (q + 1) <
        orderStatisticTopKSumFromMean (paretoCitedOrderStatisticMean α) k (q + 1) -
          orderStatisticTopKSumFromMean (paretoCitedOrderStatisticMean α) k q := by
  filter_upwards [Filter.eventually_atTop.2 ⟨k, fun q hq => hq⟩] with q hq
  have hq_succ : k ≤ q + 1 := by omega
  rw [paretoCitedOrderStatisticMean_topK_forward_marginal_eq_fin_sum
      α hq_succ,
    paretoCitedOrderStatisticMean_topK_forward_marginal_eq_fin_sum
      α hq]
  refine Finset.sum_lt_sum ?hle ?hlt
  · intro i _hi
    exact (paretoRankGammaRatioMean_forward_marginal_strict_antitone
      hα i.val q).le
  · exact ⟨⟨0, hk⟩, Finset.mem_univ _,
      paretoRankGammaRatioMean_forward_marginal_strict_antitone hα 0 q⟩

/-- The cited Pareto top-`k` gamma-ratio sequence has positive forward marginals. -/
theorem paretoCitedOrderStatisticMean_topK_forward_marginal_pos
    {α : ℝ} (hα : 1 < α) {k : ℕ} (hk : 0 < k) (q : ℕ) :
    0 <
      orderStatisticTopKSumFromMean (paretoCitedOrderStatisticMean α) k (q + 1) -
        orderStatisticTopKSumFromMean (paretoCitedOrderStatisticMean α) k q := by
  by_cases hkq : k ≤ q
  · rw [paretoCitedOrderStatisticMean_topK_forward_marginal_eq_fin_sum
      α hkq]
    refine Finset.sum_pos ?_ ?_
    · intro i _hi
      exact paretoRankGammaRatioMean_forward_marginal_pos hα i.val q
    · exact ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  · have hq_lt_k : q < k := Nat.lt_of_not_ge hkq
    have hq_le_k : q ≤ k := le_of_lt hq_lt_k
    have hq_succ_le_k : q + 1 ≤ k := Nat.succ_le_of_lt hq_lt_k
    let A : ℕ → ℝ := fun i =>
      paretoCitedOrderStatisticMean α (q + 1 - i) (q + 1)
    let B : ℕ → ℝ := fun i =>
      paretoCitedOrderStatisticMean α (q - i) q
    have hdecomp :
        orderStatisticTopKSumFromMean (paretoCitedOrderStatisticMean α) k (q + 1) -
            orderStatisticTopKSumFromMean (paretoCitedOrderStatisticMean α) k q =
          (∑ i ∈ Finset.range q, (A i - B i)) + A q := by
      rw [orderStatisticTopKSumFromMean_eq_bottomIndexed_sum,
        orderStatisticTopKSumFromMean_eq_bottomIndexed_sum]
      rw [min_eq_right hq_succ_le_k, min_eq_right hq_le_k]
      rw [Finset.sum_range_succ]
      change
        (∑ i ∈ Finset.range q, A i) + A q -
            (∑ i ∈ Finset.range q, B i) =
          (∑ i ∈ Finset.range q, (A i - B i)) + A q
      calc
        (∑ i ∈ Finset.range q, A i) + A q -
            (∑ i ∈ Finset.range q, B i)
            =
          (∑ i ∈ Finset.range q, A i -
            ∑ i ∈ Finset.range q, B i) + A q := by ring
        _ = (∑ i ∈ Finset.range q, (A i - B i)) + A q := by
          rw [Finset.sum_sub_distrib]
    have hsum_nonneg :
        0 ≤ ∑ i ∈ Finset.range q, (A i - B i) := by
      refine Finset.sum_nonneg ?_
      intro i hi
      have hiq : i < q := Finset.mem_range.1 hi
      have hiq_succ : i < q + 1 := Nat.lt_trans hiq (Nat.lt_succ_self q)
      have hAi :
          A i = paretoRankGammaRatioMean α i (q + 1) := by
        dsimp [A]
        rw [paretoCitedOrderStatisticMean_eq_rankGammaRatio_of_rank_from_top
          (α := α) (r := i) (q := q + 1) (by omega)]
      have hBi :
          B i = paretoRankGammaRatioMean α i q := by
        dsimp [B]
        rw [paretoCitedOrderStatisticMean_eq_rankGammaRatio_of_rank_from_top
          (α := α) (r := i) (q := q) (le_of_lt hiq)]
      rw [hAi, hBi]
      exact (paretoRankGammaRatioMean_forward_marginal_pos hα i q).le
    have hlast_pos : 0 < A q := by
      dsimp [A]
      rw [paretoCitedOrderStatisticMean_eq_rankGammaRatio_of_rank_from_top
        α (Nat.le_succ q)]
      exact paretoRankGammaRatioMean_pos hα q (q + 1)
    rw [hdecomp]
    exact add_pos_of_nonneg_of_pos hsum_nonneg hlast_pos

/--
Source-shaped identification boundary for actual Pareto sample laws.

For each fixed distance `r` from the top order statistic, the concrete
expected order-statistic mean sequence agrees eventually with the gamma-ratio
formula cited in Lemma D.4.  This is intentionally weaker than a global
equality because the reusable sample-order-statistic interface is total on
invalid ranks.
-/
structure ParetoCitedOrderStatisticSource
    (sampleMeasure : (a : ℕ) → MeasureTheory.Measure (Fin a → ℝ))
    (α : ℝ) : Prop where
  fixed_rank_eq :
    ∀ r : ℕ,
      ∀ᶠ q in Filter.atTop,
        expectedOrderStatisticMeanSeq sampleMeasure (q - r) q =
          paretoRankGammaRatioMean α r q

namespace ParetoCitedOrderStatisticSource

/--
A concrete source identification with the cited gamma-ratio sequence supplies
the fixed-rank Pareto scaled marginal limit at the global `μ_D` boundary.
-/
theorem fixed_rank_scaled_limit
    {sampleMeasure : (a : ℕ) → MeasureTheory.Measure (Fin a → ℝ)}
    {α : ℝ} (hα : 1 < α)
    (C : ParetoCitedOrderStatisticSource sampleMeasure α) (r : ℕ) :
    Filter.Tendsto
      (fun q : ℕ =>
        (expectedOrderStatisticMeanSeq sampleMeasure (q + 1 - r) (q + 1) -
            expectedOrderStatisticMeanSeq sampleMeasure (q - r) q) /
          paretoPowerMarginalScale α q)
      Filter.atTop (nhds (paretoRankMarginalCoeff α r)) := by
  refine Filter.Tendsto.congr' ?_ (paretoRankGammaRatioMean_scaled_limit hα r)
  have hsucc :
      ∀ᶠ q in Filter.atTop,
        expectedOrderStatisticMeanSeq sampleMeasure (q + 1 - r) (q + 1) =
          paretoRankGammaRatioMean α r (q + 1) := by
    rcases Filter.eventually_atTop.1 (C.fixed_rank_eq r) with ⟨N, hN⟩
    exact Filter.eventually_atTop.2
      ⟨N, fun q hq => hN (q + 1) (Nat.le_trans hq (Nat.le_succ q))⟩
  filter_upwards [hsucc, C.fixed_rank_eq r] with q hq_succ hq
  simp [hq_succ, hq]

/--
The source-identification package agrees eventually with the cited gamma-ratio
sequence at the aggregate top-`k` sum boundary.
-/
theorem topKSum_eq_cited_eventually
    {sampleMeasure : (a : ℕ) → MeasureTheory.Measure (Fin a → ℝ)}
    {α : ℝ}
    (C : ParetoCitedOrderStatisticSource sampleMeasure α) (k : ℕ) :
    ∀ᶠ q in Filter.atTop,
      orderStatisticTopKSumFromMean
          (expectedOrderStatisticMeanSeq sampleMeasure) k q =
        orderStatisticTopKSumFromMean (paretoCitedOrderStatisticMean α) k q := by
  classical
  have hfixed :
      ∀ᶠ q in Filter.atTop,
        ∀ i : Fin k,
          expectedOrderStatisticMeanSeq sampleMeasure (q - i.val) q =
            paretoRankGammaRatioMean α i.val q := by
    exact Filter.eventually_all.2 (fun i : Fin k => C.fixed_rank_eq i.val)
  filter_upwards [Filter.eventually_atTop.2 ⟨k, fun q hq => hq⟩, hfixed]
    with q hq hq_fixed
  rw [orderStatisticTopKSumFromMean_eq_fin_sum_of_le
      (expectedOrderStatisticMeanSeq sampleMeasure) hq,
    orderStatisticTopKSumFromMean_eq_fin_sum_of_le
      (paretoCitedOrderStatisticMean α) hq]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [hq_fixed i]
  rw [paretoCitedOrderStatisticMean_eq_rankGammaRatio_of_rank_from_top
      α (by omega : i.val ≤ q)]

/--
If an actual source law is identified with the cited gamma-ratio sequence, it
inherits the cited sequence's eventual strict top-`k` diminishing marginals.
-/
theorem topK_forward_marginal_strict_antitone_eventually
    {sampleMeasure : (a : ℕ) → MeasureTheory.Measure (Fin a → ℝ)}
    {α : ℝ} (hα : 1 < α) {k : ℕ} (hk : 0 < k)
    (C : ParetoCitedOrderStatisticSource sampleMeasure α) :
    ∀ᶠ q in Filter.atTop,
      orderStatisticTopKSumFromMean
          (expectedOrderStatisticMeanSeq sampleMeasure) k (q + 2) -
          orderStatisticTopKSumFromMean
            (expectedOrderStatisticMeanSeq sampleMeasure) k (q + 1) <
        orderStatisticTopKSumFromMean
            (expectedOrderStatisticMeanSeq sampleMeasure) k (q + 1) -
          orderStatisticTopKSumFromMean
            (expectedOrderStatisticMeanSeq sampleMeasure) k q := by
  have hcited :=
    paretoCitedOrderStatisticMean_topK_forward_marginal_strict_antitone_eventually
      hα hk
  have htop := C.topKSum_eq_cited_eventually k
  have htop_succ :
      ∀ᶠ q in Filter.atTop,
        orderStatisticTopKSumFromMean
            (expectedOrderStatisticMeanSeq sampleMeasure) k (q + 1) =
          orderStatisticTopKSumFromMean
            (paretoCitedOrderStatisticMean α) k (q + 1) := by
    rcases Filter.eventually_atTop.1 htop with ⟨N, hN⟩
    exact Filter.eventually_atTop.2
      ⟨N, fun q hq => hN (q + 1) (Nat.le_trans hq (Nat.le_succ q))⟩
  have htop_succ_succ :
      ∀ᶠ q in Filter.atTop,
        orderStatisticTopKSumFromMean
            (expectedOrderStatisticMeanSeq sampleMeasure) k (q + 2) =
          orderStatisticTopKSumFromMean
            (paretoCitedOrderStatisticMean α) k (q + 2) := by
    rcases Filter.eventually_atTop.1 htop with ⟨N, hN⟩
    exact Filter.eventually_atTop.2
      ⟨N, fun q hq =>
        hN (q + 2) (Nat.le_trans hq (Nat.le_add_right q 2))⟩
  filter_upwards [hcited, htop, htop_succ, htop_succ_succ] with
    q hstrict hq hq_succ hq_succ_succ
  simpa [hq, hq_succ, hq_succ_succ] using hstrict

end ParetoCitedOrderStatisticSource

/--
Concrete source identification for the scale-one iid Pareto law used in
Lemma D.4.

The reusable probability library proves the upper-order-statistic expectation
as the beta/gamma finite-sum closed form.  This theorem only changes indexing:
the paper's bottom-indexed rank `q - r` is the `r`-from-top statistic once
`q > r`.
-/
theorem paretoIidSampleMeasure_rank_eq_rankGammaRatio
    {α : ℝ} (hα : 1 < α) {q r : ℕ} (hrq : r < q) :
    expectedOrderStatisticMeanSeq (paretoIidSampleMeasure α) (q - r) q =
      paretoRankGammaRatioMean α r q := by
  calc
    expectedOrderStatisticMeanSeq (paretoIidSampleMeasure α) (q - r) q
        =
          AppliedModelingLib.Probability.expectedUpperOrderStatistic
            (paretoIidSampleMeasure α q) ⟨r, hrq⟩ := by
          simpa [expectedOrderStatisticMeanSeq] using
            AppliedModelingLib.Probability.expectedSampleOrderStatisticMean_eq_expectedUpperOrderStatistic_of_rank_from_top
              (μ := paretoIidSampleMeasure α q) (r := r) (a := q) hrq
    _ = paretoRankGammaRatioMean α r q := by
          simpa [paretoIidSampleMeasure, paretoRankGammaRatioMean,
            paretoRankValueCoeff] using
            AppliedModelingLib.Probability.Pareto.iidProductMeasure_one_expectedUpperOrderStatistic_eq_gamma_ratio
              (α := α) hα (q := q) (rankFromTop := ⟨r, hrq⟩)

theorem paretoIidSampleMeasure_fixed_rank_eq_rankGammaRatio_eventually
    {α : ℝ} (hα : 1 < α) (r : ℕ) :
    ∀ᶠ q in Filter.atTop,
      expectedOrderStatisticMeanSeq (paretoIidSampleMeasure α) (q - r) q =
        paretoRankGammaRatioMean α r q := by
  filter_upwards [Filter.eventually_atTop.2 ⟨r + 1, fun q hq => hq⟩] with q hq
  have hrq : r < q := by omega
  exact paretoIidSampleMeasure_rank_eq_rankGammaRatio hα hrq

/--
Concrete source package for the scale-one iid Pareto law.  This discharges the
previous cited-source assumption for the paper's Pareto order-statistic branch.
-/
theorem paretoIidSampleMeasure_citedOrderStatisticSource
    {α : ℝ} (hα : 1 < α) :
    ParetoCitedOrderStatisticSource (paretoIidSampleMeasure α) α where
  fixed_rank_eq := paretoIidSampleMeasure_fixed_rank_eq_rankGammaRatio_eventually hα

/--
The concrete iid Pareto top-`k` source sum agrees with the cited gamma-ratio
sum at every valid sample count.
-/
theorem paretoIidOrderStatisticTopKSum_eq_cited
    {α : ℝ} (hα : 1 < α) (k q : ℕ) :
    orderStatisticTopKSumFromMean (paretoIidOrderStatisticMeanSeq α) k q =
      orderStatisticTopKSumFromMean (paretoCitedOrderStatisticMean α) k q := by
  by_cases hq_zero : q = 0
  · simp [hq_zero]
  · rw [orderStatisticTopKSumFromMean_eq_bottomIndexed_sum,
      orderStatisticTopKSumFromMean_eq_bottomIndexed_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hi_lt_min : i < min k q := Finset.mem_range.1 hi
    have hiq : i < q := lt_of_lt_of_le hi_lt_min (min_le_right k q)
    rw [paretoIidOrderStatisticMeanSeq,
      paretoIidSampleMeasure_rank_eq_rankGammaRatio hα hiq]
    rw [paretoCitedOrderStatisticMean_eq_rankGammaRatio_of_rank_from_top
      α (le_of_lt hiq)]

/-- Concrete iid Pareto top-`k` marginals factor through the common gamma factor. -/
theorem paretoIidOrderStatisticTopK_forward_marginal_eq_coeff_sum_mul_common
    (T : ℕ) {k : ℕ} {α : ℝ}
    (hα : 1 < α) {q : ℕ} (hq : k ≤ q) (t : ItemType T) :
    (paretoIidOrderStatisticOracle T α).expectedTopSum k t (q + 1) -
        (paretoIidOrderStatisticOracle T α).expectedTopSum k t q =
      (∑ i : Fin k, paretoRankMarginalCoeff α i.val) *
        paretoCommonMarginalFactor α q := by
  have hq_succ :=
    paretoIidOrderStatisticTopKSum_eq_cited hα k (q + 1)
  have hq_eq :=
    paretoIidOrderStatisticTopKSum_eq_cited hα k q
  simpa [paretoIidOrderStatisticOracle, TopKValueOracle.ofOrderStatisticMean,
    hq_succ, hq_eq] using
    paretoCitedOrderStatisticMean_topK_forward_marginal_eq_coeff_sum_mul_common
      hα hq

theorem paretoIidOrderStatisticTopK_forward_marginal_le_power_bound
    (T : ℕ) {k : ℕ} {α : ℝ}
    (hα : 1 < α) {q : ℕ} (hq : k ≤ q) (hq_pos : 0 < q)
    (t : ItemType T) :
    (paretoIidOrderStatisticOracle T α).expectedTopSum k t (q + 1) -
        (paretoIidOrderStatisticOracle T α).expectedTopSum k t q ≤
      (∑ i : Fin k, paretoRankMarginalCoeff α i.val) *
        ((q : ℝ) ^ (-(paretoMarginalExponent α))) := by
  rw [paretoIidOrderStatisticTopK_forward_marginal_eq_coeff_sum_mul_common
    T hα hq t]
  have hcoeff_nonneg :
      0 ≤ ∑ i : Fin k, paretoRankMarginalCoeff α i.val :=
    Finset.sum_nonneg
      (fun i _hi => (paretoRankMarginalCoeff_pos hα i.val).le)
  exact mul_le_mul_of_nonneg_left
    (paretoCommonMarginalFactor_le_pred_rpow_neg hα hq_pos)
    hcoeff_nonneg

theorem paretoIidOrderStatisticTopK_power_bound_le_forward_marginal
    (T : ℕ) {k : ℕ} {α : ℝ}
    (hα : 1 < α) {q : ℕ} (hq : k ≤ q) (hk : 0 < k)
    (t : ItemType T) :
      (∑ i : Fin k, paretoRankMarginalCoeff α i.val) *
        ((((q + 1 : ℕ) : ℝ) ^ (-(paretoMarginalExponent α)))) ≤
    (paretoIidOrderStatisticOracle T α).expectedTopSum k t (q + 1) -
        (paretoIidOrderStatisticOracle T α).expectedTopSum k t q := by
  rw [paretoIidOrderStatisticTopK_forward_marginal_eq_coeff_sum_mul_common
    T hα hq t]
  have hcoeff_nonneg :
      0 ≤ ∑ i : Fin k, paretoRankMarginalCoeff α i.val :=
    Finset.sum_nonneg
      (fun i _hi => (paretoRankMarginalCoeff_pos hα i.val).le)
  exact mul_le_mul_of_nonneg_left
    (paretoCommonMarginalFactor_rpow_neg_le hα q)
    hcoeff_nonneg

theorem paretoIidOrderStatistic_weightedBackwardMarginal_le_power_bound
    {T : ℕ} (likelihood : ItemType T → ℝ) {k : ℕ} {α : ℝ}
    (hα : 1 < α) (hk : 0 < k)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    {q : ℕ} (hq : k < q) (t : ItemType T) :
    (paretoIidOrderStatisticConsumptionModel likelihood k α).weightedBackwardMarginal t q ≤
      likelihood t *
        ((∑ i : Fin k, paretoRankMarginalCoeff α i.val) *
          (((q - 1 : ℕ) : ℝ) ^ (-(paretoMarginalExponent α)))) := by
  have hq_pos : 0 < q := by omega
  have hq_pred_pos : 0 < q - 1 := by omega
  have hk_le_pred : k ≤ q - 1 := by omega
  have hbase :=
    paretoIidOrderStatisticTopK_forward_marginal_le_power_bound
      T hα hk_le_pred hq_pred_pos t
  have hdiff_le :
      (paretoIidOrderStatisticOracle T α).expectedTopSum k t q -
          (paretoIidOrderStatisticOracle T α).expectedTopSum k t (q - 1) ≤
        (∑ i : Fin k, paretoRankMarginalCoeff α i.val) *
          (((q - 1 : ℕ) : ℝ) ^ (-(paretoMarginalExponent α))) := by
    simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hq_pos)] using hbase
  unfold paretoIidOrderStatisticConsumptionModel
    ConsumptionModel.weightedBackwardMarginal TopKValueOracle.toConsumptionModel
  rw [dif_neg (Nat.ne_of_gt hq_pos)]
  exact mul_le_mul_of_nonneg_left hdiff_le (hlike_pos t).le

theorem paretoIidOrderStatistic_power_bound_le_weightedForwardMarginal
    {T : ℕ} (likelihood : ItemType T → ℝ) {k : ℕ} {α : ℝ}
    (hα : 1 < α) (hk : 0 < k)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    {q : ℕ} (hq : k ≤ q) (t : ItemType T) :
      likelihood t *
        ((∑ i : Fin k, paretoRankMarginalCoeff α i.val) *
          ((((q + 1 : ℕ) : ℝ) ^ (-(paretoMarginalExponent α))))) ≤
    (paretoIidOrderStatisticConsumptionModel likelihood k α).weightedForwardMarginal t q := by
  have hbase :=
    paretoIidOrderStatisticTopK_power_bound_le_forward_marginal
      T hα hq hk t
  unfold paretoIidOrderStatisticConsumptionModel
    ConsumptionModel.weightedForwardMarginal ConsumptionModel.marginalValue
    TopKValueOracle.toConsumptionModel AppliedModelingLib.Allocation.marginal
  exact mul_le_mul_of_nonneg_left hbase (hlike_pos t).le

/-- The concrete iid Pareto top-`k` source has positive forward marginals. -/
theorem paretoIidOrderStatisticTopK_forward_marginal_pos
    (T : ℕ) {k : ℕ} {α : ℝ}
    (hα : 1 < α) (hk : 0 < k) (t : ItemType T) (q : ℕ) :
    0 <
      (paretoIidOrderStatisticOracle T α).expectedTopSum k t (q + 1) -
        (paretoIidOrderStatisticOracle T α).expectedTopSum k t q := by
  have hq_succ :=
    paretoIidOrderStatisticTopKSum_eq_cited hα k (q + 1)
  have hq :=
    paretoIidOrderStatisticTopKSum_eq_cited hα k q
  simpa [paretoIidOrderStatisticOracle, TopKValueOracle.ofOrderStatisticMean,
    hq_succ, hq] using
    paretoCitedOrderStatisticMean_topK_forward_marginal_pos hα hk q

/--
Canonical-coefficient version of the fixed-rank Pareto finite-difference
bridge.  This is the form expected after the external Lemma D.4 gamma-ratio
calculation proves the fixed-rank value asymptotic.
-/
theorem pareto_rank_scaled_limit_of_canonical_value_asymptotic_and_scaled_drop
    {μ : ℕ → ℕ → ℝ} {α : ℝ} {r : ℕ}
    (hα : 1 < α)
    (hvalue :
      AppliedModelingLib.Math.AsymptoticEquivalent
        (fun q : ℕ => μ (q - r) q)
        (fun q : ℕ =>
          (Real.Gamma ((r : ℝ) + 1 - 1 / α) /
              Real.Gamma ((r : ℝ) + 1)) *
            ((q : ℝ) ^ (1 / α))))
    (hdrop :
      Filter.Tendsto
        (fun q : ℕ =>
          (((q + 1 : ℕ) : ℝ) *
            ((μ (q + 1 - r) (q + 1) - μ (q - r) q) /
              μ (q - r) q)))
        Filter.atTop (nhds (1 / α))) :
    Filter.Tendsto
      (fun q : ℕ =>
        (μ (q + 1 - r) (q + 1) - μ (q - r) q) /
          paretoPowerMarginalScale α q)
      Filter.atTop (nhds (paretoRankMarginalCoeff α r)) := by
  have hα_pos : 0 < α := lt_trans zero_lt_one hα
  have hinv_lt_one : 1 / α < 1 := by
    rw [div_lt_one hα_pos]
    exact hα
  have hnum_arg_pos : 0 < (r : ℝ) + 1 - 1 / α := by
    have hr_nonneg : 0 ≤ (r : ℝ) := by positivity
    linarith
  have hden_arg_pos : 0 < (r : ℝ) + 1 := by positivity
  have hcoeff_pos :
      0 <
        Real.Gamma ((r : ℝ) + 1 - 1 / α) /
          Real.Gamma ((r : ℝ) + 1) :=
    div_pos
      (Real.Gamma_pos_of_pos hnum_arg_pos)
      (Real.Gamma_pos_of_pos hden_arg_pos)
  simpa [paretoRankMarginalCoeff] using
    pareto_rank_scaled_limit_of_value_asymptotic_and_scaled_drop
      hα hcoeff_pos hvalue hdrop

theorem paretoRankMarginalCoeff_sum_pos {α : ℝ} {k : ℕ}
    (hα : 1 < α) (hk : 0 < k) :
    0 < ∑ i : Fin k, paretoRankMarginalCoeff α i.val := by
  haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  exact Finset.sum_pos
    (fun i _hi => paretoRankMarginalCoeff_pos hα i.val)
    Finset.univ_nonempty

/--
The exact Pareto power-marginal oracle satisfies the reusable scaled-marginal
certificate with unit type weights.
-/
noncomputable def paretoPowerMarginalScaledMarginalLimitCertificate
    (T : ℕ) (α : ℝ) :
    TopKScaledMarginalLimitCertificate
      (paretoPowerMarginalOracle T α) 1
      (paretoPowerMarginalScale α)
      (fun _ : ItemType T => (1 : ℝ)) where
  scale_pos_eventually := by
    filter_upwards with q
    exact paretoPowerMarginalScale_pos α q
  weight_pos := by
    intro t
    norm_num
  marginal_ratio_tendsto := by
    intro t
    convert (tendsto_const_nhds : Filter.Tendsto
      (fun q : ℕ => (1 : ℝ)) Filter.atTop (nhds 1)) using 1
    ext q
    have hpow_ne :
        (((q : ℝ) + 1) ^ (-(paretoMarginalExponent α))) ≠ 0 :=
      (Real.rpow_pos_of_pos (by positivity) _).ne'
    simp [AppliedModelingLib.Probability.TopKExpectationOracle.marginalTopK,
      topKExpectationOracleOfTopKValueOracle, paretoPowerMarginalOracle,
      TopKValueOracle.common, paretoPowerMarginalScale,
      paretoPowerMarginalValue_forward_marginal, hpow_ne]

/--
Source-side Pareto order-statistic asymptotic certificate.

Here `μ rank a` is the paper's bottom-indexed order-statistic mean
`μ_D(rank,a)`, and `limitCoeff` is the positive constant in the marginal form
of the Pareto top-`k` asymptotic.  The key source obligation is
`marginal_ratio_tendsto`: for fixed `k`, the discrete marginal of the paper's
Definition 3 top-`k` order-statistic sum is asymptotic to
`limitCoeff * q^-((α-1)/α)`.  Proving that field from Lemma D.4/equation (77)
is the remaining probability calculation.
-/
structure ParetoOrderStatisticScaledMarginalCertificate
    (μ : ℕ → ℕ → ℝ) (k : ℕ) (α limitCoeff : ℝ) : Prop where
  alpha_gt_one : 1 < α
  k_pos : 0 < k
  coeff_pos : 0 < limitCoeff
  marginal_ratio_tendsto :
    Filter.Tendsto
      (fun q : ℕ =>
        (orderStatisticTopKSumFromMean μ k (q + 1) -
            orderStatisticTopKSumFromMean μ k q) /
          (paretoPowerMarginalScale α q * limitCoeff))
      Filter.atTop (nhds 1)

namespace ParetoOrderStatisticScaledMarginalCertificate

def toOrderStatisticScaledMarginalCertificate
    {μ : ℕ → ℕ → ℝ} {k : ℕ} {α limitCoeff : ℝ}
    (C : ParetoOrderStatisticScaledMarginalCertificate μ k α limitCoeff) :
    AppliedModelingLib.Probability.OrderStatisticScaledMarginalCertificate μ k
      (paretoPowerMarginalScale α) limitCoeff where
  k_pos := C.k_pos
  coeff_pos := C.coeff_pos
  scale_pos_eventually := by
    filter_upwards with q
    exact paretoPowerMarginalScale_pos α q
  marginal_ratio_tendsto := C.marginal_ratio_tendsto

/--
Restate the source-side marginal field in the repository's standard
`AsymptoticEquivalent` vocabulary.  This is the exact form expected from a
Pareto order-statistic probability calculation.
-/
theorem marginal_asymptoticEquivalent
    {μ : ℕ → ℕ → ℝ} {k : ℕ} {α limitCoeff : ℝ}
    (C : ParetoOrderStatisticScaledMarginalCertificate μ k α limitCoeff) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun q : ℕ =>
        orderStatisticTopKSumFromMean μ k (q + 1) -
          orderStatisticTopKSumFromMean μ k q)
      (fun q : ℕ => paretoPowerMarginalScale α q * limitCoeff) :=
  C.toOrderStatisticScaledMarginalCertificate.marginal_asymptoticEquivalent

/--
Constructor from the source-style asymptotic-equivalence statement for the
Pareto top-`k` order-statistic marginal.
-/
def ofMarginalAsymptoticEquivalent
    {μ : ℕ → ℕ → ℝ} {k : ℕ} {α limitCoeff : ℝ}
    (hα : 1 < α) (hk : 0 < k) (hcoeff : 0 < limitCoeff)
    (hmargin :
      AppliedModelingLib.Math.AsymptoticEquivalent
        (fun q : ℕ =>
          orderStatisticTopKSumFromMean μ k (q + 1) -
            orderStatisticTopKSumFromMean μ k q)
        (fun q : ℕ => paretoPowerMarginalScale α q * limitCoeff)) :
    ParetoOrderStatisticScaledMarginalCertificate μ k α limitCoeff where
  alpha_gt_one := hα
  k_pos := hk
  coeff_pos := hcoeff
  marginal_ratio_tendsto := hmargin

/--
Variant of `ofMarginalAsymptoticEquivalent` for source calculations that write
the constant before the Pareto scale.
-/
def ofConstMulScaleAsymptoticEquivalent
    {μ : ℕ → ℕ → ℝ} {k : ℕ} {α limitCoeff : ℝ}
    (hα : 1 < α) (hk : 0 < k) (hcoeff : 0 < limitCoeff)
    (hmargin :
      AppliedModelingLib.Math.AsymptoticEquivalent
        (fun q : ℕ =>
          orderStatisticTopKSumFromMean μ k (q + 1) -
            orderStatisticTopKSumFromMean μ k q)
        (fun q : ℕ => limitCoeff * paretoPowerMarginalScale α q)) :
    ParetoOrderStatisticScaledMarginalCertificate μ k α limitCoeff := by
  let G : AppliedModelingLib.Probability.OrderStatisticScaledMarginalCertificate μ k
      (paretoPowerMarginalScale α) limitCoeff :=
    AppliedModelingLib.Probability.OrderStatisticScaledMarginalCertificate.ofConstMulScaleAsymptoticEquivalent
        hk hcoeff
        (by
          filter_upwards with q
          exact paretoPowerMarginalScale_pos α q)
        hmargin
  exact
    { alpha_gt_one := hα
      k_pos := G.k_pos
      coeff_pos := G.coeff_pos
      marginal_ratio_tendsto := G.marginal_ratio_tendsto }

/--
Constructor from the paper's fixed-`k`, per-rank marginal sum.

The Pareto calculation is usually stated rank-by-rank, for fixed `i < k`,
before summing over the top-`k` window.  This theorem exposes that
source-facing obligation: it is enough to prove the displayed finite `Fin k`
sum is asymptotic to the Pareto scale times the aggregate constant.
-/
def ofFiniteRankMarginalSumAsymptoticEquivalent
    {μ : ℕ → ℕ → ℝ} {k : ℕ} {α limitCoeff : ℝ}
    (hα : 1 < α) (hk : 0 < k) (hcoeff : 0 < limitCoeff)
    (hmargin :
      AppliedModelingLib.Math.AsymptoticEquivalent
        (fun q : ℕ =>
          ∑ i : Fin k,
            (μ (q + 1 - i.val) (q + 1) - μ (q - i.val) q))
        (fun q : ℕ => limitCoeff * paretoPowerMarginalScale α q)) :
    ParetoOrderStatisticScaledMarginalCertificate μ k α limitCoeff := by
  let G : AppliedModelingLib.Probability.OrderStatisticScaledMarginalCertificate μ k
      (paretoPowerMarginalScale α) limitCoeff :=
    AppliedModelingLib.Probability.OrderStatisticScaledMarginalCertificate.ofFiniteRankMarginalSumAsymptoticEquivalent
        hk hcoeff
        (by
          filter_upwards with q
          exact paretoPowerMarginalScale_pos α q)
        hmargin
  exact
    { alpha_gt_one := hα
      k_pos := G.k_pos
      coeff_pos := G.coeff_pos
      marginal_ratio_tendsto := G.marginal_ratio_tendsto }

/--
Constructor from fixed-rank scaled marginal limits.

This is the most direct handoff point for a Pareto beta/gamma calculation:
prove, for each fixed rank `i < k`, that its marginal divided by
`paretoPowerMarginalScale α` tends to `rankCoeff i`, and prove that those
constants sum to `limitCoeff`.
-/
def ofFiniteRankScaledLimits
    {μ : ℕ → ℕ → ℝ} {k : ℕ} {α limitCoeff : ℝ}
    (rankCoeff : Fin k → ℝ)
    (hα : 1 < α) (hk : 0 < k) (hcoeff : 0 < limitCoeff)
    (hcoeff_sum : (∑ i : Fin k, rankCoeff i) = limitCoeff)
    (hrank :
      ∀ i : Fin k,
        Filter.Tendsto
          (fun q : ℕ =>
            (μ (q + 1 - i.val) (q + 1) - μ (q - i.val) q) /
              paretoPowerMarginalScale α q)
          Filter.atTop (nhds (rankCoeff i))) :
    ParetoOrderStatisticScaledMarginalCertificate μ k α limitCoeff := by
  let G : AppliedModelingLib.Probability.OrderStatisticScaledMarginalCertificate μ k
      (paretoPowerMarginalScale α) limitCoeff :=
    AppliedModelingLib.Probability.OrderStatisticScaledMarginalCertificate.ofFiniteRankScaledLimits
        rankCoeff hk hcoeff
        (by
          filter_upwards with q
          exact paretoPowerMarginalScale_pos α q)
        hcoeff_sum hrank
  exact
    { alpha_gt_one := hα
      k_pos := G.k_pos
      coeff_pos := G.coeff_pos
      marginal_ratio_tendsto := G.marginal_ratio_tendsto }

/--
Pareto-specialized fixed-rank constructor.  The gamma-ratio calculation only
needs to prove the per-rank limits with the canonical Lemma D.4 coefficients;
Lean then supplies the positive aggregate coefficient automatically.
-/
def ofParetoRankScaledLimits
    {μ : ℕ → ℕ → ℝ} {k : ℕ} {α : ℝ}
    (hα : 1 < α) (hk : 0 < k)
    (hrank :
      ∀ i : Fin k,
        Filter.Tendsto
          (fun q : ℕ =>
            (μ (q + 1 - i.val) (q + 1) - μ (q - i.val) q) /
              paretoPowerMarginalScale α q)
          Filter.atTop (nhds (paretoRankMarginalCoeff α i.val))) :
    ParetoOrderStatisticScaledMarginalCertificate μ k α
      (∑ i : Fin k, paretoRankMarginalCoeff α i.val) :=
  ofFiniteRankScaledLimits
    (fun i : Fin k => paretoRankMarginalCoeff α i.val)
    hα hk (paretoRankMarginalCoeff_sum_pos hα hk) rfl hrank

/--
Certificate for the cited Pareto gamma-ratio order-statistic mean sequence.
This closes the algebraic sequence layer of Lemma D.4 while leaving the
measure/order-statistic identification of a concrete Pareto law as a separate
source bridge.
-/
def ofCitedOrderStatisticMean
    {k : ℕ} {α : ℝ}
    (hα : 1 < α) (hk : 0 < k) :
    ParetoOrderStatisticScaledMarginalCertificate
      (paretoCitedOrderStatisticMean α) k α
      (∑ i : Fin k, paretoRankMarginalCoeff α i.val) :=
  ofParetoRankScaledLimits hα hk
    (fun i => paretoCitedOrderStatisticMean_fixed_rank_scaled_limit hα i.val)

/--
Certificate for an expected order-statistic mean sequence whose concrete
source law agrees eventually with the cited Pareto gamma-ratio formula at every
fixed rank.
-/
def ofExpectedOrderStatisticMeanSeqCitedSource
    {sampleMeasure : (a : ℕ) → MeasureTheory.Measure (Fin a → ℝ)}
    {k : ℕ} {α : ℝ}
    (hα : 1 < α) (hk : 0 < k)
    (hsrc : ParetoCitedOrderStatisticSource sampleMeasure α) :
    ParetoOrderStatisticScaledMarginalCertificate
      (expectedOrderStatisticMeanSeq sampleMeasure) k α
      (∑ i : Fin k, paretoRankMarginalCoeff α i.val) :=
  ofParetoRankScaledLimits hα hk
    (fun i => hsrc.fixed_rank_scaled_limit hα i.val)

/--
Convert the Pareto source-side order-statistic marginal asymptotic into the
reusable probability-to-optimization scaled marginal certificate.
-/
noncomputable def toTopKScaledMarginalLimitCertificate
    {T : ℕ} {μ : ℕ → ℕ → ℝ} {k : ℕ} {α limitCoeff : ℝ}
    (C : ParetoOrderStatisticScaledMarginalCertificate μ k α limitCoeff) :
    TopKScaledMarginalLimitCertificate
      (TopKValueOracle.ofOrderStatisticMean T μ) k
      (paretoPowerMarginalScale α)
      (fun _ : ItemType T => limitCoeff) := by
  simpa [topKExpectationOracleOfTopKValueOracle,
      AppliedModelingLib.Probability.TopKExpectationOracle.orderStatisticTopKExpectationOracle,
      TopKValueOracle.ofOrderStatisticMean]
    using
      C.toOrderStatisticScaledMarginalCertificate
        |>.toTopKExpectationScaledMarginalLimitCertificate (ItemType T)

end ParetoOrderStatisticScaledMarginalCertificate

/-- The Pareto power-marginal scale tends to zero. -/
theorem paretoPowerMarginalScale_tendsto_zero
    {α : ℝ} (hα : 1 < α) :
    Filter.Tendsto (paretoPowerMarginalScale α)
      Filter.atTop (nhds 0) := by
  change Filter.Tendsto
    (fun q : ℕ =>
      (((q + 1 : ℕ) : ℝ) ^ (-(paretoMarginalExponent α))))
    Filter.atTop (nhds 0)
  simpa [Nat.cast_add, Nat.cast_one] using
    AppliedModelingLib.Math.tendsto_nat_succ_cast_rpow_neg_nhds_zero
      (paretoMarginalExponent_pos hα)

/--
Concrete iid Pareto top-`k` source marginals vanish as the type count grows.

This is a reusable interiority ingredient: high-count backward marginals become
smaller than any fixed positive low-count forward marginal.
-/
theorem paretoIidOrderStatisticTopK_forward_marginal_tendsto_zero
    (T : ℕ) {k : ℕ} {α : ℝ}
    (hα : 1 < α) (hk : 0 < k) (t : ItemType T) :
    Filter.Tendsto
      (fun q =>
        (paretoIidOrderStatisticOracle T α).expectedTopSum k t (q + 1) -
          (paretoIidOrderStatisticOracle T α).expectedTopSum k t q)
      Filter.atTop (nhds 0) := by
  let C :
      TopKScaledMarginalLimitCertificate
        (paretoIidOrderStatisticOracle T α) k
        (paretoPowerMarginalScale α)
        (fun _ : ItemType T =>
          ∑ i : Fin k, paretoRankMarginalCoeff α i.val) :=
    ParetoOrderStatisticScaledMarginalCertificate.toTopKScaledMarginalLimitCertificate
      (ParetoOrderStatisticScaledMarginalCertificate.ofExpectedOrderStatisticMeanSeqCitedSource
        hα hk (paretoIidSampleMeasure_citedOrderStatisticSource hα))
  exact TopKScaledMarginalLimitCertificate.marginal_tendsto_zero
    C (paretoPowerMarginalScale_tendsto_zero hα) t

/-- The first concrete iid Pareto top-`k` forward marginal is positive. -/
theorem paretoIidOrderStatisticTopK_forward_zero_pos
    (T : ℕ) {k : ℕ} {α : ℝ}
    (hα : 1 < α) (hk : 0 < k) (t : ItemType T) :
    0 <
      (paretoIidOrderStatisticOracle T α).expectedTopSum k t 1 -
        (paretoIidOrderStatisticOracle T α).expectedTopSum k t 0 := by
  have hmean :
      paretoIidOrderStatisticMeanSeq α 1 1 =
        paretoRankGammaRatioMean α 0 1 := by
    calc
      paretoIidOrderStatisticMeanSeq α 1 1
          =
            AppliedModelingLib.Probability.expectedUpperOrderStatistic
              (paretoIidSampleMeasure α 1) ⟨0, by norm_num⟩ := by
            simpa [paretoIidOrderStatisticMeanSeq] using
              AppliedModelingLib.Probability.expectedSampleOrderStatisticMean_eq_expectedUpperOrderStatistic_of_rank_from_top
                (μ := paretoIidSampleMeasure α 1) (r := 0) (a := 1)
                (by norm_num)
      _ = paretoRankGammaRatioMean α 0 1 := by
            simpa [paretoIidSampleMeasure, paretoRankGammaRatioMean,
              paretoRankValueCoeff] using
              AppliedModelingLib.Probability.Pareto.iidProductMeasure_one_expectedUpperOrderStatistic_eq_gamma_ratio
                (α := α) hα (q := 1)
                (rankFromTop := ⟨0, by norm_num⟩)
  have hpos : 0 < paretoIidOrderStatisticMeanSeq α 1 1 := by
    rw [hmean]
    exact paretoRankGammaRatioMean_pos hα 0 1
  have htop_one :
      orderStatisticTopKSumFromMean (paretoIidOrderStatisticMeanSeq α) k 1 =
        paretoIidOrderStatisticMeanSeq α 1 1 := by
    rw [orderStatisticTopKSumFromMean_eq_bottomIndexed_sum]
    rw [min_eq_right (Nat.succ_le_of_lt hk)]
    simp
  simpa [paretoIidOrderStatisticOracle, TopKValueOracle.ofOrderStatisticMean,
    htop_one] using hpos

/--
In the concrete iid Pareto order-statistic model, every type eventually has a
positive count in every finite optimum.

This discharges the count-floor/interiority part of the Pareto FOC package
with floor `0`; the remaining direct Theorem 1(iv) gap is the variable-count
large-gap marginal comparison.
-/
theorem paretoIidOrderStatistic_count_positive_eventually
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) {k : ℕ} {α : ℝ}
    (hα : 1 < α) (hk : 0 < k)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t) :
    ∀ᶠ N in Filter.atTop,
      ∀ a : CountAllocation T, 0 < N →
        (paretoIidOrderStatisticConsumptionModel likelihood k α).IsOptimalAtTotal N a →
        ∀ t, 0 < a.count t := by
  classical
  let M : ConsumptionModel T :=
    paretoIidOrderStatisticConsumptionModel likelihood k α
  have hdom_ev :
      ∀ᶠ q in Filter.atTop,
        ∀ src dst : ItemType T,
          M.weightedBackwardMarginal src q <
            M.weightedForwardMarginal dst 0 := by
    refine Filter.eventually_all.2 ?_
    intro src
    refine Filter.eventually_all.2 ?_
    intro dst
    have hzero_forward_pos :
        0 < M.weightedForwardMarginal dst 0 := by
      have hbase :=
        paretoIidOrderStatisticTopK_forward_zero_pos T hα hk dst
      unfold M paretoIidOrderStatisticConsumptionModel
        ConsumptionModel.weightedForwardMarginal ConsumptionModel.marginalValue
        AppliedModelingLib.Allocation.marginal TopKValueOracle.toConsumptionModel
      exact mul_pos (hlike_pos dst) hbase
    have hforward_tend :=
      paretoIidOrderStatisticTopK_forward_marginal_tendsto_zero
        T hα hk src
    have hback_tend :
        Filter.Tendsto
          (fun q =>
            (paretoIidOrderStatisticOracle T α).expectedTopSum k src q -
              (paretoIidOrderStatisticOracle T α).expectedTopSum k src (q - 1))
          Filter.atTop (nhds 0) := by
      have hcomp := hforward_tend.comp (Filter.tendsto_sub_atTop_nat 1)
      refine Filter.Tendsto.congr' ?_ hcomp
      filter_upwards [Filter.eventually_gt_atTop 0] with q hq
      dsimp [Function.comp_def]
      rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hq)]
    have hweighted_tend :
        Filter.Tendsto
          (fun q =>
            likelihood src *
              ((paretoIidOrderStatisticOracle T α).expectedTopSum k src q -
                (paretoIidOrderStatisticOracle T α).expectedTopSum k src (q - 1)))
          Filter.atTop (nhds 0) := by
      simpa using hback_tend.const_mul (likelihood src)
    have hlt :=
      hweighted_tend.eventually
        (eventually_lt_nhds hzero_forward_pos)
    filter_upwards [hlt, Filter.eventually_gt_atTop 0] with q hltq hqpos
    unfold M paretoIidOrderStatisticConsumptionModel
      ConsumptionModel.weightedBackwardMarginal
      ConsumptionModel.weightedForwardMarginal ConsumptionModel.marginalValue
      AppliedModelingLib.Allocation.marginal TopKValueOracle.toConsumptionModel
    rw [dif_neg (Nat.ne_of_gt hqpos)]
    exact hltq
  rcases Filter.eventually_atTop.1 hdom_ev with ⟨source_threshold, hthreshold⟩
  refine Filter.eventually_atTop.2 ?_
  refine ⟨T * source_threshold + 1, ?_⟩
  intro N hNlarge a hNpos hopt dst
  by_contra hnot_pos
  have hdst_zero : a.count dst = 0 := Nat.eq_zero_of_not_pos hnot_pos
  have hlarge : T * source_threshold < N := by omega
  have hexists_src :
      ∃ src : ItemType T, source_threshold < a.count src := by
    by_contra hnone
    push Not at hnone
    have hsum_le :
        AppliedModelingLib.Allocation.total a ≤ T * source_threshold := by
      unfold AppliedModelingLib.Allocation.total
      calc
        (∑ t : ItemType T, a.count t)
            ≤ ∑ _t : ItemType T, source_threshold :=
              Finset.sum_le_sum (fun t _ => hnone t)
        _ = T * source_threshold := by
              simp [Finset.sum_const, Fintype.card_fin]
    rw [hopt.1] at hsum_le
    exact (not_lt_of_ge hsum_le) hlarge
  obtain ⟨src, hsrc_large⟩ := hexists_src
  have hsrc_pos : 0 < a.count src := Nat.zero_lt_of_lt hsrc_large
  have hne : src ≠ dst := by
    intro hsame
    subst dst
    rw [hdst_zero] at hsrc_large
    exact Nat.not_lt_zero _ hsrc_large
  have hfoc :=
    ConsumptionModel.weightedForwardMarginal_le_weightedBackwardMarginal_of_optimum
      (M := paretoIidOrderStatisticConsumptionModel likelihood k α)
      (N := N) (a := a) (src := src) (dst := dst)
      hopt hne hsrc_pos
  have hdom := hthreshold (a.count src) (le_of_lt hsrc_large) src dst
  rw [hdst_zero] at hfoc
  exact (not_lt_of_ge hfoc) hdom

/--
In the concrete iid Pareto order-statistic model, every type eventually has
count above any fixed finite floor in every finite optimum.
-/
theorem paretoIidOrderStatistic_count_floor_eventually
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) {k : ℕ} {α : ℝ}
    (hα : 1 < α) (hk : 0 < k)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (floor : ℕ) :
    ∀ᶠ N in Filter.atTop,
      ∀ a : CountAllocation T, 0 < N →
        (paretoIidOrderStatisticConsumptionModel likelihood k α).IsOptimalAtTotal N a →
        ∀ t, floor < a.count t :=
  topK_count_floor_eventually_of_marginal_tendsto_zero_and_positive_low_forward
    (paretoIidOrderStatisticOracle T α) likelihood k floor hlike_pos
    (by
      intro t q _hq_floor
      simpa [TopKValueOracle.marginalTopK,
        paretoIidOrderStatisticOracle,
        TopKValueOracle.ofOrderStatisticMean] using
        paretoIidOrderStatisticTopK_forward_marginal_pos
          T hα hk t q)
    (paretoIidOrderStatisticTopK_forward_marginal_tendsto_zero
      T hα hk)

/--
Concrete iid Pareto large-gap marginal comparison.

The `1 / sqrt (N+1)` base error grows like `sqrt N` after multiplying by
`N`, so it eventually absorbs the one-count source/destination shifts needed
to compare backward and forward marginals against the same power-law template.
-/
theorem paretoIidOrderStatistic_large_gap_count_eventually
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) {k : ℕ} {α : ℝ}
    (hα : 1 < α) (hk : 0 < k)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t) :
    ∀ᶠ N in Filter.atTop,
      ∀ src dst qsrc qdst,
        qsrc ≤ N →
        qdst ≤ N →
        k < qsrc →
        k < qdst →
        AppliedModelingLib.Math.invSqrtSuccError N * (N : ℝ) <
          (qsrc : ℝ) / likelihood src ^ (α / (α - 1)) -
            (qdst : ℝ) / likelihood dst ^ (α / (α - 1)) →
        (paretoIidOrderStatisticConsumptionModel likelihood k α).weightedBackwardMarginal
            src qsrc <
          (paretoIidOrderStatisticConsumptionModel likelihood k α).weightedForwardMarginal
            dst qdst := by
  classical
  let η : ℝ := paretoMarginalExponent α
  let γ : ℝ := α / (α - 1)
  have hη_pos : 0 < η := by
    dsimp [η]
    exact paretoMarginalExponent_pos hα
  have hγ_eq : 1 / η = γ := by
    dsimp [η, γ]
    exact paretoMarginalExponent_one_div_eq_gamma hα
  have hcoeff_pos :
      0 < ∑ i : Fin k, paretoRankMarginalCoeff α i.val :=
    paretoRankMarginalCoeff_sum_pos hα hk
  exact
    AppliedModelingLib.Allocation.powerLawEnvelope_large_gap_count_eventually
      likelihood
      (paretoIidOrderStatisticConsumptionModel likelihood k α).valueOfCount
      (η := η) (γ := γ)
      (coeff := ∑ i : Fin k, paretoRankMarginalCoeff α i.val)
      (dstShift := 0) (floor := k)
      hη_pos hγ_eq hcoeff_pos (by norm_num) hk hlike_pos
      (by
        intro src qsrc hsrc_floor
        simpa [η] using
          paretoIidOrderStatistic_weightedBackwardMarginal_le_power_bound
            likelihood hα hk hlike_pos hsrc_floor src)
      (by
        intro dst qdst hdst_floor
        simpa [η, Nat.cast_add, Nat.cast_one, add_assoc] using
          paretoIidOrderStatistic_power_bound_le_weightedForwardMarginal
            likelihood hα hk hlike_pos (le_of_lt hdst_floor) dst)

/--
Reduced Pareto iid optimization certificate.

The count-floor/interiority field is now proved internally for the concrete iid
Pareto order-statistic model, so the remaining source obligation is only the
variable-count large-gap marginal comparison.
-/
structure ParetoIidOrderStatisticLargeGapCertificate {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (k : ℕ) (α : ℝ) where
  base_error : ℕ → ℝ
  base_error_nonneg : ∀ N, 0 ≤ base_error N
  base_error_tends_to_zero : AppliedModelingLib.Math.TendsToZero base_error
  floor : ℕ
  large_gap_count :
    ∀ᶠ N in Filter.atTop,
      ∀ src dst qsrc qdst,
        qsrc ≤ N →
        qdst ≤ N →
        floor < qsrc →
        floor < qdst →
        base_error N * (N : ℝ) <
          (qsrc : ℝ) / likelihood src ^ (α / (α - 1)) -
            (qdst : ℝ) / likelihood dst ^ (α / (α - 1)) →
        (paretoIidOrderStatisticConsumptionModel likelihood k α).weightedBackwardMarginal
            src qsrc <
          (paretoIidOrderStatisticConsumptionModel likelihood k α).weightedForwardMarginal
            dst qdst

/-- Concrete large-gap certificate for the iid Pareto order-statistic model. -/
noncomputable def paretoIidOrderStatistic_largeGapCertificate
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) {k : ℕ} {α : ℝ}
    (hα : 1 < α) (hk : 0 < k)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t) :
    ParetoIidOrderStatisticLargeGapCertificate likelihood k α where
  base_error := AppliedModelingLib.Math.invSqrtSuccError
  base_error_nonneg := AppliedModelingLib.Math.invSqrtSuccError_nonneg
  base_error_tends_to_zero := AppliedModelingLib.Math.invSqrtSuccError_tendsToZero
  floor := k
  large_gap_count :=
    paretoIidOrderStatistic_large_gap_count_eventually
      likelihood hα hk hlike_pos

namespace ParetoIidOrderStatisticLargeGapCertificate

noncomputable def toEventualFOCCertificate
    {T : ℕ} [NeZero T]
    {likelihood : ItemType T → ℝ} {k : ℕ} {α : ℝ}
    (C : ParetoIidOrderStatisticLargeGapCertificate likelihood k α)
    (hα : 1 < α) (hk : 0 < k)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t) :
    ParetoIidOrderStatisticEventualFOCCertificate likelihood k α where
  base_error := C.base_error
  base_error_nonneg := C.base_error_nonneg
  base_error_tends_to_zero := C.base_error_tends_to_zero
  floor := C.floor
  count_floor_eventually :=
    paretoIidOrderStatistic_count_floor_eventually
      likelihood hα hk hlike_pos C.floor
  large_gap_count := by
    filter_upwards [C.large_gap_count] with N hN src dst qsrc qdst
      hqsrc_le hqdst_le hqsrc_floor hqdst_floor hgap
    exact hN src dst qsrc qdst hqsrc_le hqdst_le
      hqsrc_floor hqdst_floor hgap

noncomputable def toPairwiseScaledEventualSublinearFOCCertificate
    {T : ℕ} [NeZero T]
    {likelihood : ItemType T → ℝ} {k : ℕ} {α : ℝ}
    (C : ParetoIidOrderStatisticLargeGapCertificate likelihood k α)
    (hα : 1 < α) (hk : 0 < k)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t) :
    PairwiseScaledEventualSublinearFOCCertificate
      (fun _ => paretoIidOrderStatisticConsumptionModel likelihood k α)
      (fun t : ItemType T => likelihood t ^ (α / (α - 1)))
      (gammaLikelihoodProfile likelihood (α / (α - 1))) :=
  ParetoIidOrderStatisticEventualFOCCertificate.toPairwiseScaledEventualSublinearFOCCertificate
    (C.toEventualFOCCertificate hα hk hlike_pos) hlike_pos

end ParetoIidOrderStatisticLargeGapCertificate

theorem paretoPowerMarginalValue_backward_marginal
    (α : ℝ) {q : ℕ} (hq : 0 < q) :
    paretoPowerMarginalValue α q -
        paretoPowerMarginalValue α (q - 1) =
      ((q : ℝ) ^ (-(paretoMarginalExponent α))) := by
  have hpred : q - 1 + 1 = q := Nat.sub_add_cancel (Nat.succ_le_of_lt hq)
  nth_rewrite 1 [← hpred]
  rw [paretoPowerMarginalValue_forward_marginal]
  simp [hpred]

theorem paretoPowerMarginalValue_forward_marginal_nonneg
    (α : ℝ) (q : ℕ) :
    0 ≤ paretoPowerMarginalValue α (q + 1) -
        paretoPowerMarginalValue α q := by
  rw [paretoPowerMarginalValue_forward_marginal]
  exact Real.rpow_nonneg (by positivity) _

theorem paretoPowerMarginalValue_marginal_antitone_step
    {α : ℝ} (hα_gt_one : 1 < α) (q : ℕ) :
    paretoPowerMarginalValue α (q + 2) -
        paretoPowerMarginalValue α (q + 1) ≤
      paretoPowerMarginalValue α (q + 1) -
        paretoPowerMarginalValue α q := by
  rw [paretoPowerMarginalValue_forward_marginal,
    paretoPowerMarginalValue_forward_marginal]
  have hbase_pos : 0 < ((q + 1 : ℕ) : ℝ) := by positivity
  have hbase_le : ((q + 1 : ℕ) : ℝ) ≤ ((q + 2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.le_succ q)
  have hexp_nonpos : -(paretoMarginalExponent α) ≤ 0 :=
    neg_nonpos.mpr (le_of_lt (paretoMarginalExponent_pos hα_gt_one))
  exact Real.rpow_le_rpow_of_nonpos hbase_pos hbase_le hexp_nonpos

theorem paretoPowerMarginalModel_has_nonnegative_marginals
    {T : ℕ} (likelihood : ItemType T → ℝ) (α : ℝ) :
    ((paretoPowerMarginalOracle T α).toConsumptionModel likelihood 1).HasNonnegativeMarginals := by
  intro t q
  exact paretoPowerMarginalValue_forward_marginal_nonneg α q

theorem paretoPowerMarginalModel_has_diminishing_returns
    {T : ℕ} (likelihood : ItemType T → ℝ) {α : ℝ}
    (hα_gt_one : 1 < α) :
    ((paretoPowerMarginalOracle T α).toConsumptionModel likelihood 1).HasDiminishingReturns := by
  intro t q
  exact paretoPowerMarginalValue_marginal_antitone_step hα_gt_one q

/-- Finite-prefix error for the exact Pareto power-marginal FOC proof. -/
noncomputable def paretoPowerMarginalError {T : ℕ}
    (likelihood : ItemType T → ℝ) (α : ℝ) (N : ℕ) : ℝ :=
  powerLawSublinearFOCError likelihood (α / (α - 1)) N

theorem paretoPowerMarginalError_nonneg {T : ℕ}
    (likelihood : ItemType T → ℝ) (α : ℝ)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (N : ℕ) :
    0 ≤ paretoPowerMarginalError likelihood α N :=
  powerLawSublinearFOCError_nonneg likelihood (α / (α - 1)) hlike_pos N

theorem paretoPowerMarginalError_tends_to_zero {T : ℕ}
    (likelihood : ItemType T → ℝ) (α : ℝ)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t) :
    AppliedModelingLib.Math.TendsToZero
      (paretoPowerMarginalError likelihood α) :=
  powerLawSublinearFOCError_tends_to_zero likelihood (α / (α - 1)) hlike_pos

/--
Exact Pareto power-marginal FOC certificate.

This closes the optimization layer for a top-one oracle with the paper's
Pareto marginal decay exponent. The remaining source-specific probability work
is to derive these power-law marginals, or their asymptotic equivalent, from the
actual Pareto order-statistic model.
-/
noncomputable def paretoPowerMarginalSublinearFOCCertificate
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (α : ℝ)
    (hα_gt_one : 1 < α)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t) :
    PairwiseScaledSublinearFOCCertificate
      (fun _ =>
        (paretoPowerMarginalOracle T α).toConsumptionModel likelihood 1)
      (fun t : ItemType T => likelihood t ^ (α / (α - 1)))
      (gammaLikelihoodProfile likelihood (α / (α - 1))) :=
  topKPowerLawSublinearFOCCertificate likelihood
    (paretoMarginalExponent_pos hα_gt_one)
    (paretoMarginalExponent_one_div_eq_gamma hα_gt_one)
    hlike_pos
    (fun _t _q hq => paretoPowerMarginalValue_backward_marginal α hq)
    (fun _t q => paretoPowerMarginalValue_forward_marginal α q)

/--
Auxiliary tail-index bridge.

If marginals decay as `q ^ (1/α - 1)`, then the optimal allocation is
approximately γ-homogeneous with γ = `1 - 1/α`.  This is not the paper's
Theorem 2, which is about Bernoulli success probabilities decaying by item rank.
-/
structure TailIndexHomogeneityCertificate
    {T : ℕ} [NeZero T] (M : ConsumptionModel T) (α : ℝ) : Prop where
  alpha_gt_one : 1 < α
  tail_index : HasTypeTailIndex M (1/α)
  likelihood_pos : ∀ t, 0 < M.likelihood t
  asymptotic_homogeneity :
    ConsumptionModel.AsymptoticHomogeneityTarget
      (fun _ => M) (paretoProfile M.likelihood α) AppliedModelingLib.Math.ExactInvRate

/--
Auxiliary tail-index homogeneity bridge from an explicit certificate.
-/
theorem homogeneity_of_tail_index
    {T : ℕ} [NeZero T] (M : ConsumptionModel T) (α : ℝ)
    (hcert : TailIndexHomogeneityCertificate M α) :
    ConsumptionModel.AsymptoticHomogeneityTarget
      (fun _ => M) (paretoProfile M.likelihood α) AppliedModelingLib.Math.ExactInvRate := hcert.asymptotic_homogeneity

/--
Finite pairwise difference bound for Pareto types.
If marginals are `L * q^(1/α - 1)`, then optimal counts satisfy a power-law balance.
-/
def ParetoOptimumPairwiseBoundTarget
    {T : ℕ} (M : ConsumptionModel T) (index : ℝ) : Prop :=
  ∀ N {a : CountAllocation T},
    M.IsOptimalAtTotal N a →
      ∀ t₁ t₂,
        0 < a.count t₁ → t₁ ≠ t₂ →
        ((a.count t₁ : ℝ) - 1) ^ (index - 1) ≤
          (M.likelihood t₂ / M.likelihood t₁) *
            (a.count t₂ + 1 : ℝ) ^ (index - 1)

/--
Certificate for the finite Pareto pairwise balance target.

The current `HasTailIndex` interface allows type-specific constants and says
nothing about the first marginal at zero, so it is not enough by itself to prove
this bound. Keep the exact pairwise inequality as a named certificate until the
paper's Pareto order-statistic asymptotics are formalized.
-/
structure ParetoOptimumPairwiseBoundCertificate
    {T : ℕ} (M : ConsumptionModel T) (index : ℝ) : Prop where
  tail_index : HasTypeTailIndex M index
  likelihood_pos : ∀ t, 0 < M.likelihood t
  pairwise_bound : ParetoOptimumPairwiseBoundTarget M index

theorem pareto_optimum_pairwise_bound
    {T : ℕ} (M : ConsumptionModel T) (index : ℝ)
    (hcert : ParetoOptimumPairwiseBoundCertificate M index)
    (N : ℕ) {a : CountAllocation T}
    (hopt : M.IsOptimalAtTotal N a) :
    ∀ t₁ t₂,
      0 < a.count t₁ → t₁ ≠ t₂ →
      ((a.count t₁ : ℝ) - 1) ^ (index - 1) ≤
        (M.likelihood t₂ / M.likelihood t₁) * (a.count t₂ + 1 : ℝ) ^ (index - 1) :=  hcert.pairwise_bound N hopt

end PRPKG24AccuracyDiversity

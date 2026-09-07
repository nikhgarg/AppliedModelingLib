import PRPKG24AccuracyDiversity.SeparableAsymptotic
import PRPKG24AccuracyDiversity.Uniform
import AppliedModelingLib.Foundations.Math.GammaAsymptotics
import AppliedModelingLib.Foundations.Probability.RealDistribution
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm

namespace PRPKG24AccuracyDiversity

open Filter Topology
open scoped BigOperators

/--
Marginal decay exponent for the bounded-support branch's power-law oracle.

If the upper-tail density behaves like `(M - x)^(beta - 1)`, the paper's
bounded branch has `h(q + 1) - h(q)` proportional to
`q^-((beta + 1) / beta)`.
-/
noncomputable def boundedMarginalExponent (beta : ℝ) : ℝ := (beta + 1) / beta

theorem boundedMarginalExponent_pos {beta : ℝ} (hbeta_pos : 0 < beta) :
    0 < boundedMarginalExponent beta := by
  unfold boundedMarginalExponent
  exact div_pos (by linarith) hbeta_pos

theorem boundedMarginalExponent_one_div_eq_gamma
    {beta : ℝ} (hbeta_pos : 0 < beta) :
    1 / boundedMarginalExponent beta = beta / (beta + 1) := by
  have hsum_pos : 0 < beta + 1 := by linarith
  unfold boundedMarginalExponent
  field_simp [ne_of_gt hbeta_pos, ne_of_gt hsum_pos]

/--
Exact power-marginal value used as a bounded-support asymptotic checkpoint.

This records the marginal law predicted by Lemma 1 for bounded distributions
with tail exponent `beta`. The remaining source-specific probability work is to
derive this marginal law, or its asymptotic equivalent, from Lemma D.2.
-/
noncomputable def boundedPowerMarginalValue (beta : ℝ) (q : ℕ) : ℝ :=
  ∑ j ∈ Finset.range q,
    (((j + 1 : ℕ) : ℝ) ^ (-(boundedMarginalExponent beta)))

/-- Common top-one oracle with exact bounded-branch power-law marginals. -/
noncomputable def boundedPowerMarginalOracle (T : ℕ) (beta : ℝ) :
    TopKValueOracle T := TopKValueOracle.common T (boundedPowerMarginalValue beta)

theorem boundedPowerMarginalValue_zero (beta : ℝ) :
    boundedPowerMarginalValue beta 0 = 0 := by
  simp [boundedPowerMarginalValue]

theorem boundedPowerMarginalValue_forward_marginal
    (beta : ℝ) (q : ℕ) :
    boundedPowerMarginalValue beta (q + 1) -
        boundedPowerMarginalValue beta q =
      (((q + 1 : ℕ) : ℝ) ^ (-(boundedMarginalExponent beta))) := by
  simp [boundedPowerMarginalValue, Finset.sum_range_succ]

/-- Exact scaled marginal used by the bounded power-marginal oracle. -/
noncomputable def boundedPowerMarginalScale (beta : ℝ) (q : ℕ) : ℝ := (((q + 1 : ℕ) : ℝ) ^ (-(boundedMarginalExponent beta)))

theorem boundedPowerMarginalScale_pos (beta : ℝ) (q : ℕ) :
    0 < boundedPowerMarginalScale beta q := by
  unfold boundedPowerMarginalScale
  exact Real.rpow_pos_of_pos (by positivity) _

theorem boundedPowerMarginalScale_tendsto_zero
    {beta : ℝ} (hbeta_pos : 0 < beta) :
    Tendsto (boundedPowerMarginalScale beta) atTop (nhds 0) := by
  have hη_pos : 0 < boundedMarginalExponent beta :=
    boundedMarginalExponent_pos hbeta_pos
  change Tendsto
    (fun q : ℕ => (((q + 1 : ℕ) : ℝ) ^
      (-(boundedMarginalExponent beta)))) atTop (nhds 0)
  convert
    (tendsto_rpow_neg_atTop hη_pos).comp
      (tendsto_natCast_atTop_atTop.comp
        (Filter.tendsto_add_atTop_nat 1)) using 1

theorem boundedPowerMarginalScale_one_eq_inv_sq (q : ℕ) :
    boundedPowerMarginalScale 1 q =
      (((q + 1 : ℕ) : ℝ) ^ (-(2 : ℝ))) := by
  norm_num [boundedPowerMarginalScale, boundedMarginalExponent]

/-- The bounded marginal scale is stable under one index shift. -/
theorem boundedPowerMarginalScale_succ_ratio_tendsto_one
    {beta : ℝ} (hbeta_pos : 0 < beta) :
    Tendsto
      (fun q : ℕ =>
        boundedPowerMarginalScale beta (q + 1) /
          boundedPowerMarginalScale beta q)
      atTop (nhds 1) := by
  let eta : ℝ := boundedMarginalExponent beta
  have hratio :
      Tendsto
        (fun q : ℕ =>
          (((q + 1 : ℕ) : ℝ) / (((q + 2 : ℕ) : ℝ))))
        atTop (nhds 1) := by
    have h :=
      tendsto_add_mul_div_add_mul_atTop_nhds
        (𝕜 := ℝ) (1 : ℝ) (2 : ℝ) (1 : ℝ)
        (by norm_num : (1 : ℝ) ≠ 0)
    convert h using 1
    · ext q
      norm_num [Nat.cast_add, Nat.cast_one]
      ring_nf
    · norm_num
  have hrpow :
      Tendsto
        (fun q : ℕ =>
          ((((q + 1 : ℕ) : ℝ) / (((q + 2 : ℕ) : ℝ))) ^ eta))
        atTop (nhds 1) := by
    have h :=
      hratio.rpow_const (p := eta)
        (Or.inl (by norm_num : (1 : ℝ) ≠ 0))
    simpa using h
  refine Tendsto.congr' ?_ hrpow
  filter_upwards with q
  have hq1_pos : 0 < (((q + 1 : ℕ) : ℝ)) := by positivity
  have hq2_pos : 0 < (((q + 2 : ℕ) : ℝ)) := by positivity
  have hq1_ne : (((q + 1 : ℕ) : ℝ)) ≠ 0 := ne_of_gt hq1_pos
  have hq2_ne : (((q + 2 : ℕ) : ℝ)) ≠ 0 := ne_of_gt hq2_pos
  have hq1_pow_ne : (((q + 1 : ℕ) : ℝ)) ^ eta ≠ 0 :=
    (Real.rpow_pos_of_pos hq1_pos eta).ne'
  have hq2_pow_ne : (((q + 2 : ℕ) : ℝ)) ^ eta ≠ 0 :=
    (Real.rpow_pos_of_pos hq2_pos eta).ne'
  rw [boundedPowerMarginalScale]
  change
    ((((q + 1 : ℕ) : ℝ) / (((q + 2 : ℕ) : ℝ))) ^ eta) =
      (((q + 2 : ℕ) : ℝ) ^ (-eta)) /
        (((q + 1 : ℕ) : ℝ) ^ (-eta))
  rw [Real.rpow_neg hq2_pos.le eta, Real.rpow_neg hq1_pos.le eta]
  rw [Real.div_rpow hq1_pos.le hq2_pos.le eta]
  field_simp [hq1_ne, hq2_ne, hq1_pow_ne, hq2_pow_ne]

/--
The exact bounded power-marginal oracle satisfies the reusable scaled-marginal
certificate with unit type weights.
-/
noncomputable def boundedPowerMarginalScaledMarginalLimitCertificate
    (T : ℕ) (beta : ℝ) :
    TopKScaledMarginalLimitCertificate
      (boundedPowerMarginalOracle T beta) 1
      (boundedPowerMarginalScale beta)
      (fun _ : ItemType T => (1 : ℝ)) where
  scale_pos_eventually := by
    filter_upwards with q
    exact boundedPowerMarginalScale_pos beta q
  weight_pos := by
    intro t
    norm_num
  marginal_ratio_tendsto := by
    intro t
    refine (tendsto_congr' ?_).mpr tendsto_const_nhds
    filter_upwards with q
    have hpow_ne :
        (((q : ℝ) + 1) ^ (-(boundedMarginalExponent beta))) ≠ 0 :=
      (Real.rpow_pos_of_pos (by positivity) _).ne'
    simp [AppliedModelingLib.Probability.TopKExpectationOracle.marginalTopK,
      topKExpectationOracleOfTopKValueOracle, boundedPowerMarginalOracle,
      TopKValueOracle.common, boundedPowerMarginalScale,
      boundedPowerMarginalValue_forward_marginal, hpow_ne]

theorem boundedPowerMarginalValue_backward_marginal
    (beta : ℝ) {q : ℕ} (hq : 0 < q) :
    boundedPowerMarginalValue beta q -
        boundedPowerMarginalValue beta (q - 1) =
      ((q : ℝ) ^ (-(boundedMarginalExponent beta))) := by
  have hpred : q - 1 + 1 = q := Nat.sub_add_cancel (Nat.succ_le_of_lt hq)
  nth_rewrite 1 [← hpred]
  rw [boundedPowerMarginalValue_forward_marginal]
  simp [hpred]

theorem boundedPowerMarginalValue_forward_marginal_nonneg
    (beta : ℝ) (q : ℕ) :
    0 ≤ boundedPowerMarginalValue beta (q + 1) -
        boundedPowerMarginalValue beta q := by
  rw [boundedPowerMarginalValue_forward_marginal]
  exact Real.rpow_nonneg (by positivity) _

theorem boundedPowerMarginalValue_marginal_antitone_step
    {beta : ℝ} (hbeta_pos : 0 < beta) (q : ℕ) :
    boundedPowerMarginalValue beta (q + 2) -
        boundedPowerMarginalValue beta (q + 1) ≤
      boundedPowerMarginalValue beta (q + 1) -
        boundedPowerMarginalValue beta q := by
  rw [boundedPowerMarginalValue_forward_marginal,
    boundedPowerMarginalValue_forward_marginal]
  have hbase_pos : 0 < ((q + 1 : ℕ) : ℝ) := by positivity
  have hbase_le : ((q + 1 : ℕ) : ℝ) ≤ ((q + 2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.le_succ q)
  have hexp_nonpos : -(boundedMarginalExponent beta) ≤ 0 :=
    neg_nonpos.mpr (le_of_lt (boundedMarginalExponent_pos hbeta_pos))
  exact Real.rpow_le_rpow_of_nonpos hbase_pos hbase_le hexp_nonpos

/--
Generic source-algebra bridge: if finitely many rank terms are each
asymptotic to a nonzero coefficient times a common scale, then their sum is
asymptotic to the sum of those coefficients times the same scale.

This is the finite-sum step used after Lemma D.2 in the bounded branch of
Theorem 1(ii): the analytic work supplies one asymptotic equivalent for each
fixed rank/index term, and this theorem assembles the top-`k` loss.
-/
theorem finite_sum_asymptoticEquivalent_common_scale
    {ι : Type*} [Fintype ι]
    (term : ι → ℕ → ℝ) (coeff : ι → ℝ) (scale : ℕ → ℝ)
    (hcoeff_ne : ∀ i, coeff i ≠ 0)
    (htotal_ne : (∑ i : ι, coeff i) ≠ 0)
    (hscale_ne : ∀ᶠ n in atTop, scale n ≠ 0)
    (hterm :
      ∀ i,
        AppliedModelingLib.Math.AsymptoticEquivalent (term i)
          (fun n => coeff i * scale n)) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun n => ∑ i : ι, term i n)
      (fun n => (∑ i : ι, coeff i) * scale n) :=
  AppliedModelingLib.Math.finite_sum_asymptoticEquivalent_common_scale
    term coeff scale hcoeff_ne htotal_ne hscale_ne hterm

/--
If a main term is asymptotic to `coeff * scale` and a remainder is
`o(scale)`, their sum has the same asymptotic equivalent.
-/
theorem asymptoticEquivalent_add_negligible_common_scale
    (main remainder scale : ℕ → ℝ) (coeff : ℝ)
    (hcoeff_ne : coeff ≠ 0)
    (hscale_ne : ∀ᶠ n in atTop, scale n ≠ 0)
    (hmain :
      AppliedModelingLib.Math.AsymptoticEquivalent main
        (fun n => coeff * scale n))
    (hremainder :
      Tendsto (fun n => remainder n / scale n) atTop (nhds 0)) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun n => main n + remainder n)
      (fun n => coeff * scale n) :=
  AppliedModelingLib.Math.asymptoticEquivalent_add_negligible_common_scale
    main remainder scale coeff hcoeff_ne hscale_ne hmain hremainder

/-- The bounded branch's common scale, `a^(-1 / beta)`. -/
noncomputable def boundedTailScale (beta : ℝ) (a : ℕ) : ℝ := (a : ℝ) ^ (-(1 / beta))

theorem boundedTailScale_eventually_ne_zero (beta : ℝ) :
    ∀ᶠ a in atTop, boundedTailScale beta a ≠ 0 := by
  filter_upwards [eventually_gt_atTop 0] with a ha
  have ha_pos : 0 < (a : ℝ) := by exact_mod_cast ha
  exact (Real.rpow_pos_of_pos ha_pos (-(1 / beta))).ne'

theorem boundedTailScale_eventually_pos (beta : ℝ) :
    ∀ᶠ a in atTop, 0 < boundedTailScale beta a := by
  filter_upwards [eventually_gt_atTop 0] with a ha
  have ha_pos : 0 < (a : ℝ) := by exact_mod_cast ha
  exact Real.rpow_pos_of_pos ha_pos (-(1 / beta))

theorem boundedTailScale_tendsto_zero
    {beta : ℝ} (hbeta_pos : 0 < beta) :
    Tendsto (boundedTailScale beta) atTop (nhds 0) := by
  have hexp_pos : 0 < 1 / beta := one_div_pos.mpr hbeta_pos
  change Tendsto (fun a : ℕ => ((a : ℝ) ^ (-(1 / beta)))) atTop (nhds 0)
  simpa [one_div] using
    (tendsto_rpow_neg_atTop hexp_pos).comp
      tendsto_natCast_atTop_atTop

theorem boundedTailScale_div_succ_ratio_eventually_eq_rpow
    {beta : ℝ} (hbeta_pos : 0 < beta) :
    ∀ᶠ q in atTop,
      (boundedTailScale beta q / (((q + 1 : ℕ) : ℝ))) /
          boundedPowerMarginalScale beta q =
        ((((q + 1 : ℕ) : ℝ) / (q : ℝ)) ^ (1 / beta)) := by
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with q hq_pos_nat
  have hq_pos : 0 < (q : ℝ) := by exact_mod_cast hq_pos_nat
  have hq_nonneg : 0 ≤ (q : ℝ) := hq_pos.le
  have hq_ne : (q : ℝ) ≠ 0 := ne_of_gt hq_pos
  have hsucc_pos : 0 < (((q + 1 : ℕ) : ℝ)) := by positivity
  have hsucc_nonneg : 0 ≤ (((q + 1 : ℕ) : ℝ)) := hsucc_pos.le
  have hsucc_ne : (((q + 1 : ℕ) : ℝ)) ≠ 0 := ne_of_gt hsucc_pos
  have hbeta_ne : beta ≠ 0 := ne_of_gt hbeta_pos
  have hq_pow_ne : (q : ℝ) ^ (1 / beta) ≠ 0 :=
    (Real.rpow_pos_of_pos hq_pos (1 / beta)).ne'
  have hsucc_pow_ne : (((q + 1 : ℕ) : ℝ)) ^ (1 / beta) ≠ 0 :=
    (Real.rpow_pos_of_pos hsucc_pos (1 / beta)).ne'
  have heta :
      boundedMarginalExponent beta = 1 + 1 / beta := by
    unfold boundedMarginalExponent
    field_simp [hbeta_ne]
  rw [boundedTailScale, boundedPowerMarginalScale, heta,
    Real.rpow_neg hq_nonneg (1 / beta),
    Real.rpow_neg hsucc_nonneg (1 + 1 / beta),
    Real.rpow_add hsucc_pos 1 (1 / beta),
    Real.rpow_one,
    Real.div_rpow hsucc_nonneg hq_nonneg (1 / beta)]
  field_simp [hq_ne, hsucc_ne, hq_pow_ne, hsucc_pow_ne]

theorem boundedTailScale_div_succ_ratio_tendsto_one
    {beta : ℝ} (hbeta_pos : 0 < beta) :
    Tendsto
      (fun q : ℕ =>
        (boundedTailScale beta q / (((q + 1 : ℕ) : ℝ))) /
          boundedPowerMarginalScale beta q)
      atTop (nhds 1) := by
  have hratio :
      Tendsto
        (fun q : ℕ => (((q + 1 : ℕ) : ℝ) / (q : ℝ)))
        atTop (nhds 1) := by
    have h :=
      tendsto_add_mul_div_add_mul_atTop_nhds
        (𝕜 := ℝ) (1 : ℝ) (0 : ℝ) (1 : ℝ)
        (by norm_num : (1 : ℝ) ≠ 0)
    convert h using 1
    · ext q
      rw [Nat.cast_add, Nat.cast_one]
      ring
    · norm_num
  have hrpow :
      Tendsto
        (fun q : ℕ =>
          ((((q + 1 : ℕ) : ℝ) / (q : ℝ)) ^ (1 / beta)))
        atTop (nhds 1) := by
    have h :=
      hratio.rpow_const (p := 1 / beta)
        (Or.inl (by norm_num : (1 : ℝ) ≠ 0))
    simpa using h
  refine Tendsto.congr' ?_ hrpow
  filter_upwards
    [boundedTailScale_div_succ_ratio_eventually_eq_rpow hbeta_pos] with q hq
  exact hq.symm

/--
Finite-difference bridge from a bounded-source loss asymptotic to a forward
marginal asymptotic.

The discrete-drop hypothesis is deliberately explicit: the loss asymptotic
`A - h q ~ C q^(-1 / beta)` alone does not control first differences.
-/
theorem bounded_source_forward_marginal_asymptotic_of_loss_ae_and_scaled_drop
    {h : ℕ → ℝ} {A C beta : ℝ}
    (hbeta_pos : 0 < beta) (hC_pos : 0 < C)
    (hloss :
      AppliedModelingLib.Math.AsymptoticEquivalent
        (fun q => A - h q)
        (fun q => C * boundedTailScale beta q))
    (hdrop :
      Tendsto
        (fun q : ℕ =>
          (((q + 1 : ℕ) : ℝ) *
            (((A - h q) - (A - h (q + 1))) / (A - h q))))
        atTop (nhds (1 / beta))) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun q => h (q + 1) - h q)
      (fun q => (C / beta) * boundedPowerMarginalScale beta q) := by
  rw [AppliedModelingLib.Math.AsymptoticEquivalent] at hloss ⊢
  have hbeta_ne : beta ≠ 0 := ne_of_gt hbeta_pos
  have hC_ne : C ≠ 0 := ne_of_gt hC_pos
  have hcoeff_ne : C / beta ≠ 0 := div_ne_zero hC_ne hbeta_ne
  have hdrop_forward :
      Tendsto
        (fun q : ℕ =>
          (((q + 1 : ℕ) : ℝ) *
            ((h (q + 1) - h q) / (A - h q))))
        atTop (nhds (1 / beta)) := by
    refine Tendsto.congr' ?_ hdrop
    filter_upwards with q
    ring
  have hdrop_unit :
      Tendsto
        (fun q : ℕ =>
          beta *
            (((q + 1 : ℕ) : ℝ) *
              ((h (q + 1) - h q) / (A - h q))))
        atTop (nhds 1) := by
    have h := hdrop_forward.const_mul beta
    have hlim : beta * beta⁻¹ = 1 := by
      field_simp [hbeta_ne]
    simpa [one_div, hlim] using h
  have hscale := boundedTailScale_div_succ_ratio_tendsto_one hbeta_pos
  have hprod :
      Tendsto
        (fun q : ℕ =>
          (beta *
              (((q + 1 : ℕ) : ℝ) *
                ((h (q + 1) - h q) / (A - h q)))) *
            ((A - h q) / (C * boundedTailScale beta q)) *
            ((boundedTailScale beta q / (((q + 1 : ℕ) : ℝ))) /
              boundedPowerMarginalScale beta q))
        atTop (nhds 1) := by
    simpa using (hdrop_unit.mul hloss).mul hscale
  have hloss_ne_eventually :
      ∀ᶠ q in atTop, A - h q ≠ 0 := by
    filter_upwards [hloss.eventually_ne (by norm_num : (1 : ℝ) ≠ 0)] with q hratio_ne
    intro hloss_zero
    rw [hloss_zero] at hratio_ne
    simp at hratio_ne
  refine Tendsto.congr' ?_ hprod
  filter_upwards
    [hloss_ne_eventually,
      boundedTailScale_eventually_ne_zero beta] with q hloss_ne htail_ne
  have hsucc_ne : (((q + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hpower_ne : boundedPowerMarginalScale beta q ≠ 0 :=
    (boundedPowerMarginalScale_pos beta q).ne'
  field_simp [hloss_ne, htail_ne, hsucc_ne, hpower_ne, hC_ne, hbeta_ne,
    hcoeff_ne]

/--
If the adjacent drop of the endpoint loss is already known, converting it to
the source forward marginal is just algebra:
`(A - h q) - (A - h(q+1)) = h(q+1) - h(q)`.
-/
theorem bounded_source_forward_marginal_asymptotic_of_loss_adjacent_drop
    {h : ℕ → ℝ} {A D beta : ℝ}
    (hdrop :
      AppliedModelingLib.Math.AsymptoticEquivalent
        (fun q : ℕ => (A - h q) - (A - h (q + 1)))
        (fun q : ℕ => D * boundedPowerMarginalScale beta q)) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun q : ℕ => h (q + 1) - h q)
      (fun q : ℕ => D * boundedPowerMarginalScale beta q) := by
  exact AppliedModelingLib.Math.AsymptoticEquivalent.congr_left_eventually
    (by
      filter_upwards with q
      ring)
    hdrop

/--
Source-side bounded order-statistic marginal certificate.

This is the bounded analogue of the Pareto source certificate: prove the
top-`k` order-statistic marginal asymptotic once, then convert it to the
shared scaled-marginal interface consumed by the optimization layer.
-/
structure BoundedOrderStatisticScaledMarginalCertificate
    (μ : ℕ → ℕ → ℝ) (k : ℕ) (beta limitCoeff : ℝ) : Prop where
  beta_pos : 0 < beta
  k_pos : 0 < k
  coeff_pos : 0 < limitCoeff
  marginal_ratio_tendsto :
    Filter.Tendsto
      (fun q : ℕ =>
        (orderStatisticTopKSumFromMean μ k (q + 1) -
            orderStatisticTopKSumFromMean μ k q) /
          (boundedPowerMarginalScale beta q * limitCoeff))
      Filter.atTop (nhds 1)

namespace BoundedOrderStatisticScaledMarginalCertificate

def toOrderStatisticScaledMarginalCertificate
    {μ : ℕ → ℕ → ℝ} {k : ℕ} {beta limitCoeff : ℝ}
    (C : BoundedOrderStatisticScaledMarginalCertificate μ k beta limitCoeff) :
    AppliedModelingLib.Probability.OrderStatisticScaledMarginalCertificate μ k
      (boundedPowerMarginalScale beta) limitCoeff where
  k_pos := C.k_pos
  coeff_pos := C.coeff_pos
  scale_pos_eventually := by
    filter_upwards with q
    exact boundedPowerMarginalScale_pos beta q
  marginal_ratio_tendsto := C.marginal_ratio_tendsto

theorem marginal_asymptoticEquivalent
    {μ : ℕ → ℕ → ℝ} {k : ℕ} {beta limitCoeff : ℝ}
    (C : BoundedOrderStatisticScaledMarginalCertificate μ k beta limitCoeff) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun q : ℕ =>
        orderStatisticTopKSumFromMean μ k (q + 1) -
          orderStatisticTopKSumFromMean μ k q)
      (fun q : ℕ => boundedPowerMarginalScale beta q * limitCoeff) :=
  C.toOrderStatisticScaledMarginalCertificate.marginal_asymptoticEquivalent

def ofMarginalAsymptoticEquivalent
    {μ : ℕ → ℕ → ℝ} {k : ℕ} {beta limitCoeff : ℝ}
    (hbeta : 0 < beta) (hk : 0 < k) (hcoeff : 0 < limitCoeff)
    (hmargin :
      AppliedModelingLib.Math.AsymptoticEquivalent
        (fun q : ℕ =>
          orderStatisticTopKSumFromMean μ k (q + 1) -
            orderStatisticTopKSumFromMean μ k q)
        (fun q : ℕ => boundedPowerMarginalScale beta q * limitCoeff)) :
    BoundedOrderStatisticScaledMarginalCertificate μ k beta limitCoeff where
  beta_pos := hbeta
  k_pos := hk
  coeff_pos := hcoeff
  marginal_ratio_tendsto := hmargin

def ofConstMulScaleAsymptoticEquivalent
    {μ : ℕ → ℕ → ℝ} {k : ℕ} {beta limitCoeff : ℝ}
    (hbeta : 0 < beta) (hk : 0 < k) (hcoeff : 0 < limitCoeff)
    (hmargin :
      AppliedModelingLib.Math.AsymptoticEquivalent
        (fun q : ℕ =>
          orderStatisticTopKSumFromMean μ k (q + 1) -
            orderStatisticTopKSumFromMean μ k q)
        (fun q : ℕ => limitCoeff * boundedPowerMarginalScale beta q)) :
    BoundedOrderStatisticScaledMarginalCertificate μ k beta limitCoeff :=
  ofMarginalAsymptoticEquivalent hbeta hk hcoeff <| by
    rw [AppliedModelingLib.Math.AsymptoticEquivalent] at hmargin ⊢
    refine Filter.Tendsto.congr' ?_ hmargin
    filter_upwards with q
    rw [mul_comm]

def ofLossAsymptoticAndScaledDrop
    {μ : ℕ → ℕ → ℝ} {k : ℕ} {A C beta : ℝ}
    (hbeta : 0 < beta) (hk : 0 < k) (hC : 0 < C)
    (hloss :
      AppliedModelingLib.Math.AsymptoticEquivalent
        (fun q : ℕ => A - orderStatisticTopKSumFromMean μ k q)
        (fun q : ℕ => C * boundedTailScale beta q))
    (hdrop :
      Filter.Tendsto
        (fun q : ℕ =>
          (((q + 1 : ℕ) : ℝ) *
            (((A - orderStatisticTopKSumFromMean μ k q) -
              (A - orderStatisticTopKSumFromMean μ k (q + 1))) /
              (A - orderStatisticTopKSumFromMean μ k q))))
        Filter.atTop (nhds (1 / beta))) :
    BoundedOrderStatisticScaledMarginalCertificate μ k beta (C / beta) :=
  ofConstMulScaleAsymptoticEquivalent hbeta hk (div_pos hC hbeta) <|
    bounded_source_forward_marginal_asymptotic_of_loss_ae_and_scaled_drop
      hbeta hC hloss hdrop

def ofLossAdjacentDropAsymptotic
    {μ : ℕ → ℕ → ℝ} {k : ℕ} {A beta limitCoeff : ℝ}
    (hbeta : 0 < beta) (hk : 0 < k) (hcoeff : 0 < limitCoeff)
    (hdrop :
      AppliedModelingLib.Math.AsymptoticEquivalent
        (fun q : ℕ =>
          (A - orderStatisticTopKSumFromMean μ k q) -
            (A - orderStatisticTopKSumFromMean μ k (q + 1)))
        (fun q : ℕ => limitCoeff * boundedPowerMarginalScale beta q)) :
    BoundedOrderStatisticScaledMarginalCertificate μ k beta limitCoeff :=
  ofConstMulScaleAsymptoticEquivalent hbeta hk hcoeff <|
    bounded_source_forward_marginal_asymptotic_of_loss_adjacent_drop hdrop

noncomputable def toTopKScaledMarginalLimitCertificate
    {T : ℕ} {μ : ℕ → ℕ → ℝ} {k : ℕ} {beta limitCoeff : ℝ}
    (C : BoundedOrderStatisticScaledMarginalCertificate μ k beta limitCoeff) :
    TopKScaledMarginalLimitCertificate
      (TopKValueOracle.ofOrderStatisticMean T μ) k
      (boundedPowerMarginalScale beta)
      (fun _ : ItemType T => limitCoeff) := by
  simpa [topKExpectationOracleOfTopKValueOracle,
      AppliedModelingLib.Probability.TopKExpectationOracle.orderStatisticTopKExpectationOracle,
      TopKValueOracle.ofOrderStatisticMean]
    using
      C.toOrderStatisticScaledMarginalCertificate
        |>.toTopKExpectationScaledMarginalLimitCertificate (ItemType T)

end BoundedOrderStatisticScaledMarginalCertificate

/--
Generic iid bounded-source order-statistic mean sequence induced by a
one-dimensional base law.  Source-specific bounded laws instantiate this table
by proving reflected-CDF tail facts about `baseMeasure`.
-/
noncomputable def boundedIidOrderStatisticMeanSeq
    (baseMeasure : MeasureTheory.Measure ℝ) : ℕ → ℕ → ℝ :=
  expectedOrderStatisticMeanSeq
    (fun a => MeasureTheory.Measure.pi (fun _ : Fin a => baseMeasure))

/-- Top-`k` oracle induced by a generic iid bounded-source base law. -/
noncomputable def boundedIidOrderStatisticOracle
    (T : ℕ) (baseMeasure : MeasureTheory.Measure ℝ) : TopKValueOracle T :=
  TopKValueOracle.ofOrderStatisticMean T
    (boundedIidOrderStatisticMeanSeq baseMeasure)

/-- Consumption model induced by a generic iid bounded-source base law. -/
noncomputable def boundedIidOrderStatisticConsumptionModel {T : ℕ}
    (likelihood : ItemType T → ℝ) (k : ℕ)
    (baseMeasure : MeasureTheory.Measure ℝ) : ConsumptionModel T :=
  (boundedIidOrderStatisticOracle T baseMeasure).toConsumptionModel
    likelihood k

/--
For every count, the generic bounded iid order-statistic oracle marginal is the
difference of the expected top-`k` sums after adding one iid draw.
-/
theorem boundedIidOrderStatisticOracle_marginalTopK_eq_expectedSampleTopKSum_sub
    {T : ℕ} (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    {L M : ℝ}
    (h_base_bounds : ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    {k q : ℕ} (t : ItemType T) :
    (boundedIidOrderStatisticOracle T baseMeasure).marginalTopK k t q =
      AppliedModelingLib.Probability.expectedSampleTopKSum
          (MeasureTheory.Measure.pi (fun _ : Fin (q + 1) => baseMeasure)) k -
        AppliedModelingLib.Probability.expectedSampleTopKSum
          (MeasureTheory.Measure.pi (fun _ : Fin q => baseMeasure)) k := by
  classical
  let sampleMeasure : (a : ℕ) → MeasureTheory.Measure (Fin a → ℝ) :=
    fun a => MeasureTheory.Measure.pi (fun _ : Fin a => baseMeasure)
  have htop_succ :
      orderStatisticTopKSumFromMean
          (expectedOrderStatisticMeanSeq sampleMeasure) k (q + 1) =
        AppliedModelingLib.Probability.expectedSampleTopKSum
          (MeasureTheory.Measure.pi (fun _ : Fin (q + 1) => baseMeasure)) k := by
    refine
      AppliedModelingLib.Probability.expectedOrderStatisticMeanSeq_topKSum_eq_expectedSampleTopKSum
        sampleMeasure k (q + 1) ?_
    exact
      AppliedModelingLib.Probability.sampleOrderStatisticValue_topKRange_integrable_of_ae_bounds
        L M (MeasureTheory.Measure.pi (fun _ : Fin (q + 1) => baseMeasure))
        k
        (AppliedModelingLib.Probability.iidProductMeasure_forall_bounds_ae
          baseMeasure h_base_bounds)
  have htop_q :
      orderStatisticTopKSumFromMean
          (expectedOrderStatisticMeanSeq sampleMeasure) k q =
        AppliedModelingLib.Probability.expectedSampleTopKSum
          (MeasureTheory.Measure.pi (fun _ : Fin q => baseMeasure)) k := by
    refine
      AppliedModelingLib.Probability.expectedOrderStatisticMeanSeq_topKSum_eq_expectedSampleTopKSum
        sampleMeasure k q ?_
    exact
      AppliedModelingLib.Probability.sampleOrderStatisticValue_topKRange_integrable_of_ae_bounds
        L M (MeasureTheory.Measure.pi (fun _ : Fin q => baseMeasure)) k
        (AppliedModelingLib.Probability.iidProductMeasure_forall_bounds_ae
          baseMeasure h_base_bounds)
  simp [boundedIidOrderStatisticOracle, boundedIidOrderStatisticMeanSeq,
    TopKValueOracle.marginalTopK, TopKValueOracle.ofOrderStatisticMean,
    sampleMeasure, htop_succ, htop_q]

/--
Before top-`k` capacity binds, a generic bounded iid order-statistic oracle has
one-draw marginal equal to the base-law mean.
-/
theorem boundedIidOrderStatisticOracle_marginalTopK_eq_integral_before_capacity
    {T : ℕ} (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    {L M : ℝ}
    (h_base_bounds : ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    {k q : ℕ} (hq : q + 1 ≤ k) (t : ItemType T) :
    (boundedIidOrderStatisticOracle T baseMeasure).marginalTopK k t q =
      ∫ x, x ∂baseMeasure := by
  classical
  have h_base_int :
      MeasureTheory.Integrable (fun x : ℝ => x) baseMeasure := by
    exact MeasureTheory.Integrable.of_mem_Icc L M
      measurable_id.aemeasurable h_base_bounds
  let sampleMeasure : (a : ℕ) → MeasureTheory.Measure (Fin a → ℝ) :=
    fun a => MeasureTheory.Measure.pi (fun _ : Fin a => baseMeasure)
  have htop_succ :
      orderStatisticTopKSumFromMean
          (expectedOrderStatisticMeanSeq sampleMeasure) k (q + 1) =
        AppliedModelingLib.Probability.expectedSampleTopKSum
          (MeasureTheory.Measure.pi (fun _ : Fin (q + 1) => baseMeasure)) k := by
    refine
      AppliedModelingLib.Probability.expectedOrderStatisticMeanSeq_topKSum_eq_expectedSampleTopKSum
        sampleMeasure k (q + 1) ?_
    exact
      AppliedModelingLib.Probability.sampleOrderStatisticValue_topKRange_integrable_of_ae_bounds
        L M (MeasureTheory.Measure.pi (fun _ : Fin (q + 1) => baseMeasure))
        k
        (AppliedModelingLib.Probability.iidProductMeasure_forall_bounds_ae
          baseMeasure h_base_bounds)
  have htop_q :
      orderStatisticTopKSumFromMean
          (expectedOrderStatisticMeanSeq sampleMeasure) k q =
        AppliedModelingLib.Probability.expectedSampleTopKSum
          (MeasureTheory.Measure.pi (fun _ : Fin q => baseMeasure)) k := by
    refine
      AppliedModelingLib.Probability.expectedOrderStatisticMeanSeq_topKSum_eq_expectedSampleTopKSum
        sampleMeasure k q ?_
    exact
      AppliedModelingLib.Probability.sampleOrderStatisticValue_topKRange_integrable_of_ae_bounds
        L M (MeasureTheory.Measure.pi (fun _ : Fin q => baseMeasure)) k
        (AppliedModelingLib.Probability.iidProductMeasure_forall_bounds_ae
          baseMeasure h_base_bounds)
  have hsucc_eval :
      AppliedModelingLib.Probability.expectedSampleTopKSum
          (MeasureTheory.Measure.pi (fun _ : Fin (q + 1) => baseMeasure)) k =
        ((q + 1 : ℕ) : ℝ) * ∫ x, x ∂baseMeasure :=
    AppliedModelingLib.Probability.expectedSampleTopKSum_pi_eq_card_mul_integral_of_card_le
      baseMeasure h_base_int k hq
  have hq_le : q ≤ k := Nat.le_trans (Nat.le_succ q) hq
  have hq_eval :
      AppliedModelingLib.Probability.expectedSampleTopKSum
          (MeasureTheory.Measure.pi (fun _ : Fin q => baseMeasure)) k =
        (q : ℝ) * ∫ x, x ∂baseMeasure :=
    AppliedModelingLib.Probability.expectedSampleTopKSum_pi_eq_card_mul_integral_of_card_le
      baseMeasure h_base_int k hq_le
  simp [boundedIidOrderStatisticOracle, boundedIidOrderStatisticMeanSeq,
    TopKValueOracle.marginalTopK, TopKValueOracle.ofOrderStatisticMean,
    sampleMeasure, htop_succ, htop_q, hsucc_eval, hq_eval]
  ring

/--
Strict finite-prefix positivity for a bounded iid source before top-`k`
capacity binds.  For the paper's nonnegative support convention, the remaining
source step is to derive the positive one-draw mean from positive upper-tail
mass.
-/
theorem boundedIidOrderStatisticOracle_low_forward_pos_before_capacity_of_positive_mean
    {T : ℕ} (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    {L M : ℝ}
    (h_base_bounds : ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (hmean_pos : 0 < ∫ x, x ∂baseMeasure)
    {k q : ℕ} (hq : q + 1 ≤ k) (t : ItemType T) :
    0 < (boundedIidOrderStatisticOracle T baseMeasure).marginalTopK k t q := by
  rw [boundedIidOrderStatisticOracle_marginalTopK_eq_integral_before_capacity
    baseMeasure h_base_bounds hq t]
  exact hmean_pos

/--
Strict finite-prefix positivity for a bounded iid source with nonnegative
support and positive mass above a positive threshold.
-/
theorem
    boundedIidOrderStatisticOracle_low_forward_pos_before_capacity_of_nonnegative_support_and_positive_tail_mass
    {T : ℕ} (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    {L M a : ℝ}
    (h_base_bounds : ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (h_nonneg : ∀ᵐ y ∂baseMeasure, 0 ≤ y)
    (ha_pos : 0 < a)
    (hmass : 0 < baseMeasure (Set.Ici a))
    {k q : ℕ} (hq : q + 1 ≤ k) (t : ItemType T) :
    0 < (boundedIidOrderStatisticOracle T baseMeasure).marginalTopK k t q := by
  have hmean_pos : 0 < ∫ x, x ∂baseMeasure :=
    AppliedModelingLib.Probability.integral_id_pos_of_ae_nonneg_of_measure_Ici_pos_of_ae_bounds
      baseMeasure h_base_bounds h_nonneg ha_pos hmass
  exact
    boundedIidOrderStatisticOracle_low_forward_pos_before_capacity_of_positive_mean
      baseMeasure h_base_bounds hmean_pos hq t

/--
Strict finite-count positivity for every count under the paper's
nonnegative-support convention and reflected upper-tail power law.

The proof uses a positive rectangle: previous iid samples below `b` and the
new draw above `a`, where the reflected-CDF tail law supplies positive mass on
both sides with `0 < b < a`.
-/
theorem
    boundedIidOrderStatisticOracle_low_forward_pos_of_nonnegative_support_and_reflectedCDF_tail
    {T : ℕ} (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    {L M β c : ℝ}
    (h_base_bounds : ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (h_nonneg : ∀ᵐ y ∂baseMeasure, 0 ≤ y)
    (hM_pos : 0 < M)
    (tail :
      AppliedModelingLib.Probability.CDFPowerTailSandwich
        (AppliedModelingLib.Probability.reflectedCDFMass baseMeasure M) β c)
    {k q : ℕ} (hk_pos : 0 < k) (t : ItemType T) :
    0 < (boundedIidOrderStatisticOracle T baseMeasure).marginalTopK k t q := by
  rcases
      AppliedModelingLib.Probability.CDFPowerTailSandwich.exists_positive_Iio_Ici_mass_gap_of_reflectedCDFMass_tail
        tail hM_pos with
    ⟨b, a, hb_pos, hba, hlow, hhigh⟩
  have h_bounds_0M :
      ∀ᵐ y ∂baseMeasure, 0 ≤ y ∧ y ≤ M := by
    filter_upwards [h_nonneg, h_base_bounds] with y hy_nonneg hy_bounds
    exact ⟨hy_nonneg, hy_bounds.2⟩
  rw [boundedIidOrderStatisticOracle_marginalTopK_eq_expectedSampleTopKSum_sub
    baseMeasure h_base_bounds t]
  exact
    AppliedModelingLib.Probability.expectedSampleTopKSum_pi_succ_sub_pos_of_mass_gap
      baseMeasure h_bounds_0M hM_pos.le hb_pos.le hba hlow hhigh hk_pos

/--
Strict finite-prefix positivity for a bounded iid source under the paper's
nonnegative-support convention and reflected upper-tail power law.
-/
theorem
    boundedIidOrderStatisticOracle_low_forward_pos_before_capacity_of_nonnegative_support_and_reflectedCDF_tail
    {T : ℕ} (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    {L M β c : ℝ}
    (h_base_bounds : ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (h_nonneg : ∀ᵐ y ∂baseMeasure, 0 ≤ y)
    (hM_pos : 0 < M)
    (tail :
      AppliedModelingLib.Probability.CDFPowerTailSandwich
        (AppliedModelingLib.Probability.reflectedCDFMass baseMeasure M) β c)
    {k q : ℕ} (hq : q + 1 ≤ k) (t : ItemType T) :
    0 < (boundedIidOrderStatisticOracle T baseMeasure).marginalTopK k t q := by
  rcases
      AppliedModelingLib.Probability.CDFPowerTailSandwich.exists_positive_Ici_mass_of_reflectedCDFMass_tail
        tail hM_pos with
    ⟨a, ha_pos, hmass⟩
  exact
    boundedIidOrderStatisticOracle_low_forward_pos_before_capacity_of_nonnegative_support_and_positive_tail_mass
      baseMeasure h_base_bounds h_nonneg ha_pos hmass hq t

/--
Fixed-rank loss coefficient for the exact reflected-power bounded source.

If `Y = 1 - X` has CDF `P[Y ≤ x] = x^β` on `[0,1]`, then the `r`-th
zero-based bottom order statistic of `Y` has expectation
`boundedReflectedPowerRankLossCoeff β r *
 boundedReflectedPowerCommonLossFactor β q` among `q` samples.
-/
noncomputable def boundedReflectedPowerRankLossCoeff
    (beta : ℝ) (r : ℕ) : ℝ :=
  Real.Gamma ((r : ℝ) + 1 + 1 / beta) /
    Real.Gamma ((r : ℝ) + 1)

/-- Common finite-sample gamma-ratio factor for reflected-power bounded losses. -/
noncomputable def boundedReflectedPowerCommonLossFactor
    (beta : ℝ) (q : ℕ) : ℝ :=
  Real.Gamma ((q : ℝ) + 1) /
    Real.Gamma ((q : ℝ) + 1 + 1 / beta)

/-- Expected zero-based bottom-rank reflected loss for the exact reflected-power table. -/
noncomputable def boundedReflectedPowerRankLossMean
    (beta : ℝ) (r q : ℕ) : ℝ :=
  boundedReflectedPowerRankLossCoeff beta r *
    boundedReflectedPowerCommonLossFactor beta q

/--
Definition-3-shaped order-statistic mean table for the exact reflected-power
bounded source on `[0,1]`.

The table is bottom-indexed in the paper's convention for `X`; internally it
uses the corresponding bottom ranks of `Y = 1 - X`.
-/
noncomputable def boundedReflectedPowerOrderStatisticMean
    (beta : ℝ) (rank sampleSize : ℕ) : ℝ :=
  1 - boundedReflectedPowerRankLossMean beta (sampleSize - rank) sampleSize

/-- Top-`k` endpoint-loss coefficient for the reflected-power bounded source. -/
noncomputable def boundedReflectedPowerTopKLossCoeff
    (beta : ℝ) (k : ℕ) : ℝ :=
  ∑ i : Fin k, boundedReflectedPowerRankLossCoeff beta i.val

/--
Concrete iid source bridge for the reflected-power bounded model: the expected
zero-based bottom rank of the reflected losses `1 - X` is exactly the
gamma-ratio rank-loss table used by the bounded branch.
-/
theorem boundedReflectedPowerProductMeasure_expectedReflectedAscendingOrderStatistic_eq_rankLossMean
    {beta : ℝ} (hbeta_pos : 0 < beta) {q : ℕ} (rank : Fin q) :
    (∫ sample : Fin q → ℝ,
        AppliedModelingLib.Probability.ascendingOrderStatistic
          (AppliedModelingLib.Probability.reflectedSample 1 sample) rank
        ∂MeasureTheory.Measure.pi
          (fun _ : Fin q => boundedReflectedPowerSourceMeasure beta)) =
      boundedReflectedPowerRankLossMean beta rank.val q := by
  classical
  let μ : MeasureTheory.Measure (Fin q → ℝ) :=
    MeasureTheory.Measure.pi
      (fun _ : Fin q => boundedReflectedPowerSourceMeasure beta)
  let tail : ℝ → ℝ := fun x =>
    μ.real
      {sample : Fin q → ℝ |
        x < AppliedModelingLib.Probability.ascendingOrderStatistic
          (AppliedModelingLib.Probability.reflectedSample 1 sample) rank}
  have h_nonneg :
      (fun _sample : Fin q → ℝ => (0 : ℝ)) ≤ᵐ[μ]
        fun sample =>
          AppliedModelingLib.Probability.ascendingOrderStatistic
            (AppliedModelingLib.Probability.reflectedSample 1 sample) rank := by
    simpa [μ] using
      boundedReflectedPowerProductMeasure_reflectedAscendingOrderStatistic_nonnegative_ae
        hbeta_pos rank
  have h_int :
      MeasureTheory.Integrable
        (fun sample : Fin q → ℝ =>
          AppliedModelingLib.Probability.ascendingOrderStatistic
            (AppliedModelingLib.Probability.reflectedSample 1 sample) rank) μ := by
    simpa [μ] using
      boundedReflectedPowerProductMeasure_reflectedAscendingOrderStatistic_integrable
        hbeta_pos rank
  have hlayer :
      (∫ sample : Fin q → ℝ,
          AppliedModelingLib.Probability.ascendingOrderStatistic
            (AppliedModelingLib.Probability.reflectedSample 1 sample) rank ∂μ) =
        ∫ x in Set.Ioi (0 : ℝ), tail x := by
    simpa [tail] using h_int.integral_eq_integral_meas_lt h_nonneg
  have hbelow_Ioo : MeasureTheory.IntegrableOn tail (Set.Ioo (0 : ℝ) 1) := by
    simpa [tail, μ] using
      boundedReflectedPowerProductMeasure_reflectedAscendingOrderStatistic_tail_integrableOn_Ioo_zero_one
        hbeta_pos rank
  have hbelow_Ioc : MeasureTheory.IntegrableOn tail (Set.Ioc (0 : ℝ) 1) :=
    (integrableOn_Ioc_iff_integrableOn_Ioo
      (μ := MeasureTheory.volume) (f := tail) (a := 0) (b := 1)).2
      hbelow_Ioo
  have habove_Ioi : MeasureTheory.IntegrableOn tail (Set.Ioi (1 : ℝ)) := by
    simpa [tail, μ] using
      boundedReflectedPowerProductMeasure_reflectedAscendingOrderStatistic_tail_integrableOn_Ioi_one
        hbeta_pos rank
  have hsplit :
      ∫ x in (Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ)), tail x =
        (∫ x in Set.Ioc (0 : ℝ) 1, tail x) +
          ∫ x in Set.Ioi (1 : ℝ), tail x := by
    exact MeasureTheory.setIntegral_union
      Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hbelow_Ioc habove_Ioi
  rw [Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)] at hsplit
  have hbelow_eq :
      ∫ x in Set.Ioc (0 : ℝ) 1, tail x =
        boundedReflectedPowerRankLossMean beta rank.val q := by
    calc
      ∫ x in Set.Ioc (0 : ℝ) 1, tail x
          = ∫ x in Set.Ioo (0 : ℝ) 1, tail x := by
            rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]
      _ =
          ∑ j ∈ Finset.Icc 0 rank.val,
            (Nat.choose q j : ℝ) *
              ((1 / beta) *
                ProbabilityTheory.beta
                  ((j : ℝ) + 1 / beta)
                  (((q - j : ℕ) : ℝ) + 1)) := by
            simpa [tail, μ] using
              boundedReflectedPowerProductMeasure_reflectedAscendingOrderStatistic_tail_integral_Ioo_zero_one
                hbeta_pos rank
      _ = boundedReflectedPowerRankLossMean beta rank.val q := by
            have hinv_pos : 0 < 1 / beta := one_div_pos.mpr hbeta_pos
            have hsum :=
              AppliedModelingLib.Math.sum_choose_mul_s_mul_beta_add_eq_gamma_ratio
                (s := 1 / beta) hinv_pos
                (r := rank.val) (q := q) (Nat.le_of_lt rank.isLt)
            simpa [boundedReflectedPowerRankLossMean,
              boundedReflectedPowerRankLossCoeff,
              boundedReflectedPowerCommonLossFactor,
              add_assoc, add_comm, add_left_comm, mul_assoc, mul_left_comm,
              mul_comm] using hsum
  have habove_eq : ∫ x in Set.Ioi (1 : ℝ), tail x = 0 := by
    calc
      ∫ x in Set.Ioi (1 : ℝ), tail x =
          ∫ _x in Set.Ioi (1 : ℝ), (0 : ℝ) := by
            refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
            intro x hx
            dsimp [tail, μ]
            exact
              boundedReflectedPowerProductMeasure_reflectedAscendingOrderStatistic_gt_real_of_one_lt
                hbeta_pos hx rank
      _ = 0 := by simp
  calc
    (∫ sample : Fin q → ℝ,
        AppliedModelingLib.Probability.ascendingOrderStatistic
          (AppliedModelingLib.Probability.reflectedSample 1 sample) rank
        ∂MeasureTheory.Measure.pi
          (fun _ : Fin q => boundedReflectedPowerSourceMeasure beta))
        =
        ∫ sample : Fin q → ℝ,
          AppliedModelingLib.Probability.ascendingOrderStatistic
            (AppliedModelingLib.Probability.reflectedSample 1 sample) rank ∂μ := by
          rfl
    _ = ∫ x in Set.Ioi (0 : ℝ), tail x := hlayer
    _ = (∫ x in Set.Ioc (0 : ℝ) 1, tail x) +
          ∫ x in Set.Ioi (1 : ℝ), tail x := hsplit
    _ = boundedReflectedPowerRankLossMean beta rank.val q := by
          rw [hbelow_eq, habove_eq, add_zero]

/-- Expected upper order statistic for the concrete bounded reflected-power source. -/
theorem boundedReflectedPowerProductMeasure_expectedUpperOrderStatistic_eq
    {beta : ℝ} (hbeta_pos : 0 < beta)
    {q : ℕ} (rankFromTop : Fin q) :
    AppliedModelingLib.Probability.expectedUpperOrderStatistic
        (MeasureTheory.Measure.pi
          (fun _ : Fin q => boundedReflectedPowerSourceMeasure beta))
        rankFromTop =
      boundedReflectedPowerOrderStatisticMean
        beta (q - rankFromTop.val) q := by
  let μ : MeasureTheory.Measure (Fin q → ℝ) :=
    MeasureTheory.Measure.pi
      (fun _ : Fin q => boundedReflectedPowerSourceMeasure beta)
  have h_int :
      MeasureTheory.Integrable
        (fun sample : Fin q → ℝ =>
          AppliedModelingLib.Probability.ascendingOrderStatistic
            (AppliedModelingLib.Probability.reflectedSample 1 sample) rankFromTop) μ := by
    simpa [μ] using
      boundedReflectedPowerProductMeasure_reflectedAscendingOrderStatistic_integrable
        hbeta_pos rankFromTop
  calc
    AppliedModelingLib.Probability.expectedUpperOrderStatistic
        (MeasureTheory.Measure.pi
          (fun _ : Fin q => boundedReflectedPowerSourceMeasure beta))
        rankFromTop
        =
        AppliedModelingLib.Probability.expectedUpperOrderStatistic μ rankFromTop := by
          rfl
    _ =
        1 -
          ∫ sample : Fin q → ℝ,
            AppliedModelingLib.Probability.ascendingOrderStatistic
              (AppliedModelingLib.Probability.reflectedSample 1 sample) rankFromTop ∂μ := by
          exact
            AppliedModelingLib.Probability.expectedUpperOrderStatistic_eq_endpoint_sub_expectedReflectedAscending
              1 μ rankFromTop h_int
    _ = 1 - boundedReflectedPowerRankLossMean beta rankFromTop.val q := by
          rw [boundedReflectedPowerProductMeasure_expectedReflectedAscendingOrderStatistic_eq_rankLossMean
            hbeta_pos rankFromTop]
    _ =
        boundedReflectedPowerOrderStatisticMean
          beta (q - rankFromTop.val) q := by
          have hsub : q - (q - rankFromTop.val) = rankFromTop.val := by
            omega
          simp [boundedReflectedPowerOrderStatisticMean, hsub]

/-- Concrete Definition-3 mean table induced by iid reflected-power bounded samples. -/
noncomputable def boundedReflectedPowerSourceIidOrderStatisticMeanSeq
    (beta : ℝ) (rank sampleSize : ℕ) : ℝ :=
  AppliedModelingLib.Probability.expectedOrderStatisticMeanSeq
    (fun a => MeasureTheory.Measure.pi
      (fun _ : Fin a => boundedReflectedPowerSourceMeasure beta))
    rank sampleSize

/--
The concrete iid reflected-power source induces exactly the gamma-ratio
bounded order-statistic mean table.
-/
theorem
    boundedReflectedPowerSourceIidOrderStatisticMeanSeq_eq_boundedReflectedPowerOrderStatisticMean
    {beta : ℝ} (hbeta_pos : 0 < beta) {q r : ℕ} (hrq : r < q) :
    boundedReflectedPowerSourceIidOrderStatisticMeanSeq beta (q - r) q =
      boundedReflectedPowerOrderStatisticMean beta (q - r) q := by
  calc
    boundedReflectedPowerSourceIidOrderStatisticMeanSeq beta (q - r) q
        =
        AppliedModelingLib.Probability.expectedUpperOrderStatistic
          (MeasureTheory.Measure.pi
            (fun _ : Fin q => boundedReflectedPowerSourceMeasure beta))
          ⟨r, hrq⟩ := by
          simpa [boundedReflectedPowerSourceIidOrderStatisticMeanSeq,
            AppliedModelingLib.Probability.expectedOrderStatisticMeanSeq] using
            AppliedModelingLib.Probability.expectedSampleOrderStatisticMean_eq_expectedUpperOrderStatistic_of_rank_from_top
              (μ := MeasureTheory.Measure.pi
                (fun _ : Fin q => boundedReflectedPowerSourceMeasure beta))
              (a := q) (r := r) hrq
    _ = boundedReflectedPowerOrderStatisticMean beta (q - r) q :=
        boundedReflectedPowerProductMeasure_expectedUpperOrderStatistic_eq
          hbeta_pos ⟨r, hrq⟩

/-- Top-`k` sum equality for the concrete iid reflected-power source table. -/
theorem
    boundedReflectedPowerSourceIidOrderStatisticTopKSum_eq_boundedReflectedPowerOrderStatisticTopKSum
    {beta : ℝ} (hbeta_pos : 0 < beta) (k q : ℕ) :
    orderStatisticTopKSumFromMean
        (boundedReflectedPowerSourceIidOrderStatisticMeanSeq beta) k q =
      orderStatisticTopKSumFromMean
        (boundedReflectedPowerOrderStatisticMean beta) k q := by
  rw [orderStatisticTopKSumFromMean_eq_bottomIndexed_sum,
    orderStatisticTopKSumFromMean_eq_bottomIndexed_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hiq : i < q :=
    lt_of_lt_of_le (Finset.mem_range.mp hi) (min_le_right k q)
  exact
    boundedReflectedPowerSourceIidOrderStatisticMeanSeq_eq_boundedReflectedPowerOrderStatisticMean
      hbeta_pos hiq

/-- The concrete iid reflected-power bounded source oracle. -/
noncomputable def boundedReflectedPowerSourceIidOrderStatisticOracle
    (T : ℕ) (beta : ℝ) : TopKValueOracle T :=
  TopKValueOracle.ofOrderStatisticMean T
    (boundedReflectedPowerSourceIidOrderStatisticMeanSeq beta)

theorem boundedReflectedPowerRankLossCoeff_pos
    {beta : ℝ} (hbeta_pos : 0 < beta) (r : ℕ) :
    0 < boundedReflectedPowerRankLossCoeff beta r := by
  unfold boundedReflectedPowerRankLossCoeff
  have hinv_pos : 0 < 1 / beta := one_div_pos.mpr hbeta_pos
  exact div_pos
    (Real.Gamma_pos_of_pos (by positivity))
    (Real.Gamma_pos_of_pos (by positivity))

theorem boundedReflectedPowerCommonLossFactor_pos
    {beta : ℝ} (hbeta_pos : 0 < beta) (q : ℕ) :
    0 < boundedReflectedPowerCommonLossFactor beta q := by
  unfold boundedReflectedPowerCommonLossFactor
  have hinv_pos : 0 < 1 / beta := one_div_pos.mpr hbeta_pos
  exact div_pos
    (Real.Gamma_pos_of_pos (by positivity))
    (Real.Gamma_pos_of_pos (by positivity))

theorem boundedReflectedPowerTopKLossCoeff_pos
    {beta : ℝ} (hbeta_pos : 0 < beta) {k : ℕ} (hk : 0 < k) :
    0 < boundedReflectedPowerTopKLossCoeff beta k := by
  unfold boundedReflectedPowerTopKLossCoeff
  refine Finset.sum_pos ?_ ?_
  · intro i _hi
    exact boundedReflectedPowerRankLossCoeff_pos hbeta_pos i.val
  · exact ⟨⟨0, hk⟩, Finset.mem_univ _⟩

/-- Exact recurrence for the common reflected-power gamma-ratio loss factor. -/
theorem boundedReflectedPowerCommonLossFactor_succ_div_self
    {beta : ℝ} (hbeta_pos : 0 < beta) (q : ℕ) :
    boundedReflectedPowerCommonLossFactor beta (q + 1) /
        boundedReflectedPowerCommonLossFactor beta q =
      (((q + 1 : ℕ) : ℝ) / ((q : ℝ) + 1 + 1 / beta)) := by
  have hinv_pos : 0 < 1 / beta := one_div_pos.mpr hbeta_pos
  have hq1_pos : 0 < (q : ℝ) + 1 := by positivity
  have harg_pos : 0 < (q : ℝ) + 1 + 1 / beta := by positivity
  have hgamma_q1_ne : Real.Gamma ((q : ℝ) + 1) ≠ 0 :=
    (Real.Gamma_pos_of_pos hq1_pos).ne'
  have hgamma_arg_ne : Real.Gamma ((q : ℝ) + 1 + 1 / beta) ≠ 0 :=
    (Real.Gamma_pos_of_pos harg_pos).ne'
  have harg_succ_pos : 0 < ((q + 1 : ℕ) : ℝ) + 1 + 1 / beta := by
    positivity
  have hgamma_arg_succ_ne :
      Real.Gamma (((q + 1 : ℕ) : ℝ) + 1 + 1 / beta) ≠ 0 :=
    (Real.Gamma_pos_of_pos harg_succ_pos).ne'
  have hgamma_num_succ :
      Real.Gamma (((q + 1 : ℕ) : ℝ) + 1) =
        (((q + 1 : ℕ) : ℝ) *
          Real.Gamma (((q + 1 : ℕ) : ℝ))) :=
    Real.Gamma_add_one (by positivity : (((q + 1 : ℕ) : ℝ)) ≠ 0)
  have hgamma_den_succ :
      Real.Gamma (((q + 1 : ℕ) : ℝ) + 1 + 1 / beta) =
        (((q : ℝ) + 1 + 1 / beta) *
          Real.Gamma ((q : ℝ) + 1 + 1 / beta)) := by
    rw [show (((q + 1 : ℕ) : ℝ) + 1 + 1 / beta) =
          ((q : ℝ) + 1 + 1 / beta) + 1 by
        rw [Nat.cast_add, Nat.cast_one]
        ring]
    exact Real.Gamma_add_one (ne_of_gt harg_pos)
  unfold boundedReflectedPowerCommonLossFactor
  rw [hgamma_num_succ, hgamma_den_succ]
  rw [show (((q + 1 : ℕ) : ℝ)) = (q : ℝ) + 1 by
    rw [Nat.cast_add, Nat.cast_one]]
  field_simp [hgamma_q1_ne, hgamma_arg_ne, hgamma_arg_succ_ne]

/-- The common reflected-power loss factor has the bounded-tail scale. -/
theorem boundedReflectedPowerCommonLossFactor_asymptoticEquivalent
    {beta : ℝ} (hbeta_pos : 0 < beta) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (boundedReflectedPowerCommonLossFactor beta)
      (boundedTailScale beta) := by
  have hinv_pos : 0 < 1 / beta := one_div_pos.mpr hbeta_pos
  change
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun q : ℕ =>
        Real.Gamma ((q : ℝ) + 1) /
          Real.Gamma ((q : ℝ) + 1 + 1 / beta))
      (fun q : ℕ => (q : ℝ) ^ (-(1 / beta)))
  simpa [one_div] using
    AppliedModelingLib.Math.gamma_ratio_nat_add_one_add_asymptoticEquivalent hinv_pos

/--
For valid sample counts, the reflected-power top-`k` endpoint loss is exactly
one finite coefficient times the common gamma-ratio factor.
-/
theorem boundedReflectedPowerOrderStatistic_topK_loss_eq
    (beta : ℝ) {k q : ℕ} (hq : k ≤ q) :
    (k : ℝ) -
        orderStatisticTopKSumFromMean
          (boundedReflectedPowerOrderStatisticMean beta) k q =
      boundedReflectedPowerTopKLossCoeff beta k *
        boundedReflectedPowerCommonLossFactor beta q := by
  rw [orderStatisticTopKSumFromMean_eq_fin_sum_of_le
      (boundedReflectedPowerOrderStatisticMean beta) hq]
  let factor := boundedReflectedPowerCommonLossFactor beta q
  have hterm :
      ∀ i : Fin k,
        boundedReflectedPowerOrderStatisticMean beta (q - i.val) q =
          1 - boundedReflectedPowerRankLossCoeff beta i.val * factor := by
    intro i
    have hiq : i.val ≤ q := by omega
    have hsub : q - (q - i.val) = i.val := by omega
    simp [boundedReflectedPowerOrderStatisticMean,
      boundedReflectedPowerRankLossMean, factor, hsub]
  have hsum :
      (∑ i : Fin k,
        (1 - boundedReflectedPowerRankLossCoeff beta i.val * factor)) =
        (k : ℝ) - boundedReflectedPowerTopKLossCoeff beta k * factor := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, ← Finset.sum_mul]
    simp [boundedReflectedPowerTopKLossCoeff, nsmul_eq_mul]
  calc
    (k : ℝ) -
        ∑ i : Fin k,
          boundedReflectedPowerOrderStatisticMean beta (q - i.val) q
        =
      (k : ℝ) -
        ∑ i : Fin k,
          (1 - boundedReflectedPowerRankLossCoeff beta i.val * factor) := by
            congr 1
            exact Finset.sum_congr rfl (fun i _hi => hterm i)
    _ = boundedReflectedPowerTopKLossCoeff beta k * factor := by
          rw [hsum]
          ring

/--
Exact finite forward marginal for the reflected-power bounded order-statistic
table once the fixed top-`k` prefix has entered the stable `k <= q` range.
-/
theorem boundedReflectedPowerOrderStatistic_topK_forward_marginal_eq
    {beta : ℝ} (hbeta_pos : 0 < beta) {k q : ℕ} (hq : k ≤ q) :
    orderStatisticTopKSumFromMean
        (boundedReflectedPowerOrderStatisticMean beta) k (q + 1) -
      orderStatisticTopKSumFromMean
        (boundedReflectedPowerOrderStatisticMean beta) k q =
      boundedReflectedPowerTopKLossCoeff beta k *
        boundedReflectedPowerCommonLossFactor beta q *
          ((1 / beta) / ((q : ℝ) + 1 + 1 / beta)) := by
  let C := boundedReflectedPowerTopKLossCoeff beta k
  let factor := boundedReflectedPowerCommonLossFactor beta
  have hq_succ : k ≤ q + 1 := by omega
  have hfactor_pos : 0 < factor q :=
    boundedReflectedPowerCommonLossFactor_pos hbeta_pos q
  have hfactor_ne : factor q ≠ 0 := hfactor_pos.ne'
  have hden_pos : 0 < (q : ℝ) + 1 + 1 / beta := by
    have hinv_pos : 0 < 1 / beta := one_div_pos.mpr hbeta_pos
    positivity
  have hden_ne : (q : ℝ) + 1 + 1 / beta ≠ 0 := hden_pos.ne'
  have hrec :
      factor (q + 1) / factor q =
        (((q + 1 : ℕ) : ℝ) / ((q : ℝ) + 1 + 1 / beta)) :=
    boundedReflectedPowerCommonLossFactor_succ_div_self hbeta_pos q
  have hfactor_succ :
      factor (q + 1) =
        (((q + 1 : ℕ) : ℝ) / ((q : ℝ) + 1 + 1 / beta)) * factor q := by
    rw [← hrec]
    field_simp [hfactor_ne]
  have hloss_q :=
    boundedReflectedPowerOrderStatistic_topK_loss_eq
      (beta := beta) (k := k) (q := q) hq
  have hloss_succ :=
    boundedReflectedPowerOrderStatistic_topK_loss_eq
      (beta := beta) (k := k) (q := q + 1) hq_succ
  calc
    orderStatisticTopKSumFromMean
        (boundedReflectedPowerOrderStatisticMean beta) k (q + 1) -
      orderStatisticTopKSumFromMean
        (boundedReflectedPowerOrderStatisticMean beta) k q =
        ((k : ℝ) -
          orderStatisticTopKSumFromMean
            (boundedReflectedPowerOrderStatisticMean beta) k q) -
          ((k : ℝ) -
            orderStatisticTopKSumFromMean
              (boundedReflectedPowerOrderStatisticMean beta) k (q + 1)) := by
          ring
    _ = C * factor q - C * factor (q + 1) := by
          rw [hloss_q, hloss_succ]
    _ = C * factor q *
          ((1 / beta) / ((q : ℝ) + 1 + 1 / beta)) := by
          rw [hfactor_succ]
          rw [show (((q + 1 : ℕ) : ℝ)) = (q : ℝ) + 1 by
            rw [Nat.cast_add, Nat.cast_one]]
          field_simp [hden_ne]
          ring

/-- Positivity of the stable reflected-power bounded top-`k` forward marginal. -/
theorem boundedReflectedPowerOrderStatistic_topK_forward_marginal_pos_of_le
    {beta : ℝ} (hbeta_pos : 0 < beta) {k q : ℕ}
    (hk : 0 < k) (hq : k ≤ q) :
    0 <
      orderStatisticTopKSumFromMean
          (boundedReflectedPowerOrderStatisticMean beta) k (q + 1) -
        orderStatisticTopKSumFromMean
          (boundedReflectedPowerOrderStatisticMean beta) k q := by
  rw [boundedReflectedPowerOrderStatistic_topK_forward_marginal_eq
    hbeta_pos hq]
  have hcoeff_pos :
      0 < boundedReflectedPowerTopKLossCoeff beta k :=
    boundedReflectedPowerTopKLossCoeff_pos hbeta_pos hk
  have hfactor_pos :
      0 < boundedReflectedPowerCommonLossFactor beta q :=
    boundedReflectedPowerCommonLossFactor_pos hbeta_pos q
  have hinv_pos : 0 < 1 / beta := one_div_pos.mpr hbeta_pos
  have hden_pos : 0 < (q : ℝ) + 1 + 1 / beta := by positivity
  exact mul_pos (mul_pos hcoeff_pos hfactor_pos)
    (div_pos hinv_pos hden_pos)

/-- Common first-difference factor for the reflected-power bounded table. -/
noncomputable def boundedReflectedPowerCommonMarginalFactor
    (beta : ℝ) (q : ℕ) : ℝ :=
  boundedReflectedPowerCommonLossFactor beta q *
    ((1 / beta) / ((q : ℝ) + 1 + 1 / beta))

theorem boundedReflectedPowerCommonMarginalFactor_pos
    {beta : ℝ} (hbeta_pos : 0 < beta) (q : ℕ) :
    0 < boundedReflectedPowerCommonMarginalFactor beta q := by
  unfold boundedReflectedPowerCommonMarginalFactor
  have hfactor_pos :
      0 < boundedReflectedPowerCommonLossFactor beta q :=
    boundedReflectedPowerCommonLossFactor_pos hbeta_pos q
  have hinv_pos : 0 < 1 / beta := one_div_pos.mpr hbeta_pos
  have hden_pos : 0 < (q : ℝ) + 1 + 1 / beta := by positivity
  exact mul_pos hfactor_pos (div_pos hinv_pos hden_pos)

theorem boundedReflectedPowerCommonMarginalFactor_eq_gamma_ratio
    {beta : ℝ} (hbeta_pos : 0 < beta) (q : ℕ) :
    boundedReflectedPowerCommonMarginalFactor beta q =
      (1 / beta) *
        (Real.Gamma (((q + 1 : ℕ) : ℝ)) /
          Real.Gamma ((((q + 1 : ℕ) : ℝ)) + boundedMarginalExponent beta)) := by
  have hbeta_ne : beta ≠ 0 := hbeta_pos.ne'
  have hs_pos : 0 < 1 / beta := one_div_pos.mpr hbeta_pos
  have hx_pos : 0 < (((q + 1 : ℕ) : ℝ)) := by positivity
  have hx_s_pos : 0 < (((q + 1 : ℕ) : ℝ)) + 1 / beta := by positivity
  have hΓ_ne :
      Real.Gamma ((((q + 1 : ℕ) : ℝ)) + 1 / beta) ≠ 0 :=
    (Real.Gamma_pos_of_pos hx_s_pos).ne'
  have hden_ne :
      ((q : ℝ) + 1 + 1 / beta) ≠ 0 := by positivity
  have hη :
      boundedMarginalExponent beta = 1 + 1 / beta := by
    unfold boundedMarginalExponent
    field_simp [hbeta_ne]
  unfold boundedReflectedPowerCommonMarginalFactor
    boundedReflectedPowerCommonLossFactor
  rw [hη]
  rw [show (((q + 1 : ℕ) : ℝ)) = (q : ℝ) + 1 by
    rw [Nat.cast_add, Nat.cast_one]]
  rw [show ((q : ℝ) + 1 + (1 + 1 / beta)) =
      ((q : ℝ) + 1 + 1 / beta) + 1 by ring]
  rw [Real.Gamma_add_one hden_ne]
  field_simp [hΓ_ne, hden_ne]

theorem boundedReflectedPowerCommonMarginalFactor_le_pred_rpow_neg
    {beta : ℝ} (hbeta_pos : 0 < beta) {q : ℕ} (hq : 0 < q) :
    boundedReflectedPowerCommonMarginalFactor beta q ≤
      (1 / beta) * ((q : ℝ) ^ (-(boundedMarginalExponent beta))) := by
  let x : ℝ := (((q + 1 : ℕ) : ℝ))
  let η : ℝ := boundedMarginalExponent beta
  have hx_gt_one : 1 < x := by
    dsimp [x]
    exact_mod_cast Nat.succ_lt_succ hq
  have hη_pos : 0 < η := by
    dsimp [η]
    exact boundedMarginalExponent_pos hbeta_pos
  have hinv_nonneg : 0 ≤ 1 / beta := (one_div_pos.mpr hbeta_pos).le
  have hratio :=
    AppliedModelingLib.Math.gamma_div_gamma_add_le_pred_rpow_neg_of_pos
      (x := x) (s := η) hx_gt_one hη_pos
  calc
    boundedReflectedPowerCommonMarginalFactor beta q =
        (1 / beta) *
          (Real.Gamma x / Real.Gamma (x + η)) := by
          simpa [x, η] using
            boundedReflectedPowerCommonMarginalFactor_eq_gamma_ratio
              hbeta_pos q
    _ ≤ (1 / beta) * ((x - 1) ^ (-η)) :=
          mul_le_mul_of_nonneg_left hratio hinv_nonneg
    _ = (1 / beta) * ((q : ℝ) ^ (-(boundedMarginalExponent beta))) := by
          have hpred : x - 1 = (q : ℝ) := by
            dsimp [x]
            norm_num
          simp [hpred, η]

theorem boundedReflectedPowerCommonMarginalFactor_shift_rpow_neg_le
    {beta : ℝ} (hbeta_pos : 0 < beta) (q : ℕ) :
    (1 / beta) *
        (((q : ℝ) + 1 + boundedMarginalExponent beta) ^
          (-(boundedMarginalExponent beta))) ≤
      boundedReflectedPowerCommonMarginalFactor beta q := by
  let x : ℝ := (((q + 1 : ℕ) : ℝ))
  let η : ℝ := boundedMarginalExponent beta
  have hx_pos : 0 < x := by dsimp [x]; positivity
  have hη_pos : 0 < η := by
    dsimp [η]
    exact boundedMarginalExponent_pos hbeta_pos
  have hinv_nonneg : 0 ≤ 1 / beta := (one_div_pos.mpr hbeta_pos).le
  have hratio :=
    AppliedModelingLib.Math.rpow_neg_add_shift_le_gamma_div_gamma_add
      (x := x) (s := η) hx_pos hη_pos
  calc
      (1 / beta) *
          (((q : ℝ) + 1 + boundedMarginalExponent beta) ^
            (-(boundedMarginalExponent beta))) =
        (1 / beta) * ((x + η) ^ (-η)) := by
          simp [x, η, Nat.cast_add, Nat.cast_one, add_assoc]
    _ ≤ (1 / beta) *
        (Real.Gamma x / Real.Gamma (x + η)) :=
          mul_le_mul_of_nonneg_left hratio hinv_nonneg
    _ = boundedReflectedPowerCommonMarginalFactor beta q := by
          simpa [x, η] using
            (boundedReflectedPowerCommonMarginalFactor_eq_gamma_ratio
              hbeta_pos q).symm

/-- The bounded reflected-power order-statistic oracle. -/
noncomputable def boundedReflectedPowerOrderStatisticOracle
    (T : ℕ) (beta : ℝ) : TopKValueOracle T :=
  TopKValueOracle.ofOrderStatisticMean T
    (boundedReflectedPowerOrderStatisticMean beta)

/-- Consumption model induced by the reflected-power bounded order-statistic table. -/
noncomputable def boundedReflectedPowerOrderStatisticConsumptionModel
    {T : ℕ} (likelihood : ItemType T → ℝ) (k : ℕ) (beta : ℝ) :
    ConsumptionModel T :=
  (boundedReflectedPowerOrderStatisticOracle T beta).toConsumptionModel
    likelihood k

/--
The concrete iid reflected-power source oracle has the same expected top-`k`
table as the exact gamma-ratio reflected-power oracle.
-/
theorem boundedReflectedPowerSourceIidOrderStatisticOracle_expectedTopSum_eq
    {beta : ℝ} (hbeta_pos : 0 < beta)
    (T : ℕ) (k : ℕ) (t : ItemType T) (q : ℕ) :
    (boundedReflectedPowerSourceIidOrderStatisticOracle T beta).expectedTopSum
        k t q =
      (boundedReflectedPowerOrderStatisticOracle T beta).expectedTopSum
        k t q := by
  simp [boundedReflectedPowerSourceIidOrderStatisticOracle,
    boundedReflectedPowerOrderStatisticOracle,
    boundedReflectedPowerSourceIidOrderStatisticTopKSum_eq_boundedReflectedPowerOrderStatisticTopKSum
      hbeta_pos k q]

/-- Consumption model induced by the concrete iid reflected-power bounded source. -/
noncomputable def boundedReflectedPowerSourceIidOrderStatisticConsumptionModel
    {T : ℕ} (likelihood : ItemType T → ℝ) (k : ℕ) (beta : ℝ) :
    ConsumptionModel T :=
  (boundedReflectedPowerSourceIidOrderStatisticOracle T beta).toConsumptionModel
    likelihood k

/--
The concrete iid reflected-power consumption model is extensionally identical
to the exact reflected-power gamma-ratio table model.
-/
theorem boundedReflectedPowerSourceIidOrderStatisticConsumptionModel_eq
    {T : ℕ} {beta : ℝ} (hbeta_pos : 0 < beta)
    (likelihood : ItemType T → ℝ) (k : ℕ) :
    boundedReflectedPowerSourceIidOrderStatisticConsumptionModel
        likelihood k beta =
      boundedReflectedPowerOrderStatisticConsumptionModel likelihood k beta := by
  change
    ConsumptionModel.mk likelihood
        (fun t q =>
          (boundedReflectedPowerSourceIidOrderStatisticOracle T beta).expectedTopSum
            k t q) =
      ConsumptionModel.mk likelihood
          (fun t q =>
            (boundedReflectedPowerOrderStatisticOracle T beta).expectedTopSum
              k t q)
  congr
  funext t q
  exact
    boundedReflectedPowerSourceIidOrderStatisticOracle_expectedTopSum_eq
      hbeta_pos T k t q

theorem boundedReflectedPowerOrderStatisticTopK_forward_marginal_eq_coeff_mul_common
    (T : ℕ) {beta : ℝ} (hbeta_pos : 0 < beta) {k q : ℕ}
    (hq : k ≤ q) (t : ItemType T) :
    (boundedReflectedPowerOrderStatisticOracle T beta).expectedTopSum k t (q + 1) -
        (boundedReflectedPowerOrderStatisticOracle T beta).expectedTopSum k t q =
      boundedReflectedPowerTopKLossCoeff beta k *
        boundedReflectedPowerCommonMarginalFactor beta q := by
  simpa [boundedReflectedPowerOrderStatisticOracle,
    boundedReflectedPowerCommonMarginalFactor, mul_assoc] using
    boundedReflectedPowerOrderStatistic_topK_forward_marginal_eq
      hbeta_pos hq

theorem boundedReflectedPowerOrderStatisticTopK_forward_marginal_le_power_bound
    (T : ℕ) {beta : ℝ} (hbeta_pos : 0 < beta) {k q : ℕ}
    (hk : 0 < k) (hq : k ≤ q) (hq_pos : 0 < q)
    (t : ItemType T) :
    (boundedReflectedPowerOrderStatisticOracle T beta).expectedTopSum k t (q + 1) -
        (boundedReflectedPowerOrderStatisticOracle T beta).expectedTopSum k t q ≤
      (boundedReflectedPowerTopKLossCoeff beta k / beta) *
        ((q : ℝ) ^ (-(boundedMarginalExponent beta))) := by
  rw [boundedReflectedPowerOrderStatisticTopK_forward_marginal_eq_coeff_mul_common
    T hbeta_pos hq t]
  have hcoeff_nonneg :
      0 ≤ boundedReflectedPowerTopKLossCoeff beta k :=
    (boundedReflectedPowerTopKLossCoeff_pos hbeta_pos hk).le
  have hbound :=
    boundedReflectedPowerCommonMarginalFactor_le_pred_rpow_neg
      hbeta_pos hq_pos
  calc
    boundedReflectedPowerTopKLossCoeff beta k *
        boundedReflectedPowerCommonMarginalFactor beta q
        ≤
      boundedReflectedPowerTopKLossCoeff beta k *
        ((1 / beta) * ((q : ℝ) ^ (-(boundedMarginalExponent beta)))) :=
          mul_le_mul_of_nonneg_left hbound hcoeff_nonneg
    _ = (boundedReflectedPowerTopKLossCoeff beta k / beta) *
        ((q : ℝ) ^ (-(boundedMarginalExponent beta))) := by ring

theorem boundedReflectedPowerOrderStatisticTopK_power_bound_le_forward_marginal
    (T : ℕ) {beta : ℝ} (hbeta_pos : 0 < beta) {k q : ℕ}
    (hk : 0 < k) (hq : k ≤ q) (t : ItemType T) :
      (boundedReflectedPowerTopKLossCoeff beta k / beta) *
        (((q : ℝ) + 1 + boundedMarginalExponent beta) ^
          (-(boundedMarginalExponent beta))) ≤
    (boundedReflectedPowerOrderStatisticOracle T beta).expectedTopSum k t (q + 1) -
        (boundedReflectedPowerOrderStatisticOracle T beta).expectedTopSum k t q := by
  rw [boundedReflectedPowerOrderStatisticTopK_forward_marginal_eq_coeff_mul_common
    T hbeta_pos hq t]
  have hcoeff_nonneg :
      0 ≤ boundedReflectedPowerTopKLossCoeff beta k :=
    (boundedReflectedPowerTopKLossCoeff_pos hbeta_pos hk).le
  have hbound :=
    boundedReflectedPowerCommonMarginalFactor_shift_rpow_neg_le
      hbeta_pos q
  calc
    (boundedReflectedPowerTopKLossCoeff beta k / beta) *
        (((q : ℝ) + 1 + boundedMarginalExponent beta) ^
          (-(boundedMarginalExponent beta)))
        =
      boundedReflectedPowerTopKLossCoeff beta k *
        ((1 / beta) *
          (((q : ℝ) + 1 + boundedMarginalExponent beta) ^
            (-(boundedMarginalExponent beta)))) := by
          ring
    _ ≤ boundedReflectedPowerTopKLossCoeff beta k *
        boundedReflectedPowerCommonMarginalFactor beta q :=
          mul_le_mul_of_nonneg_left hbound hcoeff_nonneg

theorem boundedReflectedPowerOrderStatistic_weightedBackwardMarginal_le_power_bound
    {T : ℕ} (likelihood : ItemType T → ℝ) {k : ℕ} {beta : ℝ}
    (hbeta_pos : 0 < beta) (hk : 0 < k)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    {q : ℕ} (hq : k < q) (t : ItemType T) :
    (boundedReflectedPowerOrderStatisticConsumptionModel likelihood k beta).weightedBackwardMarginal
        t q ≤
      likelihood t *
        ((boundedReflectedPowerTopKLossCoeff beta k / beta) *
          (((q - 1 : ℕ) : ℝ) ^ (-(boundedMarginalExponent beta)))) := by
  have hq_pos : 0 < q := by omega
  have hq_pred_pos : 0 < q - 1 := by omega
  have hk_le_pred : k ≤ q - 1 := by omega
  have hbase :=
    boundedReflectedPowerOrderStatisticTopK_forward_marginal_le_power_bound
      T hbeta_pos hk hk_le_pred hq_pred_pos t
  have hdiff_le :
      (boundedReflectedPowerOrderStatisticOracle T beta).expectedTopSum k t q -
          (boundedReflectedPowerOrderStatisticOracle T beta).expectedTopSum k t (q - 1) ≤
        (boundedReflectedPowerTopKLossCoeff beta k / beta) *
          (((q - 1 : ℕ) : ℝ) ^ (-(boundedMarginalExponent beta))) := by
    simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hq_pos)] using hbase
  unfold boundedReflectedPowerOrderStatisticConsumptionModel
    ConsumptionModel.weightedBackwardMarginal TopKValueOracle.toConsumptionModel
  rw [dif_neg (Nat.ne_of_gt hq_pos)]
  exact mul_le_mul_of_nonneg_left hdiff_le (hlike_pos t).le

theorem boundedReflectedPowerOrderStatistic_power_bound_le_weightedForwardMarginal
    {T : ℕ} (likelihood : ItemType T → ℝ) {k : ℕ} {beta : ℝ}
    (hbeta_pos : 0 < beta) (hk : 0 < k)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    {q : ℕ} (hq : k ≤ q) (t : ItemType T) :
      likelihood t *
        ((boundedReflectedPowerTopKLossCoeff beta k / beta) *
          (((q : ℝ) + 1 + boundedMarginalExponent beta) ^
            (-(boundedMarginalExponent beta)))) ≤
    (boundedReflectedPowerOrderStatisticConsumptionModel likelihood k beta).weightedForwardMarginal
        t q := by
  have hbase :=
    boundedReflectedPowerOrderStatisticTopK_power_bound_le_forward_marginal
      T hbeta_pos hk hq t
  unfold boundedReflectedPowerOrderStatisticConsumptionModel
    ConsumptionModel.weightedForwardMarginal ConsumptionModel.marginalValue
    TopKValueOracle.toConsumptionModel AppliedModelingLib.Allocation.marginal
  exact mul_le_mul_of_nonneg_left hbase (hlike_pos t).le

theorem boundedReflectedPowerCommonLossFactor_mul_rankLossCoeff_self
    {beta : ℝ} (hbeta_pos : 0 < beta) (q : ℕ) :
    boundedReflectedPowerCommonLossFactor beta q *
      boundedReflectedPowerRankLossCoeff beta q = 1 := by
  have hx_pos : 0 < (q : ℝ) + 1 := by positivity
  have hxs_pos : 0 < (q : ℝ) + 1 + 1 / beta := by positivity
  have hΓx_ne : Real.Gamma ((q : ℝ) + 1) ≠ 0 :=
    (Real.Gamma_pos_of_pos hx_pos).ne'
  have hΓxs_ne : Real.Gamma ((q : ℝ) + 1 + 1 / beta) ≠ 0 :=
    (Real.Gamma_pos_of_pos hxs_pos).ne'
  unfold boundedReflectedPowerCommonLossFactor
    boundedReflectedPowerRankLossCoeff
  field_simp [hΓx_ne, hΓxs_ne]

theorem boundedReflectedPowerCommonLossFactor_mul_rankLossCoeff_sum_range
    {beta : ℝ} (hbeta_pos : 0 < beta) (q : ℕ) :
    boundedReflectedPowerCommonLossFactor beta q *
        (∑ i ∈ Finset.range q,
          boundedReflectedPowerRankLossCoeff beta i) =
      (q : ℝ) / (1 + 1 / beta) := by
  induction q with
  | zero =>
      simp
  | succ q ih =>
      let factor := boundedReflectedPowerCommonLossFactor beta
      let coeff := boundedReflectedPowerRankLossCoeff beta
      have hfactor_pos : 0 < factor q :=
        boundedReflectedPowerCommonLossFactor_pos hbeta_pos q
      have hfactor_ne : factor q ≠ 0 := hfactor_pos.ne'
      have hden_pos : 0 < (q : ℝ) + 1 + 1 / beta := by positivity
      have hden_ne : (q : ℝ) + 1 + 1 / beta ≠ 0 := hden_pos.ne'
      have hrec :
          factor (q + 1) =
            (((q + 1 : ℕ) : ℝ) / ((q : ℝ) + 1 + 1 / beta)) *
              factor q := by
        have hratio :=
          boundedReflectedPowerCommonLossFactor_succ_div_self
            hbeta_pos q
        have hratio' :
            factor (q + 1) / factor q =
              (((q + 1 : ℕ) : ℝ) / ((q : ℝ) + 1 + 1 / beta)) := by
          simpa [factor] using hratio
        calc
          factor (q + 1) = (factor (q + 1) / factor q) * factor q := by
            field_simp [hfactor_ne]
          _ = (((q + 1 : ℕ) : ℝ) / ((q : ℝ) + 1 + 1 / beta)) *
              factor q := by rw [hratio']
      have hself : factor q * coeff q = 1 := by
        dsimp [factor, coeff]
        exact boundedReflectedPowerCommonLossFactor_mul_rankLossCoeff_self
          hbeta_pos q
      rw [Finset.sum_range_succ]
      calc
        factor (q + 1) *
            ((∑ i ∈ Finset.range q, coeff i) + coeff q) =
          (((q + 1 : ℕ) : ℝ) / ((q : ℝ) + 1 + 1 / beta)) *
            (factor q *
              ((∑ i ∈ Finset.range q, coeff i) + coeff q)) := by
              rw [hrec]
              ring
        _ =
          (((q + 1 : ℕ) : ℝ) / ((q : ℝ) + 1 + 1 / beta)) *
            ((q : ℝ) / (1 + 1 / beta) + 1) := by
              rw [mul_add, ih, hself]
        _ = ((q + 1 : ℕ) : ℝ) / (1 + 1 / beta) := by
              rw [Nat.cast_add, Nat.cast_one]
              field_simp [hden_ne]
              ring

theorem boundedReflectedPowerOrderStatistic_topK_sum_eq_all_samples_of_le
    {beta : ℝ} (hbeta_pos : 0 < beta) {k q : ℕ} (hqk : q ≤ k) :
    orderStatisticTopKSumFromMean
        (boundedReflectedPowerOrderStatisticMean beta) k q =
      (q : ℝ) / (beta + 1) := by
  rw [orderStatisticTopKSumFromMean_eq_bottomIndexed_sum]
  rw [min_eq_right hqk]
  let factor := boundedReflectedPowerCommonLossFactor beta q
  let coeff := boundedReflectedPowerRankLossCoeff beta
  have hterm :
      ∀ i ∈ Finset.range q,
        boundedReflectedPowerOrderStatisticMean beta (q - i) q =
          1 - coeff i * factor := by
    intro i hi
    have hiq : i ≤ q := le_of_lt (Finset.mem_range.1 hi)
    have hsub : q - (q - i) = i := by omega
    simp [boundedReflectedPowerOrderStatisticMean,
      boundedReflectedPowerRankLossMean, factor, coeff, hsub]
  have hsum :
      (∑ i ∈ Finset.range q,
        boundedReflectedPowerOrderStatisticMean beta (q - i) q) =
        (q : ℝ) - factor * (∑ i ∈ Finset.range q, coeff i) := by
    calc
      (∑ i ∈ Finset.range q,
        boundedReflectedPowerOrderStatisticMean beta (q - i) q)
          =
        ∑ i ∈ Finset.range q, (1 - coeff i * factor) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact hterm i hi
      _ = (q : ℝ) - factor * (∑ i ∈ Finset.range q, coeff i) := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, ← Finset.sum_mul]
          simp [nsmul_eq_mul]
          ring
  rw [hsum]
  have hbeta_ne : beta ≠ 0 := hbeta_pos.ne'
  have hden_ne : beta + 1 ≠ 0 := by positivity
  have hall_loss :=
    boundedReflectedPowerCommonLossFactor_mul_rankLossCoeff_sum_range
      hbeta_pos q
  rw [hall_loss]
  field_simp [hbeta_ne, hden_ne]
  ring

/-- The reflected-power bounded top-`k` table has positive forward marginals. -/
theorem boundedReflectedPowerOrderStatistic_topK_forward_marginal_pos
    {beta : ℝ} (hbeta_pos : 0 < beta) {k : ℕ} (hk : 0 < k)
    (q : ℕ) :
    0 <
      orderStatisticTopKSumFromMean
          (boundedReflectedPowerOrderStatisticMean beta) k (q + 1) -
        orderStatisticTopKSumFromMean
          (boundedReflectedPowerOrderStatisticMean beta) k q := by
  by_cases hstable : k ≤ q
  · exact boundedReflectedPowerOrderStatistic_topK_forward_marginal_pos_of_le
      hbeta_pos hk hstable
  · have hq_lt_k : q < k := Nat.lt_of_not_ge hstable
    have hq_le_k : q ≤ k := le_of_lt hq_lt_k
    have hqsucc_le_k : q + 1 ≤ k := Nat.succ_le_of_lt hq_lt_k
    rw [boundedReflectedPowerOrderStatistic_topK_sum_eq_all_samples_of_le
        hbeta_pos hqsucc_le_k,
      boundedReflectedPowerOrderStatistic_topK_sum_eq_all_samples_of_le
        hbeta_pos hq_le_k]
    have hden_pos : 0 < beta + 1 := by positivity
    rw [Nat.cast_add, Nat.cast_one]
    field_simp [hden_pos.ne']
    norm_num

theorem boundedReflectedPowerOrderStatisticTopK_forward_marginal_tendsto_zero
    (T : ℕ) {beta : ℝ} (hbeta_pos : 0 < beta) {k : ℕ}
    (hk : 0 < k) (t : ItemType T) :
    Filter.Tendsto
      (fun q =>
        (boundedReflectedPowerOrderStatisticOracle T beta).expectedTopSum k t (q + 1) -
          (boundedReflectedPowerOrderStatisticOracle T beta).expectedTopSum k t q)
      Filter.atTop (nhds 0) := by
  let η : ℝ := boundedMarginalExponent beta
  let C : ℝ := boundedReflectedPowerTopKLossCoeff beta k / beta
  have hη_pos : 0 < η := by
    dsimp [η]
    exact boundedMarginalExponent_pos hbeta_pos
  have hupper_tend :
      Filter.Tendsto (fun q : ℕ => C * ((q : ℝ) ^ (-η)))
        Filter.atTop (nhds 0) := by
    have hpow :
        Filter.Tendsto (fun q : ℕ => ((q : ℝ) ^ (-η)))
          Filter.atTop (nhds 0) := by
      simpa using
        (tendsto_rpow_neg_atTop hη_pos).comp
          tendsto_natCast_atTop_atTop
    simpa using hpow.const_mul C
  refine squeeze_zero' ?_ ?_ hupper_tend
  · filter_upwards with q
    exact le_of_lt
      (boundedReflectedPowerOrderStatistic_topK_forward_marginal_pos
        hbeta_pos hk q)
  · filter_upwards
      [Filter.eventually_atTop.2
        ⟨max k 1, fun q hq => hq⟩] with q hq
    have hkq : k ≤ q := by omega
    have hqpos : 0 < q := by omega
    simpa [C, η] using
      boundedReflectedPowerOrderStatisticTopK_forward_marginal_le_power_bound
        T hbeta_pos hk hkq hqpos t

/--
Reflected-power bounded order-statistic large-gap marginal comparison for
`β > 0`.

This is the bounded analogue of the Pareto finite large-gap comparison.  The
finite gamma-ratio envelopes now use the arbitrary-positive-shift Wendel
wrappers in `AppliedModelingLib.Foundations.Math.GammaAsymptotics`.
-/
theorem boundedReflectedPowerOrderStatistic_large_gap_count_eventually
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) {k : ℕ} {beta : ℝ}
    (hbeta_pos : 0 < beta) (hk : 0 < k)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t) :
    ∀ᶠ N in Filter.atTop,
      ∀ src dst qsrc qdst,
        qsrc ≤ N →
        qdst ≤ N →
        k < qsrc →
        k < qdst →
        AppliedModelingLib.Math.invSqrtSuccError N * (N : ℝ) <
          (qsrc : ℝ) / likelihood src ^ (beta / (beta + 1)) -
            (qdst : ℝ) / likelihood dst ^ (beta / (beta + 1)) →
        (boundedReflectedPowerOrderStatisticConsumptionModel likelihood k beta).weightedBackwardMarginal
            src qsrc <
          (boundedReflectedPowerOrderStatisticConsumptionModel likelihood k beta).weightedForwardMarginal
            dst qdst := by
  classical
  let η : ℝ := boundedMarginalExponent beta
  let γ : ℝ := beta / (beta + 1)
  have hη_pos : 0 < η := by
    dsimp [η]
    exact boundedMarginalExponent_pos hbeta_pos
  have hγ_eq : 1 / η = γ := by
    dsimp [η, γ]
    exact boundedMarginalExponent_one_div_eq_gamma hbeta_pos
  have hcoeff_pos :
      0 < boundedReflectedPowerTopKLossCoeff beta k / beta :=
    div_pos (boundedReflectedPowerTopKLossCoeff_pos hbeta_pos hk)
      hbeta_pos
  exact
    AppliedModelingLib.Allocation.powerLawEnvelope_large_gap_count_eventually
      likelihood
      (boundedReflectedPowerOrderStatisticConsumptionModel likelihood k beta).valueOfCount
      (η := η) (γ := γ)
      (coeff := boundedReflectedPowerTopKLossCoeff beta k / beta)
      (dstShift := η) (floor := k)
      hη_pos hγ_eq hcoeff_pos (le_of_lt hη_pos) hk hlike_pos
      (by
        intro src qsrc hsrc_floor
        simpa [η] using
          boundedReflectedPowerOrderStatistic_weightedBackwardMarginal_le_power_bound
            likelihood hbeta_pos hk hlike_pos hsrc_floor src)
      (by
        intro dst qdst hdst_floor
        simpa [η] using
          boundedReflectedPowerOrderStatistic_power_bound_le_weightedForwardMarginal
            likelihood hbeta_pos hk hlike_pos (le_of_lt hdst_floor) dst)

theorem boundedReflectedPowerOrderStatistic_count_floor_eventually
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) {k : ℕ} {beta : ℝ}
    (hbeta_pos : 0 < beta) (hk : 0 < k)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (floor : ℕ) :
    ∀ᶠ N in Filter.atTop,
      ∀ a : CountAllocation T, 0 < N →
        (boundedReflectedPowerOrderStatisticConsumptionModel likelihood k beta).IsOptimalAtTotal N a →
        ∀ t, floor < a.count t :=
  topK_count_floor_eventually_of_marginal_tendsto_zero_and_positive_low_forward
    (boundedReflectedPowerOrderStatisticOracle T beta) likelihood k floor
    hlike_pos
    (by
      intro t q _hq_floor
      simpa [TopKValueOracle.marginalTopK,
        boundedReflectedPowerOrderStatisticOracle,
        TopKValueOracle.ofOrderStatisticMean] using
        boundedReflectedPowerOrderStatistic_topK_forward_marginal_pos
          hbeta_pos hk q)
    (boundedReflectedPowerOrderStatisticTopK_forward_marginal_tendsto_zero
      T hbeta_pos hk)

/--
Count-level FOC package for the exact reflected-power bounded
order-statistic model.

The concrete constructor below is available for every `β > 0`; the finite
gamma-ratio estimates are supplied by the arbitrary-positive-shift Wendel
wrappers in the shared math library.
-/
structure BoundedReflectedPowerOrderStatisticEventualFOCCertificate {T : ℕ}
    [NeZero T]
    (likelihood : ItemType T → ℝ) (k : ℕ) (beta : ℝ) where
  base_error : ℕ → ℝ
  base_error_nonneg : ∀ N, 0 ≤ base_error N
  base_error_tends_to_zero : AppliedModelingLib.Math.TendsToZero base_error
  floor : ℕ
  count_floor_eventually :
    ∀ᶠ N in Filter.atTop,
      ∀ a : CountAllocation T, 0 < N →
        (boundedReflectedPowerOrderStatisticConsumptionModel likelihood k beta).IsOptimalAtTotal N a →
        ∀ t, floor < a.count t
  large_gap_count :
    ∀ᶠ N in Filter.atTop,
      ∀ src dst qsrc qdst,
        qsrc ≤ N →
        qdst ≤ N →
        floor < qsrc →
        floor < qdst →
        base_error N * (N : ℝ) <
          (qsrc : ℝ) / likelihood src ^ (beta / (beta + 1)) -
            (qdst : ℝ) / likelihood dst ^ (beta / (beta + 1)) →
        (boundedReflectedPowerOrderStatisticConsumptionModel likelihood k beta).weightedBackwardMarginal
            src qsrc <
          (boundedReflectedPowerOrderStatisticConsumptionModel likelihood k beta).weightedForwardMarginal
            dst qdst

namespace BoundedReflectedPowerOrderStatisticEventualFOCCertificate

noncomputable def toPairwiseScaledEventualSublinearFOCCertificate
    {T : ℕ} [NeZero T]
    {likelihood : ItemType T → ℝ} {k : ℕ} {beta : ℝ}
    (hcert :
      BoundedReflectedPowerOrderStatisticEventualFOCCertificate likelihood k beta)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t) :
    PairwiseScaledEventualSublinearFOCCertificate
      (fun _ => boundedReflectedPowerOrderStatisticConsumptionModel likelihood k beta)
      (fun t : ItemType T => likelihood t ^ (beta / (beta + 1)))
      (gammaLikelihoodProfile likelihood (beta / (beta + 1))) := by
  refine
    PairwiseScaledEventualSublinearFOCCertificate.of_count_gap
      (Mseq :=
        fun _ => boundedReflectedPowerOrderStatisticConsumptionModel
          likelihood k beta)
      (weight := fun t : ItemType T => likelihood t ^ (beta / (beta + 1)))
      (G := gammaLikelihoodProfile likelihood (beta / (beta + 1)))
      ?_ ?_ hcert.base_error hcert.base_error_nonneg
      hcert.base_error_tends_to_zero hcert.floor
      hcert.count_floor_eventually hcert.large_gap_count
  · intro t
    exact Real.rpow_pos_of_pos (hlike_pos t) (beta / (beta + 1))
  · intro t
    have hnorm_pos :
        0 < ∑ i : ItemType T, likelihood i ^ (beta / (beta + 1)) :=
      Finset.sum_pos
        (fun i _ => Real.rpow_pos_of_pos
          (hlike_pos i) (beta / (beta + 1)))
        Finset.univ_nonempty
    exact gammaLikelihoodProfile_targetShare_eq likelihood
      (beta / (beta + 1)) t (ne_of_gt hnorm_pos)

end BoundedReflectedPowerOrderStatisticEventualFOCCertificate

/-- Concrete `β > 0` FOC certificate for the reflected-power bounded model. -/
noncomputable def boundedReflectedPowerOrderStatistic_eventualFOCCertificate
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) {k : ℕ} {beta : ℝ}
    (hbeta_pos : 0 < beta) (hk : 0 < k)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t) :
    BoundedReflectedPowerOrderStatisticEventualFOCCertificate likelihood k beta where
  base_error := AppliedModelingLib.Math.invSqrtSuccError
  base_error_nonneg := AppliedModelingLib.Math.invSqrtSuccError_nonneg
  base_error_tends_to_zero := AppliedModelingLib.Math.invSqrtSuccError_tendsToZero
  floor := k
  count_floor_eventually :=
    boundedReflectedPowerOrderStatistic_count_floor_eventually
      likelihood hbeta_pos hk hlike_pos k
  large_gap_count :=
    boundedReflectedPowerOrderStatistic_large_gap_count_eventually
      likelihood hbeta_pos hk hlike_pos

/--
Concrete `β > 0` reflected-power bounded order-statistic model, packaged directly
as the shared eventual sublinear FOC certificate used by Theorem 1(ii).
-/
noncomputable def
    boundedReflectedPowerOrderStatistic_pairwiseEventualSublinearFOCCertificate
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) {k : ℕ} {beta : ℝ}
    (hbeta_pos : 0 < beta) (hk : 0 < k)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t) :
    PairwiseScaledEventualSublinearFOCCertificate
      (fun _ => boundedReflectedPowerOrderStatisticConsumptionModel likelihood k beta)
      (fun t : ItemType T => likelihood t ^ (beta / (beta + 1)))
      (gammaLikelihoodProfile likelihood (beta / (beta + 1))) :=
  (boundedReflectedPowerOrderStatistic_eventualFOCCertificate
    likelihood hbeta_pos hk hlike_pos).toPairwiseScaledEventualSublinearFOCCertificate
      hlike_pos

/-- Loss asymptotic for the exact reflected-power bounded order-statistic table. -/
theorem boundedReflectedPowerOrderStatistic_loss_asymptoticEquivalent
    {beta : ℝ} (hbeta_pos : 0 < beta) {k : ℕ} (hk : 0 < k) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun q : ℕ =>
        (k : ℝ) -
          orderStatisticTopKSumFromMean
            (boundedReflectedPowerOrderStatisticMean beta) k q)
      (fun q : ℕ =>
        boundedReflectedPowerTopKLossCoeff beta k * boundedTailScale beta q) := by
  have hcoeff_ne :
      boundedReflectedPowerTopKLossCoeff beta k ≠ 0 :=
    (boundedReflectedPowerTopKLossCoeff_pos hbeta_pos hk).ne'
  refine AppliedModelingLib.Math.AsymptoticEquivalent.congr_left_eventually
    (x' := fun q : ℕ =>
      boundedReflectedPowerTopKLossCoeff beta k *
        boundedReflectedPowerCommonLossFactor beta q) ?_ ?_
  · filter_upwards [eventually_atTop.2 ⟨k, fun q hq => hq⟩] with q hq
    exact boundedReflectedPowerOrderStatistic_topK_loss_eq beta hq
  · have hfactor :=
      boundedReflectedPowerCommonLossFactor_asymptoticEquivalent hbeta_pos
    rw [AppliedModelingLib.Math.AsymptoticEquivalent] at hfactor
    rw [AppliedModelingLib.Math.AsymptoticEquivalent]
    refine Tendsto.congr' ?_ hfactor
    filter_upwards [boundedTailScale_eventually_ne_zero beta] with q hscale_ne
    field_simp [hcoeff_ne, hscale_ne]

/-- Scaled-drop law for the exact reflected-power bounded order-statistic loss. -/
theorem boundedReflectedPowerOrderStatistic_scaled_drop
    {beta : ℝ} (hbeta_pos : 0 < beta) {k : ℕ} (hk : 0 < k) :
    Tendsto
      (fun q : ℕ =>
        (((q + 1 : ℕ) : ℝ) *
          ((((k : ℝ) -
                orderStatisticTopKSumFromMean
                  (boundedReflectedPowerOrderStatisticMean beta) k q) -
              ((k : ℝ) -
                orderStatisticTopKSumFromMean
                  (boundedReflectedPowerOrderStatisticMean beta) k (q + 1))) /
            ((k : ℝ) -
              orderStatisticTopKSumFromMean
                (boundedReflectedPowerOrderStatisticMean beta) k q))))
      atTop (nhds (1 / beta)) := by
  let C := boundedReflectedPowerTopKLossCoeff beta k
  let factor := boundedReflectedPowerCommonLossFactor beta
  have hC_ne : C ≠ 0 :=
    (boundedReflectedPowerTopKLossCoeff_pos hbeta_pos hk).ne'
  have hinv_pos : 0 < 1 / beta := one_div_pos.mpr hbeta_pos
  have hratio :
      Tendsto
        (fun q : ℕ =>
          (((q + 1 : ℕ) : ℝ) /
            (((q + 1 : ℕ) : ℝ) + 1 / beta)))
        atTop (nhds 1) := by
    have h :=
      tendsto_add_mul_div_add_mul_atTop_nhds
        (𝕜 := ℝ) (1 : ℝ) (1 + 1 / beta) (1 : ℝ)
        (by norm_num : (1 : ℝ) ≠ 0)
    simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] using h
  have htarget :
      Tendsto
        (fun q : ℕ =>
          (1 / beta) *
            (((q + 1 : ℕ) : ℝ) /
              (((q + 1 : ℕ) : ℝ) + 1 / beta)))
        atTop (nhds (1 / beta)) := by
    simpa using hratio.const_mul (1 / beta)
  refine Tendsto.congr' ?_ htarget
  filter_upwards [eventually_atTop.2 ⟨k, fun q hq => hq⟩] with q hq
  have hq_succ : k ≤ q + 1 := by omega
  have hfactor_pos : 0 < factor q :=
    boundedReflectedPowerCommonLossFactor_pos hbeta_pos q
  have hfactor_ne : factor q ≠ 0 := hfactor_pos.ne'
  have hden_pos : 0 < (q : ℝ) + 1 + 1 / beta := by positivity
  have hden_ne : (q : ℝ) + 1 + 1 / beta ≠ 0 := hden_pos.ne'
  have hrec :
      factor (q + 1) / factor q =
        (((q + 1 : ℕ) : ℝ) / ((q : ℝ) + 1 + 1 / beta)) :=
    boundedReflectedPowerCommonLossFactor_succ_div_self hbeta_pos q
  rw [boundedReflectedPowerOrderStatistic_topK_loss_eq beta hq,
    boundedReflectedPowerOrderStatistic_topK_loss_eq beta hq_succ]
  change
      (1 / beta) *
        (((q + 1 : ℕ) : ℝ) /
          (((q + 1 : ℕ) : ℝ) + 1 / beta)) =
    (((q + 1 : ℕ) : ℝ) *
      (((C * factor q) - (C * factor (q + 1))) / (C * factor q)))
  rw [show factor (q + 1) = (factor (q + 1) / factor q) * factor q by
        field_simp [hfactor_ne]]
  rw [hrec]
  rw [show (((q + 1 : ℕ) : ℝ)) = (q : ℝ) + 1 by
    rw [Nat.cast_add, Nat.cast_one]]
  field_simp [hC_ne, hfactor_ne, hden_ne]
  ring

/--
Exact reflected-power bounded source certificate.

This is a direct source-specific alternative to the generic bounded
loss-plus-`scaled_drop` wrapper: the gamma-ratio mean table supplies both
the loss asymptotic and the scaled-drop law internally.
-/
noncomputable def boundedReflectedPowerOrderStatisticScaledMarginalCertificate
    {beta : ℝ} (hbeta_pos : 0 < beta) {k : ℕ} (hk : 0 < k) :
    BoundedOrderStatisticScaledMarginalCertificate
      (boundedReflectedPowerOrderStatisticMean beta) k beta
      (boundedReflectedPowerTopKLossCoeff beta k / beta) :=
  BoundedOrderStatisticScaledMarginalCertificate.ofLossAsymptoticAndScaledDrop
    hbeta_pos hk
    (boundedReflectedPowerTopKLossCoeff_pos hbeta_pos hk)
    (boundedReflectedPowerOrderStatistic_loss_asymptoticEquivalent hbeta_pos hk)
    (boundedReflectedPowerOrderStatistic_scaled_drop hbeta_pos hk)

/-- The paper's rescaled split threshold `delta / a^(-1/beta)` diverges. -/
theorem boundedTailScale_delta_div_tendsto_atTop
    {beta delta : ℝ} (hbeta_pos : 0 < beta) (hdelta_pos : 0 < delta) :
    Tendsto (fun a : ℕ => delta / boundedTailScale beta a) atTop atTop :=
  AppliedModelingLib.Math.tendsto_const_div_atTop_of_pos_tendsto_zero
    hdelta_pos (boundedTailScale_tendsto_zero hbeta_pos)
    (boundedTailScale_eventually_pos beta)

theorem boundedTailScale_const_mul_tendsto_zero
    {beta y : ℝ} (hbeta_pos : 0 < beta) :
    Tendsto (fun a => y * boundedTailScale beta a) atTop (nhds 0) := by
  simpa using (boundedTailScale_tendsto_zero hbeta_pos).const_mul y

/--
A geometric tail beats the bounded-branch scale `a^(-1 / beta)`, even after a
fixed polynomial factor.
-/
theorem boundedTailScale_polynomial_geometric_ratio_tendsto_zero
    {beta rho : ℝ} (hbeta_pos : 0 < beta)
    (hrho_pos : 0 < rho) (hrho_lt_one : rho < 1)
    (degree : ℕ) (C : ℝ) :
    Tendsto
      (fun a : ℕ =>
        C * ((a : ℝ) ^ degree * rho ^ a) / boundedTailScale beta a)
      atTop (nhds 0) := by
  have hbase :
      Tendsto
        (fun a : ℕ =>
          C * ((a : ℝ) ^ ((degree : ℝ) + 1 / beta) * rho ^ a))
        atTop (nhds 0) := by
    simpa [mul_assoc] using
      (AppliedModelingLib.Math.rpow_mul_geometric_tendsto_zero
        ((degree : ℝ) + 1 / beta) hrho_pos hrho_lt_one).const_mul C
  refine Tendsto.congr' ?_ hbase
  filter_upwards [eventually_gt_atTop 0] with a ha
  have ha_pos : 0 < (a : ℝ) := by exact_mod_cast ha
  have ha_nonneg : 0 ≤ (a : ℝ) := le_of_lt ha_pos
  rw [boundedTailScale, ← Real.rpow_natCast]
  rw [Real.rpow_neg ha_nonneg]
  have hxpow_ne : (a : ℝ) ^ (1 / beta) ≠ 0 :=
    (Real.rpow_pos_of_pos ha_pos (1 / beta)).ne'
  field_simp [hxpow_ne]
  have hexp_eq :
      ((degree : ℝ) * beta + 1) / beta =
        (degree : ℝ) + 1 / beta := by
    field_simp [ne_of_gt hbeta_pos]
  rw [← Real.rpow_natCast]
  rw [hexp_eq, Real.rpow_add ha_pos]
  ring

/--
A geometric tail beats the bounded-branch marginal scale, even after a fixed
polynomial factor in `(a + 1)`.
-/
theorem boundedPowerMarginalScale_succ_polynomial_geometric_ratio_tendsto_zero
    {beta rho : ℝ} (hbeta_pos : 0 < beta)
    (hrho_pos : 0 < rho) (hrho_lt_one : rho < 1)
    (degree : ℕ) (C : ℝ) :
    Tendsto
      (fun a : ℕ =>
        C * (((((a + 1 : ℕ) : ℝ)) ^ degree) * rho ^ a) /
          boundedPowerMarginalScale beta a)
      atTop (nhds 0) := by
  let eta : ℝ := boundedMarginalExponent beta
  have hbase :
      Tendsto
        (fun a : ℕ =>
          (C * rho⁻¹) *
            (((((a + 1 : ℕ) : ℝ)) ^ ((degree : ℝ) + eta)) *
              rho ^ (a + 1 : ℕ)))
        atTop (nhds 0) := by
    have h :=
      (AppliedModelingLib.Math.rpow_mul_geometric_tendsto_zero
        ((degree : ℝ) + eta) hrho_pos hrho_lt_one).comp
        (tendsto_add_atTop_nat 1)
    simpa [mul_assoc] using h.const_mul (C * rho⁻¹)
  refine Tendsto.congr' ?_ hbase
  filter_upwards with a
  have hsucc_pos : 0 < (((a + 1 : ℕ) : ℝ)) := by positivity
  have hsucc_nonneg : 0 ≤ (((a + 1 : ℕ) : ℝ)) := hsucc_pos.le
  have hsucc_pow_ne :
      (((a + 1 : ℕ) : ℝ)) ^ eta ≠ 0 :=
    (Real.rpow_pos_of_pos hsucc_pos eta).ne'
  rw [boundedPowerMarginalScale]
  change
    (C * rho⁻¹) *
        (((((a + 1 : ℕ) : ℝ)) ^ ((degree : ℝ) + eta)) *
          rho ^ (a + 1 : ℕ)) =
      C * (((((a + 1 : ℕ) : ℝ)) ^ degree) * rho ^ a) /
        (((a + 1 : ℕ) : ℝ) ^ (-eta))
  rw [Real.rpow_neg hsucc_nonneg eta]
  field_simp [hsucc_pow_ne, hrho_pos.ne']
  rw [show (((a + 1 : ℕ) : ℝ) ^ degree) =
      (((a + 1 : ℕ) : ℝ) ^ (degree : ℝ)) by
        rw [Real.rpow_natCast]]
  rw [Real.rpow_add hsucc_pos]
  rw [pow_succ]
  ring

theorem boundedTailScale_rpow_beta
    {beta : ℝ} (hbeta_pos : 0 < beta) {a : ℕ} (ha : 0 < a) :
    (boundedTailScale beta a) ^ beta = (a : ℝ) ^ (-1 : ℝ) := by
  have ha_nonneg : 0 ≤ (a : ℝ) := by positivity
  have hexp : -(1 / beta) * beta = (-1 : ℝ) := by
    field_simp [ne_of_gt hbeta_pos]
  rw [boundedTailScale, ← Real.rpow_mul ha_nonneg, hexp]

theorem boundedTailScale_rescaled_rpow_beta
    {beta y : ℝ} (hbeta_pos : 0 < beta) (hy_pos : 0 < y)
    {a : ℕ} (ha : 0 < a) :
    (y * boundedTailScale beta a) ^ beta =
      y ^ beta * (a : ℝ) ^ (-1 : ℝ) := by
  have hscale_pos : 0 < boundedTailScale beta a := by
    have ha_real_pos : 0 < (a : ℝ) := by exact_mod_cast ha
    exact Real.rpow_pos_of_pos ha_real_pos (-(1 / beta))
  rw [Real.mul_rpow hy_pos.le hscale_pos.le,
    boundedTailScale_rpow_beta hbeta_pos ha]

/--
Local CDF power bounds keep their expected `1/a` form after the bounded
Lemma D.2 substitution `x = y*a^(-1/beta)`.
-/
theorem boundedLemmaD2_eventually_rescaled_local_cdf_power_bounds
    {G : ℝ → ℝ} {beta A B delta : ℝ}
    (hbeta_pos : 0 < beta)
    (hG_lower :
      ∀ x : ℝ, 0 < x → x < delta → A * x ^ beta ≤ G x)
    (hG_upper :
      ∀ x : ℝ, 0 < x → x < delta → G x ≤ B * x ^ beta) :
    ∀ᶠ a in atTop,
      ∀ {y : ℝ}, 0 < y →
        y < delta / boundedTailScale beta a →
          A * (y ^ beta * (a : ℝ) ^ (-1 : ℝ)) ≤
              G (y * boundedTailScale beta a) ∧
            G (y * boundedTailScale beta a) ≤
              B * (y ^ beta * (a : ℝ) ^ (-1 : ℝ)) := by
  filter_upwards
    [eventually_gt_atTop (0 : ℕ), boundedTailScale_eventually_pos beta] with
      a ha hscale_pos y hy_pos hy_lt
  have hx_pos : 0 < y * boundedTailScale beta a :=
    mul_pos hy_pos hscale_pos
  have hx_lt_delta : y * boundedTailScale beta a < delta :=
    (lt_div_iff₀ hscale_pos).mp hy_lt
  have hpow :
      (y * boundedTailScale beta a) ^ beta =
        y ^ beta * (a : ℝ) ^ (-1 : ℝ) :=
    boundedTailScale_rescaled_rpow_beta hbeta_pos hy_pos ha
  constructor
  · simpa [hpow] using
      hG_lower (y * boundedTailScale beta a) hx_pos hx_lt_delta
  · simpa [hpow] using
      hG_upper (y * boundedTailScale beta a) hx_pos hx_lt_delta

/-- Gamma-shaped local envelope for bounded Lemma D.2's growing-window kernel. -/
noncomputable def boundedLemmaD2LocalEnvelope
    (beta A B : ℝ) (j : ℕ) (y : ℝ) : ℝ :=
  B ^ j * (y ^ (beta * (j : ℝ)) *
    Real.exp (-(A / 2) * y ^ beta))

/--
Local envelope for the normalized fixed-rank finite difference. Compared to
`boundedLemmaD2LocalEnvelope`, it carries one extra polynomial factor coming
from `(a + 1) * G(y*a^(-1/beta)) - j`.
-/
noncomputable def boundedLemmaD2ForwardDifferenceLocalEnvelope
    (beta A B : ℝ) (j : ℕ) (y : ℝ) : ℝ :=
  (2 * ((j : ℝ) + 2 * B * y ^ beta)) *
    boundedLemmaD2LocalEnvelope beta A B j y

/-- The local Lemma D.2 envelope is nonnegative on `(0,∞)` when `B ≥ 0`. -/
theorem boundedLemmaD2LocalEnvelope_nonneg
    {beta A B y : ℝ} {j : ℕ}
    (hB_nonneg : 0 ≤ B) (hy_nonneg : 0 ≤ y) :
    0 ≤ boundedLemmaD2LocalEnvelope beta A B j y := by
  unfold boundedLemmaD2LocalEnvelope
  exact mul_nonneg (pow_nonneg hB_nonneg j)
    (mul_nonneg (Real.rpow_nonneg hy_nonneg _)
      (Real.exp_nonneg _))

/--
The finite-difference local envelope is nonnegative on `(0,∞)` under the same
local CDF upper-bound sign hypotheses.
-/
theorem boundedLemmaD2ForwardDifferenceLocalEnvelope_nonneg
    {beta A B y : ℝ} {j : ℕ}
    (hB_nonneg : 0 ≤ B) (hy_nonneg : 0 ≤ y) :
    0 ≤ boundedLemmaD2ForwardDifferenceLocalEnvelope beta A B j y := by
  unfold boundedLemmaD2ForwardDifferenceLocalEnvelope
  have hybeta_nonneg : 0 ≤ y ^ beta := Real.rpow_nonneg hy_nonneg _
  have hfactor_nonneg :
      0 ≤ 2 * ((j : ℝ) + 2 * B * y ^ beta) := by
    have hj_nonneg : 0 ≤ (j : ℝ) := by positivity
    have hpoly_nonneg : 0 ≤ 2 * B * y ^ beta := by positivity
    positivity
  exact mul_nonneg hfactor_nonneg
    (boundedLemmaD2LocalEnvelope_nonneg hB_nonneg hy_nonneg)

/--
Scalar envelope bound for the fixed-rank binomial kernel once the rescaled CDF
is trapped between local power bounds. This is the pointwise algebra behind
the bounded Lemma D.2 dominated-kernel certificate.
-/
theorem boundedLemmaD2_binomial_kernel_norm_le_power_exp_of_rescaled_bounds
    {beta A B y g : ℝ} {j a : ℕ}
    (hA_pos : 0 < A) (hB_nonneg : 0 ≤ B)
    (hy_pos : 0 < y) (ha_pos_nat : 0 < a)
    (hlarge : 2 * j ≤ a)
    (hg_nonneg : 0 ≤ g) (hg_le_one : g ≤ 1)
    (hg_lower : A * (y ^ beta * (a : ℝ) ^ (-1 : ℝ)) ≤ g)
    (hg_upper : g ≤ B * (y ^ beta * (a : ℝ) ^ (-1 : ℝ))) :
    ‖(Nat.choose a j : ℝ) * g ^ j * (1 - g) ^ (a - j)‖ ≤
      B ^ j * y ^ (beta * (j : ℝ)) *
        Real.exp (-(A / 2) * y ^ beta) := by
  have ha_pos : 0 < (a : ℝ) := by exact_mod_cast ha_pos_nat
  have ha_ne : (a : ℝ) ≠ 0 := ne_of_gt ha_pos
  have hybeta_pos : 0 < y ^ beta := Real.rpow_pos_of_pos hy_pos beta
  have hybeta_nonneg : 0 ≤ y ^ beta := le_of_lt hybeta_pos
  have hchoose_nonneg : 0 ≤ (Nat.choose a j : ℝ) := by positivity
  have htail_nonneg : 0 ≤ 1 - g := sub_nonneg.mpr hg_le_one
  have hkernel_nonneg :
      0 ≤ (Nat.choose a j : ℝ) * g ^ j * (1 - g) ^ (a - j) :=
    mul_nonneg
      (mul_nonneg hchoose_nonneg (pow_nonneg hg_nonneg j))
      (pow_nonneg htail_nonneg (a - j))
  rw [Real.norm_of_nonneg hkernel_nonneg]
  have hupper_nonneg :
      0 ≤ B * (y ^ beta * (a : ℝ) ^ (-1 : ℝ)) :=
    hg_nonneg.trans hg_upper
  have hgpow_le :
      g ^ j ≤ (B * (y ^ beta * (a : ℝ) ^ (-1 : ℝ))) ^ j :=
    pow_le_pow_left₀ hg_nonneg hg_upper j
  have hchoose_le : (Nat.choose a j : ℝ) ≤ (a : ℝ) ^ j := by
    exact_mod_cast Nat.choose_le_pow a j
  have hfront_le_raw :
      (Nat.choose a j : ℝ) * g ^ j ≤
        (a : ℝ) ^ j *
          (B * (y ^ beta * (a : ℝ) ^ (-1 : ℝ))) ^ j :=
    mul_le_mul hchoose_le hgpow_le (pow_nonneg hg_nonneg j)
      (pow_nonneg ha_pos.le j)
  have hfront_eq :
      (a : ℝ) ^ j *
          (B * (y ^ beta * (a : ℝ) ^ (-1 : ℝ))) ^ j =
        B ^ j * y ^ (beta * (j : ℝ)) := by
    have hcancel :
        (a : ℝ) *
            (B * (y ^ beta * (a : ℝ) ^ (-1 : ℝ))) =
          B * y ^ beta := by
      rw [Real.rpow_neg_one]
      field_simp [ha_ne]
    have hy_pow :
        (y ^ beta) ^ j = y ^ (beta * (j : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hy_pos.le]
    calc
      (a : ℝ) ^ j *
          (B * (y ^ beta * (a : ℝ) ^ (-1 : ℝ))) ^ j
          = ((a : ℝ) *
              (B * (y ^ beta * (a : ℝ) ^ (-1 : ℝ)))) ^ j := by
            rw [← mul_pow]
      _ = (B * y ^ beta) ^ j := by rw [hcancel]
      _ = B ^ j * (y ^ beta) ^ j := by rw [mul_pow]
      _ = B ^ j * y ^ (beta * (j : ℝ)) := by
            rw [hy_pow]
  have hfront_le :
      (Nat.choose a j : ℝ) * g ^ j ≤
        B ^ j * y ^ (beta * (j : ℝ)) := by
    simpa [hfront_eq] using hfront_le_raw
  have hfront_bound_nonneg :
      0 ≤ B ^ j * y ^ (beta * (j : ℝ)) :=
    mul_nonneg (pow_nonneg hB_nonneg j)
      (le_of_lt (Real.rpow_pos_of_pos hy_pos (beta * (j : ℝ))))
  have hbase_le_exp :
      1 - g ≤ Real.exp (-(A * (y ^ beta * (a : ℝ) ^ (-1 : ℝ)))) := by
    calc
      1 - g ≤ 1 - A * (y ^ beta * (a : ℝ) ^ (-1 : ℝ)) :=
        sub_le_sub_left hg_lower 1
      _ ≤ Real.exp (-(A * (y ^ beta * (a : ℝ) ^ (-1 : ℝ)))) :=
        Real.one_sub_le_exp_neg
          (A * (y ^ beta * (a : ℝ) ^ (-1 : ℝ)))
  have htail_le_raw :
      (1 - g) ^ (a - j) ≤
        (Real.exp (-(A * (y ^ beta * (a : ℝ) ^ (-1 : ℝ))))) ^ (a - j) :=
    pow_le_pow_left₀ htail_nonneg hbase_le_exp (a - j)
  have hja : j ≤ a := by omega
  have hsub_ge_half : (1 / 2 : ℝ) ≤ ((a - j : ℕ) : ℝ) / (a : ℝ) := by
    rw [le_div_iff₀ ha_pos]
    rw [Nat.cast_sub hja]
    have hlarge_real : (2 * (j : ℝ)) ≤ (a : ℝ) := by
      exact_mod_cast hlarge
    nlinarith
  have hK_nonneg : 0 ≤ A * y ^ beta :=
    mul_nonneg hA_pos.le hybeta_nonneg
  have harg_le :
      ((a - j : ℕ) : ℝ) *
          (-(A * (y ^ beta * (a : ℝ) ^ (-1 : ℝ)))) ≤
        -(A / 2) * y ^ beta := by
    have hleft_eq :
        ((a - j : ℕ) : ℝ) *
            (-(A * (y ^ beta * (a : ℝ) ^ (-1 : ℝ)))) =
          -(A * y ^ beta) * (((a - j : ℕ) : ℝ) / (a : ℝ)) := by
      rw [Real.rpow_neg_one]
      field_simp [ha_ne]
    have hright_eq :
        -(A / 2) * y ^ beta = -(A * y ^ beta) * (1 / 2) := by
      ring
    rw [hleft_eq, hright_eq]
    exact mul_le_mul_of_nonpos_left hsub_ge_half (neg_nonpos.mpr hK_nonneg)
  have htail_le :
      (1 - g) ^ (a - j) ≤ Real.exp (-(A / 2) * y ^ beta) := by
    calc
      (1 - g) ^ (a - j)
          ≤ (Real.exp (-(A * (y ^ beta * (a : ℝ) ^ (-1 : ℝ))))) ^ (a - j) :=
            htail_le_raw
      _ = Real.exp
          (((a - j : ℕ) : ℝ) *
            (-(A * (y ^ beta * (a : ℝ) ^ (-1 : ℝ))))) := by
            rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (-(A / 2) * y ^ beta) :=
            Real.exp_le_exp.mpr harg_le
  calc
    (Nat.choose a j : ℝ) * g ^ j * (1 - g) ^ (a - j)
        ≤ (B ^ j * y ^ (beta * (j : ℝ))) *
            Real.exp (-(A / 2) * y ^ beta) :=
      mul_le_mul hfront_le htail_le
        (pow_nonneg htail_nonneg (a - j)) hfront_bound_nonneg
    _ = B ^ j * y ^ (beta * (j : ℝ)) *
          Real.exp (-(A / 2) * y ^ beta) := by ring

/--
The gamma-shaped envelope used in bounded Lemma D.2 is integrable on
`(0,∞)` for any positive power exponent.
-/
theorem integrableOn_rpow_mul_exp_neg_mul_rpow_of_pos
    {p q b : ℝ} (hp : 0 < p) (hq : -1 < q) (hb : 0 < b) :
    MeasureTheory.IntegrableOn
      (fun x : ℝ => x ^ q * Real.exp (-b * x ^ p))
      (Set.Ioi (0 : ℝ)) := by
  let s : ℝ := (q + 1) / p
  have hs_pos : 0 < s :=
    div_pos (by linarith) hp
  have hgamma :
      MeasureTheory.IntegrableOn
        (fun u : ℝ => Real.exp (-u) * u ^ (s - 1))
        (Set.Ioi (0 : ℝ)) :=
    Real.GammaIntegral_convergent hs_pos
  have hgamma0 :
      MeasureTheory.IntegrableOn
        (fun u : ℝ => Real.exp (-u) * u ^ (s - 1))
        (Set.Ioi (b * 0)) := by
    simpa using hgamma
  have hscaled_raw :
      MeasureTheory.IntegrableOn
        (fun u : ℝ => Real.exp (-(b * u)) * (b * u) ^ (s - 1))
        (Set.Ioi (0 : ℝ)) := by
    simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using
      (MeasureTheory.integrableOn_Ioi_comp_mul_left_iff
        (fun u : ℝ => Real.exp (-u) * u ^ (s - 1))
        (0 : ℝ) hb).mpr hgamma0
  have hbpow_ne : b ^ (s - 1) ≠ 0 :=
    (Real.rpow_pos_of_pos hb (s - 1)).ne'
  have hscaled :
      MeasureTheory.IntegrableOn
        (fun u : ℝ => Real.exp (-b * u) * u ^ (s - 1))
        (Set.Ioi (0 : ℝ)) := by
    have hscaled_const :
        MeasureTheory.IntegrableOn
          (fun u : ℝ =>
            (b ^ (s - 1))⁻¹ *
              (Real.exp (-(b * u)) * (b * u) ^ (s - 1)))
          (Set.Ioi (0 : ℝ)) :=
      hscaled_raw.const_mul (b ^ (s - 1))⁻¹
    refine hscaled_const.congr_fun ?_ measurableSet_Ioi
    intro u hu
    have hu_nonneg : 0 ≤ u := le_of_lt hu
    dsimp
    rw [Real.mul_rpow hb.le hu_nonneg]
    field_simp [hbpow_ne]
  have hcomp :
      MeasureTheory.IntegrableOn
        (fun x : ℝ =>
          x ^ (p - 1) •
            ((fun u : ℝ => Real.exp (-b * u) * u ^ (s - 1)) (x ^ p)))
        (Set.Ioi (0 : ℝ)) :=
          (MeasureTheory.integrableOn_Ioi_comp_rpow_iff'
        (fun u : ℝ => Real.exp (-b * u) * u ^ (s - 1))
        (ne_of_gt hp)).mpr hscaled
  refine hcomp.congr_fun ?_ measurableSet_Ioi
  intro x hx
  have hx_nonneg : 0 ≤ x := le_of_lt hx
  have hx_pos : 0 < x := hx
  have hpow :
      (x ^ p) ^ (s - 1) = x ^ (q + 1 - p) := by
    rw [← Real.rpow_mul hx_nonneg]
    congr 1
    dsimp [s]
    field_simp [ne_of_gt hp]
  simp only [smul_eq_mul, hpow]
  have hmul_pow :
      x ^ (p - 1) * x ^ (q + 1 - p) = x ^ q := by
    rw [← Real.rpow_add hx_pos]
    congr 1
    ring
  calc
    x ^ (p - 1) * (Real.exp (-b * x ^ p) * x ^ (q + 1 - p))
        = (x ^ (p - 1) * x ^ (q + 1 - p)) *
            Real.exp (-b * x ^ p) := by ring
    _ = x ^ q * Real.exp (-b * x ^ p) := by rw [hmul_pow]

/-- Integrability of the bounded Lemma D.2 local envelope on `(0,∞)`. -/
theorem boundedLemmaD2LocalEnvelope_integrable
    {beta A B : ℝ} (hbeta_pos : 0 < beta) (hA_pos : 0 < A)
    (j : ℕ) :
    MeasureTheory.Integrable
      (boundedLemmaD2LocalEnvelope beta A B j)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hq : -1 < beta * (j : ℝ) := by
    have hj_nonneg : 0 ≤ (j : ℝ) := by positivity
    have hmul_nonneg : 0 ≤ beta * (j : ℝ) :=
      mul_nonneg hbeta_pos.le hj_nonneg
    linarith
  have hb : 0 < A / 2 := by positivity
  have hbase :=
    (integrableOn_rpow_mul_exp_neg_mul_rpow_of_pos
      (p := beta) (q := beta * (j : ℝ)) (b := A / 2)
      hbeta_pos hq hb).integrable
  have hconst :
      MeasureTheory.Integrable
        (fun x : ℝ =>
          B ^ j *
            (x ^ (beta * (j : ℝ)) *
              Real.exp (-(A / 2) * x ^ beta)))
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    hbase.const_mul (B ^ j)
  refine hconst.congr (Filter.Eventually.of_forall ?_)
  intro x
  unfold boundedLemmaD2LocalEnvelope
  congr 3

/--
Integrability of the finite-difference local envelope on `(0,∞)`. The extra
factor contributes one additional polynomial moment, still dominated by the
same exponential tail.
-/
theorem boundedLemmaD2ForwardDifferenceLocalEnvelope_integrable
    {beta A B : ℝ} (hbeta_pos : 0 < beta) (hA_pos : 0 < A)
    (j : ℕ) :
    MeasureTheory.Integrable
      (boundedLemmaD2ForwardDifferenceLocalEnvelope beta A B j)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  let μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
  have hlocal :
      MeasureTheory.Integrable
        (boundedLemmaD2LocalEnvelope beta A B j) μ := by
    simpa [μ] using
      boundedLemmaD2LocalEnvelope_integrable hbeta_pos hA_pos j
  have hfirst :
      MeasureTheory.Integrable
        (fun y : ℝ =>
          (2 * (j : ℝ)) *
            boundedLemmaD2LocalEnvelope beta A B j y) μ :=
    hlocal.const_mul (2 * (j : ℝ))
  have hq_next : -1 < beta * ((j : ℝ) + 1) := by
    have hj_nonneg : 0 ≤ (j : ℝ) := by positivity
    have hsum_pos : 0 < (j : ℝ) + 1 := by positivity
    have hmul_pos : 0 < beta * ((j : ℝ) + 1) :=
      mul_pos hbeta_pos hsum_pos
    linarith
  have hb : 0 < A / 2 := by positivity
  have hnext_base :
      MeasureTheory.Integrable
        (fun y : ℝ =>
          y ^ (beta * ((j : ℝ) + 1)) *
            Real.exp (-(A / 2) * y ^ beta)) μ := by
    simpa [μ] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow_of_pos
        (p := beta) (q := beta * ((j : ℝ) + 1)) (b := A / 2)
        hbeta_pos hq_next hb).integrable
  have hsecond :
      MeasureTheory.Integrable
        (fun y : ℝ =>
          (4 * B * B ^ j) *
            (y ^ (beta * ((j : ℝ) + 1)) *
              Real.exp (-(A / 2) * y ^ beta))) μ :=
    hnext_base.const_mul (4 * B * B ^ j)
  have hsum := hfirst.add hsecond
  refine hsum.congr ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with y hy
  have hy_pos : 0 < y := hy
  have hpow_mul :
      y ^ beta * y ^ (beta * (j : ℝ)) =
        y ^ (beta * ((j : ℝ) + 1)) := by
    rw [← Real.rpow_add hy_pos]
    congr 1
    ring
  unfold boundedLemmaD2ForwardDifferenceLocalEnvelope
    boundedLemmaD2LocalEnvelope
  dsimp
  rw [← hpow_mul]
  ring

theorem bounded_one_sub_div_pow_tendsto_exp (z : ℝ) :
    Tendsto
      (fun a : ℕ => (1 - z / (a : ℝ)) ^ a)
      atTop (nhds (Real.exp (-z))) := by
  simpa [sub_eq_add_neg, neg_div] using
    Real.tendsto_one_add_div_pow_exp (-z)

/--
Fixed-rank version of the preceding exponential limit.

Lemma D.2 keeps `j` fixed while the exponent is `a - j`; this verifies that
removing finitely many factors does not change the `exp(-z)` limit.
-/
theorem bounded_one_sub_div_pow_sub_tendsto_exp (z : ℝ) (j : ℕ) :
    Tendsto
      (fun a : ℕ => (1 - z / (a : ℝ)) ^ (a - j))
      atTop (nhds (Real.exp (-z))) := by
  have hbase :
      Tendsto (fun a : ℕ => 1 - z / (a : ℝ)) atTop (nhds 1) := by
    simpa using
      tendsto_const_nhds.sub
        (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) z)
  have hdenom :
      Tendsto (fun a : ℕ => (1 - z / (a : ℝ)) ^ j)
        atTop (nhds 1) := by
    simpa using hbase.pow j
  have hquot :
      Tendsto
        (fun a : ℕ =>
          (1 - z / (a : ℝ)) ^ a / (1 - z / (a : ℝ)) ^ j)
        atTop (nhds (Real.exp (-z))) := by
    have h :=
      (bounded_one_sub_div_pow_tendsto_exp z).div hdenom
        (by norm_num : (1 : ℝ) ≠ 0)
    simpa using h
  refine Tendsto.congr' ?_ hquot
  filter_upwards
    [eventually_ge_atTop j,
      hbase.eventually_ne (by norm_num : (1 : ℝ) ≠ 0)] with a ha_ge hbase_ne
  let b : ℝ := 1 - z / (a : ℝ)
  have hb_ne : b ≠ 0 := hbase_ne
  have hpow_ne : b ^ j ≠ 0 := pow_ne_zero j hb_ne
  have hpow_add : b ^ (a - j) * b ^ j = b ^ a := by
    rw [← pow_add, Nat.sub_add_cancel ha_ge]
  change b ^ a / b ^ j =
    b ^ (a - j)
  rw [← hpow_add, mul_div_cancel_right₀ _ hpow_ne]

/--
General exponential kernel limit: if `a * u a -> z`, then
`(1 - u a)^a -> exp(-z)`.
-/
theorem bounded_one_sub_of_nat_mul_tendsto_pow_tendsto_exp
    {u : ℕ → ℝ} {z : ℝ}
    (hu : Tendsto (fun a : ℕ => (a : ℝ) * u a) atTop (nhds z)) :
    Tendsto
      (fun a : ℕ => (1 - u a) ^ a)
      atTop (nhds (Real.exp (-z))) := by
  have hneg :
      Tendsto (fun a : ℕ => (a : ℝ) * (-(u a))) atTop (nhds (-z)) := by
    simpa [mul_neg] using hu.neg
  simpa [sub_eq_add_neg] using
    Real.tendsto_one_add_pow_exp_of_tendsto hneg

/--
Fixed-rank version of the general exponential kernel limit. This is the
analytic shape of the Lemma D.2 factor `(1 - G(x))^(a-j)`.
-/
theorem bounded_one_sub_of_nat_mul_tendsto_pow_sub_tendsto_exp
    {u : ℕ → ℝ} {z : ℝ}
    (hu : Tendsto (fun a : ℕ => (a : ℝ) * u a) atTop (nhds z))
    (j : ℕ) :
    Tendsto
      (fun a : ℕ => (1 - u a) ^ (a - j))
      atTop (nhds (Real.exp (-z))) := by
  have hu_zero : Tendsto u atTop (nhds 0) := by
    have hdiv :
        Tendsto
          (fun a : ℕ => ((a : ℝ) * u a) / (a : ℝ))
          atTop (nhds 0) :=
      hu.div_atTop tendsto_natCast_atTop_atTop
    refine Tendsto.congr' ?_ hdiv
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with a ha
    have ha_ne : (a : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt ha)
    field_simp [ha_ne]
  have hbase : Tendsto (fun a : ℕ => 1 - u a) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hu_zero
  have hdenom :
      Tendsto (fun a : ℕ => (1 - u a) ^ j) atTop (nhds 1) := by
    simpa using hbase.pow j
  have hquot :
      Tendsto
        (fun a : ℕ => (1 - u a) ^ a / (1 - u a) ^ j)
        atTop (nhds (Real.exp (-z))) := by
    have h :=
      (bounded_one_sub_of_nat_mul_tendsto_pow_tendsto_exp hu).div hdenom
        (by norm_num : (1 : ℝ) ≠ 0)
    simpa using h
  refine Tendsto.congr' ?_ hquot
  filter_upwards
    [eventually_ge_atTop j,
      hbase.eventually_ne (by norm_num : (1 : ℝ) ≠ 0)] with a ha_ge hbase_ne
  let b : ℝ := 1 - u a
  have hb_ne : b ≠ 0 := hbase_ne
  have hpow_ne : b ^ j ≠ 0 := pow_ne_zero j hb_ne
  have hpow_add : b ^ (a - j) * b ^ j = b ^ a := by
    rw [← pow_add, Nat.sub_add_cancel ha_ge]
  change b ^ a / b ^ j =
    b ^ (a - j)
  rw [← hpow_add, mul_div_cancel_right₀ _ hpow_ne]

/--
Paper-local name for the reusable near-zero CDF power-law sandwich used in
Lemma D.2.

For the reflected CDF `G`, the source proof derives this from the density
asymptotic `g(x) ~ c*x^(β-1)` by integrating near zero.
-/
abbrev BoundedTailCDFPowerSandwich :=
  AppliedModelingLib.Probability.CDFPowerTailSandwich

namespace BoundedTailCDFPowerSandwich

theorem of_eventually_eq_const_mul_power
    {G : ℝ → ℝ} {beta c : ℝ}
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (hG :
      ∀ᶠ x in 𝓝[>] (0 : ℝ),
        G x = (c / beta) * x ^ beta) :
    BoundedTailCDFPowerSandwich G beta c :=
  AppliedModelingLib.Probability.CDFPowerTailSandwich.of_eventually_eq_const_mul_power
    hbeta_pos hc_pos hG

theorem of_reflectedCDFMass_upper_endpoint_tail_sandwich
    {μ : MeasureTheory.Measure ℝ} {M beta c : ℝ}
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (htail :
      ∀ {ε : ℝ}, 0 < ε →
        ∀ᶠ x in 𝓝[>] (0 : ℝ),
          (1 - ε) * (c / beta) * x ^ beta ≤
              μ.real (Set.Ici (M - x)) ∧
            μ.real (Set.Ici (M - x)) ≤
              (1 + ε) * (c / beta) * x ^ beta) :
    BoundedTailCDFPowerSandwich
      (AppliedModelingLib.Probability.reflectedCDFMass μ M) beta c :=
  AppliedModelingLib.Probability.CDFPowerTailSandwich.of_reflectedCDFMass_upper_endpoint_tail_sandwich
    hbeta_pos hc_pos htail

theorem of_reflectedCDFMass_upper_endpoint_eventually_eq_power
    {μ : MeasureTheory.Measure ℝ} {M beta c : ℝ}
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (htail :
      ∀ᶠ x in 𝓝[>] (0 : ℝ),
        μ.real (Set.Ici (M - x)) = (c / beta) * x ^ beta) :
    BoundedTailCDFPowerSandwich
      (AppliedModelingLib.Probability.reflectedCDFMass μ M) beta c :=
  AppliedModelingLib.Probability.CDFPowerTailSandwich.of_reflectedCDFMass_upper_endpoint_eventually_eq_power
    hbeta_pos hc_pos htail

theorem identity_beta_one :
    BoundedTailCDFPowerSandwich (fun x : ℝ => x) 1 1 :=
  AppliedModelingLib.Probability.CDFPowerTailSandwich.identity_beta_one

/--
Power integral used by the bounded-density bridge:
`∫_0^x u^(β-1) du = x^β / β` for `0 ≤ x` and `β > 0`.
-/
theorem integral_Ioo_zero_rpow_sub_one_eq
    {beta x : ℝ} (hbeta_pos : 0 < beta) (hx_nonneg : 0 ≤ x) :
    ∫ u in Set.Ioo (0 : ℝ) x, u ^ (beta - 1) = x ^ beta / beta := by
  have hpow :=
    integral_rpow
      (a := (0 : ℝ)) (b := x) (r := beta - 1)
      (Or.inl (by linarith : -1 < beta - 1))
  rw [intervalIntegral.integral_of_le hx_nonneg] at hpow
  rw [MeasureTheory.integral_Ioc_eq_integral_Ioo] at hpow
  have hden : (beta - 1) + 1 = beta := by ring
  calc
    ∫ u in Set.Ioo (0 : ℝ) x, u ^ (beta - 1)
        = (x ^ ((beta - 1) + 1) - 0 ^ ((beta - 1) + 1)) /
            ((beta - 1) + 1) := hpow
    _ = (x ^ beta - 0 ^ beta) / beta := by rw [hden]
    _ = (x ^ beta - 0) / beta := by
          rw [Real.zero_rpow (ne_of_gt hbeta_pos)]
    _ = x ^ beta / beta := by ring

/--
If a property holds eventually on the right-neighborhood of zero, then, for all
sufficiently small positive `x`, it holds for every `u ∈ (0, x)`.
-/
theorem eventually_forall_pos_lt_of_eventually_nhdsGT_zero
    {P : ℝ → Prop}
    (hP : ∀ᶠ u in 𝓝[>] (0 : ℝ), P u) :
    ∀ᶠ x in 𝓝[>] (0 : ℝ), ∀ u : ℝ, 0 < u → u < x → P u := by
  have hP_nhds :
      ∀ᶠ u in 𝓝 (0 : ℝ), u ∈ Set.Ioi (0 : ℝ) → P u :=
    eventually_nhdsWithin_iff.1 hP
  rcases Metric.eventually_nhds_iff.1 hP_nhds with
    ⟨δ, hδ_pos, hδ⟩
  filter_upwards
    [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ_pos)] with
    x hx_pos hx_ltδ u hu_pos hu_lt
  have hu_ltδ : u < δ := lt_trans hu_lt hx_ltδ
  have hdist : dist u (0 : ℝ) < δ := by
    simpa [Real.dist_eq, abs_of_nonneg (le_of_lt hu_pos)] using hu_ltδ
  exact hδ hdist hu_pos

/--
The paper's density asymptotic convention, expressed as a right-neighborhood
ratio limit, gives the interval-uniform density sandwich used by the bounded
tail-mass integral bridge.
-/
theorem density_sandwich_of_tendsto_ratio
    {g : ℝ → ℝ} {beta c : ℝ}
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (hratio :
      Tendsto (fun u : ℝ => g u / (c * u ^ (beta - 1)))
        (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ))) :
    ∀ {ε : ℝ}, 0 < ε →
      ∀ᶠ x in 𝓝[>] (0 : ℝ),
        ∀ u : ℝ, 0 < u → u < x →
          (1 - ε) * c * u ^ (beta - 1) ≤ g u ∧
            g u ≤ (1 + ε) * c * u ^ (beta - 1) := by
  intro ε hε
  have hnear :
      Set.Ioo (1 - ε) (1 + ε) ∈ 𝓝 (1 : ℝ) :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have hpoint :
      ∀ᶠ u in 𝓝[>] (0 : ℝ),
        (1 - ε) * c * u ^ (beta - 1) ≤ g u ∧
          g u ≤ (1 + ε) * c * u ^ (beta - 1) := by
    filter_upwards [hratio.eventually hnear, self_mem_nhdsWithin] with
      u hratio_u hu_pos
    have hpow_pos : 0 < u ^ (beta - 1) :=
      Real.rpow_pos_of_pos hu_pos _
    have hden_pos : 0 < c * u ^ (beta - 1) :=
      mul_pos hc_pos hpow_pos
    have hden_ne : c * u ^ (beta - 1) ≠ 0 := ne_of_gt hden_pos
    have hlow :=
      mul_lt_mul_of_pos_right hratio_u.1 hden_pos
    have hhigh :=
      mul_lt_mul_of_pos_right hratio_u.2 hden_pos
    constructor
    · exact le_of_lt (by
        simpa [div_mul_cancel₀ _ hden_ne, mul_assoc] using hlow)
    · exact le_of_lt (by
        simpa [div_mul_cancel₀ _ hden_ne, mul_assoc] using hhigh)
  exact eventually_forall_pos_lt_of_eventually_nhdsGT_zero hpoint

/--
Source-calculus bridge for the bounded branch.

If the local upper-tail mass is represented as an integral of a reflected
density `g`, and `g(u)` is eventually sandwiched by
`(1 ± ε) * c * u^(β-1)` on every sufficiently small interval `(0, x)`, then the
upper-tail mass has the sandwich used by Lemma D.2.
-/
theorem upper_tail_mass_sandwich_of_density_integral_sandwich
    {mass g : ℝ → ℝ} {beta c : ℝ}
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (h_integrable :
      ∀ᶠ x in 𝓝[>] (0 : ℝ),
        MeasureTheory.IntegrableOn g (Set.Ioo (0 : ℝ) x))
    (hmass :
      ∀ᶠ x in 𝓝[>] (0 : ℝ),
        mass x = ∫ u in Set.Ioo (0 : ℝ) x, g u)
    (hdensity :
      ∀ {ε : ℝ}, 0 < ε →
        ∀ᶠ x in 𝓝[>] (0 : ℝ),
          ∀ u : ℝ, 0 < u → u < x →
            (1 - ε) * c * u ^ (beta - 1) ≤ g u ∧
              g u ≤ (1 + ε) * c * u ^ (beta - 1)) :
    ∀ {ε : ℝ}, 0 < ε →
      ∀ᶠ x in 𝓝[>] (0 : ℝ),
        (1 - ε) * (c / beta) * x ^ beta ≤ mass x ∧
          mass x ≤ (1 + ε) * (c / beta) * x ^ beta := by
  intro ε hε
  filter_upwards [self_mem_nhdsWithin, h_integrable, hmass, hdensity hε] with
    x hx_pos hg_int hmass_eq hdensity_x
  have hx_nonneg : 0 ≤ x := le_of_lt hx_pos
  have hpow_int :
      MeasureTheory.IntegrableOn (fun u : ℝ => u ^ (beta - 1))
        (Set.Ioo (0 : ℝ) x) := by
    have hpow_Ioc :
        MeasureTheory.IntegrableOn (fun u : ℝ => u ^ (beta - 1))
          (Set.Ioc (0 : ℝ) x) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hx_nonneg).1
        (intervalIntegral.intervalIntegrable_rpow'
          (by linarith : -1 < beta - 1))
    exact
      (integrableOn_Ioc_iff_integrableOn_Ioo
        (μ := MeasureTheory.volume)
        (f := fun u : ℝ => u ^ (beta - 1))
        (a := (0 : ℝ)) (b := x)).1 hpow_Ioc
  have hleft_int :
      MeasureTheory.IntegrableOn
        (fun u : ℝ => (1 - ε) * c * u ^ (beta - 1))
        (Set.Ioo (0 : ℝ) x) := hpow_int.const_mul _
  have hright_int :
      MeasureTheory.IntegrableOn
        (fun u : ℝ => (1 + ε) * c * u ^ (beta - 1))
        (Set.Ioo (0 : ℝ) x) := hpow_int.const_mul _
  have hlow :
      ∫ u in Set.Ioo (0 : ℝ) x, (1 - ε) * c * u ^ (beta - 1) ≤
        ∫ u in Set.Ioo (0 : ℝ) x, g u := by
    refine MeasureTheory.setIntegral_mono_on hleft_int hg_int measurableSet_Ioo ?_
    intro u hu
    exact (hdensity_x u hu.1 hu.2).1
  have hhigh :
      ∫ u in Set.Ioo (0 : ℝ) x, g u ≤
        ∫ u in Set.Ioo (0 : ℝ) x, (1 + ε) * c * u ^ (beta - 1) := by
    refine MeasureTheory.setIntegral_mono_on hg_int hright_int measurableSet_Ioo ?_
    intro u hu
    exact (hdensity_x u hu.1 hu.2).2
  have hpow_eval :=
    integral_Ioo_zero_rpow_sub_one_eq (beta := beta) (x := x)
      hbeta_pos hx_nonneg
  have hleft_eval :
      ∫ u in Set.Ioo (0 : ℝ) x, (1 - ε) * c * u ^ (beta - 1) =
        (1 - ε) * (c / beta) * x ^ beta := by
    rw [MeasureTheory.integral_const_mul, hpow_eval]
    ring
  have hright_eval :
      ∫ u in Set.Ioo (0 : ℝ) x, (1 + ε) * c * u ^ (beta - 1) =
        (1 + ε) * (c / beta) * x ^ beta := by
    rw [MeasureTheory.integral_const_mul, hpow_eval]
    ring
  constructor
  · rw [← hleft_eval, hmass_eq]
    exact hlow
  · rw [← hright_eval, hmass_eq]
    exact hhigh

/--
Version of `upper_tail_mass_sandwich_of_density_integral_sandwich` from the
paper's asymptotic density-ratio convention.
-/
theorem upper_tail_mass_sandwich_of_density_ratio_integral
    {mass g : ℝ → ℝ} {beta c : ℝ}
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (h_integrable :
      ∀ᶠ x in 𝓝[>] (0 : ℝ),
        MeasureTheory.IntegrableOn g (Set.Ioo (0 : ℝ) x))
    (hmass :
      ∀ᶠ x in 𝓝[>] (0 : ℝ),
        mass x = ∫ u in Set.Ioo (0 : ℝ) x, g u)
    (hratio :
      Tendsto (fun u : ℝ => g u / (c * u ^ (beta - 1)))
        (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ))) :
    ∀ {ε : ℝ}, 0 < ε →
      ∀ᶠ x in 𝓝[>] (0 : ℝ),
        (1 - ε) * (c / beta) * x ^ beta ≤ mass x ∧
          mass x ≤ (1 + ε) * (c / beta) * x ^ beta :=
  upper_tail_mass_sandwich_of_density_integral_sandwich
    hbeta_pos hc_pos h_integrable hmass
    (density_sandwich_of_tendsto_ratio hbeta_pos hc_pos hratio)

/--
Packaged bounded-tail certificate from the paper's upper-endpoint density
convention for a probability measure with upper endpoint `M`.
-/
theorem of_reflectedCDFMass_upper_endpoint_density_ratio_integral
    {μ : MeasureTheory.Measure ℝ} {M beta c : ℝ} {g : ℝ → ℝ}
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (h_integrable :
      ∀ᶠ x in 𝓝[>] (0 : ℝ),
        MeasureTheory.IntegrableOn g (Set.Ioo (0 : ℝ) x))
    (hmass :
      ∀ᶠ x in 𝓝[>] (0 : ℝ),
        μ.real (Set.Ici (M - x)) =
          ∫ u in Set.Ioo (0 : ℝ) x, g u)
    (hratio :
      Tendsto (fun u : ℝ => g u / (c * u ^ (beta - 1)))
        (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ))) :
    BoundedTailCDFPowerSandwich
      (AppliedModelingLib.Probability.reflectedCDFMass μ M) beta c :=
  of_reflectedCDFMass_upper_endpoint_tail_sandwich hbeta_pos hc_pos
    (upper_tail_mass_sandwich_of_density_ratio_integral
      hbeta_pos hc_pos h_integrable hmass hratio)

theorem exists_local_cdf_power_bounds
    {G : ℝ → ℝ} {beta c : ℝ}
    (C : BoundedTailCDFPowerSandwich G beta c) :
    ∃ delta A B : ℝ,
      0 < delta ∧ 0 < A ∧ 0 ≤ B ∧
        (∀ x : ℝ, 0 < x → x < delta → A * x ^ beta ≤ G x) ∧
        (∀ x : ℝ, 0 < x → x < delta → G x ≤ B * x ^ beta) :=
  AppliedModelingLib.Probability.CDFPowerTailSandwich.exists_local_cdf_power_bounds C

/--
After the source change of variables `x = y * a^(-1/β)`, the near-zero CDF
sandwich applies eventually for every fixed `y > 0`.
-/
theorem eventually_rescaled_cdf_power_sandwich
    {G : ℝ → ℝ} {beta c : ℝ}
    (C : BoundedTailCDFPowerSandwich G beta c)
    {ε y : ℝ} (hε : 0 < ε) (hy_pos : 0 < y) :
    ∀ᶠ a : ℕ in atTop,
      (1 - ε) * (c / beta) *
          (y * boundedTailScale beta a) ^ beta ≤
          G (y * boundedTailScale beta a) ∧
        G (y * boundedTailScale beta a) ≤
          (1 + ε) * (c / beta) *
            (y * boundedTailScale beta a) ^ beta := by
  have hrescale :
      Tendsto (fun a => y * boundedTailScale beta a)
        atTop (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      (fun a => y * boundedTailScale beta a)
      (boundedTailScale_const_mul_tendsto_zero C.beta_pos) ?_
    filter_upwards [boundedTailScale_eventually_pos beta] with a hscale
    exact mul_pos hy_pos hscale
  exact hrescale.eventually (C.cdf_power_sandwich hε)

/--
Simplified rescaled CDF sandwich: after `x = y * a^(-1/β)`, the power term
becomes `y^β * a^-1`.
-/
theorem eventually_rescaled_cdf_power_sandwich_inv_nat
    {G : ℝ → ℝ} {beta c : ℝ}
    (C : BoundedTailCDFPowerSandwich G beta c)
    {ε y : ℝ} (hε : 0 < ε) (hy_pos : 0 < y) :
    ∀ᶠ a : ℕ in atTop,
      (1 - ε) * (c / beta) *
          (y ^ beta * (a : ℝ) ^ (-1 : ℝ)) ≤
          G (y * boundedTailScale beta a) ∧
        G (y * boundedTailScale beta a) ≤
          (1 + ε) * (c / beta) *
            (y ^ beta * (a : ℝ) ^ (-1 : ℝ)) := by
  filter_upwards
    [C.eventually_rescaled_cdf_power_sandwich hε hy_pos,
      eventually_gt_atTop (0 : ℕ)] with a hbound ha
  simpa [boundedTailScale_rescaled_rpow_beta C.beta_pos hy_pos ha]
    using hbound

/--
After multiplying by `a`, the rescaled CDF sandwich becomes a constant
sandwich around `(c / beta) * y^beta`.
-/
theorem eventually_rescaled_cdf_nat_mul_sandwich
    {G : ℝ → ℝ} {beta c : ℝ}
    (C : BoundedTailCDFPowerSandwich G beta c)
    {ε y : ℝ} (hε : 0 < ε) (hy_pos : 0 < y) :
    ∀ᶠ a : ℕ in atTop,
      (1 - ε) * ((c / beta) * y ^ beta) ≤
          (a : ℝ) * G (y * boundedTailScale beta a) ∧
        (a : ℝ) * G (y * boundedTailScale beta a) ≤
          (1 + ε) * ((c / beta) * y ^ beta) := by
  filter_upwards
    [C.eventually_rescaled_cdf_power_sandwich_inv_nat hε hy_pos,
      eventually_gt_atTop (0 : ℕ)] with a hbound ha
  have ha_pos : 0 < (a : ℝ) := by exact_mod_cast ha
  have ha_ne : (a : ℝ) ≠ 0 := ne_of_gt ha_pos
  have hcancel (d : ℝ) :
      (a : ℝ) *
          (d * (c / beta) * (y ^ beta * (a : ℝ) ^ (-1 : ℝ))) =
        d * ((c / beta) * y ^ beta) := by
    rw [Real.rpow_neg_one]
    field_simp [ha_ne]
  have hleft :=
    mul_le_mul_of_nonneg_left hbound.1 (le_of_lt ha_pos)
  have hright :=
    mul_le_mul_of_nonneg_left hbound.2 (le_of_lt ha_pos)
  constructor
  · calc
      (1 - ε) * ((c / beta) * y ^ beta)
          =
            (a : ℝ) *
              ((1 - ε) * (c / beta) *
                (y ^ beta * (a : ℝ) ^ (-1 : ℝ))) := by
              rw [hcancel]
      _ ≤ (a : ℝ) * G (y * boundedTailScale beta a) := hleft
  · calc
      (a : ℝ) * G (y * boundedTailScale beta a)
          ≤
            (a : ℝ) *
              ((1 + ε) * (c / beta) *
                (y ^ beta * (a : ℝ) ^ (-1 : ℝ))) := hright
      _ =
          (1 + ε) * ((c / beta) * y ^ beta) := by
            rw [hcancel]

/--
Pointwise rescaled CDF convergence used in Lemma D.2: for each fixed
`y > 0`, `a * G(y * a^(-1/beta))` tends to `(c / beta) * y^beta`.
-/
theorem rescaled_cdf_nat_mul_tendsto
    {G : ℝ → ℝ} {beta c : ℝ}
    (C : BoundedTailCDFPowerSandwich G beta c)
    {y : ℝ} (hy_pos : 0 < y) :
    Tendsto
      (fun a : ℕ => (a : ℝ) * G (y * boundedTailScale beta a))
      atTop (nhds ((c / beta) * y ^ beta)) := by
  let z : ℝ := (c / beta) * y ^ beta
  have hz_pos : 0 < z :=
    mul_pos (div_pos C.c_pos C.beta_pos)
      (Real.rpow_pos_of_pos hy_pos beta)
  refine Metric.tendsto_nhds.mpr ?_
  intro δ hδ
  let ε : ℝ := δ / (2 * z)
  have hε : 0 < ε :=
    div_pos hδ (mul_pos two_pos hz_pos)
  filter_upwards [C.eventually_rescaled_cdf_nat_mul_sandwich hε hy_pos] with a hsand
  have hleft :
      (1 - ε) * z ≤ (a : ℝ) * G (y * boundedTailScale beta a) := by
    simpa [z] using hsand.1
  have hright :
      (a : ℝ) * G (y * boundedTailScale beta a) ≤ (1 + ε) * z := by
    simpa [z] using hsand.2
  have habs :
      |(a : ℝ) * G (y * boundedTailScale beta a) - z| ≤ ε * z := by
    rw [abs_sub_le_iff]
    constructor <;> nlinarith [hleft, hright, hz_pos]
  have hεz : ε * z = δ / 2 := by
    dsimp [ε]
    field_simp [ne_of_gt hz_pos]
  rw [Real.dist_eq]
  exact lt_of_le_of_lt habs (by rw [hεz]; linarith)

/--
Rescaled bounded-tail kernel limit for the `a` exponent:
`(1 - G(y * a^(-1/beta)))^a -> exp(-((c / beta) * y^beta))`.
-/
theorem rescaled_cdf_one_sub_pow_tendsto_exp
    {G : ℝ → ℝ} {beta c : ℝ}
    (C : BoundedTailCDFPowerSandwich G beta c)
    {y : ℝ} (hy_pos : 0 < y) :
    Tendsto
      (fun a : ℕ =>
        (1 - G (y * boundedTailScale beta a)) ^ a)
      atTop (nhds (Real.exp (-((c / beta) * y ^ beta)))) :=
  bounded_one_sub_of_nat_mul_tendsto_pow_tendsto_exp
    (C.rescaled_cdf_nat_mul_tendsto hy_pos)

/--
Fixed-rank rescaled bounded-tail kernel limit for Lemma D.2:
`(1 - G(y * a^(-1/beta)))^(a-j) -> exp(-((c / beta) * y^beta))`.
-/
theorem rescaled_cdf_one_sub_pow_sub_tendsto_exp
    {G : ℝ → ℝ} {beta c : ℝ}
    (C : BoundedTailCDFPowerSandwich G beta c)
    {y : ℝ} (hy_pos : 0 < y) (j : ℕ) :
    Tendsto
      (fun a : ℕ =>
        (1 - G (y * boundedTailScale beta a)) ^ (a - j))
      atTop (nhds (Real.exp (-((c / beta) * y ^ beta)))) :=
  bounded_one_sub_of_nat_mul_tendsto_pow_sub_tendsto_exp
    (C.rescaled_cdf_nat_mul_tendsto hy_pos) j

/--
Pointwise Lemma D.2 binomial-kernel limit after the source substitution
`x = y * a^(-1/beta)`.
-/
theorem rescaled_cdf_binomial_kernel_tendsto
    {G : ℝ → ℝ} {beta c : ℝ}
    (C : BoundedTailCDFPowerSandwich G beta c)
    {y : ℝ} (hy_pos : 0 < y) (j : ℕ) :
    Tendsto
      (fun a : ℕ =>
        (Nat.choose a j : ℝ) *
          (G (y * boundedTailScale beta a)) ^ j *
          (1 - G (y * boundedTailScale beta a)) ^ (a - j))
      atTop
      (nhds
        (Real.exp (-((c / beta) * y ^ beta)) *
          (((c / beta) * y ^ beta) ^ j) / j.factorial)) := by
  simpa using
    ProbabilityTheory.tendsto_choose_mul_pow_of_tendsto_mul_atTop j
      (C.rescaled_cdf_nat_mul_tendsto hy_pos)

end BoundedTailCDFPowerSandwich

/--
Index set for the paper's bounded proof after equation (95).

The source uses `i = 1, ..., k` and `j = 0, ..., i - 1`; here `i : Fin k`
stores the zero-based value `i_source - 1`, and `j : Fin (i.val + 1)` stores
the inner summation index.
-/
abbrev BoundedLemmaD2Index (k : ℕ) := Sigma (fun i : Fin k => Fin (i.val + 1))

/--
The limiting integrand in Lemma D.2 after the substitution
`x = y * a^(-1/beta)`.
-/
noncomputable def boundedLemmaD2LimitKernel
    (beta c : ℝ) (j : ℕ) (y : ℝ) : ℝ :=
  ((c / beta) ^ j / (j.factorial : ℝ)) *
    (y ^ (beta * (j : ℝ)) *
      Real.exp (-(c / beta) * y ^ beta))

/--
The rescaled finite-`a` Lemma D.2 kernel after the source substitution
`x = y * a^(-1/beta)`.
-/
noncomputable def boundedLemmaD2RescaledKernel
    (G : ℝ → ℝ) (beta : ℝ) (j a : ℕ) (y : ℝ) : ℝ :=
  (Nat.choose a j : ℝ) *
    (G (y * boundedTailScale beta a)) ^ j *
      (1 - G (y * boundedTailScale beta a)) ^ (a - j)

/--
Pointwise eventual envelope for the rescaled Lemma D.2 kernel on the growing
near-zero window, derived from local CDF power bounds.
-/
theorem boundedLemmaD2RescaledKernel_eventually_norm_le_power_exp_on_growing
    {G : ℝ → ℝ} {beta A B delta : ℝ} (j : ℕ)
    (hbeta_pos : 0 < beta)
    (hA_pos : 0 < A) (hB_nonneg : 0 ≤ B)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_lower :
      ∀ x : ℝ, 0 < x → x < delta → A * x ^ beta ≤ G x)
    (hG_upper :
      ∀ x : ℝ, 0 < x → x < delta → G x ≤ B * x ^ beta) :
    ∀ᶠ a in atTop,
      ∀ᵐ y ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
        y < delta / boundedTailScale beta a →
          ‖boundedLemmaD2RescaledKernel G beta j a y‖ ≤
            B ^ j * y ^ (beta * (j : ℝ)) *
              Real.exp (-(A / 2) * y ^ beta) := by
  filter_upwards
    [eventually_gt_atTop (0 : ℕ),
      eventually_ge_atTop (2 * j),
      boundedLemmaD2_eventually_rescaled_local_cdf_power_bounds
        hbeta_pos hG_lower hG_upper] with
      a ha_pos hlarge hlocal
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with
    y hy_pos hy_window
  have hbounds := hlocal hy_pos hy_window
  simpa [boundedLemmaD2RescaledKernel] using
    boundedLemmaD2_binomial_kernel_norm_le_power_exp_of_rescaled_bounds
      (beta := beta) (A := A) (B := B) (y := y)
      (g := G (y * boundedTailScale beta a)) (j := j) (a := a)
      hA_pos hB_nonneg hy_pos ha_pos hlarge
      (hG_nonneg (y * boundedTailScale beta a))
      (hG_le_one (y * boundedTailScale beta a))
      hbounds.1 hbounds.2

/--
Indicator form of the local envelope bound, ready for dominated convergence on
the growing near-zero interval.
-/
theorem boundedLemmaD2RescaledKernel_eventually_indicator_norm_le_localEnvelope
    {G : ℝ → ℝ} {beta A B delta : ℝ} (j : ℕ)
    (hbeta_pos : 0 < beta)
    (hA_pos : 0 < A) (hB_nonneg : 0 ≤ B)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_lower :
      ∀ x : ℝ, 0 < x → x < delta → A * x ^ beta ≤ G x)
    (hG_upper :
      ∀ x : ℝ, 0 < x → x < delta → G x ≤ B * x ^ beta) :
    ∀ᶠ a in atTop,
      ∀ᵐ y ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
        ‖(Set.Iio (delta / boundedTailScale beta a)).indicator
            (fun z : ℝ => boundedLemmaD2RescaledKernel G beta j a z) y‖ ≤
          boundedLemmaD2LocalEnvelope beta A B j y := by
  filter_upwards
    [boundedLemmaD2RescaledKernel_eventually_norm_le_power_exp_on_growing
      j hbeta_pos hA_pos hB_nonneg hG_nonneg hG_le_one hG_lower hG_upper]
    with a hbound
  filter_upwards
    [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi, hbound] with
      y hy_pos hbound_y
  by_cases hy : y < delta / boundedTailScale beta a
  · have hmem : y ∈ Set.Iio (delta / boundedTailScale beta a) := hy
    simpa [Set.indicator_of_mem hmem, boundedLemmaD2LocalEnvelope,
      mul_assoc] using hbound_y hy
  · have hmem : y ∉ Set.Iio (delta / boundedTailScale beta a) := hy
    rw [Set.indicator_of_notMem hmem]
    simpa using
      boundedLemmaD2LocalEnvelope_nonneg
        (beta := beta) (A := A) (B := B) (j := j)
        hB_nonneg hy_pos.le

theorem boundedLemmaD2LimitKernel_eq_poisson_form
    {beta c y : ℝ} (hy_pos : 0 < y) (j : ℕ) :
    boundedLemmaD2LimitKernel beta c j y =
      Real.exp (-((c / beta) * y ^ beta)) *
        (((c / beta) * y ^ beta) ^ j) / j.factorial := by
  have hy_nonneg : 0 ≤ y := le_of_lt hy_pos
  have hy_pow :
      (y ^ beta) ^ j = y ^ (beta * (j : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy_nonneg]
  rw [boundedLemmaD2LimitKernel]
  rw [mul_pow, hy_pow]
  ring_nf

namespace BoundedTailCDFPowerSandwich

/--
Pointwise convergence of the rescaled finite-`a` Lemma D.2 kernel to the
limiting gamma-kernel integrand.
-/
theorem rescaled_kernel_tendsto_limit
    {G : ℝ → ℝ} {beta c : ℝ}
    (C : BoundedTailCDFPowerSandwich G beta c)
    {y : ℝ} (hy_pos : 0 < y) (j : ℕ) :
    Tendsto
      (fun a : ℕ => boundedLemmaD2RescaledKernel G beta j a y)
      atTop (nhds (boundedLemmaD2LimitKernel beta c j y)) := by
  have h :=
    C.rescaled_cdf_binomial_kernel_tendsto (y := y) hy_pos j
  simpa [boundedLemmaD2RescaledKernel,
    boundedLemmaD2LimitKernel_eq_poisson_form hy_pos j] using h

end BoundedTailCDFPowerSandwich

/-- Measurability of the rescaled finite-`a` Lemma D.2 kernel. -/
theorem boundedLemmaD2RescaledKernel_aestronglyMeasurable
    {G : ℝ → ℝ} (hG : Measurable G) (beta : ℝ) (j a : ℕ) :
    MeasureTheory.AEStronglyMeasurable
      (fun y : ℝ => boundedLemmaD2RescaledKernel G beta j a y)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  have harg :
      Measurable (fun y : ℝ => y * boundedTailScale beta a) :=
    measurable_id.mul measurable_const
  have hGcomp :
      Measurable (fun y : ℝ => G (y * boundedTailScale beta a)) :=
    hG.comp harg
  have hkernel :
      Measurable
        (fun y : ℝ => boundedLemmaD2RescaledKernel G beta j a y) := by
    unfold boundedLemmaD2RescaledKernel
    exact
      (measurable_const.mul (hGcomp.pow_const j)).mul
        ((measurable_const.sub hGcomp).pow_const (a - j))
  exact hkernel.aestronglyMeasurable

/-- The Lemma D.2 limiting coefficient for one fixed inner index `j`. -/
noncomputable def boundedLemmaD2LimitCoeff
    (beta c : ℝ) (j : ℕ) : ℝ := ∫ y in Set.Ioi (0 : ℝ), boundedLemmaD2LimitKernel beta c j y

/--
Gamma-integral evaluation of the fixed-`j` Lemma D.2 limiting coefficient.
-/
theorem boundedLemmaD2LimitCoeff_eq_gamma
    {beta c : ℝ} (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (j : ℕ) :
    boundedLemmaD2LimitCoeff beta c j =
      ((c / beta) ^ j / (j.factorial : ℝ)) *
        ((c / beta) ^ (-(beta * (j : ℝ) + 1) / beta) *
          (1 / beta) *
          Real.Gamma ((beta * (j : ℝ) + 1) / beta)) := by
  have hb_pos : 0 < c / beta := div_pos hc_pos hbeta_pos
  have hq : -1 < beta * (j : ℝ) := by
    have hj_nonneg : 0 ≤ (j : ℝ) := by positivity
    have hmul_nonneg : 0 ≤ beta * (j : ℝ) :=
      mul_nonneg hbeta_pos.le hj_nonneg
    linarith
  rw [boundedLemmaD2LimitCoeff]
  change
    (∫ y in Set.Ioi (0 : ℝ),
      ((c / beta) ^ j / (j.factorial : ℝ)) *
        (y ^ (beta * (j : ℝ)) *
          Real.exp (-(c / beta) * y ^ beta))) =
      ((c / beta) ^ j / (j.factorial : ℝ)) *
        ((c / beta) ^ (-(beta * (j : ℝ) + 1) / beta) *
          (1 / beta) *
          Real.Gamma ((beta * (j : ℝ) + 1) / beta))
  rw [MeasureTheory.integral_const_mul]
  rw [integral_rpow_mul_exp_neg_mul_rpow hbeta_pos hq hb_pos]

/-- Simplified Gamma form of the fixed-`j` Lemma D.2 coefficient. -/
theorem boundedLemmaD2LimitCoeff_eq_gamma_simple
    {beta c : ℝ} (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (j : ℕ) :
    boundedLemmaD2LimitCoeff beta c j =
      (((c / beta) ^ (-(1 / beta)) * (1 / beta) *
        Real.Gamma ((j : ℝ) + 1 / beta)) / (j.factorial : ℝ)) := by
  let lambda : ℝ := c / beta
  have hlambda_pos : 0 < lambda := div_pos hc_pos hbeta_pos
  have hbeta_ne : beta ≠ 0 := ne_of_gt hbeta_pos
  have hfac_ne : (j.factorial : ℝ) ≠ 0 := by positivity
  have harg :
      (beta * (j : ℝ) + 1) / beta = (j : ℝ) + 1 / beta := by
    field_simp [hbeta_ne]
  have hpow :
      lambda ^ j *
          lambda ^ (-(beta * (j : ℝ) + 1) / beta) =
        lambda ^ (-(1 / beta)) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_add hlambda_pos]
    congr 1
    field_simp [hbeta_ne]
    ring
  rw [boundedLemmaD2LimitCoeff_eq_gamma hbeta_pos hc_pos j]
  dsimp [lambda] at hpow
  rw [harg]
  field_simp [hfac_ne]
  have hexp :
      (-(beta * (j : ℝ) + 1) / beta) =
        -((beta * (j : ℝ) + 1) / beta) := by
    ring
  rw [hexp] at hpow
  rw [hpow]

/--
For the uniform reflected-CDF normalization `β = c = 1`, each fixed inner
Lemma D.2 coefficient is one.
-/
theorem boundedLemmaD2LimitCoeff_one_one (j : ℕ) :
    boundedLemmaD2LimitCoeff 1 1 j = 1 := by
  rw [boundedLemmaD2LimitCoeff_eq_gamma (by norm_num) (by norm_num)]
  have hfac : (j.factorial : ℝ) ≠ 0 := by positivity
  norm_num
  rw [Real.Gamma_nat_eq_factorial]
  field_simp [hfac]

/-- The fixed-`j` Lemma D.2 limiting coefficient is positive. -/
theorem boundedLemmaD2LimitCoeff_pos
    {beta c : ℝ} (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (j : ℕ) :
    0 < boundedLemmaD2LimitCoeff beta c j := by
  have hb_pos : 0 < c / beta := div_pos hc_pos hbeta_pos
  have hfactorial_pos : 0 < (j.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos j
  have harg_pos : 0 < (beta * (j : ℝ) + 1) / beta := by
    have hj_nonneg : 0 ≤ (j : ℝ) := by positivity
    have hmul_nonneg : 0 ≤ beta * (j : ℝ) :=
      mul_nonneg hbeta_pos.le hj_nonneg
    exact div_pos (by linarith) hbeta_pos
  rw [boundedLemmaD2LimitCoeff_eq_gamma hbeta_pos hc_pos j]
  exact mul_pos
    (div_pos (pow_pos hb_pos j) hfactorial_pos)
    (mul_pos
      (mul_pos
        (Real.rpow_pos_of_pos hb_pos
          (-(beta * (j : ℝ) + 1) / beta))
        (one_div_pos.mpr hbeta_pos))
      (Real.Gamma_pos_of_pos harg_pos))

theorem boundedLemmaD2LimitCoeff_sum_pos
    {beta c : ℝ} {k : ℕ}
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c) (k_pos : 0 < k) :
    0 < ∑ p : BoundedLemmaD2Index k,
      boundedLemmaD2LimitCoeff beta c p.2.val := by
  haveI : Nonempty (BoundedLemmaD2Index k) :=
    ⟨⟨⟨0, k_pos⟩, ⟨0, by simp⟩⟩⟩
  exact Finset.sum_pos
    (fun p _ => boundedLemmaD2LimitCoeff_pos hbeta_pos hc_pos p.2.val)
    Finset.univ_nonempty

/-- Finite-`a` source integrand in Lemma D.2. -/
noncomputable def boundedLemmaD2IntegralKernel
    (G : ℝ → ℝ) (j a : ℕ) (x : ℝ) : ℝ := (Nat.choose a j : ℝ) * (G x) ^ j * (1 - G x) ^ (a - j)

/--
Normalized fixed-rank finite-difference kernel for the bounded Lemma D.2
integral term, using the `a`-scale substitution `x = y*a^(-1/beta)` for both
adjacent source kernels.
-/
noncomputable def boundedLemmaD2ForwardDifferenceRescaledKernel
    (G : ℝ → ℝ) (beta : ℝ) (j a : ℕ) (y : ℝ) : ℝ :=
  (((a + 1 : ℕ) : ℝ)) *
    (boundedLemmaD2IntegralKernel G j a
        (y * boundedTailScale beta a) -
      boundedLemmaD2IntegralKernel G j (a + 1)
        (y * boundedTailScale beta a))

/--
The scalar factor left after factoring the normalized finite difference
through the ordinary rescaled Lemma D.2 kernel.
-/
noncomputable def boundedLemmaD2ForwardDifferenceFactor
    (G : ℝ → ℝ) (beta : ℝ) (j a : ℕ) (y : ℝ) : ℝ :=
  (((a + 1 : ℕ) : ℝ) / (((a + 1 - j : ℕ) : ℝ))) *
    ((((a + 1 : ℕ) : ℝ) *
        G (y * boundedTailScale beta a)) - (j : ℝ))

/-- Limiting kernel for the normalized fixed-rank finite difference. -/
noncomputable def boundedLemmaD2ForwardDifferenceLimitKernel
    (beta c : ℝ) (j : ℕ) (y : ℝ) : ℝ :=
  (((c / beta) * y ^ beta) - (j : ℝ)) *
    boundedLemmaD2LimitKernel beta c j y

/--
The finite-difference limiting kernel is the linear combination of adjacent
Lemma D.2 limiting kernels induced by the Poisson recurrence.
-/
theorem boundedLemmaD2ForwardDifferenceLimitKernel_eq_succ_sub
    {beta c y : ℝ} (hy_pos : 0 < y) (j : ℕ) :
    boundedLemmaD2ForwardDifferenceLimitKernel beta c j y =
      (((j + 1 : ℕ) : ℝ) *
          boundedLemmaD2LimitKernel beta c (j + 1) y) -
        (j : ℝ) * boundedLemmaD2LimitKernel beta c j y := by
  have hfac_succ :
      (((j + 1).factorial : ℕ) : ℝ) =
        (((j + 1 : ℕ) : ℝ)) * (j.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_succ j
  have hfac_ne : (j.factorial : ℝ) ≠ 0 := by positivity
  have hsucc_ne : (((j + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hy_pow :
      y ^ beta * y ^ (beta * (j : ℝ)) =
        y ^ (beta * (((j + 1 : ℕ) : ℝ))) := by
    rw [← Real.rpow_add hy_pos]
    congr 1
    norm_num
    ring
  unfold boundedLemmaD2ForwardDifferenceLimitKernel
    boundedLemmaD2LimitKernel
  rw [hfac_succ, ← hy_pow]
  field_simp [hfac_ne, hsucc_ne]
  ring

/-- Integrability of the fixed-rank Lemma D.2 limiting kernel on `(0,∞)`. -/
theorem boundedLemmaD2LimitKernel_integrable
    {beta c : ℝ} (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (j : ℕ) :
    MeasureTheory.Integrable
      (boundedLemmaD2LimitKernel beta c j)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hb_pos : 0 < c / beta := div_pos hc_pos hbeta_pos
  have hq : -1 < beta * (j : ℝ) := by
    have hj_nonneg : 0 ≤ (j : ℝ) := by positivity
    have hmul_nonneg : 0 ≤ beta * (j : ℝ) :=
      mul_nonneg hbeta_pos.le hj_nonneg
    linarith
  have hbase :
      MeasureTheory.Integrable
        (fun y : ℝ =>
          y ^ (beta * (j : ℝ)) *
            Real.exp (-(c / beta) * y ^ beta))
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    simpa using
      (integrableOn_rpow_mul_exp_neg_mul_rpow_of_pos
        (p := beta) (q := beta * (j : ℝ)) (b := c / beta)
        hbeta_pos hq hb_pos).integrable
  have hconst :
      MeasureTheory.Integrable
        (fun y : ℝ =>
          ((c / beta) ^ j / (j.factorial : ℝ)) *
            (y ^ (beta * (j : ℝ)) *
              Real.exp (-(c / beta) * y ^ beta)))
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    hbase.const_mul ((c / beta) ^ j / (j.factorial : ℝ))
  refine hconst.congr (Filter.Eventually.of_forall ?_)
  intro y
  unfold boundedLemmaD2LimitKernel
  rfl

/-- Limiting coefficient for the normalized fixed-rank finite difference. -/
noncomputable def boundedLemmaD2ForwardDifferenceLimitCoeff
    (beta c : ℝ) (j : ℕ) : ℝ :=
  ∫ y in Set.Ioi (0 : ℝ),
    boundedLemmaD2ForwardDifferenceLimitKernel beta c j y

/--
Integrated Poisson-recurrence identity for the finite-difference limiting
coefficient.
-/
theorem boundedLemmaD2ForwardDifferenceLimitCoeff_eq_succ_sub
    {beta c : ℝ} (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (j : ℕ) :
    boundedLemmaD2ForwardDifferenceLimitCoeff beta c j =
      (((j + 1 : ℕ) : ℝ) *
          boundedLemmaD2LimitCoeff beta c (j + 1)) -
        (j : ℝ) * boundedLemmaD2LimitCoeff beta c j := by
  have hint_j :=
    boundedLemmaD2LimitKernel_integrable hbeta_pos hc_pos j
  have hint_succ :=
    boundedLemmaD2LimitKernel_integrable hbeta_pos hc_pos (j + 1)
  rw [boundedLemmaD2ForwardDifferenceLimitCoeff, boundedLemmaD2LimitCoeff]
  calc
    (∫ y in Set.Ioi (0 : ℝ),
        boundedLemmaD2ForwardDifferenceLimitKernel beta c j y)
        =
      ∫ y in Set.Ioi (0 : ℝ),
        ((((j + 1 : ℕ) : ℝ) *
            boundedLemmaD2LimitKernel beta c (j + 1) y) -
          (j : ℝ) * boundedLemmaD2LimitKernel beta c j y) := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
          intro y hy
          exact boundedLemmaD2ForwardDifferenceLimitKernel_eq_succ_sub hy j
    _ =
      (((j + 1 : ℕ) : ℝ) *
          (∫ y in Set.Ioi (0 : ℝ),
            boundedLemmaD2LimitKernel beta c (j + 1) y)) -
        (j : ℝ) *
          (∫ y in Set.Ioi (0 : ℝ),
            boundedLemmaD2LimitKernel beta c j y) := by
          rw [MeasureTheory.integral_sub
            (hint_succ.const_mul (((j + 1 : ℕ) : ℝ)))
            (hint_j.const_mul (j : ℝ))]
          rw [MeasureTheory.integral_const_mul,
            MeasureTheory.integral_const_mul]

/--
Closed form of the finite-difference limiting coefficient. This is the
coefficient identity needed to convert the normalized adjacent-drop integral
back to the paper's bounded marginal scale.
-/
theorem boundedLemmaD2ForwardDifferenceLimitCoeff_eq_div
    {beta c : ℝ} (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (j : ℕ) :
    boundedLemmaD2ForwardDifferenceLimitCoeff beta c j =
      boundedLemmaD2LimitCoeff beta c j / beta := by
  have hbase :=
    boundedLemmaD2ForwardDifferenceLimitCoeff_eq_succ_sub
      hbeta_pos hc_pos j
  rw [hbase]
  have hbeta_ne : beta ≠ 0 := hbeta_pos.ne'
  have hb_pos : 0 < c / beta := div_pos hc_pos hbeta_pos
  have hb_ne : c / beta ≠ 0 := hb_pos.ne'
  have hfac_j_ne : (j.factorial : ℝ) ≠ 0 := by positivity
  have harg_j :
      (beta * (j : ℝ) + 1) / beta = (j : ℝ) + 1 / beta := by
    field_simp [hbeta_ne]
  have harg_succ :
      (beta * (((j + 1 : ℕ) : ℝ)) + 1) / beta =
        (j : ℝ) + 1 / beta + 1 := by
    rw [Nat.cast_add, Nat.cast_one]
    field_simp [hbeta_ne]
    ring
  have hgamma_succ :
      Real.Gamma ((beta * (((j + 1 : ℕ) : ℝ)) + 1) / beta) =
        ((j : ℝ) + 1 / beta) *
          Real.Gamma ((beta * (j : ℝ) + 1) / beta) := by
    rw [harg_succ, harg_j]
    exact Real.Gamma_add_one (by positivity)
  have hrpow_succ :
      (c / beta) ^ (-(beta * ((j : ℝ) + 1) + 1) / beta) =
        (c / beta) ^ (-(beta * (j : ℝ) + 1) / beta) / (c / beta) := by
    have hexp :
        (-(beta * ((j : ℝ) + 1) + 1) / beta) =
          (-(beta * (j : ℝ) + 1) / beta) - 1 := by
      field_simp [hbeta_ne]
      ring
    rw [hexp, Real.rpow_sub hb_pos, Real.rpow_one]
  rw [boundedLemmaD2LimitCoeff_eq_gamma hbeta_pos hc_pos (j + 1),
    boundedLemmaD2LimitCoeff_eq_gamma hbeta_pos hc_pos j]
  rw [hgamma_succ]
  rw [show (((j + 1).factorial : ℕ) : ℝ) =
      (((j + 1 : ℕ) : ℝ)) * (j.factorial : ℝ) by
    exact_mod_cast Nat.factorial_succ j]
  rw [show (((j + 1 : ℕ) : ℝ)) = (j : ℝ) + 1 by
    rw [Nat.cast_add, Nat.cast_one]]
  rw [hrpow_succ, pow_succ]
  field_simp [hfac_j_ne, hbeta_ne, hb_ne]
  ring

/--
Algebraic factorization of the normalized finite-difference kernel. This is
the local fixed-rank identity used before the dominated-convergence step.
-/
theorem boundedLemmaD2ForwardDifferenceRescaledKernel_eq_rescaledKernel_mul_factor
    (G : ℝ → ℝ) (beta : ℝ) (j a : ℕ) (y : ℝ)
    (hja : j ≤ a) :
    boundedLemmaD2ForwardDifferenceRescaledKernel G beta j a y =
      boundedLemmaD2RescaledKernel G beta j a y *
        boundedLemmaD2ForwardDifferenceFactor G beta j a y := by
  have hden_ne : (((a + 1 - j : ℕ) : ℝ)) ≠ 0 := by
    have hpos : 0 < a + 1 - j := by omega
    exact_mod_cast (ne_of_gt hpos)
  have hchoose :
      ((Nat.choose (a + 1) j : ℕ) : ℝ) =
        ((Nat.choose a j : ℕ) : ℝ) * (((a + 1 : ℕ) : ℝ)) /
          (((a + 1 - j : ℕ) : ℝ)) := by
    have hnat := Nat.choose_mul_succ_eq a j
    have hnat_cast :
        ((Nat.choose a j : ℕ) : ℝ) * (((a + 1 : ℕ) : ℝ)) =
          ((Nat.choose (a + 1) j : ℕ) : ℝ) *
            (((a + 1 - j : ℕ) : ℝ)) := by
      exact_mod_cast hnat
    rw [eq_div_iff hden_ne]
    exact hnat_cast.symm
  have hsub_succ : a + 1 - j = (a - j) + 1 := by omega
  unfold boundedLemmaD2ForwardDifferenceRescaledKernel
    boundedLemmaD2RescaledKernel boundedLemmaD2ForwardDifferenceFactor
    boundedLemmaD2IntegralKernel
  rw [hchoose, hsub_succ, pow_succ]
  field_simp [hden_ne]
  have hcast_sub_succ :
      ((a - j + 1 : ℕ) : ℝ) =
        ((a + 1 : ℕ) : ℝ) - (j : ℝ) := by
    have hnat : a - j + 1 = a + 1 - j := by omega
    rw [hnat]
    rw [Nat.cast_sub (by omega : j ≤ a + 1)]
  rw [hcast_sub_succ]
  ring

/--
Pointwise convergence of the scalar finite-difference factor after the
Lemma D.2 source substitution.
-/
theorem boundedLemmaD2ForwardDifferenceFactor_tendsto
    {G : ℝ → ℝ} {beta c : ℝ}
    (C : BoundedTailCDFPowerSandwich G beta c)
    {y : ℝ} (hy_pos : 0 < y) (j : ℕ) :
    Tendsto
      (fun a : ℕ =>
        boundedLemmaD2ForwardDifferenceFactor G beta j a y)
      atTop
      (nhds (((c / beta) * y ^ beta) - (j : ℝ))) := by
  have hsucc_ratio :
      Tendsto
        (fun a : ℕ => (((a + 1 : ℕ) : ℝ) / (a : ℝ)))
        atTop (nhds 1) := by
    have hbase :=
      tendsto_add_mul_div_add_mul_atTop_nhds
        (𝕜 := ℝ) (1 : ℝ) (0 : ℝ) (1 : ℝ)
        (show (1 : ℝ) ≠ 0 by norm_num)
    simpa [add_comm, add_left_comm, add_assoc] using hbase
  have hsucc_cdf :
      Tendsto
        (fun a : ℕ =>
          (((a + 1 : ℕ) : ℝ) *
            G (y * boundedTailScale beta a)))
        atTop (nhds ((c / beta) * y ^ beta)) := by
    have hprod :=
      hsucc_ratio.mul (C.rescaled_cdf_nat_mul_tendsto hy_pos)
    refine Tendsto.congr' ?_ (by simpa using hprod)
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with a ha
    have ha_ne : (a : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt ha)
    field_simp [ha_ne]
    rw [Nat.cast_add, Nat.cast_one]
    ring_nf
  have hdiff :
      Tendsto
        (fun a : ℕ =>
          (((a + 1 : ℕ) : ℝ) *
            G (y * boundedTailScale beta a)) - (j : ℝ))
        atTop (nhds (((c / beta) * y ^ beta) - (j : ℝ))) :=
    hsucc_cdf.sub tendsto_const_nhds
  have hratio :
      Tendsto
        (fun a : ℕ =>
          (((a + 1 : ℕ) : ℝ) / (((a + 1 - j : ℕ) : ℝ))))
        atTop (nhds 1) := by
    have hbase :=
      tendsto_add_mul_div_add_mul_atTop_nhds
        (𝕜 := ℝ) (1 : ℝ) (1 - (j : ℝ)) (1 : ℝ)
        (show (1 : ℝ) ≠ 0 by norm_num)
    refine Tendsto.congr' ?_ (by simpa using hbase)
    filter_upwards [eventually_ge_atTop j] with a ha
    have hden_cast :
        (((a + 1 - j : ℕ) : ℝ)) = ((a + 1 : ℕ) : ℝ) - (j : ℝ) := by
      exact_mod_cast Nat.cast_sub (by omega : j ≤ a + 1)
    rw [hden_cast]
    norm_num [Nat.cast_add, Nat.cast_one]
    ring_nf
  have hprod := hratio.mul hdiff
  simpa [boundedLemmaD2ForwardDifferenceFactor] using hprod

/--
Pointwise convergence of the normalized rescaled finite-difference kernel.
-/
theorem boundedLemmaD2ForwardDifferenceRescaledKernel_tendsto_limit
    {G : ℝ → ℝ} {beta c : ℝ}
    (C : BoundedTailCDFPowerSandwich G beta c)
    {y : ℝ} (hy_pos : 0 < y) (j : ℕ) :
    Tendsto
      (fun a : ℕ =>
        boundedLemmaD2ForwardDifferenceRescaledKernel G beta j a y)
      atTop
      (nhds (boundedLemmaD2ForwardDifferenceLimitKernel beta c j y)) := by
  have hkernel := C.rescaled_kernel_tendsto_limit hy_pos j
  have hfactor := boundedLemmaD2ForwardDifferenceFactor_tendsto C hy_pos j
  have hprod := hkernel.mul hfactor
  refine Tendsto.congr' ?_
    (by
      simpa [boundedLemmaD2ForwardDifferenceLimitKernel, mul_comm, mul_left_comm,
        mul_assoc] using hprod)
  filter_upwards [eventually_ge_atTop j] with a hja
  rw [boundedLemmaD2ForwardDifferenceRescaledKernel_eq_rescaledKernel_mul_factor
    G beta j a y hja]
  rw [mul_comm]

/--
On the growing near-zero window, the scalar finite-difference factor is
eventually bounded by a polynomial factor independent of `a`.
-/
theorem boundedLemmaD2ForwardDifferenceFactor_eventually_norm_le_on_growing
    {G : ℝ → ℝ} {beta B delta : ℝ} (j : ℕ)
    (hbeta_pos : 0 < beta) (hB_nonneg : 0 ≤ B)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_upper :
      ∀ x : ℝ, 0 < x → x < delta → G x ≤ B * x ^ beta) :
    ∀ᶠ a in atTop,
      ∀ᵐ y ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
        y < delta / boundedTailScale beta a →
          ‖boundedLemmaD2ForwardDifferenceFactor G beta j a y‖ ≤
            2 * ((j : ℝ) + 2 * B * y ^ beta) := by
  filter_upwards
    [eventually_gt_atTop (0 : ℕ),
      eventually_ge_atTop (2 * j),
      boundedTailScale_eventually_pos beta] with
      a ha_pos_nat hlarge hscale_pos
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with
    y hy_pos hy_window
  have ha_pos : 0 < (a : ℝ) := by exact_mod_cast ha_pos_nat
  have ha_ne : (a : ℝ) ≠ 0 := ne_of_gt ha_pos
  have hx_pos : 0 < y * boundedTailScale beta a :=
    mul_pos hy_pos hscale_pos
  have hx_lt_delta : y * boundedTailScale beta a < delta :=
    (lt_div_iff₀ hscale_pos).mp hy_window
  have hpow :
      (y * boundedTailScale beta a) ^ beta =
        y ^ beta * (a : ℝ) ^ (-1 : ℝ) :=
    boundedTailScale_rescaled_rpow_beta hbeta_pos hy_pos ha_pos_nat
  have hg_upper :
      G (y * boundedTailScale beta a) ≤
        B * (y ^ beta * (a : ℝ) ^ (-1 : ℝ)) := by
    simpa [hpow] using
      hG_upper (y * boundedTailScale beta a) hx_pos hx_lt_delta
  have hg_nonneg : 0 ≤ G (y * boundedTailScale beta a) :=
    hG_nonneg (y * boundedTailScale beta a)
  have hybeta_nonneg : 0 ≤ y ^ beta :=
    le_of_lt (Real.rpow_pos_of_pos hy_pos beta)
  have hBy_nonneg : 0 ≤ B * y ^ beta :=
    mul_nonneg hB_nonneg hybeta_nonneg
  have hsucc_div_le_two :
      (((a + 1 : ℕ) : ℝ) / (a : ℝ)) ≤ 2 := by
    rw [div_le_iff₀ ha_pos]
    rw [Nat.cast_add, Nat.cast_one]
    have ha_ge_one : (1 : ℝ) ≤ (a : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt ha_pos_nat
    nlinarith
  have hg_scaled_le :
      (((a + 1 : ℕ) : ℝ) *
          G (y * boundedTailScale beta a)) ≤
        2 * B * y ^ beta := by
    calc
      (((a + 1 : ℕ) : ℝ) *
          G (y * boundedTailScale beta a))
          ≤ ((a + 1 : ℕ) : ℝ) *
              (B * (y ^ beta * (a : ℝ) ^ (-1 : ℝ))) :=
            mul_le_mul_of_nonneg_left hg_upper (by positivity)
      _ = (((a + 1 : ℕ) : ℝ) / (a : ℝ)) * (B * y ^ beta) := by
            rw [Real.rpow_neg_one]
            field_simp [ha_ne]
      _ ≤ 2 * (B * y ^ beta) :=
            mul_le_mul_of_nonneg_right hsucc_div_le_two hBy_nonneg
      _ = 2 * B * y ^ beta := by ring
  have hscaled_nonneg :
      0 ≤ (((a + 1 : ℕ) : ℝ) *
          G (y * boundedTailScale beta a)) :=
    mul_nonneg (by positivity) hg_nonneg
  have hdiff_abs :
      ‖(((a + 1 : ℕ) : ℝ) *
          G (y * boundedTailScale beta a) - (j : ℝ))‖ ≤
        (j : ℝ) + 2 * B * y ^ beta := by
    rw [Real.norm_eq_abs, abs_sub_le_iff]
    constructor <;>
      nlinarith [hscaled_nonneg, hg_scaled_le,
        (show 0 ≤ (j : ℝ) by positivity)]
  have hden_pos :
      0 < (((a + 1 - j : ℕ) : ℝ)) := by
    have hnat : 0 < a + 1 - j := by omega
    exact_mod_cast hnat
  have hratio_nonneg :
      0 ≤ (((a + 1 : ℕ) : ℝ) /
          (((a + 1 - j : ℕ) : ℝ))) :=
    div_nonneg (by positivity) hden_pos.le
  have hratio_le_two :
      (((a + 1 : ℕ) : ℝ) /
          (((a + 1 - j : ℕ) : ℝ))) ≤ 2 := by
    rw [div_le_iff₀ hden_pos]
    have hden_cast :
        (((a + 1 - j : ℕ) : ℝ)) =
          ((a + 1 : ℕ) : ℝ) - (j : ℝ) := by
      exact_mod_cast Nat.cast_sub (by omega : j ≤ a + 1)
    rw [hden_cast]
    rw [Nat.cast_add, Nat.cast_one]
    have hlarge_real : 2 * (j : ℝ) ≤ (a : ℝ) := by
      exact_mod_cast hlarge
    nlinarith
  let r : ℝ :=
    (((a + 1 : ℕ) : ℝ) / (((a + 1 - j : ℕ) : ℝ)))
  let d : ℝ :=
    (((a + 1 : ℕ) : ℝ) *
      G (y * boundedTailScale beta a) - (j : ℝ))
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    exact hratio_nonneg
  have hr_le_two : r ≤ 2 := by
    dsimp [r]
    exact hratio_le_two
  have hd_abs : ‖d‖ ≤ (j : ℝ) + 2 * B * y ^ beta := by
    dsimp [d]
    exact hdiff_abs
  rw [boundedLemmaD2ForwardDifferenceFactor]
  change ‖r * d‖ ≤ 2 * ((j : ℝ) + 2 * B * y ^ beta)
  calc
    ‖r * d‖ = ‖r‖ * ‖d‖ := by rw [norm_mul]
    _ = r * ‖d‖ := by rw [Real.norm_of_nonneg hr_nonneg]
    _ ≤ 2 * ((j : ℝ) + 2 * B * y ^ beta) :=
            mul_le_mul hr_le_two hd_abs (norm_nonneg _) (by norm_num)

/--
Indicator form of the finite-difference local envelope bound, ready for the
dominated-convergence step on the growing near-zero interval.
-/
theorem boundedLemmaD2ForwardDifferenceRescaledKernel_eventually_indicator_norm_le_localEnvelope
    {G : ℝ → ℝ} {beta A B delta : ℝ} (j : ℕ)
    (hbeta_pos : 0 < beta)
    (hA_pos : 0 < A) (hB_nonneg : 0 ≤ B)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_lower :
      ∀ x : ℝ, 0 < x → x < delta → A * x ^ beta ≤ G x)
    (hG_upper :
      ∀ x : ℝ, 0 < x → x < delta → G x ≤ B * x ^ beta) :
    ∀ᶠ a in atTop,
      ∀ᵐ y ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
        ‖(Set.Iio (delta / boundedTailScale beta a)).indicator
            (fun z : ℝ =>
              boundedLemmaD2ForwardDifferenceRescaledKernel G beta j a z)
            y‖ ≤
          boundedLemmaD2ForwardDifferenceLocalEnvelope beta A B j y := by
  filter_upwards
    [boundedLemmaD2RescaledKernel_eventually_norm_le_power_exp_on_growing
      j hbeta_pos hA_pos hB_nonneg hG_nonneg hG_le_one hG_lower hG_upper,
      boundedLemmaD2ForwardDifferenceFactor_eventually_norm_le_on_growing
        j hbeta_pos hB_nonneg hG_nonneg hG_upper,
      eventually_ge_atTop j] with a hkernel hfactor hja
  filter_upwards
    [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi,
      hkernel, hfactor] with y hy_pos hkernel_y hfactor_y
  by_cases hy : y < delta / boundedTailScale beta a
  · have hmem : y ∈ Set.Iio (delta / boundedTailScale beta a) := hy
    have hkernel_local :
        ‖boundedLemmaD2RescaledKernel G beta j a y‖ ≤
          boundedLemmaD2LocalEnvelope beta A B j y := by
      simpa [boundedLemmaD2LocalEnvelope, mul_assoc] using hkernel_y hy
    have hfactor_bound :
        ‖boundedLemmaD2ForwardDifferenceFactor G beta j a y‖ ≤
          2 * ((j : ℝ) + 2 * B * y ^ beta) :=
      hfactor_y hy
    have hfactor_nonneg :
        0 ≤ 2 * ((j : ℝ) + 2 * B * y ^ beta) := by
      have hybeta_nonneg : 0 ≤ y ^ beta :=
        le_of_lt (Real.rpow_pos_of_pos hy_pos beta)
      have hj_nonneg : 0 ≤ (j : ℝ) := by positivity
      positivity
    have hlocal_nonneg :
        0 ≤ boundedLemmaD2LocalEnvelope beta A B j y :=
      boundedLemmaD2LocalEnvelope_nonneg hB_nonneg hy_pos.le
    rw [Set.indicator_of_mem hmem]
    rw [boundedLemmaD2ForwardDifferenceRescaledKernel_eq_rescaledKernel_mul_factor
      G beta j a y hja]
    calc
      ‖boundedLemmaD2RescaledKernel G beta j a y *
          boundedLemmaD2ForwardDifferenceFactor G beta j a y‖
          = ‖boundedLemmaD2RescaledKernel G beta j a y‖ *
              ‖boundedLemmaD2ForwardDifferenceFactor G beta j a y‖ := by
              rw [norm_mul]
      _ ≤ boundedLemmaD2LocalEnvelope beta A B j y *
            (2 * ((j : ℝ) + 2 * B * y ^ beta)) :=
              mul_le_mul hkernel_local hfactor_bound
                (norm_nonneg _) hlocal_nonneg
      _ = boundedLemmaD2ForwardDifferenceLocalEnvelope beta A B j y := by
              unfold boundedLemmaD2ForwardDifferenceLocalEnvelope
              ring
  · have hmem : y ∉ Set.Iio (delta / boundedTailScale beta a) := hy
    rw [Set.indicator_of_notMem hmem]
    simpa using
      boundedLemmaD2ForwardDifferenceLocalEnvelope_nonneg
        (beta := beta) (A := A) (B := B) (j := j)
        hB_nonneg hy_pos.le

/-- Measurability of the finite-`a` source integrand in Lemma D.2. -/
theorem boundedLemmaD2IntegralKernel_measurable
    {G : ℝ → ℝ} (hG : Measurable G) (j a : ℕ) :
    Measurable (fun x : ℝ => boundedLemmaD2IntegralKernel G j a x) := by
  unfold boundedLemmaD2IntegralKernel
  exact
    (measurable_const.mul (hG.pow_const j)).mul
      ((measurable_const.sub hG).pow_const (a - j))

/-- Measurability of the normalized finite-difference rescaled kernel. -/
theorem boundedLemmaD2ForwardDifferenceRescaledKernel_aestronglyMeasurable
    {G : ℝ → ℝ} (hG : Measurable G) (beta : ℝ) (j a : ℕ) :
    MeasureTheory.AEStronglyMeasurable
      (fun y : ℝ =>
        boundedLemmaD2ForwardDifferenceRescaledKernel G beta j a y)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  have harg :
      Measurable (fun y : ℝ => y * boundedTailScale beta a) :=
    measurable_id.mul measurable_const
  have hkernel_a :
      Measurable
        (fun y : ℝ =>
          boundedLemmaD2IntegralKernel G j a
            (y * boundedTailScale beta a)) :=
    (boundedLemmaD2IntegralKernel_measurable hG j a).comp harg
  have hkernel_succ :
      Measurable
        (fun y : ℝ =>
          boundedLemmaD2IntegralKernel G j (a + 1)
            (y * boundedTailScale beta a)) :=
    (boundedLemmaD2IntegralKernel_measurable hG j (a + 1)).comp harg
  have hmeas :
      Measurable
        (fun y : ℝ =>
          boundedLemmaD2ForwardDifferenceRescaledKernel G beta j a y) := by
    unfold boundedLemmaD2ForwardDifferenceRescaledKernel
    exact measurable_const.mul (hkernel_a.sub hkernel_succ)
  exact hmeas.aestronglyMeasurable

/--
If `G` is CDF-valued, the source Lemma D.2 kernel is bounded by the binomial
coefficient.
-/
theorem boundedLemmaD2IntegralKernel_norm_le_choose_of_cdf_range
    {G : ℝ → ℝ} (j a : ℕ) {x : ℝ}
    (hG_nonneg : 0 ≤ G x) (hG_le_one : G x ≤ 1) :
    ‖boundedLemmaD2IntegralKernel G j a x‖ ≤ (Nat.choose a j : ℝ) := by
  have hchoose_nonneg : 0 ≤ (Nat.choose a j : ℝ) := by positivity
  have htail_nonneg : 0 ≤ 1 - G x := sub_nonneg.mpr hG_le_one
  have htail_le_one : 1 - G x ≤ 1 := by linarith
  have hGpow_nonneg : 0 ≤ (G x) ^ j := pow_nonneg hG_nonneg j
  have hGpow_le_one : (G x) ^ j ≤ 1 :=
    pow_le_one₀ hG_nonneg hG_le_one
  have htailpow_nonneg : 0 ≤ (1 - G x) ^ (a - j) :=
    pow_nonneg htail_nonneg (a - j)
  have htailpow_le_one : (1 - G x) ^ (a - j) ≤ 1 :=
    pow_le_one₀ htail_nonneg htail_le_one
  have hprod_le_one :
      (G x) ^ j * (1 - G x) ^ (a - j) ≤ 1 :=
    mul_le_one₀ hGpow_le_one htailpow_nonneg htailpow_le_one
  have hkernel_nonneg :
      0 ≤ boundedLemmaD2IntegralKernel G j a x := by
    unfold boundedLemmaD2IntegralKernel
    exact mul_nonneg (mul_nonneg hchoose_nonneg hGpow_nonneg)
      htailpow_nonneg
  rw [Real.norm_of_nonneg hkernel_nonneg]
  unfold boundedLemmaD2IntegralKernel
  calc
    (Nat.choose a j : ℝ) * (G x) ^ j *
        (1 - G x) ^ (a - j)
        = (Nat.choose a j : ℝ) *
            ((G x) ^ j * (1 - G x) ^ (a - j)) := by ring
    _ ≤ (Nat.choose a j : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hprod_le_one hchoose_nonneg
    _ = (Nat.choose a j : ℝ) := by ring

/-- The finite-`a` source integrand is nonnegative for CDF-valued `G`. -/
theorem boundedLemmaD2IntegralKernel_nonneg_of_cdf_range
    {G : ℝ → ℝ} (j a : ℕ) {x : ℝ}
    (hG_nonneg : 0 ≤ G x) (hG_le_one : G x ≤ 1) :
    0 ≤ boundedLemmaD2IntegralKernel G j a x := by
  have hchoose_nonneg : 0 ≤ (Nat.choose a j : ℝ) := by positivity
  have htail_nonneg : 0 ≤ 1 - G x := sub_nonneg.mpr hG_le_one
  unfold boundedLemmaD2IntegralKernel
  exact mul_nonneg
    (mul_nonneg hchoose_nonneg (pow_nonneg hG_nonneg j))
    (pow_nonneg htail_nonneg (a - j))

/-- The bounded-support source kernel is zero after the support endpoint. -/
theorem boundedLemmaD2IntegralKernel_eq_zero_of_support
    {G : ℝ → ℝ} {M x : ℝ} {j a : ℕ}
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    (hMx : M ≤ x) (hja : j < a) :
    boundedLemmaD2IntegralKernel G j a x = 0 := by
  have hGx : G x = 1 := hG_eq_one_of_support x hMx
  have hsub_pos : 0 < a - j := Nat.sub_pos_of_lt hja
  simp [boundedLemmaD2IntegralKernel, hGx, ne_of_gt hsub_pos]

/--
Pointwise geometric tail bound for the source kernel once `G x` is bounded
below by `p`.
-/
theorem boundedLemmaD2IntegralKernel_le_geometric_tail_of_cdf_range
    {G : ℝ → ℝ} (j a : ℕ) {x p : ℝ}
    (hp_nonneg : 0 ≤ p) (hp_le_one : p ≤ 1)
    (hG_nonneg : 0 ≤ G x) (hG_le_one : G x ≤ 1)
    (hp_le_G : p ≤ G x) :
    boundedLemmaD2IntegralKernel G j a x ≤
      (Nat.choose a j : ℝ) * (1 - p) ^ (a - j) := by
  have hchoose_nonneg : 0 ≤ (Nat.choose a j : ℝ) := by positivity
  have htail_nonneg : 0 ≤ 1 - G x := sub_nonneg.mpr hG_le_one
  have hp_tail_nonneg : 0 ≤ 1 - p := sub_nonneg.mpr hp_le_one
  have htail_le : 1 - G x ≤ 1 - p := by linarith
  have hGpow_nonneg : 0 ≤ (G x) ^ j := pow_nonneg hG_nonneg j
  have hGpow_le_one : (G x) ^ j ≤ 1 :=
    pow_le_one₀ hG_nonneg hG_le_one
  have htailpow_nonneg : 0 ≤ (1 - G x) ^ (a - j) :=
    pow_nonneg htail_nonneg (a - j)
  have htailpow_le : (1 - G x) ^ (a - j) ≤ (1 - p) ^ (a - j) :=
    pow_le_pow_left₀ htail_nonneg htail_le (a - j)
  have hprod_le :
      (G x) ^ j * (1 - G x) ^ (a - j) ≤
        (1 - p) ^ (a - j) := by
    calc
      (G x) ^ j * (1 - G x) ^ (a - j)
          ≤ 1 * (1 - G x) ^ (a - j) :=
            mul_le_mul_of_nonneg_right hGpow_le_one htailpow_nonneg
      _ = (1 - G x) ^ (a - j) := by ring
      _ ≤ (1 - p) ^ (a - j) := htailpow_le
  unfold boundedLemmaD2IntegralKernel
  calc
    (Nat.choose a j : ℝ) * (G x) ^ j * (1 - G x) ^ (a - j)
        = (Nat.choose a j : ℝ) *
            ((G x) ^ j * (1 - G x) ^ (a - j)) := by ring
    _ ≤ (Nat.choose a j : ℝ) * (1 - p) ^ (a - j) :=       mul_le_mul_of_nonneg_left hprod_le hchoose_nonneg

/-- A finite-interval constant envelope is integrable on `(0,∞)`. -/
theorem boundedConstantIndicator_integrable_Ioi (M C : ℝ) :
    MeasureTheory.Integrable
      (fun x : ℝ => if x < M then C else 0)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hindicator :
      (fun x : ℝ => if x < M then C else 0) =
        (Set.Iio M).indicator (fun _x : ℝ => C) := by
    funext x
    by_cases hx : x < M <;> simp [hx]
  rw [hindicator]
  have hfinite :
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) (Set.Iio M) ≠ ⊤ := by
    rw [MeasureTheory.Measure.restrict_apply measurableSet_Iio]
    have hset : Set.Iio M ∩ Set.Ioi (0 : ℝ) = Set.Ioo (0 : ℝ) M := by
      ext x
      simp [and_comm]
    rw [hset, Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  exact
    (MeasureTheory.integrableOn_const
      (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
      (s := Set.Iio M) (C := C) hfinite).integrable_indicator
      measurableSet_Iio

/-- A finite-interval constant envelope is integrable on `(lower,∞)`. -/
theorem boundedConstantIndicator_integrable_Ioi_from
    (lower M C : ℝ) :
    MeasureTheory.Integrable
      (fun x : ℝ => if x < M then C else 0)
      (MeasureTheory.volume.restrict (Set.Ioi lower)) := by
  have hindicator :
      (fun x : ℝ => if x < M then C else 0) =
        (Set.Iio M).indicator (fun _x : ℝ => C) := by
    funext x
    by_cases hx : x < M <;> simp [hx]
  rw [hindicator]
  have hfinite :
      (MeasureTheory.volume.restrict (Set.Ioi lower)) (Set.Iio M) ≠ ⊤ := by
    rw [MeasureTheory.Measure.restrict_apply measurableSet_Iio]
    have hset : Set.Iio M ∩ Set.Ioi lower = Set.Ioo lower M := by
      ext x
      simp [and_comm]
    rw [hset, Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  exact
    (MeasureTheory.integrableOn_const
      (μ := MeasureTheory.volume.restrict (Set.Ioi lower))
      (s := Set.Iio M) (C := C) hfinite).integrable_indicator
      measurableSet_Iio

/-- Integral of a finite-interval constant envelope over a tail interval. -/
theorem boundedConstantIndicator_integral_Ioi_from
    {lower M C : ℝ} (hlowerM : lower ≤ M) :
    ∫ x in Set.Ioi lower, (if x < M then C else 0) =
      C * (M - lower) := by
  have hindicator :
      (fun x : ℝ => if x < M then C else 0) =
        (Set.Iio M).indicator (fun _x : ℝ => C) := by
    funext x
    by_cases hx : x < M <;> simp [hx]
  rw [hindicator, MeasureTheory.setIntegral_indicator measurableSet_Iio]
  have hset : Set.Ioi lower ∩ Set.Iio M = Set.Ioo lower M := by
    ext x
    simp
  rw [hset, MeasureTheory.setIntegral_const]
  simp [Real.volume_real_Ioo_of_le hlowerM, mul_comm]

/--
Bounded-support CDF conditions imply eventual source-kernel integrability for
fixed `j`: once `a > j`, the kernel is zero beyond the support and bounded on
the finite interval below the support.
-/
theorem boundedLemmaD2IntegralKernel_integrableOn_of_bounded_support
    {G : ℝ → ℝ} (hG_measurable : Measurable G)
    (M : ℝ)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    {j a : ℕ} (hja : j < a) :
    MeasureTheory.IntegrableOn
      (boundedLemmaD2IntegralKernel G j a)
      (Set.Ioi (0 : ℝ)) := by
  let envelope : ℝ → ℝ :=
    fun x => if x < M then (Nat.choose a j : ℝ) else 0
  have henv_int :
      MeasureTheory.Integrable envelope
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    boundedConstantIndicator_integrable_Ioi M (Nat.choose a j : ℝ)
  have hkernel_aemeasurable :
      MeasureTheory.AEStronglyMeasurable
        (fun x : ℝ => boundedLemmaD2IntegralKernel G j a x)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
    (boundedLemmaD2IntegralKernel_measurable hG_measurable j a).aestronglyMeasurable
  refine MeasureTheory.Integrable.mono' henv_int hkernel_aemeasurable ?_
  refine Filter.Eventually.of_forall ?_
  intro x
  by_cases hxM : x < M
  · have hbound :=
      boundedLemmaD2IntegralKernel_norm_le_choose_of_cdf_range
        (G := G) j a (hG_nonneg x) (hG_le_one x)
    simpa [envelope, hxM] using hbound
  · have hGx : G x = 1 :=
      hG_eq_one_of_support x (le_of_not_gt hxM)
    have hsub_pos : 0 < a - j := Nat.sub_pos_of_lt hja
    have hkernel_zero :
        boundedLemmaD2IntegralKernel G j a x = 0 := by
      simp [boundedLemmaD2IntegralKernel, hGx, ne_of_gt hsub_pos]
    simp [envelope, hxM, hkernel_zero]

/--
Eventual bounded-support source-kernel integrability for a fixed Lemma D.2
rank `j`.
-/
theorem boundedLemmaD2IntegralKernel_eventually_integrableOn_of_bounded_support
    {G : ℝ → ℝ} (hG_measurable : Measurable G)
    (M : ℝ)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    (j : ℕ) :
    ∀ᶠ a in atTop,
      MeasureTheory.IntegrableOn
        (boundedLemmaD2IntegralKernel G j a)
        (Set.Ioi (0 : ℝ)) := by
  filter_upwards [eventually_gt_atTop j] with a hja
  exact boundedLemmaD2IntegralKernel_integrableOn_of_bounded_support
    hG_measurable M hG_nonneg hG_le_one hG_eq_one_of_support hja

/--
Source Lemma D.2 integral term:

`∫_0^∞ choose(a,j) * G(x)^j * (1 - G(x))^(a-j) dx`.

Here `G` is the reflected CDF `G_X` from the proof of Theorem 1(ii). The hard
analytic proof is to show this is asymptotic to a positive constant times
`a^(-1/β)` for each fixed `j`.
-/
noncomputable def boundedLemmaD2IntegralTerm
    (G : ℝ → ℝ) (j a : ℕ) : ℝ := ∫ x in Set.Ioi (0 : ℝ), boundedLemmaD2IntegralKernel G j a x

/-- The near-zero part of the Lemma D.2 integral, split at `delta`. -/
noncomputable def boundedLemmaD2IntegralTermBelow
    (G : ℝ → ℝ) (j a : ℕ) (delta : ℝ) : ℝ := ∫ x in Set.Ioo (0 : ℝ) delta, boundedLemmaD2IntegralKernel G j a x

/-- The tail part of the Lemma D.2 integral, split at `delta`. -/
noncomputable def boundedLemmaD2IntegralTermAbove
    (G : ℝ → ℝ) (j a : ℕ) (delta : ℝ) : ℝ := ∫ x in Set.Ioi delta, boundedLemmaD2IntegralKernel G j a x

/-- The above-`delta` source integral is nonnegative for CDF-valued `G`. -/
theorem boundedLemmaD2IntegralTermAbove_nonneg_of_cdf_range
    {G : ℝ → ℝ} (j a : ℕ) (delta : ℝ)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1) :
    0 ≤ boundedLemmaD2IntegralTermAbove G j a delta := by
  dsimp [boundedLemmaD2IntegralTermAbove]
  exact MeasureTheory.setIntegral_nonneg measurableSet_Ioi
    (fun x _hx =>
      boundedLemmaD2IntegralKernel_nonneg_of_cdf_range
        (G := G) j a (hG_nonneg x) (hG_le_one x))

/--
Finite-support geometric tail bound for the above-`delta` Lemma D.2 source
integral.
-/
theorem boundedLemmaD2IntegralTermAbove_le_geometric_support_bound
    {G : ℝ → ℝ} (hG_measurable : Measurable G)
    {delta M p : ℝ} (hdelta_nonneg : 0 ≤ delta) (hdeltaM : delta ≤ M)
    (hp_nonneg : 0 ≤ p) (hp_le_one : p ≤ 1)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    (hp_le_G_on_tail : ∀ x : ℝ, delta < x → p ≤ G x)
    {j a : ℕ} (hja : j < a) :
    boundedLemmaD2IntegralTermAbove G j a delta ≤
      ((Nat.choose a j : ℝ) * (1 - p) ^ (a - j)) *
        (M - delta) := by
  let envelope : ℝ → ℝ :=
    fun x => if x < M then
      (Nat.choose a j : ℝ) * (1 - p) ^ (a - j) else 0
  have hleft :
      MeasureTheory.IntegrableOn
        (boundedLemmaD2IntegralKernel G j a)
        (Set.Ioi delta) := by
    have hbase :=
      boundedLemmaD2IntegralKernel_integrableOn_of_bounded_support
        hG_measurable M hG_nonneg hG_le_one hG_eq_one_of_support hja
    exact hbase.mono_set (fun x hx => hdelta_nonneg.trans_lt hx)
  have hright :
      MeasureTheory.IntegrableOn envelope (Set.Ioi delta) :=
    boundedConstantIndicator_integrable_Ioi_from delta M
      ((Nat.choose a j : ℝ) * (1 - p) ^ (a - j))
  have hmono :
      boundedLemmaD2IntegralTermAbove G j a delta ≤
        ∫ x in Set.Ioi delta, envelope x := by
    dsimp [boundedLemmaD2IntegralTermAbove]
    refine MeasureTheory.setIntegral_mono_on hleft hright measurableSet_Ioi ?_
    intro x hx_tail
    by_cases hxM : x < M
    · have hbound :=
        boundedLemmaD2IntegralKernel_le_geometric_tail_of_cdf_range
          (G := G) j a hp_nonneg hp_le_one
          (hG_nonneg x) (hG_le_one x) (hp_le_G_on_tail x hx_tail)
      simpa [envelope, hxM] using hbound
    · have hzero :=
        boundedLemmaD2IntegralKernel_eq_zero_of_support
          (G := G) (M := M) (x := x) (j := j) (a := a)
          hG_eq_one_of_support (le_of_not_gt hxM) hja
      simp [envelope, hxM, hzero]
  have henv_integral :
      ∫ x in Set.Ioi delta, envelope x =
        ((Nat.choose a j : ℝ) * (1 - p) ^ (a - j)) *
          (M - delta) :=
    boundedConstantIndicator_integral_Ioi_from hdeltaM
  exact hmono.trans_eq henv_integral

/--
The binomial/geometric support bound is negligible relative to the bounded
branch scale. This is the scalar tail estimate used after splitting Lemma D.2
at a fixed `delta`.
-/
theorem boundedTailScale_choose_geometric_tail_ratio_tendsto_zero
    {beta p C : ℝ} (hbeta_pos : 0 < beta)
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hC_nonneg : 0 ≤ C) (j : ℕ) :
    Tendsto
      (fun a : ℕ =>
        (((Nat.choose a j : ℝ) * (1 - p) ^ (a - j)) * C) /
          boundedTailScale beta a)
      atTop (nhds 0) := by
  let rho : ℝ := 1 - p
  have hrho_pos : 0 < rho := by
    dsimp [rho]
    linarith
  have hrho_lt_one : rho < 1 := by
    dsimp [rho]
    linarith
  have hupper_tendsto :
      Tendsto
        (fun a : ℕ =>
          ((C * (rho ^ j)⁻¹) * ((a : ℝ) ^ j * rho ^ a)) /
            boundedTailScale beta a)
        atTop (nhds 0) :=
    boundedTailScale_polynomial_geometric_ratio_tendsto_zero
      hbeta_pos hrho_pos hrho_lt_one j (C * (rho ^ j)⁻¹)
  refine squeeze_zero' ?_ ?_ hupper_tendsto
  · filter_upwards [boundedTailScale_eventually_pos beta] with a hscale_pos
    have htail_nonneg : 0 ≤ (1 - p) ^ (a - j) :=
      pow_nonneg (by linarith : 0 ≤ 1 - p) (a - j)
    have hnum_nonneg :
        0 ≤ ((Nat.choose a j : ℝ) * (1 - p) ^ (a - j)) * C :=
      mul_nonneg (mul_nonneg (by positivity) htail_nonneg) hC_nonneg
    exact div_nonneg hnum_nonneg hscale_pos.le
  · filter_upwards
      [eventually_gt_atTop j, boundedTailScale_eventually_pos beta] with
        a hja hscale_pos
    have hle : j ≤ a := le_of_lt hja
    have hchoose_le :
        (Nat.choose a j : ℝ) ≤ (a : ℝ) ^ j := by
      exact_mod_cast Nat.choose_le_pow a j
    have hrho_pow_ne : rho ^ j ≠ 0 := pow_ne_zero j hrho_pos.ne'
    have hpow :
        rho ^ a = rho ^ (a - j) * rho ^ j := by
      rw [← pow_add, Nat.sub_add_cancel hle]
    have hrho_shift :
        rho ^ (a - j) = rho ^ a * (rho ^ j)⁻¹ := by
      calc
        rho ^ (a - j) = rho ^ (a - j) * 1 := by ring
        _ = rho ^ (a - j) * (rho ^ j * (rho ^ j)⁻¹) := by
              rw [mul_inv_cancel₀ hrho_pow_ne]
        _ = (rho ^ (a - j) * rho ^ j) * (rho ^ j)⁻¹ := by ring
        _ = rho ^ a * (rho ^ j)⁻¹ := by rw [← hpow]
    have htail_factor_nonneg :
        0 ≤ rho ^ a * (rho ^ j)⁻¹ :=
      mul_nonneg (pow_nonneg hrho_pos.le a)
        (inv_nonneg.mpr (pow_nonneg hrho_pos.le j))
    have hnum_le :
        ((Nat.choose a j : ℝ) * rho ^ (a - j)) * C ≤
          (((a : ℝ) ^ j * (rho ^ a * (rho ^ j)⁻¹)) * C) := by
      rw [hrho_shift]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hchoose_le htail_factor_nonneg)
        hC_nonneg
    have hdiv_le :
        (((Nat.choose a j : ℝ) * rho ^ (a - j)) * C) /
            boundedTailScale beta a ≤
          (((a : ℝ) ^ j * (rho ^ a * (rho ^ j)⁻¹)) * C) /
            boundedTailScale beta a :=
      div_le_div_of_nonneg_right hnum_le hscale_pos.le
    calc
      (((Nat.choose a j : ℝ) * (1 - p) ^ (a - j)) * C) /
          boundedTailScale beta a
          ≤ (((a : ℝ) ^ j * (rho ^ a * (rho ^ j)⁻¹)) * C) /
              boundedTailScale beta a := by
            simpa [rho] using hdiv_le
      _ = ((C * (rho ^ j)⁻¹) * ((a : ℝ) ^ j * rho ^ a)) /
            boundedTailScale beta a := by ring

/--
The same binomial/geometric support bound is negligible relative to the
bounded marginal scale `a^(-1/beta)/(a+1)`.
-/
theorem boundedPowerMarginalScale_choose_geometric_tail_ratio_tendsto_zero
    {beta p C : ℝ} (hbeta_pos : 0 < beta)
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hC_nonneg : 0 ≤ C) (j : ℕ) :
    Tendsto
      (fun a : ℕ =>
        (((Nat.choose a j : ℝ) * (1 - p) ^ (a - j)) * C) /
          boundedPowerMarginalScale beta a)
      atTop (nhds 0) := by
  let rho : ℝ := 1 - p
  have hrho_pos : 0 < rho := by
    dsimp [rho]
    linarith
  have hrho_lt_one : rho < 1 := by
    dsimp [rho]
    linarith
  have hupper_tendsto :
      Tendsto
        (fun a : ℕ =>
          ((C * (rho ^ j)⁻¹) *
              ((((a + 1 : ℕ) : ℝ) ^ j) * rho ^ a)) /
            boundedPowerMarginalScale beta a)
        atTop (nhds 0) :=
    boundedPowerMarginalScale_succ_polynomial_geometric_ratio_tendsto_zero
      hbeta_pos hrho_pos hrho_lt_one j (C * (rho ^ j)⁻¹)
  refine squeeze_zero' ?_ ?_ hupper_tendsto
  · filter_upwards with a
    have htail_nonneg : 0 ≤ (1 - p) ^ (a - j) :=
      pow_nonneg (by linarith : 0 ≤ 1 - p) (a - j)
    have hnum_nonneg :
        0 ≤ ((Nat.choose a j : ℝ) * (1 - p) ^ (a - j)) * C :=
      mul_nonneg (mul_nonneg (by positivity) htail_nonneg) hC_nonneg
    exact div_nonneg hnum_nonneg
      (boundedPowerMarginalScale_pos beta a).le
  · filter_upwards [eventually_gt_atTop j] with a hja
    have hle : j ≤ a := le_of_lt hja
    have hchoose_le_a :
        (Nat.choose a j : ℝ) ≤ (a : ℝ) ^ j := by
      exact_mod_cast Nat.choose_le_pow a j
    have ha_le_succ : (a : ℝ) ≤ (((a + 1 : ℕ) : ℝ)) := by
      rw [Nat.cast_add, Nat.cast_one]
      linarith
    have hchoose_le_succ :
        (Nat.choose a j : ℝ) ≤ (((a + 1 : ℕ) : ℝ)) ^ j :=
      hchoose_le_a.trans
        (pow_le_pow_left₀ (by positivity) ha_le_succ j)
    have hrho_pow_ne : rho ^ j ≠ 0 := pow_ne_zero j hrho_pos.ne'
    have hpow :
        rho ^ a = rho ^ (a - j) * rho ^ j := by
      rw [← pow_add, Nat.sub_add_cancel hle]
    have hrho_shift :
        rho ^ (a - j) = rho ^ a * (rho ^ j)⁻¹ := by
      calc
        rho ^ (a - j) = rho ^ (a - j) * 1 := by ring
        _ = rho ^ (a - j) * (rho ^ j * (rho ^ j)⁻¹) := by
              rw [mul_inv_cancel₀ hrho_pow_ne]
        _ = (rho ^ (a - j) * rho ^ j) * (rho ^ j)⁻¹ := by ring
        _ = rho ^ a * (rho ^ j)⁻¹ := by rw [← hpow]
    have htail_factor_nonneg :
        0 ≤ rho ^ a * (rho ^ j)⁻¹ :=
      mul_nonneg (pow_nonneg hrho_pos.le a)
        (inv_nonneg.mpr (pow_nonneg hrho_pos.le j))
    have hnum_le :
        ((Nat.choose a j : ℝ) * rho ^ (a - j)) * C ≤
          (((((a + 1 : ℕ) : ℝ) ^ j) *
              (rho ^ a * (rho ^ j)⁻¹)) * C) := by
      rw [hrho_shift]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hchoose_le_succ htail_factor_nonneg)
        hC_nonneg
    have hdiv_le :
        (((Nat.choose a j : ℝ) * rho ^ (a - j)) * C) /
            boundedPowerMarginalScale beta a ≤
          (((((a + 1 : ℕ) : ℝ) ^ j) *
              (rho ^ a * (rho ^ j)⁻¹)) * C) /
            boundedPowerMarginalScale beta a :=
      div_le_div_of_nonneg_right hnum_le
        (boundedPowerMarginalScale_pos beta a).le
    calc
      (((Nat.choose a j : ℝ) * (1 - p) ^ (a - j)) * C) /
          boundedPowerMarginalScale beta a
          ≤ (((((a + 1 : ℕ) : ℝ) ^ j) *
              (rho ^ a * (rho ^ j)⁻¹)) * C) /
              boundedPowerMarginalScale beta a := by
            simpa [rho] using hdiv_le
      _ = ((C * (rho ^ j)⁻¹) *
              ((((a + 1 : ℕ) : ℝ) ^ j) * rho ^ a)) /
            boundedPowerMarginalScale beta a := by ring

/--
Finite-support geometric domination makes the above-`delta` Lemma D.2 tail
negligible relative to `a^(-1 / beta)`.
-/
theorem boundedLemmaD2IntegralTermAbove_negligible_of_geometric_support_bound
    {G : ℝ → ℝ} (hG_measurable : Measurable G)
    {beta delta M p : ℝ} (hbeta_pos : 0 < beta)
    (hdelta_nonneg : 0 ≤ delta) (hdeltaM : delta ≤ M)
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    (hp_le_G_on_tail : ∀ x : ℝ, delta < x → p ≤ G x)
    (j : ℕ) :
    Tendsto
      (fun a : ℕ =>
        boundedLemmaD2IntegralTermAbove G j a delta /
          boundedTailScale beta a)
      atTop (nhds 0) := by
  have hC_nonneg : 0 ≤ M - delta := sub_nonneg.mpr hdeltaM
  have hscalar :
      Tendsto
        (fun a : ℕ =>
          (((Nat.choose a j : ℝ) * (1 - p) ^ (a - j)) *
              (M - delta)) /
            boundedTailScale beta a)
        atTop (nhds 0) :=
    boundedTailScale_choose_geometric_tail_ratio_tendsto_zero
      hbeta_pos hp_pos hp_lt_one hC_nonneg j
  refine squeeze_zero' ?_ ?_ hscalar
  · filter_upwards [boundedTailScale_eventually_pos beta] with a hscale_pos
    exact div_nonneg
      (boundedLemmaD2IntegralTermAbove_nonneg_of_cdf_range
        (G := G) j a delta hG_nonneg hG_le_one)
      hscale_pos.le
  · filter_upwards
      [eventually_gt_atTop j, boundedTailScale_eventually_pos beta] with
        a hja hscale_pos
    have htail :=
      boundedLemmaD2IntegralTermAbove_le_geometric_support_bound
        hG_measurable hdelta_nonneg hdeltaM hp_pos.le hp_lt_one.le
        hG_nonneg hG_le_one hG_eq_one_of_support hp_le_G_on_tail hja
    exact div_le_div_of_nonneg_right htail hscale_pos.le

/--
Finite-support geometric domination makes the above-`delta` Lemma D.2 tail
negligible relative to the bounded marginal scale.
-/
theorem boundedLemmaD2IntegralTermAbove_negligible_powerMarginalScale_of_geometric_support_bound
    {G : ℝ → ℝ} (hG_measurable : Measurable G)
    {beta delta M p : ℝ} (hbeta_pos : 0 < beta)
    (hdelta_nonneg : 0 ≤ delta) (hdeltaM : delta ≤ M)
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    (hp_le_G_on_tail : ∀ x : ℝ, delta < x → p ≤ G x)
    (j : ℕ) :
    Tendsto
      (fun a : ℕ =>
        boundedLemmaD2IntegralTermAbove G j a delta /
          boundedPowerMarginalScale beta a)
      atTop (nhds 0) := by
  have hC_nonneg : 0 ≤ M - delta := sub_nonneg.mpr hdeltaM
  have hscalar :
      Tendsto
        (fun a : ℕ =>
          (((Nat.choose a j : ℝ) * (1 - p) ^ (a - j)) *
              (M - delta)) /
            boundedPowerMarginalScale beta a)
        atTop (nhds 0) :=
    boundedPowerMarginalScale_choose_geometric_tail_ratio_tendsto_zero
      hbeta_pos hp_pos hp_lt_one hC_nonneg j
  refine squeeze_zero' ?_ ?_ hscalar
  · filter_upwards with a
    exact div_nonneg
      (boundedLemmaD2IntegralTermAbove_nonneg_of_cdf_range
        (G := G) j a delta hG_nonneg hG_le_one)
      (boundedPowerMarginalScale_pos beta a).le
  · filter_upwards [eventually_gt_atTop j] with a hja
    have htail :=
      boundedLemmaD2IntegralTermAbove_le_geometric_support_bound
        hG_measurable hdelta_nonneg hdeltaM hp_pos.le hp_lt_one.le
        hG_nonneg hG_le_one hG_eq_one_of_support hp_le_G_on_tail hja
    exact div_le_div_of_nonneg_right htail
      (boundedPowerMarginalScale_pos beta a).le

/--
The adjacent difference of above-`delta` tails is negligible at the bounded
marginal scale.
-/
theorem boundedLemmaD2IntegralTermAbove_forward_difference_negligible_powerMarginalScale_of_geometric_support_bound
    {G : ℝ → ℝ} (hG_measurable : Measurable G)
    {beta delta M p : ℝ} (hbeta_pos : 0 < beta)
    (hdelta_nonneg : 0 ≤ delta) (hdeltaM : delta ≤ M)
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    (hp_le_G_on_tail : ∀ x : ℝ, delta < x → p ≤ G x)
    (j : ℕ) :
    Tendsto
      (fun a : ℕ =>
        (boundedLemmaD2IntegralTermAbove G j a delta -
          boundedLemmaD2IntegralTermAbove G j (a + 1) delta) /
          boundedPowerMarginalScale beta a)
      atTop (nhds 0) := by
  have htail :=
    boundedLemmaD2IntegralTermAbove_negligible_powerMarginalScale_of_geometric_support_bound
      hG_measurable hbeta_pos hdelta_nonneg hdeltaM hp_pos hp_lt_one
      hG_nonneg hG_le_one hG_eq_one_of_support hp_le_G_on_tail j
  have htail_succ_at_succ :
      Tendsto
        (fun a : ℕ =>
          boundedLemmaD2IntegralTermAbove G j (a + 1) delta /
            boundedPowerMarginalScale beta (a + 1))
        atTop (nhds 0) :=
    htail.comp (tendsto_add_atTop_nat 1)
  have hscale_ratio :=
    boundedPowerMarginalScale_succ_ratio_tendsto_one hbeta_pos
  have htail_succ :
      Tendsto
        (fun a : ℕ =>
          boundedLemmaD2IntegralTermAbove G j (a + 1) delta /
            boundedPowerMarginalScale beta a)
        atTop (nhds 0) := by
    have hprod := htail_succ_at_succ.mul hscale_ratio
    refine Tendsto.congr' ?_ (by simpa using hprod)
    filter_upwards with a
    have hscale_ne : boundedPowerMarginalScale beta a ≠ 0 :=
      (boundedPowerMarginalScale_pos beta a).ne'
    have hscale_succ_ne :
        boundedPowerMarginalScale beta (a + 1) ≠ 0 :=
      (boundedPowerMarginalScale_pos beta (a + 1)).ne'
    field_simp [hscale_ne, hscale_succ_ne]
  have hdiff := htail.sub htail_succ
  refine Tendsto.congr' ?_ (by simpa using hdiff)
  filter_upwards with a
  have hscale_ne : boundedPowerMarginalScale beta a ≠ 0 :=
    (boundedPowerMarginalScale_pos beta a).ne'
  field_simp [hscale_ne]

/--
Exact near-zero/tail split of the source Lemma D.2 integral.

This closes the bookkeeping part of the paper's split at `delta`; the remaining
analytic work is the near-zero asymptotic and the tail-negligibility estimate.
-/
theorem boundedLemmaD2IntegralTerm_split
    (G : ℝ → ℝ) (j a : ℕ) {delta : ℝ} (hdelta_nonneg : 0 ≤ delta)
    (h_integrable :
      MeasureTheory.IntegrableOn
        (boundedLemmaD2IntegralKernel G j a)
        (Set.Ioi (0 : ℝ))) :
    boundedLemmaD2IntegralTerm G j a =
      boundedLemmaD2IntegralTermBelow G j a delta +
        boundedLemmaD2IntegralTermAbove G j a delta := by
  let kernel := boundedLemmaD2IntegralKernel G j a
  have htail :=
    intervalIntegral.integral_Ioi_sub_Ioi
      (f := kernel) (μ := MeasureTheory.volume)
      h_integrable hdelta_nonneg
  have hinterval :
      ∫ x in (0 : ℝ)..delta, kernel x =
        ∫ x in Set.Ioo (0 : ℝ) delta, kernel x := by
    rw [intervalIntegral.integral_of_le hdelta_nonneg,
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
  dsimp [boundedLemmaD2IntegralTerm, boundedLemmaD2IntegralTermBelow,
    boundedLemmaD2IntegralTermAbove, kernel] at htail hinterval ⊢
  rw [← hinterval]
  linarith

/--
Eventual near-zero/tail split of the source Lemma D.2 integral from eventual
integrability of the source kernel.
-/
theorem boundedLemmaD2IntegralTerm_eventually_split
    (G : ℝ → ℝ) (j : ℕ) {delta : ℝ} (hdelta_nonneg : 0 ≤ delta)
    (h_integrable :
      ∀ᶠ a in atTop,
        MeasureTheory.IntegrableOn
          (boundedLemmaD2IntegralKernel G j a)
          (Set.Ioi (0 : ℝ))) :
    ∀ᶠ a in atTop,
      boundedLemmaD2IntegralTerm G j a =
        boundedLemmaD2IntegralTermBelow G j a delta +
          boundedLemmaD2IntegralTermAbove G j a delta := by
  filter_upwards [h_integrable] with a h_integrable_a
  exact boundedLemmaD2IntegralTerm_split G j a hdelta_nonneg h_integrable_a

/--
Source change of variables for Lemma D.2:
`x = y * a^(-1/beta)` on `(0,∞)`.
-/
theorem boundedLemmaD2IntegralTerm_changeOfVariables
    (G : ℝ → ℝ) (beta : ℝ) (j a : ℕ)
    (hscale_pos : 0 < boundedTailScale beta a) :
    boundedLemmaD2IntegralTerm G j a =
      boundedTailScale beta a *
        ∫ y in Set.Ioi (0 : ℝ),
          boundedLemmaD2RescaledKernel G beta j a y := by
  let scale := boundedTailScale beta a
  let kernel : ℝ → ℝ :=
    fun x => (Nat.choose a j : ℝ) * (G x) ^ j * (1 - G x) ^ (a - j)
  have hcv :=
    MeasureTheory.integral_comp_mul_left_Ioi (g := kernel) (a := (0 : ℝ))
      (b := scale) hscale_pos
  have hmul :
      scale * (∫ y in Set.Ioi (0 : ℝ), kernel (scale * y)) =
        ∫ x in Set.Ioi (0 : ℝ), kernel x := by
    rw [hcv]
    simp [scale, hscale_pos.ne']
  calc
    boundedLemmaD2IntegralTerm G j a =
        ∫ x in Set.Ioi (0 : ℝ), kernel x := by
          rfl
    _ = scale * (∫ y in Set.Ioi (0 : ℝ), kernel (scale * y)) := hmul.symm
    _ =
        boundedTailScale beta a *
          ∫ y in Set.Ioi (0 : ℝ),
            boundedLemmaD2RescaledKernel G beta j a y := by
          dsimp [scale]
          congr 1
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
          intro y _hy
          simp [kernel, boundedLemmaD2RescaledKernel, mul_comm, mul_left_comm,
            mul_assoc]

/--
Source change of variables for the adjacent finite difference of Lemma D.2
terms, using the same `a`-scale for both adjacent source kernels.
-/
theorem boundedLemmaD2IntegralTerm_forward_difference_changeOfVariables
    (G : ℝ → ℝ) (beta : ℝ) (j a : ℕ)
    (hscale_pos : 0 < boundedTailScale beta a)
    (h_integrable_a :
      MeasureTheory.IntegrableOn
        (boundedLemmaD2IntegralKernel G j a)
        (Set.Ioi (0 : ℝ)))
    (h_integrable_succ :
      MeasureTheory.IntegrableOn
        (boundedLemmaD2IntegralKernel G j (a + 1))
        (Set.Ioi (0 : ℝ))) :
    boundedLemmaD2IntegralTerm G j a -
        boundedLemmaD2IntegralTerm G j (a + 1) =
      (boundedTailScale beta a / (((a + 1 : ℕ) : ℝ))) *
        ∫ y in Set.Ioi (0 : ℝ),
          boundedLemmaD2ForwardDifferenceRescaledKernel G beta j a y := by
  let scale := boundedTailScale beta a
  let kernel : ℕ → ℝ → ℝ :=
    fun n x => boundedLemmaD2IntegralKernel G j n x
  let diffKernel : ℝ → ℝ := fun x => kernel a x - kernel (a + 1) x
  have hsource_sub :
      boundedLemmaD2IntegralTerm G j a -
          boundedLemmaD2IntegralTerm G j (a + 1) =
        ∫ x in Set.Ioi (0 : ℝ), diffKernel x := by
    dsimp [boundedLemmaD2IntegralTerm, diffKernel, kernel]
    rw [MeasureTheory.integral_sub h_integrable_a h_integrable_succ]
  have hcv :=
    MeasureTheory.integral_comp_mul_left_Ioi
      (g := diffKernel) (a := (0 : ℝ)) (b := scale) hscale_pos
  have hmul :
      scale * (∫ y in Set.Ioi (0 : ℝ), diffKernel (scale * y)) =
        ∫ x in Set.Ioi (0 : ℝ), diffKernel x := by
    rw [hcv]
    simp [scale, hscale_pos.ne']
  have hforward_integral :
      (∫ y in Set.Ioi (0 : ℝ),
          boundedLemmaD2ForwardDifferenceRescaledKernel G beta j a y) =
        (((a + 1 : ℕ) : ℝ)) *
          ∫ y in Set.Ioi (0 : ℝ), diffKernel (scale * y) := by
    calc
      (∫ y in Set.Ioi (0 : ℝ),
          boundedLemmaD2ForwardDifferenceRescaledKernel G beta j a y)
          =
        ∫ y in Set.Ioi (0 : ℝ),
          (((a + 1 : ℕ) : ℝ)) * diffKernel (scale * y) := by
            refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
            intro y _hy
            simp [diffKernel, kernel, scale,
              boundedLemmaD2ForwardDifferenceRescaledKernel,
              mul_comm]
      _ =
        (((a + 1 : ℕ) : ℝ)) *
          ∫ y in Set.Ioi (0 : ℝ), diffKernel (scale * y) := by
            rw [MeasureTheory.integral_const_mul]
  have hden_ne : (((a + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  calc
    boundedLemmaD2IntegralTerm G j a -
        boundedLemmaD2IntegralTerm G j (a + 1)
        = ∫ x in Set.Ioi (0 : ℝ), diffKernel x := hsource_sub
    _ = scale *
          (∫ y in Set.Ioi (0 : ℝ), diffKernel (scale * y)) := hmul.symm
    _ =
        (scale / (((a + 1 : ℕ) : ℝ))) *
          ((((a + 1 : ℕ) : ℝ)) *
            ∫ y in Set.Ioi (0 : ℝ), diffKernel (scale * y)) := by
          field_simp [hden_ne]
    _ =
        (boundedTailScale beta a / (((a + 1 : ℕ) : ℝ))) *
          ∫ y in Set.Ioi (0 : ℝ),
            boundedLemmaD2ForwardDifferenceRescaledKernel G beta j a y := by
          dsimp [scale]
          rw [← hforward_integral]

/--
Eventual source change of variables for the adjacent finite difference of
Lemma D.2 terms, from eventual integrability of the source kernels.
-/
theorem boundedLemmaD2IntegralTerm_forward_difference_eventually_changeOfVariables
    (G : ℝ → ℝ) (beta : ℝ) (j : ℕ)
    (h_integrable :
      ∀ᶠ a in atTop,
        MeasureTheory.IntegrableOn
          (boundedLemmaD2IntegralKernel G j a)
          (Set.Ioi (0 : ℝ))) :
    ∀ᶠ a in atTop,
      boundedLemmaD2IntegralTerm G j a -
          boundedLemmaD2IntegralTerm G j (a + 1) =
        (boundedTailScale beta a / (((a + 1 : ℕ) : ℝ))) *
          ∫ y in Set.Ioi (0 : ℝ),
            boundedLemmaD2ForwardDifferenceRescaledKernel G beta j a y := by
  have h_integrable_succ :
      ∀ᶠ a in atTop,
        MeasureTheory.IntegrableOn
          (boundedLemmaD2IntegralKernel G j (a + 1))
          (Set.Ioi (0 : ℝ)) :=
    (Filter.tendsto_add_atTop_nat 1).eventually h_integrable
  filter_upwards
    [boundedTailScale_eventually_pos beta,
      h_integrable, h_integrable_succ] with
      a hscale_pos h_integrable_a h_integrable_succ_a
  exact
    boundedLemmaD2IntegralTerm_forward_difference_changeOfVariables
      G beta j a hscale_pos h_integrable_a h_integrable_succ_a

/--
Full rescaled finite-difference convergence gives the source adjacent-drop
asymptotic at the scale `a^(-1/beta)/(a+1)`.
-/
theorem boundedLemmaD2IntegralTerm_forward_difference_asymptotic_of_rescaled_integral
    {G : ℝ → ℝ} {beta c : ℝ} (j : ℕ)
    (hcoeff_ne :
      boundedLemmaD2ForwardDifferenceLimitCoeff beta c j ≠ 0)
    (h_integrable :
      ∀ᶠ a in atTop,
        MeasureTheory.IntegrableOn
          (boundedLemmaD2IntegralKernel G j a)
          (Set.Ioi (0 : ℝ)))
    (hrescaled :
      Tendsto
        (fun a : ℕ =>
          ∫ y in Set.Ioi (0 : ℝ),
            boundedLemmaD2ForwardDifferenceRescaledKernel G beta j a y)
        atTop
        (nhds (boundedLemmaD2ForwardDifferenceLimitCoeff beta c j))) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun a =>
        boundedLemmaD2IntegralTerm G j a -
          boundedLemmaD2IntegralTerm G j (a + 1))
      (fun a =>
        boundedLemmaD2ForwardDifferenceLimitCoeff beta c j *
          (boundedTailScale beta a / (((a + 1 : ℕ) : ℝ)))) := by
  have hratio :
      Tendsto
        (fun a : ℕ =>
          (∫ y in Set.Ioi (0 : ℝ),
            boundedLemmaD2ForwardDifferenceRescaledKernel G beta j a y) /
              boundedLemmaD2ForwardDifferenceLimitCoeff beta c j)
        atTop (nhds 1) := by
    have h :=
      hrescaled.div_const
        (boundedLemmaD2ForwardDifferenceLimitCoeff beta c j)
    simpa [hcoeff_ne] using h
  rw [AppliedModelingLib.Math.AsymptoticEquivalent]
  refine Tendsto.congr' ?_ hratio
  filter_upwards
    [boundedLemmaD2IntegralTerm_forward_difference_eventually_changeOfVariables
      G beta j h_integrable,
      boundedTailScale_eventually_ne_zero beta] with
      a hchange hscale_ne
  have hden_ne : (((a + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  rw [hchange]
  field_simp [hcoeff_ne, hscale_ne, hden_ne]

/--
Paper-scale fixed-rank adjacent-drop asymptotic from full rescaled
finite-difference convergence.
-/
theorem boundedLemmaD2IntegralTerm_forward_difference_asymptotic_of_rescaled_integral_paper_scale
    {G : ℝ → ℝ} {beta c : ℝ}
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c) (j : ℕ)
    (h_integrable :
      ∀ᶠ a in atTop,
        MeasureTheory.IntegrableOn
          (boundedLemmaD2IntegralKernel G j a)
          (Set.Ioi (0 : ℝ)))
    (hrescaled :
      Tendsto
        (fun a : ℕ =>
          ∫ y in Set.Ioi (0 : ℝ),
            boundedLemmaD2ForwardDifferenceRescaledKernel G beta j a y)
        atTop
        (nhds (boundedLemmaD2ForwardDifferenceLimitCoeff beta c j))) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun a =>
        boundedLemmaD2IntegralTerm G j a -
          boundedLemmaD2IntegralTerm G j (a + 1))
      (fun a =>
        (boundedLemmaD2LimitCoeff beta c j / beta) *
          boundedPowerMarginalScale beta a) := by
  have hcoeff_eq :
      boundedLemmaD2ForwardDifferenceLimitCoeff beta c j =
        boundedLemmaD2LimitCoeff beta c j / beta :=
    boundedLemmaD2ForwardDifferenceLimitCoeff_eq_div hbeta_pos hc_pos j
  have hcoeff_target_ne :
      boundedLemmaD2LimitCoeff beta c j / beta ≠ 0 := by
    exact div_ne_zero
      (ne_of_gt (boundedLemmaD2LimitCoeff_pos hbeta_pos hc_pos j))
      (ne_of_gt hbeta_pos)
  have hcoeff_ne :
      boundedLemmaD2ForwardDifferenceLimitCoeff beta c j ≠ 0 := by
    rw [hcoeff_eq]
    exact hcoeff_target_ne
  have hdrop :=
    boundedLemmaD2IntegralTerm_forward_difference_asymptotic_of_rescaled_integral
      (G := G) (beta := beta) (c := c) j hcoeff_ne h_integrable
      hrescaled
  have hscale := boundedTailScale_div_succ_ratio_tendsto_one hbeta_pos
  rw [AppliedModelingLib.Math.AsymptoticEquivalent] at hdrop ⊢
  have hprod := hdrop.mul hscale
  refine Tendsto.congr' ?_ (by simpa using hprod)
  filter_upwards
    [boundedTailScale_eventually_ne_zero beta] with a htail_ne
  have hden_ne : (((a + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have htail_div_ne :
      boundedTailScale beta a / (((a + 1 : ℕ) : ℝ)) ≠ 0 :=
    div_ne_zero htail_ne hden_ne
  have hpower_ne : boundedPowerMarginalScale beta a ≠ 0 :=
    (boundedPowerMarginalScale_pos beta a).ne'
  rw [hcoeff_eq]
  field_simp [hcoeff_target_ne, htail_div_ne, hpower_ne]

/--
Near-zero source change of variables for the adjacent finite difference of
Lemma D.2 terms.
-/
theorem boundedLemmaD2IntegralTermBelow_forward_difference_changeOfVariables
    (G : ℝ → ℝ) (beta : ℝ) (j a : ℕ) {delta : ℝ}
    (hdelta_nonneg : 0 ≤ delta)
    (hscale_pos : 0 < boundedTailScale beta a)
    (h_integrable_a :
      MeasureTheory.IntegrableOn
        (boundedLemmaD2IntegralKernel G j a)
        (Set.Ioi (0 : ℝ)))
    (h_integrable_succ :
      MeasureTheory.IntegrableOn
        (boundedLemmaD2IntegralKernel G j (a + 1))
        (Set.Ioi (0 : ℝ))) :
    boundedLemmaD2IntegralTermBelow G j a delta -
        boundedLemmaD2IntegralTermBelow G j (a + 1) delta =
      (boundedTailScale beta a / (((a + 1 : ℕ) : ℝ))) *
        ∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale beta a),
          boundedLemmaD2ForwardDifferenceRescaledKernel G beta j a y := by
  let scale := boundedTailScale beta a
  let kernel : ℕ → ℝ → ℝ :=
    fun n x => boundedLemmaD2IntegralKernel G j n x
  let diffKernel : ℝ → ℝ := fun x => kernel a x - kernel (a + 1) x
  have h_integrable_below_a :
      MeasureTheory.IntegrableOn (kernel a) (Set.Ioo (0 : ℝ) delta) :=
    h_integrable_a.mono_set (fun x hx => hx.1)
  have h_integrable_below_succ :
      MeasureTheory.IntegrableOn (kernel (a + 1)) (Set.Ioo (0 : ℝ) delta) :=
    h_integrable_succ.mono_set (fun x hx => hx.1)
  have hupper_nonneg : 0 ≤ delta / scale :=
    div_nonneg hdelta_nonneg hscale_pos.le
  have hsource_sub :
      boundedLemmaD2IntegralTermBelow G j a delta -
          boundedLemmaD2IntegralTermBelow G j (a + 1) delta =
        ∫ x in Set.Ioo (0 : ℝ) delta, diffKernel x := by
    dsimp [boundedLemmaD2IntegralTermBelow, diffKernel, kernel]
    rw [MeasureTheory.integral_sub
      h_integrable_below_a h_integrable_below_succ]
  have hdiff_interval :
      ∫ x in Set.Ioo (0 : ℝ) delta, diffKernel x =
        ∫ x in (0 : ℝ)..delta, diffKernel x := by
    rw [intervalIntegral.integral_of_le hdelta_nonneg,
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
  have hy_interval :
      ∫ y in Set.Ioo (0 : ℝ) (delta / scale), diffKernel (scale * y) =
        ∫ y in (0 : ℝ)..(delta / scale), diffKernel (scale * y) := by
    rw [intervalIntegral.integral_of_le hupper_nonneg,
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
  have hcv :
      scale * (∫ y in (0 : ℝ)..(delta / scale),
          diffKernel (scale * y)) =
        ∫ x in (0 : ℝ)..delta, diffKernel x := by
    have h :=
      intervalIntegral.smul_integral_comp_mul_left
        (f := diffKernel) (a := (0 : ℝ)) (b := delta / scale) scale
    have hscale_ne : scale ≠ 0 := ne_of_gt hscale_pos
    calc
      scale * (∫ y in (0 : ℝ)..(delta / scale),
          diffKernel (scale * y))
          =
        scale • (∫ y in (0 : ℝ)..(delta / scale),
          diffKernel (scale * y)) := by rfl
      _ = ∫ x in scale * (0 : ℝ)..scale * (delta / scale),
            diffKernel x := h
      _ = ∫ x in (0 : ℝ)..scale * (delta / scale), diffKernel x := by
            rw [mul_zero]
      _ = ∫ x in (0 : ℝ)..delta, diffKernel x := by
            congr 1
            field_simp [hscale_ne]
  have hforward_integral :
      (∫ y in Set.Ioo (0 : ℝ) (delta / scale),
          boundedLemmaD2ForwardDifferenceRescaledKernel G beta j a y) =
        (((a + 1 : ℕ) : ℝ)) *
          ∫ y in Set.Ioo (0 : ℝ) (delta / scale),
            diffKernel (scale * y) := by
    calc
      (∫ y in Set.Ioo (0 : ℝ) (delta / scale),
          boundedLemmaD2ForwardDifferenceRescaledKernel G beta j a y)
          =
        ∫ y in Set.Ioo (0 : ℝ) (delta / scale),
          (((a + 1 : ℕ) : ℝ)) * diffKernel (scale * y) := by
            refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo ?_
            intro y _hy
            simp [diffKernel, kernel, scale,
              boundedLemmaD2ForwardDifferenceRescaledKernel, mul_comm]
      _ =
        (((a + 1 : ℕ) : ℝ)) *
          ∫ y in Set.Ioo (0 : ℝ) (delta / scale),
            diffKernel (scale * y) := by
            rw [MeasureTheory.integral_const_mul]
  have hden_ne : (((a + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  calc
    boundedLemmaD2IntegralTermBelow G j a delta -
        boundedLemmaD2IntegralTermBelow G j (a + 1) delta
        = ∫ x in Set.Ioo (0 : ℝ) delta, diffKernel x := hsource_sub
    _ = ∫ x in (0 : ℝ)..delta, diffKernel x := hdiff_interval
    _ = scale * (∫ y in (0 : ℝ)..(delta / scale),
          diffKernel (scale * y)) := hcv.symm
    _ = scale *
          (∫ y in Set.Ioo (0 : ℝ) (delta / scale),
            diffKernel (scale * y)) := by rw [hy_interval]
    _ =
        (scale / (((a + 1 : ℕ) : ℝ))) *
          ((((a + 1 : ℕ) : ℝ)) *
            ∫ y in Set.Ioo (0 : ℝ) (delta / scale),
              diffKernel (scale * y)) := by
          field_simp [hden_ne]
    _ =
        (boundedTailScale beta a / (((a + 1 : ℕ) : ℝ))) *
          ∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale beta a),
            boundedLemmaD2ForwardDifferenceRescaledKernel G beta j a y := by
          dsimp [scale]
          rw [← hforward_integral]

/--
Eventual near-zero source change of variables for the adjacent finite
difference of Lemma D.2 terms.
-/
theorem boundedLemmaD2IntegralTermBelow_forward_difference_eventually_changeOfVariables
    (G : ℝ → ℝ) (beta : ℝ) (j : ℕ) {delta : ℝ}
    (hdelta_nonneg : 0 ≤ delta)
    (h_integrable :
      ∀ᶠ a in atTop,
        MeasureTheory.IntegrableOn
          (boundedLemmaD2IntegralKernel G j a)
          (Set.Ioi (0 : ℝ))) :
    ∀ᶠ a in atTop,
      boundedLemmaD2IntegralTermBelow G j a delta -
          boundedLemmaD2IntegralTermBelow G j (a + 1) delta =
        (boundedTailScale beta a / (((a + 1 : ℕ) : ℝ))) *
          ∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale beta a),
            boundedLemmaD2ForwardDifferenceRescaledKernel G beta j a y := by
  have h_integrable_succ :
      ∀ᶠ a in atTop,
        MeasureTheory.IntegrableOn
          (boundedLemmaD2IntegralKernel G j (a + 1))
          (Set.Ioi (0 : ℝ)) :=
    (Filter.tendsto_add_atTop_nat 1).eventually h_integrable
  filter_upwards
    [boundedTailScale_eventually_pos beta,
      h_integrable, h_integrable_succ] with
      a hscale_pos h_integrable_a h_integrable_succ_a
  exact
    boundedLemmaD2IntegralTermBelow_forward_difference_changeOfVariables
      G beta j a hdelta_nonneg hscale_pos h_integrable_a
      h_integrable_succ_a

/--
Near-zero source change of variables for Lemma D.2:
`x = y * a^(-1/beta)` on `(0, delta)`.
-/
theorem boundedLemmaD2IntegralTermBelow_changeOfVariables
    (G : ℝ → ℝ) (beta : ℝ) (j a : ℕ) {delta : ℝ}
    (hdelta_nonneg : 0 ≤ delta)
    (hscale_pos : 0 < boundedTailScale beta a) :
    boundedLemmaD2IntegralTermBelow G j a delta =
      boundedTailScale beta a *
        ∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale beta a),
          boundedLemmaD2RescaledKernel G beta j a y := by
  let scale := boundedTailScale beta a
  let kernel : ℝ → ℝ :=
    fun x => (Nat.choose a j : ℝ) * (G x) ^ j * (1 - G x) ^ (a - j)
  have hscale_ne : scale ≠ 0 := ne_of_gt hscale_pos
  have hupper_nonneg : 0 ≤ delta / scale :=
    div_nonneg hdelta_nonneg hscale_pos.le
  have hbelow_interval :
      boundedLemmaD2IntegralTermBelow G j a delta =
        ∫ x in (0 : ℝ)..delta, kernel x := by
    rw [intervalIntegral.integral_of_le hdelta_nonneg,
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rfl
  have hy_interval :
      ∫ y in Set.Ioo (0 : ℝ) (delta / scale), kernel (scale * y) =
        ∫ y in (0 : ℝ)..(delta / scale), kernel (scale * y) := by
    rw [intervalIntegral.integral_of_le hupper_nonneg,
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
  have hcv :
      scale * (∫ y in (0 : ℝ)..(delta / scale), kernel (scale * y)) =
        ∫ x in (0 : ℝ)..delta, kernel x := by
    have h :=
      intervalIntegral.smul_integral_comp_mul_left
        (f := kernel) (a := (0 : ℝ)) (b := delta / scale) scale
    calc
      scale * (∫ y in (0 : ℝ)..(delta / scale), kernel (scale * y))
          = scale • (∫ y in (0 : ℝ)..(delta / scale), kernel (scale * y)) := by
            rfl
      _ = ∫ x in scale * (0 : ℝ)..scale * (delta / scale), kernel x := h
      _ = ∫ x in (0 : ℝ)..scale * (delta / scale), kernel x := by
            rw [mul_zero]
      _ = ∫ x in (0 : ℝ)..delta, kernel x := by
            congr 1
            field_simp [hscale_ne]
  calc
    boundedLemmaD2IntegralTermBelow G j a delta =
        ∫ x in (0 : ℝ)..delta, kernel x := hbelow_interval
    _ = scale *
        (∫ y in (0 : ℝ)..(delta / scale), kernel (scale * y)) := hcv.symm
    _ = boundedTailScale beta a *
        ∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale beta a),
          boundedLemmaD2RescaledKernel G beta j a y := by
          dsimp [scale]
          rw [← hy_interval]
          congr 1
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo ?_
          intro y _hy
          simp [kernel, boundedLemmaD2RescaledKernel, scale, mul_comm, mul_left_comm,
            mul_assoc]

/--
Above-`delta` source change of variables for Lemma D.2:
`x = y * a^(-1/beta)` on `(delta, ∞)`.
-/
theorem boundedLemmaD2IntegralTermAbove_changeOfVariables
    (G : ℝ → ℝ) (beta : ℝ) (j a : ℕ) {delta : ℝ}
    (hscale_pos : 0 < boundedTailScale beta a) :
    boundedLemmaD2IntegralTermAbove G j a delta =
      boundedTailScale beta a *
        ∫ y in Set.Ioi (delta / boundedTailScale beta a),
          boundedLemmaD2RescaledKernel G beta j a y := by
  let scale := boundedTailScale beta a
  let kernel : ℝ → ℝ :=
    fun x => (Nat.choose a j : ℝ) * (G x) ^ j * (1 - G x) ^ (a - j)
  have hscale_ne : scale ≠ 0 := ne_of_gt hscale_pos
  have hendpoint : scale * (delta / scale) = delta := by
    field_simp [hscale_ne]
  have hcv :=
    MeasureTheory.integral_comp_mul_left_Ioi
      (g := kernel) (a := delta / scale) (b := scale) hscale_pos
  have hmul :
      scale * (∫ y in Set.Ioi (delta / scale), kernel (scale * y)) =
        ∫ x in Set.Ioi delta, kernel x := by
    rw [hcv]
    simp [hscale_ne, hendpoint]
  calc
    boundedLemmaD2IntegralTermAbove G j a delta =
        ∫ x in Set.Ioi delta, kernel x := by
          rfl
    _ = scale *
        (∫ y in Set.Ioi (delta / scale), kernel (scale * y)) := hmul.symm
    _ = boundedTailScale beta a *
        ∫ y in Set.Ioi (delta / boundedTailScale beta a),
          boundedLemmaD2RescaledKernel G beta j a y := by
          dsimp [scale]
          congr 1
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
          intro y _hy
          simp [kernel, boundedLemmaD2RescaledKernel, mul_comm, mul_left_comm,
            mul_assoc]

/--
Eventual near-zero source change of variables for Lemma D.2. The only
excluded finite prefix is where the scaling factor may be zero.
-/
theorem boundedLemmaD2IntegralTermBelow_eventually_changeOfVariables
    (G : ℝ → ℝ) (beta : ℝ) (j : ℕ) {delta : ℝ}
    (hdelta_nonneg : 0 ≤ delta) :
    ∀ᶠ a in atTop,
      boundedLemmaD2IntegralTermBelow G j a delta =
        boundedTailScale beta a *
          ∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale beta a),
            boundedLemmaD2RescaledKernel G beta j a y := by
  filter_upwards [boundedTailScale_eventually_pos beta] with a hscale_pos
  exact boundedLemmaD2IntegralTermBelow_changeOfVariables
    G beta j a hdelta_nonneg hscale_pos

/--
Eventual above-`delta` source change of variables for Lemma D.2. The only
excluded finite prefix is where the scaling factor may be zero.
-/
theorem boundedLemmaD2IntegralTermAbove_eventually_changeOfVariables
    (G : ℝ → ℝ) (beta : ℝ) (j : ℕ) (delta : ℝ) :
    ∀ᶠ a in atTop,
      boundedLemmaD2IntegralTermAbove G j a delta =
        boundedTailScale beta a *
          ∫ y in Set.Ioi (delta / boundedTailScale beta a),
            boundedLemmaD2RescaledKernel G beta j a y := by
  filter_upwards [boundedTailScale_eventually_pos beta] with a hscale_pos
  exact boundedLemmaD2IntegralTermAbove_changeOfVariables
    G beta j a hscale_pos

/--
Near-zero source asymptotic from convergence of the growing rescaled integral.

After the substitution `x = y*a^(-1/beta)`, the below-`delta` interval becomes
`0 < y < delta / a^(-1/beta)`. This theorem isolates the remaining analytic
task: prove convergence of that growing-interval rescaled integral to the
gamma coefficient.
-/
theorem boundedLemmaD2IntegralTermBelow_asymptotic_of_growing_rescaled_integral
    {G : ℝ → ℝ} {beta c : ℝ} (hbeta_pos : 0 < beta)
    (hc_pos : 0 < c) (j : ℕ) {delta : ℝ}
    (hdelta_nonneg : 0 ≤ delta)
    (hgrowing :
      Tendsto
        (fun a : ℕ =>
          ∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale beta a),
            boundedLemmaD2RescaledKernel G beta j a y)
        atTop (nhds (boundedLemmaD2LimitCoeff beta c j))) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun a => boundedLemmaD2IntegralTermBelow G j a delta)
      (fun a => boundedLemmaD2LimitCoeff beta c j *
        boundedTailScale beta a) := by
  have hcoeff_ne :
      boundedLemmaD2LimitCoeff beta c j ≠ 0 :=
    ne_of_gt (boundedLemmaD2LimitCoeff_pos hbeta_pos hc_pos j)
  have hratio :
      Tendsto
        (fun a : ℕ =>
          (∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale beta a),
            boundedLemmaD2RescaledKernel G beta j a y) /
            boundedLemmaD2LimitCoeff beta c j)
        atTop (nhds 1) := by
    have h :=
      hgrowing.div_const (boundedLemmaD2LimitCoeff beta c j)
    simpa [hcoeff_ne] using h
  rw [AppliedModelingLib.Math.AsymptoticEquivalent]
  refine Tendsto.congr' ?_ hratio
  filter_upwards
    [boundedLemmaD2IntegralTermBelow_eventually_changeOfVariables
      G beta j hdelta_nonneg,
      boundedTailScale_eventually_ne_zero beta] with a hchange hscale_ne
  rw [hchange]
  field_simp [hcoeff_ne, hscale_ne]

/--
Eventual source change of variables for Lemma D.2. The only excluded finite
prefix is where the scaling factor may be zero.
-/
theorem boundedLemmaD2IntegralTerm_eventually_changeOfVariables
    (G : ℝ → ℝ) (beta : ℝ) (j : ℕ) :
    ∀ᶠ a in atTop,
      boundedLemmaD2IntegralTerm G j a =
        boundedTailScale beta a *
          ∫ y in Set.Ioi (0 : ℝ),
            boundedLemmaD2RescaledKernel G beta j a y := by
  filter_upwards [boundedTailScale_eventually_pos beta] with a hscale_pos
  exact boundedLemmaD2IntegralTerm_changeOfVariables G beta j a hscale_pos

/--
Exact split of the rescaled Lemma D.2 integral at the growing threshold
`delta / a^(-1/beta)`.
-/
theorem boundedLemmaD2RescaledIntegral_split
    (G : ℝ → ℝ) (beta : ℝ) (j a : ℕ) {delta : ℝ}
    (hdelta_nonneg : 0 ≤ delta)
    (hscale_pos : 0 < boundedTailScale beta a)
    (h_integrable :
      MeasureTheory.IntegrableOn
        (fun y : ℝ => boundedLemmaD2RescaledKernel G beta j a y)
        (Set.Ioi (0 : ℝ))) :
    (∫ y in Set.Ioi (0 : ℝ),
        boundedLemmaD2RescaledKernel G beta j a y) =
      (∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale beta a),
        boundedLemmaD2RescaledKernel G beta j a y) +
      (∫ y in Set.Ioi (delta / boundedTailScale beta a),
        boundedLemmaD2RescaledKernel G beta j a y) := by
  let kernel : ℝ → ℝ :=
    fun y => boundedLemmaD2RescaledKernel G beta j a y
  have hupper_nonneg :
      0 ≤ delta / boundedTailScale beta a :=
    div_nonneg hdelta_nonneg hscale_pos.le
  have htail :=
    intervalIntegral.integral_Ioi_sub_Ioi
      (f := kernel) (μ := MeasureTheory.volume)
      h_integrable hupper_nonneg
  have hinterval :
      ∫ y in (0 : ℝ)..(delta / boundedTailScale beta a), kernel y =
        ∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale beta a),
          kernel y := by
    rw [intervalIntegral.integral_of_le hupper_nonneg,
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
  dsimp [kernel] at htail hinterval ⊢
  rw [← hinterval]
  linarith

/--
Eventual split of the rescaled Lemma D.2 integral at the growing threshold
`delta / a^(-1/beta)`.
-/
theorem boundedLemmaD2RescaledIntegral_eventually_split
    (G : ℝ → ℝ) (beta : ℝ) (j : ℕ) {delta : ℝ}
    (hdelta_nonneg : 0 ≤ delta)
    (h_integrable :
      ∀ᶠ a in atTop,
        MeasureTheory.IntegrableOn
          (fun y : ℝ => boundedLemmaD2RescaledKernel G beta j a y)
          (Set.Ioi (0 : ℝ))) :
    ∀ᶠ a in atTop,
      (∫ y in Set.Ioi (0 : ℝ),
          boundedLemmaD2RescaledKernel G beta j a y) =
        (∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale beta a),
          boundedLemmaD2RescaledKernel G beta j a y) +
        (∫ y in Set.Ioi (delta / boundedTailScale beta a),
          boundedLemmaD2RescaledKernel G beta j a y) := by
  filter_upwards
    [h_integrable, boundedTailScale_eventually_pos beta] with
      a h_integrable_a hscale_pos
  exact boundedLemmaD2RescaledIntegral_split
    G beta j a hdelta_nonneg hscale_pos h_integrable_a

/--
Integrating the rescaled kernel over the growing interval `(0,T)` is the same
as integrating the `Iio T`-truncated kernel against volume restricted to
`(0,∞)`.
-/
theorem boundedLemmaD2RescaledIntegral_Ioo_eq_indicator_integral
    (G : ℝ → ℝ) (beta : ℝ) (j a : ℕ) (T : ℝ) :
    (∫ y in Set.Ioo (0 : ℝ) T,
        boundedLemmaD2RescaledKernel G beta j a y) =
      ∫ y,
        (Set.Iio T).indicator
          (fun z : ℝ => boundedLemmaD2RescaledKernel G beta j a z) y
        ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  rw [MeasureTheory.integral_indicator measurableSet_Iio]
  rw [MeasureTheory.Measure.restrict_restrict measurableSet_Iio]
  have hset : Set.Iio T ∩ Set.Ioi (0 : ℝ) = Set.Ioo (0 : ℝ) T := by
    ext y
    simp [and_comm]
  rw [hset]

/--
Finite-difference analogue of
`boundedLemmaD2RescaledIntegral_Ioo_eq_indicator_integral`.
-/
theorem boundedLemmaD2ForwardDifferenceRescaledIntegral_Ioo_eq_indicator_integral
    (G : ℝ → ℝ) (beta : ℝ) (j a : ℕ) (T : ℝ) :
    (∫ y in Set.Ioo (0 : ℝ) T,
        boundedLemmaD2ForwardDifferenceRescaledKernel G beta j a y) =
      ∫ y,
        (Set.Iio T).indicator
          (fun z : ℝ =>
            boundedLemmaD2ForwardDifferenceRescaledKernel G beta j a z) y
        ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  rw [MeasureTheory.integral_indicator measurableSet_Iio]
  rw [MeasureTheory.Measure.restrict_restrict measurableSet_Iio]
  have hset : Set.Iio T ∩ Set.Ioi (0 : ℝ) = Set.Ioo (0 : ℝ) T := by
    ext y
    simp [and_comm]
  rw [hset]

/--
Direct growing near-zero rescaled-integral convergence from local CDF power
bounds. This is the paper's dominated-convergence step on the expanding
near-zero interval, with the domination applied to the indicator-truncated
kernels rather than to the full tail.
-/
theorem boundedLemmaD2GrowingRescaledIntegral_tendsto_of_local_cdf_power_bounds
    {G : ℝ → ℝ} {beta c A B : ℝ}
    (tail : BoundedTailCDFPowerSandwich G beta c)
    (hG_measurable : Measurable G)
    {delta : ℝ} (hdelta_pos : 0 < delta)
    (hA_pos : 0 < A) (hB_nonneg : 0 ≤ B)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_lower :
      ∀ x : ℝ, 0 < x → x < delta → A * x ^ beta ≤ G x)
    (hG_upper :
      ∀ x : ℝ, 0 < x → x < delta → G x ≤ B * x ^ beta)
    (j : ℕ) :
    Tendsto
      (fun a : ℕ =>
        ∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale beta a),
          boundedLemmaD2RescaledKernel G beta j a y)
      atTop (nhds (boundedLemmaD2LimitCoeff beta c j)) := by
  let μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
  let truncated : ℕ → ℝ → ℝ :=
    fun a y =>
      (Set.Iio (delta / boundedTailScale beta a)).indicator
        (fun z : ℝ => boundedLemmaD2RescaledKernel G beta j a z) y
  have hmeas :
      ∀ᶠ a in atTop,
        MeasureTheory.AEStronglyMeasurable (truncated a) μ := by
    filter_upwards with a
    dsimp [truncated, μ]
    exact
      (boundedLemmaD2RescaledKernel_aestronglyMeasurable
        hG_measurable beta j a).indicator measurableSet_Iio
  have hbound :
      ∀ᶠ a in atTop,
        ∀ᵐ y ∂μ,
          ‖truncated a y‖ ≤
            boundedLemmaD2LocalEnvelope beta A B j y := by
    simpa [truncated, μ] using
      boundedLemmaD2RescaledKernel_eventually_indicator_norm_le_localEnvelope
        j tail.beta_pos hA_pos hB_nonneg hG_nonneg hG_le_one
        hG_lower hG_upper
  have hbound_integrable :
      MeasureTheory.Integrable
        (boundedLemmaD2LocalEnvelope beta A B j) μ := by
    simpa [μ] using
      boundedLemmaD2LocalEnvelope_integrable tail.beta_pos hA_pos j
  have hlim :
      ∀ᵐ y ∂μ,
        Tendsto (fun a : ℕ => truncated a y) atTop
          (nhds (boundedLemmaD2LimitKernel beta c j y)) := by
    filter_upwards
      [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with y hy
    have hthreshold :
        ∀ᶠ a in atTop,
          y < delta / boundedTailScale beta a := by
      have hsmall :
          ∀ᶠ a in atTop,
            y * boundedTailScale beta a < delta :=
        (boundedTailScale_const_mul_tendsto_zero
          (y := y) tail.beta_pos).eventually
          (Iio_mem_nhds hdelta_pos)
      filter_upwards
        [hsmall, boundedTailScale_eventually_pos beta] with
          a hsmall_a hscale_pos
      rw [lt_div_iff₀ hscale_pos]
      simpa [mul_comm] using hsmall_a
    refine Tendsto.congr' ?_
      (tail.rescaled_kernel_tendsto_limit hy j)
    filter_upwards [hthreshold] with a hthreshold_a
    dsimp [truncated]
    rw [Set.indicator_of_mem (show y ∈ Set.Iio
      (delta / boundedTailScale beta a) from hthreshold_a)]
  have h :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := μ) (boundedLemmaD2LocalEnvelope beta A B j)
      hmeas hbound hbound_integrable hlim
  refine Tendsto.congr' ?_ (by simpa [μ, boundedLemmaD2LimitCoeff] using h)
  filter_upwards with a
  symm
  exact boundedLemmaD2RescaledIntegral_Ioo_eq_indicator_integral
    G beta j a (delta / boundedTailScale beta a)

/--
Finite-difference dominated-convergence step on the growing near-zero
interval. This is the normalized fixed-rank analogue of
`boundedLemmaD2GrowingRescaledIntegral_tendsto_of_local_cdf_power_bounds`.
-/
theorem boundedLemmaD2ForwardDifferenceGrowingRescaledIntegral_tendsto_of_local_cdf_power_bounds
    {G : ℝ → ℝ} {beta c A B : ℝ}
    (tail : BoundedTailCDFPowerSandwich G beta c)
    (hG_measurable : Measurable G)
    {delta : ℝ} (hdelta_pos : 0 < delta)
    (hA_pos : 0 < A) (hB_nonneg : 0 ≤ B)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_lower :
      ∀ x : ℝ, 0 < x → x < delta → A * x ^ beta ≤ G x)
    (hG_upper :
      ∀ x : ℝ, 0 < x → x < delta → G x ≤ B * x ^ beta)
    (j : ℕ) :
    Tendsto
      (fun a : ℕ =>
        ∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale beta a),
          boundedLemmaD2ForwardDifferenceRescaledKernel G beta j a y)
      atTop
      (nhds (boundedLemmaD2ForwardDifferenceLimitCoeff beta c j)) := by
  let μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
  let truncated : ℕ → ℝ → ℝ :=
    fun a y =>
      (Set.Iio (delta / boundedTailScale beta a)).indicator
        (fun z : ℝ =>
          boundedLemmaD2ForwardDifferenceRescaledKernel G beta j a z) y
  have hmeas :
      ∀ᶠ a in atTop,
        MeasureTheory.AEStronglyMeasurable (truncated a) μ := by
    filter_upwards with a
    dsimp [truncated, μ]
    exact
      (boundedLemmaD2ForwardDifferenceRescaledKernel_aestronglyMeasurable
        hG_measurable beta j a).indicator measurableSet_Iio
  have hbound :
      ∀ᶠ a in atTop,
        ∀ᵐ y ∂μ,
          ‖truncated a y‖ ≤
            boundedLemmaD2ForwardDifferenceLocalEnvelope beta A B j y := by
    simpa [truncated, μ] using
      boundedLemmaD2ForwardDifferenceRescaledKernel_eventually_indicator_norm_le_localEnvelope
        j tail.beta_pos hA_pos hB_nonneg hG_nonneg hG_le_one
        hG_lower hG_upper
  have hbound_integrable :
      MeasureTheory.Integrable
        (boundedLemmaD2ForwardDifferenceLocalEnvelope beta A B j) μ := by
    simpa [μ] using
      boundedLemmaD2ForwardDifferenceLocalEnvelope_integrable
        tail.beta_pos hA_pos j
  have hlim :
      ∀ᵐ y ∂μ,
        Tendsto (fun a : ℕ => truncated a y) atTop
          (nhds (boundedLemmaD2ForwardDifferenceLimitKernel beta c j y)) := by
    filter_upwards
      [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with y hy
    have hthreshold :
        ∀ᶠ a in atTop,
          y < delta / boundedTailScale beta a := by
      have hsmall :
          ∀ᶠ a in atTop,
            y * boundedTailScale beta a < delta :=
        (boundedTailScale_const_mul_tendsto_zero
          (y := y) tail.beta_pos).eventually
          (Iio_mem_nhds hdelta_pos)
      filter_upwards
        [hsmall, boundedTailScale_eventually_pos beta] with
          a hsmall_a hscale_pos
      rw [lt_div_iff₀ hscale_pos]
      simpa [mul_comm] using hsmall_a
    refine Tendsto.congr' ?_
      (boundedLemmaD2ForwardDifferenceRescaledKernel_tendsto_limit
        tail hy j)
    filter_upwards [hthreshold] with a hthreshold_a
    dsimp [truncated]
    rw [Set.indicator_of_mem (show y ∈ Set.Iio
      (delta / boundedTailScale beta a) from hthreshold_a)]
  have h :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := μ) (boundedLemmaD2ForwardDifferenceLocalEnvelope beta A B j)
      hmeas hbound hbound_integrable hlim
  refine Tendsto.congr' ?_
    (by simpa [μ, boundedLemmaD2ForwardDifferenceLimitCoeff] using h)
  filter_upwards with a
  symm
  exact boundedLemmaD2ForwardDifferenceRescaledIntegral_Ioo_eq_indicator_integral
    G beta j a (delta / boundedTailScale beta a)

/--
Near-zero fixed-rank adjacent-drop asymptotic from local CDF power bounds.
-/
theorem boundedLemmaD2IntegralTermBelow_forward_difference_asymptotic_of_local_cdf_power_bounds
    {G : ℝ → ℝ} {beta c A B : ℝ}
    (tail : BoundedTailCDFPowerSandwich G beta c)
    (hG_measurable : Measurable G)
    {delta : ℝ} (hdelta_pos : 0 < delta)
    (hA_pos : 0 < A) (hB_nonneg : 0 ≤ B)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_lower :
      ∀ x : ℝ, 0 < x → x < delta → A * x ^ beta ≤ G x)
    (hG_upper :
      ∀ x : ℝ, 0 < x → x < delta → G x ≤ B * x ^ beta)
    (j : ℕ)
    (h_integrable :
      ∀ᶠ a in atTop,
        MeasureTheory.IntegrableOn
          (boundedLemmaD2IntegralKernel G j a)
          (Set.Ioi (0 : ℝ))) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun a =>
        boundedLemmaD2IntegralTermBelow G j a delta -
          boundedLemmaD2IntegralTermBelow G j (a + 1) delta)
      (fun a =>
        boundedLemmaD2ForwardDifferenceLimitCoeff beta c j *
          (boundedTailScale beta a / (((a + 1 : ℕ) : ℝ)))) := by
  have hcoeff_ne :
      boundedLemmaD2ForwardDifferenceLimitCoeff beta c j ≠ 0 := by
    rw [boundedLemmaD2ForwardDifferenceLimitCoeff_eq_div
      tail.beta_pos tail.c_pos j]
    exact div_ne_zero
      (ne_of_gt (boundedLemmaD2LimitCoeff_pos tail.beta_pos tail.c_pos j))
      (ne_of_gt tail.beta_pos)
  have hgrowing :=
    boundedLemmaD2ForwardDifferenceGrowingRescaledIntegral_tendsto_of_local_cdf_power_bounds
      tail hG_measurable hdelta_pos hA_pos hB_nonneg hG_nonneg hG_le_one
      hG_lower hG_upper j
  have hratio :
      Tendsto
        (fun a : ℕ =>
          (∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale beta a),
            boundedLemmaD2ForwardDifferenceRescaledKernel G beta j a y) /
              boundedLemmaD2ForwardDifferenceLimitCoeff beta c j)
        atTop (nhds 1) := by
    have h := hgrowing.div_const
      (boundedLemmaD2ForwardDifferenceLimitCoeff beta c j)
    simpa [hcoeff_ne] using h
  rw [AppliedModelingLib.Math.AsymptoticEquivalent]
  refine Tendsto.congr' ?_ hratio
  filter_upwards
    [boundedLemmaD2IntegralTermBelow_forward_difference_eventually_changeOfVariables
      G beta j hdelta_pos.le h_integrable,
      boundedTailScale_eventually_ne_zero beta] with
      a hchange hscale_ne
  have hden_ne : (((a + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  rw [hchange]
  field_simp [hcoeff_ne, hscale_ne, hden_ne]

/--
Paper-scale near-zero fixed-rank adjacent-drop asymptotic from local CDF power
bounds.
-/
theorem boundedLemmaD2IntegralTermBelow_forward_difference_asymptotic_paper_scale_of_local_cdf_power_bounds
    {G : ℝ → ℝ} {beta c A B : ℝ}
    (tail : BoundedTailCDFPowerSandwich G beta c)
    (hG_measurable : Measurable G)
    {delta : ℝ} (hdelta_pos : 0 < delta)
    (hA_pos : 0 < A) (hB_nonneg : 0 ≤ B)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_lower :
      ∀ x : ℝ, 0 < x → x < delta → A * x ^ beta ≤ G x)
    (hG_upper :
      ∀ x : ℝ, 0 < x → x < delta → G x ≤ B * x ^ beta)
    (j : ℕ)
    (h_integrable :
      ∀ᶠ a in atTop,
        MeasureTheory.IntegrableOn
          (boundedLemmaD2IntegralKernel G j a)
          (Set.Ioi (0 : ℝ))) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun a =>
        boundedLemmaD2IntegralTermBelow G j a delta -
          boundedLemmaD2IntegralTermBelow G j (a + 1) delta)
      (fun a =>
        (boundedLemmaD2LimitCoeff beta c j / beta) *
          boundedPowerMarginalScale beta a) := by
  have hnear :=
    boundedLemmaD2IntegralTermBelow_forward_difference_asymptotic_of_local_cdf_power_bounds
      tail hG_measurable hdelta_pos hA_pos hB_nonneg hG_nonneg hG_le_one
      hG_lower hG_upper j h_integrable
  have hcoeff_eq :
      boundedLemmaD2ForwardDifferenceLimitCoeff beta c j =
        boundedLemmaD2LimitCoeff beta c j / beta :=
    boundedLemmaD2ForwardDifferenceLimitCoeff_eq_div
      tail.beta_pos tail.c_pos j
  have hcoeff_target_ne :
      boundedLemmaD2LimitCoeff beta c j / beta ≠ 0 := by
    exact div_ne_zero
      (ne_of_gt (boundedLemmaD2LimitCoeff_pos tail.beta_pos tail.c_pos j))
      (ne_of_gt tail.beta_pos)
  have hscale := boundedTailScale_div_succ_ratio_tendsto_one tail.beta_pos
  rw [AppliedModelingLib.Math.AsymptoticEquivalent] at hnear ⊢
  have hprod := hnear.mul hscale
  refine Tendsto.congr' ?_ (by simpa using hprod)
  filter_upwards [boundedTailScale_eventually_ne_zero beta] with a htail_ne
  have hden_ne : (((a + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have htail_div_ne :
      boundedTailScale beta a / (((a + 1 : ℕ) : ℝ)) ≠ 0 :=
    div_ne_zero htail_ne hden_ne
  have hpower_ne : boundedPowerMarginalScale beta a ≠ 0 :=
    (boundedPowerMarginalScale_pos beta a).ne'
  rw [hcoeff_eq]
  field_simp [hcoeff_target_ne, htail_div_ne, hpower_ne]

/--
Full fixed-rank adjacent-drop asymptotic for the Lemma D.2 source integral
from the paper's near-zero power bounds and bounded-support geometric tail.
-/
theorem boundedLemmaD2IntegralTerm_forward_difference_asymptotic_paper_scale_of_local_cdf_power_bounds_and_geometric_tail
    {G : ℝ → ℝ} {beta c A B delta M p : ℝ}
    (tail : BoundedTailCDFPowerSandwich G beta c)
    (hG_measurable : Measurable G)
    (hdelta_pos : 0 < delta) (hdeltaM : delta ≤ M)
    (hA_pos : 0 < A) (hB_nonneg : 0 ≤ B)
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    (hp_le_G_on_tail : ∀ x : ℝ, delta < x → p ≤ G x)
    (hG_lower :
      ∀ x : ℝ, 0 < x → x < delta → A * x ^ beta ≤ G x)
    (hG_upper :
      ∀ x : ℝ, 0 < x → x < delta → G x ≤ B * x ^ beta)
    (j : ℕ) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun a =>
        boundedLemmaD2IntegralTerm G j a -
          boundedLemmaD2IntegralTerm G j (a + 1))
      (fun a =>
        (boundedLemmaD2LimitCoeff beta c j / beta) *
          boundedPowerMarginalScale beta a) := by
  have h_integrable :
      ∀ᶠ a in atTop,
        MeasureTheory.IntegrableOn
          (boundedLemmaD2IntegralKernel G j a)
          (Set.Ioi (0 : ℝ)) :=
    boundedLemmaD2IntegralKernel_eventually_integrableOn_of_bounded_support
      hG_measurable M hG_nonneg hG_le_one hG_eq_one_of_support j
  have hbelow :=
    boundedLemmaD2IntegralTermBelow_forward_difference_asymptotic_paper_scale_of_local_cdf_power_bounds
      tail hG_measurable hdelta_pos hA_pos hB_nonneg hG_nonneg hG_le_one
      hG_lower hG_upper j h_integrable
  have habove :=
    boundedLemmaD2IntegralTermAbove_forward_difference_negligible_powerMarginalScale_of_geometric_support_bound
      hG_measurable tail.beta_pos hdelta_pos.le hdeltaM hp_pos hp_lt_one
      hG_nonneg hG_le_one hG_eq_one_of_support hp_le_G_on_tail j
  have hcoeff_ne :
      boundedLemmaD2LimitCoeff beta c j / beta ≠ 0 := by
    exact div_ne_zero
      (ne_of_gt (boundedLemmaD2LimitCoeff_pos tail.beta_pos tail.c_pos j))
      (ne_of_gt tail.beta_pos)
  have habove_coeff :
      Tendsto
        (fun a : ℕ =>
          (boundedLemmaD2IntegralTermAbove G j a delta -
            boundedLemmaD2IntegralTermAbove G j (a + 1) delta) /
            ((boundedLemmaD2LimitCoeff beta c j / beta) *
              boundedPowerMarginalScale beta a))
        atTop (nhds 0) := by
    have h := habove.div_const (boundedLemmaD2LimitCoeff beta c j / beta)
    refine Tendsto.congr' ?_ (by simpa [hcoeff_ne] using h)
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with a _ha
    have hscale_ne : boundedPowerMarginalScale beta a ≠ 0 :=
      (boundedPowerMarginalScale_pos beta a).ne'
    field_simp [hcoeff_ne, hscale_ne]
  rw [AppliedModelingLib.Math.AsymptoticEquivalent] at hbelow ⊢
  have hsum := hbelow.add habove_coeff
  refine Tendsto.congr' ?_ (by simpa using hsum)
  have hsplit :=
    boundedLemmaD2IntegralTerm_eventually_split G j hdelta_pos.le
      h_integrable
  have hsplit_succ :
      ∀ᶠ a in atTop,
        boundedLemmaD2IntegralTerm G j (a + 1) =
          boundedLemmaD2IntegralTermBelow G j (a + 1) delta +
            boundedLemmaD2IntegralTermAbove G j (a + 1) delta :=
    (Filter.tendsto_add_atTop_nat 1).eventually hsplit
  filter_upwards
    [hsplit, hsplit_succ] with a hsplit_a hsplit_succ_a
  rw [hsplit_a, hsplit_succ_a]
  ring

/--
Local CDF power bounds give the below-`delta` source asymptotic through the
paper's growing near-zero rescaled integral.
-/
theorem boundedLemmaD2IntegralTermBelow_asymptotic_of_local_cdf_power_bounds
    {G : ℝ → ℝ} {beta c A B : ℝ}
    (tail : BoundedTailCDFPowerSandwich G beta c)
    (hG_measurable : Measurable G)
    {delta : ℝ} (hdelta_pos : 0 < delta)
    (hA_pos : 0 < A) (hB_nonneg : 0 ≤ B)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_lower :
      ∀ x : ℝ, 0 < x → x < delta → A * x ^ beta ≤ G x)
    (hG_upper :
      ∀ x : ℝ, 0 < x → x < delta → G x ≤ B * x ^ beta)
    (j : ℕ) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun a => boundedLemmaD2IntegralTermBelow G j a delta)
      (fun a => boundedLemmaD2LimitCoeff beta c j *
        boundedTailScale beta a) :=
  boundedLemmaD2IntegralTermBelow_asymptotic_of_growing_rescaled_integral
    tail.beta_pos tail.c_pos j hdelta_pos.le
    (boundedLemmaD2GrowingRescaledIntegral_tendsto_of_local_cdf_power_bounds
      tail hG_measurable hdelta_pos hA_pos hB_nonneg hG_nonneg hG_le_one
      hG_lower hG_upper j)

/--
Growing near-zero rescaled-integral convergence from full rescaled convergence
and convergence of the rescaled above-threshold tail to zero.
-/
theorem boundedLemmaD2GrowingRescaledIntegral_tendsto_of_full_and_tail
    {G : ℝ → ℝ} {beta c : ℝ} (j : ℕ) {delta : ℝ}
    (hdelta_nonneg : 0 ≤ delta)
    (h_integrable :
      ∀ᶠ a in atTop,
        MeasureTheory.IntegrableOn
          (fun y : ℝ => boundedLemmaD2RescaledKernel G beta j a y)
          (Set.Ioi (0 : ℝ)))
    (hfull :
      Tendsto
        (fun a : ℕ =>
          ∫ y in Set.Ioi (0 : ℝ),
            boundedLemmaD2RescaledKernel G beta j a y)
        atTop (nhds (boundedLemmaD2LimitCoeff beta c j)))
    (htail :
      Tendsto
        (fun a : ℕ =>
          ∫ y in Set.Ioi (delta / boundedTailScale beta a),
            boundedLemmaD2RescaledKernel G beta j a y)
        atTop (nhds 0)) :
    Tendsto
      (fun a : ℕ =>
        ∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale beta a),
          boundedLemmaD2RescaledKernel G beta j a y)
      atTop (nhds (boundedLemmaD2LimitCoeff beta c j)) := by
  have hdiff := hfull.sub htail
  refine Tendsto.congr' ?_ (by simpa using hdiff)
  filter_upwards
    [boundedLemmaD2RescaledIntegral_eventually_split
      G beta j hdelta_nonneg h_integrable] with a hsplit
  rw [hsplit]
  ring

/--
Growing near-zero rescaled-integral convergence from full rescaled convergence
and source-tail negligibility. The above-`delta` change of variables converts
the source tail divided by `a^(-1/beta)` into the rescaled tail integral.
-/
theorem boundedLemmaD2GrowingRescaledIntegral_tendsto_of_full_and_source_tail
    {G : ℝ → ℝ} {beta c : ℝ} (j : ℕ) {delta : ℝ}
    (hdelta_nonneg : 0 ≤ delta)
    (h_integrable :
      ∀ᶠ a in atTop,
        MeasureTheory.IntegrableOn
          (fun y : ℝ => boundedLemmaD2RescaledKernel G beta j a y)
          (Set.Ioi (0 : ℝ)))
    (hfull :
      Tendsto
        (fun a : ℕ =>
          ∫ y in Set.Ioi (0 : ℝ),
            boundedLemmaD2RescaledKernel G beta j a y)
        atTop (nhds (boundedLemmaD2LimitCoeff beta c j)))
    (htail_source :
      Tendsto
        (fun a : ℕ =>
          boundedLemmaD2IntegralTermAbove G j a delta /
            boundedTailScale beta a)
        atTop (nhds 0)) :
    Tendsto
      (fun a : ℕ =>
        ∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale beta a),
          boundedLemmaD2RescaledKernel G beta j a y)
      atTop (nhds (boundedLemmaD2LimitCoeff beta c j)) := by
  have htail_rescaled :
      Tendsto
        (fun a : ℕ =>
          ∫ y in Set.Ioi (delta / boundedTailScale beta a),
            boundedLemmaD2RescaledKernel G beta j a y)
        atTop (nhds 0) := by
    refine Tendsto.congr' ?_ htail_source
    filter_upwards
      [boundedLemmaD2IntegralTermAbove_eventually_changeOfVariables
        G beta j delta,
        boundedTailScale_eventually_ne_zero beta] with a hchange hscale_ne
    rw [hchange]
    field_simp [hscale_ne]
  exact boundedLemmaD2GrowingRescaledIntegral_tendsto_of_full_and_tail
    j hdelta_nonneg h_integrable hfull htail_rescaled

/-- The source integral term indexed by the paper's `(i,j)` finite sum. -/
noncomputable def boundedLemmaD2IndexedIntegralTerm
    (G : ℝ → ℝ) {k : ℕ}
    (p : BoundedLemmaD2Index k) (a : ℕ) : ℝ := boundedLemmaD2IntegralTerm G p.2.val a

/--
The finite double sum of Lemma D.2-style rank terms that gives the bounded
top-`k` loss `M k - h(a)` after the reflection identity.
-/
noncomputable def boundedLemmaD2TopKLoss
    (k : ℕ) (term : BoundedLemmaD2Index k → ℕ → ℝ) (a : ℕ) : ℝ := ∑ p : BoundedLemmaD2Index k, term p a

/-- The `Sigma` index is exactly the paper's nested `i`/`j` finite sum. -/
theorem boundedLemmaD2TopKLoss_eq_nested_sum
    (k : ℕ) (term : BoundedLemmaD2Index k → ℕ → ℝ) (a : ℕ) :
    boundedLemmaD2TopKLoss k term a =
      ∑ i : Fin k, ∑ j : Fin (i.val + 1), term ⟨i, j⟩ a := by
  rw [boundedLemmaD2TopKLoss, Fintype.sum_sigma]

/--
Finite-sum adjacent-drop transfer for the Lemma D.2 top-`k` loss.
-/
theorem boundedLemmaD2TopKLoss_forward_difference_asymptotic
    {k : ℕ} (term : BoundedLemmaD2Index k → ℕ → ℝ)
    (coeff : BoundedLemmaD2Index k → ℝ) (scale : ℕ → ℝ)
    (hcoeff_ne : ∀ p, coeff p ≠ 0)
    (htotal_ne : (∑ p : BoundedLemmaD2Index k, coeff p) ≠ 0)
    (hscale_ne : ∀ᶠ a in atTop, scale a ≠ 0)
    (hterm :
      ∀ p : BoundedLemmaD2Index k,
        AppliedModelingLib.Math.AsymptoticEquivalent
          (fun a => term p a - term p (a + 1))
          (fun a => coeff p * scale a)) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun a =>
        boundedLemmaD2TopKLoss k term a -
          boundedLemmaD2TopKLoss k term (a + 1))
      (fun a =>
        (∑ p : BoundedLemmaD2Index k, coeff p) * scale a) := by
  let termDrop : BoundedLemmaD2Index k → ℕ → ℝ :=
    fun p a => term p a - term p (a + 1)
  have hsum :=
    AppliedModelingLib.Math.finite_sum_asymptoticEquivalent_common_scale
      termDrop coeff scale hcoeff_ne htotal_ne hscale_ne hterm
  refine AppliedModelingLib.Math.AsymptoticEquivalent.congr_left_eventually ?_ hsum
  filter_upwards with a
  unfold boundedLemmaD2TopKLoss termDrop
  rw [Finset.sum_sub_distrib]

/--
Top-`k` Lemma D.2 source-loss adjacent-drop asymptotic from local CDF power
bounds and bounded-support geometric tail.
-/
theorem boundedLemmaD2TopKLoss_forward_difference_asymptotic_of_local_cdf_power_bounds_and_geometric_tail
    {G : ℝ → ℝ} {beta c A B delta M p0 : ℝ} {k : ℕ}
    (tail : BoundedTailCDFPowerSandwich G beta c)
    (hG_measurable : Measurable G)
    (hk_pos : 0 < k)
    (hdelta_pos : 0 < delta) (hdeltaM : delta ≤ M)
    (hA_pos : 0 < A) (hB_nonneg : 0 ≤ B)
    (hp_pos : 0 < p0) (hp_lt_one : p0 < 1)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    (hp_le_G_on_tail : ∀ x : ℝ, delta < x → p0 ≤ G x)
    (hG_lower :
      ∀ x : ℝ, 0 < x → x < delta → A * x ^ beta ≤ G x)
    (hG_upper :
      ∀ x : ℝ, 0 < x → x < delta → G x ≤ B * x ^ beta) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun a =>
        boundedLemmaD2TopKLoss k (boundedLemmaD2IndexedIntegralTerm G) a -
          boundedLemmaD2TopKLoss k (boundedLemmaD2IndexedIntegralTerm G)
            (a + 1))
      (fun a =>
        (∑ p : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c p.2.val / beta) *
          boundedPowerMarginalScale beta a) := by
  let coeff : BoundedLemmaD2Index k → ℝ :=
    fun p => boundedLemmaD2LimitCoeff beta c p.2.val / beta
  have hcoeff_ne : ∀ p : BoundedLemmaD2Index k, coeff p ≠ 0 := by
    intro p
    exact div_ne_zero
      (ne_of_gt (boundedLemmaD2LimitCoeff_pos tail.beta_pos tail.c_pos p.2.val))
      (ne_of_gt tail.beta_pos)
  have htotal_pos : 0 < ∑ p : BoundedLemmaD2Index k, coeff p := by
    haveI : Nonempty (BoundedLemmaD2Index k) := by
      refine ⟨⟨⟨0, hk_pos⟩, ⟨0, by simp⟩⟩⟩
    exact Finset.sum_pos
      (fun p _ =>
        div_pos
          (boundedLemmaD2LimitCoeff_pos tail.beta_pos tail.c_pos p.2.val)
          tail.beta_pos)
      Finset.univ_nonempty
  have hterm :
      ∀ q : BoundedLemmaD2Index k,
        AppliedModelingLib.Math.AsymptoticEquivalent
          (fun a =>
            boundedLemmaD2IndexedIntegralTerm G q a -
              boundedLemmaD2IndexedIntegralTerm G q (a + 1))
          (fun a => coeff q * boundedPowerMarginalScale beta a) := by
    intro q
    dsimp [boundedLemmaD2IndexedIntegralTerm, coeff]
    exact
      boundedLemmaD2IntegralTerm_forward_difference_asymptotic_paper_scale_of_local_cdf_power_bounds_and_geometric_tail
        tail hG_measurable hdelta_pos hdeltaM hA_pos hB_nonneg hp_pos
        hp_lt_one hG_nonneg hG_le_one hG_eq_one_of_support
        hp_le_G_on_tail hG_lower hG_upper q.2.val
  simpa [coeff] using
    boundedLemmaD2TopKLoss_forward_difference_asymptotic
      (k := k)
      (term := boundedLemmaD2IndexedIntegralTerm G)
      (coeff := coeff)
      (scale := boundedPowerMarginalScale beta)
      hcoeff_ne (ne_of_gt htotal_pos)
      (by
        filter_upwards with a
        exact (boundedPowerMarginalScale_pos beta a).ne')
      hterm

/--
Top-`k` Lemma D.2 source-loss adjacent-drop asymptotic from the source-facing
bounded-tail conditions: a CDF power sandwich near zero, monotonicity, CDF
range, and bounded support.
-/
theorem boundedLemmaD2TopKLoss_forward_difference_asymptotic_of_cdf_power_sandwich_monotone_bounded_support
    {G : ℝ → ℝ} {beta c M : ℝ} {k : ℕ}
    (tail : BoundedTailCDFPowerSandwich G beta c)
    (hG_measurable : Measurable G)
    (hk_pos : 0 < k)
    (hM_pos : 0 < M)
    (hG_mono : Monotone G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun a =>
        boundedLemmaD2TopKLoss k (boundedLemmaD2IndexedIntegralTerm G) a -
          boundedLemmaD2TopKLoss k (boundedLemmaD2IndexedIntegralTerm G)
            (a + 1))
      (fun a =>
        ((∑ p : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c p.2.val) / beta) *
          boundedPowerMarginalScale beta a) := by
  let hlocal := tail.exists_local_cdf_power_bounds
  let delta₀ : ℝ := Classical.choose hlocal
  let hlocal_delta := Classical.choose_spec hlocal
  let A : ℝ := Classical.choose hlocal_delta
  let hlocal_A := Classical.choose_spec hlocal_delta
  let B : ℝ := Classical.choose hlocal_A
  have hlocal_spec := Classical.choose_spec hlocal_A
  rcases hlocal_spec with
    ⟨hdelta₀_pos, hA_pos, hB_nonneg, hG_lower₀, hG_upper₀⟩
  let delta : ℝ := min delta₀ M / 2
  let probe : ℝ := delta / 2
  let p0 : ℝ := (A * probe ^ beta) / 2
  have hmin_pos : 0 < min delta₀ M := lt_min hdelta₀_pos hM_pos
  have hdelta_pos : 0 < delta := by
    dsimp [delta]
    positivity
  have hdelta_lt_delta₀ : delta < delta₀ := by
    have hmin_le : min delta₀ M ≤ delta₀ := min_le_left _ _
    dsimp [delta]
    linarith
  have hdeltaM : delta ≤ M := by
    have hmin_le : min delta₀ M ≤ M := min_le_right _ _
    dsimp [delta]
    linarith
  have hprobe_pos : 0 < probe := by
    dsimp [probe]
    positivity
  have hprobe_lt_delta : probe < delta := by
    dsimp [probe]
    linarith
  have hprobe_lt_delta₀ : probe < delta₀ :=
    lt_trans hprobe_lt_delta hdelta_lt_delta₀
  have hprobe_lower : A * probe ^ beta ≤ G probe :=
    hG_lower₀ probe hprobe_pos hprobe_lt_delta₀
  have hAprobe_pos : 0 < A * probe ^ beta :=
    mul_pos hA_pos (Real.rpow_pos_of_pos hprobe_pos beta)
  have hp_pos : 0 < p0 := by
    dsimp [p0]
    positivity
  have hp_le_Aprobe : p0 ≤ A * probe ^ beta := by
    dsimp [p0]
    linarith
  have hp_lt_one : p0 < 1 := by
    have hAprobe_le_one : A * probe ^ beta ≤ 1 :=
      le_trans hprobe_lower (hG_le_one probe)
    dsimp [p0]
    linarith
  have hG_lower :
      ∀ x : ℝ, 0 < x → x < delta → A * x ^ beta ≤ G x := by
    intro x hx_pos hx_lt
    exact hG_lower₀ x hx_pos (lt_trans hx_lt hdelta_lt_delta₀)
  have hG_upper :
      ∀ x : ℝ, 0 < x → x < delta → G x ≤ B * x ^ beta := by
    intro x hx_pos hx_lt
    exact hG_upper₀ x hx_pos (lt_trans hx_lt hdelta_lt_delta₀)
  have hp_le_G_on_tail : ∀ x : ℝ, delta < x → p0 ≤ G x := by
    intro x hx
    have hprobe_le_x : probe ≤ x :=
      le_of_lt (lt_trans hprobe_lt_delta hx)
    exact le_trans hp_le_Aprobe
      (le_trans hprobe_lower (hG_mono hprobe_le_x))
  have hdrop :=
    boundedLemmaD2TopKLoss_forward_difference_asymptotic_of_local_cdf_power_bounds_and_geometric_tail
      tail hG_measurable hk_pos hdelta_pos hdeltaM hA_pos hB_nonneg
      hp_pos hp_lt_one hG_nonneg hG_le_one hG_eq_one_of_support
      hp_le_G_on_tail hG_lower hG_upper
  exact AppliedModelingLib.Math.AsymptoticEquivalent.congr_right_eventually
    (by
      filter_upwards with a
      rw [Finset.sum_div])
    hdrop

/--
If an order-statistic source has endpoint loss eventually equal to the Lemma
D.2 finite integral sum, then the source forward marginal has the paper's
bounded power scale. This is the bridge that replaces an external
`scaled_drop` hypothesis by the proved adjacent-difference asymptotic.
-/
theorem boundedOrderStatistic_forward_marginal_asymptotic_of_eventual_loss_eq_topKLoss_and_cdf_power_sandwich_monotone_bounded_support
    {μ : ℕ → ℕ → ℝ} {G : ℝ → ℝ} {beta c M M₀ : ℝ} {k : ℕ}
    (h_loss_eq :
      ∀ᶠ a in atTop,
        (k : ℝ) * M - orderStatisticTopKSumFromMean μ k a =
          boundedLemmaD2TopKLoss k (boundedLemmaD2IndexedIntegralTerm G) a)
    (tail : BoundedTailCDFPowerSandwich G beta c)
    (hG_measurable : Measurable G)
    (hk_pos : 0 < k)
    (hM₀_pos : 0 < M₀)
    (hG_mono : Monotone G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M₀ ≤ x → G x = 1) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun a =>
        orderStatisticTopKSumFromMean μ k (a + 1) -
          orderStatisticTopKSumFromMean μ k a)
      (fun a =>
        ((∑ p : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c p.2.val) / beta) *
          boundedPowerMarginalScale beta a) := by
  have h_loss_eq_succ :
      ∀ᶠ a in atTop,
        (k : ℝ) * M - orderStatisticTopKSumFromMean μ k (a + 1) =
          boundedLemmaD2TopKLoss k (boundedLemmaD2IndexedIntegralTerm G)
            (a + 1) := by
    rcases Filter.eventually_atTop.1 h_loss_eq with ⟨N, hN⟩
    exact Filter.eventually_atTop.2
      ⟨N, fun a ha =>
        hN (a + 1) (Nat.le_trans ha (Nat.le_succ a))⟩
  have htop_drop :=
    boundedLemmaD2TopKLoss_forward_difference_asymptotic_of_cdf_power_sandwich_monotone_bounded_support
      tail hG_measurable hk_pos hM₀_pos hG_mono hG_nonneg hG_le_one
      hG_eq_one_of_support
  have hloss_drop :
      AppliedModelingLib.Math.AsymptoticEquivalent
        (fun a : ℕ =>
          ((k : ℝ) * M - orderStatisticTopKSumFromMean μ k a) -
            ((k : ℝ) * M - orderStatisticTopKSumFromMean μ k (a + 1)))
        (fun a =>
          ((∑ p : BoundedLemmaD2Index k,
            boundedLemmaD2LimitCoeff beta c p.2.val) / beta) *
            boundedPowerMarginalScale beta a) :=
    AppliedModelingLib.Math.AsymptoticEquivalent.congr_left_eventually
      (by
        filter_upwards [h_loss_eq, h_loss_eq_succ] with a ha ha_succ
        rw [ha, ha_succ])
      htop_drop
  exact bounded_source_forward_marginal_asymptotic_of_loss_adjacent_drop
    (A := (k : ℝ) * M) hloss_drop

/--
Reflection algebra behind equations (91)-(95): if each original upper
order-statistic mean equals `M` minus the corresponding reflected nested
integral sum, then the top-`k` loss is exactly the nested reflected sum.
-/
theorem boundedLemmaD2_reflection_loss_eq_nested_sum
    (M : ℝ) {k : ℕ}
    (sourceMean : Fin k → ℝ)
    (term : BoundedLemmaD2Index k → ℝ)
    (hsource :
      ∀ i : Fin k,
        sourceMean i =
          M - ∑ j : Fin (i.val + 1), term ⟨i, j⟩) :
    (k : ℝ) * M - ∑ i : Fin k, sourceMean i =
      ∑ i : Fin k, ∑ j : Fin (i.val + 1), term ⟨i, j⟩ := by
  simpa [AppliedModelingLib.Probability.topKEndpointLoss,
    AppliedModelingLib.Probability.reflectedTopKMeanSum] using
    AppliedModelingLib.Probability.topKEndpointLoss_eq_reflectedTopKMeanSum
      M sourceMean
      (fun i : Fin k => ∑ j : Fin (i.val + 1), term ⟨i, j⟩)
      hsource

/--
Sequence form of the reflection algebra, targeting the internal
`boundedLemmaD2TopKLoss` finite-sum object.
-/
theorem boundedLemmaD2_reflection_loss_eq_topKLoss
    (M : ℝ) {k : ℕ}
    (sourceMean : Fin k → ℕ → ℝ)
    (term : BoundedLemmaD2Index k → ℕ → ℝ)
    (hsource :
      ∀ a (i : Fin k),
        sourceMean i a =
          M - ∑ j : Fin (i.val + 1), term ⟨i, j⟩ a)
    (a : ℕ) :
    (k : ℝ) * M - ∑ i : Fin k, sourceMean i a =
      boundedLemmaD2TopKLoss k term a := by
  rw [boundedLemmaD2TopKLoss_eq_nested_sum]
  simpa [AppliedModelingLib.Probability.topKEndpointLossSeq,
    AppliedModelingLib.Probability.reflectedTopKMeanSumSeq,
    AppliedModelingLib.Probability.topKEndpointLoss,
    AppliedModelingLib.Probability.reflectedTopKMeanSum] using
    AppliedModelingLib.Probability.topKEndpointLossSeq_eq_reflectedTopKMeanSumSeq
      M sourceMean
      (fun i a => ∑ j : Fin (i.val + 1), term ⟨i, j⟩ a)
      hsource a

/--
Certificate for the bounded branch's Lemma D.2 outputs, separated from the
hard analytic integral proof.

Each fixed `(i,j)` term must be asymptotic to a positive coefficient times the
paper scale `a^(-1 / beta)`. The `totalCoeff_pos` field records the source
fact that summing the finitely many positive constants still gives a positive
constant `B`.
-/
structure BoundedLemmaD2FiniteSumCertificate
    (beta : ℝ) (k : ℕ)
    (term : BoundedLemmaD2Index k → ℕ → ℝ) where
  /-- Positive coefficient for each fixed Lemma D.2 rank/index term. -/
  coeff : BoundedLemmaD2Index k → ℝ
  coeff_pos : ∀ p, 0 < coeff p
  totalCoeff_pos : 0 < ∑ p : BoundedLemmaD2Index k, coeff p
  term_asymptotic :
    ∀ p,
      AppliedModelingLib.Math.AsymptoticEquivalent (term p)
        (fun a => coeff p * boundedTailScale beta a)

namespace BoundedLemmaD2FiniteSumCertificate

/--
Each fixed Lemma D.2 term is eventually trapped between the standard
`(1±ε)` multiples of its asymptotic equivalent.
-/
theorem eventually_term_sandwich
    {beta : ℝ} {k : ℕ}
    {term : BoundedLemmaD2Index k → ℕ → ℝ}
    (C : BoundedLemmaD2FiniteSumCertificate beta k term)
    (p : BoundedLemmaD2Index k)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ a in atTop,
      (1 - ε) * (C.coeff p * boundedTailScale beta a) ≤ term p a ∧
        term p a ≤
          (1 + ε) * (C.coeff p * boundedTailScale beta a) := by
  refine
    AppliedModelingLib.Math.AsymptoticEquivalent.eventually_sandwich_of_pos_right
      (C.term_asymptotic p) ?_ hε
  filter_upwards [boundedTailScale_eventually_pos beta] with a hscale
  exact mul_pos (C.coeff_pos p) hscale

/--
Uniform finite-index version of `eventually_term_sandwich`, useful when the
source proof needs one threshold that works for every fixed `(i,j)` term.
-/
theorem eventually_all_term_sandwich
    {beta : ℝ} {k : ℕ}
    {term : BoundedLemmaD2Index k → ℕ → ℝ}
    (C : BoundedLemmaD2FiniteSumCertificate beta k term)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ a in atTop,
      ∀ p : BoundedLemmaD2Index k,
        (1 - ε) * (C.coeff p * boundedTailScale beta a) ≤ term p a ∧
          term p a ≤
            (1 + ε) * (C.coeff p * boundedTailScale beta a) := by
  classical
  refine eventually_all.2 ?_
  intro p
  exact C.eventually_term_sandwich p hε

end BoundedLemmaD2FiniteSumCertificate

/--
Source-facing certificate for the actual bounded Lemma D.2 integral terms.

Supplying this certificate is precisely the remaining analytic work in the
bounded branch: prove the reflected CDF integral term has the paper's
`a^(-1/β)` asymptotic for each fixed source `(i,j)` index.
-/
abbrev BoundedLemmaD2IntegralAsymptoticCertificate
    (beta : ℝ) (k : ℕ) (G : ℝ → ℝ) :=
  BoundedLemmaD2FiniteSumCertificate beta k
    (boundedLemmaD2IndexedIntegralTerm G)

/--
Sharper source-facing certificate for the actual Lemma D.2 integral terms:
the coefficient for each fixed source rank/index is the gamma-integral
coefficient of the limiting kernel.
-/
structure BoundedLemmaD2LimitIntegralAsymptoticCertificate
    (beta c : ℝ) (k : ℕ) (G : ℝ → ℝ) where
  beta_pos : 0 < beta
  c_pos : 0 < c
  k_pos : 0 < k
  term_asymptotic :
    ∀ p : BoundedLemmaD2Index k,
      AppliedModelingLib.Math.AsymptoticEquivalent
        (boundedLemmaD2IndexedIntegralTerm G p)
        (fun a =>
          boundedLemmaD2LimitCoeff beta c p.2.val *
            boundedTailScale beta a)

namespace BoundedLemmaD2LimitIntegralAsymptoticCertificate

/--
For `k > 0`, the exact limiting coefficients give a standard finite-sum
certificate for the actual source integral terms.
-/
noncomputable def toIntegralAsymptoticCertificate
    {beta c : ℝ} {k : ℕ} {G : ℝ → ℝ}
    (C : BoundedLemmaD2LimitIntegralAsymptoticCertificate beta c k G) :
    BoundedLemmaD2IntegralAsymptoticCertificate beta k G := by
  haveI : Nonempty (BoundedLemmaD2Index k) := by
    refine ⟨⟨⟨0, C.k_pos⟩, ⟨0, by simp⟩⟩⟩
  refine
    { coeff := fun p => boundedLemmaD2LimitCoeff beta c p.2.val
      coeff_pos := ?_
      totalCoeff_pos := ?_
      term_asymptotic := C.term_asymptotic }
  · intro p
    exact boundedLemmaD2LimitCoeff_pos C.beta_pos C.c_pos p.2.val
  · exact Finset.sum_pos
      (fun p _ =>
        boundedLemmaD2LimitCoeff_pos C.beta_pos C.c_pos p.2.val)
      Finset.univ_nonempty

end BoundedLemmaD2LimitIntegralAsymptoticCertificate

/--
Per-rank dominated-convergence certificate for Lemma D.2.

This records the two analytic facts not supplied by the near-zero CDF
sandwich alone: the source change of variables and a single integrable
dominating envelope for the rescaled kernels. The pointwise kernel limit is
proved from `tail`.
-/
structure BoundedLemmaD2DominatedKernelCertificate
    (beta c : ℝ) (G : ℝ → ℝ) (j : ℕ) where
  tail : BoundedTailCDFPowerSandwich G beta c
  change_of_variables :
    ∀ᶠ a in atTop,
      boundedLemmaD2IntegralTerm G j a =
        boundedTailScale beta a *
          ∫ y in Set.Ioi (0 : ℝ),
            boundedLemmaD2RescaledKernel G beta j a y
  kernel_measurable :
    ∀ᶠ a in atTop,
      MeasureTheory.AEStronglyMeasurable
        (fun y : ℝ => boundedLemmaD2RescaledKernel G beta j a y)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
  bound : ℝ → ℝ
  bound_integrable :
    MeasureTheory.Integrable bound
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
  kernel_bound :
    ∀ᶠ a in atTop,
      ∀ᵐ y ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
        ‖boundedLemmaD2RescaledKernel G beta j a y‖ ≤ bound y

namespace BoundedLemmaD2DominatedKernelCertificate

/--
Build the per-rank dominated-convergence certificate from measurability of the
reflected CDF and an integrable envelope. The source change of variables is
proved internally by `boundedLemmaD2IntegralTerm_eventually_changeOfVariables`.
-/
noncomputable def ofMeasurableBound
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ}
    (tail : BoundedTailCDFPowerSandwich G beta c)
    (hG : Measurable G)
    (bound : ℝ → ℝ)
    (bound_integrable :
      MeasureTheory.Integrable bound
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (kernel_bound :
      ∀ᶠ a in atTop,
        ∀ᵐ y ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
          ‖boundedLemmaD2RescaledKernel G beta j a y‖ ≤ bound y) :
    BoundedLemmaD2DominatedKernelCertificate beta c G j where
  tail := tail
  change_of_variables :=
    boundedLemmaD2IntegralTerm_eventually_changeOfVariables G beta j
  kernel_measurable := by
    filter_upwards with a
    exact boundedLemmaD2RescaledKernel_aestronglyMeasurable hG beta j a
  bound := bound
  bound_integrable := bound_integrable
  kernel_bound := kernel_bound

/--
Dominated convergence for the rescaled Lemma D.2 kernels.
-/
theorem rescaled_integral_tendsto
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ}
    (C : BoundedLemmaD2DominatedKernelCertificate beta c G j) :
    Tendsto
      (fun a : ℕ =>
        ∫ y in Set.Ioi (0 : ℝ),
          boundedLemmaD2RescaledKernel G beta j a y)
      atTop (nhds (boundedLemmaD2LimitCoeff beta c j)) := by
  have hlim :
      ∀ᵐ y ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
        Tendsto
          (fun a : ℕ => boundedLemmaD2RescaledKernel G beta j a y)
          atTop (nhds (boundedLemmaD2LimitKernel beta c j y)) := by
    filter_upwards
      [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with y hy
    exact C.tail.rescaled_kernel_tendsto_limit hy j
  have h :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
      C.bound C.kernel_measurable C.kernel_bound C.bound_integrable hlim
  simpa [boundedLemmaD2LimitCoeff] using h

/--
The dominated-convergence certificate also supplies eventual integrability of
the rescaled kernels on `(0,∞)`.
-/
theorem eventually_rescaledKernel_integrableOn
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ}
    (C : BoundedLemmaD2DominatedKernelCertificate beta c G j) :
    ∀ᶠ a in atTop,
      MeasureTheory.IntegrableOn
        (fun y : ℝ => boundedLemmaD2RescaledKernel G beta j a y)
        (Set.Ioi (0 : ℝ)) := by
  filter_upwards [C.kernel_measurable, C.kernel_bound] with
    a hmeas hbound
  exact MeasureTheory.Integrable.mono'
    C.bound_integrable hmeas hbound

/--
Direct dominated-convergence proof of the paper's growing near-zero rescaled
integral. The truncation interval expands to `(0,∞)` because
`delta / a^(-1/beta) → ∞`.
-/
theorem growing_rescaled_integral_tendsto
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ}
    (C : BoundedLemmaD2DominatedKernelCertificate beta c G j)
    {delta : ℝ} (hdelta_pos : 0 < delta) :
    Tendsto
      (fun a : ℕ =>
        ∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale beta a),
          boundedLemmaD2RescaledKernel G beta j a y)
      atTop (nhds (boundedLemmaD2LimitCoeff beta c j)) := by
  let μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
  let truncated : ℕ → ℝ → ℝ :=
    fun a y =>
      (Set.Iio (delta / boundedTailScale beta a)).indicator
        (fun z : ℝ => boundedLemmaD2RescaledKernel G beta j a z) y
  have hmeas :
      ∀ᶠ a in atTop,
        MeasureTheory.AEStronglyMeasurable (truncated a) μ := by
    filter_upwards [C.kernel_measurable] with a hkernel_meas
    dsimp [truncated, μ] at hkernel_meas ⊢
    exact hkernel_meas.indicator measurableSet_Iio
  have hbound :
      ∀ᶠ a in atTop,
        ∀ᵐ y ∂μ, ‖truncated a y‖ ≤ C.bound y := by
    filter_upwards [C.kernel_bound] with a hkernel_bound
    filter_upwards [hkernel_bound] with y hbound_y
    dsimp [truncated]
    by_cases hy :
        y ∈ Set.Iio (delta / boundedTailScale beta a)
    · simpa [Set.indicator_of_mem hy] using hbound_y
    · have hbound_nonneg : 0 ≤ C.bound y :=
        (norm_nonneg
          (boundedLemmaD2RescaledKernel G beta j a y)).trans hbound_y
      rw [Set.indicator_of_notMem hy]
      simpa using hbound_nonneg
  have hlim :
      ∀ᵐ y ∂μ,
        Tendsto (fun a : ℕ => truncated a y) atTop
          (nhds (boundedLemmaD2LimitKernel beta c j y)) := by
    filter_upwards
      [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with y hy
    have hthreshold :
        ∀ᶠ a in atTop,
          y < delta / boundedTailScale beta a := by
      have hsmall :
          ∀ᶠ a in atTop,
            y * boundedTailScale beta a < delta :=
        (boundedTailScale_const_mul_tendsto_zero
          (y := y) C.tail.beta_pos).eventually
          (Iio_mem_nhds hdelta_pos)
      filter_upwards
        [hsmall, boundedTailScale_eventually_pos beta] with
          a hsmall_a hscale_pos
      rw [lt_div_iff₀ hscale_pos]
      simpa [mul_comm] using hsmall_a
    refine Tendsto.congr' ?_
      (C.tail.rescaled_kernel_tendsto_limit hy j)
    filter_upwards [hthreshold] with a hthreshold_a
    dsimp [truncated]
    rw [Set.indicator_of_mem (show y ∈ Set.Iio
      (delta / boundedTailScale beta a) from hthreshold_a)]
  have h :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := μ) C.bound hmeas hbound C.bound_integrable hlim
  refine Tendsto.congr' ?_ (by simpa [μ, boundedLemmaD2LimitCoeff] using h)
  filter_upwards with a
  symm
  exact boundedLemmaD2RescaledIntegral_Ioo_eq_indicator_integral
    G beta j a (delta / boundedTailScale beta a)

/--
The dominated-convergence certificate gives the below-`delta` source
asymptotic directly through the paper's growing near-zero rescaled integral.
-/
theorem integralTermBelow_asymptoticEquivalent
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ}
    (C : BoundedLemmaD2DominatedKernelCertificate beta c G j)
    {delta : ℝ} (hdelta_pos : 0 < delta) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun a => boundedLemmaD2IntegralTermBelow G j a delta)
      (fun a => boundedLemmaD2LimitCoeff beta c j *
        boundedTailScale beta a) :=
  boundedLemmaD2IntegralTermBelow_asymptotic_of_growing_rescaled_integral
    C.tail.beta_pos C.tail.c_pos j hdelta_pos.le
    (C.growing_rescaled_integral_tendsto hdelta_pos)

/--
The dominated-convergence certificate plus source-tail negligibility gives the
paper's growing near-zero rescaled integral convergence.
-/
theorem growing_rescaled_integral_tendsto_of_source_tail
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ}
    (C : BoundedLemmaD2DominatedKernelCertificate beta c G j)
    {delta : ℝ} (hdelta_nonneg : 0 ≤ delta)
    (htail_source :
      Tendsto
        (fun a : ℕ =>
          boundedLemmaD2IntegralTermAbove G j a delta /
            boundedTailScale beta a)
        atTop (nhds 0)) :
    Tendsto
      (fun a : ℕ =>
        ∫ y in Set.Ioo (0 : ℝ) (delta / boundedTailScale beta a),
          boundedLemmaD2RescaledKernel G beta j a y)
      atTop (nhds (boundedLemmaD2LimitCoeff beta c j)) :=
  boundedLemmaD2GrowingRescaledIntegral_tendsto_of_full_and_source_tail
    j hdelta_nonneg C.eventually_rescaledKernel_integrableOn
    C.rescaled_integral_tendsto htail_source

/--
The dominated-convergence certificate plus source-tail negligibility gives the
below-`delta` source asymptotic by the paper's growing-interval route.
-/
theorem integralTermBelow_asymptoticEquivalent_of_source_tail
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ}
    (C : BoundedLemmaD2DominatedKernelCertificate beta c G j)
    {delta : ℝ} (hdelta_nonneg : 0 ≤ delta)
    (htail_source :
      Tendsto
        (fun a : ℕ =>
          boundedLemmaD2IntegralTermAbove G j a delta /
            boundedTailScale beta a)
        atTop (nhds 0)) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun a => boundedLemmaD2IntegralTermBelow G j a delta)
      (fun a => boundedLemmaD2LimitCoeff beta c j *
        boundedTailScale beta a) :=
  boundedLemmaD2IntegralTermBelow_asymptotic_of_growing_rescaled_integral
    C.tail.beta_pos C.tail.c_pos j hdelta_nonneg
    (C.growing_rescaled_integral_tendsto_of_source_tail
      hdelta_nonneg htail_source)

/--
A per-rank dominated-convergence certificate supplies the exact
`a^(-1/beta)` asymptotic for the source Lemma D.2 integral term.
-/
theorem integralTerm_asymptoticEquivalent
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ}
    (C : BoundedLemmaD2DominatedKernelCertificate beta c G j) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (boundedLemmaD2IntegralTerm G j)
      (fun a => boundedLemmaD2LimitCoeff beta c j *
        boundedTailScale beta a) := by
  have hcoeff_ne :
      boundedLemmaD2LimitCoeff beta c j ≠ 0 :=
    ne_of_gt (boundedLemmaD2LimitCoeff_pos
      C.tail.beta_pos C.tail.c_pos j)
  have hratio :
      Tendsto
        (fun a : ℕ =>
          (∫ y in Set.Ioi (0 : ℝ),
            boundedLemmaD2RescaledKernel G beta j a y) /
              boundedLemmaD2LimitCoeff beta c j)
        atTop (nhds 1) := by
    have h :=
      C.rescaled_integral_tendsto.div_const
        (boundedLemmaD2LimitCoeff beta c j)
    simpa [hcoeff_ne] using h
  rw [AppliedModelingLib.Math.AsymptoticEquivalent]
  refine Tendsto.congr' ?_ hratio
  filter_upwards
    [C.change_of_variables, boundedTailScale_eventually_ne_zero beta] with
      a hchange hscale_ne
  rw [hchange]
  field_simp [hcoeff_ne, hscale_ne]

end BoundedLemmaD2DominatedKernelCertificate

/--
Per-rank split certificate matching the paper proof of Lemma D.2.

The near-zero integral has the gamma asymptotic, the tail integral is
negligible relative to `a^(-1/beta)`, and the full integral is eventually the
sum of those two pieces.
-/
structure BoundedLemmaD2SplitIntegralAsymptoticCertificate
    (beta c : ℝ) (G : ℝ → ℝ) (j : ℕ) where
  beta_pos : 0 < beta
  c_pos : 0 < c
  delta : ℝ
  delta_pos : 0 < delta
  split :
    ∀ᶠ a in atTop,
      boundedLemmaD2IntegralTerm G j a =
        boundedLemmaD2IntegralTermBelow G j a delta +
          boundedLemmaD2IntegralTermAbove G j a delta
  below_asymptotic :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun a => boundedLemmaD2IntegralTermBelow G j a delta)
      (fun a => boundedLemmaD2LimitCoeff beta c j *
        boundedTailScale beta a)
  above_negligible :
    Tendsto
      (fun a => boundedLemmaD2IntegralTermAbove G j a delta /
        boundedTailScale beta a)
      atTop (nhds 0)

namespace BoundedLemmaD2SplitIntegralAsymptoticCertificate

/--
Build the paper-style split certificate once the source kernel is eventually
integrable and the two analytic estimates have been proved.
-/
noncomputable def ofAsymptotics
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ} {delta : ℝ}
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (hdelta_pos : 0 < delta)
    (h_integrable :
      ∀ᶠ a in atTop,
        MeasureTheory.IntegrableOn
          (boundedLemmaD2IntegralKernel G j a)
          (Set.Ioi (0 : ℝ)))
    (below_asymptotic :
      AppliedModelingLib.Math.AsymptoticEquivalent
        (fun a => boundedLemmaD2IntegralTermBelow G j a delta)
        (fun a => boundedLemmaD2LimitCoeff beta c j *
          boundedTailScale beta a))
    (above_negligible :
      Tendsto
        (fun a => boundedLemmaD2IntegralTermAbove G j a delta /
          boundedTailScale beta a)
        atTop (nhds 0)) :
    BoundedLemmaD2SplitIntegralAsymptoticCertificate beta c G j where
  beta_pos := hbeta_pos
  c_pos := hc_pos
  delta := delta
  delta_pos := hdelta_pos
  split :=
    boundedLemmaD2IntegralTerm_eventually_split G j hdelta_pos.le
      h_integrable
  below_asymptotic := below_asymptotic
  above_negligible := above_negligible

/--
Build the paper-style split certificate from the already-assembled full
integral asymptotic plus the tail-negligibility estimate. This is useful for
checking that the direct dominated-convergence route and the paper's
near-zero/tail split route agree on the same coefficient.
-/
noncomputable def ofFullAsymptoticAndTail
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ} {delta : ℝ}
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (hdelta_pos : 0 < delta)
    (h_integrable :
      ∀ᶠ a in atTop,
        MeasureTheory.IntegrableOn
          (boundedLemmaD2IntegralKernel G j a)
          (Set.Ioi (0 : ℝ)))
    (full_asymptotic :
      AppliedModelingLib.Math.AsymptoticEquivalent
        (boundedLemmaD2IntegralTerm G j)
        (fun a => boundedLemmaD2LimitCoeff beta c j *
          boundedTailScale beta a))
    (above_negligible :
      Tendsto
        (fun a => boundedLemmaD2IntegralTermAbove G j a delta /
          boundedTailScale beta a)
        atTop (nhds 0)) :
    BoundedLemmaD2SplitIntegralAsymptoticCertificate beta c G j where
  beta_pos := hbeta_pos
  c_pos := hc_pos
  delta := delta
  delta_pos := hdelta_pos
  split :=
    boundedLemmaD2IntegralTerm_eventually_split G j hdelta_pos.le
      h_integrable
  below_asymptotic := by
    have hsplit :=
      boundedLemmaD2IntegralTerm_eventually_split G j hdelta_pos.le
        h_integrable
    have hcoeff_ne :
        boundedLemmaD2LimitCoeff beta c j ≠ 0 :=
      ne_of_gt (boundedLemmaD2LimitCoeff_pos hbeta_pos hc_pos j)
    have htail_coeff :
        Tendsto
          (fun a : ℕ =>
            boundedLemmaD2IntegralTermAbove G j a delta /
              (boundedLemmaD2LimitCoeff beta c j *
                boundedTailScale beta a))
          atTop (nhds 0) := by
      have h :=
        above_negligible.div_const (boundedLemmaD2LimitCoeff beta c j)
      refine Tendsto.congr' ?_ (by simpa [hcoeff_ne] using h)
      filter_upwards [boundedTailScale_eventually_ne_zero beta] with a hscale_ne
      field_simp [hcoeff_ne, hscale_ne]
    rw [AppliedModelingLib.Math.AsymptoticEquivalent] at full_asymptotic ⊢
    have hdiff := full_asymptotic.sub htail_coeff
    refine Tendsto.congr' ?_ (by simpa using hdiff)
    filter_upwards
      [hsplit, boundedTailScale_eventually_ne_zero beta] with
        a hsplit_a hscale_ne
    rw [hsplit_a]
    field_simp [hcoeff_ne, hscale_ne]
    ring
  above_negligible := above_negligible

/--
Build the paper-style split certificate from bounded-support CDF conditions
and the two remaining analytic estimates.
-/
noncomputable def ofBoundedSupportAsymptotics
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ} {delta : ℝ}
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (hdelta_pos : 0 < delta)
    (hG_measurable : Measurable G) (M : ℝ)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    (below_asymptotic :
      AppliedModelingLib.Math.AsymptoticEquivalent
        (fun a => boundedLemmaD2IntegralTermBelow G j a delta)
        (fun a => boundedLemmaD2LimitCoeff beta c j *
          boundedTailScale beta a))
    (above_negligible :
      Tendsto
        (fun a => boundedLemmaD2IntegralTermAbove G j a delta /
          boundedTailScale beta a)
        atTop (nhds 0)) :
    BoundedLemmaD2SplitIntegralAsymptoticCertificate beta c G j :=
  ofAsymptotics hbeta_pos hc_pos hdelta_pos
    (boundedLemmaD2IntegralKernel_eventually_integrableOn_of_bounded_support
      hG_measurable M hG_nonneg hG_le_one hG_eq_one_of_support j)
    below_asymptotic above_negligible

/--
Build the paper-style split certificate from bounded-support CDF conditions,
the positive CDF floor on the above-`delta` tail, and the near-zero asymptotic.
The geometric tail-negligibility estimate is proved internally.
-/
noncomputable def ofBoundedSupportNearZeroAsymptotic
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ} {delta M p : ℝ}
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (hdelta_pos : 0 < delta) (hdeltaM : delta ≤ M)
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hG_measurable : Measurable G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    (hp_le_G_on_tail : ∀ x : ℝ, delta < x → p ≤ G x)
    (below_asymptotic :
      AppliedModelingLib.Math.AsymptoticEquivalent
        (fun a => boundedLemmaD2IntegralTermBelow G j a delta)
        (fun a => boundedLemmaD2LimitCoeff beta c j *
          boundedTailScale beta a)) :
    BoundedLemmaD2SplitIntegralAsymptoticCertificate beta c G j :=
  ofBoundedSupportAsymptotics hbeta_pos hc_pos hdelta_pos
    hG_measurable M hG_nonneg hG_le_one hG_eq_one_of_support
    below_asymptotic
    (boundedLemmaD2IntegralTermAbove_negligible_of_geometric_support_bound
      hG_measurable hbeta_pos hdelta_pos.le hdeltaM hp_pos hp_lt_one
      hG_nonneg hG_le_one hG_eq_one_of_support hp_le_G_on_tail j)

/--
Convert a dominated-convergence full-integral certificate into the
paper-style split certificate when bounded support supplies the geometric tail
estimate. This proves the near-zero split field by subtracting the negligible
tail from the full asymptotic.
-/
noncomputable def ofDominatedKernelAndGeometricTail
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ} {delta M p : ℝ}
    (D : BoundedLemmaD2DominatedKernelCertificate beta c G j)
    (hdelta_pos : 0 < delta) (hdeltaM : delta ≤ M)
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hG_measurable : Measurable G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    (hp_le_G_on_tail : ∀ x : ℝ, delta < x → p ≤ G x) :
    BoundedLemmaD2SplitIntegralAsymptoticCertificate beta c G j :=
  ofFullAsymptoticAndTail D.tail.beta_pos D.tail.c_pos hdelta_pos
    (boundedLemmaD2IntegralKernel_eventually_integrableOn_of_bounded_support
      hG_measurable M hG_nonneg hG_le_one hG_eq_one_of_support j)
    D.integralTerm_asymptoticEquivalent
    (boundedLemmaD2IntegralTermAbove_negligible_of_geometric_support_bound
      hG_measurable D.tail.beta_pos hdelta_pos.le hdeltaM hp_pos hp_lt_one
      hG_nonneg hG_le_one hG_eq_one_of_support hp_le_G_on_tail j)

/--
Convert a dominated-convergence full-integral certificate into the
paper-style split certificate through the growing near-zero rescaled integral.
This uses the same bounded-support geometric tail estimate, but proves the
below-`delta` field by the paper's rescaled near-zero interval rather than by
subtracting source asymptotics.
-/
noncomputable def ofDominatedKernelAndGeometricTailViaGrowing
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ} {delta M p : ℝ}
    (D : BoundedLemmaD2DominatedKernelCertificate beta c G j)
    (hdelta_pos : 0 < delta) (hdeltaM : delta ≤ M)
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hG_measurable : Measurable G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    (hp_le_G_on_tail : ∀ x : ℝ, delta < x → p ≤ G x) :
    BoundedLemmaD2SplitIntegralAsymptoticCertificate beta c G j := by
  let htail_source :=
    boundedLemmaD2IntegralTermAbove_negligible_of_geometric_support_bound
      hG_measurable D.tail.beta_pos hdelta_pos.le hdeltaM hp_pos hp_lt_one
      hG_nonneg hG_le_one hG_eq_one_of_support hp_le_G_on_tail j
  exact
    ofBoundedSupportAsymptotics D.tail.beta_pos D.tail.c_pos hdelta_pos
      hG_measurable M hG_nonneg hG_le_one hG_eq_one_of_support
      (D.integralTermBelow_asymptoticEquivalent hdelta_pos)
      htail_source

/--
Construct the paper-style split certificate directly from the bounded-tail
limit, local CDF power bounds near zero, and bounded-support geometric tail
control. This is the faithful bounded-support Lemma D.2 route: local domination
on the expanding near-zero interval proves the below split, while bounded
support controls the above split.
-/
noncomputable def ofLocalCDFPowerBoundsAndGeometricTail
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ} {delta M p A B : ℝ}
    (tail : BoundedTailCDFPowerSandwich G beta c)
    (hdelta_pos : 0 < delta) (hdeltaM : delta ≤ M)
    (hA_pos : 0 < A) (hB_nonneg : 0 ≤ B)
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hG_measurable : Measurable G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_lower :
      ∀ x : ℝ, 0 < x → x < delta → A * x ^ beta ≤ G x)
    (hG_upper :
      ∀ x : ℝ, 0 < x → x < delta → G x ≤ B * x ^ beta)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    (hp_le_G_on_tail : ∀ x : ℝ, delta < x → p ≤ G x) :
    BoundedLemmaD2SplitIntegralAsymptoticCertificate beta c G j := by
  let hbelow :=
    boundedLemmaD2IntegralTermBelow_asymptotic_of_local_cdf_power_bounds
      tail hG_measurable hdelta_pos hA_pos hB_nonneg
      hG_nonneg hG_le_one hG_lower hG_upper j
  let htail_source :=
    boundedLemmaD2IntegralTermAbove_negligible_of_geometric_support_bound
      hG_measurable tail.beta_pos hdelta_pos.le hdeltaM hp_pos hp_lt_one
      hG_nonneg hG_le_one hG_eq_one_of_support hp_le_G_on_tail j
  exact
    ofBoundedSupportAsymptotics tail.beta_pos tail.c_pos hdelta_pos
      hG_measurable M hG_nonneg hG_le_one hG_eq_one_of_support
      hbelow htail_source

/--
Construct the paper-style split certificate from the bounded-tail CDF
asymptotic, monotonicity of the reflected CDF, and bounded support. The CDF
asymptotic gives local power bounds near zero; monotonicity turns a smaller
near-zero lower bound into the positive above-threshold floor used by the
geometric tail estimate.
-/
noncomputable def ofCDFPowerSandwichMonotoneBoundedSupport
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ} {M : ℝ}
    (tail : BoundedTailCDFPowerSandwich G beta c)
    (hM_pos : 0 < M)
    (hG_measurable : Measurable G)
    (hG_mono : Monotone G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1) :
    BoundedLemmaD2SplitIntegralAsymptoticCertificate beta c G j := by
  let hlocal := tail.exists_local_cdf_power_bounds
  let delta₀ : ℝ := Classical.choose hlocal
  let hlocal_delta := Classical.choose_spec hlocal
  let A : ℝ := Classical.choose hlocal_delta
  let hlocal_A := Classical.choose_spec hlocal_delta
  let B : ℝ := Classical.choose hlocal_A
  have hlocal_spec := Classical.choose_spec hlocal_A
  rcases hlocal_spec with
    ⟨hdelta₀_pos, hA_pos, hB_nonneg, hG_lower₀, hG_upper₀⟩
  let delta : ℝ := min delta₀ M / 2
  let probe : ℝ := delta / 2
  let p : ℝ := (A * probe ^ beta) / 2
  have hmin_pos : 0 < min delta₀ M := lt_min hdelta₀_pos hM_pos
  have hdelta_pos : 0 < delta := by
    dsimp [delta]
    positivity
  have hdelta_lt_delta₀ : delta < delta₀ := by
    have hmin_le : min delta₀ M ≤ delta₀ := min_le_left _ _
    dsimp [delta]
    linarith
  have hdeltaM : delta ≤ M := by
    have hmin_le : min delta₀ M ≤ M := min_le_right _ _
    dsimp [delta]
    linarith
  have hprobe_pos : 0 < probe := by
    dsimp [probe]
    positivity
  have hprobe_lt_delta : probe < delta := by
    dsimp [probe]
    linarith
  have hprobe_lt_delta₀ : probe < delta₀ :=
    lt_trans hprobe_lt_delta hdelta_lt_delta₀
  have hprobe_lower : A * probe ^ beta ≤ G probe :=
    hG_lower₀ probe hprobe_pos hprobe_lt_delta₀
  have hAprobe_pos : 0 < A * probe ^ beta :=
    mul_pos hA_pos (Real.rpow_pos_of_pos hprobe_pos beta)
  have hp_pos : 0 < p := by
    dsimp [p]
    positivity
  have hp_le_Aprobe : p ≤ A * probe ^ beta := by
    dsimp [p]
    linarith
  have hp_lt_one : p < 1 := by
    have hAprobe_le_one : A * probe ^ beta ≤ 1 :=
      le_trans hprobe_lower (hG_le_one probe)
    dsimp [p]
    linarith
  have hG_lower :
      ∀ x : ℝ, 0 < x → x < delta → A * x ^ beta ≤ G x := by
    intro x hx_pos hx_lt
    exact hG_lower₀ x hx_pos (lt_trans hx_lt hdelta_lt_delta₀)
  have hG_upper :
      ∀ x : ℝ, 0 < x → x < delta → G x ≤ B * x ^ beta := by
    intro x hx_pos hx_lt
    exact hG_upper₀ x hx_pos (lt_trans hx_lt hdelta_lt_delta₀)
  have hp_le_G_on_tail : ∀ x : ℝ, delta < x → p ≤ G x := by
    intro x hx
    have hprobe_le_x : probe ≤ x :=
      le_of_lt (lt_trans hprobe_lt_delta hx)
    exact le_trans hp_le_Aprobe
      (le_trans hprobe_lower (hG_mono hprobe_le_x))
  exact
    ofLocalCDFPowerBoundsAndGeometricTail tail hdelta_pos hdeltaM
      hA_pos hB_nonneg hp_pos hp_lt_one hG_measurable
      hG_nonneg hG_le_one hG_lower hG_upper hG_eq_one_of_support
      hp_le_G_on_tail

/--
The paper's split proof supplies the fixed-rank Lemma D.2 integral
asymptotic.
-/
theorem integralTerm_asymptoticEquivalent
    {beta c : ℝ} {G : ℝ → ℝ} {j : ℕ}
    (C : BoundedLemmaD2SplitIntegralAsymptoticCertificate beta c G j) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (boundedLemmaD2IntegralTerm G j)
      (fun a => boundedLemmaD2LimitCoeff beta c j *
        boundedTailScale beta a) := by
  have hcoeff_ne :
      boundedLemmaD2LimitCoeff beta c j ≠ 0 :=
    ne_of_gt (boundedLemmaD2LimitCoeff_pos C.beta_pos C.c_pos j)
  have hsum :=
    asymptoticEquivalent_add_negligible_common_scale
      (fun a => boundedLemmaD2IntegralTermBelow G j a C.delta)
      (fun a => boundedLemmaD2IntegralTermAbove G j a C.delta)
      (boundedTailScale beta)
      (boundedLemmaD2LimitCoeff beta c j)
      hcoeff_ne
      (boundedTailScale_eventually_ne_zero beta)
      C.below_asymptotic
      C.above_negligible
  rw [AppliedModelingLib.Math.AsymptoticEquivalent] at hsum ⊢
  refine Tendsto.congr' ?_ hsum
  filter_upwards [C.split] with a hsplit
  rw [hsplit]

end BoundedLemmaD2SplitIntegralAsymptoticCertificate

/--
Finite-index split certificate for the actual bounded Lemma D.2 integral
terms.
-/
structure BoundedLemmaD2SplitIntegralFiniteCertificate
    (beta c : ℝ) (k : ℕ) (G : ℝ → ℝ) where
  k_pos : 0 < k
  fixed :
    ∀ p : BoundedLemmaD2Index k,
      BoundedLemmaD2SplitIntegralAsymptoticCertificate beta c G p.2.val

namespace BoundedLemmaD2SplitIntegralFiniteCertificate

/--
Finite-index paper-style split certificate directly from the bounded-tail
limit, local CDF power bounds, and bounded-support geometric tail control.
-/
noncomputable def ofLocalCDFPowerBoundsAndGeometricTail
    {beta c : ℝ} {k : ℕ} {G : ℝ → ℝ} {delta M p A B : ℝ}
    (tail : BoundedTailCDFPowerSandwich G beta c)
    (k_pos : 0 < k)
    (hdelta_pos : 0 < delta) (hdeltaM : delta ≤ M)
    (hA_pos : 0 < A) (hB_nonneg : 0 ≤ B)
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hG_measurable : Measurable G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_lower :
      ∀ x : ℝ, 0 < x → x < delta → A * x ^ beta ≤ G x)
    (hG_upper :
      ∀ x : ℝ, 0 < x → x < delta → G x ≤ B * x ^ beta)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    (hp_le_G_on_tail : ∀ x : ℝ, delta < x → p ≤ G x) :
    BoundedLemmaD2SplitIntegralFiniteCertificate beta c k G where
  k_pos := k_pos
  fixed := by
    intro q
    exact
      BoundedLemmaD2SplitIntegralAsymptoticCertificate.ofLocalCDFPowerBoundsAndGeometricTail
        tail hdelta_pos hdeltaM hA_pos hB_nonneg hp_pos hp_lt_one
        hG_measurable hG_nonneg hG_le_one hG_lower hG_upper
        hG_eq_one_of_support hp_le_G_on_tail

/--
Finite-index split certificate from the bounded-tail CDF asymptotic,
monotonicity of the reflected CDF, and bounded support.
-/
noncomputable def ofCDFPowerSandwichMonotoneBoundedSupport
    {beta c : ℝ} {k : ℕ} {G : ℝ → ℝ} {M : ℝ}
    (tail : BoundedTailCDFPowerSandwich G beta c)
    (k_pos : 0 < k)
    (hM_pos : 0 < M)
    (hG_measurable : Measurable G)
    (hG_mono : Monotone G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1) :
    BoundedLemmaD2SplitIntegralFiniteCertificate beta c k G where
  k_pos := k_pos
  fixed := by
    intro q
    exact
      BoundedLemmaD2SplitIntegralAsymptoticCertificate.ofCDFPowerSandwichMonotoneBoundedSupport
        tail hM_pos hG_measurable hG_mono hG_nonneg hG_le_one
        hG_eq_one_of_support

/--
The finite split certificate supplies the exact-coefficient integral
asymptotic certificate consumed downstream.
-/
noncomputable def toLimitIntegralAsymptoticCertificate
    {beta c : ℝ} {k : ℕ} {G : ℝ → ℝ}
    (C : BoundedLemmaD2SplitIntegralFiniteCertificate beta c k G) :
    BoundedLemmaD2LimitIntegralAsymptoticCertificate beta c k G where
  beta_pos := by
    let p0 : BoundedLemmaD2Index k := ⟨⟨0, C.k_pos⟩, ⟨0, by simp⟩⟩
    exact (C.fixed p0).beta_pos
  c_pos := by
    let p0 : BoundedLemmaD2Index k := ⟨⟨0, C.k_pos⟩, ⟨0, by simp⟩⟩
    exact (C.fixed p0).c_pos
  k_pos := C.k_pos
  term_asymptotic := by
    intro p
    simpa [boundedLemmaD2IndexedIntegralTerm] using
      (C.fixed p).integralTerm_asymptoticEquivalent

end BoundedLemmaD2SplitIntegralFiniteCertificate

/--
Finite-index dominated-convergence certificate for the actual bounded
Lemma D.2 integral terms. This is the formal version of the paper's remaining
analytic work after the pointwise rescaled-kernel limit.
-/
structure BoundedLemmaD2DominatedIntegralAsymptoticCertificate
    (beta c : ℝ) (k : ℕ) (G : ℝ → ℝ) where
  tail : BoundedTailCDFPowerSandwich G beta c
  k_pos : 0 < k
  change_of_variables :
    ∀ p : BoundedLemmaD2Index k,
      ∀ᶠ a in atTop,
        boundedLemmaD2IntegralTerm G p.2.val a =
          boundedTailScale beta a *
            ∫ y in Set.Ioi (0 : ℝ),
              boundedLemmaD2RescaledKernel G beta p.2.val a y
  kernel_measurable :
    ∀ p : BoundedLemmaD2Index k,
      ∀ᶠ a in atTop,
        MeasureTheory.AEStronglyMeasurable
          (fun y : ℝ => boundedLemmaD2RescaledKernel G beta p.2.val a y)
          (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
  bound : BoundedLemmaD2Index k → ℝ → ℝ
  bound_integrable :
    ∀ p : BoundedLemmaD2Index k,
      MeasureTheory.Integrable (bound p)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
  kernel_bound :
    ∀ p : BoundedLemmaD2Index k,
      ∀ᶠ a in atTop,
        ∀ᵐ y ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
          ‖boundedLemmaD2RescaledKernel G beta p.2.val a y‖ ≤ bound p y

namespace BoundedLemmaD2DominatedIntegralAsymptoticCertificate

/--
Build the finite-index dominated-convergence certificate from measurability of
the reflected CDF and integrable envelopes for each fixed paper index. The
change-of-variables and kernel-measurability fields are derived automatically.
-/
noncomputable def ofMeasurableBound
    {beta c : ℝ} {k : ℕ} {G : ℝ → ℝ}
    (tail : BoundedTailCDFPowerSandwich G beta c)
    (k_pos : 0 < k)
    (hG : Measurable G)
    (bound : BoundedLemmaD2Index k → ℝ → ℝ)
    (bound_integrable :
      ∀ p : BoundedLemmaD2Index k,
        MeasureTheory.Integrable (bound p)
          (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (kernel_bound :
      ∀ p : BoundedLemmaD2Index k,
        ∀ᶠ a in atTop,
          ∀ᵐ y ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
            ‖boundedLemmaD2RescaledKernel G beta p.2.val a y‖ ≤ bound p y) :
    BoundedLemmaD2DominatedIntegralAsymptoticCertificate beta c k G where
  tail := tail
  k_pos := k_pos
  change_of_variables := by
    intro p
    exact boundedLemmaD2IntegralTerm_eventually_changeOfVariables
      G beta p.2.val
  kernel_measurable := by
    intro p
    filter_upwards with a
    exact boundedLemmaD2RescaledKernel_aestronglyMeasurable
      hG beta p.2.val a
  bound := bound
  bound_integrable := bound_integrable
  kernel_bound := kernel_bound

/-- The finite-index certificate gives a per-rank dominated-kernel certificate. -/
noncomputable def fixedCertificate
    {beta c : ℝ} {k : ℕ} {G : ℝ → ℝ}
    (C : BoundedLemmaD2DominatedIntegralAsymptoticCertificate beta c k G)
    (p : BoundedLemmaD2Index k) :
    BoundedLemmaD2DominatedKernelCertificate beta c G p.2.val where
  tail := C.tail
  change_of_variables := C.change_of_variables p
  kernel_measurable := C.kernel_measurable p
  bound := C.bound p
  bound_integrable := C.bound_integrable p
  kernel_bound := C.kernel_bound p

/--
The finite-index dominated certificate plus a common bounded-support geometric
tail estimate supplies the paper-style split finite certificate through the
growing near-zero rescaled interval.
-/
noncomputable def toSplitIntegralFiniteCertificateOfGeometricTailViaGrowing
    {beta c : ℝ} {k : ℕ} {G : ℝ → ℝ}
    (C : BoundedLemmaD2DominatedIntegralAsymptoticCertificate beta c k G)
    {delta M p : ℝ}
    (hdelta_pos : 0 < delta) (hdeltaM : delta ≤ M)
    (hp_pos : 0 < p) (hp_lt_one : p < 1)
    (hG_measurable : Measurable G)
    (hG_nonneg : ∀ x : ℝ, 0 ≤ G x)
    (hG_le_one : ∀ x : ℝ, G x ≤ 1)
    (hG_eq_one_of_support : ∀ x : ℝ, M ≤ x → G x = 1)
    (hp_le_G_on_tail : ∀ x : ℝ, delta < x → p ≤ G x) :
    BoundedLemmaD2SplitIntegralFiniteCertificate beta c k G where
  k_pos := C.k_pos
  fixed := by
    intro q
    exact
      BoundedLemmaD2SplitIntegralAsymptoticCertificate.ofDominatedKernelAndGeometricTailViaGrowing
        (C.fixedCertificate q) hdelta_pos hdeltaM hp_pos hp_lt_one
        hG_measurable hG_nonneg hG_le_one hG_eq_one_of_support
        hp_le_G_on_tail

/--
The dominated-convergence certificate supplies the sharper exact-coefficient
integral asymptotic certificate consumed by the finite-sum assembly.
-/
noncomputable def toLimitIntegralAsymptoticCertificate
    {beta c : ℝ} {k : ℕ} {G : ℝ → ℝ}
    (C : BoundedLemmaD2DominatedIntegralAsymptoticCertificate beta c k G) :
    BoundedLemmaD2LimitIntegralAsymptoticCertificate beta c k G where
  beta_pos := C.tail.beta_pos
  c_pos := C.tail.c_pos
  k_pos := C.k_pos
  term_asymptotic := by
    intro p
    simpa [boundedLemmaD2IndexedIntegralTerm] using
      (C.fixedCertificate p).integralTerm_asymptoticEquivalent

end BoundedLemmaD2DominatedIntegralAsymptoticCertificate

/--
Eventual sandwich for the actual source integral terms, derived from the
integral asymptotic certificate.
-/
theorem boundedLemmaD2IntegralAsymptoticCertificate_eventually_integral_sandwich
    {beta : ℝ} {k : ℕ} {G : ℝ → ℝ}
    (C : BoundedLemmaD2IntegralAsymptoticCertificate beta k G)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ a in atTop,
      ∀ p : BoundedLemmaD2Index k,
        (1 - ε) * (C.coeff p * boundedTailScale beta a) ≤
            boundedLemmaD2IndexedIntegralTerm G p a ∧
          boundedLemmaD2IndexedIntegralTerm G p a ≤
            (1 + ε) * (C.coeff p * boundedTailScale beta a) := C.eventually_all_term_sandwich hε

/--
Formalized finite-sum conclusion after Lemma D.2: once every fixed rank/index
integral has the paper's `a^(-1 / beta)` asymptotic, their double sum has the
same scale with coefficient equal to the sum of the fixed coefficients.
-/
theorem boundedLemmaD2TopKLoss_asymptoticEquivalent
    {beta : ℝ} {k : ℕ}
    (term : BoundedLemmaD2Index k → ℕ → ℝ)
    (C : BoundedLemmaD2FiniteSumCertificate beta k term) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (boundedLemmaD2TopKLoss k term)
      (fun a => (∑ p : BoundedLemmaD2Index k, C.coeff p) *
        boundedTailScale beta a) :=
   finite_sum_asymptoticEquivalent_common_scale
    term C.coeff (boundedTailScale beta)
    (fun p => ne_of_gt (C.coeff_pos p))
    (ne_of_gt C.totalCoeff_pos)
    (boundedTailScale_eventually_ne_zero beta)
    C.term_asymptotic

/-- The certificate's total coefficient is the matching nested sum. -/
theorem boundedLemmaD2FiniteSumCertificate_totalCoeff_eq_nested_sum
    {beta : ℝ} {k : ℕ}
    {term : BoundedLemmaD2Index k → ℕ → ℝ}
    (C : BoundedLemmaD2FiniteSumCertificate beta k term) :
    (∑ p : BoundedLemmaD2Index k, C.coeff p) =
      ∑ i : Fin k, ∑ j : Fin (i.val + 1), C.coeff ⟨i, j⟩ := by
  rw [Fintype.sum_sigma]

/--
Nested-sum version of the Lemma D.2 finite assembly, matching the source
display with `i = 1, ..., k` and `j = 0, ..., i - 1`.
-/
theorem boundedLemmaD2NestedTopKLoss_asymptoticEquivalent
    {beta : ℝ} {k : ℕ}
    (term : BoundedLemmaD2Index k → ℕ → ℝ)
    (C : BoundedLemmaD2FiniteSumCertificate beta k term) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun a => ∑ i : Fin k, ∑ j : Fin (i.val + 1), term ⟨i, j⟩ a)
      (fun a =>
        (∑ i : Fin k, ∑ j : Fin (i.val + 1), C.coeff ⟨i, j⟩) *
          boundedTailScale beta a) := by
  have h := boundedLemmaD2TopKLoss_asymptoticEquivalent term C
  rw [AppliedModelingLib.Math.AsymptoticEquivalent] at h ⊢
  refine Tendsto.congr' ?_ h
  filter_upwards with a
  rw [boundedLemmaD2TopKLoss_eq_nested_sum,
    boundedLemmaD2FiniteSumCertificate_totalCoeff_eq_nested_sum]

/--
Equations (91)-(96) assembled: reflection identities plus fixed-term Lemma
D.2 asymptotics imply the bounded top-`k` source loss
`M * k - h(a) ~ B * a^(-1/β)`.
-/
theorem boundedLemmaD2_reflected_source_loss_asymptoticEquivalent
    {beta M : ℝ} {k : ℕ}
    (sourceMean : Fin k → ℕ → ℝ)
    (term : BoundedLemmaD2Index k → ℕ → ℝ)
    (hsource :
      ∀ a (i : Fin k),
        sourceMean i a =
          M - ∑ j : Fin (i.val + 1), term ⟨i, j⟩ a)
    (C : BoundedLemmaD2FiniteSumCertificate beta k term) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun a => (k : ℝ) * M - ∑ i : Fin k, sourceMean i a)
      (fun a => (∑ p : BoundedLemmaD2Index k, C.coeff p) *
        boundedTailScale beta a) := by
  have h := boundedLemmaD2TopKLoss_asymptoticEquivalent term C
  rw [AppliedModelingLib.Math.AsymptoticEquivalent] at h ⊢
  refine Tendsto.congr' ?_ h
  filter_upwards with a
  rw [boundedLemmaD2_reflection_loss_eq_topKLoss M sourceMean term hsource a]

/--
Actual-integral version of the Lemma D.2 finite assembly: a certificate for
the source integral terms yields the top-`k` bounded-loss asymptotic.
-/
theorem boundedLemmaD2IntegralTopKLoss_asymptoticEquivalent
    {beta : ℝ} {k : ℕ} (G : ℝ → ℝ)
    (C : BoundedLemmaD2IntegralAsymptoticCertificate beta k G) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (boundedLemmaD2TopKLoss k (boundedLemmaD2IndexedIntegralTerm G))
      (fun a => (∑ p : BoundedLemmaD2Index k, C.coeff p) *
        boundedTailScale beta a) :=
  boundedLemmaD2TopKLoss_asymptoticEquivalent
    (boundedLemmaD2IndexedIntegralTerm G) C

/--
Equations (91)-(96) with the actual Lemma D.2 integral term. This is the
bounded branch's current analytic proof target: prove the integral certificate
for `G`, then this theorem gives the source loss asymptotic.
-/
theorem boundedLemmaD2_reflected_integral_source_loss_asymptoticEquivalent
    {beta M : ℝ} {k : ℕ} (G : ℝ → ℝ)
    (sourceMean : Fin k → ℕ → ℝ)
    (hsource :
      ∀ a (i : Fin k),
        sourceMean i a =
          M - ∑ j : Fin (i.val + 1),
            boundedLemmaD2IntegralTerm G j.val a)
    (C : BoundedLemmaD2IntegralAsymptoticCertificate beta k G) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun a => (k : ℝ) * M - ∑ i : Fin k, sourceMean i a)
      (fun a => (∑ p : BoundedLemmaD2Index k, C.coeff p) *
        boundedTailScale beta a) :=
   boundedLemmaD2_reflected_source_loss_asymptoticEquivalent
    sourceMean (boundedLemmaD2IndexedIntegralTerm G)
    (fun a i => by
      simpa [boundedLemmaD2IndexedIntegralTerm] using hsource a i)
    C

/--
Actual-integral finite assembly with the exact gamma limiting coefficients.
The only remaining source work is to prove the sharper certificate's
fixed-`j` integral asymptotics.
-/
theorem boundedLemmaD2IntegralTopKLoss_asymptoticEquivalent_of_limit_coeff_certificate
    {beta c : ℝ} {k : ℕ} (G : ℝ → ℝ)
    (C : BoundedLemmaD2LimitIntegralAsymptoticCertificate beta c k G) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (boundedLemmaD2TopKLoss k (boundedLemmaD2IndexedIntegralTerm G))
      (fun a =>
        (∑ p : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c p.2.val) *
          boundedTailScale beta a) :=
  boundedLemmaD2IntegralTopKLoss_asymptoticEquivalent G
    C.toIntegralAsymptoticCertificate

/--
Equations (91)-(96) with the exact gamma limiting coefficients.
-/
theorem
    boundedLemmaD2_reflected_integral_source_loss_asymptoticEquivalent_of_limit_coeff_certificate
    {beta c M : ℝ} {k : ℕ} (G : ℝ → ℝ)
    (sourceMean : Fin k → ℕ → ℝ)
    (hsource :
      ∀ a (i : Fin k),
        sourceMean i a =
          M - ∑ j : Fin (i.val + 1),
            boundedLemmaD2IntegralTerm G j.val a)
    (C : BoundedLemmaD2LimitIntegralAsymptoticCertificate beta c k G) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun a => (k : ℝ) * M - ∑ i : Fin k, sourceMean i a)
      (fun a =>
        (∑ p : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c p.2.val) *
          boundedTailScale beta a) :=
  boundedLemmaD2_reflected_integral_source_loss_asymptoticEquivalent
    G sourceMean hsource C.toIntegralAsymptoticCertificate

/--
Actual-integral finite assembly from an explicit dominated-convergence and
change-of-variables certificate.
-/
theorem boundedLemmaD2IntegralTopKLoss_asymptoticEquivalent_of_dominated_certificate
    {beta c : ℝ} {k : ℕ} (G : ℝ → ℝ)
    (C : BoundedLemmaD2DominatedIntegralAsymptoticCertificate beta c k G) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (boundedLemmaD2TopKLoss k (boundedLemmaD2IndexedIntegralTerm G))
      (fun a =>
        (∑ p : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c p.2.val) *
          boundedTailScale beta a) :=
  boundedLemmaD2IntegralTopKLoss_asymptoticEquivalent_of_limit_coeff_certificate
    G C.toLimitIntegralAsymptoticCertificate

/--
Equations (91)-(96) from an explicit dominated-convergence and
change-of-variables certificate.
-/
theorem
    boundedLemmaD2_reflected_integral_source_loss_asymptoticEquivalent_of_dominated_certificate
    {beta c M : ℝ} {k : ℕ} (G : ℝ → ℝ)
    (sourceMean : Fin k → ℕ → ℝ)
    (hsource :
      ∀ a (i : Fin k),
        sourceMean i a =
          M - ∑ j : Fin (i.val + 1),
            boundedLemmaD2IntegralTerm G j.val a)
    (C : BoundedLemmaD2DominatedIntegralAsymptoticCertificate beta c k G) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun a => (k : ℝ) * M - ∑ i : Fin k, sourceMean i a)
      (fun a =>
        (∑ p : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c p.2.val) *
          boundedTailScale beta a) :=
  boundedLemmaD2_reflected_integral_source_loss_asymptoticEquivalent_of_limit_coeff_certificate
    G sourceMean hsource C.toLimitIntegralAsymptoticCertificate

/--
Actual-integral finite assembly from the paper-style split certificate.
-/
theorem boundedLemmaD2IntegralTopKLoss_asymptoticEquivalent_of_split_certificate
    {beta c : ℝ} {k : ℕ} (G : ℝ → ℝ)
    (C : BoundedLemmaD2SplitIntegralFiniteCertificate beta c k G) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (boundedLemmaD2TopKLoss k (boundedLemmaD2IndexedIntegralTerm G))
      (fun a =>
        (∑ p : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c p.2.val) *
          boundedTailScale beta a) :=
  boundedLemmaD2IntegralTopKLoss_asymptoticEquivalent_of_limit_coeff_certificate
    G C.toLimitIntegralAsymptoticCertificate

/--
Equations (91)-(96) from the paper-style split certificate.
-/
theorem
    boundedLemmaD2_reflected_integral_source_loss_asymptoticEquivalent_of_split_certificate
    {beta c M : ℝ} {k : ℕ} (G : ℝ → ℝ)
    (sourceMean : Fin k → ℕ → ℝ)
    (hsource :
      ∀ a (i : Fin k),
        sourceMean i a =
          M - ∑ j : Fin (i.val + 1),
            boundedLemmaD2IntegralTerm G j.val a)
    (C : BoundedLemmaD2SplitIntegralFiniteCertificate beta c k G) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun a => (k : ℝ) * M - ∑ i : Fin k, sourceMean i a)
      (fun a =>
        (∑ p : BoundedLemmaD2Index k,
          boundedLemmaD2LimitCoeff beta c p.2.val) *
          boundedTailScale beta a) :=
  boundedLemmaD2_reflected_integral_source_loss_asymptoticEquivalent_of_limit_coeff_certificate
    G sourceMean hsource C.toLimitIntegralAsymptoticCertificate

theorem boundedPowerMarginalModel_has_nonnegative_marginals
    {T : ℕ} (likelihood : ItemType T → ℝ) (beta : ℝ) :
    ((boundedPowerMarginalOracle T beta).toConsumptionModel likelihood 1).HasNonnegativeMarginals := by
  intro t q
  exact boundedPowerMarginalValue_forward_marginal_nonneg beta q

theorem boundedPowerMarginalModel_has_diminishing_returns
    {T : ℕ} (likelihood : ItemType T → ℝ) {beta : ℝ}
    (hbeta_pos : 0 < beta) :
    ((boundedPowerMarginalOracle T beta).toConsumptionModel likelihood 1).HasDiminishingReturns := by
  intro t q
  exact boundedPowerMarginalValue_marginal_antitone_step hbeta_pos q

/-- Finite-prefix error for the exact bounded power-marginal FOC proof. -/
noncomputable def boundedPowerMarginalError {T : ℕ}
    (likelihood : ItemType T → ℝ) (beta : ℝ) (N : ℕ) : ℝ :=
  powerLawSublinearFOCError likelihood (beta / (beta + 1)) N

theorem boundedPowerMarginalError_nonneg {T : ℕ}
    (likelihood : ItemType T → ℝ) (beta : ℝ)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (N : ℕ) :
    0 ≤ boundedPowerMarginalError likelihood beta N :=
  powerLawSublinearFOCError_nonneg likelihood (beta / (beta + 1)) hlike_pos N

theorem boundedPowerMarginalError_tends_to_zero {T : ℕ}
    (likelihood : ItemType T → ℝ) (beta : ℝ)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t) :
    AppliedModelingLib.Math.TendsToZero
      (boundedPowerMarginalError likelihood beta) :=
  powerLawSublinearFOCError_tends_to_zero likelihood (beta / (beta + 1))
    hlike_pos

/--
Exact bounded power-marginal FOC certificate.

This closes the optimization layer for a top-one oracle with the paper's
bounded-support marginal decay exponent. The remaining source-specific
probability work is to derive these power-law marginals, or their asymptotic
equivalent, from the actual bounded order-statistic model.
-/
noncomputable def boundedPowerMarginalSublinearFOCCertificate
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (beta : ℝ)
    (hbeta_pos : 0 < beta)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t) :
    PairwiseScaledSublinearFOCCertificate
      (fun _ =>
        (boundedPowerMarginalOracle T beta).toConsumptionModel likelihood 1)
      (fun t : ItemType T => likelihood t ^ (beta / (beta + 1)))
      (gammaLikelihoodProfile likelihood (beta / (beta + 1))) :=
  topKPowerLawSublinearFOCCertificate likelihood
    (boundedMarginalExponent_pos hbeta_pos)
    (boundedMarginalExponent_one_div_eq_gamma hbeta_pos)
    hlike_pos
    (fun _t _q hq => boundedPowerMarginalValue_backward_marginal beta hq)
    (fun _t q => boundedPowerMarginalValue_forward_marginal beta q)

end PRPKG24AccuracyDiversity

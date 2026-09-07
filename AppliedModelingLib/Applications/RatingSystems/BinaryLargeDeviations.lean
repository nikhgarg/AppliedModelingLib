import AppliedModelingLib.Applications.RatingSystems.FiniteComparison
import AppliedModelingLib.Foundations.Math.ThresholdCharacterization
import AppliedModelingLib.Foundations.Optimization.Endpoint
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Function.Floor

open scoped BigOperators
open MeasureTheory

namespace AppliedModelingLib
namespace Probability

noncomputable section

/-!
# Binary Finite-Rating Large-Deviation Models

Reusable `Bool`-valued finite-rating infrastructure for papers whose ratings
are Bernoulli success/failure observations.  This module specializes the
generic finite-rating LDP API to the binary rating score `false ↦ 0`,
`true ↦ 1`, while leaving the harder Bernoulli-KL Legendre identification to
downstream analysis lemmas.
-/

/-- Bernoulli finite law from a real success probability in `[0,1]`. -/
def realBernoulliPMF (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : PMF Bool :=
  PMF.bernoulli ⟨p, hp0⟩ (by
    change p ≤ (1 : ℝ)
    exact hp1)

@[simp] theorem realBernoulliPMF_apply_true_toReal
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (realBernoulliPMF p hp0 hp1 true).toReal = p := by
  rw [realBernoulliPMF, PMF.bernoulli_apply]
  change ((⟨p, hp0⟩ : NNReal) : ℝ) = p
  rfl

@[simp] theorem realBernoulliPMF_apply_false_toReal
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (realBernoulliPMF p hp0 hp1 false).toReal = 1 - p := by
  rw [realBernoulliPMF, PMF.bernoulli_apply]
  change ((1 - ⟨p, hp0⟩ : NNReal) : ℝ) = 1 - p
  rw [NNReal.coe_sub]
  · rfl
  · change p ≤ (1 : ℝ)
    exact hp1

/-- Binary rating score: success has score `1`, failure has score `0`. -/
def binaryRatingScore (b : Bool) : ℝ :=
  if b then 1 else 0

@[simp] theorem binaryRatingScore_true : binaryRatingScore true = 1 := by
  rfl

@[simp] theorem binaryRatingScore_false : binaryRatingScore false = 0 := by
  rfl

/-- The zero-score atom of a Bernoulli binary rating has mass `1 - p`. -/
theorem realBernoulliPMF_binaryRatingScore_zero_prob
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    AppliedModelingLib.pmfProb (realBernoulliPMF p hp0 hp1)
        (fun b : Bool => binaryRatingScore b = 0) =
      1 - p := by
  unfold AppliedModelingLib.pmfProb AppliedModelingLib.pmfExp binaryRatingScore
  simp [realBernoulliPMF_apply_false_toReal]

/-- The one-score atom of a Bernoulli binary rating has mass `p`. -/
theorem realBernoulliPMF_binaryRatingScore_one_prob
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    AppliedModelingLib.pmfProb (realBernoulliPMF p hp0 hp1)
        (fun b : Bool => binaryRatingScore b = 1) =
      p := by
  unfold AppliedModelingLib.pmfProb AppliedModelingLib.pmfExp binaryRatingScore
  simp [realBernoulliPMF_apply_true_toReal]

/-- The zero atom of the complementary binary score `1 - score` has mass `p`. -/
theorem realBernoulliPMF_one_sub_binaryRatingScore_zero_prob
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    AppliedModelingLib.pmfProb (realBernoulliPMF p hp0 hp1)
        (fun b : Bool => 1 - binaryRatingScore b = 0) =
      p := by
  unfold AppliedModelingLib.pmfProb AppliedModelingLib.pmfExp binaryRatingScore
  simp [realBernoulliPMF_apply_true_toReal]

/-- Finite MGF of the Bernoulli binary-rating score. -/
theorem finiteMGF_realBernoulliPMF_binaryRatingScore
    (p z : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
  finiteMGF (realBernoulliPMF p hp0 hp1) binaryRatingScore z =
      (1 - p) + p * Real.exp z := by
  unfold finiteMGF binaryRatingScore
  simp
  ring

/-- Finite log-MGF of the Bernoulli binary-rating score. -/
theorem finiteLogMGF_realBernoulliPMF_binaryRatingScore
    (p z : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    finiteLogMGF (realBernoulliPMF p hp0 hp1) binaryRatingScore z =
      Real.log ((1 - p) + p * Real.exp z) := by
  simp [finiteLogMGF, finiteMGF_realBernoulliPMF_binaryRatingScore]

/-- Derivative of the Bernoulli binary-rating log-MGF. -/
theorem finiteLogMGF_realBernoulliPMF_binaryRatingScore_hasDerivAt
    (p z : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    HasDerivAt
      (fun t : ℝ =>
        finiteLogMGF (realBernoulliPMF p hp0 hp1) binaryRatingScore t)
      (p * Real.exp z / ((1 - p) + p * Real.exp z)) z := by
  have h :=
    finiteLogMGF_hasDerivAt
      (realBernoulliPMF p hp0 hp1) binaryRatingScore z
  convert h using 1
  simp [finiteMGF_realBernoulliPMF_binaryRatingScore]

/--
Dual parameter whose Bernoulli binary log-MGF derivative equals the target
threshold `a`.
-/
def binaryLogMGFDerivativeArg (p a : ℝ) : ℝ :=
  Real.log (a * (1 - p) / (p * (1 - a)))

/-- Log-odds of an interior Bernoulli success probability. -/
def bernoulliLogOdds (p : ℝ) : ℝ :=
  Real.log (p / (1 - p))

/-- Failure-side weighted geometric base for two Bernoulli probabilities. -/
def weightedBernoulliFailureBase (gHi gLo pHi pLo : ℝ) : ℝ :=
  (1 - pLo) ^ (gLo / (gHi + gLo)) *
    (1 - pHi) ^ (gHi / (gHi + gLo))

/-- Success-side weighted geometric base for two Bernoulli probabilities. -/
def weightedBernoulliSuccessBase (gHi gLo pHi pLo : ℝ) : ℝ :=
  pLo ^ (gLo / (gHi + gLo)) *
    pHi ^ (gHi / (gHi + gLo))

/-- Closed-rate base for the weighted two-Bernoulli threshold problem. -/
def weightedBernoulliClosedRateBase (gHi gLo pHi pLo : ℝ) : ℝ :=
  weightedBernoulliFailureBase gHi gLo pHi pLo +
    weightedBernoulliSuccessBase gHi gLo pHi pLo

/--
Equal-weight Bernoulli Hellinger/Bhattacharyya base between two success
probabilities.  This is the `gHi = gLo = 1` specialization of the closed-rate
base, written without fractional powers.
-/
def bernoulliHellingerBase (pLo pHi : ℝ) : ℝ :=
  Real.sqrt ((1 - pLo) * (1 - pHi)) + Real.sqrt (pLo * pHi)

/--
First endpoint split that equalizes the endpoint rate from `0` to the split
with the equal-weight closed rate from the split to `pHi`.
-/
def bernoulliFirstEndpointEqualSplit (pHi : ℝ) : ℝ :=
  (1 - Real.sqrt (1 - pHi)) / 2

/--
Last endpoint split that equalizes the equal-weight closed rate from `pLo` to
the split with the endpoint rate from the split to `1`.
-/
def bernoulliLastEndpointEqualSplit (pLo : ℝ) : ℝ :=
  (1 + Real.sqrt pLo) / 2

/-- Failure-side squared gap used by the equal-weight interior split. -/
def bernoulliInteriorFailureSplitNumerator (pLo pHi : ℝ) : ℝ :=
  (Real.sqrt (1 - pLo) - Real.sqrt (1 - pHi)) ^ 2

/-- Success-side squared gap used by the equal-weight interior split. -/
def bernoulliInteriorSuccessSplitNumerator (pLo pHi : ℝ) : ℝ :=
  (Real.sqrt pHi - Real.sqrt pLo) ^ 2

/-- Denominator of the equal-weight interior split. -/
def bernoulliInteriorSplitDenominator (pLo pHi : ℝ) : ℝ :=
  bernoulliInteriorFailureSplitNumerator pLo pHi +
    bernoulliInteriorSuccessSplitNumerator pLo pHi

/--
Interior split that equalizes the two equal-weight Bernoulli Hellinger bases
inside an interval.
-/
def bernoulliInteriorEqualSplit (pLo pHi : ℝ) : ℝ :=
  bernoulliInteriorFailureSplitNumerator pLo pHi /
    bernoulliInteriorSplitDenominator pLo pHi

/--
Interior threshold selected by the weighted geometric Bernoulli minimizer.
It is the success-side base normalized by the sum of success and failure bases.
-/
def weightedBernoulliCommonThreshold (gHi gLo pHi pLo : ℝ) : ℝ :=
  weightedBernoulliSuccessBase gHi gLo pHi pLo /
    weightedBernoulliClosedRateBase gHi gLo pHi pLo

/-- Closed weighted two-Bernoulli threshold rate. -/
def weightedBernoulliClosedThresholdRate (gHi gLo pHi pLo : ℝ) : ℝ :=
  -(gHi + gLo) *
    Real.log (weightedBernoulliClosedRateBase gHi gLo pHi pLo)

/-- Equal weights turn the closed-rate base into the Hellinger base. -/
theorem weightedBernoulliClosedRateBase_one_one_eq_bernoulliHellingerBase
    {pHi pLo : ℝ} (hpHi0 : 0 ≤ pHi) (hpHi1 : pHi ≤ 1)
    (hpLo0 : 0 ≤ pLo) (hpLo1 : pLo ≤ 1) :
    weightedBernoulliClosedRateBase 1 1 pHi pLo =
      bernoulliHellingerBase pLo pHi := by
  have hpHi_fail_nonneg : 0 ≤ 1 - pHi := by linarith
  have hpLo_fail_nonneg : 0 ≤ 1 - pLo := by linarith
  dsimp [weightedBernoulliClosedRateBase, weightedBernoulliFailureBase,
    weightedBernoulliSuccessBase, bernoulliHellingerBase]
  norm_num
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  rw [← Real.mul_rpow hpLo_fail_nonneg hpHi_fail_nonneg,
    ← Real.mul_rpow hpLo0 hpHi0]

theorem bernoulliFirstEndpointEqualSplit_nonneg
    {pHi : ℝ} (hpHi0 : 0 ≤ pHi) (hpHi1 : pHi ≤ 1) :
    0 ≤ bernoulliFirstEndpointEqualSplit pHi := by
  have hrad_nonneg : 0 ≤ 1 - pHi := by linarith
  have hrad_le_one : 1 - pHi ≤ 1 := by linarith
  have hsqrt_le_one : Real.sqrt (1 - pHi) ≤ 1 := by
    exact (Real.sqrt_le_one).mpr hrad_le_one
  dsimp [bernoulliFirstEndpointEqualSplit]
  nlinarith

theorem bernoulliFirstEndpointEqualSplit_le_half
    {pHi : ℝ} :
    bernoulliFirstEndpointEqualSplit pHi ≤ 1 / 2 := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt (1 - pHi) := Real.sqrt_nonneg _
  dsimp [bernoulliFirstEndpointEqualSplit]
  nlinarith

theorem bernoulliFirstEndpointEqualSplit_lt_one
    {pHi : ℝ} :
    bernoulliFirstEndpointEqualSplit pHi < 1 := by
  have hle : bernoulliFirstEndpointEqualSplit pHi ≤ 1 / 2 :=
    bernoulliFirstEndpointEqualSplit_le_half
  linarith

theorem bernoulliFirstEndpointEqualSplit_le
    {pHi : ℝ} (hpHi0 : 0 ≤ pHi) (hpHi1 : pHi ≤ 1) :
    bernoulliFirstEndpointEqualSplit pHi ≤ pHi := by
  let s : ℝ := Real.sqrt (1 - pHi)
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hs_le_one : s ≤ 1 := by
    simpa [s] using (Real.sqrt_le_one).mpr (by linarith : 1 - pHi ≤ 1)
  have hpHi_eq : pHi = 1 - s ^ 2 := by
    dsimp [s]
    rw [Real.sq_sqrt (by linarith)]
    ring
  have hsplit : bernoulliFirstEndpointEqualSplit pHi = (1 - s) / 2 := by
    rfl
  rw [hsplit, hpHi_eq]
  nlinarith [mul_nonneg (sub_nonneg.mpr hs_le_one)
    (by nlinarith : (0 : ℝ) ≤ 1 + 2 * s)]

theorem bernoulliFirstEndpointEqualSplit_mem_Ioo
    {pHi : ℝ} (hpHi0 : 0 < pHi) (hpHi1 : pHi ≤ 1) :
    bernoulliFirstEndpointEqualSplit pHi ∈ Set.Ioo (0 : ℝ) pHi := by
  let s : ℝ := Real.sqrt (1 - pHi)
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hs_lt_one : s < 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by linarith : 0 ≤ 1 - pHi) (by linarith : 1 - pHi < 1)
  have hpHi_eq : pHi = 1 - s ^ 2 := by
    dsimp [s]
    rw [Real.sq_sqrt (by linarith : 0 ≤ 1 - pHi)]
    ring
  have hsplit : bernoulliFirstEndpointEqualSplit pHi = (1 - s) / 2 := by
    rfl
  constructor
  · rw [hsplit]
    linarith
  · rw [hsplit, hpHi_eq]
    nlinarith [mul_pos (sub_pos.mpr hs_lt_one)
      (by nlinarith : (0 : ℝ) < 1 + 2 * s)]

theorem bernoulliLastEndpointEqualSplit_nonneg
    {pLo : ℝ} :
    0 ≤ bernoulliLastEndpointEqualSplit pLo := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt pLo := Real.sqrt_nonneg _
  dsimp [bernoulliLastEndpointEqualSplit]
  nlinarith

theorem bernoulliLastEndpointEqualSplit_le_one
    {pLo : ℝ} (hpLo1 : pLo ≤ 1) :
    bernoulliLastEndpointEqualSplit pLo ≤ 1 := by
  have hpLo_nonneg_or := le_total 0 pLo
  by_cases hpLo0 : 0 ≤ pLo
  · have hsqrt_le_one : Real.sqrt pLo ≤ 1 := by
      exact (Real.sqrt_le_one).mpr hpLo1
    dsimp [bernoulliLastEndpointEqualSplit]
    nlinarith
  · have hsqrt_eq : Real.sqrt pLo = 0 := Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hpLo0)
    dsimp [bernoulliLastEndpointEqualSplit]
    rw [hsqrt_eq]
    norm_num

theorem le_bernoulliLastEndpointEqualSplit
    {pLo : ℝ} (hpLo0 : 0 ≤ pLo) (hpLo1 : pLo ≤ 1) :
    pLo ≤ bernoulliLastEndpointEqualSplit pLo := by
  let s : ℝ := Real.sqrt pLo
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hs_le_one : s ≤ 1 := by
    simpa [s] using (Real.sqrt_le_one).mpr hpLo1
  have hpLo_eq : pLo = s ^ 2 := by
    dsimp [s]
    rw [Real.sq_sqrt hpLo0]
  have hsplit : bernoulliLastEndpointEqualSplit pLo = (1 + s) / 2 := by
    rfl
  rw [hsplit, hpLo_eq]
  nlinarith [mul_nonneg hs_nonneg (sub_nonneg.mpr hs_le_one)]

theorem bernoulliLastEndpointEqualSplit_mem_Ioo
    {pLo : ℝ} (hpLo0 : 0 ≤ pLo) (hpLo1 : pLo < 1) :
    bernoulliLastEndpointEqualSplit pLo ∈ Set.Ioo pLo (1 : ℝ) := by
  let s : ℝ := Real.sqrt pLo
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hs_lt_one : s < 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt hpLo0 hpLo1
  have hpLo_eq : pLo = s ^ 2 := by
    dsimp [s]
    rw [Real.sq_sqrt hpLo0]
  have hsplit : bernoulliLastEndpointEqualSplit pLo = (1 + s) / 2 := by
    rfl
  constructor
  · rw [hsplit, hpLo_eq]
    nlinarith [mul_pos (sub_pos.mpr hs_lt_one)
      (by nlinarith : (0 : ℝ) < 1 + 2 * s)]
  · rw [hsplit]
    linarith

theorem bernoulliInteriorFailureSplitNumerator_pos
    {pLo pHi : ℝ} (hpHi1 : pHi ≤ 1) (hlt : pLo < pHi) :
    0 < bernoulliInteriorFailureSplitNumerator pLo pHi := by
  have hradHi_nonneg : 0 ≤ 1 - pHi := by linarith
  have hsqrt_lt :
      Real.sqrt (1 - pHi) < Real.sqrt (1 - pLo) :=
    Real.sqrt_lt_sqrt hradHi_nonneg (by linarith : 1 - pHi < 1 - pLo)
  dsimp [bernoulliInteriorFailureSplitNumerator]
  exact sq_pos_of_pos (sub_pos.mpr hsqrt_lt)

theorem bernoulliInteriorSuccessSplitNumerator_pos
    {pLo pHi : ℝ} (hpLo0 : 0 ≤ pLo) (hlt : pLo < pHi) :
    0 < bernoulliInteriorSuccessSplitNumerator pLo pHi := by
  have hsqrt_lt : Real.sqrt pLo < Real.sqrt pHi :=
    Real.sqrt_lt_sqrt hpLo0 hlt
  dsimp [bernoulliInteriorSuccessSplitNumerator]
  exact sq_pos_of_pos (sub_pos.mpr hsqrt_lt)

theorem bernoulliInteriorSplitDenominator_pos
    {pLo pHi : ℝ} (hpLo0 : 0 ≤ pLo) (hpHi1 : pHi ≤ 1)
    (hlt : pLo < pHi) :
    0 < bernoulliInteriorSplitDenominator pLo pHi := by
  dsimp [bernoulliInteriorSplitDenominator]
  exact add_pos
    (bernoulliInteriorFailureSplitNumerator_pos hpHi1 hlt)
    (bernoulliInteriorSuccessSplitNumerator_pos hpLo0 hlt)

theorem bernoulliInteriorEqualSplit_pos
    {pLo pHi : ℝ} (hpLo0 : 0 ≤ pLo) (hpHi1 : pHi ≤ 1)
    (hlt : pLo < pHi) :
    0 < bernoulliInteriorEqualSplit pLo pHi := by
  dsimp [bernoulliInteriorEqualSplit]
  exact div_pos
    (bernoulliInteriorFailureSplitNumerator_pos hpHi1 hlt)
    (bernoulliInteriorSplitDenominator_pos hpLo0 hpHi1 hlt)

theorem bernoulliInteriorEqualSplit_lt_one
    {pLo pHi : ℝ} (hpLo0 : 0 ≤ pLo) (hpHi1 : pHi ≤ 1)
    (hlt : pLo < pHi) :
    bernoulliInteriorEqualSplit pLo pHi < 1 := by
  have hden_pos := bernoulliInteriorSplitDenominator_pos hpLo0 hpHi1 hlt
  have hsucc_pos := bernoulliInteriorSuccessSplitNumerator_pos hpLo0 hlt
  have hden_sum_pos :
      0 <
        bernoulliInteriorFailureSplitNumerator pLo pHi +
          bernoulliInteriorSuccessSplitNumerator pLo pHi := by
    simpa [bernoulliInteriorSplitDenominator] using hden_pos
  dsimp [bernoulliInteriorEqualSplit, bernoulliInteriorSplitDenominator]
  rw [div_lt_one hden_sum_pos]
  linarith

theorem bernoulliInteriorEqualSplit_mem_Ioo
    {pLo pHi : ℝ} (hpLo0 : 0 ≤ pLo) (hpHi1 : pHi ≤ 1)
    (hlt : pLo < pHi) :
    bernoulliInteriorEqualSplit pLo pHi ∈ Set.Ioo pLo pHi := by
  let x : ℝ := Real.sqrt pHi
  let z : ℝ := Real.sqrt pLo
  let y : ℝ := Real.sqrt (1 - pHi)
  let w : ℝ := Real.sqrt (1 - pLo)
  let a : ℝ := w - y
  let b : ℝ := x - z
  let A : ℝ := a ^ 2
  let B : ℝ := b ^ 2
  let D : ℝ := A + B
  have hpHi0 : 0 ≤ pHi := le_trans hpLo0 hlt.le
  have hpLo1 : pLo ≤ 1 := le_trans hlt.le hpHi1
  have hpLo_lt_one : pLo < 1 := lt_of_lt_of_le hlt hpHi1
  have hfailLo0 : 0 ≤ 1 - pLo := by linarith
  have hfailHi0 : 0 ≤ 1 - pHi := by linarith
  have hx_nonneg : 0 ≤ x := Real.sqrt_nonneg _
  have hz_nonneg : 0 ≤ z := Real.sqrt_nonneg _
  have hy_nonneg : 0 ≤ y := Real.sqrt_nonneg _
  have hw_nonneg : 0 ≤ w := Real.sqrt_nonneg _
  have hx_pos : 0 < x := Real.sqrt_pos.mpr (lt_of_le_of_lt hpLo0 hlt)
  have hw_pos : 0 < w := Real.sqrt_pos.mpr (by linarith : 0 < 1 - pLo)
  have hz_lt_x : z < x := by
    dsimp [z, x]
    exact Real.sqrt_lt_sqrt hpLo0 hlt
  have hy_lt_w : y < w := by
    dsimp [y, w]
    exact Real.sqrt_lt_sqrt hfailHi0 (by linarith : 1 - pHi < 1 - pLo)
  have ha_pos : 0 < a := by
    dsimp [a]
    linarith
  have hb_pos : 0 < b := by
    dsimp [b]
    linarith
  have hpLo_eq : pLo = z ^ 2 := by
    dsimp [z]
    rw [Real.sq_sqrt hpLo0]
  have hpHi_eq : pHi = x ^ 2 := by
    dsimp [x]
    rw [Real.sq_sqrt hpHi0]
  have hunit_wz : w ^ 2 + z ^ 2 = 1 := by
    dsimp [w, z]
    rw [Real.sq_sqrt hfailLo0, Real.sq_sqrt hpLo0]
    ring
  have hunit_yx : y ^ 2 + x ^ 2 = 1 := by
    dsimp [y, x]
    rw [Real.sq_sqrt hfailHi0, Real.sq_sqrt hpHi0]
    ring
  have hdet_pos : 0 < w * x - z * y := by
    have hzy_le_zw : z * y ≤ z * w :=
      mul_le_mul_of_nonneg_left (le_of_lt hy_lt_w) hz_nonneg
    have hzw_lt_xw : z * w < x * w :=
      mul_lt_mul_of_pos_right hz_lt_x hw_pos
    nlinarith
  have hinner_nonneg : 0 ≤ w * y + z * x := by
    exact add_nonneg
      (mul_nonneg hw_nonneg hy_nonneg)
      (mul_nonneg hz_nonneg hx_nonneg)
  have hsq_identity :
      (w * y + z * x) ^ 2 + (w * x - z * y) ^ 2 =
        (w ^ 2 + z ^ 2) * (y ^ 2 + x ^ 2) := by
    ring
  have hdet_sq_pos : 0 < (w * x - z * y) ^ 2 :=
    sq_pos_of_pos hdet_pos
  have hinner_sq_lt_one : (w * y + z * x) ^ 2 < 1 := by
    nlinarith
  have hinner_lt_one : w * y + z * x < 1 := by
    by_contra hnot
    have hge : 1 ≤ w * y + z * x := le_of_not_gt hnot
    have hsq_ge : 1 ≤ (w * y + z * x) ^ 2 := by
      nlinarith
    linarith
  have hA_eq :
      bernoulliInteriorFailureSplitNumerator pLo pHi = A := by
    dsimp [bernoulliInteriorFailureSplitNumerator, A, a, w, y]
  have hD_eq :
      bernoulliInteriorSplitDenominator pLo pHi = D := by
    dsimp [bernoulliInteriorSplitDenominator,
      bernoulliInteriorFailureSplitNumerator,
      bernoulliInteriorSuccessSplitNumerator, A, B, D, a, b, w, y, x, z]
  have hD_pos : 0 < D := by
    dsimp [D, A, B]
    exact add_pos (sq_pos_of_pos ha_pos) (sq_pos_of_pos hb_pos)
  have hlow_first :
      w * a - z * b = 1 - (w * y + z * x) := by
    calc
      w * a - z * b = (w ^ 2 + z ^ 2) - (w * y + z * x) := by
        dsimp [a, b]
        ring
      _ = 1 - (w * y + z * x) := by rw [hunit_wz]
  have hlow_second_pos : 0 < w * a + z * b := by
    have hwa_pos : 0 < w * a := mul_pos hw_pos ha_pos
    have hzb_nonneg : 0 ≤ z * b := mul_nonneg hz_nonneg (le_of_lt hb_pos)
    exact add_pos_of_pos_of_nonneg hwa_pos hzb_nonneg
  have hlow_diff_pos : 0 < A - pLo * D := by
    have hfactor :
        A - pLo * D = (w * a - z * b) * (w * a + z * b) := by
      have hw_sq : w ^ 2 = 1 - z ^ 2 := by nlinarith [hunit_wz]
      calc
        A - pLo * D = w ^ 2 * a ^ 2 - z ^ 2 * b ^ 2 := by
          rw [hpLo_eq]
          dsimp [A, B, D]
          rw [hw_sq]
          ring
        _ = (w * a - z * b) * (w * a + z * b) := by
          ring
    rw [hfactor]
    exact mul_pos (by rw [hlow_first]; linarith) hlow_second_pos
  have hhi_first :
      x * b - y * a = 1 - (w * y + z * x) := by
    calc
      x * b - y * a = (y ^ 2 + x ^ 2) - (w * y + z * x) := by
        dsimp [a, b]
        ring
      _ = 1 - (w * y + z * x) := by rw [hunit_yx]
  have hhi_second_pos : 0 < x * b + y * a := by
    have hxb_pos : 0 < x * b := mul_pos hx_pos hb_pos
    have hya_nonneg : 0 ≤ y * a := mul_nonneg hy_nonneg (le_of_lt ha_pos)
    exact add_pos_of_pos_of_nonneg hxb_pos hya_nonneg
  have hhi_diff_pos : 0 < pHi * D - A := by
    have hfactor :
        pHi * D - A = (x * b - y * a) * (x * b + y * a) := by
      have hy_sq : y ^ 2 = 1 - x ^ 2 := by nlinarith [hunit_yx]
      calc
        pHi * D - A = x ^ 2 * b ^ 2 - y ^ 2 * a ^ 2 := by
          rw [hpHi_eq]
          dsimp [A, B, D]
          rw [hy_sq]
          ring
        _ = (x * b - y * a) * (x * b + y * a) := by
          ring
    rw [hfactor]
    exact mul_pos (by rw [hhi_first]; linarith) hhi_second_pos
  constructor
  · dsimp [bernoulliInteriorEqualSplit]
    rw [hA_eq, hD_eq]
    rw [lt_div_iff₀ hD_pos]
    linarith
  · dsimp [bernoulliInteriorEqualSplit]
    rw [hA_eq, hD_eq]
    rw [div_lt_iff₀ hD_pos]
    linarith

theorem one_sub_bernoulliInteriorEqualSplit_eq_success_div
    {pLo pHi : ℝ}
    (hden : bernoulliInteriorSplitDenominator pLo pHi ≠ 0) :
    1 - bernoulliInteriorEqualSplit pLo pHi =
      bernoulliInteriorSuccessSplitNumerator pLo pHi /
        bernoulliInteriorSplitDenominator pLo pHi := by
  have hsum_ne :
      bernoulliInteriorFailureSplitNumerator pLo pHi +
          bernoulliInteriorSuccessSplitNumerator pLo pHi ≠ 0 := by
    simpa [bernoulliInteriorSplitDenominator] using hden
  dsimp [bernoulliInteriorEqualSplit, bernoulliInteriorSplitDenominator]
  field_simp [hsum_ne]
  ring_nf

theorem sqrt_bernoulliInteriorEqualSplit_eq_failure_gap_div_sqrt_den
    {pLo pHi : ℝ} (hpLo0 : 0 ≤ pLo) (hpHi1 : pHi ≤ 1)
    (hlt : pLo < pHi) :
    Real.sqrt (bernoulliInteriorEqualSplit pLo pHi) =
      (Real.sqrt (1 - pLo) - Real.sqrt (1 - pHi)) /
        Real.sqrt (bernoulliInteriorSplitDenominator pLo pHi) := by
  have hden_pos := bernoulliInteriorSplitDenominator_pos hpLo0 hpHi1 hlt
  have hradHi_nonneg : 0 ≤ 1 - pHi := by linarith
  have hgap_nonneg :
      0 ≤ Real.sqrt (1 - pLo) - Real.sqrt (1 - pHi) := by
    exact le_of_lt
      (sub_pos.mpr
        (Real.sqrt_lt_sqrt hradHi_nonneg (by linarith : 1 - pHi < 1 - pLo)))
  dsimp [bernoulliInteriorEqualSplit,
    bernoulliInteriorFailureSplitNumerator]
  rw [Real.sqrt_div (sq_nonneg _) (bernoulliInteriorSplitDenominator pLo pHi)]
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hgap_nonneg]

theorem sqrt_one_sub_bernoulliInteriorEqualSplit_eq_success_gap_div_sqrt_den
    {pLo pHi : ℝ} (hpLo0 : 0 ≤ pLo) (hpHi1 : pHi ≤ 1)
    (hlt : pLo < pHi) :
    Real.sqrt (1 - bernoulliInteriorEqualSplit pLo pHi) =
      (Real.sqrt pHi - Real.sqrt pLo) /
        Real.sqrt (bernoulliInteriorSplitDenominator pLo pHi) := by
  have hden_pos := bernoulliInteriorSplitDenominator_pos hpLo0 hpHi1 hlt
  have hden_ne : bernoulliInteriorSplitDenominator pLo pHi ≠ 0 :=
    ne_of_gt hden_pos
  have hgap_nonneg : 0 ≤ Real.sqrt pHi - Real.sqrt pLo := by
    exact le_of_lt (sub_pos.mpr (Real.sqrt_lt_sqrt hpLo0 hlt))
  rw [one_sub_bernoulliInteriorEqualSplit_eq_success_div hden_ne]
  dsimp [bernoulliInteriorSuccessSplitNumerator]
  rw [Real.sqrt_div (sq_nonneg _) (bernoulliInteriorSplitDenominator pLo pHi)]
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hgap_nonneg]

theorem bernoulliHellingerBase_left_interiorEqualSplit_eq_common_div
    {pLo pHi : ℝ} (hpLo0 : 0 ≤ pLo) (hpHi1 : pHi ≤ 1)
    (hlt : pLo < pHi) :
    bernoulliHellingerBase pLo (bernoulliInteriorEqualSplit pLo pHi) =
      (Real.sqrt (1 - pLo) * Real.sqrt pHi -
          Real.sqrt pLo * Real.sqrt (1 - pHi)) /
        Real.sqrt (bernoulliInteriorSplitDenominator pLo pHi) := by
  let mid : ℝ := bernoulliInteriorEqualSplit pLo pHi
  have hpHi0 : 0 ≤ pHi := le_trans hpLo0 hlt.le
  have hpLo1 : pLo ≤ 1 := le_trans hlt.le hpHi1
  have hfailLo_nonneg : 0 ≤ 1 - pLo := by linarith
  have hden_pos := bernoulliInteriorSplitDenominator_pos hpLo0 hpHi1 hlt
  have hsqrt_den_pos :
      0 < Real.sqrt (bernoulliInteriorSplitDenominator pLo pHi) :=
    Real.sqrt_pos.mpr hden_pos
  have hmid_nonneg : 0 ≤ mid := by
    exact le_of_lt (by
      dsimp [mid]
      exact bernoulliInteriorEqualSplit_pos hpLo0 hpHi1 hlt)
  have hmid_lt_one : mid < 1 := by
    dsimp [mid]
    exact bernoulliInteriorEqualSplit_lt_one hpLo0 hpHi1 hlt
  have hs_mid :
      Real.sqrt mid =
        (Real.sqrt (1 - pLo) - Real.sqrt (1 - pHi)) /
          Real.sqrt (bernoulliInteriorSplitDenominator pLo pHi) := by
    dsimp [mid]
    exact sqrt_bernoulliInteriorEqualSplit_eq_failure_gap_div_sqrt_den
      hpLo0 hpHi1 hlt
  have hs_one_mid :
      Real.sqrt (1 - mid) =
        (Real.sqrt pHi - Real.sqrt pLo) /
          Real.sqrt (bernoulliInteriorSplitDenominator pLo pHi) := by
    dsimp [mid]
    exact sqrt_one_sub_bernoulliInteriorEqualSplit_eq_success_gap_div_sqrt_den
      hpLo0 hpHi1 hlt
  dsimp [bernoulliHellingerBase, mid]
  rw [Real.sqrt_mul hfailLo_nonneg (1 - bernoulliInteriorEqualSplit pLo pHi)]
  rw [Real.sqrt_mul hpLo0 (bernoulliInteriorEqualSplit pLo pHi)]
  rw [hs_one_mid, hs_mid]
  field_simp [ne_of_gt hsqrt_den_pos]
  ring

theorem bernoulliHellingerBase_right_interiorEqualSplit_eq_common_div
    {pLo pHi : ℝ} (hpLo0 : 0 ≤ pLo) (hpHi1 : pHi ≤ 1)
    (hlt : pLo < pHi) :
    bernoulliHellingerBase (bernoulliInteriorEqualSplit pLo pHi) pHi =
      (Real.sqrt (1 - pLo) * Real.sqrt pHi -
          Real.sqrt pLo * Real.sqrt (1 - pHi)) /
        Real.sqrt (bernoulliInteriorSplitDenominator pLo pHi) := by
  let mid : ℝ := bernoulliInteriorEqualSplit pLo pHi
  have hpHi0 : 0 ≤ pHi := le_trans hpLo0 hlt.le
  have hfailHi_nonneg : 0 ≤ 1 - pHi := by linarith
  have hden_pos := bernoulliInteriorSplitDenominator_pos hpLo0 hpHi1 hlt
  have hsqrt_den_pos :
      0 < Real.sqrt (bernoulliInteriorSplitDenominator pLo pHi) :=
    Real.sqrt_pos.mpr hden_pos
  have hmid_nonneg : 0 ≤ mid := by
    exact le_of_lt (by
      dsimp [mid]
      exact bernoulliInteriorEqualSplit_pos hpLo0 hpHi1 hlt)
  have hmid_lt_one : mid < 1 := by
    dsimp [mid]
    exact bernoulliInteriorEqualSplit_lt_one hpLo0 hpHi1 hlt
  have hone_mid_nonneg : 0 ≤ 1 - mid := by linarith
  have hs_mid :
      Real.sqrt mid =
        (Real.sqrt (1 - pLo) - Real.sqrt (1 - pHi)) /
          Real.sqrt (bernoulliInteriorSplitDenominator pLo pHi) := by
    dsimp [mid]
    exact sqrt_bernoulliInteriorEqualSplit_eq_failure_gap_div_sqrt_den
      hpLo0 hpHi1 hlt
  have hs_one_mid :
      Real.sqrt (1 - mid) =
        (Real.sqrt pHi - Real.sqrt pLo) /
          Real.sqrt (bernoulliInteriorSplitDenominator pLo pHi) := by
    dsimp [mid]
    exact sqrt_one_sub_bernoulliInteriorEqualSplit_eq_success_gap_div_sqrt_den
      hpLo0 hpHi1 hlt
  dsimp [bernoulliHellingerBase, mid]
  rw [Real.sqrt_mul hone_mid_nonneg (1 - pHi)]
  rw [Real.sqrt_mul hmid_nonneg pHi]
  rw [hs_one_mid, hs_mid]
  field_simp [ne_of_gt hsqrt_den_pos]
  ring

/--
For the equal-weight interior split, the squared Hellinger base on either
refined half equals `(1 + oldBase) / 2`.  This is the algebraic rate-doubling
identity used in Lemma C.5-style binary rating arguments.
-/
theorem bernoulliHellingerBase_left_interiorEqualSplit_sq_eq_one_add_base_div_two
    {pLo pHi : ℝ} (hpLo0 : 0 ≤ pLo) (hpHi1 : pHi ≤ 1)
    (hlt : pLo < pHi) :
    (bernoulliHellingerBase pLo (bernoulliInteriorEqualSplit pLo pHi)) ^ 2 =
      (1 + bernoulliHellingerBase pLo pHi) / 2 := by
  let a : ℝ := Real.sqrt (1 - pLo)
  let b : ℝ := Real.sqrt (1 - pHi)
  let c : ℝ := Real.sqrt pLo
  let d : ℝ := Real.sqrt pHi
  let H : ℝ := a * b + c * d
  let D : ℝ := (a - b) ^ 2 + (d - c) ^ 2
  let N : ℝ := a * d - c * b
  have hpHi0 : 0 ≤ pHi := le_trans hpLo0 hlt.le
  have hpLo1 : pLo ≤ 1 := le_trans hlt.le hpHi1
  have ha2 : a ^ 2 = 1 - pLo := by
    dsimp [a]
    rw [Real.sq_sqrt (by linarith : 0 ≤ 1 - pLo)]
  have hb2 : b ^ 2 = 1 - pHi := by
    dsimp [b]
    rw [Real.sq_sqrt (by linarith : 0 ≤ 1 - pHi)]
  have hc2 : c ^ 2 = pLo := by
    dsimp [c]
    rw [Real.sq_sqrt hpLo0]
  have hd2 : d ^ 2 = pHi := by
    dsimp [d]
    rw [Real.sq_sqrt hpHi0]
  have hac : a ^ 2 + c ^ 2 = 1 := by linarith
  have hbd : b ^ 2 + d ^ 2 = 1 := by linarith
  have hbase : bernoulliHellingerBase pLo pHi = H := by
    dsimp [bernoulliHellingerBase, H, a, b, c, d]
    rw [Real.sqrt_mul (by linarith : 0 ≤ 1 - pLo) (1 - pHi)]
    rw [Real.sqrt_mul hpLo0 pHi]
  have hD_pos :
      0 < D := by
    dsimp [D, a, b, c, d]
    exact bernoulliInteriorSplitDenominator_pos hpLo0 hpHi1 hlt
  have hsqrtD_pos : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD_pos
  have hleft :
      bernoulliHellingerBase pLo (bernoulliInteriorEqualSplit pLo pHi) =
        N / Real.sqrt D := by
    have h :=
      bernoulliHellingerBase_left_interiorEqualSplit_eq_common_div
        hpLo0 hpHi1 hlt
    simpa [N, D, a, b, c, d] using h
  have hD : D = 2 * (1 - H) := by
    dsimp [D, H]
    nlinarith [hac, hbd]
  have hN_sq : N ^ 2 = 1 - H ^ 2 := by
    dsimp [N, H]
    nlinarith [hac, hbd]
  have hOneMinusH_pos : 0 < 1 - H := by
    nlinarith [hD_pos, hD]
  calc
    (bernoulliHellingerBase pLo (bernoulliInteriorEqualSplit pLo pHi)) ^ 2 =
        (N / Real.sqrt D) ^ 2 := by rw [hleft]
    _ = N ^ 2 / D := by
        rw [div_pow, Real.sq_sqrt hD_pos.le]
    _ = (1 - H ^ 2) / (2 * (1 - H)) := by rw [hN_sq, hD]
    _ = (1 + H) / 2 := by
        field_simp [ne_of_gt hOneMinusH_pos]
        ring
    _ = (1 + bernoulliHellingerBase pLo pHi) / 2 := by rw [hbase]

theorem bernoulliHellingerBase_interiorEqualSplit_eq
    {pLo pHi : ℝ} (hpLo0 : 0 ≤ pLo) (hpHi1 : pHi ≤ 1)
    (hlt : pLo < pHi) :
    bernoulliHellingerBase pLo (bernoulliInteriorEqualSplit pLo pHi) =
      bernoulliHellingerBase (bernoulliInteriorEqualSplit pLo pHi) pHi := by
  rw [bernoulliHellingerBase_left_interiorEqualSplit_eq_common_div
      hpLo0 hpHi1 hlt,
    bernoulliHellingerBase_right_interiorEqualSplit_eq_common_div
      hpLo0 hpHi1 hlt]

/--
The interior equal split equalizes the two equal-weight Bernoulli closed-rate
bases on the left and right subintervals.
-/
theorem weightedBernoulliClosedRateBase_one_one_interiorEqualSplit_eq
    {pLo pHi : ℝ} (hpLo0 : 0 ≤ pLo) (hpHi1 : pHi ≤ 1)
    (hlt : pLo < pHi) :
    weightedBernoulliClosedRateBase 1 1
        (bernoulliInteriorEqualSplit pLo pHi) pLo =
      weightedBernoulliClosedRateBase 1 1
        pHi (bernoulliInteriorEqualSplit pLo pHi) := by
  let mid : ℝ := bernoulliInteriorEqualSplit pLo pHi
  have hpHi0 : 0 ≤ pHi := le_trans hpLo0 hlt.le
  have hpLo1 : pLo ≤ 1 := le_trans hlt.le hpHi1
  have hmid0 : 0 ≤ mid := by
    exact le_of_lt (by
      dsimp [mid]
      exact bernoulliInteriorEqualSplit_pos hpLo0 hpHi1 hlt)
  have hmid1 : mid ≤ 1 := by
    exact le_of_lt (by
      dsimp [mid]
      exact bernoulliInteriorEqualSplit_lt_one hpLo0 hpHi1 hlt)
  have hleft :
      weightedBernoulliClosedRateBase 1 1 mid pLo =
        bernoulliHellingerBase pLo mid :=
    weightedBernoulliClosedRateBase_one_one_eq_bernoulliHellingerBase
      hmid0 hmid1 hpLo0 hpLo1
  have hright :
      weightedBernoulliClosedRateBase 1 1 pHi mid =
        bernoulliHellingerBase mid pHi :=
    weightedBernoulliClosedRateBase_one_one_eq_bernoulliHellingerBase
      hpHi0 hpHi1 hmid0 hmid1
  rw [show bernoulliInteriorEqualSplit pLo pHi = mid from rfl]
  rw [hleft, hright]
  exact bernoulliHellingerBase_interiorEqualSplit_eq hpLo0 hpHi1 hlt

/--
The interior equal split equalizes the two equal-weight Bernoulli closed
threshold rates on the left and right subintervals.
-/
theorem weightedBernoulliClosedThresholdRate_one_one_interiorEqualSplit_eq
    {pLo pHi : ℝ} (hpLo0 : 0 ≤ pLo) (hpHi1 : pHi ≤ 1)
    (hlt : pLo < pHi) :
    weightedBernoulliClosedThresholdRate 1 1
        (bernoulliInteriorEqualSplit pLo pHi) pLo =
      weightedBernoulliClosedThresholdRate 1 1
        pHi (bernoulliInteriorEqualSplit pLo pHi) := by
  unfold weightedBernoulliClosedThresholdRate
  rw [weightedBernoulliClosedRateBase_one_one_interiorEqualSplit_eq
    hpLo0 hpHi1 hlt]

/--
The first endpoint split makes the equal-weight Hellinger base from the split
to `pHi` equal to the square root of the endpoint survival mass.
-/
theorem bernoulliHellingerBase_firstEndpointEqualSplit_eq_sqrt_one_sub
    {pHi : ℝ} (hpHi0 : 0 ≤ pHi) (hpHi1 : pHi ≤ 1) :
    bernoulliHellingerBase (bernoulliFirstEndpointEqualSplit pHi) pHi =
      Real.sqrt (1 - bernoulliFirstEndpointEqualSplit pHi) := by
  let s : ℝ := Real.sqrt (1 - pHi)
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hs_le_one : s ≤ 1 := by
    simpa [s] using (Real.sqrt_le_one).mpr (by linarith : 1 - pHi ≤ 1)
  have hpHi_eq : pHi = 1 - s ^ 2 := by
    dsimp [s]
    rw [Real.sq_sqrt (by linarith : 0 ≤ 1 - pHi)]
    ring
  have hsplit : bernoulliFirstEndpointEqualSplit pHi = (1 - s) / 2 := by
    rfl
  have hone_minus_split :
      1 - bernoulliFirstEndpointEqualSplit pHi = (1 + s) / 2 := by
    rw [hsplit]
    ring
  have hbase :
      bernoulliHellingerBase (bernoulliFirstEndpointEqualSplit pHi) pHi =
        Real.sqrt (((1 + s) / 2) * s ^ 2) +
          Real.sqrt (((1 - s) / 2) * (1 - s ^ 2)) := by
    dsimp [bernoulliHellingerBase]
    rw [hsplit, hpHi_eq]
    congr 2
    ring
  have hmid_nonneg : 0 ≤ (1 + s) / 2 := by nlinarith
  have hterm1 :
      Real.sqrt (((1 + s) / 2) * s ^ 2) =
        s * Real.sqrt ((1 + s) / 2) := by
    rw [Real.sqrt_mul hmid_nonneg (s ^ 2)]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hs_nonneg]
    ring
  have harg2 :
      ((1 - s) / 2) * (1 - s ^ 2) =
        (1 - s) ^ 2 * ((1 + s) / 2) := by
    ring
  have hterm2 :
      Real.sqrt (((1 - s) / 2) * (1 - s ^ 2)) =
        (1 - s) * Real.sqrt ((1 + s) / 2) := by
    rw [harg2]
    rw [Real.sqrt_mul (sq_nonneg (1 - s)) ((1 + s) / 2)]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (sub_nonneg.mpr hs_le_one)]
  rw [hbase, hone_minus_split, hterm1, hterm2]
  ring

/--
The first endpoint split equalizes the endpoint rate from zero with the
equal-weight closed threshold rate to the next level.
-/
theorem weightedBernoulliClosedThresholdRate_one_one_firstEndpointEqualSplit_eq
    {pHi : ℝ} (hpHi0 : 0 ≤ pHi) (hpHi1 : pHi ≤ 1) :
    weightedBernoulliClosedThresholdRate 1 1 pHi
        (bernoulliFirstEndpointEqualSplit pHi) =
      -Real.log (1 - bernoulliFirstEndpointEqualSplit pHi) := by
  let mid : ℝ := bernoulliFirstEndpointEqualSplit pHi
  have hmid0 : 0 ≤ mid := by
    dsimp [mid]
    exact bernoulliFirstEndpointEqualSplit_nonneg hpHi0 hpHi1
  have hmid_lt_one : mid < 1 := by
    dsimp [mid]
    exact bernoulliFirstEndpointEqualSplit_lt_one
  have hmid1 : mid ≤ 1 := le_of_lt hmid_lt_one
  have hx_pos : 0 < 1 - mid := by linarith
  have hbase :
      weightedBernoulliClosedRateBase 1 1 pHi mid =
        Real.sqrt (1 - mid) := by
    calc
      weightedBernoulliClosedRateBase 1 1 pHi mid =
          bernoulliHellingerBase mid pHi :=
            weightedBernoulliClosedRateBase_one_one_eq_bernoulliHellingerBase
              hpHi0 hpHi1 hmid0 hmid1
      _ = Real.sqrt (1 - mid) := by
            dsimp [mid]
            exact bernoulliHellingerBase_firstEndpointEqualSplit_eq_sqrt_one_sub
              hpHi0 hpHi1
  have hlog_sqrt :
      Real.log (1 - mid) = 2 * Real.log (Real.sqrt (1 - mid)) := by
    have hsqrt_pos : 0 < Real.sqrt (1 - mid) := Real.sqrt_pos.mpr hx_pos
    have hsqrt_mul :
        Real.sqrt (1 - mid) * Real.sqrt (1 - mid) = 1 - mid :=
      Real.mul_self_sqrt hx_pos.le
    calc
      Real.log (1 - mid) =
          Real.log (Real.sqrt (1 - mid) * Real.sqrt (1 - mid)) := by
            rw [hsqrt_mul]
      _ = 2 * Real.log (Real.sqrt (1 - mid)) := by
            rw [Real.log_mul (ne_of_gt hsqrt_pos) (ne_of_gt hsqrt_pos)]
            ring
  dsimp [weightedBernoulliClosedThresholdRate]
  rw [show bernoulliFirstEndpointEqualSplit pHi = mid from rfl, hbase]
  norm_num
  linarith

/--
The last endpoint split makes the equal-weight Hellinger base from `pLo` to
the split equal to the square root of the endpoint success mass.
-/
theorem bernoulliHellingerBase_lastEndpointEqualSplit_eq_sqrt
    {pLo : ℝ} (hpLo0 : 0 ≤ pLo) (hpLo1 : pLo ≤ 1) :
    bernoulliHellingerBase pLo (bernoulliLastEndpointEqualSplit pLo) =
      Real.sqrt (bernoulliLastEndpointEqualSplit pLo) := by
  let s : ℝ := Real.sqrt pLo
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hs_le_one : s ≤ 1 := by
    simpa [s] using (Real.sqrt_le_one).mpr hpLo1
  have hpLo_eq : pLo = s ^ 2 := by
    dsimp [s]
    rw [Real.sq_sqrt hpLo0]
  have hsplit : bernoulliLastEndpointEqualSplit pLo = (1 + s) / 2 := by
    rfl
  have hone_minus_split :
      1 - bernoulliLastEndpointEqualSplit pLo = (1 - s) / 2 := by
    rw [hsplit]
    ring
  have hbase :
      bernoulliHellingerBase pLo (bernoulliLastEndpointEqualSplit pLo) =
        Real.sqrt ((1 - s ^ 2) * ((1 - s) / 2)) +
          Real.sqrt (s ^ 2 * ((1 + s) / 2)) := by
    dsimp [bernoulliHellingerBase]
    rw [hsplit, hpLo_eq]
    congr 2
    ring
  have hmid_nonneg : 0 ≤ (1 + s) / 2 := by nlinarith
  have harg1 :
      (1 - s ^ 2) * ((1 - s) / 2) =
        (1 - s) ^ 2 * ((1 + s) / 2) := by
    ring
  have hterm1 :
      Real.sqrt ((1 - s ^ 2) * ((1 - s) / 2)) =
        (1 - s) * Real.sqrt ((1 + s) / 2) := by
    rw [harg1]
    rw [Real.sqrt_mul (sq_nonneg (1 - s)) ((1 + s) / 2)]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (sub_nonneg.mpr hs_le_one)]
  have hterm2 :
      Real.sqrt (s ^ 2 * ((1 + s) / 2)) =
        s * Real.sqrt ((1 + s) / 2) := by
    rw [Real.sqrt_mul (sq_nonneg s) ((1 + s) / 2)]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hs_nonneg]
  rw [hbase, hsplit, hterm1, hterm2]
  ring

/--
The last endpoint split equalizes the equal-weight closed threshold rate from
the previous level with the endpoint rate to one.
-/
theorem weightedBernoulliClosedThresholdRate_one_one_lastEndpointEqualSplit_eq
    {pLo : ℝ} (hpLo0 : 0 ≤ pLo) (hpLo1 : pLo ≤ 1) :
    weightedBernoulliClosedThresholdRate 1 1
        (bernoulliLastEndpointEqualSplit pLo) pLo =
      -Real.log (bernoulliLastEndpointEqualSplit pLo) := by
  let mid : ℝ := bernoulliLastEndpointEqualSplit pLo
  have hmid0 : 0 ≤ mid := by
    dsimp [mid]
    exact bernoulliLastEndpointEqualSplit_nonneg
  have hmid_pos : 0 < mid := by
    dsimp [mid, bernoulliLastEndpointEqualSplit]
    nlinarith [Real.sqrt_nonneg pLo]
  have hmid1 : mid ≤ 1 := by
    dsimp [mid]
    exact bernoulliLastEndpointEqualSplit_le_one hpLo1
  have hbase :
      weightedBernoulliClosedRateBase 1 1 mid pLo =
        Real.sqrt mid := by
    calc
      weightedBernoulliClosedRateBase 1 1 mid pLo =
          bernoulliHellingerBase pLo mid :=
            weightedBernoulliClosedRateBase_one_one_eq_bernoulliHellingerBase
              hmid0 hmid1 hpLo0 hpLo1
      _ = Real.sqrt mid := by
            dsimp [mid]
            exact bernoulliHellingerBase_lastEndpointEqualSplit_eq_sqrt
              hpLo0 hpLo1
  have hlog_sqrt :
      Real.log mid = 2 * Real.log (Real.sqrt mid) := by
    have hsqrt_pos : 0 < Real.sqrt mid := Real.sqrt_pos.mpr hmid_pos
    have hsqrt_mul : Real.sqrt mid * Real.sqrt mid = mid :=
      Real.mul_self_sqrt hmid_pos.le
    calc
      Real.log mid = Real.log (Real.sqrt mid * Real.sqrt mid) := by
            rw [hsqrt_mul]
      _ = 2 * Real.log (Real.sqrt mid) := by
            rw [Real.log_mul (ne_of_gt hsqrt_pos) (ne_of_gt hsqrt_pos)]
            ring
  dsimp [weightedBernoulliClosedThresholdRate]
  rw [show bernoulliLastEndpointEqualSplit pLo = mid from rfl, hbase]
  norm_num
  linarith

/--
Equal-weight fixed-width Bernoulli closed-rate base bound.  If two Bernoulli
success probabilities are `x` apart, their Bhattacharyya-type closed-rate base
is at least `sqrt (1 - x)`.
-/
theorem weightedBernoulliClosedRateBase_one_one_ge_sqrt_one_sub_width
    {pLo x : ℝ} (hpLo0 : 0 ≤ pLo) (hx0 : 0 ≤ x)
    (hhi1 : pLo + x ≤ 1) :
    Real.sqrt (1 - x) ≤
      weightedBernoulliClosedRateBase 1 1 (pLo + x) pLo := by
  let A : ℝ := (1 - pLo) * (1 - (pLo + x))
  let C : ℝ := pLo * (pLo + x)
  have hpHi0 : 0 ≤ pLo + x := add_nonneg hpLo0 hx0
  have hpLo1 : pLo ≤ 1 := by linarith
  have hx1 : x ≤ 1 := by linarith
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (by linarith) (by linarith)
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg hpLo0 hpHi0
  have hD_nonneg : 0 ≤ 1 - x := by linarith
  have hy_nonneg : 0 ≤ pLo * (1 - (pLo + x)) := by
    exact mul_nonneg hpLo0 (by linarith)
  have hcross_sq :
      (pLo * (1 - (pLo + x))) ^ 2 ≤ A * C := by
    dsimp [A, C]
    nlinarith [mul_nonneg hx0 hy_nonneg]
  have hcross :
      pLo * (1 - (pLo + x)) ≤ Real.sqrt (A * C) := by
    apply le_of_sq_le_sq
    · simpa [Real.sq_sqrt (mul_nonneg hA_nonneg hC_nonneg)] using hcross_sq
    · exact Real.sqrt_nonneg _
  have hD_eq :
      1 - x = A + C + 2 * (pLo * (1 - (pLo + x))) := by
    dsimp [A, C]
    ring
  have hD_le_sq :
      1 - x ≤ (Real.sqrt A + Real.sqrt C) ^ 2 := by
    have hsquare :
        (Real.sqrt A + Real.sqrt C) ^ 2 =
          A + C + 2 * Real.sqrt (A * C) := by
      rw [add_sq, Real.sq_sqrt hA_nonneg, Real.sq_sqrt hC_nonneg]
      have hmul : Real.sqrt (A * C) = Real.sqrt A * Real.sqrt C :=
        Real.sqrt_mul hA_nonneg C
      nlinarith
    rw [hsquare]
    calc
      1 - x = A + C + 2 * (pLo * (1 - (pLo + x))) := hD_eq
      _ ≤ A + C + 2 * Real.sqrt (A * C) := by nlinarith
  have hsum_nonneg : 0 ≤ Real.sqrt A + Real.sqrt C :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsqrt_le :
      Real.sqrt (1 - x) ≤ Real.sqrt A + Real.sqrt C := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) hsum_nonneg).mp
    rwa [Real.sq_sqrt hD_nonneg]
  have hbase :
      weightedBernoulliClosedRateBase 1 1 (pLo + x) pLo =
        Real.sqrt A + Real.sqrt C := by
    have hpLo_fail_nonneg : 0 ≤ 1 - pLo := by linarith
    have hpHi_fail_nonneg : 0 ≤ 1 - (pLo + x) := by linarith
    dsimp [weightedBernoulliClosedRateBase, weightedBernoulliFailureBase,
      weightedBernoulliSuccessBase, A, C]
    norm_num
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    rw [← Real.mul_rpow hpLo_fail_nonneg hpHi_fail_nonneg,
      ← Real.mul_rpow hpLo0 hpHi0]
  simpa [hbase]
    using hsqrt_le

/--
Equal-weight Bernoulli closed-rate base separation.  If two Bernoulli success
probabilities are `x` apart, their Bhattacharyya-type closed-rate base is at
most `sqrt (1 - x^2)`.
-/
theorem weightedBernoulliClosedRateBase_one_one_le_sqrt_one_sub_width_sq
    {pLo x : ℝ} (hpLo0 : 0 ≤ pLo) (hx0 : 0 ≤ x)
    (hhi1 : pLo + x ≤ 1) :
    weightedBernoulliClosedRateBase 1 1 (pLo + x) pLo ≤
      Real.sqrt (1 - x ^ 2) := by
  let a : ℝ := Real.sqrt (1 - pLo)
  let b : ℝ := Real.sqrt pLo
  let c : ℝ := Real.sqrt (1 - (pLo + x))
  let d : ℝ := Real.sqrt (pLo + x)
  have hpHi0 : 0 ≤ pLo + x := add_nonneg hpLo0 hx0
  have hpLo1 : pLo ≤ 1 := by linarith
  have hx1 : x ≤ 1 := by linarith
  have hfailLo : 0 ≤ 1 - pLo := by linarith
  have hfailHi : 0 ≤ 1 - (pLo + x) := by linarith
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hd0 : 0 ≤ d := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = 1 - pLo := by
    dsimp [a]
    exact Real.sq_sqrt hfailLo
  have hb2 : b ^ 2 = pLo := by
    dsimp [b]
    exact Real.sq_sqrt hpLo0
  have hc2 : c ^ 2 = 1 - (pLo + x) := by
    dsimp [c]
    exact Real.sq_sqrt hfailHi
  have hd2 : d ^ 2 = pLo + x := by
    dsimp [d]
    exact Real.sq_sqrt hpHi0
  have hbase :
      weightedBernoulliClosedRateBase 1 1 (pLo + x) pLo =
        a * c + b * d := by
    rw [weightedBernoulliClosedRateBase_one_one_eq_bernoulliHellingerBase
      hpHi0 hhi1 hpLo0 hpLo1]
    dsimp [bernoulliHellingerBase, a, b, c, d]
    rw [Real.sqrt_mul hfailLo, Real.sqrt_mul hpLo0]
  have hdet_sq :
      (a * d - b * c) ^ 2 = 1 - (a * c + b * d) ^ 2 := by
    have hnorm_lo : a ^ 2 + b ^ 2 = 1 := by
      rw [ha2, hb2]
      ring
    have hnorm_hi : c ^ 2 + d ^ 2 = 1 := by
      rw [hc2, hd2]
      ring
    nlinarith [sq_nonneg (a * c + b * d),
      sq_nonneg (a * d - b * c)]
  have hdet_nonneg : 0 ≤ a * d - b * c := by
    have hsq :
        (b * c) ^ 2 ≤ (a * d) ^ 2 := by
      rw [mul_pow, mul_pow, hb2, hc2, ha2, hd2]
      nlinarith [hpLo0, hx0, hhi1]
    exact sub_nonneg.mpr
      ((sq_le_sq₀ (mul_nonneg hb0 hc0) (mul_nonneg ha0 hd0)).mp hsq)
  have hcross_le_one : a * d + b * c ≤ 1 := by
    have hnonneg : 0 ≤ a * d + b * c :=
      add_nonneg (mul_nonneg ha0 hd0) (mul_nonneg hb0 hc0)
    have hsq :
        (a * d + b * c) ^ 2 ≤ 1 := by
      have hcs :
          (a * d + b * c) ^ 2 ≤ (a ^ 2 + b ^ 2) * (d ^ 2 + c ^ 2) := by
        nlinarith [sq_nonneg (a * c - b * d)]
      have hnorm :
          (a ^ 2 + b ^ 2) * (d ^ 2 + c ^ 2) = 1 := by
        rw [ha2, hb2, hd2, hc2]
        ring
      exact hcs.trans_eq hnorm
    exact (sq_le_one_iff₀ hnonneg).mp hsq
  have hx_eq :
      x = (a * d - b * c) * (a * d + b * c) := by
    symm
    calc
      (a * d - b * c) * (a * d + b * c)
          = a ^ 2 * d ^ 2 - b ^ 2 * c ^ 2 := by ring
      _ = x := by
            rw [ha2, hb2, hc2, hd2]
            ring
  have hx_le_det : x ≤ a * d - b * c := by
    rw [hx_eq]
    have hdet_cross_nonneg :
        0 ≤ (a * d - b * c) * (a * d + b * c) :=
      mul_nonneg hdet_nonneg
        (add_nonneg (mul_nonneg ha0 hd0) (mul_nonneg hb0 hc0))
    calc
      (a * d - b * c) * (a * d + b * c)
          ≤ (a * d - b * c) * 1 :=
            mul_le_mul_of_nonneg_left hcross_le_one hdet_nonneg
      _ = a * d - b * c := by ring
  have hx_sq_le_det_sq : x ^ 2 ≤ (a * d - b * c) ^ 2 :=
    (sq_le_sq₀ hx0 hdet_nonneg).mpr hx_le_det
  have hbase_sq_le :
      (a * c + b * d) ^ 2 ≤ 1 - x ^ 2 := by
    nlinarith [hdet_sq, hx_sq_le_det_sq]
  have hbase_nonneg : 0 ≤ a * c + b * d :=
    add_nonneg (mul_nonneg ha0 hc0) (mul_nonneg hb0 hd0)
  have hrad_nonneg : 0 ≤ 1 - x ^ 2 := by
    nlinarith [sq_nonneg x, mul_self_le_mul_self hx0 hx1]
  rw [hbase]
  exact (sq_le_sq₀ hbase_nonneg (Real.sqrt_nonneg _)).mp
    (by simpa [Real.sq_sqrt hrad_nonneg] using hbase_sq_le)

/--
Equal-weight fixed-width Bernoulli closed-rate bound.  This is the reusable
algebraic inequality for equal-weight endpoint chains: the equal-weight interior
closed threshold rate for a width-`x` Bernoulli interval is at most the last
endpoint rate with the same width.
-/
theorem weightedBernoulliClosedThresholdRate_one_one_le_neg_log_one_sub_width
    {pLo x : ℝ} (hpLo0 : 0 ≤ pLo) (hx0 : 0 ≤ x)
    (hhi1 : pLo + x ≤ 1) (hx1 : x < 1) :
    weightedBernoulliClosedThresholdRate 1 1 (pLo + x) pLo ≤
      -Real.log (1 - x) := by
  let B : ℝ := weightedBernoulliClosedRateBase 1 1 (pLo + x) pLo
  have hD_pos : 0 < 1 - x := by linarith
  have hsqrt_pos : 0 < Real.sqrt (1 - x) := Real.sqrt_pos.mpr hD_pos
  have hB_ge : Real.sqrt (1 - x) ≤ B := by
    dsimp [B]
    exact
      weightedBernoulliClosedRateBase_one_one_ge_sqrt_one_sub_width
        hpLo0 hx0 hhi1
  have hB_pos : 0 < B := hsqrt_pos.trans_le hB_ge
  have hlog_le : Real.log (Real.sqrt (1 - x)) ≤ Real.log B :=
    Real.log_le_log hsqrt_pos hB_ge
  have hlog_sqrt :
      Real.log (1 - x) = 2 * Real.log (Real.sqrt (1 - x)) := by
    have hsqrt_mul :
        Real.sqrt (1 - x) * Real.sqrt (1 - x) = 1 - x :=
      Real.mul_self_sqrt hD_pos.le
    calc
      Real.log (1 - x) =
          Real.log (Real.sqrt (1 - x) * Real.sqrt (1 - x)) := by
            rw [hsqrt_mul]
      _ = 2 * Real.log (Real.sqrt (1 - x)) := by
            rw [Real.log_mul (ne_of_gt hsqrt_pos) (ne_of_gt hsqrt_pos)]
            ring
  dsimp [weightedBernoulliClosedThresholdRate, B] at hB_pos hlog_le ⊢
  norm_num
  nlinarith

/--
Equal-weight fixed-width Bernoulli closed-rate lower bound.  If two Bernoulli
success probabilities are `x` apart, the equal-weight closed threshold rate is
at least `-log (1 - x^2)`.
-/
theorem weightedBernoulliClosedThresholdRate_one_one_ge_neg_log_one_sub_width_sq
    {pLo x : ℝ} (hpLo0 : 0 ≤ pLo) (hx0 : 0 ≤ x)
    (hhi1 : pLo + x ≤ 1) (hx1 : x < 1) :
    -Real.log (1 - x ^ 2) ≤
      weightedBernoulliClosedThresholdRate 1 1 (pLo + x) pLo := by
  let B : ℝ := weightedBernoulliClosedRateBase 1 1 (pLo + x) pLo
  have hD_pos : 0 < 1 - x ^ 2 := by
    have hx_sq_lt : x ^ 2 < 1 := (sq_lt_one_iff₀ hx0).mpr hx1
    linarith
  have hsqrtD_pos : 0 < Real.sqrt (1 - x ^ 2) :=
    Real.sqrt_pos.mpr hD_pos
  have hone_sub_x_pos : 0 < 1 - x := by linarith
  have hsqrt_one_sub_x_pos : 0 < Real.sqrt (1 - x) :=
    Real.sqrt_pos.mpr hone_sub_x_pos
  have hB_ge : Real.sqrt (1 - x) ≤ B := by
    dsimp [B]
    exact
      weightedBernoulliClosedRateBase_one_one_ge_sqrt_one_sub_width
        hpLo0 hx0 hhi1
  have hB_pos : 0 < B := hsqrt_one_sub_x_pos.trans_le hB_ge
  have hB_le : B ≤ Real.sqrt (1 - x ^ 2) := by
    dsimp [B]
    exact
      weightedBernoulliClosedRateBase_one_one_le_sqrt_one_sub_width_sq
        hpLo0 hx0 hhi1
  have hlog_le :
      Real.log B ≤ Real.log (Real.sqrt (1 - x ^ 2)) :=
    Real.log_le_log hB_pos hB_le
  have hlog_sqrt :
      Real.log (1 - x ^ 2) =
        2 * Real.log (Real.sqrt (1 - x ^ 2)) := by
    have hsqrt_mul :
        Real.sqrt (1 - x ^ 2) * Real.sqrt (1 - x ^ 2) =
          1 - x ^ 2 :=
      Real.mul_self_sqrt hD_pos.le
    calc
      Real.log (1 - x ^ 2) =
          Real.log
            (Real.sqrt (1 - x ^ 2) * Real.sqrt (1 - x ^ 2)) := by
            rw [hsqrt_mul]
      _ = 2 * Real.log (Real.sqrt (1 - x ^ 2)) := by
            rw [Real.log_mul (ne_of_gt hsqrtD_pos) (ne_of_gt hsqrtD_pos)]
            ring
  dsimp [weightedBernoulliClosedThresholdRate, B] at hB_pos hlog_le ⊢
  norm_num
  nlinarith

/-- Derivative of the closed-rate base with respect to the lower endpoint. -/
theorem weightedBernoulliClosedRateBase_hasDerivAt_lo
    {gHi gLo pHi pLo : ℝ} (hpLo0 : 0 < pLo) (hpLo1 : pLo < 1) :
    HasDerivAt
      (fun x : ℝ => weightedBernoulliClosedRateBase gHi gLo pHi x)
      (((-1) * (gLo / (gHi + gLo)) *
            (1 - pLo) ^ (gLo / (gHi + gLo) - 1)) *
          (1 - pHi) ^ (gHi / (gHi + gLo)) +
        ((gLo / (gHi + gLo)) *
            pLo ^ (gLo / (gHi + gLo) - 1)) *
          pHi ^ (gHi / (gHi + gLo))) pLo := by
  let aLo := gLo / (gHi + gLo)
  let aHi := gHi / (gHi + gLo)
  have hfail_var :
      HasDerivAt (fun x : ℝ => (1 - x) ^ aLo)
        ((-1) * aLo * (1 - pLo) ^ (aLo - 1)) pLo := by
    have hbase : HasDerivAt (fun x : ℝ => 1 - x) (-1) pLo := by
      simpa using (hasDerivAt_const (c := (1 : ℝ)) pLo).sub
        (hasDerivAt_id pLo)
    simpa using
      hbase.rpow_const (p := aLo)
        (Or.inl (ne_of_gt (sub_pos.mpr hpLo1)))
  have hfail :
      HasDerivAt
        (fun x : ℝ => (1 - x) ^ aLo * (1 - pHi) ^ aHi)
        (((-1) * aLo * (1 - pLo) ^ (aLo - 1)) *
          (1 - pHi) ^ aHi) pLo :=
    hfail_var.mul_const ((1 - pHi) ^ aHi)
  have hsucc_var :
      HasDerivAt (fun x : ℝ => x ^ aLo)
        ((gLo / (gHi + gLo)) *
          pLo ^ (gLo / (gHi + gLo) - 1)) pLo := by
    simpa [aLo] using
      (hasDerivAt_id pLo).rpow_const (p := aLo)
        (Or.inl hpLo0.ne')
  have hsucc :
      HasDerivAt
        (fun x : ℝ => x ^ aLo * pHi ^ aHi)
        (((gLo / (gHi + gLo)) *
          pLo ^ (gLo / (gHi + gLo) - 1)) *
          pHi ^ aHi) pLo :=
    hsucc_var.mul_const (pHi ^ aHi)
  simpa [weightedBernoulliClosedRateBase, weightedBernoulliFailureBase,
    weightedBernoulliSuccessBase, aLo, aHi, add_comm, add_left_comm, add_assoc]
    using hfail.add hsucc

/-- Derivative of the closed-rate base with respect to the higher endpoint. -/
theorem weightedBernoulliClosedRateBase_hasDerivAt_hi
    {gHi gLo pHi pLo : ℝ} (hpHi0 : 0 < pHi) (hpHi1 : pHi < 1) :
    HasDerivAt
      (fun x : ℝ => weightedBernoulliClosedRateBase gHi gLo x pLo)
      ((1 - pLo) ^ (gLo / (gHi + gLo)) *
          ((-1) * (gHi / (gHi + gLo)) *
            (1 - pHi) ^ (gHi / (gHi + gLo) - 1)) +
        pLo ^ (gLo / (gHi + gLo)) *
          ((gHi / (gHi + gLo)) *
            pHi ^ (gHi / (gHi + gLo) - 1))) pHi := by
  let aLo := gLo / (gHi + gLo)
  let aHi := gHi / (gHi + gLo)
  have hfail_var :
      HasDerivAt (fun x : ℝ => (1 - x) ^ aHi)
        ((-1) * aHi * (1 - pHi) ^ (aHi - 1)) pHi := by
    have hbase : HasDerivAt (fun x : ℝ => 1 - x) (-1) pHi := by
      simpa using (hasDerivAt_const (c := (1 : ℝ)) pHi).sub
        (hasDerivAt_id pHi)
    simpa using
      hbase.rpow_const (p := aHi)
        (Or.inl (ne_of_gt (sub_pos.mpr hpHi1)))
  have hfail :
      HasDerivAt
        (fun x : ℝ => (1 - pLo) ^ aLo * (1 - x) ^ aHi)
        ((1 - pLo) ^ aLo *
          ((-1) * aHi * (1 - pHi) ^ (aHi - 1))) pHi :=
    hfail_var.const_mul ((1 - pLo) ^ aLo)
  have hsucc_var :
      HasDerivAt (fun x : ℝ => x ^ aHi)
        ((gHi / (gHi + gLo)) *
          pHi ^ (gHi / (gHi + gLo) - 1)) pHi := by
    simpa [aHi] using
      (hasDerivAt_id pHi).rpow_const (p := aHi)
        (Or.inl hpHi0.ne')
  have hsucc :
      HasDerivAt
        (fun x : ℝ => pLo ^ aLo * x ^ aHi)
        (pLo ^ aLo *
          ((gHi / (gHi + gLo)) *
            pHi ^ (gHi / (gHi + gLo) - 1))) pHi :=
    hsucc_var.const_mul (pLo ^ aLo)
  simpa [weightedBernoulliClosedRateBase, weightedBernoulliFailureBase,
    weightedBernoulliSuccessBase, aLo, aHi, add_comm, add_left_comm, add_assoc,
    mul_comm, mul_left_comm, mul_assoc] using hfail.add hsucc

/--
Interior inverse for the Bernoulli binary log-MGF derivative.
-/
theorem finiteLogMGF_realBernoulliPMF_binaryRatingScore_hasDerivAt_inverse
    (p a : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (ha0 : 0 < a) (ha1 : a < 1) :
    HasDerivAt
      (fun t : ℝ =>
        finiteLogMGF (realBernoulliPMF p hp0.le hp1.le) binaryRatingScore t)
      a (binaryLogMGFDerivativeArg p a) := by
  have hbase_pos :
      0 < a * (1 - p) / (p * (1 - a)) := by
    exact div_pos
      (mul_pos ha0 (sub_pos.mpr hp1))
      (mul_pos hp0 (sub_pos.mpr ha1))
  have hexp :
      Real.exp (binaryLogMGFDerivativeArg p a) =
        a * (1 - p) / (p * (1 - a)) := by
    simp [binaryLogMGFDerivativeArg, Real.exp_log hbase_pos]
  have hderiv :=
    finiteLogMGF_realBernoulliPMF_binaryRatingScore_hasDerivAt
      p (binaryLogMGFDerivativeArg p a) hp0.le hp1.le
  convert hderiv using 1
  rw [hexp]
  field_simp [ne_of_gt hp0, ne_of_gt (sub_pos.mpr hp1),
    ne_of_gt (sub_pos.mpr ha1)]
  ring_nf

/-- The Bernoulli inverse-dual parameter is nonpositive when the target is below `p`. -/
theorem binaryLogMGFDerivativeArg_nonpos_of_le
    {p a : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (ha0 : 0 < a) (ha1 : a < 1) (ha_le : a ≤ p) :
    binaryLogMGFDerivativeArg p a ≤ 0 := by
  have hnum_nonneg : 0 ≤ a * (1 - p) :=
    mul_nonneg ha0.le (sub_nonneg.mpr hp1.le)
  have hden_pos : 0 < p * (1 - a) :=
    mul_pos hp0 (sub_pos.mpr ha1)
  have hratio_nonneg : 0 ≤ a * (1 - p) / (p * (1 - a)) :=
    div_nonneg hnum_nonneg hden_pos.le
  have hnum_le_den : a * (1 - p) ≤ p * (1 - a) := by
    nlinarith [ha_le]
  have hratio_le_one : a * (1 - p) / (p * (1 - a)) ≤ 1 :=
    (div_le_one hden_pos).mpr hnum_le_den
  simpa [binaryLogMGFDerivativeArg] using
    Real.log_nonpos hratio_nonneg hratio_le_one

/-- The Bernoulli inverse-dual parameter is nonnegative when the target is above `p`. -/
theorem binaryLogMGFDerivativeArg_nonneg_of_ge
    {p a : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (ha0 : 0 < a) (ha1 : a < 1) (hp_le : p ≤ a) :
    0 ≤ binaryLogMGFDerivativeArg p a := by
  have hden_pos : 0 < p * (1 - a) :=
    mul_pos hp0 (sub_pos.mpr ha1)
  have hden_le_num : p * (1 - a) ≤ a * (1 - p) := by
    nlinarith [hp_le]
  have hone_le_ratio : 1 ≤ a * (1 - p) / (p * (1 - a)) :=
    (one_le_div hden_pos).mpr hden_le_num
  simpa [binaryLogMGFDerivativeArg] using
    Real.log_nonneg hone_le_ratio

/--
For `p ≤ a`, the Bernoulli KL exponent at threshold `a` is bounded by the
endpoint success exponent `-log p`. This is useful when a comparison against
the source endpoint `1` is dominated by a nearby interior threshold.
-/
theorem bernoulliKL_le_neg_log_of_le
    {p a : ℝ} (hp0 : 0 < p) (ha1 : a < 1) (hp_le : p ≤ a) :
    bernoulliKL a p ≤ -Real.log p := by
  have ha0 : 0 < a := hp0.trans_le hp_le
  have ha_nonneg : 0 ≤ a := ha0.le
  have ha_le_one : a ≤ 1 := ha1.le
  have hp1 : p < 1 := hp_le.trans_lt ha1
  have hp_ne : p ≠ 0 := ne_of_gt hp0
  have ha_ne : a ≠ 0 := ne_of_gt ha0
  have hpden_pos : 0 < 1 - p := sub_pos.mpr hp1
  have haden_pos : 0 < 1 - a := sub_pos.mpr ha1
  have hsuccess_ratio_ge_one : 1 ≤ a / p :=
    (one_le_div hp0).mpr hp_le
  have hsuccess_log_nonneg : 0 ≤ Real.log (a / p) :=
    Real.log_nonneg hsuccess_ratio_ge_one
  have hsuccess_ratio_le : a / p ≤ 1 / p :=
    div_le_div_of_nonneg_right ha_le_one hp0.le
  have hsuccess_log_le :
      Real.log (a / p) ≤ -Real.log p := by
    have hlog :
        Real.log (a / p) ≤ Real.log (1 / p) :=
      Real.log_le_log (div_pos ha0 hp0) hsuccess_ratio_le
    rw [Real.log_div one_ne_zero hp_ne] at hlog
    simpa using hlog
  have hsuccess_term_le :
      a * Real.log (a / p) ≤ -Real.log p := by
    have hmul :
        a * Real.log (a / p) ≤ 1 * Real.log (a / p) :=
      mul_le_mul_of_nonneg_right ha_le_one hsuccess_log_nonneg
    linarith
  have hfailure_ratio_nonneg :
      0 ≤ (1 - a) / (1 - p) :=
    div_nonneg (sub_nonneg.mpr ha_le_one) hpden_pos.le
  have hfailure_ratio_le_one :
      (1 - a) / (1 - p) ≤ 1 := by
    have hnum_le_den : 1 - a ≤ 1 - p := by
      linarith
    exact (div_le_one hpden_pos).mpr hnum_le_den
  have hfailure_log_nonpos :
      Real.log ((1 - a) / (1 - p)) ≤ 0 :=
    Real.log_nonpos hfailure_ratio_nonneg hfailure_ratio_le_one
  have hfailure_term_nonpos :
      (1 - a) * Real.log ((1 - a) / (1 - p)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ha_le_one)
      hfailure_log_nonpos
  unfold bernoulliKL
  linarith

/-- Bernoulli KL is zero when the two Bernoulli means agree. -/
theorem bernoulliKL_self {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    bernoulliKL p p = 0 := by
  have hp_ne : p ≠ 0 := ne_of_gt hp0
  have hfail_ne : 1 - p ≠ 0 := ne_of_gt (sub_pos.mpr hp1)
  unfold bernoulliKL
  rw [div_self hp_ne, div_self hfail_ne, Real.log_one]
  ring

/-- Bernoulli log-odds is monotone on the open unit interval. -/
theorem bernoulliLogOdds_le_of_le
    {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hq0 : 0 < q) (hq1 : q < 1) (hpq : p ≤ q) :
    bernoulliLogOdds p ≤ bernoulliLogOdds q := by
  have hpden_pos : 0 < 1 - p := sub_pos.mpr hp1
  have hqden_pos : 0 < 1 - q := sub_pos.mpr hq1
  have hodds_le : p / (1 - p) ≤ q / (1 - q) := by
    rw [div_le_div_iff₀ hpden_pos hqden_pos]
    nlinarith
  exact Real.log_le_log (div_pos hp0 hpden_pos) hodds_le

/-- Bernoulli log-odds is strictly monotone on the open unit interval. -/
theorem bernoulliLogOdds_lt_of_lt
    {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hq0 : 0 < q) (hq1 : q < 1) (hpq : p < q) :
    bernoulliLogOdds p < bernoulliLogOdds q := by
  have hpden_pos : 0 < 1 - p := sub_pos.mpr hp1
  have hqden_pos : 0 < 1 - q := sub_pos.mpr hq1
  have hodds_lt : p / (1 - p) < q / (1 - q) := by
    rw [div_lt_div_iff₀ hpden_pos hqden_pos]
    nlinarith
  exact Real.log_lt_log (div_pos hp0 hpden_pos) hodds_lt

/-- The failure-side weighted geometric base is positive for interior probabilities. -/
theorem weightedBernoulliFailureBase_pos
    {gHi gLo pHi pLo : ℝ} (hpHi1 : pHi < 1) (hpLo1 : pLo < 1) :
    0 < weightedBernoulliFailureBase gHi gLo pHi pLo := by
  dsimp [weightedBernoulliFailureBase]
  exact mul_pos
    (Real.rpow_pos_of_pos (sub_pos.mpr hpLo1) _)
    (Real.rpow_pos_of_pos (sub_pos.mpr hpHi1) _)

/-- The success-side weighted geometric base is positive for interior probabilities. -/
theorem weightedBernoulliSuccessBase_pos
    {gHi gLo pHi pLo : ℝ} (hpHi0 : 0 < pHi) (hpLo0 : 0 < pLo) :
    0 < weightedBernoulliSuccessBase gHi gLo pHi pLo := by
  dsimp [weightedBernoulliSuccessBase]
  exact mul_pos
    (Real.rpow_pos_of_pos hpLo0 _)
    (Real.rpow_pos_of_pos hpHi0 _)

/-- The weighted two-Bernoulli closed-rate base is positive for interior probabilities. -/
theorem weightedBernoulliClosedRateBase_pos
    {gHi gLo pHi pLo : ℝ}
    (hpHi0 : 0 < pHi) (hpHi1 : pHi < 1)
    (hpLo0 : 0 < pLo) (hpLo1 : pLo < 1) :
    0 < weightedBernoulliClosedRateBase gHi gLo pHi pLo := by
  exact add_pos
    (weightedBernoulliFailureBase_pos hpHi1 hpLo1)
    (weightedBernoulliSuccessBase_pos hpHi0 hpLo0)

/--
Interior C.5 rate transform: the equal-weight split rate on the left refined
half is `-log ((1 + exp (-oldRate/2)) / 2)`, where `oldRate` is the
equal-weight closed threshold rate on the original interval.
-/
theorem weightedBernoulliClosedThresholdRate_one_one_interiorEqualSplit_left_eq_transform
    {pLo pHi : ℝ} (hpLo0 : 0 < pLo) (hpHi1 : pHi < 1)
    (hlt : pLo < pHi) :
    weightedBernoulliClosedThresholdRate 1 1
        (bernoulliInteriorEqualSplit pLo pHi) pLo =
      -Real.log
        ((1 +
          Real.exp
            (-(weightedBernoulliClosedThresholdRate 1 1 pHi pLo) / 2)) / 2) := by
  let mid : ℝ := bernoulliInteriorEqualSplit pLo pHi
  let H : ℝ := bernoulliHellingerBase pLo pHi
  let B : ℝ := weightedBernoulliClosedRateBase 1 1 mid pLo
  have hpLo0' : 0 ≤ pLo := le_of_lt hpLo0
  have hpHi1' : pHi ≤ 1 := le_of_lt hpHi1
  have hpHi0 : 0 < pHi := lt_trans hpLo0 hlt
  have hpLo1 : pLo < 1 := lt_trans hlt hpHi1
  have hmid_mem := bernoulliInteriorEqualSplit_mem_Ioo hpLo0' hpHi1' hlt
  have hmid0 : 0 < mid := lt_trans hpLo0 hmid_mem.1
  have hmid1 : mid < 1 := lt_trans hmid_mem.2 hpHi1
  have hBpos : 0 < B := by
    dsimp [B, mid]
    exact weightedBernoulliClosedRateBase_pos hmid0 hmid1 hpLo0 hpLo1
  have hHpos : 0 < H := by
    dsimp [H]
    have hbase :
        weightedBernoulliClosedRateBase 1 1 pHi pLo =
          bernoulliHellingerBase pLo pHi :=
      weightedBernoulliClosedRateBase_one_one_eq_bernoulliHellingerBase
        (le_of_lt hpHi0) hpHi1' hpLo0' (le_of_lt hpLo1)
    rw [← hbase]
    exact weightedBernoulliClosedRateBase_pos hpHi0 hpHi1 hpLo0 hpLo1
  have hBsq : B ^ 2 = (1 + H) / 2 := by
    have hB :
        B = bernoulliHellingerBase pLo mid := by
      dsimp [B, mid]
      exact
        weightedBernoulliClosedRateBase_one_one_eq_bernoulliHellingerBase
          (le_of_lt hmid0) (le_of_lt hmid1) hpLo0' (le_of_lt hpLo1)
    dsimp [H]
    rw [hB]
    exact
      bernoulliHellingerBase_left_interiorEqualSplit_sq_eq_one_add_base_div_two
        hpLo0' hpHi1' hlt
  have holdRate :
      weightedBernoulliClosedThresholdRate 1 1 pHi pLo =
        -2 * Real.log H := by
    have hbase :
        weightedBernoulliClosedRateBase 1 1 pHi pLo = H := by
      dsimp [H]
      exact
        weightedBernoulliClosedRateBase_one_one_eq_bernoulliHellingerBase
          (le_of_lt hpHi0) hpHi1' hpLo0' (le_of_lt hpLo1)
    dsimp [weightedBernoulliClosedThresholdRate]
    rw [hbase]
    norm_num
  have hExp :
      Real.exp
          (-(weightedBernoulliClosedThresholdRate 1 1 pHi pLo) / 2) = H := by
    rw [holdRate]
    have harg : -(-2 * Real.log H) / 2 = Real.log H := by ring
    rw [harg, Real.exp_log hHpos]
  have hnewRate :
      weightedBernoulliClosedThresholdRate 1 1 mid pLo =
        -Real.log (B ^ 2) := by
    dsimp [weightedBernoulliClosedThresholdRate, B]
    norm_num
  rw [show bernoulliInteriorEqualSplit pLo pHi = mid from rfl]
  rw [hnewRate, hBsq, hExp]

/-- The closed-rate base is exactly one when the two Bernoulli laws coincide. -/
theorem weightedBernoulliClosedRateBase_self
    {gHi gLo p : ℝ} (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hp0 : 0 < p) (hp1 : p < 1) :
    weightedBernoulliClosedRateBase gHi gLo p p = 1 := by
  have hG_pos : 0 < gHi + gLo := add_pos hgHi hgLo
  have hG_ne : gHi + gLo ≠ 0 := ne_of_gt hG_pos
  have hsum : gLo / (gHi + gLo) + gHi / (gHi + gLo) = 1 := by
    field_simp [hG_ne]
    ring
  have hfail_pos : 0 < 1 - p := sub_pos.mpr hp1
  have hfailure :
      (1 - p) ^ (gLo / (gHi + gLo)) *
          (1 - p) ^ (gHi / (gHi + gLo)) =
        1 - p := by
    rw [← Real.rpow_add hfail_pos, hsum, Real.rpow_one]
  have hsuccess :
      p ^ (gLo / (gHi + gLo)) * p ^ (gHi / (gHi + gLo)) =
        p := by
    rw [← Real.rpow_add hp0, hsum, Real.rpow_one]
  rw [weightedBernoulliClosedRateBase, weightedBernoulliFailureBase,
    weightedBernoulliSuccessBase, hfailure, hsuccess]
  ring

/-- The closed threshold rate is zero when the two Bernoulli laws coincide. -/
theorem weightedBernoulliClosedThresholdRate_self
    {gHi gLo p : ℝ} (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hp0 : 0 < p) (hp1 : p < 1) :
    weightedBernoulliClosedThresholdRate gHi gLo p p = 0 := by
  rw [weightedBernoulliClosedThresholdRate,
    weightedBernoulliClosedRateBase_self hgHi hgLo hp0 hp1, Real.log_one]
  ring

/-- Swapping the two Bernoulli laws and their sample weights preserves the closed-rate base. -/
theorem weightedBernoulliClosedRateBase_swap
    (gHi gLo pHi pLo : ℝ) :
    weightedBernoulliClosedRateBase gHi gLo pHi pLo =
      weightedBernoulliClosedRateBase gLo gHi pLo pHi := by
  simp [weightedBernoulliClosedRateBase,
    weightedBernoulliFailureBase, weightedBernoulliSuccessBase,
    add_comm, mul_comm]

/-- Swapping the two Bernoulli laws and their sample weights preserves the closed threshold rate. -/
theorem weightedBernoulliClosedThresholdRate_swap
    (gHi gLo pHi pLo : ℝ) :
    weightedBernoulliClosedThresholdRate gHi gLo pHi pLo =
      weightedBernoulliClosedThresholdRate gLo gHi pLo pHi := by
  simp [weightedBernoulliClosedThresholdRate,
    weightedBernoulliClosedRateBase_swap, add_comm]

/--
The closed threshold rate is antitone in the closed-rate base: a larger
Bhattacharyya-style base gives a no larger large-deviation rate.
-/
theorem weightedBernoulliClosedThresholdRate_le_of_closedRateBase_le
    {gHi gLo pHi pLo pHi' pLo' : ℝ}
    (hG : 0 ≤ gHi + gLo)
    (hbase_pos :
      0 < weightedBernoulliClosedRateBase gHi gLo pHi pLo)
    (hbase_le :
      weightedBernoulliClosedRateBase gHi gLo pHi pLo ≤
        weightedBernoulliClosedRateBase gHi gLo pHi' pLo') :
    weightedBernoulliClosedThresholdRate gHi gLo pHi' pLo' ≤
      weightedBernoulliClosedThresholdRate gHi gLo pHi pLo := by
  have hlog :
      Real.log (weightedBernoulliClosedRateBase gHi gLo pHi pLo) ≤
        Real.log (weightedBernoulliClosedRateBase gHi gLo pHi' pLo') :=
    Real.log_le_log hbase_pos hbase_le
  have hneg :
      -Real.log (weightedBernoulliClosedRateBase gHi gLo pHi' pLo') ≤
        -Real.log (weightedBernoulliClosedRateBase gHi gLo pHi pLo) :=
    neg_le_neg hlog
  have hmul :
      (gHi + gLo) *
          (-Real.log (weightedBernoulliClosedRateBase gHi gLo pHi' pLo')) ≤
        (gHi + gLo) *
          (-Real.log (weightedBernoulliClosedRateBase gHi gLo pHi pLo)) :=
    mul_le_mul_of_nonneg_left hneg hG
  dsimp [weightedBernoulliClosedThresholdRate]
  nlinarith

/--
The closed threshold rate is strictly antitone in the closed-rate base when
the total sample weight is positive.
-/
theorem weightedBernoulliClosedThresholdRate_lt_of_closedRateBase_lt
    {gHi gLo pHi pLo pHi' pLo' : ℝ}
    (hG : 0 < gHi + gLo)
    (hbase_pos :
      0 < weightedBernoulliClosedRateBase gHi gLo pHi pLo)
    (hbase_lt :
      weightedBernoulliClosedRateBase gHi gLo pHi pLo <
        weightedBernoulliClosedRateBase gHi gLo pHi' pLo') :
    weightedBernoulliClosedThresholdRate gHi gLo pHi' pLo' <
      weightedBernoulliClosedThresholdRate gHi gLo pHi pLo := by
  have hlog :
      Real.log (weightedBernoulliClosedRateBase gHi gLo pHi pLo) <
        Real.log (weightedBernoulliClosedRateBase gHi gLo pHi' pLo') :=
    Real.log_lt_log hbase_pos hbase_lt
  have hneg :
      -Real.log (weightedBernoulliClosedRateBase gHi gLo pHi' pLo') <
        -Real.log (weightedBernoulliClosedRateBase gHi gLo pHi pLo) :=
    neg_lt_neg hlog
  have hmul :
      (gHi + gLo) *
          (-Real.log (weightedBernoulliClosedRateBase gHi gLo pHi' pLo')) <
        (gHi + gLo) *
          (-Real.log (weightedBernoulliClosedRateBase gHi gLo pHi pLo)) :=
    mul_lt_mul_of_pos_left hneg hG
  dsimp [weightedBernoulliClosedThresholdRate]
  nlinarith

/-- The weighted two-Bernoulli common threshold is positive. -/
theorem weightedBernoulliCommonThreshold_pos
    {gHi gLo pHi pLo : ℝ}
    (hpHi0 : 0 < pHi) (hpHi1 : pHi < 1)
    (hpLo0 : 0 < pLo) (hpLo1 : pLo < 1) :
    0 < weightedBernoulliCommonThreshold gHi gLo pHi pLo := by
  exact div_pos
    (weightedBernoulliSuccessBase_pos hpHi0 hpLo0)
    (weightedBernoulliClosedRateBase_pos hpHi0 hpHi1 hpLo0 hpLo1)

/-- The weighted two-Bernoulli common threshold is below one. -/
theorem weightedBernoulliCommonThreshold_lt_one
    {gHi gLo pHi pLo : ℝ}
    (hpHi0 : 0 < pHi) (hpHi1 : pHi < 1)
    (hpLo0 : 0 < pLo) (hpLo1 : pLo < 1) :
    weightedBernoulliCommonThreshold gHi gLo pHi pLo < 1 := by
  have hfailure_pos :
      0 < weightedBernoulliFailureBase gHi gLo pHi pLo :=
    weightedBernoulliFailureBase_pos hpHi1 hpLo1
  have hsuccess_pos :
      0 < weightedBernoulliSuccessBase gHi gLo pHi pLo :=
    weightedBernoulliSuccessBase_pos hpHi0 hpLo0
  have hden_pos :
      0 < weightedBernoulliClosedRateBase gHi gLo pHi pLo :=
    weightedBernoulliClosedRateBase_pos hpHi0 hpHi1 hpLo0 hpLo1
  rw [weightedBernoulliCommonThreshold]
  rw [div_lt_one hden_pos]
  dsimp [weightedBernoulliClosedRateBase]
  linarith

/-- Failure probability at the common threshold equals normalized failure base. -/
theorem one_sub_weightedBernoulliCommonThreshold_eq
    {gHi gLo pHi pLo : ℝ}
    (hpHi0 : 0 < pHi) (hpHi1 : pHi < 1)
    (hpLo0 : 0 < pLo) (hpLo1 : pLo < 1) :
    1 - weightedBernoulliCommonThreshold gHi gLo pHi pLo =
      weightedBernoulliFailureBase gHi gLo pHi pLo /
        weightedBernoulliClosedRateBase gHi gLo pHi pLo := by
  have hden_ne :
      weightedBernoulliClosedRateBase gHi gLo pHi pLo ≠ 0 :=
    ne_of_gt (weightedBernoulliClosedRateBase_pos hpHi0 hpHi1 hpLo0 hpLo1)
  have hden_ne' :
      weightedBernoulliSuccessBase gHi gLo pHi pLo +
          weightedBernoulliFailureBase gHi gLo pHi pLo ≠ 0 := by
    exact ne_of_gt
      (add_pos
        (weightedBernoulliSuccessBase_pos hpHi0 hpLo0)
        (weightedBernoulliFailureBase_pos hpHi1 hpLo1))
  rw [weightedBernoulliCommonThreshold]
  dsimp [weightedBernoulliClosedRateBase]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  rw [show weightedBernoulliFailureBase gHi gLo pHi pLo +
        weightedBernoulliSuccessBase gHi gLo pHi pLo =
      weightedBernoulliSuccessBase gHi gLo pHi pLo +
        weightedBernoulliFailureBase gHi gLo pHi pLo by ring]
  calc
    1 -
        weightedBernoulliSuccessBase gHi gLo pHi pLo *
          (weightedBernoulliSuccessBase gHi gLo pHi pLo +
            weightedBernoulliFailureBase gHi gLo pHi pLo)⁻¹
        =
        (weightedBernoulliSuccessBase gHi gLo pHi pLo +
            weightedBernoulliFailureBase gHi gLo pHi pLo) *
          (weightedBernoulliSuccessBase gHi gLo pHi pLo +
            weightedBernoulliFailureBase gHi gLo pHi pLo)⁻¹ -
          weightedBernoulliSuccessBase gHi gLo pHi pLo *
            (weightedBernoulliSuccessBase gHi gLo pHi pLo +
              weightedBernoulliFailureBase gHi gLo pHi pLo)⁻¹ := by
          rw [mul_inv_cancel₀ hden_ne']
    _ =
        weightedBernoulliFailureBase gHi gLo pHi pLo *
          (weightedBernoulliSuccessBase gHi gLo pHi pLo +
            weightedBernoulliFailureBase gHi gLo pHi pLo)⁻¹ := by
          ring

/--
Algebraic order criterion for the weighted common threshold: if the
success/failure bases have odds no larger than the high Bernoulli odds, then
the normalized threshold is no larger than the high probability.
-/
theorem weightedBernoulliCommonThreshold_le_of_success_failure_le_hi_odds
    {gHi gLo pHi pLo : ℝ}
    (hpHi0 : 0 < pHi) (hpHi1 : pHi < 1)
    (hpLo0 : 0 < pLo) (hpLo1 : pLo < 1)
    (hodds :
      weightedBernoulliSuccessBase gHi gLo pHi pLo * (1 - pHi) ≤
        pHi * weightedBernoulliFailureBase gHi gLo pHi pLo) :
    weightedBernoulliCommonThreshold gHi gLo pHi pLo ≤ pHi := by
  have hden_pos :
      0 < weightedBernoulliClosedRateBase gHi gLo pHi pLo :=
    weightedBernoulliClosedRateBase_pos hpHi0 hpHi1 hpLo0 hpLo1
  rw [weightedBernoulliCommonThreshold]
  rw [div_le_iff₀ hden_pos]
  dsimp [weightedBernoulliClosedRateBase]
  nlinarith

/--
Algebraic order criterion for the weighted common threshold: if the
success/failure bases have odds at least the low Bernoulli odds, then the low
probability is no larger than the normalized threshold.
-/
theorem le_weightedBernoulliCommonThreshold_of_lo_odds_le_success_failure
    {gHi gLo pHi pLo : ℝ}
    (hpHi0 : 0 < pHi) (hpHi1 : pHi < 1)
    (hpLo0 : 0 < pLo) (hpLo1 : pLo < 1)
    (hodds :
      pLo * weightedBernoulliFailureBase gHi gLo pHi pLo ≤
        weightedBernoulliSuccessBase gHi gLo pHi pLo * (1 - pLo)) :
    pLo ≤ weightedBernoulliCommonThreshold gHi gLo pHi pLo := by
  have hden_pos :
      0 < weightedBernoulliClosedRateBase gHi gLo pHi pLo :=
    weightedBernoulliClosedRateBase_pos hpHi0 hpHi1 hpLo0 hpLo1
  rw [weightedBernoulliCommonThreshold]
  rw [le_div_iff₀ hden_pos]
  dsimp [weightedBernoulliClosedRateBase]
  nlinarith

/-- Log identity for the success-side weighted geometric Bernoulli base. -/
theorem weightedBernoulliSuccessBase_log_mul_sum
    {gHi gLo pHi pLo : ℝ} (hG : gHi + gLo ≠ 0)
    (hpHi0 : 0 < pHi) (hpLo0 : 0 < pLo) :
    (gHi + gLo) *
        Real.log (weightedBernoulliSuccessBase gHi gLo pHi pLo) =
      gLo * Real.log pLo + gHi * Real.log pHi := by
  have hpLo_pow_pos : 0 < pLo ^ (gLo / (gHi + gLo)) :=
    Real.rpow_pos_of_pos hpLo0 _
  have hpHi_pow_pos : 0 < pHi ^ (gHi / (gHi + gLo)) :=
    Real.rpow_pos_of_pos hpHi0 _
  rw [weightedBernoulliSuccessBase]
  rw [Real.log_mul (ne_of_gt hpLo_pow_pos) (ne_of_gt hpHi_pow_pos)]
  rw [Real.log_rpow hpLo0, Real.log_rpow hpHi0]
  field_simp [hG]

/-- Log identity for the failure-side weighted geometric Bernoulli base. -/
theorem weightedBernoulliFailureBase_log_mul_sum
    {gHi gLo pHi pLo : ℝ} (hG : gHi + gLo ≠ 0)
    (hpHi1 : pHi < 1) (hpLo1 : pLo < 1) :
    (gHi + gLo) *
        Real.log (weightedBernoulliFailureBase gHi gLo pHi pLo) =
      gLo * Real.log (1 - pLo) + gHi * Real.log (1 - pHi) := by
  have hpLo_fail_pos : 0 < 1 - pLo := sub_pos.mpr hpLo1
  have hpHi_fail_pos : 0 < 1 - pHi := sub_pos.mpr hpHi1
  have hpLo_pow_pos : 0 < (1 - pLo) ^ (gLo / (gHi + gLo)) :=
    Real.rpow_pos_of_pos hpLo_fail_pos _
  have hpHi_pow_pos : 0 < (1 - pHi) ^ (gHi / (gHi + gLo)) :=
    Real.rpow_pos_of_pos hpHi_fail_pos _
  rw [weightedBernoulliFailureBase]
  rw [Real.log_mul (ne_of_gt hpLo_pow_pos) (ne_of_gt hpHi_pow_pos)]
  rw [Real.log_rpow hpLo_fail_pos, Real.log_rpow hpHi_fail_pos]
  field_simp [hG]

/--
At the weighted common threshold, the weighted two-Bernoulli KL objective has
the closed logarithmic value. This is the value identity underlying the
closed-form adjacent rate; the separate minimizer/no-duality-gap argument
turns this value into the threshold infimum.
-/
theorem twoBernoulliThresholdRate_weightedCommonThreshold_eq_closed
    {gHi gLo pHi pLo : ℝ} (hG : gHi + gLo ≠ 0)
    (hpHi0 : 0 < pHi) (hpHi1 : pHi < 1)
    (hpLo0 : 0 < pLo) (hpLo1 : pLo < 1) :
    twoBernoulliThresholdRate gHi gLo pHi pLo
        (weightedBernoulliCommonThreshold gHi gLo pHi pLo) =
      weightedBernoulliClosedThresholdRate gHi gLo pHi pLo := by
  let S := weightedBernoulliSuccessBase gHi gLo pHi pLo
  let F := weightedBernoulliFailureBase gHi gLo pHi pLo
  let B := weightedBernoulliClosedRateBase gHi gLo pHi pLo
  let a := weightedBernoulliCommonThreshold gHi gLo pHi pLo
  have hS_pos : 0 < S := weightedBernoulliSuccessBase_pos hpHi0 hpLo0
  have hF_pos : 0 < F := weightedBernoulliFailureBase_pos hpHi1 hpLo1
  have hB_pos : 0 < B :=
    weightedBernoulliClosedRateBase_pos hpHi0 hpHi1 hpLo0 hpLo1
  have hS_ne : S ≠ 0 := ne_of_gt hS_pos
  have hF_ne : F ≠ 0 := ne_of_gt hF_pos
  have hB_ne : B ≠ 0 := ne_of_gt hB_pos
  have hpHi_ne : pHi ≠ 0 := ne_of_gt hpHi0
  have hpLo_ne : pLo ≠ 0 := ne_of_gt hpLo0
  have hpHi_fail_pos : 0 < 1 - pHi := sub_pos.mpr hpHi1
  have hpLo_fail_pos : 0 < 1 - pLo := sub_pos.mpr hpLo1
  have hpHi_fail_ne : 1 - pHi ≠ 0 := ne_of_gt hpHi_fail_pos
  have hpLo_fail_ne : 1 - pLo ≠ 0 := ne_of_gt hpLo_fail_pos
  have ha_eq : a = S / B := by
    rfl
  have hone_sub_a : 1 - a = F / B := by
    dsimp [a, S, F, B]
    exact
      one_sub_weightedBernoulliCommonThreshold_eq
        hpHi0 hpHi1 hpLo0 hpLo1
  have hone_sub_SB : 1 - S / B = F / B := by
    rw [← ha_eq]
    exact hone_sub_a
  have hone_sub_SB : 1 - S / B = F / B := by
    rw [← ha_eq]
    exact hone_sub_a
  have hlogS :
      (gHi + gLo) * Real.log S =
        gLo * Real.log pLo + gHi * Real.log pHi := by
    dsimp [S]
    exact weightedBernoulliSuccessBase_log_mul_sum hG hpHi0 hpLo0
  have hlogF :
      (gHi + gLo) * Real.log F =
        gLo * Real.log (1 - pLo) + gHi * Real.log (1 - pHi) := by
    dsimp [F]
    exact weightedBernoulliFailureBase_log_mul_sum hG hpHi1 hpLo1
  have hsuccess :
      gHi * Real.log ((S / B) / pHi) +
          gLo * Real.log ((S / B) / pLo) =
        -(gHi + gLo) * Real.log B := by
    rw [Real.log_div (div_ne_zero hS_ne hB_ne) hpHi_ne,
      Real.log_div (div_ne_zero hS_ne hB_ne) hpLo_ne,
      Real.log_div hS_ne hB_ne]
    nlinarith [hlogS]
  have hfailure :
      gHi * Real.log ((F / B) / (1 - pHi)) +
          gLo * Real.log ((F / B) / (1 - pLo)) =
        -(gHi + gLo) * Real.log B := by
    rw [Real.log_div (div_ne_zero hF_ne hB_ne) hpHi_fail_ne,
      Real.log_div (div_ne_zero hF_ne hB_ne) hpLo_fail_ne,
      Real.log_div hF_ne hB_ne]
    nlinarith [hlogF]
  rw [twoBernoulliThresholdRate, weightedBernoulliClosedThresholdRate]
  simp only [bernoulliKL]
  dsimp [a] at ha_eq hone_sub_a
  rw [ha_eq, hone_sub_SB]
  change
    gHi * (S / B * Real.log (S / B / pHi) +
          F / B * Real.log (F / B / (1 - pHi))) +
        gLo * (S / B * Real.log (S / B / pLo) +
          F / B * Real.log (F / B / (1 - pLo))) =
      -(gHi + gLo) * Real.log B
  have hweights_sum : S / B + F / B = 1 := by
    have hB_eq : B = F + S := by
      dsimp [B, F, S, weightedBernoulliClosedRateBase]
    rw [hB_eq]
    field_simp [show F + S ≠ 0 by
      exact ne_of_gt (add_pos hF_pos hS_pos)]
    ring
  calc
    gHi * (S / B * Real.log (S / B / pHi) +
          F / B * Real.log (F / B / (1 - pHi))) +
        gLo * (S / B * Real.log (S / B / pLo) +
          F / B * Real.log (F / B / (1 - pLo)))
        =
        (S / B) *
            (gHi * Real.log (S / B / pHi) +
              gLo * Real.log (S / B / pLo)) +
          (F / B) *
            (gHi * Real.log (F / B / (1 - pHi)) +
              gLo * Real.log (F / B / (1 - pLo))) := by
          ring
    _ =
        (S / B) * (-(gHi + gLo) * Real.log B) +
          (F / B) * (-(gHi + gLo) * Real.log B) := by
          rw [hsuccess, hfailure]
    _ = -(gHi + gLo) * Real.log B := by
          rw [← add_mul, hweights_sum, one_mul]

/--
The weighted geometric common threshold satisfies the weighted Bernoulli
common-dual first-order equation.
-/
theorem weightedBernoulliCommonThreshold_dual_balance
    {gHi gLo pHi pLo : ℝ} (hG : gHi + gLo ≠ 0)
    (hpHi0 : 0 < pHi) (hpHi1 : pHi < 1)
    (hpLo0 : 0 < pLo) (hpLo1 : pLo < 1) :
    gHi *
        binaryLogMGFDerivativeArg pHi
          (weightedBernoulliCommonThreshold gHi gLo pHi pLo) =
      -(gLo *
        binaryLogMGFDerivativeArg pLo
          (weightedBernoulliCommonThreshold gHi gLo pHi pLo)) := by
  let S := weightedBernoulliSuccessBase gHi gLo pHi pLo
  let F := weightedBernoulliFailureBase gHi gLo pHi pLo
  let B := weightedBernoulliClosedRateBase gHi gLo pHi pLo
  let a := weightedBernoulliCommonThreshold gHi gLo pHi pLo
  have hS_pos : 0 < S := weightedBernoulliSuccessBase_pos hpHi0 hpLo0
  have hF_pos : 0 < F := weightedBernoulliFailureBase_pos hpHi1 hpLo1
  have hB_pos : 0 < B :=
    weightedBernoulliClosedRateBase_pos hpHi0 hpHi1 hpLo0 hpLo1
  have hS_ne : S ≠ 0 := ne_of_gt hS_pos
  have hF_ne : F ≠ 0 := ne_of_gt hF_pos
  have hB_ne : B ≠ 0 := ne_of_gt hB_pos
  have hpHi_ne : pHi ≠ 0 := ne_of_gt hpHi0
  have hpLo_ne : pLo ≠ 0 := ne_of_gt hpLo0
  have hpHi_fail_pos : 0 < 1 - pHi := sub_pos.mpr hpHi1
  have hpLo_fail_pos : 0 < 1 - pLo := sub_pos.mpr hpLo1
  have hpHi_fail_ne : 1 - pHi ≠ 0 := ne_of_gt hpHi_fail_pos
  have hpLo_fail_ne : 1 - pLo ≠ 0 := ne_of_gt hpLo_fail_pos
  have ha_eq : a = S / B := by
    rfl
  have hone_sub_a : 1 - a = F / B := by
    dsimp [a, S, F, B]
    exact
      one_sub_weightedBernoulliCommonThreshold_eq
        hpHi0 hpHi1 hpLo0 hpLo1
  have hone_sub_SB : 1 - S / B = F / B := by
    rw [← ha_eq]
    exact hone_sub_a
  have hlogS :
      (gHi + gLo) * Real.log S =
        gLo * Real.log pLo + gHi * Real.log pHi := by
    dsimp [S]
    exact weightedBernoulliSuccessBase_log_mul_sum hG hpHi0 hpLo0
  have hlogF :
      (gHi + gLo) * Real.log F =
        gLo * Real.log (1 - pLo) + gHi * Real.log (1 - pHi) := by
    dsimp [F]
    exact weightedBernoulliFailureBase_log_mul_sum hG hpHi1 hpLo1
  have hdual_hi :
      binaryLogMGFDerivativeArg pHi a =
        Real.log S + Real.log (1 - pHi) - Real.log pHi - Real.log F := by
    rw [binaryLogMGFDerivativeArg, ha_eq, hone_sub_SB]
    have hratio :
        (S / B) * (1 - pHi) / (pHi * (F / B)) =
          (S * (1 - pHi)) / (pHi * F) := by
      field_simp [hB_ne, hpHi_ne, hF_ne]
    rw [hratio]
    rw [Real.log_div (mul_ne_zero hS_ne hpHi_fail_ne)
      (mul_ne_zero hpHi_ne hF_ne)]
    rw [Real.log_mul hS_ne hpHi_fail_ne]
    rw [Real.log_mul hpHi_ne hF_ne]
    ring
  have hdual_lo :
      binaryLogMGFDerivativeArg pLo a =
        Real.log S + Real.log (1 - pLo) - Real.log pLo - Real.log F := by
    rw [binaryLogMGFDerivativeArg, ha_eq, hone_sub_SB]
    have hratio :
        (S / B) * (1 - pLo) / (pLo * (F / B)) =
          (S * (1 - pLo)) / (pLo * F) := by
      field_simp [hB_ne, hpLo_ne, hF_ne]
    rw [hratio]
    rw [Real.log_div (mul_ne_zero hS_ne hpLo_fail_ne)
      (mul_ne_zero hpLo_ne hF_ne)]
    rw [Real.log_mul hS_ne hpLo_fail_ne]
    rw [Real.log_mul hpLo_ne hF_ne]
    ring
  have hsum :
      gHi * binaryLogMGFDerivativeArg pHi a +
          gLo * binaryLogMGFDerivativeArg pLo a = 0 := by
    rw [hdual_hi, hdual_lo]
    nlinarith [hlogS, hlogF]
  dsimp [a] at hsum ⊢
  linarith

/--
The weighted common threshold has log-odds equal to the sample-rate weighted
average of the two Bernoulli log-odds.
-/
theorem weightedBernoulliCommonThreshold_logOdds_mul_sum
    {gHi gLo pHi pLo : ℝ} (hG : gHi + gLo ≠ 0)
    (hpHi0 : 0 < pHi) (hpHi1 : pHi < 1)
    (hpLo0 : 0 < pLo) (hpLo1 : pLo < 1) :
    (gHi + gLo) *
        bernoulliLogOdds
          (weightedBernoulliCommonThreshold gHi gLo pHi pLo) =
      gLo * bernoulliLogOdds pLo + gHi * bernoulliLogOdds pHi := by
  let S := weightedBernoulliSuccessBase gHi gLo pHi pLo
  let F := weightedBernoulliFailureBase gHi gLo pHi pLo
  let B := weightedBernoulliClosedRateBase gHi gLo pHi pLo
  let a := weightedBernoulliCommonThreshold gHi gLo pHi pLo
  have hS_pos : 0 < S := weightedBernoulliSuccessBase_pos hpHi0 hpLo0
  have hF_pos : 0 < F := weightedBernoulliFailureBase_pos hpHi1 hpLo1
  have hB_pos : 0 < B :=
    weightedBernoulliClosedRateBase_pos hpHi0 hpHi1 hpLo0 hpLo1
  have hS_ne : S ≠ 0 := ne_of_gt hS_pos
  have hF_ne : F ≠ 0 := ne_of_gt hF_pos
  have hB_ne : B ≠ 0 := ne_of_gt hB_pos
  have ha_eq : a = S / B := by
    rfl
  have hone_sub_a : 1 - a = F / B := by
    dsimp [a, S, F, B]
    exact
      one_sub_weightedBernoulliCommonThreshold_eq
        hpHi0 hpHi1 hpLo0 hpLo1
  have hone_sub_SB : 1 - S / B = F / B := by
    rw [← ha_eq]
    exact hone_sub_a
  have hlogS :
      (gHi + gLo) * Real.log S =
        gLo * Real.log pLo + gHi * Real.log pHi := by
    dsimp [S]
    exact weightedBernoulliSuccessBase_log_mul_sum hG hpHi0 hpLo0
  have hlogF :
      (gHi + gLo) * Real.log F =
        gLo * Real.log (1 - pLo) + gHi * Real.log (1 - pHi) := by
    dsimp [F]
    exact weightedBernoulliFailureBase_log_mul_sum hG hpHi1 hpLo1
  have hlogit_a :
      bernoulliLogOdds a = Real.log S - Real.log F := by
    rw [bernoulliLogOdds, ha_eq, hone_sub_SB]
    have hratio : (S / B) / (F / B) = S / F := by
      field_simp [hB_ne, hF_ne]
    rw [hratio, Real.log_div hS_ne hF_ne]
  have hlogit_hi :
      bernoulliLogOdds pHi = Real.log pHi - Real.log (1 - pHi) := by
    rw [bernoulliLogOdds, Real.log_div (ne_of_gt hpHi0)
      (ne_of_gt (sub_pos.mpr hpHi1))]
  have hlogit_lo :
      bernoulliLogOdds pLo = Real.log pLo - Real.log (1 - pLo) := by
    rw [bernoulliLogOdds, Real.log_div (ne_of_gt hpLo0)
      (ne_of_gt (sub_pos.mpr hpLo1))]
  rw [hlogit_a, hlogit_hi, hlogit_lo]
  nlinarith [hlogS, hlogF]

/--
If the lower Bernoulli probability is no larger than the higher one and the
sample weights are nonnegative with positive total, then the weighted common
threshold is no larger than the high probability.
-/
theorem weightedBernoulliCommonThreshold_le_hi_of_le
    {gHi gLo pHi pLo : ℝ}
    (hgHi : 0 ≤ gHi) (hgLo : 0 ≤ gLo) (hGpos : 0 < gHi + gLo)
    (hpHi0 : 0 < pHi) (hpHi1 : pHi < 1)
    (hpLo0 : 0 < pLo) (hpLo1 : pLo < 1)
    (hpLo_le_hi : pLo ≤ pHi) :
    weightedBernoulliCommonThreshold gHi gLo pHi pLo ≤ pHi := by
  let a := weightedBernoulliCommonThreshold gHi gLo pHi pLo
  have ha0 : 0 < a := by
    dsimp [a]
    exact weightedBernoulliCommonThreshold_pos hpHi0 hpHi1 hpLo0 hpLo1
  have ha1 : a < 1 := by
    dsimp [a]
    exact weightedBernoulliCommonThreshold_lt_one hpHi0 hpHi1 hpLo0 hpLo1
  have hlog_lo_hi :
      bernoulliLogOdds pLo ≤ bernoulliLogOdds pHi :=
    bernoulliLogOdds_le_of_le hpLo0 hpLo1 hpHi0 hpHi1 hpLo_le_hi
  have hweighted_le :
      gLo * bernoulliLogOdds pLo + gHi * bernoulliLogOdds pHi ≤
        (gHi + gLo) * bernoulliLogOdds pHi := by
    have hlo_scaled :
        gLo * bernoulliLogOdds pLo ≤
          gLo * bernoulliLogOdds pHi :=
      mul_le_mul_of_nonneg_left hlog_lo_hi hgLo
    nlinarith
  have hlog_sum :
      (gHi + gLo) * bernoulliLogOdds a =
        gLo * bernoulliLogOdds pLo + gHi * bernoulliLogOdds pHi := by
    dsimp [a]
    exact
      weightedBernoulliCommonThreshold_logOdds_mul_sum
        hGpos.ne' hpHi0 hpHi1 hpLo0 hpLo1
  have hlogit_le : bernoulliLogOdds a ≤ bernoulliLogOdds pHi := by
    have hmul :
        (gHi + gLo) * bernoulliLogOdds a ≤
          (gHi + gLo) * bernoulliLogOdds pHi := by
      rwa [hlog_sum]
    nlinarith
  have ha_den_pos : 0 < 1 - a := sub_pos.mpr ha1
  have hpHi_den_pos : 0 < 1 - pHi := sub_pos.mpr hpHi1
  have hodds_le :
      a / (1 - a) ≤ pHi / (1 - pHi) := by
    have hlog_le :
        Real.log (a / (1 - a)) ≤ Real.log (pHi / (1 - pHi)) := by
      simpa [bernoulliLogOdds] using hlogit_le
    exact
      (Real.log_le_log_iff
        (div_pos ha0 ha_den_pos)
        (div_pos hpHi0 hpHi_den_pos)).mp hlog_le
  rw [div_le_div_iff₀ ha_den_pos hpHi_den_pos] at hodds_le
  nlinarith

/--
If the lower Bernoulli probability is strictly below the higher one and the
lower endpoint has positive sample weight, then the weighted common threshold
is strictly below the high probability.
-/
theorem weightedBernoulliCommonThreshold_lt_hi_of_lt
    {gHi gLo pHi pLo : ℝ}
    (hgHi : 0 ≤ gHi) (hgLo : 0 < gLo) (hGpos : 0 < gHi + gLo)
    (hpHi0 : 0 < pHi) (hpHi1 : pHi < 1)
    (hpLo0 : 0 < pLo) (hpLo1 : pLo < 1)
    (hpLo_lt_hi : pLo < pHi) :
    weightedBernoulliCommonThreshold gHi gLo pHi pLo < pHi := by
  let a := weightedBernoulliCommonThreshold gHi gLo pHi pLo
  have ha0 : 0 < a := by
    dsimp [a]
    exact weightedBernoulliCommonThreshold_pos hpHi0 hpHi1 hpLo0 hpLo1
  have ha1 : a < 1 := by
    dsimp [a]
    exact weightedBernoulliCommonThreshold_lt_one hpHi0 hpHi1 hpLo0 hpLo1
  have hlog_lo_hi :
      bernoulliLogOdds pLo < bernoulliLogOdds pHi :=
    bernoulliLogOdds_lt_of_lt hpLo0 hpLo1 hpHi0 hpHi1 hpLo_lt_hi
  have hweighted_lt :
      gLo * bernoulliLogOdds pLo + gHi * bernoulliLogOdds pHi <
        (gHi + gLo) * bernoulliLogOdds pHi := by
    have hlo_scaled :
        gLo * bernoulliLogOdds pLo <
          gLo * bernoulliLogOdds pHi :=
      mul_lt_mul_of_pos_left hlog_lo_hi hgLo
    nlinarith
  have hlog_sum :
      (gHi + gLo) * bernoulliLogOdds a =
        gLo * bernoulliLogOdds pLo + gHi * bernoulliLogOdds pHi := by
    dsimp [a]
    exact
      weightedBernoulliCommonThreshold_logOdds_mul_sum
        hGpos.ne' hpHi0 hpHi1 hpLo0 hpLo1
  have hlogit_lt : bernoulliLogOdds a < bernoulliLogOdds pHi := by
    have hmul :
        (gHi + gLo) * bernoulliLogOdds a <
          (gHi + gLo) * bernoulliLogOdds pHi := by
      rwa [hlog_sum]
    nlinarith
  have ha_den_pos : 0 < 1 - a := sub_pos.mpr ha1
  have hpHi_den_pos : 0 < 1 - pHi := sub_pos.mpr hpHi1
  have hodds_lt :
      a / (1 - a) < pHi / (1 - pHi) := by
    have hlog_lt :
        Real.log (a / (1 - a)) < Real.log (pHi / (1 - pHi)) := by
      simpa [bernoulliLogOdds] using hlogit_lt
    exact
      (Real.log_lt_log_iff
        (div_pos ha0 ha_den_pos)
        (div_pos hpHi0 hpHi_den_pos)).mp hlog_lt
  rw [div_lt_div_iff₀ ha_den_pos hpHi_den_pos] at hodds_lt
  nlinarith

/--
If the lower Bernoulli probability is no larger than the higher one and the
sample weights are nonnegative with positive total, then the low probability
is no larger than the weighted common threshold.
-/
theorem le_weightedBernoulliCommonThreshold_of_le
    {gHi gLo pHi pLo : ℝ}
    (hgHi : 0 ≤ gHi) (hgLo : 0 ≤ gLo) (hGpos : 0 < gHi + gLo)
    (hpHi0 : 0 < pHi) (hpHi1 : pHi < 1)
    (hpLo0 : 0 < pLo) (hpLo1 : pLo < 1)
    (hpLo_le_hi : pLo ≤ pHi) :
    pLo ≤ weightedBernoulliCommonThreshold gHi gLo pHi pLo := by
  let a := weightedBernoulliCommonThreshold gHi gLo pHi pLo
  have ha0 : 0 < a := by
    dsimp [a]
    exact weightedBernoulliCommonThreshold_pos hpHi0 hpHi1 hpLo0 hpLo1
  have ha1 : a < 1 := by
    dsimp [a]
    exact weightedBernoulliCommonThreshold_lt_one hpHi0 hpHi1 hpLo0 hpLo1
  have hlog_lo_hi :
      bernoulliLogOdds pLo ≤ bernoulliLogOdds pHi :=
    bernoulliLogOdds_le_of_le hpLo0 hpLo1 hpHi0 hpHi1 hpLo_le_hi
  have hweighted_ge :
      (gHi + gLo) * bernoulliLogOdds pLo ≤
        gLo * bernoulliLogOdds pLo + gHi * bernoulliLogOdds pHi := by
    have hhi_scaled :
        gHi * bernoulliLogOdds pLo ≤
          gHi * bernoulliLogOdds pHi :=
      mul_le_mul_of_nonneg_left hlog_lo_hi hgHi
    nlinarith
  have hlog_sum :
      (gHi + gLo) * bernoulliLogOdds a =
        gLo * bernoulliLogOdds pLo + gHi * bernoulliLogOdds pHi := by
    dsimp [a]
    exact
      weightedBernoulliCommonThreshold_logOdds_mul_sum
        hGpos.ne' hpHi0 hpHi1 hpLo0 hpLo1
  have hlogit_ge : bernoulliLogOdds pLo ≤ bernoulliLogOdds a := by
    have hmul :
        (gHi + gLo) * bernoulliLogOdds pLo ≤
          (gHi + gLo) * bernoulliLogOdds a := by
      rwa [hlog_sum]
    nlinarith
  have ha_den_pos : 0 < 1 - a := sub_pos.mpr ha1
  have hpLo_den_pos : 0 < 1 - pLo := sub_pos.mpr hpLo1
  have hodds_le :
      pLo / (1 - pLo) ≤ a / (1 - a) := by
    have hlog_le :
        Real.log (pLo / (1 - pLo)) ≤ Real.log (a / (1 - a)) := by
      simpa [bernoulliLogOdds] using hlogit_ge
    exact
      (Real.log_le_log_iff
        (div_pos hpLo0 hpLo_den_pos)
        (div_pos ha0 ha_den_pos)).mp hlog_le
  rw [div_le_div_iff₀ hpLo_den_pos ha_den_pos] at hodds_le
  nlinarith

/--
If the lower Bernoulli probability is strictly below the higher one and the
higher endpoint has positive sample weight, then the low probability is
strictly below the weighted common threshold.
-/
theorem lt_weightedBernoulliCommonThreshold_of_lt
    {gHi gLo pHi pLo : ℝ}
    (hgHi : 0 < gHi) (hgLo : 0 ≤ gLo) (hGpos : 0 < gHi + gLo)
    (hpHi0 : 0 < pHi) (hpHi1 : pHi < 1)
    (hpLo0 : 0 < pLo) (hpLo1 : pLo < 1)
    (hpLo_lt_hi : pLo < pHi) :
    pLo < weightedBernoulliCommonThreshold gHi gLo pHi pLo := by
  let a := weightedBernoulliCommonThreshold gHi gLo pHi pLo
  have ha0 : 0 < a := by
    dsimp [a]
    exact weightedBernoulliCommonThreshold_pos hpHi0 hpHi1 hpLo0 hpLo1
  have ha1 : a < 1 := by
    dsimp [a]
    exact weightedBernoulliCommonThreshold_lt_one hpHi0 hpHi1 hpLo0 hpLo1
  have hlog_lo_hi :
      bernoulliLogOdds pLo < bernoulliLogOdds pHi :=
    bernoulliLogOdds_lt_of_lt hpLo0 hpLo1 hpHi0 hpHi1 hpLo_lt_hi
  have hweighted_gt :
      (gHi + gLo) * bernoulliLogOdds pLo <
        gLo * bernoulliLogOdds pLo + gHi * bernoulliLogOdds pHi := by
    have hhi_scaled :
        gHi * bernoulliLogOdds pLo <
          gHi * bernoulliLogOdds pHi :=
      mul_lt_mul_of_pos_left hlog_lo_hi hgHi
    nlinarith
  have hlog_sum :
      (gHi + gLo) * bernoulliLogOdds a =
        gLo * bernoulliLogOdds pLo + gHi * bernoulliLogOdds pHi := by
    dsimp [a]
    exact
      weightedBernoulliCommonThreshold_logOdds_mul_sum
        hGpos.ne' hpHi0 hpHi1 hpLo0 hpLo1
  have hlogit_gt : bernoulliLogOdds pLo < bernoulliLogOdds a := by
    have hmul :
        (gHi + gLo) * bernoulliLogOdds pLo <
          (gHi + gLo) * bernoulliLogOdds a := by
      rwa [hlog_sum]
    nlinarith
  have ha_den_pos : 0 < 1 - a := sub_pos.mpr ha1
  have hpLo_den_pos : 0 < 1 - pLo := sub_pos.mpr hpLo1
  have hodds_lt :
      pLo / (1 - pLo) < a / (1 - a) := by
    have hlog_lt :
        Real.log (pLo / (1 - pLo)) < Real.log (a / (1 - a)) := by
      simpa [bernoulliLogOdds] using hlogit_gt
    exact
      (Real.log_lt_log_iff
        (div_pos hpLo0 hpLo_den_pos)
        (div_pos ha0 ha_den_pos)).mp hlog_lt
  rw [div_lt_div_iff₀ hpLo_den_pos ha_den_pos] at hodds_lt
  nlinarith

/--
The lower-endpoint derivative of the closed-rate base is nonnegative when the
lower endpoint is below the higher endpoint.
-/
theorem weightedBernoulliClosedRateBase_deriv_lo_nonneg_of_le
    {gHi gLo pHi pLo : ℝ}
    (hgHi : 0 ≤ gHi) (hgLo : 0 ≤ gLo) (hGpos : 0 < gHi + gLo)
    (hpHi0 : 0 < pHi) (hpHi1 : pHi < 1)
    (hpLo0 : 0 < pLo) (hpLo1 : pLo < 1)
    (hpLo_le_hi : pLo ≤ pHi) :
    0 ≤
      ((-1) * (gLo / (gHi + gLo)) *
            (1 - pLo) ^ (gLo / (gHi + gLo) - 1)) *
          (1 - pHi) ^ (gHi / (gHi + gLo)) +
        ((gLo / (gHi + gLo)) *
            pLo ^ (gLo / (gHi + gLo) - 1)) *
          pHi ^ (gHi / (gHi + gLo)) := by
  let aLo := gLo / (gHi + gLo)
  let aHi := gHi / (gHi + gLo)
  let F := weightedBernoulliFailureBase gHi gLo pHi pLo
  let S := weightedBernoulliSuccessBase gHi gLo pHi pLo
  let B := weightedBernoulliClosedRateBase gHi gLo pHi pLo
  have hF_pos : 0 < F := by
    dsimp [F]
    exact weightedBernoulliFailureBase_pos hpHi1 hpLo1
  have hS_pos : 0 < S := by
    dsimp [S]
    exact weightedBernoulliSuccessBase_pos hpHi0 hpLo0
  have hB_pos : 0 < B := by
    dsimp [B]
    exact weightedBernoulliClosedRateBase_pos hpHi0 hpHi1 hpLo0 hpLo1
  have hthreshold :
      pLo ≤ weightedBernoulliCommonThreshold gHi gLo pHi pLo :=
    le_weightedBernoulliCommonThreshold_of_le
      hgHi hgLo hGpos hpHi0 hpHi1 hpLo0 hpLo1 hpLo_le_hi
  have hmul_le : pLo * B ≤ S := by
    dsimp [weightedBernoulliCommonThreshold, B, S] at hthreshold
    exact (le_div_iff₀ hB_pos).mp hthreshold
  have hcross : F * pLo ≤ S * (1 - pLo) := by
    have hB_eq : B = F + S := by
      dsimp [B, F, S, weightedBernoulliClosedRateBase]
    rw [hB_eq] at hmul_le
    nlinarith
  have hquot : F / (1 - pLo) ≤ S / pLo := by
    rw [div_le_div_iff₀ (sub_pos.mpr hpLo1) hpLo0]
    nlinarith
  have hdiff_nonneg : 0 ≤ S / pLo - F / (1 - pLo) :=
    sub_nonneg.mpr hquot
  have haLo_nonneg : 0 ≤ aLo :=
    div_nonneg hgLo hGpos.le
  have hfactored :
      ((-1) * (gLo / (gHi + gLo)) *
            (1 - pLo) ^ (gLo / (gHi + gLo) - 1)) *
          (1 - pHi) ^ (gHi / (gHi + gLo)) +
        ((gLo / (gHi + gLo)) *
            pLo ^ (gLo / (gHi + gLo) - 1)) *
          pHi ^ (gHi / (gHi + gLo)) =
        aLo * (S / pLo - F / (1 - pLo)) := by
    dsimp [aLo, aHi, S, F, weightedBernoulliSuccessBase,
      weightedBernoulliFailureBase]
    rw [Real.rpow_sub_one (ne_of_gt (sub_pos.mpr hpLo1)),
      Real.rpow_sub_one (ne_of_gt hpLo0)]
    field_simp [ne_of_gt hpLo0, ne_of_gt (sub_pos.mpr hpLo1)]
    ring
  rw [hfactored]
  exact mul_nonneg haLo_nonneg hdiff_nonneg

/--
The lower-endpoint derivative of the closed-rate base is strictly positive
when both sample weights are positive and the lower endpoint is strictly below
the higher endpoint.
-/
theorem weightedBernoulliClosedRateBase_deriv_lo_pos_of_lt
    {gHi gLo pHi pLo : ℝ}
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hpHi0 : 0 < pHi) (hpHi1 : pHi < 1)
    (hpLo0 : 0 < pLo) (hpLo1 : pLo < 1)
    (hpLo_lt_hi : pLo < pHi) :
    0 <
      ((-1) * (gLo / (gHi + gLo)) *
            (1 - pLo) ^ (gLo / (gHi + gLo) - 1)) *
          (1 - pHi) ^ (gHi / (gHi + gLo)) +
        ((gLo / (gHi + gLo)) *
            pLo ^ (gLo / (gHi + gLo) - 1)) *
          pHi ^ (gHi / (gHi + gLo)) := by
  let aLo := gLo / (gHi + gLo)
  let F := weightedBernoulliFailureBase gHi gLo pHi pLo
  let S := weightedBernoulliSuccessBase gHi gLo pHi pLo
  let B := weightedBernoulliClosedRateBase gHi gLo pHi pLo
  have hGpos : 0 < gHi + gLo := add_pos hgHi hgLo
  have hB_pos : 0 < B := by
    dsimp [B]
    exact weightedBernoulliClosedRateBase_pos hpHi0 hpHi1 hpLo0 hpLo1
  have hthreshold :
      pLo < weightedBernoulliCommonThreshold gHi gLo pHi pLo :=
    lt_weightedBernoulliCommonThreshold_of_lt
      hgHi hgLo.le hGpos hpHi0 hpHi1 hpLo0 hpLo1 hpLo_lt_hi
  have hmul_lt : pLo * B < S := by
    dsimp [weightedBernoulliCommonThreshold, B, S] at hthreshold
    exact (lt_div_iff₀ hB_pos).mp hthreshold
  have hcross : F * pLo < S * (1 - pLo) := by
    have hB_eq : B = F + S := by
      dsimp [B, F, S, weightedBernoulliClosedRateBase]
    rw [hB_eq] at hmul_lt
    nlinarith
  have hquot : F / (1 - pLo) < S / pLo := by
    rw [div_lt_div_iff₀ (sub_pos.mpr hpLo1) hpLo0]
    nlinarith
  have hdiff_pos : 0 < S / pLo - F / (1 - pLo) :=
    sub_pos.mpr hquot
  have haLo_pos : 0 < aLo :=
    div_pos hgLo hGpos
  have hfactored :
      ((-1) * (gLo / (gHi + gLo)) *
            (1 - pLo) ^ (gLo / (gHi + gLo) - 1)) *
          (1 - pHi) ^ (gHi / (gHi + gLo)) +
        ((gLo / (gHi + gLo)) *
            pLo ^ (gLo / (gHi + gLo) - 1)) *
          pHi ^ (gHi / (gHi + gLo)) =
        aLo * (S / pLo - F / (1 - pLo)) := by
    dsimp [aLo, S, F, weightedBernoulliSuccessBase,
      weightedBernoulliFailureBase]
    rw [Real.rpow_sub_one (ne_of_gt (sub_pos.mpr hpLo1)),
      Real.rpow_sub_one (ne_of_gt hpLo0)]
    field_simp [ne_of_gt hpLo0, ne_of_gt (sub_pos.mpr hpLo1)]
    ring
  rw [hfactored]
  exact mul_pos haLo_pos hdiff_pos

/--
The higher-endpoint derivative of the closed-rate base is nonpositive when the
lower endpoint is below the higher endpoint.
-/
theorem weightedBernoulliClosedRateBase_deriv_hi_nonpos_of_le
    {gHi gLo pHi pLo : ℝ}
    (hgHi : 0 ≤ gHi) (hgLo : 0 ≤ gLo) (hGpos : 0 < gHi + gLo)
    (hpHi0 : 0 < pHi) (hpHi1 : pHi < 1)
    (hpLo0 : 0 < pLo) (hpLo1 : pLo < 1)
    (hpLo_le_hi : pLo ≤ pHi) :
    ((1 - pLo) ^ (gLo / (gHi + gLo)) *
          ((-1) * (gHi / (gHi + gLo)) *
            (1 - pHi) ^ (gHi / (gHi + gLo) - 1)) +
        pLo ^ (gLo / (gHi + gLo)) *
          ((gHi / (gHi + gLo)) *
            pHi ^ (gHi / (gHi + gLo) - 1))) ≤ 0 := by
  let aLo := gLo / (gHi + gLo)
  let aHi := gHi / (gHi + gLo)
  let F := weightedBernoulliFailureBase gHi gLo pHi pLo
  let S := weightedBernoulliSuccessBase gHi gLo pHi pLo
  let B := weightedBernoulliClosedRateBase gHi gLo pHi pLo
  have hB_pos : 0 < B := by
    dsimp [B]
    exact weightedBernoulliClosedRateBase_pos hpHi0 hpHi1 hpLo0 hpLo1
  have hthreshold :
      weightedBernoulliCommonThreshold gHi gLo pHi pLo ≤ pHi :=
    weightedBernoulliCommonThreshold_le_hi_of_le
      hgHi hgLo hGpos hpHi0 hpHi1 hpLo0 hpLo1 hpLo_le_hi
  have hmul_le : S ≤ pHi * B := by
    dsimp [weightedBernoulliCommonThreshold, B, S] at hthreshold
    exact (div_le_iff₀ hB_pos).mp hthreshold
  have hcross : S * (1 - pHi) ≤ F * pHi := by
    have hB_eq : B = F + S := by
      dsimp [B, F, S, weightedBernoulliClosedRateBase]
    rw [hB_eq] at hmul_le
    nlinarith
  have hquot : S / pHi ≤ F / (1 - pHi) := by
    rw [div_le_div_iff₀ hpHi0 (sub_pos.mpr hpHi1)]
    nlinarith
  have hdiff_nonpos : S / pHi - F / (1 - pHi) ≤ 0 :=
    sub_nonpos.mpr hquot
  have haHi_nonneg : 0 ≤ aHi :=
    div_nonneg hgHi hGpos.le
  have hfactored :
      (1 - pLo) ^ (gLo / (gHi + gLo)) *
          ((-1) * (gHi / (gHi + gLo)) *
            (1 - pHi) ^ (gHi / (gHi + gLo) - 1)) +
        pLo ^ (gLo / (gHi + gLo)) *
          ((gHi / (gHi + gLo)) *
            pHi ^ (gHi / (gHi + gLo) - 1)) =
        aHi * (S / pHi - F / (1 - pHi)) := by
    dsimp [aLo, aHi, S, F, weightedBernoulliSuccessBase,
      weightedBernoulliFailureBase]
    rw [Real.rpow_sub_one (ne_of_gt (sub_pos.mpr hpHi1)),
      Real.rpow_sub_one (ne_of_gt hpHi0)]
    field_simp [ne_of_gt hpHi0, ne_of_gt (sub_pos.mpr hpHi1)]
    ring
  rw [hfactored]
  exact mul_nonpos_of_nonneg_of_nonpos haHi_nonneg hdiff_nonpos

/--
The higher-endpoint derivative of the closed-rate base is strictly negative
when both sample weights are positive and the lower endpoint is strictly below
the higher endpoint.
-/
theorem weightedBernoulliClosedRateBase_deriv_hi_neg_of_lt
    {gHi gLo pHi pLo : ℝ}
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hpHi0 : 0 < pHi) (hpHi1 : pHi < 1)
    (hpLo0 : 0 < pLo) (hpLo1 : pLo < 1)
    (hpLo_lt_hi : pLo < pHi) :
    ((1 - pLo) ^ (gLo / (gHi + gLo)) *
          ((-1) * (gHi / (gHi + gLo)) *
            (1 - pHi) ^ (gHi / (gHi + gLo) - 1)) +
        pLo ^ (gLo / (gHi + gLo)) *
          ((gHi / (gHi + gLo)) *
            pHi ^ (gHi / (gHi + gLo) - 1))) < 0 := by
  let aHi := gHi / (gHi + gLo)
  let F := weightedBernoulliFailureBase gHi gLo pHi pLo
  let S := weightedBernoulliSuccessBase gHi gLo pHi pLo
  let B := weightedBernoulliClosedRateBase gHi gLo pHi pLo
  have hGpos : 0 < gHi + gLo := add_pos hgHi hgLo
  have hB_pos : 0 < B := by
    dsimp [B]
    exact weightedBernoulliClosedRateBase_pos hpHi0 hpHi1 hpLo0 hpLo1
  have hthreshold :
      weightedBernoulliCommonThreshold gHi gLo pHi pLo < pHi :=
    weightedBernoulliCommonThreshold_lt_hi_of_lt
      hgHi.le hgLo hGpos hpHi0 hpHi1 hpLo0 hpLo1 hpLo_lt_hi
  have hmul_lt : S < pHi * B := by
    dsimp [weightedBernoulliCommonThreshold, B, S] at hthreshold
    exact (div_lt_iff₀ hB_pos).mp hthreshold
  have hcross : S * (1 - pHi) < F * pHi := by
    have hB_eq : B = F + S := by
      dsimp [B, F, S, weightedBernoulliClosedRateBase]
    rw [hB_eq] at hmul_lt
    nlinarith
  have hquot : S / pHi < F / (1 - pHi) := by
    rw [div_lt_div_iff₀ hpHi0 (sub_pos.mpr hpHi1)]
    nlinarith
  have hdiff_neg : S / pHi - F / (1 - pHi) < 0 :=
    sub_neg.mpr hquot
  have haHi_pos : 0 < aHi :=
    div_pos hgHi hGpos
  have hfactored :
      (1 - pLo) ^ (gLo / (gHi + gLo)) *
          ((-1) * (gHi / (gHi + gLo)) *
            (1 - pHi) ^ (gHi / (gHi + gLo) - 1)) +
        pLo ^ (gLo / (gHi + gLo)) *
          ((gHi / (gHi + gLo)) *
            pHi ^ (gHi / (gHi + gLo) - 1)) =
        aHi * (S / pHi - F / (1 - pHi)) := by
    dsimp [aHi, S, F, weightedBernoulliSuccessBase,
      weightedBernoulliFailureBase]
    rw [Real.rpow_sub_one (ne_of_gt (sub_pos.mpr hpHi1)),
      Real.rpow_sub_one (ne_of_gt hpHi0)]
    field_simp [ne_of_gt hpHi0, ne_of_gt (sub_pos.mpr hpHi1)]
    ring
  rw [hfactored]
  exact mul_neg_of_pos_of_neg haHi_pos hdiff_neg

/--
For fixed higher endpoint, moving the lower endpoint upward toward it weakly
increases the closed-rate base.
-/
theorem weightedBernoulliClosedRateBase_le_of_lo_le
    {gHi gLo pHi pLo pLo' : ℝ}
    (hgHi : 0 ≤ gHi) (hgLo : 0 ≤ gLo) (hGpos : 0 < gHi + gLo)
    (hpLo0 : 0 < pLo) (hpLo_le : pLo ≤ pLo')
    (hpLo'_le_hi : pLo' ≤ pHi) (hpHi1 : pHi < 1) :
    weightedBernoulliClosedRateBase gHi gLo pHi pLo ≤
      weightedBernoulliClosedRateBase gHi gLo pHi pLo' := by
  let f : ℝ → ℝ := fun x => weightedBernoulliClosedRateBase gHi gLo pHi x
  have hpHi0 : 0 < pHi := hpLo0.trans_le (hpLo_le.trans hpLo'_le_hi)
  have hcont : ContinuousOn f (Set.Icc pLo pLo') := by
    intro x hx
    have hx0 : 0 < x := hpLo0.trans_le hx.1
    have hx1 : x < 1 :=
      lt_of_le_of_lt hx.2 (hpLo'_le_hi.trans_lt hpHi1)
    exact (weightedBernoulliClosedRateBase_hasDerivAt_lo
      (gHi := gHi) (gLo := gLo) (pHi := pHi) (pLo := x)
      hx0 hx1).continuousAt.continuousWithinAt
  have hderiv :
      ∀ x ∈ Set.Ioo pLo pLo',
        HasDerivAt f
          (((-1) * (gLo / (gHi + gLo)) *
                (1 - x) ^ (gLo / (gHi + gLo) - 1)) *
              (1 - pHi) ^ (gHi / (gHi + gLo)) +
            ((gLo / (gHi + gLo)) *
                x ^ (gLo / (gHi + gLo) - 1)) *
              pHi ^ (gHi / (gHi + gLo))) x := by
    intro x hx
    have hx0 : 0 < x := hpLo0.trans hx.1
    have hx1 : x < 1 :=
      lt_trans (lt_of_lt_of_le hx.2 hpLo'_le_hi) hpHi1
    exact weightedBernoulliClosedRateBase_hasDerivAt_lo
      (gHi := gHi) (gLo := gLo) (pHi := pHi) (pLo := x)
      hx0 hx1
  have hnonneg :
      ∀ x ∈ Set.Ioo pLo pLo',
        0 ≤
          ((-1) * (gLo / (gHi + gLo)) *
                (1 - x) ^ (gLo / (gHi + gLo) - 1)) *
              (1 - pHi) ^ (gHi / (gHi + gLo)) +
            ((gLo / (gHi + gLo)) *
                x ^ (gLo / (gHi + gLo) - 1)) *
              pHi ^ (gHi / (gHi + gLo)) := by
    intro x hx
    have hx0 : 0 < x := hpLo0.trans hx.1
    have hx1 : x < 1 :=
      lt_trans (lt_of_lt_of_le hx.2 hpLo'_le_hi) hpHi1
    have hx_le_hi : x ≤ pHi := hx.2.le.trans hpLo'_le_hi
    exact weightedBernoulliClosedRateBase_deriv_lo_nonneg_of_le
      hgHi hgLo hGpos hpHi0 hpHi1 hx0 hx1 hx_le_hi
  exact
    AppliedModelingLib.Optimization.endpoint_path_le_of_hasDerivAt_nonneg_on_Icc
      (f := f)
      (f' := fun x =>
        ((-1) * (gLo / (gHi + gLo)) *
              (1 - x) ^ (gLo / (gHi + gLo) - 1)) *
            (1 - pHi) ^ (gHi / (gHi + gLo)) +
          ((gLo / (gHi + gLo)) *
              x ^ (gLo / (gHi + gLo) - 1)) *
            pHi ^ (gHi / (gHi + gLo)))
      hpLo_le hcont hderiv hnonneg

/--
For fixed higher endpoint, moving the lower endpoint strictly upward toward it
strictly increases the closed-rate base when both sample weights are positive.
-/
theorem weightedBernoulliClosedRateBase_lt_of_lo_lt
    {gHi gLo pHi pLo pLo' : ℝ}
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hpLo0 : 0 < pLo) (hpLo_lt : pLo < pLo')
    (hpLo'_le_hi : pLo' ≤ pHi) (hpHi1 : pHi < 1) :
    weightedBernoulliClosedRateBase gHi gLo pHi pLo <
      weightedBernoulliClosedRateBase gHi gLo pHi pLo' := by
  let f : ℝ → ℝ := fun x => weightedBernoulliClosedRateBase gHi gLo pHi x
  have hpHi0 : 0 < pHi := hpLo0.trans (hpLo_lt.trans_le hpLo'_le_hi)
  have hcont : ContinuousOn f (Set.Icc pLo pLo') := by
    intro x hx
    have hx0 : 0 < x := hpLo0.trans_le hx.1
    have hx1 : x < 1 :=
      lt_of_le_of_lt hx.2 (hpLo'_le_hi.trans_lt hpHi1)
    exact (weightedBernoulliClosedRateBase_hasDerivAt_lo
      (gHi := gHi) (gLo := gLo) (pHi := pHi) (pLo := x)
      hx0 hx1).continuousAt.continuousWithinAt
  have hderiv :
      ∀ x ∈ Set.Ioo pLo pLo',
        HasDerivAt f
          (((-1) * (gLo / (gHi + gLo)) *
                (1 - x) ^ (gLo / (gHi + gLo) - 1)) *
              (1 - pHi) ^ (gHi / (gHi + gLo)) +
            ((gLo / (gHi + gLo)) *
                x ^ (gLo / (gHi + gLo) - 1)) *
              pHi ^ (gHi / (gHi + gLo))) x := by
    intro x hx
    have hx0 : 0 < x := hpLo0.trans hx.1
    have hx1 : x < 1 :=
      lt_trans (lt_of_lt_of_le hx.2 hpLo'_le_hi) hpHi1
    exact weightedBernoulliClosedRateBase_hasDerivAt_lo
      (gHi := gHi) (gLo := gLo) (pHi := pHi) (pLo := x)
      hx0 hx1
  have hpos :
      ∀ x ∈ Set.Ioo pLo pLo',
        0 <
          ((-1) * (gLo / (gHi + gLo)) *
                (1 - x) ^ (gLo / (gHi + gLo) - 1)) *
              (1 - pHi) ^ (gHi / (gHi + gLo)) +
            ((gLo / (gHi + gLo)) *
                x ^ (gLo / (gHi + gLo) - 1)) *
              pHi ^ (gHi / (gHi + gLo)) := by
    intro x hx
    have hx0 : 0 < x := hpLo0.trans hx.1
    have hx1 : x < 1 :=
      lt_trans (lt_of_lt_of_le hx.2 hpLo'_le_hi) hpHi1
    have hx_lt_hi : x < pHi := hx.2.trans_le hpLo'_le_hi
    exact weightedBernoulliClosedRateBase_deriv_lo_pos_of_lt
      hgHi hgLo hpHi0 hpHi1 hx0 hx1 hx_lt_hi
  exact
    AppliedModelingLib.Optimization.endpoint_path_lt_of_hasDerivAt_pos_on_Icc
      (f := f)
      (f' := fun x =>
        ((-1) * (gLo / (gHi + gLo)) *
              (1 - x) ^ (gLo / (gHi + gLo) - 1)) *
            (1 - pHi) ^ (gHi / (gHi + gLo)) +
          ((gLo / (gHi + gLo)) *
              x ^ (gLo / (gHi + gLo) - 1)) *
            pHi ^ (gHi / (gHi + gLo)))
      hpLo_lt hcont hderiv hpos

/--
For fixed lower endpoint, moving the higher endpoint downward toward it weakly
increases the closed-rate base.
-/
theorem weightedBernoulliClosedRateBase_le_of_hi_le
    {gHi gLo pHi pHi' pLo : ℝ}
    (hgHi : 0 ≤ gHi) (hgLo : 0 ≤ gLo) (hGpos : 0 < gHi + gLo)
    (hpLo0 : 0 < pLo) (hpLo_le_hi' : pLo ≤ pHi')
    (hpHi'_le : pHi' ≤ pHi) (hpHi1 : pHi < 1) :
    weightedBernoulliClosedRateBase gHi gLo pHi pLo ≤
      weightedBernoulliClosedRateBase gHi gLo pHi' pLo := by
  let f : ℝ → ℝ := fun x => weightedBernoulliClosedRateBase gHi gLo x pLo
  have hpLo1 : pLo < 1 :=
    lt_of_le_of_lt (hpLo_le_hi'.trans hpHi'_le) hpHi1
  have hcont : ContinuousOn f (Set.Icc pHi' pHi) := by
    intro x hx
    have hx0 : 0 < x := hpLo0.trans_le (hpLo_le_hi'.trans hx.1)
    have hx1 : x < 1 := hx.2.trans_lt hpHi1
    exact (weightedBernoulliClosedRateBase_hasDerivAt_hi
      (gHi := gHi) (gLo := gLo) (pHi := x) (pLo := pLo)
      hx0 hx1).continuousAt.continuousWithinAt
  have hderiv :
      ∀ x ∈ Set.Ioo pHi' pHi,
        HasDerivAt f
          ((1 - pLo) ^ (gLo / (gHi + gLo)) *
              ((-1) * (gHi / (gHi + gLo)) *
                (1 - x) ^ (gHi / (gHi + gLo) - 1)) +
            pLo ^ (gLo / (gHi + gLo)) *
              ((gHi / (gHi + gLo)) *
                x ^ (gHi / (gHi + gLo) - 1))) x := by
    intro x hx
    have hx0 : 0 < x := hpLo0.trans_le (hpLo_le_hi'.trans hx.1.le)
    have hx1 : x < 1 := hx.2.trans hpHi1
    exact weightedBernoulliClosedRateBase_hasDerivAt_hi
      (gHi := gHi) (gLo := gLo) (pHi := x) (pLo := pLo)
      hx0 hx1
  have hnonpos :
      ∀ x ∈ Set.Ioo pHi' pHi,
        ((1 - pLo) ^ (gLo / (gHi + gLo)) *
              ((-1) * (gHi / (gHi + gLo)) *
                (1 - x) ^ (gHi / (gHi + gLo) - 1)) +
            pLo ^ (gLo / (gHi + gLo)) *
              ((gHi / (gHi + gLo)) *
                x ^ (gHi / (gHi + gLo) - 1))) ≤ 0 := by
    intro x hx
    have hx0 : 0 < x := hpLo0.trans_le (hpLo_le_hi'.trans hx.1.le)
    have hx1 : x < 1 := hx.2.trans hpHi1
    have hpLo_le_x : pLo ≤ x := hpLo_le_hi'.trans hx.1.le
    exact weightedBernoulliClosedRateBase_deriv_hi_nonpos_of_le
      hgHi hgLo hGpos hx0 hx1 hpLo0 hpLo1 hpLo_le_x
  exact
    AppliedModelingLib.Optimization.endpoint_path_ge_of_hasDerivAt_nonpos_on_Icc
      (f := f)
      (f' := fun x =>
        (1 - pLo) ^ (gLo / (gHi + gLo)) *
            ((-1) * (gHi / (gHi + gLo)) *
              (1 - x) ^ (gHi / (gHi + gLo) - 1)) +
          pLo ^ (gLo / (gHi + gLo)) *
            ((gHi / (gHi + gLo)) *
              x ^ (gHi / (gHi + gLo) - 1)))
      hpHi'_le hcont hderiv hnonpos

/--
For fixed lower endpoint, moving the higher endpoint strictly downward toward
it strictly increases the closed-rate base when both sample weights are
positive.
-/
theorem weightedBernoulliClosedRateBase_lt_of_hi_lt
    {gHi gLo pHi pHi' pLo : ℝ}
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hpLo0 : 0 < pLo) (hpLo_le_hi' : pLo ≤ pHi')
    (hpHi'_lt : pHi' < pHi) (hpHi1 : pHi < 1) :
    weightedBernoulliClosedRateBase gHi gLo pHi pLo <
      weightedBernoulliClosedRateBase gHi gLo pHi' pLo := by
  let f : ℝ → ℝ := fun x => weightedBernoulliClosedRateBase gHi gLo x pLo
  have hpLo1 : pLo < 1 :=
    lt_of_le_of_lt (hpLo_le_hi'.trans hpHi'_lt.le) hpHi1
  have hcont : ContinuousOn f (Set.Icc pHi' pHi) := by
    intro x hx
    have hx0 : 0 < x := hpLo0.trans_le (hpLo_le_hi'.trans hx.1)
    have hx1 : x < 1 := hx.2.trans_lt hpHi1
    exact (weightedBernoulliClosedRateBase_hasDerivAt_hi
      (gHi := gHi) (gLo := gLo) (pHi := x) (pLo := pLo)
      hx0 hx1).continuousAt.continuousWithinAt
  have hderiv :
      ∀ x ∈ Set.Ioo pHi' pHi,
        HasDerivAt f
          ((1 - pLo) ^ (gLo / (gHi + gLo)) *
              ((-1) * (gHi / (gHi + gLo)) *
                (1 - x) ^ (gHi / (gHi + gLo) - 1)) +
            pLo ^ (gLo / (gHi + gLo)) *
              ((gHi / (gHi + gLo)) *
                x ^ (gHi / (gHi + gLo) - 1))) x := by
    intro x hx
    have hx0 : 0 < x := hpLo0.trans_le (hpLo_le_hi'.trans hx.1.le)
    have hx1 : x < 1 := hx.2.trans hpHi1
    exact weightedBernoulliClosedRateBase_hasDerivAt_hi
      (gHi := gHi) (gLo := gLo) (pHi := x) (pLo := pLo)
      hx0 hx1
  have hneg :
      ∀ x ∈ Set.Ioo pHi' pHi,
        ((1 - pLo) ^ (gLo / (gHi + gLo)) *
              ((-1) * (gHi / (gHi + gLo)) *
                (1 - x) ^ (gHi / (gHi + gLo) - 1)) +
            pLo ^ (gLo / (gHi + gLo)) *
              ((gHi / (gHi + gLo)) *
                x ^ (gHi / (gHi + gLo) - 1))) < 0 := by
    intro x hx
    have hx0 : 0 < x := hpLo0.trans_le (hpLo_le_hi'.trans hx.1.le)
    have hx1 : x < 1 := hx.2.trans hpHi1
    have hpLo_lt_x : pLo < x := lt_of_le_of_lt hpLo_le_hi' hx.1
    exact weightedBernoulliClosedRateBase_deriv_hi_neg_of_lt
      hgHi hgLo hx0 hx1 hpLo0 hpLo1 hpLo_lt_x
  exact
    AppliedModelingLib.Optimization.endpoint_path_gt_of_hasDerivAt_neg_on_Icc
      (f := f)
      (f' := fun x =>
        (1 - pLo) ^ (gLo / (gHi + gLo)) *
            ((-1) * (gHi / (gHi + gLo)) *
              (1 - x) ^ (gHi / (gHi + gLo) - 1)) +
          pLo ^ (gLo / (gHi + gLo)) *
            ((gHi / (gHi + gLo)) *
              x ^ (gHi / (gHi + gLo) - 1)))
      hpHi'_lt hcont hderiv hneg

/--
Shrinking an interior Bernoulli interval weakly increases the closed-rate base.
This is the reusable monotonicity fact behind endpoint-rate cascade arguments.
-/
theorem weightedBernoulliClosedRateBase_le_of_shrink
    {gHi gLo pHi pLo pHi' pLo' : ℝ}
    (hgHi : 0 ≤ gHi) (hgLo : 0 ≤ gLo) (hGpos : 0 < gHi + gLo)
    (hpLo0 : 0 < pLo)
    (hpLo_le_pLo' : pLo ≤ pLo')
    (hpLo'_le_pHi' : pLo' ≤ pHi')
    (hpHi'_le_pHi : pHi' ≤ pHi)
    (hpHi1 : pHi < 1) :
    weightedBernoulliClosedRateBase gHi gLo pHi pLo ≤
      weightedBernoulliClosedRateBase gHi gLo pHi' pLo' := by
  have hpLo'_le_pHi : pLo' ≤ pHi := hpLo'_le_pHi'.trans hpHi'_le_pHi
  have hlow :
      weightedBernoulliClosedRateBase gHi gLo pHi pLo ≤
        weightedBernoulliClosedRateBase gHi gLo pHi pLo' :=
    weightedBernoulliClosedRateBase_le_of_lo_le
      hgHi hgLo hGpos hpLo0 hpLo_le_pLo' hpLo'_le_pHi hpHi1
  have hpLo'0 : 0 < pLo' := hpLo0.trans_le hpLo_le_pLo'
  have hhi :
      weightedBernoulliClosedRateBase gHi gLo pHi pLo' ≤
        weightedBernoulliClosedRateBase gHi gLo pHi' pLo' :=
    weightedBernoulliClosedRateBase_le_of_hi_le
      hgHi hgLo hGpos hpLo'0 hpLo'_le_pHi' hpHi'_le_pHi hpHi1
  exact hlow.trans hhi

/--
Shrinking an interior Bernoulli interval weakly lowers the closed threshold
rate. Equivalently, among nested intervals with fixed sample weights, the
wider interval has at least as large an error exponent.
-/
theorem weightedBernoulliClosedThresholdRate_le_of_shrink
    {gHi gLo pHi pLo pHi' pLo' : ℝ}
    (hgHi : 0 ≤ gHi) (hgLo : 0 ≤ gLo) (hGpos : 0 < gHi + gLo)
    (hpLo0 : 0 < pLo)
    (hpLo_le_pLo' : pLo ≤ pLo')
    (hpLo'_le_pHi' : pLo' ≤ pHi')
    (hpHi'_le_pHi : pHi' ≤ pHi)
    (hpHi1 : pHi < 1) :
    weightedBernoulliClosedThresholdRate gHi gLo pHi' pLo' ≤
      weightedBernoulliClosedThresholdRate gHi gLo pHi pLo := by
  have hpHi0 : 0 < pHi :=
    hpLo0.trans_le
      (hpLo_le_pLo'.trans (hpLo'_le_pHi'.trans hpHi'_le_pHi))
  have hpLo1 : pLo < 1 :=
    lt_of_le_of_lt
      (hpLo_le_pLo'.trans (hpLo'_le_pHi'.trans hpHi'_le_pHi))
      hpHi1
  exact
    weightedBernoulliClosedThresholdRate_le_of_closedRateBase_le
      hGpos.le
      (weightedBernoulliClosedRateBase_pos hpHi0 hpHi1 hpLo0 hpLo1)
      (weightedBernoulliClosedRateBase_le_of_shrink
        hgHi hgLo hGpos hpLo0 hpLo_le_pLo' hpLo'_le_pHi'
        hpHi'_le_pHi hpHi1)

/--
If a target is strictly below the closed threshold rate on a nested interior
subinterval, then it is strictly below the closed threshold rate on the wider
interval.  This is the strict-target packaging of
`weightedBernoulliClosedThresholdRate_le_of_shrink`.
-/
theorem lt_weightedBernoulliClosedThresholdRate_of_lt_of_shrink
    {gHi gLo pHi pLo pHi' pLo' target : ℝ}
    (hgHi : 0 ≤ gHi) (hgLo : 0 ≤ gLo) (hGpos : 0 < gHi + gLo)
    (hpLo0 : 0 < pLo)
    (hpLo_le_pLo' : pLo ≤ pLo')
    (hpLo'_le_pHi' : pLo' ≤ pHi')
    (hpHi'_le_pHi : pHi' ≤ pHi)
    (hpHi1 : pHi < 1)
    (htarget_lt :
      target <
        weightedBernoulliClosedThresholdRate gHi gLo pHi' pLo') :
    target <
      weightedBernoulliClosedThresholdRate gHi gLo pHi pLo :=
  htarget_lt.trans_le
    (weightedBernoulliClosedThresholdRate_le_of_shrink
      hgHi hgLo hGpos hpLo0 hpLo_le_pLo' hpLo'_le_pHi'
      hpHi'_le_pHi hpHi1)

/--
Increasing the lower Bernoulli endpoint from `pLo` to `pLo'` can enlarge the
closed-rate base by at most the success-side multiplicative factor
`(pLo' / pLo) ^ (gLo / (gHi + gLo))`.
-/
theorem weightedBernoulliClosedRateBase_low_shift_le_mul_ratio_rpow
    {gHi gLo pHi pLo pLo' : ℝ}
    (hgHi : 0 ≤ gHi) (hgLo : 0 ≤ gLo) (hGpos : 0 < gHi + gLo)
    (hpHi0 : 0 < pHi) (hpHi1 : pHi < 1)
    (hpLo0 : 0 < pLo) (hpLo_le : pLo ≤ pLo') (hpLo'1 : pLo' < 1) :
    weightedBernoulliClosedRateBase gHi gLo pHi pLo' ≤
      weightedBernoulliClosedRateBase gHi gLo pHi pLo *
        (pLo' / pLo) ^ (gLo / (gHi + gLo)) := by
  let aLo : ℝ := gLo / (gHi + gLo)
  let aHi : ℝ := gHi / (gHi + gLo)
  let ratio : ℝ := pLo' / pLo
  have haLo_nonneg : 0 ≤ aLo := by
    dsimp [aLo]
    exact div_nonneg hgLo hGpos.le
  have haHi_nonneg : 0 ≤ aHi := by
    dsimp [aHi]
    exact div_nonneg hgHi hGpos.le
  have hpLo'0 : 0 < pLo' := hpLo0.trans_le hpLo_le
  have hratio_pos : 0 < ratio := by
    dsimp [ratio]
    exact div_pos hpLo'0 hpLo0
  have hratio_nonneg : 0 ≤ ratio := hratio_pos.le
  have hratio_ge_one : 1 ≤ ratio := by
    dsimp [ratio]
    rw [le_div_iff₀ hpLo0]
    simpa using hpLo_le
  have hratio_pow_ge_one : 1 ≤ ratio ^ aLo := by
    have hpow :=
      Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hratio_ge_one
        haLo_nonneg
    simpa using hpow
  have hfailLo_nonneg : 0 ≤ 1 - pLo := by linarith
  have hfailLo'_nonneg : 0 ≤ 1 - pLo' := by linarith
  have hfailHi_nonneg : 0 ≤ 1 - pHi := by linarith
  have hfailLo_le : 1 - pLo' ≤ 1 - pLo := by linarith
  have hfail_pow_le :
      (1 - pLo') ^ aLo ≤ (1 - pLo) ^ aLo :=
    Real.rpow_le_rpow hfailLo'_nonneg hfailLo_le haLo_nonneg
  have hfailHi_pow_nonneg :
      0 ≤ (1 - pHi) ^ aHi :=
    Real.rpow_nonneg hfailHi_nonneg aHi
  have hfailure_le :
      (1 - pLo') ^ aLo * (1 - pHi) ^ aHi ≤
        ((1 - pLo) ^ aLo * (1 - pHi) ^ aHi) *
          ratio ^ aLo := by
    have hfirst :
        (1 - pLo') ^ aLo * (1 - pHi) ^ aHi ≤
          (1 - pLo) ^ aLo * (1 - pHi) ^ aHi :=
      mul_le_mul_of_nonneg_right hfail_pow_le hfailHi_pow_nonneg
    have hold_nonneg :
        0 ≤ (1 - pLo) ^ aLo * (1 - pHi) ^ aHi :=
      mul_nonneg (Real.rpow_nonneg hfailLo_nonneg aLo)
        hfailHi_pow_nonneg
    have hsecond :
        (1 - pLo) ^ aLo * (1 - pHi) ^ aHi ≤
          ((1 - pLo) ^ aLo * (1 - pHi) ^ aHi) *
            ratio ^ aLo := by
      calc
        (1 - pLo) ^ aLo * (1 - pHi) ^ aHi =
            ((1 - pLo) ^ aLo * (1 - pHi) ^ aHi) * 1 := by ring
        _ ≤ ((1 - pLo) ^ aLo * (1 - pHi) ^ aHi) *
              ratio ^ aLo :=
            mul_le_mul_of_nonneg_left hratio_pow_ge_one hold_nonneg
    exact hfirst.trans hsecond
  have hsuccess_eq :
      pLo' ^ aLo * pHi ^ aHi =
        (pLo ^ aLo * pHi ^ aHi) * ratio ^ aLo := by
    have hmul : pLo * ratio = pLo' := by
      dsimp [ratio]
      field_simp [ne_of_gt hpLo0]
    have hpow :
        pLo' ^ aLo = pLo ^ aLo * ratio ^ aLo := by
      calc
        pLo' ^ aLo = (pLo * ratio) ^ aLo := by rw [hmul]
        _ = pLo ^ aLo * ratio ^ aLo :=
            Real.mul_rpow hpLo0.le hratio_nonneg
    rw [hpow]
    ring
  dsimp [weightedBernoulliClosedRateBase, weightedBernoulliFailureBase,
    weightedBernoulliSuccessBase, aLo, aHi, ratio]
  nlinarith

/--
Quantitative low-endpoint shift bound for the closed threshold rate. If the
lower endpoint is moved from `pLo` to `pLo'`, the closed rate decreases by at
most `gLo * log (pLo' / pLo)`.
-/
theorem weightedBernoulliClosedThresholdRate_low_shift_ge_sub_log_ratio
    {gHi gLo pHi pLo pLo' : ℝ}
    (hgHi : 0 ≤ gHi) (hgLo : 0 ≤ gLo) (hGpos : 0 < gHi + gLo)
    (hpHi0 : 0 < pHi) (hpHi1 : pHi < 1)
    (hpLo0 : 0 < pLo) (hpLo_le : pLo ≤ pLo') (hpLo'1 : pLo' < 1) :
    weightedBernoulliClosedThresholdRate gHi gLo pHi pLo -
        gLo * Real.log (pLo' / pLo) ≤
      weightedBernoulliClosedThresholdRate gHi gLo pHi pLo' := by
  let G : ℝ := gHi + gLo
  let aLo : ℝ := gLo / G
  let ratio : ℝ := pLo' / pLo
  let B : ℝ := weightedBernoulliClosedRateBase gHi gLo pHi pLo
  let B' : ℝ := weightedBernoulliClosedRateBase gHi gLo pHi pLo'
  have hpLo'0 : 0 < pLo' := hpLo0.trans_le hpLo_le
  have hpLo1 : pLo < 1 := lt_of_le_of_lt hpLo_le hpLo'1
  have hB_pos : 0 < B := by
    dsimp [B]
    exact weightedBernoulliClosedRateBase_pos hpHi0 hpHi1 hpLo0 hpLo1
  have hB'_pos : 0 < B' := by
    dsimp [B']
    exact weightedBernoulliClosedRateBase_pos hpHi0 hpHi1 hpLo'0 hpLo'1
  have hratio_pos : 0 < ratio := by
    dsimp [ratio]
    exact div_pos hpLo'0 hpLo0
  have hbase :
      B' ≤ B * ratio ^ aLo := by
    dsimp [B, ratio, aLo, G]
    exact
      weightedBernoulliClosedRateBase_low_shift_le_mul_ratio_rpow
        hgHi hgLo (by simpa [G] using hGpos) hpHi0 hpHi1
        hpLo0 hpLo_le hpLo'1
  have hlog_le :
      Real.log B' ≤ Real.log (B * ratio ^ aLo) :=
    Real.log_le_log hB'_pos hbase
  have hlog_prod :
      Real.log (B * ratio ^ aLo) =
        Real.log B + aLo * Real.log ratio := by
    rw [Real.log_mul (ne_of_gt hB_pos)
      (ne_of_gt (Real.rpow_pos_of_pos hratio_pos aLo))]
    rw [Real.log_rpow hratio_pos]
  have hGa : G * aLo = gLo := by
    dsimp [G, aLo]
    field_simp [ne_of_gt hGpos]
  calc
    weightedBernoulliClosedThresholdRate gHi gLo pHi pLo -
        gLo * Real.log (pLo' / pLo)
        =
        -G * Real.log B - gLo * Real.log ratio := by
          dsimp [weightedBernoulliClosedThresholdRate, G, B, ratio]
    _ = -G * Real.log (B * ratio ^ aLo) := by
          rw [hlog_prod]
          rw [← hGa]
          ring
    _ ≤ -G * Real.log B' := by
          nlinarith [hlog_le, hGpos]
    _ = weightedBernoulliClosedThresholdRate gHi gLo pHi pLo' := by
          dsimp [weightedBernoulliClosedThresholdRate, G, B']

/--
Grid-width form of the low-endpoint shift bound: if the new lower endpoint is
at most `delta` above the old one, the closed rate decreases by at most
`gLo * log ((pLo + delta) / pLo)`.
-/
theorem weightedBernoulliClosedThresholdRate_low_shift_ge_sub_log_add_div
    {gHi gLo pHi pLo pLo' delta : ℝ}
    (hgHi : 0 ≤ gHi) (hgLo : 0 ≤ gLo) (hGpos : 0 < gHi + gLo)
    (hpHi0 : 0 < pHi) (hpHi1 : pHi < 1)
    (hpLo0 : 0 < pLo) (hpLo_le : pLo ≤ pLo') (hpLo'_le : pLo' ≤ pLo + delta)
    (hpLo'1 : pLo' < 1) :
    weightedBernoulliClosedThresholdRate gHi gLo pHi pLo -
        gLo * Real.log ((pLo + delta) / pLo) ≤
      weightedBernoulliClosedThresholdRate gHi gLo pHi pLo' := by
  have hpLo'0 : 0 < pLo' := hpLo0.trans_le hpLo_le
  have hratio_le :
      pLo' / pLo ≤ (pLo + delta) / pLo :=
    div_le_div_of_nonneg_right hpLo'_le hpLo0.le
  have hlog_le :
      Real.log (pLo' / pLo) ≤ Real.log ((pLo + delta) / pLo) :=
    Real.log_le_log (div_pos hpLo'0 hpLo0) hratio_le
  have hmul :
      gLo * Real.log (pLo' / pLo) ≤
        gLo * Real.log ((pLo + delta) / pLo) :=
    mul_le_mul_of_nonneg_left hlog_le hgLo
  have hshift :=
    weightedBernoulliClosedThresholdRate_low_shift_ge_sub_log_ratio
      hgHi hgLo hGpos hpHi0 hpHi1 hpLo0 hpLo_le hpLo'1
  linarith

/--
Shrinking an interior Bernoulli interval with a strictly higher low endpoint
strictly increases the closed-rate base.
-/
theorem weightedBernoulliClosedRateBase_lt_of_shrink_lo_lt
    {gHi gLo pHi pLo pHi' pLo' : ℝ}
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hpLo0 : 0 < pLo)
    (hpLo_lt_pLo' : pLo < pLo')
    (hpLo'_le_pHi' : pLo' ≤ pHi')
    (hpHi'_le_pHi : pHi' ≤ pHi)
    (hpHi1 : pHi < 1) :
    weightedBernoulliClosedRateBase gHi gLo pHi pLo <
      weightedBernoulliClosedRateBase gHi gLo pHi' pLo' := by
  have hpLo'_le_pHi : pLo' ≤ pHi := hpLo'_le_pHi'.trans hpHi'_le_pHi
  have hlow :
      weightedBernoulliClosedRateBase gHi gLo pHi pLo <
        weightedBernoulliClosedRateBase gHi gLo pHi pLo' :=
    weightedBernoulliClosedRateBase_lt_of_lo_lt
      hgHi hgLo hpLo0 hpLo_lt_pLo' hpLo'_le_pHi hpHi1
  have hpLo'0 : 0 < pLo' := hpLo0.trans hpLo_lt_pLo'
  have hhi :
      weightedBernoulliClosedRateBase gHi gLo pHi pLo' ≤
        weightedBernoulliClosedRateBase gHi gLo pHi' pLo' :=
    weightedBernoulliClosedRateBase_le_of_hi_le
      hgHi.le hgLo.le (add_pos hgHi hgLo) hpLo'0
      hpLo'_le_pHi' hpHi'_le_pHi hpHi1
  exact hlow.trans_le hhi

/--
Shrinking an interior Bernoulli interval with a strictly lower high endpoint
strictly increases the closed-rate base.
-/
theorem weightedBernoulliClosedRateBase_lt_of_shrink_hi_lt
    {gHi gLo pHi pLo pHi' pLo' : ℝ}
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hpLo0 : 0 < pLo)
    (hpLo_le_pLo' : pLo ≤ pLo')
    (hpLo'_le_pHi' : pLo' ≤ pHi')
    (hpHi'_lt_pHi : pHi' < pHi)
    (hpHi1 : pHi < 1) :
    weightedBernoulliClosedRateBase gHi gLo pHi pLo <
      weightedBernoulliClosedRateBase gHi gLo pHi' pLo' := by
  have hpLo'_le_pHi : pLo' ≤ pHi := hpLo'_le_pHi'.trans hpHi'_lt_pHi.le
  have hlow :
      weightedBernoulliClosedRateBase gHi gLo pHi pLo ≤
        weightedBernoulliClosedRateBase gHi gLo pHi pLo' :=
    weightedBernoulliClosedRateBase_le_of_lo_le
      hgHi.le hgLo.le (add_pos hgHi hgLo) hpLo0
      hpLo_le_pLo' hpLo'_le_pHi hpHi1
  have hpLo'0 : 0 < pLo' := hpLo0.trans_le hpLo_le_pLo'
  have hhi :
      weightedBernoulliClosedRateBase gHi gLo pHi pLo' <
        weightedBernoulliClosedRateBase gHi gLo pHi' pLo' :=
    weightedBernoulliClosedRateBase_lt_of_hi_lt
      hgHi hgLo hpLo'0 hpLo'_le_pHi' hpHi'_lt_pHi hpHi1
  exact hlow.trans_lt hhi

/--
Shrinking an interior Bernoulli interval with a strictly higher low endpoint
strictly lowers the closed threshold rate.
-/
theorem weightedBernoulliClosedThresholdRate_lt_of_shrink_lo_lt
    {gHi gLo pHi pLo pHi' pLo' : ℝ}
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hpLo0 : 0 < pLo)
    (hpLo_lt_pLo' : pLo < pLo')
    (hpLo'_le_pHi' : pLo' ≤ pHi')
    (hpHi'_le_pHi : pHi' ≤ pHi)
    (hpHi1 : pHi < 1) :
    weightedBernoulliClosedThresholdRate gHi gLo pHi' pLo' <
      weightedBernoulliClosedThresholdRate gHi gLo pHi pLo := by
  have hpHi0 : 0 < pHi :=
    hpLo0.trans (hpLo_lt_pLo'.trans_le (hpLo'_le_pHi'.trans hpHi'_le_pHi))
  have hpLo1 : pLo < 1 :=
    hpLo_lt_pLo'.trans_le (hpLo'_le_pHi'.trans (hpHi'_le_pHi.trans hpHi1.le))
  exact
    weightedBernoulliClosedThresholdRate_lt_of_closedRateBase_lt
      (add_pos hgHi hgLo)
      (weightedBernoulliClosedRateBase_pos hpHi0 hpHi1 hpLo0 hpLo1)
      (weightedBernoulliClosedRateBase_lt_of_shrink_lo_lt
        hgHi hgLo hpLo0 hpLo_lt_pLo' hpLo'_le_pHi'
        hpHi'_le_pHi hpHi1)

/--
Shrinking an interior Bernoulli interval with a strictly lower high endpoint
strictly lowers the closed threshold rate.
-/
theorem weightedBernoulliClosedThresholdRate_lt_of_shrink_hi_lt
    {gHi gLo pHi pLo pHi' pLo' : ℝ}
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hpLo0 : 0 < pLo)
    (hpLo_le_pLo' : pLo ≤ pLo')
    (hpLo'_le_pHi' : pLo' ≤ pHi')
    (hpHi'_lt_pHi : pHi' < pHi)
    (hpHi1 : pHi < 1) :
    weightedBernoulliClosedThresholdRate gHi gLo pHi' pLo' <
      weightedBernoulliClosedThresholdRate gHi gLo pHi pLo := by
  have hpHi0 : 0 < pHi :=
    hpLo0.trans_le (hpLo_le_pLo'.trans (hpLo'_le_pHi'.trans hpHi'_lt_pHi.le))
  have hpLo1 : pLo < 1 :=
    lt_of_le_of_lt
      (hpLo_le_pLo'.trans (hpLo'_le_pHi'.trans hpHi'_lt_pHi.le))
      hpHi1
  exact
    weightedBernoulliClosedThresholdRate_lt_of_closedRateBase_lt
      (add_pos hgHi hgLo)
      (weightedBernoulliClosedRateBase_pos hpHi0 hpHi1 hpLo0 hpLo1)
      (weightedBernoulliClosedRateBase_lt_of_shrink_hi_lt
        hgHi hgLo hpLo0 hpLo_le_pLo' hpLo'_le_pHi'
        hpHi'_lt_pHi hpHi1)

/-- Distinct ordered interior Bernoulli laws have positive closed threshold rate. -/
theorem weightedBernoulliClosedThresholdRate_pos_of_lt
    {gHi gLo pHi pLo : ℝ}
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hpLo0 : 0 < pLo) (hpLo_lt_hi : pLo < pHi) (hpHi1 : pHi < 1) :
    0 < weightedBernoulliClosedThresholdRate gHi gLo pHi pLo := by
  have hpLo1 : pLo < 1 := hpLo_lt_hi.trans hpHi1
  have hlt :
      weightedBernoulliClosedThresholdRate gHi gLo pLo pLo <
        weightedBernoulliClosedThresholdRate gHi gLo pHi pLo :=
    weightedBernoulliClosedThresholdRate_lt_of_shrink_hi_lt
      (gHi := gHi) (gLo := gLo) (pHi := pHi) (pLo := pLo)
      (pHi' := pLo) (pLo' := pLo)
      hgHi hgLo hpLo0 le_rfl le_rfl hpLo_lt_hi hpHi1
  rwa [weightedBernoulliClosedThresholdRate_self hgHi hgLo hpLo0 hpLo1] at hlt

/-- Interior Bernoulli laws have nonnegative closed threshold exponent. -/
theorem weightedBernoulliClosedThresholdRate_nonneg
    {gHi gLo pHi pLo : ℝ}
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hpHi0 : 0 < pHi) (hpHi1 : pHi < 1)
    (hpLo0 : 0 < pLo) (hpLo1 : pLo < 1) :
    0 ≤ weightedBernoulliClosedThresholdRate gHi gLo pHi pLo := by
  rcases lt_trichotomy pLo pHi with hlt | heq | hgt
  · exact
      (weightedBernoulliClosedThresholdRate_pos_of_lt
        hgHi hgLo hpLo0 hlt hpHi1).le
  · subst pHi
    rw [weightedBernoulliClosedThresholdRate_self hgHi hgLo hpLo0 hpLo1]
  · rw [weightedBernoulliClosedThresholdRate_swap]
    exact
      (weightedBernoulliClosedThresholdRate_pos_of_lt
        hgLo hgHi hpHi0 hgt hpLo1).le

/--
If the low Bernoulli endpoint tends to `0` and the high endpoint tends to `1`,
the closed-rate base tends to zero from the positive side.
-/
theorem weightedBernoulliClosedRateBase_tendsto_nhdsGT_zero_of_hi_tendsto_one_lo_tendsto_zero
    {ι : Type*} {l : Filter ι} {gHi gLo : ℝ}
    {pHi pLo : ι → ℝ}
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hpHi : Filter.Tendsto pHi l (nhds (1 : ℝ)))
    (hpLo : Filter.Tendsto pLo l (nhds (0 : ℝ)))
    (hvalid :
      ∀ᶠ x in l, pHi x ∈ Set.Ioo (0 : ℝ) 1 ∧
        pLo x ∈ Set.Ioo (0 : ℝ) 1) :
    Filter.Tendsto
      (fun x : ι => weightedBernoulliClosedRateBase gHi gLo (pHi x) (pLo x))
      l (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
  let aLo : ℝ := gLo / (gHi + gLo)
  let aHi : ℝ := gHi / (gHi + gLo)
  have hG_pos : 0 < gHi + gLo := add_pos hgHi hgLo
  have haLo_nonneg : 0 ≤ aLo := by
    dsimp [aLo]
    exact div_nonneg hgLo.le hG_pos.le
  have haHi_nonneg : 0 ≤ aHi := by
    dsimp [aHi]
    exact div_nonneg hgHi.le hG_pos.le
  have haLo_pos : 0 < aLo := by
    dsimp [aLo]
    exact div_pos hgLo hG_pos
  have haHi_pos : 0 < aHi := by
    dsimp [aHi]
    exact div_pos hgHi hG_pos
  have hfailLo :
      Filter.Tendsto (fun x : ι => (1 - pLo x) ^ aLo)
        l (nhds 1) := by
    have hsub :
        Filter.Tendsto (fun x : ι => 1 - pLo x) l (nhds 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hpLo
    simpa using hsub.rpow_const (p := aLo)
      (Or.inl (by norm_num : (1 : ℝ) ≠ 0))
  have hfailHi :
      Filter.Tendsto (fun x : ι => (1 - pHi x) ^ aHi)
        l (nhds 0) := by
    have hsub :
        Filter.Tendsto (fun x : ι => 1 - pHi x) l (nhds 0) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hpHi
    simpa [Real.zero_rpow haHi_pos.ne'] using
      hsub.rpow_const (p := aHi) (Or.inr haHi_nonneg)
  have hsuccLo :
      Filter.Tendsto (fun x : ι => (pLo x) ^ aLo)
        l (nhds 0) := by
    simpa [Real.zero_rpow haLo_pos.ne'] using
      hpLo.rpow_const (p := aLo) (Or.inr haLo_nonneg)
  have hsuccHi :
      Filter.Tendsto (fun x : ι => (pHi x) ^ aHi)
        l (nhds 1) := by
    simpa using hpHi.rpow_const (p := aHi)
      (Or.inl (by norm_num : (1 : ℝ) ≠ 0))
  have hbase_nhds :
      Filter.Tendsto
        (fun x : ι =>
          weightedBernoulliClosedRateBase gHi gLo (pHi x) (pLo x))
        l (nhds 0) := by
    simpa [weightedBernoulliClosedRateBase,
      weightedBernoulliFailureBase, weightedBernoulliSuccessBase, aLo, aHi,
      add_comm, add_left_comm, add_assoc] using
      (hfailLo.mul hfailHi).add (hsuccLo.mul hsuccHi)
  have hbase_pos :
      ∀ᶠ x in l,
        weightedBernoulliClosedRateBase gHi gLo (pHi x) (pLo x) ∈
          Set.Ioi (0 : ℝ) := by
    filter_upwards [hvalid] with x hx
    exact weightedBernoulliClosedRateBase_pos
      hx.1.1 hx.1.2 hx.2.1 hx.2.2
  exact tendsto_nhdsWithin_iff.mpr ⟨hbase_nhds, hbase_pos⟩

/--
If the low Bernoulli endpoint tends to `0` and the high endpoint tends to `1`,
the closed threshold rate diverges to infinity.
-/
theorem weightedBernoulliClosedThresholdRate_tendsto_atTop_of_hi_tendsto_one_lo_tendsto_zero
    {ι : Type*} {l : Filter ι} {gHi gLo : ℝ}
    {pHi pLo : ι → ℝ}
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hpHi : Filter.Tendsto pHi l (nhds (1 : ℝ)))
    (hpLo : Filter.Tendsto pLo l (nhds (0 : ℝ)))
    (hvalid :
      ∀ᶠ x in l, pHi x ∈ Set.Ioo (0 : ℝ) 1 ∧
        pLo x ∈ Set.Ioo (0 : ℝ) 1) :
    Filter.Tendsto
      (fun x : ι =>
        weightedBernoulliClosedThresholdRate gHi gLo (pHi x) (pLo x))
      l Filter.atTop := by
  have hbase :=
    weightedBernoulliClosedRateBase_tendsto_nhdsGT_zero_of_hi_tendsto_one_lo_tendsto_zero
      hgHi hgLo hpHi hpLo hvalid
  have hlog :
      Filter.Tendsto
        (fun x : ι =>
          Real.log
            (weightedBernoulliClosedRateBase gHi gLo (pHi x) (pLo x)))
        l Filter.atBot :=
    Real.tendsto_log_nhdsGT_zero.comp hbase
  have hneglog :
      Filter.Tendsto
        (fun x : ι =>
          -Real.log
            (weightedBernoulliClosedRateBase gHi gLo (pHi x) (pLo x)))
        l Filter.atTop :=
    Filter.tendsto_neg_atBot_atTop.comp hlog
  have hG_pos : 0 < gHi + gLo := add_pos hgHi hgLo
  have hscaled :
      Filter.Tendsto
        (fun x : ι =>
          (gHi + gLo) *
            (-Real.log
              (weightedBernoulliClosedRateBase gHi gLo (pHi x) (pLo x))))
        l Filter.atTop :=
    hneglog.const_mul_atTop hG_pos
  convert hscaled using 1
  ext x
  simp [weightedBernoulliClosedThresholdRate]
  ring

/-- Continuity of the closed threshold rate in the higher Bernoulli endpoint. -/
theorem weightedBernoulliClosedThresholdRate_continuousAt_hi
    {gHi gLo pHi pLo : ℝ}
    (hpHi0 : 0 < pHi) (hpHi1 : pHi < 1)
    (hpLo0 : 0 < pLo) (hpLo1 : pLo < 1) :
    ContinuousAt
      (fun x : ℝ => weightedBernoulliClosedThresholdRate gHi gLo x pLo)
      pHi := by
  have hbase_cont :
      ContinuousAt
        (fun x : ℝ => weightedBernoulliClosedRateBase gHi gLo x pLo)
        pHi :=
    (weightedBernoulliClosedRateBase_hasDerivAt_hi
      (gHi := gHi) (gLo := gLo) (pHi := pHi) (pLo := pLo)
      hpHi0 hpHi1).continuousAt
  have hbase_pos :
      0 < weightedBernoulliClosedRateBase gHi gLo pHi pLo :=
    weightedBernoulliClosedRateBase_pos hpHi0 hpHi1 hpLo0 hpLo1
  have hlog_cont :
      ContinuousAt
        (fun x : ℝ =>
          Real.log (weightedBernoulliClosedRateBase gHi gLo x pLo))
        pHi :=
    hbase_cont.log (ne_of_gt hbase_pos)
  simpa [weightedBernoulliClosedThresholdRate] using
    hlog_cont.const_mul (-(gHi + gLo))

/--
Continuity of the closed threshold rate on a high-endpoint interval whose low
endpoint remains fixed.
-/
theorem weightedBernoulliClosedThresholdRate_continuousOn_hi_Icc
    {gHi gLo pLo left right : ℝ}
    (hpLo0 : 0 < pLo) (hpLo_le_left : pLo ≤ left) (hright1 : right < 1) :
    ContinuousOn
      (fun x : ℝ => weightedBernoulliClosedThresholdRate gHi gLo x pLo)
      (Set.Icc left right) := by
  intro x hx
  have hx0 : 0 < x := hpLo0.trans_le (hpLo_le_left.trans hx.1)
  have hx1 : x < 1 := hx.2.trans_lt hright1
  have hpLo1 : pLo < 1 := lt_of_le_of_lt (hpLo_le_left.trans hx.1) hx1
  exact
    (weightedBernoulliClosedThresholdRate_continuousAt_hi
      (gHi := gHi) (gLo := gLo) (pHi := x) (pLo := pLo)
      hx0 hx1 hpLo0 hpLo1).continuousWithinAt

/--
For a fixed low endpoint, the closed threshold rate is strictly increasing in
the high endpoint on any interval above the low endpoint.
-/
theorem weightedBernoulliClosedThresholdRate_strictMonoOn_hi_Icc
    {gHi gLo pLo left right : ℝ}
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hpLo0 : 0 < pLo) (hpLo_le_left : pLo ≤ left) (hright1 : right < 1) :
    StrictMonoOn
      (fun x : ℝ => weightedBernoulliClosedThresholdRate gHi gLo x pLo)
      (Set.Icc left right) := by
  intro x hx y hy hxy
  have hpLo_le_x : pLo ≤ x := hpLo_le_left.trans hx.1
  have hy1 : y < 1 := hy.2.trans_lt hright1
  exact
    weightedBernoulliClosedThresholdRate_lt_of_shrink_hi_lt
      (gHi := gHi) (gLo := gLo) (pHi := y) (pLo := pLo)
      (pHi' := x) (pLo' := pLo)
      hgHi hgLo hpLo0 le_rfl hpLo_le_x hxy hy1

/--
One-dimensional shooting for the closed threshold rate: if a target rate lies
between the diagonal value and the rate at a right endpoint, then there is an
interior high endpoint realizing exactly that target.
-/
theorem exists_high_endpoint_for_weightedBernoulliClosedThresholdRate
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
          pHi ≤ x) := by
  let f : ℝ → ℝ :=
    fun x => weightedBernoulliClosedThresholdRate gHi gLo x pLo
  have hcont : ContinuousOn f (Set.Icc pLo right) :=
    weightedBernoulliClosedThresholdRate_continuousOn_hi_Icc
      (gHi := gHi) (gLo := gLo) hpLo0 le_rfl hright1
  have hmono : StrictMonoOn f (Set.Icc pLo right) :=
    weightedBernoulliClosedThresholdRate_strictMonoOn_hi_Icc
      (gHi := gHi) (gLo := gLo) hgHi hgLo hpLo0 le_rfl hright1
  have hleft : f pLo < target := by
    dsimp [f]
    rw [weightedBernoulliClosedThresholdRate_self hgHi hgLo hpLo0
      (hpLo_lt_right.trans hright1)]
    exact htarget_pos
  rcases
    AppliedModelingLib.exists_threshold_of_continuous_strictMonoOn_Icc_crossing_interval
      (f := f) (level := target) (left := pLo) (right := right)
      hpLo_lt_right hcont hmono hleft htarget_lt_right with
    ⟨pHi, hpHi_mem, hpHi_rate, hlt, hgt, hle, hge⟩
  exact ⟨pHi, hpHi_mem, hpHi_rate, hlt, hgt, hle, hge⟩

/--
The high endpoint realizing a target closed threshold rate is unique inside
the bracket interval.
-/
theorem existsUnique_high_endpoint_for_weightedBernoulliClosedThresholdRate
    {gHi gLo pLo right target : ℝ}
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hpLo0 : 0 < pLo) (hpLo_lt_right : pLo < right)
    (hright1 : right < 1)
    (htarget_pos : 0 < target)
    (htarget_lt_right :
      target <
        weightedBernoulliClosedThresholdRate gHi gLo right pLo) :
    ∃! pHi : ℝ, pHi ∈ Set.Ioo pLo right ∧
      weightedBernoulliClosedThresholdRate gHi gLo pHi pLo = target := by
  rcases
    exists_high_endpoint_for_weightedBernoulliClosedThresholdRate
      hgHi hgLo hpLo0 hpLo_lt_right hright1 htarget_pos htarget_lt_right with
    ⟨pHi, hpHi_mem, hpHi_rate, _hlt, _hgt, hle, hge⟩
  refine ⟨pHi, ⟨hpHi_mem, hpHi_rate⟩, ?_⟩
  intro y hy
  have hyIcc : y ∈ Set.Icc pLo right := ⟨hy.1.1.le, hy.1.2.le⟩
  have hy_le : y ≤ pHi := (hle y hyIcc).mp hy.2.le
  have hpHi_le : pHi ≤ y := (hge y hyIcc).mp hy.2.ge
  exact le_antisymm hy_le hpHi_le

/--
Any selector that returns the high endpoint realizing each target rate is
continuous on its target domain.
-/
theorem continuousOn_highEndpointSelector_for_weightedBernoulliClosedThresholdRate
    {gHi gLo pLo right : ℝ} {targetSet : Set ℝ} {root : ℝ → ℝ}
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hpLo0 : 0 < pLo) (hpLo_lt_right : pLo < right)
    (hright1 : right < 1)
    (hroot_mem : ∀ target ∈ targetSet, root target ∈ Set.Ioo pLo right)
    (hroot_rate :
      ∀ target ∈ targetSet,
        weightedBernoulliClosedThresholdRate gHi gLo (root target) pLo =
          target) :
    ContinuousOn root targetSet := by
  let base : ℝ → ℝ :=
    fun x => weightedBernoulliClosedThresholdRate gHi gLo x pLo
  have hmono : StrictMonoOn base (Set.Icc pLo right) :=
    weightedBernoulliClosedThresholdRate_strictMonoOn_hi_Icc
      (gHi := gHi) (gLo := gLo) hgHi hgLo hpLo0 le_rfl hright1
  exact
    AppliedModelingLib.continuousOn_rightInverse_of_strictMonoOn_Icc
      (base := base) (root := root) (s := targetSet)
      (left := pLo) (right := right)
      hmono hroot_mem hroot_rate

/--
Feasibility conditions for selecting a high endpoint that realizes a target
closed threshold rate below a fixed cap.
-/
structure WeightedBernoulliHighEndpointTargetFeasible
    (gHi gLo pLo cap target : ℝ) : Prop where
  hgHi : 0 < gHi
  hgLo : 0 < gLo
  hpLo0 : 0 < pLo
  hpLo_lt_cap : pLo < cap
  hcap1 : cap < 1
  htarget_pos : 0 < target
  htarget_lt_cap :
    target < weightedBernoulliClosedThresholdRate gHi gLo cap pLo

/--
Clipped high-endpoint selector for target-rate shooting.  If the target rate is
attainable before the cap, this returns the unique interior high endpoint;
otherwise it returns the cap.
-/
def weightedBernoulliHighEndpointOfRateOrCap
    (gHi gLo pLo cap target : ℝ) : ℝ := by
  classical
  exact
    if h : WeightedBernoulliHighEndpointTargetFeasible
        gHi gLo pLo cap target then
      Classical.choose
        (exists_high_endpoint_for_weightedBernoulliClosedThresholdRate
          h.hgHi h.hgLo h.hpLo0 h.hpLo_lt_cap h.hcap1
          h.htarget_pos h.htarget_lt_cap)
    else
      cap

/-- Under feasibility, the clipped selector lies strictly between the low endpoint and cap. -/
theorem weightedBernoulliHighEndpointOfRateOrCap_mem_Ioo_of_feasible
    {gHi gLo pLo cap target : ℝ}
    (h : WeightedBernoulliHighEndpointTargetFeasible
      gHi gLo pLo cap target) :
    weightedBernoulliHighEndpointOfRateOrCap gHi gLo pLo cap target ∈
      Set.Ioo pLo cap := by
  unfold weightedBernoulliHighEndpointOfRateOrCap
  simp [h]
  simpa using
    (Classical.choose_spec
      (exists_high_endpoint_for_weightedBernoulliClosedThresholdRate
        h.hgHi h.hgLo h.hpLo0 h.hpLo_lt_cap h.hcap1
        h.htarget_pos h.htarget_lt_cap)).1

/-- Under feasibility, the clipped selector realizes the requested target rate. -/
theorem weightedBernoulliHighEndpointOfRateOrCap_rate_of_feasible
    {gHi gLo pLo cap target : ℝ}
    (h : WeightedBernoulliHighEndpointTargetFeasible
      gHi gLo pLo cap target) :
    weightedBernoulliClosedThresholdRate gHi gLo
        (weightedBernoulliHighEndpointOfRateOrCap gHi gLo pLo cap target)
        pLo =
      target := by
  unfold weightedBernoulliHighEndpointOfRateOrCap
  simp [h]
  simpa using
    (Classical.choose_spec
      (exists_high_endpoint_for_weightedBernoulliClosedThresholdRate
        h.hgHi h.hgLo h.hpLo0 h.hpLo_lt_cap h.hcap1
        h.htarget_pos h.htarget_lt_cap)).2.1

/-- If feasibility fails, the clipped selector returns the cap. -/
theorem weightedBernoulliHighEndpointOfRateOrCap_eq_cap_of_not_feasible
    {gHi gLo pLo cap target : ℝ}
    (h : ¬ WeightedBernoulliHighEndpointTargetFeasible
      gHi gLo pLo cap target) :
    weightedBernoulliHighEndpointOfRateOrCap gHi gLo pLo cap target = cap := by
  simp [weightedBernoulliHighEndpointOfRateOrCap, h]

/-- If the low endpoint is not strictly below the cap, the clipped selector returns the cap. -/
theorem weightedBernoulliHighEndpointOfRateOrCap_eq_cap_of_not_lt_cap
    {gHi gLo pLo cap target : ℝ} (hnot_lt : ¬ pLo < cap) :
    weightedBernoulliHighEndpointOfRateOrCap gHi gLo pLo cap target = cap := by
  refine weightedBernoulliHighEndpointOfRateOrCap_eq_cap_of_not_feasible ?_
  intro h
  exact hnot_lt h.hpLo_lt_cap

/-- Under weak bracket validity, the clipped high-endpoint selector is no larger than the cap. -/
theorem weightedBernoulliHighEndpointOfRateOrCap_le_cap
    {gHi gLo pLo cap target : ℝ} (hpLo_le_cap : pLo ≤ cap) :
    weightedBernoulliHighEndpointOfRateOrCap gHi gLo pLo cap target ≤ cap := by
  by_cases h : WeightedBernoulliHighEndpointTargetFeasible
      gHi gLo pLo cap target
  · exact
      (weightedBernoulliHighEndpointOfRateOrCap_mem_Ioo_of_feasible h).2.le
  · rw [weightedBernoulliHighEndpointOfRateOrCap_eq_cap_of_not_feasible h]

/-- Under weak bracket validity, the clipped high-endpoint selector is at least the low endpoint. -/
theorem le_weightedBernoulliHighEndpointOfRateOrCap
    {gHi gLo pLo cap target : ℝ} (hpLo_le_cap : pLo ≤ cap) :
    pLo ≤ weightedBernoulliHighEndpointOfRateOrCap gHi gLo pLo cap target := by
  by_cases h : WeightedBernoulliHighEndpointTargetFeasible
      gHi gLo pLo cap target
  · exact
      (weightedBernoulliHighEndpointOfRateOrCap_mem_Ioo_of_feasible h).1.le
  · rw [weightedBernoulliHighEndpointOfRateOrCap_eq_cap_of_not_feasible h]
    exact hpLo_le_cap

/-- Under weak bracket validity, the clipped high-endpoint selector lies in the bracket. -/
theorem weightedBernoulliHighEndpointOfRateOrCap_mem_Icc
    {gHi gLo pLo cap target : ℝ} (hpLo_le_cap : pLo ≤ cap) :
    weightedBernoulliHighEndpointOfRateOrCap gHi gLo pLo cap target ∈
      Set.Icc pLo cap :=
  ⟨le_weightedBernoulliHighEndpointOfRateOrCap hpLo_le_cap,
    weightedBernoulliHighEndpointOfRateOrCap_le_cap hpLo_le_cap⟩

/-- The clipped high-endpoint selector always lies above `min pLo cap`. -/
theorem min_le_weightedBernoulliHighEndpointOfRateOrCap
    {gHi gLo pLo cap target : ℝ} :
    min pLo cap ≤
      weightedBernoulliHighEndpointOfRateOrCap gHi gLo pLo cap target := by
  by_cases hle : pLo ≤ cap
  · exact (min_le_left _ _).trans
      (le_weightedBernoulliHighEndpointOfRateOrCap hle)
  · have hnot_lt : ¬ pLo < cap := not_lt.mpr (le_of_not_ge hle)
    rw [weightedBernoulliHighEndpointOfRateOrCap_eq_cap_of_not_lt_cap hnot_lt]
    exact min_le_right _ _

/-- The clipped high-endpoint selector always lies below `max pLo cap`. -/
theorem weightedBernoulliHighEndpointOfRateOrCap_le_max
    {gHi gLo pLo cap target : ℝ} :
    weightedBernoulliHighEndpointOfRateOrCap gHi gLo pLo cap target ≤
      max pLo cap := by
  by_cases hle : pLo ≤ cap
  · exact (weightedBernoulliHighEndpointOfRateOrCap_le_cap hle).trans
      (le_max_right _ _)
  · have hnot_lt : ¬ pLo < cap := not_lt.mpr (le_of_not_ge hle)
    rw [weightedBernoulliHighEndpointOfRateOrCap_eq_cap_of_not_lt_cap hnot_lt]
    exact le_max_right _ _

/--
The clipped high-endpoint selector never produces a closed threshold rate above
the target, assuming positive weights and a weak valid bracket.
-/
theorem weightedBernoulliClosedThresholdRate_highEndpointOfRateOrCap_le_target
    {gHi gLo pLo cap target : ℝ}
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hpLo0 : 0 < pLo) (hpLo_le_cap : pLo ≤ cap)
    (hcap1 : cap < 1) (htarget_pos : 0 < target) :
    weightedBernoulliClosedThresholdRate gHi gLo
        (weightedBernoulliHighEndpointOfRateOrCap gHi gLo pLo cap target)
        pLo ≤ target := by
  by_cases h : WeightedBernoulliHighEndpointTargetFeasible
      gHi gLo pLo cap target
  · rw [weightedBernoulliHighEndpointOfRateOrCap_rate_of_feasible h]
  · rw [weightedBernoulliHighEndpointOfRateOrCap_eq_cap_of_not_feasible h]
    rcases lt_or_eq_of_le hpLo_le_cap with hpLo_lt_cap | hcap_eq
    · have hfeas_except :
          WeightedBernoulliHighEndpointTargetFeasible
            gHi gLo pLo cap target ↔
          target < weightedBernoulliClosedThresholdRate gHi gLo cap pLo := by
        constructor
        · intro hfeas
          exact hfeas.htarget_lt_cap
        · intro htarget_lt_cap
          exact
            ⟨hgHi, hgLo, hpLo0, hpLo_lt_cap, hcap1,
              htarget_pos, htarget_lt_cap⟩
      have hnot_lt :
          ¬ target < weightedBernoulliClosedThresholdRate gHi gLo cap pLo := by
        intro htarget_lt_cap
        exact h ((hfeas_except.mpr htarget_lt_cap))
      exact le_of_not_gt hnot_lt
    · subst cap
      have hpLo1 : pLo < 1 := hcap1
      rw [weightedBernoulliClosedThresholdRate_self hgHi hgLo hpLo0 hpLo1]
      exact htarget_pos.le

/--
If the target rate is below the closed rate at an interior comparison point,
then the clipped high-endpoint selector lies below that point.
-/
theorem weightedBernoulliHighEndpointOfRateOrCap_lt_of_target_lt_rate
    {gHi gLo pLo cap target eps : ℝ}
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hpLo0 : 0 < pLo) (hpLo_lt_eps : pLo < eps)
    (heps_lt_cap : eps < cap) (hcap1 : cap < 1)
    (htarget_pos : 0 < target)
    (htarget_lt_eps :
      target < weightedBernoulliClosedThresholdRate gHi gLo eps pLo) :
    weightedBernoulliHighEndpointOfRateOrCap gHi gLo pLo cap target < eps := by
  by_cases hfeasible :
      WeightedBernoulliHighEndpointTargetFeasible gHi gLo pLo cap target
  · let selected : ℝ :=
      weightedBernoulliHighEndpointOfRateOrCap gHi gLo pLo cap target
    have hselected_mem :
        selected ∈ Set.Ioo pLo cap := by
      dsimp [selected]
      exact weightedBernoulliHighEndpointOfRateOrCap_mem_Ioo_of_feasible
        hfeasible
    have hselected_rate :
        weightedBernoulliClosedThresholdRate gHi gLo selected pLo =
          target := by
      dsimp [selected]
      exact weightedBernoulliHighEndpointOfRateOrCap_rate_of_feasible
        hfeasible
    by_contra hnot_lt
    have heps_le_selected : eps ≤ selected := le_of_not_gt hnot_lt
    rcases lt_or_eq_of_le heps_le_selected with heps_lt_selected |
      heps_eq_selected
    · have hrate_lt :
          weightedBernoulliClosedThresholdRate gHi gLo eps pLo <
            weightedBernoulliClosedThresholdRate gHi gLo selected pLo :=
        weightedBernoulliClosedThresholdRate_lt_of_shrink_hi_lt
          (gHi := gHi) (gLo := gLo) (pHi := selected) (pLo := pLo)
          (pHi' := eps) (pLo' := pLo)
          hgHi hgLo hpLo0 le_rfl hpLo_lt_eps.le heps_lt_selected
          (hselected_mem.2.trans hcap1)
      have hcycle : target < target := by
        calc
          target < weightedBernoulliClosedThresholdRate gHi gLo eps pLo :=
            htarget_lt_eps
          _ < weightedBernoulliClosedThresholdRate gHi gLo selected pLo :=
            hrate_lt
          _ = target := hselected_rate
      exact (lt_irrefl target) hcycle
    · have hcycle : target < target := by
        calc
          target < weightedBernoulliClosedThresholdRate gHi gLo eps pLo :=
            htarget_lt_eps
          _ = weightedBernoulliClosedThresholdRate gHi gLo selected pLo := by
            rw [heps_eq_selected]
          _ = target := hselected_rate
      exact (lt_irrefl target) hcycle
  · have hpLo_lt_cap : pLo < cap := hpLo_lt_eps.trans heps_lt_cap
    have hrate_eps_lt_cap :
        weightedBernoulliClosedThresholdRate gHi gLo eps pLo <
          weightedBernoulliClosedThresholdRate gHi gLo cap pLo :=
      weightedBernoulliClosedThresholdRate_lt_of_shrink_hi_lt
        (gHi := gHi) (gLo := gLo) (pHi := cap) (pLo := pLo)
        (pHi' := eps) (pLo' := pLo)
        hgHi hgLo hpLo0 le_rfl hpLo_lt_eps.le heps_lt_cap hcap1
    have htarget_lt_cap :
        target < weightedBernoulliClosedThresholdRate gHi gLo cap pLo :=
      htarget_lt_eps.trans hrate_eps_lt_cap
    exact False.elim
      (hfeasible
        ⟨hgHi, hgLo, hpLo0, hpLo_lt_cap, hcap1,
          htarget_pos, htarget_lt_cap⟩)

/--
If the closed rate at an interior comparison point is below the target and the
target is attainable before the cap, then the clipped high-endpoint selector
lies above that comparison point.
-/
theorem lt_weightedBernoulliHighEndpointOfRateOrCap_of_rate_lt_target
    {gHi gLo pLo cap target eps : ℝ}
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hpLo0 : 0 < pLo) (hpLo_le_eps : pLo ≤ eps)
    (heps_lt_cap : eps < cap) (hcap1 : cap < 1)
    (htarget_pos : 0 < target)
    (hrate_lt_target :
      weightedBernoulliClosedThresholdRate gHi gLo eps pLo < target)
    (htarget_lt_cap :
      target < weightedBernoulliClosedThresholdRate gHi gLo cap pLo) :
    eps <
      weightedBernoulliHighEndpointOfRateOrCap gHi gLo pLo cap target := by
  have hpLo_lt_cap : pLo < cap := hpLo_le_eps.trans_lt heps_lt_cap
  let hfeasible : WeightedBernoulliHighEndpointTargetFeasible
      gHi gLo pLo cap target :=
    ⟨hgHi, hgLo, hpLo0, hpLo_lt_cap, hcap1,
      htarget_pos, htarget_lt_cap⟩
  let selected : ℝ :=
    weightedBernoulliHighEndpointOfRateOrCap gHi gLo pLo cap target
  have hselected_mem : selected ∈ Set.Ioo pLo cap := by
    dsimp [selected]
    exact weightedBernoulliHighEndpointOfRateOrCap_mem_Ioo_of_feasible
      hfeasible
  have hselected_rate :
      weightedBernoulliClosedThresholdRate gHi gLo selected pLo =
        target := by
    dsimp [selected]
    exact weightedBernoulliHighEndpointOfRateOrCap_rate_of_feasible
      hfeasible
  by_contra hnot_lt
  have hselected_le_eps : selected ≤ eps := le_of_not_gt hnot_lt
  rcases lt_or_eq_of_le hselected_le_eps with hselected_lt_eps |
    hselected_eq_eps
  · have hrate_lt :
        weightedBernoulliClosedThresholdRate gHi gLo selected pLo <
          weightedBernoulliClosedThresholdRate gHi gLo eps pLo :=
      weightedBernoulliClosedThresholdRate_lt_of_shrink_hi_lt
        (gHi := gHi) (gLo := gLo) (pHi := eps) (pLo := pLo)
        (pHi' := selected) (pLo' := pLo)
        hgHi hgLo hpLo0 le_rfl hselected_mem.1.le hselected_lt_eps
        (heps_lt_cap.trans hcap1)
    have hcycle : target < target := by
      calc
        target = weightedBernoulliClosedThresholdRate gHi gLo selected pLo :=
          hselected_rate.symm
        _ < weightedBernoulliClosedThresholdRate gHi gLo eps pLo := hrate_lt
        _ < target := hrate_lt_target
    exact (lt_irrefl target) hcycle
  · have hcycle : target < target := by
      calc
        target = weightedBernoulliClosedThresholdRate gHi gLo selected pLo :=
          hselected_rate.symm
        _ = weightedBernoulliClosedThresholdRate gHi gLo eps pLo := by
          rw [hselected_eq_eps]
        _ < target := hrate_lt_target
    exact (lt_irrefl target) hcycle

/--
Collapsed-bracket continuity for the clipped high-endpoint selector: if the
low endpoint and cap converge to the same limit and the weak bracket is
eventually valid, then the clipped selector converges to that same limit.
-/
theorem weightedBernoulliHighEndpointOfRateOrCap_tendsto_of_bracket_tendsto_same
    {ι : Type*} {l : Filter ι}
    {gHi gLo limit : ℝ} {pLo cap target : ι → ℝ}
    (hpLo : Filter.Tendsto pLo l (nhds limit))
    (hcap : Filter.Tendsto cap l (nhds limit))
    (hvalid : ∀ᶠ x in l, pLo x ≤ cap x) :
    Filter.Tendsto
      (fun x : ι =>
        weightedBernoulliHighEndpointOfRateOrCap
          gHi gLo (pLo x) (cap x) (target x))
      l (nhds limit) := by
  refine
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hpLo hcap ?_ ?_
  · filter_upwards [hvalid] with x hx
    exact le_weightedBernoulliHighEndpointOfRateOrCap hx
  · filter_upwards [hvalid] with x hx
    exact weightedBernoulliHighEndpointOfRateOrCap_le_cap hx

/--
Collapsed-bracket continuity without an eventual ordering assumption: if the
low endpoint and cap both converge to the same limit, then the clipped selector
also converges to that limit.
-/
theorem weightedBernoulliHighEndpointOfRateOrCap_tendsto_of_bracket_tendsto_same'
    {ι : Type*} {l : Filter ι}
    {gHi gLo limit : ℝ} {pLo cap target : ι → ℝ}
    (hpLo : Filter.Tendsto pLo l (nhds limit))
    (hcap : Filter.Tendsto cap l (nhds limit)) :
    Filter.Tendsto
      (fun x : ι =>
        weightedBernoulliHighEndpointOfRateOrCap
          gHi gLo (pLo x) (cap x) (target x))
      l (nhds limit) := by
  have hmin :
      Filter.Tendsto (fun x : ι => min (pLo x) (cap x))
        l (nhds limit) := by
    simpa using hpLo.min hcap
  have hmax :
      Filter.Tendsto (fun x : ι => max (pLo x) (cap x))
        l (nhds limit) := by
    simpa using hpLo.max hcap
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hmin hmax ?_ ?_
  · exact Filter.Eventually.of_forall fun x =>
      min_le_weightedBernoulliHighEndpointOfRateOrCap
  · exact Filter.Eventually.of_forall fun x =>
      weightedBernoulliHighEndpointOfRateOrCap_le_max

/--
Near-zero asymptotics for the clipped high-endpoint selector.  If the low
endpoint and target rate both converge to zero while the cap converges to a
strictly positive interior point, then the selected high endpoint converges to
zero.
-/
theorem weightedBernoulliHighEndpointOfRateOrCap_tendsto_zero_of_low_target_tendsto_zero
    {ι : Type*} {l : Filter ι}
    {gHi gLo capLimit : ℝ} {pLo cap target : ι → ℝ}
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hcapLimit0 : 0 < capLimit)
    (hpLo : Filter.Tendsto pLo l (nhds (0 : ℝ)))
    (hcap : Filter.Tendsto cap l (nhds capLimit))
    (htarget : Filter.Tendsto target l (nhds (0 : ℝ)))
    (hvalid :
      ∀ᶠ x in l, 0 < pLo x ∧ pLo x ≤ cap x ∧ cap x < 1 ∧
        0 < target x) :
    Filter.Tendsto
      (fun x : ι =>
        weightedBernoulliHighEndpointOfRateOrCap
          gHi gLo (pLo x) (cap x) (target x))
      l (nhds (0 : ℝ)) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro b hb
    have hpLo_gt_b : ∀ᶠ x in l, b < pLo x :=
      hpLo.eventually (eventually_gt_nhds hb)
    filter_upwards [hpLo_gt_b, hvalid] with x hb_lt hx
    exact hb_lt.trans_le
      (le_weightedBernoulliHighEndpointOfRateOrCap hx.2.1)
  · intro b hb
    let eps : ℝ := min (min b capLimit) 1 / 2
    have heps_pos : 0 < eps := by
      dsimp [eps]
      exact half_pos (lt_min (lt_min hb hcapLimit0) zero_lt_one)
    have heps_lt_b : eps < b := by
      dsimp [eps]
      have hmin_le : min (min b capLimit) 1 ≤ b :=
        (min_le_left _ _).trans (min_le_left _ _)
      nlinarith
    have heps_lt_capLimit : eps < capLimit := by
      dsimp [eps]
      have hmin_le : min (min b capLimit) 1 ≤ capLimit :=
        (min_le_left _ _).trans (min_le_right _ _)
      nlinarith
    have heps_lt_one : eps < 1 := by
      dsimp [eps]
      have hmin_le : min (min b capLimit) 1 ≤ (1 : ℝ) := min_le_right _ _
      nlinarith
    let lowBound : ℝ := eps / 2
    have hlowBound_pos : 0 < lowBound := half_pos heps_pos
    have hlowBound_lt_eps : lowBound < eps := by
      dsimp [lowBound]
      nlinarith
    let rateBound : ℝ :=
      weightedBernoulliClosedThresholdRate gHi gLo eps lowBound
    have hrateBound_pos : 0 < rateBound := by
      dsimp [rateBound]
      exact weightedBernoulliClosedThresholdRate_pos_of_lt
        hgHi hgLo hlowBound_pos hlowBound_lt_eps heps_lt_one
    have hpLo_lt_lowBound : ∀ᶠ x in l, pLo x < lowBound :=
      hpLo.eventually (eventually_lt_nhds hlowBound_pos)
    have hcap_gt_eps : ∀ᶠ x in l, eps < cap x :=
      hcap.eventually (eventually_gt_nhds heps_lt_capLimit)
    have htarget_lt_rateBound : ∀ᶠ x in l, target x < rateBound :=
      htarget.eventually (eventually_lt_nhds hrateBound_pos)
    filter_upwards
      [hpLo_lt_lowBound, hcap_gt_eps, htarget_lt_rateBound, hvalid]
      with x hpLo_lt hcap_gt htarget_lt hx
    have hpLo_lt_eps : pLo x < eps := hpLo_lt.trans hlowBound_lt_eps
    have hrateBound_lt :
        rateBound <
          weightedBernoulliClosedThresholdRate gHi gLo eps (pLo x) := by
      dsimp [rateBound]
      exact weightedBernoulliClosedThresholdRate_lt_of_shrink_lo_lt
        (gHi := gHi) (gLo := gLo) (pHi := eps) (pLo := pLo x)
        (pHi' := eps) (pLo' := lowBound)
        hgHi hgLo hx.1 hpLo_lt hlowBound_lt_eps.le le_rfl heps_lt_one
    have htarget_lt_eps_rate :
        target x <
          weightedBernoulliClosedThresholdRate gHi gLo eps (pLo x) :=
      htarget_lt.trans hrateBound_lt
    have hselected_lt_eps :
        weightedBernoulliHighEndpointOfRateOrCap
            gHi gLo (pLo x) (cap x) (target x) < eps :=
      weightedBernoulliHighEndpointOfRateOrCap_lt_of_target_lt_rate
        hgHi hgLo hx.1 hpLo_lt_eps hcap_gt hx.2.2.1 hx.2.2.2
        htarget_lt_eps_rate
    exact hselected_lt_eps.trans heps_lt_b

/-- Continuity of the closed threshold rate in the lower Bernoulli endpoint. -/
theorem weightedBernoulliClosedThresholdRate_continuousAt_lo
    {gHi gLo pHi pLo : ℝ}
    (hpHi0 : 0 < pHi) (hpHi1 : pHi < 1)
    (hpLo0 : 0 < pLo) (hpLo1 : pLo < 1) :
    ContinuousAt
      (fun x : ℝ => weightedBernoulliClosedThresholdRate gHi gLo pHi x)
      pLo := by
  have hbase_cont :
      ContinuousAt
        (fun x : ℝ => weightedBernoulliClosedRateBase gHi gLo pHi x)
        pLo :=
    (weightedBernoulliClosedRateBase_hasDerivAt_lo
      (gHi := gHi) (gLo := gLo) (pHi := pHi) (pLo := pLo)
      hpLo0 hpLo1).continuousAt
  have hbase_pos :
      0 < weightedBernoulliClosedRateBase gHi gLo pHi pLo :=
    weightedBernoulliClosedRateBase_pos hpHi0 hpHi1 hpLo0 hpLo1
  have hlog_cont :
      ContinuousAt
        (fun x : ℝ =>
          Real.log (weightedBernoulliClosedRateBase gHi gLo pHi x))
        pLo :=
    hbase_cont.log (ne_of_gt hbase_pos)
  simpa [weightedBernoulliClosedThresholdRate] using
    hlog_cont.const_mul (-(gHi + gLo))

/--
Joint continuity of the closed threshold rate in the two Bernoulli endpoints
at an interior endpoint pair.
-/
theorem weightedBernoulliClosedThresholdRate_continuousAt_pair
    {gHi gLo pHi pLo : ℝ}
    (hpHi0 : 0 < pHi) (hpHi1 : pHi < 1)
    (hpLo0 : 0 < pLo) (hpLo1 : pLo < 1) :
    ContinuousAt
      (fun q : ℝ × ℝ =>
        weightedBernoulliClosedThresholdRate gHi gLo q.1 q.2)
      (pHi, pLo) := by
  have hbase_cont :
      ContinuousAt
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedRateBase gHi gLo q.1 q.2)
        (pHi, pLo) := by
    let aLo : ℝ := gLo / (gHi + gLo)
    let aHi : ℝ := gHi / (gHi + gLo)
    have hfailLo :
        ContinuousAt (fun q : ℝ × ℝ => 1 - q.2) (pHi, pLo) := by
      fun_prop
    have hfailHi :
        ContinuousAt (fun q : ℝ × ℝ => 1 - q.1) (pHi, pLo) := by
      fun_prop
    have hsuccLo :
        ContinuousAt (fun q : ℝ × ℝ => q.2) (pHi, pLo) := by
      fun_prop
    have hsuccHi :
        ContinuousAt (fun q : ℝ × ℝ => q.1) (pHi, pLo) := by
      fun_prop
    have hfailLo_pow :
        ContinuousAt (fun q : ℝ × ℝ => (1 - q.2) ^ aLo) (pHi, pLo) :=
      hfailLo.rpow_const (Or.inl (ne_of_gt (sub_pos.mpr hpLo1)))
    have hfailHi_pow :
        ContinuousAt (fun q : ℝ × ℝ => (1 - q.1) ^ aHi) (pHi, pLo) :=
      hfailHi.rpow_const (Or.inl (ne_of_gt (sub_pos.mpr hpHi1)))
    have hsuccLo_pow :
        ContinuousAt (fun q : ℝ × ℝ => q.2 ^ aLo) (pHi, pLo) :=
      hsuccLo.rpow_const (Or.inl (ne_of_gt hpLo0))
    have hsuccHi_pow :
        ContinuousAt (fun q : ℝ × ℝ => q.1 ^ aHi) (pHi, pLo) :=
      hsuccHi.rpow_const (Or.inl (ne_of_gt hpHi0))
    simpa [weightedBernoulliClosedRateBase,
      weightedBernoulliFailureBase, weightedBernoulliSuccessBase, aLo, aHi]
      using (hfailLo_pow.mul hfailHi_pow).add
        (hsuccLo_pow.mul hsuccHi_pow)
  have hbase_pos :
      0 < weightedBernoulliClosedRateBase gHi gLo pHi pLo :=
    weightedBernoulliClosedRateBase_pos hpHi0 hpHi1 hpLo0 hpLo1
  have hlog_cont :
      ContinuousAt
        (fun q : ℝ × ℝ =>
          Real.log (weightedBernoulliClosedRateBase gHi gLo q.1 q.2))
        (pHi, pLo) :=
    hbase_cont.log (ne_of_gt hbase_pos)
  simpa [weightedBernoulliClosedThresholdRate] using
    hlog_cont.const_mul (-(gHi + gLo))

/--
Filter-polymorphic joint continuity of the closed threshold rate in both
sample-rate weights and both Bernoulli endpoints.
-/
theorem weightedBernoulliClosedThresholdRate_tendsto
    {ι : Type*} {l : Filter ι}
    {gHi gLo pHi pLo : ι → ℝ} {GHi GLo PHi PLo : ℝ}
    (hGHi0 : 0 < GHi) (hGLo0 : 0 < GLo)
    (hPHi0 : 0 < PHi) (hPHi1 : PHi < 1)
    (hPLo0 : 0 < PLo) (hPLo1 : PLo < 1)
    (hgHi : Filter.Tendsto gHi l (nhds GHi))
    (hgLo : Filter.Tendsto gLo l (nhds GLo))
    (hpHi : Filter.Tendsto pHi l (nhds PHi))
    (hpLo : Filter.Tendsto pLo l (nhds PLo)) :
    Filter.Tendsto
      (fun x : ι =>
        weightedBernoulliClosedThresholdRate
          (gHi x) (gLo x) (pHi x) (pLo x))
      l
      (nhds (weightedBernoulliClosedThresholdRate GHi GLo PHi PLo)) := by
  let denom : ι → ℝ := fun x => gHi x + gLo x
  let Denom : ℝ := GHi + GLo
  have hdenom :
      Filter.Tendsto denom l (nhds Denom) := by
    simpa [denom, Denom] using hgHi.add hgLo
  have hDenom_pos : 0 < Denom := by
    dsimp [Denom]
    linarith
  have hDenom_ne : Denom ≠ 0 := ne_of_gt hDenom_pos
  let aLo : ι → ℝ := fun x => gLo x / denom x
  let ALo : ℝ := GLo / Denom
  let aHi : ι → ℝ := fun x => gHi x / denom x
  let AHi : ℝ := GHi / Denom
  have haLo : Filter.Tendsto aLo l (nhds ALo) := by
    simpa [aLo, ALo, denom, Denom] using hgLo.div hdenom hDenom_ne
  have haHi : Filter.Tendsto aHi l (nhds AHi) := by
    simpa [aHi, AHi, denom, Denom] using hgHi.div hdenom hDenom_ne
  have hfailLo :
      Filter.Tendsto (fun x : ι => 1 - pLo x) l (nhds (1 - PLo)) := by
    simpa using tendsto_const_nhds.sub hpLo
  have hfailHi :
      Filter.Tendsto (fun x : ι => 1 - pHi x) l (nhds (1 - PHi)) := by
    simpa using tendsto_const_nhds.sub hpHi
  have hfailLo_pow :
      Filter.Tendsto
        (fun x : ι => (1 - pLo x) ^ aLo x)
        l (nhds ((1 - PLo) ^ ALo)) :=
    hfailLo.rpow haLo (Or.inl (ne_of_gt (sub_pos.mpr hPLo1)))
  have hfailHi_pow :
      Filter.Tendsto
        (fun x : ι => (1 - pHi x) ^ aHi x)
        l (nhds ((1 - PHi) ^ AHi)) :=
    hfailHi.rpow haHi (Or.inl (ne_of_gt (sub_pos.mpr hPHi1)))
  have hsuccLo_pow :
      Filter.Tendsto
        (fun x : ι => pLo x ^ aLo x)
        l (nhds (PLo ^ ALo)) :=
    hpLo.rpow haLo (Or.inl (ne_of_gt hPLo0))
  have hsuccHi_pow :
      Filter.Tendsto
        (fun x : ι => pHi x ^ aHi x)
        l (nhds (PHi ^ AHi)) :=
    hpHi.rpow haHi (Or.inl (ne_of_gt hPHi0))
  have hbase :
      Filter.Tendsto
        (fun x : ι =>
          weightedBernoulliClosedRateBase
            (gHi x) (gLo x) (pHi x) (pLo x))
        l
        (nhds (weightedBernoulliClosedRateBase GHi GLo PHi PLo)) := by
    simpa [weightedBernoulliClosedRateBase,
      weightedBernoulliFailureBase, weightedBernoulliSuccessBase,
      aLo, aHi, ALo, AHi, denom, Denom]
      using (hfailLo_pow.mul hfailHi_pow).add
        (hsuccLo_pow.mul hsuccHi_pow)
  have hbase_pos :
      0 < weightedBernoulliClosedRateBase GHi GLo PHi PLo :=
    weightedBernoulliClosedRateBase_pos hPHi0 hPHi1 hPLo0 hPLo1
  have hlog :
      Filter.Tendsto
        (fun x : ι =>
          Real.log
            (weightedBernoulliClosedRateBase
              (gHi x) (gLo x) (pHi x) (pLo x)))
        l
        (nhds (Real.log
          (weightedBernoulliClosedRateBase GHi GLo PHi PLo))) :=
    hbase.log (ne_of_gt hbase_pos)
  have hscale :
      Filter.Tendsto
        (fun x : ι => -(gHi x + gLo x))
        l
        (nhds (-(GHi + GLo))) := by
    simpa using (hgHi.add hgLo).neg
  simpa [weightedBernoulliClosedThresholdRate] using hscale.mul hlog

/--
Joint continuity of the closed threshold rate when sample weights and
Bernoulli endpoints are continuous at the parameter point.
-/
theorem weightedBernoulliClosedThresholdRate_continuousAt
    {α : Type*} [TopologicalSpace α] {x0 : α}
    {gHi gLo pHi pLo : α → ℝ}
    (hgHi0 : 0 < gHi x0) (hgLo0 : 0 < gLo x0)
    (hpHi0 : 0 < pHi x0) (hpHi1 : pHi x0 < 1)
    (hpLo0 : 0 < pLo x0) (hpLo1 : pLo x0 < 1)
    (hgHi : ContinuousAt gHi x0)
    (hgLo : ContinuousAt gLo x0)
    (hpHi : ContinuousAt pHi x0)
    (hpLo : ContinuousAt pLo x0) :
    ContinuousAt
      (fun x : α =>
        weightedBernoulliClosedThresholdRate
          (gHi x) (gLo x) (pHi x) (pLo x))
      x0 :=
  weightedBernoulliClosedThresholdRate_tendsto
    hgHi0 hgLo0 hpHi0 hpHi1 hpLo0 hpLo1
    hgHi hgLo hpHi hpLo

/--
If two Bernoulli endpoints coalesce at an interior probability, the fixed-weight
closed threshold exponent tends to zero.  The filter-polymorphic form is useful
for sequences, product neighborhoods, and model-specific parameter maps.
-/
theorem weightedBernoulliClosedThresholdRate_tendsto_zero_of_pair_tendsto_same
    {ι : Type*} {l : Filter ι}
    {gHi gLo p : ℝ} {pHi pLo : ι → ℝ}
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hp0 : 0 < p) (hp1 : p < 1)
    (hHi : Filter.Tendsto pHi l (nhds p))
    (hLo : Filter.Tendsto pLo l (nhds p)) :
    Filter.Tendsto
      (fun x : ι =>
        weightedBernoulliClosedThresholdRate gHi gLo (pHi x) (pLo x))
      l (nhds 0) := by
  have hpair :
      Filter.Tendsto (fun x : ι => (pHi x, pLo x))
        l (nhds (p, p)) :=
    by
      simpa [nhds_prod_eq] using Filter.Tendsto.prodMk hHi hLo
  have hcont :
      ContinuousAt
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate gHi gLo q.1 q.2)
        (p, p) :=
    weightedBernoulliClosedThresholdRate_continuousAt_pair
      (gHi := gHi) (gLo := gLo) (pHi := p) (pLo := p)
      hp0 hp1 hp0 hp1
  have hself :
      weightedBernoulliClosedThresholdRate gHi gLo p p = 0 :=
    weightedBernoulliClosedThresholdRate_self hgHi hgLo hp0 hp1
  simpa [hself] using hcont.tendsto.comp hpair

/--
Moving-parameter continuity of the clipped high-endpoint selector on the
strict clipped side, where the target rate is locally above the cap rate.
-/
theorem weightedBernoulliHighEndpointOfRateOrCap_continuousAt_params_of_cap_rate_lt_target
    {gHi gLo pLo cap target : ℝ}
    (hpLo0 : 0 < pLo) (hpLo_lt_cap : pLo < cap)
    (hcap1 : cap < 1)
    (hcap_rate_lt_target :
      weightedBernoulliClosedThresholdRate gHi gLo cap pLo < target) :
    ContinuousAt
      (fun q : ℝ × ℝ × ℝ =>
        weightedBernoulliHighEndpointOfRateOrCap
          gHi gLo q.1 q.2.1 q.2.2)
      (pLo, cap, target) := by
  have hcap0 : 0 < cap := hpLo0.trans hpLo_lt_cap
  have hpLo1 : pLo < 1 := hpLo_lt_cap.trans hcap1
  have hpair_cont :
      ContinuousAt
        (fun q : ℝ × ℝ × ℝ => (q.2.1, q.1))
        (pLo, cap, target) := by
    fun_prop
  have hrate_pair :
      ContinuousAt
        (fun q : ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate gHi gLo q.1 q.2)
        (cap, pLo) :=
    weightedBernoulliClosedThresholdRate_continuousAt_pair
      (gHi := gHi) (gLo := gLo) (pHi := cap) (pLo := pLo)
      hcap0 hcap1 hpLo0 hpLo1
  have hrate_cont :
      ContinuousAt
        (fun q : ℝ × ℝ × ℝ =>
          weightedBernoulliClosedThresholdRate gHi gLo q.2.1 q.1)
        (pLo, cap, target) := by
    fun_prop
  have htarget_cont :
      ContinuousAt (fun q : ℝ × ℝ × ℝ => q.2.2)
        (pLo, cap, target) := by
    fun_prop
  have hmargin_cont :
      ContinuousAt
        (fun q : ℝ × ℝ × ℝ =>
          q.2.2 -
            weightedBernoulliClosedThresholdRate gHi gLo q.2.1 q.1)
        (pLo, cap, target) :=
    htarget_cont.sub hrate_cont
  have hmargin_pos :
      ∀ᶠ q in nhds (pLo, cap, target),
        0 <
          q.2.2 -
            weightedBernoulliClosedThresholdRate gHi gLo q.2.1 q.1 := by
    have hbase :
        0 <
          target -
            weightedBernoulliClosedThresholdRate gHi gLo cap pLo :=
      sub_pos.mpr hcap_rate_lt_target
    exact hmargin_cont.eventually (Ioi_mem_nhds (by simpa using hbase))
  have hcap_cont :
      ContinuousAt (fun q : ℝ × ℝ × ℝ => q.2.1)
        (pLo, cap, target) := by
    fun_prop
  have hbase_not_feasible :
      ¬ WeightedBernoulliHighEndpointTargetFeasible
        gHi gLo pLo cap target := by
    intro hfeasible
    exact (not_lt_of_ge hcap_rate_lt_target.le) hfeasible.htarget_lt_cap
  have hbase_eq :
      weightedBernoulliHighEndpointOfRateOrCap gHi gLo pLo cap target =
        cap :=
    weightedBernoulliHighEndpointOfRateOrCap_eq_cap_of_not_feasible
      hbase_not_feasible
  rw [ContinuousAt, hbase_eq]
  have hcap_tendsto :
      Filter.Tendsto (fun q : ℝ × ℝ × ℝ => q.2.1)
        (nhds (pLo, cap, target)) (nhds cap) := by
    simpa [ContinuousAt] using hcap_cont
  refine Filter.Tendsto.congr' ?_ hcap_tendsto
  filter_upwards [hmargin_pos] with q hq
  have hnot_feasible :
      ¬ WeightedBernoulliHighEndpointTargetFeasible
        gHi gLo q.1 q.2.1 q.2.2 := by
    intro hfeasible
    exact (not_lt_of_ge (sub_nonneg.mp hq.le)) hfeasible.htarget_lt_cap
  exact
    (weightedBernoulliHighEndpointOfRateOrCap_eq_cap_of_not_feasible
      hnot_feasible).symm

/--
Moving-parameter continuity of the clipped high-endpoint selector on the
strict feasible side, where the target rate is locally below the cap rate.
-/
theorem weightedBernoulliHighEndpointOfRateOrCap_continuousAt_params_of_target_lt_cap_rate
    {gHi gLo pLo cap target : ℝ}
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hpLo0 : 0 < pLo) (hpLo_lt_cap : pLo < cap)
    (hcap1 : cap < 1) (htarget_pos : 0 < target)
    (htarget_lt_cap :
      target < weightedBernoulliClosedThresholdRate gHi gLo cap pLo) :
    ContinuousAt
      (fun q : ℝ × ℝ × ℝ =>
        weightedBernoulliHighEndpointOfRateOrCap
          gHi gLo q.1 q.2.1 q.2.2)
      (pLo, cap, target) := by
  let selected : ℝ :=
    weightedBernoulliHighEndpointOfRateOrCap gHi gLo pLo cap target
  let hfeasible : WeightedBernoulliHighEndpointTargetFeasible
      gHi gLo pLo cap target :=
    ⟨hgHi, hgLo, hpLo0, hpLo_lt_cap, hcap1,
      htarget_pos, htarget_lt_cap⟩
  have hselected_mem : selected ∈ Set.Ioo pLo cap := by
    dsimp [selected]
    exact weightedBernoulliHighEndpointOfRateOrCap_mem_Ioo_of_feasible
      hfeasible
  have hselected_rate :
      weightedBernoulliClosedThresholdRate gHi gLo selected pLo =
        target := by
    dsimp [selected]
    exact weightedBernoulliHighEndpointOfRateOrCap_rate_of_feasible
      hfeasible
  rw [ContinuousAt]
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro b hb
    let lower : ℝ := (max b pLo + selected) / 2
    have hmax_lt_selected : max b pLo < selected :=
      max_lt hb hselected_mem.1
    have hb_lt_lower : b < lower := by
      have hb_le_max : b ≤ max b pLo := le_max_left _ _
      dsimp [lower]
      nlinarith
    have hpLo_lt_lower : pLo < lower := by
      have hpLo_le_max : pLo ≤ max b pLo := le_max_right _ _
      dsimp [lower]
      nlinarith
    have hlower_lt_selected : lower < selected := by
      dsimp [lower]
      nlinarith
    have hlower_lt_cap : lower < cap := hlower_lt_selected.trans hselected_mem.2
    have hlower0 : 0 < lower := hpLo0.trans hpLo_lt_lower
    have hlower1 : lower < 1 := hlower_lt_cap.trans hcap1
    have hrate_lower_lt_target :
        weightedBernoulliClosedThresholdRate gHi gLo lower pLo < target := by
      rw [← hselected_rate]
      exact
        weightedBernoulliClosedThresholdRate_lt_of_shrink_hi_lt
          (gHi := gHi) (gLo := gLo) (pHi := selected) (pLo := pLo)
          (pHi' := lower) (pLo' := pLo)
          hgHi hgLo hpLo0 le_rfl hpLo_lt_lower.le
          hlower_lt_selected (hselected_mem.2.trans hcap1)
    have hlow_pos_eventually :
        ∀ᶠ q in nhds (pLo, cap, target), 0 < q.1 :=
      (continuousAt_fst.eventually (Ioi_mem_nhds hpLo0))
    have hlow_le_lower_eventually :
        ∀ᶠ q in nhds (pLo, cap, target), q.1 ≤ lower :=
      (continuousAt_fst.eventually
        (Iio_mem_nhds hpLo_lt_lower)).mono fun _ hlt => hlt.le
    have hlower_lt_cap_eventually :
        ∀ᶠ q in nhds (pLo, cap, target), lower < q.2.1 :=
      ((continuousAt_snd.fst).eventually
        (Ioi_mem_nhds hlower_lt_cap))
    have hcap_lt_one_eventually :
        ∀ᶠ q in nhds (pLo, cap, target), q.2.1 < 1 :=
      ((continuousAt_snd.fst).eventually (Iio_mem_nhds hcap1))
    have htarget_pos_eventually :
        ∀ᶠ q in nhds (pLo, cap, target), 0 < q.2.2 :=
      ((continuousAt_snd.snd).eventually (Ioi_mem_nhds htarget_pos))
    have hrate_lower_cont :
        ContinuousAt
          (fun q : ℝ × ℝ × ℝ =>
            weightedBernoulliClosedThresholdRate gHi gLo lower q.1)
          (pLo, cap, target) := by
      have hbase :
          ContinuousAt
            (fun x : ℝ =>
              weightedBernoulliClosedThresholdRate gHi gLo lower x)
            pLo :=
        weightedBernoulliClosedThresholdRate_continuousAt_lo
          (gHi := gHi) (gLo := gLo) (pHi := lower) (pLo := pLo)
          hlower0 hlower1 hpLo0 (hpLo_lt_lower.trans hlower1)
      simpa [Function.comp_def] using hbase.comp continuousAt_fst
    have htarget_cont :
        ContinuousAt (fun q : ℝ × ℝ × ℝ => q.2.2)
          (pLo, cap, target) := by
      fun_prop
    have htarget_minus_lower_pos :
        ∀ᶠ q in nhds (pLo, cap, target),
          0 <
            q.2.2 -
              weightedBernoulliClosedThresholdRate gHi gLo lower q.1 := by
      have hmargin :
          0 <
            target -
              weightedBernoulliClosedThresholdRate gHi gLo lower pLo :=
        sub_pos.mpr hrate_lower_lt_target
      exact (htarget_cont.sub hrate_lower_cont).eventually
        (Ioi_mem_nhds (by simpa using hmargin))
    have hcap_rate_cont :
        ContinuousAt
          (fun q : ℝ × ℝ × ℝ =>
            weightedBernoulliClosedThresholdRate gHi gLo q.2.1 q.1)
          (pLo, cap, target) := by
      let pair : (ℝ × ℝ × ℝ) → ℝ × ℝ := fun q => (q.2.1, q.1)
      have hpair : ContinuousAt pair (pLo, cap, target) := by
        dsimp [pair]
        fun_prop
      have hbase :
          ContinuousAt
            (fun q : ℝ × ℝ =>
              weightedBernoulliClosedThresholdRate gHi gLo q.1 q.2)
            (cap, pLo) :=
        weightedBernoulliClosedThresholdRate_continuousAt_pair
          (gHi := gHi) (gLo := gLo) (pHi := cap) (pLo := pLo)
          (hpLo0.trans hpLo_lt_cap) hcap1 hpLo0
          (hpLo_lt_cap.trans hcap1)
      change ContinuousAt
        ((fun q : ℝ × ℝ =>
            weightedBernoulliClosedThresholdRate gHi gLo q.1 q.2) ∘ pair)
        (pLo, cap, target)
      exact hbase.comp_of_eq hpair rfl
    have hcap_rate_minus_target_pos :
        ∀ᶠ q in nhds (pLo, cap, target),
          0 <
            weightedBernoulliClosedThresholdRate gHi gLo q.2.1 q.1 -
              q.2.2 := by
      have hmargin :
          0 <
            weightedBernoulliClosedThresholdRate gHi gLo cap pLo -
              target :=
        sub_pos.mpr htarget_lt_cap
      exact (hcap_rate_cont.sub htarget_cont).eventually
        (Ioi_mem_nhds (by simpa using hmargin))
    filter_upwards
      [hlow_pos_eventually, hlow_le_lower_eventually,
        hlower_lt_cap_eventually, hcap_lt_one_eventually,
        htarget_pos_eventually, htarget_minus_lower_pos,
        hcap_rate_minus_target_pos]
      with q hqlo0 hqlo_le_lower hlower_lt_qcap hqcap1 hqtarget0
        htarget_minus hcap_minus
    have hrate_lower_lt_qtarget :
        weightedBernoulliClosedThresholdRate gHi gLo lower q.1 < q.2.2 :=
      sub_pos.mp htarget_minus
    have hqtarget_lt_cap :
        q.2.2 < weightedBernoulliClosedThresholdRate gHi gLo q.2.1 q.1 :=
      sub_pos.mp hcap_minus
    exact hb_lt_lower.trans
      (lt_weightedBernoulliHighEndpointOfRateOrCap_of_rate_lt_target
        hgHi hgLo hqlo0 hqlo_le_lower hlower_lt_qcap hqcap1 hqtarget0
        hrate_lower_lt_qtarget hqtarget_lt_cap)
  · intro b hb
    let upper : ℝ := (selected + min b cap) / 2
    have hselected_lt_min : selected < min b cap :=
      lt_min hb hselected_mem.2
    have hselected_lt_upper : selected < upper := by
      dsimp [upper]
      nlinarith
    have hupper_lt_b : upper < b := by
      have hmin_le_b : min b cap ≤ b := min_le_left _ _
      dsimp [upper]
      nlinarith
    have hupper_lt_cap : upper < cap := by
      have hmin_le_cap : min b cap ≤ cap := min_le_right _ _
      dsimp [upper]
      nlinarith
    have hpLo_lt_upper : pLo < upper := hselected_mem.1.trans hselected_lt_upper
    have hupper0 : 0 < upper := hpLo0.trans hpLo_lt_upper
    have hupper1 : upper < 1 := hupper_lt_cap.trans hcap1
    have htarget_lt_rate_upper :
        target < weightedBernoulliClosedThresholdRate gHi gLo upper pLo := by
      rw [← hselected_rate]
      exact
        weightedBernoulliClosedThresholdRate_lt_of_shrink_hi_lt
          (gHi := gHi) (gLo := gLo) (pHi := upper) (pLo := pLo)
          (pHi' := selected) (pLo' := pLo)
          hgHi hgLo hpLo0 le_rfl hselected_mem.1.le
          hselected_lt_upper hupper1
    have hlow_pos_eventually :
        ∀ᶠ q in nhds (pLo, cap, target), 0 < q.1 :=
      (continuousAt_fst.eventually (Ioi_mem_nhds hpLo0))
    have hlow_lt_upper_eventually :
        ∀ᶠ q in nhds (pLo, cap, target), q.1 < upper :=
      continuousAt_fst.eventually (Iio_mem_nhds hpLo_lt_upper)
    have hupper_lt_cap_eventually :
        ∀ᶠ q in nhds (pLo, cap, target), upper < q.2.1 :=
      (continuousAt_snd.fst).eventually (Ioi_mem_nhds hupper_lt_cap)
    have hcap_lt_one_eventually :
        ∀ᶠ q in nhds (pLo, cap, target), q.2.1 < 1 :=
      (continuousAt_snd.fst).eventually (Iio_mem_nhds hcap1)
    have htarget_pos_eventually :
        ∀ᶠ q in nhds (pLo, cap, target), 0 < q.2.2 :=
      (continuousAt_snd.snd).eventually (Ioi_mem_nhds htarget_pos)
    have hrate_upper_cont :
        ContinuousAt
          (fun q : ℝ × ℝ × ℝ =>
            weightedBernoulliClosedThresholdRate gHi gLo upper q.1)
          (pLo, cap, target) := by
      have hbase :
          ContinuousAt
            (fun x : ℝ =>
              weightedBernoulliClosedThresholdRate gHi gLo upper x)
            pLo :=
        weightedBernoulliClosedThresholdRate_continuousAt_lo
          (gHi := gHi) (gLo := gLo) (pHi := upper) (pLo := pLo)
          hupper0 hupper1 hpLo0 (hpLo_lt_upper.trans hupper1)
      simpa [Function.comp_def] using hbase.comp continuousAt_fst
    have htarget_cont :
        ContinuousAt (fun q : ℝ × ℝ × ℝ => q.2.2)
          (pLo, cap, target) := by
      fun_prop
    have hrate_upper_minus_target_pos :
        ∀ᶠ q in nhds (pLo, cap, target),
          0 <
            weightedBernoulliClosedThresholdRate gHi gLo upper q.1 -
              q.2.2 := by
      have hmargin :
          0 <
            weightedBernoulliClosedThresholdRate gHi gLo upper pLo -
              target :=
        sub_pos.mpr htarget_lt_rate_upper
      exact (hrate_upper_cont.sub htarget_cont).eventually
        (Ioi_mem_nhds (by simpa using hmargin))
    filter_upwards
      [hlow_pos_eventually, hlow_lt_upper_eventually,
        hupper_lt_cap_eventually, hcap_lt_one_eventually,
        htarget_pos_eventually, hrate_upper_minus_target_pos]
      with q hqlo0 hqlo_lt_upper hupper_lt_qcap hqcap1 hqtarget0
        hupper_minus
    have hqtarget_lt_rate_upper :
        q.2.2 < weightedBernoulliClosedThresholdRate gHi gLo upper q.1 :=
      sub_pos.mp hupper_minus
    exact
      (weightedBernoulliHighEndpointOfRateOrCap_lt_of_target_lt_rate
        hgHi hgLo hqlo0 hqlo_lt_upper hupper_lt_qcap hqcap1 hqtarget0
        hqtarget_lt_rate_upper).trans hupper_lt_b

/--
Moving-parameter continuity of the clipped high-endpoint selector on the
switching boundary, where the target rate equals the cap rate.
-/
theorem weightedBernoulliHighEndpointOfRateOrCap_continuousAt_params_of_target_eq_cap_rate
    {gHi gLo pLo cap target : ℝ}
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hpLo0 : 0 < pLo) (hpLo_lt_cap : pLo < cap)
    (hcap1 : cap < 1) (htarget_pos : 0 < target)
    (htarget_eq_cap :
      target = weightedBernoulliClosedThresholdRate gHi gLo cap pLo) :
    ContinuousAt
      (fun q : ℝ × ℝ × ℝ =>
        weightedBernoulliHighEndpointOfRateOrCap
          gHi gLo q.1 q.2.1 q.2.2)
      (pLo, cap, target) := by
  have hbase_not_feasible :
      ¬ WeightedBernoulliHighEndpointTargetFeasible
        gHi gLo pLo cap target := by
    intro hfeasible
    rw [htarget_eq_cap] at hfeasible
    exact (lt_irrefl _) hfeasible.htarget_lt_cap
  have hbase_eq :
      weightedBernoulliHighEndpointOfRateOrCap gHi gLo pLo cap target =
        cap :=
    weightedBernoulliHighEndpointOfRateOrCap_eq_cap_of_not_feasible
      hbase_not_feasible
  rw [ContinuousAt, hbase_eq]
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro b hb
    let lower : ℝ := (max b pLo + cap) / 2
    have hmax_lt_cap : max b pLo < cap := max_lt hb hpLo_lt_cap
    have hb_lt_lower : b < lower := by
      have hb_le_max : b ≤ max b pLo := le_max_left _ _
      dsimp [lower]
      nlinarith
    have hpLo_lt_lower : pLo < lower := by
      have hpLo_le_max : pLo ≤ max b pLo := le_max_right _ _
      dsimp [lower]
      nlinarith
    have hlower_lt_cap : lower < cap := by
      dsimp [lower]
      nlinarith
    have hlower0 : 0 < lower := hpLo0.trans hpLo_lt_lower
    have hlower1 : lower < 1 := hlower_lt_cap.trans hcap1
    have hrate_lower_lt_target :
        weightedBernoulliClosedThresholdRate gHi gLo lower pLo < target := by
      rw [htarget_eq_cap]
      exact
        weightedBernoulliClosedThresholdRate_lt_of_shrink_hi_lt
          (gHi := gHi) (gLo := gLo) (pHi := cap) (pLo := pLo)
          (pHi' := lower) (pLo' := pLo)
          hgHi hgLo hpLo0 le_rfl hpLo_lt_lower.le
          hlower_lt_cap hcap1
    have hlow_pos_eventually :
        ∀ᶠ q in nhds (pLo, cap, target), 0 < q.1 :=
      continuousAt_fst.eventually (Ioi_mem_nhds hpLo0)
    have hlow_le_lower_eventually :
        ∀ᶠ q in nhds (pLo, cap, target), q.1 ≤ lower :=
      (continuousAt_fst.eventually
        (Iio_mem_nhds hpLo_lt_lower)).mono fun _ hlt => hlt.le
    have hlower_lt_cap_eventually :
        ∀ᶠ q in nhds (pLo, cap, target), lower < q.2.1 :=
      (continuousAt_snd.fst).eventually (Ioi_mem_nhds hlower_lt_cap)
    have hcap_lt_one_eventually :
        ∀ᶠ q in nhds (pLo, cap, target), q.2.1 < 1 :=
      (continuousAt_snd.fst).eventually (Iio_mem_nhds hcap1)
    have htarget_pos_eventually :
        ∀ᶠ q in nhds (pLo, cap, target), 0 < q.2.2 :=
      (continuousAt_snd.snd).eventually (Ioi_mem_nhds htarget_pos)
    have hcap_gt_b_eventually :
        ∀ᶠ q in nhds (pLo, cap, target), b < q.2.1 :=
      (continuousAt_snd.fst).eventually (Ioi_mem_nhds hb)
    have hrate_lower_cont :
        ContinuousAt
          (fun q : ℝ × ℝ × ℝ =>
            weightedBernoulliClosedThresholdRate gHi gLo lower q.1)
          (pLo, cap, target) := by
      have hbase :
          ContinuousAt
            (fun x : ℝ =>
              weightedBernoulliClosedThresholdRate gHi gLo lower x)
            pLo :=
        weightedBernoulliClosedThresholdRate_continuousAt_lo
          (gHi := gHi) (gLo := gLo) (pHi := lower) (pLo := pLo)
          hlower0 hlower1 hpLo0 (hpLo_lt_lower.trans hlower1)
      simpa [Function.comp_def] using hbase.comp continuousAt_fst
    have htarget_cont :
        ContinuousAt (fun q : ℝ × ℝ × ℝ => q.2.2)
          (pLo, cap, target) := by
      fun_prop
    have htarget_minus_lower_pos :
        ∀ᶠ q in nhds (pLo, cap, target),
          0 <
            q.2.2 -
              weightedBernoulliClosedThresholdRate gHi gLo lower q.1 := by
      have hmargin :
          0 <
            target -
              weightedBernoulliClosedThresholdRate gHi gLo lower pLo :=
        sub_pos.mpr hrate_lower_lt_target
      exact (htarget_cont.sub hrate_lower_cont).eventually
        (Ioi_mem_nhds (by simpa using hmargin))
    filter_upwards
      [hlow_pos_eventually, hlow_le_lower_eventually,
        hlower_lt_cap_eventually, hcap_lt_one_eventually,
        htarget_pos_eventually, hcap_gt_b_eventually,
        htarget_minus_lower_pos]
      with q hqlo0 hqlo_le_lower hlower_lt_qcap hqcap1 hqtarget0
        hb_lt_qcap htarget_minus
    by_cases hfeasible :
        WeightedBernoulliHighEndpointTargetFeasible
          gHi gLo q.1 q.2.1 q.2.2
    · have hrate_lower_lt_qtarget :
          weightedBernoulliClosedThresholdRate gHi gLo lower q.1 < q.2.2 :=
        sub_pos.mp htarget_minus
      exact hb_lt_lower.trans
        (lt_weightedBernoulliHighEndpointOfRateOrCap_of_rate_lt_target
          hgHi hgLo hqlo0 hqlo_le_lower hlower_lt_qcap hqcap1 hqtarget0
          hrate_lower_lt_qtarget hfeasible.htarget_lt_cap)
    · rw [weightedBernoulliHighEndpointOfRateOrCap_eq_cap_of_not_feasible
        hfeasible]
      exact hb_lt_qcap
  · intro b hb
    have hlow_lt_b_eventually :
        ∀ᶠ q in nhds (pLo, cap, target), q.1 < b :=
      continuousAt_fst.eventually
        (Iio_mem_nhds (hpLo_lt_cap.trans hb))
    have hcap_lt_b_eventually :
        ∀ᶠ q in nhds (pLo, cap, target), q.2.1 < b :=
      (continuousAt_snd.fst).eventually (Iio_mem_nhds hb)
    filter_upwards [hlow_lt_b_eventually, hcap_lt_b_eventually]
      with q hqlo_lt hqcap_lt
    exact lt_of_le_of_lt weightedBernoulliHighEndpointOfRateOrCap_le_max
      (max_lt hqlo_lt hqcap_lt)

/--
Moving-parameter continuity of the clipped high-endpoint selector throughout the
ordered interior region.  This packages the strict feasible side, strict clipped
side, switching boundary, and collapsed-bracket cases behind one reusable
interface.
-/
theorem weightedBernoulliHighEndpointOfRateOrCap_continuousAt_params
    {gHi gLo pLo cap target : ℝ}
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hpLo0 : 0 < pLo) (hpLo_le_cap : pLo ≤ cap)
    (hcap1 : cap < 1) (htarget_pos : 0 < target) :
    ContinuousAt
      (fun q : ℝ × ℝ × ℝ =>
        weightedBernoulliHighEndpointOfRateOrCap
          gHi gLo q.1 q.2.1 q.2.2)
      (pLo, cap, target) := by
  rcases lt_or_eq_of_le hpLo_le_cap with hpLo_lt_cap | hpLo_eq_cap
  · rcases lt_trichotomy target
      (weightedBernoulliClosedThresholdRate gHi gLo cap pLo) with
      htarget_lt_cap_rate | htarget_eq_cap_rate | hcap_rate_lt_target
    · exact
        weightedBernoulliHighEndpointOfRateOrCap_continuousAt_params_of_target_lt_cap_rate
          (gHi := gHi) (gLo := gLo) (pLo := pLo) (cap := cap)
          (target := target) hgHi hgLo hpLo0 hpLo_lt_cap hcap1
          htarget_pos htarget_lt_cap_rate
    · exact
        weightedBernoulliHighEndpointOfRateOrCap_continuousAt_params_of_target_eq_cap_rate
          (gHi := gHi) (gLo := gLo) (pLo := pLo) (cap := cap)
          (target := target) hgHi hgLo hpLo0 hpLo_lt_cap hcap1
          htarget_pos htarget_eq_cap_rate
    · exact
        weightedBernoulliHighEndpointOfRateOrCap_continuousAt_params_of_cap_rate_lt_target
          (gHi := gHi) (gLo := gLo) (pLo := pLo) (cap := cap)
          (target := target) hpLo0 hpLo_lt_cap hcap1 hcap_rate_lt_target
  · have hnot_lt : ¬ pLo < cap := by
      rw [hpLo_eq_cap]
      exact not_lt.mpr le_rfl
    have hbase_eq :
        weightedBernoulliHighEndpointOfRateOrCap gHi gLo pLo cap target =
          cap :=
      weightedBernoulliHighEndpointOfRateOrCap_eq_cap_of_not_lt_cap hnot_lt
    have hpLo_tendsto :
        Filter.Tendsto (fun q : ℝ × ℝ × ℝ => q.1)
          (nhds (pLo, cap, target)) (nhds cap) := by
      simpa [ContinuousAt, hpLo_eq_cap] using
        (continuousAt_fst :
          ContinuousAt (fun q : ℝ × ℝ × ℝ => q.1)
            (pLo, cap, target))
    have hcap_tendsto :
        Filter.Tendsto (fun q : ℝ × ℝ × ℝ => q.2.1)
          (nhds (pLo, cap, target)) (nhds cap) := by
      simpa [ContinuousAt] using
        (continuousAt_snd.fst :
          ContinuousAt (fun q : ℝ × ℝ × ℝ => q.2.1)
            (pLo, cap, target))
    simpa [ContinuousAt, hbase_eq] using
      (weightedBernoulliHighEndpointOfRateOrCap_tendsto_of_bracket_tendsto_same'
        (gHi := gHi) (gLo := gLo) (limit := cap)
        (pLo := fun q : ℝ × ℝ × ℝ => q.1)
        (cap := fun q : ℝ × ℝ × ℝ => q.2.1)
        (target := fun q : ℝ × ℝ × ℝ => q.2.2)
        hpLo_tendsto hcap_tendsto)

/--
Joint continuity of the closed threshold rate on the ordered interior endpoint
region `0 < pLo ≤ pHi < 1`.
-/
theorem weightedBernoulliClosedThresholdRate_continuousOn_ordered
    (gHi gLo : ℝ) :
    ContinuousOn
      (fun q : ℝ × ℝ =>
        weightedBernoulliClosedThresholdRate gHi gLo q.1 q.2)
      {q : ℝ × ℝ | 0 < q.2 ∧ q.2 ≤ q.1 ∧ q.1 < 1} := by
  intro q hq
  exact
    (weightedBernoulliClosedThresholdRate_continuousAt_pair
      (gHi := gHi) (gLo := gLo) (pHi := q.1) (pLo := q.2)
      (hq.1.trans_le hq.2.1) hq.2.2 hq.1
      (lt_of_le_of_lt hq.2.1 hq.2.2)).continuousWithinAt

/--
Continuity of the closed threshold rate on a low-endpoint interval whose high
endpoint remains fixed.
-/
theorem weightedBernoulliClosedThresholdRate_continuousOn_lo_Icc
    {gHi gLo pHi left right : ℝ}
    (hleft0 : 0 < left) (hright_le_hi : right ≤ pHi) (hpHi1 : pHi < 1) :
    ContinuousOn
      (fun x : ℝ => weightedBernoulliClosedThresholdRate gHi gLo pHi x)
      (Set.Icc left right) := by
  intro x hx
  have hpHi0 : 0 < pHi := hleft0.trans_le (hx.1.trans (hx.2.trans hright_le_hi))
  have hx0 : 0 < x := hleft0.trans_le hx.1
  have hx_le_hi : x ≤ pHi := hx.2.trans hright_le_hi
  have hx1 : x < 1 := lt_of_le_of_lt hx_le_hi hpHi1
  exact
    (weightedBernoulliClosedThresholdRate_continuousAt_lo
      (gHi := gHi) (gLo := gLo) (pHi := pHi) (pLo := x)
      hpHi0 hpHi1 hx0 hx1).continuousWithinAt

/--
For a fixed high endpoint, the closed threshold rate is strictly decreasing in
the low endpoint on any interval below the high endpoint.
-/
theorem weightedBernoulliClosedThresholdRate_strictAntiOn_lo_Icc
    {gHi gLo pHi left right : ℝ}
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hleft0 : 0 < left) (hright_le_hi : right ≤ pHi) (hpHi1 : pHi < 1) :
    StrictAntiOn
      (fun x : ℝ => weightedBernoulliClosedThresholdRate gHi gLo pHi x)
      (Set.Icc left right) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := hleft0.trans_le hx.1
  have hy_le_hi : y ≤ pHi := hy.2.trans hright_le_hi
  exact
    weightedBernoulliClosedThresholdRate_lt_of_shrink_lo_lt
      (gHi := gHi) (gLo := gLo) (pHi := pHi) (pLo := x)
      (pHi' := pHi) (pLo' := y)
      hgHi hgLo hx0 hxy hy_le_hi le_rfl hpHi1

/--
One-dimensional shooting for the low endpoint: if a target rate lies between
the rate at a left cap and the diagonal value, then there is an interior low
endpoint realizing exactly that target.
-/
theorem exists_low_endpoint_for_weightedBernoulliClosedThresholdRate
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
          pLo ≤ x) := by
  let f : ℝ → ℝ :=
    fun x => weightedBernoulliClosedThresholdRate gHi gLo pHi x
  have hcont : ContinuousOn f (Set.Icc left pHi) :=
    weightedBernoulliClosedThresholdRate_continuousOn_lo_Icc
      (gHi := gHi) (gLo := gLo) hleft0 le_rfl hpHi1
  have hanti : StrictAntiOn f (Set.Icc left pHi) :=
    weightedBernoulliClosedThresholdRate_strictAntiOn_lo_Icc
      (gHi := gHi) (gLo := gLo) hgHi hgLo hleft0 le_rfl hpHi1
  have hpHi0 : 0 < pHi := hleft0.trans hleft_lt_hi
  have hright : f pHi < target := by
    dsimp [f]
    rw [weightedBernoulliClosedThresholdRate_self hgHi hgLo hpHi0 hpHi1]
    exact htarget_pos
  rcases
    AppliedModelingLib.exists_threshold_of_continuous_strictAntiOn_Icc_crossing_interval
      (f := f) (level := target) (left := left) (right := pHi)
      hleft_lt_hi hcont hanti htarget_lt_left hright with
    ⟨pLo, hpLo_mem, hpLo_rate, hgt, hlt, hge, hle⟩
  exact ⟨pLo, hpLo_mem, hpLo_rate, hgt, hlt, hge, hle⟩

/--
The low endpoint realizing a target closed threshold rate is unique inside the
bracket interval.
-/
theorem existsUnique_low_endpoint_for_weightedBernoulliClosedThresholdRate
    {gHi gLo left pHi target : ℝ}
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hleft0 : 0 < left) (hleft_lt_hi : left < pHi)
    (hpHi1 : pHi < 1)
    (htarget_pos : 0 < target)
    (htarget_lt_left :
      target <
        weightedBernoulliClosedThresholdRate gHi gLo pHi left) :
    ∃! pLo : ℝ, pLo ∈ Set.Ioo left pHi ∧
      weightedBernoulliClosedThresholdRate gHi gLo pHi pLo = target := by
  rcases
    exists_low_endpoint_for_weightedBernoulliClosedThresholdRate
      hgHi hgLo hleft0 hleft_lt_hi hpHi1 htarget_pos htarget_lt_left with
    ⟨pLo, hpLo_mem, hpLo_rate, _hgt, _hlt, hge, hle⟩
  refine ⟨pLo, ⟨hpLo_mem, hpLo_rate⟩, ?_⟩
  intro y hy
  have hyIcc : y ∈ Set.Icc left pHi := ⟨hy.1.1.le, hy.1.2.le⟩
  have hy_le : y ≤ pLo := (hge y hyIcc).mp hy.2.ge
  have hpLo_le : pLo ≤ y := (hle y hyIcc).mp hy.2.le
  exact le_antisymm hy_le hpLo_le

/--
Any selector that returns the low endpoint realizing each target rate is
continuous on its target domain.
-/
theorem continuousOn_lowEndpointSelector_for_weightedBernoulliClosedThresholdRate
    {gHi gLo left pHi : ℝ} {targetSet : Set ℝ} {root : ℝ → ℝ}
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hleft0 : 0 < left) (hleft_lt_hi : left < pHi)
    (hpHi1 : pHi < 1)
    (hroot_mem : ∀ target ∈ targetSet, root target ∈ Set.Ioo left pHi)
    (hroot_rate :
      ∀ target ∈ targetSet,
        weightedBernoulliClosedThresholdRate gHi gLo pHi (root target) =
          target) :
    ContinuousOn root targetSet := by
  let base : ℝ → ℝ :=
    fun x => weightedBernoulliClosedThresholdRate gHi gLo pHi x
  have hanti : StrictAntiOn base (Set.Icc left pHi) :=
    weightedBernoulliClosedThresholdRate_strictAntiOn_lo_Icc
      (gHi := gHi) (gLo := gLo) hgHi hgLo hleft0 le_rfl hpHi1
  exact
    AppliedModelingLib.continuousOn_rightInverse_of_strictAntiOn_Icc
      (base := base) (root := root) (s := targetSet)
      (left := left) (right := pHi)
      hanti hroot_mem hroot_rate

/--
Feasibility conditions for selecting a low endpoint that realizes a target
closed threshold rate above a fixed floor.
-/
structure WeightedBernoulliLowEndpointTargetFeasible
    (gHi gLo floor pHi target : ℝ) : Prop where
  hgHi : 0 < gHi
  hgLo : 0 < gLo
  hfloor0 : 0 < floor
  hfloor_lt_hi : floor < pHi
  hpHi1 : pHi < 1
  htarget_pos : 0 < target
  htarget_lt_floor :
    target < weightedBernoulliClosedThresholdRate gHi gLo pHi floor

/--
Clipped low-endpoint selector for target-rate shooting.  If the target rate is
attainable above the floor, this returns the unique interior low endpoint;
otherwise it returns the floor.
-/
def weightedBernoulliLowEndpointOfRateOrFloor
    (gHi gLo floor pHi target : ℝ) : ℝ := by
  classical
  exact
    if h : WeightedBernoulliLowEndpointTargetFeasible
        gHi gLo floor pHi target then
      Classical.choose
        (exists_low_endpoint_for_weightedBernoulliClosedThresholdRate
          h.hgHi h.hgLo h.hfloor0 h.hfloor_lt_hi h.hpHi1
          h.htarget_pos h.htarget_lt_floor)
    else
      floor

/-- Under feasibility, the clipped low-endpoint selector lies strictly between the floor and high endpoint. -/
theorem weightedBernoulliLowEndpointOfRateOrFloor_mem_Ioo_of_feasible
    {gHi gLo floor pHi target : ℝ}
    (h : WeightedBernoulliLowEndpointTargetFeasible
      gHi gLo floor pHi target) :
    weightedBernoulliLowEndpointOfRateOrFloor gHi gLo floor pHi target ∈
      Set.Ioo floor pHi := by
  unfold weightedBernoulliLowEndpointOfRateOrFloor
  simp [h]
  simpa using
    (Classical.choose_spec
      (exists_low_endpoint_for_weightedBernoulliClosedThresholdRate
        h.hgHi h.hgLo h.hfloor0 h.hfloor_lt_hi h.hpHi1
        h.htarget_pos h.htarget_lt_floor)).1

/-- Under feasibility, the clipped low-endpoint selector realizes the requested target rate. -/
theorem weightedBernoulliLowEndpointOfRateOrFloor_rate_of_feasible
    {gHi gLo floor pHi target : ℝ}
    (h : WeightedBernoulliLowEndpointTargetFeasible
      gHi gLo floor pHi target) :
    weightedBernoulliClosedThresholdRate gHi gLo pHi
        (weightedBernoulliLowEndpointOfRateOrFloor gHi gLo floor pHi target) =
      target := by
  unfold weightedBernoulliLowEndpointOfRateOrFloor
  simp [h]
  simpa using
    (Classical.choose_spec
      (exists_low_endpoint_for_weightedBernoulliClosedThresholdRate
        h.hgHi h.hgLo h.hfloor0 h.hfloor_lt_hi h.hpHi1
        h.htarget_pos h.htarget_lt_floor)).2.1

/--
On the boundary where the target equals the floor rate, the clipped
low-endpoint selector returns the floor and therefore still realizes the
target rate.  This is the weak-feasibility side of target-rate shooting.
-/
theorem weightedBernoulliLowEndpointOfRateOrFloor_rate_of_target_eq_floor_rate
    {gHi gLo floor pHi target : ℝ}
    (htarget_eq_floor :
      target = weightedBernoulliClosedThresholdRate gHi gLo pHi floor) :
    weightedBernoulliClosedThresholdRate gHi gLo pHi
        (weightedBernoulliLowEndpointOfRateOrFloor gHi gLo floor pHi target) =
      target := by
  unfold weightedBernoulliLowEndpointOfRateOrFloor
  by_cases h :
      WeightedBernoulliLowEndpointTargetFeasible
        gHi gLo floor pHi target
  · rw [htarget_eq_floor] at h
    exfalso
    exact (lt_irrefl _) h.htarget_lt_floor
  · rw [dif_neg h]
    exact htarget_eq_floor.symm

/--
Weak target-rate shooting for the clipped low-endpoint selector.  If the target
rate is at or below the floor rate, the selector realizes the target: in the
strict case it chooses the unique interior low endpoint; in the equality case
it clips to the floor.
-/
theorem weightedBernoulliLowEndpointOfRateOrFloor_rate_of_target_le_floor_rate
    {gHi gLo floor pHi target : ℝ}
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hfloor0 : 0 < floor) (hfloor_lt_hi : floor < pHi)
    (hpHi1 : pHi < 1) (htarget_pos : 0 < target)
    (htarget_le_floor :
      target ≤ weightedBernoulliClosedThresholdRate gHi gLo pHi floor) :
    weightedBernoulliClosedThresholdRate gHi gLo pHi
        (weightedBernoulliLowEndpointOfRateOrFloor gHi gLo floor pHi target) =
      target := by
  rcases lt_or_eq_of_le htarget_le_floor with htarget_lt_floor | htarget_eq_floor
  · exact
      weightedBernoulliLowEndpointOfRateOrFloor_rate_of_feasible
        ⟨hgHi, hgLo, hfloor0, hfloor_lt_hi, hpHi1, htarget_pos,
          htarget_lt_floor⟩
  · exact
      weightedBernoulliLowEndpointOfRateOrFloor_rate_of_target_eq_floor_rate
        htarget_eq_floor

/-- If feasibility fails, the clipped low-endpoint selector returns the floor. -/
theorem weightedBernoulliLowEndpointOfRateOrFloor_eq_floor_of_not_feasible
    {gHi gLo floor pHi target : ℝ}
    (h : ¬ WeightedBernoulliLowEndpointTargetFeasible
      gHi gLo floor pHi target) :
    weightedBernoulliLowEndpointOfRateOrFloor gHi gLo floor pHi target =
      floor := by
  simp [weightedBernoulliLowEndpointOfRateOrFloor, h]

/--
If the clipped low-endpoint selector returns a point strictly above the floor,
then the target-rate feasibility certificate must hold.  This is the converse
of the infeasible branch of `weightedBernoulliLowEndpointOfRateOrFloor`.
-/
theorem weightedBernoulliLowEndpointTargetFeasible_of_floor_lt_lowEndpointOfRateOrFloor
    {gHi gLo floor pHi target : ℝ}
    (hfloor_lt :
      floor <
        weightedBernoulliLowEndpointOfRateOrFloor gHi gLo floor pHi target) :
    WeightedBernoulliLowEndpointTargetFeasible gHi gLo floor pHi target := by
  by_contra hnot
  have hfloor_eq :
      weightedBernoulliLowEndpointOfRateOrFloor gHi gLo floor pHi target =
        floor :=
    weightedBernoulliLowEndpointOfRateOrFloor_eq_floor_of_not_feasible hnot
  rw [hfloor_eq] at hfloor_lt
  exact (lt_irrefl floor) hfloor_lt

/-- If the floor is not strictly below the high endpoint, the clipped selector returns the floor. -/
theorem weightedBernoulliLowEndpointOfRateOrFloor_eq_floor_of_not_lt_hi
    {gHi gLo floor pHi target : ℝ} (hnot_lt : ¬ floor < pHi) :
    weightedBernoulliLowEndpointOfRateOrFloor gHi gLo floor pHi target =
      floor := by
  refine weightedBernoulliLowEndpointOfRateOrFloor_eq_floor_of_not_feasible ?_
  intro h
  exact hnot_lt h.hfloor_lt_hi

/--
The clipped low-endpoint selector is always at least its floor.  In the
infeasible branch it is exactly the floor; in the feasible branch this follows
from the selected interior witness.
-/
theorem floor_le_weightedBernoulliLowEndpointOfRateOrFloor_unconditional
    {gHi gLo floor pHi target : ℝ} :
    floor ≤
      weightedBernoulliLowEndpointOfRateOrFloor gHi gLo floor pHi target := by
  by_cases h : WeightedBernoulliLowEndpointTargetFeasible
      gHi gLo floor pHi target
  · exact
      (weightedBernoulliLowEndpointOfRateOrFloor_mem_Ioo_of_feasible h).1.le
  · rw [weightedBernoulliLowEndpointOfRateOrFloor_eq_floor_of_not_feasible h]

/-- Under weak bracket validity, the clipped low-endpoint selector is at least the floor. -/
theorem floor_le_weightedBernoulliLowEndpointOfRateOrFloor
    {gHi gLo floor pHi target : ℝ} (hfloor_le_hi : floor ≤ pHi) :
    floor ≤
      weightedBernoulliLowEndpointOfRateOrFloor gHi gLo floor pHi target := by
  exact floor_le_weightedBernoulliLowEndpointOfRateOrFloor_unconditional

/-- Under weak bracket validity, the clipped low-endpoint selector is at most the high endpoint. -/
theorem weightedBernoulliLowEndpointOfRateOrFloor_le_hi
    {gHi gLo floor pHi target : ℝ} (hfloor_le_hi : floor ≤ pHi) :
    weightedBernoulliLowEndpointOfRateOrFloor gHi gLo floor pHi target ≤
      pHi := by
  by_cases h : WeightedBernoulliLowEndpointTargetFeasible
      gHi gLo floor pHi target
  · exact
      (weightedBernoulliLowEndpointOfRateOrFloor_mem_Ioo_of_feasible h).2.le
  · rw [weightedBernoulliLowEndpointOfRateOrFloor_eq_floor_of_not_feasible h]
    exact hfloor_le_hi

/-- Under weak bracket validity, the clipped low-endpoint selector lies in the bracket. -/
theorem weightedBernoulliLowEndpointOfRateOrFloor_mem_Icc
    {gHi gLo floor pHi target : ℝ} (hfloor_le_hi : floor ≤ pHi) :
    weightedBernoulliLowEndpointOfRateOrFloor gHi gLo floor pHi target ∈
      Set.Icc floor pHi :=
  ⟨floor_le_weightedBernoulliLowEndpointOfRateOrFloor hfloor_le_hi,
    weightedBernoulliLowEndpointOfRateOrFloor_le_hi hfloor_le_hi⟩

/--
The clipped low-endpoint selector never produces a closed threshold rate above
the target, assuming positive weights, a positive floor, and a weak valid
bracket.
-/
theorem weightedBernoulliClosedThresholdRate_lowEndpointOfRateOrFloor_le_target
    {gHi gLo floor pHi target : ℝ}
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hfloor0 : 0 < floor) (hfloor_le_hi : floor ≤ pHi)
    (hpHi1 : pHi < 1) (htarget_pos : 0 < target) :
    weightedBernoulliClosedThresholdRate gHi gLo pHi
        (weightedBernoulliLowEndpointOfRateOrFloor gHi gLo floor pHi target) ≤
      target := by
  by_cases h : WeightedBernoulliLowEndpointTargetFeasible
      gHi gLo floor pHi target
  · rw [weightedBernoulliLowEndpointOfRateOrFloor_rate_of_feasible h]
  · rw [weightedBernoulliLowEndpointOfRateOrFloor_eq_floor_of_not_feasible h]
    rcases lt_or_eq_of_le hfloor_le_hi with hfloor_lt_hi | hhi_eq
    · have hfeas_except :
          WeightedBernoulliLowEndpointTargetFeasible
            gHi gLo floor pHi target ↔
          target < weightedBernoulliClosedThresholdRate gHi gLo pHi floor := by
        constructor
        · intro hfeas
          exact hfeas.htarget_lt_floor
        · intro htarget_lt_floor
          exact
            ⟨hgHi, hgLo, hfloor0, hfloor_lt_hi, hpHi1,
              htarget_pos, htarget_lt_floor⟩
      have hnot_lt :
          ¬ target < weightedBernoulliClosedThresholdRate gHi gLo pHi floor := by
        intro htarget_lt_floor
        exact h ((hfeas_except.mpr htarget_lt_floor))
      exact le_of_not_gt hnot_lt
    · subst pHi
      rw [weightedBernoulliClosedThresholdRate_self hgHi hgLo hfloor0 hpHi1]
      exact htarget_pos.le

/--
If a candidate low endpoint already has closed threshold rate at most the
target, then the clipped low-endpoint selector lies no higher than that
candidate.  In the infeasible branch the selector is the floor; in the feasible
branch this is the right-side characterization of the unique shooting root.
-/
theorem weightedBernoulliLowEndpointOfRateOrFloor_le_of_rate_le_target
    {gHi gLo floor pHi target x : ℝ}
    (hfloor_le_x : floor ≤ x)
    (hx_le_hi : x ≤ pHi)
    (hrate_le :
      weightedBernoulliClosedThresholdRate gHi gLo pHi x ≤ target) :
    weightedBernoulliLowEndpointOfRateOrFloor gHi gLo floor pHi target ≤ x := by
  by_cases h : WeightedBernoulliLowEndpointTargetFeasible
      gHi gLo floor pHi target
  · by_contra hnot
    have hx_lt_root :
        x < weightedBernoulliLowEndpointOfRateOrFloor
            gHi gLo floor pHi target :=
      lt_of_not_ge hnot
    have hroot_mem :
        weightedBernoulliLowEndpointOfRateOrFloor
            gHi gLo floor pHi target ∈ Set.Ioo floor pHi :=
      weightedBernoulliLowEndpointOfRateOrFloor_mem_Ioo_of_feasible h
    have hanti :
        StrictAntiOn
          (fun y : ℝ => weightedBernoulliClosedThresholdRate gHi gLo pHi y)
          (Set.Icc floor pHi) :=
      weightedBernoulliClosedThresholdRate_strictAntiOn_lo_Icc
        h.hgHi h.hgLo h.hfloor0 le_rfl h.hpHi1
    have hrate_lt :
        weightedBernoulliClosedThresholdRate gHi gLo pHi
            (weightedBernoulliLowEndpointOfRateOrFloor
              gHi gLo floor pHi target) <
          weightedBernoulliClosedThresholdRate gHi gLo pHi x :=
      hanti ⟨hfloor_le_x, hx_le_hi⟩
        ⟨hroot_mem.1.le, hroot_mem.2.le⟩ hx_lt_root
    rw [weightedBernoulliLowEndpointOfRateOrFloor_rate_of_feasible h] at hrate_lt
    exact not_lt_of_ge hrate_le hrate_lt
  · rw [weightedBernoulliLowEndpointOfRateOrFloor_eq_floor_of_not_feasible h]
    exact hfloor_le_x

/--
Feasible low-endpoint selector comparison without assuming the candidate is
above the floor.  If the selector's shooting problem is feasible and a positive
candidate below the high endpoint already has rate at most the target, strict
antitonicity forces the selected endpoint below that candidate.
-/
theorem weightedBernoulliLowEndpointOfRateOrFloor_le_of_feasible_rate_le_target
    {gHi gLo floor pHi target x : ℝ}
    (h : WeightedBernoulliLowEndpointTargetFeasible
      gHi gLo floor pHi target)
    (hx0 : 0 < x)
    (hx_le_hi : x ≤ pHi)
    (hrate_le :
      weightedBernoulliClosedThresholdRate gHi gLo pHi x ≤ target) :
    weightedBernoulliLowEndpointOfRateOrFloor gHi gLo floor pHi target ≤ x := by
  by_contra hnot
  have hx_lt_root :
      x < weightedBernoulliLowEndpointOfRateOrFloor
          gHi gLo floor pHi target :=
    lt_of_not_ge hnot
  have hroot_mem :
      weightedBernoulliLowEndpointOfRateOrFloor
          gHi gLo floor pHi target ∈ Set.Ioo floor pHi :=
    weightedBernoulliLowEndpointOfRateOrFloor_mem_Ioo_of_feasible h
  have hanti :
      StrictAntiOn
        (fun y : ℝ => weightedBernoulliClosedThresholdRate gHi gLo pHi y)
        (Set.Icc x pHi) :=
    weightedBernoulliClosedThresholdRate_strictAntiOn_lo_Icc
      h.hgHi h.hgLo hx0 le_rfl h.hpHi1
  have hrate_lt :
      weightedBernoulliClosedThresholdRate gHi gLo pHi
          (weightedBernoulliLowEndpointOfRateOrFloor
            gHi gLo floor pHi target) <
        weightedBernoulliClosedThresholdRate gHi gLo pHi x :=
    hanti ⟨le_rfl, hx_le_hi⟩
      ⟨hx_lt_root.le, hroot_mem.2.le⟩ hx_lt_root
  rw [weightedBernoulliLowEndpointOfRateOrFloor_rate_of_feasible h] at hrate_lt
  exact not_lt_of_ge hrate_le hrate_lt

/--
Feasible low-endpoint selector comparison in the opposite direction.  If the
selector's shooting problem is feasible and a candidate in the bracket still
has closed threshold rate at least the target, strict antitonicity forces that
candidate to lie below the selected endpoint.
-/
theorem le_weightedBernoulliLowEndpointOfRateOrFloor_of_feasible_target_le_rate
    {gHi gLo floor pHi target x : ℝ}
    (h : WeightedBernoulliLowEndpointTargetFeasible
      gHi gLo floor pHi target)
    (hfloor_le_x : floor ≤ x)
    (hx_le_hi : x ≤ pHi)
    (htarget_le :
      target ≤ weightedBernoulliClosedThresholdRate gHi gLo pHi x) :
    x ≤ weightedBernoulliLowEndpointOfRateOrFloor gHi gLo floor pHi target := by
  by_contra hnot
  have hroot_lt_x :
      weightedBernoulliLowEndpointOfRateOrFloor gHi gLo floor pHi target < x :=
    lt_of_not_ge hnot
  have hroot_mem :
      weightedBernoulliLowEndpointOfRateOrFloor
          gHi gLo floor pHi target ∈ Set.Ioo floor pHi :=
    weightedBernoulliLowEndpointOfRateOrFloor_mem_Ioo_of_feasible h
  have hanti :
      StrictAntiOn
        (fun y : ℝ => weightedBernoulliClosedThresholdRate gHi gLo pHi y)
        (Set.Icc floor pHi) :=
    weightedBernoulliClosedThresholdRate_strictAntiOn_lo_Icc
      h.hgHi h.hgLo h.hfloor0 le_rfl h.hpHi1
  have hrate_lt :
      weightedBernoulliClosedThresholdRate gHi gLo pHi x <
        weightedBernoulliClosedThresholdRate gHi gLo pHi
          (weightedBernoulliLowEndpointOfRateOrFloor
            gHi gLo floor pHi target) :=
    hanti ⟨hroot_mem.1.le, hroot_mem.2.le⟩
      ⟨hfloor_le_x, hx_le_hi⟩ hroot_lt_x
  rw [weightedBernoulliLowEndpointOfRateOrFloor_rate_of_feasible h] at hrate_lt
  exact not_lt_of_ge htarget_le hrate_lt

/--
Weak comparison for the clipped low-endpoint selector.  If a candidate endpoint
in the valid bracket still has closed threshold rate at least the target, then
the candidate lies below the clipped selected endpoint.  Unlike
`le_weightedBernoulliLowEndpointOfRateOrFloor_of_feasible_target_le_rate`,
this also handles the boundary case where the target is exactly the floor
rate and the selector clips to the floor.
-/
theorem le_weightedBernoulliLowEndpointOfRateOrFloor_of_target_le_rate
    {gHi gLo floor pHi target x : ℝ}
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hfloor0 : 0 < floor) (hfloor_lt_hi : floor < pHi)
    (hpHi1 : pHi < 1) (htarget_pos : 0 < target)
    (hfloor_le_x : floor ≤ x) (hx_le_hi : x ≤ pHi)
    (htarget_le :
      target ≤ weightedBernoulliClosedThresholdRate gHi gLo pHi x) :
    x ≤ weightedBernoulliLowEndpointOfRateOrFloor gHi gLo floor pHi target := by
  by_cases h : WeightedBernoulliLowEndpointTargetFeasible
      gHi gLo floor pHi target
  · exact
      le_weightedBernoulliLowEndpointOfRateOrFloor_of_feasible_target_le_rate
        h hfloor_le_x hx_le_hi htarget_le
  · rw [weightedBernoulliLowEndpointOfRateOrFloor_eq_floor_of_not_feasible h]
    by_contra hnot
    have hfloor_lt_x : floor < x := lt_of_not_ge hnot
    have hnot_target_lt_floor :
        ¬ target < weightedBernoulliClosedThresholdRate gHi gLo pHi floor := by
      intro htarget_lt_floor
      exact h
        { hgHi := hgHi
          hgLo := hgLo
          hfloor0 := hfloor0
          hfloor_lt_hi := hfloor_lt_hi
          hpHi1 := hpHi1
          htarget_pos := htarget_pos
          htarget_lt_floor := htarget_lt_floor }
    have hfloor_rate_le_target :
        weightedBernoulliClosedThresholdRate gHi gLo pHi floor ≤ target :=
      le_of_not_gt hnot_target_lt_floor
    have hanti :
        StrictAntiOn
          (fun y : ℝ => weightedBernoulliClosedThresholdRate gHi gLo pHi y)
          (Set.Icc floor pHi) :=
      weightedBernoulliClosedThresholdRate_strictAntiOn_lo_Icc
        hgHi hgLo hfloor0 le_rfl hpHi1
    have hx_rate_lt_floor_rate :
        weightedBernoulliClosedThresholdRate gHi gLo pHi x <
          weightedBernoulliClosedThresholdRate gHi gLo pHi floor :=
      hanti ⟨le_rfl, hfloor_lt_hi.le⟩ ⟨hfloor_le_x, hx_le_hi⟩ hfloor_lt_x
    linarith

/--
Under feasibility, the clipped low-endpoint selector is the threshold for the
rate comparison on the bracket: a candidate low endpoint is to the right of
the selector exactly when its closed-threshold rate is at most the target.
-/
theorem weightedBernoulliLowEndpointOfRateOrFloor_le_iff_rate_le_target_of_feasible
    {gHi gLo floor pHi target x : ℝ}
    (h : WeightedBernoulliLowEndpointTargetFeasible
      gHi gLo floor pHi target)
    (hfloor_le_x : floor ≤ x)
    (hx_le_hi : x ≤ pHi) :
    weightedBernoulliLowEndpointOfRateOrFloor gHi gLo floor pHi target ≤ x ↔
      weightedBernoulliClosedThresholdRate gHi gLo pHi x ≤ target := by
  constructor
  · intro hroot_le_x
    have hroot_mem :
        weightedBernoulliLowEndpointOfRateOrFloor
            gHi gLo floor pHi target ∈ Set.Ioo floor pHi :=
      weightedBernoulliLowEndpointOfRateOrFloor_mem_Ioo_of_feasible h
    have hanti :
        StrictAntiOn
          (fun y : ℝ => weightedBernoulliClosedThresholdRate gHi gLo pHi y)
          (Set.Icc floor pHi) :=
      weightedBernoulliClosedThresholdRate_strictAntiOn_lo_Icc
        h.hgHi h.hgLo h.hfloor0 le_rfl h.hpHi1
    rcases lt_or_eq_of_le hroot_le_x with hroot_lt_x | hroot_eq_x
    · have hrate_lt :
          weightedBernoulliClosedThresholdRate gHi gLo pHi x <
            weightedBernoulliClosedThresholdRate gHi gLo pHi
              (weightedBernoulliLowEndpointOfRateOrFloor
                gHi gLo floor pHi target) :=
        hanti ⟨hroot_mem.1.le, hroot_mem.2.le⟩
          ⟨hfloor_le_x, hx_le_hi⟩ hroot_lt_x
      rw [weightedBernoulliLowEndpointOfRateOrFloor_rate_of_feasible h] at hrate_lt
      exact hrate_lt.le
    · rw [← hroot_eq_x,
        weightedBernoulliLowEndpointOfRateOrFloor_rate_of_feasible h]
  · intro hrate_le
    exact
      weightedBernoulliLowEndpointOfRateOrFloor_le_of_rate_le_target
        hfloor_le_x hx_le_hi hrate_le

/--
At the inverse-dual Bernoulli parameter, the finite Legendre objective is the
Bernoulli KL divergence.
-/
theorem finiteLegendreValue_realBernoulliPMF_binaryRatingScore_inverse_eq_bernoulliKL
    {p a : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (ha0 : 0 < a) (ha1 : a < 1) :
    finiteLegendreValue (realBernoulliPMF p hp0.le hp1.le)
        binaryRatingScore a (binaryLogMGFDerivativeArg p a) =
      bernoulliKL a p := by
  have hp_ne : p ≠ 0 := ne_of_gt hp0
  have h_one_sub_p_pos : 0 < 1 - p := sub_pos.mpr hp1
  have h_one_sub_p_ne : 1 - p ≠ 0 := ne_of_gt h_one_sub_p_pos
  have ha_ne : a ≠ 0 := ne_of_gt ha0
  have h_one_sub_a_pos : 0 < 1 - a := sub_pos.mpr ha1
  have h_one_sub_a_ne : 1 - a ≠ 0 := ne_of_gt h_one_sub_a_pos
  have hratio_pos : 0 < a * (1 - p) / (p * (1 - a)) := by
    exact div_pos
      (mul_pos ha0 h_one_sub_p_pos)
      (mul_pos hp0 h_one_sub_a_pos)
  have hmgf :
      (1 - p) + p * (a * (1 - p) / (p * (1 - a))) =
        (1 - p) / (1 - a) := by
    field_simp [hp_ne, h_one_sub_a_ne]
    ring
  have hmain :
      binaryLogMGFDerivativeArg p a * a -
          Real.log ((1 - p) +
            p * Real.exp (binaryLogMGFDerivativeArg p a)) =
        bernoulliKL a p := by
    rw [binaryLogMGFDerivativeArg, Real.exp_log hratio_pos, hmgf,
      bernoulliKL]
    rw [Real.log_div (mul_ne_zero ha_ne h_one_sub_p_ne)
      (mul_ne_zero hp_ne h_one_sub_a_ne)]
    rw [Real.log_mul ha_ne h_one_sub_p_ne]
    rw [Real.log_mul hp_ne h_one_sub_a_ne]
    rw [Real.log_div h_one_sub_p_ne h_one_sub_a_ne]
    rw [Real.log_div ha_ne hp_ne]
    rw [Real.log_div h_one_sub_a_ne h_one_sub_p_ne]
    ring
  simpa [finiteLegendreValue,
    finiteLogMGF_realBernoulliPMF_binaryRatingScore] using hmain

/-- Interior Bernoulli binary finite-rate function equals Bernoulli KL. -/
theorem finiteRateFunction_realBernoulliPMF_binaryRatingScore_eq_bernoulliKL
    {p a : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (ha0 : 0 < a) (ha1 : a < 1) :
    finiteRateFunction (realBernoulliPMF p hp0.le hp1.le)
        binaryRatingScore a =
      bernoulliKL a p := by
  rw [finiteRateFunction_eq_eval_of_logMGF_hasDerivAt_no_bdd
    (realBernoulliPMF p hp0.le hp1.le) binaryRatingScore
    a (binaryLogMGFDerivativeArg p a)
    (finiteLogMGF_realBernoulliPMF_binaryRatingScore_hasDerivAt_inverse
      p a hp0 hp1 ha0 ha1)]
  exact
    finiteLegendreValue_realBernoulliPMF_binaryRatingScore_inverse_eq_bernoulliKL
      hp0 hp1 ha0 ha1

/-- Interior Bernoulli binary extended finite-rate function equals Bernoulli KL. -/
theorem finiteRateFunctionTop_realBernoulliPMF_binaryRatingScore_eq_bernoulliKL
    {p a : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (ha0 : 0 < a) (ha1 : a < 1) :
    finiteRateFunctionTop (realBernoulliPMF p hp0.le hp1.le)
        binaryRatingScore a =
      (bernoulliKL a p : WithTop ℝ) := by
  rw [finiteRateFunctionTop_eq_eval_of_logMGF_hasDerivAt
    (realBernoulliPMF p hp0.le hp1.le) binaryRatingScore
    a (binaryLogMGFDerivativeArg p a)
    (finiteLogMGF_realBernoulliPMF_binaryRatingScore_hasDerivAt_inverse
      p a hp0 hp1 ha0 ha1)]
  exact_mod_cast
    finiteLegendreValue_realBernoulliPMF_binaryRatingScore_inverse_eq_bernoulliKL
      hp0 hp1 ha0 ha1

/-- `Bool`-valued finite-rating LDP model from real success probabilities. -/
def realBinaryRatingLDPModel {θ : Type*}
    (successProb : θ → ℝ)
    (hprob0 : ∀ t, 0 ≤ successProb t)
    (hprob1 : ∀ t, successProb t ≤ 1) :
    FiniteRatingLDPModel θ Bool where
  typeLaw := fun t => realBernoulliPMF (successProb t) (hprob0 t) (hprob1 t)
  score := binaryRatingScore

/-- At Bernoulli endpoints, the joint two-sample law is concentrated on the
corresponding constant Boolean samples. -/
theorem realBinaryRatingLDPModel_twoSampleRatingLaw_endpoint_apply_toReal
    {θ : Type*} (successProb : θ → ℝ)
    (hprob0 : ∀ t, 0 ≤ successProb t)
    (hprob1 : ∀ t, successProb t ≤ 1)
    (hi lo : θ) (bHi bLo : Bool)
    (hpHi : successProb hi = if bHi then 1 else 0)
    (hpLo : successProb lo = if bLo then 1 else 0)
    (nHi nLo : ℕ)
    (sample : (Fin nHi → Bool) × (Fin nLo → Bool)) :
    (twoSampleRatingLaw
      (realBinaryRatingLDPModel successProb hprob0 hprob1)
      hi lo nHi nLo sample).toReal =
      if sample = ((fun _ : Fin nHi => bHi), (fun _ : Fin nLo => bLo))
      then 1 else 0 := by
  classical
  by_cases hs : sample = ((fun _ : Fin nHi => bHi), (fun _ : Fin nLo => bLo))
  · subst sample
    cases bHi <;> cases bLo <;>
      simp [twoSampleRatingLaw, realBinaryRatingLDPModel, hpHi, hpLo,
        realBernoulliPMF_apply_true_toReal,
        realBernoulliPMF_apply_false_toReal]
  · rw [if_neg hs]
    unfold twoSampleRatingLaw
    rw [AppliedModelingLib.pmfProd_apply_toReal]
    have hor : sample.1 ≠ (fun _ : Fin nHi => bHi) ∨
        sample.2 ≠ (fun _ : Fin nLo => bLo) := by
      by_contra h
      push Not at h
      exact hs (Prod.ext h.1 h.2)
    rcases hor with hhi | hlo
    · have hex : ∃ i : Fin nHi, sample.1 i ≠ bHi := by
        by_contra h
        push Not at h
        exact hhi (funext h)
      obtain ⟨i, hi_ne⟩ := hex
      apply mul_eq_zero_of_left
      rw [AppliedModelingLib.pmfProduct_apply_toReal]
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      cases bHi <;> cases hi_value : sample.1 i <;>
        simp_all [realBinaryRatingLDPModel,
          realBernoulliPMF_apply_true_toReal,
          realBernoulliPMF_apply_false_toReal]
    · have hex : ∃ i : Fin nLo, sample.2 i ≠ bLo := by
        by_contra h
        push Not at h
        exact hlo (funext h)
      obtain ⟨i, hlo_ne⟩ := hex
      apply mul_eq_zero_of_right
      rw [AppliedModelingLib.pmfProduct_apply_toReal]
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      cases bLo <;> cases lo_value : sample.2 i <;>
        simp_all [realBinaryRatingLDPModel,
          realBernoulliPMF_apply_true_toReal,
          realBernoulliPMF_apply_false_toReal]

/-- At Bernoulli endpoints, the joint two-sample law is the point mass on the
two constant endpoint samples. -/
theorem realBinaryRatingLDPModel_twoSampleRatingLaw_endpoint_eq_pure
    {θ : Type*} (successProb : θ → ℝ)
    (hprob0 : ∀ t, 0 ≤ successProb t)
    (hprob1 : ∀ t, successProb t ≤ 1)
    (hi lo : θ) (bHi bLo : Bool)
    (hpHi : successProb hi = if bHi then 1 else 0)
    (hpLo : successProb lo = if bLo then 1 else 0)
    (nHi nLo : ℕ) :
    twoSampleRatingLaw
      (realBinaryRatingLDPModel successProb hprob0 hprob1)
      hi lo nHi nLo =
      PMF.pure ((fun _ : Fin nHi => bHi), (fun _ : Fin nLo => bLo)) := by
  classical
  apply PMF.ext
  intro sample
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [realBinaryRatingLDPModel_twoSampleRatingLaw_endpoint_apply_toReal
    successProb hprob0 hprob1 hi lo bHi bLo hpHi hpLo nHi nLo sample]
  by_cases hs : sample = ((fun _ : Fin nHi => bHi), (fun _ : Fin nLo => bLo))
  · subst sample
    simp [PMF.pure_apply]
  · simp [PMF.pure_apply, hs]

/-- With positive sample counts, a pair of Bernoulli endpoint populations has
the deterministic paper objective given by the strict order of its two
Boolean scores. -/
theorem realBinaryRatingLDPModel_twoSamplePkObjectiveProb_eq_of_endpoints
    {θ : Type*} (successProb : θ → ℝ)
    (hprob0 : ∀ t, 0 ≤ successProb t)
    (hprob1 : ∀ t, successProb t ≤ 1)
    (hi lo : θ) (bHi bLo : Bool)
    (hpHi : successProb hi = if bHi then 1 else 0)
    (hpLo : successProb lo = if bLo then 1 else 0)
    (nHi nLo : ℕ) (hnHi : 0 < nHi) (hnLo : 0 < nLo) :
    twoSamplePkObjectiveProb
      (realBinaryRatingLDPModel successProb hprob0 hprob1)
      hi lo nHi nLo ((nHi : ℝ)⁻¹) ((nLo : ℝ)⁻¹) =
      (if binaryRatingScore bLo < binaryRatingScore bHi then 1 else 0) -
        (if binaryRatingScore bHi < binaryRatingScore bLo then 1 else 0) := by
  have hlaw := realBinaryRatingLDPModel_twoSampleRatingLaw_endpoint_eq_pure
    successProb hprob0 hprob1 hi lo bHi bLo hpHi hpLo nHi nLo
  unfold twoSamplePkObjectiveProb twoSampleScoreGapStrictRightProb
    twoSampleScoreGapStrictLeftProb
  rw [hlaw]
  simp only [AppliedModelingLib.pmfProb, AppliedModelingLib.pmfExp_pure]
  simp [twoSampleScoreGapSum, finiteIidScoreSum, hnHi.ne', hnLo.ne',
    realBinaryRatingLDPModel]

/-- A positive-count top-versus-bottom Bernoulli comparison has `P_k = 1`. -/
theorem realBinaryRatingLDPModel_twoSamplePkObjectiveProb_eq_one_of_one_zero
    {θ : Type*} (successProb : θ → ℝ)
    (hprob0 : ∀ t, 0 ≤ successProb t)
    (hprob1 : ∀ t, successProb t ≤ 1)
    (hi lo : θ) (hpHi : successProb hi = 1) (hpLo : successProb lo = 0)
    (nHi nLo : ℕ) (hnHi : 0 < nHi) (hnLo : 0 < nLo) :
    twoSamplePkObjectiveProb
      (realBinaryRatingLDPModel successProb hprob0 hprob1)
      hi lo nHi nLo ((nHi : ℝ)⁻¹) ((nLo : ℝ)⁻¹) = 1 := by
  have h :=
    realBinaryRatingLDPModel_twoSamplePkObjectiveProb_eq_of_endpoints
      successProb hprob0 hprob1 hi lo true false
      (by simpa using hpHi) (by simpa using hpLo) nHi nLo hnHi hnLo
  norm_num [binaryRatingScore] at h
  exact h

/-- Positive-count Bernoulli populations at the same endpoint have `P_k = 0`. -/
theorem realBinaryRatingLDPModel_twoSamplePkObjectiveProb_eq_zero_of_same_endpoint
    {θ : Type*} (successProb : θ → ℝ)
    (hprob0 : ∀ t, 0 ≤ successProb t)
    (hprob1 : ∀ t, successProb t ≤ 1)
    (hi lo : θ) (b : Bool)
    (hpHi : successProb hi = if b then 1 else 0)
    (hpLo : successProb lo = if b then 1 else 0)
    (nHi nLo : ℕ) (hnHi : 0 < nHi) (hnLo : 0 < nLo) :
    twoSamplePkObjectiveProb
      (realBinaryRatingLDPModel successProb hprob0 hprob1)
      hi lo nHi nLo ((nHi : ℝ)⁻¹) ((nLo : ℝ)⁻¹) = 0 := by
  have h :=
    realBinaryRatingLDPModel_twoSamplePkObjectiveProb_eq_of_endpoints
      successProb hprob0 hprob1 hi lo b b hpHi hpLo nHi nLo hnHi hnLo
  cases b
  · norm_num [binaryRatingScore] at h ⊢
    exact h
  · norm_num [binaryRatingScore] at h ⊢
    exact h

/-- MGF formula for a real-parameter binary finite-rating model. -/
theorem realBinaryRatingLDPModel_mgf_eq
    {θ : Type*} (successProb : θ → ℝ)
    (hprob0 : ∀ t, 0 ≤ successProb t)
    (hprob1 : ∀ t, successProb t ≤ 1)
    (t : θ) (z : ℝ) :
    (realBinaryRatingLDPModel successProb hprob0 hprob1).mgf t z =
      (1 - successProb t) + successProb t * Real.exp z :=
  finiteMGF_realBernoulliPMF_binaryRatingScore
    (successProb t) z (hprob0 t) (hprob1 t)

/-- Log-MGF formula for a real-parameter binary finite-rating model. -/
theorem realBinaryRatingLDPModel_logMGF_eq
    {θ : Type*} (successProb : θ → ℝ)
    (hprob0 : ∀ t, 0 ≤ successProb t)
    (hprob1 : ∀ t, successProb t ≤ 1)
    (t : θ) (z : ℝ) :
    (realBinaryRatingLDPModel successProb hprob0 hprob1).logMGF t z =
      Real.log ((1 - successProb t) + successProb t * Real.exp z) :=
  finiteLogMGF_realBernoulliPMF_binaryRatingScore
    (successProb t) z (hprob0 t) (hprob1 t)

/-- Bernoulli atom masses are measurable in the real success probability. -/
theorem realBernoulliPMF_apply_toReal_measurable
    {α : Type*} [MeasurableSpace α]
    (successProb : α → ℝ)
    (hprob0 : ∀ x, 0 ≤ successProb x)
    (hprob1 : ∀ x, successProb x ≤ 1)
    (hprob_meas : Measurable successProb)
    (b : Bool) :
    Measurable fun x : α =>
      ((realBernoulliPMF (successProb x) (hprob0 x) (hprob1 x) b).toReal :
        ℝ) := by
  cases b
  · simpa using (measurable_const.sub hprob_meas)
  · simpa using hprob_meas

/--
For fixed sample counts, each two-sample binary rating atom has measurable
mass as a function of the two seller parameters.
-/
theorem realBinaryRatingLDPModel_twoSampleRatingLaw_apply_toReal_measurable
    (successProb : ℝ → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (nHi nLo : ℕ)
    (sample : (Fin nHi → Bool) × (Fin nLo → Bool)) :
    Measurable fun q : ℝ × ℝ =>
      (twoSampleRatingLaw
        (realBinaryRatingLDPModel successProb hprob0 hprob1)
        q.1 q.2 nHi nLo sample).toReal := by
  unfold twoSampleRatingLaw
  simp only [AppliedModelingLib.pmfProd_apply_toReal,
    AppliedModelingLib.pmfProduct_apply_toReal]
  refine (Finset.measurable_prod Finset.univ ?_).mul
    (Finset.measurable_prod Finset.univ ?_)
  · intro i _hi
    exact
      realBernoulliPMF_apply_toReal_measurable
        (fun q : ℝ × ℝ => successProb q.1)
        (fun q => hprob0 q.1) (fun q => hprob1 q.1)
        (hprob_meas.comp measurable_fst) (sample.1 i)
  · intro i _hi
    exact
      realBernoulliPMF_apply_toReal_measurable
        (fun q : ℝ × ℝ => successProb q.2)
        (fun q => hprob0 q.2) (fun q => hprob1 q.2)
        (hprob_meas.comp measurable_snd) (sample.2 i)

/--
For fixed sample counts and coefficients, the binary two-sample `1 - P_k`
comparison error is measurable in the two seller parameters.
-/
theorem realBinaryRatingLDPModel_twoSamplePkComplementErrorProb_measurable_fixed_counts
    (successProb : ℝ → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (nHi nLo : ℕ) (cHi cLo : ℝ) :
    Measurable fun q : ℝ × ℝ =>
      twoSamplePkComplementErrorProb
        (realBinaryRatingLDPModel successProb hprob0 hprob1)
        q.1 q.2 nHi nLo cHi cLo := by
  unfold twoSamplePkComplementErrorProb twoSampleScoreGapStrictLeftProb
    twoSampleScoreGapTieProb AppliedModelingLib.pmfProb AppliedModelingLib.pmfExp
  refine (measurable_const.mul ?_).add ?_
  · refine Finset.measurable_sum Finset.univ ?_
    intro sample _hsample
    exact
      (realBinaryRatingLDPModel_twoSampleRatingLaw_apply_toReal_measurable
        successProb hprob0 hprob1 hprob_meas nHi nLo sample).mul
        measurable_const
  · refine Finset.measurable_sum Finset.univ ?_
    intro sample _hsample
    exact
      (realBinaryRatingLDPModel_twoSampleRatingLaw_apply_toReal_measurable
        successProb hprob0 hprob1 hprob_meas nHi nLo sample).mul
        measurable_const

/--
The source floor-count binary `1 - P_k` comparison-error kernel is measurable
in the two seller parameters.
-/
theorem realBinaryRatingLDPModel_twoSampleFloorPkComplementErrorProb_measurable
    (successProb sampleRate : ℝ → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (k : ℕ) :
    Measurable fun q : ℝ × ℝ =>
      twoSampleFloorPkComplementErrorProb
        (realBinaryRatingLDPModel successProb hprob0 hprob1)
        sampleRate q.1 q.2 k := by
  let count : ℝ × ℝ → ℕ × ℕ := fun q =>
    (floorSampleCount sampleRate q.1 k,
      floorSampleCount sampleRate q.2 k)
  let F : (ℕ × ℕ) × (ℝ × ℝ) → ℝ := fun p =>
    twoSamplePkComplementErrorProb
      (realBinaryRatingLDPModel successProb hprob0 hprob1)
      p.2.1 p.2.2 p.1.1 p.1.2
      (((p.1.1 : ℕ) : ℝ)⁻¹) (((p.1.2 : ℕ) : ℝ)⁻¹)
  have hF : Measurable F := by
    refine measurable_from_prod_countable_right ?_
    intro counts
    exact
      realBinaryRatingLDPModel_twoSamplePkComplementErrorProb_measurable_fixed_counts
        successProb hprob0 hprob1 hprob_meas counts.1 counts.2
        (((counts.1 : ℕ) : ℝ)⁻¹) (((counts.2 : ℕ) : ℝ)⁻¹)
  have hcount : Measurable count := by
    have hnHi : Measurable fun q : ℝ × ℝ =>
        floorSampleCount sampleRate q.1 k := by
      dsimp [floorSampleCount]
      exact
        (measurable_const.mul (hsample_meas.comp measurable_fst)).nat_floor
    have hnLo : Measurable fun q : ℝ × ℝ =>
        floorSampleCount sampleRate q.2 k := by
      dsimp [floorSampleCount]
      exact
        (measurable_const.mul (hsample_meas.comp measurable_snd)).nat_floor
    exact hnHi.prodMk hnLo
  have hpair : Measurable fun q : ℝ × ℝ => (count q, q) :=
    hcount.prodMk measurable_id
  change Measurable fun q : ℝ × ℝ => F (count q, q)
  exact hF.comp hpair

/--
AEStrongly-measurable form of
`realBinaryRatingLDPModel_twoSampleFloorPkComplementErrorProb_measurable`.
-/
theorem realBinaryRatingLDPModel_twoSampleFloorPkComplementErrorProb_aestronglyMeasurable
    (μ : Measure (ℝ × ℝ))
    (successProb sampleRate : ℝ → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (k : ℕ) :
    AEStronglyMeasurable
      (fun q : ℝ × ℝ =>
        twoSampleFloorPkComplementErrorProb
          (realBinaryRatingLDPModel successProb hprob0 hprob1)
          sampleRate q.1 q.2 k) μ :=
  (realBinaryRatingLDPModel_twoSampleFloorPkComplementErrorProb_measurable
    successProb sampleRate hprob0 hprob1 hprob_meas hsample_meas k).aestronglyMeasurable

/--
The source floor-count binary paper objective `P_k` is measurable in the two
seller parameters.
-/
theorem realBinaryRatingLDPModel_twoSampleFloorPkObjectiveProb_measurable
    (successProb sampleRate : ℝ → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (k : ℕ) :
    Measurable fun q : ℝ × ℝ =>
      twoSampleFloorPkObjectiveProb
        (realBinaryRatingLDPModel successProb hprob0 hprob1)
        sampleRate q.1 q.2 k := by
  have herror :
      Measurable fun q : ℝ × ℝ =>
        twoSampleFloorPkComplementErrorProb
          (realBinaryRatingLDPModel successProb hprob0 hprob1)
          sampleRate q.1 q.2 k :=
    realBinaryRatingLDPModel_twoSampleFloorPkComplementErrorProb_measurable
      successProb sampleRate hprob0 hprob1 hprob_meas hsample_meas k
  have hobj_eq :
      (fun q : ℝ × ℝ =>
        twoSampleFloorPkObjectiveProb
          (realBinaryRatingLDPModel successProb hprob0 hprob1)
          sampleRate q.1 q.2 k) =
        fun q : ℝ × ℝ =>
          1 -
            twoSampleFloorPkComplementErrorProb
              (realBinaryRatingLDPModel successProb hprob0 hprob1)
              sampleRate q.1 q.2 k := by
    funext q
    have h :=
      twoSampleFloorPkComplementErrorProb_eq_one_sub_pkObjectiveProb
        (realBinaryRatingLDPModel successProb hprob0 hprob1)
        sampleRate q.1 q.2 k
    linarith
  rw [hobj_eq]
  exact measurable_const.sub herror

/--
AEStrongly-measurable form of
`realBinaryRatingLDPModel_twoSampleFloorPkObjectiveProb_measurable`.
-/
theorem realBinaryRatingLDPModel_twoSampleFloorPkObjectiveProb_aestronglyMeasurable
    (μ : Measure (ℝ × ℝ))
    (successProb sampleRate : ℝ → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (hprob_meas : Measurable successProb)
    (hsample_meas : Measurable sampleRate)
    (k : ℕ) :
    AEStronglyMeasurable
      (fun q : ℝ × ℝ =>
        twoSampleFloorPkObjectiveProb
          (realBinaryRatingLDPModel successProb hprob0 hprob1)
          sampleRate q.1 q.2 k) μ :=
  (realBinaryRatingLDPModel_twoSampleFloorPkObjectiveProb_measurable
    successProb sampleRate hprob0 hprob1 hprob_meas hsample_meas k).aestronglyMeasurable

/-- Derivative formula for a real-parameter binary finite-rating model. -/
theorem realBinaryRatingLDPModel_logMGF_hasDerivAt
    {θ : Type*} (successProb : θ → ℝ)
    (hprob0 : ∀ t, 0 ≤ successProb t)
    (hprob1 : ∀ t, successProb t ≤ 1)
    (θ0 : θ) (z : ℝ) :
    HasDerivAt
      (fun t : ℝ =>
        (realBinaryRatingLDPModel successProb hprob0 hprob1).logMGF θ0 t)
      (successProb θ0 * Real.exp z /
        ((1 - successProb θ0) + successProb θ0 * Real.exp z)) z := by
  simpa [realBinaryRatingLDPModel, FiniteRatingLDPModel.logMGF] using
    finiteLogMGF_realBernoulliPMF_binaryRatingScore_hasDerivAt
      (successProb θ0) z (hprob0 θ0) (hprob1 θ0)

/-- Interior inverse derivative formula for a real-parameter binary model. -/
theorem realBinaryRatingLDPModel_logMGF_hasDerivAt_inverse
    {θ : Type*} (successProb : θ → ℝ)
    (hprob0 : ∀ t, 0 ≤ successProb t)
    (hprob1 : ∀ t, successProb t ≤ 1)
    (hprob_pos : ∀ t, 0 < successProb t)
    (hprob_lt_one : ∀ t, successProb t < 1)
    (θ0 : θ) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    HasDerivAt
      (fun t : ℝ =>
        (realBinaryRatingLDPModel successProb hprob0 hprob1).logMGF θ0 t)
      a (binaryLogMGFDerivativeArg (successProb θ0) a) := by
  simpa [realBinaryRatingLDPModel, FiniteRatingLDPModel.logMGF] using
    finiteLogMGF_realBernoulliPMF_binaryRatingScore_hasDerivAt_inverse
      (successProb θ0) a (hprob_pos θ0) (hprob_lt_one θ0) ha0 ha1

/-- Interior binary model rate function equals Bernoulli KL. -/
theorem realBinaryRatingLDPModel_rateFunction_eq_bernoulliKL
    {θ : Type*} (successProb : θ → ℝ)
    (hprob0 : ∀ t, 0 ≤ successProb t)
    (hprob1 : ∀ t, successProb t ≤ 1)
    (hprob_pos : ∀ t, 0 < successProb t)
    (hprob_lt_one : ∀ t, successProb t < 1)
    (θ0 : θ) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    (realBinaryRatingLDPModel successProb hprob0 hprob1).rateFunction θ0 a =
      bernoulliKL a (successProb θ0) := by
  simpa [realBinaryRatingLDPModel, FiniteRatingLDPModel.rateFunction] using
    finiteRateFunction_realBernoulliPMF_binaryRatingScore_eq_bernoulliKL
      (hprob_pos θ0) (hprob_lt_one θ0) ha0 ha1

/-- Interior binary model extended rate function equals Bernoulli KL. -/
theorem realBinaryRatingLDPModel_rateFunctionTop_eq_bernoulliKL
    {θ : Type*} (successProb : θ → ℝ)
    (hprob0 : ∀ t, 0 ≤ successProb t)
    (hprob1 : ∀ t, successProb t ≤ 1)
    (hprob_pos : ∀ t, 0 < successProb t)
    (hprob_lt_one : ∀ t, successProb t < 1)
    (θ0 : θ) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    (realBinaryRatingLDPModel successProb hprob0 hprob1).rateFunctionTop θ0 a =
      (bernoulliKL a (successProb θ0) : WithTop ℝ) := by
  simpa [realBinaryRatingLDPModel, FiniteRatingLDPModel.rateFunctionTop] using
    finiteRateFunctionTop_realBernoulliPMF_binaryRatingScore_eq_bernoulliKL
      (hprob_pos θ0) (hprob_lt_one θ0) ha0 ha1

/--
For an interior threshold, the binary pairwise support-safe rate objective is
the weighted two-Bernoulli KL threshold rate.
-/
theorem realBinaryRatingLDPModel_pairwiseRateObjectiveTop_eq_twoBernoulliThresholdRate
    {θ : Type*} (successProb : θ → ℝ)
    (hprob0 : ∀ t, 0 ≤ successProb t)
    (hprob1 : ∀ t, successProb t ≤ 1)
    (hprob_pos : ∀ t, 0 < successProb t)
    (hprob_lt_one : ∀ t, successProb t < 1)
    (sampleRate : θ → ℝ) (hi lo : θ)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    (realBinaryRatingLDPModel successProb hprob0 hprob1).pairwiseRateObjectiveTop
        sampleRate hi lo a =
      (twoBernoulliThresholdRate (sampleRate hi) (sampleRate lo)
        (successProb hi) (successProb lo) a : WithTop ℝ) := by
  rw [FiniteRatingLDPModel.pairwiseRateObjectiveTop,
    realBinaryRatingLDPModel_rateFunctionTop_eq_bernoulliKL
      successProb hprob0 hprob1 hprob_pos hprob_lt_one hi ha0 ha1,
    realBinaryRatingLDPModel_rateFunctionTop_eq_bernoulliKL
      successProb hprob0 hprob1 hprob_pos hprob_lt_one lo ha0 ha1]
  simp [withTopRealScale, twoBernoulliThresholdRate]

/--
For two interior Bernoulli types, the support-safe pairwise threshold rate of
the binary finite-rating model is the closed weighted two-Bernoulli rate.
-/
theorem realBinaryRatingLDPModel_pairwiseSellerThresholdRateTop_eq_weightedClosedThresholdRate
    {θ : Type*} (successProb : θ → ℝ)
    (hprob0 : ∀ t, 0 ≤ successProb t)
    (hprob1 : ∀ t, successProb t ≤ 1)
    (hprob_pos : ∀ t, 0 < successProb t)
    (hprob_lt_one : ∀ t, successProb t < 1)
    (sampleRate : θ → ℝ) (hi lo : θ)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo)
    (hG : sampleRate hi + sampleRate lo ≠ 0) :
    pairwiseSellerThresholdRateTop
        (realBinaryRatingLDPModel successProb hprob0 hprob1)
        sampleRate hi lo =
      (weightedBernoulliClosedThresholdRate
        (sampleRate hi) (sampleRate lo)
        (successProb hi) (successProb lo) : WithTop ℝ) := by
  let M := realBinaryRatingLDPModel successProb hprob0 hprob1
  let a : ℝ :=
    weightedBernoulliCommonThreshold
      (sampleRate hi) (sampleRate lo) (successProb hi) (successProb lo)
  let z : ℝ :=
    sampleRate hi * binaryLogMGFDerivativeArg (successProb hi) a
  have ha0 : 0 < a := by
    dsimp [a]
    exact
      weightedBernoulliCommonThreshold_pos
        (hprob_pos hi) (hprob_lt_one hi)
        (hprob_pos lo) (hprob_lt_one lo)
  have ha1 : a < 1 := by
    dsimp [a]
    exact
      weightedBernoulliCommonThreshold_lt_one
        (hprob_pos hi) (hprob_lt_one hi)
        (hprob_pos lo) (hprob_lt_one lo)
  have hdual :
      sampleRate hi * binaryLogMGFDerivativeArg (successProb hi) a =
        -(sampleRate lo * binaryLogMGFDerivativeArg (successProb lo) a) := by
    dsimp [a]
    exact
      weightedBernoulliCommonThreshold_dual_balance
        hG (hprob_pos hi) (hprob_lt_one hi)
        (hprob_pos lo) (hprob_lt_one lo)
  have hderiv_hi :
      HasDerivAt (fun t : ℝ => M.logMGF hi t) a
        (z * (sampleRate hi)⁻¹) := by
    have hz_hi :
        z * (sampleRate hi)⁻¹ =
          binaryLogMGFDerivativeArg (successProb hi) a := by
      dsimp [z]
      field_simp [ne_of_gt hgHi]
    simpa [M, hz_hi] using
      realBinaryRatingLDPModel_logMGF_hasDerivAt_inverse
        successProb hprob0 hprob1 hprob_pos hprob_lt_one hi ha0 ha1
  have hderiv_lo :
      HasDerivAt (fun t : ℝ => M.logMGF lo t) a
        (-(z * (sampleRate lo)⁻¹)) := by
    have hz_lo :
        -(z * (sampleRate lo)⁻¹) =
          binaryLogMGFDerivativeArg (successProb lo) a := by
      dsimp [z]
      rw [hdual]
      field_simp [ne_of_gt hgLo]
    simpa [M, hz_lo] using
      realBinaryRatingLDPModel_logMGF_hasDerivAt_inverse
        successProb hprob0 hprob1 hprob_pos hprob_lt_one lo ha0 ha1
  have hthreshold :
      pairwiseSellerThresholdRateTop M sampleRate hi lo =
        (M.pairwiseRateObjective sampleRate hi lo a : WithTop ℝ) :=
    pairwiseSellerThresholdRateTop_eq_coe_pairwiseRateObjective_of_common_logMGF_derivatives
      M sampleRate hi lo hgHi hgLo a z hderiv_hi hderiv_lo
  have hobjective :
      M.pairwiseRateObjective sampleRate hi lo a =
        weightedBernoulliClosedThresholdRate
          (sampleRate hi) (sampleRate lo)
          (successProb hi) (successProb lo) := by
    rw [FiniteRatingLDPModel.pairwiseRateObjective,
      realBinaryRatingLDPModel_rateFunction_eq_bernoulliKL
        successProb hprob0 hprob1 hprob_pos hprob_lt_one hi ha0 ha1,
      realBinaryRatingLDPModel_rateFunction_eq_bernoulliKL
        successProb hprob0 hprob1 hprob_pos hprob_lt_one lo ha0 ha1]
    dsimp [a]
    exact
      twoBernoulliThresholdRate_weightedCommonThreshold_eq_closed
        hG (hprob_pos hi) (hprob_lt_one hi)
        (hprob_pos lo) (hprob_lt_one lo)
  simpa [M, hobjective] using hthreshold

/--
The closed two-Bernoulli threshold exponent is no larger than the endpoint
success exponent for the lower-probability population. Equivalently, when a
comparison against the source endpoint `1` has rate `gLo * (-log pLo)`, the
interior adjacent comparison ending at any `pHi ≥ pLo` is a valid dominating
candidate.
-/
theorem weightedBernoulliClosedThresholdRate_le_low_success_endpoint
    {gHi gLo pHi pLo : ℝ}
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hpHi0 : 0 < pHi) (hpHi1 : pHi < 1)
    (hpLo0 : 0 < pLo) (hpLo1 : pLo < 1)
    (hpLo_le_hi : pLo ≤ pHi) :
    weightedBernoulliClosedThresholdRate gHi gLo pHi pLo ≤
      gLo * (-Real.log pLo) := by
  let successProb : Bool → ℝ := fun b => if b then pHi else pLo
  let sampleRate : Bool → ℝ := fun b => if b then gHi else gLo
  let M := realBinaryRatingLDPModel successProb
    (by
      intro b
      cases b <;> simp [successProb, hpHi0.le, hpLo0.le])
    (by
      intro b
      cases b <;> simp [successProb, hpHi1.le, hpLo1.le])
  have hprob0 : ∀ b, 0 ≤ successProb b := by
    intro b
    cases b <;> simp [successProb, hpHi0.le, hpLo0.le]
  have hprob1 : ∀ b, successProb b ≤ 1 := by
    intro b
    cases b <;> simp [successProb, hpHi1.le, hpLo1.le]
  have hprob_pos : ∀ b, 0 < successProb b := by
    intro b
    cases b <;> simp [successProb, hpHi0, hpLo0]
  have hprob_lt_one : ∀ b, successProb b < 1 := by
    intro b
    cases b <;> simp [successProb, hpHi1, hpLo1]
  have hthreshold_eq :
      M.pairwiseThresholdRateTop sampleRate true false =
        (weightedBernoulliClosedThresholdRate gHi gLo pHi pLo : WithTop ℝ) := by
    have h :=
      realBinaryRatingLDPModel_pairwiseSellerThresholdRateTop_eq_weightedClosedThresholdRate
        successProb hprob0 hprob1 hprob_pos hprob_lt_one sampleRate
        true false hgHi hgLo (ne_of_gt (add_pos hgHi hgLo))
    simpa [M, successProb, sampleRate, pairwiseSellerThresholdRateTop] using h
  have hpoint :
      M.pairwiseThresholdRateTop sampleRate true false ≤
        M.pairwiseRateObjectiveTop sampleRate true false pHi :=
    M.pairwiseThresholdRateTop_le_pairwiseRateObjectiveTop
      sampleRate true false pHi hgHi.le hgLo.le
  have hobjective_eq :
      M.pairwiseRateObjectiveTop sampleRate true false pHi =
        (twoBernoulliThresholdRate gHi gLo pHi pLo pHi : WithTop ℝ) := by
    simpa [M, successProb, sampleRate] using
      realBinaryRatingLDPModel_pairwiseRateObjectiveTop_eq_twoBernoulliThresholdRate
        successProb hprob0 hprob1 hprob_pos hprob_lt_one sampleRate
        true false hpHi0 hpHi1
  have hthreshold_le_objective :
      (weightedBernoulliClosedThresholdRate gHi gLo pHi pLo : WithTop ℝ) ≤
        (twoBernoulliThresholdRate gHi gLo pHi pLo pHi : WithTop ℝ) := by
    calc
      (weightedBernoulliClosedThresholdRate gHi gLo pHi pLo : WithTop ℝ)
          = M.pairwiseThresholdRateTop sampleRate true false := hthreshold_eq.symm
      _ ≤ M.pairwiseRateObjectiveTop sampleRate true false pHi := hpoint
      _ = (twoBernoulliThresholdRate gHi gLo pHi pLo pHi : WithTop ℝ) :=
          hobjective_eq
  have hkl_le : bernoulliKL pHi pLo ≤ -Real.log pLo :=
    bernoulliKL_le_neg_log_of_le hpLo0 hpHi1 hpLo_le_hi
  have hobjective_real_le :
      twoBernoulliThresholdRate gHi gLo pHi pLo pHi ≤
        gLo * (-Real.log pLo) := by
    have hmul :
        gLo * bernoulliKL pHi pLo ≤ gLo * (-Real.log pLo) :=
      mul_le_mul_of_nonneg_left hkl_le hgLo.le
    unfold twoBernoulliThresholdRate
    rw [bernoulliKL_self hpHi0 hpHi1]
    linarith
  have hobjective_top_le :
      (twoBernoulliThresholdRate gHi gLo pHi pLo pHi : WithTop ℝ) ≤
        (gLo * (-Real.log pLo) : WithTop ℝ) := by
    exact_mod_cast hobjective_real_le
  have hclosed_top_le :
      (weightedBernoulliClosedThresholdRate gHi gLo pHi pLo : WithTop ℝ) ≤
        (gLo * (-Real.log pLo) : WithTop ℝ) :=
    hthreshold_le_objective.trans hobjective_top_le
  exact_mod_cast hclosed_top_le

/--
The closed Bernoulli threshold exponent is monotone in the two sample weights:
increasing either population's sample rate cannot decrease the pairwise
large-deviation exponent.
-/
theorem weightedBernoulliClosedThresholdRate_le_of_weights_le
    {gHi gLo gHi' gLo' pHi pLo : ℝ}
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hgHi' : 0 < gHi') (hgLo' : 0 < gLo')
    (hhi_le : gHi ≤ gHi') (hlo_le : gLo ≤ gLo')
    (hpHi0 : 0 < pHi) (hpHi1 : pHi < 1)
    (hpLo0 : 0 < pLo) (hpLo1 : pLo < 1) :
    weightedBernoulliClosedThresholdRate gHi gLo pHi pLo ≤
      weightedBernoulliClosedThresholdRate gHi' gLo' pHi pLo := by
  let successProb : Bool → ℝ := fun b => if b then pHi else pLo
  let sampleRate : Bool → ℝ := fun b => if b then gHi else gLo
  let sampleRate' : Bool → ℝ := fun b => if b then gHi' else gLo'
  let M := realBinaryRatingLDPModel successProb
    (by
      intro b
      cases b <;> simp [successProb, hpHi0.le, hpLo0.le])
    (by
      intro b
      cases b <;> simp [successProb, hpHi1.le, hpLo1.le])
  have hprob0 : ∀ b, 0 ≤ successProb b := by
    intro b
    cases b <;> simp [successProb, hpHi0.le, hpLo0.le]
  have hprob1 : ∀ b, successProb b ≤ 1 := by
    intro b
    cases b <;> simp [successProb, hpHi1.le, hpLo1.le]
  have hprob_pos : ∀ b, 0 < successProb b := by
    intro b
    cases b <;> simp [successProb, hpHi0, hpLo0]
  have hprob_lt_one : ∀ b, successProb b < 1 := by
    intro b
    cases b <;> simp [successProb, hpHi1, hpLo1]
  have htop_le_method :
      M.pairwiseThresholdRateTop sampleRate true false ≤
        M.pairwiseThresholdRateTop sampleRate' true false := by
    exact
      M.pairwiseThresholdRateTop_le_of_sampleRate_le
        (sampleRate := sampleRate) (sampleRate' := sampleRate')
        true false
        (by simp [sampleRate, hgHi.le])
        (by simp [sampleRate, hgLo.le])
        (by simpa [sampleRate, sampleRate'] using hhi_le)
        (by simpa [sampleRate, sampleRate'] using hlo_le)
  have htop_le :
      pairwiseSellerThresholdRateTop M sampleRate true false ≤
        pairwiseSellerThresholdRateTop M sampleRate' true false := by
    simpa [pairwiseSellerThresholdRateTop] using htop_le_method
  have hleft_eq :
      pairwiseSellerThresholdRateTop M sampleRate true false =
        (weightedBernoulliClosedThresholdRate gHi gLo pHi pLo : WithTop ℝ) := by
    simpa [M, successProb, sampleRate] using
      realBinaryRatingLDPModel_pairwiseSellerThresholdRateTop_eq_weightedClosedThresholdRate
        successProb hprob0 hprob1 hprob_pos hprob_lt_one
        sampleRate true false hgHi hgLo
        (ne_of_gt (add_pos hgHi hgLo))
  have hright_eq :
      pairwiseSellerThresholdRateTop M sampleRate' true false =
        (weightedBernoulliClosedThresholdRate gHi' gLo' pHi pLo : WithTop ℝ) := by
    simpa [M, successProb, sampleRate'] using
      realBinaryRatingLDPModel_pairwiseSellerThresholdRateTop_eq_weightedClosedThresholdRate
        successProb hprob0 hprob1 hprob_pos hprob_lt_one
        sampleRate' true false hgHi' hgLo'
        (ne_of_gt (add_pos hgHi' hgLo'))
  have hcoe :
      (weightedBernoulliClosedThresholdRate gHi gLo pHi pLo : WithTop ℝ) ≤
      (weightedBernoulliClosedThresholdRate gHi' gLo' pHi pLo : WithTop ℝ) := by
    simpa [hleft_eq, hright_eq] using htop_le
  exact WithTop.coe_le_coe.mp hcoe

/--
Adjacent-dominance for an ordered Bernoulli chain: if sample rates and success
levels are monotone, then the adjacent comparison `(i, i+1)` has no larger
closed threshold exponent than any wider comparison `(i, j)` with `i+1 ≤ j`.
-/
theorem weightedBernoulliClosedThresholdRate_adjacent_le_nonadjacent_of_monotone
    {g p : ℕ → ℝ} {i j : ℕ}
    (hg_pos : ∀ n, 0 < g n)
    (hg_mono : Monotone g)
    (hp_mono : Monotone p)
    (hi_pos : 0 < p i)
    (hj_lt_one : p j < 1)
    (hij : i + 1 ≤ j) :
    weightedBernoulliClosedThresholdRate (g (i + 1)) (g i)
        (p (i + 1)) (p i) ≤
      weightedBernoulliClosedThresholdRate (g j) (g i) (p j) (p i) := by
  have hg_adj_le_j : g (i + 1) ≤ g j := hg_mono hij
  have hp_i_le_adj : p i ≤ p (i + 1) := hp_mono (Nat.le_succ i)
  have hp_adj_le_j : p (i + 1) ≤ p j := hp_mono hij
  have hp_adj_pos : 0 < p (i + 1) := hi_pos.trans_le hp_i_le_adj
  have hp_i_lt_one : p i < 1 :=
    lt_of_le_of_lt (hp_i_le_adj.trans hp_adj_le_j) hj_lt_one
  have hp_adj_lt_one : p (i + 1) < 1 :=
    lt_of_le_of_lt hp_adj_le_j hj_lt_one
  have hweight :
      weightedBernoulliClosedThresholdRate (g (i + 1)) (g i)
          (p (i + 1)) (p i) ≤
        weightedBernoulliClosedThresholdRate (g j) (g i)
          (p (i + 1)) (p i) :=
    weightedBernoulliClosedThresholdRate_le_of_weights_le
      (hg_pos (i + 1)) (hg_pos i) (hg_pos j) (hg_pos i)
      hg_adj_le_j le_rfl hp_adj_pos hp_adj_lt_one hi_pos hp_i_lt_one
  have hshrink :
      weightedBernoulliClosedThresholdRate (g j) (g i)
          (p (i + 1)) (p i) ≤
        weightedBernoulliClosedThresholdRate (g j) (g i)
          (p j) (p i) :=
    weightedBernoulliClosedThresholdRate_le_of_shrink
      (le_of_lt (hg_pos j)) (le_of_lt (hg_pos i))
      (add_pos (hg_pos j) (hg_pos i))
      hi_pos le_rfl hp_i_le_adj hp_adj_le_j hj_lt_one
  exact hweight.trans hshrink

/-- Bernoulli law has full binary support for interior success probabilities. -/
theorem realBernoulliPMF_fullSupport_of_pos_lt_one
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∀ b : Bool, 0 < (realBernoulliPMF p hp0.le hp1.le b).toReal := by
  intro b
  cases b <;> simp <;> linarith

/--
Interior binary success probabilities give full support for the corresponding
finite-rating model.
-/
theorem realBinaryRatingLDPModel_fullSupport_of_pos_lt_one
    {θ : Type*} (successProb : θ → ℝ)
    (hprob0 : ∀ t, 0 ≤ successProb t)
    (hprob1 : ∀ t, successProb t ≤ 1)
    (hprob_pos : ∀ t, 0 < successProb t)
    (hprob_lt_one : ∀ t, successProb t < 1) :
    (realBinaryRatingLDPModel successProb hprob0 hprob1).fullSupport := by
  intro t b
  exact
    realBernoulliPMF_fullSupport_of_pos_lt_one
      (successProb t) (hprob_pos t) (hprob_lt_one t) b

/--
For two binary-rating populations whose failure atom has positive mass, the
fixed-count paper complement error `1 - P_k` is strictly positive.  The all
failure sample is a positive-mass tie event.
-/
theorem realBinaryRatingLDPModel_twoSamplePkComplementErrorProb_pos_of_lt_one
    {θ : Type*} (successProb : θ → ℝ)
    (hprob0 : ∀ t, 0 ≤ successProb t)
    (hprob1 : ∀ t, successProb t ≤ 1)
    (hi lo : θ) (nHi nLo : ℕ) (cHi cLo : ℝ)
    (hpHi1 : successProb hi < 1) (hpLo1 : successProb lo < 1) :
    0 <
      twoSamplePkComplementErrorProb
        (realBinaryRatingLDPModel successProb hprob0 hprob1)
        hi lo nHi nLo cHi cLo := by
  classical
  let M := realBinaryRatingLDPModel successProb hprob0 hprob1
  have hmass_hi : 0 < (M.typeLaw hi false).toReal := by
    dsimp [M, realBinaryRatingLDPModel]
    simp [realBernoulliPMF_apply_false_toReal]
    linarith
  have hmass_lo : 0 < (M.typeLaw lo false).toReal := by
    dsimp [M, realBinaryRatingLDPModel]
    simp [realBernoulliPMF_apply_false_toReal]
    linarith
  exact
    twoSamplePkComplementErrorProb_pos_of_zero_score_atoms
      M hi lo nHi nLo cHi cLo false false hmass_hi hmass_lo
      (by simp [M, realBinaryRatingLDPModel, binaryRatingScore])
      (by simp [M, realBinaryRatingLDPModel, binaryRatingScore])

/--
Floor-count specialization of
`realBinaryRatingLDPModel_twoSamplePkComplementErrorProb_pos_of_lt_one`.
-/
theorem realBinaryRatingLDPModel_floorPkComplementErrorProb_pos_of_lt_one
    {θ : Type*} (successProb : θ → ℝ)
    (hprob0 : ∀ t, 0 ≤ successProb t)
    (hprob1 : ∀ t, successProb t ≤ 1)
    (sampleRate : θ → ℝ) (hi lo : θ) (k : ℕ)
    (hpHi1 : successProb hi < 1) (hpLo1 : successProb lo < 1) :
    0 <
      twoSampleFloorPkComplementErrorProb
        (realBinaryRatingLDPModel successProb hprob0 hprob1)
        sampleRate hi lo k := by
  unfold twoSampleFloorPkComplementErrorProb
  exact
    realBinaryRatingLDPModel_twoSamplePkComplementErrorProb_pos_of_lt_one
      successProb hprob0 hprob1 hi lo
      (floorSampleCount sampleRate hi k)
      (floorSampleCount sampleRate lo k)
      (((floorSampleCount sampleRate hi k : ℕ) : ℝ)⁻¹)
      (((floorSampleCount sampleRate lo k : ℕ) : ℝ)⁻¹)
      hpHi1 hpLo1

/--
Floor-count binary left-tail score-gap probability is positive when both
Bernoulli laws put positive mass on failure.
-/
theorem realBinaryRatingLDPModel_floorScoreGapLeftTailProb_pos_of_lt_one
    {θ : Type*} (successProb : θ → ℝ)
    (hprob0 : ∀ t, 0 ≤ successProb t)
    (hprob1 : ∀ t, successProb t ≤ 1)
    (sampleRate : θ → ℝ) (hi lo : θ) (k : ℕ)
    (hpHi1 : successProb hi < 1) (hpLo1 : successProb lo < 1) :
    0 <
      twoSampleFloorScoreGapLeftTailProb
        (realBinaryRatingLDPModel successProb hprob0 hprob1)
        sampleRate hi lo k := by
  let M := realBinaryRatingLDPModel successProb hprob0 hprob1
  have hmass_hi : 0 < (M.typeLaw hi false).toReal := by
    dsimp [M, realBinaryRatingLDPModel]
    simp [realBernoulliPMF_apply_false_toReal]
    linarith
  have hmass_lo : 0 < (M.typeLaw lo false).toReal := by
    dsimp [M, realBinaryRatingLDPModel]
    simp [realBernoulliPMF_apply_false_toReal]
    linarith
  exact
    twoSampleFloorScoreGapLeftTailProb_pos_of_zero_score_atoms
      M sampleRate hi lo k false false hmass_hi hmass_lo
      (by simp [M, realBinaryRatingLDPModel, binaryRatingScore])
      (by simp [M, realBinaryRatingLDPModel, binaryRatingScore])

/--
If both compared Bernoulli laws put positive mass on success and both sample
rates are positive, the floor-count paper complement error is eventually
positive. This covers endpoint comparisons to a type with success probability
one, where the all-failure witness is unavailable.
-/
theorem realBinaryRatingLDPModel_floorPkComplementErrorProb_eventually_pos_of_pos
    {θ : Type*} (successProb : θ → ℝ)
    (hprob0 : ∀ t, 0 ≤ successProb t)
    (hprob1 : ∀ t, successProb t ≤ 1)
    (sampleRate : θ → ℝ) (hi lo : θ)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo)
    (hpHi0 : 0 < successProb hi) (hpLo0 : 0 < successProb lo) :
    ∀ᶠ k : ℕ in Filter.atTop,
      0 <
        twoSampleFloorPkComplementErrorProb
          (realBinaryRatingLDPModel successProb hprob0 hprob1)
          sampleRate hi lo k := by
  let M := realBinaryRatingLDPModel successProb hprob0 hprob1
  have hmass_hi : 0 < (M.typeLaw hi true).toReal := by
    dsimp [M, realBinaryRatingLDPModel]
    simpa using hpHi0
  have hmass_lo : 0 < (M.typeLaw lo true).toReal := by
    dsimp [M, realBinaryRatingLDPModel]
    simpa using hpLo0
  exact
    twoSampleFloorPkComplementErrorProb_eventually_pos_of_one_score_atoms
      M sampleRate hi lo hgHi hgLo true true hmass_hi hmass_lo
      (by simp [M, realBinaryRatingLDPModel, binaryRatingScore])
      (by simp [M, realBinaryRatingLDPModel, binaryRatingScore])

/--
For an interior threshold `a ∈ (0,1)`, a full-support binary rating law
straddles the threshold.
-/
theorem realBinaryRatingLDPModel_straddlesThreshold_of_threshold_mem_Ioo
    {θ : Type*} (successProb : θ → ℝ)
    (hprob0 : ∀ t, 0 ≤ successProb t)
    (hprob1 : ∀ t, successProb t ≤ 1)
    (hprob_pos : ∀ t, 0 < successProb t)
    (hprob_lt_one : ∀ t, successProb t < 1)
    (t : θ) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    (realBinaryRatingLDPModel successProb hprob0 hprob1).straddlesThreshold t a := by
  constructor
  · refine ⟨false, ?_, ?_⟩
    · exact
        realBernoulliPMF_fullSupport_of_pos_lt_one
          (successProb t) (hprob_pos t) (hprob_lt_one t) false
    · simpa [realBinaryRatingLDPModel, binaryRatingScore] using ha0
  · refine ⟨true, ?_, ?_⟩
    · exact
        realBernoulliPMF_fullSupport_of_pos_lt_one
          (successProb t) (hprob_pos t) (hprob_lt_one t) true
    · simpa [realBinaryRatingLDPModel, binaryRatingScore] using ha1

/--
Pairwise threshold-rate LDP certificates for a real-parameter binary rating
model from common log-MGF derivative witnesses.  The binary support and
bottom/top score hypotheses are discharged internally.
-/
def realBinaryRating_pairwiseThresholdRateTopLdpCertificate_of_common_logMGF_derivatives
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
            (realBinaryRatingLDPModel successProb hprob0 hprob1).logMGF
              (pairHi p) t)
          (a p) (z p * (sampleRate (pairHi p))⁻¹))
    (hderiv_lo :
      ∀ p : Pair,
        HasDerivAt
          (fun t : ℝ =>
            (realBinaryRatingLDPModel successProb hprob0 hprob1).logMGF
              (pairLo p) t)
          (a p) (-(z p * (sampleRate (pairLo p))⁻¹))) :
    PairwiseThresholdRateTopLdpCertificate
      (realBinaryRatingLDPModel successProb hprob0 hprob1)
      sampleRate pairHi pairLo := by
  let M := realBinaryRatingLDPModel successProb hprob0 hprob1
  refine
    PairwiseThresholdRateTopLdpCertificate.of_common_logMGF_derivatives_and_score_bounds
      M sampleRate pairHi pairLo hpositive_hi hpositive_lo
      a z hz ?_ ?_ false true ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro p
    simpa [M] using hderiv_hi p
  · intro p
    simpa [M] using hderiv_lo p
  · intro p
    exact
      realBernoulliPMF_fullSupport_of_pos_lt_one
        (successProb (pairHi p)) (hprob_pos (pairHi p))
        (hprob_lt_one (pairHi p)) false
  · intro p
    exact
      realBernoulliPMF_fullSupport_of_pos_lt_one
        (successProb (pairHi p)) (hprob_pos (pairHi p))
        (hprob_lt_one (pairHi p)) true
  · intro p
    exact
      realBernoulliPMF_fullSupport_of_pos_lt_one
        (successProb (pairLo p)) (hprob_pos (pairLo p))
        (hprob_lt_one (pairLo p)) false
  · intro p
    exact
      realBernoulliPMF_fullSupport_of_pos_lt_one
        (successProb (pairLo p)) (hprob_pos (pairLo p))
        (hprob_lt_one (pairLo p)) true
  · intro r
    cases r <;> simp [M, realBinaryRatingLDPModel, binaryRatingScore]
  · intro r
    cases r <;> simp [M, realBinaryRatingLDPModel, binaryRatingScore]
  · simp [M, realBinaryRatingLDPModel, binaryRatingScore]

/--
Pairwise threshold-rate LDP certificates for a real-parameter binary rating
model from explicit Bernoulli log-MGF derivative equations. This is the
paper-facing algebraic form of the common-threshold condition.
-/
def realBinaryRating_pairwiseThresholdRateTopLdpCertificate_of_derivative_formula
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
      (realBinaryRatingLDPModel successProb hprob0 hprob1)
      sampleRate pairHi pairLo :=
  realBinaryRating_pairwiseThresholdRateTopLdpCertificate_of_common_logMGF_derivatives
    successProb hprob0 hprob1 hprob_pos hprob_lt_one
    sampleRate pairHi pairLo hpositive_hi hpositive_lo
    a z hz
    (fun p => by
      simpa [hcommon_hi p] using
        realBinaryRatingLDPModel_logMGF_hasDerivAt
          successProb hprob0 hprob1 (pairHi p)
          (z p * (sampleRate (pairHi p))⁻¹))
    (fun p => by
      simpa [hcommon_lo p] using
        realBinaryRatingLDPModel_logMGF_hasDerivAt
          successProb hprob0 hprob1 (pairLo p)
          (-(z p * (sampleRate (pairLo p))⁻¹)))

/--
Pairwise threshold-rate LDP certificates for a real-parameter binary rating
model from a common interior threshold and the weighted common-dual equation.
This packages the stationarity algebra used by binary-rating papers.
-/
def realBinaryRating_pairwiseThresholdRateTopLdpCertificate_of_common_threshold_inverse
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
      (realBinaryRatingLDPModel successProb hprob0 hprob1)
      sampleRate pairHi pairLo := by
  let z : Pair → ℝ := fun p =>
    sampleRate (pairHi p) *
      binaryLogMGFDerivativeArg (successProb (pairHi p)) (a p)
  refine
    realBinaryRating_pairwiseThresholdRateTopLdpCertificate_of_common_logMGF_derivatives
      successProb hprob0 hprob1 hprob_pos hprob_lt_one
      sampleRate pairHi pairLo hpositive_hi hpositive_lo
      a z hdual_nonpos ?_ ?_
  · intro p
    have hz_hi :
        z p * (sampleRate (pairHi p))⁻¹ =
          binaryLogMGFDerivativeArg (successProb (pairHi p)) (a p) := by
      dsimp [z]
      field_simp [ne_of_gt (hpositive_hi p)]
    simpa [hz_hi] using
      realBinaryRatingLDPModel_logMGF_hasDerivAt_inverse
        successProb hprob0 hprob1 hprob_pos hprob_lt_one
        (pairHi p) (ha0 p) (ha1 p)
  · intro p
    have hz_lo :
        -(z p * (sampleRate (pairLo p))⁻¹) =
          binaryLogMGFDerivativeArg (successProb (pairLo p)) (a p) := by
      dsimp [z]
      rw [hdual_eq p]
      field_simp [ne_of_gt (hpositive_lo p)]
    simpa [hz_lo] using
      realBinaryRatingLDPModel_logMGF_hasDerivAt_inverse
        successProb hprob0 hprob1 hprob_pos hprob_lt_one
        (pairLo p) (ha0 p) (ha1 p)

/--
Pairwise binary threshold-rate LDP certificates from a common interior
threshold and weighted common-dual equation, with the high-side dual sign
derived from the natural order condition `a ≤ p_hi`.
-/
def realBinaryRating_pairwiseThresholdRateTopLdpCertificate_of_ordered_common_threshold_inverse
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
      (realBinaryRatingLDPModel successProb hprob0 hprob1)
      sampleRate pairHi pairLo :=
  realBinaryRating_pairwiseThresholdRateTopLdpCertificate_of_common_threshold_inverse
    successProb hprob0 hprob1 hprob_pos hprob_lt_one
    sampleRate pairHi pairLo hpositive_hi hpositive_lo
    a ha0 ha1
    (fun p =>
      mul_nonpos_of_nonneg_of_nonpos
        (hpositive_hi p).le
        (binaryLogMGFDerivativeArg_nonpos_of_le
          (hprob_pos (pairHi p)) (hprob_lt_one (pairHi p))
          (ha0 p) (ha1 p) (ha_le_hi p)))
    hdual_eq

/--
Pairwise binary threshold-rate LDP certificates from the weighted geometric
common threshold. The dual equation and threshold interior facts are discharged
internally; callers provide the natural high-side order condition that ensures
the left-tail Chernoff dual has the correct sign.
-/
def realBinaryRating_pairwiseThresholdRateTopLdpCertificate_of_weighted_common_threshold
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
      (realBinaryRatingLDPModel successProb hprob0 hprob1)
      sampleRate pairHi pairLo :=
  realBinaryRating_pairwiseThresholdRateTopLdpCertificate_of_ordered_common_threshold_inverse
    successProb hprob0 hprob1 hprob_pos hprob_lt_one
    sampleRate pairHi pairLo hpositive_hi hpositive_lo
    (fun p =>
      weightedBernoulliCommonThreshold
        (sampleRate (pairHi p)) (sampleRate (pairLo p))
        (successProb (pairHi p)) (successProb (pairLo p)))
    (fun p =>
      weightedBernoulliCommonThreshold_pos
        (hprob_pos (pairHi p)) (hprob_lt_one (pairHi p))
        (hprob_pos (pairLo p)) (hprob_lt_one (pairLo p)))
    (fun p =>
      weightedBernoulliCommonThreshold_lt_one
        (hprob_pos (pairHi p)) (hprob_lt_one (pairHi p))
        (hprob_pos (pairLo p)) (hprob_lt_one (pairLo p)))
    ha_le_hi
    (fun p =>
      weightedBernoulliCommonThreshold_dual_balance
        (hG p)
        (hprob_pos (pairHi p)) (hprob_lt_one (pairHi p))
        (hprob_pos (pairLo p)) (hprob_lt_one (pairLo p)))

/--
Pair-local exact floor-count left-tail certificate for two interior Bernoulli
rating laws at the weighted geometric common threshold. Unlike the packaged
pairwise threshold certificate above, this theorem only assumes the two
compared types have interior success probabilities, so it can be combined with
endpoint comparisons in a larger finite level chain.
-/
theorem realBinaryRatingLDPModel_floorScoreGapLeftTail_exponentialRateCertificate_of_weighted_common_threshold_pair
    {Seller : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (sampleRate : Seller → ℝ) (hi lo : Seller)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo)
    (hpHi0 : 0 < successProb hi) (hpHi1 : successProb hi < 1)
    (hpLo0 : 0 < successProb lo) (hpLo1 : successProb lo < 1)
    (hpLo_le_hi : successProb lo ≤ successProb hi) :
    ExponentialRateCertificate
      (twoSampleFloorScoreGapLeftTailProb
        (realBinaryRatingLDPModel successProb hprob0 hprob1) sampleRate hi lo)
      (weightedBernoulliClosedThresholdRate
        (sampleRate hi) (sampleRate lo)
        (successProb hi) (successProb lo)) := by
  let M := realBinaryRatingLDPModel successProb hprob0 hprob1
  let a : ℝ :=
    weightedBernoulliCommonThreshold
      (sampleRate hi) (sampleRate lo) (successProb hi) (successProb lo)
  let z : ℝ :=
    sampleRate hi * binaryLogMGFDerivativeArg (successProb hi) a
  have hGpos : 0 < sampleRate hi + sampleRate lo :=
    add_pos hgHi hgLo
  have hG : sampleRate hi + sampleRate lo ≠ 0 :=
    ne_of_gt hGpos
  have ha0 : 0 < a := by
    dsimp [a]
    exact weightedBernoulliCommonThreshold_pos hpHi0 hpHi1 hpLo0 hpLo1
  have ha1 : a < 1 := by
    dsimp [a]
    exact weightedBernoulliCommonThreshold_lt_one hpHi0 hpHi1 hpLo0 hpLo1
  have ha_le_hi : a ≤ successProb hi := by
    dsimp [a]
    exact
      weightedBernoulliCommonThreshold_le_hi_of_le
        hgHi.le hgLo.le hGpos hpHi0 hpHi1 hpLo0 hpLo1 hpLo_le_hi
  have hdual :
      sampleRate hi * binaryLogMGFDerivativeArg (successProb hi) a =
        -(sampleRate lo * binaryLogMGFDerivativeArg (successProb lo) a) := by
    dsimp [a]
    exact
      weightedBernoulliCommonThreshold_dual_balance
        hG hpHi0 hpHi1 hpLo0 hpLo1
  have hz : z ≤ 0 := by
    dsimp [z]
    exact
      mul_nonpos_of_nonneg_of_nonpos hgHi.le
        (binaryLogMGFDerivativeArg_nonpos_of_le
          hpHi0 hpHi1 ha0 ha1 ha_le_hi)
  have hderiv_hi :
      HasDerivAt (fun t : ℝ => M.logMGF hi t) a
        (z * (sampleRate hi)⁻¹) := by
    have hz_hi :
        z * (sampleRate hi)⁻¹ =
          binaryLogMGFDerivativeArg (successProb hi) a := by
      dsimp [z]
      field_simp [ne_of_gt hgHi]
    simpa [M, realBinaryRatingLDPModel, FiniteRatingLDPModel.logMGF,
      hz_hi] using
      finiteLogMGF_realBernoulliPMF_binaryRatingScore_hasDerivAt_inverse
        (successProb hi) a hpHi0 hpHi1 ha0 ha1
  have hderiv_lo :
      HasDerivAt (fun t : ℝ => M.logMGF lo t) a
        (-(z * (sampleRate lo)⁻¹)) := by
    have hz_lo :
        -(z * (sampleRate lo)⁻¹) =
          binaryLogMGFDerivativeArg (successProb lo) a := by
      dsimp [z]
      rw [hdual]
      field_simp [ne_of_gt hgLo]
    simpa [M, realBinaryRatingLDPModel, FiniteRatingLDPModel.logMGF,
      hz_lo] using
      finiteLogMGF_realBernoulliPMF_binaryRatingScore_hasDerivAt_inverse
        (successProb lo) a hpLo0 hpLo1 ha0 ha1
  have hstraddle_hi : ratingLawStraddlesThreshold M hi a := by
    constructor
    · refine ⟨false, ?_, ?_⟩
      · simpa [M, realBinaryRatingLDPModel] using
          realBernoulliPMF_fullSupport_of_pos_lt_one
            (successProb hi) hpHi0 hpHi1 false
      · simpa [M, realBinaryRatingLDPModel, binaryRatingScore] using ha0
    · refine ⟨true, ?_, ?_⟩
      · simpa [M, realBinaryRatingLDPModel] using
          realBernoulliPMF_fullSupport_of_pos_lt_one
            (successProb hi) hpHi0 hpHi1 true
      · simpa [M, realBinaryRatingLDPModel, binaryRatingScore] using ha1
  have hstraddle_lo : ratingLawStraddlesThreshold M lo a := by
    constructor
    · refine ⟨false, ?_, ?_⟩
      · simpa [M, realBinaryRatingLDPModel] using
          realBernoulliPMF_fullSupport_of_pos_lt_one
            (successProb lo) hpLo0 hpLo1 false
      · simpa [M, realBinaryRatingLDPModel, binaryRatingScore] using ha0
    · refine ⟨true, ?_, ?_⟩
      · simpa [M, realBinaryRatingLDPModel] using
          realBernoulliPMF_fullSupport_of_pos_lt_one
            (successProb lo) hpLo0 hpLo1 true
      · simpa [M, realBinaryRatingLDPModel, binaryRatingScore] using ha1
  have hobjective :
      M.pairwiseRateObjective sampleRate hi lo a =
        weightedBernoulliClosedThresholdRate
          (sampleRate hi) (sampleRate lo)
          (successProb hi) (successProb lo) := by
    have hrate_hi :
        M.rateFunction hi a = bernoulliKL a (successProb hi) := by
      simpa [M, realBinaryRatingLDPModel, FiniteRatingLDPModel.rateFunction] using
        finiteRateFunction_realBernoulliPMF_binaryRatingScore_eq_bernoulliKL
          hpHi0 hpHi1 ha0 ha1
    have hrate_lo :
        M.rateFunction lo a = bernoulliKL a (successProb lo) := by
      simpa [M, realBinaryRatingLDPModel, FiniteRatingLDPModel.rateFunction] using
        finiteRateFunction_realBernoulliPMF_binaryRatingScore_eq_bernoulliKL
          hpLo0 hpLo1 ha0 ha1
    rw [FiniteRatingLDPModel.pairwiseRateObjective, hrate_hi, hrate_lo]
    dsimp [a]
    exact
      twoBernoulliThresholdRate_weightedCommonThreshold_eq_closed
        hG hpHi0 hpHi1 hpLo0 hpLo1
  have hcert :
      ExponentialRateCertificate
        (twoSampleFloorScoreGapLeftTailProb M sampleRate hi lo)
        (M.pairwiseRateObjective sampleRate hi lo a) :=
    twoSampleFloorScoreGapLeftTail_pairwiseObjective_exponentialRateCertificate_of_logMGF_derivative_minimizer_of_straddling_support
      M sampleRate hi lo hgHi hgLo a z hz hderiv_hi hderiv_lo
      hstraddle_hi hstraddle_lo
  simpa [M, hobjective] using hcert

/--
Uniform normalized-log certificate for compact families of interior binary
left-tail score-gap kernels.  The binary library supplies pointwise Cramer
certificates and positivity; the caller supplies the compact-family
regularity of the normalized log-kernels.
-/
def realBinaryRatingLDPModel_floorScoreGapLeftTail_uniformNormalizedLogRateCertificateOn_of_eventually_lipschitz_on_compact
    {Seller α : Type*} [PseudoMetricSpace α]
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (sampleRate : Seller → ℝ)
    (pairHi pairLo : α → Seller)
    {s K : Set α}
    (hKcompact : IsCompact K) (hsub : s ⊆ K)
    (hsample_hi_pos :
      ∀ x : α, x ∈ K → 0 < sampleRate (pairHi x))
    (hsample_lo_pos :
      ∀ x : α, x ∈ K → 0 < sampleRate (pairLo x))
    (hprob_hi_pos :
      ∀ x : α, x ∈ K → 0 < successProb (pairHi x))
    (hprob_hi_lt_one :
      ∀ x : α, x ∈ K → successProb (pairHi x) < 1)
    (hprob_lo_pos :
      ∀ x : α, x ∈ K → 0 < successProb (pairLo x))
    (hprob_lo_lt_one :
      ∀ x : α, x ∈ K → successProb (pairLo x) < 1)
    (hprob_order :
      ∀ x : α, x ∈ K →
        successProb (pairLo x) ≤ successProb (pairHi x))
    (hrate_cont :
      ∀ x : α, x ∈ K →
        ContinuousAt
          (fun y : α =>
            weightedBernoulliClosedThresholdRate
              (sampleRate (pairHi y)) (sampleRate (pairLo y))
              (successProb (pairHi y)) (successProb (pairLo y)))
          x)
    {L : ℝ} (hL : 0 < L)
    (hlog_lipschitz :
      ∀ᶠ k : ℕ in Filter.atTop,
        ∀ x : α, x ∈ K → ∀ y : α, y ∈ K →
          |normalizedLogKernelRate
              (fun k x =>
                twoSampleFloorScoreGapLeftTailProb
                  (realBinaryRatingLDPModel successProb hprob0 hprob1)
                  sampleRate (pairHi x) (pairLo x) k)
              k y -
            normalizedLogKernelRate
              (fun k x =>
                twoSampleFloorScoreGapLeftTailProb
                  (realBinaryRatingLDPModel successProb hprob0 hprob1)
                  sampleRate (pairHi x) (pairLo x) k)
              k x| ≤ L * dist y x) :
    UniformNormalizedLogRateCertificateOn
      (fun k x =>
        twoSampleFloorScoreGapLeftTailProb
          (realBinaryRatingLDPModel successProb hprob0 hprob1)
          sampleRate (pairHi x) (pairLo x) k)
      (fun x =>
        weightedBernoulliClosedThresholdRate
          (sampleRate (pairHi x)) (sampleRate (pairLo x))
          (successProb (pairHi x)) (successProb (pairLo x)))
      s := by
  let M := realBinaryRatingLDPModel successProb hprob0 hprob1
  let kernel : ℕ → α → ℝ :=
    fun k x =>
      twoSampleFloorScoreGapLeftTailProb M sampleRate
        (pairHi x) (pairLo x) k
  let rate : α → ℝ := fun x =>
    weightedBernoulliClosedThresholdRate
      (sampleRate (pairHi x)) (sampleRate (pairLo x))
      (successProb (pairHi x)) (successProb (pairLo x))
  have hpos :
      ∀ᶠ k : ℕ in Filter.atTop, ∀ x : α, x ∈ s → 0 < kernel k x := by
    filter_upwards with k x hx
    have hxK : x ∈ K := hsub hx
    simpa [kernel, M] using
      realBinaryRatingLDPModel_floorScoreGapLeftTailProb_pos_of_lt_one
        successProb hprob0 hprob1 sampleRate (pairHi x) (pairLo x) k
        (hprob_hi_lt_one x hxK) (hprob_lo_lt_one x hxK)
  have hcert :
      ∀ x : α, x ∈ K →
        ExponentialRateCertificate (fun k : ℕ => kernel k x) (rate x) := by
    intro x hx
    simpa [kernel, rate, M] using
      realBinaryRatingLDPModel_floorScoreGapLeftTail_exponentialRateCertificate_of_weighted_common_threshold_pair
        successProb hprob0 hprob1 sampleRate (pairHi x) (pairLo x)
        (hsample_hi_pos x hx) (hsample_lo_pos x hx)
        (hprob_hi_pos x hx) (hprob_hi_lt_one x hx)
        (hprob_lo_pos x hx) (hprob_lo_lt_one x hx)
        (hprob_order x hx)
  simpa [kernel, rate, M] using
    UniformNormalizedLogRateCertificateOn.of_pointwise_exponentialRateCertificate_eventually_lipschitz_on_compact_superset_of_rate_continuousAt
      hKcompact hsub hpos hcert hrate_cont hL
      (by simpa [kernel, M] using hlog_lipschitz)

/--
Uniform normalized-log certificate for compact families of interior binary
left-tail score-gap kernels from local asymptotic equicontinuity.  This is the
same pointwise-Cramer package as the Lipschitz version, with the regularity
input stated in the weaker local form used by compact-uniform large-deviation
bridges.
-/
def realBinaryRatingLDPModel_floorScoreGapLeftTail_uniformNormalizedLogRateCertificateOn_of_locally_equicontinuous_on_compact
    {Seller α : Type*} [TopologicalSpace α]
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (sampleRate : Seller → ℝ)
    (pairHi pairLo : α → Seller)
    {s K : Set α}
    (hKcompact : IsCompact K) (hsub : s ⊆ K)
    (hsample_hi_pos :
      ∀ x : α, x ∈ K → 0 < sampleRate (pairHi x))
    (hsample_lo_pos :
      ∀ x : α, x ∈ K → 0 < sampleRate (pairLo x))
    (hprob_hi_pos :
      ∀ x : α, x ∈ K → 0 < successProb (pairHi x))
    (hprob_hi_lt_one :
      ∀ x : α, x ∈ K → successProb (pairHi x) < 1)
    (hprob_lo_pos :
      ∀ x : α, x ∈ K → 0 < successProb (pairLo x))
    (hprob_lo_lt_one :
      ∀ x : α, x ∈ K → successProb (pairLo x) < 1)
    (hprob_order :
      ∀ x : α, x ∈ K →
        successProb (pairLo x) ≤ successProb (pairHi x))
    (hrate_cont :
      ∀ x : α, x ∈ K →
        ContinuousAt
          (fun y : α =>
            weightedBernoulliClosedThresholdRate
              (sampleRate (pairHi y)) (sampleRate (pairLo y))
              (successProb (pairHi y)) (successProb (pairLo y)))
          x)
    (hlog_local :
      ∀ x : α, x ∈ K → ∀ ε > 0,
        ∃ U : Set α,
          IsOpen U ∧ x ∈ U ∧
            ∀ᶠ k : ℕ in Filter.atTop,
              ∀ y : α, y ∈ K → y ∈ U →
                |normalizedLogKernelRate
                    (fun k x =>
                      twoSampleFloorScoreGapLeftTailProb
                        (realBinaryRatingLDPModel successProb hprob0 hprob1)
                        sampleRate (pairHi x) (pairLo x) k)
                    k y -
                  normalizedLogKernelRate
                    (fun k x =>
                      twoSampleFloorScoreGapLeftTailProb
                        (realBinaryRatingLDPModel successProb hprob0 hprob1)
                        sampleRate (pairHi x) (pairLo x) k)
                    k x| ≤ ε) :
    UniformNormalizedLogRateCertificateOn
      (fun k x =>
        twoSampleFloorScoreGapLeftTailProb
          (realBinaryRatingLDPModel successProb hprob0 hprob1)
          sampleRate (pairHi x) (pairLo x) k)
      (fun x =>
        weightedBernoulliClosedThresholdRate
          (sampleRate (pairHi x)) (sampleRate (pairLo x))
          (successProb (pairHi x)) (successProb (pairLo x)))
      s := by
  let M := realBinaryRatingLDPModel successProb hprob0 hprob1
  let kernel : ℕ → α → ℝ :=
    fun k x =>
      twoSampleFloorScoreGapLeftTailProb M sampleRate
        (pairHi x) (pairLo x) k
  let rate : α → ℝ := fun x =>
    weightedBernoulliClosedThresholdRate
      (sampleRate (pairHi x)) (sampleRate (pairLo x))
      (successProb (pairHi x)) (successProb (pairLo x))
  have hpos :
      ∀ᶠ k : ℕ in Filter.atTop, ∀ x : α, x ∈ s → 0 < kernel k x := by
    filter_upwards with k x hx
    have hxK : x ∈ K := hsub hx
    simpa [kernel, M] using
      realBinaryRatingLDPModel_floorScoreGapLeftTailProb_pos_of_lt_one
        successProb hprob0 hprob1 sampleRate (pairHi x) (pairLo x) k
        (hprob_hi_lt_one x hxK) (hprob_lo_lt_one x hxK)
  have hcert :
      ∀ x : α, x ∈ K →
        ExponentialRateCertificate (fun k : ℕ => kernel k x) (rate x) := by
    intro x hx
    simpa [kernel, rate, M] using
      realBinaryRatingLDPModel_floorScoreGapLeftTail_exponentialRateCertificate_of_weighted_common_threshold_pair
        successProb hprob0 hprob1 sampleRate (pairHi x) (pairLo x)
        (hsample_hi_pos x hx) (hsample_lo_pos x hx)
        (hprob_hi_pos x hx) (hprob_hi_lt_one x hx)
        (hprob_lo_pos x hx) (hprob_lo_lt_one x hx)
        (hprob_order x hx)
  simpa [kernel, rate, M] using
    UniformNormalizedLogRateCertificateOn.of_pointwise_exponentialRateCertificate_locally_equicontinuous_on_compact_superset_of_rate_continuousAt
      hKcompact hsub hpos hcert hrate_cont
      (by simpa [kernel, M] using hlog_local)

/--
Uniform exponential-sandwich version of
`realBinaryRatingLDPModel_floorScoreGapLeftTail_uniformNormalizedLogRateCertificateOn_of_eventually_lipschitz_on_compact`.
-/
def realBinaryRatingLDPModel_floorScoreGapLeftTail_uniformExponentialRateCertificateOn_of_eventually_lipschitz_on_compact
    {Seller α : Type*} [PseudoMetricSpace α]
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (sampleRate : Seller → ℝ)
    (pairHi pairLo : α → Seller)
    {s K : Set α}
    (hKcompact : IsCompact K) (hsub : s ⊆ K)
    (hsample_hi_pos :
      ∀ x : α, x ∈ K → 0 < sampleRate (pairHi x))
    (hsample_lo_pos :
      ∀ x : α, x ∈ K → 0 < sampleRate (pairLo x))
    (hprob_hi_pos :
      ∀ x : α, x ∈ K → 0 < successProb (pairHi x))
    (hprob_hi_lt_one :
      ∀ x : α, x ∈ K → successProb (pairHi x) < 1)
    (hprob_lo_pos :
      ∀ x : α, x ∈ K → 0 < successProb (pairLo x))
    (hprob_lo_lt_one :
      ∀ x : α, x ∈ K → successProb (pairLo x) < 1)
    (hprob_order :
      ∀ x : α, x ∈ K →
        successProb (pairLo x) ≤ successProb (pairHi x))
    (hrate_cont :
      ∀ x : α, x ∈ K →
        ContinuousAt
          (fun y : α =>
            weightedBernoulliClosedThresholdRate
              (sampleRate (pairHi y)) (sampleRate (pairLo y))
              (successProb (pairHi y)) (successProb (pairLo y)))
          x)
    {L : ℝ} (hL : 0 < L)
    (hlog_lipschitz :
      ∀ᶠ k : ℕ in Filter.atTop,
        ∀ x : α, x ∈ K → ∀ y : α, y ∈ K →
          |normalizedLogKernelRate
              (fun k x =>
                twoSampleFloorScoreGapLeftTailProb
                  (realBinaryRatingLDPModel successProb hprob0 hprob1)
                  sampleRate (pairHi x) (pairLo x) k)
              k y -
            normalizedLogKernelRate
              (fun k x =>
                twoSampleFloorScoreGapLeftTailProb
                  (realBinaryRatingLDPModel successProb hprob0 hprob1)
                  sampleRate (pairHi x) (pairLo x) k)
              k x| ≤ L * dist y x) :
    UniformExponentialRateCertificateOn
      (fun k x =>
        twoSampleFloorScoreGapLeftTailProb
          (realBinaryRatingLDPModel successProb hprob0 hprob1)
          sampleRate (pairHi x) (pairLo x) k)
      (fun x =>
        weightedBernoulliClosedThresholdRate
          (sampleRate (pairHi x)) (sampleRate (pairLo x))
          (successProb (pairHi x)) (successProb (pairLo x)))
      s :=
  (realBinaryRatingLDPModel_floorScoreGapLeftTail_uniformNormalizedLogRateCertificateOn_of_eventually_lipschitz_on_compact
    successProb hprob0 hprob1 sampleRate pairHi pairLo hKcompact hsub
    hsample_hi_pos hsample_lo_pos hprob_hi_pos hprob_hi_lt_one
    hprob_lo_pos hprob_lo_lt_one hprob_order hrate_cont hL
    hlog_lipschitz).toUniformExponentialRateCertificateOn

/--
Uniform exponential-sandwich version of
`realBinaryRatingLDPModel_floorScoreGapLeftTail_uniformNormalizedLogRateCertificateOn_of_locally_equicontinuous_on_compact`.
-/
def realBinaryRatingLDPModel_floorScoreGapLeftTail_uniformExponentialRateCertificateOn_of_locally_equicontinuous_on_compact
    {Seller α : Type*} [TopologicalSpace α]
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (sampleRate : Seller → ℝ)
    (pairHi pairLo : α → Seller)
    {s K : Set α}
    (hKcompact : IsCompact K) (hsub : s ⊆ K)
    (hsample_hi_pos :
      ∀ x : α, x ∈ K → 0 < sampleRate (pairHi x))
    (hsample_lo_pos :
      ∀ x : α, x ∈ K → 0 < sampleRate (pairLo x))
    (hprob_hi_pos :
      ∀ x : α, x ∈ K → 0 < successProb (pairHi x))
    (hprob_hi_lt_one :
      ∀ x : α, x ∈ K → successProb (pairHi x) < 1)
    (hprob_lo_pos :
      ∀ x : α, x ∈ K → 0 < successProb (pairLo x))
    (hprob_lo_lt_one :
      ∀ x : α, x ∈ K → successProb (pairLo x) < 1)
    (hprob_order :
      ∀ x : α, x ∈ K →
        successProb (pairLo x) ≤ successProb (pairHi x))
    (hrate_cont :
      ∀ x : α, x ∈ K →
        ContinuousAt
          (fun y : α =>
            weightedBernoulliClosedThresholdRate
              (sampleRate (pairHi y)) (sampleRate (pairLo y))
              (successProb (pairHi y)) (successProb (pairLo y)))
          x)
    (hlog_local :
      ∀ x : α, x ∈ K → ∀ ε > 0,
        ∃ U : Set α,
          IsOpen U ∧ x ∈ U ∧
            ∀ᶠ k : ℕ in Filter.atTop,
              ∀ y : α, y ∈ K → y ∈ U →
                |normalizedLogKernelRate
                    (fun k x =>
                      twoSampleFloorScoreGapLeftTailProb
                        (realBinaryRatingLDPModel successProb hprob0 hprob1)
                        sampleRate (pairHi x) (pairLo x) k)
                    k y -
                  normalizedLogKernelRate
                    (fun k x =>
                      twoSampleFloorScoreGapLeftTailProb
                        (realBinaryRatingLDPModel successProb hprob0 hprob1)
                        sampleRate (pairHi x) (pairLo x) k)
                    k x| ≤ ε) :
    UniformExponentialRateCertificateOn
      (fun k x =>
        twoSampleFloorScoreGapLeftTailProb
          (realBinaryRatingLDPModel successProb hprob0 hprob1)
          sampleRate (pairHi x) (pairLo x) k)
      (fun x =>
        weightedBernoulliClosedThresholdRate
          (sampleRate (pairHi x)) (sampleRate (pairLo x))
          (successProb (pairHi x)) (successProb (pairLo x)))
      s :=
  (realBinaryRatingLDPModel_floorScoreGapLeftTail_uniformNormalizedLogRateCertificateOn_of_locally_equicontinuous_on_compact
    successProb hprob0 hprob1 sampleRate pairHi pairLo hKcompact hsub
    hsample_hi_pos hsample_lo_pos hprob_hi_pos hprob_hi_lt_one
    hprob_lo_pos hprob_lo_lt_one hprob_order hrate_cont
    hlog_local).toUniformExponentialRateCertificateOn

/--
Pair-local exact floor-count `1 - P_k` certificate for two interior Bernoulli
rating laws at the weighted geometric common threshold.  This is the generic
pairwise error kernel used by continuum integral reductions.
-/
theorem realBinaryRatingLDPModel_floorPkComplementError_exponentialRateCertificate_of_weighted_common_threshold_pair
    {Seller : Type*}
    (successProb : Seller → ℝ)
    (hprob0 : ∀ θ, 0 ≤ successProb θ)
    (hprob1 : ∀ θ, successProb θ ≤ 1)
    (sampleRate : Seller → ℝ) (hi lo : Seller)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo)
    (hpHi0 : 0 < successProb hi) (hpHi1 : successProb hi < 1)
    (hpLo0 : 0 < successProb lo) (hpLo1 : successProb lo < 1)
    (hpLo_le_hi : successProb lo ≤ successProb hi) :
    ExponentialRateCertificate
      (twoSampleFloorPkComplementErrorProb
        (realBinaryRatingLDPModel successProb hprob0 hprob1) sampleRate hi lo)
      (weightedBernoulliClosedThresholdRate
        (sampleRate hi) (sampleRate lo)
        (successProb hi) (successProb lo)) :=
  twoSampleFloorPkComplementError_exponentialRateCertificate_of_leftTail
    (realBinaryRatingLDPModel successProb hprob0 hprob1) sampleRate hi lo
    (realBinaryRatingLDPModel_floorScoreGapLeftTail_exponentialRateCertificate_of_weighted_common_threshold_pair
      successProb hprob0 hprob1 sampleRate hi lo hgHi hgLo hpHi0 hpHi1
      hpLo0 hpLo1 hpLo_le_hi)

end

end Probability
end AppliedModelingLib

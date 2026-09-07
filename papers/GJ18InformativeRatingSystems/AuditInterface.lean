import GJ18InformativeRatingSystems.MainTheorems
import GJ18InformativeRatingSystems.Assumptions

/-!
# Auxiliary Proof Surface: Designing Informative Rating Systems

This historical auxiliary proof surface exposes earlier large-deviation proof
seams. Some declarations retain superseded full-support and legacy-real-rate
routes for audit traceability. They are not the governing GJ18 model and must
not be used as source-fidelity or closeout evidence.

The configured row-level review surface is `PaperInterface.lean`. Keep
human-facing reviewed rows there; declarations in this module are proof support
unless they are re-exported by `PaperInterface.lean`. The governing corrected
model and the final paper theorems are in `ClarifiedSourceModel.lean` and
`PaperInterface.lean`.
-/

namespace GJ18InformativeRatingSystems

noncomputable section

open AppliedModelingLib.Probability

/-- Source object: the paper's log-MGF `Lambda(z | theta)`. -/
abbrev paperLogMGF {Seller Rating : Type*} [Fintype Rating]
    [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (θ : Seller) (z : ℝ) : ℝ :=
  ratingLogMGF M θ z

/-- Source object: the paper's Legendre-transform rate function `I(a | theta)`. -/
abbrev paperRateFunction {Seller Rating : Type*} [Fintype Rating]
    [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (θ : Seller) (a : ℝ) : ℝ :=
  ratingRateFunction M θ a

/--
The paper's log-MGF formula `Λ(z | θ)`.
Source status: Direct source formula.
Source note: Theorem 1 and Appendix Lemma `Pk_LD` define `Lambda` as the log
moment generating function of one rating.
-/
theorem definition_log_mgf_formula
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (θ : Seller) (z : ℝ) :
    paperLogMGF M θ z =
      Real.log (∑ y : Rating,
        ((M.typeLaw θ) y).toReal * Real.exp (z * M.score y)) :=
  ratingLogMGF_eq_finite_formula M θ z

/--
The paper's Legendre-transform formula `I(a | θ)`.
Source status: Direct source formula.
Source note: Theorem 1 and Appendix Lemma `Pk_LD` define `I(a | theta)` as the
Legendre transform of the source log-MGF.
-/
theorem definition_rate_function_formula
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (θ : Seller) (a : ℝ) :
    paperRateFunction M θ a =
      sSup (Set.range fun z : ℝ =>
        z * a - paperLogMGF M θ z) :=
  ratingRateFunction_eq_finite_formula M θ a

/-- Lemma C.1/C.2 right-hand side: pairwise threshold-rate formula. -/
theorem lemmaC_pairwise_threshold_rate_formula
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller) :
    pairwiseSellerThresholdRate M sampleRate hi lo =
      sInf (Set.range fun a : ℝ =>
        sampleRate hi * paperRateFunction M hi a +
          sampleRate lo * paperRateFunction M lo a) :=
  pairwiseSellerThresholdRate_eq_inf_ratingRateFunction M sampleRate hi lo

/--
Support-safe Lemma C threshold attainment: common-dual log-MGF derivatives
realize the extended pairwise threshold rate, without all-threshold boundedness
assumptions for the real-valued Legendre API.
-/
theorem lemmaC_pairwise_threshold_rate_top_attained_of_common_logMGF_derivatives
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo)
    (a z : ℝ)
    (hderiv_hi :
      HasDerivAt (fun t : ℝ => M.logMGF hi t) a
        (z * (sampleRate hi)⁻¹))
    (hderiv_lo :
      HasDerivAt (fun t : ℝ => M.logMGF lo t) a
        (-(z * (sampleRate lo)⁻¹))) :
    pairwiseRateObjectiveTop M sampleRate hi lo a =
      pairwiseSellerThresholdRateTop M sampleRate hi lo :=
  pairwiseSellerThresholdRateTop_eq_of_common_logMGF_derivatives
    M sampleRate hi lo hgHi hgLo a z hderiv_hi hderiv_lo

/--
Support-safe Lemma C threshold-rate identity in displayed real-objective form:
the extended source threshold rate equals the finite real objective evaluated
at a common-dual derivative threshold.
-/
theorem lemmaC_pairwise_threshold_rate_top_eq_displayed_objective_of_common_logMGF_derivatives
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo)
    (a z : ℝ)
    (hderiv_hi :
      HasDerivAt (fun t : ℝ => M.logMGF hi t) a
        (z * (sampleRate hi)⁻¹))
    (hderiv_lo :
      HasDerivAt (fun t : ℝ => M.logMGF lo t) a
        (-(z * (sampleRate lo)⁻¹))) :
    pairwiseSellerThresholdRateTop M sampleRate hi lo =
      (M.pairwiseRateObjective sampleRate hi lo a : WithTop ℝ) :=
  pairwiseSellerThresholdRateTop_eq_coe_pairwiseRateObjective_of_common_logMGF_derivatives
    M sampleRate hi lo hgHi hgLo a z hderiv_hi hderiv_lo

/--
Paper-facing package for the remaining pairwise threshold-rate regularity in
Theorem 1.  A value of this type supplies the displayed source thresholds,
common-dual log-MGF derivative witnesses, exact source-threshold rate
identities, and the finite two-sided support needed by the Cramer lower bound.
-/
abbrev theorem1PairwiseThresholdRateRegularity
    {Seller Rating Pair : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller) :=
  PairwiseThresholdRateRegularity M sampleRate pairHi pairLo

/--
Paper-facing support-safe pairwise LDP certificate.  A value supplies, for each
ordered comparison pair, a finite representative of the extended source
threshold rate and an exact floor-count left-tail LDP at that rate.
-/
abbrev theorem1PairwiseThresholdRateTopLdpCertificate
    {Seller Rating Pair : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller) :=
  PairwiseThresholdRateTopLdpCertificate M sampleRate pairHi pairLo

/-- Convert threshold-rate regularity into the support-safe pairwise LDP certificate. -/
def theorem1PairwiseThresholdRateTopLdpCertificate_of_regularity
    {Seller Rating Pair : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
    (hpositive_hi : ∀ p : Pair, 0 < sampleRate (pairHi p))
    (hpositive_lo : ∀ p : Pair, 0 < sampleRate (pairLo p))
    (C : theorem1PairwiseThresholdRateRegularity M sampleRate pairHi pairLo) :
    theorem1PairwiseThresholdRateTopLdpCertificate M sampleRate pairHi pairLo :=
  PairwiseThresholdRateTopLdpCertificate.of_regularity
    M sampleRate pairHi pairLo hpositive_hi hpositive_lo C

/--
Lemma C finite equal-sample MGF bridge: the paired high/low rating-gap MGF
factorizes as the high-type MGF at `z` times the low-type MGF at `-z`.
-/
theorem lemmaC_equal_sample_pairwise_mgf_product_formula
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller) (z : ℝ) :
    finiteMGF (pairedRatingLaw M hi lo) (pairedRatingGapScore M) z =
      M.mgf hi z * M.mgf lo (-z) :=
  pairedRatingGapMGF_eq_product M hi lo z

/--
Lemma C finite equal-sample mean bridge: the paired high/low rating-gap mean
is the high-type expected score minus the low-type expected score.
-/
theorem lemmaC_equal_sample_pairwise_gap_mean_formula
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller) :
    AppliedModelingLib.pmfExp (pairedRatingLaw M hi lo) (pairedRatingGapScore M) =
      AppliedModelingLib.pmfExp (M.typeLaw hi) M.score -
        AppliedModelingLib.pmfExp (M.typeLaw lo) M.score :=
  pairedRatingGapMean_eq_sub M hi lo

/--
Lemma C two-population sample MGF bridge: the exponential moment of independent
high and low rating samples factors into the two finite-rating MGFs.
-/
theorem lemmaC_two_population_sample_mgf_product_formula
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (nHi nLo : ℕ) (cHi cLo z : ℝ) :
    AppliedModelingLib.pmfExp (twoSampleRatingLaw M hi lo nHi nLo)
        (fun sample =>
          Real.exp (z * twoSampleScoreGapSum M cHi cLo sample)) =
      (M.mgf hi (z * cHi)) ^ nHi *
        (M.mgf lo (-(z * cLo))) ^ nLo :=
  twoSampleScoreGapSum_exp_mgf_eq_product M hi lo nHi nLo cHi cLo z

/--
Lemma C two-population Chernoff upper bridge: for a nonpositive dual parameter,
the finite scaled comparison error is bounded by the two-sample MGF product.
-/
theorem lemmaC_two_population_sample_chernoff_upper_bound
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (nHi nLo : ℕ) (cHi cLo : ℝ) {z : ℝ}
    (hz : z ≤ 0) :
    twoSampleScoreGapLeftTailProb M hi lo nHi nLo cHi cLo ≤
      (M.mgf hi (z * cHi)) ^ nHi *
        (M.mgf lo (-(z * cLo))) ^ nLo :=
  twoSampleScoreGapLeftTailProb_le_mgf_product_of_nonpos
    M hi lo nHi nLo cHi cLo hz

/--
Lemma C integer-rate Chernoff upper certificate: with sample counts
`n * gHi` and `n * gLo`, any nonpositive dual parameter gives an exponential
upper bound at the displayed two-population dual exponent.
-/
theorem lemmaC_two_population_integer_rate_chernoff_upper_certificate
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (gHi gLo : ℕ) {z targetRate : ℝ}
    (hz : z ≤ 0)
    (hrate :
      targetRate ≤
        -((gHi : ℝ) * M.logMGF hi (z * (gHi : ℝ)⁻¹) +
          (gLo : ℝ) * M.logMGF lo (-(z * (gLo : ℝ)⁻¹)))) :
    HasExpUpperBoundWithConst
      (fun n : ℕ =>
        twoSampleScoreGapLeftTailProb M hi lo
          (n * gHi) (n * gLo) ((gHi : ℝ)⁻¹) ((gLo : ℝ)⁻¹))
      targetRate :=
  twoSampleAverageGapLeftTail_hasExpUpperBoundWithConst_of_dual
    M hi lo gHi gLo hz hrate

/--
Lemma C integer-rate block MGF bridge: one macro-sample with `gHi` high draws
and `gLo` low draws has the two-population product MGF.
-/
theorem lemmaC_integer_rate_block_mgf_product_formula
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (gHi gLo : ℕ) (z : ℝ) :
    finiteMGF (twoSampleRateBlockLaw M hi lo gHi gLo)
        (twoSampleRateBlockScore M gHi gLo) z =
      (M.mgf hi (z * (gHi : ℝ)⁻¹)) ^ gHi *
        (M.mgf lo (-(z * (gLo : ℝ)⁻¹))) ^ gLo :=
  twoSampleRateBlock_finiteMGF_eq_product M hi lo gHi gLo z

/--
Lemma C integer-rate block log-MGF bridge: the macro-sample log-MGF is the
sum of the two one-rating log-MGFs scaled by the integer sample rates.
-/
theorem lemmaC_integer_rate_block_log_mgf_formula
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (gHi gLo : ℕ) (z : ℝ) :
    finiteLogMGF (twoSampleRateBlockLaw M hi lo gHi gLo)
        (twoSampleRateBlockScore M gHi gLo) z =
      (gHi : ℝ) * M.logMGF hi (z * (gHi : ℝ)⁻¹) +
        (gLo : ℝ) * M.logMGF lo (-(z * (gLo : ℝ)⁻¹)) :=
  twoSampleRateBlock_finiteLogMGF_eq M hi lo gHi gLo z

/--
Lemma C integer-rate block exact-rate bridge: after grouping `gHi` and `gLo`
ratings into one independent block, the reusable finite iid Cramer certificate
gives the exact comparison exponent for repeated blocks.
-/
theorem lemmaC_integer_rate_block_error_rate_from_cramer
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (gHi gLo : ℕ)
    (C :
      FiniteIidScoreCramerCertificate
        (twoSampleRateBlockLaw M hi lo gHi gLo)
        (twoSampleRateBlockScore M gHi gLo)) :
    ExponentialRateCertificate
      (twoSampleRateBlockErrorProb M hi lo gHi gLo)
      (twoSampleRateBlockChernoffRate M hi lo gHi gLo) :=
  twoSampleRateBlock_exponentialRateCertificate_of_cramer M hi lo gHi gLo C

/--
Lemma C integer-rate grouping bridge: the repeated block comparison error is
the same probability as the ungrouped two-population comparison with counts
`n * gHi` and `n * gLo`.
-/
theorem lemmaC_integer_rate_block_error_probability_eq_two_population_probability
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (gHi gLo n : ℕ) :
    twoSampleRateBlockErrorProb M hi lo gHi gLo n =
      twoSampleScoreGapLeftTailProb M hi lo
        (n * gHi) (n * gLo) ((gHi : ℝ)⁻¹) ((gLo : ℝ)⁻¹) :=
  twoSampleRateBlockErrorProb_eq_twoSampleScoreGapLeftTailProb
    M hi lo gHi gLo n

/--
Lemma C integer-rate block exact-rate bridge from a stationary Chernoff tilt:
the finite block Cramer certificate is discharged by the shared empirical-type
method-of-types theorem.
-/
theorem lemmaC_integer_rate_block_error_rate_from_stationary_tilt
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (gHi gLo : ℕ)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp (twoSampleRateBlockLaw M hi lo gHi gLo)
          (twoSampleRateBlockScore M gHi gLo))
    {samplePos sampleNeg : (Fin gHi → Rating) × (Fin gLo → Rating)}
    (hmassPos :
      0 < (twoSampleRateBlockLaw M hi lo gHi gLo samplePos).toReal)
    (hscorePos : 0 < twoSampleRateBlockScore M gHi gLo samplePos)
    (hmassNeg :
      0 < (twoSampleRateBlockLaw M hi lo gHi gLo sampleNeg).toReal)
    (hscoreNeg : twoSampleRateBlockScore M gHi gLo sampleNeg < 0)
    {z : ℝ}
    (hstationary :
      (∑ sample : (Fin gHi → Rating) × (Fin gLo → Rating),
        (twoSampleRateBlockLaw M hi lo gHi gLo sample).toReal *
          (twoSampleRateBlockScore M gHi gLo sample *
            Real.exp (z * twoSampleRateBlockScore M gHi gLo sample))) = 0) :
    ExponentialRateCertificate
      (twoSampleRateBlockErrorProb M hi lo gHi gLo)
      (twoSampleRateBlockChernoffRate M hi lo gHi gLo) :=
  twoSampleRateBlock_exponentialRateCertificate_of_stationary_tilt
    M hi lo gHi gLo hmean hmassPos hscorePos hmassNeg hscoreNeg
    hstationary

/--
Lemma C one-sided Fenchel bridge: under positive integer sample rates and the
finite-real bounded-Legendre side conditions, the block Chernoff exponent is
bounded above by the source infimum over common score thresholds.
-/
theorem lemmaC_integer_rate_block_chernoff_le_source_threshold_rate
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller) (gHi gLo : ℕ)
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hsample_hi : sampleRate hi = (gHi : ℝ))
    (hsample_lo : sampleRate lo = (gLo : ℝ))
    (hbdd_hi :
      ∀ a : ℝ, BddAbove (Set.range fun z : ℝ =>
        finiteLegendreValue (M.typeLaw hi) M.score a z))
    (hbdd_lo :
      ∀ a : ℝ, BddAbove (Set.range fun z : ℝ =>
        finiteLegendreValue (M.typeLaw lo) M.score a z)) :
    twoSampleRateBlockChernoffRate M hi lo gHi gLo ≤
      pairwiseSellerThresholdRate M sampleRate hi lo :=
  twoSampleRateBlockChernoffRate_le_pairwiseSellerThresholdRate
    M sampleRate hi lo gHi gLo hgHi hgLo hsample_hi hsample_lo
    hbdd_hi hbdd_lo

/--
Lemma C source-threshold exact-rate bridge: combining the finite iid Cramer
certificate, the proved forward Fenchel inequality, and the remaining reverse
no-duality-gap inequality yields the exact source threshold rate.
-/
theorem lemmaC_integer_rate_block_source_threshold_rate_from_cramer
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller) (gHi gLo : ℕ)
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hsample_hi : sampleRate hi = (gHi : ℝ))
    (hsample_lo : sampleRate lo = (gLo : ℝ))
    (hbdd_hi :
      ∀ a : ℝ, BddAbove (Set.range fun z : ℝ =>
        finiteLegendreValue (M.typeLaw hi) M.score a z))
    (hbdd_lo :
      ∀ a : ℝ, BddAbove (Set.range fun z : ℝ =>
        finiteLegendreValue (M.typeLaw lo) M.score a z))
    (hreverse :
      pairwiseSellerThresholdRate M sampleRate hi lo ≤
        twoSampleRateBlockChernoffRate M hi lo gHi gLo)
    (C :
      FiniteIidScoreCramerCertificate
        (twoSampleRateBlockLaw M hi lo gHi gLo)
        (twoSampleRateBlockScore M gHi gLo)) :
    ExponentialRateCertificate
      (twoSampleRateBlockErrorProb M hi lo gHi gLo)
      (pairwiseSellerThresholdRate M sampleRate hi lo) :=
  twoSampleRateBlock_pairwiseThresholdRate_exponentialRateCertificate
    M sampleRate hi lo gHi gLo hgHi hgLo hsample_hi hsample_lo
    hbdd_hi hbdd_lo hreverse C

/--
Lemma C source-threshold exact-rate bridge from a stationary Chernoff tilt:
the finite block Cramer side is derived from empirical-type lower bounds, while
the reverse Fenchel/no-duality-gap inequality remains the source analytic side
condition.
-/
theorem lemmaC_integer_rate_block_source_threshold_rate_from_stationary_tilt
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller) (gHi gLo : ℕ)
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hsample_hi : sampleRate hi = (gHi : ℝ))
    (hsample_lo : sampleRate lo = (gLo : ℝ))
    (hbdd_hi :
      ∀ a : ℝ, BddAbove (Set.range fun z : ℝ =>
        finiteLegendreValue (M.typeLaw hi) M.score a z))
    (hbdd_lo :
      ∀ a : ℝ, BddAbove (Set.range fun z : ℝ =>
        finiteLegendreValue (M.typeLaw lo) M.score a z))
    (hreverse :
      pairwiseSellerThresholdRate M sampleRate hi lo ≤
        twoSampleRateBlockChernoffRate M hi lo gHi gLo)
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp (twoSampleRateBlockLaw M hi lo gHi gLo)
          (twoSampleRateBlockScore M gHi gLo))
    {samplePos sampleNeg : (Fin gHi → Rating) × (Fin gLo → Rating)}
    (hmassPos :
      0 < (twoSampleRateBlockLaw M hi lo gHi gLo samplePos).toReal)
    (hscorePos : 0 < twoSampleRateBlockScore M gHi gLo samplePos)
    (hmassNeg :
      0 < (twoSampleRateBlockLaw M hi lo gHi gLo sampleNeg).toReal)
    (hscoreNeg : twoSampleRateBlockScore M gHi gLo sampleNeg < 0)
    {z : ℝ}
    (hstationary :
      (∑ sample : (Fin gHi → Rating) × (Fin gLo → Rating),
        (twoSampleRateBlockLaw M hi lo gHi gLo sample).toReal *
          (twoSampleRateBlockScore M gHi gLo sample *
            Real.exp (z * twoSampleRateBlockScore M gHi gLo sample))) = 0) :
    ExponentialRateCertificate
      (twoSampleRateBlockErrorProb M hi lo gHi gLo)
      (pairwiseSellerThresholdRate M sampleRate hi lo) :=
  twoSampleRateBlock_pairwiseThresholdRate_exponentialRateCertificate_of_stationary_tilt
    M sampleRate hi lo gHi gLo hgHi hgLo hsample_hi hsample_lo
    hbdd_hi hbdd_lo hreverse hmean hmassPos hscorePos hmassNeg hscoreNeg
    hstationary

/--
Lemma C source-threshold exact-rate bridge from first-order Fenchel data: a
common derivative threshold plus a stationary block dual discharges the reverse
Fenchel side, and the empirical-type theorem discharges the finite block
Cramer side.
-/
theorem lemmaC_integer_rate_block_source_threshold_rate_from_common_derivatives
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller) (gHi gLo : ℕ)
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hsample_hi : sampleRate hi = (gHi : ℝ))
    (hsample_lo : sampleRate lo = (gLo : ℝ))
    (hbdd_hi :
      ∀ a : ℝ, BddAbove (Set.range fun z : ℝ =>
        finiteLegendreValue (M.typeLaw hi) M.score a z))
    (hbdd_lo :
      ∀ a : ℝ, BddAbove (Set.range fun z : ℝ =>
        finiteLegendreValue (M.typeLaw lo) M.score a z))
    (a z : ℝ)
    (hderiv_hi :
      HasDerivAt (fun t : ℝ => M.logMGF hi t) a
        (z * (gHi : ℝ)⁻¹))
    (hderiv_lo :
      HasDerivAt (fun t : ℝ => M.logMGF lo t) a
        (-(z * (gLo : ℝ)⁻¹)))
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp (twoSampleRateBlockLaw M hi lo gHi gLo)
          (twoSampleRateBlockScore M gHi gLo))
    {samplePos sampleNeg : (Fin gHi → Rating) × (Fin gLo → Rating)}
    (hmassPos :
      0 < (twoSampleRateBlockLaw M hi lo gHi gLo samplePos).toReal)
    (hscorePos : 0 < twoSampleRateBlockScore M gHi gLo samplePos)
    (hmassNeg :
      0 < (twoSampleRateBlockLaw M hi lo gHi gLo sampleNeg).toReal)
    (hscoreNeg : twoSampleRateBlockScore M gHi gLo sampleNeg < 0)
    (hstationary :
      (∑ sample : (Fin gHi → Rating) × (Fin gLo → Rating),
        (twoSampleRateBlockLaw M hi lo gHi gLo sample).toReal *
          (twoSampleRateBlockScore M gHi gLo sample *
            Real.exp (z * twoSampleRateBlockScore M gHi gLo sample))) = 0) :
    ExponentialRateCertificate
      (twoSampleRateBlockErrorProb M hi lo gHi gLo)
      (pairwiseSellerThresholdRate M sampleRate hi lo) :=
  twoSampleRateBlock_pairwiseThresholdRate_exponentialRateCertificate_of_common_derivatives
    M sampleRate hi lo gHi gLo hgHi hgLo hsample_hi hsample_lo
    hbdd_hi hbdd_lo a z hderiv_hi hderiv_lo hmean
    hmassPos hscorePos hmassNeg hscoreNeg hstationary

/--
Lemma C source-threshold exact-rate bridge from common one-rating log-MGF
derivatives.  The common-derivative equations imply the block dual is
stationary, so this version has no separate stationary-sum input.
-/
theorem lemmaC_integer_rate_block_source_threshold_rate_from_logMGF_derivatives
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller) (gHi gLo : ℕ)
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hsample_hi : sampleRate hi = (gHi : ℝ))
    (hsample_lo : sampleRate lo = (gLo : ℝ))
    (hbdd_hi :
      ∀ a : ℝ, BddAbove (Set.range fun z : ℝ =>
        finiteLegendreValue (M.typeLaw hi) M.score a z))
    (hbdd_lo :
      ∀ a : ℝ, BddAbove (Set.range fun z : ℝ =>
        finiteLegendreValue (M.typeLaw lo) M.score a z))
    (a z : ℝ)
    (hderiv_hi :
      HasDerivAt (fun t : ℝ => M.logMGF hi t) a
        (z * (gHi : ℝ)⁻¹))
    (hderiv_lo :
      HasDerivAt (fun t : ℝ => M.logMGF lo t) a
        (-(z * (gLo : ℝ)⁻¹)))
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp (twoSampleRateBlockLaw M hi lo gHi gLo)
          (twoSampleRateBlockScore M gHi gLo))
    {samplePos sampleNeg : (Fin gHi → Rating) × (Fin gLo → Rating)}
    (hmassPos :
      0 < (twoSampleRateBlockLaw M hi lo gHi gLo samplePos).toReal)
    (hscorePos : 0 < twoSampleRateBlockScore M gHi gLo samplePos)
    (hmassNeg :
      0 < (twoSampleRateBlockLaw M hi lo gHi gLo sampleNeg).toReal)
    (hscoreNeg : twoSampleRateBlockScore M gHi gLo sampleNeg < 0) :
    ExponentialRateCertificate
      (twoSampleRateBlockErrorProb M hi lo gHi gLo)
      (pairwiseSellerThresholdRate M sampleRate hi lo) :=
  twoSampleRateBlock_pairwiseThresholdRate_exponentialRateCertificate_of_logMGF_derivatives
    M sampleRate hi lo gHi gLo hgHi hgLo hsample_hi hsample_lo
    hbdd_hi hbdd_lo a z hderiv_hi hderiv_lo hmean
    hmassPos hscorePos hmassNeg hscoreNeg

/--
Lemma C ungrouped integer-rate exact-rate bridge from common one-rating
log-MGF derivatives.  This is the same comparison in the paper's native
two-population sample-count form.
-/
theorem lemmaC_integer_rate_two_population_source_threshold_rate_from_logMGF_derivatives
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller) (gHi gLo : ℕ)
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hsample_hi : sampleRate hi = (gHi : ℝ))
    (hsample_lo : sampleRate lo = (gLo : ℝ))
    (hbdd_hi :
      ∀ a : ℝ, BddAbove (Set.range fun z : ℝ =>
        finiteLegendreValue (M.typeLaw hi) M.score a z))
    (hbdd_lo :
      ∀ a : ℝ, BddAbove (Set.range fun z : ℝ =>
        finiteLegendreValue (M.typeLaw lo) M.score a z))
    (a z : ℝ)
    (hderiv_hi :
      HasDerivAt (fun t : ℝ => M.logMGF hi t) a
        (z * (gHi : ℝ)⁻¹))
    (hderiv_lo :
      HasDerivAt (fun t : ℝ => M.logMGF lo t) a
        (-(z * (gLo : ℝ)⁻¹)))
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp (twoSampleRateBlockLaw M hi lo gHi gLo)
          (twoSampleRateBlockScore M gHi gLo))
    {samplePos sampleNeg : (Fin gHi → Rating) × (Fin gLo → Rating)}
    (hmassPos :
      0 < (twoSampleRateBlockLaw M hi lo gHi gLo samplePos).toReal)
    (hscorePos : 0 < twoSampleRateBlockScore M gHi gLo samplePos)
    (hmassNeg :
      0 < (twoSampleRateBlockLaw M hi lo gHi gLo sampleNeg).toReal)
    (hscoreNeg : twoSampleRateBlockScore M gHi gLo sampleNeg < 0) :
    ExponentialRateCertificate
      (fun n : ℕ =>
        twoSampleScoreGapLeftTailProb M hi lo
          (n * gHi) (n * gLo) ((gHi : ℝ)⁻¹) ((gLo : ℝ)⁻¹))
      (pairwiseSellerThresholdRate M sampleRate hi lo) :=
  twoSampleIntegerRateLeftTail_pairwiseThresholdRate_exponentialRateCertificate_of_logMGF_derivatives
    M sampleRate hi lo gHi gLo hgHi hgLo hsample_hi hsample_lo
    hbdd_hi hbdd_lo a z hderiv_hi hderiv_lo hmean
    hmassPos hscorePos hmassNeg hscoreNeg

/--
Lemma `Pk_LD` comparison bridge: the paper's `1 - P_k` pairwise error is
within fixed constants of the nonpositive score-gap event.
-/
theorem lemmaC_pk_complement_error_probability_sandwich_left_tail
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (nHi nLo : ℕ) (cHi cLo : ℝ) :
    twoSampleScoreGapLeftTailProb M hi lo nHi nLo cHi cLo ≤
        twoSamplePkComplementErrorProb M hi lo nHi nLo cHi cLo ∧
      twoSamplePkComplementErrorProb M hi lo nHi nLo cHi cLo ≤
        2 * twoSampleScoreGapLeftTailProb M hi lo nHi nLo cHi cLo :=
  twoSamplePkComplementErrorProb_sandwich_leftTail
    M hi lo nHi nLo cHi cLo

/--
Paper-definition bridge: for
`P_k = Pr(x_hi > x_lo) - Pr(x_hi < x_lo)`, the proof expression
`2 Pr(x_hi < x_lo) + Pr(x_hi = x_lo)` is exactly `1 - P_k`.
-/
theorem lemmaC_pk_complement_error_eq_one_sub_pk_objective
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (nHi nLo : ℕ) (cHi cLo : ℝ) :
    twoSamplePkComplementErrorProb M hi lo nHi nLo cHi cLo =
      1 - twoSamplePkObjectiveProb M hi lo nHi nLo cHi cLo :=
  twoSamplePkComplementErrorProb_eq_one_sub_pkObjectiveProb
    M hi lo nHi nLo cHi cLo

/--
Lemma `Pk_LD` rate bridge: an exact rate for the nonpositive two-sample
score-gap event transfers to the paper's `1 - P_k` pairwise error.
-/
theorem lemmaC_pk_complement_error_rate_from_left_tail
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (gHi gLo : ℕ) {rate : ℝ}
    (C :
      ExponentialRateCertificate
        (fun n : ℕ =>
          twoSampleScoreGapLeftTailProb M hi lo
            (n * gHi) (n * gLo) ((gHi : ℝ)⁻¹) ((gLo : ℝ)⁻¹))
        rate) :
    ExponentialRateCertificate
      (fun n : ℕ =>
        twoSamplePkComplementErrorProb M hi lo
          (n * gHi) (n * gLo) ((gHi : ℝ)⁻¹) ((gLo : ℝ)⁻¹))
      rate :=
  twoSamplePkComplementError_exponentialRateCertificate_of_leftTail
    M hi lo gHi gLo C

/--
Lemma `Pk_LD` source-threshold exact-rate bridge from common one-rating
log-MGF derivatives.
Source status: Source lemma bridge.
Source note: This is the integer-rate source-threshold transfer for the
appendix `1 - P_k` large-deviation statement.
-/
theorem lemmaC_pk_complement_source_threshold_rate_from_logMGF_derivatives
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller) (gHi gLo : ℕ)
    (hgHi : 0 < gHi) (hgLo : 0 < gLo)
    (hsample_hi : sampleRate hi = (gHi : ℝ))
    (hsample_lo : sampleRate lo = (gLo : ℝ))
    (hbdd_hi :
      ∀ a : ℝ, BddAbove (Set.range fun z : ℝ =>
        finiteLegendreValue (M.typeLaw hi) M.score a z))
    (hbdd_lo :
      ∀ a : ℝ, BddAbove (Set.range fun z : ℝ =>
        finiteLegendreValue (M.typeLaw lo) M.score a z))
    (a z : ℝ)
    (hderiv_hi :
      HasDerivAt (fun t : ℝ => M.logMGF hi t) a
        (z * (gHi : ℝ)⁻¹))
    (hderiv_lo :
      HasDerivAt (fun t : ℝ => M.logMGF lo t) a
        (-(z * (gLo : ℝ)⁻¹)))
    (hmean :
      0 ≤
        AppliedModelingLib.pmfExp (twoSampleRateBlockLaw M hi lo gHi gLo)
          (twoSampleRateBlockScore M gHi gLo))
    {samplePos sampleNeg : (Fin gHi → Rating) × (Fin gLo → Rating)}
    (hmassPos :
      0 < (twoSampleRateBlockLaw M hi lo gHi gLo samplePos).toReal)
    (hscorePos : 0 < twoSampleRateBlockScore M gHi gLo samplePos)
    (hmassNeg :
      0 < (twoSampleRateBlockLaw M hi lo gHi gLo sampleNeg).toReal)
    (hscoreNeg : twoSampleRateBlockScore M gHi gLo sampleNeg < 0) :
    ExponentialRateCertificate
      (fun n : ℕ =>
        twoSamplePkComplementErrorProb M hi lo
          (n * gHi) (n * gLo) ((gHi : ℝ)⁻¹) ((gLo : ℝ)⁻¹))
      (pairwiseSellerThresholdRate M sampleRate hi lo) :=
  twoSamplePkComplementError_pairwiseThresholdRate_exponentialRateCertificate_of_logMGF_derivatives
    M sampleRate hi lo gHi gLo hgHi hgLo hsample_hi hsample_lo
    hbdd_hi hbdd_lo a z hderiv_hi hderiv_lo hmean
    hmassPos hscorePos hmassNeg hscoreNeg

/--
Source model count normalization: the paper's sample count
`n_k(theta) = floor(k g(theta))` has asymptotic sampling rate `g(theta)`.
-/
theorem source_floor_sample_count_div_tendsto_sampleRate
    {Seller : Type*} (sampleRate : Seller → ℝ) (θ : Seller)
    (h_nonneg : 0 ≤ sampleRate θ) :
    Filter.Tendsto
      (fun k : ℕ =>
        ((floorSampleCount sampleRate θ k : ℕ) : ℝ) / (k : ℝ))
      Filter.atTop (nhds (sampleRate θ)) :=
  floorSampleCount_div_tendsto_sampleRate sampleRate θ h_nonneg

/--
Natural-valued floor-count bridge: if `g(theta)` is represented by a natural
number, then `floor(k g(theta)) = k g(theta)`.
-/
theorem source_floor_sample_count_eq_mul_of_nat_sampleRate
    {Seller : Type*} (sampleRate : Seller → ℝ) (θ : Seller)
    (g k : ℕ) (hsample : sampleRate θ = (g : ℝ)) :
    floorSampleCount sampleRate θ k = k * g :=
  floorSampleCount_eq_mul_of_nat_sampleRate sampleRate θ g k hsample

/--
Floor-count `Pk_LD` comparison bridge: the source-shaped `1 - P_k` pairwise
error is within fixed constants of the corresponding nonpositive score-gap
event.
-/
theorem lemmaC_floor_pk_complement_error_probability_sandwich_left_tail
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller) (k : ℕ) :
    twoSampleFloorScoreGapLeftTailProb M sampleRate hi lo k ≤
        twoSampleFloorPkComplementErrorProb M sampleRate hi lo k ∧
      twoSampleFloorPkComplementErrorProb M sampleRate hi lo k ≤
        2 * twoSampleFloorScoreGapLeftTailProb M sampleRate hi lo k :=
  twoSampleFloorPkComplementErrorProb_sandwich_leftTail
    M sampleRate hi lo k

/--
Floor-count paper-definition bridge: the source-shaped proof expression is
exactly `1 - P_k` for the paper's `floor(k g(theta))` pairwise objective.
-/
theorem lemmaC_floor_pk_complement_error_eq_one_sub_pk_objective
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller) (k : ℕ) :
    twoSampleFloorPkComplementErrorProb M sampleRate hi lo k =
      1 - twoSampleFloorPkObjectiveProb M sampleRate hi lo k :=
  twoSampleFloorPkComplementErrorProb_eq_one_sub_pkObjectiveProb
    M sampleRate hi lo k

/--
Objective algebra bridge: if the finite pair weights sum to one, the expanded
floor-count `1 - P_k` aggregate is exactly `1 - W_k`.
-/
theorem theorem1_floor_pk_complement_error_eq_one_sub_weighted_objective
    {Seller Rating Pair : Type*} [Fintype Rating] [DecidableEq Rating]
    [Fintype Pair]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller) (weight : Pair → ℝ)
    (hweight_sum : ∑ p : Pair, weight p = 1) (k : ℕ) :
    finiteFloorPkComplementError M sampleRate pairHi pairLo weight k =
      1 - finiteFloorPkObjective M sampleRate pairHi pairLo weight k :=
  finiteFloorPkComplementError_eq_one_sub_objective
    M sampleRate pairHi pairLo weight hweight_sum k

/--
Integer-rate objective algebra bridge: if the finite pair weights sum to one,
the expanded integer-rate `1 - P_n` aggregate is exactly `1 - W_n`.
-/
theorem theorem1_integer_rate_pk_complement_error_eq_one_sub_weighted_objective
    {Seller Rating Pair : Type*} [Fintype Rating] [DecidableEq Rating]
    [Fintype Pair]
    (M : FiniteRatingLDPModel Seller Rating)
    (pairHi pairLo : Pair → Seller) (gHi gLo : Pair → ℕ)
    (weight : Pair → ℝ)
    (hweight_sum : ∑ p : Pair, weight p = 1) (n : ℕ) :
    finiteIntegerRatePkComplementError M pairHi pairLo gHi gLo weight n =
      1 - finiteIntegerRatePkObjective M pairHi pairLo gHi gLo weight n :=
  finiteIntegerRatePkComplementError_eq_one_sub_objective
    M pairHi pairLo gHi gLo weight hweight_sum n

/--
Natural-valued floor-count objective bridge: for positive horizons, the
source floor-count objective is the integer-rate objective.
-/
theorem theorem1_floor_weighted_objective_eq_integer_rate_objective_of_nat_sampleRates
    {Seller Rating Pair : Type*} [Fintype Rating] [DecidableEq Rating]
    [Fintype Pair]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller) (gHi gLo : Pair → ℕ)
    (weight : Pair → ℝ)
    (hsample_hi :
      ∀ p : Pair, sampleRate (pairHi p) = (gHi p : ℝ))
    (hsample_lo :
      ∀ p : Pair, sampleRate (pairLo p) = (gLo p : ℝ))
    (hgHi : ∀ p : Pair, 0 < gHi p)
    (hgLo : ∀ p : Pair, 0 < gLo p)
    (n : ℕ) (hn : 0 < n) :
    finiteFloorPkObjective M sampleRate pairHi pairLo weight n =
      finiteIntegerRatePkObjective M pairHi pairLo gHi gLo weight n :=
  finiteFloorPkObjective_eq_integerRatePkObjective_of_nat_sampleRates
    M sampleRate pairHi pairLo gHi gLo weight
    hsample_hi hsample_lo hgHi hgLo n hn

/--
Floor-count `Pk_LD` rate bridge: an exact rate for the source-shaped
nonpositive score-gap event transfers to the source-shaped `1 - P_k`
pairwise error.
-/
theorem lemmaC_floor_pk_complement_error_rate_from_left_tail
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller) {rate : ℝ}
    (C :
      ExponentialRateCertificate
        (twoSampleFloorScoreGapLeftTailProb M sampleRate hi lo)
        rate) :
    ExponentialRateCertificate
      (twoSampleFloorPkComplementErrorProb M sampleRate hi lo)
      rate :=
  twoSampleFloorPkComplementError_exponentialRateCertificate_of_leftTail
    M sampleRate hi lo C

/--
Lemma C arbitrary-real floor-count pairwise score-gap rate from shifted
high/low finite iid Cramer certificates plus source-rate identities.
-/
theorem lemmaC_floor_score_gap_rate_from_shifted_cramer_minimizer
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo)
    (a z : ℝ) (hz : z ≤ 0)
    (C_hi :
      FiniteIidScoreCramerCertificate (M.typeLaw hi)
        (fun r : Rating => M.score r - a))
    (C_lo :
      FiniteIidScoreCramerCertificate (M.typeLaw lo)
        (fun r : Rating => a - M.score r))
    (hshifted_rate :
      sampleRate hi *
          finiteChernoffRate (M.typeLaw hi)
            (fun r : Rating => M.score r - a) +
        sampleRate lo *
          finiteChernoffRate (M.typeLaw lo)
            (fun r : Rating => a - M.score r) =
        pairwiseSellerThresholdRate M sampleRate hi lo)
    (hdual_rate :
      -((sampleRate hi) *
          M.logMGF hi (z * (sampleRate hi)⁻¹) +
        (sampleRate lo) *
          M.logMGF lo (-(z * (sampleRate lo)⁻¹))) =
        pairwiseSellerThresholdRate M sampleRate hi lo) :
    ExponentialRateCertificate
      (twoSampleFloorScoreGapLeftTailProb M sampleRate hi lo)
      (pairwiseSellerThresholdRate M sampleRate hi lo) :=
  twoSampleFloorScoreGapLeftTail_pairwiseThresholdRate_exponentialRateCertificate_of_shifted_cramer_minimizer
    M sampleRate hi lo hgHi hgLo a z hz C_hi C_lo
    hshifted_rate hdual_rate

/--
Lemma C arbitrary-real floor-count pairwise score-gap rate from source
log-MGF derivative minimizer data.
-/
theorem lemmaC_floor_score_gap_rate_from_logMGF_derivative_minimizer
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo)
    (a z : ℝ) (hz : z ≤ 0)
    (hbdd_hi : BddAbove (Set.range fun t : ℝ =>
      finiteLegendreValue (M.typeLaw hi) M.score a t))
    (hbdd_lo : BddAbove (Set.range fun t : ℝ =>
      finiteLegendreValue (M.typeLaw lo) M.score a t))
    (hderiv_hi :
      HasDerivAt (fun t : ℝ => M.logMGF hi t) a
        (z * (sampleRate hi)⁻¹))
    (hderiv_lo :
      HasDerivAt (fun t : ℝ => M.logMGF lo t) a
        (-(z * (sampleRate lo)⁻¹)))
    (hthreshold_eq :
      M.pairwiseRateObjective sampleRate hi lo a =
        pairwiseSellerThresholdRate M sampleRate hi lo)
    (hmean_hi :
      0 ≤
        AppliedModelingLib.pmfExp (M.typeLaw hi)
          (fun r : Rating => M.score r - a))
    (hmean_lo :
      0 ≤
        AppliedModelingLib.pmfExp (M.typeLaw lo)
          (fun r : Rating => a - M.score r))
    {hiPos hiNeg loPos loNeg : Rating}
    (hmass_hi_pos : 0 < (M.typeLaw hi hiPos).toReal)
    (hscore_hi_pos : 0 < M.score hiPos - a)
    (hmass_hi_neg : 0 < (M.typeLaw hi hiNeg).toReal)
    (hscore_hi_neg : M.score hiNeg - a < 0)
    (hmass_lo_pos : 0 < (M.typeLaw lo loPos).toReal)
    (hscore_lo_pos : 0 < a - M.score loPos)
    (hmass_lo_neg : 0 < (M.typeLaw lo loNeg).toReal)
    (hscore_lo_neg : a - M.score loNeg < 0) :
    ExponentialRateCertificate
      (twoSampleFloorScoreGapLeftTailProb M sampleRate hi lo)
      (pairwiseSellerThresholdRate M sampleRate hi lo) :=
  twoSampleFloorScoreGapLeftTail_pairwiseThresholdRate_exponentialRateCertificate_of_logMGF_derivative_minimizer
    M sampleRate hi lo hgHi hgLo a z hz hbdd_hi hbdd_lo
    hderiv_hi hderiv_lo hthreshold_eq hmean_hi hmean_lo
    hmass_hi_pos hscore_hi_pos hmass_hi_neg hscore_hi_neg
    hmass_lo_pos hscore_lo_pos hmass_lo_neg hscore_lo_neg

/--
Lemma C arbitrary-real floor-count pairwise score-gap rate from source
log-MGF derivative minimizer data, deriving the Legendre boundedness and
shifted mean signs from finite log-MGF convexity.
-/
theorem lemmaC_floor_score_gap_rate_from_logMGF_derivative_minimizer_of_pos_neg_atoms
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo)
    (a z : ℝ) (hz : z ≤ 0)
    (hderiv_hi :
      HasDerivAt (fun t : ℝ => M.logMGF hi t) a
        (z * (sampleRate hi)⁻¹))
    (hderiv_lo :
      HasDerivAt (fun t : ℝ => M.logMGF lo t) a
        (-(z * (sampleRate lo)⁻¹)))
    (hthreshold_eq :
      M.pairwiseRateObjective sampleRate hi lo a =
        pairwiseSellerThresholdRate M sampleRate hi lo)
    {hiPos hiNeg loPos loNeg : Rating}
    (hmass_hi_pos : 0 < (M.typeLaw hi hiPos).toReal)
    (hscore_hi_pos : 0 < M.score hiPos - a)
    (hmass_hi_neg : 0 < (M.typeLaw hi hiNeg).toReal)
    (hscore_hi_neg : M.score hiNeg - a < 0)
    (hmass_lo_pos : 0 < (M.typeLaw lo loPos).toReal)
    (hscore_lo_pos : 0 < a - M.score loPos)
    (hmass_lo_neg : 0 < (M.typeLaw lo loNeg).toReal)
    (hscore_lo_neg : a - M.score loNeg < 0) :
    ExponentialRateCertificate
      (twoSampleFloorScoreGapLeftTailProb M sampleRate hi lo)
      (pairwiseSellerThresholdRate M sampleRate hi lo) :=
  twoSampleFloorScoreGapLeftTail_pairwiseThresholdRate_exponentialRateCertificate_of_logMGF_derivative_minimizer_of_pos_neg_atoms
    M sampleRate hi lo hgHi hgLo a z hz
    hderiv_hi hderiv_lo hthreshold_eq
    hmass_hi_pos hscore_hi_pos hmass_hi_neg hscore_hi_neg
    hmass_lo_pos hscore_lo_pos hmass_lo_neg hscore_lo_neg

/--
Lemma C arbitrary-real floor-count pairwise score-gap rate from source
log-MGF derivative minimizer data and two-sided positive-mass support around
the pairwise threshold.
-/
theorem lemmaC_floor_score_gap_rate_from_logMGF_derivative_minimizer_of_straddling_support
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo)
    (a z : ℝ) (hz : z ≤ 0)
    (hderiv_hi :
      HasDerivAt (fun t : ℝ => M.logMGF hi t) a
        (z * (sampleRate hi)⁻¹))
    (hderiv_lo :
      HasDerivAt (fun t : ℝ => M.logMGF lo t) a
        (-(z * (sampleRate lo)⁻¹)))
    (hthreshold_eq :
      M.pairwiseRateObjective sampleRate hi lo a =
        pairwiseSellerThresholdRate M sampleRate hi lo)
    (hstraddle_hi : ratingLawStraddlesThreshold M hi a)
    (hstraddle_lo : ratingLawStraddlesThreshold M lo a) :
    ExponentialRateCertificate
      (twoSampleFloorScoreGapLeftTailProb M sampleRate hi lo)
      (pairwiseSellerThresholdRate M sampleRate hi lo) :=
  twoSampleFloorScoreGapLeftTail_pairwiseThresholdRate_exponentialRateCertificate_of_logMGF_derivative_minimizer_of_straddling_support
    M sampleRate hi lo hgHi hgLo a z hz
    hderiv_hi hderiv_lo hthreshold_eq hstraddle_hi hstraddle_lo

/--
Lemma C arbitrary-real floor-count pairwise score-gap rate from source
log-MGF derivative data, two-sided support, and the source-level assertion that
the displayed common threshold minimizes the pairwise rate objective.
Source status: Auxiliary proof-route lemma.
Source note: This row exposes the Appendix C derivative/minimizer route for
reuse; the canonical Theorem 1 endpoint derives/packages the needed witnesses.
-/
theorem lemmaC_floor_score_gap_rate_from_logMGF_derivative_threshold_minimizer_of_straddling_support
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo)
    (a z : ℝ) (hz : z ≤ 0)
    (hderiv_hi :
      HasDerivAt (fun t : ℝ => M.logMGF hi t) a
        (z * (sampleRate hi)⁻¹))
    (hderiv_lo :
      HasDerivAt (fun t : ℝ => M.logMGF lo t) a
        (-(z * (sampleRate lo)⁻¹)))
    (hthreshold_min :
      ∀ b : ℝ,
        M.pairwiseRateObjective sampleRate hi lo a ≤
          M.pairwiseRateObjective sampleRate hi lo b)
    (hstraddle_hi : ratingLawStraddlesThreshold M hi a)
    (hstraddle_lo : ratingLawStraddlesThreshold M lo a) :
    ExponentialRateCertificate
      (twoSampleFloorScoreGapLeftTailProb M sampleRate hi lo)
      (pairwiseSellerThresholdRate M sampleRate hi lo) :=
  twoSampleFloorScoreGapLeftTail_pairwiseThresholdRate_exponentialRateCertificate_of_logMGF_derivative_threshold_minimizer_of_straddling_support
    M sampleRate hi lo hgHi hgLo a z hz
    hderiv_hi hderiv_lo hthreshold_min hstraddle_hi hstraddle_lo

/--
Lemma C arbitrary-real floor-count pairwise score-gap rate from source
log-MGF derivative data and compact two-sided support. The source threshold
minimizer is derived by Fenchel optimality under the current bounded-rate
finite-rate API side condition.
-/
theorem lemmaC_floor_score_gap_rate_from_logMGF_derivatives_of_straddling_support
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo)
    (hbdd_hi :
      ∀ b : ℝ, BddAbove (Set.range fun t : ℝ =>
        finiteLegendreValue (M.typeLaw hi) M.score b t))
    (hbdd_lo :
      ∀ b : ℝ, BddAbove (Set.range fun t : ℝ =>
        finiteLegendreValue (M.typeLaw lo) M.score b t))
    (a z : ℝ) (hz : z ≤ 0)
    (hderiv_hi :
      HasDerivAt (fun t : ℝ => M.logMGF hi t) a
        (z * (sampleRate hi)⁻¹))
    (hderiv_lo :
      HasDerivAt (fun t : ℝ => M.logMGF lo t) a
        (-(z * (sampleRate lo)⁻¹)))
    (hstraddle_hi : ratingLawStraddlesThreshold M hi a)
    (hstraddle_lo : ratingLawStraddlesThreshold M lo a) :
    ExponentialRateCertificate
      (twoSampleFloorScoreGapLeftTailProb M sampleRate hi lo)
      (pairwiseSellerThresholdRate M sampleRate hi lo) :=
  twoSampleFloorScoreGapLeftTail_pairwiseThresholdRate_exponentialRateCertificate_of_logMGF_derivatives_of_straddling_support
    M sampleRate hi lo hgHi hgLo hbdd_hi hbdd_lo a z hz
    hderiv_hi hderiv_lo hstraddle_hi hstraddle_lo

/--
Lemma C arbitrary-real floor-count `Pk_LD` rate from shifted high/low finite
iid Cramer certificates plus source-rate identities.
-/
theorem lemmaC_floor_pk_complement_error_rate_from_shifted_cramer_minimizer
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (hi lo : Seller)
    (hgHi : 0 < sampleRate hi) (hgLo : 0 < sampleRate lo)
    (a z : ℝ) (hz : z ≤ 0)
    (C_hi :
      FiniteIidScoreCramerCertificate (M.typeLaw hi)
        (fun r : Rating => M.score r - a))
    (C_lo :
      FiniteIidScoreCramerCertificate (M.typeLaw lo)
        (fun r : Rating => a - M.score r))
    (hshifted_rate :
      sampleRate hi *
          finiteChernoffRate (M.typeLaw hi)
            (fun r : Rating => M.score r - a) +
        sampleRate lo *
          finiteChernoffRate (M.typeLaw lo)
            (fun r : Rating => a - M.score r) =
        pairwiseSellerThresholdRate M sampleRate hi lo)
    (hdual_rate :
      -((sampleRate hi) *
          M.logMGF hi (z * (sampleRate hi)⁻¹) +
        (sampleRate lo) *
          M.logMGF lo (-(z * (sampleRate lo)⁻¹))) =
        pairwiseSellerThresholdRate M sampleRate hi lo) :
    ExponentialRateCertificate
      (twoSampleFloorPkComplementErrorProb M sampleRate hi lo)
      (pairwiseSellerThresholdRate M sampleRate hi lo) :=
  twoSampleFloorPkComplementError_pairwiseThresholdRate_exponentialRateCertificate_of_shifted_cramer_minimizer
    M sampleRate hi lo hgHi hgLo a z hz C_hi C_lo
    hshifted_rate hdual_rate

/--
Lemma C finite equal-sample rate bridge: a finite iid Cramer certificate for
the paired high/low rating gap gives the exact pairwise comparison exponent.
-/
theorem lemmaC_equal_sample_pairwise_error_rate_from_cramer
    {Seller Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel Seller Rating) (hi lo : Seller)
    (C :
      FiniteIidScoreCramerCertificate
        (pairedRatingLaw M hi lo) (pairedRatingGapScore M)) :
    ExponentialRateCertificate
      (equalSamplePairwiseErrorProb M hi lo)
      (equalSamplePairwiseChernoffRate M hi lo) :=
  equalSamplePairwiseError_exponentialRateCertificate_of_cramer M hi lo C

/--
Lemma C `P_k` transfer: a fixed-positive-constant sandwich around a pairwise
comparison error preserves its exact large-deviation exponent.
-/
theorem lemmaC_pk_error_rate_from_pairwise_const_sandwich
    {pairwiseError pkError : ℕ → ℝ} {rate lower upper : ℝ}
    (hpairwise : ExponentialRateCertificate pairwiseError rate)
    (hlower : 0 < lower) (hupper : 0 < upper)
    (hsandwich : ∀ᶠ k in Filter.atTop,
      lower * pairwiseError k ≤ pkError k ∧
        pkError k ≤ upper * pairwiseError k) :
    ExponentialRateCertificate pkError rate :=
  pkError_hasExponentialRate_of_pairwise_const_sandwich
    hpairwise hlower hupper hsandwich

/--
Theorem 1 finite-aggregation bridge: finite pairwise LDP certificates imply an
eventual exponential upper bound for a finite ranking-objective error.
-/
theorem theorem1_finite_ranking_error_upper_bound_from_pair_certificates
    {ι : Type*} [Fintype ι]
    (C : FiniteErrorRateCertificate ι)
    {weight : ι → ℝ} {targetRate : ℝ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hrate : ∀ i, targetRate < C.rate i) :
    HasExpUpperBoundWithConst (C.aggregateError weight) targetRate :=
  rankingObjectiveError_hasExpUpperBound_of_pair_certificates
    C hweight hrate

/--
Theorem 1 finite-min bridge: if one positive-weight pair realizes the minimum
pairwise error exponent and all other finite pairwise exponents are no smaller,
then the finite ranking-objective error has that exact exponent.
-/
theorem theorem1_finite_ranking_error_exact_rate_from_min_pair_certificate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : FiniteErrorRateCertificate ι)
    {weight : ι → ℝ} {minRate : ℝ}
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (iMin : ι) (hweight_pos : 0 < weight iMin)
    (hrate_min : C.rate iMin = minRate)
    (hrate_ge : ∀ i, minRate ≤ C.rate i) :
    HasExponentialRate (C.aggregateError weight) minRate :=
  rankingObjectiveError_hasExponentialRate_of_min_pair_certificate
    C hweight_nonneg iMin hweight_pos hrate_min hrate_ge

/--
Theorem 1 finite adjacent-pair bridge: once adjacent pair exponents dominate
all comparison-pair exponents, the ranking objective has the minimum adjacent
exponent exactly.
-/
theorem theorem1_finite_ranking_error_exact_rate_from_adjacent_pair_min
    {Pair Adj : Type*} [Fintype Pair] [DecidableEq Pair]
    (C : FiniteErrorRateCertificate Pair)
    (adjacentPair : Adj → Pair)
    {weight : Pair → ℝ}
    (hweight_nonneg : ∀ p, 0 ≤ weight p)
    (iMin : Adj) (hweight_pos : 0 < weight (adjacentPair iMin))
    (hadj_min :
      ∀ i : Adj, C.rate (adjacentPair iMin) ≤ C.rate (adjacentPair i))
    (hadj_dominates :
      ∀ p : Pair, ∃ i : Adj, C.rate (adjacentPair i) ≤ C.rate p) :
    HasExponentialRate
      (C.aggregateError weight) (C.rate (adjacentPair iMin)) :=
  rankingObjectiveError_hasExponentialRate_of_adjacent_min_pair_certificate
    C adjacentPair hweight_nonneg iMin hweight_pos hadj_min hadj_dominates

/--
Theorem 1 finite source-rate bridge in the paper's `1 - P_k` notation:
pairwise source-threshold certificates for all comparison pairs imply that the
finite ranking-objective error has the minimum adjacent-pair source rate.
-/
theorem theorem1_finite_pk_complement_ranking_error_exact_rate_from_adjacent_source_rates
    {Seller Rating Pair Adj : Type*} [Fintype Rating] [DecidableEq Rating]
    [Fintype Pair] [DecidableEq Pair]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
    (gHi gLo : Pair → ℕ)
    (weight : Pair → ℝ)
    (adjacentPair : Adj → Pair)
    (hweight_nonneg : ∀ p, 0 ≤ weight p)
    (iMin : Adj) (hweight_pos : 0 < weight (adjacentPair iMin))
    (hpair :
      ∀ p : Pair,
        ExponentialRateCertificate
          (fun n : ℕ =>
            twoSamplePkComplementErrorProb M (pairHi p) (pairLo p)
              (n * gHi p) (n * gLo p)
              (((gHi p : ℕ) : ℝ)⁻¹) (((gLo p : ℕ) : ℝ)⁻¹))
          (pairwiseSellerThresholdRate M sampleRate (pairHi p) (pairLo p)))
    (hadj_min :
      ∀ i : Adj,
        pairwiseSellerThresholdRate M sampleRate
            (pairHi (adjacentPair iMin)) (pairLo (adjacentPair iMin)) ≤
          pairwiseSellerThresholdRate M sampleRate
            (pairHi (adjacentPair i)) (pairLo (adjacentPair i)))
    (hadj_dominates :
      ∀ p : Pair, ∃ i : Adj,
        pairwiseSellerThresholdRate M sampleRate
            (pairHi (adjacentPair i)) (pairLo (adjacentPair i)) ≤
          pairwiseSellerThresholdRate M sampleRate (pairHi p) (pairLo p)) :
    HasExponentialRate
      (fun n : ℕ =>
        ∑ p : Pair,
          weight p *
            twoSamplePkComplementErrorProb M (pairHi p) (pairLo p)
              (n * gHi p) (n * gLo p)
              (((gHi p : ℕ) : ℝ)⁻¹) (((gLo p : ℕ) : ℝ)⁻¹))
      (pairwiseSellerThresholdRate M sampleRate
        (pairHi (adjacentPair iMin)) (pairLo (adjacentPair iMin))) :=
  finiteRankingPkComplementError_hasExponentialRate_of_adjacent_min_source_rates
    M sampleRate pairHi pairLo gHi gLo weight adjacentPair
    hweight_nonneg iMin hweight_pos hpair hadj_min hadj_dominates

/--
Theorem 1 floor-count finite source-rate bridge: pairwise exact source-rate
certificates for the paper's `floor(k g(theta))` pairwise `1 - P_k` errors
imply the finite ranking-objective rate.
-/
theorem theorem1_floor_pk_complement_ranking_error_exact_rate_from_adjacent_source_rates
    {Seller Rating Pair Adj : Type*} [Fintype Rating] [DecidableEq Rating]
    [Fintype Pair] [DecidableEq Pair]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
    (weight : Pair → ℝ)
    (adjacentPair : Adj → Pair)
    (hweight_nonneg : ∀ p, 0 ≤ weight p)
    (iMin : Adj) (hweight_pos : 0 < weight (adjacentPair iMin))
    (hpair :
      ∀ p : Pair,
        ExponentialRateCertificate
          (twoSampleFloorPkComplementErrorProb M sampleRate
            (pairHi p) (pairLo p))
          (pairwiseSellerThresholdRate M sampleRate (pairHi p) (pairLo p)))
    (hadj_min :
      ∀ i : Adj,
        pairwiseSellerThresholdRate M sampleRate
            (pairHi (adjacentPair iMin)) (pairLo (adjacentPair iMin)) ≤
          pairwiseSellerThresholdRate M sampleRate
            (pairHi (adjacentPair i)) (pairLo (adjacentPair i)))
    (hadj_dominates :
      ∀ p : Pair, ∃ i : Adj,
        pairwiseSellerThresholdRate M sampleRate
            (pairHi (adjacentPair i)) (pairLo (adjacentPair i)) ≤
          pairwiseSellerThresholdRate M sampleRate (pairHi p) (pairLo p)) :
    HasExponentialRate
      (fun k : ℕ =>
        ∑ p : Pair,
          weight p *
            twoSampleFloorPkComplementErrorProb M sampleRate
              (pairHi p) (pairLo p) k)
      (pairwiseSellerThresholdRate M sampleRate
        (pairHi (adjacentPair iMin)) (pairLo (adjacentPair iMin))) :=
  finiteRankingFloorPkComplementError_hasExponentialRate_of_adjacent_min_source_rates
    M sampleRate pairHi pairLo weight adjacentPair
    hweight_nonneg iMin hweight_pos hpair hadj_min hadj_dominates

/--
Theorem 1 floor-count finite source-rate bridge from nonpositive score-gap
certificates: this discharges the `Pk_LD` constant-factor transfer before
aggregating to the ranking objective.
-/
theorem theorem1_floor_pk_complement_ranking_error_exact_rate_from_adjacent_leftTail_source_rates
    {Seller Rating Pair Adj : Type*} [Fintype Rating] [DecidableEq Rating]
    [Fintype Pair] [DecidableEq Pair]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
    (weight : Pair → ℝ)
    (adjacentPair : Adj → Pair)
    (hweight_nonneg : ∀ p, 0 ≤ weight p)
    (iMin : Adj) (hweight_pos : 0 < weight (adjacentPair iMin))
    (hleftTail :
      ∀ p : Pair,
        ExponentialRateCertificate
          (twoSampleFloorScoreGapLeftTailProb M sampleRate
            (pairHi p) (pairLo p))
          (pairwiseSellerThresholdRate M sampleRate (pairHi p) (pairLo p)))
    (hadj_min :
      ∀ i : Adj,
        pairwiseSellerThresholdRate M sampleRate
            (pairHi (adjacentPair iMin)) (pairLo (adjacentPair iMin)) ≤
          pairwiseSellerThresholdRate M sampleRate
            (pairHi (adjacentPair i)) (pairLo (adjacentPair i)))
    (hadj_dominates :
      ∀ p : Pair, ∃ i : Adj,
        pairwiseSellerThresholdRate M sampleRate
            (pairHi (adjacentPair i)) (pairLo (adjacentPair i)) ≤
          pairwiseSellerThresholdRate M sampleRate (pairHi p) (pairLo p)) :
    HasExponentialRate
      (fun k : ℕ =>
        ∑ p : Pair,
          weight p *
            twoSampleFloorPkComplementErrorProb M sampleRate
              (pairHi p) (pairLo p) k)
      (pairwiseSellerThresholdRate M sampleRate
        (pairHi (adjacentPair iMin)) (pairLo (adjacentPair iMin))) :=
  finiteRankingFloorPkComplementError_hasExponentialRate_of_adjacent_leftTail_source_rates
    M sampleRate pairHi pairLo weight adjacentPair
    hweight_nonneg iMin hweight_pos hleftTail hadj_min hadj_dominates

/--
Theorem 1 floor-count source-shaped endpoint: the finite paper objective
itself has the claimed exact adjacent-pair source rate for `1 - W_k`.
-/
theorem theorem1_floor_weighted_objective_oneSub_exact_rate_from_adjacent_leftTail_source_rates
    {Seller Rating Pair Adj : Type*} [Fintype Rating] [DecidableEq Rating]
    [Fintype Pair] [DecidableEq Pair]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
    (weight : Pair → ℝ)
    (adjacentPair : Adj → Pair)
    (hweight_nonneg : ∀ p, 0 ≤ weight p)
    (hweight_sum : ∑ p : Pair, weight p = 1)
    (iMin : Adj) (hweight_pos : 0 < weight (adjacentPair iMin))
    (hleftTail :
      ∀ p : Pair,
        ExponentialRateCertificate
          (twoSampleFloorScoreGapLeftTailProb M sampleRate
            (pairHi p) (pairLo p))
          (pairwiseSellerThresholdRate M sampleRate (pairHi p) (pairLo p)))
    (hadj_min :
      ∀ i : Adj,
        pairwiseSellerThresholdRate M sampleRate
            (pairHi (adjacentPair iMin)) (pairLo (adjacentPair iMin)) ≤
          pairwiseSellerThresholdRate M sampleRate
            (pairHi (adjacentPair i)) (pairLo (adjacentPair i)))
    (hadj_dominates :
      ∀ p : Pair, ∃ i : Adj,
        pairwiseSellerThresholdRate M sampleRate
            (pairHi (adjacentPair i)) (pairLo (adjacentPair i)) ≤
          pairwiseSellerThresholdRate M sampleRate (pairHi p) (pairLo p)) :
    HasExponentialRate
      (fun k : ℕ =>
        1 - finiteFloorPkObjective M sampleRate pairHi pairLo weight k)
      (pairwiseSellerThresholdRate M sampleRate
        (pairHi (adjacentPair iMin)) (pairLo (adjacentPair iMin))) :=
  finiteFloorPkObjective_oneSub_hasExponentialRate_of_adjacent_leftTail_source_rates
    M sampleRate pairHi pairLo weight adjacentPair
    hweight_nonneg hweight_sum iMin hweight_pos hleftTail
    hadj_min hadj_dominates

/--
Theorem 1 arbitrary-real floor-count endpoint from per-pair shifted-Cramer
minimizers and source-rate identities: the paper-style objective has the exact
adjacent-pair source rate for `1 - W_k`.
-/
theorem theorem1_floor_weighted_objective_oneSub_exact_rate_from_adjacent_shifted_cramer_minimizers
    {Seller Rating Pair Adj : Type*} [Fintype Rating] [DecidableEq Rating]
    [Fintype Pair] [DecidableEq Pair]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
    (weight : Pair → ℝ)
    (adjacentPair : Adj → Pair)
    (hweight_nonneg : ∀ p, 0 ≤ weight p)
    (hweight_sum : ∑ p : Pair, weight p = 1)
    (iMin : Adj) (hweight_pos : 0 < weight (adjacentPair iMin))
    (hgHi : ∀ p : Pair, 0 < sampleRate (pairHi p))
    (hgLo : ∀ p : Pair, 0 < sampleRate (pairLo p))
    (a z : Pair → ℝ)
    (hz : ∀ p : Pair, z p ≤ 0)
    (C_hi :
      ∀ p : Pair,
        FiniteIidScoreCramerCertificate (M.typeLaw (pairHi p))
          (fun r : Rating => M.score r - a p))
    (C_lo :
      ∀ p : Pair,
        FiniteIidScoreCramerCertificate (M.typeLaw (pairLo p))
          (fun r : Rating => a p - M.score r))
    (hshifted_rate :
      ∀ p : Pair,
        sampleRate (pairHi p) *
            finiteChernoffRate (M.typeLaw (pairHi p))
              (fun r : Rating => M.score r - a p) +
          sampleRate (pairLo p) *
            finiteChernoffRate (M.typeLaw (pairLo p))
              (fun r : Rating => a p - M.score r) =
          pairwiseSellerThresholdRate M sampleRate (pairHi p) (pairLo p))
    (hdual_rate :
      ∀ p : Pair,
        -((sampleRate (pairHi p)) *
            M.logMGF (pairHi p) (z p * (sampleRate (pairHi p))⁻¹) +
          (sampleRate (pairLo p)) *
            M.logMGF (pairLo p) (-(z p * (sampleRate (pairLo p))⁻¹))) =
          pairwiseSellerThresholdRate M sampleRate (pairHi p) (pairLo p))
    (hadj_min :
      ∀ i : Adj,
        pairwiseSellerThresholdRate M sampleRate
            (pairHi (adjacentPair iMin)) (pairLo (adjacentPair iMin)) ≤
          pairwiseSellerThresholdRate M sampleRate
            (pairHi (adjacentPair i)) (pairLo (adjacentPair i)))
    (hadj_dominates :
      ∀ p : Pair, ∃ i : Adj,
        pairwiseSellerThresholdRate M sampleRate
            (pairHi (adjacentPair i)) (pairLo (adjacentPair i)) ≤
          pairwiseSellerThresholdRate M sampleRate (pairHi p) (pairLo p)) :
    HasExponentialRate
      (fun k : ℕ =>
        1 - finiteFloorPkObjective M sampleRate pairHi pairLo weight k)
      (pairwiseSellerThresholdRate M sampleRate
        (pairHi (adjacentPair iMin)) (pairLo (adjacentPair iMin))) :=
  finiteFloorPkObjective_oneSub_hasExponentialRate_of_adjacent_shifted_cramer_minimizers
    M sampleRate pairHi pairLo weight adjacentPair
    hweight_nonneg hweight_sum iMin hweight_pos hgHi hgLo
    a z hz C_hi C_lo hshifted_rate hdual_rate hadj_min hadj_dominates

/--
Theorem 1 arbitrary-real floor-count endpoint from per-pair source log-MGF
derivative minimizers: the paper-style objective has the exact adjacent-pair
source rate for `1 - W_k`.
-/
theorem theorem1_floor_weighted_objective_oneSub_exact_rate_from_adjacent_logMGF_derivative_minimizers
    {Seller Rating Pair Adj : Type*} [Fintype Rating] [DecidableEq Rating]
    [Fintype Pair] [DecidableEq Pair]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
    (weight : Pair → ℝ)
    (adjacentPair : Adj → Pair)
    (hweight_nonneg : ∀ p, 0 ≤ weight p)
    (hweight_sum : ∑ p : Pair, weight p = 1)
    (iMin : Adj) (hweight_pos : 0 < weight (adjacentPair iMin))
    (hgHi : ∀ p : Pair, 0 < sampleRate (pairHi p))
    (hgLo : ∀ p : Pair, 0 < sampleRate (pairLo p))
    (a z : Pair → ℝ)
    (hz : ∀ p : Pair, z p ≤ 0)
    (hbdd_hi :
      ∀ p : Pair, BddAbove (Set.range fun t : ℝ =>
        finiteLegendreValue (M.typeLaw (pairHi p)) M.score (a p) t))
    (hbdd_lo :
      ∀ p : Pair, BddAbove (Set.range fun t : ℝ =>
        finiteLegendreValue (M.typeLaw (pairLo p)) M.score (a p) t))
    (hderiv_hi :
      ∀ p : Pair,
        HasDerivAt (fun t : ℝ => M.logMGF (pairHi p) t) (a p)
          (z p * (sampleRate (pairHi p))⁻¹))
    (hderiv_lo :
      ∀ p : Pair,
        HasDerivAt (fun t : ℝ => M.logMGF (pairLo p) t) (a p)
          (-(z p * (sampleRate (pairLo p))⁻¹)))
    (hthreshold_eq :
      ∀ p : Pair,
        M.pairwiseRateObjective sampleRate (pairHi p) (pairLo p) (a p) =
          pairwiseSellerThresholdRate M sampleRate (pairHi p) (pairLo p))
    (hmean_hi :
      ∀ p : Pair,
        0 ≤
          AppliedModelingLib.pmfExp (M.typeLaw (pairHi p))
            (fun r : Rating => M.score r - a p))
    (hmean_lo :
      ∀ p : Pair,
        0 ≤
          AppliedModelingLib.pmfExp (M.typeLaw (pairLo p))
            (fun r : Rating => a p - M.score r))
    (hiPos hiNeg loPos loNeg : Pair → Rating)
    (hmass_hi_pos :
      ∀ p : Pair, 0 < (M.typeLaw (pairHi p) (hiPos p)).toReal)
    (hscore_hi_pos :
      ∀ p : Pair, 0 < M.score (hiPos p) - a p)
    (hmass_hi_neg :
      ∀ p : Pair, 0 < (M.typeLaw (pairHi p) (hiNeg p)).toReal)
    (hscore_hi_neg :
      ∀ p : Pair, M.score (hiNeg p) - a p < 0)
    (hmass_lo_pos :
      ∀ p : Pair, 0 < (M.typeLaw (pairLo p) (loPos p)).toReal)
    (hscore_lo_pos :
      ∀ p : Pair, 0 < a p - M.score (loPos p))
    (hmass_lo_neg :
      ∀ p : Pair, 0 < (M.typeLaw (pairLo p) (loNeg p)).toReal)
    (hscore_lo_neg :
      ∀ p : Pair, a p - M.score (loNeg p) < 0)
    (hadj_min :
      ∀ i : Adj,
        pairwiseSellerThresholdRate M sampleRate
            (pairHi (adjacentPair iMin)) (pairLo (adjacentPair iMin)) ≤
          pairwiseSellerThresholdRate M sampleRate
            (pairHi (adjacentPair i)) (pairLo (adjacentPair i)))
    (hadj_dominates :
      ∀ p : Pair, ∃ i : Adj,
        pairwiseSellerThresholdRate M sampleRate
            (pairHi (adjacentPair i)) (pairLo (adjacentPair i)) ≤
          pairwiseSellerThresholdRate M sampleRate (pairHi p) (pairLo p)) :
    HasExponentialRate
      (fun k : ℕ =>
        1 - finiteFloorPkObjective M sampleRate pairHi pairLo weight k)
      (pairwiseSellerThresholdRate M sampleRate
        (pairHi (adjacentPair iMin)) (pairLo (adjacentPair iMin))) :=
  finiteFloorPkObjective_oneSub_hasExponentialRate_of_adjacent_logMGF_derivative_minimizers
    M sampleRate pairHi pairLo weight adjacentPair
    hweight_nonneg hweight_sum iMin hweight_pos hgHi hgLo
    a z hz hbdd_hi hbdd_lo hderiv_hi hderiv_lo hthreshold_eq
    hmean_hi hmean_lo hiPos hiNeg loPos loNeg
    hmass_hi_pos hscore_hi_pos hmass_hi_neg hscore_hi_neg
    hmass_lo_pos hscore_lo_pos hmass_lo_neg hscore_lo_neg
    hadj_min hadj_dominates

/--
Theorem 1 arbitrary-real floor-count endpoint from per-pair source log-MGF
derivative minimizers, deriving the Legendre boundedness and shifted mean signs
from finite log-MGF convexity.
-/
theorem theorem1_floor_weighted_objective_oneSub_exact_rate_from_adjacent_logMGF_derivative_minimizers_of_pos_neg_atoms
    {Seller Rating Pair Adj : Type*} [Fintype Rating] [DecidableEq Rating]
    [Fintype Pair] [DecidableEq Pair]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
    (weight : Pair → ℝ)
    (adjacentPair : Adj → Pair)
    (hweight_nonneg : ∀ p, 0 ≤ weight p)
    (hweight_sum : ∑ p : Pair, weight p = 1)
    (iMin : Adj) (hweight_pos : 0 < weight (adjacentPair iMin))
    (hgHi : ∀ p : Pair, 0 < sampleRate (pairHi p))
    (hgLo : ∀ p : Pair, 0 < sampleRate (pairLo p))
    (a z : Pair → ℝ)
    (hz : ∀ p : Pair, z p ≤ 0)
    (hderiv_hi :
      ∀ p : Pair,
        HasDerivAt (fun t : ℝ => M.logMGF (pairHi p) t) (a p)
          (z p * (sampleRate (pairHi p))⁻¹))
    (hderiv_lo :
      ∀ p : Pair,
        HasDerivAt (fun t : ℝ => M.logMGF (pairLo p) t) (a p)
          (-(z p * (sampleRate (pairLo p))⁻¹)))
    (hthreshold_eq :
      ∀ p : Pair,
        M.pairwiseRateObjective sampleRate (pairHi p) (pairLo p) (a p) =
          pairwiseSellerThresholdRate M sampleRate (pairHi p) (pairLo p))
    (hiPos hiNeg loPos loNeg : Pair → Rating)
    (hmass_hi_pos :
      ∀ p : Pair, 0 < (M.typeLaw (pairHi p) (hiPos p)).toReal)
    (hscore_hi_pos :
      ∀ p : Pair, 0 < M.score (hiPos p) - a p)
    (hmass_hi_neg :
      ∀ p : Pair, 0 < (M.typeLaw (pairHi p) (hiNeg p)).toReal)
    (hscore_hi_neg :
      ∀ p : Pair, M.score (hiNeg p) - a p < 0)
    (hmass_lo_pos :
      ∀ p : Pair, 0 < (M.typeLaw (pairLo p) (loPos p)).toReal)
    (hscore_lo_pos :
      ∀ p : Pair, 0 < a p - M.score (loPos p))
    (hmass_lo_neg :
      ∀ p : Pair, 0 < (M.typeLaw (pairLo p) (loNeg p)).toReal)
    (hscore_lo_neg :
      ∀ p : Pair, a p - M.score (loNeg p) < 0)
    (hadj_min :
      ∀ i : Adj,
        pairwiseSellerThresholdRate M sampleRate
            (pairHi (adjacentPair iMin)) (pairLo (adjacentPair iMin)) ≤
          pairwiseSellerThresholdRate M sampleRate
            (pairHi (adjacentPair i)) (pairLo (adjacentPair i)))
    (hadj_dominates :
      ∀ p : Pair, ∃ i : Adj,
        pairwiseSellerThresholdRate M sampleRate
            (pairHi (adjacentPair i)) (pairLo (adjacentPair i)) ≤
          pairwiseSellerThresholdRate M sampleRate (pairHi p) (pairLo p)) :
    HasExponentialRate
      (fun k : ℕ =>
        1 - finiteFloorPkObjective M sampleRate pairHi pairLo weight k)
      (pairwiseSellerThresholdRate M sampleRate
        (pairHi (adjacentPair iMin)) (pairLo (adjacentPair iMin))) :=
  finiteFloorPkObjective_oneSub_hasExponentialRate_of_adjacent_logMGF_derivative_minimizers_of_pos_neg_atoms
    M sampleRate pairHi pairLo weight adjacentPair
    hweight_nonneg hweight_sum iMin hweight_pos hgHi hgLo
    a z hz hderiv_hi hderiv_lo hthreshold_eq
    hiPos hiNeg loPos loNeg
    hmass_hi_pos hscore_hi_pos hmass_hi_neg hscore_hi_neg
    hmass_lo_pos hscore_lo_pos hmass_lo_neg hscore_lo_neg
    hadj_min hadj_dominates

/--
Theorem 1 arbitrary-real floor-count endpoint from per-pair common-dual
log-MGF derivative data, source-level threshold minimizers, and compact
two-sided support. This is the canonical weighted/adjacent paper-facing
endpoint for the finite rating-scale model when the per-pair threshold
minimizer fact is treated as source regularity.
-/
theorem theorem1_floor_weighted_objective_oneSub_exact_rate_from_adjacent_logMGF_derivative_threshold_minimizers_of_straddling_support
    {Seller Rating Pair Adj : Type*} [Fintype Rating] [DecidableEq Rating]
    [Fintype Pair] [DecidableEq Pair]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
    (weight : Pair → ℝ)
    (adjacentPair : Adj → Pair)
    (hweight_nonneg : ∀ p, 0 ≤ weight p)
    (hweight_sum : ∑ p : Pair, weight p = 1)
    (iMin : Adj) (hweight_pos : 0 < weight (adjacentPair iMin))
    (hgHi : ∀ p : Pair, 0 < sampleRate (pairHi p))
    (hgLo : ∀ p : Pair, 0 < sampleRate (pairLo p))
    (a z : Pair → ℝ)
    (hz : ∀ p : Pair, z p ≤ 0)
    (hderiv_hi :
      ∀ p : Pair,
        HasDerivAt (fun t : ℝ => M.logMGF (pairHi p) t) (a p)
          (z p * (sampleRate (pairHi p))⁻¹))
    (hderiv_lo :
      ∀ p : Pair,
        HasDerivAt (fun t : ℝ => M.logMGF (pairLo p) t) (a p)
          (-(z p * (sampleRate (pairLo p))⁻¹)))
    (hthreshold_min :
      ∀ p : Pair, ∀ b : ℝ,
        M.pairwiseRateObjective sampleRate (pairHi p) (pairLo p) (a p) ≤
          M.pairwiseRateObjective sampleRate (pairHi p) (pairLo p) b)
    (hstraddle_hi :
      ∀ p : Pair, ratingLawStraddlesThreshold M (pairHi p) (a p))
    (hstraddle_lo :
      ∀ p : Pair, ratingLawStraddlesThreshold M (pairLo p) (a p))
    (hadj_min :
      ∀ i : Adj,
        pairwiseSellerThresholdRate M sampleRate
            (pairHi (adjacentPair iMin)) (pairLo (adjacentPair iMin)) ≤
          pairwiseSellerThresholdRate M sampleRate
            (pairHi (adjacentPair i)) (pairLo (adjacentPair i)))
    (hadj_dominates :
      ∀ p : Pair, ∃ i : Adj,
        pairwiseSellerThresholdRate M sampleRate
            (pairHi (adjacentPair i)) (pairLo (adjacentPair i)) ≤
          pairwiseSellerThresholdRate M sampleRate (pairHi p) (pairLo p)) :
    HasExponentialRate
      (fun k : ℕ =>
        1 - finiteFloorPkObjective M sampleRate pairHi pairLo weight k)
      (pairwiseSellerThresholdRate M sampleRate
        (pairHi (adjacentPair iMin)) (pairLo (adjacentPair iMin))) :=
  finiteFloorPkObjective_oneSub_hasExponentialRate_of_adjacent_logMGF_derivative_threshold_minimizers_of_straddling_support
    M sampleRate pairHi pairLo weight adjacentPair
    hweight_nonneg hweight_sum iMin hweight_pos hgHi hgLo
    a z hz hderiv_hi hderiv_lo hthreshold_min
    hstraddle_hi hstraddle_lo hadj_min hadj_dominates

/--
Theorem 1 finite-chain specialization.  Sellers are indexed by a strict finite
chain, comparison pairs are exactly `(theta_j, theta_i)` with `i < j`, and
the paper's final minimum is over adjacent pairs `(theta_{i+1}, theta_i)`.
-/
theorem theorem1_finite_chain_uniform_floor_objective_oneSub_exact_rate_from_adjacent_logMGF_derivative_threshold_minimizers_of_straddling_support
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    [DecidableEq (finiteChainOrderedPair n)]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n → ℝ)
    (hpositive_sample : ∀ θ : Fin n, 0 < sampleRate θ)
    (a z : finiteChainOrderedPair n → ℝ)
    (hz : ∀ p : finiteChainOrderedPair n, z p ≤ 0)
    (hderiv_hi :
      ∀ p : finiteChainOrderedPair n,
        HasDerivAt
          (fun t : ℝ => M.logMGF (finiteChainOrderedPairHi p) t) (a p)
          (z p * (sampleRate (finiteChainOrderedPairHi p))⁻¹))
    (hderiv_lo :
      ∀ p : finiteChainOrderedPair n,
        HasDerivAt
          (fun t : ℝ => M.logMGF (finiteChainOrderedPairLo p) t) (a p)
          (-(z p * (sampleRate (finiteChainOrderedPairLo p))⁻¹)))
    (hthreshold_min :
      ∀ p : finiteChainOrderedPair n, ∀ b : ℝ,
        M.pairwiseRateObjective sampleRate
            (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) (a p) ≤
          M.pairwiseRateObjective sampleRate
            (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) b)
    (hstraddle_hi :
      ∀ p : finiteChainOrderedPair n,
        ratingLawStraddlesThreshold M (finiteChainOrderedPairHi p) (a p))
    (hstraddle_lo :
      ∀ p : finiteChainOrderedPair n,
        ratingLawStraddlesThreshold M (finiteChainOrderedPairLo p) (a p))
    (iMin : finiteChainAdjacentIndex n)
    (hadj_min :
      ∀ i : finiteChainAdjacentIndex n,
        pairwiseSellerThresholdRate M sampleRate
            (finiteChainOrderedPairHi (finiteChainAdjacentPair iMin))
            (finiteChainOrderedPairLo (finiteChainAdjacentPair iMin)) ≤
          pairwiseSellerThresholdRate M sampleRate
            (finiteChainOrderedPairHi (finiteChainAdjacentPair i))
            (finiteChainOrderedPairLo (finiteChainAdjacentPair i)))
    (hadj_dominates :
      ∀ p : finiteChainOrderedPair n, ∃ i : finiteChainAdjacentIndex n,
        pairwiseSellerThresholdRate M sampleRate
            (finiteChainOrderedPairHi (finiteChainAdjacentPair i))
            (finiteChainOrderedPairLo (finiteChainAdjacentPair i)) ≤
          pairwiseSellerThresholdRate M sampleRate
            (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p)) :
    HasExponentialRate
      (fun k : ℕ =>
        1 - finiteUniformFloorPkObjective M sampleRate
          finiteChainOrderedPairHi finiteChainOrderedPairLo k)
      (pairwiseSellerThresholdRate M sampleRate
        (finiteChainOrderedPairHi (finiteChainAdjacentPair iMin))
        (finiteChainOrderedPairLo (finiteChainAdjacentPair iMin))) :=
  finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_adjacent_logMGF_derivative_threshold_minimizers_of_straddling_support
    M sampleRate hpositive_sample a z hz hderiv_hi hderiv_lo
    hthreshold_min hstraddle_hi hstraddle_lo iMin hadj_min hadj_dominates

/--
Theorem 1 finite-chain specialization with the adjacent-dominance step stated
as an interval-local threshold-rate predicate: for every pair `(theta_j,
theta_i)`, some adjacent pair between them has no larger threshold rate.
-/
theorem theorem1_finite_chain_uniform_floor_objective_oneSub_exact_rate_from_interval_adjacent_threshold_rate_dominance
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    [DecidableEq (finiteChainOrderedPair n)]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n → ℝ)
    (hpositive_sample : ∀ θ : Fin n, 0 < sampleRate θ)
    (a z : finiteChainOrderedPair n → ℝ)
    (hz : ∀ p : finiteChainOrderedPair n, z p ≤ 0)
    (hderiv_hi :
      ∀ p : finiteChainOrderedPair n,
        HasDerivAt
          (fun t : ℝ => M.logMGF (finiteChainOrderedPairHi p) t) (a p)
          (z p * (sampleRate (finiteChainOrderedPairHi p))⁻¹))
    (hderiv_lo :
      ∀ p : finiteChainOrderedPair n,
        HasDerivAt
          (fun t : ℝ => M.logMGF (finiteChainOrderedPairLo p) t) (a p)
          (-(z p * (sampleRate (finiteChainOrderedPairLo p))⁻¹)))
    (hthreshold_min :
      ∀ p : finiteChainOrderedPair n, ∀ b : ℝ,
        M.pairwiseRateObjective sampleRate
            (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) (a p) ≤
          M.pairwiseRateObjective sampleRate
            (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) b)
    (hstraddle_hi :
      ∀ p : finiteChainOrderedPair n,
        ratingLawStraddlesThreshold M (finiteChainOrderedPairHi p) (a p))
    (hstraddle_lo :
      ∀ p : finiteChainOrderedPair n,
        ratingLawStraddlesThreshold M (finiteChainOrderedPairLo p) (a p))
    (iMin : finiteChainAdjacentIndex n)
    (hadj_min :
      finiteChainAdjacentThresholdRateMinimizer M sampleRate iMin)
    (hadj_dominates :
      finiteChainIntervalAdjacentThresholdRatesDominate M sampleRate) :
    HasExponentialRate
      (fun k : ℕ =>
        1 - finiteUniformFloorPkObjective M sampleRate
          finiteChainOrderedPairHi finiteChainOrderedPairLo k)
      (finiteChainAdjacentThresholdRate M sampleRate iMin) :=
  finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_interval_adjacent_threshold_rate_dominance
    M sampleRate hpositive_sample a z hz hderiv_hi hderiv_lo hthreshold_min
    hstraddle_hi hstraddle_lo iMin hadj_min hadj_dominates

/--
Theorem 1 finite-chain specialization with the exponent in the paper's
displayed form: the finite minimum over adjacent-pair threshold rates.  The
adjacent minimizer is selected internally.
-/
theorem theorem1_finite_chain_uniform_floor_objective_oneSub_exact_min_adjacent_rate_from_interval_adjacent_threshold_rate_dominance
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    [DecidableEq (finiteChainOrderedPair n)]
    [Nonempty (finiteChainAdjacentIndex n)]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n → ℝ)
    (hpositive_sample : ∀ θ : Fin n, 0 < sampleRate θ)
    (a z : finiteChainOrderedPair n → ℝ)
    (hz : ∀ p : finiteChainOrderedPair n, z p ≤ 0)
    (hderiv_hi :
      ∀ p : finiteChainOrderedPair n,
        HasDerivAt
          (fun t : ℝ => M.logMGF (finiteChainOrderedPairHi p) t) (a p)
          (z p * (sampleRate (finiteChainOrderedPairHi p))⁻¹))
    (hderiv_lo :
      ∀ p : finiteChainOrderedPair n,
        HasDerivAt
          (fun t : ℝ => M.logMGF (finiteChainOrderedPairLo p) t) (a p)
          (-(z p * (sampleRate (finiteChainOrderedPairLo p))⁻¹)))
    (hthreshold_min :
      ∀ p : finiteChainOrderedPair n, ∀ b : ℝ,
        M.pairwiseRateObjective sampleRate
            (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) (a p) ≤
          M.pairwiseRateObjective sampleRate
            (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) b)
    (hstraddle_hi :
      ∀ p : finiteChainOrderedPair n,
        ratingLawStraddlesThreshold M (finiteChainOrderedPairHi p) (a p))
    (hstraddle_lo :
      ∀ p : finiteChainOrderedPair n,
        ratingLawStraddlesThreshold M (finiteChainOrderedPairLo p) (a p))
    (hadj_dominates :
      finiteChainIntervalAdjacentThresholdRatesDominate M sampleRate) :
    HasExponentialRate
      (fun k : ℕ =>
        1 - finiteUniformFloorPkObjective M sampleRate
          finiteChainOrderedPairHi finiteChainOrderedPairLo k)
      (minFiniteChainAdjacentThresholdRate M sampleRate) :=
  finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_interval_adjacent_threshold_rate_dominance_min_rate
    M sampleRate hpositive_sample a z hz hderiv_hi hderiv_lo hthreshold_min
    hstraddle_hi hstraddle_lo hadj_dominates

/--
Theorem 1 finite-chain specialization with the exponent in the paper's
displayed form, deriving adjacent threshold-rate dominance from interval-local
floor-count left-tail event bounds.
-/
theorem theorem1_finite_chain_uniform_floor_objective_oneSub_exact_min_adjacent_rate_from_interval_floor_leftTail_event_bounds
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    [DecidableEq (finiteChainOrderedPair n)]
    [Nonempty (finiteChainAdjacentIndex n)]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n → ℝ)
    (hpositive_sample : ∀ θ : Fin n, 0 < sampleRate θ)
    (a z : finiteChainOrderedPair n → ℝ)
    (hz : ∀ p : finiteChainOrderedPair n, z p ≤ 0)
    (hderiv_hi :
      ∀ p : finiteChainOrderedPair n,
        HasDerivAt
          (fun t : ℝ => M.logMGF (finiteChainOrderedPairHi p) t) (a p)
          (z p * (sampleRate (finiteChainOrderedPairHi p))⁻¹))
    (hderiv_lo :
      ∀ p : finiteChainOrderedPair n,
        HasDerivAt
          (fun t : ℝ => M.logMGF (finiteChainOrderedPairLo p) t) (a p)
          (-(z p * (sampleRate (finiteChainOrderedPairLo p))⁻¹)))
    (hthreshold_min :
      ∀ p : finiteChainOrderedPair n, ∀ b : ℝ,
        M.pairwiseRateObjective sampleRate
            (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) (a p) ≤
          M.pairwiseRateObjective sampleRate
            (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) b)
    (hstraddle_hi :
      ∀ p : finiteChainOrderedPair n,
        ratingLawStraddlesThreshold M (finiteChainOrderedPairHi p) (a p))
    (hstraddle_lo :
      ∀ p : finiteChainOrderedPair n,
        ratingLawStraddlesThreshold M (finiteChainOrderedPairLo p) (a p))
    (hinterval_bound :
      ∀ p : finiteChainOrderedPair n,
        ∀ᶠ k in Filter.atTop,
          twoSampleFloorScoreGapLeftTailProb M sampleRate
              (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) k ≤
            ∑ m : AppliedModelingLib.FiniteIntervalAdjacentIndex
                (finiteChainOrderedPairLo p) (finiteChainOrderedPairHi p),
              twoSampleFloorScoreGapLeftTailProb M sampleRate m.succ m.1 k) :
    HasExponentialRate
      (fun k : ℕ =>
        1 - finiteUniformFloorPkObjective M sampleRate
          finiteChainOrderedPairHi finiteChainOrderedPairLo k)
      (minFiniteChainAdjacentThresholdRate M sampleRate) :=
  finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_interval_floor_leftTail_event_bounds_min_rate
    M sampleRate hpositive_sample a z hz hderiv_hi hderiv_lo hthreshold_min
    hstraddle_hi hstraddle_lo hinterval_bound

/--
Theorem 1 finite-chain specialization with the exponent in the paper's
displayed form, using a joint finite score law whose two-coordinate marginals
agree with the pairwise floor-count left-tail probabilities.
-/
theorem theorem1_finite_chain_uniform_floor_objective_oneSub_exact_min_adjacent_rate_from_joint_score_marginals
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    [DecidableEq (finiteChainOrderedPair n)]
    [Nonempty (finiteChainAdjacentIndex n)]
    {Ω : ℕ → Type*} [∀ k : ℕ, Fintype (Ω k)]
    [∀ k : ℕ, DecidableEq (Ω k)]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n → ℝ)
    (hpositive_sample : ∀ θ : Fin n, 0 < sampleRate θ)
    (a z : finiteChainOrderedPair n → ℝ)
    (hz : ∀ p : finiteChainOrderedPair n, z p ≤ 0)
    (hderiv_hi :
      ∀ p : finiteChainOrderedPair n,
        HasDerivAt
          (fun t : ℝ => M.logMGF (finiteChainOrderedPairHi p) t) (a p)
          (z p * (sampleRate (finiteChainOrderedPairHi p))⁻¹))
    (hderiv_lo :
      ∀ p : finiteChainOrderedPair n,
        HasDerivAt
          (fun t : ℝ => M.logMGF (finiteChainOrderedPairLo p) t) (a p)
          (-(z p * (sampleRate (finiteChainOrderedPairLo p))⁻¹)))
    (hthreshold_min :
      ∀ p : finiteChainOrderedPair n, ∀ b : ℝ,
        M.pairwiseRateObjective sampleRate
            (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) (a p) ≤
          M.pairwiseRateObjective sampleRate
            (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) b)
    (hstraddle_hi :
      ∀ p : finiteChainOrderedPair n,
        ratingLawStraddlesThreshold M (finiteChainOrderedPairHi p) (a p))
    (hstraddle_lo :
      ∀ p : finiteChainOrderedPair n,
        ratingLawStraddlesThreshold M (finiteChainOrderedPairLo p) (a p))
    (μ : ∀ k : ℕ, PMF (Ω k)) (score : ∀ k : ℕ, Ω k → Fin n → ℝ)
    (hmarginal :
      ∀ (p : finiteChainOrderedPair n) (k : ℕ),
        twoSampleFloorScoreGapLeftTailProb M sampleRate
            (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) k =
          AppliedModelingLib.pmfProb (μ k)
            (fun ω => score k ω (finiteChainOrderedPairHi p) ≤
              score k ω (finiteChainOrderedPairLo p))) :
    HasExponentialRate
      (fun k : ℕ =>
        1 - finiteUniformFloorPkObjective M sampleRate
          finiteChainOrderedPairHi finiteChainOrderedPairLo k)
      (minFiniteChainAdjacentThresholdRate M sampleRate) :=
  finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_joint_score_marginals_min_rate
    M sampleRate hpositive_sample a z hz hderiv_hi hderiv_lo hthreshold_min
    hstraddle_hi hstraddle_lo μ score hmarginal

/--
Theorem 1 finite-chain specialization for the concrete independent joint
floor-rating law over all seller samples.  The marginal hypothesis states that
two-coordinate projections agree with the paper's pairwise floor-count
left-tail laws.
-/
theorem theorem1_finite_chain_uniform_floor_objective_oneSub_exact_min_adjacent_rate_from_joint_floor_rating_marginals
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    [DecidableEq (finiteChainOrderedPair n)]
    [Nonempty (finiteChainAdjacentIndex n)]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n → ℝ)
    (hpositive_sample : ∀ θ : Fin n, 0 < sampleRate θ)
    (a z : finiteChainOrderedPair n → ℝ)
    (hz : ∀ p : finiteChainOrderedPair n, z p ≤ 0)
    (hderiv_hi :
      ∀ p : finiteChainOrderedPair n,
        HasDerivAt
          (fun t : ℝ => M.logMGF (finiteChainOrderedPairHi p) t) (a p)
          (z p * (sampleRate (finiteChainOrderedPairHi p))⁻¹))
    (hderiv_lo :
      ∀ p : finiteChainOrderedPair n,
        HasDerivAt
          (fun t : ℝ => M.logMGF (finiteChainOrderedPairLo p) t) (a p)
          (-(z p * (sampleRate (finiteChainOrderedPairLo p))⁻¹)))
    (hthreshold_min :
      ∀ p : finiteChainOrderedPair n, ∀ b : ℝ,
        M.pairwiseRateObjective sampleRate
            (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) (a p) ≤
          M.pairwiseRateObjective sampleRate
            (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) b)
    (hstraddle_hi :
      ∀ p : finiteChainOrderedPair n,
        ratingLawStraddlesThreshold M (finiteChainOrderedPairHi p) (a p))
    (hstraddle_lo :
      ∀ p : finiteChainOrderedPair n,
        ratingLawStraddlesThreshold M (finiteChainOrderedPairLo p) (a p))
    (hmarginal :
      ∀ (p : finiteChainOrderedPair n) (k : ℕ),
        twoSampleFloorScoreGapLeftTailProb M sampleRate
            (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) k =
          AppliedModelingLib.pmfProb (finiteChainJointFloorRatingLaw M sampleRate k)
            (fun sample =>
              finiteChainJointFloorAverageScore M sampleRate k sample
                  (finiteChainOrderedPairHi p) ≤
                finiteChainJointFloorAverageScore M sampleRate k sample
                  (finiteChainOrderedPairLo p))) :
    HasExponentialRate
      (fun k : ℕ =>
        1 - finiteUniformFloorPkObjective M sampleRate
          finiteChainOrderedPairHi finiteChainOrderedPairLo k)
      (minFiniteChainAdjacentThresholdRate M sampleRate) :=
  finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_joint_floor_rating_marginals_min_rate
    M sampleRate hpositive_sample a z hz hderiv_hi hderiv_lo hthreshold_min
    hstraddle_hi hstraddle_lo hmarginal

/--
Theorem 1 finite-chain specialization for the concrete independent joint
floor-rating law over all seller samples.  The adjacent-pair reduction is
derived internally from the joint law's two-coordinate marginals and the
deterministic adjacent-inversion inclusion.
-/
theorem theorem1_finite_chain_uniform_floor_objective_oneSub_exact_min_adjacent_rate_from_joint_floor_rating_law
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    [DecidableEq (finiteChainOrderedPair n)]
    [Nonempty (finiteChainAdjacentIndex n)]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n → ℝ)
    (hpositive_sample : ∀ θ : Fin n, 0 < sampleRate θ)
    (a z : finiteChainOrderedPair n → ℝ)
    (hz : ∀ p : finiteChainOrderedPair n, z p ≤ 0)
    (hderiv_hi :
      ∀ p : finiteChainOrderedPair n,
        HasDerivAt
          (fun t : ℝ => M.logMGF (finiteChainOrderedPairHi p) t) (a p)
          (z p * (sampleRate (finiteChainOrderedPairHi p))⁻¹))
    (hderiv_lo :
      ∀ p : finiteChainOrderedPair n,
        HasDerivAt
          (fun t : ℝ => M.logMGF (finiteChainOrderedPairLo p) t) (a p)
          (-(z p * (sampleRate (finiteChainOrderedPairLo p))⁻¹)))
    (hthreshold_min :
      ∀ p : finiteChainOrderedPair n, ∀ b : ℝ,
        M.pairwiseRateObjective sampleRate
            (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) (a p) ≤
          M.pairwiseRateObjective sampleRate
            (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) b)
    (hstraddle_hi :
      ∀ p : finiteChainOrderedPair n,
        ratingLawStraddlesThreshold M (finiteChainOrderedPairHi p) (a p))
    (hstraddle_lo :
      ∀ p : finiteChainOrderedPair n,
        ratingLawStraddlesThreshold M (finiteChainOrderedPairLo p) (a p)) :
    HasExponentialRate
      (fun k : ℕ =>
        1 - finiteUniformFloorPkObjective M sampleRate
          finiteChainOrderedPairHi finiteChainOrderedPairLo k)
      (minFiniteChainAdjacentThresholdRate M sampleRate) :=
  finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_joint_floor_rating_law_min_rate
    M sampleRate hpositive_sample a z hz hderiv_hi hderiv_lo hthreshold_min
    hstraddle_hi hstraddle_lo

/--
Theorem 1 finite-chain specialization for the concrete independent joint
floor-rating law from exact per-pair source-threshold rate identities.  This
keeps the adjacent-pair reduction internal to the joint law while exposing the
pairwise source-rate equality directly, instead of a stronger minimizer
predicate.
-/
theorem theorem1_finite_chain_uniform_floor_objective_oneSub_exact_min_adjacent_rate_from_joint_floor_rating_law_threshold_eq
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    [DecidableEq (finiteChainOrderedPair n)]
    [Nonempty (finiteChainAdjacentIndex n)]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n → ℝ)
    (hpositive_sample : ∀ θ : Fin n, 0 < sampleRate θ)
    (a z : finiteChainOrderedPair n → ℝ)
    (hz : ∀ p : finiteChainOrderedPair n, z p ≤ 0)
    (hderiv_hi :
      ∀ p : finiteChainOrderedPair n,
        HasDerivAt
          (fun t : ℝ => M.logMGF (finiteChainOrderedPairHi p) t) (a p)
          (z p * (sampleRate (finiteChainOrderedPairHi p))⁻¹))
    (hderiv_lo :
      ∀ p : finiteChainOrderedPair n,
        HasDerivAt
          (fun t : ℝ => M.logMGF (finiteChainOrderedPairLo p) t) (a p)
          (-(z p * (sampleRate (finiteChainOrderedPairLo p))⁻¹)))
    (hthreshold_eq :
      ∀ p : finiteChainOrderedPair n,
        M.pairwiseRateObjective sampleRate
            (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) (a p) =
          pairwiseSellerThresholdRate M sampleRate
            (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p))
    (hstraddle_hi :
      ∀ p : finiteChainOrderedPair n,
        ratingLawStraddlesThreshold M (finiteChainOrderedPairHi p) (a p))
    (hstraddle_lo :
      ∀ p : finiteChainOrderedPair n,
        ratingLawStraddlesThreshold M (finiteChainOrderedPairLo p) (a p)) :
    HasExponentialRate
      (fun k : ℕ =>
        1 - finiteUniformFloorPkObjective M sampleRate
          finiteChainOrderedPairHi finiteChainOrderedPairLo k)
      (minFiniteChainAdjacentThresholdRate M sampleRate) :=
  finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_joint_floor_rating_law_min_rate_of_threshold_eq
    M sampleRate hpositive_sample a z hz hderiv_hi hderiv_lo hthreshold_eq
    hstraddle_hi hstraddle_lo

/--
Theorem 1 finite-chain specialization from exact source-threshold rate
identities and primitive finite support at common bottom/top ratings.  This
derives the two-sided straddling support required by the finite Cramer lower
bound from the displayed log-MGF derivative equations.
-/
theorem theorem1_finite_chain_uniform_floor_objective_oneSub_exact_min_adjacent_rate_from_threshold_rate_eq_and_score_bounds
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    [DecidableEq (finiteChainOrderedPair n)]
    [Nonempty (finiteChainAdjacentIndex n)]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n → ℝ)
    (hpositive_sample : ∀ θ : Fin n, 0 < sampleRate θ)
    (a z : finiteChainOrderedPair n → ℝ)
    (hz : ∀ p : finiteChainOrderedPair n, z p ≤ 0)
    (hderiv_hi :
      ∀ p : finiteChainOrderedPair n,
        HasDerivAt
          (fun t : ℝ => M.logMGF (finiteChainOrderedPairHi p) t) (a p)
          (z p * (sampleRate (finiteChainOrderedPairHi p))⁻¹))
    (hderiv_lo :
      ∀ p : finiteChainOrderedPair n,
        HasDerivAt
          (fun t : ℝ => M.logMGF (finiteChainOrderedPairLo p) t) (a p)
          (-(z p * (sampleRate (finiteChainOrderedPairLo p))⁻¹)))
    (hthreshold_eq :
      ∀ p : finiteChainOrderedPair n,
        M.pairwiseRateObjective sampleRate
            (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) (a p) =
          pairwiseSellerThresholdRate M sampleRate
            (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p))
    (rLow rHigh : Rating)
    (hmass_low : ∀ θ : Fin n, 0 < (M.typeLaw θ rLow).toReal)
    (hmass_high : ∀ θ : Fin n, 0 < (M.typeLaw θ rHigh).toReal)
    (hscore_low_le : ∀ r : Rating, M.score rLow ≤ M.score r)
    (hscore_le_high : ∀ r : Rating, M.score r ≤ M.score rHigh)
    (hscore_lt : M.score rLow < M.score rHigh) :
    HasExponentialRate
      (fun k : ℕ =>
        1 - finiteUniformFloorPkObjective M sampleRate
          finiteChainOrderedPairHi finiteChainOrderedPairLo k)
      (minFiniteChainAdjacentThresholdRate M sampleRate) :=
  finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_joint_floor_rating_law_min_rate_of_pairwise_threshold_rate_regularity
    M sampleRate hpositive_sample
    (PairwiseThresholdRateRegularity.of_threshold_rate_eq_and_score_bounds
      (M := M) (sampleRate := sampleRate)
      (pairHi := finiteChainOrderedPairHi)
      (pairLo := finiteChainOrderedPairLo)
      a z hz hderiv_hi hderiv_lo hthreshold_eq rLow rHigh
      (fun p => hmass_low (finiteChainOrderedPairHi p))
      (fun p => hmass_high (finiteChainOrderedPairHi p))
      (fun p => hmass_low (finiteChainOrderedPairLo p))
      (fun p => hmass_high (finiteChainOrderedPairLo p))
      hscore_low_le hscore_le_high hscore_lt)

/--
Theorem 1 finite-chain floor-count endpoint at the displayed adjacent
pairwise-objective rate.  This proves the finite large-deviation and
aggregation layers from derivative witnesses and primitive bottom/top rating
support, without assuming that the displayed thresholds have already been
identified with the paper's source threshold-rate infimum.
-/
theorem theorem1_finite_chain_uniform_floor_objective_oneSub_exact_adjacent_objective_rate_from_logMGF_derivatives_and_score_bounds
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    [DecidableEq (finiteChainOrderedPair n)]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n → ℝ)
    (hpositive_sample : ∀ θ : Fin n, 0 < sampleRate θ)
    (a z : finiteChainOrderedPair n → ℝ)
    (hz : ∀ p : finiteChainOrderedPair n, z p ≤ 0)
    (hderiv_hi :
      ∀ p : finiteChainOrderedPair n,
        HasDerivAt
          (fun t : ℝ => M.logMGF (finiteChainOrderedPairHi p) t) (a p)
          (z p * (sampleRate (finiteChainOrderedPairHi p))⁻¹))
    (hderiv_lo :
      ∀ p : finiteChainOrderedPair n,
        HasDerivAt
          (fun t : ℝ => M.logMGF (finiteChainOrderedPairLo p) t) (a p)
          (-(z p * (sampleRate (finiteChainOrderedPairLo p))⁻¹)))
    (rLow rHigh : Rating)
    (hmass_low : ∀ θ : Fin n, 0 < (M.typeLaw θ rLow).toReal)
    (hmass_high : ∀ θ : Fin n, 0 < (M.typeLaw θ rHigh).toReal)
    (hscore_low_le : ∀ r : Rating, M.score rLow ≤ M.score r)
    (hscore_le_high : ∀ r : Rating, M.score r ≤ M.score rHigh)
    (hscore_lt : M.score rLow < M.score rHigh)
    (iMin : finiteChainAdjacentIndex n)
    (hadj_min :
      ∀ i : finiteChainAdjacentIndex n,
        M.pairwiseRateObjective sampleRate
            (finiteChainOrderedPairHi (finiteChainAdjacentPair iMin))
            (finiteChainOrderedPairLo (finiteChainAdjacentPair iMin))
            (a (finiteChainAdjacentPair iMin)) ≤
          M.pairwiseRateObjective sampleRate
            (finiteChainOrderedPairHi (finiteChainAdjacentPair i))
            (finiteChainOrderedPairLo (finiteChainAdjacentPair i))
            (a (finiteChainAdjacentPair i)))
    (hadj_dominates :
      ∀ p : finiteChainOrderedPair n, ∃ i : finiteChainAdjacentIndex n,
        M.pairwiseRateObjective sampleRate
            (finiteChainOrderedPairHi (finiteChainAdjacentPair i))
            (finiteChainOrderedPairLo (finiteChainAdjacentPair i))
            (a (finiteChainAdjacentPair i)) ≤
          M.pairwiseRateObjective sampleRate
            (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) (a p)) :
    HasExponentialRate
      (fun k : ℕ =>
        1 - finiteUniformFloorPkObjective M sampleRate
          finiteChainOrderedPairHi finiteChainOrderedPairLo k)
      (M.pairwiseRateObjective sampleRate
        (finiteChainOrderedPairHi (finiteChainAdjacentPair iMin))
        (finiteChainOrderedPairLo (finiteChainAdjacentPair iMin))
        (a (finiteChainAdjacentPair iMin))) := by
  letI : Nonempty (finiteChainOrderedPair n) := ⟨finiteChainAdjacentPair iMin⟩
  simpa [finiteUniformFloorPkObjective] using
    finiteFloorPkObjective_oneSub_hasExponentialRate_of_adjacent_logMGF_derivative_objective_rates_of_straddling_support
      (Adj := finiteChainAdjacentIndex n)
      M sampleRate finiteChainOrderedPairHi finiteChainOrderedPairLo
      (uniformPairWeight (finiteChainOrderedPair n))
      finiteChainAdjacentPair
      (uniformPairWeight_nonneg (finiteChainOrderedPair n))
      (uniformPairWeight_sum_eq_one (finiteChainOrderedPair n))
      iMin
      (uniformPairWeight_pos
        (finiteChainOrderedPair n) (finiteChainAdjacentPair iMin))
      (fun p => hpositive_sample (finiteChainOrderedPairHi p))
      (fun p => hpositive_sample (finiteChainOrderedPairLo p))
      a z hz hderiv_hi hderiv_lo
      (fun p =>
        ratingLawStraddlesThreshold_of_logMGF_hasDerivAt_of_score_bounds
          M (finiteChainOrderedPairHi p) (hderiv_hi p)
          (hmass_low (finiteChainOrderedPairHi p))
          (hmass_high (finiteChainOrderedPairHi p))
          hscore_low_le hscore_le_high hscore_lt)
      (fun p =>
        ratingLawStraddlesThreshold_of_logMGF_hasDerivAt_of_score_bounds
          M (finiteChainOrderedPairLo p) (hderiv_lo p)
          (hmass_low (finiteChainOrderedPairLo p))
          (hmass_high (finiteChainOrderedPairLo p))
          hscore_low_le hscore_le_high hscore_lt)
      hadj_min hadj_dominates

/--
Theorem 1 finite-chain floor-count endpoint at the finite minimum over adjacent
displayed pairwise-objective rates.  The concrete joint floor-rating law and
adjacent-pair reduction are proved internally; common-dual derivative data
gives the pairwise objective certificates, and bottom/top rating support gives
the two-sided support needed by the finite Cramer lower bound.
-/
theorem theorem1_finite_chain_uniform_floor_objective_oneSub_exact_min_adjacent_objective_rate_from_joint_floor_rating_law_logMGF_derivatives_and_score_bounds
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    [DecidableEq (finiteChainOrderedPair n)]
    [Nonempty (finiteChainAdjacentIndex n)]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n → ℝ)
    (hpositive_sample : ∀ θ : Fin n, 0 < sampleRate θ)
    (a z : finiteChainOrderedPair n → ℝ)
    (hz : ∀ p : finiteChainOrderedPair n, z p ≤ 0)
    (hderiv_hi :
      ∀ p : finiteChainOrderedPair n,
        HasDerivAt
          (fun t : ℝ => M.logMGF (finiteChainOrderedPairHi p) t) (a p)
          (z p * (sampleRate (finiteChainOrderedPairHi p))⁻¹))
    (hderiv_lo :
      ∀ p : finiteChainOrderedPair n,
        HasDerivAt
          (fun t : ℝ => M.logMGF (finiteChainOrderedPairLo p) t) (a p)
          (-(z p * (sampleRate (finiteChainOrderedPairLo p))⁻¹)))
    (rLow rHigh : Rating)
    (hmass_low : ∀ θ : Fin n, 0 < (M.typeLaw θ rLow).toReal)
    (hmass_high : ∀ θ : Fin n, 0 < (M.typeLaw θ rHigh).toReal)
    (hscore_low_le : ∀ r : Rating, M.score rLow ≤ M.score r)
    (hscore_le_high : ∀ r : Rating, M.score r ≤ M.score rHigh)
    (hscore_lt : M.score rLow < M.score rHigh) :
    HasExponentialRate
      (fun k : ℕ =>
        1 - finiteUniformFloorPkObjective M sampleRate
          finiteChainOrderedPairHi finiteChainOrderedPairLo k)
      (minFiniteChainAdjacentObjectiveRate M sampleRate a) :=
  finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_joint_floor_rating_law_min_objective_rate_of_score_bounds
    M sampleRate hpositive_sample a z hz hderiv_hi hderiv_lo
    rLow rHigh hmass_low hmass_high hscore_low_le hscore_le_high hscore_lt

/--
Theorem 1 support-safe adjacent-rate identification: at the same common-dual
derivative thresholds used by the finite objective endpoint, the extended
source adjacent threshold-rate minimum equals the displayed real adjacent
objective minimum.
Source status: Derived source-rate identification.
Source note: This is the support-safe finite-rating version of the paper's
displayed adjacent objective rate.
-/
theorem theorem1_finite_chain_adjacent_threshold_rate_top_min_eq_displayed_objective_min_of_logMGF_derivatives
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    [Nonempty (finiteChainAdjacentIndex n)]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n → ℝ)
    (hpositive_sample : ∀ θ : Fin n, 0 < sampleRate θ)
    (a z : finiteChainOrderedPair n → ℝ)
    (hderiv_hi :
      ∀ p : finiteChainOrderedPair n,
        HasDerivAt
          (fun t : ℝ => M.logMGF (finiteChainOrderedPairHi p) t) (a p)
          (z p * (sampleRate (finiteChainOrderedPairHi p))⁻¹))
    (hderiv_lo :
      ∀ p : finiteChainOrderedPair n,
        HasDerivAt
          (fun t : ℝ => M.logMGF (finiteChainOrderedPairLo p) t) (a p)
          (-(z p * (sampleRate (finiteChainOrderedPairLo p))⁻¹))) :
    minFiniteChainAdjacentThresholdRateTop M sampleRate =
      (minFiniteChainAdjacentObjectiveRate M sampleRate a : WithTop ℝ) :=
  minFiniteChainAdjacentThresholdRateTop_eq_coe_minFiniteChainAdjacentObjectiveRate_of_common_logMGF_derivatives
    M sampleRate hpositive_sample a z hderiv_hi hderiv_lo

/--
Theorem 1 support-safe endpoint from pairwise finite-support LDP certificates.
This is the source-shaped closure target for the paper's Appendix C
large-deviation/Laplace step: the joint floor-rating law and adjacent
aggregation are internal, while the only supplied analytic data is an exact
pairwise LDP at each support-safe threshold rate.
-/
theorem theorem1_finite_chain_uniform_floor_objective_oneSub_extended_min_adjacent_threshold_rate_from_pairwise_top_ldp_certificates
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    [DecidableEq (finiteChainOrderedPair n)]
    [Nonempty (finiteChainAdjacentIndex n)]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n → ℝ)
    (C :
      theorem1PairwiseThresholdRateTopLdpCertificate M sampleRate
        finiteChainOrderedPairHi finiteChainOrderedPairLo) :
    HasExtendedExponentialRate
      (fun k : ℕ =>
        1 - finiteUniformFloorPkObjective M sampleRate
          finiteChainOrderedPairHi finiteChainOrderedPairLo k)
      (minFiniteChainAdjacentThresholdRateTop M sampleRate) :=
  finiteChainUniformFloorPkObjective_oneSub_hasExtendedExponentialRate_of_joint_floor_rating_law_min_threshold_rate_top_of_pairwise_ldp_certificates
    M sampleRate C

/-- Theorem 1 support-safe endpoint from the paper-facing threshold-rate regularity package. -/
theorem theorem1_finite_chain_uniform_floor_objective_oneSub_extended_min_adjacent_threshold_rate_from_pairwise_threshold_rate_regularity
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    [DecidableEq (finiteChainOrderedPair n)]
    [Nonempty (finiteChainAdjacentIndex n)]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n → ℝ)
    (hpositive_sample : ∀ θ : Fin n, 0 < sampleRate θ)
    (C :
      theorem1PairwiseThresholdRateRegularity M sampleRate
        finiteChainOrderedPairHi finiteChainOrderedPairLo) :
    HasExtendedExponentialRate
      (fun k : ℕ =>
        1 - finiteUniformFloorPkObjective M sampleRate
          finiteChainOrderedPairHi finiteChainOrderedPairLo k)
      (minFiniteChainAdjacentThresholdRateTop M sampleRate) :=
  finiteChainUniformFloorPkObjective_oneSub_hasExtendedExponentialRate_of_joint_floor_rating_law_min_threshold_rate_top_of_pairwise_threshold_rate_regularity
    M sampleRate hpositive_sample C

/--
Theorem 1 support-safe endpoint from source-mean ordering and primitive
bottom/top support.  For each ordered comparison pair, Lean derives the
stationary Chernoff dual and pairwise support-safe LDP certificate internally.
-/
theorem theorem1_finite_chain_uniform_floor_objective_oneSub_extended_min_adjacent_threshold_rate_from_expected_score_gap_and_common_extreme_support
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    [DecidableEq (finiteChainOrderedPair n)]
    [Nonempty (finiteChainAdjacentIndex n)]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n → ℝ)
    (hpositive_sample : ∀ θ : Fin n, 0 < sampleRate θ)
    (hmean_gap :
      ∀ p : finiteChainOrderedPair n,
        AppliedModelingLib.pmfExp (M.typeLaw (finiteChainOrderedPairLo p)) M.score ≤
          AppliedModelingLib.pmfExp (M.typeLaw (finiteChainOrderedPairHi p)) M.score)
    (rLow rHigh : Rating)
    (hmass_low : ∀ θ : Fin n, 0 < (M.typeLaw θ rLow).toReal)
    (hmass_high : ∀ θ : Fin n, 0 < (M.typeLaw θ rHigh).toReal)
    (hscore_low_le : ∀ r : Rating, M.score rLow ≤ M.score r)
    (hscore_le_high : ∀ r : Rating, M.score r ≤ M.score rHigh)
    (hscore_lt : M.score rLow < M.score rHigh) :
    HasExtendedExponentialRate
      (fun k : ℕ =>
        1 - finiteUniformFloorPkObjective M sampleRate
          finiteChainOrderedPairHi finiteChainOrderedPairLo k)
      (minFiniteChainAdjacentThresholdRateTop M sampleRate) :=
  finiteChainUniformFloorPkObjective_oneSub_hasExtendedExponentialRate_of_joint_floor_rating_law_min_threshold_rate_top_of_expected_score_gap_and_common_extreme_support
    M sampleRate hpositive_sample hmean_gap rLow rHigh hmass_low hmass_high
    hscore_low_le hscore_le_high hscore_lt

/--
Theorem 1 support-safe endpoint from the paper's finite ordinal rating-scale
primitive: higher source types have weakly larger upper-tail rating
probabilities, scores are monotone on ratings, and the common bottom/top
ratings have positive mass.
-/
theorem theorem1_finite_chain_uniform_floor_objective_oneSub_extended_min_adjacent_threshold_rate_from_rating_tail_dominance_and_common_extreme_support
    {n m : ℕ}
    [DecidableEq (finiteChainOrderedPair n)]
    [Nonempty (finiteChainAdjacentIndex n)]
    (M : FiniteRatingLDPModel (Fin n) (Fin (m + 1)))
    (sampleRate : Fin n → ℝ)
    (hpositive_sample : ∀ θ : Fin n, 0 < sampleRate θ)
    (htail :
      ∀ p : finiteChainOrderedPair n, ∀ t : Fin (m + 1),
        AppliedModelingLib.pmfProb (M.typeLaw (finiteChainOrderedPairLo p))
            (fun r => t ≤ r) ≤
          AppliedModelingLib.pmfProb (M.typeLaw (finiteChainOrderedPairHi p))
            (fun r => t ≤ r))
    (hscore_mono : Monotone M.score)
    (hmass_low : ∀ θ : Fin n, 0 < (M.typeLaw θ 0).toReal)
    (hmass_high : ∀ θ : Fin n, 0 < (M.typeLaw θ (Fin.last m)).toReal)
    (hscore_lt : M.score 0 < M.score (Fin.last m)) :
    HasExtendedExponentialRate
      (fun k : ℕ =>
        1 - finiteUniformFloorPkObjective M sampleRate
          finiteChainOrderedPairHi finiteChainOrderedPairLo k)
      (minFiniteChainAdjacentThresholdRateTop M sampleRate) :=
  finiteChainUniformFloorPkObjective_oneSub_hasExtendedExponentialRate_of_joint_floor_rating_law_min_threshold_rate_top_of_rating_tail_dominance_and_common_extreme_support
    M sampleRate hpositive_sample htail hscore_mono hmass_low hmass_high
    hscore_lt

/--
Theorem 1 source-facing support-safe endpoint from the paper's finite ordinal
rating-scale primitive.  Full support of the ordinal rating law supplies the
bottom/top atom support needed by the finite-support lower-bound route.
Source status: Main source theorem endpoint.
Source note: This is the canonical finite-support Theorem 1 statement for the
paper's finite ordered rating model.
-/
theorem theorem1_finite_chain_uniform_floor_objective_oneSub_extended_min_adjacent_threshold_rate_from_rating_tail_dominance_and_full_support
    {n m : ℕ}
    [DecidableEq (finiteChainOrderedPair n)]
    [Nonempty (finiteChainAdjacentIndex n)]
    (M : FiniteRatingLDPModel (Fin n) (Fin (m + 1)))
    (sampleRate : Fin n → ℝ)
    (hpositive_sample : ∀ θ : Fin n, 0 < sampleRate θ)
    (htail :
      ∀ p : finiteChainOrderedPair n, ∀ t : Fin (m + 1),
        AppliedModelingLib.pmfProb (M.typeLaw (finiteChainOrderedPairLo p))
            (fun r => t ≤ r) ≤
          AppliedModelingLib.pmfProb (M.typeLaw (finiteChainOrderedPairHi p))
            (fun r => t ≤ r))
    (hscore_mono : Monotone M.score)
    (hfull_support : M.fullSupport)
    (hscore_lt : M.score 0 < M.score (Fin.last m)) :
    HasExtendedExponentialRate
      (fun k : ℕ =>
        1 - finiteUniformFloorPkObjective M sampleRate
          finiteChainOrderedPairHi finiteChainOrderedPairLo k)
      (minFiniteChainAdjacentThresholdRateTop M sampleRate) :=
  finiteChainUniformFloorPkObjective_oneSub_hasExtendedExponentialRate_of_joint_floor_rating_law_min_threshold_rate_top_of_rating_tail_dominance_and_full_support
    M sampleRate hpositive_sample htail hscore_mono hfull_support hscore_lt

/--
Theorem 1 support-safe extended-rate endpoint.  Under the finite-support
extended-rate convention, the concrete joint floor-rating law has exponential
rate equal to the adjacent source threshold-rate minimum.
-/
theorem theorem1_finite_chain_uniform_floor_objective_oneSub_extended_min_adjacent_threshold_rate_from_joint_floor_rating_law_logMGF_derivatives_and_score_bounds
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    [DecidableEq (finiteChainOrderedPair n)]
    [Nonempty (finiteChainAdjacentIndex n)]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n → ℝ)
    (hpositive_sample : ∀ θ : Fin n, 0 < sampleRate θ)
    (a z : finiteChainOrderedPair n → ℝ)
    (hz : ∀ p : finiteChainOrderedPair n, z p ≤ 0)
    (hderiv_hi :
      ∀ p : finiteChainOrderedPair n,
        HasDerivAt
          (fun t : ℝ => M.logMGF (finiteChainOrderedPairHi p) t) (a p)
          (z p * (sampleRate (finiteChainOrderedPairHi p))⁻¹))
    (hderiv_lo :
      ∀ p : finiteChainOrderedPair n,
        HasDerivAt
          (fun t : ℝ => M.logMGF (finiteChainOrderedPairLo p) t) (a p)
          (-(z p * (sampleRate (finiteChainOrderedPairLo p))⁻¹)))
    (rLow rHigh : Rating)
    (hmass_low : ∀ θ : Fin n, 0 < (M.typeLaw θ rLow).toReal)
    (hmass_high : ∀ θ : Fin n, 0 < (M.typeLaw θ rHigh).toReal)
    (hscore_low_le : ∀ r : Rating, M.score rLow ≤ M.score r)
    (hscore_le_high : ∀ r : Rating, M.score r ≤ M.score rHigh)
    (hscore_lt : M.score rLow < M.score rHigh) :
    HasExtendedExponentialRate
      (fun k : ℕ =>
        1 - finiteUniformFloorPkObjective M sampleRate
          finiteChainOrderedPairHi finiteChainOrderedPairLo k)
      (minFiniteChainAdjacentThresholdRateTop M sampleRate) :=
  finiteChainUniformFloorPkObjective_oneSub_hasExtendedExponentialRate_of_joint_floor_rating_law_min_threshold_rate_top_of_score_bounds
    M sampleRate hpositive_sample a z hz hderiv_hi hderiv_lo
    rLow rHigh hmass_low hmass_high hscore_low_le hscore_le_high hscore_lt

/--
Theorem 1 real-rate bridge from the support-safe endpoint. If the finite-support
extended adjacent threshold-rate minimum agrees with the paper's real adjacent
threshold-rate minimum, the support-safe theorem is exactly the paper's
real-valued exponential-rate statement.
Source status: Compatibility wrapper.
Source note: This optional row recovers the older all-real statement under an
explicit extended-rate equality condition; it is not the canonical endpoint.
-/
theorem theorem1_finite_chain_uniform_floor_objective_oneSub_exact_min_adjacent_threshold_rate_from_joint_floor_rating_law_logMGF_derivatives_and_score_bounds_of_extended_min_eq
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    [DecidableEq (finiteChainOrderedPair n)]
    [Nonempty (finiteChainAdjacentIndex n)]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n → ℝ)
    (hpositive_sample : ∀ θ : Fin n, 0 < sampleRate θ)
    (a z : finiteChainOrderedPair n → ℝ)
    (hz : ∀ p : finiteChainOrderedPair n, z p ≤ 0)
    (hderiv_hi :
      ∀ p : finiteChainOrderedPair n,
        HasDerivAt
          (fun t : ℝ => M.logMGF (finiteChainOrderedPairHi p) t) (a p)
          (z p * (sampleRate (finiteChainOrderedPairHi p))⁻¹))
    (hderiv_lo :
      ∀ p : finiteChainOrderedPair n,
        HasDerivAt
          (fun t : ℝ => M.logMGF (finiteChainOrderedPairLo p) t) (a p)
          (-(z p * (sampleRate (finiteChainOrderedPairLo p))⁻¹)))
    (rLow rHigh : Rating)
    (hmass_low : ∀ θ : Fin n, 0 < (M.typeLaw θ rLow).toReal)
    (hmass_high : ∀ θ : Fin n, 0 < (M.typeLaw θ rHigh).toReal)
    (hscore_low_le : ∀ r : Rating, M.score rLow ≤ M.score r)
    (hscore_le_high : ∀ r : Rating, M.score r ≤ M.score rHigh)
    (hscore_lt : M.score rLow < M.score rHigh)
    (hextended_min_eq :
      minFiniteChainAdjacentThresholdRateTop M sampleRate =
        (minFiniteChainAdjacentThresholdRate M sampleRate : WithTop ℝ)) :
    HasExponentialRate
      (fun k : ℕ =>
        1 - finiteUniformFloorPkObjective M sampleRate
          finiteChainOrderedPairHi finiteChainOrderedPairLo k)
      (minFiniteChainAdjacentThresholdRate M sampleRate) :=
  finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_joint_floor_rating_law_min_threshold_rate_of_score_bounds_of_extended_min_eq
    M sampleRate hpositive_sample a z hz hderiv_hi hderiv_lo
    rLow rHigh hmass_low hmass_high hscore_low_le hscore_le_high hscore_lt
    hextended_min_eq

/--
Theorem 1 finite-chain specialization from the named pairwise threshold-rate
regularity package. This is the compact human-facing endpoint for the current
finite formalization: the joint floor-rating law and adjacent-pair aggregation
are proved internally, while the pairwise source-rate regularity is supplied
as one explicit certificate.
-/
theorem theorem1_finite_chain_uniform_floor_objective_oneSub_exact_min_adjacent_rate_from_pairwise_threshold_rate_regularity
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    [DecidableEq (finiteChainOrderedPair n)]
    [Nonempty (finiteChainAdjacentIndex n)]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n → ℝ)
    (hpositive_sample : ∀ θ : Fin n, 0 < sampleRate θ)
    (C :
      theorem1PairwiseThresholdRateRegularity M sampleRate
        finiteChainOrderedPairHi finiteChainOrderedPairLo) :
    HasExponentialRate
      (fun k : ℕ =>
        1 - finiteUniformFloorPkObjective M sampleRate
          finiteChainOrderedPairHi finiteChainOrderedPairLo k)
      (minFiniteChainAdjacentThresholdRate M sampleRate) :=
  finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_joint_floor_rating_law_min_rate_of_pairwise_threshold_rate_regularity
    M sampleRate hpositive_sample C

/--
Theorem 1 finite-chain specialization for the concrete independent joint
floor-rating law from per-pair common-dual log-MGF derivatives.  The source
threshold equalities are derived internally by Fenchel optimality, under the
current real-valued finite-rate boundedness side condition.
-/
theorem theorem1_finite_chain_uniform_floor_objective_oneSub_exact_min_adjacent_rate_from_joint_floor_rating_law_logMGF_derivatives
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    [DecidableEq (finiteChainOrderedPair n)]
    [Nonempty (finiteChainAdjacentIndex n)]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n → ℝ)
    (hpositive_sample : ∀ θ : Fin n, 0 < sampleRate θ)
    (hbdd_hi :
      ∀ p : finiteChainOrderedPair n, ∀ b : ℝ,
        BddAbove (Set.range fun t : ℝ =>
          finiteLegendreValue
            (M.typeLaw (finiteChainOrderedPairHi p)) M.score b t))
    (hbdd_lo :
      ∀ p : finiteChainOrderedPair n, ∀ b : ℝ,
        BddAbove (Set.range fun t : ℝ =>
          finiteLegendreValue
            (M.typeLaw (finiteChainOrderedPairLo p)) M.score b t))
    (a z : finiteChainOrderedPair n → ℝ)
    (hz : ∀ p : finiteChainOrderedPair n, z p ≤ 0)
    (hderiv_hi :
      ∀ p : finiteChainOrderedPair n,
        HasDerivAt
          (fun t : ℝ => M.logMGF (finiteChainOrderedPairHi p) t) (a p)
          (z p * (sampleRate (finiteChainOrderedPairHi p))⁻¹))
    (hderiv_lo :
      ∀ p : finiteChainOrderedPair n,
        HasDerivAt
          (fun t : ℝ => M.logMGF (finiteChainOrderedPairLo p) t) (a p)
          (-(z p * (sampleRate (finiteChainOrderedPairLo p))⁻¹)))
    (hstraddle_hi :
      ∀ p : finiteChainOrderedPair n,
        ratingLawStraddlesThreshold M (finiteChainOrderedPairHi p) (a p))
    (hstraddle_lo :
      ∀ p : finiteChainOrderedPair n,
        ratingLawStraddlesThreshold M (finiteChainOrderedPairLo p) (a p)) :
    HasExponentialRate
      (fun k : ℕ =>
        1 - finiteUniformFloorPkObjective M sampleRate
          finiteChainOrderedPairHi finiteChainOrderedPairLo k)
      (minFiniteChainAdjacentThresholdRate M sampleRate) :=
  finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_joint_floor_rating_law_min_rate_of_logMGF_derivatives
    M sampleRate hpositive_sample hbdd_hi hbdd_lo a z hz
    hderiv_hi hderiv_lo hstraddle_hi hstraddle_lo

/--
Theorem 1 arbitrary-real floor-count endpoint from per-pair common-dual
log-MGF derivative data and compact two-sided support, deriving threshold
minimality by Fenchel optimality under the current all-threshold bounded-rate
side condition.
-/
theorem theorem1_floor_weighted_objective_oneSub_exact_rate_from_adjacent_logMGF_derivatives_of_straddling_support
    {Seller Rating Pair Adj : Type*} [Fintype Rating] [DecidableEq Rating]
    [Fintype Pair] [DecidableEq Pair]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
    (weight : Pair → ℝ)
    (adjacentPair : Adj → Pair)
    (hweight_nonneg : ∀ p, 0 ≤ weight p)
    (hweight_sum : ∑ p : Pair, weight p = 1)
    (iMin : Adj) (hweight_pos : 0 < weight (adjacentPair iMin))
    (hgHi : ∀ p : Pair, 0 < sampleRate (pairHi p))
    (hgLo : ∀ p : Pair, 0 < sampleRate (pairLo p))
    (hbdd_hi :
      ∀ p : Pair, ∀ b : ℝ, BddAbove (Set.range fun t : ℝ =>
        finiteLegendreValue (M.typeLaw (pairHi p)) M.score b t))
    (hbdd_lo :
      ∀ p : Pair, ∀ b : ℝ, BddAbove (Set.range fun t : ℝ =>
        finiteLegendreValue (M.typeLaw (pairLo p)) M.score b t))
    (a z : Pair → ℝ)
    (hz : ∀ p : Pair, z p ≤ 0)
    (hderiv_hi :
      ∀ p : Pair,
        HasDerivAt (fun t : ℝ => M.logMGF (pairHi p) t) (a p)
          (z p * (sampleRate (pairHi p))⁻¹))
    (hderiv_lo :
      ∀ p : Pair,
        HasDerivAt (fun t : ℝ => M.logMGF (pairLo p) t) (a p)
          (-(z p * (sampleRate (pairLo p))⁻¹)))
    (hstraddle_hi :
      ∀ p : Pair, ratingLawStraddlesThreshold M (pairHi p) (a p))
    (hstraddle_lo :
      ∀ p : Pair, ratingLawStraddlesThreshold M (pairLo p) (a p))
    (hadj_min :
      ∀ i : Adj,
        pairwiseSellerThresholdRate M sampleRate
            (pairHi (adjacentPair iMin)) (pairLo (adjacentPair iMin)) ≤
          pairwiseSellerThresholdRate M sampleRate
            (pairHi (adjacentPair i)) (pairLo (adjacentPair i)))
    (hadj_dominates :
      ∀ p : Pair, ∃ i : Adj,
        pairwiseSellerThresholdRate M sampleRate
            (pairHi (adjacentPair i)) (pairLo (adjacentPair i)) ≤
          pairwiseSellerThresholdRate M sampleRate (pairHi p) (pairLo p)) :
    HasExponentialRate
      (fun k : ℕ =>
        1 - finiteFloorPkObjective M sampleRate pairHi pairLo weight k)
      (pairwiseSellerThresholdRate M sampleRate
        (pairHi (adjacentPair iMin)) (pairLo (adjacentPair iMin))) :=
  finiteFloorPkObjective_oneSub_hasExponentialRate_of_adjacent_logMGF_derivatives_of_straddling_support
    M sampleRate pairHi pairLo weight adjacentPair
    hweight_nonneg hweight_sum iMin hweight_pos hgHi hgLo
    hbdd_hi hbdd_lo a z hz hderiv_hi hderiv_lo
    hstraddle_hi hstraddle_lo hadj_min hadj_dominates

/--
Theorem 1 all-pairs-minimum floor-count endpoint.  This is the source proof
line before the adjacent-pair reduction, with the minimum taken over the finite
pair family directly.
-/
theorem theorem1_floor_weighted_objective_oneSub_exact_rate_from_min_logMGF_derivative_minimizers_of_pos_neg_atoms
    {Seller Rating Pair : Type*} [Fintype Rating] [DecidableEq Rating]
    [Fintype Pair] [DecidableEq Pair]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
    (weight : Pair → ℝ)
    (hweight_nonneg : ∀ p, 0 ≤ weight p)
    (hweight_sum : ∑ p : Pair, weight p = 1)
    (pMin : Pair) (hweight_pos : 0 < weight pMin)
    (hgHi : ∀ p : Pair, 0 < sampleRate (pairHi p))
    (hgLo : ∀ p : Pair, 0 < sampleRate (pairLo p))
    (a z : Pair → ℝ)
    (hz : ∀ p : Pair, z p ≤ 0)
    (hderiv_hi :
      ∀ p : Pair,
        HasDerivAt (fun t : ℝ => M.logMGF (pairHi p) t) (a p)
          (z p * (sampleRate (pairHi p))⁻¹))
    (hderiv_lo :
      ∀ p : Pair,
        HasDerivAt (fun t : ℝ => M.logMGF (pairLo p) t) (a p)
          (-(z p * (sampleRate (pairLo p))⁻¹)))
    (hthreshold_eq :
      ∀ p : Pair,
        M.pairwiseRateObjective sampleRate (pairHi p) (pairLo p) (a p) =
          pairwiseSellerThresholdRate M sampleRate (pairHi p) (pairLo p))
    (hiPos hiNeg loPos loNeg : Pair → Rating)
    (hmass_hi_pos :
      ∀ p : Pair, 0 < (M.typeLaw (pairHi p) (hiPos p)).toReal)
    (hscore_hi_pos :
      ∀ p : Pair, 0 < M.score (hiPos p) - a p)
    (hmass_hi_neg :
      ∀ p : Pair, 0 < (M.typeLaw (pairHi p) (hiNeg p)).toReal)
    (hscore_hi_neg :
      ∀ p : Pair, M.score (hiNeg p) - a p < 0)
    (hmass_lo_pos :
      ∀ p : Pair, 0 < (M.typeLaw (pairLo p) (loPos p)).toReal)
    (hscore_lo_pos :
      ∀ p : Pair, 0 < a p - M.score (loPos p))
    (hmass_lo_neg :
      ∀ p : Pair, 0 < (M.typeLaw (pairLo p) (loNeg p)).toReal)
    (hscore_lo_neg :
      ∀ p : Pair, a p - M.score (loNeg p) < 0)
    (hmin :
      ∀ p : Pair,
        pairwiseSellerThresholdRate M sampleRate (pairHi pMin) (pairLo pMin) ≤
          pairwiseSellerThresholdRate M sampleRate (pairHi p) (pairLo p)) :
    HasExponentialRate
      (fun k : ℕ =>
        1 - finiteFloorPkObjective M sampleRate pairHi pairLo weight k)
      (pairwiseSellerThresholdRate M sampleRate
        (pairHi pMin) (pairLo pMin)) :=
  finiteFloorPkObjective_oneSub_hasExponentialRate_of_min_logMGF_derivative_minimizers_of_pos_neg_atoms
    M sampleRate pairHi pairLo weight
    hweight_nonneg hweight_sum pMin hweight_pos hgHi hgLo
    a z hz hderiv_hi hderiv_lo hthreshold_eq
    hiPos hiNeg loPos loNeg
    hmass_hi_pos hscore_hi_pos hmass_hi_neg hscore_hi_neg
    hmass_lo_pos hscore_lo_pos hmass_lo_neg hscore_lo_neg
    hmin

/--
Theorem 1 finite `W_k` endpoint with uniform weights over the finite family of
comparison pairs. This is the paper-facing specialization of the all-pairs
minimum statement.
-/
theorem theorem1_uniform_floor_objective_oneSub_exact_rate_from_min_logMGF_derivative_minimizers_of_pos_neg_atoms
    {Seller Rating Pair : Type*} [Fintype Rating] [DecidableEq Rating]
    [Fintype Pair] [DecidableEq Pair] [Nonempty Pair]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
    (pMin : Pair)
    (hgHi : ∀ p : Pair, 0 < sampleRate (pairHi p))
    (hgLo : ∀ p : Pair, 0 < sampleRate (pairLo p))
    (a z : Pair → ℝ)
    (hz : ∀ p : Pair, z p ≤ 0)
    (hderiv_hi :
      ∀ p : Pair,
        HasDerivAt (fun t : ℝ => M.logMGF (pairHi p) t) (a p)
          (z p * (sampleRate (pairHi p))⁻¹))
    (hderiv_lo :
      ∀ p : Pair,
        HasDerivAt (fun t : ℝ => M.logMGF (pairLo p) t) (a p)
          (-(z p * (sampleRate (pairLo p))⁻¹)))
    (hthreshold_eq :
      ∀ p : Pair,
        M.pairwiseRateObjective sampleRate (pairHi p) (pairLo p) (a p) =
          pairwiseSellerThresholdRate M sampleRate (pairHi p) (pairLo p))
    (hiPos hiNeg loPos loNeg : Pair → Rating)
    (hmass_hi_pos :
      ∀ p : Pair, 0 < (M.typeLaw (pairHi p) (hiPos p)).toReal)
    (hscore_hi_pos :
      ∀ p : Pair, 0 < M.score (hiPos p) - a p)
    (hmass_hi_neg :
      ∀ p : Pair, 0 < (M.typeLaw (pairHi p) (hiNeg p)).toReal)
    (hscore_hi_neg :
      ∀ p : Pair, M.score (hiNeg p) - a p < 0)
    (hmass_lo_pos :
      ∀ p : Pair, 0 < (M.typeLaw (pairLo p) (loPos p)).toReal)
    (hscore_lo_pos :
      ∀ p : Pair, 0 < a p - M.score (loPos p))
    (hmass_lo_neg :
      ∀ p : Pair, 0 < (M.typeLaw (pairLo p) (loNeg p)).toReal)
    (hscore_lo_neg :
      ∀ p : Pair, a p - M.score (loNeg p) < 0)
    (hmin :
      ∀ p : Pair,
        pairwiseSellerThresholdRate M sampleRate (pairHi pMin) (pairLo pMin) ≤
          pairwiseSellerThresholdRate M sampleRate (pairHi p) (pairLo p)) :
    HasExponentialRate
      (fun k : ℕ =>
        1 - finiteUniformFloorPkObjective M sampleRate pairHi pairLo k)
      (pairwiseSellerThresholdRate M sampleRate
        (pairHi pMin) (pairLo pMin)) :=
  finiteUniformFloorPkObjective_oneSub_hasExponentialRate_of_min_logMGF_derivative_minimizers_of_pos_neg_atoms
    M sampleRate pairHi pairLo pMin hgHi hgLo
    a z hz hderiv_hi hderiv_lo hthreshold_eq
    hiPos hiNeg loPos loNeg
    hmass_hi_pos hscore_hi_pos hmass_hi_neg hscore_hi_neg
    hmass_lo_pos hscore_lo_pos hmass_lo_neg hscore_lo_neg
    hmin

/--
Theorem 1 finite source-rate endpoint from per-pair log-MGF derivative
witnesses: Appendix Lemma `problessthan`, Lemma `Pk_LD`, and the finite
adjacent-pair aggregation argument are all discharged in the integer-rate
finite model.
-/
theorem theorem1_finite_pk_complement_ranking_error_exact_rate_from_adjacent_logMGF_derivatives
    {Seller Rating Pair Adj : Type*} [Fintype Rating] [DecidableEq Rating]
    [Fintype Pair] [DecidableEq Pair]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
    (gHi gLo : Pair → ℕ)
    (weight : Pair → ℝ)
    (adjacentPair : Adj → Pair)
    (hweight_nonneg : ∀ p, 0 ≤ weight p)
    (iMin : Adj) (hweight_pos : 0 < weight (adjacentPair iMin))
    (hgHi : ∀ p : Pair, 0 < gHi p)
    (hgLo : ∀ p : Pair, 0 < gLo p)
    (hsample_hi :
      ∀ p : Pair, sampleRate (pairHi p) = (gHi p : ℝ))
    (hsample_lo :
      ∀ p : Pair, sampleRate (pairLo p) = (gLo p : ℝ))
    (hbdd_hi :
      ∀ p : Pair, ∀ a : ℝ, BddAbove (Set.range fun z : ℝ =>
        finiteLegendreValue (M.typeLaw (pairHi p)) M.score a z))
    (hbdd_lo :
      ∀ p : Pair, ∀ a : ℝ, BddAbove (Set.range fun z : ℝ =>
        finiteLegendreValue (M.typeLaw (pairLo p)) M.score a z))
    (a z : Pair → ℝ)
    (hderiv_hi :
      ∀ p : Pair,
        HasDerivAt (fun t : ℝ => M.logMGF (pairHi p) t) (a p)
          (z p * (gHi p : ℝ)⁻¹))
    (hderiv_lo :
      ∀ p : Pair,
        HasDerivAt (fun t : ℝ => M.logMGF (pairLo p) t) (a p)
          (-(z p * (gLo p : ℝ)⁻¹)))
    (hmean :
      ∀ p : Pair,
        0 ≤
          AppliedModelingLib.pmfExp
            (twoSampleRateBlockLaw M (pairHi p) (pairLo p)
              (gHi p) (gLo p))
            (twoSampleRateBlockScore M (gHi p) (gLo p)))
    (samplePos sampleNeg :
      ∀ p : Pair, (Fin (gHi p) → Rating) × (Fin (gLo p) → Rating))
    (hmassPos :
      ∀ p : Pair,
        0 <
          (twoSampleRateBlockLaw M (pairHi p) (pairLo p)
            (gHi p) (gLo p) (samplePos p)).toReal)
    (hscorePos :
      ∀ p : Pair,
        0 < twoSampleRateBlockScore M (gHi p) (gLo p) (samplePos p))
    (hmassNeg :
      ∀ p : Pair,
        0 <
          (twoSampleRateBlockLaw M (pairHi p) (pairLo p)
            (gHi p) (gLo p) (sampleNeg p)).toReal)
    (hscoreNeg :
      ∀ p : Pair,
        twoSampleRateBlockScore M (gHi p) (gLo p) (sampleNeg p) < 0)
    (hadj_min :
      ∀ i : Adj,
        pairwiseSellerThresholdRate M sampleRate
            (pairHi (adjacentPair iMin)) (pairLo (adjacentPair iMin)) ≤
          pairwiseSellerThresholdRate M sampleRate
            (pairHi (adjacentPair i)) (pairLo (adjacentPair i)))
    (hadj_dominates :
      ∀ p : Pair, ∃ i : Adj,
        pairwiseSellerThresholdRate M sampleRate
            (pairHi (adjacentPair i)) (pairLo (adjacentPair i)) ≤
          pairwiseSellerThresholdRate M sampleRate (pairHi p) (pairLo p)) :
    HasExponentialRate
      (fun n : ℕ =>
        ∑ p : Pair,
          weight p *
            twoSamplePkComplementErrorProb M (pairHi p) (pairLo p)
              (n * gHi p) (n * gLo p)
              (((gHi p : ℕ) : ℝ)⁻¹) (((gLo p : ℕ) : ℝ)⁻¹))
      (pairwiseSellerThresholdRate M sampleRate
        (pairHi (adjacentPair iMin)) (pairLo (adjacentPair iMin))) :=
  finiteRankingPkComplementError_hasExponentialRate_of_adjacent_logMGF_derivatives
    M sampleRate pairHi pairLo gHi gLo weight adjacentPair
    hweight_nonneg iMin hweight_pos hgHi hgLo hsample_hi hsample_lo
    hbdd_hi hbdd_lo a z hderiv_hi hderiv_lo hmean samplePos sampleNeg
    hmassPos hscorePos hmassNeg hscoreNeg hadj_min hadj_dominates

/--
Theorem 1 integer-rate finite source endpoint from per-pair log-MGF derivative
witnesses: the paper-style objective itself has the exact adjacent-pair source
rate for `1 - W_n`.
-/
theorem theorem1_integer_rate_weighted_objective_oneSub_exact_rate_from_adjacent_logMGF_derivatives
    {Seller Rating Pair Adj : Type*} [Fintype Rating] [DecidableEq Rating]
    [Fintype Pair] [DecidableEq Pair]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
    (gHi gLo : Pair → ℕ)
    (weight : Pair → ℝ)
    (adjacentPair : Adj → Pair)
    (hweight_nonneg : ∀ p, 0 ≤ weight p)
    (hweight_sum : ∑ p : Pair, weight p = 1)
    (iMin : Adj) (hweight_pos : 0 < weight (adjacentPair iMin))
    (hgHi : ∀ p : Pair, 0 < gHi p)
    (hgLo : ∀ p : Pair, 0 < gLo p)
    (hsample_hi :
      ∀ p : Pair, sampleRate (pairHi p) = (gHi p : ℝ))
    (hsample_lo :
      ∀ p : Pair, sampleRate (pairLo p) = (gLo p : ℝ))
    (hbdd_hi :
      ∀ p : Pair, ∀ a : ℝ, BddAbove (Set.range fun z : ℝ =>
        finiteLegendreValue (M.typeLaw (pairHi p)) M.score a z))
    (hbdd_lo :
      ∀ p : Pair, ∀ a : ℝ, BddAbove (Set.range fun z : ℝ =>
        finiteLegendreValue (M.typeLaw (pairLo p)) M.score a z))
    (a z : Pair → ℝ)
    (hderiv_hi :
      ∀ p : Pair,
        HasDerivAt (fun t : ℝ => M.logMGF (pairHi p) t) (a p)
          (z p * (gHi p : ℝ)⁻¹))
    (hderiv_lo :
      ∀ p : Pair,
        HasDerivAt (fun t : ℝ => M.logMGF (pairLo p) t) (a p)
          (-(z p * (gLo p : ℝ)⁻¹)))
    (hmean :
      ∀ p : Pair,
        0 ≤
          AppliedModelingLib.pmfExp
            (twoSampleRateBlockLaw M (pairHi p) (pairLo p)
              (gHi p) (gLo p))
            (twoSampleRateBlockScore M (gHi p) (gLo p)))
    (samplePos sampleNeg :
      ∀ p : Pair, (Fin (gHi p) → Rating) × (Fin (gLo p) → Rating))
    (hmassPos :
      ∀ p : Pair,
        0 <
          (twoSampleRateBlockLaw M (pairHi p) (pairLo p)
            (gHi p) (gLo p) (samplePos p)).toReal)
    (hscorePos :
      ∀ p : Pair,
        0 < twoSampleRateBlockScore M (gHi p) (gLo p) (samplePos p))
    (hmassNeg :
      ∀ p : Pair,
        0 <
          (twoSampleRateBlockLaw M (pairHi p) (pairLo p)
            (gHi p) (gLo p) (sampleNeg p)).toReal)
    (hscoreNeg :
      ∀ p : Pair,
        twoSampleRateBlockScore M (gHi p) (gLo p) (sampleNeg p) < 0)
    (hadj_min :
      ∀ i : Adj,
        pairwiseSellerThresholdRate M sampleRate
            (pairHi (adjacentPair iMin)) (pairLo (adjacentPair iMin)) ≤
          pairwiseSellerThresholdRate M sampleRate
            (pairHi (adjacentPair i)) (pairLo (adjacentPair i)))
    (hadj_dominates :
      ∀ p : Pair, ∃ i : Adj,
        pairwiseSellerThresholdRate M sampleRate
            (pairHi (adjacentPair i)) (pairLo (adjacentPair i)) ≤
          pairwiseSellerThresholdRate M sampleRate (pairHi p) (pairLo p)) :
    HasExponentialRate
      (fun n : ℕ =>
        1 - finiteIntegerRatePkObjective M pairHi pairLo gHi gLo weight n)
      (pairwiseSellerThresholdRate M sampleRate
        (pairHi (adjacentPair iMin)) (pairLo (adjacentPair iMin))) :=
  finiteIntegerRatePkObjective_oneSub_hasExponentialRate_of_adjacent_logMGF_derivatives
    M sampleRate pairHi pairLo gHi gLo weight adjacentPair
    hweight_nonneg hweight_sum iMin hweight_pos hgHi hgLo
    hsample_hi hsample_lo hbdd_hi hbdd_lo a z hderiv_hi hderiv_lo
    hmean samplePos sampleNeg hmassPos hscorePos hmassNeg hscoreNeg
    hadj_min hadj_dominates

/--
Theorem 1 source floor-count endpoint for natural-valued match rates: the
paper-style floor-count objective has the exact adjacent-pair source rate for
`1 - W_k`.
-/
theorem theorem1_floor_weighted_objective_oneSub_exact_rate_from_nat_sampleRates_adjacent_logMGF_derivatives
    {Seller Rating Pair Adj : Type*} [Fintype Rating] [DecidableEq Rating]
    [Fintype Pair] [DecidableEq Pair]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
    (gHi gLo : Pair → ℕ)
    (weight : Pair → ℝ)
    (adjacentPair : Adj → Pair)
    (hweight_nonneg : ∀ p, 0 ≤ weight p)
    (hweight_sum : ∑ p : Pair, weight p = 1)
    (iMin : Adj) (hweight_pos : 0 < weight (adjacentPair iMin))
    (hgHi : ∀ p : Pair, 0 < gHi p)
    (hgLo : ∀ p : Pair, 0 < gLo p)
    (hsample_hi :
      ∀ p : Pair, sampleRate (pairHi p) = (gHi p : ℝ))
    (hsample_lo :
      ∀ p : Pair, sampleRate (pairLo p) = (gLo p : ℝ))
    (hbdd_hi :
      ∀ p : Pair, ∀ a : ℝ, BddAbove (Set.range fun z : ℝ =>
        finiteLegendreValue (M.typeLaw (pairHi p)) M.score a z))
    (hbdd_lo :
      ∀ p : Pair, ∀ a : ℝ, BddAbove (Set.range fun z : ℝ =>
        finiteLegendreValue (M.typeLaw (pairLo p)) M.score a z))
    (a z : Pair → ℝ)
    (hderiv_hi :
      ∀ p : Pair,
        HasDerivAt (fun t : ℝ => M.logMGF (pairHi p) t) (a p)
          (z p * (gHi p : ℝ)⁻¹))
    (hderiv_lo :
      ∀ p : Pair,
        HasDerivAt (fun t : ℝ => M.logMGF (pairLo p) t) (a p)
          (-(z p * (gLo p : ℝ)⁻¹)))
    (hmean :
      ∀ p : Pair,
        0 ≤
          AppliedModelingLib.pmfExp
            (twoSampleRateBlockLaw M (pairHi p) (pairLo p)
              (gHi p) (gLo p))
            (twoSampleRateBlockScore M (gHi p) (gLo p)))
    (samplePos sampleNeg :
      ∀ p : Pair, (Fin (gHi p) → Rating) × (Fin (gLo p) → Rating))
    (hmassPos :
      ∀ p : Pair,
        0 <
          (twoSampleRateBlockLaw M (pairHi p) (pairLo p)
            (gHi p) (gLo p) (samplePos p)).toReal)
    (hscorePos :
      ∀ p : Pair,
        0 < twoSampleRateBlockScore M (gHi p) (gLo p) (samplePos p))
    (hmassNeg :
      ∀ p : Pair,
        0 <
          (twoSampleRateBlockLaw M (pairHi p) (pairLo p)
            (gHi p) (gLo p) (sampleNeg p)).toReal)
    (hscoreNeg :
      ∀ p : Pair,
        twoSampleRateBlockScore M (gHi p) (gLo p) (sampleNeg p) < 0)
    (hadj_min :
      ∀ i : Adj,
        pairwiseSellerThresholdRate M sampleRate
            (pairHi (adjacentPair iMin)) (pairLo (adjacentPair iMin)) ≤
          pairwiseSellerThresholdRate M sampleRate
            (pairHi (adjacentPair i)) (pairLo (adjacentPair i)))
    (hadj_dominates :
      ∀ p : Pair, ∃ i : Adj,
        pairwiseSellerThresholdRate M sampleRate
            (pairHi (adjacentPair i)) (pairLo (adjacentPair i)) ≤
          pairwiseSellerThresholdRate M sampleRate (pairHi p) (pairLo p)) :
    HasExponentialRate
      (fun n : ℕ =>
        1 - finiteFloorPkObjective M sampleRate pairHi pairLo weight n)
      (pairwiseSellerThresholdRate M sampleRate
        (pairHi (adjacentPair iMin)) (pairLo (adjacentPair iMin))) :=
  finiteFloorPkObjective_oneSub_hasExponentialRate_of_nat_sampleRates_adjacent_logMGF_derivatives
    M sampleRate pairHi pairLo gHi gLo weight adjacentPair
    hweight_nonneg hweight_sum iMin hweight_pos hgHi hgLo
    hsample_hi hsample_lo hbdd_hi hbdd_lo a z hderiv_hi hderiv_lo
    hmean samplePos sampleNeg hmassPos hscorePos hmassNeg hscoreNeg
    hadj_min hadj_dominates

end

end GJ18InformativeRatingSystems

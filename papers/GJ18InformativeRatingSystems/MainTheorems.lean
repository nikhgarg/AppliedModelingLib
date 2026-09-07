import AppliedModelingLib.Applications.RatingSystems.FiniteComparison

/-!
# Implementation Theorems: Designing Informative Rating Systems

This file starts the Lean audit for Garg and Johari (2018).  The reusable
formalization surface is the finite rating-scale large-deviation model:
single-rating log-MGFs, Legendre rate functions, pairwise score-comparison
rates, and finite aggregation into the paper's Kendall-style ranking objective.

The current source-facing boundary is the finite-domain bridge between the
support-safe extended adjacent threshold-rate minimum and the paper's real
adjacent threshold-rate minimum.
-/

open scoped BigOperators

namespace GJ18InformativeRatingSystems

noncomputable section

open AppliedModelingLib.Probability

/--
Lemma C transfer bridge: if the paper's `P_k`-style error probability is
eventually within fixed positive constants of a certified pairwise comparison
error, then it has the same exact exponential rate.
-/
theorem pkError_hasExponentialRate_of_pairwise_const_sandwich
    {pairwiseError pkError : ℕ → ℝ} {rate lower upper : ℝ}
    (hpairwise : ExponentialRateCertificate pairwiseError rate)
    (hlower : 0 < lower) (hupper : 0 < upper)
    (hsandwich : ∀ᶠ k in Filter.atTop,
      lower * pairwiseError k ≤ pkError k ∧
        pkError k ≤ upper * pairwiseError k) :
    ExponentialRateCertificate pkError rate :=
  hpairwise.of_eventually_const_sandwich hlower hupper hsandwich

/--
Finite aggregation bridge for the paper's `1 - W_k` objective after a finite
seller-type discretization or finite adjacent-pair reduction has supplied
pairwise LDP certificates.
-/
theorem rankingObjectiveError_hasExpUpperBound_of_pair_certificates
    {ι : Type*} [Fintype ι]
    (C : FiniteErrorRateCertificate ι)
    {weight : ι → ℝ} {targetRate : ℝ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hrate : ∀ i, targetRate < C.rate i) :
    HasExpUpperBoundWithConst (C.aggregateError weight) targetRate :=
  C.aggregateError_hasExpUpperBoundWithConst_of_lt hweight hrate

/--
Finite exact-rate bridge for the paper's `1 - W_k` objective: once a finite
set of pairwise comparison errors has exact rates, any positive-weight
component attaining the minimum rate gives the exact aggregate rate.
-/
theorem rankingObjectiveError_hasExponentialRate_of_min_pair_certificate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : FiniteErrorRateCertificate ι)
    {weight : ι → ℝ} {minRate : ℝ}
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (iMin : ι) (hweight_pos : 0 < weight iMin)
    (hrate_min : C.rate iMin = minRate)
    (hrate_ge : ∀ i, minRate ≤ C.rate i) :
    HasExponentialRate (C.aggregateError weight) minRate :=
  C.aggregateError_hasExponentialRate_of_min_component
    hweight_nonneg iMin hweight_pos hrate_min hrate_ge

/--
Finite Theorem 1 adjacent-pair bridge.  If a selected adjacent pair minimizes
the adjacent-pair exponents, and every comparison pair is dominated by some
adjacent-pair exponent, then the finite ranking objective has the selected
adjacent exponent exactly.
-/
theorem rankingObjectiveError_hasExponentialRate_of_adjacent_min_pair_certificate
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
  C.aggregateError_hasExponentialRate_of_dominating_subfamily
    adjacentPair hweight_nonneg iMin hweight_pos hadj_min hadj_dominates

/--
Finite Theorem 1 bridge specialized to the paper's pairwise `1 - P_k`
errors.  Once each comparison pair has an exact source-threshold rate, the
weighted finite ranking-objective error has the minimum adjacent-pair rate.
-/
theorem finiteRankingPkComplementError_hasExponentialRate_of_adjacent_min_source_rates
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
        (pairHi (adjacentPair iMin)) (pairLo (adjacentPair iMin))) := by
  let C : FiniteErrorRateCertificate Pair :=
    { errorProb := fun p n =>
        twoSamplePkComplementErrorProb M (pairHi p) (pairLo p)
          (n * gHi p) (n * gLo p)
          (((gHi p : ℕ) : ℝ)⁻¹) (((gLo p : ℕ) : ℝ)⁻¹)
      rate := fun p =>
        pairwiseSellerThresholdRate M sampleRate (pairHi p) (pairLo p)
      has_rate := hpair }
  simpa [FiniteErrorRateCertificate.aggregateError, C] using
    rankingObjectiveError_hasExponentialRate_of_adjacent_min_pair_certificate
      C adjacentPair hweight_nonneg iMin hweight_pos hadj_min hadj_dominates

/--
Finite Theorem 1 bridge specialized to the paper's floor-count pairwise
`1 - P_k` errors.  This is the aggregation layer for the source model
`n_k(theta) = floor(k g(theta))`; the pairwise floor-count LDP certificates are
supplied as hypotheses.
-/
theorem finiteRankingFloorPkComplementError_hasExponentialRate_of_adjacent_min_source_rates
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
        (pairHi (adjacentPair iMin)) (pairLo (adjacentPair iMin))) := by
  let C : FiniteErrorRateCertificate Pair :=
    { errorProb := fun p =>
        twoSampleFloorPkComplementErrorProb M sampleRate
          (pairHi p) (pairLo p)
      rate := fun p =>
        pairwiseSellerThresholdRate M sampleRate (pairHi p) (pairLo p)
      has_rate := hpair }
  simpa [FiniteErrorRateCertificate.aggregateError, C] using
    rankingObjectiveError_hasExponentialRate_of_adjacent_min_pair_certificate
      C adjacentPair hweight_nonneg iMin hweight_pos hadj_min hadj_dominates

/--
Finite Theorem 1 floor-count bridge from pairwise nonpositive score-gap
certificates.  The constant-factor `Pk` transfer is discharged for every pair
before applying the finite adjacent-pair aggregation theorem.
-/
theorem finiteRankingFloorPkComplementError_hasExponentialRate_of_adjacent_leftTail_source_rates
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
  finiteRankingFloorPkComplementError_hasExponentialRate_of_adjacent_min_source_rates
    M sampleRate pairHi pairLo weight adjacentPair
    hweight_nonneg iMin hweight_pos
    (fun p =>
      twoSampleFloorPkComplementError_exponentialRateCertificate_of_leftTail
        M sampleRate (pairHi p) (pairLo p) (hleftTail p))
    hadj_min hadj_dominates

/--
Source-shaped finite Theorem 1 endpoint: under floor-count pairwise left-tail
source-rate certificates, the paper objective itself satisfies
`-log(1 - W_k) / k -> min adjacent source rate`.
-/
theorem finiteFloorPkObjective_oneSub_hasExponentialRate_of_adjacent_leftTail_source_rates
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
        (pairHi (adjacentPair iMin)) (pairLo (adjacentPair iMin))) := by
  have hcomp :
      HasExponentialRate
        (finiteFloorPkComplementError M sampleRate pairHi pairLo weight)
        (pairwiseSellerThresholdRate M sampleRate
          (pairHi (adjacentPair iMin)) (pairLo (adjacentPair iMin))) := by
    simpa [finiteFloorPkComplementError] using
      finiteRankingFloorPkComplementError_hasExponentialRate_of_adjacent_leftTail_source_rates
        M sampleRate pairHi pairLo weight adjacentPair
        hweight_nonneg iMin hweight_pos hleftTail hadj_min hadj_dominates
  refine Filter.Tendsto.congr' ?_ hcomp
  filter_upwards with k
  rw [logDecay]
  rw [logDecay]
  rw [← finiteFloorPkComplementError_eq_one_sub_objective
    M sampleRate pairHi pairLo weight hweight_sum k]

/--
Finite floor-count aggregation bridge for arbitrary per-pair rates.  This is
the rate-parametric version of the source-rate bridge: pairwise left-tail
certificates are first transferred to `1 - P_k`, then the finite aggregation
minimum is selected by the adjacent subfamily.
-/
theorem finiteRankingFloorPkComplementError_hasExponentialRate_of_adjacent_leftTail_rates
    {Seller Rating Pair Adj : Type*} [Fintype Rating] [DecidableEq Rating]
    [Fintype Pair] [DecidableEq Pair]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
    (weight : Pair → ℝ)
    (adjacentPair : Adj → Pair)
    (hweight_nonneg : ∀ p, 0 ≤ weight p)
    (iMin : Adj) (hweight_pos : 0 < weight (adjacentPair iMin))
    (rate : Pair → ℝ)
    (hleftTail :
      ∀ p : Pair,
        ExponentialRateCertificate
          (twoSampleFloorScoreGapLeftTailProb M sampleRate
            (pairHi p) (pairLo p))
          (rate p))
    (hadj_min :
      ∀ i : Adj, rate (adjacentPair iMin) ≤ rate (adjacentPair i))
    (hadj_dominates :
      ∀ p : Pair, ∃ i : Adj, rate (adjacentPair i) ≤ rate p) :
    HasExponentialRate
      (fun k : ℕ =>
        ∑ p : Pair,
          weight p *
            twoSampleFloorPkComplementErrorProb M sampleRate
              (pairHi p) (pairLo p) k)
      (rate (adjacentPair iMin)) := by
  let C : FiniteErrorRateCertificate Pair :=
    { errorProb := fun p =>
        twoSampleFloorPkComplementErrorProb M sampleRate
          (pairHi p) (pairLo p)
      rate := rate
      has_rate := fun p =>
        twoSampleFloorPkComplementError_exponentialRateCertificate_of_leftTail
          M sampleRate (pairHi p) (pairLo p) (hleftTail p) }
  simpa [FiniteErrorRateCertificate.aggregateError, C] using
    rankingObjectiveError_hasExponentialRate_of_adjacent_min_pair_certificate
      C adjacentPair hweight_nonneg iMin hweight_pos hadj_min hadj_dominates

/--
Finite `1 - W_k` bridge for arbitrary per-pair rates.  The only aggregation
requirements are nonnegative weights summing to one and an adjacent subfamily
that realizes and dominates the finite minimum.
-/
theorem finiteFloorPkObjective_oneSub_hasExponentialRate_of_adjacent_leftTail_rates
    {Seller Rating Pair Adj : Type*} [Fintype Rating] [DecidableEq Rating]
    [Fintype Pair] [DecidableEq Pair]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
    (weight : Pair → ℝ)
    (adjacentPair : Adj → Pair)
    (hweight_nonneg : ∀ p, 0 ≤ weight p)
    (hweight_sum : ∑ p : Pair, weight p = 1)
    (iMin : Adj) (hweight_pos : 0 < weight (adjacentPair iMin))
    (rate : Pair → ℝ)
    (hleftTail :
      ∀ p : Pair,
        ExponentialRateCertificate
          (twoSampleFloorScoreGapLeftTailProb M sampleRate
            (pairHi p) (pairLo p))
          (rate p))
    (hadj_min :
      ∀ i : Adj, rate (adjacentPair iMin) ≤ rate (adjacentPair i))
    (hadj_dominates :
      ∀ p : Pair, ∃ i : Adj, rate (adjacentPair i) ≤ rate p) :
    HasExponentialRate
      (fun k : ℕ =>
        1 - finiteFloorPkObjective M sampleRate pairHi pairLo weight k)
      (rate (adjacentPair iMin)) := by
  have hcomp :
      HasExponentialRate
        (finiteFloorPkComplementError M sampleRate pairHi pairLo weight)
        (rate (adjacentPair iMin)) := by
    simpa [finiteFloorPkComplementError] using
      finiteRankingFloorPkComplementError_hasExponentialRate_of_adjacent_leftTail_rates
        M sampleRate pairHi pairLo weight adjacentPair
        hweight_nonneg iMin hweight_pos rate hleftTail hadj_min hadj_dominates
  refine Filter.Tendsto.congr' ?_ hcomp
  filter_upwards with k
  rw [logDecay]
  rw [logDecay]
  rw [← finiteFloorPkComplementError_eq_one_sub_objective
    M sampleRate pairHi pairLo weight hweight_sum k]

/--
Finite `1 - W_k` endpoint whose exponent is the displayed pairwise objective
at the supplied derivative thresholds.  This closes the finite floor-count
large-deviation and aggregation layers without using the source threshold-rate
infimum; the remaining source step is to identify these displayed objective
values with the paper's threshold rates.
-/
theorem finiteFloorPkObjective_oneSub_hasExponentialRate_of_adjacent_logMGF_derivative_objective_rates_of_straddling_support
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
    (hstraddle_hi :
      ∀ p : Pair, ratingLawStraddlesThreshold M (pairHi p) (a p))
    (hstraddle_lo :
      ∀ p : Pair, ratingLawStraddlesThreshold M (pairLo p) (a p))
    (hadj_min :
      ∀ i : Adj,
        M.pairwiseRateObjective sampleRate
            (pairHi (adjacentPair iMin)) (pairLo (adjacentPair iMin))
            (a (adjacentPair iMin)) ≤
          M.pairwiseRateObjective sampleRate
            (pairHi (adjacentPair i)) (pairLo (adjacentPair i))
            (a (adjacentPair i)))
    (hadj_dominates :
      ∀ p : Pair, ∃ i : Adj,
        M.pairwiseRateObjective sampleRate
            (pairHi (adjacentPair i)) (pairLo (adjacentPair i))
            (a (adjacentPair i)) ≤
          M.pairwiseRateObjective sampleRate (pairHi p) (pairLo p) (a p)) :
    HasExponentialRate
      (fun k : ℕ =>
        1 - finiteFloorPkObjective M sampleRate pairHi pairLo weight k)
      (M.pairwiseRateObjective sampleRate
        (pairHi (adjacentPair iMin)) (pairLo (adjacentPair iMin))
        (a (adjacentPair iMin))) :=
  finiteFloorPkObjective_oneSub_hasExponentialRate_of_adjacent_leftTail_rates
    M sampleRate pairHi pairLo weight adjacentPair
    hweight_nonneg hweight_sum iMin hweight_pos
    (fun p => M.pairwiseRateObjective sampleRate (pairHi p) (pairLo p) (a p))
    (fun p =>
      twoSampleFloorScoreGapLeftTail_pairwiseObjective_exponentialRateCertificate_of_logMGF_derivative_minimizer_of_straddling_support
        M sampleRate (pairHi p) (pairLo p)
        (hgHi p) (hgLo p) (a p) (z p) (hz p)
        (hderiv_hi p) (hderiv_lo p) (hstraddle_hi p) (hstraddle_lo p))
    hadj_min hadj_dominates

/--
Source-shaped finite Theorem 1 endpoint for arbitrary real floor-count sample
rates from per-pair shifted-Cramer minimizers and source-rate identities.
-/
theorem finiteFloorPkObjective_oneSub_hasExponentialRate_of_adjacent_shifted_cramer_minimizers
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
        (pairHi (adjacentPair iMin)) (pairLo (adjacentPair iMin))) := by
  have hcomp :
      HasExponentialRate
        (finiteFloorPkComplementError M sampleRate pairHi pairLo weight)
        (pairwiseSellerThresholdRate M sampleRate
          (pairHi (adjacentPair iMin)) (pairLo (adjacentPair iMin))) := by
    simpa [finiteFloorPkComplementError] using
      finiteRankingFloorPkComplementError_hasExponentialRate_of_adjacent_min_source_rates
        M sampleRate pairHi pairLo weight adjacentPair
        hweight_nonneg iMin hweight_pos
        (fun p =>
          twoSampleFloorPkComplementError_pairwiseThresholdRate_exponentialRateCertificate_of_shifted_cramer_minimizer
            M sampleRate (pairHi p) (pairLo p)
            (hgHi p) (hgLo p) (a p) (z p) (hz p)
            (C_hi p) (C_lo p) (hshifted_rate p) (hdual_rate p))
        hadj_min hadj_dominates
  refine Filter.Tendsto.congr' ?_ hcomp
  filter_upwards with k
  rw [logDecay]
  rw [logDecay]
  rw [← finiteFloorPkComplementError_eq_one_sub_objective
    M sampleRate pairHi pairLo weight hweight_sum k]

/--
Source-shaped finite Theorem 1 endpoint for arbitrary real floor-count sample
rates from per-pair log-MGF derivative minimizers.  This is the floor-count
version of the finite GJ18 theorem: the one-population shifted Cramer
certificates and the rate identities are built from the source finite-MGF
derivative assumptions for each pair.
-/
theorem finiteFloorPkObjective_oneSub_hasExponentialRate_of_adjacent_logMGF_derivative_minimizers
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
  finiteFloorPkObjective_oneSub_hasExponentialRate_of_adjacent_leftTail_source_rates
    M sampleRate pairHi pairLo weight adjacentPair
    hweight_nonneg hweight_sum iMin hweight_pos
    (fun p =>
      twoSampleFloorScoreGapLeftTail_pairwiseThresholdRate_exponentialRateCertificate_of_logMGF_derivative_minimizer
        M sampleRate (pairHi p) (pairLo p)
        (hgHi p) (hgLo p) (a p) (z p) (hz p)
        (hbdd_hi p) (hbdd_lo p) (hderiv_hi p) (hderiv_lo p)
        (hthreshold_eq p) (hmean_hi p) (hmean_lo p)
        (hmass_hi_pos p) (hscore_hi_pos p)
        (hmass_hi_neg p) (hscore_hi_neg p)
        (hmass_lo_pos p) (hscore_lo_pos p)
        (hmass_lo_neg p) (hscore_lo_neg p))
    hadj_min hadj_dominates

/--
Source-shaped finite Theorem 1 endpoint for arbitrary real floor-count sample
rates with the minimum taken over all comparison pairs.  This is the source
proof line immediately before the adjacent-pair reduction: no adjacent
dominance hypothesis is needed, only that the selected pair attains the
minimum over the displayed finite pair family.
-/
theorem finiteFloorPkObjective_oneSub_hasExponentialRate_of_min_logMGF_derivative_minimizers
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
    (hmin :
      ∀ p : Pair,
        pairwiseSellerThresholdRate M sampleRate (pairHi pMin) (pairLo pMin) ≤
          pairwiseSellerThresholdRate M sampleRate (pairHi p) (pairLo p)) :
    HasExponentialRate
      (fun k : ℕ =>
        1 - finiteFloorPkObjective M sampleRate pairHi pairLo weight k)
      (pairwiseSellerThresholdRate M sampleRate
        (pairHi pMin) (pairLo pMin)) :=
  finiteFloorPkObjective_oneSub_hasExponentialRate_of_adjacent_logMGF_derivative_minimizers
    (Pair := Pair) (Adj := Pair)
    M sampleRate pairHi pairLo weight (fun p : Pair => p)
    hweight_nonneg hweight_sum pMin hweight_pos hgHi hgLo
    a z hz hbdd_hi hbdd_lo hderiv_hi hderiv_lo hthreshold_eq
    hmean_hi hmean_lo hiPos hiNeg loPos loNeg
    hmass_hi_pos hscore_hi_pos hmass_hi_neg hscore_hi_neg
    hmass_lo_pos hscore_lo_pos hmass_lo_neg hscore_lo_neg
    hmin (fun p => ⟨p, le_rfl⟩)

/--
Source-shaped finite Theorem 1 endpoint for arbitrary real floor-count sample
rates from per-pair log-MGF derivative minimizers, with proof-technical
Legendre boundedness and shifted mean signs derived internally.
-/
theorem finiteFloorPkObjective_oneSub_hasExponentialRate_of_adjacent_logMGF_derivative_minimizers_of_pos_neg_atoms
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
  finiteFloorPkObjective_oneSub_hasExponentialRate_of_adjacent_leftTail_source_rates
    M sampleRate pairHi pairLo weight adjacentPair
    hweight_nonneg hweight_sum iMin hweight_pos
    (fun p =>
      twoSampleFloorScoreGapLeftTail_pairwiseThresholdRate_exponentialRateCertificate_of_logMGF_derivative_minimizer_of_pos_neg_atoms
        M sampleRate (pairHi p) (pairLo p)
        (hgHi p) (hgLo p) (a p) (z p) (hz p)
        (hderiv_hi p) (hderiv_lo p) (hthreshold_eq p)
        (hmass_hi_pos p) (hscore_hi_pos p)
        (hmass_hi_neg p) (hscore_hi_neg p)
        (hmass_lo_pos p) (hscore_lo_pos p)
        (hmass_lo_neg p) (hscore_lo_neg p))
    hadj_min hadj_dominates

/--
Source-shaped finite Theorem 1 endpoint for arbitrary real floor-count sample
rates from per-pair common-dual log-MGF derivatives. Compared with the
`derivative_minimizers` variant, the source threshold equalities are derived
by Fenchel optimality under the current all-threshold boundedness side
condition for the real-valued finite-rate API.
-/
theorem finiteFloorPkObjective_oneSub_hasExponentialRate_of_adjacent_logMGF_derivatives_of_pos_neg_atoms
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
    a z hz hderiv_hi hderiv_lo
    (fun p =>
      pairwiseSellerThresholdRate_eq_of_common_logMGF_derivatives
        M sampleRate (pairHi p) (pairLo p) (hgHi p) (hgLo p)
        (hbdd_hi p) (hbdd_lo p) (a p) (z p)
        (hderiv_hi p) (hderiv_lo p))
    hiPos hiNeg loPos loNeg
    hmass_hi_pos hscore_hi_pos hmass_hi_neg hscore_hi_neg
    hmass_lo_pos hscore_lo_pos hmass_lo_neg hscore_lo_neg
    hadj_min hadj_dominates

/--
Source-shaped finite Theorem 1 endpoint for arbitrary real floor-count sample
rates from per-pair common-dual log-MGF derivatives, source-level threshold
minimizers, and compact two-sided support. This avoids the global all-threshold
Legendre boundedness side condition by making the per-pair minimizer fact the
explicit source regularity hypothesis.
-/
theorem finiteFloorPkObjective_oneSub_hasExponentialRate_of_adjacent_logMGF_derivative_threshold_minimizers_of_straddling_support
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
  finiteFloorPkObjective_oneSub_hasExponentialRate_of_adjacent_leftTail_source_rates
    M sampleRate pairHi pairLo weight adjacentPair
    hweight_nonneg hweight_sum iMin hweight_pos
    (fun p =>
      twoSampleFloorScoreGapLeftTail_pairwiseThresholdRate_exponentialRateCertificate_of_logMGF_derivative_threshold_minimizer_of_straddling_support
        M sampleRate (pairHi p) (pairLo p)
        (hgHi p) (hgLo p) (a p) (z p) (hz p)
        (hderiv_hi p) (hderiv_lo p) (hthreshold_min p)
        (hstraddle_hi p) (hstraddle_lo p))
    hadj_min hadj_dominates

/--
Ordered comparison pairs for a finite seller chain.  A value records the
paper's convention `theta_j > theta_i` as a high/low pair of chain indices.
-/
abbrev finiteChainOrderedPair (n : ℕ) :=
  {p : Fin n × Fin n // p.2.val < p.1.val}

/-- High seller index in a finite-chain ordered comparison pair. -/
def finiteChainOrderedPairHi {n : ℕ} (p : finiteChainOrderedPair n) :
    Fin n :=
  p.1.1

/-- Low seller index in a finite-chain ordered comparison pair. -/
def finiteChainOrderedPairLo {n : ℕ} (p : finiteChainOrderedPair n) :
    Fin n :=
  p.1.2

/-- Adjacent low seller indices in a finite seller chain. -/
abbrev finiteChainAdjacentIndex (n : ℕ) :=
  {i : Fin n // i.val + 1 < n}

/-- Adjacent ordered pair `(i+1, i)` in a finite seller chain. -/
def finiteChainAdjacentPair {n : ℕ}
    (i : finiteChainAdjacentIndex n) : finiteChainOrderedPair n :=
  ⟨(⟨i.1.val + 1, i.2⟩, i.1), by simp⟩

/-- Threshold rate for an ordered comparison pair in a finite seller chain. -/
def finiteChainOrderedPairThresholdRate
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n → ℝ)
    (p : finiteChainOrderedPair n) : ℝ :=
  pairwiseSellerThresholdRate M sampleRate
    (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p)

/-- Support-safe extended threshold rate for an ordered finite-chain pair. -/
def finiteChainOrderedPairThresholdRateTop
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n → ℝ)
    (p : finiteChainOrderedPair n) : WithTop ℝ :=
  pairwiseSellerThresholdRateTop M sampleRate
    (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p)

/-- Threshold rate for an adjacent ordered pair in a finite seller chain. -/
def finiteChainAdjacentThresholdRate
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n → ℝ)
    (i : finiteChainAdjacentIndex n) : ℝ :=
  finiteChainOrderedPairThresholdRate M sampleRate (finiteChainAdjacentPair i)

/-- Support-safe extended threshold rate for an adjacent finite-chain pair. -/
def finiteChainAdjacentThresholdRateTop
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n → ℝ)
    (i : finiteChainAdjacentIndex n) : WithTop ℝ :=
  finiteChainOrderedPairThresholdRateTop M sampleRate (finiteChainAdjacentPair i)

/-- Minimum adjacent-pair threshold rate in a finite seller chain. -/
def minFiniteChainAdjacentThresholdRate
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    [Nonempty (finiteChainAdjacentIndex n)]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n → ℝ) :
    ℝ :=
  (Finset.univ : Finset (finiteChainAdjacentIndex n)).inf'
    Finset.univ_nonempty
    (finiteChainAdjacentThresholdRate M sampleRate)

/-- Minimum support-safe extended adjacent-pair threshold rate. -/
def minFiniteChainAdjacentThresholdRateTop
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    [Nonempty (finiteChainAdjacentIndex n)]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n → ℝ) :
    WithTop ℝ :=
  (Finset.univ : Finset (finiteChainAdjacentIndex n)).inf'
    Finset.univ_nonempty
    (finiteChainAdjacentThresholdRateTop M sampleRate)

/-- Displayed pairwise objective value for an ordered finite-chain pair. -/
def finiteChainOrderedPairObjectiveRate
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n → ℝ)
    (a : finiteChainOrderedPair n → ℝ) (p : finiteChainOrderedPair n) :
    ℝ :=
  M.pairwiseRateObjective sampleRate
    (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) (a p)

/-- Displayed pairwise objective value for an adjacent finite-chain pair. -/
def finiteChainAdjacentObjectiveRate
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n → ℝ)
    (a : finiteChainOrderedPair n → ℝ)
    (i : finiteChainAdjacentIndex n) : ℝ :=
  finiteChainOrderedPairObjectiveRate M sampleRate a (finiteChainAdjacentPair i)

/-- Minimum adjacent displayed pairwise objective rate in a finite seller chain. -/
def minFiniteChainAdjacentObjectiveRate
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    [Nonempty (finiteChainAdjacentIndex n)]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n → ℝ)
    (a : finiteChainOrderedPair n → ℝ) : ℝ :=
  (Finset.univ : Finset (finiteChainAdjacentIndex n)).inf'
    Finset.univ_nonempty
    (finiteChainAdjacentObjectiveRate M sampleRate a)

/--
If every adjacent support-safe threshold rate is represented by a finite real
rate and a selected adjacent pair minimizes those representatives, then the
support-safe adjacent minimum is that finite rate.
-/
theorem minFiniteChainAdjacentThresholdRateTop_eq_coe_adjacent_rate_of_top_eq
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    [Nonempty (finiteChainAdjacentIndex n)]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n → ℝ)
    (rate : finiteChainOrderedPair n → ℝ)
    (iMin : finiteChainAdjacentIndex n)
    (hpoint :
      ∀ p : finiteChainOrderedPair n,
        finiteChainOrderedPairThresholdRateTop M sampleRate p =
          (rate p : WithTop ℝ))
    (hmin :
      ∀ i : finiteChainAdjacentIndex n,
        rate (finiteChainAdjacentPair iMin) ≤
          rate (finiteChainAdjacentPair i)) :
    minFiniteChainAdjacentThresholdRateTop M sampleRate =
      (rate (finiteChainAdjacentPair iMin) : WithTop ℝ) := by
  classical
  have hpoint_adj :
      ∀ i : finiteChainAdjacentIndex n,
        finiteChainAdjacentThresholdRateTop M sampleRate i =
          (rate (finiteChainAdjacentPair i) : WithTop ℝ) := by
    intro i
    simpa [finiteChainAdjacentThresholdRateTop] using
      hpoint (finiteChainAdjacentPair i)
  apply le_antisymm
  · have hle :
        minFiniteChainAdjacentThresholdRateTop M sampleRate ≤
          finiteChainAdjacentThresholdRateTop M sampleRate iMin := by
      unfold minFiniteChainAdjacentThresholdRateTop
      exact Finset.inf'_le
        (s := (Finset.univ : Finset (finiteChainAdjacentIndex n)))
        (f := finiteChainAdjacentThresholdRateTop M sampleRate)
        (by simp : iMin ∈ (Finset.univ : Finset (finiteChainAdjacentIndex n)))
    calc
      minFiniteChainAdjacentThresholdRateTop M sampleRate
          ≤ finiteChainAdjacentThresholdRateTop M sampleRate iMin := hle
      _ = (rate (finiteChainAdjacentPair iMin) : WithTop ℝ) :=
          hpoint_adj iMin
  · unfold minFiniteChainAdjacentThresholdRateTop
    apply Finset.le_inf'
    intro i _hi
    rw [hpoint_adj i]
    exact_mod_cast hmin i

/--
Common-dual derivative data identifies the support-safe extended adjacent
source threshold-rate minimum with the finite displayed adjacent-objective
minimum.
-/
theorem minFiniteChainAdjacentThresholdRateTop_eq_coe_minFiniteChainAdjacentObjectiveRate_of_common_logMGF_derivatives
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
      (minFiniteChainAdjacentObjectiveRate M sampleRate a : WithTop ℝ) := by
  classical
  have hpoint :
      ∀ i : finiteChainAdjacentIndex n,
        finiteChainAdjacentThresholdRateTop M sampleRate i =
          (finiteChainAdjacentObjectiveRate M sampleRate a i : WithTop ℝ) := by
    intro i
    let p : finiteChainOrderedPair n := finiteChainAdjacentPair i
    have h :=
      pairwiseSellerThresholdRateTop_eq_coe_pairwiseRateObjective_of_common_logMGF_derivatives
        M sampleRate (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p)
        (hpositive_sample (finiteChainOrderedPairHi p))
        (hpositive_sample (finiteChainOrderedPairLo p))
        (a p) (z p) (hderiv_hi p) (hderiv_lo p)
    simpa [p, finiteChainAdjacentThresholdRateTop,
      finiteChainOrderedPairThresholdRateTop, finiteChainAdjacentObjectiveRate,
      finiteChainOrderedPairObjectiveRate] using h
  apply le_antisymm
  · obtain ⟨iMin, _hiMin, hmin_eq⟩ :=
      Finset.exists_mem_eq_inf'
        (s := (Finset.univ : Finset (finiteChainAdjacentIndex n)))
        (H := Finset.univ_nonempty)
        (f := finiteChainAdjacentObjectiveRate M sampleRate a)
    have hle :
        minFiniteChainAdjacentThresholdRateTop M sampleRate ≤
          finiteChainAdjacentThresholdRateTop M sampleRate iMin := by
      unfold minFiniteChainAdjacentThresholdRateTop
      exact Finset.inf'_le
        (s := (Finset.univ : Finset (finiteChainAdjacentIndex n)))
        (f := finiteChainAdjacentThresholdRateTop M sampleRate)
        (by simp : iMin ∈ (Finset.univ : Finset (finiteChainAdjacentIndex n)))
    calc
      minFiniteChainAdjacentThresholdRateTop M sampleRate
          ≤ finiteChainAdjacentThresholdRateTop M sampleRate iMin := hle
      _ = (finiteChainAdjacentObjectiveRate M sampleRate a iMin :
            WithTop ℝ) := hpoint iMin
      _ = (minFiniteChainAdjacentObjectiveRate M sampleRate a :
            WithTop ℝ) := by
          simpa [minFiniteChainAdjacentObjectiveRate] using
            (congrArg (fun x : ℝ => (x : WithTop ℝ)) hmin_eq).symm
  · unfold minFiniteChainAdjacentThresholdRateTop
    apply Finset.le_inf'
    intro i _hi
    have hle :
        minFiniteChainAdjacentObjectiveRate M sampleRate a ≤
          finiteChainAdjacentObjectiveRate M sampleRate a i := by
      unfold minFiniteChainAdjacentObjectiveRate
      exact Finset.inf'_le
        (s := (Finset.univ : Finset (finiteChainAdjacentIndex n)))
        (f := finiteChainAdjacentObjectiveRate M sampleRate a)
        (by simp : i ∈ (Finset.univ : Finset (finiteChainAdjacentIndex n)))
    rw [hpoint i]
    exact_mod_cast hle

/--
The selected adjacent pair realizes the minimum adjacent-pair threshold rate in
the finite seller chain.
-/
def finiteChainAdjacentThresholdRateMinimizer
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n → ℝ)
    (iMin : finiteChainAdjacentIndex n) : Prop :=
  ∀ i : finiteChainAdjacentIndex n,
    finiteChainAdjacentThresholdRate M sampleRate iMin ≤
      finiteChainAdjacentThresholdRate M sampleRate i

/--
Every ordered pair has an adjacent pair with no larger threshold rate. This is
the finite-chain statement of the paper's "adjacent pairs dominate the rate"
step.
-/
def finiteChainAdjacentThresholdRatesDominate
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n → ℝ) :
    Prop :=
  ∀ p : finiteChainOrderedPair n, ∃ i : finiteChainAdjacentIndex n,
    finiteChainAdjacentThresholdRate M sampleRate i ≤
      finiteChainOrderedPairThresholdRate M sampleRate p

/--
Every ordered pair has an adjacent pair with no larger displayed objective
rate at the supplied thresholds.
-/
def finiteChainAdjacentObjectiveRatesDominate
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n → ℝ)
    (a : finiteChainOrderedPair n → ℝ) : Prop :=
  ∀ p : finiteChainOrderedPair n, ∃ i : finiteChainAdjacentIndex n,
    finiteChainAdjacentObjectiveRate M sampleRate a i ≤
      finiteChainOrderedPairObjectiveRate M sampleRate a p

/--
Interval-local version of adjacent-pair dominance: for every ordered pair
`(j,i)`, a rate-dominating adjacent pair can be chosen between `i` and `j`.
-/
def finiteChainIntervalAdjacentThresholdRatesDominate
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n → ℝ) :
    Prop :=
  ∀ p : finiteChainOrderedPair n, ∃ i : finiteChainAdjacentIndex n,
    (finiteChainOrderedPairLo p).val ≤ i.1.val ∧
      i.1.val < (finiteChainOrderedPairHi p).val ∧
        finiteChainAdjacentThresholdRate M sampleRate i ≤
          finiteChainOrderedPairThresholdRate M sampleRate p

/--
Interval-local version of displayed objective-rate dominance.
-/
def finiteChainIntervalAdjacentObjectiveRatesDominate
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n → ℝ)
    (a : finiteChainOrderedPair n → ℝ) : Prop :=
  ∀ p : finiteChainOrderedPair n, ∃ i : finiteChainAdjacentIndex n,
    (finiteChainOrderedPairLo p).val ≤ i.1.val ∧
      i.1.val < (finiteChainOrderedPairHi p).val ∧
        finiteChainAdjacentObjectiveRate M sampleRate a i ≤
          finiteChainOrderedPairObjectiveRate M sampleRate a p

/--
Interval-local adjacent dominance implies the coarser adjacent-dominance
hypothesis used by finite aggregation.
-/
theorem finiteChainAdjacentThresholdRatesDominate_of_interval
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    {M : FiniteRatingLDPModel (Fin n) Rating} {sampleRate : Fin n → ℝ}
    (h : finiteChainIntervalAdjacentThresholdRatesDominate M sampleRate) :
    finiteChainAdjacentThresholdRatesDominate M sampleRate := by
  intro p
  rcases h p with ⟨i, _hlo, _hhi, hrate⟩
  exact ⟨i, hrate⟩

/--
The concrete independent joint floor-rating law has the expected two-coordinate
pairwise left-tail marginal for each ordered finite-chain comparison pair.
-/
theorem twoSampleFloorScoreGapLeftTailProb_eq_joint_floor_rating_prob
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    [DecidableEq (finiteChainOrderedPair n)]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n → ℝ)
    (p : finiteChainOrderedPair n) (k : ℕ) :
    twoSampleFloorScoreGapLeftTailProb M sampleRate
        (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) k =
      AppliedModelingLib.pmfProb (finiteChainJointFloorRatingLaw M sampleRate k)
        (fun sample =>
          finiteChainJointFloorAverageScore M sampleRate k sample
              (finiteChainOrderedPairHi p) ≤
            finiteChainJointFloorAverageScore M sampleRate k sample
              (finiteChainOrderedPairLo p)) := by
  classical
  let hi := finiteChainOrderedPairHi p
  let lo := finiteChainOrderedPairLo p
  let nHi := floorSampleCount sampleRate hi k
  let nLo := floorSampleCount sampleRate lo k
  let cHi : ℝ := ((nHi : ℕ) : ℝ)⁻¹
  let cLo : ℝ := ((nLo : ℕ) : ℝ)⁻¹
  have hne : hi ≠ lo := by
    intro h
    have hp : lo.val < hi.val := by
      simpa [hi, lo] using p.2
    have hval : hi.val = lo.val := congrArg Fin.val h
    rw [hval] at hp
    exact (Nat.lt_irrefl lo.val) hp
  have hmarginal :=
    AppliedModelingLib.pmfProb_pmfPi_twoCoord_eq_pmfProd_dependent
      (μ := fun θ : Fin n =>
        AppliedModelingLib.pmfProduct
          (Fin (floorSampleCount sampleRate θ k)) Rating (M.typeLaw θ))
      (i := hi) (j := lo) hne
      (p := fun hiSample loSample =>
        cHi * finiteIidScoreSum M.score hiSample ≤
          cLo * finiteIidScoreSum M.score loSample)
  have hpair :
      twoSampleFloorScoreGapLeftTailProb M sampleRate hi lo k =
        AppliedModelingLib.pmfProb
          (AppliedModelingLib.pmfProd
            (AppliedModelingLib.pmfProduct (Fin nHi) Rating (M.typeLaw hi))
            (AppliedModelingLib.pmfProduct (Fin nLo) Rating (M.typeLaw lo)))
          (fun sample =>
            cHi * finiteIidScoreSum M.score sample.1 ≤
              cLo * finiteIidScoreSum M.score sample.2) := by
    unfold twoSampleFloorScoreGapLeftTailProb twoSampleScoreGapLeftTailProb
      twoSampleRatingLaw twoSampleScoreGapSum
    dsimp [hi, lo, nHi, nLo, cHi, cLo]
    refine AppliedModelingLib.pmfProb_congr _ ?_
    intro sample
    constructor <;> intro h <;> linarith
  calc
    twoSampleFloorScoreGapLeftTailProb M sampleRate
        (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) k
        =
      twoSampleFloorScoreGapLeftTailProb M sampleRate hi lo k := by
        simp [hi, lo]
    _ =
      AppliedModelingLib.pmfProb
        (AppliedModelingLib.pmfProd
          (AppliedModelingLib.pmfProduct (Fin nHi) Rating (M.typeLaw hi))
          (AppliedModelingLib.pmfProduct (Fin nLo) Rating (M.typeLaw lo)))
        (fun sample =>
          cHi * finiteIidScoreSum M.score sample.1 ≤
            cLo * finiteIidScoreSum M.score sample.2) := hpair
    _ =
      AppliedModelingLib.pmfProb (finiteChainJointFloorRatingLaw M sampleRate k)
        (fun sample =>
          finiteChainJointFloorAverageScore M sampleRate k sample hi ≤
            finiteChainJointFloorAverageScore M sampleRate k sample lo) := by
        simpa [finiteChainJointFloorRatingLaw,
          finiteChainJointFloorAverageScore, hi, lo, nHi, nLo, cHi, cLo]
          using hmarginal.symm
    _ =
      AppliedModelingLib.pmfProb (finiteChainJointFloorRatingLaw M sampleRate k)
        (fun sample =>
          finiteChainJointFloorAverageScore M sampleRate k sample
              (finiteChainOrderedPairHi p) ≤
            finiteChainJointFloorAverageScore M sampleRate k sample
              (finiteChainOrderedPairLo p)) := by
        simp [hi, lo]

/--
Interval-local adjacent dominance for any exact per-pair rate family follows
from interval-local finite event bounds on the floor-count left-tail
probabilities.
-/
theorem finiteChainIntervalAdjacentRatesDominate_of_floor_leftTail_event_bounds
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    [DecidableEq (finiteChainOrderedPair n)]
    {M : FiniteRatingLDPModel (Fin n) Rating} {sampleRate : Fin n → ℝ}
    (rate : finiteChainOrderedPair n → ℝ)
    (hcert :
      ∀ p : finiteChainOrderedPair n,
        ExponentialRateCertificate
          (fun k : ℕ =>
            twoSampleFloorScoreGapLeftTailProb M sampleRate
              (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) k)
          (rate p))
    (hinterval_bound :
      ∀ p : finiteChainOrderedPair n,
        ∀ᶠ k in Filter.atTop,
          twoSampleFloorScoreGapLeftTailProb M sampleRate
              (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) k ≤
            ∑ m : AppliedModelingLib.FiniteIntervalAdjacentIndex
                (finiteChainOrderedPairLo p) (finiteChainOrderedPairHi p),
              twoSampleFloorScoreGapLeftTailProb M sampleRate m.succ m.1 k) :
    ∀ p : finiteChainOrderedPair n, ∃ i : finiteChainAdjacentIndex n,
      (finiteChainOrderedPairLo p).val ≤ i.1.val ∧
        i.1.val < (finiteChainOrderedPairHi p).val ∧
          rate (finiteChainAdjacentPair i) ≤ rate p := by
  classical
  intro p
  let ι := AppliedModelingLib.FiniteIntervalAdjacentIndex
    (finiteChainOrderedPairLo p) (finiteChainOrderedPairHi p)
  have hι_nonempty : Nonempty ι := by
    refine ⟨⟨finiteChainOrderedPairLo p, ?_, ?_⟩⟩
    · exact le_rfl
    · exact p.2
  let intervalPair : ι → finiteChainOrderedPair n :=
    fun m => ⟨(m.succ, m.1), by
      simpa [AppliedModelingLib.FiniteIntervalAdjacentIndex.succ] using
        Nat.lt_succ_self m.1.val⟩
  have hcomponent :
      ∃ m : ι, rate (intervalPair m) ≤ rate p := by
    have hq :
        ∀ m : ι,
          ExponentialRateCertificate
            (fun k : ℕ =>
              twoSampleFloorScoreGapLeftTailProb M sampleRate m.succ m.1 k)
            (rate (intervalPair m)) := by
      intro m
      simpa [intervalPair] using hcert (intervalPair m)
    exact
      AppliedModelingLib.Probability.exists_component_rate_le_of_eventually_le_finite_sum
        (ι := ι)
        (p := fun k : ℕ =>
          twoSampleFloorScoreGapLeftTailProb M sampleRate
            (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) k)
        (q := fun m : ι => fun k : ℕ =>
          twoSampleFloorScoreGapLeftTailProb M sampleRate m.succ m.1 k)
        (rateP := rate p)
        (rate := fun m : ι => rate (intervalPair m))
        (hcert p) hq (hinterval_bound p)
  rcases hcomponent with ⟨m, hmrate⟩
  let i : finiteChainAdjacentIndex n :=
    ⟨m.1, lt_of_le_of_lt (Nat.succ_le_of_lt m.2.2)
      (finiteChainOrderedPairHi p).isLt⟩
  refine ⟨i, m.2.1, m.2.2, ?_⟩
  simpa [i, intervalPair, finiteChainAdjacentPair,
    AppliedModelingLib.FiniteIntervalAdjacentIndex.succ] using hmrate

/--
Interval-local adjacent threshold-rate dominance follows from interval-local
finite event bounds on the floor-count left-tail probabilities. This is the
rate-theoretic version of the paper's last adjacent-pair reduction: if every
nonadjacent pair inversion probability is eventually bounded by the sum of
adjacent inversion probabilities along the interval, exact pairwise rates force
some interval-adjacent pair to have no larger threshold rate.
-/
theorem finiteChainIntervalAdjacentThresholdRatesDominate_of_floor_leftTail_event_bounds
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    [DecidableEq (finiteChainOrderedPair n)]
    {M : FiniteRatingLDPModel (Fin n) Rating} {sampleRate : Fin n → ℝ}
    (hcert :
      ∀ p : finiteChainOrderedPair n,
        ExponentialRateCertificate
          (fun k : ℕ =>
            twoSampleFloorScoreGapLeftTailProb M sampleRate
              (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) k)
          (finiteChainOrderedPairThresholdRate M sampleRate p))
    (hinterval_bound :
      ∀ p : finiteChainOrderedPair n,
        ∀ᶠ k in Filter.atTop,
          twoSampleFloorScoreGapLeftTailProb M sampleRate
              (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) k ≤
            ∑ m : AppliedModelingLib.FiniteIntervalAdjacentIndex
                (finiteChainOrderedPairLo p) (finiteChainOrderedPairHi p),
              twoSampleFloorScoreGapLeftTailProb M sampleRate m.succ m.1 k) :
    finiteChainIntervalAdjacentThresholdRatesDominate M sampleRate := by
  classical
  intro p
  let ι := AppliedModelingLib.FiniteIntervalAdjacentIndex
    (finiteChainOrderedPairLo p) (finiteChainOrderedPairHi p)
  have hι_nonempty : Nonempty ι := by
    refine ⟨⟨finiteChainOrderedPairLo p, ?_, ?_⟩⟩
    · exact le_rfl
    · exact p.2
  let intervalPair : ι → finiteChainOrderedPair n :=
    fun m => ⟨(m.succ, m.1), by
      simpa [AppliedModelingLib.FiniteIntervalAdjacentIndex.succ] using
        Nat.lt_succ_self m.1.val⟩
  have hcomponent :
      ∃ m : ι,
        finiteChainOrderedPairThresholdRate M sampleRate (intervalPair m) ≤
          finiteChainOrderedPairThresholdRate M sampleRate p := by
    have hq :
        ∀ m : ι,
          ExponentialRateCertificate
            (fun k : ℕ =>
              twoSampleFloorScoreGapLeftTailProb M sampleRate m.succ m.1 k)
            (finiteChainOrderedPairThresholdRate M sampleRate
              (intervalPair m)) := by
      intro m
      simpa [intervalPair] using hcert (intervalPair m)
    exact
      AppliedModelingLib.Probability.exists_component_rate_le_of_eventually_le_finite_sum
        (ι := ι)
        (p := fun k : ℕ =>
          twoSampleFloorScoreGapLeftTailProb M sampleRate
            (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) k)
        (q := fun m : ι => fun k : ℕ =>
          twoSampleFloorScoreGapLeftTailProb M sampleRate m.succ m.1 k)
        (rateP := finiteChainOrderedPairThresholdRate M sampleRate p)
        (rate := fun m : ι =>
          finiteChainOrderedPairThresholdRate M sampleRate (intervalPair m))
        (hcert p) hq (hinterval_bound p)
  rcases hcomponent with ⟨m, hmrate⟩
  let i : finiteChainAdjacentIndex n :=
    ⟨m.1, lt_of_le_of_lt (Nat.succ_le_of_lt m.2.2)
      (finiteChainOrderedPairHi p).isLt⟩
  refine ⟨i, m.2.1, m.2.2, ?_⟩
  simpa [i, intervalPair, finiteChainAdjacentThresholdRate,
    finiteChainOrderedPairThresholdRate, finiteChainAdjacentPair,
    AppliedModelingLib.FiniteIntervalAdjacentIndex.succ] using hmrate

/--
The interval-local floor-count left-tail event bounds follow from a joint
finite score law whose two-coordinate marginals agree with the pairwise
floor-count left-tail probabilities. This is the source-paper coupling behind
the adjacent-inversion reduction.
-/
theorem finiteChainIntervalFloorLeftTailEventBounds_of_joint_score_marginals
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    [DecidableEq (finiteChainOrderedPair n)]
    {Ω : ℕ → Type*} [∀ k : ℕ, Fintype (Ω k)]
    [∀ k : ℕ, DecidableEq (Ω k)]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n → ℝ)
    (μ : ∀ k : ℕ, PMF (Ω k)) (score : ∀ k : ℕ, Ω k → Fin n → ℝ)
    (hmarginal :
      ∀ (p : finiteChainOrderedPair n) (k : ℕ),
        twoSampleFloorScoreGapLeftTailProb M sampleRate
            (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) k =
          AppliedModelingLib.pmfProb (μ k)
            (fun ω => score k ω (finiteChainOrderedPairHi p) ≤
              score k ω (finiteChainOrderedPairLo p))) :
    ∀ p : finiteChainOrderedPair n,
      ∀ᶠ k in Filter.atTop,
        twoSampleFloorScoreGapLeftTailProb M sampleRate
            (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) k ≤
          ∑ m : AppliedModelingLib.FiniteIntervalAdjacentIndex
              (finiteChainOrderedPairLo p) (finiteChainOrderedPairHi p),
            twoSampleFloorScoreGapLeftTailProb M sampleRate m.succ m.1 k := by
  classical
  intro p
  filter_upwards with k
  let ι := AppliedModelingLib.FiniteIntervalAdjacentIndex
    (finiteChainOrderedPairLo p) (finiteChainOrderedPairHi p)
  have hbound :=
    AppliedModelingLib.pmfProb_pairInversion_le_sum_intervalAdjacentInversion
      (μ k) (score k)
      (i := finiteChainOrderedPairLo p)
      (j := finiteChainOrderedPairHi p)
      p.2
  have hsum_eq :
      (∑ m : ι,
        AppliedModelingLib.pmfProb (μ k) (fun ω => score k ω m.succ ≤ score k ω m.1)) =
      ∑ m : ι,
        twoSampleFloorScoreGapLeftTailProb M sampleRate m.succ m.1 k := by
    refine Finset.sum_congr rfl ?_
    intro m _
    let pAdj : finiteChainOrderedPair n :=
      ⟨(m.succ, m.1), by
        simpa [AppliedModelingLib.FiniteIntervalAdjacentIndex.succ] using
          Nat.lt_succ_self m.1.val⟩
    have hm := hmarginal pAdj k
    simpa [pAdj] using hm.symm
  calc
    twoSampleFloorScoreGapLeftTailProb M sampleRate
        (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) k
        =
      AppliedModelingLib.pmfProb (μ k)
        (fun ω => score k ω (finiteChainOrderedPairHi p) ≤
          score k ω (finiteChainOrderedPairLo p)) := hmarginal p k
    _ ≤
      ∑ m : ι,
        AppliedModelingLib.pmfProb (μ k) (fun ω => score k ω m.succ ≤ score k ω m.1) :=
      hbound
    _ =
      ∑ m : ι,
        twoSampleFloorScoreGapLeftTailProb M sampleRate m.succ m.1 k :=
      hsum_eq

/--
Support-safe finite-chain Theorem 1 endpoint from exact pairwise LDP
certificates at the extended threshold rates.  The concrete joint floor-rating
law supplies the adjacent-inversion reduction; the pairwise certificate
package is the only remaining analytic/Laplace input.
-/
theorem finiteChainUniformFloorPkObjective_oneSub_hasExtendedExponentialRate_of_joint_floor_rating_law_min_threshold_rate_top_of_pairwise_ldp_certificates
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    [DecidableEq (finiteChainOrderedPair n)]
    [Nonempty (finiteChainAdjacentIndex n)]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n → ℝ)
    (C :
      PairwiseThresholdRateTopLdpCertificate M sampleRate
        finiteChainOrderedPairHi finiteChainOrderedPairLo) :
    HasExtendedExponentialRate
      (fun k : ℕ =>
        1 - finiteUniformFloorPkObjective M sampleRate
          finiteChainOrderedPairHi finiteChainOrderedPairLo k)
      (minFiniteChainAdjacentThresholdRateTop M sampleRate) := by
  classical
  let rate : finiteChainOrderedPair n → ℝ := C.rate
  have hcert :
      ∀ p : finiteChainOrderedPair n,
        ExponentialRateCertificate
          (fun k : ℕ =>
            twoSampleFloorScoreGapLeftTailProb M sampleRate
              (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) k)
          (rate p) := by
    intro p
    simpa [rate] using C.leftTail p
  have hinterval_bound :
      ∀ p : finiteChainOrderedPair n,
        ∀ᶠ k in Filter.atTop,
          twoSampleFloorScoreGapLeftTailProb M sampleRate
              (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) k ≤
            ∑ m : AppliedModelingLib.FiniteIntervalAdjacentIndex
                (finiteChainOrderedPairLo p) (finiteChainOrderedPairHi p),
              twoSampleFloorScoreGapLeftTailProb M sampleRate m.succ m.1 k :=
    finiteChainIntervalFloorLeftTailEventBounds_of_joint_score_marginals
      (Ω := fun k : ℕ => finiteChainJointFloorRatingSample Rating sampleRate k)
      M sampleRate
      (fun k : ℕ => finiteChainJointFloorRatingLaw M sampleRate k)
      (fun k sample θ => finiteChainJointFloorAverageScore M sampleRate k sample θ)
      (twoSampleFloorScoreGapLeftTailProb_eq_joint_floor_rating_prob
        M sampleRate)
  have hinterval_dom :
      ∀ p : finiteChainOrderedPair n, ∃ i : finiteChainAdjacentIndex n,
        (finiteChainOrderedPairLo p).val ≤ i.1.val ∧
          i.1.val < (finiteChainOrderedPairHi p).val ∧
            rate (finiteChainAdjacentPair i) ≤ rate p :=
    finiteChainIntervalAdjacentRatesDominate_of_floor_leftTail_event_bounds
      rate hcert hinterval_bound
  have hadj_dominates :
      ∀ p : finiteChainOrderedPair n, ∃ i : finiteChainAdjacentIndex n,
        rate (finiteChainAdjacentPair i) ≤ rate p := by
    intro p
    rcases hinterval_dom p with ⟨i, _hlo, _hhi, hrate⟩
    exact ⟨i, hrate⟩
  let adjRate : finiteChainAdjacentIndex n → ℝ :=
    fun i => rate (finiteChainAdjacentPair i)
  obtain ⟨iMin, _hiMin, hmin_eq⟩ :=
    Finset.exists_mem_eq_inf'
      (s := (Finset.univ : Finset (finiteChainAdjacentIndex n)))
      (H := Finset.univ_nonempty) (f := adjRate)
  have hadj_min :
      ∀ i : finiteChainAdjacentIndex n,
        rate (finiteChainAdjacentPair iMin) ≤
          rate (finiteChainAdjacentPair i) := by
    intro i
    have hle :
        (Finset.univ : Finset (finiteChainAdjacentIndex n)).inf'
            Finset.univ_nonempty
            (fun i => rate (finiteChainAdjacentPair i)) ≤
          rate (finiteChainAdjacentPair i) := by
      exact Finset.inf'_le
        (s := (Finset.univ : Finset (finiteChainAdjacentIndex n)))
        (f := fun i => rate (finiteChainAdjacentPair i))
        (by simp : i ∈ (Finset.univ : Finset (finiteChainAdjacentIndex n)))
    have hle' : adjRate iMin ≤ adjRate i := by
      have hmin_eq' :
          (Finset.univ : Finset (finiteChainAdjacentIndex n)).inf'
              Finset.univ_nonempty
              (fun i => rate (finiteChainAdjacentPair i)) =
            rate (finiteChainAdjacentPair iMin) := by
        simpa [adjRate] using hmin_eq
      change rate (finiteChainAdjacentPair iMin) ≤
        rate (finiteChainAdjacentPair i)
      rw [← hmin_eq']
      exact hle
    simpa [adjRate] using hle'
  have htop_point :
      ∀ p : finiteChainOrderedPair n,
        finiteChainOrderedPairThresholdRateTop M sampleRate p =
          (rate p : WithTop ℝ) := by
    intro p
    simpa [rate, finiteChainOrderedPairThresholdRateTop] using
      C.threshold_rate_top_eq p
  have htop_eq :
      minFiniteChainAdjacentThresholdRateTop M sampleRate =
        (rate (finiteChainAdjacentPair iMin) : WithTop ℝ) :=
    minFiniteChainAdjacentThresholdRateTop_eq_coe_adjacent_rate_of_top_eq
      M sampleRate rate iMin htop_point hadj_min
  letI : Nonempty (finiteChainOrderedPair n) := ⟨finiteChainAdjacentPair iMin⟩
  have hmain :
      HasExponentialRate
        (fun k : ℕ =>
          1 - finiteUniformFloorPkObjective M sampleRate
            finiteChainOrderedPairHi finiteChainOrderedPairLo k)
        (rate (finiteChainAdjacentPair iMin)) :=
    finiteFloorPkObjective_oneSub_hasExponentialRate_of_adjacent_leftTail_rates
      (Pair := finiteChainOrderedPair n)
      (Adj := finiteChainAdjacentIndex n)
      M sampleRate finiteChainOrderedPairHi finiteChainOrderedPairLo
      (uniformPairWeight (finiteChainOrderedPair n))
      finiteChainAdjacentPair
      (uniformPairWeight_nonneg (finiteChainOrderedPair n))
      (uniformPairWeight_sum_eq_one (finiteChainOrderedPair n))
      iMin
      (uniformPairWeight_pos
        (finiteChainOrderedPair n) (finiteChainAdjacentPair iMin))
      rate hcert hadj_min hadj_dominates
  rw [htop_eq]
  exact HasExtendedExponentialRate.finite hmain

/--
Support-safe finite-chain Theorem 1 endpoint from the paper-facing pairwise
regularity package.  This is the compact route that keeps the extended
finite-support threshold convention at the top level while deriving the
pairwise LDP certificates from common-dual derivative and straddling data.
-/
theorem finiteChainUniformFloorPkObjective_oneSub_hasExtendedExponentialRate_of_joint_floor_rating_law_min_threshold_rate_top_of_pairwise_threshold_rate_regularity
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    [DecidableEq (finiteChainOrderedPair n)]
    [Nonempty (finiteChainAdjacentIndex n)]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n → ℝ)
    (hpositive_sample : ∀ θ : Fin n, 0 < sampleRate θ)
    (C :
      PairwiseThresholdRateRegularity M sampleRate
        finiteChainOrderedPairHi finiteChainOrderedPairLo) :
    HasExtendedExponentialRate
      (fun k : ℕ =>
        1 - finiteUniformFloorPkObjective M sampleRate
          finiteChainOrderedPairHi finiteChainOrderedPairLo k)
      (minFiniteChainAdjacentThresholdRateTop M sampleRate) :=
  finiteChainUniformFloorPkObjective_oneSub_hasExtendedExponentialRate_of_joint_floor_rating_law_min_threshold_rate_top_of_pairwise_ldp_certificates
    M sampleRate
    (PairwiseThresholdRateTopLdpCertificate.of_regularity
      M sampleRate finiteChainOrderedPairHi finiteChainOrderedPairLo
      (fun p => hpositive_sample (finiteChainOrderedPairHi p))
      (fun p => hpositive_sample (finiteChainOrderedPairLo p))
      C)

/--
Support-safe finite-chain Theorem 1 endpoint from stationary real-rate
pairwise duals and primitive bottom/top rating support.  The common threshold
for each comparison pair is derived internally from stationarity.
-/
theorem finiteChainUniformFloorPkObjective_oneSub_hasExtendedExponentialRate_of_joint_floor_rating_law_min_threshold_rate_top_of_pairwise_dual_stationary_and_score_bounds
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    [DecidableEq (finiteChainOrderedPair n)]
    [Nonempty (finiteChainAdjacentIndex n)]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n → ℝ)
    (hpositive_sample : ∀ θ : Fin n, 0 < sampleRate θ)
    (z : finiteChainOrderedPair n → ℝ)
    (hz : ∀ p : finiteChainOrderedPair n, z p ≤ 0)
    (hdual_stationary :
      ∀ p : finiteChainOrderedPair n,
        HasDerivAt
          (fun t : ℝ =>
            pairwiseDualLogMGF M sampleRate
              (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) t)
          0 (z p))
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
  finiteChainUniformFloorPkObjective_oneSub_hasExtendedExponentialRate_of_joint_floor_rating_law_min_threshold_rate_top_of_pairwise_ldp_certificates
    M sampleRate
    (PairwiseThresholdRateTopLdpCertificate.of_pairwise_dual_stationary_and_score_bounds
      M sampleRate finiteChainOrderedPairHi finiteChainOrderedPairLo
      (fun p => hpositive_sample (finiteChainOrderedPairHi p))
      (fun p => hpositive_sample (finiteChainOrderedPairLo p))
      z hz hdual_stationary rLow rHigh
      (fun p => hmass_low (finiteChainOrderedPairHi p))
      (fun p => hmass_high (finiteChainOrderedPairHi p))
      (fun p => hmass_low (finiteChainOrderedPairLo p))
      (fun p => hmass_high (finiteChainOrderedPairLo p))
      hscore_low_le hscore_le_high hscore_lt)

/--
Support-safe finite-chain Theorem 1 endpoint from expected-score ordering,
nonpositive tilted-mean crossings, and primitive bottom/top rating support.
Stationary duals and common thresholds are selected internally.
-/
theorem finiteChainUniformFloorPkObjective_oneSub_hasExtendedExponentialRate_of_joint_floor_rating_law_min_threshold_rate_top_of_expected_score_gap_and_tilted_crossing_and_score_bounds
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    [DecidableEq (finiteChainOrderedPair n)]
    [Nonempty (finiteChainAdjacentIndex n)]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n → ℝ)
    (hpositive_sample : ∀ θ : Fin n, 0 < sampleRate θ)
    (hmean_gap :
      ∀ p : finiteChainOrderedPair n,
        AppliedModelingLib.pmfExp (M.typeLaw (finiteChainOrderedPairLo p)) M.score ≤
          AppliedModelingLib.pmfExp (M.typeLaw (finiteChainOrderedPairHi p)) M.score)
    (zCross : finiteChainOrderedPair n → ℝ)
    (hzCross : ∀ p : finiteChainOrderedPair n, zCross p ≤ 0)
    (hcross :
      ∀ p : finiteChainOrderedPair n,
        pairwiseTiltedScoreMeanGap M sampleRate
          (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p)
          (zCross p) ≤ 0)
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
  finiteChainUniformFloorPkObjective_oneSub_hasExtendedExponentialRate_of_joint_floor_rating_law_min_threshold_rate_top_of_pairwise_ldp_certificates
    M sampleRate
    (PairwiseThresholdRateTopLdpCertificate.of_expected_score_gap_and_tilted_crossing_and_score_bounds
      M sampleRate finiteChainOrderedPairHi finiteChainOrderedPairLo
      (fun p => hpositive_sample (finiteChainOrderedPairHi p))
      (fun p => hpositive_sample (finiteChainOrderedPairLo p))
      hmean_gap zCross hzCross hcross rLow rHigh
      (fun p => hmass_low (finiteChainOrderedPairHi p))
      (fun p => hmass_high (finiteChainOrderedPairHi p))
      (fun p => hmass_low (finiteChainOrderedPairLo p))
      (fun p => hmass_high (finiteChainOrderedPairLo p))
      hscore_low_le hscore_le_high hscore_lt)

/--
Support-safe finite-chain Theorem 1 endpoint from expected-score ordering and
primitive common bottom/top rating support.  The nonpositive stationary duals,
common thresholds, and pairwise LDP certificates are selected internally.
-/
theorem finiteChainUniformFloorPkObjective_oneSub_hasExtendedExponentialRate_of_joint_floor_rating_law_min_threshold_rate_top_of_expected_score_gap_and_common_extreme_support
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
  finiteChainUniformFloorPkObjective_oneSub_hasExtendedExponentialRate_of_joint_floor_rating_law_min_threshold_rate_top_of_pairwise_ldp_certificates
    M sampleRate
    (PairwiseThresholdRateTopLdpCertificate.of_expected_score_gap_and_common_extreme_support
      M sampleRate finiteChainOrderedPairHi finiteChainOrderedPairLo
      (fun p => hpositive_sample (finiteChainOrderedPairHi p))
      (fun p => hpositive_sample (finiteChainOrderedPairLo p))
      hmean_gap rLow rHigh
      (fun p => hmass_low (finiteChainOrderedPairHi p))
      (fun p => hmass_high (finiteChainOrderedPairHi p))
      (fun p => hmass_low (finiteChainOrderedPairLo p))
      (fun p => hmass_high (finiteChainOrderedPairLo p))
      hscore_low_le hscore_le_high hscore_lt)

/--
Finite-chain extended-rate endpoint from expected-score ordering and per-law
positive-mass extrema. This is the source-faithful route when a displayed top
rating can have zero probability for some seller types.
-/
theorem finiteChainUniformFloorPkObjective_oneSub_hasExtendedExponentialRate_of_joint_floor_rating_law_min_threshold_rate_top_of_expected_score_gap_and_support_extrema
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    [DecidableEq (finiteChainOrderedPair n)]
    [Nonempty (finiteChainAdjacentIndex n)]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n → ℝ)
    (hpositive_sample : ∀ θ : Fin n, 0 < sampleRate θ)
    (hmean_gap :
      ∀ p : finiteChainOrderedPair n,
        AppliedModelingLib.pmfExp (M.typeLaw (finiteChainOrderedPairLo p)) M.score ≤
          AppliedModelingLib.pmfExp (M.typeLaw (finiteChainOrderedPairHi p)) M.score)
    (rHiLow rHiHigh rLoLow rLoHigh : finiteChainOrderedPair n → Rating)
    (hmass_hi_low :
      ∀ p : finiteChainOrderedPair n,
        0 < (M.typeLaw (finiteChainOrderedPairHi p) (rHiLow p)).toReal)
    (hmass_hi_high :
      ∀ p : finiteChainOrderedPair n,
        0 < (M.typeLaw (finiteChainOrderedPairHi p) (rHiHigh p)).toReal)
    (hmass_lo_low :
      ∀ p : finiteChainOrderedPair n,
        0 < (M.typeLaw (finiteChainOrderedPairLo p) (rLoLow p)).toReal)
    (hmass_lo_high :
      ∀ p : finiteChainOrderedPair n,
        0 < (M.typeLaw (finiteChainOrderedPairLo p) (rLoHigh p)).toReal)
    (hscore_hi_low_le :
      ∀ p : finiteChainOrderedPair n, ∀ r : Rating,
        0 < (M.typeLaw (finiteChainOrderedPairHi p) r).toReal →
          M.score (rHiLow p) ≤ M.score r)
    (hscore_hi_le_high :
      ∀ p : finiteChainOrderedPair n, ∀ r : Rating,
        0 < (M.typeLaw (finiteChainOrderedPairHi p) r).toReal →
          M.score r ≤ M.score (rHiHigh p))
    (hscore_lo_low_le :
      ∀ p : finiteChainOrderedPair n, ∀ r : Rating,
        0 < (M.typeLaw (finiteChainOrderedPairLo p) r).toReal →
          M.score (rLoLow p) ≤ M.score r)
    (hscore_lo_le_high :
      ∀ p : finiteChainOrderedPair n, ∀ r : Rating,
        0 < (M.typeLaw (finiteChainOrderedPairLo p) r).toReal →
          M.score r ≤ M.score (rLoHigh p))
    (hscore_hi_span :
      ∀ p : finiteChainOrderedPair n,
        M.score (rHiLow p) < M.score (rHiHigh p))
    (hscore_lo_span :
      ∀ p : finiteChainOrderedPair n,
        M.score (rLoLow p) < M.score (rLoHigh p))
    (hscore_cross :
      ∀ p : finiteChainOrderedPair n,
        M.score (rHiLow p) < M.score (rLoHigh p)) :
    HasExtendedExponentialRate
      (fun k : ℕ =>
        1 - finiteUniformFloorPkObjective M sampleRate
          finiteChainOrderedPairHi finiteChainOrderedPairLo k)
      (minFiniteChainAdjacentThresholdRateTop M sampleRate) :=
  finiteChainUniformFloorPkObjective_oneSub_hasExtendedExponentialRate_of_joint_floor_rating_law_min_threshold_rate_top_of_pairwise_ldp_certificates
    M sampleRate
    (PairwiseThresholdRateTopLdpCertificate.of_expected_score_gap_and_support_extrema
      M sampleRate finiteChainOrderedPairHi finiteChainOrderedPairLo
      (fun p => hpositive_sample (finiteChainOrderedPairHi p))
      (fun p => hpositive_sample (finiteChainOrderedPairLo p))
      hmean_gap rHiLow rHiHigh rLoLow rLoHigh
      hmass_hi_low hmass_hi_high hmass_lo_low hmass_lo_high
      hscore_hi_low_le hscore_hi_le_high
      hscore_lo_low_le hscore_lo_le_high
      hscore_hi_span hscore_lo_span hscore_cross)

/--
Source-shaped finite-chain Theorem 1 endpoint from ordinal upper-tail
dominance.  This packages the paper's monotone finite rating-scale primitive:
if higher source types have weakly larger upper-tail rating probabilities and
scores are monotone on the ordered rating scale, Lean derives the expected-score
ordering used by the support-safe finite-support endpoint.
-/
theorem finiteChainUniformFloorPkObjective_oneSub_hasExtendedExponentialRate_of_joint_floor_rating_law_min_threshold_rate_top_of_rating_tail_dominance_and_common_extreme_support
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
      (minFiniteChainAdjacentThresholdRateTop M sampleRate) := by
  have hmean_gap :
      ∀ p : finiteChainOrderedPair n,
        AppliedModelingLib.pmfExp (M.typeLaw (finiteChainOrderedPairLo p)) M.score ≤
          AppliedModelingLib.pmfExp (M.typeLaw (finiteChainOrderedPairHi p)) M.score :=
    fun p =>
      AppliedModelingLib.pmfExp_le_pmfExp_of_fin_tail_prob_le
        (M.typeLaw (finiteChainOrderedPairLo p))
        (M.typeLaw (finiteChainOrderedPairHi p))
        M.score hscore_mono (htail p)
  have hscore_low_le : ∀ r : Fin (m + 1), M.score 0 ≤ M.score r :=
    fun r => hscore_mono (Fin.zero_le r)
  have hscore_le_high :
      ∀ r : Fin (m + 1), M.score r ≤ M.score (Fin.last m) :=
    fun r => hscore_mono (Fin.le_last r)
  exact
    finiteChainUniformFloorPkObjective_oneSub_hasExtendedExponentialRate_of_joint_floor_rating_law_min_threshold_rate_top_of_expected_score_gap_and_common_extreme_support
      M sampleRate hpositive_sample hmean_gap 0 (Fin.last m)
      hmass_low hmass_high hscore_low_le hscore_le_high hscore_lt

/--
Source-shaped finite-chain Theorem 1 endpoint from ordinal upper-tail
dominance and full finite rating support.  The common bottom/top atom support
used by the finite-support lower-bound route is derived internally from
`FiniteRatingLDPModel.fullSupport`.
-/
theorem finiteChainUniformFloorPkObjective_oneSub_hasExtendedExponentialRate_of_joint_floor_rating_law_min_threshold_rate_top_of_rating_tail_dominance_and_full_support
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
  finiteChainUniformFloorPkObjective_oneSub_hasExtendedExponentialRate_of_joint_floor_rating_law_min_threshold_rate_top_of_rating_tail_dominance_and_common_extreme_support
    M sampleRate hpositive_sample htail hscore_mono
    (fun θ => M.mass_pos_of_fullSupport hfull_support θ 0)
    (fun θ => M.mass_pos_of_fullSupport hfull_support θ (Fin.last m))
    hscore_lt

/--
Finite-chain Theorem 1 endpoint.  This specializes the generic weighted
adjacent-pair theorem to sellers indexed by a strict finite chain, ordered
comparison pairs `(j,i)` with `i < j`, uniform Kendall weights, and adjacent
pairs `(i+1,i)`.
-/
theorem finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_adjacent_logMGF_derivative_threshold_minimizers_of_straddling_support
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
        (finiteChainOrderedPairLo (finiteChainAdjacentPair iMin))) := by
  letI : Nonempty (finiteChainOrderedPair n) :=
    ⟨finiteChainAdjacentPair iMin⟩
  simpa [finiteUniformFloorPkObjective] using
    finiteFloorPkObjective_oneSub_hasExponentialRate_of_adjacent_logMGF_derivative_threshold_minimizers_of_straddling_support
      (Pair := finiteChainOrderedPair n)
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
      a z hz hderiv_hi hderiv_lo hthreshold_min
      hstraddle_hi hstraddle_lo hadj_min hadj_dominates

/--
Finite-chain Theorem 1 endpoint using named adjacent threshold-rate
conditions.  This exposes the paper's final adjacent-pair reduction as a
source-level rate dominance predicate instead of an arbitrary `Pair`/`Adj`
existential.
-/
theorem finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_adjacent_threshold_rate_conditions
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
      finiteChainAdjacentThresholdRatesDominate M sampleRate) :
    HasExponentialRate
      (fun k : ℕ =>
        1 - finiteUniformFloorPkObjective M sampleRate
          finiteChainOrderedPairHi finiteChainOrderedPairLo k)
      (finiteChainAdjacentThresholdRate M sampleRate iMin) := by
  have hadj_min' :
      ∀ i : finiteChainAdjacentIndex n,
        pairwiseSellerThresholdRate M sampleRate
            (finiteChainOrderedPairHi (finiteChainAdjacentPair iMin))
            (finiteChainOrderedPairLo (finiteChainAdjacentPair iMin)) ≤
          pairwiseSellerThresholdRate M sampleRate
            (finiteChainOrderedPairHi (finiteChainAdjacentPair i))
            (finiteChainOrderedPairLo (finiteChainAdjacentPair i)) := by
    intro i
    simpa [finiteChainAdjacentThresholdRate,
      finiteChainOrderedPairThresholdRate] using hadj_min i
  have hadj_dominates' :
      ∀ p : finiteChainOrderedPair n, ∃ i : finiteChainAdjacentIndex n,
        pairwiseSellerThresholdRate M sampleRate
            (finiteChainOrderedPairHi (finiteChainAdjacentPair i))
            (finiteChainOrderedPairLo (finiteChainAdjacentPair i)) ≤
          pairwiseSellerThresholdRate M sampleRate
            (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) := by
    intro p
    rcases hadj_dominates p with ⟨i, hi⟩
    exact ⟨i, by
      simpa [finiteChainAdjacentThresholdRate,
        finiteChainOrderedPairThresholdRate] using hi⟩
  simpa [finiteChainAdjacentThresholdRate, finiteChainOrderedPairThresholdRate] using
    finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_adjacent_logMGF_derivative_threshold_minimizers_of_straddling_support
      M sampleRate hpositive_sample a z hz hderiv_hi hderiv_lo
      hthreshold_min hstraddle_hi hstraddle_lo iMin
      hadj_min' hadj_dominates'

/--
Finite-chain Theorem 1 endpoint from interval-local adjacent threshold-rate
dominance.
-/
theorem finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_interval_adjacent_threshold_rate_dominance
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
  finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_adjacent_threshold_rate_conditions
    M sampleRate hpositive_sample a z hz hderiv_hi hderiv_lo hthreshold_min
    hstraddle_hi hstraddle_lo iMin hadj_min
    (finiteChainAdjacentThresholdRatesDominate_of_interval hadj_dominates)

/--
Finite-chain Theorem 1 endpoint with the exponent written as the finite
minimum over adjacent threshold rates.  The adjacent minimizer is selected
internally from the finite chain.
-/
theorem finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_interval_adjacent_threshold_rate_dominance_min_rate
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
      (minFiniteChainAdjacentThresholdRate M sampleRate) := by
  classical
  let adjRate : finiteChainAdjacentIndex n → ℝ :=
    finiteChainAdjacentThresholdRate M sampleRate
  obtain ⟨iMin, _hiMin, hmin_eq⟩ :=
    Finset.exists_mem_eq_inf'
      (s := (Finset.univ : Finset (finiteChainAdjacentIndex n)))
      (H := Finset.univ_nonempty) (f := adjRate)
  have hadj_min :
      finiteChainAdjacentThresholdRateMinimizer M sampleRate iMin := by
    intro i
    have hle :
        minFiniteChainAdjacentThresholdRate M sampleRate ≤
          finiteChainAdjacentThresholdRate M sampleRate i := by
      unfold minFiniteChainAdjacentThresholdRate
      exact Finset.inf'_le
        (s := (Finset.univ : Finset (finiteChainAdjacentIndex n)))
        (f := finiteChainAdjacentThresholdRate M sampleRate)
        (by simp : i ∈ (Finset.univ : Finset (finiteChainAdjacentIndex n)))
    dsimp [adjRate] at hmin_eq
    rw [hmin_eq.symm]
    exact hle
  have hrate_eq :
      finiteChainAdjacentThresholdRate M sampleRate iMin =
        minFiniteChainAdjacentThresholdRate M sampleRate := by
    dsimp [adjRate] at hmin_eq
    exact hmin_eq.symm
  have hmain :=
    finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_interval_adjacent_threshold_rate_dominance
      M sampleRate hpositive_sample a z hz hderiv_hi hderiv_lo hthreshold_min
      hstraddle_hi hstraddle_lo iMin hadj_min hadj_dominates
  simpa [hrate_eq] using hmain

/--
Finite-chain Theorem 1 endpoint from pairwise floor-count left-tail exact-rate
certificates and interval-local adjacent threshold-rate dominance. This is the
aggregation core used when the pairwise source-rate identity has already been
proved, avoiding any need to expose source-level threshold minimizer
predicates at this layer.
-/
theorem finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_interval_adjacent_threshold_rate_dominance_min_rate_of_leftTail_certificates
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    [DecidableEq (finiteChainOrderedPair n)]
    [Nonempty (finiteChainAdjacentIndex n)]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n → ℝ)
    (hleftTail :
      ∀ p : finiteChainOrderedPair n,
        ExponentialRateCertificate
          (fun k : ℕ =>
            twoSampleFloorScoreGapLeftTailProb M sampleRate
              (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) k)
          (finiteChainOrderedPairThresholdRate M sampleRate p))
    (hadj_dominates :
      finiteChainIntervalAdjacentThresholdRatesDominate M sampleRate) :
    HasExponentialRate
      (fun k : ℕ =>
        1 - finiteUniformFloorPkObjective M sampleRate
          finiteChainOrderedPairHi finiteChainOrderedPairLo k)
      (minFiniteChainAdjacentThresholdRate M sampleRate) := by
  classical
  let adjRate : finiteChainAdjacentIndex n → ℝ :=
    finiteChainAdjacentThresholdRate M sampleRate
  obtain ⟨iMin, _hiMin, hmin_eq⟩ :=
    Finset.exists_mem_eq_inf'
      (s := (Finset.univ : Finset (finiteChainAdjacentIndex n)))
      (H := Finset.univ_nonempty) (f := adjRate)
  have hadj_min :
      ∀ i : finiteChainAdjacentIndex n,
        pairwiseSellerThresholdRate M sampleRate
            (finiteChainOrderedPairHi (finiteChainAdjacentPair iMin))
            (finiteChainOrderedPairLo (finiteChainAdjacentPair iMin)) ≤
          pairwiseSellerThresholdRate M sampleRate
            (finiteChainOrderedPairHi (finiteChainAdjacentPair i))
            (finiteChainOrderedPairLo (finiteChainAdjacentPair i)) := by
    intro i
    have hle :
        minFiniteChainAdjacentThresholdRate M sampleRate ≤
          finiteChainAdjacentThresholdRate M sampleRate i := by
      unfold minFiniteChainAdjacentThresholdRate
      exact Finset.inf'_le
        (s := (Finset.univ : Finset (finiteChainAdjacentIndex n)))
        (f := finiteChainAdjacentThresholdRate M sampleRate)
        (by simp : i ∈ (Finset.univ : Finset (finiteChainAdjacentIndex n)))
    dsimp [adjRate] at hmin_eq
    have hle' :
        finiteChainAdjacentThresholdRate M sampleRate iMin ≤
          finiteChainAdjacentThresholdRate M sampleRate i := by
      simpa [minFiniteChainAdjacentThresholdRate, hmin_eq] using hle
    simpa [finiteChainAdjacentThresholdRate,
      finiteChainOrderedPairThresholdRate] using hle'
  have hadj_dominates' :
      ∀ p : finiteChainOrderedPair n, ∃ i : finiteChainAdjacentIndex n,
        pairwiseSellerThresholdRate M sampleRate
            (finiteChainOrderedPairHi (finiteChainAdjacentPair i))
            (finiteChainOrderedPairLo (finiteChainAdjacentPair i)) ≤
          pairwiseSellerThresholdRate M sampleRate
            (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) := by
    intro p
    rcases (finiteChainAdjacentThresholdRatesDominate_of_interval
        hadj_dominates) p with ⟨i, hi⟩
    exact ⟨i, by
      simpa [finiteChainAdjacentThresholdRate,
        finiteChainOrderedPairThresholdRate] using hi⟩
  have hrate_eq :
      pairwiseSellerThresholdRate M sampleRate
          (finiteChainOrderedPairHi (finiteChainAdjacentPair iMin))
          (finiteChainOrderedPairLo (finiteChainAdjacentPair iMin)) =
        minFiniteChainAdjacentThresholdRate M sampleRate := by
    dsimp [adjRate] at hmin_eq
    simpa [finiteChainAdjacentThresholdRate,
      finiteChainOrderedPairThresholdRate] using hmin_eq.symm
  letI : Nonempty (finiteChainOrderedPair n) :=
    ⟨finiteChainAdjacentPair iMin⟩
  have hmain :=
    finiteFloorPkObjective_oneSub_hasExponentialRate_of_adjacent_leftTail_source_rates
      (Pair := finiteChainOrderedPair n)
      (Adj := finiteChainAdjacentIndex n)
      M sampleRate finiteChainOrderedPairHi finiteChainOrderedPairLo
      (uniformPairWeight (finiteChainOrderedPair n))
      finiteChainAdjacentPair
      (uniformPairWeight_nonneg (finiteChainOrderedPair n))
      (uniformPairWeight_sum_eq_one (finiteChainOrderedPair n))
      iMin
      (uniformPairWeight_pos
        (finiteChainOrderedPair n) (finiteChainAdjacentPair iMin))
      (fun p => by
        simpa [finiteChainOrderedPairThresholdRate] using hleftTail p)
      hadj_min hadj_dominates'
  simpa [finiteUniformFloorPkObjective, hrate_eq] using hmain

/--
Finite-chain endpoint with the exponent written as the finite minimum over
adjacent displayed pairwise objective rates.  The adjacent dominance is derived
from interval-local floor-count event bounds, so this theorem does not require
source threshold-rate identities or minimizers.
-/
theorem finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_interval_floor_leftTail_event_bounds_min_objective_rate
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
      (minFiniteChainAdjacentObjectiveRate M sampleRate a) := by
  classical
  let rate : finiteChainOrderedPair n → ℝ :=
    finiteChainOrderedPairObjectiveRate M sampleRate a
  have hcert :
      ∀ p : finiteChainOrderedPair n,
        ExponentialRateCertificate
          (fun k : ℕ =>
            twoSampleFloorScoreGapLeftTailProb M sampleRate
              (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) k)
          (rate p) := by
    intro p
    simpa [rate, finiteChainOrderedPairObjectiveRate] using
      twoSampleFloorScoreGapLeftTail_pairwiseObjective_exponentialRateCertificate_of_logMGF_derivative_minimizer_of_straddling_support
        M sampleRate (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p)
        (hpositive_sample (finiteChainOrderedPairHi p))
        (hpositive_sample (finiteChainOrderedPairLo p))
        (a p) (z p) (hz p) (hderiv_hi p) (hderiv_lo p)
        (hstraddle_hi p) (hstraddle_lo p)
  have hinterval_dom :
      ∀ p : finiteChainOrderedPair n, ∃ i : finiteChainAdjacentIndex n,
        (finiteChainOrderedPairLo p).val ≤ i.1.val ∧
          i.1.val < (finiteChainOrderedPairHi p).val ∧
            rate (finiteChainAdjacentPair i) ≤ rate p :=
    finiteChainIntervalAdjacentRatesDominate_of_floor_leftTail_event_bounds
      rate hcert hinterval_bound
  have hadj_dominates :
      ∀ p : finiteChainOrderedPair n, ∃ i : finiteChainAdjacentIndex n,
        rate (finiteChainAdjacentPair i) ≤ rate p := by
    intro p
    rcases hinterval_dom p with ⟨i, _hlo, _hhi, hrate⟩
    exact ⟨i, hrate⟩
  let adjRate : finiteChainAdjacentIndex n → ℝ :=
    finiteChainAdjacentObjectiveRate M sampleRate a
  obtain ⟨iMin, _hiMin, hmin_eq⟩ :=
    Finset.exists_mem_eq_inf'
      (s := (Finset.univ : Finset (finiteChainAdjacentIndex n)))
      (H := Finset.univ_nonempty) (f := adjRate)
  have hadj_min :
      ∀ i : finiteChainAdjacentIndex n,
        rate (finiteChainAdjacentPair iMin) ≤
          rate (finiteChainAdjacentPair i) := by
    intro i
    have hle :
        minFiniteChainAdjacentObjectiveRate M sampleRate a ≤
          finiteChainAdjacentObjectiveRate M sampleRate a i := by
      unfold minFiniteChainAdjacentObjectiveRate
      exact Finset.inf'_le
        (s := (Finset.univ : Finset (finiteChainAdjacentIndex n)))
        (f := finiteChainAdjacentObjectiveRate M sampleRate a)
        (by simp : i ∈ (Finset.univ : Finset (finiteChainAdjacentIndex n)))
    have hle' :
        finiteChainAdjacentObjectiveRate M sampleRate a iMin ≤
          finiteChainAdjacentObjectiveRate M sampleRate a i := by
      dsimp [adjRate] at hmin_eq
      rw [hmin_eq.symm]
      exact hle
    simpa [rate, finiteChainAdjacentObjectiveRate,
      finiteChainOrderedPairObjectiveRate] using hle'
  have hrate_eq :
      rate (finiteChainAdjacentPair iMin) =
        minFiniteChainAdjacentObjectiveRate M sampleRate a := by
    dsimp [adjRate] at hmin_eq
    simpa [rate, finiteChainAdjacentObjectiveRate,
      finiteChainOrderedPairObjectiveRate] using hmin_eq.symm
  letI : Nonempty (finiteChainOrderedPair n) := ⟨finiteChainAdjacentPair iMin⟩
  have hmain :=
    finiteFloorPkObjective_oneSub_hasExponentialRate_of_adjacent_leftTail_rates
      (Pair := finiteChainOrderedPair n)
      (Adj := finiteChainAdjacentIndex n)
      M sampleRate finiteChainOrderedPairHi finiteChainOrderedPairLo
      (uniformPairWeight (finiteChainOrderedPair n))
      finiteChainAdjacentPair
      (uniformPairWeight_nonneg (finiteChainOrderedPair n))
      (uniformPairWeight_sum_eq_one (finiteChainOrderedPair n))
      iMin
      (uniformPairWeight_pos
        (finiteChainOrderedPair n) (finiteChainAdjacentPair iMin))
      rate hcert hadj_min hadj_dominates
  simpa [finiteUniformFloorPkObjective, hrate_eq] using hmain

/--
Finite-chain Theorem 1 endpoint with the exponent written as the finite
minimum over adjacent threshold rates, deriving the adjacent threshold-rate
dominance from interval-local floor-count left-tail event bounds.
-/
theorem finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_interval_floor_leftTail_event_bounds_min_rate
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
      (minFiniteChainAdjacentThresholdRate M sampleRate) := by
  classical
  have hcert :
      ∀ p : finiteChainOrderedPair n,
        ExponentialRateCertificate
          (fun k : ℕ =>
            twoSampleFloorScoreGapLeftTailProb M sampleRate
              (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) k)
          (finiteChainOrderedPairThresholdRate M sampleRate p) := by
    intro p
    simpa [finiteChainOrderedPairThresholdRate] using
      twoSampleFloorScoreGapLeftTail_pairwiseThresholdRate_exponentialRateCertificate_of_logMGF_derivative_threshold_minimizer_of_straddling_support
        M sampleRate (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p)
        (hpositive_sample (finiteChainOrderedPairHi p))
        (hpositive_sample (finiteChainOrderedPairLo p))
        (a p) (z p) (hz p) (hderiv_hi p) (hderiv_lo p)
        (hthreshold_min p) (hstraddle_hi p) (hstraddle_lo p)
  exact
    finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_interval_adjacent_threshold_rate_dominance_min_rate
      M sampleRate hpositive_sample a z hz hderiv_hi hderiv_lo hthreshold_min
      hstraddle_hi hstraddle_lo
      (finiteChainIntervalAdjacentThresholdRatesDominate_of_floor_leftTail_event_bounds
        hcert hinterval_bound)

/--
Finite-chain Theorem 1 endpoint with the exponent written as the finite
minimum over adjacent threshold rates, deriving the adjacent threshold-rate
dominance from interval-local floor-count left-tail event bounds.  This
variant assumes exact source-threshold rate identities directly instead of
source-level minimizer predicates.
-/
theorem finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_interval_floor_leftTail_event_bounds_min_rate_of_threshold_eq
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
      (minFiniteChainAdjacentThresholdRate M sampleRate) := by
  classical
  have hcert :
      ∀ p : finiteChainOrderedPair n,
        ExponentialRateCertificate
          (fun k : ℕ =>
            twoSampleFloorScoreGapLeftTailProb M sampleRate
              (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p) k)
          (finiteChainOrderedPairThresholdRate M sampleRate p) := by
    intro p
    simpa [finiteChainOrderedPairThresholdRate] using
      twoSampleFloorScoreGapLeftTail_pairwiseThresholdRate_exponentialRateCertificate_of_logMGF_derivative_minimizer_of_straddling_support
        M sampleRate (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p)
        (hpositive_sample (finiteChainOrderedPairHi p))
        (hpositive_sample (finiteChainOrderedPairLo p))
        (a p) (z p) (hz p) (hderiv_hi p) (hderiv_lo p)
        (hthreshold_eq p) (hstraddle_hi p) (hstraddle_lo p)
  exact
    finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_interval_adjacent_threshold_rate_dominance_min_rate_of_leftTail_certificates
      M sampleRate hcert
      (finiteChainIntervalAdjacentThresholdRatesDominate_of_floor_leftTail_event_bounds
        hcert hinterval_bound)

/--
Finite-chain Theorem 1 endpoint from a joint finite score law whose
two-coordinate marginals agree with the paper's pairwise floor-count left-tail
probabilities. The adjacent-pair reduction is derived from deterministic
adjacent-inversion inclusion and finite union bounds.
-/
theorem finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_joint_score_marginals_min_rate
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
  finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_interval_floor_leftTail_event_bounds_min_rate
    M sampleRate hpositive_sample a z hz hderiv_hi hderiv_lo hthreshold_min
    hstraddle_hi hstraddle_lo
    (finiteChainIntervalFloorLeftTailEventBounds_of_joint_score_marginals
      M sampleRate μ score hmarginal)

/--
Finite-chain Theorem 1 endpoint from a joint finite score law whose
two-coordinate marginals agree with the paper's pairwise floor-count left-tail
probabilities, using exact source-threshold rate identities directly.
-/
theorem finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_joint_score_marginals_min_rate_of_threshold_eq
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
  finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_interval_floor_leftTail_event_bounds_min_rate_of_threshold_eq
    M sampleRate hpositive_sample a z hz hderiv_hi hderiv_lo hthreshold_eq
    hstraddle_hi hstraddle_lo
    (finiteChainIntervalFloorLeftTailEventBounds_of_joint_score_marginals
      M sampleRate μ score hmarginal)

/--
Finite-chain Theorem 1 endpoint from a joint finite score law, with the
exponent written as the finite minimum over adjacent displayed pairwise
objective rates.  This avoids source-threshold `sInf` identification and uses
the joint-law adjacent-inversion reduction directly.
-/
theorem finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_joint_score_marginals_min_objective_rate
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
      (minFiniteChainAdjacentObjectiveRate M sampleRate a) :=
  finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_interval_floor_leftTail_event_bounds_min_objective_rate
    M sampleRate hpositive_sample a z hz hderiv_hi hderiv_lo
    hstraddle_hi hstraddle_lo
    (finiteChainIntervalFloorLeftTailEventBounds_of_joint_score_marginals
      M sampleRate μ score hmarginal)

/--
Finite-chain Theorem 1 endpoint specialized to the concrete independent joint
floor-rating law over all seller samples.  The remaining marginal hypothesis is
the statement that the two-coordinate projection of this joint law agrees with
the pairwise floor-count left-tail law.
-/
theorem finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_joint_floor_rating_marginals_min_rate
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
  finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_joint_score_marginals_min_rate
    (Ω := fun k : ℕ => finiteChainJointFloorRatingSample Rating sampleRate k)
    M sampleRate hpositive_sample a z hz hderiv_hi hderiv_lo hthreshold_min
    hstraddle_hi hstraddle_lo
    (fun k : ℕ => finiteChainJointFloorRatingLaw M sampleRate k)
    (fun k sample θ => finiteChainJointFloorAverageScore M sampleRate k sample θ)
    hmarginal

/--
Finite-chain Theorem 1 endpoint specialized to the concrete independent joint
floor-rating law over all seller samples, using exact source-threshold rate
identities directly.  The remaining marginal hypothesis states that the
two-coordinate projection of the joint law agrees with the pairwise floor-count
left-tail law.
-/
theorem finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_joint_floor_rating_marginals_min_rate_of_threshold_eq
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
  finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_joint_score_marginals_min_rate_of_threshold_eq
    (Ω := fun k : ℕ => finiteChainJointFloorRatingSample Rating sampleRate k)
    M sampleRate hpositive_sample a z hz hderiv_hi hderiv_lo hthreshold_eq
    hstraddle_hi hstraddle_lo
    (fun k : ℕ => finiteChainJointFloorRatingLaw M sampleRate k)
    (fun k sample θ => finiteChainJointFloorAverageScore M sampleRate k sample θ)
    hmarginal

/--
Finite-chain Theorem 1 endpoint specialized to the concrete independent joint
floor-rating law, with the exponent written as the finite minimum over adjacent
displayed pairwise objective rates.
-/
theorem finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_joint_floor_rating_marginals_min_objective_rate
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
      (minFiniteChainAdjacentObjectiveRate M sampleRate a) :=
  finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_joint_score_marginals_min_objective_rate
    (Ω := fun k : ℕ => finiteChainJointFloorRatingSample Rating sampleRate k)
    M sampleRate hpositive_sample a z hz hderiv_hi hderiv_lo
    hstraddle_hi hstraddle_lo
    (fun k : ℕ => finiteChainJointFloorRatingLaw M sampleRate k)
    (fun k sample θ => finiteChainJointFloorAverageScore M sampleRate k sample θ)
    hmarginal

/--
Finite-chain Theorem 1 endpoint for the concrete independent joint floor-rating
law.  The adjacent-pair reduction is derived internally from the joint law's
two-coordinate marginals and the deterministic adjacent-inversion inclusion.
-/
theorem finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_joint_floor_rating_law_min_rate
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
  finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_joint_floor_rating_marginals_min_rate
    M sampleRate hpositive_sample a z hz hderiv_hi hderiv_lo hthreshold_min
    hstraddle_hi hstraddle_lo
    (twoSampleFloorScoreGapLeftTailProb_eq_joint_floor_rating_prob
      M sampleRate)

/--
Finite-chain Theorem 1 endpoint for the concrete independent joint floor-rating
law from per-pair source-threshold rate identities. This is the same joint-law
adjacent reduction as
`finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_joint_floor_rating_law_min_rate`,
but callers provide the exact source-rate identity directly instead of the
stronger source-level minimizer predicate.
-/
theorem finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_joint_floor_rating_law_min_rate_of_threshold_eq
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
  finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_joint_floor_rating_marginals_min_rate_of_threshold_eq
    M sampleRate hpositive_sample a z hz hderiv_hi hderiv_lo hthreshold_eq
    hstraddle_hi hstraddle_lo
    (twoSampleFloorScoreGapLeftTailProb_eq_joint_floor_rating_prob
      M sampleRate)

/--
Finite-chain Theorem 1 endpoint for the concrete independent joint floor-rating
law, with the exponent written as the finite minimum over adjacent displayed
pairwise objective rates.
-/
theorem finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_joint_floor_rating_law_min_objective_rate
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
      (minFiniteChainAdjacentObjectiveRate M sampleRate a) :=
  finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_joint_floor_rating_marginals_min_objective_rate
    M sampleRate hpositive_sample a z hz hderiv_hi hderiv_lo
    hstraddle_hi hstraddle_lo
    (twoSampleFloorScoreGapLeftTailProb_eq_joint_floor_rating_prob
      M sampleRate)

/--
Finite-chain Theorem 1 endpoint for the concrete independent joint floor-rating
law at the displayed adjacent-objective minimum.  Common-dual derivative data
provides the per-pair objective rates, and common bottom/top support supplies
the finite two-sided support needed for the Cramer lower bound.
-/
theorem finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_joint_floor_rating_law_min_objective_rate_of_score_bounds
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
  finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_joint_floor_rating_law_min_objective_rate
    M sampleRate hpositive_sample a z hz hderiv_hi hderiv_lo
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

/--
Source-facing extended-rate Theorem 1 endpoint for the concrete independent
joint floor-rating law.  The finite objective rate is promoted to the
support-safe extended adjacent source threshold-rate minimum.
-/
theorem finiteChainUniformFloorPkObjective_oneSub_hasExtendedExponentialRate_of_joint_floor_rating_law_min_threshold_rate_top_of_score_bounds
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
      (minFiniteChainAdjacentThresholdRateTop M sampleRate) := by
  have hfinite :
      HasExponentialRate
        (fun k : ℕ =>
          1 - finiteUniformFloorPkObjective M sampleRate
            finiteChainOrderedPairHi finiteChainOrderedPairLo k)
        (minFiniteChainAdjacentObjectiveRate M sampleRate a) :=
    finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_joint_floor_rating_law_min_objective_rate_of_score_bounds
      M sampleRate hpositive_sample a z hz hderiv_hi hderiv_lo
      rLow rHigh hmass_low hmass_high hscore_low_le hscore_le_high hscore_lt
  have htop :
      minFiniteChainAdjacentThresholdRateTop M sampleRate =
        (minFiniteChainAdjacentObjectiveRate M sampleRate a : WithTop ℝ) :=
    minFiniteChainAdjacentThresholdRateTop_eq_coe_minFiniteChainAdjacentObjectiveRate_of_common_logMGF_derivatives
      M sampleRate hpositive_sample a z hderiv_hi hderiv_lo
  rw [htop]
  exact HasExtendedExponentialRate.finite hfinite

/--
Real-rate source theorem from the support-safe extended-rate endpoint, once
the finite-support domain convention is reconciled with the paper's real
adjacent threshold-rate minimum.
-/
theorem finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_joint_floor_rating_law_min_threshold_rate_of_score_bounds_of_extended_min_eq
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
      (minFiniteChainAdjacentThresholdRate M sampleRate) := by
  have htop :
      HasExtendedExponentialRate
        (fun k : ℕ =>
          1 - finiteUniformFloorPkObjective M sampleRate
            finiteChainOrderedPairHi finiteChainOrderedPairLo k)
        (minFiniteChainAdjacentThresholdRateTop M sampleRate) :=
    finiteChainUniformFloorPkObjective_oneSub_hasExtendedExponentialRate_of_joint_floor_rating_law_min_threshold_rate_top_of_score_bounds
      M sampleRate hpositive_sample a z hz hderiv_hi hderiv_lo
      rLow rHigh hmass_low hmass_high hscore_low_le hscore_le_high hscore_lt
  rw [hextended_min_eq] at htop
  exact HasExtendedExponentialRate.to_finite htop

/--
Finite-chain Theorem 1 endpoint from a named pairwise threshold-rate
regularity package.  This is the compact proof-facing form of the current
source boundary: the concrete joint floor-rating law and adjacent aggregation
are internal, while the pairwise threshold-rate regularity remains explicit.
-/
theorem finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_joint_floor_rating_law_min_rate_of_pairwise_threshold_rate_regularity
    {n : ℕ} {Rating : Type*} [Fintype Rating] [DecidableEq Rating]
    [DecidableEq (finiteChainOrderedPair n)]
    [Nonempty (finiteChainAdjacentIndex n)]
    (M : FiniteRatingLDPModel (Fin n) Rating) (sampleRate : Fin n → ℝ)
    (hpositive_sample : ∀ θ : Fin n, 0 < sampleRate θ)
    (C :
      PairwiseThresholdRateRegularity M sampleRate
        finiteChainOrderedPairHi finiteChainOrderedPairLo) :
    HasExponentialRate
      (fun k : ℕ =>
        1 - finiteUniformFloorPkObjective M sampleRate
          finiteChainOrderedPairHi finiteChainOrderedPairLo k)
      (minFiniteChainAdjacentThresholdRate M sampleRate) :=
  finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_joint_floor_rating_law_min_rate_of_threshold_eq
    M sampleRate hpositive_sample C.threshold C.dual C.dual_nonpos
    C.deriv_hi C.deriv_lo C.threshold_rate_eq C.straddles_hi C.straddles_lo

/--
Finite-chain Theorem 1 endpoint for the concrete independent joint floor-rating
law from per-pair common-dual log-MGF derivatives and compact two-sided support.
The exact source-threshold rate identities are derived internally by Fenchel
optimality under the current real-valued finite-rate boundedness side condition.
-/
theorem finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_joint_floor_rating_law_min_rate_of_logMGF_derivatives
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
  finiteChainUniformFloorPkObjective_oneSub_hasExponentialRate_of_joint_floor_rating_law_min_rate_of_threshold_eq
    M sampleRate hpositive_sample a z hz hderiv_hi hderiv_lo
    (fun p =>
      pairwiseSellerThresholdRate_eq_of_common_logMGF_derivatives
        M sampleRate
        (finiteChainOrderedPairHi p) (finiteChainOrderedPairLo p)
        (hpositive_sample (finiteChainOrderedPairHi p))
        (hpositive_sample (finiteChainOrderedPairLo p))
        (hbdd_hi p) (hbdd_lo p) (a p) (z p)
        (hderiv_hi p) (hderiv_lo p))
    hstraddle_hi hstraddle_lo

/--
Source-shaped finite Theorem 1 endpoint for arbitrary real floor-count sample
rates from per-pair common-dual log-MGF derivatives and compact two-sided
support at each threshold. This is the most compact weighted/adjacent theorem
surface currently available for the paper-shaped `W_k` objective.
-/
theorem finiteFloorPkObjective_oneSub_hasExponentialRate_of_adjacent_logMGF_derivatives_of_straddling_support
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
  finiteFloorPkObjective_oneSub_hasExponentialRate_of_adjacent_leftTail_source_rates
    M sampleRate pairHi pairLo weight adjacentPair
    hweight_nonneg hweight_sum iMin hweight_pos
    (fun p =>
      twoSampleFloorScoreGapLeftTail_pairwiseThresholdRate_exponentialRateCertificate_of_logMGF_derivatives_of_straddling_support
        M sampleRate (pairHi p) (pairLo p)
        (hgHi p) (hgLo p) (hbdd_hi p) (hbdd_lo p) (a p) (z p) (hz p)
        (hderiv_hi p) (hderiv_lo p)
        (hstraddle_hi p) (hstraddle_lo p))
    hadj_min hadj_dominates

/--
All-pairs-minimum version of the arbitrary-real floor-count endpoint with
proof-technical boundedness and shifted mean signs derived internally.
-/
theorem finiteFloorPkObjective_oneSub_hasExponentialRate_of_min_logMGF_derivative_minimizers_of_pos_neg_atoms
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
  finiteFloorPkObjective_oneSub_hasExponentialRate_of_adjacent_logMGF_derivative_minimizers_of_pos_neg_atoms
    (Pair := Pair) (Adj := Pair)
    M sampleRate pairHi pairLo weight (fun p : Pair => p)
    hweight_nonneg hweight_sum pMin hweight_pos hgHi hgLo
    a z hz hderiv_hi hderiv_lo hthreshold_eq
    hiPos hiNeg loPos loNeg
    hmass_hi_pos hscore_hi_pos hmass_hi_neg hscore_hi_neg
    hmass_lo_pos hscore_lo_pos hmass_lo_neg hscore_lo_neg
    hmin (fun p => ⟨p, le_rfl⟩)

/--
Uniform-pair version of the all-pairs floor-count endpoint. This is the finite
`W_k` specialization used by the paper when `Pair` enumerates the ordered
comparison pairs.
-/
theorem finiteUniformFloorPkObjective_oneSub_hasExponentialRate_of_min_logMGF_derivative_minimizers_of_pos_neg_atoms
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
        (pairHi pMin) (pairLo pMin)) := by
  simpa [finiteUniformFloorPkObjective] using
    finiteFloorPkObjective_oneSub_hasExponentialRate_of_min_logMGF_derivative_minimizers_of_pos_neg_atoms
      (Pair := Pair)
      M sampleRate pairHi pairLo (uniformPairWeight Pair)
      (uniformPairWeight_nonneg Pair)
      (uniformPairWeight_sum_eq_one Pair)
      pMin (uniformPairWeight_pos Pair pMin)
      hgHi hgLo a z hz hderiv_hi hderiv_lo hthreshold_eq
      hiPos hiNeg loPos loNeg
      hmass_hi_pos hscore_hi_pos hmass_hi_neg hscore_hi_neg
      hmass_lo_pos hscore_lo_pos hmass_lo_neg hscore_lo_neg
      hmin

/--
Uniform-pair floor-count endpoint with the rate written as the finite minimum
over all comparison pairs. The minimizing pair is selected internally from
finite nonemptiness of `Pair`.
-/
theorem finiteUniformFloorPkObjective_oneSub_hasExponentialRate_of_logMGF_derivative_minimizers_of_pos_neg_atoms
    {Seller Rating Pair : Type*} [Fintype Rating] [DecidableEq Rating]
    [Fintype Pair] [DecidableEq Pair] [Nonempty Pair]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
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
      ∀ p : Pair, a p - M.score (loNeg p) < 0) :
    HasExponentialRate
      (fun k : ℕ =>
        1 - finiteUniformFloorPkObjective M sampleRate pairHi pairLo k)
      (minPairwiseSellerThresholdRate M sampleRate pairHi pairLo) := by
  classical
  let pairRate : Pair → ℝ :=
    fun p : Pair =>
      pairwiseSellerThresholdRate M sampleRate (pairHi p) (pairLo p)
  obtain ⟨pMin, _hpMin, hmin_eq⟩ :=
    Finset.exists_mem_eq_inf'
      (s := (Finset.univ : Finset Pair))
      (H := Finset.univ_nonempty) (f := pairRate)
  have hmin :
      ∀ p : Pair,
        pairwiseSellerThresholdRate M sampleRate (pairHi pMin) (pairLo pMin) ≤
          pairwiseSellerThresholdRate M sampleRate (pairHi p) (pairLo p) := by
    intro p
    have hp :
        minPairwiseSellerThresholdRate M sampleRate pairHi pairLo ≤
          pairwiseSellerThresholdRate M sampleRate (pairHi p) (pairLo p) := by
      unfold minPairwiseSellerThresholdRate
      exact Finset.inf'_le
        (s := (Finset.univ : Finset Pair))
        (f := fun p : Pair =>
          pairwiseSellerThresholdRate M sampleRate (pairHi p) (pairLo p))
        (by simp : p ∈ (Finset.univ : Finset Pair))
    dsimp [pairRate] at hmin_eq
    rw [hmin_eq.symm]
    exact hp
  have hrate_eq :
      pairwiseSellerThresholdRate M sampleRate (pairHi pMin) (pairLo pMin) =
        minPairwiseSellerThresholdRate M sampleRate pairHi pairLo := by
    dsimp [pairRate] at hmin_eq
    exact hmin_eq.symm
  have hmain :=
    finiteUniformFloorPkObjective_oneSub_hasExponentialRate_of_min_logMGF_derivative_minimizers_of_pos_neg_atoms
      M sampleRate pairHi pairLo pMin hgHi hgLo
      a z hz hderiv_hi hderiv_lo hthreshold_eq
      hiPos hiNeg loPos loNeg
      hmass_hi_pos hscore_hi_pos hmass_hi_neg hscore_hi_neg
      hmass_lo_pos hscore_lo_pos hmass_lo_neg hscore_lo_neg
      hmin
  simpa [hrate_eq] using hmain

/--
Uniform-pair floor-count endpoint using the compact straddling-support
predicate for each pairwise threshold. The exponent is the finite minimum over
all comparison-pair threshold rates.
-/
theorem finiteUniformFloorPkObjective_oneSub_hasExponentialRate_of_logMGF_derivative_minimizers_of_straddling_support
    {Seller Rating Pair : Type*} [Fintype Rating] [DecidableEq Rating]
    [Fintype Pair] [DecidableEq Pair] [Nonempty Pair]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
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
    (hstraddle_hi :
      ∀ p : Pair, ratingLawStraddlesThreshold M (pairHi p) (a p))
    (hstraddle_lo :
      ∀ p : Pair, ratingLawStraddlesThreshold M (pairLo p) (a p)) :
    HasExponentialRate
      (fun k : ℕ =>
        1 - finiteUniformFloorPkObjective M sampleRate pairHi pairLo k)
      (minPairwiseSellerThresholdRate M sampleRate pairHi pairLo) := by
  classical
  let pairRate : Pair → ℝ :=
    fun p : Pair =>
      pairwiseSellerThresholdRate M sampleRate (pairHi p) (pairLo p)
  obtain ⟨pMin, _hpMin, hmin_eq⟩ :=
    Finset.exists_mem_eq_inf'
      (s := (Finset.univ : Finset Pair))
      (H := Finset.univ_nonempty) (f := pairRate)
  have hmin :
      ∀ p : Pair,
        pairwiseSellerThresholdRate M sampleRate (pairHi pMin) (pairLo pMin) ≤
          pairwiseSellerThresholdRate M sampleRate (pairHi p) (pairLo p) := by
    intro p
    have hp :
        minPairwiseSellerThresholdRate M sampleRate pairHi pairLo ≤
          pairwiseSellerThresholdRate M sampleRate (pairHi p) (pairLo p) := by
      unfold minPairwiseSellerThresholdRate
      exact Finset.inf'_le
        (s := (Finset.univ : Finset Pair))
        (f := fun p : Pair =>
          pairwiseSellerThresholdRate M sampleRate (pairHi p) (pairLo p))
        (by simp : p ∈ (Finset.univ : Finset Pair))
    dsimp [pairRate] at hmin_eq
    rw [hmin_eq.symm]
    exact hp
  have hrate_eq :
      pairwiseSellerThresholdRate M sampleRate (pairHi pMin) (pairLo pMin) =
        minPairwiseSellerThresholdRate M sampleRate pairHi pairLo := by
    dsimp [pairRate] at hmin_eq
    exact hmin_eq.symm
  have hleftTail :
      ∀ p : Pair,
        ExponentialRateCertificate
          (twoSampleFloorScoreGapLeftTailProb M sampleRate
            (pairHi p) (pairLo p))
          (pairwiseSellerThresholdRate M sampleRate (pairHi p) (pairLo p)) :=
    fun p =>
      twoSampleFloorScoreGapLeftTail_pairwiseThresholdRate_exponentialRateCertificate_of_logMGF_derivative_minimizer_of_straddling_support
        M sampleRate (pairHi p) (pairLo p)
        (hgHi p) (hgLo p) (a p) (z p) (hz p)
        (hderiv_hi p) (hderiv_lo p) (hthreshold_eq p)
        (hstraddle_hi p) (hstraddle_lo p)
  have hmain :=
    finiteFloorPkObjective_oneSub_hasExponentialRate_of_adjacent_leftTail_source_rates
      (Pair := Pair) (Adj := Pair)
      M sampleRate pairHi pairLo (uniformPairWeight Pair) (fun p : Pair => p)
      (uniformPairWeight_nonneg Pair) (uniformPairWeight_sum_eq_one Pair)
      pMin (uniformPairWeight_pos Pair pMin)
      hleftTail hmin (fun p => ⟨p, le_rfl⟩)
  simpa [finiteUniformFloorPkObjective, hrate_eq] using hmain

/--
Uniform-pair floor-count endpoint from per-pair log-MGF derivative data and
explicit threshold minimizers. The finite comparison-family minimum is selected
internally; each pair only supplies the source-level fact that its displayed
threshold minimizes the pairwise rate objective.
-/
theorem finiteUniformFloorPkObjective_oneSub_hasExponentialRate_of_logMGF_derivative_threshold_minimizers_of_straddling_support
    {Seller Rating Pair : Type*} [Fintype Rating] [DecidableEq Rating]
    [Fintype Pair] [DecidableEq Pair] [Nonempty Pair]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
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
      ∀ p : Pair, ratingLawStraddlesThreshold M (pairLo p) (a p)) :
    HasExponentialRate
      (fun k : ℕ =>
        1 - finiteUniformFloorPkObjective M sampleRate pairHi pairLo k)
      (minPairwiseSellerThresholdRate M sampleRate pairHi pairLo) :=
  finiteUniformFloorPkObjective_oneSub_hasExponentialRate_of_logMGF_derivative_minimizers_of_straddling_support
    M sampleRate pairHi pairLo hgHi hgLo a z hz hderiv_hi hderiv_lo
    (fun p =>
      pairwiseSellerThresholdRate_eq_of_pairwiseRateObjective_minimizer
        M sampleRate (pairHi p) (pairLo p) (a p) (hthreshold_min p))
    hstraddle_hi hstraddle_lo

/--
Uniform-pair floor-count endpoint from a named pairwise regularity package.
This is the compact proof-facing boundary for the source's pairwise
threshold-rate step.
-/
theorem finiteUniformFloorPkObjective_oneSub_hasExponentialRate_of_pairwise_threshold_rate_regularity
    {Seller Rating Pair : Type*} [Fintype Rating] [DecidableEq Rating]
    [Fintype Pair] [DecidableEq Pair] [Nonempty Pair]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
    (hgHi : ∀ p : Pair, 0 < sampleRate (pairHi p))
    (hgLo : ∀ p : Pair, 0 < sampleRate (pairLo p))
    (C : PairwiseThresholdRateRegularity M sampleRate pairHi pairLo) :
    HasExponentialRate
      (fun k : ℕ =>
        1 - finiteUniformFloorPkObjective M sampleRate pairHi pairLo k)
      (minPairwiseSellerThresholdRate M sampleRate pairHi pairLo) :=
  finiteUniformFloorPkObjective_oneSub_hasExponentialRate_of_logMGF_derivative_minimizers_of_straddling_support
    M sampleRate pairHi pairLo hgHi hgLo C.threshold C.dual C.dual_nonpos
    C.deriv_hi C.deriv_lo C.threshold_rate_eq C.straddles_hi C.straddles_lo

/--
Uniform-pair floor-count endpoint from per-pair common-dual log-MGF
derivative data and compact two-sided support. The finite comparison-family
minimum is selected internally, and the per-pair source threshold minimizers
are proved by Fenchel optimality under the current bounded-rate API side
condition.
-/
theorem finiteUniformFloorPkObjective_oneSub_hasExponentialRate_of_logMGF_derivatives_of_straddling_support
    {Seller Rating Pair : Type*} [Fintype Rating] [DecidableEq Rating]
    [Fintype Pair] [DecidableEq Pair] [Nonempty Pair]
    (M : FiniteRatingLDPModel Seller Rating) (sampleRate : Seller → ℝ)
    (pairHi pairLo : Pair → Seller)
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
      ∀ p : Pair, ratingLawStraddlesThreshold M (pairLo p) (a p)) :
    HasExponentialRate
      (fun k : ℕ =>
        1 - finiteUniformFloorPkObjective M sampleRate pairHi pairLo k)
      (minPairwiseSellerThresholdRate M sampleRate pairHi pairLo) :=
  finiteUniformFloorPkObjective_oneSub_hasExponentialRate_of_logMGF_derivative_minimizers_of_straddling_support
    M sampleRate pairHi pairLo hgHi hgLo a z hz hderiv_hi hderiv_lo
    (fun p =>
      pairwiseSellerThresholdRate_eq_of_common_logMGF_derivatives
        M sampleRate (pairHi p) (pairLo p) (hgHi p) (hgLo p)
        (hbdd_hi p) (hbdd_lo p) (a p) (z p)
        (hderiv_hi p) (hderiv_lo p))
    hstraddle_hi hstraddle_lo

/--
Finite Theorem 1 bridge directly from the per-pair log-MGF derivative data.
This packages Appendix Lemma `problessthan`, Lemma `Pk_LD`, and the finite
adjacent-pair aggregation step into one source-facing endpoint for the
integer-rate finite model.
-/
theorem finiteRankingPkComplementError_hasExponentialRate_of_adjacent_logMGF_derivatives
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
        (pairHi (adjacentPair iMin)) (pairLo (adjacentPair iMin))) := by
  refine
    finiteRankingPkComplementError_hasExponentialRate_of_adjacent_min_source_rates
      M sampleRate pairHi pairLo gHi gLo weight adjacentPair
      hweight_nonneg iMin hweight_pos ?_ hadj_min hadj_dominates
  intro p
  exact
    twoSamplePkComplementError_pairwiseThresholdRate_exponentialRateCertificate_of_logMGF_derivatives
      M sampleRate (pairHi p) (pairLo p) (gHi p) (gLo p)
      (hgHi p) (hgLo p) (hsample_hi p) (hsample_lo p)
      (hbdd_hi p) (hbdd_lo p) (a p) (z p)
      (hderiv_hi p) (hderiv_lo p) (hmean p)
      (hmassPos p) (hscorePos p) (hmassNeg p) (hscoreNeg p)

/--
Literal integer-rate finite Theorem 1 endpoint from per-pair log-MGF
derivative data: the paper-style objective satisfies
`-log(1 - W_n) / n -> min adjacent source rate`.
-/
theorem finiteIntegerRatePkObjective_oneSub_hasExponentialRate_of_adjacent_logMGF_derivatives
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
        (pairHi (adjacentPair iMin)) (pairLo (adjacentPair iMin))) := by
  have hcomp :
      HasExponentialRate
        (finiteIntegerRatePkComplementError M pairHi pairLo gHi gLo weight)
        (pairwiseSellerThresholdRate M sampleRate
          (pairHi (adjacentPair iMin)) (pairLo (adjacentPair iMin))) := by
    simpa [finiteIntegerRatePkComplementError] using
      finiteRankingPkComplementError_hasExponentialRate_of_adjacent_logMGF_derivatives
        M sampleRate pairHi pairLo gHi gLo weight adjacentPair
        hweight_nonneg iMin hweight_pos hgHi hgLo hsample_hi hsample_lo
        hbdd_hi hbdd_lo a z hderiv_hi hderiv_lo hmean samplePos sampleNeg
        hmassPos hscorePos hmassNeg hscoreNeg hadj_min hadj_dominates
  refine Filter.Tendsto.congr' ?_ hcomp
  filter_upwards with n
  rw [logDecay]
  rw [logDecay]
  rw [← finiteIntegerRatePkComplementError_eq_one_sub_objective
    M pairHi pairLo gHi gLo weight hweight_sum n]

/--
Source floor-count Theorem 1 endpoint for natural-valued match rates.  In this
case `floor(k g(theta)) = k g(theta)`, so the completed integer-rate
log-MGF-derivative proof transfers to the paper's floor-count objective.
-/
theorem finiteFloorPkObjective_oneSub_hasExponentialRate_of_nat_sampleRates_adjacent_logMGF_derivatives
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
        (pairHi (adjacentPair iMin)) (pairLo (adjacentPair iMin))) := by
  have hinteger :
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
  refine Filter.Tendsto.congr' ?_ hinteger
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  rw [logDecay]
  rw [logDecay]
  rw [finiteFloorPkObjective_eq_integerRatePkObjective_of_nat_sampleRates
    M sampleRate pairHi pairLo gHi gLo weight hsample_hi hsample_lo
    hgHi hgLo n hn]

end

end GJ18InformativeRatingSystems

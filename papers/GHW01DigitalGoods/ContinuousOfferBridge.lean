import GHW01DigitalGoods.AuctionMainTheorems
import AppliedModelingLib.Foundations.Probability.RealDistribution

open MeasureTheory
open Set
open AppliedModelingLib.Auction
open AppliedModelingLib.Probability

namespace GHW01DigitalGoods

/-! A probability-measure bridge for Theorem 8.2.  The finite `PMF` endpoint
is retained; this theorem isolates the source's continuous-outcome extension
as an ordinary integral monotonicity argument, with integrability exposed
explicitly rather than hidden in a finite-support carrier. -/

noncomputable def paper_theorem8_2_journal_monotone_measure_expected_revenue
    {Agent Outcome : Type*} [Fintype Agent] [Nonempty Agent]
    [DecidableEq Agent] [MeasurableSpace Outcome]
    (μ : Measure Outcome) (values : Agent → ℝ)
    (offerPrice : Outcome → Agent → ℝ) : ℝ :=
  ∫ outcome, paper_theorem8_2_journal_monotone_offer_revenue values
      (offerPrice outcome) ∂μ

/-! The marginal-law bridge below separates two facts in the journal argument:
a common outcome law gives an accepted-offer monotone coupling, while each
bidder's offer marginal gives the one-dimensional revenue integral.  The
source-model construction from CDFs appears below this reusable bridge. -/

noncomputable def paper_theorem8_2_continuous_marginal_expected_revenue
    {Agent : Type*} [Fintype Agent]
    (values : Agent → ℝ) (offerLaw : Agent → Measure ℝ) : ℝ :=
  ∑ i : Agent, ∫ p, if p ≤ values i then p else 0 ∂offerLaw i

structure PaperTheorem82ContinuousMarginalCoupling
    (Agent Outcome : Type*) [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    [MeasurableSpace Outcome] where
  values : Agent → ℝ
  offerLaw : Agent → Measure ℝ
  law : Measure Outcome
  law_isProbability : IsProbabilityMeasure law
  offer : Outcome → Agent → ℝ
  offer_aemeasurable : ∀ i, AEMeasurable (fun outcome => offer outcome i) law
  marginal : ∀ i, Measure.map (fun outcome => offer outcome i) law = offerLaw i
  offer_nonneg : ∀ᵐ outcome ∂law, ∀ i, 0 ≤ offer outcome i
  offer_accept_monotone : ∀ᵐ outcome ∂law, ∀ i j, values i ≤ values j →
    offer outcome i ≤ values i → offer outcome j ≤ offer outcome i
  marginal_integrable : ∀ i,
    Integrable (fun p : ℝ => if p ≤ values i then p else 0) (offerLaw i)
  coupled_integrable : Integrable
    (fun outcome => paper_theorem8_2_journal_monotone_offer_revenue values
      (offer outcome)) law

theorem paper_theorem8_2_continuous_marginal_expected_revenue_eq_coupled
    {Agent Outcome : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    [MeasurableSpace Outcome]
    (model : PaperTheorem82ContinuousMarginalCoupling Agent Outcome) :
    paper_theorem8_2_continuous_marginal_expected_revenue
        model.values model.offerLaw =
      paper_theorem8_2_journal_monotone_measure_expected_revenue
        model.law model.values model.offer := by
  classical
  unfold paper_theorem8_2_continuous_marginal_expected_revenue
    paper_theorem8_2_journal_monotone_measure_expected_revenue
  change (∑ i : Agent, ∫ p, if p ≤ model.values i then p else 0 ∂model.offerLaw i) =
    ∫ outcome, ∑ i : Agent,
      (if (model.offer outcome i) ≤ model.values i then model.offer outcome i else 0)
        ∂model.law
  rw [MeasureTheory.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i _hi
    have hfun_meas : Measurable (fun p : ℝ => if p ≤ model.values i then p else 0) := by
      exact (measurable_id.ite measurableSet_Iic measurable_const)
    have hmap :
        (∫ p, (if p ≤ model.values i then p else 0)
          ∂Measure.map (fun outcome => model.offer outcome i) model.law) =
          ∫ outcome, (if model.offer outcome i ≤ model.values i then
            model.offer outcome i else 0) ∂model.law := by
      exact MeasureTheory.integral_map
        (model.offer_aemeasurable i)
        (by rw [model.marginal i]
            exact hfun_meas.aestronglyMeasurable)
    rw [← model.marginal i, hmap]
  · intro i _hi
    have hfun_meas : Measurable (fun p : ℝ => if p ≤ model.values i then p else 0) := by
      exact (measurable_id.ite measurableSet_Iic measurable_const)
    have hmapped : Integrable
        (fun p : ℝ => if p ≤ model.values i then p else 0)
        (Measure.map (fun outcome => model.offer outcome i) model.law) := by
      rw [model.marginal i]
      exact model.marginal_integrable i
    have hmap_int := (MeasureTheory.integrable_map_measure
      hfun_meas.aestronglyMeasurable
      (model.offer_aemeasurable i)).mp hmapped
    simpa [Function.comp_def] using hmap_int

/-- Journal-version continuous source model for Theorem 8.2.  This states
Definition 8.1 directly for arbitrary real offer laws: below a lower bid,
that bidder's offer CDF is at most each higher bidder's offer CDF. -/
structure PaperTheorem82ContinuousRawCDFMonotoneOfferSourceModel
    (Agent : Type*) [Fintype Agent] [Nonempty Agent] [DecidableEq Agent] where
  values : Agent → ℝ
  offerLaw : Agent → Measure ℝ
  offerLaw_isProbability : ∀ i, IsProbabilityMeasure (offerLaw i)
  value_nonneg : ∀ i, 0 ≤ values i
  offer_nonneg : ∀ i, offerLaw i (Iio 0) = 0
  cdf_monotone : ∀ i j, values i ≤ values j → ∀ t, t ≤ values i →
    ProbabilityTheory.cdf (offerLaw i) t ≤ ProbabilityTheory.cdf (offerLaw j) t

/-- The common-uniform coupling constructed in the journal proof from the
raw marginal CDFs.  Uniform's two endpoints are null, so the offer regularity
facts are recorded almost everywhere under the resulting uniform law. -/
noncomputable def paper_theorem8_2_continuous_marginal_coupling_of_raw_cdf_monotone_offer_source_model
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (model : PaperTheorem82ContinuousRawCDFMonotoneOfferSourceModel Agent) :
    PaperTheorem82ContinuousMarginalCoupling Agent ℝ where
  values := model.values
  offerLaw := model.offerLaw
  law := volume.restrict (Ioo (0 : ℝ) 1)
  law_isProbability := by
    constructor
    rw [Measure.restrict_apply' measurableSet_Ioo]
    simp only [univ_inter, Real.volume_Ioo]
    norm_num
  offer := fun u i => cdfQuantile (model.offerLaw i) u
  offer_aemeasurable := by
    intro i
    letI : IsProbabilityMeasure (model.offerLaw i) := model.offerLaw_isProbability i
    exact aemeasurable_cdfQuantile_volume_restrict_Ioo (model.offerLaw i)
  marginal := by
    intro i
    letI : IsProbabilityMeasure (model.offerLaw i) := model.offerLaw_isProbability i
    exact map_cdfQuantile_volume_restrict_Ioo (model.offerLaw i)
  offer_nonneg := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    intro i
    letI : IsProbabilityMeasure (model.offerLaw i) := model.offerLaw_isProbability i
    exact cdfQuantile_nonneg_of_measure_Iio_eq_zero
      (model.offerLaw i) hu (model.offer_nonneg i)
  offer_accept_monotone := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    intro i j hvalue haccept
    letI : IsProbabilityMeasure (model.offerLaw i) := model.offerLaw_isProbability i
    letI : IsProbabilityMeasure (model.offerLaw j) := model.offerLaw_isProbability j
    exact cdfQuantile_le_of_cdf_le_on
      (model.offerLaw i) (model.offerLaw j) hu haccept
      (model.cdf_monotone i j hvalue)
  marginal_integrable := by
    intro i
    letI : IsProbabilityMeasure (model.offerLaw i) := model.offerLaw_isProbability i
    exact integrable_if_le_id_of_ae_nonneg
      (model.offerLaw i) (model.values i)
      (ae_nonneg_of_measure_Iio_eq_zero (model.offerLaw i) (model.offer_nonneg i))
  coupled_integrable := by
    apply integrable_finset_sum (s := Finset.univ)
    intro i _hi
    letI : IsProbabilityMeasure (model.offerLaw i) := model.offerLaw_isProbability i
    have haccepted_integrable : Integrable
        (fun p : ℝ => if p ≤ model.values i then p else 0)
        (model.offerLaw i) :=
      integrable_if_le_id_of_ae_nonneg
        (model.offerLaw i) (model.values i)
        (ae_nonneg_of_measure_Iio_eq_zero (model.offerLaw i) (model.offer_nonneg i))
    have haccepted_measurable : Measurable
        (fun p : ℝ => if p ≤ model.values i then p else 0) := by
      exact measurable_id.ite measurableSet_Iic measurable_const
    have hmap_integrable : Integrable
        (fun p : ℝ => if p ≤ model.values i then p else 0)
        (Measure.map (cdfQuantile (model.offerLaw i))
          (volume.restrict (Ioo (0 : ℝ) 1))) := by
      rw [map_cdfQuantile_volume_restrict_Ioo]
      exact haccepted_integrable
    have hpullback := (MeasureTheory.integrable_map_measure
      haccepted_measurable.aestronglyMeasurable
      (aemeasurable_cdfQuantile_volume_restrict_Ioo (model.offerLaw i))).mp
        hmap_integrable
    simpa [Function.comp_def] using hpullback

theorem paper_theorem8_2_expected_revenue_le_finite_candidate_benchmark_of_measure_accept_monotone_offer_source_model
    {Agent Outcome : Type*} [Fintype Agent] [Nonempty Agent]
    [DecidableEq Agent] [MeasurableSpace Outcome]
    (μ : Measure Outcome) [IsProbabilityMeasure μ]
    (values : Agent → ℝ) (offerPrice : Outcome → Agent → ℝ)
    (hoff_integrable : Integrable
      (fun outcome => paper_theorem8_2_journal_monotone_offer_revenue
        values (offerPrice outcome)) μ)
    (hoff_nonneg : ∀ᵐ outcome ∂μ, ∀ i, 0 ≤ offerPrice outcome i)
    (hoff_accept_monotone : ∀ᵐ outcome ∂μ, ∀ i j, values i ≤ values j →
      offerPrice outcome i ≤ values i → offerPrice outcome j ≤ offerPrice outcome i) :
    paper_theorem8_2_journal_monotone_measure_expected_revenue
        μ values offerPrice ≤
      finiteCandidateFixedPriceBenchmark values 1 := by
  let B : ℝ := finiteCandidateFixedPriceBenchmark values 1
  have hB_nonneg : 0 ≤ B := by
    exact finiteCandidateFixedPriceBenchmark_nonneg values 1
  have hpoint : ∀ᵐ outcome ∂μ,
      paper_theorem8_2_journal_monotone_offer_revenue values
          (offerPrice outcome) ≤ B := by
    filter_upwards [hoff_nonneg, hoff_accept_monotone] with outcome hnonneg haccept
    exact paper_theorem8_2_journal_accept_monotone_offer_revenue_le_finite_candidate_benchmark
      values (offerPrice outcome) hnonneg haccept
  have hB_integrable : Integrable (fun _ : Outcome => B) μ :=
    integrable_const B
  calc
    paper_theorem8_2_journal_monotone_measure_expected_revenue
        μ values offerPrice
        ≤ ∫ _ : Outcome, B ∂μ := by
          exact integral_mono_ae hoff_integrable hB_integrable hpoint
    _ = B := by
      rw [integral_const, measureReal_def, IsProbabilityMeasure.measure_univ]
      norm_num
    _ = finiteCandidateFixedPriceBenchmark values 1 := rfl

theorem paper_theorem8_2_expected_marginal_revenue_le_finite_candidate_benchmark
    {Agent Outcome : Type*} [Fintype Agent] [Nonempty Agent]
    [DecidableEq Agent] [MeasurableSpace Outcome]
    (model : PaperTheorem82ContinuousMarginalCoupling Agent Outcome) :
    paper_theorem8_2_continuous_marginal_expected_revenue
        model.values model.offerLaw ≤
      finiteCandidateFixedPriceBenchmark model.values 1 := by
  letI : IsProbabilityMeasure model.law := model.law_isProbability
  rw [paper_theorem8_2_continuous_marginal_expected_revenue_eq_coupled model]
  exact paper_theorem8_2_expected_revenue_le_finite_candidate_benchmark_of_measure_accept_monotone_offer_source_model
    model.law model.values model.offer model.coupled_integrable
    model.offer_nonneg model.offer_accept_monotone

/-- The journal Theorem 8.2 inequality for arbitrary real marginal offer
laws satisfying Definition 8.1.  The proof constructs the journal's shared
uniform inverse-CDF experiment and then applies the accepted-offer pointwise
benchmark bound. -/
theorem paper_theorem8_2_expected_marginal_revenue_le_finite_candidate_benchmark_of_raw_cdf_monotone_offer_source_model
    {Agent : Type*} [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (model : PaperTheorem82ContinuousRawCDFMonotoneOfferSourceModel Agent) :
    paper_theorem8_2_continuous_marginal_expected_revenue
        model.values model.offerLaw ≤
      finiteCandidateFixedPriceBenchmark model.values 1 := by
  exact paper_theorem8_2_expected_marginal_revenue_le_finite_candidate_benchmark
    (paper_theorem8_2_continuous_marginal_coupling_of_raw_cdf_monotone_offer_source_model
      model)

end GHW01DigitalGoods

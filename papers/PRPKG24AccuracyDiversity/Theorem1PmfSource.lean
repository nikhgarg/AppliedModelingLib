import PRPKG24AccuracyDiversity.AppendixD2DensitySource
import PRPKG24AccuracyDiversity.Definition3IidSource
import PRPKG24AccuracyDiversity.ProofInterface
import PRPKG24AccuracyDiversity.SourcePreferenceMixture

/-!
# Theorem 1(ii--iv) preferred-type PMF source endpoints

The distribution-specific Theorem 1 proofs are stated in terms of a
likelihood function because that is the optimizer's implementation surface.
The paper's equation (3), however, first samples a preferred type.  This
module binds the two surfaces: the likelihood is the real mass function of a
finite preferred-type PMF, and every allocation's objective is the resulting
outer PMF expectation.  The conditional iid models and their allocation
limits remain those proved by the distribution-specific endpoints.
-/

open scoped BigOperators

namespace PRPKG24AccuracyDiversity

open Filter Topology

/-- The bounded iid oracle is the expected realized top-`k` sample value. -/
private theorem boundedIidOrderStatisticConsumptionModel_value_eq_expectedSampleTopKSum
    {T : ℕ} (likelihood : ItemType T → ℝ) (k : ℕ)
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_finite_mean : MeasureTheory.Integrable (fun x : ℝ => x) baseMeasure)
    (t : ItemType T) (q : ℕ) :
    (boundedIidOrderStatisticConsumptionModel likelihood k baseMeasure).valueOfCount t q =
      AppliedModelingLib.Probability.expectedSampleTopKSum
        (definition3IidSampleMeasure baseMeasure q) k := by
  change
    AppliedModelingLib.Probability.orderStatisticTopKSumFromMean
        (boundedIidOrderStatisticMeanSeq baseMeasure) k q =
      AppliedModelingLib.Probability.expectedSampleTopKSum
        (definition3IidSampleMeasure baseMeasure q) k
  simpa [boundedIidOrderStatisticMeanSeq, definition3IidOrderStatisticMean,
    definition3IidSampleMeasure] using
    definition3_iid_orderStatisticTopKSum_eq_expectedSampleTopKSum
      baseMeasure h_finite_mean k q

/-- The exponential oracle is the expected realized top-`k` iid sample value. -/
private theorem exponentialTopKOrderStatisticConsumptionModel_value_eq_expectedSampleTopKSum
    {T : ℕ} (likelihood : ItemType T → ℝ) (lambda : ℝ)
    (hlambda_pos : 0 < lambda) (k : ℕ) (t : ItemType T) (q : ℕ) :
    ((exponentialTopKOrderStatisticOracle T lambda k).toConsumptionModel
      likelihood k).valueOfCount t q =
      AppliedModelingLib.Probability.expectedSampleTopKSum
        ((exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q) k := by
  change exponentialTopKOrderStatisticValue lambda k q =
    AppliedModelingLib.Probability.expectedSampleTopKSum
      ((exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q) k
  cases q with
  | zero =>
      have hzero :
          (fun sample : Fin 0 → ℝ =>
            AppliedModelingLib.Probability.sampleTopKSum sample k) = fun _ => 0 := by
        funext sample
        unfold AppliedModelingLib.Probability.sampleTopKSum
        apply Finset.sum_eq_zero
        intro i _
        exact False.elim ((Nat.not_lt_zero i.val)
          (lt_of_lt_of_le i.isLt (min_le_right k 0)))
      simp [AppliedModelingLib.Probability.expectedSampleTopKSum, hzero]
  | succ q =>
      let M := exponentialDistributionModel lambda hlambda_pos
      letI : NeZero (q + 1) := ⟨Nat.add_one_ne_zero q⟩
      symm
      calc
        AppliedModelingLib.Probability.expectedSampleTopKSum (M.iidProductMeasure (q + 1)) k =
            ∫ sample, exponentialFiniteSampleTopKSum k sample
              ∂M.iidProductMeasure (q + 1) := by
            simpa [M, exponentialFiniteSampleTopKSum] using
              AppliedModelingLib.Probability.expectedSampleTopKSum_eq_integral_topKSumOn_of_ae_nonneg
                (M.iidProductMeasure (q + 1)) k
                (M.iidProductMeasure_all_nonnegative_ae (q + 1))
        _ = exponentialTopKOrderStatisticValue lambda k (q + 1) := by
            simpa [M] using
              paper_theorem1_iii_exponential_finite_sample_top_k_integral_order_statistic
                lambda hlambda_pos (q := q + 1) k

/-- The Pareto iid oracle is the expected realized top-`k` sample value. -/
private theorem paretoIidOrderStatisticConsumptionModel_value_eq_expectedSampleTopKSum
    {T : ℕ} (likelihood : ItemType T → ℝ) {k : ℕ} {alpha : ℝ}
    (halpha : 1 < alpha) (t : ItemType T) (q : ℕ) :
    (paretoIidOrderStatisticConsumptionModel likelihood k alpha).valueOfCount t q =
      AppliedModelingLib.Probability.expectedSampleTopKSum
        (paretoIidSampleMeasure alpha q) k := by
  change
    AppliedModelingLib.Probability.orderStatisticTopKSumFromMean
        (paretoIidOrderStatisticMeanSeq alpha) k q =
      AppliedModelingLib.Probability.expectedSampleTopKSum
        (paretoIidSampleMeasure alpha q) k
  simpa [paretoIidOrderStatisticMeanSeq] using
    AppliedModelingLib.Probability.expectedOrderStatisticMeanSeq_topKSum_eq_expectedSampleTopKSum
      (paretoIidSampleMeasure alpha) k q (by
        intro i hi
        have hi_lt : i < min k q := Finset.mem_range.mp hi
        have hiq : i < q := lt_of_lt_of_le hi_lt (min_le_right k q)
        have hvalue :
            (fun sample : Fin q → ℝ =>
              AppliedModelingLib.Probability.sampleOrderStatisticValue sample (q - i)) =
              fun sample =>
                AppliedModelingLib.Probability.upperOrderStatistic sample ⟨i, hiq⟩ := by
            funext sample
            exact AppliedModelingLib.Probability.sampleOrderStatisticValue_eq_upperOrderStatistic_of_rank_from_top
              sample hiq
        rw [hvalue]
        simpa [paretoIidSampleMeasure] using
          AppliedModelingLib.Probability.Pareto.iidProductMeasure_one_upperOrderStatistic_integrable
            halpha (rankFromTop := ⟨i, hiq⟩))

/--
Theorem 1(ii) with the paper's preferred-type draw made explicit as a PMF.

The bounded conditional iid law is the literal `withDensity` probability law
from the PDF endpoint.  The outer equation is only over the selected
preferred type; it makes no assertion about a joint coupling of conditional
samples belonging to different types.
-/
theorem theorem1_ii_bounded_iid_pmf_source_model_endpoint
    {T : ℕ} [NeZero T] {beta c M L : ℝ} {k : ℕ}
    (preferenceLaw : SourcePreferenceLaw T)
    (baseMeasure : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure baseMeasure]
    (h_finite_mean : MeasureTheory.Integrable (fun x : ℝ => x) baseMeasure)
    (h_base_bounds :
      ∀ᵐ y ∂baseMeasure, L ≤ y ∧ y ≤ M)
    (h_nonneg : ∀ᵐ y ∂baseMeasure, 0 ≤ y)
    (hM_pos : 0 < M)
    (f : ℝ → ℝ)
    (hpdf :
      baseMeasure = MeasureTheory.volume.withDensity
        (fun y => ENNReal.ofReal (f y)))
    (hf_nonneg : ∀ y, 0 ≤ f y)
    (hf_measurable : Measurable f)
    (hbeta_pos : 0 < beta) (hc_pos : 0 < c)
    (hratio :
      Tendsto (fun x : ℝ => f x / ((M - x) ^ (beta - 1)))
        (nhdsWithin M (Set.Iio M)) (nhds c))
    (hpreference_pos : ∀ t : ItemType T, 0 < (preferenceLaw t).toReal)
    (k_pos : 0 < k)
    (hwidth_pos : 0 < M - L)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          boundedIidOrderStatisticConsumptionModel
            (fun t => (preferenceLaw t).toReal) k baseMeasure)) :
    (∀ a : CountAllocation T,
      (boundedIidOrderStatisticConsumptionModel
          (fun t => (preferenceLaw t).toReal) k baseMeasure).objective a =
        AppliedModelingLib.pmfExp preferenceLaw
          (fun t =>
            AppliedModelingLib.Probability.expectedSampleTopKSum
              (definition3IidSampleMeasure baseMeasure (a.count t)) k)) ∧
      ∀ t : ItemType T,
        Tendsto
          (fun N => CountAllocation.representation (seq.allocation N) t)
          atTop
          (nhds
            (((preferenceLaw t).toReal) ^ (beta / (beta + 1)) /
              ∑ i : ItemType T,
                ((preferenceLaw i).toReal) ^ (beta / (beta + 1)))) := by
  constructor
  · intro a
    calc
      (boundedIidOrderStatisticConsumptionModel
          (fun t => (preferenceLaw t).toReal) k baseMeasure).objective a =
          AppliedModelingLib.pmfExp preferenceLaw
            (fun t =>
              (boundedIidOrderStatisticConsumptionModel
                (fun i => (preferenceLaw i).toReal) k baseMeasure).valueOfCount
                t (a.count t)) :=
        ConsumptionModel.objective_eq_sourcePreferenceLaw_pmfExp
          (boundedIidOrderStatisticConsumptionModel
            (fun t => (preferenceLaw t).toReal) k baseMeasure)
          a preferenceLaw (by
            intro t
            rfl)
      _ = AppliedModelingLib.pmfExp preferenceLaw
            (fun t =>
              AppliedModelingLib.Probability.expectedSampleTopKSum
                (definition3IidSampleMeasure baseMeasure (a.count t)) k) := by
        congr 1
        funext t
        exact boundedIidOrderStatisticConsumptionModel_value_eq_expectedSampleTopKSum
          (fun i => (preferenceLaw i).toReal) k baseMeasure h_finite_mean t
          (a.count t)
  · exact theorem1_ii_bounded_iid_upper_endpoint_pdf_sequence_formula
      baseMeasure h_finite_mean h_base_bounds h_nonneg hM_pos f hpdf
      hf_nonneg hf_measurable hbeta_pos hc_pos hratio
      (fun t => (preferenceLaw t).toReal) hpreference_pos k_pos hwidth_pos seq

/--
Theorem 1(iii) with a PMF preferred-type draw and the existing common
exponential iid conditional model.
-/
theorem theorem1_iii_exponential_iid_pmf_source_model_endpoint
    {T : ℕ} [NeZero T]
    (preferenceLaw : SourcePreferenceLaw T) (lambda : ℝ) (k : ℕ)
    (hlambda_pos : 0 < lambda)
    (hk_pos : 0 < k)
    (hpreference_pos : ∀ t : ItemType T, 0 < (preferenceLaw t).toReal)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          (exponentialTopKOrderStatisticOracle T lambda k).toConsumptionModel
            (fun t => (preferenceLaw t).toReal) k)) :
    (∀ a : CountAllocation T,
      ((exponentialTopKOrderStatisticOracle T lambda k).toConsumptionModel
          (fun t => (preferenceLaw t).toReal) k).objective a =
        AppliedModelingLib.pmfExp preferenceLaw
          (fun t =>
            AppliedModelingLib.Probability.expectedSampleTopKSum
              ((exponentialDistributionModel lambda hlambda_pos).iidProductMeasure
                (a.count t)) k)) ∧
      ∀ t : ItemType T,
        Tendsto
          (fun N => CountAllocation.representation (seq.allocation N) t)
          atTop
          (nhds
            (((preferenceLaw t).toReal) ^ (1 : ℝ) /
              ∑ i : ItemType T, ((preferenceLaw i).toReal) ^ (1 : ℝ))) := by
  constructor
  · intro a
    calc
      ((exponentialTopKOrderStatisticOracle T lambda k).toConsumptionModel
          (fun t => (preferenceLaw t).toReal) k).objective a =
          AppliedModelingLib.pmfExp preferenceLaw
            (fun t =>
              ((exponentialTopKOrderStatisticOracle T lambda k).toConsumptionModel
                (fun i => (preferenceLaw i).toReal) k).valueOfCount
                t (a.count t)) :=
        ConsumptionModel.objective_eq_sourcePreferenceLaw_pmfExp
          ((exponentialTopKOrderStatisticOracle T lambda k).toConsumptionModel
            (fun t => (preferenceLaw t).toReal) k)
          a preferenceLaw (by
            intro t
            rfl)
      _ = AppliedModelingLib.pmfExp preferenceLaw
            (fun t =>
              AppliedModelingLib.Probability.expectedSampleTopKSum
                ((exponentialDistributionModel lambda hlambda_pos).iidProductMeasure
                  (a.count t)) k) := by
        congr 1
        funext t
        exact exponentialTopKOrderStatisticConsumptionModel_value_eq_expectedSampleTopKSum
          (fun i => (preferenceLaw i).toReal) lambda hlambda_pos k t
          (a.count t)
  · exact paper_theorem1_iii_exponential_top_k_order_statistic_sequence_formula
      (fun t => (preferenceLaw t).toReal) lambda k
      hlambda_pos hk_pos hpreference_pos seq

/--
Theorem 1(iv) with a PMF preferred-type draw and the concrete scale-one iid
Pareto conditional model.
-/
theorem theorem1_iv_pareto_iid_pmf_source_model_endpoint
    {T : ℕ} [NeZero T]
    (preferenceLaw : SourcePreferenceLaw T) {k : ℕ} {alpha : ℝ}
    (halpha : 1 < alpha) (hk : 0 < k)
    (hpreference_pos : ∀ t : ItemType T, 0 < (preferenceLaw t).toReal)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          paretoIidOrderStatisticConsumptionModel
            (fun t => (preferenceLaw t).toReal) k alpha)) :
    (∀ a : CountAllocation T,
      (paretoIidOrderStatisticConsumptionModel
          (fun t => (preferenceLaw t).toReal) k alpha).objective a =
        AppliedModelingLib.pmfExp preferenceLaw
          (fun t =>
            AppliedModelingLib.Probability.expectedSampleTopKSum
              (paretoIidSampleMeasure alpha (a.count t)) k)) ∧
      ∀ t : ItemType T,
        Tendsto
          (fun N => CountAllocation.representation (seq.allocation N) t)
          atTop
          (nhds
            (((preferenceLaw t).toReal) ^ (alpha / (alpha - 1)) /
              ∑ i : ItemType T,
                ((preferenceLaw i).toReal) ^ (alpha / (alpha - 1)))) := by
  constructor
  · intro a
    calc
      (paretoIidOrderStatisticConsumptionModel
          (fun t => (preferenceLaw t).toReal) k alpha).objective a =
          AppliedModelingLib.pmfExp preferenceLaw
            (fun t =>
              (paretoIidOrderStatisticConsumptionModel
                (fun i => (preferenceLaw i).toReal) k alpha).valueOfCount
                t (a.count t)) :=
        ConsumptionModel.objective_eq_sourcePreferenceLaw_pmfExp
          (paretoIidOrderStatisticConsumptionModel
            (fun t => (preferenceLaw t).toReal) k alpha)
          a preferenceLaw (by
            intro t
            rfl)
      _ = AppliedModelingLib.pmfExp preferenceLaw
            (fun t =>
              AppliedModelingLib.Probability.expectedSampleTopKSum
                (paretoIidSampleMeasure alpha (a.count t)) k) := by
        congr 1
        funext t
        exact paretoIidOrderStatisticConsumptionModel_value_eq_expectedSampleTopKSum
          (fun i => (preferenceLaw i).toReal) halpha t (a.count t)
  · exact paper_theorem1_iv_pareto_iid_order_statistic_sequence_formula
      (fun t => (preferenceLaw t).toReal)
      halpha hk hpreference_pos seq

end PRPKG24AccuracyDiversity

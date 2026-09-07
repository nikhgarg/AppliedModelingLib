import PRPKG24AccuracyDiversity.MainTheorems

namespace PRPKG24AccuracyDiversity

open scoped BigOperators

/--
For a valid upper rank, the pointwise top-`r+1` sum differs from the top-`r`
sum by exactly the `r`-from-top order statistic.

This indexing lemma is kept local to the source-Lemma-D.3 bridge.  The paper
uses the equivalent one-based bottom index `q - r`.
-/
private theorem sampleTopKSum_succ_sub_eq_upperOrderStatistic
    {q r : ℕ} (hrq : r < q) (sample : Fin q → ℝ) :
    AppliedModelingLib.Probability.sampleTopKSum sample (r + 1) =
      AppliedModelingLib.Probability.sampleTopKSum sample r +
        AppliedModelingLib.Probability.upperOrderStatistic sample ⟨r, hrq⟩ := by
  have hr_le_q : r ≤ q := Nat.le_of_lt hrq
  have hrsucc_le_q : r + 1 ≤ q := Nat.succ_le_iff.mpr hrq
  have hmin_succ : min (r + 1) q = r + 1 := min_eq_left hrsucc_le_q
  have hmin : min r q = r := min_eq_left hr_le_q
  let eSucc : Fin (r + 1) ≃ Fin (min (r + 1) q) :=
    (Fin.castOrderIso hmin_succ.symm).toEquiv
  let e : Fin r ≃ Fin (min r q) :=
    (Fin.castOrderIso hmin.symm).toEquiv
  have htop_succ :
      AppliedModelingLib.Probability.sampleTopKSum sample (r + 1) =
        ∑ i : Fin (r + 1),
          AppliedModelingLib.Probability.upperOrderStatistic sample
            (AppliedModelingLib.Probability.topKRankEmbedding (r + 1) q (eSucc i)) := by
    unfold AppliedModelingLib.Probability.sampleTopKSum
    symm
    exact Fintype.sum_equiv eSucc
      (fun i => AppliedModelingLib.Probability.upperOrderStatistic sample
        (AppliedModelingLib.Probability.topKRankEmbedding (r + 1) q (eSucc i)))
      (fun i => AppliedModelingLib.Probability.upperOrderStatistic sample
        (AppliedModelingLib.Probability.topKRankEmbedding (r + 1) q i))
      (fun _ => rfl)
  have htop :
      AppliedModelingLib.Probability.sampleTopKSum sample r =
        ∑ i : Fin r,
          AppliedModelingLib.Probability.upperOrderStatistic sample
            (AppliedModelingLib.Probability.topKRankEmbedding r q (e i)) := by
    unfold AppliedModelingLib.Probability.sampleTopKSum
    symm
    exact Fintype.sum_equiv e
      (fun i => AppliedModelingLib.Probability.upperOrderStatistic sample
        (AppliedModelingLib.Probability.topKRankEmbedding r q (e i)))
      (fun i => AppliedModelingLib.Probability.upperOrderStatistic sample
        (AppliedModelingLib.Probability.topKRankEmbedding r q i))
      (fun _ => rfl)
  rw [htop_succ, htop]
  rw [Fin.sum_univ_castSucc (n := r)]
  congr 1

/--
The generic expected top-`k` statistic is integrable for a positive-rate iid
exponential sample.  This is obtained from the concrete maximizing-subset
statistic only after using nonnegativity to identify it with the sorted
top-`k` statistic.
-/
private theorem exponential_iid_expectedSampleTopKSum_integrable
    (lambda : ℝ) (hlambda_pos : 0 < lambda) {q : ℕ} [NeZero q] (k : ℕ) :
    MeasureTheory.Integrable
      (fun sample : Fin q → ℝ => AppliedModelingLib.Probability.sampleTopKSum sample k)
      ((exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q) := by
  let M := exponentialDistributionModel lambda hlambda_pos
  have hsample_eq :
      (fun sample : Fin q → ℝ =>
        AppliedModelingLib.Probability.sampleTopKSum sample k) =ᵐ[M.iidProductMeasure q]
        exponentialFiniteSampleTopKSum (q := q) k := by
    filter_upwards [M.iidProductMeasure_all_nonnegative_ae q] with sample hnonneg
    simpa [exponentialFiniteSampleTopKSum] using
      (AppliedModelingLib.Probability.topKSumOn_eq_sampleTopKSum_of_forall_nonneg
        sample k hnonneg).symm
  exact (exponentialFiniteSampleTopKSum_integrable M k).congr hsample_eq.symm

/--
For a valid upper rank, the expected iid exponential order statistic is the
difference between two concrete expected top-`k` sample sums.
-/
private theorem exponential_iid_expectedUpperOrderStatistic_eq_topK_difference
    (lambda : ℝ) (hlambda_pos : 0 < lambda) {q r : ℕ} (hrq : r < q) :
    AppliedModelingLib.Probability.expectedUpperOrderStatistic
        ((exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q)
        ⟨r, hrq⟩ =
      AppliedModelingLib.Probability.expectedSampleTopKSum
          ((exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q)
          (r + 1) -
        AppliedModelingLib.Probability.expectedSampleTopKSum
          ((exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q)
          r := by
  let M := exponentialDistributionModel lambda hlambda_pos
  let mu := M.iidProductMeasure q
  let f : (Fin q → ℝ) → ℝ := fun sample =>
    AppliedModelingLib.Probability.sampleTopKSum sample (r + 1)
  let g : (Fin q → ℝ) → ℝ := fun sample =>
    AppliedModelingLib.Probability.sampleTopKSum sample r
  let h : (Fin q → ℝ) → ℝ := fun sample =>
    AppliedModelingLib.Probability.upperOrderStatistic sample ⟨r, hrq⟩
  have hpoint : f = fun sample => g sample + h sample := by
    funext sample
    exact sampleTopKSum_succ_sub_eq_upperOrderStatistic hrq sample
  have hq_ne : q ≠ 0 := Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le r) hrq)
  letI : NeZero q := ⟨hq_ne⟩
  have hf_int : MeasureTheory.Integrable f mu := by
    simpa [f, mu, M] using
      exponential_iid_expectedSampleTopKSum_integrable lambda hlambda_pos (q := q)
        (r + 1)
  have hg_int : MeasureTheory.Integrable g mu := by
    simpa [g, mu, M] using
      exponential_iid_expectedSampleTopKSum_integrable lambda hlambda_pos (q := q) r
  have hh_int : MeasureTheory.Integrable h mu := by
    have hsub : f - g = h := by
      funext sample
      have hs := congrFun hpoint sample
      dsimp [f, g, h] at hs ⊢
      linarith
    exact (hf_int.sub hg_int).congr (Filter.Eventually.of_forall
      (fun sample => congrFun hsub sample))
  have hint :
      (∫ sample, f sample ∂mu) =
        (∫ sample, g sample ∂mu) + (∫ sample, h sample ∂mu) := by
    rw [hpoint]
    exact MeasureTheory.integral_add hg_int hh_int
  change (∫ sample, h sample ∂mu) =
    (∫ sample, f sample ∂mu) - (∫ sample, g sample ∂mu)
  linarith

/--
The concrete iid exponential top-`k` expectation agrees with the finite
harmonic order-statistic oracle.  Unlike the abstract oracle, the left side
is an integral over the actual product sample law.
-/
private theorem exponential_iid_expectedSampleTopKSum_eq_orderStatisticValue
    (lambda : ℝ) (hlambda_pos : 0 < lambda) {q : ℕ} [NeZero q] (k : ℕ) :
    AppliedModelingLib.Probability.expectedSampleTopKSum
        ((exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q) k =
      exponentialTopKOrderStatisticValue lambda k q := by
  let M := exponentialDistributionModel lambda hlambda_pos
  calc
    AppliedModelingLib.Probability.expectedSampleTopKSum (M.iidProductMeasure q) k =
        ∫ sample, exponentialFiniteSampleTopKSum (q := q) k sample
          ∂M.iidProductMeasure q := by
          simpa [exponentialFiniteSampleTopKSum] using
            (AppliedModelingLib.Probability.expectedSampleTopKSum_eq_integral_topKSumOn_of_ae_nonneg
              (M.iidProductMeasure q) k (M.iidProductMeasure_all_nonnegative_ae q))
    _ = exponentialTopKOrderStatisticValue lambda k q := by
      simpa [M] using
        paper_theorem1_iii_exponential_finite_sample_top_k_integral_order_statistic
          lambda hlambda_pos (q := q) k

/--
Corrected source Lemma D.3 finite formula.  For the positive-rate iid
exponential model, the paper's one-based bottom index `q - r` is the
`r`-from-top statistic, and its expected value is exactly
`(H_q - H_r) / lambda` whenever the rank is valid.

The printed source omits the factor `1 / lambda` in its logarithmic display;
this exact identity retains that factor.
-/
theorem lemmaD3_exponential_iid_fixed_rank_mean_eq_harmonic_difference
    (lambda : ℝ) (hlambda_pos : 0 < lambda) {q r : ℕ} (hrq : r < q) :
    expectedOrderStatisticMeanSeq
        (fun a => (exponentialDistributionModel lambda hlambda_pos).iidProductMeasure a)
        (q - r) q =
      (1 / lambda) * (harmonicReal q - harmonicReal r) := by
  have hq_pos : 0 < q := lt_of_le_of_lt (Nat.zero_le r) hrq
  letI : NeZero q := ⟨Nat.ne_of_gt hq_pos⟩
  calc
    expectedOrderStatisticMeanSeq
        (fun a => (exponentialDistributionModel lambda hlambda_pos).iidProductMeasure a)
        (q - r) q =
        AppliedModelingLib.Probability.expectedUpperOrderStatistic
          ((exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q)
          ⟨r, hrq⟩ := by
          simpa [expectedOrderStatisticMeanSeq] using
            AppliedModelingLib.Probability.expectedSampleOrderStatisticMean_eq_expectedUpperOrderStatistic_of_rank_from_top
              (μ := (exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q)
              (r := r) (a := q) hrq
    _ =
        AppliedModelingLib.Probability.expectedSampleTopKSum
            ((exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q)
            (r + 1) -
          AppliedModelingLib.Probability.expectedSampleTopKSum
            ((exponentialDistributionModel lambda hlambda_pos).iidProductMeasure q)
            r :=
      exponential_iid_expectedUpperOrderStatistic_eq_topK_difference
        lambda hlambda_pos hrq
    _ =
        exponentialTopKOrderStatisticValue lambda (r + 1) q -
          exponentialTopKOrderStatisticValue lambda r q := by
      rw [exponential_iid_expectedSampleTopKSum_eq_orderStatisticValue
        lambda hlambda_pos (r + 1),
        exponential_iid_expectedSampleTopKSum_eq_orderStatisticValue
          lambda hlambda_pos r]
    _ = (1 / lambda) * (harmonicReal q - harmonicReal r) := by
      by_cases hr_zero : r = 0
      · subst r
        rw [exponentialTopKOrderStatisticValue_eq_harmonic_of_k_le
          lambda (by omega : 0 < 0 + 1) (by omega : 0 + 1 ≤ q),
          harmonicReal_succ, harmonicReal_zero]
        simp [exponentialTopKOrderStatisticValue]
      · have hr_pos : 0 < r := Nat.pos_of_ne_zero hr_zero
        rw [exponentialTopKOrderStatisticValue_eq_harmonic_of_k_le
          lambda (by omega : 0 < r + 1) (by omega : r + 1 ≤ q),
          exponentialTopKOrderStatisticValue_eq_harmonic_of_k_le
            lambda hr_pos (Nat.le_of_lt hrq), harmonicReal_succ]
        have hr_cast_ne : (r + 1 : ℝ) ≠ 0 := by positivity
        field_simp [hr_cast_ne]
        push_cast
        ring

/--
Corrected source Lemma D.3 asymptotic for a fixed upper rank.  The logarithmic
coefficient is `1 / lambda`, and the finite-rank correction is
`-(1 / lambda) * H_r`.
-/
theorem lemmaD3_exponential_iid_fixed_rank_sub_log_tendsto
    (lambda : ℝ) (hlambda_pos : 0 < lambda) (r : ℕ) :
    Filter.Tendsto
      (fun q : ℕ =>
        expectedOrderStatisticMeanSeq
            (fun a =>
              (exponentialDistributionModel lambda hlambda_pos).iidProductMeasure a)
            (q - r) q -
          (1 / lambda) * Real.log q)
      Filter.atTop
      (nhds
        ((1 / lambda) *
          (Real.eulerMascheroniConstant - harmonicReal r))) := by
  let c : ℝ := 1 / lambda
  have hbase :
      Filter.Tendsto
        (fun q : ℕ => harmonicReal q - Real.log q)
        Filter.atTop (nhds Real.eulerMascheroniConstant) := by
    have h := Real.tendsto_harmonic_sub_log
    refine h.congr' ?_
    filter_upwards with q
    rw [harmonicReal_eq_harmonic]
  have hlim :
      Filter.Tendsto
        (fun q : ℕ =>
          c * (-harmonicReal r) + c * (harmonicReal q - Real.log q))
        Filter.atTop
        (nhds
          (c * (-harmonicReal r) +
            c * Real.eulerMascheroniConstant)) :=
    tendsto_const_nhds.add (hbase.const_mul c)
  have htarget :
      Filter.Tendsto
        (fun q : ℕ =>
          c * (-harmonicReal r) + c * (harmonicReal q - Real.log q))
        Filter.atTop
        (nhds
          ((1 / lambda) *
            (Real.eulerMascheroniConstant - harmonicReal r))) := by
    convert hlim using 1
    dsimp [c]
    ring_nf
  refine htarget.congr' ?_
  filter_upwards [Filter.eventually_atTop.2
    ⟨r + 1, fun q hq => hq⟩] with q hq
  have hrq : r < q := by omega
  rw [lemmaD3_exponential_iid_fixed_rank_mean_eq_harmonic_difference
    lambda hlambda_pos hrq]
  dsimp [c]
  ring

/--
Corrected source Lemma D.3 discrete strict-concavity consequence.  Since the
global order-statistic interface totalizes invalid small ranks, strict
diminishing forward marginals are stated on the eventual valid-rank tail.
-/
theorem lemmaD3_exponential_iid_fixed_rank_forward_marginal_strict_antitone_eventually
    (lambda : ℝ) (hlambda_pos : 0 < lambda) (r : ℕ) :
    ∀ᶠ q in Filter.atTop,
      expectedOrderStatisticMeanSeq
          (fun a =>
            (exponentialDistributionModel lambda hlambda_pos).iidProductMeasure a)
          (q + 2 - r) (q + 2) -
        expectedOrderStatisticMeanSeq
          (fun a =>
            (exponentialDistributionModel lambda hlambda_pos).iidProductMeasure a)
          (q + 1 - r) (q + 1) <
      expectedOrderStatisticMeanSeq
          (fun a =>
            (exponentialDistributionModel lambda hlambda_pos).iidProductMeasure a)
          (q + 1 - r) (q + 1) -
        expectedOrderStatisticMeanSeq
          (fun a =>
            (exponentialDistributionModel lambda hlambda_pos).iidProductMeasure a)
          (q - r) q := by
  filter_upwards [Filter.eventually_atTop.2
    ⟨r + 1, fun q hq => hq⟩] with q hq
  have hrq : r < q := by omega
  have hrq_succ : r < q + 1 := by omega
  have hrq_succ_succ : r < q + 2 := by omega
  rw [lemmaD3_exponential_iid_fixed_rank_mean_eq_harmonic_difference
      lambda hlambda_pos hrq_succ_succ,
    lemmaD3_exponential_iid_fixed_rank_mean_eq_harmonic_difference
      lambda hlambda_pos hrq_succ,
    lemmaD3_exponential_iid_fixed_rank_mean_eq_harmonic_difference
      lambda hlambda_pos hrq]
  rw [harmonicReal_succ (q + 1), harmonicReal_succ q]
  have hq_succ_pos : (0 : ℝ) < ((q + 1 : ℕ) : ℝ) := by positivity
  have hq_succ_lt : ((q + 1 : ℕ) : ℝ) < ((q + 2 : ℕ) : ℝ) := by
    norm_num
  have hrecip :
      (1 : ℝ) / ((q + 2 : ℕ) : ℝ) <
        (1 : ℝ) / ((q + 1 : ℕ) : ℝ) :=
    one_div_lt_one_div_of_lt hq_succ_pos hq_succ_lt
  have hscale_pos : 0 < 1 / lambda := one_div_pos.mpr hlambda_pos
  have hscaled := mul_lt_mul_of_pos_left hrecip hscale_pos
  linarith

end PRPKG24AccuracyDiversity

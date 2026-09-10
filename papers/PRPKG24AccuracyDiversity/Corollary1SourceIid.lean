import PRPKG24AccuracyDiversity.MainTheorems
import AppliedModelingLib.Applications.RatingSystems.BinaryLargeDeviations

/-!
# Corollary 1 Source-IID Witnesses

This module makes the existential model in source Corollary 1 reviewable:
the witness is one of the four concrete source-iid constructions used by the
case proof, with its admissible parameters and the equation identifying its
homogeneity exponent recorded in the proposition itself.
-/

open scoped BigOperators

namespace PRPKG24AccuracyDiversity

/--
The literal two-point i.i.d. source model used by Corollary 1's `gamma = 0`
case.  The conditional item-value law is the same Bernoulli law for every
type; `k` only specifies the fixed top-`k` evaluation of an item set.
-/
noncomputable def corollary1FiniteTwoPointBernoulliSourceIidModel {T : ℕ}
    (likelihood : ItemType T → ℝ) (k : ℕ) (q : ℝ)
    (hq_nonneg : 0 ≤ q) (hq_le_one : q ≤ 1) : ConsumptionModel T :=
  (TopKValueOracle.common T
    (finiteDiscreteIidTopKExpected Bool
      (AppliedModelingLib.Probability.realBernoulliPMF q hq_nonneg hq_le_one)
      k AppliedModelingLib.Probability.binaryRatingScore)).toConsumptionModel
        likelihood k

/--
The direct finite-discrete i.i.d. top-`k` Bernoulli realization of Corollary
1's zero-homogeneity case.  This is not the old top-one satisfaction model:
the returned consumption model is the expected sum of the best `k` draws from
a common two-point conditional-value law.
-/
theorem paper_corollary1_finite_discrete_bernoulli_top_k_gamma_zero_sequence_formula
    {T : ℕ} [NeZero T] {k : ℕ}
    (likelihood : ItemType T → ℝ) (q : ℝ)
    (hq_pos : 0 < q) (hq_lt_one : q < 1) (hk_pos : 0 < k)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t)
    (seq :
      OptimalAllocationSequence
        (fun _ =>
          corollary1FiniteTwoPointBernoulliSourceIidModel likelihood k q
            hq_pos.le hq_lt_one.le)) :
    ∀ t : ItemType T,
      Filter.Tendsto
        (fun N => CountAllocation.representation (seq.allocation N) t)
        Filter.atTop
        (nhds
          ((likelihood t) ^ (0 : ℝ) /
            ∑ i : ItemType T, (likelihood i) ^ (0 : ℝ))) := by
  let itemLaw : PMF Bool :=
    AppliedModelingLib.Probability.realBernoulliPMF q hq_pos.le hq_lt_one.le
  have htop_mass :
      AppliedModelingLib.pmfProb itemLaw
          (fun b => AppliedModelingLib.Probability.binaryRatingScore b = (1 : ℝ)) = q := by
    simpa [itemLaw] using
      AppliedModelingLib.Probability.realBernoulliPMF_binaryRatingScore_one_prob q
        hq_pos.le hq_lt_one.le
  have hnontop_mass :
      0 < AppliedModelingLib.pmfProb itemLaw
          (fun b => ¬ AppliedModelingLib.Probability.binaryRatingScore b = (1 : ℝ)) := by
    rw [AppliedModelingLib.pmfProb_compl]
    rw [htop_mass]
    linarith
  have hconv :
      seq.toAllocationSequence.ConvergesToProfile (uniformProfile T) := by
    simpa [corollary1FiniteTwoPointBernoulliSourceIidModel, itemLaw] using
      paper_theorem1_i_finite_discrete_sequence_homogeneity_of_iid_top_split
        (xTop := 1) (xSecond := 0)
        itemLaw AppliedModelingLib.Probability.binaryRatingScore likelihood k seq hk_pos
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by
          intro b
          cases b <;> simp [AppliedModelingLib.Probability.binaryRatingScore])
        (by
          intro b
          cases b <;> simp [AppliedModelingLib.Probability.binaryRatingScore])
        (by rw [htop_mass]; exact hq_pos)
        hnontop_mass hlike_pos
  intro t
  have htarget :
      (likelihood t) ^ (0 : ℝ) /
          ∑ i : ItemType T, (likelihood i) ^ (0 : ℝ) =
        1 / (T : ℝ) := by
    have hden :
        (∑ i : ItemType T, (likelihood i) ^ (0 : ℝ)) = (T : ℝ) := by
      simp [Real.rpow_zero]
    rw [hden]
    simp [Real.rpow_zero]
  simpa [AllocationSequence.representation, uniformProfile_targetShare, htarget] using
    hconv t

/--
The four concrete source-iid families used to witness Corollary 1.

Each constructor exposes both the actual conditional-value law `D` and the
consumption-model expression generated from that law, along with the parameter
bounds and the equation connecting that branch's parameterization to `gamma`.
This is a semantic provenance predicate rather than a name-only label or
certificate assumption.
-/
inductive Corollary1SourceIidFamily {T : ℕ}
    (likelihood : ItemType T → ℝ) (gamma : ℝ) (k : ℕ) :
    MeasureTheory.Measure ℝ → ConsumptionModel T → Prop where
  | finiteTwoPointBernoulli
      (q : ℝ) (hq_pos : 0 < q) (hq_lt_one : q < 1)
      (hgamma : gamma = 0) :
      Corollary1SourceIidFamily likelihood gamma k
        (MeasureTheory.Measure.map AppliedModelingLib.Probability.binaryRatingScore
          (AppliedModelingLib.Probability.realBernoulliPMF q
            hq_pos.le hq_lt_one.le).toMeasure)
        (corollary1FiniteTwoPointBernoulliSourceIidModel likelihood k q
          hq_pos.le hq_lt_one.le)
  | boundedReflectedPowerOrderStatistic
      (beta : ℝ)
      (hbeta_pos : 0 < beta) (hk_pos : 0 < k)
      (hgamma : beta / (beta + 1) = gamma) :
      Corollary1SourceIidFamily likelihood gamma k
        (boundedReflectedPowerSourceMeasure beta)
        (boundedReflectedPowerSourceIidOrderStatisticConsumptionModel
          likelihood k beta)
  | exponentialOrderStatistic
      (lambda : ℝ)
      (hlambda_pos : 0 < lambda) (hk_pos : 0 < k)
      (hgamma : gamma = 1) :
      Corollary1SourceIidFamily likelihood gamma k
        ((exponentialDistributionModel lambda hlambda_pos).measure)
        ((exponentialTopKOrderStatisticOracle T lambda k).toConsumptionModel
          likelihood k)
  | paretoOrderStatistic
      (alpha : ℝ)
      (halpha_gt_one : 1 < alpha) (hk_pos : 0 < k)
      (hgamma : alpha / (alpha - 1) = gamma) :
      Corollary1SourceIidFamily likelihood gamma k
        (ProbabilityTheory.paretoMeasure 1 alpha)
        (paretoIidOrderStatisticConsumptionModel likelihood k alpha)

/--
Source Corollary 1 with the returned conditional-value model tied explicitly
to a concrete source-iid branch.  Every optimal fixed-`k` sequence for that
same returned model converges to the requested `gamma`-homogeneous profile.
-/
theorem paper_corollary1_any_nonnegative_gamma_source_iid_model_sequence_formula
    {T : ℕ} [NeZero T] {k : ℕ}
    (likelihood : ItemType T → ℝ) (gamma : ℝ)
    (hk_pos : 0 < k) (hgamma_nonneg : 0 ≤ gamma)
    (hlike_pos : ∀ t : ItemType T, 0 < likelihood t) :
    ∃ (D : MeasureTheory.Measure ℝ) (M : ConsumptionModel T),
      MeasureTheory.IsProbabilityMeasure D ∧
      Corollary1SourceIidFamily likelihood gamma k D M ∧
        ∀ seq : OptimalAllocationSequence (fun _ => M),
          ∀ t : ItemType T,
            Filter.Tendsto
              (fun N => CountAllocation.representation (seq.allocation N) t)
              Filter.atTop
              (nhds
                ((likelihood t) ^ gamma /
                  ∑ i : ItemType T, (likelihood i) ^ gamma)) := by
  rcases paper_corollary1_gamma_parameter_cases gamma hgamma_nonneg with
    hgamma_zero | hrest
  · subst gamma
    refine
      ⟨MeasureTheory.Measure.map AppliedModelingLib.Probability.binaryRatingScore
          (AppliedModelingLib.Probability.realBernoulliPMF (1 / 2)
            (by norm_num) (by norm_num)).toMeasure,
        corollary1FiniteTwoPointBernoulliSourceIidModel likelihood k (1 / 2)
          (by norm_num) (by norm_num), ?_, ?_, ?_⟩
    · exact MeasureTheory.Measure.isProbabilityMeasure_map
        (measurable_of_finite _).aemeasurable
    · exact
      Corollary1SourceIidFamily.finiteTwoPointBernoulli (k := k) (1 / 2)
          (by norm_num) (by norm_num) rfl
    · intro seq t
      exact
        paper_corollary1_finite_discrete_bernoulli_top_k_gamma_zero_sequence_formula
          likelihood (1 / 2) (by norm_num) (by norm_num) hk_pos hlike_pos seq t
  · rcases hrest with hbounded | hrest
    · rcases hbounded with ⟨beta, hbeta_pos, hbeta_eq⟩
      refine
        ⟨boundedReflectedPowerSourceMeasure beta,
          boundedReflectedPowerSourceIidOrderStatisticConsumptionModel
            likelihood k beta, by infer_instance, ?_, ?_⟩
      · exact
          Corollary1SourceIidFamily.boundedReflectedPowerOrderStatistic
            (k := k) beta hbeta_pos hk_pos hbeta_eq
      · intro seq t
        have hformula :=
          paper_theorem1_ii_bounded_reflected_power_source_iid_order_statistic_sequence_formula
            likelihood hbeta_pos hk_pos hlike_pos seq t
        simpa [hbeta_eq] using hformula
    · rcases hrest with hgamma_one | hpareto
      · subst gamma
        refine
          ⟨(exponentialDistributionModel 1 (by norm_num)).measure,
            (exponentialTopKOrderStatisticOracle T 1 k).toConsumptionModel
              likelihood k,
            (exponentialDistributionModel 1 (by norm_num)).isProbabilityMeasure_measure,
            ?_, ?_⟩
        · exact
          Corollary1SourceIidFamily.exponentialOrderStatistic
              (k := k) 1 (by norm_num) hk_pos rfl
        · intro seq t
          exact
            paper_corollary1_exponential_top_k_order_statistic_gamma_one_sequence_formula
              likelihood 1 k (by norm_num) hk_pos hlike_pos seq t
      · rcases hpareto with ⟨alpha, halpha_gt_one, halpha_eq⟩
        refine ⟨ProbabilityTheory.paretoMeasure 1 alpha,
          paretoIidOrderStatisticConsumptionModel likelihood k alpha,
          ProbabilityTheory.isProbabilityMeasure_paretoMeasure (by norm_num)
            (lt_trans zero_lt_one halpha_gt_one), ?_, ?_⟩
        · exact
          Corollary1SourceIidFamily.paretoOrderStatistic
              (k := k) alpha halpha_gt_one hk_pos halpha_eq
        · intro seq t
          have hformula :=
            paper_theorem1_iv_pareto_iid_order_statistic_sequence_formula
              likelihood halpha_gt_one hk_pos hlike_pos seq t
          simpa [halpha_eq] using hformula

end PRPKG24AccuracyDiversity

import AppliedModelingLib.Foundations.Math.Asymptotics
import AppliedModelingLib.Foundations.Math.AbsolutelyContinuous
import AppliedModelingLib.Foundations.Math.FiniteSum
import AppliedModelingLib.Foundations.Probability.FiniteExpectation
import AppliedModelingLib.Foundations.Probability.RealDistribution
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Moments.Variance
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic

open Filter Topology MeasureTheory
open scoped BigOperators ProbabilityTheory

namespace AppliedModelingLib
namespace Probability

noncomputable section

/-!
# Order-Statistic Certificate Interfaces

Reusable scaffolding for papers whose probability layer supplies expected
top-`k` values or marginal order-statistic asymptotics.  This file does not
prove distribution-specific bounded/exponential/Pareto integral asymptotics;
it gives those analytic results a stable target interface.

## Main declarations

- `TopKExpectationOracle`
- `topKCandidateSets`
- `topKSumOn`
- `topKSumOn_comp_equiv`
- `topKSumOn_eq_card_mul_of_top_witness`
- `hasKTopValues`
- `topValueCount`
- `TopKExpectationOracle.marginalTopK`
- `ascendingOrderStatistic`
- `ascendingOrderStatistic_measurable`
- `ascendingOrderStatistic_integrable_of_ae_bounds`
- `upperOrderStatistic_eq_endpoint_sub_reflectedAscending`
- `iidMaximumCdf`
- `iidMaximumCdf_eq_lowerCDFMass_pow`
- `sampleTopKEndpointLoss_eq_reflectedBottomKSum`
- `sampleTopKSum_integrable_of_ae_bounds`
- `sampleTopKEndpointLoss_integrable_of_ae_bounds`
- `reflectedBottomKSum_integrable_of_ae_bounds`
- `ascendingOrderStatistic_eq_integral_rank_count_indicator`
- `reflectedBottomKSum_eq_integral_rank_count_indicator`
- `reflectedBottomKRankCountLayer_measurable_prod`
- `reflectedBottomKRankCountLayer_integrable_prod_of_ae_bounds`
- `expectedSampleTopKSum_eq_sum_expectedUpperOrderStatistic`
- `expectedReflectedBottomKSum_eq_sum_reflectedAscendingOrderStatistic`
- `expectedReflectedBottomKSum_eq_sum_reflectedAscendingOrderStatistic_of_le`
- `expectedSampleTopKEndpointLoss_eq_expectedReflectedBottomKSum`
- `orderStatisticTopKSumFromMean`
- `sampleOrderStatisticValue`
- `expectedSampleOrderStatisticMean`
- `expectedOrderStatisticMeanSeq`
- `topKEndpointLoss_eq_reflectedTopKMeanSum`
- `TopKExpectationOracle.ScaledMarginalLimitCertificate`
- `TopKExpectationOracle.ScaledMarginalLimitCertificate.eventually_marginal_sandwich`
- `TopKExpectationOracle.ScaledMarginalLimitCertificate.marginal_lt_of_scaled_gap`
- `TopKExpectationOracle.ScaledMarginalLimitCertificate.eventually_same_count_marginal_lt_of_weight_gap`
- `OrderStatisticScaledMarginalCertificate`
-/

/-!
## Finite top-`k` maximization

The at-most-`k` convention is useful for finite-sample revenue/value proofs:
with nonnegative values, it agrees with the usual top-`k` sum, while keeping
the empty candidate available for nonnegativity and avoiding edge cases when
the finite index type has fewer than `k` elements.
-/

/-- Candidate index sets for the sum of the best at-most-`k` values. -/
def topKCandidateSets (ι : Type*) [Fintype ι] [DecidableEq ι] (k : ℕ) :
    Finset (Finset ι) := (Finset.univ : Finset ι).powerset.filter (fun s => s.card ≤ k)

theorem topKCandidateSets_nonempty
    (ι : Type*) [Fintype ι] [DecidableEq ι] (k : ℕ) :
    (topKCandidateSets ι k).Nonempty := by
  classical
  refine ⟨∅, ?_⟩
  simp [topKCandidateSets]

/-- Sum of the best at-most-`k` values over a finite sample. -/
def topKSumOn {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (v : ι → ℝ) : ℝ :=
  (topKCandidateSets ι k).sup' (topKCandidateSets_nonempty ι k)
    (fun s => ∑ i ∈ s, v i)

/-- A concrete candidate set is bounded by the top-`k` value. -/
theorem sum_le_topKSumOn {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (v : ι → ℝ) (s : Finset ι) (hs_card : s.card ≤ k) :
    (∑ i ∈ s, v i) ≤ topKSumOn k v := by
  classical
  unfold topKSumOn
  refine Finset.le_sup' (fun s => ∑ i ∈ s, v i) ?_
  simp [topKCandidateSets, hs_card]

/-- The empty candidate makes the at-most-`k` top value nonnegative. -/
theorem topKSumOn_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (v : ι → ℝ) :
    0 ≤ topKSumOn k v := by
  classical
  simpa using sum_le_topKSumOn (ι := ι) k v ∅ (Nat.zero_le k)

theorem topKSumOn_measurable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) :
    Measurable (fun sample : ι → ℝ => topKSumOn k sample) := by
  classical
  unfold topKSumOn
  let F : Finset ι → (ι → ℝ) → ℝ :=
    fun s sample => ∑ i ∈ s, sample i
  have hF : Measurable
      ((topKCandidateSets ι k).sup' (topKCandidateSets_nonempty ι k) F) :=
    Finset.measurable_sup'
      (α := ℝ) (δ := ι → ℝ)
      (s := topKCandidateSets ι k)
      (f := F)
      (topKCandidateSets_nonempty ι k)
      (by
        intro s _hs
        exact Finset.measurable_sum s
          (fun i _hi => measurable_pi_apply i))
  convert hF using 1
  ext sample
  simp [F]

/-- Reindexing the finite sample does not change its top-`k` sum. -/
theorem topKSumOn_comp_equiv {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (k : ℕ) (v : κ → ℝ) :
    topKSumOn k (fun i : ι => v (e i)) = topKSumOn k v := by
  classical
  have hle :
      topKSumOn k (fun i : ι => v (e i)) ≤ topKSumOn k v := by
    unfold topKSumOn
    refine Finset.sup'_le (topKCandidateSets_nonempty ι k)
      (fun s => ∑ i ∈ s, v (e i)) ?_
    intro s hs
    have hs_card : s.card ≤ k := by
      simpa [topKCandidateSets] using hs
    let t : Finset κ := s.map e.toEmbedding
    have ht_card : t.card ≤ k := by
      have hcard : t.card = s.card := by
        simp [t]
      simpa [hcard] using hs_card
    have hsum :
        (∑ i ∈ s, v (e i)) = ∑ x ∈ t, v x := by
      dsimp [t]
      symm
      simpa using
        (Finset.sum_map (s := s) (f := e.toEmbedding) (g := v))
    change (∑ i ∈ s, v (e i)) ≤ topKSumOn k v
    simpa [hsum] using sum_le_topKSumOn (ι := κ) k v t ht_card
  have hge :
      topKSumOn k v ≤ topKSumOn k (fun i : ι => v (e i)) := by
    unfold topKSumOn
    refine Finset.sup'_le (topKCandidateSets_nonempty κ k)
      (fun s => ∑ i ∈ s, v i) ?_
    intro s hs
    have hs_card : s.card ≤ k := by
      simpa [topKCandidateSets] using hs
    let t : Finset ι := s.map e.symm.toEmbedding
    have ht_card : t.card ≤ k := by
      have hcard : t.card = s.card := by
        simp [t]
      simpa [hcard] using hs_card
    have hsum :
        (∑ x ∈ s, v x) = ∑ i ∈ t, v (e i) := by
      dsimp [t]
      symm
      simpa using
        (Finset.sum_map (s := s) (f := e.symm.toEmbedding)
          (g := fun i : ι => v (e i)))
    change (∑ x ∈ s, v x) ≤ topKSumOn k (fun i : ι => v (e i))
    simpa [hsum] using
      sum_le_topKSumOn (ι := ι) k (fun i : ι => v (e i)) t ht_card
  exact le_antisymm hle hge

/-- If every sample value is at most `C`, then the top-`k` sum is at most `k*C`. -/
theorem topKSumOn_le_card_mul_of_forall_le {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (k : ℕ) (v : ι → ℝ) {C : ℝ}
    (hC_nonneg : 0 ≤ C) (h_le : ∀ i, v i ≤ C) :
    topKSumOn k v ≤ (k : ℝ) * C := by
  classical
  unfold topKSumOn
  refine Finset.sup'_le (topKCandidateSets_nonempty ι k)
    (fun s => ∑ i ∈ s, v i) ?_
  intro s hs
  have hs_card : s.card ≤ k := by
    simpa [topKCandidateSets] using hs
  have hsum_le : (∑ i ∈ s, v i) ≤ (s.card : ℝ) * C :=
    AppliedModelingLib.FiniteSum.finset_sum_le_card_mul_of_forall_le
      s v C (fun i _ => h_le i)
  have hcard_le : (s.card : ℝ) * C ≤ (k : ℝ) * C :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hs_card) hC_nonneg
  exact le_trans hsum_le hcard_le

/--
If every coordinate is almost surely in `[0, M]`, then the max-over-subsets
top-`k` sum is integrable.
-/
theorem topKSumOn_integrable_of_ae_nonneg_bounds {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (M : ℝ) (μ : MeasureTheory.Measure (ι → ℝ))
    [MeasureTheory.IsFiniteMeasure μ] (k : ℕ)
    (hM_nonneg : 0 ≤ M)
    (h_bounds :
      ∀ᵐ sample ∂μ, ∀ i : ι, 0 ≤ sample i ∧ sample i ≤ M) :
    MeasureTheory.Integrable (fun sample : ι → ℝ => topKSumOn k sample) μ := by
  refine MeasureTheory.Integrable.of_mem_Icc 0 ((k : ℝ) * M)
    (topKSumOn_measurable k).aemeasurable ?_
  filter_upwards [h_bounds] with sample hsample
  exact ⟨
    topKSumOn_nonneg k sample,
    topKSumOn_le_card_mul_of_forall_le k sample hM_nonneg
      (fun i => (hsample i).2)⟩

/-- A witnessed set of `k` top values pins the top-`k` sum to `k * xTop`. -/
theorem topKSumOn_eq_card_mul_of_top_witness {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (k : ℕ) (v : ι → ℝ) {xTop : ℝ}
    (hxTop_nonneg : 0 ≤ xTop) (h_le : ∀ i, v i ≤ xTop)
    (sTop : Finset ι) (hsTop_card : sTop.card = k)
    (hsTop_value : ∀ i ∈ sTop, v i = xTop) :
    topKSumOn k v = (k : ℝ) * xTop := by
  classical
  apply le_antisymm
  · exact topKSumOn_le_card_mul_of_forall_le k v hxTop_nonneg h_le
  · have hsum :
        (∑ i ∈ sTop, v i) = (k : ℝ) * xTop := by
      calc
        (∑ i ∈ sTop, v i) = ∑ i ∈ sTop, xTop := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact hsTop_value i hi
        _ = (k : ℝ) * xTop := by
          simp [hsTop_card]
    simpa [hsum] using
      sum_le_topKSumOn (ι := ι) k v sTop (by rw [hsTop_card])

/-- The sample has at least `k` entries equal to the top support value. -/
def hasKTopValues {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (xTop : ℝ) (v : ι → ℝ) : Prop :=
  ∃ s : Finset ι, s.card = k ∧ ∀ i ∈ s, v i = xTop

/-- Number of entries equal to the top support value. -/
def topValueCount {ι : Type*} [Fintype ι]
    (xTop : ℝ) (v : ι → ℝ) : ℕ :=
  ((Finset.univ : Finset ι).filter (fun i => v i = xTop)).card

/-- Having `k` top values is the same as the top-value count being at least `k`. -/
theorem hasKTopValues_iff_le_topValueCount {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (k : ℕ) (xTop : ℝ) (v : ι → ℝ) :
    hasKTopValues k xTop v ↔ k ≤ topValueCount xTop v := by
  classical
  unfold hasKTopValues topValueCount
  constructor
  · rintro ⟨s, hs_card, hs_value⟩
    have hsub : s ⊆ (Finset.univ : Finset ι).filter (fun i => v i = xTop) := by
      intro i hi
      simp [hs_value i hi]
    have hcard := Finset.card_le_card hsub
    simpa [hs_card] using hcard
  · intro hcount
    obtain ⟨s, hs_sub, hs_card⟩ :=
      Finset.exists_subset_card_eq
        (s := (Finset.univ : Finset ι).filter (fun i => v i = xTop))
        hcount
    refine ⟨s, hs_card, ?_⟩
    intro i hi
    have hi_filter := hs_sub hi
    simpa using hi_filter

/-- Add one new value to a finite sample. -/
def extendSample {ι : Type*} (v : ι → ℝ) (newValue : ℝ) : Option ι → ℝ
  | none => newValue
  | some i => v i

/--
Measurable equivalence between an option-extended real sample and an old
sample together with one new draw.
-/
def optionSampleMeasurableEquivProd (ι : Type*) :
    (Option ι → ℝ) ≃ᵐ (ι → ℝ) × ℝ where
  toFun sample := (fun i => sample (some i), sample none)
  invFun pair := extendSample pair.1 pair.2
  left_inv sample := by
    funext x
    cases x <;> rfl
  right_inv pair := by
    ext i
    · rfl
    · rfl
  measurable_toFun := by
    exact
      (measurable_pi_iff.mpr
        (fun i => measurable_pi_apply (some i))).prodMk
        (measurable_pi_apply none)
  measurable_invFun := by
    exact measurable_pi_iff.mpr (by
      intro x
      cases x with
      | none =>
          exact
            (measurable_snd :
              Measurable (fun z : (ι → ℝ) × ℝ => z.2))
      | some i =>
          exact (measurable_pi_apply i).comp
            (measurable_fst :
              Measurable (fun z : (ι → ℝ) × ℝ => z.1)))

theorem pi_map_optionSampleMeasurableEquivProd_symm
    {ι : Type*} [Fintype ι]
    (μ : MeasureTheory.Measure ℝ) [MeasureTheory.SigmaFinite μ] :
    (((MeasureTheory.Measure.pi (fun _ : ι => μ)).prod μ).map
        (optionSampleMeasurableEquivProd ι).symm) =
      MeasureTheory.Measure.pi (fun _ : Option ι => μ) := by
  refine MeasureTheory.Measure.pi_eq (fun s _ ↦ ?_) |>.symm
  let e_meas : ((ι → ℝ) × ℝ) ≃ᵐ (Option ι → ℝ) :=
    (optionSampleMeasurableEquivProd ι).symm
  have me := MeasurableEquiv.measurableEmbedding e_meas
  have hpre :
      e_meas ⁻¹' Set.pi Set.univ s =
        (Set.pi Set.univ (fun i : ι => s (some i))) ×ˢ (s none) := by
    ext x
    constructor
    · intro hx
      refine ⟨?_, ?_⟩
      · intro i _hi
        exact hx (some i) (by simp)
      · exact hx none (by simp)
    · intro hx i _hi
      cases i with
      | none => exact hx.2
      | some i => exact hx.1 i (by simp)
  rw [me.map_apply, hpre, MeasureTheory.Measure.prod_prod,
    MeasureTheory.Measure.pi_pi, Fintype.prod_option]
  rw [mul_comm]

/-- Adding one more value cannot reduce the at-most-`k` top value. -/
theorem topKSumOn_le_extend {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (v : ι → ℝ) (newValue : ℝ) :
    topKSumOn k v ≤ topKSumOn k (extendSample v newValue) := by
  classical
  unfold topKSumOn
  refine Finset.sup'_le (topKCandidateSets_nonempty ι k)
    (fun s => ∑ i ∈ s, v i) ?_
  intro s hs
  have hs_card : s.card ≤ k := by
    simpa [topKCandidateSets] using hs
  let sExt : Finset (Option ι) := s.image (fun i => some i)
  have hsExt_card : sExt.card ≤ k := by
    have hcard :
        sExt.card = s.card := by
      simpa [sExt] using
        (Finset.card_image_of_injective s
          (fun _ _ h => Option.some.inj h))
    simpa [hcard] using hs_card
  have hsum :
      (∑ x ∈ sExt, extendSample v newValue x) = ∑ i ∈ s, v i := by
    dsimp [sExt]
    rw [Finset.sum_image (by
      intro a _ b _ h
      exact Option.some.inj h)]
    simp [extendSample]
  have hcandidate :=
    sum_le_topKSumOn (ι := Option ι) k (extendSample v newValue)
      sExt hsExt_card
  have hcandidate' :
      (∑ i ∈ s, v i) ≤ topKSumOn k (extendSample v newValue) := by
    simpa [hsum] using hcandidate
  simpa [topKSumOn] using hcandidate'

/--
If the old sample has fewer than `k` coordinates, a maximizing old candidate
set can be augmented by the new coordinate. Thus the top-`k` value after the
extension is at least the old top-`k` value plus the new value.
-/
theorem topKSumOn_add_newValue_le_extend_of_card_lt {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (k : ℕ) (v : ι → ℝ) (newValue : ℝ)
    (hcard_lt : Fintype.card ι < k) :
    topKSumOn k v + newValue ≤
      topKSumOn k (extendSample v newValue) := by
  classical
  obtain ⟨s, hs_mem, hs_eq⟩ :=
    Finset.exists_mem_eq_sup'
      (s := topKCandidateSets ι k)
      (H := topKCandidateSets_nonempty ι k)
      (f := fun s => ∑ i ∈ s, v i)
  have hs_card_lt : s.card < k :=
    lt_of_le_of_lt (Finset.card_le_univ s) hcard_lt
  let sExt : Finset (Option ι) := insert none (s.image (fun i => some i))
  have hnone_not_mem : none ∉ s.image (fun i : ι => some i) := by
    simp
  have hcard_image :
      (s.image (fun i : ι => some i)).card = s.card :=
    Finset.card_image_of_injective s (fun _ _ h => Option.some.inj h)
  have hsExt_card : sExt.card ≤ k := by
    have hcard : sExt.card = s.card + 1 := by
      simp [sExt, hnone_not_mem, hcard_image]
    omega
  have hold_eq : topKSumOn k v = ∑ i ∈ s, v i := by
    unfold topKSumOn
    exact hs_eq
  have hsum_image :
      (∑ x ∈ s.image (fun i : ι => some i),
          extendSample v newValue x) =
        ∑ i ∈ s, v i := by
    rw [Finset.sum_image]
    · simp [extendSample]
    · intro a _ b _ h
      exact Option.some.inj h
  have hsum_ext :
      (∑ x ∈ sExt, extendSample v newValue x) =
        (∑ i ∈ s, v i) + newValue := by
    simp [sExt, hnone_not_mem, extendSample, add_comm]
  calc
    topKSumOn k v + newValue =
        (∑ i ∈ s, v i) + newValue := by
          rw [hold_eq]
    _ = ∑ x ∈ sExt, extendSample v newValue x := hsum_ext.symm
    _ ≤ topKSumOn k (extendSample v newValue) :=
        sum_le_topKSumOn (ι := Option ι) k
          (extendSample v newValue) sExt hsExt_card

/--
When the old sample has fewer than `k` coordinates, the marginal gain from
adding a new value is at least that value.
-/
theorem newValue_le_topKSumOn_extend_sub_of_card_lt {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (k : ℕ) (v : ι → ℝ) (newValue : ℝ)
    (hcard_lt : Fintype.card ι < k) :
    newValue ≤ topKSumOn k (extendSample v newValue) - topKSumOn k v := by
  have h :=
    topKSumOn_add_newValue_le_extend_of_card_lt
      (ι := ι) k v newValue hcard_lt
  linarith

/--
Adding a new coordinate to a maximizer for the old top-`k - 1` problem gives
a candidate for the extended top-`k` problem.
-/
theorem topKSumOn_pred_add_newValue_le_extend {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (k : ℕ) (v : ι → ℝ) (newValue : ℝ)
    (hk_pos : 0 < k) :
    topKSumOn (k - 1) v + newValue ≤
      topKSumOn k (extendSample v newValue) := by
  classical
  obtain ⟨s, hs_mem, hs_eq⟩ :=
    Finset.exists_mem_eq_sup'
      (s := topKCandidateSets ι (k - 1))
      (H := topKCandidateSets_nonempty ι (k - 1))
      (f := fun s => ∑ i ∈ s, v i)
  have hs_card : s.card ≤ k - 1 := by
    simpa [topKCandidateSets] using hs_mem
  let sExt : Finset (Option ι) := insert none (s.image (fun i => some i))
  have hnone_not_mem : none ∉ s.image (fun i : ι => some i) := by
    simp
  have hcard_image :
      (s.image (fun i : ι => some i)).card = s.card :=
    Finset.card_image_of_injective s (fun _ _ h => Option.some.inj h)
  have hsExt_card : sExt.card ≤ k := by
    have hcard : sExt.card = s.card + 1 := by
      simp [sExt, hnone_not_mem, hcard_image]
    omega
  have hold_eq : topKSumOn (k - 1) v = ∑ i ∈ s, v i := by
    unfold topKSumOn
    exact hs_eq
  have hsum_ext :
      (∑ x ∈ sExt, extendSample v newValue x) =
        (∑ i ∈ s, v i) + newValue := by
    simp [sExt, hnone_not_mem, extendSample, add_comm]
  calc
    topKSumOn (k - 1) v + newValue =
        (∑ i ∈ s, v i) + newValue := by rw [hold_eq]
    _ = ∑ x ∈ sExt, extendSample v newValue x := hsum_ext.symm
    _ ≤ topKSumOn k (extendSample v newValue) :=
        sum_le_topKSumOn (ι := Option ι) k
          (extendSample v newValue) sExt hsExt_card

/--
If every old coordinate is at most `bound`, then the old top-`k` sum is at
most the old top-`k - 1` sum plus `bound`.
-/
theorem topKSumOn_le_pred_add_bound {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (k : ℕ) (v : ι → ℝ) {bound : ℝ}
    (hk_pos : 0 < k) (hbound_nonneg : 0 ≤ bound)
    (h_le : ∀ i, v i ≤ bound) :
    topKSumOn k v ≤ topKSumOn (k - 1) v + bound := by
  classical
  unfold topKSumOn
  refine Finset.sup'_le (topKCandidateSets_nonempty ι k)
    (fun s => ∑ i ∈ s, v i) ?_
  intro s hs
  have hs_card : s.card ≤ k := by
    simpa [topKCandidateSets] using hs
  by_cases hsmall : s.card ≤ k - 1
  · have hcandidate :
        (∑ i ∈ s, v i) ≤
          Finset.sup' (topKCandidateSets ι (k - 1))
            (topKCandidateSets_nonempty ι (k - 1))
            (fun s => ∑ i ∈ s, v i) :=
      Finset.le_sup' (fun s => ∑ i ∈ s, v i)
        (by simpa [topKCandidateSets] using hsmall)
    have hnonneg :
        0 ≤
          Finset.sup' (topKCandidateSets ι (k - 1))
            (topKCandidateSets_nonempty ι (k - 1))
            (fun s => ∑ i ∈ s, v i) := by
      change 0 ≤ topKSumOn (k - 1) v
      exact topKSumOn_nonneg (k - 1) v
    linarith
  · have hcard_eq : s.card = k := by omega
    have hs_nonempty : s.Nonempty := by
      exact Finset.card_pos.mp (by omega)
    rcases hs_nonempty with ⟨i, hi⟩
    have herase_card : (s.erase i).card ≤ k - 1 := by
      exact le_of_eq (by rw [Finset.card_erase_of_mem hi, hcard_eq])
    have herase_candidate :
        (∑ j ∈ s.erase i, v j) ≤
          Finset.sup' (topKCandidateSets ι (k - 1))
            (topKCandidateSets_nonempty ι (k - 1))
            (fun s => ∑ i ∈ s, v i) :=
      Finset.le_sup' (fun s => ∑ i ∈ s, v i)
        (by simpa [topKCandidateSets] using herase_card)
    have hsum :
        (∑ j ∈ s, v j) = (∑ j ∈ s.erase i, v j) + v i := by
      rw [← Finset.sum_erase_add _ _ hi]
    calc
      (∑ j ∈ s, v j) =
          (∑ j ∈ s.erase i, v j) + v i := hsum
      _ ≤
          Finset.sup' (topKCandidateSets ι (k - 1))
            (topKCandidateSets_nonempty ι (k - 1))
            (fun s => ∑ i ∈ s, v i) + bound :=
          add_le_add herase_candidate (h_le i)

/--
If all old values are at most `bound` and the new value is above `bound`,
then the top-`k` increment is at least the gap `newValue - bound`.
-/
theorem topKSumOn_extend_sub_ge_newValue_sub_bound_of_forall_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (v : ι → ℝ) {bound newValue : ℝ}
    (hk_pos : 0 < k) (hbound_nonneg : 0 ≤ bound)
    (h_le : ∀ i, v i ≤ bound) :
    newValue - bound ≤
      topKSumOn k (extendSample v newValue) - topKSumOn k v := by
  have hnew :=
    topKSumOn_pred_add_newValue_le_extend k v newValue hk_pos
  have hold :=
    topKSumOn_le_pred_add_bound k v hk_pos hbound_nonneg h_le
  linarith

theorem hasKTopValues_extend_of_hasKTopValues {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    {k : ℕ} {xTop : ℝ} {v : ι → ℝ} {newValue : ℝ}
    (h : hasKTopValues k xTop v) :
    hasKTopValues k xTop (extendSample v newValue) := by
  classical
  rcases h with ⟨s, hs_card, hs_value⟩
  refine ⟨s.image (fun i => some i), ?_, ?_⟩
  · simpa [hs_card] using
      (Finset.card_image_of_injective s
        (fun _ _ h => Option.some.inj h))
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    exact hs_value i hi

/--
If a sample already has `k` top-support values, adding one more bounded item
leaves the top-`k` sum unchanged.
-/
theorem topKSumOn_extend_eq_of_hasKTopValues {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (k : ℕ) (v : ι → ℝ) {xTop newValue : ℝ}
    (hxTop_nonneg : 0 ≤ xTop)
    (h_le : ∀ i, v i ≤ xTop) (hnew_le : newValue ≤ xTop)
    (hTop : hasKTopValues k xTop v) :
    topKSumOn k (extendSample v newValue) = topKSumOn k v := by
  classical
  rcases hTop with ⟨s, hs_card, hs_value⟩
  have hold :
      topKSumOn k v = (k : ℝ) * xTop :=
    topKSumOn_eq_card_mul_of_top_witness k v hxTop_nonneg h_le
      s hs_card hs_value
  have hext_le : ∀ x : Option ι, extendSample v newValue x ≤ xTop := by
    intro x
    cases x with
    | none => exact hnew_le
    | some i => exact h_le i
  have hextTop :
      hasKTopValues k xTop (extendSample v newValue) :=
    hasKTopValues_extend_of_hasKTopValues
      (v := v) (newValue := newValue) ⟨s, hs_card, hs_value⟩
  rcases hextTop with ⟨sExt, hsExt_card, hsExt_value⟩
  have hnew :
      topKSumOn k (extendSample v newValue) = (k : ℝ) * xTop :=
    topKSumOn_eq_card_mul_of_top_witness k (extendSample v newValue)
      hxTop_nonneg hext_le sExt hsExt_card hsExt_value
  rw [hnew, hold]

/--
Pointwise upper marginal bound for the finite top-mass failure event:
outside failure, the marginal is zero; on failure, it is at most `k * xTop`.
-/
theorem topKSumOn_extend_sub_le_top_failure_indicator {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (k : ℕ) (v : ι → ℝ) {xTop newValue : ℝ}
    [Decidable (hasKTopValues k xTop v)]
    (hxTop_nonneg : 0 ≤ xTop)
    (h_le : ∀ i, v i ≤ xTop) (hnew_le : newValue ≤ xTop) :
    topKSumOn k (extendSample v newValue) - topKSumOn k v ≤
      (k : ℝ) * xTop *
        (if hasKTopValues k xTop v then (0 : ℝ) else 1) := by
  classical
  by_cases hTop : hasKTopValues k xTop v
  · have heq :=
      topKSumOn_extend_eq_of_hasKTopValues k v hxTop_nonneg h_le
        hnew_le hTop
    simp [hTop, heq]
  · have hext_le : ∀ x : Option ι, extendSample v newValue x ≤ xTop := by
      intro x
      cases x with
      | none => exact hnew_le
      | some i => exact h_le i
    have hupper :
        topKSumOn k (extendSample v newValue) ≤ (k : ℝ) * xTop :=
      topKSumOn_le_card_mul_of_forall_le k (extendSample v newValue)
        hxTop_nonneg hext_le
    have hold_nonneg : 0 ≤ topKSumOn k v := topKSumOn_nonneg k v
    have hmul_nonneg : 0 ≤ (k : ℝ) * xTop :=
      mul_nonneg (Nat.cast_nonneg k) hxTop_nonneg
    simp [hTop]
    linarith

/--
The old sample has exactly `k-1` top-support values and every other value is
at most the second support value.
-/
def hasPredTopValuesWithSecondBound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (xTop xSecond : ℝ) (v : ι → ℝ) : Prop :=
  ∃ topSet : Finset ι,
    topSet.card = k - 1 ∧
      (∀ i ∈ topSet, v i = xTop) ∧
        (∀ i, i ∉ topSet → v i ≤ xSecond)

/--
When every value is either the top value or at most the second support value,
and the second support value is strictly below the top one, the promoting-event
predicate is exactly the statement that the top-value count is `k-1`.
-/
theorem hasPredTopValuesWithSecondBound_iff_topValueCount_eq {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (k : ℕ) {xTop xSecond : ℝ} (v : ι → ℝ)
    (hsecond_lt_top : xSecond < xTop)
    (hvalue_split : ∀ i, v i = xTop ∨ v i ≤ xSecond) :
    hasPredTopValuesWithSecondBound k xTop xSecond v ↔
      topValueCount xTop v = k - 1 := by
  classical
  unfold hasPredTopValuesWithSecondBound topValueCount
  constructor
  · rintro ⟨topSet, htop_card, htop_value, hnontop_le⟩
    have hfilter_eq :
        (Finset.univ : Finset ι).filter (fun i => v i = xTop) = topSet := by
      apply Finset.ext
      intro i
      constructor
      · intro hi
        by_contra hnot
        have hv_eq : v i = xTop := by simpa using hi
        have hv_le : v i ≤ xSecond := hnontop_le i hnot
        linarith
      · intro hi
        simp [htop_value i hi]
    simpa [hfilter_eq, htop_card]
  · intro hcount
    let topSet : Finset ι := (Finset.univ : Finset ι).filter (fun i => v i = xTop)
    refine ⟨topSet, hcount, ?_, ?_⟩
    · intro i hi
      simpa [topSet] using hi
    · intro i hi
      rcases hvalue_split i with hv_eq | hv_le
      · have hi_top : i ∈ topSet := by
          simp [topSet, hv_eq]
        exact False.elim (hi hi_top)
      · exact hv_le

/-- Arithmetic bound behind the `k-1`-top promoting event. -/
theorem top_second_count_bound
    {k b c : ℕ} {xTop xSecond : ℝ}
    (hk_pos : 0 < k)
    (hb : b ≤ k - 1) (hbc : b + c ≤ k)
    (hxSecond_nonneg : 0 ≤ xSecond)
    (hsecond_le_top : xSecond ≤ xTop) :
    (b : ℝ) * xTop + (c : ℝ) * xSecond ≤
      ((k - 1 : ℕ) : ℝ) * xTop + xSecond := by
  have hk_pred_cast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    norm_num [Nat.cast_sub (Nat.succ_le_of_lt hk_pos)]
  have hbR : (b : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast hb
  have hbcR : (b : ℝ) + (c : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast hbc
  have hcR : (c : ℝ) ≤ (k : ℝ) - (b : ℝ) := by
    linarith
  have hfirst :
      (b : ℝ) * xTop + (c : ℝ) * xSecond ≤
        (b : ℝ) * xTop + ((k : ℝ) - (b : ℝ)) * xSecond := by
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left
        (mul_le_mul_of_nonneg_right hcR hxSecond_nonneg)
        ((b : ℝ) * xTop)
  have hprod_nonneg :
      0 ≤ (((k - 1 : ℕ) : ℝ) - (b : ℝ)) * (xTop - xSecond) :=
    mul_nonneg (sub_nonneg.mpr hbR) (sub_nonneg.mpr hsecond_le_top)
  have halg :
      (b : ℝ) * xTop + ((k : ℝ) - (b : ℝ)) * xSecond +
          (((k - 1 : ℕ) : ℝ) - (b : ℝ)) * (xTop - xSecond) =
        ((k - 1 : ℕ) : ℝ) * xTop + xSecond := by
    rw [hk_pred_cast]
    ring
  linarith

/--
If a candidate set contains at most `k` indices, while the whole sample has
exactly `k-1` top-support values and every other value is at most `xSecond`,
then that candidate's sum is at most `(k-1) * xTop + xSecond`.
-/
theorem finset_sum_le_pred_top_add_second {ι : Type*}
    [DecidableEq ι]
    {k : ℕ} {v : ι → ℝ} {xTop xSecond : ℝ}
    (hk_pos : 0 < k)
    (hxSecond_nonneg : 0 ≤ xSecond)
    (hsecond_le_top : xSecond ≤ xTop)
    (topSet s : Finset ι)
    (htop_card : topSet.card = k - 1)
    (hs_card : s.card ≤ k)
    (htop_value : ∀ i ∈ topSet, v i = xTop)
    (hnontop_le : ∀ i, i ∉ topSet → v i ≤ xSecond) :
    (∑ i ∈ s, v i) ≤ ((k - 1 : ℕ) : ℝ) * xTop + xSecond := by
  classical
  let sTop := s.filter (fun i => i ∈ topSet)
  let sNonTop := s.filter (fun i => i ∉ topSet)
  have hsplit :
      (∑ i ∈ s, v i) =
        (∑ i ∈ sTop, v i) + (∑ i ∈ sNonTop, v i) := by
    simp [sTop, sNonTop, Finset.sum_filter_add_sum_filter_not]
  have htop_sum :
      (∑ i ∈ sTop, v i) ≤ (sTop.card : ℝ) * xTop :=
    AppliedModelingLib.FiniteSum.finset_sum_le_card_mul_of_forall_le sTop v xTop (by
      intro i hi
      have hitop : i ∈ topSet := by
        have hi' : i ∈ s ∧ i ∈ topSet := by
          simpa [sTop] using hi
        exact hi'.2
      exact (htop_value i hitop).le)
  have hnontop_sum :
      (∑ i ∈ sNonTop, v i) ≤ (sNonTop.card : ℝ) * xSecond :=
    AppliedModelingLib.FiniteSum.finset_sum_le_card_mul_of_forall_le sNonTop v xSecond (by
      intro i hi
      have hinot : i ∉ topSet := by
        have hi' : i ∈ s ∧ i ∉ topSet := by
          simpa [sNonTop] using hi
        exact hi'.2
      exact hnontop_le i hinot)
  have htop_subset : sTop ⊆ topSet := by
    intro i hi
    have hi' : i ∈ s ∧ i ∈ topSet := by
      simpa [sTop] using hi
    exact hi'.2
  have htop_card_le : sTop.card ≤ k - 1 := by
    rw [← htop_card]
    exact Finset.card_le_card htop_subset
  have hcard_split : sTop.card + sNonTop.card = s.card := by
    simpa [sTop, sNonTop] using
      (Finset.card_filter_add_card_filter_not
        (s := s) (p := fun i => i ∈ topSet))
  have hsum_card_le : sTop.card + sNonTop.card ≤ k := by
    simpa [hcard_split] using hs_card
  calc
    (∑ i ∈ s, v i)
        = (∑ i ∈ sTop, v i) + (∑ i ∈ sNonTop, v i) := hsplit
    _ ≤ (sTop.card : ℝ) * xTop + (sNonTop.card : ℝ) * xSecond :=
          add_le_add htop_sum hnontop_sum
    _ ≤ ((k - 1 : ℕ) : ℝ) * xTop + xSecond :=
          top_second_count_bound hk_pos htop_card_le hsum_card_le
            hxSecond_nonneg hsecond_le_top

/--
Under the exact `k-1` top-count event, the old top-`k` value is at most
`(k-1) * xTop + xSecond`.
-/
theorem topKSumOn_le_pred_top_add_second {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (k : ℕ) (v : ι → ℝ) {xTop xSecond : ℝ}
    (hk_pos : 0 < k)
    (hxSecond_nonneg : 0 ≤ xSecond)
    (hsecond_le_top : xSecond ≤ xTop)
    (topSet : Finset ι)
    (htop_card : topSet.card = k - 1)
    (htop_value : ∀ i ∈ topSet, v i = xTop)
    (hnontop_le : ∀ i, i ∉ topSet → v i ≤ xSecond) :
    topKSumOn k v ≤ ((k - 1 : ℕ) : ℝ) * xTop + xSecond := by
  classical
  unfold topKSumOn
  refine Finset.sup'_le (topKCandidateSets_nonempty ι k)
    (fun s => ∑ i ∈ s, v i) ?_
  intro s hs
  have hs_card : s.card ≤ k := by
    simpa [topKCandidateSets] using hs
  exact finset_sum_le_pred_top_add_second hk_pos hxSecond_nonneg
    hsecond_le_top topSet s htop_card hs_card htop_value hnontop_le

/--
Deterministic promoting-event lower bound. If the old sample has exactly
`k-1` top-support values, all other old values are at most `xSecond`, and the
new draw is top-support, then the top-`k` sum increases by at least the gap
`xTop - xSecond`.
-/
theorem topKSumOn_extend_sub_ge_top_gap_of_pred_top_witness {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (k : ℕ) (v : ι → ℝ) {xTop xSecond newValue : ℝ}
    (hk_pos : 0 < k)
    (hxTop_nonneg : 0 ≤ xTop)
    (hxSecond_nonneg : 0 ≤ xSecond)
    (hsecond_le_top : xSecond ≤ xTop)
    (topSet : Finset ι)
    (htop_card : topSet.card = k - 1)
    (htop_value : ∀ i ∈ topSet, v i = xTop)
    (hnontop_le : ∀ i, i ∉ topSet → v i ≤ xSecond)
    (hnew_eq : newValue = xTop) :
    xTop - xSecond ≤
      topKSumOn k (extendSample v newValue) - topKSumOn k v := by
  classical
  let sExt : Finset (Option ι) := insert none (topSet.image (fun i => some i))
  have hnone_not_mem : none ∉ topSet.image (fun i => some i) := by
    intro hmem
    rcases Finset.mem_image.mp hmem with ⟨i, _hi, hnone⟩
    cases hnone
  have hcard_image :
      (topSet.image (fun i => some i)).card = topSet.card :=
    Finset.card_image_of_injective topSet (fun _ _ h => Option.some.inj h)
  have hsExt_card : sExt.card = k := by
    simp [sExt, hnone_not_mem, hcard_image, htop_card,
      Nat.sub_add_cancel (Nat.succ_le_of_lt hk_pos)]
  have hext_le : ∀ x : Option ι, extendSample v newValue x ≤ xTop := by
    intro x
    cases x with
    | none =>
        simp [extendSample, hnew_eq]
    | some i =>
        by_cases hi : i ∈ topSet
        · exact (htop_value i hi).le
        · exact le_trans (hnontop_le i hi) hsecond_le_top
  have hsExt_value : ∀ x ∈ sExt, extendSample v newValue x = xTop := by
    intro x hx
    simp [sExt] at hx
    rcases hx with hx_none | hx_image
    · subst hx_none
      simp [extendSample, hnew_eq]
    · rcases hx_image with ⟨i, hi, rfl⟩
      exact htop_value i hi
  have hext_eq :
      topKSumOn k (extendSample v newValue) = (k : ℝ) * xTop :=
    topKSumOn_eq_card_mul_of_top_witness k (extendSample v newValue)
      hxTop_nonneg hext_le sExt hsExt_card hsExt_value
  have hold_upper :
      topKSumOn k v ≤ ((k - 1 : ℕ) : ℝ) * xTop + xSecond :=
    topKSumOn_le_pred_top_add_second k v hk_pos hxSecond_nonneg
      hsecond_le_top topSet htop_card htop_value hnontop_le
  have hk_pred_cast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    norm_num [Nat.cast_sub (Nat.succ_le_of_lt hk_pos)]
  rw [hext_eq]
  have hgap_eq :
      (k : ℝ) * xTop - (((k - 1 : ℕ) : ℝ) * xTop + xSecond) =
        xTop - xSecond := by
    rw [hk_pred_cast]
    ring
  calc
    xTop - xSecond =
        (k : ℝ) * xTop - (((k - 1 : ℕ) : ℝ) * xTop + xSecond) :=
          hgap_eq.symm
    _ ≤ (k : ℝ) * xTop - topKSumOn k v := by
          linarith

/--
Pointwise lower marginal bound for the finite top-mass promoting event.
Outside the event the bound is zero; on the event the increase is at least the
top gap `xTop - xSecond`.
-/
theorem topKSumOn_extend_sub_ge_top_gap_promoting_indicator {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (k : ℕ) (v : ι → ℝ) {xTop xSecond newValue : ℝ}
    [Decidable
      (hasPredTopValuesWithSecondBound k xTop xSecond v ∧
        newValue = xTop)]
    (hk_pos : 0 < k)
    (hxTop_nonneg : 0 ≤ xTop)
    (hxSecond_nonneg : 0 ≤ xSecond)
    (hsecond_le_top : xSecond ≤ xTop) :
    (xTop - xSecond) *
        (if hasPredTopValuesWithSecondBound k xTop xSecond v ∧
            newValue = xTop then (1 : ℝ) else 0) ≤
      topKSumOn k (extendSample v newValue) - topKSumOn k v := by
  classical
  by_cases hprom :
      hasPredTopValuesWithSecondBound k xTop xSecond v ∧
        newValue = xTop
  · rcases hprom with ⟨⟨topSet, htop_card, htop_value, hnontop_le⟩,
      hnew_eq⟩
    have hprom_true :
        hasPredTopValuesWithSecondBound k xTop xSecond v ∧
          newValue = xTop :=
      ⟨⟨topSet, htop_card, htop_value, hnontop_le⟩, hnew_eq⟩
    have hlower :
        xTop - xSecond ≤
          topKSumOn k (extendSample v newValue) - topKSumOn k v :=
      topKSumOn_extend_sub_ge_top_gap_of_pred_top_witness
        k v hk_pos hxTop_nonneg hxSecond_nonneg hsecond_le_top topSet
        htop_card htop_value hnontop_le hnew_eq
    simpa [hprom_true] using hlower
  · have hmono := topKSumOn_le_extend k v newValue
    have hdiff_nonneg :
        0 ≤ topKSumOn k (extendSample v newValue) - topKSumOn k v := by
      linarith
    simpa [hprom] using hdiff_nonneg

/-!
## Finite iid top-`k` expectations

These definitions connect the pointwise finite top-`k` API above to the finite
PMF product machinery in `FiniteExpectation`.
-/

/-- Expected top-`k` value for an iid finite sample indexed by `ι`. -/
def iidTopKExpectedOn (ι Ω : Type*) [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [DecidableEq Ω]
    (itemLaw : PMF Ω) (k : ℕ) (value : Ω → ℝ) : ℝ :=
  AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct ι Ω itemLaw)
    (fun sample : ι → Ω => topKSumOn k (fun i => value (sample i)))

/-- Expected top-`k` value for an iid finite sample of natural size `a`. -/
def finiteIidTopKExpected (Ω : Type*) [Fintype Ω] [DecidableEq Ω]
    (itemLaw : PMF Ω) (k : ℕ) (value : Ω → ℝ) (a : ℕ) : ℝ :=
  iidTopKExpectedOn (Fin a) Ω itemLaw k value

/--
Pair-expectation form of the one-draw iid marginal equals the difference
between the option-extended iid expectation and the old iid expectation.
-/
theorem pmfPairExp_topK_extend_sub_eq_iidTopKExpectedOn_option_sub
    {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [DecidableEq Ω]
    (itemLaw : PMF Ω) (k : ℕ) (value : Ω → ℝ) :
    AppliedModelingLib.pmfPairExp (AppliedModelingLib.pmfProduct ι Ω itemLaw) itemLaw
        (fun sample newItem =>
          topKSumOn k
              (extendSample (fun i => value (sample i)) (value newItem)) -
            topKSumOn k (fun i => value (sample i))) =
      iidTopKExpectedOn (Option ι) Ω itemLaw k value -
        iidTopKExpectedOn ι Ω itemLaw k value := by
  classical
  rw [AppliedModelingLib.pmfPairExp_sub]
  have hext :
      AppliedModelingLib.pmfPairExp (AppliedModelingLib.pmfProduct ι Ω itemLaw) itemLaw
          (fun sample newItem =>
            topKSumOn k
              (extendSample (fun i => value (sample i)) (value newItem))) =
        iidTopKExpectedOn (Option ι) Ω itemLaw k value := by
    have hcongr :
        AppliedModelingLib.pmfPairExp (AppliedModelingLib.pmfProduct ι Ω itemLaw) itemLaw
            (fun sample newItem =>
              topKSumOn k
                (extendSample (fun i => value (sample i)) (value newItem))) =
          AppliedModelingLib.pmfPairExp (AppliedModelingLib.pmfProduct ι Ω itemLaw) itemLaw
            (fun sample newItem =>
              topKSumOn k (fun x => value (AppliedModelingLib.extendDraw sample newItem x))) := by
      unfold AppliedModelingLib.pmfPairExp
      refine AppliedModelingLib.pmfExp_congr (AppliedModelingLib.pmfProduct ι Ω itemLaw) ?_
      intro sample
      refine AppliedModelingLib.pmfExp_congr itemLaw ?_
      intro newItem
      change
        topKSumOn k
            (extendSample (fun i => value (sample i)) (value newItem)) =
          topKSumOn k (fun x => value (AppliedModelingLib.extendDraw sample newItem x))
      apply congrArg (topKSumOn k)
      funext x
      cases x <;> rfl
    have hpair :
        AppliedModelingLib.pmfPairExp (AppliedModelingLib.pmfProduct ι Ω itemLaw) itemLaw
            (fun sample newItem =>
              topKSumOn k (fun x => value (AppliedModelingLib.extendDraw sample newItem x))) =
          iidTopKExpectedOn (Option ι) Ω itemLaw k value := by
      unfold iidTopKExpectedOn
      exact
        (AppliedModelingLib.pmfExp_pmfProduct_option_eq_pairExp itemLaw
          (fun sample : Option ι → Ω =>
            topKSumOn k (fun x => value (sample x)))).symm
    exact hcongr.trans hpair
  have hold :
      AppliedModelingLib.pmfPairExp (AppliedModelingLib.pmfProduct ι Ω itemLaw) itemLaw
          (fun sample _newItem =>
            topKSumOn k (fun i => value (sample i))) =
        iidTopKExpectedOn ι Ω itemLaw k value := by
    simp [iidTopKExpectedOn]
  rw [hext, hold]

/-- Reindexing an iid finite sample does not change the expected top-`k` value. -/
theorem iidTopKExpectedOn_equiv {ι κ Ω : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [Fintype Ω] [DecidableEq Ω]
    (e : ι ≃ κ) (itemLaw : PMF Ω) (k : ℕ) (value : Ω → ℝ) :
    iidTopKExpectedOn ι Ω itemLaw k value =
      iidTopKExpectedOn κ Ω itemLaw k value := by
  classical
  unfold iidTopKExpectedOn
  have htop :
      ∀ sample : ι → Ω,
        topKSumOn k (fun i => value (sample i)) =
          topKSumOn k (fun j : κ => value (sample (e.symm j))) := by
    intro sample
    simpa using
      topKSumOn_comp_equiv (e := e) (k := k)
        (v := fun j : κ => value (sample (e.symm j)))
  calc
    AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct ι Ω itemLaw)
        (fun sample : ι → Ω => topKSumOn k (fun i => value (sample i)))
        =
        AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct ι Ω itemLaw)
          (fun sample : ι → Ω =>
            topKSumOn k (fun j : κ => value (sample (e.symm j)))) := by
          exact AppliedModelingLib.pmfExp_congr _ htop
    _ =
        AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProduct κ Ω itemLaw)
          (fun sample : κ → Ω => topKSumOn k (fun j => value (sample j))) :=
          AppliedModelingLib.pmfExp_pmfProduct_equiv (e := e) itemLaw
            (fun sample : κ → Ω => topKSumOn k (fun j => value (sample j)))

/-- The option-step expectation for `Fin a` is the natural-size expectation at `a+1`. -/
theorem iidTopKExpectedOn_option_fin_eq_succ
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (itemLaw : PMF Ω) (k a : ℕ) (value : Ω → ℝ) :
    iidTopKExpectedOn (Option (Fin a)) Ω itemLaw k value =
      finiteIidTopKExpected Ω itemLaw k value (a + 1) := by
  unfold finiteIidTopKExpected
  exact iidTopKExpectedOn_equiv
    (AppliedModelingLib.optionFinEquivFinSucc a) itemLaw k value

/-!
## Endpoint/reflection algebra

Several bounded-support order-statistic arguments work by reflecting source
draws around an upper endpoint `M`.  If each upper order-statistic mean is
`M` minus the corresponding reflected lower order-statistic mean, the top-`k`
source loss is exactly the sum of the reflected means.  The following small
interface keeps that finite algebra in the shared probability layer, leaving
distribution-specific integral identities to paper files.
-/

/--
Top-`k` loss from an upper endpoint, expressed using the `k` source
order-statistic means at a fixed sample count.
-/
def topKEndpointLoss (M : ℝ) {k : ℕ} (sourceMean : Fin k → ℝ) : ℝ :=
  (k : ℝ) * M - ∑ i : Fin k, sourceMean i

/-- Sum of the reflected lower order-statistic means at a fixed sample count. -/
def reflectedTopKMeanSum {k : ℕ} (reflectedMean : Fin k → ℝ) : ℝ :=
  ∑ i : Fin k, reflectedMean i

/--
Reflection identity for bounded-support top-`k` order statistics: if every
source order-statistic mean is the upper endpoint minus its reflected mean,
then the total endpoint loss equals the reflected finite sum.
-/
theorem topKEndpointLoss_eq_reflectedTopKMeanSum
    (M : ℝ) {k : ℕ}
    (sourceMean reflectedMean : Fin k → ℝ)
    (hsource : ∀ i : Fin k, sourceMean i = M - reflectedMean i) :
    topKEndpointLoss M sourceMean =
      reflectedTopKMeanSum reflectedMean := by
  have hconst : (∑ _i : Fin k, M) = (k : ℝ) * M := by
    simp [Fintype.card_fin, nsmul_eq_mul, mul_comm]
  calc
    topKEndpointLoss M sourceMean
        = (∑ _i : Fin k, M) - ∑ i : Fin k, sourceMean i := by
          rw [topKEndpointLoss, hconst]
    _ = ∑ i : Fin k, (M - sourceMean i) := by
          rw [Finset.sum_sub_distrib]
    _ = ∑ i : Fin k, reflectedMean i := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [hsource i]
          ring
    _ = reflectedTopKMeanSum reflectedMean := by
          rw [reflectedTopKMeanSum]

/--
Sample-count-indexed wrapper for `topKEndpointLoss`, matching common
paper notation where source means depend on the number of sampled items.
-/
def topKEndpointLossSeq
    (M : ℝ) {k : ℕ} (sourceMean : Fin k → ℕ → ℝ) (a : ℕ) : ℝ :=
  topKEndpointLoss M (fun i => sourceMean i a)

/-- Sample-count-indexed wrapper for `reflectedTopKMeanSum`. -/
def reflectedTopKMeanSumSeq
    {k : ℕ} (reflectedMean : Fin k → ℕ → ℝ) (a : ℕ) : ℝ :=
  reflectedTopKMeanSum (fun i => reflectedMean i a)

/-- Sequence form of `topKEndpointLoss_eq_reflectedTopKMeanSum`. -/
theorem topKEndpointLossSeq_eq_reflectedTopKMeanSumSeq
    (M : ℝ) {k : ℕ}
    (sourceMean reflectedMean : Fin k → ℕ → ℝ)
    (hsource : ∀ a (i : Fin k), sourceMean i a = M - reflectedMean i a)
    (a : ℕ) :
    topKEndpointLossSeq M sourceMean a =
      reflectedTopKMeanSumSeq reflectedMean a :=
  topKEndpointLoss_eq_reflectedTopKMeanSum M
    (fun i => sourceMean i a)
    (fun i => reflectedMean i a)
    (fun i => hsource a i)

/-!
## Tuple-level real order statistics

The declarations below are deliberately measure-free.  They provide the
pointwise sorted-sample layer that distribution-specific files can integrate
against.  The key bounded-support bridge is the reflection identity: the
`i`-th largest source sample is the endpoint minus the `i`-th smallest
reflected sample.
-/

/-- The `rank`-th smallest value in a finite real sample. -/
def ascendingOrderStatistic {n : ℕ} (sample : Fin n → ℝ) (rank : Fin n) : ℝ :=
  sample (Tuple.sort sample rank)

theorem ascendingOrderStatistic_mono {n : ℕ} (sample : Fin n → ℝ) :
    Monotone (ascendingOrderStatistic sample) := by
  simpa [ascendingOrderStatistic, Function.comp_def] using
    Tuple.monotone_sort sample

theorem ascendingOrderStatistic_filter_card_eq
    {n : ℕ} (sample : Fin n → ℝ) (x : ℝ) :
    (Finset.univ.filter
        (fun i : Fin n => ascendingOrderStatistic sample i ≤ x)).card =
      (Finset.univ.filter (fun i : Fin n => sample i ≤ x)).card := by
  classical
  rw [← Fintype.card_subtype
      (fun i : Fin n => ascendingOrderStatistic sample i ≤ x),
    ← Fintype.card_subtype (fun i : Fin n => sample i ≤ x)]
  refine Fintype.card_congr ?_
  exact
    { toFun := fun i =>
        ⟨Tuple.sort sample i.1, by
          simpa [ascendingOrderStatistic] using i.2⟩
      invFun := fun i =>
        ⟨(Tuple.sort sample).symm i.1, by
          simpa [ascendingOrderStatistic] using i.2⟩
      left_inv := by
        intro i
        exact Subtype.ext ((Tuple.sort sample).symm_apply_apply i.1)
      right_inv := by
        intro i
        exact Subtype.ext ((Tuple.sort sample).apply_symm_apply i.1) }

theorem ascendingOrderStatistic_le_iff_rank_lt_card_le
    {n : ℕ} (sample : Fin n → ℝ) (rank : Fin n) (x : ℝ) :
    ascendingOrderStatistic sample rank ≤ x ↔
      rank.val <
        (Finset.univ.filter (fun i : Fin n => sample i ≤ x)).card := by
  classical
  have hsorted :=
    Tuple.lt_card_le_iff_apply_le_of_monotone
      (j := rank) (f := ascendingOrderStatistic sample) (a := x)
      (ascendingOrderStatistic_mono sample)
  rw [← hsorted, ascendingOrderStatistic_filter_card_eq]

theorem coordinate_le_count_measurable {n : ℕ} (x : ℝ) :
    Measurable
      (fun sample : Fin n → ℝ =>
        (Finset.univ.filter (fun i : Fin n => sample i ≤ x)).card) := by
  classical
  have hsum :
      Measurable
        (fun sample : Fin n → ℝ =>
          ∑ i : Fin n, if sample i ≤ x then (1 : ℕ) else 0) := by
    exact Finset.measurable_sum Finset.univ
      (fun i _hi =>
        Measurable.ite
          (measurableSet_le (measurable_pi_apply i) measurable_const)
          measurable_const measurable_const)
  convert hsum using 1
  ext sample
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

theorem ascendingOrderStatistic_measurable {n : ℕ} (rank : Fin n) :
    Measurable
      (fun sample : Fin n → ℝ => ascendingOrderStatistic sample rank) := by
  refine measurable_of_Iic ?_
  intro x
  have hset :
      (fun sample : Fin n → ℝ => ascendingOrderStatistic sample rank) ⁻¹'
          Set.Iic x =
        {sample : Fin n → ℝ |
          rank.val <
            (Finset.univ.filter (fun i : Fin n => sample i ≤ x)).card} := by
    ext sample
    simp [ascendingOrderStatistic_le_iff_rank_lt_card_le]
  rw [hset]
  exact measurableSet_lt measurable_const (coordinate_le_count_measurable x)

/-- The `rankFromTop`-th largest value in a finite real sample. -/
def upperOrderStatistic {n : ℕ} (sample : Fin n → ℝ)
    (rankFromTop : Fin n) : ℝ :=
  ascendingOrderStatistic sample rankFromTop.rev

theorem upperOrderStatistic_measurable {n : ℕ} (rankFromTop : Fin n) :
    Measurable
      (fun sample : Fin n → ℝ => upperOrderStatistic sample rankFromTop) :=
  ascendingOrderStatistic_measurable rankFromTop.rev

/--
The `rankFromTop`-th largest value is strictly above `x` iff more than
`rankFromTop` coordinates are strictly above `x`.
-/
theorem upperOrderStatistic_lt_iff_rank_lt_iidSuccessCount_Ioi
    {n : ℕ} (sample : Fin n → ℝ) (rankFromTop : Fin n) (x : ℝ) :
    x < upperOrderStatistic sample rankFromTop ↔
      rankFromTop.val < iidSuccessCount (Set.Ioi x) sample := by
  classical
  let countLE : ℕ :=
    (Finset.univ.filter (fun i : Fin n => sample i ≤ x)).card
  let countGT : ℕ := iidSuccessCount (Set.Ioi x) sample
  have hcountGT :
      countGT =
        (Finset.univ.filter (fun i : Fin n => ¬ sample i ≤ x)).card := by
    dsimp [countGT, iidSuccessCount, iidSuccessIndexSet]
    congr 1
    ext i
    simp [Set.mem_Ioi, not_le]
  have hsum : countLE + countGT = n := by
    have h :=
      Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin n)))
        (p := fun i : Fin n => sample i ≤ x)
    rw [hcountGT]
    simpa [countLE] using h
  have hle :
      upperOrderStatistic sample rankFromTop ≤ x ↔
        rankFromTop.rev.val < countLE := by
    simpa [upperOrderStatistic, countLE] using
      ascendingOrderStatistic_le_iff_rank_lt_card_le
        sample rankFromTop.rev x
  constructor
  · intro hgt
    have hnle : ¬ upperOrderStatistic sample rankFromTop ≤ x :=
      not_le.mpr hgt
    have hnot : ¬ rankFromTop.rev.val < countLE := by
      intro hrank
      exact hnle (hle.2 hrank)
    have hcount_le : countLE ≤ rankFromTop.rev.val :=
      Nat.le_of_not_gt hnot
    have hrev : rankFromTop.rev.val = n - (rankFromTop.val + 1) := by
      simp [Fin.val_rev]
    have hrank_lt_n : rankFromTop.val < n := rankFromTop.is_lt
    omega
  · intro hcount
    have hnle : ¬ upperOrderStatistic sample rankFromTop ≤ x := by
      intro hupper_le
      have hrank : rankFromTop.rev.val < countLE := hle.1 hupper_le
      have hrev : rankFromTop.rev.val = n - (rankFromTop.val + 1) := by
        simp [Fin.val_rev]
      have hrank_lt_n : rankFromTop.val < n := rankFromTop.is_lt
      omega
    exact lt_of_not_ge hnle

/-- The top rank in a nonempty finite sample. -/
noncomputable def topSampleRank {n : ℕ} [NeZero n] : Fin n :=
  ⟨0, Nat.pos_iff_ne_zero.mpr (NeZero.ne n)⟩

/--
Some coordinate of a finite sample exceeds `x` iff the count of coordinates
exceeding `x` is positive.
-/
theorem exists_lt_iff_iidSuccessCount_pos {n : ℕ}
    (sample : Fin n → ℝ) (x : ℝ) :
    (∃ i : Fin n, x < sample i) ↔
      0 < iidSuccessCount (Set.Ioi x) sample := by
  classical
  constructor
  · rintro ⟨i, hi⟩
    rw [iidSuccessCount]
    exact Finset.card_pos.mpr
      ⟨i, (mem_iidSuccessIndexSet (Set.Ioi x) sample i).2 hi⟩
  · intro h
    rw [iidSuccessCount] at h
    rcases Finset.card_pos.mp h with ⟨i, hi⟩
    exact ⟨i, (mem_iidSuccessIndexSet (Set.Ioi x) sample i).1 hi⟩

/--
Some coordinate of a nonempty finite sample exceeds `x` iff the largest order
statistic exceeds `x`.
-/
theorem exists_lt_iff_topOrderStatistic_gt {n : ℕ} [NeZero n]
    (sample : Fin n → ℝ) (x : ℝ) :
    (∃ i : Fin n, x < sample i) ↔
      x < upperOrderStatistic sample (topSampleRank (n := n)) := by
  rw [exists_lt_iff_iidSuccessCount_pos]
  rw [upperOrderStatistic_lt_iff_rank_lt_iidSuccessCount_Ioi]
  simp [topSampleRank]

/-- Real-valued probability that the top order statistic crosses `x`. -/
noncomputable def topOrderCrossingProbability {n : ℕ} [NeZero n]
    (μ : Measure (Fin n → ℝ)) (x : ℝ) : ℝ :=
  μ.real {noise : Fin n → ℝ |
    x < upperOrderStatistic noise (topSampleRank (n := n))}

/-- Real-valued probability that the top order statistic deviates from `center`. -/
noncomputable def topOrderDeviationProbability {n : ℕ} [NeZero n]
    (μ : Measure (Fin n → ℝ)) (center ε : ℝ) : ℝ :=
  μ.real {noise : Fin n → ℝ |
    ε < |upperOrderStatistic noise (topSampleRank (n := n)) - center|}

theorem topOrderCrossingSet_measurable {n : ℕ} [NeZero n]
    (x : ℝ) :
    MeasurableSet {noise : Fin n → ℝ |
      x < upperOrderStatistic noise (topSampleRank (n := n))} :=
  measurableSet_lt measurable_const
    (upperOrderStatistic_measurable (topSampleRank (n := n)))

theorem topOrderDeviationSet_measurable {n : ℕ} [NeZero n]
    (center ε : ℝ) :
    MeasurableSet {noise : Fin n → ℝ |
      ε < |upperOrderStatistic noise (topSampleRank (n := n)) - center|} := by
  have hmeas :
      Measurable
        (fun noise : Fin n → ℝ =>
          upperOrderStatistic noise (topSampleRank (n := n)) - center) :=
    (upperOrderStatistic_measurable (topSampleRank (n := n))).sub measurable_const
  exact measurableSet_lt measurable_const
    (continuous_abs.measurable.comp hmeas)

/--
For iid real samples, the top-order crossing probability is the source CDF
formula `1 - F(x)^n`.
-/
theorem topOrderCrossingProbability_iidProduct_eq_one_sub_lowerCDFMass_pow
    {n : ℕ} [NeZero n]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    topOrderCrossingProbability (Measure.pi (fun _ : Fin n => μ)) x =
      1 - (lowerCDFMass μ x) ^ n := by
  let productMeasure : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => μ)
  haveI : IsProbabilityMeasure productMeasure := by
    dsimp [productMeasure]
    infer_instance
  let crossingSet : Set (Fin n → ℝ) :=
    {sample : Fin n → ℝ | x < upperOrderStatistic sample (topSampleRank (n := n))}
  let zeroSet : Set (Fin n → ℝ) :=
    {sample : Fin n → ℝ | iidSuccessCount (Set.Ioi x) sample = 0}
  have hcompl : crossingSetᶜ = zeroSet := by
    ext sample
    simp [crossingSet, zeroSet,
      upperOrderStatistic_lt_iff_rank_lt_iidSuccessCount_Ioi,
      topSampleRank]
  have hcross_meas : MeasurableSet crossingSet := by
    simpa [crossingSet] using topOrderCrossingSet_measurable (n := n) x
  have hcompl_real :
      productMeasure.real zeroSet = 1 - productMeasure.real crossingSet := by
    rw [← hcompl]
    exact probReal_compl_eq_one_sub (μ := productMeasure) hcross_meas
  have hzero :
      productMeasure.real zeroSet =
        (lowerCDFMass μ x) ^ n := by
    have hbinom :=
      iidProductMeasure_successCount_eq_real
        (μ := μ) (s := Set.Ioi x) measurableSet_Ioi (j := 0)
        (n := n)
    have hsum := lowerCDFMass_add_upperTailMass_eq_one μ x
    calc
      productMeasure.real zeroSet =
          (Nat.choose n 0 : ℝ) *
            (μ.real (Set.Ioi x)) ^ 0 *
            (1 - μ.real (Set.Ioi x)) ^ (n - 0) := by
            simpa [productMeasure, zeroSet] using hbinom
      _ = (lowerCDFMass μ x) ^ n := by
            have htail : μ.real (Set.Ioi x) = upperTailMass μ x := rfl
            have hrewrite : 1 - μ.real (Set.Ioi x) = lowerCDFMass μ x := by
              rw [htail]
              linarith
            simp [hrewrite]
  have htop :
      topOrderCrossingProbability (Measure.pi (fun _ : Fin n => μ)) x =
        productMeasure.real crossingSet := rfl
  rw [htop]
  linarith

/-- Probability that every draw in a finite iid real sample is at most `x`.
For a nonempty sample this is the CDF of its maximum; the definition also
handles the empty finite product, whose value is one. -/
noncomputable def iidMaximumCdf {n : ℕ}
    (μ : Measure ℝ) (x : ℝ) : ℝ :=
  (Measure.pi (fun _ : Fin n => μ)).real
    (Set.pi Set.univ fun _ => Set.Iic x)

/-- The maximum-CDF event of a finite iid sample is the corresponding natural
power of the one-draw lower CDF mass. -/
theorem iidMaximumCdf_eq_lowerCDFMass_pow
    {n : ℕ}
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    iidMaximumCdf (n := n) μ x = (lowerCDFMass μ x) ^ n := by
  unfold iidMaximumCdf lowerCDFMass Measure.real
  rw [Measure.pi_pi, ENNReal.toReal_prod]
  simp [Finset.prod_const]

/-- The CDF of a finite iid maximum is monotone. -/
theorem iidMaximumCdf_mono
    {n : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Monotone (iidMaximumCdf (n := n) μ) := by
  intro x y hxy
  rw [iidMaximumCdf_eq_lowerCDFMass_pow, iidMaximumCdf_eq_lowerCDFMass_pow]
  exact pow_le_pow_left₀ (lowerCDFMass_nonneg μ x) (lowerCDFMass_mono μ hxy) n

/--
The derivative of a finite iid-maximum CDF is the ordinary power-rule
derivative of the one-draw lower CDF.  A `HasDerivAt` premise keeps this
pointwise and does not assume a global density representation.
-/
theorem hasDerivAt_iidMaximumCdf_of_hasDerivAt_lowerCDFMass
    {n : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ] {x : ℝ}
    {d : ℝ} (h : HasDerivAt (lowerCDFMass μ) d x) :
    HasDerivAt (iidMaximumCdf (n := n) μ)
      ((n : ℝ) * (lowerCDFMass μ x) ^ (n - 1) * d) x := by
  convert h.pow n using 1
  funext y
  simp only [iidMaximumCdf_eq_lowerCDFMass_pow, Pi.pow_apply]

/--
Pointwise derivative formula for a finite iid-maximum CDF, obtained from a
realized derivative of the one-draw lower CDF.
-/
theorem deriv_iidMaximumCdf_eq_of_hasDerivAt_lowerCDFMass
    {n : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ] {x : ℝ}
    (h : HasDerivAt (lowerCDFMass μ) (deriv (lowerCDFMass μ) x) x) :
    deriv (fun y => iidMaximumCdf (n := n) μ y) x =
      (n : ℝ) * (lowerCDFMass μ x) ^ (n - 1) * deriv (lowerCDFMass μ) x :=
  (hasDerivAt_iidMaximumCdf_of_hasDerivAt_lowerCDFMass μ h).deriv

/--
Recover the underlying one-draw CDF power law from a nonempty iid-maximum CDF
power law at a nonnegative point.  This is the natural-root step that turns an
order-statistic reward identity into the distribution identity used for
density calculations.
-/
theorem lowerCDFMass_eq_const_mul_rpow_of_iidMaximumCdf_eq
    {mu : Measure ℝ} [IsProbabilityMeasure mu]
    {n : ℕ} {C z β : ℝ}
    (hn : n ≠ 0) (hC : 0 ≤ C) (hz : 0 ≤ z)
    (hmax : iidMaximumCdf (n := n) mu z = C * z ^ β) :
    lowerCDFMass mu z =
      C ^ ((n : ℝ)⁻¹) * z ^ (β / (n : ℝ)) := by
  apply RealAnalysis.eq_const_mul_rpow_of_natPow_eq
    (lowerCDFMass_nonneg mu z) hC hz hn
  rw [← iidMaximumCdf_eq_lowerCDFMass_pow]
  exact hmax

/-- The CDF of a finite iid maximum inherits any finite or infinite order of
continuous differentiability possessed locally by the one-draw lower CDF. -/
theorem iidMaximumCdf_contDiffAt_of_lowerCDFMass
    {n : ℕ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {x : ℝ} {k : ℕ∞}
    (h : ContDiffAt ℝ k (lowerCDFMass μ) x) :
    ContDiffAt ℝ k (iidMaximumCdf (n := n) μ) x := by
  convert h.pow n using 1
  funext y
  rw [iidMaximumCdf_eq_lowerCDFMass_pow]

/--
The iid maximum CDF inherits equality of the one-draw lower CDF masses.
This is the order-statistic transport used to convert an atomless marginal
support gap into an equal-reward C1 deviation.
-/
theorem iidMaximumCdf_eq_of_lowerCDFMass_eq
    {n : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ] {a b : ℝ}
    (hflat : lowerCDFMass μ a = lowerCDFMass μ b) :
    iidMaximumCdf (n := n) μ a = iidMaximumCdf (n := n) μ b := by
  rw [iidMaximumCdf_eq_lowerCDFMass_pow,
    iidMaximumCdf_eq_lowerCDFMass_pow, hflat]

/--
For a nonempty iid sample, the maximum CDF vanishes at a lower endpoint of an
atomless marginal support.  This is the CDF boundary fact needed when a C1
support endpoint is compared with the zero action.
-/
theorem iidMaximumCdf_eq_zero_of_forall_mem_support_le
    {n : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ]
    (hn : n ≠ 0) {a : ℝ}
    (hmin : ∀ x ∈ μ.support, a ≤ x) :
    iidMaximumCdf (n := n) μ a = 0 := by
  rw [iidMaximumCdf_eq_lowerCDFMass_pow,
    lowerCDFMass_eq_zero_of_forall_mem_support_le μ hmin,
    zero_pow hn]

/--
At a support point, an iid maximum CDF is invariant under a measurable map
that is strictly increasing on the source support.  The conclusion is local to
the represented support point; no monotonicity is assumed away from support.
-/
theorem iidMaximumCdf_map_eq_of_support_strictMonoOn
    {n : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ] {g : ℝ → ℝ}
    (hg : Measurable g)
    (hstrict : ∀ x ∈ μ.support, ∀ y ∈ μ.support, x < y → g x < g y)
    {x : ℝ} (hx : x ∈ μ.support) :
    iidMaximumCdf (n := n) (Measure.map g μ) (g x) =
      iidMaximumCdf (n := n) μ x := by
  letI : IsProbabilityMeasure (Measure.map g μ) :=
    Measure.isProbabilityMeasure_map hg.aemeasurable
  rw [iidMaximumCdf_eq_lowerCDFMass_pow,
    iidMaximumCdf_eq_lowerCDFMass_pow,
    lowerCDFMass_map_eq_of_support_strictMonoOn hg hstrict hx]

/--
If a joint probability law is supported on the graph of a measurable function,
then its second iid maximum CDF agrees with the first one after graph
transport, provided the graph function is strictly increasing on first
marginal support.  This is the measure-theoretic C2 bridge used by graph-based
equilibrium arguments.
-/
theorem iidMaximumCdf_snd_eq_fst_of_support_graph_strictMonoOn
    {n : ℕ} (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν]
    {g : ℝ → ℝ} (hg : Measurable g)
    (hgraph : ∀ z ∈ ν.support, z.2 = g z.1)
    (hstrict : ∀ x ∈ (Measure.map Prod.fst ν).support,
      ∀ y ∈ (Measure.map Prod.fst ν).support, x < y → g x < g y)
    {x : ℝ} (hx : x ∈ (Measure.map Prod.fst ν).support) :
    iidMaximumCdf (n := n) (Measure.map Prod.snd ν) (g x) =
      iidMaximumCdf (n := n) (Measure.map Prod.fst ν) x := by
  letI : IsProbabilityMeasure (Measure.map Prod.fst ν) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  rw [map_snd_eq_map_graph_map_fst_of_support_graph hg hgraph]
  exact iidMaximumCdf_map_eq_of_support_strictMonoOn
    (Measure.map Prod.fst ν) hg hstrict hx

/--
An atomless open support gap is invisible to an iid maximum CDF through its
right endpoint.  The topological-support and atomlessness hypotheses are kept
explicit so this theorem never treats an open gap as excluding an endpoint
atom by default.
-/
theorem iidMaximumCdf_eq_of_Ioo_subset_compl_support_of_noAtoms
    {n : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ]
    {a b : ℝ} (hab : a ≤ b) (hgap : Set.Ioo a b ⊆ μ.supportᶜ) :
    iidMaximumCdf (n := n) μ a = iidMaximumCdf (n := n) μ b :=
  iidMaximumCdf_eq_of_lowerCDFMass_eq μ
    (lowerCDFMass_eq_of_Ioo_subset_compl_support_of_noAtoms μ hab hgap)

/--
For iid samples, if the lower-tail mass at a threshold is strictly below one,
then the probability that the sample maximum does not cross that threshold
vanishes as the sample size grows.
-/
theorem one_sub_topOrderCrossingProbability_iidProduct_tendsto_zero_of_lowerCDFMass_lt_one
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {x : ℝ}
    (hlt : lowerCDFMass μ x < 1) :
    Tendsto
      (fun n : ℕ =>
        1 -
          topOrderCrossingProbability
            (Measure.pi (fun _ : Fin (n + 1) => μ)) x)
      atTop (nhds 0) := by
  have hpow :
      Tendsto
        (fun n : ℕ => (lowerCDFMass μ x) ^ (n + 1))
        atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one
      (lowerCDFMass_nonneg μ x) hlt).comp (tendsto_add_atTop_nat 1)
  refine Tendsto.congr' ?_ hpow
  filter_upwards with n
  have hcross :=
    topOrderCrossingProbability_iidProduct_eq_one_sub_lowerCDFMass_pow
      (n := n + 1) μ x
  rw [hcross]
  ring

/--
For iid samples, if the lower-tail mass at a threshold is strictly below one,
then the sample maximum eventually crosses that threshold with probability
tending to one.
-/
theorem topOrderCrossingProbability_iidProduct_tendsto_one_of_lowerCDFMass_lt_one
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {x : ℝ}
    (hlt : lowerCDFMass μ x < 1) :
    Tendsto
      (fun n : ℕ =>
        topOrderCrossingProbability
          (Measure.pi (fun _ : Fin (n + 1) => μ)) x)
      atTop (nhds 1) := by
  have hfail :=
    one_sub_topOrderCrossingProbability_iidProduct_tendsto_zero_of_lowerCDFMass_lt_one
      μ hlt
  have hsub :
      Tendsto
        (fun n : ℕ =>
          1 -
            (1 -
              topOrderCrossingProbability
                (Measure.pi (fun _ : Fin (n + 1) => μ)) x))
        atTop (nhds (1 - 0)) :=
    tendsto_const_nhds.sub hfail
  simpa using hsub

/--
Endpoint form: if every threshold strictly below the upper endpoint has CDF
mass below one, then the iid maximum crosses any fixed sub-endpoint threshold
with probability tending to one.
-/
theorem topOrderCrossingProbability_iidProduct_tendsto_one_of_lt_endpoint
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {x M : ℝ}
    (hcdf_lt_top : ∀ y : ℝ, y < M → lowerCDFMass μ y < 1)
    (hx : x < M) :
    Tendsto
      (fun n : ℕ =>
        topOrderCrossingProbability
          (Measure.pi (fun _ : Fin (n + 1) => μ)) x)
      atTop (nhds 1) :=
  topOrderCrossingProbability_iidProduct_tendsto_one_of_lowerCDFMass_lt_one
    μ (hcdf_lt_top x hx)

theorem topOrderCrossingProbability_le_deviationProbability_of_center_add_le
    {n : ℕ} [NeZero n]
    (μ : Measure (Fin n → ℝ)) [IsFiniteMeasure μ]
    {x center ε : ℝ} (hsep : center + ε ≤ x) :
    topOrderCrossingProbability μ x ≤
      topOrderDeviationProbability μ center ε := by
  unfold topOrderCrossingProbability topOrderDeviationProbability
  exact measureReal_mono
    (μ := μ)
    (by
      intro noise hcross
      change x < upperOrderStatistic noise (topSampleRank (n := n)) at hcross
      have hdev :
          ε < upperOrderStatistic noise (topSampleRank (n := n)) - center := by
        linarith
      exact lt_of_lt_of_le hdev (le_abs_self _))
    (measure_ne_top μ _)

theorem one_sub_topOrderCrossingProbability_le_deviationProbability_of_lt_center_sub
    {n : ℕ} [NeZero n]
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    {x center ε : ℝ} (hε : 0 < ε) (hsep : x < center - ε) :
    1 - topOrderCrossingProbability μ x ≤
      topOrderDeviationProbability μ center ε := by
  let crossingSet : Set (Fin n → ℝ) :=
    {noise : Fin n → ℝ |
      x < upperOrderStatistic noise (topSampleRank (n := n))}
  let deviationSet : Set (Fin n → ℝ) :=
    {noise : Fin n → ℝ |
      ε < |upperOrderStatistic noise (topSampleRank (n := n)) - center|}
  have hcross_meas : MeasurableSet crossingSet := by
    simpa [crossingSet] using topOrderCrossingSet_measurable (n := n) x
  have hcompl_subset : crossingSetᶜ ⊆ deviationSet := by
    intro noise hnoise
    simp [crossingSet, deviationSet] at hnoise ⊢
    have hle :
        upperOrderStatistic noise (topSampleRank (n := n)) ≤ x :=
      hnoise
    let gap : ℝ :=
      upperOrderStatistic noise (topSampleRank (n := n)) - center
    have hgap_lt_neg : gap < -ε := by
      dsimp [gap]
      linarith
    have hgap_neg : gap < 0 := by linarith
    have habs : |gap| = -gap := abs_of_neg hgap_neg
    change ε < |gap|
    rw [habs]
    linarith
  have hcompl_real :
      μ.real crossingSetᶜ = 1 - μ.real crossingSet :=
    probReal_compl_eq_one_sub (μ := μ) hcross_meas
  calc
    1 - topOrderCrossingProbability μ x
        = μ.real crossingSetᶜ := by
            rw [hcompl_real]
            rfl
    _ ≤ μ.real deviationSet :=
        measureReal_mono (μ := μ) hcompl_subset (measure_ne_top μ _)
    _ = topOrderDeviationProbability μ center ε := rfl

/--
Sequence form of the maximum-order-statistic deviation probability.  The
sample size is `n + 1` to keep the finite sample nonempty without threading
`NeZero n` through asymptotic statements.
-/
noncomputable def topOrderDeviationProbabilitySeq
    (sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ))
    (center : ℕ → ℝ) (ε : ℝ) (n : ℕ) : ℝ :=
  topOrderDeviationProbability (sampleLaw n) (center n) ε

/--
Reusable maximum-concentration interface: the top order statistic of a
nonempty finite sample concentrates around the supplied center sequence.
-/
def TopOrderDeviationConcentrating
    (sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ))
    (center : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (topOrderDeviationProbabilitySeq sampleLaw center ε) atTop (nhds 0)

/--
Chebyshev-style bridge to maximum-order concentration.  If the deviation
probability at radius `ε` is eventually bounded by a variance bound divided by
`ε^2`, and that variance bound tends to zero, then the top order statistic
concentrates around the supplied center.
-/
theorem TopOrderDeviationConcentrating.of_chebyshev_bound
    {sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)}
    {center varianceBound : ℕ → ℝ}
    (hvariance_zero : Tendsto varianceBound atTop (nhds 0))
    (hchebyshev :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n : ℕ in atTop,
          topOrderDeviationProbability (sampleLaw n) (center n) ε ≤
            varianceBound n / ε ^ 2) :
    TopOrderDeviationConcentrating sampleLaw center := by
  intro ε hε
  have hscaled :
      Tendsto (fun n : ℕ => varianceBound n / ε ^ 2) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      hvariance_zero.mul_const ((ε ^ 2)⁻¹)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hscaled ?_ ?_
  · filter_upwards with n
    exact measureReal_nonneg
  · exact hchebyshev ε hε

theorem TopOrderDeviationConcentrating.eventually_deviation_lt
    {sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)}
    {center : ℕ → ℝ}
    (hconc : TopOrderDeviationConcentrating sampleLaw center)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop,
      topOrderDeviationProbability (sampleLaw n) (center n) ε < η :=
  hconc ε hε (isOpen_Iio.mem_nhds hη)

/--
If a threshold is eventually at least `ε` above the concentration center, the
top-order crossing probability tends to zero.
-/
theorem topOrderCrossingProbability_tendsto_zero_of_eventually_center_add_le
    {sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)}
    {center threshold : ℕ → ℝ}
    (hfinite : ∀ n, IsFiniteMeasure (sampleLaw n))
    (hconc : TopOrderDeviationConcentrating sampleLaw center)
    {ε : ℝ} (hε : 0 < ε)
    (hsep : ∀ᶠ n : ℕ in atTop, center n + ε ≤ threshold n) :
    Tendsto
      (fun n : ℕ =>
        topOrderCrossingProbability (sampleLaw n) (threshold n))
      atTop (nhds 0) := by
  have hdev_zero :
      Tendsto
        (fun n : ℕ =>
          topOrderDeviationProbability (sampleLaw n) (center n) ε)
        atTop (nhds 0) :=
    hconc ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hdev_zero ?_ ?_
  · filter_upwards with n
    exact measureReal_nonneg
  · filter_upwards [hsep] with n hn
    haveI : IsFiniteMeasure (sampleLaw n) := hfinite n
    exact topOrderCrossingProbability_le_deviationProbability_of_center_add_le
      (sampleLaw n) hn

/--
If a threshold is eventually at least `ε` below the concentration center, the
failure probability `1 - Pr[max > threshold]` tends to zero.
-/
theorem one_sub_topOrderCrossingProbability_tendsto_zero_of_eventually_lt_center_sub
    {sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ)}
    {center threshold : ℕ → ℝ}
    (hprob : ∀ n, IsProbabilityMeasure (sampleLaw n))
    (hconc : TopOrderDeviationConcentrating sampleLaw center)
    {ε : ℝ} (hε : 0 < ε)
    (hsep : ∀ᶠ n : ℕ in atTop, threshold n < center n - ε) :
    Tendsto
      (fun n : ℕ =>
        1 - topOrderCrossingProbability (sampleLaw n) (threshold n))
      atTop (nhds 0) := by
  have hdev_zero :
      Tendsto
        (fun n : ℕ =>
          topOrderDeviationProbability (sampleLaw n) (center n) ε)
        atTop (nhds 0) :=
    hconc ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hdev_zero ?_ ?_
  · filter_upwards with n
    haveI : IsProbabilityMeasure (sampleLaw n) := hprob n
    have hle_one :
        topOrderCrossingProbability (sampleLaw n) (threshold n) ≤ 1 := by
      simpa [topOrderCrossingProbability] using
        measureReal_le_one (μ := sampleLaw n)
          (s := {noise : Fin (n + 1) → ℝ |
            threshold n < upperOrderStatistic noise (topSampleRank (n := n + 1))})
    linarith
  · filter_upwards [hsep] with n hn
    haveI : IsProbabilityMeasure (sampleLaw n) := hprob n
    exact
      one_sub_topOrderCrossingProbability_le_deviationProbability_of_lt_center_sub
        (sampleLaw n) hε hn

/-- Reflect a finite sample around an upper endpoint `M`. -/
def reflectedSample (M : ℝ) {n : ℕ} (sample : Fin n → ℝ) : Fin n → ℝ :=
  fun i => M - sample i

theorem reflectedSample_measurable (M : ℝ) {n : ℕ} :
    Measurable (fun sample : Fin n → ℝ => reflectedSample M sample) := by
  refine measurable_pi_lambda _ ?_
  intro i
  exact measurable_const.sub (measurable_pi_apply i)

theorem reflectedAscendingOrderStatistic_measurable
    (M : ℝ) {n : ℕ} (rank : Fin n) :
    Measurable
      (fun sample : Fin n → ℝ =>
        ascendingOrderStatistic (reflectedSample M sample) rank) :=
  (ascendingOrderStatistic_measurable rank).comp
    (reflectedSample_measurable M)

/--
Sorting the reflected sample in ascending order gives the endpoint minus the
source sample sorted in descending order.  This value-level statement is robust
to ties because `Tuple.unique_monotone` identifies the sorted value tuple.
-/
theorem ascendingOrderStatistic_reflectedSample
    (M : ℝ) {n : ℕ} (sample : Fin n → ℝ) (rank : Fin n) :
    ascendingOrderStatistic (reflectedSample M sample) rank =
      M - ascendingOrderStatistic sample rank.rev := by
  let σ : Equiv.Perm (Fin n) := Fin.revPerm.trans (Tuple.sort sample)
  have hmonoσ : Monotone ((reflectedSample M sample) ∘ σ) := by
    intro i j hij
    have hrev : j.rev ≤ i.rev := by
      rw [Fin.le_iff_val_le_val]
      simp only [Fin.val_rev]
      omega
    have hsort := ascendingOrderStatistic_mono sample hrev
    dsimp [ascendingOrderStatistic, reflectedSample, Function.comp_def, σ] at hsort ⊢
    linarith
  have hsorted :
      (reflectedSample M sample) ∘ σ =
        (reflectedSample M sample) ∘ Tuple.sort (reflectedSample M sample) :=
    Tuple.unique_monotone hmonoσ (Tuple.monotone_sort (reflectedSample M sample))
  have hrank := congr_fun hsorted rank
  simpa [ascendingOrderStatistic, reflectedSample, Function.comp_def, σ] using
    hrank.symm

/--
Bounded-support reflection for a single upper order statistic: the `i`-th
largest source value equals `M` minus the `i`-th smallest reflected value.
-/
theorem upperOrderStatistic_eq_endpoint_sub_reflectedAscending
    (M : ℝ) {n : ℕ} (sample : Fin n → ℝ) (rankFromTop : Fin n) :
    upperOrderStatistic sample rankFromTop =
      M - ascendingOrderStatistic (reflectedSample M sample) rankFromTop := by
  rw [ascendingOrderStatistic_reflectedSample]
  simp [upperOrderStatistic]

theorem ascendingOrderStatistic_le_of_forall_le
    {n : ℕ} {sample : Fin n → ℝ} {B : ℝ}
    (hB : ∀ i, sample i ≤ B) (rank : Fin n) :
    ascendingOrderStatistic sample rank ≤ B :=
  hB (Tuple.sort sample rank)

theorem le_ascendingOrderStatistic_of_forall_le
    {n : ℕ} {sample : Fin n → ℝ} {B : ℝ}
    (hB : ∀ i, B ≤ sample i) (rank : Fin n) :
    B ≤ ascendingOrderStatistic sample rank :=
  hB (Tuple.sort sample rank)

theorem upperOrderStatistic_le_of_forall_le
    {n : ℕ} {sample : Fin n → ℝ} {B : ℝ}
    (hB : ∀ i, sample i ≤ B) (rankFromTop : Fin n) :
    upperOrderStatistic sample rankFromTop ≤ B :=
  ascendingOrderStatistic_le_of_forall_le hB rankFromTop.rev

theorem le_upperOrderStatistic_of_forall_le
    {n : ℕ} {sample : Fin n → ℝ} {B : ℝ}
    (hB : ∀ i, B ≤ sample i) (rankFromTop : Fin n) :
    B ≤ upperOrderStatistic sample rankFromTop :=
  le_ascendingOrderStatistic_of_forall_le hB rankFromTop.rev

/-- Embed the first `min k n` top ranks into all sample ranks. -/
def topKRankEmbedding (k n : ℕ) (i : Fin (min k n)) : Fin n :=
  ⟨i.val, lt_of_lt_of_le i.isLt (min_le_right k n)⟩

/-- Pointwise top-`k` sum of the largest values in a finite real sample. -/
def sampleTopKSum {n : ℕ} (sample : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ i : Fin (min k n),
    upperOrderStatistic sample (topKRankEmbedding k n i)

theorem sampleTopKSum_measurable {n : ℕ} (k : ℕ) :
    Measurable (fun sample : Fin n → ℝ => sampleTopKSum sample k) := by
  unfold sampleTopKSum
  exact Finset.measurable_sum Finset.univ
    (fun i _hi => upperOrderStatistic_measurable (topKRankEmbedding k n i))

theorem sampleTopKSum_le_of_forall_le
    {n : ℕ} {sample : Fin n → ℝ} {B : ℝ}
    (hB : ∀ i, sample i ≤ B) (k : ℕ) :
    sampleTopKSum sample k ≤ (min k n : ℝ) * B := by
  calc
    sampleTopKSum sample k
        ≤ ∑ _i : Fin (min k n), B := by
          unfold sampleTopKSum
          exact Finset.sum_le_sum
            (fun i _hi =>
              upperOrderStatistic_le_of_forall_le hB
                (topKRankEmbedding k n i))
    _ = (min k n : ℝ) * B := by
          simp [Fintype.card_fin, nsmul_eq_mul]

theorem sampleTopKSum_ge_of_forall_lower
    {n : ℕ} {sample : Fin n → ℝ} {L : ℝ}
    (hL : ∀ i, L ≤ sample i) (k : ℕ) :
    (min k n : ℝ) * L ≤ sampleTopKSum sample k := by
  calc
    (min k n : ℝ) * L = ∑ _i : Fin (min k n), L := by
          simp [Fintype.card_fin, nsmul_eq_mul]
    _ ≤ sampleTopKSum sample k := by
          unfold sampleTopKSum
          exact Finset.sum_le_sum
            (fun i _hi =>
              le_upperOrderStatistic_of_forall_le hL
                (topKRankEmbedding k n i))

theorem sampleTopKSum_nonneg_of_forall_nonneg
    {n : ℕ} {sample : Fin n → ℝ}
    (h_nonneg : ∀ i, 0 ≤ sample i) (k : ℕ) :
    0 ≤ sampleTopKSum sample k := by
  unfold sampleTopKSum
  exact Finset.sum_nonneg
    (fun i _hi =>
      le_upperOrderStatistic_of_forall_le h_nonneg
        (topKRankEmbedding k n i))

/-- Indices of the largest `min k n` entries of a finite sample. -/
def sampleTopKIndexSet {n : ℕ} (sample : Fin n → ℝ) (k : ℕ) :
    Finset (Fin n) :=
  (Finset.univ : Finset (Fin (min k n))).image
    (fun i => Tuple.sort sample (topKRankEmbedding k n i).rev)

theorem sampleTopKIndexSet_card {n : ℕ} (sample : Fin n → ℝ) (k : ℕ) :
    (sampleTopKIndexSet sample k).card = min k n := by
  classical
  unfold sampleTopKIndexSet
  rw [Finset.card_image_of_injective]
  · simp
  · intro i j hij
    have hrev :
        (topKRankEmbedding k n i).rev =
          (topKRankEmbedding k n j).rev :=
      (Tuple.sort sample).injective hij
    have htop :
        topKRankEmbedding k n i = topKRankEmbedding k n j := by
      exact Fin.rev_injective hrev
    exact Fin.ext (by simpa [topKRankEmbedding] using congrArg Fin.val htop)

theorem sampleTopKIndexSet_mem_iff {n : ℕ} (sample : Fin n → ℝ)
    (k : ℕ) (x : Fin n) :
    x ∈ sampleTopKIndexSet sample k ↔
      (((Tuple.sort sample).symm x).rev.val < min k n) := by
  classical
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨i, _hi, hix⟩
    have hs :
        (Tuple.sort sample).symm x =
          (topKRankEmbedding k n i).rev := by
      simpa [hix] using
        (Equiv.symm_apply_apply (Tuple.sort sample)
          (topKRankEmbedding k n i).rev)
    have hrev :
        ((Tuple.sort sample).symm x).rev =
          topKRankEmbedding k n i := by
      rw [hs, Fin.rev_rev]
    simpa [hrev, topKRankEmbedding] using i.isLt
  · intro hx
    let i : Fin (min k n) :=
      ⟨((Tuple.sort sample).symm x).rev.val, hx⟩
    have htop :
        topKRankEmbedding k n i =
          ((Tuple.sort sample).symm x).rev := by
      exact Fin.ext (by simp [i, topKRankEmbedding])
    have hx_eq :
        x = Tuple.sort sample (topKRankEmbedding k n i).rev := by
      rw [htop, Fin.rev_rev]
      exact (Equiv.apply_symm_apply (Tuple.sort sample) x).symm
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hx_eq.symm⟩

theorem sample_le_of_not_mem_sampleTopKIndexSet_of_mem
    {n : ℕ} {sample : Fin n → ℝ} {k : ℕ}
    {a b : Fin n}
    (ha : a ∉ sampleTopKIndexSet sample k)
    (hb : b ∈ sampleTopKIndexSet sample k) :
    sample a ≤ sample b := by
  classical
  have ha_rank :
      min k n ≤ (((Tuple.sort sample).symm a).rev.val) := by
    have hnot :=
      mt (sampleTopKIndexSet_mem_iff sample k a).2 ha
    exact le_of_not_gt hnot
  have hb_rank :
      (((Tuple.sort sample).symm b).rev.val) < min k n :=
    (sampleTopKIndexSet_mem_iff sample k b).1 hb
  have hrev_lt :
      (((Tuple.sort sample).symm b).rev.val) <
        (((Tuple.sort sample).symm a).rev.val) :=
    lt_of_lt_of_le hb_rank ha_rank
  have hrank_le :
      (Tuple.sort sample).symm a ≤ (Tuple.sort sample).symm b := by
    change ((Tuple.sort sample).symm a).val ≤
      ((Tuple.sort sample).symm b).val
    simp only [Fin.val_rev] at hrev_lt
    omega
  have hmono :=
    ascendingOrderStatistic_mono sample hrank_le
  simpa [ascendingOrderStatistic] using hmono

theorem sampleTopKSum_eq_sum_sampleTopKIndexSet
    {n : ℕ} (sample : Fin n → ℝ) (k : ℕ) :
    sampleTopKSum sample k =
      ∑ i ∈ sampleTopKIndexSet sample k, sample i := by
  classical
  unfold sampleTopKSum sampleTopKIndexSet upperOrderStatistic
  symm
  refine Finset.sum_image ?_
  intro i _hi j _hj hij
  have hrev :
      (topKRankEmbedding k n i).rev =
        (topKRankEmbedding k n j).rev :=
    (Tuple.sort sample).injective hij
  have htop :
      topKRankEmbedding k n i = topKRankEmbedding k n j :=
    Fin.rev_injective hrev
  exact Fin.ext (by simpa [topKRankEmbedding] using congrArg Fin.val htop)

theorem topKSumOn_eq_sampleTopKSum_of_forall_nonneg
    {n : ℕ} (sample : Fin n → ℝ) (k : ℕ)
    (h_nonneg : ∀ i, 0 ≤ sample i) :
    topKSumOn k sample = sampleTopKSum sample k := by
  classical
  let topSet : Finset (Fin n) := sampleTopKIndexSet sample k
  have htop_card : topSet.card = min k n := by
    simpa [topSet] using sampleTopKIndexSet_card sample k
  have htop_card_le : topSet.card ≤ k := by
    rw [htop_card]
    exact min_le_left k n
  have htop_sum :
      sampleTopKSum sample k = ∑ i ∈ topSet, sample i := by
    simpa [topSet] using sampleTopKSum_eq_sum_sampleTopKIndexSet sample k
  apply le_antisymm
  · unfold topKSumOn
    refine Finset.sup'_le (topKCandidateSets_nonempty (Fin n) k)
      (fun s => ∑ i ∈ s, sample i) ?_
    intro s hs
    have hs_card_le_k : s.card ≤ k := by
      simpa [topKCandidateSets] using hs
    have hs_card_le_n : s.card ≤ n := by
      simpa using Finset.card_le_univ (s := s)
    have hs_card : s.card ≤ topSet.card := by
      rw [htop_card]
      exact le_min hs_card_le_k hs_card_le_n
    have hpair :
        ∀ a ∈ s \ topSet, ∀ b ∈ topSet \ s, sample a ≤ sample b := by
      intro a ha b hb
      exact sample_le_of_not_mem_sampleTopKIndexSet_of_mem
        (sample := sample) (k := k)
        (by simpa [topSet] using (Finset.mem_sdiff.mp ha).2)
        (by simpa [topSet] using (Finset.mem_sdiff.mp hb).1)
    have htdiff_nonneg :
        ∀ b ∈ topSet \ s, 0 ≤ sample b := by
      intro b _hb
      exact h_nonneg b
    have hleTop :
        (∑ i ∈ s, sample i) ≤ ∑ i ∈ topSet, sample i :=
      AppliedModelingLib.FiniteSum.finset_sum_le_sum_of_card_le_pairwise_sdiff
        s topSet sample hs_card hpair htdiff_nonneg
    exact hleTop.trans_eq htop_sum.symm
  · have hle :=
      sum_le_topKSumOn (ι := Fin n) k sample topSet htop_card_le
    simpa [htop_sum] using hle

/-- If `k` covers the whole sample, the top-`k` sum is the full sample sum. -/
theorem sampleTopKSum_eq_sum_of_card_le
    {n : ℕ} (sample : Fin n → ℝ) (k : ℕ)
    (hnk : n ≤ k) :
    sampleTopKSum sample k = ∑ i : Fin n, sample i := by
  classical
  have hmin : min k n = n := min_eq_right hnk
  calc
    sampleTopKSum sample k
        = ∑ i : Fin (min k n),
            sample (Tuple.sort sample (topKRankEmbedding k n i).rev) := by
          rfl
    _ = ∑ j : Fin n, sample (Tuple.sort sample j.rev) := by
          let e : Fin (min k n) ≃ Fin n := finCongr hmin
          exact Fintype.sum_equiv e
            (fun i : Fin (min k n) =>
              sample (Tuple.sort sample (topKRankEmbedding k n i).rev))
            (fun j : Fin n => sample (Tuple.sort sample j.rev))
            (by
              intro i
              apply congrArg (fun r : Fin n => sample (Tuple.sort sample r.rev))
              apply Fin.ext
              simp [e, topKRankEmbedding])
    _ = ∑ j : Fin n, sample j := by
          let e : Equiv.Perm (Fin n) := Fin.revPerm.trans (Tuple.sort sample)
          have hsum :
              (∑ j : Fin n, sample (e j)) = ∑ j : Fin n, sample j :=
            Fintype.sum_equiv e
              (fun j : Fin n => sample (e j)) sample (by intro j; rfl)
          simpa [e, Fin.revPerm] using hsum

/-- Endpoint loss of the pointwise top-`k` sample sum. -/
def sampleTopKEndpointLoss (M : ℝ) {n : ℕ}
    (sample : Fin n → ℝ) (k : ℕ) : ℝ :=
  (min k n : ℝ) * M - sampleTopKSum sample k

theorem sampleTopKEndpointLoss_measurable (M : ℝ) {n : ℕ} (k : ℕ) :
    Measurable
      (fun sample : Fin n → ℝ => sampleTopKEndpointLoss M sample k) := by
  unfold sampleTopKEndpointLoss
  exact measurable_const.sub (sampleTopKSum_measurable k)

theorem sampleTopKEndpointLoss_nonneg_of_forall_le
    (M : ℝ) {n : ℕ} {sample : Fin n → ℝ}
    (hM : ∀ i, sample i ≤ M) (k : ℕ) :
    0 ≤ sampleTopKEndpointLoss M sample k := by
  unfold sampleTopKEndpointLoss
  exact sub_nonneg.mpr (sampleTopKSum_le_of_forall_le hM k)

theorem reflectedSample_nonneg_of_forall_le
    (M : ℝ) {n : ℕ} {sample : Fin n → ℝ}
    (hM : ∀ i, sample i ≤ M) (i : Fin n) :
    0 ≤ reflectedSample M sample i := by
  unfold reflectedSample
  exact sub_nonneg.mpr (hM i)

theorem reflectedSample_le_of_forall_lower
    (M L : ℝ) {n : ℕ} {sample : Fin n → ℝ}
    (hL : ∀ i, L ≤ sample i) (i : Fin n) :
    reflectedSample M sample i ≤ M - L := by
  unfold reflectedSample
  linarith [hL i]

/-- Sum of the first `min k n` reflected lower order statistics. -/
def reflectedBottomKSum (M : ℝ) {n : ℕ}
    (sample : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ i : Fin (min k n),
    ascendingOrderStatistic (reflectedSample M sample) (topKRankEmbedding k n i)

theorem reflectedBottomKSum_measurable (M : ℝ) {n : ℕ} (k : ℕ) :
    Measurable
      (fun sample : Fin n → ℝ => reflectedBottomKSum M sample k) := by
  unfold reflectedBottomKSum
  exact Finset.measurable_sum Finset.univ
    (fun i _hi =>
      reflectedAscendingOrderStatistic_measurable
        M (topKRankEmbedding k n i))

theorem reflectedBottomKSum_nonneg_of_forall_le
    (M : ℝ) {n : ℕ} {sample : Fin n → ℝ}
    (hM : ∀ i, sample i ≤ M) (k : ℕ) :
    0 ≤ reflectedBottomKSum M sample k := by
  unfold reflectedBottomKSum
  exact Finset.sum_nonneg
    (fun i _hi =>
      le_ascendingOrderStatistic_of_forall_le
        (reflectedSample_nonneg_of_forall_le M hM)
        (topKRankEmbedding k n i))

theorem reflectedBottomKSum_le_of_forall_lower
    (M L : ℝ) {n : ℕ} {sample : Fin n → ℝ}
    (hL : ∀ i, L ≤ sample i) (k : ℕ) :
    reflectedBottomKSum M sample k ≤ (min k n : ℝ) * (M - L) := by
  calc
    reflectedBottomKSum M sample k
        ≤ ∑ _i : Fin (min k n), (M - L) := by
          unfold reflectedBottomKSum
          exact Finset.sum_le_sum
            (fun i _hi =>
              ascendingOrderStatistic_le_of_forall_le
                (reflectedSample_le_of_forall_lower M L hL)
                (topKRankEmbedding k n i))
    _ = (min k n : ℝ) * (M - L) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          simp

/--
Pointwise top-`k` reflection algebra: endpoint loss of the largest source
values equals the sum of the smallest reflected values.
-/
theorem sampleTopKEndpointLoss_eq_reflectedBottomKSum
    (M : ℝ) {n : ℕ} (sample : Fin n → ℝ) (k : ℕ) :
    sampleTopKEndpointLoss M sample k =
      reflectedBottomKSum M sample k := by
  simpa [sampleTopKEndpointLoss, sampleTopKSum, reflectedBottomKSum,
    topKEndpointLoss, reflectedTopKMeanSum] using
    topKEndpointLoss_eq_reflectedTopKMeanSum M
      (fun i : Fin (min k n) =>
        upperOrderStatistic sample (topKRankEmbedding k n i))
      (fun i : Fin (min k n) =>
        ascendingOrderStatistic (reflectedSample M sample)
          (topKRankEmbedding k n i))
      (fun i =>
        upperOrderStatistic_eq_endpoint_sub_reflectedAscending
          M sample (topKRankEmbedding k n i))

theorem sampleTopKEndpointLoss_le_of_forall_bounds
    (M L : ℝ) {n : ℕ} {sample : Fin n → ℝ}
    (hL : ∀ i, L ≤ sample i) (k : ℕ) :
    sampleTopKEndpointLoss M sample k ≤ (min k n : ℝ) * (M - L) := by
  rw [sampleTopKEndpointLoss_eq_reflectedBottomKSum]
  exact reflectedBottomKSum_le_of_forall_lower M L hL k

theorem ascendingOrderStatistic_integrable_of_ae_bounds
    (L U : ℝ) {n : ℕ} (μ : MeasureTheory.Measure (Fin n → ℝ))
    [MeasureTheory.IsFiniteMeasure μ] (rank : Fin n)
    (h_bounds :
      ∀ᵐ sample ∂μ, ∀ i : Fin n, L ≤ sample i ∧ sample i ≤ U) :
    MeasureTheory.Integrable
      (fun sample : Fin n → ℝ => ascendingOrderStatistic sample rank) μ := by
  refine MeasureTheory.Integrable.of_mem_Icc L U
    (ascendingOrderStatistic_measurable rank).aemeasurable ?_
  filter_upwards [h_bounds] with sample hsample
  exact ⟨
    le_ascendingOrderStatistic_of_forall_le
      (fun i => (hsample i).1) rank,
    ascendingOrderStatistic_le_of_forall_le
      (fun i => (hsample i).2) rank⟩

theorem upperOrderStatistic_integrable_of_ae_bounds
    (L U : ℝ) {n : ℕ} (μ : MeasureTheory.Measure (Fin n → ℝ))
    [MeasureTheory.IsFiniteMeasure μ] (rankFromTop : Fin n)
    (h_bounds :
      ∀ᵐ sample ∂μ, ∀ i : Fin n, L ≤ sample i ∧ sample i ≤ U) :
    MeasureTheory.Integrable
      (fun sample : Fin n → ℝ => upperOrderStatistic sample rankFromTop) μ :=
  ascendingOrderStatistic_integrable_of_ae_bounds
    L U μ rankFromTop.rev h_bounds

theorem reflectedAscendingOrderStatistic_integrable_of_ae_bounds
    (M L : ℝ) {n : ℕ} (μ : MeasureTheory.Measure (Fin n → ℝ))
    [MeasureTheory.IsFiniteMeasure μ] (rank : Fin n)
    (h_bounds :
      ∀ᵐ sample ∂μ, ∀ i : Fin n, L ≤ sample i ∧ sample i ≤ M) :
    MeasureTheory.Integrable
      (fun sample : Fin n → ℝ =>
        ascendingOrderStatistic (reflectedSample M sample) rank) μ := by
  refine MeasureTheory.Integrable.of_mem_Icc 0 (M - L)
    (reflectedAscendingOrderStatistic_measurable M rank).aemeasurable ?_
  filter_upwards [h_bounds] with sample hsample
  exact ⟨
    le_ascendingOrderStatistic_of_forall_le
      (reflectedSample_nonneg_of_forall_le M
        (fun i => (hsample i).2)) rank,
    ascendingOrderStatistic_le_of_forall_le
      (reflectedSample_le_of_forall_lower M L
        (fun i => (hsample i).1)) rank⟩

theorem sampleTopKSum_integrable_of_ae_bounds
    (L U : ℝ) {n : ℕ} (μ : MeasureTheory.Measure (Fin n → ℝ))
    [MeasureTheory.IsFiniteMeasure μ] (k : ℕ)
    (h_bounds :
      ∀ᵐ sample ∂μ, ∀ i : Fin n, L ≤ sample i ∧ sample i ≤ U) :
    MeasureTheory.Integrable
      (fun sample : Fin n → ℝ => sampleTopKSum sample k) μ := by
  refine MeasureTheory.Integrable.of_mem_Icc
    ((min k n : ℝ) * L) ((min k n : ℝ) * U)
    (sampleTopKSum_measurable k).aemeasurable ?_
  filter_upwards [h_bounds] with sample hsample
  exact ⟨
    sampleTopKSum_ge_of_forall_lower
      (fun i => (hsample i).1) k,
    sampleTopKSum_le_of_forall_le
      (fun i => (hsample i).2) k⟩

theorem sampleTopKEndpointLoss_integrable_of_ae_bounds
    (M L : ℝ) {n : ℕ} (μ : MeasureTheory.Measure (Fin n → ℝ))
    [MeasureTheory.IsFiniteMeasure μ] (k : ℕ)
    (h_bounds :
      ∀ᵐ sample ∂μ, ∀ i : Fin n, L ≤ sample i ∧ sample i ≤ M) :
    MeasureTheory.Integrable
      (fun sample : Fin n → ℝ => sampleTopKEndpointLoss M sample k) μ := by
  refine MeasureTheory.Integrable.of_mem_Icc 0 ((min k n : ℝ) * (M - L))
    (sampleTopKEndpointLoss_measurable M k).aemeasurable ?_
  filter_upwards [h_bounds] with sample hsample
  exact ⟨
    sampleTopKEndpointLoss_nonneg_of_forall_le
      M (fun i => (hsample i).2) k,
    sampleTopKEndpointLoss_le_of_forall_bounds
      M L (fun i => (hsample i).1) k⟩

theorem reflectedBottomKSum_integrable_of_ae_bounds
    (M L : ℝ) {n : ℕ} (μ : MeasureTheory.Measure (Fin n → ℝ))
    [MeasureTheory.IsFiniteMeasure μ] (k : ℕ)
    (h_bounds :
      ∀ᵐ sample ∂μ, ∀ i : Fin n, L ≤ sample i ∧ sample i ≤ M) :
    MeasureTheory.Integrable
      (fun sample : Fin n → ℝ => reflectedBottomKSum M sample k) μ := by
  refine MeasureTheory.Integrable.of_mem_Icc 0 ((min k n : ℝ) * (M - L))
    (reflectedBottomKSum_measurable M k).aemeasurable ?_
  filter_upwards [h_bounds] with sample hsample
  exact ⟨
    reflectedBottomKSum_nonneg_of_forall_le
      M (fun i => (hsample i).2) k,
    reflectedBottomKSum_le_of_forall_lower
      M L (fun i => (hsample i).1) k⟩

theorem integral_Ioi_indicator_lt_eq
    (a : ℝ) (ha : 0 ≤ a) :
    ∫ x in Set.Ioi (0 : ℝ), (if x < a then (1 : ℝ) else 0) = a := by
  have hindicator :
      (fun x : ℝ => if x < a then (1 : ℝ) else 0) =
        (Set.Iio a).indicator (fun _x : ℝ => (1 : ℝ)) := by
    funext x
    by_cases hx : x < a <;> simp [hx]
  rw [hindicator, MeasureTheory.setIntegral_indicator measurableSet_Iio]
  have hset : Set.Ioi (0 : ℝ) ∩ Set.Iio a = Set.Ioo (0 : ℝ) a := by
    ext x
    simp [and_comm]
  rw [hset, MeasureTheory.setIntegral_const]
  simp [Real.volume_real_Ioo_of_le ha]

theorem thresholdIndicator_integrable_Ioi (a : ℝ) :
    MeasureTheory.Integrable
      (fun x : ℝ => if x < a then (1 : ℝ) else 0)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hindicator :
      (fun x : ℝ => if x < a then (1 : ℝ) else 0) =
        (Set.Iio a).indicator (fun _x : ℝ => (1 : ℝ)) := by
    funext x
    by_cases hx : x < a <;> simp [hx]
  rw [hindicator]
  have hfinite :
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) (Set.Iio a) ≠ ⊤ := by
    rw [MeasureTheory.Measure.restrict_apply measurableSet_Iio]
    have hset : Set.Iio a ∩ Set.Ioi (0 : ℝ) = Set.Ioo (0 : ℝ) a := by
      ext x
      simp [and_comm]
    rw [hset, Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  exact (MeasureTheory.integrableOn_const
    (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
    (s := Set.Iio a) (C := (1 : ℝ)) hfinite).integrable_indicator
      measurableSet_Iio

theorem ascendingOrderStatistic_rank_count_le_iff
    {n : ℕ} (sample : Fin n → ℝ) (rank : Fin n) (x : ℝ) :
    (Finset.univ.filter (fun i : Fin n => sample i ≤ x)).card ≤ rank.val ↔
      x < ascendingOrderStatistic sample rank := by
  rw [← not_iff_not]
  push Not
  exact (ascendingOrderStatistic_le_iff_rank_lt_card_le sample rank x).symm

theorem ascendingOrderStatistic_rank_count_indicator_integrable
    {n : ℕ} (sample : Fin n → ℝ) (rank : Fin n) :
    MeasureTheory.Integrable
      (fun x : ℝ =>
        if (Finset.univ.filter (fun i : Fin n => sample i ≤ x)).card ≤ rank.val
        then (1 : ℝ) else 0)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  refine (thresholdIndicator_integrable_Ioi
    (ascendingOrderStatistic sample rank)).congr ?_
  filter_upwards with x
  have hiff := ascendingOrderStatistic_rank_count_le_iff sample rank x
  by_cases hcount :
      (Finset.univ.filter (fun i : Fin n => sample i ≤ x)).card ≤ rank.val
  · have hx : x < ascendingOrderStatistic sample rank := hiff.mp hcount
    simp [hcount, hx]
  · have hx : ¬ x < ascendingOrderStatistic sample rank := by
      intro hx
      exact hcount (hiff.mpr hx)
    simp [hcount, hx]

theorem ascendingOrderStatistic_eq_integral_rank_count_indicator
    {n : ℕ} (sample : Fin n → ℝ) (rank : Fin n)
    (h_nonneg : ∀ i, 0 ≤ sample i) :
    ascendingOrderStatistic sample rank =
      ∫ x in Set.Ioi (0 : ℝ),
        if (Finset.univ.filter (fun i : Fin n => sample i ≤ x)).card ≤ rank.val
        then (1 : ℝ) else 0 := by
  have hstat_nonneg : 0 ≤ ascendingOrderStatistic sample rank :=
    le_ascendingOrderStatistic_of_forall_le h_nonneg rank
  rw [← integral_Ioi_indicator_lt_eq
    (ascendingOrderStatistic sample rank) hstat_nonneg]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
  intro x _hx
  have hiff := ascendingOrderStatistic_rank_count_le_iff sample rank x
  by_cases hcount :
      (Finset.univ.filter (fun i : Fin n => sample i ≤ x)).card ≤ rank.val
  · have hx : x < ascendingOrderStatistic sample rank := hiff.mp hcount
    simp [hcount, hx]
  · have hx : ¬ x < ascendingOrderStatistic sample rank := by
      intro hx
      exact hcount (hiff.mpr hx)
    simp [hcount, hx]

theorem reflectedBottomKSum_eq_integral_rank_count_indicator
    (M : ℝ) {n : ℕ} (sample : Fin n → ℝ) (k : ℕ)
    (hM : ∀ i, sample i ≤ M) :
    reflectedBottomKSum M sample k =
      ∫ x in Set.Ioi (0 : ℝ),
        ∑ i : Fin (min k n),
          if (Finset.univ.filter
              (fun j : Fin n => reflectedSample M sample j ≤ x)).card ≤
              (topKRankEmbedding k n i).val
          then (1 : ℝ) else 0 := by
  have h_nonneg : ∀ i : Fin n, 0 ≤ reflectedSample M sample i :=
    reflectedSample_nonneg_of_forall_le M hM
  calc
    reflectedBottomKSum M sample k =
        ∑ i : Fin (min k n),
          ∫ x in Set.Ioi (0 : ℝ),
            if (Finset.univ.filter
                (fun j : Fin n => reflectedSample M sample j ≤ x)).card ≤
                (topKRankEmbedding k n i).val
            then (1 : ℝ) else 0 := by
          unfold reflectedBottomKSum
          refine Finset.sum_congr rfl ?_
          intro i _hi
          exact ascendingOrderStatistic_eq_integral_rank_count_indicator
            (reflectedSample M sample) (topKRankEmbedding k n i) h_nonneg
    _ = ∫ x in Set.Ioi (0 : ℝ),
        ∑ i : Fin (min k n),
          if (Finset.univ.filter
              (fun j : Fin n => reflectedSample M sample j ≤ x)).card ≤
              (topKRankEmbedding k n i).val
          then (1 : ℝ) else 0 := by
          rw [MeasureTheory.integral_finset_sum]
          intro i _hi
          exact ascendingOrderStatistic_rank_count_indicator_integrable
            (reflectedSample M sample) (topKRankEmbedding k n i)

/--
Threshold-count layer whose positive-threshold integral recovers the reflected
bottom-`k` sum.  The event counts reflected coordinates below threshold `x`;
for rank `r`, the indicator is active exactly when the `r`th reflected order
statistic is above `x`.
-/
def reflectedBottomKRankCountLayer
    (M : ℝ) {n : ℕ} (k : ℕ) (sample : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ i : Fin (min k n),
    if (Finset.univ.filter
        (fun j : Fin n => reflectedSample M sample j ≤ x)).card ≤
        (topKRankEmbedding k n i).val
    then (1 : ℝ) else 0

theorem reflectedBottomKRankCountLayer_nonneg
    (M : ℝ) {n : ℕ} (k : ℕ) (sample : Fin n → ℝ) (x : ℝ) :
    0 ≤ reflectedBottomKRankCountLayer M k sample x := by
  classical
  unfold reflectedBottomKRankCountLayer
  exact Finset.sum_nonneg (fun i _hi => by split <;> norm_num)

theorem reflectedBottomKRankCountLayer_le_card
    (M : ℝ) {n : ℕ} (k : ℕ) (sample : Fin n → ℝ) (x : ℝ) :
    reflectedBottomKRankCountLayer M k sample x ≤ (min k n : ℝ) := by
  classical
  unfold reflectedBottomKRankCountLayer
  calc
    (∑ i : Fin (min k n),
        if (Finset.univ.filter
            (fun j : Fin n => reflectedSample M sample j ≤ x)).card ≤
            (topKRankEmbedding k n i).val
        then (1 : ℝ) else 0)
        ≤ ∑ _i : Fin (min k n), (1 : ℝ) := by
          refine Finset.sum_le_sum ?_
          intro i _hi
          split <;> norm_num
    _ = (min k n : ℝ) := by simp

theorem reflectedCoordinate_le_threshold_count_measurable_prod
    (M : ℝ) {n : ℕ} :
    Measurable
      (fun z : (Fin n → ℝ) × ℝ =>
        (Finset.univ.filter
          (fun i : Fin n => reflectedSample M z.1 i ≤ z.2)).card) := by
  classical
  have hsum :
      Measurable
        (fun z : (Fin n → ℝ) × ℝ =>
          ∑ i : Fin n,
            if reflectedSample M z.1 i ≤ z.2 then (1 : ℕ) else 0) := by
    exact Finset.measurable_sum Finset.univ
      (fun i _hi =>
        Measurable.ite
          (measurableSet_le
            (measurable_const.sub
              ((measurable_pi_apply i).comp measurable_fst))
            measurable_snd)
          measurable_const measurable_const)
  convert hsum using 1
  ext z
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

theorem reflectedRankCountIndicator_measurable_prod
    (M : ℝ) {n : ℕ} (rank : ℕ) :
    Measurable
      (fun z : (Fin n → ℝ) × ℝ =>
        if (Finset.univ.filter
            (fun i : Fin n => reflectedSample M z.1 i ≤ z.2)).card ≤ rank
        then (1 : ℝ) else 0) := by
  exact Measurable.ite
    (measurableSet_le
      (reflectedCoordinate_le_threshold_count_measurable_prod M)
      measurable_const)
    measurable_const measurable_const

theorem reflectedBottomKRankCountLayer_measurable_prod
    (M : ℝ) {n : ℕ} (k : ℕ) :
    Measurable
      (fun z : (Fin n → ℝ) × ℝ =>
        reflectedBottomKRankCountLayer M k z.1 z.2) := by
  unfold reflectedBottomKRankCountLayer
  exact Finset.measurable_sum Finset.univ
    (fun i _hi =>
      reflectedRankCountIndicator_measurable_prod
        M (topKRankEmbedding k n i).val)

theorem reflectedBottomKRankCountLayer_integrable_Ioi
    (M : ℝ) {n : ℕ} (k : ℕ) (sample : Fin n → ℝ) :
    MeasureTheory.Integrable
      (fun x : ℝ => reflectedBottomKRankCountLayer M k sample x)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  unfold reflectedBottomKRankCountLayer
  exact MeasureTheory.integrable_finset_sum Finset.univ
    (fun i _hi =>
      ascendingOrderStatistic_rank_count_indicator_integrable
        (reflectedSample M sample) (topKRankEmbedding k n i))

theorem reflectedBottomKSum_eq_integral_rank_count_layer
    (M : ℝ) {n : ℕ} (sample : Fin n → ℝ) (k : ℕ)
    (hM : ∀ i, sample i ≤ M) :
    reflectedBottomKSum M sample k =
      ∫ x in Set.Ioi (0 : ℝ),
        reflectedBottomKRankCountLayer M k sample x := by
  simpa [reflectedBottomKRankCountLayer] using
    reflectedBottomKSum_eq_integral_rank_count_indicator M sample k hM

theorem reflectedBottomKRankCountLayer_integrable_prod_of_ae_bounds
    (M L : ℝ) {n : ℕ} (μ : MeasureTheory.Measure (Fin n → ℝ))
    [MeasureTheory.IsFiniteMeasure μ] (k : ℕ)
    (h_bounds :
      ∀ᵐ sample ∂μ, ∀ i : Fin n, L ≤ sample i ∧ sample i ≤ M) :
    MeasureTheory.Integrable
      (fun z : (Fin n → ℝ) × ℝ =>
        reflectedBottomKRankCountLayer M k z.1 z.2)
      (μ.prod (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) := by
  let ν := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
  let f : (Fin n → ℝ) × ℝ → ℝ :=
    fun z => reflectedBottomKRankCountLayer M k z.1 z.2
  have hf_meas : Measurable f := by
    simpa [f] using reflectedBottomKRankCountLayer_measurable_prod (M := M) (n := n) k
  have hsections :
      ∀ᵐ sample ∂μ,
        MeasureTheory.Integrable (fun x : ℝ => f (sample, x)) ν := by
    filter_upwards with sample
    simpa [f, ν] using
      reflectedBottomKRankCountLayer_integrable_Ioi M k sample
  have hinner_eq :
      (fun sample : Fin n → ℝ => ∫ x, ‖f (sample, x)‖ ∂ν) =ᵐ[μ]
        fun sample : Fin n → ℝ => reflectedBottomKSum M sample k := by
    filter_upwards [h_bounds] with sample hsample
    have hnorm :
        ∫ x, ‖f (sample, x)‖ ∂ν =
          ∫ x, f (sample, x) ∂ν := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with x
      have hnonneg : 0 ≤ f (sample, x) := by
        simpa [f] using reflectedBottomKRankCountLayer_nonneg M k sample x
      simp [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    calc
      ∫ x, ‖f (sample, x)‖ ∂ν =
          ∫ x, f (sample, x) ∂ν := hnorm
      _ =
          ∫ x in Set.Ioi (0 : ℝ),
            reflectedBottomKRankCountLayer M k sample x := by
            rfl
      _ = reflectedBottomKSum M sample k := by
            exact (reflectedBottomKSum_eq_integral_rank_count_layer
              M sample k (fun i => (hsample i).2)).symm
  have hinner_int :
      MeasureTheory.Integrable
        (fun sample : Fin n → ℝ => ∫ x, ‖f (sample, x)‖ ∂ν) μ := by
    exact (reflectedBottomKSum_integrable_of_ae_bounds M L μ k h_bounds).congr
      hinner_eq.symm
  have hf_int : MeasureTheory.Integrable f (μ.prod ν) := by
    exact (MeasureTheory.integrable_prod_iff hf_meas.aestronglyMeasurable).2
      ⟨hsections, hinner_int⟩
  simpa [ν, f] using hf_int

/-!
## Expected finite-sample order statistics

These declarations are still distribution-agnostic: the sample law is any
probability measure on finite real tuples.  Distribution files can instantiate
the measure as an iid product law and then prove measurability/integrability or
closed forms separately.
-/

/-- Expected ascending order statistic under a finite-sample law. -/
def expectedAscendingOrderStatistic {n : ℕ}
    (μ : MeasureTheory.Measure (Fin n → ℝ)) (rank : Fin n) : ℝ :=
  ∫ sample, ascendingOrderStatistic sample rank ∂μ

/-- Expected upper order statistic under a finite-sample law. -/
def expectedUpperOrderStatistic {n : ℕ}
    (μ : MeasureTheory.Measure (Fin n → ℝ)) (rankFromTop : Fin n) : ℝ :=
  ∫ sample, upperOrderStatistic sample rankFromTop ∂μ

/-- Expected maximum/top order statistic under a nonempty finite-sample law. -/
def expectedTopOrderStatistic {n : ℕ} [NeZero n]
    (μ : MeasureTheory.Measure (Fin n → ℝ)) : ℝ :=
  expectedUpperOrderStatistic μ (topSampleRank (n := n))

/--
Expected maximum/top order statistic for a sequence of nonempty finite-sample
laws indexed by `n`, with sample size `n + 1`.
-/
def expectedTopOrderStatisticSeq
    (sampleLaw : ∀ n : ℕ, MeasureTheory.Measure (Fin (n + 1) → ℝ))
    (n : ℕ) : ℝ :=
  expectedTopOrderStatistic (sampleLaw n)

/--
Chebyshev bound for the top order statistic around its own expectation,
bridging variance calculations for maximum order statistics to
deviation-probability interfaces used by matching-market concentration
arguments.
-/
theorem topOrderDeviationProbability_le_variance_div_sq
    {n : ℕ} [NeZero n]
    (μ : MeasureTheory.Measure (Fin n → ℝ)) [MeasureTheory.IsFiniteMeasure μ]
    (hmem :
      MeasureTheory.MemLp
        (fun sample : Fin n → ℝ =>
          upperOrderStatistic sample (topSampleRank (n := n))) 2 μ)
    {ε : ℝ} (hε : 0 < ε) :
    topOrderDeviationProbability μ (expectedTopOrderStatistic μ) ε ≤
      ProbabilityTheory.variance
        (fun sample : Fin n → ℝ =>
          upperOrderStatistic sample (topSampleRank (n := n))) μ / ε ^ 2 := by
  let X : (Fin n → ℝ) → ℝ :=
    fun sample => upperOrderStatistic sample (topSampleRank (n := n))
  have hvariance_nonneg :
      0 ≤ ProbabilityTheory.variance X μ / ε ^ 2 := by
    exact div_nonneg
      (ProbabilityTheory.variance_nonneg X μ)
      (sq_nonneg ε)
  have hchebyshev_enn :
      μ {sample : Fin n → ℝ | ε ≤ |X sample - μ[X]|} ≤
        ENNReal.ofReal (ProbabilityTheory.variance X μ / ε ^ 2) :=
    ProbabilityTheory.meas_ge_le_variance_div_sq
      (μ := μ) (X := X) hmem hε
  have hchebyshev_real :
      μ.real {sample : Fin n → ℝ | ε ≤ |X sample - μ[X]|} ≤
        ProbabilityTheory.variance X μ / ε ^ 2 :=
    (ENNReal.le_ofReal_iff_toReal_le
      (measure_ne_top μ {sample : Fin n → ℝ | ε ≤ |X sample - μ[X]|})
      hvariance_nonneg).1 hchebyshev_enn
  have hsubset :
      {sample : Fin n → ℝ |
        ε < |X sample - expectedTopOrderStatistic μ|} ⊆
      {sample : Fin n → ℝ | ε ≤ |X sample - μ[X]|} := by
    intro sample hsample
    exact le_of_lt (by
      simpa [X, expectedTopOrderStatistic, expectedUpperOrderStatistic]
        using hsample)
  calc
    topOrderDeviationProbability μ (expectedTopOrderStatistic μ) ε
        = μ.real
            {sample : Fin n → ℝ |
              ε < |X sample - expectedTopOrderStatistic μ|} := by
            rfl
    _ ≤ μ.real {sample : Fin n → ℝ | ε ≤ |X sample - μ[X]|} :=
        measureReal_mono (μ := μ) hsubset (measure_ne_top μ _)
    _ ≤ ProbabilityTheory.variance X μ / ε ^ 2 :=
        hchebyshev_real

/--
Variance-bound route to top-order-statistic concentration.  The finite-measure
and `L²` hypotheses are explicit so downstream paper files can expose the
source variance premise instead of a raw Chebyshev inequality.
-/
theorem TopOrderDeviationConcentrating.of_variance_bound
    {sampleLaw : ∀ n : ℕ, MeasureTheory.Measure (Fin (n + 1) → ℝ)}
    {varianceBound : ℕ → ℝ}
    (hfinite : ∀ n : ℕ, MeasureTheory.IsFiniteMeasure (sampleLaw n))
    (hvariance_zero : Tendsto varianceBound atTop (nhds 0))
    (hmem :
      ∀ᶠ n : ℕ in atTop,
        MeasureTheory.MemLp
          (fun sample : Fin (n + 1) → ℝ =>
            upperOrderStatistic sample (topSampleRank (n := n + 1))) 2
          (sampleLaw n))
    (hvariance_bound :
      ∀ᶠ n : ℕ in atTop,
        ProbabilityTheory.variance
          (fun sample : Fin (n + 1) → ℝ =>
            upperOrderStatistic sample (topSampleRank (n := n + 1)))
          (sampleLaw n) ≤ varianceBound n) :
    TopOrderDeviationConcentrating sampleLaw
      (expectedTopOrderStatisticSeq sampleLaw) := by
  refine TopOrderDeviationConcentrating.of_chebyshev_bound
    hvariance_zero ?_
  intro ε hε
  filter_upwards [hmem, hvariance_bound] with n hnmem hnvariance
  letI : MeasureTheory.IsFiniteMeasure (sampleLaw n) := hfinite n
  have hdeviation :
      topOrderDeviationProbability
          (sampleLaw n)
          (expectedTopOrderStatisticSeq sampleLaw n) ε ≤
        ProbabilityTheory.variance
          (fun sample : Fin (n + 1) → ℝ =>
            upperOrderStatistic sample (topSampleRank (n := n + 1)))
          (sampleLaw n) / ε ^ 2 := by
    simpa [expectedTopOrderStatisticSeq] using
      topOrderDeviationProbability_le_variance_div_sq
        (μ := sampleLaw n) hnmem hε
  have hdivide :
      ProbabilityTheory.variance
          (fun sample : Fin (n + 1) → ℝ =>
            upperOrderStatistic sample (topSampleRank (n := n + 1)))
          (sampleLaw n) / ε ^ 2 ≤
        varianceBound n / ε ^ 2 :=
    div_le_div_of_nonneg_right hnvariance (sq_nonneg ε)
  exact hdeviation.trans hdivide

/--
Layer-cake form for a nonnegative integrable upper order statistic.

Distribution-specific files can combine this with their threshold-event
probability formulas to derive closed-form expected order statistics.
-/
theorem expectedUpperOrderStatistic_eq_integral_tail_probability_of_nonneg
    {n : ℕ} (μ : MeasureTheory.Measure (Fin n → ℝ))
    (rankFromTop : Fin n)
    (h_nonneg :
      0 ≤ᵐ[μ] fun sample : Fin n → ℝ =>
        upperOrderStatistic sample rankFromTop)
    (h_integrable :
      MeasureTheory.Integrable
        (fun sample : Fin n → ℝ =>
          upperOrderStatistic sample rankFromTop) μ) :
    expectedUpperOrderStatistic μ rankFromTop =
      ∫ x in Set.Ioi (0 : ℝ),
        μ.real
          {sample : Fin n → ℝ |
            x < upperOrderStatistic sample rankFromTop} := by
  simpa [expectedUpperOrderStatistic] using
    h_integrable.integral_eq_integral_meas_lt h_nonneg

/--
Layer-cake form for a nonnegative integrable ascending order statistic.

This is the bottom-indexed counterpart of
`expectedUpperOrderStatistic_eq_integral_tail_probability_of_nonneg`.
-/
theorem expectedAscendingOrderStatistic_eq_integral_tail_probability_of_nonneg
    {n : ℕ} (μ : MeasureTheory.Measure (Fin n → ℝ))
    (rank : Fin n)
    (h_nonneg :
      0 ≤ᵐ[μ] fun sample : Fin n → ℝ =>
        ascendingOrderStatistic sample rank)
    (h_integrable :
      MeasureTheory.Integrable
        (fun sample : Fin n → ℝ =>
          ascendingOrderStatistic sample rank) μ) :
    expectedAscendingOrderStatistic μ rank =
      ∫ x in Set.Ioi (0 : ℝ),
        μ.real
          {sample : Fin n → ℝ |
            x < ascendingOrderStatistic sample rank} := by
  simpa [expectedAscendingOrderStatistic] using
    h_integrable.integral_eq_integral_meas_lt h_nonneg

/-- Expected pointwise top-`k` sum under a finite-sample law. -/
def expectedSampleTopKSum {n : ℕ}
    (μ : MeasureTheory.Measure (Fin n → ℝ)) (k : ℕ) : ℝ :=
  ∫ sample, sampleTopKSum sample k ∂μ

theorem expectedSampleTopKSum_eq_integral_topKSumOn_of_ae_nonneg
    {n : ℕ} (μ : MeasureTheory.Measure (Fin n → ℝ)) (k : ℕ)
    (h_nonneg : ∀ᵐ sample ∂μ, ∀ i, 0 ≤ sample i) :
    expectedSampleTopKSum μ k =
      ∫ sample, topKSumOn k sample ∂μ := by
  unfold expectedSampleTopKSum
  exact MeasureTheory.integral_congr_ae
    (h_nonneg.mono fun sample hsample =>
      (topKSumOn_eq_sampleTopKSum_of_forall_nonneg sample k hsample).symm)

theorem integral_topKSumOn_pi_option_eq_prod
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : MeasureTheory.Measure ℝ) [MeasureTheory.SigmaFinite μ] (k : ℕ) :
    (∫ sample : Option ι → ℝ, topKSumOn k sample
        ∂MeasureTheory.Measure.pi (fun _ : Option ι => μ)) =
      ∫ z : (ι → ℝ) × ℝ,
        topKSumOn k (extendSample z.1 z.2)
          ∂((MeasureTheory.Measure.pi (fun _ : ι => μ)).prod μ) := by
  let e : ((ι → ℝ) × ℝ) ≃ᵐ (Option ι → ℝ) :=
    (optionSampleMeasurableEquivProd ι).symm
  have hmap :
      (((MeasureTheory.Measure.pi (fun _ : ι => μ)).prod μ).map e) =
        MeasureTheory.Measure.pi (fun _ : Option ι => μ) := by
    simpa [e] using pi_map_optionSampleMeasurableEquivProd_symm
      (ι := ι) μ
  calc
    (∫ sample : Option ι → ℝ, topKSumOn k sample
        ∂MeasureTheory.Measure.pi (fun _ : Option ι => μ))
        =
      ∫ sample : Option ι → ℝ, topKSumOn k sample
        ∂(((MeasureTheory.Measure.pi (fun _ : ι => μ)).prod μ).map e) := by
          rw [hmap]
    _ =
      ∫ z : (ι → ℝ) × ℝ, topKSumOn k (e z)
        ∂((MeasureTheory.Measure.pi (fun _ : ι => μ)).prod μ) := by
          rw [MeasureTheory.integral_map_equiv e]
    _ =
      ∫ z : (ι → ℝ) × ℝ,
        topKSumOn k (extendSample z.1 z.2)
          ∂((MeasureTheory.Measure.pi (fun _ : ι => μ)).prod μ) := by
          rfl

theorem integral_topKSumOn_pi_fin_succ_eq_prod
    (μ : MeasureTheory.Measure ℝ) [MeasureTheory.SigmaFinite μ]
    (k q : ℕ) :
    (∫ sample : Fin (q + 1) → ℝ, topKSumOn k sample
        ∂MeasureTheory.Measure.pi (fun _ : Fin (q + 1) => μ)) =
      ∫ z : (Fin q → ℝ) × ℝ,
        topKSumOn k (extendSample z.1 z.2)
          ∂((MeasureTheory.Measure.pi (fun _ : Fin q => μ)).prod μ) := by
  classical
  let eFin : Option (Fin q) ≃ Fin (q + 1) :=
    AppliedModelingLib.optionFinEquivFinSucc q
  let e :
      (Option (Fin q) → ℝ) ≃ᵐ (Fin (q + 1) → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin (q + 1) => ℝ) eFin
  have hmp :
      MeasureTheory.MeasurePreserving e
        (MeasureTheory.Measure.pi (fun _ : Option (Fin q) => μ))
        (MeasureTheory.Measure.pi (fun _ : Fin (q + 1) => μ)) := by
    simpa [e, eFin] using
      (MeasureTheory.measurePreserving_piCongrLeft
        (fun _ : Fin (q + 1) => μ) eFin)
  have hreindex :
      (∫ sample : Option (Fin q) → ℝ, topKSumOn k (e sample)
          ∂MeasureTheory.Measure.pi (fun _ : Option (Fin q) => μ)) =
        ∫ sample : Option (Fin q) → ℝ, topKSumOn k sample
          ∂MeasureTheory.Measure.pi (fun _ : Option (Fin q) => μ) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro sample
    have htop :=
      topKSumOn_comp_equiv (e := eFin) (k := k)
        (v := e sample)
    simpa [e, MeasurableEquiv.piCongrLeft_apply_apply] using htop.symm
  calc
    (∫ sample : Fin (q + 1) → ℝ, topKSumOn k sample
        ∂MeasureTheory.Measure.pi (fun _ : Fin (q + 1) => μ))
        =
      ∫ sample : Option (Fin q) → ℝ, topKSumOn k (e sample)
        ∂MeasureTheory.Measure.pi (fun _ : Option (Fin q) => μ) := by
          exact (hmp.integral_comp' (g := fun sample : Fin (q + 1) → ℝ =>
            topKSumOn k sample)).symm
    _ =
      ∫ sample : Option (Fin q) → ℝ, topKSumOn k sample
        ∂MeasureTheory.Measure.pi (fun _ : Option (Fin q) => μ) := hreindex
    _ =
      ∫ z : (Fin q → ℝ) × ℝ,
        topKSumOn k (extendSample z.1 z.2)
          ∂((MeasureTheory.Measure.pi (fun _ : Fin q => μ)).prod μ) :=
        integral_topKSumOn_pi_option_eq_prod μ k

theorem expectedSampleTopKSum_pi_succ_sub_eq_integral_topKSumOn_extend_sub
    (μ : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure μ]
    {k q : ℕ}
    (h_nonneg_q :
      ∀ᵐ sample ∂MeasureTheory.Measure.pi (fun _ : Fin q => μ),
        ∀ i, 0 ≤ sample i)
    (h_nonneg_succ :
      ∀ᵐ sample ∂MeasureTheory.Measure.pi (fun _ : Fin (q + 1) => μ),
        ∀ i, 0 ≤ sample i)
    (h_int_extend :
      MeasureTheory.Integrable
        (fun z : (Fin q → ℝ) × ℝ =>
          topKSumOn k (extendSample z.1 z.2))
        ((MeasureTheory.Measure.pi (fun _ : Fin q => μ)).prod μ))
    (h_int_old :
      MeasureTheory.Integrable
        (fun z : (Fin q → ℝ) × ℝ => topKSumOn k z.1)
        ((MeasureTheory.Measure.pi (fun _ : Fin q => μ)).prod μ)) :
    expectedSampleTopKSum
        (MeasureTheory.Measure.pi (fun _ : Fin (q + 1) => μ)) k -
      expectedSampleTopKSum
        (MeasureTheory.Measure.pi (fun _ : Fin q => μ)) k =
      ∫ z : (Fin q → ℝ) × ℝ,
        (topKSumOn k (extendSample z.1 z.2) - topKSumOn k z.1)
          ∂((MeasureTheory.Measure.pi (fun _ : Fin q => μ)).prod μ) := by
  rw [expectedSampleTopKSum_eq_integral_topKSumOn_of_ae_nonneg
      (MeasureTheory.Measure.pi (fun _ : Fin (q + 1) => μ)) k h_nonneg_succ,
    expectedSampleTopKSum_eq_integral_topKSumOn_of_ae_nonneg
      (MeasureTheory.Measure.pi (fun _ : Fin q => μ)) k h_nonneg_q,
    integral_topKSumOn_pi_fin_succ_eq_prod]
  have hold :
      (∫ z : (Fin q → ℝ) × ℝ, topKSumOn k z.1
          ∂((MeasureTheory.Measure.pi (fun _ : Fin q => μ)).prod μ)) =
        ∫ sample : Fin q → ℝ, topKSumOn k sample
          ∂MeasureTheory.Measure.pi (fun _ : Fin q => μ) := by
    rw [MeasureTheory.integral_fun_fst
      (μ := MeasureTheory.Measure.pi (fun _ : Fin q => μ))
      (ν := μ)
      (f := fun sample : Fin q → ℝ => topKSumOn k sample)]
    simp [MeasureTheory.probReal_univ]
  rw [← hold]
  rw [MeasureTheory.integral_sub h_int_extend h_int_old]

/--
If a bounded nonnegative one-dimensional law has positive mass below `b` and
positive mass above `a > b`, then adding one more iid draw strictly increases
the expected top-`k` value for every positive `k`.
-/
theorem expectedSampleTopKSum_pi_succ_sub_pos_of_mass_gap
    (μ : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure μ]
    {M b a : ℝ}
    (h_bounds : ∀ᵐ x ∂μ, 0 ≤ x ∧ x ≤ M)
    (hM_nonneg : 0 ≤ M)
    (hb_nonneg : 0 ≤ b)
    (hba : b < a)
    (hlow : 0 < μ (Set.Iio b))
    (hhigh : 0 < μ (Set.Ici a))
    {k q : ℕ} (hk_pos : 0 < k) :
    0 <
      expectedSampleTopKSum
          (MeasureTheory.Measure.pi (fun _ : Fin (q + 1) => μ)) k -
        expectedSampleTopKSum
          (MeasureTheory.Measure.pi (fun _ : Fin q => μ)) k := by
  classical
  let μq : MeasureTheory.Measure (Fin q → ℝ) :=
    MeasureTheory.Measure.pi (fun _ : Fin q => μ)
  let μprod : MeasureTheory.Measure ((Fin q → ℝ) × ℝ) := μq.prod μ
  let μoption : MeasureTheory.Measure (Option (Fin q) → ℝ) :=
    MeasureTheory.Measure.pi (fun _ : Option (Fin q) => μ)
  let inc : (Fin q → ℝ) × ℝ → ℝ :=
    fun z => topKSumOn k (extendSample z.1 z.2) - topKSumOn k z.1
  have h_bounds_q :
      ∀ᵐ sample ∂μq, ∀ i : Fin q, 0 ≤ sample i ∧ sample i ≤ M := by
    simpa [μq] using
      (productMeasure_forall_bounds_ae (ι := Fin q) μ h_bounds)
  have h_bounds_succ :
      ∀ᵐ sample ∂MeasureTheory.Measure.pi (fun _ : Fin (q + 1) => μ),
        ∀ i : Fin (q + 1), 0 ≤ sample i ∧ sample i ≤ M := by
    simpa using
      (productMeasure_forall_bounds_ae (ι := Fin (q + 1)) μ h_bounds)
  have h_nonneg_q :
      ∀ᵐ sample ∂MeasureTheory.Measure.pi (fun _ : Fin q => μ),
        ∀ i, 0 ≤ sample i := by
    simpa [μq] using h_bounds_q.mono (fun sample hsample i => (hsample i).1)
  have h_nonneg_succ :
      ∀ᵐ sample ∂MeasureTheory.Measure.pi (fun _ : Fin (q + 1) => μ),
        ∀ i, 0 ≤ sample i :=
    h_bounds_succ.mono (fun sample hsample i => (hsample i).1)
  have h_int_old_pi :
      MeasureTheory.Integrable
        (fun sample : Fin q → ℝ => topKSumOn k sample) μq :=
    topKSumOn_integrable_of_ae_nonneg_bounds M μq k
      hM_nonneg h_bounds_q
  have h_int_old :
      MeasureTheory.Integrable
        (fun z : (Fin q → ℝ) × ℝ => topKSumOn k z.1) μprod := by
    have hmp :
        MeasureTheory.MeasurePreserving
          (fun z : (Fin q → ℝ) × ℝ => z.1) μprod μq := by
      simpa [μprod, μq] using
        (MeasureTheory.measurePreserving_fst
          (μ := μq) (ν := μ))
    simpa [Function.comp_def] using
      hmp.integrable_comp_of_integrable h_int_old_pi
  have h_bounds_option :
      ∀ᵐ sample ∂μoption, ∀ i : Option (Fin q),
        0 ≤ sample i ∧ sample i ≤ M := by
    simpa [μoption] using
      (productMeasure_forall_bounds_ae
        (ι := Option (Fin q)) μ h_bounds)
  have h_int_option :
      MeasureTheory.Integrable
        (fun sample : Option (Fin q) → ℝ => topKSumOn k sample) μoption :=
    topKSumOn_integrable_of_ae_nonneg_bounds M μoption k
      hM_nonneg h_bounds_option
  let e : ((Fin q → ℝ) × ℝ) ≃ᵐ (Option (Fin q) → ℝ) :=
    (optionSampleMeasurableEquivProd (Fin q)).symm
  have hmap : μprod.map e = μoption := by
    simpa [μprod, μq, μoption, e] using
      (pi_map_optionSampleMeasurableEquivProd_symm
        (ι := Fin q) μ)
  have h_int_extend :
      MeasureTheory.Integrable
        (fun z : (Fin q → ℝ) × ℝ =>
          topKSumOn k (extendSample z.1 z.2)) μprod := by
    have hmp : MeasureTheory.MeasurePreserving e μprod μoption :=
      ⟨e.measurable, hmap⟩
    have hcomp :=
      hmp.integrable_comp_of_integrable h_int_option
    simpa [Function.comp_def, e, optionSampleMeasurableEquivProd] using hcomp
  have hdiff :=
    expectedSampleTopKSum_pi_succ_sub_eq_integral_topKSumOn_extend_sub
      (μ := μ) (k := k) (q := q)
      h_nonneg_q h_nonneg_succ h_int_extend h_int_old
  rw [hdiff]
  have hinc_nonneg : ∀ᵐ z ∂μprod, 0 ≤ inc z := by
    exact Filter.Eventually.of_forall (fun z => by
      dsimp [inc]
      exact sub_nonneg.mpr (topKSumOn_le_extend k z.1 z.2))
  have hinc_int : MeasureTheory.Integrable inc μprod := by
    exact h_int_extend.sub h_int_old
  change 0 < ∫ z, inc z ∂μprod
  rw [MeasureTheory.integral_pos_iff_support_of_nonneg_ae hinc_nonneg hinc_int]
  let R : Set ((Fin q → ℝ) × ℝ) :=
    (Set.pi Set.univ (fun _ : Fin q => Set.Iio b)) ×ˢ Set.Ici a
  have hlow_prod :
      0 < μq (Set.pi Set.univ (fun _ : Fin q => Set.Iio b)) := by
    simpa [μq] using
      (pi_univ_Iio_measure_pos (ι := Fin q) μ hlow)
  have hRpos : 0 < μprod R := by
    have hprod :
        μprod R =
          μq (Set.pi Set.univ (fun _ : Fin q => Set.Iio b)) *
            μ (Set.Ici a) := by
      simp [μprod, R]
    rw [hprod]
    exact ENNReal.mul_pos hlow_prod.ne' hhigh.ne'
  exact lt_of_lt_of_le hRpos (MeasureTheory.measure_mono (by
    intro z hz
    have hold_le : ∀ i : Fin q, z.1 i ≤ b := by
      intro i
      exact le_of_lt (hz.1 i (by simp))
    have hgap :=
      topKSumOn_extend_sub_ge_newValue_sub_bound_of_forall_le
        (ι := Fin q) k z.1 (bound := b) (newValue := z.2)
        hk_pos hb_nonneg hold_le
    have hnew_gap : 0 < z.2 - b := by
      have hz2 : a ≤ z.2 := hz.2
      linarith
    exact ne_of_gt (lt_of_lt_of_le hnew_gap hgap)))

/--
For an iid product sample below top-`k` capacity, the expected top-`k` value is
the number of draws times the one-draw mean.
-/
theorem expectedSampleTopKSum_pi_eq_card_mul_integral_of_card_le
    {n : ℕ} (μ : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure μ]
    (h_int : MeasureTheory.Integrable (fun x : ℝ => x) μ)
    (k : ℕ) (hnk : n ≤ k) :
    expectedSampleTopKSum (MeasureTheory.Measure.pi (fun _ : Fin n => μ)) k =
      (n : ℝ) * ∫ x, x ∂μ := by
  classical
  unfold expectedSampleTopKSum
  calc
    ∫ sample : Fin n → ℝ, sampleTopKSum sample k
        ∂MeasureTheory.Measure.pi (fun _ : Fin n => μ)
        = ∫ sample : Fin n → ℝ, ∑ i : Fin n, sample i
            ∂MeasureTheory.Measure.pi (fun _ : Fin n => μ) := by
          exact MeasureTheory.integral_congr_ae
            (Filter.Eventually.of_forall
              (fun sample => sampleTopKSum_eq_sum_of_card_le sample k hnk))
    _ = ∑ i : Fin n, ∫ sample : Fin n → ℝ, sample i
            ∂MeasureTheory.Measure.pi (fun _ : Fin n => μ) := by
          rw [MeasureTheory.integral_finset_sum]
          intro i _hi
          simpa using
            (MeasureTheory.integrable_eval
              (μ := fun _ : Fin n => μ) (i := i) h_int)
    _ = ∑ _i : Fin n, ∫ x, x ∂μ := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          simpa using
            (MeasureTheory.integral_comp_eval
              (μ := fun _ : Fin n => μ) (i := i)
              (f := fun x : ℝ => x) measurable_id.aestronglyMeasurable)
    _ = (n : ℝ) * ∫ x, x ∂μ := by
          simp [Fintype.card_fin, nsmul_eq_mul]

/--
Layer-cake form for a nonnegative integrable top-`k` sample sum.
-/
theorem expectedSampleTopKSum_eq_integral_tail_probability_of_nonneg
    {n : ℕ} (μ : MeasureTheory.Measure (Fin n → ℝ)) (k : ℕ)
    (h_nonneg :
      0 ≤ᵐ[μ] fun sample : Fin n → ℝ => sampleTopKSum sample k)
    (h_integrable :
      MeasureTheory.Integrable
        (fun sample : Fin n → ℝ => sampleTopKSum sample k) μ) :
    expectedSampleTopKSum μ k =
      ∫ x in Set.Ioi (0 : ℝ),
        μ.real
          {sample : Fin n → ℝ | x < sampleTopKSum sample k} := by
  simpa [expectedSampleTopKSum] using
    h_integrable.integral_eq_integral_meas_lt h_nonneg

/-- Expected reflected bottom-`k` sum under a finite-sample law. -/
def expectedReflectedBottomKSum (M : ℝ) {n : ℕ}
    (μ : MeasureTheory.Measure (Fin n → ℝ)) (k : ℕ) : ℝ :=
  ∫ sample, reflectedBottomKSum M sample k ∂μ

theorem expectedReflectedBottomKSum_eq_integral_rank_count_layer_of_integrable
    (M : ℝ) {n : ℕ} (μ : MeasureTheory.Measure (Fin n → ℝ)) (k : ℕ)
    [MeasureTheory.IsProbabilityMeasure μ]
    (hM : ∀ᵐ sample ∂μ, ∀ i, sample i ≤ M)
    (h_layer_integrable :
      MeasureTheory.Integrable
        (fun z : (Fin n → ℝ) × ℝ =>
          reflectedBottomKRankCountLayer M k z.1 z.2)
        (μ.prod (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))) :
    expectedReflectedBottomKSum M μ k =
      ∫ x in Set.Ioi (0 : ℝ),
        ∫ sample, reflectedBottomKRankCountLayer M k sample x ∂μ := by
  let ν := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
  let f : (Fin n → ℝ) → ℝ → ℝ :=
    fun sample x => reflectedBottomKRankCountLayer M k sample x
  have h_layer_integrable' :
      MeasureTheory.Integrable (Function.uncurry f) (μ.prod ν) := by
    simpa [ν, f, Function.uncurry] using h_layer_integrable
  have hpoint :
      (fun sample : Fin n → ℝ => reflectedBottomKSum M sample k) =ᵐ[μ]
        fun sample : Fin n → ℝ => ∫ x, f sample x ∂ν := by
    filter_upwards [hM] with sample hsample
    simpa [ν, f] using
      reflectedBottomKSum_eq_integral_rank_count_layer M sample k hsample
  calc
    expectedReflectedBottomKSum M μ k =
        ∫ sample, reflectedBottomKSum M sample k ∂μ := by
          rfl
    _ = ∫ sample, (∫ x, f sample x ∂ν) ∂μ := by
          exact MeasureTheory.integral_congr_ae hpoint
    _ = ∫ x, (∫ sample, f sample x ∂μ) ∂ν := by
          exact MeasureTheory.integral_integral_swap
            (μ := μ) (ν := ν) (f := f) h_layer_integrable'
    _ = ∫ x in Set.Ioi (0 : ℝ),
        ∫ sample, reflectedBottomKRankCountLayer M k sample x ∂μ := by
          rfl

/--
Linearity of expectation for the reflected bottom-`k` sum: the aggregate
reflected endpoint-loss term is the sum of the expected lower order statistics
of the reflected sample.
-/
theorem expectedReflectedBottomKSum_eq_sum_reflectedAscendingOrderStatistic
    (M : ℝ) {n : ℕ} (μ : MeasureTheory.Measure (Fin n → ℝ)) (k : ℕ)
    (h_integrable :
      ∀ i : Fin (min k n),
        MeasureTheory.Integrable
          (fun sample =>
            ascendingOrderStatistic (reflectedSample M sample)
              (topKRankEmbedding k n i))
          μ) :
    expectedReflectedBottomKSum M μ k =
      ∑ i : Fin (min k n),
        ∫ sample,
          ascendingOrderStatistic (reflectedSample M sample)
            (topKRankEmbedding k n i) ∂μ := by
  unfold expectedReflectedBottomKSum reflectedBottomKSum
  exact MeasureTheory.integral_finset_sum Finset.univ
    (fun i _hi => h_integrable i)

/--
Fixed-`k` version of
`expectedReflectedBottomKSum_eq_sum_reflectedAscendingOrderStatistic`, for the
eventual asymptotic regime where the sample size is at least `k`.
-/
theorem expectedReflectedBottomKSum_eq_sum_reflectedAscendingOrderStatistic_of_le
    (M : ℝ) {n : ℕ} (μ : MeasureTheory.Measure (Fin n → ℝ)) {k : ℕ}
    (hkn : k ≤ n)
    (h_integrable :
      ∀ i : Fin k,
        MeasureTheory.Integrable
          (fun sample =>
            ascendingOrderStatistic (reflectedSample M sample)
              ⟨i.val, lt_of_lt_of_le i.isLt hkn⟩)
          μ) :
    expectedReflectedBottomKSum M μ k =
      ∑ i : Fin k,
        ∫ sample,
          ascendingOrderStatistic (reflectedSample M sample)
            ⟨i.val, lt_of_lt_of_le i.isLt hkn⟩ ∂μ := by
  have hmin : min k n = k := min_eq_left hkn
  have h_integrable' :
      ∀ i : Fin (min k n),
        MeasureTheory.Integrable
          (fun sample =>
            ascendingOrderStatistic (reflectedSample M sample)
              (topKRankEmbedding k n i))
          μ := by
    intro i
    let i' : Fin k := ⟨i.val, by simpa [hmin] using i.isLt⟩
    simpa [topKRankEmbedding, i'] using h_integrable i'
  have hlin :=
    expectedReflectedBottomKSum_eq_sum_reflectedAscendingOrderStatistic
      M μ k h_integrable'
  have hsum :
      (∑ i : Fin (min k n),
        ∫ sample,
          ascendingOrderStatistic (reflectedSample M sample)
            (topKRankEmbedding k n i) ∂μ) =
        ∑ i : Fin k,
          ∫ sample,
            ascendingOrderStatistic (reflectedSample M sample)
              ⟨i.val, lt_of_lt_of_le i.isLt hkn⟩ ∂μ := by
    let e : Fin (min k n) ≃ Fin k := finCongr hmin
    exact Fintype.sum_equiv e
      (fun i : Fin (min k n) =>
        ∫ sample,
          ascendingOrderStatistic (reflectedSample M sample)
            (topKRankEmbedding k n i) ∂μ)
      (fun i : Fin k =>
        ∫ sample,
          ascendingOrderStatistic (reflectedSample M sample)
            ⟨i.val, lt_of_lt_of_le i.isLt hkn⟩ ∂μ)
      (by
        intro i
        have hval : (e i).val = i.val := by
          simp [e]
        have hrank :
            topKRankEmbedding k n i =
              (⟨(e i).val, lt_of_lt_of_le (e i).isLt hkn⟩ : Fin n) := by
          apply Fin.ext
          simp [topKRankEmbedding, hval]
        simp [hrank])
  exact hlin.trans hsum

/--
Linearity of expectation for the tuple-level top-`k` sum: the expected sum of
upper order statistics is the sum of expected upper order statistics.
-/
theorem expectedSampleTopKSum_eq_sum_expectedUpperOrderStatistic
    {n : ℕ} (μ : MeasureTheory.Measure (Fin n → ℝ)) (k : ℕ)
    (h_integrable :
      ∀ i : Fin (min k n),
        MeasureTheory.Integrable
          (fun sample => upperOrderStatistic sample (topKRankEmbedding k n i))
          μ) :
    expectedSampleTopKSum μ k =
      ∑ i : Fin (min k n),
        expectedUpperOrderStatistic μ (topKRankEmbedding k n i) := by
  unfold expectedSampleTopKSum expectedUpperOrderStatistic sampleTopKSum
  exact MeasureTheory.integral_finset_sum Finset.univ
    (fun i _hi => h_integrable i)

/--
Expected form of the single-rank bounded-support reflection identity.
-/
theorem expectedUpperOrderStatistic_eq_endpoint_sub_expectedReflectedAscending
    (M : ℝ) {n : ℕ} (μ : MeasureTheory.Measure (Fin n → ℝ))
    [MeasureTheory.IsProbabilityMeasure μ] (rankFromTop : Fin n)
    (h_integrable :
      MeasureTheory.Integrable
        (fun sample =>
          ascendingOrderStatistic (reflectedSample M sample) rankFromTop)
        μ) :
    expectedUpperOrderStatistic μ rankFromTop =
      M -
        ∫ sample,
          ascendingOrderStatistic (reflectedSample M sample) rankFromTop ∂μ := by
  unfold expectedUpperOrderStatistic
  calc
    ∫ sample, upperOrderStatistic sample rankFromTop ∂μ
        = ∫ sample,
            M - ascendingOrderStatistic (reflectedSample M sample) rankFromTop
            ∂μ := by
          exact MeasureTheory.integral_congr_ae
            (Filter.Eventually.of_forall
              (fun sample =>
                upperOrderStatistic_eq_endpoint_sub_reflectedAscending
                  M sample rankFromTop))
    _ = M -
        ∫ sample,
          ascendingOrderStatistic (reflectedSample M sample) rankFromTop ∂μ := by
          rw [MeasureTheory.integral_sub
            (MeasureTheory.integrable_const M) h_integrable]
          simp [MeasureTheory.integral_const, MeasureTheory.probReal_univ]

/--
Expected bounded-support reflection identity for the top-`k` sample sum:
endpoint loss of the expected top-`k` value equals the expected sum of the
bottom reflected order statistics.
-/
theorem expectedSampleTopKEndpointLoss_eq_expectedReflectedBottomKSum
    (M : ℝ) {n : ℕ} (μ : MeasureTheory.Measure (Fin n → ℝ))
    [MeasureTheory.IsProbabilityMeasure μ] (k : ℕ)
    (h_integrable :
      MeasureTheory.Integrable (fun sample => sampleTopKSum sample k) μ) :
    (min k n : ℝ) * M - expectedSampleTopKSum μ k =
      expectedReflectedBottomKSum M μ k := by
  unfold expectedSampleTopKSum expectedReflectedBottomKSum
  calc
    (min k n : ℝ) * M - ∫ sample, sampleTopKSum sample k ∂μ
        = ∫ sample, (min k n : ℝ) * M - sampleTopKSum sample k ∂μ := by
          rw [MeasureTheory.integral_sub
            (MeasureTheory.integrable_const ((min k n : ℝ) * M))
            h_integrable]
          simp [MeasureTheory.integral_const, MeasureTheory.probReal_univ]
    _ = ∫ sample, sampleTopKEndpointLoss M sample k ∂μ := rfl
    _ = ∫ sample, reflectedBottomKSum M sample k ∂μ := by
          exact MeasureTheory.integral_congr_ae
            (Filter.Eventually.of_forall
              (fun sample =>
                sampleTopKEndpointLoss_eq_reflectedBottomKSum M sample k))

/-!
## Bottom-indexed paper order-statistic means

Some papers state order-statistic expectations as a global function
`μ rank sampleSize`, with one-based ranks from the bottom.  The bridge below
connects that notation to the tuple-level `sampleTopKSum` API above.
-/

/--
Top-`k` sum from bottom-indexed expected order-statistic means.  The rank
argument is one-based: rank `a` is the largest item in an `a`-sample.
-/
def orderStatisticTopKSumFromMean
    (μ : ℕ → ℕ → ℝ) (k a : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (min k a), μ (a - i) a

@[simp] theorem orderStatisticTopKSumFromMean_zero_samples
    (μ : ℕ → ℕ → ℝ) (k : ℕ) :
    orderStatisticTopKSumFromMean μ k 0 = 0 := by
  simp [orderStatisticTopKSumFromMean]

@[simp] theorem orderStatisticTopKSumFromMean_zero_k
    (μ : ℕ → ℕ → ℝ) (a : ℕ) :
    orderStatisticTopKSumFromMean μ 0 a = 0 := by
  simp [orderStatisticTopKSumFromMean]

theorem orderStatisticTopKSumFromMean_eq_bottomIndexed_sum
    (μ : ℕ → ℕ → ℝ) (k a : ℕ) :
    orderStatisticTopKSumFromMean μ k a =
      ∑ i ∈ Finset.range (min k a), μ (a - i) a := rfl

/--
When the sample count is at least `k`, the bottom-indexed top-`k`
order-statistic sum is the `Fin k` sum over the upper order-statistic means.
-/
theorem orderStatisticTopKSumFromMean_eq_fin_sum_of_le
    (μ : ℕ → ℕ → ℝ) {k a : ℕ} (hka : k ≤ a) :
    orderStatisticTopKSumFromMean μ k a =
      ∑ i : Fin k, μ (a - i.val) a := by
  unfold orderStatisticTopKSumFromMean
  rw [min_eq_left hka]
  exact (Fin.sum_univ_eq_sum_range (fun i => μ (a - i) a) k).symm

/--
Fixed-`k` endpoint-loss form of
`orderStatisticTopKSumFromMean_eq_fin_sum_of_le`.
-/
theorem orderStatisticTopKLossFromMean_eq_fin_loss_of_le
    (M : ℝ) (μ : ℕ → ℕ → ℝ) {k a : ℕ} (hka : k ≤ a) :
    (k : ℝ) * M - orderStatisticTopKSumFromMean μ k a =
      (k : ℝ) * M - ∑ i : Fin k, μ (a - i.val) a := by
  rw [orderStatisticTopKSumFromMean_eq_fin_sum_of_le μ hka]

/--
The `rank`-th smallest value of a concrete `a`-sample, using a one-based rank
convention.  Out-of-range ranks are set to zero; the top-`k` bridge only
evaluates valid ranks.
-/
def sampleOrderStatisticValue {a : ℕ}
    (sample : Fin a → ℝ) (rank : ℕ) : ℝ :=
  if hrank : 0 < rank ∧ rank ≤ a then
    ascendingOrderStatistic sample ⟨rank - 1, by omega⟩
  else 0

/--
The bottom-indexed one-based rank `a - r` is the same statistic as the `r`-th
value from the top, whenever `r < a`.
-/
theorem sampleOrderStatisticValue_eq_upperOrderStatistic_of_rank_from_top
    {a r : ℕ} (sample : Fin a → ℝ) (hr : r < a) :
    sampleOrderStatisticValue sample (a - r) =
      upperOrderStatistic sample ⟨r, hr⟩ := by
  have hrank : 0 < a - r ∧ a - r ≤ a := by omega
  simp [sampleOrderStatisticValue, hrank, upperOrderStatistic]
  exact congrArg (ascendingOrderStatistic sample)
    (Fin.ext (by simp [Fin.rev]; omega))

theorem sampleOrderStatisticValue_measurable {a : ℕ} (rank : ℕ) :
    Measurable
      (fun sample : Fin a → ℝ => sampleOrderStatisticValue sample rank) := by
  by_cases hrank : 0 < rank ∧ rank ≤ a
  · simpa [sampleOrderStatisticValue, hrank] using
      ascendingOrderStatistic_measurable (⟨rank - 1, by omega⟩ : Fin a)
  · simp [sampleOrderStatisticValue, hrank]

theorem sampleOrderStatisticValue_integrable_of_ae_bounds
    (L U : ℝ) {a : ℕ} (μ : MeasureTheory.Measure (Fin a → ℝ))
    [MeasureTheory.IsFiniteMeasure μ] (rank : ℕ)
    (h_bounds :
      ∀ᵐ sample ∂μ, ∀ i : Fin a, L ≤ sample i ∧ sample i ≤ U) :
    MeasureTheory.Integrable
      (fun sample : Fin a → ℝ => sampleOrderStatisticValue sample rank) μ := by
  by_cases hrank : 0 < rank ∧ rank ≤ a
  · simpa [sampleOrderStatisticValue, hrank] using
      ascendingOrderStatistic_integrable_of_ae_bounds
        L U μ (⟨rank - 1, by omega⟩ : Fin a) h_bounds
  · simp [sampleOrderStatisticValue, hrank]

theorem sampleOrderStatisticValue_topKRange_integrable_of_ae_bounds
    (L U : ℝ) {a : ℕ} (μ : MeasureTheory.Measure (Fin a → ℝ))
    [MeasureTheory.IsFiniteMeasure μ] (k : ℕ)
    (h_bounds :
      ∀ᵐ sample ∂μ, ∀ i : Fin a, L ≤ sample i ∧ sample i ≤ U) :
    ∀ i ∈ Finset.range (min k a),
      MeasureTheory.Integrable
        (fun sample : Fin a → ℝ => sampleOrderStatisticValue sample (a - i)) μ := by
  intro i _hi
  exact sampleOrderStatisticValue_integrable_of_ae_bounds
    L U μ (a - i) h_bounds

/--
Pointwise bridge: the bottom-indexed order-statistic sum induced by a concrete
sorted tuple equals the tuple-level top-`k` sample sum.
-/
theorem orderStatisticTopKSumFromSample_eq_sampleTopKSum
    {a : ℕ} (sample : Fin a → ℝ) (k : ℕ) :
    orderStatisticTopKSumFromMean
        (fun rank sampleSize =>
          if sampleSize = a then sampleOrderStatisticValue sample rank else 0)
        k a =
      sampleTopKSum sample k := by
  unfold orderStatisticTopKSumFromMean sampleTopKSum
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  have hi_lt : i < min k a := Finset.mem_range.mp hi
  have hi_lt_k : i < k := lt_of_lt_of_le hi_lt (min_le_left k a)
  have hi_lt_a : i < a := lt_of_lt_of_le hi_lt (min_le_right k a)
  have hrank_pos : 0 < a - i := Nat.sub_pos_of_lt hi_lt_a
  have hrank_le : a - i ≤ a := Nat.sub_le a i
  simp [sampleOrderStatisticValue, hrank_pos, hrank_le, hi_lt_k, hi_lt_a]
  unfold upperOrderStatistic
  congr 1

/--
Expected bottom-indexed order-statistic mean induced by a sample law on `a`
real draws.  The value is intended at `sampleSize = a`; other sample sizes are
set to zero so the function has a global `ℕ → ℕ → ℝ` shape.
-/
def expectedSampleOrderStatisticMean {a : ℕ}
    (μ : MeasureTheory.Measure (Fin a → ℝ)) (rank sampleSize : ℕ) : ℝ :=
  if sampleSize = a then
    ∫ sample, sampleOrderStatisticValue sample rank ∂μ
  else 0

/--
Expectation-level bridge from the bottom-indexed one-based rank `a - r` to the
library's `r`-from-top order statistic.
-/
theorem expectedSampleOrderStatisticMean_eq_expectedUpperOrderStatistic_of_rank_from_top
    {a r : ℕ} (μ : MeasureTheory.Measure (Fin a → ℝ)) (hr : r < a) :
    expectedSampleOrderStatisticMean μ (a - r) a =
      expectedUpperOrderStatistic μ ⟨r, hr⟩ := by
  unfold expectedSampleOrderStatisticMean expectedUpperOrderStatistic
  simp
  exact MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall
      (fun sample =>
        sampleOrderStatisticValue_eq_upperOrderStatistic_of_rank_from_top
          sample hr))

/--
Expectation form of the pointwise bridge: if the bottom-indexed mean function
is induced by integrating sample order statistics, then its top-`k` sum is the
expected tuple-level top-`k` sample sum.
-/
theorem expectedSampleOrderStatisticTopKSum_eq_expectedSampleTopKSum
    {a : ℕ} (μ : MeasureTheory.Measure (Fin a → ℝ)) (k : ℕ)
    (h_integrable :
      ∀ i ∈ Finset.range (min k a),
        MeasureTheory.Integrable
          (fun sample => sampleOrderStatisticValue sample (a - i)) μ) :
    orderStatisticTopKSumFromMean
        (expectedSampleOrderStatisticMean μ) k a =
      expectedSampleTopKSum μ k := by
  calc
    orderStatisticTopKSumFromMean
        (expectedSampleOrderStatisticMean μ) k a
        = ∑ i ∈ Finset.range (min k a),
            ∫ sample, sampleOrderStatisticValue sample (a - i) ∂μ := by
          unfold orderStatisticTopKSumFromMean expectedSampleOrderStatisticMean
          simp
    _ = ∫ sample,
          ∑ i ∈ Finset.range (min k a),
            sampleOrderStatisticValue sample (a - i) ∂μ := by
          rw [MeasureTheory.integral_finset_sum]
          exact h_integrable
    _ = ∫ sample,
          orderStatisticTopKSumFromMean
            (fun rank sampleSize =>
              if sampleSize = a then sampleOrderStatisticValue sample rank else 0)
            k a ∂μ := by
          exact MeasureTheory.integral_congr_ae
            (Filter.Eventually.of_forall
              (fun sample => by
                simp [orderStatisticTopKSumFromMean]))
    _ = expectedSampleTopKSum μ k := by
          unfold expectedSampleTopKSum
          exact MeasureTheory.integral_congr_ae
            (Filter.Eventually.of_forall
              (fun sample =>
                orderStatisticTopKSumFromSample_eq_sampleTopKSum sample k))

/--
Expected bounded-support top-`k` reflection in the bottom-indexed mean
interface.
-/
theorem expectedSampleOrderStatisticTopKEndpointLoss_eq_expectedReflectedBottomKSum
    (M : ℝ) {a : ℕ} (μ : MeasureTheory.Measure (Fin a → ℝ))
    [MeasureTheory.IsProbabilityMeasure μ] (k : ℕ)
    (h_order_integrable :
      ∀ i ∈ Finset.range (min k a),
        MeasureTheory.Integrable
          (fun sample => sampleOrderStatisticValue sample (a - i)) μ)
    (h_top_integrable :
      MeasureTheory.Integrable
        (fun sample => sampleTopKSum sample k) μ) :
    (min k a : ℝ) * M -
        orderStatisticTopKSumFromMean
          (expectedSampleOrderStatisticMean μ) k a =
      expectedReflectedBottomKSum M μ k := by
  rw [expectedSampleOrderStatisticTopKSum_eq_expectedSampleTopKSum
    μ k h_order_integrable]
  exact expectedSampleTopKEndpointLoss_eq_expectedReflectedBottomKSum
    M μ k h_top_integrable

/--
Bottom-indexed expected order-statistic mean induced by a family of finite
sample laws, one law for each sample size.
-/
def expectedOrderStatisticMeanSeq
    (sampleMeasure : (a : ℕ) → MeasureTheory.Measure (Fin a → ℝ))
    (rank sampleSize : ℕ) : ℝ :=
  expectedSampleOrderStatisticMean (sampleMeasure sampleSize) rank sampleSize

/--
Varying-sample-size version of
`expectedSampleOrderStatisticTopKSum_eq_expectedSampleTopKSum`.
-/
theorem expectedOrderStatisticMeanSeq_topKSum_eq_expectedSampleTopKSum
    (sampleMeasure : (a : ℕ) → MeasureTheory.Measure (Fin a → ℝ))
    (k a : ℕ)
    (h_integrable :
      ∀ i ∈ Finset.range (min k a),
        MeasureTheory.Integrable
          (fun sample => sampleOrderStatisticValue sample (a - i))
          (sampleMeasure a)) :
    orderStatisticTopKSumFromMean
        (expectedOrderStatisticMeanSeq sampleMeasure) k a =
      expectedSampleTopKSum (sampleMeasure a) k := by
  simpa [expectedOrderStatisticMeanSeq] using
    expectedSampleOrderStatisticTopKSum_eq_expectedSampleTopKSum
      (sampleMeasure a) k h_integrable

/--
Varying-sample-size bounded reflection bridge in the global
`μ rank sampleSize` interface.
-/
theorem expectedOrderStatisticMeanSeq_topKEndpointLoss_eq_expectedReflectedBottomKSum
    (M : ℝ)
    (sampleMeasure : (a : ℕ) → MeasureTheory.Measure (Fin a → ℝ))
    {a : ℕ} [MeasureTheory.IsProbabilityMeasure (sampleMeasure a)] (k : ℕ)
    (h_order_integrable :
      ∀ i ∈ Finset.range (min k a),
        MeasureTheory.Integrable
          (fun sample => sampleOrderStatisticValue sample (a - i))
          (sampleMeasure a))
    (h_top_integrable :
      MeasureTheory.Integrable
        (fun sample => sampleTopKSum sample k)
        (sampleMeasure a)) :
    (min k a : ℝ) * M -
        orderStatisticTopKSumFromMean
          (expectedOrderStatisticMeanSeq sampleMeasure) k a =
      expectedReflectedBottomKSum M (sampleMeasure a) k := by
  simpa [expectedOrderStatisticMeanSeq] using
    expectedSampleOrderStatisticTopKEndpointLoss_eq_expectedReflectedBottomKSum
      M (sampleMeasure a) k h_order_integrable h_top_integrable

/--
Oracle for the expected value of the best `k` consumed items among `q` sampled
items of a type/category.
-/
structure TopKExpectationOracle (τ : Type*) where
  expectedTopSum : ℕ → τ → ℕ → ℝ

namespace TopKExpectationOracle

variable {τ : Type*}

/-- Top-`k` expectation oracle induced by a common scalar value function. -/
def common (τ : Type*) (h : ℕ → ℝ) : TopKExpectationOracle τ where
  expectedTopSum := fun _k _t q => h q

@[simp] theorem common_expectedTopSum
    (τ : Type*) (h : ℕ → ℝ) (k : ℕ) (t : τ) (q : ℕ) :
    (common τ h).expectedTopSum k t q = h q := rfl

/-- Marginal expected top-`k` value from adding one more sampled item. -/
def marginalTopK (O : TopKExpectationOracle τ)
    (k : ℕ) (t : τ) (q : ℕ) : ℝ :=
  O.expectedTopSum k t (q + 1) - O.expectedTopSum k t q

/-- Diminishing marginal expected top-`k` values. -/
def HasDiminishingReturnsAt (O : TopKExpectationOracle τ) (k : ℕ) : Prop :=
  ∀ t q, O.marginalTopK k t (q + 1) ≤ O.marginalTopK k t q

/-- Nonnegative marginal expected top-`k` values. -/
def HasNonnegativeMarginalsAt (O : TopKExpectationOracle τ) (k : ℕ) : Prop :=
  ∀ t q, 0 ≤ O.marginalTopK k t q

@[simp] theorem marginalTopK_apply (O : TopKExpectationOracle τ)
    (k : ℕ) (t : τ) (q : ℕ) :
    O.marginalTopK k t q =
      O.expectedTopSum k t (q + 1) - O.expectedTopSum k t q := rfl

/--
Weight a top-`k` expectation oracle by a type-specific objective coefficient.

This is the probability-side analogue of recommendation objectives whose
expected value contribution is `likelihood t * expectedTopSum t q`.
-/
def weighted (O : TopKExpectationOracle τ) (objectiveWeight : τ → ℝ) :
    TopKExpectationOracle τ where
  expectedTopSum := fun k t q => objectiveWeight t * O.expectedTopSum k t q

@[simp] theorem weighted_expectedTopSum
    (O : TopKExpectationOracle τ) (objectiveWeight : τ → ℝ)
    (k : ℕ) (t : τ) (q : ℕ) :
    (O.weighted objectiveWeight).expectedTopSum k t q =
      objectiveWeight t * O.expectedTopSum k t q := rfl

@[simp] theorem weighted_marginalTopK
    (O : TopKExpectationOracle τ) (objectiveWeight : τ → ℝ)
    (k : ℕ) (t : τ) (q : ℕ) :
    (O.weighted objectiveWeight).marginalTopK k t q =
      objectiveWeight t * O.marginalTopK k t q := by
  simp [marginalTopK, mul_sub]

/--
Top-`k` expectation oracle induced by a bottom-indexed order-statistic mean
table.  The oracle is constant across item types; caller-specific finite type
oracles can wrap this definition.
-/
def orderStatisticTopKExpectationOracle
    (τ : Type*) (μ : ℕ → ℕ → ℝ) : TopKExpectationOracle τ where
  expectedTopSum := fun k _t q => orderStatisticTopKSumFromMean μ k q

@[simp] theorem orderStatisticTopKExpectationOracle_expectedTopSum
    (τ : Type*) (μ : ℕ → ℕ → ℝ) (k : ℕ) (t : τ) (q : ℕ) :
    (orderStatisticTopKExpectationOracle τ μ).expectedTopSum k t q =
      orderStatisticTopKSumFromMean μ k q := rfl

/--
Certificate that all finite type-specific top-`k` marginals share a common
asymptotic scale, up to a positive type weight:

`marginal(k,t,q) / (scale q * weight t) -> 1`.

This is the probability-facing object that bounded, exponential, Pareto, or
finite-discrete order-statistic calculations should produce before the
optimization layer consumes marginal comparisons.
-/
structure ScaledMarginalLimitCertificate [Fintype τ]
    (O : TopKExpectationOracle τ) (k : ℕ)
    (scale : ℕ → ℝ) (weight : τ → ℝ) where
  scale_pos_eventually : ∀ᶠ q in atTop, 0 < scale q
  weight_pos : ∀ t, 0 < weight t
  marginal_ratio_tendsto :
    ∀ t,
      Tendsto
        (fun q => O.marginalTopK k t q / (scale q * weight t))
        atTop (nhds 1)

namespace ScaledMarginalLimitCertificate

variable [Fintype τ]
variable {k : ℕ}
variable {scale : ℕ → ℝ} {weight : τ → ℝ}

/--
Lift a scaled-marginal certificate through type-specific objective weights.

If `O.marginalTopK k t q ~ scale q * weight t`, then the weighted oracle has
margin `objectiveWeight t * O.marginalTopK k t q` and type weight
`objectiveWeight t * weight t`.
-/
theorem weighted
    {O : TopKExpectationOracle τ}
    (C : ScaledMarginalLimitCertificate O k scale weight)
    {objectiveWeight : τ → ℝ} (hobjective_pos : ∀ t, 0 < objectiveWeight t) :
    ScaledMarginalLimitCertificate
      (O.weighted objectiveWeight) k scale
      (fun t => objectiveWeight t * weight t) where
  scale_pos_eventually := C.scale_pos_eventually
  weight_pos := fun t => mul_pos (hobjective_pos t) (C.weight_pos t)
  marginal_ratio_tendsto := by
    intro t
    refine Tendsto.congr' ?_ (C.marginal_ratio_tendsto t)
    filter_upwards [C.scale_pos_eventually] with q hscale
    have hobjective_ne : objectiveWeight t ≠ 0 := ne_of_gt (hobjective_pos t)
    have hweight_ne : weight t ≠ 0 := ne_of_gt (C.weight_pos t)
    have hscale_ne : scale q ≠ 0 := ne_of_gt hscale
    dsimp [TopKExpectationOracle.marginalTopK, TopKExpectationOracle.weighted]
    field_simp [hobjective_ne, hweight_ne, hscale_ne]

/--
Transport a scaled-marginal certificate across an eventually equal marginal
sequence.  This is useful when a source-specific expected top-`k` table has
first been identified with a synthetic table whose asymptotics are already
proved.
-/
theorem congr_marginal
    {O' : TopKExpectationOracle τ}
    {O : TopKExpectationOracle τ}
    (C : ScaledMarginalLimitCertificate O k scale weight)
    (hmargin :
      ∀ᶠ q in atTop,
        ∀ t, O'.marginalTopK k t q = O.marginalTopK k t q) :
    ScaledMarginalLimitCertificate O' k scale weight where
  scale_pos_eventually := C.scale_pos_eventually
  weight_pos := C.weight_pos
  marginal_ratio_tendsto := by
    intro t
    refine Tendsto.congr' ?_ (C.marginal_ratio_tendsto t)
    filter_upwards [hmargin] with q hq
    rw [hq t]

theorem eventually_uniform_ratio_abs_sub_lt
    {O : TopKExpectationOracle τ}
    (C : ScaledMarginalLimitCertificate O k scale weight)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q in atTop,
      ∀ t : τ,
        |O.marginalTopK k t q / (scale q * weight t) - 1| < ε := by
  classical
  refine eventually_all.2 ?_
  intro t
  have ht :=
    (C.marginal_ratio_tendsto t).eventually
      (Metric.ball_mem_nhds 1 hε)
  filter_upwards [ht] with q hq
  simpa [Metric.mem_ball, Real.dist_eq] using hq

/--
Threshold for the uniform finite-type ratio estimate at tolerance
`1 / (m + 1)`.

This packages the usual `eventually_atTop` choice so downstream optimization
arguments can build one concrete `o(1)` error schedule from the family of
asymptotic marginal estimates.
-/
noncomputable def uniformRatioThreshold
    {O : TopKExpectationOracle τ}
    (C : ScaledMarginalLimitCertificate O k scale weight) (m : ℕ) : ℕ :=
  Classical.choose
    (eventually_atTop.1
      (C.eventually_uniform_ratio_abs_sub_lt
        (by positivity : (0 : ℝ) < 1 / ((m + 1 : ℕ) : ℝ))))

theorem uniformRatioThreshold_spec
    {O : TopKExpectationOracle τ}
    (C : ScaledMarginalLimitCertificate O k scale weight) (m : ℕ) :
    ∀ q ≥ C.uniformRatioThreshold m,
      ∀ t : τ,
        |O.marginalTopK k t q / (scale q * weight t) - 1| <
          1 / ((m + 1 : ℕ) : ℝ) :=
  Classical.choose_spec
    (eventually_atTop.1
      (C.eventually_uniform_ratio_abs_sub_lt
        (by positivity : (0 : ℝ) < 1 / ((m + 1 : ℕ) : ℝ))))

/--
Concrete `o(1)` error schedule induced by the uniform finite-type ratio
thresholds of a scaled-marginal certificate.
-/
noncomputable def uniformRatioError
    {O : TopKExpectationOracle τ}
    (C : ScaledMarginalLimitCertificate O k scale weight) : ℕ → ℝ :=
  AppliedModelingLib.Math.reciprocalThresholdError C.uniformRatioThreshold

theorem uniformRatioError_nonneg
    {O : TopKExpectationOracle τ}
    (C : ScaledMarginalLimitCertificate O k scale weight) (N : ℕ) :
    0 ≤ C.uniformRatioError N :=
  AppliedModelingLib.Math.reciprocalThresholdError_nonneg C.uniformRatioThreshold N

theorem uniformRatioError_tendsToZero
    {O : TopKExpectationOracle τ}
    (C : ScaledMarginalLimitCertificate O k scale weight) :
    AppliedModelingLib.Math.TendsToZero C.uniformRatioError :=
  AppliedModelingLib.Math.reciprocalThresholdError_tendsToZero C.uniformRatioThreshold

theorem uniformRatioError_le_of_threshold_le
    {O : TopKExpectationOracle τ}
    (C : ScaledMarginalLimitCertificate O k scale weight)
    {m N : ℕ}
    (hm_le_N : m ≤ N)
    (hthreshold_le_N : C.uniformRatioThreshold m ≤ N) :
    C.uniformRatioError N ≤ 1 / ((m + 1 : ℕ) : ℝ) := by
  simpa [uniformRatioError, Nat.cast_add, Nat.cast_one] using
    AppliedModelingLib.Math.reciprocalThresholdError_le_of_threshold_le
      C.uniformRatioThreshold hm_le_N hthreshold_le_N

theorem uniform_ratio_abs_sub_lt_uniformRatioError
    {O : TopKExpectationOracle τ}
    (C : ScaledMarginalLimitCertificate O k scale weight)
    {q : ℕ} (hq_base : C.uniformRatioThreshold 0 ≤ q) :
    ∀ t : τ,
      |O.marginalTopK k t q / (scale q * weight t) - 1| <
        C.uniformRatioError q := by
  let m : ℕ :=
    Nat.findGreatest (fun r => C.uniformRatioThreshold r ≤ q) q
  have hm_threshold : C.uniformRatioThreshold m ≤ q := by
    dsimp [m]
    exact
      Nat.findGreatest_spec
        (P := fun r => C.uniformRatioThreshold r ≤ q)
        (m := 0) (n := q) (Nat.zero_le q) hq_base
  intro t
  have hspec := C.uniformRatioThreshold_spec m q hm_threshold t
  simpa [uniformRatioError, AppliedModelingLib.Math.reciprocalThresholdError, m,
    Nat.cast_add, Nat.cast_one] using hspec

/--
Prefix-scaled envelope of the certificate's uniform ratio error.

For every `q ≤ N`, `uniformRatioError q * q` is bounded by
`uniformRatioPrefixError N * N`, while the prefix envelope still tends to zero.
-/
noncomputable def uniformRatioPrefixError
    {O : TopKExpectationOracle τ}
    (C : ScaledMarginalLimitCertificate O k scale weight) : ℕ → ℝ :=
  AppliedModelingLib.Math.prefixScaledError C.uniformRatioError

theorem uniformRatioPrefixError_nonneg
    {O : TopKExpectationOracle τ}
    (C : ScaledMarginalLimitCertificate O k scale weight) (N : ℕ) :
    0 ≤ C.uniformRatioPrefixError N :=
  AppliedModelingLib.Math.prefixScaledError_nonneg C.uniformRatioError
    C.uniformRatioError_nonneg N

theorem uniformRatioPrefixError_tendsToZero
    {O : TopKExpectationOracle τ}
    (C : ScaledMarginalLimitCertificate O k scale weight) :
    AppliedModelingLib.Math.TendsToZero C.uniformRatioPrefixError :=
  AppliedModelingLib.Math.prefixScaledError_tendsToZero C.uniformRatioError
    C.uniformRatioError_nonneg C.uniformRatioError_tendsToZero

theorem uniformRatioError_mul_count_le_prefix
    {O : TopKExpectationOracle τ}
    (C : ScaledMarginalLimitCertificate O k scale weight)
    {q N : ℕ} (hN_pos : 0 < N) (hq_le_N : q ≤ N) :
    C.uniformRatioError q * (q : ℝ) ≤
      C.uniformRatioPrefixError N * (N : ℝ) :=
  AppliedModelingLib.Math.le_prefixScaledError_mul_nat
    C.uniformRatioError hN_pos hq_le_N

theorem eventually_uniform_ratio_mem_Icc
    {O : TopKExpectationOracle τ}
    (C : ScaledMarginalLimitCertificate O k scale weight)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q in atTop,
      ∀ t : τ,
        (1 - ε ≤ O.marginalTopK k t q / (scale q * weight t)) ∧
          (O.marginalTopK k t q / (scale q * weight t) ≤ 1 + ε) := by
  filter_upwards [C.eventually_uniform_ratio_abs_sub_lt hε] with q hq t
  have habs := hq t
  rw [abs_lt] at habs
  constructor <;> linarith

theorem eventually_uniform_ratio_pos
    {O : TopKExpectationOracle τ}
    (C : ScaledMarginalLimitCertificate O k scale weight) :
    ∀ᶠ q in atTop,
      ∀ t : τ,
        0 < O.marginalTopK k t q / (scale q * weight t) := by
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  filter_upwards [C.eventually_uniform_ratio_mem_Icc hhalf] with q hq t
  linarith [(hq t).1]

theorem marginalTopK_eq_ratio_mul
    {O : TopKExpectationOracle τ}
    (C : ScaledMarginalLimitCertificate O k scale weight)
    {q : ℕ} {t : τ} (hscale : scale q ≠ 0) :
    O.marginalTopK k t q =
      (O.marginalTopK k t q / (scale q * weight t)) *
        (scale q * weight t) := by
  have hweight : weight t ≠ 0 := ne_of_gt (C.weight_pos t)
  field_simp [hscale, hweight]

/--
Uniform finite-type asymptotic ratio control gives an eventual multiplicative
sandwich for every type's marginal top-`k` value.
-/
theorem eventually_marginal_sandwich
    {O : TopKExpectationOracle τ}
    (C : ScaledMarginalLimitCertificate O k scale weight)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q in atTop,
      ∀ t : τ,
        (1 - ε) * (scale q * weight t) ≤ O.marginalTopK k t q ∧
          O.marginalTopK k t q ≤
            (1 + ε) * (scale q * weight t) := by
  filter_upwards
    [C.eventually_uniform_ratio_mem_Icc hε, C.scale_pos_eventually]
    with q hratio hscale t
  have hden_pos : 0 < scale q * weight t :=
    mul_pos hscale (C.weight_pos t)
  have hden_nonneg : 0 ≤ scale q * weight t := hden_pos.le
  have heq :=
    C.marginalTopK_eq_ratio_mul
      (q := q) (t := t) (ne_of_gt hscale)
  constructor
  · calc
      (1 - ε) * (scale q * weight t)
          ≤ (O.marginalTopK k t q / (scale q * weight t)) *
              (scale q * weight t) :=
            mul_le_mul_of_nonneg_right (hratio t).1 hden_nonneg
      _ = O.marginalTopK k t q := by rw [← heq]
  · calc
      O.marginalTopK k t q
          = (O.marginalTopK k t q / (scale q * weight t)) *
              (scale q * weight t) := heq
      _ ≤ (1 + ε) * (scale q * weight t) :=
            mul_le_mul_of_nonneg_right (hratio t).2 hden_nonneg

/--
If the common marginal scale vanishes, then every type-specific top-`k`
marginal in a scaled-marginal certificate also vanishes.
-/
theorem marginalTopK_tendsto_zero
    {O : TopKExpectationOracle τ}
    (C : ScaledMarginalLimitCertificate O k scale weight)
    (hscale_zero : Tendsto scale atTop (nhds 0)) (t : τ) :
    Tendsto (fun q => O.marginalTopK k t q) atTop (nhds 0) := by
  have hscaled_zero :
      Tendsto (fun q => scale q * weight t) atTop (nhds 0) := by
    simpa using hscale_zero.mul_const (weight t)
  have hprod :
      Tendsto
        (fun q =>
          (O.marginalTopK k t q / (scale q * weight t)) *
            (scale q * weight t))
        atTop (nhds (1 * 0)) :=
    (C.marginal_ratio_tendsto t).mul hscaled_zero
  refine Tendsto.congr' ?_ (by simpa using hprod)
  filter_upwards [C.scale_pos_eventually] with q hscale
  exact (C.marginalTopK_eq_ratio_mul (q := q) (t := t)
    (ne_of_gt hscale)).symm

/-- A one-index marginal sandwich at a fixed count. -/
def MarginalSandwichAt
    {O : TopKExpectationOracle τ}
    (C : ScaledMarginalLimitCertificate O k scale weight)
    (ε : ℝ) (q : ℕ) : Prop :=
  ∀ t : τ,
    (1 - ε) * (scale q * weight t) ≤ O.marginalTopK k t q ∧
      O.marginalTopK k t q ≤ (1 + ε) * (scale q * weight t)

theorem eventually_marginalSandwichAt
    {O : TopKExpectationOracle τ}
    (C : ScaledMarginalLimitCertificate O k scale weight)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ q in atTop, C.MarginalSandwichAt ε q :=
  C.eventually_marginal_sandwich hε

/--
If the upper scaled approximation for one marginal lies below the lower scaled
approximation for another, then the actual marginals are strictly ordered.
-/
theorem marginal_lt_of_scaled_gap
    {O : TopKExpectationOracle τ}
    (C : ScaledMarginalLimitCertificate O k scale weight)
    {ε : ℝ} {qsrc qdst : ℕ} {src dst : τ}
    (hsrc : C.MarginalSandwichAt ε qsrc)
    (hdst : C.MarginalSandwichAt ε qdst)
    (hgap :
      (1 + ε) * (scale qsrc * weight src) <
        (1 - ε) * (scale qdst * weight dst)) :
    O.marginalTopK k src qsrc < O.marginalTopK k dst qdst :=
  lt_of_le_of_lt (hsrc src).2 (hgap.trans_le (hdst dst).1)

/--
Same-count specialization: a strict gap between scaled type weights eventually
implies the same strict ordering of top-`k` marginals.
-/
theorem eventually_same_count_marginal_lt_of_weight_gap
    {O : TopKExpectationOracle τ}
    (C : ScaledMarginalLimitCertificate O k scale weight)
    {ε : ℝ} (hε : 0 < ε) {src dst : τ}
    (hgap : (1 + ε) * weight src < (1 - ε) * weight dst) :
    ∀ᶠ q in atTop,
      O.marginalTopK k src q < O.marginalTopK k dst q := by
  filter_upwards [C.eventually_marginalSandwichAt hε, C.scale_pos_eventually]
    with q hq hscale
  apply C.marginal_lt_of_scaled_gap (qsrc := q) (qdst := q)
    (src := src) (dst := dst) hq hq
  have hscaled :
      scale q * ((1 + ε) * weight src) <
        scale q * ((1 - ε) * weight dst) :=
    mul_lt_mul_of_pos_left hgap hscale
  calc
    (1 + ε) * (scale q * weight src)
        = scale q * ((1 + ε) * weight src) := by ring
    _ < scale q * ((1 - ε) * weight dst) := hscaled
    _ = (1 - ε) * (scale q * weight dst) := by ring

end ScaledMarginalLimitCertificate

end TopKExpectationOracle

/--
Distribution-neutral source certificate for fixed-`k` order-statistic marginal
asymptotics.  Bounded, Pareto, exponential, and finite-discrete sources can keep
family-specific scale definitions while delegating the finite-sum and top-k
oracle packaging to this structure.
-/
structure OrderStatisticScaledMarginalCertificate
    (μ : ℕ → ℕ → ℝ) (k : ℕ)
    (scale : ℕ → ℝ) (limitCoeff : ℝ) : Prop where
  k_pos : 0 < k
  coeff_pos : 0 < limitCoeff
  scale_pos_eventually : ∀ᶠ q in atTop, 0 < scale q
  marginal_ratio_tendsto :
    Tendsto
      (fun q : ℕ =>
        (orderStatisticTopKSumFromMean μ k (q + 1) -
            orderStatisticTopKSumFromMean μ k q) /
          (scale q * limitCoeff))
      atTop (nhds 1)

namespace OrderStatisticScaledMarginalCertificate

variable {μ : ℕ → ℕ → ℝ} {k : ℕ}
variable {scale : ℕ → ℝ} {limitCoeff : ℝ}

/-- Restate the marginal-ratio field as an asymptotic equivalence. -/
theorem marginal_asymptoticEquivalent
    (C : OrderStatisticScaledMarginalCertificate μ k scale limitCoeff) :
    AppliedModelingLib.Math.AsymptoticEquivalent
      (fun q : ℕ =>
        orderStatisticTopKSumFromMean μ k (q + 1) -
          orderStatisticTopKSumFromMean μ k q)
      (fun q : ℕ => scale q * limitCoeff) := C.marginal_ratio_tendsto

/-- Constructor from the standard asymptotic-equivalence statement. -/
def ofMarginalAsymptoticEquivalent
    (hk : 0 < k) (hcoeff : 0 < limitCoeff)
    (hscale_pos_eventually : ∀ᶠ q in atTop, 0 < scale q)
    (hmargin :
      AppliedModelingLib.Math.AsymptoticEquivalent
        (fun q : ℕ =>
          orderStatisticTopKSumFromMean μ k (q + 1) -
            orderStatisticTopKSumFromMean μ k q)
        (fun q : ℕ => scale q * limitCoeff)) :
    OrderStatisticScaledMarginalCertificate μ k scale limitCoeff where
  k_pos := hk
  coeff_pos := hcoeff
  scale_pos_eventually := hscale_pos_eventually
  marginal_ratio_tendsto := hmargin

/-- Constructor for sources that write the coefficient before the scale. -/
def ofConstMulScaleAsymptoticEquivalent
    (hk : 0 < k) (hcoeff : 0 < limitCoeff)
    (hscale_pos_eventually : ∀ᶠ q in atTop, 0 < scale q)
    (hmargin :
      AppliedModelingLib.Math.AsymptoticEquivalent
        (fun q : ℕ =>
          orderStatisticTopKSumFromMean μ k (q + 1) -
            orderStatisticTopKSumFromMean μ k q)
        (fun q : ℕ => limitCoeff * scale q)) :
    OrderStatisticScaledMarginalCertificate μ k scale limitCoeff :=
  ofMarginalAsymptoticEquivalent hk hcoeff hscale_pos_eventually <| by
    rw [AppliedModelingLib.Math.AsymptoticEquivalent] at hmargin ⊢
    refine Tendsto.congr' ?_ hmargin
    filter_upwards with q
    rw [mul_comm]

/--
Constructor from a fixed-`k`, per-rank marginal-sum asymptotic.  It converts
the finite rank sum into the repository's `orderStatisticTopKSumFromMean`
top-`k` marginal.
-/
def ofFiniteRankMarginalSumAsymptoticEquivalent
    (hk : 0 < k) (hcoeff : 0 < limitCoeff)
    (hscale_pos_eventually : ∀ᶠ q in atTop, 0 < scale q)
    (hmargin :
      AppliedModelingLib.Math.AsymptoticEquivalent
        (fun q : ℕ =>
          ∑ i : Fin k,
            (μ (q + 1 - i.val) (q + 1) - μ (q - i.val) q))
        (fun q : ℕ => limitCoeff * scale q)) :
    OrderStatisticScaledMarginalCertificate μ k scale limitCoeff :=
  ofConstMulScaleAsymptoticEquivalent hk hcoeff hscale_pos_eventually <| by
    refine AppliedModelingLib.Math.AsymptoticEquivalent.congr_left_eventually ?_ hmargin
    filter_upwards [eventually_atTop.2 ⟨k, fun q hq => hq⟩] with q hkq
    have hkq_succ : k ≤ q + 1 := Nat.le_trans hkq (Nat.le_succ q)
    rw [orderStatisticTopKSumFromMean_eq_fin_sum_of_le μ hkq_succ,
      orderStatisticTopKSumFromMean_eq_fin_sum_of_le μ hkq]
    rw [← Finset.sum_sub_distrib]

/--
Constructor from fixed-rank scaled marginal limits and an aggregate coefficient
identity.
-/
def ofFiniteRankScaledLimits
    (rankCoeff : Fin k → ℝ)
    (hk : 0 < k) (hcoeff : 0 < limitCoeff)
    (hscale_pos_eventually : ∀ᶠ q in atTop, 0 < scale q)
    (hcoeff_sum : (∑ i : Fin k, rankCoeff i) = limitCoeff)
    (hrank :
      ∀ i : Fin k,
        Tendsto
          (fun q : ℕ =>
            (μ (q + 1 - i.val) (q + 1) - μ (q - i.val) q) /
              scale q)
          atTop (nhds (rankCoeff i))) :
    OrderStatisticScaledMarginalCertificate μ k scale limitCoeff :=
  ofFiniteRankMarginalSumAsymptoticEquivalent hk hcoeff
      hscale_pos_eventually <| by
    rw [AppliedModelingLib.Math.AsymptoticEquivalent]
    have hsum_scaled :
        Tendsto
          (fun q : ℕ =>
            ∑ i : Fin k,
              (μ (q + 1 - i.val) (q + 1) - μ (q - i.val) q) /
                scale q)
          atTop (nhds (∑ i : Fin k, rankCoeff i)) :=
      tendsto_finset_sum Finset.univ (fun i _ => hrank i)
    have hratio_scaled :
        Tendsto
          (fun q : ℕ =>
            (∑ i : Fin k,
              (μ (q + 1 - i.val) (q + 1) - μ (q - i.val) q) /
                scale q) /
              limitCoeff)
          atTop (nhds 1) := by
      have hdiv := hsum_scaled.div_const limitCoeff
      simpa [hcoeff_sum, hcoeff.ne'] using hdiv
    refine Tendsto.congr' ?_ hratio_scaled
    filter_upwards [hscale_pos_eventually] with q hscale_pos
    have hscale_ne : scale q ≠ 0 := ne_of_gt hscale_pos
    have hcoeff_ne : limitCoeff ≠ 0 := hcoeff.ne'
    have hsum_div :
        (∑ i : Fin k,
          (μ (q + 1 - i.val) (q + 1) - μ (q - i.val) q) /
            scale q) =
          (∑ i : Fin k,
            (μ (q + 1 - i.val) (q + 1) - μ (q - i.val) q)) /
            scale q := by
      simp_rw [div_eq_mul_inv]
      rw [Finset.sum_mul]
    rw [hsum_div]
    field_simp [hcoeff_ne, hscale_ne]

/--
Convert a source-side order-statistic marginal certificate into the reusable
finite-type top-`k` marginal certificate for the constant-in-type oracle.
-/
noncomputable def toTopKExpectationScaledMarginalLimitCertificate
    (C : OrderStatisticScaledMarginalCertificate μ k scale limitCoeff)
    (τ : Type*) [Fintype τ] :
    TopKExpectationOracle.ScaledMarginalLimitCertificate
      (TopKExpectationOracle.orderStatisticTopKExpectationOracle τ μ)
      k scale (fun _ : τ => limitCoeff) where
  scale_pos_eventually := C.scale_pos_eventually
  weight_pos := by
    intro _t
    exact C.coeff_pos
  marginal_ratio_tendsto := by
    intro t
    simpa [TopKExpectationOracle.marginalTopK,
      TopKExpectationOracle.orderStatisticTopKExpectationOracle]
      using C.marginal_ratio_tendsto

end OrderStatisticScaledMarginalCertificate

end

end Probability
end AppliedModelingLib

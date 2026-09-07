import LMMS04FairDivision.MainTheorems

/-!
# Proof Interface: Approximately Fair Allocations of Indivisible Goods

This is the broad proof-facing compatibility surface for the LMMS 2004
formalization. The compact human-review surface is `PaperInterface.lean`.
-/

open MeasureTheory
open Filter
open scoped BigOperators
open AppliedModelingLib.FairDivision

namespace LMMS04FairDivision
namespace ProofInterface

variable {Agent Item : Type*} [Fintype Agent] [Fintype Item] [DecidableEq Agent]
  [DecidableEq Item] [Nonempty Agent] [Nonempty Item]

noncomputable section

/-! ## Paper Definitions -/

/-- Envy of agent `i` toward agent `j`: positive part of the value difference. -/
def envy (v : Valuation Agent Item) (A : Allocation Agent Item)
    (i j : Agent) : ℝ :=
  max 0 (v.value i (A j) - v.value i (A i))

/-- Envy-free allocations have no positive envy between any ordered pair. -/
def envyFree (v : Valuation Agent Item) (A : Allocation Agent Item) : Prop :=
  ∀ i j, v.value i (A j) ≤ v.value i (A i)

/-- Bounded-envy predicate used in Theorem 2.1. -/
def envyBoundedBy (v : Valuation Agent Item) (A : Allocation Agent Item)
    (alpha : ℝ) : Prop :=
  ∀ i j, envy v A i j ≤ alpha

/-- Maximum marginal item value. -/
def maxMarginal (v : Valuation Agent Item) : ℝ :=
  LMMS04FairDivision.paper_max_marginal v

/-- Allocation of exactly the specified finite set of goods. -/
def isAllocationOf (A : Allocation Agent Item) (goods : Finset Item) : Prop :=
  IsAllocationOf A goods

/-! ## Section 2: Bounded Envy -/

/--
Lemma 2.2: envy-cycle elimination preserves the allocated goods and envy bound
while producing an acyclic envy graph.
-/
theorem lemma2_2_acyclic_reduction
    (v : Valuation Agent Item) {alpha : ℝ} (goods : Finset Item)
    (A : Allocation Agent Item)
    (halloc : isAllocationOf A goods)
    (hbound : envyBoundedBy v A alpha) :
    ∃ B : Allocation Agent Item,
      isAllocationOf B goods ∧ envyBoundedBy v B alpha ∧
        AcyclicEnvyGraph v B := by
  exact
    LMMS04FairDivision.paper_lmms_lemma_2_2_acyclic_reduction
      v goods A halloc hbound

/--
Theorem 2.1: every finite indivisible-goods instance has an allocation whose
envy is bounded by the maximum marginal item value.
-/
theorem theorem2_1_bounded_envy_allocation_exists
    (v : Valuation Agent Item) (goods : Finset Item) :
    ∃ A, isAllocationOf A goods ∧ envyBoundedBy v A (maxMarginal v) := by
  exact LMMS04FairDivision.paper_lmms_theorem_2_1_existence v goods

/--
Theorem 2.1 alpha-bounded form: if every marginal value is at most `alpha`,
there is an allocation with envy at most `alpha`.
-/
theorem theorem2_1_alpha_bounded_allocation_exists
    (v : Valuation Agent Item) {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha) (hbound : MarginalBound v alpha)
    (goods : Finset Item) :
    ∃ A, isAllocationOf A goods ∧ envyBoundedBy v A alpha := by
  exact
    LMMS04FairDivision.paper_lmms_theorem_2_1_existence_alpha
      v halpha_nonneg hbound goods

/--
Theorem 2.1 constructive form: on a duplicate-free input list, the LMMS
algorithm returns an allocation of exactly `goodsList.toFinset` with envy
bounded by `alpha`.
-/
theorem theorem2_1_algorithm_correct_list_toFinset
    (v : Valuation Agent Item) {alpha : ℝ}
    (halpha_nonneg : 0 ≤ alpha) (hbound : MarginalBound v alpha)
    (goodsList : List Item) (hnodup : goodsList.Nodup) :
    isAllocationOf
        (LMMS04FairDivision.paper_lmms_algorithm v halpha_nonneg hbound goodsList)
        goodsList.toFinset ∧
      envyBoundedBy v
        (LMMS04FairDivision.paper_lmms_algorithm v halpha_nonneg hbound goodsList)
        alpha := by
  exact
    LMMS04FairDivision.paper_lmms_algorithm_correct_list_toFinset
      v halpha_nonneg hbound goodsList hnodup

/--
Theorem 2.3 and Lemma 2.4: for finite measures supported on a real interval,
bounded paper atoms imply a finite split into singleton high points and
residual low-mass pieces; Theorem 2.1 then gives envy at most `alpha`.
-/
theorem theorem2_3_real_interval_supported_atom_bound
    {mu : Agent → Measure ℝ} [∀ agent, IsFiniteMeasure (mu agent)]
    {alpha a b : ℝ} (halpha_pos : 0 < alpha)
    (hatoms : ∀ agent, Lemma24.PaperAtomsBoundedBy (mu agent) alpha)
    (haggregate_support :
      (aggregateMeasure mu).real ((Set.Ioc a b)ᶜ) = 0) :
    ∃ H : Finset ℝ,
      ∃ P : AppliedModelingLib.Probability.RealIntervalPartition
        ((aggregateMeasure mu).restrict (H : Set ℝ)ᶜ) alpha a b,
        letI := P.instFintype
        letI := P.instDecidableEq
        ∃ A : Allocation Agent ({x : ℝ // x ∈ H} ⊕ Option P.Piece),
          IsAllocationOf A
              (Finset.univ : Finset ({x : ℝ // x ∈ H} ⊕ Option P.Piece)) ∧
            EnvyBoundedBy
              (measurePartitionCertificateOfFiniteSingletonsAndResidualAggregate
                mu H (Lemma24.realIntervalResidualSet H P)
                (Lemma24.realIntervalResidualSet_measurable H P)
                (Lemma24.realIntervalResidualSet_pairwiseDisjoint H P)
                (Lemma24.realIntervalResidualSet_cover H P)
                (fun agent x _ => Lemma24.paper_atom_bound_implies_point_mass_bound
                  (mu agent) (le_of_lt halpha_pos) (hatoms agent) x)
                (Lemma24.realIntervalResidualSet_aggregate_le
                  (Agent := Agent) (le_of_lt halpha_pos) H P
                  haggregate_support)).valuation A alpha := by
  exact
    LMMS04FairDivision.paper_lmms_theorem_2_3_real_interval_supported_atom_bound
      halpha_pos hatoms haggregate_support

/-! ## Section 3: Lower Bounds and Identical Utilities -/

/--
Theorem 3.1, minimum-envy form: deterministic adaptive two-bit value-query
strategies whose query budget is asymptotically negligible relative to the
middle-pair hard-family count cannot eventually guarantee minimum envy on
every crossed hard profile.
-/
theorem theorem3_1_eventually_minimum_envy_lower_bound_from_twoBit_adaptive_queries
    {SourceItem : ℕ → Type*}
    [∀ n, Fintype (SourceItem n)] [∀ n, DecidableEq (SourceItem n)]
    {k q : ℕ → ℕ}
    (C : ∀ n, Theorem31.LMMS31MiddleComplementPairs (SourceItem n) (k n))
    (hcard_items : ∀ n, Fintype.card (SourceItem n) = 2 * k n)
    (strategy :
      ∀ n,
        Theorem31.AdaptiveQueryStrategy
          (Finset (SourceItem n)) (Bool × Bool))
    (output :
      ∀ n, Theorem31.QueryTranscript (Bool × Bool) (q n) →
        Allocation Theorem31.LMMS31Agent (SourceItem n))
    (hquery_ratio :
      AppliedModelingLib.Math.TendsToZero fun n =>
        (((2 * q n : ℕ) : ℝ) / (Fintype.card (C n).Pair : ℝ)))
    (hpair_pos : ∀ᶠ n in atTop, 0 < Fintype.card (C n).Pair) :
    ∀ᶠ n in atTop,
      ¬ ∀ choice₁ choice₂,
        MinimumReportEnvyAllocation
          (Theorem31.lmms31CrossReport
            ((C n).hardFunctionOfMiddleChoice choice₁)
            ((C n).hardFunctionOfMiddleChoice choice₂))
          (Finset.univ : Finset (SourceItem n))
          (output n
            (Theorem31.twoPlayerHardFunctionAdaptiveTranscript (strategy n)
              ((C n).hardFunctionOfMiddleChoice choice₁)
              ((C n).hardFunctionOfMiddleChoice choice₂))) := by
  exact
    LMMS04FairDivision.paper_lmms_theorem_3_1_eventually_minimum_envy_lower_bound_from_twoBit_adaptive_queries
      C hcard_items strategy output hquery_ratio hpair_pos

/--
Theorem 3.1, envy-ratio form: the same asymptotic adaptive-query lower bound
holds for minimum envy-ratio correctness.
-/
theorem theorem3_1_eventually_minimum_envy_ratio_lower_bound_from_twoBit_adaptive_queries
    {SourceItem : ℕ → Type*}
    [∀ n, Fintype (SourceItem n)] [∀ n, DecidableEq (SourceItem n)]
    {k q : ℕ → ℕ}
    (C : ∀ n, Theorem31.LMMS31MiddleComplementPairs (SourceItem n) (k n))
    (hcard_items : ∀ n, Fintype.card (SourceItem n) = 2 * k n)
    (strategy :
      ∀ n,
        Theorem31.AdaptiveQueryStrategy
          (Finset (SourceItem n)) (Bool × Bool))
    (output :
      ∀ n, Theorem31.QueryTranscript (Bool × Bool) (q n) →
        Allocation Theorem31.LMMS31Agent (SourceItem n))
    (hquery_ratio :
      AppliedModelingLib.Math.TendsToZero fun n =>
        (((2 * q n : ℕ) : ℝ) / (Fintype.card (C n).Pair : ℝ)))
    (hpair_pos : ∀ᶠ n in atTop, 0 < Fintype.card (C n).Pair) :
    ∀ᶠ n in atTop,
      ¬ ∀ choice₁ choice₂,
        Theorem31.MinimumReportEnvyRatioAllocation
          (Theorem31.lmms31CrossReport
            ((C n).hardFunctionOfMiddleChoice choice₁)
            ((C n).hardFunctionOfMiddleChoice choice₂))
          (Finset.univ : Finset (SourceItem n))
          (output n
            (Theorem31.twoPlayerHardFunctionAdaptiveTranscript (strategy n)
              ((C n).hardFunctionOfMiddleChoice choice₁)
              ((C n).hardFunctionOfMiddleChoice choice₂))) := by
  exact
    LMMS04FairDivision.paper_lmms_theorem_3_1_eventually_minimum_envy_ratio_lower_bound_from_twoBit_adaptive_queries
      C hcard_items strategy output hquery_ratio hpair_pos

/--
Theorem 3.2: a Graham `1.4` scheduling-approximation certificate gives the
corresponding envy-ratio bound in the identical-utilities fair-division model.
-/
theorem theorem3_2_graham_certificate_to_envy_ratio_bound
    {SourceAgent : Type*} {load : SourceAgent → ℝ} {optimalRatio : ℝ}
    (C : Theorem32.Graham14SchedulingApproximationCertificate
      load optimalRatio) :
    Theorem32.IdenticalUtilitiesEnvyRatioBound load
      (Theorem32.grahamApproximationFactor * optimalRatio) := by
  exact
    LMMS04FairDivision.paper_lmms_theorem_3_2_graham_certificate_to_envy_ratio_bound
      C

/-- The Theorem 3.2 approximation factor `1.4` is exactly `7 / 5`. -/
theorem theorem3_2_graham_factor_eq_seven_fifths :
    Theorem32.grahamApproximationFactor = (7 : ℝ) / 5 := by
  exact LMMS04FairDivision.paper_lmms_theorem_3_2_graham_factor_eq_seven_fifths

/--
Theorem 3.3 finite-load support: public alias for nonnegativity of the
identical-utilities allocation load ratio under positive per-agent loads.
-/
def theorem3_3_allocation_load_ratio_nonneg_of_loads_pos :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_allocation_load_ratio_nonneg_of_loads_pos

/--
Theorem 3.3 finite-load support: public alias identifying the allocation load
ratio with the scalar ratio used by the transfer layer.
-/
def theorem3_3_allocation_load_ratio_eq_transfer_ratio :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_allocation_load_ratio_eq_transfer_ratio

/--
Theorem 3.3 model-level transfer endpoint: public alias for the finite-model
`(1 + epsilon)` transfer certificate.
-/
def theorem3_3_model_ratio_transfer_certificate_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_model_ratio_transfer_certificate_epsilon

/--
Theorem 3.3 rounded-instance endpoint: public alias for the certificate-level
`(1 + epsilon)` ratio guarantee.
-/
def theorem3_3_rounded_instance_certificate_ratio_guarantee :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_rounded_instance_certificate_ratio_guarantee

/--
Theorem 3.3 rounded search endpoint: public alias for the finite value-pair
search certificate's final ratio guarantee.
-/
def theorem3_3_rounded_instance_search_certificate_ratio_guarantee :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_rounded_instance_search_certificate_ratio_guarantee

/--
Theorem 3.3 rounded search-certificate assembly: public alias packaging a
rounded allocation, output allocation, finite value-pair search certificate,
and the two transfer inequalities into the certificate consumed by the final
ratio endpoint.
-/
def theorem3_3_exists_rounded_instance_search_certificate_of_transfer :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_rounded_instance_search_certificate_of_transfer

/--
Theorem 3.3 rounded search-certificate assembly from additive transfer:
public alias deriving the certificate's transfer fields from the raw Lemma 3.5
max/min additive inequalities at `lambda = 56 / epsilon`.
-/
def theorem3_3_exists_rounded_instance_search_certificate_of_additive_transfer :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_rounded_instance_search_certificate_of_additive_transfer

/--
Theorem 3.3 rounded search-certificate assembly from agentwise additive
transfer: public alias globalizing per-agent Lemma 3.5 load estimates before
assembling the rounded-instance search certificate.
-/
def theorem3_3_exists_rounded_instance_search_certificate_of_agentwise_additive_transfer :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_rounded_instance_search_certificate_of_agentwise_additive_transfer

/--
Theorem 3.3 rounded search-certificate assembly from agentwise additive
transfer and Claim-3.4-style min/max windows: public alias deriving the
half-average and nonnegativity side conditions from `boundedAroundAverage`.
-/
def theorem3_3_exists_rounded_instance_search_certificate_of_agentwise_additive_transfer_with_bounded_min_max :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_rounded_instance_search_certificate_of_agentwise_additive_transfer_with_bounded_min_max

/--
Theorem 3.3 rounded search-certificate assembly from agentwise additive
transfer and per-agent Claim-3.4 windows: public alias projecting per-agent
rounded/optimal load windows to the min/max windows used by the transfer layer.
-/
def theorem3_3_exists_rounded_instance_search_certificate_of_agentwise_additive_transfer_with_allocation_windows :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_rounded_instance_search_certificate_of_agentwise_additive_transfer_with_allocation_windows

/--
Theorem 3.3 rounded search-certificate assembly from agentwise additive
transfer and per-agent Claim-3.4 windows: public alias deriving output
positive minimum load from the backward minimum transfer estimate.
-/
def theorem3_3_exists_rounded_instance_search_certificate_of_agentwise_additive_transfer_with_allocation_windows_of_backward_min :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_rounded_instance_search_certificate_of_agentwise_additive_transfer_with_allocation_windows_of_backward_min

/--
Theorem 3.3 rounded search-certificate assembly from Claim-3.4 certificates
and agentwise additive transfer: public alias using the certificates for the
rounded/optimal load windows and deriving output positive minimum load.
-/
def theorem3_3_exists_rounded_instance_search_certificate_of_agentwise_additive_transfer_with_claim34_certificates_of_backward_min :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_rounded_instance_search_certificate_of_agentwise_additive_transfer_with_claim34_certificates_of_backward_min

/--
Theorem 3.3 source/rounded transfer: public alias for the ratio-transfer
wrapper comparing source output, source optimum, and rounded loads that may
come from different item types.
-/
def theorem3_3_source_output_ratio_transfer_of_rounded_allocation :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_output_ratio_transfer_of_rounded_allocation

/--
Theorem 3.3 source/rounded transfer: public alias deriving the source output
positive-minimum premise from the rounded window and backward minimum transfer.
-/
def theorem3_3_source_output_ratio_transfer_of_rounded_allocation_of_backward_min :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_output_ratio_transfer_of_rounded_allocation_of_backward_min

/--
Theorem 3.3 source/rounded transfer: public alias for the ratio-level variant
that keeps only the backward direction agentwise and consumes scalar
source-to-rounded optimality.
-/
def theorem3_3_source_output_ratio_transfer_of_rounded_allocation_of_backward_min_and_forward_ratio :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_output_ratio_transfer_of_rounded_allocation_of_backward_min_and_forward_ratio

/--
Theorem 3.3 source/rounded transfer: public alias for the two-scale
ratio-level variant where the rounded allocation is bounded around `LR` and
`L <= LR` supplies the lower-half load bounds.
-/
def theorem3_3_source_output_ratio_transfer_of_rounded_allocation_of_backward_min_and_forward_ratio_two_scale :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_output_ratio_transfer_of_rounded_allocation_of_backward_min_and_forward_ratio_two_scale

/--
Theorem 3.3 source/rounded transfer: public alias assembling a source output
from exact high and low source partitions, then applying the epsilon ratio
transfer against an actual rounded allocation.
-/
def theorem3_3_source_output_ratio_transfer_of_exact_low_partition_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_output_ratio_transfer_of_exact_low_partition_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias assembling a source output
from high bundles and low owner estimates, then applying the epsilon ratio
transfer against an actual rounded allocation.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_owner_estimates_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_owner_estimates_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias for the owner-estimate
endpoint with scalar source-to-rounded optimality.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_owner_estimates_forward_ratio_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_owner_estimates_forward_ratio_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias constructing the low owner
map from ordered finite prefix targets before applying the epsilon ratio
transfer against an actual rounded allocation.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_finite_prefix_targets_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_finite_prefix_targets_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias for the finite-prefix
endpoint with scalar source-to-rounded optimality.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_finite_prefix_targets_forward_ratio_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_finite_prefix_targets_forward_ratio_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias for the finite-prefix target
endpoint with the low-good total stated as a finset sum.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_finite_prefix_targets_total_sum_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_finite_prefix_targets_total_sum_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias for the finite-prefix
total-sum endpoint with scalar source-to-rounded optimality.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_finite_prefix_targets_total_sum_forward_ratio_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_finite_prefix_targets_total_sum_forward_ratio_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias deriving finite-prefix low
target bounds from the aggregated low artificial-supply total.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_aggregated_lowRoundedLoad_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_aggregated_lowRoundedLoad_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias for the aggregated low-load
endpoint with scalar source-to-rounded optimality.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_aggregated_lowRoundedLoad_forward_ratio_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_aggregated_lowRoundedLoad_forward_ratio_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias deriving the aggregated low
target total from an exact allocation of the materialized low artificial goods.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_exact_aggregated_low_supply_allocation_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_exact_aggregated_low_supply_allocation_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias deriving the source output
directly from an exact allocation of the typed combined high/low materialization.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_exact_typed_combined_high_low_allocation_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_exact_typed_combined_high_low_allocation_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias deriving source output from
an exact typed combined allocation with scalar source-to-rounded optimality.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_exact_typed_combined_high_low_allocation_forward_ratio_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_exact_typed_combined_high_low_allocation_forward_ratio_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias deriving source output from
an exact typed combined allocation bounded around an actual rounded average
`LR`, using `L ≤ LR` and scalar source-to-rounded optimality.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_exact_typed_combined_high_low_allocation_forward_ratio_two_scale_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_exact_typed_combined_high_low_allocation_forward_ratio_two_scale_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias deriving source output from
an exact typed combined allocation, a Claim 3.4 source certificate, and
two-scale scalar source-to-rounded optimality.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_exact_typed_combined_high_low_allocation_claim_3_4_forward_ratio_two_scale_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_exact_typed_combined_high_low_allocation_claim_3_4_forward_ratio_two_scale_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias deriving the source output
from an exact typed combined high/low allocation and a Claim 3.4 certificate
for the bounded optimal source allocation.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_exact_typed_combined_high_low_allocation_claim_3_4_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_exact_typed_combined_high_low_allocation_claim_3_4_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias deriving source output from
an exact typed combined allocation, a Claim 3.4 source certificate, and scalar
source-to-rounded optimality.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_exact_typed_combined_high_low_allocation_claim_3_4_forward_ratio_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_exact_typed_combined_high_low_allocation_claim_3_4_forward_ratio_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias deriving both the source
output and the finite-search witness from one exact typed combined high/low
allocation.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_search_of_exact_typed_combined_high_low_allocation_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_search_of_exact_typed_combined_high_low_allocation_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias realizing a capped
value-pair search certificate at scale `L` and deriving source output once the
realized rounded allocation satisfies the forward comparison premises.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_forward_premises_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_forward_premises_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias realizing a capped search
certificate at scale `L` and deriving source output from scalar
source-to-rounded optimality.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_forward_ratio_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_forward_ratio_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias realizing a capped search
certificate and deriving source output from a scalar forward ratio bound for
the selected value pair.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_chosen_pair_forward_ratio_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_chosen_pair_forward_ratio_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias deriving the selected-pair
forward comparison from additive Lemma 3.5 pair estimates.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_chosen_pair_forward_additive_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_chosen_pair_forward_additive_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias realizing a two-scale capped
search certificate at actual rounded average `LR`; `L ≤ LR` discharges the
rounded-window side condition, leaving scalar source-to-rounded optimality as
the continuation premise.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_forward_ratio_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_forward_ratio_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias realizing a two-scale capped
search certificate and selected-pair forward comparison, using `L ≤ LR` to
close the rounded-window side condition.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_chosen_pair_forward_ratio_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_chosen_pair_forward_ratio_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias for the two-scale capped
search bridge where selected-pair forward comparison is proved from additive
Lemma 3.5 pair estimates.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_chosen_pair_forward_additive_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_chosen_pair_forward_additive_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias for the two-scale capped
search bridge with a feasible comparison capped IP and scalar forward bound.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_comparison_ip_forward_ratio_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_comparison_ip_forward_ratio_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias for the two-scale capped
search bridge whose comparison IP is induced by an exact typed combined
allocation.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_comparison_allocation_forward_ratio_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_comparison_allocation_forward_ratio_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias for the two-scale capped
search bridge with a comparison capped IP and additive Lemma 3.5 pair
estimates.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_comparison_ip_forward_additive_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_comparison_ip_forward_additive_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias for the two-scale bridge
whose comparison IP is induced by an exact typed allocation and whose scalar
forward comparison is proved from additive pair estimates.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_comparison_allocation_forward_additive_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_comparison_allocation_forward_additive_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a Claim 3.4 source
certificate for the two-scale capped-search bridge with selected-pair forward
comparison.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_claim_3_4_and_chosen_pair_forward_ratio_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_claim_3_4_and_chosen_pair_forward_ratio_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a Claim 3.4 source
certificate for the two-scale selected-pair additive bridge.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_claim_3_4_and_chosen_pair_forward_additive_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_claim_3_4_and_chosen_pair_forward_additive_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a Claim 3.4 source
certificate for the two-scale capped-search bridge with a comparison capped IP.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_claim_3_4_and_comparison_ip_forward_ratio_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_claim_3_4_and_comparison_ip_forward_ratio_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a Claim 3.4 source
certificate for the two-scale bridge whose comparison IP is induced by an
exact typed combined allocation.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_claim_3_4_and_comparison_allocation_forward_ratio_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_claim_3_4_and_comparison_allocation_forward_ratio_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a Claim 3.4 source
certificate for the two-scale capped-search bridge with a comparison capped IP
and additive pair estimates.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_claim_3_4_and_comparison_ip_forward_additive_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_claim_3_4_and_comparison_ip_forward_additive_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a Claim 3.4 source
certificate for the two-scale exact-comparison-allocation bridge with additive
pair estimates.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_claim_3_4_and_comparison_allocation_forward_additive_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_claim_3_4_and_comparison_allocation_forward_additive_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a Claim 3.4 source
certificate for the two-scale capped-search bridge whose comparison IP is the
source optimum's min/max pair.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_claim_3_4_and_source_min_max_comparison_ip_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_claim_3_4_and_source_min_max_comparison_ip_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias deriving source output from
a capped search certificate and a feasible comparison capped IP whose pair has
the scalar forward ratio bound.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_comparison_ip_forward_ratio_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_comparison_ip_forward_ratio_epsilon

/--
Theorem 3.3 value-pair forward transfer: public alias deriving the scalar
forward ratio bound for a value pair from Lemma 3.5 additive pair estimates.
-/
def theorem3_3_value_pair_forward_ratio_transfer_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_value_pair_forward_ratio_transfer_epsilon

/--
Theorem 3.3 value-pair forward transfer: public alias deriving the scalar
forward ratio bound for a source-average value pair from additive estimates.
-/
def theorem3_3_value_pair_forward_ratio_transfer_epsilon_of_source_average_additive_pair :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_value_pair_forward_ratio_transfer_epsilon_of_source_average_additive_pair

/--
Theorem 3.3 value-pair forward transfer: public alias for the identity
comparison case using the bounded source optimum's own min/max pair.
-/
def theorem3_3_source_min_max_value_pair_forward_ratio_transfer_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_min_max_value_pair_forward_ratio_transfer_epsilon

/--
Theorem 3.3 value-pair forward transfer: public alias consuming a Claim 3.4
source certificate and additive pair estimates.
-/
def theorem3_3_claim_3_4_value_pair_forward_ratio_transfer_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_claim_3_4_value_pair_forward_ratio_transfer_epsilon

/--
Theorem 3.3 value-pair forward transfer: public alias consuming a Claim 3.4
source certificate for the source optimum's own min/max pair.
-/
def theorem3_3_claim_3_4_source_min_max_value_pair_forward_ratio_transfer_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_claim_3_4_source_min_max_value_pair_forward_ratio_transfer_epsilon

/--
Theorem 3.3 capped value-pair support: public alias showing an admissible
capped value pair has positive first value at positive average scale.
-/
def theorem3_3_value_pair_first_pos_of_mem_roundedAdmissibleValuePairSetWithCap :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_value_pair_first_pos_of_mem_roundedAdmissibleValuePairSetWithCap

/--
Theorem 3.3 capped concrete-IP support: public alias showing a feasible
capped comparison pair has positive first value at positive average scale.
-/
def theorem3_3_capped_concrete_ip_pair_first_pos :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_capped_concrete_ip_pair_first_pos

/--
Theorem 3.3 capped comparison-IP support: public alias showing the bounded
source optimum's finite min/max loads form a capped value pair from rounded
type witnesses.
-/
def theorem3_3_source_min_max_pair_mem_roundedAdmissibleValuePairSetWithCap_of_types :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_min_max_pair_mem_roundedAdmissibleValuePairSetWithCap_of_types

/--
Theorem 3.3 capped comparison-IP support: public alias constructing the
source-min/max capped comparison IP from rounded type witnesses and a matching
type assignment for the combined high/low supply.
-/
def theorem3_3_source_min_max_comparison_ip_with_cap_of_type_assignment :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_min_max_comparison_ip_with_cap_of_type_assignment

/--
Theorem 3.3 capped comparison-IP support: public alias constructing the
source-min/max capped comparison IP from a load-realizing rounded type
assignment, selecting the finite min/max type witnesses internally.
-/
def theorem3_3_source_min_max_comparison_ip_with_cap_of_type_assignment_loads :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_min_max_comparison_ip_with_cap_of_type_assignment_loads

/--
Theorem 3.3 capped comparison-IP support: public alias deriving source-min/max
capped-window membership from a load-realizing rounded type assignment.
-/
def theorem3_3_source_min_max_type_assignment_mem_window_with_cap_of_loads :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_min_max_type_assignment_mem_window_with_cap_of_loads

/--
Theorem 3.3 capped comparison-IP support: public alias constructing the
source-min/max capped comparison IP from only a load-realizing rounded type
assignment and matching rounded-supply counts.
-/
def theorem3_3_source_min_max_comparison_ip_with_cap_of_type_assignment_loads_and_counts :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_min_max_comparison_ip_with_cap_of_type_assignment_loads_and_counts

/--
Theorem 3.3 capped comparison-IP support: public alias constructing the
source-min/max comparison IP at a larger search cap from a smaller-cap
load/count certificate.
-/
def theorem3_3_source_min_max_comparison_ip_with_larger_cap_of_type_assignment_loads_and_counts :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_min_max_comparison_ip_with_larger_cap_of_type_assignment_loads_and_counts

/--
Theorem 3.3 capped comparison-IP support: public alias constructing the
source-min/max comparison IP at a larger search cap from an existential
load/count type-assignment provider.
-/
def theorem3_3_source_min_max_comparison_ip_with_larger_cap_of_type_assignment_provider :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_min_max_comparison_ip_with_larger_cap_of_type_assignment_provider

/--
Theorem 3.3 capped comparison-IP support: public alias constructing the
source-min/max comparison IP at the paper's source auto-cap from load/count
type-assignment data.
-/
def theorem3_3_source_min_max_comparison_ip_with_source_auto_cap_of_type_assignment_loads_and_counts :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_min_max_comparison_ip_with_source_auto_cap_of_type_assignment_loads_and_counts

/--
Theorem 3.3 capped comparison-IP support: public alias constructing the
source-min/max comparison IP at the paper's source auto-cap from an existential
load/count type-assignment provider.
-/
def theorem3_3_source_min_max_comparison_ip_with_source_auto_cap_of_type_assignment_provider :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_min_max_comparison_ip_with_source_auto_cap_of_type_assignment_provider

/--
Theorem 3.3 capped comparison-IP support: public alias extracting an
existential source-min/max load/count type-assignment provider from an exact
typed combined allocation whose rounded loads match the source optimum.
-/
def theorem3_3_source_min_max_type_assignment_provider_of_exact_typed_combined_high_low_allocation_loads :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_min_max_type_assignment_provider_of_exact_typed_combined_high_low_allocation_loads

/--
Theorem 3.3 capped comparison-IP support: public alias constructing the
source-min/max capped comparison IP from an exact typed combined allocation
whose rounded loads match the source optimum loads.
-/
def theorem3_3_source_min_max_comparison_ip_with_cap_of_exact_typed_combined_high_low_allocation_loads :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_min_max_comparison_ip_with_cap_of_exact_typed_combined_high_low_allocation_loads

/--
Theorem 3.3 capped comparison-IP support: public alias constructing the
source-min/max comparison IP at a larger search cap from an exact typed
combined allocation certified at a smaller cap.
-/
def theorem3_3_source_min_max_comparison_ip_with_larger_cap_of_exact_typed_combined_high_low_allocation_loads :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_min_max_comparison_ip_with_larger_cap_of_exact_typed_combined_high_low_allocation_loads

/--
Theorem 3.3 capped comparison-IP support: public alias constructing the
source-min/max comparison IP at the paper's source auto-cap from an exact typed
combined allocation whose rounded loads match the source optimum loads.
-/
def theorem3_3_source_min_max_comparison_ip_with_source_auto_cap_of_exact_typed_combined_high_low_allocation_loads :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_min_max_comparison_ip_with_source_auto_cap_of_exact_typed_combined_high_low_allocation_loads

/--
Theorem 3.3 finite search support: public alias producing a larger-capped
search certificate from a load-realizing source-min/max type assignment
certified at a smaller cap.
-/
def theorem3_3_exists_value_pair_search_certificate_with_larger_cap_of_source_min_max_type_assignment_loads :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_larger_cap_of_source_min_max_type_assignment_loads

/--
Theorem 3.3 finite search support: public alias producing a larger-capped
search certificate from a source-min/max load/count type assignment certified
at a smaller cap.
-/
def theorem3_3_exists_value_pair_search_certificate_with_larger_cap_of_source_min_max_type_assignment_loads_and_counts :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_larger_cap_of_source_min_max_type_assignment_loads_and_counts

/--
Theorem 3.3 finite search support: public alias producing a two-scale
larger-capped search certificate from a windowed source-min/max load/count
type-assignment witness.
-/
def theorem3_3_exists_value_pair_search_certificate_with_two_scale_larger_cap_of_windowed_type_assignment_loads_and_counts :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_two_scale_larger_cap_of_windowed_type_assignment_loads_and_counts

/--
Theorem 3.3 finite search support: public alias producing a two-scale
larger-capped search certificate from an existential windowed source-min/max
load/count provider.
-/
def theorem3_3_exists_value_pair_search_certificate_with_two_scale_larger_cap_of_windowed_type_assignment_loads_and_counts_provider :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_two_scale_larger_cap_of_windowed_type_assignment_loads_and_counts_provider

/--
Theorem 3.3 finite search support: public alias producing the paper's
source-auto-cap two-scale search certificate from a windowed source-min/max
load/count witness.
-/
def theorem3_3_exists_value_pair_search_certificate_with_two_scale_source_auto_cap_of_windowed_type_assignment_loads_and_counts :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_two_scale_source_auto_cap_of_windowed_type_assignment_loads_and_counts

/--
Theorem 3.3 finite search support: public alias producing the paper's
source-auto-cap two-scale search certificate from an existential windowed
source-min/max load/count provider.
-/
def theorem3_3_exists_value_pair_search_certificate_with_two_scale_source_auto_cap_of_windowed_type_assignment_loads_and_counts_provider :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_two_scale_source_auto_cap_of_windowed_type_assignment_loads_and_counts_provider

/--
Theorem 3.3 finite search support: public alias producing a larger-capped
search certificate from an exact typed combined allocation whose rounded loads
match the source optimum.
-/
def theorem3_3_exists_value_pair_search_certificate_with_larger_cap_of_exact_typed_combined_high_low_allocation_loads :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_larger_cap_of_exact_typed_combined_high_low_allocation_loads

/--
Theorem 3.3 finite search support: public alias producing a two-scale
larger-capped search certificate from an exact typed combined allocation whose
loads match the source optimum.
-/
def theorem3_3_exists_value_pair_search_certificate_with_two_scale_larger_cap_of_windowed_exact_typed_combined_high_low_allocation_loads :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_two_scale_larger_cap_of_windowed_exact_typed_combined_high_low_allocation_loads

/--
Theorem 3.3 finite search support: public alias producing the paper's
source-auto-cap two-scale search certificate from an exact typed combined
allocation whose loads match the source optimum.
-/
def theorem3_3_exists_value_pair_search_certificate_with_two_scale_source_auto_cap_of_windowed_exact_typed_combined_high_low_allocation_loads :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_two_scale_source_auto_cap_of_windowed_exact_typed_combined_high_low_allocation_loads

/--
Theorem 3.3 finite search support: public alias showing the bounded rounded
type box is monotone in the count cap.
-/
def theorem3_3_boundedRoundedBundleTypeSet_mono_of_le :=
  @Theorem33.boundedRoundedBundleTypeSet_mono_of_le

/--
Theorem 3.3 finite search support: public alias showing the capped admissible
type set is monotone in the count cap.
-/
def theorem3_3_roundedAdmissibleTypeSetWithCap_mono_of_le :=
  @Theorem33.roundedAdmissibleTypeSetWithCap_mono_of_le

/--
Theorem 3.3 finite search support: public alias showing the capped admissible
value set is monotone in the count cap.
-/
def theorem3_3_roundedAdmissibleValueSetWithCap_mono_of_le :=
  @Theorem33.roundedAdmissibleValueSetWithCap_mono_of_le

/--
Theorem 3.3 finite search support: public alias showing the capped admissible
value-pair set is monotone in the count cap.
-/
def theorem3_3_roundedAdmissibleValuePairSetWithCap_mono_of_le :=
  @Theorem33.roundedAdmissibleValuePairSetWithCap_mono_of_le

/--
Theorem 3.3 finite search support: public alias showing selected capped type
windows are monotone in the count cap.
-/
def theorem3_3_roundedTypesInValueWindowWithCap_mono_of_le :=
  @Theorem33.roundedTypesInValueWindowWithCap_mono_of_le

/--
Theorem 3.3 finite search support: public alias lifting a concrete capped IP
certificate to any larger count cap.
-/
def theorem3_3_roundedConcreteIPCertificateWithCap_mono_of_le :=
  @Theorem33.RoundedConcreteIPCertificateWithCap.mono_of_le

/--
Theorem 3.3 finite search support: public alias invoking the larger capped
search from a feasible pair certified at a smaller cap.
-/
def theorem3_3_exists_roundedValuePairSearchCertificateWithCap_of_smaller_cap_feasible_pair :=
  @Theorem33.exists_roundedValuePairSearchCertificateWithCap_of_smaller_cap_feasible_pair

/--
Theorem 3.3 finite search support: public alias lifting a paper-level capped
concrete IP certificate to a larger count cap.
-/
def theorem3_3_concrete_ip_certificate_with_cap_mono_of_le :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_concrete_ip_certificate_with_cap_mono_of_le

/--
Theorem 3.3 finite search support: public alias producing a larger-capped
search certificate from a concrete IP certified at a smaller cap.
-/
def theorem3_3_exists_value_pair_search_certificate_with_larger_cap_of_concrete_ip :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_larger_cap_of_concrete_ip

/--
Theorem 3.3 finite search support: public alias comparing a capped search
certificate against an allocation's own min/max load pair.
-/
def theorem3_3_value_pair_search_with_cap_ratio_le_allocation_min_max_of_concrete_ip :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_value_pair_search_with_cap_ratio_le_allocation_min_max_of_concrete_ip

/--
Theorem 3.3 finite search support: public alias producing a capped search
certificate bounded by an allocation's own min/max load ratio.
-/
def theorem3_3_exists_value_pair_search_certificate_with_cap_ratio_le_allocation_min_max_of_concrete_ip :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_cap_ratio_le_allocation_min_max_of_concrete_ip

/--
Theorem 3.3 finite search support: public alias producing a larger-capped search
certificate bounded by an allocation's own min/max load ratio.
-/
def theorem3_3_exists_value_pair_search_certificate_with_larger_cap_ratio_le_allocation_min_max_of_concrete_ip :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_larger_cap_ratio_le_allocation_min_max_of_concrete_ip

/--
Theorem 3.3 finite search support: public alias for the larger-capped search
and rounded-instance guarantee from a concrete IP certified at a smaller cap.
-/
def theorem3_3_exists_value_pair_search_certificate_with_larger_cap_ratio_guarantee_of_concrete_ip :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_larger_cap_ratio_guarantee_of_concrete_ip

/--
Theorem 3.3 finite search support: public alias producing a larger-capped
search certificate from a type assignment certified at a smaller cap.
-/
def theorem3_3_exists_value_pair_search_certificate_with_larger_cap_of_supply_type_assignment :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_larger_cap_of_supply_type_assignment

/--
Theorem 3.3 finite search support: public alias extracting a typed combined
high/low rounded type assignment with its per-agent rounded-load identities.
-/
def theorem3_3_exists_typed_combined_high_low_type_assignment_with_loads_of_exact_bounded_allocation :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_typed_combined_high_low_type_assignment_with_loads_of_exact_bounded_allocation

/--
Theorem 3.3 finite search support: public alias extracting a typed combined
high/low rounded type assignment with per-agent load identities, capped
two-scale window membership, and matching high-plus-low supply counts.
-/
def theorem3_3_exists_typed_combined_high_low_type_assignment_with_cap_loads_of_exact_bounded_allocation :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_typed_combined_high_low_type_assignment_with_cap_loads_of_exact_bounded_allocation

/--
Theorem 3.3 source/rounded transfer: public alias deriving source output from
a capped search certificate, a feasible comparison capped IP, and forward
additive pair estimates.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_comparison_ip_forward_additive_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_comparison_ip_forward_additive_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias bounding the selected larger
capped search pair by the source optimum's min/max forward-ratio comparison.
-/
def theorem3_3_selected_pair_forward_ratio_of_larger_cap_source_min_max_comparison_ip_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_selected_pair_forward_ratio_of_larger_cap_source_min_max_comparison_ip_epsilon

/--
Theorem 3.3 source/rounded transfer: public Claim-3.4 alias bounding the
selected larger capped search pair by the source optimum's min/max
forward-ratio comparison.
-/
def theorem3_3_selected_pair_forward_ratio_of_larger_cap_claim_3_4_source_min_max_comparison_ip_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_selected_pair_forward_ratio_of_larger_cap_claim_3_4_source_min_max_comparison_ip_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias deriving source output from
a capped comparison IP for the bounded source optimum's own min/max pair.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_source_min_max_comparison_ip_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_source_min_max_comparison_ip_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias internally producing the
larger-capped search certificate from a smaller-cap source-min/max comparison
IP and then deriving source output.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_larger_cap_search_of_source_min_max_comparison_ip_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_larger_cap_search_of_source_min_max_comparison_ip_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias for the larger-capped
source-min/max package that also returns the selected-pair forward-ratio bound.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_larger_cap_search_with_selected_pair_forward_ratio_of_source_min_max_comparison_ip_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_larger_cap_search_with_selected_pair_forward_ratio_of_source_min_max_comparison_ip_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias deriving source output from
source-min/max rounded type witnesses and a matching combined-supply type
assignment.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_source_min_max_type_assignment_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_source_min_max_type_assignment_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias deriving source output from
a load-realizing source-min/max rounded type assignment, selecting the finite
min/max type witnesses internally.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_source_min_max_type_assignment_loads_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_source_min_max_type_assignment_loads_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias deriving source output from
a source-min/max rounded type assignment whose loads match the source optimum
and whose counts match the combined rounded supply.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_source_min_max_type_assignment_loads_and_counts_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_source_min_max_type_assignment_loads_and_counts_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias deriving source output from
a smaller-cap source-min/max load/count certificate lifted to the search cap.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_source_min_max_type_assignment_loads_and_counts_larger_cap_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_source_min_max_type_assignment_loads_and_counts_larger_cap_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias internally producing the
larger-capped search certificate from a smaller-cap source-min/max load/count
type assignment and then deriving source output.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_larger_cap_search_of_source_min_max_type_assignment_loads_and_counts_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_larger_cap_search_of_source_min_max_type_assignment_loads_and_counts_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias internally producing search
at the paper's source auto-cap from source-min/max load/count type-assignment
data and then deriving source output.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_source_auto_cap_search_of_source_min_max_type_assignment_loads_and_counts_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_source_auto_cap_search_of_source_min_max_type_assignment_loads_and_counts_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias internally producing search
and source output from an existential source-min/max load/count type-assignment
provider.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_larger_cap_search_of_source_min_max_type_assignment_provider_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_larger_cap_search_of_source_min_max_type_assignment_provider_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias internally producing search
at the paper's source auto-cap from an existential source-min/max load/count
type-assignment provider.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_source_auto_cap_search_of_source_min_max_type_assignment_provider_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_source_auto_cap_search_of_source_min_max_type_assignment_provider_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias internally producing the
larger-capped search certificate, selected-pair forward-ratio bound, and source
output from source-min/max load/count type-assignment data.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_larger_cap_search_with_selected_pair_forward_ratio_of_source_min_max_type_assignment_loads_and_counts_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_larger_cap_search_with_selected_pair_forward_ratio_of_source_min_max_type_assignment_loads_and_counts_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias internally producing the
source-auto-cap search certificate, selected-pair forward-ratio bound, and
source output from source-min/max load/count type-assignment data.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_source_auto_cap_search_with_selected_pair_forward_ratio_of_source_min_max_type_assignment_loads_and_counts_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_source_auto_cap_search_with_selected_pair_forward_ratio_of_source_min_max_type_assignment_loads_and_counts_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias internally producing search,
selected-pair forward-ratio bound, and source output from an existential
source-min/max load/count type-assignment provider.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_larger_cap_search_with_selected_pair_forward_ratio_of_source_min_max_type_assignment_provider_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_larger_cap_search_with_selected_pair_forward_ratio_of_source_min_max_type_assignment_provider_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias internally producing the
source-auto-cap search certificate, selected-pair forward-ratio bound, and
source output from an existential source-min/max load/count provider.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_source_auto_cap_search_with_selected_pair_forward_ratio_of_source_min_max_type_assignment_provider_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_source_auto_cap_search_with_selected_pair_forward_ratio_of_source_min_max_type_assignment_provider_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias deriving source output from
a capped search certificate plus an exact typed combined allocation whose
rounded loads match the source optimum.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_exact_typed_combined_high_low_allocation_loads_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_exact_typed_combined_high_low_allocation_loads_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias deriving source output from
a capped search certificate plus a smaller-cap exact typed combined allocation
whose rounded loads match the source optimum.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_exact_typed_combined_high_low_allocation_loads_larger_cap_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_exact_typed_combined_high_low_allocation_loads_larger_cap_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias internally producing the
larger-capped search certificate from an exact typed combined allocation and
then deriving source output.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_larger_cap_search_of_exact_typed_combined_high_low_allocation_loads_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_larger_cap_search_of_exact_typed_combined_high_low_allocation_loads_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias internally producing search
at the paper's source auto-cap from an exact typed combined allocation whose
rounded loads match the source optimum.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_source_auto_cap_search_of_exact_typed_combined_high_low_allocation_loads_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_source_auto_cap_search_of_exact_typed_combined_high_low_allocation_loads_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias internally producing search,
selected-pair forward-ratio bound, and source output from an exact typed
combined allocation whose rounded loads match the source optimum.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_larger_cap_search_with_selected_pair_forward_ratio_of_exact_typed_combined_high_low_allocation_loads_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_larger_cap_search_with_selected_pair_forward_ratio_of_exact_typed_combined_high_low_allocation_loads_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias internally producing the
source-auto-cap search certificate, selected-pair forward-ratio bound, and
source output from an exact typed combined allocation.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_source_auto_cap_search_with_selected_pair_forward_ratio_of_exact_typed_combined_high_low_allocation_loads_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_source_auto_cap_search_with_selected_pair_forward_ratio_of_exact_typed_combined_high_low_allocation_loads_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias deriving source output from
a capped search certificate plus an exact bounded typed combined comparison
allocation with a scalar forward ratio bound.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_comparison_allocation_forward_ratio_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_comparison_allocation_forward_ratio_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias internally producing the
search certificate from an exact bounded typed combined comparison allocation
with a scalar forward ratio bound.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_search_of_comparison_allocation_forward_ratio_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_search_of_comparison_allocation_forward_ratio_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias deriving source output from
a capped search certificate plus an exact bounded typed combined comparison
allocation with forward additive pair estimates.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_comparison_allocation_forward_additive_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_comparison_allocation_forward_additive_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias internally producing the
search certificate from an exact bounded typed combined comparison allocation
with forward additive pair estimates.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_search_of_comparison_allocation_forward_additive_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_search_of_comparison_allocation_forward_additive_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias realizing a capped search
certificate, consuming a Claim 3.4 source certificate, and leaving only scalar
source-to-rounded optimality.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_claim_3_4_forward_ratio_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_claim_3_4_forward_ratio_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a Claim 3.4 source
certificate and a scalar forward ratio bound for the capped search's selected
value pair.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_claim_3_4_and_chosen_pair_forward_ratio_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_claim_3_4_and_chosen_pair_forward_ratio_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a Claim 3.4 source
certificate and deriving the selected-pair forward comparison from additive
Lemma 3.5 pair estimates.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_claim_3_4_and_chosen_pair_forward_additive_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_claim_3_4_and_chosen_pair_forward_additive_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a Claim 3.4 source
certificate plus a feasible comparison capped IP whose pair has the scalar
forward ratio bound.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_claim_3_4_and_comparison_ip_forward_ratio_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_claim_3_4_and_comparison_ip_forward_ratio_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a Claim 3.4 source
certificate, a feasible comparison capped IP, and forward additive pair
estimates.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_claim_3_4_and_comparison_ip_forward_additive_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_claim_3_4_and_comparison_ip_forward_additive_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a Claim 3.4 source
certificate and a capped comparison IP for that source optimum's own min/max
pair.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_claim_3_4_and_source_min_max_comparison_ip_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_claim_3_4_and_source_min_max_comparison_ip_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a Claim 3.4 source
certificate, internally producing the larger-capped search certificate from a
smaller-cap source-min/max comparison IP, and deriving source output.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_larger_cap_search_of_claim_3_4_source_min_max_comparison_ip_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_larger_cap_search_of_claim_3_4_source_min_max_comparison_ip_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias for the Claim 3.4
larger-capped source-min/max package that also returns the selected-pair
forward-ratio bound.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_larger_cap_search_with_selected_pair_forward_ratio_of_claim_3_4_source_min_max_comparison_ip_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_larger_cap_search_with_selected_pair_forward_ratio_of_claim_3_4_source_min_max_comparison_ip_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a Claim 3.4 source
certificate, internally producing the two-scale larger-capped search
certificate from a smaller-cap source-min/max comparison IP, and deriving
source output.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_two_scale_larger_cap_search_of_claim_3_4_source_min_max_comparison_ip_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_larger_cap_search_of_claim_3_4_source_min_max_comparison_ip_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias for the Claim 3.4 two-scale
larger-capped source-min/max package that also returns the selected-pair
forward-ratio bound.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_two_scale_larger_cap_search_with_selected_pair_forward_ratio_of_claim_3_4_source_min_max_comparison_ip_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_larger_cap_search_with_selected_pair_forward_ratio_of_claim_3_4_source_min_max_comparison_ip_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a Claim 3.4 source
certificate and a smaller-cap source-min/max comparison IP, with two-scale
search fixed to the paper's source auto-cap.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_two_scale_source_auto_cap_search_of_claim_3_4_source_min_max_comparison_ip_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_source_auto_cap_search_of_claim_3_4_source_min_max_comparison_ip_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias for the Claim 3.4 two-scale
source-auto-cap source-min/max package that also returns the selected-pair
forward-ratio bound.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_two_scale_source_auto_cap_search_with_selected_pair_forward_ratio_of_claim_3_4_source_min_max_comparison_ip_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_source_auto_cap_search_with_selected_pair_forward_ratio_of_claim_3_4_source_min_max_comparison_ip_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a Claim 3.4 source
certificate plus a two-scale source-min/max value window and matching
type-assignment provider, then internally producing the larger-capped search
certificate and source output.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_two_scale_larger_cap_search_of_claim_3_4_source_min_max_windowed_type_assignment_provider_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_larger_cap_search_of_claim_3_4_source_min_max_windowed_type_assignment_provider_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a Claim 3.4 source
certificate plus a two-scale source-min/max value window and matching
type-assignment provider, then producing the larger-capped search certificate,
selected-pair forward-ratio bound, and source output.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_two_scale_larger_cap_search_with_selected_pair_forward_ratio_of_claim_3_4_source_min_max_windowed_type_assignment_provider_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_larger_cap_search_with_selected_pair_forward_ratio_of_claim_3_4_source_min_max_windowed_type_assignment_provider_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a Claim 3.4 source
certificate plus a two-scale source-min/max value window and matching
type-assignment provider, with search fixed to the paper's source auto-cap.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_two_scale_source_auto_cap_search_of_claim_3_4_source_min_max_windowed_type_assignment_provider_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_source_auto_cap_search_of_claim_3_4_source_min_max_windowed_type_assignment_provider_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a Claim 3.4 source
certificate plus a two-scale source-min/max value window and matching
type-assignment provider, then producing the source-auto-cap search
certificate, selected-pair forward-ratio bound, and source output.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_two_scale_source_auto_cap_search_with_selected_pair_forward_ratio_of_claim_3_4_source_min_max_windowed_type_assignment_provider_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_source_auto_cap_search_with_selected_pair_forward_ratio_of_claim_3_4_source_min_max_windowed_type_assignment_provider_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias deriving the two-scale
source-min/max value-pair membership from a load-realizing windowed type
assignment.
-/
def theorem3_3_source_min_max_pair_mem_roundedAdmissibleValuePairSetWithCap_of_windowed_type_assignment_loads :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_min_max_pair_mem_roundedAdmissibleValuePairSetWithCap_of_windowed_type_assignment_loads

/--
Theorem 3.3 source/rounded transfer: public alias constructing the two-scale
source-min/max comparison IP from a load-realizing windowed type assignment
with matching rounded-supply counts.
-/
def theorem3_3_source_min_max_comparison_ip_with_cap_of_windowed_type_assignment_loads_and_counts :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_min_max_comparison_ip_with_cap_of_windowed_type_assignment_loads_and_counts

/--
Theorem 3.3 source/rounded transfer: public alias constructing the two-scale
source-min/max comparison IP at a larger search cap from a smaller-cap
windowed load/count witness.
-/
def theorem3_3_source_min_max_comparison_ip_with_larger_cap_of_windowed_type_assignment_loads_and_counts :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_min_max_comparison_ip_with_larger_cap_of_windowed_type_assignment_loads_and_counts

/--
Theorem 3.3 source/rounded transfer: public alias constructing the two-scale
source-min/max comparison IP at a larger search cap from an existential
windowed load/count provider.
-/
def theorem3_3_source_min_max_comparison_ip_with_larger_cap_of_windowed_type_assignment_loads_and_counts_provider :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_min_max_comparison_ip_with_larger_cap_of_windowed_type_assignment_loads_and_counts_provider

/--
Theorem 3.3 source/rounded transfer: public alias constructing the two-scale
source-min/max comparison IP at the paper's source auto-cap from a smaller-cap
windowed load/count witness.
-/
def theorem3_3_source_min_max_comparison_ip_with_source_auto_cap_of_windowed_type_assignment_loads_and_counts :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_min_max_comparison_ip_with_source_auto_cap_of_windowed_type_assignment_loads_and_counts

/--
Theorem 3.3 source/rounded transfer: public alias constructing the two-scale
source-min/max comparison IP at the paper's source auto-cap from an existential
windowed load/count provider.
-/
def theorem3_3_source_min_max_comparison_ip_with_source_auto_cap_of_windowed_type_assignment_loads_and_counts_provider :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_min_max_comparison_ip_with_source_auto_cap_of_windowed_type_assignment_loads_and_counts_provider

/--
Theorem 3.3 source/rounded transfer: public alias extracting the two-scale
source-min/max windowed type-assignment provider from an exact typed combined
allocation whose loads match the source optimum.
-/
def theorem3_3_source_min_max_windowed_type_assignment_provider_of_exact_typed_combined_high_low_allocation_loads :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_min_max_windowed_type_assignment_provider_of_exact_typed_combined_high_low_allocation_loads

/--
Theorem 3.3 source/rounded transfer: public alias constructing the two-scale
source-min/max comparison IP from an exact typed combined allocation whose
loads match the source optimum.
-/
def theorem3_3_source_min_max_comparison_ip_with_cap_of_windowed_exact_typed_combined_high_low_allocation_loads :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_min_max_comparison_ip_with_cap_of_windowed_exact_typed_combined_high_low_allocation_loads

/--
Theorem 3.3 source/rounded transfer: public alias constructing the two-scale
source-min/max comparison IP at a larger search cap from an exact typed
combined allocation whose loads match the source optimum.
-/
def theorem3_3_source_min_max_comparison_ip_with_larger_cap_of_windowed_exact_typed_combined_high_low_allocation_loads :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_min_max_comparison_ip_with_larger_cap_of_windowed_exact_typed_combined_high_low_allocation_loads

/--
Theorem 3.3 source/rounded transfer: public alias constructing the two-scale
source-min/max comparison IP at the paper's source auto-cap from an exact typed
combined allocation whose loads match the source optimum.
-/
def theorem3_3_source_min_max_comparison_ip_with_source_auto_cap_of_windowed_exact_typed_combined_high_low_allocation_loads :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_min_max_comparison_ip_with_source_auto_cap_of_windowed_exact_typed_combined_high_low_allocation_loads

/--
Theorem 3.3 source/rounded transfer: public alias consuming a two-scale
capped search certificate and an exact typed combined allocation whose loads
match the Claim 3.4 source optimum.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_claim_3_4_and_windowed_exact_typed_combined_high_low_allocation_loads_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_claim_3_4_and_windowed_exact_typed_combined_high_low_allocation_loads_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a two-scale
capped search certificate at a larger cap and an exact typed combined
allocation certified at a smaller cap.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_claim_3_4_and_windowed_exact_typed_combined_high_low_allocation_loads_larger_cap_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_claim_3_4_and_windowed_exact_typed_combined_high_low_allocation_loads_larger_cap_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a two-scale
capped search certificate fixed to the paper's source auto-cap and an exact
typed combined allocation whose loads match the Claim 3.4 source optimum.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_claim_3_4_and_windowed_exact_typed_combined_high_low_allocation_loads_source_auto_cap_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_claim_3_4_and_windowed_exact_typed_combined_high_low_allocation_loads_source_auto_cap_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias producing a larger-capped
two-scale search certificate and source output from an exact typed combined
allocation whose loads match the Claim 3.4 source optimum.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_two_scale_larger_cap_search_of_claim_3_4_windowed_exact_typed_combined_high_low_allocation_loads_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_larger_cap_search_of_claim_3_4_windowed_exact_typed_combined_high_low_allocation_loads_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias producing a larger-capped
two-scale search certificate, selected-pair forward-ratio bound, and source
output from an exact typed combined allocation whose loads match the Claim 3.4
source optimum.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_two_scale_larger_cap_search_with_selected_pair_forward_ratio_of_claim_3_4_windowed_exact_typed_combined_high_low_allocation_loads_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_larger_cap_search_with_selected_pair_forward_ratio_of_claim_3_4_windowed_exact_typed_combined_high_low_allocation_loads_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias producing the paper's
source-auto-cap two-scale search certificate and source output from an exact
typed combined allocation whose loads match the Claim 3.4 source optimum.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_two_scale_source_auto_cap_search_of_claim_3_4_windowed_exact_typed_combined_high_low_allocation_loads_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_source_auto_cap_search_of_claim_3_4_windowed_exact_typed_combined_high_low_allocation_loads_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias producing the paper's
source-auto-cap two-scale search certificate, selected-pair forward-ratio
bound, and source output from an exact typed combined allocation whose loads
match the Claim 3.4 source optimum.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_two_scale_source_auto_cap_search_with_selected_pair_forward_ratio_of_claim_3_4_windowed_exact_typed_combined_high_low_allocation_loads_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_source_auto_cap_search_with_selected_pair_forward_ratio_of_claim_3_4_windowed_exact_typed_combined_high_low_allocation_loads_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a two-scale
capped search certificate and a load-realizing source-min/max windowed
type-assignment witness.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a two-scale
capped search certificate and an existential source-min/max windowed
load/count provider.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_provider_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_provider_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a two-scale
capped search certificate at a larger cap and a smaller-cap source-min/max
windowed load/count witness.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_larger_cap_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_larger_cap_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a larger-cap
two-scale capped search certificate and an existential smaller-cap
source-min/max windowed load/count provider.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_larger_cap_provider_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_larger_cap_provider_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a two-scale
capped search certificate fixed to the paper's source auto-cap and a
source-min/max windowed load/count witness.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_source_auto_cap_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_source_auto_cap_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a two-scale
capped search certificate fixed to the paper's source auto-cap and an
existential source-min/max windowed load/count provider.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_source_auto_cap_provider_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_two_scale_capped_search_certificate_with_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_source_auto_cap_provider_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a Claim 3.4 source
certificate plus load-realizing two-scale source-min/max type assignment data,
then internally producing the larger-capped search certificate and source
output.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_two_scale_larger_cap_search_of_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_larger_cap_search_of_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming load-realizing
two-scale source-min/max type assignment data, then producing the larger-capped
search certificate, selected-pair forward-ratio bound, and source output.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_two_scale_larger_cap_search_with_selected_pair_forward_ratio_of_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_larger_cap_search_with_selected_pair_forward_ratio_of_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a Claim 3.4 source
certificate plus load-realizing two-scale source-min/max type assignment data,
with search fixed to the paper's source auto-cap.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_two_scale_source_auto_cap_search_of_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_source_auto_cap_search_of_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming load-realizing
two-scale source-min/max type assignment data, then producing the
source-auto-cap search certificate, selected-pair forward-ratio bound, and
source output.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_two_scale_source_auto_cap_search_with_selected_pair_forward_ratio_of_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_source_auto_cap_search_with_selected_pair_forward_ratio_of_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming an existential
load/count provider for the two-scale source-min/max windowed type-assignment
boundary.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_two_scale_larger_cap_search_of_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_provider_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_larger_cap_search_of_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_provider_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming an existential
load/count provider and producing the larger-capped search certificate,
selected-pair forward-ratio bound, and source output.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_two_scale_larger_cap_search_with_selected_pair_forward_ratio_of_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_provider_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_larger_cap_search_with_selected_pair_forward_ratio_of_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_provider_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming an existential
load/count provider for the two-scale source-min/max windowed type-assignment
boundary, with search fixed to the paper's source auto-cap.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_two_scale_source_auto_cap_search_of_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_provider_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_source_auto_cap_search_of_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_provider_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming an existential
load/count provider and producing the source-auto-cap search certificate,
selected-pair forward-ratio bound, and source output.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_two_scale_source_auto_cap_search_with_selected_pair_forward_ratio_of_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_provider_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_source_auto_cap_search_with_selected_pair_forward_ratio_of_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_provider_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias for the generated-rounding
two-scale source-min/max load/count provider route, with search fixed to the
paper's source auto-cap.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_two_scale_source_auto_cap_search_of_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_provider_of_generated_rounding_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_source_auto_cap_search_of_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_provider_of_generated_rounding_no_top_of_margin

/--
Theorem 3.3 source/rounded transfer: public alias for the generated-rounding
two-scale source-min/max load/count provider route with separate proof and
search caps.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_two_scale_larger_cap_search_of_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_provider_of_generated_rounding_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_larger_cap_search_of_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_provider_of_generated_rounding_no_top_of_margin

/--
Theorem 3.3 source/rounded transfer: public alias for the source-average
generated-rounding two-scale source-min/max load/count provider route with
separate proof and search caps.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_two_scale_larger_cap_search_of_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_provider_of_source_average_generated_rounding_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_larger_cap_search_of_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_provider_of_source_average_generated_rounding_no_top_of_margin

/--
Theorem 3.3 source/rounded transfer: public alias for the source-average
generated-rounding two-scale source-min/max load/count provider route with the
proof cap fixed to the paper's canonical source auto-cap and the final search
cap allowed to be any larger cap.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_two_scale_larger_cap_search_of_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_provider_canonical_of_source_average_generated_rounding_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_larger_cap_search_of_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_provider_canonical_of_source_average_generated_rounding_no_top_of_margin

/--
Theorem 3.3 source/rounded transfer: public alias for the source-average
generated-rounding two-scale source-min/max load/count provider route with the
canonical proof cap, a larger final search cap, and the selected-pair
forward-ratio bound.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_two_scale_larger_cap_search_with_selected_pair_forward_ratio_of_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_provider_canonical_of_source_average_generated_rounding_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_larger_cap_search_with_selected_pair_forward_ratio_of_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_provider_canonical_of_source_average_generated_rounding_no_top_of_margin

/--
Theorem 3.3 source/rounded transfer: public alias for the generated-rounding
two-scale source-min/max load/count provider route with the proof cap fixed to
the paper's canonical source auto-cap.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_two_scale_source_auto_cap_search_of_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_provider_canonical_of_generated_rounding_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_source_auto_cap_search_of_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_provider_canonical_of_generated_rounding_no_top_of_margin

/--
Theorem 3.3 source/rounded transfer: public alias for the generated-rounding
two-scale source-min/max load/count provider route with the proof cap fixed to
the paper's canonical source auto-cap and source-average hypotheses deriving
the rounded target lower bound.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_two_scale_source_auto_cap_search_of_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_provider_canonical_of_source_average_generated_rounding_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_source_auto_cap_search_of_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_provider_canonical_of_source_average_generated_rounding_no_top_of_margin

/--
Theorem 3.3 source/rounded transfer: public alias for the source-average
generated-rounding source-min/max provider route with the canonical source
auto-cap and the selected-pair forward-ratio bound.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_two_scale_source_auto_cap_search_with_selected_pair_forward_ratio_of_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_provider_canonical_of_source_average_generated_rounding_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_source_auto_cap_search_with_selected_pair_forward_ratio_of_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_provider_canonical_of_source_average_generated_rounding_no_top_of_margin

/--
Theorem 3.3 source/rounded transfer: public alias for the source-average
generated-rounding source-min/max provider route with the comparison IP and
standard explicit full-IP summaries exposed alongside the source output.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_two_scale_source_auto_cap_search_with_full_ip_summaries_of_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_provider_canonical_of_source_average_generated_rounding_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_source_auto_cap_search_with_full_ip_summaries_of_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_provider_canonical_of_source_average_generated_rounding_no_top_of_margin

/--
Theorem 3.3 source/rounded transfer: public alias pairing the canonical
selected-pair source-min/max provider endpoint with the canonical full-IP
summary endpoint.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_two_scale_source_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_provider_canonical_of_source_average_generated_rounding_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_source_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_provider_canonical_of_source_average_generated_rounding_no_top_of_margin

/--
Theorem 3.3 source/rounded transfer: public alias for the source-average
generated-rounding source-min/max provider route with a larger search cap,
exposing the comparison IP and standard explicit full-IP summaries alongside
the source output.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_two_scale_larger_cap_search_with_full_ip_summaries_of_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_provider_canonical_of_source_average_generated_rounding_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_larger_cap_search_with_full_ip_summaries_of_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_provider_canonical_of_source_average_generated_rounding_no_top_of_margin

/--
Theorem 3.3 source/rounded transfer: public alias pairing the larger-cap
selected-pair source-min/max provider endpoint with the larger-cap full-IP
summary endpoint.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_two_scale_larger_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_provider_canonical_of_source_average_generated_rounding_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_larger_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_claim_3_4_source_min_max_windowed_type_assignment_loads_and_counts_provider_canonical_of_source_average_generated_rounding_no_top_of_margin

/--
Theorem 3.3 source/rounded transfer: public alias consuming a Claim 3.4 source
certificate plus source-min/max rounded type witnesses and a matching
combined-supply type assignment.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_claim_3_4_and_source_min_max_type_assignment_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_claim_3_4_and_source_min_max_type_assignment_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a Claim 3.4 source
certificate plus a load-realizing source-min/max rounded type assignment,
selecting the finite min/max type witnesses internally.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_claim_3_4_and_source_min_max_type_assignment_loads_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_claim_3_4_and_source_min_max_type_assignment_loads_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a Claim 3.4 source
certificate and a source-min/max rounded type assignment whose loads match the
source optimum and whose counts match the combined rounded supply.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_claim_3_4_and_source_min_max_type_assignment_loads_and_counts_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_claim_3_4_and_source_min_max_type_assignment_loads_and_counts_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a Claim 3.4 source
certificate and a smaller-cap source-min/max load/count certificate lifted to
the search cap.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_claim_3_4_and_source_min_max_type_assignment_loads_and_counts_larger_cap_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_claim_3_4_and_source_min_max_type_assignment_loads_and_counts_larger_cap_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a Claim 3.4 source
certificate, internally producing the larger-capped search certificate from a
smaller-cap source-min/max load/count type assignment, and deriving source
output.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_larger_cap_search_of_claim_3_4_source_min_max_type_assignment_loads_and_counts_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_larger_cap_search_of_claim_3_4_source_min_max_type_assignment_loads_and_counts_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a Claim 3.4 source
certificate and internally producing search at the paper's source auto-cap
from source-min/max load/count type-assignment data.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_source_auto_cap_search_of_claim_3_4_source_min_max_type_assignment_loads_and_counts_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_source_auto_cap_search_of_claim_3_4_source_min_max_type_assignment_loads_and_counts_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a Claim 3.4 source
certificate and internally producing search and source output from an
existential source-min/max load/count type-assignment provider.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_larger_cap_search_of_claim_3_4_source_min_max_type_assignment_provider_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_larger_cap_search_of_claim_3_4_source_min_max_type_assignment_provider_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a Claim 3.4 source
certificate and internally producing search at the paper's source auto-cap
from an existential source-min/max load/count type-assignment provider.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_source_auto_cap_search_of_claim_3_4_source_min_max_type_assignment_provider_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_source_auto_cap_search_of_claim_3_4_source_min_max_type_assignment_provider_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a Claim 3.4 source
certificate and source-min/max load/count data, then producing search,
selected-pair forward-ratio bound, and source output.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_larger_cap_search_with_selected_pair_forward_ratio_of_claim_3_4_source_min_max_type_assignment_loads_and_counts_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_larger_cap_search_with_selected_pair_forward_ratio_of_claim_3_4_source_min_max_type_assignment_loads_and_counts_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a Claim 3.4 source
certificate and source-min/max load/count data, with search fixed to the
paper's source auto-cap and selected-pair forward-ratio bound returned.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_source_auto_cap_search_with_selected_pair_forward_ratio_of_claim_3_4_source_min_max_type_assignment_loads_and_counts_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_source_auto_cap_search_with_selected_pair_forward_ratio_of_claim_3_4_source_min_max_type_assignment_loads_and_counts_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a Claim 3.4 source
certificate and an existential source-min/max load/count provider, then
producing search, selected-pair forward-ratio bound, and source output.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_larger_cap_search_with_selected_pair_forward_ratio_of_claim_3_4_source_min_max_type_assignment_provider_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_larger_cap_search_with_selected_pair_forward_ratio_of_claim_3_4_source_min_max_type_assignment_provider_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a Claim 3.4 source
certificate and an existential source-min/max load/count provider, with search
fixed to the source auto-cap and selected-pair forward-ratio bound returned.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_source_auto_cap_search_with_selected_pair_forward_ratio_of_claim_3_4_source_min_max_type_assignment_provider_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_source_auto_cap_search_with_selected_pair_forward_ratio_of_claim_3_4_source_min_max_type_assignment_provider_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias for the generated-rounding
source-min/max load/count provider route, with search fixed to the paper's
source auto-cap.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_source_auto_cap_search_of_claim_3_4_source_min_max_type_assignment_provider_of_generated_rounding_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_source_auto_cap_search_of_claim_3_4_source_min_max_type_assignment_provider_of_generated_rounding_no_top_of_margin

/--
Theorem 3.3 source/rounded transfer: public alias consuming a Claim 3.4 source
certificate and an exact typed combined allocation whose rounded loads match
the source optimum.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_claim_3_4_and_exact_typed_combined_high_low_allocation_loads_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_claim_3_4_and_exact_typed_combined_high_low_allocation_loads_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a Claim 3.4 source
certificate and a smaller-cap exact typed combined allocation whose rounded
loads match the source optimum.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_claim_3_4_and_exact_typed_combined_high_low_allocation_loads_larger_cap_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_claim_3_4_and_exact_typed_combined_high_low_allocation_loads_larger_cap_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a Claim 3.4 source
certificate, internally producing the larger-capped search certificate from an
exact typed combined allocation, and deriving source output.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_larger_cap_search_of_claim_3_4_exact_typed_combined_high_low_allocation_loads_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_larger_cap_search_of_claim_3_4_exact_typed_combined_high_low_allocation_loads_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a Claim 3.4 source
certificate and internally producing search at the paper's source auto-cap
from an exact typed combined allocation whose rounded loads match the source
optimum.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_source_auto_cap_search_of_claim_3_4_exact_typed_combined_high_low_allocation_loads_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_source_auto_cap_search_of_claim_3_4_exact_typed_combined_high_low_allocation_loads_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a Claim 3.4 source
certificate and an exact typed combined allocation, then producing search,
selected-pair forward-ratio bound, and source output.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_larger_cap_search_with_selected_pair_forward_ratio_of_claim_3_4_exact_typed_combined_high_low_allocation_loads_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_larger_cap_search_with_selected_pair_forward_ratio_of_claim_3_4_exact_typed_combined_high_low_allocation_loads_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a Claim 3.4 source
certificate and an exact typed combined allocation, with source-auto-cap search
and selected-pair forward-ratio bound returned.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_source_auto_cap_search_with_selected_pair_forward_ratio_of_claim_3_4_exact_typed_combined_high_low_allocation_loads_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_source_auto_cap_search_with_selected_pair_forward_ratio_of_claim_3_4_exact_typed_combined_high_low_allocation_loads_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias for the generated-rounding
exact typed combined allocation provider route, with search fixed to the
paper's source auto-cap.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_source_auto_cap_search_of_claim_3_4_exact_typed_combined_high_low_allocation_loads_provider_of_generated_rounding_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_source_auto_cap_search_of_claim_3_4_exact_typed_combined_high_low_allocation_loads_provider_of_generated_rounding_no_top_of_margin

/--
Theorem 3.3 source/rounded transfer: public alias for the generated-rounding
exact typed combined allocation provider route with canonical source auto-cap
search, exposing the comparison IP and standard explicit full-IP summaries.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_source_auto_cap_search_with_full_ip_summaries_of_claim_3_4_exact_typed_combined_high_low_allocation_loads_provider_of_generated_rounding_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_source_auto_cap_search_with_full_ip_summaries_of_claim_3_4_exact_typed_combined_high_low_allocation_loads_provider_of_generated_rounding_no_top_of_margin

/--
Theorem 3.3 source/rounded transfer: public alias for the generated-rounding
two-scale windowed exact typed combined allocation provider route, with search
fixed to the paper's source auto-cap.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_two_scale_source_auto_cap_search_of_claim_3_4_windowed_exact_typed_combined_high_low_allocation_loads_provider_of_generated_rounding_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_source_auto_cap_search_of_claim_3_4_windowed_exact_typed_combined_high_low_allocation_loads_provider_of_generated_rounding_no_top_of_margin

/--
Theorem 3.3 source/rounded transfer: public alias for the source-average
generated-rounding two-scale exact typed combined allocation provider route,
with the proof cap fixed to the paper's canonical source auto-cap.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_two_scale_source_auto_cap_search_of_claim_3_4_windowed_exact_typed_combined_high_low_allocation_loads_provider_canonical_of_source_average_generated_rounding_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_source_auto_cap_search_of_claim_3_4_windowed_exact_typed_combined_high_low_allocation_loads_provider_canonical_of_source_average_generated_rounding_no_top_of_margin

/--
Theorem 3.3 source/rounded transfer: public alias for the source-average
generated-rounding two-scale exact typed combined allocation provider route
with canonical source auto-cap search and selected-pair forward-ratio payload.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_two_scale_source_auto_cap_search_with_selected_pair_forward_ratio_of_claim_3_4_windowed_exact_typed_combined_high_low_allocation_loads_provider_canonical_of_source_average_generated_rounding_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_source_auto_cap_search_with_selected_pair_forward_ratio_of_claim_3_4_windowed_exact_typed_combined_high_low_allocation_loads_provider_canonical_of_source_average_generated_rounding_no_top_of_margin

/--
Theorem 3.3 source/rounded transfer: public alias for the source-average
generated-rounding two-scale exact typed combined allocation provider route,
with canonical source auto-cap search and explicit full-IP summaries exposed.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_two_scale_source_auto_cap_search_with_full_ip_summaries_of_claim_3_4_windowed_exact_typed_combined_high_low_allocation_loads_provider_canonical_of_source_average_generated_rounding_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_source_auto_cap_search_with_full_ip_summaries_of_claim_3_4_windowed_exact_typed_combined_high_low_allocation_loads_provider_canonical_of_source_average_generated_rounding_no_top_of_margin

/--
Theorem 3.3 source/rounded transfer: public alias pairing the canonical
selected-pair exact typed allocation provider endpoint with the canonical
full-IP summary endpoint.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_two_scale_source_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_claim_3_4_windowed_exact_typed_combined_high_low_allocation_loads_provider_canonical_of_source_average_generated_rounding_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_source_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_claim_3_4_windowed_exact_typed_combined_high_low_allocation_loads_provider_canonical_of_source_average_generated_rounding_no_top_of_margin

/--
Theorem 3.3 source/rounded transfer: public alias for the source-average
generated-rounding two-scale exact typed combined allocation provider route,
with the proof cap fixed to the paper's canonical source auto-cap and the
final search cap allowed to be any larger cap.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_two_scale_larger_cap_search_of_claim_3_4_windowed_exact_typed_combined_high_low_allocation_loads_provider_canonical_of_source_average_generated_rounding_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_larger_cap_search_of_claim_3_4_windowed_exact_typed_combined_high_low_allocation_loads_provider_canonical_of_source_average_generated_rounding_no_top_of_margin

/--
Theorem 3.3 source/rounded transfer: public alias for the source-average
generated-rounding two-scale exact typed combined allocation provider route
with a larger search cap and selected-pair forward-ratio payload.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_two_scale_larger_cap_search_with_selected_pair_forward_ratio_of_claim_3_4_windowed_exact_typed_combined_high_low_allocation_loads_provider_canonical_of_source_average_generated_rounding_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_larger_cap_search_with_selected_pair_forward_ratio_of_claim_3_4_windowed_exact_typed_combined_high_low_allocation_loads_provider_canonical_of_source_average_generated_rounding_no_top_of_margin

/--
Theorem 3.3 source/rounded transfer: public alias for the source-average
generated-rounding two-scale exact typed combined allocation provider route
with a larger search cap, exposing the comparison IP and standard explicit
full-IP summaries alongside the source output.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_two_scale_larger_cap_search_with_full_ip_summaries_of_claim_3_4_windowed_exact_typed_combined_high_low_allocation_loads_provider_canonical_of_source_average_generated_rounding_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_larger_cap_search_with_full_ip_summaries_of_claim_3_4_windowed_exact_typed_combined_high_low_allocation_loads_provider_canonical_of_source_average_generated_rounding_no_top_of_margin

/--
Theorem 3.3 source/rounded transfer: public alias pairing the larger-cap
selected-pair exact typed allocation provider endpoint with the larger-cap
full-IP summary endpoint.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_two_scale_larger_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_claim_3_4_windowed_exact_typed_combined_high_low_allocation_loads_provider_canonical_of_source_average_generated_rounding_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_two_scale_larger_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_claim_3_4_windowed_exact_typed_combined_high_low_allocation_loads_provider_canonical_of_source_average_generated_rounding_no_top_of_margin

/--
Theorem 3.3 source/rounded transfer: public alias consuming a Claim 3.4 source
certificate and an exact bounded typed combined comparison allocation with a
scalar forward ratio bound.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_claim_3_4_and_comparison_allocation_forward_ratio_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_claim_3_4_and_comparison_allocation_forward_ratio_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a Claim 3.4 source
certificate and internally producing search from an exact bounded typed
combined comparison allocation with scalar source-to-rounded optimality.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_search_of_claim_3_4_comparison_allocation_forward_ratio_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_search_of_claim_3_4_comparison_allocation_forward_ratio_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a Claim 3.4 source
certificate and an exact bounded typed combined comparison allocation with
forward additive pair estimates.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_claim_3_4_and_comparison_allocation_forward_additive_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_claim_3_4_and_comparison_allocation_forward_additive_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias consuming a Claim 3.4 source
certificate and internally producing search from an exact bounded typed
combined comparison allocation with additive source-to-rounded estimates.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_search_of_claim_3_4_comparison_allocation_forward_additive_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_search_of_claim_3_4_comparison_allocation_forward_additive_epsilon

/--
Theorem 3.3 source/rounded transfer: public alias realizing a capped search
certificate and consuming a Claim 3.4 certificate for the optimal source
allocation, leaving only the forward comparison premises.
-/
def theorem3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_claim_3_4_and_forward_premises_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_of_capped_search_certificate_with_claim_3_4_and_forward_premises_epsilon

/--
Theorem 3.3 finite-search support: public alias for the explicit
`lambda^2 + 1` bound on the rounded value-index universe.
-/
def theorem3_3_rounded_value_index_card_le :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_rounded_value_index_card_le

/--
Theorem 3.3 finite-search support: public alias for the explicit source
finite-type cardinality bound.
-/
def theorem3_3_rounded_admissible_type_set_card_le_explicit :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_rounded_admissible_type_set_card_le_explicit

/--
Theorem 3.3 finite-search support: public alias for the explicit source
value-pair cardinality bound.
-/
def theorem3_3_rounded_admissible_value_pair_set_card_le_explicit :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_rounded_admissible_value_pair_set_card_le_explicit

/--
Theorem 3.3 finite-search support: public alias for the explicit two-scale
finite-type cardinality bound.
-/
def theorem3_3_rounded_admissible_type_set_with_cap_card_le_explicit :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_rounded_admissible_type_set_with_cap_card_le_explicit

/--
Theorem 3.3 finite-search support: public alias for the explicit two-scale
value-pair cardinality bound.
-/
def theorem3_3_rounded_admissible_value_pair_set_with_cap_card_le_explicit :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_rounded_admissible_value_pair_set_with_cap_card_le_explicit

/--
Theorem 3.3 finite-search support: public alias for the uncapped value-pair
IP certificate's pair bounds, selected type window, and player-count equation.
-/
def theorem3_3_value_pair_ip_certificate_summary :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_value_pair_ip_certificate_summary

/--
Theorem 3.3 finite-search support: public alias for the uncapped value-pair
search-space and chosen-IP size bounds.
-/
def theorem3_3_value_pair_search_certificate_size_bound :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_value_pair_search_certificate_size_bound

/--
Theorem 3.3 finite-search support: public alias for the selected IP payload
inside an uncapped value-pair search certificate.
-/
def theorem3_3_value_pair_search_certificate_chosen_ip_summary :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_value_pair_search_certificate_chosen_ip_summary

/--
Theorem 3.3 finite-search support: public alias comparing an uncapped value
pair search result against an abstract feasible value-pair IP.
-/
def theorem3_3_value_pair_search_ratio_le_of_value_pair_ip :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_value_pair_search_ratio_le_of_value_pair_ip

/--
Theorem 3.3 finite-search support: public alias comparing an uncapped value
pair search result against a concrete feasible IP pair.
-/
def theorem3_3_value_pair_search_ratio_le_of_concrete_ip :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_value_pair_search_ratio_le_of_concrete_ip

/--
Theorem 3.3 finite-search support: public alias constructing an uncapped
value-pair search certificate from an abstract feasible value-pair IP.
-/
def theorem3_3_exists_value_pair_search_certificate_of_value_pair_ip :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_of_value_pair_ip

/--
Theorem 3.3 finite-search support: public alias constructing an uncapped
value-pair search certificate from a concrete feasible IP pair.
-/
def theorem3_3_exists_value_pair_search_certificate_of_concrete_ip :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_of_concrete_ip

/--
Theorem 3.3 value-pair-IP search endpoint: public alias packaging a supplied
abstract feasible value-pair IP with the finite-search certificate and final
rounded-instance guarantee.
-/
def theorem3_3_value_pair_ip_search_certificate_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_ratio_guarantee_of_value_pair_ip

/--
Theorem 3.3 value-pair-IP search summary endpoint: public alias packaging a
supplied abstract feasible value-pair IP with the finite-search certificate,
final guarantee, and selected-search-IP summary.
-/
def theorem3_3_value_pair_ip_search_certificate_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_summary_with_ratio_guarantee_of_value_pair_ip

/--
Theorem 3.3 concrete-IP search endpoint: public alias packaging a supplied
uncapped concrete IP candidate with the finite-search certificate and final
rounded-instance guarantee.
-/
def theorem3_3_concrete_ip_search_certificate_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_ratio_guarantee_of_concrete_ip

/--
Theorem 3.3 concrete-IP search summary endpoint: public alias packaging a
supplied uncapped concrete IP candidate with the finite-search certificate,
final guarantee, and selected-search-IP summary.
-/
def theorem3_3_concrete_ip_search_certificate_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_summary_with_ratio_guarantee_of_concrete_ip

/--
Theorem 3.3 concrete-IP support: public alias for the full uncapped
comparison-IP constraint summary.
-/
def theorem3_3_concrete_ip_certificate_full_summary :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_concrete_ip_certificate_full_summary

/--
Theorem 3.3 capped finite-search support: public alias for the capped
value-pair search-space and chosen-IP equations.
-/
def theorem3_3_value_pair_search_certificate_with_cap_size_bound :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_value_pair_search_certificate_with_cap_size_bound

/--
Theorem 3.3 capped finite-search support: public alias for value-window
cardinality inside the capped type box.
-/
def theorem3_3_rounded_types_in_value_window_with_cap_card_le :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_rounded_types_in_value_window_with_cap_card_le

/--
Theorem 3.3 capped concrete-IP support: public alias for the full comparison-IP
constraint summary.
-/
def theorem3_3_concrete_ip_certificate_with_cap_full_summary :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_concrete_ip_certificate_with_cap_full_summary

/--
Theorem 3.3 capped finite-search support: public alias for the full chosen-IP
constraint summary.
-/
def theorem3_3_value_pair_search_certificate_with_cap_full_summary :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_value_pair_search_certificate_with_cap_full_summary

/--
Theorem 3.3 capped concrete-IP support: public alias for the full comparison-IP
summary after pushing through the linear count bound.
-/
def theorem3_3_concrete_ip_certificate_with_cap_full_summary_of_count_bound :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_concrete_ip_certificate_with_cap_full_summary_of_count_bound

/--
Theorem 3.3 capped finite-search support: public alias for the full chosen-IP
summary after pushing through the linear count bound.
-/
def theorem3_3_value_pair_search_certificate_with_cap_full_summary_of_count_bound :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_value_pair_search_certificate_with_cap_full_summary_of_count_bound

/--
Theorem 3.3 capped finite-search support: public alias packaging the capped
ratio comparison with both explicit full-IP summaries under a count bound.
-/
def theorem3_3_value_pair_search_with_cap_ratio_and_explicit_full_ip_summaries_of_count_bound :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_value_pair_search_with_cap_ratio_and_explicit_full_ip_summaries_of_count_bound

/--
Theorem 3.3 capped finite-search support: public alias comparing a capped
search result against a concrete feasible capped IP pair.
-/
def theorem3_3_value_pair_search_with_cap_ratio_le_of_concrete_ip :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_value_pair_search_with_cap_ratio_le_of_concrete_ip

/--
Theorem 3.3 capped finite-search support: public alias constructing a capped
value-pair search certificate from a concrete feasible capped IP pair.
-/
def theorem3_3_exists_value_pair_search_certificate_with_cap_of_concrete_ip :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_cap_of_concrete_ip

/--
Theorem 3.3 capped concrete-IP search endpoint: public alias packaging a
supplied capped concrete IP candidate with the capped finite-search certificate
and final rounded-instance guarantee.
-/
def theorem3_3_capped_concrete_ip_search_certificate_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_cap_ratio_guarantee_of_concrete_ip

/--
Theorem 3.3 capped concrete-IP search full-summary endpoint: public alias
packaging a supplied capped concrete IP candidate with full comparison-IP and
chosen-IP summaries plus the final rounded-instance guarantee.
-/
def theorem3_3_capped_concrete_ip_search_certificate_full_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_cap_full_summary_ratio_guarantee_of_concrete_ip

/--
Theorem 3.3 capped concrete-IP construction: public alias turning a capped
rounded type assignment into a capped concrete IP certificate.
-/
def theorem3_3_concrete_ip_certificate_with_cap_of_supply_type_assignment :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_concrete_ip_certificate_with_cap_of_supply_type_assignment

/--
Theorem 3.3 capped finite-search support: public alias comparing a capped
search result against a concrete capped type assignment.
-/
def theorem3_3_value_pair_search_with_cap_ratio_le_of_supply_type_assignment :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_value_pair_search_with_cap_ratio_le_of_supply_type_assignment

/--
Theorem 3.3 capped finite-search support: public alias constructing a capped
search certificate from a concrete capped type assignment.
-/
def theorem3_3_exists_value_pair_search_certificate_with_cap_of_supply_type_assignment :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_cap_of_supply_type_assignment

/--
Theorem 3.3 capped supply-type-assignment ratio endpoint: a concrete capped
rounded type assignment yields a capped finite-search certificate together
with the final rounded-instance `(1 + epsilon)` guarantee.
-/
def theorem3_3_capped_supply_type_assignment_search_certificate_ratio_endpoint
    {SourceAgent SourceItem Alloc : Type*}
    [Fintype SourceAgent] [Nonempty SourceAgent]
    {M : Theorem33.IdenticalUtilitiesModel SourceAgent SourceItem Alloc}
    {L LR epsilon : ℝ} {lambda maxCount : ℕ} {optimal : Alloc}
    (hepsilon_pos : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1)
    (cert : Theorem33.RoundedInstanceSearchCertificate M L epsilon lambda optimal)
    {supply : Theorem33.RoundedValueIndex lambda → ℕ}
    {p : ℝ × ℝ}
    (hpair :
      p ∈ Theorem33.roundedAdmissibleValuePairSetWithCap
        L LR lambda maxCount)
    (typeOf : SourceAgent → Theorem33.RoundedBundleType lambda)
    (htypes :
      ∀ i : SourceAgent,
        typeOf i ∈
          Theorem33.roundedTypesInValueWindowWithCap
            L LR lambda maxCount p.1 p.2)
    (hcounts :
      ∀ k : Theorem33.RoundedValueIndex lambda,
        (∑ i : SourceAgent, (typeOf i).count k) = supply k) :=
  LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_cap_ratio_guarantee_of_supply_type_assignment
    hepsilon_pos hepsilon_le_one cert hpair typeOf htypes hcounts

/--
Theorem 3.3 capped supply-type-assignment search full-summary ratio endpoint:
public alias exposing the chosen capped search IP's full summary together with
the final rounded-instance guarantee.
-/
def theorem3_3_capped_supply_type_assignment_search_certificate_full_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_cap_full_summary_ratio_guarantee_of_supply_type_assignment

/--
Theorem 3.3 capped supply-type-assignment concrete-IP/search ratio endpoint:
a concrete capped rounded type assignment yields a capped concrete IP
certificate, a capped finite-search certificate, and the final guarantee.
-/
def theorem3_3_capped_supply_type_assignment_concrete_ip_search_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_concrete_ip_and_search_with_cap_ratio_guarantee_of_supply_type_assignment

/--
Theorem 3.3 capped supply-type-assignment full concrete-IP/search ratio
endpoint: public alias exposing full comparison-IP and chosen-IP summaries
under the linear count bound.
-/
def theorem3_3_capped_supply_type_assignment_concrete_ip_search_full_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_concrete_ip_and_search_with_cap_full_summary_ratio_guarantee_of_supply_type_assignment

/--
Theorem 3.3 concrete-IP construction: public alias turning an uncapped rounded
type assignment into a concrete IP certificate.
-/
def theorem3_3_concrete_ip_certificate_of_type_assignment :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_concrete_ip_certificate_of_type_assignment

/--
Theorem 3.3 concrete-IP construction: public alias for the externally
specified rounded goods-supply form.
-/
def theorem3_3_concrete_ip_certificate_of_supply_type_assignment :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_concrete_ip_certificate_of_supply_type_assignment

/--
Theorem 3.3 finite-search support: public alias comparing an uncapped search
result against a concrete type assignment.
-/
def theorem3_3_value_pair_search_ratio_le_of_supply_type_assignment :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_value_pair_search_ratio_le_of_supply_type_assignment

/--
Theorem 3.3 finite-search support: public alias constructing an uncapped
search certificate from a concrete type assignment.
-/
def theorem3_3_exists_value_pair_search_certificate_of_supply_type_assignment :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_of_supply_type_assignment

/--
Theorem 3.3 supply-type-assignment ratio endpoint: a concrete rounded type
assignment yields an uncapped finite-search certificate together with the
final rounded-instance `(1 + epsilon)` guarantee.
-/
def theorem3_3_supply_type_assignment_search_certificate_ratio_endpoint
    {SourceAgent SourceItem Alloc : Type*}
    [Fintype SourceAgent] [Nonempty SourceAgent]
    {M : Theorem33.IdenticalUtilitiesModel SourceAgent SourceItem Alloc}
    {L epsilon : ℝ} {lambda : ℕ} {optimal : Alloc}
    (hepsilon_pos : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1)
    (cert : Theorem33.RoundedInstanceSearchCertificate M L epsilon lambda optimal)
    {supply : Theorem33.RoundedValueIndex lambda → ℕ}
    {p : ℝ × ℝ}
    (hpair : p ∈ Theorem33.roundedAdmissibleValuePairSet L lambda)
    (typeOf : SourceAgent → Theorem33.RoundedBundleType lambda)
    (htypes :
      ∀ i : SourceAgent,
        typeOf i ∈ Theorem33.roundedTypesInValueWindow L lambda p.1 p.2)
    (hcounts :
      ∀ k : Theorem33.RoundedValueIndex lambda,
        (∑ i : SourceAgent, (typeOf i).count k) = supply k) :=
  LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_ratio_guarantee_of_supply_type_assignment
    hepsilon_pos hepsilon_le_one cert hpair typeOf htypes hcounts

/--
Theorem 3.3 supply-type-assignment search-summary ratio endpoint: public alias
exposing the selected uncapped search IP summary together with the final
rounded-instance guarantee.
-/
def theorem3_3_supply_type_assignment_search_certificate_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_summary_with_ratio_guarantee_of_supply_type_assignment

/--
Theorem 3.3 supply-type-assignment concrete-IP/search ratio endpoint: a
concrete rounded type assignment yields an uncapped concrete IP certificate,
a finite-search certificate, and the final rounded-instance guarantee.
-/
def theorem3_3_supply_type_assignment_concrete_ip_search_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_concrete_ip_and_search_with_ratio_guarantee_of_supply_type_assignment

/--
Theorem 3.3 supply-type-assignment concrete-IP/search full-summary ratio
endpoint: a concrete rounded type assignment yields an uncapped concrete IP,
finite search certificate, final guarantee, and common IP/search summaries.
-/
def theorem3_3_supply_type_assignment_concrete_ip_search_full_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_concrete_ip_and_search_full_summary_ratio_guarantee_of_supply_type_assignment

/--
Theorem 3.3 high-good rounding seam: public alias for choosing a rounded
value index map that upward-rounds high source goods within additive
`L / lambda^2`.
-/
def theorem3_3_exists_high_good_index_of :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_high_good_indexOf

/--
Theorem 3.3 rounded-source construction: public alias for the rounded
identical-utilities model induced by a source-good rounding map.
-/
def theorem3_3_rounded_model_of_index :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_roundedModelOfIndex

/--
Theorem 3.3 rounded-source construction: public alias for the rounded bundle
type induced by a source bundle and rounding map.
-/
def theorem3_3_rounded_bundle_type_of_bundle :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_roundedBundleTypeOfBundle

/--
Theorem 3.3 rounded-source construction: public alias equating the induced
rounded bundle-type load with the direct rounded value sum over the bundle.
-/
def theorem3_3_rounded_bundle_type_of_bundle_load_eq_sum :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_roundedBundleTypeOfBundle_load_eq_sum

/--
Theorem 3.3 rounded-source construction: public alias for the rounded
goods-supply vector induced by a finite source-good set.
-/
def theorem3_3_rounded_goods_supply_of_goods :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_roundedGoodsSupplyOfGoods

/--
Theorem 3.3 rounded-source construction: public alias showing an unused
rounded value index has zero induced goods supply.
-/
def theorem3_3_rounded_goods_supply_of_goods_eq_zero_of_index_ne :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_roundedGoodsSupplyOfGoods_eq_zero_of_index_ne

/--
Theorem 3.3 materialized rounded supply: public alias for the finite item type
created from a rounded goods-supply vector.
-/
abbrev theorem3_3_rounded_supply_item
    {lambda : ℕ} (supply : Theorem33.RoundedValueIndex lambda → ℕ) :=
  LMMS04FairDivision.paper_lmms_theorem_3_3_roundedSupplyItem supply

/--
Theorem 3.3 materialized rounded supply: public alias for recovering the
rounded value index of a materialized supply item.
-/
def theorem3_3_rounded_supply_index_of :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_roundedSupplyIndexOf

/--
Theorem 3.3 materialized rounded supply: public alias for the top rounded
value index `lambda^2`.
-/
def theorem3_3_top_rounded_value_index :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_topRoundedValueIndex

/--
Theorem 3.3 materialized rounded supply: public alias for the natural value of
the top rounded value index.
-/
def theorem3_3_top_rounded_value_index_value :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_topRoundedValueIndex_value

/--
Theorem 3.3 materialized rounded supply: public alias for the rounded value of
a materialized supply item.
-/
def theorem3_3_rounded_supply_value :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_roundedSupplyValue

/--
Theorem 3.3 materialized rounded supply: public alias for positivity of
materialized rounded-supply item values.
-/
def theorem3_3_rounded_supply_value_pos :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_roundedSupplyValue_pos

/--
Theorem 3.3 materialized rounded supply: public alias identifying the rounded
value of the top index with `L`.
-/
def theorem3_3_rounded_value_top_rounded_value_index_eq :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_roundedValue_topRoundedValueIndex_eq

/--
Theorem 3.3 no-top support: public alias proving high-good rounded indices are
not top indices under the source rounding margin.
-/
def theorem3_3_high_index_of_ne_top_of_rounding_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_high_indexOf_ne_top_of_rounding_margin

/--
Theorem 3.3 low-good support: public alias for the natural value of the
artificial low-good rounded index.
-/
def theorem3_3_low_good_rounded_value_index_value :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_lowGoodRoundedValueIndex_value

/--
Theorem 3.3 low-good support: public alias showing the artificial low-good
rounded index is not the top index when `lambda > 1`.
-/
def theorem3_3_low_good_rounded_value_index_ne_top_rounded_value_index :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_lowGoodRoundedValueIndex_ne_topRoundedValueIndex

/--
Theorem 3.3 low-good support: public alias showing low-good aggregation
contributes no top-index goods when `lambda > 1`.
-/
def theorem3_3_low_goods_aggregated_supply_top_eq_zero :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_lowGoodsAggregatedSupply_top_eq_zero

/--
Theorem 3.3 rounded-value bounds: public alias bounding every rounded value by
the average-load scale `L`.
-/
def theorem3_3_rounded_value_le_L :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_roundedValue_le_L

/--
Theorem 3.3 rounded-value bounds: public alias bounding every materialized
rounded-supply item value by `L`.
-/
def theorem3_3_rounded_supply_value_le_L :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_roundedSupplyValue_le_L

/--
Theorem 3.3 rounded-value bounds: public alias showing below-top rounded
indices have value strictly below `L`.
-/
def theorem3_3_rounded_value_lt_L_of_index_lt_top :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_roundedValue_lt_L_of_index_lt_top

/--
Theorem 3.3 rounded-value bounds: public alias showing materialized supply
items below the top index have value strictly below `L`.
-/
def theorem3_3_rounded_supply_value_lt_L_of_index_lt_top :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_roundedSupplyValue_lt_L_of_index_lt_top

/--
Theorem 3.3 no-top materialization: public alias showing top-free rounded
supply materializes only below-top indices.
-/
def theorem3_3_rounded_supply_index_lt_top_of_top_supply_eq_zero :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_roundedSupplyIndex_lt_top_of_top_supply_eq_zero

/--
Theorem 3.3 no-top materialization: public alias showing top-free rounded
supply materializes only values strictly below `L`.
-/
def theorem3_3_rounded_supply_value_lt_L_of_top_supply_eq_zero :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_roundedSupplyValue_lt_L_of_top_supply_eq_zero

/--
Theorem 3.3 materialized rounded supply: public alias showing materialization
recovers the original rounded goods-supply vector.
-/
def theorem3_3_rounded_goods_supply_of_supply_eq :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_roundedGoodsSupplyOfSupply_eq

/--
Theorem 3.3 rounded-source construction: public alias for preservation of the
weighted rounded value of source goods.
-/
def theorem3_3_rounded_goods_supply_of_goods_weighted_sum_eq_sum_goods :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_roundedGoodsSupplyOfGoods_weighted_sum_eq_sum_goods

/--
Theorem 3.3 high-good transfer support: public alias bounding the rounded load
of a high-good bundle by the source load scaled by `(lambda + 1) / lambda`.
-/
def theorem3_3_high_bundle_rounded_load_le_scaled_source_load :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_high_bundle_rounded_load_le_scaled_source_load

/--
Theorem 3.3 high/low transfer support: public alias combining the high-good
rounded-load bound with a supplied low artificial-load estimate.
-/
def theorem3_3_high_low_bundle_rounded_load_le_forward_transfer :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_high_low_bundle_rounded_load_le_forward_transfer

/--
Theorem 3.3 high/low transfer support: public alias packaging the forward
upper bundle transfer into agentwise inequalities.
-/
def theorem3_3_forward_agentwise_transfer_of_high_low_bundle_estimates :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_forward_agentwise_transfer_of_high_low_bundle_estimates

/--
Theorem 3.3 high-good transfer support: public alias bounding high source load
by high rounded load.
-/
def theorem3_3_high_bundle_source_load_le_rounded_load :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_high_bundle_source_load_le_rounded_load

/--
Theorem 3.3 high-good transfer support: public alias lower-bounding high
source load by `lambda / (lambda + 1)` times high rounded load.
-/
def theorem3_3_high_bundle_source_load_ge_scaled_rounded_load :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_high_bundle_source_load_ge_scaled_rounded_load

/--
Theorem 3.3 high/low transfer support: public alias for the backward maximum
transfer from a supplied low-load upper estimate.
-/
def theorem3_3_high_low_bundle_source_load_le_backward_transfer :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_high_low_bundle_source_load_le_backward_transfer

/--
Theorem 3.3 high/low transfer support: public alias for the backward minimum
transfer from a supplied low-load lower estimate.
-/
def theorem3_3_high_low_bundle_source_load_ge_backward_transfer :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_high_low_bundle_source_load_ge_backward_transfer

/--
Theorem 3.3 high/low transfer support: public alias packaging the backward
upper/lower bundle transfers into agentwise inequalities.
-/
def theorem3_3_backward_agentwise_transfer_of_high_low_bundle_estimates :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_backward_agentwise_transfer_of_high_low_bundle_estimates

/--
Theorem 3.3 high/low transfer support: public alias returning the four
epsilon-specialized additive transfer premises from a supplied exact low-good
partition.
-/
def theorem3_3_low_partition_agentwise_additive_transfer_premises_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_low_partition_agentwise_additive_transfer_premises_epsilon

/--
Theorem 3.3 high/low allocation support: public alias unioning exact high and
low allocations over disjoint goods.
-/
def theorem3_3_isAllocationOf_union_of_disjoint_allocations :=
  @LMMS04FairDivision.paper_lmms_isAllocationOf_union_of_disjoint_allocations

/--
Theorem 3.3 high/low allocation support: public alias for the value-sum
identity over disjoint high/low bundle unions.
-/
def theorem3_3_finset_sum_union_of_subsets_of_disjoint :=
  @LMMS04FairDivision.paper_lmms_finset_sum_union_of_subsets_of_disjoint

/--
Theorem 3.3 high/low allocation support: public alias for the common-load
identity over disjoint bundle unions.
-/
def theorem3_3_commonLoad_union_eq_add_of_disjoint :=
  @LMMS04FairDivision.paper_lmms_commonLoad_union_eq_add_of_disjoint

/--
Theorem 3.3 high/low allocation support: public alias assembling exact high
and low allocations into one exact combined source allocation.
-/
def theorem3_3_exists_combined_allocation_of_disjoint_exact_allocations :=
  @LMMS04FairDivision.paper_lmms_exists_combined_allocation_of_disjoint_exact_allocations

/--
Theorem 3.3 high/low allocation support: public alias for exact output
assembly with common-load decomposition.
-/
def theorem3_3_exact_high_low_output_assembly :=
  @LMMS04FairDivision.paper_lmms_exact_high_low_output_assembly

/--
Theorem 3.3 low-good partition support: public alias building an exact
low-good allocation from an owner map satisfying per-agent low-load estimates.
-/
def theorem3_3_exists_low_goods_partition_of_owner_load_estimates :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_low_goods_partition_of_owner_load_estimates

/--
Theorem 3.3 low-good partition support: public alias building an exact
low-good allocation directly from ordered finite prefix targets.
-/
def theorem3_3_exists_low_goods_partition_of_finite_prefix_targets :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_low_goods_partition_of_finite_prefix_targets

/--
Theorem 3.3 low-good partition support: public alias for the finite-prefix
target low partition with the low-good total stated as a finset sum.
-/
def theorem3_3_exists_low_goods_partition_of_finite_prefix_targets_of_total_sum :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_low_goods_partition_of_finite_prefix_targets_of_total_sum

/--
Theorem 3.3 low-good partition and transfer support: public alias building the
low-good allocation from owner estimates and packaging the backward transfer
inequalities.
-/
def theorem3_3_exists_low_partition_and_backward_agentwise_transfer_of_owner_estimates :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_low_partition_and_backward_agentwise_transfer_of_owner_estimates

/--
Theorem 3.3 low-good partition and transfer support: public alias building the
low-good allocation from owner estimates and packaging the forward transfer
inequality.
-/
def theorem3_3_exists_low_partition_and_forward_agentwise_transfer_of_owner_estimates :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_low_partition_and_forward_agentwise_transfer_of_owner_estimates

/--
Theorem 3.3 low-good partition and transfer support: public alias building one
low-good allocation from owner estimates and packaging both forward and
backward transfer inequalities.
-/
def theorem3_3_exists_low_partition_and_agentwise_transfer_of_owner_estimates :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_low_partition_and_agentwise_transfer_of_owner_estimates

/--
Theorem 3.3 low-good partition and transfer support: public alias for the
two-way owner-estimate transfer package specialized to `lambda = 56 / epsilon`.
-/
def theorem3_3_exists_low_partition_and_agentwise_transfer_of_owner_estimates_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_low_partition_and_agentwise_transfer_of_owner_estimates_epsilon

/--
Theorem 3.3 low-good partition and transfer support: public alias for the
epsilon-specialized owner-estimate bridge returning the four additive transfer
premises consumed by the final load-transfer endpoint.
-/
def theorem3_3_exists_low_partition_and_agentwise_additive_transfer_premises_of_owner_estimates_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_low_partition_and_agentwise_additive_transfer_premises_of_owner_estimates_epsilon

/--
Theorem 3.3 low-good weighted-prefix support: public alias for the ordered
prefix weight used by the low-good partition construction.
-/
def theorem3_3_prefixWeight :=
  @LMMS04FairDivision.paper_lmms_prefixWeight

/--
Theorem 3.3 low-good weighted-prefix support: public alias identifying the full
prefix weight of a finset list with its finset sum.
-/
def theorem3_3_prefixWeight_toList_length_eq_sum :=
  @LMMS04FairDivision.paper_lmms_prefixWeight_toList_length_eq_sum

/--
Theorem 3.3 low-good weighted-prefix support: public alias for the
cardinality-indexed full-prefix finset sum identity.
-/
def theorem3_3_prefixWeight_toList_card_eq_sum :=
  @LMMS04FairDivision.paper_lmms_prefixWeight_toList_card_eq_sum

/--
Theorem 3.3 low-good weighted-prefix support: public alias for the maximal
prefix below a target and within one item-size from below.
-/
def theorem3_3_exists_prefixWeight_floor :=
  @LMMS04FairDivision.paper_lmms_exists_prefixWeight_floor

/--
Theorem 3.3 low-good weighted-prefix support: public alias for monotonicity of
maximal prefix cuts as targets increase.
-/
def theorem3_3_prefixWeight_floor_index_le_of_target_le :=
  @LMMS04FairDivision.paper_lmms_prefixWeight_floor_index_le_of_target_le

/--
Theorem 3.3 low-good weighted-prefix support: public alias for the prefix-floor
error interval.
-/
def theorem3_3_prefixWeight_floor_error_bounds :=
  @LMMS04FairDivision.paper_lmms_prefixWeight_floor_error_bounds

/--
Theorem 3.3 low-good weighted-prefix support: public alias producing monotone
prefix cuts for cumulative low-good targets.
-/
def theorem3_3_exists_monotone_prefixWeight_cuts :=
  @LMMS04FairDivision.paper_lmms_exists_monotone_prefixWeight_cuts

/--
Theorem 3.3 low-good weighted-prefix support: public alias for the weight of a
consecutive prefix-cut interval.
-/
def theorem3_3_prefixSliceWeight :=
  @LMMS04FairDivision.paper_lmms_prefixSliceWeight

/--
Theorem 3.3 low-good weighted-prefix support: public alias for the concrete
list slice between consecutive prefix cuts.
-/
def theorem3_3_prefixSliceList :=
  @LMMS04FairDivision.paper_lmms_prefixSliceList

/--
Theorem 3.3 low-good weighted-prefix support: public alias identifying a
concrete slice list's sum with the prefix-difference slice weight.
-/
def theorem3_3_prefixSliceWeight_eq_sum_prefixSliceList :=
  @LMMS04FairDivision.paper_lmms_prefixSliceWeight_eq_sum_prefixSliceList

/--
Theorem 3.3 low-good weighted-prefix support: public alias identifying a
drop/take slice's finset with the original-list index interval.
-/
def theorem3_3_list_drop_take_toFinset_eq_filter_idxOf :=
  @LMMS04FairDivision.paper_lmms_list_drop_take_toFinset_eq_filter_idxOf

/--
Theorem 3.3 low-good weighted-prefix support: public alias identifying a
prefix-slice list's finset with its original-list index interval.
-/
def theorem3_3_prefixSliceList_toFinset_eq_filter_idxOf :=
  @LMMS04FairDivision.paper_lmms_prefixSliceList_toFinset_eq_filter_idxOf

/--
Theorem 3.3 low-good weighted-prefix support: public alias locating each valid
list index in a consecutive cut interval.
-/
def theorem3_3_exists_cut_interval_of_final :=
  @LMMS04FairDivision.paper_lmms_exists_cut_interval_of_final

/--
Theorem 3.3 low-good weighted-prefix support: public alias constructing an
owner map whose filters are exactly the ordered prefix-slice finsets.
-/
def theorem3_3_exists_owner_filter_eq_prefixSliceList_toFinset_of_monotone_cuts :=
  @LMMS04FairDivision.paper_lmms_exists_owner_filter_eq_prefixSliceList_toFinset_of_monotone_cuts

/--
Theorem 3.3 low-good weighted-prefix support: public alias constructing an
owner map whose filtered loads match the ordered prefix-slice sums.
-/
def theorem3_3_exists_owner_slice_sum_eq_of_monotone_cuts :=
  @LMMS04FairDivision.paper_lmms_exists_owner_slice_sum_eq_of_monotone_cuts

/--
Theorem 3.3 low-good weighted-prefix support: public alias for consecutive
cumulative target increments.
-/
def theorem3_3_targetIncrement :=
  @LMMS04FairDivision.paper_lmms_targetIncrement

/--
Theorem 3.3 low-good weighted-prefix support: public alias for cumulative target
loads in the canonical `Fin N` agent order.
-/
def theorem3_3_finPrefixTarget :=
  @LMMS04FairDivision.paper_lmms_finPrefixTarget

/--
Theorem 3.3 low-good weighted-prefix support: public alias for the empty
finite-agent cumulative target.
-/
def theorem3_3_finPrefixTarget_zero :=
  @LMMS04FairDivision.paper_lmms_finPrefixTarget_zero

/--
Theorem 3.3 low-good weighted-prefix support: public alias identifying the full
finite-agent prefix with the total target load.
-/
def theorem3_3_finPrefixTarget_total :=
  @LMMS04FairDivision.paper_lmms_finPrefixTarget_total

/--
Theorem 3.3 low-good weighted-prefix support: public alias for nonnegativity of
finite-agent cumulative targets.
-/
def theorem3_3_finPrefixTarget_nonneg :=
  @LMMS04FairDivision.paper_lmms_finPrefixTarget_nonneg

/--
Theorem 3.3 low-good weighted-prefix support: public alias for monotonicity of
finite-agent cumulative targets.
-/
def theorem3_3_finPrefixTarget_mono :=
  @LMMS04FairDivision.paper_lmms_finPrefixTarget_mono

/--
Theorem 3.3 low-good weighted-prefix support: public alias identifying finite
cumulative target increments with the next agent target.
-/
def theorem3_3_targetIncrement_finPrefixTarget :=
  @LMMS04FairDivision.paper_lmms_targetIncrement_finPrefixTarget

/--
Theorem 3.3 low-good weighted-prefix support: public alias producing concrete
prefix-slice estimates for finite-agent targets.
-/
def theorem3_3_exists_prefixSliceList_estimates_for_fin_targets :=
  @LMMS04FairDivision.paper_lmms_exists_prefixSliceList_estimates_for_fin_targets

/--
Theorem 3.3 low-good weighted-prefix support: public alias producing concrete
prefix-slice estimates for arbitrary finite-agent targets using the canonical
`Fintype.equivFin` order.
-/
def theorem3_3_exists_prefixSliceList_estimates_for_finite_targets :=
  @LMMS04FairDivision.paper_lmms_exists_prefixSliceList_estimates_for_finite_targets

/--
Theorem 3.3 low-good weighted-prefix support: public alias turning consecutive
cumulative prefix errors into one-unit slice estimates.
-/
def theorem3_3_prefixSliceWeight_estimates_of_cumulative_bounds :=
  @LMMS04FairDivision.paper_lmms_prefixSliceWeight_estimates_of_cumulative_bounds

/--
Theorem 3.3 low-good weighted-prefix support: public alias deriving per-slice
estimates from monotone prefix cuts.
-/
def theorem3_3_prefixSliceWeight_estimates_of_monotone_cuts :=
  @LMMS04FairDivision.paper_lmms_prefixSliceWeight_estimates_of_monotone_cuts

/--
Theorem 3.3 low-good weighted-prefix support: public alias deriving concrete
list-slice estimates from monotone prefix cuts.
-/
def theorem3_3_prefixSliceList_sum_estimates_of_monotone_cuts :=
  @LMMS04FairDivision.paper_lmms_prefixSliceList_sum_estimates_of_monotone_cuts

/--
Theorem 3.3 low-good weighted-prefix support: public alias converting concrete
prefix-slice estimates into owner-filter load estimates.
-/
def theorem3_3_low_goods_owner_load_estimates_of_prefix_sliceList_estimates :=
  @LMMS04FairDivision.paper_lmms_low_goods_owner_load_estimates_of_prefix_sliceList_estimates

/--
Theorem 3.3 low-good weighted-prefix support: public alias constructing an
owner map with target load estimates from ordered finite prefix targets.
-/
def theorem3_3_exists_low_goods_owner_load_estimates_of_finite_prefix_targets :=
  @LMMS04FairDivision.paper_lmms_exists_low_goods_owner_load_estimates_of_finite_prefix_targets

/--
Theorem 3.3 low-good weighted-prefix support: public alias for finite prefix
target owner estimates with the low-good total stated as a finset sum.
-/
def theorem3_3_exists_low_goods_owner_load_estimates_of_finite_prefix_targets_of_total_sum :=
  @LMMS04FairDivision.paper_lmms_exists_low_goods_owner_load_estimates_of_finite_prefix_targets_of_total_sum

/--
Theorem 3.3 low-good weighted-prefix support: public alias deriving finite
prefix total bounds from the aggregated low artificial-supply total.
-/
def theorem3_3_low_goods_aggregated_supply_total_bounds :=
  @LMMS04FairDivision.paper_lmms_low_goods_aggregated_supply_total_bounds

/--
Theorem 3.3 low-good weighted-prefix support: public alias constructing owner
estimates from the actual aggregated low artificial-supply total.
-/
def theorem3_3_exists_low_goods_owner_load_estimates_of_aggregated_lowRoundedLoad :=
  @LMMS04FairDivision.paper_lmms_exists_low_goods_owner_load_estimates_of_aggregated_lowRoundedLoad

/--
Theorem 3.3 low-good weighted-prefix support: public alias constructing owner
estimates from an exact allocation of the materialized aggregated low supply.
-/
def theorem3_3_exists_low_goods_owner_load_estimates_of_exact_aggregated_low_supply_allocation :=
  @LMMS04FairDivision.paper_lmms_exists_low_goods_owner_load_estimates_of_exact_aggregated_low_supply_allocation

/--
Theorem 3.3 source-output support: public alias assembling the combined source
output allocation and four additive transfer premises from a supplied exact
low partition.
-/
def theorem3_3_source_output_allocation_agentwise_additive_transfer_premises_of_exact_low_partition_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_output_allocation_agentwise_additive_transfer_premises_of_exact_low_partition_epsilon

/--
Theorem 3.3 source-output support: public alias assembling the combined source
output allocation and four additive transfer premises from low owner-map
estimates.
-/
def theorem3_3_exists_source_output_allocation_and_agentwise_additive_transfer_premises_of_owner_estimates_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_allocation_and_agentwise_additive_transfer_premises_of_owner_estimates_epsilon

/--
Theorem 3.3 rounded-source construction: public alias relating exact
allocation bundle-type loads to the weighted induced goods-supply vector.
-/
def theorem3_3_exact_allocation_sum_rounded_bundle_type_loads_eq_goods_supply_weighted_sum :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_isAllocationOf_sum_roundedBundleType_loads_eq_goodsSupply_weighted_sum

/--
Theorem 3.3 materialized rounded supply: public alias for the weighted-supply
sum identity of materialized items.
-/
def theorem3_3_rounded_supply_value_sum_eq_weighted_supply :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_roundedSupplyValue_sum_eq_weighted_supply

/--
Theorem 3.3 materialized rounded supply: public alias saying an exact
allocation's total rounded load equals the weighted supply value.
-/
def theorem3_3_rounded_supply_allocation_total_load_eq_weighted_supply :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_roundedSupplyAllocation_total_load_eq_weighted_supply

/--
Theorem 3.3 low-good aggregation seam: public alias specializing the exact
rounded allocation total identity to the aggregated low artificial supply.
-/
def theorem3_3_low_goods_aggregated_supply_allocation_total_load_eq_weighted_supply :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_lowGoodsAggregatedSupplyAllocation_total_load_eq_weighted_supply

/--
Theorem 3.3 combined high/low seam: public alias for the provenance-carrying
materialized item type with high source goods and low artificial goods.
-/
noncomputable abbrev theorem3_3_typed_combined_high_low_supply_item
    {SourceItem : Type*} {L : ℝ} {lambda : ℕ}
    (highGoods lowGoods : Finset SourceItem) (sourceValue : SourceItem → ℝ) :=
  LMMS04FairDivision.paper_lmms_theorem_3_3_typedCombinedHighLowSupplyItem
    (L := L) (lambda := lambda) highGoods lowGoods sourceValue

/--
Theorem 3.3 combined high/low seam: public alias for the rounded index of a
provenance-carrying combined high/low item.
-/
def theorem3_3_typed_combined_high_low_supply_index_of :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_typedCombinedHighLowSupplyIndexOf

/--
Theorem 3.3 combined high/low seam: public alias for the rounded value of a
provenance-carrying combined high/low item.
-/
def theorem3_3_typed_combined_high_low_supply_value :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_typedCombinedHighLowSupplyValue

/--
Theorem 3.3 combined high/low seam: public alias showing the typed
materialization has exactly the high-source plus low-artificial supply vector.
-/
def theorem3_3_typed_combined_high_low_supply_goods_supply_eq :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_typedCombinedHighLowSupply_goodsSupply_eq

/--
Theorem 3.3 combined high/low seam: public alias splitting the typed
materialization's total value into high rounded value plus low artificial value.
-/
def theorem3_3_typed_combined_high_low_supply_value_sum_eq_high_low_weighted_sum :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_typedCombinedHighLowSupply_value_sum_eq_high_low_weighted_sum

/--
Theorem 3.3 combined high/low seam: public alias for the typed materialization's
source-value lower bound and rounded-error upper bound.
-/
def theorem3_3_typed_combined_high_low_supply_value_bounds :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_typedCombinedHighLowSupply_value_bounds

/--
Theorem 3.3 combined high/low seam: public alias projecting a typed combined
allocation to its source high-good part.
-/
def theorem3_3_typed_combined_high_part :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_typedCombinedHighPart

/--
Theorem 3.3 combined high/low seam: public alias proving the projected high
part is an exact allocation of the original high goods.
-/
def theorem3_3_typed_combined_high_part_is_allocation_of :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_typedCombinedHighPart_isAllocationOf

/--
Theorem 3.3 combined high/low seam: public alias extracting per-agent low
rounded loads from the artificial-low side of a typed combined allocation.
-/
def theorem3_3_typed_combined_low_rounded_load :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_typedCombinedLowRoundedLoad

/--
Theorem 3.3 combined high/low seam: public alias proving extracted low rounded
loads are nonnegative.
-/
def theorem3_3_typed_combined_low_rounded_load_nonneg :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_typedCombinedLowRoundedLoad_nonneg

/--
Theorem 3.3 combined high/low seam: public alias proving the extracted low
rounded loads sum to the aggregated low artificial supply value.
-/
def theorem3_3_typed_combined_low_rounded_load_total_eq_weighted_supply :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_typedCombinedLowRoundedLoad_total_eq_weighted_supply

/--
Theorem 3.3 combined high/low seam: public alias equating the projected high
part's rounded source sum with the high side of the typed combined bundle.
-/
def theorem3_3_typed_combined_high_part_sum_eq_high_side_sum :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_typedCombinedHighPart_sum_eq_highSide_sum

/--
Theorem 3.3 combined high/low seam: public alias decomposing typed combined
rounded load into projected high load plus extracted low rounded load.
-/
def theorem3_3_typed_combined_common_load_eq_high_part_add_low_rounded_load :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_typedCombined_commonLoad_eq_highPart_add_lowRoundedLoad

/--
Theorem 3.3 combined high/low seam: public alias packaging a bounded exact
typed combined allocation as a concrete IP certificate for the explicit
high-plus-low supply vector.
-/
def theorem3_3_concrete_ip_certificate_of_exact_bounded_typed_combined_high_low_allocation :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_concrete_ip_certificate_of_exact_bounded_typed_combined_high_low_allocation

/--
Theorem 3.3 combined high/low seam: public alias packaging a bounded exact
typed combined allocation as a capped concrete IP certificate around the
actual average scale.
-/
def theorem3_3_concrete_ip_certificate_with_cap_of_exact_bounded_typed_combined_high_low_allocation :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_concrete_ip_certificate_with_cap_of_exact_bounded_typed_combined_high_low_allocation

/--
Theorem 3.3 combined high/low seam: public alias extracting per-agent rounded
bundle types from a bounded exact typed combined allocation, with coordinate
totals equal to the explicit high-plus-low supply vector.
-/
def theorem3_3_exists_typed_combined_high_low_type_assignment_of_exact_bounded_allocation :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_typed_combined_high_low_type_assignment_of_exact_bounded_allocation

/--
Theorem 3.3 combined high/low seam: public alias constructing a value-pair
search certificate from a bounded exact typed combined allocation.
-/
def theorem3_3_exists_value_pair_search_certificate_of_exact_bounded_typed_combined_high_low_allocation :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_of_exact_bounded_typed_combined_high_low_allocation

/--
Theorem 3.3 combined high/low seam: public alias adding the final
rounded-instance `(1 + epsilon)` guarantee to the finite-search certificate
induced by a bounded exact typed combined allocation.
-/
def theorem3_3_exact_bounded_typed_combined_high_low_allocation_search_certificate_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_ratio_guarantee_of_exact_bounded_typed_combined_high_low_allocation

/--
Theorem 3.3 combined high/low seam: public alias exposing selected-pair
admissibility for the typed combined finite-search certificate with the final
rounded-instance guarantee.
-/
def theorem3_3_exact_bounded_typed_combined_high_low_allocation_search_certificate_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_summary_with_ratio_guarantee_of_exact_bounded_typed_combined_high_low_allocation

/--
Theorem 3.3 combined high/low seam: public alias packaging a bounded exact
typed combined allocation as a concrete IP certificate plus finite search
witness with the final rounded-instance guarantee.
-/
def theorem3_3_exact_bounded_typed_combined_high_low_allocation_concrete_ip_search_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_concrete_ip_and_search_with_ratio_guarantee_of_exact_bounded_typed_combined_high_low_allocation

/--
Theorem 3.3 combined high/low seam: public alias exposing the full concrete-IP
constraint summary and chosen search-IP summary for a bounded exact typed
combined allocation with the final rounded-instance guarantee.
-/
def theorem3_3_exact_bounded_typed_combined_high_low_allocation_concrete_ip_search_full_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_concrete_ip_and_search_full_summary_ratio_guarantee_of_exact_bounded_typed_combined_high_low_allocation

/--
Theorem 3.3 materialized rounded supply: public alias for the load ratio of an
allocation over a materialized rounded supply.
-/
def theorem3_3_rounded_supply_allocation_ratio :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_roundedSupplyAllocationRatio

/--
Theorem 3.3 low-good aggregation seam: public alias for constructing the
artificial rounded supply of low goods with the paper's value bounds.
-/
def theorem3_3_exists_low_goods_artificial_supply :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_low_goods_artificial_supply

/--
Theorem 3.3 combined high/low seam: public alias for constructing the combined
rounded goods-supply vector and its source-value error bounds.
-/
def theorem3_3_exists_combined_high_low_rounded_goods_supply :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_rounded_goods_supply

/--
Theorem 3.3 combined high/low arithmetic: public alias for the reusable
weighted-value bounds of the rounded high/low supply equations.
-/
def theorem3_3_combined_high_low_rounded_goods_supply_weighted_value_bounds :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_combined_high_low_rounded_goods_supply_weighted_value_bounds

/--
Theorem 3.3 combined high/low no-top seam: public alias showing the combined
supply has no top-index goods from no-top high support.
-/
def theorem3_3_combined_high_low_supply_top_eq_zero :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_combined_high_low_supply_top_eq_zero

/--
Theorem 3.3 combined high/low no-top seam: public alias for constructing a
combined rounded supply with no top-index support under the source margin.
-/
def theorem3_3_exists_combined_high_low_rounded_goods_supply_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_rounded_goods_supply_no_top_of_margin

/--
Theorem 3.3 materialized combined-supply seam: public alias showing the
materialized combined rounded supply inherits the source-value error bounds.
-/
def theorem3_3_exists_combined_high_low_materialized_supply_value_bounds :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_materialized_supply_value_bounds

/--
Theorem 3.3 combined high/low type-assignment search endpoint: public alias
for constructing the finite-search certificate from a solver-provided
type-assignment witness before adjoining the final rounded-instance guarantee.
-/
def theorem3_3_combined_high_low_type_assignment_search_certificate_exists :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_of_combined_high_low_type_assignment

/--
Theorem 3.3 combined high/low type-assignment search ratio endpoint: a solver
that supplies a feasible type assignment for the constructed combined rounded
supply yields a finite-search certificate together with the final
rounded-instance `(1 + epsilon)` guarantee.
-/
def theorem3_3_combined_high_low_type_assignment_search_certificate_ratio_endpoint
    {SourceAgent SourceItem Alloc : Type*}
    [Fintype SourceAgent] [Nonempty SourceAgent] [DecidableEq SourceItem]
    {M : Theorem33.IdenticalUtilitiesModel SourceAgent SourceItem Alloc}
    {L epsilon : ℝ} {lambda : ℕ} {optimal : Alloc}
    (hepsilon_pos : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1)
    (cert : Theorem33.RoundedInstanceSearchCertificate M L epsilon lambda optimal)
    (highGoods lowGoods : Finset SourceItem) (v : SourceItem → ℝ)
    (hlambda : 0 < lambda) (hL : 0 < L)
    (hhigh :
      ∀ g : SourceItem, g ∈ highGoods →
        L / (lambda : ℝ) < v g ∧ v g < L)
    (hlow :
      ∀ g : SourceItem, g ∈ lowGoods →
        0 ≤ v g ∧ v g < L / (lambda : ℝ))
    (solver :
      ∀ (indexOf : SourceItem → Theorem33.RoundedValueIndex lambda)
        (combinedSupply : Theorem33.RoundedValueIndex lambda → ℕ),
        (∀ g : SourceItem, g ∈ highGoods →
          v g ≤ Theorem33.roundedValue L lambda (indexOf g) ∧
            Theorem33.roundedValue L lambda (indexOf g) <
              v g + L / ((lambda : ℝ) ^ 2)) →
        (∀ k : Theorem33.RoundedValueIndex lambda,
          combinedSupply k =
            paper_lmms_theorem_3_3_roundedGoodsSupplyOfGoods indexOf highGoods k +
              Theorem33.lowGoodsAggregatedSupply L lambda (lowGoods.sum v) k) →
        ∃ p : ℝ × ℝ,
          p ∈ Theorem33.roundedAdmissibleValuePairSet L lambda ∧
            ∃ typeOf : SourceAgent → Theorem33.RoundedBundleType lambda,
              (∀ i : SourceAgent,
                typeOf i ∈
                  Theorem33.roundedTypesInValueWindow L lambda p.1 p.2) ∧
                ∀ k : Theorem33.RoundedValueIndex lambda,
                  (∑ i : SourceAgent, (typeOf i).count k) =
                    combinedSupply k) :=
  LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_ratio_guarantee_of_combined_high_low_type_assignment
    hepsilon_pos hepsilon_le_one cert highGoods lowGoods v hlambda hL hhigh
    hlow solver

/--
Theorem 3.3 combined high/low type-assignment search-summary ratio endpoint:
public alias exposing the generated rounded supply and selected uncapped
search IP summary with the final rounded-instance guarantee.
-/
def theorem3_3_combined_high_low_type_assignment_search_certificate_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_summary_with_ratio_guarantee_of_combined_high_low_type_assignment

/--
Theorem 3.3 combined high/low type-assignment concrete-IP/search endpoint:
public alias packaging the solver-provided witness as a concrete IP
certificate before adjoining the final rounded-instance guarantee.
-/
def theorem3_3_combined_high_low_type_assignment_concrete_ip_search_certificate_exists :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_concrete_ip_and_search_of_combined_high_low_type_assignment

/--
Theorem 3.3 combined high/low type-assignment concrete-IP/search ratio
endpoint: a solver for the constructed combined rounded supply yields the
concrete IP certificate, finite-search certificate, and final guarantee.
-/
def theorem3_3_combined_high_low_type_assignment_concrete_ip_search_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_concrete_ip_and_search_with_ratio_guarantee_of_combined_high_low_type_assignment

/--
Theorem 3.3 combined high/low type-assignment concrete-IP/search full-summary
ratio endpoint: public alias keeping the generated rounding map, combined
supply facts, final guarantee, and common uncapped IP/search summaries.
-/
def theorem3_3_combined_high_low_type_assignment_concrete_ip_search_full_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_concrete_ip_and_search_full_summary_with_ratio_guarantee_of_combined_high_low_type_assignment

/--
Theorem 3.3 capped combined high/low IP-solver search endpoint: public alias
for the no-top capped solver payload before adjoining the final rounded
instance guarantee.
-/
def theorem3_3_combined_high_low_capped_ip_solver_concrete_ip_search_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_value_pair_search_certificate_with_cap_of_ip_solver_no_top_of_margin

/--
Theorem 3.3 capped combined high/low IP-solver concrete-IP/search ratio
endpoint: public alias pairing the no-top capped solver IP/search payload with
the final rounded-instance guarantee.
-/
def theorem3_3_combined_high_low_capped_ip_solver_concrete_ip_search_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_concrete_ip_and_search_with_cap_ratio_guarantee_of_ip_solver_no_top_of_margin

/--
Theorem 3.3 capped combined high/low IP-solver concrete-IP/search full-summary
ratio endpoint: public alias exposing full capped comparison-IP and chosen-IP
summaries together with the generated no-top supply and final guarantee.
-/
def theorem3_3_combined_high_low_capped_ip_solver_concrete_ip_search_full_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_capped_ip_solver_concrete_ip_and_search_full_summary_with_ratio_guarantee_no_top_of_margin

/--
Theorem 3.3 exact rounded-allocation concrete-IP construction: public alias
for turning an exact allocation under a fixed rounded-value map into the
uncapped concrete IP candidate for a supplied value pair.
-/
def theorem3_3_concrete_ip_certificate_of_exact_rounded_allocation :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_concrete_ip_certificate_of_exact_rounded_allocation

/--
Theorem 3.3 exact rounded-allocation finite-search comparison: public alias
comparing finite search against a supplied exact rounded allocation and value
pair.
-/
def theorem3_3_value_pair_search_ratio_le_of_exact_rounded_allocation :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_value_pair_search_ratio_le_of_exact_rounded_allocation

/--
Theorem 3.3 exact rounded-allocation finite-search existence: public alias
constructing the search certificate from a supplied value-pair window for an
exact rounded allocation.
-/
def theorem3_3_exists_value_pair_search_certificate_of_exact_rounded_allocation :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_of_exact_rounded_allocation

/--
Theorem 3.3 exact rounded-allocation search ratio endpoint: public alias for a
supplied value-pair window on an exact rounded allocation, paired with the
final rounded-instance guarantee.
-/
def theorem3_3_exact_rounded_allocation_search_certificate_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_ratio_guarantee_of_exact_rounded_allocation

/--
Theorem 3.3 exact rounded-allocation search summary ratio endpoint: public
alias for a supplied value-pair window, additionally recording selected-pair
admissibility for the finite search certificate.
-/
def theorem3_3_exact_rounded_allocation_search_certificate_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_summary_with_ratio_guarantee_of_exact_rounded_allocation

/--
Theorem 3.3 exact rounded-allocation concrete-IP/search ratio endpoint: public
alias packaging a supplied value-pair window as the concrete IP candidate for
the exact rounded allocation.
-/
def theorem3_3_exact_rounded_allocation_concrete_ip_search_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_concrete_ip_and_search_with_ratio_guarantee_of_exact_rounded_allocation

/--
Theorem 3.3 exact rounded-allocation concrete-IP/search full-summary ratio
endpoint: public alias exposing full concrete-IP constraints and chosen
search-IP summary for a supplied value-pair window.
-/
def theorem3_3_exact_rounded_allocation_concrete_ip_search_full_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_concrete_ip_and_search_full_summary_ratio_guarantee_of_exact_rounded_allocation

/--
Theorem 3.3 exact rounded-allocation min/max pair: public alias proving that a
bounded exact rounded allocation's min/max load pair lies in the admissible
value-pair set.
-/
def theorem3_3_exact_rounded_allocation_min_max_pair_mem :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exact_rounded_allocation_min_max_pair_mem

/--
Theorem 3.3 exact rounded-allocation type-window bridge: public alias proving
that each induced rounded bundle type lies in the allocation's min/max window.
-/
def theorem3_3_exact_rounded_allocation_types_in_min_max_window :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exact_rounded_allocation_types_in_min_max_window

/--
Theorem 3.3 bounded exact rounded-allocation concrete-IP construction: public
alias using the allocation's min/max rounded loads as the concrete IP pair.
-/
def theorem3_3_concrete_ip_certificate_of_exact_bounded_rounded_allocation :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_concrete_ip_certificate_of_exact_bounded_rounded_allocation

/--
Theorem 3.3 capped exact rounded-allocation concrete-IP construction: public
alias using the allocation's min/max rounded loads as a capped concrete IP
pair at the actual average scale.
-/
def theorem3_3_concrete_ip_certificate_with_cap_of_exact_bounded_rounded_allocation :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_concrete_ip_certificate_with_cap_of_exact_bounded_rounded_allocation

/--
Theorem 3.3 Claim 3.4 bridge: public alias converting a Claim 3.4 certificate
for the rounded source model into min/max rounded type-window membership.
-/
def theorem3_3_rounded_bundle_type_of_bundle_mem_min_max_window_of_claim34 :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_roundedBundleTypeOfBundle_mem_min_max_window_of_claim34

/--
Theorem 3.3 bounded exact rounded-allocation finite-search comparison: public
alias comparing finite search against the allocation's own min/max load ratio.
-/
def theorem3_3_value_pair_search_ratio_le_of_exact_bounded_rounded_allocation :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_value_pair_search_ratio_le_of_exact_bounded_rounded_allocation

/--
Theorem 3.3 bounded exact rounded-allocation finite-search existence: public
alias constructing the search certificate from the allocation-induced concrete
IP candidate.
-/
def theorem3_3_exists_value_pair_search_certificate_of_exact_bounded_rounded_allocation :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_of_exact_bounded_rounded_allocation

/--
Theorem 3.3 exact rounded-allocation search ratio endpoint: public alias for
the finite-search certificate induced by any bounded exact allocation under a
fixed rounded-value map, paired with the final rounded-instance guarantee.
-/
def theorem3_3_exact_bounded_rounded_allocation_search_certificate_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_ratio_guarantee_of_exact_bounded_rounded_allocation

/--
Theorem 3.3 exact bounded rounded-allocation search summary ratio endpoint:
public alias exposing selected-pair admissibility for the finite search
certificate induced by a bounded exact allocation.
-/
def theorem3_3_exact_bounded_rounded_allocation_search_certificate_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_summary_with_ratio_guarantee_of_exact_bounded_rounded_allocation

/--
Theorem 3.3 exact rounded-allocation concrete-IP/search ratio endpoint: public
alias packaging a bounded exact allocation under a fixed rounded-value map as
the concrete IP certificate for its rounded min/max pair.
-/
def theorem3_3_exact_bounded_rounded_allocation_concrete_ip_search_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_concrete_ip_and_search_with_ratio_guarantee_of_exact_bounded_rounded_allocation

/--
Theorem 3.3 exact bounded rounded-allocation concrete-IP/search full-summary
ratio endpoint: public alias exposing full min/max concrete-IP constraints
and chosen search-IP summary for a bounded exact allocation.
-/
def theorem3_3_exact_bounded_rounded_allocation_concrete_ip_search_full_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_concrete_ip_and_search_full_summary_ratio_guarantee_of_exact_bounded_rounded_allocation

/--
Theorem 3.3 exact rounded-supply allocation concrete-IP construction: public
alias packaging a bounded exact allocation of a materialized rounded supply as
the concrete IP certificate for its rounded min/max pair.
-/
def theorem3_3_concrete_ip_certificate_of_exact_bounded_supply_allocation :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_concrete_ip_certificate_of_exact_bounded_supply_allocation

/--
Theorem 3.3 exact rounded-supply allocation type-assignment existence: public
alias extracting the rounded bundle-type assignment from a bounded exact
allocation of a materialized rounded supply.
-/
def theorem3_3_exists_supply_type_assignment_of_exact_bounded_supply_allocation :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_supply_type_assignment_of_exact_bounded_supply_allocation

/--
Theorem 3.3 capped exact rounded-supply allocation concrete-IP construction:
public alias packaging a bounded exact allocation of a materialized rounded
supply as a capped concrete IP certificate around the actual average scale.
-/
def theorem3_3_concrete_ip_certificate_with_cap_of_exact_bounded_supply_allocation :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_concrete_ip_certificate_with_cap_of_exact_bounded_supply_allocation

/--
Theorem 3.3 capped concrete-IP realization: public alias for the generic
load-window consequence of realizing capped IP multiplicities by agent types.
-/
def theorem3_3_exact_bounded_allocation_window_of_capped_ip_type_realization :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exact_bounded_allocation_window_of_capped_ip_type_realization

/--
Theorem 3.3 rounded-load identity: public alias showing that per-index count
realization of a rounded bundle type implies the exact rounded common-load
identity.
-/
def theorem3_3_commonLoad_eq_roundedBundleTypeLoad_of_bundle_index_counts :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_commonLoad_eq_roundedBundleTypeLoad_of_bundle_index_counts

/--
Theorem 3.3 realized-allocation ratio bound: public alias bounding an exact
rounded allocation's load ratio by any value-pair window realized by its
per-agent rounded types.
-/
def theorem3_3_rounded_allocation_ratio_le_value_pair_of_window_count_realization :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_rounded_allocation_ratio_le_value_pair_of_window_count_realization

/--
Theorem 3.3 selected capped-search realization: public alias bounding a
realized chosen-IP allocation by the selected capped search pair's ratio.
-/
def theorem3_3_realized_capped_search_allocation_ratio_le_chosen_pair :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_realized_capped_search_allocation_ratio_le_chosen_pair

/--
Theorem 3.3 capped concrete-IP realization: public alias for the count-based
bounded-window consequence of realizing capped IP multiplicities.
-/
def theorem3_3_exact_bounded_allocation_window_of_capped_ip_count_realization :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exact_bounded_allocation_window_of_capped_ip_count_realization

/--
Theorem 3.3 capped concrete-IP realization: public alias for the window-plus
count version of the bounded-window consequence.
-/
def theorem3_3_exact_bounded_allocation_window_of_capped_ip_window_count_realization :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exact_bounded_allocation_window_of_capped_ip_window_count_realization

/--
Theorem 3.3 capped concrete-IP realization: public alias assigning concrete
agent types with fibers equal to the capped IP multiplicities.
-/
def theorem3_3_exists_type_assignment_realizing_capped_ip :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_type_assignment_realizing_capped_ip

/--
Theorem 3.3 capped concrete-IP realization: public alias constructing an exact
allocation with the assigned per-index rounded-type counts.
-/
def theorem3_3_exists_exact_allocation_realizing_capped_ip_type_assignment :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_exact_allocation_realizing_capped_ip_type_assignment

/--
Theorem 3.3 capped concrete-IP realization: public alias constructing a
bounded exact allocation over any finite indexed materialization with matching
supply fibers.
-/
def theorem3_3_exists_exact_bounded_allocation_of_indexed_concrete_ip_with_cap :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_exact_bounded_allocation_of_indexed_concrete_ip_with_cap

/--
Theorem 3.3 materialized rounded-supply capped-IP realization: public alias for
the full finite realization from a capped IP certificate to a bounded exact
anonymous rounded-supply allocation.
-/
def theorem3_3_exists_exact_bounded_supply_allocation_of_concrete_ip_with_cap :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_exact_bounded_supply_allocation_of_concrete_ip_with_cap

/--
Theorem 3.3 typed combined high/low capped-IP realization: public alias for the
full finite realization from a capped IP certificate to a bounded exact typed
combined high/low allocation.
-/
def theorem3_3_exists_exact_bounded_typed_combined_high_low_allocation_of_concrete_ip_with_cap :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_exact_bounded_typed_combined_high_low_allocation_of_concrete_ip_with_cap

/--
Theorem 3.3 materialized rounded-supply search realization: public alias
materializing the chosen capped IP in a value-pair search certificate.
-/
def theorem3_3_exists_exact_bounded_supply_allocation_of_search_certificate_with_cap :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_exact_bounded_supply_allocation_of_search_certificate_with_cap

/--
Theorem 3.3 typed combined high/low search realization: public alias
materializing the chosen capped IP in a value-pair search certificate.
-/
def theorem3_3_exists_exact_bounded_typed_combined_high_low_allocation_of_search_certificate_with_cap :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_exact_bounded_typed_combined_high_low_allocation_of_search_certificate_with_cap

/--
Theorem 3.3 capped concrete-IP realization: public alias turning a realized
capped IP and exact allocation into a bounded exact allocation.
-/
def theorem3_3_exists_exact_bounded_allocation_of_concrete_ip_with_cap_realization :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_exact_bounded_allocation_of_concrete_ip_with_cap_realization

/--
Theorem 3.3 materialized rounded-supply capped-IP realization: public alias
for the reverse-direction target over anonymous materialized rounded items.
-/
def theorem3_3_exists_exact_bounded_supply_allocation_of_concrete_ip_with_cap_realization :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_exact_bounded_supply_allocation_of_concrete_ip_with_cap_realization

/--
Theorem 3.3 materialized rounded-supply capped-IP realization: public alias for
the per-index count-realization variant.
-/
def theorem3_3_exists_exact_bounded_supply_allocation_of_concrete_ip_with_cap_count_realization :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_exact_bounded_supply_allocation_of_concrete_ip_with_cap_count_realization

/--
Theorem 3.3 typed combined high/low capped-IP realization: public alias for
the reverse-direction target over provenance-carrying combined high/low items.
-/
def theorem3_3_exists_exact_bounded_typed_combined_high_low_allocation_of_concrete_ip_with_cap_realization :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_exact_bounded_typed_combined_high_low_allocation_of_concrete_ip_with_cap_realization

/--
Theorem 3.3 typed combined high/low capped-IP realization: public alias for
the per-index count-realization variant.
-/
def theorem3_3_exists_exact_bounded_typed_combined_high_low_allocation_of_concrete_ip_with_cap_count_realization :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_exact_bounded_typed_combined_high_low_allocation_of_concrete_ip_with_cap_count_realization

/--
Theorem 3.3 solver-premise bridge: public alias turning a provider of bounded
exact materialized rounded-supply allocations into the capped concrete-IP
witness premise used by solver-facing endpoints.
-/
def theorem3_3_solver_premise_with_cap_of_exact_bounded_supply_allocation_provider :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_solver_premise_with_cap_of_exact_bounded_supply_allocation_provider

/--
Theorem 3.3 source-auto-cap solver-premise bridge: public alias turning a
provider of bounded exact materialized rounded-supply allocations into the
capped concrete-IP witness premise with the canonical source auto cap.
-/
def theorem3_3_source_auto_cap_solver_premise_with_cap_of_exact_bounded_supply_allocation_provider :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_auto_cap_solver_premise_with_cap_of_exact_bounded_supply_allocation_provider

/--
Theorem 3.3 source-auto-cap solver-premise bridge: public alias turning a
provider of bounded exact typed combined high/low allocations into the capped
concrete-IP witness premise for the generated anonymous rounded supply.
-/
def theorem3_3_source_auto_cap_solver_premise_with_cap_of_exact_bounded_typed_combined_high_low_allocation_provider :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_auto_cap_solver_premise_with_cap_of_exact_bounded_typed_combined_high_low_allocation_provider

/--
Theorem 3.3 source-average solver-premise bridge: public alias deriving the
canonical source auto-cap solver premise from source-average high/low
hypotheses and a provider of bounded exact materialized rounded-supply
allocations.
-/
def theorem3_3_source_auto_cap_solver_premise_with_cap_of_source_average_exact_bounded_supply_allocation_provider :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_auto_cap_solver_premise_with_cap_of_source_average_exact_bounded_supply_allocation_provider

/--
Theorem 3.3 source-average solver-premise bridge: public alias deriving the
canonical source auto-cap solver premise from source-average high/low
hypotheses and a provider of bounded exact typed combined high/low allocations.
-/
def theorem3_3_source_auto_cap_solver_premise_with_cap_of_source_average_exact_bounded_typed_combined_high_low_allocation_provider :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_auto_cap_solver_premise_with_cap_of_source_average_exact_bounded_typed_combined_high_low_allocation_provider

/--
Theorem 3.3 named source-auto-cap solver obligation: public alias deriving the
named obligation from a bounded exact materialized-allocation provider and an
explicit rounded-average cap bound.
-/
def theorem3_3_source_auto_cap_ip_solver_obligation_of_exact_bounded_supply_allocation_provider :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_auto_cap_ip_solver_obligation_of_exact_bounded_supply_allocation_provider

/--
Theorem 3.3 named source-auto-cap solver obligation: public alias deriving the
named obligation from a bounded exact typed high/low allocation provider and an
explicit rounded-average cap bound.
-/
def theorem3_3_source_auto_cap_ip_solver_obligation_of_exact_bounded_typed_combined_high_low_allocation_provider :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_auto_cap_ip_solver_obligation_of_exact_bounded_typed_combined_high_low_allocation_provider

/--
Theorem 3.3 named source-auto-cap solver obligation: public alias deriving the
named obligation from source-average hypotheses and a bounded exact
materialized-allocation provider.
-/
def theorem3_3_source_auto_cap_ip_solver_obligation_of_source_average_exact_bounded_supply_allocation_provider :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_auto_cap_ip_solver_obligation_of_source_average_exact_bounded_supply_allocation_provider

/--
Theorem 3.3 named source-auto-cap solver obligation: public alias deriving the
named obligation from source-average hypotheses and a bounded exact typed
high/low allocation provider.
-/
def theorem3_3_source_auto_cap_ip_solver_obligation_of_source_average_exact_bounded_typed_combined_high_low_allocation_provider :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_auto_cap_ip_solver_obligation_of_source_average_exact_bounded_typed_combined_high_low_allocation_provider

/--
Theorem 3.3 named source-auto-cap solver obligation: public alias deriving the
named obligation directly from the verified Claim 3.4 rounded-supply bridge
under source-average high/low hypotheses.
-/
def theorem3_3_source_auto_cap_ip_solver_obligation_of_source_average_claim34_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_auto_cap_ip_solver_obligation_of_source_average_claim34_no_top_of_margin

/--
Theorem 3.3 external-complexity seam: public alias packaging any concrete
external solver notion, feasibility/runtime predicate, and consequence through
the named source-auto-cap IP solver obligation.
-/
def theorem3_3_external_source_auto_cap_ip_solver_obligation_consequence :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_external_source_auto_cap_ip_solver_obligation_consequence

/--
Theorem 3.3 external-complexity seam: public alias returning both the named
source-auto-cap solver obligation and the corresponding external consequence.
-/
def theorem3_3_external_source_auto_cap_ip_solver_obligation_and_consequence :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_external_source_auto_cap_ip_solver_obligation_and_consequence

/--
Theorem 3.3 external-complexity seam: public alias using the source-average
Claim 3.4 bridge to supply the named source-auto-cap solver obligation before
applying an external feasible-solver consequence.
-/
def theorem3_3_external_source_auto_cap_ip_solver_obligation_consequence_of_source_average_claim34_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_external_source_auto_cap_ip_solver_obligation_consequence_of_source_average_claim34_no_top_of_margin

/--
Theorem 3.3 external-complexity seam: public alias returning both the
source-average Claim 3.4 named obligation and the corresponding external
consequence.
-/
def theorem3_3_external_source_auto_cap_ip_solver_obligation_and_consequence_of_source_average_claim34_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_external_source_auto_cap_ip_solver_obligation_and_consequence_of_source_average_claim34_no_top_of_margin

/--
Theorem 3.3 external-complexity seam: public alias using a source-average
exact bounded materialized-allocation provider to supply the named
source-auto-cap solver obligation before applying an external consequence.
-/
def theorem3_3_external_source_auto_cap_ip_solver_obligation_consequence_of_source_average_exact_bounded_supply_allocation_provider :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_external_source_auto_cap_ip_solver_obligation_consequence_of_source_average_exact_bounded_supply_allocation_provider

/--
Theorem 3.3 external-complexity seam: public alias returning both the named
obligation from a source-average exact bounded materialized-allocation provider
and the corresponding external consequence.
-/
def theorem3_3_external_source_auto_cap_ip_solver_obligation_and_consequence_of_source_average_exact_bounded_supply_allocation_provider :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_external_source_auto_cap_ip_solver_obligation_and_consequence_of_source_average_exact_bounded_supply_allocation_provider

/--
Theorem 3.3 external-complexity seam: public alias using a source-average
exact bounded typed high/low allocation provider to supply the named
source-auto-cap solver obligation before applying an external consequence.
-/
def theorem3_3_external_source_auto_cap_ip_solver_obligation_consequence_of_source_average_exact_bounded_typed_combined_high_low_allocation_provider :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_external_source_auto_cap_ip_solver_obligation_consequence_of_source_average_exact_bounded_typed_combined_high_low_allocation_provider

/--
Theorem 3.3 external-complexity seam: public alias returning both the named
obligation from a source-average exact bounded typed high/low allocation
provider and the corresponding external consequence.
-/
def theorem3_3_external_source_auto_cap_ip_solver_obligation_and_consequence_of_source_average_exact_bounded_typed_combined_high_low_allocation_provider :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_external_source_auto_cap_ip_solver_obligation_and_consequence_of_source_average_exact_bounded_typed_combined_high_low_allocation_provider

/--
Theorem 3.3 exact rounded-supply allocation finite-search comparison: public
alias comparing finite search against a bounded exact allocation of a
materialized rounded supply.
-/
def theorem3_3_value_pair_search_ratio_le_of_exact_bounded_supply_allocation :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_value_pair_search_ratio_le_of_exact_bounded_supply_allocation

/--
Theorem 3.3 exact rounded-supply allocation finite-search existence: public
alias constructing the search certificate from a bounded exact allocation of a
materialized rounded supply.
-/
def theorem3_3_exists_value_pair_search_certificate_of_exact_bounded_supply_allocation :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_of_exact_bounded_supply_allocation

/--
Theorem 3.3 exact rounded-supply allocation ratio endpoint: a bounded exact
allocation of a materialized rounded supply yields a finite-search certificate
together with the final rounded-instance `(1 + epsilon)` guarantee.
-/
def theorem3_3_exact_bounded_supply_allocation_search_certificate_ratio_endpoint
    {SourceAgent SourceItem Alloc : Type*}
    [Fintype SourceAgent] [Nonempty SourceAgent]
    {M : Theorem33.IdenticalUtilitiesModel SourceAgent SourceItem Alloc}
    {L epsilon : ℝ} {lambda : ℕ} {optimal : Alloc}
    (hepsilon_pos : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1)
    (cert : Theorem33.RoundedInstanceSearchCertificate M L epsilon lambda optimal)
    (supply : Theorem33.RoundedValueIndex lambda → ℕ)
    (A :
      Allocation SourceAgent
        (paper_lmms_theorem_3_3_roundedSupplyItem supply))
    (halloc :
      IsAllocationOf A
        (Finset.univ :
          Finset (paper_lmms_theorem_3_3_roundedSupplyItem supply)))
    (hlambda : 0 < lambda) (hL : 0 < L)
    (hwindow :
      ∀ i : SourceAgent,
        Theorem34.boundedAroundAverage L
          (Theorem34.commonLoad
            (fun item : paper_lmms_theorem_3_3_roundedSupplyItem supply =>
              Theorem33.roundedValue L lambda
                (paper_lmms_theorem_3_3_roundedSupplyIndexOf item))
            (A i))) :=
  LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_ratio_guarantee_of_exact_bounded_supply_allocation
    hepsilon_pos hepsilon_le_one cert supply A halloc hlambda hL hwindow

/--
Theorem 3.3 exact rounded-supply allocation search summary ratio endpoint:
public alias exposing selected-pair admissibility for the finite search
certificate induced by a bounded allocation of a materialized rounded supply.
-/
def theorem3_3_exact_bounded_supply_allocation_search_certificate_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_summary_with_ratio_guarantee_of_exact_bounded_supply_allocation

/--
Theorem 3.3 exact rounded-supply allocation concrete-IP/search endpoint:
a bounded exact allocation of a materialized rounded supply yields the
concrete IP certificate for its min/max pair, a finite-search certificate,
and the final rounded-instance `(1 + epsilon)` guarantee.
-/
def theorem3_3_exact_bounded_supply_allocation_concrete_ip_search_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_concrete_ip_and_search_with_ratio_guarantee_of_exact_bounded_supply_allocation

/--
Theorem 3.3 exact rounded-supply allocation concrete-IP/search full-summary
endpoint: public alias exposing the full concrete-IP constraint summary and
chosen search-IP summary for a bounded exact allocation of a materialized
rounded supply.
-/
def theorem3_3_exact_bounded_supply_allocation_concrete_ip_search_full_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_concrete_ip_and_search_full_summary_ratio_guarantee_of_exact_bounded_supply_allocation

/--
Theorem 3.3: a rounded-instance search certificate gives the final
`(1 + epsilon)` ratio guarantee, and every concrete goods-supply IP candidate
exposes the source value-pair comparison plus assignment and goods equations.
-/
theorem theorem3_3_search_certificate_ratio_guarantee_and_concrete_ip_summary
    {SourceAgent SourceItem Alloc : Type*}
    [Fintype SourceAgent] [Nonempty SourceAgent]
    {M : Theorem33.IdenticalUtilitiesModel SourceAgent SourceItem Alloc}
    {L epsilon : ℝ} {lambda : ℕ} {optimal : Alloc}
    (hepsilon_pos : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1)
    (cert : Theorem33.RoundedInstanceSearchCertificate M L epsilon lambda optimal)
    {p : ℝ × ℝ} {goodsSupply : Theorem33.RoundedValueIndex lambda → ℕ}
    (ip : Theorem33.RoundedConcreteIPCertificate L lambda SourceAgent p goodsSupply) :
    Theorem33.allocationLoadRatio M cert.output ≤
        Theorem33.allocationLoadRatio M optimal * (1 + epsilon) ∧
      Theorem33.roundedValuePairRatio cert.chosenPair ≤
        Theorem33.roundedValuePairRatio p ∧
      ip.toValuePairIPCertificate.ip.admissibleTypes.card ≤
          (2 * lambda + 1) ^
            Fintype.card (Theorem33.RoundedValueIndex lambda) ∧
      ip.toValuePairIPCertificate.ip.admissibleTypes.sum
          ip.toValuePairIPCertificate.ip.typeMultiplicity =
        Fintype.card SourceAgent ∧
      (∀ k : Theorem33.RoundedValueIndex lambda,
        ip.toValuePairIPCertificate.ip.admissibleTypes.sum
            (fun t => ip.toValuePairIPCertificate.ip.typeMultiplicity t * t.count k) =
          goodsSupply k) := by
  exact
    LMMS04FairDivision.paper_lmms_theorem_3_3_search_certificate_ratio_guarantee_and_concrete_ip_summary
      hepsilon_pos hepsilon_le_one cert ip

/--
Theorem 3.3 capped search/IP interface: public alias exposing the final
rounded-instance guarantee together with the selected capped search pair and
chosen-IP constraints.
-/
def theorem3_3_capped_search_certificate_ratio_guarantee_and_chosen_ip_summary :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_rounded_instance_search_certificate_ratio_guarantee_and_capped_chosen_ip_summary

/--
Theorem 3.3 capped search/IP interface: a rounded-instance search certificate
gives the final `(1 + epsilon)` guarantee, while a capped finite value-pair
search certificate exposes the comparison IP, search-space, and chosen-IP
constraints used by the two-scale solver surface.
-/
theorem theorem3_3_capped_search_certificate_ratio_guarantee_and_full_ip_summary
    {SourceAgent SourceItem Alloc : Type*}
    [Fintype SourceAgent] [Nonempty SourceAgent]
    {M : Theorem33.IdenticalUtilitiesModel SourceAgent SourceItem Alloc}
    {L LR epsilon : ℝ} {lambda maxCount : ℕ} {optimal : Alloc}
    (hepsilon_pos : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1)
    (cert : Theorem33.RoundedInstanceSearchCertificate M L epsilon lambda optimal)
    {supply : Theorem33.RoundedValueIndex lambda → ℕ}
    (hmaxCount : maxCount ≤ 2 * lambda + 4)
    (search :
      Theorem33.RoundedValuePairSearchCertificateWithCap
        L LR lambda maxCount SourceAgent supply)
    {p : ℝ × ℝ}
    (ip :
      Theorem33.RoundedConcreteIPCertificateWithCap
        L LR lambda maxCount SourceAgent p supply) :
    Theorem33.allocationLoadRatio M cert.output ≤
        Theorem33.allocationLoadRatio M optimal * (1 + epsilon) ∧
      Theorem33.roundedValuePairRatio search.chosenPair ≤
        Theorem33.roundedValuePairRatio p ∧
      p ∈ Theorem33.roundedAdmissibleValuePairSetWithCap
          L LR lambda maxCount ∧
        (Theorem33.roundedTypesInValueWindowWithCap
            L LR lambda maxCount p.1 p.2).card ≤
          (2 * lambda + 5) ^
            Fintype.card (Theorem33.RoundedValueIndex lambda) ∧
          (∀ t : Theorem33.RoundedBundleType lambda,
            t ∉
              Theorem33.roundedTypesInValueWindowWithCap
                L LR lambda maxCount p.1 p.2 →
            ip.typeMultiplicity t = 0) ∧
            (Theorem33.roundedTypesInValueWindowWithCap
                L LR lambda maxCount p.1 p.2).sum
              ip.typeMultiplicity =
                Fintype.card SourceAgent ∧
              (∀ k : Theorem33.RoundedValueIndex lambda,
                (Theorem33.roundedTypesInValueWindowWithCap
                    L LR lambda maxCount p.1 p.2).sum
                  (fun t => ip.typeMultiplicity t * t.count k) =
                    supply k) ∧
                (Theorem33.roundedAdmissibleValuePairSetWithCap
                    L LR lambda maxCount).card ≤
                  ((2 * lambda + 5) ^
                    Fintype.card
                      (Theorem33.RoundedValueIndex lambda)) ^ 2 ∧
                  search.chosenPair ∈
                    Theorem33.roundedAdmissibleValuePairSetWithCap
                      L LR lambda maxCount ∧
                    (Theorem33.roundedTypesInValueWindowWithCap
                        L LR lambda maxCount search.chosenPair.1
                          search.chosenPair.2).card ≤
                      (2 * lambda + 5) ^
                        Fintype.card
                          (Theorem33.RoundedValueIndex lambda) ∧
                      (∀ t : Theorem33.RoundedBundleType lambda,
                        t ∉
                          Theorem33.roundedTypesInValueWindowWithCap
                            L LR lambda maxCount search.chosenPair.1
                              search.chosenPair.2 →
                        search.chosenIP.typeMultiplicity t = 0) ∧
                        (Theorem33.roundedTypesInValueWindowWithCap
                            L LR lambda maxCount search.chosenPair.1
                              search.chosenPair.2).sum
                          search.chosenIP.typeMultiplicity =
                            Fintype.card SourceAgent ∧
                          ∀ k : Theorem33.RoundedValueIndex lambda,
                            (Theorem33.roundedTypesInValueWindowWithCap
                                L LR lambda maxCount search.chosenPair.1
                                  search.chosenPair.2).sum
                              (fun t =>
                                search.chosenIP.typeMultiplicity t *
                                  t.count k) =
                              supply k := by
  exact
    LMMS04FairDivision.paper_lmms_theorem_3_3_rounded_instance_search_certificate_ratio_guarantee_and_capped_full_ip_summary
      hepsilon_pos hepsilon_le_one cert hmaxCount search ip

/--
Theorem 3.3 source auto-cap arithmetic: public alias transferring an
inequality between scaled totals to an inequality between average loads.
-/
def theorem3_3_average_le_of_scaled_totals :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_average_le_of_scaled_totals

/--
Theorem 3.3 source auto-cap arithmetic: public alias for the concrete count
cap used to cover a target capped average.
-/
def theorem3_3_cap_count_for_average :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_capCountForAverage

/--
Theorem 3.3 source auto-cap arithmetic: public alias showing the concrete
count cap covers the target average window.
-/
def theorem3_3_cap_count_for_average_satisfies :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_capCountForAverage_satisfies

/--
Theorem 3.3 source auto-cap arithmetic: public alias showing the paper's
source auto-cap count covers the base source average.
-/
def theorem3_3_source_auto_cap_count_satisfies_base_average :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_auto_cap_count_satisfies_base_average

/--
Theorem 3.3 source auto-cap arithmetic: public alias bounding the aggregate
high/low rounding-error budget by the source slack.
-/
def theorem3_3_rounding_error_budget_le_source_slack :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_rounding_error_budget_le_source_slack

/--
Theorem 3.3 source auto-cap arithmetic: public alias bounding the paper
source-average rounding-error budget by the generated extra average.
-/
def theorem3_3_source_average_auto_cap_error_budget :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_average_auto_cap_error_budget

/--
Theorem 3.3 source auto-cap arithmetic: public alias proving that any generated
rounded average from the source-average high/low construction is bounded by
the paper's source auto-cap average.
-/
def theorem3_3_generated_rounded_average_le_source_auto_cap_average_of_source_average :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_generated_rounded_average_le_source_auto_cap_average_of_source_average

/--
Theorem 3.3 source auto-cap arithmetic: public alias proving that the paper's
source auto-cap count covers any generated rounded average from the
source-average high/low construction.
-/
def theorem3_3_source_auto_cap_count_satisfies_generated_average_of_source_average :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_auto_cap_count_satisfies_generated_average_of_source_average

/--
Theorem 3.3 source auto-cap arithmetic: public alias bounding the per-agent
extra average by two rounded grid units.
-/
def theorem3_3_source_auto_cap_extra_average_le_two_units :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_auto_cap_extra_average_le_two_units

/--
Theorem 3.3 source auto-cap arithmetic: public alias bounding the auto-cap
average by the paper's `L * (1 + 2 / lambda)` scale.
-/
def theorem3_3_source_auto_cap_average_le_one_plus_two_over_lambda :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_auto_cap_average_le_one_plus_two_over_lambda

/--
Theorem 3.3 source auto-cap arithmetic: public alias for the linear
`2 * lambda + 4` cap-count bound.
-/
def theorem3_3_source_auto_cap_count_le :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_auto_cap_count_le

/--
Theorem 3.3 source auto-cap search surface: public alias for the capped
value-pair set cardinality bound.
-/
def theorem3_3_source_auto_cap_value_pair_set_card_le :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_auto_cap_value_pair_set_card_le

/--
Theorem 3.3 source auto-cap search surface: public alias for the capped type
set cardinality bound.
-/
def theorem3_3_source_auto_cap_type_set_card_le :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_auto_cap_type_set_card_le

/--
Theorem 3.3 source auto-cap search surface: public alias for the capped
value-window cardinality bound.
-/
def theorem3_3_source_auto_cap_value_window_card_le :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_auto_cap_value_window_card_le

/--
Theorem 3.3 source auto-cap search surface: public alias for the explicit
`lambda^2 + 1` capped value-pair set cardinality bound.
-/
def theorem3_3_source_auto_cap_value_pair_set_card_le_explicit :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_auto_cap_value_pair_set_card_le_explicit

/--
Theorem 3.3 source auto-cap search surface: public alias for the explicit
`lambda^2 + 1` capped type set cardinality bound.
-/
def theorem3_3_source_auto_cap_type_set_card_le_explicit :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_auto_cap_type_set_card_le_explicit

/--
Theorem 3.3 source auto-cap search surface: public alias for the explicit
`lambda^2 + 1` capped value-window cardinality bound.
-/
def theorem3_3_source_auto_cap_value_window_card_le_explicit :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_auto_cap_value_window_card_le_explicit

/--
Theorem 3.3 source auto-cap solver boundary: public alias naming the exact
capped concrete-IP certificate obligation left to the solver/Lenstra layer.
-/
def theorem3_3_source_auto_cap_ip_solver_obligation :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_source_auto_cap_ip_solver_obligation

/--
Theorem 3.3 source auto-cap seam: public alias for constructing a no-top
combined rounded supply whose rounded total is bounded by the source-average
auto-cap slack.
-/
def theorem3_3_exists_combined_high_low_source_auto_cap_upper_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_rounded_goods_supply_source_auto_cap_upper_no_top_of_margin

/--
Theorem 3.3 source-average auto-cap interface: conditional on the supplied
source-average and rounded-average identities, the high/low rounded supply
construction returns bounded capped IP/search witnesses together with the final
rounded-instance `(1 + epsilon)` ratio guarantee.
-/
theorem theorem3_3_combined_high_low_auto_cap_full_ip_summary_with_ratio_guarantee
    {SourceAgent SourceItem Alloc : Type*}
    [Fintype SourceAgent] [Nonempty SourceAgent] [DecidableEq SourceAgent]
    [DecidableEq SourceItem]
    {M : Theorem33.IdenticalUtilitiesModel SourceAgent SourceItem Alloc}
    {L LR epsilon : ℝ} {lambda : ℕ} {optimal : Alloc}
    (hepsilon_pos : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1)
    (cert : Theorem33.RoundedInstanceSearchCertificate M L epsilon lambda optimal)
    (highGoods lowGoods : Finset SourceItem) (v : SourceItem → ℝ)
    (hlambda : 1 < lambda) (hL : 0 < L)
    (hhigh :
      ∀ g : SourceItem, g ∈ highGoods →
        L / (lambda : ℝ) < v g ∧ v g < L)
    (hlow :
      ∀ g : SourceItem, g ∈ lowGoods →
        0 ≤ v g ∧ v g < L / (lambda : ℝ))
    (hmargin :
      ∀ g : SourceItem, g ∈ highGoods →
        v g + L / ((lambda : ℝ) ^ 2) ≤ L)
    (hsource_average :
      highGoods.sum v + lowGoods.sum v =
        (Fintype.card SourceAgent : ℝ) * L)
    (haverage :
      ∀ (indexOf : SourceItem → Theorem33.RoundedValueIndex lambda)
        (combinedSupply : Theorem33.RoundedValueIndex lambda → ℕ),
        (∀ g : SourceItem, g ∈ highGoods →
          v g ≤ Theorem33.roundedValue L lambda (indexOf g) ∧
            Theorem33.roundedValue L lambda (indexOf g) <
              v g + L / ((lambda : ℝ) ^ 2)) →
        (∀ k : Theorem33.RoundedValueIndex lambda,
          combinedSupply k =
            paper_lmms_theorem_3_3_roundedGoodsSupplyOfGoods indexOf highGoods k +
              Theorem33.lowGoodsAggregatedSupply L lambda (lowGoods.sum v) k) →
        (∑ k : Theorem33.RoundedValueIndex lambda,
            (combinedSupply k : ℝ) * Theorem33.roundedValue L lambda k) =
          (Fintype.card SourceAgent : ℝ) * LR) :
    ∃ maxCount : ℕ,
      maxCount ≤ 2 * lambda + 4 ∧
        (Theorem33.roundedAdmissibleTypeSetWithCap
            L LR lambda maxCount).card ≤
          (2 * lambda + 5) ^
            Fintype.card (Theorem33.RoundedValueIndex lambda) ∧
          (Theorem33.roundedAdmissibleValuePairSetWithCap
              L LR lambda maxCount).card ≤
            ((2 * lambda + 5) ^
              Fintype.card (Theorem33.RoundedValueIndex lambda)) ^ 2 ∧
            ∃ indexOf : SourceItem → Theorem33.RoundedValueIndex lambda,
              ∃ combinedSupply : Theorem33.RoundedValueIndex lambda → ℕ,
                ∃ p : ℝ × ℝ,
                  ∃ ip :
                    Theorem33.RoundedConcreteIPCertificateWithCap
                      L LR lambda maxCount SourceAgent p combinedSupply,
                    ∃ search :
                      Theorem33.RoundedValuePairSearchCertificateWithCap
                        L LR lambda maxCount SourceAgent combinedSupply,
                      Theorem33.allocationLoadRatio M cert.output ≤
                          Theorem33.allocationLoadRatio M optimal *
                            (1 + epsilon) ∧
                        Theorem33.roundedValuePairRatio search.chosenPair ≤
                          Theorem33.roundedValuePairRatio p ∧
                          p ∈
                            Theorem33.roundedAdmissibleValuePairSetWithCap
                              L LR lambda maxCount ∧
                            (Theorem33.roundedTypesInValueWindowWithCap
                                L LR lambda maxCount p.1 p.2).card ≤
                              (2 * lambda + 5) ^
                                Fintype.card
                                  (Theorem33.RoundedValueIndex lambda) ∧
                              (∀ t : Theorem33.RoundedBundleType lambda,
                                t ∉
                                  Theorem33.roundedTypesInValueWindowWithCap
                                    L LR lambda maxCount p.1 p.2 →
                                  ip.typeMultiplicity t = 0) ∧
                                (Theorem33.roundedTypesInValueWindowWithCap
                                    L LR lambda maxCount p.1 p.2).sum
                                  ip.typeMultiplicity =
                                    Fintype.card SourceAgent ∧
                                  (∀ k : Theorem33.RoundedValueIndex lambda,
                                    (Theorem33.roundedTypesInValueWindowWithCap
                                        L LR lambda maxCount p.1 p.2).sum
                                      (fun t =>
                                        ip.typeMultiplicity t * t.count k) =
                                      combinedSupply k) ∧
                                    search.chosenPair ∈
                                      Theorem33.roundedAdmissibleValuePairSetWithCap
                                        L LR lambda maxCount ∧
                                      (Theorem33.roundedTypesInValueWindowWithCap
                                          L LR lambda maxCount
                                            search.chosenPair.1
                                            search.chosenPair.2).card ≤
                                        (2 * lambda + 5) ^
                                          Fintype.card
                                            (Theorem33.RoundedValueIndex
                                              lambda) ∧
                                        (∀ t :
                                          Theorem33.RoundedBundleType lambda,
                                          t ∉
                                            Theorem33.roundedTypesInValueWindowWithCap
                                              L LR lambda maxCount
                                                search.chosenPair.1
                                                search.chosenPair.2 →
                                            search.chosenIP.typeMultiplicity t =
                                              0) ∧
                                          (Theorem33.roundedTypesInValueWindowWithCap
                                              L LR lambda maxCount
                                                search.chosenPair.1
                                                search.chosenPair.2).sum
                                            search.chosenIP.typeMultiplicity =
                                              Fintype.card SourceAgent ∧
                                            (∀ k :
                                              Theorem33.RoundedValueIndex
                                                lambda,
                                              (Theorem33.roundedTypesInValueWindowWithCap
                                                  L LR lambda maxCount
                                                    search.chosenPair.1
                                                    search.chosenPair.2).sum
                                                (fun t =>
                                                  search.chosenIP.typeMultiplicity
                                                      t *
                                                    t.count k) =
                                                combinedSupply k) ∧
                                              (∀ g : SourceItem,
                                                g ∈ highGoods →
                                                  v g ≤
                                                      Theorem33.roundedValue L
                                                        lambda (indexOf g) ∧
                                                    Theorem33.roundedValue L
                                                        lambda (indexOf g) <
                                                      v g +
                                                        L /
                                                          ((lambda : ℝ) ^ 2)) ∧
                                                (∀ k :
                                                  Theorem33.RoundedValueIndex
                                                    lambda,
                                                  combinedSupply k =
                                                    paper_lmms_theorem_3_3_roundedGoodsSupplyOfGoods
                                                        indexOf highGoods k +
                                                      Theorem33.lowGoodsAggregatedSupply
                                                        L lambda
                                                        (lowGoods.sum v) k) ∧
                                                  combinedSupply
                                                      (paper_lmms_theorem_3_3_topRoundedValueIndex
                                                        lambda) =
                                                    0 := by
  exact
    LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_auto_cap_full_ip_summary_with_ratio_guarantee_of_source_average_no_top_of_margin
      hepsilon_pos hepsilon_le_one cert highGoods lowGoods v hlambda hL
      hhigh hlow hmargin hsource_average haverage

/--
Theorem 3.3 source-average auto-cap concrete-IP/search full-summary endpoint:
conditional public alias exposing the common capped comparison-IP and
selected-search-IP summaries with the final rounded-instance guarantee, assuming
the supplied source-average and rounded-average identities.
-/
def theorem3_3_combined_high_low_auto_cap_concrete_ip_search_full_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_auto_cap_concrete_ip_and_search_full_summary_with_ratio_guarantee_of_source_average_no_top_of_margin

/--
Theorem 3.3 source-average auto-cap finite-search ratio endpoint: public alias
for the direct type-assignment/search payload with the final rounded-instance
guarantee.
-/
def theorem3_3_combined_high_low_auto_cap_search_certificate_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_value_pair_search_certificate_with_auto_cap_ratio_guarantee_of_source_average_no_top_of_margin

/--
Theorem 3.3 source-average auto-cap finite-search full-summary endpoint:
public alias exposing the selected capped search-IP summary with the final
rounded-instance guarantee.
-/
def theorem3_3_combined_high_low_auto_cap_search_certificate_full_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_value_pair_search_certificate_with_auto_cap_full_summary_ratio_guarantee_of_source_average_no_top_of_margin

/--
Theorem 3.3 source-average auto-cap ratio endpoint: conditional compact alias
for the projected endpoint that keeps the final ratio guarantee, capped search
comparison, selected pairs, and rounded source/supply facts, assuming the
supplied source-average and rounded-average identities.
-/
def theorem3_3_combined_high_low_auto_cap_ratio_endpoint
    {SourceAgent SourceItem Alloc : Type*}
    [Fintype SourceAgent] [Nonempty SourceAgent] [DecidableEq SourceAgent]
    [DecidableEq SourceItem]
    {M : Theorem33.IdenticalUtilitiesModel SourceAgent SourceItem Alloc}
    {L LR epsilon : ℝ} {lambda : ℕ} {optimal : Alloc}
    (hepsilon_pos : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1)
    (cert : Theorem33.RoundedInstanceSearchCertificate M L epsilon lambda optimal)
    (highGoods lowGoods : Finset SourceItem) (v : SourceItem → ℝ)
    (hlambda : 1 < lambda) (hL : 0 < L)
    (hhigh :
      ∀ g : SourceItem, g ∈ highGoods →
        L / (lambda : ℝ) < v g ∧ v g < L)
    (hlow :
      ∀ g : SourceItem, g ∈ lowGoods →
        0 ≤ v g ∧ v g < L / (lambda : ℝ))
    (hmargin :
      ∀ g : SourceItem, g ∈ highGoods →
        v g + L / ((lambda : ℝ) ^ 2) ≤ L)
    (hsource_average :
      highGoods.sum v + lowGoods.sum v =
        (Fintype.card SourceAgent : ℝ) * L)
    (haverage :
      ∀ (indexOf : SourceItem → Theorem33.RoundedValueIndex lambda)
        (combinedSupply : Theorem33.RoundedValueIndex lambda → ℕ),
        (∀ g : SourceItem, g ∈ highGoods →
          v g ≤ Theorem33.roundedValue L lambda (indexOf g) ∧
            Theorem33.roundedValue L lambda (indexOf g) <
              v g + L / ((lambda : ℝ) ^ 2)) →
        (∀ k : Theorem33.RoundedValueIndex lambda,
          combinedSupply k =
            paper_lmms_theorem_3_3_roundedGoodsSupplyOfGoods indexOf highGoods k +
              Theorem33.lowGoodsAggregatedSupply L lambda (lowGoods.sum v) k) →
        (∑ k : Theorem33.RoundedValueIndex lambda,
            (combinedSupply k : ℝ) * Theorem33.roundedValue L lambda k) =
          (Fintype.card SourceAgent : ℝ) * LR) :=
  LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_auto_cap_ratio_endpoint_of_source_average_no_top_of_margin
    hepsilon_pos hepsilon_le_one cert highGoods lowGoods v hlambda hL hhigh
    hlow hmargin hsource_average haverage

/--
Theorem 3.3 source-auto-cap endpoint: public alias packaging the lightweight
auto-cap ratio endpoint with the two-scale source-output bridge.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_auto_cap_search_of_source_average_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_auto_cap_search_of_source_average_no_top_of_margin

/--
Theorem 3.3 solver source-auto-cap endpoint: public alias packaging a
solver-provided capped search with the two-scale source-output bridge, leaving
the scalar forward comparison for the solver pair explicit.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_source_average_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_source_average_no_top_of_margin

/--
Theorem 3.3 compact package: public alias for a rounded-instance search
certificate paired with capped comparison/search full-IP summaries.
-/
def theorem3_3_rounded_instance_search_certificate_capped_full_ip_summary_package :=
  @LMMS04FairDivision.theorem33RoundedInstanceSearchCertificateCappedFullIPSummaryPackage

/--
Theorem 3.3 compact package: public alias for the actual-average auto-cap
route that ties the selected-pair forward-ratio bound, full-IP summaries, and
source-output payload to the same selected search witness.
-/
def theorem3_3_actual_average_auto_cap_selected_pair_full_summary_source_output_package :=
  @LMMS04FairDivision.theorem33ActualAverageAutoCapSelectedPairFullSummarySourceOutputPackage

/--
Theorem 3.3 compact package: public alias for the solver auto-cap route that
ties the selected-pair forward-ratio bound, full-IP summaries, and
source-output payload to the same selected search witness.
-/
def theorem3_3_solver_auto_cap_selected_pair_full_summary_source_output_package :=
  @LMMS04FairDivision.theorem33SolverAutoCapSelectedPairFullSummarySourceOutputPackage

/--
Theorem 3.3 compact package: public alias for the final conditional external
solver boundary, pairing the selected-pair/full-IP source-output package with an
abstract external solver consequence.
-/
def theorem3_3_external_solver_selected_pair_full_summary_source_output_package :=
  @LMMS04FairDivision.theorem33ExternalSolverSelectedPairFullSummarySourceOutputPackage

/--
Theorem 3.3 compact package: public alias for projecting the verified
selected-pair/full-IP source-output payload out of the final conditional
package.
-/
def theorem3_3_external_solver_selected_pair_full_summary_source_output_payload :=
  @LMMS04FairDivision.theorem33ExternalSolverSelectedPairFullSummarySourceOutputPayload

/--
Theorem 3.3 compact package: public alias for projecting the externally
supplied runtime/FPTAS consequence out of the final conditional package.
-/
def theorem3_3_external_solver_selected_pair_full_summary_source_output_consequence :=
  @LMMS04FairDivision.theorem33ExternalSolverSelectedPairFullSummarySourceOutputConsequence

/--
Theorem 3.3 compact package: public alias for the lightweight solver auto-cap
source-output package.
-/
def theorem3_3_solver_auto_cap_source_output_package :=
  @LMMS04FairDivision.theorem33SolverAutoCapSourceOutputPackage

/--
Theorem 3.3 solver source-auto-cap endpoint: public alias for the named
solver-obligation form with scalar forward comparison.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_source_average_of_solver_obligation_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_source_average_of_solver_obligation_no_top_of_margin

/--
Theorem 3.3 solver source-auto-cap endpoint: public alias pairing the named
solver-obligation source-output package with the full comparison/search IP
summaries.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_with_full_ip_summaries_of_source_average_of_solver_obligation_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_with_full_ip_summaries_of_source_average_of_solver_obligation_no_top_of_margin

/--
Theorem 3.3 solver source-auto-cap endpoint: public alias returning the named
solver-obligation full-IP summary, selected-pair forward-ratio bound, and
source-output payload for the same selected search witness.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_source_average_of_solver_obligation_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_source_average_of_solver_obligation_no_top_of_margin

/--
Theorem 3.3 solver source-auto-cap endpoint: public alias pairing the named
solver-obligation additive source-output package with the full
comparison/search IP summaries.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_with_full_ip_summaries_of_source_average_forward_additive_of_solver_obligation_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_with_full_ip_summaries_of_source_average_forward_additive_of_solver_obligation_no_top_of_margin

/--
Theorem 3.3 solver source-auto-cap endpoint: public alias returning the named
solver-obligation additive full-IP summary, selected-pair forward-ratio bound,
and source-output payload for the same selected search witness.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_source_average_forward_additive_of_solver_obligation_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_source_average_forward_additive_of_solver_obligation_no_top_of_margin

/--
Theorem 3.3 solver source-auto-cap endpoint: public alias deriving the named
solver obligation from the source-average Claim-3.4 bridge while keeping the
scalar forward comparison explicit.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_source_average_claim34_solver_obligation_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_source_average_claim34_solver_obligation_no_top_of_margin

/--
Theorem 3.3 solver source-auto-cap endpoint: public alias pairing the
Claim-3.4-discharge scalar source-output package with the full
comparison/search IP summaries.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_with_full_ip_summaries_of_source_average_claim34_solver_obligation_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_with_full_ip_summaries_of_source_average_claim34_solver_obligation_no_top_of_margin

/--
Theorem 3.3 solver source-auto-cap endpoint: public alias returning the
Claim-3.4-discharge full-IP summary, selected-pair forward-ratio bound, and
source-output payload for the same selected search witness.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_source_average_claim34_solver_obligation_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_source_average_claim34_solver_obligation_no_top_of_margin

/--
Theorem 3.3 solver source-auto-cap endpoint: public alias deriving the named
solver obligation from a source-average exact bounded materialized-allocation
provider before applying the source-output bridge.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_source_average_exact_bounded_supply_allocation_provider_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_source_average_exact_bounded_supply_allocation_provider_no_top_of_margin

/--
Theorem 3.3 solver source-auto-cap endpoint: public alias deriving the named
solver obligation from a source-average exact bounded materialized-allocation
provider and returning full IP summaries, selected-pair forward-ratio bound,
and source-output payload for the same selected search witness.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_source_average_exact_bounded_supply_allocation_provider_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_source_average_exact_bounded_supply_allocation_provider_no_top_of_margin

/--
Theorem 3.3 solver source-auto-cap endpoint: public alias deriving the named
solver obligation from a source-average exact bounded typed high/low allocation
provider before applying the source-output bridge.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_source_average_exact_bounded_typed_combined_high_low_allocation_provider_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_source_average_exact_bounded_typed_combined_high_low_allocation_provider_no_top_of_margin

/--
Theorem 3.3 solver source-auto-cap endpoint: public alias deriving the named
solver obligation from a source-average exact bounded typed high/low allocation
provider and returning full IP summaries, selected-pair forward-ratio bound,
and source-output payload for the same selected search witness.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_source_average_exact_bounded_typed_combined_high_low_allocation_provider_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_source_average_exact_bounded_typed_combined_high_low_allocation_provider_no_top_of_margin

/--
Theorem 3.3 external source-output seam: public alias pairing the exact
bounded materialized-allocation provider source-output package with an
externally supplied complexity consequence.
-/
def theorem3_3_external_source_output_ratio_transfer_and_solver_auto_cap_search_of_source_average_exact_bounded_supply_allocation_provider_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_external_source_output_ratio_transfer_and_solver_auto_cap_search_of_source_average_exact_bounded_supply_allocation_provider_no_top_of_margin

/--
Theorem 3.3 external source-output seam: public alias pairing the exact
bounded materialized-allocation provider selected-pair full-IP source-output
package with an externally supplied complexity consequence.
-/
def theorem3_3_external_source_output_ratio_transfer_and_solver_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_source_average_exact_bounded_supply_allocation_provider_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_external_source_output_ratio_transfer_and_solver_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_source_average_exact_bounded_supply_allocation_provider_no_top_of_margin

/--
Theorem 3.3 external source-output seam: public alias pairing the exact
bounded typed high/low allocation provider source-output package with an
externally supplied complexity consequence.
-/
def theorem3_3_external_source_output_ratio_transfer_and_solver_auto_cap_search_of_source_average_exact_bounded_typed_combined_high_low_allocation_provider_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_external_source_output_ratio_transfer_and_solver_auto_cap_search_of_source_average_exact_bounded_typed_combined_high_low_allocation_provider_no_top_of_margin

/--
Theorem 3.3 external source-output seam: public alias pairing the exact
bounded typed high/low allocation provider selected-pair full-IP source-output
package with an externally supplied complexity consequence.
-/
def theorem3_3_external_source_output_ratio_transfer_and_solver_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_source_average_exact_bounded_typed_combined_high_low_allocation_provider_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_external_source_output_ratio_transfer_and_solver_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_source_average_exact_bounded_typed_combined_high_low_allocation_provider_no_top_of_margin

/--
Theorem 3.3 solver source-auto-cap endpoint: public alias packaging a
solver-provided capped search with additive pair estimates for the scalar
forward continuation of the solver pair.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_source_average_forward_additive_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_source_average_forward_additive_no_top_of_margin

/--
Theorem 3.3 solver source-auto-cap endpoint: public alias for the named
solver-obligation form with additive pair estimates.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_source_average_forward_additive_of_solver_obligation_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_source_average_forward_additive_of_solver_obligation_no_top_of_margin

/--
Theorem 3.3 solver source-auto-cap endpoint: public alias deriving the named
solver obligation from the source-average Claim-3.4 bridge, with additive
pair estimates.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_source_average_forward_additive_claim34_solver_obligation_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_source_average_forward_additive_claim34_solver_obligation_no_top_of_margin

/--
Theorem 3.3 solver source-auto-cap endpoint: public alias pairing the
Claim-3.4-discharge additive source-output package with the full
comparison/search IP summaries.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_with_full_ip_summaries_of_source_average_forward_additive_claim34_solver_obligation_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_with_full_ip_summaries_of_source_average_forward_additive_claim34_solver_obligation_no_top_of_margin

/--
Theorem 3.3 solver source-auto-cap endpoint: public alias deriving the named
solver obligation from a source-average exact bounded materialized-allocation
provider, then applying the additive-forward source-output bridge.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_source_average_forward_additive_exact_bounded_supply_allocation_provider_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_source_average_forward_additive_exact_bounded_supply_allocation_provider_no_top_of_margin

/--
Theorem 3.3 solver source-auto-cap endpoint: public alias deriving the named
solver obligation from a source-average exact bounded materialized-allocation
provider and returning additive full-IP summaries, selected-pair forward-ratio
bound, and source-output payload for the same selected search witness.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_source_average_forward_additive_exact_bounded_supply_allocation_provider_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_source_average_forward_additive_exact_bounded_supply_allocation_provider_no_top_of_margin

/--
Theorem 3.3 solver source-auto-cap endpoint: public alias deriving the named
solver obligation from a source-average exact bounded typed high/low allocation
provider, then applying the additive-forward source-output bridge.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_source_average_forward_additive_exact_bounded_typed_combined_high_low_allocation_provider_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_source_average_forward_additive_exact_bounded_typed_combined_high_low_allocation_provider_no_top_of_margin

/--
Theorem 3.3 solver source-auto-cap endpoint: public alias deriving the named
solver obligation from a source-average exact bounded typed high/low allocation
provider and returning additive full-IP summaries, selected-pair forward-ratio
bound, and source-output payload for the same selected search witness.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_source_average_forward_additive_exact_bounded_typed_combined_high_low_allocation_provider_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_source_average_forward_additive_exact_bounded_typed_combined_high_low_allocation_provider_no_top_of_margin

/--
Theorem 3.3 external source-output seam: public alias pairing the exact
bounded materialized-allocation provider additive-forward source-output package
with an externally supplied complexity consequence.
-/
def theorem3_3_external_source_output_ratio_transfer_and_solver_auto_cap_search_of_source_average_forward_additive_exact_bounded_supply_allocation_provider_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_external_source_output_ratio_transfer_and_solver_auto_cap_search_of_source_average_forward_additive_exact_bounded_supply_allocation_provider_no_top_of_margin

/--
Theorem 3.3 external source-output seam: public alias pairing the exact
bounded materialized-allocation provider additive selected-pair full-IP
source-output package with an externally supplied complexity consequence.
-/
def theorem3_3_external_source_output_ratio_transfer_and_solver_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_source_average_forward_additive_exact_bounded_supply_allocation_provider_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_external_source_output_ratio_transfer_and_solver_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_source_average_forward_additive_exact_bounded_supply_allocation_provider_no_top_of_margin

/--
Theorem 3.3 external source-output seam: public alias pairing the exact
bounded typed high/low allocation provider additive-forward source-output
package with an externally supplied complexity consequence.
-/
def theorem3_3_external_source_output_ratio_transfer_and_solver_auto_cap_search_of_source_average_forward_additive_exact_bounded_typed_combined_high_low_allocation_provider_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_external_source_output_ratio_transfer_and_solver_auto_cap_search_of_source_average_forward_additive_exact_bounded_typed_combined_high_low_allocation_provider_no_top_of_margin

/--
Theorem 3.3 external source-output seam: public alias pairing the exact
bounded typed high/low allocation provider additive selected-pair full-IP
source-output package with an externally supplied complexity consequence.
-/
def theorem3_3_external_source_output_ratio_transfer_and_solver_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_source_average_forward_additive_exact_bounded_typed_combined_high_low_allocation_provider_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_external_source_output_ratio_transfer_and_solver_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_source_average_forward_additive_exact_bounded_typed_combined_high_low_allocation_provider_no_top_of_margin

/--
Theorem 3.3 source-auto-cap endpoint: public alias packaging the actual
rounded-average auto-cap search endpoint with the two-scale source-output
bridge.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_actual_average_auto_cap_search_of_source_average_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_actual_average_auto_cap_search_of_source_average_no_top_of_margin

/--
Theorem 3.3 actual-average source-auto-cap endpoint: public alias consuming
additive pair estimates for the generated feasible pair.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_actual_average_auto_cap_search_of_source_average_forward_additive_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_actual_average_auto_cap_search_of_source_average_forward_additive_no_top_of_margin

/--
Theorem 3.3 actual-average source-auto-cap endpoint: public alias pairing the
actual-average full-IP summary with the generic source-average source-output
package.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_actual_average_auto_cap_search_with_full_ip_summaries_of_source_average_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_actual_average_auto_cap_search_with_full_ip_summaries_of_source_average_no_top_of_margin

/--
Theorem 3.3 actual-average source-auto-cap endpoint: public alias returning
the full-IP summary, selected-pair forward-ratio bound, and source-output
payload for the same selected search witness.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_actual_average_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_source_average_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_actual_average_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_source_average_no_top_of_margin

/--
Theorem 3.3 actual-average source-auto-cap endpoint: public alias pairing the
actual-average full-IP summary with the additive-forward generic
source-average source-output package.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_actual_average_auto_cap_search_with_full_ip_summaries_of_source_average_forward_additive_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_actual_average_auto_cap_search_with_full_ip_summaries_of_source_average_forward_additive_no_top_of_margin

/--
Theorem 3.3 actual-average source-auto-cap endpoint: public alias returning
the full-IP summary, selected-pair forward-ratio bound, and source-output
payload using additive pair estimates for the generated feasible pair.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_actual_average_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_source_average_forward_additive_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_actual_average_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_source_average_forward_additive_no_top_of_margin

/--
Theorem 3.3 source-auto-cap endpoint: public alias consuming a Claim 3.4
bounded-optimum certificate and packaging the source-average auto-cap search
with the two-scale source-output bridge.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_auto_cap_search_of_claim_3_4_source_average_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_auto_cap_search_of_claim_3_4_source_average_no_top_of_margin

/--
Theorem 3.3 solver source-auto-cap endpoint: public alias consuming a
Claim 3.4 bounded-optimum certificate while keeping the scalar forward
comparison for the solver pair explicit.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_claim_3_4_source_average_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_claim_3_4_source_average_no_top_of_margin

/--
Theorem 3.3 solver source-auto-cap endpoint: public alias for the Claim-3.4
named solver-obligation form with scalar forward comparison.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_claim_3_4_source_average_of_solver_obligation_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_claim_3_4_source_average_of_solver_obligation_no_top_of_margin

/--
Theorem 3.3 solver source-auto-cap endpoint: public alias returning the Claim
3.4 named-obligation full-IP summary, selected-pair forward-ratio bound, and
source-output payload for the same selected search witness.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_claim_3_4_source_average_of_solver_obligation_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_claim_3_4_source_average_of_solver_obligation_no_top_of_margin

/--
Theorem 3.3 solver source-auto-cap endpoint: public alias deriving the named
solver obligation from the source-average Claim-3.4 bridge, with a Claim 3.4
bounded-optimum certificate and scalar forward comparison.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_claim_3_4_source_average_claim34_solver_obligation_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_claim_3_4_source_average_claim34_solver_obligation_no_top_of_margin

/--
Theorem 3.3 solver source-auto-cap endpoint: public alias pairing the
Claim-3.4-discharge Claim-3.4 scalar source-output package with the full
comparison/search IP summaries.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_with_full_ip_summaries_of_claim_3_4_source_average_claim34_solver_obligation_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_with_full_ip_summaries_of_claim_3_4_source_average_claim34_solver_obligation_no_top_of_margin

/--
Theorem 3.3 solver source-auto-cap endpoint: public alias returning the
Claim-3.4-discharge Claim-3.4 full-IP summary, selected-pair forward-ratio
bound, and source-output payload for the same selected search witness.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_claim_3_4_source_average_claim34_solver_obligation_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_claim_3_4_source_average_claim34_solver_obligation_no_top_of_margin

/--
Theorem 3.3 external solver consequence endpoint: public alias pairing the
strongest Claim-3.4 scalar selected-pair/full-IP source-output package with an
abstract external solver consequence.
-/
def theorem3_3_external_solver_consequence_and_selected_pair_full_summary_source_output_of_claim_3_4_source_average_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_external_solver_consequence_and_selected_pair_full_summary_source_output_of_claim_3_4_source_average_no_top_of_margin

/--
Theorem 3.3 external source-output seam: public alias pairing the Claim-3.4
source-average scalar-forward source-output package with an externally supplied
complexity consequence.
-/
def theorem3_3_external_source_output_ratio_transfer_and_solver_auto_cap_search_of_claim_3_4_source_average_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_external_source_output_ratio_transfer_and_solver_auto_cap_search_of_claim_3_4_source_average_no_top_of_margin

/--
Theorem 3.3 external source-output seam: public alias pairing the Claim-3.4
source-average selected-pair full-IP source-output package with an externally
supplied complexity consequence.
-/
def theorem3_3_external_source_output_ratio_transfer_and_solver_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_claim_3_4_source_average_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_external_source_output_ratio_transfer_and_solver_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_claim_3_4_source_average_no_top_of_margin

/--
Theorem 3.3 solver source-auto-cap endpoint: public alias deriving the named
solver obligation from a source-average exact bounded materialized-allocation
provider, with a Claim 3.4 bounded-optimum certificate.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_claim_3_4_source_average_exact_bounded_supply_allocation_provider_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_claim_3_4_source_average_exact_bounded_supply_allocation_provider_no_top_of_margin

/--
Theorem 3.3 solver source-auto-cap endpoint: public alias deriving the named
solver obligation from a source-average exact bounded materialized-allocation
provider, with a Claim 3.4 bounded-optimum certificate, and returning full IP
summaries, selected-pair forward-ratio bound, and source-output payload for the
same selected search witness.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_claim_3_4_source_average_exact_bounded_supply_allocation_provider_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_claim_3_4_source_average_exact_bounded_supply_allocation_provider_no_top_of_margin

/--
Theorem 3.3 solver source-auto-cap endpoint: public alias deriving the named
solver obligation from a source-average exact bounded typed high/low allocation
provider, with a Claim 3.4 bounded-optimum certificate.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_claim_3_4_source_average_exact_bounded_typed_combined_high_low_allocation_provider_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_claim_3_4_source_average_exact_bounded_typed_combined_high_low_allocation_provider_no_top_of_margin

/--
Theorem 3.3 solver source-auto-cap endpoint: public alias deriving the named
solver obligation from a source-average exact bounded typed high/low allocation
provider, with a Claim 3.4 bounded-optimum certificate, and returning full IP
summaries, selected-pair forward-ratio bound, and source-output payload for the
same selected search witness.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_claim_3_4_source_average_exact_bounded_typed_combined_high_low_allocation_provider_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_claim_3_4_source_average_exact_bounded_typed_combined_high_low_allocation_provider_no_top_of_margin

/--
Theorem 3.3 solver source-auto-cap endpoint: public alias consuming a
Claim 3.4 bounded-optimum certificate and additive pair estimates for the
solver pair's scalar forward continuation.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_claim_3_4_source_average_forward_additive_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_claim_3_4_source_average_forward_additive_no_top_of_margin

/--
Theorem 3.3 solver source-auto-cap endpoint: public alias for the Claim-3.4
named solver-obligation form with additive pair estimates.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_claim_3_4_source_average_forward_additive_of_solver_obligation_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_claim_3_4_source_average_forward_additive_of_solver_obligation_no_top_of_margin

/--
Theorem 3.3 solver source-auto-cap endpoint: public alias for the Claim-3.4
named solver-obligation additive full-IP summary, selected-pair forward-ratio
bound, and source-output payload for the same selected search witness.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_claim_3_4_source_average_forward_additive_of_solver_obligation_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_claim_3_4_source_average_forward_additive_of_solver_obligation_no_top_of_margin

/--
Theorem 3.3 solver source-auto-cap endpoint: public alias deriving the named
solver obligation from the source-average Claim-3.4 bridge, with a Claim 3.4
bounded-optimum certificate and additive pair estimates.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_claim_3_4_source_average_forward_additive_claim34_solver_obligation_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_claim_3_4_source_average_forward_additive_claim34_solver_obligation_no_top_of_margin

/--
Theorem 3.3 solver source-auto-cap endpoint: public alias pairing the
Claim-3.4-discharge Claim-3.4 additive source-output package with the full
comparison/search IP summaries.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_with_full_ip_summaries_of_claim_3_4_source_average_forward_additive_claim34_solver_obligation_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_with_full_ip_summaries_of_claim_3_4_source_average_forward_additive_claim34_solver_obligation_no_top_of_margin

/--
Theorem 3.3 solver source-auto-cap endpoint: public alias returning the
Claim-3.4-discharge additive full-IP summary, selected-pair forward-ratio
bound, and source-output payload for the same selected search witness.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_claim_3_4_source_average_forward_additive_claim34_solver_obligation_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_claim_3_4_source_average_forward_additive_claim34_solver_obligation_no_top_of_margin

/--
Theorem 3.3 external solver consequence endpoint: public alias pairing the
strongest Claim-3.4 additive selected-pair/full-IP source-output package with
an abstract external solver consequence.
-/
def theorem3_3_external_solver_consequence_and_selected_pair_full_summary_source_output_of_claim_3_4_source_average_forward_additive_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_external_solver_consequence_and_selected_pair_full_summary_source_output_of_claim_3_4_source_average_forward_additive_no_top_of_margin

/--
Theorem 3.3 external source-output seam: public alias pairing the Claim-3.4
source-average additive-forward source-output package with an externally
supplied complexity consequence.
-/
def theorem3_3_external_source_output_ratio_transfer_and_solver_auto_cap_search_of_claim_3_4_source_average_forward_additive_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_external_source_output_ratio_transfer_and_solver_auto_cap_search_of_claim_3_4_source_average_forward_additive_no_top_of_margin

/--
Theorem 3.3 external source-output seam: public alias pairing the Claim-3.4
source-average additive selected-pair full-IP source-output package with an
externally supplied complexity consequence.
-/
def theorem3_3_external_source_output_ratio_transfer_and_solver_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_claim_3_4_source_average_forward_additive_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_external_source_output_ratio_transfer_and_solver_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_claim_3_4_source_average_forward_additive_no_top_of_margin

/--
Theorem 3.3 solver source-auto-cap endpoint: public alias deriving the named
solver obligation from a source-average exact bounded materialized-allocation
provider, with Claim 3.4 and additive pair estimates.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_claim_3_4_source_average_forward_additive_exact_bounded_supply_allocation_provider_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_claim_3_4_source_average_forward_additive_exact_bounded_supply_allocation_provider_no_top_of_margin

/--
Theorem 3.3 solver source-auto-cap endpoint: public alias deriving the named
solver obligation from a source-average exact bounded materialized-allocation
provider, with Claim 3.4, and returning additive full-IP summaries,
selected-pair forward-ratio bound, and source-output payload.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_claim_3_4_source_average_forward_additive_exact_bounded_supply_allocation_provider_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_claim_3_4_source_average_forward_additive_exact_bounded_supply_allocation_provider_no_top_of_margin

/--
Theorem 3.3 solver source-auto-cap endpoint: public alias deriving the named
solver obligation from a source-average exact bounded typed high/low allocation
provider, with Claim 3.4 and additive pair estimates.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_claim_3_4_source_average_forward_additive_exact_bounded_typed_combined_high_low_allocation_provider_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_of_claim_3_4_source_average_forward_additive_exact_bounded_typed_combined_high_low_allocation_provider_no_top_of_margin

/--
Theorem 3.3 solver source-auto-cap endpoint: public alias deriving the named
solver obligation from a source-average exact bounded typed high/low allocation
provider, with Claim 3.4, and returning additive full-IP summaries,
selected-pair forward-ratio bound, and source-output payload.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_claim_3_4_source_average_forward_additive_exact_bounded_typed_combined_high_low_allocation_provider_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_solver_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_claim_3_4_source_average_forward_additive_exact_bounded_typed_combined_high_low_allocation_provider_no_top_of_margin

/--
Theorem 3.3 source-auto-cap endpoint: public alias consuming a Claim 3.4
bounded-optimum certificate and additive pair estimates for the remaining
scalar forward continuation.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_auto_cap_search_of_claim_3_4_source_average_forward_additive_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_auto_cap_search_of_claim_3_4_source_average_forward_additive_no_top_of_margin

/--
Theorem 3.3 actual-average source-auto-cap endpoint: public alias consuming a
Claim 3.4 bounded-optimum certificate and packaging the generated rounded
average with the two-scale source-output bridge.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_actual_average_auto_cap_search_of_claim_3_4_source_average_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_actual_average_auto_cap_search_of_claim_3_4_source_average_no_top_of_margin

/--
Theorem 3.3 actual-average source-auto-cap endpoint: public alias consuming a
Claim 3.4 bounded-optimum certificate and additive pair estimates for the
remaining scalar forward continuation.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_actual_average_auto_cap_search_of_claim_3_4_source_average_forward_additive_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_actual_average_auto_cap_search_of_claim_3_4_source_average_forward_additive_no_top_of_margin

/--
Theorem 3.3 actual-average source-auto-cap endpoint: public alias pairing the
actual-average full-IP summary with the Claim-3.4 source-output package.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_actual_average_auto_cap_search_with_full_ip_summaries_of_claim_3_4_source_average_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_actual_average_auto_cap_search_with_full_ip_summaries_of_claim_3_4_source_average_no_top_of_margin

/--
Theorem 3.3 actual-average source-auto-cap endpoint: public alias returning
the Claim-3.4 full-IP summary, selected-pair forward-ratio bound, and
source-output payload for the same selected search witness.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_actual_average_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_claim_3_4_source_average_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_actual_average_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_claim_3_4_source_average_no_top_of_margin

/--
Theorem 3.3 actual-average source-auto-cap endpoint: public alias pairing the
actual-average full-IP summary with the additive-forward Claim-3.4
source-output package.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_actual_average_auto_cap_search_with_full_ip_summaries_of_claim_3_4_source_average_forward_additive_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_actual_average_auto_cap_search_with_full_ip_summaries_of_claim_3_4_source_average_forward_additive_no_top_of_margin

/--
Theorem 3.3 actual-average source-auto-cap endpoint: public alias returning
the Claim-3.4 full-IP summary, selected-pair forward-ratio bound, and
source-output payload using additive pair estimates for the generated feasible
pair.
-/
def theorem3_3_exists_source_output_ratio_transfer_and_actual_average_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_claim_3_4_source_average_forward_additive_no_top_of_margin :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_source_output_ratio_transfer_and_actual_average_auto_cap_search_with_selected_pair_forward_ratio_and_full_ip_summaries_of_claim_3_4_source_average_forward_additive_no_top_of_margin

/--
Theorem 3.3 solver auto-cap workload summary: public alias for the
solver-provided capped IP/search workload payload before adjoining the final
rounded-instance guarantee.
-/
def theorem3_3_solver_auto_cap_workload_summary_exists :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_solver_workload_summary_with_source_auto_cap_no_top_of_margin

/--
Theorem 3.3 solver auto-cap workload summary: public alias for the named
solver-obligation form of the finite workload payload.
-/
def theorem3_3_solver_auto_cap_workload_summary_exists_of_solver_obligation :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_solver_workload_summary_with_source_auto_cap_of_solver_obligation_no_top_of_margin

/--
Theorem 3.3 solver auto-cap workload summary from exact allocations: public
alias for the source-average bounded materialized-allocation-provider wrapper.
-/
def theorem3_3_solver_auto_cap_workload_summary_exists_of_source_average_exact_bounded_supply_allocation_provider :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_solver_workload_summary_with_source_auto_cap_of_source_average_exact_bounded_supply_allocation_provider_no_top_of_margin

/--
Theorem 3.3 solver auto-cap workload summary from typed exact allocations:
public alias for the source-average bounded typed-combined-allocation-provider
wrapper.
-/
def theorem3_3_solver_auto_cap_workload_summary_exists_of_source_average_exact_bounded_typed_combined_high_low_allocation_provider :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_solver_workload_summary_with_source_auto_cap_of_source_average_exact_bounded_typed_combined_high_low_allocation_provider_no_top_of_margin

/--
Theorem 3.3 solver auto-cap workload summary from Claim 3.4: public alias
discharging the named source-auto-cap solver obligation from source-average
high/low hypotheses.
-/
def theorem3_3_solver_auto_cap_workload_summary_exists_of_source_average_claim34 :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_solver_workload_summary_with_source_auto_cap_of_source_average_claim34_no_top_of_margin

/--
Theorem 3.3 solver auto-cap workload ratio endpoint: assuming the supplied
rounded-average identity and solver premise, a capped comparison IP induces
explicit finite-workload bounds together with the final rounded-instance
guarantee.
-/
def theorem3_3_solver_auto_cap_workload_ratio_endpoint
    {SourceAgent SourceItem Alloc : Type*}
    [Fintype SourceAgent] [Nonempty SourceAgent] [DecidableEq SourceItem]
    {M : Theorem33.IdenticalUtilitiesModel SourceAgent SourceItem Alloc}
    {L LR epsilon : ℝ} {lambda : ℕ} {optimal : Alloc}
    (hepsilon_pos : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1)
    (cert : Theorem33.RoundedInstanceSearchCertificate M L epsilon lambda optimal)
    (highGoods lowGoods : Finset SourceItem) (v : SourceItem → ℝ)
    (hlambda : 1 < lambda) (hL : 0 < L)
    (hhigh :
      ∀ g : SourceItem, g ∈ highGoods →
        L / (lambda : ℝ) < v g ∧ v g < L)
    (hlow :
      ∀ g : SourceItem, g ∈ lowGoods →
        0 ≤ v g ∧ v g < L / (lambda : ℝ))
    (hmargin :
      ∀ g : SourceItem, g ∈ highGoods →
        v g + L / ((lambda : ℝ) ^ 2) ≤ L)
    (haverage :
      ∀ (indexOf : SourceItem → Theorem33.RoundedValueIndex lambda)
        (combinedSupply : Theorem33.RoundedValueIndex lambda → ℕ),
        (∀ g : SourceItem, g ∈ highGoods →
          v g ≤ Theorem33.roundedValue L lambda (indexOf g) ∧
            Theorem33.roundedValue L lambda (indexOf g) <
              v g + L / ((lambda : ℝ) ^ 2)) →
        (∀ k : Theorem33.RoundedValueIndex lambda,
          combinedSupply k =
            paper_lmms_theorem_3_3_roundedGoodsSupplyOfGoods indexOf highGoods k +
              Theorem33.lowGoodsAggregatedSupply L lambda (lowGoods.sum v) k) →
        (∑ k : Theorem33.RoundedValueIndex lambda,
            (combinedSupply k : ℝ) * Theorem33.roundedValue L lambda k) =
          (Fintype.card SourceAgent : ℝ) * LR)
    (solver :
      ∀ (indexOf : SourceItem → Theorem33.RoundedValueIndex lambda)
        (combinedSupply : Theorem33.RoundedValueIndex lambda → ℕ),
        (∀ g : SourceItem, g ∈ highGoods →
          v g ≤ Theorem33.roundedValue L lambda (indexOf g) ∧
            Theorem33.roundedValue L lambda (indexOf g) <
              v g + L / ((lambda : ℝ) ^ 2)) →
        (∀ k : Theorem33.RoundedValueIndex lambda,
          combinedSupply k =
            paper_lmms_theorem_3_3_roundedGoodsSupplyOfGoods indexOf highGoods k +
              Theorem33.lowGoodsAggregatedSupply L lambda (lowGoods.sum v) k) →
        combinedSupply (paper_lmms_theorem_3_3_topRoundedValueIndex lambda) = 0 →
        (∑ k : Theorem33.RoundedValueIndex lambda,
            (combinedSupply k : ℝ) * Theorem33.roundedValue L lambda k) =
          (Fintype.card SourceAgent : ℝ) * LR →
        ∃ p : ℝ × ℝ,
          Nonempty
            (Theorem33.RoundedConcreteIPCertificateWithCap
              L LR lambda
                (paper_lmms_theorem_3_3_capCountForAverage
                  L
                    (L +
                      (((Fintype.card SourceAgent : ℝ) + 1) *
                          (L / (lambda : ℝ))) /
                        (Fintype.card SourceAgent : ℝ))
                  lambda)
              SourceAgent p combinedSupply)) :=
  LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_solver_workload_summary_with_source_auto_cap_ratio_guarantee_no_top_of_margin
    hepsilon_pos hepsilon_le_one cert highGoods lowGoods v hlambda hL
    hhigh hlow hmargin haverage solver

/--
Theorem 3.3 solver auto-cap workload ratio endpoint from exact allocations:
public alias for the source-average bounded materialized-allocation-provider
ratio wrapper.
-/
def theorem3_3_solver_auto_cap_workload_ratio_endpoint_of_source_average_exact_bounded_supply_allocation_provider :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_solver_workload_summary_with_source_auto_cap_ratio_guarantee_of_source_average_exact_bounded_supply_allocation_provider_no_top_of_margin

/--
Theorem 3.3 solver auto-cap workload ratio endpoint from typed exact
allocations: public alias for the source-average bounded
typed-combined-allocation-provider ratio wrapper.
-/
def theorem3_3_solver_auto_cap_workload_ratio_endpoint_of_source_average_exact_bounded_typed_combined_high_low_allocation_provider :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_solver_workload_summary_with_source_auto_cap_ratio_guarantee_of_source_average_exact_bounded_typed_combined_high_low_allocation_provider_no_top_of_margin

/--
Theorem 3.3 solver auto-cap workload ratio endpoint from Claim 3.4: public
alias discharging the named source-auto-cap solver obligation internally.
-/
def theorem3_3_solver_auto_cap_workload_ratio_endpoint_of_source_average_claim34 :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_solver_workload_summary_with_source_auto_cap_ratio_guarantee_of_source_average_claim34_no_top_of_margin

/--
Theorem 3.3 solver auto-cap workload summary with ratio guarantee: public
summary-named alias of the workload ratio endpoint.
-/
def theorem3_3_solver_auto_cap_workload_summary_with_ratio_guarantee :=
  @theorem3_3_solver_auto_cap_workload_ratio_endpoint

/--
Theorem 3.3 solver auto-cap workload ratio endpoint: public alias for the
named solver-obligation form.
-/
def theorem3_3_solver_auto_cap_workload_ratio_endpoint_of_solver_obligation :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_solver_workload_summary_with_source_auto_cap_ratio_guarantee_of_solver_obligation_no_top_of_margin

/--
Theorem 3.3 solver auto-cap full-IP-constraint summary: public alias for the
solver-produced capped IP constraints and chosen search-IP constraints before
adjoining the final rounded-instance guarantee.
-/
def theorem3_3_solver_auto_cap_full_ip_constraint_summary_exists :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_solver_full_ip_constraint_summary_with_source_auto_cap_no_top_of_margin

/--
Theorem 3.3 solver auto-cap full-IP-constraint summary: public alias for the
named solver-obligation form.
-/
def theorem3_3_solver_auto_cap_full_ip_constraint_summary_exists_of_solver_obligation :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_solver_full_ip_constraint_summary_with_source_auto_cap_of_solver_obligation_no_top_of_margin

/--
Theorem 3.3 solver auto-cap full-IP-constraint summary from exact allocations:
public alias for the source-average bounded materialized-allocation-provider
wrapper.
-/
def theorem3_3_solver_auto_cap_full_ip_constraint_summary_exists_of_source_average_exact_bounded_supply_allocation_provider :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_solver_full_ip_constraint_summary_with_source_auto_cap_of_source_average_exact_bounded_supply_allocation_provider_no_top_of_margin

/--
Theorem 3.3 solver auto-cap full-IP-constraint summary from typed exact
allocations: public alias for the source-average bounded
typed-combined-allocation-provider wrapper.
-/
def theorem3_3_solver_auto_cap_full_ip_constraint_summary_exists_of_source_average_exact_bounded_typed_combined_high_low_allocation_provider :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_solver_full_ip_constraint_summary_with_source_auto_cap_of_source_average_exact_bounded_typed_combined_high_low_allocation_provider_no_top_of_margin

/--
Theorem 3.3 solver auto-cap full-IP-constraint summary from Claim 3.4:
public alias discharging the named source-auto-cap solver obligation
internally.
-/
def theorem3_3_solver_auto_cap_full_ip_constraint_summary_exists_of_source_average_claim34 :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_solver_full_ip_constraint_summary_with_source_auto_cap_of_source_average_claim34_no_top_of_margin

/--
Theorem 3.3 solver auto-cap full-IP-constraint ratio endpoint: assuming the
supplied rounded-average identity and solver premise, exposes the
solver-produced capped IP constraints and the chosen search-IP constraints
together with the final rounded-instance guarantee.
-/
def theorem3_3_solver_auto_cap_full_ip_constraint_ratio_endpoint
    {SourceAgent SourceItem Alloc : Type*}
    [Fintype SourceAgent] [Nonempty SourceAgent] [DecidableEq SourceItem]
    {M : Theorem33.IdenticalUtilitiesModel SourceAgent SourceItem Alloc}
    {L LR epsilon : ℝ} {lambda : ℕ} {optimal : Alloc}
    (hepsilon_pos : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1)
    (cert : Theorem33.RoundedInstanceSearchCertificate M L epsilon lambda optimal)
    (highGoods lowGoods : Finset SourceItem) (v : SourceItem → ℝ)
    (hlambda : 1 < lambda) (hL : 0 < L)
    (hhigh :
      ∀ g : SourceItem, g ∈ highGoods →
        L / (lambda : ℝ) < v g ∧ v g < L)
    (hlow :
      ∀ g : SourceItem, g ∈ lowGoods →
        0 ≤ v g ∧ v g < L / (lambda : ℝ))
    (hmargin :
      ∀ g : SourceItem, g ∈ highGoods →
        v g + L / ((lambda : ℝ) ^ 2) ≤ L)
    (haverage :
      ∀ (indexOf : SourceItem → Theorem33.RoundedValueIndex lambda)
        (combinedSupply : Theorem33.RoundedValueIndex lambda → ℕ),
        (∀ g : SourceItem, g ∈ highGoods →
          v g ≤ Theorem33.roundedValue L lambda (indexOf g) ∧
            Theorem33.roundedValue L lambda (indexOf g) <
              v g + L / ((lambda : ℝ) ^ 2)) →
        (∀ k : Theorem33.RoundedValueIndex lambda,
          combinedSupply k =
            paper_lmms_theorem_3_3_roundedGoodsSupplyOfGoods indexOf highGoods k +
              Theorem33.lowGoodsAggregatedSupply L lambda (lowGoods.sum v) k) →
        (∑ k : Theorem33.RoundedValueIndex lambda,
            (combinedSupply k : ℝ) * Theorem33.roundedValue L lambda k) =
          (Fintype.card SourceAgent : ℝ) * LR)
    (solver :
      ∀ (indexOf : SourceItem → Theorem33.RoundedValueIndex lambda)
        (combinedSupply : Theorem33.RoundedValueIndex lambda → ℕ),
        (∀ g : SourceItem, g ∈ highGoods →
          v g ≤ Theorem33.roundedValue L lambda (indexOf g) ∧
            Theorem33.roundedValue L lambda (indexOf g) <
              v g + L / ((lambda : ℝ) ^ 2)) →
        (∀ k : Theorem33.RoundedValueIndex lambda,
          combinedSupply k =
            paper_lmms_theorem_3_3_roundedGoodsSupplyOfGoods indexOf highGoods k +
              Theorem33.lowGoodsAggregatedSupply L lambda (lowGoods.sum v) k) →
        combinedSupply (paper_lmms_theorem_3_3_topRoundedValueIndex lambda) = 0 →
        (∑ k : Theorem33.RoundedValueIndex lambda,
            (combinedSupply k : ℝ) * Theorem33.roundedValue L lambda k) =
          (Fintype.card SourceAgent : ℝ) * LR →
        ∃ p : ℝ × ℝ,
          Nonempty
            (Theorem33.RoundedConcreteIPCertificateWithCap
              L LR lambda
                (paper_lmms_theorem_3_3_capCountForAverage
                  L
                    (L +
                      (((Fintype.card SourceAgent : ℝ) + 1) *
                          (L / (lambda : ℝ))) /
                        (Fintype.card SourceAgent : ℝ))
                  lambda)
              SourceAgent p combinedSupply)) :=
  LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_solver_full_ip_constraint_summary_with_ratio_guarantee_and_source_auto_cap_no_top_of_margin
    hepsilon_pos hepsilon_le_one cert highGoods lowGoods v hlambda hL
    hhigh hlow hmargin haverage solver

/--
Theorem 3.3 solver auto-cap full-IP-constraint ratio endpoint from exact
allocations: public alias for the source-average bounded materialized-
allocation-provider wrapper.
-/
def theorem3_3_solver_auto_cap_full_ip_constraint_ratio_endpoint_of_source_average_exact_bounded_supply_allocation_provider :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_solver_full_ip_constraint_summary_with_ratio_guarantee_of_source_average_exact_bounded_supply_allocation_provider_no_top_of_margin

/--
Theorem 3.3 solver auto-cap full-IP-constraint ratio endpoint from typed exact
allocations: public alias for the source-average bounded
typed-combined-allocation-provider wrapper.
-/
def theorem3_3_solver_auto_cap_full_ip_constraint_ratio_endpoint_of_source_average_exact_bounded_typed_combined_high_low_allocation_provider :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_solver_full_ip_constraint_summary_with_ratio_guarantee_of_source_average_exact_bounded_typed_combined_high_low_allocation_provider_no_top_of_margin

/--
Theorem 3.3 solver auto-cap full-IP-constraint ratio endpoint from Claim 3.4:
public alias discharging the named source-auto-cap solver obligation
internally.
-/
def theorem3_3_solver_auto_cap_full_ip_constraint_ratio_endpoint_of_source_average_claim34 :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_solver_full_ip_constraint_summary_with_ratio_guarantee_and_source_auto_cap_of_source_average_claim34_no_top_of_margin

/--
Theorem 3.3 solver auto-cap full-IP-constraint summary with ratio guarantee:
public summary-named alias of the full-IP-constraint ratio endpoint.
-/
def theorem3_3_solver_auto_cap_full_ip_constraint_summary_with_ratio_guarantee :=
  @theorem3_3_solver_auto_cap_full_ip_constraint_ratio_endpoint

/--
Theorem 3.3 solver auto-cap full-IP-constraint ratio endpoint: public alias
for the named solver-obligation form.
-/
def theorem3_3_solver_auto_cap_full_ip_constraint_ratio_endpoint_of_solver_obligation :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_solver_full_ip_constraint_summary_with_ratio_guarantee_and_source_auto_cap_of_solver_obligation_no_top_of_margin

/--
Theorem 3.3 solver auto-cap interface: conditional on the supplied
rounded-average identity and solver premise, a capped comparison IP for the
rounded high/low supply induces bounded capped IP/search witnesses and the
final rounded-instance `(1 + epsilon)` ratio guarantee.
-/
theorem theorem3_3_solver_auto_cap_full_ip_summary_with_ratio_guarantee
    {SourceAgent SourceItem Alloc : Type*}
    [Fintype SourceAgent] [Nonempty SourceAgent] [DecidableEq SourceItem]
    {M : Theorem33.IdenticalUtilitiesModel SourceAgent SourceItem Alloc}
    {L LR epsilon : ℝ} {lambda : ℕ} {optimal : Alloc}
    (hepsilon_pos : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1)
    (cert : Theorem33.RoundedInstanceSearchCertificate M L epsilon lambda optimal)
    (highGoods lowGoods : Finset SourceItem) (v : SourceItem → ℝ)
    (hlambda : 1 < lambda) (hL : 0 < L)
    (hhigh :
      ∀ g : SourceItem, g ∈ highGoods →
        L / (lambda : ℝ) < v g ∧ v g < L)
    (hlow :
      ∀ g : SourceItem, g ∈ lowGoods →
        0 ≤ v g ∧ v g < L / (lambda : ℝ))
    (hmargin :
      ∀ g : SourceItem, g ∈ highGoods →
        v g + L / ((lambda : ℝ) ^ 2) ≤ L)
    (haverage :
      ∀ (indexOf : SourceItem → Theorem33.RoundedValueIndex lambda)
        (combinedSupply : Theorem33.RoundedValueIndex lambda → ℕ),
        (∀ g : SourceItem, g ∈ highGoods →
          v g ≤ Theorem33.roundedValue L lambda (indexOf g) ∧
            Theorem33.roundedValue L lambda (indexOf g) <
              v g + L / ((lambda : ℝ) ^ 2)) →
        (∀ k : Theorem33.RoundedValueIndex lambda,
          combinedSupply k =
            paper_lmms_theorem_3_3_roundedGoodsSupplyOfGoods indexOf highGoods k +
              Theorem33.lowGoodsAggregatedSupply L lambda (lowGoods.sum v) k) →
        (∑ k : Theorem33.RoundedValueIndex lambda,
            (combinedSupply k : ℝ) * Theorem33.roundedValue L lambda k) =
          (Fintype.card SourceAgent : ℝ) * LR)
    (solver :
      ∀ (indexOf : SourceItem → Theorem33.RoundedValueIndex lambda)
        (combinedSupply : Theorem33.RoundedValueIndex lambda → ℕ),
        (∀ g : SourceItem, g ∈ highGoods →
          v g ≤ Theorem33.roundedValue L lambda (indexOf g) ∧
            Theorem33.roundedValue L lambda (indexOf g) <
              v g + L / ((lambda : ℝ) ^ 2)) →
        (∀ k : Theorem33.RoundedValueIndex lambda,
          combinedSupply k =
            paper_lmms_theorem_3_3_roundedGoodsSupplyOfGoods indexOf highGoods k +
              Theorem33.lowGoodsAggregatedSupply L lambda (lowGoods.sum v) k) →
        combinedSupply (paper_lmms_theorem_3_3_topRoundedValueIndex lambda) = 0 →
        (∑ k : Theorem33.RoundedValueIndex lambda,
            (combinedSupply k : ℝ) * Theorem33.roundedValue L lambda k) =
          (Fintype.card SourceAgent : ℝ) * LR →
        ∃ p : ℝ × ℝ,
          Nonempty
            (Theorem33.RoundedConcreteIPCertificateWithCap
              L LR lambda
                (paper_lmms_theorem_3_3_capCountForAverage
                  L
                    (L +
                      (((Fintype.card SourceAgent : ℝ) + 1) *
                          (L / (lambda : ℝ))) /
                        (Fintype.card SourceAgent : ℝ))
                  lambda)
              SourceAgent p combinedSupply)) :
    ∃ maxCount : ℕ,
      maxCount ≤ 2 * lambda + 4 ∧
        (Theorem33.roundedAdmissibleTypeSetWithCap
            L LR lambda maxCount).card ≤
          (2 * lambda + 5) ^
            Fintype.card (Theorem33.RoundedValueIndex lambda) ∧
          (Theorem33.roundedAdmissibleValuePairSetWithCap
              L LR lambda maxCount).card ≤
            ((2 * lambda + 5) ^
              Fintype.card (Theorem33.RoundedValueIndex lambda)) ^ 2 ∧
            ∃ indexOf : SourceItem → Theorem33.RoundedValueIndex lambda,
              ∃ combinedSupply : Theorem33.RoundedValueIndex lambda → ℕ,
                ∃ p : ℝ × ℝ,
                  ∃ ip :
                    Theorem33.RoundedConcreteIPCertificateWithCap
                      L LR lambda maxCount SourceAgent p combinedSupply,
                    ∃ search :
                      Theorem33.RoundedValuePairSearchCertificateWithCap
                        L LR lambda maxCount SourceAgent combinedSupply,
                      Theorem33.allocationLoadRatio M cert.output ≤
                          Theorem33.allocationLoadRatio M optimal *
                            (1 + epsilon) ∧
                        Theorem33.roundedValuePairRatio search.chosenPair ≤
                          Theorem33.roundedValuePairRatio p ∧
                          p ∈
                            Theorem33.roundedAdmissibleValuePairSetWithCap
                              L LR lambda maxCount ∧
                            (Theorem33.roundedTypesInValueWindowWithCap
                                L LR lambda maxCount p.1 p.2).card ≤
                              (2 * lambda + 5) ^
                                Fintype.card
                                  (Theorem33.RoundedValueIndex lambda) ∧
                              (∀ t : Theorem33.RoundedBundleType lambda,
                                t ∉
                                  Theorem33.roundedTypesInValueWindowWithCap
                                    L LR lambda maxCount p.1 p.2 →
                                  ip.typeMultiplicity t = 0) ∧
                                (Theorem33.roundedTypesInValueWindowWithCap
                                    L LR lambda maxCount p.1 p.2).sum
                                  ip.typeMultiplicity =
                                    Fintype.card SourceAgent ∧
                                  (∀ k : Theorem33.RoundedValueIndex lambda,
                                    (Theorem33.roundedTypesInValueWindowWithCap
                                        L LR lambda maxCount p.1 p.2).sum
                                      (fun t =>
                                        ip.typeMultiplicity t * t.count k) =
                                      combinedSupply k) ∧
                                    search.chosenPair ∈
                                      Theorem33.roundedAdmissibleValuePairSetWithCap
                                        L LR lambda maxCount ∧
                                      (Theorem33.roundedTypesInValueWindowWithCap
                                          L LR lambda maxCount
                                            search.chosenPair.1
                                            search.chosenPair.2).card ≤
                                        (2 * lambda + 5) ^
                                          Fintype.card
                                            (Theorem33.RoundedValueIndex
                                              lambda) ∧
                                        (∀ t :
                                          Theorem33.RoundedBundleType lambda,
                                          t ∉
                                            Theorem33.roundedTypesInValueWindowWithCap
                                              L LR lambda maxCount
                                                search.chosenPair.1
                                                search.chosenPair.2 →
                                            search.chosenIP.typeMultiplicity t =
                                              0) ∧
                                          (Theorem33.roundedTypesInValueWindowWithCap
                                              L LR lambda maxCount
                                                search.chosenPair.1
                                                search.chosenPair.2).sum
                                            search.chosenIP.typeMultiplicity =
                                              Fintype.card SourceAgent ∧
                                            (∀ k :
                                              Theorem33.RoundedValueIndex
                                                lambda,
                                              (Theorem33.roundedTypesInValueWindowWithCap
                                                  L LR lambda maxCount
                                                    search.chosenPair.1
                                                    search.chosenPair.2).sum
                                                (fun t =>
                                                  search.chosenIP.typeMultiplicity
                                                      t *
                                                    t.count k) =
                                                combinedSupply k) ∧
                                              (∀ g : SourceItem,
                                                g ∈ highGoods →
                                                  v g ≤
                                                      Theorem33.roundedValue L
                                                        lambda (indexOf g) ∧
                                                    Theorem33.roundedValue L
                                                        lambda (indexOf g) <
                                                      v g +
                                                        L /
                                                          ((lambda : ℝ) ^ 2)) ∧
                                                (∀ k :
                                                  Theorem33.RoundedValueIndex
                                                    lambda,
                                                  combinedSupply k =
                                                    paper_lmms_theorem_3_3_roundedGoodsSupplyOfGoods
                                                        indexOf highGoods k +
                                                      Theorem33.lowGoodsAggregatedSupply
                                                        L lambda
                                                        (lowGoods.sum v) k) ∧
                                                  combinedSupply
                                                      (paper_lmms_theorem_3_3_topRoundedValueIndex
                                                        lambda) =
                                                    0 := by
  exact
    LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_solver_full_ip_summary_with_ratio_guarantee_and_source_auto_cap_no_top_of_margin
      hepsilon_pos hepsilon_le_one cert highGoods lowGoods v hlambda hL
      hhigh hlow hmargin haverage solver

/--
Theorem 3.3 solver auto-cap full-IP summary from exact allocations: public
alias for the source-average bounded materialized-allocation-provider full-IP
summary wrapper.
-/
def theorem3_3_solver_auto_cap_full_ip_summary_with_ratio_guarantee_of_source_average_exact_bounded_supply_allocation_provider :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_solver_full_ip_summary_with_ratio_guarantee_and_source_auto_cap_of_source_average_exact_bounded_supply_allocation_provider_no_top_of_margin

/--
Theorem 3.3 solver auto-cap full-IP summary from typed exact allocations:
public alias for the source-average bounded typed-combined-allocation-provider
full-IP summary wrapper.
-/
def theorem3_3_solver_auto_cap_full_ip_summary_with_ratio_guarantee_of_source_average_exact_bounded_typed_combined_high_low_allocation_provider :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_solver_full_ip_summary_with_ratio_guarantee_and_source_auto_cap_of_source_average_exact_bounded_typed_combined_high_low_allocation_provider_no_top_of_margin

/--
Theorem 3.3 solver auto-cap full-IP summary from Claim 3.4: public alias
discharging the named source-auto-cap solver obligation internally.
-/
def theorem3_3_solver_auto_cap_full_ip_summary_with_ratio_guarantee_of_source_average_claim34 :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_solver_full_ip_summary_with_ratio_guarantee_and_source_auto_cap_of_source_average_claim34_no_top_of_margin

/--
Theorem 3.3 solver auto-cap full-IP summary: public alias for the named
solver-obligation form.
-/
def theorem3_3_solver_auto_cap_full_ip_summary_with_ratio_guarantee_of_solver_obligation :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_solver_full_ip_summary_with_ratio_guarantee_and_source_auto_cap_of_solver_obligation_no_top_of_margin

/--
Theorem 3.3 solver auto-cap concrete-IP/search full-summary endpoint: public
alias exposing the common capped comparison-IP and selected-search-IP summaries
for the solver-boundary auto-cap payload.
-/
def theorem3_3_solver_auto_cap_concrete_ip_search_full_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_solver_auto_cap_concrete_ip_and_search_full_summary_with_ratio_guarantee_no_top_of_margin

/--
Theorem 3.3 solver auto-cap concrete-IP/search full-summary endpoint: public
alias for the named solver-obligation form.
-/
def theorem3_3_solver_auto_cap_concrete_ip_search_full_summary_ratio_endpoint_of_solver_obligation :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_solver_auto_cap_concrete_ip_and_search_full_summary_with_ratio_guarantee_of_solver_obligation_no_top_of_margin

/--
Theorem 3.3 solver auto-cap concrete-IP/search full-summary endpoint from
exact allocations: public alias for the source-average bounded materialized-
allocation-provider wrapper.
-/
def theorem3_3_solver_auto_cap_concrete_ip_search_full_summary_ratio_endpoint_of_source_average_exact_bounded_supply_allocation_provider :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_solver_auto_cap_concrete_ip_and_search_full_summary_with_ratio_guarantee_of_source_average_exact_bounded_supply_allocation_provider_no_top_of_margin

/--
Theorem 3.3 solver auto-cap concrete-IP/search full-summary endpoint from
typed exact allocations: public alias for the source-average bounded
typed-combined-allocation-provider wrapper.
-/
def theorem3_3_solver_auto_cap_concrete_ip_search_full_summary_ratio_endpoint_of_source_average_exact_bounded_typed_combined_high_low_allocation_provider :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_solver_auto_cap_concrete_ip_and_search_full_summary_with_ratio_guarantee_of_source_average_exact_bounded_typed_combined_high_low_allocation_provider_no_top_of_margin

/--
Theorem 3.3 solver auto-cap concrete-IP/search full-summary endpoint from
Claim 3.4: public alias discharging the named source-auto-cap solver
obligation internally.
-/
def theorem3_3_solver_auto_cap_concrete_ip_search_full_summary_ratio_endpoint_of_source_average_claim34 :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_solver_auto_cap_concrete_ip_and_search_full_summary_with_ratio_guarantee_of_source_average_claim34_no_top_of_margin

/--
Theorem 3.3 solver auto-cap ratio endpoint: compact public alias for the
conditional solver endpoint retaining the final ratio guarantee, capped search
comparison, selected pairs, and rounded source/supply facts under the supplied
rounded-average identity and solver premise.
-/
def theorem3_3_solver_auto_cap_ratio_endpoint
    {SourceAgent SourceItem Alloc : Type*}
    [Fintype SourceAgent] [Nonempty SourceAgent] [DecidableEq SourceItem]
    {M : Theorem33.IdenticalUtilitiesModel SourceAgent SourceItem Alloc}
    {L LR epsilon : ℝ} {lambda : ℕ} {optimal : Alloc}
    (hepsilon_pos : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1)
    (cert : Theorem33.RoundedInstanceSearchCertificate M L epsilon lambda optimal)
    (highGoods lowGoods : Finset SourceItem) (v : SourceItem → ℝ)
    (hlambda : 1 < lambda) (hL : 0 < L)
    (hhigh :
      ∀ g : SourceItem, g ∈ highGoods →
        L / (lambda : ℝ) < v g ∧ v g < L)
    (hlow :
      ∀ g : SourceItem, g ∈ lowGoods →
        0 ≤ v g ∧ v g < L / (lambda : ℝ))
    (hmargin :
      ∀ g : SourceItem, g ∈ highGoods →
        v g + L / ((lambda : ℝ) ^ 2) ≤ L)
    (haverage :
      ∀ (indexOf : SourceItem → Theorem33.RoundedValueIndex lambda)
        (combinedSupply : Theorem33.RoundedValueIndex lambda → ℕ),
        (∀ g : SourceItem, g ∈ highGoods →
          v g ≤ Theorem33.roundedValue L lambda (indexOf g) ∧
            Theorem33.roundedValue L lambda (indexOf g) <
              v g + L / ((lambda : ℝ) ^ 2)) →
        (∀ k : Theorem33.RoundedValueIndex lambda,
          combinedSupply k =
            paper_lmms_theorem_3_3_roundedGoodsSupplyOfGoods indexOf highGoods k +
              Theorem33.lowGoodsAggregatedSupply L lambda (lowGoods.sum v) k) →
        (∑ k : Theorem33.RoundedValueIndex lambda,
            (combinedSupply k : ℝ) * Theorem33.roundedValue L lambda k) =
          (Fintype.card SourceAgent : ℝ) * LR)
    (solver :
      ∀ (indexOf : SourceItem → Theorem33.RoundedValueIndex lambda)
        (combinedSupply : Theorem33.RoundedValueIndex lambda → ℕ),
        (∀ g : SourceItem, g ∈ highGoods →
          v g ≤ Theorem33.roundedValue L lambda (indexOf g) ∧
            Theorem33.roundedValue L lambda (indexOf g) <
              v g + L / ((lambda : ℝ) ^ 2)) →
        (∀ k : Theorem33.RoundedValueIndex lambda,
          combinedSupply k =
            paper_lmms_theorem_3_3_roundedGoodsSupplyOfGoods indexOf highGoods k +
              Theorem33.lowGoodsAggregatedSupply L lambda (lowGoods.sum v) k) →
        combinedSupply (paper_lmms_theorem_3_3_topRoundedValueIndex lambda) = 0 →
        (∑ k : Theorem33.RoundedValueIndex lambda,
            (combinedSupply k : ℝ) * Theorem33.roundedValue L lambda k) =
          (Fintype.card SourceAgent : ℝ) * LR →
        ∃ p : ℝ × ℝ,
          Nonempty
            (Theorem33.RoundedConcreteIPCertificateWithCap
              L LR lambda
                (paper_lmms_theorem_3_3_capCountForAverage
                  L
                    (L +
                      (((Fintype.card SourceAgent : ℝ) + 1) *
                          (L / (lambda : ℝ))) /
                        (Fintype.card SourceAgent : ℝ))
                  lambda)
              SourceAgent p combinedSupply)) :=
  LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_solver_auto_cap_ratio_endpoint_no_top_of_margin
    hepsilon_pos hepsilon_le_one cert highGoods lowGoods v hlambda hL hhigh
    hlow hmargin haverage solver

/--
Theorem 3.3 solver auto-cap ratio endpoint: public alias for the named
solver-obligation form.
-/
def theorem3_3_solver_auto_cap_ratio_endpoint_of_solver_obligation :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_solver_auto_cap_ratio_endpoint_of_solver_obligation_no_top_of_margin

/--
Theorem 3.3 solver auto-cap ratio endpoint from Claim 3.4: public alias
discharging the named source-auto-cap solver obligation internally.
-/
def theorem3_3_solver_auto_cap_ratio_endpoint_of_source_average_claim34 :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_solver_auto_cap_ratio_endpoint_of_source_average_claim34_no_top_of_margin

/--
Theorem 3.3 Claim-3.4 weighted-supply type-assignment/search endpoint:
public alias for the raw no-top weighted-supply witness before adjoining the
final rounded-instance guarantee.
-/
def theorem3_3_claim34_weighted_supply_type_assignment_search_certificate_exists :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_type_assignment_of_claim34_no_top_weighted_supply

/--
Theorem 3.3 Claim-3.4 weighted-supply summary endpoint: public alias exposing
the type assignment, finite-search comparison, and selected-pair admissibility
together.
-/
def theorem3_3_claim34_weighted_supply_type_assignment_summary_exists :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_type_assignment_summary_of_claim34_no_top_weighted_supply

/--
Theorem 3.3 Claim-3.4 weighted-supply ratio endpoint: a no-top weighted
rounded supply yields an uncapped type assignment/search witness and the final
rounded-instance `(1 + epsilon)` ratio guarantee.
-/
def theorem3_3_claim34_weighted_supply_ratio_endpoint
    {SourceAgent SourceItem Alloc : Type*}
    [Fintype SourceAgent] [Nonempty SourceAgent] [DecidableEq SourceAgent]
    {M : Theorem33.IdenticalUtilitiesModel SourceAgent SourceItem Alloc}
    {L epsilon : ℝ} {lambda : ℕ} {optimal : Alloc}
    (hepsilon_pos : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1)
    (cert : Theorem33.RoundedInstanceSearchCertificate M L epsilon lambda optimal)
    (supply : Theorem33.RoundedValueIndex lambda → ℕ)
    (hsupply_average :
      (∑ k : Theorem33.RoundedValueIndex lambda,
          (supply k : ℝ) * Theorem33.roundedValue L lambda k) =
        (Fintype.card SourceAgent : ℝ) * L)
    (htop_zero :
      supply (paper_lmms_theorem_3_3_topRoundedValueIndex lambda) = 0)
    (hlambda : 0 < lambda) (hL : 0 < L) :=
  LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_type_assignment_with_ratio_guarantee_of_claim34_no_top_weighted_supply
    hepsilon_pos hepsilon_le_one cert supply hsupply_average htop_zero hlambda hL

/--
Theorem 3.3 Claim-3.4 weighted-supply summary ratio endpoint: public alias
pairing selected-pair metadata with the final rounded-instance `(1 + epsilon)`
guarantee.
-/
def theorem3_3_claim34_weighted_supply_type_assignment_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_type_assignment_summary_with_ratio_guarantee_of_claim34_no_top_weighted_supply

/--
Theorem 3.3 Claim-3.4 weighted-supply concrete-IP/search ratio endpoint:
public alias packaging the no-top weighted-supply type assignment as an
uncapped concrete IP certificate.
-/
def theorem3_3_claim34_weighted_supply_concrete_ip_search_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_concrete_ip_and_search_with_ratio_guarantee_of_claim34_no_top_weighted_supply

/--
Theorem 3.3 Claim-3.4 weighted-supply concrete-IP/search full-summary ratio
endpoint: public alias exposing concrete-IP and selected-search-IP summaries
with the final rounded-instance guarantee.
-/
def theorem3_3_claim34_weighted_supply_concrete_ip_search_full_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_concrete_ip_and_search_full_summary_with_ratio_guarantee_of_claim34_no_top_weighted_supply

/--
Theorem 3.3 Claim-3.4 fixed-rounding type-assignment/search endpoint: public
alias for the raw no-top bridge from a fixed high/low rounded supply into the
finite value-pair search layer.
-/
def theorem3_3_claim34_fixed_rounding_type_assignment_search_certificate_exists :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_type_assignment_of_combined_high_low_claim34_no_top_of_margin

/--
Theorem 3.3 Claim-3.4 fixed-rounding summary endpoint: public alias exposing
no-top support, the feasible type assignment, finite-search comparison, and
selected-pair admissibility together.
-/
def theorem3_3_claim34_fixed_rounding_type_assignment_summary_exists :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_type_assignment_summary_of_combined_high_low_claim34_no_top_of_margin

/--
Theorem 3.3 Claim-3.4 fixed-rounding ratio endpoint: a fixed high/low rounded
supply satisfying the no-top margin yields an uncapped type assignment/search
witness and the final rounded-instance `(1 + epsilon)` ratio guarantee.
-/
def theorem3_3_claim34_fixed_rounding_ratio_endpoint
    {SourceAgent SourceItem Alloc : Type*}
    [Fintype SourceAgent] [Nonempty SourceAgent] [DecidableEq SourceAgent]
    [DecidableEq SourceItem]
    {M : Theorem33.IdenticalUtilitiesModel SourceAgent SourceItem Alloc}
    {L epsilon : ℝ} {lambda : ℕ} {optimal : Alloc}
    (hepsilon_pos : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1)
    (cert : Theorem33.RoundedInstanceSearchCertificate M L epsilon lambda optimal)
    (highGoods lowGoods : Finset SourceItem) (v : SourceItem → ℝ)
    (indexOf : SourceItem → Theorem33.RoundedValueIndex lambda)
    (combinedSupply : Theorem33.RoundedValueIndex lambda → ℕ)
    (hlambda : 1 < lambda) (hL : 0 < L)
    (hindex :
      ∀ g : SourceItem, g ∈ highGoods →
        v g ≤ Theorem33.roundedValue L lambda (indexOf g) ∧
          Theorem33.roundedValue L lambda (indexOf g) <
            v g + L / ((lambda : ℝ) ^ 2))
    (hsupply :
      ∀ k : Theorem33.RoundedValueIndex lambda,
        combinedSupply k =
          paper_lmms_theorem_3_3_roundedGoodsSupplyOfGoods indexOf highGoods k +
            Theorem33.lowGoodsAggregatedSupply L lambda (lowGoods.sum v) k)
    (hmargin :
      ∀ g : SourceItem, g ∈ highGoods →
        v g + L / ((lambda : ℝ) ^ 2) ≤ L)
    (hsupply_average :
      (∑ k : Theorem33.RoundedValueIndex lambda,
          (combinedSupply k : ℝ) * Theorem33.roundedValue L lambda k) =
        (Fintype.card SourceAgent : ℝ) * L) :=
  LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_type_assignment_with_ratio_guarantee_of_combined_high_low_claim34_no_top_of_margin
    hepsilon_pos hepsilon_le_one cert highGoods lowGoods v indexOf
    combinedSupply hlambda hL hindex hsupply hmargin hsupply_average

/--
Theorem 3.3 Claim-3.4 fixed-rounding summary ratio endpoint: public alias
pairing the selected-pair metadata summary with the final rounded-instance
`(1 + epsilon)` guarantee.
-/
def theorem3_3_claim34_fixed_rounding_type_assignment_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_type_assignment_summary_with_ratio_guarantee_of_combined_high_low_claim34_no_top_of_margin

/--
Theorem 3.3 Claim-3.4 fixed-rounding materialized-search ratio endpoint:
public alias preserving the bounded materialized allocation/search payload for
the fixed high/low rounded supply.
-/
def theorem3_3_claim34_fixed_rounding_materialized_search_certificate_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_ratio_guarantee_of_combined_high_low_claim34_no_top_of_margin

/--
Theorem 3.3 Claim-3.4 fixed-rounding materialized-search summary ratio
endpoint: public alias preserving the bounded materialized allocation/search
payload and selected-pair admissibility.
-/
def theorem3_3_claim34_fixed_rounding_materialized_search_certificate_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_summary_with_ratio_guarantee_of_combined_high_low_claim34_no_top_of_margin

/--
Theorem 3.3 Claim-3.4 fixed-rounding concrete-IP/search ratio endpoint:
public alias packaging the comparison pair as an uncapped concrete IP
certificate for the fixed high/low rounded supply.
-/
def theorem3_3_claim34_fixed_rounding_concrete_ip_search_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_concrete_ip_and_search_with_ratio_guarantee_of_combined_high_low_claim34_no_top_of_margin

/--
Theorem 3.3 Claim-3.4 fixed-rounding concrete-IP/search full-summary endpoint:
public alias exposing the comparison IP and selected-search-IP summaries for
the fixed high/low rounded supply.
-/
def theorem3_3_claim34_fixed_rounding_concrete_ip_search_full_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_concrete_ip_and_search_full_summary_with_ratio_guarantee_of_combined_high_low_claim34_no_top_of_margin

/--
Theorem 3.3 capped Claim-3.4 weighted-supply bounded-optimum endpoint: public
alias for the materialized bounded allocation before extracting type
assignments, search certificates, or concrete IP witnesses.
-/
def theorem3_3_claim34_capped_weighted_supply_bounded_optimum_endpoint :=
  @LMMS04FairDivision.paper_lmms_claim_3_4_exists_bounded_optimal_for_rounded_supply_average_no_top

/--
Theorem 3.3 capped Claim-3.4 weighted-supply materialized-search endpoint:
public alias for the raw bounded allocation/search payload before adjoining
the final rounded-instance guarantee.
-/
def theorem3_3_claim34_capped_weighted_supply_search_certificate_exists :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_cap_of_rounded_supply_average_no_top

/--
Theorem 3.3 capped Claim-3.4 weighted-supply type-assignment/search endpoint:
public alias for the raw capped type-assignment witness before adjoining the
final rounded-instance guarantee.
-/
def theorem3_3_claim34_capped_weighted_supply_type_assignment_search_certificate_exists :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_type_assignment_with_cap_of_rounded_supply_average_no_top

/--
Theorem 3.3 capped Claim-3.4 weighted-supply ratio endpoint: a no-top
weighted rounded supply at rounded average `LR` yields a capped
type-assignment/search witness and the final rounded-instance guarantee.
-/
def theorem3_3_claim34_capped_weighted_supply_ratio_endpoint
    {SourceAgent SourceItem Alloc : Type*}
    [Fintype SourceAgent] [Nonempty SourceAgent] [DecidableEq SourceAgent]
    {M : Theorem33.IdenticalUtilitiesModel SourceAgent SourceItem Alloc}
    {L LR epsilon : ℝ} {lambda maxCount : ℕ} {optimal : Alloc}
    (hepsilon_pos : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1)
    (cert : Theorem33.RoundedInstanceSearchCertificate M L epsilon lambda optimal)
    (supply : Theorem33.RoundedValueIndex lambda → ℕ)
    (hsupply_average :
      (∑ k : Theorem33.RoundedValueIndex lambda,
          (supply k : ℝ) * Theorem33.roundedValue L lambda k) =
        (Fintype.card SourceAgent : ℝ) * LR)
    (hbase_le_avg : L ≤ LR)
    (htop_zero :
      supply (paper_lmms_theorem_3_3_topRoundedValueIndex lambda) = 0)
    (hcap :
      2 * LR ≤ (maxCount + 1 : ℝ) * (L / (lambda : ℝ)))
    (hlambda : 0 < lambda) (hL : 0 < L) (hLR : 0 < LR) :=
  LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_type_assignment_with_cap_ratio_guarantee_of_rounded_supply_average_no_top
    hepsilon_pos hepsilon_le_one cert supply hsupply_average hbase_le_avg
    htop_zero hcap hlambda hL hLR

/--
Theorem 3.3 capped Claim-3.4 weighted-supply search-certificate ratio
endpoint: public alias for the materialized bounded allocation/search payload,
paired with the final rounded-instance guarantee.
-/
def theorem3_3_claim34_capped_weighted_supply_search_certificate_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_cap_ratio_guarantee_of_rounded_supply_average_no_top

/--
Theorem 3.3 capped Claim-3.4 weighted-supply search-certificate full-summary
ratio endpoint: public alias preserving the bounded rounded-supply allocation
and exposing the chosen capped search IP's full summary.
-/
def theorem3_3_claim34_capped_weighted_supply_search_certificate_full_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_cap_full_summary_ratio_guarantee_of_rounded_supply_average_no_top

/--
Theorem 3.3 capped Claim-3.4 weighted-supply concrete-IP/search endpoint:
public alias packaging the raw capped type-assignment witness as a concrete IP
certificate before adjoining the final rounded-instance guarantee.
-/
def theorem3_3_claim34_capped_weighted_supply_concrete_ip_search_certificate_exists :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_concrete_ip_and_search_with_cap_of_rounded_supply_average_no_top

/--
Theorem 3.3 capped Claim-3.4 weighted-supply concrete-IP/search ratio
endpoint: public alias packaging the capped type-assignment witness as a
capped concrete IP certificate.
-/
def theorem3_3_claim34_capped_weighted_supply_concrete_ip_search_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_concrete_ip_and_search_with_cap_ratio_guarantee_of_rounded_supply_average_no_top

/--
Theorem 3.3 capped Claim-3.4 weighted-supply concrete-IP/search full-summary
endpoint: public alias exposing the capped comparison-IP and selected-search
IP summaries with the final rounded-instance guarantee.
-/
def theorem3_3_claim34_capped_weighted_supply_concrete_ip_search_full_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_concrete_ip_and_search_with_cap_full_summary_ratio_guarantee_of_rounded_supply_average_no_top

/--
Theorem 3.3 capped Claim-3.4 fixed-rounding ratio endpoint: a fixed high/low
rounded supply satisfying the no-top margin yields a capped
type-assignment/search witness and the final rounded-instance guarantee.
-/
def theorem3_3_claim34_capped_fixed_rounding_ratio_endpoint
    {SourceAgent SourceItem Alloc : Type*}
    [Fintype SourceAgent] [Nonempty SourceAgent] [DecidableEq SourceAgent]
    [DecidableEq SourceItem]
    {M : Theorem33.IdenticalUtilitiesModel SourceAgent SourceItem Alloc}
    {L LR epsilon : ℝ} {lambda maxCount : ℕ} {optimal : Alloc}
    (hepsilon_pos : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1)
    (cert : Theorem33.RoundedInstanceSearchCertificate M L epsilon lambda optimal)
    (highGoods lowGoods : Finset SourceItem) (v : SourceItem → ℝ)
    (indexOf : SourceItem → Theorem33.RoundedValueIndex lambda)
    (combinedSupply : Theorem33.RoundedValueIndex lambda → ℕ)
    (hlambda : 1 < lambda) (hL : 0 < L) (hLR : 0 < LR)
    (hindex :
      ∀ g : SourceItem, g ∈ highGoods →
        v g ≤ Theorem33.roundedValue L lambda (indexOf g) ∧
          Theorem33.roundedValue L lambda (indexOf g) <
            v g + L / ((lambda : ℝ) ^ 2))
    (hsupply :
      ∀ k : Theorem33.RoundedValueIndex lambda,
        combinedSupply k =
          paper_lmms_theorem_3_3_roundedGoodsSupplyOfGoods indexOf highGoods k +
            Theorem33.lowGoodsAggregatedSupply L lambda (lowGoods.sum v) k)
    (hmargin :
      ∀ g : SourceItem, g ∈ highGoods →
        v g + L / ((lambda : ℝ) ^ 2) ≤ L)
    (hsupply_average :
      (∑ k : Theorem33.RoundedValueIndex lambda,
          (combinedSupply k : ℝ) * Theorem33.roundedValue L lambda k) =
        (Fintype.card SourceAgent : ℝ) * LR)
    (hbase_le_avg : L ≤ LR)
    (hcap :
      2 * LR ≤ (maxCount + 1 : ℝ) * (L / (lambda : ℝ))) :=
  LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_type_assignment_with_cap_ratio_guarantee_of_combined_high_low_rounded_supply_average_no_top_of_margin
    hepsilon_pos hepsilon_le_one cert highGoods lowGoods v indexOf
    combinedSupply hlambda hL hLR hindex hsupply hmargin hsupply_average
    hbase_le_avg hcap

/--
Theorem 3.3 capped Claim-3.4 fixed-rounding type-assignment/search endpoint:
public alias for the raw capped fixed high/low rounded-supply witness before
adjoining the final rounded-instance guarantee.
-/
def theorem3_3_claim34_capped_fixed_rounding_type_assignment_search_certificate_exists :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_type_assignment_with_cap_of_combined_high_low_rounded_supply_average_no_top_of_margin

/--
Theorem 3.3 capped Claim-3.4 fixed-rounding search-certificate ratio endpoint:
public alias preserving the materialized bounded allocation/search payload
under the fixed high/low rounded supply construction.
-/
def theorem3_3_claim34_capped_fixed_rounding_search_certificate_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_cap_ratio_guarantee_of_combined_high_low_rounded_supply_average_no_top_of_margin

/--
Theorem 3.3 capped Claim-3.4 fixed-rounding search-certificate full-summary
ratio endpoint: public alias preserving the bounded rounded-supply allocation
and exposing the chosen capped search IP's full summary.
-/
def theorem3_3_claim34_capped_fixed_rounding_search_certificate_full_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_cap_full_summary_ratio_guarantee_of_combined_high_low_rounded_supply_average_no_top_of_margin

/--
Theorem 3.3 capped Claim-3.4 fixed-rounding concrete-IP/search ratio endpoint:
public alias packaging the capped fixed high/low type assignment as a concrete
IP certificate.
-/
def theorem3_3_claim34_capped_fixed_rounding_concrete_ip_search_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_concrete_ip_and_search_with_cap_ratio_guarantee_of_combined_high_low_rounded_supply_average_no_top_of_margin

/--
Theorem 3.3 capped Claim-3.4 fixed-rounding concrete-IP/search full-summary
ratio endpoint: public alias exposing capped comparison-IP and selected-search
IP summaries for a fixed high/low rounded supply.
-/
def theorem3_3_claim34_capped_fixed_rounding_concrete_ip_search_full_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_concrete_ip_and_search_with_cap_full_summary_ratio_guarantee_of_combined_high_low_rounded_supply_average_no_top_of_margin

/--
Theorem 3.3 capped Claim-3.4 generated-rounding ratio endpoint: the high/low
rounding construction chooses the rounded supply, then returns a capped
type-assignment/search witness and the final rounded-instance guarantee.
-/
def theorem3_3_claim34_capped_generated_rounding_ratio_endpoint
    {SourceAgent SourceItem Alloc : Type*}
    [Fintype SourceAgent] [Nonempty SourceAgent] [DecidableEq SourceAgent]
    [DecidableEq SourceItem]
    {M : Theorem33.IdenticalUtilitiesModel SourceAgent SourceItem Alloc}
    {L LR epsilon : ℝ} {lambda maxCount : ℕ} {optimal : Alloc}
    (hepsilon_pos : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1)
    (cert : Theorem33.RoundedInstanceSearchCertificate M L epsilon lambda optimal)
    (highGoods lowGoods : Finset SourceItem) (v : SourceItem → ℝ)
    (hlambda : 1 < lambda) (hL : 0 < L) (hLR : 0 < LR)
    (hhigh :
      ∀ g : SourceItem, g ∈ highGoods →
        L / (lambda : ℝ) < v g ∧ v g < L)
    (hlow :
      ∀ g : SourceItem, g ∈ lowGoods →
        0 ≤ v g ∧ v g < L / (lambda : ℝ))
    (hmargin :
      ∀ g : SourceItem, g ∈ highGoods →
        v g + L / ((lambda : ℝ) ^ 2) ≤ L)
    (haverage :
      ∀ (indexOf : SourceItem → Theorem33.RoundedValueIndex lambda)
        (combinedSupply : Theorem33.RoundedValueIndex lambda → ℕ),
        (∀ g : SourceItem, g ∈ highGoods →
          v g ≤ Theorem33.roundedValue L lambda (indexOf g) ∧
            Theorem33.roundedValue L lambda (indexOf g) <
              v g + L / ((lambda : ℝ) ^ 2)) →
        (∀ k : Theorem33.RoundedValueIndex lambda,
          combinedSupply k =
            paper_lmms_theorem_3_3_roundedGoodsSupplyOfGoods indexOf highGoods k +
              Theorem33.lowGoodsAggregatedSupply L lambda (lowGoods.sum v) k) →
        (∑ k : Theorem33.RoundedValueIndex lambda,
            (combinedSupply k : ℝ) * Theorem33.roundedValue L lambda k) =
          (Fintype.card SourceAgent : ℝ) * LR)
    (hbase_le_avg : L ≤ LR)
    (hcap :
      2 * LR ≤ (maxCount + 1 : ℝ) * (L / (lambda : ℝ))) :=
  LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_value_pair_type_assignment_with_cap_ratio_guarantee_of_rounded_supply_average_no_top_of_margin
    hepsilon_pos hepsilon_le_one cert highGoods lowGoods v hlambda hL hLR
    hhigh hlow hmargin haverage hbase_le_avg hcap

/--
Theorem 3.3 capped Claim-3.4 generated-rounding type-assignment/search
endpoint: public alias for the raw generated high/low rounded-supply witness
before adjoining the final rounded-instance guarantee.
-/
def theorem3_3_claim34_capped_generated_rounding_type_assignment_search_certificate_exists :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_value_pair_type_assignment_with_cap_of_rounded_supply_average_no_top_of_margin

/--
Theorem 3.3 capped Claim-3.4 generated-rounding search-certificate ratio
endpoint: public alias preserving the selected rounding map, rounded supply,
and materialized bounded allocation/search payload.
-/
def theorem3_3_claim34_capped_generated_rounding_search_certificate_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_value_pair_search_certificate_with_cap_ratio_guarantee_of_rounded_supply_average_no_top_of_margin

/--
Theorem 3.3 capped Claim-3.4 generated-rounding search-certificate
full-summary ratio endpoint: public alias preserving the selected rounding
map, rounded supply, bounded allocation, and chosen capped search IP summary.
-/
def theorem3_3_claim34_capped_generated_rounding_search_certificate_full_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_value_pair_search_certificate_with_cap_full_summary_ratio_guarantee_of_rounded_supply_average_no_top_of_margin

/--
Theorem 3.3 capped Claim-3.4 generated-rounding concrete-IP/search ratio
endpoint: public alias preserving the selected rounding map and rounded supply
while packaging the capped type assignment as a concrete IP certificate.
-/
def theorem3_3_claim34_capped_generated_rounding_concrete_ip_search_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_concrete_ip_and_search_with_cap_ratio_guarantee_of_rounded_supply_average_no_top_of_margin

/--
Theorem 3.3 capped Claim-3.4 generated-rounding concrete-IP/search
full-summary ratio endpoint: public alias exposing capped comparison-IP and
selected-search IP summaries while preserving the generated rounded supply.
-/
def theorem3_3_claim34_capped_generated_rounding_concrete_ip_search_full_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_concrete_ip_and_search_with_cap_full_summary_ratio_guarantee_of_rounded_supply_average_no_top_of_margin

/--
Theorem 3.3 capped Claim-3.4 source-average type-assignment/search endpoint:
public alias for the raw capped source-average witness before adjoining the
final rounded-instance guarantee.
-/
def theorem3_3_claim34_capped_source_average_type_assignment_search_certificate_exists :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_value_pair_type_assignment_with_cap_of_source_average_no_top_of_margin

/--
Theorem 3.3 capped Claim-3.4 source-average ratio endpoint: under supplied
rounded-average identity and cap assumptions, the high/low source average
provides the lower-average side condition and returns a capped
type-assignment/search witness with the final guarantee.
-/
def theorem3_3_claim34_capped_source_average_ratio_endpoint
    {SourceAgent SourceItem Alloc : Type*}
    [Fintype SourceAgent] [Nonempty SourceAgent] [DecidableEq SourceAgent]
    [DecidableEq SourceItem]
    {M : Theorem33.IdenticalUtilitiesModel SourceAgent SourceItem Alloc}
    {L LR epsilon : ℝ} {lambda maxCount : ℕ} {optimal : Alloc}
    (hepsilon_pos : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1)
    (cert : Theorem33.RoundedInstanceSearchCertificate M L epsilon lambda optimal)
    (highGoods lowGoods : Finset SourceItem) (v : SourceItem → ℝ)
    (hlambda : 1 < lambda) (hL : 0 < L)
    (hhigh :
      ∀ g : SourceItem, g ∈ highGoods →
        L / (lambda : ℝ) < v g ∧ v g < L)
    (hlow :
      ∀ g : SourceItem, g ∈ lowGoods →
        0 ≤ v g ∧ v g < L / (lambda : ℝ))
    (hmargin :
      ∀ g : SourceItem, g ∈ highGoods →
        v g + L / ((lambda : ℝ) ^ 2) ≤ L)
    (hsource_average :
      highGoods.sum v + lowGoods.sum v =
        (Fintype.card SourceAgent : ℝ) * L)
    (haverage :
      ∀ (indexOf : SourceItem → Theorem33.RoundedValueIndex lambda)
        (combinedSupply : Theorem33.RoundedValueIndex lambda → ℕ),
        (∀ g : SourceItem, g ∈ highGoods →
          v g ≤ Theorem33.roundedValue L lambda (indexOf g) ∧
            Theorem33.roundedValue L lambda (indexOf g) <
              v g + L / ((lambda : ℝ) ^ 2)) →
        (∀ k : Theorem33.RoundedValueIndex lambda,
          combinedSupply k =
            paper_lmms_theorem_3_3_roundedGoodsSupplyOfGoods indexOf highGoods k +
              Theorem33.lowGoodsAggregatedSupply L lambda (lowGoods.sum v) k) →
        (∑ k : Theorem33.RoundedValueIndex lambda,
            (combinedSupply k : ℝ) * Theorem33.roundedValue L lambda k) =
          (Fintype.card SourceAgent : ℝ) * LR)
    (hcap :
      2 * LR ≤ (maxCount + 1 : ℝ) * (L / (lambda : ℝ))) :=
  LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_value_pair_type_assignment_with_cap_ratio_guarantee_of_source_average_no_top_of_margin
    hepsilon_pos hepsilon_le_one cert highGoods lowGoods v hlambda hL hhigh
    hlow hmargin hsource_average haverage hcap

/--
Theorem 3.3 capped Claim-3.4 source-average search-certificate ratio endpoint:
conditional public alias preserving the generated rounded supply and
materialized bounded allocation/search payload under the supplied
rounded-average identity and cap assumptions.
-/
def theorem3_3_claim34_capped_source_average_search_certificate_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_value_pair_search_certificate_with_cap_ratio_guarantee_of_source_average_no_top_of_margin

/--
Theorem 3.3 capped Claim-3.4 source-average search-certificate full-summary
ratio endpoint: conditional public alias preserving the generated rounded
supply and bounded allocation while exposing the chosen capped search IP
summary under the supplied rounded-average identity and cap assumptions.
-/
def theorem3_3_claim34_capped_source_average_search_certificate_full_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_value_pair_search_certificate_with_cap_full_summary_ratio_guarantee_of_source_average_no_top_of_margin

/--
Theorem 3.3 capped Claim-3.4 source-average concrete-IP/search ratio endpoint:
conditional public alias packaging the source-average capped witness as a
concrete IP certificate under the supplied rounded-average identity and cap.
-/
def theorem3_3_claim34_capped_source_average_concrete_ip_search_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_concrete_ip_and_search_with_cap_ratio_guarantee_of_source_average_no_top_of_margin

/--
Theorem 3.3 capped Claim-3.4 source-average concrete-IP/search full-summary
ratio endpoint: conditional public alias exposing capped comparison-IP and
selected-search IP summaries under the supplied rounded-average identity and
cap assumptions.
-/
def theorem3_3_claim34_capped_source_average_concrete_ip_search_full_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_concrete_ip_and_search_with_cap_full_summary_ratio_guarantee_of_source_average_no_top_of_margin

/--
Theorem 3.3 capped Claim-3.4 source-average upper-bound type-assignment/search
endpoint: public alias for the raw externally capped source-average witness
before adjoining the final rounded-instance guarantee.
-/
def theorem3_3_claim34_capped_source_average_upper_bound_type_assignment_search_certificate_exists :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_value_pair_type_assignment_with_cap_of_source_average_upper_bound_no_top_of_margin

/--
Theorem 3.3 capped Claim-3.4 source-average upper-bound ratio endpoint: an
external upper bound on the rounded average supplies the cap, while the source
average derives the lower bound needed for the capped finite search.
-/
def theorem3_3_claim34_capped_source_average_upper_bound_ratio_endpoint
    {SourceAgent SourceItem Alloc : Type*}
    [Fintype SourceAgent] [Nonempty SourceAgent] [DecidableEq SourceAgent]
    [DecidableEq SourceItem]
    {M : Theorem33.IdenticalUtilitiesModel SourceAgent SourceItem Alloc}
    {L LR capAverage epsilon : ℝ} {lambda maxCount : ℕ} {optimal : Alloc}
    (hepsilon_pos : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1)
    (cert : Theorem33.RoundedInstanceSearchCertificate M L epsilon lambda optimal)
    (highGoods lowGoods : Finset SourceItem) (v : SourceItem → ℝ)
    (hlambda : 1 < lambda) (hL : 0 < L)
    (hhigh :
      ∀ g : SourceItem, g ∈ highGoods →
        L / (lambda : ℝ) < v g ∧ v g < L)
    (hlow :
      ∀ g : SourceItem, g ∈ lowGoods →
        0 ≤ v g ∧ v g < L / (lambda : ℝ))
    (hmargin :
      ∀ g : SourceItem, g ∈ highGoods →
        v g + L / ((lambda : ℝ) ^ 2) ≤ L)
    (hsource_average :
      highGoods.sum v + lowGoods.sum v =
        (Fintype.card SourceAgent : ℝ) * L)
    (haverage :
      ∀ (indexOf : SourceItem → Theorem33.RoundedValueIndex lambda)
        (combinedSupply : Theorem33.RoundedValueIndex lambda → ℕ),
        (∀ g : SourceItem, g ∈ highGoods →
          v g ≤ Theorem33.roundedValue L lambda (indexOf g) ∧
            Theorem33.roundedValue L lambda (indexOf g) <
              v g + L / ((lambda : ℝ) ^ 2)) →
        (∀ k : Theorem33.RoundedValueIndex lambda,
          combinedSupply k =
            paper_lmms_theorem_3_3_roundedGoodsSupplyOfGoods indexOf highGoods k +
              Theorem33.lowGoodsAggregatedSupply L lambda (lowGoods.sum v) k) →
        (∑ k : Theorem33.RoundedValueIndex lambda,
            (combinedSupply k : ℝ) * Theorem33.roundedValue L lambda k) =
          (Fintype.card SourceAgent : ℝ) * LR)
    (hrounded_upper :
      ∀ (indexOf : SourceItem → Theorem33.RoundedValueIndex lambda)
        (combinedSupply : Theorem33.RoundedValueIndex lambda → ℕ),
        (∀ g : SourceItem, g ∈ highGoods →
          v g ≤ Theorem33.roundedValue L lambda (indexOf g) ∧
            Theorem33.roundedValue L lambda (indexOf g) <
              v g + L / ((lambda : ℝ) ^ 2)) →
        (∀ k : Theorem33.RoundedValueIndex lambda,
          combinedSupply k =
            paper_lmms_theorem_3_3_roundedGoodsSupplyOfGoods indexOf highGoods k +
              Theorem33.lowGoodsAggregatedSupply L lambda (lowGoods.sum v) k) →
        (∑ k : Theorem33.RoundedValueIndex lambda,
            (combinedSupply k : ℝ) * Theorem33.roundedValue L lambda k) ≤
          (Fintype.card SourceAgent : ℝ) * capAverage)
    (hcap_upper :
      2 * capAverage ≤ (maxCount + 1 : ℝ) * (L / (lambda : ℝ))) :=
  LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_value_pair_type_assignment_with_cap_ratio_guarantee_of_source_average_upper_bound_no_top_of_margin
    hepsilon_pos hepsilon_le_one cert highGoods lowGoods v hlambda hL hhigh
    hlow hmargin hsource_average haverage hrounded_upper hcap_upper

/--
Theorem 3.3 capped Claim-3.4 source-average upper-bound search-certificate
ratio endpoint: public alias preserving the materialized bounded
allocation/search payload after converting the external upper bound to the
actual cap premise.
-/
def theorem3_3_claim34_capped_source_average_upper_bound_search_certificate_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_value_pair_search_certificate_with_cap_ratio_guarantee_of_source_average_upper_bound_no_top_of_margin

/--
Theorem 3.3 capped Claim-3.4 source-average upper-bound search-certificate
full-summary ratio endpoint: public alias exposing the chosen capped search IP
summary under an external rounded-average cap.
-/
def theorem3_3_claim34_capped_source_average_upper_bound_search_certificate_full_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_value_pair_search_certificate_with_cap_full_summary_ratio_guarantee_of_source_average_upper_bound_no_top_of_margin

/--
Theorem 3.3 capped Claim-3.4 source-average upper-bound concrete-IP/search
ratio endpoint: public alias packaging the externally capped witness as a
concrete IP certificate under the supplied cap.
-/
def theorem3_3_claim34_capped_source_average_upper_bound_concrete_ip_search_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_concrete_ip_and_search_with_cap_ratio_guarantee_of_source_average_upper_bound_no_top_of_margin

/--
Theorem 3.3 capped Claim-3.4 source-average upper-bound concrete-IP/search
full-summary ratio endpoint: public alias exposing capped comparison-IP and
selected-search IP summaries under an external rounded-average cap.
-/
def theorem3_3_claim34_capped_source_average_upper_bound_concrete_ip_search_full_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_concrete_ip_and_search_with_cap_full_summary_ratio_guarantee_of_source_average_upper_bound_no_top_of_margin

/--
Theorem 3.3 Claim-3.4 auto-cap source-error-bound type-assignment/search
endpoint: public alias for the raw generated-cap witness before adjoining the
final rounded-instance guarantee.
-/
def theorem3_3_claim34_auto_cap_source_error_bound_type_assignment_search_certificate_exists :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_value_pair_type_assignment_with_auto_cap_of_source_error_bound_no_top_of_margin

/--
Theorem 3.3 Claim-3.4 auto-cap source-error-bound ratio endpoint: the rounded
total is bounded by `capAverage`, so the generated cap is
`capCountForAverage L capAverage lambda`.
-/
def theorem3_3_claim34_auto_cap_source_error_bound_ratio_endpoint
    {SourceAgent SourceItem Alloc : Type*}
    [Fintype SourceAgent] [Nonempty SourceAgent] [DecidableEq SourceAgent]
    [DecidableEq SourceItem]
    {M : Theorem33.IdenticalUtilitiesModel SourceAgent SourceItem Alloc}
    {L LR capAverage epsilon : ℝ} {lambda : ℕ} {optimal : Alloc}
    (hepsilon_pos : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1)
    (cert : Theorem33.RoundedInstanceSearchCertificate M L epsilon lambda optimal)
    (highGoods lowGoods : Finset SourceItem) (v : SourceItem → ℝ)
    (hlambda : 1 < lambda) (hL : 0 < L)
    (hhigh :
      ∀ g : SourceItem, g ∈ highGoods →
        L / (lambda : ℝ) < v g ∧ v g < L)
    (hlow :
      ∀ g : SourceItem, g ∈ lowGoods →
        0 ≤ v g ∧ v g < L / (lambda : ℝ))
    (hmargin :
      ∀ g : SourceItem, g ∈ highGoods →
        v g + L / ((lambda : ℝ) ^ 2) ≤ L)
    (hsource_average :
      highGoods.sum v + lowGoods.sum v =
        (Fintype.card SourceAgent : ℝ) * L)
    (haverage :
      ∀ (indexOf : SourceItem → Theorem33.RoundedValueIndex lambda)
        (combinedSupply : Theorem33.RoundedValueIndex lambda → ℕ),
        (∀ g : SourceItem, g ∈ highGoods →
          v g ≤ Theorem33.roundedValue L lambda (indexOf g) ∧
            Theorem33.roundedValue L lambda (indexOf g) <
              v g + L / ((lambda : ℝ) ^ 2)) →
        (∀ k : Theorem33.RoundedValueIndex lambda,
          combinedSupply k =
            paper_lmms_theorem_3_3_roundedGoodsSupplyOfGoods indexOf highGoods k +
              Theorem33.lowGoodsAggregatedSupply L lambda (lowGoods.sum v) k) →
        (∑ k : Theorem33.RoundedValueIndex lambda,
            (combinedSupply k : ℝ) * Theorem33.roundedValue L lambda k) =
          (Fintype.card SourceAgent : ℝ) * LR)
    (herror_upper :
      highGoods.sum v + lowGoods.sum v +
          (highGoods.card : ℝ) * (L / ((lambda : ℝ) ^ 2)) +
            L / (lambda : ℝ) ≤
        (Fintype.card SourceAgent : ℝ) * capAverage) :=
  LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_value_pair_type_assignment_with_auto_cap_ratio_guarantee_of_source_error_bound_no_top_of_margin
    hepsilon_pos hepsilon_le_one cert highGoods lowGoods v hlambda hL hhigh
    hlow hmargin hsource_average haverage herror_upper

/--
Theorem 3.3 Claim-3.4 auto-cap source-error-bound search-certificate ratio
endpoint: public alias preserving the materialized bounded allocation/search
payload under the generated cap.
-/
def theorem3_3_claim34_auto_cap_source_error_bound_search_certificate_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_value_pair_search_certificate_with_auto_cap_ratio_guarantee_of_source_error_bound_no_top_of_margin

/--
Theorem 3.3 Claim-3.4 auto-cap source-error-bound search-certificate
full-summary ratio endpoint: public alias exposing the chosen capped search IP
summary under the generated cap.
-/
def theorem3_3_claim34_auto_cap_source_error_bound_search_certificate_full_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_value_pair_search_certificate_with_auto_cap_full_summary_ratio_guarantee_of_source_error_bound_no_top_of_margin

/--
Theorem 3.3 Claim-3.4 auto-cap source-error-bound concrete-IP/search ratio
endpoint: public alias packaging the comparison pair as a capped concrete IP
certificate under the generated cap.
-/
def theorem3_3_claim34_auto_cap_source_error_bound_concrete_ip_search_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_concrete_ip_and_search_with_auto_cap_ratio_guarantee_of_source_error_bound_no_top_of_margin

/--
Theorem 3.3 Claim-3.4 auto-cap source-error-bound concrete-IP/search
full-summary ratio endpoint: public alias exposing capped comparison-IP and
selected-search IP summaries under the generated cap.
-/
def theorem3_3_claim34_auto_cap_source_error_bound_concrete_ip_search_full_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_auto_cap_concrete_ip_and_search_full_summary_with_ratio_guarantee_of_source_error_bound_no_top_of_margin

/--
Theorem 3.3 Claim-3.4 auto-cap source-error-budget type-assignment/search
endpoint: public alias for the raw aggregate-error-budget witness before
adjoining the final rounded-instance guarantee.
-/
def theorem3_3_claim34_auto_cap_source_error_budget_type_assignment_search_certificate_exists :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_value_pair_type_assignment_with_auto_cap_of_source_error_budget_no_top_of_margin

/--
Theorem 3.3 Claim-3.4 auto-cap source-error-budget ratio endpoint: the caller
supplies only the aggregate rounding-error budget, and the generated cap uses
`L + extraAverage`.
-/
def theorem3_3_claim34_auto_cap_source_error_budget_ratio_endpoint
    {SourceAgent SourceItem Alloc : Type*}
    [Fintype SourceAgent] [Nonempty SourceAgent] [DecidableEq SourceAgent]
    [DecidableEq SourceItem]
    {M : Theorem33.IdenticalUtilitiesModel SourceAgent SourceItem Alloc}
    {L LR extraAverage epsilon : ℝ} {lambda : ℕ} {optimal : Alloc}
    (hepsilon_pos : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1)
    (cert : Theorem33.RoundedInstanceSearchCertificate M L epsilon lambda optimal)
    (highGoods lowGoods : Finset SourceItem) (v : SourceItem → ℝ)
    (hlambda : 1 < lambda) (hL : 0 < L)
    (hhigh :
      ∀ g : SourceItem, g ∈ highGoods →
        L / (lambda : ℝ) < v g ∧ v g < L)
    (hlow :
      ∀ g : SourceItem, g ∈ lowGoods →
        0 ≤ v g ∧ v g < L / (lambda : ℝ))
    (hmargin :
      ∀ g : SourceItem, g ∈ highGoods →
        v g + L / ((lambda : ℝ) ^ 2) ≤ L)
    (hsource_average :
      highGoods.sum v + lowGoods.sum v =
        (Fintype.card SourceAgent : ℝ) * L)
    (haverage :
      ∀ (indexOf : SourceItem → Theorem33.RoundedValueIndex lambda)
        (combinedSupply : Theorem33.RoundedValueIndex lambda → ℕ),
        (∀ g : SourceItem, g ∈ highGoods →
          v g ≤ Theorem33.roundedValue L lambda (indexOf g) ∧
            Theorem33.roundedValue L lambda (indexOf g) <
              v g + L / ((lambda : ℝ) ^ 2)) →
        (∀ k : Theorem33.RoundedValueIndex lambda,
          combinedSupply k =
            paper_lmms_theorem_3_3_roundedGoodsSupplyOfGoods indexOf highGoods k +
              Theorem33.lowGoodsAggregatedSupply L lambda (lowGoods.sum v) k) →
        (∑ k : Theorem33.RoundedValueIndex lambda,
            (combinedSupply k : ℝ) * Theorem33.roundedValue L lambda k) =
          (Fintype.card SourceAgent : ℝ) * LR)
    (herror_budget :
      (highGoods.card : ℝ) * (L / ((lambda : ℝ) ^ 2)) +
          L / (lambda : ℝ) ≤
        (Fintype.card SourceAgent : ℝ) * extraAverage) :=
  LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_value_pair_type_assignment_with_auto_cap_ratio_guarantee_of_source_error_budget_no_top_of_margin
    hepsilon_pos hepsilon_le_one cert highGoods lowGoods v hlambda hL hhigh
    hlow hmargin hsource_average haverage herror_budget

/--
Theorem 3.3 Claim-3.4 auto-cap source-error-budget search-certificate ratio
endpoint: public alias preserving the materialized bounded allocation/search
payload under the `L + extraAverage` generated cap.
-/
def theorem3_3_claim34_auto_cap_source_error_budget_search_certificate_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_value_pair_search_certificate_with_auto_cap_ratio_guarantee_of_source_error_budget_no_top_of_margin

/--
Theorem 3.3 Claim-3.4 auto-cap source-error-budget search-certificate
full-summary ratio endpoint: public alias exposing the chosen capped search IP
summary under the `L + extraAverage` generated cap.
-/
def theorem3_3_claim34_auto_cap_source_error_budget_search_certificate_full_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_value_pair_search_certificate_with_auto_cap_full_summary_ratio_guarantee_of_source_error_budget_no_top_of_margin

/--
Theorem 3.3 Claim-3.4 auto-cap source-error-budget concrete-IP/search ratio
endpoint: public alias packaging the comparison pair as a capped concrete IP
certificate under the `L + extraAverage` generated cap.
-/
def theorem3_3_claim34_auto_cap_source_error_budget_concrete_ip_search_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_concrete_ip_and_search_with_auto_cap_ratio_guarantee_of_source_error_budget_no_top_of_margin

/--
Theorem 3.3 Claim-3.4 auto-cap source-error-budget concrete-IP/search
full-summary ratio endpoint: public alias exposing capped comparison-IP and
selected-search IP summaries under the generated `L + extraAverage` cap.
-/
def theorem3_3_claim34_auto_cap_source_error_budget_concrete_ip_search_full_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_auto_cap_concrete_ip_and_search_full_summary_with_ratio_guarantee_of_source_error_budget_no_top_of_margin

/--
Theorem 3.3 Claim-3.4 auto-cap source-average type-assignment/search endpoint:
public alias for the raw source-average auto-cap witness, conditional on the
supplied rounded-average identity, before adjoining the final rounded-instance
guarantee.
-/
def theorem3_3_claim34_auto_cap_source_average_type_assignment_search_certificate_exists :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_value_pair_type_assignment_with_auto_cap_of_source_average_no_top_of_margin

/--
Theorem 3.3 Claim-3.4 auto-cap source-average type-assignment ratio endpoint:
assuming the supplied source-average and rounded-average identities, the source
high/low split uses the paper's auto cap and returns the direct capped
type-assignment/search payload with the final rounded-instance guarantee.
-/
def theorem3_3_claim34_auto_cap_source_average_type_assignment_ratio_endpoint
    {SourceAgent SourceItem Alloc : Type*}
    [Fintype SourceAgent] [Nonempty SourceAgent] [DecidableEq SourceAgent]
    [DecidableEq SourceItem]
    {M : Theorem33.IdenticalUtilitiesModel SourceAgent SourceItem Alloc}
    {L LR epsilon : ℝ} {lambda : ℕ} {optimal : Alloc}
    (hepsilon_pos : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1)
    (cert : Theorem33.RoundedInstanceSearchCertificate M L epsilon lambda optimal)
    (highGoods lowGoods : Finset SourceItem) (v : SourceItem → ℝ)
    (hlambda : 1 < lambda) (hL : 0 < L)
    (hhigh :
      ∀ g : SourceItem, g ∈ highGoods →
        L / (lambda : ℝ) < v g ∧ v g < L)
    (hlow :
      ∀ g : SourceItem, g ∈ lowGoods →
        0 ≤ v g ∧ v g < L / (lambda : ℝ))
    (hmargin :
      ∀ g : SourceItem, g ∈ highGoods →
        v g + L / ((lambda : ℝ) ^ 2) ≤ L)
    (hsource_average :
      highGoods.sum v + lowGoods.sum v =
        (Fintype.card SourceAgent : ℝ) * L)
    (haverage :
      ∀ (indexOf : SourceItem → Theorem33.RoundedValueIndex lambda)
        (combinedSupply : Theorem33.RoundedValueIndex lambda → ℕ),
        (∀ g : SourceItem, g ∈ highGoods →
          v g ≤ Theorem33.roundedValue L lambda (indexOf g) ∧
            Theorem33.roundedValue L lambda (indexOf g) <
              v g + L / ((lambda : ℝ) ^ 2)) →
        (∀ k : Theorem33.RoundedValueIndex lambda,
          combinedSupply k =
            paper_lmms_theorem_3_3_roundedGoodsSupplyOfGoods indexOf highGoods k +
              Theorem33.lowGoodsAggregatedSupply L lambda (lowGoods.sum v) k) →
        (∑ k : Theorem33.RoundedValueIndex lambda,
            (combinedSupply k : ℝ) * Theorem33.roundedValue L lambda k) =
          (Fintype.card SourceAgent : ℝ) * LR) :=
  LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_value_pair_type_assignment_with_auto_cap_ratio_guarantee_of_source_average_no_top_of_margin
    hepsilon_pos hepsilon_le_one cert highGoods lowGoods v hlambda hL hhigh
    hlow hmargin hsource_average haverage

/--
Theorem 3.3 Claim-3.4 auto-cap source-average finite-search endpoint: public
alias for the raw generated-cap type-assignment/search seam, conditional on the
supplied rounded-average identity, before adjoining the materialized Claim-3.4
allocation payload or final rounded-instance guarantee.
-/
def theorem3_3_claim34_auto_cap_source_average_search_certificate_exists :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_value_pair_search_certificate_with_auto_cap_of_source_average_no_top_of_margin

/--
Theorem 3.3 Claim-3.4 auto-cap source-average finite-search ratio endpoint:
assuming the supplied source-average and rounded-average identities, the source
high/low split uses the auto cap and exposes the capped value-pair search
certificate, materialized bounded allocation, and final guarantee.
-/
def theorem3_3_claim34_auto_cap_source_average_search_certificate_ratio_endpoint
    {SourceAgent SourceItem Alloc : Type*}
    [Fintype SourceAgent] [Nonempty SourceAgent] [DecidableEq SourceAgent]
    [DecidableEq SourceItem]
    {M : Theorem33.IdenticalUtilitiesModel SourceAgent SourceItem Alloc}
    {L LR epsilon : ℝ} {lambda : ℕ} {optimal : Alloc}
    (hepsilon_pos : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1)
    (cert : Theorem33.RoundedInstanceSearchCertificate M L epsilon lambda optimal)
    (highGoods lowGoods : Finset SourceItem) (v : SourceItem → ℝ)
    (hlambda : 1 < lambda) (hL : 0 < L)
    (hhigh :
      ∀ g : SourceItem, g ∈ highGoods →
        L / (lambda : ℝ) < v g ∧ v g < L)
    (hlow :
      ∀ g : SourceItem, g ∈ lowGoods →
        0 ≤ v g ∧ v g < L / (lambda : ℝ))
    (hmargin :
      ∀ g : SourceItem, g ∈ highGoods →
        v g + L / ((lambda : ℝ) ^ 2) ≤ L)
    (hsource_average :
      highGoods.sum v + lowGoods.sum v =
        (Fintype.card SourceAgent : ℝ) * L)
    (haverage :
      ∀ (indexOf : SourceItem → Theorem33.RoundedValueIndex lambda)
        (combinedSupply : Theorem33.RoundedValueIndex lambda → ℕ),
        (∀ g : SourceItem, g ∈ highGoods →
          v g ≤ Theorem33.roundedValue L lambda (indexOf g) ∧
            Theorem33.roundedValue L lambda (indexOf g) <
              v g + L / ((lambda : ℝ) ^ 2)) →
        (∀ k : Theorem33.RoundedValueIndex lambda,
          combinedSupply k =
            paper_lmms_theorem_3_3_roundedGoodsSupplyOfGoods indexOf highGoods k +
              Theorem33.lowGoodsAggregatedSupply L lambda (lowGoods.sum v) k) →
        (∑ k : Theorem33.RoundedValueIndex lambda,
            (combinedSupply k : ℝ) * Theorem33.roundedValue L lambda k) =
          (Fintype.card SourceAgent : ℝ) * LR) :=
  LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_value_pair_search_certificate_with_auto_cap_materialized_ratio_guarantee_of_source_average_no_top_of_margin
    hepsilon_pos hepsilon_le_one cert highGoods lowGoods v hlambda hL hhigh
    hlow hmargin hsource_average haverage

/--
Theorem 3.3 Claim-3.4 auto-cap source-average search-certificate full-summary
ratio endpoint: conditional public alias preserving the materialized bounded
allocation while exposing the chosen capped search IP summary under the
generated source-average cap and supplied rounded-average identity.
-/
def theorem3_3_claim34_auto_cap_source_average_search_certificate_full_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_value_pair_search_certificate_with_auto_cap_materialized_full_summary_ratio_guarantee_of_source_average_no_top_of_margin

/--
Theorem 3.3 Claim-3.4 auto-cap actual-average full-summary ratio endpoint:
public alias for the generated high/low rounded supply package that defines
`LR` as the supply's actual rounded average, proves the exact average identity,
and preserves the materialized bounded allocation plus capped search summary.
-/
def theorem3_3_claim34_auto_cap_source_actual_average_search_certificate_full_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_actual_average_value_pair_search_certificate_with_auto_cap_materialized_full_summary_ratio_guarantee_no_top_of_margin

/--
Theorem 3.3 Claim-3.4 auto-cap actual-average full-IP summary endpoint:
public alias for the generated high/low rounded supply package that defines
`LR` as the supply's actual rounded average and exposes the comparison capped
IP plus selected capped-search IP constraints with explicit search-size bounds.
-/
def theorem3_3_claim34_auto_cap_source_actual_average_full_ip_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_actual_average_auto_cap_full_ip_summary_with_ratio_guarantee_no_top_of_margin

/--
Theorem 3.3 Claim-3.4 auto-cap actual-average full-IP summary endpoint from
raw Lemma 3.5 additive transfer premises: public alias for the generated
high/low rounded supply package that assembles the rounded-instance search
certificate internally before exposing the capped comparison IP and selected
search IP constraints.
-/
def theorem3_3_claim34_auto_cap_source_actual_average_full_ip_summary_of_additive_transfer_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_actual_average_auto_cap_full_ip_summary_of_additive_transfer_no_top_of_margin

/--
Theorem 3.3 Claim-3.4 auto-cap source-average concrete-IP/search endpoint:
public alias for the raw generated-cap concrete-IP payload, conditional on the
supplied rounded-average identity, before adjoining the final rounded-instance
guarantee.
-/
def theorem3_3_claim34_auto_cap_source_average_concrete_ip_search_certificate_exists :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_concrete_ip_and_search_with_auto_cap_of_source_average_no_top_of_margin

/--
Theorem 3.3 Claim-3.4 auto-cap source-average concrete-IP ratio endpoint:
assuming the supplied source-average and rounded-average identities, the direct
auto-cap witness is packaged as a capped concrete IP certificate for the
comparison pair, with the final rounded-instance guarantee.
-/
def theorem3_3_claim34_auto_cap_source_average_concrete_ip_ratio_endpoint
    {SourceAgent SourceItem Alloc : Type*}
    [Fintype SourceAgent] [Nonempty SourceAgent] [DecidableEq SourceAgent]
    [DecidableEq SourceItem]
    {M : Theorem33.IdenticalUtilitiesModel SourceAgent SourceItem Alloc}
    {L LR epsilon : ℝ} {lambda : ℕ} {optimal : Alloc}
    (hepsilon_pos : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1)
    (cert : Theorem33.RoundedInstanceSearchCertificate M L epsilon lambda optimal)
    (highGoods lowGoods : Finset SourceItem) (v : SourceItem → ℝ)
    (hlambda : 1 < lambda) (hL : 0 < L)
    (hhigh :
      ∀ g : SourceItem, g ∈ highGoods →
        L / (lambda : ℝ) < v g ∧ v g < L)
    (hlow :
      ∀ g : SourceItem, g ∈ lowGoods →
        0 ≤ v g ∧ v g < L / (lambda : ℝ))
    (hmargin :
      ∀ g : SourceItem, g ∈ highGoods →
        v g + L / ((lambda : ℝ) ^ 2) ≤ L)
    (hsource_average :
      highGoods.sum v + lowGoods.sum v =
        (Fintype.card SourceAgent : ℝ) * L)
    (haverage :
      ∀ (indexOf : SourceItem → Theorem33.RoundedValueIndex lambda)
        (combinedSupply : Theorem33.RoundedValueIndex lambda → ℕ),
        (∀ g : SourceItem, g ∈ highGoods →
          v g ≤ Theorem33.roundedValue L lambda (indexOf g) ∧
            Theorem33.roundedValue L lambda (indexOf g) <
              v g + L / ((lambda : ℝ) ^ 2)) →
        (∀ k : Theorem33.RoundedValueIndex lambda,
          combinedSupply k =
            paper_lmms_theorem_3_3_roundedGoodsSupplyOfGoods indexOf highGoods k +
              Theorem33.lowGoodsAggregatedSupply L lambda (lowGoods.sum v) k) →
        (∑ k : Theorem33.RoundedValueIndex lambda,
            (combinedSupply k : ℝ) * Theorem33.roundedValue L lambda k) =
          (Fintype.card SourceAgent : ℝ) * LR) :=
  LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_concrete_ip_and_search_with_auto_cap_ratio_guarantee_of_source_average_no_top_of_margin
    hepsilon_pos hepsilon_le_one cert highGoods lowGoods v hlambda hL hhigh
    hlow hmargin hsource_average haverage

/--
Theorem 3.3 Claim-3.4 auto-cap source-average concrete-IP/search summary
endpoint: public alias for the raw comparison/search IP-equation summary
before adjoining the final rounded-instance guarantee.
-/
def theorem3_3_claim34_auto_cap_source_average_concrete_ip_search_summary_exists :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_concrete_ip_and_search_summary_with_auto_cap_of_source_average_no_top_of_margin

/--
Theorem 3.3 Claim-3.4 auto-cap source-average concrete-IP/search full-summary
ratio endpoint: conditional public alias exposing the common capped comparison-IP
and selected-search-IP summaries under the generated source-average cap and
supplied rounded-average identity.
-/
def theorem3_3_claim34_auto_cap_source_average_concrete_ip_search_full_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_auto_cap_concrete_ip_and_search_full_summary_with_ratio_guarantee_of_source_average_no_top_of_margin

/--
Theorem 3.3 Claim-3.4 auto-cap source-average concrete-IP/search summary ratio
endpoint: conditional on the supplied source-average and rounded-average
identities, exposes both the comparison IP equations and the selected search IP
equations, plus the final rounded-instance guarantee.
-/
def theorem3_3_claim34_auto_cap_source_average_concrete_ip_search_summary_ratio_endpoint
    {SourceAgent SourceItem Alloc : Type*}
    [Fintype SourceAgent] [Nonempty SourceAgent] [DecidableEq SourceAgent]
    [DecidableEq SourceItem]
    {M : Theorem33.IdenticalUtilitiesModel SourceAgent SourceItem Alloc}
    {L LR epsilon : ℝ} {lambda : ℕ} {optimal : Alloc}
    (hepsilon_pos : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1)
    (cert : Theorem33.RoundedInstanceSearchCertificate M L epsilon lambda optimal)
    (highGoods lowGoods : Finset SourceItem) (v : SourceItem → ℝ)
    (hlambda : 1 < lambda) (hL : 0 < L)
    (hhigh :
      ∀ g : SourceItem, g ∈ highGoods →
        L / (lambda : ℝ) < v g ∧ v g < L)
    (hlow :
      ∀ g : SourceItem, g ∈ lowGoods →
        0 ≤ v g ∧ v g < L / (lambda : ℝ))
    (hmargin :
      ∀ g : SourceItem, g ∈ highGoods →
        v g + L / ((lambda : ℝ) ^ 2) ≤ L)
    (hsource_average :
      highGoods.sum v + lowGoods.sum v =
        (Fintype.card SourceAgent : ℝ) * L)
    (haverage :
      ∀ (indexOf : SourceItem → Theorem33.RoundedValueIndex lambda)
        (combinedSupply : Theorem33.RoundedValueIndex lambda → ℕ),
        (∀ g : SourceItem, g ∈ highGoods →
          v g ≤ Theorem33.roundedValue L lambda (indexOf g) ∧
            Theorem33.roundedValue L lambda (indexOf g) <
              v g + L / ((lambda : ℝ) ^ 2)) →
        (∀ k : Theorem33.RoundedValueIndex lambda,
          combinedSupply k =
            paper_lmms_theorem_3_3_roundedGoodsSupplyOfGoods indexOf highGoods k +
              Theorem33.lowGoodsAggregatedSupply L lambda (lowGoods.sum v) k) →
        (∑ k : Theorem33.RoundedValueIndex lambda,
            (combinedSupply k : ℝ) * Theorem33.roundedValue L lambda k) =
          (Fintype.card SourceAgent : ℝ) * LR) :=
  LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_concrete_ip_and_search_summary_with_auto_cap_ratio_guarantee_of_source_average_no_top_of_margin
    hepsilon_pos hepsilon_le_one cert highGoods lowGoods v hlambda hL hhigh
    hlow hmargin hsource_average haverage

/--
Theorem 3.3 Claim-3.4 auto-cap source-average explicit-size endpoint: public
alias for the raw generated-cap size summary before adjoining the final
rounded-instance guarantee.
-/
def theorem3_3_claim34_auto_cap_source_average_explicit_size_summary_exists :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_concrete_ip_and_search_explicit_size_summary_with_auto_cap_of_source_average_no_top_of_margin

/--
Theorem 3.3 Claim-3.4 auto-cap source-average explicit-size ratio endpoint:
under the supplied source-average and rounded-average identities, keeps the
computed cap as a result-level `let` and exposes the explicit `2 * lambda + 5`
value-pair search-space bound with the final guarantee.
-/
def theorem3_3_claim34_auto_cap_source_average_explicit_size_ratio_endpoint
    {SourceAgent SourceItem Alloc : Type*}
    [Fintype SourceAgent] [Nonempty SourceAgent] [DecidableEq SourceAgent]
    [DecidableEq SourceItem]
    {M : Theorem33.IdenticalUtilitiesModel SourceAgent SourceItem Alloc}
    {L LR epsilon : ℝ} {lambda : ℕ} {optimal : Alloc}
    (hepsilon_pos : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1)
    (cert : Theorem33.RoundedInstanceSearchCertificate M L epsilon lambda optimal)
    (highGoods lowGoods : Finset SourceItem) (v : SourceItem → ℝ)
    (hlambda : 1 < lambda) (hL : 0 < L)
    (hhigh :
      ∀ g : SourceItem, g ∈ highGoods →
        L / (lambda : ℝ) < v g ∧ v g < L)
    (hlow :
      ∀ g : SourceItem, g ∈ lowGoods →
        0 ≤ v g ∧ v g < L / (lambda : ℝ))
    (hmargin :
      ∀ g : SourceItem, g ∈ highGoods →
        v g + L / ((lambda : ℝ) ^ 2) ≤ L)
    (hsource_average :
      highGoods.sum v + lowGoods.sum v =
        (Fintype.card SourceAgent : ℝ) * L)
    (haverage :
      ∀ (indexOf : SourceItem → Theorem33.RoundedValueIndex lambda)
        (combinedSupply : Theorem33.RoundedValueIndex lambda → ℕ),
        (∀ g : SourceItem, g ∈ highGoods →
          v g ≤ Theorem33.roundedValue L lambda (indexOf g) ∧
            Theorem33.roundedValue L lambda (indexOf g) <
              v g + L / ((lambda : ℝ) ^ 2)) →
        (∀ k : Theorem33.RoundedValueIndex lambda,
          combinedSupply k =
            paper_lmms_theorem_3_3_roundedGoodsSupplyOfGoods indexOf highGoods k +
              Theorem33.lowGoodsAggregatedSupply L lambda (lowGoods.sum v) k) →
        (∑ k : Theorem33.RoundedValueIndex lambda,
            (combinedSupply k : ℝ) * Theorem33.roundedValue L lambda k) =
          (Fintype.card SourceAgent : ℝ) * LR) :=
  LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_concrete_ip_and_search_explicit_size_summary_with_auto_cap_ratio_guarantee_of_source_average_no_top_of_margin
    hepsilon_pos hepsilon_le_one cert highGoods lowGoods v hlambda hL hhigh
    hlow hmargin hsource_average haverage

/--
Theorem 3.3 Claim-3.4 auto-cap source-average explicit cap-count endpoint:
public alias for the raw generated cap-count summary before adjoining the
final rounded-instance guarantee.
-/
def theorem3_3_claim34_auto_cap_source_average_explicit_cap_count_summary_exists :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_concrete_ip_and_search_explicit_cap_count_summary_with_auto_cap_of_source_average_no_top_of_margin

/--
Theorem 3.3 Claim-3.4 auto-cap source-average explicit cap-count ratio
endpoint: under the supplied source-average and rounded-average identities,
exposes the generated cap existentially together with its `2 * lambda + 4`
bound and the final rounded-instance guarantee.
-/
def theorem3_3_claim34_auto_cap_source_average_explicit_cap_count_ratio_endpoint
    {SourceAgent SourceItem Alloc : Type*}
    [Fintype SourceAgent] [Nonempty SourceAgent] [DecidableEq SourceAgent]
    [DecidableEq SourceItem]
    {M : Theorem33.IdenticalUtilitiesModel SourceAgent SourceItem Alloc}
    {L LR epsilon : ℝ} {lambda : ℕ} {optimal : Alloc}
    (hepsilon_pos : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1)
    (cert : Theorem33.RoundedInstanceSearchCertificate M L epsilon lambda optimal)
    (highGoods lowGoods : Finset SourceItem) (v : SourceItem → ℝ)
    (hlambda : 1 < lambda) (hL : 0 < L)
    (hhigh :
      ∀ g : SourceItem, g ∈ highGoods →
        L / (lambda : ℝ) < v g ∧ v g < L)
    (hlow :
      ∀ g : SourceItem, g ∈ lowGoods →
        0 ≤ v g ∧ v g < L / (lambda : ℝ))
    (hmargin :
      ∀ g : SourceItem, g ∈ highGoods →
        v g + L / ((lambda : ℝ) ^ 2) ≤ L)
    (hsource_average :
      highGoods.sum v + lowGoods.sum v =
        (Fintype.card SourceAgent : ℝ) * L)
    (haverage :
      ∀ (indexOf : SourceItem → Theorem33.RoundedValueIndex lambda)
        (combinedSupply : Theorem33.RoundedValueIndex lambda → ℕ),
        (∀ g : SourceItem, g ∈ highGoods →
          v g ≤ Theorem33.roundedValue L lambda (indexOf g) ∧
            Theorem33.roundedValue L lambda (indexOf g) <
              v g + L / ((lambda : ℝ) ^ 2)) →
        (∀ k : Theorem33.RoundedValueIndex lambda,
          combinedSupply k =
            paper_lmms_theorem_3_3_roundedGoodsSupplyOfGoods indexOf highGoods k +
              Theorem33.lowGoodsAggregatedSupply L lambda (lowGoods.sum v) k) →
        (∑ k : Theorem33.RoundedValueIndex lambda,
            (combinedSupply k : ℝ) * Theorem33.roundedValue L lambda k) =
          (Fintype.card SourceAgent : ℝ) * LR) :=
  LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_concrete_ip_and_search_explicit_cap_count_summary_with_auto_cap_ratio_guarantee_of_source_average_no_top_of_margin
    hepsilon_pos hepsilon_le_one cert highGoods lowGoods v hlambda hL hhigh
    hlow hmargin hsource_average haverage

/--
Theorem 3.3 Claim-3.4 auto-cap source-average explicit search-space endpoint:
public alias for the raw generated search-space summary before adjoining the
final rounded-instance guarantee.
-/
def theorem3_3_claim34_auto_cap_source_average_explicit_search_space_summary_exists :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_concrete_ip_and_search_explicit_search_space_summary_with_auto_cap_of_source_average_no_top_of_margin

/--
Theorem 3.3 Claim-3.4 auto-cap source-average explicit search-space ratio
endpoint: under the supplied source-average and rounded-average identities,
exposes the linear generated cap, capped type-space bound, value-pair
search-space bound, and the final rounded-instance guarantee.
-/
def theorem3_3_claim34_auto_cap_source_average_explicit_search_space_ratio_endpoint
    {SourceAgent SourceItem Alloc : Type*}
    [Fintype SourceAgent] [Nonempty SourceAgent] [DecidableEq SourceAgent]
    [DecidableEq SourceItem]
    {M : Theorem33.IdenticalUtilitiesModel SourceAgent SourceItem Alloc}
    {L LR epsilon : ℝ} {lambda : ℕ} {optimal : Alloc}
    (hepsilon_pos : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1)
    (cert : Theorem33.RoundedInstanceSearchCertificate M L epsilon lambda optimal)
    (highGoods lowGoods : Finset SourceItem) (v : SourceItem → ℝ)
    (hlambda : 1 < lambda) (hL : 0 < L)
    (hhigh :
      ∀ g : SourceItem, g ∈ highGoods →
        L / (lambda : ℝ) < v g ∧ v g < L)
    (hlow :
      ∀ g : SourceItem, g ∈ lowGoods →
        0 ≤ v g ∧ v g < L / (lambda : ℝ))
    (hmargin :
      ∀ g : SourceItem, g ∈ highGoods →
        v g + L / ((lambda : ℝ) ^ 2) ≤ L)
    (hsource_average :
      highGoods.sum v + lowGoods.sum v =
        (Fintype.card SourceAgent : ℝ) * L)
    (haverage :
      ∀ (indexOf : SourceItem → Theorem33.RoundedValueIndex lambda)
        (combinedSupply : Theorem33.RoundedValueIndex lambda → ℕ),
        (∀ g : SourceItem, g ∈ highGoods →
          v g ≤ Theorem33.roundedValue L lambda (indexOf g) ∧
            Theorem33.roundedValue L lambda (indexOf g) <
              v g + L / ((lambda : ℝ) ^ 2)) →
        (∀ k : Theorem33.RoundedValueIndex lambda,
          combinedSupply k =
            paper_lmms_theorem_3_3_roundedGoodsSupplyOfGoods indexOf highGoods k +
              Theorem33.lowGoodsAggregatedSupply L lambda (lowGoods.sum v) k) →
        (∑ k : Theorem33.RoundedValueIndex lambda,
            (combinedSupply k : ℝ) * Theorem33.roundedValue L lambda k) =
          (Fintype.card SourceAgent : ℝ) * LR) :=
  LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_concrete_ip_and_search_explicit_search_space_summary_with_auto_cap_ratio_guarantee_of_source_average_no_top_of_margin
    hepsilon_pos hepsilon_le_one cert highGoods lowGoods v hlambda hL hhigh
    hlow hmargin hsource_average haverage

/--
Theorem 3.3 Claim-3.4 auto-cap source-average explicit IP-variable endpoint:
public alias for the raw IP-variable summary before adjoining the final
rounded-instance guarantee.
-/
def theorem3_3_claim34_auto_cap_source_average_explicit_ip_variable_summary_exists :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_concrete_ip_and_search_explicit_ip_variable_summary_with_auto_cap_of_source_average_no_top_of_margin

/--
Theorem 3.3 Claim-3.4 auto-cap source-average explicit IP-variable ratio
endpoint: under the supplied source-average and rounded-average identities,
additionally exposes the comparison-IP and chosen-search-IP value-window
cardinality bounds, plus the final guarantee.
-/
def theorem3_3_claim34_auto_cap_source_average_explicit_ip_variable_ratio_endpoint
    {SourceAgent SourceItem Alloc : Type*}
    [Fintype SourceAgent] [Nonempty SourceAgent] [DecidableEq SourceAgent]
    [DecidableEq SourceItem]
    {M : Theorem33.IdenticalUtilitiesModel SourceAgent SourceItem Alloc}
    {L LR epsilon : ℝ} {lambda : ℕ} {optimal : Alloc}
    (hepsilon_pos : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1)
    (cert : Theorem33.RoundedInstanceSearchCertificate M L epsilon lambda optimal)
    (highGoods lowGoods : Finset SourceItem) (v : SourceItem → ℝ)
    (hlambda : 1 < lambda) (hL : 0 < L)
    (hhigh :
      ∀ g : SourceItem, g ∈ highGoods →
        L / (lambda : ℝ) < v g ∧ v g < L)
    (hlow :
      ∀ g : SourceItem, g ∈ lowGoods →
        0 ≤ v g ∧ v g < L / (lambda : ℝ))
    (hmargin :
      ∀ g : SourceItem, g ∈ highGoods →
        v g + L / ((lambda : ℝ) ^ 2) ≤ L)
    (hsource_average :
      highGoods.sum v + lowGoods.sum v =
        (Fintype.card SourceAgent : ℝ) * L)
    (haverage :
      ∀ (indexOf : SourceItem → Theorem33.RoundedValueIndex lambda)
        (combinedSupply : Theorem33.RoundedValueIndex lambda → ℕ),
        (∀ g : SourceItem, g ∈ highGoods →
          v g ≤ Theorem33.roundedValue L lambda (indexOf g) ∧
            Theorem33.roundedValue L lambda (indexOf g) <
              v g + L / ((lambda : ℝ) ^ 2)) →
        (∀ k : Theorem33.RoundedValueIndex lambda,
          combinedSupply k =
            paper_lmms_theorem_3_3_roundedGoodsSupplyOfGoods indexOf highGoods k +
              Theorem33.lowGoodsAggregatedSupply L lambda (lowGoods.sum v) k) →
        (∑ k : Theorem33.RoundedValueIndex lambda,
            (combinedSupply k : ℝ) * Theorem33.roundedValue L lambda k) =
          (Fintype.card SourceAgent : ℝ) * LR) :=
  LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_concrete_ip_and_search_explicit_ip_variable_summary_with_auto_cap_ratio_guarantee_of_source_average_no_top_of_margin
    hepsilon_pos hepsilon_le_one cert highGoods lowGoods v hlambda hL hhigh
    hlow hmargin hsource_average haverage

/--
Theorem 3.3 Claim-3.4 auto-cap source-average explicit full-IP-constraint
endpoint: public alias for the raw full-IP-constraint summary before adjoining
the final rounded-instance guarantee.
-/
def theorem3_3_claim34_auto_cap_source_average_explicit_full_ip_constraint_summary_exists :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_concrete_ip_and_search_explicit_full_ip_constraint_summary_with_auto_cap_of_source_average_no_top_of_margin

/--
Theorem 3.3 Claim-3.4 auto-cap source-average explicit full-IP-constraint ratio
endpoint: under the supplied source-average and rounded-average identities,
additionally records that the comparison IP and chosen search IP assign zero
multiplicity outside their selected capped value windows.
-/
def theorem3_3_claim34_auto_cap_source_average_explicit_full_ip_constraint_ratio_endpoint
    {SourceAgent SourceItem Alloc : Type*}
    [Fintype SourceAgent] [Nonempty SourceAgent] [DecidableEq SourceAgent]
    [DecidableEq SourceItem]
    {M : Theorem33.IdenticalUtilitiesModel SourceAgent SourceItem Alloc}
    {L LR epsilon : ℝ} {lambda : ℕ} {optimal : Alloc}
    (hepsilon_pos : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1)
    (cert : Theorem33.RoundedInstanceSearchCertificate M L epsilon lambda optimal)
    (highGoods lowGoods : Finset SourceItem) (v : SourceItem → ℝ)
    (hlambda : 1 < lambda) (hL : 0 < L)
    (hhigh :
      ∀ g : SourceItem, g ∈ highGoods →
        L / (lambda : ℝ) < v g ∧ v g < L)
    (hlow :
      ∀ g : SourceItem, g ∈ lowGoods →
        0 ≤ v g ∧ v g < L / (lambda : ℝ))
    (hmargin :
      ∀ g : SourceItem, g ∈ highGoods →
        v g + L / ((lambda : ℝ) ^ 2) ≤ L)
    (hsource_average :
      highGoods.sum v + lowGoods.sum v =
        (Fintype.card SourceAgent : ℝ) * L)
    (haverage :
      ∀ (indexOf : SourceItem → Theorem33.RoundedValueIndex lambda)
        (combinedSupply : Theorem33.RoundedValueIndex lambda → ℕ),
        (∀ g : SourceItem, g ∈ highGoods →
          v g ≤ Theorem33.roundedValue L lambda (indexOf g) ∧
            Theorem33.roundedValue L lambda (indexOf g) <
              v g + L / ((lambda : ℝ) ^ 2)) →
        (∀ k : Theorem33.RoundedValueIndex lambda,
          combinedSupply k =
            paper_lmms_theorem_3_3_roundedGoodsSupplyOfGoods indexOf highGoods k +
              Theorem33.lowGoodsAggregatedSupply L lambda (lowGoods.sum v) k) →
        (∑ k : Theorem33.RoundedValueIndex lambda,
            (combinedSupply k : ℝ) * Theorem33.roundedValue L lambda k) =
          (Fintype.card SourceAgent : ℝ) * LR) :=
  LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_concrete_ip_and_search_explicit_full_ip_constraint_summary_with_auto_cap_ratio_guarantee_of_source_average_no_top_of_margin
    hepsilon_pos hepsilon_le_one cert highGoods lowGoods v hlambda hL hhigh
    hlow hmargin hsource_average haverage

/--
Theorem 3.3 Claim-3.4 generated type-assignment/search endpoint: public alias
for choosing the high/low rounding map and rounded supply, proving no-top
support, and exposing the raw finite value-pair search witness.
-/
def theorem3_3_claim34_type_assignment_search_certificate_exists :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_value_pair_type_assignment_of_claim34_no_top_of_margin

/--
Theorem 3.3 Claim-3.4 generated type-assignment summary endpoint: public alias
for choosing the high/low rounding map and rounded supply, proving no-top
support, and exposing selected-pair admissibility with the search comparison.
-/
def theorem3_3_claim34_type_assignment_summary_exists :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_value_pair_type_assignment_summary_of_claim34_no_top_of_margin

/--
Theorem 3.3 Claim-3.4 type-assignment ratio endpoint: the uncapped no-top
Claim-3.4 bridge, packaged with the final rounded-instance `(1 + epsilon)`
ratio guarantee.
-/
def theorem3_3_claim34_type_assignment_ratio_endpoint
    {SourceAgent SourceItem Alloc : Type*}
    [Fintype SourceAgent] [Nonempty SourceAgent] [DecidableEq SourceAgent]
    [DecidableEq SourceItem]
    {M : Theorem33.IdenticalUtilitiesModel SourceAgent SourceItem Alloc}
    {L epsilon : ℝ} {lambda : ℕ} {optimal : Alloc}
    (hepsilon_pos : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1)
    (cert : Theorem33.RoundedInstanceSearchCertificate M L epsilon lambda optimal)
    (highGoods lowGoods : Finset SourceItem) (v : SourceItem → ℝ)
    (hlambda : 1 < lambda) (hL : 0 < L)
    (hhigh :
      ∀ g : SourceItem, g ∈ highGoods →
        L / (lambda : ℝ) < v g ∧ v g < L)
    (hlow :
      ∀ g : SourceItem, g ∈ lowGoods →
        0 ≤ v g ∧ v g < L / (lambda : ℝ))
    (hmargin :
      ∀ g : SourceItem, g ∈ highGoods →
        v g + L / ((lambda : ℝ) ^ 2) ≤ L)
    (haverage :
      ∀ (indexOf : SourceItem → Theorem33.RoundedValueIndex lambda)
        (combinedSupply : Theorem33.RoundedValueIndex lambda → ℕ),
        (∀ g : SourceItem, g ∈ highGoods →
          v g ≤ Theorem33.roundedValue L lambda (indexOf g) ∧
            Theorem33.roundedValue L lambda (indexOf g) <
              v g + L / ((lambda : ℝ) ^ 2)) →
        (∀ k : Theorem33.RoundedValueIndex lambda,
          combinedSupply k =
            paper_lmms_theorem_3_3_roundedGoodsSupplyOfGoods indexOf highGoods k +
              Theorem33.lowGoodsAggregatedSupply L lambda (lowGoods.sum v) k) →
        (∑ k : Theorem33.RoundedValueIndex lambda,
            (combinedSupply k : ℝ) * Theorem33.roundedValue L lambda k) =
          (Fintype.card SourceAgent : ℝ) * L) :=
  LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_claim34_type_assignment_with_ratio_guarantee_no_top_of_margin
    hepsilon_pos hepsilon_le_one cert highGoods lowGoods v hlambda hL hhigh
    hlow hmargin haverage

/--
Theorem 3.3 Claim-3.4 type-assignment summary ratio endpoint: public alias
pairing the generated no-top type-assignment/search summary with the final
rounded-instance `(1 + epsilon)` guarantee.
-/
def theorem3_3_claim34_type_assignment_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_claim34_type_assignment_summary_with_ratio_guarantee_no_top_of_margin

/--
Theorem 3.3 Claim-3.4 materialized-search ratio endpoint: public alias for the
generated high/low rounded supply bridge preserving the bounded materialized
allocation/search payload.
-/
def theorem3_3_claim34_materialized_search_certificate_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_value_pair_search_certificate_with_ratio_guarantee_of_claim34_no_top_of_margin

/--
Theorem 3.3 Claim-3.4 materialized-search summary ratio endpoint: public alias
for the generated high/low rounded supply bridge, additionally recording that
the finite search's selected pair is admissible.
-/
def theorem3_3_claim34_materialized_search_certificate_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_value_pair_search_certificate_summary_with_ratio_guarantee_of_claim34_no_top_of_margin

/--
Theorem 3.3 Claim-3.4 concrete-IP/search ratio endpoint: public alias for the
generated high/low rounded supply bridge that packages the feasible rounded
type assignment as an uncapped concrete IP certificate.
-/
def theorem3_3_claim34_concrete_ip_search_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_concrete_ip_and_search_with_ratio_guarantee_of_claim34_no_top_of_margin

/--
Theorem 3.3 Claim-3.4 concrete-IP/search summary ratio endpoint: public alias
for the generated high/low rounded supply bridge that keeps the concrete IP
payload and selected-pair admissibility.
-/
def theorem3_3_claim34_concrete_ip_search_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_concrete_ip_and_search_summary_with_ratio_guarantee_of_claim34_no_top_of_margin

/--
Theorem 3.3 Claim-3.4 concrete-IP/search full-summary ratio endpoint: public
alias for the generated high/low rounded supply bridge exposing common full
summaries for both the concrete IP and selected finite-search IP.
-/
def theorem3_3_claim34_concrete_ip_search_full_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_combined_high_low_concrete_ip_and_search_full_summary_with_ratio_guarantee_of_claim34_no_top_of_margin

/--
Claim 3.4 generic certificate wrapper: public alias turning a
ratio-nonincreasing bounded reallocation from an optimum into a Claim 3.4
certificate.
-/
def claim3_4_bounded_optimal_certificate :=
  @LMMS04FairDivision.paper_lmms_claim_3_4_bounded_optimal_certificate

/--
Claim 3.4 generic certificate projection: public alias exposing optimality,
per-agent load windows, and induced min/max load windows from a Claim 3.4
certificate.
-/
def claim3_4_certificate_projection_summary :=
  @LMMS04FairDivision.paper_lmms_claim_3_4_certificate_projection_summary

/--
Claim 3.4 generic certificate explicit-bounds projection: public alias
splitting the per-agent and min/max load windows into lower/upper inequalities.
-/
def claim3_4_certificate_explicit_bounds_summary :=
  @LMMS04FairDivision.paper_lmms_claim_3_4_certificate_explicit_bounds_summary

/--
Claim 3.4 generic finite-descent wrapper: public alias for producing a
bounded optimal allocation from a natural-number descent step.
-/
def claim3_4_bounded_optimal_of_finite_descent :=
  @LMMS04FairDivision.paper_lmms_claim_3_4_bounded_optimal_of_finite_descent

/--
Claim 3.4 generic branching-descent wrapper: public alias for the
overfull-cardinality/min-load lexicographic finite-descent assembly.
-/
def claim3_4_bounded_optimal_of_branching_potential_descent :=
  @LMMS04FairDivision.paper_lmms_claim_3_4_bounded_optimal_of_branching_potential_descent

/--
Claim 3.4 one-step support: public alias for the load-ratio monotonicity
certificate of moving load from a high source to a low target.
-/
def claim3_4_load_ratio_nonincreasing_of_move :=
  @LMMS04FairDivision.paper_lmms_claim_3_4_load_ratio_nonincreasing_of_move

/--
Claim 3.4 local move support: public alias for the concrete one-good
reallocation certificate from a high source bundle to a low target bundle.
-/
def claim3_4_local_reallocation_certificate_of_low_target_high_source :=
  @LMMS04FairDivision.paper_lmms_claim_3_4_local_reallocation_certificate_of_low_target_high_source

/--
Claim 3.4 local finite-descent wrapper: public alias for assembling local
high-source moves into a bounded optimal allocation.
-/
def claim3_4_bounded_optimal_of_local_reallocation_descent :=
  @LMMS04FairDivision.paper_lmms_claim_3_4_bounded_optimal_of_local_reallocation_descent

/--
Claim 3.4 min/max trichotomy step: public alias for the source branch step
used by the lexicographic finite descent.
-/
def claim3_4_branch_step_of_minmax_source_trichotomy :=
  @LMMS04FairDivision.paper_lmms_claim_3_4_branch_step_of_minmax_source_trichotomy

/--
Claim 3.4 min/max source-data wrapper: public alias assembling average-load,
min/max, ownership, and move-update obligations into the bounded optimum.
-/
def claim3_4_bounded_optimal_of_minmax_source_trichotomy :=
  @LMMS04FairDivision.paper_lmms_claim_3_4_bounded_optimal_of_minmax_source_trichotomy

/--
Claim 3.4 concrete min/max source-data wrapper: public alias for the canonical
min/max-load specialization of the min/max source trichotomy endpoint.
-/
def claim3_4_bounded_optimal_of_concrete_minmax_source_trichotomy :=
  @LMMS04FairDivision.paper_lmms_claim_3_4_bounded_optimal_of_concrete_minmax_source_trichotomy

/--
Claim 3.4 source-domain exact-allocation helper: public alias for the
owner-filter exact allocation construction.
-/
def claim3_4_isAllocationOf_filter_owner :=
  @LMMS04FairDivision.paper_lmms_isAllocationOf_filter_owner

/--
Claim 3.4 source-domain exact-allocation helper: public alias constructing an
owner map from an exact allocation, recovering the allocation by owner filters.
-/
def claim3_4_exists_owner_filter_eq_of_isAllocationOf :=
  @LMMS04FairDivision.paper_lmms_exists_owner_filter_eq_of_isAllocationOf

/--
Theorem 3.3 low-good partition support: public alias turning an exact
low-good partition with per-agent load estimates into equivalent owner-map
load estimates.
-/
def theorem3_3_exists_low_goods_owner_load_estimates_of_exact_low_partition :=
  @LMMS04FairDivision.paper_lmms_exists_low_goods_owner_load_estimates_of_exact_low_partition

/--
Theorem 3.3 low-good partition support: public alias showing owner-map load
estimates are equivalent to an exact low partition with the same estimates.
-/
def theorem3_3_exists_low_goods_owner_load_estimates_iff_exists_exact_low_partition :=
  @LMMS04FairDivision.paper_lmms_exists_low_goods_owner_load_estimates_iff_exists_exact_low_partition

/--
Claim 3.4 source-domain exact-allocation helper: public alias constructing an
exact nonempty allocation from a surjective owner map.
-/
def claim3_4_exists_nonempty_exact_allocation_of_surjective_owner :=
  @LMMS04FairDivision.paper_lmms_exists_nonempty_exact_allocation_of_surjective_owner

/--
Claim 3.4 source-domain owner helper: public alias constructing a surjective
owner map from strictly small positive goods with total load `#agents * L`.
-/
def claim3_4_exists_surjective_owner_of_total_strictly_small_positive_values :=
  @LMMS04FairDivision.paper_lmms_exists_surjective_owner_of_total_strictly_small_positive_values

/--
Claim 3.4 exact-allocation sum helper: public alias showing an exact
allocation's bundle-value sum equals the value of the allocated goods.
-/
def claim3_4_isAllocationOf_sum_bundle_values_eq_sum_goods :=
  @LMMS04FairDivision.paper_lmms_isAllocationOf_sum_bundle_values_eq_sum_goods

/--
Claim 3.4 exact-allocation count helper: public alias showing an exact
allocation's per-index bundle counts equal the corresponding goods count.
-/
def claim3_4_isAllocationOf_sum_bundle_index_counts_eq_goods_count :=
  @LMMS04FairDivision.paper_lmms_isAllocationOf_sum_bundle_index_counts_eq_goods_count

/--
Claim 3.4 exact-allocation move helper: public alias showing a one-good move
preserves exact allocation of the same goods.
-/
def claim3_4_isAllocationOf_moveBundle :=
  @LMMS04FairDivision.paper_lmms_isAllocationOf_moveBundle

/--
Claim 3.4 exact-allocation nonempty move helper: public alias preserving
nonempty bundles when the donor keeps positive load after the move.
-/
def claim3_4_moveBundle_nonempty_of_source_load_gt_item :=
  @LMMS04FairDivision.paper_lmms_moveBundle_nonempty_of_source_load_gt_item

/--
Claim 3.4 exact-allocation gap move helper: public alias preserving nonempty
bundles from the paper's min/max gap condition.
-/
def claim3_4_moveBundle_nonempty_of_gap :=
  @LMMS04FairDivision.paper_lmms_moveBundle_nonempty_of_gap

/--
Claim 3.4 exact-allocation obstruction helper: public alias showing an empty
bundle forces the exact allocation's minimum common load to be zero under
nonnegative item values.
-/
def claim3_4_minCommonLoad_eq_zero_of_exact_allocation_empty_bundle :=
  @LMMS04FairDivision.paper_lmms_claim_3_4_minCommonLoad_eq_zero_of_exact_allocation_empty_bundle

/--
Claim 3.4 exact-allocation positivity helper: public alias showing positive
goods and nonempty bundles force positive minimum common load.
-/
def claim3_4_minCommonLoad_pos_of_exact_allocation_each_agent_nonempty :=
  @LMMS04FairDivision.paper_lmms_claim_3_4_minCommonLoad_pos_of_exact_allocation_each_agent_nonempty

/--
Claim 3.4 exact-allocation nonempty helper: public alias extracting nonempty
bundles from positive minimum common load.
-/
def claim3_4_each_agent_nonempty_of_minCommonLoad_pos :=
  @LMMS04FairDivision.paper_lmms_claim_3_4_each_agent_nonempty_of_minCommonLoad_pos

/--
Claim 3.4 exact nonempty branch step: public alias for the concrete min/max
trichotomy step over exact allocations of positive small goods.
-/
def claim3_4_branch_step_of_exact_nonempty_positive_goods :=
  @LMMS04FairDivision.paper_lmms_claim_3_4_branch_step_of_exact_nonempty_positive_goods

/--
Claim 3.4 exact positive-minimum finite-descent selector: public alias for the
source-domain descent wrapper over positive-minimum exact allocations.
-/
def claim3_4_bounded_optimal_on_exact_positive_min_allocations :=
  @LMMS04FairDivision.paper_lmms_claim_3_4_bounded_optimal_on_exact_positive_min_allocations

/--
Claim 3.4 exact positive-minimum finite-descent selector with concrete
potentials: public alias for the branching-potential specialization.
-/
def claim3_4_bounded_optimal_on_exact_positive_min_allocations_branching_potentials :=
  @LMMS04FairDivision.paper_lmms_claim_3_4_bounded_optimal_on_exact_positive_min_allocations_branching_potentials

/--
Claim 3.4 exact nonempty positive-goods selector: public alias for the
finite-descent wrapper over exact nonempty positive-good allocations.
-/
def claim3_4_bounded_optimal_on_exact_nonempty_positive_goods :=
  @LMMS04FairDivision.paper_lmms_claim_3_4_bounded_optimal_on_exact_nonempty_positive_goods

/--
Claim 3.4 exact nonempty positive-goods selector with concrete potentials:
public alias for the branching-potential specialization.
-/
def claim3_4_bounded_optimal_on_exact_nonempty_positive_goods_branching_potentials :=
  @LMMS04FairDivision.paper_lmms_claim_3_4_bounded_optimal_on_exact_nonempty_positive_goods_branching_potentials

/--
Claim 3.4 exact nonempty positive-goods existence selector: public alias for
choosing a bounded exact nonempty optimum from any feasible exact nonempty
allocation.
-/
def claim3_4_exists_bounded_optimal_on_exact_nonempty_positive_goods :=
  @LMMS04FairDivision.paper_lmms_claim_3_4_exists_bounded_optimal_on_exact_nonempty_positive_goods

/--
Claim 3.4 exact owner-map selector: public alias for deriving a bounded exact
nonempty optimum from a surjective owner map.
-/
def claim3_4_exists_bounded_optimal_of_surjective_owner :=
  @LMMS04FairDivision.paper_lmms_claim_3_4_exists_bounded_optimal_of_surjective_owner

/--
Claim 3.4 all-goods source-domain selector: public alias deriving a bounded
exact nonempty optimum from exact total load, positive values, and strict
smallness of every finite source good.
-/
def claim3_4_exists_bounded_optimal_of_total_strictly_small_positive_goods :=
  @LMMS04FairDivision.paper_lmms_claim_3_4_exists_bounded_optimal_of_total_strictly_small_positive_goods

/--
Claim 3.4 exact-allocation source-domain selector with concrete potentials:
public alias for the nonempty-positive-goods wrapper over all exact
allocations.
-/
def claim3_4_bounded_optimal_on_exact_allocations_from_nonempty_positive_goods_branching_potentials :=
  @LMMS04FairDivision.paper_lmms_claim_3_4_bounded_optimal_on_exact_allocations_from_nonempty_positive_goods_branching_potentials

/--
Claim 3.4 exact-allocation source-domain selector: public alias for the
nonempty-positive-goods wrapper over all exact allocations.
-/
def claim3_4_bounded_optimal_on_exact_allocations_from_nonempty_positive_goods :=
  @LMMS04FairDivision.paper_lmms_claim_3_4_bounded_optimal_on_exact_allocations_from_nonempty_positive_goods

/--
Claim 3.4 exact-allocation summary: public alias projecting the bounded
optimal exact-allocation theorem into exact allocation, optimality, and
per-agent load-window facts.
-/
def claim3_4_bounded_optimal_exact_allocations_summary :=
  @LMMS04FairDivision.paper_lmms_claim_3_4_bounded_optimal_exact_allocations_summary

/--
Claim 3.4 exact-allocation explicit-bounds summary: public alias projecting
the bounded exact allocation into the two per-agent load-window inequalities.
-/
def claim3_4_bounded_optimal_exact_allocations_explicit_bounds_summary :=
  @LMMS04FairDivision.paper_lmms_claim_3_4_bounded_optimal_exact_allocations_explicit_bounds_summary

/--
Claim 3.4: for exact finite allocations of positive small goods, if every
unbounded optimal bundle gives each agent some good, the high-source, low-only,
and strict upper-boundary branches combine into finite lexicographic descent,
yielding an optimal allocation whose every load lies between `L / 2` and `2L`.
-/
theorem claim3_4_bounded_optimal_of_exact_allocations_with_nonempty_positive_goods
    {SourceAgent SourceItem : Type*}
    [Fintype SourceAgent] [Fintype SourceItem] [Nonempty SourceAgent]
    [DecidableEq SourceAgent] [DecidableEq SourceItem]
    {goods : Finset SourceItem} {v : SourceItem → ℝ} {L : ℝ}
    (A₀ : Allocation SourceAgent SourceItem)
    (hA₀ :
      Theorem34.IsOptimalRatio
        (fun A : Allocation SourceAgent SourceItem =>
          Theorem34.loadRatio
            (Theorem34.minCommonLoad v A)
            (Theorem34.maxCommonLoad v A)) A₀)
    (hopt_alloc :
      ∀ A : Allocation SourceAgent SourceItem,
        Theorem34.IsOptimalRatio
          (fun C : Allocation SourceAgent SourceItem =>
            Theorem34.loadRatio
              (Theorem34.minCommonLoad v C)
              (Theorem34.maxCommonLoad v C)) A →
          IsAllocationOf A goods)
    (hL : 0 < L)
    (hgoods_load :
      Theorem34.commonLoad v goods = (Fintype.card SourceAgent : ℝ) * L)
    (hopt_owns :
      ∀ A : Allocation SourceAgent SourceItem,
        Theorem34.IsOptimalRatio
          (fun C : Allocation SourceAgent SourceItem =>
            Theorem34.loadRatio
              (Theorem34.minCommonLoad v C)
              (Theorem34.maxCommonLoad v C)) A →
          (¬ ∀ i : SourceAgent,
            Theorem34.boundedAroundAverage L (Theorem34.commonLoad v (A i))) →
          ∀ i : SourceAgent, ∃ g : SourceItem, g ∈ A i)
    (hgoods_pos : ∀ g : SourceItem, g ∈ goods → 0 < v g)
    (hgoods_lt : ∀ g : SourceItem, g ∈ goods → v g < L) :
    ∃ B : Allocation SourceAgent SourceItem,
      IsAllocationOf B goods ∧
        Theorem34.Claim34Certificate v L
          (fun A : Allocation SourceAgent SourceItem =>
            Theorem34.loadRatio
              (Theorem34.minCommonLoad v A)
              (Theorem34.maxCommonLoad v A))
          (fun A i => A i) B := by
  exact
    LMMS04FairDivision.paper_lmms_claim_3_4_bounded_optimal_of_exact_allocations_with_nonempty_positive_goods
      A₀ hA₀ hopt_alloc hL hgoods_load hopt_owns hgoods_pos hgoods_lt

/--
Claim 3.4 exact-allocation assembly: public alias for the positive-minimum
version over finite exact allocations.
-/
def claim3_4_bounded_optimal_of_exact_allocations :=
  @LMMS04FairDivision.paper_lmms_claim_3_4_bounded_optimal_of_exact_allocations

/--
Claim 3.4 exact-allocation assembly: public alias for the variant where
positive-valued goods in every unbounded optimal bundle imply the minimum-load
premise.
-/
def claim3_4_bounded_optimal_of_exact_allocations_with_positive_bundles :=
  @LMMS04FairDivision.paper_lmms_claim_3_4_bounded_optimal_of_exact_allocations_with_positive_bundles

/--
Claim 3.4 identical-utilities bridge: public alias lifting the concrete
min/max source-data assembly to a finite identical-utilities model.
-/
def claim3_4_bounded_optimal_of_identical_utilities_model :=
  @LMMS04FairDivision.paper_lmms_claim_3_4_bounded_optimal_of_identical_utilities_model

/--
Claim 3.4 identical-utilities summary: public alias projecting the model-level
certificate into load-ratio optimality and `allocationLoad` window bounds.
-/
def claim3_4_identical_utilities_model_load_summary :=
  @LMMS04FairDivision.paper_lmms_claim_3_4_identical_utilities_model_load_summary

/--
Theorem 3.3/Claim 3.4 bridge: public alias identifying the model minimum
allocation load with the concrete minimum common load.
-/
def theorem3_3_minAllocationLoad_eq_minCommonLoad :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_minAllocationLoad_eq_minCommonLoad

/--
Theorem 3.3/Claim 3.4 bridge: public alias identifying the model maximum
allocation load with the concrete maximum common load.
-/
def theorem3_3_maxAllocationLoad_eq_maxCommonLoad :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_maxAllocationLoad_eq_maxCommonLoad

/--
Theorem 3.3/Claim 3.4 bridge: public alias projecting per-agent allocation
load windows to the model-level minimum and maximum allocation loads.
-/
def theorem3_3_min_max_windows_of_allocation_load_windows :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_min_max_windows_of_allocation_load_windows

/--
Theorem 3.3/Claim 3.4 bridge: public alias for membership of the bounded
optimum's rounded min/max load pair in the finite value-pair search space.
-/
def theorem3_3_claim34_min_max_pair_mem_of_rounded_types :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_claim_3_4_min_max_pair_mem_of_rounded_types

/--
Theorem 3.3/Claim 3.4 min/max summary: public alias exposing min/max
load-window facts together with finite value-pair membership.
-/
def theorem3_3_claim34_min_max_window_and_pair_mem_of_rounded_types :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_claim_3_4_min_max_window_and_pair_mem_of_rounded_types

/--
Theorem 3.3/Claim 3.4 bridge: public alias converting a rounded type-IP
certificate for the min/max window into a value-pair IP certificate.
-/
def theorem3_3_claim34_value_pair_ip_certificate_of_rounded_types :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_claim_3_4_value_pair_ip_certificate_of_rounded_types

/--
Theorem 3.3 search optimality bridge: public alias comparing the finite
value-pair search result to a Claim-3.4 bounded optimum's load ratio.
-/
def theorem3_3_value_pair_search_ratio_le_claim34_min_max :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_value_pair_search_ratio_le_claim_3_4_min_max

/--
Theorem 3.3 search-existence bridge: public alias constructing a finite
value-pair search certificate against a Claim-3.4 bounded optimum.
-/
def theorem3_3_exists_value_pair_search_certificate_claim34_min_max :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_claim_3_4_min_max

/--
Theorem 3.3/Claim 3.4 min/max IP/search endpoint: public alias keeping the
constructed value-pair IP certificate with the finite-search witness before
adjoining the final rounded-instance guarantee.
-/
def theorem3_3_claim34_min_max_value_pair_ip_and_search_certificate_exists :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_ip_and_search_certificate_claim_3_4_min_max

/--
Theorem 3.3/Claim 3.4 min/max IP/search endpoint: compact public alias for
the same raw value-pair IP/search payload.
-/
def theorem3_3_claim34_min_max_value_pair_ip_search_certificate_exists :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_ip_and_search_certificate_claim_3_4_min_max

/--
Theorem 3.3/Claim 3.4 min/max IP/search payload summary: public alias
exposing the constructed value-pair IP window, type-space bound, player
equation, and selected-pair metadata.
-/
def theorem3_3_claim34_min_max_value_pair_ip_search_payload_summary :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_claim_3_4_min_max_ip_search_payload_summary

/--
Theorem 3.3/Claim 3.4 min/max search ratio endpoint: public alias packaging
the min/max finite-search certificate with the final rounded-instance
`(1 + epsilon)` guarantee.
-/
def theorem3_3_claim34_min_max_search_certificate_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_claim_3_4_min_max_with_ratio_guarantee

/--
Theorem 3.3/Claim 3.4 min/max IP/search ratio endpoint: public alias keeping
the constructed value-pair IP certificate together with the finite-search
certificate and final `(1 + epsilon)` guarantee.
-/
def theorem3_3_claim34_min_max_value_pair_ip_search_certificate_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_ip_and_search_certificate_claim_3_4_min_max_with_ratio_guarantee

/--
Theorem 3.3/Claim 3.4 min/max IP/search payload summary ratio endpoint:
public alias pairing the full payload summary with the final rounded-instance
`(1 + epsilon)` guarantee.
-/
def theorem3_3_claim34_min_max_value_pair_ip_search_payload_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_claim_3_4_min_max_ip_search_payload_summary_with_ratio_guarantee

/--
Theorem 3.3/Claim 3.4 min/max IP/search chosen-IP summary ratio endpoint:
public alias exposing both the comparison value-pair IP summary and selected
search-IP summary with the final rounded-instance guarantee.
-/
def theorem3_3_claim34_min_max_value_pair_ip_search_chosen_ip_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_claim_3_4_min_max_ip_search_chosen_ip_summary_with_ratio_guarantee

/--
Theorem 3.3 materialized rounded-supply optimality bridge: public alias
comparing the finite search result against any exact allocation once it is no
worse than an exact optimal candidate.
-/
def theorem3_3_value_pair_search_ratio_le_of_exact_supply_optimal_candidate :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_value_pair_search_ratio_le_of_exact_supply_optimal_candidate

/--
Theorem 3.3 materialized Claim-3.4 exact-supply comparison endpoint: public
alias comparing finite search against the bounded optimum returned by Claim
3.4 before constructing the search certificate.
-/
def theorem3_3_value_pair_search_ratio_le_of_claim34_exact_supply_optimum :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_value_pair_search_ratio_le_of_claim34_exact_supply_optimum

/--
Theorem 3.3 materialized Claim-3.4 no-top exact-supply comparison endpoint:
public alias discharging strict-small-good assumptions from the no-top rounded
supply condition before constructing the search certificate.
-/
def theorem3_3_value_pair_search_ratio_le_of_claim34_exact_supply_optimum_no_top :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_value_pair_search_ratio_le_of_claim34_exact_supply_optimum_no_top

/--
Theorem 3.3 materialized Claim-3.4 no-top weighted-supply comparison endpoint:
public alias deriving the materialized average identity before comparing
finite search against the Claim-3.4 bounded optimum.
-/
def theorem3_3_value_pair_search_ratio_le_of_claim34_exact_supply_optimum_no_top_weighted :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_value_pair_search_ratio_le_of_claim34_exact_supply_optimum_no_top_of_weighted_supply

/--
Theorem 3.3 materialized Claim-3.4 exact-supply search existence: public alias
for the raw bounded optimum/search payload before adjoining the final
rounded-instance guarantee.
-/
def theorem3_3_claim34_exact_supply_optimum_no_top_search_certificate_exists :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_of_claim34_exact_supply_optimum_no_top

/--
Theorem 3.3 materialized Claim-3.4 exact-supply search endpoint: public alias
packaging the exact optimum/search payload with the final rounded-instance
`(1 + epsilon)` guarantee.
-/
def theorem3_3_claim34_exact_supply_optimum_no_top_search_certificate_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_ratio_guarantee_of_claim34_exact_supply_optimum_no_top

/--
Theorem 3.3 materialized Claim-3.4 exact-supply search summary endpoint:
public alias packaging the exact optimum/search payload with the final
guarantee and selected-pair admissibility.
-/
def theorem3_3_claim34_exact_supply_optimum_no_top_search_certificate_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_summary_with_ratio_guarantee_of_claim34_exact_supply_optimum_no_top

/--
Theorem 3.3 materialized Claim-3.4 exact-supply concrete-IP/search endpoint:
public alias packaging the bounded optimum as a concrete IP certificate
alongside the finite search witness and final rounded-instance guarantee.
-/
def theorem3_3_claim34_exact_supply_optimum_no_top_concrete_ip_search_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_concrete_ip_and_search_with_ratio_guarantee_of_claim34_exact_supply_optimum_no_top

/--
Theorem 3.3 materialized Claim-3.4 exact-supply concrete-IP/search full-summary
endpoint: public alias exposing the common uncapped concrete-IP and selected
finite-search IP summaries.
-/
def theorem3_3_claim34_exact_supply_optimum_no_top_concrete_ip_search_full_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_concrete_ip_and_search_full_summary_with_ratio_guarantee_of_claim34_exact_supply_optimum_no_top

/--
Theorem 3.3 materialized Claim-3.4 weighted-supply exact-optimum search
existence: public alias deriving the materialized average identity before
exposing the raw bounded optimum/search payload.
-/
def theorem3_3_claim34_exact_supply_optimum_no_top_weighted_search_certificate_exists :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_of_claim34_exact_supply_optimum_no_top_of_weighted_supply

/--
Theorem 3.3 materialized Claim-3.4 weighted-supply exact-optimum search
endpoint: public alias deriving the materialized average identity before
pairing the search payload with the final rounded-instance guarantee.
-/
def theorem3_3_claim34_exact_supply_optimum_no_top_weighted_search_certificate_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_ratio_guarantee_of_claim34_exact_supply_optimum_no_top_of_weighted_supply

/--
Theorem 3.3 materialized Claim-3.4 weighted-supply exact-optimum search
summary endpoint: public alias deriving the materialized average identity
before exposing selected-pair admissibility with the final guarantee.
-/
def theorem3_3_claim34_exact_supply_optimum_no_top_weighted_search_certificate_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_summary_with_ratio_guarantee_of_claim34_exact_supply_optimum_no_top_of_weighted_supply

/--
Theorem 3.3 materialized Claim-3.4 weighted-supply exact-optimum concrete-IP
search endpoint: public alias deriving the materialized average identity
before exposing the bounded optimum as a concrete IP certificate.
-/
def theorem3_3_claim34_exact_supply_optimum_no_top_weighted_concrete_ip_search_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_concrete_ip_and_search_with_ratio_guarantee_of_claim34_exact_supply_optimum_no_top_of_weighted_supply

/--
Theorem 3.3 materialized Claim-3.4 weighted-supply exact-optimum concrete-IP
search full-summary endpoint: public alias deriving the materialized average
identity before exposing the common IP/search summaries.
-/
def theorem3_3_claim34_exact_supply_optimum_no_top_weighted_concrete_ip_search_full_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_concrete_ip_and_search_full_summary_with_ratio_guarantee_of_claim34_exact_supply_optimum_no_top_of_weighted_supply

/--
Theorem 3.3 materialized Claim-3.4 owner-map weighted-supply search existence:
public alias exposing the raw source-owner bounded optimum/search payload
before adjoining the final rounded-instance guarantee.
-/
def theorem3_3_claim34_owner_no_top_weighted_search_certificate_exists :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_of_claim34_owner_no_top_of_weighted_supply

/--
Theorem 3.3 materialized Claim-3.4 owner-map weighted-supply search endpoint:
public alias packaging the source-owner bounded optimum/search payload with the
final rounded-instance guarantee.
-/
def theorem3_3_claim34_owner_no_top_weighted_search_certificate_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_ratio_guarantee_of_claim34_owner_no_top_of_weighted_supply

/--
Theorem 3.3 materialized Claim-3.4 owner-map weighted-supply search summary
endpoint: public alias adding selected-pair admissibility to the source-owner
bounded optimum/search payload with the final guarantee.
-/
def theorem3_3_claim34_owner_no_top_weighted_search_certificate_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_summary_with_ratio_guarantee_of_claim34_owner_no_top_of_weighted_supply

/--
Theorem 3.3 materialized Claim-3.4 owner-map weighted-supply concrete-IP/search
endpoint: public alias packaging the source-owner bounded optimum as a concrete
IP certificate alongside the finite search witness and final guarantee.
-/
def theorem3_3_claim34_owner_no_top_weighted_concrete_ip_search_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_concrete_ip_and_search_with_ratio_guarantee_of_claim34_owner_no_top_of_weighted_supply

/--
Theorem 3.3 materialized Claim-3.4 owner-map weighted-supply concrete-IP/search
full-summary endpoint: public alias exposing common full summaries for the
owner-map comparison IP and selected finite-search IP.
-/
def theorem3_3_claim34_owner_no_top_weighted_concrete_ip_search_full_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_concrete_ip_and_search_full_summary_with_ratio_guarantee_of_claim34_owner_no_top_of_weighted_supply

/--
Theorem 3.3 materialized Claim-3.4 owner-free weighted-supply search
existence: public alias deriving the owner map internally and exposing the raw
bounded optimum/search payload before adjoining the final rounded-instance
guarantee.
-/
def theorem3_3_claim34_no_top_weighted_search_certificate_exists :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_of_claim34_no_top_of_weighted_supply

/--
Theorem 3.3 materialized Claim-3.4 owner-free weighted-supply search endpoint:
public alias deriving the owner map internally and pairing the search payload
with the final rounded-instance guarantee.
-/
def theorem3_3_claim34_no_top_weighted_search_certificate_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_with_ratio_guarantee_of_claim34_no_top_of_weighted_supply

/--
Theorem 3.3 materialized Claim-3.4 owner-free weighted-supply search summary
endpoint: public alias deriving the owner map internally and exposing
selected-pair admissibility with the final guarantee.
-/
def theorem3_3_claim34_no_top_weighted_search_certificate_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_value_pair_search_certificate_summary_with_ratio_guarantee_of_claim34_no_top_of_weighted_supply

/--
Theorem 3.3 materialized Claim-3.4 owner-free weighted-supply concrete-IP/search
endpoint: public alias deriving the owner map internally and exposing the
bounded optimum as a concrete IP certificate.
-/
def theorem3_3_claim34_no_top_weighted_concrete_ip_search_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_concrete_ip_and_search_with_ratio_guarantee_of_claim34_no_top_of_weighted_supply

/--
Theorem 3.3 materialized Claim-3.4 owner-free weighted-supply concrete-IP/search
full-summary endpoint: public alias exposing common full summaries for the
comparison IP and selected finite-search IP.
-/
def theorem3_3_claim34_no_top_weighted_concrete_ip_search_full_summary_ratio_endpoint :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_exists_concrete_ip_and_search_full_summary_with_ratio_guarantee_of_claim34_no_top_of_weighted_supply

/--
Theorem 3.3 ratio-transfer composition: public alias for composing the
rounded-to-source and source-to-rounded transfer inequalities.
-/
def theorem3_3_ratio_transfer_certificate :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_ratio_transfer_certificate

/--
Theorem 3.3 transfer-factor algebra: public alias for the displayed product
of Lemma 3.5 transfer factors.
-/
def theorem3_3_transfer_factor_eq_source_fraction :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_transfer_factor_eq_source_fraction

/--
Theorem 3.3 transfer-factor endpoint: public alias for the `56 / epsilon`
bound by `1 + epsilon`.
-/
def theorem3_3_transfer_factor_le_one_add_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_transfer_factor_le_one_add_epsilon

/--
Theorem 3.3 ratio-transfer epsilon endpoint: public alias for the final
transfer guarantee with a nonnegative optimal rounded ratio side.
-/
def theorem3_3_ratio_transfer_certificate_epsilon :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_ratio_transfer_certificate_epsilon

/--
Theorem 3.3 ratio-transfer epsilon endpoint with natural optimal-load
assumptions.
-/
def theorem3_3_ratio_transfer_certificate_epsilon_of_opt_loads :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_ratio_transfer_certificate_epsilon_of_opt_loads

/--
Theorem 3.3/Lemma 3.5 additive-transfer endpoint: exact-name public alias for
the raw additive inequalities implying the `(1 + epsilon)` guarantee.
-/
def theorem3_3_ratio_transfer_certificate_epsilon_of_additive :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_ratio_transfer_certificate_epsilon_of_additive

/--
Theorem 3.3/Lemma 3.5 additive-transfer endpoint over per-agent load
functions: public alias for composing the agentwise additive transfer
inequalities into the `(1 + epsilon)` ratio guarantee.
-/
def theorem3_3_ratio_transfer_certificate_epsilon_of_agentwise_additive_loads :=
  @LMMS04FairDivision.paper_lmms_theorem_3_3_ratio_transfer_certificate_epsilon_of_agentwise_additive_loads

/--
Lemma 3.5 and Theorem 3.3 final algebra: with `lambda = 56 / epsilon`,
the raw additive rounding-transfer inequalities give a `(1 + epsilon)`
multiplicative envy-ratio guarantee.
-/
theorem lemma3_5_additive_transfer_certificate_epsilon_of_opt_loads
    {epsilon L optMin optMax roundedMin roundedMax outMin outMax : ℝ}
    (hepsilon_pos : 0 < epsilon) (hepsilon_le_one : epsilon ≤ 1)
    (houtMin : 0 < outMin)
    (hroundedMin : 0 < roundedMin)
    (hoptMin : 0 < optMin) (hoptMax : 0 ≤ optMax)
    (hroundedMax_nonneg : 0 ≤ roundedMax)
    (hroundedMin_half : L ≤ 2 * roundedMin)
    (hroundedMax_half : L ≤ 2 * roundedMax)
    (hoptMin_half : L ≤ 2 * optMin)
    (hoptMax_half : L ≤ 2 * optMax)
    (hbackward_max :
      outMax ≤ roundedMax + L / (56 / epsilon))
    (hbackward_min :
      ((56 / epsilon) / ((56 / epsilon) + 1)) * roundedMin -
          (2 / (56 / epsilon)) * L ≤ outMin)
    (hforward_max :
      roundedMax ≤ (((56 / epsilon) + 1) / (56 / epsilon)) * optMax +
        L / (56 / epsilon))
    (hforward_min :
      optMin - L / (56 / epsilon) ≤ roundedMin) :
    Theorem35.ratio outMin outMax ≤
      Theorem35.ratio optMin optMax * (1 + epsilon) := by
  exact
    LMMS04FairDivision.paper_lmms_theorem_3_3_ratio_transfer_certificate_epsilon_of_additive
      hepsilon_pos hepsilon_le_one houtMin hroundedMin hoptMin hoptMax
      hroundedMax_nonneg hroundedMin_half hroundedMax_half hoptMin_half
      hoptMax_half hbackward_max hbackward_min hforward_max hforward_min

/-! ## Section 4: Truthfulness and Random Allocation -/

/-- Direct fair-division mechanism without transfers. -/
abbrev directMechanism (Agent Item : Type*) :=
  LMMS04FairDivision.paper_direct_mechanism Agent Item

/-- Randomized direct fair-division mechanism without transfers. -/
abbrev randomizedDirectMechanism (Agent Item : Type*) :=
  LMMS04FairDivision.paper_randomized_direct_mechanism Agent Item

/-- Dominant-strategy truthfulness for direct fair-division mechanisms. -/
def truthful [DecidableEq Agent] (M : directMechanism Agent Item) : Prop :=
  LMMS04FairDivision.paper_fair_division_truthful M

/-- Expected-utility truthfulness for randomized direct mechanisms. -/
def randomizedTruthful
    [Fintype (Allocation Agent Item)] [DecidableEq (Allocation Agent Item)]
    [DecidableEq Agent]
    (M : randomizedDirectMechanism Agent Item) : Prop :=
  LMMS04FairDivision.paper_randomized_fair_division_truthful M

/-- The finite two-player/eight-egg source goods used for Theorem 4.1. -/
abbrev theorem4_1_source_goods : Finset Theorem41.LMMS41Item :=
  Theorem41.lmms41Goods

/-- The truthful source report used for Theorem 4.1. -/
abbrev theorem4_1_true_report : Theorem41.LMMS41Report :=
  Theorem41.lmms41TrueReport

/--
Theorem 4.1: no mechanism that always allocates the finite source goods and
returns an envy-free allocation whenever one exists is truthful.
-/
theorem theorem4_1_source_not_truthful_envy_free_whenever_exists
    (M : Theorem41.LMMS41Mechanism)
    (halloc : ReturnsAllocationOf M Theorem41.lmms41Goods)
    (hef : ReturnsEnvyFreeWheneverExists M Theorem41.lmms41Goods) :
    ¬ M.Truthful := by
  exact
    LMMS04FairDivision.paper_lmms_theorem_4_1_source_not_truthful_envy_free_whenever_exists
      M halloc hef

/--
Theorem 4.1 minimum-envy form: a mechanism that always chooses a minimum
reported-envy allocation of the finite source goods is not truthful.
-/
theorem theorem4_1_source_minimum_envy_not_truthful
    (M : Theorem41.LMMS41Mechanism)
    (hmin : ReturnsMinimumReportEnvy M Theorem41.lmms41Goods) :
    ¬ M.Truthful := by
  exact
    LMMS04FairDivision.paper_lmms_theorem_4_1_source_minimum_envy_not_truthful
      M hmin

/--
Theorem 4.2: independently assigning each good uniformly at random is truthful
in expected utility.
-/
theorem theorem4_2_uniform_random_mechanism_truthful
    [Fintype (Allocation Agent Item)] [DecidableEq (Allocation Agent Item)] :
    randomizedTruthful (Theorem42.lmms42UniformRandomMechanism Agent Item) := by
  exact
    LMMS04FairDivision.paper_lmms_theorem_4_2_uniform_random_mechanism_truthful

/--
Theorem 4.2 concentration bound: under normalized additive utilities and item
values bounded by `alpha`, independent uniform allocation has maximum envy at
most `t` with the paper's explicit Chebyshev/union-bound probability.
-/
theorem theorem4_2_uniform_random_max_envy_probability_bound
    (w : Theorem42.LMMS42ItemWeights Agent Item) {alpha t : ℝ}
    (halpha : 0 ≤ alpha) (ht : 0 < t)
    (hnonneg : ∀ p : Agent, ∀ g : Item, 0 ≤ w p g)
    (hsum : ∀ p : Agent, ∑ g : Item, w p g = 1)
    (hbound : ∀ p : Agent, ∀ g : Item, w p g ≤ alpha) :
    1 - 2 * alpha * (Fintype.card Agent : ℝ) / t ^ 2 ≤
      AppliedModelingLib.pmfProb (Theorem42.lmms42UniformAssignmentLaw Agent Item)
        (fun assign : Item → Agent =>
          maxReportEnvy (Theorem42.lmms42AdditiveReport w)
            (Theorem42.lmms42AllocationOfAssignment assign) ≤ t) := by
  exact
    LMMS04FairDivision.paper_lmms_theorem_4_2_uniform_random_max_envy_probability_bound
      w halpha ht hnonneg hsum hbound

end

end ProofInterface
end LMMS04FairDivision

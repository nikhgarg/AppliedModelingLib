import CGGG20SelectiveInformationAcquisition.MainTheorems
import CGGG20SelectiveInformationAcquisition.SourcePairModel
import CGGG20SelectiveInformationAcquisition.Assumptions
import AppliedModelingLib.Foundations.Optimization.MeasureThreshold

/-!
# Human-Facing Paper Interface: Fair Allocation through Selective Information Acquisition

This first review surface covers the fixed-threshold LP construction in Section
3 of the paper.  It exposes the source quantities and the algebraic facts that
make the objective, budget constraint, and diversity constraints linear in the
screening probabilities.
-/

open scoped BigOperators

namespace CGGG20SelectiveInformationAcquisition

namespace ProofBridge

open MeasureTheory
open AppliedModelingLib.Decision
open AppliedModelingLib.Optimization
open AppliedModelingLib.Probability

/--
Finite-state data for the appendix cost-aware threshold argument.

Source status: finite weighted-sum model of the appendix expectations for
Lemma 1, using posterior utilities `\hat U_i` as in the proof.
-/
abbrev paper_cost_aware_threshold_data (Applicant State : Type*) :=
  CostAwareThresholdData Applicant State

/--
Allocation policy for the finite-state appendix model.

Source status: direct finite-state representation of state-dependent
allocation probabilities.
-/
abbrev paper_cost_aware_allocation_policy (Applicant State : Type*) :=
  CostAwareThresholdData.AllocationPolicy Applicant State

/--
Allocation probabilities lie in `[0,1]`.

Source status: source allocation-policy probability constraint.
-/
def paper_cost_aware_allocation_policy_bounds
    {Applicant State : Type*}
    (policy : paper_cost_aware_allocation_policy Applicant State) : Prop :=
  ∀ item state, 0 ≤ policy item state ∧ policy item state ≤ 1

/--
The appendix's literal single-group cost-aware threshold rule. The displayed
comparison is by posterior utility divided by allocation cost; strictly
positive costs make it equivalent to the product comparison used internally.
-/
def paper_expected_single_cost_aware_threshold_policy
    {Applicant Outcome : Type*} [Fintype Applicant]
    (D : ExpectedCostAwareData Applicant Outcome)
    (t alpha : ℝ)
    (policy : ExpectedCostAwareData.AllocationPolicy Applicant Outcome) : Prop :=
  0 ≤ alpha ∧ alpha ≤ 1 ∧
    ∀ item outcome,
      (t < D.posteriorUtility item outcome / D.allocCost item →
        policy item outcome = 1) ∧
      (D.posteriorUtility item outcome / D.allocCost item = t →
        policy item outcome = alpha) ∧
      (D.posteriorUtility item outcome / D.allocCost item < t →
        policy item outcome = 0)

/-- The source ratio formulation and the exchange proof's product form agree. -/
theorem paper_expected_single_cost_aware_threshold_policy_iff
    {Applicant Outcome : Type*} [Fintype Applicant]
    (D : ExpectedCostAwareData Applicant Outcome)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (t alpha : ℝ)
    (policy : ExpectedCostAwareData.AllocationPolicy Applicant Outcome) :
    paper_expected_single_cost_aware_threshold_policy D t alpha policy ↔
      D.IsSingleCostAwareThresholdPolicy t alpha policy := by
  constructor
  · rintro ⟨halpha_nonneg, halpha_le_one, hcases⟩
    refine ⟨halpha_nonneg, halpha_le_one, ?_⟩
    intro item outcome
    constructor
    · intro habove
      have hscore : t < D.posteriorUtility item outcome / D.allocCost item := by
        apply (lt_div_iff₀ (hcost_pos item)).2
        simpa [mul_comm] using habove
      exact (hcases item outcome).1 hscore
    constructor
    · intro heq
      have hscore : D.posteriorUtility item outcome / D.allocCost item = t := by
        apply (div_eq_iff (ne_of_gt (hcost_pos item))).2
        simpa [mul_comm] using heq
      exact (hcases item outcome).2.1 hscore
    · intro hbelow
      have hscore : D.posteriorUtility item outcome / D.allocCost item < t := by
        apply (div_lt_iff₀ (hcost_pos item)).2
        simpa [mul_comm] using hbelow
      exact (hcases item outcome).2.2 hscore
  · rintro ⟨halpha_nonneg, halpha_le_one, hcases⟩
    refine ⟨halpha_nonneg, halpha_le_one, ?_⟩
    intro item outcome
    constructor
    · intro hscore
      have habove : D.allocCost item * t < D.posteriorUtility item outcome := by
        simpa [mul_comm] using (lt_div_iff₀ (hcost_pos item)).1 hscore
      exact (hcases item outcome).1 habove
    constructor
    · intro hscore
      have heq : D.posteriorUtility item outcome = D.allocCost item * t := by
        simpa [mul_comm] using (div_eq_iff (ne_of_gt (hcost_pos item))).1 hscore
      exact (hcases item outcome).2.1 heq
    · intro hscore
      have hbelow : D.posteriorUtility item outcome < D.allocCost item * t := by
        simpa [mul_comm] using (div_lt_iff₀ (hcost_pos item)).1 hscore
      exact (hcases item outcome).2.2 hbelow

/--
Appendix Definition, cost-aware single-threshold policy.

Source status: direct single-group formalization of the cost-aware threshold
policy definition, written as `c_i t` comparisons rather than division by
`c_i`.
-/
abbrev paper_cost_aware_single_threshold_policy
    {Applicant State : Type*} [Fintype Applicant] [Fintype State]
    (D : paper_cost_aware_threshold_data Applicant State)
    (t alpha : ℝ)
    (policy : paper_cost_aware_allocation_policy Applicant State) : Prop :=
  D.IsSingleCostAwareThresholdPolicy t alpha policy

/--
Canonical boundary-randomized single-threshold policy.

Source status: constructive form of the appendix cost-aware threshold-policy
definition.
-/
noncomputable abbrev paper_cost_aware_canonical_single_threshold_policy
    {Applicant State : Type*} [Fintype Applicant] [Fintype State]
    (D : paper_cost_aware_threshold_data Applicant State)
    (t alpha : ℝ) :
    paper_cost_aware_allocation_policy Applicant State :=
  D.singleThresholdPolicy t alpha

/--
The canonical boundary-randomized rule satisfies the cost-aware threshold
definition.

Source status: derived constructor for the appendix definition.
-/
theorem paper_cost_aware_canonical_single_threshold_policy_is_threshold
    {Applicant State : Type*} [Fintype Applicant] [Fintype State]
    (D : paper_cost_aware_threshold_data Applicant State)
    (t alpha : ℝ)
    (halpha_nonneg : 0 ≤ alpha) (halpha_le_one : alpha ≤ 1) :
    paper_cost_aware_single_threshold_policy D t alpha
      (paper_cost_aware_canonical_single_threshold_policy D t alpha) :=
  D.singleThresholdPolicy_isSingleCostAwareThresholdPolicy
    t alpha halpha_nonneg halpha_le_one

/--
Lemma 2 boundary interpolation for expected posterior utility.

Source status: derived finite weighted-sum version of the appendix boundary
randomization step once a bracketing threshold is known.
-/
theorem paper_lemma2_boundary_interpolation_expectedPosteriorUtility
    {Applicant State : Type*} [Fintype Applicant] [Fintype State]
    (D : paper_cost_aware_threshold_data Applicant State)
    (t target : ℝ)
    (hboundary : 0 < D.boundaryPosteriorUtility t)
    (hlower : D.strictAbovePosteriorUtility t ≤ target)
    (hupper :
      target ≤ D.strictAbovePosteriorUtility t +
        D.boundaryPosteriorUtility t) :
    ∃ alpha : ℝ,
      0 ≤ alpha ∧ alpha ≤ 1 ∧
        D.expectedPosteriorUtility
            (paper_cost_aware_canonical_single_threshold_policy D t alpha) =
          target :=
  D.exists_alpha_singleThresholdPolicy_expectedPosteriorUtility_eq
    t target hboundary hlower hupper

/--
Lemma 2 boundary interpolation for expected cost.

Source status: derived finite weighted-sum version of the appendix boundary
randomization step once a bracketing threshold is known.
-/
theorem paper_lemma2_boundary_interpolation_expectedCost
    {Applicant State : Type*} [Fintype Applicant] [Fintype State]
    (D : paper_cost_aware_threshold_data Applicant State)
    (t target : ℝ)
    (hboundary : 0 < D.boundaryCost t)
    (hlower : D.strictAboveCost t ≤ target)
    (hupper : target ≤ D.strictAboveCost t + D.boundaryCost t) :
    ∃ alpha : ℝ,
      0 ≤ alpha ∧ alpha ≤ 1 ∧
        D.expectedCost
            (paper_cost_aware_canonical_single_threshold_policy D t alpha) =
          target :=
  D.exists_alpha_singleThresholdPolicy_expectedCost_eq
    t target hboundary hlower hupper

/--
Extended real thresholds with formal endpoints.

Source status: source convention in the threshold definitions, where
thresholds may lie in `R union {-infinity, infinity}`.
-/
abbrev paper_cost_aware_extended_threshold :=
  RealThreshold

/--
Appendix Definition, endpoint-aware cost-aware threshold policy.

Source status: direct formalization of the appendix threshold domain
`R union {-infinity, infinity}`; finite thresholds use the cost-aware
comparison and the formal endpoints allocate everyone or no one.
-/
abbrev paper_cost_aware_extended_single_threshold_policy
    {Applicant State : Type*} [Fintype Applicant] [Fintype State]
    (D : paper_cost_aware_threshold_data Applicant State)
    (threshold : paper_cost_aware_extended_threshold) (alpha : ℝ)
    (policy : paper_cost_aware_allocation_policy Applicant State) : Prop :=
  D.IsSingleCostAwareExtendedThresholdPolicy threshold alpha policy

/--
Canonical endpoint-aware cost-aware threshold policy.

Source status: constructive form of the source endpoint threshold convention.
-/
noncomputable abbrev paper_cost_aware_canonical_extended_single_threshold_policy
    {Applicant State : Type*} [Fintype Applicant] [Fintype State]
    (D : paper_cost_aware_threshold_data Applicant State)
    (threshold : paper_cost_aware_extended_threshold) (alpha : ℝ) :
    paper_cost_aware_allocation_policy Applicant State :=
  D.extendedSingleThresholdPolicy threshold alpha

/--
The canonical endpoint-aware rule satisfies the source threshold definition.

Source status: derived constructor for the endpoint-aware appendix definition.
-/
theorem paper_cost_aware_canonical_extended_single_threshold_policy_is_threshold
    {Applicant State : Type*} [Fintype Applicant] [Fintype State]
    (D : paper_cost_aware_threshold_data Applicant State)
    (threshold : paper_cost_aware_extended_threshold) (alpha : ℝ)
    (halpha_nonneg : 0 ≤ alpha) (halpha_le_one : alpha ≤ 1) :
    paper_cost_aware_extended_single_threshold_policy D threshold alpha
      (paper_cost_aware_canonical_extended_single_threshold_policy
        D threshold alpha) :=
  D.extendedSingleThresholdPolicy_isSingleCostAwareExtendedThresholdPolicy
    threshold alpha halpha_nonneg halpha_le_one

/--
Endpoint-aware cost-aware threshold policies have allocation probabilities in
`[0,1]`.

Source status: derived well-formedness fact for the endpoint-aware appendix
definition.
-/
theorem paper_cost_aware_extended_single_threshold_policy_bounds
    {Applicant State : Type*} [Fintype Applicant] [Fintype State]
    (D : paper_cost_aware_threshold_data Applicant State)
    (threshold : paper_cost_aware_extended_threshold) (alpha : ℝ)
    (policy : paper_cost_aware_allocation_policy Applicant State)
    (hthreshold :
      paper_cost_aware_extended_single_threshold_policy
        D threshold alpha policy) :
    paper_cost_aware_allocation_policy_bounds policy :=
  D.singleCostAwareExtendedThresholdPolicy_bounds
    threshold alpha policy hthreshold

/--
Appendix Lemma 2, finite-measure threshold bracketing with source endpoints.

Source status: measure-level version of the proof step choosing a threshold
whose strict and closed upper-tail masses bracket the target; formal endpoints
cover the zero and total-mass cases allowed by the source definition.
-/
theorem paper_lemma2_finite_measure_threshold_bracket
    (μ : Measure ℝ) [IsFiniteMeasure μ] {target : ℝ}
    (htarget_nonneg : 0 ≤ target)
    (htarget_le_total : target ≤ μ.real (Set.univ : Set ℝ)) :
    ∃ θ : paper_cost_aware_extended_threshold,
      θ.strictUpperTailMass μ ≤ target ∧
        target ≤ θ.closedUpperTailMass μ :=
  exists_realThreshold_upperTailMass_bracket_finite
    μ htarget_nonneg htarget_le_total

/--
Appendix Lemma 2, finite-measure threshold attainment with boundary
randomization.

Source status: source-general tail-mass core of Lemma 2. For any target
between zero and the total finite measure mass, an extended threshold and
boundary randomization probability attain the target exactly.
-/
theorem paper_lemma2_finite_measure_threshold_attainment
    (μ : Measure ℝ) [IsFiniteMeasure μ] {target : ℝ}
    (htarget_nonneg : 0 ≤ target)
    (htarget_le_total : target ≤ μ.real (Set.univ : Set ℝ)) :
    ∃ θ : paper_cost_aware_extended_threshold,
      ∃ alpha : ℝ,
        0 ≤ alpha ∧ alpha ≤ 1 ∧
          θ.strictUpperTailMass μ +
              alpha *
                (θ.closedUpperTailMass μ -
                  θ.strictUpperTailMass μ) =
            target :=
  exists_realThreshold_upperTailMass_interpolation_finite
    μ htarget_nonneg htarget_le_total

/--
Theorem 1 source proof step: apply finite-measure Lemma 2 groupwise.

Source status: measure-level groupwise version of the appendix step
"applying Lemma 2 to each group" to choose thresholds and boundary
randomization probabilities.
-/
theorem paper_theorem1_groupwise_finite_measure_threshold_attainment
    {Group : Type*} [Fintype Group]
    (μ : Group → Measure ℝ) [∀ g, IsFiniteMeasure (μ g)]
    {target : Group → ℝ}
    (htarget_nonneg : ∀ g, 0 ≤ target g)
    (htarget_le_total :
      ∀ g, target g ≤ (μ g).real (Set.univ : Set ℝ)) :
    ∃ θ : Group → paper_cost_aware_extended_threshold,
      ∃ alpha : Group → ℝ,
        ∀ g,
          0 ≤ alpha g ∧ alpha g ≤ 1 ∧
            (θ g).strictUpperTailMass (μ g) +
                alpha g *
                  ((θ g).closedUpperTailMass (μ g) -
                    (θ g).strictUpperTailMass (μ g)) =
              target g :=
  exists_group_realThreshold_upperTailMass_interpolation_finite
    μ htarget_nonneg htarget_le_total

/--
Lemma 2 boundary interpolation for expected posterior utility, without
requiring positive boundary mass.

Source status: derived boundary-randomization step for continuous or atomless
thresholds; if the strict and closed values coincide, any target between them
is already attained.
-/
theorem paper_lemma2_boundary_interpolation_expectedPosteriorUtility_of_closed_bracket
    {Applicant State : Type*} [Fintype Applicant] [Fintype State]
    (D : paper_cost_aware_threshold_data Applicant State)
    (t target : ℝ)
    (hlower : D.strictAbovePosteriorUtility t ≤ target)
    (hupper :
      target ≤ D.strictAbovePosteriorUtility t +
        D.boundaryPosteriorUtility t) :
    ∃ alpha : ℝ,
      0 ≤ alpha ∧ alpha ≤ 1 ∧
        D.expectedPosteriorUtility
            (paper_cost_aware_canonical_single_threshold_policy D t alpha) =
          target :=
  D.exists_alpha_singleThresholdPolicy_expectedPosteriorUtility_eq_of_closed_bracket
    t target hlower hupper

/--
Lemma 2 boundary interpolation for expected cost, without requiring positive
boundary mass.

Source status: derived boundary-randomization step for continuous or atomless
thresholds; if the strict and closed values coincide, any target between them
is already attained.
-/
theorem paper_lemma2_boundary_interpolation_expectedCost_of_closed_bracket
    {Applicant State : Type*} [Fintype Applicant] [Fintype State]
    (D : paper_cost_aware_threshold_data Applicant State)
    (t target : ℝ)
    (hlower : D.strictAboveCost t ≤ target)
    (hupper : target ≤ D.strictAboveCost t + D.boundaryCost t) :
    ∃ alpha : ℝ,
      0 ≤ alpha ∧ alpha ≤ 1 ∧
        D.expectedCost
            (paper_cost_aware_canonical_single_threshold_policy D t alpha) =
          target :=
  D.exists_alpha_singleThresholdPolicy_expectedCost_eq_of_closed_bracket
    t target hlower hupper

/--
Appendix Lemma 2, utility replacement from a closed threshold bracket.

Source status: derived single-group replacement step from Lemma 2 once the
strict and closed threshold utility values bracket the target; allows atomless
thresholds.
-/
theorem paper_lemma2_same_utility_threshold_replacement_of_closed_bracket
    {Applicant State : Type*} [Fintype Applicant] [Fintype State]
    (D : paper_cost_aware_threshold_data Applicant State)
    (original : paper_cost_aware_allocation_policy Applicant State)
    (B :
      D.ClosedUtilityThresholdBracket
        (D.expectedPosteriorUtility original)) :
    Nonempty (D.SameUtilityThresholdReplacement original) :=
  ⟨B.toSameUtilityThresholdReplacement D original⟩

/--
Appendix Lemma 2, cost replacement from a closed threshold bracket.

Source status: derived single-group replacement step from Lemma 2 once the
strict and closed threshold cost values bracket the target; allows atomless
thresholds.
-/
theorem paper_lemma2_same_cost_threshold_replacement_of_closed_bracket
    {Applicant State : Type*} [Fintype Applicant] [Fintype State]
    (D : paper_cost_aware_threshold_data Applicant State)
    (original : paper_cost_aware_allocation_policy Applicant State)
    (B : D.ClosedCostThresholdBracket (D.expectedCost original)) :
    Nonempty (D.SameCostThresholdReplacement original) :=
  ⟨B.toSameCostThresholdReplacement D original⟩

/--
Appendix Lemma 2, cost-attainment version.

Source status: derived finite-support version of Lemma 2's expected-cost
attainment claim, under the finite atom model with nonnegative weights,
positive allocation costs, bounded allocation probabilities, and positive
total cost mass.
-/
theorem paper_lemma2_same_cost_threshold_replacement_of_finite_positive_costs
    {Applicant State : Type*} [Fintype Applicant] [Fintype State]
    (D : paper_cost_aware_threshold_data Applicant State)
    (original : paper_cost_aware_allocation_policy Applicant State)
    (hweight : ∀ state, 0 ≤ D.weight state)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (horiginal : paper_cost_aware_allocation_policy_bounds original)
    (htotal_pos : 0 < finiteAtomTotalMass D.costAtomMass) :
    Nonempty (D.SameCostThresholdReplacement original) :=
  D.exists_sameCostThresholdReplacement_of_finite_positive_costs
    original hweight hcost_pos horiginal htotal_pos

/--
Appendix Lemma 2, utility-attainment version.

Source status: derived finite-support version of Lemma 2's expected-utility
attainment claim, under the finite atom model with nonnegative weights and
posterior utilities, positive allocation costs, bounded allocation
probabilities, and positive total utility mass.
-/
theorem paper_lemma2_same_utility_threshold_replacement_of_finite_positive_costs
    {Applicant State : Type*} [Fintype Applicant] [Fintype State]
    (D : paper_cost_aware_threshold_data Applicant State)
    (original : paper_cost_aware_allocation_policy Applicant State)
    (hweight : ∀ state, 0 ≤ D.weight state)
    (hutility_nonneg : ∀ item state, 0 ≤ D.posteriorUtility item state)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (horiginal : paper_cost_aware_allocation_policy_bounds original)
    (htotal_pos : 0 < finiteAtomTotalMass D.utilityAtomMass) :
    Nonempty (D.SameUtilityThresholdReplacement original) :=
  D.exists_sameUtilityThresholdReplacement_of_finite_positive_costs
    original hweight hutility_nonneg hcost_pos horiginal htotal_pos

/--
Appendix Lemma 1 key expected-delta inequality for a single threshold.

Source status: derived finite weighted-sum form of Eq. (key), using the shared
threshold-exchange lemma.
-/
theorem paper_lemma1_single_threshold_expected_delta_key
    {Applicant State : Type*} [Fintype Applicant] [Fintype State]
    (D : paper_cost_aware_threshold_data Applicant State) (t alpha : ℝ)
    (threshold other : paper_cost_aware_allocation_policy Applicant State)
    (hweight : ∀ state, 0 ≤ D.weight state)
    (hthreshold : paper_cost_aware_single_threshold_policy D t alpha threshold)
    (hother : paper_cost_aware_allocation_policy_bounds other) :
    t * (D.expectedCost threshold - D.expectedCost other) ≤
      D.expectedPosteriorUtility threshold -
        D.expectedPosteriorUtility other :=
  D.singleCostAwareThreshold_expected_delta_key
    t alpha threshold other hweight hthreshold hother

/--
Appendix Lemma 1, Case 1: equal expected cost implies weakly higher expected
posterior utility for the threshold policy.

Source status: derived finite weighted-sum form of Lemma 1 Case 1.
-/
theorem paper_lemma1_single_threshold_utility_ge_of_cost_eq
    {Applicant State : Type*} [Fintype Applicant] [Fintype State]
    (D : paper_cost_aware_threshold_data Applicant State) (t alpha : ℝ)
    (threshold other : paper_cost_aware_allocation_policy Applicant State)
    (hweight : ∀ state, 0 ≤ D.weight state)
    (hthreshold : paper_cost_aware_single_threshold_policy D t alpha threshold)
    (hother : paper_cost_aware_allocation_policy_bounds other)
    (hcost : D.expectedCost threshold = D.expectedCost other) :
    D.expectedPosteriorUtility other ≤ D.expectedPosteriorUtility threshold :=
  D.singleCostAwareThreshold_expectedPosteriorUtility_ge_of_expectedCost_eq
    t alpha threshold other hweight hthreshold hother hcost

/--
Appendix Lemma 1, Case 2: equal expected posterior utility implies weakly lower
expected cost for a positive-threshold policy.

Source status: derived finite weighted-sum form of Lemma 1 Case 2.
-/
theorem paper_lemma1_single_threshold_cost_le_of_utility_eq
    {Applicant State : Type*} [Fintype Applicant] [Fintype State]
    (D : paper_cost_aware_threshold_data Applicant State) (t alpha : ℝ)
    (threshold other : paper_cost_aware_allocation_policy Applicant State)
    (ht : 0 < t)
    (hweight : ∀ state, 0 ≤ D.weight state)
    (hthreshold : paper_cost_aware_single_threshold_policy D t alpha threshold)
    (hother : paper_cost_aware_allocation_policy_bounds other)
    (hutility :
      D.expectedPosteriorUtility threshold =
        D.expectedPosteriorUtility other) :
    D.expectedCost threshold ≤ D.expectedCost other :=
  D.singleCostAwareThreshold_expectedCost_le_of_expectedPosteriorUtility_eq
    t alpha threshold other ht hweight hthreshold hother hutility

/--
Appendix Lemma 1 key inequality under an abstract finite-linear expectation.

Source status: source-general form of Eq. (key), abstracting over the
underlying probability space by requiring only monotonicity and finite
linearity of expectation.
-/
theorem paper_lemma1_expected_delta_key_of_finite_linear_expectation
    {Applicant Outcome : Type*} [Fintype Applicant]
    (expect : (Outcome → ℝ) → ℝ)
    (hlin : FiniteLinearExpectation expect)
    (posteriorUtility : Applicant → Outcome → ℝ)
    (allocCost : Applicant → ℝ)
    (threshold other : Applicant → Outcome → ℝ)
    (t : ℝ)
    (hpos :
      ∀ item outcome,
        0 < threshold item outcome - other item outcome →
          allocCost item * t ≤ posteriorUtility item outcome)
    (hneg :
      ∀ item outcome,
        threshold item outcome - other item outcome < 0 →
          posteriorUtility item outcome ≤ allocCost item * t) :
    t * expectedDeltaCost expect allocCost threshold other ≤
      expectedDeltaValue expect posteriorUtility threshold other :=
  mul_expectedDeltaCost_le_expectedDeltaValue
    expect hlin posteriorUtility allocCost threshold other t hpos hneg

/--
Appendix Lemma 1, Case 1, under an abstract finite-linear expectation.

Source status: source-general equal-cost consequence of Eq. (key).
-/
theorem paper_lemma1_expected_utility_ge_of_expected_cost_eq_of_finite_linear_expectation
    {Applicant Outcome : Type*} [Fintype Applicant]
    (expect : (Outcome → ℝ) → ℝ)
    (hlin : FiniteLinearExpectation expect)
    (posteriorUtility : Applicant → Outcome → ℝ)
    (allocCost : Applicant → ℝ)
    (threshold other : Applicant → Outcome → ℝ)
    (t : ℝ)
    (hpos :
      ∀ item outcome,
        0 < threshold item outcome - other item outcome →
          allocCost item * t ≤ posteriorUtility item outcome)
    (hneg :
      ∀ item outcome,
        threshold item outcome - other item outcome < 0 →
          posteriorUtility item outcome ≤ allocCost item * t)
    (hcost : expectedDeltaCost expect allocCost threshold other = 0) :
    0 ≤ expectedDeltaValue expect posteriorUtility threshold other :=
  expectedDeltaValue_nonneg_of_expectedDeltaCost_eq_zero
    expect hlin posteriorUtility allocCost threshold other t hpos hneg hcost

/--
Appendix Lemma 1, Case 2, under an abstract finite-linear expectation.

Source status: source-general equal-utility consequence of Eq. (key).
-/
theorem paper_lemma1_expected_cost_le_of_expected_utility_eq_of_finite_linear_expectation
    {Applicant Outcome : Type*} [Fintype Applicant]
    (expect : (Outcome → ℝ) → ℝ)
    (hlin : FiniteLinearExpectation expect)
    (posteriorUtility : Applicant → Outcome → ℝ)
    (allocCost : Applicant → ℝ)
    (threshold other : Applicant → Outcome → ℝ)
    (t : ℝ)
    (ht : 0 < t)
    (hpos :
      ∀ item outcome,
        0 < threshold item outcome - other item outcome →
          allocCost item * t ≤ posteriorUtility item outcome)
    (hneg :
      ∀ item outcome,
        threshold item outcome - other item outcome < 0 →
          posteriorUtility item outcome ≤ allocCost item * t)
    (hvalue : expectedDeltaValue expect posteriorUtility threshold other = 0) :
    expectedDeltaCost expect allocCost threshold other ≤ 0 :=
  expectedDeltaCost_nonpos_of_expectedDeltaValue_eq_zero
    expect hlin posteriorUtility allocCost threshold other t ht hpos hneg
    hvalue

/--
Grouped finite-state allocation data for the main theorem's allocation
replacement step.

Source status: finite weighted-sum model of Eq. (def2) budget and Eq. (def3)
group utility constraints with fixed screening.
-/
abbrev paper_group_allocation_data (Applicant State Group : Type*) :=
  GroupAllocationData Applicant State Group

/--
Feasibility for the grouped allocation replacement problem.

Source status: direct formalization of the budget and diversity constraints
after fixing the screening policy.
-/
abbrev paper_group_allocation_feasible
    {Applicant State Group : Type*} [Fintype Applicant] [Fintype State]
    [DecidableEq Group]
    (D : paper_group_allocation_data Applicant State Group)
    (budget : ℝ) (diversityTarget : Group → ℝ)
    (policy : GroupAllocationData.AllocationPolicy Applicant State) : Prop :=
  D.SourceFeasible budget diversityTarget policy

/--
Optimality for the grouped allocation replacement problem.

Source status: source-shaped optimality predicate for the allocation part of
Theorem 1 after fixing screening.
-/
abbrev paper_group_allocation_optimal
    {Applicant State Group : Type*} [Fintype Applicant] [Fintype State]
    [DecidableEq Group]
    (D : paper_group_allocation_data Applicant State Group)
    (budget : ℝ) (diversityTarget : Group → ℝ)
    (policy : GroupAllocationData.AllocationPolicy Applicant State) : Prop :=
  D.SourceOptimal budget diversityTarget policy

/--
Optimality for the equality-diversity allocation replacement problem.

Source status: source-shaped optimality predicate for Lemma 3's equality
diversity variant.
-/
abbrev paper_group_allocation_equality_optimal
    {Applicant State Group : Type*} [Fintype Applicant] [Fintype State]
    [DecidableEq Group]
    (D : paper_group_allocation_data Applicant State Group)
    (budget : ℝ) (equalityTarget : Group → ℝ)
    (policy : GroupAllocationData.AllocationPolicy Applicant State) : Prop :=
  D.SourceEqualityOptimal budget equalityTarget policy

/--
Theorem 1 assembly step: a replacement allocation with weakly lower cost,
weakly higher group utilities, and weakly higher total utility is also optimal.

Source status: derived optimization bookkeeping used in the appendix proof of
Theorem 1 after the per-group threshold replacements are available.
-/
theorem paper_theorem1_group_replacement_preserves_optimality
    {Applicant State Group : Type*} [Fintype Applicant] [Fintype State]
    [DecidableEq Group]
    (D : paper_group_allocation_data Applicant State Group)
    (budget : ℝ) (diversityTarget : Group → ℝ)
    (original replacement : GroupAllocationData.AllocationPolicy Applicant State)
    (horiginal : paper_group_allocation_optimal D budget diversityTarget original)
    (hreplacement_bounds :
      CostAwareThresholdData.AllocationPolicyBounds replacement)
    (hcost :
      D.expectedCost replacement ≤ D.expectedCost original)
    (hgroup :
      ∀ g,
        D.expectedGroupPosteriorUtility g original ≤
          D.expectedGroupPosteriorUtility g replacement)
    (hutility :
      D.expectedPosteriorUtility original ≤
        D.expectedPosteriorUtility replacement) :
    paper_group_allocation_optimal D budget diversityTarget replacement := by
  constructor
  · exact ⟨hreplacement_bounds, hcost.trans horiginal.1.2.1,
      fun g => (horiginal.1.2.2 g).trans (hgroup g)⟩
  · intro other hother
    exact (horiginal.2 other hother).trans hutility

/--
Group utilities sum to total utility in the finite grouped model.

Source status: derived bookkeeping for the groupwise application of the
appendix threshold-replacement argument.
-/
theorem paper_theorem1_group_utilities_sum_to_total
    {Applicant State Group : Type*} [Fintype Applicant] [Fintype State]
    [Fintype Group] [DecidableEq Group]
    (D : paper_group_allocation_data Applicant State Group)
    (policy : GroupAllocationData.AllocationPolicy Applicant State) :
    (∑ g : Group, D.expectedGroupPosteriorUtility g policy) =
      D.expectedPosteriorUtility policy :=
  D.sum_expectedGroupPosteriorUtility_eq_expectedPosteriorUtility policy

/--
Group costs sum to total cost in the finite grouped model.

Source status: derived bookkeeping for preserving the source budget constraint
after groupwise threshold replacement.
-/
theorem paper_theorem1_group_costs_sum_to_total
    {Applicant State Group : Type*} [Fintype Applicant] [Fintype State]
    [Fintype Group] [DecidableEq Group]
    (D : paper_group_allocation_data Applicant State Group)
    (policy : GroupAllocationData.AllocationPolicy Applicant State) :
    (∑ g : Group, D.expectedGroupCost g policy) =
      D.expectedCost policy :=
  D.sum_expectedGroupCost_eq_expectedCost policy

/--
Theorem 1 groupwise assembly: per-group equal-cost and weak-utility-improving
replacements preserve global optimality.

Source status: derived source-shaped assembly step for Theorem 1, leaving only
the source's Lemma 2 threshold-attainment construction to supply the groupwise
replacement facts.
-/
theorem paper_theorem1_groupwise_replacement_preserves_optimality
    {Applicant State Group : Type*} [Fintype Applicant] [Fintype State]
    [Fintype Group] [DecidableEq Group]
    (D : paper_group_allocation_data Applicant State Group)
    (budget : ℝ) (diversityTarget : Group → ℝ)
    (original replacement : GroupAllocationData.AllocationPolicy Applicant State)
    (horiginal : paper_group_allocation_optimal D budget diversityTarget original)
    (hreplacement_bounds :
      CostAwareThresholdData.AllocationPolicyBounds replacement)
    (hcost :
      ∀ g,
        D.expectedGroupCost g replacement =
          D.expectedGroupCost g original)
    (hgroup :
      ∀ g,
        D.expectedGroupPosteriorUtility g original ≤
          D.expectedGroupPosteriorUtility g replacement) :
    paper_group_allocation_optimal D budget diversityTarget replacement :=
  D.sourceOptimal_of_groupwise_replacement_improves_constraints
    budget diversityTarget original replacement horiginal
    hreplacement_bounds hcost hgroup

/--
Grouped measure-space allocation data for the main theorem's allocation
replacement step.

Source status: source-general model of the appendix allocation replacement
problem after fixing the screening policy; the outcome space carries the
post-screening utility estimates.
-/
abbrev paper_measure_group_allocation_data
    (Applicant Outcome Group : Type*) [MeasurableSpace Outcome] :=
  MeasureGroupAllocationData Applicant Outcome Group

/--
Measure-space groupwise cost-aware threshold policy.

Source status: direct endpoint-aware version of the appendix cost-aware
threshold policy, with one threshold and one boundary randomization probability
per group.
-/
noncomputable abbrev paper_measure_groupwise_cost_aware_threshold_policy
    {Applicant Outcome Group : Type*} [Fintype Applicant]
    [MeasurableSpace Outcome] [DecidableEq Group]
    (D : paper_measure_group_allocation_data Applicant Outcome Group)
    (threshold : Group → paper_cost_aware_extended_threshold)
    (alpha : Group → ℝ) :
    MeasureGroupAllocationData.AllocationPolicy Applicant Outcome :=
  D.groupwiseExtendedScoreThresholdPolicy threshold alpha

/--
Appendix Definition 3 written directly as the source's posterior-utility over
allocation-cost comparison, including the two endpoint threshold policies.
-/
def paper_cost_aware_groupwise_threshold_policy
    {Applicant Outcome Group : Type*} [Fintype Applicant]
    [MeasurableSpace Outcome]
    (D : paper_measure_group_allocation_data Applicant Outcome Group)
    (threshold : Group → paper_cost_aware_extended_threshold)
    (alpha : Group → ℝ)
    (policy : MeasureGroupAllocationData.AllocationPolicy Applicant Outcome) : Prop :=
  (∀ g, 0 ≤ alpha g ∧ alpha g ≤ 1) ∧
    ∀ item outcome,
      match threshold (D.group item) with
      | .negInf => policy item outcome = 1
      | .finite t =>
          (t < D.posteriorUtility item outcome / D.allocCost item →
            policy item outcome = 1) ∧
          (D.posteriorUtility item outcome / D.allocCost item = t →
            policy item outcome = alpha (D.group item)) ∧
          (D.posteriorUtility item outcome / D.allocCost item < t →
            policy item outcome = 0)
      | .posInf => policy item outcome = 0

/--
The appendix's literal single-group endpoint-aware cost-aware threshold rule.
It is the one-group version of the displayed Definition 3 policy.
-/
def paper_measure_single_cost_aware_threshold_policy
    {Applicant Outcome : Type*} [Fintype Applicant]
    [MeasurableSpace Outcome]
    (D : MeasureCostAwareData Applicant Outcome)
    (threshold : paper_cost_aware_extended_threshold) (alpha : ℝ)
    (policy : MeasureCostAwareData.AllocationPolicy Applicant Outcome) : Prop :=
  0 ≤ alpha ∧ alpha ≤ 1 ∧
    ∀ item outcome,
      match threshold with
      | .negInf => policy item outcome = 1
      | .finite t =>
          (t < D.posteriorUtility item outcome / D.allocCost item →
            policy item outcome = 1) ∧
          (D.posteriorUtility item outcome / D.allocCost item = t →
            policy item outcome = alpha) ∧
          (D.posteriorUtility item outcome / D.allocCost item < t →
            policy item outcome = 0)
      | .posInf => policy item outcome = 0

/-- The canonical endpoint-aware score rule satisfies the source definition. -/
theorem paper_measure_single_cost_aware_threshold_policy_source_definition
    {Applicant Outcome : Type*} [Fintype Applicant]
    [MeasurableSpace Outcome]
    (D : MeasureCostAwareData Applicant Outcome)
    (threshold : paper_cost_aware_extended_threshold) (alpha : ℝ)
    (halpha : 0 ≤ alpha ∧ alpha ≤ 1) :
    paper_measure_single_cost_aware_threshold_policy D threshold alpha
      (D.extendedScoreThresholdPolicy threshold alpha) := by
  refine ⟨halpha.1, halpha.2, ?_⟩
  intro item outcome
  cases hthreshold : threshold with
  | negInf =>
      simp [MeasureCostAwareData.extendedScoreThresholdPolicy]
  | finite t =>
      constructor
      · intro hgt
        simp [MeasureCostAwareData.extendedScoreThresholdPolicy,
          MeasureCostAwareData.scoreThresholdPolicy, MeasureCostAwareData.score,
          hgt]
      constructor
      · intro heq
        simp [MeasureCostAwareData.extendedScoreThresholdPolicy,
          MeasureCostAwareData.scoreThresholdPolicy, MeasureCostAwareData.score,
          heq]
      · intro hlt
        have hnot : ¬ t < D.posteriorUtility item outcome / D.allocCost item :=
          not_lt.mpr hlt.le
        simp [MeasureCostAwareData.extendedScoreThresholdPolicy,
          MeasureCostAwareData.scoreThresholdPolicy, MeasureCostAwareData.score,
          hlt, hnot]
  | posInf =>
      simp [MeasureCostAwareData.extendedScoreThresholdPolicy]

/-- The canonical grouped score-threshold policy satisfies Appendix Definition
3's direct utility-over-cost characterization. -/
theorem paper_measure_groupwise_cost_aware_threshold_policy_source_definition
    {Applicant Outcome Group : Type*} [Fintype Applicant]
    [MeasurableSpace Outcome] [DecidableEq Group]
    (D : paper_measure_group_allocation_data Applicant Outcome Group)
    (threshold : Group → paper_cost_aware_extended_threshold)
    (alpha : Group → ℝ)
    (halpha : ∀ g, 0 ≤ alpha g ∧ alpha g ≤ 1) :
    paper_cost_aware_groupwise_threshold_policy D threshold alpha
      (paper_measure_groupwise_cost_aware_threshold_policy D threshold alpha) := by
  refine ⟨halpha, ?_⟩
  intro item outcome
  cases hthreshold : threshold (D.group item) with
  | negInf =>
      simp [hthreshold,
        MeasureGroupAllocationData.groupwiseExtendedScoreThresholdPolicy,
        MeasureCostAwareData.extendedScoreThresholdPolicy]
  | finite t =>
      constructor
      · intro hgt
        simp [hthreshold,
          MeasureGroupAllocationData.groupwiseExtendedScoreThresholdPolicy,
          MeasureGroupAllocationData.groupMeasureCostAwareData,
          MeasureCostAwareData.extendedScoreThresholdPolicy,
          MeasureCostAwareData.scoreThresholdPolicy, MeasureCostAwareData.score,
          hgt]
      constructor
      · intro heq
        simp [hthreshold,
          MeasureGroupAllocationData.groupwiseExtendedScoreThresholdPolicy,
          MeasureGroupAllocationData.groupMeasureCostAwareData,
          MeasureCostAwareData.extendedScoreThresholdPolicy,
          MeasureCostAwareData.scoreThresholdPolicy, MeasureCostAwareData.score,
          heq]
      · intro hlt
        have hnot : ¬ t < D.posteriorUtility item outcome / D.allocCost item :=
          not_lt.mpr hlt.le
        simp [hthreshold,
          MeasureGroupAllocationData.groupwiseExtendedScoreThresholdPolicy,
          MeasureGroupAllocationData.groupMeasureCostAwareData,
          MeasureCostAwareData.extendedScoreThresholdPolicy,
          MeasureCostAwareData.scoreThresholdPolicy, MeasureCostAwareData.score,
          hlt, hnot]
  | posInf =>
      simp [hthreshold,
        MeasureGroupAllocationData.groupwiseExtendedScoreThresholdPolicy,
        MeasureCostAwareData.extendedScoreThresholdPolicy]

/--
Optimality for the measure-space grouped allocation replacement problem.

Source status: source-shaped optimality predicate for the allocation part of
Theorem 1 after fixing screening.
-/
abbrev paper_measure_group_allocation_optimal
    {Applicant Outcome Group : Type*} [Fintype Applicant]
    [MeasurableSpace Outcome] [DecidableEq Group]
    (D : paper_measure_group_allocation_data Applicant Outcome Group)
    (budget : ℝ) (diversityTarget : Group → ℝ)
    (policy : MeasureGroupAllocationData.AllocationPolicy Applicant Outcome) :
    Prop :=
  D.SourceOptimal budget diversityTarget policy

/--
Optimality for the measure-space equality-diversity allocation problem.

Source status: source-shaped optimality predicate for Lemma 3's equality
diversity variant after fixing screening.
-/
abbrev paper_measure_group_allocation_equality_optimal
    {Applicant Outcome Group : Type*} [Fintype Applicant]
    [MeasurableSpace Outcome] [DecidableEq Group]
    (D : paper_measure_group_allocation_data Applicant Outcome Group)
    (budget : ℝ) (equalityTarget : Group → ℝ)
    (policy : MeasureGroupAllocationData.AllocationPolicy Applicant Outcome) :
    Prop :=
  D.SourceEqualityOptimal budget equalityTarget policy

/--
Theorem 1, source-general threshold-replacement endpoint.

Source status: derived measure-space version of Theorem 1's
threshold-policy sufficiency claim after fixing screening. The replacement is
explicitly a groupwise endpoint-aware cost-aware threshold policy.
-/
theorem paper_theorem1_measure_positive_cost_threshold_replacement_optimal
    {Applicant Outcome Group : Type*} [Fintype Applicant]
    [MeasurableSpace Outcome] [Fintype Group] [DecidableEq Group]
    (D : paper_measure_group_allocation_data Applicant Outcome Group)
    [IsFiniteMeasure D.law]
    (budget : ℝ) (diversityTarget : Group → ℝ)
    (original : MeasureGroupAllocationData.AllocationPolicy Applicant Outcome)
    (horiginal :
      paper_measure_group_allocation_optimal
        D budget diversityTarget original)
    (hcost_pos : ∀ item, 0 < D.allocCost item) :
    ∃ threshold : Group → paper_cost_aware_extended_threshold,
      ∃ alpha : Group → ℝ,
        ∃ replacement :
            MeasureGroupAllocationData.AllocationPolicy Applicant Outcome,
          (∀ g, 0 ≤ alpha g ∧ alpha g ≤ 1) ∧
            replacement =
              paper_measure_groupwise_cost_aware_threshold_policy
                D threshold alpha ∧
              paper_measure_group_allocation_optimal
                D budget diversityTarget replacement :=
  D.exists_sourceOptimal_groupwise_threshold_replacement_with_witness
    budget diversityTarget original horiginal hcost_pos

/-- Appendix Theorem 1 with its threshold replacement stated through the
source's direct cost-aware threshold-policy predicate. -/
theorem paper_theorem1_measure_positive_cost_threshold_source_policy_optimal
    {Applicant Outcome Group : Type*} [Fintype Applicant]
    [MeasurableSpace Outcome] [Fintype Group] [DecidableEq Group]
    (D : paper_measure_group_allocation_data Applicant Outcome Group)
    [IsFiniteMeasure D.law]
    (budget : ℝ) (diversityTarget : Group → ℝ)
    (original : MeasureGroupAllocationData.AllocationPolicy Applicant Outcome)
    (horiginal : paper_measure_group_allocation_optimal D budget diversityTarget original)
    (hcost_pos : ∀ item, 0 < D.allocCost item) :
    ∃ threshold : Group → paper_cost_aware_extended_threshold,
      ∃ alpha : Group → ℝ,
        ∃ replacement : MeasureGroupAllocationData.AllocationPolicy Applicant Outcome,
          (∀ g, 0 ≤ alpha g ∧ alpha g ≤ 1) ∧
            paper_cost_aware_groupwise_threshold_policy D threshold alpha replacement ∧
              paper_measure_group_allocation_optimal D budget diversityTarget replacement := by
  rcases paper_theorem1_measure_positive_cost_threshold_replacement_optimal
      D budget diversityTarget original horiginal hcost_pos with
    ⟨threshold, alpha, replacement, halpha, hreplacement, hoptimal⟩
  refine ⟨threshold, alpha, replacement, halpha, ?_, hoptimal⟩
  rw [hreplacement]
  exact paper_measure_groupwise_cost_aware_threshold_policy_source_definition
    D threshold alpha halpha

/--
Lemma 3, source-general equality-diversity threshold-replacement endpoint.

Source status: derived measure-space version of Lemma 3 after fixing
screening. The replacement is explicitly a groupwise endpoint-aware
cost-aware threshold policy and remains optimal under equality group-utility
constraints.
-/
theorem paper_lemma3_measure_positive_cost_equality_threshold_replacement_optimal
    {Applicant Outcome Group : Type*} [Fintype Applicant]
    [MeasurableSpace Outcome] [Fintype Group] [DecidableEq Group]
    (D : paper_measure_group_allocation_data Applicant Outcome Group)
    [IsFiniteMeasure D.law]
    (budget : ℝ) (equalityTarget : Group → ℝ)
    (original : MeasureGroupAllocationData.AllocationPolicy Applicant Outcome)
    (horiginal :
      paper_measure_group_allocation_equality_optimal
        D budget equalityTarget original)
    (hequalityTarget_nonneg :
      ∀ g : Group, 0 ≤ equalityTarget g)
    (hcost_pos : ∀ item, 0 < D.allocCost item) :
    ∃ threshold : Group → paper_cost_aware_extended_threshold,
      ∃ alpha : Group → ℝ,
        ∃ replacement :
            MeasureGroupAllocationData.AllocationPolicy Applicant Outcome,
          (∀ g, 0 ≤ alpha g ∧ alpha g ≤ 1) ∧
            replacement =
              paper_measure_groupwise_cost_aware_threshold_policy
                D threshold alpha ∧
              paper_measure_group_allocation_equality_optimal
                D budget equalityTarget replacement :=
  D.exists_sourceEqualityOptimal_groupwise_threshold_replacement_with_witness_signed_nonnegative_targets
    budget equalityTarget original horiginal hequalityTarget_nonneg hcost_pos

/-- Appendix Lemma 3 with the replacement policy expressed by the direct
cost-aware threshold condition from Appendix Definition 3. -/
theorem paper_lemma3_measure_positive_cost_equality_threshold_source_policy_optimal
    {Applicant Outcome Group : Type*} [Fintype Applicant]
    [MeasurableSpace Outcome] [Fintype Group] [DecidableEq Group]
    (D : paper_measure_group_allocation_data Applicant Outcome Group)
    [IsFiniteMeasure D.law]
    (budget : ℝ) (equalityTarget : Group → ℝ)
    (original : MeasureGroupAllocationData.AllocationPolicy Applicant Outcome)
    (horiginal : paper_measure_group_allocation_equality_optimal D budget equalityTarget original)
    (hequalityTarget_nonneg : ∀ g : Group, 0 ≤ equalityTarget g)
    (hcost_pos : ∀ item, 0 < D.allocCost item) :
    ∃ threshold : Group → paper_cost_aware_extended_threshold,
      ∃ alpha : Group → ℝ,
        ∃ replacement : MeasureGroupAllocationData.AllocationPolicy Applicant Outcome,
          (∀ g, 0 ≤ alpha g ∧ alpha g ≤ 1) ∧
            paper_cost_aware_groupwise_threshold_policy D threshold alpha replacement ∧
              paper_measure_group_allocation_equality_optimal
                D budget equalityTarget replacement := by
  rcases paper_lemma3_measure_positive_cost_equality_threshold_replacement_optimal
      D budget equalityTarget original horiginal hequalityTarget_nonneg hcost_pos with
    ⟨threshold, alpha, replacement, halpha, hreplacement, hoptimal⟩
  refine ⟨threshold, alpha, replacement, halpha, ?_, hoptimal⟩
  rw [hreplacement]
  exact paper_measure_groupwise_cost_aware_threshold_policy_source_definition
    D threshold alpha halpha

/--
Theorem 1, finite-support threshold-replacement endpoint.

Source status: derived finite-support version of Theorem 1's threshold-policy
sufficiency claim after fixing screening, under nonnegative weights, positive
allocation costs, bounded allocation probabilities, and positive group cost
mass.
-/
theorem paper_theorem1_finite_positive_cost_threshold_replacement_optimal
    {Applicant State Group : Type*} [Fintype Applicant] [Fintype State]
    [Fintype Group] [DecidableEq Group]
    (D : paper_group_allocation_data Applicant State Group)
    (budget : ℝ) (diversityTarget : Group → ℝ)
    (original : GroupAllocationData.AllocationPolicy Applicant State)
    (horiginal : paper_group_allocation_optimal D budget diversityTarget original)
    (hweight : ∀ state, 0 ≤ D.weight state)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (htotal_pos :
      ∀ g : Group,
        0 < finiteAtomTotalMass ((D.groupCostAwareData g).costAtomMass)) :
    ∃ threshold alpha : Group → ℝ,
      ∃ replacement : GroupAllocationData.AllocationPolicy Applicant State,
        (∀ g, 0 ≤ alpha g ∧ alpha g ≤ 1) ∧
          D.IsGroupwiseSingleCostAwareThresholdPolicy
            threshold alpha replacement ∧
            paper_group_allocation_optimal
              D budget diversityTarget replacement :=
  D.exists_sourceOptimal_groupwise_threshold_replacement_of_finite_positive_costs
    budget diversityTarget original horiginal hweight hcost_pos htotal_pos

/--
Lemma 3, finite-support equality-diversity endpoint.

Source status: statement-freeze for the finite-support source-shaped version
of Lemma 3's equality-diversity threshold-policy sufficiency claim after fixing
screening. Unlike the earlier restricted theorem, this target keeps only the
source-level nonnegative group equality targets and does not assume pointwise
posterior-utility nonnegativity or positive utility mass.
-/
theorem paper_lemma3_finite_positive_cost_equality_threshold_replacement_optimal
    {Applicant State Group : Type*} [Fintype Applicant] [Fintype State]
    [Fintype Group] [DecidableEq Group]
    (D : paper_group_allocation_data Applicant State Group)
    (budget : ℝ) (equalityTarget : Group → ℝ)
    (original : GroupAllocationData.AllocationPolicy Applicant State)
    (horiginal :
      paper_group_allocation_equality_optimal D budget equalityTarget original)
    (hweight : ∀ state, 0 ≤ D.weight state)
    (hequalityTarget_nonneg : ∀ g : Group, 0 ≤ equalityTarget g)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    :
    ∃ threshold alpha : Group → ℝ,
      ∃ replacement : GroupAllocationData.AllocationPolicy Applicant State,
        (∀ g, 0 ≤ alpha g ∧ alpha g ≤ 1) ∧
          D.IsGroupwiseSingleCostAwareThresholdPolicy
            threshold alpha replacement ∧
            paper_group_allocation_equality_optimal
              D budget equalityTarget replacement :=
  D.exists_sourceEqualityOptimal_groupwise_threshold_replacement_of_finite_signed_nonnegative_targets
    budget equalityTarget original horiginal hweight hequalityTarget_nonneg
    hcost_pos

/--
Fixed-threshold source data.

Source status: Section 3 definitions immediately before Eqs. (obj),
(constr1), and (constr2): `q_i`, `e_i`, `o_i`, `mu_i`, costs, budget, and
diversity targets are treated as fixed constants for a chosen threshold policy.
-/
abbrev paper_fixed_threshold_data (Applicant Group : Type*) :=
  FixedThresholdLPSourceData Applicant Group

/--
Equation (obj), displayed expected utility for a fixed threshold policy.

Source status: direct formalization of Eq. (obj).
-/
noncomputable abbrev paper_equation_obj
    {Applicant Group : Type*} [Fintype Applicant]
    (D : paper_fixed_threshold_data Applicant Group) (p : Applicant → ℝ) : ℝ :=
  D.toFixedThresholdData.utility p

/--
Equation (constr1), displayed expected budget use for a fixed threshold policy.

Source status: direct formalization of Eq. (constr1).
-/
noncomputable abbrev paper_equation_constr1
    {Applicant Group : Type*} [Fintype Applicant]
    (D : paper_fixed_threshold_data Applicant Group) (p : Applicant → ℝ) : ℝ :=
  D.toFixedThresholdData.budgetUse p

/--
Equation (constr2), displayed expected group utility for a fixed threshold
policy.

Source status: direct formalization of Eq. (constr2).
-/
noncomputable abbrev paper_equation_constr2
    {Applicant Group : Type*} [Fintype Applicant] [DecidableEq Group]
    (D : paper_fixed_threshold_data Applicant Group) (g : Group)
    (p : Applicant → ℝ) : ℝ :=
  D.toFixedThresholdData.groupUtility g p

/--
Section 3 claim: Eq. (obj) is linear/affine in the screening probabilities.

Source status: derived algebraic bridge from Eq. (obj).
-/
theorem paper_equation_obj_affine
    {Applicant Group : Type*} [Fintype Applicant]
    (D : paper_fixed_threshold_data Applicant Group) (p : Applicant → ℝ) :
    paper_equation_obj D p =
      D.baseUtility + ∑ i : Applicant, D.utilityCoeff i * p i :=
  D.toFixedThresholdData.utility_eq_base_add p

/--
Section 3 claim: Eq. (constr1) is linear/affine in the screening
probabilities.

Source status: derived algebraic bridge from Eq. (constr1).
-/
theorem paper_equation_constr1_affine
    {Applicant Group : Type*} [Fintype Applicant]
    (D : paper_fixed_threshold_data Applicant Group) (p : Applicant → ℝ) :
    paper_equation_constr1 D p =
      D.baseBudgetUse + ∑ i : Applicant, D.budgetCoeff i * p i :=
  D.toFixedThresholdData.budgetUse_eq_base_add p

/--
Section 3 claim: each Eq. (constr2) group-utility expression is linear/affine
in the screening probabilities.

Source status: derived algebraic bridge from Eq. (constr2).
-/
theorem paper_equation_constr2_affine
    {Applicant Group : Type*} [Fintype Applicant] [DecidableEq Group]
    (D : paper_fixed_threshold_data Applicant Group) (g : Group)
    (p : Applicant → ℝ) :
    paper_equation_constr2 D g p =
      D.baseGroupUtility g +
        ∑ i : Applicant, D.groupUtilityCoeff g i * p i :=
  D.toFixedThresholdData.groupUtility_eq_base_add g p

/--
The standard finite LP objective is Eq. (obj) with its constant term removed.

Source status: Section 3 LP bridge, using the shared `StandardMaxLP` library.
-/
theorem paper_fixed_threshold_lp_objective_eq_utility_sub_base
    {Applicant Group : Type*}
    [Fintype Applicant] [Fintype Group] [DecidableEq Applicant]
    [DecidableEq Group]
    (D : paper_fixed_threshold_data Applicant Group) (p : Applicant → ℝ) :
    (D.toFixedThresholdData.fixedThresholdLP).primalObjective p =
      paper_equation_obj D p - D.toFixedThresholdData.baseUtility :=
  D.toFixedThresholdData.fixedThresholdLP_objective_eq_utility_sub_base p

/--
The standard finite LP budget row is equivalent to Eq. (constr1)'s budget
inequality.

Source status: Section 3 LP bridge for the budget constraint.
-/
theorem paper_fixed_threshold_lp_budget_row_iff
    {Applicant Group : Type*}
    [Fintype Applicant] [Fintype Group] [DecidableEq Applicant]
    [DecidableEq Group]
    (D : paper_fixed_threshold_data Applicant Group) (p : Applicant → ℝ) :
    (∑ i : Applicant,
        D.toFixedThresholdData.fixedThresholdLP.A
            (.budget : FixedThresholdConstraint Applicant Group) i * p i) ≤
        D.toFixedThresholdData.fixedThresholdLP.b
            (.budget : FixedThresholdConstraint Applicant Group) ↔
      paper_equation_constr1 D p ≤ D.toFixedThresholdData.budget :=
  D.toFixedThresholdData.fixedThresholdLP_budget_row_iff p

/--
The standard finite LP diversity row is equivalent to Eq. (constr2)'s lower
bound for a group.

Source status: Section 3 LP bridge for diversity constraints.
-/
theorem paper_fixed_threshold_lp_diversity_row_iff
    {Applicant Group : Type*}
    [Fintype Applicant] [Fintype Group] [DecidableEq Applicant]
    [DecidableEq Group]
    (D : paper_fixed_threshold_data Applicant Group) (g : Group)
    (p : Applicant → ℝ) :
    (∑ i : Applicant,
        D.toFixedThresholdData.fixedThresholdLP.A
            (.diversity g : FixedThresholdConstraint Applicant Group) i *
          p i) ≤
        D.toFixedThresholdData.fixedThresholdLP.b
            (.diversity g : FixedThresholdConstraint Applicant Group) ↔
      D.toFixedThresholdData.diversityTarget g ≤ paper_equation_constr2 D g p :=
  D.toFixedThresholdData.fixedThresholdLP_diversity_row_iff g p

/--
The standard finite LP upper-bound row is the probability upper bound
`p_i <= 1`.

Source status: Section 3 LP bridge for probability-vector constraints.
-/
theorem paper_fixed_threshold_lp_probability_upper_row_iff
    {Applicant Group : Type*}
    [Fintype Applicant] [Fintype Group] [DecidableEq Applicant]
    [DecidableEq Group]
    (D : paper_fixed_threshold_data Applicant Group) (p : Applicant → ℝ)
    (i : Applicant) :
    (∑ j : Applicant,
        D.toFixedThresholdData.fixedThresholdLP.A
            (.probabilityUpper i : FixedThresholdConstraint Applicant Group) j *
          p j) ≤
        D.toFixedThresholdData.fixedThresholdLP.b
            (.probabilityUpper i : FixedThresholdConstraint Applicant Group) ↔
      p i ≤ 1 :=
  D.toFixedThresholdData.fixedThresholdLP_probabilityUpper_row_iff p i

/--
Appendix optimized-procedure two-group data.

Source status: source data for Eqs. (lp1)--(lp5), with one screened group and
one direct-allocation group.
-/
abbrev paper_optimized_two_group_data
    (ScreenApplicant DirectApplicant : Type*) :=
  OptimizedTwoGroupLPSourceData ScreenApplicant DirectApplicant

/--
Equation (lp1), optimized two-group objective.

Source status: direct formalization of Eq. (lp1).
-/
noncomputable abbrev paper_equation_lp1
    {ScreenApplicant DirectApplicant : Type*}
    [Fintype ScreenApplicant] [Fintype DirectApplicant]
    (D : paper_optimized_two_group_data ScreenApplicant DirectApplicant)
    (p : ScreenApplicant → ℝ) (a : DirectApplicant → ℝ) : ℝ :=
  D.toOptimizedTwoGroupData.utility p a

/--
Equation (lp2), optimized two-group budget use.

Source status: direct formalization of Eq. (lp2)'s right-hand-side budget use.
-/
noncomputable abbrev paper_equation_lp2
    {ScreenApplicant DirectApplicant : Type*}
    [Fintype ScreenApplicant] [Fintype DirectApplicant]
    (D : paper_optimized_two_group_data ScreenApplicant DirectApplicant)
    (p : ScreenApplicant → ℝ) (a : DirectApplicant → ℝ) : ℝ :=
  D.toOptimizedTwoGroupData.budgetUse p a

/--
Equation (lp3), screened-group utility equality expression.

Source status: direct formalization of Eq. (lp3).
-/
noncomputable abbrev paper_equation_lp3
    {ScreenApplicant DirectApplicant : Type*}
    [Fintype ScreenApplicant] [Fintype DirectApplicant]
    (D : paper_optimized_two_group_data ScreenApplicant DirectApplicant)
    (p : ScreenApplicant → ℝ) : ℝ :=
  D.toOptimizedTwoGroupData.screenedGroupUtility p

/--
Equation (lp4), direct-allocation group utility equality expression.

Source status: direct formalization of Eq. (lp4).
-/
noncomputable abbrev paper_equation_lp4
    {ScreenApplicant DirectApplicant : Type*}
    [Fintype ScreenApplicant] [Fintype DirectApplicant]
    (D : paper_optimized_two_group_data ScreenApplicant DirectApplicant)
    (a : DirectApplicant → ℝ) : ℝ :=
  D.toOptimizedTwoGroupData.directGroupUtility a

/--
Equation (lp5), with the source's probability-vector domain.

Source status: the display gives upper bounds and its surrounding source text
declares both decision vectors to be probability vectors.
-/
abbrev paper_equation_lp5
    {ScreenApplicant DirectApplicant : Type*}
    [Fintype ScreenApplicant] [Fintype DirectApplicant]
    (D : paper_optimized_two_group_data ScreenApplicant DirectApplicant)
    (p : ScreenApplicant → ℝ) (a : DirectApplicant → ℝ) : Prop :=
  D.probabilityBounds p a

/--
Equation (lp5) states that both optimized decision vectors are probability
vectors, so every coordinate lies in the unit interval.

Source status: explicit expansion of Eq. (lp5)'s probability-vector upper
bounds.
-/
theorem paper_equation_lp5_iff
    {ScreenApplicant DirectApplicant : Type*}
    [Fintype ScreenApplicant] [Fintype DirectApplicant]
    (D : paper_optimized_two_group_data ScreenApplicant DirectApplicant)
    (p : ScreenApplicant → ℝ) (a : DirectApplicant → ℝ) :
    paper_equation_lp5 D p a ↔
      (∀ i : ScreenApplicant, 0 ≤ p i ∧ p i ≤ 1) ∧
        ∀ i : DirectApplicant, 0 ≤ a i ∧ a i ≤ 1 :=
  Iff.rfl

/-- Equation (lp5) with both probability-vector bounds visible. -/
theorem paper_equation_lp5_source_formula
    {ScreenApplicant DirectApplicant : Type*}
    [Fintype ScreenApplicant] [Fintype DirectApplicant]
    (D : paper_optimized_two_group_data ScreenApplicant DirectApplicant)
    (p : ScreenApplicant → ℝ) (a : DirectApplicant → ℝ) :
    paper_equation_lp5 D p a ↔
      (∀ i : ScreenApplicant, 0 ≤ p i ∧ p i ≤ 1) ∧
        ∀ i : DirectApplicant, 0 ≤ a i ∧ a i ≤ 1 :=
  paper_equation_lp5_iff D p a

/--
Equation (lp1) is affine in the optimized variables.

Source status: derived algebraic bridge from Eq. (lp1).
-/
theorem paper_equation_lp1_affine
    {ScreenApplicant DirectApplicant : Type*}
    [Fintype ScreenApplicant] [Fintype DirectApplicant]
    (D : paper_optimized_two_group_data ScreenApplicant DirectApplicant)
    (p : ScreenApplicant → ℝ) (a : DirectApplicant → ℝ) :
    paper_equation_lp1 D p a =
      D.baseUtility +
        (∑ i : ScreenApplicant, D.screenUtilityCoeff i * p i) +
          (∑ i : DirectApplicant, D.muDirect i * a i) :=
  D.toOptimizedTwoGroupData.utility_eq_base_add p a

/--
Equation (lp2) is affine in the optimized variables.

Source status: derived algebraic bridge from Eq. (lp2).
-/
theorem paper_equation_lp2_affine
    {ScreenApplicant DirectApplicant : Type*}
    [Fintype ScreenApplicant] [Fintype DirectApplicant]
    (D : paper_optimized_two_group_data ScreenApplicant DirectApplicant)
    (p : ScreenApplicant → ℝ) (a : DirectApplicant → ℝ) :
    paper_equation_lp2 D p a =
      D.baseBudgetUse +
        (∑ i : ScreenApplicant, D.screenBudgetCoeff i * p i) +
          (∑ i : DirectApplicant, D.allocCost * a i) :=
  D.budgetUse_eq_base_add p a

/--
Equation (lp3) is affine in the screened-group screening probabilities.

Source status: derived algebraic bridge from Eq. (lp3).
-/
theorem paper_equation_lp3_affine
    {ScreenApplicant DirectApplicant : Type*}
    [Fintype ScreenApplicant] [Fintype DirectApplicant]
    (D : paper_optimized_two_group_data ScreenApplicant DirectApplicant)
    (p : ScreenApplicant → ℝ) :
    paper_equation_lp3 D p =
      D.baseUtility +
        (∑ i : ScreenApplicant, D.screenUtilityCoeff i * p i) :=
  D.screenedGroupUtility_eq_base_add p

/-- Equation (obj) with the fixed-threshold source expression displayed
directly rather than through the implementation's objective alias. -/
theorem paper_equation_obj_source_formula
    {Applicant Group : Type*} [Fintype Applicant]
    (D : paper_fixed_threshold_data Applicant Group) (p : Applicant → ℝ) :
    paper_equation_obj D p =
      ∑ i : Applicant, (D.q i * D.e i * p i + D.o i * D.mu i * (1 - p i)) :=
  rfl

/-- Equation (constr1) is the displayed fixed-threshold budget inequality. -/
theorem paper_equation_constr1_source_formula
    {Applicant Group : Type*} [Fintype Applicant]
    (D : paper_fixed_threshold_data Applicant Group) (p : Applicant → ℝ) :
    paper_equation_constr1 D p ≤ D.budget ↔
      (∑ i : Applicant,
        (D.screenCost * p i + D.allocCost * D.q i * p i +
          D.allocCost * D.o i * (1 - p i))) ≤ D.budget :=
  Iff.rfl

/-- Equation (constr2) is the displayed per-group utility lower bound. -/
theorem paper_equation_constr2_source_formula
    {Applicant Group : Type*} [Fintype Applicant] [DecidableEq Group]
    (D : paper_fixed_threshold_data Applicant Group) (g : Group)
    (p : Applicant → ℝ) :
    D.diversityTarget g ≤ paper_equation_constr2 D g p ↔
      D.diversityTarget g ≤
        ∑ i : Applicant, (if D.group i = g then
            D.q i * D.e i * p i + D.o i * D.mu i * (1 - p i)
          else 0) :=
  Iff.rfl

/-- Equation (lp1) with both source variable blocks displayed directly. -/
theorem paper_equation_lp1_source_formula
    {ScreenApplicant DirectApplicant : Type*}
    [Fintype ScreenApplicant] [Fintype DirectApplicant]
    (D : paper_optimized_two_group_data ScreenApplicant DirectApplicant)
    (p : ScreenApplicant → ℝ) (a : DirectApplicant → ℝ) :
    paper_equation_lp1 D p a =
      (∑ i : ScreenApplicant,
        (D.q i * D.e i * p i + D.o i * D.muScreen i * (1 - p i))) +
        ∑ i : DirectApplicant, D.muDirect i * a i :=
  rfl

/-- Equation (lp2) is the displayed optimized-procedure budget inequality. -/
theorem paper_equation_lp2_source_formula
    {ScreenApplicant DirectApplicant : Type*}
    [Fintype ScreenApplicant] [Fintype DirectApplicant]
    (D : paper_optimized_two_group_data ScreenApplicant DirectApplicant)
    (p : ScreenApplicant → ℝ) (a : DirectApplicant → ℝ) :
    paper_equation_lp2 D p a ≤ D.budget ↔
      (∑ i : ScreenApplicant,
        (D.screenCost * p i + D.allocCost * D.q i * p i +
          D.allocCost * D.o i * (1 - p i))) +
          (∑ i : DirectApplicant, D.allocCost * a i) ≤ D.budget :=
  Iff.rfl

/-- Equation (lp3) is the source's screened-group equality condition. -/
theorem paper_equation_lp3_source_formula
    {ScreenApplicant DirectApplicant : Type*}
    [Fintype ScreenApplicant] [Fintype DirectApplicant]
    (D : paper_optimized_two_group_data ScreenApplicant DirectApplicant)
    (p : ScreenApplicant → ℝ) :
    paper_equation_lp3 D p = D.lambdaScreen ↔
      (∑ i : ScreenApplicant,
        (D.q i * D.e i * p i + D.o i * D.muScreen i * (1 - p i))) =
          D.lambdaScreen :=
  Iff.rfl

/-- Equation (lp4) is the source's direct-allocation group equality condition. -/
theorem paper_equation_lp4_source_formula
    {ScreenApplicant DirectApplicant : Type*}
    [Fintype ScreenApplicant] [Fintype DirectApplicant]
    (D : paper_optimized_two_group_data ScreenApplicant DirectApplicant)
    (a : DirectApplicant → ℝ) :
    paper_equation_lp4 D a = D.lambdaDirect ↔
      (∑ i : DirectApplicant, D.muDirect i * a i) = D.lambdaDirect :=
  Iff.rfl

/-- Multiplying a finite score cutoff by a common positive allocation cost;
the infinite cutoffs remain the corresponding endpoint policies. -/
def paper_scale_score_threshold (c : ℝ) (threshold : RealThreshold) : RealThreshold :=
  match threshold with
  | .negInf => .negInf
  | .finite t => .finite (c * t)
  | .posInf => .posInf

/--
Source data for the joint screening-and-allocation optimization problem.
Unlike the downstream allocation slice, this records the screening policy that
the paper keeps fixed when replacing the allocation policy.
-/
abbrev paper_screening_allocation_data
    (Applicant Outcome Group : Type*) [Fintype Applicant] [MeasurableSpace Outcome] :=
  ScreeningAllocationData Applicant Outcome Group

/-- A source screening policy together with its post-screening allocation policy. -/
abbrev paper_screening_allocation_pair
    {Applicant Outcome Group : Type*} [Fintype Applicant] [MeasurableSpace Outcome]
    (D : paper_screening_allocation_data Applicant Outcome Group) :=
  ScreeningAllocationData.PolicyPair D

/-- Appendix Definition 3 as a source allocation rule with input exactly the
full post-screening estimate vector. -/
noncomputable def paper_cost_aware_threshold_rule
    {Applicant Outcome Group : Type*} [Fintype Applicant] [MeasurableSpace Outcome]
    (D : paper_screening_allocation_data Applicant Outcome Group)
    (threshold : Group → paper_cost_aware_extended_threshold)
    (alpha : Group → ℝ) :
    ScreeningAllocationData.PostScreeningAllocationRule Applicant :=
  fun estimates item =>
    match threshold (D.group item) with
    | .negInf => 1
    | .finite t =>
        if t < estimates item / D.allocCost item then 1
        else if estimates item / D.allocCost item < t then 0
        else alpha (D.group item)
    | .posInf => 0

/-- The explicit Appendix Definition 3 rule is Borel measurable in `hat U`. -/
theorem paper_cost_aware_threshold_rule_measurable
    {Applicant Outcome Group : Type*} [Fintype Applicant] [MeasurableSpace Outcome]
    (D : paper_screening_allocation_data Applicant Outcome Group)
    (threshold : Group → paper_cost_aware_extended_threshold)
    (alpha : Group → ℝ) (item : Applicant) :
    Measurable fun estimates => paper_cost_aware_threshold_rule D threshold alpha estimates item := by
  cases hthreshold : threshold (D.group item) with
  | negInf => simp [paper_cost_aware_threshold_rule, hthreshold]
  | finite t =>
      have hscore : Measurable fun estimates : Applicant → ℝ =>
          estimates item / D.allocCost item :=
        (measurable_pi_apply item).div_const _
      simp only [paper_cost_aware_threshold_rule, hthreshold]
      exact Measurable.ite (measurableSet_lt measurable_const hscore) measurable_const
        (Measurable.ite (measurableSet_lt hscore measurable_const)
          measurable_const measurable_const)
  | posInf => simp [paper_cost_aware_threshold_rule, hthreshold]

/-- Evaluating the explicit Appendix Definition 3 rule gives the existing
score-threshold allocation policy. -/
theorem paper_evaluate_cost_aware_threshold_rule
    {Applicant Outcome Group : Type*} [Fintype Applicant] [MeasurableSpace Outcome]
    [DecidableEq Group]
    (D : paper_screening_allocation_data Applicant Outcome Group)
    (p : ScreeningPolicy Applicant)
    (threshold : Group → paper_cost_aware_extended_threshold)
    (alpha : Group → ℝ) :
    D.evaluatePostScreeningAllocationRule p
      (paper_cost_aware_threshold_rule D threshold alpha) =
      paper_measure_groupwise_cost_aware_threshold_policy
        (D.post p) threshold alpha := by
  funext item outcome
  cases hthreshold : threshold (D.group item) <;>
    simp [ScreeningAllocationData.evaluatePostScreeningAllocationRule,
      paper_cost_aware_threshold_rule, hthreshold,
      D.post_group p, D.post_allocCost p,
      MeasureGroupAllocationData.groupwiseExtendedScoreThresholdPolicy,
      MeasureGroupAllocationData.groupMeasureCostAwareData,
      MeasureCostAwareData.extendedScoreThresholdPolicy,
      MeasureCostAwareData.scoreThresholdPolicy, MeasureCostAwareData.score]

/--
Main-text Definition 1, threshold-policy condition.  With the paper's common
allocation cost, an applicant is selected according to whether its posterior
utility is above, at, or below the threshold of its demographic group.
-/
def paper_main_text_groupwise_threshold_policy
    {Applicant Outcome Group : Type*} [Fintype Applicant]
    [MeasurableSpace Outcome]
    (D : paper_measure_group_allocation_data Applicant Outcome Group)
    (threshold : Group → RealThreshold) (alpha : Group → ℝ)
    (policy : MeasureGroupAllocationData.AllocationPolicy Applicant Outcome) : Prop :=
  (∀ g, 0 ≤ alpha g ∧ alpha g ≤ 1) ∧
    ∀ item outcome,
      match threshold (D.group item) with
      | .negInf => policy item outcome = 1
      | .finite t =>
          (t < D.posteriorUtility item outcome → policy item outcome = 1) ∧
          (D.posteriorUtility item outcome = t →
            policy item outcome = alpha (D.group item)) ∧
          (D.posteriorUtility item outcome < t → policy item outcome = 0)
      | .posInf => policy item outcome = 0

/-- Under a positive common allocation cost, a score-threshold policy is the
main-text utility-threshold policy obtained by rescaling every finite cutoff. -/
theorem paper_groupwise_score_threshold_is_main_text_threshold
    {Applicant Outcome Group : Type*} [Fintype Applicant]
    [MeasurableSpace Outcome] [DecidableEq Group]
    (D : paper_measure_group_allocation_data Applicant Outcome Group)
    (c : ℝ) (hc : 0 < c) (hcost : ∀ item, D.allocCost item = c)
    (threshold : Group → RealThreshold) (alpha : Group → ℝ)
    (halpha : ∀ g, 0 ≤ alpha g ∧ alpha g ≤ 1) :
    paper_main_text_groupwise_threshold_policy
      D (fun g => paper_scale_score_threshold c (threshold g)) alpha
      (D.groupwiseExtendedScoreThresholdPolicy threshold alpha) := by
  refine ⟨halpha, ?_⟩
  intro item outcome
  have hcost_item : D.allocCost item = c := hcost item
  cases hthreshold : threshold (D.group item) with
  | negInf =>
      simp only [hthreshold, paper_scale_score_threshold]
      simp [hthreshold,
        MeasureGroupAllocationData.groupwiseExtendedScoreThresholdPolicy,
        MeasureCostAwareData.extendedScoreThresholdPolicy]
  | finite t =>
      simp only [hthreshold, paper_scale_score_threshold]
      constructor
      · intro hgt
        have hscore :
            t < D.posteriorUtility item outcome / D.allocCost item := by
          rw [hcost_item]
          apply (lt_div_iff₀ hc).2
          simpa [mul_comm] using hgt
        simp [hthreshold,
          MeasureGroupAllocationData.groupwiseExtendedScoreThresholdPolicy,
          MeasureGroupAllocationData.groupMeasureCostAwareData,
          MeasureCostAwareData.extendedScoreThresholdPolicy,
          MeasureCostAwareData.scoreThresholdPolicy, MeasureCostAwareData.score,
          hscore]
      constructor
      · intro heq
        have hscore :
            D.posteriorUtility item outcome / D.allocCost item = t := by
          rw [hcost_item]
          apply (div_eq_iff (ne_of_gt hc)).2
          simpa [mul_comm] using heq
        simp [hthreshold,
          MeasureGroupAllocationData.groupwiseExtendedScoreThresholdPolicy,
          MeasureGroupAllocationData.groupMeasureCostAwareData,
          MeasureCostAwareData.extendedScoreThresholdPolicy,
          MeasureCostAwareData.scoreThresholdPolicy, MeasureCostAwareData.score,
          hscore]
      · intro hlt
        have hscore :
            D.posteriorUtility item outcome / D.allocCost item < t := by
          rw [hcost_item]
          apply (div_lt_iff₀ hc).2
          simpa [mul_comm] using hlt
        have hnot_score : ¬ t < D.posteriorUtility item outcome / D.allocCost item :=
          not_lt.mpr hscore.le
        simp [hthreshold,
          MeasureGroupAllocationData.groupwiseExtendedScoreThresholdPolicy,
          MeasureGroupAllocationData.groupMeasureCostAwareData,
          MeasureCostAwareData.extendedScoreThresholdPolicy,
          MeasureCostAwareData.scoreThresholdPolicy, MeasureCostAwareData.score,
          hscore, hnot_score]
  | posInf =>
      simp only [hthreshold, paper_scale_score_threshold]
      simp [hthreshold,
        MeasureGroupAllocationData.groupwiseExtendedScoreThresholdPolicy,
        MeasureCostAwareData.extendedScoreThresholdPolicy]

/-- A cost-aware source threshold policy is the main-text threshold policy
after multiplying each finite score threshold by a common positive cost. -/
theorem paper_cost_aware_threshold_policy_to_main_text_threshold
    {Applicant Outcome Group : Type*} [Fintype Applicant]
    [MeasurableSpace Outcome]
    (D : paper_measure_group_allocation_data Applicant Outcome Group)
    (c : ℝ) (hc : 0 < c) (hcost : ∀ item, D.allocCost item = c)
    (threshold : Group → paper_cost_aware_extended_threshold)
    (alpha : Group → ℝ)
    (policy : MeasureGroupAllocationData.AllocationPolicy Applicant Outcome)
    (hpolicy : paper_cost_aware_groupwise_threshold_policy D threshold alpha policy) :
    paper_main_text_groupwise_threshold_policy
      D (fun g => paper_scale_score_threshold c (threshold g)) alpha policy := by
  refine ⟨hpolicy.1, ?_⟩
  intro item outcome
  have hcost_item : D.allocCost item = c := hcost item
  cases hthreshold : threshold (D.group item) with
  | negInf =>
      simpa [hthreshold, paper_scale_score_threshold] using hpolicy.2 item outcome
  | finite t =>
      have hpoint := hpolicy.2 item outcome
      simp only [hthreshold] at hpoint
      simp only [hthreshold, paper_scale_score_threshold]
      constructor
      · intro hgt
        apply hpoint.1
        rw [hcost_item]
        apply (lt_div_iff₀ hc).2
        simpa [mul_comm] using hgt
      constructor
      · intro heq
        apply hpoint.2.1
        rw [hcost_item]
        apply (div_eq_iff (ne_of_gt hc)).2
        simpa [mul_comm] using heq
      · intro hlt
        apply hpoint.2.2
        rw [hcost_item]
        apply (div_lt_iff₀ hc).2
        simpa [mul_comm] using hlt
  | posInf =>
      simpa [hthreshold, paper_scale_score_threshold] using hpolicy.2 item outcome

/--
Main Theorem 1 as the constant-allocation-cost specialization of the appendix
threshold-replacement theorem.  Every optimal screening policy has an optimal
groupwise utility-threshold replacement.
-/
theorem paper_main_text_threshold_policies_suffice
    {Applicant Outcome Group : Type*} [Fintype Applicant]
    [MeasurableSpace Outcome] [Fintype Group] [DecidableEq Group]
    (D : paper_measure_group_allocation_data Applicant Outcome Group)
    [IsFiniteMeasure D.law]
    (c : ℝ) (hc : 0 < c) (hcost : ∀ item, D.allocCost item = c)
    (budget : ℝ) (diversityTarget : Group → ℝ)
    (original : MeasureGroupAllocationData.AllocationPolicy Applicant Outcome)
    (horiginal : paper_measure_group_allocation_optimal D budget diversityTarget original) :
    ∃ threshold : Group → RealThreshold,
      ∃ alpha : Group → ℝ,
        ∃ replacement : MeasureGroupAllocationData.AllocationPolicy Applicant Outcome,
          paper_main_text_groupwise_threshold_policy D threshold alpha replacement ∧
            paper_measure_group_allocation_optimal D budget diversityTarget replacement := by
  rcases paper_theorem1_measure_positive_cost_threshold_replacement_optimal
      D budget diversityTarget original horiginal
      (fun item => by rw [hcost item]; exact hc) with
    ⟨scoreThreshold, alpha, replacement, halpha, hrepl, hoptimal⟩
  refine ⟨fun g => paper_scale_score_threshold c (scoreThreshold g), alpha,
    replacement, ?_, hoptimal⟩
  rw [hrepl]
  exact paper_groupwise_score_threshold_is_main_text_threshold
    D c hc hcost scoreThreshold alpha halpha

/--
Appendix Lemma 3 in the main text's common-cost model. Its source conclusion
is the ordinary threshold rule of Definition 1, not the more general
cost-aware rule used in the appendix proof.
-/
theorem paper_lemma3_main_text_equality_threshold_sufficiency
    {Applicant Outcome Group : Type*} [Fintype Applicant]
    [MeasurableSpace Outcome] [Fintype Group] [DecidableEq Group]
    (D : paper_measure_group_allocation_data Applicant Outcome Group)
    [IsFiniteMeasure D.law]
    (c : ℝ) (hc : 0 < c) (hcost : ∀ item, D.allocCost item = c)
    (budget : ℝ) (equalityTarget : Group → ℝ)
    (original : MeasureGroupAllocationData.AllocationPolicy Applicant Outcome)
    (horiginal : paper_measure_group_allocation_equality_optimal D budget equalityTarget original)
    (hequalityTarget_nonneg : ∀ g : Group, 0 ≤ equalityTarget g) :
    ∃ threshold : Group → RealThreshold,
      ∃ alpha : Group → ℝ,
        ∃ replacement : MeasureGroupAllocationData.AllocationPolicy Applicant Outcome,
          paper_main_text_groupwise_threshold_policy D threshold alpha replacement ∧
            paper_measure_group_allocation_equality_optimal
              D budget equalityTarget replacement := by
  rcases paper_lemma3_measure_positive_cost_equality_threshold_replacement_optimal
      D budget equalityTarget original horiginal hequalityTarget_nonneg
      (fun item => by rw [hcost item]; exact hc) with
    ⟨scoreThreshold, alpha, replacement, halpha, hrepl, hoptimal⟩
  refine ⟨fun g => paper_scale_score_threshold c (scoreThreshold g), alpha,
    replacement, ?_, hoptimal⟩
  rw [hrepl]
  exact paper_groupwise_score_threshold_is_main_text_threshold
    D c hc hcost scoreThreshold alpha halpha

/--
Appendix Theorem 1 at the source's full policy-pair level.  The pair's
allocation rule has `hat U` as its only run-time input; the proof stays in that
source policy class instead of treating an arbitrary `Outcome →` policy as
admissible.
-/
theorem paper_cost_aware_threshold_policy_pairs_suffice
    {Applicant Outcome Group : Type*} [Fintype Applicant]
    [MeasurableSpace Outcome] [Fintype Group]
    (D : paper_screening_allocation_data Applicant Outcome Group)
    (budget : ℝ) (diversityTarget : Group → ℝ)
    (original : paper_screening_allocation_pair D)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (horiginal : D.PairSourceOptimal budget diversityTarget original) :
    letI : DecidableEq Group := Classical.decEq Group
    ∃ threshold : Group → RealThreshold,
      ∃ alpha : Group → ℝ,
        ∃ replacement : paper_screening_allocation_pair D,
          replacement.screening = original.screening ∧
            paper_cost_aware_groupwise_threshold_policy
              (D.post original.screening) threshold alpha replacement.allocation ∧
              D.PairSourceOptimal budget diversityTarget replacement := by
  classical
  letI : IsFiniteMeasure (D.post original.screening).law :=
    D.post_finite original.screening
  have hpost_cost_pos : ∀ item, 0 < (D.post original.screening).allocCost item := by
    intro item
    rw [D.post_allocCost]
    exact hcost_pos item
  rcases (D.post original.screening).exists_groupwiseSameCostExtendedScoreThresholdPolicy_with_witness
      original.allocation hpost_cost_pos horiginal.1.2.2.1 horiginal.1.2.1 with
    ⟨threshold, alpha, rawReplacement, halpha, hrawReplacement,
      hrawBounds, hrawMeasurable, hgroupCost, hgroupUtility⟩
  let replacement : paper_screening_allocation_pair D :=
    { screening := original.screening
      allocationRule := paper_cost_aware_threshold_rule D threshold alpha
      allocationRule_measurable := paper_cost_aware_threshold_rule_measurable D threshold alpha }
  have hreplacement_allocation : replacement.allocation = rawReplacement := by
    rw [hrawReplacement]
    exact paper_evaluate_cost_aware_threshold_rule D original.screening threshold alpha
  have hcost_total :
      (D.post original.screening).expectedCost rawReplacement =
        (D.post original.screening).expectedCost original.allocation := by
    rw [← (D.post original.screening).sum_expectedGroupCost_eq_expectedCost
        rawReplacement hrawMeasurable hrawBounds,
      ← (D.post original.screening).sum_expectedGroupCost_eq_expectedCost
        original.allocation horiginal.1.2.2.1 horiginal.1.2.1]
    exact Finset.sum_congr rfl (fun g _ => hgroupCost g)
  have hutility_total :
      (D.post original.screening).expectedPosteriorUtility original.allocation ≤
        (D.post original.screening).expectedPosteriorUtility rawReplacement := by
    rw [← (D.post original.screening).sum_expectedGroupPosteriorUtility_eq_expectedPosteriorUtility
        original.allocation horiginal.1.2.2.1 horiginal.1.2.1,
      ← (D.post original.screening).sum_expectedGroupPosteriorUtility_eq_expectedPosteriorUtility
        rawReplacement hrawMeasurable hrawBounds]
    exact Finset.sum_le_sum (fun g _ => hgroupUtility g)
  have hreplacement_feasible : D.PairSourceFeasible budget diversityTarget replacement := by
    refine ⟨horiginal.1.1, ?_, ?_, ?_, ?_⟩
    · rw [hreplacement_allocation]
      exact hrawBounds
    · rw [hreplacement_allocation]
      exact hrawMeasurable
    · rw [hreplacement_allocation, hcost_total]
      exact horiginal.1.2.2.2.1
    · intro g
      rw [hreplacement_allocation]
      exact (horiginal.1.2.2.2.2 g).trans (hgroupUtility g)
  have hreplaced : D.PairSourceOptimal budget diversityTarget replacement :=
    D.pairSourceOptimal_of_feasible_improvement budget diversityTarget
      original replacement horiginal hreplacement_feasible (by
        rw [hreplacement_allocation]
        exact hutility_total)
  refine ⟨threshold, alpha, replacement, rfl, ?_, hreplaced⟩
  rw [hreplacement_allocation, hrawReplacement]
  exact paper_measure_groupwise_cost_aware_threshold_policy_source_definition
    (D.post original.screening) threshold alpha halpha

/--
Theorem 1 at the source's full policy-pair level.  The source pair carries an
allocation rule of the post-screening estimate vector, and the threshold
replacement remains in that policy class.
-/
theorem paper_main_text_threshold_policy_pairs_suffice
    {Applicant Outcome Group : Type*} [Fintype Applicant]
    [MeasurableSpace Outcome] [Fintype Group]
    (D : paper_screening_allocation_data Applicant Outcome Group)
    (c : ℝ) (hc : 0 < c)
    (budget : ℝ) (diversityTarget : Group → ℝ)
    (original : paper_screening_allocation_pair D)
    (hcost : ∀ item, D.allocCost item = c)
    (horiginal : D.PairSourceOptimal budget diversityTarget original) :
    letI : DecidableEq Group := Classical.decEq Group
    ∃ threshold : Group → RealThreshold,
      ∃ alpha : Group → ℝ,
        ∃ replacement : paper_screening_allocation_pair D,
          replacement.screening = original.screening ∧
            paper_main_text_groupwise_threshold_policy
              (D.post original.screening) threshold alpha replacement.allocation ∧
              D.PairSourceOptimal budget diversityTarget replacement := by
  classical
  have hpost_cost : ∀ item, (D.post original.screening).allocCost item = c := by
    intro item
    rw [D.post_allocCost]
    exact hcost item
  rcases paper_cost_aware_threshold_policy_pairs_suffice
      D budget diversityTarget original (fun item => by rw [hcost item]; exact hc) horiginal with
    ⟨scoreThreshold, alpha, replacement, hscreening, hcostAware, hreplaced⟩
  refine ⟨fun g => paper_scale_score_threshold c (scoreThreshold g), alpha,
    replacement, hscreening, ?_, hreplaced⟩
  exact paper_cost_aware_threshold_policy_to_main_text_threshold
    (D.post original.screening) c hc hpost_cost scoreThreshold alpha
    replacement.allocation hcostAware

/-- Appendix Lemma 3 at the source's full equality-constrained pair level. -/
theorem paper_main_text_equality_threshold_policy_pairs_suffice
    {Applicant Outcome Group : Type*} [Fintype Applicant]
    [MeasurableSpace Outcome] [Fintype Group]
    (D : paper_screening_allocation_data Applicant Outcome Group)
    (c : ℝ) (hc : 0 < c)
    (budget : ℝ) (equalityTarget : Group → ℝ)
    (original : paper_screening_allocation_pair D)
    (hcost : ∀ item, D.allocCost item = c)
    (hequalityTarget_nonneg : ∀ g : Group, 0 ≤ equalityTarget g)
    (horiginal : D.PairSourceEqualityOptimal budget equalityTarget original) :
    letI : DecidableEq Group := Classical.decEq Group
    ∃ threshold : Group → RealThreshold,
      ∃ alpha : Group → ℝ,
        ∃ replacement : paper_screening_allocation_pair D,
          replacement.screening = original.screening ∧
          paper_main_text_groupwise_threshold_policy
            (D.post original.screening) threshold alpha replacement.allocation ∧
            D.PairSourceEqualityOptimal budget equalityTarget replacement := by
  classical
  letI : IsFiniteMeasure (D.post original.screening).law :=
    D.post_finite original.screening
  have hpost_cost : ∀ item, (D.post original.screening).allocCost item = c := by
    intro item
    rw [D.post_allocCost]
    exact hcost item
  have hpost_cost_pos : ∀ item, 0 < (D.post original.screening).allocCost item := by
    intro item
    rw [D.post_allocCost]
    rw [hcost item]
    exact hc
  rcases (D.post original.screening).exists_groupwiseSameUtilityExtendedScoreThresholdPolicy_with_witness_signed_nonnegative_targets
      original.allocation hpost_cost_pos horiginal.1.2.2.1 horiginal.1.2.1
      (by
        intro g
        rw [horiginal.1.2.2.2.2 g]
        exact hequalityTarget_nonneg g) with
    ⟨scoreThreshold, alpha, rawReplacement, halpha, hrawReplacement,
      hrawBounds, hrawMeasurable, hgroupUtility, hgroupCost⟩
  let replacement : paper_screening_allocation_pair D :=
    { screening := original.screening
      allocationRule := paper_cost_aware_threshold_rule D scoreThreshold alpha
      allocationRule_measurable := paper_cost_aware_threshold_rule_measurable D scoreThreshold alpha }
  have hreplacement_allocation : replacement.allocation = rawReplacement := by
    rw [hrawReplacement]
    exact paper_evaluate_cost_aware_threshold_rule D original.screening scoreThreshold alpha
  have hcost_total :
      (D.post original.screening).expectedCost rawReplacement ≤
        (D.post original.screening).expectedCost original.allocation := by
    rw [← (D.post original.screening).sum_expectedGroupCost_eq_expectedCost
        rawReplacement hrawMeasurable hrawBounds,
      ← (D.post original.screening).sum_expectedGroupCost_eq_expectedCost
        original.allocation horiginal.1.2.2.1 horiginal.1.2.1]
    exact Finset.sum_le_sum (fun g _ => hgroupCost g)
  have hutility_total :
      (D.post original.screening).expectedPosteriorUtility original.allocation =
        (D.post original.screening).expectedPosteriorUtility rawReplacement := by
    rw [← (D.post original.screening).sum_expectedGroupPosteriorUtility_eq_expectedPosteriorUtility
        original.allocation horiginal.1.2.2.1 horiginal.1.2.1,
      ← (D.post original.screening).sum_expectedGroupPosteriorUtility_eq_expectedPosteriorUtility
        rawReplacement hrawMeasurable hrawBounds]
    exact Finset.sum_congr rfl (fun g _ => (hgroupUtility g).symm)
  have hreplacement_feasible :
      D.PairSourceEqualityFeasible budget equalityTarget replacement := by
    refine ⟨horiginal.1.1, ?_, ?_, ?_, ?_⟩
    · rw [hreplacement_allocation]
      exact hrawBounds
    · rw [hreplacement_allocation]
      exact hrawMeasurable
    · rw [hreplacement_allocation]
      linarith [hcost_total, horiginal.1.2.2.2.1]
    · intro g
      rw [hreplacement_allocation]
      rw [hgroupUtility g]
      exact horiginal.1.2.2.2.2 g
  have hreplaced : D.PairSourceEqualityOptimal budget equalityTarget replacement :=
    D.pairSourceEqualityOptimal_of_feasible_improvement budget equalityTarget
      original replacement horiginal hreplacement_feasible (by
        rw [hreplacement_allocation]
        exact hutility_total.le)
  refine ⟨fun g => paper_scale_score_threshold c (scoreThreshold g), alpha,
    replacement, rfl, ?_, hreplaced⟩
  have hcostAware :
      paper_cost_aware_groupwise_threshold_policy
        (D.post original.screening) scoreThreshold alpha replacement.allocation := by
    rw [hreplacement_allocation, hrawReplacement]
    exact paper_measure_groupwise_cost_aware_threshold_policy_source_definition
      (D.post original.screening) scoreThreshold alpha halpha
  exact paper_cost_aware_threshold_policy_to_main_text_threshold
    (D.post original.screening) c hc hpost_cost scoreThreshold alpha
    replacement.allocation hcostAware

end ProofBridge

end CGGG20SelectiveInformationAcquisition

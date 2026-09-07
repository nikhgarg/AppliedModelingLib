import LMMS04FairDivision.ProofInterface
import LMMS04FairDivision.Assumptions

/-!
# Paper Interface: Approximately Fair Allocations of Indivisible Goods

Compact human-facing review surface for the LMMS 2004 formalization. Broad
proof-facing aliases and migration endpoints live in `ProofInterface.lean`.
-/

open MeasureTheory
open Filter
open scoped BigOperators
open AppliedModelingLib.FairDivision

namespace LMMS04FairDivision
namespace PaperInterface

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

/-- Lemma 2.2: envy-cycle elimination produces an acyclic envy graph. -/
abbrev lemma2_2_acyclic_reduction :=
  @LMMS04FairDivision.ProofInterface.lemma2_2_acyclic_reduction

/-- Theorem 2.1: bounded-envy allocation existence. -/
abbrev theorem2_1_bounded_envy_allocation_exists :=
  @LMMS04FairDivision.ProofInterface.theorem2_1_bounded_envy_allocation_exists

/-- Theorem 2.1 alpha-bounded form. -/
abbrev theorem2_1_alpha_bounded_allocation_exists :=
  @LMMS04FairDivision.ProofInterface.theorem2_1_alpha_bounded_allocation_exists

/-- Theorem 2.1 constructive list algorithm form. -/
abbrev theorem2_1_algorithm_correct_list_toFinset :=
  @LMMS04FairDivision.ProofInterface.theorem2_1_algorithm_correct_list_toFinset

/--
Theorem 2.3 real-interval supported atom-bound endpoint.
Source status: direct source text
-/
abbrev theorem2_3_real_interval_supported_atom_bound :=
  @LMMS04FairDivision.ProofInterface.theorem2_3_real_interval_supported_atom_bound

/-! ## Section 3: Approximation and PTAS Boundary -/

/--
Theorem 3.1 adaptive-query lower bound.
Source status: direct source text
-/
abbrev theorem3_1_eventually_minimum_envy_lower_bound_from_twoBit_adaptive_queries :=
  @LMMS04FairDivision.ProofInterface.theorem3_1_eventually_minimum_envy_lower_bound_from_twoBit_adaptive_queries

/--
Theorem 3.1 adaptive-query ratio lower bound.
Source status: direct source text
-/
abbrev theorem3_1_eventually_minimum_envy_ratio_lower_bound_from_twoBit_adaptive_queries :=
  @LMMS04FairDivision.ProofInterface.theorem3_1_eventually_minimum_envy_ratio_lower_bound_from_twoBit_adaptive_queries

/--
Theorem 3.2 Graham-certificate fair-division consequence.
Source status: partial external dependency
Source note: Lean proves the fair-division consequence from the Graham scheduling theorem cited by the paper.
-/
abbrev theorem3_2_graham_certificate_to_envy_ratio_bound :=
  @LMMS04FairDivision.ProofInterface.theorem3_2_graham_certificate_to_envy_ratio_bound

/--
Theorem 3.2 evaluates the Graham factor as seven fifths.
Source status: direct source formula
-/
abbrev theorem3_2_graham_factor_eq_seven_fifths :=
  @LMMS04FairDivision.ProofInterface.theorem3_2_graham_factor_eq_seven_fifths

/--
Theorem 3.3 conditional fixed-dimension IP summary.
Source status: partial boundary
Source note: The fixed-dimension IP runtime theorem is a reusable library dependency, not yet derived in Lean.
-/
abbrev theorem3_3_solver_auto_cap_full_ip_summary_with_ratio_guarantee :=
  @LMMS04FairDivision.ProofInterface.theorem3_3_solver_auto_cap_full_ip_summary_with_ratio_guarantee

/--
Theorem 3.3 compact external-solver package.
Source status: partial boundary
Source note: Lean supplies the selected-pair/full-IP source-output payload; the
runtime/FPTAS conclusion is exactly the supplied external solver consequence.
-/
abbrev theorem3_3_external_solver_selected_pair_full_summary_source_output_package :=
  @LMMS04FairDivision.ProofInterface.theorem3_3_external_solver_selected_pair_full_summary_source_output_package

/--
Theorem 3.3 compact external-solver payload projection.
Source status: partial boundary
Source note: This projects the verified selected-pair/full-IP source-output
payload from the conditional external-solver package.
-/
abbrev theorem3_3_external_solver_selected_pair_full_summary_source_output_payload :=
  @LMMS04FairDivision.ProofInterface.theorem3_3_external_solver_selected_pair_full_summary_source_output_payload

/--
Theorem 3.3 compact external-solver consequence projection.
Source status: partial boundary
Source note: This projection records that the final runtime/FPTAS conclusion is
the external solver consequence, pending the reusable fixed-dimension IP theorem.
-/
abbrev theorem3_3_external_solver_selected_pair_full_summary_source_output_consequence :=
  @LMMS04FairDivision.ProofInterface.theorem3_3_external_solver_selected_pair_full_summary_source_output_consequence

/--
Theorem 3.3 strongest Claim-3.4 additive external-solver endpoint.
Source status: partial boundary
Source note: Under the source-average Claim 3.4 hypotheses and additive
selected-pair estimates, this returns the compact external-solver package.
-/
abbrev theorem3_3_external_solver_consequence_and_selected_pair_full_summary_source_output_of_claim_3_4_source_average_forward_additive_no_top_of_margin :=
  @LMMS04FairDivision.ProofInterface.theorem3_3_external_solver_consequence_and_selected_pair_full_summary_source_output_of_claim_3_4_source_average_forward_additive_no_top_of_margin

/--
Claim 3.4 fixed-rounding ratio endpoint.
Source status: partial boundary
Source note: Section 3 rounded-search helpers still expose selected-certificate premises.
-/
abbrev theorem3_3_claim34_fixed_rounding_ratio_endpoint :=
  @LMMS04FairDivision.ProofInterface.theorem3_3_claim34_fixed_rounding_ratio_endpoint

/--
Claim 3.4 capped weighted-supply endpoint.
Source status: partial boundary
Source note: Section 3 rounded-search helpers still expose selected-certificate premises.
-/
abbrev theorem3_3_claim34_capped_weighted_supply_ratio_endpoint :=
  @LMMS04FairDivision.ProofInterface.theorem3_3_claim34_capped_weighted_supply_ratio_endpoint

/-- Claim 3.4 exact-allocation bounded optimum endpoint. -/
abbrev claim3_4_bounded_optimal_of_exact_allocations_with_nonempty_positive_goods :=
  @LMMS04FairDivision.ProofInterface.claim3_4_bounded_optimal_of_exact_allocations_with_nonempty_positive_goods

/-- Claim 3.4 identical-utilities bounded optimum endpoint. -/
abbrev claim3_4_bounded_optimal_of_identical_utilities_model :=
  @LMMS04FairDivision.ProofInterface.claim3_4_bounded_optimal_of_identical_utilities_model

/--
Claim 3.4 identical-utilities bounded optimum bound.
Source status: partial boundary
Source note: This is the exact Claim 3.4 identical-utilities bound, but the
Section 3 rounded-search runtime layer remains a partial boundary.
-/
abbrev claim3_4_identical_utilities_bounded_optimum_bound :=
  @LMMS04FairDivision.ProofInterface.claim3_4_bounded_optimal_of_identical_utilities_model

/--
Theorem 3.3 additive-load ratio transfer.
Source status: direct source proof step
-/
abbrev theorem3_3_ratio_transfer_certificate_epsilon_of_agentwise_additive_loads :=
  @LMMS04FairDivision.ProofInterface.theorem3_3_ratio_transfer_certificate_epsilon_of_agentwise_additive_loads

/-- Lemma 3.5 additive transfer endpoint. -/
abbrev lemma3_5_additive_transfer_certificate_epsilon_of_opt_loads :=
  @LMMS04FairDivision.ProofInterface.lemma3_5_additive_transfer_certificate_epsilon_of_opt_loads

/--
Lemma 3.5 additive transfer epsilon bound.
Source status: partial boundary
Source note: This exposes the Lemma 3.5 additive-transfer inequality; the
certificate/load-window premises are recorded in the paper assumption ledger.
-/
abbrev lemma3_5_additive_transfer_epsilon_bound :=
  @LMMS04FairDivision.ProofInterface.lemma3_5_additive_transfer_certificate_epsilon_of_opt_loads

/-! ## Section 4: Truthfulness and Random Allocation -/

/-- Direct fair-division mechanism without transfers. -/
abbrev directMechanism (Agent Item : Type*) :=
  LMMS04FairDivision.paper_direct_mechanism Agent Item

/--
A direct no-transfer mechanism consists only of an allocation rule.
Source status: direct paper definition
-/
theorem directMechanism_fields
    (Agent Item : Type*) (M : directMechanism Agent Item) :
    M = { allocation := M.allocation } := by
  cases M
  rfl

/-- Randomized direct fair-division mechanism without transfers. -/
abbrev randomizedDirectMechanism (Agent Item : Type*) :=
  LMMS04FairDivision.paper_randomized_direct_mechanism Agent Item

/--
A randomized direct no-transfer mechanism consists only of an allocation law.
Source status: direct paper definition
-/
theorem randomizedDirectMechanism_fields
    (Agent Item : Type*) (M : randomizedDirectMechanism Agent Item) :
    M = { allocationLaw := M.allocationLaw } := by
  cases M
  rfl

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
abbrev theorem4_1_source_goods :=
  @LMMS04FairDivision.ProofInterface.theorem4_1_source_goods

/--
Theorem 4.1 uses the full finite source universe: two named goods plus eight
egg goods, for ten goods total and two agents.
-/
theorem theorem4_1_source_goods_content :
    theorem4_1_source_goods = Finset.univ ∧
      Fintype.card Theorem41.LMMS41Agent = 2 ∧
        theorem4_1_source_goods.card = 10 ∧
          Theorem41.lmms41EggItems.card = 8 := by
  exact ⟨rfl, by decide, by decide, Theorem41.lmms41EggItems_card⟩

/-- The truthful source report used for Theorem 4.1. -/
abbrev theorem4_1_true_report :=
  @LMMS04FairDivision.ProofInterface.theorem4_1_true_report

/--
Theorem 4.1's truthful report is the additive bundle valuation generated by
the displayed two-player item weights.
Source status: direct source formula
-/
theorem theorem4_1_true_report_formula :
    theorem4_1_true_report =
      Theorem41.lmms41AdditiveReport Theorem41.lmms41TrueWeight ∧
      ∀ agent item,
        Theorem41.lmms41TrueWeight agent item =
          if agent = Theorem41.LMMS41Agent.player1 then
            if item = Theorem41.LMMS41Item.a then (9 : ℝ) / 20
            else if item = Theorem41.LMMS41Item.b then (7 : ℝ) / 20
            else (1 : ℝ) / 40
          else
            if item = Theorem41.LMMS41Item.a then (7 : ℝ) / 20
            else if item = Theorem41.LMMS41Item.b then (9 : ℝ) / 20
            else (1 : ℝ) / 40 := by
  exact ⟨rfl, by intro agent item; rfl⟩

/-- Theorem 4.1 envy-free mechanism impossibility. -/
abbrev theorem4_1_source_not_truthful_envy_free_whenever_exists :=
  @LMMS04FairDivision.ProofInterface.theorem4_1_source_not_truthful_envy_free_whenever_exists

/-- Theorem 4.1 minimum-envy mechanism impossibility. -/
abbrev theorem4_1_source_minimum_envy_not_truthful :=
  @LMMS04FairDivision.ProofInterface.theorem4_1_source_minimum_envy_not_truthful

/-- Theorem 4.2 uniform-random mechanism truthfulness. -/
abbrev theorem4_2_uniform_random_mechanism_truthful :=
  @LMMS04FairDivision.ProofInterface.theorem4_2_uniform_random_mechanism_truthful

/--
Theorem 4.2 uniform-random maximum-envy probability bound.
Source status: direct source formula
-/
abbrev theorem4_2_uniform_random_max_envy_probability_bound :=
  @LMMS04FairDivision.ProofInterface.theorem4_2_uniform_random_max_envy_probability_bound

/- Elaborator support for Specs of polymorphic theorem aliases.

The target is the alias's exact proposition type, obtained from Lean's
environment rather than reconstructed from a lossy pretty-printed expression.
-/
open Lean Elab Term Meta

syntax "v11PropositionTypeOf " ident : term

elab_rules : term
  | `(v11PropositionTypeOf $identifier:ident) => do
    let name ← resolveGlobalConstNoOverload identifier
    let info ← getConstInfo name
    let proposition := info.type
    let sort ← inferType proposition
    unless sort.isProp do
      throwError "v11PropositionTypeOf expects a proposition-valued declaration"
    return proposition

/-- Transparent v11 semantic target for the source definition `envy`. -/
def envySpec (v : Valuation Agent Item) (A : Allocation Agent Item)
    (i j : Agent) : Prop :=
  envy v A i j = (max 0 (v.value i (A j) - v.value i (A i)))

/-- Transparent v11 semantic target for the source definition `envyFree`. -/
def envyFreeSpec (v : Valuation Agent Item) (A : Allocation Agent Item) : Prop :=
  envyFree v A = (∀ i j, v.value i (A j) ≤ v.value i (A i))

/-- Transparent v11 semantic target for the source definition `envyBoundedBy`. -/
def envyBoundedBySpec (v : Valuation Agent Item) (A : Allocation Agent Item)
    (alpha : ℝ) : Prop :=
  envyBoundedBy v A alpha = (∀ i j, envy v A i j ≤ alpha)

/-- Transparent v11 semantic target for the source definition `maxMarginal`. -/
def maxMarginalSpec (v : Valuation Agent Item) : Prop :=
  maxMarginal v = (LMMS04FairDivision.paper_max_marginal v)

/-- Transparent v11 semantic target for the source definition `isAllocationOf`. -/
def isAllocationOfSpec (A : Allocation Agent Item) (goods : Finset Item) : Prop :=
  isAllocationOf A goods = (IsAllocationOf A goods)

/-- Transparent v11 semantic target for the source abbreviation `lemma2_2_acyclic_reduction`. -/
def lemma2_2_acyclic_reductionSpec : Prop :=
  v11PropositionTypeOf lemma2_2_acyclic_reduction

/-- Transparent v11 semantic target for the source abbreviation `theorem2_1_bounded_envy_allocation_exists`. -/
def theorem2_1_bounded_envy_allocation_existsSpec : Prop :=
  v11PropositionTypeOf theorem2_1_bounded_envy_allocation_exists

/-- Transparent v11 semantic target for the source abbreviation `theorem2_1_alpha_bounded_allocation_exists`. -/
def theorem2_1_alpha_bounded_allocation_existsSpec : Prop :=
  v11PropositionTypeOf theorem2_1_alpha_bounded_allocation_exists

/-- Transparent v11 semantic target for the source abbreviation `theorem2_1_algorithm_correct_list_toFinset`. -/
def theorem2_1_algorithm_correct_list_toFinsetSpec : Prop :=
  v11PropositionTypeOf theorem2_1_algorithm_correct_list_toFinset

/-- Transparent v11 semantic target for the source abbreviation `theorem2_3_real_interval_supported_atom_bound`. -/
def theorem2_3_real_interval_supported_atom_boundSpec : Prop :=
  v11PropositionTypeOf theorem2_3_real_interval_supported_atom_bound

/-- Transparent v11 semantic target for the source abbreviation `theorem3_1_eventually_minimum_envy_lower_bound_from_twoBit_adaptive_queries`. -/
def theorem3_1_eventually_minimum_envy_lower_bound_from_twoBit_adaptive_queriesSpec : Prop :=
  v11PropositionTypeOf theorem3_1_eventually_minimum_envy_lower_bound_from_twoBit_adaptive_queries

/-- Transparent v11 semantic target for the source abbreviation `theorem3_1_eventually_minimum_envy_ratio_lower_bound_from_twoBit_adaptive_queries`. -/
def theorem3_1_eventually_minimum_envy_ratio_lower_bound_from_twoBit_adaptive_queriesSpec : Prop :=
  v11PropositionTypeOf theorem3_1_eventually_minimum_envy_ratio_lower_bound_from_twoBit_adaptive_queries

/-- Transparent v11 semantic target for the source abbreviation `theorem3_2_graham_certificate_to_envy_ratio_bound`. -/
def theorem3_2_graham_certificate_to_envy_ratio_boundSpec : Prop :=
  v11PropositionTypeOf theorem3_2_graham_certificate_to_envy_ratio_bound

/-- Transparent v11 semantic target for the source abbreviation `theorem3_2_graham_factor_eq_seven_fifths`. -/
def theorem3_2_graham_factor_eq_seven_fifthsSpec : Prop :=
  v11PropositionTypeOf theorem3_2_graham_factor_eq_seven_fifths

/-- Transparent v11 semantic target for the source abbreviation `theorem3_3_solver_auto_cap_full_ip_summary_with_ratio_guarantee`. -/
def theorem3_3_solver_auto_cap_full_ip_summary_with_ratio_guaranteeSpec : Prop :=
  v11PropositionTypeOf theorem3_3_solver_auto_cap_full_ip_summary_with_ratio_guarantee

/-- Transparent v11 semantic target for the source abbreviation `theorem3_3_claim34_fixed_rounding_ratio_endpoint`. -/
def theorem3_3_claim34_fixed_rounding_ratio_endpointSpec : Prop :=
  v11PropositionTypeOf theorem3_3_claim34_fixed_rounding_ratio_endpoint

/-- Transparent v11 semantic target for the source abbreviation `theorem3_3_claim34_capped_weighted_supply_ratio_endpoint`. -/
def theorem3_3_claim34_capped_weighted_supply_ratio_endpointSpec : Prop :=
  v11PropositionTypeOf theorem3_3_claim34_capped_weighted_supply_ratio_endpoint

/-- Transparent v11 semantic target for the source abbreviation `claim3_4_bounded_optimal_of_exact_allocations_with_nonempty_positive_goods`. -/
def claim3_4_bounded_optimal_of_exact_allocations_with_nonempty_positive_goodsSpec : Prop :=
  v11PropositionTypeOf claim3_4_bounded_optimal_of_exact_allocations_with_nonempty_positive_goods

/-- Transparent v11 semantic target for the source abbreviation `claim3_4_identical_utilities_bounded_optimum_bound`. -/
def claim3_4_identical_utilities_bounded_optimum_boundSpec : Prop :=
  v11PropositionTypeOf claim3_4_identical_utilities_bounded_optimum_bound

/-- Transparent v11 semantic target for the source abbreviation `theorem3_3_ratio_transfer_certificate_epsilon_of_agentwise_additive_loads`. -/
def theorem3_3_ratio_transfer_certificate_epsilon_of_agentwise_additive_loadsSpec : Prop :=
  v11PropositionTypeOf theorem3_3_ratio_transfer_certificate_epsilon_of_agentwise_additive_loads

/-- Transparent v11 semantic target for the source abbreviation `lemma3_5_additive_transfer_epsilon_bound`. -/
def lemma3_5_additive_transfer_epsilon_boundSpec : Prop :=
  v11PropositionTypeOf lemma3_5_additive_transfer_epsilon_bound

/-- Transparent v11 semantic target for `directMechanism_fields`. -/
def directMechanism_fieldsSpec
    (Agent Item : Type*) (M : directMechanism Agent Item) : Prop :=
  M = { allocation := M.allocation }

/-- Transparent v11 semantic target for `randomizedDirectMechanism_fields`. -/
def randomizedDirectMechanism_fieldsSpec
    (Agent Item : Type*) (M : randomizedDirectMechanism Agent Item) : Prop :=
  M = { allocationLaw := M.allocationLaw }

/-- Transparent v11 semantic target for the source definition `truthful`. -/
def truthfulSpec [DecidableEq Agent] (M : directMechanism Agent Item) : Prop :=
  truthful M = (LMMS04FairDivision.paper_fair_division_truthful M)

/-- Transparent v11 semantic target for the source definition `randomizedTruthful`. -/
def randomizedTruthfulSpec
    [Fintype (Allocation Agent Item)] [DecidableEq (Allocation Agent Item)]
    [DecidableEq Agent]
    (M : randomizedDirectMechanism Agent Item) : Prop :=
  randomizedTruthful M = (LMMS04FairDivision.paper_randomized_fair_division_truthful M)

/-- Transparent v11 semantic target for `theorem4_1_source_goods_content`. -/
def theorem4_1_source_goods_contentSpec : Prop :=
  theorem4_1_source_goods = Finset.univ ∧
    Fintype.card Theorem41.LMMS41Agent = 2 ∧
      theorem4_1_source_goods.card = 10 ∧
        Theorem41.lmms41EggItems.card = 8

/-- Transparent v11 semantic target for `theorem4_1_true_report_formula`. -/
def theorem4_1_true_report_formulaSpec : Prop :=
  theorem4_1_true_report =
    Theorem41.lmms41AdditiveReport Theorem41.lmms41TrueWeight ∧
    ∀ agent item,
      Theorem41.lmms41TrueWeight agent item =
        if agent = Theorem41.LMMS41Agent.player1 then
          if item = Theorem41.LMMS41Item.a then (9 : ℝ) / 20
          else if item = Theorem41.LMMS41Item.b then (7 : ℝ) / 20
          else (1 : ℝ) / 40
        else
          if item = Theorem41.LMMS41Item.a then (7 : ℝ) / 20
          else if item = Theorem41.LMMS41Item.b then (9 : ℝ) / 20
          else (1 : ℝ) / 40

/-- Transparent v11 semantic target for the source abbreviation `theorem4_1_source_not_truthful_envy_free_whenever_exists`. -/
def theorem4_1_source_not_truthful_envy_free_whenever_existsSpec : Prop :=
  v11PropositionTypeOf theorem4_1_source_not_truthful_envy_free_whenever_exists

/-- Transparent v11 semantic target for the source abbreviation `theorem4_1_source_minimum_envy_not_truthful`. -/
def theorem4_1_source_minimum_envy_not_truthfulSpec : Prop :=
  v11PropositionTypeOf theorem4_1_source_minimum_envy_not_truthful

/-- Transparent v11 semantic target for the source abbreviation `theorem4_2_uniform_random_mechanism_truthful`. -/
def theorem4_2_uniform_random_mechanism_truthfulSpec : Prop :=
  v11PropositionTypeOf theorem4_2_uniform_random_mechanism_truthful

/-- Transparent v11 semantic target for the source abbreviation `theorem4_2_uniform_random_max_envy_probability_bound`. -/
def theorem4_2_uniform_random_max_envy_probability_boundSpec : Prop :=
  v11PropositionTypeOf theorem4_2_uniform_random_max_envy_probability_bound

/-- Lean-checked proof endpoint for the Lemma 2.2 source contract. -/
theorem lemma2_2_acyclic_reductionSpec_proof :
    lemma2_2_acyclic_reductionSpec := by
  exact lemma2_2_acyclic_reduction

/-- Lean-checked proof endpoint for the Theorem 2.1 existence source contract. -/
theorem theorem2_1_bounded_envy_allocation_existsSpec_proof :
    theorem2_1_bounded_envy_allocation_existsSpec := by
  exact theorem2_1_bounded_envy_allocation_exists

/-- Lean-checked proof endpoint for the Theorem 2.3 source contract. -/
theorem theorem2_3_real_interval_supported_atom_boundSpec_proof :
    theorem2_3_real_interval_supported_atom_boundSpec := by
  exact theorem2_3_real_interval_supported_atom_bound

/-- Lean-checked proof endpoint for Theorem 4.1's envy-free clause. -/
theorem theorem4_1_source_not_truthful_envy_free_whenever_existsSpec_proof :
    theorem4_1_source_not_truthful_envy_free_whenever_existsSpec := by
  exact theorem4_1_source_not_truthful_envy_free_whenever_exists

/-- Lean-checked proof endpoint for Theorem 4.1's minimum-envy clause. -/
theorem theorem4_1_source_minimum_envy_not_truthfulSpec_proof :
    theorem4_1_source_minimum_envy_not_truthfulSpec := by
  exact theorem4_1_source_minimum_envy_not_truthful

/-- Lean-checked proof endpoint for Theorem 4.2's uniform-truthfulness atom. -/
theorem theorem4_2_uniform_random_mechanism_truthfulSpec_proof :
    theorem4_2_uniform_random_mechanism_truthfulSpec := by
  exact theorem4_2_uniform_random_mechanism_truthful

end

end PaperInterface
end LMMS04FairDivision

import MSVV07AdWords.AlgorithmCost
import MSVV07AdWords.SourceRunner
import MSVV07AdWords.AppendixCounterexample

/-!
# Human-Facing Paper Interface: MSVV07 AdWords

This compact module is the configured row-level review surface.
Implementation lemmas remain in `AuditInterface.lean`, but each audited
paper-facing declaration is written directly here for dashboard and human review.
-/

open scoped BigOperators

namespace AppliedModelingLib
namespace Online
namespace MSVV07PaperFacing
namespace PaperInterface

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {Advertiser Query Time Regime : Type*}

/--
- Paper multiple-slot distinctness spelled out by original query and slot.
Source status: direct paper model extension
-/
theorem paperSlotsPerPageDistinct_iff
    {Advertiser Query : Type*} (Slot : Query → Type*)
    (A : PaperAssignment Advertiser (Σ q : Query, Slot q)) :
    paperSlotsPerPageDistinct Slot A ↔
      ∀ q s₁ s₂ a,
        A ⟨q, s₁⟩ = some a →
        A ⟨q, s₂⟩ = some a →
        s₁ = s₂ := by
  rfl

/--
- Paper spend formula for advertiser `a` under assignment `A`.
Source status: direct paper formula
-/
theorem paperSpend_formula
    {Advertiser Query : Type*} [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) (a : Advertiser) :
    paperSpend I A a =
      ∑ q : Query,
        match A q with
        | none => 0
        | some a' => if a' = a then I.bid a q else 0 := by
  rfl

/--
- Paper revenue formula for an assignment.
Source status: direct paper formula
-/
theorem paperRevenue_formula
    {Advertiser Query : Type*} [Fintype Query]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) :
    paperRevenue I A =
      ∑ q : Query,
        match A q with
        | none => 0
        | some a => I.bid a q := by
  rfl

/--
- Paper budget feasibility: no advertiser spends more than her budget.
Source status: direct paper constraint
-/
theorem paperFeasible_iff
    {Advertiser Query : Type*} [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) :
    paperFeasible I A ↔ ∀ a, paperSpend I A a ≤ I.budget a := by
  rfl

/--
Section 2's chronological allocation model: every arrival has an assignee and
the resulting occurrence-level spend respects every daily budget.  This is the
literal source model; it is deliberately separate from the identifier-indexed
library feasibility predicate.
Source status: direct paper definition
-/
theorem section2_occurrence_assignment_feasibility_definition
    {Advertiser Query : Type*} [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query) (history : List Query)
    (A : Fin history.length → Option Advertiser) :
    SourceRunner.occurrenceAssignmentFeasible I history A ↔
      (∀ t, ∃ a, A t = some a) ∧
        ∀ a, SourceRunner.occurrenceSpend I history A a ≤ I.budget a := by
  rfl

/--
- Paper small-bids condition: every bid is at most an `epsilon` budget fraction.
Source status: direct paper assumption
-/
theorem paperSmallBids_iff
    {Advertiser Query : Type*}
    (I : PaperInstance Advertiser Query) (epsilon : ℝ) :
    paperSmallBids I epsilon ↔ ∀ a q, I.bid a q ≤ epsilon * I.budget a := by
  rfl

/--
- Paper fractional LP value.
Source status: direct paper formula
-/
theorem paperFractionalRevenue_formula
    {Advertiser Query : Type*} [Fintype Advertiser] [Fintype Query]
    (I : PaperInstance Advertiser Query)
    (x : Advertiser → Query → ℝ) :
    paperFractionalRevenue I x =
      ∑ q : Query, ∑ a : Advertiser, I.bid a q * x a q := by
  rfl

/--
- Paper fractional LP feasibility constraints.
Source status: direct paper constraints
-/
theorem paperFractionalFeasible_iff
    {Advertiser Query : Type*} [Fintype Advertiser] [Fintype Query]
    (I : PaperInstance Advertiser Query)
    (x : Advertiser → Query → ℝ) :
    PaperFractionalFeasible I x ↔
      (∀ a q, 0 ≤ x a q) ∧
        (∀ q, (∑ a : Advertiser, x a q) ≤ 1) ∧
          ∀ a, (∑ q : Query, I.bid a q * x a q) ≤ I.budget a := by
  constructor
  · intro h
    exact ⟨h.nonneg, h.query, h.budget⟩
  · rintro ⟨hnonneg, hquery, hbudget⟩
    exact ⟨hnonneg, hquery, hbudget⟩

/--
- The paper's MSVV/Balance tradeoff function at spent fraction `s`.
Source status: direct paper formula
-/
theorem paperTradeoff_formula (s : ℝ) :
    paperTradeoff s = 1 - Real.exp (s - 1) := by
  rfl

/-- The source's finite-`k` Section 3 tradeoff weight for one-indexed slab `i+1`. -/
noncomputable def paperDiscreteTradeoff (k : ℕ) (i : Fin k) : ℝ :=
  SourceRunner.discreteTradeoff k i

/--
Section 3's displayed discretized tradeoff formula
`psi_k(i) = 1 - exp(-(1 - i/k))`, with Lean index `i` representing source slab
`i+1`. This row checks the finite formula; the discrete runner and convergence
bridge to the continuous rule remain separate source obligations.
Source status: direct paper formula
-/
theorem section3_discrete_tradeoff_formula (k : ℕ) (i : Fin k) :
    paperDiscreteTradeoff k i =
      1 - Real.exp
        (-(1 - (((i.val + 1 : ℕ) : ℝ) / (k : ℝ)))) := by
  rfl

/--
- The paper's competitive ratio `1 - 1/e`.
Source status: direct paper formula
-/
theorem paperMsvvRatio_formula :
    paperMsvvRatio = 1 - 1 / Real.exp 1 := by
  rfl

/--
- Paper Balance/MSVV scaled bid.
Source status: direct paper formula
-/
theorem paperBalanceScore_formula
    {Advertiser Query : Type*} [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) (a : Advertiser) (q : Query) :
    paperBalanceScore I A a q =
      I.bid a q * paperTradeoff (paperSpend I A a / I.budget a) := by
  rfl

/--
Section 3's finite Balance score at one arriving occurrence: the bid times
`psi_k` of the bidder's active slab.
Source status: direct paper formula
-/
theorem section3_discrete_balance_score_formula
    {Advertiser Query : Type*}
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (S : SourceRunner.OccurrenceState Advertiser Query)
    (q : Query) (a : Advertiser) :
    SourceRunner.occurrenceDiscreteScore k hk I S q a =
      I.bid a q * paperDiscreteTradeoff k
        (SourceRunner.activeBudgetSlab k hk (S.spent a) (I.budget a)) := by
  rfl

/--
Section 3's discrete allocation rule: a scan winner is feasible and maximizes
the finite `psi_k`-scaled bid over all feasible advertisers.
Source status: direct paper algorithm rule
-/
theorem section3_discrete_balance_choice_rule
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (S : SourceRunner.OccurrenceState Advertiser Query)
    (q : Query) (a : Advertiser)
    (hchoice : (SourceRunner.discreteBalanceScan k hk I S q).winner = some a) :
    SourceRunner.occurrenceDiscreteBalanceChoice k hk I S q a := by
  exact SourceRunner.discreteBalanceScan_winner_is_discrete_choice
    k hk I S q a hchoice

/--
- Paper feasibility for assigning query `q` next to advertiser `a`.
Source status: direct paper budget constraint
-/
theorem paperCanAssign_iff
    {Advertiser Query : Type*} [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) (q : Query) (a : Advertiser) :
    paperCanAssign I A q a ↔
      paperSpend I A a + I.bid a q ≤ I.budget a := by
  rfl

/--
-
Paper Balance/MSVV choice rule: advertiser `a` is feasible for query `q` and
maximizes the scaled bid among feasible advertisers.
Source status: direct paper algorithm rule
-/
theorem paperIsBalanceChoice_iff
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) (q : Query) (a : Advertiser) :
    paperIsBalanceChoice I A q a ↔
      paperCanAssign I A q a ∧
        ∀ b, paperCanAssign I A q b →
          paperBalanceScore I A b q ≤ paperBalanceScore I A a q := by
  rfl

/--
The source calls Balance simple and time efficient. This support theorem pairs
noncomputable maximizer existence with the candidate/comparison counts targeted
by a direct finite scan in a unit-cost exact-real oracle model. The ledger is
not derived from a cost-threaded runner, so this is not a complete
algorithm-efficiency bridge.
Source status: partial support for the qualitative efficiency claim
-/
theorem section3_balance_choice_exists_with_finite_max_cost
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) (q : Query)
    (h : ∃ a, paperCanAssign I A q a) :
    ∃ a, paperIsBalanceChoice I A q a ∧
      (balanceFiniteMaxCost Advertiser).candidateTests =
        Fintype.card Advertiser ∧
      (balanceFiniteMaxCost Advertiser).scoreComparisonUpperBound ≤
        Fintype.card Advertiser := by
  exact
    MSVV07PaperFacing.section3_balance_choice_exists_with_finite_max_cost
      I A q h

/-! ## Section 4: displayed factor-revealing LP and witnesses -/

/--
The paper's displayed factor-revealing primal/dual programs in the finite
`m = k-1` indexing. This row exposes both objectives and both feasible sets,
rather than relying only on a later LP-row lemma.
Source status: direct paper LP formulas
-/
theorem section4_factor_revealing_primal_dual_lp_formulas
    {m : ℕ} (N : ℝ) (x y : Fin m → ℝ) :
    (MSVV07SourceLemmas.factorRevealingLP m N).primalObjective x =
        MSVV07SourceLemmas.paperRoutePrimalObjective x ∧
      ((MSVV07SourceLemmas.factorRevealingLP m N).PrimalFeasible x ↔
        MSVV07SourceLemmas.paperRoutePrimalFeasible N x) ∧
      (MSVV07SourceLemmas.factorRevealingLP m N).dualObjective y =
        MSVV07SourceLemmas.paperRouteDualObjective N y ∧
      ((MSVV07SourceLemmas.factorRevealingLP m N).DualFeasible y ↔
        MSVV07SourceLemmas.paperRouteDualFeasible y) := by
  exact ⟨
    MSVV07SourceLemmas.factorRevealingLP_primalObjective_eq N x,
    MSVV07SourceLemmas.factorRevealingLP_primalFeasible_iff N x,
    MSVV07SourceLemmas.factorRevealingLP_dualObjective_eq N y,
    MSVV07SourceLemmas.factorRevealingLP_dualFeasible_iff N y⟩

/--
Section 4 Lemma 3's displayed geometric witnesses are feasible and attain the
same finite value; the primal witness is a maximizer and the dual witness is a
minimizer. The separate Lemma 3 row checks the limiting value as `k` grows.
Source status: direct paper Lemma 3 witness/optimality claim
-/
theorem section4_lemma3_displayed_primal_dual_witnesses_optimal
    {m N : ℕ} :
    Optimization.IsMaximizerOn
        (MSVV07SourceLemmas.paperRoutePrimalFeasible (m := m) (N : ℝ))
        (MSVV07SourceLemmas.paperRoutePrimalObjective (m := m))
        (MSVV07SourceLemmas.paperRoutePrimalCandidate (m := m) (N : ℝ)) ∧
      Optimization.IsMinimizerOn
        (MSVV07SourceLemmas.factorRevealingLP m (N : ℝ)).DualFeasible
        (MSVV07SourceLemmas.factorRevealingLP m (N : ℝ)).dualObjective
        (MSVV07SourceLemmas.paperRouteDualCandidate (m := m)) ∧
      MSVV07SourceLemmas.paperRoutePrimalObjective
          (MSVV07SourceLemmas.paperRoutePrimalCandidate (m := m) (N : ℝ)) =
        MSVV07SourceLemmas.factorRevealingLPValue m (N : ℝ) ∧
      MSVV07SourceLemmas.paperRouteDualObjective (N : ℝ)
          (MSVV07SourceLemmas.paperRouteDualCandidate (m := m)) =
        MSVV07SourceLemmas.factorRevealingLPValue m (N : ℝ) := by
  have hN_real : 0 ≤ (N : ℝ) := by positivity
  have hprimal :=
    MSVV07SourceLemmas.lemma3_factor_revealing_lp_primal_candidate_is_maximizer
      (m := m) hN_real
  have hp :
      (MSVV07SourceLemmas.factorRevealingLP m (N : ℝ)).PrimalFeasible
        (MSVV07SourceLemmas.paperRoutePrimalCandidate (m := m) (N : ℝ)) :=
    (MSVV07SourceLemmas.factorRevealingLP_primalFeasible_iff (N : ℝ) _).2
      (MSVV07SourceLemmas.paperRoutePrimalCandidate_feasible hN_real)
  have hd :
      (MSVV07SourceLemmas.factorRevealingLP m (N : ℝ)).DualFeasible
        (MSVV07SourceLemmas.paperRouteDualCandidate (m := m)) :=
    (MSVV07SourceLemmas.factorRevealingLP_dualFeasible_iff (N : ℝ) _).2
      MSVV07SourceLemmas.paperRouteDualCandidate_feasible
  have hv :
      (MSVV07SourceLemmas.factorRevealingLP m (N : ℝ)).primalObjective
          (MSVV07SourceLemmas.paperRoutePrimalCandidate (m := m) (N : ℝ)) =
        (MSVV07SourceLemmas.factorRevealingLP m (N : ℝ)).dualObjective
          (MSVV07SourceLemmas.paperRouteDualCandidate (m := m)) := by
    rw [MSVV07SourceLemmas.factorRevealingLP_primalObjective_eq]
    rw [MSVV07SourceLemmas.factorRevealingLP_dualObjective_eq]
    rw [MSVV07SourceLemmas.paperRoutePrimalCandidate_objective_value]
    rw [MSVV07SourceLemmas.paperRouteDualCandidate_objective_value]
  have hdual :=
    MSVV07SourceLemmas.lemma4_standardMaxLP_dual_yStar_optimal
      (MSVV07SourceLemmas.factorRevealingLP m (N : ℝ)) hp hd hv
  exact ⟨hprimal, hdual,
    MSVV07SourceLemmas.paperRoutePrimalCandidate_objective_value (N : ℝ),
    MSVV07SourceLemmas.paperRouteDualCandidate_objective_value (N : ℝ)⟩

/--
- Section 4 Lemma 1: equal bids imply Balance pays no later than the OPT type.
-/
theorem section4_lemma1_balance_pays_no_later_slab
    {Slab : Type*} [LinearOrder Slab]
    (psi : Slab → ℝ) {optType optCurrentSlab chosenSlab : Slab}
    {bid chosenBid : ℝ}
    (hoptCurrent_le_type : optCurrentSlab ≤ optType)
    (hchoice :
      bid * psi optCurrentSlab ≤ chosenBid * psi chosenSlab)
    (hequal_bids : chosenBid = bid)
    (hbid_pos : 0 < bid)
    (hpsi_strictAnti : StrictAnti psi) :
    chosenSlab ≤ optType := by
  exact
    Proof.proof_section4_lemma1_balance_pays_no_later_slab
      psi hoptCurrent_le_type hchoice hequal_bids hbid_pos hpsi_strictAnti

/--
- Section 4 Lemma 2: Lemma 1's prefix accounting yields the LP row constraint.
-/
theorem section4_lemma2_factor_revealing_lp_constraint
    {m : ℕ} (N : ℝ) (x beta : Fin m → ℝ) (i : Fin m)
    (hprefix_cover :
      (∑ j ∈ MSVV07SourceLemmas.paperRoutePrefix i, x j) ≤
        ∑ j ∈ MSVV07SourceLemmas.paperRoutePrefix i, beta j)
    (hbeta_prefix :
      (∑ j ∈ MSVV07SourceLemmas.paperRoutePrefix i, beta j) =
        MSVV07SourceLemmas.paperRouteRhs N i -
          ∑ j ∈ MSVV07SourceLemmas.paperRoutePrefix i,
            MSVV07SourceLemmas.paperRouteDeltaCoeff i j * x j) :
    MSVV07SourceLemmas.paperRouteLPRow x i ≤
      MSVV07SourceLemmas.paperRouteRhs N i := by
  exact
    Proof.proof_section4_lemma2_factor_revealing_lp_constraint
      N x beta i hprefix_cover hbeta_prefix

/--
- Section 4 Lemma 3: the displayed factor-revealing LP value tends to `N / e`.
-/
theorem section4_lemma3_factor_revealing_lp_optimality (N : ℝ) :
    Sequence.SeqTendsTo
      (fun k : ℕ => N * (1 - 1 / (k : ℝ)) ^ k)
      (N / Real.exp 1) := by
  exact Proof.section4_lemma3_factor_revealing_lp_value_tends N

/-! ## Section 5: tradeoff-revealing LP formulas -/

/--
The Section 5 LP family `L(pi, psi)` keeps the factor-LP matrix/objective and
replaces the right-hand side by `l`; its dual keeps the same feasible region and
uses `l` in the objective. This row exposes the complete finite primal/dual
formulas.
Source status: direct paper LP-family formulas
-/
theorem section5_tradeoff_revealing_primal_dual_lp_formulas
    {m : ℕ} (c l x y : Fin m → ℝ) :
    (MSVV07SourceLemmas.tradeoffRevealingLP c l).primalObjective x =
        ∑ i : Fin m, c i * x i ∧
      ((MSVV07SourceLemmas.tradeoffRevealingLP c l).PrimalFeasible x ↔
        (∀ i, 0 ≤ x i) ∧
          ∀ r, (∑ i : Fin m,
            MSVV07SourceLemmas.paperRouteMatrixCoeff r i * x i) ≤ l r) ∧
      (MSVV07SourceLemmas.tradeoffRevealingLP c l).dualObjective y =
        ∑ r : Fin m, y r * l r ∧
      ((MSVV07SourceLemmas.tradeoffRevealingLP c l).DualFeasible y ↔
        (∀ r, 0 ≤ y r) ∧
          ∀ i, c i ≤ ∑ r : Fin m,
            MSVV07SourceLemmas.paperRouteMatrixCoeff r i * y r) := by
  exact ⟨rfl, Iff.rfl, rfl, Iff.rfl⟩

/--
Theorem 8's finite tradeoff weights are the suffix sums of the displayed dual
witness and equal the paper's closed geometric form.
Source status: direct paper Theorem 8 formula
-/
theorem theorem8_dual_induced_tradeoff_formula
    {m : ℕ} (i : Fin m) :
    MSVV07SourceLemmas.paperRoutePsiCandidate i =
      1 - (1 - 1 / (((m + 1 : ℕ) : ℝ))) ^ (m - i.val) := by
  exact MSVV07SourceLemmas.paperRoutePsiCandidate_eq_closed_form i

/--
The printed Theorem 8 exponent `k-i+1` is not the suffix sum of the displayed
dual witness: already at `k=2`, `i=1`, the suffix sum is `1/2`, whereas the
printed exponent gives `3/4`. The general row above proves the corrected
exponent `k-i` in the paper's one-indexed notation.
Source status: corrected source formula; minor finite-index typo
-/
theorem theorem8_dual_induced_tradeoff_ne_printed_exponent_at_k2 :
    MSVV07SourceLemmas.paperRoutePsiCandidate (m := 1) 0 = (1 / 2 : ℝ) ∧
      MSVV07SourceLemmas.paperRoutePsiCandidate (m := 1) 0 ≠
        1 - (1 - 1 / (2 : ℝ)) ^ 2 := by
  norm_num [MSVV07SourceLemmas.paperRoutePsiCandidate_eq_closed_form]

/--
In the simple proof after Theorem 8, a type-`i` bidder whose exact spent
fraction is `i/k` has unspent fraction `(k-i)/k`.  This is the corrected
coefficient corresponding to the corrected dual-suffix exponent.
Source status: corrected source formula; minor finite-index typo
-/
theorem theorem8_corrected_unspent_fraction_formula
    (k i : ℕ) (hk : 0 < k) :
    1 - (i : ℝ) / (k : ℝ) =
      ((k : ℝ) - (i : ℝ)) / (k : ℝ) := by
  exact
    MSVV07PaperFacing.theorem8_corrected_unspent_fraction_formula k i hk

/--
The simple proof's printed coefficient `(k-i+1)/k` is not precisely the
unspent fraction: at `k=2`, type `i=1` has unspent fraction `1/2`, whereas the
printed coefficient is `1`.  The discrepancy vanishes as `k` grows.
Source status: corrected source formula; minor finite-index typo
-/
theorem theorem8_unspent_fraction_ne_printed_at_k2 :
    1 - (1 : ℝ) / 2 = (1 / 2 : ℝ) ∧
      1 - (1 : ℝ) / 2 ≠ ((2 : ℝ) - 1 + 1) / 2 := by
  exact MSVV07PaperFacing.theorem8_unspent_fraction_ne_printed_at_k2

/--
-
Section 5 Lemma 4: for every AdWords instance and monotonically decreasing
tradeoff, the realized preterminal type-count vector gives the right side
`A a` for the factor-revealing matrix.  The fixed geometric dual point is
optimal for the resulting tradeoff-revealing dual.
-/
theorem section5_lemma4_dual_optimal_from_primal_dual_match
    {Advertiser Query : Type*} [Fintype Advertiser]
    (m : ℕ) (I : Proof.PaperInstance Advertiser Query) (history : List Query)
    (psi : ℝ → ℝ) (_hpsi : Antitone psi)
    (_hbid : I.NonnegativeBids) (_hbudget : I.PositiveBudgets) :
    Optimization.IsMinimizerOn
      (MSVV07SourceLemmas.tradeoffRevealingLP (m := m)
        MSVV07SourceLemmas.paperRoutePrimalObjectiveCoeff
        (fun row => ∑ i : Fin m, MSVV07SourceLemmas.paperRouteMatrixCoeff row i *
          SourceRunner.section5PreterminalAlphaTypeCountOfTradeoffRun
            m psi I history i)).DualFeasible
      (MSVV07SourceLemmas.tradeoffRevealingLP (m := m)
        MSVV07SourceLemmas.paperRoutePrimalObjectiveCoeff
        (fun row => ∑ i : Fin m, MSVV07SourceLemmas.paperRouteMatrixCoeff row i *
          SourceRunner.section5PreterminalAlphaTypeCountOfTradeoffRun
            m psi I history i)).dualObjective
      MSVV07SourceLemmas.paperRouteDualCandidate := by
  exact
    Proof.proof_section5_lemma4_paper_tradeoff_dual_candidate_optimal
      (SourceRunner.section5PreterminalAlphaTypeCountOfTradeoffRun m psi I history)
      (SourceRunner.section5PreterminalAlphaTypeCountOfTradeoffRun_nonnegative
        m psi I history)

/--
-
Section 5 Lemma 5: the perturbed LP right side is the base right side plus delta.

Source status: direct paper-facing algebraic row for Lemma 5's perturbed
right-hand side identity.
-/
theorem section5_lemma5_tradeoff_rhs_eq_base_add_delta
    {m : ℕ} (N : ℝ) (alpha beta : Fin m → ℝ) (i : Fin m)
    (hbeta_prefix :
      (∑ j ∈ MSVV07SourceLemmas.paperRoutePrefix i, beta j) =
        MSVV07SourceLemmas.paperRouteRhs N i -
          ∑ j ∈ MSVV07SourceLemmas.paperRoutePrefix i,
            MSVV07SourceLemmas.paperRouteDeltaCoeff i j * alpha j) :
    MSVV07SourceLemmas.paperRouteLPRow alpha i =
      MSVV07SourceLemmas.paperRouteRhs N i +
        MSVV07SourceLemmas.paperRouteDelta alpha beta i := by
  exact
    Proof.proof_section5_lemma5_tradeoff_rhs_eq_base_add_delta
      N alpha beta i hbeta_prefix

/--
- Section 5 Lemma 6: each query satisfies the pointwise ALG/OPT tradeoff.
-/
theorem section5_lemma6_per_query_tradeoff
    {Slab : Type*} [Preorder Slab]
    (psi : Slab → ℝ) {queryType optCurrentSlab algSlab : Slab}
    {optBid algBid : ℝ}
    (hoptCurrent_le_type : optCurrentSlab ≤ queryType)
    (hpsi_antitone : Antitone psi)
    (hoptBid_nonneg : 0 ≤ optBid)
    (hchoice : optBid * psi optCurrentSlab ≤ algBid * psi algSlab) :
    optBid * psi queryType ≤ algBid * psi algSlab := by
  exact
    Proof.proof_section5_lemma6_per_query_tradeoff
      psi hoptCurrent_le_type hpsi_antitone hoptBid_nonneg hchoice

/--
-
Section 5 Lemma 7: the paper's pointwise tradeoff and its type/slab accounting
give the displayed `N/k` weighted-perturbation bound.  The final-slab term is
not an unconstrained interface parameter.
-/
theorem section5_lemma7_weighted_perturbation_bound
    {m Query : Type*} [Fintype m] [Fintype Query] [DecidableEq m]
    (psi alpha beta : m → ℝ) (opt alg : Query → ℝ)
    (queryType querySlab : Query → m) (N : ℝ) (k : ℕ)
    (hpointwise :
      ∀ q : Query, opt q * psi (queryType q) -
        alg q * psi (querySlab q) ≤ 0)
    (hα :
      ∀ i : m,
        (∑ q ∈ (Finset.univ : Finset Query).filter
          (fun q => queryType q = i), opt q) = alpha i)
    (hpsi_nonneg : ∀ i, 0 ≤ psi i)
    (hβ :
      ∀ i : m,
        (∑ q ∈ (Finset.univ : Finset Query).filter
          (fun q => querySlab q = i), alg q) ≤ beta i)
    (hfinal_nonneg : 0 ≤ N / (k : ℝ)) :
    (∑ i : m, psi i * (alpha i - beta i)) ≤ N / (k : ℝ) := by
  exact
    Proof.proof_section5_lemma7_weighted_perturbation_bound_exact_N_div_k_from_pointwise_fibers
      psi alpha beta opt alg queryType querySlab N k hpointwise hα hpsi_nonneg hβ
      hfinal_nonneg

/--
-
Theorem 8, source-shaped limiting endpoint.  As the proved finite small-bids
error vanishes, the `1 - 1/e` competitive inequality holds eventually for
every positive tolerance.  OPT and revenue convergence are conclusions one
may study afterwards, not premises of this theorem.
Source status: Theorem 8 and proof, cached source lines 718-773.
-/
theorem theorem8_balance_msvv_competitive_of_small_bids_limit_family
    {Advertiser : Type*}
    [Fintype Advertiser] [Nonempty Advertiser] [DecidableEq Advertiser]
    (n : ℕ → ℕ)
    (I : (k : ℕ) → PaperInstance Advertiser (Fin (n k)))
    (epsilon : ℕ → ℝ)
    (hbid : ∀ k, (I k).NonnegativeBids)
    (hbudget : ∀ k, (I k).PositiveBudgets)
    (hepsilon : ∀ k, 0 ≤ epsilon k)
    (hepsilon_le_one : ∀ k, epsilon k ≤ 1)
    (hsmall : ∀ k, paperSmallBids (I k) (epsilon k))
    (herror_tendsTo_zero :
      Sequence.SeqTendsTo
        (fun k =>
          epsilon k * (Real.exp 1 + 1) *
            (∑ q : Fin (n k), (I k).maxBidForQuery q))
        0) :
    ∀ delta : ℝ, 0 < delta →
      ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
        paperMsvvRatio *
            (I k).offlineOptimumValue (fun a => (hbudget k a).le) ≤
          paperRevenue (I k)
              ((I k).runAssignment (I k).balanceChoiceRule
                (List.finRange (n k))) +
            delta := by
  exact
    Proof.theorem8_balance_msvv_eventually_competitive_of_vanishing_small_bids_error
      n I epsilon hbid hbudget hepsilon hepsilon_le_one hsmall
      herror_tendsTo_zero

/--
-
Section 6 items 1--2. Different advertiser budgets and nonexhaustive optima
are already part of the base model.  The arrival list is re-indexed by its
positions, so repeated query words are distinct online occurrences rather than
a hidden `Nodup` hypothesis.
-/
theorem section6_different_budgets_and_nonexhaustive_optimum_theorem8_finite_explicit_error
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hepsilon_le_one : epsilon ≤ 1)
    (hsmall : paperSmallBids I epsilon) :
    paperMsvvRatio *
        (SourceRunner.occurrenceIndexedInstance I history).offlineOptimumValue
          (fun a => (hbudget a).le) ≤
      paperRevenue (SourceRunner.occurrenceIndexedInstance I history)
        ((SourceRunner.occurrenceIndexedInstance I history).runAssignment
          (SourceRunner.occurrenceIndexedInstance I history).balanceChoiceRule
          (List.finRange history.length)) +
        epsilon * (Real.exp 1 + 1) *
          (∑ t : Fin history.length,
            (SourceRunner.occurrenceIndexedInstance I history).maxBidForQuery t) := by
  exact
    paper_adwords_balance_msvv_finRange_approx_competitive_with_query_sum_error_bound
      (SourceRunner.occurrenceIndexedInstance I history)
      (SourceRunner.occurrenceIndexedInstance_nonnegativeBids I history hbid)
      (SourceRunner.occurrenceIndexedInstance_positiveBudgets I history hbudget)
      hepsilon hepsilon_le_one
      (SourceRunner.occurrenceIndexedInstance_smallBids I history hsmall)

/--
-
The all-bidders Section 6 next-price charge is the maximum of zero and the
largest bid from an advertiser other than `a`, or zero when there is no other
advertiser.
Source status: direct paper model extension
-/
theorem section6_next_highest_bid_all_formula
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query) (a : Advertiser) (q : Query) :
    section6_next_highest_bid_all I a q =
      let others : Finset Advertiser := (Finset.univ : Finset Advertiser).erase a
      if h : others.Nonempty then
        max 0 (others.sup' h fun b => I.bid b q)
      else
        0 := by
  classical
  unfold section6_next_highest_bid_all Proof.section6_next_highest_bid_all
  rfl

/--
-
The alive-bidders Section 6 next-price charge is the maximum of zero and the
largest bid from an alive advertiser other than `a`, or zero when no such
advertiser exists.
Source status: direct paper model extension
-/
theorem section6_next_highest_bid_alive_formula
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (alive : Advertiser → Query → Prop) [∀ a q, Decidable (alive a q)]
    (a : Advertiser) (q : Query) :
    section6_next_highest_bid_alive I alive a q =
      let others : Finset Advertiser :=
        ((Finset.univ : Finset Advertiser).erase a).filter fun b => alive b q
      if h : others.Nonempty then
        max 0 (others.sup' h fun b => I.bid b q)
      else
        0 := by
  classical
  unfold section6_next_highest_bid_alive Proof.section6_next_highest_bid_alive
  rfl

/--
Section 6's all-bidders next-price algorithm inherits the finite Theorem 8
guarantee when its actual effective charges satisfy the small-bids condition.
This is the precise arbitrary-budget condition; equal budgets are only one
sufficient special case.
-/
theorem section6_next_highest_bid_all_theorem8_finite_explicit_error
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hepsilon_le_one : epsilon ≤ 1)
    (hnext_small : ∀ a q,
      section6_next_highest_bid_all I a q ≤ epsilon * I.budget a) :
    paperMsvvRatio *
        (SourceRunner.occurrenceIndexedInstance
          (I.withEffectiveBids (section6_next_highest_bid_all I)) history).offlineOptimumValue
          (fun a => (hbudget a).le) ≤
      paperRevenue
        (SourceRunner.occurrenceIndexedInstance
          (I.withEffectiveBids (section6_next_highest_bid_all I)) history)
        ((SourceRunner.occurrenceIndexedInstance
          (I.withEffectiveBids (section6_next_highest_bid_all I)) history).runAssignment
          (SourceRunner.occurrenceIndexedInstance
            (I.withEffectiveBids (section6_next_highest_bid_all I)) history).balanceChoiceRule
          (List.finRange history.length)) +
        epsilon * (Real.exp 1 + 1) *
          (∑ t : Fin history.length,
            (SourceRunner.occurrenceIndexedInstance
              (I.withEffectiveBids (section6_next_highest_bid_all I)) history).maxBidForQuery t) := by
  exact
    paper_adwords_balance_msvv_finRange_approx_competitive_with_query_sum_error_bound
      (SourceRunner.occurrenceIndexedInstance
        (I.withEffectiveBids (section6_next_highest_bid_all I)) history)
      (SourceRunner.occurrenceIndexedInstance_nonnegativeBids _ _
        (AdWordsInstance.withEffectiveBids_nonnegativeBids I _
          (Proof.section6_next_highest_bid_all_nonnegative I)))
      (SourceRunner.occurrenceIndexedInstance_positiveBudgets _ _
        (AdWordsInstance.withEffectiveBids_positiveBudgets I _ hbudget))
      hepsilon hepsilon_le_one
      (SourceRunner.occurrenceIndexedInstance_smallBids _ _
        (Proof.section6_effective_bids_small_bids I
          (section6_next_highest_bid_all I) hnext_small))

/--
For the Section 6 alive-bidders next-price case, MSVV07 permits the online
algorithm to keep every bidder alive. The alive charge rule then reduces
pointwise to the all-bidders rule, so its finite occurrence-indexed guarantee
is exactly the all-bidders one under the same effective-charge small-bids
condition.
-/
theorem section6_next_highest_bid_alive_theorem8_finite_explicit_error
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hepsilon_le_one : epsilon ≤ 1)
    (hnext_small : ∀ a q,
      section6_next_highest_bid_all I a q ≤ epsilon * I.budget a) :
    (∀ a q,
      Proof.section6_next_highest_bid_alive I (fun _ _ => True) a q =
        Proof.section6_next_highest_bid_all I a q) ∧
    paperMsvvRatio *
        (SourceRunner.occurrenceIndexedInstance
          (I.withEffectiveBids (section6_next_highest_bid_all I)) history).offlineOptimumValue
          (fun a => (hbudget a).le) ≤
      paperRevenue
        (SourceRunner.occurrenceIndexedInstance
          (I.withEffectiveBids (section6_next_highest_bid_all I)) history)
        ((SourceRunner.occurrenceIndexedInstance
          (I.withEffectiveBids (section6_next_highest_bid_all I)) history).runAssignment
          (SourceRunner.occurrenceIndexedInstance
            (I.withEffectiveBids (section6_next_highest_bid_all I)) history).balanceChoiceRule
          (List.finRange history.length)) +
        epsilon * (Real.exp 1 + 1) *
          (∑ t : Fin history.length,
            (SourceRunner.occurrenceIndexedInstance
              (I.withEffectiveBids (section6_next_highest_bid_all I)) history).maxBidForQuery t) := by
  refine ⟨?_, ?_⟩
  · intro a q
    exact SourceRunner.section6_all_alive_next_price_reduces_to_all_bidders I a q
  · exact
      section6_next_highest_bid_all_theorem8_finite_explicit_error
        I hbudget history hepsilon hepsilon_le_one hnext_small

/--
Section 6's click-through-rate reduction replaces each bid by the expected
effective bid `CTR * bid` while leaving budgets unchanged.
Source status: direct paper model-extension formula
-/
theorem section6_click_through_rates_effective_bid_formula
    {Advertiser Query : Type*}
    (I : PaperInstance Advertiser Query)
    (ctr : Advertiser → Query → ℝ) (a : Advertiser) (q : Query) :
    (I.withClickThroughRates ctr).bid a q = ctr a q * I.bid a q := by
  rfl

/-- Section 6 CTR guarantee on the occurrence-indexed arrival model. -/
theorem section6_click_through_rates_theorem8_finite_explicit_error
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (ctr : Advertiser → Query → ℝ)
    (hctr_nonneg : ∀ a q, 0 ≤ ctr a q)
    (hctr_le_one : ∀ a q, ctr a q ≤ 1)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hepsilon_le_one : epsilon ≤ 1)
    (hsmall : paperSmallBids I epsilon) :
    paperMsvvRatio *
        (SourceRunner.occurrenceIndexedInstance
          (I.withClickThroughRates ctr) history).offlineOptimumValue
          (fun a => (hbudget a).le) ≤
      paperRevenue (SourceRunner.occurrenceIndexedInstance
        (I.withClickThroughRates ctr) history)
        ((SourceRunner.occurrenceIndexedInstance
          (I.withClickThroughRates ctr) history).runAssignment
          (SourceRunner.occurrenceIndexedInstance
            (I.withClickThroughRates ctr) history).balanceChoiceRule
          (List.finRange history.length)) +
        epsilon * (Real.exp 1 + 1) *
          (∑ t : Fin history.length,
            (SourceRunner.occurrenceIndexedInstance
              (I.withClickThroughRates ctr) history).maxBidForQuery t) := by
  exact
    paper_adwords_balance_msvv_finRange_approx_competitive_with_query_sum_error_bound
      (SourceRunner.occurrenceIndexedInstance (I.withClickThroughRates ctr) history)
      (SourceRunner.occurrenceIndexedInstance_nonnegativeBids _ _
        (AdWordsInstance.withClickThroughRates_nonnegativeBids I ctr hctr_nonneg hbid))
      (SourceRunner.occurrenceIndexedInstance_positiveBudgets _ _
        (AdWordsInstance.withClickThroughRates_positiveBudgets I ctr hbudget))
      hepsilon hepsilon_le_one
      (SourceRunner.occurrenceIndexedInstance_smallBids _ _
        (Proof.section6_click_through_rates_small_bids I ctr hbid hctr_le_one hsmall))

/--
Section 6 delayed-entry guarantee on the occurrence-indexed arrival model.
Each advertiser has one entry time, so it is unavailable before that occurrence
and remains available afterwards, as the source's "enter at any time" model
requires.
-/
theorem section6_availability_theorem8_finite_explicit_error
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    (entryTime : Advertiser → Fin (history.length + 1))
    {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hepsilon_le_one : epsilon ≤ 1)
    (hsmall : paperSmallBids I epsilon) :
    let J0 := SourceRunner.occurrenceIndexedInstance I history
    let J := J0.withAvailability (SourceRunner.availableFromEntry entryTime)
    paperMsvvRatio *
        J.offlineOptimumValue
          (fun a => (hbudget a).le) ≤
      paperRevenue J
        (J.runAssignment J.balanceChoiceRule
          (List.finRange history.length)) +
        epsilon * (Real.exp 1 + 1) *
          (∑ t : Fin history.length,
            J.maxBidForQuery t) := by
  exact
    paper_adwords_balance_msvv_finRange_approx_competitive_with_query_sum_error_bound
      ((SourceRunner.occurrenceIndexedInstance I history).withAvailability
        (SourceRunner.availableFromEntry entryTime))
      (AdWordsInstance.withAvailability_nonnegativeBids _ _
        (SourceRunner.occurrenceIndexedInstance_nonnegativeBids I history hbid))
      (AdWordsInstance.withAvailability_positiveBudgets _ _
        (SourceRunner.occurrenceIndexedInstance_positiveBudgets I history hbudget))
      hepsilon hepsilon_le_one
      (Proof.section6_availability_small_bids
        (SourceRunner.occurrenceIndexedInstance I history)
        (SourceRunner.availableFromEntry entryTime) hepsilon
        (SourceRunner.occurrenceIndexedInstance_positiveBudgets I history hbudget)
        (SourceRunner.occurrenceIndexedInstance_smallBids I history hsmall))

/--
-
Section 6 multiple slots: source-shaped page-level finite explicit Theorem 8
guarantee. On each page `q`, Balance chooses the top `slots q` distinct feasible
advertisers by current scaled bid, and competes with the page-level offline
optimum subject to the same per-page cardinality and advertiser-budget
constraints.
-/
theorem section6_page_top_balance_theorem8_finite_explicit_error
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : PaperInstance Advertiser Query)
    (slots : Query → ℕ)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    (hnodup : history.Nodup)
    (hcover : AdWordsInstance.historyFinset history = Finset.univ)
    {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hepsilon_le_one : epsilon ≤ 1)
    (hsmall : paperSmallBids I epsilon) :
    paperMsvvRatio *
        I.pageOfflineOptimumValue slots (fun a => (hbudget a).le) ≤
      I.pageRevenue
        (I.runPageAssignment slots (I.pageTopBalanceRule slots) history) +
        epsilon * (Real.exp 1 + 1) *
          I.pageHistoryMaxBidSum slots history := by
  exact
    Proof.proof_section6_page_top_balance_theorem8_finite_explicit_error
      I slots hbid hbudget history hnodup hcover
      hepsilon hepsilon_le_one hsmall

/--
-
Section 8's weighted-bid proposal replaces each advertiser's bid by
`weight advertiser * bid`.  This row checks only the proposed effective-bid
definition, not the open fixed-distribution guarantee or online weight update.
Source status: direct paper algorithm formula
-/
theorem section8_weighted_effective_bid_formula
    {Advertiser Query : Type*}
    (I : PaperInstance Advertiser Query)
    (weight : Advertiser → ℝ) (a : Advertiser) (q : Query) :
    (I.withAdvertiserWeights weight).bid a q = weight a * I.bid a q := by
  rfl

/--
-
Auxiliary transformed-instance theorem for advertiser-weighted effective bids.
This is not the source's Section 8 claim: Section 8 proposes a weighted-bid
algorithm for a fixed-distribution model and leaves its `1 - o(1)` guarantee as
an open question. Accordingly this theorem is not part of the configured
paper-facing review surface.
-/
theorem section8_weighted_bids_theorem8_finite_explicit_error_of_weighted_small_bids
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : PaperInstance Advertiser Query)
    (weight : Advertiser → ℝ)
    (hweight_nonneg : ∀ a, 0 ≤ weight a)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    (hnodup : history.Nodup)
    (hcover : AdWordsInstance.historyFinset history = Finset.univ)
    {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hepsilon_le_one : epsilon ≤ 1)
    (hweighted_small :
      ∀ a q, weight a * I.bid a q ≤ epsilon * I.budget a) :
    paperMsvvRatio *
        (I.withAdvertiserWeights weight).offlineOptimumValue
          (fun a => (hbudget a).le) ≤
      (I.withAdvertiserWeights weight).revenue
        ((I.withAdvertiserWeights weight).runAssignment
          (I.withAdvertiserWeights weight).balanceChoiceRule history) +
        epsilon * (Real.exp 1 + 1) *
          (∑ q : Query, (I.withAdvertiserWeights weight).maxBidForQuery q) := by
  exact
    Proof.proof_section8_weighted_bids_theorem8_finite_explicit_error_of_weighted_small_bids
      I weight hweight_nonneg hbid hbudget history hnodup hcover
      hepsilon hepsilon_le_one hweighted_small

/--
If one uses the Appendix's asserted zero phase-3 revenue, its printed phase
counts contribute `0.4N + 0.2N + 0 = 0.6N`.  This is an arithmetic check on
the printed account, not the true revenue of the corrected execution below.
Source status: corrected Appendix arithmetic note
-/
theorem appendix_highest_bid_phase_total_eq_three_fifths (N : ℝ) :
    appendixHighestBidPhaseOneRevenue N +
        appendixHighestBidPhaseTwoRevenue N +
        appendixHighestBidPhaseThreeRevenue N =
      (3 / 5 : ℝ) * N := by
  exact
    MSVV07PaperFacing.appendix_highest_bid_phase_total_eq_three_fifths N

/--
For positive `N`, the Appendix phase counts do not equal its printed `0.62N`
display.  This is one ordinary arithmetic defect in the printed zero-phase-3
account; the state-derived execution below supplies the actual revenue.
Source status: corrected Appendix arithmetic
-/
theorem appendix_highest_bid_phase_total_ne_printed_062
    {N : ℝ} (hN : 0 < N) :
    appendixHighestBidPhaseOneRevenue N +
        appendixHighestBidPhaseTwoRevenue N +
        appendixHighestBidPhaseThreeRevenue N ≠
      (31 / 50 : ℝ) * N := by
  exact
    MSVV07PaperFacing.appendix_highest_bid_phase_total_ne_printed_062 hN

/--
The zero-phase-3 phase-count factor `3/5` is below the paper's `1 - 1/e`
benchmark.  The true corrected execution has a slightly different factor,
proved separately below to satisfy the same strict inequality.
Source status: corrected Appendix arithmetic
-/
theorem appendix_three_fifths_lt_msvv_ratio :
    (3 / 5 : ℝ) < paperMsvvRatio := by
  exact MSVV07PaperFacing.appendix_three_fifths_lt_msvv_ratio

/-!
### Appendix state-derived fluid execution

The source takes the small-bid limit `a → 0`.  The configured rows therefore
expose the corresponding fluid execution, including within-phase choice-state
checks, rather than claiming a fixed positive-`a` finite runner theorem.
-/

/--
In phase 1 all currently eligible bidders have equal prior spend.  In phase 2
the allocated tail bidders have maximal raw bid and remain tied in prior spend.
These are the source rule's choice conditions in its small-bids fluid limit.
Source status: direct source algorithm in the small-bids fluid limit
-/
theorem appendix_naive_highest_bid_fluid_rule :
    (∀ r : ℝ, 0 ≤ r → r ≤ 2 / 5 →
      (∫ _bidder in (1 / 10 + r)..1,
        MSVV07Appendix.printedPhaseOneAllocationRate r) = 1) ∧
    (∀ r bidder₁ bidder₂ : ℝ,
      0 ≤ r → r ≤ 2 / 5 →
      MSVV07Appendix.printedPhaseOneEligible r bidder₁ →
      MSVV07Appendix.printedPhaseOneEligible r bidder₂ →
        MSVV07Appendix.printedPhaseOneRawBid r bidder₁ =
            MSVV07Appendix.printedPhaseOneRawBid r bidder₂ ∧
          MSVV07Appendix.printedIndividualLeftover bidder₁
              (MSVV07Appendix.printedPhaseOneSpentBefore r bidder₁) =
            MSVV07Appendix.printedIndividualLeftover bidder₂
              (MSVV07Appendix.printedPhaseOneSpentBefore r bidder₂)) ∧
    (∫ bidder in (1 / 2 : ℝ)..1,
      MSVV07Appendix.printedPhaseTwoAllocationDensity bidder) = 1 ∧
    (∀ offset bidder competitor : ℝ,
      0 < MSVV07Appendix.printedPhaseTwoAllocationDensity bidder →
      ((1 / 2 ≤ competitor ∧ competitor ≤ 1) ∨ competitor = offset) →
        MSVV07Appendix.printedPhaseTwoRawBid offset competitor ≤
          MSVV07Appendix.printedPhaseTwoRawBid offset bidder) ∧
    (∀ offset bidder₁ bidder₂ : ℝ,
      0 ≤ offset → offset ≤ 1 / 10 →
      (1 / 2 ≤ bidder₁ ∧ bidder₁ ≤ 1) →
      (1 / 2 ≤ bidder₂ ∧ bidder₂ ≤ 1) →
        MSVV07Appendix.printedIndividualLeftover bidder₁
            (MSVV07Appendix.printedPhaseTwoSpentBefore offset bidder₁) =
          MSVV07Appendix.printedIndividualLeftover bidder₂
            (MSVV07Appendix.printedPhaseTwoSpentBefore offset bidder₂)) ∧
    (∀ progress owner : ℝ, 0 ≤ progress →
      MSVV07Appendix.printedPhaseThreeAllocationRate progress owner owner +
        MSVV07Appendix.printedPhaseThreeDiscardRate progress = 1) ∧
    ∀ progress owner : ℝ,
      (1 / 2 ≤ owner ∧ owner ≤ 1) →
      0 < MSVV07Appendix.printedPhaseThreeDiscardRate progress →
        MSVV07Appendix.printedPhaseThreeSpentBefore
          progress owner = 1 := by
  refine ⟨?_, ?_, MSVV07Appendix.printed_phaseTwo_round_conservation,
    ?_, ?_, ?_, ?_⟩
  · intro r hr0 hr
    exact MSVV07Appendix.printed_phaseOne_round_conservation hr0 hr
  · intro r bidder₁ bidder₂ hr0 hr h₁ h₂
    exact ⟨MSVV07Appendix.printed_phaseOne_raw_bid_tie_of_eligible h₁ h₂,
      MSVV07Appendix.printed_phaseOne_equal_leftover_of_eligible hr0 hr h₁ h₂⟩
  · intro offset bidder competitor hallocated hcompetitor
    exact MSVV07Appendix.printed_phaseTwo_raw_bid_maximal
      hallocated hcompetitor
  · intro offset bidder₁ bidder₂ hoffset0 hoffset h₁ h₂
    exact MSVV07Appendix.printed_phaseTwo_equal_leftover_of_tail
      hoffset0 hoffset h₁ h₂
  · intro progress owner hprogress0
    exact MSVV07Appendix.printed_phaseThree_round_conservation hprogress0
  · intro progress owner howner hdiscard
    exact MSVV07Appendix.printed_phaseThree_no_discard_unless_saturated
      howner hdiscard

/--
The corrected three-phase allocation is feasible; its decision-time states are
computed from prior allocations, and the positive phase-3 residual is served
to exhaust the tail cohort.
Source status: corrected source construction in the stated small-bids fluid limit
-/
theorem appendix_naive_three_phase_fluid_construction :
    0 < MSVV07Appendix.printedPhaseThreeResidualPerTail ∧
    (∀ owner : ℝ, (1 / 2 ≤ owner ∧ owner ≤ 1) →
      MSVV07Appendix.printedPhaseThreeSpentBefore
        MSVV07Appendix.printedPhaseThreeResidualPerTail owner = 1) ∧
    MSVV07Appendix.printedContinuousOnlineValue =
      9 / 10 - 1 / 2 * Real.log (9 / 5) ∧
    MSVV07Appendix.printedContinuousOfflineValue = 1 := by
  refine ⟨MSVV07Appendix.printedPhaseThreeResidualPerTail_pos, ?_,
    MSVV07Appendix.printedContinuousOnlineValue_eq,
    MSVV07Appendix.printedContinuousOfflineValue_eq_one⟩
  intro owner howner
  exact MSVV07Appendix.printed_phaseThree_owner_saturated howner

/--
The printed exhaustion claim is false.  The corrected online value includes
the phase-3 residual; the separate `3/5` and `31/50` equalities record the two
numbers appearing in the paper's erroneous zero-phase-3 account.
Source status: corrected source statement
-/
theorem appendix_naive_algorithm_true_revenue_formula :
    MSVV07Appendix.printedContinuousOnlineValue =
      9 / 10 - 1 / 2 * Real.log (9 / 5) ∧
    MSVV07Appendix.printedPhaseThreeServedMass =
      3 / 10 - 1 / 2 * Real.log (9 / 5) ∧
    0 < MSVV07Appendix.printedPhaseThreeServedMass ∧
    (2 / 5 : ℝ) + 2 * (1 / 10) = 3 / 5 ∧
    (3 / 5 : ℝ) ≠ 31 / 50 := by
  refine ⟨MSVV07Appendix.printedContinuousOnlineValue_eq,
    MSVV07Appendix.printedPhaseThreeServedMass_eq, ?_,
    MSVV07Appendix.printed_zero_phaseThree_accounting,
    MSVV07Appendix.printed_zero_phaseThree_accounting_ne_point62⟩
  exact mul_pos (by norm_num) MSVV07Appendix.printedPhaseThreeResidualPerTail_pos

/--
The displayed offline allocation is feasible, has value one, and is optimal.
Source status: direct paper Appendix offline-optimum formula
-/
theorem appendix_optimum_revenue_formula :
    ((∀ r : ℝ, 0 ≤ r → r ≤ 2 / 5 →
        MSVV07Appendix.printedPhaseOneRawBid r (1 / 10 + r) = 1) ∧
      (∀ offset : ℝ, 0 ≤ offset → offset ≤ 1 / 10 →
        MSVV07Appendix.printedPhaseTwoRawBid offset offset = 1) ∧
      (∀ owner : ℝ, 1 / 2 ≤ owner → owner ≤ 1 →
        MSVV07Appendix.printedPhaseThreeRawBid owner owner = 1) ∧
      (2 / 5 : ℝ) + 1 / 10 + 1 / 2 = 1) ∧
    MSVV07Appendix.ContinuousUnitBudgetFeasible
        (fun _bidder : ℝ => (1 : ℝ)) ∧
    MSVV07Appendix.printedContinuousOfflineValue = 1 ∧
    ∀ spend : ℝ → ℝ,
      MSVV07Appendix.ContinuousUnitBudgetFeasible spend →
        (∫ bidder in (0 : ℝ)..1, spend bidder) ≤
          MSVV07Appendix.printedContinuousOfflineValue := by
  exact MSVV07Appendix.printed_continuous_offline_optimal

/--
The corrected printed-instance competitive factor is still strictly below `1-1/e`.
Source status: corrected source conclusion
-/
theorem appendix_naive_true_ratio_conclusion :
    MSVV07Appendix.printedContinuousOnlineValue /
        MSVV07Appendix.printedContinuousOfflineValue <
      paperMsvvRatio := by
  rw [MSVV07Appendix.printedContinuousOnlineValue_eq,
    MSVV07Appendix.printedContinuousOfflineValue_eq_one,
    div_one, paperMsvvRatio_formula]
  exact MSVV07Appendix.printed_true_ratio_lt_msvvRatio

/--
For every `kappa > 1`, the explicit derived normalized `0/1/kappa` family has
a continuous per-individual highest-bid/most-leftover execution.  The source
states this existence claim but does not print parameters.
Source status: derived witness for a source existence claim; the source omits phase parameters
-/
theorem appendix_kappa_continuous_source_execution
    {κ : ℝ} (hκ : 1 < κ) :
    (∀ progress : ℝ, 0 ≤ progress → progress ≤ MSVV07Appendix.derivedKappaB κ →
      (∫ _bidder in
          (MSVV07Appendix.derivedKappaX κ + progress)..1,
        MSVV07Appendix.derivedKappaPhaseOneAllocationRate κ progress) = 1) ∧
    (∀ progress bidder₁ bidder₂ : ℝ,
      0 ≤ progress → progress ≤ MSVV07Appendix.derivedKappaB κ →
      MSVV07Appendix.derivedKappaPhaseOneEligible κ progress bidder₁ →
      MSVV07Appendix.derivedKappaPhaseOneEligible κ progress bidder₂ →
        MSVV07Appendix.derivedKappaPhaseOneRawBid κ progress bidder₁ =
            MSVV07Appendix.derivedKappaPhaseOneRawBid κ progress bidder₂ ∧
          MSVV07Appendix.printedIndividualLeftover bidder₁
              (MSVV07Appendix.derivedKappaPhaseOneSpentBefore κ progress bidder₁) =
            MSVV07Appendix.printedIndividualLeftover bidder₂
              (MSVV07Appendix.derivedKappaPhaseOneSpentBefore
                κ progress bidder₂)) ∧
    (∫ bidder in (1 - MSVV07Appendix.derivedKappaT κ)..1,
      MSVV07Appendix.derivedKappaPhaseTwoAllocationDensity κ bidder) = 1 ∧
    (∀ offset bidder competitor : ℝ,
      0 < MSVV07Appendix.derivedKappaPhaseTwoAllocationDensity κ bidder →
      (MSVV07Appendix.derivedKappaTail κ competitor ∨ competitor = offset) →
        MSVV07Appendix.derivedKappaPhaseTwoRawBid κ offset competitor ≤
          MSVV07Appendix.derivedKappaPhaseTwoRawBid κ offset bidder) ∧
    (∀ offset bidder₁ bidder₂ : ℝ,
      0 ≤ offset → offset ≤ MSVV07Appendix.derivedKappaX κ →
      MSVV07Appendix.derivedKappaTail κ bidder₁ →
      MSVV07Appendix.derivedKappaTail κ bidder₂ →
        MSVV07Appendix.printedIndividualLeftover bidder₁
            (MSVV07Appendix.derivedKappaPhaseTwoSpentBefore κ offset bidder₁) =
          MSVV07Appendix.printedIndividualLeftover bidder₂
            (MSVV07Appendix.derivedKappaPhaseTwoSpentBefore
              κ offset bidder₂)) ∧
    (∀ bidder : ℝ, MSVV07Appendix.derivedKappaTail κ bidder →
      MSVV07Appendix.derivedKappaPhaseTwoSpentBefore
        κ (MSVV07Appendix.derivedKappaX κ) bidder = 1) ∧
    (∀ owner : ℝ, MSVV07Appendix.derivedKappaTail κ owner →
      MSVV07Appendix.derivedKappaPhaseThreeAllocationRate owner owner +
          MSVV07Appendix.derivedKappaPhaseThreeDiscardRate owner = 1 ∧
        MSVV07Appendix.derivedKappaPhaseTwoSpentBefore
            κ (MSVV07Appendix.derivedKappaX κ) owner = 1 ∧
        ∀ bidder : ℝ,
          0 < MSVV07Appendix.derivedKappaPhaseThreeRawBid owner bidder →
            bidder = owner) ∧
    MSVV07Appendix.derivedKappaContinuousOnlineValue κ =
      MSVV07Appendix.derivedKappaRatio κ ∧
    MSVV07Appendix.derivedKappaContinuousOfflineValue κ = 1 := by
  exact MSVV07Appendix.derivedKappa_continuous_source_execution_bridge hκ

/-- The continuous DERIVED execution has optimum one and factor below `1-1/e`. -/
theorem appendix_kappa_counterexample_family
    {κ : ℝ} (hκ : 1 < κ) :
    MSVV07Appendix.derivedKappaContinuousOnlineValue κ =
      MSVV07Appendix.derivedKappaRatio κ ∧
    MSVV07Appendix.derivedKappaContinuousOfflineValue κ = 1 ∧
    MSVV07Appendix.ContinuousUnitBudgetFeasible
      (fun _bidder : ℝ => (1 : ℝ)) ∧
    (∀ spend : ℝ → ℝ,
      MSVV07Appendix.ContinuousUnitBudgetFeasible spend →
        (∫ bidder in (0 : ℝ)..1, spend bidder) ≤
          MSVV07Appendix.derivedKappaContinuousOfflineValue κ) ∧
    MSVV07Appendix.derivedKappaContinuousOnlineValue κ /
        MSVV07Appendix.derivedKappaContinuousOfflineValue κ <
      paperMsvvRatio := by
  have hoff := MSVV07Appendix.derivedKappa_continuous_offline_optimal hκ
  refine ⟨MSVV07Appendix.derivedKappaContinuousOnlineValue_eq hκ,
    hoff.2.1, hoff.1, hoff.2.2, ?_⟩
  rw [MSVV07Appendix.derivedKappaContinuousOnlineValue_eq hκ,
    MSVV07Appendix.derivedKappaContinuousOfflineValue_eq_one hκ,
    div_one, paperMsvvRatio_formula]
  exact MSVV07Appendix.derivedKappaRatio_lt_msvvRatio hκ

/--
The derived family's factor tends to `1-1/e` as `kappa` tends to infinity.
Source status: derived witness for a source existence claim; the source omits phase parameters
-/
theorem appendix_kappa_ratio_limit_infinity :
    (∀ κ : ℝ, 1 < κ →
      MSVV07Appendix.derivedKappaContinuousOnlineValue κ /
          MSVV07Appendix.derivedKappaContinuousOfflineValue κ =
        MSVV07Appendix.derivedKappaRatio κ) ∧
    Filter.Tendsto MSVV07Appendix.derivedKappaRatio Filter.atTop
      (nhds paperMsvvRatio) := by
  refine ⟨?_, ?_⟩
  · intro κ hκ
    rw [MSVV07Appendix.derivedKappaContinuousOnlineValue_eq hκ,
      MSVV07Appendix.derivedKappaContinuousOfflineValue_eq_one hκ, div_one]
  · rw [paperMsvvRatio_formula]
    exact MSVV07Appendix.derivedKappaRatio_tendsto_atTop

/--
The derived factor tends to one half from the right at `kappa=1`, whereas the
separate `kappa = 1` BALANCE instance has factor `1 - 1/e`.  The continuous
extension of the auxiliary formula is deliberately not identified with that
source instance.
Source status: derived witness for a source existence claim; the source omits phase parameters
-/
theorem appendix_kappa_ratio_limit_one :
    (∀ κ : ℝ, 1 < κ →
      MSVV07Appendix.derivedKappaContinuousOnlineValue κ /
          MSVV07Appendix.derivedKappaContinuousOfflineValue κ =
        MSVV07Appendix.derivedKappaRatio κ) ∧
    Filter.Tendsto MSVV07Appendix.derivedKappaRatio
        (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds (1 / 2 : ℝ)) ∧
    (1 / 2 : ℝ) ≠ paperMsvvRatio := by
  refine ⟨?_, MSVV07Appendix.derivedKappaRatio_tendsto_one_right,
    ?_⟩
  · intro κ hκ
    rw [MSVV07Appendix.derivedKappaContinuousOnlineValue_eq hκ,
      MSVV07Appendix.derivedKappaContinuousOfflineValue_eq_one hκ, div_one]
  rw [paperMsvvRatio_formula]
  exact MSVV07Appendix.derivedKappa_right_limit_ne_balance_factor

/--
- The hard distribution in Theorem 9 is uniform over bidder permutations.
-/
theorem theorem9HardDistribution_uniform (N : ℕ) :
    theorem9HardDistribution N = uniformPermutationDistribution N := by
  rfl

/--
Implementation identity for capped revenue on one realized permutation.  It is
kept as support for the final averaging argument, but is not itself the
source-facing Theorem 9 q_ij expectation claim.
-/
theorem theorem9CappedNormalizedRevenue_formula
    (N : ℕ)
    (algorithm :
      { choice : BMatchingIntegralPrefixChoice N //
        BMatchingIntegralPrefixChoice.Feasible choice })
    (permutation : Equiv.Perm (Fin N)) :
    theorem9CappedNormalizedRevenue N algorithm permutation =
      (∑ bidder : Fin N,
        min 1
          (∑ round : Fin N,
            BMatchingIntegralPrefixAlgorithm.prefixAllocation algorithm
              (theorem9ObservedPrefix N permutation round)
              round (permutation bidder))) /
        (N : ℝ) := by
  exact theorem9_capped_normalized_revenue_eq_prefix_spend N algorithm permutation

/--
Theorem 9's source-facing `q_ij` claim: for a fixed deterministic algorithm,
the expected fraction of round-`i` queries allocated to bidder `j` under a
uniform random bidder permutation is at most `1/(N-i+1)` when that bidder is
eligible, and is zero otherwise.
-/
theorem theorem9_qij_expected_allocation_bound
    (N : ℕ) (algorithm : BMatchingIntegralPrefixAlgorithm N)
    (round bidder : Fin N) :
    (SourceRunner.theorem9ExpectedRoundAllocation N algorithm round bidder ≤
      if (round : ℕ) ≤ (bidder : ℕ) then
        1 / ((N - (round : ℕ) : ℕ) : ℝ)
      else 0) ∧
      (¬ (round : ℕ) ≤ (bidder : ℕ) →
        SourceRunner.theorem9ExpectedRoundAllocation
          N algorithm round bidder = 0) := by
  exact
    ⟨SourceRunner.theorem9_expected_round_allocation_bound
        N algorithm round bidder,
      SourceRunner.theorem9_expected_round_allocation_zero_of_ineligible
        N algorithm round bidder⟩

/--
-
Theorem 9, paper-facing randomized online algorithm endpoint in the finite
prefix model.
Source status: direct paper theorem
-/
theorem theorem9_no_randomized_online_algorithm_beats_msvv_ratio :
    ∀ delta : ℝ, 0 < delta →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        ∀ randomizedAlgorithm : theorem9RandomizedOnlineAlgorithm N,
          ¬ ∀ permutation,
            paperMsvvRatio + delta <
              AppliedModelingLib.pmfExp randomizedAlgorithm
                (fun algorithm =>
                  theorem9CappedNormalizedRevenue N algorithm permutation) := by
  exact Proof.proof_theorem9_no_randomized_online_algorithm_beats_msvv_ratio

/-! ## Paper assumption rows defined in the theorem layer -/

/--
-
The source-shaped small-bids limiting regime for Theorem 8: the finite error
term obtained from the proved accounting theorem tends to zero.  This
definition does not assume convergence of OPT, revenue, or the competitive
conclusion.
Source status: Theorem 8 and proof, cached source lines 718-773.
-/
def paperSmallBidsLimitFamily_fields
    {Advertiser : Type*}
    [Fintype Advertiser] [Nonempty Advertiser] [DecidableEq Advertiser]
    (n : ℕ → ℕ)
    (I : (k : ℕ) → PaperInstance Advertiser (Fin (n k)))
    (epsilon : ℕ → ℝ) : Prop :=
  (∀ k, (I k).NonnegativeBids) ∧
    (∀ k, (I k).PositiveBudgets) ∧
      (∀ k, 0 ≤ epsilon k) ∧
        (∀ k, epsilon k ≤ 1) ∧
          (∀ k, paperSmallBids (I k) (epsilon k)) ∧
            Sequence.SeqTendsTo
              (fun k =>
                epsilon k * (Real.exp 1 + 1) *
                  (∑ q : Fin (n k), (I k).maxBidForQuery q))
              0

/-! ## Source-completeness rows added by the full paper audit -/

/--
Section 2's universal revenue-ratio definition of alpha competitiveness.
Source status: direct paper definition
-/
theorem section2_competitive_ratio_definition
    {Instance : Type*} (onlineRevenue offlineRevenue : Instance → ℝ) (α : ℝ) :
    SourceRunner.IsAlphaCompetitive onlineRevenue offlineRevenue α ↔
      ∀ I, α ≤ onlineRevenue I / offlineRevenue I := by
  rfl

/--
The equal-unit-budget normalization used temporarily in Sections 2--5.
Source status: direct paper simplifying assumption
-/
theorem section2_equal_unit_budgets_simplifying_assumption
    {Advertiser Query : Type*} (I : PaperInstance Advertiser Query) :
    SourceRunner.EqualUnitBudgets I ↔ ∀ a, I.budget a = 1 := by
  rfl

/--
The temporary Section 2 simplifying assumption: a best offline allocation
exhausts every bidder budget.  Both the optimality qualifier and the
exhaustion condition are part of the source statement.
-/
theorem section2_exhaustive_optimum_simplifying_assumption
    {Advertiser Query : Type*} [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (opt : PaperAssignment Advertiser Query) :
    (I.IsOptimalAssignment opt ∧ SourceRunner.ExhaustsEveryBudget I opt) ↔
      (I.IsOptimalAssignment opt ∧ ∀ a, paperSpend I opt a = I.budget a) := by
  rfl

/-- The displayed finite `psi_k` is decreasing over source slabs `1,...,k`. -/
theorem section3_discrete_tradeoff_monotonicity (k : ℕ) :
    Antitone (paperDiscreteTradeoff k) := by
  exact SourceRunner.discreteTradeoff_antitone k

/--
The source current slab is the capped floor of `k` times spent fraction.
Source status: direct paper definition
-/
theorem section3_slab_and_current_slab_definition
    (k : ℕ) (hk : 0 < k) (spentFraction : ℝ) :
    (SourceRunner.activeSlab k hk spentFraction).val =
      min (Nat.floor (max 0 ((k : ℝ) * spentFraction))) (k - 1) := by
  exact SourceRunner.activeSlab_val_formula k hk spentFraction

/-- Finite slab weights converge to the continuous tradeoff along convergent slab fractions. -/
theorem section3_discrete_tradeoff_convergence
    (slab : ℕ → ℕ) (s : ℝ)
    (hfraction :
      Filter.Tendsto
        (fun k : ℕ => ((slab k + 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ))
        Filter.atTop (nhds s)) :
    Sequence.SeqTendsTo
      (fun k : ℕ =>
        1 - Real.exp
          (-(1 - (((slab k + 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ)))))
      (1 - Real.exp (-(1 - s))) := by
  exact SourceRunner.discreteTradeoff_converges_along_slab_fractions slab s hfraction

/-- The occurrence-indexed discrete runner uses the exact `bid * psi_k(current slab)` scan. -/
theorem section3_discrete_balance_algorithm
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (S : SourceRunner.OccurrenceState Advertiser Query)
    (q : Query) (a : Advertiser)
    (hchoice : (SourceRunner.discreteBalanceScan k hk I S q).winner = some a) :
    SourceRunner.occurrenceDiscreteBalanceChoice k hk I S q a := by
  exact section3_discrete_balance_choice_rule k hk I S q a hchoice

/-- Equal positive bids make a discrete-score winner the earliest feasible slab (BALANCE). -/
theorem section3_equal_bid_discrete_msvv_is_balance
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (S : SourceRunner.OccurrenceState Advertiser Query) (q : Query)
    (a : Advertiser) {commonBid : ℝ}
    (hcommon : ∀ b, I.bid b q = commonBid) (hcommon_pos : 0 < commonBid)
    (hchoice : (SourceRunner.discreteBalanceScan k hk I S q).winner = some a) :
    SourceRunner.occurrenceCanAssign I S q a ∧
      ∀ b, SourceRunner.occurrenceCanAssign I S q b →
        SourceRunner.activeBudgetSlab k hk (S.spent a) (I.budget a) ≤
          SourceRunner.activeBudgetSlab k hk (S.spent b) (I.budget b) := by
  exact SourceRunner.equal_bid_discrete_winner_has_earliest_slab
    k hk I S q a hcommon hcommon_pos hchoice

/-- Actual cost-threaded runtime bound for `M` arrivals and `N` advertisers. -/
theorem section3_balance_occurrence_runner_cost
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query) (history : List Query) :
    (SourceRunner.runBalanceOccurrences I history).candidateTests =
        history.length * Fintype.card Advertiser ∧
      (SourceRunner.runBalanceOccurrences I history).scoreComparisons ≤
        history.length * Fintype.card Advertiser := by
  exact ⟨SourceRunner.runBalanceOccurrences_candidateTests I history,
    SourceRunner.runBalanceOccurrences_scoreComparisons_le I history⟩

/-- Ratio attained by the two-word greedy construction after its first bidder is exhausted. -/
noncomputable def section3GreedyTwoWordRatio (c epsilon : ℝ) : ℝ :=
  (c + epsilon) / (2 * c + epsilon)

/--
The forced-greedy example approaches the tight ratio `1/2` as epsilon vanishes.
Source status: direct paper example
-/
theorem section3_greedy_tight_half_example
    {c : ℝ} (hc : 0 < c) :
    Filter.Tendsto (fun epsilon : ℝ => section3GreedyTwoWordRatio c epsilon)
      (nhds 0) (nhds (1 / 2 : ℝ)) := by
  have hcont :
      ContinuousAt (fun epsilon : ℝ => (c + epsilon) / (2 * c + epsilon)) 0 := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · nlinarith
  have hvalue : (c + 0) / (2 * c + 0) = (1 / 2 : ℝ) := by
    field_simp [ne_of_gt hc]
    ring
  change Filter.Tendsto
    (fun epsilon : ℝ => (c + epsilon) / (2 * c + epsilon))
    (nhds 0) (nhds (1 / 2 : ℝ))
  rw [← hvalue]
  exact hcont.tendsto

/--
The source's two-word small-bid construction has the stated online and offline
revenues before the limiting argument is applied.
-/
theorem section3_greedy_two_word_fluid_construction
    {c epsilon : ℝ} (hc : 0 < c) (hepsilon : 0 < epsilon) :
    c < c + epsilon ∧
      SourceRunner.greedyTwoWordOnlineRevenue c epsilon = 1 ∧
      SourceRunner.greedyTwoWordOfflineRevenue c epsilon =
        1 + c / (c + epsilon) ∧
      c / (c + epsilon) ≤ 1 ∧
      SourceRunner.greedyTwoWordOnlineRevenue c epsilon /
          SourceRunner.greedyTwoWordOfflineRevenue c epsilon =
        section3GreedyTwoWordRatio c epsilon := by
  simpa [section3GreedyTwoWordRatio] using
    SourceRunner.greedyTwoWordFluidOutcome_fields hc hepsilon

/-! ### Section 4 accounting -/

/--
Final type `i+1` is the right-closed interval `(i/k,(i+1)/k]`, with zero in type one.
Source status: direct paper definition
-/
theorem section4_bidder_type_definition
    (k : ℕ) (spentFraction : ℝ) (i : Fin k) :
    SourceRunner.IsFinalType k spentFraction i ↔
      (spentFraction = 0 ∧ i.val = 0) ∨
        ((i.val : ℝ) / (k : ℝ) < spentFraction ∧
          spentFraction ≤ (((i.val + 1 : ℕ) : ℝ) / (k : ℝ))) := by
  rfl

/--
`x_i` counts the bidders whose final spent fraction has type `i+1`.
Source status: direct paper definition
-/
theorem section4_type_count_x_definition
    {Advertiser : Type*} [Fintype Advertiser]
    (k : ℕ) (finalSpentFraction : Advertiser → ℝ) (i : Fin k) :
    SourceRunner.section4TypeCount k finalSpentFraction i =
      ∑ a : Advertiser,
        if SourceRunner.IsFinalType k (finalSpentFraction a) i then 1 else 0 := by
  rfl

/--
The idealized slab expenditure is `N/k` minus the earlier-type count divided by `k`.
Source status: direct paper formula
-/
theorem section4_slab_spend_beta_formula
    {k : ℕ} (N : ℝ) (x : Fin k → ℝ) (i : Fin k) :
    SourceRunner.section4IdealizedSlabSpend N x i =
      N / (k : ℝ) - (∑ j ∈ Finset.Iio i, x j) / (k : ℝ) := by
  rfl

/--
The stated per-bidder rounding premise aggregates to total error at most `N/k`.
Source status: direct paper sufficiently-small-bids approximation claim
-/
theorem section4_discretization_error_bound
    {Advertiser : Type*} [Fintype Advertiser]
    {k : ℕ} (hk : 0 < k) (error : Advertiser → ℝ)
    (herror_nonneg : ∀ a, 0 ≤ error a)
    (herror : ∀ a, error a ≤ 1 / (k : ℝ)) :
    ∑ a : Advertiser, error a ≤
      (Fintype.card Advertiser : ℝ) / (k : ℝ) := by
  exact SourceRunner.section4_discretization_error_le_N_div_k
    hk error herror_nonneg herror

/--
The displayed lower bound `BAL >= N-Phi-N/k`.
Source status: direct paper formula
-/
theorem section4_balance_revenue_factor_lp_bridge_formula
    {k : ℕ} (N BAL Φ : ℝ)
    (hBAL : N - BAL ≤ Φ + N / (k : ℝ)) :
    N - Φ - N / (k : ℝ) ≤ BAL := by
  exact SourceRunner.section4_balance_revenue_factor_lp_bridge N BAL Φ hBAL

/--
All rows of the displayed factor LP are tight at the geometric witness and its
objective has the claimed finite value.  This is the formalized mathematical
content used by the cited KP00 tight construction; MSVV07 does not print that
external construction, so this row does not misattribute its incidence data to
the journal text.
-/
theorem section4_all_factor_lp_rows_tight
    {m : ℕ} (N : ℝ) :
    (∀ i : Fin m,
      MSVV07SourceLemmas.paperRouteLPRow
          (MSVV07SourceLemmas.paperRoutePrimalCandidate (m := m) N) i =
        MSVV07SourceLemmas.paperRouteRhs N i) ∧
      MSVV07SourceLemmas.paperRoutePrimalObjective
          (MSVV07SourceLemmas.paperRoutePrimalCandidate (m := m) N) =
        MSVV07SourceLemmas.factorRevealingLPValue m N := by
  exact ⟨MSVV07SourceLemmas.paperRoutePrimalCandidate_row_tight N,
    MSVV07SourceLemmas.paperRoutePrimalCandidate_objective_value N⟩

/--
The Section 4 geometric witness is realized by one cohort-fluid BALANCE
execution: its active-mass drops are the final-type counts, every active bidder
has the same slab state and increment, every slab is work-conserving, all LP
rows are tight for those realized counts, and revenue is total budget minus the
realized unspent-budget objective.  Its unit-budget execution tends to
`1 - 1/e`.  This is a corrected, internal limiting witness: MSVV07 itself
cites an external KP00 exact finite instance rather than printing it.
Source status: corrected source target; external exact witness not reconstructed
-/
theorem section4_balance_exact_tightness_instance
    (m : ℕ) (N : ℝ) (hN : 0 ≤ N) :
    let E := SourceRunner.factorLPTightFluidExecution m N
    (∀ i, 0 ≤ E.typeMass i) ∧
    (∀ i : Fin m,
      E.activeMassBeforeSlab i.val - E.activeMassBeforeSlab (i.val + 1) =
        E.typeMass i) ∧
    (∀ stage, stage ≤ m →
      E.spentBeforeSlab stage = (stage : ℝ) / ((m + 1 : ℕ) : ℝ) ∧
      E.allocationPerActiveBidder stage =
        1 / ((m + 1 : ℕ) : ℝ) ∧
      E.queryMassAtSlab stage =
        E.activeMassBeforeSlab stage / ((m + 1 : ℕ) : ℝ) ∧
      (stage < m →
        E.spentBeforeSlab (stage + 1) =
          E.spentBeforeSlab stage + E.allocationPerActiveBidder stage) ∧
      E.spentBeforeSlab stage + E.allocationPerActiveBidder stage ≤ 1 ∧
      E.activeMassBeforeSlab stage * E.allocationPerActiveBidder stage =
        E.queryMassAtSlab stage) ∧
    (∑ i : Fin m, E.typeMass i) + E.fullMass = N ∧
    (∀ i,
      MSVV07SourceLemmas.paperRouteLPRow E.typeMass i =
        MSVV07SourceLemmas.paperRouteRhs N i) ∧
    E.revenue =
      (∑ i : Fin m,
        E.typeMass i * SourceRunner.factorLPTightFinalSpendFraction m i) +
        E.fullMass ∧
    E.revenue =
      ∑ stage ∈ Finset.range (m + 1),
        E.activeMassBeforeSlab stage * E.allocationPerActiveBidder stage ∧
    E.revenue = N - MSVV07SourceLemmas.factorRevealingLPValue m N ∧
    Sequence.SeqTendsTo
      (fun r : ℕ => (SourceRunner.factorLPTightFluidExecution r 1).revenue)
      paperMsvvRatio := by
  let E := SourceRunner.factorLPTightFluidExecution m N
  refine ⟨?_, E.active_mass_drop_eq_typeMass, ?_, E.type_mass_partition,
    E.lp_rows_realized_tight, E.revenue_from_final_types,
    E.revenue_from_slab_allocations,
    E.revenue_eq_N_sub_lpValue, ?_⟩
  · intro i
    rw [E.typeMass_eq_candidate]
    exact MSVV07SourceLemmas.paperRoutePrimalCandidate_nonnegative hN i
  · intro stage hstage
    exact ⟨E.equal_least_spend_state stage hstage,
      E.equal_allocation_increment stage hstage,
      E.query_mass_formula stage hstage,
      fun hlt => E.state_update stage hlt,
      E.budget_feasible stage hstage,
      E.slab_work_conservation stage hstage⟩
  · exact SourceRunner.factorLPTightFluidRevenue_tendsTo_msvvRatio

/-! ### Section 5 definitions and intermediate formulas -/

/--
Section 5 uses the same final-type definition for arbitrary bids.
Source status: direct paper definition
-/
theorem section5_bidder_type_definition
    (k : ℕ) (spentFraction : ℝ) (i : Fin k) :
    SourceRunner.IsFinalType k spentFraction i ↔
      (spentFraction = 0 ∧ i.val = 0) ∨
        ((i.val : ℝ) / (k : ℝ) < spentFraction ∧
          spentFraction ≤ (((i.val + 1 : ℕ) : ℝ) / (k : ℝ))) := by
  rfl

/-- Explicit predicate for the temporary exact-type-spend simplification. -/
def section5ExactTypeSpend
    (k : ℕ) (spentFraction : Advertiser → ℝ)
    (finalType : Advertiser → Fin k) : Prop :=
  ∀ a, spentFraction a = (((finalType a).val + 1 : ℕ) : ℝ) / (k : ℝ)

theorem section5_exact_type_spend_simplifying_assumption
    (k : ℕ) (spentFraction : Advertiser → ℝ)
    (finalType : Advertiser → Fin k) :
    section5ExactTypeSpend k spentFraction finalType ↔
      ∀ a, spentFraction a =
        (((finalType a).val + 1 : ℕ) : ℝ) / (k : ℝ) := by
  rfl

theorem section5_alpha_type_count_definition
    {Advertiser : Type*} [Fintype Advertiser]
    (k : ℕ) (finalSpentFraction : Advertiser → ℝ) (i : Fin k) :
    SourceRunner.section5AlphaTypeCount k finalSpentFraction i =
      SourceRunner.section4TypeCount k finalSpentFraction i := by
  rfl

theorem section5_beta_slab_spend_definition
    {k : ℕ} (N : ℝ) (alpha : Fin k → ℝ) (i : Fin k) :
    SourceRunner.section5IdealizedBeta N alpha i =
      N / (k : ℝ) - (∑ j ∈ Finset.Iio i, alpha j) / (k : ℝ) := by
  rfl

theorem section5_delta_prefix_definition
    {k : ℕ} (alpha beta : Fin k → ℝ) (i : Fin k) :
    SourceRunner.section5Delta alpha beta i =
      ∑ j ∈ Finset.Iic i, (alpha j - beta j) := by
  rfl

theorem section5_alg_query_revenue_definition
    (I : PaperInstance Advertiser Query)
    (d : SourceRunner.OccurrenceDecision Advertiser Query) :
    SourceRunner.section5AlgQueryRevenue I d =
      match d.winner with
      | none => 0
      | some a => I.bid a d.query := by
  rfl

theorem section5_opt_query_revenue_definition
    (I : PaperInstance Advertiser Query) (history : List Query)
    (opt : Fin history.length → Option Advertiser) (t : Fin history.length) :
    SourceRunner.section5OptQueryRevenue I history opt t =
      match opt t with
      | none => 0
      | some a => I.bid a (history.get t) := by
  rfl

theorem section5_query_type_definition
    (optOwner : Option Advertiser) (finalType : Advertiser → Fin k) :
    SourceRunner.section5QueryType optOwner finalType = optOwner.map finalType := by
  rfl

theorem section5_query_slab_definition
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (d : SourceRunner.OccurrenceDecision Advertiser Query) :
    SourceRunner.section5QuerySlab k hk I d =
      d.winner.map fun a =>
        SourceRunner.activeBudgetSlab k hk (d.spentBefore a) (I.budget a) := by
  rfl

theorem section5_type_fiber_alpha_accounting_formula
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    {k : ℕ} (I : PaperInstance Advertiser Query) (history : List Query)
    (opt : Fin history.length → Option Advertiser)
    (finalType : Advertiser → Fin k)
    (hexhaust : ∀ a, SourceRunner.occurrenceSpend I history opt a = 1)
    (i : Fin k) :
    SourceRunner.section5OptTypeFiberRevenue I history opt finalType i =
      ∑ a : Advertiser, if finalType a = i then 1 else 0 := by
  exact SourceRunner.section5_opt_type_fiber_revenue_eq_type_count
    I history opt finalType hexhaust i

theorem section5_slab_fiber_beta_accounting_formula
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (decisions : List (SourceRunner.OccurrenceDecision Advertiser Query))
    (i : Fin k) :
    SourceRunner.section5AlgSlabFiberRevenue k hk I decisions i =
      (decisions.map fun d =>
        if SourceRunner.section5QuerySlab k hk I d = some i then
          SourceRunner.section5AlgQueryRevenue I d
        else 0).sum := by
  rfl

/--
Theorem 8's finite summation-by-parts identity.
Source status: direct paper formula
-/
theorem theorem8_delta_dual_suffix_identity
    {m : ℕ} (alpha beta y : Fin m → ℝ) :
    (∑ i : Fin m, y i * MSVV07SourceLemmas.paperRouteDelta alpha beta i) =
      ∑ i : Fin m,
        MSVV07SourceLemmas.paperRoutePsiFromDual y i * (alpha i - beta i) := by
  exact MSVV07SourceLemmas.theorem8_delta_dot_y_eq_weighted_perturbation
    alpha beta y

theorem theorem8_simple_proof_beta_recurrence_formula
    {k : ℕ} (N : ℝ) (alpha : Fin k → ℝ) (i : Fin k) :
    SourceRunner.section5IdealizedBeta N alpha i =
      N / (k : ℝ) - (∑ j ∈ Finset.Iio i, alpha j) / (k : ℝ) := by
  rfl

/-- The exact weighted alpha-beta inequality used in the simple proof. -/
def theorem8WeightedAlphaBeta
    {k : ℕ} (psi alpha beta : Fin k → ℝ) : Prop :=
  (∑ i : Fin k, psi i * alpha i) ≤ ∑ i : Fin k, psi i * beta i

theorem theorem8_simple_proof_weighted_alpha_beta_inequality
    {k : ℕ} (psi alpha beta : Fin k → ℝ) :
    theorem8WeightedAlphaBeta psi alpha beta ↔
      (∑ i : Fin k, psi i * alpha i) ≤ ∑ i : Fin k, psi i * beta i := by
  rfl

/--
The simple proof's final algebra: a `(1-1/e)` revenue lower bound with additive
error is equivalent to an `N/e` upper bound on unspent budget with the same
error.  Applying this row to the vanishing finite error in the configured
Theorem 8 family gives the stated limiting conclusion.
Source status: direct paper proof conclusion
-/
theorem theorem8_unspent_budget_bound_formula
    (N revenue error : ℝ)
    (hcompetitive : paperMsvvRatio * N ≤ revenue + error) :
    N - revenue ≤ N / Real.exp 1 + error := by
  unfold paperMsvvRatio at hcompetitive
  ring_nf at hcompetitive ⊢
  linarith

/-! ### Section 6 generalized accounting -/

/--
The current type is computed from the bidder's current spent-budget fraction.
Source status: direct paper definition
-/
theorem section6_current_type_definition
    (k : ℕ) (hk : 0 < k) (spent budget : ℝ) :
    SourceRunner.section6CurrentType k hk spent budget =
      SourceRunner.activeBudgetSlab k hk spent budget := by
  rfl

/-
The source's generalized Section 6 rule is an occurrence-level rule: on each
arrival it selects a feasible advertiser maximizing `bid * psi_k(current
type)`.  Stating the scan expansion, rather than merely its recursive runner,
keeps repeated occurrences in scope.
Source status: direct paper algorithm definition
-/
theorem section6_generalized_current_type_balance_algorithm
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (S : SourceRunner.OccurrenceState Advertiser Query) (q : Query)
    (a : Advertiser)
    (hchoice : (SourceRunner.discreteBalanceScan k hk I S q).winner = some a) :
    SourceRunner.occurrenceDiscreteBalanceChoice k hk I S q a := by
  exact SourceRunner.discreteBalanceScan_winner_is_discrete_choice
    k hk I S q a hchoice

theorem section6_beta_ij_definition
    {Advertiser Query : Type*}
    (k : ℕ) (I : PaperInstance Advertiser Query)
    (finalSpend : Advertiser → ℝ)
    (i : Fin k) (a : Advertiser) :
    SourceRunner.section6BidderSlabSpend k I finalSpend i a =
      min (finalSpend a) (SourceRunner.section6SlabUpper k I i a) -
        min (finalSpend a) (SourceRunner.section6SlabLower k I i a) := by
  rfl

theorem section6_beta_i_aggregate_definition
    {Advertiser Query : Type*} [Fintype Advertiser]
    (k : ℕ) (I : PaperInstance Advertiser Query)
    (finalSpend : Advertiser → ℝ)
    (i : Fin k) :
    SourceRunner.section6AggregateSlabSpend k I finalSpend i =
      ∑ a : Advertiser,
        SourceRunner.section6BidderSlabSpend k I finalSpend i a := by
  rfl

theorem section6_alpha_i_definition
    (I : PaperInstance Advertiser Query) (history : List Query)
    (opt : Fin history.length → Option Advertiser)
    (finalType : Advertiser → Fin k) (i : Fin k) :
    SourceRunner.section6OptRevenueByFinalType I history opt finalType i =
      ∑ t : Fin history.length,
        match opt t with
        | none => 0
        | some a => if finalType a = i then I.bid a (history.get t) else 0 := by
  rfl

theorem section6_alpha_total_definition
    (I : PaperInstance Advertiser Query) (history : List Query)
    (opt : Fin history.length → Option Advertiser)
    (finalType : Advertiser → Fin k) :
    SourceRunner.section6OptRevenueTotalByType I history opt finalType =
      SourceRunner.occurrenceRevenue I history opt := by
  exact SourceRunner.section6_alpha_total_eq_occurrenceRevenue
    I history opt finalType

/-- Exact predicate for Section 6's per-slab lower bounds. -/
def section6BetaLowerBounds
    {k : ℕ} (alphaTotal : ℝ) (alpha beta : Fin k → ℝ) : Prop :=
  ∀ i, (alphaTotal - ∑ j ∈ Finset.Iic i, alpha j) / (k : ℝ) ≤ beta i

theorem section6_beta_lower_bound_formula
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    {k : ℕ} (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (history : List Query)
    (opt : Fin history.length → Option Advertiser)
    (finalType : Advertiser → Fin k)
    (hbudget : I.PositiveBudgets)
    (hoptFeasible : ∀ a,
      SourceRunner.occurrenceSpend I history opt a ≤ I.budget a)
    (hfinalType : ∀ a,
      SourceRunner.IsFinalType k
        ((SourceRunner.runDiscreteBalanceOccurrences k hk I history).spent a /
          I.budget a)
        (finalType a)) :
    section6BetaLowerBounds
      (SourceRunner.section6OptRevenueTotalByType I history opt finalType)
      (SourceRunner.section6OptRevenueByFinalType I history opt finalType)
      (SourceRunner.section6AggregateSlabSpend k I
        (SourceRunner.runDiscreteBalanceOccurrences k hk I history).spent) := by
  exact
    SourceRunner.section6_beta_lower_bound_from_opt_feasibility_and_final_types
      hk I history opt
      (SourceRunner.runDiscreteBalanceOccurrences k hk I history).spent
      finalType hbudget hoptFeasible hfinalType

theorem section6_weighted_alpha_beta_inequality
    {m Query : Type*} [Fintype m] [Fintype Query]
    (psi alpha beta : m → ℝ) (opt alg : Query → ℝ)
    (queryType querySlab : Query → m)
    (htradeoff_sum :
      (∑ q : Query,
        (opt q * psi (queryType q) - alg q * psi (querySlab q))) ≤ 0)
    (hopt_accounting :
      (∑ q : Query, opt q * psi (queryType q)) =
        ∑ i : m, psi i * alpha i)
    (halg_accounting :
      (∑ q : Query, alg q * psi (querySlab q)) ≤
        ∑ i : m, psi i * beta i) :
    (∑ i : m, psi i * alpha i) ≤ ∑ i : m, psi i * beta i := by
  exact SourceRunner.section6_weighted_alpha_beta_of_query_accounting
    psi alpha beta opt alg queryType querySlab
    htradeoff_sum hopt_accounting halg_accounting

theorem section6_next_highest_alive_keep_alive_reduction
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query) (a : Advertiser) (q : Query) :
    Proof.section6_next_highest_bid_alive I (fun _ _ => True) a q =
      Proof.section6_next_highest_bid_all I a q := by
  exact SourceRunner.section6_all_alive_next_price_reduces_to_all_bidders I a q

/-! ### Section 8 proposals (definitions only; guarantees remain open) -/

theorem section8_switching_query_distribution_model
    (M : SourceRunner.SwitchingQueryDistribution Time Regime Query)
    (switchCount : ℕ) (periodAt : Time → Fin (switchCount + 1))
    (regimeForPeriod : Fin (switchCount + 1) → Regime)
    (hadversarial_schedule :
      ∀ time, M.regimeAt time = regimeForPeriod (periodAt time)) :
    (∀ time,
      M.queryDistributionAt time =
        M.queryDistribution (regimeForPeriod (periodAt time))) ∧
      (∀ time₁ time₂, periodAt time₁ = periodAt time₂ →
        M.queryDistributionAt time₁ = M.queryDistributionAt time₂) := by
  constructor
  · intro time
    simp only [SourceRunner.SwitchingQueryDistribution.queryDistributionAt,
      hadversarial_schedule]
  · intro time₁ time₂ hperiod
    simp only [SourceRunner.SwitchingQueryDistribution.queryDistributionAt,
      hadversarial_schedule]
    rw [hperiod]

theorem section8_weighted_bid_algorithm_proposal
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query) (weight : Advertiser → ℝ)
    (history : List Query) :
    SourceRunner.runWeightedBidProposal I weight history =
      SourceRunner.runBalanceOccurrences (I.withAdvertiserWeights weight) history := by
  rfl

theorem section8_online_weight_adjustment_heuristic
    (weight finalWeight : ℝ) (windows : List (ℝ × ℝ)) :
    SourceRunner.IsRepeatedWeightAdjustment weight windows finalWeight ↔
      match windows with
      | [] => finalWeight = weight
      | (spent, fairShare) :: remaining =>
          ∃ nextWeight,
            SourceRunner.IsWeightAdjustment
              weight spent fairShare nextWeight ∧
              SourceRunner.IsRepeatedWeightAdjustment
                nextWeight remaining finalWeight := by
  cases windows <;> rfl

theorem section8_online_weight_adjustment_heuristic_exists
    (weight : ℝ) (windows : List (ℝ × ℝ)) :
    ∃ finalWeight,
      SourceRunner.IsRepeatedWeightAdjustment weight windows finalWeight := by
  exact SourceRunner.exists_repeated_weight_adjustment weight windows

theorem section8_replicated_ranking_algorithm_proposal
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (m : ℕ) (hm : 0 < m) (I : PaperInstance Advertiser Query)
    (rank : SourceRunner.Representative Advertiser m → ℕ)
    (rankScale : ℕ → ℝ)
    (rankWeight : SourceRunner.Representative Advertiser m → ℝ)
    (history : List Query)
    (hrank_injective : Function.Injective rank)
    (hrank_weight : ∀ r, rankWeight r = rankScale (rank r)) :
    (∀ r : SourceRunner.Representative Advertiser m,
        (SourceRunner.replicatedInstance m I).budget r =
          I.budget r.1 / (m : ℝ)) ∧
      (∀ (r : SourceRunner.Representative Advertiser m) (q : Query),
        (SourceRunner.replicatedInstance m I).bid r q = I.bid r.1 q ∧
          SourceRunner.replicatedRankingScore I rankWeight r q =
            I.bid r.1 q * rankScale (rank r)) ∧
      SourceRunner.runReplicatedRankingProposal m I rankWeight history =
        SourceRunner.runOccurrencesFrom
          (SourceRunner.replicatedRankingStep m I rankWeight)
          SourceRunner.initialOccurrenceState history := by
  exact ⟨fun _ => rfl, fun r q => ⟨rfl, by simp [SourceRunner.replicatedRankingScore,
      hrank_weight r]⟩, rfl⟩

/-! ### Theorem 9's intermediate source formulas -/

theorem theorem9_hard_instance_round_bids_and_optimum
    (N m : ℕ) (epsilon : ℝ) (permutation : Equiv.Perm (Fin N))
    (hround : (m : ℝ) * epsilon = 1) :
    (∀ round bidder,
      SourceRunner.theorem9RoundBid N epsilon permutation round bidder =
        if (round : ℕ) ≤ (bidder : ℕ) then epsilon else 0) ∧
      paperRevenue (SourceRunner.theorem9HardInstance N m epsilon permutation)
          (SourceRunner.theorem9HardOfflineAssignment N m permutation) = (N : ℝ) := by
  exact ⟨fun round bidder =>
      SourceRunner.theorem9RoundBid_formula N epsilon permutation round bidder,
    SourceRunner.theorem9HardOfflineAssignment_revenue_eq_N
      N m epsilon permutation hround⟩

theorem theorem9_expected_round_allocation_bound
    (N : ℕ) (algorithm : BMatchingIntegralPrefixAlgorithm N)
    (round bidder : Fin N) :
    (SourceRunner.theorem9ExpectedRoundAllocation N algorithm round bidder ≤
      if (round : ℕ) ≤ (bidder : ℕ) then
        1 / ((N - (round : ℕ) : ℕ) : ℝ)
      else 0) ∧
      (¬ (round : ℕ) ≤ (bidder : ℕ) →
        SourceRunner.theorem9ExpectedRoundAllocation
          N algorithm round bidder = 0) := by
  exact
    ⟨SourceRunner.theorem9_expected_round_allocation_bound
        N algorithm round bidder,
      SourceRunner.theorem9_expected_round_allocation_zero_of_ineligible
        N algorithm round bidder⟩

theorem theorem9_harmonic_spend_and_revenue_bound
    (N : ℕ) (algorithm : BMatchingIntegralPrefixAlgorithm N)
    (bidder : Fin N) :
    theorem9BidderSpendUpperBound N bidder =
        min 1
          (∑ round : Fin N,
            if (round : ℕ) ≤ (bidder : ℕ) then
              1 / ((N - (round : ℕ) : ℕ) : ℝ)
            else 0) ∧
      min 1
          (∑ round : Fin N,
            SourceRunner.theorem9ExpectedRoundAllocation
              N algorithm round bidder) ≤
        theorem9BidderSpendUpperBound N bidder ∧
      theorem9NormalizedRevenueUpperBound N =
        (∑ b : Fin N, theorem9BidderSpendUpperBound N b) / (N : ℝ) ∧
      pmfExp (uniformPermutationDistribution N)
          (fun permutation =>
            (SourceRunner.theorem9IntegralRoundCertificate N).normalizedRevenue
              algorithm permutation) ≤
        theorem9NormalizedRevenueUpperBound N ∧
      ∀ delta : ℝ, 0 < delta →
        ∃ N0 : ℕ, ∀ marketSize : ℕ, N0 ≤ marketSize →
          theorem9NormalizedRevenueUpperBound marketSize ≤
            paperMsvvRatio + delta := by
  exact
    ⟨SourceRunner.theorem9_harmonic_spend_formula N bidder,
      SourceRunner.theorem9_expected_bidder_spend_le_harmonic_bound
        N algorithm bidder,
      SourceRunner.theorem9_harmonic_revenue_formula N,
      SourceRunner.theorem9_expected_normalized_revenue_le_harmonic_bound
        N algorithm,
      Proof.theorem9_harmonic_eventually_le_msvv_ratio_add_delta⟩

/--
The unpermuted nested-round base instance's equal-spread BALANCE calculation is
the capped harmonic revenue expression and is eventually at most
`1 - 1/e + delta`.  This formalizes the finite calculation underlying the
paper's informal "one can show" sentence.
-/
theorem theorem9_base_instance_balance_revenue_claim :
    ∀ delta : ℝ, 0 < delta →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        SourceRunner.theorem9BaseEqualSpreadBalanceRevenue N / (N : ℝ) ≤
          paperMsvvRatio + delta := by
  simpa [paperMsvvRatio, Proof.paperMsvvRatio, AdWordsInstance.msvvRatio] using
    SourceRunner.theorem9_base_equal_spread_balance_eventually_le_msvvRatio_add

/--
The concrete `m`-occurrence hard family has exactly the unit round-bid masses
used by the fluid BALANCE execution when every occurrence has bid `1/m`, while
the individual bid size tends to zero.  The same certificate exposes the
allocation-derived state, least-spend choice rule, unit budgets, and
no-discard-unless-saturated rule of that limiting execution.
-/
theorem theorem9_base_instance_small_bids_fluid_bridge (N : ℕ) :
    let F := SourceRunner.theorem9NestedSuffixBalanceFluidLimit N
    (∀ m : ℕ, 0 < m → ∀ round bidder : Fin N,
      (∑ copy : Fin m,
        (SourceRunner.theorem9HardInstance N m (1 / (m : ℝ))
          (Equiv.refl (Fin N))).bid bidder (round, copy)) =
        SourceRunner.theorem9HardFluidRoundMass N round bidder) ∧
    Filter.Tendsto (fun m : ℕ => (1 / (m : ℝ) : ℝ))
      Filter.atTop (nhds 0) ∧
    (∀ round bidder : Fin N,
      Filter.Tendsto
        (fun m : ℕ =>
          ∑ copy : Fin (m + 1),
            (SourceRunner.theorem9HardInstance N (m + 1)
              (1 / ((m + 1 : ℕ) : ℝ)) (Equiv.refl (Fin N))).bid
                bidder (round, copy))
        Filter.atTop
        (nhds (SourceRunner.theorem9HardFluidRoundMass N round bidder))) ∧
    (∀ round bidder,
      SourceRunner.theorem9HardFluidRoundMass N round bidder = 0 →
        F.execution.allocation round bidder = 0) ∧
    (∀ round bidder bidder',
      SourceRunner.theorem9HardFluidRoundMass N round bidder = 1 →
      SourceRunner.theorem9HardFluidRoundMass N round bidder' = 1 →
        F.execution.spentBefore round bidder =
          F.execution.spentBefore round bidder') ∧
    (∀ round bidder,
      F.execution.spentBefore round bidder =
        ∑ previous : Fin N,
          if (previous : ℕ) < (round : ℕ) then
            F.execution.allocation previous bidder
          else 0) ∧
    (∀ round bidder,
      F.execution.spentBefore round bidder +
        F.execution.allocation round bidder ≤ 1) ∧
    (∀ round,
      (∑ bidder ∈ theorem9EligibleBidders N round,
        F.execution.allocation round bidder) = 1 ∨
      ∀ bidder, bidder ∈ theorem9EligibleBidders N round →
        F.execution.spentBefore round bidder +
          F.execution.allocation round bidder = 1) ∧
    ∀ bidder,
      F.execution.finalSpend bidder =
        ∑ round : Fin N, F.execution.allocation round bidder := by
  let F := SourceRunner.theorem9NestedSuffixBalanceFluidLimit N
  exact ⟨F.finite_round_bid_mass, F.bid_size_tendsto_zero,
    F.finite_round_bid_mass_tendsto,
    F.allocation_zero_of_zero_round_mass, F.eligible_equal_least_spend,
    F.spentBefore_eq_prior_allocations, F.budget_feasible,
    F.work_conserving_or_saturated, F.finalSpend_eq_sum⟩

/--
Construction-level invariants and harmonic payoff of the fluid base-instance execution.
Source status: derived execution supporting the direct Theorem 9 base-instance claim
-/
theorem theorem9_base_instance_balance_execution_fields (N : ℕ) :
    let E := SourceRunner.nestedSuffixFluidBalanceExecution N
    (∀ (round bidder : Fin N),
      ¬ (round : ℕ) ≤ (bidder : ℕ) → E.allocation round bidder = 0) ∧
    (∀ (round bidder bidder' : Fin N),
      (round : ℕ) ≤ (bidder : ℕ) →
      (round : ℕ) ≤ (bidder' : ℕ) →
        E.spentBefore round bidder = E.spentBefore round bidder') ∧
    (∀ (round bidder : Fin N),
      E.spentBefore round bidder + E.allocation round bidder ≤ 1) ∧
    (∀ (round bidder : Fin N),
      E.spentBefore round bidder =
        ∑ previous : Fin N,
          if (previous : ℕ) < (round : ℕ) then
            E.allocation previous bidder
          else 0) ∧
    (∀ (round next bidder : Fin N),
      (next : ℕ) = (round : ℕ) + 1 →
        E.spentBefore next bidder =
          E.spentBefore round bidder + E.allocation round bidder) ∧
    (∀ (round : Fin N),
      (∑ bidder ∈ theorem9EligibleBidders N round,
        E.allocation round bidder) ≤ 1) ∧
    (∀ (round : Fin N),
      (∑ bidder ∈ theorem9EligibleBidders N round,
        E.allocation round bidder) = 1 ∨
      ∀ bidder : Fin N, bidder ∈ theorem9EligibleBidders N round →
        E.spentBefore round bidder + E.allocation round bidder = 1) ∧
    (∀ bidder : Fin N,
      E.finalSpend bidder = theorem9BidderSpendUpperBound N bidder) ∧
    SourceRunner.theorem9BaseEqualSpreadBalanceRevenue N / (N : ℝ) =
      theorem9NormalizedRevenueUpperBound N := by
  let E := SourceRunner.nestedSuffixFluidBalanceExecution N
  refine ⟨E.zero_of_ineligible, E.eligible_equal_least_spend,
    E.budget_feasible, E.spentBefore_eq_prefix, E.state_update,
    E.round_conservation, E.work_conserving_or_saturated, ?_,
    SourceRunner.theorem9BaseEqualSpreadBalanceRevenue_normalized N⟩
  intro bidder
  exact SourceRunner.fluidBalance_finalSpend_eq_harmonicCap N bidder

/-- Transparent v11 semantic target for `paperSlotsPerPageDistinct_iff`. -/
def paperSlotsPerPageDistinct_iffSpec
    {Advertiser Query : Type*} (Slot : Query → Type*)
    (A : PaperAssignment Advertiser (Σ q : Query, Slot q)) : Prop :=
  paperSlotsPerPageDistinct Slot A ↔
    ∀ q s₁ s₂ a,
      A ⟨q, s₁⟩ = some a →
      A ⟨q, s₂⟩ = some a →
      s₁ = s₂

/-- Transparent v11 semantic target for `paperSpend_formula`. -/
def paperSpend_formulaSpec
    {Advertiser Query : Type*} [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) (a : Advertiser) : Prop :=
  paperSpend I A a =
    ∑ q : Query,
      match A q with
      | none => 0
      | some a' => if a' = a then I.bid a q else 0

/-- Transparent v11 semantic target for `paperRevenue_formula`. -/
def paperRevenue_formulaSpec
    {Advertiser Query : Type*} [Fintype Query]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) : Prop :=
  paperRevenue I A =
    ∑ q : Query,
      match A q with
      | none => 0
      | some a => I.bid a q

/-- Transparent v11 semantic target for `paperFeasible_iff`. -/
def paperFeasible_iffSpec
    {Advertiser Query : Type*} [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) : Prop :=
  paperFeasible I A ↔ ∀ a, paperSpend I A a ≤ I.budget a

/-- Transparent v11 semantic target for `paperSmallBids_iff`. -/
def paperSmallBids_iffSpec
    {Advertiser Query : Type*}
    (I : PaperInstance Advertiser Query) (epsilon : ℝ) : Prop :=
  paperSmallBids I epsilon ↔ ∀ a q, I.bid a q ≤ epsilon * I.budget a

/-- Transparent v11 semantic target for `paperTradeoff_formula`. -/
def paperTradeoff_formulaSpec (s : ℝ) : Prop :=
  paperTradeoff s = 1 - Real.exp (s - 1)

/-- Transparent v11 semantic target for `section3_discrete_tradeoff_formula`. -/
def section3_discrete_tradeoff_formulaSpec (k : ℕ) (i : Fin k) : Prop :=
  paperDiscreteTradeoff k i =
    1 - Real.exp
      (-(1 - (((i.val + 1 : ℕ) : ℝ) / (k : ℝ))))

/-- Transparent v11 semantic target for `paperMsvvRatio_formula`. -/
def paperMsvvRatio_formulaSpec : Prop :=
  paperMsvvRatio = 1 - 1 / Real.exp 1

/-- Transparent v11 semantic target for `paperBalanceScore_formula`. -/
def paperBalanceScore_formulaSpec
    {Advertiser Query : Type*} [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) (a : Advertiser) (q : Query) : Prop :=
  paperBalanceScore I A a q =
    I.bid a q * paperTradeoff (paperSpend I A a / I.budget a)

/-- Transparent v11 semantic target for `paperCanAssign_iff`. -/
def paperCanAssign_iffSpec
    {Advertiser Query : Type*} [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) (q : Query) (a : Advertiser) : Prop :=
  paperCanAssign I A q a ↔
    paperSpend I A a + I.bid a q ≤ I.budget a

/-- Transparent v11 semantic target for `paperIsBalanceChoice_iff`. -/
def paperIsBalanceChoice_iffSpec
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) (q : Query) (a : Advertiser) : Prop :=
  paperIsBalanceChoice I A q a ↔
    paperCanAssign I A q a ∧
      ∀ b, paperCanAssign I A q b →
        paperBalanceScore I A b q ≤ paperBalanceScore I A a q

/-- Transparent v11 semantic target for `section4_factor_revealing_primal_dual_lp_formulas`. -/
def section4_factor_revealing_primal_dual_lp_formulasSpec
    {m : ℕ} (N : ℝ) (x y : Fin m → ℝ) : Prop :=
  (MSVV07SourceLemmas.factorRevealingLP m N).primalObjective x =
      MSVV07SourceLemmas.paperRoutePrimalObjective x ∧
    ((MSVV07SourceLemmas.factorRevealingLP m N).PrimalFeasible x ↔
      MSVV07SourceLemmas.paperRoutePrimalFeasible N x) ∧
    (MSVV07SourceLemmas.factorRevealingLP m N).dualObjective y =
      MSVV07SourceLemmas.paperRouteDualObjective N y ∧
    ((MSVV07SourceLemmas.factorRevealingLP m N).DualFeasible y ↔
      MSVV07SourceLemmas.paperRouteDualFeasible y)

/-- Transparent v11 semantic target for `section4_lemma3_displayed_primal_dual_witnesses_optimal`. -/
def section4_lemma3_displayed_primal_dual_witnesses_optimalSpec
    {m N : ℕ} : Prop :=
  Optimization.IsMaximizerOn
      (MSVV07SourceLemmas.paperRoutePrimalFeasible (m := m) (N : ℝ))
      (MSVV07SourceLemmas.paperRoutePrimalObjective (m := m))
      (MSVV07SourceLemmas.paperRoutePrimalCandidate (m := m) (N : ℝ)) ∧
    Optimization.IsMinimizerOn
      (MSVV07SourceLemmas.factorRevealingLP m (N : ℝ)).DualFeasible
      (MSVV07SourceLemmas.factorRevealingLP m (N : ℝ)).dualObjective
      (MSVV07SourceLemmas.paperRouteDualCandidate (m := m)) ∧
    MSVV07SourceLemmas.paperRoutePrimalObjective
        (MSVV07SourceLemmas.paperRoutePrimalCandidate (m := m) (N : ℝ)) =
      MSVV07SourceLemmas.factorRevealingLPValue m (N : ℝ) ∧
    MSVV07SourceLemmas.paperRouteDualObjective (N : ℝ)
        (MSVV07SourceLemmas.paperRouteDualCandidate (m := m)) =
      MSVV07SourceLemmas.factorRevealingLPValue m (N : ℝ)

/-- Transparent v11 semantic target for `section4_lemma1_balance_pays_no_later_slab`. -/
def section4_lemma1_balance_pays_no_later_slabSpec
    {Slab : Type*} [LinearOrder Slab]
    (psi : Slab → ℝ) {optType optCurrentSlab chosenSlab : Slab}
    {bid chosenBid : ℝ}
    (hoptCurrent_le_type : optCurrentSlab ≤ optType)
    (hchoice :
      bid * psi optCurrentSlab ≤ chosenBid * psi chosenSlab)
    (hequal_bids : chosenBid = bid)
    (hbid_pos : 0 < bid)
    (hpsi_strictAnti : StrictAnti psi) : Prop :=
  chosenSlab ≤ optType

/-- Transparent v11 semantic target for `section4_lemma2_factor_revealing_lp_constraint`. -/
def section4_lemma2_factor_revealing_lp_constraintSpec
    {m : ℕ} (N : ℝ) (x beta : Fin m → ℝ) (i : Fin m)
    (hprefix_cover :
      (∑ j ∈ MSVV07SourceLemmas.paperRoutePrefix i, x j) ≤
        ∑ j ∈ MSVV07SourceLemmas.paperRoutePrefix i, beta j)
    (hbeta_prefix :
      (∑ j ∈ MSVV07SourceLemmas.paperRoutePrefix i, beta j) =
        MSVV07SourceLemmas.paperRouteRhs N i -
          ∑ j ∈ MSVV07SourceLemmas.paperRoutePrefix i,
            MSVV07SourceLemmas.paperRouteDeltaCoeff i j * x j) : Prop :=
  MSVV07SourceLemmas.paperRouteLPRow x i ≤
    MSVV07SourceLemmas.paperRouteRhs N i

/-- Transparent v11 semantic target for `section4_lemma3_factor_revealing_lp_optimality`. -/
def section4_lemma3_factor_revealing_lp_optimalitySpec (N : ℝ) : Prop :=
  Sequence.SeqTendsTo
    (fun k : ℕ => N * (1 - 1 / (k : ℝ)) ^ k)
    (N / Real.exp 1)

/-- Transparent v11 semantic target for `section5_tradeoff_revealing_primal_dual_lp_formulas`. -/
def section5_tradeoff_revealing_primal_dual_lp_formulasSpec
    {m : ℕ} (c l x y : Fin m → ℝ) : Prop :=
  (MSVV07SourceLemmas.tradeoffRevealingLP c l).primalObjective x =
      ∑ i : Fin m, c i * x i ∧
    ((MSVV07SourceLemmas.tradeoffRevealingLP c l).PrimalFeasible x ↔
      (∀ i, 0 ≤ x i) ∧
        ∀ r, (∑ i : Fin m,
          MSVV07SourceLemmas.paperRouteMatrixCoeff r i * x i) ≤ l r) ∧
    (MSVV07SourceLemmas.tradeoffRevealingLP c l).dualObjective y =
      ∑ r : Fin m, y r * l r ∧
    ((MSVV07SourceLemmas.tradeoffRevealingLP c l).DualFeasible y ↔
      (∀ r, 0 ≤ y r) ∧
        ∀ i, c i ≤ ∑ r : Fin m,
          MSVV07SourceLemmas.paperRouteMatrixCoeff r i * y r)

/-- Transparent v11 semantic target for `theorem8_dual_induced_tradeoff_formula`. -/
def theorem8_dual_induced_tradeoff_formulaSpec
    {m : ℕ} (i : Fin m) : Prop :=
  MSVV07SourceLemmas.paperRoutePsiCandidate i =
    1 - (1 - 1 / (((m + 1 : ℕ) : ℝ))) ^ (m - i.val)

/-- Transparent v11 semantic target for `theorem8_dual_induced_tradeoff_ne_printed_exponent_at_k2`. -/
def theorem8_dual_induced_tradeoff_ne_printed_exponent_at_k2Spec : Prop :=
  MSVV07SourceLemmas.paperRoutePsiCandidate (m := 1) 0 = (1 / 2 : ℝ) ∧
    MSVV07SourceLemmas.paperRoutePsiCandidate (m := 1) 0 ≠
      1 - (1 - 1 / (2 : ℝ)) ^ 2

/-- Transparent v11 semantic target for `theorem8_corrected_unspent_fraction_formula`. -/
def theorem8_corrected_unspent_fraction_formulaSpec
    (k i : ℕ) (hk : 0 < k) : Prop :=
  1 - (i : ℝ) / (k : ℝ) =
    ((k : ℝ) - (i : ℝ)) / (k : ℝ)

/-- Transparent v11 semantic target for `theorem8_unspent_fraction_ne_printed_at_k2`. -/
def theorem8_unspent_fraction_ne_printed_at_k2Spec : Prop :=
  1 - (1 : ℝ) / 2 = (1 / 2 : ℝ) ∧
    1 - (1 : ℝ) / 2 ≠ ((2 : ℝ) - 1 + 1) / 2

/-- Transparent v11 semantic target for `section5_lemma4_dual_optimal_from_primal_dual_match`. -/
def section5_lemma4_dual_optimal_from_primal_dual_matchSpec
    {Advertiser Query : Type*} [Fintype Advertiser]
    (m : ℕ) (I : Proof.PaperInstance Advertiser Query) (history : List Query)
    (psi : ℝ → ℝ) (_hpsi : Antitone psi)
    (_hbid : I.NonnegativeBids) (_hbudget : I.PositiveBudgets) : Prop :=
  Optimization.IsMinimizerOn
    (MSVV07SourceLemmas.tradeoffRevealingLP (m := m)
      MSVV07SourceLemmas.paperRoutePrimalObjectiveCoeff
      (fun row => ∑ i : Fin m, MSVV07SourceLemmas.paperRouteMatrixCoeff row i *
        SourceRunner.section5PreterminalAlphaTypeCountOfTradeoffRun
          m psi I history i)).DualFeasible
    (MSVV07SourceLemmas.tradeoffRevealingLP (m := m)
      MSVV07SourceLemmas.paperRoutePrimalObjectiveCoeff
      (fun row => ∑ i : Fin m, MSVV07SourceLemmas.paperRouteMatrixCoeff row i *
        SourceRunner.section5PreterminalAlphaTypeCountOfTradeoffRun
          m psi I history i)).dualObjective
    MSVV07SourceLemmas.paperRouteDualCandidate

/-- Transparent v11 semantic target for `section5_lemma5_tradeoff_rhs_eq_base_add_delta`. -/
def section5_lemma5_tradeoff_rhs_eq_base_add_deltaSpec
    {m : ℕ} (N : ℝ) (alpha beta : Fin m → ℝ) (i : Fin m)
    (hbeta_prefix :
      (∑ j ∈ MSVV07SourceLemmas.paperRoutePrefix i, beta j) =
        MSVV07SourceLemmas.paperRouteRhs N i -
          ∑ j ∈ MSVV07SourceLemmas.paperRoutePrefix i,
            MSVV07SourceLemmas.paperRouteDeltaCoeff i j * alpha j) : Prop :=
  MSVV07SourceLemmas.paperRouteLPRow alpha i =
    MSVV07SourceLemmas.paperRouteRhs N i +
      MSVV07SourceLemmas.paperRouteDelta alpha beta i

/-- Transparent v11 semantic target for `section5_lemma6_per_query_tradeoff`. -/
def section5_lemma6_per_query_tradeoffSpec
    {Slab : Type*} [Preorder Slab]
    (psi : Slab → ℝ) {queryType optCurrentSlab algSlab : Slab}
    {optBid algBid : ℝ}
    (hoptCurrent_le_type : optCurrentSlab ≤ queryType)
    (hpsi_antitone : Antitone psi)
    (hoptBid_nonneg : 0 ≤ optBid)
    (hchoice : optBid * psi optCurrentSlab ≤ algBid * psi algSlab) : Prop :=
  optBid * psi queryType ≤ algBid * psi algSlab

/-- Transparent v11 semantic target for `section5_lemma7_weighted_perturbation_bound`. -/
def section5_lemma7_weighted_perturbation_boundSpec
    {m Query : Type*} [Fintype m] [Fintype Query] [DecidableEq m]
    (psi alpha beta : m → ℝ) (opt alg : Query → ℝ)
    (queryType querySlab : Query → m) (N : ℝ) (k : ℕ)
    (hpointwise :
      ∀ q : Query, opt q * psi (queryType q) -
        alg q * psi (querySlab q) ≤ 0)
    (hα :
      ∀ i : m,
        (∑ q ∈ (Finset.univ : Finset Query).filter
          (fun q => queryType q = i), opt q) = alpha i)
    (hpsi_nonneg : ∀ i, 0 ≤ psi i)
    (hβ :
      ∀ i : m,
        (∑ q ∈ (Finset.univ : Finset Query).filter
          (fun q => querySlab q = i), alg q) ≤ beta i)
    (hfinal_nonneg : 0 ≤ N / (k : ℝ)) : Prop :=
  (∑ i : m, psi i * (alpha i - beta i)) ≤ N / (k : ℝ)

/-- Transparent v11 semantic target for `theorem8_balance_msvv_competitive_of_small_bids_limit_family`. -/
def theorem8_balance_msvv_competitive_of_small_bids_limit_familySpec
    {Advertiser : Type*}
    [Fintype Advertiser] [Nonempty Advertiser] [DecidableEq Advertiser]
    (n : ℕ → ℕ)
    (I : (k : ℕ) → PaperInstance Advertiser (Fin (n k)))
    (epsilon : ℕ → ℝ)
    (hbid : ∀ k, (I k).NonnegativeBids)
    (hbudget : ∀ k, (I k).PositiveBudgets)
    (hepsilon : ∀ k, 0 ≤ epsilon k)
    (hepsilon_le_one : ∀ k, epsilon k ≤ 1)
    (hsmall : ∀ k, paperSmallBids (I k) (epsilon k))
    (herror_tendsTo_zero :
      Sequence.SeqTendsTo
        (fun k =>
          epsilon k * (Real.exp 1 + 1) *
            (∑ q : Fin (n k), (I k).maxBidForQuery q))
        0) : Prop :=
  ∀ delta : ℝ, 0 < delta →
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      paperMsvvRatio *
          (I k).offlineOptimumValue (fun a => (hbudget k a).le) ≤
        paperRevenue (I k)
            ((I k).runAssignment (I k).balanceChoiceRule
              (List.finRange (n k))) +
          delta

/-- Transparent v11 semantic target for `section6_different_budgets_and_nonexhaustive_optimum_theorem8_finite_explicit_error`. -/
def section6_different_budgets_and_nonexhaustive_optimum_theorem8_finite_explicit_errorSpec
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hepsilon_le_one : epsilon ≤ 1)
    (hsmall : paperSmallBids I epsilon) : Prop :=
  paperMsvvRatio *
      (SourceRunner.occurrenceIndexedInstance I history).offlineOptimumValue
        (fun a => (hbudget a).le) ≤
    paperRevenue (SourceRunner.occurrenceIndexedInstance I history)
      ((SourceRunner.occurrenceIndexedInstance I history).runAssignment
        (SourceRunner.occurrenceIndexedInstance I history).balanceChoiceRule
        (List.finRange history.length)) +
      epsilon * (Real.exp 1 + 1) *
        (∑ t : Fin history.length,
          (SourceRunner.occurrenceIndexedInstance I history).maxBidForQuery t)

/-- Transparent v11 semantic target for `section6_next_highest_bid_all_formula`. -/
def section6_next_highest_bid_all_formulaSpec
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query) (a : Advertiser) (q : Query) : Prop :=
  section6_next_highest_bid_all I a q =
    let others : Finset Advertiser := (Finset.univ : Finset Advertiser).erase a
    if h : others.Nonempty then
      max 0 (others.sup' h fun b => I.bid b q)
    else
      0

/-- Transparent v11 semantic target for `section6_next_highest_bid_alive_formula`. -/
def section6_next_highest_bid_alive_formulaSpec
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (alive : Advertiser → Query → Prop) [∀ a q, Decidable (alive a q)]
    (a : Advertiser) (q : Query) : Prop :=
  section6_next_highest_bid_alive I alive a q =
    let others : Finset Advertiser :=
      ((Finset.univ : Finset Advertiser).erase a).filter fun b => alive b q
    if h : others.Nonempty then
      max 0 (others.sup' h fun b => I.bid b q)
    else
      0

/-- Transparent v11 semantic target for `section6_next_highest_bid_all_theorem8_finite_explicit_error`. -/
def section6_next_highest_bid_all_theorem8_finite_explicit_errorSpec
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hepsilon_le_one : epsilon ≤ 1)
    (hnext_small : ∀ a q,
      section6_next_highest_bid_all I a q ≤ epsilon * I.budget a) : Prop :=
  let J := SourceRunner.occurrenceIndexedInstance
    (I.withEffectiveBids (section6_next_highest_bid_all I)) history
  paperMsvvRatio *
      J.offlineOptimumValue (fun a => (hbudget a).le) ≤
    paperRevenue J
      (J.runAssignment J.balanceChoiceRule (List.finRange history.length)) +
      epsilon * (Real.exp 1 + 1) *
        (∑ t : Fin history.length, J.maxBidForQuery t)

/-- Transparent v11 semantic target for `section6_next_highest_bid_alive_theorem8_finite_explicit_error`. -/
def section6_next_highest_bid_alive_theorem8_finite_explicit_errorSpec
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hepsilon_le_one : epsilon ≤ 1)
    (hnext_small : ∀ a q,
      section6_next_highest_bid_all I a q ≤ epsilon * I.budget a) : Prop :=
  let J := SourceRunner.occurrenceIndexedInstance
    (I.withEffectiveBids (section6_next_highest_bid_all I)) history
  (∀ a q,
    Proof.section6_next_highest_bid_alive I (fun _ _ => True) a q =
      Proof.section6_next_highest_bid_all I a q) ∧
  paperMsvvRatio *
      J.offlineOptimumValue (fun a => (hbudget a).le) ≤
    paperRevenue J
      (J.runAssignment J.balanceChoiceRule (List.finRange history.length)) +
      epsilon * (Real.exp 1 + 1) *
        (∑ t : Fin history.length, J.maxBidForQuery t)

/-- Transparent v11 semantic target for `section6_click_through_rates_effective_bid_formula`. -/
def section6_click_through_rates_effective_bid_formulaSpec
    {Advertiser Query : Type*}
    (I : PaperInstance Advertiser Query)
    (ctr : Advertiser → Query → ℝ) (a : Advertiser) (q : Query) : Prop :=
  (I.withClickThroughRates ctr).bid a q = ctr a q * I.bid a q

/-- Transparent v11 semantic target for `section6_click_through_rates_theorem8_finite_explicit_error`. -/
def section6_click_through_rates_theorem8_finite_explicit_errorSpec
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (ctr : Advertiser → Query → ℝ)
    (hctr_nonneg : ∀ a q, 0 ≤ ctr a q)
    (hctr_le_one : ∀ a q, ctr a q ≤ 1)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hepsilon_le_one : epsilon ≤ 1)
    (hsmall : paperSmallBids I epsilon) : Prop :=
  let J := SourceRunner.occurrenceIndexedInstance (I.withClickThroughRates ctr) history
  paperMsvvRatio *
      J.offlineOptimumValue (fun a => (hbudget a).le) ≤
    paperRevenue J (J.runAssignment J.balanceChoiceRule (List.finRange history.length)) +
      epsilon * (Real.exp 1 + 1) *
        (∑ t : Fin history.length, J.maxBidForQuery t)

/-- Transparent v11 semantic target for `section6_availability_theorem8_finite_explicit_error`. -/
def section6_availability_theorem8_finite_explicit_errorSpec
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    (entryTime : Advertiser → Fin (history.length + 1))
    {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hepsilon_le_one : epsilon ≤ 1)
    (hsmall : paperSmallBids I epsilon) : Prop :=
  let J0 := SourceRunner.occurrenceIndexedInstance I history
  let J := J0.withAvailability (SourceRunner.availableFromEntry entryTime)
  paperMsvvRatio *
      J.offlineOptimumValue (fun a => (hbudget a).le) ≤
    paperRevenue J (J.runAssignment J.balanceChoiceRule (List.finRange history.length)) +
      epsilon * (Real.exp 1 + 1) *
        (∑ t : Fin history.length, J.maxBidForQuery t)

/-- Transparent v11 semantic target for `section6_page_top_balance_theorem8_finite_explicit_error`. -/
def section6_page_top_balance_theorem8_finite_explicit_errorSpec
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : PaperInstance Advertiser Query)
    (slots : Query → ℕ)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    (hnodup : history.Nodup)
    (hcover : AdWordsInstance.historyFinset history = Finset.univ)
    {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hepsilon_le_one : epsilon ≤ 1)
    (hsmall : paperSmallBids I epsilon) : Prop :=
  paperMsvvRatio *
      I.pageOfflineOptimumValue slots (fun a => (hbudget a).le) ≤
    I.pageRevenue
      (I.runPageAssignment slots (I.pageTopBalanceRule slots) history) +
      epsilon * (Real.exp 1 + 1) *
        I.pageHistoryMaxBidSum slots history

/-- Transparent v11 semantic target for `section8_weighted_effective_bid_formula`. -/
def section8_weighted_effective_bid_formulaSpec
    {Advertiser Query : Type*}
    (I : PaperInstance Advertiser Query)
    (weight : Advertiser → ℝ) (a : Advertiser) (q : Query) : Prop :=
  (I.withAdvertiserWeights weight).bid a q = weight a * I.bid a q

/-- Transparent v11 semantic target for `appendix_highest_bid_phase_total_eq_three_fifths`. -/
def appendix_highest_bid_phase_total_eq_three_fifthsSpec (N : ℝ) : Prop :=
  appendixHighestBidPhaseOneRevenue N +
      appendixHighestBidPhaseTwoRevenue N +
      appendixHighestBidPhaseThreeRevenue N =
    (3 / 5 : ℝ) * N

/-- Transparent v11 semantic target for `appendix_highest_bid_phase_total_ne_printed_062`. -/
def appendix_highest_bid_phase_total_ne_printed_062Spec
    {N : ℝ} (hN : 0 < N) : Prop :=
  appendixHighestBidPhaseOneRevenue N +
      appendixHighestBidPhaseTwoRevenue N +
      appendixHighestBidPhaseThreeRevenue N ≠
    (31 / 50 : ℝ) * N

/-- Transparent v11 semantic target for `appendix_three_fifths_lt_msvv_ratio`. -/
def appendix_three_fifths_lt_msvv_ratioSpec : Prop :=
  (3 / 5 : ℝ) < paperMsvvRatio

/-- Transparent v11 semantic target for `theorem9HardDistribution_uniform`. -/
def theorem9HardDistribution_uniformSpec (N : ℕ) : Prop :=
  theorem9HardDistribution N = uniformPermutationDistribution N

/-- Transparent v11 semantic target for `theorem9CappedNormalizedRevenue_formula`. -/
def theorem9CappedNormalizedRevenue_formulaSpec
    (N : ℕ)
    (algorithm :
      { choice : BMatchingIntegralPrefixChoice N //
        BMatchingIntegralPrefixChoice.Feasible choice })
    (permutation : Equiv.Perm (Fin N)) : Prop :=
  theorem9CappedNormalizedRevenue N algorithm permutation =
    (∑ bidder : Fin N,
      min 1
        (∑ round : Fin N,
          BMatchingIntegralPrefixAlgorithm.prefixAllocation algorithm
            (theorem9ObservedPrefix N permutation round)
            round (permutation bidder))) /
      (N : ℝ)

/-- Transparent v11 semantic target for `theorem9_qij_expected_allocation_bound`. -/
def theorem9_qij_expected_allocation_boundSpec
    (N : ℕ) (algorithm : BMatchingIntegralPrefixAlgorithm N)
    (round bidder : Fin N) : Prop :=
  (SourceRunner.theorem9ExpectedRoundAllocation N algorithm round bidder ≤
    if (round : ℕ) ≤ (bidder : ℕ) then
      1 / ((N - (round : ℕ) : ℕ) : ℝ)
    else 0) ∧
    (¬ (round : ℕ) ≤ (bidder : ℕ) →
      SourceRunner.theorem9ExpectedRoundAllocation
        N algorithm round bidder = 0)

/-- Transparent v11 semantic target for `theorem9_no_randomized_online_algorithm_beats_msvv_ratio`. -/
def theorem9_no_randomized_online_algorithm_beats_msvv_ratioSpec : Prop :=
  ∀ delta : ℝ, 0 < delta →
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      ∀ randomizedAlgorithm : theorem9RandomizedOnlineAlgorithm N,
        ¬ ∀ permutation,
          paperMsvvRatio + delta <
            AppliedModelingLib.pmfExp randomizedAlgorithm
              (fun algorithm =>
                theorem9CappedNormalizedRevenue N algorithm permutation)

/-- Transparent v11 semantic target for `appendix_kappa_counterexample_family`. -/
def appendix_kappa_counterexample_familySpec
    {κ : ℝ} (hκ : 1 < κ) : Prop :=
  MSVV07Appendix.derivedKappaContinuousOnlineValue κ =
    MSVV07Appendix.derivedKappaRatio κ ∧
  MSVV07Appendix.derivedKappaContinuousOfflineValue κ = 1 ∧
  MSVV07Appendix.ContinuousUnitBudgetFeasible
    (fun _bidder : ℝ => (1 : ℝ)) ∧
  (∀ spend : ℝ → ℝ,
    MSVV07Appendix.ContinuousUnitBudgetFeasible spend →
      (∫ bidder in (0 : ℝ)..1, spend bidder) ≤
        MSVV07Appendix.derivedKappaContinuousOfflineValue κ) ∧
  MSVV07Appendix.derivedKappaContinuousOnlineValue κ /
      MSVV07Appendix.derivedKappaContinuousOfflineValue κ <
    paperMsvvRatio

/-- Transparent v11 semantic target for `appendix_kappa_continuous_source_execution`. -/
def appendix_kappa_continuous_source_executionSpec
    {κ : ℝ} (hκ : 1 < κ) : Prop :=
  (∀ progress : ℝ, 0 ≤ progress → progress ≤ MSVV07Appendix.derivedKappaB κ →
    (∫ _bidder in
        (MSVV07Appendix.derivedKappaX κ + progress)..1,
      MSVV07Appendix.derivedKappaPhaseOneAllocationRate κ progress) = 1) ∧
  (∀ progress bidder₁ bidder₂ : ℝ,
    0 ≤ progress → progress ≤ MSVV07Appendix.derivedKappaB κ →
    MSVV07Appendix.derivedKappaPhaseOneEligible κ progress bidder₁ →
    MSVV07Appendix.derivedKappaPhaseOneEligible κ progress bidder₂ →
      MSVV07Appendix.derivedKappaPhaseOneRawBid κ progress bidder₁ =
          MSVV07Appendix.derivedKappaPhaseOneRawBid κ progress bidder₂ ∧
        MSVV07Appendix.printedIndividualLeftover bidder₁
            (MSVV07Appendix.derivedKappaPhaseOneSpentBefore κ progress bidder₁) =
          MSVV07Appendix.printedIndividualLeftover bidder₂
            (MSVV07Appendix.derivedKappaPhaseOneSpentBefore
              κ progress bidder₂)) ∧
  (∫ bidder in (1 - MSVV07Appendix.derivedKappaT κ)..1,
    MSVV07Appendix.derivedKappaPhaseTwoAllocationDensity κ bidder) = 1 ∧
  (∀ offset bidder competitor : ℝ,
    0 < MSVV07Appendix.derivedKappaPhaseTwoAllocationDensity κ bidder →
    (MSVV07Appendix.derivedKappaTail κ competitor ∨ competitor = offset) →
      MSVV07Appendix.derivedKappaPhaseTwoRawBid κ offset competitor ≤
        MSVV07Appendix.derivedKappaPhaseTwoRawBid κ offset bidder) ∧
  (∀ offset bidder₁ bidder₂ : ℝ,
    0 ≤ offset → offset ≤ MSVV07Appendix.derivedKappaX κ →
    MSVV07Appendix.derivedKappaTail κ bidder₁ →
    MSVV07Appendix.derivedKappaTail κ bidder₂ →
      MSVV07Appendix.printedIndividualLeftover bidder₁
          (MSVV07Appendix.derivedKappaPhaseTwoSpentBefore κ offset bidder₁) =
        MSVV07Appendix.printedIndividualLeftover bidder₂
          (MSVV07Appendix.derivedKappaPhaseTwoSpentBefore
            κ offset bidder₂)) ∧
  (∀ bidder : ℝ, MSVV07Appendix.derivedKappaTail κ bidder →
    MSVV07Appendix.derivedKappaPhaseTwoSpentBefore
      κ (MSVV07Appendix.derivedKappaX κ) bidder = 1) ∧
  (∀ owner : ℝ, MSVV07Appendix.derivedKappaTail κ owner →
    MSVV07Appendix.derivedKappaPhaseThreeAllocationRate owner owner +
        MSVV07Appendix.derivedKappaPhaseThreeDiscardRate owner = 1 ∧
      MSVV07Appendix.derivedKappaPhaseTwoSpentBefore
          κ (MSVV07Appendix.derivedKappaX κ) owner = 1 ∧
      ∀ bidder : ℝ,
        0 < MSVV07Appendix.derivedKappaPhaseThreeRawBid owner bidder →
          bidder = owner) ∧
  MSVV07Appendix.derivedKappaContinuousOnlineValue κ =
    MSVV07Appendix.derivedKappaRatio κ ∧
  MSVV07Appendix.derivedKappaContinuousOfflineValue κ = 1

/-- Transparent v11 semantic target for `appendix_kappa_ratio_limit_infinity`. -/
def appendix_kappa_ratio_limit_infinitySpec : Prop :=
  (∀ κ : ℝ, 1 < κ →
    MSVV07Appendix.derivedKappaContinuousOnlineValue κ /
        MSVV07Appendix.derivedKappaContinuousOfflineValue κ =
      MSVV07Appendix.derivedKappaRatio κ) ∧
  Filter.Tendsto MSVV07Appendix.derivedKappaRatio Filter.atTop
    (nhds paperMsvvRatio)

/-- Transparent v11 semantic target for `appendix_kappa_ratio_limit_one`. -/
def appendix_kappa_ratio_limit_oneSpec : Prop :=
  (∀ κ : ℝ, 1 < κ →
    MSVV07Appendix.derivedKappaContinuousOnlineValue κ /
        MSVV07Appendix.derivedKappaContinuousOfflineValue κ =
      MSVV07Appendix.derivedKappaRatio κ) ∧
  Filter.Tendsto MSVV07Appendix.derivedKappaRatio
      (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds (1 / 2 : ℝ)) ∧
  (1 / 2 : ℝ) ≠ paperMsvvRatio

/-- Transparent v11 semantic target for `appendix_naive_algorithm_true_revenue_formula`. -/
def appendix_naive_algorithm_true_revenue_formulaSpec : Prop :=
  MSVV07Appendix.printedContinuousOnlineValue =
    9 / 10 - 1 / 2 * Real.log (9 / 5) ∧
  MSVV07Appendix.printedPhaseThreeServedMass =
    3 / 10 - 1 / 2 * Real.log (9 / 5) ∧
  0 < MSVV07Appendix.printedPhaseThreeServedMass ∧
  (2 / 5 : ℝ) + 2 * (1 / 10) = 3 / 5 ∧
  (3 / 5 : ℝ) ≠ 31 / 50

/-- Transparent v11 semantic target for `appendix_naive_highest_bid_fluid_rule`. -/
def appendix_naive_highest_bid_fluid_ruleSpec : Prop :=
  (∀ r : ℝ, 0 ≤ r → r ≤ 2 / 5 →
    (∫ _bidder in (1 / 10 + r)..1,
      MSVV07Appendix.printedPhaseOneAllocationRate r) = 1) ∧
  (∀ r bidder₁ bidder₂ : ℝ,
    0 ≤ r → r ≤ 2 / 5 →
    MSVV07Appendix.printedPhaseOneEligible r bidder₁ →
    MSVV07Appendix.printedPhaseOneEligible r bidder₂ →
      MSVV07Appendix.printedPhaseOneRawBid r bidder₁ =
          MSVV07Appendix.printedPhaseOneRawBid r bidder₂ ∧
        MSVV07Appendix.printedIndividualLeftover bidder₁
            (MSVV07Appendix.printedPhaseOneSpentBefore r bidder₁) =
          MSVV07Appendix.printedIndividualLeftover bidder₂
            (MSVV07Appendix.printedPhaseOneSpentBefore r bidder₂)) ∧
  (∫ bidder in (1 / 2 : ℝ)..1,
    MSVV07Appendix.printedPhaseTwoAllocationDensity bidder) = 1 ∧
  (∀ offset bidder competitor : ℝ,
    0 < MSVV07Appendix.printedPhaseTwoAllocationDensity bidder →
    ((1 / 2 ≤ competitor ∧ competitor ≤ 1) ∨ competitor = offset) →
      MSVV07Appendix.printedPhaseTwoRawBid offset competitor ≤
        MSVV07Appendix.printedPhaseTwoRawBid offset bidder) ∧
  (∀ offset bidder₁ bidder₂ : ℝ,
    0 ≤ offset → offset ≤ 1 / 10 →
    (1 / 2 ≤ bidder₁ ∧ bidder₁ ≤ 1) →
    (1 / 2 ≤ bidder₂ ∧ bidder₂ ≤ 1) →
      MSVV07Appendix.printedIndividualLeftover bidder₁
          (MSVV07Appendix.printedPhaseTwoSpentBefore offset bidder₁) =
        MSVV07Appendix.printedIndividualLeftover bidder₂
          (MSVV07Appendix.printedPhaseTwoSpentBefore offset bidder₂)) ∧
  (∀ progress owner : ℝ, 0 ≤ progress →
    MSVV07Appendix.printedPhaseThreeAllocationRate progress owner owner +
      MSVV07Appendix.printedPhaseThreeDiscardRate progress = 1) ∧
  ∀ progress owner : ℝ,
    (1 / 2 ≤ owner ∧ owner ≤ 1) →
    0 < MSVV07Appendix.printedPhaseThreeDiscardRate progress →
      MSVV07Appendix.printedPhaseThreeSpentBefore
        progress owner = 1

/-- Transparent v11 semantic target for `appendix_naive_three_phase_fluid_construction`. -/
def appendix_naive_three_phase_fluid_constructionSpec : Prop :=
  0 < MSVV07Appendix.printedPhaseThreeResidualPerTail ∧
  (∀ owner : ℝ, (1 / 2 ≤ owner ∧ owner ≤ 1) →
    MSVV07Appendix.printedPhaseThreeSpentBefore
      MSVV07Appendix.printedPhaseThreeResidualPerTail owner = 1) ∧
  MSVV07Appendix.printedContinuousOnlineValue =
    9 / 10 - 1 / 2 * Real.log (9 / 5) ∧
  MSVV07Appendix.printedContinuousOfflineValue = 1

/-- Transparent v11 semantic target for `appendix_naive_true_ratio_conclusion`. -/
def appendix_naive_true_ratio_conclusionSpec : Prop :=
  MSVV07Appendix.printedContinuousOnlineValue /
      MSVV07Appendix.printedContinuousOfflineValue <
    paperMsvvRatio

/-- Transparent v11 semantic target for `appendix_optimum_revenue_formula`. -/
def appendix_optimum_revenue_formulaSpec : Prop :=
  ((∀ r : ℝ, 0 ≤ r → r ≤ 2 / 5 →
      MSVV07Appendix.printedPhaseOneRawBid r (1 / 10 + r) = 1) ∧
    (∀ offset : ℝ, 0 ≤ offset → offset ≤ 1 / 10 →
      MSVV07Appendix.printedPhaseTwoRawBid offset offset = 1) ∧
    (∀ owner : ℝ, 1 / 2 ≤ owner → owner ≤ 1 →
      MSVV07Appendix.printedPhaseThreeRawBid owner owner = 1) ∧
    (2 / 5 : ℝ) + 1 / 10 + 1 / 2 = 1) ∧
  MSVV07Appendix.ContinuousUnitBudgetFeasible
      (fun _bidder : ℝ => (1 : ℝ)) ∧
  MSVV07Appendix.printedContinuousOfflineValue = 1 ∧
  ∀ spend : ℝ → ℝ,
    MSVV07Appendix.ContinuousUnitBudgetFeasible spend →
      (∫ bidder in (0 : ℝ)..1, spend bidder) ≤
        MSVV07Appendix.printedContinuousOfflineValue

/-- Transparent v11 semantic target for `section2_competitive_ratio_definition`. -/
def section2_competitive_ratio_definitionSpec
    {Instance : Type*} (onlineRevenue offlineRevenue : Instance → ℝ) (α : ℝ) : Prop :=
  SourceRunner.IsAlphaCompetitive onlineRevenue offlineRevenue α ↔
    ∀ I, α ≤ onlineRevenue I / offlineRevenue I

/-- Transparent v11 semantic target for the occurrence-level Section 2 model. -/
def section2_occurrence_assignment_feasibility_definitionSpec
    {Advertiser Query : Type*} [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query) (history : List Query)
    (A : Fin history.length → Option Advertiser) : Prop :=
  SourceRunner.occurrenceAssignmentFeasible I history A ↔
    (∀ t, ∃ a, A t = some a) ∧
      ∀ a, SourceRunner.occurrenceSpend I history A a ≤ I.budget a

/-- Transparent v11 semantic target for Section 3's finite score formula. -/
def section3_discrete_balance_score_formulaSpec
    {Advertiser Query : Type*}
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (S : SourceRunner.OccurrenceState Advertiser Query)
    (q : Query) (a : Advertiser) : Prop :=
  SourceRunner.occurrenceDiscreteScore k hk I S q a =
    I.bid a q * paperDiscreteTradeoff k
      (SourceRunner.activeBudgetSlab k hk (S.spent a) (I.budget a))

/-- Transparent v11 semantic target for Section 3's finite argmax rule. -/
def section3_discrete_balance_choice_ruleSpec
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (S : SourceRunner.OccurrenceState Advertiser Query)
    (q : Query) (a : Advertiser)
    (hchoice : (SourceRunner.discreteBalanceScan k hk I S q).winner = some a) : Prop :=
  SourceRunner.occurrenceDiscreteBalanceChoice k hk I S q a

/-- Transparent v11 semantic target for `section3_balance_occurrence_runner_cost`. -/
def section3_balance_occurrence_runner_costSpec
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query) (history : List Query) : Prop :=
  (SourceRunner.runBalanceOccurrences I history).candidateTests =
      history.length * Fintype.card Advertiser ∧
    (SourceRunner.runBalanceOccurrences I history).scoreComparisons ≤
      history.length * Fintype.card Advertiser

/-- Transparent v11 semantic target for `section3_discrete_balance_algorithm`. -/
def section3_discrete_balance_algorithmSpec
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (S : SourceRunner.OccurrenceState Advertiser Query)
    (q : Query) (a : Advertiser)
    (hchoice : (SourceRunner.discreteBalanceScan k hk I S q).winner = some a) : Prop :=
  SourceRunner.occurrenceDiscreteBalanceChoice k hk I S q a

/-- Transparent v11 semantic target for `section3_discrete_tradeoff_convergence`. -/
def section3_discrete_tradeoff_convergenceSpec
    (slab : ℕ → ℕ) (s : ℝ)
    (hfraction :
      Filter.Tendsto
        (fun k : ℕ => ((slab k + 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ))
        Filter.atTop (nhds s)) : Prop :=
  Sequence.SeqTendsTo
    (fun k : ℕ =>
      1 - Real.exp
        (-(1 - (((slab k + 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ)))))
    (1 - Real.exp (-(1 - s)))

/-- Transparent v11 semantic target for `section3_discrete_tradeoff_monotonicity`. -/
def section3_discrete_tradeoff_monotonicitySpec (k : ℕ) : Prop :=
  Antitone (paperDiscreteTradeoff k)

/-- Transparent v11 semantic target for `section3_equal_bid_discrete_msvv_is_balance`. -/
def section3_equal_bid_discrete_msvv_is_balanceSpec
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (S : SourceRunner.OccurrenceState Advertiser Query) (q : Query)
    (a : Advertiser) {commonBid : ℝ}
    (hcommon : ∀ b, I.bid b q = commonBid) (hcommon_pos : 0 < commonBid)
    (hchoice : (SourceRunner.discreteBalanceScan k hk I S q).winner = some a) : Prop :=
  SourceRunner.occurrenceCanAssign I S q a ∧
    ∀ b, SourceRunner.occurrenceCanAssign I S q b →
      SourceRunner.activeBudgetSlab k hk (S.spent a) (I.budget a) ≤
        SourceRunner.activeBudgetSlab k hk (S.spent b) (I.budget b)

/-- Transparent v11 semantic target for `section3_greedy_tight_half_example`. -/
def section3_greedy_tight_half_exampleSpec
    {c : ℝ} (hc : 0 < c) : Prop :=
  Filter.Tendsto (fun epsilon : ℝ => section3GreedyTwoWordRatio c epsilon)
    (nhds 0) (nhds (1 / 2 : ℝ))

/-- Transparent v11 semantic target for `section3_greedy_two_word_fluid_construction`. -/
def section3_greedy_two_word_fluid_constructionSpec
    {c epsilon : ℝ} (hc : 0 < c) (hepsilon : 0 < epsilon) : Prop :=
  c < c + epsilon ∧
    SourceRunner.greedyTwoWordOnlineRevenue c epsilon = 1 ∧
    SourceRunner.greedyTwoWordOfflineRevenue c epsilon =
      1 + c / (c + epsilon) ∧
    c / (c + epsilon) ≤ 1 ∧
    SourceRunner.greedyTwoWordOnlineRevenue c epsilon /
        SourceRunner.greedyTwoWordOfflineRevenue c epsilon =
      section3GreedyTwoWordRatio c epsilon

/-- Transparent v11 semantic target for `section3_slab_and_current_slab_definition`. -/
def section3_slab_and_current_slab_definitionSpec
    (k : ℕ) (hk : 0 < k) (spentFraction : ℝ) : Prop :=
  (SourceRunner.activeSlab k hk spentFraction).val =
    min (Nat.floor (max 0 ((k : ℝ) * spentFraction))) (k - 1)

/-- Transparent v11 semantic target for `section4_balance_exact_tightness_instance`. -/
def section4_balance_exact_tightness_instanceSpec
    (m : ℕ) (N : ℝ) (hN : 0 ≤ N) : Prop :=
  let E := SourceRunner.factorLPTightFluidExecution m N
  (∀ i, 0 ≤ E.typeMass i) ∧
  (∀ i : Fin m,
    E.activeMassBeforeSlab i.val - E.activeMassBeforeSlab (i.val + 1) =
      E.typeMass i) ∧
  (∀ stage, stage ≤ m →
    E.spentBeforeSlab stage = (stage : ℝ) / ((m + 1 : ℕ) : ℝ) ∧
    E.allocationPerActiveBidder stage =
      1 / ((m + 1 : ℕ) : ℝ) ∧
    E.queryMassAtSlab stage =
      E.activeMassBeforeSlab stage / ((m + 1 : ℕ) : ℝ) ∧
    (stage < m →
      E.spentBeforeSlab (stage + 1) =
        E.spentBeforeSlab stage + E.allocationPerActiveBidder stage) ∧
    E.spentBeforeSlab stage + E.allocationPerActiveBidder stage ≤ 1 ∧
    E.activeMassBeforeSlab stage * E.allocationPerActiveBidder stage =
      E.queryMassAtSlab stage) ∧
  (∑ i : Fin m, E.typeMass i) + E.fullMass = N ∧
  (∀ i,
    MSVV07SourceLemmas.paperRouteLPRow E.typeMass i =
      MSVV07SourceLemmas.paperRouteRhs N i) ∧
  E.revenue =
    (∑ i : Fin m,
      E.typeMass i * SourceRunner.factorLPTightFinalSpendFraction m i) +
      E.fullMass ∧
  E.revenue =
    ∑ stage ∈ Finset.range (m + 1),
      E.activeMassBeforeSlab stage * E.allocationPerActiveBidder stage ∧
  E.revenue = N - MSVV07SourceLemmas.factorRevealingLPValue m N ∧
  Sequence.SeqTendsTo
    (fun r : ℕ => (SourceRunner.factorLPTightFluidExecution r 1).revenue)
    paperMsvvRatio

/-- Transparent v11 semantic target for `section4_balance_revenue_factor_lp_bridge_formula`. -/
def section4_balance_revenue_factor_lp_bridge_formulaSpec
    {k : ℕ} (N BAL Φ : ℝ)
    (hBAL : N - BAL ≤ Φ + N / (k : ℝ)) : Prop :=
  N - Φ - N / (k : ℝ) ≤ BAL

/-- Transparent v11 semantic target for `section4_bidder_type_definition`. -/
def section4_bidder_type_definitionSpec
    (k : ℕ) (spentFraction : ℝ) (i : Fin k) : Prop :=
  SourceRunner.IsFinalType k spentFraction i ↔
    (spentFraction = 0 ∧ i.val = 0) ∨
      ((i.val : ℝ) / (k : ℝ) < spentFraction ∧
        spentFraction ≤ (((i.val + 1 : ℕ) : ℝ) / (k : ℝ)))

/-- Transparent v11 semantic target for `section4_discretization_error_bound`. -/
def section4_discretization_error_boundSpec
    {Advertiser : Type*} [Fintype Advertiser]
    {k : ℕ} (hk : 0 < k) (error : Advertiser → ℝ)
    (herror_nonneg : ∀ a, 0 ≤ error a)
    (herror : ∀ a, error a ≤ 1 / (k : ℝ)) : Prop :=
  ∑ a : Advertiser, error a ≤
    (Fintype.card Advertiser : ℝ) / (k : ℝ)

/-- Transparent v11 semantic target for `section4_slab_spend_beta_formula`. -/
def section4_slab_spend_beta_formulaSpec
    {k : ℕ} (N : ℝ) (x : Fin k → ℝ) (i : Fin k) : Prop :=
  SourceRunner.section4IdealizedSlabSpend N x i =
    N / (k : ℝ) - (∑ j ∈ Finset.Iio i, x j) / (k : ℝ)

/-- Transparent v11 semantic target for `section4_type_count_x_definition`. -/
def section4_type_count_x_definitionSpec
    {Advertiser : Type*} [Fintype Advertiser]
    (k : ℕ) (finalSpentFraction : Advertiser → ℝ) (i : Fin k) : Prop :=
  SourceRunner.section4TypeCount k finalSpentFraction i =
    ∑ a : Advertiser,
      if SourceRunner.IsFinalType k (finalSpentFraction a) i then 1 else 0

/-- Transparent v11 semantic target for `section5_alg_query_revenue_definition`. -/
def section5_alg_query_revenue_definitionSpec
    (I : PaperInstance Advertiser Query)
    (d : SourceRunner.OccurrenceDecision Advertiser Query) : Prop :=
  SourceRunner.section5AlgQueryRevenue I d =
    match d.winner with
    | none => 0
    | some a => I.bid a d.query

/-- Transparent v11 semantic target for `section5_alpha_type_count_definition`. -/
def section5_alpha_type_count_definitionSpec
    {Advertiser : Type*} [Fintype Advertiser]
    (k : ℕ) (finalSpentFraction : Advertiser → ℝ) (i : Fin k) : Prop :=
  SourceRunner.section5AlphaTypeCount k finalSpentFraction i =
    SourceRunner.section4TypeCount k finalSpentFraction i

/-- Transparent v11 semantic target for `section5_beta_slab_spend_definition`. -/
def section5_beta_slab_spend_definitionSpec
    {k : ℕ} (N : ℝ) (alpha : Fin k → ℝ) (i : Fin k) : Prop :=
  SourceRunner.section5IdealizedBeta N alpha i =
    N / (k : ℝ) - (∑ j ∈ Finset.Iio i, alpha j) / (k : ℝ)

/-- Transparent v11 semantic target for `section5_bidder_type_definition`. -/
def section5_bidder_type_definitionSpec
    (k : ℕ) (spentFraction : ℝ) (i : Fin k) : Prop :=
  SourceRunner.IsFinalType k spentFraction i ↔
    (spentFraction = 0 ∧ i.val = 0) ∨
      ((i.val : ℝ) / (k : ℝ) < spentFraction ∧
        spentFraction ≤ (((i.val + 1 : ℕ) : ℝ) / (k : ℝ)))

/-- Transparent v11 semantic target for `section5_delta_prefix_definition`. -/
def section5_delta_prefix_definitionSpec
    {k : ℕ} (alpha beta : Fin k → ℝ) (i : Fin k) : Prop :=
  SourceRunner.section5Delta alpha beta i =
    ∑ j ∈ Finset.Iic i, (alpha j - beta j)

/-- Transparent v11 semantic target for `section5_opt_query_revenue_definition`. -/
def section5_opt_query_revenue_definitionSpec
    (I : PaperInstance Advertiser Query) (history : List Query)
    (opt : Fin history.length → Option Advertiser) (t : Fin history.length) : Prop :=
  SourceRunner.section5OptQueryRevenue I history opt t =
    match opt t with
    | none => 0
    | some a => I.bid a (history.get t)

/-- Transparent v11 semantic target for `section5_query_slab_definition`. -/
def section5_query_slab_definitionSpec
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (d : SourceRunner.OccurrenceDecision Advertiser Query) : Prop :=
  SourceRunner.section5QuerySlab k hk I d =
    d.winner.map fun a =>
      SourceRunner.activeBudgetSlab k hk (d.spentBefore a) (I.budget a)

/-- Transparent v11 semantic target for `section5_query_type_definition`. -/
def section5_query_type_definitionSpec
    (optOwner : Option Advertiser) (finalType : Advertiser → Fin k) : Prop :=
  SourceRunner.section5QueryType optOwner finalType = optOwner.map finalType

/-- Transparent v11 semantic target for `section5_slab_fiber_beta_accounting_formula`. -/
def section5_slab_fiber_beta_accounting_formulaSpec
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (decisions : List (SourceRunner.OccurrenceDecision Advertiser Query))
    (i : Fin k) : Prop :=
  SourceRunner.section5AlgSlabFiberRevenue k hk I decisions i =
    (decisions.map fun d =>
      if SourceRunner.section5QuerySlab k hk I d = some i then
        SourceRunner.section5AlgQueryRevenue I d
      else 0).sum

/-- Transparent v11 semantic target for `section5_type_fiber_alpha_accounting_formula`. -/
def section5_type_fiber_alpha_accounting_formulaSpec
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    {k : ℕ} (I : PaperInstance Advertiser Query) (history : List Query)
    (opt : Fin history.length → Option Advertiser)
    (finalType : Advertiser → Fin k)
    (hexhaust : ∀ a, SourceRunner.occurrenceSpend I history opt a = 1)
    (i : Fin k) : Prop :=
  SourceRunner.section5OptTypeFiberRevenue I history opt finalType i =
    ∑ a : Advertiser, if finalType a = i then 1 else 0

/-- Transparent v11 semantic target for `section6_alpha_i_definition`. -/
def section6_alpha_i_definitionSpec
    (I : PaperInstance Advertiser Query) (history : List Query)
    (opt : Fin history.length → Option Advertiser)
    (finalType : Advertiser → Fin k) (i : Fin k) : Prop :=
  SourceRunner.section6OptRevenueByFinalType I history opt finalType i =
    ∑ t : Fin history.length,
      match opt t with
      | none => 0
      | some a => if finalType a = i then I.bid a (history.get t) else 0

/-- Transparent v11 semantic target for `section6_alpha_total_definition`. -/
def section6_alpha_total_definitionSpec
    (I : PaperInstance Advertiser Query) (history : List Query)
    (opt : Fin history.length → Option Advertiser)
    (finalType : Advertiser → Fin k) : Prop :=
  SourceRunner.section6OptRevenueTotalByType I history opt finalType =
    SourceRunner.occurrenceRevenue I history opt

/-- Transparent v11 semantic target for `section6_beta_i_aggregate_definition`. -/
def section6_beta_i_aggregate_definitionSpec
    {Advertiser Query : Type*} [Fintype Advertiser]
    (k : ℕ) (I : PaperInstance Advertiser Query)
    (finalSpend : Advertiser → ℝ)
    (i : Fin k) : Prop :=
  SourceRunner.section6AggregateSlabSpend k I finalSpend i =
    ∑ a : Advertiser,
      SourceRunner.section6BidderSlabSpend k I finalSpend i a

/-- Transparent v11 semantic target for `section6_beta_ij_definition`. -/
def section6_beta_ij_definitionSpec
    {Advertiser Query : Type*}
    (k : ℕ) (I : PaperInstance Advertiser Query)
    (finalSpend : Advertiser → ℝ)
    (i : Fin k) (a : Advertiser) : Prop :=
  SourceRunner.section6BidderSlabSpend k I finalSpend i a =
    min (finalSpend a) (SourceRunner.section6SlabUpper k I i a) -
      min (finalSpend a) (SourceRunner.section6SlabLower k I i a)

/-- Transparent v11 semantic target for `section6_beta_lower_bound_formula`. -/
def section6_beta_lower_bound_formulaSpec
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    {k : ℕ} (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (history : List Query)
    (opt : Fin history.length → Option Advertiser)
    (finalType : Advertiser → Fin k)
    (hbudget : I.PositiveBudgets)
    (hoptFeasible : ∀ a,
      SourceRunner.occurrenceSpend I history opt a ≤ I.budget a)
    (hfinalType : ∀ a,
      SourceRunner.IsFinalType k
        ((SourceRunner.runDiscreteBalanceOccurrences k hk I history).spent a /
          I.budget a)
        (finalType a)) : Prop :=
  section6BetaLowerBounds
    (SourceRunner.section6OptRevenueTotalByType I history opt finalType)
    (SourceRunner.section6OptRevenueByFinalType I history opt finalType)
    (SourceRunner.section6AggregateSlabSpend k I
      (SourceRunner.runDiscreteBalanceOccurrences k hk I history).spent)

/-- Transparent v11 semantic target for `section6_current_type_definition`. -/
def section6_current_type_definitionSpec
    (k : ℕ) (hk : 0 < k) (spent budget : ℝ) : Prop :=
  SourceRunner.section6CurrentType k hk spent budget =
    SourceRunner.activeBudgetSlab k hk spent budget

/-- Transparent v11 semantic target for `section6_generalized_current_type_balance_algorithm`. -/
def section6_generalized_current_type_balance_algorithmSpec
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (S : SourceRunner.OccurrenceState Advertiser Query) (q : Query)
    (a : Advertiser)
    (hchoice : (SourceRunner.discreteBalanceScan k hk I S q).winner = some a) : Prop :=
  SourceRunner.occurrenceDiscreteBalanceChoice k hk I S q a

/-- Transparent v11 semantic target for `section6_next_highest_alive_keep_alive_reduction`. -/
def section6_next_highest_alive_keep_alive_reductionSpec
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query) (a : Advertiser) (q : Query) : Prop :=
  Proof.section6_next_highest_bid_alive I (fun _ _ => True) a q =
    Proof.section6_next_highest_bid_all I a q

/-- Transparent v11 semantic target for `section6_weighted_alpha_beta_inequality`. -/
def section6_weighted_alpha_beta_inequalitySpec
    {m Query : Type*} [Fintype m] [Fintype Query]
    (psi alpha beta : m → ℝ) (opt alg : Query → ℝ)
    (queryType querySlab : Query → m)
    (htradeoff_sum :
      (∑ q : Query,
        (opt q * psi (queryType q) - alg q * psi (querySlab q))) ≤ 0)
    (hopt_accounting :
      (∑ q : Query, opt q * psi (queryType q)) =
        ∑ i : m, psi i * alpha i)
    (halg_accounting :
      (∑ q : Query, alg q * psi (querySlab q)) ≤
        ∑ i : m, psi i * beta i) : Prop :=
  (∑ i : m, psi i * alpha i) ≤ ∑ i : m, psi i * beta i

/-- Transparent v11 semantic target for `section8_online_weight_adjustment_heuristic`. -/
def section8_online_weight_adjustment_heuristicSpec
    (weight finalWeight : ℝ) (windows : List (ℝ × ℝ)) : Prop :=
  SourceRunner.IsRepeatedWeightAdjustment weight windows finalWeight ↔
    match windows with
    | [] => finalWeight = weight
    | (spent, fairShare) :: remaining =>
        ∃ nextWeight,
          SourceRunner.IsWeightAdjustment
            weight spent fairShare nextWeight ∧
            SourceRunner.IsRepeatedWeightAdjustment
              nextWeight remaining finalWeight

/-- Transparent v11 semantic target for `section8_replicated_ranking_algorithm_proposal`. -/
def section8_replicated_ranking_algorithm_proposalSpec
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (m : ℕ) (hm : 0 < m) (I : PaperInstance Advertiser Query)
    (rank : SourceRunner.Representative Advertiser m → ℕ)
    (rankScale : ℕ → ℝ)
    (rankWeight : SourceRunner.Representative Advertiser m → ℝ)
    (history : List Query)
    (hrank_injective : Function.Injective rank)
    (hrank_weight : ∀ r, rankWeight r = rankScale (rank r)) : Prop :=
  (∀ r : SourceRunner.Representative Advertiser m,
      (SourceRunner.replicatedInstance m I).budget r =
        I.budget r.1 / (m : ℝ)) ∧
    (∀ (r : SourceRunner.Representative Advertiser m) (q : Query),
      (SourceRunner.replicatedInstance m I).bid r q = I.bid r.1 q ∧
        SourceRunner.replicatedRankingScore I rankWeight r q =
          I.bid r.1 q * rankScale (rank r)) ∧
    SourceRunner.runReplicatedRankingProposal m I rankWeight history =
      SourceRunner.runOccurrencesFrom
        (SourceRunner.replicatedRankingStep m I rankWeight)
        SourceRunner.initialOccurrenceState history

/-- Transparent v11 semantic target for `section8_switching_query_distribution_model`. -/
def section8_switching_query_distribution_modelSpec
    (M : SourceRunner.SwitchingQueryDistribution Time Regime Query)
    (switchCount : ℕ) (periodAt : Time → Fin (switchCount + 1))
    (regimeForPeriod : Fin (switchCount + 1) → Regime)
    (hadversarial_schedule :
      ∀ time, M.regimeAt time = regimeForPeriod (periodAt time)) : Prop :=
  (∀ time,
    M.queryDistributionAt time =
      M.queryDistribution (regimeForPeriod (periodAt time))) ∧
    (∀ time₁ time₂, periodAt time₁ = periodAt time₂ →
      M.queryDistributionAt time₁ = M.queryDistributionAt time₂)

/-- Transparent v11 semantic target for `section8_weighted_bid_algorithm_proposal`. -/
def section8_weighted_bid_algorithm_proposalSpec
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query) (weight : Advertiser → ℝ)
    (history : List Query) : Prop :=
  SourceRunner.runWeightedBidProposal I weight history =
    SourceRunner.runBalanceOccurrences (I.withAdvertiserWeights weight) history

/-- Transparent v11 semantic target for `theorem8_delta_dual_suffix_identity`. -/
def theorem8_delta_dual_suffix_identitySpec
    {m : ℕ} (alpha beta y : Fin m → ℝ) : Prop :=
  (∑ i : Fin m, y i * MSVV07SourceLemmas.paperRouteDelta alpha beta i) =
    ∑ i : Fin m,
      MSVV07SourceLemmas.paperRoutePsiFromDual y i * (alpha i - beta i)

/-- Transparent v11 semantic target for `theorem8_simple_proof_beta_recurrence_formula`. -/
def theorem8_simple_proof_beta_recurrence_formulaSpec
    {k : ℕ} (N : ℝ) (alpha : Fin k → ℝ) (i : Fin k) : Prop :=
  SourceRunner.section5IdealizedBeta N alpha i =
    N / (k : ℝ) - (∑ j ∈ Finset.Iio i, alpha j) / (k : ℝ)

/-- Transparent v11 semantic target for `theorem8_simple_proof_weighted_alpha_beta_inequality`. -/
def theorem8_simple_proof_weighted_alpha_beta_inequalitySpec
    {k : ℕ} (psi alpha beta : Fin k → ℝ) : Prop :=
  theorem8WeightedAlphaBeta psi alpha beta ↔
    (∑ i : Fin k, psi i * alpha i) ≤ ∑ i : Fin k, psi i * beta i

/-- Transparent v11 semantic target for `theorem8_unspent_budget_bound_formula`. -/
def theorem8_unspent_budget_bound_formulaSpec
    (N revenue error : ℝ)
    (hcompetitive : paperMsvvRatio * N ≤ revenue + error) : Prop :=
  N - revenue ≤ N / Real.exp 1 + error

/-- Transparent v11 semantic target for `theorem9_base_instance_balance_revenue_claim`. -/
def theorem9_base_instance_balance_revenue_claimSpec : Prop :=
  ∀ delta : ℝ, 0 < delta →
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      SourceRunner.theorem9BaseEqualSpreadBalanceRevenue N / (N : ℝ) ≤
        paperMsvvRatio + delta

/-- Transparent v11 semantic target for `theorem9_expected_round_allocation_bound`. -/
def theorem9_expected_round_allocation_boundSpec
    (N : ℕ) (algorithm : BMatchingIntegralPrefixAlgorithm N)
    (round bidder : Fin N) : Prop :=
  (SourceRunner.theorem9ExpectedRoundAllocation N algorithm round bidder ≤
    if (round : ℕ) ≤ (bidder : ℕ) then
      1 / ((N - (round : ℕ) : ℕ) : ℝ)
    else 0) ∧
    (¬ (round : ℕ) ≤ (bidder : ℕ) →
      SourceRunner.theorem9ExpectedRoundAllocation
        N algorithm round bidder = 0)

/-- Transparent v11 semantic target for `theorem9_hard_instance_round_bids_and_optimum`. -/
def theorem9_hard_instance_round_bids_and_optimumSpec
    (N m : ℕ) (epsilon : ℝ) (permutation : Equiv.Perm (Fin N))
    (hround : (m : ℝ) * epsilon = 1) : Prop :=
  (∀ round bidder,
    SourceRunner.theorem9RoundBid N epsilon permutation round bidder =
      if (round : ℕ) ≤ (bidder : ℕ) then epsilon else 0) ∧
    paperRevenue (SourceRunner.theorem9HardInstance N m epsilon permutation)
        (SourceRunner.theorem9HardOfflineAssignment N m permutation) = (N : ℝ)

/-- Transparent v11 semantic target for `theorem9_harmonic_spend_and_revenue_bound`. -/
def theorem9_harmonic_spend_and_revenue_boundSpec
    (N : ℕ) (algorithm : BMatchingIntegralPrefixAlgorithm N)
    (bidder : Fin N) : Prop :=
  theorem9BidderSpendUpperBound N bidder =
      min 1
        (∑ round : Fin N,
          if (round : ℕ) ≤ (bidder : ℕ) then
            1 / ((N - (round : ℕ) : ℕ) : ℝ)
          else 0) ∧
    min 1
        (∑ round : Fin N,
          SourceRunner.theorem9ExpectedRoundAllocation
            N algorithm round bidder) ≤
      theorem9BidderSpendUpperBound N bidder ∧
    theorem9NormalizedRevenueUpperBound N =
      (∑ b : Fin N, theorem9BidderSpendUpperBound N b) / (N : ℝ) ∧
    pmfExp (uniformPermutationDistribution N)
        (fun permutation =>
          (SourceRunner.theorem9IntegralRoundCertificate N).normalizedRevenue
            algorithm permutation) ≤
      theorem9NormalizedRevenueUpperBound N ∧
    ∀ delta : ℝ, 0 < delta →
      ∃ N0 : ℕ, ∀ marketSize : ℕ, N0 ≤ marketSize →
        theorem9NormalizedRevenueUpperBound marketSize ≤
          paperMsvvRatio + delta

/-- Transparent v11 source-item target for `section3_balance_choice_exists_with_finite_max_cost`. -/
def section3_balance_choice_exists_with_finite_max_costSpec : Prop :=
  (∀
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query) (history : List Query), (SourceRunner.runBalanceOccurrences I history).candidateTests =
        history.length * Fintype.card Advertiser ∧
      (SourceRunner.runBalanceOccurrences I history).scoreComparisons ≤
        history.length * Fintype.card Advertiser)

/-- Checked proof endpoint for the v11 source-item target `section3_balance_choice_exists_with_finite_max_cost`. -/
theorem section3_balance_choice_exists_with_finite_max_costSpec_proof : section3_balance_choice_exists_with_finite_max_costSpec := by
  unfold section3_balance_choice_exists_with_finite_max_costSpec
  exact section3_balance_occurrence_runner_cost

/-- Transparent v11 source-item target for `appendix_naive_highest_bid_rule`. -/
def appendix_naive_highest_bid_ruleSpec : Prop :=
  ((∀ r : ℝ, 0 ≤ r → r ≤ 2 / 5 →
      (∫ _bidder in (1 / 10 + r)..1,
        MSVV07Appendix.printedPhaseOneAllocationRate r) = 1) ∧
    (∀ r bidder₁ bidder₂ : ℝ,
      0 ≤ r → r ≤ 2 / 5 →
      MSVV07Appendix.printedPhaseOneEligible r bidder₁ →
      MSVV07Appendix.printedPhaseOneEligible r bidder₂ →
        MSVV07Appendix.printedPhaseOneRawBid r bidder₁ =
            MSVV07Appendix.printedPhaseOneRawBid r bidder₂ ∧
          MSVV07Appendix.printedIndividualLeftover bidder₁
              (MSVV07Appendix.printedPhaseOneSpentBefore r bidder₁) =
            MSVV07Appendix.printedIndividualLeftover bidder₂
              (MSVV07Appendix.printedPhaseOneSpentBefore r bidder₂)) ∧
    (∫ bidder in (1 / 2 : ℝ)..1,
      MSVV07Appendix.printedPhaseTwoAllocationDensity bidder) = 1 ∧
    (∀ offset bidder competitor : ℝ,
      0 < MSVV07Appendix.printedPhaseTwoAllocationDensity bidder →
      ((1 / 2 ≤ competitor ∧ competitor ≤ 1) ∨ competitor = offset) →
        MSVV07Appendix.printedPhaseTwoRawBid offset competitor ≤
          MSVV07Appendix.printedPhaseTwoRawBid offset bidder) ∧
    (∀ offset bidder₁ bidder₂ : ℝ,
      0 ≤ offset → offset ≤ 1 / 10 →
      (1 / 2 ≤ bidder₁ ∧ bidder₁ ≤ 1) →
      (1 / 2 ≤ bidder₂ ∧ bidder₂ ≤ 1) →
        MSVV07Appendix.printedIndividualLeftover bidder₁
            (MSVV07Appendix.printedPhaseTwoSpentBefore offset bidder₁) =
          MSVV07Appendix.printedIndividualLeftover bidder₂
            (MSVV07Appendix.printedPhaseTwoSpentBefore offset bidder₂)) ∧
    (∀ progress owner : ℝ, 0 ≤ progress →
      MSVV07Appendix.printedPhaseThreeAllocationRate progress owner owner +
        MSVV07Appendix.printedPhaseThreeDiscardRate progress = 1) ∧
    ∀ progress owner : ℝ,
      (1 / 2 ≤ owner ∧ owner ≤ 1) →
      0 < MSVV07Appendix.printedPhaseThreeDiscardRate progress →
        MSVV07Appendix.printedPhaseThreeSpentBefore
          progress owner = 1)

/-- Checked proof endpoint for the v11 source-item target `appendix_naive_highest_bid_rule`. -/
theorem appendix_naive_highest_bid_ruleSpec_proof : appendix_naive_highest_bid_ruleSpec := by
  unfold appendix_naive_highest_bid_ruleSpec
  exact appendix_naive_highest_bid_fluid_rule

/-- Transparent v11 source-item target for `appendix_naive_three_phase_construction`. -/
def appendix_naive_three_phase_constructionSpec : Prop :=
  (0 < MSVV07Appendix.printedPhaseThreeResidualPerTail ∧
    (∀ owner : ℝ, (1 / 2 ≤ owner ∧ owner ≤ 1) →
      MSVV07Appendix.printedPhaseThreeSpentBefore
        MSVV07Appendix.printedPhaseThreeResidualPerTail owner = 1) ∧
    MSVV07Appendix.printedContinuousOnlineValue =
      9 / 10 - 1 / 2 * Real.log (9 / 5) ∧
    MSVV07Appendix.printedContinuousOfflineValue = 1)

/-- Checked proof endpoint for the v11 source-item target `appendix_naive_three_phase_construction`. -/
theorem appendix_naive_three_phase_constructionSpec_proof : appendix_naive_three_phase_constructionSpec := by
  unfold appendix_naive_three_phase_constructionSpec
  exact appendix_naive_three_phase_fluid_construction

/-- Transparent v11 source-item target for `appendix_naive_algorithm_revenue_formula`. -/
def appendix_naive_algorithm_revenue_formulaSpec : Prop :=
  (MSVV07Appendix.printedContinuousOnlineValue =
      9 / 10 - 1 / 2 * Real.log (9 / 5) ∧
    MSVV07Appendix.printedPhaseThreeServedMass =
      3 / 10 - 1 / 2 * Real.log (9 / 5) ∧
    0 < MSVV07Appendix.printedPhaseThreeServedMass ∧
    (2 / 5 : ℝ) + 2 * (1 / 10) = 3 / 5 ∧
    (3 / 5 : ℝ) ≠ 31 / 50)

/-- Checked proof endpoint for the v11 source-item target `appendix_naive_algorithm_revenue_formula`. -/
theorem appendix_naive_algorithm_revenue_formulaSpec_proof : appendix_naive_algorithm_revenue_formulaSpec := by
  unfold appendix_naive_algorithm_revenue_formulaSpec
  exact appendix_naive_algorithm_true_revenue_formula

/-- Transparent v11 source-item target for `appendix_naive_strict_ratio_conclusion`. -/
def appendix_naive_strict_ratio_conclusionSpec : Prop :=
  (MSVV07Appendix.printedContinuousOnlineValue /
        MSVV07Appendix.printedContinuousOfflineValue <
      paperMsvvRatio)

/-- Checked proof endpoint for the v11 source-item target `appendix_naive_strict_ratio_conclusion`. -/
theorem appendix_naive_strict_ratio_conclusionSpec_proof : appendix_naive_strict_ratio_conclusionSpec := by
  unfold appendix_naive_strict_ratio_conclusionSpec
  exact appendix_naive_true_ratio_conclusion

end

end PaperInterface
end MSVV07PaperFacing
end Online
end AppliedModelingLib

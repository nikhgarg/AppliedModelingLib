import MSVV07AdWords.PaperInterface
import MSVV07AdWords.ProofInterface

/-!
# Audit Ledger: MSVV07 AdWords

This ledger exposes importable endpoint wrappers for the post-verification
audit of Mehta, Saberi, Vazirani, and Vazirani, *AdWords and Generalized
Online Matching*. For the compact human-facing statement surface, read
`PaperInterface.lean`; the broader proof-route aliases below point to
`ProofInterface.lean` when they are not part of the compact paper-facing
surface.

Cached source text inventory checked by this audit:

- Problem definition, line 196: finite AdWords budgets, bids, assignments,
  feasibility, small-bids assumption, and competitive ratio.
- Section 3 definition, line 232: active slab and discretized Balance/MSVV
  scaled-bid rule.
- Section 4 Lemmas 1--3, lines 264, 300, and 456: factor-revealing LP proof
  route for equal bids. These source-route lemmas are formalized below;
  Theorem 8 is closed through the finite LP/dual-fitting route exposed below.
- Section 5 Lemmas 4--7, lines 548, 562, 586, and 597: tradeoff-revealing LP
  proof route. These source-route lemmas are formalized below as weak-duality,
  right-hand-side, per-query tradeoff, and summed-perturbation endpoints.
- Theorem 8, line 718: Balance/MSVV is `1 - 1/e` competitive in the
  small-bids limit.
- Section 6, lines 799--859: different budgets, nonexhaustive optimum,
  delayed entry, multiple slots, click-through rates, and next-price style
  effective charges.
- Theorem 9, line 897: no randomized online algorithm beats `1 - 1/e` for
  large-budget b-matching.
- Section 8, line 971: advertiser-specific weights via effective bids.

No numbered propositions or corollaries were found in the cached source text.
-/

open scoped BigOperators

namespace AppliedModelingLib
namespace Online
namespace MSVV07PaperFacing

open Proof

namespace AuditLedger

/-! ## Sections 2--3: paper model and Balance/MSVV rule -/

/-- Audit endpoint for the Section 2 finite AdWords model's feasible empty assignment. -/
theorem audit_section2_empty_assignment_feasible
    {Advertiser Query : Type*}
    [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (hbudget : ∀ a, 0 ≤ I.budget a) :
    paperFeasible I
      (AdWordsInstance.emptyAssignment :
        PaperAssignment Advertiser Query) := by
  exact section2_empty_assignment_feasible I hbudget

/-- Audit endpoint for Section 2 offline optimum existence on finite instances. -/
theorem audit_section2_offline_optimum_exists
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (hbudget : ∀ a, 0 ≤ I.budget a) :
    ∃ A : PaperAssignment Advertiser Query,
      I.IsOptimalAssignment A := by
  exact section2_offline_optimum_exists I hbudget

/-- Audit endpoint for the Section 2 fractional LP weak-duality support. -/
theorem audit_section2_fractional_lp_weak_duality
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Fintype Query]
    (I : PaperInstance Advertiser Query)
    (x : Advertiser → Query → ℝ)
    (alpha : Advertiser → ℝ) (beta : Query → ℝ)
    (hfeasible : I.FractionalFeasible x)
    (hdual : I.DualFeasible alpha beta) :
    paperFractionalRevenue I x ≤ I.dualObjective alpha beta := by
  exact section2_fractional_lp_weak_duality I x alpha beta hfeasible hdual

/-- Audit endpoint for Section 3: a Balance/MSVV maximizer exists when feasible. -/
theorem audit_section3_balance_choice_exists
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) (q : Query)
    (h : ∃ a, paperCanAssign I A q a) :
    ∃ a, paperIsBalanceChoice I A q a := by
  exact section3_balance_choice_exists I A q h

/-- Audit endpoint for Section 3: the canonical choice rule maximizes score. -/
theorem audit_section3_balance_choice_score_ge_of_can_assign
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) (q : Query)
    {chosen opt : Advertiser}
    (hchoice : I.balanceChoiceRule A q = some chosen)
    (hopt_can : paperCanAssign I A q opt) :
    paperBalanceScore I A opt q ≤ paperBalanceScore I A chosen q := by
  exact
    section3_balance_choice_score_ge_of_can_assign
      I A q hchoice hopt_can

/-- Audit endpoint for Section 3: the canonical Balance/MSVV run is feasible. -/
theorem audit_section3_balance_run_assignment_feasible
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    [DecidableEq Query]
    (I : PaperInstance Advertiser Query)
    (hbudget : ∀ a, 0 ≤ I.budget a)
    (history : List Query) :
    paperFeasible I (I.runAssignment I.balanceChoiceRule history) := by
  exact section3_balance_run_assignment_feasible I hbudget history

/-! ## Sections 4--5: source proof-route lemmas -/

/-- Audit endpoint for monotonicity of the paper tradeoff factor. -/
theorem audit_paperTradeoff_antitone :
    Antitone paperTradeoff := by
  exact paperTradeoff_antitone

/-- Audit endpoint for strict monotonicity of the paper tradeoff factor. -/
theorem audit_paperTradeoff_strictAnti :
    StrictAnti paperTradeoff := by
  exact paperTradeoff_strictAnti

/-- Audit endpoint for MSVV Section 4 Lemma 1. -/
theorem audit_section4_lemma1_balance_pays_no_later_slab
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
    section4_lemma1_balance_pays_no_later_slab
      psi hoptCurrent_le_type hchoice hequal_bids hbid_pos hpsi_strictAnti

/-- Audit endpoint for Section 4 Lemma 1 using the concrete Balance/MSVV choice rule. -/
theorem audit_section4_lemma1_balance_pays_no_later_spent_fraction_of_balance_choice
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) (q : Query)
    {opt chosen : Advertiser} {optType : ℝ}
    (hchoice : I.balanceChoiceRule A q = some chosen)
    (hopt_can : paperCanAssign I A q opt)
    (hoptCurrent_le_type : paperSpend I A opt / I.budget opt ≤ optType)
    (hequal_bids : I.bid chosen q = I.bid opt q)
    (hbid_pos : 0 < I.bid opt q) :
    paperSpend I A chosen / I.budget chosen ≤ optType := by
  exact
    section4_lemma1_balance_pays_no_later_spent_fraction_of_balance_choice
      I A q hchoice hopt_can hoptCurrent_le_type hequal_bids hbid_pos

/-- Audit endpoint for MSVV Section 4 Lemma 2. -/
theorem audit_section4_lemma2_factor_revealing_lp_constraint
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
    section4_lemma2_factor_revealing_lp_constraint
      N x beta i hprefix_cover hbeta_prefix

/-- Audit endpoint for MSVV Section 4 Lemma 3. -/
theorem audit_section4_lemma3_factor_revealing_lp_value_tends (N : ℝ) :
    Sequence.SeqTendsTo
      (fun k : ℕ => N * (1 - 1 / (k : ℝ)) ^ k)
      (N / Real.exp 1) := by
  exact section4_lemma3_factor_revealing_lp_value_tends N

/-- Audit endpoint for MSVV Section 4 Lemma 3 finite LP weak duality. -/
theorem audit_section4_lemma3_factor_revealing_lp_weak_duality
    {m : ℕ} (N : ℝ) {x y : Fin m → ℝ}
    (hx : MSVV07SourceLemmas.paperRoutePrimalFeasible N x)
    (hy : MSVV07SourceLemmas.paperRouteDualFeasible y) :
    MSVV07SourceLemmas.paperRoutePrimalObjective x ≤
      MSVV07SourceLemmas.paperRouteDualObjective N y := by
  exact section4_lemma3_factor_revealing_lp_weak_duality N hx hy

/-- Audit endpoint for MSVV Section 4 Lemma 3 primal witness nonnegativity. -/
theorem audit_section4_lemma3_primal_candidate_nonnegative
    {m : ℕ} {N : ℝ} (hN : 0 ≤ N) (i : Fin m) :
    0 ≤ MSVV07SourceLemmas.paperRoutePrimalCandidate (m := m) N i := by
  exact section4_lemma3_primal_candidate_nonnegative hN i

/-- Audit endpoint for MSVV Section 4 Lemma 3 dual witness nonnegativity. -/
theorem audit_section4_lemma3_dual_candidate_nonnegative
    {m : ℕ} (i : Fin m) :
    0 ≤ MSVV07SourceLemmas.paperRouteDualCandidate (m := m) i := by
  exact section4_lemma3_dual_candidate_nonnegative i

/-- Audit endpoint for MSVV Section 4 Lemma 3 primal row tightness. -/
theorem audit_section4_lemma3_primal_candidate_row_tight
    {m : ℕ} (N : ℝ) (i : Fin m) :
    MSVV07SourceLemmas.paperRouteLPRow
      (MSVV07SourceLemmas.paperRoutePrimalCandidate (m := m) N) i =
      MSVV07SourceLemmas.paperRouteRhs N i := by
  exact section4_lemma3_primal_candidate_row_tight N i

/-- Audit endpoint for MSVV Section 4 Lemma 3 primal witness feasibility. -/
theorem audit_section4_lemma3_primal_candidate_feasible
    {m : ℕ} {N : ℝ} (hN : 0 ≤ N) :
    MSVV07SourceLemmas.paperRoutePrimalFeasible (m := m) N
      (MSVV07SourceLemmas.paperRoutePrimalCandidate (m := m) N) := by
  exact section4_lemma3_primal_candidate_feasible hN

/-- Audit endpoint for MSVV Section 4 Lemma 3 dual row tightness. -/
theorem audit_section4_lemma3_dual_candidate_row_tight
    {m : ℕ} (i : Fin m) :
    MSVV07SourceLemmas.paperRouteDualRow
      (MSVV07SourceLemmas.paperRouteDualCandidate (m := m)) i =
      MSVV07SourceLemmas.paperRoutePrimalObjectiveCoeff (m := m) i := by
  exact section4_lemma3_dual_candidate_row_tight i

/-- Audit endpoint for MSVV Section 4 Lemma 3 dual witness feasibility. -/
theorem audit_section4_lemma3_dual_candidate_feasible
    {m : ℕ} :
    MSVV07SourceLemmas.paperRouteDualFeasible (m := m)
      (MSVV07SourceLemmas.paperRouteDualCandidate (m := m)) := by
  exact section4_lemma3_dual_candidate_feasible

/-- Audit endpoint for MSVV Section 4 Lemma 3 primal witness value. -/
theorem audit_section4_lemma3_primal_candidate_objective_value
    {m : ℕ} (N : ℝ) :
    MSVV07SourceLemmas.paperRoutePrimalObjective (m := m)
      (MSVV07SourceLemmas.paperRoutePrimalCandidate (m := m) N) =
      MSVV07SourceLemmas.factorRevealingLPValue m N := by
  exact section4_lemma3_primal_candidate_objective_value N

/-- Audit endpoint for MSVV Section 4 Lemma 3 dual witness value. -/
theorem audit_section4_lemma3_dual_candidate_objective_value
    {m : ℕ} (N : ℝ) :
    MSVV07SourceLemmas.paperRouteDualObjective (m := m) N
      (MSVV07SourceLemmas.paperRouteDualCandidate (m := m)) =
      MSVV07SourceLemmas.factorRevealingLPValue m N := by
  exact section4_lemma3_dual_candidate_objective_value N

/-- Audit endpoint for MSVV Section 4 Lemma 3 finite LP certificate optimality. -/
noncomputable def audit_section4_lemma3_factor_revealing_lp_optimal_from_certificate
    {m : ℕ} (N : ℝ)
    (hprimal :
      MSVV07SourceLemmas.paperRoutePrimalFeasible (m := m) N
        (MSVV07SourceLemmas.paperRoutePrimalCandidate (m := m) N))
    (hdual :
      MSVV07SourceLemmas.paperRouteDualFeasible (m := m)
        (MSVV07SourceLemmas.paperRouteDualCandidate (m := m)))
    (hprimal_value :
      MSVV07SourceLemmas.paperRoutePrimalObjective (m := m)
        (MSVV07SourceLemmas.paperRoutePrimalCandidate (m := m) N) =
        MSVV07SourceLemmas.factorRevealingLPValue m N)
    (hdual_value :
      MSVV07SourceLemmas.paperRouteDualObjective (m := m) N
        (MSVV07SourceLemmas.paperRouteDualCandidate (m := m)) =
        MSVV07SourceLemmas.factorRevealingLPValue m N) :
    Optimization.UpperBoundCertificate
      (α := Fin m → ℝ)
      (MSVV07SourceLemmas.paperRoutePrimalFeasible (m := m) N)
      (MSVV07SourceLemmas.paperRoutePrimalObjective (m := m))
      (MSVV07SourceLemmas.factorRevealingLPValue m N) :=
  section4_lemma3_factor_revealing_lp_optimal_from_certificate
    N hprimal hdual hprimal_value hdual_value

/--
Audit endpoint for MSVV Section 4 Lemma 3 finite LP optimality from row/value
certificates for the displayed `x*`,`y*` witnesses.
-/
noncomputable def audit_section4_lemma3_factor_revealing_lp_optimal_from_row_certificates
    {m : ℕ} {N : ℝ} (hN : 0 ≤ N)
    (hprimal_rows :
      ∀ i,
        MSVV07SourceLemmas.paperRouteLPRow
          (MSVV07SourceLemmas.paperRoutePrimalCandidate (m := m) N) i ≤
          MSVV07SourceLemmas.paperRouteRhs N i)
    (hdual_rows :
      ∀ i,
        MSVV07SourceLemmas.paperRoutePrimalObjectiveCoeff (m := m) i ≤
          MSVV07SourceLemmas.paperRouteDualRow
            (MSVV07SourceLemmas.paperRouteDualCandidate (m := m)) i)
    (hprimal_value :
      MSVV07SourceLemmas.paperRoutePrimalObjective (m := m)
        (MSVV07SourceLemmas.paperRoutePrimalCandidate (m := m) N) =
        MSVV07SourceLemmas.factorRevealingLPValue m N)
    (hdual_value :
      MSVV07SourceLemmas.paperRouteDualObjective (m := m) N
        (MSVV07SourceLemmas.paperRouteDualCandidate (m := m)) =
        MSVV07SourceLemmas.factorRevealingLPValue m N) :
    Optimization.UpperBoundCertificate
      (α := Fin m → ℝ)
      (MSVV07SourceLemmas.paperRoutePrimalFeasible (m := m) N)
      (MSVV07SourceLemmas.paperRoutePrimalObjective (m := m))
      (MSVV07SourceLemmas.factorRevealingLPValue m N) :=
  section4_lemma3_factor_revealing_lp_optimal_from_row_certificates
    hN hprimal_rows hdual_rows hprimal_value hdual_value

/--
Audit endpoint for MSVV Section 4 Lemma 3 finite LP optimality for the
displayed geometric `x*`,`y*` witnesses.
-/
noncomputable def audit_section4_lemma3_factor_revealing_lp_optimal
    {m : ℕ} {N : ℝ} (hN : 0 ≤ N) :
    Optimization.UpperBoundCertificate
      (α := Fin m → ℝ)
      (MSVV07SourceLemmas.paperRoutePrimalFeasible (m := m) N)
      (MSVV07SourceLemmas.paperRoutePrimalObjective (m := m))
      (MSVV07SourceLemmas.factorRevealingLPValue m N) :=
  section4_lemma3_factor_revealing_lp_optimal hN

/--
Audit endpoint for MSVV Section 4 Lemma 3 direct optimizer statement for the
displayed geometric primal witness.
-/
theorem audit_section4_lemma3_factor_revealing_lp_primal_candidate_is_maximizer
    {m : ℕ} {N : ℝ} (hN : 0 ≤ N) :
    Optimization.IsMaximizerOn
      (MSVV07SourceLemmas.paperRoutePrimalFeasible (m := m) N)
      (MSVV07SourceLemmas.paperRoutePrimalObjective (m := m))
      (MSVV07SourceLemmas.paperRoutePrimalCandidate (m := m) N) := by
  exact section4_lemma3_factor_revealing_lp_primal_candidate_is_maximizer hN

/--
Audit endpoint for MSVV Section 4 Lemma 3 direct universal upper bound for the
finite factor-revealing LP.
-/
theorem audit_section4_lemma3_factor_revealing_lp_upper_bound
    {m : ℕ} {N : ℝ} (hN : 0 ≤ N)
    (x : Fin m → ℝ)
    (hx :
      MSVV07SourceLemmas.paperRoutePrimalFeasible (m := m) N x) :
    MSVV07SourceLemmas.paperRoutePrimalObjective (m := m) x ≤
      MSVV07SourceLemmas.factorRevealingLPValue m N := by
  exact section4_lemma3_factor_revealing_lp_upper_bound hN x hx

/-- Audit endpoint for MSVV Section 5 Lemma 4. -/
theorem audit_section5_lemma4_dual_optimal_from_primal_dual_match
    {Primal Dual : Type*}
    (primalFeasible : Primal → Prop) (dualFeasible : Dual → Prop)
    (primalObjective : Primal → ℝ) (dualObjective : Dual → ℝ)
    (hweak :
      ∀ primal dual,
        primalFeasible primal → dualFeasible dual →
          primalObjective primal ≤ dualObjective dual)
    {a : Primal} {ystar : Dual}
    (ha : primalFeasible a)
    (hystar : dualFeasible ystar)
    (hvalue : primalObjective a = dualObjective ystar) :
    ∀ y, dualFeasible y → dualObjective ystar ≤ dualObjective y := by
  exact
    section5_lemma4_dual_optimal_from_primal_dual_match
      primalFeasible dualFeasible primalObjective dualObjective hweak
      ha hystar hvalue

/-- Audit endpoint for MSVV Section 5 Lemma 4 in `StandardMaxLP` form. -/
theorem audit_section5_lemma4_standardMaxLP_dual_yStar_optimal
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : Optimization.StandardMaxLP ι κ)
    {a : ι → ℝ} {ystar : κ → ℝ}
    (ha : P.PrimalFeasible a)
    (hystar : P.DualFeasible ystar)
    (hvalue : P.primalObjective a = P.dualObjective ystar) :
    Optimization.IsMinimizerOn P.DualFeasible P.dualObjective ystar := by
  exact section5_lemma4_standardMaxLP_dual_yStar_optimal P ha hystar hvalue

/-- Audit endpoint for MSVV Section 5 Lemma 4's unchanged-dual-constraints step. -/
theorem audit_section5_lemma4_dual_feasible_of_same_A_c
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : κ → ι → ℝ) (b l : κ → ℝ) (c : ι → ℝ)
    {ystar : κ → ℝ}
    (hystar :
      (Optimization.StandardMaxLP.mk A b c).DualFeasible ystar) :
    (Optimization.StandardMaxLP.mk A l c).DualFeasible ystar := by
  exact section5_lemma4_dual_feasible_of_same_A_c A b l c hystar

/-- Audit endpoint for MSVV Section 5 Lemma 5. -/
theorem audit_section5_lemma5_tradeoff_rhs_eq_base_add_delta
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
    section5_lemma5_tradeoff_rhs_eq_base_add_delta
      N alpha beta i hbeta_prefix

/-- Audit endpoint for MSVV Section 5 Lemma 6. -/
theorem audit_section5_lemma6_per_query_tradeoff
    {Slab : Type*} [Preorder Slab]
    (psi : Slab → ℝ) {queryType optCurrentSlab algSlab : Slab}
    {optBid algBid : ℝ}
    (hoptCurrent_le_type : optCurrentSlab ≤ queryType)
    (hpsi_antitone : Antitone psi)
    (hoptBid_nonneg : 0 ≤ optBid)
    (hchoice : optBid * psi optCurrentSlab ≤ algBid * psi algSlab) :
    optBid * psi queryType ≤ algBid * psi algSlab := by
  exact
    section5_lemma6_per_query_tradeoff
      psi hoptCurrent_le_type hpsi_antitone hoptBid_nonneg hchoice

/-- Audit endpoint for Lemma 6 using the concrete Balance/MSVV choice rule. -/
theorem audit_section5_lemma6_per_query_tradeoff_of_balance_choice
    {Advertiser Query Slab : Type*}
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    [Preorder Slab]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) (q : Query)
    (psi : Slab → ℝ)
    {opt chosen : Advertiser} {queryType optCurrentSlab algSlab : Slab}
    (hchoice : I.balanceChoiceRule A q = some chosen)
    (hopt_can : paperCanAssign I A q opt)
    (hoptCurrent_le_type : optCurrentSlab ≤ queryType)
    (hpsi_antitone : Antitone psi)
    (hoptBid_nonneg : 0 ≤ I.bid opt q)
    (hopt_score :
      paperBalanceScore I A opt q = I.bid opt q * psi optCurrentSlab)
    (hchosen_score :
      paperBalanceScore I A chosen q = I.bid chosen q * psi algSlab) :
    I.bid opt q * psi queryType ≤ I.bid chosen q * psi algSlab := by
  exact
    proof_section5_lemma6_per_query_tradeoff_of_balance_choice
      I A q psi hchoice hopt_can hoptCurrent_le_type hpsi_antitone
      hoptBid_nonneg hopt_score hchosen_score

/-- Audit endpoint for Lemma 6 in concrete spent-fraction form. -/
theorem audit_section5_lemma6_per_query_tradeoff_of_balance_choice_spent_fraction
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) (q : Query)
    {opt chosen : Advertiser} {queryType : ℝ}
    (hbid : I.NonnegativeBids)
    (hchoice : I.balanceChoiceRule A q = some chosen)
    (hopt_can : paperCanAssign I A q opt)
    (hoptCurrent_le_type : paperSpend I A opt / I.budget opt ≤ queryType) :
    I.bid opt q * paperTradeoff queryType ≤
      I.bid chosen q *
        paperTradeoff (paperSpend I A chosen / I.budget chosen) := by
  exact
    proof_section5_lemma6_per_query_tradeoff_of_balance_choice_spent_fraction
      I A q hbid hchoice hopt_can hoptCurrent_le_type

/-- Audit endpoint for MSVV Section 5 Lemma 7. -/
theorem audit_section5_lemma7_weighted_perturbation_bound
    {m Query : Type*} [Fintype m] [Fintype Query]
    (psi alpha beta : m → ℝ) (opt alg : Query → ℝ)
    (queryType querySlab : Query → m) (finalSlabError : ℝ)
    (htradeoff_sum :
      (∑ q : Query,
        (opt q * psi (queryType q) - alg q * psi (querySlab q))) ≤ 0)
    (hopt_accounting :
      (∑ q : Query, opt q * psi (queryType q)) =
        ∑ i : m, psi i * alpha i)
    (halg_accounting :
      (∑ q : Query, alg q * psi (querySlab q)) ≤
        (∑ i : m, psi i * beta i) + finalSlabError) :
    (∑ i : m, psi i * (alpha i - beta i)) ≤ finalSlabError := by
  exact
    section5_lemma7_weighted_perturbation_bound
      psi alpha beta opt alg queryType querySlab finalSlabError
      htradeoff_sum hopt_accounting halg_accounting

/-- Audit endpoint for MSVV Section 5 Lemma 7's paper-shaped `N/k` corollary. -/
theorem audit_section5_lemma7_weighted_perturbation_bound_by_N_div_k
    {m Query : Type*} [Fintype m] [Fintype Query]
    (psi alpha beta : m → ℝ) (opt alg : Query → ℝ)
    (queryType querySlab : Query → m) (finalSlabError N : ℝ) (k : ℕ)
    (htradeoff_sum :
      (∑ q : Query,
        (opt q * psi (queryType q) - alg q * psi (querySlab q))) ≤ 0)
    (hopt_accounting :
      (∑ q : Query, opt q * psi (queryType q)) =
        ∑ i : m, psi i * alpha i)
    (halg_accounting :
      (∑ q : Query, alg q * psi (querySlab q)) ≤
        (∑ i : m, psi i * beta i) + finalSlabError)
    (hfinal :
      finalSlabError ≤ N / (k : ℝ)) :
    (∑ i : m, psi i * (alpha i - beta i)) ≤ N / (k : ℝ) := by
  exact
    proof_section5_lemma7_weighted_perturbation_bound_by_N_div_k
      psi alpha beta opt alg queryType querySlab finalSlabError N k
      htradeoff_sum hopt_accounting halg_accounting hfinal

/-- Audit endpoint for MSVV Section 5 Lemma 7's exact `N/k` accounting form. -/
theorem audit_section5_lemma7_weighted_perturbation_bound_exact_N_div_k
    {m Query : Type*} [Fintype m] [Fintype Query]
    (psi alpha beta : m → ℝ) (opt alg : Query → ℝ)
    (queryType querySlab : Query → m) (N : ℝ) (k : ℕ)
    (htradeoff_sum :
      (∑ q : Query,
        (opt q * psi (queryType q) - alg q * psi (querySlab q))) ≤ 0)
    (hopt_accounting :
      (∑ q : Query, opt q * psi (queryType q)) =
        ∑ i : m, psi i * alpha i)
    (halg_accounting_N_div_k :
      (∑ q : Query, alg q * psi (querySlab q)) ≤
        (∑ i : m, psi i * beta i) + N / (k : ℝ)) :
    (∑ i : m, psi i * (alpha i - beta i)) ≤ N / (k : ℝ) := by
  exact
    proof_section5_lemma7_weighted_perturbation_bound_exact_N_div_k
      psi alpha beta opt alg queryType querySlab N k htradeoff_sum
      hopt_accounting halg_accounting_N_div_k

/--
Audit endpoint for the pointwise-to-global summation step in MSVV Section 5
Lemma 7.
-/
theorem audit_section5_lemma7_tradeoff_sum_of_pointwise
    {Query : Type*} [Fintype Query] (w : Query → ℝ)
    (h : ∀ q, w q ≤ 0) :
    (∑ q : Query, w q) ≤ 0 := by
  exact section5_lemma7_tradeoff_sum_of_pointwise w h

/--
Audit endpoint for the OPT type-fiber accounting step in MSVV Section 5
Lemma 7.
-/
theorem audit_section5_lemma7_opt_accounting_of_type_fibers
    {m Query : Type*} [Fintype m] [Fintype Query] [DecidableEq m]
    (psi alpha : m → ℝ) (opt : Query → ℝ) (queryType : Query → m)
    (hα :
      ∀ i : m,
        (∑ q ∈ (Finset.univ : Finset Query).filter
          (fun q => queryType q = i), opt q) = alpha i) :
    (∑ q : Query, opt q * psi (queryType q)) =
      ∑ i : m, psi i * alpha i := by
  exact
    section5_lemma7_opt_accounting_of_type_fibers
      psi alpha opt queryType hα

/--
Audit endpoint for the ALG slab-fiber accounting step in MSVV Section 5
Lemma 7.
-/
theorem audit_section5_lemma7_alg_accounting_of_slab_fibers_and_final_error
    {m Query : Type*} [Fintype m] [Fintype Query] [DecidableEq m]
    (psi beta : m → ℝ) (alg : Query → ℝ)
    (querySlab : Query → m) (finalSlabError : ℝ)
    (hpsi_nonneg : ∀ i, 0 ≤ psi i)
    (hβ :
      ∀ i : m,
        (∑ q ∈ (Finset.univ : Finset Query).filter
          (fun q => querySlab q = i), alg q) ≤ beta i)
    (hfinal_nonneg : 0 ≤ finalSlabError) :
    (∑ q : Query, alg q * psi (querySlab q)) ≤
      (∑ i : m, psi i * beta i) + finalSlabError := by
  exact
    section5_lemma7_alg_accounting_of_slab_fibers_and_final_error
      psi beta alg querySlab finalSlabError hpsi_nonneg hβ hfinal_nonneg

/--
Audit endpoint for Lemma 7's `N/k` perturbation bound from pointwise tradeoff
and fiber accounting facts.
-/
theorem audit_section5_lemma7_weighted_perturbation_bound_exact_N_div_k_from_pointwise_fibers
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
    proof_section5_lemma7_weighted_perturbation_bound_exact_N_div_k_from_pointwise_fibers
      psi alpha beta opt alg queryType querySlab N k
      hpointwise hα hpsi_nonneg hβ hfinal_nonneg

/--
Audit endpoint for concrete aggregate MSVV accounting with explicit finite
small-bids error.
-/
theorem audit_section5_balance_msvv_scaled_dual_objective_le_revenue_add_explicit_error
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : PaperInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    (hnodup : history.Nodup)
    (hcover : AdWordsInstance.historyFinset history = Finset.univ)
    {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hsmall : paperSmallBids I epsilon) :
    let A := I.runAssignment I.balanceChoiceRule history
    paperMsvvRatio *
      I.dualObjective (I.msvvNormalizedAlphaFromAssignment A)
        (I.maxSlackBeta (I.msvvNormalizedAlphaFromAssignment A)) ≤
      paperRevenue I A +
        (I.historyMaxBidAlphaErrorSum epsilon history +
          I.historyMaxBidErrorSum epsilon history) := by
  exact
    section5_balance_msvv_scaled_dual_objective_le_revenue_add_explicit_error
      I hbid hbudget history hnodup hcover hepsilon hsmall

/-- Audit endpoint for Theorem 8's source dual-perturbation algebra. -/
theorem audit_theorem8_delta_dot_y_eq_weighted_perturbation
    {m : ℕ} (alpha beta y : Fin m → ℝ) :
    (∑ i : Fin m,
      y i * MSVV07SourceLemmas.paperRouteDelta alpha beta i) =
      ∑ i : Fin m,
        MSVV07SourceLemmas.paperRoutePsiFromDual y i *
          (alpha i - beta i) := by
  exact theorem8_delta_dot_y_eq_weighted_perturbation alpha beta y

/-- Audit endpoint for Theorem 8's dual-induced tradeoff monotonicity. -/
theorem audit_theorem8_dual_induced_tradeoff_antitone
    {m : ℕ} (y : Fin m → ℝ) (hy : ∀ i, 0 ≤ y i) :
    Antitone (MSVV07SourceLemmas.paperRoutePsiFromDual y) := by
  exact theorem8_dual_induced_tradeoff_antitone y hy

/-- Audit endpoint for Theorem 8's displayed-dual-candidate tradeoff monotonicity. -/
theorem audit_theorem8_dual_candidate_induced_tradeoff_antitone
    {m : ℕ} :
    Antitone
      (MSVV07SourceLemmas.paperRoutePsiFromDual (m := m)
        MSVV07SourceLemmas.paperRouteDualCandidate) := by
  exact theorem8_dual_candidate_induced_tradeoff_antitone

/-- Audit endpoint for nonnegativity of Theorem 8's displayed-dual-candidate `ψ`. -/
theorem audit_theorem8_dual_candidate_psi_nonnegative
    {m : ℕ} :
    ∀ i : Fin m,
      0 ≤ MSVV07SourceLemmas.paperRoutePsiCandidate (m := m) i := by
  exact theorem8_dual_candidate_psi_nonnegative

/-- Audit endpoint for Theorem 8's `ψ` closed form induced by `y*`. -/
theorem audit_theorem8_dual_candidate_psi_closed_form
    {m : ℕ} (i : Fin m) :
    MSVV07SourceLemmas.paperRoutePsiCandidate (m := m) i =
      1 - (1 - 1 / (((m + 1 : ℕ) : ℝ))) ^ (m - i.val) := by
  exact theorem8_dual_candidate_psi_closed_form i

/-- Audit endpoint for Theorem 8's source-route finite `N/e + N/k` value bound. -/
theorem audit_theorem8_source_route_dual_value_bound
    {m : ℕ} (N : ℝ) (k : ℕ)
    (alpha beta y l : Fin m → ℝ)
    (hl :
      ∀ i, l i =
        MSVV07SourceLemmas.paperRouteRhs N i +
          MSVV07SourceLemmas.paperRouteDelta alpha beta i)
    (hbase :
      MSVV07SourceLemmas.paperRouteDualObjective N y ≤ N / Real.exp 1)
    (hperturb :
      (∑ i : Fin m,
        MSVV07SourceLemmas.paperRoutePsiFromDual y i *
          (alpha i - beta i)) ≤ N / (k : ℝ)) :
    (∑ i : Fin m, l i * y i) ≤ N / Real.exp 1 + N / (k : ℝ) := by
  exact
    theorem8_source_route_dual_value_bound
      N k alpha beta y l hl hbase hperturb

/-- Audit endpoint for Theorem 8's exact finite source-route `y*` value bound. -/
theorem audit_theorem8_source_route_dual_candidate_value_bound_exact_base
    {m : ℕ} (N : ℝ) (k : ℕ)
    (alpha beta l : Fin m → ℝ)
    (hl :
      ∀ i, l i =
        MSVV07SourceLemmas.paperRouteRhs N i +
          MSVV07SourceLemmas.paperRouteDelta alpha beta i)
    (hperturb :
      (∑ i : Fin m,
        MSVV07SourceLemmas.paperRoutePsiCandidate i *
          (alpha i - beta i)) ≤ N / (k : ℝ)) :
    (∑ i : Fin m,
      l i * MSVV07SourceLemmas.paperRouteDualCandidate i) ≤
      MSVV07SourceLemmas.factorRevealingLPValue m N + N / (k : ℝ) := by
  exact
    theorem8_source_route_dual_candidate_value_bound_exact_base
      N k alpha beta l hl hperturb

/-- Audit endpoint for source-route dual feasibility of the displayed `y*`. -/
theorem audit_theorem8_source_route_dual_candidate_tradeoff_feasible
    {m : ℕ} (l : Fin m → ℝ) :
    (MSVV07SourceLemmas.tradeoffRevealingLP
      (m := m) MSVV07SourceLemmas.paperRoutePrimalObjectiveCoeff l).DualFeasible
      MSVV07SourceLemmas.paperRouteDualCandidate := by
  exact theorem8_source_route_dual_candidate_tradeoff_feasible l

/-- Audit endpoint for Theorem 8's source-route tradeoff-LP primal upper bound. -/
theorem audit_theorem8_source_route_tradeoff_lp_upper_bound
    {m : ℕ} (N : ℝ) (k : ℕ)
    (c alpha beta y l : Fin m → ℝ)
    (hy : (MSVV07SourceLemmas.tradeoffRevealingLP c l).DualFeasible y)
    (hl :
      ∀ i, l i =
        MSVV07SourceLemmas.paperRouteRhs N i +
          MSVV07SourceLemmas.paperRouteDelta alpha beta i)
    (hbase :
      MSVV07SourceLemmas.paperRouteDualObjective N y ≤ N / Real.exp 1)
    (hperturb :
      (∑ i : Fin m,
        MSVV07SourceLemmas.paperRoutePsiFromDual y i *
          (alpha i - beta i)) ≤ N / (k : ℝ))
    {x : Fin m → ℝ}
    (hx : (MSVV07SourceLemmas.tradeoffRevealingLP c l).PrimalFeasible x) :
    (MSVV07SourceLemmas.tradeoffRevealingLP c l).primalObjective x ≤
      N / Real.exp 1 + N / (k : ℝ) := by
  exact
    theorem8_source_route_tradeoff_lp_upper_bound
      N k c alpha beta y l hy hl hbase hperturb hx

/-- Audit endpoint for Theorem 8's exact finite source-route LP upper bound. -/
theorem audit_theorem8_source_route_tradeoff_lp_upper_bound_exact_base
    {m : ℕ} (N : ℝ) (k : ℕ)
    (alpha beta l : Fin m → ℝ)
    (hl :
      ∀ i, l i =
        MSVV07SourceLemmas.paperRouteRhs N i +
          MSVV07SourceLemmas.paperRouteDelta alpha beta i)
    (hperturb :
      (∑ i : Fin m,
        MSVV07SourceLemmas.paperRoutePsiCandidate i *
          (alpha i - beta i)) ≤ N / (k : ℝ))
    {x : Fin m → ℝ}
    (hx :
      (MSVV07SourceLemmas.tradeoffRevealingLP
        (m := m) MSVV07SourceLemmas.paperRoutePrimalObjectiveCoeff l).PrimalFeasible
        x) :
    (MSVV07SourceLemmas.tradeoffRevealingLP
      (m := m) MSVV07SourceLemmas.paperRoutePrimalObjectiveCoeff l).primalObjective x ≤
      MSVV07SourceLemmas.factorRevealingLPValue m N + N / (k : ℝ) := by
  exact
    theorem8_source_route_tradeoff_lp_upper_bound_exact_base
      N k alpha beta l hl hperturb hx

/--
Audit endpoint for Theorem 8's source-route exact finite LP upper bound from
query-accounting hypotheses.
-/
theorem audit_theorem8_source_route_tradeoff_lp_upper_bound_from_query_accounting
    {m : ℕ} {Query : Type*} [Fintype Query]
    (N : ℝ) (k : ℕ)
    (alpha beta l : Fin m → ℝ)
    (opt alg : Query → ℝ)
    (queryType querySlab : Query → Fin m)
    (hl :
      ∀ i, l i =
        MSVV07SourceLemmas.paperRouteRhs N i +
          MSVV07SourceLemmas.paperRouteDelta alpha beta i)
    (htradeoff_sum :
      (∑ q : Query,
        (opt q * MSVV07SourceLemmas.paperRoutePsiCandidate (queryType q) -
          alg q * MSVV07SourceLemmas.paperRoutePsiCandidate (querySlab q))) ≤ 0)
    (hopt_accounting :
      (∑ q : Query,
        opt q * MSVV07SourceLemmas.paperRoutePsiCandidate (queryType q)) =
        ∑ i : Fin m, MSVV07SourceLemmas.paperRoutePsiCandidate i * alpha i)
    (halg_accounting_N_div_k :
      (∑ q : Query,
        alg q * MSVV07SourceLemmas.paperRoutePsiCandidate (querySlab q)) ≤
        (∑ i : Fin m, MSVV07SourceLemmas.paperRoutePsiCandidate i * beta i) +
          N / (k : ℝ))
    {x : Fin m → ℝ}
    (hx :
      (MSVV07SourceLemmas.tradeoffRevealingLP
        (m := m) MSVV07SourceLemmas.paperRoutePrimalObjectiveCoeff l).PrimalFeasible
        x) :
    (MSVV07SourceLemmas.tradeoffRevealingLP
      (m := m) MSVV07SourceLemmas.paperRoutePrimalObjectiveCoeff l).primalObjective x ≤
      MSVV07SourceLemmas.factorRevealingLPValue m N + N / (k : ℝ) := by
  exact
    theorem8_source_route_tradeoff_lp_upper_bound_from_query_accounting
      N k alpha beta l opt alg queryType querySlab hl
      htradeoff_sum hopt_accounting halg_accounting_N_div_k hx

/--
Audit endpoint for Theorem 8's source-route exact finite LP upper bound from
pointwise tradeoff and fiber accounting.
-/
theorem audit_theorem8_source_route_tradeoff_lp_upper_bound_from_pointwise_fibers
    {m : ℕ} {Query : Type*} [Fintype Query]
    (N : ℝ) (k : ℕ)
    (alpha beta : Fin m → ℝ)
    (opt alg : Query → ℝ)
    (queryType querySlab : Query → Fin m)
    (hpointwise :
      ∀ q : Query,
        opt q * MSVV07SourceLemmas.paperRoutePsiCandidate (m := m)
            (queryType q) -
          alg q * MSVV07SourceLemmas.paperRoutePsiCandidate (m := m)
            (querySlab q) ≤ 0)
    (hα :
      ∀ i : Fin m,
        (∑ q ∈ (Finset.univ : Finset Query).filter
          (fun q => queryType q = i), opt q) = alpha i)
    (hβ :
      ∀ i : Fin m,
        (∑ q ∈ (Finset.univ : Finset Query).filter
          (fun q => querySlab q = i), alg q) ≤ beta i)
    (hfinal_nonneg : 0 ≤ N / (k : ℝ))
    {x : Fin m → ℝ}
    (hx :
      (MSVV07SourceLemmas.tradeoffRevealingLP
        (m := m) MSVV07SourceLemmas.paperRoutePrimalObjectiveCoeff
        (fun i => MSVV07SourceLemmas.paperRouteRhs N i +
          MSVV07SourceLemmas.paperRouteDelta alpha beta i)).PrimalFeasible
        x) :
    (MSVV07SourceLemmas.tradeoffRevealingLP
      (m := m) MSVV07SourceLemmas.paperRoutePrimalObjectiveCoeff
      (fun i => MSVV07SourceLemmas.paperRouteRhs N i +
        MSVV07SourceLemmas.paperRouteDelta alpha beta i)).primalObjective x ≤
      MSVV07SourceLemmas.factorRevealingLPValue m N + N / (k : ℝ) := by
  exact
    theorem8_source_route_tradeoff_lp_upper_bound_from_pointwise_fibers
      N k alpha beta opt alg queryType querySlab
      hpointwise hα hβ hfinal_nonneg hx

/-! ## Theorem 8: Balance/MSVV competitive ratio -/

/-- Audit endpoint for Theorem 8's finite explicit-error form. -/
theorem audit_theorem8_finite_explicit_error
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : PaperInstance Advertiser Query)
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
        I.offlineOptimumValue (fun a => (hbudget a).le) ≤
      paperRevenue I (I.runAssignment I.balanceChoiceRule history) +
        epsilon * (Real.exp 1 + 1) *
          (∑ q : Query, I.maxBidForQuery q) := by
  exact
    theorem8_finite_explicit_error I hbid hbudget history hnodup hcover
      hepsilon hepsilon_le_one hsmall

/-- Audit endpoint for the source-shaped asymptotic Theorem 8 guarantee. -/
theorem audit_theorem8_balance_msvv_competitive_of_small_bids_limit_family
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
  exact theorem8_balance_msvv_competitive_of_small_bids_limit_family
    n I epsilon hbid hbudget hepsilon hepsilon_le_one hsmall
    herror_tendsTo_zero

/-! ## Section 6 and Section 8: effective-bid extensions -/

/--
Audit endpoint for Section 6 items 1--2: different budgets and nonexhaustive
optima are covered by the base finite explicit Theorem 8 statement.
-/
theorem audit_section6_different_budgets_and_nonexhaustive_optimum_theorem8_finite_explicit_error
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : PaperInstance Advertiser Query)
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
        I.offlineOptimumValue (fun a => (hbudget a).le) ≤
      paperRevenue I (I.runAssignment I.balanceChoiceRule history) +
        epsilon * (Real.exp 1 + 1) *
          (∑ q : Query, I.maxBidForQuery q) := by
  exact
    section6_different_budgets_and_nonexhaustive_optimum_theorem8_finite_explicit_error
      I hbid hbudget history hnodup hcover hepsilon hepsilon_le_one hsmall

/-- Audit endpoint for Section 6: arbitrary effective charges preserve small bids. -/
theorem audit_section6_effective_bids_small_bids
    {Advertiser Query : Type*}
    (I : PaperInstance Advertiser Query)
    (effectiveBid : Advertiser → Query → ℝ) {epsilon : ℝ}
    (hsmall : ∀ a q, effectiveBid a q ≤ epsilon * I.budget a) :
    paperSmallBids (I.withEffectiveBids effectiveBid) epsilon := by
  exact section6_effective_bids_small_bids I effectiveBid hsmall

/-- Audit endpoint for Section 6: CTR effective bids preserve small bids. -/
theorem audit_section6_click_through_rates_small_bids
    {Advertiser Query : Type*}
    (I : PaperInstance Advertiser Query)
    (ctr : Advertiser → Query → ℝ) {epsilon : ℝ}
    (hbid : I.NonnegativeBids)
    (hctr_le_one : ∀ a q, ctr a q ≤ 1)
    (hsmall : paperSmallBids I epsilon) :
    paperSmallBids (I.withClickThroughRates ctr) epsilon := by
  exact section6_click_through_rates_small_bids I ctr hbid hctr_le_one hsmall

/-- Audit endpoint for Section 6: availability masks preserve small bids. -/
theorem audit_section6_availability_small_bids
    {Advertiser Query : Type*}
    (I : PaperInstance Advertiser Query)
    (available : Advertiser → Query → Prop) {epsilon : ℝ}
    [∀ a q, Decidable (available a q)]
    (hepsilon : 0 ≤ epsilon)
    (hbudget : I.PositiveBudgets)
    (hsmall : paperSmallBids I epsilon) :
    paperSmallBids (I.withAvailability available) epsilon := by
  exact section6_availability_small_bids I available hepsilon hbudget hsmall

/-- Audit endpoint for Section 6: multiple slots reduce to slot-query IDs. -/
theorem audit_section6_multiple_slots_small_bids
    {Advertiser Query : Type*}
    (I : PaperInstance Advertiser Query) {epsilon : ℝ}
    (Slot : Query → Type*)
    (hsmall : paperSmallBids I epsilon) :
    paperSmallBids (I.withSlots Slot) epsilon := by
  exact section6_multiple_slots_small_bids I Slot hsmall

/-- Audit endpoint for Section 8: advertiser-weighted bids preserve small bids. -/
theorem audit_section8_weighted_bids_small_bids
    {Advertiser Query : Type*}
    (I : PaperInstance Advertiser Query)
    (weight : Advertiser → ℝ) {epsilon : ℝ}
    (hbid : I.NonnegativeBids)
    (hweight_le_one : ∀ a, weight a ≤ 1)
    (hsmall : paperSmallBids I epsilon) :
    paperSmallBids (I.withAdvertiserWeights weight) epsilon := by
  exact section8_weighted_bids_small_bids I weight hbid hweight_le_one hsmall

/--
Audit endpoint for Section 6: arbitrary effective charges inherit the finite
explicit Theorem 8 guarantee.
-/
theorem audit_section6_effective_bids_theorem8_finite_explicit_error
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : PaperInstance Advertiser Query)
    (effectiveBid : Advertiser → Query → ℝ)
    (hbid : ∀ a q, 0 ≤ effectiveBid a q)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    (hnodup : history.Nodup)
    (hcover : AdWordsInstance.historyFinset history = Finset.univ)
    {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hepsilon_le_one : epsilon ≤ 1)
    (hsmall : ∀ a q, effectiveBid a q ≤ epsilon * I.budget a) :
    paperMsvvRatio *
        (I.withEffectiveBids effectiveBid).offlineOptimumValue
          (fun a => (hbudget a).le) ≤
      paperRevenue (I.withEffectiveBids effectiveBid)
        ((I.withEffectiveBids effectiveBid).runAssignment
          (I.withEffectiveBids effectiveBid).balanceChoiceRule history) +
        epsilon * (Real.exp 1 + 1) *
          (∑ q : Query, (I.withEffectiveBids effectiveBid).maxBidForQuery q) := by
  exact
    section6_effective_bids_theorem8_finite_explicit_error
      I effectiveBid hbid hbudget history hnodup hcover hepsilon
      hepsilon_le_one hsmall

/--
Audit endpoint for Section 6: next-highest-bid charges over all bidders inherit
the finite explicit Theorem 8 guarantee when those charges are small.
-/
theorem audit_section6_next_highest_bid_all_theorem8_finite_explicit_error
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : PaperInstance Advertiser Query)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    (hnodup : history.Nodup)
    (hcover : AdWordsInstance.historyFinset history = Finset.univ)
    {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hepsilon_le_one : epsilon ≤ 1)
    (hnext_small :
      ∀ a q, section6_next_highest_bid_all I a q ≤ epsilon * I.budget a) :
    paperMsvvRatio *
        (I.withEffectiveBids (section6_next_highest_bid_all I)).offlineOptimumValue
          (fun a => (hbudget a).le) ≤
      paperRevenue (I.withEffectiveBids (section6_next_highest_bid_all I))
        ((I.withEffectiveBids (section6_next_highest_bid_all I)).runAssignment
          (I.withEffectiveBids
            (section6_next_highest_bid_all I)).balanceChoiceRule history) +
        epsilon * (Real.exp 1 + 1) *
          (∑ q : Query,
            (I.withEffectiveBids
              (section6_next_highest_bid_all I)).maxBidForQuery q) := by
  exact
    section6_next_highest_bid_all_theorem8_finite_explicit_error
      I hbudget history hnodup hcover hepsilon hepsilon_le_one hnext_small

/--
Audit endpoint for Section 6: next-highest-bid charges over alive bidders
inherit the finite explicit Theorem 8 guarantee when those charges are small.
-/
theorem audit_section6_next_highest_bid_alive_theorem8_finite_explicit_error
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : PaperInstance Advertiser Query)
    (alive : Advertiser → Query → Prop) [∀ a q, Decidable (alive a q)]
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    (hnodup : history.Nodup)
    (hcover : AdWordsInstance.historyFinset history = Finset.univ)
    {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hepsilon_le_one : epsilon ≤ 1)
    (hnext_small :
      ∀ a q, section6_next_highest_bid_alive I alive a q ≤
        epsilon * I.budget a) :
    paperMsvvRatio *
        (I.withEffectiveBids
          (section6_next_highest_bid_alive I alive)).offlineOptimumValue
          (fun a => (hbudget a).le) ≤
      paperRevenue
        (I.withEffectiveBids (section6_next_highest_bid_alive I alive))
        ((I.withEffectiveBids
          (section6_next_highest_bid_alive I alive)).runAssignment
          (I.withEffectiveBids
            (section6_next_highest_bid_alive I alive)).balanceChoiceRule history) +
        epsilon * (Real.exp 1 + 1) *
          (∑ q : Query,
            (I.withEffectiveBids
              (section6_next_highest_bid_alive I alive)).maxBidForQuery q) := by
  exact
    section6_next_highest_bid_alive_theorem8_finite_explicit_error
      I alive hbudget history hnodup hcover hepsilon hepsilon_le_one
      hnext_small

/--
Audit endpoint for Section 6: click-through-rate effective bids inherit the
finite explicit Theorem 8 guarantee.
-/
theorem audit_section6_click_through_rates_theorem8_finite_explicit_error
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : PaperInstance Advertiser Query)
    (ctr : Advertiser → Query → ℝ)
    (hctr_nonneg : ∀ a q, 0 ≤ ctr a q)
    (hctr_le_one : ∀ a q, ctr a q ≤ 1)
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
        (I.withClickThroughRates ctr).offlineOptimumValue
          (fun a => (hbudget a).le) ≤
      paperRevenue (I.withClickThroughRates ctr)
        ((I.withClickThroughRates ctr).runAssignment
          (I.withClickThroughRates ctr).balanceChoiceRule history) +
        epsilon * (Real.exp 1 + 1) *
          (∑ q : Query, (I.withClickThroughRates ctr).maxBidForQuery q) := by
  exact
    section6_click_through_rates_theorem8_finite_explicit_error
      I ctr hctr_nonneg hctr_le_one hbid hbudget history hnodup hcover
      hepsilon hepsilon_le_one hsmall

/--
Audit endpoint for Section 6: availability masks inherit the finite explicit
Theorem 8 guarantee.
-/
theorem audit_section6_availability_theorem8_finite_explicit_error
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : PaperInstance Advertiser Query)
    (available : Advertiser → Query → Prop)
    [∀ a q, Decidable (available a q)]
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
        (I.withAvailability available).offlineOptimumValue
          (fun a => (hbudget a).le) ≤
      paperRevenue (I.withAvailability available)
        ((I.withAvailability available).runAssignment
          (I.withAvailability available).balanceChoiceRule history) +
        epsilon * (Real.exp 1 + 1) *
          (∑ q : Query, (I.withAvailability available).maxBidForQuery q) := by
  exact
    section6_availability_theorem8_finite_explicit_error
      I available hbid hbudget history hnodup hcover hepsilon hepsilon_le_one
      hsmall

/--
Audit endpoint for Section 6: slot-expanded instances inherit the finite
explicit Theorem 8 guarantee.
-/
theorem audit_section6_multiple_slots_theorem8_finite_explicit_error
    {Advertiser Query : Type*} {Slot : Query → Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype (Σ q : Query, Slot q)]
    [DecidableEq Advertiser] [DecidableEq (Σ q : Query, Slot q)]
    (I : PaperInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List (Σ q : Query, Slot q))
    (hnodup : history.Nodup)
    (hcover : AdWordsInstance.historyFinset history = Finset.univ)
    {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hepsilon_le_one : epsilon ≤ 1)
    (hsmall : paperSmallBids I epsilon) :
    paperMsvvRatio *
        (I.withSlots Slot).offlineOptimumValue
          (fun a => (hbudget a).le) ≤
      paperRevenue (I.withSlots Slot)
        ((I.withSlots Slot).runAssignment
          (I.withSlots Slot).balanceChoiceRule history) +
        epsilon * (Real.exp 1 + 1) *
          (∑ q : Σ q : Query, Slot q, (I.withSlots Slot).maxBidForQuery q) := by
  exact
    section6_multiple_slots_theorem8_finite_explicit_error
      I hbid hbudget history hnodup hcover hepsilon hepsilon_le_one hsmall

/--
Audit endpoint for Section 6: source-shaped page-level top-`n_q` Balance with
distinct advertisers per page satisfies the finite explicit Theorem 8 guarantee.
-/
theorem audit_section6_page_top_balance_theorem8_finite_explicit_error
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
    section6_page_top_balance_theorem8_finite_explicit_error
      I slots hbid hbudget history hnodup hcover
      hepsilon hepsilon_le_one hsmall

/--
Audit endpoint for Section 6 multiple slots: the distinct-choice wrapper enforces
that the same advertiser is not assigned twice to slots of one original query.
-/
theorem audit_section6_multiple_slots_distinct_choice_run_assignment_per_page_distinct
    {Advertiser Query : Type*} {Slot : Query → Type*}
    [Fintype Advertiser] [Fintype (Σ q : Query, Slot q)]
    [DecidableEq Advertiser] [DecidableEq (Σ q : Query, Slot q)]
    (I : PaperInstance Advertiser Query)
    (history : List (Σ q : Query, Slot q)) :
    paperSlotsPerPageDistinct Slot
      ((I.withSlots Slot).runAssignment
        (AdWordsInstance.withSlotsDistinctChoice Slot
          (I.withSlots Slot).balanceChoiceRule)
        history) := by
  exact
    section6_multiple_slots_distinct_choice_run_assignment_per_page_distinct
      I history

/--
Audit endpoint for Section 8: advertiser-weighted bids inherit the finite
explicit Theorem 8 guarantee.
-/
theorem audit_section8_weighted_bids_theorem8_finite_explicit_error
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : PaperInstance Advertiser Query)
    (weight : Advertiser → ℝ)
    (hweight_nonneg : ∀ a, 0 ≤ weight a)
    (hweight_le_one : ∀ a, weight a ≤ 1)
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
        (I.withAdvertiserWeights weight).offlineOptimumValue
          (fun a => (hbudget a).le) ≤
      paperRevenue (I.withAdvertiserWeights weight)
        ((I.withAdvertiserWeights weight).runAssignment
          (I.withAdvertiserWeights weight).balanceChoiceRule history) +
        epsilon * (Real.exp 1 + 1) *
          (∑ q : Query, (I.withAdvertiserWeights weight).maxBidForQuery q) := by
  exact
    section8_weighted_bids_theorem8_finite_explicit_error
      I weight hweight_nonneg hweight_le_one hbid hbudget history hnodup
      hcover hepsilon hepsilon_le_one hsmall

/--
Audit endpoint for Section 8: weighted bids inherit the finite explicit
Theorem 8 guarantee when the weighted effective bids are themselves small.
-/
theorem audit_section8_weighted_bids_theorem8_finite_explicit_error_of_weighted_small_bids
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
      paperRevenue (I.withAdvertiserWeights weight)
        ((I.withAdvertiserWeights weight).runAssignment
          (I.withAdvertiserWeights weight).balanceChoiceRule history) +
        epsilon * (Real.exp 1 + 1) *
          (∑ q : Query, (I.withAdvertiserWeights weight).maxBidForQuery q) := by
  exact
    section8_weighted_bids_theorem8_finite_explicit_error_of_weighted_small_bids
      I weight hweight_nonneg hbid hbudget history hnodup hcover hepsilon
      hepsilon_le_one hweighted_small

/-! ## Theorem 9: randomized lower bound -/

/-- Audit endpoint for Theorem 9's harmonic hard-instance cap. -/
theorem audit_theorem9_harmonic_eventually_le_msvv_ratio_add_delta :
    ∀ delta : ℝ, 0 < delta →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        theorem9NormalizedRevenueUpperBound N ≤
          paperMsvvRatio + delta := by
  exact theorem9_harmonic_eventually_le_msvv_ratio_add_delta

/-- Audit endpoint for the canonical capped normalized spend expression. -/
theorem audit_theorem9_capped_normalized_revenue_eq_prefix_spend
    (N : ℕ) (algorithm : theorem9IntegralPrefixAlgorithm N)
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
Audit endpoint for Theorem 9 over arbitrary finite feasible observed-prefix
allocation rule families.
-/
theorem audit_theorem9_no_randomized_feasible_prefix_rule_family_beats_msvv_ratio
    {Algorithm : ℕ → Type*}
    [∀ N, Fintype (Algorithm N)] [∀ N, DecidableEq (Algorithm N)]
    (C : theorem9FeasiblePrefixRuleFamily Algorithm) :
    ∀ delta : ℝ, 0 < delta →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        ∀ randomizedAlgorithm : PMF (Algorithm N),
          ¬ ∀ permutation,
            paperMsvvRatio + delta <
              AppliedModelingLib.pmfExp randomizedAlgorithm
                (fun algorithm =>
                  C.normalizedRevenue N algorithm permutation) := by
  exact theorem9_no_randomized_feasible_prefix_rule_family_beats_msvv_ratio C

/--
Audit endpoint for Theorem 9: no randomized distribution over finite
integral-prefix algorithms beats `1 - 1/e` by a positive additive margin on
all sufficiently large hard instances.
-/
theorem audit_theorem9_no_randomized_integral_prefix_algorithm_beats_msvv_ratio :
    ∀ delta : ℝ, 0 < delta →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        ∀ randomizedAlgorithm : PMF (theorem9IntegralPrefixAlgorithm N),
          ¬ ∀ permutation,
            paperMsvvRatio + delta <
              AppliedModelingLib.pmfExp randomizedAlgorithm
                (fun algorithm =>
                  theorem9CappedNormalizedRevenue N algorithm permutation) := by
  exact theorem9_no_randomized_integral_prefix_algorithm_beats_msvv_ratio

/--
Audit endpoint for Theorem 9 using the paper-facing randomized online
algorithm alias for the finite prefix model.
-/
theorem audit_theorem9_no_randomized_online_algorithm_beats_msvv_ratio :
    ∀ delta : ℝ, 0 < delta →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        ∀ randomizedAlgorithm : theorem9RandomizedOnlineAlgorithm N,
          ¬ ∀ permutation,
            paperMsvvRatio + delta <
              AppliedModelingLib.pmfExp randomizedAlgorithm
                (fun algorithm =>
                  theorem9CappedNormalizedRevenue N algorithm permutation) := by
  exact theorem9_no_randomized_online_algorithm_beats_msvv_ratio

end AuditLedger
end MSVV07PaperFacing
end Online
end AppliedModelingLib

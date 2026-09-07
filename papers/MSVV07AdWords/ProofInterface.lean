import MSVV07AdWords.SourceLemmas

/-!
# Paper Interface: MSVV07 AdWords

This file is the single Lean file intended for human audit of the formalized
surface of Mehta, Saberi, Vazirani, and Vazirani, *AdWords and Generalized
Online Matching* (JACM 2007).

The declarations below deliberately expose the paper-facing formulas for the
finite AdWords model, Balance/MSVV rule, small-bids limit, and Section 7
b-matching lower bound. The proofs are thin wrappers around the detailed
formalization in `MainTheorems.lean`, `AdWords.lean`, `AdWordsExtensions.lean`,
and `AdWordsLowerBound.lean`.
-/

open scoped BigOperators

namespace AppliedModelingLib
namespace Online
namespace MSVV07PaperFacing.Proof

/-! ## Sections 2--3: finite AdWords model and Balance/MSVV rule -/

/--
Paper model. An AdWords instance consists of advertiser budgets `budget a` and
query bids `bid a q`, where assigning query `q` to advertiser `a` earns
`bid a q` and charges the same amount to `a`.
-/
abbrev PaperInstance (Advertiser Query : Type*) :=
  AdWordsInstance Advertiser Query

/-- Paper assignment: every query is assigned to one advertiser or left unmatched. -/
abbrev PaperAssignment (Advertiser Query : Type*) :=
  Query → Option Advertiser

/--
Paper multiple-slot distinctness: no advertiser is assigned to two slots of the
same original query.
-/
abbrev paperSlotsPerPageDistinct
    {Advertiser Query : Type*} (Slot : Query → Type*)
    (A : PaperAssignment Advertiser (Σ q : Query, Slot q)) : Prop :=
  AdWordsInstance.withSlotsPerPageDistinct Slot A

/-- Paper spend formula for advertiser `a` under assignment `A`. -/
noncomputable abbrev paperSpend
    {Advertiser Query : Type*} [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) (a : Advertiser) : ℝ :=
  ∑ q : Query,
    match A q with
    | none => 0
    | some a' => if a' = a then I.bid a q else 0

/-- Paper revenue formula for an assignment. -/
noncomputable abbrev paperRevenue
    {Advertiser Query : Type*} [Fintype Query]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) : ℝ :=
  ∑ q : Query,
    match A q with
    | none => 0
    | some a => I.bid a q

/-- Paper budget feasibility: no advertiser spends more than her budget. -/
abbrev paperFeasible
    {Advertiser Query : Type*} [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) : Prop :=
  ∀ a, paperSpend I A a ≤ I.budget a

/-- Paper small-bids condition: every bid is at most an `epsilon` budget fraction. -/
abbrev paperSmallBids
    {Advertiser Query : Type*}
    (I : PaperInstance Advertiser Query) (epsilon : ℝ) : Prop :=
  ∀ a q, I.bid a q ≤ epsilon * I.budget a

/--
Paper fractional LP value: the relaxed assignment variable `x a q` contributes
`bid a q * x a q`.
-/
noncomputable abbrev paperFractionalRevenue
    {Advertiser Query : Type*} [Fintype Advertiser] [Fintype Query]
    (I : PaperInstance Advertiser Query)
    (x : Advertiser → Query → ℝ) : ℝ :=
  ∑ q : Query, ∑ a : Advertiser, I.bid a q * x a q

/--
Paper fractional LP feasibility: nonnegative assignment, at most one unit per
query, and budget feasibility for every advertiser.
-/
structure PaperFractionalFeasible
    {Advertiser Query : Type*} [Fintype Advertiser] [Fintype Query]
    (I : PaperInstance Advertiser Query)
    (x : Advertiser → Query → ℝ) : Prop where
  nonneg : ∀ a q, 0 ≤ x a q
  query : ∀ q, (∑ a : Advertiser, x a q) ≤ 1
  budget : ∀ a, (∑ q : Query, I.bid a q * x a q) ≤ I.budget a

/-- The paper's MSVV/Balance tradeoff function at spent fraction `s`. -/
noncomputable abbrev paperTradeoff (s : ℝ) : ℝ :=
  1 - Real.exp (s - 1)

/-- The paper's competitive ratio `1 - 1/e`. -/
noncomputable abbrev paperMsvvRatio : ℝ :=
  1 - 1 / Real.exp 1

/-- Paper Balance/MSVV scaled bid. -/
noncomputable abbrev paperBalanceScore
    {Advertiser Query : Type*} [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) (a : Advertiser) (q : Query) : ℝ :=
  I.bid a q * paperTradeoff (paperSpend I A a / I.budget a)

/-- Paper feasibility for assigning query `q` next to advertiser `a`. -/
abbrev paperCanAssign
    {Advertiser Query : Type*} [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) (q : Query) (a : Advertiser) : Prop :=
  paperSpend I A a + I.bid a q ≤ I.budget a

/--
Paper Balance/MSVV choice rule: assign the query to a feasible advertiser with
maximum scaled bid.
-/
abbrev paperIsBalanceChoice
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) (q : Query) (a : Advertiser) : Prop :=
  paperCanAssign I A q a ∧
    ∀ b, paperCanAssign I A q b →
      paperBalanceScore I A b q ≤ paperBalanceScore I A a q

/-- Paper spend agrees definitionally with the reusable library spend formula. -/
theorem paperSpend_eq_library
    {Advertiser Query : Type*} [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) (a : Advertiser) :
    paperSpend I A a = I.spend A a := by
  rfl

/-- Paper revenue agrees definitionally with the reusable library revenue formula. -/
theorem paperRevenue_eq_library
    {Advertiser Query : Type*} [Fintype Query]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) :
    paperRevenue I A = I.revenue A := by
  rfl

/-- Paper budget feasibility agrees definitionally with library feasibility. -/
theorem paperFeasible_eq_library
    {Advertiser Query : Type*} [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) :
    paperFeasible I A = I.Feasible A := by
  rfl

/-- Paper small-bids condition agrees definitionally with the library condition. -/
theorem paperSmallBids_eq_library
    {Advertiser Query : Type*}
    (I : PaperInstance Advertiser Query) (epsilon : ℝ) :
    paperSmallBids I epsilon = I.SmallBids epsilon := by
  rfl

/-- Paper fractional LP objective agrees definitionally with the library objective. -/
theorem paperFractionalRevenue_eq_library
    {Advertiser Query : Type*} [Fintype Advertiser] [Fintype Query]
    (I : PaperInstance Advertiser Query)
    (x : Advertiser → Query → ℝ) :
    paperFractionalRevenue I x = I.fractionalRevenue x := by
  rfl

/-- The paper tradeoff function is the library Balance/MSVV discount. -/
theorem paperTradeoff_eq_library (s : ℝ) :
    paperTradeoff s = AdWordsInstance.balanceDiscount s := by
  rfl

/-- The paper competitive ratio is the library MSVV ratio. -/
theorem paperMsvvRatio_eq_library :
    paperMsvvRatio = AdWordsInstance.msvvRatio := by
  rfl

/-- Paper scaled bid agrees definitionally with the library Balance score. -/
theorem paperBalanceScore_eq_library
    {Advertiser Query : Type*} [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) (a : Advertiser) (q : Query) :
    paperBalanceScore I A a q = I.balanceScore A a q := by
  rfl

/-- Paper assignability agrees definitionally with library assignability. -/
theorem paperCanAssign_eq_library
    {Advertiser Query : Type*} [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) (q : Query) (a : Advertiser) :
    paperCanAssign I A q a = I.CanAssign A q a := by
  rfl

/-- Paper Balance-choice maximization agrees definitionally with the library rule predicate. -/
theorem paperIsBalanceChoice_eq_library
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) (q : Query) (a : Advertiser) :
    paperIsBalanceChoice I A q a = I.IsBalanceChoice A q a := by
  rfl

/-- The paper tradeoff factor is antitone in the spent fraction. -/
theorem paperTradeoff_antitone : Antitone paperTradeoff := by
  intro x y hxy
  unfold paperTradeoff
  have hexp : Real.exp (x - 1) ≤ Real.exp (y - 1) :=
    Real.exp_le_exp.mpr (by linarith)
  linarith

/-- The paper tradeoff factor is strictly antitone in the spent fraction. -/
theorem paperTradeoff_strictAnti : StrictAnti paperTradeoff := by
  intro x y hxy
  unfold paperTradeoff
  have hexp : Real.exp (x - 1) < Real.exp (y - 1) :=
    Real.exp_lt_exp.mpr (by linarith)
  linarith

/-! ## Core LP and online-run support used by the paper proof -/

/-- Empty assignments are feasible under nonnegative budgets. -/
theorem section2_empty_assignment_feasible
    {Advertiser Query : Type*}
    [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (hbudget : ∀ a, 0 ≤ I.budget a) :
    paperFeasible I
      (AdWordsInstance.emptyAssignment :
        PaperAssignment Advertiser Query) := by
  simpa [paperFeasible_eq_library] using
    paper_adwords_empty_assignment_feasible I hbudget

/-- Finite instances have an offline optimum assignment. -/
theorem section2_offline_optimum_exists
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (hbudget : ∀ a, 0 ≤ I.budget a) :
    ∃ A : PaperAssignment Advertiser Query,
      I.IsOptimalAssignment A := by
  exact paper_adwords_offline_optimum_exists I hbudget

/-- Paper LP weak duality for the fractional AdWords relaxation. -/
theorem section2_fractional_lp_weak_duality
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Fintype Query]
    (I : PaperInstance Advertiser Query)
    (x : Advertiser → Query → ℝ)
    (alpha : Advertiser → ℝ) (beta : Query → ℝ)
    (hfeasible : I.FractionalFeasible x)
    (hdual : I.DualFeasible alpha beta) :
    paperFractionalRevenue I x ≤ I.dualObjective alpha beta := by
  simpa [paperFractionalRevenue_eq_library] using
    paper_adwords_fractional_lp_weak_duality I x alpha beta hfeasible hdual

/-- A Balance/MSVV maximizer exists whenever some advertiser can accept the query. -/
theorem section3_balance_choice_exists
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) (q : Query)
    (h : ∃ a, paperCanAssign I A q a) :
    ∃ a, paperIsBalanceChoice I A q a := by
  simpa [paperCanAssign_eq_library, paperIsBalanceChoice_eq_library] using
    paper_adwords_balance_choice_exists I A q h

/--
Concrete Balance/MSVV choice-rule bridge: when the canonical rule returns a
chosen advertiser, its paper scaled bid is at least that of every advertiser
that can still accept the query.
-/
theorem section3_balance_choice_score_ge_of_can_assign
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) (q : Query)
    {chosen opt : Advertiser}
    (hchoice : I.balanceChoiceRule A q = some chosen)
    (hopt_can : paperCanAssign I A q opt) :
    paperBalanceScore I A opt q ≤ paperBalanceScore I A chosen q := by
  have hbal :=
    AdWordsInstance.balanceChoiceRule_isBalanceChoice_of_eq_some
      I A q chosen hchoice
  exact by
    simpa [paperBalanceScore_eq_library, paperCanAssign_eq_library] using
      hbal.2 opt (by simpa [paperCanAssign_eq_library] using hopt_can)

/-- The canonical Balance/MSVV online run is budget-feasible. -/
theorem section3_balance_run_assignment_feasible
    {Advertiser Query : Type*}
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    [DecidableEq Query]
    (I : PaperInstance Advertiser Query)
    (hbudget : ∀ a, 0 ≤ I.budget a)
    (history : List Query) :
    paperFeasible I (I.runAssignment I.balanceChoiceRule history) := by
  simpa [paperFeasible_eq_library] using
    paper_adwords_balance_run_assignment_feasible I hbudget history

/-! ## Sections 4--5: source proof-route lemmas -/

/--
Section 4 Lemma 1. In the equal-bids BALANCE proof, if OPT's bidder is still
active in a no-later slab and BALANCE maximizes a strictly decreasing equal-bid
slab score, BALANCE cannot pay from a later slab.
-/
theorem proof_section4_lemma1_balance_pays_no_later_slab
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
    MSVV07SourceLemmas.lemma1_balance_pays_no_later_slab
      psi hoptCurrent_le_type hchoice hequal_bids hbid_pos hpsi_strictAnti

/--
Concrete spent-fraction form of Section 4 Lemma 1. In the equal-bids case, the
canonical Balance/MSVV choice rule cannot choose an advertiser whose current
spent fraction lies after OPT's source type.
-/
theorem section4_lemma1_balance_pays_no_later_spent_fraction_of_balance_choice
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
  have hscore :=
    section3_balance_choice_score_ge_of_can_assign
      I A q hchoice hopt_can
  have hchoice_score :
      I.bid opt q * paperTradeoff (paperSpend I A opt / I.budget opt) ≤
        I.bid chosen q * paperTradeoff
          (paperSpend I A chosen / I.budget chosen) := by
    simpa [paperBalanceScore] using hscore
  exact
    proof_section4_lemma1_balance_pays_no_later_slab
      paperTradeoff hoptCurrent_le_type hchoice_score hequal_bids hbid_pos
      paperTradeoff_strictAnti

/--
Section 4 Lemma 2. The source factor-revealing LP constraint follows from the
prefix counting inequality supplied by Lemma 1 and the slab-spend identity.
-/
theorem proof_section4_lemma2_factor_revealing_lp_constraint
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
    MSVV07SourceLemmas.lemma2_factor_revealing_lp_constraint
      N x beta i hprefix_cover hbeta_prefix

/--
Section 4 Lemma 3, limiting value. The finite LP value exposed by the source
candidate formula `N * (1 - 1/k)^k` tends to `N/e`.
-/
theorem section4_lemma3_factor_revealing_lp_value_tends (N : ℝ) :
    Sequence.SeqTendsTo
      (fun k : ℕ => N * (1 - 1 / (k : ℝ)) ^ k)
      (N / Real.exp 1) := by
  exact MSVV07SourceLemmas.lemma3_factor_revealing_lp_value_tends N

/--
Section 4 Lemma 3, finite LP weak duality in the paper's factor-revealing
notation.
-/
theorem section4_lemma3_factor_revealing_lp_weak_duality
    {m : ℕ} (N : ℝ) {x y : Fin m → ℝ}
    (hx : MSVV07SourceLemmas.paperRoutePrimalFeasible N x)
    (hy : MSVV07SourceLemmas.paperRouteDualFeasible y) :
    MSVV07SourceLemmas.paperRoutePrimalObjective x ≤
      MSVV07SourceLemmas.paperRouteDualObjective N y := by
  exact MSVV07SourceLemmas.paperRoute_factor_revealing_weak_duality N hx hy

/-- Section 4 Lemma 3: the displayed primal witness `x*` is nonnegative. -/
theorem section4_lemma3_primal_candidate_nonnegative
    {m : ℕ} {N : ℝ} (hN : 0 ≤ N) (i : Fin m) :
    0 ≤ MSVV07SourceLemmas.paperRoutePrimalCandidate (m := m) N i := by
  exact MSVV07SourceLemmas.paperRoutePrimalCandidate_nonnegative hN i

/-- Section 4 Lemma 3: the displayed dual witness `y*` is nonnegative. -/
theorem section4_lemma3_dual_candidate_nonnegative
    {m : ℕ} (i : Fin m) :
    0 ≤ MSVV07SourceLemmas.paperRouteDualCandidate (m := m) i := by
  exact MSVV07SourceLemmas.paperRouteDualCandidate_nonnegative i

/-- Section 4 Lemma 3: the displayed primal witness makes every LP row tight. -/
theorem section4_lemma3_primal_candidate_row_tight
    {m : ℕ} (N : ℝ) (i : Fin m) :
    MSVV07SourceLemmas.paperRouteLPRow
      (MSVV07SourceLemmas.paperRoutePrimalCandidate (m := m) N) i =
      MSVV07SourceLemmas.paperRouteRhs N i := by
  exact MSVV07SourceLemmas.paperRoutePrimalCandidate_row_tight N i

/-- Section 4 Lemma 3: the displayed primal witness is feasible when `N ≥ 0`. -/
theorem section4_lemma3_primal_candidate_feasible
    {m : ℕ} {N : ℝ} (hN : 0 ≤ N) :
    MSVV07SourceLemmas.paperRoutePrimalFeasible (m := m) N
      (MSVV07SourceLemmas.paperRoutePrimalCandidate (m := m) N) := by
  exact MSVV07SourceLemmas.paperRoutePrimalCandidate_feasible hN

/-- Section 4 Lemma 3: the displayed dual witness makes every dual row tight. -/
theorem section4_lemma3_dual_candidate_row_tight
    {m : ℕ} (i : Fin m) :
    MSVV07SourceLemmas.paperRouteDualRow
      (MSVV07SourceLemmas.paperRouteDualCandidate (m := m)) i =
      MSVV07SourceLemmas.paperRoutePrimalObjectiveCoeff (m := m) i := by
  exact MSVV07SourceLemmas.paperRouteDualCandidate_row_tight i

/-- Section 4 Lemma 3: the displayed dual witness is feasible. -/
theorem section4_lemma3_dual_candidate_feasible
    {m : ℕ} :
    MSVV07SourceLemmas.paperRouteDualFeasible (m := m)
      (MSVV07SourceLemmas.paperRouteDualCandidate (m := m)) := by
  exact MSVV07SourceLemmas.paperRouteDualCandidate_feasible

/-- Section 4 Lemma 3: objective value of the displayed primal witness. -/
theorem section4_lemma3_primal_candidate_objective_value
    {m : ℕ} (N : ℝ) :
    MSVV07SourceLemmas.paperRoutePrimalObjective (m := m)
      (MSVV07SourceLemmas.paperRoutePrimalCandidate (m := m) N) =
      MSVV07SourceLemmas.factorRevealingLPValue m N := by
  exact MSVV07SourceLemmas.paperRoutePrimalCandidate_objective_value N

/-- Section 4 Lemma 3: objective value of the displayed dual witness. -/
theorem section4_lemma3_dual_candidate_objective_value
    {m : ℕ} (N : ℝ) :
    MSVV07SourceLemmas.paperRouteDualObjective (m := m) N
      (MSVV07SourceLemmas.paperRouteDualCandidate (m := m)) =
      MSVV07SourceLemmas.factorRevealingLPValue m N := by
  exact MSVV07SourceLemmas.paperRouteDualCandidate_objective_value N

/--
Section 4 Lemma 3, finite factor-revealing LP optimality from the paper's
explicit primal/dual certificate.
-/
noncomputable def section4_lemma3_factor_revealing_lp_optimal_from_certificate
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
  MSVV07SourceLemmas.lemma3_factor_revealing_lp_optimal_from_certificate
    N hprimal hdual hprimal_value hdual_value

/--
Section 4 Lemma 3, finite factor-revealing LP optimality from row/value
certificates for the displayed `x*` and `y*`; nonnegativity is proved by Lean.
-/
noncomputable def section4_lemma3_factor_revealing_lp_optimal_from_row_certificates
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
  MSVV07SourceLemmas.lemma3_factor_revealing_lp_optimal_from_row_certificates
    hN hprimal_rows hdual_rows hprimal_value hdual_value

/--
Section 4 Lemma 3, finite factor-revealing LP optimality for the displayed
geometric `x*` and `y*` witnesses.
-/
noncomputable def section4_lemma3_factor_revealing_lp_optimal
    {m : ℕ} {N : ℝ} (hN : 0 ≤ N) :
    Optimization.UpperBoundCertificate
      (α := Fin m → ℝ)
      (MSVV07SourceLemmas.paperRoutePrimalFeasible (m := m) N)
      (MSVV07SourceLemmas.paperRoutePrimalObjective (m := m))
      (MSVV07SourceLemmas.factorRevealingLPValue m N) :=
  MSVV07SourceLemmas.lemma3_factor_revealing_lp_optimal hN

/--
Section 4 Lemma 3, direct paper-facing optimizer statement for the displayed
geometric primal witness.
-/
theorem section4_lemma3_factor_revealing_lp_primal_candidate_is_maximizer
    {m : ℕ} {N : ℝ} (hN : 0 ≤ N) :
    Optimization.IsMaximizerOn
      (MSVV07SourceLemmas.paperRoutePrimalFeasible (m := m) N)
      (MSVV07SourceLemmas.paperRoutePrimalObjective (m := m))
      (MSVV07SourceLemmas.paperRoutePrimalCandidate (m := m) N) := by
  exact
    MSVV07SourceLemmas.lemma3_factor_revealing_lp_primal_candidate_is_maximizer
      hN

/--
Section 4 Lemma 3, direct paper-facing universal upper bound for every
feasible solution of the finite factor-revealing LP.
-/
theorem section4_lemma3_factor_revealing_lp_upper_bound
    {m : ℕ} {N : ℝ} (hN : 0 ≤ N)
    (x : Fin m → ℝ)
    (hx :
      MSVV07SourceLemmas.paperRoutePrimalFeasible (m := m) N x) :
    MSVV07SourceLemmas.paperRoutePrimalObjective (m := m) x ≤
      MSVV07SourceLemmas.factorRevealingLPValue m N := by
  exact
    MSVV07SourceLemmas.lemma3_factor_revealing_lp_upper_bound
      hN x hx

/--
Section 5 Lemma 4. If weak duality holds and a feasible primal point matches
the value of the inherited feasible dual point, that inherited dual point is
optimal for the tradeoff-revealing LP.
-/
theorem proof_section5_lemma4_dual_optimal_from_primal_dual_match
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
    MSVV07SourceLemmas.lemma4_dual_optimal_from_primal_dual_match
      primalFeasible dualFeasible primalObjective dualObjective hweak
      ha hystar hvalue

/--
Section 5 Lemma 4, finite-LP form: equal feasible primal/dual objective values
certify optimality of the inherited dual solution.
-/
theorem section5_lemma4_standardMaxLP_dual_yStar_optimal
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : Optimization.StandardMaxLP ι κ)
    {a : ι → ℝ} {ystar : κ → ℝ}
    (ha : P.PrimalFeasible a)
    (hystar : P.DualFeasible ystar)
    (hvalue : P.primalObjective a = P.dualObjective ystar) :
    Optimization.IsMinimizerOn P.DualFeasible P.dualObjective ystar := by
  exact
    MSVV07SourceLemmas.lemma4_standardMaxLP_dual_yStar_optimal
      P ha hystar hvalue

/--
Section 5 Lemma 4, source "same constraints" step: dual feasibility is
unchanged when only the dual objective/RHS vector changes.
-/
theorem section5_lemma4_dual_feasible_of_same_A_c
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : κ → ι → ℝ) (b l : κ → ℝ) (c : ι → ℝ)
    {ystar : κ → ℝ}
    (hystar :
      (Optimization.StandardMaxLP.mk A b c).DualFeasible ystar) :
    (Optimization.StandardMaxLP.mk A l c).DualFeasible ystar := by
  exact MSVV07SourceLemmas.lemma4_dual_feasible_of_same_A_c A b l c hystar

/--
Section 5 Lemma 4 in the paper's tradeoff-revealing form.  `L(π, ψ)` keeps the
base constraint matrix and objective coefficients, replaces its right-hand
side by `A a`, and therefore inherits feasibility of `y*`; equality of the
two witnessed objectives certifies that inherited dual point as optimal.
-/
theorem proof_section5_lemma4_tradeoff_revealing_dual_optimal
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : κ → ι → ℝ) (b : κ → ℝ) (c : ι → ℝ)
    (a : ι → ℝ) (ystar : κ → ℝ)
    (ha_nonnegative : ∀ i, 0 ≤ a i)
    (hystar_base :
      (Optimization.StandardMaxLP.mk A b c).DualFeasible ystar)
    (hvalue :
      (Optimization.StandardMaxLP.mk A
        (fun row => ∑ i : ι, A row i * a i) c).primalObjective a =
      (Optimization.StandardMaxLP.mk A
        (fun row => ∑ i : ι, A row i * a i) c).dualObjective ystar) :
    Optimization.IsMinimizerOn
      (Optimization.StandardMaxLP.mk A
        (fun row => ∑ i : ι, A row i * a i) c).DualFeasible
      (Optimization.StandardMaxLP.mk A
        (fun row => ∑ i : ι, A row i * a i) c).dualObjective
      ystar := by
  let l : κ → ℝ := fun row => ∑ i : ι, A row i * a i
  let P : Optimization.StandardMaxLP ι κ :=
    Optimization.StandardMaxLP.mk A l c
  have ha : P.PrimalFeasible a := by
    constructor
    · exact ha_nonnegative
    · intro row
      change (∑ i : ι, A row i * a i) ≤ ∑ i : ι, A row i * a i
      exact le_rfl
  have hystar : P.DualFeasible ystar := by
    simpa [P, l] using section5_lemma4_dual_feasible_of_same_A_c
      A b l c hystar_base
  exact section5_lemma4_standardMaxLP_dual_yStar_optimal P ha hystar
    (by simpa [P, l] using hvalue)

/--
Section 5 Lemma 4 for the paper's factor-revealing matrix: the realized type
vector gives the constructed right side, and the fixed geometric dual is
optimal without a separately supplied feasibility or objective-equality fact.
-/
theorem proof_section5_lemma4_paper_tradeoff_dual_candidate_optimal
    {m : ℕ} (a : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i) :
    Optimization.IsMinimizerOn
      (MSVV07SourceLemmas.tradeoffRevealingLP (m := m)
        MSVV07SourceLemmas.paperRoutePrimalObjectiveCoeff
        (fun row => ∑ i : Fin m, MSVV07SourceLemmas.paperRouteMatrixCoeff row i * a i)).DualFeasible
      (MSVV07SourceLemmas.tradeoffRevealingLP (m := m)
        MSVV07SourceLemmas.paperRoutePrimalObjectiveCoeff
        (fun row => ∑ i : Fin m, MSVV07SourceLemmas.paperRouteMatrixCoeff row i * a i)).dualObjective
      MSVV07SourceLemmas.paperRouteDualCandidate := by
  exact MSVV07SourceLemmas.lemma4_paper_tradeoff_dual_candidate_optimal a ha

/--
Section 5 Lemma 5. The right-hand side of `L(π, ψ)` is the original LP
right-hand side plus the perturbation vector `Δ(π, ψ)`.
-/
theorem proof_section5_lemma5_tradeoff_rhs_eq_base_add_delta
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
    MSVV07SourceLemmas.lemma5_tradeoff_rhs_eq_base_add_delta
      N alpha beta i hbeta_prefix

/--
Section 5 Lemma 6. For each query with OPT type at most `k - 1`, the
Balance/MSVV choice rule and monotonicity of `ψ` imply the paper's per-query
tradeoff inequality.
-/
theorem proof_section5_lemma6_per_query_tradeoff
    {Slab : Type*} [Preorder Slab]
    (psi : Slab → ℝ) {queryType optCurrentSlab algSlab : Slab}
    {optBid algBid : ℝ}
    (hoptCurrent_le_type : optCurrentSlab ≤ queryType)
    (hpsi_antitone : Antitone psi)
    (hoptBid_nonneg : 0 ≤ optBid)
    (hchoice : optBid * psi optCurrentSlab ≤ algBid * psi algSlab) :
    optBid * psi queryType ≤ algBid * psi algSlab := by
  exact
    MSVV07SourceLemmas.lemma6_per_query_tradeoff
      psi hoptCurrent_le_type hpsi_antitone hoptBid_nonneg hchoice

/--
Section 5 Lemma 6 bridge for the concrete Balance/MSVV choice rule. The
score-maximization premise is discharged by the actual canonical choice rule;
only the source slab/score identifications remain explicit.
-/
theorem proof_section5_lemma6_per_query_tradeoff_of_balance_choice
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
  have hscore :=
    section3_balance_choice_score_ge_of_can_assign
      I A q hchoice hopt_can
  have hchoice_score :
      I.bid opt q * psi optCurrentSlab ≤ I.bid chosen q * psi algSlab := by
    calc
      I.bid opt q * psi optCurrentSlab =
          paperBalanceScore I A opt q := hopt_score.symm
      _ ≤ paperBalanceScore I A chosen q := hscore
      _ = I.bid chosen q * psi algSlab := hchosen_score
  exact
    proof_section5_lemma6_per_query_tradeoff
      psi hoptCurrent_le_type hpsi_antitone hoptBid_nonneg hchoice_score

/--
Section 5 Lemma 6 in concrete spent-fraction form. The score identities and
tradeoff monotonicity are discharged from the paper definitions, leaving only
the source type comparison and the actual Balance/MSVV choice.
-/
theorem proof_section5_lemma6_per_query_tradeoff_of_balance_choice_spent_fraction
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
    proof_section5_lemma6_per_query_tradeoff_of_balance_choice
      I A q paperTradeoff hchoice hopt_can hoptCurrent_le_type
      paperTradeoff_antitone (hbid opt q) rfl rfl

/--
Section 5 Lemma 7. Summing Lemma 6 over queries and using the paper's type and
slab accounting identities bounds the weighted perturbation by the last-slab
error term.
-/
theorem proof_section5_lemma7_weighted_perturbation_bound
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
    MSVV07SourceLemmas.lemma7_weighted_perturbation_bound
      psi alpha beta opt alg queryType querySlab finalSlabError
      htradeoff_sum hopt_accounting halg_accounting

/--
Section 5 Lemma 7, paper-shaped `N/k` corollary once the last-slab accounting
error has the paper's `N/k` bound.
-/
theorem proof_section5_lemma7_weighted_perturbation_bound_by_N_div_k
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
    MSVV07SourceLemmas.lemma7_weighted_perturbation_bound_by_N_div_k
      psi alpha beta opt alg queryType querySlab finalSlabError N k
      htradeoff_sum hopt_accounting halg_accounting hfinal

/--
Section 5 Lemma 7, exact paper-shaped `N/k` corollary with no separate error
variable.
-/
theorem proof_section5_lemma7_weighted_perturbation_bound_exact_N_div_k
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
    MSVV07SourceLemmas.lemma7_weighted_perturbation_bound_exact_N_div_k
      psi alpha beta opt alg queryType querySlab N k htradeoff_sum
      hopt_accounting halg_accounting_N_div_k

/--
Section 5 Lemma 7 helper. Pointwise query tradeoff inequalities sum to the
global tradeoff inequality used by the weighted perturbation argument.
-/
theorem section5_lemma7_tradeoff_sum_of_pointwise
    {Query : Type*} [Fintype Query] (w : Query → ℝ)
    (h : ∀ q, w q ≤ 0) :
    (∑ q : Query, w q) ≤ 0 := by
  exact MSVV07SourceLemmas.lemma7_tradeoff_sum_of_pointwise w h

/--
Section 5 Lemma 7 helper. If `alpha i` is the OPT revenue over the fiber of
queries of type `i`, then the weighted OPT query sum equals `Σ_i ψ_i α_i`.
-/
theorem section5_lemma7_opt_accounting_of_type_fibers
    {m Query : Type*} [Fintype m] [Fintype Query] [DecidableEq m]
    (psi alpha : m → ℝ) (opt : Query → ℝ) (queryType : Query → m)
    (hα :
      ∀ i : m,
        (∑ q ∈ (Finset.univ : Finset Query).filter
          (fun q => queryType q = i), opt q) = alpha i) :
    (∑ q : Query, opt q * psi (queryType q)) =
      ∑ i : m, psi i * alpha i := by
  exact
    MSVV07SourceLemmas.lemma7_opt_accounting_of_type_fibers
      psi alpha opt queryType hα

/--
Section 5 Lemma 7 helper. Slab-fiber bounds on ALG revenue imply the weighted
ALG accounting inequality, up to an explicit nonnegative final-slab error.
-/
theorem section5_lemma7_alg_accounting_of_slab_fibers_and_final_error
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
    MSVV07SourceLemmas.lemma7_alg_accounting_of_slab_fibers_and_final_error
      psi beta alg querySlab finalSlabError hpsi_nonneg hβ hfinal_nonneg

/--
Section 5 Lemma 7 composed from pointwise tradeoff and fiber accounting facts.
This removes the already-summed accounting hypotheses from the paper-facing
`N/k` perturbation bound.
-/
theorem proof_section5_lemma7_weighted_perturbation_bound_exact_N_div_k_from_pointwise_fibers
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
  have htradeoff_sum :
      (∑ q : Query,
        (opt q * psi (queryType q) - alg q * psi (querySlab q))) ≤ 0 :=
    section5_lemma7_tradeoff_sum_of_pointwise
      (fun q : Query => opt q * psi (queryType q) -
        alg q * psi (querySlab q))
      hpointwise
  have hopt_accounting :
      (∑ q : Query, opt q * psi (queryType q)) =
        ∑ i : m, psi i * alpha i :=
    section5_lemma7_opt_accounting_of_type_fibers
      psi alpha opt queryType hα
  have halg_accounting :
      (∑ q : Query, alg q * psi (querySlab q)) ≤
        (∑ i : m, psi i * beta i) + N / (k : ℝ) :=
    section5_lemma7_alg_accounting_of_slab_fibers_and_final_error
      psi beta alg querySlab (N / (k : ℝ))
      hpsi_nonneg hβ hfinal_nonneg
  exact
    proof_section5_lemma7_weighted_perturbation_bound_exact_N_div_k
      psi alpha beta opt alg queryType querySlab N k
      htradeoff_sum hopt_accounting halg_accounting

/--
Concrete aggregate MSVV accounting theorem from the existing Balance-run
small-bids certificate: the assignment-induced normalized dual objective is
paid for by the run revenue plus the explicit finite small-bids error.
-/
theorem section5_balance_msvv_scaled_dual_objective_le_revenue_add_explicit_error
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
  have hcert :=
    paper_adwords_balance_msvv_approx_objective_bound_with_explicit_error
      I hbid hbudget history hnodup hcover hepsilon
      (by simpa [paperSmallBids_eq_library] using hsmall)
  simpa [paperMsvvRatio_eq_library, paperRevenue_eq_library] using
    hcert.scaled_dual_bound

/--
Theorem 8 source algebra: the dual-weighted perturbation vector equals the
weighted `α - β` sum for `ψ_i = Σ_{j≥i} y_j`.
-/
theorem theorem8_delta_dot_y_eq_weighted_perturbation
    {m : ℕ} (alpha beta y : Fin m → ℝ) :
    (∑ i : Fin m,
      y i * MSVV07SourceLemmas.paperRouteDelta alpha beta i) =
      ∑ i : Fin m,
        MSVV07SourceLemmas.paperRoutePsiFromDual y i *
          (alpha i - beta i) := by
  exact
    MSVV07SourceLemmas.theorem8_delta_dot_y_eq_weighted_perturbation
      alpha beta y

/--
Theorem 8 source tradeoff monotonicity: suffix-sum tradeoff weights induced by
a nonnegative dual vector are antitone.
-/
theorem theorem8_dual_induced_tradeoff_antitone
    {m : ℕ} (y : Fin m → ℝ) (hy : ∀ i, 0 ≤ y i) :
    Antitone (MSVV07SourceLemmas.paperRoutePsiFromDual y) := by
  exact MSVV07SourceLemmas.paperRoutePsiFromDual_antitone_of_nonnegative y hy

/-- Theorem 8 source tradeoff monotonicity for the paper's displayed `y*`. -/
theorem theorem8_dual_candidate_induced_tradeoff_antitone
    {m : ℕ} :
    Antitone
      (MSVV07SourceLemmas.paperRoutePsiFromDual (m := m)
        MSVV07SourceLemmas.paperRouteDualCandidate) := by
  exact MSVV07SourceLemmas.paperRoutePsiFromDualCandidate_antitone

/-- The tradeoff weights induced by the displayed Theorem 8 dual candidate are nonnegative. -/
theorem theorem8_dual_candidate_psi_nonnegative
    {m : ℕ} :
    ∀ i : Fin m,
      0 ≤ MSVV07SourceLemmas.paperRoutePsiCandidate (m := m) i := by
  intro i
  classical
  unfold MSVV07SourceLemmas.paperRoutePsiCandidate
    MSVV07SourceLemmas.paperRoutePsiFromDual
  exact Finset.sum_nonneg fun j _ =>
    MSVV07SourceLemmas.paperRouteDualCandidate_nonnegative j

/-- Theorem 8 source route: closed form for the `ψ` weights induced by `y*`. -/
theorem theorem8_dual_candidate_psi_closed_form
    {m : ℕ} (i : Fin m) :
    MSVV07SourceLemmas.paperRoutePsiCandidate (m := m) i =
      1 - (1 - 1 / (((m + 1 : ℕ) : ℝ))) ^ (m - i.val) := by
  exact MSVV07SourceLemmas.paperRoutePsiCandidate_eq_closed_form i

/--
Theorem 8 source-route algebraic bridge: `l = b + Δ`, the Section 4 base
dual bound, and Lemma 7's `N/k` perturbation bound imply the paper's finite
`N/e + N/k` tradeoff-LP dual-value bound.
-/
theorem theorem8_source_route_dual_value_bound
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
    MSVV07SourceLemmas.theorem8_source_route_dual_value_bound
      N k alpha beta y l hl hbase hperturb

/--
Theorem 8 source-route exact finite base bound for the displayed dual
candidate `y*`.
-/
theorem theorem8_source_route_dual_candidate_value_bound_exact_base
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
    MSVV07SourceLemmas.theorem8_source_route_dual_candidate_value_bound_exact_base
      N k alpha beta l hl hperturb

/--
Theorem 8 source-route dual feasibility for the displayed dual candidate `y*`
in the tradeoff-revealing LP with the paper objective coefficients.
-/
theorem theorem8_source_route_dual_candidate_tradeoff_feasible
    {m : ℕ} (l : Fin m → ℝ) :
    (MSVV07SourceLemmas.tradeoffRevealingLP
      (m := m) MSVV07SourceLemmas.paperRoutePrimalObjectiveCoeff l).DualFeasible
      MSVV07SourceLemmas.paperRouteDualCandidate := by
  exact MSVV07SourceLemmas.theorem8_source_route_dual_candidate_tradeoff_feasible l

/--
Theorem 8 source-route LP upper bound: the same `N/e + N/k` algebra, combined
with finite weak duality, upper-bounds every feasible tradeoff-LP primal value.
-/
theorem theorem8_source_route_tradeoff_lp_upper_bound
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
    MSVV07SourceLemmas.theorem8_source_route_tradeoff_lp_upper_bound
      N k c alpha beta y l hy hl hbase hperturb hx

/--
Theorem 8 source-route exact finite LP upper bound using the displayed dual
candidate `y*` and the exact Section 4 finite base value.
-/
theorem theorem8_source_route_tradeoff_lp_upper_bound_exact_base
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
    MSVV07SourceLemmas.theorem8_source_route_tradeoff_lp_upper_bound_exact_base
      N k alpha beta l hl hperturb hx

/--
Theorem 8 source-route query-accounting wrapper: Lemma 7's accounting
hypotheses feed directly into the exact finite tradeoff-LP upper bound for
the displayed dual candidate.
-/
theorem theorem8_source_route_tradeoff_lp_upper_bound_from_query_accounting
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
    MSVV07SourceLemmas.theorem8_source_route_tradeoff_lp_upper_bound_from_query_accounting
      N k alpha beta l opt alg queryType querySlab hl
      htradeoff_sum hopt_accounting halg_accounting_N_div_k hx

/--
Theorem 8 source-route wrapper from pointwise tradeoff and fiber accounting.
The right-hand side vector is specialized to the paper's `b + Δ`, and the
displayed dual candidate supplies nonnegative `ψ` weights.
-/
theorem theorem8_source_route_tradeoff_lp_upper_bound_from_pointwise_fibers
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
  have hperturb :
      (∑ i : Fin m,
        MSVV07SourceLemmas.paperRoutePsiCandidate (m := m) i *
          (alpha i - beta i)) ≤ N / (k : ℝ) :=
    proof_section5_lemma7_weighted_perturbation_bound_exact_N_div_k_from_pointwise_fibers
      (MSVV07SourceLemmas.paperRoutePsiCandidate (m := m))
      alpha beta opt alg queryType querySlab N k
      hpointwise hα theorem8_dual_candidate_psi_nonnegative hβ hfinal_nonneg
  exact
    theorem8_source_route_tradeoff_lp_upper_bound_exact_base
      N k alpha beta
      (fun i => MSVV07SourceLemmas.paperRouteRhs N i +
        MSVV07SourceLemmas.paperRouteDelta alpha beta i)
      (by intro i; rfl) hperturb hx

/-! ## Section 5 / Theorem 8: Balance/MSVV is `1 - 1/e` competitive -/

/--
Paper-facing small-bids limiting family. The paper's limiting theorem is about
a sequence of finite instances whose bids become small relative to budgets;
these fields spell out that limiting model.
-/
structure PaperSmallBidsLimitFamily
    (Advertiser : Type*) [Fintype Advertiser] [Nonempty Advertiser]
    [DecidableEq Advertiser] where
  queryCount : ℕ → ℕ
  instanceAt : (k : ℕ) → PaperInstance Advertiser (Fin (queryCount k))
  optLimit : ℝ
  revenueLimit : ℝ
  nonnegative_bids : ∀ k, (instanceAt k).NonnegativeBids
  positive_budgets : ∀ k, (instanceAt k).PositiveBudgets
  maxBidSum_pos :
    ∀ k, 0 < ∑ q : Fin (queryCount k), (instanceAt k).maxBidForQuery q
  small_bids_eventually :
    ∀ delta : ℝ, 0 < delta →
      ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
        paperSmallBids (instanceAt k)
          (min 1
            (delta / ((Real.exp 1 + 1) *
              (∑ q : Fin (queryCount k), (instanceAt k).maxBidForQuery q))))
  offlineOptimum_tendsTo :
    Sequence.SeqTendsTo
      (fun k =>
        (instanceAt k).offlineOptimumValue
          (fun a => (positive_budgets k a).le))
      optLimit
  revenue_tendsTo :
    Sequence.SeqTendsTo
      (fun k =>
        (instanceAt k).revenue
          ((instanceAt k).runAssignment (instanceAt k).balanceChoiceRule
            (List.finRange (queryCount k))))
      revenueLimit

namespace PaperSmallBidsLimitFamily

/-- Convert the paper small-bids limiting family into the reusable library package. -/
noncomputable def toLibrary
    {Advertiser : Type*} [Fintype Advertiser] [Nonempty Advertiser]
    [DecidableEq Advertiser]
    (F : PaperSmallBidsLimitFamily Advertiser) :
    AdWordsInstance.MsvvSmallBidsLimitFamily Advertiser where
  queryCount := F.queryCount
  instanceAt := F.instanceAt
  optLimit := F.optLimit
  revenueLimit := F.revenueLimit
  nonnegative_bids := F.nonnegative_bids
  positive_budgets := F.positive_budgets
  maxBidSum_pos := F.maxBidSum_pos
  small_bids_eventually := by
    intro delta hdelta
    obtain ⟨N, hN⟩ := F.small_bids_eventually delta hdelta
    exact ⟨N, fun k hk => by
      simpa [paperSmallBids_eq_library] using hN k hk⟩
  offlineOptimum_tendsTo := F.offlineOptimum_tendsTo
  revenue_tendsTo := F.revenue_tendsTo

end PaperSmallBidsLimitFamily

/--
Theorem 8, finite explicit-error form. For a complete finite query history,
Balance/MSVV gets the `1 - 1/e` scaled offline optimum up to the explicit
small-bids error.
-/
theorem theorem8_finite_explicit_error
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
  rw [paperMsvvRatio_eq_library, paperRevenue_eq_library]
  exact
    paper_adwords_balance_msvv_approx_competitive_with_query_sum_error_bound
      I hbid hbudget history hnodup hcover hepsilon hepsilon_le_one
      (by simpa [paperSmallBids_eq_library] using hsmall)

/--
Source-shaped asymptotic form of Theorem 8.  If the explicit finite small-bids
error tends to zero, then for every positive tolerance the Balance/MSVV
competitive inequality holds eventually.  No convergence of OPT or revenue is
assumed.
-/
theorem theorem8_balance_msvv_eventually_competitive_of_vanishing_small_bids_error
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
  have herror_eventually :
      ∀ delta : ℝ, 0 < delta →
        ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
          epsilon k * (Real.exp 1 + 1) *
              (∑ q : Fin (n k), (I k).maxBidForQuery q) ≤ delta := by
    intro delta hdelta
    obtain ⟨N, hN⟩ := herror_tendsTo_zero delta hdelta
    refine ⟨N, ?_⟩
    intro k hk
    have habs := hN k hk
    have hle_abs :
        epsilon k * (Real.exp 1 + 1) *
            (∑ q : Fin (n k), (I k).maxBidForQuery q) ≤
          |epsilon k * (Real.exp 1 + 1) *
            (∑ q : Fin (n k), (I k).maxBidForQuery q)| :=
      le_abs_self _
    have habs' :
        |epsilon k * (Real.exp 1 + 1) *
          (∑ q : Fin (n k), (I k).maxBidForQuery q)| ≤ delta := by
      simpa using habs
    exact hle_abs.trans habs'
  rw [paperMsvvRatio_eq_library]
  exact
    AdWordsInstance.balance_msvv_finRange_family_eventually_up_to_delta
      n I epsilon hbid hbudget hepsilon hepsilon_le_one
      (fun k => by simpa [paperSmallBids_eq_library] using hsmall k)
      herror_eventually

/--
Theorem 8, paper-level limiting endpoint. Any finite-query small-bids family
satisfying the explicit threshold eventually has limiting competitive ratio
`1 - 1/e`.
-/
theorem proof_theorem8_balance_msvv_competitive_of_small_bids_limit_family
    {Advertiser : Type*}
    [Fintype Advertiser] [Nonempty Advertiser] [DecidableEq Advertiser]
    (F : PaperSmallBidsLimitFamily Advertiser) :
    paperMsvvRatio * F.optLimit ≤ F.revenueLimit := by
  rw [paperMsvvRatio_eq_library]
  exact
    paper_adwords_balance_msvv_competitive_of_small_bids_limit_family
      F.toLibrary

/-! ## Section 6 and Section 8: model extensions by effective bids -/

/--
Section 6 items 1--2. Different advertiser budgets and nonexhaustive optima are
already part of the base AdWords model, so the finite explicit Theorem 8
guarantee applies without changing the instance.
-/
theorem proof_section6_different_budgets_and_nonexhaustive_optimum_theorem8_finite_explicit_error
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
  exact theorem8_finite_explicit_error
    I hbid hbudget history hnodup hcover hepsilon hepsilon_le_one hsmall

/-- Section 6: arbitrary effective charges preserve the paper small-bids condition. -/
theorem section6_effective_bids_small_bids
    {Advertiser Query : Type*}
    (I : PaperInstance Advertiser Query)
    (effectiveBid : Advertiser → Query → ℝ) {epsilon : ℝ}
    (hsmall : ∀ a q, effectiveBid a q ≤ epsilon * I.budget a) :
    paperSmallBids (I.withEffectiveBids effectiveBid) epsilon := by
  simpa [paperSmallBids_eq_library] using
    paper_adwords_effective_bids_small_bids I effectiveBid hsmall

/-- Section 6 next-price charge from all bidders, floored at zero. -/
noncomputable def section6_next_highest_bid_all
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query) (a : Advertiser) (q : Query) : ℝ := by
  classical
  let others : Finset Advertiser := (Finset.univ : Finset Advertiser).erase a
  by_cases h : others.Nonempty
  · exact max 0 (others.sup' h fun b => I.bid b q)
  · exact 0

/-- Section 6 next-price charge among alive bidders, floored at zero. -/
noncomputable def section6_next_highest_bid_alive
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (alive : Advertiser → Query → Prop) [∀ a q, Decidable (alive a q)]
    (a : Advertiser) (q : Query) : ℝ := by
  classical
  let others : Finset Advertiser :=
    ((Finset.univ : Finset Advertiser).erase a).filter fun b => alive b q
  by_cases h : others.Nonempty
  · exact max 0 (others.sup' h fun b => I.bid b q)
  · exact 0

/-- The all-bidders next-price effective charge is nonnegative. -/
theorem section6_next_highest_bid_all_nonnegative
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query) :
    ∀ a q, 0 ≤ section6_next_highest_bid_all I a q := by
  intro a q
  classical
  unfold section6_next_highest_bid_all
  by_cases h : ((Finset.univ : Finset Advertiser).erase a).Nonempty
  · simp [h]
  · simp [h]

/-- The alive-bidders next-price effective charge is nonnegative. -/
theorem section6_next_highest_bid_alive_nonnegative
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (alive : Advertiser → Query → Prop) [∀ a q, Decidable (alive a q)] :
    ∀ a q, 0 ≤ section6_next_highest_bid_alive I alive a q := by
  intro a q
  classical
  unfold section6_next_highest_bid_alive
  by_cases h :
      (((Finset.univ : Finset Advertiser).erase a).filter fun b => alive b q).Nonempty
  · simp [h]
  · simp [h]

/-- Section 6: click-through-rate effective bids preserve small bids when CTRs are at most one. -/
theorem section6_click_through_rates_small_bids
    {Advertiser Query : Type*}
    (I : PaperInstance Advertiser Query)
    (ctr : Advertiser → Query → ℝ) {epsilon : ℝ}
    (hbid : I.NonnegativeBids)
    (hctr_le_one : ∀ a q, ctr a q ≤ 1)
    (hsmall : paperSmallBids I epsilon) :
    paperSmallBids (I.withClickThroughRates ctr) epsilon := by
  simpa [paperSmallBids_eq_library] using
    paper_adwords_click_through_rates_small_bids I ctr hctr_le_one hbid
      (by simpa [paperSmallBids_eq_library] using hsmall)

/-- Section 6: delayed-entry availability masks preserve small bids. -/
theorem section6_availability_small_bids
    {Advertiser Query : Type*}
    (I : PaperInstance Advertiser Query)
    (available : Advertiser → Query → Prop) {epsilon : ℝ}
    [∀ a q, Decidable (available a q)]
    (hepsilon : 0 ≤ epsilon)
    (hbudget : I.PositiveBudgets)
    (hsmall : paperSmallBids I epsilon) :
    paperSmallBids (I.withAvailability available) epsilon := by
  simpa [paperSmallBids_eq_library] using
    paper_adwords_availability_small_bids I available hepsilon hbudget
      (by simpa [paperSmallBids_eq_library] using hsmall)

/-- Section 6: multiple slots per query reduce to distinct slot-query IDs. -/
theorem section6_multiple_slots_small_bids
    {Advertiser Query : Type*}
    (I : PaperInstance Advertiser Query) {epsilon : ℝ}
    (Slot : Query → Type*)
    (hsmall : paperSmallBids I epsilon) :
    paperSmallBids (I.withSlots Slot) epsilon := by
  simpa [paperSmallBids_eq_library] using
    paper_adwords_multiple_slots_small_bids I Slot
      (by simpa [paperSmallBids_eq_library] using hsmall)

/--
Section 6 multiple slots: running a slot-expanded rule through the
distinct-advertiser wrapper enforces per-page distinct advertisers.

This is intentionally only an invariant for the wrapped run. The finite
competitive guarantee below remains the ordinary slot-expanded Balance/MSVV
endpoint, not a guarantee for the wrapped rule.
-/
theorem section6_multiple_slots_distinct_choice_run_per_page_distinct
    {Advertiser Query : Type*} {Slot : Query → Type*}
    [Fintype (Σ q : Query, Slot q)]
    [DecidableEq Advertiser] [DecidableEq (Σ q : Query, Slot q)]
    (I : PaperInstance Advertiser Query)
    (rule : AdWordsInstance.ChoiceRule Advertiser (Σ q : Query, Slot q))
    (history : List (Σ q : Query, Slot q)) :
    paperSlotsPerPageDistinct Slot
      ((I.withSlots Slot).runAssignment
        (AdWordsInstance.withSlotsDistinctChoice Slot rule) history) := by
  exact
    AdWordsInstance.withSlotsDistinctChoice_runAssignment_per_page_distinct
      Slot (I.withSlots Slot) rule history

/-- Section 8: advertiser-weighted effective bids preserve small bids for weights in `[0,1]`. -/
theorem section8_weighted_bids_small_bids
    {Advertiser Query : Type*}
    (I : PaperInstance Advertiser Query)
    (weight : Advertiser → ℝ) {epsilon : ℝ}
    (hbid : I.NonnegativeBids)
    (hweight_le_one : ∀ a, weight a ≤ 1)
    (hsmall : paperSmallBids I epsilon) :
    paperSmallBids (I.withAdvertiserWeights weight) epsilon := by
  simpa [paperSmallBids_eq_library] using
    paper_adwords_weighted_bids_small_bids I weight hweight_le_one hbid
      (by simpa [paperSmallBids_eq_library] using hsmall)

/--
Section 6 effective-bid variant composed with Theorem 8. The transformed
effective-charge instance receives the same finite explicit MSVV guarantee.
-/
theorem section6_effective_bids_theorem8_finite_explicit_error
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
    theorem8_finite_explicit_error
      (I.withEffectiveBids effectiveBid)
      (AdWordsInstance.withEffectiveBids_nonnegativeBids I effectiveBid hbid)
      (AdWordsInstance.withEffectiveBids_positiveBudgets I effectiveBid hbudget)
      history hnodup hcover hepsilon hepsilon_le_one
      (section6_effective_bids_small_bids I effectiveBid hsmall)

/--
Section 6 next-price variant using the next-highest bid among all initial bids.
Once these next-price charges satisfy the paper's small-bids condition, the
finite explicit Theorem 8 guarantee applies.
-/
theorem proof_section6_next_highest_bid_all_theorem8_finite_explicit_error
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
    section6_effective_bids_theorem8_finite_explicit_error
      I (section6_next_highest_bid_all I)
      (section6_next_highest_bid_all_nonnegative I)
      hbudget history hnodup hcover hepsilon hepsilon_le_one hnext_small

/--
Section 6 next-price variant using the next-highest bid among alive bidders.
When the online model keeps alive bidders so this charge process is available
and the resulting charges are small, the finite explicit Theorem 8 guarantee
applies to the induced effective-bid instance.
-/
theorem proof_section6_next_highest_bid_alive_theorem8_finite_explicit_error
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
    section6_effective_bids_theorem8_finite_explicit_error
      I (section6_next_highest_bid_alive I alive)
      (section6_next_highest_bid_alive_nonnegative I alive)
      hbudget history hnodup hcover hepsilon hepsilon_le_one hnext_small

/--
Section 6 click-through-rate variant composed with Theorem 8. CTR-weighted
effective bids inherit the finite explicit MSVV guarantee.
-/
theorem proof_section6_click_through_rates_theorem8_finite_explicit_error
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
    theorem8_finite_explicit_error
      (I.withClickThroughRates ctr)
      (AdWordsInstance.withClickThroughRates_nonnegativeBids I ctr
        hctr_nonneg hbid)
      (AdWordsInstance.withClickThroughRates_positiveBudgets I ctr hbudget)
      history hnodup hcover hepsilon hepsilon_le_one
      (section6_click_through_rates_small_bids I ctr hbid hctr_le_one hsmall)

/--
Section 6 availability/delayed-entry variant composed with Theorem 8. Zeroing
inactive advertisers' bids preserves the finite explicit MSVV guarantee.
-/
theorem proof_section6_availability_theorem8_finite_explicit_error
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
    theorem8_finite_explicit_error
      (I.withAvailability available)
      (AdWordsInstance.withAvailability_nonnegativeBids I available hbid)
      (AdWordsInstance.withAvailability_positiveBudgets I available hbudget)
      history hnodup hcover hepsilon hepsilon_le_one
      (section6_availability_small_bids I available hepsilon hbudget hsmall)

/--
Section 6 multiple-slot variant composed with Theorem 8. Expanding every slot
to an ordinary query receives the same finite explicit MSVV guarantee.
-/
theorem section6_multiple_slots_theorem8_finite_explicit_error
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
    theorem8_finite_explicit_error
      (I.withSlots Slot)
      (AdWordsInstance.withSlots_nonnegativeBids I Slot hbid)
      (AdWordsInstance.withSlots_positiveBudgets I Slot hbudget)
      history hnodup hcover hepsilon hepsilon_le_one
      (section6_multiple_slots_small_bids I Slot hsmall)

/--
Section 6 multiple slots, source-shaped page rule. For each arriving page `q`,
the rule simultaneously chooses the top `slots q` distinct feasible advertisers
by the Balance/MSVV scaled bid. The benchmark is the page-level offline optimum
with at most `slots q` distinct advertisers per page.
-/
theorem proof_section6_page_top_balance_theorem8_finite_explicit_error
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
  rw [paperMsvvRatio_eq_library]
  exact
    AdWordsInstance.page_top_balance_msvv_approx_competitive_with_error_bound
      I hbid hbudget slots history hnodup hcover hepsilon hepsilon_le_one
      (by simpa [paperSmallBids_eq_library] using hsmall)

/--
Section 8 weighted-bid variant composed with Theorem 8. Weighted effective
bids inherit the finite explicit MSVV guarantee.
-/
theorem section8_weighted_bids_theorem8_finite_explicit_error
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
    theorem8_finite_explicit_error
      (I.withAdvertiserWeights weight)
      (AdWordsInstance.withAdvertiserWeights_nonnegativeBids I weight
        hweight_nonneg hbid)
      (AdWordsInstance.withAdvertiserWeights_positiveBudgets I weight hbudget)
      history hnodup hcover hepsilon hepsilon_le_one
      (section8_weighted_bids_small_bids I weight hbid hweight_le_one hsmall)

/--
Section 8 weighted-bid variant without normalizing weights by one. If the
weighted effective bids themselves are nonnegative and small, they inherit the
finite explicit MSVV guarantee.
-/
theorem proof_section8_weighted_bids_theorem8_finite_explicit_error_of_weighted_small_bids
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
    section6_effective_bids_theorem8_finite_explicit_error
      I (fun a q => weight a * I.bid a q)
      (fun a q => mul_nonneg (hweight_nonneg a) (hbid a q))
      hbudget history hnodup hcover hepsilon hepsilon_le_one hweighted_small

/-! ## Section 7 / Theorem 9: b-matching randomized lower bound -/

/-- The hard distribution in Theorem 9 is uniform over bidder permutations. -/
noncomputable abbrev theorem9HardDistribution (N : ℕ) :
    PMF (Equiv.Perm (Fin N)) :=
  uniformPermutationDistribution N

/--
Theorem 9 deterministic algorithms in this formalization: a finite integral
prefix algorithm sees only the observed prefix and chooses at most one visible
eligible bidder each round.
-/
abbrev theorem9IntegralPrefixAlgorithm (N : ℕ) :=
  BMatchingIntegralPrefixAlgorithm N

/--
The randomized online algorithms used in Theorem 9, formalized as probability
distributions over finite integral prefix algorithms.
-/
abbrev theorem9RandomizedOnlineAlgorithm (N : ℕ) :=
  PMF (theorem9IntegralPrefixAlgorithm N)

/--
The broader finite online-information model for Theorem 9: feasible real-valued
allocation rules that depend only on the observed prefix.
-/
abbrev theorem9FeasiblePrefixRuleFamily
    (Algorithm : ℕ → Type*)
    [∀ N, Fintype (Algorithm N)] [∀ N, DecidableEq (Algorithm N)] :=
  BMatchingTheorem9FeasiblePrefixRuleFamily Algorithm

/-- The capped normalized revenue expression used in the Section 7 proof. -/
noncomputable abbrev theorem9CappedNormalizedRevenue
    (N : ℕ) (algorithm : theorem9IntegralPrefixAlgorithm N)
    (permutation : Equiv.Perm (Fin N)) : ℝ :=
  paper_adwords_theorem9_integral_prefix_algorithm_family.normalizedRevenue
    N algorithm permutation

/--
The canonical normalized payoff in the Theorem 9 endpoint is exactly the paper's
capped spend expression for integral prefix algorithms.
-/
theorem theorem9_capped_normalized_revenue_eq_prefix_spend
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
  exact
    paper_adwords_theorem9_integral_prefix_algorithm_family_normalized_revenue_eq_capped_spend
      N algorithm permutation

/--
Theorem 9 harmonic-cap lemma: the finite normalized hard-instance revenue cap
is eventually within every positive additive error of `1 - 1/e`.
-/
theorem theorem9_harmonic_eventually_le_msvv_ratio_add_delta :
    ∀ delta : ℝ, 0 < delta →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        theorem9NormalizedRevenueUpperBound N ≤
          paperMsvvRatio + delta := by
  rw [paperMsvvRatio_eq_library]
  exact paper_adwords_theorem9_harmonic_eventually_le_msvv_ratio_add_delta

/--
Theorem 9, broad finite online-information endpoint. No randomized
distribution over any finite family of feasible observed-prefix allocation
rules, with payoff defined by the paper's capped normalized spend expression,
can beat `1 - 1/e + delta` on every sufficiently large hard instance.
-/
theorem theorem9_no_randomized_feasible_prefix_rule_family_beats_msvv_ratio
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
  rw [paperMsvvRatio_eq_library]
  exact
    paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_feasible_prefix_rule_family
      C

/--
Theorem 9, concrete integral-prefix endpoint. No randomized distribution over
finite prefix algorithms can beat `1 - 1/e + delta` on every sufficiently large
permutation instance of the hard b-matching family.
-/
theorem theorem9_no_randomized_integral_prefix_algorithm_beats_msvv_ratio
    :
    ∀ delta : ℝ, 0 < delta →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        ∀ randomizedAlgorithm : PMF (theorem9IntegralPrefixAlgorithm N),
          ¬ ∀ permutation,
            paperMsvvRatio + delta <
              AppliedModelingLib.pmfExp randomizedAlgorithm
                (fun algorithm =>
                  theorem9CappedNormalizedRevenue N algorithm permutation) := by
  rw [paperMsvvRatio_eq_library]
  exact
    paper_adwords_theorem9_eventually_no_randomized_algorithm_beats_msvv_ratio_add_delta_of_integral_prefix_algorithms

/--
Theorem 9, paper-facing randomized online algorithm endpoint in the finite
prefix model.
-/
theorem proof_theorem9_no_randomized_online_algorithm_beats_msvv_ratio :
    ∀ delta : ℝ, 0 < delta →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        ∀ randomizedAlgorithm : theorem9RandomizedOnlineAlgorithm N,
          ¬ ∀ permutation,
            paperMsvvRatio + delta <
              AppliedModelingLib.pmfExp randomizedAlgorithm
                (fun algorithm =>
                  theorem9CappedNormalizedRevenue N algorithm permutation) := by
  exact theorem9_no_randomized_integral_prefix_algorithm_beats_msvv_ratio

end MSVV07PaperFacing.Proof
end Online
end AppliedModelingLib

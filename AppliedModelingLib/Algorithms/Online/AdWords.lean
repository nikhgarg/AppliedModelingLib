import AppliedModelingLib.Foundations.Math.Sequence
import AppliedModelingLib.Foundations.Optimization.Approximation
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.FinRange
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith

open scoped BigOperators

namespace AppliedModelingLib
namespace Online

/--
Finite AdWords-style instance.

`budget a` is advertiser `a`'s budget and `bid a q` is the revenue/spend
contribution from assigning query `q` to advertiser `a`.
-/
structure AdWordsInstance (Advertiser Query : Type*) where
  budget : Advertiser → ℝ
  bid : Advertiser → Query → ℝ

namespace AdWordsInstance

variable {Advertiser Query : Type*}

/-- An offline assignment of every query to either one advertiser or nobody. -/
abbrev Assignment (Advertiser Query : Type*) :=
  Query → Option Advertiser

/-- Fractional AdWords assignment variables `x a q`. -/
abbrev FractionalAssignment (Advertiser Query : Type*) :=
  Advertiser → Query → ℝ

/-- The assignment that leaves every query unmatched. -/
def emptyAssignment : Assignment Advertiser Query :=
  fun _ => none

/-- Update an assignment by assigning query `q` to advertiser `a`. -/
def assignQuery [DecidableEq Query]
    (A : Assignment Advertiser Query) (q : Query) (a : Advertiser) :
    Assignment Advertiser Query :=
  fun q' => if q' = q then some a else A q'

/-- State carried by an online AdWords algorithm over a query history. -/
structure HistoryState (Advertiser Query : Type*) where
  assignment : Assignment Advertiser Query
  seen : Finset Query

/-- Initial online state: nothing assigned and no queries seen. -/
def initialHistoryState [DecidableEq Query] : HistoryState Advertiser Query where
  assignment := emptyAssignment
  seen := ∅

/-- The finite set of query identifiers appearing in a history list. -/
def historyFinset [DecidableEq Query] : List Query → Finset Query
  | [] => ∅
  | q :: qs => insert q (historyFinset qs)

theorem mem_historyFinset [DecidableEq Query]
    {history : List Query} {q : Query} :
    q ∈ historyFinset history ↔ q ∈ history := by
  induction history with
  | nil =>
      simp [historyFinset]
  | cons r rs ih =>
      simp [historyFinset, ih]

theorem sum_historyFinset_eq_list_sum [DecidableEq Query]
    (history : List Query) (hnodup : history.Nodup) (f : Query → ℝ) :
    (∑ q ∈ historyFinset history, f q) = (history.map f).sum := by
  induction history with
  | nil =>
      simp [historyFinset]
  | cons q qs ih =>
      have hparts := List.nodup_cons.mp hnodup
      have hnot : q ∉ historyFinset qs := by
        intro hmem
        exact hparts.1 ((mem_historyFinset (history := qs) (q := q)).1 hmem)
      simp [historyFinset, hnot, ih hparts.2]

theorem sum_univ_eq_list_sum_of_historyFinset_eq_univ
    [Fintype Query] [DecidableEq Query]
    (history : List Query) (hnodup : history.Nodup)
    (hcover : historyFinset history = Finset.univ) (f : Query → ℝ) :
    (∑ q : Query, f q) = (history.map f).sum := by
  rw [← hcover]
  exact sum_historyFinset_eq_list_sum history hnodup f

theorem historyFinset_finRange (n : ℕ) :
    historyFinset (List.finRange n) = (Finset.univ : Finset (Fin n)) := by
  ext q
  rw [mem_historyFinset]
  simp

theorem finRange_history_nodup (n : ℕ) :
    (List.finRange n).Nodup :=
  List.nodup_finRange n

/-- Spend charged to one advertiser by an assignment. -/
noncomputable def spend [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (a : Advertiser) : ℝ :=
  ∑ q : Query,
    match A q with
    | none => 0
    | some a' => if a' = a then I.bid a q else 0

/-- Total revenue of an assignment. -/
noncomputable def revenue [Fintype Query]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) : ℝ :=
  ∑ q : Query,
    match A q with
    | none => 0
    | some a => I.bid a q

/-- Budget feasibility: no advertiser is charged above her budget. -/
def Feasible [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) : Prop :=
  ∀ a, I.spend A a ≤ I.budget a

/-- Revenue of a fractional AdWords assignment. -/
noncomputable def fractionalRevenue
    [Fintype Advertiser] [Fintype Query]
    (I : AdWordsInstance Advertiser Query)
    (X : FractionalAssignment Advertiser Query) : ℝ :=
  ∑ q : Query, ∑ a : Advertiser, I.bid a q * X a q

/--
Feasibility of the standard fractional AdWords LP: nonnegative assignment
variables, at most one unit assigned per query, and advertiser budget
constraints.
-/
structure FractionalFeasible
    [Fintype Advertiser] [Fintype Query]
    (I : AdWordsInstance Advertiser Query)
    (X : FractionalAssignment Advertiser Query) : Prop where
  nonneg : ∀ a q, 0 ≤ X a q
  query : ∀ q, (∑ a : Advertiser, X a q) ≤ 1
  budget : ∀ a, (∑ q : Query, I.bid a q * X a q) ≤ I.budget a

/-- Embed an integral assignment as a `0/1` fractional assignment. -/
def assignmentFraction [DecidableEq Advertiser]
    (A : Assignment Advertiser Query) :
    FractionalAssignment Advertiser Query :=
  fun a q =>
    match A q with
    | none => 0
    | some owner => if owner = a then 1 else 0

/-- Remaining budget for advertiser `a` under assignment `A`. -/
noncomputable def residualBudget [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (a : Advertiser) : ℝ :=
  I.budget a - I.spend A a

/--
An advertiser can accept query `q` after the partial assignment `A` if adding
the query's bid would still respect her budget.
-/
def CanAssign [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (q : Query) (a : Advertiser) : Prop :=
  I.spend A a + I.bid a q ≤ I.budget a

/-- Entrywise nonnegative bids. -/
def NonnegativeBids (I : AdWordsInstance Advertiser Query) : Prop :=
  ∀ a q, 0 ≤ I.bid a q

/-- Nonnegative advertiser budgets. -/
def NonnegativeBudgets (I : AdWordsInstance Advertiser Query) : Prop :=
  ∀ a, 0 ≤ I.budget a

/-- Strictly positive advertiser budgets. -/
def PositiveBudgets (I : AdWordsInstance Advertiser Query) : Prop :=
  ∀ a, 0 < I.budget a

/-- Small-bids condition: every bid is at most an `ε` fraction of the budget. -/
def SmallBids (I : AdWordsInstance Advertiser Query) (ε : ℝ) : Prop :=
  ∀ a q, I.bid a q ≤ ε * I.budget a

/-- A choice rule maps the current assignment and query to an optional advertiser. -/
abbrev ChoiceRule (Advertiser Query : Type*) :=
  Assignment Advertiser Query → Query → Option Advertiser

/--
A choice rule is feasible if every advertiser it returns can accept the query
under the current assignment.
-/
def ChoiceRuleFeasible
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (rule : ChoiceRule Advertiser Query) : Prop :=
  ∀ A q a, rule A q = some a → I.CanAssign A q a

/--
Online-state invariant: the current assignment is budget-feasible and every
query outside the `seen` set is still unassigned.
-/
def StateInvariant
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (S : HistoryState Advertiser Query) : Prop :=
  I.Feasible S.assignment ∧ ∀ q, q ∉ S.seen → S.assignment q = none

/--
The finite set of feasible offline assignments. This is the offline benchmark
domain for AdWords-style competitive-ratio statements.
-/
noncomputable def feasibleAssignments
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query) :
    Finset (Assignment Advertiser Query) := by
  classical
  exact Finset.univ.filter fun A => I.Feasible A

/-- An assignment is offline-optimal if it is feasible and dominates all feasible assignments. -/
def IsOptimalAssignment [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) : Prop :=
  I.Feasible A ∧ ∀ B, I.Feasible B → I.revenue B ≤ I.revenue A

/--
Dual feasibility for the standard AdWords LP relaxation:
`bid a q ≤ bid a q * alpha a + beta q`, with nonnegative dual variables.
-/
structure DualFeasible
    (I : AdWordsInstance Advertiser Query)
    (alpha : Advertiser → ℝ) (beta : Query → ℝ) : Prop where
  alpha_nonneg : ∀ a, 0 ≤ alpha a
  beta_nonneg : ∀ q, 0 ≤ beta q
  covers : ∀ a q, I.bid a q ≤ I.bid a q * alpha a + beta q

/-- Objective value of an AdWords LP dual solution. -/
noncomputable def dualObjective
    [Fintype Advertiser] [Fintype Query]
    (I : AdWordsInstance Advertiser Query)
    (alpha : Advertiser → ℝ) (beta : Query → ℝ) : ℝ :=
  (∑ a : Advertiser, I.budget a * alpha a) + ∑ q : Query, beta q

/--
The part of the dual objective induced by advertisers actually assigned by an
offline assignment.
-/
noncomputable def assignedWeightedSpend
    [Fintype Query]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (alpha : Advertiser → ℝ) : ℝ :=
  ∑ q : Query,
    match A q with
    | none => 0
    | some a => I.bid a q * alpha a

/-- The fraction of advertiser `a`'s budget already spent. -/
noncomputable def spentFraction [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (a : Advertiser) : ℝ :=
  I.spend A a / I.budget a

/--
The MSVV/Balance discount factor as a function of used budget fraction.
For fractions in `[0, 1]`, this lies in `[0, 1]`.
-/
noncomputable def balanceDiscount (x : ℝ) : ℝ :=
  1 - Real.exp (x - 1)

/-- The MSVV dual variable as a function of used budget fraction. -/
noncomputable def msvvDualAlpha (x : ℝ) : ℝ :=
  Real.exp (x - 1)

/--
The normalized MSVV advertiser dual used in the standard dual-fitting proof.
It starts at zero when the spent fraction is zero and reaches one at a fully
spent budget.
-/
noncomputable def msvvNormalizedDualAlpha (x : ℝ) : ℝ :=
  (Real.exp x - 1) / (Real.exp 1 - 1)

/-- The classical MSVV competitive ratio `1 - 1/e`. -/
noncomputable def msvvRatio : ℝ :=
  1 - 1 / Real.exp 1

/-- Balance/MSVV scaled bid for assigning query `q` to advertiser `a`. -/
noncomputable def balanceScore [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (a : Advertiser) (q : Query) : ℝ :=
  I.bid a q * balanceDiscount (I.spentFraction A a)

/-- MSVV advertiser duals induced by an assignment's spent fractions. -/
noncomputable def msvvAlphaFromAssignment
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (a : Advertiser) : ℝ :=
  msvvDualAlpha (I.spentFraction A a)

/-- Normalized MSVV advertiser duals induced by an assignment's spent fractions. -/
noncomputable def msvvNormalizedAlphaFromAssignment
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (a : Advertiser) : ℝ :=
  msvvNormalizedDualAlpha (I.spentFraction A a)

/-- Budget-weighted mass of normalized MSVV advertiser duals. -/
noncomputable def msvvNormalizedAlphaBudgetMass
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) : ℝ :=
  ∑ a : Advertiser, I.budget a * I.msvvNormalizedAlphaFromAssignment A a

/-- Slack-score form of a dual covering constraint for one advertiser-query pair. -/
noncomputable def slackScore
    (I : AdWordsInstance Advertiser Query)
    (alpha : Advertiser → ℝ) (a : Advertiser) (q : Query) : ℝ :=
  I.bid a q * (1 - alpha a)

/--
For a fixed advertiser dual `alpha`, choose the nonnegative query dual `beta q`
as the maximum advertiser slack score for query `q`, floored at zero.
-/
noncomputable def maxSlackBeta
    [Fintype Advertiser] [Nonempty Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (alpha : Advertiser → ℝ) (q : Query) : ℝ := by
  classical
  let scores : Finset ℝ :=
    Finset.univ.image fun a : Advertiser => I.slackScore alpha a q
  have hscores : scores.Nonempty := by
    obtain ⟨a⟩ := (inferInstance : Nonempty Advertiser)
    exact ⟨I.slackScore alpha a q, by simp [scores]⟩
  exact max 0 (scores.max' hscores)

/-- The largest bid for a query, floored at zero. -/
noncomputable def maxBidForQuery
    [Fintype Advertiser] [Nonempty Advertiser]
    (I : AdWordsInstance Advertiser Query) (q : Query) : ℝ := by
  classical
  let bids : Finset ℝ :=
    Finset.univ.image fun a : Advertiser => I.bid a q
  have hbids : bids.Nonempty := by
    obtain ⟨a⟩ := (inferInstance : Nonempty Advertiser)
    exact ⟨I.bid a q, by simp [bids]⟩
  exact max 0 (bids.max' hbids)

/-- Feasible advertisers for the next query under the current partial assignment. -/
noncomputable def feasibleAdvertisers
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (q : Query) :
    Finset Advertiser := by
  classical
  exact Finset.univ.filter fun a => I.CanAssign A q a

/--
A Balance/MSVV choice maximizes the scaled bid over advertisers that can still
accept the query without exceeding budget.
-/
def IsBalanceChoice
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (q : Query) (a : Advertiser) : Prop :=
  I.CanAssign A q a ∧
    ∀ b, I.CanAssign A q b → I.balanceScore A b q ≤ I.balanceScore A a q

/--
One online update step. Repeated queries are marked as seen but not reassigned;
new queries are assigned according to the choice rule when it returns an
advertiser.
-/
def stepHistoryState
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (_I : AdWordsInstance Advertiser Query)
    (rule : ChoiceRule Advertiser Query)
    (S : HistoryState Advertiser Query) (q : Query) :
    HistoryState Advertiser Query :=
  if q ∈ S.seen then
    { S with seen := insert q S.seen }
  else
    match rule S.assignment q with
    | none => { assignment := S.assignment, seen := insert q S.seen }
    | some a =>
        { assignment := assignQuery S.assignment q a
          seen := insert q S.seen }

/-- Run an online choice rule from an arbitrary state over a finite query history. -/
def runHistoryStateFrom
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (rule : ChoiceRule Advertiser Query) :
    HistoryState Advertiser Query → List Query → HistoryState Advertiser Query
  | S, [] => S
  | S, q :: qs => runHistoryStateFrom I rule (stepHistoryState I rule S q) qs

/-- Run an online choice rule from the initial empty state. -/
def runHistoryState
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (rule : ChoiceRule Advertiser Query) (history : List Query) :
    HistoryState Advertiser Query :=
  runHistoryStateFrom I rule initialHistoryState history

/-- The final assignment returned by an online choice rule on a query history. -/
def runAssignment
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (rule : ChoiceRule Advertiser Query) (history : List Query) :
    Assignment Advertiser Query :=
  (runHistoryState I rule history).assignment

/-- Sum of a query-dual value over a concrete history list. -/
noncomputable def historyMaxSlackBetaSum
    [Fintype Advertiser] [Nonempty Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (alpha : Advertiser → ℝ) : List Query → ℝ
  | [] => 0
  | q :: qs => I.maxSlackBeta alpha q + historyMaxSlackBetaSum I alpha qs

/-- Sum of the finite max-bid exhausted-advertiser error over a history list. -/
noncomputable def historyMaxBidErrorSum
    [Fintype Advertiser] [Nonempty Advertiser]
    (I : AdWordsInstance Advertiser Query) (ε : ℝ) : List Query → ℝ
  | [] => 0
  | q :: qs =>
      I.maxBidForQuery q * (1 - Real.exp (-ε)) +
        historyMaxBidErrorSum I ε qs

/--
Sum of the finite max-bid error used for advertiser-alpha discretization over
a history list.
-/
noncomputable def historyMaxBidAlphaErrorSum
    [Fintype Advertiser] [Nonempty Advertiser]
    (I : AdWordsInstance Advertiser Query) (ε : ℝ) : List Query → ℝ
  | [] => 0
  | q :: qs =>
      I.maxBidForQuery q * (Real.exp ε - 1) +
        historyMaxBidAlphaErrorSum I ε qs

/-- Sum of per-query maximum bids over a concrete history list. -/
noncomputable def historyMaxBidSum
    [Fintype Advertiser] [Nonempty Advertiser]
    (I : AdWordsInstance Advertiser Query) : List Query → ℝ
  | [] => 0
  | q :: qs => I.maxBidForQuery q + historyMaxBidSum I qs

/--
Combined explicit finite small-bids error for the Balance/MSVV proof.
The first term is advertiser-alpha discretization; the second term is the
exhausted-advertiser query-dual error.
-/
noncomputable def historyMsvvSmallBidsErrorSum
    [Fintype Advertiser] [Nonempty Advertiser]
    (I : AdWordsInstance Advertiser Query) (ε : ℝ) (history : List Query) : ℝ :=
  I.historyMaxBidAlphaErrorSum ε history + I.historyMaxBidErrorSum ε history

/--
The list-sum of Balance charges generated by an online run. The definition
mirrors `stepHistoryState`, so repeated queries contribute no new charge.
-/
noncomputable def historyBalanceChargeFrom
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (rule : ChoiceRule Advertiser Query) :
    HistoryState Advertiser Query → List Query → ℝ
  | _S, [] => 0
  | S, q :: qs =>
      let stepCharge :=
        if q ∈ S.seen then
          0
        else
          match rule S.assignment q with
          | none => 0
          | some a => I.balanceScore S.assignment a q
      stepCharge +
        historyBalanceChargeFrom I rule
          (stepHistoryState I rule S q) qs

/-- Revenue increment generated by one online step. -/
noncomputable def stepRevenueCharge
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (rule : ChoiceRule Advertiser Query)
    (S : HistoryState Advertiser Query) (q : Query) : ℝ :=
  if q ∈ S.seen then
    0
  else
    match rule S.assignment q with
    | none => 0
    | some a => I.bid a q

/-- Sum of online revenue increments over a history list. -/
noncomputable def historyRevenueChargeFrom
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (rule : ChoiceRule Advertiser Query) :
    HistoryState Advertiser Query → List Query → ℝ
  | _S, [] => 0
  | S, q :: qs =>
      I.stepRevenueCharge rule S q +
        historyRevenueChargeFrom I rule
          (stepHistoryState I rule S q) qs

theorem historyMaxSlackBetaSum_eq_list_sum
    [Fintype Advertiser] [Nonempty Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (alpha : Advertiser → ℝ) (history : List Query) :
    historyMaxSlackBetaSum I alpha history =
      (history.map fun q => I.maxSlackBeta alpha q).sum := by
  induction history with
  | nil =>
      simp [historyMaxSlackBetaSum]
  | cons q qs ih =>
      simp [historyMaxSlackBetaSum, ih]

theorem historyMaxBidErrorSum_eq_list_sum
    [Fintype Advertiser] [Nonempty Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (ε : ℝ) (history : List Query) :
    historyMaxBidErrorSum I ε history =
      (history.map fun q => I.maxBidForQuery q * (1 - Real.exp (-ε))).sum := by
  induction history with
  | nil =>
      simp [historyMaxBidErrorSum]
  | cons q qs ih =>
      simp [historyMaxBidErrorSum, ih]

theorem historyMaxBidAlphaErrorSum_eq_list_sum
    [Fintype Advertiser] [Nonempty Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (ε : ℝ) (history : List Query) :
    historyMaxBidAlphaErrorSum I ε history =
      (history.map fun q => I.maxBidForQuery q * (Real.exp ε - 1)).sum := by
  induction history with
  | nil =>
      simp [historyMaxBidAlphaErrorSum]
  | cons q qs ih =>
      simp [historyMaxBidAlphaErrorSum, ih]

theorem historyMaxBidSum_eq_list_sum
    [Fintype Advertiser] [Nonempty Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (history : List Query) :
    historyMaxBidSum I history =
      (history.map fun q => I.maxBidForQuery q).sum := by
  induction history with
  | nil =>
      simp [historyMaxBidSum]
  | cons q qs ih =>
      simp [historyMaxBidSum, ih]

theorem historyMsvvSmallBidsErrorSum_eq_list_sum
    [Fintype Advertiser] [Nonempty Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (ε : ℝ) (history : List Query) :
    I.historyMsvvSmallBidsErrorSum ε history =
      (history.map fun q =>
        I.maxBidForQuery q *
          ((Real.exp ε - 1) + (1 - Real.exp (-ε)))).sum := by
  induction history with
  | nil =>
      simp [historyMsvvSmallBidsErrorSum, historyMaxBidAlphaErrorSum,
        historyMaxBidErrorSum]
  | cons q qs ih =>
      calc
        I.historyMsvvSmallBidsErrorSum ε (q :: qs) =
            I.maxBidForQuery q *
                ((Real.exp ε - 1) + (1 - Real.exp (-ε))) +
              I.historyMsvvSmallBidsErrorSum ε qs := by
              simp [historyMsvvSmallBidsErrorSum, historyMaxBidAlphaErrorSum,
                historyMaxBidErrorSum]
              ring
        _ =
            ((q :: qs).map fun q =>
              I.maxBidForQuery q *
                ((Real.exp ε - 1) + (1 - Real.exp (-ε)))).sum := by
              simp [ih]

theorem sum_univ_maxSlackBeta_eq_historyMaxSlackBetaSum_of_cover
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (alpha : Advertiser → ℝ) (history : List Query)
    (hnodup : history.Nodup)
    (hcover : historyFinset history = Finset.univ) :
    (∑ q : Query, I.maxSlackBeta alpha q) =
      historyMaxSlackBetaSum I alpha history := by
  rw [sum_univ_eq_list_sum_of_historyFinset_eq_univ history hnodup hcover]
  rw [historyMaxSlackBetaSum_eq_list_sum]

theorem sum_univ_maxBidError_eq_historyMaxBidErrorSum_of_cover
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (ε : ℝ) (history : List Query)
    (hnodup : history.Nodup)
    (hcover : historyFinset history = Finset.univ) :
    (∑ q : Query, I.maxBidForQuery q * (1 - Real.exp (-ε))) =
      historyMaxBidErrorSum I ε history := by
  rw [sum_univ_eq_list_sum_of_historyFinset_eq_univ history hnodup hcover]
  rw [historyMaxBidErrorSum_eq_list_sum]

theorem sum_univ_maxBidForQuery_eq_historyMaxBidSum_of_cover
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (history : List Query)
    (hnodup : history.Nodup)
    (hcover : historyFinset history = Finset.univ) :
    (∑ q : Query, I.maxBidForQuery q) =
      I.historyMaxBidSum history := by
  rw [sum_univ_eq_list_sum_of_historyFinset_eq_univ history hnodup hcover]
  rw [historyMaxBidSum_eq_list_sum]

/--
A reusable certificate for the competitive-ratio conclusion. The hard paper
proof supplies this certificate for the Balance/MSVV algorithm with ratio
`1 - 1 / Real.exp 1` in the small-bids limit.
-/
structure CompetitiveRatioCertificate
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (ratio : ℝ) : Prop where
  feasible : I.Feasible A
  competitive :
    ∀ Opt, I.IsOptimalAssignment Opt → ratio * I.revenue Opt ≤ I.revenue A

/--
A primal-dual certificate for a competitive ratio. The charging argument can be
isolated to constructing `alpha`, `beta`, and the final scaled dual-objective
bound for the algorithm's assignment.
-/
structure PrimalDualCompetitiveCertificate
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (ratio : ℝ) where
  feasible : I.Feasible A
  ratio_nonneg : 0 ≤ ratio
  alpha : Advertiser → ℝ
  beta : Query → ℝ
  dual_feasible : I.DualFeasible alpha beta
  scaled_dual_bound : ratio * I.dualObjective alpha beta ≤ I.revenue A

theorem spend_emptyAssignment [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query) (a : Advertiser) :
    I.spend (emptyAssignment : Assignment Advertiser Query) a = 0 := by
  simp [spend, emptyAssignment]

theorem revenue_emptyAssignment [Fintype Query]
    (I : AdWordsInstance Advertiser Query) :
    I.revenue (emptyAssignment : Assignment Advertiser Query) = 0 := by
  simp [revenue, emptyAssignment]

theorem revenue_assignQuery_of_unassigned
    [Fintype Query] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (q : Query) (a : Advertiser)
    (hunassigned : A q = none) :
    I.revenue (assignQuery A q a) = I.revenue A + I.bid a q := by
  classical
  unfold revenue assignQuery
  calc
    (∑ q' : Query,
        match (if q' = q then some a else A q') with
        | none => 0
        | some a' => I.bid a' q') =
        ∑ q' : Query,
          ((match A q' with
            | none => 0
            | some a' => I.bid a' q') +
            if q' = q then I.bid a q else 0) := by
      apply Finset.sum_congr rfl
      intro q' _hq'
      by_cases hq : q' = q
      · subst q'
        simp [hunassigned]
      · simp [hq]
    _ = (∑ q' : Query,
          match A q' with
          | none => 0
          | some a' => I.bid a' q') +
        ∑ q' : Query, (if q' = q then I.bid a q else 0) := by
      rw [Finset.sum_add_distrib]
    _ = (∑ q' : Query,
          match A q' with
          | none => 0
          | some a' => I.bid a' q') + I.bid a q := by
      rw [Finset.sum_ite_eq']
      simp

theorem emptyAssignment_feasible [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets) :
    I.Feasible (emptyAssignment : Assignment Advertiser Query) := by
  intro a
  rw [spend_emptyAssignment]
  exact hbudget a

@[simp]
theorem assignQuery_apply_self [DecidableEq Query]
    (A : Assignment Advertiser Query) (q : Query) (a : Advertiser) :
    assignQuery A q a q = some a := by
  simp [assignQuery]

theorem assignQuery_apply_ne [DecidableEq Query]
    (A : Assignment Advertiser Query) {q q' : Query} (a : Advertiser)
    (hne : q' ≠ q) :
    assignQuery A q a q' = A q' := by
  simp [assignQuery, hne]

theorem spend_assignQuery_self_of_unassigned
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (q : Query) (a : Advertiser)
    (hunassigned : A q = none) :
    I.spend (assignQuery A q a) a = I.spend A a + I.bid a q := by
  classical
  unfold spend assignQuery
  calc
    (∑ q' : Query,
        match (if q' = q then some a else A q') with
        | none => 0
        | some a' => if a' = a then I.bid a q' else 0) =
        ∑ q' : Query,
          ((match A q' with
            | none => 0
            | some a' => if a' = a then I.bid a q' else 0) +
            if q' = q then I.bid a q else 0) := by
      apply Finset.sum_congr rfl
      intro q' _hq'
      by_cases hq : q' = q
      · subst q'
        simp [hunassigned]
      · simp [hq]
    _ = (∑ q' : Query,
          match A q' with
          | none => 0
          | some a' => if a' = a then I.bid a q' else 0) +
        ∑ q' : Query, (if q' = q then I.bid a q else 0) := by
      rw [Finset.sum_add_distrib]
    _ = (∑ q' : Query,
          match A q' with
          | none => 0
          | some a' => if a' = a then I.bid a q' else 0) + I.bid a q := by
      rw [Finset.sum_ite_eq']
      simp

theorem spend_assignQuery_other_of_unassigned
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (q : Query) {a b : Advertiser}
    (hunassigned : A q = none) (hne : b ≠ a) :
    I.spend (assignQuery A q a) b = I.spend A b := by
  classical
  unfold spend assignQuery
  apply Finset.sum_congr rfl
  intro q' _hq'
  by_cases hq : q' = q
  · subst q'
    simp [hunassigned, hne.symm]
  · simp [hq]

theorem feasible_assignQuery_of_canAssign
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (q : Query) (a : Advertiser)
    (hfeasible : I.Feasible A)
    (hunassigned : A q = none)
    (hcan : I.CanAssign A q a) :
    I.Feasible (assignQuery A q a) := by
  intro b
  by_cases hb : b = a
  · subst b
    rw [spend_assignQuery_self_of_unassigned I A q a hunassigned]
    exact hcan
  · rw [spend_assignQuery_other_of_unassigned I A q hunassigned hb]
    exact hfeasible b

theorem initialHistoryState_invariant
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets) :
    I.StateInvariant (initialHistoryState : HistoryState Advertiser Query) := by
  constructor
  · exact emptyAssignment_feasible I hbudget
  · intro q _hq
    rfl

theorem residualBudget_nonneg_of_feasible
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (a : Advertiser)
    (hfeasible : I.Feasible A) :
    0 ≤ I.residualBudget A a := by
  unfold residualBudget
  exact sub_nonneg.mpr (hfeasible a)

theorem canAssign_iff_bid_le_residualBudget
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (q : Query) (a : Advertiser) :
    I.CanAssign A q a ↔ I.bid a q ≤ I.residualBudget A a := by
  unfold CanAssign residualBudget
  constructor <;> intro h <;> linarith

theorem spend_nonneg [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query) (hbid : I.NonnegativeBids)
    (A : Assignment Advertiser Query) (a : Advertiser) :
    0 ≤ I.spend A a := by
  classical
  unfold spend
  exact Finset.sum_nonneg fun q _ => by
    cases hassign : A q with
    | none =>
        simp
    | some a' =>
        by_cases ha : a' = a
        · simpa [hassign, ha] using hbid a q
        · simp [ha]

theorem revenue_nonneg [Fintype Query]
    (I : AdWordsInstance Advertiser Query) (hbid : I.NonnegativeBids)
    (A : Assignment Advertiser Query) :
    0 ≤ I.revenue A := by
  classical
  unfold revenue
  exact Finset.sum_nonneg fun q _ => by
    cases hassign : A q with
    | none =>
        simp
    | some a =>
        simpa [hassign] using hbid a q

theorem revenue_eq_sum_spend
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) :
    I.revenue A = ∑ a : Advertiser, I.spend A a := by
  classical
  unfold revenue spend
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _hq
  cases hassign : A q with
  | none =>
      simp
  | some owner =>
      simp

theorem revenue_le_totalBudget_of_feasible
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query)
    (hfeasible : I.Feasible A) :
    I.revenue A ≤ ∑ a : Advertiser, I.budget a := by
  calc
    I.revenue A = ∑ a : Advertiser, I.spend A a :=
      revenue_eq_sum_spend I A
    _ ≤ ∑ a : Advertiser, I.budget a :=
      Finset.sum_le_sum fun a _ => hfeasible a

theorem assignmentFraction_nonneg
    [DecidableEq Advertiser]
    (A : Assignment Advertiser Query) :
    ∀ a q, 0 ≤ assignmentFraction A a q := by
  intro a q
  unfold assignmentFraction
  cases A q with
  | none =>
      simp
  | some owner =>
      by_cases h : owner = a <;> simp [h]

theorem assignmentFraction_query_sum_le_one
    [Fintype Advertiser] [DecidableEq Advertiser]
    (A : Assignment Advertiser Query) (q : Query) :
    (∑ a : Advertiser, assignmentFraction A a q) ≤ 1 := by
  classical
  unfold assignmentFraction
  cases A q with
  | none =>
      simp
  | some owner =>
      simp

theorem assignmentFraction_budget_sum_eq_spend
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (a : Advertiser) :
    (∑ q : Query, I.bid a q * assignmentFraction A a q) =
      I.spend A a := by
  classical
  unfold assignmentFraction spend
  apply Finset.sum_congr rfl
  intro q _hq
  cases hassign : A q with
  | none =>
      simp
  | some owner =>
      by_cases h : owner = a
      · subst owner
        simp
      · simp [h]

theorem assignmentFraction_fractionalFeasible_of_feasible
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query)
    (hfeasible : I.Feasible A) :
    I.FractionalFeasible (assignmentFraction A) where
  nonneg := assignmentFraction_nonneg A
  query := assignmentFraction_query_sum_le_one A
  budget := by
    intro a
    rw [assignmentFraction_budget_sum_eq_spend I A a]
    exact hfeasible a

theorem fractionalRevenue_assignmentFraction_eq_revenue
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) :
    I.fractionalRevenue (assignmentFraction A) = I.revenue A := by
  classical
  unfold fractionalRevenue revenue assignmentFraction
  apply Finset.sum_congr rfl
  intro q _hq
  cases A q with
  | none =>
      simp
  | some owner =>
      simp

theorem fractional_dual_expansion
    [Fintype Advertiser] [Fintype Query]
    (I : AdWordsInstance Advertiser Query)
    (X : FractionalAssignment Advertiser Query)
    (alpha : Advertiser → ℝ) (beta : Query → ℝ) :
    (∑ q : Query, ∑ a : Advertiser,
        (I.bid a q * alpha a + beta q) * X a q) =
      (∑ a : Advertiser, (∑ q : Query, I.bid a q * X a q) * alpha a) +
        ∑ q : Query, beta q * ∑ a : Advertiser, X a q := by
  classical
  calc
    (∑ q : Query, ∑ a : Advertiser,
        (I.bid a q * alpha a + beta q) * X a q) =
        ∑ q : Query, ∑ a : Advertiser,
          ((I.bid a q * X a q) * alpha a + beta q * X a q) := by
      apply Finset.sum_congr rfl
      intro q _hq
      apply Finset.sum_congr rfl
      intro a _ha
      ring
    _ =
        (∑ q : Query, ∑ a : Advertiser,
          (I.bid a q * X a q) * alpha a) +
          ∑ q : Query, ∑ a : Advertiser, beta q * X a q := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro q _hq
      rw [← Finset.sum_add_distrib]
    _ =
        (∑ a : Advertiser, ∑ q : Query,
          (I.bid a q * X a q) * alpha a) +
          ∑ q : Query, ∑ a : Advertiser, beta q * X a q := by
      rw [Finset.sum_comm]
    _ =
        (∑ a : Advertiser, (∑ q : Query, I.bid a q * X a q) * alpha a) +
          ∑ q : Query, beta q * ∑ a : Advertiser, X a q := by
      congr 1
      · apply Finset.sum_congr rfl
        intro a _ha
        rw [Finset.sum_mul]
      · apply Finset.sum_congr rfl
        intro q _hq
        rw [Finset.mul_sum]

theorem fractionalRevenue_le_dualObjective_of_dualFeasible
    [Fintype Advertiser] [Fintype Query]
    (I : AdWordsInstance Advertiser Query)
    (X : FractionalAssignment Advertiser Query)
    (alpha : Advertiser → ℝ) (beta : Query → ℝ)
    (hfeasible : I.FractionalFeasible X)
    (hdual : I.DualFeasible alpha beta) :
    I.fractionalRevenue X ≤ I.dualObjective alpha beta := by
  have hpoint :
      I.fractionalRevenue X ≤
        ∑ q : Query, ∑ a : Advertiser,
          (I.bid a q * alpha a + beta q) * X a q := by
    unfold fractionalRevenue
    exact Finset.sum_le_sum fun q _ =>
      Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_right (hdual.covers a q)
          (hfeasible.nonneg a q)
  have hbudget :
      (∑ a : Advertiser, (∑ q : Query, I.bid a q * X a q) * alpha a) ≤
        ∑ a : Advertiser, I.budget a * alpha a := by
    exact Finset.sum_le_sum fun a _ =>
      mul_le_mul_of_nonneg_right (hfeasible.budget a)
        (hdual.alpha_nonneg a)
  have hquery :
      (∑ q : Query, beta q * ∑ a : Advertiser, X a q) ≤
        ∑ q : Query, beta q := by
    exact Finset.sum_le_sum fun q _ => by
      have hmul :=
        mul_le_mul_of_nonneg_left (hfeasible.query q)
          (hdual.beta_nonneg q)
      simpa using hmul
  rw [fractional_dual_expansion I X alpha beta] at hpoint
  unfold dualObjective
  linarith

theorem assignedWeightedSpend_eq_sum_spend_mul
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (alpha : Advertiser → ℝ) :
    I.assignedWeightedSpend A alpha =
      ∑ a : Advertiser, I.spend A a * alpha a := by
  classical
  calc
    I.assignedWeightedSpend A alpha =
        ∑ q : Query, ∑ a : Advertiser,
          match A q with
          | none => 0
          | some owner => if owner = a then I.bid a q * alpha a else 0 := by
      unfold assignedWeightedSpend
      apply Finset.sum_congr rfl
      intro q _hq
      cases A q <;> simp
    _ = ∑ a : Advertiser, ∑ q : Query,
          match A q with
          | none => 0
          | some owner => if owner = a then I.bid a q * alpha a else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ a : Advertiser, I.spend A a * alpha a := by
      apply Finset.sum_congr rfl
      intro a _ha
      unfold spend
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q _hq
      cases A q with
      | none =>
          simp
      | some owner =>
          by_cases h : owner = a <;> simp [h]

theorem assignedWeightedSpend_le_budget_weighted_of_feasible
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (alpha : Advertiser → ℝ)
    (hfeasible : I.Feasible A)
    (halpha : ∀ a, 0 ≤ alpha a) :
    I.assignedWeightedSpend A alpha ≤
      ∑ a : Advertiser, I.budget a * alpha a := by
  rw [assignedWeightedSpend_eq_sum_spend_mul]
  exact Finset.sum_le_sum fun a _ =>
    mul_le_mul_of_nonneg_right (hfeasible a) (halpha a)

theorem revenue_le_assignedWeightedSpend_add_beta_of_dualFeasible
    [Fintype Query]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query)
    (alpha : Advertiser → ℝ) (beta : Query → ℝ)
    (hdual : I.DualFeasible alpha beta) :
    I.revenue A ≤ I.assignedWeightedSpend A alpha + ∑ q : Query, beta q := by
  classical
  unfold revenue assignedWeightedSpend
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun q _ => by
    cases A q with
    | none =>
        simpa using hdual.beta_nonneg q
    | some a =>
        exact hdual.covers a q

theorem revenue_le_dualObjective_of_dualFeasible
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query)
    (alpha : Advertiser → ℝ) (beta : Query → ℝ)
    (hfeasible : I.Feasible A)
    (hdual : I.DualFeasible alpha beta) :
    I.revenue A ≤ I.dualObjective alpha beta := by
  have hrev :=
    revenue_le_assignedWeightedSpend_add_beta_of_dualFeasible
      I A alpha beta hdual
  have hspend :=
    assignedWeightedSpend_le_budget_weighted_of_feasible
      I A alpha hfeasible hdual.alpha_nonneg
  unfold dualObjective
  linarith

theorem mem_feasibleAssignments
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) :
    A ∈ I.feasibleAssignments ↔ I.Feasible A := by
  classical
  simp [feasibleAssignments]

theorem feasibleAssignments_nonempty
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets) :
    I.feasibleAssignments.Nonempty := by
  classical
  refine ⟨emptyAssignment, ?_⟩
  exact (mem_feasibleAssignments I
    (emptyAssignment : Assignment Advertiser Query)).2
    (emptyAssignment_feasible I hbudget)

set_option linter.unusedFintypeInType false in
theorem exists_optimalAssignment
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets) :
    ∃ A : Assignment Advertiser Query, I.IsOptimalAssignment A := by
  classical
  obtain ⟨A, hA, hmax⟩ :=
    Finset.exists_max_image I.feasibleAssignments (fun A => I.revenue A)
      (feasibleAssignments_nonempty I hbudget)
  refine ⟨A, ?_, ?_⟩
  · exact (mem_feasibleAssignments I A).1 hA
  · intro B hB
    exact hmax B ((mem_feasibleAssignments I B).2 hB)

/-- A chosen offline optimum assignment. -/
noncomputable def offlineOptimumAssignment
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets) : Assignment Advertiser Query :=
  Classical.choose (exists_optimalAssignment I hbudget)

/-- The offline optimum value used as the benchmark in competitive analysis. -/
noncomputable def offlineOptimumValue
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets) : ℝ :=
  I.revenue (I.offlineOptimumAssignment hbudget)

theorem offlineOptimumAssignment_isOptimal
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets) :
    I.IsOptimalAssignment (I.offlineOptimumAssignment hbudget) := by
  exact Classical.choose_spec (exists_optimalAssignment I hbudget)

theorem revenue_le_offlineOptimumValue
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets)
    (A : Assignment Advertiser Query)
    (hfeasible : I.Feasible A) :
    I.revenue A ≤ I.offlineOptimumValue hbudget := by
  exact (offlineOptimumAssignment_isOptimal I hbudget).2 A hfeasible

theorem offlineOptimumValue_le_totalBudget
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets) :
    I.offlineOptimumValue hbudget ≤ ∑ a : Advertiser, I.budget a := by
  exact revenue_le_totalBudget_of_feasible I
    (I.offlineOptimumAssignment hbudget)
    (offlineOptimumAssignment_isOptimal I hbudget).1

theorem offlineOptimumValue_le_dualObjective_of_dualFeasible
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets)
    (alpha : Advertiser → ℝ) (beta : Query → ℝ)
    (hdual : I.DualFeasible alpha beta) :
    I.offlineOptimumValue hbudget ≤ I.dualObjective alpha beta := by
  exact revenue_le_dualObjective_of_dualFeasible I
    (I.offlineOptimumAssignment hbudget) alpha beta
    (offlineOptimumAssignment_isOptimal I hbudget).1 hdual

theorem spentFraction_nonneg
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (A : Assignment Advertiser Query) (a : Advertiser)
    (hbudget : 0 < I.budget a) :
    0 ≤ I.spentFraction A a := by
  unfold spentFraction
  exact div_nonneg (spend_nonneg I hbid A a) hbudget.le

theorem spentFraction_le_one_of_feasible
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (a : Advertiser)
    (hbudget : 0 < I.budget a)
    (hfeasible : I.Feasible A) :
    I.spentFraction A a ≤ 1 := by
  unfold spentFraction
  calc
    I.spend A a / I.budget a ≤ I.budget a / I.budget a :=
      div_le_div_of_nonneg_right (hfeasible a) hbudget.le
    _ = 1 := by
      exact div_self hbudget.ne'

theorem spentFraction_gt_one_sub_epsilon_of_not_canAssign
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (a : Advertiser) (q : Query)
    {ε : ℝ}
    (hbudget : 0 < I.budget a)
    (hsmall : I.SmallBids ε)
    (hnot : ¬ I.CanAssign A q a) :
    1 - ε < I.spentFraction A a := by
  unfold CanAssign at hnot
  have hlt : I.budget a < I.spend A a + I.bid a q :=
    lt_of_not_ge hnot
  have hbidle : I.bid a q ≤ ε * I.budget a := hsmall a q
  have hlt' : I.budget a < I.spend A a + ε * I.budget a :=
    lt_of_lt_of_le hlt (add_le_add_right hbidle (I.spend A a))
  have hmul : (1 - ε) * I.budget a < I.spend A a := by
    nlinarith
  have hdiv :=
    div_lt_div_of_pos_right hmul hbudget
  have hleft :
      ((1 - ε) * I.budget a) / I.budget a = 1 - ε := by
    exact mul_div_cancel_right₀ _ hbudget.ne'
  simpa [spentFraction, hleft] using hdiv

theorem spentFraction_assignQuery_self_of_unassigned
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (q : Query) (a : Advertiser)
    (hunassigned : A q = none)
    (hbudget : I.budget a ≠ 0) :
    I.spentFraction (assignQuery A q a) a =
      I.spentFraction A a + I.bid a q / I.budget a := by
  unfold spentFraction
  rw [spend_assignQuery_self_of_unassigned I A q a hunassigned]
  field_simp [hbudget]

theorem spentFraction_assignQuery_other_of_unassigned
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (q : Query) {owner a : Advertiser}
    (hunassigned : A q = none) (hne : a ≠ owner) :
    I.spentFraction (assignQuery A q owner) a =
      I.spentFraction A a := by
  unfold spentFraction
  rw [spend_assignQuery_other_of_unassigned I A q
    (a := owner) (b := a) hunassigned hne]

theorem balanceDiscount_nonneg_of_le_one {x : ℝ} (hx : x ≤ 1) :
    0 ≤ balanceDiscount x := by
  unfold balanceDiscount
  have hexp : Real.exp (x - 1) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  linarith

theorem balanceDiscount_le_one (x : ℝ) :
    balanceDiscount x ≤ 1 := by
  unfold balanceDiscount
  have hexp : 0 ≤ Real.exp (x - 1) := Real.exp_nonneg (x - 1)
  linarith

theorem balanceDiscount_mem_unit_interval_of_le_one {x : ℝ} (hx : x ≤ 1) :
    0 ≤ balanceDiscount x ∧ balanceDiscount x ≤ 1 :=
  ⟨balanceDiscount_nonneg_of_le_one hx, balanceDiscount_le_one x⟩

theorem msvvDualAlpha_pos (x : ℝ) :
    0 < msvvDualAlpha x := by
  unfold msvvDualAlpha
  exact Real.exp_pos (x - 1)

theorem msvvDualAlpha_nonneg (x : ℝ) :
    0 ≤ msvvDualAlpha x :=
  (msvvDualAlpha_pos x).le

theorem msvvDualAlpha_mono {x y : ℝ} (hxy : x ≤ y) :
    msvvDualAlpha x ≤ msvvDualAlpha y := by
  unfold msvvDualAlpha
  exact Real.exp_le_exp.mpr (by linarith)

theorem exp_one_sub_one_pos : 0 < Real.exp 1 - 1 := by
  have hgt : 1 < Real.exp 1 :=
    Real.one_lt_exp_iff.mpr zero_lt_one
  linarith

theorem msvvNormalizedDualAlpha_nonneg_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ msvvNormalizedDualAlpha x := by
  unfold msvvNormalizedDualAlpha
  have hnum : 0 ≤ Real.exp x - 1 := by
    rw [sub_nonneg]
    simpa using (Real.exp_le_exp.mpr hx : Real.exp 0 ≤ Real.exp x)
  exact div_nonneg hnum exp_one_sub_one_pos.le

theorem msvvNormalizedDualAlpha_mono {x y : ℝ} (hxy : x ≤ y) :
    msvvNormalizedDualAlpha x ≤ msvvNormalizedDualAlpha y := by
  unfold msvvNormalizedDualAlpha
  exact div_le_div_of_nonneg_right
    (sub_le_sub_right (Real.exp_le_exp.mpr hxy) 1)
    exp_one_sub_one_pos.le

theorem one_sub_exp_neg_nonneg {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ 1 - Real.exp (-ε) := by
  have hexp : Real.exp (-ε) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  linarith

theorem balanceDiscount_eq_one_sub_msvvDualAlpha (x : ℝ) :
    balanceDiscount x = 1 - msvvDualAlpha x := by
  rfl

theorem msvvRatio_pos : 0 < msvvRatio := by
  unfold msvvRatio
  have hexp_pos : 0 < Real.exp 1 := Real.exp_pos 1
  have hfrac_lt : 1 / Real.exp 1 < 1 := by
    exact (div_lt_one hexp_pos).2
      (Real.one_lt_exp_iff.mpr zero_lt_one)
  linarith

theorem msvvRatio_nonneg : 0 ≤ msvvRatio :=
  le_of_lt msvvRatio_pos

theorem msvvRatio_lt_one : msvvRatio < 1 := by
  unfold msvvRatio
  have hfrac_pos : 0 < 1 / Real.exp 1 := by
    positivity
  linarith

theorem balanceScore_nonneg_of_feasible
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (A : Assignment Advertiser Query) (a : Advertiser) (q : Query)
    (hbudget : 0 < I.budget a)
    (hfeasible : I.Feasible A) :
    0 ≤ I.balanceScore A a q := by
  unfold balanceScore
  exact mul_nonneg (hbid a q)
    (balanceDiscount_nonneg_of_le_one
      (spentFraction_le_one_of_feasible I A a hbudget hfeasible))

theorem balanceScore_eq_slackScore_msvvDualAlpha
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (a : Advertiser) (q : Query) :
    I.balanceScore A a q =
      I.slackScore (fun b => msvvDualAlpha (I.spentFraction A b)) a q := by
  simp [balanceScore, balanceDiscount, slackScore, msvvDualAlpha]

theorem msvvAlphaFromAssignment_nonneg
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) :
    ∀ a, 0 ≤ I.msvvAlphaFromAssignment A a := by
  intro a
  exact msvvDualAlpha_nonneg (I.spentFraction A a)

theorem msvvNormalizedAlphaFromAssignment_nonneg
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (A : Assignment Advertiser Query) :
    ∀ a, 0 ≤ I.msvvNormalizedAlphaFromAssignment A a := by
  intro a
  exact msvvNormalizedDualAlpha_nonneg_of_nonneg
    (spentFraction_nonneg I hbid A a (hbudget a))

theorem msvvNormalizedAlphaBudgetMass_emptyAssignment
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query) :
    I.msvvNormalizedAlphaBudgetMass
        (emptyAssignment : Assignment Advertiser Query) = 0 := by
  classical
  unfold msvvNormalizedAlphaBudgetMass msvvNormalizedAlphaFromAssignment
    msvvNormalizedDualAlpha spentFraction
  simp [spend_emptyAssignment]

theorem msvvNormalizedAlphaBudgetMass_assignQuery_of_unassigned
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (q : Query) (owner : Advertiser)
    (hunassigned : A q = none) :
    I.msvvNormalizedAlphaBudgetMass (assignQuery A q owner) =
      I.msvvNormalizedAlphaBudgetMass A +
        I.budget owner *
          (I.msvvNormalizedAlphaFromAssignment (assignQuery A q owner) owner -
            I.msvvNormalizedAlphaFromAssignment A owner) := by
  classical
  have hdiff :
      I.msvvNormalizedAlphaBudgetMass (assignQuery A q owner) -
          I.msvvNormalizedAlphaBudgetMass A =
        ∑ a : Advertiser,
          (I.budget a *
              I.msvvNormalizedAlphaFromAssignment (assignQuery A q owner) a -
            I.budget a * I.msvvNormalizedAlphaFromAssignment A a) := by
    unfold msvvNormalizedAlphaBudgetMass
    rw [Finset.sum_sub_distrib]
  have hsingle_raw :
      (∑ a : Advertiser,
          (I.budget a *
              I.msvvNormalizedAlphaFromAssignment (assignQuery A q owner) a -
            I.budget a * I.msvvNormalizedAlphaFromAssignment A a)) =
        I.budget owner *
            I.msvvNormalizedAlphaFromAssignment (assignQuery A q owner) owner -
          I.budget owner * I.msvvNormalizedAlphaFromAssignment A owner := by
    apply Finset.sum_eq_single (s := Finset.univ) owner
    · intro a _ha hne
      have hfrac :
          I.spentFraction (assignQuery A q owner) a =
            I.spentFraction A a :=
        spentFraction_assignQuery_other_of_unassigned
          I A q hunassigned hne
      simp [msvvNormalizedAlphaFromAssignment, hfrac]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ owner))
  have hsingle :
      (∑ a : Advertiser,
          (I.budget a *
              I.msvvNormalizedAlphaFromAssignment (assignQuery A q owner) a -
            I.budget a * I.msvvNormalizedAlphaFromAssignment A a)) =
        I.budget owner *
          (I.msvvNormalizedAlphaFromAssignment (assignQuery A q owner) owner -
            I.msvvNormalizedAlphaFromAssignment A owner) := by
    rw [hsingle_raw]
    ring
  linarith

theorem balanceScore_eq_slackScore_msvvAlphaFromAssignment
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (a : Advertiser) (q : Query) :
    I.balanceScore A a q =
      I.slackScore (I.msvvAlphaFromAssignment A) a q := by
  simp [balanceScore, balanceDiscount, slackScore,
    msvvAlphaFromAssignment, msvvDualAlpha]

theorem msvvRatio_mul_slackScore_msvvNormalizedAlphaFromAssignment_eq_balanceScore
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (a : Advertiser) (q : Query) :
    msvvRatio *
        I.slackScore (I.msvvNormalizedAlphaFromAssignment A) a q =
      I.balanceScore A a q := by
  unfold msvvRatio slackScore balanceScore balanceDiscount
    msvvNormalizedAlphaFromAssignment msvvNormalizedDualAlpha
  have hE : Real.exp 1 ≠ 0 := ne_of_gt (Real.exp_pos 1)
  have hden : Real.exp 1 - 1 ≠ 0 := ne_of_gt exp_one_sub_one_pos
  rw [show Real.exp (I.spentFraction A a - 1) =
      Real.exp (I.spentFraction A a) / Real.exp 1 by
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_neg]
    ring]
  field_simp [hE, hden]
  ring

theorem msvvRatio_mul_one_sub_msvvNormalizedDualAlpha_one_sub (ε : ℝ) :
    msvvRatio * (1 - msvvNormalizedDualAlpha (1 - ε)) =
      1 - Real.exp (-ε) := by
  unfold msvvRatio msvvNormalizedDualAlpha
  have hE : Real.exp 1 ≠ 0 := ne_of_gt (Real.exp_pos 1)
  have hden : Real.exp 1 - 1 ≠ 0 := ne_of_gt exp_one_sub_one_pos
  rw [show Real.exp (1 - ε) = Real.exp 1 * Real.exp (-ε) by
    rw [sub_eq_add_neg, Real.exp_add]]
  field_simp [hE, hden]
  ring

theorem exp_sub_one_nonneg_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ Real.exp x - 1 := by
  rw [sub_nonneg]
  simpa using (Real.exp_le_exp.mpr hx : Real.exp 0 ≤ Real.exp x)

theorem exp_sub_one_le_mul_self_exp (x : ℝ) :
    Real.exp x - 1 ≤ x * Real.exp x := by
  have h :=
    mul_le_mul_of_nonneg_right (Real.one_sub_le_exp_neg x)
      (Real.exp_nonneg x)
  have hright : Real.exp (-x) * Real.exp x = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  rw [hright] at h
  nlinarith

theorem exp_sub_one_le_mul_exp_of_mem_interval {x ε : ℝ}
    (hx : 0 ≤ x) (hxε : x ≤ ε) :
    Real.exp x - 1 ≤ x * Real.exp ε := by
  have hbase := exp_sub_one_le_mul_self_exp x
  have hexp : Real.exp x ≤ Real.exp ε := Real.exp_le_exp.mpr hxε
  have hmul : x * Real.exp x ≤ x * Real.exp ε :=
    mul_le_mul_of_nonneg_left hexp hx
  exact hbase.trans hmul

theorem one_sub_exp_neg_le_self (x : ℝ) :
    1 - Real.exp (-x) ≤ x := by
  have h := Real.one_sub_le_exp_neg x
  linarith

theorem msvvSmallBidsErrorFactor_nonneg {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ (Real.exp ε - 1) + (1 - Real.exp (-ε)) := by
  exact add_nonneg (exp_sub_one_nonneg_of_nonneg hε)
    (one_sub_exp_neg_nonneg hε)

theorem msvvSmallBidsErrorFactor_le_epsilon_mul_exp_one_add_one
    {ε : ℝ} (hε : 0 ≤ ε) (hε_le_one : ε ≤ 1) :
    (Real.exp ε - 1) + (1 - Real.exp (-ε)) ≤
      ε * (Real.exp 1 + 1) := by
  have halpha :
      Real.exp ε - 1 ≤ ε * Real.exp 1 :=
    exp_sub_one_le_mul_exp_of_mem_interval hε hε_le_one
  have hbeta :
      1 - Real.exp (-ε) ≤ ε :=
    one_sub_exp_neg_le_self ε
  calc
    (Real.exp ε - 1) + (1 - Real.exp (-ε)) ≤
        ε * Real.exp 1 + ε :=
          add_le_add halpha hbeta
    _ = ε * (Real.exp 1 + 1) := by
        ring

theorem msvvRatio_mul_budget_normalizedDualAlpha_increment_eq
    (B s δ : ℝ) :
    msvvRatio *
        (B * (msvvNormalizedDualAlpha (s + δ) -
          msvvNormalizedDualAlpha s)) =
      B * Real.exp (s - 1) * (Real.exp δ - 1) := by
  unfold msvvRatio msvvNormalizedDualAlpha
  have hE : Real.exp 1 ≠ 0 := ne_of_gt (Real.exp_pos 1)
  have hden : Real.exp 1 - 1 ≠ 0 := ne_of_gt exp_one_sub_one_pos
  rw [show Real.exp (s + δ) = Real.exp s * Real.exp δ by
    rw [Real.exp_add]]
  rw [show Real.exp (s - 1) = Real.exp s / Real.exp 1 by
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_neg]
    ring]
  field_simp [hE, hden]
  ring

theorem msvvRatio_mul_normalizedAlphaBudgetMass_increment_assignQuery_eq
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (q : Query) (owner : Advertiser)
    (hunassigned : A q = none)
    (hbudget : I.budget owner ≠ 0) :
    msvvRatio *
        (I.msvvNormalizedAlphaBudgetMass (assignQuery A q owner) -
          I.msvvNormalizedAlphaBudgetMass A) =
      I.budget owner * Real.exp (I.spentFraction A owner - 1) *
        (Real.exp (I.bid owner q / I.budget owner) - 1) := by
  have hmass :=
    msvvNormalizedAlphaBudgetMass_assignQuery_of_unassigned
      I A q owner hunassigned
  have hdiff :
      I.msvvNormalizedAlphaBudgetMass (assignQuery A q owner) -
          I.msvvNormalizedAlphaBudgetMass A =
        I.budget owner *
          (I.msvvNormalizedAlphaFromAssignment (assignQuery A q owner) owner -
            I.msvvNormalizedAlphaFromAssignment A owner) := by
    linarith
  rw [hdiff]
  simp only [msvvNormalizedAlphaFromAssignment]
  rw [spentFraction_assignQuery_self_of_unassigned
    I A q owner hunassigned hbudget]
  exact msvvRatio_mul_budget_normalizedDualAlpha_increment_eq
    (I.budget owner) (I.spentFraction A owner)
    (I.bid owner q / I.budget owner)

theorem msvvRatio_mul_normalizedAlphaBudgetMass_increment_assignQuery_add_balanceScore_le_bid_add_alphaError
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (A : Assignment Advertiser Query) (q : Query) (owner : Advertiser)
    (hunassigned : A q = none)
    (hfeasible : I.Feasible A)
    {ε : ℝ}
    (hε : 0 ≤ ε)
    (hsmall : I.SmallBids ε) :
    msvvRatio *
        (I.msvvNormalizedAlphaBudgetMass (assignQuery A q owner) -
          I.msvvNormalizedAlphaBudgetMass A) +
        I.balanceScore A owner q ≤
      I.bid owner q + I.bid owner q * (Real.exp ε - 1) := by
  let s := I.spentFraction A owner
  let δ := I.bid owner q / I.budget owner
  have hBpos : 0 < I.budget owner := hbudget owner
  have hδ_nonneg : 0 ≤ δ := by
    exact div_nonneg (hbid owner q) hBpos.le
  have hδ_le : δ ≤ ε := by
    exact (div_le_iff₀ hBpos).2 (hsmall owner q)
  have hinc_eq :=
    msvvRatio_mul_normalizedAlphaBudgetMass_increment_assignQuery_eq
      I A q owner hunassigned hBpos.ne'
  have hfactor :
      Real.exp δ - 1 ≤ δ * Real.exp ε :=
    exp_sub_one_le_mul_exp_of_mem_interval hδ_nonneg hδ_le
  have hleft_nonneg :
      0 ≤ I.budget owner * Real.exp (s - 1) :=
    mul_nonneg hBpos.le (Real.exp_nonneg (s - 1))
  have hinc_le :
      msvvRatio *
          (I.msvvNormalizedAlphaBudgetMass (assignQuery A q owner) -
            I.msvvNormalizedAlphaBudgetMass A) ≤
        I.bid owner q * Real.exp (s - 1) * Real.exp ε := by
    have hBδ : I.budget owner * δ = I.bid owner q := by
      change I.budget owner * (I.bid owner q / I.budget owner) =
        I.bid owner q
      calc
        I.budget owner * (I.bid owner q / I.budget owner) =
            I.bid owner q * I.budget owner / I.budget owner := by
            ring
        _ = I.bid owner q := by
            exact mul_div_cancel_right₀ (I.bid owner q) hBpos.ne'
    calc
      msvvRatio *
          (I.msvvNormalizedAlphaBudgetMass (assignQuery A q owner) -
            I.msvvNormalizedAlphaBudgetMass A) =
          I.budget owner * Real.exp (s - 1) *
            (Real.exp δ - 1) := by
            simpa [s, δ] using hinc_eq
      _ ≤ I.budget owner * Real.exp (s - 1) *
            (δ * Real.exp ε) :=
          mul_le_mul_of_nonneg_left hfactor hleft_nonneg
      _ = I.bid owner q * Real.exp (s - 1) * Real.exp ε := by
          rw [show I.budget owner * Real.exp (s - 1) *
                (δ * Real.exp ε) =
              (I.budget owner * δ) * Real.exp (s - 1) * Real.exp ε by ring]
          rw [hBδ]
  have hbalance :
      I.balanceScore A owner q =
        I.bid owner q * (1 - Real.exp (s - 1)) := by
    simp [balanceScore, balanceDiscount, s]
  have hs_le_one : s ≤ 1 := by
    exact spentFraction_le_one_of_feasible I A owner hBpos hfeasible
  have hexp_s_le_one : Real.exp (s - 1) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have herr_nonneg : 0 ≤ Real.exp ε - 1 :=
    exp_sub_one_nonneg_of_nonneg hε
  have htail :
      I.bid owner q * Real.exp (s - 1) * (Real.exp ε - 1) ≤
        I.bid owner q * (Real.exp ε - 1) := by
    have hcoeff_nonneg :
        0 ≤ I.bid owner q * (Real.exp ε - 1) :=
      mul_nonneg (hbid owner q) herr_nonneg
    calc
      I.bid owner q * Real.exp (s - 1) * (Real.exp ε - 1) =
          (I.bid owner q * (Real.exp ε - 1)) *
            Real.exp (s - 1) := by
            ring
      _ ≤ (I.bid owner q * (Real.exp ε - 1)) * 1 :=
          mul_le_mul_of_nonneg_left hexp_s_le_one hcoeff_nonneg
      _ = I.bid owner q * (Real.exp ε - 1) := by
          ring
  calc
    msvvRatio *
        (I.msvvNormalizedAlphaBudgetMass (assignQuery A q owner) -
          I.msvvNormalizedAlphaBudgetMass A) +
        I.balanceScore A owner q
        ≤
      I.bid owner q * Real.exp (s - 1) * Real.exp ε +
        I.bid owner q * (1 - Real.exp (s - 1)) :=
          add_le_add hinc_le (le_of_eq hbalance)
    _ = I.bid owner q +
        I.bid owner q * Real.exp (s - 1) * (Real.exp ε - 1) := by
          ring
    _ ≤ I.bid owner q + I.bid owner q * (Real.exp ε - 1) := by
          linarith

theorem slackScore_anti_mono_alpha
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (alpha alpha' : Advertiser → ℝ) (a : Advertiser) (q : Query)
    (halpha : alpha a ≤ alpha' a) :
    I.slackScore alpha' a q ≤ I.slackScore alpha a q := by
  unfold slackScore
  have hfactor : 1 - alpha' a ≤ 1 - alpha a := by
    linarith
  exact mul_le_mul_of_nonneg_left hfactor (hbid a q)

theorem dualFeasible_of_slackScore_le_beta
    (I : AdWordsInstance Advertiser Query)
    (alpha : Advertiser → ℝ) (beta : Query → ℝ)
    (halpha : ∀ a, 0 ≤ alpha a)
    (hbeta : ∀ q, 0 ≤ beta q)
    (hcover : ∀ a q, I.slackScore alpha a q ≤ beta q) :
    I.DualFeasible alpha beta := by
  refine ⟨halpha, hbeta, ?_⟩
  intro a q
  have h := hcover a q
  unfold slackScore at h
  nlinarith

theorem slackScore_le_maxSlackBeta
    [Fintype Advertiser] [Nonempty Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (alpha : Advertiser → ℝ) (a : Advertiser) (q : Query) :
    I.slackScore alpha a q ≤ I.maxSlackBeta alpha q := by
  classical
  unfold maxSlackBeta
  let scores : Finset ℝ :=
    Finset.univ.image fun a : Advertiser => I.slackScore alpha a q
  have hmem : I.slackScore alpha a q ∈ scores := by
    simp [scores]
  have hle_max : I.slackScore alpha a q ≤
      scores.max' ⟨I.slackScore alpha a q, hmem⟩ :=
    scores.le_max' (I.slackScore alpha a q) hmem
  exact hle_max.trans (le_max_right 0 _)

theorem maxSlackBeta_nonneg
    [Fintype Advertiser] [Nonempty Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (alpha : Advertiser → ℝ) (q : Query) :
    0 ≤ I.maxSlackBeta alpha q := by
  classical
  unfold maxSlackBeta
  let scores : Finset ℝ :=
    Finset.univ.image fun a : Advertiser => I.slackScore alpha a q
  exact le_max_left 0 (scores.max' _)

theorem maxBidForQuery_nonneg
    [Fintype Advertiser] [Nonempty Advertiser]
    (I : AdWordsInstance Advertiser Query) (q : Query) :
    0 ≤ I.maxBidForQuery q := by
  classical
  unfold maxBidForQuery
  let bids : Finset ℝ :=
    Finset.univ.image fun a : Advertiser => I.bid a q
  exact le_max_left 0 (bids.max' _)

theorem bid_le_maxBidForQuery
    [Fintype Advertiser] [Nonempty Advertiser]
    (I : AdWordsInstance Advertiser Query) (a : Advertiser) (q : Query) :
    I.bid a q ≤ I.maxBidForQuery q := by
  classical
  unfold maxBidForQuery
  let bids : Finset ℝ :=
    Finset.univ.image fun a : Advertiser => I.bid a q
  have hmem : I.bid a q ∈ bids := by
    simp [bids]
  have hle : I.bid a q ≤ bids.max' ⟨I.bid a q, hmem⟩ :=
    bids.le_max' (I.bid a q) hmem
  exact hle.trans (le_max_right 0 _)

theorem historyMaxBidSum_nonneg
    [Fintype Advertiser] [Nonempty Advertiser]
    (I : AdWordsInstance Advertiser Query) (history : List Query) :
    0 ≤ I.historyMaxBidSum history := by
  induction history with
  | nil =>
      simp [historyMaxBidSum]
  | cons q qs ih =>
      simp [historyMaxBidSum]
      exact add_nonneg (maxBidForQuery_nonneg I q) ih

theorem historyMsvvSmallBidsErrorSum_nonneg
    [Fintype Advertiser] [Nonempty Advertiser]
    (I : AdWordsInstance Advertiser Query) (history : List Query)
    {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ I.historyMsvvSmallBidsErrorSum ε history := by
  induction history with
  | nil =>
      simp [historyMsvvSmallBidsErrorSum, historyMaxBidAlphaErrorSum,
        historyMaxBidErrorSum]
  | cons q qs ih =>
      have hfactor :
          0 ≤ (Real.exp ε - 1) + (1 - Real.exp (-ε)) :=
        msvvSmallBidsErrorFactor_nonneg hε
      calc
        0 ≤
            I.maxBidForQuery q *
                ((Real.exp ε - 1) + (1 - Real.exp (-ε))) +
              I.historyMsvvSmallBidsErrorSum ε qs :=
              add_nonneg
                (mul_nonneg (maxBidForQuery_nonneg I q) hfactor) ih
        _ = I.historyMsvvSmallBidsErrorSum ε (q :: qs) := by
              simp [historyMsvvSmallBidsErrorSum, historyMaxBidAlphaErrorSum,
                historyMaxBidErrorSum]
              ring

theorem historyMsvvSmallBidsErrorSum_le_epsilon_mul_exp_one_add_one_mul_historyMaxBidSum
    [Fintype Advertiser] [Nonempty Advertiser]
    (I : AdWordsInstance Advertiser Query) (history : List Query)
    {ε : ℝ} (hε : 0 ≤ ε) (hε_le_one : ε ≤ 1) :
    I.historyMsvvSmallBidsErrorSum ε history ≤
      ε * (Real.exp 1 + 1) * I.historyMaxBidSum history := by
  induction history with
  | nil =>
      simp [historyMsvvSmallBidsErrorSum, historyMaxBidAlphaErrorSum,
        historyMaxBidErrorSum, historyMaxBidSum]
  | cons q qs ih =>
      have hfactor :
          (Real.exp ε - 1) + (1 - Real.exp (-ε)) ≤
            ε * (Real.exp 1 + 1) :=
        msvvSmallBidsErrorFactor_le_epsilon_mul_exp_one_add_one
          hε hε_le_one
      have hhead :
          I.maxBidForQuery q *
              ((Real.exp ε - 1) + (1 - Real.exp (-ε))) ≤
            ε * (Real.exp 1 + 1) * I.maxBidForQuery q := by
        calc
          I.maxBidForQuery q *
              ((Real.exp ε - 1) + (1 - Real.exp (-ε))) ≤
              I.maxBidForQuery q * (ε * (Real.exp 1 + 1)) :=
                mul_le_mul_of_nonneg_left hfactor
                  (maxBidForQuery_nonneg I q)
          _ = ε * (Real.exp 1 + 1) * I.maxBidForQuery q := by
              ring
      calc
        I.historyMsvvSmallBidsErrorSum ε (q :: qs) =
            I.maxBidForQuery q *
                ((Real.exp ε - 1) + (1 - Real.exp (-ε))) +
              I.historyMsvvSmallBidsErrorSum ε qs := by
              simp [historyMsvvSmallBidsErrorSum, historyMaxBidAlphaErrorSum,
                historyMaxBidErrorSum]
              ring
        _ ≤
            ε * (Real.exp 1 + 1) * I.maxBidForQuery q +
              ε * (Real.exp 1 + 1) * I.historyMaxBidSum qs :=
              add_le_add hhead ih
        _ =
            ε * (Real.exp 1 + 1) * I.historyMaxBidSum (q :: qs) := by
              simp [historyMaxBidSum]
              ring

theorem msvvRatio_mul_normalizedAlphaBudgetMass_step_increment_add_balanceCharge_le_stepRevenueCharge_add_alphaError
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (rule : ChoiceRule Advertiser Query)
    (S : HistoryState Advertiser Query) (q : Query)
    (hS : I.StateInvariant S)
    {ε : ℝ}
    (hε : 0 ≤ ε)
    (hsmall : I.SmallBids ε) :
    msvvRatio *
        (I.msvvNormalizedAlphaBudgetMass
            (stepHistoryState I rule S q).assignment -
          I.msvvNormalizedAlphaBudgetMass S.assignment) +
        (if q ∈ S.seen then
          0
        else
          match rule S.assignment q with
          | none => 0
          | some a => I.balanceScore S.assignment a q) ≤
      I.stepRevenueCharge rule S q +
        I.maxBidForQuery q * (Real.exp ε - 1) := by
  classical
  have herr_nonneg : 0 ≤ Real.exp ε - 1 :=
    exp_sub_one_nonneg_of_nonneg hε
  have hmaxerr_nonneg :
      0 ≤ I.maxBidForQuery q * (Real.exp ε - 1) :=
    mul_nonneg (maxBidForQuery_nonneg I q) herr_nonneg
  by_cases hseen : q ∈ S.seen
  · simpa [stepHistoryState, stepRevenueCharge, hseen] using hmaxerr_nonneg
  · cases hchoice : rule S.assignment q with
    | none =>
        simpa [stepHistoryState, stepRevenueCharge, hseen, hchoice]
          using hmaxerr_nonneg
    | some owner =>
        have hunassigned : S.assignment q = none := hS.2 q hseen
        have hlocal :=
          msvvRatio_mul_normalizedAlphaBudgetMass_increment_assignQuery_add_balanceScore_le_bid_add_alphaError
            I hbid hbudget S.assignment q owner hunassigned hS.1 hε hsmall
        have hbiderr_le :
            I.bid owner q * (Real.exp ε - 1) ≤
              I.maxBidForQuery q * (Real.exp ε - 1) :=
          mul_le_mul_of_nonneg_right
            (bid_le_maxBidForQuery I owner q) herr_nonneg
        have hlocal' :
            msvvRatio *
                (I.msvvNormalizedAlphaBudgetMass
                    (assignQuery S.assignment q owner) -
                  I.msvvNormalizedAlphaBudgetMass S.assignment) +
                I.balanceScore S.assignment owner q ≤
              I.bid owner q +
                I.maxBidForQuery q * (Real.exp ε - 1) := by
          linarith
        simpa [stepHistoryState, stepRevenueCharge, hseen, hchoice]
          using hlocal'

theorem maxSlackBeta_le_of_slackScore_le
    [Fintype Advertiser] [Nonempty Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (alpha : Advertiser → ℝ) (q : Query) {B : ℝ}
    (hB : 0 ≤ B)
    (hscore : ∀ a, I.slackScore alpha a q ≤ B) :
    I.maxSlackBeta alpha q ≤ B := by
  classical
  unfold maxSlackBeta
  let scores : Finset ℝ :=
    Finset.univ.image fun a : Advertiser => I.slackScore alpha a q
  have hscores : scores.Nonempty := by
    obtain ⟨a⟩ := (inferInstance : Nonempty Advertiser)
    exact ⟨I.slackScore alpha a q, by simp [scores]⟩
  apply max_le hB
  exact Finset.max'_le scores hscores B fun x hx => by
    rcases Finset.mem_image.mp hx with ⟨a, _ha, rfl⟩
    exact hscore a

theorem mul_maxSlackBeta_le_of_mul_slackScore_le
    [Fintype Advertiser] [Nonempty Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (alpha : Advertiser → ℝ) (q : Query) {r B : ℝ}
    (hr : 0 ≤ r)
    (hB : 0 ≤ B)
    (hscore : ∀ a, r * I.slackScore alpha a q ≤ B) :
    r * I.maxSlackBeta alpha q ≤ B := by
  classical
  unfold maxSlackBeta
  let scores : Finset ℝ :=
    Finset.univ.image fun a : Advertiser => I.slackScore alpha a q
  have hscores : scores.Nonempty := by
    obtain ⟨a⟩ := (inferInstance : Nonempty Advertiser)
    exact ⟨I.slackScore alpha a q, by simp [scores]⟩
  by_cases hmax_nonneg : 0 ≤ scores.max' hscores
  · rw [max_eq_right hmax_nonneg]
    have hmem : scores.max' hscores ∈ scores := Finset.max'_mem scores hscores
    rcases Finset.mem_image.mp hmem with ⟨a, _ha, ha⟩
    simpa [ha] using hscore a
  · rw [max_eq_left (le_of_not_ge hmax_nonneg)]
    simpa using hB

theorem dualFeasible_maxSlackBeta
    [Fintype Advertiser] [Nonempty Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (alpha : Advertiser → ℝ)
    (halpha : ∀ a, 0 ≤ alpha a) :
    I.DualFeasible alpha (I.maxSlackBeta alpha) := by
  exact dualFeasible_of_slackScore_le_beta I alpha (I.maxSlackBeta alpha)
    halpha (maxSlackBeta_nonneg I alpha)
    (slackScore_le_maxSlackBeta I alpha)

theorem dualFeasible_msvvAssignment
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) :
    I.DualFeasible (I.msvvAlphaFromAssignment A)
      (I.maxSlackBeta (I.msvvAlphaFromAssignment A)) := by
  exact dualFeasible_maxSlackBeta I (I.msvvAlphaFromAssignment A)
    (msvvAlphaFromAssignment_nonneg I A)

theorem dualFeasible_msvvNormalizedAssignment
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (A : Assignment Advertiser Query) :
    I.DualFeasible (I.msvvNormalizedAlphaFromAssignment A)
      (I.maxSlackBeta (I.msvvNormalizedAlphaFromAssignment A)) := by
  exact dualFeasible_maxSlackBeta I (I.msvvNormalizedAlphaFromAssignment A)
    (msvvNormalizedAlphaFromAssignment_nonneg I hbid hbudget A)

theorem mem_feasibleAdvertisers
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (q : Query) (a : Advertiser) :
    a ∈ I.feasibleAdvertisers A q ↔ I.CanAssign A q a := by
  classical
  simp [feasibleAdvertisers]

theorem exists_balanceChoice_of_exists_canAssign
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (q : Query)
    (h : ∃ a, I.CanAssign A q a) :
    ∃ a, I.IsBalanceChoice A q a := by
  classical
  have hnonempty : (I.feasibleAdvertisers A q).Nonempty := by
    rcases h with ⟨a, ha⟩
    exact ⟨a, (mem_feasibleAdvertisers I A q a).2 ha⟩
  obtain ⟨a, ha, hmax⟩ :=
    Finset.exists_max_image (I.feasibleAdvertisers A q)
      (fun a => I.balanceScore A a q) hnonempty
  refine ⟨a, ?_, ?_⟩
  · exact (mem_feasibleAdvertisers I A q a).1 ha
  · intro b hb
    exact hmax b ((mem_feasibleAdvertisers I A q b).2 hb)

/-- Canonical Balance/MSVV choice rule: pick a scaled-bid maximizer if one exists. -/
noncomputable def balanceChoiceRule
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query) :
    ChoiceRule Advertiser Query := by
  classical
  exact fun A q =>
    if h : ∃ a, I.CanAssign A q a then
      some (Classical.choose (exists_balanceChoice_of_exists_canAssign I A q h))
    else
      none

theorem balanceChoiceRule_isBalanceChoice_of_eq_some
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (q : Query) (a : Advertiser)
    (hchoice : I.balanceChoiceRule A q = some a) :
    I.IsBalanceChoice A q a := by
  classical
  unfold balanceChoiceRule at hchoice
  by_cases h : ∃ a, I.CanAssign A q a
  · simp [h] at hchoice
    have hspec :=
      Classical.choose_spec (exists_balanceChoice_of_exists_canAssign I A q h)
    simpa [← hchoice] using hspec
  · simp [h] at hchoice

theorem balanceChoiceRule_feasible
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query) :
    I.ChoiceRuleFeasible I.balanceChoiceRule := by
  intro A q a hchoice
  exact (balanceChoiceRule_isBalanceChoice_of_eq_some I A q a hchoice).1

theorem balanceChoiceRule_eq_none_iff_forall_not_canAssign
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (q : Query) :
    I.balanceChoiceRule A q = none ↔ ∀ a, ¬ I.CanAssign A q a := by
  classical
  unfold balanceChoiceRule
  by_cases h : ∃ a, I.CanAssign A q a
  · simp [h]
  · simp [h]
    intro a ha
    exact h ⟨a, ha⟩

theorem spend_le_spend_assignQuery_of_unassigned
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (A : Assignment Advertiser Query) (q : Query) (owner a : Advertiser)
    (hunassigned : A q = none) :
    I.spend A a ≤ I.spend (assignQuery A q owner) a := by
  by_cases ha : a = owner
  · subst a
    rw [spend_assignQuery_self_of_unassigned I A q owner hunassigned]
    exact le_add_of_nonneg_right (hbid owner q)
  · rw [spend_assignQuery_other_of_unassigned I A q
      (a := owner) (b := a) hunassigned ha]

set_option linter.flexible false in
theorem spend_le_stepHistoryState_spend
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (rule : ChoiceRule Advertiser Query)
    (S : HistoryState Advertiser Query) (q : Query)
    (hS : I.StateInvariant S) (a : Advertiser) :
    I.spend S.assignment a ≤
      I.spend (stepHistoryState I rule S q).assignment a := by
  classical
  by_cases hseen : q ∈ S.seen
  · simp [stepHistoryState, hseen]
  · cases hchoice : rule S.assignment q with
    | none =>
        simp [stepHistoryState, hseen, hchoice]
    | some owner =>
        simp [stepHistoryState, hseen, hchoice]
        exact spend_le_spend_assignQuery_of_unassigned I hbid
          S.assignment q owner a (hS.2 q hseen)

set_option linter.flexible false in
theorem stepHistoryState_invariant
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (rule : ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (S : HistoryState Advertiser Query) (q : Query)
    (hS : I.StateInvariant S) :
    I.StateInvariant (stepHistoryState I rule S q) := by
  classical
  by_cases hseen : q ∈ S.seen
  · simp [stepHistoryState, hseen]
    constructor
    · exact hS.1
    · intro q' hq'
      exact hS.2 q' hq'
  · cases hchoice : rule S.assignment q with
    | none =>
        simp [stepHistoryState, hseen, hchoice]
        constructor
        · exact hS.1
        · intro q' hq'
          have hnotseen : q' ∉ S.seen := by
            intro hin
            exact hq' (by simp [hin])
          exact hS.2 q' hnotseen
    | some a =>
        simp [stepHistoryState, hseen, hchoice]
        constructor
        · exact feasible_assignQuery_of_canAssign I S.assignment q a
            hS.1 (hS.2 q hseen) (hrule S.assignment q a hchoice)
        · intro q' hq'
          have hne : q' ≠ q := by
            intro heq
            apply hq'
            simp [heq]
          have hnotseen : q' ∉ S.seen := by
            intro hin
            exact hq' (by simp [hin])
          change assignQuery S.assignment q a q' = none
          rw [assignQuery_apply_ne S.assignment a hne]
          exact hS.2 q' hnotseen

theorem revenue_stepHistoryState_eq_add_stepRevenueCharge
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (rule : ChoiceRule Advertiser Query)
    (S : HistoryState Advertiser Query) (q : Query)
    (hS : I.StateInvariant S) :
    I.revenue (stepHistoryState I rule S q).assignment =
      I.revenue S.assignment + I.stepRevenueCharge rule S q := by
  classical
  by_cases hseen : q ∈ S.seen
  · simp [stepHistoryState, stepRevenueCharge, hseen]
  · cases hchoice : rule S.assignment q with
    | none =>
        simp [stepHistoryState, stepRevenueCharge, hseen, hchoice]
    | some a =>
        simp [stepHistoryState, stepRevenueCharge, hseen, hchoice]
        exact revenue_assignQuery_of_unassigned
          I S.assignment q a (hS.2 q hseen)

theorem runHistoryStateFrom_invariant
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (rule : ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query) (S : HistoryState Advertiser Query)
    (hS : I.StateInvariant S) :
    I.StateInvariant (runHistoryStateFrom I rule S history) := by
  induction history generalizing S with
  | nil =>
      exact hS
  | cons q qs ih =>
      exact ih (stepHistoryState I rule S q)
        (stepHistoryState_invariant I rule hrule S q hS)

theorem revenue_runHistoryStateFrom_eq_revenue_add_historyRevenueChargeFrom
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (rule : ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query) (S : HistoryState Advertiser Query)
    (hS : I.StateInvariant S) :
    I.revenue (runHistoryStateFrom I rule S history).assignment =
      I.revenue S.assignment + I.historyRevenueChargeFrom rule S history := by
  induction history generalizing S with
  | nil =>
      simp [runHistoryStateFrom, historyRevenueChargeFrom]
  | cons q qs ih =>
      let S' := stepHistoryState I rule S q
      have hS' : I.StateInvariant S' :=
        stepHistoryState_invariant I rule hrule S q hS
      have hstep :
          I.revenue S'.assignment =
            I.revenue S.assignment + I.stepRevenueCharge rule S q := by
        simpa [S'] using
          revenue_stepHistoryState_eq_add_stepRevenueCharge I rule S q hS
      have htail := ih S' hS'
      calc
        I.revenue (runHistoryStateFrom I rule S (q :: qs)).assignment =
            I.revenue (runHistoryStateFrom I rule S' qs).assignment := by
          simp [runHistoryStateFrom, S']
        _ = I.revenue S'.assignment + I.historyRevenueChargeFrom rule S' qs :=
          htail
        _ = I.revenue S.assignment + I.historyRevenueChargeFrom rule S (q :: qs) := by
          simp [historyRevenueChargeFrom, S', hstep, add_left_comm, add_comm]

theorem msvvRatio_mul_normalizedAlphaBudgetMass_increment_runHistoryStateFrom_add_historyBalanceCharge_le_historyRevenueCharge_add_historyMaxBidAlphaErrorSum
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (rule : ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query) (S : HistoryState Advertiser Query)
    (hS : I.StateInvariant S)
    {ε : ℝ}
    (hε : 0 ≤ ε)
    (hsmall : I.SmallBids ε) :
    msvvRatio *
        (I.msvvNormalizedAlphaBudgetMass
            (runHistoryStateFrom I rule S history).assignment -
          I.msvvNormalizedAlphaBudgetMass S.assignment) +
        I.historyBalanceChargeFrom rule S history ≤
      I.historyRevenueChargeFrom rule S history +
        I.historyMaxBidAlphaErrorSum ε history := by
  induction history generalizing S with
  | nil =>
      simp [runHistoryStateFrom, historyBalanceChargeFrom,
        historyRevenueChargeFrom, historyMaxBidAlphaErrorSum]
  | cons q qs ih =>
      let S' := stepHistoryState I rule S q
      have hS' : I.StateInvariant S' :=
        stepHistoryState_invariant I rule hrule S q hS
      have hhead :=
        msvvRatio_mul_normalizedAlphaBudgetMass_step_increment_add_balanceCharge_le_stepRevenueCharge_add_alphaError
          I hbid hbudget rule S q hS hε hsmall
      have htail := ih S' hS'
      calc
        msvvRatio *
            (I.msvvNormalizedAlphaBudgetMass
                (runHistoryStateFrom I rule S (q :: qs)).assignment -
              I.msvvNormalizedAlphaBudgetMass S.assignment) +
            I.historyBalanceChargeFrom rule S (q :: qs)
            =
          (msvvRatio *
              (I.msvvNormalizedAlphaBudgetMass S'.assignment -
                I.msvvNormalizedAlphaBudgetMass S.assignment) +
              (if q ∈ S.seen then
                0
              else
                match rule S.assignment q with
                | none => 0
                | some a => I.balanceScore S.assignment a q)) +
            (msvvRatio *
                (I.msvvNormalizedAlphaBudgetMass
                    (runHistoryStateFrom I rule S' qs).assignment -
                  I.msvvNormalizedAlphaBudgetMass S'.assignment) +
                I.historyBalanceChargeFrom rule S' qs) := by
                simp [runHistoryStateFrom, historyBalanceChargeFrom, S']
                ring
        _ ≤
          (I.stepRevenueCharge rule S q +
              I.maxBidForQuery q * (Real.exp ε - 1)) +
            (I.historyRevenueChargeFrom rule S' qs +
              I.historyMaxBidAlphaErrorSum ε qs) :=
                add_le_add hhead htail
        _ =
          I.historyRevenueChargeFrom rule S (q :: qs) +
            I.historyMaxBidAlphaErrorSum ε (q :: qs) := by
              simp [historyRevenueChargeFrom, historyMaxBidAlphaErrorSum, S']
              ring

theorem msvvRatio_mul_normalizedAlphaBudgetMass_balanceRun_add_historyBalanceCharge_le_revenue_add_historyMaxBidAlphaErrorSum
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    {ε : ℝ}
    (hε : 0 ≤ ε)
    (hsmall : I.SmallBids ε) :
    msvvRatio *
        I.msvvNormalizedAlphaBudgetMass
          (I.runAssignment I.balanceChoiceRule history) +
        I.historyBalanceChargeFrom I.balanceChoiceRule
          initialHistoryState history ≤
      I.revenue (I.runAssignment I.balanceChoiceRule history) +
        I.historyMaxBidAlphaErrorSum ε history := by
  have hnonneg : I.NonnegativeBudgets := fun a => (hbudget a).le
  have hS :
      I.StateInvariant
        (initialHistoryState : HistoryState Advertiser Query) :=
    initialHistoryState_invariant I hnonneg
  have hhist :=
    msvvRatio_mul_normalizedAlphaBudgetMass_increment_runHistoryStateFrom_add_historyBalanceCharge_le_historyRevenueCharge_add_historyMaxBidAlphaErrorSum
      I hbid hbudget I.balanceChoiceRule (balanceChoiceRule_feasible I)
      history (initialHistoryState : HistoryState Advertiser Query)
      hS hε hsmall
  have hhist' :
      msvvRatio *
          (I.msvvNormalizedAlphaBudgetMass
              (I.runAssignment I.balanceChoiceRule history) -
            I.msvvNormalizedAlphaBudgetMass
              (emptyAssignment : Assignment Advertiser Query)) +
          I.historyBalanceChargeFrom I.balanceChoiceRule
            initialHistoryState history ≤
        I.historyRevenueChargeFrom I.balanceChoiceRule
            initialHistoryState history +
          I.historyMaxBidAlphaErrorSum ε history := by
    simpa [runAssignment, runHistoryState, initialHistoryState]
      using hhist
  rw [msvvNormalizedAlphaBudgetMass_emptyAssignment I] at hhist'
  have hrev :
      I.revenue (I.runAssignment I.balanceChoiceRule history) =
        I.historyRevenueChargeFrom I.balanceChoiceRule
          initialHistoryState history := by
    have h :=
      revenue_runHistoryStateFrom_eq_revenue_add_historyRevenueChargeFrom
        I I.balanceChoiceRule (balanceChoiceRule_feasible I) history
        (initialHistoryState : HistoryState Advertiser Query) hS
    simpa [runAssignment, runHistoryState, initialHistoryState,
      revenue_emptyAssignment] using h
  rw [hrev]
  simpa using hhist'

theorem historyBalanceChargeFrom_le_historyRevenueChargeFrom
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (rule : ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query) (S : HistoryState Advertiser Query)
    (hS : I.StateInvariant S) :
    I.historyBalanceChargeFrom rule S history ≤
      I.historyRevenueChargeFrom rule S history := by
  induction history generalizing S with
  | nil =>
      simp [historyBalanceChargeFrom, historyRevenueChargeFrom]
  | cons q qs ih =>
      let S' := stepHistoryState I rule S q
      have hS' : I.StateInvariant S' :=
        stepHistoryState_invariant I rule hrule S q hS
      have htail := ih S' hS'
      by_cases hseen : q ∈ S.seen
      · simpa [historyBalanceChargeFrom, historyRevenueChargeFrom,
          stepRevenueCharge, hseen, S'] using htail
      · cases hchoice : rule S.assignment q with
        | none =>
            simpa [historyBalanceChargeFrom, historyRevenueChargeFrom,
              stepRevenueCharge, hseen, hchoice, S'] using htail
        | some a =>
            have hscore :
                I.balanceScore S.assignment a q ≤ I.bid a q := by
              unfold balanceScore
              have hmul :=
                mul_le_mul_of_nonneg_left
                  (balanceDiscount_le_one (I.spentFraction S.assignment a))
                  (hbid a q)
              simpa using hmul
            simpa [historyBalanceChargeFrom, historyRevenueChargeFrom,
              stepRevenueCharge, hseen, hchoice, S'] using
              add_le_add hscore htail

theorem spend_le_runHistoryStateFrom_spend
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (rule : ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query) (S : HistoryState Advertiser Query)
    (hS : I.StateInvariant S) (a : Advertiser) :
    I.spend S.assignment a ≤
      I.spend (runHistoryStateFrom I rule S history).assignment a := by
  induction history generalizing S with
  | nil =>
      simp [runHistoryStateFrom]
  | cons q qs ih =>
      have hstep :
          I.spend S.assignment a ≤
            I.spend (stepHistoryState I rule S q).assignment a :=
        spend_le_stepHistoryState_spend I hbid rule S q hS a
      have hSstep :
          I.StateInvariant (stepHistoryState I rule S q) :=
        stepHistoryState_invariant I rule hrule S q hS
      have htail :
          I.spend (stepHistoryState I rule S q).assignment a ≤
            I.spend
              (runHistoryStateFrom I rule
                (stepHistoryState I rule S q) qs).assignment a :=
        ih (stepHistoryState I rule S q) hSstep
      exact hstep.trans htail

theorem spentFraction_le_runHistoryStateFrom_spentFraction
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (rule : ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query) (S : HistoryState Advertiser Query)
    (hS : I.StateInvariant S) (a : Advertiser)
    (hbudget : 0 < I.budget a) :
    I.spentFraction S.assignment a ≤
      I.spentFraction (runHistoryStateFrom I rule S history).assignment a := by
  unfold spentFraction
  exact div_le_div_of_nonneg_right
    (spend_le_runHistoryStateFrom_spend I hbid rule hrule history S hS a)
    hbudget.le

theorem msvvAlphaFromAssignment_le_runHistoryStateFrom
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (rule : ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query) (S : HistoryState Advertiser Query)
    (hS : I.StateInvariant S) (a : Advertiser)
    (hbudget : 0 < I.budget a) :
    I.msvvAlphaFromAssignment S.assignment a ≤
      I.msvvAlphaFromAssignment
        (runHistoryStateFrom I rule S history).assignment a := by
  unfold msvvAlphaFromAssignment
  exact msvvDualAlpha_mono
    (spentFraction_le_runHistoryStateFrom_spentFraction
      I hbid rule hrule history S hS a hbudget)

theorem msvvNormalizedAlphaFromAssignment_le_runHistoryStateFrom
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (rule : ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query) (S : HistoryState Advertiser Query)
    (hS : I.StateInvariant S) (a : Advertiser)
    (hbudget : 0 < I.budget a) :
    I.msvvNormalizedAlphaFromAssignment S.assignment a ≤
      I.msvvNormalizedAlphaFromAssignment
        (runHistoryStateFrom I rule S history).assignment a := by
  unfold msvvNormalizedAlphaFromAssignment
  exact msvvNormalizedDualAlpha_mono
    (spentFraction_le_runHistoryStateFrom_spentFraction
      I hbid rule hrule history S hS a hbudget)

theorem final_slackScore_le_initial_balanceScore
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (rule : ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query) (S : HistoryState Advertiser Query)
    (hS : I.StateInvariant S) (a : Advertiser) (q : Query)
    (hbudget : 0 < I.budget a) :
    I.slackScore
        (I.msvvAlphaFromAssignment
          (runHistoryStateFrom I rule S history).assignment) a q ≤
      I.balanceScore S.assignment a q := by
  have halpha :=
    msvvAlphaFromAssignment_le_runHistoryStateFrom
      I hbid rule hrule history S hS a hbudget
  have hslack :=
    slackScore_anti_mono_alpha I hbid
      (I.msvvAlphaFromAssignment S.assignment)
      (I.msvvAlphaFromAssignment
        (runHistoryStateFrom I rule S history).assignment)
      a q halpha
  simpa [balanceScore_eq_slackScore_msvvAlphaFromAssignment I S.assignment a q]
    using hslack

theorem msvvRatio_mul_final_normalized_slackScore_le_initial_balanceScore
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (rule : ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query) (S : HistoryState Advertiser Query)
    (hS : I.StateInvariant S) (a : Advertiser) (q : Query)
    (hbudget : 0 < I.budget a) :
    msvvRatio *
        I.slackScore
          (I.msvvNormalizedAlphaFromAssignment
            (runHistoryStateFrom I rule S history).assignment) a q ≤
      I.balanceScore S.assignment a q := by
  have halpha :=
    msvvNormalizedAlphaFromAssignment_le_runHistoryStateFrom
      I hbid rule hrule history S hS a hbudget
  have hslack :=
    slackScore_anti_mono_alpha I hbid
      (I.msvvNormalizedAlphaFromAssignment S.assignment)
      (I.msvvNormalizedAlphaFromAssignment
        (runHistoryStateFrom I rule S history).assignment)
      a q halpha
  have hscaled :=
    mul_le_mul_of_nonneg_left hslack msvvRatio_nonneg
  simpa [msvvRatio_mul_slackScore_msvvNormalizedAlphaFromAssignment_eq_balanceScore
    I S.assignment a q] using hscaled

theorem maxSlackBeta_runHistoryStateFrom_le_balanceScore_of_all_canAssign
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (rule : ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query) (S : HistoryState Advertiser Query)
    (hS : I.StateInvariant S) (q : Query) (chosen : Advertiser)
    (hchoice : I.IsBalanceChoice S.assignment q chosen)
    (hall : ∀ a, I.CanAssign S.assignment q a) :
    I.maxSlackBeta
        (I.msvvAlphaFromAssignment
          (runHistoryStateFrom I rule S history).assignment) q ≤
      I.balanceScore S.assignment chosen q := by
  apply maxSlackBeta_le_of_slackScore_le
  · exact balanceScore_nonneg_of_feasible I hbid S.assignment chosen q
      (hbudget chosen) hS.1
  · intro a
    exact (final_slackScore_le_initial_balanceScore
      I hbid rule hrule history S hS a q (hbudget a)).trans
      (hchoice.2 a (hall a))

theorem msvvRatio_mul_maxSlackBeta_normalized_runHistoryStateFrom_le_balanceScore_of_all_canAssign
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (rule : ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query) (S : HistoryState Advertiser Query)
    (hS : I.StateInvariant S) (q : Query) (chosen : Advertiser)
    (hchoice : I.IsBalanceChoice S.assignment q chosen)
    (hall : ∀ a, I.CanAssign S.assignment q a) :
    msvvRatio *
        I.maxSlackBeta
          (I.msvvNormalizedAlphaFromAssignment
            (runHistoryStateFrom I rule S history).assignment) q ≤
      I.balanceScore S.assignment chosen q := by
  apply mul_maxSlackBeta_le_of_mul_slackScore_le
  · exact msvvRatio_nonneg
  · exact balanceScore_nonneg_of_feasible I hbid S.assignment chosen q
      (hbudget chosen) hS.1
  · intro a
    exact (msvvRatio_mul_final_normalized_slackScore_le_initial_balanceScore
      I hbid rule hrule history S hS a q (hbudget a)).trans
      (hchoice.2 a (hall a))

theorem final_msvvAlphaFromAssignment_ge_exp_neg_epsilon_of_not_canAssign
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (rule : ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query) (S : HistoryState Advertiser Query)
    (hS : I.StateInvariant S) {ε : ℝ}
    (hsmall : I.SmallBids ε) (a : Advertiser) (q : Query)
    (hbudget : 0 < I.budget a)
    (hnot : ¬ I.CanAssign S.assignment q a) :
    Real.exp (-ε) ≤
      I.msvvAlphaFromAssignment
        (runHistoryStateFrom I rule S history).assignment a := by
  have hblocked :
      1 - ε < I.spentFraction S.assignment a :=
    spentFraction_gt_one_sub_epsilon_of_not_canAssign
      I S.assignment a q hbudget hsmall hnot
  have hrun :
      I.spentFraction S.assignment a ≤
        I.spentFraction
          (runHistoryStateFrom I rule S history).assignment a :=
    spentFraction_le_runHistoryStateFrom_spentFraction
      I hbid rule hrule history S hS a hbudget
  have hfrac :
      1 - ε ≤
        I.spentFraction
          (runHistoryStateFrom I rule S history).assignment a :=
    (le_of_lt hblocked).trans hrun
  unfold msvvAlphaFromAssignment msvvDualAlpha
  exact Real.exp_le_exp.mpr (by linarith)

theorem final_msvvNormalizedAlphaFromAssignment_ge_one_sub_epsilon_of_not_canAssign
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (rule : ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query) (S : HistoryState Advertiser Query)
    (hS : I.StateInvariant S) {ε : ℝ}
    (hsmall : I.SmallBids ε) (a : Advertiser) (q : Query)
    (hbudget : 0 < I.budget a)
    (hnot : ¬ I.CanAssign S.assignment q a) :
    msvvNormalizedDualAlpha (1 - ε) ≤
      I.msvvNormalizedAlphaFromAssignment
        (runHistoryStateFrom I rule S history).assignment a := by
  have hblocked :
      1 - ε < I.spentFraction S.assignment a :=
    spentFraction_gt_one_sub_epsilon_of_not_canAssign
      I S.assignment a q hbudget hsmall hnot
  have hrun :
      I.spentFraction S.assignment a ≤
        I.spentFraction
          (runHistoryStateFrom I rule S history).assignment a :=
    spentFraction_le_runHistoryStateFrom_spentFraction
      I hbid rule hrule history S hS a hbudget
  have hfrac :
      1 - ε ≤
        I.spentFraction
          (runHistoryStateFrom I rule S history).assignment a :=
    (le_of_lt hblocked).trans hrun
  unfold msvvNormalizedAlphaFromAssignment
  exact msvvNormalizedDualAlpha_mono hfrac

theorem final_slackScore_le_bid_mul_one_sub_exp_neg_epsilon_of_not_canAssign
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (rule : ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query) (S : HistoryState Advertiser Query)
    (hS : I.StateInvariant S) {ε : ℝ}
    (hsmall : I.SmallBids ε) (a : Advertiser) (q : Query)
    (hbudget : 0 < I.budget a)
    (hnot : ¬ I.CanAssign S.assignment q a) :
    I.slackScore
        (I.msvvAlphaFromAssignment
          (runHistoryStateFrom I rule S history).assignment) a q ≤
      I.bid a q * (1 - Real.exp (-ε)) := by
  have halpha :=
    final_msvvAlphaFromAssignment_ge_exp_neg_epsilon_of_not_canAssign
      I hbid rule hrule history S hS hsmall a q hbudget hnot
  unfold slackScore
  have hfactor :
      1 -
          I.msvvAlphaFromAssignment
            (runHistoryStateFrom I rule S history).assignment a ≤
        1 - Real.exp (-ε) := by
    linarith
  exact mul_le_mul_of_nonneg_left hfactor (hbid a q)

theorem msvvRatio_mul_final_normalized_slackScore_le_bid_error_of_not_canAssign
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (rule : ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query) (S : HistoryState Advertiser Query)
    (hS : I.StateInvariant S) {ε : ℝ}
    (hsmall : I.SmallBids ε) (a : Advertiser) (q : Query)
    (hbudget : 0 < I.budget a)
    (hnot : ¬ I.CanAssign S.assignment q a) :
    msvvRatio *
        I.slackScore
          (I.msvvNormalizedAlphaFromAssignment
            (runHistoryStateFrom I rule S history).assignment) a q ≤
      I.bid a q * (1 - Real.exp (-ε)) := by
  have halpha :=
    final_msvvNormalizedAlphaFromAssignment_ge_one_sub_epsilon_of_not_canAssign
      I hbid rule hrule history S hS hsmall a q hbudget hnot
  have hfactor :
      1 -
          I.msvvNormalizedAlphaFromAssignment
            (runHistoryStateFrom I rule S history).assignment a ≤
        1 - msvvNormalizedDualAlpha (1 - ε) := by
    linarith
  have hslack :
      I.slackScore
          (I.msvvNormalizedAlphaFromAssignment
            (runHistoryStateFrom I rule S history).assignment) a q ≤
        I.bid a q * (1 - msvvNormalizedDualAlpha (1 - ε)) := by
    unfold slackScore
    exact mul_le_mul_of_nonneg_left hfactor (hbid a q)
  have hscaled :=
    mul_le_mul_of_nonneg_left hslack msvvRatio_nonneg
  calc
    msvvRatio *
        I.slackScore
          (I.msvvNormalizedAlphaFromAssignment
            (runHistoryStateFrom I rule S history).assignment) a q ≤
        msvvRatio * (I.bid a q * (1 - msvvNormalizedDualAlpha (1 - ε))) :=
          hscaled
    _ = I.bid a q * (1 - Real.exp (-ε)) := by
      rw [show msvvRatio *
            (I.bid a q * (1 - msvvNormalizedDualAlpha (1 - ε))) =
          I.bid a q *
            (msvvRatio * (1 - msvvNormalizedDualAlpha (1 - ε))) by ring]
      rw [msvvRatio_mul_one_sub_msvvNormalizedDualAlpha_one_sub]

theorem msvvRatio_mul_final_normalized_slackScore_le_max_balanceScore_maxBidError_of_choice
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (rule : ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query) (S : HistoryState Advertiser Query)
    (hS : I.StateInvariant S) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hsmall : I.SmallBids ε) (q : Query) (chosen a : Advertiser)
    (hchoice : I.IsBalanceChoice S.assignment q chosen) :
    msvvRatio *
        I.slackScore
          (I.msvvNormalizedAlphaFromAssignment
            (runHistoryStateFrom I rule S history).assignment) a q ≤
      max (I.balanceScore S.assignment chosen q)
        (I.maxBidForQuery q * (1 - Real.exp (-ε))) := by
  by_cases hcan : I.CanAssign S.assignment q a
  · have hle :=
      msvvRatio_mul_final_normalized_slackScore_le_initial_balanceScore
        I hbid rule hrule history S hS a q (hbudget a)
    exact (hle.trans (hchoice.2 a hcan)).trans (le_max_left _ _)
  · have hle :=
      msvvRatio_mul_final_normalized_slackScore_le_bid_error_of_not_canAssign
        I hbid rule hrule history S hS hsmall a q (hbudget a) hcan
    have hbidMax :
        I.bid a q * (1 - Real.exp (-ε)) ≤
          I.maxBidForQuery q * (1 - Real.exp (-ε)) :=
      mul_le_mul_of_nonneg_right
        (bid_le_maxBidForQuery I a q) (one_sub_exp_neg_nonneg hε)
    exact (hle.trans hbidMax).trans (le_max_right _ _)

theorem msvvRatio_mul_maxSlackBeta_normalized_runHistoryStateFrom_le_max_balanceScore_maxBidError_of_choice
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (rule : ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query) (S : HistoryState Advertiser Query)
    (hS : I.StateInvariant S) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hsmall : I.SmallBids ε) (q : Query) (chosen : Advertiser)
    (hchoice : I.IsBalanceChoice S.assignment q chosen) :
    msvvRatio *
        I.maxSlackBeta
          (I.msvvNormalizedAlphaFromAssignment
            (runHistoryStateFrom I rule S history).assignment) q ≤
      max (I.balanceScore S.assignment chosen q)
        (I.maxBidForQuery q * (1 - Real.exp (-ε))) := by
  apply mul_maxSlackBeta_le_of_mul_slackScore_le
  · exact msvvRatio_nonneg
  · have hbal :
        0 ≤ I.balanceScore S.assignment chosen q :=
      balanceScore_nonneg_of_feasible
        I hbid S.assignment chosen q (hbudget chosen) hS.1
    exact hbal.trans (le_max_left _ _)
  · intro a
    exact msvvRatio_mul_final_normalized_slackScore_le_max_balanceScore_maxBidError_of_choice
      I hbid hbudget rule hrule history S hS hε hsmall q chosen a hchoice

theorem msvvRatio_mul_maxSlackBeta_normalized_runHistoryStateFrom_le_balanceScore_add_maxBidError_of_choice
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (rule : ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query) (S : HistoryState Advertiser Query)
    (hS : I.StateInvariant S) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hsmall : I.SmallBids ε) (q : Query) (chosen : Advertiser)
    (hchoice : I.IsBalanceChoice S.assignment q chosen) :
    msvvRatio *
        I.maxSlackBeta
          (I.msvvNormalizedAlphaFromAssignment
            (runHistoryStateFrom I rule S history).assignment) q ≤
      I.balanceScore S.assignment chosen q +
        I.maxBidForQuery q * (1 - Real.exp (-ε)) := by
  have hmax :=
    msvvRatio_mul_maxSlackBeta_normalized_runHistoryStateFrom_le_max_balanceScore_maxBidError_of_choice
      I hbid hbudget rule hrule history S hS hε hsmall q chosen hchoice
  have hbal :
      0 ≤ I.balanceScore S.assignment chosen q :=
    balanceScore_nonneg_of_feasible
      I hbid S.assignment chosen q (hbudget chosen) hS.1
  have herr :
      0 ≤ I.maxBidForQuery q * (1 - Real.exp (-ε)) :=
    mul_nonneg (maxBidForQuery_nonneg I q) (one_sub_exp_neg_nonneg hε)
  have hsum :
      max (I.balanceScore S.assignment chosen q)
          (I.maxBidForQuery q * (1 - Real.exp (-ε))) ≤
        I.balanceScore S.assignment chosen q +
          I.maxBidForQuery q * (1 - Real.exp (-ε)) := by
    apply max_le
    · linarith
    · linarith
  exact hmax.trans hsum

theorem msvvRatio_mul_maxSlackBeta_normalized_runHistoryStateFrom_le_maxBidError_of_all_not_canAssign
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (rule : ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query) (S : HistoryState Advertiser Query)
    (hS : I.StateInvariant S) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hsmall : I.SmallBids ε) (q : Query)
    (hallBlocked : ∀ a, ¬ I.CanAssign S.assignment q a) :
    msvvRatio *
        I.maxSlackBeta
          (I.msvvNormalizedAlphaFromAssignment
            (runHistoryStateFrom I rule S history).assignment) q ≤
      I.maxBidForQuery q * (1 - Real.exp (-ε)) := by
  apply mul_maxSlackBeta_le_of_mul_slackScore_le
  · exact msvvRatio_nonneg
  · exact mul_nonneg (maxBidForQuery_nonneg I q) (one_sub_exp_neg_nonneg hε)
  · intro a
    have hle :=
      msvvRatio_mul_final_normalized_slackScore_le_bid_error_of_not_canAssign
        I hbid rule hrule history S hS hsmall a q (hbudget a)
        (hallBlocked a)
    have hbidMax :
        I.bid a q * (1 - Real.exp (-ε)) ≤
          I.maxBidForQuery q * (1 - Real.exp (-ε)) :=
      mul_le_mul_of_nonneg_right
        (bid_le_maxBidForQuery I a q) (one_sub_exp_neg_nonneg hε)
    exact hle.trans hbidMax

theorem final_slackScore_le_max_balanceScore_bidError_of_choice
    [Fintype Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (rule : ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query) (S : HistoryState Advertiser Query)
    (hS : I.StateInvariant S) {ε : ℝ}
    (hsmall : I.SmallBids ε) (q : Query) (chosen a : Advertiser)
    (hchoice : I.IsBalanceChoice S.assignment q chosen) :
    I.slackScore
        (I.msvvAlphaFromAssignment
          (runHistoryStateFrom I rule S history).assignment) a q ≤
      max (I.balanceScore S.assignment chosen q)
        (I.bid a q * (1 - Real.exp (-ε))) := by
  by_cases hcan : I.CanAssign S.assignment q a
  · have hle :=
      final_slackScore_le_initial_balanceScore
        I hbid rule hrule history S hS a q (hbudget a)
    exact (hle.trans (hchoice.2 a hcan)).trans (le_max_left _ _)
  · have hle :=
      final_slackScore_le_bid_mul_one_sub_exp_neg_epsilon_of_not_canAssign
        I hbid rule hrule history S hS hsmall a q (hbudget a) hcan
    exact hle.trans (le_max_right _ _)

theorem final_slackScore_le_max_balanceScore_maxBidError_of_choice
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (rule : ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query) (S : HistoryState Advertiser Query)
    (hS : I.StateInvariant S) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hsmall : I.SmallBids ε) (q : Query) (chosen a : Advertiser)
    (hchoice : I.IsBalanceChoice S.assignment q chosen) :
    I.slackScore
        (I.msvvAlphaFromAssignment
          (runHistoryStateFrom I rule S history).assignment) a q ≤
      max (I.balanceScore S.assignment chosen q)
        (I.maxBidForQuery q * (1 - Real.exp (-ε))) := by
  by_cases hcan : I.CanAssign S.assignment q a
  · have hle :=
      final_slackScore_le_initial_balanceScore
        I hbid rule hrule history S hS a q (hbudget a)
    exact (hle.trans (hchoice.2 a hcan)).trans (le_max_left _ _)
  · have hle :=
      final_slackScore_le_bid_mul_one_sub_exp_neg_epsilon_of_not_canAssign
        I hbid rule hrule history S hS hsmall a q (hbudget a) hcan
    have hbidMax :
        I.bid a q * (1 - Real.exp (-ε)) ≤
          I.maxBidForQuery q * (1 - Real.exp (-ε)) :=
      mul_le_mul_of_nonneg_right
        (bid_le_maxBidForQuery I a q) (one_sub_exp_neg_nonneg hε)
    exact (hle.trans hbidMax).trans (le_max_right _ _)

theorem maxSlackBeta_runHistoryStateFrom_le_max_balanceScore_maxBidError_of_choice
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (rule : ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query) (S : HistoryState Advertiser Query)
    (hS : I.StateInvariant S) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hsmall : I.SmallBids ε) (q : Query) (chosen : Advertiser)
    (hchoice : I.IsBalanceChoice S.assignment q chosen) :
    I.maxSlackBeta
        (I.msvvAlphaFromAssignment
          (runHistoryStateFrom I rule S history).assignment) q ≤
      max (I.balanceScore S.assignment chosen q)
        (I.maxBidForQuery q * (1 - Real.exp (-ε))) := by
  apply maxSlackBeta_le_of_slackScore_le
  · have hbal :
        0 ≤ I.balanceScore S.assignment chosen q :=
      balanceScore_nonneg_of_feasible
        I hbid S.assignment chosen q (hbudget chosen) hS.1
    exact hbal.trans (le_max_left _ _)
  · intro a
    exact final_slackScore_le_max_balanceScore_maxBidError_of_choice
      I hbid hbudget rule hrule history S hS hε hsmall q chosen a hchoice

theorem maxSlackBeta_runHistoryStateFrom_le_balanceScore_add_maxBidError_of_choice
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (rule : ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query) (S : HistoryState Advertiser Query)
    (hS : I.StateInvariant S) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hsmall : I.SmallBids ε) (q : Query) (chosen : Advertiser)
    (hchoice : I.IsBalanceChoice S.assignment q chosen) :
    I.maxSlackBeta
        (I.msvvAlphaFromAssignment
          (runHistoryStateFrom I rule S history).assignment) q ≤
      I.balanceScore S.assignment chosen q +
        I.maxBidForQuery q * (1 - Real.exp (-ε)) := by
  have hmax :=
    maxSlackBeta_runHistoryStateFrom_le_max_balanceScore_maxBidError_of_choice
      I hbid hbudget rule hrule history S hS hε hsmall q chosen hchoice
  have hbal :
      0 ≤ I.balanceScore S.assignment chosen q :=
    balanceScore_nonneg_of_feasible
      I hbid S.assignment chosen q (hbudget chosen) hS.1
  have herr :
      0 ≤ I.maxBidForQuery q * (1 - Real.exp (-ε)) :=
    mul_nonneg (maxBidForQuery_nonneg I q) (one_sub_exp_neg_nonneg hε)
  have hsum :
      max (I.balanceScore S.assignment chosen q)
          (I.maxBidForQuery q * (1 - Real.exp (-ε))) ≤
        I.balanceScore S.assignment chosen q +
          I.maxBidForQuery q * (1 - Real.exp (-ε)) := by
    apply max_le
    · linarith
    · linarith
  exact hmax.trans hsum

theorem maxSlackBeta_runHistoryStateFrom_le_maxBidError_of_all_not_canAssign
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (rule : ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query) (S : HistoryState Advertiser Query)
    (hS : I.StateInvariant S) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hsmall : I.SmallBids ε) (q : Query)
    (hallBlocked : ∀ a, ¬ I.CanAssign S.assignment q a) :
    I.maxSlackBeta
        (I.msvvAlphaFromAssignment
          (runHistoryStateFrom I rule S history).assignment) q ≤
      I.maxBidForQuery q * (1 - Real.exp (-ε)) := by
  apply maxSlackBeta_le_of_slackScore_le
  · exact mul_nonneg (maxBidForQuery_nonneg I q) (one_sub_exp_neg_nonneg hε)
  · intro a
    have hle :=
      final_slackScore_le_bid_mul_one_sub_exp_neg_epsilon_of_not_canAssign
        I hbid rule hrule history S hS hsmall a q (hbudget a)
        (hallBlocked a)
    have hbidMax :
        I.bid a q * (1 - Real.exp (-ε)) ≤
          I.maxBidForQuery q * (1 - Real.exp (-ε)) :=
      mul_le_mul_of_nonneg_right
        (bid_le_maxBidForQuery I a q) (one_sub_exp_neg_nonneg hε)
    exact hle.trans hbidMax

theorem stepHistoryState_seen
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (rule : ChoiceRule Advertiser Query)
    (S : HistoryState Advertiser Query) (q : Query) :
    (stepHistoryState I rule S q).seen = insert q S.seen := by
  classical
  unfold stepHistoryState
  by_cases hseen : q ∈ S.seen
  · simp [hseen]
  · simp [hseen]
    cases rule S.assignment q <;> simp

theorem runHistoryStateFrom_seen
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (rule : ChoiceRule Advertiser Query)
    (history : List Query) (S : HistoryState Advertiser Query) :
    (runHistoryStateFrom I rule S history).seen =
      historyFinset history ∪ S.seen := by
  induction history generalizing S with
  | nil =>
      simp [runHistoryStateFrom, historyFinset]
  | cons q qs ih =>
      rw [runHistoryStateFrom, ih]
      rw [stepHistoryState_seen]
      ext q'
      simp [historyFinset, or_comm]

theorem runHistoryState_seen
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (rule : ChoiceRule Advertiser Query) (history : List Query) :
    (runHistoryState I rule history).seen = historyFinset history := by
  unfold runHistoryState
  rw [runHistoryStateFrom_seen]
  ext q
  simp [initialHistoryState]

theorem historyMaxSlackBetaSum_balanceChoiceRun_le_balanceCharge_add_maxBidError
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List Query) (S : HistoryState Advertiser Query)
    (hS : I.StateInvariant S)
    (hfresh : ∀ q, q ∈ historyFinset history → q ∉ S.seen)
    (hnodup : history.Nodup) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hsmall : I.SmallBids ε) :
    historyMaxSlackBetaSum I
        (I.msvvAlphaFromAssignment
          (runHistoryStateFrom I I.balanceChoiceRule S history).assignment)
        history ≤
      historyBalanceChargeFrom I I.balanceChoiceRule S history +
        historyMaxBidErrorSum I ε history := by
  induction history generalizing S with
  | nil =>
      simp [historyMaxSlackBetaSum, historyBalanceChargeFrom,
        historyMaxBidErrorSum]
  | cons q qs ih =>
      have hnodupParts := List.nodup_cons.mp hnodup
      have hqNotMemQs : q ∉ qs := hnodupParts.1
      have hnodupQs : qs.Nodup := hnodupParts.2
      have hqFresh : q ∉ S.seen := by
        exact hfresh q (by simp [historyFinset])
      let S' := stepHistoryState I I.balanceChoiceRule S q
      have hS' : I.StateInvariant S' :=
        stepHistoryState_invariant I I.balanceChoiceRule
          (balanceChoiceRule_feasible I) S q hS
      have hqNotTail : q ∉ historyFinset qs := by
        intro hmem
        exact hqNotMemQs ((mem_historyFinset (history := qs) (q := q)).1 hmem)
      have htailFresh :
          ∀ r, r ∈ historyFinset qs → r ∉ S'.seen := by
        intro r hr hseen
        have hseen_eq :
            S'.seen = insert q S.seen := by
          simpa [S'] using
            (stepHistoryState_seen I I.balanceChoiceRule S q)
        rw [hseen_eq] at hseen
        rcases Finset.mem_insert.mp hseen with hqr | hseenOld
        · subst r
          exact hqNotTail hr
        · exact hfresh r (by simp [historyFinset, hr]) hseenOld
      have htail :=
        ih S' hS' htailFresh hnodupQs
      have hhead :
          I.maxSlackBeta
              (I.msvvAlphaFromAssignment
                (runHistoryStateFrom I I.balanceChoiceRule S (q :: qs)).assignment)
              q ≤
            (match I.balanceChoiceRule S.assignment q with
              | none => 0
              | some a => I.balanceScore S.assignment a q) +
              I.maxBidForQuery q * (1 - Real.exp (-ε)) := by
        cases hchoice : I.balanceChoiceRule S.assignment q with
        | none =>
            have hallBlocked :
                ∀ a, ¬ I.CanAssign S.assignment q a :=
              (balanceChoiceRule_eq_none_iff_forall_not_canAssign
                I S.assignment q).1 hchoice
            have hle :=
              maxSlackBeta_runHistoryStateFrom_le_maxBidError_of_all_not_canAssign
                I hbid hbudget I.balanceChoiceRule
                (balanceChoiceRule_feasible I) (q :: qs) S hS hε hsmall q
                hallBlocked
            simpa [hchoice] using hle
        | some chosen =>
            have hbalance :
                I.IsBalanceChoice S.assignment q chosen :=
              balanceChoiceRule_isBalanceChoice_of_eq_some
                I S.assignment q chosen hchoice
            have hle :=
              maxSlackBeta_runHistoryStateFrom_le_balanceScore_add_maxBidError_of_choice
                I hbid hbudget I.balanceChoiceRule
                (balanceChoiceRule_feasible I) (q :: qs) S hS hε hsmall
                q chosen hbalance
            simpa [hchoice] using hle
      have hhead' :
          I.maxSlackBeta
              (I.msvvAlphaFromAssignment
                (runHistoryStateFrom I I.balanceChoiceRule S' qs).assignment)
              q ≤
            (match I.balanceChoiceRule S.assignment q with
              | none => 0
              | some a => I.balanceScore S.assignment a q) +
              I.maxBidForQuery q * (1 - Real.exp (-ε)) := by
        simpa [S', runHistoryStateFrom] using hhead
      calc
        historyMaxSlackBetaSum I
            (I.msvvAlphaFromAssignment
              (runHistoryStateFrom I I.balanceChoiceRule S (q :: qs)).assignment)
            (q :: qs)
            =
          I.maxSlackBeta
              (I.msvvAlphaFromAssignment
                (runHistoryStateFrom I I.balanceChoiceRule S' qs).assignment)
              q +
            historyMaxSlackBetaSum I
              (I.msvvAlphaFromAssignment
                (runHistoryStateFrom I I.balanceChoiceRule S' qs).assignment)
              qs := by
                simp [historyMaxSlackBetaSum, runHistoryStateFrom, S']
        _ ≤
          ((match I.balanceChoiceRule S.assignment q with
            | none => 0
            | some a => I.balanceScore S.assignment a q) +
              I.maxBidForQuery q * (1 - Real.exp (-ε))) +
            (historyBalanceChargeFrom I I.balanceChoiceRule S' qs +
              historyMaxBidErrorSum I ε qs) :=
                add_le_add hhead' htail
        _ =
          historyBalanceChargeFrom I I.balanceChoiceRule S (q :: qs) +
            historyMaxBidErrorSum I ε (q :: qs) := by
                simp [historyBalanceChargeFrom, historyMaxBidErrorSum,
                  hqFresh, S', add_assoc, add_left_comm, add_comm]

theorem msvvRatio_mul_historyMaxSlackBetaSum_normalized_balanceChoiceRun_le_balanceCharge_add_maxBidError
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List Query) (S : HistoryState Advertiser Query)
    (hS : I.StateInvariant S)
    (hfresh : ∀ q, q ∈ historyFinset history → q ∉ S.seen)
    (hnodup : history.Nodup) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hsmall : I.SmallBids ε) :
    msvvRatio *
        historyMaxSlackBetaSum I
          (I.msvvNormalizedAlphaFromAssignment
            (runHistoryStateFrom I I.balanceChoiceRule S history).assignment)
          history ≤
      historyBalanceChargeFrom I I.balanceChoiceRule S history +
        historyMaxBidErrorSum I ε history := by
  induction history generalizing S with
  | nil =>
      simp [historyMaxSlackBetaSum, historyBalanceChargeFrom,
        historyMaxBidErrorSum]
  | cons q qs ih =>
      have hnodupParts := List.nodup_cons.mp hnodup
      have hqNotMemQs : q ∉ qs := hnodupParts.1
      have hnodupQs : qs.Nodup := hnodupParts.2
      have hqFresh : q ∉ S.seen := by
        exact hfresh q (by simp [historyFinset])
      let S' := stepHistoryState I I.balanceChoiceRule S q
      have hS' : I.StateInvariant S' :=
        stepHistoryState_invariant I I.balanceChoiceRule
          (balanceChoiceRule_feasible I) S q hS
      have hqNotTail : q ∉ historyFinset qs := by
        intro hmem
        exact hqNotMemQs ((mem_historyFinset (history := qs) (q := q)).1 hmem)
      have htailFresh :
          ∀ r, r ∈ historyFinset qs → r ∉ S'.seen := by
        intro r hr hseen
        have hseen_eq :
            S'.seen = insert q S.seen := by
          simpa [S'] using
            (stepHistoryState_seen I I.balanceChoiceRule S q)
        rw [hseen_eq] at hseen
        rcases Finset.mem_insert.mp hseen with hqr | hseenOld
        · subst r
          exact hqNotTail hr
        · exact hfresh r (by simp [historyFinset, hr]) hseenOld
      have htail :=
        ih S' hS' htailFresh hnodupQs
      have hhead :
          msvvRatio *
              I.maxSlackBeta
                (I.msvvNormalizedAlphaFromAssignment
                  (runHistoryStateFrom I I.balanceChoiceRule S (q :: qs)).assignment)
                q ≤
            (match I.balanceChoiceRule S.assignment q with
              | none => 0
              | some a => I.balanceScore S.assignment a q) +
              I.maxBidForQuery q * (1 - Real.exp (-ε)) := by
        cases hchoice : I.balanceChoiceRule S.assignment q with
        | none =>
            have hallBlocked :
                ∀ a, ¬ I.CanAssign S.assignment q a :=
              (balanceChoiceRule_eq_none_iff_forall_not_canAssign
                I S.assignment q).1 hchoice
            have hle :=
              msvvRatio_mul_maxSlackBeta_normalized_runHistoryStateFrom_le_maxBidError_of_all_not_canAssign
                I hbid hbudget I.balanceChoiceRule
                (balanceChoiceRule_feasible I) (q :: qs) S hS hε hsmall q
                hallBlocked
            simpa [hchoice] using hle
        | some chosen =>
            have hbalance :
                I.IsBalanceChoice S.assignment q chosen :=
              balanceChoiceRule_isBalanceChoice_of_eq_some
                I S.assignment q chosen hchoice
            have hle :=
              msvvRatio_mul_maxSlackBeta_normalized_runHistoryStateFrom_le_balanceScore_add_maxBidError_of_choice
                I hbid hbudget I.balanceChoiceRule
                (balanceChoiceRule_feasible I) (q :: qs) S hS hε hsmall
                q chosen hbalance
            simpa [hchoice] using hle
      have hhead' :
          msvvRatio *
              I.maxSlackBeta
                (I.msvvNormalizedAlphaFromAssignment
                  (runHistoryStateFrom I I.balanceChoiceRule S' qs).assignment)
                q ≤
            (match I.balanceChoiceRule S.assignment q with
              | none => 0
              | some a => I.balanceScore S.assignment a q) +
              I.maxBidForQuery q * (1 - Real.exp (-ε)) := by
        simpa [S', runHistoryStateFrom] using hhead
      calc
        msvvRatio *
            historyMaxSlackBetaSum I
              (I.msvvNormalizedAlphaFromAssignment
                (runHistoryStateFrom I I.balanceChoiceRule S (q :: qs)).assignment)
              (q :: qs)
            =
          msvvRatio *
              I.maxSlackBeta
                (I.msvvNormalizedAlphaFromAssignment
                  (runHistoryStateFrom I I.balanceChoiceRule S' qs).assignment)
                q +
            msvvRatio *
              historyMaxSlackBetaSum I
                (I.msvvNormalizedAlphaFromAssignment
                  (runHistoryStateFrom I I.balanceChoiceRule S' qs).assignment)
                qs := by
                  simp [historyMaxSlackBetaSum, runHistoryStateFrom, S',
                    mul_add]
        _ ≤
          ((match I.balanceChoiceRule S.assignment q with
            | none => 0
            | some a => I.balanceScore S.assignment a q) +
              I.maxBidForQuery q * (1 - Real.exp (-ε))) +
            (historyBalanceChargeFrom I I.balanceChoiceRule S' qs +
              historyMaxBidErrorSum I ε qs) :=
                add_le_add hhead' htail
        _ =
          historyBalanceChargeFrom I I.balanceChoiceRule S (q :: qs) +
            historyMaxBidErrorSum I ε (q :: qs) := by
                simp [historyBalanceChargeFrom, historyMaxBidErrorSum,
                  hqFresh, S', add_assoc, add_left_comm, add_comm]

theorem sum_maxSlackBeta_balanceRun_le_balanceCharge_add_maxBidError_of_cover
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    (hnodup : history.Nodup)
    (hcover : historyFinset history = Finset.univ)
    {ε : ℝ}
    (hε : 0 ≤ ε)
    (hsmall : I.SmallBids ε) :
    (∑ q : Query,
      I.maxSlackBeta
        (I.msvvAlphaFromAssignment
          (I.runAssignment I.balanceChoiceRule history)) q) ≤
      historyBalanceChargeFrom I I.balanceChoiceRule
        initialHistoryState history +
        historyMaxBidErrorSum I ε history := by
  have hnonneg : I.NonnegativeBudgets := fun a => (hbudget a).le
  have hS :
      I.StateInvariant
        (initialHistoryState : HistoryState Advertiser Query) :=
    initialHistoryState_invariant I hnonneg
  have hfresh :
      ∀ q,
        q ∈ historyFinset history →
          q ∉
            (initialHistoryState : HistoryState Advertiser Query).seen := by
    simp [initialHistoryState]
  have hhist :=
    historyMaxSlackBetaSum_balanceChoiceRun_le_balanceCharge_add_maxBidError
      I hbid hbudget history
      (initialHistoryState : HistoryState Advertiser Query)
      hS hfresh hnodup hε hsmall
  have hhist' :
      historyMaxSlackBetaSum I
          (I.msvvAlphaFromAssignment
            (I.runAssignment I.balanceChoiceRule history))
          history ≤
        historyBalanceChargeFrom I I.balanceChoiceRule
          initialHistoryState history +
          historyMaxBidErrorSum I ε history := by
    simpa [runAssignment, runHistoryState] using hhist
  rw [sum_univ_maxSlackBeta_eq_historyMaxSlackBetaSum_of_cover
    I (I.msvvAlphaFromAssignment (I.runAssignment I.balanceChoiceRule history))
    history hnodup hcover]
  exact hhist'

theorem msvvRatio_mul_sum_maxSlackBeta_normalized_balanceRun_le_balanceCharge_add_maxBidError_of_cover
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    (hnodup : history.Nodup)
    (hcover : historyFinset history = Finset.univ)
    {ε : ℝ}
    (hε : 0 ≤ ε)
    (hsmall : I.SmallBids ε) :
    msvvRatio *
      (∑ q : Query,
        I.maxSlackBeta
          (I.msvvNormalizedAlphaFromAssignment
            (I.runAssignment I.balanceChoiceRule history)) q) ≤
      historyBalanceChargeFrom I I.balanceChoiceRule
        initialHistoryState history +
        historyMaxBidErrorSum I ε history := by
  have hnonneg : I.NonnegativeBudgets := fun a => (hbudget a).le
  have hS :
      I.StateInvariant
        (initialHistoryState : HistoryState Advertiser Query) :=
    initialHistoryState_invariant I hnonneg
  have hfresh :
      ∀ q,
        q ∈ historyFinset history →
          q ∉
            (initialHistoryState : HistoryState Advertiser Query).seen := by
    simp [initialHistoryState]
  have hhist :=
    msvvRatio_mul_historyMaxSlackBetaSum_normalized_balanceChoiceRun_le_balanceCharge_add_maxBidError
      I hbid hbudget history
      (initialHistoryState : HistoryState Advertiser Query)
      hS hfresh hnodup hε hsmall
  have hhist' :
      msvvRatio *
        historyMaxSlackBetaSum I
          (I.msvvNormalizedAlphaFromAssignment
            (I.runAssignment I.balanceChoiceRule history))
          history ≤
        historyBalanceChargeFrom I I.balanceChoiceRule
          initialHistoryState history +
          historyMaxBidErrorSum I ε history := by
    simpa [runAssignment, runHistoryState] using hhist
  rw [sum_univ_maxSlackBeta_eq_historyMaxSlackBetaSum_of_cover
    I (I.msvvNormalizedAlphaFromAssignment
      (I.runAssignment I.balanceChoiceRule history)) history hnodup hcover]
  exact hhist'

theorem runHistoryState_invariant
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets)
    (rule : ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query) :
    I.StateInvariant (runHistoryState I rule history) := by
  exact runHistoryStateFrom_invariant I rule hrule history
    initialHistoryState (initialHistoryState_invariant I hbudget)

theorem runAssignment_feasible
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets)
    (rule : ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query) :
    I.Feasible (I.runAssignment rule history) := by
  exact (runHistoryState_invariant I hbudget rule hrule history).1

theorem revenue_runAssignment_eq_historyRevenueChargeFrom
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets)
    (rule : ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query) :
    I.revenue (I.runAssignment rule history) =
      I.historyRevenueChargeFrom rule initialHistoryState history := by
  have hS := initialHistoryState_invariant I hbudget
  have h :=
    revenue_runHistoryStateFrom_eq_revenue_add_historyRevenueChargeFrom
      I rule hrule history
      (initialHistoryState : HistoryState Advertiser Query) hS
  simpa [runAssignment, runHistoryState, initialHistoryState,
    revenue_emptyAssignment] using h

theorem historyBalanceChargeFrom_initial_le_runAssignment_revenue
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.NonnegativeBudgets)
    (rule : ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query) :
    I.historyBalanceChargeFrom rule initialHistoryState history ≤
      I.revenue (I.runAssignment rule history) := by
  have hS := initialHistoryState_invariant I hbudget
  have hcharge :=
    historyBalanceChargeFrom_le_historyRevenueChargeFrom
      I hbid rule hrule history
      (initialHistoryState : HistoryState Advertiser Query) hS
  rw [revenue_runAssignment_eq_historyRevenueChargeFrom I hbudget rule hrule history]
  exact hcharge

theorem runAssignment_unseen_eq_none
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets)
    (rule : ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query) {q : Query}
    (hnot : q ∉ historyFinset history) :
    I.runAssignment rule history q = none := by
  have hinv := runHistoryState_invariant I hbudget rule hrule history
  have hseen := runHistoryState_seen I rule history
  exact hinv.2 q (by simpa [hseen] using hnot)

theorem runAssignment_assigned_mem_historyFinset
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets)
    (rule : ChoiceRule Advertiser Query)
    (hrule : I.ChoiceRuleFeasible rule)
    (history : List Query) {q : Query} {a : Advertiser}
    (hassigned : I.runAssignment rule history q = some a) :
    q ∈ historyFinset history := by
  by_contra hnot
  have hnone :=
    runAssignment_unseen_eq_none I hbudget rule hrule history hnot
  rw [hassigned] at hnone
  contradiction

theorem balanceRunAssignment_feasible
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets)
    (history : List Query) :
    I.Feasible (I.runAssignment I.balanceChoiceRule history) := by
  exact runAssignment_feasible I hbudget I.balanceChoiceRule
    (balanceChoiceRule_feasible I) history

theorem balanceRunAssignment_unseen_eq_none
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets)
    (history : List Query) {q : Query}
    (hnot : q ∉ historyFinset history) :
    I.runAssignment I.balanceChoiceRule history q = none := by
  exact runAssignment_unseen_eq_none I hbudget I.balanceChoiceRule
    (balanceChoiceRule_feasible I) history hnot

theorem balanceRunAssignment_assigned_mem_historyFinset
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets)
    (history : List Query) {q : Query} {a : Advertiser}
    (hassigned : I.runAssignment I.balanceChoiceRule history q = some a) :
    q ∈ historyFinset history := by
  exact runAssignment_assigned_mem_historyFinset I hbudget I.balanceChoiceRule
    (balanceChoiceRule_feasible I) history hassigned

theorem competitive_of_certificate
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets)
    (A : Assignment Advertiser Query) (ratio : ℝ)
    (hcert : I.CompetitiveRatioCertificate A ratio) :
    ratio * I.offlineOptimumValue hbudget ≤ I.revenue A := by
  exact hcert.competitive (I.offlineOptimumAssignment hbudget)
    (offlineOptimumAssignment_isOptimal I hbudget)

theorem competitiveRatioCertificate_of_primalDual
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (A : Assignment Advertiser Query) (ratio : ℝ)
    (hcert : I.PrimalDualCompetitiveCertificate A ratio) :
    I.CompetitiveRatioCertificate A ratio := by
  refine ⟨hcert.feasible, ?_⟩
  intro Opt hOpt
  have hopt_dual :
      I.revenue Opt ≤ I.dualObjective hcert.alpha hcert.beta :=
    revenue_le_dualObjective_of_dualFeasible I Opt hcert.alpha hcert.beta
      hOpt.1 hcert.dual_feasible
  let approximation : Optimization.UpperBoundApproximationCertificate
      (I.revenue Opt) (I.revenue A) ratio :=
    ⟨I.dualObjective hcert.alpha hcert.beta, hopt_dual,
      hcert.scaled_dual_bound⟩
  exact approximation.scaled_benchmark_le_achieved hcert.ratio_nonneg

theorem competitive_of_primalDual
    [Fintype Advertiser] [Fintype Query] [DecidableEq Advertiser]
    (I : AdWordsInstance Advertiser Query)
    (hbudget : I.NonnegativeBudgets)
    (A : Assignment Advertiser Query) (ratio : ℝ)
    (hcert : I.PrimalDualCompetitiveCertificate A ratio) :
    ratio * I.offlineOptimumValue hbudget ≤ I.revenue A := by
  exact competitive_of_certificate I hbudget A ratio
    (competitiveRatioCertificate_of_primalDual I A ratio hcert)

/--
The remaining finite MSVV objective-bound seam for the concrete Balance run.
All feasibility and dual feasibility fields are already proved elsewhere; this
certificate is exactly the scaled dual-objective inequality still requiring the
charging argument.
-/
structure MsvvObjectiveBoundCertificate
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (history : List Query) : Prop where
  scaled_dual_bound :
    let A := I.runAssignment I.balanceChoiceRule history
    msvvRatio *
      I.dualObjective (I.msvvNormalizedAlphaFromAssignment A)
        (I.maxSlackBeta (I.msvvNormalizedAlphaFromAssignment A)) ≤
      I.revenue A

/-- Finite small-bids MSVV objective bound with an explicit additive error. -/
structure MsvvApproxObjectiveBoundCertificate
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (history : List Query) (error : ℝ) : Prop where
  scaled_dual_bound :
    let A := I.runAssignment I.balanceChoiceRule history
    msvvRatio *
      I.dualObjective (I.msvvNormalizedAlphaFromAssignment A)
        (I.maxSlackBeta (I.msvvNormalizedAlphaFromAssignment A)) ≤
      I.revenue A + error

/--
The remaining history-level MSVV accounting seam after the query-dual summation
lemmas. This certificate isolates the analytic/small-bids step: advertiser
duals plus recursive Balance charges plus the explicit max-bid error are
scaled by `1 - 1/e` and paid for by the run revenue.
-/
structure MsvvHistoryAccountingCertificate
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (history : List Query) (ε : ℝ) : Prop where
  nonnegative_bids : I.NonnegativeBids
  positive_budgets : I.PositiveBudgets
  history_nodup : history.Nodup
  history_covers_queries : historyFinset history = Finset.univ
  epsilon_nonneg : 0 ≤ ε
  small_bids : I.SmallBids ε
  scaled_accounting_bound :
    let A := I.runAssignment I.balanceChoiceRule history
    msvvRatio *
        (∑ a : Advertiser, I.budget a * I.msvvNormalizedAlphaFromAssignment A a) +
        I.historyBalanceChargeFrom I.balanceChoiceRule initialHistoryState history +
        I.historyMaxBidErrorSum ε history ≤
      I.revenue A

/--
Approximate history-level accounting seam for the finite small-bids analysis.
The explicit `error` absorbs the remaining advertiser-alpha discretization and
small-bids limiting terms.
-/
structure MsvvHistoryApproxAccountingCertificate
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (history : List Query) (ε error : ℝ) : Prop where
  nonnegative_bids : I.NonnegativeBids
  positive_budgets : I.PositiveBudgets
  history_nodup : history.Nodup
  history_covers_queries : historyFinset history = Finset.univ
  epsilon_nonneg : 0 ≤ ε
  small_bids : I.SmallBids ε
  scaled_accounting_bound :
    let A := I.runAssignment I.balanceChoiceRule history
    msvvRatio *
        (∑ a : Advertiser, I.budget a * I.msvvNormalizedAlphaFromAssignment A a) +
        I.historyBalanceChargeFrom I.balanceChoiceRule initialHistoryState history +
        I.historyMaxBidErrorSum ε history ≤
      I.revenue A + error

/--
Explicit finite-history approximate accounting certificate for Balance/MSVV.
The additive error is the sum of the advertiser-alpha discretization error and
the exhausted-advertiser query-dual error.
-/
theorem msvvHistoryApproxAccountingCertificate_balanceChoiceRun
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    (hnodup : history.Nodup)
    (hcover : historyFinset history = Finset.univ)
    {ε : ℝ}
    (hε : 0 ≤ ε)
    (hsmall : I.SmallBids ε) :
    I.MsvvHistoryApproxAccountingCertificate history ε
      (I.historyMaxBidAlphaErrorSum ε history +
        I.historyMaxBidErrorSum ε history) := by
  refine ⟨hbid, hbudget, hnodup, hcover, hε, hsmall, ?_⟩
  let A := I.runAssignment I.balanceChoiceRule history
  have halpha :=
    msvvRatio_mul_normalizedAlphaBudgetMass_balanceRun_add_historyBalanceCharge_le_revenue_add_historyMaxBidAlphaErrorSum
      I hbid hbudget history hε hsmall
  have halpha' :
      msvvRatio *
          (∑ a : Advertiser,
            I.budget a * I.msvvNormalizedAlphaFromAssignment A a) +
          I.historyBalanceChargeFrom I.balanceChoiceRule
            initialHistoryState history ≤
        I.revenue A + I.historyMaxBidAlphaErrorSum ε history := by
    simpa [A, msvvNormalizedAlphaBudgetMass] using halpha
  linarith

theorem msvvObjectiveBoundCertificate_of_historyAccounting
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (history : List Query) {ε : ℝ}
    (hcert : I.MsvvHistoryAccountingCertificate history ε) :
    I.MsvvObjectiveBoundCertificate history := by
  refine ⟨?_⟩
  let A := I.runAssignment I.balanceChoiceRule history
  have hquery :
      msvvRatio *
        (∑ q : Query,
          I.maxSlackBeta (I.msvvNormalizedAlphaFromAssignment A) q) ≤
        I.historyBalanceChargeFrom I.balanceChoiceRule
          initialHistoryState history +
          I.historyMaxBidErrorSum ε history := by
    simpa [A] using
      msvvRatio_mul_sum_maxSlackBeta_normalized_balanceRun_le_balanceCharge_add_maxBidError_of_cover
        I hcert.nonnegative_bids hcert.positive_budgets history
        hcert.history_nodup hcert.history_covers_queries
        hcert.epsilon_nonneg hcert.small_bids
  have hdual :
      msvvRatio *
          I.dualObjective (I.msvvNormalizedAlphaFromAssignment A)
            (I.maxSlackBeta (I.msvvNormalizedAlphaFromAssignment A)) ≤
        msvvRatio *
            (∑ a : Advertiser,
              I.budget a * I.msvvNormalizedAlphaFromAssignment A a) +
          I.historyBalanceChargeFrom I.balanceChoiceRule
            initialHistoryState history +
          I.historyMaxBidErrorSum ε history := by
    unfold dualObjective
    linarith
  exact hdual.trans (by simpa [A] using hcert.scaled_accounting_bound)

theorem msvvApproxObjectiveBoundCertificate_of_historyApproxAccounting
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (history : List Query) {ε error : ℝ}
    (hcert : I.MsvvHistoryApproxAccountingCertificate history ε error) :
    I.MsvvApproxObjectiveBoundCertificate history error := by
  refine ⟨?_⟩
  let A := I.runAssignment I.balanceChoiceRule history
  have hquery :
      msvvRatio *
        (∑ q : Query,
          I.maxSlackBeta (I.msvvNormalizedAlphaFromAssignment A) q) ≤
        I.historyBalanceChargeFrom I.balanceChoiceRule
          initialHistoryState history +
          I.historyMaxBidErrorSum ε history := by
    simpa [A] using
      msvvRatio_mul_sum_maxSlackBeta_normalized_balanceRun_le_balanceCharge_add_maxBidError_of_cover
        I hcert.nonnegative_bids hcert.positive_budgets history
        hcert.history_nodup hcert.history_covers_queries
        hcert.epsilon_nonneg hcert.small_bids
  have hdual :
      msvvRatio *
          I.dualObjective (I.msvvNormalizedAlphaFromAssignment A)
            (I.maxSlackBeta (I.msvvNormalizedAlphaFromAssignment A)) ≤
        msvvRatio *
            (∑ a : Advertiser,
              I.budget a * I.msvvNormalizedAlphaFromAssignment A a) +
          I.historyBalanceChargeFrom I.balanceChoiceRule
            initialHistoryState history +
          I.historyMaxBidErrorSum ε history := by
    unfold dualObjective
    linarith
  exact hdual.trans (by simpa [A] using hcert.scaled_accounting_bound)

theorem msvvApproxObjectiveBoundCertificate_balanceChoiceRun
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    (hnodup : history.Nodup)
    (hcover : historyFinset history = Finset.univ)
    {ε : ℝ}
    (hε : 0 ≤ ε)
    (hsmall : I.SmallBids ε) :
    I.MsvvApproxObjectiveBoundCertificate history
      (I.historyMaxBidAlphaErrorSum ε history +
        I.historyMaxBidErrorSum ε history) := by
  exact msvvApproxObjectiveBoundCertificate_of_historyApproxAccounting
    I history
    (msvvHistoryApproxAccountingCertificate_balanceChoiceRun
      I hbid hbudget history hnodup hcover hε hsmall)

noncomputable def primalDualCompetitiveCertificate_of_msvvObjectiveBound
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    (hcert : I.MsvvObjectiveBoundCertificate history) :
    I.PrimalDualCompetitiveCertificate
      (I.runAssignment I.balanceChoiceRule history) msvvRatio where
  feasible := balanceRunAssignment_feasible I (fun a => (hbudget a).le) history
  ratio_nonneg := msvvRatio_nonneg
  alpha :=
    I.msvvNormalizedAlphaFromAssignment
      (I.runAssignment I.balanceChoiceRule history)
  beta :=
    I.maxSlackBeta
      (I.msvvNormalizedAlphaFromAssignment
        (I.runAssignment I.balanceChoiceRule history))
  dual_feasible :=
    dualFeasible_msvvNormalizedAssignment I hbid hbudget
      (I.runAssignment I.balanceChoiceRule history)
  scaled_dual_bound := by
    simpa using hcert.scaled_dual_bound

theorem balance_msvv_competitive_of_objectiveBound
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    (hcert : I.MsvvObjectiveBoundCertificate history) :
    msvvRatio * I.offlineOptimumValue (fun a => (hbudget a).le) ≤
      I.revenue (I.runAssignment I.balanceChoiceRule history) := by
  exact competitive_of_primalDual I (fun a => (hbudget a).le)
    (I.runAssignment I.balanceChoiceRule history) msvvRatio
    (primalDualCompetitiveCertificate_of_msvvObjectiveBound
      I hbid hbudget history hcert)

theorem balance_msvv_approx_competitive_of_approxObjectiveBound
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List Query) {error : ℝ}
    (hcert : I.MsvvApproxObjectiveBoundCertificate history error) :
    msvvRatio * I.offlineOptimumValue (fun a => (hbudget a).le) ≤
      I.revenue (I.runAssignment I.balanceChoiceRule history) + error := by
  let A := I.runAssignment I.balanceChoiceRule history
  let alpha := I.msvvNormalizedAlphaFromAssignment A
  let beta := I.maxSlackBeta alpha
  have hdual : I.DualFeasible alpha beta := by
    simpa [alpha, beta, A] using
      dualFeasible_msvvNormalizedAssignment I hbid hbudget A
  have hopt :
      I.offlineOptimumValue (fun a => (hbudget a).le) ≤
        I.dualObjective alpha beta :=
    offlineOptimumValue_le_dualObjective_of_dualFeasible
      I (fun a => (hbudget a).le) alpha beta hdual
  have hscaled :
      msvvRatio * I.offlineOptimumValue (fun a => (hbudget a).le) ≤
        msvvRatio * I.dualObjective alpha beta :=
    mul_le_mul_of_nonneg_left hopt msvvRatio_nonneg
  exact hscaled.trans (by simpa [alpha, beta, A] using hcert.scaled_dual_bound)

theorem balance_msvv_approx_competitive_with_history_error
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    (hnodup : history.Nodup)
    (hcover : historyFinset history = Finset.univ)
    {ε : ℝ}
    (hε : 0 ≤ ε)
    (hsmall : I.SmallBids ε) :
    msvvRatio * I.offlineOptimumValue (fun a => (hbudget a).le) ≤
      I.revenue (I.runAssignment I.balanceChoiceRule history) +
        (I.historyMaxBidAlphaErrorSum ε history +
          I.historyMaxBidErrorSum ε history) := by
  exact balance_msvv_approx_competitive_of_approxObjectiveBound
    I hbid hbudget history
    (msvvApproxObjectiveBoundCertificate_balanceChoiceRun
      I hbid hbudget history hnodup hcover hε hsmall)

theorem balance_msvv_approx_competitive_with_error_bound
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    (hnodup : history.Nodup)
    (hcover : historyFinset history = Finset.univ)
    {ε : ℝ}
    (hε : 0 ≤ ε)
    (hε_le_one : ε ≤ 1)
    (hsmall : I.SmallBids ε) :
    msvvRatio * I.offlineOptimumValue (fun a => (hbudget a).le) ≤
      I.revenue (I.runAssignment I.balanceChoiceRule history) +
        ε * (Real.exp 1 + 1) * I.historyMaxBidSum history := by
  have hbase :=
    balance_msvv_approx_competitive_with_history_error
      I hbid hbudget history hnodup hcover hε hsmall
  have hbase' :
      msvvRatio * I.offlineOptimumValue (fun a => (hbudget a).le) ≤
        I.revenue (I.runAssignment I.balanceChoiceRule history) +
          I.historyMsvvSmallBidsErrorSum ε history := by
    simpa [historyMsvvSmallBidsErrorSum] using hbase
  have herror :=
    historyMsvvSmallBidsErrorSum_le_epsilon_mul_exp_one_add_one_mul_historyMaxBidSum
      I history hε hε_le_one
  have hbound :
      I.revenue (I.runAssignment I.balanceChoiceRule history) +
          I.historyMsvvSmallBidsErrorSum ε history ≤
        I.revenue (I.runAssignment I.balanceChoiceRule history) +
          ε * (Real.exp 1 + 1) * I.historyMaxBidSum history := by
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left herror
          (I.revenue (I.runAssignment I.balanceChoiceRule history))
  exact hbase'.trans hbound

theorem balance_msvv_approx_competitive_with_query_sum_error_bound
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    (hnodup : history.Nodup)
    (hcover : historyFinset history = Finset.univ)
    {ε : ℝ}
    (hε : 0 ≤ ε)
    (hε_le_one : ε ≤ 1)
    (hsmall : I.SmallBids ε) :
    msvvRatio * I.offlineOptimumValue (fun a => (hbudget a).le) ≤
      I.revenue (I.runAssignment I.balanceChoiceRule history) +
        ε * (Real.exp 1 + 1) *
          (∑ q : Query, I.maxBidForQuery q) := by
  have hbase :=
    balance_msvv_approx_competitive_with_error_bound
      I hbid hbudget history hnodup hcover hε hε_le_one hsmall
  have hsum :=
    sum_univ_maxBidForQuery_eq_historyMaxBidSum_of_cover
      I history hnodup hcover
  rw [hsum]
  exact hbase

theorem balance_msvv_approx_competitive_finRange_with_query_sum_error_bound
    [Fintype Advertiser] [Nonempty Advertiser] [DecidableEq Advertiser]
    {n : ℕ}
    (I : AdWordsInstance Advertiser (Fin n))
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    {ε : ℝ}
    (hε : 0 ≤ ε)
    (hε_le_one : ε ≤ 1)
    (hsmall : I.SmallBids ε) :
    msvvRatio * I.offlineOptimumValue (fun a => (hbudget a).le) ≤
      I.revenue (I.runAssignment I.balanceChoiceRule (List.finRange n)) +
        ε * (Real.exp 1 + 1) *
          (∑ q : Fin n, I.maxBidForQuery q) := by
  exact balance_msvv_approx_competitive_with_query_sum_error_bound
    I hbid hbudget (List.finRange n) (finRange_history_nodup n)
    (historyFinset_finRange n) hε hε_le_one hsmall

theorem balance_msvv_approx_competitive_up_to_delta
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    (hnodup : history.Nodup)
    (hcover : historyFinset history = Finset.univ)
    {ε δ : ℝ}
    (hε : 0 ≤ ε)
    (hε_le_one : ε ≤ 1)
    (hsmall : I.SmallBids ε)
    (herror_le_delta :
      ε * (Real.exp 1 + 1) * I.historyMaxBidSum history ≤ δ) :
    msvvRatio * I.offlineOptimumValue (fun a => (hbudget a).le) ≤
      I.revenue (I.runAssignment I.balanceChoiceRule history) + δ := by
  have hbase :=
    balance_msvv_approx_competitive_with_error_bound
      I hbid hbudget history hnodup hcover hε hε_le_one hsmall
  have hbound :
      I.revenue (I.runAssignment I.balanceChoiceRule history) +
          ε * (Real.exp 1 + 1) * I.historyMaxBidSum history ≤
        I.revenue (I.runAssignment I.balanceChoiceRule history) + δ :=
    by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left herror_le_delta
          (I.revenue (I.runAssignment I.balanceChoiceRule history))
  exact hbase.trans hbound

theorem balance_msvv_approx_competitive_finRange_up_to_delta
    [Fintype Advertiser] [Nonempty Advertiser] [DecidableEq Advertiser]
    {n : ℕ}
    (I : AdWordsInstance Advertiser (Fin n))
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    {ε δ : ℝ}
    (hε : 0 ≤ ε)
    (hε_le_one : ε ≤ 1)
    (hsmall : I.SmallBids ε)
    (herror_le_delta :
      ε * (Real.exp 1 + 1) *
          (∑ q : Fin n, I.maxBidForQuery q) ≤ δ) :
    msvvRatio * I.offlineOptimumValue (fun a => (hbudget a).le) ≤
      I.revenue (I.runAssignment I.balanceChoiceRule (List.finRange n)) +
        δ := by
  have hbase :=
    balance_msvv_approx_competitive_finRange_with_query_sum_error_bound
      I hbid hbudget hε hε_le_one hsmall
  have hbound :
      I.revenue (I.runAssignment I.balanceChoiceRule (List.finRange n)) +
          ε * (Real.exp 1 + 1) *
            (∑ q : Fin n, I.maxBidForQuery q) ≤
        I.revenue (I.runAssignment I.balanceChoiceRule (List.finRange n)) +
          δ :=
    by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left herror_le_delta
          (I.revenue (I.runAssignment I.balanceChoiceRule (List.finRange n)))
  exact hbase.trans hbound

theorem balance_msvv_approx_competitive_up_to_delta_of_smallBids_threshold
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    (hnodup : history.Nodup)
    (hcover : historyFinset history = Finset.univ)
    {δ : ℝ}
    (hδ : 0 ≤ δ)
    (hmaxBidSum_pos : 0 < I.historyMaxBidSum history)
    (hsmall :
      I.SmallBids
        (min 1
          (δ / ((Real.exp 1 + 1) * I.historyMaxBidSum history)))) :
    msvvRatio * I.offlineOptimumValue (fun a => (hbudget a).le) ≤
      I.revenue (I.runAssignment I.balanceChoiceRule history) + δ := by
  let ε :=
    min 1 (δ / ((Real.exp 1 + 1) * I.historyMaxBidSum history))
  let scale := (Real.exp 1 + 1) * I.historyMaxBidSum history
  have hcoef_pos : 0 < Real.exp 1 + 1 := by
    have hexp_pos : 0 < Real.exp 1 := Real.exp_pos 1
    linarith
  have hscale_pos : 0 < scale := by
    exact mul_pos hcoef_pos hmaxBidSum_pos
  have hε_nonneg : 0 ≤ ε := by
    unfold ε
    exact le_min zero_le_one (div_nonneg hδ hscale_pos.le)
  have hε_le_one : ε ≤ 1 := by
    unfold ε
    exact min_le_left 1 (δ / scale)
  have hε_le_threshold : ε ≤ δ / scale := by
    unfold ε
    exact min_le_right 1 (δ / scale)
  have herror_le_delta :
      ε * (Real.exp 1 + 1) * I.historyMaxBidSum history ≤ δ := by
    have hmul :=
      mul_le_mul_of_nonneg_right hε_le_threshold hscale_pos.le
    calc
      ε * (Real.exp 1 + 1) * I.historyMaxBidSum history =
          ε * scale := by
          simp [scale]
          ring
      _ ≤ (δ / scale) * scale := hmul
      _ = δ := by
          exact div_mul_cancel₀ δ hscale_pos.ne'
  exact balance_msvv_approx_competitive_up_to_delta
    I hbid hbudget history hnodup hcover hε_nonneg hε_le_one hsmall
    herror_le_delta

theorem balance_msvv_approx_competitive_finRange_up_to_delta_of_smallBids_threshold
    [Fintype Advertiser] [Nonempty Advertiser] [DecidableEq Advertiser]
    {n : ℕ}
    (I : AdWordsInstance Advertiser (Fin n))
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    {δ : ℝ}
    (hδ : 0 ≤ δ)
    (hmaxBidSum_pos : 0 < ∑ q : Fin n, I.maxBidForQuery q)
    (hsmall :
      I.SmallBids
        (min 1
          (δ / ((Real.exp 1 + 1) *
            (∑ q : Fin n, I.maxBidForQuery q))))) :
    msvvRatio * I.offlineOptimumValue (fun a => (hbudget a).le) ≤
      I.revenue (I.runAssignment I.balanceChoiceRule (List.finRange n)) +
        δ := by
  let ε :=
    min 1
      (δ / ((Real.exp 1 + 1) *
        (∑ q : Fin n, I.maxBidForQuery q)))
  let scale := (Real.exp 1 + 1) * (∑ q : Fin n, I.maxBidForQuery q)
  have hcoef_pos : 0 < Real.exp 1 + 1 := by
    have hexp_pos : 0 < Real.exp 1 := Real.exp_pos 1
    linarith
  have hscale_pos : 0 < scale := by
    exact mul_pos hcoef_pos hmaxBidSum_pos
  have hε_nonneg : 0 ≤ ε := by
    unfold ε
    exact le_min zero_le_one (div_nonneg hδ hscale_pos.le)
  have hε_le_one : ε ≤ 1 := by
    unfold ε
    exact min_le_left 1 (δ / scale)
  have hε_le_threshold : ε ≤ δ / scale := by
    unfold ε
    exact min_le_right 1 (δ / scale)
  have herror_le_delta :
      ε * (Real.exp 1 + 1) *
          (∑ q : Fin n, I.maxBidForQuery q) ≤ δ := by
    have hmul :=
      mul_le_mul_of_nonneg_right hε_le_threshold hscale_pos.le
    calc
      ε * (Real.exp 1 + 1) * (∑ q : Fin n, I.maxBidForQuery q) =
          ε * scale := by
          simp [scale]
          ring
      _ ≤ (δ / scale) * scale := hmul
      _ = δ := by
          exact div_mul_cancel₀ δ hscale_pos.ne'
  exact balance_msvv_approx_competitive_finRange_up_to_delta
    I hbid hbudget hε_nonneg hε_le_one hsmall herror_le_delta

theorem balance_msvv_competitive_of_arbitrarily_smallBids_threshold
    [Fintype Advertiser] [Nonempty Advertiser]
    [Fintype Query] [DecidableEq Advertiser] [DecidableEq Query]
    (I : AdWordsInstance Advertiser Query)
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (history : List Query)
    (hnodup : history.Nodup)
    (hcover : historyFinset history = Finset.univ)
    (hmaxBidSum_pos : 0 < I.historyMaxBidSum history)
    (hsmall :
      ∀ δ : ℝ, 0 < δ →
        I.SmallBids
          (min 1
            (δ / ((Real.exp 1 + 1) * I.historyMaxBidSum history)))) :
    msvvRatio * I.offlineOptimumValue (fun a => (hbudget a).le) ≤
      I.revenue (I.runAssignment I.balanceChoiceRule history) := by
  let lhs := msvvRatio * I.offlineOptimumValue (fun a => (hbudget a).le)
  let rhs := I.revenue (I.runAssignment I.balanceChoiceRule history)
  by_contra hnot
  have hlt : rhs < lhs := lt_of_not_ge hnot
  let δ := (lhs - rhs) / 2
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    linarith
  have happrox :
      lhs ≤ rhs + δ := by
    simpa [lhs, rhs] using
      balance_msvv_approx_competitive_up_to_delta_of_smallBids_threshold
        I hbid hbudget history hnodup hcover hδ_pos.le hmaxBidSum_pos
        (hsmall δ hδ_pos)
  have hgap : rhs + δ < lhs := by
    dsimp [δ]
    linarith
  exact (not_lt_of_ge happrox) hgap

theorem balance_msvv_finRange_competitive_of_arbitrarily_smallBids_threshold
    [Fintype Advertiser] [Nonempty Advertiser] [DecidableEq Advertiser]
    {n : ℕ}
    (I : AdWordsInstance Advertiser (Fin n))
    (hbid : I.NonnegativeBids)
    (hbudget : I.PositiveBudgets)
    (hmaxBidSum_pos : 0 < ∑ q : Fin n, I.maxBidForQuery q)
    (hsmall :
      ∀ δ : ℝ, 0 < δ →
        I.SmallBids
          (min 1
            (δ / ((Real.exp 1 + 1) *
              (∑ q : Fin n, I.maxBidForQuery q))))) :
    msvvRatio * I.offlineOptimumValue (fun a => (hbudget a).le) ≤
      I.revenue (I.runAssignment I.balanceChoiceRule (List.finRange n)) := by
  let lhs := msvvRatio * I.offlineOptimumValue (fun a => (hbudget a).le)
  let rhs := I.revenue (I.runAssignment I.balanceChoiceRule (List.finRange n))
  by_contra hnot
  have hlt : rhs < lhs := lt_of_not_ge hnot
  let δ := (lhs - rhs) / 2
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    linarith
  have happrox :
      lhs ≤ rhs + δ := by
    simpa [lhs, rhs] using
      balance_msvv_approx_competitive_finRange_up_to_delta_of_smallBids_threshold
        I hbid hbudget hδ_pos.le hmaxBidSum_pos (hsmall δ hδ_pos)
  have hgap : rhs + δ < lhs := by
    dsimp [δ]
    linarith
  exact (not_lt_of_ge happrox) hgap

theorem balance_msvv_finRange_family_eventually_up_to_delta
    [Fintype Advertiser] [Nonempty Advertiser] [DecidableEq Advertiser]
    (n : ℕ → ℕ)
    (I : (k : ℕ) → AdWordsInstance Advertiser (Fin (n k)))
    (ε : ℕ → ℝ)
    (hbid : ∀ k, (I k).NonnegativeBids)
    (hbudget : ∀ k, (I k).PositiveBudgets)
    (hε : ∀ k, 0 ≤ ε k)
    (hε_le_one : ∀ k, ε k ≤ 1)
    (hsmall : ∀ k, (I k).SmallBids (ε k))
    (herror_eventually :
      ∀ δ : ℝ, 0 < δ →
        ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
          ε k * (Real.exp 1 + 1) *
              (∑ q : Fin (n k), (I k).maxBidForQuery q) ≤ δ) :
    ∀ δ : ℝ, 0 < δ →
      ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
        msvvRatio *
            (I k).offlineOptimumValue (fun a => (hbudget k a).le) ≤
          (I k).revenue
              ((I k).runAssignment (I k).balanceChoiceRule
                (List.finRange (n k))) +
            δ := by
  intro δ hδ
  obtain ⟨N, hN⟩ := herror_eventually δ hδ
  refine ⟨N, ?_⟩
  intro k hk
  exact balance_msvv_approx_competitive_finRange_up_to_delta
    (I k) (hbid k) (hbudget k) (hε k) (hε_le_one k) (hsmall k)
    (hN k hk)

theorem balance_msvv_finRange_family_eventually_up_to_delta_of_smallBids_threshold
    [Fintype Advertiser] [Nonempty Advertiser] [DecidableEq Advertiser]
    (n : ℕ → ℕ)
    (I : (k : ℕ) → AdWordsInstance Advertiser (Fin (n k)))
    (hbid : ∀ k, (I k).NonnegativeBids)
    (hbudget : ∀ k, (I k).PositiveBudgets)
    (hmaxBidSum_pos :
      ∀ k, 0 < ∑ q : Fin (n k), (I k).maxBidForQuery q)
    (hsmall_eventually :
      ∀ δ : ℝ, 0 < δ →
        ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
          (I k).SmallBids
            (min 1
              (δ / ((Real.exp 1 + 1) *
                (∑ q : Fin (n k), (I k).maxBidForQuery q))))) :
    ∀ δ : ℝ, 0 < δ →
      ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
        msvvRatio *
            (I k).offlineOptimumValue (fun a => (hbudget k a).le) ≤
          (I k).revenue
              ((I k).runAssignment (I k).balanceChoiceRule
                (List.finRange (n k))) +
            δ := by
  intro δ hδ
  obtain ⟨N, hN⟩ := hsmall_eventually δ hδ
  refine ⟨N, ?_⟩
  intro k hk
  exact
    balance_msvv_approx_competitive_finRange_up_to_delta_of_smallBids_threshold
      (I k) (hbid k) (hbudget k) hδ.le (hmaxBidSum_pos k) (hN k hk)

theorem balance_msvv_finRange_family_limit_competitive_of_error_eventually
    [Fintype Advertiser] [Nonempty Advertiser] [DecidableEq Advertiser]
    (n : ℕ → ℕ)
    (I : (k : ℕ) → AdWordsInstance Advertiser (Fin (n k)))
    (ε : ℕ → ℝ)
    (hbid : ∀ k, (I k).NonnegativeBids)
    (hbudget : ∀ k, (I k).PositiveBudgets)
    (hε : ∀ k, 0 ≤ ε k)
    (hε_le_one : ∀ k, ε k ≤ 1)
    (hsmall : ∀ k, (I k).SmallBids (ε k))
    (herror_eventually :
      ∀ δ : ℝ, 0 < δ →
        ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
          ε k * (Real.exp 1 + 1) *
              (∑ q : Fin (n k), (I k).maxBidForQuery q) ≤ δ)
    {scaledOptLimit revenueLimit : ℝ}
    (hscaledOpt :
      Sequence.SeqTendsTo
        (fun k =>
          msvvRatio *
            (I k).offlineOptimumValue (fun a => (hbudget k a).le))
        scaledOptLimit)
    (hrevenue :
      Sequence.SeqTendsTo
        (fun k =>
          (I k).revenue
            ((I k).runAssignment (I k).balanceChoiceRule
              (List.finRange (n k))))
        revenueLimit) :
    scaledOptLimit ≤ revenueLimit := by
  exact Sequence.le_of_seqTendsTo_eventually_le_add hscaledOpt hrevenue
    (balance_msvv_finRange_family_eventually_up_to_delta
      n I ε hbid hbudget hε hε_le_one hsmall herror_eventually)

theorem balance_msvv_finRange_family_limit_competitive_of_smallBids_threshold
    [Fintype Advertiser] [Nonempty Advertiser] [DecidableEq Advertiser]
    (n : ℕ → ℕ)
    (I : (k : ℕ) → AdWordsInstance Advertiser (Fin (n k)))
    (hbid : ∀ k, (I k).NonnegativeBids)
    (hbudget : ∀ k, (I k).PositiveBudgets)
    (hmaxBidSum_pos :
      ∀ k, 0 < ∑ q : Fin (n k), (I k).maxBidForQuery q)
    (hsmall_eventually :
      ∀ δ : ℝ, 0 < δ →
        ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
          (I k).SmallBids
            (min 1
              (δ / ((Real.exp 1 + 1) *
                (∑ q : Fin (n k), (I k).maxBidForQuery q)))))
    {scaledOptLimit revenueLimit : ℝ}
    (hscaledOpt :
      Sequence.SeqTendsTo
        (fun k =>
          msvvRatio *
            (I k).offlineOptimumValue (fun a => (hbudget k a).le))
        scaledOptLimit)
    (hrevenue :
      Sequence.SeqTendsTo
        (fun k =>
          (I k).revenue
            ((I k).runAssignment (I k).balanceChoiceRule
              (List.finRange (n k))))
        revenueLimit) :
    scaledOptLimit ≤ revenueLimit := by
  exact Sequence.le_of_seqTendsTo_eventually_le_add hscaledOpt hrevenue
    (balance_msvv_finRange_family_eventually_up_to_delta_of_smallBids_threshold
      n I hbid hbudget hmaxBidSum_pos hsmall_eventually)

theorem balance_msvv_finRange_family_limit_competitive_of_error_eventually_of_offlineOpt_convergence
    [Fintype Advertiser] [Nonempty Advertiser] [DecidableEq Advertiser]
    (n : ℕ → ℕ)
    (I : (k : ℕ) → AdWordsInstance Advertiser (Fin (n k)))
    (ε : ℕ → ℝ)
    (hbid : ∀ k, (I k).NonnegativeBids)
    (hbudget : ∀ k, (I k).PositiveBudgets)
    (hε : ∀ k, 0 ≤ ε k)
    (hε_le_one : ∀ k, ε k ≤ 1)
    (hsmall : ∀ k, (I k).SmallBids (ε k))
    (herror_eventually :
      ∀ δ : ℝ, 0 < δ →
        ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
          ε k * (Real.exp 1 + 1) *
              (∑ q : Fin (n k), (I k).maxBidForQuery q) ≤ δ)
    {optLimit revenueLimit : ℝ}
    (hopt :
      Sequence.SeqTendsTo
        (fun k => (I k).offlineOptimumValue (fun a => (hbudget k a).le))
        optLimit)
    (hrevenue :
      Sequence.SeqTendsTo
        (fun k =>
          (I k).revenue
            ((I k).runAssignment (I k).balanceChoiceRule
              (List.finRange (n k))))
        revenueLimit) :
    msvvRatio * optLimit ≤ revenueLimit := by
  exact
    balance_msvv_finRange_family_limit_competitive_of_error_eventually
      n I ε hbid hbudget hε hε_le_one hsmall herror_eventually
      (Sequence.SeqTendsTo.const_mul_of_nonneg hopt msvvRatio_nonneg)
      hrevenue

theorem balance_msvv_finRange_family_limit_competitive_of_smallBids_threshold_of_offlineOpt_convergence
    [Fintype Advertiser] [Nonempty Advertiser] [DecidableEq Advertiser]
    (n : ℕ → ℕ)
    (I : (k : ℕ) → AdWordsInstance Advertiser (Fin (n k)))
    (hbid : ∀ k, (I k).NonnegativeBids)
    (hbudget : ∀ k, (I k).PositiveBudgets)
    (hmaxBidSum_pos :
      ∀ k, 0 < ∑ q : Fin (n k), (I k).maxBidForQuery q)
    (hsmall_eventually :
      ∀ δ : ℝ, 0 < δ →
        ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
          (I k).SmallBids
            (min 1
              (δ / ((Real.exp 1 + 1) *
                (∑ q : Fin (n k), (I k).maxBidForQuery q)))))
    {optLimit revenueLimit : ℝ}
    (hopt :
      Sequence.SeqTendsTo
        (fun k => (I k).offlineOptimumValue (fun a => (hbudget k a).le))
        optLimit)
    (hrevenue :
      Sequence.SeqTendsTo
        (fun k =>
          (I k).revenue
            ((I k).runAssignment (I k).balanceChoiceRule
              (List.finRange (n k))))
        revenueLimit) :
    msvvRatio * optLimit ≤ revenueLimit := by
  exact
    balance_msvv_finRange_family_limit_competitive_of_smallBids_threshold
      n I hbid hbudget hmaxBidSum_pos hsmall_eventually
      (Sequence.SeqTendsTo.const_mul_of_nonneg hopt msvvRatio_nonneg)
      hrevenue

/--
Small-bids limiting family for Balance/MSVV.

The limiting theorem is not a statement about one fixed finite instance; it is
a statement about a sequence of finite instances in which bids become small
relative to budgets. This structure packages exactly the finite query model,
positivity assumptions, small-bids threshold, and convergence hypotheses needed
by the formal limiting theorem.
-/
structure MsvvSmallBidsLimitFamily
    (Advertiser : Type*) [Fintype Advertiser] [Nonempty Advertiser]
    [DecidableEq Advertiser] where
  queryCount : ℕ → ℕ
  instanceAt : (k : ℕ) → AdWordsInstance Advertiser (Fin (queryCount k))
  optLimit : ℝ
  revenueLimit : ℝ
  nonnegative_bids : ∀ k, (instanceAt k).NonnegativeBids
  positive_budgets : ∀ k, (instanceAt k).PositiveBudgets
  maxBidSum_pos :
    ∀ k, 0 < ∑ q : Fin (queryCount k), (instanceAt k).maxBidForQuery q
  small_bids_eventually :
    ∀ δ : ℝ, 0 < δ →
      ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
        (instanceAt k).SmallBids
          (min 1
            (δ / ((Real.exp 1 + 1) *
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

theorem balance_msvv_competitive_of_smallBidsLimitFamily
    [Fintype Advertiser] [Nonempty Advertiser] [DecidableEq Advertiser]
    (F : MsvvSmallBidsLimitFamily Advertiser) :
    msvvRatio * F.optLimit ≤ F.revenueLimit := by
  exact
    balance_msvv_finRange_family_limit_competitive_of_smallBids_threshold_of_offlineOpt_convergence
      F.queryCount F.instanceAt F.nonnegative_bids F.positive_budgets
      F.maxBidSum_pos F.small_bids_eventually F.offlineOptimum_tendsTo
      F.revenue_tendsTo

end AdWordsInstance

end Online
end AppliedModelingLib

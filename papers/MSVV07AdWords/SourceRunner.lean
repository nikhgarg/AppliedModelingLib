import MSVV07AdWords.AuditInterface
import Mathlib.Tactic

/-!
# Source-faithful runners and accounting objects for MSVV07

The reusable `AdWordsInstance.runAssignment` runner uses query identifiers as
assignment keys.  That is the right model when a finite query set is enumerated
once, but Sections 2--6 of MSVV07 describe a *sequence of occurrences* in which
the same query word may appear many times.  This file therefore gives each list
position its own decision record.  It also threads the feasibility-test and
score-comparison counts through the finite maximum scan that actually chooses
the advertiser.

The cost claims below use the paper's natural unit-cost exact-real oracle model:
one bid/budget feasibility test and one real score comparison each cost one.
They do not claim bit complexity for evaluating `Real.exp`.
-/

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

open scoped BigOperators Topology
open Filter

namespace AppliedModelingLib
namespace Online
namespace MSVV07PaperFacing
namespace SourceRunner

variable {Advertiser Query : Type*}

/-! ## Sections 2--3: source definitions -/

/--
Re-index a concrete arrival list by its positions.  This is the faithful
finite query universe for MSVV's online model: two equal query *words* at
different times become distinct `Fin history.length` occurrences while retain
their original bid vector.  It is deliberately not a deduplication.
-/
def occurrenceIndexedInstance
    (I : PaperInstance Advertiser Query) (history : List Query) :
    PaperInstance Advertiser (Fin history.length) where
  budget := I.budget
  bid a t := I.bid a (history.get t)

@[simp]
theorem occurrenceIndexedInstance_budget
    (I : PaperInstance Advertiser Query) (history : List Query) (a : Advertiser) :
    (occurrenceIndexedInstance I history).budget a = I.budget a :=
  rfl

@[simp]
theorem occurrenceIndexedInstance_bid
    (I : PaperInstance Advertiser Query) (history : List Query)
    (a : Advertiser) (t : Fin history.length) :
    (occurrenceIndexedInstance I history).bid a t = I.bid a (history.get t) :=
  rfl

theorem occurrenceIndexedInstance_nonnegativeBids
    (I : PaperInstance Advertiser Query) (history : List Query)
    (hbid : I.NonnegativeBids) :
    (occurrenceIndexedInstance I history).NonnegativeBids := by
  intro a t
  exact hbid a (history.get t)

theorem occurrenceIndexedInstance_positiveBudgets
    (I : PaperInstance Advertiser Query) (history : List Query)
    (hbudget : I.PositiveBudgets) :
    (occurrenceIndexedInstance I history).PositiveBudgets := by
  intro a
  simpa using hbudget a

theorem occurrenceIndexedInstance_smallBids
    (I : PaperInstance Advertiser Query) (history : List Query) {epsilon : ℝ}
    (hsmall : paperSmallBids I epsilon) :
    paperSmallBids (occurrenceIndexedInstance I history) epsilon := by
  intro a t
  simpa using hsmall a (history.get t)

/--
Section 6 delayed entry, represented on a concrete arrival sequence.  An
advertiser is unavailable before its one entry time and remains available from
then on; this deliberately rules out disappearance and re-entry.
-/
def availableFromEntry {n : ℕ}
    (entryTime : Advertiser → Fin (n + 1)) :
    Advertiser → Fin n → Prop :=
  fun a t => entryTime a ≤ t.castSucc

/-- Section 2's ratio definition, including its universal quantifier over inputs. -/
def IsAlphaCompetitive {Instance : Type*}
    (onlineRevenue offlineRevenue : Instance → ℝ) (α : ℝ) : Prop :=
  ∀ I, α ≤ onlineRevenue I / offlineRevenue I

/-- The temporary Section 2 normalization that every advertiser budget is one. -/
def EqualUnitBudgets {Advertiser Query : Type*}
    (I : PaperInstance Advertiser Query) : Prop :=
  ∀ a, I.budget a = 1

/-- The temporary Section 2 assumption that the chosen offline allocation exhausts all budgets. -/
def ExhaustsEveryBudget
    {Advertiser Query : Type*} [Fintype Query] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query) : Prop :=
  ∀ a, paperSpend I A a = I.budget a

/-- Section 3's finite tradeoff, with Lean index `i` representing source slab `i+1`. -/
noncomputable def discreteTradeoff (k : ℕ) (i : Fin k) : ℝ :=
  1 - Real.exp (-(1 - (((i.val + 1 : ℕ) : ℝ) / (k : ℝ))))

/-- The displayed finite tradeoff is antitone in the slab number. -/
theorem discreteTradeoff_antitone (k : ℕ) :
    Antitone (discreteTradeoff k) := by
  intro i j hij
  have hkNat : 0 < k := Nat.zero_lt_of_lt i.isLt
  have hk : 0 < (k : ℝ) := by exact_mod_cast hkNat
  have hijNat : i.val + 1 ≤ j.val + 1 := Nat.add_le_add_right hij 1
  have hijReal : ((i.val + 1 : ℕ) : ℝ) ≤ ((j.val + 1 : ℕ) : ℝ) := by
    exact_mod_cast hijNat
  have hfrac :
      ((i.val + 1 : ℕ) : ℝ) / (k : ℝ) ≤
        ((j.val + 1 : ℕ) : ℝ) / (k : ℝ) :=
    (div_le_div_iff_of_pos_right hk).2 hijReal
  have hexp :
      Real.exp (-(1 - (((i.val + 1 : ℕ) : ℝ) / (k : ℝ)))) ≤
        Real.exp (-(1 - (((j.val + 1 : ℕ) : ℝ) / (k : ℝ)))) :=
    Real.exp_le_exp.mpr (by linarith)
  unfold discreteTradeoff
  linarith

/-- The finite tradeoff is strictly decreasing on its finite slab domain. -/
theorem discreteTradeoff_strictAnti (k : ℕ) :
    StrictAnti (discreteTradeoff k) := by
  intro i j hij
  have hkNat : 0 < k := Nat.zero_lt_of_lt i.isLt
  have hk : 0 < (k : ℝ) := by exact_mod_cast hkNat
  have hijNat : i.val + 1 < j.val + 1 := Nat.add_lt_add_right hij 1
  have hijReal : ((i.val + 1 : ℕ) : ℝ) < ((j.val + 1 : ℕ) : ℝ) := by
    exact_mod_cast hijNat
  have hfrac :
      ((i.val + 1 : ℕ) : ℝ) / (k : ℝ) <
        ((j.val + 1 : ℕ) : ℝ) / (k : ℝ) :=
    (div_lt_div_iff_of_pos_right hk).2 hijReal
  have hexp :
      Real.exp (-(1 - (((i.val + 1 : ℕ) : ℝ) / (k : ℝ)))) <
        Real.exp (-(1 - (((j.val + 1 : ℕ) : ℝ) / (k : ℝ)))) :=
    Real.exp_lt_exp.mpr (by linarith)
  unfold discreteTradeoff
  linarith

/--
Source-shaped convergence bridge.  Whenever the fractions represented by a
sequence of one-indexed slabs converge to `s`, their finite weights converge to
the continuous Section 3 weight at `s`.
-/
theorem discreteTradeoff_converges_along_slab_fractions
    (slab : ℕ → ℕ) (s : ℝ)
    (hfraction :
      Tendsto (fun k : ℕ => ((slab k + 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ))
        atTop (nhds s)) :
    Sequence.SeqTendsTo
      (fun k : ℕ =>
        1 - Real.exp
          (-(1 - (((slab k + 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ)))))
      (1 - Real.exp (-(1 - s))) := by
  apply MSVV07SourceLemmas.seqTendsTo_of_tendsto
  have hcontinuous : Continuous (fun x : ℝ => 1 - Real.exp (-(1 - x))) := by
    fun_prop
  exact hcontinuous.continuousAt.tendsto.comp hfraction

/-! ## Section 3 greedy tight example in the paper's small-bid fluid scaling -/

/-- Aggregate revenues of the explicit two-bidder, two-word greedy example. -/
structure GreedyTwoWordFluidOutcome where
  greedyFirstPhase : ℝ
  greedySecondPhase : ℝ
  offlineFirstPhase : ℝ
  offlineSecondPhase : ℝ

/--
The first word has bids `c` and `c+epsilon` and total mass `1/(c+epsilon)`;
the second has bids `0` and `c` and total mass `1/c`.
-/
noncomputable def greedyTwoWordFluidOutcome (c epsilon : ℝ) :
    GreedyTwoWordFluidOutcome where
  greedyFirstPhase := (c + epsilon) * (1 / (c + epsilon))
  greedySecondPhase := 0
  offlineFirstPhase := c * (1 / (c + epsilon))
  offlineSecondPhase := c * (1 / c)

/-- Total online revenue in the fluid example. -/
noncomputable def greedyTwoWordOnlineRevenue (c epsilon : ℝ) : ℝ :=
  (greedyTwoWordFluidOutcome c epsilon).greedyFirstPhase +
    (greedyTwoWordFluidOutcome c epsilon).greedySecondPhase

/-- Revenue of the source's cross-phase offline assignment. -/
noncomputable def greedyTwoWordOfflineRevenue (c epsilon : ℝ) : ℝ :=
  (greedyTwoWordFluidOutcome c epsilon).offlineFirstPhase +
    (greedyTwoWordFluidOutcome c epsilon).offlineSecondPhase

/--
Construction-level calculation: greedy exhausts bidder two in phase one,
earns nothing in phase two, while the cross-phase offline assignment is
budget-feasible and obtains the displayed larger revenue.
-/
theorem greedyTwoWordFluidOutcome_fields
    {c epsilon : ℝ} (hc : 0 < c) (hepsilon : 0 < epsilon) :
    c < c + epsilon ∧
      greedyTwoWordOnlineRevenue c epsilon = 1 ∧
      greedyTwoWordOfflineRevenue c epsilon = 1 + c / (c + epsilon) ∧
      c / (c + epsilon) ≤ 1 ∧
      greedyTwoWordOnlineRevenue c epsilon /
          greedyTwoWordOfflineRevenue c epsilon =
        (c + epsilon) / (2 * c + epsilon) := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have hsum : 0 < c + epsilon := by linarith
  have hsumne : c + epsilon ≠ 0 := ne_of_gt hsum
  have hden : 0 < 2 * c + epsilon := by linarith
  refine ⟨by linarith, ?_, ?_, ?_, ?_⟩
  · unfold greedyTwoWordOnlineRevenue greedyTwoWordFluidOutcome
    field_simp [hsumne]
    norm_num
  · unfold greedyTwoWordOfflineRevenue greedyTwoWordFluidOutcome
    field_simp [hcne, hsumne]
    ring
  · exact (div_le_one hsum).2 (by linarith)
  · rw [show greedyTwoWordOnlineRevenue c epsilon = 1 by
      unfold greedyTwoWordOnlineRevenue greedyTwoWordFluidOutcome
      field_simp [hsumne]
      norm_num]
    rw [show greedyTwoWordOfflineRevenue c epsilon =
        1 + c / (c + epsilon) by
      unfold greedyTwoWordOfflineRevenue greedyTwoWordFluidOutcome
      field_simp [hcne, hsumne]
      ring]
    field_simp [hsumne, ne_of_gt hden]
    ring

/--
The active zero-based slab for a nonnegative spent fraction.  The `min` maps a
fully spent bidder to the last slab; source slab numbers are this value plus one.
-/
noncomputable def activeSlab
    (k : ℕ) (hk : 0 < k) (spentFraction : ℝ) : Fin k :=
  ⟨min (Nat.floor (max 0 ((k : ℝ) * spentFraction))) (k - 1), by
    have hlast : k - 1 < k := Nat.sub_lt hk (by omega)
    exact lt_of_le_of_lt (Nat.min_le_right _ _) hlast⟩

/-- The active slab in a general-budget state, using the spent-budget fraction. -/
noncomputable def activeBudgetSlab
    (k : ℕ) (hk : 0 < k) (spent budget : ℝ) : Fin k :=
  activeSlab k hk (spent / budget)

/-- Paper-facing expansion of the current-slab computation. -/
theorem activeSlab_val_formula
    (k : ℕ) (hk : 0 < k) (spentFraction : ℝ) :
    (activeSlab k hk spentFraction).val =
      min (Nat.floor (max 0 ((k : ℝ) * spentFraction))) (k - 1) := by
  rfl

/-! ## An actual finite maximum scan with a cost ledger -/

/-- Result and exact unit-cost counters returned by a finite maximum scan. -/
structure FiniteMaxScanResult (Advertiser : Type*) where
  winner : Option Advertiser
  candidateTests : ℕ
  scoreComparisons : ℕ

/--
A right-to-left scan of a concrete advertiser list.  Every element incurs one
feasibility test.  A score comparison is incurred exactly when the element is
feasible and the already-scanned suffix has a feasible winner.
-/
noncomputable def finiteMaxScan {Advertiser : Type*}
    (feasible : Advertiser → Prop) (score : Advertiser → ℝ) :
    List Advertiser → FiniteMaxScanResult Advertiser
  | [] => ⟨none, 0, 0⟩
  | a :: as =>
      let tail := finiteMaxScan feasible score as
      if ha : feasible a then
        match tail.winner with
        | none => ⟨some a, tail.candidateTests + 1, tail.scoreComparisons⟩
        | some b =>
            if score b ≤ score a then
              ⟨some a, tail.candidateTests + 1, tail.scoreComparisons + 1⟩
            else
              ⟨some b, tail.candidateTests + 1, tail.scoreComparisons + 1⟩
      else
        ⟨tail.winner, tail.candidateTests + 1, tail.scoreComparisons⟩

/-- The candidate counter is the exact number of list elements inspected. -/
theorem finiteMaxScan_candidateTests {Advertiser : Type*}
    (feasible : Advertiser → Prop) (score : Advertiser → ℝ)
    (xs : List Advertiser) :
    (finiteMaxScan feasible score xs).candidateTests = xs.length := by
  classical
  induction xs with
  | nil => rfl
  | cons a as ih =>
      by_cases ha : feasible a
      · rw [finiteMaxScan]
        simp only [ha, dite_true]
        cases htail : (finiteMaxScan feasible score as).winner with
        | none => simp [htail, ih]
        | some b =>
            by_cases hscore : score b ≤ score a <;>
              simp [htail, hscore, ih]
      · rw [finiteMaxScan]
        simp [ha, ih]

/-- A scan performs at most one score comparison per inspected candidate. -/
theorem finiteMaxScan_scoreComparisons_le {Advertiser : Type*}
    (feasible : Advertiser → Prop) (score : Advertiser → ℝ)
    (xs : List Advertiser) :
    (finiteMaxScan feasible score xs).scoreComparisons ≤ xs.length := by
  classical
  induction xs with
  | nil => simp [finiteMaxScan]
  | cons a as ih =>
      by_cases ha : feasible a
      · rw [finiteMaxScan]
        simp only [ha, dite_true]
        cases htail : (finiteMaxScan feasible score as).winner with
        | none =>
            simp only [htail, List.length_cons]
            omega
        | some b =>
            by_cases hscore : score b ≤ score a <;>
              simp [htail, hscore, ih]
      · rw [finiteMaxScan]
        simp only [ha, dite_false, List.length_cons]
        omega

/-- Complete semantic specification of the recursive scan's selected winner. -/
theorem finiteMaxScan_winner_spec {Advertiser : Type*}
    (feasible : Advertiser → Prop) (score : Advertiser → ℝ)
    (xs : List Advertiser) :
    let result := finiteMaxScan feasible score xs
    (result.winner = none ↔ ∀ a ∈ xs, ¬ feasible a) ∧
      ∀ w, result.winner = some w →
        w ∈ xs ∧ feasible w ∧
          ∀ a ∈ xs, feasible a → score a ≤ score w := by
  classical
  induction xs with
  | nil => simp [finiteMaxScan]
  | cons a as ih =>
      dsimp only
      by_cases ha : feasible a
      · cases htail : (finiteMaxScan feasible score as).winner with
        | none =>
            have ihNone : ∀ b ∈ as, ¬ feasible b :=
              (ih.1).1 htail
            simp only [finiteMaxScan, ha, dite_true, htail]
            constructor
            · constructor
              · intro hnone
                simp at hnone
              · intro hall
                exact False.elim ((hall a (by simp)) ha)
            · intro w hw
              have hw' : a = w := by simpa using hw
              subst w
              refine ⟨by simp, ha, ?_⟩
              intro b hb hbfeas
              simp only [List.mem_cons] at hb
              rcases hb with hba | hb
              · subst b
                exact le_rfl
              · exact False.elim (ihNone b hb hbfeas)
        | some b =>
            have ihSome := ih.2 b htail
            by_cases hscore : score b ≤ score a
            · simp only [finiteMaxScan, ha, dite_true, htail, hscore, if_pos]
              constructor
              · constructor
                · intro hnone
                  simp at hnone
                · intro hall
                  exact False.elim ((hall a (by simp)) ha)
              · intro w hw
                have hw' : a = w := by simpa using hw
                subst w
                refine ⟨by simp, ha, ?_⟩
                intro c hc hcfeas
                simp only [List.mem_cons] at hc
                rcases hc with hca | hc
                · subst c
                  exact le_rfl
                · exact (ihSome.2.2 c hc hcfeas).trans hscore
            · have ha_le_b : score a ≤ score b := le_of_not_ge hscore
              simp only [finiteMaxScan, ha, dite_true, htail, hscore, if_false]
              constructor
              · constructor
                · intro hnone
                  simp at hnone
                · intro hall
                  exact False.elim ((hall a (by simp)) ha)
              · intro w hw
                have hw' : b = w := by simpa using hw
                subst w
                refine ⟨by simp [ihSome.1], ihSome.2.1, ?_⟩
                intro c hc hcfeas
                simp only [List.mem_cons] at hc
                rcases hc with hca | hc
                · subst c
                  exact ha_le_b
                · exact ihSome.2.2 c hc hcfeas
      · simp only [finiteMaxScan, ha, dite_false]
        constructor
        · constructor
          · intro hnone
            have hnoneTail :
                (finiteMaxScan feasible score as).winner = none := hnone
            intro b hb
            simp only [List.mem_cons] at hb
            rcases hb with hba | hb
            · subst b
              exact ha
            · exact (ih.1.1 hnoneTail) b hb
          · intro hall
            exact ih.1.2 (fun b hb => hall b (by simp [hb]))
        · intro w hw
          have hspec := ih.2 w hw
          exact ⟨by simp [hspec.1], hspec.2.1, by
            intro b hb hbfeas
            simp only [List.mem_cons] at hb
            rcases hb with hba | hb
            · subst b
              exact False.elim (ha hbfeas)
            · exact hspec.2.2 b hb hbfeas⟩

/-! ## Occurrence-indexed online execution -/

/-- One source-sequence decision, including the spend vector before the arrival. -/
structure OccurrenceDecision (Advertiser Query : Type*) where
  query : Query
  winner : Option Advertiser
  spentBefore : Advertiser → ℝ

/-- State of an occurrence-indexed online execution. -/
structure OccurrenceState (Advertiser Query : Type*) where
  spent : Advertiser → ℝ
  revenue : ℝ
  decisionsRev : List (OccurrenceDecision Advertiser Query)
  candidateTests : ℕ
  scoreComparisons : ℕ

/-- Empty occurrence-indexed state. -/
def initialOccurrenceState : OccurrenceState Advertiser Query where
  spent := fun _ => 0
  revenue := 0
  decisionsRev := []
  candidateTests := 0
  scoreComparisons := 0

/-- Feasibility of assigning the next occurrence in an occurrence state. -/
def occurrenceCanAssign
    (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query) (a : Advertiser) : Prop :=
  S.spent a + I.bid a q ≤ I.budget a

/-- Continuous MSVV scaled bid computed from the occurrence state's actual spend. -/
noncomputable def occurrenceBalanceScore
    (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query) (a : Advertiser) : ℝ :=
  I.bid a q * (1 - Real.exp (S.spent a / I.budget a - 1))

/--
The score used by the Section 5 algorithm with an arbitrary tradeoff function
`psi`: a bid times `psi` of the bidder's current spent-budget fraction.
-/
noncomputable def occurrenceTradeoffScore
    (psi : ℝ → ℝ) (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query) (a : Advertiser) : ℝ :=
  I.bid a q * psi (S.spent a / I.budget a)

/-- Discrete Section 3 score computed from the currently active budget slab. -/
noncomputable def occurrenceDiscreteScore
    (k : ℕ) (hk : 0 < k)
    (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query) (a : Advertiser) : ℝ :=
  I.bid a q * discreteTradeoff k
    (activeBudgetSlab k hk (S.spent a) (I.budget a))

/-- A discrete Section 3 choice is feasible and maximizes the `psi_k` score. -/
def occurrenceDiscreteBalanceChoice
    (k : ℕ) (hk : 0 < k)
    (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query) (a : Advertiser) : Prop :=
  occurrenceCanAssign I S q a ∧
    ∀ b, occurrenceCanAssign I S q b →
      occurrenceDiscreteScore k hk I S q b ≤ occurrenceDiscreteScore k hk I S q a

/-- The actual finite scan used for one continuous Balance/MSVV decision. -/
noncomputable def balanceScan
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query) :
    FiniteMaxScanResult Advertiser :=
  finiteMaxScan (occurrenceCanAssign I S q) (occurrenceBalanceScore I S q)
    (Finset.univ : Finset Advertiser).toList

/--
The deterministic finite scan for the source algorithm with tradeoff `psi`.
It makes the source's resulting allocation, and hence its final type counts,
an explicit function of the instance, arrival history, and tradeoff.
-/
noncomputable def tradeoffScan
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (psi : ℝ → ℝ) (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query) :
    FiniteMaxScanResult Advertiser :=
  finiteMaxScan (occurrenceCanAssign I S q) (occurrenceTradeoffScore psi I S q)
    (Finset.univ : Finset Advertiser).toList

/-- The actual finite scan used for one discrete Section 3 decision. -/
noncomputable def discreteBalanceScan
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k)
    (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query) :
    FiniteMaxScanResult Advertiser :=
  finiteMaxScan (occurrenceCanAssign I S q) (occurrenceDiscreteScore k hk I S q)
    (Finset.univ : Finset Advertiser).toList

/-- Apply one already-computed finite scan result and thread both costs. -/
noncomputable def applyScanDecision
    {Advertiser Query : Type*} [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query)
    (scan : FiniteMaxScanResult Advertiser) :
    OccurrenceState Advertiser Query :=
  let charge := fun a => I.bid a q
  { spent := fun a =>
      match scan.winner with
      | none => S.spent a
      | some winner => if a = winner then S.spent a + charge winner else S.spent a
    revenue :=
      match scan.winner with
      | none => S.revenue
      | some winner => S.revenue + charge winner
    decisionsRev :=
      ⟨q, scan.winner, S.spent⟩ :: S.decisionsRev
    candidateTests := S.candidateTests + scan.candidateTests
    scoreComparisons := S.scoreComparisons + scan.scoreComparisons }

/-- One occurrence step of the continuous Balance/MSVV runner. -/
noncomputable def balanceStep
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query) :
    OccurrenceState Advertiser Query :=
  applyScanDecision I S q (balanceScan I S q)

/-- One occurrence step of the source algorithm using the supplied tradeoff. -/
noncomputable def tradeoffStep
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (psi : ℝ → ℝ) (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query) :
    OccurrenceState Advertiser Query :=
  applyScanDecision I S q (tradeoffScan psi I S q)

/-- One occurrence step of the discrete Section 3 runner. -/
noncomputable def discreteBalanceStep
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k)
    (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query) :
    OccurrenceState Advertiser Query :=
  applyScanDecision I S q (discreteBalanceScan k hk I S q)

/-- Execute a step function on every occurrence, including repeated query words. -/
noncomputable def runOccurrencesFrom
    (step : OccurrenceState Advertiser Query → Query →
      OccurrenceState Advertiser Query) :
    OccurrenceState Advertiser Query → List Query →
      OccurrenceState Advertiser Query
  | S, [] => S
  | S, q :: qs => runOccurrencesFrom step (step S q) qs

/-- Source-faithful continuous Balance/MSVV run. -/
noncomputable def runBalanceOccurrences
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query) (history : List Query) :
    OccurrenceState Advertiser Query :=
  runOccurrencesFrom (balanceStep I) initialOccurrenceState history

/--
The Section 5 run for an arbitrary tradeoff `psi` on a concrete AdWords
instance and finite arrival history.
-/
noncomputable def runTradeoffOccurrences
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (psi : ℝ → ℝ) (I : PaperInstance Advertiser Query) (history : List Query) :
    OccurrenceState Advertiser Query :=
  runOccurrencesFrom (tradeoffStep psi I) initialOccurrenceState history

/-- Source-faithful discrete Section 3 run. -/
noncomputable def runDiscreteBalanceOccurrences
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k)
    (I : PaperInstance Advertiser Query) (history : List Query) :
    OccurrenceState Advertiser Query :=
  runOccurrencesFrom (discreteBalanceStep k hk I) initialOccurrenceState history

/-- The continuous scan's winner is feasible and score-maximal among all advertisers. -/
theorem balanceScan_winner_is_balance_choice
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query) (a : Advertiser)
    (hchoice : (balanceScan I S q).winner = some a) :
    occurrenceCanAssign I S q a ∧
      ∀ b, occurrenceCanAssign I S q b →
        occurrenceBalanceScore I S q b ≤ occurrenceBalanceScore I S q a := by
  classical
  have hspec :=
    (finiteMaxScan_winner_spec
      (occurrenceCanAssign I S q) (occurrenceBalanceScore I S q)
      (Finset.univ : Finset Advertiser).toList).2 a hchoice
  exact ⟨hspec.2.1, fun b hb => hspec.2.2 b (by simp) hb⟩

/-- The discrete finite scan realizes its stated feasible `psi_k` argmax rule. -/
theorem discreteBalanceScan_winner_is_discrete_choice
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k)
    (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query) (a : Advertiser)
    (hchoice : (discreteBalanceScan k hk I S q).winner = some a) :
    occurrenceDiscreteBalanceChoice k hk I S q a := by
  classical
  have hspec :=
    (finiteMaxScan_winner_spec
      (occurrenceCanAssign I S q) (occurrenceDiscreteScore k hk I S q)
      (Finset.univ : Finset Advertiser).toList).2 a hchoice
  exact ⟨hspec.2.1, fun b hb => hspec.2.2 b (by simp) hb⟩

/--
With a common positive bid, a discrete-score maximizer has the earliest active
slab among feasible advertisers, which is the BALANCE rule.  Strict decrease
is the precise tie convention needed by the source's phrase "monotonically
decreasing."
-/
theorem equal_bid_discrete_winner_has_earliest_slab
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (k : ℕ) (hk : 0 < k)
    (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query) (a : Advertiser)
    {commonBid : ℝ} (hcommon : ∀ b, I.bid b q = commonBid)
    (hcommon_pos : 0 < commonBid)
    (hchoice : (discreteBalanceScan k hk I S q).winner = some a) :
    occurrenceCanAssign I S q a ∧
      ∀ b, occurrenceCanAssign I S q b →
        activeBudgetSlab k hk (S.spent a) (I.budget a) ≤
          activeBudgetSlab k hk (S.spent b) (I.budget b) := by
  classical
  have hspec :=
    (finiteMaxScan_winner_spec
      (occurrenceCanAssign I S q) (occurrenceDiscreteScore k hk I S q)
      (Finset.univ : Finset Advertiser).toList).2 a hchoice
  refine ⟨hspec.2.1, ?_⟩
  intro b hb
  by_contra hnot
  have hlt :
      activeBudgetSlab k hk (S.spent b) (I.budget b) <
        activeBudgetSlab k hk (S.spent a) (I.budget a) :=
    lt_of_not_ge hnot
  have hpsi := discreteTradeoff_strictAnti k hlt
  have hscaled :
      commonBid * discreteTradeoff k
          (activeBudgetSlab k hk (S.spent a) (I.budget a)) <
        commonBid * discreteTradeoff k
          (activeBudgetSlab k hk (S.spent b) (I.budget b)) :=
    mul_lt_mul_of_pos_left hpsi hcommon_pos
  have hmax := hspec.2.2 b (by simp) hb
  unfold occurrenceDiscreteScore at hmax
  rw [hcommon a, hcommon b] at hmax
  exact (not_lt_of_ge hmax) hscaled

/-- Each actual Balance scan performs exactly one feasibility test per advertiser. -/
theorem balanceScan_candidateTests
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query) :
    (balanceScan I S q).candidateTests = Fintype.card Advertiser := by
  classical
  unfold balanceScan
  rw [finiteMaxScan_candidateTests]
  simp

/-- Each actual Balance scan performs at most one comparison per advertiser. -/
theorem balanceScan_scoreComparisons_le
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (S : OccurrenceState Advertiser Query) (q : Query) :
    (balanceScan I S q).scoreComparisons ≤ Fintype.card Advertiser := by
  classical
  unfold balanceScan
  simpa using
    finiteMaxScan_scoreComparisons_le
      (occurrenceCanAssign I S q) (occurrenceBalanceScore I S q)
      (Finset.univ : Finset Advertiser).toList

/-- Exact candidate-test count for a complete occurrence-indexed run. -/
theorem runBalanceOccurrences_candidateTests
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query) (history : List Query) :
    (runBalanceOccurrences I history).candidateTests =
      history.length * Fintype.card Advertiser := by
  classical
  unfold runBalanceOccurrences
  have hgeneral :
      ∀ (S : OccurrenceState Advertiser Query),
        (runOccurrencesFrom (balanceStep I) S history).candidateTests =
          S.candidateTests + history.length * Fintype.card Advertiser := by
    induction history with
    | nil => intro S; simp [runOccurrencesFrom]
    | cons q qs ih =>
        intro S
        rw [runOccurrencesFrom, ih]
        simp [balanceStep, applyScanDecision, balanceScan_candidateTests]
        simp only [List.length_cons, Nat.succ_mul, one_mul]
        omega
  simpa [initialOccurrenceState] using hgeneral initialOccurrenceState

/-- Comparison bound for the same actual occurrence-indexed run. -/
theorem runBalanceOccurrences_scoreComparisons_le
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query) (history : List Query) :
    (runBalanceOccurrences I history).scoreComparisons ≤
      history.length * Fintype.card Advertiser := by
  classical
  unfold runBalanceOccurrences
  have hgeneral :
      ∀ (S : OccurrenceState Advertiser Query),
        (runOccurrencesFrom (balanceStep I) S history).scoreComparisons ≤
          S.scoreComparisons + history.length * Fintype.card Advertiser := by
    induction history with
    | nil => intro S; simp [runOccurrencesFrom]
    | cons q qs ih =>
        intro S
        calc
          (runOccurrencesFrom (balanceStep I) S (q :: qs)).scoreComparisons =
              (runOccurrencesFrom (balanceStep I) (balanceStep I S q) qs).scoreComparisons :=
                rfl
          _ ≤ (balanceStep I S q).scoreComparisons +
              qs.length * Fintype.card Advertiser := ih (balanceStep I S q)
          _ ≤ S.scoreComparisons +
              (q :: qs).length * Fintype.card Advertiser := by
                have hscan := balanceScan_scoreComparisons_le I S q
                simp only [balanceStep, applyScanDecision, List.length_cons,
                  Nat.succ_mul, one_mul]
                omega
  simpa [initialOccurrenceState] using hgeneral initialOccurrenceState

/-! ## Occurrence revenue and the distinct-identifier bridge -/

/-- Revenue contributed by one query occurrence under an occurrence assignment. -/
noncomputable def occurrenceRevenueAt
    (I : PaperInstance Advertiser Query) (history : List Query)
    (A : Fin history.length → Option Advertiser) (t : Fin history.length) : ℝ :=
  match A t with
  | none => 0
  | some a => I.bid a (history.get t)

/-- Total revenue of an assignment whose domain is occurrences, not query words. -/
noncomputable def occurrenceRevenue
    (I : PaperInstance Advertiser Query) (history : List Query)
    (A : Fin history.length → Option Advertiser) : ℝ :=
  ∑ t : Fin history.length, occurrenceRevenueAt I history A t

/-- Spend charged to one advertiser by an occurrence-indexed assignment. -/
noncomputable def occurrenceSpend
    [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query) (history : List Query)
    (A : Fin history.length → Option Advertiser) (a : Advertiser) : ℝ :=
  ∑ t : Fin history.length,
    match A t with
    | none => 0
    | some owner => if owner = a then I.bid a (history.get t) else 0

/-- A source-model allocation is total when every arriving occurrence receives an owner. -/
def occurrenceAssignmentIsTotal
    (history : List Query) (A : Fin history.length → Option Advertiser) : Prop :=
  ∀ t, ∃ a, A t = some a

/--
The Section 2 feasibility model for a chronological allocation: every arrival
is assigned and no advertiser is charged above its budget.  The separate
online runner may expose an unassigned occurrence when its feasibility scan has
no candidate; connecting that execution to this total source model is a later
theorem obligation, not a definitionally hidden convention.
-/
def occurrenceAssignmentFeasible
    [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query) (history : List Query)
    (A : Fin history.length → Option Advertiser) : Prop :=
  occurrenceAssignmentIsTotal history A ∧
    ∀ a, occurrenceSpend I history A a ≤ I.budget a

/--
When query identifiers are genuinely distinct and cover the finite query type,
the old identifier-indexed revenue is the corresponding chronological list sum.
No such bridge is asserted for histories with repeated words.
-/
theorem identifierRevenue_eq_history_sum_of_nodup_cover
    {Advertiser Query : Type*} [Fintype Query]
    [DecidableEq Query]
    (I : PaperInstance Advertiser Query)
    (A : PaperAssignment Advertiser Query)
    (history : List Query) (hnodup : history.Nodup)
    (hcover : AdWordsInstance.historyFinset history = Finset.univ) :
    paperRevenue I A =
      (history.map fun q =>
        match A q with
        | none => 0
        | some a => I.bid a q).sum := by
  exact AdWordsInstance.sum_univ_eq_list_sum_of_historyFinset_eq_univ
    history hnodup hcover (fun q =>
      match A q with
      | none => 0
      | some a => I.bid a q)

/-! ## Sections 4--6: explicit source accounting objects -/

/--
Section 4/5 final-type relation: type `i+1` means final spend fraction in
`(i/k,(i+1)/k]`, with zero spend assigned to the first type by convention.
-/
def IsFinalType (k : ℕ) (spentFraction : ℝ) (i : Fin k) : Prop :=
  (spentFraction = 0 ∧ i.val = 0) ∨
    ((i.val : ℝ) / (k : ℝ) < spentFraction ∧
      spentFraction ≤ (((i.val + 1 : ℕ) : ℝ) / (k : ℝ)))

/-- Section 4's number `x_i` of bidders in final type `i+1`. -/
noncomputable def section4TypeCount
    {Advertiser : Type*} [Fintype Advertiser]
    (k : ℕ) (finalSpentFraction : Advertiser → ℝ) (i : Fin k) : ℝ :=
  ∑ a : Advertiser, if IsFinalType k (finalSpentFraction a) i then 1 else 0

/-- The idealized Section 4 slab-spend formula after the stated rounding simplification. -/
noncomputable def section4IdealizedSlabSpend
    {k : ℕ} (N : ℝ) (x : Fin k → ℝ) (i : Fin k) : ℝ :=
  N / (k : ℝ) -
    (∑ j ∈ Finset.Iio i, x j) / (k : ℝ)

/-- Section 4's displayed formula for `beta_i`. -/
theorem section4IdealizedSlabSpend_formula
    {k : ℕ} (N : ℝ) (x : Fin k → ℝ) (i : Fin k) :
    section4IdealizedSlabSpend N x i =
      N / (k : ℝ) - (∑ j ∈ Finset.Iio i, x j) / (k : ℝ) := by
  rfl

/--
The aggregate `N/k` discretization bound from the explicit per-bidder rounding
premise used in Section 4's informal small-bid argument.
-/
theorem section4_discretization_error_le_N_div_k
    {Advertiser : Type*} [Fintype Advertiser]
    {k : ℕ} (hk : 0 < k) (error : Advertiser → ℝ)
    (herror_nonneg : ∀ a, 0 ≤ error a)
    (herror : ∀ a, error a ≤ 1 / (k : ℝ)) :
    ∑ a : Advertiser, error a ≤
      (Fintype.card Advertiser : ℝ) / (k : ℝ) := by
  calc
    ∑ a : Advertiser, error a ≤
        ∑ _a : Advertiser, (1 / (k : ℝ)) :=
      Finset.sum_le_sum fun a _ => herror a
    _ = (Fintype.card Advertiser : ℝ) / (k : ℝ) := by
      simp [div_eq_mul_inv]

/-- Section 4's revenue-to-factor-LP bridge, separated from the LP optimum proof. -/
theorem section4_balance_revenue_factor_lp_bridge
    {k : ℕ} (N BAL Φ : ℝ)
    (hBAL : N - BAL ≤ Φ + N / (k : ℝ)) :
    N - Φ - N / (k : ℝ) ≤ BAL := by
  linarith

/-- Section 5's type-count vector `alpha`. -/
noncomputable abbrev section5AlphaTypeCount
    {Advertiser : Type*} [Fintype Advertiser]
    (k : ℕ) (finalSpentFraction : Advertiser → ℝ) : Fin k → ℝ :=
  section4TypeCount k finalSpentFraction

/--
The vector `a` used by Section 5's factor-revealing LP has the first `k - 1`
type counts: the terminal type is not an LP variable.  Writing `k = m + 1`
makes that source convention total, including the degenerate `m = 0` case.
-/
noncomputable def section5PreterminalAlphaTypeCount
    {Advertiser : Type*} [Fintype Advertiser]
    (m : ℕ) (finalSpentFraction : Advertiser → ℝ) : Fin m → ℝ :=
  fun i => section5AlphaTypeCount (m + 1) finalSpentFraction i.castSucc

/-- Each realized Section 5 preterminal type count is nonnegative. -/
theorem section5PreterminalAlphaTypeCount_nonnegative
    {Advertiser : Type*} [Fintype Advertiser]
    (m : ℕ) (finalSpentFraction : Advertiser → ℝ) (i : Fin m) :
    0 ≤ section5PreterminalAlphaTypeCount m finalSpentFraction i := by
  unfold section5PreterminalAlphaTypeCount section5AlphaTypeCount section4TypeCount
  apply Finset.sum_nonneg
  intro a _
  split_ifs <;> norm_num

/-- The final spent-budget fraction produced by a Section 5 tradeoff run. -/
noncomputable def section5TradeoffRunSpentFraction
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (psi : ℝ → ℝ) (I : PaperInstance Advertiser Query) (history : List Query) :
    Advertiser → ℝ :=
  fun a => (runTradeoffOccurrences psi I history).spent a / I.budget a

/--
Section 5's `k-1`-coordinate type-count vector for the actual run on an
instance with tradeoff `psi` (with `k = m + 1`).
-/
noncomputable def section5PreterminalAlphaTypeCountOfTradeoffRun
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (m : ℕ) (psi : ℝ → ℝ) (I : PaperInstance Advertiser Query)
    (history : List Query) : Fin m → ℝ :=
  section5PreterminalAlphaTypeCount m
    (section5TradeoffRunSpentFraction psi I history)

/-- Actual-run Section 5 type counts are nonnegative. -/
theorem section5PreterminalAlphaTypeCountOfTradeoffRun_nonnegative
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (m : ℕ) (psi : ℝ → ℝ) (I : PaperInstance Advertiser Query)
    (history : List Query) (i : Fin m) :
    0 ≤ section5PreterminalAlphaTypeCountOfTradeoffRun m psi I history i := by
  exact section5PreterminalAlphaTypeCount_nonnegative m
    (section5TradeoffRunSpentFraction psi I history) i

/-- Section 5's idealized slab-spend vector `beta`. -/
noncomputable abbrev section5IdealizedBeta
    {k : ℕ} (N : ℝ) (alpha : Fin k → ℝ) : Fin k → ℝ :=
  section4IdealizedSlabSpend N alpha

/-- Section 5's prefix perturbation `Delta_i = sum_{j <= i}(alpha_j-beta_j)`. -/
noncomputable def section5Delta
    {k : ℕ} (alpha beta : Fin k → ℝ) (i : Fin k) : ℝ :=
  ∑ j ∈ Finset.Iic i, (alpha j - beta j)

/-- `ALG(q)` for one recorded occurrence decision. -/
noncomputable def section5AlgQueryRevenue
    (I : PaperInstance Advertiser Query)
    (d : OccurrenceDecision Advertiser Query) : ℝ :=
  match d.winner with
  | none => 0
  | some a => I.bid a d.query

/-- `OPT(q)` for occurrence `t`, so repeated query words remain distinct. -/
noncomputable def section5OptQueryRevenue
    (I : PaperInstance Advertiser Query) (history : List Query)
    (opt : Fin history.length → Option Advertiser) (t : Fin history.length) : ℝ :=
  occurrenceRevenueAt I history opt t

/-- OPT revenue over the fiber of occurrences whose owner has final type `i`. -/
noncomputable def section5OptTypeFiberRevenue
    (I : PaperInstance Advertiser Query) (history : List Query)
    (opt : Fin history.length → Option Advertiser)
    (finalType : Advertiser → Fin k) (i : Fin k) : ℝ :=
  ∑ t : Fin history.length,
    match opt t with
    | none => 0
    | some a => if finalType a = i then I.bid a (history.get t) else 0

/-- Query type induced by OPT's owner and the online run's final bidder type classifier. -/
def section5QueryType
    (optOwner : Option Advertiser) (finalType : Advertiser → Fin k) : Option (Fin k) :=
  optOwner.map finalType

/-- Slab from which the online algorithm paid for a recorded occurrence. -/
noncomputable def section5QuerySlab
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (d : OccurrenceDecision Advertiser Query) : Option (Fin k) :=
  d.winner.map fun a => activeBudgetSlab k hk (d.spentBefore a) (I.budget a)

/-- ALG revenue over the fiber of recorded occurrences paid from slab `i`. -/
noncomputable def section5AlgSlabFiberRevenue
    (k : ℕ) (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (decisions : List (OccurrenceDecision Advertiser Query)) (i : Fin k) : ℝ :=
  (decisions.map fun d =>
    if section5QuerySlab k hk I d = some i then
      section5AlgQueryRevenue I d
    else 0).sum

/--
Under the Section 2--5 unit-budget exhaustive-OPT assumption, OPT revenue over
a final-type fiber equals the number of bidders in that fiber.
-/
theorem section5_opt_type_fiber_revenue_eq_type_count
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    {k : ℕ} (I : PaperInstance Advertiser Query) (history : List Query)
    (opt : Fin history.length → Option Advertiser)
    (finalType : Advertiser → Fin k)
    (hexhaust : ∀ a, occurrenceSpend I history opt a = 1)
    (i : Fin k) :
    section5OptTypeFiberRevenue I history opt finalType i =
      ∑ a : Advertiser, if finalType a = i then 1 else 0 := by
  classical
  calc
    section5OptTypeFiberRevenue I history opt finalType i =
        ∑ t : Fin history.length, ∑ a : Advertiser,
          if finalType a = i then
            match opt t with
            | none => 0
            | some owner => if owner = a then I.bid a (history.get t) else 0
          else 0 := by
            unfold section5OptTypeFiberRevenue
            apply Finset.sum_congr rfl
            intro t _
            cases hopt : opt t with
            | none => simp [hopt]
            | some owner =>
                by_cases htype : finalType owner = i
                · simp only [hopt]
                  rw [if_pos htype]
                  symm
                  have hsum := Fintype.sum_eq_single owner
                    (f := fun b : Advertiser =>
                      if finalType b = i then
                        if owner = b then I.bid b (history.get t) else 0
                      else 0)
                    (fun b hne => by
                      have howner : owner ≠ b := Ne.symm hne
                      simp [howner])
                  simpa [htype] using hsum
                · simp only [hopt]
                  rw [if_neg htype]
                  symm
                  apply Fintype.sum_eq_zero
                  intro b
                  by_cases howner : owner = b
                  · subst b
                    simp [htype]
                  · simp [howner]
    _ = ∑ a : Advertiser, ∑ t : Fin history.length,
          if finalType a = i then
            match opt t with
            | none => 0
            | some owner => if owner = a then I.bid a (history.get t) else 0
          else 0 := Finset.sum_comm
    _ = ∑ a : Advertiser,
          if finalType a = i then occurrenceSpend I history opt a else 0 := by
            apply Finset.sum_congr rfl
            intro a _
            by_cases htype : finalType a = i
            · simp [htype, occurrenceSpend]
            · simp [htype]
    _ = ∑ a : Advertiser, if finalType a = i then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro a _
          rw [hexhaust a]

/-- Section 6's current type is the one-indexed active budget slab. -/
noncomputable abbrev section6CurrentType
    (k : ℕ) (hk : 0 < k) (spent budget : ℝ) : Fin k :=
  activeBudgetSlab k hk spent budget

/-- Lower endpoint of bidder `a`'s budget slab `i`. -/
noncomputable def section6SlabLower
    (k : ℕ) (I : PaperInstance Advertiser Query)
    (i : Fin k) (a : Advertiser) : ℝ :=
  I.budget a * (i.val : ℝ) / (k : ℝ)

/-- Upper endpoint of bidder `a`'s budget slab `i`. -/
noncomputable def section6SlabUpper
    (k : ℕ) (I : PaperInstance Advertiser Query)
    (i : Fin k) (a : Advertiser) : ℝ :=
  I.budget a * ((i.val + 1 : ℕ) : ℝ) / (k : ℝ)

/--
`beta_i^j`: the amount of bidder `a`'s final spend lying in budget interval
`[i B_a/k, (i+1) B_a/k]`.  The difference of clipped cumulative spends splits
a payment that crosses a slab boundary instead of assigning the whole payment
to its starting slab.
-/
noncomputable def section6BidderSlabSpend
    (k : ℕ) (I : PaperInstance Advertiser Query)
    (finalSpend : Advertiser → ℝ)
    (i : Fin k) (a : Advertiser) : ℝ :=
  min (finalSpend a) (section6SlabUpper k I i a) -
    min (finalSpend a) (section6SlabLower k I i a)

/-- `beta_i`: aggregate split payment from slab `i` across all bidders. -/
noncomputable def section6AggregateSlabSpend
    {Advertiser Query : Type*} [Fintype Advertiser]
    (k : ℕ) (I : PaperInstance Advertiser Query)
    (finalSpend : Advertiser → ℝ) (i : Fin k) : ℝ :=
  ∑ a : Advertiser, section6BidderSlabSpend k I finalSpend i a

/-- `alpha_i`: OPT revenue from occurrences assigned to bidders of final type `i`. -/
noncomputable def section6OptRevenueByFinalType
    {Advertiser Query : Type*}
    (I : PaperInstance Advertiser Query) (history : List Query)
    (opt : Fin history.length → Option Advertiser)
    (finalType : Advertiser → Fin k) (i : Fin k) : ℝ :=
  ∑ t : Fin history.length,
    match opt t with
    | none => 0
    | some a =>
        if finalType a = i then I.bid a (history.get t) else 0

/-- Section 6's `alpha`, the sum of the `alpha_i` values. -/
noncomputable def section6OptRevenueTotalByType
    {Advertiser Query : Type*} [Fintype (Fin k)]
    (I : PaperInstance Advertiser Query) (history : List Query)
    (opt : Fin history.length → Option Advertiser)
    (finalType : Advertiser → Fin k) : ℝ :=
  ∑ i : Fin k, section6OptRevenueByFinalType I history opt finalType i

/-- The type fibers partition the occurrence-indexed OPT revenue. -/
theorem section6_alpha_total_eq_occurrenceRevenue
    {Advertiser Query : Type*} {k : ℕ}
    (I : PaperInstance Advertiser Query) (history : List Query)
    (opt : Fin history.length → Option Advertiser)
    (finalType : Advertiser → Fin k) :
    section6OptRevenueTotalByType I history opt finalType =
      occurrenceRevenue I history opt := by
  classical
  unfold section6OptRevenueTotalByType section6OptRevenueByFinalType
    occurrenceRevenue occurrenceRevenueAt
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  cases hopt : opt t with
  | none => simp [hopt]
  | some a => simp [hopt]

/-- Each positive-budget slab's lower endpoint is at most its upper endpoint. -/
theorem section6SlabLower_le_upper
    {k : ℕ} (I : PaperInstance Advertiser Query)
    (hbudget : I.PositiveBudgets) (i : Fin k) (a : Advertiser) :
    section6SlabLower k I i a ≤ section6SlabUpper k I i a := by
  unfold section6SlabLower section6SlabUpper
  have hkNat : 0 < k := Nat.zero_lt_of_lt i.isLt
  have hk : 0 < (k : ℝ) := by exact_mod_cast hkNat
  apply (div_le_div_iff_of_pos_right hk).2
  exact mul_le_mul_of_nonneg_left (by norm_num) (hbudget a).le

/-- Split-payment slab spend is nonnegative. -/
theorem section6BidderSlabSpend_nonnegative
    {k : ℕ} (I : PaperInstance Advertiser Query)
    (hbudget : I.PositiveBudgets) (finalSpend : Advertiser → ℝ)
    (i : Fin k) (a : Advertiser) :
    0 ≤ section6BidderSlabSpend k I finalSpend i a := by
  unfold section6BidderSlabSpend
  exact sub_nonneg.mpr
    (min_le_min_left _ (section6SlabLower_le_upper I hbudget i a))

/--
If bidder `a` finishes in a type strictly after slab `i`, final-type semantics
force the whole interval `i` to have been spent.
-/
theorem section6BidderSlabSpend_eq_budget_div_of_lt_finalType
    {k : ℕ} (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (hbudget : I.PositiveBudgets) (finalSpend : Advertiser → ℝ)
    (finalType : Advertiser → Fin k)
    (hfinalType : ∀ a,
      IsFinalType k (finalSpend a / I.budget a) (finalType a))
    (i : Fin k) (a : Advertiser) (hi : i < finalType a) :
    section6BidderSlabSpend k I finalSpend i a =
      I.budget a / (k : ℝ) := by
  have hkReal : 0 < (k : ℝ) := by exact_mod_cast hk
  have htypeLower :
      ((finalType a).val : ℝ) / (k : ℝ) <
        finalSpend a / I.budget a := by
    rcases hfinalType a with hzero | hinterval
    · exact False.elim (by omega)
    · exact hinterval.1
  have hindexNat : i.val + 1 ≤ (finalType a).val := by omega
  have hindexReal :
      ((i.val + 1 : ℕ) : ℝ) ≤ ((finalType a).val : ℝ) := by
    exact_mod_cast hindexNat
  have hindexFrac :
      ((i.val + 1 : ℕ) : ℝ) / (k : ℝ) ≤
        ((finalType a).val : ℝ) / (k : ℝ) :=
    (div_le_div_iff_of_pos_right hkReal).2 hindexReal
  have hupperFrac :
      ((i.val + 1 : ℕ) : ℝ) / (k : ℝ) <
        finalSpend a / I.budget a :=
    hindexFrac.trans_lt htypeLower
  have hupper :
      section6SlabUpper k I i a < finalSpend a := by
    have hmul := (lt_div_iff₀ (hbudget a)).mp hupperFrac
    calc
      section6SlabUpper k I i a =
          ((i.val + 1 : ℕ) : ℝ) / (k : ℝ) * I.budget a := by
            unfold section6SlabUpper
            ring
      _ < finalSpend a := hmul
  have hlower :
      section6SlabLower k I i a ≤ finalSpend a :=
    (section6SlabLower_le_upper I hbudget i a).trans hupper.le
  unfold section6BidderSlabSpend
  rw [min_eq_right hupper.le, min_eq_right hlower]
  unfold section6SlabUpper section6SlabLower
  push_cast
  ring

/-- Regroup one OPT final-type fiber as advertiser-wise occurrence spend. -/
theorem section6OptRevenueByFinalType_eq_sum_occurrenceSpend
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    {k : ℕ} (I : PaperInstance Advertiser Query) (history : List Query)
    (opt : Fin history.length → Option Advertiser)
    (finalType : Advertiser → Fin k) (i : Fin k) :
    section6OptRevenueByFinalType I history opt finalType i =
      ∑ a : Advertiser,
        if finalType a = i then occurrenceSpend I history opt a else 0 := by
  classical
  calc
    section6OptRevenueByFinalType I history opt finalType i =
        ∑ t : Fin history.length, ∑ a : Advertiser,
          if finalType a = i then
            match opt t with
            | none => 0
            | some owner => if owner = a then I.bid a (history.get t) else 0
          else 0 := by
            unfold section6OptRevenueByFinalType
            apply Finset.sum_congr rfl
            intro t _
            cases hopt : opt t with
            | none => simp
            | some owner =>
                by_cases htype : finalType owner = i
                · simp only
                  rw [if_pos htype]
                  symm
                  have hsum := Fintype.sum_eq_single owner
                    (f := fun b : Advertiser =>
                      if finalType b = i then
                        if owner = b then I.bid b (history.get t) else 0
                      else 0)
                    (fun b hne => by
                      have howner : owner ≠ b := Ne.symm hne
                      simp [howner])
                  simpa [htype] using hsum
                · simp only
                  rw [if_neg htype]
                  symm
                  apply Fintype.sum_eq_zero
                  intro b
                  by_cases howner : owner = b
                  · subst b
                    simp [htype]
                  · simp [howner]
    _ = ∑ a : Advertiser, ∑ t : Fin history.length,
          if finalType a = i then
            match opt t with
            | none => 0
            | some owner => if owner = a then I.bid a (history.get t) else 0
          else 0 := Finset.sum_comm
    _ = ∑ a : Advertiser,
          if finalType a = i then occurrenceSpend I history opt a else 0 := by
            apply Finset.sum_congr rfl
            intro a _
            by_cases htype : finalType a = i
            · simp only [if_pos htype, occurrenceSpend]
            · simp [htype]

/-- The OPT revenue after type `i` is exactly the spend of later-type owners. -/
theorem section6OptRevenueTail_eq_sum_later_spend
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    {k : ℕ} (I : PaperInstance Advertiser Query) (history : List Query)
    (opt : Fin history.length → Option Advertiser)
    (finalType : Advertiser → Fin k) (i : Fin k) :
    section6OptRevenueTotalByType I history opt finalType -
        ∑ j ∈ Finset.Iic i,
          section6OptRevenueByFinalType I history opt finalType j =
      ∑ a : Advertiser,
        if i < finalType a then occurrenceSpend I history opt a else 0 := by
  classical
  unfold section6OptRevenueTotalByType
  rw [show
    (∑ j : Fin k,
        section6OptRevenueByFinalType I history opt finalType j) -
          ∑ j ∈ Finset.Iic i,
            section6OptRevenueByFinalType I history opt finalType j =
        ∑ j ∈ Finset.Ioi i,
          section6OptRevenueByFinalType I history opt finalType j by
      exact (by
        have hdiff := Finset.sum_sdiff
          (s₁ := (Finset.Iic i))
          (s₂ := (Finset.univ : Finset (Fin k)))
          (f := section6OptRevenueByFinalType I history opt finalType)
          (by simp)
        rw [← hdiff, add_sub_cancel_right]
        apply Finset.sum_congr
        · ext j
          simp
        · intro j hj
          rfl)]
  simp_rw [section6OptRevenueByFinalType_eq_sum_occurrenceSpend]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : i < finalType a
  · simp [ha]
  · simp [ha]

/-- Actual advertiser-wise OPT feasibility bounds every later-type OPT tail. -/
theorem section6OptRevenueTail_le_later_budgets
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    {k : ℕ} (I : PaperInstance Advertiser Query) (history : List Query)
    (opt : Fin history.length → Option Advertiser)
    (finalType : Advertiser → Fin k)
    (hoptFeasible : ∀ a,
      occurrenceSpend I history opt a ≤ I.budget a)
    (i : Fin k) :
    section6OptRevenueTotalByType I history opt finalType -
        ∑ j ∈ Finset.Iic i,
          section6OptRevenueByFinalType I history opt finalType j ≤
      ∑ a ∈ (Finset.univ : Finset Advertiser).filter
        (fun a => i < finalType a), I.budget a := by
  rw [section6OptRevenueTail_eq_sum_later_spend]
  rw [Finset.sum_filter]
  exact Finset.sum_le_sum fun a _ => by
    by_cases ha : i < finalType a
    · simpa [ha] using hoptFeasible a
    · simp [ha]

/--
The generalized Section 6 beta inequality derived from the paper's primitive
objects: an occurrence-indexed feasible OPT assignment and final types of the
online run.  No tail-budget or full-earlier-slab fact remains as an input.
-/
theorem section6_beta_lower_bound_from_opt_feasibility_and_final_types
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    {k : ℕ} (hk : 0 < k) (I : PaperInstance Advertiser Query)
    (history : List Query)
    (opt : Fin history.length → Option Advertiser)
    (finalSpend : Advertiser → ℝ)
    (finalType : Advertiser → Fin k)
    (hbudget : I.PositiveBudgets)
    (hoptFeasible : ∀ a,
      occurrenceSpend I history opt a ≤ I.budget a)
    (hfinalType : ∀ a,
      IsFinalType k (finalSpend a / I.budget a) (finalType a)) :
    ∀ i : Fin k,
      (section6OptRevenueTotalByType I history opt finalType -
          ∑ j ∈ Finset.Iic i,
            section6OptRevenueByFinalType I history opt finalType j) /
          (k : ℝ) ≤
        section6AggregateSlabSpend k I finalSpend i := by
  intro i
  have hkReal : 0 < (k : ℝ) := by exact_mod_cast hk
  have htail :=
    section6OptRevenueTail_le_later_budgets
      I history opt finalType hoptFeasible i
  have htailDiv :
      (section6OptRevenueTotalByType I history opt finalType -
          ∑ j ∈ Finset.Iic i,
            section6OptRevenueByFinalType I history opt finalType j) /
          (k : ℝ) ≤
        (∑ a ∈ (Finset.univ : Finset Advertiser).filter
          (fun a => i < finalType a), I.budget a) / (k : ℝ) :=
    (div_le_div_iff_of_pos_right hkReal).2 htail
  calc
    (section6OptRevenueTotalByType I history opt finalType -
          ∑ j ∈ Finset.Iic i,
            section6OptRevenueByFinalType I history opt finalType j) /
          (k : ℝ) ≤
        (∑ a ∈ (Finset.univ : Finset Advertiser).filter
          (fun a => i < finalType a), I.budget a) / (k : ℝ) := htailDiv
    _ = ∑ a : Advertiser,
        if i < finalType a then I.budget a / (k : ℝ) else 0 := by
          rw [Finset.sum_div]
          simp only [Finset.sum_filter]
    _ ≤ ∑ a : Advertiser,
        section6BidderSlabSpend k I finalSpend i a := by
          exact Finset.sum_le_sum fun a _ => by
            by_cases ha : i < finalType a
            · simpa [ha] using
                (section6BidderSlabSpend_eq_budget_div_of_lt_finalType
                  hk I hbudget finalSpend finalType hfinalType i a ha).ge
            · simpa [ha] using
                section6BidderSlabSpend_nonnegative
                  I hbudget finalSpend i a
    _ = section6AggregateSlabSpend k I finalSpend i := rfl

/--
The Section 6 weighted relation follows from the same query-fiber accounting
used in Lemma 7 when the final-slab error is zero.
-/
theorem section6_weighted_alpha_beta_of_query_accounting
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
    (∑ i : m, psi i * alpha i) ≤
      ∑ i : m, psi i * beta i := by
  have h := MSVV07SourceLemmas.lemma7_weighted_perturbation_bound
    psi alpha beta opt alg queryType querySlab 0
    htradeoff_sum hopt_accounting (by simpa using halg_accounting)
  simpa [mul_sub, Finset.sum_sub_distrib] using h

/--
Under the equal-unit-budget normalization used before Section 6's
heterogeneous-budget extension, the paper's original small-bids condition also
bounds the all-bidders next-price charge by the winner's budget fraction.
-/
theorem section6_next_highest_bid_all_small_bids_of_equal_unit_budgets
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query) {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hunit : EqualUnitBudgets I)
    (hsmall : paperSmallBids I epsilon) :
    ∀ a q,
      Proof.section6_next_highest_bid_all I a q ≤ epsilon * I.budget a := by
  classical
  intro a q
  unfold Proof.section6_next_highest_bid_all
  let others : Finset Advertiser := (Finset.univ : Finset Advertiser).erase a
  by_cases h : others.Nonempty
  · have hsup :
        others.sup' h (fun b => I.bid b q) ≤ epsilon := by
      apply Finset.sup'_le h
      intro b hb
      simpa [hunit b] using hsmall b q
    simpa [others, h, hunit a] using max_le hepsilon hsup
  · simp [others, h, hunit a, hepsilon]

/--
The same equal-unit-budget argument applies after filtering the competing bids
to the bidders that are alive at the current query.
-/
theorem section6_next_highest_bid_alive_small_bids_of_equal_unit_budgets
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query)
    (alive : Advertiser → Query → Prop) [∀ a q, Decidable (alive a q)]
    {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hunit : EqualUnitBudgets I)
    (hsmall : paperSmallBids I epsilon) :
    ∀ a q,
      Proof.section6_next_highest_bid_alive I alive a q ≤
        epsilon * I.budget a := by
  classical
  intro a q
  unfold Proof.section6_next_highest_bid_alive
  let others : Finset Advertiser :=
    ((Finset.univ : Finset Advertiser).erase a).filter fun b => alive b q
  by_cases h : others.Nonempty
  · have hsup :
        others.sup' h (fun b => I.bid b q) ≤ epsilon := by
      apply Finset.sup'_le h
      intro b hb
      simpa [hunit b] using hsmall b q
    simpa [others, h, hunit a] using max_le hepsilon hsup
  · simp [others, h, hunit a, hepsilon]

/-- The all-alive specialization makes the alive next-price charge equal the all-bidder charge. -/
theorem section6_all_alive_next_price_reduces_to_all_bidders
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query) (a : Advertiser) (q : Query) :
    Proof.section6_next_highest_bid_alive I (fun _ _ => True) a q =
      Proof.section6_next_highest_bid_all I a q := by
  classical
  unfold Proof.section6_next_highest_bid_alive Proof.section6_next_highest_bid_all
  simp

/-! ## Section 8: proposals as definitions, not proved guarantees -/

/-- A finite switching-distribution day: each time belongs to a regime with a fixed query PMF. -/
structure SwitchingQueryDistribution (Time Regime Query : Type*) where
  regimeAt : Time → Regime
  queryDistribution : Regime → PMF Query

/--
The fixed query distribution in force at a particular time.  Switching the
regime changes this PMF; within a regime the PMF is unchanged.
-/
noncomputable def SwitchingQueryDistribution.queryDistributionAt
    {Time Regime Query : Type*}
    (M : SwitchingQueryDistribution Time Regime Query) (time : Time) :
    PMF Query :=
  M.queryDistribution (M.regimeAt time)

/-- Paper proposal: run Balance after multiplying each advertiser's bids by its weight. -/
noncomputable def runWeightedBidProposal
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (I : PaperInstance Advertiser Query) (weight : Advertiser → ℝ)
    (history : List Query) : OccurrenceState Advertiser Query :=
  runBalanceOccurrences (I.withAdvertiserWeights weight) history

/-- One window of the Section 8 up/down weight-adjustment heuristic. -/
noncomputable def updateWeightAfterWindow
    (step : ℝ) (weight spent fairShare : ℝ) : ℝ :=
  if spent < fairShare then weight + step
  else if fairShare < spent then max 0 (weight - step)
  else weight

/--
Repeat the Section 8 weight-adjustment heuristic after each time window.  Each
pair records the bidder's spend and fair-share target in the next window.
-/
noncomputable def updateWeightAfterWindows (step : ℝ) :
    ℝ → List (ℝ × ℝ) → ℝ
  | weight, [] => weight
  | weight, (spent, fairShare) :: windows =>
      updateWeightAfterWindows step
        (updateWeightAfterWindow step weight spent fairShare) windows

/--
The source-faithful one-window heuristic relation: underspending raises the
weight, overspending lowers it, and exact fair-share spending leaves it fixed.
The paper does not specify a step size or a zero clamp.
-/
def IsWeightAdjustment
    (weight spent fairShare nextWeight : ℝ) : Prop :=
  (spent < fairShare ∧ weight < nextWeight) ∨
    (fairShare < spent ∧ nextWeight < weight) ∨
    (spent = fairShare ∧ nextWeight = weight)

/-- Repeat the source's direction-only adjustment relation after every window. -/
def IsRepeatedWeightAdjustment : ℝ → List (ℝ × ℝ) → ℝ → Prop
  | weight, [], finalWeight => finalWeight = weight
  | weight, (spent, fairShare) :: windows, finalWeight =>
      ∃ nextWeight,
        IsWeightAdjustment weight spent fairShare nextWeight ∧
          IsRepeatedWeightAdjustment nextWeight windows finalWeight

/-- Every finite window history admits at least one source-faithful adjustment path. -/
theorem exists_repeated_weight_adjustment
    (weight : ℝ) (windows : List (ℝ × ℝ)) :
    ∃ finalWeight, IsRepeatedWeightAdjustment weight windows finalWeight := by
  induction windows generalizing weight with
  | nil =>
      exact ⟨weight, rfl⟩
  | cons window windows ih =>
      rcases window with ⟨spent, fairShare⟩
      by_cases hunder : spent < fairShare
      · obtain ⟨finalWeight, hpath⟩ := ih (weight + 1)
        exact ⟨finalWeight, weight + 1, ⟨Or.inl ⟨hunder, by linarith⟩, hpath⟩⟩
      · by_cases hover : fairShare < spent
        · obtain ⟨finalWeight, hpath⟩ := ih (weight - 1)
          exact
            ⟨finalWeight, weight - 1,
              ⟨Or.inr (Or.inl ⟨hover, by linarith⟩), hpath⟩⟩
        · have hequal : spent = fairShare := le_antisymm
            (le_of_not_gt hover) (le_of_not_gt hunder)
          obtain ⟨finalWeight, hpath⟩ := ih weight
          exact
            ⟨finalWeight, weight,
              ⟨Or.inr (Or.inr ⟨hequal, rfl⟩), hpath⟩⟩

/-- Advertiser representatives used by the replicated-RANKING proposal. -/
abbrev Representative (Advertiser : Type*) (m : ℕ) := Advertiser × Fin m

/-- Replace each advertiser by `m` equal-budget representatives with identical bids. -/
noncomputable def replicatedInstance
    (m : ℕ) (I : PaperInstance Advertiser Query) :
    PaperInstance (Representative Advertiser m) Query where
  budget r := I.budget r.1 / (m : ℝ)
  bid r q := I.bid r.1 q

/-- Generalized-RANKING score on a replicated advertiser population. -/
noncomputable def replicatedRankingScore
    (I : PaperInstance Advertiser Query)
    (rankWeight : Representative Advertiser m → ℝ)
    (r : Representative Advertiser m) (q : Query) : ℝ :=
  I.bid r.1 q * rankWeight r

/-- The actual finite maximum scan used by one replicated-RANKING decision. -/
noncomputable def replicatedRankingScan
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (m : ℕ) (I : PaperInstance Advertiser Query)
    (rankWeight : Representative Advertiser m → ℝ)
    (S : OccurrenceState (Representative Advertiser m) Query) (q : Query) :
    FiniteMaxScanResult (Representative Advertiser m) :=
  finiteMaxScan
    (occurrenceCanAssign (replicatedInstance m I) S q)
    (fun r => replicatedRankingScore I rankWeight r q)
    (Finset.univ : Finset (Representative Advertiser m)).toList

/-- One occurrence step of the replicated-RANKING proposal. -/
noncomputable def replicatedRankingStep
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (m : ℕ) (I : PaperInstance Advertiser Query)
    (rankWeight : Representative Advertiser m → ℝ)
    (S : OccurrenceState (Representative Advertiser m) Query) (q : Query) :
    OccurrenceState (Representative Advertiser m) Query :=
  applyScanDecision (replicatedInstance m I) S q
    (replicatedRankingScan m I rankWeight S q)

/--
Run the generalized RANKING proposal on every query occurrence, conditional on
the sampled rank weights.  The source's simulation and competitive-factor
discussion remains heuristic and is not asserted here.
-/
noncomputable def runReplicatedRankingProposal
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (m : ℕ) (I : PaperInstance Advertiser Query)
    (rankWeight : Representative Advertiser m → ℝ)
    (history : List Query) :
    OccurrenceState (Representative Advertiser m) Query :=
  runOccurrencesFrom (replicatedRankingStep m I rankWeight)
    initialOccurrenceState history

/-- A representative has exhausted its equal budget in a completed run. -/
def representativeBudgetExhausted
    {Advertiser Query : Type*}
    (m : ℕ) (I : PaperInstance Advertiser Query)
    (S : OccurrenceState (Representative Advertiser m) Query)
    (r : Representative Advertiser m) : Prop :=
  S.spent r = (replicatedInstance m I).budget r

/--
The Section 8 replicated-RANKING exhaustion-order heuristic, made explicit as
a predicate rather than claimed as a proved performance guarantee: within one
original bidder's representatives, exhaustion at a later rank entails
exhaustion at every earlier rank.
-/
def replicatedRankingExhaustionInRankOrder
    {Advertiser Query : Type*}
    (m : ℕ) (I : PaperInstance Advertiser Query)
    (rank : Representative Advertiser m → ℕ)
    (S : OccurrenceState (Representative Advertiser m) Query) : Prop :=
  ∀ r r', r.1 = r'.1 → rank r ≤ rank r' →
    representativeBudgetExhausted m I S r' →
      representativeBudgetExhausted m I S r

/-- Unfold the explicit Section 8 exhaustion-order heuristic. -/
theorem replicatedRankingExhaustionInRankOrder_iff
    {Advertiser Query : Type*}
    (m : ℕ) (I : PaperInstance Advertiser Query)
    (rank : Representative Advertiser m → ℕ)
    (S : OccurrenceState (Representative Advertiser m) Query) :
    replicatedRankingExhaustionInRankOrder m I rank S ↔
      ∀ r r', r.1 = r'.1 → rank r ≤ rank r' →
        representativeBudgetExhausted m I S r' →
          representativeBudgetExhausted m I S r := by
  rfl

/-- A selected representative is affordable and maximizes the rank-scaled bid. -/
theorem replicatedRankingScan_winner_spec
    {Advertiser Query : Type*} [Fintype Advertiser] [DecidableEq Advertiser]
    (m : ℕ) (I : PaperInstance Advertiser Query)
    (rankWeight : Representative Advertiser m → ℝ)
    (S : OccurrenceState (Representative Advertiser m) Query) (q : Query)
    (r : Representative Advertiser m)
    (hchoice : (replicatedRankingScan m I rankWeight S q).winner = some r) :
    occurrenceCanAssign (replicatedInstance m I) S q r ∧
      ∀ r', occurrenceCanAssign (replicatedInstance m I) S q r' →
        replicatedRankingScore I rankWeight r' q ≤
          replicatedRankingScore I rankWeight r q := by
  classical
  have hspec :=
    (finiteMaxScan_winner_spec
      (occurrenceCanAssign (replicatedInstance m I) S q)
      (fun r => replicatedRankingScore I rankWeight r q)
      (Finset.univ : Finset (Representative Advertiser m)).toList).2 r hchoice
  exact ⟨hspec.2.1, fun r' hr' => hspec.2.2 r' (by simp) hr'⟩

/-! ## Section 7 / Theorem 9: source intermediate formulas -/

/-- The epsilon bid in a permuted hard instance, indexed by round and bidder position. -/
noncomputable def theorem9RoundBid
    (N : ℕ) (epsilon : ℝ) (permutation : Equiv.Perm (Fin N))
    (round bidder : Fin N) : ℝ :=
  if permutation bidder ∈ theorem9ActualEligibleBidders N permutation round then
    epsilon
  else 0

/-- In zero-based indexing, exactly positions `round,...,N-1` bid epsilon. -/
theorem theorem9RoundBid_formula
    (N : ℕ) (epsilon : ℝ) (permutation : Equiv.Perm (Fin N))
    (round bidder : Fin N) :
    theorem9RoundBid N epsilon permutation round bidder =
      if (round : ℕ) ≤ (bidder : ℕ) then epsilon else 0 := by
  classical
  unfold theorem9RoundBid
  simp [mem_theorem9ActualEligibleBidders]

/-- Concrete `N`-round, `m`-occurrences-per-round hard AdWords instance. -/
noncomputable def theorem9HardInstance
    (N m : ℕ) (epsilon : ℝ) (permutation : Equiv.Perm (Fin N)) :
    PaperInstance (Fin N) (Fin N × Fin m) where
  budget _ := 1
  bid bidder q :=
    if bidder ∈ theorem9ActualEligibleBidders N permutation q.1 then epsilon else 0

/-- The source offline witness assigns every occurrence of round `i` to `permutation i`. -/
def theorem9HardOfflineAssignment
    (N m : ℕ) (permutation : Equiv.Perm (Fin N)) :
    PaperAssignment (Fin N) (Fin N × Fin m) :=
  fun q => some (permutation q.1)

/-- The displayed offline witness earns `N*m*epsilon`. -/
theorem theorem9HardOfflineAssignment_revenue
    (N m : ℕ) (epsilon : ℝ) (permutation : Equiv.Perm (Fin N)) :
    paperRevenue (theorem9HardInstance N m epsilon permutation)
        (theorem9HardOfflineAssignment N m permutation) =
      (N : ℝ) * (m : ℝ) * epsilon := by
  classical
  unfold paperRevenue Proof.paperRevenue theorem9HardOfflineAssignment
    theorem9HardInstance
  simp [theorem9ActualEligibleBidders, theorem9EligibleBidders]

/-- Under the paper normalization `m*epsilon=1`, the offline witness earns `N`. -/
theorem theorem9HardOfflineAssignment_revenue_eq_N
    (N m : ℕ) (epsilon : ℝ) (permutation : Equiv.Perm (Fin N))
    (hround : (m : ℝ) * epsilon = 1) :
    paperRevenue (theorem9HardInstance N m epsilon permutation)
        (theorem9HardOfflineAssignment N m permutation) = (N : ℝ) := by
  rw [theorem9HardOfflineAssignment_revenue, mul_assoc, hround, mul_one]

/-- The paper's `q_ij`: expected fraction of round `i` allocated to position `j`. -/
noncomputable def theorem9ExpectedRoundAllocation
    (N : ℕ) (algorithm : BMatchingIntegralPrefixAlgorithm N)
    (round bidder : Fin N) : ℝ :=
  pmfExp (uniformPermutationDistribution N) fun permutation =>
    BMatchingIntegralPrefixAlgorithm.prefixAllocation algorithm
      (theorem9ObservedPrefix N permutation round)
      round (permutation bidder)

/-- A finite certificate specialized to the concrete integral prefix algorithms. -/
noncomputable def theorem9IntegralFiniteCertificate (N : ℕ) :
    BMatchingFeasibleObservedPrefixAllocationRevenueCertificate
      N (BMatchingIntegralPrefixAlgorithm N) 1 where
  normalizedRevenue := fun algorithm permutation =>
    (∑ bidder : Fin N,
      min 1
        (∑ round : Fin N,
          BMatchingIntegralPrefixAlgorithm.prefixAllocation algorithm
            (theorem9ObservedPrefix N permutation round)
            round (permutation bidder))) / (N : ℝ)
  prefixAllocation := fun algorithm obs round bidder =>
    BMatchingIntegralPrefixAlgorithm.prefixAllocation algorithm obs round bidder
  normalizedRevenue_le_cappedPrefixAllocationSpend := by
    intro algorithm permutation
    exact le_rfl
  prefixAllocation_zero_of_not_visible := by
    intro algorithm obs round bidder hnot
    exact BMatchingIntegralPrefixAlgorithm.prefixAllocation_zero_of_not_visible
      algorithm obs round bidder hnot
  prefixAllocation_sum_le_one := by
    intro algorithm obs round
    exact BMatchingIntegralPrefixAlgorithm.prefixAllocation_sum_le_one
      algorithm obs round
  revenueBound_le_ratio := by
    by_cases hN : 0 < N
    · exact theorem9NormalizedRevenueUpperBound_le_one hN
    · have hN0 : N = 0 := Nat.eq_zero_of_not_pos hN
      subst N
      norm_num [theorem9NormalizedRevenueUpperBound]

/-- The conversion chain that proves the paper's permutation-symmetry `q_ij` bound. -/
noncomputable def theorem9IntegralRoundCertificate (N : ℕ) :
    BMatchingRoundAllocationRevenueCertificate
      N (BMatchingIntegralPrefixAlgorithm N) 1 :=
  (((theorem9IntegralFiniteCertificate N).toObservedPrefixAllocationRevenueCertificate
      ).toRelabelSymmetricPointwiseAllocationRevenueCertificate
      ).toSymmetricPointwiseAllocationRevenueCertificate
      |>.toPointwiseAllocationRevenueCertificate
      |>.toRoundAllocationRevenueCertificate

/--
Theorem 9's intermediate formula:
`E_pi[q_ij] <= 1/(N-i+1)` for `j >= i`, and it is zero for `j < i`, expressed
in zero-based indices as denominator `N-i`.
-/
theorem theorem9_expected_round_allocation_bound
    (N : ℕ) (algorithm : BMatchingIntegralPrefixAlgorithm N)
    (round bidder : Fin N) :
    theorem9ExpectedRoundAllocation N algorithm round bidder ≤
      if (round : ℕ) ≤ (bidder : ℕ) then
        1 / ((N - (round : ℕ) : ℕ) : ℝ)
      else 0 := by
  change
    (theorem9IntegralRoundCertificate N).expectedRoundBidderAllocation
        algorithm round bidder ≤ _
  exact
    (theorem9IntegralRoundCertificate N).expectedRoundBidderAllocation_le
      algorithm round bidder

/-- An ineligible bidder has exactly zero expected allocation in that round. -/
theorem theorem9_expected_round_allocation_zero_of_ineligible
    (N : ℕ) (algorithm : BMatchingIntegralPrefixAlgorithm N)
    (round bidder : Fin N) (hineligible : ¬ (round : ℕ) ≤ (bidder : ℕ)) :
    theorem9ExpectedRoundAllocation N algorithm round bidder = 0 := by
  unfold theorem9ExpectedRoundAllocation
  calc
    pmfExp (uniformPermutationDistribution N)
        (fun permutation =>
          BMatchingIntegralPrefixAlgorithm.prefixAllocation algorithm
            (theorem9ObservedPrefix N permutation round)
            round (permutation bidder)) =
        pmfExp (uniformPermutationDistribution N) (fun _ => 0) := by
          apply pmfExp_congr
          intro permutation
          apply
            BMatchingIntegralPrefixAlgorithm.prefixAllocation_zero_of_not_visible
          simp [theorem9ObservedPrefix,
            theorem9ActualEligibleBidders_not_mem_of_not_eligible hineligible]
    _ = 0 := pmfExp_zero _

/-- Summing the expected round bounds gives the paper's capped bidder-spend bound. -/
theorem theorem9_expected_bidder_spend_le_harmonic_bound
    (N : ℕ) (algorithm : BMatchingIntegralPrefixAlgorithm N)
    (bidder : Fin N) :
    min 1
        (∑ round : Fin N,
          theorem9ExpectedRoundAllocation N algorithm round bidder) ≤
      theorem9BidderSpendUpperBound N bidder := by
  unfold theorem9BidderSpendUpperBound
  exact min_le_min_left 1
    (Finset.sum_le_sum fun round _ =>
      theorem9_expected_round_allocation_bound N algorithm round bidder)

/--
After averaging over the hard permutation distribution, every deterministic
integral prefix algorithm is bounded by the summed harmonic cap.
-/
theorem theorem9_expected_normalized_revenue_le_harmonic_bound
    (N : ℕ) (algorithm : BMatchingIntegralPrefixAlgorithm N) :
    pmfExp (uniformPermutationDistribution N)
        (fun permutation =>
          (theorem9IntegralRoundCertificate N).normalizedRevenue
            algorithm permutation) ≤
      theorem9NormalizedRevenueUpperBound N := by
  exact
    (theorem9IntegralRoundCertificate N).toRevenueBoundCertificate
      |>.deterministicAverage_le_revenueBound algorithm

/-- Paper-facing expansion of the capped harmonic spend bound for bidder `j`. -/
theorem theorem9_harmonic_spend_formula (N : ℕ) (bidder : Fin N) :
    theorem9BidderSpendUpperBound N bidder =
      min 1
        (∑ round : Fin N,
          if (round : ℕ) ≤ (bidder : ℕ) then
            1 / ((N - (round : ℕ) : ℕ) : ℝ)
          else 0) := by
  rfl

/-- Summing the bidder caps and dividing by OPT `N` gives the finite revenue bound. -/
theorem theorem9_harmonic_revenue_formula (N : ℕ) :
    theorem9NormalizedRevenueUpperBound N =
      (∑ bidder : Fin N, theorem9BidderSpendUpperBound N bidder) / (N : ℝ) := by
  rfl

/--
Uncapped harmonic spend accumulated before zero-based round `r` in the nested
suffix instance.
-/
noncomputable def fluidHarmonicBefore (N r : ℕ) : ℝ :=
  ∑ round ∈ Finset.range r, 1 / ((N - round : ℕ) : ℝ)

/-- Capped common spend of every bidder still eligible before round `r`. -/
noncomputable def fluidCappedSpendBefore (N r : ℕ) : ℝ :=
  min 1 (fluidHarmonicBefore N r)

/-- Equal payment assigned to each still-eligible bidder during round `r`. -/
noncomputable def fluidBalanceRoundIncrement (N r : ℕ) : ℝ :=
  fluidCappedSpendBefore N (r + 1) - fluidCappedSpendBefore N r

/-- Fluid allocation in the identity-permutation nested suffix-round family. -/
noncomputable def fluidBalanceAllocation
    (N : ℕ) (round bidder : Fin N) : ℝ :=
  if (round : ℕ) ≤ (bidder : ℕ) then
    fluidBalanceRoundIncrement N round
  else 0

/-- Spend state immediately before a round; bidders already removed retain final spend. -/
noncomputable def fluidBalanceSpentBefore
    (N : ℕ) (round bidder : Fin N) : ℝ :=
  if (round : ℕ) ≤ (bidder : ℕ) then
    fluidCappedSpendBefore N round
  else
    fluidCappedSpendBefore N ((bidder : ℕ) + 1)

/-- Final spend of one bidder in the explicit fluid execution. -/
noncomputable def fluidBalanceFinalSpend (N : ℕ) (bidder : Fin N) : ℝ :=
  fluidCappedSpendBefore N ((bidder : ℕ) + 1)

theorem fluidHarmonicBefore_succ (N r : ℕ) :
    fluidHarmonicBefore N (r + 1) =
      fluidHarmonicBefore N r + 1 / ((N - r : ℕ) : ℝ) := by
  simp [fluidHarmonicBefore, Finset.sum_range_succ]

theorem fluidHarmonicBefore_nonneg (N r : ℕ) :
    0 ≤ fluidHarmonicBefore N r := by
  unfold fluidHarmonicBefore
  exact Finset.sum_nonneg fun i _ => by positivity

theorem fluidCappedSpendBefore_nonneg (N r : ℕ) :
    0 ≤ fluidCappedSpendBefore N r := by
  exact le_min (by norm_num) (fluidHarmonicBefore_nonneg N r)

theorem fluidCappedSpendBefore_le_one (N r : ℕ) :
    fluidCappedSpendBefore N r ≤ 1 := by
  exact min_le_left _ _

theorem fluidCappedSpendBefore_mono_step (N r : ℕ) :
    fluidCappedSpendBefore N r ≤ fluidCappedSpendBefore N (r + 1) := by
  unfold fluidCappedSpendBefore
  apply min_le_min (le_refl 1)
  rw [fluidHarmonicBefore_succ]
  have hterm : 0 ≤ 1 / ((N - r : ℕ) : ℝ) := by positivity
  linarith

theorem fluidBalanceRoundIncrement_nonneg (N r : ℕ) :
    0 ≤ fluidBalanceRoundIncrement N r := by
  unfold fluidBalanceRoundIncrement
  exact sub_nonneg.mpr (fluidCappedSpendBefore_mono_step N r)

/-- Capping can only reduce the equal `1/(N-r)` uncapped round increment. -/
theorem fluidBalanceRoundIncrement_le_harmonic_step (N r : ℕ) :
    fluidBalanceRoundIncrement N r ≤ 1 / ((N - r : ℕ) : ℝ) := by
  let H := fluidHarmonicBefore N r
  let x := 1 / ((N - r : ℕ) : ℝ)
  have hx : 0 ≤ x := by
    dsimp [x]
    positivity
  have hsucc : fluidHarmonicBefore N (r + 1) = H + x := by
    simpa [H, x] using fluidHarmonicBefore_succ N r
  unfold fluidBalanceRoundIncrement fluidCappedSpendBefore
  rw [hsucc]
  change min 1 (H + x) - min 1 H ≤ x
  by_cases hH : 1 ≤ H
  · have hHx : 1 ≤ H + x := hH.trans (le_add_of_nonneg_right hx)
    rw [min_eq_left hHx, min_eq_left hH]
    linarith
  · have hHle : H ≤ 1 := le_of_not_ge hH
    by_cases hsum : H + x ≤ 1
    · rw [min_eq_right hsum, min_eq_right hHle]
      linarith
    · have hone_le : 1 ≤ H + x := le_of_not_ge hsum
      rw [min_eq_left hone_le, min_eq_right hHle]
      linarith

/-- The explicit allocation never assigns mass to a bidder outside the suffix. -/
theorem fluidBalanceAllocation_zero_of_ineligible
    (N : ℕ) (round bidder : Fin N)
    (h : ¬ (round : ℕ) ≤ (bidder : ℕ)) :
    fluidBalanceAllocation N round bidder = 0 := by
  simp [fluidBalanceAllocation, h]

/-- All active bidders have equal spend, hence each is a least-spent eligible bidder. -/
theorem fluidBalance_eligible_equal_least_spend
    (N : ℕ) (round bidder bidder' : Fin N)
    (hbidder : (round : ℕ) ≤ (bidder : ℕ))
    (hbidder' : (round : ℕ) ≤ (bidder' : ℕ)) :
    fluidBalanceSpentBefore N round bidder =
      fluidBalanceSpentBefore N round bidder' := by
  simp [fluidBalanceSpentBefore, hbidder, hbidder']

/-- Fluid allocations are nonnegative. -/
theorem fluidBalanceAllocation_nonneg
    (N : ℕ) (round bidder : Fin N) :
    0 ≤ fluidBalanceAllocation N round bidder := by
  unfold fluidBalanceAllocation
  split_ifs
  · exact fluidBalanceRoundIncrement_nonneg N round
  · exact le_rfl

/-- The eligible-cohort allocation is its cardinality times the common increment. -/
theorem fluidBalance_sum_eligible_eq_card_mul
    (N : ℕ) (round : Fin N) :
    (∑ bidder ∈ theorem9EligibleBidders N round,
      fluidBalanceAllocation N round bidder) =
      ((theorem9EligibleBidders N round).card : ℝ) *
        fluidBalanceRoundIncrement N round := by
  calc
    (∑ bidder ∈ theorem9EligibleBidders N round,
        fluidBalanceAllocation N round bidder) =
        ∑ _bidder ∈ theorem9EligibleBidders N round,
          fluidBalanceRoundIncrement N round := by
            apply Finset.sum_congr rfl
            intro bidder hbidder
            rw [fluidBalanceAllocation, if_pos
              ((mem_theorem9EligibleBidders N round bidder).mp hbidder)]
    _ = ((theorem9EligibleBidders N round).card : ℝ) *
        fluidBalanceRoundIncrement N round := by simp

/-- Each bidder's post-round spend remains within its unit budget. -/
theorem fluidBalance_budget_feasible
    (N : ℕ) (round bidder : Fin N) :
    fluidBalanceSpentBefore N round bidder +
        fluidBalanceAllocation N round bidder ≤ 1 := by
  by_cases h : (round : ℕ) ≤ (bidder : ℕ)
  · have hcap := fluidCappedSpendBefore_le_one N ((round : ℕ) + 1)
    simpa [fluidBalanceSpentBefore, fluidBalanceAllocation,
      fluidBalanceRoundIncrement, h] using hcap
  · have hcap := fluidCappedSpendBefore_le_one N ((bidder : ℕ) + 1)
    simpa [fluidBalanceSpentBefore, fluidBalanceAllocation, h] using hcap

/-- At most one unit of query mass is allocated in every round. -/
theorem fluidBalance_round_allocation_conservation
    (N : ℕ) (round : Fin N) :
    (∑ bidder ∈ theorem9EligibleBidders N round,
      fluidBalanceAllocation N round bidder) ≤ 1 := by
  have hcount : 0 < N - (round : ℕ) := Nat.sub_pos_of_lt round.isLt
  have hcountReal : 0 < ((N - (round : ℕ) : ℕ) : ℝ) := by
    exact_mod_cast hcount
  have hincrement :=
    fluidBalanceRoundIncrement_le_harmonic_step N (round : ℕ)
  calc
    (∑ bidder ∈ theorem9EligibleBidders N round,
        fluidBalanceAllocation N round bidder) =
        ((N - (round : ℕ) : ℕ) : ℝ) *
          fluidBalanceRoundIncrement N round := by
            rw [← theorem9EligibleBidders_card]
            exact fluidBalance_sum_eligible_eq_card_mul N round
    _ ≤ ((N - (round : ℕ) : ℕ) : ℝ) *
        (1 / ((N - (round : ℕ) : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hincrement hcountReal.le
    _ = 1 := by field_simp [ne_of_gt hcountReal]

/--
Every fluid round either allocates its full unit query mass or leaves every
eligible bidder exactly saturated after the round.  Thus any discard is caused
by budget exhaustion, not by an externally stipulated slack variable.
-/
theorem fluidBalance_round_full_or_all_eligible_saturated
    (N : ℕ) (round : Fin N) :
    (∑ bidder ∈ theorem9EligibleBidders N round,
      fluidBalanceAllocation N round bidder) = 1 ∨
    ∀ bidder : Fin N, bidder ∈ theorem9EligibleBidders N round →
      fluidBalanceSpentBefore N round bidder +
        fluidBalanceAllocation N round bidder = 1 := by
  have hcount : 0 < N - (round : ℕ) := Nat.sub_pos_of_lt round.isLt
  have hcountReal : 0 < ((N - (round : ℕ) : ℕ) : ℝ) := by
    exact_mod_cast hcount
  let H := fluidHarmonicBefore N (round : ℕ)
  let x := 1 / ((N - (round : ℕ) : ℕ) : ℝ)
  have hx : 0 < x := by
    dsimp [x]
    positivity
  have hsucc : fluidHarmonicBefore N ((round : ℕ) + 1) = H + x := by
    simpa [H, x] using fluidHarmonicBefore_succ N (round : ℕ)
  by_cases hfull : H + x ≤ 1
  · left
    have hH : H ≤ 1 := le_trans (le_add_of_nonneg_right hx.le) hfull
    have hincrement : fluidBalanceRoundIncrement N round = x := by
      unfold fluidBalanceRoundIncrement fluidCappedSpendBefore
      rw [hsucc]
      change min 1 (H + x) - min 1 H = x
      rw [min_eq_right hfull, min_eq_right hH]
      ring
    calc
      (∑ bidder ∈ theorem9EligibleBidders N round,
          fluidBalanceAllocation N round bidder) =
          ((N - (round : ℕ) : ℕ) : ℝ) *
            fluidBalanceRoundIncrement N round := by
              rw [← theorem9EligibleBidders_card]
              exact fluidBalance_sum_eligible_eq_card_mul N round
      _ = ((N - (round : ℕ) : ℕ) : ℝ) * x := by rw [hincrement]
      _ = 1 := by
        dsimp [x]
        field_simp [ne_of_gt hcountReal]
  · right
    have hsaturated : fluidCappedSpendBefore N ((round : ℕ) + 1) = 1 := by
      unfold fluidCappedSpendBefore
      rw [hsucc]
      exact min_eq_left (le_of_not_ge hfull)
    intro bidder hbidder
    have heligible : (round : ℕ) ≤ (bidder : ℕ) :=
      (mem_theorem9EligibleBidders N round bidder).mp hbidder
    simpa [fluidBalanceSpentBefore, fluidBalanceAllocation,
      fluidBalanceRoundIncrement, heligible] using hsaturated

/-- Strictly subunit allocation implies saturation of every eligible bidder. -/
theorem fluidBalance_no_discard_unless_all_eligible_saturated
    (N : ℕ) (round : Fin N)
    (hdiscard :
      (∑ bidder ∈ theorem9EligibleBidders N round,
        fluidBalanceAllocation N round bidder) < 1) :
    ∀ bidder : Fin N, bidder ∈ theorem9EligibleBidders N round →
      fluidBalanceSpentBefore N round bidder +
        fluidBalanceAllocation N round bidder = 1 := by
  rcases fluidBalance_round_full_or_all_eligible_saturated N round with hfull | hsaturated
  · linarith
  · exact hsaturated

/-- The round increments telescope to the stated final spend of every bidder. -/
theorem fluidBalance_finalSpend_eq_sum_allocation
    (N : ℕ) (bidder : Fin N) :
    fluidBalanceFinalSpend N bidder =
      ∑ round : Fin N, fluidBalanceAllocation N round bidder := by
  let f : ℕ → ℝ := fluidCappedSpendBefore N
  have hfin_to_nat :
      (∑ round : Fin N, fluidBalanceAllocation N round bidder) =
        ∑ round ∈ Finset.range N,
          if round ≤ (bidder : ℕ) then f (round + 1) - f round else 0 := by
    symm
    simpa [fluidBalanceAllocation, fluidBalanceRoundIncrement, f] using
      (Finset.sum_range
        (n := N)
        (fun round : ℕ =>
          if round ≤ (bidder : ℕ) then f (round + 1) - f round else 0))
  have hprefix_set :
      (Finset.range N).filter (fun round => round ≤ (bidder : ℕ)) =
        Finset.range ((bidder : ℕ) + 1) := by
    ext round
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · intro hround
      exact Nat.lt_succ_of_le hround.2
    · intro hround
      have hle : round ≤ (bidder : ℕ) := Nat.le_of_lt_succ hround
      exact ⟨lt_of_le_of_lt hle bidder.isLt, hle⟩
  rw [hfin_to_nat, ← Finset.sum_filter, hprefix_set]
  rw [Finset.sum_range_sub]
  simp [fluidBalanceFinalSpend, f, fluidCappedSpendBefore,
    fluidHarmonicBefore]

/-- Nat-indexed telescoping prefix used to connect decision-time state to prior allocations. -/
theorem fluidBalance_natPrefix_telescope
    (N r : ℕ) (bidder : Fin N) :
    (∑ round ∈ Finset.range r,
      if round ≤ (bidder : ℕ) then
        fluidBalanceRoundIncrement N round
      else 0) =
      fluidCappedSpendBefore N (min r ((bidder : ℕ) + 1)) := by
  have hset :
      (Finset.range r).filter (fun round => round ≤ (bidder : ℕ)) =
        Finset.range (min r ((bidder : ℕ) + 1)) := by
    ext round
    simp
  rw [← Finset.sum_filter, hset]
  unfold fluidBalanceRoundIncrement
  rw [Finset.sum_range_sub]
  simp [fluidCappedSpendBefore, fluidHarmonicBefore]

/--
At every decision time, `spentBefore` is exactly the sum of this bidder's
allocations in earlier rounds; it is not an independently stipulated state.
-/
theorem fluidBalance_spentBefore_eq_prior_allocations
    (N : ℕ) (round bidder : Fin N) :
    fluidBalanceSpentBefore N round bidder =
      ∑ previous : Fin N,
        if (previous : ℕ) < (round : ℕ) then
          fluidBalanceAllocation N previous bidder
        else 0 := by
  have hfin_to_nat :
      (∑ previous : Fin N,
        if (previous : ℕ) < (round : ℕ) then
          fluidBalanceAllocation N previous bidder
        else 0) =
      ∑ previous ∈ Finset.range N,
        if previous < (round : ℕ) then
          (if previous ≤ (bidder : ℕ) then
            fluidBalanceRoundIncrement N previous else 0)
        else 0 := by
    symm
    simpa [fluidBalanceAllocation] using
      (Finset.sum_range
        (n := N)
        (fun previous : ℕ =>
          if previous < (round : ℕ) then
            (if previous ≤ (bidder : ℕ) then
              fluidBalanceRoundIncrement N previous else 0)
          else 0))
  have hround_set :
      (Finset.range N).filter (fun previous => previous < (round : ℕ)) =
        Finset.range (round : ℕ) := by
    ext previous
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · intro h
      exact h.2
    · intro h
      exact ⟨lt_trans h round.isLt, h⟩
  rw [hfin_to_nat, ← Finset.sum_filter, hround_set]
  rw [fluidBalance_natPrefix_telescope]
  by_cases h : (round : ℕ) ≤ (bidder : ℕ)
  · have hmin : min (round : ℕ) ((bidder : ℕ) + 1) = round := by
      omega
    simp [fluidBalanceSpentBefore, h, hmin]
  · have hmin : min (round : ℕ) ((bidder : ℕ) + 1) =
        (bidder : ℕ) + 1 := by
      omega
    simp [fluidBalanceSpentBefore, h, hmin]

/-- Consecutive round states update by exactly the current round allocation. -/
theorem fluidBalance_state_update
    (N : ℕ) (round next bidder : Fin N)
    (hnext : (next : ℕ) = (round : ℕ) + 1) :
    fluidBalanceSpentBefore N next bidder =
      fluidBalanceSpentBefore N round bidder +
        fluidBalanceAllocation N round bidder := by
  by_cases hcur : (round : ℕ) ≤ (bidder : ℕ)
  · by_cases hnxt : (next : ℕ) ≤ (bidder : ℕ)
    · have hnot : ¬ (bidder : ℕ) ≤ (round : ℕ) := by omega
      have hnotFin : ¬ bidder ≤ round := by
        intro h
        exact hnot h
      simp [fluidBalanceSpentBefore, fluidBalanceAllocation,
        fluidBalanceRoundIncrement, hcur, hnxt, hnext, hnot, hnotFin]
    · have hb : (bidder : ℕ) = (round : ℕ) := by omega
      simp [fluidBalanceSpentBefore, fluidBalanceAllocation,
        fluidBalanceRoundIncrement, hcur, hnxt, hnext, hb]
  · have hnxt : ¬ (next : ℕ) ≤ (bidder : ℕ) := by omega
    simp [fluidBalanceSpentBefore, fluidBalanceAllocation, hcur, hnxt]

/-- The explicit final spend is the paper's capped harmonic prefix. -/
theorem fluidBalance_finalSpend_eq_harmonicCap
    (N : ℕ) (bidder : Fin N) :
    fluidBalanceFinalSpend N bidder = theorem9BidderSpendUpperBound N bidder := by
  let g : ℕ → ℝ := fun round => 1 / ((N - round : ℕ) : ℝ)
  have hfin_to_nat :
      (∑ round : Fin N,
        if (round : ℕ) ≤ (bidder : ℕ) then g round else 0) =
        ∑ round ∈ Finset.range N,
          if round ≤ (bidder : ℕ) then g round else 0 := by
    symm
    simpa using
      (Finset.sum_range
        (n := N)
        (fun round : ℕ =>
          if round ≤ (bidder : ℕ) then g round else 0))
  have hprefix_set :
      (Finset.range N).filter (fun round => round ≤ (bidder : ℕ)) =
        Finset.range ((bidder : ℕ) + 1) := by
    ext round
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · intro hround
      exact Nat.lt_succ_of_le hround.2
    · intro hround
      have hle : round ≤ (bidder : ℕ) := Nat.le_of_lt_succ hround
      exact ⟨lt_of_le_of_lt hle bidder.isLt, hle⟩
  unfold fluidBalanceFinalSpend fluidCappedSpendBefore fluidHarmonicBefore
    theorem9BidderSpendUpperBound
  rw [hfin_to_nat, ← Finset.sum_filter, hprefix_set]

/--
A precise fluid BALANCE execution certificate for the nested suffix-round
family.  Its fields expose rather than assume the algorithmic invariants.
-/
structure FluidBalanceExecution (N : ℕ) where
  allocation : Fin N → Fin N → ℝ
  spentBefore : Fin N → Fin N → ℝ
  finalSpend : Fin N → ℝ
  zero_of_ineligible : ∀ (round bidder : Fin N),
    ¬ (round : ℕ) ≤ (bidder : ℕ) → allocation round bidder = 0
  eligible_equal_least_spend : ∀ (round bidder bidder' : Fin N),
    (round : ℕ) ≤ (bidder : ℕ) →
    (round : ℕ) ≤ (bidder' : ℕ) →
      spentBefore round bidder = spentBefore round bidder'
  allocation_nonneg : ∀ (round bidder : Fin N), 0 ≤ allocation round bidder
  budget_feasible : ∀ (round bidder : Fin N),
    spentBefore round bidder + allocation round bidder ≤ 1
  spentBefore_eq_prefix : ∀ (round bidder : Fin N),
    spentBefore round bidder =
      ∑ previous : Fin N,
        if (previous : ℕ) < (round : ℕ) then allocation previous bidder else 0
  state_update : ∀ (round next bidder : Fin N),
    (next : ℕ) = (round : ℕ) + 1 →
      spentBefore next bidder = spentBefore round bidder + allocation round bidder
  round_conservation : ∀ (round : Fin N),
    (∑ bidder ∈ theorem9EligibleBidders N round,
      allocation round bidder) ≤ 1
  work_conserving_or_saturated : ∀ (round : Fin N),
    (∑ bidder ∈ theorem9EligibleBidders N round,
      allocation round bidder) = 1 ∨
    ∀ bidder : Fin N, bidder ∈ theorem9EligibleBidders N round →
      spentBefore round bidder + allocation round bidder = 1
  finalSpend_eq_sum : ∀ bidder : Fin N,
    finalSpend bidder = ∑ round : Fin N, allocation round bidder

/-- The explicit water-filling construction satisfies the fluid BALANCE certificate. -/
noncomputable def nestedSuffixFluidBalanceExecution (N : ℕ) :
    FluidBalanceExecution N where
  allocation := fluidBalanceAllocation N
  spentBefore := fluidBalanceSpentBefore N
  finalSpend := fluidBalanceFinalSpend N
  zero_of_ineligible := fluidBalanceAllocation_zero_of_ineligible N
  eligible_equal_least_spend := fluidBalance_eligible_equal_least_spend N
  allocation_nonneg := fluidBalanceAllocation_nonneg N
  budget_feasible := fluidBalance_budget_feasible N
  spentBefore_eq_prefix := fluidBalance_spentBefore_eq_prior_allocations N
  state_update := fluidBalance_state_update N
  round_conservation := fluidBalance_round_allocation_conservation N
  work_conserving_or_saturated :=
    fluidBalance_round_full_or_all_eligible_saturated N
  finalSpend_eq_sum := fluidBalance_finalSpend_eq_sum_allocation N

/-- Unit-mass eligibility profile obtained by fluidizing one hard-instance round. -/
def theorem9HardFluidRoundMass (N : ℕ) (round bidder : Fin N) : ℝ :=
  if (round : ℕ) ≤ (bidder : ℕ) then 1 else 0

/--
With `m` occurrences of bid `1/m`, the concrete identity-permutation hard
instance has exactly the unit round mass used by the fluid execution.
-/
theorem theorem9HardInstance_identity_round_bid_mass
    (N m : ℕ) (hm : 0 < m) (round bidder : Fin N) :
    (∑ copy : Fin m,
      (theorem9HardInstance N m (1 / (m : ℝ)) (Equiv.refl (Fin N))).bid
        bidder (round, copy)) =
      theorem9HardFluidRoundMass N round bidder := by
  change (∑ _copy : Fin m,
      theorem9RoundBid N (1 / (m : ℝ)) (Equiv.refl (Fin N)) round bidder) = _
  rw [theorem9RoundBid_formula]
  by_cases heligible : (round : ℕ) ≤ (bidder : ℕ)
  · simp [theorem9HardFluidRoundMass, heligible]
    field_simp [Nat.cast_ne_zero.mpr (ne_of_gt hm)]
  · simp [theorem9HardFluidRoundMass, heligible]

/-- The concrete aggregate round-bid profiles converge pointwise to the fluid input. -/
theorem theorem9HardInstance_identity_round_bid_mass_tendsto
    (N : ℕ) (round bidder : Fin N) :
    Filter.Tendsto
      (fun m : ℕ =>
        ∑ copy : Fin (m + 1),
          (theorem9HardInstance N (m + 1) (1 / ((m + 1 : ℕ) : ℝ))
            (Equiv.refl (Fin N))).bid bidder (round, copy))
      Filter.atTop
      (nhds (theorem9HardFluidRoundMass N round bidder)) := by
  have hprofile :
      (fun m : ℕ =>
        ∑ copy : Fin (m + 1),
          (theorem9HardInstance N (m + 1) (1 / ((m + 1 : ℕ) : ℝ))
            (Equiv.refl (Fin N))).bid bidder (round, copy)) =
        fun _m : ℕ => theorem9HardFluidRoundMass N round bidder := by
    funext m
    exact theorem9HardInstance_identity_round_bid_mass
      N (m + 1) (Nat.succ_pos m) round bidder
  rw [hprofile]
  exact tendsto_const_nhds

/-- The concrete hard family is genuinely in the paper's small-bids regime. -/
theorem theorem9HardInstance_bid_size_tendsto_zero :
    Filter.Tendsto (fun m : ℕ => (1 / (m : ℝ) : ℝ))
      Filter.atTop (nhds 0) := by
  simpa using (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))

/--
Formal small-bids fluidization contract for the concrete Theorem 9 occurrence
family.  It pins the fluid input to exact finite round bid masses while bid size
tends to zero, and it requires the allocation-derived, work-conserving BALANCE
rules rather than stipulating only a payoff formula.
-/
structure Theorem9HardBalanceFluidLimit (N : ℕ) where
  execution : FluidBalanceExecution N
  finite_round_bid_mass : ∀ m : ℕ, 0 < m → ∀ round bidder : Fin N,
    (∑ copy : Fin m,
      (theorem9HardInstance N m (1 / (m : ℝ)) (Equiv.refl (Fin N))).bid
        bidder (round, copy)) = theorem9HardFluidRoundMass N round bidder
  bid_size_tendsto_zero :
    Filter.Tendsto (fun m : ℕ => (1 / (m : ℝ) : ℝ))
      Filter.atTop (nhds 0)
  finite_round_bid_mass_tendsto : ∀ round bidder : Fin N,
    Filter.Tendsto
      (fun m : ℕ =>
        ∑ copy : Fin (m + 1),
          (theorem9HardInstance N (m + 1) (1 / ((m + 1 : ℕ) : ℝ))
            (Equiv.refl (Fin N))).bid bidder (round, copy))
      Filter.atTop
      (nhds (theorem9HardFluidRoundMass N round bidder))
  allocation_zero_of_zero_round_mass : ∀ round bidder,
    theorem9HardFluidRoundMass N round bidder = 0 →
      execution.allocation round bidder = 0
  eligible_equal_least_spend : ∀ round bidder bidder',
    theorem9HardFluidRoundMass N round bidder = 1 →
    theorem9HardFluidRoundMass N round bidder' = 1 →
      execution.spentBefore round bidder = execution.spentBefore round bidder'
  spentBefore_eq_prior_allocations : ∀ round bidder,
    execution.spentBefore round bidder =
      ∑ previous : Fin N,
        if (previous : ℕ) < (round : ℕ) then
          execution.allocation previous bidder
        else 0
  budget_feasible : ∀ round bidder,
    execution.spentBefore round bidder + execution.allocation round bidder ≤ 1
  work_conserving_or_saturated : ∀ round,
    (∑ bidder ∈ theorem9EligibleBidders N round,
      execution.allocation round bidder) = 1 ∨
    ∀ bidder, bidder ∈ theorem9EligibleBidders N round →
      execution.spentBefore round bidder + execution.allocation round bidder = 1
  finalSpend_eq_sum : ∀ bidder,
    execution.finalSpend bidder =
      ∑ round : Fin N, execution.allocation round bidder

/-- The explicit harmonic water-filling execution satisfies the full fluid-limit contract. -/
noncomputable def theorem9NestedSuffixBalanceFluidLimit (N : ℕ) :
    Theorem9HardBalanceFluidLimit N where
  execution := nestedSuffixFluidBalanceExecution N
  finite_round_bid_mass := theorem9HardInstance_identity_round_bid_mass N
  bid_size_tendsto_zero := theorem9HardInstance_bid_size_tendsto_zero
  finite_round_bid_mass_tendsto :=
    theorem9HardInstance_identity_round_bid_mass_tendsto N
  allocation_zero_of_zero_round_mass := by
    intro round bidder hmass
    have hineligible : ¬ (round : ℕ) ≤ (bidder : ℕ) := by
      intro heligible
      simp [theorem9HardFluidRoundMass, heligible] at hmass
    exact (nestedSuffixFluidBalanceExecution N).zero_of_ineligible
      round bidder hineligible
  eligible_equal_least_spend := by
    intro round bidder bidder' hmass hmass'
    have heligible : (round : ℕ) ≤ (bidder : ℕ) := by
      by_contra h
      simp [theorem9HardFluidRoundMass, h] at hmass
    have heligible' : (round : ℕ) ≤ (bidder' : ℕ) := by
      by_contra h
      simp [theorem9HardFluidRoundMass, h] at hmass'
    exact (nestedSuffixFluidBalanceExecution N).eligible_equal_least_spend
      round bidder bidder' heligible heligible'
  spentBefore_eq_prior_allocations :=
    (nestedSuffixFluidBalanceExecution N).spentBefore_eq_prefix
  budget_feasible := (nestedSuffixFluidBalanceExecution N).budget_feasible
  work_conserving_or_saturated :=
    (nestedSuffixFluidBalanceExecution N).work_conserving_or_saturated
  finalSpend_eq_sum := (nestedSuffixFluidBalanceExecution N).finalSpend_eq_sum

/-! ## Section 4: an execution that realizes the tight factor-LP witness -/

/-- Remaining active bidder mass before a slab in the geometric tight execution. -/
noncomputable def factorLPTightActiveMass (m : ℕ) (N : ℝ) (stage : ℕ) : ℝ :=
  N * (1 - 1 / ((m + 1 : ℕ) : ℝ)) ^ stage

/-- Mass that exits after reaching final type `i+1`. -/
noncomputable def factorLPTightTypeMass (m : ℕ) (N : ℝ) (i : Fin m) : ℝ :=
  MSVV07SourceLemmas.paperRoutePrimalCandidate (m := m) N i

/-- Spend fraction of the cohort that exits after slab `i+1`. -/
noncomputable def factorLPTightFinalSpendFraction (m : ℕ) (i : Fin m) : ℝ :=
  ((i.val + 1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ)

/-- Remaining cohort reaches full spend after the final slab. -/
noncomputable def factorLPTightFullMass (m : ℕ) (N : ℝ) : ℝ :=
  factorLPTightActiveMass m N m

/-- Revenue computed from the realized final-spend distribution. -/
noncomputable def factorLPTightFluidRevenue (m : ℕ) (N : ℝ) : ℝ :=
  (∑ i : Fin m,
    factorLPTightTypeMass m N i * factorLPTightFinalSpendFraction m i) +
    factorLPTightFullMass m N

/-- One slab raises every still-active bidder by exactly `1/(m+1)`. -/
noncomputable def factorLPTightSpentBeforeSlab (m stage : ℕ) : ℝ :=
  (stage : ℝ) / ((m + 1 : ℕ) : ℝ)

noncomputable def factorLPTightAllocationPerActiveBidder (m : ℕ) : ℝ :=
  1 / ((m + 1 : ℕ) : ℝ)

/-- Query mass in a slab is exactly the amount allocated by its active cohort. -/
noncomputable def factorLPTightQueryMassAtSlab
    (m : ℕ) (N : ℝ) (stage : ℕ) : ℝ :=
  factorLPTightActiveMass m N stage / ((m + 1 : ℕ) : ℝ)

/-- The common per-bidder state advances by exactly the common slab allocation. -/
theorem factorLPTight_state_update (m stage : ℕ) :
    factorLPTightSpentBeforeSlab m (stage + 1) =
      factorLPTightSpentBeforeSlab m stage +
        factorLPTightAllocationPerActiveBidder m := by
  simp [factorLPTightSpentBeforeSlab,
    factorLPTightAllocationPerActiveBidder, Nat.cast_add]
  ring

/-- Through the final slab, the common post-slab state respects the unit budget. -/
theorem factorLPTight_budget_feasible
    (m stage : ℕ) (hstage : stage ≤ m) :
    factorLPTightSpentBeforeSlab m stage +
        factorLPTightAllocationPerActiveBidder m ≤ 1 := by
  have hden : 0 < (((m + 1 : ℕ) : ℝ)) := by positivity
  have hcast : (stage : ℝ) + 1 ≤ ((m + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ hstage
  rw [factorLPTightSpentBeforeSlab,
    factorLPTightAllocationPerActiveBidder, ← add_div]
  exact (div_le_one hden).2 hcast

/-- Every slab's active cohort allocates exactly that slab's query mass. -/
theorem factorLPTight_slab_work_conservation
    (m : ℕ) (N : ℝ) (stage : ℕ) :
    factorLPTightActiveMass m N stage *
        factorLPTightAllocationPerActiveBidder m =
      factorLPTightQueryMassAtSlab m N stage := by
  unfold factorLPTightAllocationPerActiveBidder
    factorLPTightQueryMassAtSlab
  ring

/-- The geometric active-mass drop is exactly the displayed LP type mass. -/
theorem factorLPTight_active_mass_drop_realizes_type
    (m : ℕ) (N : ℝ) (i : Fin m) :
    factorLPTightActiveMass m N i.val -
        factorLPTightActiveMass m N (i.val + 1) =
      factorLPTightTypeMass m N i := by
  unfold factorLPTightActiveMass factorLPTightTypeMass
    MSVV07SourceLemmas.paperRoutePrimalCandidate
  rw [pow_succ]
  ring

/-- Partial type masses together with the fully spent remainder total `N`. -/
theorem factorLPTight_type_mass_partition (m : ℕ) (N : ℝ) :
    (∑ i : Fin m, factorLPTightTypeMass m N i) +
      factorLPTightFullMass m N = N := by
  let K : ℝ := ((m + 1 : ℕ) : ℝ)
  let r : ℝ := 1 - 1 / K
  have hgeom :
      (∑ i ∈ Finset.range m, r ^ i) * (1 - r) = 1 - r ^ m :=
    geom_sum_mul_neg r m
  change (∑ i : Fin m, N / K * r ^ i.val) + N * r ^ m = N
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => N / K * r ^ i) m]
  calc
    (∑ i ∈ Finset.range m, N / K * r ^ i) + N * r ^ m =
        N * ((1 / K) * (∑ i ∈ Finset.range m, r ^ i) + r ^ m) := by
          rw [mul_add]
          apply congrArg (fun z : ℝ => z + N * r ^ m)
          calc
            (∑ i ∈ Finset.range m, N / K * r ^ i) =
                ∑ i ∈ Finset.range m, (N * (1 / K)) * r ^ i := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  ring
            _ = (N * (1 / K)) *
                (∑ i ∈ Finset.range m, r ^ i) := by
                  rw [Finset.mul_sum]
            _ = N * ((1 / K) *
                (∑ i ∈ Finset.range m, r ^ i)) := by ring
    _ = N * ((1 - r) * (∑ i ∈ Finset.range m, r ^ i) + r ^ m) := by
          dsimp [r]
          ring
    _ = N := by
          rw [mul_comm (1 - r), hgeom]
          ring

/-- A type's spent and unspent fractions sum to one. -/
theorem factorLPTight_spent_add_unspent
    (m : ℕ) (i : Fin m) :
    factorLPTightFinalSpendFraction m i +
      MSVV07SourceLemmas.paperRoutePrimalObjectiveCoeff i = 1 := by
  have hi : i.val ≤ m := Nat.le_of_lt i.isLt
  unfold factorLPTightFinalSpendFraction
    MSVV07SourceLemmas.paperRoutePrimalObjectiveCoeff
  rw [Nat.cast_sub hi]
  have hK : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  field_simp [ne_of_gt hK]
  norm_num
  ring

/-- Execution revenue plus the realized unspent-budget LP objective is total budget. -/
theorem factorLPTight_revenue_add_objective_eq_N (m : ℕ) (N : ℝ) :
    factorLPTightFluidRevenue m N +
        MSVV07SourceLemmas.paperRoutePrimalObjective
          (factorLPTightTypeMass m N) = N := by
  unfold factorLPTightFluidRevenue
    MSVV07SourceLemmas.paperRoutePrimalObjective
  calc
    ((∑ i : Fin m,
          factorLPTightTypeMass m N i * factorLPTightFinalSpendFraction m i) +
        factorLPTightFullMass m N) +
        ∑ i : Fin m,
          MSVV07SourceLemmas.paperRoutePrimalObjectiveCoeff i *
            factorLPTightTypeMass m N i =
      (∑ i : Fin m,
        factorLPTightTypeMass m N i *
          (factorLPTightFinalSpendFraction m i +
            MSVV07SourceLemmas.paperRoutePrimalObjectiveCoeff i)) +
        factorLPTightFullMass m N := by
          rw [add_assoc,
            add_comm (factorLPTightFullMass m N), ← add_assoc]
          rw [← Finset.sum_add_distrib]
          apply congrArg (fun z : ℝ => z + factorLPTightFullMass m N)
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = (∑ i : Fin m, factorLPTightTypeMass m N i) +
        factorLPTightFullMass m N := by
          apply congrArg (fun z : ℝ => z + factorLPTightFullMass m N)
          apply Finset.sum_congr rfl
          intro i hi
          rw [factorLPTight_spent_add_unspent]
          ring
    _ = N := factorLPTight_type_mass_partition m N

/-- The realized execution revenue is `N` minus the exact tight LP objective. -/
theorem factorLPTight_revenue_eq_N_sub_lpValue (m : ℕ) (N : ℝ) :
    factorLPTightFluidRevenue m N =
      N - MSVV07SourceLemmas.factorRevealingLPValue m N := by
  have htotal := factorLPTight_revenue_add_objective_eq_N m N
  have hobjective :
      MSVV07SourceLemmas.paperRoutePrimalObjective
          (factorLPTightTypeMass m N) =
        MSVV07SourceLemmas.factorRevealingLPValue m N := by
    simpa [factorLPTightTypeMass] using
      (MSVV07SourceLemmas.paperRoutePrimalCandidate_objective_value
        (m := m) N)
  rw [hobjective] at htotal
  exact eq_sub_of_add_eq htotal

/--
The explicit cohort-fluid BALANCE realization at unit total budget approaches
the MSVV ratio.  This is an internal limiting witness; it does not purport to
identify the external finite exact instance cited from KP00 in MSVV07.
-/
theorem factorLPTightFluidRevenue_tendsTo_msvvRatio :
    Sequence.SeqTendsTo
      (fun m : ℕ => factorLPTightFluidRevenue m 1)
      paperMsvvRatio := by
  intro delta hdelta
  obtain ⟨K, hK⟩ :=
    MSVV07SourceLemmas.lemma3_factor_revealing_lp_value_tends (1 : ℝ) delta hdelta
  refine ⟨K, ?_⟩
  intro m hm
  have hvalue := hK (m + 1) (by omega)
  have hfactor :
      MSVV07SourceLemmas.factorRevealingLPValue m 1 =
        1 * (1 - 1 / ((m + 1 : ℕ) : ℝ)) ^ (m + 1) := by
    rfl
  change |factorLPTightFluidRevenue m 1 - paperMsvvRatio| ≤ delta
  rw [factorLPTight_revenue_eq_N_sub_lpValue, hfactor]
  calc
    |1 - 1 * (1 - 1 / ((m + 1 : ℕ) : ℝ)) ^ (m + 1) - paperMsvvRatio| =
        |-(1 * (1 - 1 / ((m + 1 : ℕ) : ℝ)) ^ (m + 1) -
          1 / Real.exp 1)| := by
            congr 1
            simp only [paperMsvvRatio]
            ring
    _ = |1 * (1 - 1 / ((m + 1 : ℕ) : ℝ)) ^ (m + 1) -
          1 / Real.exp 1| := abs_neg _
    _ ≤ delta := hvalue

/-- Revenue is the sum of the query mass actually allocated in every slab. -/
theorem factorLPTight_sum_slab_allocations_eq_revenue (m : ℕ) (N : ℝ) :
    (∑ stage ∈ Finset.range (m + 1),
      factorLPTightActiveMass m N stage *
        factorLPTightAllocationPerActiveBidder m) =
      factorLPTightFluidRevenue m N := by
  let K : ℝ := ((m + 1 : ℕ) : ℝ)
  let r : ℝ := 1 - 1 / K
  have hr : 1 - r = 1 / K := by
    dsimp [r]
    ring
  have hgeom :
      (∑ stage ∈ Finset.range (m + 1), r ^ stage) * (1 - r) =
        1 - r ^ (m + 1) :=
    geom_sum_mul_neg r (m + 1)
  change
    (∑ stage ∈ Finset.range (m + 1),
      (N * r ^ stage) * (1 / K)) = factorLPTightFluidRevenue m N
  calc
    (∑ stage ∈ Finset.range (m + 1),
        (N * r ^ stage) * (1 / K)) =
        N * ((∑ stage ∈ Finset.range (m + 1), r ^ stage) *
          (1 - r)) := by
            rw [hr]
            calc
              (∑ stage ∈ Finset.range (m + 1),
                  (N * r ^ stage) * (1 / K)) =
                  ∑ stage ∈ Finset.range (m + 1),
                    (N * (1 / K)) * r ^ stage := by
                      apply Finset.sum_congr rfl
                      intro stage hstage
                      ring
              _ = (N * (1 / K)) *
                    (∑ stage ∈ Finset.range (m + 1), r ^ stage) := by
                      rw [Finset.mul_sum]
              _ = N *
                    ((∑ stage ∈ Finset.range (m + 1), r ^ stage) *
                      (1 / K)) := by ring
    _ = N * (1 - r ^ (m + 1)) := by rw [hgeom]
    _ = N - MSVV07SourceLemmas.factorRevealingLPValue m N := by
      simp [MSVV07SourceLemmas.factorRevealingLPValue,
        MSVV07SourceLemmas.paperRouteCandidateValue, r, K]
      ring
    _ = factorLPTightFluidRevenue m N :=
      (factorLPTight_revenue_eq_N_sub_lpValue m N).symm

/--
Cohort-fluid BALANCE execution that realizes, rather than merely juxtaposes,
the displayed factor-LP witness.  Active bidders share the same slab state and
receive the same increment; their geometric mass drop is the final-type mass.
-/
structure FactorLPTightFluidRealization (m : ℕ) (N : ℝ) where
  typeMass : Fin m → ℝ
  activeMassBeforeSlab : ℕ → ℝ
  spentBeforeSlab : ℕ → ℝ
  allocationPerActiveBidder : ℕ → ℝ
  queryMassAtSlab : ℕ → ℝ
  fullMass : ℝ
  revenue : ℝ
  typeMass_eq_candidate : ∀ i,
    typeMass i = MSVV07SourceLemmas.paperRoutePrimalCandidate (m := m) N i
  active_mass_drop_eq_typeMass : ∀ i : Fin m,
    activeMassBeforeSlab i.val - activeMassBeforeSlab (i.val + 1) = typeMass i
  equal_least_spend_state : ∀ stage, stage ≤ m →
    spentBeforeSlab stage = (stage : ℝ) / ((m + 1 : ℕ) : ℝ)
  equal_allocation_increment : ∀ stage, stage ≤ m →
    allocationPerActiveBidder stage = 1 / ((m + 1 : ℕ) : ℝ)
  query_mass_formula : ∀ stage, stage ≤ m →
    queryMassAtSlab stage = activeMassBeforeSlab stage / ((m + 1 : ℕ) : ℝ)
  state_update : ∀ stage, stage < m →
    spentBeforeSlab (stage + 1) =
      spentBeforeSlab stage + allocationPerActiveBidder stage
  budget_feasible : ∀ stage, stage ≤ m →
    spentBeforeSlab stage + allocationPerActiveBidder stage ≤ 1
  slab_work_conservation : ∀ stage, stage ≤ m →
    activeMassBeforeSlab stage * allocationPerActiveBidder stage =
      queryMassAtSlab stage
  type_mass_partition : (∑ i : Fin m, typeMass i) + fullMass = N
  lp_rows_realized_tight : ∀ i,
    MSVV07SourceLemmas.paperRouteLPRow typeMass i =
      MSVV07SourceLemmas.paperRouteRhs N i
  revenue_from_final_types :
    revenue =
      (∑ i : Fin m,
        typeMass i * factorLPTightFinalSpendFraction m i) + fullMass
  revenue_from_slab_allocations :
    revenue = ∑ stage ∈ Finset.range (m + 1),
      activeMassBeforeSlab stage * allocationPerActiveBidder stage
  revenue_eq_N_sub_lpValue :
    revenue = N - MSVV07SourceLemmas.factorRevealingLPValue m N

/-- The geometric construction satisfies the complete factor-LP realization contract. -/
noncomputable def factorLPTightFluidExecution (m : ℕ) (N : ℝ) :
    FactorLPTightFluidRealization m N where
  typeMass := factorLPTightTypeMass m N
  activeMassBeforeSlab := factorLPTightActiveMass m N
  spentBeforeSlab := factorLPTightSpentBeforeSlab m
  allocationPerActiveBidder := fun _ => factorLPTightAllocationPerActiveBidder m
  queryMassAtSlab := factorLPTightQueryMassAtSlab m N
  fullMass := factorLPTightFullMass m N
  revenue := factorLPTightFluidRevenue m N
  typeMass_eq_candidate := fun _ => rfl
  active_mass_drop_eq_typeMass := factorLPTight_active_mass_drop_realizes_type m N
  equal_least_spend_state := by intro stage hstage; rfl
  equal_allocation_increment := by intro stage hstage; rfl
  query_mass_formula := by intro stage hstage; rfl
  state_update := by
    intro stage hstage
    exact factorLPTight_state_update m stage
  budget_feasible := factorLPTight_budget_feasible m
  slab_work_conservation := by
    intro stage hstage
    exact factorLPTight_slab_work_conservation m N stage
  type_mass_partition := factorLPTight_type_mass_partition m N
  lp_rows_realized_tight := by
    intro i
    exact MSVV07SourceLemmas.paperRoutePrimalCandidate_row_tight N i
  revenue_from_final_types := rfl
  revenue_from_slab_allocations :=
    (factorLPTight_sum_slab_allocations_eq_revenue m N).symm
  revenue_eq_N_sub_lpValue := factorLPTight_revenue_eq_N_sub_lpValue m N

/-- Total revenue executed by the explicit fluid BALANCE allocation. -/
noncomputable def theorem9BaseEqualSpreadBalanceRevenue (N : ℕ) : ℝ :=
  ∑ bidder : Fin N, (nestedSuffixFluidBalanceExecution N).finalSpend bidder

/-- The execution's normalized value is exactly the finite harmonic revenue expression. -/
theorem theorem9BaseEqualSpreadBalanceRevenue_normalized (N : ℕ) :
    theorem9BaseEqualSpreadBalanceRevenue N / (N : ℝ) =
      theorem9NormalizedRevenueUpperBound N := by
  unfold theorem9BaseEqualSpreadBalanceRevenue theorem9NormalizedRevenueUpperBound
  congr 1
  apply Finset.sum_congr rfl
  intro bidder _
  exact fluidBalance_finalSpend_eq_harmonicCap N bidder

/-- The equal-spread base-instance calculation is asymptotically at most `1-1/e`. -/
theorem theorem9_base_equal_spread_balance_eventually_le_msvvRatio_add :
    ∀ delta : ℝ, 0 < delta →
      ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
        theorem9BaseEqualSpreadBalanceRevenue N / (N : ℝ) ≤
          AdWordsInstance.msvvRatio + delta := by
  intro delta hdelta
  simpa [theorem9BaseEqualSpreadBalanceRevenue_normalized] using
    theorem9_harmonic_eventually_le_msvvRatio_add delta hdelta

end SourceRunner
end MSVV07PaperFacing
end Online
end AppliedModelingLib

import AppliedModelingLib.Algorithms.Online.AdWords
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The Appendix Counterexample to Raw-Bid Greedy Allocation

The MSVV appendix studies the rule that selects a highest raw bid and, among
equal raw bids, selects an advertiser with the most budget left.  This file
separates two claims that the printed appendix conflates:

* the three displayed phase lengths sum to the source's zero-phase-3 value
  `3 / 5`, not the printed decimal `0.62`; and
* the displayed execution does not in fact exhaust the tail advertisers after
  phase 2.  Its fluid phase-1 spend is `log (9 / 5)`, so phase 2 leaves a
  positive residual.  Serving that residual in phase 3 gives the actual ratio
  `9 / 10 - (1 / 2) * log (9 / 5)`.

The execution objects below contain allocation data only.  Spend before a
round, spend after a round, final spend, and revenue are definitions computed
from that allocation.  In particular, a certificate cannot supply an
independent state trajectory that already asserts the desired conclusion.

The appendix's later `κ > 1` sentence does not print its phase parameters.  A
separate section below therefore labels its explicit family **derived**.
-/

namespace AppliedModelingLib
namespace Online
namespace MSVV07Appendix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

open scoped BigOperators Interval Topology
open Finset Set Filter

/-! ## A state-derived finite fluid certificate -/

/-- Fluid input data for finitely many aggregate rounds and advertisers. -/
structure FluidInput (rounds : ℕ) (Advertiser : Type*) where
  /-- Budget mass represented by an advertiser or advertiser cohort. -/
  budget : Advertiser → ℝ
  /-- Query mass in an aggregate round. -/
  queryMass : Fin rounds → ℝ
  /-- Whether the advertiser has a positive bid in the round. -/
  eligible : Fin rounds → Advertiser → Prop
  /-- Raw bid per unit of query mass. -/
  rawBid : Fin rounds → Advertiser → ℝ

/-- Allocation data.  `discard` is query mass not allocated in a round. -/
structure FluidAllocation {rounds : ℕ} {Advertiser : Type*}
    (I : FluidInput rounds Advertiser) where
  allocation : Fin rounds → Advertiser → ℝ
  discard : Fin rounds → ℝ

namespace FluidAllocation

variable {rounds : ℕ} {Advertiser : Type*} [Fintype Advertiser]
variable {I : FluidInput rounds Advertiser}

/-- Spend before `r`, computed only from allocations in strictly earlier rounds. -/
def spentBefore (E : FluidAllocation I) (r : Fin rounds) (a : Advertiser) : ℝ :=
  ∑ s : Fin rounds, if s < r then E.allocation s a * I.rawBid s a else 0

/-- Spend after `r`; this is a state update, not certificate-supplied data. -/
def spentAfter (E : FluidAllocation I) (r : Fin rounds) (a : Advertiser) : ℝ :=
  E.spentBefore r a + E.allocation r a * I.rawBid r a

/-- Final spend, computed from the entire allocation history. -/
def finalSpend (E : FluidAllocation I) (a : Advertiser) : ℝ :=
  ∑ r : Fin rounds, E.allocation r a * I.rawBid r a

/-- Revenue of the allocation. -/
def revenue (E : FluidAllocation I) : ℝ :=
  ∑ r : Fin rounds, ∑ a : Advertiser, E.allocation r a * I.rawBid r a

@[simp] theorem spentAfter_state_update
    (E : FluidAllocation I) (r : Fin rounds) (a : Advertiser) :
    E.spentAfter r a = E.spentBefore r a + E.allocation r a * I.rawBid r a := rfl

theorem revenue_eq_sum_finalSpend (E : FluidAllocation I) :
    E.revenue = ∑ a : Advertiser, E.finalSpend a := by
  simp only [revenue, finalSpend]
  exact Finset.sum_comm

end FluidAllocation

/-- Feasibility conditions common to online and offline fluid allocations. -/
structure FluidFeasible {rounds : ℕ} {Advertiser : Type*} [Fintype Advertiser]
    {I : FluidInput rounds Advertiser} (E : FluidAllocation I) : Prop where
  allocation_nonneg : ∀ r a, 0 ≤ E.allocation r a
  discard_nonneg : ∀ r, 0 ≤ E.discard r
  allocation_zero_of_ineligible :
    ∀ r a, ¬ I.eligible r a → E.allocation r a = 0
  round_conservation :
    ∀ r, (∑ a : Advertiser, E.allocation r a) + E.discard r = I.queryMass r
  final_budget_feasible : ∀ a, E.finalSpend a ≤ I.budget a

/--
Coarse finite-cohort accounting certificate.  Its round-boundary checks are
useful diagnostics, but they do **not** by themselves establish the paper's
per-individual, within-phase highest-bid/most-leftover execution semantics.
-/
structure FluidNaiveExecutionCertificate
    {rounds : ℕ} {Advertiser : Type*} [Fintype Advertiser]
    (I : FluidInput rounds Advertiser) where
  execution : FluidAllocation I
  feasible : FluidFeasible execution
  raw_bid_maximal :
    ∀ r a, 0 < execution.allocation r a →
      ∀ b, I.eligible r b → execution.spentBefore r b < I.budget b →
        I.rawBid r b ≤ I.rawBid r a
  least_spend_tie :
    ∀ r a, 0 < execution.allocation r a →
      ∀ b, I.eligible r b → execution.spentBefore r b < I.budget b →
        I.rawBid r b = I.rawBid r a →
        execution.spentBefore r a ≤ execution.spentBefore r b

/--
A coarse accounting execution together with an optimal offline feasible
witness.  Source-rule credit requires a separate continuous per-individual
bridge below.
-/
structure FluidCounterexampleCertificate
    {rounds : ℕ} {Advertiser : Type*} [Fintype Advertiser]
    (I : FluidInput rounds Advertiser) extends
      FluidNaiveExecutionCertificate I where
  offline : FluidAllocation I
  offline_feasible : FluidFeasible offline
  offline_optimal :
    ∀ alternative : FluidAllocation I,
      FluidFeasible alternative → alternative.revenue ≤ offline.revenue

namespace FluidCounterexampleCertificate

variable {rounds : ℕ} {Advertiser : Type*} [Fintype Advertiser]
variable {I : FluidInput rounds Advertiser}

/-- The certificate's online value. -/
def onlineValue (C : FluidCounterexampleCertificate I) : ℝ := C.execution.revenue

/-- The certificate's checked offline optimum value. -/
def offlineOptimum (C : FluidCounterexampleCertificate I) : ℝ := C.offline.revenue

theorem onlineValue_le_offlineOptimum (C : FluidCounterexampleCertificate I) :
    C.onlineValue ≤ C.offlineOptimum :=
  C.offline_optimal C.execution C.feasible

end FluidCounterexampleCertificate

/-! ## Continuous within-phase state for the printed example -/

/-- Phase-1 tail allocation rate at normalized time `r`. -/
def printedPhaseOneAllocationRate (r : ℝ) : ℝ := (9 / 10 - r)⁻¹

/-- A bidder coordinate is eligible in phase 1 exactly until its departure time. -/
def printedPhaseOneEligible (r bidder : ℝ) : Prop :=
  1 / 10 + r ≤ bidder ∧ bidder ≤ 1

/-- The normalized phase-1 raw bid is one exactly on the active suffix. -/
def printedPhaseOneRawBid (r bidder : ℝ) : ℝ :=
  if printedPhaseOneEligible r bidder then 1 else 0

/-- Every pair of phase-1 eligible bidders is tied at the maximal raw bid. -/
theorem printed_phaseOne_raw_bid_tie_of_eligible
    {r bidder₁ bidder₂ : ℝ}
    (h₁ : printedPhaseOneEligible r bidder₁)
    (h₂ : printedPhaseOneEligible r bidder₂) :
    printedPhaseOneRawBid r bidder₁ = printedPhaseOneRawBid r bidder₂ := by
  simp [printedPhaseOneRawBid, h₁, h₂]

/--
Phase-1 spend before time `r`, derived by integrating precisely the allocation
rate received while the bidder is eligible.
-/
noncomputable def printedPhaseOneSpentBefore (r bidder : ℝ) : ℝ :=
  ∫ s in 0..r,
    if printedPhaseOneEligible s bidder then printedPhaseOneAllocationRate s else 0

/-- The active phase-1 interval receives one unit of query mass per unit time. -/
theorem printed_phaseOne_round_conservation
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 2 / 5) :
    (∫ _bidder in (1 / 10 + r)..1, printedPhaseOneAllocationRate r) = 1 := by
  have hden : 9 / 10 - r ≠ 0 := by norm_num at hr0 hr ⊢; linarith
  calc
    (∫ _bidder in (1 / 10 + r)..1, printedPhaseOneAllocationRate r) =
        (1 - (1 / 10 + r)) * printedPhaseOneAllocationRate r := by simp
    _ = (9 / 10 - r) * (9 / 10 - r)⁻¹ := by
      rw [printedPhaseOneAllocationRate]
      ring
    _ = 1 := mul_inv_cancel₀ hden

/-- Eligible phase-1 bidders have exactly the integral of the common rate. -/
theorem printed_phaseOne_spentBefore_eq_integral
    {r bidder : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 2 / 5)
    (hbidder : printedPhaseOneEligible r bidder) :
    printedPhaseOneSpentBefore r bidder =
      ∫ s in 0..r, printedPhaseOneAllocationRate s := by
  rw [printedPhaseOneSpentBefore]
  apply intervalIntegral.integral_congr
  intro s hs
  have hsIcc : s ∈ Set.Icc (0 : ℝ) r := by
    simpa [uIcc_of_le hr0] using hs
  have heligible : printedPhaseOneEligible s bidder := by
    constructor
    · linarith [hsIcc.2, hbidder.1]
    · exact hbidder.2
  simp [heligible]

/-- The derived phase-1 state has the logarithmic closed form. -/
theorem printed_phaseOne_spentBefore_eq_log
    {r bidder : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 2 / 5)
    (hbidder : printedPhaseOneEligible r bidder) :
    printedPhaseOneSpentBefore r bidder =
      Real.log ((9 / 10) / (9 / 10 - r)) := by
  rw [printed_phaseOne_spentBefore_eq_integral hr0 hr hbidder]
  simp only [printedPhaseOneAllocationRate]
  rw [
    intervalIntegral.integral_comp_sub_left (fun x : ℝ => x⁻¹) (9 / 10)]
  rw [integral_inv_of_pos]
  · ring_nf
  · norm_num at hr0 hr ⊢
    linarith
  · norm_num

/-- Least-spend tie-breaking is honest: every currently eligible bidder has the same state. -/
theorem printed_phaseOne_equal_spend_of_eligible
    {r bidder₁ bidder₂ : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 2 / 5)
    (h₁ : printedPhaseOneEligible r bidder₁)
    (h₂ : printedPhaseOneEligible r bidder₂) :
    printedPhaseOneSpentBefore r bidder₁ = printedPhaseOneSpentBefore r bidder₂ := by
  rw [printed_phaseOne_spentBefore_eq_log hr0 hr h₁,
    printed_phaseOne_spentBefore_eq_log hr0 hr h₂]

/-- Every tail bidder has spent `log (9/5)` at the end of phase 1. -/
theorem printed_phaseOne_tail_spend :
    printedPhaseOneSpentBefore (2 / 5) (1 / 2) = Real.log (9 / 5) := by
  convert printed_phaseOne_spentBefore_eq_log
    (r := (2 / 5 : ℝ)) (bidder := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
      (by norm_num [printedPhaseOneEligible]) using 1 <;> norm_num

/-- Tail advertisers have raw bid `2a` in phase 2; one low bidder has bid `a`. -/
def printedPhaseTwoRawBid (offset bidder : ℝ) : ℝ :=
  if 1 / 2 ≤ bidder ∧ bidder ≤ 1 then 2
  else if bidder = offset then 1 else 0

/-- Phase 2 allocates query density two uniformly over the tail interval of width one half. -/
def printedPhaseTwoAllocationDensity (bidder : ℝ) : ℝ :=
  if 1 / 2 ≤ bidder ∧ bidder ≤ 1 then 2 else 0

/-- Phase-2 spend rate is raw bid two times allocation density two. -/
def printedPhaseTwoSpendRate (bidder : ℝ) : ℝ :=
  printedPhaseTwoRawBid 0 bidder * printedPhaseTwoAllocationDensity bidder

/-- Phase-2 state is phase-1 state plus the integral of actual phase-2 allocations and bids. -/
noncomputable def printedPhaseTwoSpentBefore (offset bidder : ℝ) : ℝ :=
  printedPhaseOneSpentBefore (2 / 5) bidder +
    ∫ s in 0..offset,
      printedPhaseTwoRawBid s bidder * printedPhaseTwoAllocationDensity bidder

theorem printed_phaseTwo_round_conservation :
    (∫ bidder in (1 / 2 : ℝ)..1, printedPhaseTwoAllocationDensity bidder) = 1 := by
  calc
    (∫ bidder in (1 / 2 : ℝ)..1,
        printedPhaseTwoAllocationDensity bidder) =
        ∫ _bidder in (1 / 2 : ℝ)..1, (2 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro bidder hbidder
          have hb : (1 / 2 : ℝ) ≤ bidder ∧ bidder ≤ 1 := by
            rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at hbidder
            exact ⟨hbidder.1, hbidder.2⟩
          rw [printedPhaseTwoAllocationDensity, if_pos hb]
    _ = 1 := by norm_num

/-- Allocated phase-2 bidders have maximal raw bid. -/
theorem printed_phaseTwo_raw_bid_maximal
    {offset bidder competitor : ℝ}
    (hallocated : 0 < printedPhaseTwoAllocationDensity bidder)
    (hcompetitor :
      (1 / 2 ≤ competitor ∧ competitor ≤ 1) ∨ competitor = offset) :
    printedPhaseTwoRawBid offset competitor ≤ printedPhaseTwoRawBid offset bidder := by
  have htail : 1 / 2 ≤ bidder ∧ bidder ≤ 1 := by
    by_contra h
    rw [printedPhaseTwoAllocationDensity, if_neg h] at hallocated
    linarith
  have hbidderRaw : printedPhaseTwoRawBid offset bidder = 2 := by
    rw [printedPhaseTwoRawBid, if_pos htail]
  rw [hbidderRaw]
  rcases hcompetitor with hcompetitor | hcompetitor
  · have hcompetitorRaw : printedPhaseTwoRawBid offset competitor = 2 := by
      rw [printedPhaseTwoRawBid, if_pos hcompetitor]
    rw [hcompetitorRaw]
  · rw [hcompetitor]
    by_cases hoffsetTail : 1 / 2 ≤ offset ∧ offset ≤ 1
    · have hoffsetRaw : printedPhaseTwoRawBid offset offset = 2 := by
        rw [printedPhaseTwoRawBid, if_pos hoffsetTail]
      rw [hoffsetRaw]
    · have hoffsetRaw : printedPhaseTwoRawBid offset offset = 1 := by
        rw [printedPhaseTwoRawBid, if_neg hoffsetTail, if_pos rfl]
      rw [hoffsetRaw]
      norm_num

/-- Tail state through phase 2 is derived from both phase allocations. -/
theorem printed_phaseTwo_tail_spentBefore_eq
    {offset bidder : ℝ} (hoffset0 : 0 ≤ offset) (hoffset : offset ≤ 1 / 10)
    (hbidder : 1 / 2 ≤ bidder ∧ bidder ≤ 1) :
    printedPhaseTwoSpentBefore offset bidder = Real.log (9 / 5) + 4 * offset := by
  rw [printedPhaseTwoSpentBefore]
  have hphaseOne : printedPhaseOneSpentBefore (2 / 5) bidder = Real.log (9 / 5) := by
    convert printed_phaseOne_spentBefore_eq_log
      (r := (2 / 5 : ℝ)) (bidder := bidder) (by norm_num) (by norm_num)
        ⟨by linarith [hbidder.1], hbidder.2⟩ using 1 <;> norm_num
  rw [hphaseOne]
  have hintegrand :
      (∫ s in 0..offset,
          printedPhaseTwoRawBid s bidder * printedPhaseTwoAllocationDensity bidder) =
        ∫ _s in 0..offset, (4 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro s _hs
    simp only [printedPhaseTwoRawBid, printedPhaseTwoAllocationDensity,
      if_pos hbidder]
    norm_num
  rw [hintegrand]
  simp
  ring

/-- All tail bidders remain tied throughout phase 2. -/
theorem printed_phaseTwo_equal_spend_of_tail
    {offset bidder₁ bidder₂ : ℝ} (hoffset0 : 0 ≤ offset)
    (hoffset : offset ≤ 1 / 10)
    (h₁ : 1 / 2 ≤ bidder₁ ∧ bidder₁ ≤ 1)
    (h₂ : 1 / 2 ≤ bidder₂ ∧ bidder₂ ≤ 1) :
    printedPhaseTwoSpentBefore offset bidder₁ =
      printedPhaseTwoSpentBefore offset bidder₂ := by
  rw [printed_phaseTwo_tail_spentBefore_eq hoffset0 hoffset h₁,
    printed_phaseTwo_tail_spentBefore_eq hoffset0 hoffset h₂]

/-! ## Exact arithmetic for the printed phase lengths -/

theorem log_nine_fifths_pos : 0 < Real.log (9 / 5) := by
  exact Real.log_pos (by norm_num)

/-- A rational Taylor bound strong enough to show the tail is not exhausted. -/
theorem log_nine_fifths_lt_three_fifths : Real.log (9 / 5) < 3 / 5 := by
  have h := Real.log_div_le_sum_range_add
    (x := (2 / 7 : ℝ)) (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

/-- The appendix's asserted exhaustion after phase 2 is false. -/
theorem printed_tail_not_exhausted_after_phaseTwo :
    printedPhaseTwoSpentBefore (1 / 10) (1 / 2) < 1 := by
  rw [printed_phaseTwo_tail_spentBefore_eq (by norm_num) (by norm_num)
    (by norm_num)]
  linarith [log_nine_fifths_lt_three_fifths]

/-- Positive per-tail-advertiser budget remaining for phase 3. -/
def printedPhaseThreeResidualPerTail : ℝ := 3 / 5 - Real.log (9 / 5)

theorem printedPhaseThreeResidualPerTail_pos :
    0 < printedPhaseThreeResidualPerTail := by
  dsimp [printedPhaseThreeResidualPerTail]
  linarith [log_nine_fifths_lt_three_fifths]

/-- Aggregate phase-3 service: tail mass one half times its per-bidder residual. -/
def printedPhaseThreeServedMass : ℝ :=
  1 / 2 * printedPhaseThreeResidualPerTail

theorem printedPhaseThreeServedMass_eq :
    printedPhaseThreeServedMass = 3 / 10 - 1 / 2 * Real.log (9 / 5) := by
  simp [printedPhaseThreeServedMass, printedPhaseThreeResidualPerTail]
  ring

/-! ## The concrete three-cohort, three-phase execution -/

/-- Cohort `0` is the first tenth, `1` the middle two fifths, and `2` the tail half. -/
def printedBudget (a : Fin 3) : ℝ :=
  match a.1 with
  | 0 => 1 / 10
  | 1 => 2 / 5
  | _ => 1 / 2

def printedQueryMass (r : Fin 3) : ℝ :=
  match r.1 with
  | 0 => 2 / 5
  | 1 => 1 / 10
  | _ => 1 / 2

def printedEligible (r a : Fin 3) : Prop :=
  match r.1, a.1 with
  | 0, 1 => True
  | 0, 2 => True
  | 1, 0 => True
  | 1, 2 => True
  | 2, 2 => True
  | _, _ => False

def printedRawBid (r a : Fin 3) : ℝ :=
  match r.1, a.1 with
  | 0, 1 => 1
  | 0, 2 => 1
  | 1, 0 => 1
  | 1, 2 => 2
  | 2, 2 => 1
  | _, _ => 0

def printedInput : FluidInput 3 (Fin 3) where
  budget := printedBudget
  queryMass := printedQueryMass
  eligible := printedEligible
  rawBid := printedRawBid

/-- The true online allocation, including the positive phase-3 residual. -/
noncomputable def printedOnlineAllocation (r a : Fin 3) : ℝ :=
  match r.1, a.1 with
  | 0, 1 => 2 / 5 - 1 / 2 * Real.log (9 / 5)
  | 0, 2 => 1 / 2 * Real.log (9 / 5)
  | 1, 2 => 1 / 10
  | 2, 2 => printedPhaseThreeServedMass
  | _, _ => 0

noncomputable def printedOnlineDiscard (r : Fin 3) : ℝ :=
  match r.1 with
  | 2 => 1 / 2 - printedPhaseThreeServedMass
  | _ => 0

noncomputable def printedOnlineExecution : FluidAllocation printedInput where
  allocation := printedOnlineAllocation
  discard := printedOnlineDiscard

/-- The offline witness assigns each phase to its dedicated cohort and exhausts all budgets. -/
def printedOfflineAllocation (r a : Fin 3) : ℝ :=
  match r.1, a.1 with
  | 0, 1 => 2 / 5
  | 1, 0 => 1 / 10
  | 2, 2 => 1 / 2
  | _, _ => 0

def printedOfflineExecution : FluidAllocation printedInput where
  allocation := printedOfflineAllocation
  discard := fun _ => 0

private theorem printed_online_feasible : FluidFeasible printedOnlineExecution := by
  constructor
  · intro r a
    fin_cases r <;> fin_cases a <;>
      simp [printedOnlineExecution, printedOnlineAllocation,
        printedPhaseThreeServedMass, printedPhaseThreeResidualPerTail]
    all_goals nlinarith [log_nine_fifths_pos, log_nine_fifths_lt_three_fifths]
  · intro r
    fin_cases r <;>
      simp [printedOnlineExecution, printedOnlineDiscard,
        printedPhaseThreeServedMass, printedPhaseThreeResidualPerTail]
    nlinarith [log_nine_fifths_pos]
  · intro r a h
    fin_cases r <;> fin_cases a <;>
      simp [printedInput, printedEligible, printedOnlineExecution,
        printedOnlineAllocation] at h ⊢
  · intro r
    fin_cases r <;>
      simp [printedInput, printedQueryMass, printedOnlineExecution,
        printedOnlineAllocation, printedOnlineDiscard, Fin.sum_univ_three]
    all_goals simp [printedPhaseThreeServedMass, printedPhaseThreeResidualPerTail]
    all_goals ring
  · intro a
    fin_cases a <;>
      simp [FluidAllocation.finalSpend, printedInput, printedBudget,
        printedRawBid, printedOnlineExecution, printedOnlineAllocation,
        Fin.sum_univ_three, printedPhaseThreeServedMass,
        printedPhaseThreeResidualPerTail]
    all_goals nlinarith [log_nine_fifths_pos, log_nine_fifths_lt_three_fifths]

private theorem printed_offline_feasible : FluidFeasible printedOfflineExecution := by
  constructor
  · intro r a
    fin_cases r <;> fin_cases a <;>
      norm_num [printedOfflineExecution, printedOfflineAllocation]
  · intro r
    simp [printedOfflineExecution]
  · intro r a h
    fin_cases r <;> fin_cases a <;>
      simp [printedInput, printedEligible, printedOfflineExecution,
        printedOfflineAllocation] at h ⊢
  · intro r
    fin_cases r <;>
      norm_num [printedInput, printedQueryMass, printedOfflineExecution,
        printedOfflineAllocation, Fin.sum_univ_three]
  · intro a
    fin_cases a <;>
      norm_num [FluidAllocation.finalSpend, printedInput, printedBudget,
        printedRawBid, printedOfflineExecution, printedOfflineAllocation,
        Fin.sum_univ_three]

private theorem printed_offline_optimal
    (alternative : FluidAllocation printedInput)
    (hfeasible : FluidFeasible alternative) :
    alternative.revenue ≤ printedOfflineExecution.revenue := by
  rw [FluidAllocation.revenue_eq_sum_finalSpend]
  calc
    (∑ a : Fin 3, alternative.finalSpend a) ≤
        ∑ a : Fin 3, printedInput.budget a := by
      exact Finset.sum_le_sum fun a _ => hfeasible.final_budget_feasible a
    _ = 1 := by
      norm_num [printedInput, printedBudget, Fin.sum_univ_three]
    _ = printedOfflineExecution.revenue := by
      norm_num [FluidAllocation.revenue, printedInput, printedRawBid,
        printedOfflineExecution, printedOfflineAllocation, Fin.sum_univ_three]

private theorem printed_raw_bid_maximal :
    ∀ r a, 0 < printedOnlineExecution.allocation r a →
      ∀ b, printedInput.eligible r b →
        printedOnlineExecution.spentBefore r b < printedInput.budget b →
        printedInput.rawBid r b ≤ printedInput.rawBid r a := by
  intro r a ha b hb _halive
  fin_cases r <;> fin_cases a <;> fin_cases b <;>
    simp [printedInput, printedEligible, printedRawBid, printedOnlineExecution,
      printedOnlineAllocation, printedPhaseThreeServedMass,
      printedPhaseThreeResidualPerTail] at ha hb ⊢
  all_goals nlinarith [log_nine_fifths_pos, log_nine_fifths_lt_three_fifths]

private theorem printed_least_spend_tie :
    ∀ r a, 0 < printedOnlineExecution.allocation r a →
      ∀ b, printedInput.eligible r b →
        printedOnlineExecution.spentBefore r b < printedInput.budget b →
        printedInput.rawBid r b = printedInput.rawBid r a →
        printedOnlineExecution.spentBefore r a ≤
          printedOnlineExecution.spentBefore r b := by
  intro r a ha b hb _halive htie
  fin_cases r <;> fin_cases a <;> fin_cases b <;>
    simp [FluidAllocation.spentBefore, printedInput, printedEligible,
      printedRawBid, printedOnlineExecution, printedOnlineAllocation,
      printedPhaseThreeServedMass, printedPhaseThreeResidualPerTail,
      Fin.sum_univ_three] at ha hb htie ⊢
  all_goals nlinarith [log_nine_fifths_pos, log_nine_fifths_lt_three_fifths]

/--
Aggregate three-cohort accounting diagnostic for the corrected printed
instance.  This is not the source-rule bridge; that bridge is proved from the
continuous per-individual state below.
-/
noncomputable def printedCounterexampleCertificate :
    FluidCounterexampleCertificate printedInput where
  execution := printedOnlineExecution
  feasible := printed_online_feasible
  raw_bid_maximal := printed_raw_bid_maximal
  least_spend_tie := printed_least_spend_tie
  offline := printedOfflineExecution
  offline_feasible := printed_offline_feasible
  offline_optimal := printed_offline_optimal

/-- The phase-2 starting state is computed from the phase-1 tail allocation. -/
theorem printed_tail_spentBefore_phaseTwo :
    printedOnlineExecution.spentBefore (1 : Fin 3) (2 : Fin 3) =
      1 / 2 * Real.log (9 / 5) := by
  simp [FluidAllocation.spentBefore, printedOnlineExecution,
    printedOnlineAllocation, printedInput, printedRawBid, Fin.sum_univ_three]

/-- The phase-3 starting state includes both earlier allocation phases. -/
theorem printed_tail_spentBefore_phaseThree :
    printedOnlineExecution.spentBefore (2 : Fin 3) (2 : Fin 3) =
      1 / 2 * Real.log (9 / 5) + 1 / 5 := by
  simp [FluidAllocation.spentBefore, printedOnlineExecution,
    printedOnlineAllocation, printedInput, printedRawBid, Fin.sum_univ_three]
  ring

/-- Serving the actual residual, rather than discarding the whole phase, exhausts the tail. -/
theorem printed_tail_spentAfter_phaseThree :
    printedOnlineExecution.spentAfter (2 : Fin 3) (2 : Fin 3) = 1 / 2 := by
  rw [FluidAllocation.spentAfter_state_update,
    printed_tail_spentBefore_phaseThree]
  simp [printedOnlineExecution, printedOnlineAllocation, printedInput,
    printedRawBid, printedPhaseThreeServedMass,
    printedPhaseThreeResidualPerTail]
  ring

/-- The source's phase-1 plus phase-2 accounting is exactly `3/5`. -/
theorem printed_zero_phaseThree_accounting : (2 / 5 : ℝ) + 2 * (1 / 10) = 3 / 5 := by
  norm_num

/-- Therefore the displayed zero-phase-3 accounting is not the printed decimal `0.62`. -/
theorem printed_zero_phaseThree_accounting_ne_point62 :
    (3 / 5 : ℝ) ≠ 31 / 50 := by
  norm_num

/-- The corrected execution's online revenue. -/
theorem printed_online_value :
    printedCounterexampleCertificate.onlineValue =
      9 / 10 - 1 / 2 * Real.log (9 / 5) := by
  norm_num [FluidCounterexampleCertificate.onlineValue,
    FluidAllocation.revenue, printedCounterexampleCertificate,
    printedOnlineExecution, printedOnlineAllocation, printedInput,
    printedRawBid, Fin.sum_univ_three, printedPhaseThreeServedMass,
    printedPhaseThreeResidualPerTail]
  ring

/-- The explicit feasible offline allocation has value one and is optimal. -/
theorem printed_offline_optimum :
    printedCounterexampleCertificate.offlineOptimum = 1 := by
  norm_num [FluidCounterexampleCertificate.offlineOptimum,
    FluidAllocation.revenue, printedCounterexampleCertificate,
    printedOfflineExecution, printedOfflineAllocation, printedInput,
    printedRawBid, Fin.sum_univ_three]

/-- The true printed-instance factor remains strictly below `1 - 1/e`. -/
theorem printed_true_ratio_lt_msvvRatio :
    9 / 10 - 1 / 2 * Real.log (9 / 5) < 1 - 1 / Real.exp 1 := by
  have hlog := Real.le_log_one_add_of_nonneg (x := (4 / 5 : ℝ)) (by norm_num)
  norm_num at hlog
  have hexp : (8 / 3 : ℝ) < Real.exp 1 :=
    lt_trans (by norm_num) Real.exp_one_gt_d9
  have hinv : 1 / Real.exp 1 < 3 / 8 := by
    rw [div_lt_iff₀ (Real.exp_pos 1)]
    nlinarith
  linarith

/-! ## Printed example: continuous per-individual source-rule bridge -/

/-- Every source bidder has unit budget before normalization by `N`. -/
def printedIndividualBudget (_bidder : ℝ) : ℝ := 1

/-- Most leftover money for a unit-budget bidder is the reverse order of spend. -/
def printedIndividualLeftover (bidder spent : ℝ) : ℝ :=
  printedIndividualBudget bidder - spent

/-- Equal phase-1 spend gives exactly equal leftover money under source unit budgets. -/
theorem printed_phaseOne_equal_leftover_of_eligible
    {r bidder₁ bidder₂ : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 2 / 5)
    (h₁ : printedPhaseOneEligible r bidder₁)
    (h₂ : printedPhaseOneEligible r bidder₂) :
    printedIndividualLeftover bidder₁ (printedPhaseOneSpentBefore r bidder₁) =
      printedIndividualLeftover bidder₂ (printedPhaseOneSpentBefore r bidder₂) := by
  rw [printed_phaseOne_equal_spend_of_eligible hr0 hr h₁ h₂]
  rfl

/-- Equal phase-2 tail spend gives exactly equal leftover money. -/
theorem printed_phaseTwo_equal_leftover_of_tail
    {offset bidder₁ bidder₂ : ℝ} (hoffset0 : 0 ≤ offset)
    (hoffset : offset ≤ 1 / 10)
    (h₁ : 1 / 2 ≤ bidder₁ ∧ bidder₁ ≤ 1)
    (h₂ : 1 / 2 ≤ bidder₂ ∧ bidder₂ ≤ 1) :
    printedIndividualLeftover bidder₁ (printedPhaseTwoSpentBefore offset bidder₁) =
      printedIndividualLeftover bidder₂
        (printedPhaseTwoSpentBefore offset bidder₂) := by
  rw [printed_phaseTwo_equal_spend_of_tail hoffset0 hoffset h₁ h₂]
  rfl

/-- In phase 3 only the query's own tail bidder has a positive raw bid. -/
def printedPhaseThreeRawBid (owner bidder : ℝ) : ℝ :=
  if bidder = owner then 1 else 0

/--
Instantaneous phase-3 allocation to the unique bidder, until its residual unit
budget is exhausted.  Query progress is normalized to the source round's unit
mass (`m` bids of size `a`).
-/
def printedPhaseThreeAllocationRate (progress owner bidder : ℝ) : ℝ :=
  if 0 ≤ progress ∧
      progress ≤ printedPhaseThreeResidualPerTail ∧ bidder = owner then 1 else 0

/-- Phase-3 discarded query rate after the unique bidder is saturated. -/
def printedPhaseThreeDiscardRate (progress : ℝ) : ℝ :=
  if progress ≤ printedPhaseThreeResidualPerTail then 0 else 1

/-- Phase-3 state is computed from both earlier phases and the current allocation integral. -/
noncomputable def printedPhaseThreeSpentBefore (progress owner : ℝ) : ℝ :=
  printedPhaseTwoSpentBefore (1 / 10) owner +
    ∫ s in 0..progress,
      printedPhaseThreeAllocationRate s owner owner *
        printedPhaseThreeRawBid owner owner

/-- During residual service the unique eligible bidder receives the whole query rate. -/
theorem printed_phaseThree_round_conservation
    {progress owner : ℝ} (hprogress0 : 0 ≤ progress) :
    printedPhaseThreeAllocationRate progress owner owner +
        printedPhaseThreeDiscardRate progress = 1 := by
  by_cases hprogress : progress ≤ printedPhaseThreeResidualPerTail
  · simp [printedPhaseThreeAllocationRate, printedPhaseThreeDiscardRate,
      hprogress0, hprogress]
  · simp [printedPhaseThreeAllocationRate, printedPhaseThreeDiscardRate,
      hprogress]

/-- A positive phase-3 bid identifies the unique eligible bidder. -/
theorem printed_phaseThree_positive_bid_only_owner
    {owner bidder : ℝ} (hbid : 0 < printedPhaseThreeRawBid owner bidder) :
    bidder = owner := by
  by_contra hne
  rw [printedPhaseThreeRawBid, if_neg hne] at hbid
  norm_num at hbid

/-- The phase-3 spend path is the integral of its actual allocations. -/
theorem printed_phaseThree_spentBefore_eq
    {progress owner : ℝ} (hprogress0 : 0 ≤ progress)
    (hprogress : progress ≤ printedPhaseThreeResidualPerTail)
    (howner : 1 / 2 ≤ owner ∧ owner ≤ 1) :
    printedPhaseThreeSpentBefore progress owner =
      Real.log (9 / 5) + 2 / 5 + progress := by
  rw [printedPhaseThreeSpentBefore,
    printed_phaseTwo_tail_spentBefore_eq (by norm_num) (by norm_num) howner]
  have hintegral :
      (∫ s in (0 : ℝ)..progress,
        printedPhaseThreeAllocationRate s owner owner *
          printedPhaseThreeRawBid owner owner) = progress := by
    calc
      (∫ s in (0 : ℝ)..progress,
          printedPhaseThreeAllocationRate s owner owner *
            printedPhaseThreeRawBid owner owner) =
          ∫ _s in (0 : ℝ)..progress, (1 : ℝ) := by
            apply intervalIntegral.integral_congr
            intro s hs
            have hsIcc : s ∈ Set.Icc (0 : ℝ) progress := by
              simpa [uIcc_of_le hprogress0] using hs
            simp [printedPhaseThreeAllocationRate, printedPhaseThreeRawBid,
              hsIcc.1, le_trans hsIcc.2 hprogress]
      _ = progress := by simp
  rw [hintegral]
  ring

/-- The corrected residual service exactly exhausts each tail bidder's unit budget. -/
theorem printed_phaseThree_owner_saturated
    {owner : ℝ} (howner : 1 / 2 ≤ owner ∧ owner ≤ 1) :
    printedPhaseThreeSpentBefore printedPhaseThreeResidualPerTail owner = 1 := by
  rw [printed_phaseThree_spentBefore_eq
    printedPhaseThreeResidualPerTail_pos.le le_rfl howner]
  simp [printedPhaseThreeResidualPerTail]
  ring

/-- Positive phase-3 discard occurs only after the sole eligible bidder is saturated. -/
theorem printed_phaseThree_no_discard_unless_saturated
    {progress owner : ℝ} (howner : 1 / 2 ≤ owner ∧ owner ≤ 1)
    (hdiscard : 0 < printedPhaseThreeDiscardRate progress) :
    printedPhaseThreeSpentBefore progress owner = 1 := by
  have hnot : ¬ progress ≤ printedPhaseThreeResidualPerTail := by
    intro hprogress
    simp [printedPhaseThreeDiscardRate, hprogress] at hdiscard
  have hres_lt : printedPhaseThreeResidualPerTail < progress :=
    lt_of_not_ge hnot
  have hprogress0 : 0 ≤ progress :=
    le_trans printedPhaseThreeResidualPerTail_pos.le hres_lt.le
  rw [printedPhaseThreeSpentBefore,
    printed_phaseTwo_tail_spentBefore_eq (by norm_num) (by norm_num) howner]
  have hresIcc :
      printedPhaseThreeResidualPerTail ∈ Set.Icc (0 : ℝ) progress :=
    ⟨printedPhaseThreeResidualPerTail_pos.le, hres_lt.le⟩
  have hintegrand :
      (∫ s in (0 : ℝ)..progress,
          printedPhaseThreeAllocationRate s owner owner *
            printedPhaseThreeRawBid owner owner) =
        ∫ s in (0 : ℝ)..progress,
          Set.indicator
            {s : ℝ | s ≤ printedPhaseThreeResidualPerTail}
            (fun _s : ℝ => (1 : ℝ)) s := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hsIcc : s ∈ Set.Icc (0 : ℝ) progress := by
      simpa [uIcc_of_le hprogress0] using hs
    by_cases hsres : s ≤ printedPhaseThreeResidualPerTail
    · simp [printedPhaseThreeAllocationRate, printedPhaseThreeRawBid,
        hsIcc.1, hsres]
    · simp [printedPhaseThreeAllocationRate, printedPhaseThreeRawBid,
        hsres]
  rw [hintegrand, intervalIntegral.integral_indicator hresIcc]
  simp [printedPhaseThreeResidualPerTail]
  ring

/-- Corrected normalized online value obtained from all three continuous phases. -/
noncomputable def printedContinuousOnlineValue : ℝ :=
  2 / 5 + 2 * (1 / 10) + printedPhaseThreeServedMass

theorem printedContinuousOnlineValue_eq :
    printedContinuousOnlineValue =
      9 / 10 - 1 / 2 * Real.log (9 / 5) := by
  rw [printedContinuousOnlineValue, printedPhaseThreeServedMass_eq]
  ring

/-- Explicit offline allocation spends every unit-budget bidder exactly once. -/
noncomputable def printedContinuousOfflineValue : ℝ :=
  ∫ _bidder in (0 : ℝ)..1, (1 : ℝ)

theorem printedContinuousOfflineValue_eq_one : printedContinuousOfflineValue = 1 := by
  norm_num [printedContinuousOfflineValue]

/--
The source's identity offline assignment has raw bid one in each of the three
owner-indexed phases; the three owner intervals partition the unit population.
-/
theorem printed_continuous_offline_owner_assignment :
    (∀ r : ℝ, 0 ≤ r → r ≤ 2 / 5 →
      printedPhaseOneRawBid r (1 / 10 + r) = 1) ∧
    (∀ offset : ℝ, 0 ≤ offset → offset ≤ 1 / 10 →
      printedPhaseTwoRawBid offset offset = 1) ∧
    (∀ owner : ℝ, 1 / 2 ≤ owner → owner ≤ 1 →
      printedPhaseThreeRawBid owner owner = 1) ∧
    (2 / 5 : ℝ) + 1 / 10 + 1 / 2 = 1 := by
  refine ⟨?_, ?_, ?_, by norm_num⟩
  · intro r hr0 hr
    have hupper : 1 / 10 + r ≤ (1 : ℝ) := by linarith
    have heligible : printedPhaseOneEligible r (1 / 10 + r) :=
      ⟨le_rfl, hupper⟩
    rw [printedPhaseOneRawBid, if_pos heligible]
  · intro offset hoffset0 hoffset
    have hnotTail : ¬ ((1 / 2 : ℝ) ≤ offset ∧ offset ≤ 1) := by
      intro htail
      norm_num at hoffset htail
      linarith
    rw [printedPhaseTwoRawBid, if_neg hnotTail, if_pos rfl]
  · intro owner howner0 howner
    simp [printedPhaseThreeRawBid]

/-- A continuous spend profile is feasible when every source unit budget is respected. -/
def ContinuousUnitBudgetFeasible (spend : ℝ → ℝ) : Prop :=
  IntervalIntegrable spend MeasureTheory.volume 0 1 ∧
    ∀ bidder ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ spend bidder ∧ spend bidder ≤ printedIndividualBudget bidder

/-- Unit budgets bound every feasible normalized offline revenue by one. -/
theorem continuous_unitBudget_revenue_le_one
    {spend : ℝ → ℝ} (hspend : ContinuousUnitBudgetFeasible spend) :
    (∫ bidder in (0 : ℝ)..1, spend bidder) ≤ 1 := by
  have hconst :
      IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) MeasureTheory.volume 0 1 :=
    intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on
    (show (0 : ℝ) ≤ 1 by norm_num) hspend.1 hconst
    (fun bidder hbidder => by
      simpa [printedIndividualBudget] using (hspend.2 bidder hbidder).2)
  norm_num at hmono ⊢
  exact hmono

/-- The unit-spend offline witness is feasible and attains the universal upper bound. -/
theorem printed_continuous_offline_optimal :
    ((∀ r : ℝ, 0 ≤ r → r ≤ 2 / 5 →
        printedPhaseOneRawBid r (1 / 10 + r) = 1) ∧
      (∀ offset : ℝ, 0 ≤ offset → offset ≤ 1 / 10 →
        printedPhaseTwoRawBid offset offset = 1) ∧
      (∀ owner : ℝ, 1 / 2 ≤ owner → owner ≤ 1 →
        printedPhaseThreeRawBid owner owner = 1) ∧
      (2 / 5 : ℝ) + 1 / 10 + 1 / 2 = 1) ∧
    ContinuousUnitBudgetFeasible (fun _bidder : ℝ => (1 : ℝ)) ∧
    printedContinuousOfflineValue = 1 ∧
    ∀ spend : ℝ → ℝ, ContinuousUnitBudgetFeasible spend →
      (∫ bidder in (0 : ℝ)..1, spend bidder) ≤ printedContinuousOfflineValue := by
  refine ⟨printed_continuous_offline_owner_assignment, ?_,
    printedContinuousOfflineValue_eq_one, ?_⟩
  · exact ⟨intervalIntegrable_const, by
      intro bidder hbidder
      simp [printedIndividualBudget]⟩
  · intro spend hspend
    rw [printedContinuousOfflineValue_eq_one]
    exact continuous_unitBudget_revenue_le_one hspend

/--
End-to-end source-rule bridge for the corrected printed example.  Every state
appearing here is allocation-derived; most-leftover comparisons use the
paper's per-individual unit budgets.
-/
theorem printed_continuous_source_execution_bridge :
    (∀ r : ℝ, 0 ≤ r → r ≤ 2 / 5 →
      (∫ _bidder in (1 / 10 + r)..1, printedPhaseOneAllocationRate r) = 1) ∧
    (∀ r bidder₁ bidder₂ : ℝ,
      0 ≤ r → r ≤ 2 / 5 →
      printedPhaseOneEligible r bidder₁ →
      printedPhaseOneEligible r bidder₂ →
        printedPhaseOneRawBid r bidder₁ = printedPhaseOneRawBid r bidder₂ ∧
          printedIndividualLeftover bidder₁
              (printedPhaseOneSpentBefore r bidder₁) =
            printedIndividualLeftover bidder₂
              (printedPhaseOneSpentBefore r bidder₂)) ∧
    (∫ bidder in (1 / 2 : ℝ)..1,
      printedPhaseTwoAllocationDensity bidder) = 1 ∧
    (∀ offset bidder competitor : ℝ,
      0 < printedPhaseTwoAllocationDensity bidder →
      ((1 / 2 ≤ competitor ∧ competitor ≤ 1) ∨ competitor = offset) →
        printedPhaseTwoRawBid offset competitor ≤
          printedPhaseTwoRawBid offset bidder) ∧
    (∀ offset bidder₁ bidder₂ : ℝ,
      0 ≤ offset → offset ≤ 1 / 10 →
      (1 / 2 ≤ bidder₁ ∧ bidder₁ ≤ 1) →
      (1 / 2 ≤ bidder₂ ∧ bidder₂ ≤ 1) →
        printedIndividualLeftover bidder₁
            (printedPhaseTwoSpentBefore offset bidder₁) =
          printedIndividualLeftover bidder₂
            (printedPhaseTwoSpentBefore offset bidder₂)) ∧
    (∀ progress owner : ℝ, 0 ≤ progress →
      printedPhaseThreeAllocationRate progress owner owner +
        printedPhaseThreeDiscardRate progress = 1) ∧
    (∀ progress owner : ℝ,
      (1 / 2 ≤ owner ∧ owner ≤ 1) →
      0 < printedPhaseThreeDiscardRate progress →
        printedPhaseThreeSpentBefore progress owner = 1) ∧
    printedContinuousOnlineValue =
      9 / 10 - 1 / 2 * Real.log (9 / 5) ∧
    printedContinuousOfflineValue = 1 ∧
    printedContinuousOnlineValue / printedContinuousOfflineValue <
      1 - 1 / Real.exp 1 := by
  refine ⟨?_, ?_, printed_phaseTwo_round_conservation, ?_, ?_,
    ?_, ?_,
    printedContinuousOnlineValue_eq, printedContinuousOfflineValue_eq_one, ?_⟩
  · intro r hr0 hr
    exact printed_phaseOne_round_conservation hr0 hr
  · intro r bidder₁ bidder₂ hr0 hr h₁ h₂
    exact ⟨printed_phaseOne_raw_bid_tie_of_eligible h₁ h₂,
      printed_phaseOne_equal_leftover_of_eligible hr0 hr h₁ h₂⟩
  · intro offset bidder competitor hallocated hcompetitor
    exact printed_phaseTwo_raw_bid_maximal hallocated hcompetitor
  · intro offset bidder₁ bidder₂ hoffset0 hoffset h₁ h₂
    exact printed_phaseTwo_equal_leftover_of_tail hoffset0 hoffset h₁ h₂
  · intro progress owner hprogress0
    exact printed_phaseThree_round_conservation hprogress0
  · intro progress owner howner hdiscard
    exact printed_phaseThree_no_discard_unless_saturated howner hdiscard
  · rw [printedContinuousOnlineValue_eq,
      printedContinuousOfflineValue_eq_one, div_one]
    exact printed_true_ratio_lt_msvvRatio

/-! ## An explicit **derived** `κ > 1` family

The paper asserts that the example can be modified for every `κ > 1`, but it
does not print phase parameters.  The following definitions are therefore a
derived construction, not a transcription of a source formula.
-/

/-- Reciprocal bid multiplier `u = 1/κ`. -/
def derivedKappaU (κ : ℝ) : ℝ := κ⁻¹

/-- Exponential abbreviation `z = exp (1-u)`. -/
def derivedKappaZ (κ : ℝ) : ℝ := Real.exp (1 - derivedKappaU κ)

/-- Auxiliary square `y = u²`. -/
def derivedKappaY (κ : ℝ) : ℝ := derivedKappaU κ ^ 2

/-- Common denominator `z+y`. -/
def derivedKappaDenominator (κ : ℝ) : ℝ := derivedKappaZ κ + derivedKappaY κ

/-- Tail fraction `t = 1/(z+y)`. -/
def derivedKappaT (κ : ℝ) : ℝ := (derivedKappaDenominator κ)⁻¹

/-- Low-bid phase fraction `x = y/(z+y)`. -/
def derivedKappaX (κ : ℝ) : ℝ :=
  derivedKappaY κ / derivedKappaDenominator κ

/-- First-phase length `b = (z-1)/(z+y)`. -/
def derivedKappaB (κ : ℝ) : ℝ :=
  (derivedKappaZ κ - 1) / derivedKappaDenominator κ

/-- Online factor of the derived family. -/
def derivedKappaRatio (κ : ℝ) : ℝ :=
  (derivedKappaZ κ - 1 + derivedKappaU κ) /
    derivedKappaDenominator κ

theorem derivedKappaU_pos {κ : ℝ} (hκ : 1 < κ) : 0 < derivedKappaU κ := by
  exact inv_pos.mpr (lt_trans zero_lt_one hκ)

theorem derivedKappaU_lt_one {κ : ℝ} (hκ : 1 < κ) : derivedKappaU κ < 1 := by
  simpa [derivedKappaU] using (inv_lt_one₀ (lt_trans zero_lt_one hκ)).mpr hκ

theorem derivedKappaZ_gt_one {κ : ℝ} (hκ : 1 < κ) : 1 < derivedKappaZ κ := by
  rw [derivedKappaZ, Real.one_lt_exp_iff]
  linarith [derivedKappaU_lt_one hκ]

theorem derivedKappaDenominator_pos {κ : ℝ} (hκ : 1 < κ) :
    0 < derivedKappaDenominator κ := by
  exact add_pos (lt_trans zero_lt_one (derivedKappaZ_gt_one hκ))
    (sq_pos_of_pos (derivedKappaU_pos hκ))

theorem derivedKappaT_pos {κ : ℝ} (hκ : 1 < κ) : 0 < derivedKappaT κ := by
  exact inv_pos.mpr (derivedKappaDenominator_pos hκ)

theorem derivedKappaX_pos {κ : ℝ} (hκ : 1 < κ) : 0 < derivedKappaX κ := by
  exact div_pos (sq_pos_of_pos (derivedKappaU_pos hκ))
    (derivedKappaDenominator_pos hκ)

theorem derivedKappaB_pos {κ : ℝ} (hκ : 1 < κ) : 0 < derivedKappaB κ := by
  exact div_pos (sub_pos.mpr (derivedKappaZ_gt_one hκ))
    (derivedKappaDenominator_pos hκ)

/-- The three derived phase lengths partition the unit interval. -/
theorem derivedKappa_phase_fractions_sum {κ : ℝ} (hκ : 1 < κ) :
    derivedKappaX κ + derivedKappaB κ + derivedKappaT κ = 1 := by
  have hden := ne_of_gt (derivedKappaDenominator_pos hκ)
  unfold derivedKappaX derivedKappaB derivedKappaT
  field_simp [hden]
  simp [derivedKappaDenominator, add_comm]
  ring

theorem derivedKappa_one_sub_x_eq_z_mul_t {κ : ℝ} (hκ : 1 < κ) :
    1 - derivedKappaX κ = derivedKappaZ κ * derivedKappaT κ := by
  have hden := ne_of_gt (derivedKappaDenominator_pos hκ)
  unfold derivedKappaX derivedKappaT
  field_simp [hden]
  simp [derivedKappaDenominator, add_comm]

/-- The phase-1 tail spend is the source-shaped equal-sharing integral `log z`. -/
theorem derivedKappa_phaseOne_tail_spend_log_z {κ : ℝ} (hκ : 1 < κ) :
    Real.log ((1 - derivedKappaX κ) / derivedKappaT κ) =
      Real.log (derivedKappaZ κ) := by
  rw [derivedKappa_one_sub_x_eq_z_mul_t hκ]
  have ht := ne_of_gt (derivedKappaT_pos hκ)
  field_simp [ht]

/-- Since `z = exp (1-u)`, the phase-1 spend is exactly `1-u`. -/
theorem derivedKappa_phaseOne_tail_spend {κ : ℝ} (hκ : 1 < κ) :
    Real.log ((1 - derivedKappaX κ) / derivedKappaT κ) =
      1 - derivedKappaU κ := by
  rw [derivedKappa_phaseOne_tail_spend_log_z hκ, derivedKappaZ,
    Real.log_exp]

/-- The high-bid phase adds `κ*x/t = u` to every tail budget. -/
theorem derivedKappa_phaseTwo_tail_spend {κ : ℝ} (hκ : 1 < κ) :
    κ * derivedKappaX κ / derivedKappaT κ = derivedKappaU κ := by
  have hκ0 : κ ≠ 0 := ne_of_gt (lt_trans zero_lt_one hκ)
  have hden := ne_of_gt (derivedKappaDenominator_pos hκ)
  unfold derivedKappaX derivedKappaT derivedKappaY derivedKappaU
  field_simp [hκ0, hden]

/-- Unlike the printed `κ=2` parameters, the derived family exhausts the tail exactly. -/
theorem derivedKappa_exact_tail_exhaustion {κ : ℝ} (hκ : 1 < κ) :
    Real.log ((1 - derivedKappaX κ) / derivedKappaT κ) +
      κ * derivedKappaX κ / derivedKappaT κ = 1 := by
  rw [derivedKappa_phaseOne_tail_spend hκ,
    derivedKappa_phaseTwo_tail_spend hκ]
  ring

/-- The explicit offline allocation exhausts the three cohort budgets. -/
theorem derivedKappa_offline_value {κ : ℝ} (hκ : 1 < κ) :
    derivedKappaB κ + derivedKappaX κ + derivedKappaT κ = 1 := by
  linarith [derivedKappa_phase_fractions_sum hκ]

/-- Phase 1 plus the high-bid phase has the advertised closed form. -/
theorem derivedKappa_online_factor {κ : ℝ} (hκ : 1 < κ) :
    derivedKappaB κ + κ * derivedKappaX κ = derivedKappaRatio κ := by
  have hκ0 : κ ≠ 0 := ne_of_gt (lt_trans zero_lt_one hκ)
  have hden := ne_of_gt (derivedKappaDenominator_pos hκ)
  unfold derivedKappaB derivedKappaX derivedKappaRatio derivedKappaY
    derivedKappaU
  field_simp [hκ0, hden]

/-! ### Generic continuous per-individual execution of the DERIVED family -/

theorem derivedKappa_one_sub_x_sub_b_eq_t {κ : ℝ} (hκ : 1 < κ) :
    1 - derivedKappaX κ - derivedKappaB κ = derivedKappaT κ := by
  linarith [derivedKappa_phase_fractions_sum hκ]

/-- Bidder `bidder` remains active at phase-1 progress `progress`. -/
def derivedKappaPhaseOneEligible (κ progress bidder : ℝ) : Prop :=
  derivedKappaX κ + progress ≤ bidder ∧ bidder ≤ 1

/-- Equal-sharing allocation density over the active phase-1 interval. -/
def derivedKappaPhaseOneAllocationRate (κ progress : ℝ) : ℝ :=
  (1 - derivedKappaX κ - progress)⁻¹

/-- All eligible phase-1 bidders have the same normalized raw bid. -/
def derivedKappaPhaseOneRawBid (κ progress bidder : ℝ) : ℝ :=
  if derivedKappaPhaseOneEligible κ progress bidder then 1 else 0

theorem derivedKappa_phaseOne_raw_bid_tie_of_eligible
    {κ progress bidder₁ bidder₂ : ℝ}
    (h₁ : derivedKappaPhaseOneEligible κ progress bidder₁)
    (h₂ : derivedKappaPhaseOneEligible κ progress bidder₂) :
    derivedKappaPhaseOneRawBid κ progress bidder₁ =
      derivedKappaPhaseOneRawBid κ progress bidder₂ := by
  simp [derivedKappaPhaseOneRawBid, h₁, h₂]

/-- Phase-1 per-individual spend derived from the allocation-density integral. -/
noncomputable def derivedKappaPhaseOneSpentBefore
    (κ progress bidder : ℝ) : ℝ :=
  ∫ s in 0..progress,
    if derivedKappaPhaseOneEligible κ s bidder then
      derivedKappaPhaseOneAllocationRate κ s
    else 0

theorem derivedKappa_phaseOne_active_length_pos
    {κ progress : ℝ} (hκ : 1 < κ) (hprogress : progress ≤ derivedKappaB κ) :
    0 < 1 - derivedKappaX κ - progress := by
  have ht := derivedKappaT_pos hκ
  rw [← derivedKappa_one_sub_x_sub_b_eq_t hκ] at ht
  linarith

/-- Every phase-1 instant allocates exactly one unit of query mass. -/
theorem derivedKappa_phaseOne_round_conservation
    {κ progress : ℝ} (hκ : 1 < κ) (hprogress0 : 0 ≤ progress)
    (hprogress : progress ≤ derivedKappaB κ) :
    (∫ _bidder in (derivedKappaX κ + progress)..1,
      derivedKappaPhaseOneAllocationRate κ progress) = 1 := by
  have hden := derivedKappa_phaseOne_active_length_pos hκ hprogress
  simp [derivedKappaPhaseOneAllocationRate, ne_of_gt hden]
  field_simp [ne_of_gt hden]
  ring

/-- Eligible phase-1 bidders receive the integral of the common rate. -/
theorem derivedKappa_phaseOne_spentBefore_eq_integral
    {κ progress bidder : ℝ} (hκ : 1 < κ) (hprogress0 : 0 ≤ progress)
    (hprogress : progress ≤ derivedKappaB κ)
    (hbidder : derivedKappaPhaseOneEligible κ progress bidder) :
    derivedKappaPhaseOneSpentBefore κ progress bidder =
      ∫ s in 0..progress, derivedKappaPhaseOneAllocationRate κ s := by
  rw [derivedKappaPhaseOneSpentBefore]
  apply intervalIntegral.integral_congr
  intro s hs
  have hsIcc : s ∈ Set.Icc (0 : ℝ) progress := by
    simpa [uIcc_of_le hprogress0] using hs
  have heligible : derivedKappaPhaseOneEligible κ s bidder := by
    constructor
    · linarith [hsIcc.2, hbidder.1]
    · exact hbidder.2
  simp [heligible]

/-- Closed form of the allocation-derived phase-1 state. -/
theorem derivedKappa_phaseOne_spentBefore_eq_log
    {κ progress bidder : ℝ} (hκ : 1 < κ) (hprogress0 : 0 ≤ progress)
    (hprogress : progress ≤ derivedKappaB κ)
    (hbidder : derivedKappaPhaseOneEligible κ progress bidder) :
    derivedKappaPhaseOneSpentBefore κ progress bidder =
      Real.log ((1 - derivedKappaX κ) /
        (1 - derivedKappaX κ - progress)) := by
  rw [derivedKappa_phaseOne_spentBefore_eq_integral hκ hprogress0 hprogress hbidder]
  simp only [derivedKappaPhaseOneAllocationRate]
  rw [
    intervalIntegral.integral_comp_sub_left
      (fun x : ℝ => x⁻¹) (1 - derivedKappaX κ)]
  have hbottom := derivedKappa_phaseOne_active_length_pos hκ hprogress
  have htop : 0 < 1 - derivedKappaX κ := by
    linarith [hbottom, hprogress0]
  rw [show 1 - derivedKappaX κ - 0 = 1 - derivedKappaX κ by ring]
  exact integral_inv_of_pos hbottom htop

/-- Phase-1 highest-bid ties are broken honestly by equal unit-budget leftover. -/
theorem derivedKappa_phaseOne_equal_leftover_of_eligible
    {κ progress bidder₁ bidder₂ : ℝ} (hκ : 1 < κ)
    (hprogress0 : 0 ≤ progress) (hprogress : progress ≤ derivedKappaB κ)
    (h₁ : derivedKappaPhaseOneEligible κ progress bidder₁)
    (h₂ : derivedKappaPhaseOneEligible κ progress bidder₂) :
    printedIndividualLeftover bidder₁
        (derivedKappaPhaseOneSpentBefore κ progress bidder₁) =
      printedIndividualLeftover bidder₂
        (derivedKappaPhaseOneSpentBefore κ progress bidder₂) := by
  rw [derivedKappa_phaseOne_spentBefore_eq_log hκ hprogress0 hprogress h₁,
    derivedKappa_phaseOne_spentBefore_eq_log hκ hprogress0 hprogress h₂]
  rfl

/-- Tail coordinates occupy the final interval of mass `t`. -/
def derivedKappaTail (κ bidder : ℝ) : Prop :=
  1 - derivedKappaT κ ≤ bidder ∧ bidder ≤ 1

/-- Every tail bidder's allocation-derived phase-1 spend is exactly `1-u`. -/
theorem derivedKappa_phaseOne_tail_spent_end
    {κ bidder : ℝ} (hκ : 1 < κ) (hbidder : derivedKappaTail κ bidder) :
    derivedKappaPhaseOneSpentBefore κ (derivedKappaB κ) bidder =
      1 - derivedKappaU κ := by
  have heligible :
      derivedKappaPhaseOneEligible κ (derivedKappaB κ) bidder := by
    constructor
    · have hstart : derivedKappaX κ + derivedKappaB κ =
          1 - derivedKappaT κ := by
        linarith [derivedKappa_phase_fractions_sum hκ]
      rw [hstart]
      exact hbidder.1
    · exact hbidder.2
  rw [derivedKappa_phaseOne_spentBefore_eq_log hκ
    (derivedKappaB_pos hκ).le le_rfl heligible]
  rw [show 1 - derivedKappaX κ - derivedKappaB κ = derivedKappaT κ
    from derivedKappa_one_sub_x_sub_b_eq_t hκ]
  exact derivedKappa_phaseOne_tail_spend hκ

/-- Tail bidders bid `kappa` in phase 2; the entering low bidder bids one. -/
def derivedKappaPhaseTwoRawBid (κ offset bidder : ℝ) : ℝ :=
  if derivedKappaTail κ bidder then κ
  else if bidder = offset then 1 else 0

/-- Phase 2 shares every query uniformly across the tail interval of mass `t`. -/
def derivedKappaPhaseTwoAllocationDensity (κ bidder : ℝ) : ℝ :=
  if derivedKappaTail κ bidder then (derivedKappaT κ)⁻¹ else 0

/-- Phase-2 spend is the phase-1 state plus the integral of actual bids and allocations. -/
noncomputable def derivedKappaPhaseTwoSpentBefore
    (κ offset bidder : ℝ) : ℝ :=
  derivedKappaPhaseOneSpentBefore κ (derivedKappaB κ) bidder +
    ∫ s in 0..offset,
      derivedKappaPhaseTwoRawBid κ s bidder *
        derivedKappaPhaseTwoAllocationDensity κ bidder

/-- Every phase-2 instant allocates exactly one unit of query mass. -/
theorem derivedKappa_phaseTwo_round_conservation {κ : ℝ} (hκ : 1 < κ) :
    (∫ bidder in (1 - derivedKappaT κ)..1,
      derivedKappaPhaseTwoAllocationDensity κ bidder) = 1 := by
  have ht := derivedKappaT_pos hκ
  calc
    (∫ bidder in (1 - derivedKappaT κ)..1,
        derivedKappaPhaseTwoAllocationDensity κ bidder) =
        ∫ _bidder in (1 - derivedKappaT κ)..1,
          (derivedKappaT κ)⁻¹ := by
            apply intervalIntegral.integral_congr
            intro bidder hbidder
            have hb : 1 - derivedKappaT κ ≤ bidder ∧ bidder ≤ 1 := by
              rw [uIcc_of_le (by linarith : 1 - derivedKappaT κ ≤ 1)] at hbidder
              exact ⟨hbidder.1, hbidder.2⟩
            rw [derivedKappaPhaseTwoAllocationDensity,
              if_pos (show derivedKappaTail κ bidder from hb)]
    _ = derivedKappaT κ * (derivedKappaT κ)⁻¹ := by
      simp
    _ = 1 := mul_inv_cancel₀ (ne_of_gt ht)

/-- Allocated phase-2 bidders have a maximal raw bid at every offset. -/
theorem derivedKappa_phaseTwo_raw_bid_maximal
    {κ offset bidder competitor : ℝ} (hκ : 1 < κ)
    (hallocated : 0 < derivedKappaPhaseTwoAllocationDensity κ bidder)
    (hcompetitor : derivedKappaTail κ competitor ∨ competitor = offset) :
    derivedKappaPhaseTwoRawBid κ offset competitor ≤
      derivedKappaPhaseTwoRawBid κ offset bidder := by
  have htail : derivedKappaTail κ bidder := by
    by_contra h
    rw [derivedKappaPhaseTwoAllocationDensity, if_neg h] at hallocated
    linarith
  have hbidderRaw : derivedKappaPhaseTwoRawBid κ offset bidder = κ := by
    rw [derivedKappaPhaseTwoRawBid, if_pos htail]
  rw [hbidderRaw]
  rcases hcompetitor with hcompetitor | hcompetitor
  · have hcompetitorRaw :
        derivedKappaPhaseTwoRawBid κ offset competitor = κ := by
      rw [derivedKappaPhaseTwoRawBid, if_pos hcompetitor]
    rw [hcompetitorRaw]
  · rw [hcompetitor]
    by_cases hoffsetTail : derivedKappaTail κ offset
    · have hoffsetRaw : derivedKappaPhaseTwoRawBid κ offset offset = κ := by
        rw [derivedKappaPhaseTwoRawBid, if_pos hoffsetTail]
      rw [hoffsetRaw]
    · have hoffsetRaw : derivedKappaPhaseTwoRawBid κ offset offset = 1 := by
        rw [derivedKappaPhaseTwoRawBid, if_neg hoffsetTail, if_pos rfl]
      rw [hoffsetRaw]
      exact hκ.le

/-- Closed form of every tail bidder's allocation-derived phase-2 state. -/
theorem derivedKappa_phaseTwo_tail_spentBefore_eq
    {κ offset bidder : ℝ} (hκ : 1 < κ) (hoffset0 : 0 ≤ offset)
    (hoffset : offset ≤ derivedKappaX κ)
    (hbidder : derivedKappaTail κ bidder) :
    derivedKappaPhaseTwoSpentBefore κ offset bidder =
      1 - derivedKappaU κ + κ * offset / derivedKappaT κ := by
  rw [derivedKappaPhaseTwoSpentBefore,
    derivedKappa_phaseOne_tail_spent_end hκ hbidder]
  have hintegral :
      (∫ s in (0 : ℝ)..offset,
        derivedKappaPhaseTwoRawBid κ s bidder *
          derivedKappaPhaseTwoAllocationDensity κ bidder) =
        κ * offset / derivedKappaT κ := by
    simp only [derivedKappaPhaseTwoRawBid,
      derivedKappaPhaseTwoAllocationDensity, if_pos hbidder]
    simp
    ring
  rw [hintegral]

/-- All maximal-bid tail bidders have equal unit-budget leftover through phase 2. -/
theorem derivedKappa_phaseTwo_equal_leftover_of_tail
    {κ offset bidder₁ bidder₂ : ℝ} (hκ : 1 < κ)
    (hoffset0 : 0 ≤ offset) (hoffset : offset ≤ derivedKappaX κ)
    (h₁ : derivedKappaTail κ bidder₁) (h₂ : derivedKappaTail κ bidder₂) :
    printedIndividualLeftover bidder₁
        (derivedKappaPhaseTwoSpentBefore κ offset bidder₁) =
      printedIndividualLeftover bidder₂
        (derivedKappaPhaseTwoSpentBefore κ offset bidder₂) := by
  rw [derivedKappa_phaseTwo_tail_spentBefore_eq hκ hoffset0 hoffset h₁,
    derivedKappa_phaseTwo_tail_spentBefore_eq hκ hoffset0 hoffset h₂]
  rfl

/-- Every tail bidder is exactly exhausted at the end of phase 2. -/
theorem derivedKappa_phaseTwo_tail_exhausted
    {κ bidder : ℝ} (hκ : 1 < κ) (hbidder : derivedKappaTail κ bidder) :
    derivedKappaPhaseTwoSpentBefore κ (derivedKappaX κ) bidder = 1 := by
  rw [derivedKappa_phaseTwo_tail_spentBefore_eq hκ
    (derivedKappaX_pos hκ).le le_rfl hbidder,
    derivedKappa_phaseTwo_tail_spend hκ]
  ring

/-- Phase 3 has only the corresponding exhausted tail bidder eligible. -/
def derivedKappaPhaseThreeRawBid (owner bidder : ℝ) : ℝ :=
  if bidder = owner then 1 else 0

def derivedKappaPhaseThreeAllocationRate (_owner _bidder : ℝ) : ℝ := 0
def derivedKappaPhaseThreeDiscardRate (_owner : ℝ) : ℝ := 1

theorem derivedKappa_phaseThree_round_conservation (owner : ℝ) :
    derivedKappaPhaseThreeAllocationRate owner owner +
      derivedKappaPhaseThreeDiscardRate owner = 1 := by
  simp [derivedKappaPhaseThreeAllocationRate,
    derivedKappaPhaseThreeDiscardRate]

theorem derivedKappa_phaseThree_positive_bid_only_owner
    {owner bidder : ℝ} (hbid : 0 < derivedKappaPhaseThreeRawBid owner bidder) :
    bidder = owner := by
  by_contra hne
  rw [derivedKappaPhaseThreeRawBid, if_neg hne] at hbid
  norm_num at hbid

/-- Phase-3 discard is justified by the unique eligible bidder's prior exhaustion. -/
theorem derivedKappa_phaseThree_discard_of_saturated
    {κ owner : ℝ} (hκ : 1 < κ) (howner : derivedKappaTail κ owner) :
    derivedKappaPhaseThreeDiscardRate owner = 1 ∧
      derivedKappaPhaseTwoSpentBefore κ (derivedKappaX κ) owner =
        printedIndividualBudget owner := by
  exact ⟨rfl, by
    rw [derivedKappa_phaseTwo_tail_exhausted hκ howner]
    rfl⟩

/-- Online value of the generic continuous source-rule execution. -/
noncomputable def derivedKappaContinuousOnlineValue (κ : ℝ) : ℝ :=
  derivedKappaB κ + κ * derivedKappaX κ

theorem derivedKappaContinuousOnlineValue_eq
    {κ : ℝ} (hκ : 1 < κ) :
    derivedKappaContinuousOnlineValue κ = derivedKappaRatio κ := by
  exact derivedKappa_online_factor hκ

/-- Unit-budget offline value of the derived normalized family. -/
noncomputable def derivedKappaContinuousOfflineValue (κ : ℝ) : ℝ :=
  derivedKappaB κ + derivedKappaX κ + derivedKappaT κ

theorem derivedKappaContinuousOfflineValue_eq_one
    {κ : ℝ} (hκ : 1 < κ) :
    derivedKappaContinuousOfflineValue κ = 1 := by
  exact derivedKappa_offline_value hκ

/-- The unit-spend witness attains the universal unit-budget upper bound. -/
theorem derivedKappa_continuous_offline_optimal
    {κ : ℝ} (hκ : 1 < κ) :
    ContinuousUnitBudgetFeasible (fun _bidder : ℝ => (1 : ℝ)) ∧
    derivedKappaContinuousOfflineValue κ = 1 ∧
    ∀ spend : ℝ → ℝ, ContinuousUnitBudgetFeasible spend →
      (∫ bidder in (0 : ℝ)..1, spend bidder) ≤
        derivedKappaContinuousOfflineValue κ := by
  refine ⟨printed_continuous_offline_optimal.2.1,
    derivedKappaContinuousOfflineValue_eq_one hκ, ?_⟩
  intro spend hspend
  rw [derivedKappaContinuousOfflineValue_eq_one hκ]
  exact continuous_unitBudget_revenue_le_one hspend

/--
End-to-end continuous source-rule execution for every member of the DERIVED
family.  The ratio and both later limit theorems refer to this execution value,
not to the coarse three-cohort accounting diagnostic.
-/
theorem derivedKappa_continuous_source_execution_bridge
    {κ : ℝ} (hκ : 1 < κ) :
    (∀ progress : ℝ, 0 ≤ progress → progress ≤ derivedKappaB κ →
      (∫ _bidder in (derivedKappaX κ + progress)..1,
        derivedKappaPhaseOneAllocationRate κ progress) = 1) ∧
    (∀ progress bidder₁ bidder₂ : ℝ,
      0 ≤ progress → progress ≤ derivedKappaB κ →
      derivedKappaPhaseOneEligible κ progress bidder₁ →
      derivedKappaPhaseOneEligible κ progress bidder₂ →
        derivedKappaPhaseOneRawBid κ progress bidder₁ =
            derivedKappaPhaseOneRawBid κ progress bidder₂ ∧
          printedIndividualLeftover bidder₁
              (derivedKappaPhaseOneSpentBefore κ progress bidder₁) =
            printedIndividualLeftover bidder₂
              (derivedKappaPhaseOneSpentBefore κ progress bidder₂)) ∧
    (∫ bidder in (1 - derivedKappaT κ)..1,
      derivedKappaPhaseTwoAllocationDensity κ bidder) = 1 ∧
    (∀ offset bidder competitor : ℝ,
      0 < derivedKappaPhaseTwoAllocationDensity κ bidder →
      (derivedKappaTail κ competitor ∨ competitor = offset) →
        derivedKappaPhaseTwoRawBid κ offset competitor ≤
          derivedKappaPhaseTwoRawBid κ offset bidder) ∧
    (∀ offset bidder₁ bidder₂ : ℝ,
      0 ≤ offset → offset ≤ derivedKappaX κ →
      derivedKappaTail κ bidder₁ → derivedKappaTail κ bidder₂ →
        printedIndividualLeftover bidder₁
            (derivedKappaPhaseTwoSpentBefore κ offset bidder₁) =
          printedIndividualLeftover bidder₂
            (derivedKappaPhaseTwoSpentBefore κ offset bidder₂)) ∧
    (∀ bidder : ℝ, derivedKappaTail κ bidder →
      derivedKappaPhaseTwoSpentBefore κ (derivedKappaX κ) bidder = 1) ∧
    (∀ owner : ℝ, derivedKappaTail κ owner →
      derivedKappaPhaseThreeAllocationRate owner owner +
          derivedKappaPhaseThreeDiscardRate owner = 1 ∧
        derivedKappaPhaseTwoSpentBefore κ (derivedKappaX κ) owner = 1 ∧
        ∀ bidder : ℝ, 0 < derivedKappaPhaseThreeRawBid owner bidder →
          bidder = owner) ∧
    derivedKappaContinuousOnlineValue κ = derivedKappaRatio κ ∧
    derivedKappaContinuousOfflineValue κ = 1 := by
  refine ⟨?_, ?_, derivedKappa_phaseTwo_round_conservation hκ,
    ?_, ?_, ?_, ?_, derivedKappaContinuousOnlineValue_eq hκ,
    derivedKappaContinuousOfflineValue_eq_one hκ⟩
  · intro progress hprogress0 hprogress
    exact derivedKappa_phaseOne_round_conservation hκ hprogress0 hprogress
  · intro progress bidder₁ bidder₂ hprogress0 hprogress h₁ h₂
    exact ⟨derivedKappa_phaseOne_raw_bid_tie_of_eligible h₁ h₂,
      derivedKappa_phaseOne_equal_leftover_of_eligible
        hκ hprogress0 hprogress h₁ h₂⟩
  · intro offset bidder competitor hallocated hcompetitor
    exact derivedKappa_phaseTwo_raw_bid_maximal hκ hallocated hcompetitor
  · intro offset bidder₁ bidder₂ hoffset0 hoffset h₁ h₂
    exact derivedKappa_phaseTwo_equal_leftover_of_tail
      hκ hoffset0 hoffset h₁ h₂
  · intro bidder hbidder
    exact derivedKappa_phaseTwo_tail_exhausted hκ hbidder
  · intro owner howner
    refine ⟨derivedKappa_phaseThree_round_conservation owner,
      derivedKappa_phaseTwo_tail_exhausted hκ howner, ?_⟩
    intro bidder hbid
    exact derivedKappa_phaseThree_positive_bid_only_owner hbid

/-
The former `Fin 3` aggregate certificate for the DERIVED family is retired.
It encoded only cohort-boundary accounting and is intentionally not compiled:
the continuous per-individual bridge above is the proof-bearing object.

/-! ### The derived family's allocation certificate -/

def derivedKappaBudget (κ : ℝ) (a : Fin 3) : ℝ :=
  match a.1 with
  | 0 => derivedKappaX κ
  | 1 => derivedKappaB κ
  | _ => derivedKappaT κ

def derivedKappaQueryMass (κ : ℝ) (r : Fin 3) : ℝ :=
  match r.1 with
  | 0 => derivedKappaB κ
  | 1 => derivedKappaX κ
  | _ => derivedKappaT κ

def derivedKappaRawBid (κ : ℝ) (r a : Fin 3) : ℝ :=
  match r.1, a.1 with
  | 0, 1 => 1
  | 0, 2 => 1
  | 1, 0 => 1
  | 1, 2 => κ
  | 2, 2 => 1
  | _, _ => 0

def derivedKappaInput (κ : ℝ) : FluidInput 3 (Fin 3) where
  budget := derivedKappaBudget κ
  queryMass := derivedKappaQueryMass κ
  eligible := printedEligible
  rawBid := derivedKappaRawBid κ

/-- Actual allocation of the derived family; phase 3 is discarded after exact exhaustion. -/
noncomputable def derivedKappaOnlineAllocation (κ : ℝ) (r a : Fin 3) : ℝ :=
  match r.1, a.1 with
  | 0, 1 => derivedKappaB κ - derivedKappaT κ * (1 - derivedKappaU κ)
  | 0, 2 => derivedKappaT κ * (1 - derivedKappaU κ)
  | 1, 2 => derivedKappaX κ
  | _, _ => 0

noncomputable def derivedKappaOnlineExecution (κ : ℝ) :
    FluidAllocation (derivedKappaInput κ) where
  allocation := derivedKappaOnlineAllocation κ
  discard := fun r => if r.1 = 2 then derivedKappaT κ else 0

def derivedKappaOfflineAllocation (κ : ℝ) (r a : Fin 3) : ℝ :=
  match r.1, a.1 with
  | 0, 1 => derivedKappaB κ
  | 1, 0 => derivedKappaX κ
  | 2, 2 => derivedKappaT κ
  | _, _ => 0

def derivedKappaOfflineExecution (κ : ℝ) :
    FluidAllocation (derivedKappaInput κ) where
  allocation := derivedKappaOfflineAllocation κ
  discard := fun _ => 0

private theorem derivedKappa_phaseOne_middle_allocation_pos
    {κ : ℝ} (hκ : 1 < κ) :
    0 < derivedKappaB κ - derivedKappaT κ * (1 - derivedKappaU κ) := by
  have hu0 := derivedKappaU_pos hκ
  have hu1 := derivedKappaU_lt_one hκ
  have hstrict : 1 + (1 - derivedKappaU κ) < derivedKappaZ κ := by
    rw [derivedKappaZ]
    exact Real.add_one_lt_exp (by linarith)
  have hden := derivedKappaDenominator_pos hκ
  simp only [derivedKappaB, derivedKappaT]
  rw [sub_pos, div_eq_mul_inv]
  rw [mul_lt_mul_right (inv_pos.mpr hden)]
  linarith

private theorem derivedKappa_tail_spend_identity
    {κ : ℝ} (hκ : 1 < κ) :
    derivedKappaT κ * (1 - derivedKappaU κ) +
      derivedKappaX κ * κ = derivedKappaT κ := by
  have hκ0 : κ ≠ 0 := ne_of_gt (lt_trans zero_lt_one hκ)
  have hden := ne_of_gt (derivedKappaDenominator_pos hκ)
  simp only [derivedKappaT, derivedKappaX, derivedKappaY,
    derivedKappaU, derivedKappaDenominator]
  field_simp
  ring

private theorem derivedKappa_online_feasible
    {κ : ℝ} (hκ : 1 < κ) : FluidFeasible (derivedKappaOnlineExecution κ) := by
  constructor
  · intro r a
    fin_cases r <;> fin_cases a <;>
      simp [derivedKappaOnlineExecution, derivedKappaOnlineAllocation]
    all_goals first
      | exact (derivedKappa_phaseOne_middle_allocation_pos hκ).le
      | positivity
      | nlinarith [derivedKappaU_pos hκ, derivedKappaU_lt_one hκ,
          derivedKappaT_pos hκ, derivedKappaX_pos hκ]
  · intro r
    fin_cases r <;>
      simp [derivedKappaOnlineExecution]
    exact (derivedKappaT_pos hκ).le
  · intro r a h
    fin_cases r <;> fin_cases a <;>
      simp [derivedKappaInput, printedEligible, derivedKappaOnlineExecution,
        derivedKappaOnlineAllocation] at h ⊢
  · intro r
    fin_cases r <;>
      simp [derivedKappaInput, derivedKappaQueryMass,
        derivedKappaOnlineExecution, derivedKappaOnlineAllocation,
        Fin.sum_univ_three]
    all_goals ring
  · intro a
    fin_cases a
    · simp [FluidAllocation.finalSpend, derivedKappaInput,
        derivedKappaBudget, derivedKappaRawBid,
        derivedKappaOnlineExecution, derivedKappaOnlineAllocation,
        Fin.sum_univ_three]
      exact (derivedKappaX_pos hκ).le
    · simp [FluidAllocation.finalSpend, derivedKappaInput,
        derivedKappaBudget, derivedKappaRawBid,
        derivedKappaOnlineExecution, derivedKappaOnlineAllocation,
        Fin.sum_univ_three]
      exact (derivedKappa_phaseOne_middle_allocation_pos hκ).le
    · simp [FluidAllocation.finalSpend, derivedKappaInput,
        derivedKappaBudget, derivedKappaRawBid,
        derivedKappaOnlineExecution, derivedKappaOnlineAllocation,
        Fin.sum_univ_three]
      exact le_of_eq (derivedKappa_tail_spend_identity hκ)

private theorem derivedKappa_offline_feasible
    {κ : ℝ} (hκ : 1 < κ) : FluidFeasible (derivedKappaOfflineExecution κ) := by
  constructor
  · intro r a
    fin_cases r <;> fin_cases a <;>
      simp [derivedKappaOfflineExecution, derivedKappaOfflineAllocation]
    all_goals positivity
  · intro r
    simp [derivedKappaOfflineExecution]
  · intro r a h
    fin_cases r <;> fin_cases a <;>
      simp [derivedKappaInput, printedEligible, derivedKappaOfflineExecution,
        derivedKappaOfflineAllocation] at h ⊢
  · intro r
    fin_cases r <;>
      simp [derivedKappaInput, derivedKappaQueryMass,
        derivedKappaOfflineExecution, derivedKappaOfflineAllocation,
        Fin.sum_univ_three]
  · intro a
    fin_cases a <;>
      simp [FluidAllocation.finalSpend, derivedKappaInput,
        derivedKappaBudget, derivedKappaRawBid,
        derivedKappaOfflineExecution, derivedKappaOfflineAllocation,
        Fin.sum_univ_three]

private theorem derivedKappa_offline_optimal
    {κ : ℝ} (hκ : 1 < κ) (alternative : FluidAllocation (derivedKappaInput κ))
    (hfeasible : FluidFeasible alternative) :
    alternative.revenue ≤ (derivedKappaOfflineExecution κ).revenue := by
  rw [FluidAllocation.revenue_eq_sum_finalSpend]
  calc
    (∑ a : Fin 3, alternative.finalSpend a) ≤
        ∑ a : Fin 3, (derivedKappaInput κ).budget a := by
      exact Finset.sum_le_sum fun a _ => hfeasible.final_budget_feasible a
    _ = 1 := by
      simp [derivedKappaInput, derivedKappaBudget, Fin.sum_univ_three]
      linarith [derivedKappa_phase_fractions_sum hκ]
    _ = (derivedKappaOfflineExecution κ).revenue := by
      simp [FluidAllocation.revenue, derivedKappaInput, derivedKappaRawBid,
        derivedKappaOfflineExecution, derivedKappaOfflineAllocation,
        Fin.sum_univ_three]
      linarith [derivedKappa_phase_fractions_sum hκ]

private theorem derivedKappa_raw_bid_maximal {κ : ℝ} (hκ : 1 < κ) :
    ∀ r a, 0 < (derivedKappaOnlineExecution κ).allocation r a →
      ∀ b, (derivedKappaInput κ).eligible r b →
        (derivedKappaOnlineExecution κ).spentBefore r b <
          (derivedKappaInput κ).budget b →
        (derivedKappaInput κ).rawBid r b ≤
          (derivedKappaInput κ).rawBid r a := by
  intro r a ha b hb _halive
  fin_cases r <;> fin_cases a <;> fin_cases b <;>
    simp [derivedKappaInput, printedEligible, derivedKappaRawBid,
      derivedKappaOnlineExecution, derivedKappaOnlineAllocation] at ha hb ⊢
  all_goals first
    | exact hκ.le
    | nlinarith [derivedKappa_phaseOne_middle_allocation_pos hκ,
        derivedKappaT_pos hκ, derivedKappaU_pos hκ,
        derivedKappaU_lt_one hκ, derivedKappaX_pos hκ]

private theorem derivedKappa_least_spend_tie {κ : ℝ} (hκ : 1 < κ) :
    ∀ r a, 0 < (derivedKappaOnlineExecution κ).allocation r a →
      ∀ b, (derivedKappaInput κ).eligible r b →
        (derivedKappaOnlineExecution κ).spentBefore r b <
          (derivedKappaInput κ).budget b →
        (derivedKappaInput κ).rawBid r b =
          (derivedKappaInput κ).rawBid r a →
        (derivedKappaOnlineExecution κ).spentBefore r a ≤
          (derivedKappaOnlineExecution κ).spentBefore r b := by
  intro r a ha b hb _halive htie
  fin_cases r <;> fin_cases a <;> fin_cases b <;>
    simp [FluidAllocation.spentBefore, derivedKappaInput, printedEligible,
      derivedKappaRawBid, derivedKappaOnlineExecution,
      derivedKappaOnlineAllocation, Fin.sum_univ_three] at ha hb htie ⊢
  all_goals first
    | nlinarith [hκ]
    | nlinarith [derivedKappa_phaseOne_middle_allocation_pos hκ,
        derivedKappaT_pos hκ, derivedKappaU_pos hκ,
        derivedKappaU_lt_one hκ, derivedKappaX_pos hκ]

/--
Aggregate three-cohort accounting diagnostic for the derived `κ > 1`
family.  The source-rule bridge uses the generic continuous flow below.
-/
noncomputable def derivedKappaCertificate (κ : ℝ) (hκ : 1 < κ) :
    FluidCounterexampleCertificate (derivedKappaInput κ) where
  execution := derivedKappaOnlineExecution κ
  feasible := derivedKappa_online_feasible hκ
  raw_bid_maximal := derivedKappa_raw_bid_maximal hκ
  least_spend_tie := derivedKappa_least_spend_tie hκ
  offline := derivedKappaOfflineExecution κ
  offline_feasible := derivedKappa_offline_feasible hκ
  offline_optimal := derivedKappa_offline_optimal hκ

/-- Phase-2 starts from the allocation-derived phase-1 tail state. -/
theorem derivedKappa_tail_spentBefore_phaseTwo {κ : ℝ} (hκ : 1 < κ) :
    (derivedKappaOnlineExecution κ).spentBefore (1 : Fin 3) (2 : Fin 3) =
      derivedKappaT κ * (1 - derivedKappaU κ) := by
  simp [FluidAllocation.spentBefore, derivedKappaOnlineExecution,
    derivedKappaOnlineAllocation, derivedKappaInput, derivedKappaRawBid,
    Fin.sum_univ_three]

/-- Phase-3 starts with the tail exactly exhausted by the two prior allocations. -/
theorem derivedKappa_tail_spentBefore_phaseThree {κ : ℝ} (hκ : 1 < κ) :
    (derivedKappaOnlineExecution κ).spentBefore (2 : Fin 3) (2 : Fin 3) =
      derivedKappaT κ := by
  simp [FluidAllocation.spentBefore, derivedKappaOnlineExecution,
    derivedKappaOnlineAllocation, derivedKappaInput, derivedKappaRawBid,
    Fin.sum_univ_three]
  exact derivedKappa_tail_spend_identity hκ

theorem derivedKappa_certificate_onlineValue {κ : ℝ} (hκ : 1 < κ) :
    (derivedKappaCertificate κ hκ).onlineValue = derivedKappaRatio κ := by
  simp [FluidCounterexampleCertificate.onlineValue, FluidAllocation.revenue,
    derivedKappaCertificate, derivedKappaOnlineExecution,
    derivedKappaOnlineAllocation, derivedKappaInput, derivedKappaRawBid,
    Fin.sum_univ_three]
  rw [derivedKappa_online_factor hκ]

theorem derivedKappa_certificate_offlineOptimum {κ : ℝ} (hκ : 1 < κ) :
    (derivedKappaCertificate κ hκ).offlineOptimum = 1 := by
  simp [FluidCounterexampleCertificate.offlineOptimum, FluidAllocation.revenue,
    derivedKappaCertificate, derivedKappaOfflineExecution,
    derivedKappaOfflineAllocation, derivedKappaInput, derivedKappaRawBid,
    Fin.sum_univ_three]
  linarith [derivedKappa_phase_fractions_sum hκ]

-/

/-! ### Strict factor and endpoint limits -/

private def derivedComparisonGap (u : ℝ) : ℝ :=
  Real.exp 1 * (1 - u) + (Real.exp 1 - 1) * u ^ 2 - Real.exp (1 - u)

private def derivedComparisonSlope (u : ℝ) : ℝ :=
  -Real.exp 1 + 2 * (Real.exp 1 - 1) * u + Real.exp (1 - u)

private def derivedComparisonCurvature (u : ℝ) : ℝ :=
  2 * (Real.exp 1 - 1) - Real.exp (1 - u)

private theorem derivedComparisonGap_hasDerivAt (u : ℝ) :
    HasDerivAt derivedComparisonGap (derivedComparisonSlope u) u := by
  have hlinear : HasDerivAt (fun x : ℝ => 1 - x) (-1) u :=
    by
      convert (hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_id u) using 1 <;>
        simp [Pi.sub_apply]
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (1 - x))
      (-Real.exp (1 - u)) u := by
    convert (Real.hasDerivAt_exp (1 - u)).comp u hlinear using 1 <;> ring
  have h₁ := hlinear.const_mul (Real.exp 1)
  have h₂ := ((hasDerivAt_id u).pow 2).const_mul (Real.exp 1 - 1)
  convert (h₁.add h₂).sub hexp using 1 <;>
    simp [derivedComparisonGap, derivedComparisonSlope] <;> ring

private theorem derivedComparisonSlope_hasDerivAt (u : ℝ) :
    HasDerivAt derivedComparisonSlope (derivedComparisonCurvature u) u := by
  have hlinear : HasDerivAt (fun x : ℝ => 1 - x) (-1) u :=
    by
      convert (hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_id u) using 1 <;>
        simp [Pi.sub_apply]
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (1 - x))
      (-Real.exp (1 - u)) u := by
    convert (Real.hasDerivAt_exp (1 - u)).comp u hlinear using 1 <;> ring
  have hconst : HasDerivAt (fun _x : ℝ => -Real.exp 1) 0 u :=
    hasDerivAt_const u _
  have hlin := (hasDerivAt_id u).const_mul (2 * (Real.exp 1 - 1))
  convert (hconst.add hlin).add hexp using 1 <;>
    simp [derivedComparisonSlope, derivedComparisonCurvature] <;> ring

private theorem derivedComparisonSlope_strictMonoOn :
    StrictMonoOn derivedComparisonSlope (Set.Icc (0 : ℝ) 1) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc (0 : ℝ) 1)
  · intro u _hu
    exact (derivedComparisonSlope_hasDerivAt u).continuousAt.continuousWithinAt
  · intro u _hu
    exact (derivedComparisonSlope_hasDerivAt u).hasDerivWithinAt
  · intro u hu
    rw [interior_Icc] at hu
    have hexp_lt : Real.exp (1 - u) < Real.exp 1 :=
      (Real.exp_lt_exp).mpr (by linarith [hu.1])
    have he := Real.exp_one_gt_two
    simp only [derivedComparisonCurvature]
    linarith

private theorem derivedComparisonSlope_pos {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    0 < derivedComparisonSlope u := by
  have h := derivedComparisonSlope_strictMonoOn
    (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num)
    (show u ∈ Set.Icc 0 1 by exact ⟨hu0.le, hu1.le⟩) hu0
  simpa [derivedComparisonSlope] using h

private theorem derivedComparisonGap_strictMonoOn :
    StrictMonoOn derivedComparisonGap (Set.Icc (0 : ℝ) 1) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc (0 : ℝ) 1)
  · intro u _hu
    exact (derivedComparisonGap_hasDerivAt u).continuousAt.continuousWithinAt
  · intro u _hu
    exact (derivedComparisonGap_hasDerivAt u).hasDerivWithinAt
  · intro u hu
    rw [interior_Icc] at hu
    exact derivedComparisonSlope_pos hu.1 hu.2

private theorem derivedComparisonGap_pos {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    0 < derivedComparisonGap u := by
  have h := derivedComparisonGap_strictMonoOn
    (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num)
    (show u ∈ Set.Icc 0 1 by exact ⟨hu0.le, hu1.le⟩) hu0
  simpa [derivedComparisonGap] using h

/-- Every finite member of the derived family is strictly below `1 - 1/e`. -/
theorem derivedKappaRatio_lt_msvvRatio {κ : ℝ} (hκ : 1 < κ) :
    derivedKappaRatio κ < 1 - 1 / Real.exp 1 := by
  let u := derivedKappaU κ
  let z := derivedKappaZ κ
  have hu0 : 0 < u := derivedKappaU_pos hκ
  have hu1 : u < 1 := derivedKappaU_lt_one hκ
  have hgap := derivedComparisonGap_pos hu0 hu1
  have hden : 0 < z + u ^ 2 := by
    exact add_pos (Real.exp_pos _) (sq_pos_of_pos hu0)
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hratio : (z - 1 + u) / (z + u ^ 2) <
      (Real.exp 1 - 1) / Real.exp 1 := by
    rw [div_lt_div_iff₀ hden he]
    change 0 < Real.exp 1 * (1 - u) +
      (Real.exp 1 - 1) * u ^ 2 - z at hgap
    nlinarith
  rw [show 1 - 1 / Real.exp 1 =
      (Real.exp 1 - 1) / Real.exp 1 by field_simp]
  simpa [derivedKappaRatio, derivedKappaDenominator, derivedKappaY, u, z]
    using hratio

/-- The derived ratio approaches one half as `κ` approaches one from above. -/
theorem derivedKappaRatio_tendsto_one_right :
    Tendsto derivedKappaRatio (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (𝓝 (1 / 2 : ℝ)) := by
  have hu : ContinuousAt (fun κ : ℝ => κ⁻¹) 1 :=
    continuousAt_id.inv₀ one_ne_zero
  have hz : ContinuousAt (fun κ : ℝ => Real.exp (1 - κ⁻¹)) 1 :=
    Real.continuous_exp.continuousAt.comp (continuousAt_const.sub hu)
  have hy : ContinuousAt (fun κ : ℝ => κ⁻¹ ^ 2) 1 := hu.pow 2
  have hden : ContinuousAt (fun κ : ℝ => Real.exp (1 - κ⁻¹) + κ⁻¹ ^ 2) 1 :=
    hz.add hy
  have hnum : ContinuousAt
      (fun κ : ℝ => Real.exp (1 - κ⁻¹) - 1 + κ⁻¹) 1 :=
    (hz.sub continuousAt_const).add hu
  have hcont : ContinuousAt derivedKappaRatio 1 := by
    unfold derivedKappaRatio derivedKappaDenominator derivedKappaZ
      derivedKappaY derivedKappaU
    exact hnum.div hden (by norm_num)
  have ht := hcont.tendsto.mono_left
    (show nhdsWithin (1 : ℝ) (Set.Ioi 1) ≤ 𝓝 1 from inf_le_left)
  convert ht using 1 <;>
    norm_num [derivedKappaRatio, derivedKappaZ, derivedKappaU,
      derivedKappaDenominator, derivedKappaY]

/-- The derived ratio approaches `1 - 1/e` as `κ → ∞`. -/
theorem derivedKappaRatio_tendsto_atTop :
    Tendsto derivedKappaRatio atTop (𝓝 (1 - 1 / Real.exp 1)) := by
  have hu : Tendsto (fun κ : ℝ => κ⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have harg : Tendsto (fun κ : ℝ => 1 - κ⁻¹) atTop (𝓝 1) := by
    convert ((tendsto_const_nhds :
      Tendsto (fun _κ : ℝ => (1 : ℝ)) atTop (𝓝 1)).sub hu) using 1 <;>
      ring
  have hz : Tendsto (fun κ : ℝ => Real.exp (1 - κ⁻¹)) atTop
      (𝓝 (Real.exp 1)) :=
    (Real.continuous_exp.tendsto 1).comp harg
  have hy : Tendsto (fun κ : ℝ => κ⁻¹ ^ 2) atTop (𝓝 0) := by
    simpa using hu.pow 2
  have hden : Tendsto
      (fun κ : ℝ => Real.exp (1 - κ⁻¹) + κ⁻¹ ^ 2) atTop
      (𝓝 (Real.exp 1 + 0)) := hz.add hy
  have hnum : Tendsto
      (fun κ : ℝ => Real.exp (1 - κ⁻¹) - 1 + κ⁻¹) atTop
      (𝓝 (Real.exp 1 - 1 + 0)) :=
    (hz.sub (tendsto_const_nhds :
      Tendsto (fun _κ : ℝ => (1 : ℝ)) atTop (𝓝 1))).add hu
  have hratio := hnum.div hden (by positivity : Real.exp 1 + 0 ≠ 0)
  have hvalue : (Real.exp 1 - 1 + 0) / (Real.exp 1 + 0) =
      1 - 1 / Real.exp 1 := by
    have hexp : Real.exp 1 ≠ 0 := ne_of_gt (Real.exp_pos 1)
    field_simp [hexp]
    ring
  rw [← hvalue]
  change Tendsto
    (fun κ : ℝ =>
      (Real.exp (1 - κ⁻¹) - 1 + κ⁻¹) /
        (Real.exp (1 - κ⁻¹) + κ⁻¹ ^ 2)) atTop
    (𝓝 ((Real.exp 1 - 1 + 0) / (Real.exp 1 + 0)))
  exact hratio

/-- At `κ=1` the derived parameterization itself evaluates to one half. -/
theorem derivedKappaRatio_at_one : derivedKappaRatio 1 = 1 / 2 := by
  norm_num [derivedKappaRatio, derivedKappaZ, derivedKappaU,
    derivedKappaDenominator, derivedKappaY]

/--
The `κ=1` algorithm is the equal-bid BALANCE model with factor `1-1/e`; it is
not the value of the derived family's right-hand limiting bad instances.
-/
theorem derivedKappa_right_limit_ne_balance_factor :
    (1 / 2 : ℝ) ≠ 1 - 1 / Real.exp 1 := by
  have he := Real.exp_one_gt_two
  have hinv : 1 / Real.exp 1 < 1 / 2 := by
    rw [div_lt_div_iff₀ (Real.exp_pos 1) (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  linarith

end
end MSVV07Appendix
end Online
end AppliedModelingLib

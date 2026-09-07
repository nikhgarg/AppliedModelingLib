import AppliedModelingLib.MechanismDesign.Auctions.Combinatorial
import Mathlib.Tactic.FinCases

/-!
# Greedy allocation: the negative results of LOS02 Sections 8 and 12

Good `0` is a and good `1` is b. The three bid positions request a, ab, and b,
respectively. Section 8 assigns these positions to Red, Green, and Blue;
Section 12 assigns the last two positions to Green and takes their union.
Both constructions use the average-per-good sort and the library's greedy
acceptance runner. Clarke payments are the other bidders' declared welfare
under the zero-report rerun minus their welfare under the original run.
-/

namespace LOS02CombinatorialAuctions
namespace NegativeResults

open AppliedModelingLib.Auction
open scoped BigOperators

/-- The source's three requested bundles a, ab, and b. -/
def requestedBundle : Fin 3 → Finset (Fin 2) := ![{0}, {0, 1}, {1}]

/-- Primitive bids for the two-good examples, before sorting or allocation. -/
def threeBids (red both blue : ℝ) : Fin 3 → SingleMindedBid (Fin 2) :=
  fun i => ⟨requestedBundle i, (![red, both, blue] : Fin 3 → ℝ) i⟩

/-- Actual greedy acceptance after sorting the submitted bids by average value. -/
noncomputable def greedyAccepted (bids : Fin 3 → SingleMindedBid (Fin 2)) : Finset (Fin 3) :=
  singleMindedGreedyAcceptedFromOrder bids (singleMindedAverageOrderOf bids)

/-- The allocation induced by the actual sorted greedy run. -/
noncomputable def greedyAllocation (bids : Fin 3 → SingleMindedBid (Fin 2)) :
    BundleAllocation (Fin 3) (Fin 2) :=
  singleMindedAllocation bids (greedyAccepted bids)

private theorem averageOrder_eq (bids : Fin 3 → SingleMindedBid (Fin 2))
    (order : List (Fin 3)) (hn : order.Nodup)
    (hm : order.toFinset = Finset.univ)
    (hs : order.Pairwise (singleMindedAverageTieRel bids)) :
    singleMindedAverageOrderOf bids = order := by
  unfold singleMindedAverageOrderOf
  rw [← hm]
  exact (List.toFinset_sort (singleMindedAverageTieRel bids) hn).mpr hs

/-- With density strictly decreasing a, ab, b, this is the actual sort result. -/
theorem threeBids_order_red_both_blue (red both blue : ℝ)
    (hrg : both / 2 < red) (hgb : blue < both / 2) :
    singleMindedAverageOrderOf (threeBids red both blue) = [0, 1, 2] := by
  apply averageOrder_eq
  · decide
  · decide
  · simp only [List.pairwise_cons, List.Pairwise.nil, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, false_implies,
      implies_true, and_true]
    constructor
    · constructor
      · apply singleMindedAverageTieRel_of_average_lt
        simpa [threeBids, requestedBundle, SingleMindedBid.averageAmountPerGood,
          SingleMindedBid.bundleSize] using hrg
      · apply singleMindedAverageTieRel_of_average_lt
        simpa [threeBids, requestedBundle, SingleMindedBid.averageAmountPerGood,
          SingleMindedBid.bundleSize] using hgb.trans hrg
    · apply singleMindedAverageTieRel_of_average_lt
      simpa [threeBids, requestedBundle, SingleMindedBid.averageAmountPerGood,
        SingleMindedBid.bundleSize] using hgb

/-- With density strictly decreasing ab, b, a, this is the actual sort result. -/
theorem threeBids_order_both_blue_red (red both blue : ℝ)
    (hgb : blue < both / 2) (hbr : red < blue) :
    singleMindedAverageOrderOf (threeBids red both blue) = [1, 2, 0] := by
  apply averageOrder_eq
  · decide
  · decide
  · simp only [List.pairwise_cons, List.Pairwise.nil, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, false_implies,
      implies_true, and_true]
    constructor
    · constructor
      · apply singleMindedAverageTieRel_of_average_lt
        simpa [threeBids, requestedBundle, SingleMindedBid.averageAmountPerGood,
          SingleMindedBid.bundleSize] using hgb
      · apply singleMindedAverageTieRel_of_average_lt
        simpa [threeBids, requestedBundle, SingleMindedBid.averageAmountPerGood,
          SingleMindedBid.bundleSize] using hbr.trans hgb
    · apply singleMindedAverageTieRel_of_average_lt
      simpa [threeBids, requestedBundle, SingleMindedBid.averageAmountPerGood,
        SingleMindedBid.bundleSize] using hbr

private theorem threeBids_run_red_both_blue (red both blue : ℝ) :
    singleMindedGreedyAcceptedFromOrder (threeBids red both blue) [0, 1, 2] = {0, 2} := by
  change singleMindedGreedyAcceptedFromOrder (threeBids 0 0 0) [0, 1, 2] = {0, 2}
  decide

private theorem threeBids_run_both_blue_red (red both blue : ℝ) :
    singleMindedGreedyAcceptedFromOrder (threeBids red both blue) [1, 2, 0] = {1} := by
  change singleMindedGreedyAcceptedFromOrder (threeBids 0 0 0) [1, 2, 0] = {1}
  decide

/-- Section 8's truthful bids cause Red and Blue to win. -/
theorem section8_truthful_accepted : greedyAccepted (threeBids 10 19 8) = {0, 2} := by
  unfold greedyAccepted
  rw [threeBids_order_red_both_blue 10 19 8 (by norm_num) (by norm_num)]
  exact threeBids_run_red_both_blue 10 19 8

/-- Zeroing Red's bid reruns the algorithm and awards both goods to Green. -/
theorem section8_zero_accepted : greedyAccepted (threeBids 0 19 8) = {1} := by
  unfold greedyAccepted
  rw [threeBids_order_both_blue_red 0 19 8 (by norm_num) (by norm_num)]
  exact threeBids_run_both_blue_red 0 19 8

/-- Greedy allocation paired with Clarke's payment formula, for single-minded reports. -/
noncomputable def greedyClarke : SingleMindedAcceptedMechanism (Fin 3) (Fin 2) where
  accepted := greedyAccepted
  payment bids i :=
    allocationValueExcept (singleMindedValuationProfile bids)
        (greedyAllocation (singleMindedValueUpdate bids i 0)) i -
      allocationValueExcept (singleMindedValuationProfile bids) (greedyAllocation bids) i

private theorem threeBids_zero_red (red both blue : ℝ) :
    singleMindedValueUpdate (threeBids red both blue) 0 0 = threeBids 0 both blue := by
  funext i
  fin_cases i <;> simp [singleMindedValueUpdate, threeBids, requestedBundle]

/-- Example 8.1: Red pays 11 truthfully, and pays zero after reporting zero. -/
theorem section8_clarke_payments :
    greedyClarke.payment (threeBids 10 19 8) 0 = 11 ∧
      greedyClarke.payment (threeBids 0 19 8) 0 = 0 := by
  simp only [greedyClarke, threeBids_zero_red, greedyAllocation,
    section8_truthful_accepted, section8_zero_accepted]
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  norm_num [allocationValueExcept, Fin.sum_univ_succ, singleMindedValuationProfile,
    singleMindedAllocation, threeBids, requestedBundle, SingleMindedBid.valuation, h12, h21]

/-- Example 8.1: truth gives utility -1; a zero report gives utility zero. -/
theorem section8_clarke_utilities :
    greedyClarke.utility (threeBids 10 19 8) (threeBids 10 19 8) 0 = -1 ∧
      greedyClarke.utility (threeBids 10 19 8) (threeBids 0 19 8) 0 = 0 := by
  simp only [SingleMindedAcceptedMechanism.utility, SingleMindedAcceptedMechanism.allocation,
    section8_clarke_payments.1, section8_clarke_payments.2]
  change
    (threeBids 10 19 8 0).valuation
        (singleMindedAllocation (threeBids 10 19 8) (greedyAccepted (threeBids 10 19 8)) 0) - 11 = -1 ∧
    (threeBids 10 19 8 0).valuation
        (singleMindedAllocation (threeBids 0 19 8) (greedyAccepted (threeBids 0 19 8)) 0) - 0 = 0
  rw [section8_truthful_accepted, section8_zero_accepted]
  norm_num [singleMindedAllocation, threeBids, requestedBundle, SingleMindedBid.valuation]

/-- The exact two-run Section 8 witness in Example 8.1.  This is the
source-facing counterexample interface; `greedyClarke` above is only its
implementation. -/
def section8Witness : Prop :=
  greedyClarke.utility (threeBids 10 19 8) (threeBids 10 19 8) 0 = -1 ∧
    greedyClarke.utility (threeBids 10 19 8) (threeBids 0 19 8) 0 = 0

theorem section8_witness : section8Witness := section8_clarke_utilities

/-- Section 8: greedy allocation with Clarke payments is not truthful even
on the nonnegative, nonempty single-minded domain. -/
theorem section8_clarke_not_truthful :
    ¬ greedyClarke.TruthfulOn SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile := by
  intro h
  have ht : SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile (threeBids 10 19 8) := by
    intro i
    fin_cases i <;> norm_num [threeBids, requestedBundle]
  have hz : SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile (threeBids 0 19 8) := by
    intro i
    fin_cases i <;> norm_num [threeBids, requestedBundle]
  have hu := h (threeBids 10 19 8) ht 0 ⟨{0}, 0⟩
  have he : Function.update (threeBids 10 19 8) 0 ⟨{0}, 0⟩ = threeBids 0 19 8 :=
    threeBids_zero_red 10 19 8
  rw [he] at hu
  have hi := hu hz
  rw [section8_clarke_utilities.1, section8_clarke_utilities.2] at hi
  norm_num at hi

/-- Green's private type or report: value for ab, and value for b without a. -/
structure GreenType where
  both : ℝ
  bOnly : ℝ

/-- Section 12's legal true values: nonnegative values and strictly more value
for `ab` than for `b`. -/
def GreenType.TrueAdmissible (v : GreenType) : Prop :=
  0 ≤ v.bOnly ∧ v.bOnly < v.both

/-- Section 12's legal reports: nonnegative coordinates and the stated
`0 ≤ g_b < 10` restriction. -/
def GreenType.ReportAdmissible (v : GreenType) : Prop :=
  0 ≤ v.both ∧ 0 ≤ v.bOnly ∧ v.bOnly < 10

/-- Green values bundles without b at zero, b alone at `bOnly`, and ab at `both`. -/
noncomputable def GreenType.valuation (v : GreenType) (S : Finset (Fin 2)) : ℝ :=
  if 1 ∈ S then if 0 ∈ S then v.both else v.bOnly else 0

/-- Red bids 10 for a; Green submits the ab and b bids and receives the union
of the bundles won by these two bid agents, as in Sections 11 and 12. -/
noncomputable def greenAllocation (report : GreenType) : Finset (Fin 2) :=
  greedyAllocation (threeBids 10 report.both report.bOnly) 1 ∪
    greedyAllocation (threeBids 10 report.both report.bOnly) 2

/-- Report-based payments on the fixed-Red slice have no access to Green's true type. -/
def GreenTruthfulPayment (payment : GreenType → ℝ) : Prop :=
  ∀ (values : GreenType), values.TrueAdmissible →
    ∀ (report : GreenType), report.ReportAdmissible →
      values.valuation (greenAllocation report) - payment report ≤
        values.valuation (greenAllocation values) - payment values

/-- The high report in the finite incentive cycle: ab is worth 21 and b is worth 9. -/
def greenHigh : GreenType := ⟨21, 9⟩

/-- The low report in the finite incentive cycle: ab is worth 19 and b is worth zero. -/
def greenLow : GreenType := ⟨19, 0⟩

theorem greenHigh_true_admissible : greenHigh.TrueAdmissible := by
  norm_num [GreenType.TrueAdmissible, greenHigh]

theorem greenLow_true_admissible : greenLow.TrueAdmissible := by
  norm_num [GreenType.TrueAdmissible, greenLow]

theorem greenHigh_report_admissible : greenHigh.ReportAdmissible := by
  norm_num [GreenType.ReportAdmissible, greenHigh]

theorem greenLow_report_admissible : greenLow.ReportAdmissible := by
  norm_num [GreenType.ReportAdmissible, greenLow]

/-- The high report puts Green's ab bid first, ahead of Red and Green's b bid. -/
theorem section12_high_order :
    singleMindedAverageOrderOf (threeBids 10 greenHigh.both greenHigh.bOnly) = [1, 0, 2] := by
  apply averageOrder_eq
  · decide
  · decide
  · simp only [List.pairwise_cons, List.Pairwise.nil, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, false_implies,
      implies_true, and_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> apply singleMindedAverageTieRel_of_average_lt <;>
      norm_num [threeBids, requestedBundle, greenHigh, SingleMindedBid.averageAmountPerGood,
        SingleMindedBid.bundleSize]
    all_goals norm_num [Matrix.cons_val_two]

/-- Running the high report grants only Green's ab bid. -/
theorem section12_high_accepted :
    greedyAccepted (threeBids 10 greenHigh.both greenHigh.bOnly) = {1} := by
  unfold greedyAccepted
  rw [section12_high_order]
  change singleMindedGreedyAcceptedFromOrder (threeBids 0 0 0) [1, 0, 2] = {1}
  decide

/-- The low report grants a to Red and b to Green. -/
theorem section12_low_accepted :
    greedyAccepted (threeBids 10 greenLow.both greenLow.bOnly) = {0, 2} := by
  unfold greedyAccepted
  rw [threeBids_order_red_both_blue 10 greenLow.both greenLow.bOnly
    (by norm_num [greenLow]) (by norm_num [greenLow])]
  exact threeBids_run_red_both_blue 10 greenLow.both greenLow.bOnly

/-- The source allocation outcomes used in the two-direction incentive comparison
are derived from the primitive submitted bids and the actual greedy runner. -/
theorem section12_green_allocations :
    greenAllocation greenHigh = {0, 1} ∧ greenAllocation greenLow = {1} := by
  unfold greenAllocation greedyAllocation
  rw [section12_high_accepted, section12_low_accepted]
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  norm_num [singleMindedAllocation, threeBids, requestedBundle, h12, h21]
  rfl

/-- The two true types evaluate both possible greedy outputs; their incremental
values for a are 12 and 19, in the opposite order from their allocations. -/
theorem section12_cross_values :
    greenHigh.valuation (greenAllocation greenHigh) = 21 ∧
      greenHigh.valuation (greenAllocation greenLow) = 9 ∧
      greenLow.valuation (greenAllocation greenLow) = 0 ∧
      greenLow.valuation (greenAllocation greenHigh) = 19 := by
  rw [section12_green_allocations.1, section12_green_allocations.2]
  norm_num [GreenType.valuation, greenHigh, greenLow]

/-- Section 12: no report-based payment makes the actual greedy allocation
truthful for Green, even with Red's report fixed at 10 for a. Truthfulness
would require the high-versus-low payment difference to be both at most 12
and at least 19. No restriction on the signs of payments is needed. -/
theorem section12_no_truthful_payment : ¬ ∃ payment : GreenType → ℝ,
    GreenTruthfulPayment payment := by
  rintro ⟨payment, h⟩
  have hh := h greenHigh greenHigh_true_admissible greenLow greenLow_report_admissible
  have hl := h greenLow greenLow_true_admissible greenHigh greenHigh_report_admissible
  rw [section12_cross_values.1, section12_cross_values.2.1] at hh
  rw [section12_cross_values.2.2.1, section12_cross_values.2.2.2] at hl
  linarith

end NegativeResults
end LOS02CombinatorialAuctions

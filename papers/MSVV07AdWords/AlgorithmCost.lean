import MSVV07AdWords.AuditInterface
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# MSVV07 finite-max support and Appendix arithmetic checks

This module closes two source-audit obligations that are easy to state precisely
without changing the mathematical AdWords model.

* Lean already proves existence of a Balance maximizer over the finite
  advertiser set.  The ledger below records the candidate-test and comparison
  counts that a direct scan would target in a unit-cost oracle model.  It is not
  derived from a cost-threaded runner, so it is supporting mathematics rather
  than a proof of the paper's qualitative time-efficiency claim.  Evaluation of
  real arithmetic and comparison is also deliberately treated as an oracle
  operation; no bit-complexity theorem is claimed.
* The Appendix's printed three-phase counts imply revenue `3N/5`, not the
  displayed `0.62N = 31N/50`.  These lemmas check only that arithmetic.  They do
  not claim to formalize the full adversarial construction or its `kappa > 1`
  family.
-/

namespace AppliedModelingLib
namespace Online
namespace MSVV07PaperFacing

/-- Unit-cost ledger for a direct finite-max scan of all advertisers. -/
structure BalanceFiniteMaxCost where
  candidateTests : ℕ
  scoreComparisonUpperBound : ℕ

/--
One pass over a finite advertiser type tests every advertiser once and needs at
most one scaled-bid comparison per advertiser.
-/
def balanceFiniteMaxCost (Advertiser : Type*) [Fintype Advertiser] :
    BalanceFiniteMaxCost :=
  { candidateTests := Fintype.card Advertiser
    scoreComparisonUpperBound := Fintype.card Advertiser }

/--
Finite-max support for auditing the paper's claim that Balance is simple and
time efficient. Whenever a feasible advertiser exists, a maximizer exists, and
the accompanying target ledger declares `card Advertiser` feasibility tests
and at most that many score comparisons. The theorem does not connect those
counts to an executed scan and therefore does not close the runtime claim.
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
  obtain ⟨a, ha⟩ := Proof.section3_balance_choice_exists I A q h
  refine ⟨a, ha, rfl, ?_⟩
  simp [balanceFiniteMaxCost]

/-! ## Theorem 8 finite-index arithmetic -/

/--
If a type-`i` bidder has spent fraction `i / k`, its unspent fraction is
`(k - i) / k` in real arithmetic.  This is the coefficient used by the
corrected finite-index reading of Theorem 8's simple proof.
-/
theorem theorem8_corrected_unspent_fraction_formula
    (k i : ℕ) (hk : 0 < k) :
    1 - (i : ℝ) / (k : ℝ) =
      ((k : ℝ) - (i : ℝ)) / (k : ℝ) := by
  have hk0 : (k : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hk
  field_simp [hk0]

/--
At `k = 2`, a type-`1` bidder has unspent fraction `1/2`, not the printed
`(k-i+1)/k = 1`.  This is the same finite-index shift as the printed
Theorem 8 suffix exponent.
-/
theorem theorem8_unspent_fraction_ne_printed_at_k2 :
    1 - (1 : ℝ) / 2 = (1 / 2 : ℝ) ∧
      1 - (1 : ℝ) / 2 ≠ ((2 : ℝ) - 1 + 1) / 2 := by
  norm_num

/-! ## Appendix phase-count arithmetic -/

/-- Revenue cap contributed by the Appendix's first `0.4N` phases. -/
noncomputable def appendixHighestBidPhaseOneRevenue (N : ℝ) : ℝ :=
  (2 / 5 : ℝ) * N

/-- Revenue cap contributed by the Appendix's next `0.1N` phases at bid `2a`. -/
noncomputable def appendixHighestBidPhaseTwoRevenue (N : ℝ) : ℝ :=
  (1 / 5 : ℝ) * N

/-- The Appendix says all phase-three queries are discarded. -/
def appendixHighestBidPhaseThreeRevenue (_N : ℝ) : ℝ := 0

/-- The three printed phase contributions sum to `3N/5`. -/
theorem appendix_highest_bid_phase_total_eq_three_fifths (N : ℝ) :
    appendixHighestBidPhaseOneRevenue N +
        appendixHighestBidPhaseTwoRevenue N +
        appendixHighestBidPhaseThreeRevenue N =
      (3 / 5 : ℝ) * N := by
  simp [appendixHighestBidPhaseOneRevenue,
    appendixHighestBidPhaseTwoRevenue,
    appendixHighestBidPhaseThreeRevenue]
  ring

/--
For positive `N`, the phase total forced by the printed construction is not the
Appendix's displayed `0.62N = 31N/50` value.
-/
theorem appendix_highest_bid_phase_total_ne_printed_062
    {N : ℝ} (hN : 0 < N) :
    appendixHighestBidPhaseOneRevenue N +
        appendixHighestBidPhaseTwoRevenue N +
        appendixHighestBidPhaseThreeRevenue N ≠
      (31 / 50 : ℝ) * N := by
  rw [appendix_highest_bid_phase_total_eq_three_fifths]
  intro h
  norm_num at h
  nlinarith

/-- The corrected three-fifths factor is still strictly below `1 - 1/e`. -/
theorem appendix_three_fifths_lt_msvv_ratio :
    (3 / 5 : ℝ) < paperMsvvRatio := by
  have hexp : (5 / 2 : ℝ) < Real.exp 1 :=
    lt_trans (by norm_num) Real.exp_one_gt_d9
  have hexp_pos : 0 < Real.exp 1 := Real.exp_pos 1
  have hinv : 1 / Real.exp 1 < (2 / 5 : ℝ) := by
    rw [div_lt_iff₀ hexp_pos]
    nlinarith
  unfold paperMsvvRatio
  linarith

end MSVV07PaperFacing
end Online
end AppliedModelingLib

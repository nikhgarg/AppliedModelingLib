import AppliedModelingLib.Queueing.MM1.Stationary
import Mathlib.Tactic

/-!
# Finite-capacity birth--death queues

This module supplies the stationary generator law for a single-server
birth--death queue whose arrivals are blocked at a finite capacity.  The
normalization is written as a finite geometric sum, so it is valid at traffic
intensity one as well as away from that boundary.
-/

namespace AppliedModelingLib
namespace Probability
namespace Queueing

/-- A reflected single-server birth--death process with arrivals blocked at
`capacity`. -/
def finiteCapacityBirthDeathRates
    (arrivalRate serviceRate : ℝ) (capacity : ℕ) : BirthDeathRates where
  birth := fun n => if n < capacity then arrivalRate else 0
  death := fun n => if n = 0 then 0 else serviceRate
  death_zero := by simp

/-- The finite geometric normalization constant on queue lengths from zero
through `capacity`. -/
def finiteCapacityGeometricNormalizer (rho : ℝ) (capacity : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (capacity + 1), rho ^ i

/-- The finite-capacity geometric stationary mass, extended by zero outside
the reachable state space. -/
noncomputable def finiteCapacityGeometricMass (rho : ℝ) (capacity n : ℕ) : ℝ :=
  if n ≤ capacity then
    rho ^ n / finiteCapacityGeometricNormalizer rho capacity
  else 0

/-- The numerator of the finite-capacity stationary mean queue length. -/
def finiteCapacityWeightedGeometricSum (rho : ℝ) (capacity : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (capacity + 1), (n : ℝ) * rho ^ n

/-- Mean queue length under the finite-capacity geometric state law. -/
noncomputable def finiteCapacityExpectedState (rho : ℝ) (capacity : ℕ) : ℝ :=
  finiteCapacityWeightedGeometricSum rho capacity /
    finiteCapacityGeometricNormalizer rho capacity

/-- The probability generating polynomial of the finite-capacity geometric
stationary law. -/
noncomputable def finiteCapacityGeometricProbabilityGeneratingFunction
    (rho z : ℝ) (capacity : ℕ) : ℝ :=
  ∑ state ∈ Finset.range (capacity + 1),
    finiteCapacityGeometricMass rho capacity state * z ^ state

/-- The cumulative delay exposure of admitting one additional customer at a
finite capacity. -/
noncomputable def finiteCapacityOpportunityCost (rho : ℝ) (capacity : ℕ) : ℝ :=
  ((capacity + 1 : ℕ) : ℝ) * finiteCapacityGeometricNormalizer rho capacity -
    finiteCapacityWeightedGeometricSum rho capacity

/-- Arrival rate admitted by a finite-capacity queue in its stationary state
law. -/
noncomputable def finiteCapacityAdmittedArrivalRate
    (arrivalRate rho : ℝ) (capacity : ℕ) : ℝ :=
  arrivalRate * (1 - finiteCapacityGeometricMass rho capacity capacity)

/-- Arrival rate rejected because the finite queue is at its admission
threshold. -/
noncomputable def finiteCapacityRejectedArrivalRate
    (arrivalRate rho : ℝ) (capacity : ℕ) : ℝ :=
  arrivalRate * finiteCapacityGeometricMass rho capacity capacity

/-- Fraction of time the server is occupied under the finite-capacity
stationary law. -/
noncomputable def finiteCapacityBusyFraction (rho : ℝ) (capacity : ℕ) : ℝ :=
  1 - finiteCapacityGeometricMass rho capacity 0

/-- A linear steady-state reward-minus-holding-cost objective for a
finite-capacity queue. -/
noncomputable def finiteCapacityLinearHoldingReward
    (arrivalRate completionReward holdingCost rho : ℝ) (capacity : ℕ) : ℝ :=
  completionReward * finiteCapacityAdmittedArrivalRate arrivalRate rho capacity -
    holdingCost * finiteCapacityExpectedState rho capacity

/-- Revenue from charging a common fee to each admitted arrival. -/
noncomputable def finiteCapacityAdmissionRevenue
    (arrivalRate admissionFee rho : ℝ) (capacity : ℕ) : ℝ :=
  admissionFee * finiteCapacityAdmittedArrivalRate arrivalRate rho capacity

/-- Customer welfare after a common admission fee is charged and retained by a
separate revenue collector. -/
noncomputable def finiteCapacityCustomerNetIncomeAfterFee
    (arrivalRate completionReward holdingCost admissionFee rho : ℝ) (capacity : ℕ) : ℝ :=
  finiteCapacityLinearHoldingReward arrivalRate completionReward holdingCost rho capacity -
    finiteCapacityAdmissionRevenue arrivalRate admissionFee rho capacity

/-- Total income when an admission fee is transferred from admitted customers
to a revenue collector. -/
noncomputable def finiteCapacityCombinedIncomeAfterFee
    (arrivalRate completionReward holdingCost admissionFee rho : ℝ) (capacity : ℕ) : ℝ :=
  finiteCapacityCustomerNetIncomeAfterFee arrivalRate completionReward holdingCost admissionFee
      rho capacity +
    finiteCapacityAdmissionRevenue arrivalRate admissionFee rho capacity

/-- A pure transfer fee does not change the combined steady-state income of
customers and the revenue collector. -/
theorem finiteCapacityCombinedIncomeAfterFee_eq_linearHoldingReward
    (arrivalRate completionReward holdingCost admissionFee rho : ℝ) (capacity : ℕ) :
    finiteCapacityCombinedIncomeAfterFee arrivalRate completionReward holdingCost admissionFee
        rho capacity =
      finiteCapacityLinearHoldingReward arrivalRate completionReward holdingCost rho capacity := by
  simp only [finiteCapacityCombinedIncomeAfterFee,
    finiteCapacityCustomerNetIncomeAfterFee]
  ring

/-- Extending capacity by one adds exactly the next geometric weight to the
normalizer. -/
theorem finiteCapacityGeometricNormalizer_succ (rho : ℝ) (capacity : ℕ) :
    finiteCapacityGeometricNormalizer rho (capacity + 1) =
      finiteCapacityGeometricNormalizer rho capacity + rho ^ (capacity + 1) := by
  simp [finiteCapacityGeometricNormalizer, Finset.sum_range_succ]

/-- The weighted geometric numerator has the corresponding one-step
recurrence. -/
theorem finiteCapacityWeightedGeometricSum_succ (rho : ℝ) (capacity : ℕ) :
    finiteCapacityWeightedGeometricSum rho (capacity + 1) =
      finiteCapacityWeightedGeometricSum rho capacity +
        ((capacity + 1 : ℕ) : ℝ) * rho ^ (capacity + 1) := by
  simp [finiteCapacityWeightedGeometricSum, Finset.sum_range_succ]

/-- The delay-exposure sequence grows by the next normalizer. -/
theorem finiteCapacityOpportunityCost_succ (rho : ℝ) (capacity : ℕ) :
    finiteCapacityOpportunityCost rho (capacity + 1) =
      finiteCapacityOpportunityCost rho capacity +
        finiteCapacityGeometricNormalizer rho (capacity + 1) := by
  simp only [finiteCapacityOpportunityCost, finiteCapacityGeometricNormalizer_succ,
    finiteCapacityWeightedGeometricSum_succ]
  push_cast
  ring

theorem one_le_finiteCapacityGeometricNormalizer
    {rho : ℝ} (hrho_nonneg : 0 ≤ rho) (capacity : ℕ) :
    1 ≤ finiteCapacityGeometricNormalizer rho capacity := by
  unfold finiteCapacityGeometricNormalizer
  have hmem : 0 ∈ Finset.range (capacity + 1) := by simp
  have hterm_nonneg : ∀ i ∈ Finset.range (capacity + 1), 0 ≤ rho ^ i := by
    intro i hi
    exact pow_nonneg hrho_nonneg i
  calc
    1 = rho ^ 0 := by simp
    _ ≤ ∑ i ∈ Finset.range (capacity + 1), rho ^ i :=
      Finset.single_le_sum hterm_nonneg hmem

/-- The opportunity cost of an additional admission is at least the number of
customers already present plus that admission. -/
theorem finiteCapacityOpportunityCost_lower_bound
    {rho : ℝ} (hrho_nonneg : 0 ≤ rho) (capacity : ℕ) :
    ((capacity + 1 : ℕ) : ℝ) ≤ finiteCapacityOpportunityCost rho capacity := by
  induction capacity with
  | zero =>
      simp [finiteCapacityOpportunityCost, finiteCapacityGeometricNormalizer,
        finiteCapacityWeightedGeometricSum]
  | succ capacity ih =>
      have hnormalizer := one_le_finiteCapacityGeometricNormalizer hrho_nonneg
        (capacity + 1)
      have hcast : (((capacity + 1) + 1 : ℕ) : ℝ) =
          ((capacity + 1 : ℕ) : ℝ) + 1 := by norm_num
      rw [hcast, finiteCapacityOpportunityCost_succ]
      linarith

/-- Away from traffic intensity one, the finite normalization has the familiar
closed geometric-series form used in textbook M/M/1 calculations. -/
theorem finiteCapacityGeometricNormalizer_eq_closedForm
    {rho : ℝ} (hrho_ne_one : rho ≠ 1) (capacity : ℕ) :
    finiteCapacityGeometricNormalizer rho capacity =
      (1 - rho ^ (capacity + 1)) / (1 - rho) := by
  unfold finiteCapacityGeometricNormalizer
  have hdenom : 1 - rho ≠ 0 := sub_ne_zero.mpr (Ne.symm hrho_ne_one)
  apply (eq_div_iff hdenom).mpr
  exact geom_sum_mul_neg rho (capacity + 1)

/-- The finite geometric mass is the usual truncated-geometric formula away
from traffic intensity one. -/
theorem finiteCapacityGeometricMass_eq_closedForm
    {rho : ℝ} {capacity n : ℕ} (hn : n ≤ capacity) (hrho_ne_one : rho ≠ 1) :
    finiteCapacityGeometricMass rho capacity n =
      (1 - rho) * rho ^ n / (1 - rho ^ (capacity + 1)) := by
  rw [finiteCapacityGeometricMass, if_pos hn,
    finiteCapacityGeometricNormalizer_eq_closedForm hrho_ne_one]
  rw [div_div_eq_mul_div]
  ring

theorem finiteCapacityGeometricNormalizer_pos
    {rho : ℝ} (hrho_nonneg : 0 ≤ rho) (capacity : ℕ) :
    0 < finiteCapacityGeometricNormalizer rho capacity := by
  unfold finiteCapacityGeometricNormalizer
  have hmem : 0 ∈ Finset.range (capacity + 1) := by
    simp
  have hterm_nonneg : ∀ i ∈ Finset.range (capacity + 1), 0 ≤ rho ^ i := by
    intro i hi
    exact pow_nonneg hrho_nonneg i
  calc
    0 < rho ^ 0 := by simp
    _ ≤ ∑ i ∈ Finset.range (capacity + 1), rho ^ i :=
      Finset.single_le_sum hterm_nonneg hmem

theorem finiteCapacityGeometricMass_nonneg
    {rho : ℝ} (hrho_nonneg : 0 ≤ rho) (capacity n : ℕ) :
    0 ≤ finiteCapacityGeometricMass rho capacity n := by
  by_cases hn : n ≤ capacity
  · rw [finiteCapacityGeometricMass, if_pos hn]
    exact div_nonneg (pow_nonneg hrho_nonneg n)
      (finiteCapacityGeometricNormalizer_pos hrho_nonneg capacity).le
  · simp [finiteCapacityGeometricMass, hn]

theorem finiteCapacityGeometricMass_eq_zero_of_capacity_lt
    {rho : ℝ} {capacity n : ℕ} (hcapacity : capacity < n) :
    finiteCapacityGeometricMass rho capacity n = 0 := by
  simp [finiteCapacityGeometricMass, Nat.not_le.mpr hcapacity]

theorem finiteCapacityGeometricMass_eq_div_of_le
    {rho : ℝ} {capacity n : ℕ} (hn : n ≤ capacity) :
    finiteCapacityGeometricMass rho capacity n =
      rho ^ n / finiteCapacityGeometricNormalizer rho capacity := by
  simp [finiteCapacityGeometricMass, hn]

/-- The stationary probability generating polynomial is a ratio of finite
geometric normalizers.  Unlike a rational closed form, this identity is
defined without a special case at traffic intensity one. -/
theorem finiteCapacityGeometricProbabilityGeneratingFunction_eq_normalizer_ratio
    (rho z : ℝ) (capacity : ℕ) :
    finiteCapacityGeometricProbabilityGeneratingFunction rho z capacity =
      finiteCapacityGeometricNormalizer (rho * z) capacity /
        finiteCapacityGeometricNormalizer rho capacity := by
  unfold finiteCapacityGeometricProbabilityGeneratingFunction
  calc
    ∑ state ∈ Finset.range (capacity + 1),
        finiteCapacityGeometricMass rho capacity state * z ^ state =
      ∑ state ∈ Finset.range (capacity + 1),
        (rho * z) ^ state / finiteCapacityGeometricNormalizer rho capacity := by
      apply Finset.sum_congr rfl
      intro state hstate
      have hstate_le : state ≤ capacity := by
        simpa using (Finset.mem_range.mp hstate)
      rw [finiteCapacityGeometricMass_eq_div_of_le hstate_le, mul_pow]
      ring
    _ = (∑ state ∈ Finset.range (capacity + 1), (rho * z) ^ state) /
        finiteCapacityGeometricNormalizer rho capacity := by
      rw [Finset.sum_div]
    _ = _ := rfl

/-- Admitted and rejected arrivals partition the original arrival stream. -/
theorem finiteCapacityAdmitted_add_rejected_eq_arrivalRate
    (arrivalRate rho : ℝ) (capacity : ℕ) :
    finiteCapacityAdmittedArrivalRate arrivalRate rho capacity +
      finiteCapacityRejectedArrivalRate arrivalRate rho capacity = arrivalRate := by
  simp only [finiteCapacityAdmittedArrivalRate, finiteCapacityRejectedArrivalRate]
  ring

/-- In stationarity, the admitted arrival flow equals the service rate times
the server's busy fraction. -/
theorem finiteCapacity_admittedArrivalRate_eq_serviceRate_mul_busyFraction
    {rho serviceRate : ℝ} (hrho_nonneg : 0 ≤ rho) (capacity : ℕ) :
    finiteCapacityAdmittedArrivalRate (rho * serviceRate) rho capacity =
      serviceRate * finiteCapacityBusyFraction rho capacity := by
  have hnormalizer_ne : finiteCapacityGeometricNormalizer rho capacity ≠ 0 :=
    ne_of_gt (finiteCapacityGeometricNormalizer_pos hrho_nonneg capacity)
  have hgeometric :
      finiteCapacityGeometricNormalizer rho capacity * (1 - rho) =
        1 - rho ^ (capacity + 1) := by
    unfold finiteCapacityGeometricNormalizer
    exact geom_sum_mul_neg rho (capacity + 1)
  simp only [finiteCapacityAdmittedArrivalRate, finiteCapacityBusyFraction]
  rw [finiteCapacityGeometricMass_eq_div_of_le (le_refl capacity),
    finiteCapacityGeometricMass_eq_div_of_le (Nat.zero_le capacity)]
  rw [pow_succ] at hgeometric
  have hscaled := congrArg (fun x : ℝ => -2 * serviceRate * x) hgeometric
  field_simp [hnormalizer_ne]
  nlinarith [hscaled]

/-- For a positive finite-capacity traffic intensity and a nonzero capacity,
the ratio of the busy fraction to the admission probability recovers the
arrival-to-service ratio. -/
theorem finiteCapacity_busyFraction_div_admissionProbability_eq_rho
    {rho : ℝ} (hrho_pos : 0 < rho) (capacity : ℕ) (hcapacity_pos : 0 < capacity) :
    finiteCapacityBusyFraction rho capacity /
        (1 - finiteCapacityGeometricMass rho capacity capacity) = rho := by
  obtain ⟨predecessor, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hcapacity_pos)
  have hprev_pos : 0 < finiteCapacityGeometricNormalizer rho predecessor :=
    finiteCapacityGeometricNormalizer_pos hrho_pos.le predecessor
  have htotal_pos : 0 < finiteCapacityGeometricNormalizer rho (predecessor + 1) :=
    finiteCapacityGeometricNormalizer_pos hrho_pos.le (predecessor + 1)
  have hterminal_lt_one :
      finiteCapacityGeometricMass rho (predecessor + 1) (predecessor + 1) < 1 := by
    rw [finiteCapacityGeometricMass_eq_div_of_le (le_refl (predecessor + 1)),
      finiteCapacityGeometricNormalizer_succ]
    apply (div_lt_one₀ (add_pos hprev_pos (pow_pos hrho_pos _))).mpr
    linarith
  have hadmission_pos :
      0 < 1 - finiteCapacityGeometricMass rho (predecessor + 1) (predecessor + 1) :=
    sub_pos.mpr hterminal_lt_one
  have hflow := finiteCapacity_admittedArrivalRate_eq_serviceRate_mul_busyFraction
    (rho := rho) (serviceRate := (1 : ℝ)) hrho_pos.le (predecessor + 1)
  have hratio :
      rho * (1 - finiteCapacityGeometricMass rho (predecessor + 1) (predecessor + 1)) =
        finiteCapacityBusyFraction rho (predecessor + 1) := by
    simpa only [finiteCapacityAdmittedArrivalRate, finiteCapacityBusyFraction, one_mul,
      mul_one] using hflow
  apply (div_eq_iff (ne_of_gt hadmission_pos)).mpr
  linarith

/-- The one-step change in a linear reward-minus-holding-cost objective is
governed by the difference between service value and the cumulative delay
exposure. -/
theorem finiteCapacityLinearHoldingReward_succ_sub
    {rho completionReward holdingCost serviceRate : ℝ}
    (hrho_nonneg : 0 ≤ rho) (hholdingCost_pos : 0 < holdingCost) (capacity : ℕ) :
    finiteCapacityLinearHoldingReward (rho * serviceRate) completionReward holdingCost rho
        (capacity + 1) -
      finiteCapacityLinearHoldingReward (rho * serviceRate) completionReward holdingCost rho
        capacity =
      holdingCost * rho ^ (capacity + 1) /
          (finiteCapacityGeometricNormalizer rho capacity *
            finiteCapacityGeometricNormalizer rho (capacity + 1)) *
        (completionReward * serviceRate / holdingCost -
          finiteCapacityOpportunityCost rho capacity) := by
  have hnormalizer_ne : finiteCapacityGeometricNormalizer rho capacity ≠ 0 :=
    ne_of_gt (finiteCapacityGeometricNormalizer_pos hrho_nonneg capacity)
  have hnormalizer_succ_ne : finiteCapacityGeometricNormalizer rho (capacity + 1) ≠ 0 :=
    ne_of_gt (finiteCapacityGeometricNormalizer_pos hrho_nonneg (capacity + 1))
  have hnormalizer_succ_expanded_ne :
      finiteCapacityGeometricNormalizer rho capacity + rho ^ (capacity + 1) ≠ 0 := by
    rw [← finiteCapacityGeometricNormalizer_succ]
    exact hnormalizer_succ_ne
  have hgeometric :
      finiteCapacityGeometricNormalizer rho capacity * (1 - rho) =
        1 - rho ^ (capacity + 1) := by
    unfold finiteCapacityGeometricNormalizer
    exact geom_sum_mul_neg rho (capacity + 1)
  simp only [finiteCapacityLinearHoldingReward, finiteCapacityAdmittedArrivalRate,
    finiteCapacityExpectedState]
  rw [
    finiteCapacityGeometricMass_eq_div_of_le (le_refl (capacity + 1)),
    finiteCapacityGeometricMass_eq_div_of_le (le_refl capacity),
    finiteCapacityGeometricNormalizer_succ,
    finiteCapacityWeightedGeometricSum_succ]
  unfold finiteCapacityOpportunityCost
  field_simp [hnormalizer_ne, hnormalizer_succ_ne, hnormalizer_succ_expanded_ne,
    ne_of_gt hholdingCost_pos]
  linear_combination
    (completionReward * serviceRate * rho * rho ^ capacity) * hgeometric

/-- The finite geometric normalizer and cumulative delay exposure satisfy a
telescoping identity.  This is useful for comparing private revenue incentives
with the system-wide queueing objective. -/
theorem finiteCapacityOpportunityCost_linear_identity (rho : ℝ) (capacity : ℕ) :
    rho * finiteCapacityGeometricNormalizer rho capacity +
        (1 - rho) * finiteCapacityOpportunityCost rho capacity =
      ((capacity + 1 : ℕ) : ℝ) := by
  induction capacity with
  | zero =>
      simp [finiteCapacityGeometricNormalizer, finiteCapacityOpportunityCost,
        finiteCapacityWeightedGeometricSum]
  | succ capacity ih =>
      have hgeometric :
          finiteCapacityGeometricNormalizer rho capacity * (1 - rho) =
            1 - rho ^ (capacity + 1) := by
        unfold finiteCapacityGeometricNormalizer
        exact geom_sum_mul_neg rho (capacity + 1)
      simp only [finiteCapacityGeometricNormalizer_succ,
        finiteCapacityOpportunityCost_succ]
      push_cast
      have hcast : ((capacity + 1 : ℕ) : ℝ) = (capacity : ℝ) + 1 := by
        norm_num
      linear_combination ih + hgeometric + hcast

/-- Multiplying the cumulative delay exposure by the terminal geometric weight
does not exceed the square of the finite normalizer. -/
theorem finiteCapacity_terminal_mul_opportunityCost_le_normalizer_sq
    {rho : ℝ} (hrho_nonneg : 0 ≤ rho) (capacity : ℕ) :
    rho ^ capacity * finiteCapacityOpportunityCost rho capacity ≤
      finiteCapacityGeometricNormalizer rho capacity ^ 2 := by
  induction capacity with
  | zero =>
      simp [finiteCapacityGeometricNormalizer, finiteCapacityOpportunityCost,
        finiteCapacityWeightedGeometricSum]
  | succ capacity ih =>
      have hpower_nonneg : 0 ≤ rho ^ capacity := pow_nonneg hrho_nonneg capacity
      have hnormalizer_nonneg :
          0 ≤ finiteCapacityGeometricNormalizer rho capacity :=
        (finiteCapacityGeometricNormalizer_pos hrho_nonneg capacity).le
      have hlinear := finiteCapacityOpportunityCost_linear_identity rho capacity
      simp only [finiteCapacityGeometricNormalizer_succ,
        finiteCapacityOpportunityCost_succ, pow_succ]
      push_cast at hlinear ⊢
      have hscaled := congrArg (fun x : ℝ => rho ^ capacity * x) hlinear
      have hadded : 0 ≤ rho ^ capacity * ((capacity : ℝ) + 1) :=
        mul_nonneg hpower_nonneg (by positivity)
      nlinarith

/-- The cumulative delay exposure rises with the finite queue capacity. -/
theorem finiteCapacityOpportunityCost_monotone
    {rho : ℝ} (hrho_nonneg : 0 ≤ rho) :
    Monotone (finiteCapacityOpportunityCost rho) := by
  intro i j hij
  refine Nat.le_induction ?_ ?_ j hij
  · exact le_rfl
  · intro n _ ih
    rw [finiteCapacityOpportunityCost_succ]
    linarith [finiteCapacityGeometricNormalizer_pos hrho_nonneg (n + 1)]

/-- A sequence that weakly rises up to a designated index and weakly falls
afterward attains a global maximum at that index. -/
theorem adjacentUnimodal_isGreatest (objective : ℕ → ℝ) (peak : ℕ)
    (hrise : ∀ capacity : ℕ, capacity < peak →
      objective capacity ≤ objective (capacity + 1))
    (hfall : ∀ capacity : ℕ, peak ≤ capacity →
      objective (capacity + 1) ≤ objective capacity) :
    ∀ capacity : ℕ, objective capacity ≤ objective peak := by
  intro capacity
  rcases le_total capacity peak with hbefore | hafter
  · exact
      (Nat.le_induction
        (P := fun n _ => n ≤ peak → objective capacity ≤ objective n)
        (by intro _; exact le_rfl)
        (by
          intro n _ ih hsucc
          have hn_lt_peak : n < peak := Nat.lt_of_succ_le hsucc
          exact (ih (Nat.le_of_succ_le hsucc)).trans (hrise n hn_lt_peak))
        peak hbefore) le_rfl
  · refine Nat.le_induction ?_ ?_ capacity hafter
    · exact le_rfl
    · intro n hn ih
      exact (hfall n hn).trans ih

/-- One-step change in toll revenue when the fee implements a finite admission
threshold. -/
theorem finiteCapacityAdmissionRevenue_succ_sub
    {rho reward queueCost serviceRate : ℝ}
    (hrho_nonneg : 0 ≤ rho) (hqueueCost_pos : 0 < queueCost)
    (hserviceRate_pos : 0 < serviceRate) (capacity : ℕ) :
    finiteCapacityAdmissionRevenue (rho * serviceRate)
        (reward - ((capacity + 1 : ℕ) : ℝ) * queueCost / serviceRate) rho
        (capacity + 1) -
      finiteCapacityAdmissionRevenue (rho * serviceRate)
        (reward - (capacity : ℝ) * queueCost / serviceRate) rho capacity =
      queueCost * rho /
          (finiteCapacityGeometricNormalizer rho capacity *
            finiteCapacityGeometricNormalizer rho (capacity + 1)) *
        ((reward * serviceRate / queueCost - (capacity : ℝ)) * rho ^ capacity -
          finiteCapacityGeometricNormalizer rho capacity ^ 2) := by
  have hnormalizer_ne : finiteCapacityGeometricNormalizer rho capacity ≠ 0 :=
    ne_of_gt (finiteCapacityGeometricNormalizer_pos hrho_nonneg capacity)
  have hnormalizer_succ_ne : finiteCapacityGeometricNormalizer rho (capacity + 1) ≠ 0 :=
    ne_of_gt (finiteCapacityGeometricNormalizer_pos hrho_nonneg (capacity + 1))
  have hnormalizer_succ_expanded_ne :
      finiteCapacityGeometricNormalizer rho capacity + rho ^ (capacity + 1) ≠ 0 := by
    rw [← finiteCapacityGeometricNormalizer_succ]
    exact hnormalizer_succ_ne
  have hgeometric :
      finiteCapacityGeometricNormalizer rho capacity * (1 - rho) =
        1 - rho ^ (capacity + 1) := by
    unfold finiteCapacityGeometricNormalizer
    exact geom_sum_mul_neg rho (capacity + 1)
  simp only [finiteCapacityAdmissionRevenue, finiteCapacityAdmittedArrivalRate]
  rw [finiteCapacityGeometricMass_eq_div_of_le (le_refl (capacity + 1)),
    finiteCapacityGeometricMass_eq_div_of_le (le_refl capacity),
    finiteCapacityGeometricNormalizer_succ]
  field_simp [hnormalizer_ne, hnormalizer_succ_ne, hnormalizer_succ_expanded_ne,
    ne_of_gt hqueueCost_pos, ne_of_gt hserviceRate_pos]
  have hcast : ((capacity + 1 : ℕ) : ℝ) = (capacity : ℝ) + 1 := by
    norm_num
  linear_combination
    (reward * serviceRate * rho * rho ^ capacity -
      queueCost * (capacity : ℝ) * rho * rho ^ capacity) * hgeometric -
    (rho * queueCost * finiteCapacityGeometricNormalizer rho capacity ^ 2) * hcast

theorem finiteCapacityGeometricMass_tsum
    {rho : ℝ} (hrho_nonneg : 0 ≤ rho) (capacity : ℕ) :
    ∑' n : ℕ, finiteCapacityGeometricMass rho capacity n = 1 := by
  let support := Finset.range (capacity + 1)
  have hsupp : ∀ n ∉ support, finiteCapacityGeometricMass rho capacity n = 0 := by
    intro n hn
    apply finiteCapacityGeometricMass_eq_zero_of_capacity_lt
    simpa [support, Nat.lt_succ_iff] using hn
  rw [tsum_eq_sum hsupp]
  calc
    ∑ n ∈ support, finiteCapacityGeometricMass rho capacity n =
        ∑ n ∈ support, rho ^ n / finiteCapacityGeometricNormalizer rho capacity := by
      apply Finset.sum_congr rfl
      intro n hn
      apply finiteCapacityGeometricMass_eq_div_of_le
      simpa [support, Nat.lt_succ_iff] using hn
    _ = finiteCapacityGeometricNormalizer rho capacity /
          finiteCapacityGeometricNormalizer rho capacity := by
      rw [← Finset.sum_div]
      rfl
    _ = 1 := div_self
      (ne_of_gt (finiteCapacityGeometricNormalizer_pos hrho_nonneg capacity))

theorem hasSum_finiteCapacityGeometricMass
    {rho : ℝ} (hrho_nonneg : 0 ≤ rho) (capacity : ℕ) :
    HasSum (finiteCapacityGeometricMass rho capacity) 1 := by
  let support := Finset.range (capacity + 1)
  have hsupp : ∀ n ∉ support, finiteCapacityGeometricMass rho capacity n = 0 := by
    intro n hn
    apply finiteCapacityGeometricMass_eq_zero_of_capacity_lt
    simpa [support, Nat.lt_succ_iff] using hn
  have hsum : (∑ n ∈ support, finiteCapacityGeometricMass rho capacity n) = 1 := by
    calc
      ∑ n ∈ support, finiteCapacityGeometricMass rho capacity n =
          ∑' n : ℕ, finiteCapacityGeometricMass rho capacity n :=
        (tsum_eq_sum hsupp).symm
      _ = 1 := finiteCapacityGeometricMass_tsum hrho_nonneg capacity
  rw [← hsum]
  exact hasSum_sum_of_ne_finset_zero hsupp

theorem finiteCapacity_detailedBalance
    (rho serviceRate : ℝ) (capacity : ℕ) :
    DetailedBalance
      (finiteCapacityBirthDeathRates (rho * serviceRate) serviceRate capacity)
      (finiteCapacityGeometricMass rho capacity) := by
  intro n
  by_cases hn : n < capacity
  · have hnle : n ≤ capacity := Nat.le_of_lt hn
    have hsuccle : n + 1 ≤ capacity := by omega
    simp [finiteCapacityBirthDeathRates, finiteCapacityGeometricMass, hn,
      hnle, hsuccle, pow_succ]
    ring
  · have hsucc : capacity < n + 1 := by omega
    simp [finiteCapacityBirthDeathRates, finiteCapacityGeometricMass, hn,
      Nat.not_le.mpr hsucc]

theorem finiteCapacity_stationaryGeneratorBalance
    (rho serviceRate : ℝ) (capacity : ℕ) :
    StationaryGeneratorBalance
      (finiteCapacityBirthDeathRates (rho * serviceRate) serviceRate capacity)
      (finiteCapacityGeometricMass rho capacity) :=
  (finiteCapacity_detailedBalance rho serviceRate capacity).stationaryGeneratorBalance

/-- The normalized stationary generator law of a finite-capacity M/M/1 queue.
No stability inequality is needed because arrivals are blocked at capacity. -/
noncomputable def finiteCapacity_geometricGeneratorStationaryLaw
    (rho serviceRate : ℝ) (hrho_nonneg : 0 ≤ rho) (capacity : ℕ) :
    GeneratorStationaryLaw
      (finiteCapacityBirthDeathRates (rho * serviceRate) serviceRate capacity) where
  mass := finiteCapacityGeometricMass rho capacity
  nonneg := finiteCapacityGeometricMass_nonneg hrho_nonneg capacity
  hasSum_one := hasSum_finiteCapacityGeometricMass hrho_nonneg capacity
  generator_balance := finiteCapacity_stationaryGeneratorBalance rho serviceRate capacity

end Queueing
end Probability
end AppliedModelingLib

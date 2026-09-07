import LG24ServiceLevelAgreements.ProposedFixedLoad
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Proposed theory: the one-class endogenous-admission objective

This file formalizes the one-class calculation in the July 2026 revision
memo.  For positive penalty, reliability, capacity, and risk, the interior
candidate `C - sqrt (a*C/D)` globally minimizes

`r * (D * (lambda-s) + a*s/(C-s))`

over admitted loads below capacity whenever the candidate is nonnegative.
The proof is an exact algebraic gap identity, not a derivative argument.  The
zero-penalty endpoint and exact constants in the two-Borough pooling threshold
are included as companion audit seams.
-/

namespace LG24ServiceLevelAgreements

noncomputable section

/-! ## Positive-penalty one-class objective -/

/-- The memo's one-class endogenous-admission objective. -/
def oneClassEndogenousObjective
    (risk penalty arrival reliability capacity admitted : ℝ) : ℝ :=
  risk * (penalty * (arrival - admitted) +
    reliability * admitted / (capacity - admitted))

/-- The stationary interior candidate from the memo's one-class calculation. -/
def oneClassInteriorCandidate
    (penalty reliability capacity : ℝ) : ℝ :=
  capacity - Real.sqrt (reliability * capacity / penalty)

private theorem oneClass_gap_algebra
    (risk penalty arrival reliability capacity admitted q : ℝ)
    (hden : capacity - admitted ≠ 0)
    (hq : q ≠ 0)
    (hbalance : penalty * q ^ 2 = reliability * capacity) :
    risk * (penalty * (arrival - admitted) +
          reliability * admitted / (capacity - admitted)) -
        risk * (penalty * (arrival - (capacity - q)) +
          reliability * (capacity - q) / (capacity - (capacity - q))) =
      risk * penalty * ((capacity - admitted) - q) ^ 2 /
        (capacity - admitted) := by
  field_simp [hden, hq]
  linear_combination risk * ((capacity - admitted) - q) * hbalance

/--
Exact objective gap around the interior candidate.  The right side is a
positive multiple of a square divided by remaining capacity.
-/
theorem oneClassEndogenousObjective_sub_interiorCandidate
    (risk penalty arrival reliability capacity admitted : ℝ)
    (hpenalty : 0 < penalty)
    (hreliability : 0 < reliability)
    (hcapacity : 0 < capacity)
    (hadmitted : admitted < capacity) :
    oneClassEndogenousObjective risk penalty arrival reliability capacity admitted -
        oneClassEndogenousObjective risk penalty arrival reliability capacity
          (oneClassInteriorCandidate penalty reliability capacity) =
      risk * penalty *
        ((capacity - admitted) -
          Real.sqrt (reliability * capacity / penalty)) ^ 2 /
        (capacity - admitted) := by
  let q : ℝ := Real.sqrt (reliability * capacity / penalty)
  have hqdef : q = Real.sqrt (reliability * capacity / penalty) := rfl
  have hquotient : 0 < reliability * capacity / penalty := by positivity
  have hqpos : 0 < q := Real.sqrt_pos.2 hquotient
  have hqne : q ≠ 0 := ne_of_gt hqpos
  have hdenpos : 0 < capacity - admitted := by linarith
  have hdenne : capacity - admitted ≠ 0 := ne_of_gt hdenpos
  have hqsq : q ^ 2 = reliability * capacity / penalty := by
    exact Real.sq_sqrt (le_of_lt hquotient)
  have hbalance : penalty * q ^ 2 = reliability * capacity := by
    rw [hqsq]
    field_simp
  simp only [oneClassEndogenousObjective, oneClassInteriorCandidate]
  rw [← hqdef]
  exact oneClass_gap_algebra risk penalty arrival reliability capacity admitted q
    hdenne hqne hbalance

/--
Under the memo's positive-parameter conditions, the candidate has no larger
objective than any admitted load below capacity.  When the candidate is also
nonnegative, this is the interior feasible minimizer.
-/
theorem oneClassInteriorCandidate_is_minimizer
    (risk penalty arrival reliability capacity admitted : ℝ)
    (hrisk : 0 ≤ risk)
    (hpenalty : 0 < penalty)
    (hreliability : 0 < reliability)
    (hcapacity : 0 < capacity)
    (hadmitted_lt : admitted < capacity) :
    oneClassEndogenousObjective risk penalty arrival reliability capacity
        (oneClassInteriorCandidate penalty reliability capacity) ≤
      oneClassEndogenousObjective risk penalty arrival reliability capacity admitted := by
  have hgap := oneClassEndogenousObjective_sub_interiorCandidate
    risk penalty arrival reliability capacity admitted
    hpenalty hreliability hcapacity hadmitted_lt
  have hden : 0 ≤ capacity - admitted := by linarith
  have hsquare : 0 ≤
      ((capacity - admitted) -
        Real.sqrt (reliability * capacity / penalty)) ^ 2 := sq_nonneg _
  have hnonneg : 0 ≤
      risk * penalty *
        ((capacity - admitted) -
          Real.sqrt (reliability * capacity / penalty)) ^ 2 /
        (capacity - admitted) := by positivity
  linarith

/-- Positive inputs make the interior candidate strictly smaller than capacity. -/
theorem oneClassInteriorCandidate_lt_capacity
    (penalty reliability capacity : ℝ)
    (hpenalty : 0 < penalty)
    (hreliability : 0 < reliability)
    (hcapacity : 0 < capacity) :
    oneClassInteriorCandidate penalty reliability capacity < capacity := by
  have hroot : 0 < Real.sqrt (reliability * capacity / penalty) := by
    exact Real.sqrt_pos.2 (by positivity)
  simp only [oneClassInteriorCandidate]
  linarith

/--
If the interior candidate lies in `[0, arrival]`, it is a feasible global
minimizer over admitted loads in that interval that remain below capacity.
-/
theorem oneClassInteriorCandidate_is_feasible_minimizer
    (risk penalty arrival reliability capacity : ℝ)
    (hrisk : 0 ≤ risk)
    (hpenalty : 0 < penalty)
    (hreliability : 0 < reliability)
    (hcapacity : 0 < capacity)
    (hcandidate_nonneg :
      0 ≤ oneClassInteriorCandidate penalty reliability capacity)
    (hcandidate_le_arrival :
      oneClassInteriorCandidate penalty reliability capacity ≤ arrival) :
    0 ≤ oneClassInteriorCandidate penalty reliability capacity ∧
      oneClassInteriorCandidate penalty reliability capacity ≤ arrival ∧
      oneClassInteriorCandidate penalty reliability capacity < capacity ∧
      ∀ admitted, 0 ≤ admitted → admitted ≤ arrival → admitted < capacity →
        oneClassEndogenousObjective risk penalty arrival reliability capacity
            (oneClassInteriorCandidate penalty reliability capacity) ≤
          oneClassEndogenousObjective risk penalty arrival reliability capacity admitted := by
  refine ⟨hcandidate_nonneg, hcandidate_le_arrival,
    oneClassInteriorCandidate_lt_capacity penalty reliability capacity
      hpenalty hreliability hcapacity, ?_⟩
  intro admitted _hadmitted_nonneg _hadmitted_le_arrival hadmitted_lt
  exact oneClassInteriorCandidate_is_minimizer
    risk penalty arrival reliability capacity admitted
    hrisk hpenalty hreliability hcapacity hadmitted_lt

/-! ## Full clipped positive-penalty optimizer -/

/-- The memo's one-class optimizer, clipped to the feasible interval. -/
def oneClassClippedOptimizer
    (penalty reliability capacity arrival : ℝ) : ℝ :=
  min arrival (max 0 (oneClassInteriorCandidate penalty reliability capacity))

private theorem oneClass_objective_sub_zero
    (risk penalty arrival reliability capacity admitted : ℝ)
    (hden : capacity - admitted ≠ 0) :
    oneClassEndogenousObjective risk penalty arrival reliability capacity admitted -
        oneClassEndogenousObjective risk penalty arrival reliability capacity 0 =
      risk * admitted *
        (reliability - penalty * (capacity - admitted)) /
        (capacity - admitted) := by
  simp only [oneClassEndogenousObjective]
  field_simp [hden]
  ring

private theorem oneClass_objective_sub_larger_admission
    (risk penalty arrival reliability capacity admitted upper : ℝ)
    (hadmitted_den : capacity - admitted ≠ 0)
    (hupper_den : capacity - upper ≠ 0) :
    oneClassEndogenousObjective risk penalty arrival reliability capacity admitted -
        oneClassEndogenousObjective risk penalty arrival reliability capacity upper =
      risk * (upper - admitted) *
        (penalty * (capacity - admitted) * (capacity - upper) -
          reliability * capacity) /
        ((capacity - admitted) * (capacity - upper)) := by
  simp only [oneClassEndogenousObjective]
  field_simp [hadmitted_den, hupper_den]
  ring

private theorem oneClass_zero_minimizes_of_candidate_nonpos
    (risk penalty arrival reliability capacity admitted : ℝ)
    (hrisk : 0 ≤ risk)
    (hpenalty : 0 < penalty)
    (hreliability : 0 < reliability)
    (hcapacity : 0 < capacity)
    (hcandidate : oneClassInteriorCandidate penalty reliability capacity ≤ 0)
    (hadmitted_nonneg : 0 ≤ admitted)
    (hadmitted_lt : admitted < capacity) :
    oneClassEndogenousObjective risk penalty arrival reliability capacity 0 ≤
      oneClassEndogenousObjective risk penalty arrival reliability capacity admitted := by
  let q : ℝ := Real.sqrt (reliability * capacity / penalty)
  have hqdef : q = Real.sqrt (reliability * capacity / penalty) := rfl
  have hquotient : 0 < reliability * capacity / penalty := by positivity
  have hqpos : 0 < q := Real.sqrt_pos.2 hquotient
  have hqsq : q ^ 2 = reliability * capacity / penalty :=
    Real.sq_sqrt (le_of_lt hquotient)
  have hbalance : penalty * q ^ 2 = reliability * capacity := by
    rw [hqsq]
    field_simp
  simp only [oneClassInteriorCandidate] at hcandidate
  rw [← hqdef] at hcandidate
  have hcapacity_le_q : capacity ≤ q := by linarith
  have hcapacity_sq_le_q_sq : capacity ^ 2 ≤ q ^ 2 := by
    nlinarith [sq_nonneg (q - capacity)]
  have hscaled : (penalty * capacity) * capacity ≤ reliability * capacity := by
    calc
      (penalty * capacity) * capacity = penalty * capacity ^ 2 := by ring
      _ ≤ penalty * q ^ 2 :=
        mul_le_mul_of_nonneg_left hcapacity_sq_le_q_sq (le_of_lt hpenalty)
      _ = reliability * capacity := hbalance
  have hcapacity_requirement : penalty * capacity ≤ reliability :=
    le_of_mul_le_mul_right hscaled hcapacity
  have hpenalty_admitted : 0 ≤ penalty * admitted :=
    mul_nonneg (le_of_lt hpenalty) hadmitted_nonneg
  have hterm : 0 ≤ reliability - penalty * (capacity - admitted) := by
    nlinarith
  have hdenpos : 0 < capacity - admitted := by linarith
  have hdiff := oneClass_objective_sub_zero
    risk penalty arrival reliability capacity admitted (ne_of_gt hdenpos)
  have hrhs : 0 ≤
      risk * admitted *
        (reliability - penalty * (capacity - admitted)) /
        (capacity - admitted) := by positivity
  linarith

private theorem oneClass_arrival_minimizes_of_candidate_ge_arrival
    (risk penalty arrival reliability capacity admitted : ℝ)
    (hrisk : 0 ≤ risk)
    (hpenalty : 0 < penalty)
    (hreliability : 0 < reliability)
    (hcapacity : 0 < capacity)
    (harrival_lt : arrival < capacity)
    (hcandidate : arrival ≤
      oneClassInteriorCandidate penalty reliability capacity)
    (hadmitted_le : admitted ≤ arrival) :
    oneClassEndogenousObjective risk penalty arrival reliability capacity arrival ≤
      oneClassEndogenousObjective risk penalty arrival reliability capacity admitted := by
  let q : ℝ := Real.sqrt (reliability * capacity / penalty)
  have hqdef : q = Real.sqrt (reliability * capacity / penalty) := rfl
  have hquotient : 0 < reliability * capacity / penalty := by positivity
  have hqpos : 0 < q := Real.sqrt_pos.2 hquotient
  have hqsq : q ^ 2 = reliability * capacity / penalty :=
    Real.sq_sqrt (le_of_lt hquotient)
  have hbalance : penalty * q ^ 2 = reliability * capacity := by
    rw [hqsq]
    field_simp
  simp only [oneClassInteriorCandidate] at hcandidate
  rw [← hqdef] at hcandidate
  have hq_le_remaining : q ≤ capacity - arrival := by linarith
  have harrival_den_pos : 0 < capacity - arrival := by linarith
  have hadmitted_den_pos : 0 < capacity - admitted := by linarith
  have hremaining_le : capacity - arrival ≤ capacity - admitted := by linarith
  have hq_sq_le_remaining_sq :
      q ^ 2 ≤ (capacity - arrival) ^ 2 := by
    nlinarith [sq_nonneg ((capacity - arrival) - q)]
  have hremaining_sq_le_product :
      (capacity - arrival) ^ 2 ≤
        (capacity - admitted) * (capacity - arrival) := by
    have hmul := mul_le_mul_of_nonneg_right hremaining_le
      (le_of_lt harrival_den_pos)
    nlinarith
  have hq_sq_le_product :
      q ^ 2 ≤ (capacity - admitted) * (capacity - arrival) :=
    hq_sq_le_remaining_sq.trans hremaining_sq_le_product
  have hnumerator :
      0 ≤ penalty * (capacity - admitted) * (capacity - arrival) -
        reliability * capacity := by
    have hmul := mul_le_mul_of_nonneg_left hq_sq_le_product
      (le_of_lt hpenalty)
    rw [hbalance] at hmul
    linarith
  have hdiff := oneClass_objective_sub_larger_admission
    risk penalty arrival reliability capacity admitted arrival
    (ne_of_gt hadmitted_den_pos) (ne_of_gt harrival_den_pos)
  have hdenproduct :
      0 < (capacity - admitted) * (capacity - arrival) :=
    mul_pos hadmitted_den_pos harrival_den_pos
  have hrhs : 0 ≤
      risk * (arrival - admitted) *
        (penalty * (capacity - admitted) * (capacity - arrival) -
          reliability * capacity) /
        ((capacity - admitted) * (capacity - arrival)) := by
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg hrisk (sub_nonneg.mpr hadmitted_le)) hnumerator
    · exact le_of_lt hdenproduct
  linarith

/--
For nonnegative risk and positive penalty, reliability, and capacity, the
memo's clipped candidate is feasible and globally minimizes the one-class
endogenous objective over `0 ≤ s ≤ arrival < capacity`.
-/
theorem oneClassClippedOptimizer_is_feasible_minimizer
    (risk penalty arrival reliability capacity : ℝ)
    (hrisk : 0 ≤ risk)
    (hpenalty : 0 < penalty)
    (hreliability : 0 < reliability)
    (hcapacity : 0 < capacity)
    (harrival_nonneg : 0 ≤ arrival)
    (harrival_lt : arrival < capacity) :
    0 ≤ oneClassClippedOptimizer penalty reliability capacity arrival ∧
      oneClassClippedOptimizer penalty reliability capacity arrival ≤ arrival ∧
      oneClassClippedOptimizer penalty reliability capacity arrival < capacity ∧
      ∀ admitted, 0 ≤ admitted → admitted ≤ arrival →
        oneClassEndogenousObjective risk penalty arrival reliability capacity
            (oneClassClippedOptimizer penalty reliability capacity arrival) ≤
          oneClassEndogenousObjective risk penalty arrival reliability capacity admitted := by
  have hoptimizer_nonneg :
      0 ≤ oneClassClippedOptimizer penalty reliability capacity arrival := by
    simp only [oneClassClippedOptimizer]
    exact le_min harrival_nonneg (le_max_left 0 _)
  have hoptimizer_le :
      oneClassClippedOptimizer penalty reliability capacity arrival ≤ arrival := by
    exact min_le_left _ _
  refine ⟨hoptimizer_nonneg, hoptimizer_le,
    hoptimizer_le.trans_lt harrival_lt, ?_⟩
  intro admitted hadmitted_nonneg hadmitted_le
  have hadmitted_lt : admitted < capacity := hadmitted_le.trans_lt harrival_lt
  by_cases hlow : oneClassInteriorCandidate penalty reliability capacity ≤ 0
  · have hopt : oneClassClippedOptimizer penalty reliability capacity arrival = 0 := by
      simp [oneClassClippedOptimizer, max_eq_left hlow,
        min_eq_right harrival_nonneg]
    rw [hopt]
    exact oneClass_zero_minimizes_of_candidate_nonpos
      risk penalty arrival reliability capacity admitted
      hrisk hpenalty hreliability hcapacity hlow hadmitted_nonneg hadmitted_lt
  · have hcandidate_pos :
        0 < oneClassInteriorCandidate penalty reliability capacity :=
      lt_of_not_ge hlow
    by_cases hhigh : arrival ≤
        oneClassInteriorCandidate penalty reliability capacity
    · have hopt :
          oneClassClippedOptimizer penalty reliability capacity arrival = arrival := by
        simp [oneClassClippedOptimizer, max_eq_right (le_of_lt hcandidate_pos),
          min_eq_left hhigh]
      rw [hopt]
      exact oneClass_arrival_minimizes_of_candidate_ge_arrival
        risk penalty arrival reliability capacity admitted
        hrisk hpenalty hreliability hcapacity harrival_lt hhigh hadmitted_le
    · have hcandidate_le :
          oneClassInteriorCandidate penalty reliability capacity ≤ arrival :=
        le_of_lt (lt_of_not_ge hhigh)
      have hopt : oneClassClippedOptimizer penalty reliability capacity arrival =
          oneClassInteriorCandidate penalty reliability capacity := by
        simp [oneClassClippedOptimizer, max_eq_right (le_of_lt hcandidate_pos),
          min_eq_right hcandidate_le]
      rw [hopt]
      exact oneClassInteriorCandidate_is_minimizer
        risk penalty arrival reliability capacity admitted
        hrisk hpenalty hreliability hcapacity hadmitted_lt

/-! ## Zero-penalty endpoint -/

/-- With zero noninspection penalty, the objective reduces to served-delay cost. -/
theorem oneClassEndogenousObjective_zero_penalty
    (risk arrival reliability capacity admitted : ℝ) :
    oneClassEndogenousObjective risk 0 arrival reliability capacity admitted =
      risk * reliability * admitted / (capacity - admitted) := by
  simp [oneClassEndogenousObjective]
  ring

/-- At zero admission, the full one-class objective with zero penalty is zero. -/
theorem oneClassEndogenousObjective_zero_penalty_zero_admission
    (risk arrival reliability capacity : ℝ) :
    oneClassEndogenousObjective risk 0 arrival reliability capacity 0 = 0 := by
  simp [oneClassEndogenousObjective]

/--
For nonnegative risk and reliability, zero admission minimizes the zero-penalty
objective over nonnegative admitted loads below capacity.
-/
theorem oneClassEndogenousObjective_zero_penalty_zero_is_minimizer
    (risk arrival reliability capacity admitted : ℝ)
    (hrisk : 0 ≤ risk)
    (hreliability : 0 ≤ reliability)
    (hadmitted : 0 ≤ admitted)
    (hcapacity : admitted < capacity) :
    oneClassEndogenousObjective risk 0 arrival reliability capacity 0 ≤
      oneClassEndogenousObjective risk 0 arrival reliability capacity admitted := by
  rw [oneClassEndogenousObjective_zero_penalty_zero_admission,
    oneClassEndogenousObjective_zero_penalty]
  apply div_nonneg
  · positivity
  · linarith

/-! ## Exact constants in the two-Borough pooling threshold -/

/-- The upper squared load-ratio threshold is `7 + 4√3`. -/
theorem twoBorough_upper_ratio_threshold_sq :
    (2 + Real.sqrt 3) ^ 2 = 7 + 4 * Real.sqrt 3 := by
  have hsqrt : Real.sqrt (3 : ℝ) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  nlinarith

/-- The lower squared threshold is `7 - 4√3`. -/
theorem twoBorough_lower_ratio_threshold_sq :
    (2 - Real.sqrt 3) ^ 2 = 7 - 4 * Real.sqrt 3 := by
  have hsqrt : Real.sqrt (3 : ℝ) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  nlinarith

/-- The lower squared threshold is the exact reciprocal of the upper one. -/
theorem twoBorough_ratio_thresholds_mul_eq_one :
    (2 + Real.sqrt 3) ^ 2 * (2 - Real.sqrt 3) ^ 2 = 1 := by
  have hsqrt : Real.sqrt (3 : ℝ) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  nlinarith

end

end LG24ServiceLevelAgreements

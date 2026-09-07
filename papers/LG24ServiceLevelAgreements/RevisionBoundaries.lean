import LG24ServiceLevelAgreements.ProposedFixedLoad
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# Revision boundaries and cross-model identities

This module formalizes the safe mathematical boundary statements called out by
the July 2026 revision memo and by `codex-lean-edits.tex`.  In particular, the
queueing response-tail theorem remains an explicit imported premise; Lean
checks the implication from that premise to the deterministic SLA constraint
and all downstream algebra recorded here.

The file also distinguishes conditional-delay burden from all-request burden,
proves convexity of the paper's sum-of-within-category ranges for the
two-Borough case, records the arrival-weight coefficient in the parity
tie-breaker, and makes the risk-bin extension a literal finite reindexing.
-/

namespace LG24ServiceLevelAgreements

open scoped BigOperators

noncomputable section

/-! ## Explicit queueing-theorem boundary -/

/--
The response-tail inequality imported from the external GPS queueing result.
No queueing theorem is asserted in this development: a caller must supply this
predicate for the system under study.
-/
def ImportedGPSTailBound
    (tailProbability guaranteedSlack delay : ℝ) : Prop :=
  tailProbability ≤ Real.exp (-(guaranteedSlack * delay))

/-- The SLA target expressed using a positive log-tail parameter `a`. -/
def ExponentialSLATarget (tailProbability logTail : ℝ) : Prop :=
  tailProbability ≤ Real.exp (-logTail)

/--
Once the external queueing bound is supplied, the multiplicative constraint
`a ≤ x z` is sufficient for the target tail probability `exp (-a)`.
-/
theorem importedGPSTailBound_implies_exponentialSLATarget
    {tailProbability guaranteedSlack delay logTail : ℝ}
    (htail : ImportedGPSTailBound tailProbability guaranteedSlack delay)
    (hsla : logTail ≤ guaranteedSlack * delay) :
    ExponentialSLATarget tailProbability logTail := by
  exact htail.trans (Real.exp_le_exp.mpr (by linarith))

/-! ## Positive-slack and zero-admission repairs -/

/-- A positive reciprocal requirement cannot fit inside zero or negative excess capacity. -/
theorem positive_excessCapacity_of_active_reciprocal_requirement
    {logTail delay excessCapacity : ℝ}
    (hlogTail : 0 < logTail) (hdelay : 0 < delay)
    (hfeasible : logTail / delay ≤ excessCapacity) :
    0 < excessCapacity :=
  lt_of_lt_of_le (div_pos hlogTail hdelay) hfeasible

/-- The zero-slack boundary is infeasible for an active class with a finite positive SLA. -/
theorem zero_excessCapacity_infeasible_for_active_class
    {logTail delay : ℝ} (hlogTail : 0 < logTail) (hdelay : 0 < delay) :
    ¬logTail / delay ≤ 0 := by
  exact not_le_of_gt (div_pos hlogTail hdelay)

/--
Even when admitted load is zero, a positive log-tail requirement and positive
allocated capacity force any feasible conditional SLA delay to be positive.
-/
theorem zeroAdmittedLoad_feasible_delay_positive
    {capacity logTail delay : ℝ}
    (hcapacity : 0 < capacity) (hlogTail : 0 < logTail)
    (hfeasible : fixedLoadSLAFeasible capacity 0 logTail delay) :
    0 < delay := by
  by_contra hnot
  have hdelay : delay ≤ 0 := le_of_not_gt hnot
  have hproduct : capacity * delay ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hcapacity.le hdelay
  simp only [fixedLoadSLAFeasible, sub_zero] at hfeasible
  linarith

/-- In particular, zero admitted load does not make a zero-day conditional SLA feasible. -/
theorem zeroAdmittedLoad_zeroDelay_infeasible
    {capacity logTail : ℝ} (hlogTail : 0 < logTail) :
    ¬fixedLoadSLAFeasible capacity 0 logTail 0 := by
  simpa [fixedLoadSLAFeasible] using hlogTail

/-! ## Conditional versus all-request burden -/

/-- Risk-weighted burden conditional on a request being admitted. -/
def conditionalRequestBurden (risk conditionalDelay : ℝ) : ℝ :=
  risk * conditionalDelay

/-- With full admission, all-request burden equals conditional burden. -/
theorem allRequestBurden_fullAdmission
    (risk conditionalDelay noninspectionPenalty : ℝ) :
    allRequestBurden risk 1 conditionalDelay noninspectionPenalty =
      conditionalRequestBurden risk conditionalDelay := by
  simp [allRequestBurden, conditionalRequestBurden]

/-- With zero admission, conditional delay drops out and only non-inspection burden remains. -/
theorem allRequestBurden_zeroAdmission
    (risk conditionalDelay noninspectionPenalty : ℝ) :
    allRequestBurden risk 0 conditionalDelay noninspectionPenalty =
      risk * noninspectionPenalty := by
  simp [allRequestBurden]

/-- The all-request burden decomposes into a fixed offset and an admitted-delay term. -/
theorem allRequestBurden_eq_offset_add_delay
    (risk inspectionProbability conditionalDelay noninspectionPenalty : ℝ) :
    allRequestBurden risk inspectionProbability conditionalDelay noninspectionPenalty =
      risk * (1 - inspectionProbability) * noninspectionPenalty +
        risk * inspectionProbability * conditionalDelay := by
  simp only [allRequestBurden]
  ring

/--
For a common fixed non-inspection offset, the remaining delay contribution at
a reciprocal-excess-capacity endpoint scales exactly as `1 / E`.
-/
theorem allRequestBurden_reciprocal_excessCapacity_decomposition
    (risk inspectionProbability rootTerm excessCapacity noninspectionPenalty : ℝ) :
    allRequestBurden risk inspectionProbability (rootTerm / excessCapacity)
        noninspectionPenalty =
      risk * (1 - inspectionProbability) * noninspectionPenalty +
        (risk * inspectionProbability * rootTerm) / excessCapacity := by
  rw [allRequestBurden_eq_offset_add_delay]
  ring

/--
Excess capacity alone cannot remove disparity caused by unequal fixed
non-inspection offsets: this example has range one for arbitrary delays.
-/
theorem unequal_noninspection_offsets_survive_any_delays
    (delay₁ delay₂ : ℝ) :
    twoBoroughRange
        (allRequestBurden 1 0 delay₁ 1)
        (allRequestBurden 1 0 delay₂ 2) = 1 := by
  norm_num [allRequestBurden, twoBoroughRange]

/-! ## The actual sum-of-within-category-ranges objective -/

/-- A two-Borough range is always nonnegative. -/
theorem twoBoroughRange_nonnegative (burden₁ burden₂ : ℝ) :
    0 ≤ twoBoroughRange burden₁ burden₂ := by
  exact sub_nonneg.mpr (min_le_max)

/-- The two-Borough range is the absolute difference of the two burdens. -/
theorem revision_twoBoroughRange_eq_abs_sub (burden₁ burden₂ : ℝ) :
    twoBoroughRange burden₁ burden₂ = |burden₁ - burden₂| := by
  by_cases h : burden₁ ≤ burden₂
  · simp [twoBoroughRange, h, abs_of_nonpos (sub_nonpos.mpr h)]
  · have h' : burden₂ ≤ burden₁ := le_of_not_ge h
    simp [twoBoroughRange, h', abs_of_nonneg (sub_nonneg.mpr h')]

/--
Convexity of one category's two-Borough range under affine interpolation of
the two burden vectors.
-/
theorem twoBoroughRange_convexCombination
    {theta left₁ left₂ right₁ right₂ : ℝ}
    (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1) :
    twoBoroughRange
        (theta * left₁ + (1 - theta) * left₂)
        (theta * right₁ + (1 - theta) * right₂) ≤
      theta * twoBoroughRange left₁ right₁ +
        (1 - theta) * twoBoroughRange left₂ right₂ := by
  rw [revision_twoBoroughRange_eq_abs_sub, revision_twoBoroughRange_eq_abs_sub,
    revision_twoBoroughRange_eq_abs_sub]
  have hone : 0 ≤ 1 - theta := sub_nonneg.mpr htheta1
  calc
    |(theta * left₁ + (1 - theta) * left₂) -
        (theta * right₁ + (1 - theta) * right₂)| =
        |theta * (left₁ - right₁) + (1 - theta) * (left₂ - right₂)| := by
          congr 1
          ring
    _ ≤ |theta * (left₁ - right₁)| +
        |(1 - theta) * (left₂ - right₂)| := abs_add_le _ _
    _ = theta * |left₁ - right₁| +
        (1 - theta) * |left₂ - right₂| := by
          rw [abs_mul, abs_mul, abs_of_nonneg htheta0, abs_of_nonneg hone]

/-- The paper's two-Borough all-request equity objective sums ranges by category. -/
def allRequestTwoBoroughRangeObjective
    {Category : Type*} [Fintype Category]
    (leftBurden rightBurden : Category → ℝ) : ℝ :=
  ∑ k, twoBoroughRange (leftBurden k) (rightBurden k)

/-- A finite sum of within-category two-Borough ranges is convex. -/
theorem allRequestTwoBoroughRangeObjective_convexCombination
    {Category : Type*} [Fintype Category]
    {theta : ℝ} (left₁ left₂ right₁ right₂ : Category → ℝ)
    (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1) :
    allRequestTwoBoroughRangeObjective
        (fun k ↦ theta * left₁ k + (1 - theta) * left₂ k)
        (fun k ↦ theta * right₁ k + (1 - theta) * right₂ k) ≤
      theta * allRequestTwoBoroughRangeObjective left₁ right₁ +
        (1 - theta) * allRequestTwoBoroughRangeObjective left₂ right₂ := by
  classical
  simp only [allRequestTwoBoroughRangeObjective, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun k _ ↦
    twoBoroughRange_convexCombination htheta0 htheta1

/-! ## Parity weights and risk-bin reindexing -/

/--
If every Borough in a category has common all-request burden `u`, its
efficiency contribution is `u` times total ARRIVAL load, not admitted load.
-/
theorem arrivalWeightedBurden_eq_totalArrival_mul_commonBurden
    {Borough : Type*} [Fintype Borough]
    (arrival burden : Borough → ℝ) (commonBurden : ℝ)
    (hparity : ∀ b, burden b = commonBurden) :
    (∑ b, arrival b * burden b) = (∑ b, arrival b) * commonBurden := by
  classical
  simp_rw [hparity]
  rw [Finset.sum_mul]

/-- The same formula with admitted-load weights, included to expose the wrong coefficient. -/
def admittedWeightedParityCoefficient
    {Borough : Type*} [Fintype Borough] (admitted : Borough → ℝ) : ℝ :=
  ∑ b, admitted b

/-- The correct all-request parity coefficient. -/
def arrivalWeightedParityCoefficient
    {Borough : Type*} [Fintype Borough] (arrival : Borough → ℝ) : ℝ :=
  ∑ b, arrival b

/-- A concrete instance where arrival and admitted parity coefficients differ. -/
theorem arrival_and_admitted_parity_coefficients_can_differ :
    arrivalWeightedParityCoefficient (fun _ : Fin 2 ↦ (2 : ℝ)) = 4 ∧
      admittedWeightedParityCoefficient (fun _ : Fin 2 ↦ (1 : ℝ)) = 2 := by
  norm_num [arrivalWeightedParityCoefficient, admittedWeightedParityCoefficient,
    Fin.sum_univ_two]

/-- A nested category/risk-bin/Borough total. -/
def nestedRiskBinTotal
    {Category RiskBin Borough : Type*}
    [Fintype Category] [Fintype RiskBin] [Fintype Borough]
    (value : Category → RiskBin → Borough → ℝ) : ℝ :=
  ∑ k, ∑ h, ∑ b, value k h b

/-- The identical total after replacing the cell index by `(category, risk bin, Borough)`. -/
def flatRiskBinTotal
    {Category RiskBin Borough : Type*}
    [Fintype Category] [Fintype RiskBin] [Fintype Borough]
    (value : Category → RiskBin → Borough → ℝ) : ℝ :=
  ∑ cell : (Category × RiskBin) × Borough,
    value cell.1.1 cell.1.2 cell.2

/-- Adding a risk-bin coordinate is a literal finite reindexing of the same sum. -/
theorem flatRiskBinTotal_eq_nestedRiskBinTotal
    {Category RiskBin Borough : Type*}
    [Fintype Category] [Fintype RiskBin] [Fintype Borough]
    (value : Category → RiskBin → Borough → ℝ) :
    flatRiskBinTotal value = nestedRiskBinTotal value := by
  classical
  unfold flatRiskBinTotal nestedRiskBinTotal
  rw [Fintype.sum_prod_type]
  change (∑ kh : Category × RiskBin, ∑ b, value kh.1 kh.2 b) = _
  rw [Fintype.sum_prod_type]

/-! ## Exact symmetry and lexicographic zero price -/

/-- A point minimizes an objective over a feasible set. -/
def MinimizesOn {X : Type*} (feasible : Set X) (objective : X → ℝ) (x : X) : Prop :=
  x ∈ feasible ∧ ∀ y ∈ feasible, objective x ≤ objective y

/-- Equity is minimized first, with efficiency as the tie-breaker. -/
def LexicographicallyMinimizesEquityThenEfficiencyOn
    {X : Type*} (feasible : Set X) (equity efficiency : X → ℝ) (x : X) : Prop :=
  x ∈ feasible ∧
    (∀ y ∈ feasible, equity x ≤ equity y) ∧
    (∀ y ∈ feasible, equity y = equity x → efficiency x ≤ efficiency y)

/--
If disparity is everywhere nonnegative and an efficiency minimizer has zero
disparity, that same point is a lexicographic equity-then-efficiency minimizer.
-/
theorem zeroEquity_efficiencyMinimizer_is_lexicographicMinimizer
    {X : Type*} {feasible : Set X} {equity efficiency : X → ℝ} {x : X}
    (heff : MinimizesOn feasible efficiency x)
    (hequity_nonnegative : ∀ y ∈ feasible, 0 ≤ equity y)
    (hequity_zero : equity x = 0) :
    LexicographicallyMinimizesEquityThenEfficiencyOn
      feasible equity efficiency x := by
  refine ⟨heff.1, ?_, ?_⟩
  · intro y hy
    rw [hequity_zero]
    exact hequity_nonnegative y hy
  · intro y hy _
    exact heff.2 y hy

/-- Choosing the same exact-symmetry endpoint on both sides gives zero additive price. -/
theorem exactSymmetry_sameEndpoint_priceOfEquity_zero
    {X : Type*} (efficiency : X → ℝ) (x : X) :
    efficiency x - efficiency x = 0 := by
  ring

end

end LG24ServiceLevelAgreements

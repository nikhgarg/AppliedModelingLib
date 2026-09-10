import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Tactic
import AppliedModelingLib.GameTheory.MultitaskIncentives
import AppliedModelingLib.GameTheory.Choice.EquilibriumAE
import AppliedModelingLib.Foundations.Optimization.Endpoint

/-!
# Strategic ranking

This file contains the source-facing algebra and order layer for
Liu--Garg--Borgs (2022).  The local statements below keep model primitives and
proof obligations explicit; the paper-facing rank-preservation and
second-price endpoints are assembled in `GammaRank.lean`,
`SecondPriceFinite.lean`, and `PaperInterface.lean`.
-/

namespace LBG22StrategicRanking

open Set
open MeasureTheory

/-- Source two-level policy parameters: capacity `rho` and cutoff `c`. -/
structure TwoLevelPolicy where
  rho : ℝ
  c : ℝ
  rho_pos : 0 < rho
  rho_lt_one : rho < 1
  c_pos : 0 < c
  c_le_capacity_complement : c ≤ 1 - rho

/-- Source high-rank admission probability `ell_1 = rho / (1 - c)`. -/
noncomputable def twoLevelHighProb (P : TwoLevelPolicy) : ℝ :=
  P.rho / (1 - P.c)

/-- Source two-level admission probability as a function of post-effort rank. -/
noncomputable def twoLevelAdmission (P : TwoLevelPolicy) (theta : ℝ) : ℝ :=
  if P.c ≤ theta then twoLevelHighProb P else 0

/-- Source one-level pure-randomization admission probability. -/
def pureRandomizationAdmission (rho : ℝ) (_theta : ℝ) : ℝ :=
  rho

theorem twoLevel_one_sub_cutoff_pos (P : TwoLevelPolicy) : 0 < 1 - P.c := by
  linarith [P.c_le_capacity_complement, P.rho_pos]

theorem twoLevel_highProb_pos (P : TwoLevelPolicy) : 0 < twoLevelHighProb P := by
  exact div_pos P.rho_pos (twoLevel_one_sub_cutoff_pos P)

theorem twoLevel_highProb_le_one (P : TwoLevelPolicy) : twoLevelHighProb P ≤ 1 := by
  have hden_nonneg : 0 ≤ 1 - P.c := le_of_lt (twoLevel_one_sub_cutoff_pos P)
  have hrho_le_den : P.rho ≤ 1 - P.c := by
    linarith [P.c_le_capacity_complement]
  calc
    twoLevelHighProb P = P.rho / (1 - P.c) := rfl
    _ ≤ (1 - P.c) / (1 - P.c) :=
      div_le_div_of_nonneg_right hrho_le_den hden_nonneg
    _ = 1 := by
      exact div_self (ne_of_gt (twoLevel_one_sub_cutoff_pos P))

theorem twoLevel_highProb_gt_capacity (P : TwoLevelPolicy) :
    P.rho < twoLevelHighProb P := by
  have hden_pos : 0 < 1 - P.c := twoLevel_one_sub_cutoff_pos P
  have hden_lt_one : 1 - P.c < 1 := by linarith [P.c_pos]
  rw [twoLevelHighProb]
  rw [lt_div_iff₀ hden_pos]
  nlinarith [P.rho_pos, hden_lt_one]

theorem twoLevel_highProb_at_nonrandomized_cutoff
    {rho : ℝ} (hrho : rho ≠ 0) :
    rho / (1 - (1 - rho)) = 1 := by
  ring_nf
  exact div_self hrho

theorem twoLevel_highProb_mul_tail_eq_capacity (P : TwoLevelPolicy) :
    twoLevelHighProb P * (1 - P.c) = P.rho := by
  rw [twoLevelHighProb]
  field_simp [ne_of_gt (twoLevel_one_sub_cutoff_pos P)]

theorem twoLevel_tail_mul_highProb_eq_capacity (P : TwoLevelPolicy) :
    (1 - P.c) * twoLevelHighProb P = P.rho := by
  rw [mul_comm]
  exact twoLevel_highProb_mul_tail_eq_capacity P

theorem twoLevel_highProb_mem_unit_interval (P : TwoLevelPolicy) :
    0 < twoLevelHighProb P ∧ P.rho < twoLevelHighProb P ∧
      twoLevelHighProb P ≤ 1 :=
  ⟨twoLevel_highProb_pos P, twoLevel_highProb_gt_capacity P,
    twoLevel_highProb_le_one P⟩

theorem twoLevel_highProb_mono_of_cutoff_mono
    {rho cLow cHigh : ℝ}
    (hrho : 0 ≤ rho)
    (hc_mono : cLow ≤ cHigh)
    (hdenLow : 0 < 1 - cLow)
    (hdenHigh : 0 < 1 - cHigh) :
    rho / (1 - cLow) ≤ rho / (1 - cHigh) := by
  have hden_order : 1 - cHigh ≤ 1 - cLow := by linarith
  have hinv : 1 / (1 - cLow) ≤ 1 / (1 - cHigh) :=
    one_div_le_one_div_of_le hdenHigh hden_order
  calc
    rho / (1 - cLow) = rho * (1 / (1 - cLow)) := by ring
    _ ≤ rho * (1 / (1 - cHigh)) :=
      mul_le_mul_of_nonneg_left hinv hrho
    _ = rho / (1 - cHigh) := by ring

/-- Source aggregate applicant welfare after using the fixed capacity constraint. -/
def applicantWelfare (rho averageEffortCost : ℝ) : ℝ :=
  rho - averageEffortCost

/-- Source finite-level applicant welfare sum. -/
def finiteApplicantWelfare {ι : Type*} [Fintype ι]
    (admissionReward averageEffortCost : ι → ℝ) : ℝ :=
  ∑ i, (admissionReward i - averageEffortCost i)

theorem finiteApplicantWelfare_eq_reward_sum_sub_cost_sum
    {ι : Type*} [Fintype ι]
    (admissionReward averageEffortCost : ι → ℝ) :
    finiteApplicantWelfare admissionReward averageEffortCost =
      (∑ i, admissionReward i) - ∑ i, averageEffortCost i := by
  simp [finiteApplicantWelfare, Finset.sum_sub_distrib]

theorem finiteApplicantWelfare_le_capacity_of_nonnegative_costs
    {ι : Type*} [Fintype ι]
    {admissionReward averageEffortCost : ι → ℝ} {rho : ℝ}
    (hcapacity : (∑ i, admissionReward i) = rho)
    (hcost : ∀ i, 0 ≤ averageEffortCost i) :
    finiteApplicantWelfare admissionReward averageEffortCost ≤ rho := by
  rw [finiteApplicantWelfare_eq_reward_sum_sub_cost_sum, hcapacity]
  have hcost_sum : 0 ≤ ∑ i, averageEffortCost i :=
    Finset.sum_nonneg fun i _hi => hcost i
  linarith

theorem finiteApplicantWelfare_eq_capacity_of_zero_costs
    {ι : Type*} [Fintype ι]
    {admissionReward averageEffortCost : ι → ℝ} {rho : ℝ}
    (hcapacity : (∑ i, admissionReward i) = rho)
    (hcost_zero : ∀ i, averageEffortCost i = 0) :
    finiteApplicantWelfare admissionReward averageEffortCost = rho := by
  rw [finiteApplicantWelfare_eq_reward_sum_sub_cost_sum, hcapacity]
  have hsum_zero : (∑ i, averageEffortCost i) = 0 := by
    simp [hcost_zero]
  rw [hsum_zero, sub_zero]

theorem finiteApplicantWelfare_le_pureRandomization_of_nonnegative_costs
    {ι : Type*} [Fintype ι]
    {admissionReward averageEffortCost : ι → ℝ} {rho : ℝ}
    (hcapacity : (∑ i, admissionReward i) = rho)
    (hcost : ∀ i, 0 ≤ averageEffortCost i) :
    finiteApplicantWelfare admissionReward averageEffortCost ≤
      applicantWelfare rho 0 := by
  simp [applicantWelfare]
  exact finiteApplicantWelfare_le_capacity_of_nonnegative_costs hcapacity hcost

theorem finiteApplicantWelfare_eq_capacity_iff_all_costs_zero
    {ι : Type*} [Fintype ι]
    {admissionReward averageEffortCost : ι → ℝ} {rho : ℝ}
    (hcapacity : (∑ i, admissionReward i) = rho)
    (hcost : ∀ i, 0 ≤ averageEffortCost i) :
    finiteApplicantWelfare admissionReward averageEffortCost = rho ↔
      ∀ i, averageEffortCost i = 0 := by
  classical
  rw [finiteApplicantWelfare_eq_reward_sum_sub_cost_sum, hcapacity]
  constructor
  · intro h
    have hsum_zero : (∑ i, averageEffortCost i) = 0 := by linarith
    intro i
    exact
      (Finset.sum_eq_zero_iff_of_nonneg
        (s := Finset.univ) (f := averageEffortCost)
        (fun j _hj => hcost j)).1 hsum_zero i (Finset.mem_univ i)
  · intro hcost_zero
    have hsum_zero : (∑ i, averageEffortCost i) = 0 := by
      simp [hcost_zero]
    rw [hsum_zero, sub_zero]

theorem applicantWelfare_le_capacity_of_nonnegative_cost
    {rho averageEffortCost : ℝ} (hcost : 0 ≤ averageEffortCost) :
    applicantWelfare rho averageEffortCost ≤ rho := by
  unfold applicantWelfare
  linarith

theorem applicantWelfare_eq_capacity_of_zero_cost (rho : ℝ) :
    applicantWelfare rho 0 = rho := by
  simp [applicantWelfare]

theorem applicantWelfare_eq_capacity_iff_zero_cost
    {rho averageEffortCost : ℝ} (hcost : 0 ≤ averageEffortCost) :
    applicantWelfare rho averageEffortCost = rho ↔ averageEffortCost = 0 := by
  unfold applicantWelfare
  constructor <;> intro h <;> linarith

theorem applicantWelfare_lt_capacity_of_positive_cost
    {rho averageEffortCost : ℝ} (hcost : 0 < averageEffortCost) :
    applicantWelfare rho averageEffortCost < rho := by
  unfold applicantWelfare
  linarith

theorem applicantWelfare_le_pureRandomization_of_nonnegative_cost
    {rho averageEffortCost : ℝ} (hcost : 0 ≤ averageEffortCost) :
    applicantWelfare rho averageEffortCost ≤ applicantWelfare rho 0 := by
  unfold applicantWelfare
  linarith

theorem applicantWelfare_nonincreasing_when_cost_increases
    {rho costLow costHigh : ℝ} (hcost : costLow ≤ costHigh) :
    applicantWelfare rho costHigh ≤ applicantWelfare rho costLow := by
  unfold applicantWelfare
  linarith

/--
Closed-form two-level total effort cost for the source-family counterexample
`f(theta)=1/sqrt(1-theta^2/4)`, `g(e)=e`, and `cost(e)=e^2`.
For this family the displayed two-level effort formula gives

`rho/(1-c) * int_c^1 (f(c)/f(theta))^2 dtheta`, which reduces to this
rational expression.
-/
noncomputable def twoLevelApplicantCostCounterexample (rho c : ℝ) : ℝ :=
  rho * (((11 : ℝ) / 12 - c + c ^ 3 / 12) /
    ((1 - c) * (1 - c ^ 2 / 4)))

theorem twoLevelApplicantCostCounterexample_decreases :
    twoLevelApplicantCostCounterexample (3 / 10) (1 / 5) <
      twoLevelApplicantCostCounterexample (3 / 10) (1 / 10) := by
  norm_num [twoLevelApplicantCostCounterexample]

theorem applicantWelfare_twoLevel_monotonicity_claim_counterexample :
    (0 : ℝ) < 1 / 10 ∧
      (1 / 10 : ℝ) ≤ 1 / 5 ∧
      (1 / 5 : ℝ) ≤ 1 - 3 / 10 ∧
      applicantWelfare (3 / 10)
          (twoLevelApplicantCostCounterexample (3 / 10) (1 / 10)) <
        applicantWelfare (3 / 10)
          (twoLevelApplicantCostCounterexample (3 / 10) (1 / 5)) := by
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  · unfold applicantWelfare
    have hcost := twoLevelApplicantCostCounterexample_decreases
    linarith

/-- A compact notion of maximizing a one-dimensional objective over an interval. -/
def MaximizesOnInterval (u : ℝ → ℝ) (x lo hi : ℝ) : Prop :=
  lo ≤ x ∧ x ≤ hi ∧ ∀ y, lo ≤ y → y ≤ hi → u y ≤ u x

/--
Source reduction for Proposition 2: once two-level private utility is known to
be nondecreasing in the cutoff, the non-randomized cutoff `1 - rho` maximizes it.
-/
theorem privateUtility_maximized_at_nonrandomized_of_nondecreasing
    {rho : ℝ} {u : ℝ → ℝ}
    (hrho_le_one : rho ≤ 1)
    (hmono : ∀ c d, 0 ≤ c → c ≤ d → d ≤ 1 - rho → u c ≤ u d) :
    MaximizesOnInterval u (1 - rho) 0 (1 - rho) := by
  refine ⟨by linarith, le_rfl, ?_⟩
  intro y hy0 hyhi
  exact hmono y (1 - rho) hy0 hyhi le_rfl

/-- Reduced two-level private utility product from the source proof. -/
def twoLevelPrivateUtilityReduced
    (effortScore skillAtCutoff : ℝ → ℝ) (c : ℝ) : ℝ :=
  effortScore c * skillAtCutoff c

/--
Source two-level private-utility expression from the appendix proof:
`g(cost^{-1}(rho/(1-c))) * f(c)`.
-/
noncomputable def twoLevelPrivateUtilitySource
    (rho : ℝ) (costInv g f : ℝ → ℝ) (c : ℝ) : ℝ :=
  g (costInv (rho / (1 - c))) * f c

theorem twoLevelPrivateUtilityReduced_mono_of_mono_nonneg
    {effortScore skillAtCutoff : ℝ → ℝ}
    (heffort_mono : ∀ c d, c ≤ d → effortScore c ≤ effortScore d)
    (hskill_mono : ∀ c d, c ≤ d → skillAtCutoff c ≤ skillAtCutoff d)
    (heffort_nonneg : ∀ c, 0 ≤ effortScore c)
    (hskill_nonneg : ∀ c, 0 ≤ skillAtCutoff c) :
    ∀ c d, c ≤ d →
      twoLevelPrivateUtilityReduced effortScore skillAtCutoff c
        ≤ twoLevelPrivateUtilityReduced effortScore skillAtCutoff d := by
  intro c d hcd
  unfold twoLevelPrivateUtilityReduced
  calc
    effortScore c * skillAtCutoff c
        ≤ effortScore d * skillAtCutoff c :=
      mul_le_mul_of_nonneg_right (heffort_mono c d hcd) (hskill_nonneg c)
    _ ≤ effortScore d * skillAtCutoff d :=
      mul_le_mul_of_nonneg_left (hskill_mono c d hcd) (heffort_nonneg d)

theorem twoLevelPrivateUtilityReduced_maximized_at_nonrandomized
    {rho : ℝ} {effortScore skillAtCutoff : ℝ → ℝ}
    (hrho_le_one : rho ≤ 1)
    (heffort_mono : ∀ c d, c ≤ d → effortScore c ≤ effortScore d)
    (hskill_mono : ∀ c d, c ≤ d → skillAtCutoff c ≤ skillAtCutoff d)
    (heffort_nonneg : ∀ c, 0 ≤ effortScore c)
    (hskill_nonneg : ∀ c, 0 ≤ skillAtCutoff c) :
    MaximizesOnInterval
      (twoLevelPrivateUtilityReduced effortScore skillAtCutoff) (1 - rho) 0 (1 - rho) := by
  exact privateUtility_maximized_at_nonrandomized_of_nondecreasing
    (u := twoLevelPrivateUtilityReduced effortScore skillAtCutoff)
    hrho_le_one
    (by
      intro c d _ hcd _
      exact twoLevelPrivateUtilityReduced_mono_of_mono_nonneg
        heffort_mono hskill_mono heffort_nonneg hskill_nonneg c d hcd)

theorem twoLevelPrivateUtilitySource_maximized_at_nonrandomized
    {rho : ℝ} {costInv g f : ℝ → ℝ}
    (hrho_pos : 0 < rho)
    (hrho_le_one : rho ≤ 1)
    (hcostInv_mono : Monotone costInv)
    (hg_mono : Monotone g)
    (hf_mono : Monotone f)
    (hg_nonneg : ∀ x, 0 ≤ g x)
    (hf_nonneg : ∀ x, 0 ≤ f x) :
    MaximizesOnInterval
      (twoLevelPrivateUtilitySource rho costInv g f) (1 - rho) 0 (1 - rho) := by
  refine privateUtility_maximized_at_nonrandomized_of_nondecreasing
    (rho := rho) (u := twoLevelPrivateUtilitySource rho costInv g f)
    hrho_le_one ?_
  intro c d _hc0 hcd hdhi
  have hdenC : 0 < 1 - c := by linarith
  have hdenD : 0 < 1 - d := by linarith
  have hprob :
      rho / (1 - c) ≤ rho / (1 - d) :=
    twoLevel_highProb_mono_of_cutoff_mono
      (le_of_lt hrho_pos) hcd hdenC hdenD
  have heffort :
      g (costInv (rho / (1 - c)))
        ≤ g (costInv (rho / (1 - d))) :=
    hg_mono (hcostInv_mono hprob)
  have hskill : f c ≤ f d := hf_mono hcd
  unfold twoLevelPrivateUtilitySource
  exact mul_le_mul heffort hskill (hf_nonneg c) (hg_nonneg _)

/--
Appendix Lemma `order_p`: the two best-response inequalities in the
rank-preservation contradiction imply the ordering of effort-cost gaps.
-/
theorem reward_imitation_inequalities_imply_cost_gap_order
    {rewardLow rewardHigh costLow costLowToHigh costHigh costHighToLow : ℝ}
    (hlow_best :
      rewardLow - costLow ≥ rewardHigh - costLowToHigh)
    (hhigh_best :
      rewardHigh - costHigh ≥ rewardLow - costHighToLow) :
    costHigh - costHighToLow ≤ costLowToHigh - costLow := by
  linarith

/--
Linear-score specialization of Appendix Lemma `order_g`: for the same score
increase, the lower-skill applicant must move a larger effort distance.
-/
theorem linear_score_effort_gap_order
    {skillLow skillHigh scoreLow scoreHigh : ℝ}
    (hskillLow_pos : 0 < skillLow)
    (hskill_order : skillLow < skillHigh)
    (hscore_order : scoreLow < scoreHigh) :
    scoreHigh / skillLow - scoreLow / skillLow
      > scoreHigh / skillHigh - scoreLow / skillHigh := by
  have hskillHigh_pos : 0 < skillHigh := lt_trans hskillLow_pos hskill_order
  have hscore_gap_pos : 0 < scoreHigh - scoreLow := by linarith
  have hinv : (1 : ℝ) / skillHigh < 1 / skillLow :=
    one_div_lt_one_div_of_lt hskillLow_pos hskill_order
  have hmul :
      (scoreHigh - scoreLow) * (1 / skillHigh)
        < (scoreHigh - scoreLow) * (1 / skillLow) :=
    mul_lt_mul_of_pos_left hinv hscore_gap_pos
  field_simp [ne_of_gt hskillLow_pos, ne_of_gt hskillHigh_pos] at hmul ⊢
  nlinarith

theorem source_score_equalities_imply_transfer_increment
    {g : ℝ → ℝ}
    {skillLow skillHigh scoreLow scoreHigh : ℝ}
    {e eToHigh eHighToLow eHigh : ℝ}
    (hskillLow_pos : 0 < skillLow)
    (hskill_order : skillLow < skillHigh)
    (hscore_order : scoreLow < scoreHigh)
    (he_score : g e = scoreLow / skillHigh)
    (htoHigh_score : g eToHigh = scoreHigh / skillHigh)
    (hhighToLow_score : g eHighToLow = scoreLow / skillLow)
    (hhigh_score : g eHigh = scoreHigh / skillLow) :
    g eToHigh - g e < g eHigh - g eHighToLow := by
  have hgap :=
    linear_score_effort_gap_order hskillLow_pos hskill_order hscore_order
  rw [he_score, htoHigh_score, hhighToLow_score, hhigh_score]
  exact hgap

/--
The source proof says the two deviation efforts are ordered because `g` is
strictly increasing and the multiplicative score equations have positive
skills.  This lemma isolates that algebra so the paper-facing rank bridge does
not have to assume the effort-order inequalities separately.
-/
theorem source_multiplicative_score_equalities_imply_effort_order
    {g : ℝ → ℝ}
    {skillLow skillHigh scoreLow scoreHigh : ℝ}
    {e eToHigh eHighToLow eHigh : ℝ}
    (hg_strict : StrictMono g)
    (hskillLow_pos : 0 < skillLow)
    (hskill_order : skillLow < skillHigh)
    (hscoreLow_nonneg : 0 ≤ scoreLow)
    (hscore_order : scoreLow < scoreHigh)
    (he_score : scoreLow = g e * skillHigh)
    (htoHigh_score : scoreHigh = g eToHigh * skillHigh)
    (hhighToLow_score : scoreLow = g eHighToLow * skillLow)
    (hhigh_score : scoreHigh = g eHigh * skillLow) :
    e < eToHigh ∧ eHighToLow < eHigh ∧
      e ≤ eHighToLow ∧ eToHigh ≤ eHigh := by
  have hskillHigh_pos : 0 < skillHigh :=
    lt_trans hskillLow_pos hskill_order
  have hscoreHigh_nonneg : 0 ≤ scoreHigh :=
    le_trans hscoreLow_nonneg (le_of_lt hscore_order)
  have hlow_div_le :
      scoreLow / skillHigh ≤ scoreLow / skillLow := by
    rw [div_le_div_iff₀ hskillHigh_pos hskillLow_pos]
    exact mul_le_mul_of_nonneg_left (le_of_lt hskill_order) hscoreLow_nonneg
  have hhigh_div_le :
      scoreHigh / skillHigh ≤ scoreHigh / skillLow := by
    rw [div_le_div_iff₀ hskillHigh_pos hskillLow_pos]
    exact mul_le_mul_of_nonneg_left (le_of_lt hskill_order) hscoreHigh_nonneg
  have he_div : g e = scoreLow / skillHigh := by
    rw [he_score]
    field_simp [ne_of_gt hskillHigh_pos]
  have htoHigh_div : g eToHigh = scoreHigh / skillHigh := by
    rw [htoHigh_score]
    field_simp [ne_of_gt hskillHigh_pos]
  have hhighToLow_div : g eHighToLow = scoreLow / skillLow := by
    rw [hhighToLow_score]
    field_simp [ne_of_gt hskillLow_pos]
  have hhigh_div : g eHigh = scoreHigh / skillLow := by
    rw [hhigh_score]
    field_simp [ne_of_gt hskillLow_pos]
  have he_toHigh : e < eToHigh := by
    apply hg_strict.lt_iff_lt.mp
    rw [he_div, htoHigh_div]
    exact div_lt_div_of_pos_right hscore_order hskillHigh_pos
  have hhighToLow_high : eHighToLow < eHigh := by
    apply hg_strict.lt_iff_lt.mp
    rw [hhighToLow_div, hhigh_div]
    exact div_lt_div_of_pos_right hscore_order hskillLow_pos
  have he_highToLow : e ≤ eHighToLow := by
    apply hg_strict.le_iff_le.mp
    rw [he_div, hhighToLow_div]
    exact hlow_div_le
  have htoHigh_high : eToHigh ≤ eHigh := by
    apply hg_strict.le_iff_le.mp
    rw [htoHigh_div, hhigh_div]
    exact hhigh_div_le
  exact ⟨he_toHigh, hhighToLow_high, he_highToLow, htoHigh_high⟩

/--
Source construction of the two deviation efforts in the rank-preservation
proof.  If the actual low-reward/high-skill applicant has score `scoreLow`
and the actual high-reward/low-skill applicant has score `scoreHigh`, then
continuity and strict monotonicity of `g` provide the effort each applicant
would need to hit the other's score.
-/
theorem source_actual_scores_yield_deviation_efforts
    {g : ℝ → ℝ}
    {skillLow skillHigh scoreLow scoreHigh : ℝ}
    {e eHigh : ℝ}
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hskillLow_pos : 0 < skillLow)
    (hskill_order : skillLow < skillHigh)
    (hscoreLow_nonneg : 0 ≤ scoreLow)
    (hscore_order : scoreLow < scoreHigh)
    (he_score : scoreLow = g e * skillHigh)
    (hhigh_score : scoreHigh = g eHigh * skillLow) :
    ∃ eToHigh eHighToLow,
      scoreHigh = g eToHigh * skillHigh ∧
      scoreLow = g eHighToLow * skillLow ∧
      e < eToHigh ∧ eHighToLow < eHigh ∧
      e ≤ eHighToLow ∧ eToHigh ≤ eHigh := by
  have hskillHigh_pos : 0 < skillHigh :=
    lt_trans hskillLow_pos hskill_order
  have hscoreHigh_nonneg : 0 ≤ scoreHigh :=
    le_trans hscoreLow_nonneg (le_of_lt hscore_order)
  have he_div : g e = scoreLow / skillHigh := by
    rw [he_score]
    field_simp [ne_of_gt hskillHigh_pos]
  have hhigh_div : g eHigh = scoreHigh / skillLow := by
    rw [hhigh_score]
    field_simp [ne_of_gt hskillLow_pos]
  have he_high : e < eHigh := by
    apply hg_strict.lt_iff_lt.mp
    rw [he_div, hhigh_div]
    calc
      scoreLow / skillHigh < scoreHigh / skillHigh :=
        div_lt_div_of_pos_right hscore_order hskillHigh_pos
      _ ≤ scoreHigh / skillLow := by
        rw [div_le_div_iff₀ hskillHigh_pos hskillLow_pos]
        exact mul_le_mul_of_nonneg_left (le_of_lt hskill_order)
          hscoreHigh_nonneg
  have htarget_high_mem :
      scoreHigh / skillHigh ∈ Set.Icc (g e) (g eHigh) := by
    constructor
    · rw [he_div]
      exact div_le_div_of_nonneg_right (le_of_lt hscore_order)
        (le_of_lt hskillHigh_pos)
    · rw [hhigh_div]
      rw [div_le_div_iff₀ hskillHigh_pos hskillLow_pos]
      exact mul_le_mul_of_nonneg_left (le_of_lt hskill_order)
        hscoreHigh_nonneg
  have htarget_low_mem :
      scoreLow / skillLow ∈ Set.Icc (g e) (g eHigh) := by
    constructor
    · rw [he_div]
      rw [div_le_div_iff₀ hskillHigh_pos hskillLow_pos]
      exact mul_le_mul_of_nonneg_left (le_of_lt hskill_order)
        hscoreLow_nonneg
    · rw [hhigh_div]
      exact div_le_div_of_nonneg_right (le_of_lt hscore_order)
        (le_of_lt hskillLow_pos)
  rcases intermediate_value_Icc (le_of_lt he_high)
      hg_cont.continuousOn htarget_high_mem with
    ⟨eToHigh, heToHigh_mem, heToHigh_score_div⟩
  rcases intermediate_value_Icc (le_of_lt he_high)
      hg_cont.continuousOn htarget_low_mem with
    ⟨eHighToLow, eHighToLow_mem, hhighToLow_score_div⟩
  have htoHigh_score :
      scoreHigh = g eToHigh * skillHigh := by
    rw [heToHigh_score_div]
    field_simp [ne_of_gt hskillHigh_pos]
  have hhighToLow_score :
      scoreLow = g eHighToLow * skillLow := by
    rw [hhighToLow_score_div]
    field_simp [ne_of_gt hskillLow_pos]
  have he_toHigh : e < eToHigh := by
    apply hg_strict.lt_iff_lt.mp
    rw [he_div, heToHigh_score_div]
    exact div_lt_div_of_pos_right hscore_order hskillHigh_pos
  have hhighToLow_high : eHighToLow < eHigh := by
    apply hg_strict.lt_iff_lt.mp
    rw [hhighToLow_score_div, hhigh_div]
    exact div_lt_div_of_pos_right hscore_order hskillLow_pos
  exact ⟨eToHigh, eHighToLow, htoHigh_score, hhighToLow_score,
    he_toHigh, hhighToLow_high, eHighToLow_mem.1, heToHigh_mem.2⟩

theorem multidim_linear_effort_score_le_total_mul_max
    {ι : Type*} [Fintype ι]
    (effort weight : ι → ℝ) {total maxWeight : ℝ}
    (heffort_nonneg : ∀ i, 0 ≤ effort i)
    (hsum : ∑ i, effort i = total)
    (hweight : ∀ i, weight i ≤ maxWeight) :
    ∑ i, effort i * weight i ≤ total * maxWeight := by
  calc
    ∑ i, effort i * weight i
        ≤ ∑ i, effort i * maxWeight := by
          exact Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left (hweight i) (heffort_nonneg i)
    _ = total * maxWeight := by
          rw [← Finset.sum_mul, hsum]

theorem multidim_linear_effort_single_best_attains_total_mul_max
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (best : ι) (weight : ι → ℝ) {total maxWeight : ℝ}
    (hbest : weight best = maxWeight) :
    ∑ i, (if i = best then total else 0) * weight i = total * maxWeight := by
  simp [hbest]

theorem multidim_linear_effort_best_coordinate_exists
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (weight : ι → ℝ) (total : ℝ) :
    ∃ best : ι, ∃ maxWeight : ℝ,
      weight best = maxWeight ∧
      (∀ i, weight i ≤ maxWeight) ∧
      (∀ effort : ι → ℝ,
          (∀ i, 0 ≤ effort i) →
          (∑ i, effort i = total) →
          ∑ i, effort i * weight i ≤ total * maxWeight)
      ∧ ∑ i, (if i = best then total else 0) * weight i = total * maxWeight := by
  classical
  rcases Finset.exists_max_image (Finset.univ : Finset ι) weight
      Finset.univ_nonempty with ⟨best, _hbest_mem, hmax⟩
  refine ⟨best, weight best, rfl, ?_, ?_, ?_⟩
  · intro i
    exact hmax i (Finset.mem_univ i)
  · intro effort heffort hsum
    exact multidim_linear_effort_score_le_total_mul_max
      effort weight heffort hsum (fun i => hmax i (Finset.mem_univ i))
  · exact multidim_linear_effort_single_best_attains_total_mul_max
      best weight rfl

theorem multidim_linear_scaled_effort_best_coordinate_exists
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (h total : ℝ) (weight : ι → ℝ) (hh_nonneg : 0 ≤ h) :
    ∃ best : ι, ∃ maxWeight : ℝ,
      weight best = maxWeight ∧
      (∀ i, weight i ≤ maxWeight) ∧
      (∀ effort : ι → ℝ,
          (∀ i, 0 ≤ effort i) →
          (∑ i, effort i = total) →
          h * (∑ i, effort i * weight i) ≤ h * total * maxWeight)
      ∧ h * (∑ i, (if i = best then total else 0) * weight i)
          = h * total * maxWeight := by
  rcases multidim_linear_effort_best_coordinate_exists weight total with
    ⟨best, maxWeight, hbest, hmax, hbound, hattain⟩
  refine ⟨best, maxWeight, hbest, hmax, ?_, ?_⟩
  · intro effort heffort hsum
    have hle : ∑ i, effort i * weight i ≤ total * maxWeight :=
      hbound effort heffort hsum
    have hscaled : h * (∑ i, effort i * weight i) ≤ h * (total * maxWeight) :=
      mul_le_mul_of_nonneg_left hle hh_nonneg
    simpa [mul_assoc] using hscaled
  · rw [hattain]
    ring

/--
With fixed total effort, linear transfer, and a monotone reward in the weighted
score, allocating all effort to a coordinate with maximal weighted skill
coefficient maximizes applicant payoff among allocations with the same total
effort cost.
-/
theorem multidim_linear_effort_single_best_maximizes_fixed_total_payoff
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (h total : ℝ) (weight : ι → ℝ) (reward : ℝ → ℝ) (costOfTotal : ℝ)
    (hh_nonneg : 0 ≤ h) (hreward_mono : Monotone reward) :
    ∃ best : ι, ∃ maxWeight : ℝ,
      weight best = maxWeight ∧
      (∀ i, weight i ≤ maxWeight) ∧
      (∀ effort : ι → ℝ,
          (∀ i, 0 ≤ effort i) →
          (∑ i, effort i = total) →
          reward (h * (∑ i, effort i * weight i)) - costOfTotal
            ≤ reward (h * total * maxWeight) - costOfTotal)
      ∧ reward (h * (∑ i, (if i = best then total else 0) * weight i)) - costOfTotal
          = reward (h * total * maxWeight) - costOfTotal := by
  rcases multidim_linear_scaled_effort_best_coordinate_exists
      h total weight hh_nonneg with
    ⟨best, maxWeight, hbest, hmax, hbound, hattain⟩
  refine ⟨best, maxWeight, hbest, hmax, ?_, ?_⟩
  · intro effort heffort hsum
    have hle := hbound effort heffort hsum
    have hreward := hreward_mono hle
    linarith
  · rw [hattain]

/--
Source `prop:linearg` score identity after the fixed-budget reduction.  If an
applicant puts the whole fixed effort budget on a coordinate attaining the
combined pre-effort index, then the linear weighted score is exactly
`h * total * combinedIndex`.
-/
theorem multidim_linear_fixed_budget_best_coordinate_score_eq
    {α ι : Type*} [Fintype ι] [DecidableEq ι]
    (h total : ℝ) (best : α → ι)
    (weight effortBySkill : α → ι → ℝ)
    (combinedIndex score : α → ℝ)
    (hbest : ∀ x, weight x (best x) = combinedIndex x)
    (heffort :
      ∀ x i, effortBySkill x i = if i = best x then total else 0)
    (hscore :
      ∀ x, score x = h * ∑ i, effortBySkill x i * weight x i) :
    ∀ x, score x = h * total * combinedIndex x := by
  intro x
  rw [hscore x]
  have hsum :
      ∑ i, effortBySkill x i * weight x i =
        total * combinedIndex x := by
    calc
      ∑ i, effortBySkill x i * weight x i
          = ∑ i, (if i = best x then total else 0) * weight x i := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [heffort x i]
      _ = total * combinedIndex x := by
            simpa [hbest x] using
              multidim_linear_effort_single_best_attains_total_mul_max
                (best x) (weight x) (total := total)
                (maxWeight := combinedIndex x) (hbest x)
  rw [hsum]
  ring

/--
Source `prop:linearg` order step: once the fixed-budget linear score has
reduced to a nonnegative scalar multiple of the combined pre-effort index,
combined-index order implies realized weighted-score order.
-/
theorem multidim_linear_fixed_budget_score_mono_of_combined_index
    {α : Type*} {h total : ℝ} {combinedIndex score : α → ℝ}
    (hscale_nonneg : 0 ≤ h * total)
    (hscore : ∀ x, score x = h * total * combinedIndex x) :
    ∀ x y, combinedIndex y ≤ combinedIndex x → score y ≤ score x := by
  intro x y hindex
  rw [hscore y, hscore x]
  exact mul_le_mul_of_nonneg_left hindex hscale_nonneg

theorem concave_increasing_increment_le_of_shifted_shorter_interval
    {g : ℝ → ℝ} {a b c d : ℝ}
    (hconc : ConcaveOn ℝ Set.univ g)
    (hmono : Monotone g)
    (hab : a < b)
    (hcd : c < d)
    (hac : a ≤ c)
    (hbd : b ≤ d)
    (hlen : d - c ≤ b - a) :
    g d - g c ≤ g b - g a := by
  have had : a < d := lt_of_le_of_lt hac hcd
  have hanti_d := hconc.slope_anti (x := d) (by simp : d ∈ Set.univ)
  have hslope_right_le_ad : slope g c d ≤ slope g a d := by
    have hs : slope g d c ≤ slope g d a :=
      hanti_d
        (by simp [ne_of_lt had] : a ∈ Set.univ \ {d})
        (by simp [ne_of_lt hcd] : c ∈ Set.univ \ {d})
        hac
    simpa [slope_comm] using hs
  have hanti_a := hconc.antitoneOn_slope_gt (x := a) (by simp : a ∈ Set.univ)
  have hslope_ad_le_left : slope g a d ≤ slope g a b := by
    have hs : slope g a d ≤ slope g a b :=
      hanti_a
        (by simp [hab] : b ∈ {y | y ∈ Set.univ ∧ a < y})
        (by simp [had] : d ∈ {y | y ∈ Set.univ ∧ a < y})
        hbd
    exact hs
  have hslope : slope g c d ≤ slope g a b :=
    le_trans hslope_right_le_ad hslope_ad_le_left
  have hlen_nonneg : 0 ≤ d - c := by linarith
  have hleft :
      (d - c) * slope g c d ≤ (d - c) * slope g a b :=
    mul_le_mul_of_nonneg_left hslope hlen_nonneg
  have hslope_nonneg : 0 ≤ slope g a b := by
    rw [slope_def_field]
    exact div_nonneg (sub_nonneg.mpr (hmono hab.le)) (sub_nonneg.mpr hab.le)
  have hright :
      (d - c) * slope g a b ≤ (b - a) * slope g a b :=
    mul_le_mul_of_nonneg_right hlen hslope_nonneg
  have hleft_eq : (d - c) * slope g c d = g d - g c := by
    rw [slope_def_field]
    field_simp [sub_ne_zero.mpr hcd.ne']
  have hright_eq : (b - a) * slope g a b = g b - g a := by
    rw [slope_def_field]
    field_simp [sub_ne_zero.mpr hab.ne']
  calc
    g d - g c = (d - c) * slope g c d := hleft_eq.symm
    _ ≤ (d - c) * slope g a b := hleft
    _ ≤ (b - a) * slope g a b := hright
    _ = g b - g a := hright_eq

theorem concave_increasing_larger_increment_implies_larger_interval
    {g : ℝ → ℝ} {a b c d : ℝ}
    (hconc : ConcaveOn ℝ Set.univ g)
    (hmono : Monotone g)
    (hab : a < b)
    (hcd : c < d)
    (hac : a ≤ c)
    (hbd : b ≤ d)
    (hinc : g b - g a < g d - g c) :
    b - a < d - c := by
  by_contra hnot
  have hlen : d - c ≤ b - a := le_of_not_gt hnot
  have hle :=
    concave_increasing_increment_le_of_shifted_shorter_interval
      hconc hmono hab hcd hac hbd hlen
  exact not_lt_of_ge hle hinc

theorem order_g_from_source_score_equalities
    {g : ℝ → ℝ}
    {skillLow skillHigh scoreLow scoreHigh : ℝ}
    {e eToHigh eHighToLow eHigh : ℝ}
    (hconc : ConcaveOn ℝ Set.univ g)
    (hmono : Monotone g)
    (hskillLow_pos : 0 < skillLow)
    (hskill_order : skillLow < skillHigh)
    (hscore_order : scoreLow < scoreHigh)
    (he_score : g e = scoreLow / skillHigh)
    (htoHigh_score : g eToHigh = scoreHigh / skillHigh)
    (hhighToLow_score : g eHighToLow = scoreLow / skillLow)
    (hhigh_score : g eHigh = scoreHigh / skillLow)
    (he_toHigh : e < eToHigh)
    (hhighToLow_high : eHighToLow < eHigh)
    (he_highToLow : e ≤ eHighToLow)
    (htoHigh_high : eToHigh ≤ eHigh) :
    eToHigh - e < eHigh - eHighToLow := by
  have hinc :
      g eToHigh - g e < g eHigh - g eHighToLow :=
    source_score_equalities_imply_transfer_increment
      hskillLow_pos hskill_order hscore_order he_score htoHigh_score
      hhighToLow_score hhigh_score
  exact concave_increasing_larger_increment_implies_larger_interval
    hconc hmono he_toHigh hhighToLow_high he_highToLow htoHigh_high hinc

/--
Multiplicative-score version of Appendix Lemma `order_g`: when a high-skill
applicant moves from `scoreLow` to `scoreHigh`, and the corresponding
low-skill boundary applicant moves between the same two scores, concavity of
`g` makes the high-skill effort interval strictly shorter.
-/
theorem source_multiplicative_score_equalities_imply_effort_interval_order
    {g : ℝ → ℝ}
    {skillLow skillHigh scoreLow scoreHigh : ℝ}
    {e eToHigh eHighToLow eHigh : ℝ}
    (hconc : ConcaveOn ℝ Set.univ g)
    (hmono : Monotone g)
    (hg_strict : StrictMono g)
    (hskillLow_pos : 0 < skillLow)
    (hskill_order : skillLow < skillHigh)
    (hscoreLow_nonneg : 0 ≤ scoreLow)
    (hscore_order : scoreLow < scoreHigh)
    (he_score : scoreLow = g e * skillHigh)
    (htoHigh_score : scoreHigh = g eToHigh * skillHigh)
    (hhighToLow_score : scoreLow = g eHighToLow * skillLow)
    (hhigh_score : scoreHigh = g eHigh * skillLow) :
    eToHigh - e < eHigh - eHighToLow := by
  have hskillHigh_pos : 0 < skillHigh :=
    lt_trans hskillLow_pos hskill_order
  have horder :=
    source_multiplicative_score_equalities_imply_effort_order
      hg_strict hskillLow_pos hskill_order hscoreLow_nonneg hscore_order
      he_score htoHigh_score hhighToLow_score hhigh_score
  have he_div : g e = scoreLow / skillHigh := by
    rw [he_score]
    field_simp [ne_of_gt hskillHigh_pos]
  have htoHigh_div : g eToHigh = scoreHigh / skillHigh := by
    rw [htoHigh_score]
    field_simp [ne_of_gt hskillHigh_pos]
  have hhighToLow_div : g eHighToLow = scoreLow / skillLow := by
    rw [hhighToLow_score]
    field_simp [ne_of_gt hskillLow_pos]
  have hhigh_div : g eHigh = scoreHigh / skillLow := by
    rw [hhigh_score]
    field_simp [ne_of_gt hskillLow_pos]
  exact
    order_g_from_source_score_equalities
      hconc hmono hskillLow_pos hskill_order hscore_order
      he_div htoHigh_div hhighToLow_div hhigh_div
      horder.1 horder.2.1 horder.2.2.1 horder.2.2.2

theorem convex_strictMono_increment_lt_of_shifted_longer_interval
    {cost : ℝ → ℝ} {e0 a b c d : ℝ}
    (hconv : ConvexOn ℝ (Set.Ici e0) cost)
    (hstrict : StrictMonoOn cost (Set.Ici e0))
    (ha : e0 ≤ a)
    (hab : a < b)
    (hcd : c < d)
    (hac : a ≤ c)
    (hbd : b ≤ d)
    (hlen : b - a < d - c) :
    cost b - cost a < cost d - cost c := by
  have hb : e0 ≤ b := le_trans ha hab.le
  have hc : e0 ≤ c := le_trans ha hac
  have hd : e0 ≤ d := le_trans hc hcd.le
  have had : a < d := lt_of_le_of_lt hac hcd
  have hslope_ab_le_ad : slope cost a b ≤ slope cost a d := by
    exact hconv.slope_mono
      (by simpa : a ∈ Set.Ici e0)
      (by simp [hb, hab.ne'] : b ∈ Set.Ici e0 \ {a})
      (by simp [hd, had.ne'] : d ∈ Set.Ici e0 \ {a})
      hbd
  have hslope_ad_le_cd : slope cost a d ≤ slope cost c d := by
    have hs := hconv.slope_mono
      (x := d)
      (by simpa : d ∈ Set.Ici e0)
      (by simp [ha, had.ne] : a ∈ Set.Ici e0 \ {d})
      (by simp [hc, hcd.ne] : c ∈ Set.Ici e0 \ {d})
      hac
    simpa [slope_comm] using hs
  have hslope : slope cost a b ≤ slope cost c d :=
    le_trans hslope_ab_le_ad hslope_ad_le_cd
  have hlen_left_nonneg : 0 ≤ b - a := by linarith
  have hleft :
      (b - a) * slope cost a b ≤ (b - a) * slope cost c d :=
    mul_le_mul_of_nonneg_left hslope hlen_left_nonneg
  have hcost_cd : cost c < cost d :=
    hstrict (by simpa : c ∈ Set.Ici e0) (by simpa : d ∈ Set.Ici e0) hcd
  have hslope_pos : 0 < slope cost c d := by
    rw [slope_def_field]
    exact div_pos (sub_pos.mpr hcost_cd) (sub_pos.mpr hcd)
  have hright :
      (b - a) * slope cost c d < (d - c) * slope cost c d :=
    mul_lt_mul_of_pos_right hlen hslope_pos
  have hleft_eq : (b - a) * slope cost a b = cost b - cost a := by
    rw [slope_def_field]
    field_simp [sub_ne_zero.mpr hab.ne']
  have hright_eq : (d - c) * slope cost c d = cost d - cost c := by
    rw [slope_def_field]
    field_simp [sub_ne_zero.mpr hcd.ne']
  calc
    cost b - cost a = (b - a) * slope cost a b := hleft_eq.symm
    _ ≤ (b - a) * slope cost c d := hleft
    _ < (d - c) * slope cost c d := hright
    _ = cost d - cost c := hright_eq

theorem convex_increasing_increment_le_of_shifted_longer_interval
    {f : ℝ → ℝ} {a b c d : ℝ}
    (hconv : ConvexOn ℝ Set.univ f)
    (hmono : Monotone f)
    (hab : a < b)
    (hcd : c < d)
    (hac : a ≤ c)
    (hbd : b ≤ d)
    (hlen : b - a ≤ d - c) :
    f b - f a ≤ f d - f c := by
  have had : a < d := lt_of_le_of_lt hac hcd
  have hslope_ab_le_ad : slope f a b ≤ slope f a d := by
    exact hconv.slope_mono
      (by simp : a ∈ Set.univ)
      (by simp [hab.ne'] : b ∈ Set.univ \ {a})
      (by simp [had.ne'] : d ∈ Set.univ \ {a})
      hbd
  have hslope_ad_le_cd : slope f a d ≤ slope f c d := by
    have hs := hconv.slope_mono
      (x := d)
      (by simp : d ∈ Set.univ)
      (by simp [had.ne] : a ∈ Set.univ \ {d})
      (by simp [hcd.ne] : c ∈ Set.univ \ {d})
      hac
    simpa [slope_comm] using hs
  have hslope : slope f a b ≤ slope f c d :=
    le_trans hslope_ab_le_ad hslope_ad_le_cd
  have hlen_left_nonneg : 0 ≤ b - a := by linarith
  have hleft :
      (b - a) * slope f a b ≤ (b - a) * slope f c d :=
    mul_le_mul_of_nonneg_left hslope hlen_left_nonneg
  have hslope_nonneg : 0 ≤ slope f c d := by
    rw [slope_def_field]
    exact div_nonneg (sub_nonneg.mpr (hmono hcd.le)) (sub_nonneg.mpr hcd.le)
  have hright :
      (b - a) * slope f c d ≤ (d - c) * slope f c d :=
    mul_le_mul_of_nonneg_right hlen hslope_nonneg
  have hleft_eq : (b - a) * slope f a b = f b - f a := by
    rw [slope_def_field]
    field_simp [sub_ne_zero.mpr hab.ne']
  have hright_eq : (d - c) * slope f c d = f d - f c := by
    rw [slope_def_field]
    field_simp [sub_ne_zero.mpr hcd.ne']
  calc
    f b - f a = (b - a) * slope f a b := hleft_eq.symm
    _ ≤ (b - a) * slope f c d := hleft
    _ ≤ (d - c) * slope f c d := hright
    _ = f d - f c := hright_eq

theorem convex_increasing_scaled_gap_mono
    {f : ℝ → ℝ} {alpha beta x y : ℝ}
    (hconv : ConvexOn ℝ Set.univ f)
    (hmono : Monotone f)
    (halpha_nonneg : 0 ≤ alpha)
    (hscale_order : alpha ≤ beta)
    (hx_nonneg : 0 ≤ x)
    (hxy : x ≤ y) :
    f (beta * x) - f (alpha * x)
      ≤ f (beta * y) - f (alpha * y) := by
  have hbeta_nonneg : 0 ≤ beta := le_trans halpha_nonneg hscale_order
  by_cases hscale_eq : alpha = beta
  · subst beta
    simp
  have hscale_lt : alpha < beta := lt_of_le_of_ne hscale_order hscale_eq
  by_cases hx_zero : x = 0
  · subst x
    have hy_nonneg : 0 ≤ y := by simpa using hxy
    have harg : alpha * y ≤ beta * y :=
      mul_le_mul_of_nonneg_right hscale_order hy_nonneg
    have hnonneg : 0 ≤ f (beta * y) - f (alpha * y) :=
      sub_nonneg.mpr (hmono harg)
    have hzero : f (beta * 0) - f (alpha * 0) = 0 := by ring_nf
    simpa [hzero] using hnonneg
  by_cases hxy_eq : x = y
  · subst y
    rfl
  have hx_pos : 0 < x := lt_of_le_of_ne hx_nonneg (Ne.symm hx_zero)
  have hxy_lt : x < y := lt_of_le_of_ne hxy hxy_eq
  have hy_pos : 0 < y := lt_trans hx_pos hxy_lt
  have hab : alpha * x < beta * x :=
    mul_lt_mul_of_pos_right hscale_lt hx_pos
  have hcd : alpha * y < beta * y :=
    mul_lt_mul_of_pos_right hscale_lt hy_pos
  have hac : alpha * x ≤ alpha * y :=
    mul_le_mul_of_nonneg_left hxy halpha_nonneg
  have hbd : beta * x ≤ beta * y :=
    mul_le_mul_of_nonneg_left hxy hbeta_nonneg
  have hscale_nonneg : 0 ≤ beta - alpha := sub_nonneg.mpr hscale_order
  have hlen_mul : (beta - alpha) * x ≤ (beta - alpha) * y :=
    mul_le_mul_of_nonneg_left hxy hscale_nonneg
  have hlen : beta * x - alpha * x ≤ beta * y - alpha * y := by
    nlinarith
  exact convex_increasing_increment_le_of_shifted_longer_interval
    hconv hmono hab hcd hac hbd hlen

theorem rank_preservation_cost_gap_contradiction
    {cost : ℝ → ℝ} {e0 a b c d : ℝ}
    (hconv : ConvexOn ℝ (Set.Ici e0) cost)
    (hstrict : StrictMonoOn cost (Set.Ici e0))
    (ha : e0 ≤ a)
    (hab : a < b)
    (hcd : c < d)
    (hac : a ≤ c)
    (hbd : b ≤ d)
    (hlen : b - a < d - c)
    (hcost_gap : cost d - cost c ≤ cost b - cost a) :
    False := by
  have hlt :=
    convex_strictMono_increment_lt_of_shifted_longer_interval
      hconv hstrict ha hab hcd hac hbd hlen
  exact not_lt_of_ge hcost_gap hlt

theorem rank_preservation_no_inversion_algebra_contradiction
    {cost g : ℝ → ℝ} {e0 e eToHigh eHighToLow eHigh rewardLow rewardHigh : ℝ}
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_mono : Monotone g)
    (he0 : e0 ≤ e)
    (he_toHigh : e < eToHigh)
    (hhighToLow_high : eHighToLow < eHigh)
    (he_highToLow : e ≤ eHighToLow)
    (htoHigh_high : eToHigh ≤ eHigh)
    (hg_increment :
      g eToHigh - g e < g eHigh - g eHighToLow)
    (hlow_best :
      rewardLow - cost e ≥ rewardHigh - cost eToHigh)
    (hhigh_best :
      rewardHigh - cost eHigh ≥ rewardLow - cost eHighToLow) :
    False := by
  have hcost_gap :
      cost eHigh - cost eHighToLow ≤ cost eToHigh - cost e :=
    reward_imitation_inequalities_imply_cost_gap_order
      hlow_best hhigh_best
  have hlen :
      eToHigh - e < eHigh - eHighToLow :=
    concave_increasing_larger_increment_implies_larger_interval
      hg_conc hg_mono he_toHigh hhighToLow_high
      he_highToLow htoHigh_high hg_increment
  exact rank_preservation_cost_gap_contradiction
    hcost_conv hcost_strict he0 he_toHigh hhighToLow_high
    he_highToLow htoHigh_high hlen hcost_gap

theorem rank_preservation_no_inversion_source_score_contradiction
    {cost g : ℝ → ℝ}
    {skillLow skillHigh scoreLow scoreHigh : ℝ}
    {e0 e eToHigh eHighToLow eHigh rewardLow rewardHigh : ℝ}
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_mono : Monotone g)
    (hskillLow_pos : 0 < skillLow)
    (hskill_order : skillLow < skillHigh)
    (hscore_order : scoreLow < scoreHigh)
    (he_score : g e = scoreLow / skillHigh)
    (htoHigh_score : g eToHigh = scoreHigh / skillHigh)
    (hhighToLow_score : g eHighToLow = scoreLow / skillLow)
    (hhigh_score : g eHigh = scoreHigh / skillLow)
    (he0 : e0 ≤ e)
    (he_toHigh : e < eToHigh)
    (hhighToLow_high : eHighToLow < eHigh)
    (he_highToLow : e ≤ eHighToLow)
    (htoHigh_high : eToHigh ≤ eHigh)
    (hlow_best :
      rewardLow - cost e ≥ rewardHigh - cost eToHigh)
    (hhigh_best :
      rewardHigh - cost eHigh ≥ rewardLow - cost eHighToLow) :
    False := by
  have hinc :
      g eToHigh - g e < g eHigh - g eHighToLow :=
    source_score_equalities_imply_transfer_increment
      hskillLow_pos hskill_order hscore_order he_score htoHigh_score
      hhighToLow_score hhigh_score
  exact rank_preservation_no_inversion_algebra_contradiction
    hcost_conv hcost_strict hg_conc hg_mono he0 he_toHigh
    hhighToLow_high he_highToLow htoHigh_high hinc hlow_best hhigh_best

/--
Analytic core of the tie-breaking lemma: if moving by an arbitrarily small
positive effort amount would obtain a strictly higher reward, continuity of the
cost at the current effort contradicts best response.
-/
theorem no_best_response_when_arbitrarily_small_increase_gets_higher_reward
    {cost : ℝ → ℝ} {effort stayReward devReward : ℝ}
    (hcost_cont : ContinuousAt cost effort)
    (hreward : stayReward < devReward)
    (hbest :
      ∀ eps, 0 < eps →
        devReward - cost (effort + eps) ≤ stayReward - cost effort) :
    False := by
  have hgap_pos : 0 < devReward - stayReward := by linarith
  rcases (Metric.continuousAt_iff.mp hcost_cont)
      (devReward - stayReward) hgap_pos with
    ⟨delta, hdelta_pos, hdelta⟩
  let eps := delta / 2
  have heps_pos : 0 < eps := by positivity
  have hdist : dist (effort + eps) effort < delta := by
    have heps_lt : eps < delta := by
      dsimp [eps]
      linarith
    simpa [Real.dist_eq, abs_of_pos heps_pos] using heps_lt
  have hnear :
      dist (cost (effort + eps)) (cost effort) < devReward - stayReward :=
    hdelta hdist
  have hcost_lt : cost (effort + eps) - cost effort < devReward - stayReward := by
    have habs :
        |cost (effort + eps) - cost effort| < devReward - stayReward := by
      simpa [Real.dist_eq, abs_sub_comm] using hnear
    exact lt_of_le_of_lt (le_abs_self _) habs
  have hprofitable :
      stayReward - cost effort < devReward - cost (effort + eps) := by
    linarith
  exact not_lt_of_ge (hbest eps heps_pos) hprofitable

/--
Source-shaped tie-breaking lemma.  If applicant `y` has the same realized score
as applicant `x` but a strictly higher reward, and every positive effort bump
by `x` reaches at least `y`'s reward level, then `x` cannot be a best response.
The strict score increase after an effort bump is derived from the
multiplicative score formula, positive skill, and strict monotonicity of `g`.
-/
theorem tied_score_higher_reward_contradicts_source_best_response
    {α : Type*} {cost g : ℝ → ℝ}
    {rankOfEffort : α → ℝ → ℝ} {rankLevel : ℝ → ℕ}
    {levelReward : ℕ → ℝ} {skill score effort : α → ℝ}
    {x y : α}
    (hcost_cont : ContinuousAt cost (effort x))
    (hg_strict : StrictMono g)
    (hskill_pos : 0 < skill x)
    (hscore_eq : ∀ z, score z = g (effort z) * skill z)
    (hsame_score : score x = score y)
    (hdeviation_reaches_y_reward :
      ∀ d, score y < g d * skill x →
        levelReward (rankLevel (rankOfEffort y (effort y))) ≤
          levelReward (rankLevel (rankOfEffort x d)))
    (hbest_x :
      ∀ d,
        levelReward (rankLevel (rankOfEffort x d)) - cost d ≤
          levelReward (rankLevel (rankOfEffort x (effort x))) - cost (effort x))
    (hreward :
      levelReward (rankLevel (rankOfEffort x (effort x))) <
        levelReward (rankLevel (rankOfEffort y (effort y)))) :
    False := by
  refine no_best_response_when_arbitrarily_small_increase_gets_higher_reward
    hcost_cont hreward ?_
  intro eps heps
  have heff_lt : effort x < effort x + eps := by linarith
  have hg_lt : g (effort x) < g (effort x + eps) :=
    hg_strict heff_lt
  have hscore_bump :
      score y < g (effort x + eps) * skill x := by
    rw [← hsame_score, hscore_eq x]
    exact mul_lt_mul_of_pos_right hg_lt hskill_pos
  have hdev_reward :=
    hdeviation_reaches_y_reward (effort x + eps) hscore_bump
  have hbest := hbest_x (effort x + eps)
  linarith

/--
Variant of the source tie-breaking lemma where the reward comparison after an
effort bump is derived from monotonicity of reward levels.
-/
theorem tied_score_higher_reward_contradicts_source_best_response_of_level_mono
    {α : Type*} {cost g : ℝ → ℝ}
    {rankOfEffort : α → ℝ → ℝ} {rankLevel : ℝ → ℕ}
    {levelReward : ℕ → ℝ} {skill score effort : α → ℝ}
    {x y : α}
    (hcost_cont : ContinuousAt cost (effort x))
    (hg_strict : StrictMono g)
    (hskill_pos : 0 < skill x)
    (hscore_eq : ∀ z, score z = g (effort z) * skill z)
    (hsame_score : score x = score y)
    (hlevelReward_mono : Monotone levelReward)
    (hdeviation_reaches_y_level :
      ∀ d, score y < g d * skill x →
        rankLevel (rankOfEffort y (effort y)) ≤
          rankLevel (rankOfEffort x d))
    (hbest_x :
      ∀ d,
        levelReward (rankLevel (rankOfEffort x d)) - cost d ≤
          levelReward (rankLevel (rankOfEffort x (effort x))) - cost (effort x))
    (hreward :
      levelReward (rankLevel (rankOfEffort x (effort x))) <
        levelReward (rankLevel (rankOfEffort y (effort y)))) :
    False :=
  tied_score_higher_reward_contradicts_source_best_response
    hcost_cont hg_strict hskill_pos hscore_eq hsame_score
    (fun d hscore => hlevelReward_mono
      (hdeviation_reaches_y_level d hscore))
    hbest_x hreward

/--
Direct equality form of the source tie-breaking lemma.  If two applicants have
the same realized score, each can reach the other's reward level after any
positive score bump, and both are best responding, then the two tied
applicants must receive the same reward.  This is the usable form for proving
that score atoms do not cross reward-level boundaries.
-/
theorem tied_score_rewards_eq_of_source_best_response
    {α : Type*} {cost g : ℝ → ℝ}
    {rankOfEffort : α → ℝ → ℝ} {rankLevel : ℝ → ℕ}
    {levelReward : ℕ → ℝ} {skill score effort : α → ℝ}
    {x y : α}
    (hcost_cont_x : ContinuousAt cost (effort x))
    (hcost_cont_y : ContinuousAt cost (effort y))
    (hg_strict : StrictMono g)
    (hskill_pos_x : 0 < skill x)
    (hskill_pos_y : 0 < skill y)
    (hscore_eq : ∀ z, score z = g (effort z) * skill z)
    (hsame_score : score x = score y)
    (hdeviation_x_reaches_y_reward :
      ∀ d, score y < g d * skill x →
        levelReward (rankLevel (rankOfEffort y (effort y))) ≤
          levelReward (rankLevel (rankOfEffort x d)))
    (hdeviation_y_reaches_x_reward :
      ∀ d, score x < g d * skill y →
        levelReward (rankLevel (rankOfEffort x (effort x))) ≤
          levelReward (rankLevel (rankOfEffort y d)))
    (hbest_x :
      ∀ d,
        levelReward (rankLevel (rankOfEffort x d)) - cost d ≤
          levelReward (rankLevel (rankOfEffort x (effort x))) - cost (effort x))
    (hbest_y :
      ∀ d,
        levelReward (rankLevel (rankOfEffort y d)) - cost d ≤
          levelReward (rankLevel (rankOfEffort y (effort y))) - cost (effort y)) :
    levelReward (rankLevel (rankOfEffort x (effort x))) =
      levelReward (rankLevel (rankOfEffort y (effort y))) := by
  apply le_antisymm
  · exact le_of_not_gt (fun hyx =>
      tied_score_higher_reward_contradicts_source_best_response
        hcost_cont_y hg_strict hskill_pos_y hscore_eq hsame_score.symm
        hdeviation_y_reaches_x_reward hbest_y hyx)
  · exact le_of_not_gt (fun hxy =>
      tied_score_higher_reward_contradicts_source_best_response
        hcost_cont_x hg_strict hskill_pos_x hscore_eq hsame_score
        hdeviation_x_reaches_y_reward hbest_x hxy)

/--
Rank-level form of the source tie-breaking lemma.  The paper's reward levels
are distinct; under that injectivity, the reward equality from
`tied_score_rewards_eq_of_source_best_response` implies equality of the
realized post-rank levels for tied actual scores.  This is the source-facing
replacement for assuming equal-score level equality at actual equilibrium
scores.
-/
theorem tied_score_actual_rank_levels_eq_of_source_best_response
    {α : Type*} {cost g : ℝ → ℝ}
    {rankOfEffort : α → ℝ → ℝ} {postRank : α → ℝ}
    {rankLevel : ℝ → ℕ}
    {levelReward : ℕ → ℝ} {skill score effort : α → ℝ}
    {x y : α}
    (hlevelReward_inj : Function.Injective levelReward)
    (hpost_actual_x :
      rankLevel (rankOfEffort x (effort x)) = rankLevel (postRank x))
    (hpost_actual_y :
      rankLevel (rankOfEffort y (effort y)) = rankLevel (postRank y))
    (hcost_cont_x : ContinuousAt cost (effort x))
    (hcost_cont_y : ContinuousAt cost (effort y))
    (hg_strict : StrictMono g)
    (hskill_pos_x : 0 < skill x)
    (hskill_pos_y : 0 < skill y)
    (hscore_eq : ∀ z, score z = g (effort z) * skill z)
    (hsame_score : score x = score y)
    (hdeviation_x_reaches_y_reward :
      ∀ d, score y < g d * skill x →
        levelReward (rankLevel (rankOfEffort y (effort y))) ≤
          levelReward (rankLevel (rankOfEffort x d)))
    (hdeviation_y_reaches_x_reward :
      ∀ d, score x < g d * skill y →
        levelReward (rankLevel (rankOfEffort x (effort x))) ≤
          levelReward (rankLevel (rankOfEffort y d)))
    (hbest_x :
      ∀ d,
        levelReward (rankLevel (rankOfEffort x d)) - cost d ≤
          levelReward (rankLevel (rankOfEffort x (effort x))) - cost (effort x))
    (hbest_y :
      ∀ d,
        levelReward (rankLevel (rankOfEffort y d)) - cost d ≤
          levelReward (rankLevel (rankOfEffort y (effort y))) - cost (effort y)) :
    rankLevel (postRank x) = rankLevel (postRank y) := by
  apply hlevelReward_inj
  have hreward :=
    tied_score_rewards_eq_of_source_best_response
      hcost_cont_x hcost_cont_y hg_strict hskill_pos_x hskill_pos_y
      hscore_eq hsame_score hdeviation_x_reaches_y_reward
      hdeviation_y_reaches_x_reward hbest_x hbest_y
  simpa [hpost_actual_x, hpost_actual_y] using hreward

theorem measure_zero_deviations_preserve_score_distribution
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {score deviatedScore : α → β}
    (hscore : score =ᵐ[μ] deviatedScore) :
    Measure.map score μ = Measure.map deviatedScore μ :=
  Measure.map_congr hscore

theorem binary_reward_preserved_of_no_inversion_and_equal_count
    {α : Type*} [Fintype α] [DecidableEq α]
    (preHigh postHigh : α → Prop)
    [DecidablePred preHigh] [DecidablePred postHigh]
    (hNoInv :
      ∀ i j, preHigh i → ¬ preHigh j → ¬ postHigh i → postHigh j → False)
    (hcount :
      (Finset.univ.filter preHigh).card =
        (Finset.univ.filter postHigh).card) :
    ∀ i, postHigh i ↔ preHigh i := by
  classical
  let S : Finset α := Finset.univ.filter preHigh
  let T : Finset α := Finset.univ.filter postHigh
  have hcountST : S.card = T.card := by simpa [S, T] using hcount
  intro i
  constructor
  · intro hpost_i
    by_contra hpre_i_not
    have hiT : i ∈ T := by simp [T, hpost_i]
    have hsub : S ⊆ T.erase i := by
      intro x hxS
      have hpre_x : preHigh x := by simpa [S] using hxS
      have hpost_x : postHigh x := by
        by_contra hpost_x_not
        exact hNoInv x i hpre_x hpre_i_not hpost_x_not hpost_i
      have hne : x ≠ i := by
        intro hxi
        subst x
        exact hpre_i_not hpre_x
      exact Finset.mem_erase.mpr ⟨hne, by simp [T, hpost_x]⟩
    have hcard_le : S.card ≤ (T.erase i).card := Finset.card_le_card hsub
    have hcard_lt : (T.erase i).card < T.card := Finset.card_erase_lt_of_mem hiT
    have hlt : S.card < T.card := lt_of_le_of_lt hcard_le hcard_lt
    have hlt_self : S.card < S.card := by simpa [hcountST] using hlt
    exact (lt_irrefl S.card) hlt_self
  · intro hpre_i
    by_contra hpost_i_not
    have hiS : i ∈ S := by simp [S, hpre_i]
    have hsub : T ⊆ S.erase i := by
      intro x hxT
      have hpost_x : postHigh x := by simpa [T] using hxT
      have hpre_x : preHigh x := by
        by_contra hpre_x_not
        exact hNoInv i x hpre_i hpre_x_not hpost_i_not hpost_x
      have hne : x ≠ i := by
        intro hxi
        subst x
        exact hpost_i_not hpost_x
      exact Finset.mem_erase.mpr ⟨hne, by simp [S, hpre_x]⟩
    have hcard_le : T.card ≤ (S.erase i).card := Finset.card_le_card hsub
    have hcard_lt : (S.erase i).card < S.card := Finset.card_erase_lt_of_mem hiS
    have hlt : T.card < S.card := lt_of_le_of_lt hcard_le hcard_lt
    have hlt_self : S.card < S.card := by simpa [hcountST] using hlt
    exact (lt_irrefl S.card) hlt_self

theorem finite_reward_levels_preserved_of_no_inversion_and_equal_tail_counts
    {α : Type*} [Fintype α] [DecidableEq α]
    (preLevel postLevel : α → ℕ)
    (hNoInv :
      ∀ i j, preLevel j < preLevel i → postLevel j ≤ postLevel i)
    (hcount :
      ∀ t,
        (Finset.univ.filter (fun i => t ≤ preLevel i)).card =
          (Finset.univ.filter (fun i => t ≤ postLevel i)).card) :
    ∀ i, postLevel i = preLevel i := by
  classical
  have htail :
      ∀ t i, t ≤ postLevel i ↔ t ≤ preLevel i := by
    intro t
    exact binary_reward_preserved_of_no_inversion_and_equal_count
      (fun i => t ≤ preLevel i)
      (fun i => t ≤ postLevel i)
      (by
        intro i j hpre_i hpre_j_not hpost_i_not hpost_j
        have hpre_j_lt_t : preLevel j < t := Nat.lt_of_not_ge hpre_j_not
        have hpost_i_lt_t : postLevel i < t := Nat.lt_of_not_ge hpost_i_not
        have hpre_order : preLevel j < preLevel i := lt_of_lt_of_le hpre_j_lt_t hpre_i
        have hpost_order : postLevel j ≤ postLevel i := hNoInv i j hpre_order
        have hpost_lt : postLevel i < postLevel j := lt_of_lt_of_le hpost_i_lt_t hpost_j
        exact not_lt_of_ge hpost_order hpost_lt)
      (hcount t)
  intro i
  exact le_antisymm
    ((htail (postLevel i) i).mp le_rfl)
    ((htail (preLevel i) i).mpr le_rfl)

theorem no_reward_inversion_of_preorder_score_monotone
    {α : Type*} (preLevel postLevel : α → ℕ) (score : α → ℝ)
    (hpre_to_score :
      ∀ x y, preLevel y < preLevel x → score y ≤ score x)
    (hpost_score_mono :
      ∀ x y, score y ≤ score x → postLevel y ≤ postLevel x) :
    ∀ x y, preLevel y < preLevel x → postLevel y ≤ postLevel x := by
  intro x y hpre
  exact hpost_score_mono x y (hpre_to_score x y hpre)

theorem finite_reward_levels_preserved_of_score_order_and_equal_tail_counts
    {α : Type*} [Fintype α] [DecidableEq α]
    (preLevel postLevel : α → ℕ) (score : α → ℝ)
    (hpre_to_score :
      ∀ x y, preLevel y < preLevel x → score y ≤ score x)
    (hpost_score_mono :
      ∀ x y, score y ≤ score x → postLevel y ≤ postLevel x)
    (hcount :
      ∀ t,
        (Finset.univ.filter (fun i => t ≤ preLevel i)).card =
          (Finset.univ.filter (fun i => t ≤ postLevel i)).card) :
    ∀ i, postLevel i = preLevel i :=
  finite_reward_levels_preserved_of_no_inversion_and_equal_tail_counts
    preLevel postLevel
    (no_reward_inversion_of_preorder_score_monotone
      preLevel postLevel score hpre_to_score hpost_score_mono)
    hcount

theorem finite_tail_counts_eq_of_exact_level_counts
    {α : Type*} [Fintype α] [DecidableEq α]
    (K : ℕ) (preLevel postLevel : α → ℕ)
    (hpre_bound : ∀ i, preLevel i < K)
    (hpost_bound : ∀ i, postLevel i < K)
    (hlevel_count :
      ∀ t, t < K →
        (Finset.univ.filter (fun i => preLevel i = t)).card =
          (Finset.univ.filter (fun i => postLevel i = t)).card) :
    ∀ t,
      (Finset.univ.filter (fun i => t ≤ preLevel i)).card =
        (Finset.univ.filter (fun i => t ≤ postLevel i)).card := by
  classical
  intro t
  let levels := (Finset.range K).filter (fun level => t ≤ level)
  have hpre_tail :
      (Finset.univ.filter (fun i => t ≤ preLevel i)).card =
        ∑ level ∈ levels,
          (Finset.univ.filter (fun i => preLevel i = level)).card := by
    have hfilter :
        Finset.univ.filter (fun i => t ≤ preLevel i) =
          Finset.univ.filter (fun i => preLevel i ∈ levels) := by
      ext i
      simp [levels, hpre_bound i]
    rw [hfilter]
    exact (Finset.sum_card_fiberwise_eq_card_filter
      (s := Finset.univ) (t := levels) (g := preLevel)).symm
  have hpost_tail :
      (Finset.univ.filter (fun i => t ≤ postLevel i)).card =
        ∑ level ∈ levels,
          (Finset.univ.filter (fun i => postLevel i = level)).card := by
    have hfilter :
        Finset.univ.filter (fun i => t ≤ postLevel i) =
          Finset.univ.filter (fun i => postLevel i ∈ levels) := by
      ext i
      simp [levels, hpost_bound i]
    rw [hfilter]
    exact (Finset.sum_card_fiberwise_eq_card_filter
      (s := Finset.univ) (t := levels) (g := postLevel)).symm
  rw [hpre_tail, hpost_tail]
  exact Finset.sum_congr rfl fun level hlevel =>
    hlevel_count level (by
      have hlevel_range : level ∈ Finset.range K := by
        exact (Finset.mem_filter.mp hlevel).1
      exact Finset.mem_range.mp hlevel_range)

theorem finite_reward_levels_preserved_of_no_inversion_and_exact_level_counts
    {α : Type*} [Fintype α] [DecidableEq α]
    (K : ℕ) (preLevel postLevel : α → ℕ)
    (hpre_bound : ∀ i, preLevel i < K)
    (hpost_bound : ∀ i, postLevel i < K)
    (hNoInv :
      ∀ i j, preLevel j < preLevel i → postLevel j ≤ postLevel i)
    (hlevel_count :
      ∀ t, t < K →
        (Finset.univ.filter (fun i => preLevel i = t)).card =
          (Finset.univ.filter (fun i => postLevel i = t)).card) :
    ∀ i, postLevel i = preLevel i :=
  finite_reward_levels_preserved_of_no_inversion_and_equal_tail_counts
    preLevel postLevel hNoInv
    (finite_tail_counts_eq_of_exact_level_counts
      K preLevel postLevel hpre_bound hpost_bound hlevel_count)

theorem finite_reward_levels_preserved_of_score_order_and_exact_level_counts
    {α : Type*} [Fintype α] [DecidableEq α]
    (K : ℕ) (preLevel postLevel : α → ℕ) (score : α → ℝ)
    (hpre_bound : ∀ i, preLevel i < K)
    (hpost_bound : ∀ i, postLevel i < K)
    (hpre_to_score :
      ∀ x y, preLevel y < preLevel x → score y ≤ score x)
    (hpost_score_mono :
      ∀ x y, score y ≤ score x → postLevel y ≤ postLevel x)
    (hlevel_count :
      ∀ t, t < K →
        (Finset.univ.filter (fun i => preLevel i = t)).card =
          (Finset.univ.filter (fun i => postLevel i = t)).card) :
    ∀ i, postLevel i = preLevel i :=
  finite_reward_levels_preserved_of_score_order_and_equal_tail_counts
    preLevel postLevel score hpre_to_score hpost_score_mono
    (finite_tail_counts_eq_of_exact_level_counts
      K preLevel postLevel hpre_bound hpost_bound hlevel_count)

theorem binary_reward_sets_ae_eq_of_no_cross_and_equal_measure
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {preHigh postHigh : Set α}
    (hNoCross :
      (preHigh \ postHigh).Nonempty →
        (postHigh \ preHigh).Nonempty → False)
    (hmeasure : μ preHigh = μ postHigh)
    (hpre_meas : NullMeasurableSet preHigh μ)
    (hpost_meas : NullMeasurableSet postHigh μ)
    (hpre_finite : (μ preHigh) ≠ ⊤)
    (hpost_finite : (μ postHigh) ≠ ⊤) :
    preHigh =ᵐ[μ] postHigh := by
  by_cases hpre_extra : (preHigh \ postHigh).Nonempty
  · have hpost_extra_empty : ¬ (postHigh \ preHigh).Nonempty := fun h =>
      hNoCross hpre_extra h
    have hsubset : postHigh ⊆ preHigh := by
      intro x hxpost
      by_contra hxpre_not
      exact hpost_extra_empty ⟨x, hxpost, hxpre_not⟩
    have hae : postHigh =ᵐ[μ] preHigh :=
      ae_eq_of_subset_of_measure_ge hsubset (by rw [hmeasure]) hpost_meas hpre_finite
    exact hae.symm
  · have hsubset : preHigh ⊆ postHigh := by
      intro x hxpre
      by_contra hxpost_not
      exact hpre_extra ⟨x, hxpre, hxpost_not⟩
    exact ae_eq_of_subset_of_measure_ge hsubset (by rw [hmeasure]) hpre_meas hpost_finite

theorem bounded_reward_levels_ae_eq_of_no_inversion_and_equal_tail_measures
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (K : ℕ) (preLevel postLevel : α → ℕ)
    (hpre_bound : ∀ x, preLevel x < K)
    (hpost_bound : ∀ x, postLevel x < K)
    (hNoInv :
      ∀ x y, preLevel y < preLevel x → postLevel y ≤ postLevel x)
    (hmeasure :
      ∀ t, t < K →
        μ {x | t ≤ preLevel x} = μ {x | t ≤ postLevel x})
    (hpre_meas :
      ∀ t, t < K → NullMeasurableSet {x | t ≤ preLevel x} μ)
    (hpost_meas :
      ∀ t, t < K → NullMeasurableSet {x | t ≤ postLevel x} μ)
    (hpre_finite :
      ∀ t, t < K → (μ {x | t ≤ preLevel x}) ≠ ⊤)
    (hpost_finite :
      ∀ t, t < K → (μ {x | t ≤ postLevel x}) ≠ ⊤) :
    postLevel =ᵐ[μ] preLevel := by
  classical
  have htail :
      ∀ t, t < K →
        {x | t ≤ postLevel x} =ᵐ[μ] {x | t ≤ preLevel x} := by
    intro t ht
    have hNoCross :
        ({x | t ≤ postLevel x} \ {x | t ≤ preLevel x}).Nonempty →
          ({x | t ≤ preLevel x} \ {x | t ≤ postLevel x}).Nonempty →
            False := by
      intro hpost_extra hpre_extra
      rcases hpost_extra with ⟨x, hxpost, hxpre_not⟩
      rcases hpre_extra with ⟨y, hypre, hypost_not⟩
      have hpre_x_lt_t : preLevel x < t := Nat.lt_of_not_ge hxpre_not
      have hpost_y_lt_t : postLevel y < t := Nat.lt_of_not_ge hypost_not
      have hpre_order : preLevel x < preLevel y := lt_of_lt_of_le hpre_x_lt_t hypre
      have hpost_order : postLevel x ≤ postLevel y := hNoInv y x hpre_order
      have hpost_lt : postLevel y < postLevel x := lt_of_lt_of_le hpost_y_lt_t hxpost
      exact not_lt_of_ge hpost_order hpost_lt
    exact binary_reward_sets_ae_eq_of_no_cross_and_equal_measure
      hNoCross (by rw [hmeasure t ht]) (hpost_meas t ht) (hpre_meas t ht)
      (hpost_finite t ht) (hpre_finite t ht)
  have hall :
      ∀ᵐ x ∂μ, ∀ t ∈ Finset.range K,
        (t ≤ postLevel x ↔ t ≤ preLevel x) := by
    rw [Filter.eventually_all_finset]
    intro t ht
    simpa using (htail t (Finset.mem_range.mp ht)).mem_iff
  filter_upwards [hall] with x hx
  exact le_antisymm
    ((hx (postLevel x) (Finset.mem_range.mpr (hpost_bound x))).mp le_rfl)
    ((hx (preLevel x) (Finset.mem_range.mpr (hpre_bound x))).mpr le_rfl)

/--
Replace a finite reward-level function by zero on a null exception set.  This
is the small adapter used to turn pointwise finite-level order arguments into
almost-everywhere statements for continuous equilibria with null tie/cutoff
exceptions.
-/
noncomputable def levelOutsideException {α : Type*}
    (exception : Set α) (level : α → ℕ) : α → ℕ := by
  classical
  exact fun x => if x ∈ exception then 0 else level x

theorem bounded_reward_levels_ae_eq_of_no_inversion_off_null_and_equal_tail_measures
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (K : ℕ) (preLevel postLevel : α → ℕ) {exception : Set α}
    (hexception : μ exception = 0)
    (hpre_bound : ∀ x, preLevel x < K)
    (hpost_bound : ∀ x, postLevel x < K)
    (hNoInv :
      ∀ x y, x ∉ exception → y ∉ exception →
        preLevel y < preLevel x → postLevel y ≤ postLevel x)
    (hmeasure :
      ∀ t, t < K →
        μ {x | t ≤ preLevel x} = μ {x | t ≤ postLevel x})
    (hpre_meas :
      ∀ t, t < K → NullMeasurableSet {x | t ≤ preLevel x} μ)
    (hpost_meas :
      ∀ t, t < K → NullMeasurableSet {x | t ≤ postLevel x} μ)
    (hpre_finite :
      ∀ t, t < K → (μ {x | t ≤ preLevel x}) ≠ ⊤)
    (hpost_finite :
      ∀ t, t < K → (μ {x | t ≤ postLevel x}) ≠ ⊤) :
    postLevel =ᵐ[μ] preLevel := by
  classical
  let preLevel' : α → ℕ := fun x => if x ∈ exception then 0 else preLevel x
  let postLevel' : α → ℕ := fun x => if x ∈ exception then 0 else postLevel x
  have hpre_tail_ae :
      ∀ t, {x | t ≤ preLevel' x} =ᵐ[μ] {x | t ≤ preLevel x} := by
    intro t
    change {x | t ≤ (if x ∈ exception then 0 else preLevel x)} =ᵐ[μ]
      {x | t ≤ preLevel x}
    exact (AppliedModelingLib.ae_iff_of_forall_not_mem_null
        (μ := μ) hexception
        (by
          intro x hx
          change (t ≤ (if x ∈ exception then 0 else preLevel x) ↔
            t ≤ preLevel x)
          rw [if_neg hx])).set_eq
  have hpost_tail_ae :
      ∀ t, {x | t ≤ postLevel' x} =ᵐ[μ] {x | t ≤ postLevel x} := by
    intro t
    change {x | t ≤ (if x ∈ exception then 0 else postLevel x)} =ᵐ[μ]
      {x | t ≤ postLevel x}
    exact (AppliedModelingLib.ae_iff_of_forall_not_mem_null
        (μ := μ) hexception
        (by
          intro x hx
          change (t ≤ (if x ∈ exception then 0 else postLevel x) ↔
            t ≤ postLevel x)
          rw [if_neg hx])).set_eq
  have hlevels' :
      postLevel' =ᵐ[μ] preLevel' := by
    refine bounded_reward_levels_ae_eq_of_no_inversion_and_equal_tail_measures
      K preLevel' postLevel' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro x
      by_cases hx : x ∈ exception
      · change (if x ∈ exception then 0 else preLevel x) < K
        rw [if_pos hx]
        exact Nat.lt_of_le_of_lt (Nat.zero_le (preLevel x)) (hpre_bound x)
      · change (if x ∈ exception then 0 else preLevel x) < K
        rw [if_neg hx]
        exact hpre_bound x
    · intro x
      by_cases hx : x ∈ exception
      · change (if x ∈ exception then 0 else postLevel x) < K
        rw [if_pos hx]
        exact Nat.lt_of_le_of_lt (Nat.zero_le (postLevel x)) (hpost_bound x)
      · change (if x ∈ exception then 0 else postLevel x) < K
        rw [if_neg hx]
        exact hpost_bound x
    · intro x y hpre
      by_cases hx : x ∈ exception
      · change (if y ∈ exception then 0 else preLevel y) <
            (if x ∈ exception then 0 else preLevel x) at hpre
        rw [if_pos hx] at hpre
        exact False.elim (Nat.not_lt_zero _ hpre)
      · by_cases hy : y ∈ exception
        · change (if y ∈ exception then 0 else postLevel y) ≤
            (if x ∈ exception then 0 else postLevel x)
          rw [if_pos hy]
          exact Nat.zero_le _
        · change (if y ∈ exception then 0 else postLevel y) ≤
            (if x ∈ exception then 0 else postLevel x)
          rw [if_neg hy, if_neg hx]
          exact
            hNoInv x y hx hy
              (by
                change (if y ∈ exception then 0 else preLevel y) <
                  (if x ∈ exception then 0 else preLevel x) at hpre
                rwa [if_neg hy, if_neg hx] at hpre)
    · intro t ht
      rw [measure_congr (hpre_tail_ae t), measure_congr (hpost_tail_ae t)]
      exact hmeasure t ht
    · intro t ht
      exact (hpre_meas t ht).congr (hpre_tail_ae t).symm
    · intro t ht
      exact (hpost_meas t ht).congr (hpost_tail_ae t).symm
    · intro t ht
      rw [measure_congr (hpre_tail_ae t)]
      exact hpre_finite t ht
    · intro t ht
      rw [measure_congr (hpost_tail_ae t)]
      exact hpost_finite t ht
  have hpost_ae :
      postLevel =ᵐ[μ] postLevel' :=
    AppliedModelingLib.ae_eq_of_forall_not_mem_null
      (μ := μ) hexception
      (by
        intro x hx
        change postLevel x = (if x ∈ exception then 0 else postLevel x)
        rw [if_neg hx])
  have hpre_ae :
      preLevel' =ᵐ[μ] preLevel :=
    AppliedModelingLib.ae_eq_of_forall_not_mem_null
      (μ := μ) hexception
      (by
        intro x hx
        change (if x ∈ exception then 0 else preLevel x) = preLevel x
        rw [if_neg hx])
  exact hpost_ae.trans (hlevels'.trans hpre_ae)

theorem bounded_reward_levels_ae_eq_of_no_inversion_and_equal_level_distribution
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    (K : ℕ) (preLevel postLevel : α → ℕ)
    (hpre_bound : ∀ x, preLevel x < K)
    (hpost_bound : ∀ x, postLevel x < K)
    (hNoInv :
      ∀ x y, preLevel y < preLevel x → postLevel y ≤ postLevel x)
    (hpre_meas : Measurable preLevel)
    (hpost_meas : Measurable postLevel)
    (hdist : Measure.map preLevel μ = Measure.map postLevel μ) :
    postLevel =ᵐ[μ] preLevel := by
  refine bounded_reward_levels_ae_eq_of_no_inversion_and_equal_tail_measures
    K preLevel postLevel hpre_bound hpost_bound hNoInv ?_ ?_ ?_ ?_ ?_
  · intro t _ht
    let tail : Set ℕ := {n | t ≤ n}
    have htail_meas : MeasurableSet tail := by
      simpa [tail] using (measurableSet_Ici : MeasurableSet (Set.Ici t))
    have hpre :
        μ {x | t ≤ preLevel x} = Measure.map preLevel μ tail := by
      rw [Measure.map_apply hpre_meas htail_meas]
      rfl
    have hpost :
        μ {x | t ≤ postLevel x} = Measure.map postLevel μ tail := by
      rw [Measure.map_apply hpost_meas htail_meas]
      rfl
    rw [hpre, hpost, hdist]
  · intro t _ht
    have htail_meas : MeasurableSet {n : ℕ | t ≤ n} := by
      simpa using (measurableSet_Ici : MeasurableSet (Set.Ici t))
    exact (hpre_meas htail_meas).nullMeasurableSet
  · intro t _ht
    have htail_meas : MeasurableSet {n : ℕ | t ≤ n} := by
      simpa using (measurableSet_Ici : MeasurableSet (Set.Ici t))
    exact (hpost_meas htail_meas).nullMeasurableSet
  · intro t _ht
    exact measure_ne_top μ {x | t ≤ preLevel x}
  · intro t _ht
    exact measure_ne_top μ {x | t ≤ postLevel x}

theorem rewardLevel_distribution_eq_of_rank_distribution_eq
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {preRank postRank : α → ℝ} {rankLevel : ℝ → ℕ}
    (hpreRank_meas : Measurable preRank)
    (hpostRank_meas : Measurable postRank)
    (hrankLevel_meas : Measurable rankLevel)
    (hrank_dist : Measure.map preRank μ = Measure.map postRank μ) :
    Measure.map (fun x => rankLevel (preRank x)) μ =
      Measure.map (fun x => rankLevel (postRank x)) μ := by
  change Measure.map (rankLevel ∘ preRank) μ =
    Measure.map (rankLevel ∘ postRank) μ
  rw [← Measure.map_map hrankLevel_meas hpreRank_meas,
    ← Measure.map_map hrankLevel_meas hpostRank_meas,
    hrank_dist]

theorem bounded_rank_levels_ae_eq_of_no_inversion_and_equal_rank_distribution
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    (K : ℕ) (preRank postRank : α → ℝ) (rankLevel : ℝ → ℕ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound : ∀ x, rankLevel (postRank x) < K)
    (hNoInv :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        rankLevel (postRank y) ≤ rankLevel (postRank x))
    (hpreRank_meas : Measurable preRank)
    (hpostRank_meas : Measurable postRank)
    (hrankLevel_meas : Measurable rankLevel)
    (hrank_dist : Measure.map preRank μ = Measure.map postRank μ) :
    (fun x => rankLevel (postRank x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  exact bounded_reward_levels_ae_eq_of_no_inversion_and_equal_level_distribution
    K (fun x => rankLevel (preRank x)) (fun x => rankLevel (postRank x))
    hpre_bound hpost_bound hNoInv
    (hrankLevel_meas.comp hpreRank_meas)
    (hrankLevel_meas.comp hpostRank_meas)
    (rewardLevel_distribution_eq_of_rank_distribution_eq
      hpreRank_meas hpostRank_meas hrankLevel_meas hrank_dist)

theorem bounded_rank_levels_ae_eq_of_pairwise_inversion_contradiction_and_equal_rank_distribution
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    (K : ℕ) (preRank postRank : α → ℝ) (rankLevel : ℝ → ℕ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound : ∀ x, rankLevel (postRank x) < K)
    (hInversionContr :
      ∀ x y,
        rankLevel (preRank y) < rankLevel (preRank x) →
        rankLevel (postRank x) < rankLevel (postRank y) →
        False)
    (hpreRank_meas : Measurable preRank)
    (hpostRank_meas : Measurable postRank)
    (hrankLevel_meas : Measurable rankLevel)
    (hrank_dist : Measure.map preRank μ = Measure.map postRank μ) :
    (fun x => rankLevel (postRank x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  refine bounded_rank_levels_ae_eq_of_no_inversion_and_equal_rank_distribution
    K preRank postRank rankLevel hpre_bound hpost_bound ?_
    hpreRank_meas hpostRank_meas hrankLevel_meas hrank_dist
  intro x y hpre
  by_contra hnot
  exact hInversionContr x y hpre (Nat.lt_of_not_ge hnot)

theorem rank_distribution_eq_of_common_reference_distribution
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {preRank postRank : α → ℝ} {reference : Measure ℝ}
    (hpre : Measure.map preRank μ = reference)
    (hpost : Measure.map postRank μ = reference) :
    Measure.map preRank μ = Measure.map postRank μ := by
  exact hpre.trans hpost.symm

/--
Source best-response primitive for the continuum equilibrium definition:
holding the rank map fixed, the selected effort maximizes reward minus cost
against every alternative effort.
-/
def SourceRankBestResponse
    {α : Type*} (cost : ℝ → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ) (levelReward : ℕ → ℝ) (effort : α → ℝ) : Prop :=
  ∀ x d,
    levelReward (rankLevel (rankOfEffort x (effort x))) - cost (effort x) ≥
      levelReward (rankLevel (rankOfEffort x d)) - cost d

/--
Source best-response primitive with the effort-domain restriction made
explicit.  The paper's effort choices live on the feasible side of the
baseline effort, so theorem endpoints that use cost monotonicity on `[e0, ∞)`
should route through this predicate rather than quantifying over all real
deviations.
-/
def SourceRankBestResponseFeasible
    {α : Type*} (e0 : ℝ) (cost : ℝ → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ) (levelReward : ℕ → ℝ) (effort : α → ℝ) : Prop :=
  (∀ x, e0 ≤ effort x) ∧
    ∀ x d, e0 ≤ d →
      levelReward (rankLevel (rankOfEffort x (effort x))) - cost (effort x) ≥
        levelReward (rankLevel (rankOfEffort x d)) - cost d

/--
Pointwise source equilibrium at the rank layer: selected efforts are
best responses to the fixed rank map, and the realized post-effort rank is the
rank induced by the selected efforts.
-/
def SourceRankEquilibrium
    {α : Type*} (cost : ℝ → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (postRank : α → ℝ) (rankLevel : ℝ → ℕ)
    (levelReward : ℕ → ℝ) (effort : α → ℝ) : Prop :=
  SourceRankBestResponse cost rankOfEffort rankLevel levelReward effort ∧
    ∀ x, rankOfEffort x (effort x) = postRank x

theorem sourceRankEquilibrium_bestResponse
    {α : Type*} {cost : ℝ → ℝ} {rankOfEffort : α → ℝ → ℝ}
    {postRank : α → ℝ} {rankLevel : ℝ → ℕ}
    {levelReward : ℕ → ℝ} {effort : α → ℝ}
    (hEq :
      SourceRankEquilibrium cost rankOfEffort postRank rankLevel
        levelReward effort) :
    SourceRankBestResponse cost rankOfEffort rankLevel levelReward effort :=
  hEq.1

theorem sourceRankEquilibrium_postRank
    {α : Type*} {cost : ℝ → ℝ} {rankOfEffort : α → ℝ → ℝ}
    {postRank : α → ℝ} {rankLevel : ℝ → ℕ}
    {levelReward : ℕ → ℝ} {effort : α → ℝ}
    (hEq :
      SourceRankEquilibrium cost rankOfEffort postRank rankLevel
        levelReward effort) :
    ∀ x, rankOfEffort x (effort x) = postRank x :=
  hEq.2

/--
Shared-library choice-equilibrium representation of the source rank
best-response condition.  All efforts are feasible in this reduced rank layer;
paper-specific feasibility restrictions should be encoded before invoking this
data, not hidden inside the equilibrium shell.
-/
def sourceRankChoiceEquilibriumData
    {α : Type*} (cost : ℝ → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ) (levelReward : ℕ → ℝ) (effort : α → ℝ) :
    AppliedModelingLib.ChoiceEquilibriumData α ℝ where
  actionFeasible := fun _ _ => True
  chosenAction := effort
  payoff := fun x d => levelReward (rankLevel (rankOfEffort x d)) - cost d
  consistency := True

/--
Choice-equilibrium representation of the source rank best-response condition
with the paper's feasible effort domain exposed as an action constraint.
-/
def sourceRankFeasibleChoiceEquilibriumData
    {α : Type*} (e0 : ℝ) (cost : ℝ → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ) (levelReward : ℕ → ℝ) (effort : α → ℝ) :
    AppliedModelingLib.ChoiceEquilibriumData α ℝ where
  actionFeasible := fun _ d => e0 ≤ d
  chosenAction := effort
  payoff := fun x d => levelReward (rankLevel (rankOfEffort x d)) - cost d
  consistency := True

theorem sourceRankBestResponse_iff_choiceEquilibrium
    {α : Type*} {cost : ℝ → ℝ} {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ} {effort : α → ℝ} :
    SourceRankBestResponse cost rankOfEffort rankLevel levelReward effort ↔
      AppliedModelingLib.IsChoiceEquilibrium
        (sourceRankChoiceEquilibriumData
          cost rankOfEffort rankLevel levelReward effort) := by
  constructor
  · intro hbest
    refine ⟨?_, ?_, trivial⟩
    · intro _x
      trivial
    · intro x d _hfeasible
      exact hbest x d
  · intro hEq x d
    exact AppliedModelingLib.isChoiceEquilibrium_best_response hEq x d trivial

theorem sourceRankBestResponseFeasible_iff_choiceEquilibrium
    {α : Type*} {e0 : ℝ} {cost : ℝ → ℝ} {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ} {effort : α → ℝ} :
    SourceRankBestResponseFeasible e0 cost rankOfEffort rankLevel levelReward effort ↔
      AppliedModelingLib.IsChoiceEquilibrium
        (sourceRankFeasibleChoiceEquilibriumData
          e0 cost rankOfEffort rankLevel levelReward effort) := by
  constructor
  · intro hbest
    refine ⟨?_, ?_, trivial⟩
    · intro x
      exact hbest.1 x
    · intro x d hd
      exact hbest.2 x d hd
  · intro hEq
    refine ⟨?_, ?_⟩
    · intro x
      exact AppliedModelingLib.isChoiceEquilibrium_feasible hEq x
    · intro x d hd
      exact AppliedModelingLib.isChoiceEquilibrium_best_response hEq x d hd

/--
Almost-everywhere source rank best response, routed through the shared
continuous-type choice-equilibrium API used by the testing/admissions papers.
-/
def SourceRankBestResponseAE
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (cost : ℝ → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ) (levelReward : ℕ → ℝ) (effort : α → ℝ) : Prop :=
  AppliedModelingLib.IsChoiceEquilibriumAE μ
    (sourceRankChoiceEquilibriumData
      cost rankOfEffort rankLevel levelReward effort)

/--
Almost-everywhere source rank best response on the feasible effort domain.
This is the source-model version to use when theorem proofs rely on monotonicity
or convexity only on `[e0, ∞)`.
-/
def SourceRankBestResponseFeasibleAE
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (e0 : ℝ) (cost : ℝ → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ) (levelReward : ℕ → ℝ) (effort : α → ℝ) : Prop :=
  AppliedModelingLib.IsChoiceEquilibriumAE μ
    (sourceRankFeasibleChoiceEquilibriumData
      e0 cost rankOfEffort rankLevel levelReward effort)

/--
Source equilibrium predicate at the rank layer: selected efforts are
almost-everywhere best responses to the fixed rank map, and the realized
post-effort rank agrees almost everywhere with the rank induced by the chosen
efforts.
-/
def SourceRankEquilibriumAE
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (cost : ℝ → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (postRank : α → ℝ) (rankLevel : ℝ → ℕ)
    (levelReward : ℕ → ℝ) (effort : α → ℝ) : Prop :=
  SourceRankBestResponseAE μ cost rankOfEffort rankLevel levelReward effort ∧
    (fun x => rankOfEffort x (effort x)) =ᵐ[μ] postRank

theorem sourceRankEquilibriumAE_bestResponse
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {cost : ℝ → ℝ} {rankOfEffort : α → ℝ → ℝ}
    {postRank : α → ℝ} {rankLevel : ℝ → ℕ}
    {levelReward : ℕ → ℝ} {effort : α → ℝ}
    (hEq :
      SourceRankEquilibriumAE μ cost rankOfEffort postRank rankLevel
        levelReward effort) :
    SourceRankBestResponseAE μ cost rankOfEffort rankLevel levelReward effort :=
  hEq.1

theorem sourceRankEquilibriumAE_postRank
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {cost : ℝ → ℝ} {rankOfEffort : α → ℝ → ℝ}
    {postRank : α → ℝ} {rankLevel : ℝ → ℕ}
    {levelReward : ℕ → ℝ} {effort : α → ℝ}
    (hEq :
      SourceRankEquilibriumAE μ cost rankOfEffort postRank rankLevel
        levelReward effort) :
    (fun x => rankOfEffort x (effort x)) =ᵐ[μ] postRank :=
  hEq.2

theorem sourceRankBestResponseAE_best_response_ae
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {cost : ℝ → ℝ} {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ} {effort : α → ℝ}
    (hEq :
      SourceRankBestResponseAE μ cost rankOfEffort rankLevel levelReward effort) :
    ∀ᵐ x ∂μ, ∀ d,
      levelReward (rankLevel (rankOfEffort x d)) - cost d ≤
        levelReward (rankLevel (rankOfEffort x (effort x))) - cost (effort x) := by
  have hbest :=
    AppliedModelingLib.isChoiceEquilibriumAE_best_response_ae hEq
  exact hbest.mono fun x hx d => hx d trivial

theorem sourceRankBestResponseFeasibleAE_feasible_ae
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {e0 : ℝ} {cost : ℝ → ℝ} {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ} {effort : α → ℝ}
    (hEq :
      SourceRankBestResponseFeasibleAE μ e0 cost rankOfEffort rankLevel
        levelReward effort) :
    ∀ᵐ x ∂μ, e0 ≤ effort x :=
  AppliedModelingLib.isChoiceEquilibriumAE_feasible_ae hEq

theorem sourceRankBestResponseFeasibleAE_best_response_ae
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {e0 : ℝ} {cost : ℝ → ℝ} {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ} {effort : α → ℝ}
    (hEq :
      SourceRankBestResponseFeasibleAE μ e0 cost rankOfEffort rankLevel
        levelReward effort) :
    ∀ᵐ x ∂μ, ∀ d, e0 ≤ d →
      levelReward (rankLevel (rankOfEffort x d)) - cost d ≤
        levelReward (rankLevel (rankOfEffort x (effort x))) - cost (effort x) :=
  AppliedModelingLib.isChoiceEquilibriumAE_best_response_ae hEq

theorem sourceRankBestResponseAE_of_forall_not_mem_null
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {cost : ℝ → ℝ} {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ} {effort : α → ℝ}
    {exception : Set α}
    (hexception : μ exception = 0)
    (hbest :
      ∀ x, x ∉ exception → ∀ d,
        levelReward (rankLevel (rankOfEffort x (effort x))) - cost (effort x) ≥
          levelReward (rankLevel (rankOfEffort x d)) - cost d) :
    SourceRankBestResponseAE μ cost rankOfEffort rankLevel levelReward effort := by
  refine AppliedModelingLib.isChoiceEquilibriumAE_of_forall_not_mem_null
    hexception ?_ ?_ trivial
  · intro _x _hx
    trivial
  · intro x hx d _hfeasible
    exact hbest x hx d

theorem sourceRankBestResponseFeasibleAE_of_forall_not_mem_null
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {e0 : ℝ} {cost : ℝ → ℝ} {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ} {effort : α → ℝ}
    {exception : Set α}
    (hexception : μ exception = 0)
    (hchosen :
      ∀ x, x ∉ exception → e0 ≤ effort x)
    (hbest :
      ∀ x, x ∉ exception → ∀ d, e0 ≤ d →
        levelReward (rankLevel (rankOfEffort x (effort x))) - cost (effort x) ≥
          levelReward (rankLevel (rankOfEffort x d)) - cost d) :
    SourceRankBestResponseFeasibleAE μ e0 cost rankOfEffort rankLevel
      levelReward effort := by
  refine AppliedModelingLib.isChoiceEquilibriumAE_of_forall_not_mem_null
    hexception ?_ ?_ trivial
  · intro x hx
    exact hchosen x hx
  · intro x hx d hd
    exact hbest x hx d hd

theorem sourceRankBestResponseAE_of_sourceRankBestResponse
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {cost : ℝ → ℝ} {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ} {effort : α → ℝ}
    (hbest :
      SourceRankBestResponse cost rankOfEffort rankLevel levelReward effort) :
    SourceRankBestResponseAE μ cost rankOfEffort rankLevel levelReward effort :=
  AppliedModelingLib.isChoiceEquilibriumAE_of_pointwise
    ((sourceRankBestResponse_iff_choiceEquilibrium).mp hbest)

theorem sourceRankBestResponseFeasibleAE_of_sourceRankBestResponseFeasible
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {e0 : ℝ} {cost : ℝ → ℝ} {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ} {effort : α → ℝ}
    (hbest :
      SourceRankBestResponseFeasible e0 cost rankOfEffort rankLevel
        levelReward effort) :
    SourceRankBestResponseFeasibleAE μ e0 cost rankOfEffort rankLevel
      levelReward effort :=
  AppliedModelingLib.isChoiceEquilibriumAE_of_pointwise
    ((sourceRankBestResponseFeasible_iff_choiceEquilibrium).mp hbest)

/--
Pointwise source tie-breaking bridge.  Under distinct reward levels, the
source best-response/tie-bump argument implies that every pair of applicants
with the same realized score has the same realized post-rank level.  This is a
usable replacement for paper-facing actual equal-score certificates.
-/
theorem actual_equal_score_rank_levels_of_source_best_response
    {α : Type*} {cost g : ℝ → ℝ}
    {rankOfEffort : α → ℝ → ℝ} {postRank : α → ℝ}
    {rankLevel : ℝ → ℕ}
    {levelReward : ℕ → ℝ} {skill score effort : α → ℝ}
    (hlevelReward_inj : Function.Injective levelReward)
    (hpost_actual :
      ∀ z, rankLevel (rankOfEffort z (effort z)) =
        rankLevel (postRank z))
    (hcost_cont : ∀ z, ContinuousAt cost (effort z))
    (hg_strict : StrictMono g)
    (hskill_pos : ∀ z, 0 < skill z)
    (hscore_eq : ∀ z, score z = g (effort z) * skill z)
    (hdeviation_reaches_reward :
      ∀ x y d, score y < g d * skill x →
        levelReward (rankLevel (rankOfEffort y (effort y))) ≤
          levelReward (rankLevel (rankOfEffort x d)))
    (hbest :
      SourceRankBestResponse cost rankOfEffort rankLevel levelReward effort) :
    ∀ x y, score x = score y → rankLevel (postRank x) = rankLevel (postRank y) := by
  intro x y hsame_score
  refine tied_score_actual_rank_levels_eq_of_source_best_response
    hlevelReward_inj (hpost_actual x) (hpost_actual y)
    (hcost_cont x) (hcost_cont y) hg_strict (hskill_pos x) (hskill_pos y)
    hscore_eq hsame_score
    (fun d hd => hdeviation_reaches_reward x y d hd)
    (fun d hd => hdeviation_reaches_reward y x d hd)
    ?_ ?_
  · intro d
    exact hbest x d
  · intro d
    exact hbest y d

theorem source_rank_best_response_pairwise_inequalities_of_pointwise
    {α : Type*}
    {cost : ℝ → ℝ} {rankOfEffort : α → ℝ → ℝ}
    {postRank : α → ℝ} {rankLevel : ℝ → ℕ}
    {levelReward : ℕ → ℝ} {effort : α → ℝ}
    (hpost_actual :
      ∀ x, rankLevel (rankOfEffort x (effort x)) =
        rankLevel (postRank x))
    {x y : α}
    (hbest_x :
      ∀ d,
        levelReward (rankLevel (rankOfEffort x d)) - cost d ≤
          levelReward (rankLevel (rankOfEffort x (effort x))) - cost (effort x))
    (hbest_y :
      ∀ d,
        levelReward (rankLevel (rankOfEffort y d)) - cost d ≤
          levelReward (rankLevel (rankOfEffort y (effort y))) - cost (effort y))
    {eToHigh eHighToLow : ℝ}
    (hx_dev :
      rankLevel (rankOfEffort x eToHigh) =
        rankLevel (postRank y))
    (hy_dev :
      rankLevel (rankOfEffort y eHighToLow) =
        rankLevel (postRank x)) :
    levelReward (rankLevel (postRank x)) - cost (effort x) ≥
        levelReward (rankLevel (postRank y)) - cost eToHigh ∧
      levelReward (rankLevel (postRank y)) - cost (effort y) ≥
        levelReward (rankLevel (postRank x)) - cost eHighToLow := by
  constructor
  · simpa [hpost_actual x, hx_dev] using hbest_x eToHigh
  · simpa [hpost_actual y, hy_dev] using hbest_y eHighToLow

theorem source_rank_best_response_pairwise_inequalities_of_pointwise_at
    {α : Type*}
    {cost : ℝ → ℝ} {rankOfEffort : α → ℝ → ℝ}
    {postRank : α → ℝ} {rankLevel : ℝ → ℕ}
    {levelReward : ℕ → ℝ} {effort : α → ℝ}
    {x y : α}
    (hpost_actual_x :
      rankLevel (rankOfEffort x (effort x)) = rankLevel (postRank x))
    (hpost_actual_y :
      rankLevel (rankOfEffort y (effort y)) = rankLevel (postRank y))
    (hbest_x :
      ∀ d,
        levelReward (rankLevel (rankOfEffort x d)) - cost d ≤
          levelReward (rankLevel (rankOfEffort x (effort x))) - cost (effort x))
    (hbest_y :
      ∀ d,
        levelReward (rankLevel (rankOfEffort y d)) - cost d ≤
          levelReward (rankLevel (rankOfEffort y (effort y))) - cost (effort y))
    {eToHigh eHighToLow : ℝ}
    (hx_dev :
      rankLevel (rankOfEffort x eToHigh) =
        rankLevel (postRank y))
    (hy_dev :
      rankLevel (rankOfEffort y eHighToLow) =
        rankLevel (postRank x)) :
    levelReward (rankLevel (postRank x)) - cost (effort x) ≥
        levelReward (rankLevel (postRank y)) - cost eToHigh ∧
      levelReward (rankLevel (postRank y)) - cost (effort y) ≥
        levelReward (rankLevel (postRank x)) - cost eHighToLow := by
  constructor
  · simpa [hpost_actual_x, hx_dev] using hbest_x eToHigh
  · simpa [hpost_actual_y, hy_dev] using hbest_y eHighToLow

theorem source_rank_best_response_pairwise_inequalities
    {α : Type*}
    {cost : ℝ → ℝ} {rankOfEffort : α → ℝ → ℝ}
    {postRank : α → ℝ} {rankLevel : ℝ → ℕ}
    {levelReward : ℕ → ℝ} {effort : α → ℝ}
    (hbest :
      SourceRankBestResponse cost rankOfEffort rankLevel levelReward effort)
    (hpost_actual :
      ∀ x, rankLevel (rankOfEffort x (effort x)) =
        rankLevel (postRank x))
    {x y : α} {eToHigh eHighToLow : ℝ}
    (hx_dev :
      rankLevel (rankOfEffort x eToHigh) =
        rankLevel (postRank y))
    (hy_dev :
      rankLevel (rankOfEffort y eHighToLow) =
        rankLevel (postRank x)) :
    levelReward (rankLevel (postRank x)) - cost (effort x) ≥
        levelReward (rankLevel (postRank y)) - cost eToHigh ∧
      levelReward (rankLevel (postRank y)) - cost (effort y) ≥
        levelReward (rankLevel (postRank x)) - cost eHighToLow := by
  exact source_rank_best_response_pairwise_inequalities_of_pointwise
    hpost_actual
    (fun d => hbest x d)
    (fun d => hbest y d)
    hx_dev hy_dev

/--
Best-response bridge using reward reachability rather than exact deviation
rank equality.  If the deviation effort for `x` reaches at least `y`'s
realized reward, and symmetrically for `y`, source best response supplies the
two payoff inequalities used in the rank-preservation contradiction.
-/
theorem source_rank_best_response_pairwise_inequalities_of_reward_reach
    {α : Type*}
    {cost : ℝ → ℝ} {rankOfEffort : α → ℝ → ℝ}
    {postRank : α → ℝ} {rankLevel : ℝ → ℕ}
    {levelReward : ℕ → ℝ} {effort : α → ℝ}
    (hbest :
      SourceRankBestResponse cost rankOfEffort rankLevel levelReward effort)
    (hpost_actual :
      ∀ x, rankLevel (rankOfEffort x (effort x)) =
        rankLevel (postRank x))
    {x y : α} {eToHigh eHighToLow : ℝ}
    (hx_reaches :
      levelReward (rankLevel (postRank y)) ≤
        levelReward (rankLevel (rankOfEffort x eToHigh)))
    (hy_reaches :
      levelReward (rankLevel (postRank x)) ≤
        levelReward (rankLevel (rankOfEffort y eHighToLow))) :
    levelReward (rankLevel (postRank x)) - cost (effort x) ≥
        levelReward (rankLevel (postRank y)) - cost eToHigh ∧
      levelReward (rankLevel (postRank y)) - cost (effort y) ≥
        levelReward (rankLevel (postRank x)) - cost eHighToLow := by
  constructor
  · calc
      levelReward (rankLevel (postRank x)) - cost (effort x)
          = levelReward (rankLevel (rankOfEffort x (effort x))) -
              cost (effort x) := by
                rw [hpost_actual x]
      _ ≥ levelReward (rankLevel (rankOfEffort x eToHigh)) -
            cost eToHigh := hbest x eToHigh
      _ ≥ levelReward (rankLevel (postRank y)) - cost eToHigh := by
            linarith
  · calc
      levelReward (rankLevel (postRank y)) - cost (effort y)
          = levelReward (rankLevel (rankOfEffort y (effort y))) -
              cost (effort y) := by
                rw [hpost_actual y]
      _ ≥ levelReward (rankLevel (rankOfEffort y eHighToLow)) -
            cost eHighToLow := hbest y eHighToLow
      _ ≥ levelReward (rankLevel (postRank x)) - cost eHighToLow := by
            linarith

/--
Pointwise-at version of the reward-reach best-response bridge, used when the
best-response and realized-post-rank facts are available only off a null set.
-/
theorem source_rank_best_response_pairwise_inequalities_of_reward_reach_at
    {α : Type*}
    {cost : ℝ → ℝ} {rankOfEffort : α → ℝ → ℝ}
    {postRank : α → ℝ} {rankLevel : ℝ → ℕ}
    {levelReward : ℕ → ℝ} {effort : α → ℝ}
    {x y : α} {eToHigh eHighToLow : ℝ}
    (hpost_actual_x :
      rankLevel (rankOfEffort x (effort x)) = rankLevel (postRank x))
    (hpost_actual_y :
      rankLevel (rankOfEffort y (effort y)) = rankLevel (postRank y))
    (hbest_x :
      ∀ d,
        levelReward (rankLevel (rankOfEffort x d)) - cost d ≤
          levelReward (rankLevel (rankOfEffort x (effort x))) - cost (effort x))
    (hbest_y :
      ∀ d,
        levelReward (rankLevel (rankOfEffort y d)) - cost d ≤
          levelReward (rankLevel (rankOfEffort y (effort y))) - cost (effort y))
    (hx_reaches :
      levelReward (rankLevel (postRank y)) ≤
        levelReward (rankLevel (rankOfEffort x eToHigh)))
    (hy_reaches :
      levelReward (rankLevel (postRank x)) ≤
        levelReward (rankLevel (rankOfEffort y eHighToLow))) :
    levelReward (rankLevel (postRank x)) - cost (effort x) ≥
        levelReward (rankLevel (postRank y)) - cost eToHigh ∧
      levelReward (rankLevel (postRank y)) - cost (effort y) ≥
        levelReward (rankLevel (postRank x)) - cost eHighToLow := by
  constructor
  · calc
      levelReward (rankLevel (postRank x)) - cost (effort x)
          = levelReward (rankLevel (rankOfEffort x (effort x))) -
              cost (effort x) := by
                rw [hpost_actual_x]
      _ ≥ levelReward (rankLevel (rankOfEffort x eToHigh)) -
            cost eToHigh := hbest_x eToHigh
      _ ≥ levelReward (rankLevel (postRank y)) - cost eToHigh := by
            linarith
  · calc
      levelReward (rankLevel (postRank y)) - cost (effort y)
          = levelReward (rankLevel (rankOfEffort y (effort y))) -
              cost (effort y) := by
                rw [hpost_actual_y]
      _ ≥ levelReward (rankLevel (rankOfEffort y eHighToLow)) -
            cost eHighToLow := hbest_y eHighToLow
      _ ≥ levelReward (rankLevel (postRank x)) - cost eHighToLow := by
            linarith

/--
Tie-breaking/source-rank consequence in primitive equal-score form: if equal
scores always receive the same reward level, then the deviation efforts
constructed to match another applicant's score land in that applicant's
post-effort reward level.
-/
theorem deviation_rank_levels_of_equal_score_reward_levels
    {α : Type*} {g : ℝ → ℝ}
    {rankOfEffort : α → ℝ → ℝ} {postRank : α → ℝ}
    {rankLevel : ℝ → ℕ}
    {skill score effort : α → ℝ}
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hpost_actual :
      ∀ x, rankLevel (rankOfEffort x (effort x)) =
        rankLevel (postRank x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    {x y : α} {eToHigh eHighToLow : ℝ}
    (htoHigh : score y = g eToHigh * skill x)
    (hhighToLow : score x = g eHighToLow * skill y) :
    rankLevel (rankOfEffort x eToHigh) =
        rankLevel (postRank y) ∧
      rankLevel (rankOfEffort y eHighToLow) =
        rankLevel (postRank x) := by
  constructor
  · have heq :
        g eToHigh * skill x = g (effort y) * skill y := by
      rw [← htoHigh, hscore_eq y]
    exact (hequal_score_level x y eToHigh (effort y) heq).trans
      (hpost_actual y)
  · have heq :
        g eHighToLow * skill y = g (effort x) * skill x := by
      rw [← hhighToLow, hscore_eq x]
    exact (hequal_score_level y x eHighToLow (effort x) heq).trans
      (hpost_actual x)

theorem deviation_rank_levels_of_equal_score_reward_levels_at
    {α : Type*} {g : ℝ → ℝ}
    {rankOfEffort : α → ℝ → ℝ} {postRank : α → ℝ}
    {rankLevel : ℝ → ℕ}
    {skill score effort : α → ℝ}
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    {x y : α}
    (hpost_actual_x :
      rankLevel (rankOfEffort x (effort x)) = rankLevel (postRank x))
    (hpost_actual_y :
      rankLevel (rankOfEffort y (effort y)) = rankLevel (postRank y))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    {eToHigh eHighToLow : ℝ}
    (htoHigh : score y = g eToHigh * skill x)
    (hhighToLow : score x = g eHighToLow * skill y) :
    rankLevel (rankOfEffort x eToHigh) =
        rankLevel (postRank y) ∧
      rankLevel (rankOfEffort y eHighToLow) =
        rankLevel (postRank x) := by
  constructor
  · have heq :
        g eToHigh * skill x = g (effort y) * skill y := by
      rw [← htoHigh, hscore_eq y]
    exact (hequal_score_level x y eToHigh (effort y) heq).trans
      hpost_actual_y
  · have heq :
        g eHighToLow * skill y = g (effort x) * skill x := by
      rw [← hhighToLow, hscore_eq x]
    exact (hequal_score_level y x eHighToLow (effort x) heq).trans
      hpost_actual_x

/--
If the score-induced post-effort reward level is monotone in score, then a
strict post-effort reward-level ordering forces the same strict ordering of
scores.  This is the score-order fact used in the rank-preservation
contradiction, separated from the source ranking/tie-breaking construction.
-/
theorem score_strict_of_strict_post_level_and_score_level_mono
    {α : Type*} (postRank : α → ℝ) (rankLevel : ℝ → ℕ) (score : α → ℝ)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (postRank y) ≤ rankLevel (postRank x)) :
    ∀ x y, rankLevel (postRank x) < rankLevel (postRank y) →
      score x < score y := by
  intro x y hlevel
  by_contra hnot
  have hyx : score y ≤ score x := le_of_not_gt hnot
  exact not_lt_of_ge (hscore_level_mono x y hyx) hlevel

/--
If source skill is a strictly increasing function of pre-effort rank, and
pre-effort reward-level order refines pre-effort rank order, then the skill
ordering used in the rank-preservation contradiction follows from source
model primitives.
-/
theorem skill_strict_of_strict_pre_level_and_strict_rank_skill
    {α : Type*} (preRank : α → ℝ) (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ) (skill : α → ℝ)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x) :
    ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
      skill y < skill x := by
  intro x y hlevel
  rw [hskill_eq y, hskill_eq x]
  exact hrankSkill_strict (hpre_level_rank_order x y hlevel)

theorem bounded_rank_levels_ae_eq_of_pairwise_inversion_contradiction_and_common_rank_distribution
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    (K : ℕ) (preRank postRank : α → ℝ) (rankLevel : ℝ → ℕ)
    {reference : Measure ℝ}
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound : ∀ x, rankLevel (postRank x) < K)
    (hInversionContr :
      ∀ x y,
        rankLevel (preRank y) < rankLevel (preRank x) →
        rankLevel (postRank x) < rankLevel (postRank y) →
        False)
    (hpreRank_meas : Measurable preRank)
    (hpostRank_meas : Measurable postRank)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist : Measure.map preRank μ = reference)
    (hpost_dist : Measure.map postRank μ = reference) :
    (fun x => rankLevel (postRank x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) :=
  bounded_rank_levels_ae_eq_of_pairwise_inversion_contradiction_and_equal_rank_distribution
    K preRank postRank rankLevel hpre_bound hpost_bound hInversionContr
    hpreRank_meas hpostRank_meas hrankLevel_meas
    (rank_distribution_eq_of_common_reference_distribution hpre_dist hpost_dist)

theorem bounded_rank_levels_ae_eq_of_pairwise_inversion_contradiction_and_equal_rank_tail_measures
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    (K : ℕ) (preRank postRank : α → ℝ) (rankLevel : ℝ → ℕ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound : ∀ x, rankLevel (postRank x) < K)
    (hInversionContr :
      ∀ x y,
        rankLevel (preRank y) < rankLevel (preRank x) →
        rankLevel (postRank x) < rankLevel (postRank y) →
        False)
    (hpreRank_meas : Measurable preRank)
    (hpostRank_meas : Measurable postRank)
    (hrankLevel_meas : Measurable rankLevel)
    (htail_measure :
      ∀ t, t < K →
        μ {x | t ≤ rankLevel (preRank x)} =
          μ {x | t ≤ rankLevel (postRank x)}) :
    (fun x => rankLevel (postRank x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  refine bounded_reward_levels_ae_eq_of_no_inversion_and_equal_tail_measures
    K (fun x => rankLevel (preRank x)) (fun x => rankLevel (postRank x))
    hpre_bound hpost_bound ?_ htail_measure ?_ ?_ ?_ ?_
  · intro x y hpre
    by_contra hnot
    exact hInversionContr x y hpre (Nat.lt_of_not_ge hnot)
  · intro t _ht
    have htail_meas : MeasurableSet {n : ℕ | t ≤ n} := by
      simpa using (measurableSet_Ici : MeasurableSet (Set.Ici t))
    exact ((hrankLevel_meas.comp hpreRank_meas) htail_meas).nullMeasurableSet
  · intro t _ht
    have htail_meas : MeasurableSet {n : ℕ | t ≤ n} := by
      simpa using (measurableSet_Ici : MeasurableSet (Set.Ici t))
    exact ((hrankLevel_meas.comp hpostRank_meas) htail_meas).nullMeasurableSet
  · intro t _ht
    exact measure_ne_top μ {x | t ≤ rankLevel (preRank x)}
  · intro t _ht
    exact measure_ne_top μ {x | t ≤ rankLevel (postRank x)}

theorem bounded_rank_levels_ae_eq_of_pairwise_inversion_contradiction_off_null_and_equal_rank_tail_measures
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    (K : ℕ) (preRank postRank : α → ℝ) (rankLevel : ℝ → ℕ)
    {exception : Set α}
    (hexception : μ exception = 0)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound : ∀ x, rankLevel (postRank x) < K)
    (hInversionContr :
      ∀ x y, x ∉ exception → y ∉ exception →
        rankLevel (preRank y) < rankLevel (preRank x) →
        rankLevel (postRank x) < rankLevel (postRank y) →
        False)
    (hpreRank_meas : Measurable preRank)
    (hpostRank_meas : Measurable postRank)
    (hrankLevel_meas : Measurable rankLevel)
    (htail_measure :
      ∀ t, t < K →
        μ {x | t ≤ rankLevel (preRank x)} =
          μ {x | t ≤ rankLevel (postRank x)}) :
    (fun x => rankLevel (postRank x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  refine bounded_reward_levels_ae_eq_of_no_inversion_off_null_and_equal_tail_measures
    K (fun x => rankLevel (preRank x)) (fun x => rankLevel (postRank x))
    hexception hpre_bound hpost_bound ?_ htail_measure ?_ ?_ ?_ ?_
  · intro x y hx hy hpre
    by_contra hnot
    exact hInversionContr x y hx hy hpre (Nat.lt_of_not_ge hnot)
  · intro t _ht
    have htail_meas : MeasurableSet {n : ℕ | t ≤ n} := by
      simpa using (measurableSet_Ici : MeasurableSet (Set.Ici t))
    exact ((hrankLevel_meas.comp hpreRank_meas) htail_meas).nullMeasurableSet
  · intro t _ht
    have htail_meas : MeasurableSet {n : ℕ | t ≤ n} := by
      simpa using (measurableSet_Ici : MeasurableSet (Set.Ici t))
    exact ((hrankLevel_meas.comp hpostRank_meas) htail_meas).nullMeasurableSet
  · intro t _ht
    exact measure_ne_top μ {x | t ≤ rankLevel (preRank x)}
  · intro t _ht
    exact measure_ne_top μ {x | t ≤ rankLevel (postRank x)}

theorem rank_preservation_ae_eq_of_source_pairwise_witnesses_and_equal_rank_distribution
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank postRank : α → ℝ) (rankLevel : ℝ → ℕ)
    (skill score effort : α → ℝ) (levelReward : ℕ → ℝ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound : ∀ x, rankLevel (postRank x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_mono : Monotone g)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_pre_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        skill y < skill x)
    (hscore_post_order :
      ∀ x y, rankLevel (postRank x) < rankLevel (postRank y) →
        score x < score y)
    (heq_score : ∀ x, g (effort x) = score x / skill x)
    (hpair :
      ∀ x y,
        rankLevel (preRank y) < rankLevel (preRank x) →
        rankLevel (postRank x) < rankLevel (postRank y) →
          ∃ eToHigh eHighToLow,
            g eToHigh = score y / skill x ∧
            g eHighToLow = score x / skill y ∧
            e0 ≤ effort x ∧
            effort x < eToHigh ∧
            eHighToLow < effort y ∧
            effort x ≤ eHighToLow ∧
            eToHigh ≤ effort y ∧
            levelReward (rankLevel (postRank x)) - cost (effort x) ≥
              levelReward (rankLevel (postRank y)) - cost eToHigh ∧
            levelReward (rankLevel (postRank y)) - cost (effort y) ≥
              levelReward (rankLevel (postRank x)) - cost eHighToLow)
    (hpreRank_meas : Measurable preRank)
    (hpostRank_meas : Measurable postRank)
    (hrankLevel_meas : Measurable rankLevel)
    (hrank_dist : Measure.map preRank μ = Measure.map postRank μ) :
    (fun x => rankLevel (postRank x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  refine bounded_rank_levels_ae_eq_of_pairwise_inversion_contradiction_and_equal_rank_distribution
    K preRank postRank rankLevel hpre_bound hpost_bound ?_
    hpreRank_meas hpostRank_meas hrankLevel_meas hrank_dist
  intro x y hpre hpost
  rcases hpair x y hpre hpost with
    ⟨eToHigh, eHighToLow, htoHigh_score, hhighToLow_score, he0,
      he_toHigh, hhighToLow_high, he_highToLow, htoHigh_high,
      hlow_best, hhigh_best⟩
  exact rank_preservation_no_inversion_source_score_contradiction
    (cost := cost) (g := g)
    (skillLow := skill y) (skillHigh := skill x)
    (scoreLow := score x) (scoreHigh := score y)
    (e0 := e0) (e := effort x) (eToHigh := eToHigh)
    (eHighToLow := eHighToLow) (eHigh := effort y)
    (rewardLow := levelReward (rankLevel (postRank x)))
    (rewardHigh := levelReward (rankLevel (postRank y)))
    hcost_conv hcost_strict hg_conc hg_mono
    (hskill_pos y)
    (hskill_pre_order x y hpre)
    (hscore_post_order x y hpost)
    (heq_score x)
    htoHigh_score
    hhighToLow_score
    (heq_score y)
    he0 he_toHigh hhighToLow_high he_highToLow htoHigh_high
    hlow_best hhigh_best

/--
Same rank-preservation bridge as
`rank_preservation_ae_eq_of_source_pairwise_witnesses_and_equal_rank_distribution`,
but with the score equations in the paper's multiplicative form
`score = g(effort) * skill`.  The two deviation efforts are constructed by
continuity and strict monotonicity of `g`; the caller supplies only the
source best-response inequalities for those deviations.
-/
theorem rank_preservation_ae_eq_of_source_pairwise_multiplicative_witnesses_and_equal_rank_distribution
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank postRank : α → ℝ) (rankLevel : ℝ → ℕ)
    (skill score effort : α → ℝ) (levelReward : ℕ → ℝ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound : ∀ x, rankLevel (postRank x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_pre_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        skill y < skill x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (postRank y) ≤ rankLevel (postRank x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hbest :
      ∀ x y eToHigh eHighToLow,
        rankLevel (preRank y) < rankLevel (preRank x) →
        rankLevel (postRank x) < rankLevel (postRank y) →
          score y = g eToHigh * skill x →
          score x = g eHighToLow * skill y →
            levelReward (rankLevel (postRank x)) - cost (effort x) ≥
              levelReward (rankLevel (postRank y)) - cost eToHigh ∧
            levelReward (rankLevel (postRank y)) - cost (effort y) ≥
              levelReward (rankLevel (postRank x)) - cost eHighToLow)
    (hpreRank_meas : Measurable preRank)
    (hpostRank_meas : Measurable postRank)
    (hrankLevel_meas : Measurable rankLevel)
    (hrank_dist : Measure.map preRank μ = Measure.map postRank μ) :
    (fun x => rankLevel (postRank x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  let hscore_post_order :=
    score_strict_of_strict_post_level_and_score_level_mono
      postRank rankLevel score hscore_level_mono
  refine rank_preservation_ae_eq_of_source_pairwise_witnesses_and_equal_rank_distribution
    K preRank postRank rankLevel skill score effort levelReward
    hpre_bound hpost_bound hcost_conv hcost_strict hg_conc hg_strict.monotone
    hskill_pos hskill_pre_order hscore_post_order ?_ ?_
    hpreRank_meas hpostRank_meas hrankLevel_meas hrank_dist
  · intro x
    rw [hscore_eq x]
    field_simp [ne_of_gt (hskill_pos x)]
  · intro x y hpre hpost
    have hscore_x_nonneg : 0 ≤ score x := by
      rw [hscore_eq x]
      exact mul_nonneg (hg_nonneg (effort x)) (le_of_lt (hskill_pos x))
    rcases source_actual_scores_yield_deviation_efforts
        (g := g) (skillLow := skill y) (skillHigh := skill x)
        (scoreLow := score x) (scoreHigh := score y)
        (e := effort x) (eHigh := effort y)
        hg_cont hg_strict (hskill_pos y) (hskill_pre_order x y hpre)
        hscore_x_nonneg (hscore_post_order x y hpost)
        (hscore_eq x) (hscore_eq y) with
      ⟨eToHigh, eHighToLow, htoHigh_mul, hhighToLow_mul,
        he_toHigh, hhighToLow_high, he_highToLow, htoHigh_high⟩
    rcases hbest x y eToHigh eHighToLow hpre hpost
        htoHigh_mul hhighToLow_mul with
      ⟨hlow_best, hhigh_best⟩
    refine ⟨eToHigh, eHighToLow, ?_, ?_, heffort_feasible x, he_toHigh,
      hhighToLow_high, he_highToLow, htoHigh_high, hlow_best,
      hhigh_best⟩
    · rw [htoHigh_mul]
      field_simp [ne_of_gt (hskill_pos x)]
    · rw [hhighToLow_mul]
      field_simp [ne_of_gt (hskill_pos y)]

theorem rank_preservation_ae_eq_of_source_pairwise_multiplicative_witnesses_and_equal_rank_tail_measures
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank postRank : α → ℝ) (rankLevel : ℝ → ℕ)
    (skill score effort : α → ℝ) (levelReward : ℕ → ℝ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound : ∀ x, rankLevel (postRank x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_pre_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        skill y < skill x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (postRank y) ≤ rankLevel (postRank x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hbest :
      ∀ x y eToHigh eHighToLow,
        rankLevel (preRank y) < rankLevel (preRank x) →
        rankLevel (postRank x) < rankLevel (postRank y) →
          score y = g eToHigh * skill x →
          score x = g eHighToLow * skill y →
            levelReward (rankLevel (postRank x)) - cost (effort x) ≥
              levelReward (rankLevel (postRank y)) - cost eToHigh ∧
            levelReward (rankLevel (postRank y)) - cost (effort y) ≥
              levelReward (rankLevel (postRank x)) - cost eHighToLow)
    (hpreRank_meas : Measurable preRank)
    (hpostRank_meas : Measurable postRank)
    (hrankLevel_meas : Measurable rankLevel)
    (htail_measure :
      ∀ t, t < K →
        μ {x | t ≤ rankLevel (preRank x)} =
          μ {x | t ≤ rankLevel (postRank x)}) :
    (fun x => rankLevel (postRank x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  let hscore_post_order :=
    score_strict_of_strict_post_level_and_score_level_mono
      postRank rankLevel score hscore_level_mono
  refine bounded_rank_levels_ae_eq_of_pairwise_inversion_contradiction_and_equal_rank_tail_measures
    K preRank postRank rankLevel hpre_bound hpost_bound ?_
    hpreRank_meas hpostRank_meas hrankLevel_meas htail_measure
  intro x y hpre hpost
  have hscore_x_nonneg : 0 ≤ score x := by
    rw [hscore_eq x]
    exact mul_nonneg (hg_nonneg (effort x)) (le_of_lt (hskill_pos x))
  rcases source_actual_scores_yield_deviation_efforts
      (g := g) (skillLow := skill y) (skillHigh := skill x)
      (scoreLow := score x) (scoreHigh := score y)
      (e := effort x) (eHigh := effort y)
      hg_cont hg_strict (hskill_pos y) (hskill_pre_order x y hpre)
      hscore_x_nonneg (hscore_post_order x y hpost)
      (hscore_eq x) (hscore_eq y) with
    ⟨eToHigh, eHighToLow, htoHigh_mul, hhighToLow_mul,
      he_toHigh, hhighToLow_high, he_highToLow, htoHigh_high⟩
  rcases hbest x y eToHigh eHighToLow hpre hpost
      htoHigh_mul hhighToLow_mul with
    ⟨hlow_best, hhigh_best⟩
  have htoHigh_score_div : g eToHigh = score y / skill x := by
    rw [htoHigh_mul]
    field_simp [ne_of_gt (hskill_pos x)]
  have hhighToLow_score_div : g eHighToLow = score x / skill y := by
    rw [hhighToLow_mul]
    field_simp [ne_of_gt (hskill_pos y)]
  exact rank_preservation_no_inversion_source_score_contradiction
    (cost := cost) (g := g)
    (skillLow := skill y) (skillHigh := skill x)
    (scoreLow := score x) (scoreHigh := score y)
    (e0 := e0) (e := effort x) (eToHigh := eToHigh)
    (eHighToLow := eHighToLow) (eHigh := effort y)
    (rewardLow := levelReward (rankLevel (postRank x)))
    (rewardHigh := levelReward (rankLevel (postRank y)))
    hcost_conv hcost_strict hg_conc hg_strict.monotone
    (hskill_pos y)
    (hskill_pre_order x y hpre)
    (hscore_post_order x y hpost)
    (by
      rw [hscore_eq x]
      field_simp [ne_of_gt (hskill_pos x)])
    htoHigh_score_div
    hhighToLow_score_div
    (by
      rw [hscore_eq y]
      field_simp [ne_of_gt (hskill_pos y)])
    (heffort_feasible x) he_toHigh hhighToLow_high he_highToLow
    htoHigh_high hlow_best hhigh_best

theorem rank_preservation_ae_eq_of_source_pairwise_multiplicative_witnesses_off_null_and_equal_rank_tail_measures
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank postRank : α → ℝ) (rankLevel : ℝ → ℕ)
    (skill score effort : α → ℝ) (levelReward : ℕ → ℝ)
    {exception : Set α}
    (hexception : μ exception = 0)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound : ∀ x, rankLevel (postRank x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_pre_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        skill y < skill x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (postRank y) ≤ rankLevel (postRank x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hbest :
      ∀ x y eToHigh eHighToLow,
        x ∉ exception → y ∉ exception →
        rankLevel (preRank y) < rankLevel (preRank x) →
        rankLevel (postRank x) < rankLevel (postRank y) →
          score y = g eToHigh * skill x →
          score x = g eHighToLow * skill y →
            levelReward (rankLevel (postRank x)) - cost (effort x) ≥
              levelReward (rankLevel (postRank y)) - cost eToHigh ∧
            levelReward (rankLevel (postRank y)) - cost (effort y) ≥
              levelReward (rankLevel (postRank x)) - cost eHighToLow)
    (hpreRank_meas : Measurable preRank)
    (hpostRank_meas : Measurable postRank)
    (hrankLevel_meas : Measurable rankLevel)
    (htail_measure :
      ∀ t, t < K →
        μ {x | t ≤ rankLevel (preRank x)} =
          μ {x | t ≤ rankLevel (postRank x)}) :
    (fun x => rankLevel (postRank x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  let hscore_post_order :=
    score_strict_of_strict_post_level_and_score_level_mono
      postRank rankLevel score hscore_level_mono
  refine bounded_rank_levels_ae_eq_of_pairwise_inversion_contradiction_off_null_and_equal_rank_tail_measures
    K preRank postRank rankLevel hexception hpre_bound hpost_bound ?_
    hpreRank_meas hpostRank_meas hrankLevel_meas htail_measure
  intro x y hx hy hpre hpost
  have hscore_x_nonneg : 0 ≤ score x := by
    rw [hscore_eq x]
    exact mul_nonneg (hg_nonneg (effort x)) (le_of_lt (hskill_pos x))
  rcases source_actual_scores_yield_deviation_efforts
      (g := g) (skillLow := skill y) (skillHigh := skill x)
      (scoreLow := score x) (scoreHigh := score y)
      (e := effort x) (eHigh := effort y)
      hg_cont hg_strict (hskill_pos y) (hskill_pre_order x y hpre)
      hscore_x_nonneg (hscore_post_order x y hpost)
      (hscore_eq x) (hscore_eq y) with
    ⟨eToHigh, eHighToLow, htoHigh_mul, hhighToLow_mul,
      he_toHigh, hhighToLow_high, he_highToLow, htoHigh_high⟩
  rcases hbest x y eToHigh eHighToLow hx hy hpre hpost
      htoHigh_mul hhighToLow_mul with
    ⟨hlow_best, hhigh_best⟩
  have htoHigh_score_div : g eToHigh = score y / skill x := by
    rw [htoHigh_mul]
    field_simp [ne_of_gt (hskill_pos x)]
  have hhighToLow_score_div : g eHighToLow = score x / skill y := by
    rw [hhighToLow_mul]
    field_simp [ne_of_gt (hskill_pos y)]
  exact rank_preservation_no_inversion_source_score_contradiction
    (cost := cost) (g := g)
    (skillLow := skill y) (skillHigh := skill x)
    (scoreLow := score x) (scoreHigh := score y)
    (e0 := e0) (e := effort x) (eToHigh := eToHigh)
    (eHighToLow := eHighToLow) (eHigh := effort y)
    (rewardLow := levelReward (rankLevel (postRank x)))
    (rewardHigh := levelReward (rankLevel (postRank y)))
    hcost_conv hcost_strict hg_conc hg_strict.monotone
    (hskill_pos y)
    (hskill_pre_order x y hpre)
    (hscore_post_order x y hpost)
    (by
      rw [hscore_eq x]
      field_simp [ne_of_gt (hskill_pos x)])
    htoHigh_score_div
    hhighToLow_score_div
    (by
      rw [hscore_eq y]
      field_simp [ne_of_gt (hskill_pos y)])
    (heffort_feasible x) he_toHigh hhighToLow_high he_highToLow
    htoHigh_high hlow_best hhigh_best

/--
Source-equilibrium version of the rank-preservation bridge.  The source
best-response condition supplies the no-profitable-deviation inequalities; the
remaining explicit obligations say that the constructed deviation scores land
in the intended post-effort reward levels and that pre/post ranks have a common
reference distribution.
-/
theorem rank_preservation_ae_eq_of_source_equilibrium_deviation_rank_facts_and_common_distribution
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank postRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ)
    (skill score effort : α → ℝ) (levelReward : ℕ → ℝ)
    {reference : Measure ℝ}
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound : ∀ x, rankLevel (postRank x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (postRank y) ≤ rankLevel (postRank x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hbest :
      SourceRankBestResponse cost rankOfEffort rankLevel levelReward effort)
    (hpost_actual :
      ∀ x, rankLevel (rankOfEffort x (effort x)) =
        rankLevel (postRank x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hpostRank_meas : Measurable postRank)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist : Measure.map preRank μ = reference)
    (hpost_dist : Measure.map postRank μ = reference) :
    (fun x => rankLevel (postRank x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  refine rank_preservation_ae_eq_of_source_pairwise_multiplicative_witnesses_and_equal_rank_distribution
    K preRank postRank rankLevel skill score effort levelReward
    hpre_bound hpost_bound hcost_conv hcost_strict hg_conc hg_cont hg_strict
    hg_nonneg heffort_feasible hskill_pos
    (skill_strict_of_strict_pre_level_and_strict_rank_skill
      preRank rankLevel rankSkill skill hskill_eq hrankSkill_strict
      hpre_level_rank_order)
    hscore_level_mono hscore_eq ?_ hpreRank_meas hpostRank_meas hrankLevel_meas
    (rank_distribution_eq_of_common_reference_distribution hpre_dist hpost_dist)
  intro x y eToHigh eHighToLow hpre hpost htoHigh hhighToLow
  rcases deviation_rank_levels_of_equal_score_reward_levels
      hscore_eq hpost_actual hequal_score_level htoHigh hhighToLow with
    ⟨hx_dev, hy_dev⟩
  exact source_rank_best_response_pairwise_inequalities hbest hpost_actual
    hx_dev hy_dev

/--
Source-equilibrium rank-preservation bridge using reward reachability rather
than exact equal-score deviation ranks.  The source-specific obligation is
that whenever a deviation score reaches another applicant's actual score, the
deviation receives at least that applicant's realized reward.  This is the
formal shape of the edited appendix proof that avoids treating arbitrary
deviation ties as a hidden certificate.
-/
theorem rank_preservation_ae_eq_of_source_equilibrium_deviation_reward_facts_and_equal_rank_tail_measures
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank postRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ)
    (skill score effort : α → ℝ) (levelReward : ℕ → ℝ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound : ∀ x, rankLevel (postRank x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (postRank y) ≤ rankLevel (postRank x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hbest :
      SourceRankBestResponse cost rankOfEffort rankLevel levelReward effort)
    (hpost_actual :
      ∀ x, rankLevel (rankOfEffort x (effort x)) =
        rankLevel (postRank x))
    (hdeviation_reaches_reward :
      ∀ x y d, score y ≤ g d * skill x →
        levelReward (rankLevel (postRank y)) ≤
          levelReward (rankLevel (rankOfEffort x d)))
    (hpreRank_meas : Measurable preRank)
    (hpostRank_meas : Measurable postRank)
    (hrankLevel_meas : Measurable rankLevel)
    (htail_measure :
      ∀ t, t < K →
        μ {x | t ≤ rankLevel (preRank x)} =
          μ {x | t ≤ rankLevel (postRank x)}) :
    (fun x => rankLevel (postRank x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  refine rank_preservation_ae_eq_of_source_pairwise_multiplicative_witnesses_and_equal_rank_tail_measures
    K preRank postRank rankLevel skill score effort levelReward
    hpre_bound hpost_bound hcost_conv hcost_strict hg_conc hg_cont hg_strict
    hg_nonneg heffort_feasible hskill_pos
    (skill_strict_of_strict_pre_level_and_strict_rank_skill
      preRank rankLevel rankSkill skill hskill_eq hrankSkill_strict
      hpre_level_rank_order)
    hscore_level_mono hscore_eq ?_ hpreRank_meas hpostRank_meas
    hrankLevel_meas htail_measure
  intro x y eToHigh eHighToLow _hpre _hpost htoHigh hhighToLow
  exact source_rank_best_response_pairwise_inequalities_of_reward_reach
    hbest hpost_actual
    (hdeviation_reaches_reward x y eToHigh (le_of_eq htoHigh))
    (hdeviation_reaches_reward y x eHighToLow (le_of_eq hhighToLow))

/--
Reward-reachability follows from the source statement that a deviation reaches
at least another applicant's post-rank, provided reward levels are monotone in
rank.  This isolates the paper's semantic ranking obligation from the payoff
algebra.
-/
theorem deviation_reward_reach_of_rank_reach
    {α : Type*} {g : ℝ → ℝ}
    {rankOfEffort : α → ℝ → ℝ} {postRank : α → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {skill score : α → ℝ}
    (hrankLevel_mono : Monotone rankLevel)
    (hlevelReward_mono : Monotone levelReward)
    (hrank_reaches :
      ∀ x y d, score y ≤ g d * skill x →
        postRank y ≤ rankOfEffort x d) :
    ∀ x y d, score y ≤ g d * skill x →
      levelReward (rankLevel (postRank y)) ≤
        levelReward (rankLevel (rankOfEffort x d)) := by
  intro x y d hscore
  exact hlevelReward_mono (hrankLevel_mono (hrank_reaches x y d hscore))

/--
Source-equilibrium rank-preservation bridge using rank reachability: if any
deviation whose score reaches another applicant's actual score also reaches at
least that applicant's post-rank, monotone reward levels turn that into the
reward-reachability premise needed by the payoff contradiction.
-/
theorem rank_preservation_ae_eq_of_source_equilibrium_deviation_rank_reach_and_equal_rank_tail_measures
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank postRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ)
    (skill score effort : α → ℝ) (levelReward : ℕ → ℝ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound : ∀ x, rankLevel (postRank x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (postRank y) ≤ rankLevel (postRank x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hbest :
      SourceRankBestResponse cost rankOfEffort rankLevel levelReward effort)
    (hpost_actual :
      ∀ x, rankLevel (rankOfEffort x (effort x)) =
        rankLevel (postRank x))
    (hrankLevel_mono : Monotone rankLevel)
    (hlevelReward_mono : Monotone levelReward)
    (hrank_reaches :
      ∀ x y d, score y ≤ g d * skill x →
        postRank y ≤ rankOfEffort x d)
    (hpreRank_meas : Measurable preRank)
    (hpostRank_meas : Measurable postRank)
    (hrankLevel_meas : Measurable rankLevel)
    (htail_measure :
      ∀ t, t < K →
        μ {x | t ≤ rankLevel (preRank x)} =
          μ {x | t ≤ rankLevel (postRank x)}) :
    (fun x => rankLevel (postRank x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) :=
  rank_preservation_ae_eq_of_source_equilibrium_deviation_reward_facts_and_equal_rank_tail_measures
    K preRank postRank rankOfEffort rankLevel rankSkill skill score effort
    levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
    hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
    hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
    hbest hpost_actual
    (deviation_reward_reach_of_rank_reach
      hrankLevel_mono hlevelReward_mono hrank_reaches)
    hpreRank_meas hpostRank_meas hrankLevel_meas htail_measure

theorem rank_preservation_ae_eq_of_source_equilibrium_deviation_rank_facts_and_equal_rank_tail_measures
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank postRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ)
    (skill score effort : α → ℝ) (levelReward : ℕ → ℝ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound : ∀ x, rankLevel (postRank x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (postRank y) ≤ rankLevel (postRank x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hbest :
      SourceRankBestResponse cost rankOfEffort rankLevel levelReward effort)
    (hpost_actual :
      ∀ x, rankLevel (rankOfEffort x (effort x)) =
        rankLevel (postRank x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hpostRank_meas : Measurable postRank)
    (hrankLevel_meas : Measurable rankLevel)
    (htail_measure :
      ∀ t, t < K →
        μ {x | t ≤ rankLevel (preRank x)} =
          μ {x | t ≤ rankLevel (postRank x)}) :
    (fun x => rankLevel (postRank x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  refine rank_preservation_ae_eq_of_source_pairwise_multiplicative_witnesses_and_equal_rank_tail_measures
    K preRank postRank rankLevel skill score effort levelReward
    hpre_bound hpost_bound hcost_conv hcost_strict hg_conc hg_cont hg_strict
    hg_nonneg heffort_feasible hskill_pos
    (skill_strict_of_strict_pre_level_and_strict_rank_skill
      preRank rankLevel rankSkill skill hskill_eq hrankSkill_strict
      hpre_level_rank_order)
    hscore_level_mono hscore_eq ?_ hpreRank_meas hpostRank_meas hrankLevel_meas
    htail_measure
  intro x y eToHigh eHighToLow _hpre _hpost htoHigh hhighToLow
  rcases deviation_rank_levels_of_equal_score_reward_levels
      hscore_eq hpost_actual hequal_score_level htoHigh hhighToLow with
    ⟨hx_dev, hy_dev⟩
  exact source_rank_best_response_pairwise_inequalities hbest hpost_actual
    hx_dev hy_dev

theorem rank_preservation_ae_eq_of_source_equilibriumAE_deviation_rank_facts_and_equal_rank_tail_measures
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank postRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ)
    (skill score effort : α → ℝ) (levelReward : ℕ → ℝ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound : ∀ x, rankLevel (postRank x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (postRank y) ≤ rankLevel (postRank x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hbestAE :
      SourceRankBestResponseAE μ cost rankOfEffort rankLevel levelReward effort)
    (hpost_actual :
      ∀ x, rankLevel (rankOfEffort x (effort x)) =
        rankLevel (postRank x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hpostRank_meas : Measurable postRank)
    (hrankLevel_meas : Measurable rankLevel)
    (htail_measure :
      ∀ t, t < K →
        μ {x | t ≤ rankLevel (preRank x)} =
          μ {x | t ≤ rankLevel (postRank x)}) :
    (fun x => rankLevel (postRank x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  let bestAt : α → Prop := fun x =>
    ∀ d,
      levelReward (rankLevel (rankOfEffort x d)) - cost d ≤
        levelReward (rankLevel (rankOfEffort x (effort x))) - cost (effort x)
  let exception : Set α := {x | ¬ bestAt x}
  have hbest_ae : ∀ᵐ x ∂μ, bestAt x := by
    simpa [bestAt] using
      sourceRankBestResponseAE_best_response_ae hbestAE
  have hexception : μ exception = 0 := by
    simpa [exception] using MeasureTheory.ae_iff.mp hbest_ae
  refine rank_preservation_ae_eq_of_source_pairwise_multiplicative_witnesses_off_null_and_equal_rank_tail_measures
    K preRank postRank rankLevel skill score effort levelReward
    hexception hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
    hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos
    (skill_strict_of_strict_pre_level_and_strict_rank_skill
      preRank rankLevel rankSkill skill hskill_eq hrankSkill_strict
      hpre_level_rank_order)
    hscore_level_mono hscore_eq ?_ hpreRank_meas hpostRank_meas hrankLevel_meas
    htail_measure
  intro x y eToHigh eHighToLow hx hy _hpre _hpost htoHigh hhighToLow
  have hbest_x : bestAt x := by
    simpa [exception] using hx
  have hbest_y : bestAt y := by
    simpa [exception] using hy
  rcases deviation_rank_levels_of_equal_score_reward_levels
      hscore_eq hpost_actual hequal_score_level htoHigh hhighToLow with
    ⟨hx_dev, hy_dev⟩
  exact source_rank_best_response_pairwise_inequalities_of_pointwise
    hpost_actual hbest_x hbest_y hx_dev hy_dev

theorem rank_preservation_ae_eq_of_source_equilibriumAE_deviation_rank_facts_ae_post_actual_and_equal_rank_tail_measures
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank postRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ)
    (skill score effort : α → ℝ) (levelReward : ℕ → ℝ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound : ∀ x, rankLevel (postRank x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (postRank y) ≤ rankLevel (postRank x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hbestAE :
      SourceRankBestResponseAE μ cost rankOfEffort rankLevel levelReward effort)
    (hpost_actual_ae :
      ∀ᵐ x ∂μ,
        rankLevel (rankOfEffort x (effort x)) = rankLevel (postRank x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hpostRank_meas : Measurable postRank)
    (hrankLevel_meas : Measurable rankLevel)
    (htail_measure :
      ∀ t, t < K →
        μ {x | t ≤ rankLevel (preRank x)} =
          μ {x | t ≤ rankLevel (postRank x)}) :
    (fun x => rankLevel (postRank x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  let bestAt : α → Prop := fun x =>
    ∀ d,
      levelReward (rankLevel (rankOfEffort x d)) - cost d ≤
        levelReward (rankLevel (rankOfEffort x (effort x))) - cost (effort x)
  let postAt : α → Prop := fun x =>
    rankLevel (rankOfEffort x (effort x)) = rankLevel (postRank x)
  let exception : Set α := {x | ¬ bestAt x ∨ ¬ postAt x}
  have hbest_ae : ∀ᵐ x ∂μ, bestAt x := by
    simpa [bestAt] using
      sourceRankBestResponseAE_best_response_ae hbestAE
  have hpost_ae : ∀ᵐ x ∂μ, postAt x := by
    simpa [postAt] using hpost_actual_ae
  have hbest_zero : μ {x | ¬ bestAt x} = 0 :=
    MeasureTheory.ae_iff.mp hbest_ae
  have hpost_zero : μ {x | ¬ postAt x} = 0 :=
    MeasureTheory.ae_iff.mp hpost_ae
  have hexception : μ exception = 0 := by
    rw [show exception = {x | ¬ bestAt x} ∪ {x | ¬ postAt x} by
      ext x
      simp [exception]]
    exact measure_union_null_iff.mpr ⟨hbest_zero, hpost_zero⟩
  refine rank_preservation_ae_eq_of_source_pairwise_multiplicative_witnesses_off_null_and_equal_rank_tail_measures
    K preRank postRank rankLevel skill score effort levelReward
    hexception hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
    hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos
    (skill_strict_of_strict_pre_level_and_strict_rank_skill
      preRank rankLevel rankSkill skill hskill_eq hrankSkill_strict
      hpre_level_rank_order)
    hscore_level_mono hscore_eq ?_ hpreRank_meas hpostRank_meas hrankLevel_meas
    htail_measure
  intro x y eToHigh eHighToLow hx hy _hpre _hpost htoHigh hhighToLow
  have hx_good : bestAt x ∧ postAt x := by
    have hx_not : ¬ (¬ bestAt x ∨ ¬ postAt x) := by
      simpa [exception] using hx
    constructor
    · by_contra hbad
      exact hx_not (Or.inl hbad)
    · by_contra hbad
      exact hx_not (Or.inr hbad)
  have hy_good : bestAt y ∧ postAt y := by
    have hy_not : ¬ (¬ bestAt y ∨ ¬ postAt y) := by
      simpa [exception] using hy
    constructor
    · by_contra hbad
      exact hy_not (Or.inl hbad)
    · by_contra hbad
      exact hy_not (Or.inr hbad)
  rcases deviation_rank_levels_of_equal_score_reward_levels_at
      hscore_eq hx_good.2 hy_good.2 hequal_score_level htoHigh hhighToLow with
    ⟨hx_dev, hy_dev⟩
  exact source_rank_best_response_pairwise_inequalities_of_pointwise_at
    hx_good.2 hy_good.2 hx_good.1 hy_good.1 hx_dev hy_dev

/--
Almost-everywhere-post-rank variant of the source-equilibrium
rank-preservation bridge using reward reachability instead of exact deviation
rank equality.  This is the a.e. form needed by source models where realized
post-rank agreement can fail only on a null boundary set.
-/
theorem rank_preservation_ae_eq_of_source_equilibriumAE_deviation_reward_facts_ae_post_actual_and_equal_rank_tail_measures
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank postRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ)
    (skill score effort : α → ℝ) (levelReward : ℕ → ℝ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound : ∀ x, rankLevel (postRank x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (postRank y) ≤ rankLevel (postRank x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hbestAE :
      SourceRankBestResponseAE μ cost rankOfEffort rankLevel levelReward effort)
    (hpost_actual_ae :
      ∀ᵐ x ∂μ,
        rankLevel (rankOfEffort x (effort x)) = rankLevel (postRank x))
    (hdeviation_reaches_reward :
      ∀ x y d, score y ≤ g d * skill x →
        levelReward (rankLevel (postRank y)) ≤
          levelReward (rankLevel (rankOfEffort x d)))
    (hpreRank_meas : Measurable preRank)
    (hpostRank_meas : Measurable postRank)
    (hrankLevel_meas : Measurable rankLevel)
    (htail_measure :
      ∀ t, t < K →
        μ {x | t ≤ rankLevel (preRank x)} =
          μ {x | t ≤ rankLevel (postRank x)}) :
    (fun x => rankLevel (postRank x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  let bestAt : α → Prop := fun x =>
    ∀ d,
      levelReward (rankLevel (rankOfEffort x d)) - cost d ≤
        levelReward (rankLevel (rankOfEffort x (effort x))) - cost (effort x)
  let postAt : α → Prop := fun x =>
    rankLevel (rankOfEffort x (effort x)) = rankLevel (postRank x)
  let exception : Set α := {x | ¬ bestAt x ∨ ¬ postAt x}
  have hbest_ae : ∀ᵐ x ∂μ, bestAt x := by
    simpa [bestAt] using
      sourceRankBestResponseAE_best_response_ae hbestAE
  have hpost_ae : ∀ᵐ x ∂μ, postAt x := by
    simpa [postAt] using hpost_actual_ae
  have hbest_zero : μ {x | ¬ bestAt x} = 0 :=
    MeasureTheory.ae_iff.mp hbest_ae
  have hpost_zero : μ {x | ¬ postAt x} = 0 :=
    MeasureTheory.ae_iff.mp hpost_ae
  have hexception : μ exception = 0 := by
    rw [show exception = {x | ¬ bestAt x} ∪ {x | ¬ postAt x} by
      ext x
      simp [exception]]
    exact measure_union_null_iff.mpr ⟨hbest_zero, hpost_zero⟩
  refine rank_preservation_ae_eq_of_source_pairwise_multiplicative_witnesses_off_null_and_equal_rank_tail_measures
    K preRank postRank rankLevel skill score effort levelReward
    hexception hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
    hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos
    (skill_strict_of_strict_pre_level_and_strict_rank_skill
      preRank rankLevel rankSkill skill hskill_eq hrankSkill_strict
      hpre_level_rank_order)
    hscore_level_mono hscore_eq ?_ hpreRank_meas hpostRank_meas hrankLevel_meas
    htail_measure
  intro x y eToHigh eHighToLow hx hy _hpre _hpost htoHigh hhighToLow
  have hx_good : bestAt x ∧ postAt x := by
    have hx_not : ¬ (¬ bestAt x ∨ ¬ postAt x) := by
      simpa [exception] using hx
    constructor
    · by_contra hbad
      exact hx_not (Or.inl hbad)
    · by_contra hbad
      exact hx_not (Or.inr hbad)
  have hy_good : bestAt y ∧ postAt y := by
    have hy_not : ¬ (¬ bestAt y ∨ ¬ postAt y) := by
      simpa [exception] using hy
    constructor
    · by_contra hbad
      exact hy_not (Or.inl hbad)
    · by_contra hbad
      exact hy_not (Or.inr hbad)
  exact source_rank_best_response_pairwise_inequalities_of_reward_reach_at
    hx_good.2 hy_good.2 hx_good.1 hy_good.1
    (hdeviation_reaches_reward x y eToHigh (le_of_eq htoHigh))
    (hdeviation_reaches_reward y x eHighToLow (le_of_eq hhighToLow))

/--
Local-post variant of
`rank_preservation_ae_eq_of_source_equilibriumAE_deviation_reward_facts_ae_post_actual_and_equal_rank_tail_measures`.
The deviation-reward fact may use the target applicant's realized post-rank
equality, which is available off the same null set.
-/
theorem rank_preservation_ae_eq_of_source_equilibriumAE_deviation_reward_facts_local_post_actual_and_equal_rank_tail_measures
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank postRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ)
    (skill score effort : α → ℝ) (levelReward : ℕ → ℝ)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound : ∀ x, rankLevel (postRank x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (postRank y) ≤ rankLevel (postRank x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hbestAE :
      SourceRankBestResponseAE μ cost rankOfEffort rankLevel levelReward effort)
    (hpost_actual_ae :
      ∀ᵐ x ∂μ,
        rankLevel (rankOfEffort x (effort x)) = rankLevel (postRank x))
    (hdeviation_reaches_reward :
      ∀ x y d,
        rankLevel (rankOfEffort y (effort y)) = rankLevel (postRank y) →
        score y ≤ g d * skill x →
          levelReward (rankLevel (postRank y)) ≤
            levelReward (rankLevel (rankOfEffort x d)))
    (hpreRank_meas : Measurable preRank)
    (hpostRank_meas : Measurable postRank)
    (hrankLevel_meas : Measurable rankLevel)
    (htail_measure :
      ∀ t, t < K →
        μ {x | t ≤ rankLevel (preRank x)} =
          μ {x | t ≤ rankLevel (postRank x)}) :
    (fun x => rankLevel (postRank x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  let bestAt : α → Prop := fun x =>
    ∀ d,
      levelReward (rankLevel (rankOfEffort x d)) - cost d ≤
        levelReward (rankLevel (rankOfEffort x (effort x))) - cost (effort x)
  let postAt : α → Prop := fun x =>
    rankLevel (rankOfEffort x (effort x)) = rankLevel (postRank x)
  let exception : Set α := {x | ¬ bestAt x ∨ ¬ postAt x}
  have hbest_ae : ∀ᵐ x ∂μ, bestAt x := by
    simpa [bestAt] using
      sourceRankBestResponseAE_best_response_ae hbestAE
  have hpost_ae : ∀ᵐ x ∂μ, postAt x := by
    simpa [postAt] using hpost_actual_ae
  have hbest_zero : μ {x | ¬ bestAt x} = 0 :=
    MeasureTheory.ae_iff.mp hbest_ae
  have hpost_zero : μ {x | ¬ postAt x} = 0 :=
    MeasureTheory.ae_iff.mp hpost_ae
  have hexception : μ exception = 0 := by
    rw [show exception = {x | ¬ bestAt x} ∪ {x | ¬ postAt x} by
      ext x
      simp [exception]]
    exact measure_union_null_iff.mpr ⟨hbest_zero, hpost_zero⟩
  refine rank_preservation_ae_eq_of_source_pairwise_multiplicative_witnesses_off_null_and_equal_rank_tail_measures
    K preRank postRank rankLevel skill score effort levelReward
    hexception hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
    hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos
    (skill_strict_of_strict_pre_level_and_strict_rank_skill
      preRank rankLevel rankSkill skill hskill_eq hrankSkill_strict
      hpre_level_rank_order)
    hscore_level_mono hscore_eq ?_ hpreRank_meas hpostRank_meas hrankLevel_meas
    htail_measure
  intro x y eToHigh eHighToLow hx hy _hpre _hpost htoHigh hhighToLow
  have hx_good : bestAt x ∧ postAt x := by
    have hx_not : ¬ (¬ bestAt x ∨ ¬ postAt x) := by
      simpa [exception] using hx
    constructor
    · by_contra hbad
      exact hx_not (Or.inl hbad)
    · by_contra hbad
      exact hx_not (Or.inr hbad)
  have hy_good : bestAt y ∧ postAt y := by
    have hy_not : ¬ (¬ bestAt y ∨ ¬ postAt y) := by
      simpa [exception] using hy
    constructor
    · by_contra hbad
      exact hy_not (Or.inl hbad)
    · by_contra hbad
      exact hy_not (Or.inr hbad)
  exact source_rank_best_response_pairwise_inequalities_of_reward_reach_at
    hx_good.2 hy_good.2 hx_good.1 hy_good.1
    (hdeviation_reaches_reward x y eToHigh hy_good.2 (le_of_eq htoHigh))
    (hdeviation_reaches_reward y x eHighToLow hx_good.2 (le_of_eq hhighToLow))

theorem rank_preservation_ae_eq_of_source_equilibriumAE_deviation_rank_facts_and_common_distribution
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {cost g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank postRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ)
    (rankSkill : ℝ → ℝ)
    (skill score effort : α → ℝ) (levelReward : ℕ → ℝ)
    {reference : Measure ℝ}
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound : ∀ x, rankLevel (postRank x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) cost)
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (postRank y) ≤ rankLevel (postRank x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hbestAE :
      SourceRankBestResponseAE μ cost rankOfEffort rankLevel levelReward effort)
    (hpost_actual :
      ∀ x, rankLevel (rankOfEffort x (effort x)) =
        rankLevel (postRank x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hpostRank_meas : Measurable postRank)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist : Measure.map preRank μ = reference)
    (hpost_dist : Measure.map postRank μ = reference) :
    (fun x => rankLevel (postRank x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  have hrank_dist :
      Measure.map preRank μ = Measure.map postRank μ :=
    rank_distribution_eq_of_common_reference_distribution hpre_dist hpost_dist
  have hlevel_dist :
      Measure.map (fun x => rankLevel (preRank x)) μ =
        Measure.map (fun x => rankLevel (postRank x)) μ :=
    rewardLevel_distribution_eq_of_rank_distribution_eq
      hpreRank_meas hpostRank_meas hrankLevel_meas hrank_dist
  have htail_measure :
      ∀ t, t < K →
        μ {x | t ≤ rankLevel (preRank x)} =
          μ {x | t ≤ rankLevel (postRank x)} := by
    intro t _ht
    let tail : Set ℕ := {n | t ≤ n}
    have htail_meas : MeasurableSet tail := by
      simp [tail]
    have hpre :
        μ {x | t ≤ rankLevel (preRank x)} =
          Measure.map (fun x => rankLevel (preRank x)) μ tail := by
      change μ ((fun x => rankLevel (preRank x)) ⁻¹' tail) =
        Measure.map (fun x => rankLevel (preRank x)) μ tail
      exact (Measure.map_apply
        (hrankLevel_meas.comp hpreRank_meas) htail_meas).symm
    have hpost :
        μ {x | t ≤ rankLevel (postRank x)} =
          Measure.map (fun x => rankLevel (postRank x)) μ tail := by
      change μ ((fun x => rankLevel (postRank x)) ⁻¹' tail) =
        Measure.map (fun x => rankLevel (postRank x)) μ tail
      exact (Measure.map_apply
        (hrankLevel_meas.comp hpostRank_meas) htail_meas).symm
    rw [hpre, hpost, hlevel_dist]
  exact
    rank_preservation_ae_eq_of_source_equilibriumAE_deviation_rank_facts_and_equal_rank_tail_measures
      K preRank postRank rankOfEffort rankLevel rankSkill skill score effort
      levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
      hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
      hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
      hbestAE hpost_actual hequal_score_level hpreRank_meas hpostRank_meas
      hrankLevel_meas htail_measure

theorem bounded_reward_levels_ae_eq_of_score_order_and_equal_tail_measures
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (K : ℕ) (preLevel postLevel : α → ℕ) (score : α → ℝ)
    (hpre_bound : ∀ x, preLevel x < K)
    (hpost_bound : ∀ x, postLevel x < K)
    (hpre_to_score :
      ∀ x y, preLevel y < preLevel x → score y ≤ score x)
    (hpost_score_mono :
      ∀ x y, score y ≤ score x → postLevel y ≤ postLevel x)
    (hmeasure :
      ∀ t, t < K →
        μ {x | t ≤ preLevel x} = μ {x | t ≤ postLevel x})
    (hpre_meas :
      ∀ t, t < K → NullMeasurableSet {x | t ≤ preLevel x} μ)
    (hpost_meas :
      ∀ t, t < K → NullMeasurableSet {x | t ≤ postLevel x} μ)
    (hpre_finite :
      ∀ t, t < K → (μ {x | t ≤ preLevel x}) ≠ ⊤)
    (hpost_finite :
      ∀ t, t < K → (μ {x | t ≤ postLevel x}) ≠ ⊤) :
    postLevel =ᵐ[μ] preLevel :=
  bounded_reward_levels_ae_eq_of_no_inversion_and_equal_tail_measures
    K preLevel postLevel hpre_bound hpost_bound
    (no_reward_inversion_of_preorder_score_monotone
      preLevel postLevel score hpre_to_score hpost_score_mono)
    hmeasure hpre_meas hpost_meas hpre_finite hpost_finite

/-- Algebraic private utility term from the source's three-level counterexample proof. -/
def threeLevelPrivateUtility (x fc1 fc2 c1 c2 : ℝ) : ℝ :=
  x * fc1 * (c2 - c1) * x + ((1 - x) * fc2 + x * fc1) * (1 - c2)

/-- Algebraic deterministic two-level private utility term used for comparison. -/
def deterministicPrivateUtility (rho fDet : ℝ) : ℝ :=
  fDet * rho

/--
Source counterexample algebra: if the chosen upper-tail quantile value makes
the source inequality hold, the three-level policy strictly improves on the
deterministic two-level policy.
-/
theorem threeLevel_privateUtility_gt_deterministic_of_source_inequality
    {rho fDet x fc1 fc2 c1 c2 : ℝ}
    (hineq :
      deterministicPrivateUtility rho fDet
        < x * fc1 * (c2 - c1) * x + ((1 - x) * fc2 + x * fc1) * (1 - c2)) :
    deterministicPrivateUtility rho fDet < threeLevelPrivateUtility x fc1 fc2 c1 c2 := by
  simpa [threeLevelPrivateUtility] using hineq

/--
Concrete algebraic witness for the three-level counterexample inequality.  This
is the source proof's long-tail construction reduced to the displayed private
utility inequality.
-/
theorem exists_threeLevel_privateUtility_counterexample_algebra :
    ∃ rho x fc1 fc2 c1 c2 fDet : ℝ,
      0 < rho ∧ rho < 1 ∧ 0 < x ∧ x < 1 ∧ c1 < c2 ∧ c2 < 1 ∧
      x * (c2 - c1) + (1 - c2) = rho ∧
      deterministicPrivateUtility rho fDet < threeLevelPrivateUtility x fc1 fc2 c1 c2 := by
  refine ⟨(1 : ℝ) / 2, (1 : ℝ) / 3, 1, 10, 0, (3 : ℝ) / 4, 1, ?_⟩
  norm_num [deterministicPrivateUtility, threeLevelPrivateUtility]

/-- Explicit long-tail quantile witness used to realize the three-level example. -/
def longTailQuantileWitness (t : ℝ) : ℝ :=
  1 + 40 * t ^ 5

theorem longTailQuantileWitness_continuous :
    Continuous longTailQuantileWitness := by
  unfold longTailQuantileWitness
  continuity

theorem longTailQuantileWitness_strictMono :
    StrictMono longTailQuantileWitness := by
  intro a b hab
  unfold longTailQuantileWitness
  have hodd : Odd (5 : ℕ) := by decide
  have hpow : a ^ 5 < b ^ 5 := hodd.strictMono_pow hab
  nlinarith

/--
Source-shaped three-level counterexample witness: the algebraic improvement can
be realized by a continuous strictly increasing long-tail quantile function, with
the deterministic benchmark evaluated at the source cutoff `1 - rho`.
-/
theorem exists_threeLevel_privateUtility_counterexample_continuous_quantile :
    ∃ Q : ℝ → ℝ, ∃ rho x c1 c2 : ℝ,
      Continuous Q ∧ StrictMonoOn Q (Set.Icc 0 1) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < Q t) ∧
      0 < rho ∧ rho < 1 ∧ 0 < x ∧ x < 1 ∧
      0 ≤ c1 ∧ c1 < 1 - rho ∧ 1 - rho < c2 ∧ c2 < 1 ∧
      x * (c2 - c1) + (1 - c2) = rho ∧
      deterministicPrivateUtility rho (Q (1 - rho))
        < threeLevelPrivateUtility x (Q c1) (Q c2) c1 c2 := by
  refine
    ⟨longTailQuantileWitness, (2 : ℝ) / 5, (1 : ℝ) / 3, 0, (9 : ℝ) / 10, ?_⟩
  constructor
  · exact longTailQuantileWitness_continuous
  constructor
  · exact longTailQuantileWitness_strictMono.strictMonoOn _
  constructor
  · intro t ht
    have ht5 : 0 ≤ t ^ 5 := pow_nonneg ht.1 5
    unfold longTailQuantileWitness
    nlinarith
  repeat' constructor <;>
    norm_num [longTailQuantileWitness, deterministicPrivateUtility, threeLevelPrivateUtility]

/--
The paper's pointwise welfare gap between the advantaged and disadvantaged
groups at a fixed latent rank.
-/
def welfareGap (welfareA welfareB : ℝ) : ℝ :=
  welfareA - welfareB

/-- Individual welfare in the source model: admission reward minus effort cost. -/
def individualWelfare (admissionReward effortCost : ℝ) : ℝ :=
  admissionReward - effortCost

theorem welfareGap_nonnegative_of_le {welfareA welfareB : ℝ}
    (h : welfareB ≤ welfareA) :
    0 ≤ welfareGap welfareA welfareB := by
  unfold welfareGap
  linarith

theorem welfareGap_positive_of_lt {welfareA welfareB : ℝ}
    (h : welfareB < welfareA) :
    0 < welfareGap welfareA welfareB := by
  unfold welfareGap
  linarith

theorem welfareGap_eq_zero_of_equal_welfare {welfareA welfareB : ℝ}
    (h : welfareA = welfareB) :
    welfareGap welfareA welfareB = 0 := by
  unfold welfareGap
  linarith

theorem welfareGap_self (welfare : ℝ) :
    welfareGap welfare welfare = 0 :=
  welfareGap_eq_zero_of_equal_welfare rfl

theorem environment_region_welfare_gap_signs
    {admitHigh midWelfareA costA costB : ℝ} :
    welfareGap (individualWelfare 0 0) (individualWelfare 0 0) = 0
    ∧ (0 ≤ midWelfareA → 0 ≤ welfareGap midWelfareA (individualWelfare 0 0))
    ∧ (costA ≤ costB →
        0 ≤ welfareGap
          (individualWelfare admitHigh costA)
          (individualWelfare admitHigh costB))
    ∧ (costA < costB →
        0 < welfareGap
          (individualWelfare admitHigh costA)
          (individualWelfare admitHigh costB)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [welfareGap, individualWelfare]
  · intro hmid
    simp [welfareGap, individualWelfare]
    exact hmid
  · intro hcost
    unfold welfareGap individualWelfare
    linarith
  · intro hcost
    unfold welfareGap individualWelfare
    linarith

theorem welfareGap_derivative_positive_from_factor_orders
    {common costDerivA costDerivB invDerivA invDerivB chainA chainB : ℝ}
    (hcostA_nonneg : 0 ≤ costDerivA)
    (hcost_order : costDerivA ≤ costDerivB)
    (hcostB_pos : 0 < costDerivB)
    (hinvA_nonneg : 0 ≤ invDerivA)
    (hinv_order : invDerivA ≤ invDerivB)
    (hinvB_pos : 0 < invDerivB)
    (hchainA_nonneg : 0 ≤ chainA)
    (hchain_order : chainA < chainB) :
    0 <
      (common - costDerivA * invDerivA * chainA)
        - (common - costDerivB * invDerivB * chainB) := by
  have hcostB_nonneg : 0 ≤ costDerivB := le_of_lt hcostB_pos
  have hprod12 :
      costDerivA * invDerivA ≤ costDerivB * invDerivB :=
    mul_le_mul hcost_order hinv_order hinvA_nonneg hcostB_nonneg
  have hprod_le :
      costDerivA * invDerivA * chainA
        ≤ costDerivB * invDerivB * chainA :=
    mul_le_mul_of_nonneg_right hprod12 hchainA_nonneg
  have hprodB_pos : 0 < costDerivB * invDerivB :=
    mul_pos hcostB_pos hinvB_pos
  have hprod_lt :
      costDerivB * invDerivB * chainA
        < costDerivB * invDerivB * chainB :=
    mul_lt_mul_of_pos_left hchain_order hprodB_pos
  have hlt :
      costDerivA * invDerivA * chainA
        < costDerivB * invDerivB * chainB :=
    lt_of_le_of_lt hprod_le hprod_lt
  linarith

/--
Source-shaped bridge for Proposition `prop:deriv-welfare-gap`.

The appendix reduces the high-region welfare-gap derivative to three factor
comparisons.  This lemma derives those comparisons from the source monotonicity
and positivity primitives: the disadvantaged environment parameter has the
larger reciprocal denominator, so both derivative arguments and the final chain
factor are larger for group `B`.
-/
theorem welfareGap_derivative_positive_from_source_factor_primitives
    {common scoreNumerator derivNumerator fTheta psiA psiB : ℝ}
    {gInv costDeriv invDeriv : ℝ → ℝ}
    (hscoreNum : 0 < scoreNumerator)
    (hderivNum : 0 < derivNumerator)
    (hfTheta : 0 < fTheta)
    (hpsiB_pos : 0 < psiB)
    (hpsi_order : psiB < psiA)
    (hgInv_mono : StrictMono gInv)
    (hcostDeriv_mono : Monotone costDeriv)
    (hcostDeriv_nonneg : ∀ x, 0 ≤ costDeriv x)
    (hcostDeriv_pos : ∀ x, 0 < costDeriv x)
    (hinvDeriv_mono : Monotone invDeriv)
    (hinvDeriv_nonneg : ∀ x, 0 ≤ invDeriv x)
    (hinvDeriv_pos : ∀ x, 0 < invDeriv x) :
    0 <
      (common
          - costDeriv (gInv (scoreNumerator / (fTheta * psiA)))
            * invDeriv (scoreNumerator / (fTheta * psiA))
            * (derivNumerator / (fTheta * psiA)))
        - (common
          - costDeriv (gInv (scoreNumerator / (fTheta * psiB)))
            * invDeriv (scoreNumerator / (fTheta * psiB))
            * (derivNumerator / (fTheta * psiB))) := by
  have hpsiA_pos : 0 < psiA := lt_trans hpsiB_pos hpsi_order
  have hdenA_pos : 0 < fTheta * psiA := mul_pos hfTheta hpsiA_pos
  have hdenB_pos : 0 < fTheta * psiB := mul_pos hfTheta hpsiB_pos
  have hden_order : fTheta * psiB < fTheta * psiA :=
    mul_lt_mul_of_pos_left hpsi_order hfTheta
  have hscore_arg_lt :
      scoreNumerator / (fTheta * psiA)
        < scoreNumerator / (fTheta * psiB) := by
    rw [div_lt_div_iff₀ hdenA_pos hdenB_pos]
    exact mul_lt_mul_of_pos_left hden_order hscoreNum
  have hderiv_chain_lt :
      derivNumerator / (fTheta * psiA)
        < derivNumerator / (fTheta * psiB) := by
    rw [div_lt_div_iff₀ hdenA_pos hdenB_pos]
    exact mul_lt_mul_of_pos_left hden_order hderivNum
  exact welfareGap_derivative_positive_from_factor_orders
    (common := common)
    (costDerivA :=
      costDeriv (gInv (scoreNumerator / (fTheta * psiA))))
    (costDerivB :=
      costDeriv (gInv (scoreNumerator / (fTheta * psiB))))
    (invDerivA :=
      invDeriv (scoreNumerator / (fTheta * psiA)))
    (invDerivB :=
      invDeriv (scoreNumerator / (fTheta * psiB)))
    (chainA := derivNumerator / (fTheta * psiA))
    (chainB := derivNumerator / (fTheta * psiB))
    (hcostDeriv_nonneg _)
    (hcostDeriv_mono (le_of_lt (hgInv_mono hscore_arg_lt)))
    (hcostDeriv_pos _)
    (hinvDeriv_nonneg _)
    (hinvDeriv_mono (le_of_lt hscore_arg_lt))
    (hinvDeriv_pos _)
    (le_of_lt (div_pos hderivNum hdenA_pos))
    hderiv_chain_lt

/--
Environment-scaled pre-effort rank from the source model:
`theta_pre = f_mix^{-1}(f(theta_true) * psi)`.
-/
noncomputable def environmentScaledRank
    (fMixInv f : ℝ → ℝ) (thetaTrue psi : ℝ) : ℝ :=
  fMixInv (f thetaTrue * psi)

theorem environmentScaledRank_advantaged_gt_disadvantaged
    {fMixInv f : ℝ → ℝ} {thetaTrue psiA psiB : ℝ}
    (hmono : StrictMono fMixInv)
    (hskill : 0 < f thetaTrue)
    (hadv : psiB < psiA) :
    environmentScaledRank fMixInv f thetaTrue psiB
      < environmentScaledRank fMixInv f thetaTrue psiA := by
  exact hmono (mul_lt_mul_of_pos_left hadv hskill)

/--
Group-specific true-rank threshold in the environment section:
`theta_G(c) = f^{-1}(f_mix(c) / psi_G)`.
-/
noncomputable def groupThreshold
    (fInv fMix : ℝ → ℝ) (c psi : ℝ) : ℝ :=
  fInv (fMix c / psi)

/--
Environment threshold equivalence from the source definitions.  If
`f_mix^{-1}` and `f` are strictly increasing and the displayed inverse
identities hold at the relevant cutoff, then clearing the environment-scaled
rank cutoff is equivalent to the true rank clearing the group threshold
`theta_G(c) = f^{-1}(f_mix(c) / psi_G)`.
-/
theorem environmentScaledRank_ge_cutoff_iff_groupThreshold_le_trueRank
    {fMixInv fInv fMix f : ℝ → ℝ} {thetaTrue psi c : ℝ}
    (hfMixInv_mono : StrictMono fMixInv)
    (hf_mono : StrictMono f)
    (hpsi_pos : 0 < psi)
    (hmix : fMixInv (fMix c) = c)
    (hfInv : f (fInv (fMix c / psi)) = fMix c / psi) :
    c ≤ environmentScaledRank fMixInv f thetaTrue psi ↔
      groupThreshold fInv fMix c psi ≤ thetaTrue := by
  unfold environmentScaledRank groupThreshold
  constructor
  · intro h
    have hscaled :
        fMixInv (fMix c) ≤ fMixInv (f thetaTrue * psi) := by
      simpa [hmix] using h
    have hx : fMix c ≤ f thetaTrue * psi :=
      hfMixInv_mono.le_iff_le.mp hscaled
    have hxdiv : fMix c / psi ≤ f thetaTrue := by
      rw [div_le_iff₀ hpsi_pos]
      exact hx
    have hf_le : f (fInv (fMix c / psi)) ≤ f thetaTrue := by
      simpa [hfInv] using hxdiv
    exact hf_mono.le_iff_le.mp hf_le
  · intro h
    have hf_le : f (fInv (fMix c / psi)) ≤ f thetaTrue :=
      hf_mono.le_iff_le.mpr h
    have hxdiv : fMix c / psi ≤ f thetaTrue := by
      simpa [hfInv] using hf_le
    have hx : fMix c ≤ f thetaTrue * psi := by
      rwa [div_le_iff₀ hpsi_pos] at hxdiv
    have hscaled :
        fMixInv (fMix c) ≤ fMixInv (f thetaTrue * psi) :=
      hfMixInv_mono.le_iff_le.mpr hx
    simpa [hmix] using hscaled

/--
The source two-group mixture inverse formula in the environment section:
`f_mix^{-1}(x) = (f^{-1}(x / psi_A) + f^{-1}(x / psi_B)) / 2`.
-/
noncomputable def twoGroupMixtureInverse
    (fInv : ℝ → ℝ) (psiA psiB x : ℝ) : ℝ :=
  (fInv (x / psiA) + fInv (x / psiB)) / 2

theorem groupThreshold_advantaged_lt_disadvantaged
    {fInv fMix : ℝ → ℝ} {c psiA psiB : ℝ}
    (hmono : StrictMono fInv)
    (hfmix_pos : 0 < fMix c)
    (hpsiB_pos : 0 < psiB)
    (hadv : psiB < psiA) :
    groupThreshold fInv fMix c psiA
      < groupThreshold fInv fMix c psiB := by
  have hpsiA_pos : 0 < psiA := lt_trans hpsiB_pos hadv
  have hfrac : fMix c / psiA < fMix c / psiB := by
    rw [div_lt_div_iff₀ hpsiA_pos hpsiB_pos]
    nlinarith
  exact hmono hfrac

theorem groupThreshold_advantaged_le_disadvantaged
    {fInv fMix : ℝ → ℝ} {c psiA psiB : ℝ}
    (hmono : Monotone fInv)
    (hfmix_nonneg : 0 ≤ fMix c)
    (hpsiB_pos : 0 < psiB)
    (hadv : psiB < psiA) :
    groupThreshold fInv fMix c psiA
      ≤ groupThreshold fInv fMix c psiB := by
  have hpsiA_pos : 0 < psiA := lt_trans hpsiB_pos hadv
  have hfrac : fMix c / psiA ≤ fMix c / psiB := by
    rw [div_le_div_iff₀ hpsiA_pos hpsiB_pos]
    nlinarith
  exact hmono hfrac

/-- Two-level admission probability for one group with true-rank threshold `thetaG`. -/
noncomputable def twoLevelGroupAdmission (rho c thetaTrue thetaG : ℝ) : ℝ :=
  if thetaG ≤ thetaTrue then rho / (1 - c) else 0

theorem twoLevel_groupAdmission_low_region
    {rho c thetaTrue thetaA thetaB : ℝ}
    (hbelowA : thetaTrue < thetaA)
    (hbelowB : thetaTrue < thetaB) :
    twoLevelGroupAdmission rho c thetaTrue thetaA = 0 ∧
      twoLevelGroupAdmission rho c thetaTrue thetaB = 0 := by
  constructor
  · have hnot : ¬ thetaA ≤ thetaTrue := not_le.mpr hbelowA
    simp [twoLevelGroupAdmission, hnot]
  · have hnot : ¬ thetaB ≤ thetaTrue := not_le.mpr hbelowB
    simp [twoLevelGroupAdmission, hnot]

theorem twoLevel_groupAdmission_middle_region
    {rho c thetaTrue thetaA thetaB : ℝ}
    (hA : thetaA ≤ thetaTrue)
    (hbelowB : thetaTrue < thetaB) :
    twoLevelGroupAdmission rho c thetaTrue thetaA = rho / (1 - c) ∧
      twoLevelGroupAdmission rho c thetaTrue thetaB = 0 := by
  constructor
  · simp [twoLevelGroupAdmission, hA]
  · simp [twoLevelGroupAdmission, not_le.mpr hbelowB]

theorem twoLevel_groupAdmission_high_region
    {rho c thetaTrue thetaA thetaB : ℝ}
    (hthreshold_order : thetaA ≤ thetaB)
    (hB : thetaB ≤ thetaTrue) :
    twoLevelGroupAdmission rho c thetaTrue thetaA = rho / (1 - c) ∧
      twoLevelGroupAdmission rho c thetaTrue thetaB = rho / (1 - c) := by
  have hA : thetaA ≤ thetaTrue := hthreshold_order.trans hB
  constructor <;> simp [twoLevelGroupAdmission, *]

/-- Disadvantaged-group access under a two-level policy with threshold `thetaB`. -/
noncomputable def twoLevelDisadvantagedAccess (rho c thetaB : ℝ) : ℝ :=
  rho / (1 - c) * (1 - thetaB)

/-- Disadvantaged-group access under pure randomization. -/
def pureRandomizationAccess (rho : ℝ) : ℝ :=
  rho

/--
Source Proposition 8 first clause, in its algebraic threshold form: if the
disadvantaged group's source threshold is above the two-level cutoff, then
pure randomization gives strictly higher disadvantaged-group access.
-/
theorem pureRandomization_access_gt_twoLevel_of_threshold_gt_cutoff
    {rho c thetaB : ℝ} (hrho : 0 < rho) (hc : c < 1) (hthreshold : c < thetaB) :
    twoLevelDisadvantagedAccess rho c thetaB < pureRandomizationAccess rho := by
  have hden : 0 < 1 - c := by linarith
  have hratio : (1 - thetaB) / (1 - c) < 1 := by
    rw [div_lt_one hden]
    linarith
  calc
    twoLevelDisadvantagedAccess rho c thetaB = rho * ((1 - thetaB) / (1 - c)) := by
      rw [twoLevelDisadvantagedAccess, div_eq_mul_inv, div_eq_mul_inv]
      ring
    _ < rho * 1 := mul_lt_mul_of_pos_left hratio hrho
    _ = pureRandomizationAccess rho := by simp [pureRandomizationAccess]

/--
Finite-difference form of the access monotonicity proof: once the threshold
movement dominates the cutoff movement, access cannot increase with `c`.
-/
theorem twoLevel_access_nonincreasing_of_threshold_slope_bound
    {rho cLow cHigh thetaLow thetaHigh : ℝ}
    (hrho : 0 ≤ rho)
    (hdenLow : 0 < 1 - cLow)
    (hdenHigh : 0 < 1 - cHigh)
    (hslope : (1 - thetaHigh) / (1 - cHigh) ≤ (1 - thetaLow) / (1 - cLow)) :
    twoLevelDisadvantagedAccess rho cHigh thetaHigh
      ≤ twoLevelDisadvantagedAccess rho cLow thetaLow := by
  calc
    twoLevelDisadvantagedAccess rho cHigh thetaHigh =
        rho * ((1 - thetaHigh) / (1 - cHigh)) := by
      rw [twoLevelDisadvantagedAccess, div_eq_mul_inv, div_eq_mul_inv]
      ring
    _ ≤ rho * ((1 - thetaLow) / (1 - cLow)) :=
      mul_le_mul_of_nonneg_left hslope hrho
    _ = twoLevelDisadvantagedAccess rho cLow thetaLow := by
      rw [twoLevelDisadvantagedAccess, div_eq_mul_inv, div_eq_mul_inv]
      ring

/--
Reusable bridge for the linear-threshold special case: if the disadvantaged
threshold is `a * c` with slope at least one, then the access expression is
nonincreasing in the two-level cutoff.
-/
theorem twoLevel_access_nonincreasing_of_affine_threshold_slope_ge_one
    {rho a cLow cHigh : ℝ}
    (hrho : 0 ≤ rho)
    (ha : 1 ≤ a)
    (hc_mono : cLow ≤ cHigh)
    (hdenLow : 0 < 1 - cLow)
    (hdenHigh : 0 < 1 - cHigh) :
    twoLevelDisadvantagedAccess rho cHigh (a * cHigh)
      ≤ twoLevelDisadvantagedAccess rho cLow (a * cLow) := by
  have hb : 0 ≤ a - 1 := by linarith
  have hmul : (a - 1) * cLow ≤ (a - 1) * cHigh :=
    mul_le_mul_of_nonneg_left hc_mono hb
  have hslope :
      (1 - a * cHigh) / (1 - cHigh) ≤ (1 - a * cLow) / (1 - cLow) := by
    rw [div_le_div_iff₀ hdenHigh hdenLow]
    nlinarith
  exact twoLevel_access_nonincreasing_of_threshold_slope_bound
    hrho hdenLow hdenHigh hslope

theorem access_ratio_nonincreasing_of_threshold_gap_monotone
    {cLow cHigh thetaLow thetaHigh : ℝ}
    (hc_mono : cLow ≤ cHigh)
    (hdenLow : 0 < 1 - cLow)
    (hdenHigh : 0 < 1 - cHigh)
    (hgapLow : 0 ≤ thetaLow - cLow)
    (hgap_mono : thetaLow - cLow ≤ thetaHigh - cHigh) :
    (1 - thetaHigh) / (1 - cHigh)
      ≤ (1 - thetaLow) / (1 - cLow) := by
  have hgapHigh : 0 ≤ thetaHigh - cHigh := le_trans hgapLow hgap_mono
  have hdenHigh_le_low : 1 - cHigh ≤ 1 - cLow := by linarith
  have hgap_div_mono :
      (thetaLow - cLow) / (1 - cLow)
        ≤ (thetaHigh - cHigh) / (1 - cHigh) := by
    have hstep1 :
        (thetaLow - cLow) / (1 - cLow)
          ≤ (thetaHigh - cHigh) / (1 - cLow) :=
      div_le_div_of_nonneg_right hgap_mono (le_of_lt hdenLow)
    have hstep2 :
        (thetaHigh - cHigh) / (1 - cLow)
          ≤ (thetaHigh - cHigh) / (1 - cHigh) := by
      rw [div_le_div_iff₀ hdenLow hdenHigh]
      nlinarith
    exact le_trans hstep1 hstep2
  have hidHigh :
      (1 - thetaHigh) / (1 - cHigh)
        = 1 - (thetaHigh - cHigh) / (1 - cHigh) := by
    field_simp [ne_of_gt hdenHigh]
    ring
  have hidLow :
      (1 - thetaLow) / (1 - cLow)
        = 1 - (thetaLow - cLow) / (1 - cLow) := by
    field_simp [ne_of_gt hdenLow]
    ring
  rw [hidHigh, hidLow]
  linarith

/--
Finite-difference access bridge used to avoid hiding a derivative certificate:
if the disadvantaged threshold's excess over the policy cutoff is monotone in
the cutoff, then disadvantaged-group access is nonincreasing.
-/
theorem twoLevel_access_nonincreasing_of_threshold_gap_monotone
    {rho cLow cHigh thetaLow thetaHigh : ℝ}
    (hrho : 0 ≤ rho)
    (hc_mono : cLow ≤ cHigh)
    (hdenLow : 0 < 1 - cLow)
    (hdenHigh : 0 < 1 - cHigh)
    (hgapLow : 0 ≤ thetaLow - cLow)
    (hgap_mono : thetaLow - cLow ≤ thetaHigh - cHigh) :
    twoLevelDisadvantagedAccess rho cHigh thetaHigh
      ≤ twoLevelDisadvantagedAccess rho cLow thetaLow :=
  twoLevel_access_nonincreasing_of_threshold_slope_bound
    hrho hdenLow hdenHigh
    (access_ratio_nonincreasing_of_threshold_gap_monotone
      hc_mono hdenLow hdenHigh hgapLow hgap_mono)

theorem groupThreshold_gap_eq_half_difference_of_mix_inverse
    {fInv fMix : ℝ → ℝ} {c psiA psiB : ℝ}
    (hmix :
      (groupThreshold fInv fMix c psiA
          + groupThreshold fInv fMix c psiB) / 2 = c) :
    groupThreshold fInv fMix c psiB - c =
      (groupThreshold fInv fMix c psiB
        - groupThreshold fInv fMix c psiA) / 2 := by
  nlinarith

theorem groupThreshold_mix_identity_of_twoGroupMixtureInverse
    {fInv fMix : ℝ → ℝ} {c psiA psiB : ℝ}
    (hmixInv :
      twoGroupMixtureInverse fInv psiA psiB (fMix c) = c) :
    (groupThreshold fInv fMix c psiA
        + groupThreshold fInv fMix c psiB) / 2 = c := by
  simpa [twoGroupMixtureInverse, groupThreshold] using hmixInv

theorem groupThreshold_cutoff_between_of_mix_inverse_order
    {fInv fMix : ℝ → ℝ} {c psiA psiB : ℝ}
    (hthreshold_order :
      groupThreshold fInv fMix c psiA ≤ groupThreshold fInv fMix c psiB)
    (hmix :
      (groupThreshold fInv fMix c psiA
          + groupThreshold fInv fMix c psiB) / 2 = c) :
    groupThreshold fInv fMix c psiA ≤ c ∧
      c ≤ groupThreshold fInv fMix c psiB := by
  constructor <;> nlinarith

theorem groupThreshold_cutoff_strict_between_of_mix_inverse_order
    {fInv fMix : ℝ → ℝ} {c psiA psiB : ℝ}
    (hthreshold_order :
      groupThreshold fInv fMix c psiA < groupThreshold fInv fMix c psiB)
    (hmix :
      (groupThreshold fInv fMix c psiA
          + groupThreshold fInv fMix c psiB) / 2 = c) :
    groupThreshold fInv fMix c psiA < c ∧
      c < groupThreshold fInv fMix c psiB := by
  constructor <;> nlinarith

theorem pureRandomization_access_gt_twoLevel_of_mix_inverse_order
    {rho c psiA psiB : ℝ} {fInv fMix : ℝ → ℝ}
    (hrho : 0 < rho)
    (hc : c < 1)
    (hthreshold_order :
      groupThreshold fInv fMix c psiA < groupThreshold fInv fMix c psiB)
    (hmix :
      (groupThreshold fInv fMix c psiA
          + groupThreshold fInv fMix c psiB) / 2 = c) :
    twoLevelDisadvantagedAccess rho c (groupThreshold fInv fMix c psiB)
      < pureRandomizationAccess rho :=
  pureRandomization_access_gt_twoLevel_of_threshold_gt_cutoff hrho hc
    (groupThreshold_cutoff_strict_between_of_mix_inverse_order
      hthreshold_order hmix).2

theorem pureRandomization_access_gt_twoLevel_of_source_threshold_identity
    {rho c psiA psiB : ℝ} {fInv fMix : ℝ → ℝ}
    (hrho : 0 < rho)
    (hc : c < 1)
    (hmono : StrictMono fInv)
    (hfmix_pos : 0 < fMix c)
    (hpsiB_pos : 0 < psiB)
    (hpsi_order : psiB < psiA)
    (hmix :
      (groupThreshold fInv fMix c psiA
          + groupThreshold fInv fMix c psiB) / 2 = c) :
    twoLevelDisadvantagedAccess rho c (groupThreshold fInv fMix c psiB)
      < pureRandomizationAccess rho :=
  pureRandomization_access_gt_twoLevel_of_mix_inverse_order hrho hc
    (groupThreshold_advantaged_lt_disadvantaged hmono hfmix_pos
      hpsiB_pos hpsi_order)
    hmix

theorem pureRandomization_access_gt_twoLevel_of_source_mix_inverse
    {rho c psiA psiB : ℝ} {fInv fMix : ℝ → ℝ}
    (hrho : 0 < rho)
    (hc : c < 1)
    (hmono : StrictMono fInv)
    (hfmix_pos : 0 < fMix c)
    (hpsiB_pos : 0 < psiB)
    (hpsi_order : psiB < psiA)
    (hmixInv :
      twoGroupMixtureInverse fInv psiA psiB (fMix c) = c) :
    twoLevelDisadvantagedAccess rho c (groupThreshold fInv fMix c psiB)
      < pureRandomizationAccess rho :=
  pureRandomization_access_gt_twoLevel_of_source_threshold_identity
    hrho hc hmono hfmix_pos hpsiB_pos hpsi_order
    (groupThreshold_mix_identity_of_twoGroupMixtureInverse hmixInv)

theorem pureRandomization_access_gt_twoLevel_of_source_mix_inverse_definition
    {rho c psiA psiB : ℝ} {fInv fMix fMixInv : ℝ → ℝ}
    (hrho : 0 < rho)
    (hc : c < 1)
    (hmono : StrictMono fInv)
    (hfmix_pos : 0 < fMix c)
    (hpsiB_pos : 0 < psiB)
    (hpsi_order : psiB < psiA)
    (hfMixInv_def :
      ∀ x, fMixInv x = twoGroupMixtureInverse fInv psiA psiB x)
    (hmix : fMixInv (fMix c) = c) :
    twoLevelDisadvantagedAccess rho c (groupThreshold fInv fMix c psiB)
      < pureRandomizationAccess rho := by
  have hmixInv :
      twoGroupMixtureInverse fInv psiA psiB (fMix c) = c := by
    simpa [hfMixInv_def (fMix c)] using hmix
  exact pureRandomization_access_gt_twoLevel_of_source_mix_inverse
    hrho hc hmono hfmix_pos hpsiB_pos hpsi_order hmixInv

theorem groupThreshold_gap_mono_of_mix_inverse_gap_mono
    {fInv fMix : ℝ → ℝ} {cLow cHigh psiA psiB : ℝ}
    (hmixLow :
      (groupThreshold fInv fMix cLow psiA
          + groupThreshold fInv fMix cLow psiB) / 2 = cLow)
    (hmixHigh :
      (groupThreshold fInv fMix cHigh psiA
          + groupThreshold fInv fMix cHigh psiB) / 2 = cHigh)
    (hgap_mono :
      groupThreshold fInv fMix cLow psiB
          - groupThreshold fInv fMix cLow psiA
        ≤ groupThreshold fInv fMix cHigh psiB
          - groupThreshold fInv fMix cHigh psiA) :
    groupThreshold fInv fMix cLow psiB - cLow
      ≤ groupThreshold fInv fMix cHigh psiB - cHigh := by
  rw [groupThreshold_gap_eq_half_difference_of_mix_inverse hmixLow,
    groupThreshold_gap_eq_half_difference_of_mix_inverse hmixHigh]
  linarith

theorem groupThreshold_gap_mono_of_convex_inverse_and_mix_mono
    {fInv fMix : ℝ → ℝ} {cLow cHigh psiA psiB : ℝ}
    (hc_mono : cLow ≤ cHigh)
    (hpsiB_pos : 0 < psiB)
    (hpsi_order : psiB < psiA)
    (hfMix_nonneg : ∀ c, 0 ≤ fMix c)
    (hfMix_mono : Monotone fMix)
    (hfInv_convex : ConvexOn ℝ Set.univ fInv)
    (hfInv_mono : Monotone fInv) :
    groupThreshold fInv fMix cLow psiB
        - groupThreshold fInv fMix cLow psiA
      ≤ groupThreshold fInv fMix cHigh psiB
        - groupThreshold fInv fMix cHigh psiA := by
  have hpsiA_pos : 0 < psiA := lt_trans hpsiB_pos hpsi_order
  have hscale_order : (1 : ℝ) / psiA ≤ 1 / psiB :=
    one_div_le_one_div_of_le hpsiB_pos (le_of_lt hpsi_order)
  have hmix_order : fMix cLow ≤ fMix cHigh := hfMix_mono hc_mono
  have hscaled :=
    convex_increasing_scaled_gap_mono
      (f := fInv)
      (alpha := (1 : ℝ) / psiA)
      (beta := (1 : ℝ) / psiB)
      (x := fMix cLow)
      (y := fMix cHigh)
      hfInv_convex hfInv_mono
      (one_div_nonneg.mpr (le_of_lt hpsiA_pos))
      hscale_order
      (hfMix_nonneg cLow)
      hmix_order
  simpa [groupThreshold, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    using hscaled

theorem monotone_of_hasDerivAt_nonneg
    {gap gapDeriv : ℝ → ℝ}
    (hderiv : ∀ x, HasDerivAt gap (gapDeriv x) x)
    (hderiv_nonneg : ∀ x, 0 ≤ gapDeriv x) :
    Monotone gap := by
  intro a b hab
  by_cases heq : a = b
  · simp [heq]
  have hcont : Continuous gap :=
    continuous_iff_continuousAt.mpr fun x => (hderiv x).continuousAt
  have hmonoOn : MonotoneOn gap (Icc a b) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg
      (f' := gapDeriv)
      (convex_Icc a b) hcont.continuousOn ?_ ?_
    · intro x _
      exact (hderiv x).hasDerivWithinAt
    · intro x _
      exact hderiv_nonneg x
  exact hmonoOn (by simp [hab]) (by simp [hab]) hab

theorem deriv_mono_of_convex_differentiable
    {f : ℝ → ℝ}
    (hconv : ConvexOn ℝ Set.univ f)
    (hdiff : ∀ x, DifferentiableAt ℝ f x) :
    ∀ y z, y ≤ z → deriv f y ≤ deriv f z := by
  intro y z hyz
  exact hconv.monotoneOn_deriv
    (fun x _ => hdiff x) (by simp) (by simp) hyz

theorem deriv_nonneg_of_monotone
    {f : ℝ → ℝ} (hmono : Monotone f) :
    ∀ x, 0 ≤ deriv f x := by
  intro x
  exact hmono.deriv_nonneg

theorem groupThreshold_gap_mono_of_derivative_nonneg
    {fInv fMix : ℝ → ℝ} {cLow cHigh psiA psiB : ℝ}
    {gapDeriv : ℝ → ℝ}
    (hc_mono : cLow ≤ cHigh)
    (hderiv :
      ∀ c,
        HasDerivAt
          (fun x =>
            groupThreshold fInv fMix x psiB
              - groupThreshold fInv fMix x psiA)
          (gapDeriv c) c)
    (hderiv_nonneg : ∀ c, 0 ≤ gapDeriv c) :
    groupThreshold fInv fMix cLow psiB
        - groupThreshold fInv fMix cLow psiA
      ≤ groupThreshold fInv fMix cHigh psiB
        - groupThreshold fInv fMix cHigh psiA := by
  exact monotone_of_hasDerivAt_nonneg hderiv hderiv_nonneg hc_mono

theorem scaled_gap_derivative_nonneg_of_mono_nonneg_derivative
    {alpha beta x : ℝ} {hDeriv : ℝ → ℝ}
    (halpha_nonneg : 0 ≤ alpha)
    (hscale_order : alpha ≤ beta)
    (hx : 0 ≤ x)
    (hderiv_mono : ∀ y z, y ≤ z → hDeriv y ≤ hDeriv z)
    (hderiv_nonneg : ∀ y, 0 ≤ hDeriv y) :
    0 ≤ beta * hDeriv (beta * x) - alpha * hDeriv (alpha * x) := by
  have hbeta_nonneg : 0 ≤ beta := le_trans halpha_nonneg hscale_order
  have harg_order : alpha * x ≤ beta * x :=
    mul_le_mul_of_nonneg_right hscale_order hx
  have hderiv_order : hDeriv (alpha * x) ≤ hDeriv (beta * x) :=
    hderiv_mono (alpha * x) (beta * x) harg_order
  have hprod1 :
      alpha * hDeriv (alpha * x) ≤ beta * hDeriv (alpha * x) :=
    mul_le_mul_of_nonneg_right hscale_order (hderiv_nonneg (alpha * x))
  have hprod2 :
      beta * hDeriv (alpha * x) ≤ beta * hDeriv (beta * x) :=
    mul_le_mul_of_nonneg_left hderiv_order hbeta_nonneg
  linarith

theorem groupThreshold_hasDerivAt
    {fInv fInvDeriv fMix fMixDeriv : ℝ → ℝ} {c psi : ℝ}
    (hfMix : HasDerivAt fMix (fMixDeriv c) c)
    (hfInv : HasDerivAt fInv (fInvDeriv (fMix c / psi)) (fMix c / psi)) :
    HasDerivAt (fun x => groupThreshold fInv fMix x psi)
      (fInvDeriv (fMix c / psi) * (fMixDeriv c / psi)) c := by
  unfold groupThreshold
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    hfInv.comp c (hfMix.div_const psi)

theorem groupThreshold_gap_hasDerivAt
    {fInv fInvDeriv fMix fMixDeriv : ℝ → ℝ} {c psiA psiB : ℝ}
    (hfMix : HasDerivAt fMix (fMixDeriv c) c)
    (hfInvA : HasDerivAt fInv (fInvDeriv (fMix c / psiA)) (fMix c / psiA))
    (hfInvB : HasDerivAt fInv (fInvDeriv (fMix c / psiB)) (fMix c / psiB)) :
    HasDerivAt
      (fun x =>
        groupThreshold fInv fMix x psiB
          - groupThreshold fInv fMix x psiA)
      (fInvDeriv (fMix c / psiB) * (fMixDeriv c / psiB)
        - fInvDeriv (fMix c / psiA) * (fMixDeriv c / psiA)) c := by
  exact (groupThreshold_hasDerivAt hfMix hfInvB).sub
    (groupThreshold_hasDerivAt hfMix hfInvA)

theorem groupThreshold_gap_derivative_nonneg_of_scaled_deriv
    {x mixDeriv psiA psiB : ℝ} {fInvDeriv : ℝ → ℝ}
    (hpsiB_pos : 0 < psiB)
    (hpsi_order : psiB < psiA)
    (hx : 0 ≤ x)
    (hmixDeriv : 0 ≤ mixDeriv)
    (hderiv_mono : ∀ y z, y ≤ z → fInvDeriv y ≤ fInvDeriv z)
    (hderiv_nonneg : ∀ y, 0 ≤ fInvDeriv y) :
    0 ≤ fInvDeriv (x / psiB) * (mixDeriv / psiB)
      - fInvDeriv (x / psiA) * (mixDeriv / psiA) := by
  have hpsiA_pos : 0 < psiA := lt_trans hpsiB_pos hpsi_order
  have hscale_order : (1 : ℝ) / psiA ≤ 1 / psiB :=
    one_div_le_one_div_of_le hpsiB_pos (le_of_lt hpsi_order)
  have hscaled :
      0 ≤ (1 / psiB) * fInvDeriv ((1 / psiB) * x)
        - (1 / psiA) * fInvDeriv ((1 / psiA) * x) :=
    scaled_gap_derivative_nonneg_of_mono_nonneg_derivative
      (alpha := (1 : ℝ) / psiA) (beta := (1 : ℝ) / psiB) (x := x)
      (by positivity) hscale_order hx hderiv_mono hderiv_nonneg
  have hmul :
      0 ≤ mixDeriv *
        ((1 / psiB) * fInvDeriv ((1 / psiB) * x)
          - (1 / psiA) * fInvDeriv ((1 / psiA) * x)) :=
    mul_nonneg hmixDeriv hscaled
  field_simp [ne_of_gt hpsiA_pos, ne_of_gt hpsiB_pos] at hmul ⊢
  nlinarith

theorem twoLevel_access_nonincreasing_of_mix_inverse_gap_mono
    {rho cLow cHigh psiA psiB : ℝ} {fInv fMix : ℝ → ℝ}
    (hrho : 0 ≤ rho)
    (hc_mono : cLow ≤ cHigh)
    (hdenLow : 0 < 1 - cLow)
    (hdenHigh : 0 < 1 - cHigh)
    (hthresholdLow : cLow ≤ groupThreshold fInv fMix cLow psiB)
    (hmixLow :
      (groupThreshold fInv fMix cLow psiA
          + groupThreshold fInv fMix cLow psiB) / 2 = cLow)
    (hmixHigh :
      (groupThreshold fInv fMix cHigh psiA
          + groupThreshold fInv fMix cHigh psiB) / 2 = cHigh)
    (hgap_mono :
      groupThreshold fInv fMix cLow psiB
          - groupThreshold fInv fMix cLow psiA
        ≤ groupThreshold fInv fMix cHigh psiB
          - groupThreshold fInv fMix cHigh psiA) :
    twoLevelDisadvantagedAccess rho cHigh (groupThreshold fInv fMix cHigh psiB)
      ≤ twoLevelDisadvantagedAccess rho cLow (groupThreshold fInv fMix cLow psiB) := by
  exact twoLevel_access_nonincreasing_of_threshold_gap_monotone
    hrho hc_mono hdenLow hdenHigh
    (by linarith)
    (groupThreshold_gap_mono_of_mix_inverse_gap_mono
      hmixLow hmixHigh hgap_mono)

theorem twoLevel_access_nonincreasing_of_mix_inverse_gap_derivative_nonneg
    {rho cLow cHigh psiA psiB : ℝ} {fInv fMix : ℝ → ℝ} {gapDeriv : ℝ → ℝ}
    (hrho : 0 ≤ rho)
    (hc_mono : cLow ≤ cHigh)
    (hdenLow : 0 < 1 - cLow)
    (hdenHigh : 0 < 1 - cHigh)
    (hthresholdLow : cLow ≤ groupThreshold fInv fMix cLow psiB)
    (hmixLow :
      (groupThreshold fInv fMix cLow psiA
          + groupThreshold fInv fMix cLow psiB) / 2 = cLow)
    (hmixHigh :
      (groupThreshold fInv fMix cHigh psiA
          + groupThreshold fInv fMix cHigh psiB) / 2 = cHigh)
    (hderiv :
      ∀ c,
        HasDerivAt
          (fun x =>
            groupThreshold fInv fMix x psiB
              - groupThreshold fInv fMix x psiA)
          (gapDeriv c) c)
    (hderiv_nonneg : ∀ c, 0 ≤ gapDeriv c) :
    twoLevelDisadvantagedAccess rho cHigh (groupThreshold fInv fMix cHigh psiB)
      ≤ twoLevelDisadvantagedAccess rho cLow (groupThreshold fInv fMix cLow psiB) := by
  exact twoLevel_access_nonincreasing_of_mix_inverse_gap_mono
    hrho hc_mono hdenLow hdenHigh hthresholdLow hmixLow hmixHigh
    (groupThreshold_gap_mono_of_derivative_nonneg
      hc_mono hderiv hderiv_nonneg)

theorem twoLevel_access_nonincreasing_of_convex_inverse_and_mix_mono
    {rho cLow cHigh psiA psiB : ℝ} {fInv fMix : ℝ → ℝ}
    (hrho : 0 ≤ rho)
    (hc_mono : cLow ≤ cHigh)
    (hdenLow : 0 < 1 - cLow)
    (hdenHigh : 0 < 1 - cHigh)
    (hpsiB_pos : 0 < psiB)
    (hpsi_order : psiB < psiA)
    (hthresholdLow : cLow ≤ groupThreshold fInv fMix cLow psiB)
    (hmixLow :
      (groupThreshold fInv fMix cLow psiA
          + groupThreshold fInv fMix cLow psiB) / 2 = cLow)
    (hmixHigh :
      (groupThreshold fInv fMix cHigh psiA
          + groupThreshold fInv fMix cHigh psiB) / 2 = cHigh)
    (hfMix_nonneg : ∀ c, 0 ≤ fMix c)
    (hfMix_mono : Monotone fMix)
    (hfInv_convex : ConvexOn ℝ Set.univ fInv)
    (hfInv_mono : Monotone fInv) :
    twoLevelDisadvantagedAccess rho cHigh (groupThreshold fInv fMix cHigh psiB)
      ≤ twoLevelDisadvantagedAccess rho cLow (groupThreshold fInv fMix cLow psiB) := by
  exact twoLevel_access_nonincreasing_of_mix_inverse_gap_mono
    hrho hc_mono hdenLow hdenHigh hthresholdLow hmixLow hmixHigh
    (groupThreshold_gap_mono_of_convex_inverse_and_mix_mono
      hc_mono hpsiB_pos hpsi_order hfMix_nonneg hfMix_mono
      hfInv_convex hfInv_mono)

theorem twoLevel_access_nonincreasing_of_mix_inverse_derivative_primitives
    {rho cLow cHigh psiA psiB : ℝ}
    {fInv fInvDeriv fMix fMixDeriv : ℝ → ℝ}
    (hrho : 0 ≤ rho)
    (hc_mono : cLow ≤ cHigh)
    (hdenLow : 0 < 1 - cLow)
    (hdenHigh : 0 < 1 - cHigh)
    (hpsiB_pos : 0 < psiB)
    (hpsi_order : psiB < psiA)
    (hthresholdLow : cLow ≤ groupThreshold fInv fMix cLow psiB)
    (hmixLow :
      (groupThreshold fInv fMix cLow psiA
          + groupThreshold fInv fMix cLow psiB) / 2 = cLow)
    (hmixHigh :
      (groupThreshold fInv fMix cHigh psiA
          + groupThreshold fInv fMix cHigh psiB) / 2 = cHigh)
    (hfMix_deriv : ∀ c, HasDerivAt fMix (fMixDeriv c) c)
    (hfInv_deriv : ∀ x, HasDerivAt fInv (fInvDeriv x) x)
    (hfMix_nonneg : ∀ c, 0 ≤ fMix c)
    (hfMixDeriv_nonneg : ∀ c, 0 ≤ fMixDeriv c)
    (hfInvDeriv_mono : ∀ y z, y ≤ z → fInvDeriv y ≤ fInvDeriv z)
    (hfInvDeriv_nonneg : ∀ y, 0 ≤ fInvDeriv y) :
    twoLevelDisadvantagedAccess rho cHigh (groupThreshold fInv fMix cHigh psiB)
      ≤ twoLevelDisadvantagedAccess rho cLow (groupThreshold fInv fMix cLow psiB) := by
  let gapDeriv : ℝ → ℝ := fun c =>
    fInvDeriv (fMix c / psiB) * (fMixDeriv c / psiB)
      - fInvDeriv (fMix c / psiA) * (fMixDeriv c / psiA)
  exact twoLevel_access_nonincreasing_of_mix_inverse_gap_derivative_nonneg
    (gapDeriv := gapDeriv)
    hrho hc_mono hdenLow hdenHigh hthresholdLow hmixLow hmixHigh
    (by
      intro c
      exact groupThreshold_gap_hasDerivAt
        (fInvDeriv := fInvDeriv) (fMixDeriv := fMixDeriv)
        (hfMix_deriv c) (hfInv_deriv (fMix c / psiA))
        (hfInv_deriv (fMix c / psiB)))
    (by
      intro c
      exact groupThreshold_gap_derivative_nonneg_of_scaled_deriv
        hpsiB_pos hpsi_order (hfMix_nonneg c) (hfMixDeriv_nonneg c)
        hfInvDeriv_mono hfInvDeriv_nonneg)

theorem twoLevel_access_nonincreasing_of_convex_inverse_primitives
    {rho cLow cHigh psiA psiB : ℝ}
    {fInv fMix fMixDeriv : ℝ → ℝ}
    (hrho : 0 ≤ rho)
    (hc_mono : cLow ≤ cHigh)
    (hdenLow : 0 < 1 - cLow)
    (hdenHigh : 0 < 1 - cHigh)
    (hpsiB_pos : 0 < psiB)
    (hpsi_order : psiB < psiA)
    (hthresholdLow : cLow ≤ groupThreshold fInv fMix cLow psiB)
    (hmixLow :
      (groupThreshold fInv fMix cLow psiA
          + groupThreshold fInv fMix cLow psiB) / 2 = cLow)
    (hmixHigh :
      (groupThreshold fInv fMix cHigh psiA
          + groupThreshold fInv fMix cHigh psiB) / 2 = cHigh)
    (hfMix_deriv : ∀ c, HasDerivAt fMix (fMixDeriv c) c)
    (hfMix_nonneg : ∀ c, 0 ≤ fMix c)
    (hfMixDeriv_nonneg : ∀ c, 0 ≤ fMixDeriv c)
    (hfInv_convex : ConvexOn ℝ Set.univ fInv)
    (hfInv_diff : ∀ x, DifferentiableAt ℝ fInv x)
    (hfInv_mono : Monotone fInv) :
    twoLevelDisadvantagedAccess rho cHigh (groupThreshold fInv fMix cHigh psiB)
      ≤ twoLevelDisadvantagedAccess rho cLow (groupThreshold fInv fMix cLow psiB) := by
  exact twoLevel_access_nonincreasing_of_mix_inverse_derivative_primitives
    (fInvDeriv := deriv fInv)
    hrho hc_mono hdenLow hdenHigh hpsiB_pos hpsi_order hthresholdLow
    hmixLow hmixHigh
    hfMix_deriv
    (fun x => (hfInv_diff x).hasDerivAt)
    hfMix_nonneg
    hfMixDeriv_nonneg
    (deriv_mono_of_convex_differentiable hfInv_convex hfInv_diff)
    (deriv_nonneg_of_monotone hfInv_mono)

theorem twoLevel_access_nonincreasing_of_source_shape_primitives
    {rho cLow cHigh psiA psiB : ℝ}
    {fInv fMix : ℝ → ℝ}
    (hrho : 0 ≤ rho)
    (hc_mono : cLow ≤ cHigh)
    (hdenLow : 0 < 1 - cLow)
    (hdenHigh : 0 < 1 - cHigh)
    (hpsiB_pos : 0 < psiB)
    (hpsi_order : psiB < psiA)
    (hthresholdLow : cLow ≤ groupThreshold fInv fMix cLow psiB)
    (hmixLow :
      (groupThreshold fInv fMix cLow psiA
          + groupThreshold fInv fMix cLow psiB) / 2 = cLow)
    (hmixHigh :
      (groupThreshold fInv fMix cHigh psiA
          + groupThreshold fInv fMix cHigh psiB) / 2 = cHigh)
    (hfMix_nonneg : ∀ c, 0 ≤ fMix c)
    (hfMix_diff : ∀ c, DifferentiableAt ℝ fMix c)
    (hfMix_mono : Monotone fMix)
    (hfInv_convex : ConvexOn ℝ Set.univ fInv)
    (hfInv_diff : ∀ x, DifferentiableAt ℝ fInv x)
    (hfInv_mono : Monotone fInv) :
    twoLevelDisadvantagedAccess rho cHigh (groupThreshold fInv fMix cHigh psiB)
      ≤ twoLevelDisadvantagedAccess rho cLow (groupThreshold fInv fMix cLow psiB) := by
  exact twoLevel_access_nonincreasing_of_convex_inverse_primitives
    (fMixDeriv := deriv fMix)
    hrho hc_mono hdenLow hdenHigh hpsiB_pos hpsi_order hthresholdLow
    hmixLow hmixHigh
    (fun c => (hfMix_diff c).hasDerivAt)
    hfMix_nonneg
    (deriv_nonneg_of_monotone hfMix_mono)
    hfInv_convex hfInv_diff hfInv_mono

theorem twoLevel_access_nonincreasing_of_source_shape_primitives_no_deriv
    {rho cLow cHigh psiA psiB : ℝ}
    {fInv fMix : ℝ → ℝ}
    (hrho : 0 ≤ rho)
    (hc_mono : cLow ≤ cHigh)
    (hdenLow : 0 < 1 - cLow)
    (hdenHigh : 0 < 1 - cHigh)
    (hpsiB_pos : 0 < psiB)
    (hpsi_order : psiB < psiA)
    (hthresholdLow : cLow ≤ groupThreshold fInv fMix cLow psiB)
    (hmixLow :
      (groupThreshold fInv fMix cLow psiA
          + groupThreshold fInv fMix cLow psiB) / 2 = cLow)
    (hmixHigh :
      (groupThreshold fInv fMix cHigh psiA
          + groupThreshold fInv fMix cHigh psiB) / 2 = cHigh)
    (hfMix_nonneg : ∀ c, 0 ≤ fMix c)
    (hfMix_mono : Monotone fMix)
    (hfInv_convex : ConvexOn ℝ Set.univ fInv)
    (hfInv_mono : Monotone fInv) :
    twoLevelDisadvantagedAccess rho cHigh (groupThreshold fInv fMix cHigh psiB)
      ≤ twoLevelDisadvantagedAccess rho cLow (groupThreshold fInv fMix cLow psiB) := by
  exact twoLevel_access_nonincreasing_of_convex_inverse_and_mix_mono
    hrho hc_mono hdenLow hdenHigh hpsiB_pos hpsi_order hthresholdLow
    hmixLow hmixHigh hfMix_nonneg hfMix_mono hfInv_convex hfInv_mono

theorem twoLevel_access_nonincreasing_of_source_shape_primitives_from_mix_identity
    {rho cLow cHigh psiA psiB : ℝ}
    {fInv fMix : ℝ → ℝ}
    (hrho : 0 ≤ rho)
    (hc_mono : cLow ≤ cHigh)
    (hdenLow : 0 < 1 - cLow)
    (hdenHigh : 0 < 1 - cHigh)
    (hpsiB_pos : 0 < psiB)
    (hpsi_order : psiB < psiA)
    (hmixLow :
      (groupThreshold fInv fMix cLow psiA
          + groupThreshold fInv fMix cLow psiB) / 2 = cLow)
    (hmixHigh :
      (groupThreshold fInv fMix cHigh psiA
          + groupThreshold fInv fMix cHigh psiB) / 2 = cHigh)
    (hfMix_nonneg : ∀ c, 0 ≤ fMix c)
    (hfMix_diff : ∀ c, DifferentiableAt ℝ fMix c)
    (hfMix_mono : Monotone fMix)
    (hfInv_convex : ConvexOn ℝ Set.univ fInv)
    (hfInv_diff : ∀ x, DifferentiableAt ℝ fInv x)
    (hfInv_mono : Monotone fInv) :
    twoLevelDisadvantagedAccess rho cHigh (groupThreshold fInv fMix cHigh psiB)
      ≤ twoLevelDisadvantagedAccess rho cLow (groupThreshold fInv fMix cLow psiB) := by
  have hthresholdLow : cLow ≤ groupThreshold fInv fMix cLow psiB :=
    (groupThreshold_cutoff_between_of_mix_inverse_order
      (groupThreshold_advantaged_le_disadvantaged hfInv_mono
        (hfMix_nonneg cLow) hpsiB_pos hpsi_order)
      hmixLow).2
  exact twoLevel_access_nonincreasing_of_source_shape_primitives
    hrho hc_mono hdenLow hdenHigh hpsiB_pos hpsi_order hthresholdLow
    hmixLow hmixHigh hfMix_nonneg hfMix_diff hfMix_mono hfInv_convex
    hfInv_diff hfInv_mono

theorem twoLevel_access_nonincreasing_of_source_shape_primitives_from_mix_identity_no_deriv
    {rho cLow cHigh psiA psiB : ℝ}
    {fInv fMix : ℝ → ℝ}
    (hrho : 0 ≤ rho)
    (hc_mono : cLow ≤ cHigh)
    (hdenLow : 0 < 1 - cLow)
    (hdenHigh : 0 < 1 - cHigh)
    (hpsiB_pos : 0 < psiB)
    (hpsi_order : psiB < psiA)
    (hmixLow :
      (groupThreshold fInv fMix cLow psiA
          + groupThreshold fInv fMix cLow psiB) / 2 = cLow)
    (hmixHigh :
      (groupThreshold fInv fMix cHigh psiA
          + groupThreshold fInv fMix cHigh psiB) / 2 = cHigh)
    (hfMix_nonneg : ∀ c, 0 ≤ fMix c)
    (hfMix_mono : Monotone fMix)
    (hfInv_convex : ConvexOn ℝ Set.univ fInv)
    (hfInv_mono : Monotone fInv) :
    twoLevelDisadvantagedAccess rho cHigh (groupThreshold fInv fMix cHigh psiB)
      ≤ twoLevelDisadvantagedAccess rho cLow (groupThreshold fInv fMix cLow psiB) := by
  have hthresholdLow : cLow ≤ groupThreshold fInv fMix cLow psiB :=
    (groupThreshold_cutoff_between_of_mix_inverse_order
      (groupThreshold_advantaged_le_disadvantaged hfInv_mono
        (hfMix_nonneg cLow) hpsiB_pos hpsi_order)
      hmixLow).2
  exact twoLevel_access_nonincreasing_of_source_shape_primitives_no_deriv
    hrho hc_mono hdenLow hdenHigh hpsiB_pos hpsi_order hthresholdLow
    hmixLow hmixHigh hfMix_nonneg hfMix_mono hfInv_convex hfInv_mono

theorem twoLevel_access_nonincreasing_of_source_shape_primitives_from_mix_inverse
    {rho cLow cHigh psiA psiB : ℝ}
    {fInv fMix : ℝ → ℝ}
    (hrho : 0 ≤ rho)
    (hc_mono : cLow ≤ cHigh)
    (hdenLow : 0 < 1 - cLow)
    (hdenHigh : 0 < 1 - cHigh)
    (hpsiB_pos : 0 < psiB)
    (hpsi_order : psiB < psiA)
    (hmixLow :
      twoGroupMixtureInverse fInv psiA psiB (fMix cLow) = cLow)
    (hmixHigh :
      twoGroupMixtureInverse fInv psiA psiB (fMix cHigh) = cHigh)
    (hfMix_nonneg : ∀ c, 0 ≤ fMix c)
    (hfMix_diff : ∀ c, DifferentiableAt ℝ fMix c)
    (hfMix_mono : Monotone fMix)
    (hfInv_convex : ConvexOn ℝ Set.univ fInv)
    (hfInv_diff : ∀ x, DifferentiableAt ℝ fInv x)
    (hfInv_mono : Monotone fInv) :
    twoLevelDisadvantagedAccess rho cHigh (groupThreshold fInv fMix cHigh psiB)
      ≤ twoLevelDisadvantagedAccess rho cLow (groupThreshold fInv fMix cLow psiB) := by
  exact twoLevel_access_nonincreasing_of_source_shape_primitives_from_mix_identity
    hrho hc_mono hdenLow hdenHigh hpsiB_pos hpsi_order
    (groupThreshold_mix_identity_of_twoGroupMixtureInverse hmixLow)
    (groupThreshold_mix_identity_of_twoGroupMixtureInverse hmixHigh)
    hfMix_nonneg hfMix_diff hfMix_mono hfInv_convex hfInv_diff hfInv_mono

theorem twoLevel_access_nonincreasing_of_source_shape_primitives_from_mix_inverse_no_deriv
    {rho cLow cHigh psiA psiB : ℝ}
    {fInv fMix : ℝ → ℝ}
    (hrho : 0 ≤ rho)
    (hc_mono : cLow ≤ cHigh)
    (hdenLow : 0 < 1 - cLow)
    (hdenHigh : 0 < 1 - cHigh)
    (hpsiB_pos : 0 < psiB)
    (hpsi_order : psiB < psiA)
    (hmixLow :
      twoGroupMixtureInverse fInv psiA psiB (fMix cLow) = cLow)
    (hmixHigh :
      twoGroupMixtureInverse fInv psiA psiB (fMix cHigh) = cHigh)
    (hfMix_nonneg : ∀ c, 0 ≤ fMix c)
    (hfMix_mono : Monotone fMix)
    (hfInv_convex : ConvexOn ℝ Set.univ fInv)
    (hfInv_mono : Monotone fInv) :
    twoLevelDisadvantagedAccess rho cHigh (groupThreshold fInv fMix cHigh psiB)
      ≤ twoLevelDisadvantagedAccess rho cLow (groupThreshold fInv fMix cLow psiB) := by
  exact
    twoLevel_access_nonincreasing_of_source_shape_primitives_from_mix_identity_no_deriv
      hrho hc_mono hdenLow hdenHigh hpsiB_pos hpsi_order
      (groupThreshold_mix_identity_of_twoGroupMixtureInverse hmixLow)
      (groupThreshold_mix_identity_of_twoGroupMixtureInverse hmixHigh)
      hfMix_nonneg hfMix_mono hfInv_convex hfInv_mono

theorem twoLevel_access_nonincreasing_of_source_shape_primitives_from_mix_inverse_definition
    {rho cLow cHigh psiA psiB : ℝ}
    {fInv fMix fMixInv : ℝ → ℝ}
    (hrho : 0 ≤ rho)
    (hc_mono : cLow ≤ cHigh)
    (hdenLow : 0 < 1 - cLow)
    (hdenHigh : 0 < 1 - cHigh)
    (hpsiB_pos : 0 < psiB)
    (hpsi_order : psiB < psiA)
    (hfMixInv_def :
      ∀ x, fMixInv x = twoGroupMixtureInverse fInv psiA psiB x)
    (hmixLow : fMixInv (fMix cLow) = cLow)
    (hmixHigh : fMixInv (fMix cHigh) = cHigh)
    (hfMix_nonneg : ∀ c, 0 ≤ fMix c)
    (hfMix_diff : ∀ c, DifferentiableAt ℝ fMix c)
    (hfMix_mono : Monotone fMix)
    (hfInv_convex : ConvexOn ℝ Set.univ fInv)
    (hfInv_diff : ∀ x, DifferentiableAt ℝ fInv x)
    (hfInv_mono : Monotone fInv) :
    twoLevelDisadvantagedAccess rho cHigh (groupThreshold fInv fMix cHigh psiB)
      ≤ twoLevelDisadvantagedAccess rho cLow (groupThreshold fInv fMix cLow psiB) := by
  have hmixLow' :
      twoGroupMixtureInverse fInv psiA psiB (fMix cLow) = cLow := by
    simpa [hfMixInv_def (fMix cLow)] using hmixLow
  have hmixHigh' :
      twoGroupMixtureInverse fInv psiA psiB (fMix cHigh) = cHigh := by
    simpa [hfMixInv_def (fMix cHigh)] using hmixHigh
  exact twoLevel_access_nonincreasing_of_source_shape_primitives_from_mix_inverse
    hrho hc_mono hdenLow hdenHigh hpsiB_pos hpsi_order hmixLow' hmixHigh'
    hfMix_nonneg hfMix_diff hfMix_mono hfInv_convex hfInv_diff hfInv_mono

theorem twoLevel_access_nonincreasing_of_source_shape_primitives_from_mix_inverse_definition_no_deriv
    {rho cLow cHigh psiA psiB : ℝ}
    {fInv fMix fMixInv : ℝ → ℝ}
    (hrho : 0 ≤ rho)
    (hc_mono : cLow ≤ cHigh)
    (hdenLow : 0 < 1 - cLow)
    (hdenHigh : 0 < 1 - cHigh)
    (hpsiB_pos : 0 < psiB)
    (hpsi_order : psiB < psiA)
    (hfMixInv_def :
      ∀ x, fMixInv x = twoGroupMixtureInverse fInv psiA psiB x)
    (hmixLow : fMixInv (fMix cLow) = cLow)
    (hmixHigh : fMixInv (fMix cHigh) = cHigh)
    (hfMix_nonneg : ∀ c, 0 ≤ fMix c)
    (hfMix_mono : Monotone fMix)
    (hfInv_convex : ConvexOn ℝ Set.univ fInv)
    (hfInv_mono : Monotone fInv) :
    twoLevelDisadvantagedAccess rho cHigh (groupThreshold fInv fMix cHigh psiB)
      ≤ twoLevelDisadvantagedAccess rho cLow (groupThreshold fInv fMix cLow psiB) := by
  have hmixLow' :
      twoGroupMixtureInverse fInv psiA psiB (fMix cLow) = cLow := by
    simpa [hfMixInv_def (fMix cLow)] using hmixLow
  have hmixHigh' :
      twoGroupMixtureInverse fInv psiA psiB (fMix cHigh) = cHigh := by
    simpa [hfMixInv_def (fMix cHigh)] using hmixHigh
  exact twoLevel_access_nonincreasing_of_source_shape_primitives_from_mix_inverse_no_deriv
    hrho hc_mono hdenLow hdenHigh hpsiB_pos hpsi_order hmixLow' hmixHigh'
    hfMix_nonneg hfMix_mono hfInv_convex hfInv_mono

theorem pureRandomization_access_gt_twoLevel_of_affine_threshold_slope_gt_one
    {rho a c : ℝ} (hrho : 0 < rho) (hc_pos : 0 < c) (hc_lt_one : c < 1)
    (ha : 1 < a) :
    twoLevelDisadvantagedAccess rho c (a * c) < pureRandomizationAccess rho := by
  have hthreshold : c < a * c := by
    have hmul := mul_lt_mul_of_pos_right ha hc_pos
    simpa [one_mul] using hmul
  exact pureRandomization_access_gt_twoLevel_of_threshold_gt_cutoff
    hrho hc_lt_one hthreshold

/--
In the linear skill-quantile environment calculation, the disadvantaged group's
true-rank threshold is affine in the policy cutoff with this slope.
-/
noncomputable def linearEnvironmentDisadvantagedThresholdSlope (psiA psiB : ℝ) : ℝ :=
  (2 * psiA) / (psiA + psiB)

theorem linearEnvironmentDisadvantagedThresholdSlope_gt_one
    {psiA psiB : ℝ} (hpsiB : 0 < psiB) (hadv : psiB < psiA) :
    1 < linearEnvironmentDisadvantagedThresholdSlope psiA psiB := by
  have hden : 0 < psiA + psiB := by linarith
  rw [linearEnvironmentDisadvantagedThresholdSlope, lt_div_iff₀ hden]
  linarith

theorem twoLevel_access_nonincreasing_linear_environment
    {rho psiA psiB cLow cHigh : ℝ}
    (hrho : 0 ≤ rho)
    (hpsiB : 0 < psiB)
    (hadv : psiB < psiA)
    (hc_mono : cLow ≤ cHigh)
    (hdenLow : 0 < 1 - cLow)
    (hdenHigh : 0 < 1 - cHigh) :
    twoLevelDisadvantagedAccess rho cHigh
        (linearEnvironmentDisadvantagedThresholdSlope psiA psiB * cHigh)
      ≤ twoLevelDisadvantagedAccess rho cLow
        (linearEnvironmentDisadvantagedThresholdSlope psiA psiB * cLow) := by
  exact twoLevel_access_nonincreasing_of_affine_threshold_slope_ge_one
    hrho (le_of_lt (linearEnvironmentDisadvantagedThresholdSlope_gt_one hpsiB hadv))
    hc_mono hdenLow hdenHigh

theorem pureRandomization_access_gt_twoLevel_linear_environment
    {rho psiA psiB c : ℝ}
    (hrho : 0 < rho)
    (hpsiB : 0 < psiB)
    (hadv : psiB < psiA)
    (hc_pos : 0 < c)
    (hc_lt_one : c < 1) :
    twoLevelDisadvantagedAccess rho c
        (linearEnvironmentDisadvantagedThresholdSlope psiA psiB * c)
      < pureRandomizationAccess rho := by
  exact pureRandomization_access_gt_twoLevel_of_affine_threshold_slope_gt_one
    hrho hc_pos hc_lt_one
    (linearEnvironmentDisadvantagedThresholdSlope_gt_one hpsiB hadv)

/--
Squared societal utility for the source-family witness
`f(c) = c`, `g(e) = e`, and `cost(e) = e^2`.

For this setting the one-threshold societal utility is
`sqrt rho * c * sqrt (1 - c)`, so maximizing the nonnegative utility is
equivalent to maximizing this squared objective.
-/
def linearEffortSquaredCostSocietalUtilitySquared (rho c : ℝ) : ℝ :=
  rho * c ^ 2 * (1 - c)

noncomputable def linearEffortSquaredCostSocietalUtility (rho c : ℝ) : ℝ :=
  Real.sqrt rho * c * Real.sqrt (1 - c)

theorem linearEffortSquaredCostSocietalUtility_sq
    {rho c : ℝ} (hrho : 0 ≤ rho) (hc_upper : c ≤ 1) :
    linearEffortSquaredCostSocietalUtility rho c ^ 2 =
      linearEffortSquaredCostSocietalUtilitySquared rho c := by
  unfold linearEffortSquaredCostSocietalUtility
  unfold linearEffortSquaredCostSocietalUtilitySquared
  rw [mul_pow, mul_pow, Real.sq_sqrt hrho, Real.sq_sqrt (sub_nonneg.mpr hc_upper)]

theorem linearEffortSquaredCostSocietalUtilitySquared_maximized_at_two_thirds
    {rho : ℝ} (hrho : 0 ≤ rho) :
    MaximizesOnInterval
      (linearEffortSquaredCostSocietalUtilitySquared rho) ((2 : ℝ) / 3) 0 1 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro y hy0 hy1
  have hbase :
      y ^ 2 * (1 - y) ≤ ((2 : ℝ) / 3) ^ 2 * (1 - (2 : ℝ) / 3) := by
    have hfactor :
        ((2 : ℝ) / 3) ^ 2 * (1 - (2 : ℝ) / 3) - y ^ 2 * (1 - y)
          = (y - (2 : ℝ) / 3) ^ 2 * (y + (1 : ℝ) / 3) := by
      ring
    have hnonneg :
        0 ≤ (y - (2 : ℝ) / 3) ^ 2 * (y + (1 : ℝ) / 3) :=
      mul_nonneg (sq_nonneg _) (by linarith)
    nlinarith
  have hscaled :
      rho * (y ^ 2 * (1 - y))
        ≤ rho * (((2 : ℝ) / 3) ^ 2 * (1 - (2 : ℝ) / 3)) :=
    mul_le_mul_of_nonneg_left hbase hrho
  unfold linearEffortSquaredCostSocietalUtilitySquared
  nlinarith

theorem linearEffortSquaredCostSocietalUtility_maximized_at_two_thirds
    {rho : ℝ} (hrho : 0 ≤ rho) :
    MaximizesOnInterval
      (linearEffortSquaredCostSocietalUtility rho) ((2 : ℝ) / 3) 0 1 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro y hy0 hy1
  have hsquared :=
    (linearEffortSquaredCostSocietalUtilitySquared_maximized_at_two_thirds
      (rho := rho) hrho).2.2 y hy0 hy1
  have hsq_y :
      linearEffortSquaredCostSocietalUtility rho y ^ 2 =
        linearEffortSquaredCostSocietalUtilitySquared rho y :=
    linearEffortSquaredCostSocietalUtility_sq hrho hy1
  have hsq_best :
      linearEffortSquaredCostSocietalUtility rho ((2 : ℝ) / 3) ^ 2 =
        linearEffortSquaredCostSocietalUtilitySquared rho ((2 : ℝ) / 3) :=
    linearEffortSquaredCostSocietalUtility_sq hrho (by norm_num)
  have hsq :
      linearEffortSquaredCostSocietalUtility rho y ^ 2
        ≤ linearEffortSquaredCostSocietalUtility rho ((2 : ℝ) / 3) ^ 2 := by
    simpa [hsq_y, hsq_best] using hsquared
  have hy_nonneg :
      0 ≤ linearEffortSquaredCostSocietalUtility rho y := by
    unfold linearEffortSquaredCostSocietalUtility
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg rho) hy0) (Real.sqrt_nonneg _)
  have hbest_nonneg :
      0 ≤ linearEffortSquaredCostSocietalUtility rho ((2 : ℝ) / 3) := by
    unfold linearEffortSquaredCostSocietalUtility
    exact mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg rho) (by norm_num))
      (Real.sqrt_nonneg _)
  exact (sq_le_sq₀ hy_nonneg hbest_nonneg).mp hsq

/--
Source Proposition `prop:SocUtil`, as a concrete source-family
interior-maximizer witness. With `f(c)=c`, `g(e)=e`, and `cost(e)=e^2`, the
nonnegative societal utility is maximized at the same cutoff as its square
`rho * c^2 * (1-c)`. The witness `rho = 1/4`, `c = 2/3` has
`ell_1 = rho/(1-c)` strictly between `rho` and `1`.
-/
theorem exists_twoLevel_societalUtility_interior_maximizer :
    ∃ rho c : ℝ,
      0 < rho ∧ rho < 1 ∧ 0 < c ∧ c < 1 - rho ∧
      (rho < rho / (1 - c) ∧ rho / (1 - c) < 1) ∧
      MaximizesOnInterval (linearEffortSquaredCostSocietalUtility rho)
        c 0 (1 - rho) := by
  refine ⟨(1 : ℝ) / 4, (2 : ℝ) / 3, ?_⟩
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · norm_num
  · refine ⟨by norm_num, by norm_num, ?_⟩
    intro y hy0 hyhi
    have hy1 : y ≤ 1 := by linarith
    exact (linearEffortSquaredCostSocietalUtility_maximized_at_two_thirds
      (rho := (1 : ℝ) / 4) (by norm_num)).2.2 y hy0 hy1

/-- Derivative of a weighted two-skill utility at a fixed two-level cutoff. -/
def weightedUtilityDerivative (beta dMeasurable dUnmeasurable : ℝ) : ℝ :=
  beta * dMeasurable + (1 - beta) * dUnmeasurable

/-- The positive scalarization weight that balances two opposite derivatives. -/
noncomputable def weightedUtilityBalancingWeight
    (dMeasurable dUnmeasurable : ℝ) : ℝ :=
  -dUnmeasurable / (dMeasurable - dUnmeasurable)

theorem weightedUtilityBalancingWeight_mem_Ioo
    {dMeasurable dUnmeasurable : ℝ}
    (hM : 0 < dMeasurable)
    (hU : dUnmeasurable < 0) :
    weightedUtilityBalancingWeight dMeasurable dUnmeasurable ∈ Set.Ioo 0 1 := by
  have hden_pos : 0 < dMeasurable - dUnmeasurable := by linarith
  constructor
  · exact div_pos (neg_pos.mpr hU) hden_pos
  · rw [weightedUtilityBalancingWeight, div_lt_one hden_pos]
    linarith

theorem weightedUtilityDerivative_balancingWeight
    {dMeasurable dUnmeasurable : ℝ}
    (hM : 0 < dMeasurable)
    (hU : dUnmeasurable < 0) :
    weightedUtilityDerivative
      (weightedUtilityBalancingWeight dMeasurable dUnmeasurable)
      dMeasurable dUnmeasurable = 0 := by
  have hden_ne : dMeasurable - dUnmeasurable ≠ 0 := by linarith
  rw [weightedUtilityBalancingWeight]
  unfold weightedUtilityDerivative
  field_simp [hden_ne]
  ring

theorem weightedUtilityDerivative_sub_eq
    (firstWeight secondWeight dMeasurable dUnmeasurable : ℝ) :
    weightedUtilityDerivative firstWeight dMeasurable dUnmeasurable -
        weightedUtilityDerivative secondWeight dMeasurable dUnmeasurable =
      (firstWeight - secondWeight) * (dMeasurable - dUnmeasurable) := by
  unfold weightedUtilityDerivative
  ring

/-- Weighted private utility from measurable and unmeasurable utility components. -/
def weightedPrivateUtility (beta : ℝ) (measurableUtility unmeasurableUtility : ℝ → ℝ) :
    ℝ → ℝ :=
  fun c => beta * measurableUtility c + (1 - beta) * unmeasurableUtility c

/--
Source Proposition `prop:2levels-fixedcap`, algebraic balancing step: if the
measurable-skill derivative is positive and the unmeasurable-skill derivative
is negative at a cutoff, some weight `beta in (0,1)` makes the weighted
first-order condition zero.
-/
theorem exists_beta_weightedUtilityDerivative_eq_zero
    {dMeasurable dUnmeasurable : ℝ}
    (hM : 0 < dMeasurable)
    (hU : dUnmeasurable < 0) :
    ∃ beta : ℝ,
      0 < beta ∧ beta < 1 ∧
      weightedUtilityDerivative beta dMeasurable dUnmeasurable = 0 := by
  exact ⟨weightedUtilityBalancingWeight dMeasurable dUnmeasurable,
    (weightedUtilityBalancingWeight_mem_Ioo hM hU).1,
    (weightedUtilityBalancingWeight_mem_Ioo hM hU).2,
    weightedUtilityDerivative_balancingWeight hM hU⟩

/--
Calculus form of the same source first-order condition: if the two component
utilities have derivatives of opposite sign at the cutoff, some `beta in (0,1)`
makes the weighted private utility stationary at that cutoff.
-/
theorem exists_beta_weightedPrivateUtility_hasDerivAt_zero
    {measurableUtility unmeasurableUtility : ℝ → ℝ}
    {c dMeasurable dUnmeasurable : ℝ}
    (hMderiv : HasDerivAt measurableUtility dMeasurable c)
    (hUderiv : HasDerivAt unmeasurableUtility dUnmeasurable c)
    (hM : 0 < dMeasurable)
    (hU : dUnmeasurable < 0) :
    ∃ beta : ℝ,
      0 < beta ∧ beta < 1 ∧
      HasDerivAt (weightedPrivateUtility beta measurableUtility unmeasurableUtility) 0 c := by
  rcases exists_beta_weightedUtilityDerivative_eq_zero hM hU with
    ⟨beta, hbeta_pos, hbeta_lt, hzero⟩
  refine ⟨beta, hbeta_pos, hbeta_lt, ?_⟩
  have hderiv :
      HasDerivAt (weightedPrivateUtility beta measurableUtility unmeasurableUtility)
        (weightedUtilityDerivative beta dMeasurable dUnmeasurable) c := by
    simpa [weightedPrivateUtility, weightedUtilityDerivative]
      using (hMderiv.const_mul beta).add
        (hUderiv.const_mul (1 - beta))
  simpa [hzero] using hderiv

/--
Global recovery requiring no supporting-frontier assumption: when measurable
utility strictly rises and unmeasurable utility strictly falls with the cutoff,
every feasible cutoff is Pareto efficient.  Concavity is only needed for the
stronger claim that a positive linear weight globally supports each cutoff.
-/
theorem every_cutoff_isTwoUtilityParetoEfficient_of_strict_tradeoff
    {measurableUtility unmeasurableUtility : ℝ → ℝ}
    {lo c hi : ℝ}
    (hmeasurable_strictMono :
      StrictMonoOn measurableUtility (Set.Icc lo hi))
    (hunmeasurable_strictAnti :
      StrictAntiOn unmeasurableUtility (Set.Icc lo hi))
    (hc : c ∈ Set.Icc lo hi) :
    AppliedModelingLib.IsTwoUtilityParetoEfficientOn
      (Set.Icc lo hi) measurableUtility unmeasurableUtility c :=
  AppliedModelingLib.isTwoUtilityParetoEfficientOn_of_strictTradeoff
    hmeasurable_strictMono hunmeasurable_strictAnti hc

/--
Weak headline recovery for Proposition B.2.  If the marginal scalarization
weight at the low-cutoff endpoint is smaller than the corresponding weight at
the high-cutoff endpoint, a weight between them makes the weighted objective
rise away from the low endpoint and fall toward the high endpoint.  Continuity
then gives some interior, hence genuinely randomized, global maximizer.

Unlike the supported-frontier condition, this endpoint crossing does not claim
that an arbitrary prescribed cutoff can be made optimal.
-/
theorem exists_weightedPrivateUtility_interior_maximizer_of_endpoint_crossing
    {measurableUtility unmeasurableUtility : ℝ → ℝ}
    {lo hi dMLo dULo dMHi dUHi : ℝ}
    (hlohi : lo < hi)
    (hMcont : ContinuousOn measurableUtility (Set.Icc lo hi))
    (hUcont : ContinuousOn unmeasurableUtility (Set.Icc lo hi))
    (hMderiv_lo : HasDerivAt measurableUtility dMLo lo)
    (hUderiv_lo : HasDerivAt unmeasurableUtility dULo lo)
    (hMderiv_hi : HasDerivAt measurableUtility dMHi hi)
    (hUderiv_hi : HasDerivAt unmeasurableUtility dUHi hi)
    (hdMLo_pos : 0 < dMLo)
    (hdULo_neg : dULo < 0)
    (hdMHi_pos : 0 < dMHi)
    (hdUHi_neg : dUHi < 0)
    (hcrossing :
      weightedUtilityBalancingWeight dMLo dULo <
        weightedUtilityBalancingWeight dMHi dUHi) :
    ∃ beta maximizer : ℝ,
      0 < beta ∧ beta < 1 ∧ maximizer ∈ Set.Ioo lo hi ∧
      MaximizesOnInterval
        (weightedPrivateUtility beta measurableUtility unmeasurableUtility)
        maximizer lo hi := by
  let betaLo := weightedUtilityBalancingWeight dMLo dULo
  let betaHi := weightedUtilityBalancingWeight dMHi dUHi
  let beta := (betaLo + betaHi) / 2
  have hbetaLo_mem : betaLo ∈ Set.Ioo (0 : ℝ) 1 :=
    weightedUtilityBalancingWeight_mem_Ioo hdMLo_pos hdULo_neg
  have hbetaHi_mem : betaHi ∈ Set.Ioo (0 : ℝ) 1 :=
    weightedUtilityBalancingWeight_mem_Ioo hdMHi_pos hdUHi_neg
  have hbetaLo_lt : betaLo < beta := by
    dsimp only [beta]
    linarith
  have hbeta_lt_betaHi : beta < betaHi := by
    dsimp only [beta]
    linarith
  have hbeta_pos : 0 < beta := by linarith [hbetaLo_mem.1]
  have hbeta_lt_one : beta < 1 := by linarith [hbetaHi_mem.2]
  have hzero_lo : weightedUtilityDerivative betaLo dMLo dULo = 0 :=
    weightedUtilityDerivative_balancingWeight hdMLo_pos hdULo_neg
  have hzero_hi : weightedUtilityDerivative betaHi dMHi dUHi = 0 :=
    weightedUtilityDerivative_balancingWeight hdMHi_pos hdUHi_neg
  have hweighted_deriv_lo_pos :
      0 < weightedUtilityDerivative beta dMLo dULo := by
    have hdiff := weightedUtilityDerivative_sub_eq beta betaLo dMLo dULo
    have hproduct : 0 < (beta - betaLo) * (dMLo - dULo) :=
      mul_pos (sub_pos.mpr hbetaLo_lt) (by linarith)
    rw [hzero_lo, sub_zero] at hdiff
    linarith
  have hweighted_deriv_hi_neg :
      weightedUtilityDerivative beta dMHi dUHi < 0 := by
    have hdiff := weightedUtilityDerivative_sub_eq beta betaHi dMHi dUHi
    have hproduct : (beta - betaHi) * (dMHi - dUHi) < 0 :=
      mul_neg_of_neg_of_pos (sub_neg.mpr hbeta_lt_betaHi) (by linarith)
    rw [hzero_hi, sub_zero] at hdiff
    linarith
  have hweighted_cont :
      ContinuousOn
        (weightedPrivateUtility beta measurableUtility unmeasurableUtility)
        (Set.Icc lo hi) := by
    simpa [weightedPrivateUtility] using
      (hMcont.const_mul beta).add (hUcont.const_mul (1 - beta))
  have hweighted_deriv_lo :
      HasDerivAt
        (weightedPrivateUtility beta measurableUtility unmeasurableUtility)
        (weightedUtilityDerivative beta dMLo dULo) lo := by
    simpa [weightedPrivateUtility, weightedUtilityDerivative] using
      (hMderiv_lo.const_mul beta).add
        (hUderiv_lo.const_mul (1 - beta))
  have hweighted_deriv_hi :
      HasDerivAt
        (weightedPrivateUtility beta measurableUtility unmeasurableUtility)
        (weightedUtilityDerivative beta dMHi dUHi) hi := by
    simpa [weightedPrivateUtility, weightedUtilityDerivative] using
      (hMderiv_hi.const_mul beta).add
        (hUderiv_hi.const_mul (1 - beta))
  rcases AppliedModelingLib.Optimization.exists_interior_maximizer_of_endpoint_derivative_signs
      hlohi hweighted_cont hweighted_deriv_lo hweighted_deriv_lo_pos
      hweighted_deriv_hi hweighted_deriv_hi_neg with
    ⟨maximizer, hmaximizer, hmax⟩
  refine ⟨beta, maximizer, hbeta_pos, hbeta_lt_one, hmaximizer,
    hmaximizer.1.le, hmaximizer.2.le, ?_⟩
  intro y hylo hyhi
  exact hmax y ⟨hylo, hyhi⟩

/--
A stationary point of a concave real objective is a global maximizer on the
interval.  This is the supporting-line step needed when a paper's first-order
condition is supplemented by an economically meaningful frontier shape.

Upstream credit: the proof directly uses Mathlib's supporting-slope lemmas
`ConcaveOn.le_slope_of_hasDerivAt` and
`ConcaveOn.slope_le_of_hasDerivAt` from
[`Analysis/Convex/Deriv.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/Convex/Deriv.lean),
under Mathlib's Apache-2.0 license.  No external source is copied or ported.
-/
theorem maximizesOnInterval_of_concaveOn_hasDerivAt_zero
    {objective : ℝ → ℝ} {lo c hi : ℝ}
    (hlo : lo ≤ c)
    (hhi : c ≤ hi)
    (hconcave : ConcaveOn ℝ (Set.Icc lo hi) objective)
    (hstationary : HasDerivAt objective 0 c) :
    MaximizesOnInterval objective c lo hi := by
  refine ⟨hlo, hhi, ?_⟩
  intro y hylo hyhi
  rcases lt_trichotomy y c with hyc | rfl | hcy
  · have hslope : 0 ≤ slope objective y c :=
      hconcave.le_slope_of_hasDerivAt
        ⟨hylo, le_trans (le_of_lt hyc) hhi⟩ ⟨hlo, hhi⟩ hyc hstationary
    rw [slope_def_field] at hslope
    rcases (div_nonneg_iff.mp hslope) with hsign | hsign
    · linarith
    · linarith
  · exact le_rfl
  · have hslope : slope objective c y ≤ 0 :=
      hconcave.slope_le_of_hasDerivAt
        ⟨hlo, le_trans (le_of_lt hcy) hyhi⟩
        ⟨hlo.trans (le_of_lt hcy), hyhi⟩ hcy hstationary
    rw [slope_def_field] at hslope
    rcases (div_nonpos_iff.mp hslope) with hsign | hsign
    · linarith
    · linarith

/--
Exact target-specific support condition for a weighted two-utility optimum.
If the unmeasurable-utility frontier has any negative-slope supporting line at
the target measurable utility, the corresponding positive scalarization weight
makes that target cutoff a global maximizer.  No global concavity or derivative
assumption is needed.
-/
theorem exists_beta_weightedPrivateUtility_maximizesOnInterval_of_frontier_support
    {measurableUtility unmeasurableUtility frontier : ℝ → ℝ}
    {lo c hi supportSlope : ℝ}
    (hlo : lo ≤ c)
    (hhi : c ≤ hi)
    (hmeasurable_mono :
      MonotoneOn measurableUtility (Set.Icc lo hi))
    (hunmeasurable_factor :
      ∀ x ∈ Set.Icc lo hi,
        unmeasurableUtility x = frontier (measurableUtility x))
    (hsupport :
      ∀ output ∈
          Set.Icc (measurableUtility lo) (measurableUtility hi),
        frontier output ≤
          frontier (measurableUtility c) +
            supportSlope * (output - measurableUtility c))
    (hslope_neg : supportSlope < 0) :
    ∃ beta : ℝ,
      0 < beta ∧ beta < 1 ∧
      MaximizesOnInterval
        (weightedPrivateUtility beta measurableUtility unmeasurableUtility)
        c lo hi := by
  let beta : ℝ := -supportSlope / (1 - supportSlope)
  have hden_pos : 0 < 1 - supportSlope := by linarith
  have hbeta_pos : 0 < beta :=
    div_pos (neg_pos.mpr hslope_neg) hden_pos
  have hbeta_lt_one : beta < 1 := by
    dsimp only [beta]
    rw [div_lt_one hden_pos]
    linarith
  have hone_minus_nonneg : 0 ≤ 1 - beta := by linarith
  have hcoefficient_zero : beta + (1 - beta) * supportSlope = 0 := by
    dsimp only [beta]
    field_simp [hden_pos.ne']
    ring
  have hlohi : lo ≤ hi := hlo.trans hhi
  have hlo_mem : lo ∈ Set.Icc lo hi := ⟨le_rfl, hlohi⟩
  have hc_mem : c ∈ Set.Icc lo hi := ⟨hlo, hhi⟩
  have hhi_mem : hi ∈ Set.Icc lo hi := ⟨hlohi, le_rfl⟩
  refine ⟨beta, hbeta_pos, hbeta_lt_one, hlo, hhi, ?_⟩
  intro y hylo hyhi
  have hy_mem : y ∈ Set.Icc lo hi := ⟨hylo, hyhi⟩
  have hMy_lo : measurableUtility lo ≤ measurableUtility y :=
    hmeasurable_mono hlo_mem hy_mem hylo
  have hMy_hi : measurableUtility y ≤ measurableUtility hi :=
    hmeasurable_mono hy_mem hhi_mem hyhi
  have hfrontier := hsupport (measurableUtility y) ⟨hMy_lo, hMy_hi⟩
  unfold weightedPrivateUtility
  rw [hunmeasurable_factor y hy_mem,
    hunmeasurable_factor c hc_mem]
  have hscaled := mul_le_mul_of_nonneg_left hfrontier hone_minus_nonneg
  calc
    beta * measurableUtility y +
        (1 - beta) * frontier (measurableUtility y) ≤
      beta * measurableUtility y +
        (1 - beta) *
          (frontier (measurableUtility c) +
            supportSlope *
              (measurableUtility y - measurableUtility c)) :=
      by simpa [add_comm] using
        (add_le_add_left hscaled (beta * measurableUtility y))
    _ = beta * measurableUtility c +
        (1 - beta) * frontier (measurableUtility c) := by
      calc
        beta * measurableUtility y +
            (1 - beta) *
              (frontier (measurableUtility c) +
                supportSlope *
                  (measurableUtility y - measurableUtility c)) =
          beta * measurableUtility c +
              (1 - beta) * frontier (measurableUtility c) +
            (beta + (1 - beta) * supportSlope) *
              (measurableUtility y - measurableUtility c) := by ring
        _ = beta * measurableUtility c +
            (1 - beta) * frontier (measurableUtility c) := by
          rw [hcoefficient_zero]
          ring

/--
Primitive-style completion of Proposition B.2 in measurable-output
coordinates.  Suppose the measurable utility `M` is nondecreasing over the
cutoff interval and the unmeasurable utility factors as
`U(c) = frontier (M(c))`.  If that frontier is concave and has negative slope
at the target output, then a positive linear weight supports the target cutoff
globally.

Unlike a condition that both `M` and `U` be concave in the arbitrary cutoff
parameter, concavity of `frontier` is invariant under increasing
reparameterizations.  Economically it says that marginal unmeasurable-skill
loss per additional unit of measurable skill weakly increases.
-/
theorem exists_beta_weightedPrivateUtility_maximizesOnInterval_of_concave_frontier
    {measurableUtility unmeasurableUtility frontier : ℝ → ℝ}
    {lo c hi frontierDerivative : ℝ}
    (hlo : lo ≤ c)
    (hhi : c ≤ hi)
    (hmeasurable_mono :
      MonotoneOn measurableUtility (Set.Icc lo hi))
    (hunmeasurable_factor :
      ∀ x ∈ Set.Icc lo hi,
        unmeasurableUtility x = frontier (measurableUtility x))
    (hfrontier_concave :
      ConcaveOn ℝ
        (Set.Icc (measurableUtility lo) (measurableUtility hi)) frontier)
    (hfrontier_deriv :
      HasDerivAt frontier frontierDerivative (measurableUtility c))
    (hfrontier_decreasing : frontierDerivative < 0) :
    ∃ beta : ℝ,
      0 < beta ∧ beta < 1 ∧
      MaximizesOnInterval
        (weightedPrivateUtility beta measurableUtility unmeasurableUtility)
        c lo hi := by
  have hlohi : lo ≤ hi := hlo.trans hhi
  have hlo_mem : lo ∈ Set.Icc lo hi := ⟨le_rfl, hlohi⟩
  have hc_mem : c ∈ Set.Icc lo hi := ⟨hlo, hhi⟩
  have hhi_mem : hi ∈ Set.Icc lo hi := ⟨hlohi, le_rfl⟩
  have hMloMc : measurableUtility lo ≤ measurableUtility c :=
    hmeasurable_mono hlo_mem hc_mem hlo
  have hMcMhi : measurableUtility c ≤ measurableUtility hi :=
    hmeasurable_mono hc_mem hhi_mem hhi
  have hid_deriv : HasDerivAt (fun output : ℝ => output) 1 (measurableUtility c) :=
    hasDerivAt_id _
  rcases exists_beta_weightedPrivateUtility_hasDerivAt_zero
      hid_deriv hfrontier_deriv (by norm_num) hfrontier_decreasing with
    ⟨beta, hbeta_pos, hbeta_lt, hstationary⟩
  have hbeta_nonneg : 0 ≤ beta := hbeta_pos.le
  have hone_minus_nonneg : 0 ≤ 1 - beta := by linarith
  have hid_concave :
      ConcaveOn ℝ
        (Set.Icc (measurableUtility lo) (measurableUtility hi))
        (fun output : ℝ => output) :=
    concaveOn_id (convex_Icc _ _)
  have hweighted_concave :
      ConcaveOn ℝ
        (Set.Icc (measurableUtility lo) (measurableUtility hi))
        (weightedPrivateUtility beta (fun output : ℝ => output) frontier) := by
    have hmeasurable_weighted :=
      ConcaveOn.smul hbeta_nonneg hid_concave
    have hunmeasurable_weighted :=
      ConcaveOn.smul hone_minus_nonneg hfrontier_concave
    simpa [weightedPrivateUtility, Pi.add_apply, smul_eq_mul] using
      hmeasurable_weighted.add hunmeasurable_weighted
  have hfrontier_max :=
    maximizesOnInterval_of_concaveOn_hasDerivAt_zero
      hMloMc hMcMhi hweighted_concave hstationary
  refine ⟨beta, hbeta_pos, hbeta_lt, hlo, hhi, ?_⟩
  intro y hylo hyhi
  have hy_mem : y ∈ Set.Icc lo hi := ⟨hylo, hyhi⟩
  have hMy_lo : measurableUtility lo ≤ measurableUtility y :=
    hmeasurable_mono hlo_mem hy_mem hylo
  have hMy_hi : measurableUtility y ≤ measurableUtility hi :=
    hmeasurable_mono hy_mem hhi_mem hyhi
  have hcompare := hfrontier_max.2.2 (measurableUtility y) hMy_lo hMy_hi
  simpa [weightedPrivateUtility,
    hunmeasurable_factor y hy_mem,
    hunmeasurable_factor c hc_mem] using hcompare

/--
Type-level shape completion of Proposition B.2.  It is enough to assume
directly that every normalized admitted type's residual-task output is
nonincreasing and concave in the measurable-output target.  This is weaker
than convexity of measurable-task effort because production curvature may
offset mild concavity in the effort response.
-/
theorem exists_beta_weightedPrivateUtility_maximizesOnInterval_of_residual_shape
    {Agent : Type*} [MeasurableSpace Agent]
    (μ : Measure Agent)
    (typeWeight : Agent → ℝ)
    (production : ℝ → ℝ)
    (budget : ℝ)
    (effortResponse : Agent → ℝ → ℝ)
    {measurableUtility unmeasurableUtility : ℝ → ℝ}
    {lo c hi frontierDerivative : ℝ}
    (hlo : lo ≤ c)
    (hhi : c ≤ hi)
    (hmeasurable_mono :
      MonotoneOn measurableUtility (Set.Icc lo hi))
    (hunmeasurable_eq :
      ∀ x ∈ Set.Icc lo hi,
        unmeasurableUtility x =
          AppliedModelingLib.aggregateCrowdOutUtility
            μ typeWeight production budget effortResponse
            (measurableUtility x))
    (hweight_nonneg : ∀ᵐ agent ∂μ, 0 ≤ typeWeight agent)
    (hresidual_concave :
      ∀ᵐ agent ∂μ,
        ConcaveOn ℝ
          (Set.Icc (measurableUtility lo) (measurableUtility hi))
          (fun target => production (budget - effortResponse agent target)))
    (hresidual_antitone :
      ∀ᵐ agent ∂μ,
        AntitoneOn
          (fun target => production (budget - effortResponse agent target))
          (Set.Icc (measurableUtility lo) (measurableUtility hi)))
    (hintegrable :
      ∀ target ∈ Set.Icc (measurableUtility lo) (measurableUtility hi),
        Integrable
          (fun agent =>
            typeWeight agent *
              production (budget - effortResponse agent target)) μ)
    (hfrontier_deriv :
      HasDerivAt
        (AppliedModelingLib.aggregateCrowdOutUtility
          μ typeWeight production budget effortResponse)
        frontierDerivative (measurableUtility c))
    (hfrontier_decreasing : frontierDerivative < 0) :
    ∃ beta : ℝ,
      0 < beta ∧ beta < 1 ∧
      MaximizesOnInterval
        (weightedPrivateUtility beta measurableUtility unmeasurableUtility)
        c lo hi := by
  have hfrontier_shape :=
    AppliedModelingLib.aggregateCrowdOutUtility_concaveOn_and_antitoneOn_of_residual_shape
      μ typeWeight production budget effortResponse
      (Set.Icc (measurableUtility lo) (measurableUtility hi))
      (convex_Icc _ _) hweight_nonneg hresidual_concave hresidual_antitone
      hintegrable
  exact
    exists_beta_weightedPrivateUtility_maximizesOnInterval_of_concave_frontier
      hlo hhi hmeasurable_mono hunmeasurable_eq hfrontier_shape.1
      hfrontier_deriv hfrontier_decreasing

/--
Behavioral-primitive completion of Proposition B.2.  Agent types may be
normalized admitted-class quantiles.  If their measurable-task effort is
nondecreasing and convex in the admitted measurable-output target, then an
increasing concave production technology makes aggregate unmeasurable utility
a nonincreasing concave frontier.  A strictly negative frontier derivative at
the target then supplies the source weight supporting that cutoff globally.
-/
theorem exists_beta_weightedPrivateUtility_maximizesOnInterval_of_convex_effort_response
    {Agent : Type*} [MeasurableSpace Agent]
    (μ : Measure Agent)
    (typeWeight : Agent → ℝ)
    (production : ℝ → ℝ)
    (budget : ℝ)
    (effortResponse : Agent → ℝ → ℝ)
    {measurableUtility unmeasurableUtility : ℝ → ℝ}
    {lo c hi frontierDerivative : ℝ}
    (hlo : lo ≤ c)
    (hhi : c ≤ hi)
    (hmeasurable_mono :
      MonotoneOn measurableUtility (Set.Icc lo hi))
    (hunmeasurable_eq :
      ∀ x ∈ Set.Icc lo hi,
        unmeasurableUtility x =
          AppliedModelingLib.aggregateCrowdOutUtility
            μ typeWeight production budget effortResponse
            (measurableUtility x))
    (hproduction_concave : ConcaveOn ℝ Set.univ production)
    (hproduction_mono : Monotone production)
    (hweight_nonneg : ∀ᵐ agent ∂μ, 0 ≤ typeWeight agent)
    (heffort_convex :
      ∀ᵐ agent ∂μ,
        ConvexOn ℝ
          (Set.Icc (measurableUtility lo) (measurableUtility hi))
          (effortResponse agent))
    (heffort_mono :
      ∀ᵐ agent ∂μ,
        MonotoneOn (effortResponse agent)
          (Set.Icc (measurableUtility lo) (measurableUtility hi)))
    (hintegrable :
      ∀ target ∈ Set.Icc (measurableUtility lo) (measurableUtility hi),
        Integrable
          (fun agent =>
            typeWeight agent *
              production (budget - effortResponse agent target)) μ)
    (hfrontier_deriv :
      HasDerivAt
        (AppliedModelingLib.aggregateCrowdOutUtility
          μ typeWeight production budget effortResponse)
        frontierDerivative (measurableUtility c))
    (hfrontier_decreasing : frontierDerivative < 0) :
    ∃ beta : ℝ,
      0 < beta ∧ beta < 1 ∧
      MaximizesOnInterval
        (weightedPrivateUtility beta measurableUtility unmeasurableUtility)
        c lo hi := by
  have hfrontier_shape :=
    AppliedModelingLib.aggregateCrowdOutUtility_concaveOn_and_antitoneOn
      μ typeWeight production budget effortResponse
      (Set.Icc (measurableUtility lo) (measurableUtility hi))
      (convex_Icc _ _) hproduction_concave hproduction_mono
      hweight_nonneg heffort_convex heffort_mono hintegrable
  exact
    exists_beta_weightedPrivateUtility_maximizesOnInterval_of_concave_frontier
      hlo hhi hmeasurable_mono hunmeasurable_eq hfrontier_shape.1
      hfrontier_deriv hfrontier_decreasing

/--
Technology-level completion of Proposition B.2.  Rather than postulating the
shape of effort directly, specify a concave strictly increasing production
technology, a right inverse on the economically relevant score range, and an
effective score requirement for each admitted type.  If that requirement is
nondecreasing and convex in the measurable-output target, the inverse
technology produces the convex nondecreasing effort response used by the
preceding theorem.

The two range conditions are substantive feasibility checks: required scores
must remain in the inverse's target range, and inverse outputs must remain in
the technology's effort domain.  No global inverse assumption is needed.
-/
theorem exists_beta_weightedPrivateUtility_maximizesOnInterval_of_convex_effectiveInput
    {Agent : Type*} [MeasurableSpace Agent]
    (μ : Measure Agent)
    (typeWeight : Agent → ℝ)
    (production productionInv : ℝ → ℝ)
    (budget : ℝ)
    (effectiveInput : Agent → ℝ → ℝ)
    (effortDomain inputDomain : Set ℝ)
    {measurableUtility unmeasurableUtility : ℝ → ℝ}
    {lo c hi frontierDerivative : ℝ}
    (hlo : lo ≤ c)
    (hhi : c ≤ hi)
    (hmeasurable_mono :
      MonotoneOn measurableUtility (Set.Icc lo hi))
    (hunmeasurable_eq :
      ∀ x ∈ Set.Icc lo hi,
        unmeasurableUtility x =
          AppliedModelingLib.aggregateCrowdOutUtility
            μ typeWeight production budget
            (fun agent target => productionInv (effectiveInput agent target))
            (measurableUtility x))
    (heffortDomain_convex : Convex ℝ effortDomain)
    (hinputDomain_convex : Convex ℝ inputDomain)
    (hproduction_concave : ConcaveOn ℝ Set.univ production)
    (hproduction_mono : Monotone production)
    (hproduction_strictMono : StrictMonoOn production effortDomain)
    (hinverse_maps : Set.MapsTo productionInv inputDomain effortDomain)
    (hinverse : Set.RightInvOn productionInv production inputDomain)
    (hweight_nonneg : ∀ᵐ agent ∂μ, 0 ≤ typeWeight agent)
    (heffective_maps :
      ∀ᵐ agent ∂μ,
        Set.MapsTo (effectiveInput agent)
          (Set.Icc (measurableUtility lo) (measurableUtility hi)) inputDomain)
    (heffective_convex :
      ∀ᵐ agent ∂μ,
        ConvexOn ℝ
          (Set.Icc (measurableUtility lo) (measurableUtility hi))
          (effectiveInput agent))
    (heffective_mono :
      ∀ᵐ agent ∂μ,
        MonotoneOn (effectiveInput agent)
          (Set.Icc (measurableUtility lo) (measurableUtility hi)))
    (hintegrable :
      ∀ target ∈ Set.Icc (measurableUtility lo) (measurableUtility hi),
        Integrable
          (fun agent =>
            typeWeight agent *
              production
                (budget - productionInv (effectiveInput agent target))) μ)
    (hfrontier_deriv :
      HasDerivAt
        (AppliedModelingLib.aggregateCrowdOutUtility
          μ typeWeight production budget
          (fun agent target => productionInv (effectiveInput agent target)))
        frontierDerivative (measurableUtility c))
    (hfrontier_decreasing : frontierDerivative < 0) :
    ∃ beta : ℝ,
      0 < beta ∧ beta < 1 ∧
      MaximizesOnInterval
        (weightedPrivateUtility beta measurableUtility unmeasurableUtility)
        c lo hi := by
  have heffort_shape :
      ∀ᵐ agent ∂μ,
        ConvexOn ℝ
            (Set.Icc (measurableUtility lo) (measurableUtility hi))
            (fun target => productionInv (effectiveInput agent target)) ∧
          MonotoneOn
            (fun target => productionInv (effectiveInput agent target))
            (Set.Icc (measurableUtility lo) (measurableUtility hi)) := by
    filter_upwards [heffective_maps, heffective_convex, heffective_mono] with
      agent hmaps hconvex hmono
    exact AppliedModelingLib.rightInverseOn_comp_convexOn_and_monotoneOn
      heffortDomain_convex hinputDomain_convex
      (hproduction_concave.subset (Set.subset_univ effortDomain)
        heffortDomain_convex)
      hproduction_strictMono hinverse_maps hinverse hmaps hconvex hmono
  have heffort_convex :
      ∀ᵐ agent ∂μ,
        ConvexOn ℝ
          (Set.Icc (measurableUtility lo) (measurableUtility hi))
          (fun target => productionInv (effectiveInput agent target)) :=
    heffort_shape.mono fun _ hshape => hshape.1
  have heffort_mono :
      ∀ᵐ agent ∂μ,
        MonotoneOn
          (fun target => productionInv (effectiveInput agent target))
          (Set.Icc (measurableUtility lo) (measurableUtility hi)) :=
    heffort_shape.mono fun _ hshape => hshape.2
  exact
    exists_beta_weightedPrivateUtility_maximizesOnInterval_of_convex_effort_response
      μ typeWeight production budget
      (fun agent target => productionInv (effectiveInput agent target))
      hlo hhi hmeasurable_mono hunmeasurable_eq hproduction_concave
      hproduction_mono hweight_nonneg heffort_convex heffort_mono
      hintegrable hfrontier_deriv hfrontier_decreasing

/--
Elasticity-level completion of Proposition B.2.  For every normalized admitted
type, write the effective measurable-score requirement as `m / F_s(m)`, where
`m` is common measurable output and `F_s` is that type's skill multiplier.
The dimensionless conditions

```text
η_s = m F_s' / F_s ≤ 1,
η_s^2 - η_s - m η_s' ≥ 0
```

make the effective input nondecreasing and convex.  Together with the
paper's concave increasing production technology, this is sufficient for the
global weighted-private-utility conclusion.  It is a primitive shape condition:
the multiplier `F_s` is obtained by composing the source skill quantile with
the induced admitted-tail cutoff path.
-/
theorem exists_beta_weightedPrivateUtility_maximizesOnInterval_of_effectiveInput_elasticity
    {Agent : Type*} [MeasurableSpace Agent]
    (μ : Measure Agent)
    (typeWeight : Agent → ℝ)
    (production productionInv : ℝ → ℝ)
    (budget : ℝ)
    (effectiveInput skill elasticity elasticityDeriv : Agent → ℝ → ℝ)
    (effortDomain inputDomain : Set ℝ)
    {measurableUtility unmeasurableUtility : ℝ → ℝ}
    {lo c hi frontierDerivative : ℝ}
    (hlo : lo ≤ c)
    (hhi : c ≤ hi)
    (hmeasurable_mono :
      MonotoneOn measurableUtility (Set.Icc lo hi))
    (hmeasurable_lo_pos : 0 < measurableUtility lo)
    (hunmeasurable_eq :
      ∀ x ∈ Set.Icc lo hi,
        unmeasurableUtility x =
          AppliedModelingLib.aggregateCrowdOutUtility
            μ typeWeight production budget
            (fun agent target => productionInv (effectiveInput agent target))
            (measurableUtility x))
    (heffortDomain_convex : Convex ℝ effortDomain)
    (hinputDomain_convex : Convex ℝ inputDomain)
    (hproduction_concave : ConcaveOn ℝ Set.univ production)
    (hproduction_mono : Monotone production)
    (hproduction_strictMono : StrictMonoOn production effortDomain)
    (hinverse_maps : Set.MapsTo productionInv inputDomain effortDomain)
    (hinverse : Set.RightInvOn productionInv production inputDomain)
    (hweight_nonneg : ∀ᵐ agent ∂μ, 0 ≤ typeWeight agent)
    (heffective_maps :
      ∀ᵐ agent ∂μ,
        Set.MapsTo (effectiveInput agent)
          (Set.Icc (measurableUtility lo) (measurableUtility hi)) inputDomain)
    (heffectiveInput_def :
      ∀ᵐ agent ∂μ,
        effectiveInput agent = fun target => target / skill agent target)
    (hskill_pos :
      ∀ᵐ agent ∂μ,
        ∀ target ∈ Set.Icc (measurableUtility lo) (measurableUtility hi),
          0 < skill agent target)
    (hskill_deriv :
      ∀ᵐ agent ∂μ,
        ∀ target ∈ Set.Icc (measurableUtility lo) (measurableUtility hi),
          HasDerivAt (skill agent)
            (elasticity agent target * skill agent target / target) target)
    (helasticity_deriv :
      ∀ᵐ agent ∂μ,
        ∀ target ∈ Set.Icc (measurableUtility lo) (measurableUtility hi),
          HasDerivAt (elasticity agent) (elasticityDeriv agent target) target)
    (helasticity_le_one :
      ∀ᵐ agent ∂μ,
        ∀ target ∈ Set.Icc (measurableUtility lo) (measurableUtility hi),
          elasticity agent target ≤ 1)
    (hcurvature :
      ∀ᵐ agent ∂μ,
        ∀ target ∈ Set.Icc (measurableUtility lo) (measurableUtility hi),
          0 ≤ elasticity agent target ^ 2 - elasticity agent target -
            target * elasticityDeriv agent target)
    (hintegrable :
      ∀ target ∈ Set.Icc (measurableUtility lo) (measurableUtility hi),
        Integrable
          (fun agent =>
            typeWeight agent *
              production
                (budget - productionInv (effectiveInput agent target))) μ)
    (hfrontier_deriv :
      HasDerivAt
        (AppliedModelingLib.aggregateCrowdOutUtility
          μ typeWeight production budget
          (fun agent target => productionInv (effectiveInput agent target)))
        frontierDerivative (measurableUtility c))
    (hfrontier_decreasing : frontierDerivative < 0) :
    ∃ beta : ℝ,
      0 < beta ∧ beta < 1 ∧
      MaximizesOnInterval
        (weightedPrivateUtility beta measurableUtility unmeasurableUtility)
        c lo hi := by
  have heffective_shape :
      ∀ᵐ agent ∂μ,
        ConvexOn ℝ
          (Set.Icc (measurableUtility lo) (measurableUtility hi))
          (effectiveInput agent) ∧
        MonotoneOn (effectiveInput agent)
          (Set.Icc (measurableUtility lo) (measurableUtility hi)) := by
    filter_upwards [heffectiveInput_def, hskill_pos, hskill_deriv,
      helasticity_deriv, helasticity_le_one, hcurvature] with
        agent hinput hpositive hskill hderiv hle hcurvature
    simpa only [hinput] using
      (AppliedModelingLib.effectiveInput_convexOn_and_monotoneOn_of_elasticity
        (lo := measurableUtility lo) (hi := measurableUtility hi)
        hmeasurable_lo_pos hpositive hskill hderiv hle hcurvature)
  have heffective_convex :
      ∀ᵐ agent ∂μ,
        ConvexOn ℝ
          (Set.Icc (measurableUtility lo) (measurableUtility hi))
          (effectiveInput agent) :=
    heffective_shape.mono fun _ hshape => hshape.1
  have heffective_mono :
      ∀ᵐ agent ∂μ,
        MonotoneOn (effectiveInput agent)
          (Set.Icc (measurableUtility lo) (measurableUtility hi)) :=
    heffective_shape.mono fun _ hshape => hshape.2
  exact
    exists_beta_weightedPrivateUtility_maximizesOnInterval_of_convex_effectiveInput
      μ typeWeight production productionInv budget effectiveInput
      effortDomain inputDomain hlo hhi hmeasurable_mono hunmeasurable_eq
      heffortDomain_convex hinputDomain_convex hproduction_concave
      hproduction_mono hproduction_strictMono hinverse_maps hinverse
      hweight_nonneg heffective_maps heffective_convex heffective_mono
      hintegrable hfrontier_deriv hfrontier_decreasing

/--
Square-root-technology completion of Proposition B.2 through the multiplier
elasticity.  If the score technology is `e ↦ sqrt e`, then the effort required
for common measurable output `m` at multiplier `F_s(m)` is `(m / F_s(m))^2`.
It is enough that the multiplier elasticity `η_s=mF_s'/F_s` stay at most
one half and weakly decrease.  This is weaker than requiring the intermediate
effective-input path `m / F_s(m)` itself to be convex: diminishing returns in
the production technology supply the remaining curvature.
-/
theorem exists_beta_weightedPrivateUtility_maximizesOnInterval_of_squared_effectiveInput_elasticity
    {Agent : Type*} [MeasurableSpace Agent]
    (μ : Measure Agent)
    (typeWeight : Agent → ℝ)
    (production : ℝ → ℝ)
    (budget : ℝ)
    (effortResponse skill elasticity elasticityDeriv : Agent → ℝ → ℝ)
    {measurableUtility unmeasurableUtility : ℝ → ℝ}
    {lo c hi frontierDerivative : ℝ}
    (hlo : lo ≤ c)
    (hhi : c ≤ hi)
    (hmeasurable_mono :
      MonotoneOn measurableUtility (Set.Icc lo hi))
    (hmeasurable_lo_pos : 0 < measurableUtility lo)
    (hunmeasurable_eq :
      ∀ x ∈ Set.Icc lo hi,
        unmeasurableUtility x =
          AppliedModelingLib.aggregateCrowdOutUtility
            μ typeWeight production budget effortResponse
            (measurableUtility x))
    (hproduction_concave : ConcaveOn ℝ Set.univ production)
    (hproduction_mono : Monotone production)
    (hweight_nonneg : ∀ᵐ agent ∂μ, 0 ≤ typeWeight agent)
    (heffortResponse_def :
      ∀ᵐ agent ∂μ,
        effortResponse agent = fun target => (target / skill agent target) ^ 2)
    (hskill_pos :
      ∀ᵐ agent ∂μ,
        ∀ target ∈ Set.Icc (measurableUtility lo) (measurableUtility hi),
          0 < skill agent target)
    (hskill_deriv :
      ∀ᵐ agent ∂μ,
        ∀ target ∈ Set.Icc (measurableUtility lo) (measurableUtility hi),
          HasDerivAt (skill agent)
            (elasticity agent target * skill agent target / target) target)
    (helasticity_deriv :
      ∀ᵐ agent ∂μ,
        ∀ target ∈ Set.Icc (measurableUtility lo) (measurableUtility hi),
          HasDerivAt (elasticity agent) (elasticityDeriv agent target) target)
    (helasticity_le_half :
      ∀ᵐ agent ∂μ,
        ∀ target ∈ Set.Icc (measurableUtility lo) (measurableUtility hi),
          elasticity agent target ≤ 1 / 2)
    (helasticityDeriv_nonpos :
      ∀ᵐ agent ∂μ,
        ∀ target ∈ Set.Icc (measurableUtility lo) (measurableUtility hi),
          elasticityDeriv agent target ≤ 0)
    (hintegrable :
      ∀ target ∈ Set.Icc (measurableUtility lo) (measurableUtility hi),
        Integrable
          (fun agent =>
            typeWeight agent *
              production (budget - effortResponse agent target)) μ)
    (hfrontier_deriv :
      HasDerivAt
        (AppliedModelingLib.aggregateCrowdOutUtility
          μ typeWeight production budget effortResponse)
        frontierDerivative (measurableUtility c))
    (hfrontier_decreasing : frontierDerivative < 0) :
    ∃ beta : ℝ,
      0 < beta ∧ beta < 1 ∧
      MaximizesOnInterval
        (weightedPrivateUtility beta measurableUtility unmeasurableUtility)
        c lo hi := by
  have heffort_shape :
      ∀ᵐ agent ∂μ,
        ConvexOn ℝ
          (Set.Icc (measurableUtility lo) (measurableUtility hi))
          (effortResponse agent) ∧
        MonotoneOn (effortResponse agent)
          (Set.Icc (measurableUtility lo) (measurableUtility hi)) := by
    filter_upwards [heffortResponse_def, hskill_pos, hskill_deriv,
      helasticity_deriv, helasticity_le_half, helasticityDeriv_nonpos] with
        agent heffort hpositive hskill hderiv hhalf hderiv_nonpos
    simpa only [heffort] using
      (AppliedModelingLib.squaredEffectiveInput_convexOn_and_monotoneOn_of_elasticity
        (lo := measurableUtility lo) (hi := measurableUtility hi)
        hmeasurable_lo_pos hpositive hskill hderiv hhalf hderiv_nonpos)
  have heffort_convex :
      ∀ᵐ agent ∂μ,
        ConvexOn ℝ
          (Set.Icc (measurableUtility lo) (measurableUtility hi))
          (effortResponse agent) :=
    heffort_shape.mono fun _ hshape => hshape.1
  have heffort_mono :
      ∀ᵐ agent ∂μ,
        MonotoneOn (effortResponse agent)
          (Set.Icc (measurableUtility lo) (measurableUtility hi)) :=
    heffort_shape.mono fun _ hshape => hshape.2
  exact
    exists_beta_weightedPrivateUtility_maximizesOnInterval_of_convex_effort_response
      μ typeWeight production budget effortResponse
      hlo hhi hmeasurable_mono hunmeasurable_eq hproduction_concave
      hproduction_mono hweight_nonneg heffort_convex heffort_mono
      hintegrable hfrontier_deriv hfrontier_decreasing

/--
Power/exponential multiplier completion of Proposition B.2 at the cutoff-path
level.  This is the source-facing specialization for
`g(e)=sqrt(e)`, `p(e)=e^2`, and a log-affine measurable-skill quantile.  Its
only quantitative restriction is that the quantile log-slope not exceed the
cutoff-curvature parameter.  In the literal power pair that parameter is
`1 / 4`.

The theorem leaves the cutoff path abstract but requires its exact derivative;
deriving that inverse-cutoff formula and the usual feasibility conditions from
the source primitives is a separate, explicit source-to-model obligation.
-/
theorem exists_beta_weightedPrivateUtility_maximizesOnInterval_of_exponentialTailMultiplier
    {Agent : Type*} [MeasurableSpace Agent]
    (μ : Measure Agent)
    (typeWeight : Agent → ℝ)
    (production : ℝ → ℝ)
    (budget scale logSlope cutoffCurvature : ℝ)
    (effortResponse : Agent → ℝ → ℝ)
    (tailPosition : Agent → ℝ)
    (cutoff : ℝ → ℝ)
    {measurableUtility unmeasurableUtility : ℝ → ℝ}
    {lo c hi frontierDerivative : ℝ}
    (hlo : lo ≤ c)
    (hhi : c ≤ hi)
    (hmeasurable_mono :
      MonotoneOn measurableUtility (Set.Icc lo hi))
    (hmeasurable_lo_pos : 0 < measurableUtility lo)
    (hunmeasurable_eq :
      ∀ x ∈ Set.Icc lo hi,
        unmeasurableUtility x =
          AppliedModelingLib.aggregateCrowdOutUtility
            μ typeWeight production budget effortResponse
            (measurableUtility x))
    (hproduction_concave : ConcaveOn ℝ Set.univ production)
    (hproduction_mono : Monotone production)
    (hweight_nonneg : ∀ᵐ agent ∂μ, 0 ≤ typeWeight agent)
    (hscale : 0 < scale)
    (hlogSlope : 0 < logSlope)
    (hcurvature : logSlope ≤ cutoffCurvature)
    (htailPosition : ∀ᵐ agent ∂μ, tailPosition agent ∈ Set.Icc 0 1)
    (hcutoff_bounds :
      ∀ output ∈ Set.Icc (measurableUtility lo) (measurableUtility hi),
        cutoff output ∈ Set.Ico 0 1)
    (hcutoff_deriv :
      ∀ output ∈ Set.Icc (measurableUtility lo) (measurableUtility hi),
        HasDerivAt cutoff
          (1 / (output *
            (logSlope + cutoffCurvature / (1 - cutoff output)))) output)
    (heffortResponse_def :
      ∀ᵐ agent ∂μ,
        effortResponse agent = fun output =>
          (output /
            AppliedModelingLib.exponentialTailMultiplier
              scale logSlope (tailPosition agent) cutoff output) ^ 2)
    (hintegrable :
      ∀ output ∈ Set.Icc (measurableUtility lo) (measurableUtility hi),
        Integrable
          (fun agent =>
            typeWeight agent *
              production (budget - effortResponse agent output)) μ)
    (hfrontier_deriv :
      HasDerivAt
        (AppliedModelingLib.aggregateCrowdOutUtility
          μ typeWeight production budget effortResponse)
        frontierDerivative (measurableUtility c))
    (hfrontier_decreasing : frontierDerivative < 0) :
    ∃ beta : ℝ,
      0 < beta ∧ beta < 1 ∧
      MaximizesOnInterval
        (weightedPrivateUtility beta measurableUtility unmeasurableUtility)
        c lo hi := by
  have hmultiplier_conditions :
      ∀ᵐ agent ∂μ,
        ∀ output ∈ Set.Icc (measurableUtility lo) (measurableUtility hi),
          0 < AppliedModelingLib.exponentialTailMultiplier
              scale logSlope (tailPosition agent) cutoff output ∧
            HasDerivAt
              (AppliedModelingLib.exponentialTailMultiplier
                scale logSlope (tailPosition agent) cutoff)
              (AppliedModelingLib.exponentialTailElasticity
                logSlope cutoffCurvature (tailPosition agent) cutoff output *
                  AppliedModelingLib.exponentialTailMultiplier
                    scale logSlope (tailPosition agent) cutoff output / output)
              output ∧
            HasDerivAt
              (AppliedModelingLib.exponentialTailElasticity
                logSlope cutoffCurvature (tailPosition agent) cutoff)
              (AppliedModelingLib.exponentialTailElasticityDeriv
                logSlope cutoffCurvature (tailPosition agent) cutoff output)
              output ∧
            AppliedModelingLib.exponentialTailElasticity
              logSlope cutoffCurvature (tailPosition agent) cutoff output ≤ 1 / 2 ∧
            AppliedModelingLib.exponentialTailElasticityDeriv
              logSlope cutoffCurvature (tailPosition agent) cutoff output ≤ 0 := by
    filter_upwards [htailPosition] with agent htail
    intro output houtput
    rcases hcutoff_bounds output houtput with ⟨hcutoff_nonneg, hcutoff_lt_one⟩
    exact AppliedModelingLib.exponentialTailMultiplier_elasticity_conditions
      hscale hlogSlope hcurvature htail.1 htail.2
      (lt_of_lt_of_le hmeasurable_lo_pos houtput.1)
      hcutoff_nonneg hcutoff_lt_one (hcutoff_deriv output houtput)
  have hskill_pos :
      ∀ᵐ agent ∂μ,
        ∀ output ∈ Set.Icc (measurableUtility lo) (measurableUtility hi),
          0 < AppliedModelingLib.exponentialTailMultiplier
              scale logSlope (tailPosition agent) cutoff output :=
    hmultiplier_conditions.mono fun _ hconditions output houtput =>
      (hconditions output houtput).1
  have hskill_deriv :
      ∀ᵐ agent ∂μ,
        ∀ output ∈ Set.Icc (measurableUtility lo) (measurableUtility hi),
          HasDerivAt
            (AppliedModelingLib.exponentialTailMultiplier
              scale logSlope (tailPosition agent) cutoff)
            (AppliedModelingLib.exponentialTailElasticity
              logSlope cutoffCurvature (tailPosition agent) cutoff output *
                AppliedModelingLib.exponentialTailMultiplier
                  scale logSlope (tailPosition agent) cutoff output / output)
            output :=
    hmultiplier_conditions.mono fun _ hconditions output houtput =>
      (hconditions output houtput).2.1
  have helasticity_deriv :
      ∀ᵐ agent ∂μ,
        ∀ output ∈ Set.Icc (measurableUtility lo) (measurableUtility hi),
          HasDerivAt
            (AppliedModelingLib.exponentialTailElasticity
              logSlope cutoffCurvature (tailPosition agent) cutoff)
            (AppliedModelingLib.exponentialTailElasticityDeriv
              logSlope cutoffCurvature (tailPosition agent) cutoff output)
            output :=
    hmultiplier_conditions.mono fun _ hconditions output houtput =>
      (hconditions output houtput).2.2.1
  have helasticity_le_half :
      ∀ᵐ agent ∂μ,
        ∀ output ∈ Set.Icc (measurableUtility lo) (measurableUtility hi),
          AppliedModelingLib.exponentialTailElasticity
            logSlope cutoffCurvature (tailPosition agent) cutoff output ≤ 1 / 2 :=
    hmultiplier_conditions.mono fun _ hconditions output houtput =>
      (hconditions output houtput).2.2.2.1
  have helasticityDeriv_nonpos :
      ∀ᵐ agent ∂μ,
        ∀ output ∈ Set.Icc (measurableUtility lo) (measurableUtility hi),
          AppliedModelingLib.exponentialTailElasticityDeriv
            logSlope cutoffCurvature (tailPosition agent) cutoff output ≤ 0 :=
    hmultiplier_conditions.mono fun _ hconditions output houtput =>
      (hconditions output houtput).2.2.2.2
  exact
    exists_beta_weightedPrivateUtility_maximizesOnInterval_of_squared_effectiveInput_elasticity
      μ typeWeight production budget effortResponse
      (fun agent =>
        AppliedModelingLib.exponentialTailMultiplier
          scale logSlope (tailPosition agent) cutoff)
      (fun agent =>
        AppliedModelingLib.exponentialTailElasticity
          logSlope cutoffCurvature (tailPosition agent) cutoff)
      (fun agent =>
        AppliedModelingLib.exponentialTailElasticityDeriv
          logSlope cutoffCurvature (tailPosition agent) cutoff)
      hlo hhi hmeasurable_mono hmeasurable_lo_pos hunmeasurable_eq
      hproduction_concave hproduction_mono hweight_nonneg heffortResponse_def
      hskill_pos hskill_deriv helasticity_deriv helasticity_le_half
      helasticityDeriv_nonpos hintegrable hfrontier_deriv hfrontier_decreasing

/--
Source-output version of the power/exponential multiplier repair.  It replaces
the cutoff-derivative premise by the concrete common-output path
`K exp(delta*c) (1-c)^(-kappa)` and a continuous local inverse.  Thus the
cutoff derivative used in the elasticity argument is derived rather than
postulated.
-/
theorem exists_beta_weightedPrivateUtility_maximizesOnInterval_of_powerExponentialCutoff
    {Agent : Type*} [MeasurableSpace Agent]
    (μ : Measure Agent)
    (typeWeight : Agent → ℝ)
    (production : ℝ → ℝ)
    (budget multiplierScale outputScale logSlope cutoffCurvature : ℝ)
    (effortResponse : Agent → ℝ → ℝ)
    (tailPosition : Agent → ℝ)
    (cutoff : ℝ → ℝ)
    {measurableUtility unmeasurableUtility : ℝ → ℝ}
    {lo c hi frontierDerivative : ℝ}
    (hlo : lo ≤ c)
    (hhi : c ≤ hi)
    (hmeasurable_mono :
      MonotoneOn measurableUtility (Set.Icc lo hi))
    (hmeasurable_lo_pos : 0 < measurableUtility lo)
    (hunmeasurable_eq :
      ∀ x ∈ Set.Icc lo hi,
        unmeasurableUtility x =
          AppliedModelingLib.aggregateCrowdOutUtility
            μ typeWeight production budget effortResponse
            (measurableUtility x))
    (hproduction_concave : ConcaveOn ℝ Set.univ production)
    (hproduction_mono : Monotone production)
    (hweight_nonneg : ∀ᵐ agent ∂μ, 0 ≤ typeWeight agent)
    (hmultiplierScale : 0 < multiplierScale)
    (hlogSlope : 0 < logSlope)
    (hcurvature : logSlope ≤ cutoffCurvature)
    (htailPosition : ∀ᵐ agent ∂μ, tailPosition agent ∈ Set.Icc 0 1)
    (hcutoff_bounds :
      ∀ output ∈ Set.Icc (measurableUtility lo) (measurableUtility hi),
        cutoff output ∈ Set.Ico 0 1)
    (hcutoff_continuous :
      ∀ output ∈ Set.Icc (measurableUtility lo) (measurableUtility hi),
        ContinuousAt cutoff output)
    (hcutoff_local_right_inverse :
      ∀ output ∈ Set.Icc (measurableUtility lo) (measurableUtility hi),
        ∀ᶠ nearbyOutput in nhds output,
          AppliedModelingLib.powerExponentialOutput
            outputScale logSlope cutoffCurvature (cutoff nearbyOutput) = nearbyOutput)
    (heffortResponse_def :
      ∀ᵐ agent ∂μ,
        effortResponse agent = fun output =>
          (output /
            AppliedModelingLib.exponentialTailMultiplier
              multiplierScale logSlope (tailPosition agent) cutoff output) ^ 2)
    (hintegrable :
      ∀ output ∈ Set.Icc (measurableUtility lo) (measurableUtility hi),
        Integrable
          (fun agent =>
            typeWeight agent *
              production (budget - effortResponse agent output)) μ)
    (hfrontier_deriv :
      HasDerivAt
        (AppliedModelingLib.aggregateCrowdOutUtility
          μ typeWeight production budget effortResponse)
        frontierDerivative (measurableUtility c))
    (hfrontier_decreasing : frontierDerivative < 0) :
    ∃ beta : ℝ,
      0 < beta ∧ beta < 1 ∧
      MaximizesOnInterval
        (weightedPrivateUtility beta measurableUtility unmeasurableUtility)
        c lo hi := by
  apply
    exists_beta_weightedPrivateUtility_maximizesOnInterval_of_exponentialTailMultiplier
      μ typeWeight production budget multiplierScale logSlope cutoffCurvature
      effortResponse tailPosition cutoff
      hlo hhi hmeasurable_mono hmeasurable_lo_pos hunmeasurable_eq
      hproduction_concave hproduction_mono hweight_nonneg hmultiplierScale
      hlogSlope hcurvature htailPosition hcutoff_bounds
  · intro output houtput
    rcases hcutoff_bounds output houtput with ⟨_, hcutoff_lt_one⟩
    exact AppliedModelingLib.powerExponentialOutput_localInverse_hasDerivAt
      hlogSlope (hlogSlope.trans_le hcurvature)
      (lt_of_lt_of_le hmeasurable_lo_pos houtput.1) hcutoff_lt_one
      (hcutoff_continuous output houtput)
      (hcutoff_local_right_inverse output houtput)
  · exact heffortResponse_def
  · exact hintegrable
  · exact hfrontier_deriv
  · exact hfrontier_decreasing

/--
The weighted first-order expression alone is not enough to justify the source
proof's global-maximizer conclusion.  This concrete monotone-tradeoff-shaped
objective has the balanced derivative expression at `c = 1/2`, but that cutoff
does not maximize the weighted utility on `[0,1]`.
-/
theorem weightedUtilityDerivative_zero_not_sufficient_for_maximum :
    ∃ beta c : ℝ, ∃ measurableUtility unmeasurableUtility : ℝ → ℝ,
      0 < beta ∧ beta < 1 ∧
      weightedUtilityDerivative beta 1 (-1) = 0 ∧
      ¬ MaximizesOnInterval
        (weightedPrivateUtility beta measurableUtility unmeasurableUtility)
        c 0 1 := by
  refine
    ⟨(1 : ℝ) / 2, (1 : ℝ) / 2, (fun x : ℝ => x),
      (fun x : ℝ => -x + (x - (1 : ℝ) / 2) ^ 3), ?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · norm_num [weightedUtilityDerivative]
  · intro hmax
    have hle := hmax.2.2 (1 : ℝ) (by norm_num) (by norm_num)
    norm_num [weightedPrivateUtility] at hle

/--
Calculus-level version of the preceding source-gap check.  Even when the
component derivatives exist with the signs used in the printed proof and the
chosen weighted utility is stationary at the cutoff, that cutoff need not be a
global maximizer on the two-level interval.
-/
theorem weightedPrivateUtility_stationary_not_sufficient_for_maximum :
    ∃ beta c : ℝ, ∃ measurableUtility unmeasurableUtility : ℝ → ℝ,
      0 < beta ∧ beta < 1 ∧
      HasDerivAt measurableUtility 1 c ∧
      HasDerivAt unmeasurableUtility (-1) c ∧
      HasDerivAt
        (weightedPrivateUtility beta measurableUtility unmeasurableUtility)
        0 c ∧
      ¬ MaximizesOnInterval
        (weightedPrivateUtility beta measurableUtility unmeasurableUtility)
        c 0 1 := by
  let beta : ℝ := (1 : ℝ) / 2
  let c : ℝ := (1 : ℝ) / 2
  let measurableUtility : ℝ → ℝ := fun x => x
  let unmeasurableUtility : ℝ → ℝ := fun x => -x + (x - (1 : ℝ) / 2) ^ 3
  refine ⟨beta, c, measurableUtility, unmeasurableUtility, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [beta]
  · norm_num [beta]
  · simpa [measurableUtility, c] using hasDerivAt_id ((1 : ℝ) / 2)
  · have hneg : HasDerivAt (fun x : ℝ => -x) (-1) ((1 : ℝ) / 2) := by
      simpa using (hasDerivAt_id ((1 : ℝ) / 2)).neg
    have hsub : HasDerivAt (fun x : ℝ => x - (1 : ℝ) / 2) 1 ((1 : ℝ) / 2) := by
      simpa using (hasDerivAt_id ((1 : ℝ) / 2)).sub_const ((1 : ℝ) / 2)
    have hpow := hsub.pow 3
    have hcubic : HasDerivAt (fun x : ℝ => (x - (1 : ℝ) / 2) ^ 3) 0
        ((1 : ℝ) / 2) := by
      simpa using hpow
    simpa [unmeasurableUtility, c] using hneg.add hcubic
  · have hM : HasDerivAt measurableUtility 1 c := by
      simpa [measurableUtility, c] using hasDerivAt_id ((1 : ℝ) / 2)
    have hU : HasDerivAt unmeasurableUtility (-1) c := by
      have hneg : HasDerivAt (fun x : ℝ => -x) (-1) ((1 : ℝ) / 2) := by
        simpa using (hasDerivAt_id ((1 : ℝ) / 2)).neg
      have hsub : HasDerivAt (fun x : ℝ => x - (1 : ℝ) / 2) 1
          ((1 : ℝ) / 2) := by
        simpa using (hasDerivAt_id ((1 : ℝ) / 2)).sub_const ((1 : ℝ) / 2)
      have hpow := hsub.pow 3
      have hcubic : HasDerivAt (fun x : ℝ => (x - (1 : ℝ) / 2) ^ 3) 0
          ((1 : ℝ) / 2) := by
        simpa using hpow
      simpa [unmeasurableUtility, c] using hneg.add hcubic
    have hderiv :
        HasDerivAt
          (weightedPrivateUtility beta measurableUtility unmeasurableUtility)
          (weightedUtilityDerivative beta 1 (-1)) c := by
      simpa [weightedPrivateUtility, weightedUtilityDerivative] using
        (hM.const_mul beta).add (hU.const_mul (1 - beta))
    have hzero : weightedUtilityDerivative beta 1 (-1) = 0 := by
      norm_num [weightedUtilityDerivative, beta]
    simpa [hzero] using hderiv
  · intro hmax
    have hle := hmax.2.2 (1 : ℝ) (by norm_num [c]) (by norm_num [c])
    norm_num [weightedPrivateUtility, measurableUtility, unmeasurableUtility,
      beta, c] at hle

/--
General one-dimensional shape lemma for the weighted-utility endpoint: if a
continuous objective has nonnegative derivative to the left of an interior
cutoff and nonpositive derivative to the right, then the cutoff maximizes the
objective on the interval.
-/
theorem maximizesOnInterval_of_derivative_signs
    {W W' : ℝ → ℝ} {lo c hi : ℝ}
    (hlo : lo ≤ c)
    (hhi : c ≤ hi)
    (hcont_left : ContinuousOn W (Set.Icc lo c))
    (hcont_right : ContinuousOn W (Set.Icc c hi))
    (hderiv_left :
      ∀ x ∈ Set.Ioo lo c, HasDerivWithinAt W (W' x) (Set.Ioo lo c) x)
    (hderiv_right :
      ∀ x ∈ Set.Ioo c hi, HasDerivWithinAt W (W' x) (Set.Ioo c hi) x)
    (hleft_nonneg : ∀ x ∈ Set.Ioo lo c, 0 ≤ W' x)
    (hright_nonpos : ∀ x ∈ Set.Ioo c hi, W' x ≤ 0) :
    MaximizesOnInterval W c lo hi := by
  have hleft_mono : MonotoneOn W (Set.Icc lo c) := by
    exact monotoneOn_of_hasDerivWithinAt_nonneg
      (D := Set.Icc lo c) (f := W) (f' := W')
      (convex_Icc lo c) hcont_left
      (by
        intro x hx
        simpa [interior_Icc] using hderiv_left x (by simpa [interior_Icc] using hx))
      (by
        intro x hx
        exact hleft_nonneg x (by simpa [interior_Icc] using hx))
  have hright_anti : AntitoneOn W (Set.Icc c hi) := by
    exact antitoneOn_of_hasDerivWithinAt_nonpos
      (D := Set.Icc c hi) (f := W) (f' := W')
      (convex_Icc c hi) hcont_right
      (by
        intro x hx
        simpa [interior_Icc] using hderiv_right x (by simpa [interior_Icc] using hx))
      (by
        intro x hx
        exact hright_nonpos x (by simpa [interior_Icc] using hx))
  refine ⟨hlo, hhi, ?_⟩
  intro y hylo hyhi
  by_cases hyc : y ≤ c
  · exact hleft_mono ⟨hylo, hyc⟩ ⟨hlo, le_rfl⟩ hyc
  · have hcy : c ≤ y := le_of_lt (lt_of_not_ge hyc)
    exact hright_anti ⟨le_rfl, hhi⟩ ⟨hcy, hyhi⟩ hcy

/--
Weighted-utility version of the one-dimensional shape lemma.  Once the chosen
weight has been fixed, if the weighted private utility has nonnegative
derivative to the left of an interior cutoff and nonpositive derivative to the
right, then that cutoff is a global maximizer on the two-level interval.
-/
theorem weightedPrivateUtility_maximizesOnInterval_of_derivative_signs
    {measurableUtility unmeasurableUtility W' : ℝ → ℝ}
    {beta lo c hi : ℝ}
    (hlo : lo ≤ c)
    (hhi : c ≤ hi)
    (hcont_left :
      ContinuousOn
        (weightedPrivateUtility beta measurableUtility unmeasurableUtility)
        (Set.Icc lo c))
    (hcont_right :
      ContinuousOn
        (weightedPrivateUtility beta measurableUtility unmeasurableUtility)
        (Set.Icc c hi))
    (hderiv_left :
      ∀ x ∈ Set.Ioo lo c,
        HasDerivWithinAt
          (weightedPrivateUtility beta measurableUtility unmeasurableUtility)
          (W' x) (Set.Ioo lo c) x)
    (hderiv_right :
      ∀ x ∈ Set.Ioo c hi,
        HasDerivWithinAt
          (weightedPrivateUtility beta measurableUtility unmeasurableUtility)
          (W' x) (Set.Ioo c hi) x)
    (hleft_nonneg : ∀ x ∈ Set.Ioo lo c, 0 ≤ W' x)
    (hright_nonpos : ∀ x ∈ Set.Ioo c hi, W' x ≤ 0) :
    MaximizesOnInterval
      (weightedPrivateUtility beta measurableUtility unmeasurableUtility)
      c lo hi :=
  maximizesOnInterval_of_derivative_signs hlo hhi hcont_left hcont_right
    hderiv_left hderiv_right hleft_nonneg hright_nonpos

/--
Derivative-shape support for Proposition `prop:2levels-fixedcap`.  If the
component derivatives are ordered so that both components are weakly larger to
the left of the target cutoff and weakly smaller to the right, then the beta
that balances the derivative at the target gives the weighted derivative the
right sign on each side.
-/
theorem weightedUtilityDerivative_signs_of_component_derivative_order
    {beta lo c hi : ℝ} {dMeasurable dUnmeasurable : ℝ → ℝ}
    (hbeta_nonneg : 0 ≤ beta)
    (hone_minus_nonneg : 0 ≤ 1 - beta)
    (hzero :
      weightedUtilityDerivative beta (dMeasurable c) (dUnmeasurable c) = 0)
    (hleftM :
      ∀ x ∈ Set.Ioo lo c, dMeasurable c ≤ dMeasurable x)
    (hleftU :
      ∀ x ∈ Set.Ioo lo c, dUnmeasurable c ≤ dUnmeasurable x)
    (hrightM :
      ∀ x ∈ Set.Ioo c hi, dMeasurable x ≤ dMeasurable c)
    (hrightU :
      ∀ x ∈ Set.Ioo c hi, dUnmeasurable x ≤ dUnmeasurable c) :
    (∀ x ∈ Set.Ioo lo c,
      0 ≤ weightedUtilityDerivative beta (dMeasurable x) (dUnmeasurable x))
    ∧
    (∀ x ∈ Set.Ioo c hi,
      weightedUtilityDerivative beta (dMeasurable x) (dUnmeasurable x) ≤ 0) := by
  constructor
  · intro x hx
    have hM : 0 ≤ dMeasurable x - dMeasurable c := sub_nonneg.mpr (hleftM x hx)
    have hU : 0 ≤ dUnmeasurable x - dUnmeasurable c :=
      sub_nonneg.mpr (hleftU x hx)
    have hdelta :
        0 ≤
          beta * (dMeasurable x - dMeasurable c) +
            (1 - beta) * (dUnmeasurable x - dUnmeasurable c) :=
      add_nonneg (mul_nonneg hbeta_nonneg hM)
        (mul_nonneg hone_minus_nonneg hU)
    unfold weightedUtilityDerivative at hzero ⊢
    linarith
  · intro x hx
    have hM : dMeasurable x - dMeasurable c ≤ 0 := sub_nonpos.mpr (hrightM x hx)
    have hU : dUnmeasurable x - dUnmeasurable c ≤ 0 :=
      sub_nonpos.mpr (hrightU x hx)
    have hdelta :
        beta * (dMeasurable x - dMeasurable c) +
            (1 - beta) * (dUnmeasurable x - dUnmeasurable c) ≤ 0 :=
      add_nonpos (mul_nonpos_of_nonneg_of_nonpos hbeta_nonneg hM)
        (mul_nonpos_of_nonneg_of_nonpos hone_minus_nonneg hU)
    unfold weightedUtilityDerivative at hzero ⊢
    linarith

/--
Derivative-sign support for Proposition `prop:2levels-fixedcap` from a
marginal-tradeoff condition.  Write `M` for the measurable component and `U`
for the unmeasurable component.  After the source first-order weight balances
`β M'(c) + (1-β) U'(c) = 0`, the cutoff is a maximum whenever the marginal
rate `-U'/M'` is weakly increasing through the target cutoff.  The hypotheses
below are the cross-multiplied form of that condition, avoiding division by
derivatives.
-/
theorem exists_beta_weightedUtilityDerivative_signs_of_marginal_tradeoff_order
    {lo c hi : ℝ} {dMeasurable dUnmeasurable : ℝ → ℝ}
    (hM_target : 0 < dMeasurable c)
    (hU_target : dUnmeasurable c < 0)
    (hleft_trade :
      ∀ x ∈ Set.Ioo lo c,
        (-dUnmeasurable x) * dMeasurable c ≤
          (-dUnmeasurable c) * dMeasurable x)
    (hright_trade :
      ∀ x ∈ Set.Ioo c hi,
        (-dUnmeasurable c) * dMeasurable x ≤
          (-dUnmeasurable x) * dMeasurable c) :
    ∃ beta : ℝ,
      0 < beta ∧ beta < 1 ∧
      weightedUtilityDerivative beta (dMeasurable c) (dUnmeasurable c) = 0 ∧
      (∀ x ∈ Set.Ioo lo c,
        0 ≤ weightedUtilityDerivative beta (dMeasurable x) (dUnmeasurable x)) ∧
      (∀ x ∈ Set.Ioo c hi,
        weightedUtilityDerivative beta (dMeasurable x) (dUnmeasurable x) ≤ 0) := by
  let beta : ℝ := -dUnmeasurable c / (dMeasurable c - dUnmeasurable c)
  have hden_pos : 0 < dMeasurable c - dUnmeasurable c := by linarith
  have hden_ne : dMeasurable c - dUnmeasurable c ≠ 0 := ne_of_gt hden_pos
  refine ⟨beta, ?_, ?_, ?_, ?_, ?_⟩
  · exact div_pos (neg_pos.mpr hU_target) hden_pos
  · rw [div_lt_one hden_pos]
    linarith
  · unfold weightedUtilityDerivative beta
    field_simp [hden_ne]
    ring
  · intro x hx
    have htrade := hleft_trade x hx
    unfold weightedUtilityDerivative beta
    field_simp [hden_pos.ne']
    nlinarith
  · intro x hx
    have htrade := hright_trade x hx
    unfold weightedUtilityDerivative beta
    field_simp [hden_pos.ne']
    nlinarith

/--
Source-shaped completion route for Proposition `prop:2levels-fixedcap`.
The first-order beta is not enough by itself; with component derivative
profiles that are single-peaked around the desired cutoff, the same beta makes
the cutoff a global maximizer on the two-level interval.
-/
theorem exists_beta_weightedPrivateUtility_maximizesOnInterval_of_component_derivative_order
    {measurableUtility unmeasurableUtility dMeasurable dUnmeasurable : ℝ → ℝ}
    {lo c hi : ℝ}
    (hlo : lo ≤ c)
    (hhi : c ≤ hi)
    (hMcont_left : ContinuousOn measurableUtility (Set.Icc lo c))
    (hMcont_right : ContinuousOn measurableUtility (Set.Icc c hi))
    (hUcont_left : ContinuousOn unmeasurableUtility (Set.Icc lo c))
    (hUcont_right : ContinuousOn unmeasurableUtility (Set.Icc c hi))
    (hMderiv_left :
      ∀ x ∈ Set.Ioo lo c,
        HasDerivWithinAt measurableUtility (dMeasurable x) (Set.Ioo lo c) x)
    (hMderiv_right :
      ∀ x ∈ Set.Ioo c hi,
        HasDerivWithinAt measurableUtility (dMeasurable x) (Set.Ioo c hi) x)
    (hUderiv_left :
      ∀ x ∈ Set.Ioo lo c,
        HasDerivWithinAt unmeasurableUtility (dUnmeasurable x) (Set.Ioo lo c) x)
    (hUderiv_right :
      ∀ x ∈ Set.Ioo c hi,
        HasDerivWithinAt unmeasurableUtility (dUnmeasurable x) (Set.Ioo c hi) x)
    (hM_target : 0 < dMeasurable c)
    (hU_target : dUnmeasurable c < 0)
    (hleftM :
      ∀ x ∈ Set.Ioo lo c, dMeasurable c ≤ dMeasurable x)
    (hleftU :
      ∀ x ∈ Set.Ioo lo c, dUnmeasurable c ≤ dUnmeasurable x)
    (hrightM :
      ∀ x ∈ Set.Ioo c hi, dMeasurable x ≤ dMeasurable c)
    (hrightU :
      ∀ x ∈ Set.Ioo c hi, dUnmeasurable x ≤ dUnmeasurable c) :
    ∃ beta : ℝ,
      0 < beta ∧ beta < 1 ∧
      MaximizesOnInterval
        (weightedPrivateUtility beta measurableUtility unmeasurableUtility)
        c lo hi := by
  rcases exists_beta_weightedUtilityDerivative_eq_zero
      hM_target hU_target with ⟨beta, hbeta_pos, hbeta_lt, hzero⟩
  have hbeta_nonneg : 0 ≤ beta := le_of_lt hbeta_pos
  have hone_minus_nonneg : 0 ≤ 1 - beta := by linarith
  rcases weightedUtilityDerivative_signs_of_component_derivative_order
      hbeta_nonneg hone_minus_nonneg hzero
      hleftM hleftU hrightM hrightU with ⟨hleft_nonneg, hright_nonpos⟩
  refine ⟨beta, hbeta_pos, hbeta_lt, ?_⟩
  refine weightedPrivateUtility_maximizesOnInterval_of_derivative_signs
    (measurableUtility := measurableUtility)
    (unmeasurableUtility := unmeasurableUtility)
    (W' := fun x =>
      weightedUtilityDerivative beta (dMeasurable x) (dUnmeasurable x))
    hlo hhi ?_ ?_ ?_ ?_ hleft_nonneg hright_nonpos
  · simpa [weightedPrivateUtility] using
      (hMcont_left.const_mul beta).add (hUcont_left.const_mul (1 - beta))
  · simpa [weightedPrivateUtility] using
      (hMcont_right.const_mul beta).add (hUcont_right.const_mul (1 - beta))
  · intro x hx
    have hderiv :
        HasDerivWithinAt
          (weightedPrivateUtility beta measurableUtility unmeasurableUtility)
          (weightedUtilityDerivative beta (dMeasurable x) (dUnmeasurable x))
          (Set.Ioo lo c) x := by
      simpa [weightedPrivateUtility, weightedUtilityDerivative] using
        ((hMderiv_left x hx).const_mul beta).add
          ((hUderiv_left x hx).const_mul (1 - beta))
    exact hderiv
  · intro x hx
    have hderiv :
        HasDerivWithinAt
          (weightedPrivateUtility beta measurableUtility unmeasurableUtility)
          (weightedUtilityDerivative beta (dMeasurable x) (dUnmeasurable x))
          (Set.Ioo c hi) x := by
      simpa [weightedPrivateUtility, weightedUtilityDerivative] using
        ((hMderiv_right x hx).const_mul beta).add
          ((hUderiv_right x hx).const_mul (1 - beta))
    exact hderiv

/--
Source-shaped completion route for Proposition `prop:2levels-fixedcap` from
monotone marginal tradeoffs.  This is the economically tight one-dimensional
condition: the ratio of marginal unmeasurable-skill loss to marginal
measurable-skill gain is weakly increasing through the target cutoff, so the
supporting weight chosen by the source first-order equation makes the target
cutoff a global maximizer.
-/
theorem exists_beta_weightedPrivateUtility_maximizesOnInterval_of_marginal_tradeoff_order
    {measurableUtility unmeasurableUtility dMeasurable dUnmeasurable : ℝ → ℝ}
    {lo c hi : ℝ}
    (hlo : lo ≤ c)
    (hhi : c ≤ hi)
    (hMcont_left : ContinuousOn measurableUtility (Set.Icc lo c))
    (hMcont_right : ContinuousOn measurableUtility (Set.Icc c hi))
    (hUcont_left : ContinuousOn unmeasurableUtility (Set.Icc lo c))
    (hUcont_right : ContinuousOn unmeasurableUtility (Set.Icc c hi))
    (hMderiv_left :
      ∀ x ∈ Set.Ioo lo c,
        HasDerivWithinAt measurableUtility (dMeasurable x) (Set.Ioo lo c) x)
    (hMderiv_right :
      ∀ x ∈ Set.Ioo c hi,
        HasDerivWithinAt measurableUtility (dMeasurable x) (Set.Ioo c hi) x)
    (hUderiv_left :
      ∀ x ∈ Set.Ioo lo c,
        HasDerivWithinAt unmeasurableUtility (dUnmeasurable x) (Set.Ioo lo c) x)
    (hUderiv_right :
      ∀ x ∈ Set.Ioo c hi,
        HasDerivWithinAt unmeasurableUtility (dUnmeasurable x) (Set.Ioo c hi) x)
    (hM_target : 0 < dMeasurable c)
    (hU_target : dUnmeasurable c < 0)
    (hleft_trade :
      ∀ x ∈ Set.Ioo lo c,
        (-dUnmeasurable x) * dMeasurable c ≤
          (-dUnmeasurable c) * dMeasurable x)
    (hright_trade :
      ∀ x ∈ Set.Ioo c hi,
        (-dUnmeasurable c) * dMeasurable x ≤
          (-dUnmeasurable x) * dMeasurable c) :
    ∃ beta : ℝ,
      0 < beta ∧ beta < 1 ∧
      MaximizesOnInterval
        (weightedPrivateUtility beta measurableUtility unmeasurableUtility)
        c lo hi := by
  rcases exists_beta_weightedUtilityDerivative_signs_of_marginal_tradeoff_order
      hM_target hU_target hleft_trade hright_trade with
    ⟨beta, hbeta_pos, hbeta_lt, _hzero, hleft_nonneg, hright_nonpos⟩
  refine ⟨beta, hbeta_pos, hbeta_lt, ?_⟩
  refine weightedPrivateUtility_maximizesOnInterval_of_derivative_signs
    (measurableUtility := measurableUtility)
    (unmeasurableUtility := unmeasurableUtility)
    (W' := fun x =>
      weightedUtilityDerivative beta (dMeasurable x) (dUnmeasurable x))
    hlo hhi ?_ ?_ ?_ ?_ hleft_nonneg hright_nonpos
  · simpa [weightedPrivateUtility] using
      (hMcont_left.const_mul beta).add (hUcont_left.const_mul (1 - beta))
  · simpa [weightedPrivateUtility] using
      (hMcont_right.const_mul beta).add (hUcont_right.const_mul (1 - beta))
  · intro x hx
    have hderiv :
        HasDerivWithinAt
          (weightedPrivateUtility beta measurableUtility unmeasurableUtility)
          (weightedUtilityDerivative beta (dMeasurable x) (dUnmeasurable x))
          (Set.Ioo lo c) x := by
      simpa [weightedPrivateUtility, weightedUtilityDerivative] using
        ((hMderiv_left x hx).const_mul beta).add
          ((hUderiv_left x hx).const_mul (1 - beta))
    exact hderiv
  · intro x hx
    have hderiv :
        HasDerivWithinAt
          (weightedPrivateUtility beta measurableUtility unmeasurableUtility)
          (weightedUtilityDerivative beta (dMeasurable x) (dUnmeasurable x))
          (Set.Ioo c hi) x := by
      simpa [weightedPrivateUtility, weightedUtilityDerivative] using
        ((hMderiv_right x hx).const_mul beta).add
          ((hUderiv_right x hx).const_mul (1 - beta))
    exact hderiv

/--
The source second-price effort formula, isolated as a definition.  The
existence/uniqueness equilibrium proof for this formula is not closed here.
-/
noncomputable def secondPriceEffort
    (e0 : ℝ) (gInv g f : ℝ → ℝ) (tildePrev c theta : ℝ) : ℝ :=
  max (gInv (g tildePrev * f c / f theta)) e0

end LBG22StrategicRanking

import PRPKG24AccuracyDiversity.SeparableAsymptotic
import PRPKG24AccuracyDiversity.Exchange
import PRPKG24AccuracyDiversity.Bernoulli
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open Filter Topology
open scoped BigOperators

namespace PRPKG24AccuracyDiversity

/--
Expected top-one Bernoulli value from a ranked list of success probabilities:
the probability that at least one of the first `q` items succeeds.
-/
noncomputable def rankBernoulliTopOneValue
    (success : ℕ → ℝ) (q : ℕ) : ℝ := 1 - ∏ i ∈ Finset.range q, (1 - success i)

/--
Expected all-consumed Bernoulli value from a ranked list of success
probabilities: the sum of expected item values.
-/
noncomputable def rankBernoulliAllConsumedValue
    (success : ℕ → ℝ) (q : ℕ) : ℝ := ∑ i ∈ Finset.range q, success i

@[simp] theorem rankBernoulliTopOneValue_zero (success : ℕ → ℝ) :
    rankBernoulliTopOneValue success 0 = 0 := by
  simp [rankBernoulliTopOneValue]

@[simp] theorem rankBernoulliAllConsumedValue_zero (success : ℕ → ℝ) :
    rankBernoulliAllConsumedValue success 0 = 0 := by
  simp [rankBernoulliAllConsumedValue]

theorem rankBernoulliTopOneValue_succ_sub (success : ℕ → ℝ) (q : ℕ) :
    rankBernoulliTopOneValue success (q + 1) -
      rankBernoulliTopOneValue success q =
        success q * ∏ i ∈ Finset.range q, (1 - success i) := by
  unfold rankBernoulliTopOneValue
  rw [Finset.prod_range_succ]
  ring

theorem rankBernoulliTopOne_survivalProduct_pos
    (success : ℕ → ℝ) (hs_lt_one : ∀ i, success i < 1) (q : ℕ) :
    0 < ∏ i ∈ Finset.range q, (1 - success i) :=  Finset.prod_pos (fun i _ => sub_pos.mpr (hs_lt_one i))

theorem rankBernoulliTopOne_marginalCore_pos
    (success : ℕ → ℝ)
    (hs_pos : ∀ i, 0 < success i)
    (hs_lt_one : ∀ i, success i < 1) (q : ℕ) :
    0 < success q * ∏ i ∈ Finset.range q, (1 - success i) :=
   mul_pos (hs_pos q)
    (rankBernoulliTopOne_survivalProduct_pos success hs_lt_one q)

theorem rankBernoulliTopOne_survivalProduct_succ_le
    (success : ℕ → ℝ)
    (hs_nonneg : ∀ i, 0 ≤ success i)
    (hs_le_one : ∀ i, success i ≤ 1) (q : ℕ) :
    ∏ i ∈ Finset.range (q + 1), (1 - success i) ≤
      ∏ i ∈ Finset.range q, (1 - success i) := by
  rw [Finset.prod_range_succ]
  have hprod_nonneg :
      0 ≤ ∏ i ∈ Finset.range q, (1 - success i) :=
    Finset.prod_nonneg (fun i _ => sub_nonneg.mpr (hs_le_one i))
  have hfactor_le_one : 1 - success q ≤ 1 := by linarith [hs_nonneg q]
  calc
    (∏ i ∈ Finset.range q, (1 - success i)) * (1 - success q)
        ≤ (∏ i ∈ Finset.range q, (1 - success i)) * 1 :=
          mul_le_mul_of_nonneg_left hfactor_le_one hprod_nonneg
    _ = ∏ i ∈ Finset.range q, (1 - success i) := by ring

theorem rankBernoulliTopOne_survivalProduct_antitone
    (success : ℕ → ℝ)
    (hs_nonneg : ∀ i, 0 ≤ success i)
    (hs_le_one : ∀ i, success i ≤ 1) {q r : ℕ} (hqr : q ≤ r) :
    ∏ i ∈ Finset.range r, (1 - success i) ≤
      ∏ i ∈ Finset.range q, (1 - success i) :=
   Nat.le_induction (by rfl)
    (fun n _ ih =>
      le_trans
        (rankBernoulliTopOne_survivalProduct_succ_le
          success hs_nonneg hs_le_one n) ih)
    r hqr

theorem rankBernoulliTopOne_survivalProduct_le_one
    (success : ℕ → ℝ)
    (hs_nonneg : ∀ i, 0 ≤ success i)
    (hs_le_one : ∀ i, success i ≤ 1) (q : ℕ) :
    ∏ i ∈ Finset.range q, (1 - success i) ≤ 1 := by
  simpa using
    rankBernoulliTopOne_survivalProduct_antitone
      success hs_nonneg hs_le_one (q := 0) (r := q) (Nat.zero_le q)

theorem rankBernoulliTopOne_prod_one_sub_le_exp_neg_sum
    (success : ℕ → ℝ)
    (hs_le_one : ∀ i, success i ≤ 1) (s : Finset ℕ) :
    ∏ i ∈ s, (1 - success i) ≤
      Real.exp (-(∑ i ∈ s, success i)) := by
  calc
    ∏ i ∈ s, (1 - success i)
        ≤ ∏ i ∈ s, Real.exp (-(success i)) :=
          Finset.prod_le_prod
            (fun i _ => sub_nonneg.mpr (hs_le_one i))
            (fun i _ => Real.one_sub_le_exp_neg (success i))
    _ = Real.exp (∑ i ∈ s, -(success i)) := by
          rw [Real.exp_sum]
    _ = Real.exp (-(∑ i ∈ s, success i)) := by simp

theorem rankBernoulliTopOne_survivalProduct_eq_mul_Ico
    (success : ℕ → ℝ) {q r : ℕ} (hqr : q ≤ r) :
    ∏ i ∈ Finset.range r, (1 - success i) =
      (∏ i ∈ Finset.range q, (1 - success i)) *
        ∏ i ∈ Finset.Ico q r, (1 - success i) :=  (Finset.prod_range_mul_prod_Ico (fun i => 1 - success i) hqr).symm

theorem rankBernoulliTopOne_survivalProduct_le_mul_exp_neg_sum_Ico
    (success : ℕ → ℝ)
    (hs_le_one : ∀ i, success i ≤ 1) {q r : ℕ} (hqr : q ≤ r) :
    ∏ i ∈ Finset.range r, (1 - success i) ≤
      (∏ i ∈ Finset.range q, (1 - success i)) *
        Real.exp (-(∑ i ∈ Finset.Ico q r, success i)) := by
  rw [rankBernoulliTopOne_survivalProduct_eq_mul_Ico success hqr]
  have hprefix_nonneg :
      0 ≤ ∏ i ∈ Finset.range q, (1 - success i) :=
    Finset.prod_nonneg (fun i _ => sub_nonneg.mpr (hs_le_one i))
  exact mul_le_mul_of_nonneg_left
      (rankBernoulliTopOne_prod_one_sub_le_exp_neg_sum
        success hs_le_one (Finset.Ico q r))
      hprefix_nonneg

theorem one_sub_inv_le_exp_two_mul
    {x : ℝ} (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    (1 - x)⁻¹ ≤ Real.exp (2 * x) := by
  have hx_lt_one : x < 1 := by linarith
  have hden_pos : 0 < 1 - x := by linarith
  have hlog :
      -Real.log (1 - x) ≤ x / (1 - x) := by
    have hbase := Real.one_sub_inv_le_log_of_pos hden_pos
    have hupper : -Real.log (1 - x) ≤ (1 - x)⁻¹ - 1 := by
      linarith
    have hrewrite : (1 - x)⁻¹ - 1 = x / (1 - x) := by
      field_simp [ne_of_gt hden_pos]
      ring
    simpa [hrewrite] using hupper
  have hfrac :
      x / (1 - x) ≤ 2 * x := by
    rw [div_le_iff₀ hden_pos]
    nlinarith
  calc
    (1 - x)⁻¹ = Real.exp (-Real.log (1 - x)) := by
      rw [Real.exp_neg, Real.exp_log hden_pos]
    _ ≤ Real.exp (2 * x) := Real.exp_le_exp.mpr (le_trans hlog hfrac)

theorem rankBernoulliTopOne_survivalProduct_le_mul_exp_sum_Ico_reverse
    (success : ℕ → ℝ)
    (hs_nonneg : ∀ i, 0 ≤ success i)
    (hs_le_one : ∀ i, success i ≤ 1)
    {q r : ℕ} (hqr : q ≤ r)
    (hs_half : ∀ i ∈ Finset.Ico q r, success i ≤ 1 / 2) :
    ∏ i ∈ Finset.range q, (1 - success i) ≤
      (∏ i ∈ Finset.range r, (1 - success i)) *
        Real.exp (2 * ∑ i ∈ Finset.Ico q r, success i) := by
  have hprod_eq :
      ∏ i ∈ Finset.range r, (1 - success i) =
        (∏ i ∈ Finset.range q, (1 - success i)) *
          ∏ i ∈ Finset.Ico q r, (1 - success i) :=
    rankBernoulliTopOne_survivalProduct_eq_mul_Ico success hqr
  have hinterval_pos :
      0 < ∏ i ∈ Finset.Ico q r, (1 - success i) := by
    refine Finset.prod_pos ?_
    intro i hi
    have hhalf := hs_half i hi
    linarith
  have hprefix_eq :
      ∏ i ∈ Finset.range q, (1 - success i) =
        (∏ i ∈ Finset.range r, (1 - success i)) *
          (∏ i ∈ Finset.Ico q r, (1 - success i))⁻¹ := by
    rw [hprod_eq]
    field_simp [ne_of_gt hinterval_pos]
  have hfactor_le :
      ∀ i ∈ Finset.Ico q r,
        (1 - success i)⁻¹ ≤ Real.exp (2 * success i) := by
    intro i hi
    exact one_sub_inv_le_exp_two_mul (hs_nonneg i) (hs_half i hi)
  have hfactor_nonneg :
      ∀ i ∈ Finset.Ico q r, 0 ≤ (1 - success i)⁻¹ := by
    intro i hi
    have hhalf := hs_half i hi
    have hpos : 0 < 1 - success i := by linarith
    exact le_of_lt (inv_pos.mpr hpos)
  have hprod_factor_le :
      ∏ i ∈ Finset.Ico q r, (1 - success i)⁻¹ ≤
        ∏ i ∈ Finset.Ico q r, Real.exp (2 * success i) :=
    Finset.prod_le_prod hfactor_nonneg hfactor_le
  have hprod_inv :
      (∏ i ∈ Finset.Ico q r, (1 - success i))⁻¹ =
        ∏ i ∈ Finset.Ico q r, (1 - success i)⁻¹ := by
    simp
  have hprod_exp :
      ∏ i ∈ Finset.Ico q r, Real.exp (2 * success i) =
        Real.exp (2 * ∑ i ∈ Finset.Ico q r, success i) := by
    calc
      ∏ i ∈ Finset.Ico q r, Real.exp (2 * success i)
          = Real.exp (∑ i ∈ Finset.Ico q r, 2 * success i) := by
          rw [Real.exp_sum]
      _ = Real.exp (2 * ∑ i ∈ Finset.Ico q r, success i) := by
          congr 1
          rw [Finset.mul_sum]
  have hsurv_r_nonneg :
      0 ≤ ∏ i ∈ Finset.range r, (1 - success i) :=
    Finset.prod_nonneg (fun i _ => sub_nonneg.mpr (hs_le_one i))
  calc
    ∏ i ∈ Finset.range q, (1 - success i)
        = (∏ i ∈ Finset.range r, (1 - success i)) *
          (∏ i ∈ Finset.Ico q r, (1 - success i))⁻¹ := hprefix_eq
    _ ≤ (∏ i ∈ Finset.range r, (1 - success i)) *
          Real.exp (2 * ∑ i ∈ Finset.Ico q r, success i) := by
        rw [hprod_inv]
        exact mul_le_mul_of_nonneg_left
          (le_trans hprod_factor_le (le_of_eq hprod_exp)) hsurv_r_nonneg

theorem rankBernoulliTopOne_weighted_marginalCore_lt_of_Ico_exp_bound
    (success : ℕ → ℝ)
    (hs_nonneg : ∀ i, 0 ≤ success i)
    (hs_lt_one : ∀ i, success i < 1)
    {wsrc wdst : ℝ} (hwsrc_nonneg : 0 ≤ wsrc)
    {qsrc qdst : ℕ} (hqdst_le : qdst ≤ qsrc - 1)
    (hscalar :
      wsrc *
          (success (qsrc - 1) *
            Real.exp (-(∑ i ∈ Finset.Ico qdst (qsrc - 1), success i))) <
        wdst * success qdst) :
    wsrc *
        (success (qsrc - 1) *
          ∏ i ∈ Finset.range (qsrc - 1), (1 - success i)) <
      wdst *
        (success qdst *
          ∏ i ∈ Finset.range qdst, (1 - success i)) := by
  have hprod_bound :
      ∏ i ∈ Finset.range (qsrc - 1), (1 - success i) ≤
        (∏ i ∈ Finset.range qdst, (1 - success i)) *
          Real.exp (-(∑ i ∈ Finset.Ico qdst (qsrc - 1), success i)) :=
    rankBernoulliTopOne_survivalProduct_le_mul_exp_neg_sum_Ico
      success (fun i => le_of_lt (hs_lt_one i)) hqdst_le
  have hsrc_success_nonneg : 0 ≤ success (qsrc - 1) :=
    hs_nonneg (qsrc - 1)
  have hleft_le :
      wsrc *
          (success (qsrc - 1) *
            ∏ i ∈ Finset.range (qsrc - 1), (1 - success i)) ≤
        wsrc *
          (success (qsrc - 1) *
            ((∏ i ∈ Finset.range qdst, (1 - success i)) *
              Real.exp (-(∑ i ∈ Finset.Ico qdst (qsrc - 1), success i)))) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hprod_bound hsrc_success_nonneg)
      hwsrc_nonneg
  have hprefix_pos :
      0 < ∏ i ∈ Finset.range qdst, (1 - success i) :=
    rankBernoulliTopOne_survivalProduct_pos success hs_lt_one qdst
  have hstrict :
      (∏ i ∈ Finset.range qdst, (1 - success i)) *
          (wsrc *
            (success (qsrc - 1) *
              Real.exp (-(∑ i ∈ Finset.Ico qdst (qsrc - 1), success i)))) <
        (∏ i ∈ Finset.range qdst, (1 - success i)) *
          (wdst * success qdst) :=
    mul_lt_mul_of_pos_left hscalar hprefix_pos
  calc
    wsrc *
        (success (qsrc - 1) *
          ∏ i ∈ Finset.range (qsrc - 1), (1 - success i))
        ≤
      wsrc *
        (success (qsrc - 1) *
          ((∏ i ∈ Finset.range qdst, (1 - success i)) *
            Real.exp (-(∑ i ∈ Finset.Ico qdst (qsrc - 1), success i)))) :=
        hleft_le
    _ =
      (∏ i ∈ Finset.range qdst, (1 - success i)) *
        (wsrc *
          (success (qsrc - 1) *
            Real.exp (-(∑ i ∈ Finset.Ico qdst (qsrc - 1), success i)))) := by
        ring
    _ <
      (∏ i ∈ Finset.range qdst, (1 - success i)) *
        (wdst * success qdst) :=
        hstrict
    _ =
      wdst *
        (success qdst *
          ∏ i ∈ Finset.range qdst, (1 - success i)) := by
        ring

theorem rankBernoulliAllConsumedValue_succ_sub (success : ℕ → ℝ) (q : ℕ) :
    rankBernoulliAllConsumedValue success (q + 1) -
      rankBernoulliAllConsumedValue success q = success q := by
  unfold rankBernoulliAllConsumedValue
  rw [Finset.sum_range_succ]
  ring

theorem rankBernoulliTopOneValue_sub_pred
    (success : ℕ → ℝ) {q : ℕ} (hq : 0 < q) :
    rankBernoulliTopOneValue success q -
      rankBernoulliTopOneValue success (q - 1) =
        success (q - 1) *
          ∏ i ∈ Finset.range (q - 1), (1 - success i) := by
  have hcancel : q - 1 + 1 = q := Nat.sub_add_cancel (Nat.succ_le_of_lt hq)
  simpa [hcancel] using rankBernoulliTopOneValue_succ_sub success (q - 1)

theorem rankBernoulliAllConsumedValue_sub_pred
    (success : ℕ → ℝ) {q : ℕ} (hq : 0 < q) :
    rankBernoulliAllConsumedValue success q -
      rankBernoulliAllConsumedValue success (q - 1) =
        success (q - 1) := by
  have hcancel : q - 1 + 1 = q := Nat.sub_add_cancel (Nat.succ_le_of_lt hq)
  simpa [hcancel] using rankBernoulliAllConsumedValue_succ_sub success (q - 1)

theorem rankBernoulliTopOneValue_succ_sub_nonneg
    (success : ℕ → ℝ)
    (hs_nonneg : ∀ i, 0 ≤ success i)
    (hs_le_one : ∀ i, success i ≤ 1) (q : ℕ) :
    0 ≤ rankBernoulliTopOneValue success (q + 1) -
      rankBernoulliTopOneValue success q := by
  rw [rankBernoulliTopOneValue_succ_sub]
  exact mul_nonneg (hs_nonneg q)
    (Finset.prod_nonneg (fun i _ => sub_nonneg.mpr (hs_le_one i)))

theorem rankBernoulliAllConsumedValue_succ_sub_nonneg
    (success : ℕ → ℝ)
    (hs_nonneg : ∀ i, 0 ≤ success i) (q : ℕ) :
    0 ≤ rankBernoulliAllConsumedValue success (q + 1) -
      rankBernoulliAllConsumedValue success q := by
  rw [rankBernoulliAllConsumedValue_succ_sub]
  exact hs_nonneg q

theorem rankBernoulliTopOneValue_marginal_antitone
    (success : ℕ → ℝ)
    (hs_nonneg : ∀ i, 0 ≤ success i)
    (hs_le_one : ∀ i, success i ≤ 1)
    (hs_antitone : ∀ i, success (i + 1) ≤ success i) (q : ℕ) :
    rankBernoulliTopOneValue success (q + 2) -
        rankBernoulliTopOneValue success (q + 1) ≤
      rankBernoulliTopOneValue success (q + 1) -
        rankBernoulliTopOneValue success q := by
  rw [rankBernoulliTopOneValue_succ_sub success (q + 1),
    rankBernoulliTopOneValue_succ_sub success q]
  rw [Finset.prod_range_succ]
  have hprod_nonneg :
      0 ≤ ∏ i ∈ Finset.range q, (1 - success i) :=
    Finset.prod_nonneg (fun i _ => sub_nonneg.mpr (hs_le_one i))
  have hfactor :
      success (q + 1) * (1 - success q) ≤ success q := by
    calc
      success (q + 1) * (1 - success q)
          ≤ success (q + 1) * 1 :=
            mul_le_mul_of_nonneg_left (by linarith [hs_nonneg q])
              (hs_nonneg (q + 1))
      _ = success (q + 1) := by ring
      _ ≤ success q := hs_antitone q
  calc
    success (q + 1) *
        ((∏ i ∈ Finset.range q, (1 - success i)) * (1 - success q))
        = (∏ i ∈ Finset.range q, (1 - success i)) *
            (success (q + 1) * (1 - success q)) := by ring
    _ ≤ (∏ i ∈ Finset.range q, (1 - success i)) * success q :=
          mul_le_mul_of_nonneg_left hfactor hprod_nonneg
    _ = success q * ∏ i ∈ Finset.range q, (1 - success i) := by ring

theorem rankBernoulliAllConsumedValue_marginal_antitone
    (success : ℕ → ℝ)
    (hs_antitone : ∀ i, success (i + 1) ≤ success i) (q : ℕ) :
    rankBernoulliAllConsumedValue success (q + 2) -
        rankBernoulliAllConsumedValue success (q + 1) ≤
      rankBernoulliAllConsumedValue success (q + 1) -
        rankBernoulliAllConsumedValue success q := by
  rw [rankBernoulliAllConsumedValue_succ_sub success (q + 1),
    rankBernoulliAllConsumedValue_succ_sub success q]
  exact hs_antitone q

/-- Generic rank-Bernoulli top-one consumption model. -/
noncomputable def rankBernoulliTopOneConsumptionModel {T : ℕ}
    (likelihood : ItemType T → ℝ) (success : ℕ → ℝ) :
    ConsumptionModel T where
  likelihood := likelihood
  valueOfCount := fun _ q => rankBernoulliTopOneValue success q

/-- Generic rank-Bernoulli all-consumed consumption model. -/
noncomputable def rankBernoulliAllConsumedConsumptionModel {T : ℕ}
    (likelihood : ItemType T → ℝ) (success : ℕ → ℝ) :
    ConsumptionModel T where
  likelihood := likelihood
  valueOfCount := fun _ q => rankBernoulliAllConsumedValue success q

theorem rankBernoulliTopOneConsumptionModel_has_nonnegative_marginals {T : ℕ}
    (likelihood : ItemType T → ℝ) (success : ℕ → ℝ)
    (hs_nonneg : ∀ i, 0 ≤ success i)
    (hs_le_one : ∀ i, success i ≤ 1) :
    (rankBernoulliTopOneConsumptionModel likelihood success).HasNonnegativeMarginals := by
  intro _ q
  exact rankBernoulliTopOneValue_succ_sub_nonneg success hs_nonneg hs_le_one q

theorem rankBernoulliAllConsumedConsumptionModel_has_nonnegative_marginals {T : ℕ}
    (likelihood : ItemType T → ℝ) (success : ℕ → ℝ)
    (hs_nonneg : ∀ i, 0 ≤ success i) :
    (rankBernoulliAllConsumedConsumptionModel likelihood success).HasNonnegativeMarginals := by
  intro _ q
  exact rankBernoulliAllConsumedValue_succ_sub_nonneg success hs_nonneg q

theorem rankBernoulliTopOneConsumptionModel_has_diminishing_returns {T : ℕ}
    (likelihood : ItemType T → ℝ) (success : ℕ → ℝ)
    (hs_nonneg : ∀ i, 0 ≤ success i)
    (hs_le_one : ∀ i, success i ≤ 1)
    (hs_antitone : ∀ i, success (i + 1) ≤ success i) :
    (rankBernoulliTopOneConsumptionModel likelihood success).HasDiminishingReturns := by
  intro _ q
  exact rankBernoulliTopOneValue_marginal_antitone
    success hs_nonneg hs_le_one hs_antitone q

theorem rankBernoulliAllConsumedConsumptionModel_has_diminishing_returns {T : ℕ}
    (likelihood : ItemType T → ℝ) (success : ℕ → ℝ)
    (hs_antitone : ∀ i, success (i + 1) ≤ success i) :
    (rankBernoulliAllConsumedConsumptionModel likelihood success).HasDiminishingReturns := by
  intro _ q
  exact rankBernoulliAllConsumedValue_marginal_antitone success hs_antitone q

theorem rankBernoulliTopOneConsumptionModel_weightedForwardMarginal {T : ℕ}
    (likelihood : ItemType T → ℝ) (success : ℕ → ℝ)
    (t : ItemType T) (q : ℕ) :
    (rankBernoulliTopOneConsumptionModel likelihood success).weightedForwardMarginal t q =
      likelihood t *
        (success q * ∏ i ∈ Finset.range q, (1 - success i)) := by
  unfold ConsumptionModel.weightedForwardMarginal ConsumptionModel.marginalValue
    AppliedModelingLib.Allocation.marginal rankBernoulliTopOneConsumptionModel
  dsimp only
  rw [rankBernoulliTopOneValue_succ_sub]

theorem rankBernoulliTopOneConsumptionModel_weightedBackwardMarginal {T : ℕ}
    (likelihood : ItemType T → ℝ) (success : ℕ → ℝ)
    (t : ItemType T) {q : ℕ} (hq : 0 < q) :
    (rankBernoulliTopOneConsumptionModel likelihood success).weightedBackwardMarginal t q =
      likelihood t *
        (success (q - 1) * ∏ i ∈ Finset.range (q - 1), (1 - success i)) := by
  unfold ConsumptionModel.weightedBackwardMarginal rankBernoulliTopOneConsumptionModel
  dsimp only
  have hq_ne : ¬ q = 0 := ne_of_gt hq
  simp [hq_ne, rankBernoulliTopOneValue_sub_pred success hq]

theorem rankBernoulliAllConsumedConsumptionModel_weightedForwardMarginal {T : ℕ}
    (likelihood : ItemType T → ℝ) (success : ℕ → ℝ)
    (t : ItemType T) (q : ℕ) :
    (rankBernoulliAllConsumedConsumptionModel likelihood success).weightedForwardMarginal t q =
      likelihood t * success q := by
  unfold ConsumptionModel.weightedForwardMarginal ConsumptionModel.marginalValue
    AppliedModelingLib.Allocation.marginal rankBernoulliAllConsumedConsumptionModel
  dsimp only
  rw [rankBernoulliAllConsumedValue_succ_sub]

theorem rankBernoulliAllConsumedConsumptionModel_weightedBackwardMarginal {T : ℕ}
    (likelihood : ItemType T → ℝ) (success : ℕ → ℝ)
    (t : ItemType T) {q : ℕ} (hq : 0 < q) :
    (rankBernoulliAllConsumedConsumptionModel likelihood success).weightedBackwardMarginal t q =
      likelihood t * success (q - 1) := by
  unfold ConsumptionModel.weightedBackwardMarginal rankBernoulliAllConsumedConsumptionModel
  dsimp only
  have hq_ne : ¬ q = 0 := ne_of_gt hq
  simp [hq_ne, rankBernoulliAllConsumedValue_sub_pred success hq]

theorem rankBernoulliTopOneValue_const (p : ℝ) (q : ℕ) :
    rankBernoulliTopOneValue (fun _ => p) q =
      bernoulliAtLeastOneValue p q := by
  simp [rankBernoulliTopOneValue, bernoulliAtLeastOneValue]

/--
Algebraic cancellation used in the `α = 1` all-consumed branch: an inverse
marginal comparison is equivalent to a scaled-count comparison.
-/
theorem scaled_le_of_inverse_marginal_le
    {p_src p_dst c x y : ℝ}
    (hp_src : 0 < p_src) (hp_dst : 0 < p_dst) (hc : 0 < c)
    (hx : 0 < x) (hy : 0 < y)
    (h : p_dst * (c * y⁻¹) ≤ p_src * (c * x⁻¹)) :
    x / p_src ≤ y / p_dst := by
  have hc_nonneg : 0 ≤ c := le_of_lt hc
  have hdivc : p_dst * y⁻¹ ≤ p_src * x⁻¹ := by
    nlinarith [mul_le_mul_of_nonneg_right h hc_nonneg]
  have h1 : p_dst / y ≤ p_src / x := by
    simpa [div_eq_mul_inv] using hdivc
  have hcross : p_dst * x ≤ p_src * y := by
    rwa [div_le_div_iff₀ hy hx] at h1
  rw [div_le_div_iff₀ hp_src hp_dst]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hcross

/--
Power version of `scaled_le_of_inverse_marginal_le`, used for the positive
`α` all-consumed decaying-Bernoulli branch.
-/
theorem scaled_le_of_rpow_neg_marginal_le
    {p_src p_dst c α x y : ℝ}
    (hp_src : 0 < p_src) (hp_dst : 0 < p_dst) (hc : 0 < c)
    (hα : 0 < α) (hx : 0 < x) (hy : 0 < y)
    (h : p_dst * (c * y ^ (-α)) ≤ p_src * (c * x ^ (-α))) :
    x / p_src ^ (1 / α) ≤ y / p_dst ^ (1 / α) := by
  have hc_nonneg : 0 ≤ c := le_of_lt hc
  have hcancel : p_dst * y ^ (-α) ≤ p_src * x ^ (-α) := by
    nlinarith [mul_le_mul_of_nonneg_right h hc_nonneg]
  have hcancel' : p_dst / (y ^ α) ≤ p_src / (x ^ α) := by
    rw [Real.rpow_neg (le_of_lt hy), Real.rpow_neg (le_of_lt hx)] at hcancel
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hcancel
  have hxpow_pos : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  have hypow_pos : 0 < y ^ α := Real.rpow_pos_of_pos hy α
  have hcross : p_dst * x ^ α ≤ p_src * y ^ α := by
    rwa [div_le_div_iff₀ hypow_pos hxpow_pos] at hcancel'
  have hpow_le :
      (x / p_src ^ (1 / α)) ^ α ≤
        (y / p_dst ^ (1 / α)) ^ α := by
    rw [Real.div_rpow (le_of_lt hx)
      (le_of_lt (Real.rpow_pos_of_pos hp_src (1 / α))) α]
    rw [Real.div_rpow (le_of_lt hy)
      (le_of_lt (Real.rpow_pos_of_pos hp_dst (1 / α))) α]
    rw [← Real.rpow_mul (le_of_lt hp_src) (1 / α) α]
    rw [← Real.rpow_mul (le_of_lt hp_dst) (1 / α) α]
    have hmul : (1 / α) * α = 1 := by field_simp [ne_of_gt hα]
    rw [hmul, Real.rpow_one, Real.rpow_one]
    rw [div_le_div_iff₀ hp_src hp_dst]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcross
  have hleft_nonneg : 0 ≤ x / p_src ^ (1 / α) := by positivity
  have hright_nonneg : 0 ≤ y / p_dst ^ (1 / α) := by positivity
  exact (Real.rpow_le_rpow_iff hleft_nonneg hright_nonneg hα).mp hpow_le

theorem rpow_neg_marginal_lt_of_scaled_lt
    {p_src p_dst c α x y : ℝ}
    (hp_src : 0 < p_src) (hp_dst : 0 < p_dst) (hc : 0 < c)
    (hα : 0 < α) (hx : 0 < x) (hy : 0 < y)
    (hscaled : y / p_dst ^ (1 / α) < x / p_src ^ (1 / α)) :
    p_src * (c * x ^ (-α)) < p_dst * (c * y ^ (-α)) := by
  let wsrc : ℝ := p_src ^ (1 / α)
  let wdst : ℝ := p_dst ^ (1 / α)
  have hwsrc_pos : 0 < wsrc := by
    dsimp [wsrc]
    exact Real.rpow_pos_of_pos hp_src (1 / α)
  have hwdst_pos : 0 < wdst := by
    dsimp [wdst]
    exact Real.rpow_pos_of_pos hp_dst (1 / α)
  have hleft_pos : 0 < y / wdst := div_pos hy hwdst_pos
  have hright_pos : 0 < x / wsrc := div_pos hx hwsrc_pos
  have hpow_lt :
      (y / wdst) ^ α < (x / wsrc) ^ α :=
    Real.rpow_lt_rpow (le_of_lt hleft_pos) (by simpa [wsrc, wdst] using hscaled) hα
  have hsrc_pow :
      (x / wsrc) ^ α = x ^ α / p_src := by
    dsimp [wsrc]
    rw [Real.div_rpow (le_of_lt hx) (le_of_lt hwsrc_pos) α]
    rw [← Real.rpow_mul (le_of_lt hp_src) (1 / α) α]
    have hmul : (1 / α) * α = 1 := by field_simp [ne_of_gt hα]
    rw [hmul, Real.rpow_one]
  have hdst_pow :
      (y / wdst) ^ α = y ^ α / p_dst := by
    dsimp [wdst]
    rw [Real.div_rpow (le_of_lt hy) (le_of_lt hwdst_pos) α]
    rw [← Real.rpow_mul (le_of_lt hp_dst) (1 / α) α]
    have hmul : (1 / α) * α = 1 := by field_simp [ne_of_gt hα]
    rw [hmul, Real.rpow_one]
  have hpow_ratio_lt :
      y ^ α / p_dst < x ^ α / p_src := by
    simpa [hsrc_pow, hdst_pow] using hpow_lt
  have hxpow_pos : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  have hypow_pos : 0 < y ^ α := Real.rpow_pos_of_pos hy α
  have hscaled_marginal :
      p_src * x ^ (-α) < p_dst * y ^ (-α) := by
    have hinv_lt :
        1 / (x ^ α / p_src) < 1 / (y ^ α / p_dst) :=
      one_div_lt_one_div_of_lt (div_pos hypow_pos hp_dst) hpow_ratio_lt
    have hleft :
        1 / (x ^ α / p_src) = p_src / x ^ α := by
      field_simp [ne_of_gt hp_src, ne_of_gt hxpow_pos]
    have hright :
        1 / (y ^ α / p_dst) = p_dst / y ^ α := by
      field_simp [ne_of_gt hp_dst, ne_of_gt hypow_pos]
    calc
      p_src * x ^ (-α) = p_src / x ^ α := by
        rw [Real.rpow_neg (le_of_lt hx)]
        ring
      _ = 1 / (x ^ α / p_src) := by rw [hleft]
      _ < 1 / (y ^ α / p_dst) := hinv_lt
      _ = p_dst / y ^ α := hright
      _ = p_dst * y ^ (-α) := by
        rw [Real.rpow_neg (le_of_lt hy)]
        ring
  calc
    p_src * (c * x ^ (-α)) = c * (p_src * x ^ (-α)) := by ring
    _ < c * (p_dst * y ^ (-α)) :=
      mul_lt_mul_of_pos_left hscaled_marginal hc
    _ = p_dst * (c * y ^ (-α)) := by ring

theorem mul_exp_neg_lt_of_log_div_lt
    {x y B : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hlog : Real.log (x / y) < B) :
    x * Real.exp (-B) < y := by
  have hdiv_pos : 0 < x / y := div_pos hx hy
  have hdiv_lt_exp : x / y < Real.exp B :=
    (Real.log_lt_iff_lt_exp hdiv_pos).mp hlog
  have hx_lt : x < Real.exp B * y := by
    rwa [div_lt_iff₀ hy] at hdiv_lt_exp
  have hexp_pos : 0 < Real.exp B := Real.exp_pos B
  have hx_div_lt : x / Real.exp B < y := by
    rwa [div_lt_iff₀' hexp_pos]
  simpa [Real.exp_neg, div_eq_mul_inv] using hx_div_lt

theorem exp_sub_one_le_exp_one_sub_one_mul
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x - 1 ≤ (Real.exp 1 - 1) * x := by
  have hconv :
      Real.exp ((1 - x) • (0 : ℝ) + x • (1 : ℝ)) ≤
        (1 - x) • Real.exp (0 : ℝ) + x • Real.exp (1 : ℝ) :=
    convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ 1)
      (by linarith) hx0 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, mul_one, Real.exp_zero] at hconv
  linarith

theorem exp_sub_one_le_exp_one_mul
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x - 1 ≤ Real.exp 1 * x := by
  have h := exp_sub_one_le_exp_one_sub_one_mul hx0 hx1
  have hcoef : Real.exp 1 - 1 ≤ Real.exp 1 := by linarith
  exact le_trans h (mul_le_mul_of_nonneg_right hcoef hx0)

/-- Source Theorem 2 rank-decay success probability `q_i = c (i + d)^(-α)`. -/
noncomputable def decayingBernoulliSuccess
    (c d α : ℝ) (i : ℕ) : ℝ := c * (((i + 1 : ℕ) : ℝ) + d) ^ (-α)

@[simp] theorem decayingBernoulliSuccess_zero
    (c d : ℝ) (i : ℕ) :
    decayingBernoulliSuccess c d 0 i = c := by
  simp [decayingBernoulliSuccess]

theorem decayingBernoulliSuccess_one
    (c d : ℝ) (hd : 0 ≤ d) (i : ℕ) :
    decayingBernoulliSuccess c d 1 i =
      c * (1 / (((i + 1 : ℕ) : ℝ) + d)) := by
  unfold decayingBernoulliSuccess
  rw [Real.rpow_neg (by positivity : 0 ≤ (((i + 1 : ℕ) : ℝ) + d))]
  rw [Real.rpow_one, one_div]

theorem decayingBernoulliSuccess_nonneg
    (c d α : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    ∀ i, 0 ≤ decayingBernoulliSuccess c d α i := by
  intro i
  unfold decayingBernoulliSuccess
  positivity

theorem decayingBernoulliSuccess_pos
    (c d α : ℝ) (hc : 0 < c) (hd : 0 ≤ d) :
    ∀ i, 0 < decayingBernoulliSuccess c d α i := by
  intro i
  unfold decayingBernoulliSuccess
  positivity

theorem decayingBernoulliSuccess_tendsto_zero
    (c d α : ℝ) (hα : 0 < α) :
    Tendsto (decayingBernoulliSuccess c d α) atTop (nhds 0) := by
  have hpow :
      Tendsto (fun i : ℕ => (((i + 1 : ℕ) : ℝ) + d) ^ (-α))
        atTop (nhds 0) :=
    AppliedModelingLib.Math.tendsto_nat_succ_cast_add_const_rpow_neg_nhds_zero d hα
  refine Tendsto.congr'
    (f₁ := fun i : ℕ => c * ((((i + 1 : ℕ) : ℝ) + d) ^ (-α))) ?_ ?_
  · filter_upwards with i
    simp [decayingBernoulliSuccess, Nat.cast_add, add_comm]
  · simpa using hpow.const_mul c

theorem decayingBernoulliSuccess_antitone
    (c d α : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) (hα : 0 ≤ α) :
    ∀ i, decayingBernoulliSuccess c d α (i + 1) ≤
      decayingBernoulliSuccess c d α i := by
  intro i
  unfold decayingBernoulliSuccess
  have hbase_pos : 0 < (((i + 1 : ℕ) : ℝ) + d) := by positivity
  have hbase_le :
      (((i + 1 : ℕ) : ℝ) + d) ≤ (((i + 1 + 1 : ℕ) : ℝ) + d) := by
    have hn : (i + 1 : ℕ) ≤ i + 1 + 1 := Nat.le_succ (i + 1)
    have hr : ((i + 1 : ℕ) : ℝ) ≤ ((i + 1 + 1 : ℕ) : ℝ) := by
      exact_mod_cast hn
    simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hr d
  have hpow :
      (((i + 1 + 1 : ℕ) : ℝ) + d) ^ (-α) ≤
      (((i + 1 : ℕ) : ℝ) + d) ^ (-α) :=
    Real.rpow_le_rpow_of_nonpos hbase_pos hbase_le (neg_nonpos.mpr hα)
  exact mul_le_mul_of_nonneg_left hpow hc

theorem decayingBernoulliSuccess_antitone_of_le
    (c d α : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) (hα : 0 ≤ α)
    {i j : ℕ} (hij : i ≤ j) :
    decayingBernoulliSuccess c d α j ≤
      decayingBernoulliSuccess c d α i :=
   Nat.le_induction (by rfl)
    (fun n _ ih =>
      le_trans (decayingBernoulliSuccess_antitone c d α hc hd hα n) ih)
    j hij

theorem decayingBernoulliSuccess_le_first
    (c d α : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) (hα : 0 ≤ α) :
    ∀ i, decayingBernoulliSuccess c d α i ≤
      decayingBernoulliSuccess c d α 0 := by
  intro i
  induction i with
  | zero => rfl
  | succ i ih =>
      exact le_trans
        (decayingBernoulliSuccess_antitone c d α hc hd hα i) ih

theorem decayingBernoulliSuccess_lt_one_of_first_lt_one
    (c d α : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) (hα : 0 ≤ α)
    (hfirst : decayingBernoulliSuccess c d α 0 < 1) :
    ∀ i, decayingBernoulliSuccess c d α i < 1 := by
  intro i
  exact lt_of_le_of_lt
    (decayingBernoulliSuccess_le_first c d α hc hd hα i) hfirst

theorem decayingBernoulliSuccess_le_one_of_first_le_one
    (c d α : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) (hα : 0 ≤ α)
    (hfirst : decayingBernoulliSuccess c d α 0 ≤ 1) :
    ∀ i, decayingBernoulliSuccess c d α i ≤ 1 := by
  intro i
  exact le_trans (decayingBernoulliSuccess_le_first c d α hc hd hα i) hfirst

theorem decayingBernoulliSuccess_Ico_sum_lower_by_right
    (c d α : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) (hα : 0 ≤ α)
    {q r : ℕ} (hqr : q ≤ r) :
    ((r - q : ℕ) : ℝ) * decayingBernoulliSuccess c d α (r - 1) ≤
      ∑ i ∈ Finset.Ico q r, decayingBernoulliSuccess c d α i := by
  by_cases hr : r = 0
  · subst r
    have hq : q = 0 := Nat.eq_zero_of_le_zero hqr
    subst q
    simp
  · have hsum_const_le :
        ∑ i ∈ Finset.Ico q r, decayingBernoulliSuccess c d α (r - 1) ≤
          ∑ i ∈ Finset.Ico q r, decayingBernoulliSuccess c d α i := by
      refine Finset.sum_le_sum ?_
      intro i hi
      have hi_lt : i < r := (Finset.mem_Ico.mp hi).2
      have hi_le_pred : i ≤ r - 1 := Nat.le_pred_of_lt hi_lt
      exact decayingBernoulliSuccess_antitone_of_le
        c d α hc hd hα hi_le_pred
    have hsum_const :
        ∑ i ∈ Finset.Ico q r, decayingBernoulliSuccess c d α (r - 1) =
          ((r - q : ℕ) : ℝ) * decayingBernoulliSuccess c d α (r - 1) := by
      simp [Nat.card_Ico]
    rw [← hsum_const]
    exact hsum_const_le

theorem decayingBernoulliSuccess_Ico_sum_upper_by_left
    (c d α : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) (hα : 0 ≤ α)
    {q r : ℕ} :
    ∑ i ∈ Finset.Ico q r, decayingBernoulliSuccess c d α i ≤
      ((r - q : ℕ) : ℝ) * decayingBernoulliSuccess c d α q := by
  have hsum_le :
      ∑ i ∈ Finset.Ico q r, decayingBernoulliSuccess c d α i ≤
        ∑ _i ∈ Finset.Ico q r, decayingBernoulliSuccess c d α q := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hqi : q ≤ i := (Finset.mem_Ico.mp hi).1
    exact decayingBernoulliSuccess_antitone_of_le c d α hc hd hα hqi
  have hsum_const :
      ∑ _i ∈ Finset.Ico q r, decayingBernoulliSuccess c d α q =
        ((r - q : ℕ) : ℝ) * decayingBernoulliSuccess c d α q := by
    simp [Nat.card_Ico]
  exact le_trans hsum_le (le_of_eq hsum_const)

theorem log_succ_div_self_le_inv {x : ℝ} (hx : 0 < x) :
    Real.log ((x + 1) / x) ≤ 1 / x := by
  have hratio_pos : 0 < (x + 1) / x := by positivity
  have hlog := Real.log_le_sub_one_of_pos hratio_pos
  have hratio_sub : (x + 1) / x - 1 = 1 / x := by
    field_simp [ne_of_gt hx]
    ring
  simpa [hratio_sub] using hlog

theorem two_div_two_mul_add_one_le_log_succ_div_self {x : ℝ} (hx : 0 < x) :
    2 / (2 * x + 1) ≤ Real.log ((x + 1) / x) := by
  have hinv_nonneg : 0 ≤ 1 / x := by positivity
  have h :=
    Real.le_log_one_add_of_nonneg hinv_nonneg
  have harg : 1 + x⁻¹ = (x + 1) / x := by
    field_simp [ne_of_gt hx]
  have hleft : 2 * x⁻¹ / (x⁻¹ + 2) = 2 / (2 * x + 1) := by
    field_simp [ne_of_gt hx]
    ring
  simpa [harg, hleft, one_div] using h

theorem neg_log_one_sub_div_le_div_sub
    {c x : ℝ} (hc : 0 ≤ c) (hcx : c < x) :
    -Real.log (1 - c / x) ≤ c / (x - c) := by
  have hx : 0 < x := lt_of_le_of_lt hc hcx
  have hpos : 0 < 1 - c / x := by
    rw [sub_pos]
    rw [div_lt_one hx]
    exact hcx
  have hlog :=
    Real.one_sub_inv_le_log_of_pos hpos
  have hupper : -Real.log (1 - c / x) ≤ (1 - c / x)⁻¹ - 1 := by
    linarith
  have hrewrite : (1 - c / x)⁻¹ - 1 = c / (x - c) := by
    field_simp [ne_of_gt hx, ne_of_gt hpos, ne_of_gt (sub_pos.mpr hcx)]
    ring
  simpa [hrewrite] using hupper

theorem alpha_one_reverse_log_correction_le
    {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (hcx2 : 2 * c ≤ x) :
    -Real.log (1 - c / x) - c * Real.log ((x + 1) / x) ≤
      c / (x - c) - c * (2 / (2 * x + 1)) := by
  have hcx : c < x := by nlinarith
  have hneg :
      -Real.log (1 - c / x) ≤ c / (x - c) :=
    neg_log_one_sub_div_le_div_sub (le_of_lt hc) hcx
  have hlog :
      2 / (2 * x + 1) ≤ Real.log ((x + 1) / x) :=
    two_div_two_mul_add_one_le_log_succ_div_self hx
  have hmul :
      c * (2 / (2 * x + 1)) ≤ c * Real.log ((x + 1) / x) :=
    mul_le_mul_of_nonneg_left hlog (le_of_lt hc)
  linarith

theorem alpha_one_reverse_correction_term_le_inv_sq
    {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (hcx2 : 2 * c ≤ x) :
    c / (x - c) - c * (2 / (2 * x + 1)) ≤
      c * (1 + 2 * c) / x ^ 2 := by
  have hcx : c < x := by nlinarith
  have hx_sub_c_pos : 0 < x - c := by linarith
  have hden_two_pos : 0 < 2 * x + 1 := by nlinarith
  have hx_sq_pos : 0 < x ^ 2 := sq_pos_of_pos hx
  have hnum_nonneg : 0 ≤ c * (1 + 2 * c) := by nlinarith
  have hrewrite :
      c / (x - c) - c * (2 / (2 * x + 1)) =
        c * (1 + 2 * c) / ((x - c) * (2 * x + 1)) := by
    field_simp [ne_of_gt hx_sub_c_pos, ne_of_gt hden_two_pos]
    ring
  have hden_ge :
      x ^ 2 ≤ (x - c) * (2 * x + 1) := by
    have hx_minus_two_c_nonneg : 0 ≤ x - 2 * c := by linarith
    have hprod_nonneg : 0 ≤ x * (x - 2 * c) :=
      mul_nonneg (le_of_lt hx) hx_minus_two_c_nonneg
    nlinarith
  have hden_pos : 0 < (x - c) * (2 * x + 1) :=
    mul_pos hx_sub_c_pos hden_two_pos
  rw [hrewrite]
  exact div_le_div_of_nonneg_left hnum_nonneg hx_sq_pos hden_ge

theorem alpha_one_reverse_correction_term_nonneg
    {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (hcx2 : 2 * c ≤ x) :
    0 ≤ c / (x - c) - c * (2 / (2 * x + 1)) := by
  have hcx : c < x := by nlinarith
  have hx_sub_c_pos : 0 < x - c := by linarith
  have hden_two_pos : 0 < 2 * x + 1 := by nlinarith
  have hrewrite :
      c / (x - c) - c * (2 / (2 * x + 1)) =
        c * (1 + 2 * c) / ((x - c) * (2 * x + 1)) := by
    field_simp [ne_of_gt hx_sub_c_pos, ne_of_gt hden_two_pos]
    ring
  rw [hrewrite]
  positivity

theorem alpha_one_reverse_correction_sum_le_inv_sq_sum
    (c d : ℝ) {q r : ℕ} (hc : 0 < c) (hd : 0 ≤ d)
    (hlarge :
      ∀ i ∈ Finset.Ico q r, 2 * c ≤ (((i + 1 : ℕ) : ℝ) + d)) :
    (∑ i ∈ Finset.Ico q r,
      (c / ((((i + 1 : ℕ) : ℝ) + d) - c) -
        c * (2 / (2 * (((i + 1 : ℕ) : ℝ) + d) + 1)))) ≤
      ∑ i ∈ Finset.Ico q r,
        c * (1 + 2 * c) / ((((i + 1 : ℕ) : ℝ) + d) ^ 2) := by
  refine Finset.sum_le_sum ?_
  intro i hi
  exact alpha_one_reverse_correction_term_le_inv_sq
    hc (by positivity) (hlarge i hi)

theorem alpha_one_reverse_correction_sum_nonneg
    (c d : ℝ) {q r : ℕ} (hc : 0 < c) (hd : 0 ≤ d)
    (hlarge :
      ∀ i ∈ Finset.Ico q r, 2 * c ≤ (((i + 1 : ℕ) : ℝ) + d)) :
    0 ≤
      ∑ i ∈ Finset.Ico q r,
        (c / ((((i + 1 : ℕ) : ℝ) + d) - c) -
          c * (2 / (2 * (((i + 1 : ℕ) : ℝ) + d) + 1))) :=
   Finset.sum_nonneg (fun i hi =>
    alpha_one_reverse_correction_term_nonneg
      hc (by positivity) (hlarge i hi))

theorem alpha_one_reverse_large_of_left_floor
    {c d : ℝ} {floor qsrc qdst i : ℕ} (hd : 0 ≤ d)
    (hfloor : 2 * c - d ≤ (floor : ℝ))
    (hqsrc_floor : floor < qsrc)
    (hi : i ∈ Finset.Ico (qsrc - 1) qdst) :
    2 * c ≤ (((i + 1 : ℕ) : ℝ) + d) := by
  have hleft : qsrc - 1 ≤ i := (Finset.mem_Ico.mp hi).1
  have hqsrc_pos : 0 < qsrc := Nat.lt_of_le_of_lt (Nat.zero_le floor) hqsrc_floor
  have hqsrc_le_i_succ : qsrc ≤ i + 1 := by
    have hsucc := Nat.succ_le_succ hleft
    simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hqsrc_pos)] using hsucc
  have hfloor_le_qsrc : floor ≤ qsrc := Nat.le_of_lt hqsrc_floor
  have hfloor_real_le_i_succ :
      (floor : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by
    exact_mod_cast le_trans hfloor_le_qsrc hqsrc_le_i_succ
  linarith

theorem alpha_one_inv_sq_Ico_sum_le_left
    (d : ℝ) (hd : 0 ≤ d) {q r : ℕ} :
    (∑ i ∈ Finset.Ico q r,
        1 / ((((i + 1 : ℕ) : ℝ) + d) ^ 2)) ≤
      ((r - q : ℕ) : ℝ) *
        (1 / ((((q + 1 : ℕ) : ℝ) + d) ^ 2)) := by
  have hterm :
      ∀ i ∈ Finset.Ico q r,
        1 / ((((i + 1 : ℕ) : ℝ) + d) ^ 2) ≤
          1 / ((((q + 1 : ℕ) : ℝ) + d) ^ 2) := by
    intro i hi
    have hqi : q ≤ i := (Finset.mem_Ico.mp hi).1
    have hbase_le :
        (((q + 1 : ℕ) : ℝ) + d) ≤ (((i + 1 : ℕ) : ℝ) + d) := by
      have hcast : ((q + 1 : ℕ) : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_succ hqi
      linarith
    have hq_pos : 0 < (((q + 1 : ℕ) : ℝ) + d) := by positivity
    have hi_pos : 0 < (((i + 1 : ℕ) : ℝ) + d) := by positivity
    have hsquares :
        (((q + 1 : ℕ) : ℝ) + d) ^ 2 ≤
          (((i + 1 : ℕ) : ℝ) + d) ^ 2 := by
      nlinarith
    exact one_div_le_one_div_of_le (sq_pos_of_pos hq_pos) hsquares
  calc
    (∑ i ∈ Finset.Ico q r,
        1 / ((((i + 1 : ℕ) : ℝ) + d) ^ 2))
        ≤ ∑ _i ∈ Finset.Ico q r,
            1 / ((((q + 1 : ℕ) : ℝ) + d) ^ 2) :=
          Finset.sum_le_sum hterm
    _ =
      ((r - q : ℕ) : ℝ) *
        (1 / ((((q + 1 : ℕ) : ℝ) + d) ^ 2)) := by
        simp [Nat.card_Ico, nsmul_eq_mul]

theorem alpha_one_reverse_correction_sum_le_length_left
    (c d : ℝ) {q r : ℕ} (hc : 0 < c) (hd : 0 ≤ d)
    (hlarge :
      ∀ i ∈ Finset.Ico q r, 2 * c ≤ (((i + 1 : ℕ) : ℝ) + d)) :
    (∑ i ∈ Finset.Ico q r,
      (c / ((((i + 1 : ℕ) : ℝ) + d) - c) -
        c * (2 / (2 * (((i + 1 : ℕ) : ℝ) + d) + 1)))) ≤
      (c * (1 + 2 * c)) * ((r - q : ℕ) : ℝ) *
        (1 / ((((q + 1 : ℕ) : ℝ) + d) ^ 2)) := by
  let K : ℝ := c * (1 + 2 * c)
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    nlinarith
  have hsum :=
    alpha_one_reverse_correction_sum_le_inv_sq_sum
      c d hc hd hlarge
  have hsum_eq :
      (∑ i ∈ Finset.Ico q r,
        c * (1 + 2 * c) / ((((i + 1 : ℕ) : ℝ) + d) ^ 2)) =
        K *
          ∑ i ∈ Finset.Ico q r,
            1 / ((((i + 1 : ℕ) : ℝ) + d) ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    dsimp [K]
    ring
  calc
    (∑ i ∈ Finset.Ico q r,
      (c / ((((i + 1 : ℕ) : ℝ) + d) - c) -
        c * (2 / (2 * (((i + 1 : ℕ) : ℝ) + d) + 1))))
        ≤ ∑ i ∈ Finset.Ico q r,
            c * (1 + 2 * c) / ((((i + 1 : ℕ) : ℝ) + d) ^ 2) :=
          hsum
    _ = K *
          ∑ i ∈ Finset.Ico q r,
            1 / ((((i + 1 : ℕ) : ℝ) + d) ^ 2) :=
          hsum_eq
    _ ≤ K *
          (((r - q : ℕ) : ℝ) *
            (1 / ((((q + 1 : ℕ) : ℝ) + d) ^ 2))) :=
          mul_le_mul_of_nonneg_left
            (alpha_one_inv_sq_Ico_sum_le_left d hd) hK_nonneg
    _ =
      (c * (1 + 2 * c)) * ((r - q : ℕ) : ℝ) *
        (1 / ((((q + 1 : ℕ) : ℝ) + d) ^ 2)) := by
        dsimp [K]
        ring

theorem alpha_one_reverse_factor_le_rpow_exp
    {c x E : ℝ} (hc : 0 < c) (hx : 0 < x) (hcx2 : 2 * c ≤ x)
    (hE :
      c / (x - c) - c * (2 / (2 * x + 1)) ≤ E) :
    (1 - c / x)⁻¹ ≤ ((x + 1) / x) ^ c * Real.exp E := by
  have hcx : c < x := by nlinarith
  have hsub_pos : 0 < 1 - c / x := by
    rw [sub_pos]
    rw [div_lt_one hx]
    exact hcx
  have hratio_pos : 0 < (x + 1) / x := by positivity
  have hcorr :=
    alpha_one_reverse_log_correction_le hc hx hcx2
  have hlog_bound :
      -Real.log (1 - c / x) ≤ c * Real.log ((x + 1) / x) + E := by
    linarith
  calc
    (1 - c / x)⁻¹
        = Real.exp (-Real.log (1 - c / x)) := by
          rw [Real.exp_neg, Real.exp_log hsub_pos]
    _ ≤ Real.exp (c * Real.log ((x + 1) / x) + E) :=
          Real.exp_le_exp.mpr hlog_bound
    _ = ((x + 1) / x) ^ c * Real.exp E := by
          rw [Real.exp_add, Real.rpow_def_of_pos hratio_pos]
          ring_nf

theorem decayingBernoulliSuccess_one_Ico_sum_lower_log
    (c d : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d)
    {q r : ℕ} (hqr : q ≤ r) :
    c * Real.log
        ((((r + 1 : ℕ) : ℝ) + d) / (((q + 1 : ℕ) : ℝ) + d)) ≤
      ∑ i ∈ Finset.Ico q r, decayingBernoulliSuccess c d 1 i := by
  have hterm :
      ∀ i ∈ Finset.Ico q r,
        c * (Real.log ((((i + 1 + 1 : ℕ) : ℝ) + d) /
            (((i + 1 : ℕ) : ℝ) + d))) ≤
          decayingBernoulliSuccess c d 1 i := by
    intro i _hi
    rw [decayingBernoulliSuccess_one c d hd i]
    have hden_pos : 0 < (((i + 1 : ℕ) : ℝ) + d) := by positivity
    have hlog_le :
        Real.log ((((i + 1 + 1 : ℕ) : ℝ) + d) /
            (((i + 1 : ℕ) : ℝ) + d)) ≤
          1 / (((i + 1 : ℕ) : ℝ) + d) := by
      have hsucc_eq :
          (((i + 1 + 1 : ℕ) : ℝ) + d) =
            (((i + 1 : ℕ) : ℝ) + d) + 1 := by
        norm_num
        ring
      rw [hsucc_eq]
      exact log_succ_div_self_le_inv hden_pos
    exact mul_le_mul_of_nonneg_left hlog_le hc
  have hsum_le :
      ∑ i ∈ Finset.Ico q r,
          c * (Real.log ((((i + 1 + 1 : ℕ) : ℝ) + d) /
            (((i + 1 : ℕ) : ℝ) + d))) ≤
        ∑ i ∈ Finset.Ico q r, decayingBernoulliSuccess c d 1 i :=
    Finset.sum_le_sum hterm
  have hlog_term :
      ∀ i,
        Real.log ((((i + 1 + 1 : ℕ) : ℝ) + d) /
            (((i + 1 : ℕ) : ℝ) + d)) =
          Real.log (((i + 1 + 1 : ℕ) : ℝ) + d) -
            Real.log (((i + 1 : ℕ) : ℝ) + d) := by
    intro i
    have hnum_ne : (((i + 1 + 1 : ℕ) : ℝ) + d) ≠ 0 := by positivity
    have hden_ne : (((i + 1 : ℕ) : ℝ) + d) ≠ 0 := by positivity
    rw [Real.log_div hnum_ne hden_ne]
  have hsum_log :
      ∑ i ∈ Finset.Ico q r,
          Real.log ((((i + 1 + 1 : ℕ) : ℝ) + d) /
            (((i + 1 : ℕ) : ℝ) + d)) =
        Real.log (((r + 1 : ℕ) : ℝ) + d) -
          Real.log (((q + 1 : ℕ) : ℝ) + d) := by
    simp_rw [hlog_term]
    simpa using
      (Finset.sum_Ico_sub (fun i : ℕ =>
        Real.log (((i + 1 : ℕ) : ℝ) + d)) hqr)
  have hsum_mul :
      ∑ i ∈ Finset.Ico q r,
          c * (Real.log ((((i + 1 + 1 : ℕ) : ℝ) + d) /
            (((i + 1 : ℕ) : ℝ) + d))) =
        c * (Real.log (((r + 1 : ℕ) : ℝ) + d) -
          Real.log (((q + 1 : ℕ) : ℝ) + d)) := by
    rw [← Finset.mul_sum, hsum_log]
  have hlog_div :
      Real.log
          ((((r + 1 : ℕ) : ℝ) + d) / (((q + 1 : ℕ) : ℝ) + d)) =
        Real.log (((r + 1 : ℕ) : ℝ) + d) -
          Real.log (((q + 1 : ℕ) : ℝ) + d) := by
    have hnum_ne : (((r + 1 : ℕ) : ℝ) + d) ≠ 0 := by positivity
    have hden_ne : (((q + 1 : ℕ) : ℝ) + d) ≠ 0 := by positivity
    rw [Real.log_div hnum_ne hden_ne]
  calc
    c * Real.log
        ((((r + 1 : ℕ) : ℝ) + d) / (((q + 1 : ℕ) : ℝ) + d))
        = ∑ i ∈ Finset.Ico q r,
            c * (Real.log ((((i + 1 + 1 : ℕ) : ℝ) + d) /
              (((i + 1 : ℕ) : ℝ) + d))) := by
          rw [hsum_mul, hlog_div]
    _ ≤ ∑ i ∈ Finset.Ico q r, decayingBernoulliSuccess c d 1 i := hsum_le

theorem decayingBernoulliTopOne_survivalProduct_pos
    (c d α : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) (hα : 0 ≤ α)
    (hfirst : decayingBernoulliSuccess c d α 0 < 1) (q : ℕ) :
    0 < ∏ i ∈ Finset.range q, (1 - decayingBernoulliSuccess c d α i) :=
   rankBernoulliTopOne_survivalProduct_pos
    (decayingBernoulliSuccess c d α)
    (decayingBernoulliSuccess_lt_one_of_first_lt_one c d α hc hd hα hfirst) q

theorem decayingBernoulliTopOne_marginalCore_pos
    (c d α : ℝ) (hc_pos : 0 < c) (hd : 0 ≤ d) (hα : 0 ≤ α)
    (hfirst : decayingBernoulliSuccess c d α 0 < 1) (q : ℕ) :
    0 < decayingBernoulliSuccess c d α q *
      ∏ i ∈ Finset.range q, (1 - decayingBernoulliSuccess c d α i) :=
   rankBernoulliTopOne_marginalCore_pos
    (decayingBernoulliSuccess c d α)
    (decayingBernoulliSuccess_pos c d α hc_pos hd)
    (decayingBernoulliSuccess_lt_one_of_first_lt_one
      c d α (le_of_lt hc_pos) hd hα hfirst) q

theorem decayingBernoulliTopOne_survivalProduct_antitone
    (c d α : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) (hα : 0 ≤ α)
    (hfirst : decayingBernoulliSuccess c d α 0 ≤ 1) {q r : ℕ}
    (hqr : q ≤ r) :
    ∏ i ∈ Finset.range r, (1 - decayingBernoulliSuccess c d α i) ≤
      ∏ i ∈ Finset.range q, (1 - decayingBernoulliSuccess c d α i) :=
   rankBernoulliTopOne_survivalProduct_antitone
    (decayingBernoulliSuccess c d α)
    (decayingBernoulliSuccess_nonneg c d α hc hd)
    (decayingBernoulliSuccess_le_one_of_first_le_one c d α hc hd hα hfirst)
    hqr

theorem decayingBernoulliTopOne_survivalProduct_le_one
    (c d α : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) (hα : 0 ≤ α)
    (hfirst : decayingBernoulliSuccess c d α 0 ≤ 1) (q : ℕ) :
    ∏ i ∈ Finset.range q, (1 - decayingBernoulliSuccess c d α i) ≤ 1 :=
   rankBernoulliTopOne_survivalProduct_le_one
    (decayingBernoulliSuccess c d α)
    (decayingBernoulliSuccess_nonneg c d α hc hd)
    (decayingBernoulliSuccess_le_one_of_first_le_one c d α hc hd hα hfirst) q

theorem decayingBernoulliTopOne_survivalProduct_le_mul_exp_neg_sum_Ico
    (c d α : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) (hα : 0 ≤ α)
    (hfirst : decayingBernoulliSuccess c d α 0 ≤ 1)
    {q r : ℕ} (hqr : q ≤ r) :
    ∏ i ∈ Finset.range r, (1 - decayingBernoulliSuccess c d α i) ≤
      (∏ i ∈ Finset.range q, (1 - decayingBernoulliSuccess c d α i)) *
        Real.exp (-(∑ i ∈ Finset.Ico q r, decayingBernoulliSuccess c d α i)) :=
    rankBernoulliTopOne_survivalProduct_le_mul_exp_neg_sum_Ico
      (decayingBernoulliSuccess c d α)
      (decayingBernoulliSuccess_le_one_of_first_le_one c d α hc hd hα hfirst)
      hqr

theorem decayingBernoulliTopOne_alpha_one_survivalProduct_le_mul_exp_neg_log_ratio
    (c d : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hfirst : decayingBernoulliSuccess c d 1 0 ≤ 1)
    {q r : ℕ} (hqr : q ≤ r) :
    ∏ i ∈ Finset.range r, (1 - decayingBernoulliSuccess c d 1 i) ≤
      (∏ i ∈ Finset.range q, (1 - decayingBernoulliSuccess c d 1 i)) *
        Real.exp
          (-(c * Real.log
            ((((r + 1 : ℕ) : ℝ) + d) / (((q + 1 : ℕ) : ℝ) + d)))) := by
  have hprod_sum :
      ∏ i ∈ Finset.range r, (1 - decayingBernoulliSuccess c d 1 i) ≤
        (∏ i ∈ Finset.range q, (1 - decayingBernoulliSuccess c d 1 i)) *
          Real.exp (-(∑ i ∈ Finset.Ico q r,
            decayingBernoulliSuccess c d 1 i)) :=
    decayingBernoulliTopOne_survivalProduct_le_mul_exp_neg_sum_Ico
      c d 1 hc hd (by norm_num) hfirst hqr
  have hsum_lower :
      c * Real.log
          ((((r + 1 : ℕ) : ℝ) + d) / (((q + 1 : ℕ) : ℝ) + d)) ≤
        ∑ i ∈ Finset.Ico q r, decayingBernoulliSuccess c d 1 i :=
    decayingBernoulliSuccess_one_Ico_sum_lower_log c d hc hd hqr
  have hexp_le :
      Real.exp (-(∑ i ∈ Finset.Ico q r,
            decayingBernoulliSuccess c d 1 i)) ≤
        Real.exp
          (-(c * Real.log
            ((((r + 1 : ℕ) : ℝ) + d) / (((q + 1 : ℕ) : ℝ) + d)))) :=
    Real.exp_le_exp.mpr (neg_le_neg hsum_lower)
  have hsuccess_le_one :
      ∀ i, decayingBernoulliSuccess c d 1 i ≤ 1 :=
    decayingBernoulliSuccess_le_one_of_first_le_one
      c d 1 hc hd (by norm_num) hfirst
  have hprefix_nonneg :
      0 ≤ ∏ i ∈ Finset.range q, (1 - decayingBernoulliSuccess c d 1 i) :=
    Finset.prod_nonneg (fun i _ => sub_nonneg.mpr (hsuccess_le_one i))
  exact le_trans hprod_sum
    (mul_le_mul_of_nonneg_left hexp_le hprefix_nonneg)

theorem exp_neg_mul_log_div_eq_div_rpow
    {A B c : ℝ} (hA : 0 < A) (hB : 0 < B) :
    Real.exp (-(c * Real.log (A / B))) = (B / A) ^ c := by
  have hBA_pos : 0 < B / A := div_pos hB hA
  rw [Real.rpow_def_of_pos hBA_pos]
  congr 1
  rw [Real.log_div (ne_of_gt hB) (ne_of_gt hA),
    Real.log_div (ne_of_gt hA) (ne_of_gt hB)]
  ring

theorem decayingBernoulliTopOne_alpha_one_survivalProduct_le_mul_rpow_ratio
    (c d : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hfirst : decayingBernoulliSuccess c d 1 0 ≤ 1)
    {q r : ℕ} (hqr : q ≤ r) :
    ∏ i ∈ Finset.range r, (1 - decayingBernoulliSuccess c d 1 i) ≤
      (∏ i ∈ Finset.range q, (1 - decayingBernoulliSuccess c d 1 i)) *
        ((((q + 1 : ℕ) : ℝ) + d) / (((r + 1 : ℕ) : ℝ) + d)) ^ c := by
  have h :=
    decayingBernoulliTopOne_alpha_one_survivalProduct_le_mul_exp_neg_log_ratio
      c d hc hd hfirst hqr
  have hA : 0 < (((r + 1 : ℕ) : ℝ) + d) := by positivity
  have hB : 0 < (((q + 1 : ℕ) : ℝ) + d) := by positivity
  rw [exp_neg_mul_log_div_eq_div_rpow
      (A := (((r + 1 : ℕ) : ℝ) + d))
      (B := (((q + 1 : ℕ) : ℝ) + d)) (c := c) hA hB] at h
  simpa [Nat.cast_add, add_comm, add_left_comm, add_assoc] using h

theorem decayingBernoulliTopOne_alpha_one_reverse_survivalProduct_le_mul_prod_exp
    (c d : ℝ) (hc : 0 < c) (hd : 0 ≤ d)
    (hfirst : decayingBernoulliSuccess c d 1 0 < 1)
    {q r : ℕ} (hqr : q ≤ r)
    (hlarge :
      ∀ i ∈ Finset.Ico q r, 2 * c ≤ (((i + 1 : ℕ) : ℝ) + d)) :
    ∏ i ∈ Finset.range q, (1 - decayingBernoulliSuccess c d 1 i) ≤
      (∏ i ∈ Finset.range r, (1 - decayingBernoulliSuccess c d 1 i)) *
        (∏ i ∈ Finset.Ico q r,
          (((((i + 1 : ℕ) : ℝ) + d) + 1) /
              (((i + 1 : ℕ) : ℝ) + d)) ^ c) *
        Real.exp
          (∑ i ∈ Finset.Ico q r,
            (c / ((((i + 1 : ℕ) : ℝ) + d) - c) -
              c * (2 / (2 * (((i + 1 : ℕ) : ℝ) + d) + 1)))) := by
  let success : ℕ → ℝ := decayingBernoulliSuccess c d 1
  let ratio : ℕ → ℝ :=
    fun i => ((((i + 1 : ℕ) : ℝ) + d) + 1) /
      (((i + 1 : ℕ) : ℝ) + d)
  let corr : ℕ → ℝ :=
    fun i =>
      c / ((((i + 1 : ℕ) : ℝ) + d) - c) -
        c * (2 / (2 * (((i + 1 : ℕ) : ℝ) + d) + 1))
  have hprod_eq :
      ∏ i ∈ Finset.range r, (1 - success i) =
        (∏ i ∈ Finset.range q, (1 - success i)) *
          ∏ i ∈ Finset.Ico q r, (1 - success i) :=
    rankBernoulliTopOne_survivalProduct_eq_mul_Ico success hqr
  have hinterval_pos :
      0 < ∏ i ∈ Finset.Ico q r, (1 - success i) := by
    refine Finset.prod_pos ?_
    intro i hi
    have hx : 0 < (((i + 1 : ℕ) : ℝ) + d) := by positivity
    have hc_lt_x : c < (((i + 1 : ℕ) : ℝ) + d) := by
      nlinarith [hlarge i hi]
    rw [show success i = c / (((i + 1 : ℕ) : ℝ) + d) by
      change decayingBernoulliSuccess c d 1 i = c / (((i + 1 : ℕ) : ℝ) + d)
      rw [decayingBernoulliSuccess_one c d hd i]
      ring]
    rw [sub_pos]
    rw [div_lt_one hx]
    exact hc_lt_x
  have hprefix_eq :
      ∏ i ∈ Finset.range q, (1 - success i) =
        (∏ i ∈ Finset.range r, (1 - success i)) *
          (∏ i ∈ Finset.Ico q r, (1 - success i))⁻¹ := by
    rw [hprod_eq]
    field_simp [ne_of_gt hinterval_pos]
  have hfactor_le :
      ∀ i ∈ Finset.Ico q r,
        (1 - success i)⁻¹ ≤ ratio i ^ c * Real.exp (corr i) := by
    intro i hi
    have hx : 0 < (((i + 1 : ℕ) : ℝ) + d) := by positivity
    have hsuccess :
        success i = c / (((i + 1 : ℕ) : ℝ) + d) := by
      change decayingBernoulliSuccess c d 1 i = c / (((i + 1 : ℕ) : ℝ) + d)
      rw [decayingBernoulliSuccess_one c d hd i]
      ring
    have h :=
      alpha_one_reverse_factor_le_rpow_exp
        (c := c) (x := (((i + 1 : ℕ) : ℝ) + d)) (E := corr i)
        hc hx (hlarge i hi) (by rfl)
    simpa [success, hsuccess, ratio, corr] using h
  have hfactor_nonneg :
      ∀ i ∈ Finset.Ico q r, 0 ≤ (1 - success i)⁻¹ := by
    intro i hi
    have hx : 0 < (((i + 1 : ℕ) : ℝ) + d) := by positivity
    have hc_lt_x : c < (((i + 1 : ℕ) : ℝ) + d) := by
      nlinarith [hlarge i hi]
    have hpos : 0 < 1 - success i := by
      rw [show success i = c / (((i + 1 : ℕ) : ℝ) + d) by
        change decayingBernoulliSuccess c d 1 i = c / (((i + 1 : ℕ) : ℝ) + d)
        rw [decayingBernoulliSuccess_one c d hd i]
        ring]
      rw [sub_pos]
      rw [div_lt_one hx]
      exact hc_lt_x
    exact le_of_lt (inv_pos.mpr hpos)
  have hprod_factor_le :
      ∏ i ∈ Finset.Ico q r, (1 - success i)⁻¹ ≤
        ∏ i ∈ Finset.Ico q r, ratio i ^ c * Real.exp (corr i) :=
    Finset.prod_le_prod hfactor_nonneg hfactor_le
  have hprod_inv :
      (∏ i ∈ Finset.Ico q r, (1 - success i))⁻¹ =
        ∏ i ∈ Finset.Ico q r, (1 - success i)⁻¹ := by
    simp
  have hprod_rhs :
      ∏ i ∈ Finset.Ico q r, ratio i ^ c * Real.exp (corr i) =
        (∏ i ∈ Finset.Ico q r, ratio i ^ c) *
          Real.exp (∑ i ∈ Finset.Ico q r, corr i) := by
    rw [Finset.prod_mul_distrib]
    rw [Real.exp_sum]
  have hprod_factor_le_bound :
      (∏ i ∈ Finset.Ico q r, (1 - success i))⁻¹ ≤
        (∏ i ∈ Finset.Ico q r, ratio i ^ c) *
          Real.exp (∑ i ∈ Finset.Ico q r, corr i) := by
    rw [hprod_inv]
    exact le_trans hprod_factor_le (le_of_eq hprod_rhs)
  have hsurv_r_pos :
      0 < ∏ i ∈ Finset.range r, (1 - success i) :=
    decayingBernoulliTopOne_survivalProduct_pos
      c d 1 (le_of_lt hc) hd (by norm_num) hfirst r
  calc
    ∏ i ∈ Finset.range q, (1 - decayingBernoulliSuccess c d 1 i)
        = (∏ i ∈ Finset.range r, (1 - success i)) *
          (∏ i ∈ Finset.Ico q r, (1 - success i))⁻¹ := by
          simpa [success] using hprefix_eq
    _ ≤ (∏ i ∈ Finset.range r, (1 - success i)) *
          ((∏ i ∈ Finset.Ico q r, ratio i ^ c) *
            Real.exp (∑ i ∈ Finset.Ico q r, corr i)) :=
          mul_le_mul_of_nonneg_left
            hprod_factor_le_bound
            (le_of_lt hsurv_r_pos)
    _ =
      (∏ i ∈ Finset.range r, (1 - success i)) *
        (∏ i ∈ Finset.Ico q r, ratio i ^ c) *
        Real.exp (∑ i ∈ Finset.Ico q r, corr i) := by
        ring
    _ =
      (∏ i ∈ Finset.range r, (1 - decayingBernoulliSuccess c d 1 i)) *
        (∏ i ∈ Finset.Ico q r,
          (((((i + 1 : ℕ) : ℝ) + d) + 1) /
              (((i + 1 : ℕ) : ℝ) + d)) ^ c) *
        Real.exp
          (∑ i ∈ Finset.Ico q r,
            (c / ((((i + 1 : ℕ) : ℝ) + d) - c) -
              c * (2 / (2 * (((i + 1 : ℕ) : ℝ) + d) + 1)))) := by
        simp [success, ratio, corr]

theorem alpha_one_adjacent_ratio_prod_eq
    (d : ℝ) (hd : 0 ≤ d) {q r : ℕ} (hqr : q ≤ r) :
    ∏ i ∈ Finset.Ico q r,
        (((((i + 1 : ℕ) : ℝ) + d) + 1) /
          (((i + 1 : ℕ) : ℝ) + d)) =
      (((r + 1 : ℕ) : ℝ) + d) /
        (((q + 1 : ℕ) : ℝ) + d) := by
  refine Nat.le_induction ?base ?step r hqr
  · simp
    have hq_pos : (((q + 1 : ℕ) : ℝ) + d) ≠ 0 := by positivity
    field_simp [hq_pos]
  · intro n hqn ih
    rw [Finset.prod_Ico_succ_top hqn]
    rw [ih]
    have hq_pos : (((q + 1 : ℕ) : ℝ) + d) ≠ 0 := by positivity
    have hn_pos : (((n + 1 : ℕ) : ℝ) + d) ≠ 0 := by positivity
    field_simp [hq_pos, hn_pos]
    norm_num
    ring

theorem alpha_one_adjacent_ratio_rpow_prod_eq
    (c d : ℝ) (hd : 0 ≤ d) {q r : ℕ} (hqr : q ≤ r) :
    ∏ i ∈ Finset.Ico q r,
        (((((i + 1 : ℕ) : ℝ) + d) + 1) /
          (((i + 1 : ℕ) : ℝ) + d)) ^ c =
      ((((r + 1 : ℕ) : ℝ) + d) /
        (((q + 1 : ℕ) : ℝ) + d)) ^ c := by
  have hnonneg :
      ∀ i ∈ Finset.Ico q r,
        0 ≤ (((((i + 1 : ℕ) : ℝ) + d) + 1) /
          (((i + 1 : ℕ) : ℝ) + d)) := by
    intro i _hi
    positivity
  rw [Real.finset_prod_rpow (Finset.Ico q r)
    (fun i => (((((i + 1 : ℕ) : ℝ) + d) + 1) /
      (((i + 1 : ℕ) : ℝ) + d))) hnonneg c]
  rw [alpha_one_adjacent_ratio_prod_eq d hd hqr]

theorem decayingBernoulliTopOne_alpha_one_reverse_survivalProduct_le_mul_rpow_exp
    (c d : ℝ) (hc : 0 < c) (hd : 0 ≤ d)
    (hfirst : decayingBernoulliSuccess c d 1 0 < 1)
    {q r : ℕ} (hqr : q ≤ r)
    (hlarge :
      ∀ i ∈ Finset.Ico q r, 2 * c ≤ (((i + 1 : ℕ) : ℝ) + d)) :
    ∏ i ∈ Finset.range q, (1 - decayingBernoulliSuccess c d 1 i) ≤
      (∏ i ∈ Finset.range r, (1 - decayingBernoulliSuccess c d 1 i)) *
        ((((r + 1 : ℕ) : ℝ) + d) /
          (((q + 1 : ℕ) : ℝ) + d)) ^ c *
        Real.exp
          (∑ i ∈ Finset.Ico q r,
            (c / ((((i + 1 : ℕ) : ℝ) + d) - c) -
              c * (2 / (2 * (((i + 1 : ℕ) : ℝ) + d) + 1)))) := by
  have h :=
    decayingBernoulliTopOne_alpha_one_reverse_survivalProduct_le_mul_prod_exp
      c d hc hd hfirst hqr hlarge
  rw [alpha_one_adjacent_ratio_rpow_prod_eq c d hd hqr] at h
  simpa [mul_assoc] using h

theorem decayingBernoulliTopOne_alpha_one_weighted_marginalCore_lt_of_rpow_ratio_bound
    (c d : ℝ) {wsrc wdst : ℝ} {qsrc qdst : ℕ}
    (hc : 0 < c) (hd : 0 ≤ d)
    (hfirst : decayingBernoulliSuccess c d 1 0 < 1)
    (hwsrc_nonneg : 0 ≤ wsrc)
    (hqsrc_pos : 0 < qsrc)
    (hqdst_le : qdst ≤ qsrc - 1)
    (hscalar :
      wsrc *
          (decayingBernoulliSuccess c d 1 (qsrc - 1) *
            ((((qdst + 1 : ℕ) : ℝ) + d) /
              (((qsrc : ℕ) : ℝ) + d)) ^ c) <
        wdst * decayingBernoulliSuccess c d 1 qdst) :
    wsrc *
        (decayingBernoulliSuccess c d 1 (qsrc - 1) *
          ∏ i ∈ Finset.range (qsrc - 1),
            (1 - decayingBernoulliSuccess c d 1 i)) <
      wdst *
        (decayingBernoulliSuccess c d 1 qdst *
          ∏ i ∈ Finset.range qdst,
            (1 - decayingBernoulliSuccess c d 1 i)) := by
  have hprod_bound :
      ∏ i ∈ Finset.range (qsrc - 1), (1 - decayingBernoulliSuccess c d 1 i) ≤
        (∏ i ∈ Finset.range qdst, (1 - decayingBernoulliSuccess c d 1 i)) *
          ((((qdst + 1 : ℕ) : ℝ) + d) /
            ((((qsrc - 1) + 1 : ℕ) : ℝ) + d)) ^ c :=
    decayingBernoulliTopOne_alpha_one_survivalProduct_le_mul_rpow_ratio
      c d (le_of_lt hc) hd (le_of_lt hfirst) hqdst_le
  have hsrc_success_nonneg :
      0 ≤ decayingBernoulliSuccess c d 1 (qsrc - 1) :=
    decayingBernoulliSuccess_nonneg c d 1 (le_of_lt hc) hd (qsrc - 1)
  have hleft_le :
      wsrc *
          (decayingBernoulliSuccess c d 1 (qsrc - 1) *
            ∏ i ∈ Finset.range (qsrc - 1),
              (1 - decayingBernoulliSuccess c d 1 i)) ≤
        wsrc *
          (decayingBernoulliSuccess c d 1 (qsrc - 1) *
            ((∏ i ∈ Finset.range qdst,
              (1 - decayingBernoulliSuccess c d 1 i)) *
              ((((qdst + 1 : ℕ) : ℝ) + d) /
                ((((qsrc - 1) + 1 : ℕ) : ℝ) + d)) ^ c)) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hprod_bound hsrc_success_nonneg)
      hwsrc_nonneg
  have hprefix_pos :
      0 < ∏ i ∈ Finset.range qdst, (1 - decayingBernoulliSuccess c d 1 i) :=
    decayingBernoulliTopOne_survivalProduct_pos
      c d 1 (le_of_lt hc) hd (by norm_num) hfirst qdst
  have hscalar' :
      wsrc *
          (decayingBernoulliSuccess c d 1 (qsrc - 1) *
            ((((qdst + 1 : ℕ) : ℝ) + d) /
              ((((qsrc - 1) + 1 : ℕ) : ℝ) + d)) ^ c) <
        wdst * decayingBernoulliSuccess c d 1 qdst := by
    have hpred_succ : qsrc - 1 + 1 = qsrc :=
      Nat.sub_add_cancel (Nat.succ_le_of_lt hqsrc_pos)
    simpa [hpred_succ] using hscalar
  have hstrict :
      (∏ i ∈ Finset.range qdst, (1 - decayingBernoulliSuccess c d 1 i)) *
          (wsrc *
            (decayingBernoulliSuccess c d 1 (qsrc - 1) *
              ((((qdst + 1 : ℕ) : ℝ) + d) /
                ((((qsrc - 1) + 1 : ℕ) : ℝ) + d)) ^ c)) <
        (∏ i ∈ Finset.range qdst, (1 - decayingBernoulliSuccess c d 1 i)) *
          (wdst * decayingBernoulliSuccess c d 1 qdst) :=
    mul_lt_mul_of_pos_left hscalar' hprefix_pos
  calc
    wsrc *
        (decayingBernoulliSuccess c d 1 (qsrc - 1) *
          ∏ i ∈ Finset.range (qsrc - 1),
            (1 - decayingBernoulliSuccess c d 1 i))
        ≤
      wsrc *
        (decayingBernoulliSuccess c d 1 (qsrc - 1) *
          ((∏ i ∈ Finset.range qdst,
            (1 - decayingBernoulliSuccess c d 1 i)) *
            ((((qdst + 1 : ℕ) : ℝ) + d) /
              ((((qsrc - 1) + 1 : ℕ) : ℝ) + d)) ^ c)) :=
        hleft_le
    _ =
      (∏ i ∈ Finset.range qdst, (1 - decayingBernoulliSuccess c d 1 i)) *
        (wsrc *
          (decayingBernoulliSuccess c d 1 (qsrc - 1) *
            ((((qdst + 1 : ℕ) : ℝ) + d) /
              ((((qsrc - 1) + 1 : ℕ) : ℝ) + d)) ^ c)) := by
        ring
    _ <
      (∏ i ∈ Finset.range qdst, (1 - decayingBernoulliSuccess c d 1 i)) *
        (wdst * decayingBernoulliSuccess c d 1 qdst) :=
        hstrict
    _ =
      wdst *
        (decayingBernoulliSuccess c d 1 qdst *
          ∏ i ∈ Finset.range qdst,
            (1 - decayingBernoulliSuccess c d 1 i)) := by
        ring

theorem decayingBernoulliTopOne_alpha_one_weighted_marginalCore_lt_of_reverse_rpow_exp_bound
    (c d : ℝ) {wsrc wdst : ℝ} {qsrc qdst : ℕ}
    (hc : 0 < c) (hd : 0 ≤ d)
    (hfirst : decayingBernoulliSuccess c d 1 0 < 1)
    (hwsrc_nonneg : 0 ≤ wsrc)
    (hqsrc_pos : 0 < qsrc)
    (hqsrc_pred_le : qsrc - 1 ≤ qdst)
    (hlarge :
      ∀ i ∈ Finset.Ico (qsrc - 1) qdst,
        2 * c ≤ (((i + 1 : ℕ) : ℝ) + d))
    (hscalar :
      wsrc *
          (decayingBernoulliSuccess c d 1 (qsrc - 1) *
            (((((qdst + 1 : ℕ) : ℝ) + d) /
              (((qsrc : ℕ) : ℝ) + d)) ^ c *
              Real.exp
                (∑ i ∈ Finset.Ico (qsrc - 1) qdst,
                  (c / ((((i + 1 : ℕ) : ℝ) + d) - c) -
                    c * (2 / (2 * (((i + 1 : ℕ) : ℝ) + d) + 1)))))) <
        wdst * decayingBernoulliSuccess c d 1 qdst) :
    wsrc *
        (decayingBernoulliSuccess c d 1 (qsrc - 1) *
          ∏ i ∈ Finset.range (qsrc - 1),
            (1 - decayingBernoulliSuccess c d 1 i)) <
      wdst *
        (decayingBernoulliSuccess c d 1 qdst *
          ∏ i ∈ Finset.range qdst,
            (1 - decayingBernoulliSuccess c d 1 i)) := by
  have hprod_bound :
      ∏ i ∈ Finset.range (qsrc - 1), (1 - decayingBernoulliSuccess c d 1 i) ≤
        (∏ i ∈ Finset.range qdst, (1 - decayingBernoulliSuccess c d 1 i)) *
          (((((qdst + 1 : ℕ) : ℝ) + d) /
            ((((qsrc - 1) + 1 : ℕ) : ℝ) + d)) ^ c) *
          Real.exp
            (∑ i ∈ Finset.Ico (qsrc - 1) qdst,
              (c / ((((i + 1 : ℕ) : ℝ) + d) - c) -
                c * (2 / (2 * (((i + 1 : ℕ) : ℝ) + d) + 1)))) :=
    decayingBernoulliTopOne_alpha_one_reverse_survivalProduct_le_mul_rpow_exp
      c d hc hd hfirst hqsrc_pred_le hlarge
  have hsrc_success_nonneg :
      0 ≤ decayingBernoulliSuccess c d 1 (qsrc - 1) :=
    decayingBernoulliSuccess_nonneg c d 1 (le_of_lt hc) hd (qsrc - 1)
  have hleft_le :
      wsrc *
          (decayingBernoulliSuccess c d 1 (qsrc - 1) *
            ∏ i ∈ Finset.range (qsrc - 1),
              (1 - decayingBernoulliSuccess c d 1 i)) ≤
        wsrc *
          (decayingBernoulliSuccess c d 1 (qsrc - 1) *
            (((∏ i ∈ Finset.range qdst,
              (1 - decayingBernoulliSuccess c d 1 i)) *
              (((((qdst + 1 : ℕ) : ℝ) + d) /
                ((((qsrc - 1) + 1 : ℕ) : ℝ) + d)) ^ c)) *
              Real.exp
                (∑ i ∈ Finset.Ico (qsrc - 1) qdst,
                  (c / ((((i + 1 : ℕ) : ℝ) + d) - c) -
                    c * (2 / (2 * (((i + 1 : ℕ) : ℝ) + d) + 1)))))) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hprod_bound hsrc_success_nonneg)
      hwsrc_nonneg
  have hprefix_pos :
      0 < ∏ i ∈ Finset.range qdst, (1 - decayingBernoulliSuccess c d 1 i) :=
    decayingBernoulliTopOne_survivalProduct_pos
      c d 1 (le_of_lt hc) hd (by norm_num) hfirst qdst
  have hscalar' :
      wsrc *
          (decayingBernoulliSuccess c d 1 (qsrc - 1) *
            (((((qdst + 1 : ℕ) : ℝ) + d) /
              ((((qsrc - 1) + 1 : ℕ) : ℝ) + d)) ^ c *
              Real.exp
                (∑ i ∈ Finset.Ico (qsrc - 1) qdst,
                  (c / ((((i + 1 : ℕ) : ℝ) + d) - c) -
                    c * (2 / (2 * (((i + 1 : ℕ) : ℝ) + d) + 1)))))) <
        wdst * decayingBernoulliSuccess c d 1 qdst := by
    have hpred_succ : qsrc - 1 + 1 = qsrc :=
      Nat.sub_add_cancel (Nat.succ_le_of_lt hqsrc_pos)
    simpa [hpred_succ] using hscalar
  have hstrict :
      (∏ i ∈ Finset.range qdst, (1 - decayingBernoulliSuccess c d 1 i)) *
          (wsrc *
            (decayingBernoulliSuccess c d 1 (qsrc - 1) *
              (((((qdst + 1 : ℕ) : ℝ) + d) /
                ((((qsrc - 1) + 1 : ℕ) : ℝ) + d)) ^ c *
                Real.exp
                  (∑ i ∈ Finset.Ico (qsrc - 1) qdst,
                    (c / ((((i + 1 : ℕ) : ℝ) + d) - c) -
                      c * (2 / (2 * (((i + 1 : ℕ) : ℝ) + d) + 1))))))) <
        (∏ i ∈ Finset.range qdst, (1 - decayingBernoulliSuccess c d 1 i)) *
          (wdst * decayingBernoulliSuccess c d 1 qdst) :=
    mul_lt_mul_of_pos_left hscalar' hprefix_pos
  calc
    wsrc *
        (decayingBernoulliSuccess c d 1 (qsrc - 1) *
          ∏ i ∈ Finset.range (qsrc - 1),
            (1 - decayingBernoulliSuccess c d 1 i))
        ≤
      wsrc *
        (decayingBernoulliSuccess c d 1 (qsrc - 1) *
          (((∏ i ∈ Finset.range qdst,
            (1 - decayingBernoulliSuccess c d 1 i)) *
            (((((qdst + 1 : ℕ) : ℝ) + d) /
              ((((qsrc - 1) + 1 : ℕ) : ℝ) + d)) ^ c)) *
            Real.exp
              (∑ i ∈ Finset.Ico (qsrc - 1) qdst,
                (c / ((((i + 1 : ℕ) : ℝ) + d) - c) -
                  c * (2 / (2 * (((i + 1 : ℕ) : ℝ) + d) + 1)))))) :=
        hleft_le
    _ =
      (∏ i ∈ Finset.range qdst, (1 - decayingBernoulliSuccess c d 1 i)) *
        (wsrc *
          (decayingBernoulliSuccess c d 1 (qsrc - 1) *
            (((((qdst + 1 : ℕ) : ℝ) + d) /
              ((((qsrc - 1) + 1 : ℕ) : ℝ) + d)) ^ c *
              Real.exp
                (∑ i ∈ Finset.Ico (qsrc - 1) qdst,
                  (c / ((((i + 1 : ℕ) : ℝ) + d) - c) -
                    c * (2 / (2 * (((i + 1 : ℕ) : ℝ) + d) + 1))))))) := by
        ring
    _ <
      (∏ i ∈ Finset.range qdst, (1 - decayingBernoulliSuccess c d 1 i)) *
        (wdst * decayingBernoulliSuccess c d 1 qdst) :=
        hstrict
    _ =
      wdst *
        (decayingBernoulliSuccess c d 1 qdst *
          ∏ i ∈ Finset.range qdst,
            (1 - decayingBernoulliSuccess c d 1 i)) := by
        ring

theorem decayingBernoulliTopOne_alpha_one_scalar_lt_of_shifted_scaled_lt
    {p_src p_dst c d : ℝ} {qsrc qdst : ℕ}
    (hp_src : 0 < p_src) (hp_dst : 0 < p_dst)
    (hc : 0 < c) (hd : 0 ≤ d) (hqsrc_pos : 0 < qsrc)
    (hscaled :
      ((((qdst + 1 : ℕ) : ℝ) + d) / p_dst ^ (1 / (1 + c))) <
        ((((qsrc : ℕ) : ℝ) + d) / p_src ^ (1 / (1 + c)))) :
    p_src *
        (decayingBernoulliSuccess c d 1 (qsrc - 1) *
          ((((qdst + 1 : ℕ) : ℝ) + d) /
            (((qsrc : ℕ) : ℝ) + d)) ^ c) <
      p_dst * decayingBernoulliSuccess c d 1 qdst := by
  let ρ : ℝ := 1 + c
  let A : ℝ := ((qsrc : ℕ) : ℝ) + d
  let B : ℝ := (((qdst + 1 : ℕ) : ℝ) + d)
  let vsrc : ℝ := p_src ^ (1 / ρ)
  let vdst : ℝ := p_dst ^ (1 / ρ)
  have hρ_pos : 0 < ρ := by dsimp [ρ]; linarith
  have hA_pos : 0 < A := by
    dsimp [A]
    positivity
  have hB_pos : 0 < B := by
    dsimp [B]
    positivity
  have hvsrc_pos : 0 < vsrc := by
    dsimp [vsrc]
    exact Real.rpow_pos_of_pos hp_src (1 / ρ)
  have hvdst_pos : 0 < vdst := by
    dsimp [vdst]
    exact Real.rpow_pos_of_pos hp_dst (1 / ρ)
  have hscaled' : B / vdst < A / vsrc := by
    simpa [A, B, vsrc, vdst, ρ] using hscaled
  have hpow_lt :
      (B / vdst) ^ ρ < (A / vsrc) ^ ρ :=
    Real.rpow_lt_rpow (le_of_lt (div_pos hB_pos hvdst_pos)) hscaled' hρ_pos
  have hvsrc_pow : vsrc ^ ρ = p_src := by
    dsimp [vsrc, ρ]
    rw [← Real.rpow_mul (le_of_lt hp_src)]
    have hmul : (1 / (1 + c)) * (1 + c) = 1 := by
      field_simp [ne_of_gt hρ_pos]
    rw [hmul, Real.rpow_one]
  have hvdst_pow : vdst ^ ρ = p_dst := by
    dsimp [vdst, ρ]
    rw [← Real.rpow_mul (le_of_lt hp_dst)]
    have hmul : (1 / (1 + c)) * (1 + c) = 1 := by
      field_simp [ne_of_gt hρ_pos]
    rw [hmul, Real.rpow_one]
  rw [Real.div_rpow (le_of_lt hB_pos) (le_of_lt hvdst_pos),
    Real.div_rpow (le_of_lt hA_pos) (le_of_lt hvsrc_pos),
    hvdst_pow, hvsrc_pow] at hpow_lt
  have hcross : p_src * (B ^ ρ) < p_dst * (A ^ ρ) := by
    rw [div_lt_div_iff₀ hp_dst hp_src] at hpow_lt
    nlinarith
  have hA_pow :
      A ^ ρ = A * A ^ c := by
    dsimp [ρ]
    rw [Real.rpow_add hA_pos, Real.rpow_one]
  have hB_pow :
      B ^ ρ = B * B ^ c := by
    dsimp [ρ]
    rw [Real.rpow_add hB_pos, Real.rpow_one]
  have hA_c_pos : 0 < A ^ c := Real.rpow_pos_of_pos hA_pos c
  have htarget_cross :
      p_src * (B / A) ^ c * B < p_dst * A := by
    have hdiv := div_lt_div_of_pos_right hcross hA_c_pos
    rw [hA_pow, hB_pow] at hdiv
    rw [Real.div_rpow (le_of_lt hB_pos) (le_of_lt hA_pos)]
    field_simp [ne_of_gt hA_c_pos]
    nlinarith
  have htarget_div :
      (p_src * (B / A) ^ c) / A < p_dst / B := by
    rw [div_lt_div_iff₀ hA_pos hB_pos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using htarget_cross
  have hsrc_success :
      decayingBernoulliSuccess c d 1 (qsrc - 1) = c * (1 / A) := by
    have hpred : qsrc - 1 + 1 = qsrc :=
      Nat.sub_add_cancel (Nat.succ_le_of_lt hqsrc_pos)
    rw [decayingBernoulliSuccess_one c d hd]
    simp [A, hpred, one_div, add_comm]
  have hdst_success :
      decayingBernoulliSuccess c d 1 qdst = c * (1 / B) := by
    rw [decayingBernoulliSuccess_one c d hd]
  have hc_nonneg : 0 ≤ c := le_of_lt hc
  calc
    p_src *
        (decayingBernoulliSuccess c d 1 (qsrc - 1) *
          ((((qdst + 1 : ℕ) : ℝ) + d) /
            (((qsrc : ℕ) : ℝ) + d)) ^ c)
        = c * ((p_src * (B / A) ^ c) / A) := by
          rw [hsrc_success]
          simp [A, B]
          ring
    _ < c * (p_dst / B) :=
          mul_lt_mul_of_pos_left htarget_div hc
    _ = p_dst * decayingBernoulliSuccess c d 1 qdst := by
          rw [hdst_success]
          ring

theorem decayingBernoulliTopOne_alpha_one_scalar_exp_lt_of_shifted_scaled_exp_lt
    {p_src p_dst c d E : ℝ} {qsrc qdst : ℕ}
    (hp_src : 0 < p_src) (hp_dst : 0 < p_dst)
    (hc : 0 < c) (hd : 0 ≤ d) (hqsrc_pos : 0 < qsrc)
    (hscaled :
      (((((qdst + 1 : ℕ) : ℝ) + d) * Real.exp (E / (1 + c))) /
          p_dst ^ (1 / (1 + c))) <
        ((((qsrc : ℕ) : ℝ) + d) / p_src ^ (1 / (1 + c)))) :
    p_src *
        (decayingBernoulliSuccess c d 1 (qsrc - 1) *
          (((((qdst + 1 : ℕ) : ℝ) + d) /
            (((qsrc : ℕ) : ℝ) + d)) ^ c * Real.exp E)) <
      p_dst * decayingBernoulliSuccess c d 1 qdst := by
  let ρ : ℝ := 1 + c
  let A : ℝ := ((qsrc : ℕ) : ℝ) + d
  let B : ℝ := (((qdst + 1 : ℕ) : ℝ) + d)
  let η : ℝ := Real.exp (E / ρ)
  let Btilde : ℝ := B * η
  let vsrc : ℝ := p_src ^ (1 / ρ)
  let vdst : ℝ := p_dst ^ (1 / ρ)
  have hρ_pos : 0 < ρ := by dsimp [ρ]; linarith
  have hA_pos : 0 < A := by
    dsimp [A]
    positivity
  have hB_pos : 0 < B := by
    dsimp [B]
    positivity
  have hη_pos : 0 < η := by
    dsimp [η]
    positivity
  have hBtilde_pos : 0 < Btilde := by
    dsimp [Btilde]
    positivity
  have hvsrc_pos : 0 < vsrc := by
    dsimp [vsrc]
    exact Real.rpow_pos_of_pos hp_src (1 / ρ)
  have hvdst_pos : 0 < vdst := by
    dsimp [vdst]
    exact Real.rpow_pos_of_pos hp_dst (1 / ρ)
  have hscaled' : Btilde / vdst < A / vsrc := by
    simpa [A, B, Btilde, η, vsrc, vdst, ρ] using hscaled
  have hpow_lt :
      (Btilde / vdst) ^ ρ < (A / vsrc) ^ ρ :=
    Real.rpow_lt_rpow (le_of_lt (div_pos hBtilde_pos hvdst_pos)) hscaled' hρ_pos
  have hvsrc_pow : vsrc ^ ρ = p_src := by
    dsimp [vsrc, ρ]
    rw [← Real.rpow_mul (le_of_lt hp_src)]
    have hmul : (1 / (1 + c)) * (1 + c) = 1 := by
      field_simp [ne_of_gt hρ_pos]
    rw [hmul, Real.rpow_one]
  have hvdst_pow : vdst ^ ρ = p_dst := by
    dsimp [vdst, ρ]
    rw [← Real.rpow_mul (le_of_lt hp_dst)]
    have hmul : (1 / (1 + c)) * (1 + c) = 1 := by
      field_simp [ne_of_gt hρ_pos]
    rw [hmul, Real.rpow_one]
  rw [Real.div_rpow (le_of_lt hBtilde_pos) (le_of_lt hvdst_pos),
    Real.div_rpow (le_of_lt hA_pos) (le_of_lt hvsrc_pos),
    hvdst_pow, hvsrc_pow] at hpow_lt
  have hcross : p_src * (Btilde ^ ρ) < p_dst * (A ^ ρ) := by
    rw [div_lt_div_iff₀ hp_dst hp_src] at hpow_lt
    nlinarith
  have hA_pow :
      A ^ ρ = A * A ^ c := by
    dsimp [ρ]
    rw [Real.rpow_add hA_pos, Real.rpow_one]
  have hB_pow :
      B ^ ρ = B * B ^ c := by
    dsimp [ρ]
    rw [Real.rpow_add hB_pos, Real.rpow_one]
  have hη_pow : η ^ ρ = Real.exp E := by
    dsimp [η, ρ]
    rw [← Real.exp_mul]
    congr 1
    field_simp [ne_of_gt hρ_pos]
  have hBtilde_pow :
      Btilde ^ ρ = B ^ ρ * Real.exp E := by
    dsimp [Btilde]
    rw [Real.mul_rpow (le_of_lt hB_pos) (le_of_lt hη_pos), hη_pow]
  have hA_c_pos : 0 < A ^ c := Real.rpow_pos_of_pos hA_pos c
  have htarget_cross :
      p_src * ((B / A) ^ c * Real.exp E) * B < p_dst * A := by
    have hdiv := div_lt_div_of_pos_right hcross hA_c_pos
    rw [hA_pow, hBtilde_pow, hB_pow] at hdiv
    have hleft_eq :
        p_src * ((B / A) ^ c * Real.exp E) * B =
          p_src * (B * B ^ c * Real.exp E) / A ^ c := by
      rw [Real.div_rpow (le_of_lt hB_pos) (le_of_lt hA_pos)]
      field_simp [ne_of_gt hA_c_pos]
    have hright_eq :
        p_dst * A = p_dst * (A * A ^ c) / A ^ c := by
      field_simp [ne_of_gt hA_c_pos]
    rw [hleft_eq, hright_eq]
    exact hdiv
  have htarget_div :
      (p_src * ((B / A) ^ c * Real.exp E)) / A < p_dst / B := by
    rw [div_lt_div_iff₀ hA_pos hB_pos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using htarget_cross
  have hsrc_success :
      decayingBernoulliSuccess c d 1 (qsrc - 1) = c * (1 / A) := by
    have hpred : qsrc - 1 + 1 = qsrc :=
      Nat.sub_add_cancel (Nat.succ_le_of_lt hqsrc_pos)
    rw [decayingBernoulliSuccess_one c d hd]
    simp [A, hpred, one_div, add_comm]
  have hdst_success :
      decayingBernoulliSuccess c d 1 qdst = c * (1 / B) := by
    rw [decayingBernoulliSuccess_one c d hd]
  calc
    p_src *
        (decayingBernoulliSuccess c d 1 (qsrc - 1) *
          (((((qdst + 1 : ℕ) : ℝ) + d) /
            (((qsrc : ℕ) : ℝ) + d)) ^ c * Real.exp E))
        = c * ((p_src * ((B / A) ^ c * Real.exp E)) / A) := by
          rw [hsrc_success]
          simp [A, B]
          ring
    _ < c * (p_dst / B) :=
          mul_lt_mul_of_pos_left htarget_div hc
    _ = p_dst * decayingBernoulliSuccess c d 1 qdst := by
          rw [hdst_success]
          ring

theorem decayingBernoulliTopOne_alpha_one_marginalCore_lt_of_shifted_scaled_lt
    {p_src p_dst c d : ℝ} {qsrc qdst : ℕ}
    (hp_src : 0 < p_src) (hp_dst : 0 < p_dst)
    (hc : 0 < c) (hd : 0 ≤ d)
    (hfirst : decayingBernoulliSuccess c d 1 0 < 1)
    (hqsrc_pos : 0 < qsrc)
    (hqdst_le : qdst ≤ qsrc - 1)
    (hscaled :
      ((((qdst + 1 : ℕ) : ℝ) + d) / p_dst ^ (1 / (1 + c))) <
        ((((qsrc : ℕ) : ℝ) + d) / p_src ^ (1 / (1 + c)))) :
    p_src *
        (decayingBernoulliSuccess c d 1 (qsrc - 1) *
          ∏ i ∈ Finset.range (qsrc - 1),
            (1 - decayingBernoulliSuccess c d 1 i)) <
      p_dst *
        (decayingBernoulliSuccess c d 1 qdst *
          ∏ i ∈ Finset.range qdst,
            (1 - decayingBernoulliSuccess c d 1 i)) :=
    decayingBernoulliTopOne_alpha_one_weighted_marginalCore_lt_of_rpow_ratio_bound
      c d hc hd hfirst (le_of_lt hp_src) hqsrc_pos hqdst_le
      (decayingBernoulliTopOne_alpha_one_scalar_lt_of_shifted_scaled_lt
        hp_src hp_dst hc hd hqsrc_pos hscaled)

theorem decayingBernoulliTopOne_alpha_one_marginalCore_lt_of_reverse_shifted_scaled_exp_lt
    {p_src p_dst c d : ℝ} {qsrc qdst : ℕ}
    (hp_src : 0 < p_src) (hp_dst : 0 < p_dst)
    (hc : 0 < c) (hd : 0 ≤ d)
    (hfirst : decayingBernoulliSuccess c d 1 0 < 1)
    (hqsrc_pos : 0 < qsrc)
    (hqsrc_pred_le : qsrc - 1 ≤ qdst)
    (hlarge :
      ∀ i ∈ Finset.Ico (qsrc - 1) qdst,
        2 * c ≤ (((i + 1 : ℕ) : ℝ) + d))
    (hscaled :
      (((((qdst + 1 : ℕ) : ℝ) + d) *
            Real.exp
              ((∑ i ∈ Finset.Ico (qsrc - 1) qdst,
                (c / ((((i + 1 : ℕ) : ℝ) + d) - c) -
                  c * (2 / (2 * (((i + 1 : ℕ) : ℝ) + d) + 1)))) /
                (1 + c))) /
          p_dst ^ (1 / (1 + c))) <
        ((((qsrc : ℕ) : ℝ) + d) / p_src ^ (1 / (1 + c)))) :
    p_src *
        (decayingBernoulliSuccess c d 1 (qsrc - 1) *
          ∏ i ∈ Finset.range (qsrc - 1),
            (1 - decayingBernoulliSuccess c d 1 i)) <
      p_dst *
        (decayingBernoulliSuccess c d 1 qdst *
          ∏ i ∈ Finset.range qdst,
            (1 - decayingBernoulliSuccess c d 1 i)) :=
    decayingBernoulliTopOne_alpha_one_weighted_marginalCore_lt_of_reverse_rpow_exp_bound
      c d hc hd hfirst (le_of_lt hp_src) hqsrc_pos hqsrc_pred_le hlarge
      (decayingBernoulliTopOne_alpha_one_scalar_exp_lt_of_shifted_scaled_exp_lt
        hp_src hp_dst hc hd hqsrc_pos hscaled)

noncomputable def decayingBernoulliTopOneAlphaOneTargetWeight {T : ℕ}
    (likelihood : ItemType T → ℝ) (c : ℝ) (t : ItemType T) : ℝ := likelihood t ^ (1 / (1 + c))

theorem decayingBernoulliTopOneAlphaOneTargetWeight_pos
    {T : ℕ} {likelihood : ItemType T → ℝ} {c : ℝ}
    (hlike_pos : ∀ t, 0 < likelihood t) (t : ItemType T) :
    0 < decayingBernoulliTopOneAlphaOneTargetWeight likelihood c t := by
  unfold decayingBernoulliTopOneAlphaOneTargetWeight
  exact Real.rpow_pos_of_pos (hlike_pos t) (1 / (1 + c))

theorem alpha_one_reverse_correction_sum_le_scaled_gap_bound
    {T : ℕ} {likelihood : ItemType T → ℝ} {c d ε : ℝ}
    {N qsrc qdst : ℕ} {src : ItemType T}
    (hc : 0 < c) (hd : 0 ≤ d)
    (hlike_pos : ∀ t, 0 < likelihood t)
    (hD_pos : 0 < ε * (N : ℝ))
    (hqdst_leN : qdst ≤ N)
    (hlarge :
      ∀ i ∈ Finset.Ico (qsrc - 1) qdst,
        2 * c ≤ (((i + 1 : ℕ) : ℝ) + d))
    (hgap_src :
      ε * (N : ℝ) <
        (qsrc : ℝ) / decayingBernoulliTopOneAlphaOneTargetWeight likelihood c src) :
    (∑ i ∈ Finset.Ico (qsrc - 1) qdst,
      (c / ((((i + 1 : ℕ) : ℝ) + d) - c) -
        c * (2 / (2 * (((i + 1 : ℕ) : ℝ) + d) + 1)))) ≤
      (c * (1 + 2 * c)) * (N : ℝ) *
        (((∑ t : ItemType T,
            1 / decayingBernoulliTopOneAlphaOneTargetWeight likelihood c t) ^ 2) /
          ((ε * (N : ℝ)) ^ 2)) := by
  classical
  let weight : ItemType T → ℝ :=
    decayingBernoulliTopOneAlphaOneTargetWeight likelihood c
  let S : ℝ := ∑ t : ItemType T, 1 / weight t
  let D : ℝ := ε * (N : ℝ)
  let A : ℝ := (qsrc : ℝ) + d
  let K : ℝ := c * (1 + 2 * c)
  have hweight_pos : ∀ t, 0 < weight t := by
    intro t
    exact decayingBernoulliTopOneAlphaOneTargetWeight_pos hlike_pos t
  have hS_pos : 0 < S := by
    dsimp [S]
    exact Finset.sum_pos
      (fun t _ => one_div_pos.mpr (hweight_pos t))
      ⟨src, Finset.mem_univ src⟩
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    nlinarith
  have hqsrc_pos : 0 < qsrc := by
    have hqsrc_div_pos :
        0 < (qsrc : ℝ) / weight src := by
      simpa [weight] using lt_trans hD_pos hgap_src
    by_contra hnot
    have hzero : qsrc = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hzero] at hqsrc_div_pos
    simp at hqsrc_div_pos
  have hA_pos : 0 < A := by
    dsimp [A]
    have hqsrc_real_pos : (0 : ℝ) < qsrc := by exact_mod_cast hqsrc_pos
    linarith
  have hinv_le_sum :
      1 / weight src ≤ S := by
    dsimp [S]
    exact Finset.single_le_sum
      (fun t _ => div_nonneg zero_le_one (le_of_lt (hweight_pos t)))
      (Finset.mem_univ src)
  have hweight_lower : 1 / S ≤ weight src := by
    rw [div_le_iff₀ hS_pos]
    have hmul :
        (1 / weight src) * weight src ≤ S * weight src :=
      mul_le_mul_of_nonneg_right hinv_le_sum (le_of_lt (hweight_pos src))
    have hone :
        (1 / weight src) * weight src = 1 := by
      field_simp [ne_of_gt (hweight_pos src)]
    nlinarith
  have hD_weight_lt_qsrc :
      D * weight src < (qsrc : ℝ) := by
    have h := (lt_div_iff₀' (hweight_pos src)).mp hgap_src
    simpa [D, weight, mul_comm, mul_left_comm, mul_assoc] using h
  have hD_div_S_le_D_weight :
      D / S ≤ D * weight src := by
    simpa [div_eq_mul_inv, one_div] using
      mul_le_mul_of_nonneg_left hweight_lower (le_of_lt hD_pos)
  have hD_div_S_lt_A : D / S < A := by
    have hlt_qsrc : D / S < (qsrc : ℝ) :=
      lt_of_le_of_lt hD_div_S_le_D_weight hD_weight_lt_qsrc
    dsimp [A]
    linarith
  have hpred_succ : qsrc - 1 + 1 = qsrc :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt hqsrc_pos)
  have hD_div_S_pos : 0 < D / S := div_pos hD_pos hS_pos
  have hA_sq_lower : (D / S) ^ 2 ≤ A ^ 2 := by
    nlinarith
  have hinv_sq_le : 1 / A ^ 2 ≤ S ^ 2 / D ^ 2 := by
    have hleft_pos : 0 < (D / S) ^ 2 := sq_pos_of_pos hD_div_S_pos
    have hrecip :
        1 / A ^ 2 ≤ 1 / ((D / S) ^ 2) :=
      one_div_le_one_div_of_le hleft_pos hA_sq_lower
    have hrewrite : 1 / ((D / S) ^ 2) = S ^ 2 / D ^ 2 := by
      field_simp [ne_of_gt hD_pos, ne_of_gt hS_pos]
    simpa [one_div, hrewrite] using hrecip
  have hlen_le_N :
      (((qdst - (qsrc - 1) : ℕ) : ℝ)) ≤ (N : ℝ) := by
    exact_mod_cast le_trans (Nat.sub_le qdst (qsrc - 1)) hqdst_leN
  have htail_nonneg : 0 ≤ 1 / A ^ 2 := by positivity
  have hsum :=
    alpha_one_reverse_correction_sum_le_length_left
      c d hc hd hlarge
  have hlength_bound :
      K * ((qdst - (qsrc - 1) : ℕ) : ℝ) * (1 / A ^ 2) ≤
        K * (N : ℝ) * (1 / A ^ 2) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlen_le_N hK_nonneg) htail_nonneg
  have hgap_bound :
      K * (N : ℝ) * (1 / A ^ 2) ≤
        K * (N : ℝ) * (S ^ 2 / D ^ 2) :=
    mul_le_mul_of_nonneg_left hinv_sq_le
      (mul_nonneg hK_nonneg (Nat.cast_nonneg N))
  calc
    (∑ i ∈ Finset.Ico (qsrc - 1) qdst,
      (c / ((((i + 1 : ℕ) : ℝ) + d) - c) -
        c * (2 / (2 * (((i + 1 : ℕ) : ℝ) + d) + 1))))
        ≤ K * ((qdst - (qsrc - 1) : ℕ) : ℝ) * (1 / A ^ 2) := by
          simpa [K, A, hpred_succ] using hsum
    _ ≤ K * (N : ℝ) * (1 / A ^ 2) := hlength_bound
    _ ≤ K * (N : ℝ) * (S ^ 2 / D ^ 2) := hgap_bound
    _ =
      (c * (1 + 2 * c)) * (N : ℝ) *
        (((∑ t : ItemType T,
            1 / decayingBernoulliTopOneAlphaOneTargetWeight likelihood c t) ^ 2) /
          ((ε * (N : ℝ)) ^ 2)) := by
        dsimp [K, S, D, weight]

theorem decayingBernoulliTopOne_alpha_one_reverse_corrected_shift_lt_of_cube_growth
    {T : ℕ} {likelihood : ItemType T → ℝ} {c d ε : ℝ}
    {N qsrc qdst : ℕ} {src dst : ItemType T}
    (hc : 0 < c) (hd : 0 ≤ d)
    (hlike_pos : ∀ t, 0 < likelihood t)
    (hε_pos : 0 < ε) (hε_le_one : ε ≤ 1) (hN_pos : 0 < N)
    (hqdst_leN : qdst ≤ N)
    (hqsrc_pred_le : qsrc - 1 ≤ qdst)
    (hlarge :
      ∀ i ∈ Finset.Ico (qsrc - 1) qdst,
        2 * c ≤ (((i + 1 : ℕ) : ℝ) + d))
    (hgap :
      ε * (N : ℝ) <
        (qsrc : ℝ) / decayingBernoulliTopOneAlphaOneTargetWeight likelihood c src -
          (qdst : ℝ) / decayingBernoulliTopOneAlphaOneTargetWeight likelihood c dst)
    (hfixed :
      2 * ((1 + d) *
          ∑ t : ItemType T,
            1 / decayingBernoulliTopOneAlphaOneTargetWeight likelihood c t) <
        ε * (N : ℝ))
    (hsmall_arg :
      (c * (1 + 2 * c)) *
          (∑ t : ItemType T,
            1 / decayingBernoulliTopOneAlphaOneTargetWeight likelihood c t) ^ 2 /
          (1 + c) <
        ε ^ 3 * (N : ℝ))
    (hsmall_corr :
      2 *
          (((2 + d) * Real.exp 1 * (c * (1 + 2 * c)) *
              (∑ t : ItemType T,
                1 / decayingBernoulliTopOneAlphaOneTargetWeight likelihood c t) ^ 3) /
            (1 + c)) <
        ε ^ 3 * (N : ℝ)) :
    (1 + d +
        ((((qdst + 1 : ℕ) : ℝ) + d) *
          (Real.exp
            ((∑ i ∈ Finset.Ico (qsrc - 1) qdst,
                (c / ((((i + 1 : ℕ) : ℝ) + d) - c) -
                  c * (2 / (2 * (((i + 1 : ℕ) : ℝ) + d) + 1)))) /
              (1 + c)) - 1))) *
        ∑ t : ItemType T,
          1 / decayingBernoulliTopOneAlphaOneTargetWeight likelihood c t <
      ε * (N : ℝ) := by
  classical
  let weight : ItemType T → ℝ :=
    decayingBernoulliTopOneAlphaOneTargetWeight likelihood c
  let S : ℝ := ∑ t : ItemType T, 1 / weight t
  let D : ℝ := ε * (N : ℝ)
  let E : ℝ :=
    ∑ i ∈ Finset.Ico (qsrc - 1) qdst,
      (c / ((((i + 1 : ℕ) : ℝ) + d) - c) -
        c * (2 / (2 * (((i + 1 : ℕ) : ℝ) + d) + 1)))
  let B : ℝ := (((qdst + 1 : ℕ) : ℝ) + d)
  let ρ : ℝ := 1 + c
  let K : ℝ := c * (1 + 2 * c)
  let Ccorr : ℝ := ((2 + d) * Real.exp 1 * K * S ^ 3) / ρ
  have hweight_pos : ∀ t, 0 < weight t := by
    intro t
    exact decayingBernoulliTopOneAlphaOneTargetWeight_pos hlike_pos t
  have hS_pos : 0 < S := by
    dsimp [S]
    exact Finset.sum_pos
      (fun t _ => one_div_pos.mpr (hweight_pos t))
      ⟨src, Finset.mem_univ src⟩
  have hS_nonneg : 0 ≤ S := le_of_lt hS_pos
  have hD_pos : 0 < D := by
    dsimp [D]
    positivity
  have hN_real_pos : 0 < (N : ℝ) := by exact_mod_cast hN_pos
  have hρ_pos : 0 < ρ := by
    dsimp [ρ]
    linarith
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    nlinarith
  have hdst_div_nonneg :
      0 ≤ (qdst : ℝ) / weight dst :=
    div_nonneg (Nat.cast_nonneg _) (le_of_lt (hweight_pos dst))
  have hgap_src :
      ε * (N : ℝ) < (qsrc : ℝ) / weight src := by
    dsimp [weight] at hgap ⊢
    linarith
  have hE_nonneg : 0 ≤ E := by
    dsimp [E]
    exact alpha_one_reverse_correction_sum_nonneg c d hc hd hlarge
  have hE_le :
      E ≤ K * (N : ℝ) * (S ^ 2 / D ^ 2) := by
    dsimp [E, K, S, D, weight]
    exact
      alpha_one_reverse_correction_sum_le_scaled_gap_bound
        (T := T) (likelihood := likelihood) (c := c) (d := d)
        (ε := ε) (N := N) (qsrc := qsrc) (qdst := qdst)
        (src := src) hc hd hlike_pos
        (by simpa [D]) hqdst_leN hlarge
        (by simpa [weight] using hgap_src)
  have hε_sqN_pos : 0 < ε ^ 2 * (N : ℝ) := by positivity
  have hε_cube_le_sq : ε ^ 3 * (N : ℝ) ≤ ε ^ 2 * (N : ℝ) := by
    have hε_cube_le_sq_base : ε ^ 3 ≤ ε ^ 2 := by
      have hsq_nonneg : 0 ≤ ε ^ 2 := sq_nonneg ε
      nlinarith [mul_le_mul_of_nonneg_left hε_le_one hsq_nonneg]
    exact mul_le_mul_of_nonneg_right hε_cube_le_sq_base (Nat.cast_nonneg N)
  have harg_small :
      K * S ^ 2 / ρ < ε ^ 2 * (N : ℝ) :=
    lt_of_lt_of_le (by simpa [K, S, ρ, weight] using hsmall_arg)
      hε_cube_le_sq
  have hE_div_le_one : E / ρ ≤ 1 := by
    have hE_div_bound :
        E / ρ ≤ (K * S ^ 2 / ρ) / (ε ^ 2 * (N : ℝ)) := by
      have hrewrite :
          K * (N : ℝ) * (S ^ 2 / D ^ 2) / ρ =
            (K * S ^ 2 / ρ) / (ε ^ 2 * (N : ℝ)) := by
        dsimp [D]
        field_simp [ne_of_gt hε_pos, ne_of_gt hN_real_pos, ne_of_gt hρ_pos]
      calc
        E / ρ ≤ (K * (N : ℝ) * (S ^ 2 / D ^ 2)) / ρ :=
          div_le_div_of_nonneg_right hE_le (le_of_lt hρ_pos)
        _ = (K * S ^ 2 / ρ) / (ε ^ 2 * (N : ℝ)) := hrewrite
    have hdiv_lt_one :
        (K * S ^ 2 / ρ) / (ε ^ 2 * (N : ℝ)) < 1 := by
      rwa [div_lt_one hε_sqN_pos]
    exact le_of_lt (lt_of_le_of_lt hE_div_bound hdiv_lt_one)
  have hE_div_nonneg : 0 ≤ E / ρ :=
    div_nonneg hE_nonneg (le_of_lt hρ_pos)
  have hexp_sub_bound :
      Real.exp (E / ρ) - 1 ≤ Real.exp 1 * (E / ρ) :=
    exp_sub_one_le_exp_one_mul hE_div_nonneg hE_div_le_one
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hB_le : B ≤ (2 + d) * (N : ℝ) := by
    have hqdst_leN_real : (qdst : ℝ) ≤ (N : ℝ) := by exact_mod_cast hqdst_leN
    have hN_ge_one : (1 : ℝ) ≤ N := by exact_mod_cast hN_pos
    have hone_d_nonneg : 0 ≤ 1 + d := by linarith
    have htail_le : 1 + d ≤ (1 + d) * (N : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hN_ge_one hone_d_nonneg
      simpa using h
    dsimp [B]
    calc
      (((qdst + 1 : ℕ) : ℝ) + d) = (qdst : ℝ) + 1 + d := by norm_num
      _ ≤ (N : ℝ) + (1 + d) := by linarith
      _ ≤ (N : ℝ) + (1 + d) * (N : ℝ) := by linarith
      _ = (2 + d) * (N : ℝ) := by ring
  have hcorr_le :
      B * (Real.exp (E / ρ) - 1) * S ≤ Ccorr / ε ^ 2 := by
    calc
      B * (Real.exp (E / ρ) - 1) * S
          ≤ B * (Real.exp 1 * (E / ρ)) * S :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hexp_sub_bound hB_nonneg) hS_nonneg
      _ ≤ ((2 + d) * (N : ℝ)) *
            (Real.exp 1 *
              ((K * (N : ℝ) * (S ^ 2 / D ^ 2)) / ρ)) * S := by
            have hE_div_le :
                E / ρ ≤ (K * (N : ℝ) * (S ^ 2 / D ^ 2)) / ρ :=
              div_le_div_of_nonneg_right hE_le (le_of_lt hρ_pos)
            gcongr
      _ = Ccorr / ε ^ 2 := by
            dsimp [Ccorr, D]
            field_simp [ne_of_gt hε_pos, ne_of_gt hN_real_pos, ne_of_gt hρ_pos]
  have hfixed_half : (1 + d) * S < D / 2 := by
    dsimp [D, S, weight] at hfixed ⊢
    linarith
  have hcorr_half : Ccorr / ε ^ 2 < D / 2 := by
    have hsmall_corr' : 2 * Ccorr < ε ^ 3 * (N : ℝ) := by
      simpa [Ccorr, K, S, ρ, weight] using hsmall_corr
    dsimp [D]
    field_simp [ne_of_gt hε_pos]
    nlinarith
  have hshift_split :
      (1 + d + B * (Real.exp (E / ρ) - 1)) * S =
        (1 + d) * S + B * (Real.exp (E / ρ) - 1) * S := by
    ring
  calc
    (1 + d + B * (Real.exp (E / ρ) - 1)) * S
        = (1 + d) * S + B * (Real.exp (E / ρ) - 1) * S := hshift_split
    _ < D / 2 + D / 2 :=
        add_lt_add hfixed_half (lt_of_le_of_lt hcorr_le hcorr_half)
    _ = D := by ring
    _ = ε * (N : ℝ) := by rfl

theorem decayingBernoulliTopOne_alpha_one_shifted_scaled_lt_of_large_gap
    {T : ℕ} {likelihood : ItemType T → ℝ} {c d Δ : ℝ}
    (hd : 0 ≤ d) (hlike_pos : ∀ t, 0 < likelihood t)
    {src dst : ItemType T} {qsrc qdst : ℕ}
    (hshift :
      (1 + d) *
          ∑ t : ItemType T,
            1 / decayingBernoulliTopOneAlphaOneTargetWeight likelihood c t <
        Δ)
    (hgap :
      Δ <
        (qsrc : ℝ) / decayingBernoulliTopOneAlphaOneTargetWeight likelihood c src -
          (qdst : ℝ) / decayingBernoulliTopOneAlphaOneTargetWeight likelihood c dst) :
    ((((qdst + 1 : ℕ) : ℝ) + d) /
          decayingBernoulliTopOneAlphaOneTargetWeight likelihood c dst) <
      ((((qsrc : ℕ) : ℝ) + d) /
          decayingBernoulliTopOneAlphaOneTargetWeight likelihood c src) := by
  let weight : ItemType T → ℝ :=
    decayingBernoulliTopOneAlphaOneTargetWeight likelihood c
  have hsrc_pos : 0 < weight src :=
    decayingBernoulliTopOneAlphaOneTargetWeight_pos hlike_pos src
  have hdst_pos : 0 < weight dst :=
    decayingBernoulliTopOneAlphaOneTargetWeight_pos hlike_pos dst
  have hsum_bound :
      (1 + d) / weight dst ≤
        (1 + d) * ∑ t : ItemType T, 1 / weight t := by
    have hinv_le_sum :
        1 / weight dst ≤ ∑ t : ItemType T, 1 / weight t :=
      Finset.single_le_sum
        (fun t _ => div_nonneg zero_le_one
          (le_of_lt (decayingBernoulliTopOneAlphaOneTargetWeight_pos hlike_pos t)))
        (Finset.mem_univ dst)
    have hshift_nonneg : 0 ≤ 1 + d := by linarith
    simpa [div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left hinv_le_sum hshift_nonneg
  have hdst_shift_lt_src :
      (qdst : ℝ) / weight dst + (1 + d) / weight dst <
        (qsrc : ℝ) / weight src := by
    have hshift_lt : (1 + d) / weight dst < Δ :=
      lt_of_le_of_lt hsum_bound hshift
    linarith
  have hsrc_le_shifted :
      (qsrc : ℝ) / weight src ≤ (((qsrc : ℕ) : ℝ) + d) / weight src := by
    have hd_div_nonneg : 0 ≤ d / weight src :=
      div_nonneg hd (le_of_lt hsrc_pos)
    have hrewrite :
        (((qsrc : ℕ) : ℝ) + d) / weight src =
          (qsrc : ℝ) / weight src + d / weight src := by
      field_simp [ne_of_gt hsrc_pos]
    rw [hrewrite]
    linarith
  have hdst_rewrite :
      ((((qdst + 1 : ℕ) : ℝ) + d) / weight dst) =
        (qdst : ℝ) / weight dst + (1 + d) / weight dst := by
    field_simp [ne_of_gt hdst_pos]
    norm_num
    ring
  calc
    ((((qdst + 1 : ℕ) : ℝ) + d) / weight dst)
        = (qdst : ℝ) / weight dst + (1 + d) / weight dst := hdst_rewrite
    _ < (qsrc : ℝ) / weight src := hdst_shift_lt_src
    _ ≤ (((qsrc : ℕ) : ℝ) + d) / weight src := hsrc_le_shifted

theorem decayingBernoulliTopOne_alpha_one_corrected_shifted_scaled_lt_of_large_gap
    {T : ℕ} {likelihood : ItemType T → ℝ} {c d Δ E : ℝ}
    (hc : 0 < c) (hd : 0 ≤ d)
    (hlike_pos : ∀ t, 0 < likelihood t)
    {src dst : ItemType T} {qsrc qdst : ℕ}
    (hE_nonneg : 0 ≤ E)
    (hshift :
      (1 + d +
          ((((qdst + 1 : ℕ) : ℝ) + d) *
            (Real.exp (E / (1 + c)) - 1))) *
          ∑ t : ItemType T,
            1 / decayingBernoulliTopOneAlphaOneTargetWeight likelihood c t <
        Δ)
    (hgap :
      Δ <
        (qsrc : ℝ) / decayingBernoulliTopOneAlphaOneTargetWeight likelihood c src -
          (qdst : ℝ) / decayingBernoulliTopOneAlphaOneTargetWeight likelihood c dst) :
    (((((qdst + 1 : ℕ) : ℝ) + d) * Real.exp (E / (1 + c))) /
          decayingBernoulliTopOneAlphaOneTargetWeight likelihood c dst) <
      ((((qsrc : ℕ) : ℝ) + d) /
          decayingBernoulliTopOneAlphaOneTargetWeight likelihood c src) := by
  let weight : ItemType T → ℝ :=
    decayingBernoulliTopOneAlphaOneTargetWeight likelihood c
  let B : ℝ := (((qdst + 1 : ℕ) : ℝ) + d)
  let C : ℝ := 1 + d + B * (Real.exp (E / (1 + c)) - 1)
  have hsrc_pos : 0 < weight src :=
    decayingBernoulliTopOneAlphaOneTargetWeight_pos hlike_pos src
  have hdst_pos : 0 < weight dst :=
    decayingBernoulliTopOneAlphaOneTargetWeight_pos hlike_pos dst
  have hρ_pos : 0 < 1 + c := by linarith
  have hEdiv_nonneg : 0 ≤ E / (1 + c) :=
    div_nonneg hE_nonneg (le_of_lt hρ_pos)
  have hexp_shift_nonneg : 0 ≤ Real.exp (E / (1 + c)) - 1 := by
    have hone_le : 1 ≤ Real.exp (E / (1 + c)) :=
      Real.one_le_exp_iff.mpr hEdiv_nonneg
    linarith
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    nlinarith
  have hsum_bound :
      C / weight dst ≤ C * ∑ t : ItemType T, 1 / weight t := by
    have hinv_le_sum :
        1 / weight dst ≤ ∑ t : ItemType T, 1 / weight t :=
      Finset.single_le_sum
        (fun t _ => div_nonneg zero_le_one
          (le_of_lt (decayingBernoulliTopOneAlphaOneTargetWeight_pos hlike_pos t)))
        (Finset.mem_univ dst)
    simpa [div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left hinv_le_sum hC_nonneg
  have hdst_shift_lt_src :
      (qdst : ℝ) / weight dst + C / weight dst <
        (qsrc : ℝ) / weight src := by
    have hshift_lt : C / weight dst < Δ :=
      lt_of_le_of_lt hsum_bound (by simpa [C, B, weight] using hshift)
    linarith
  have hsrc_le_shifted :
      (qsrc : ℝ) / weight src ≤ (((qsrc : ℕ) : ℝ) + d) / weight src := by
    have hd_div_nonneg : 0 ≤ d / weight src :=
      div_nonneg hd (le_of_lt hsrc_pos)
    have hrewrite :
        (((qsrc : ℕ) : ℝ) + d) / weight src =
          (qsrc : ℝ) / weight src + d / weight src := by
      field_simp [ne_of_gt hsrc_pos]
    rw [hrewrite]
    linarith
  have hdst_rewrite :
      (B * Real.exp (E / (1 + c))) / weight dst =
        (qdst : ℝ) / weight dst + C / weight dst := by
    dsimp [B, C]
    field_simp [ne_of_gt hdst_pos]
    norm_num
    ring
  calc
    (((((qdst + 1 : ℕ) : ℝ) + d) * Real.exp (E / (1 + c))) / weight dst)
        = (B * Real.exp (E / (1 + c))) / weight dst := by
          simp [B]
    _ = (qdst : ℝ) / weight dst + C / weight dst := hdst_rewrite
    _ < (qsrc : ℝ) / weight src := hdst_shift_lt_src
    _ ≤ (((qsrc : ℕ) : ℝ) + d) / weight src := hsrc_le_shifted

theorem decayingBernoulliTopOne_alpha_one_rawOrdered_marginalCore_lt_of_large_gap
    {T : ℕ} {likelihood : ItemType T → ℝ} {c d Δ : ℝ}
    (hc : 0 < c) (hd : 0 ≤ d)
    (hfirst : decayingBernoulliSuccess c d 1 0 < 1)
    (hlike_pos : ∀ t, 0 < likelihood t)
    {src dst : ItemType T} {qsrc qdst : ℕ}
    (hqsrc_pos : 0 < qsrc)
    (hqdst_le : qdst ≤ qsrc - 1)
    (hshift :
      (1 + d) *
          ∑ t : ItemType T,
            1 / decayingBernoulliTopOneAlphaOneTargetWeight likelihood c t <
        Δ)
    (hgap :
      Δ <
        (qsrc : ℝ) / decayingBernoulliTopOneAlphaOneTargetWeight likelihood c src -
          (qdst : ℝ) / decayingBernoulliTopOneAlphaOneTargetWeight likelihood c dst) :
    likelihood src *
        (decayingBernoulliSuccess c d 1 (qsrc - 1) *
          ∏ i ∈ Finset.range (qsrc - 1),
            (1 - decayingBernoulliSuccess c d 1 i)) <
      likelihood dst *
        (decayingBernoulliSuccess c d 1 qdst *
          ∏ i ∈ Finset.range qdst,
            (1 - decayingBernoulliSuccess c d 1 i)) := by
  have hscaled :=
    decayingBernoulliTopOne_alpha_one_shifted_scaled_lt_of_large_gap
      (T := T) (likelihood := likelihood) (c := c) (d := d) (Δ := Δ)
      hd hlike_pos (src := src) (dst := dst) (qsrc := qsrc) (qdst := qdst)
      hshift hgap
  exact
    decayingBernoulliTopOne_alpha_one_marginalCore_lt_of_shifted_scaled_lt
      (hp_src := hlike_pos src) (hp_dst := hlike_pos dst)
      hc hd hfirst hqsrc_pos hqdst_le hscaled

theorem decayingBernoulliTopOne_alpha_one_reverse_marginalCore_lt_of_corrected_large_gap
    {T : ℕ} {likelihood : ItemType T → ℝ} {c d Δ E : ℝ}
    (hc : 0 < c) (hd : 0 ≤ d)
    (hfirst : decayingBernoulliSuccess c d 1 0 < 1)
    (hlike_pos : ∀ t, 0 < likelihood t)
    {src dst : ItemType T} {qsrc qdst : ℕ}
    (hqsrc_pos : 0 < qsrc)
    (hqsrc_pred_le : qsrc - 1 ≤ qdst)
    (hlarge :
      ∀ i ∈ Finset.Ico (qsrc - 1) qdst,
        2 * c ≤ (((i + 1 : ℕ) : ℝ) + d))
    (hE_nonneg : 0 ≤ E)
    (hE_eq :
      E =
        ∑ i ∈ Finset.Ico (qsrc - 1) qdst,
          (c / ((((i + 1 : ℕ) : ℝ) + d) - c) -
            c * (2 / (2 * (((i + 1 : ℕ) : ℝ) + d) + 1))))
    (hshift :
      (1 + d +
          ((((qdst + 1 : ℕ) : ℝ) + d) *
            (Real.exp (E / (1 + c)) - 1))) *
          ∑ t : ItemType T,
            1 / decayingBernoulliTopOneAlphaOneTargetWeight likelihood c t <
        Δ)
    (hgap :
      Δ <
        (qsrc : ℝ) / decayingBernoulliTopOneAlphaOneTargetWeight likelihood c src -
          (qdst : ℝ) / decayingBernoulliTopOneAlphaOneTargetWeight likelihood c dst) :
    likelihood src *
        (decayingBernoulliSuccess c d 1 (qsrc - 1) *
          ∏ i ∈ Finset.range (qsrc - 1),
            (1 - decayingBernoulliSuccess c d 1 i)) <
      likelihood dst *
        (decayingBernoulliSuccess c d 1 qdst *
          ∏ i ∈ Finset.range qdst,
            (1 - decayingBernoulliSuccess c d 1 i)) := by
  subst E
  have hscaled :=
    decayingBernoulliTopOne_alpha_one_corrected_shifted_scaled_lt_of_large_gap
      (T := T) (likelihood := likelihood) (c := c) (d := d) (Δ := Δ)
      hc hd hlike_pos (src := src) (dst := dst) (qsrc := qsrc) (qdst := qdst)
      hE_nonneg hshift hgap
  exact
    decayingBernoulliTopOne_alpha_one_marginalCore_lt_of_reverse_shifted_scaled_exp_lt
      (hp_src := hlike_pos src) (hp_dst := hlike_pos dst)
      hc hd hfirst hqsrc_pos hqsrc_pred_le hlarge hscaled

/--
Finite product-ratio bridge for the top-one decaying-Bernoulli marginal.

In the `0 < α < 1` regime, the remaining scalar task is to make the exponential
tail factor over `Ico qdst (qsrc - 1)` dominate the finite likelihood ratio.
This lemma converts that scalar exponential inequality into the actual
source-backward versus destination-forward marginal dominance.
-/
theorem decayingBernoulliTopOne_weighted_marginalCore_lt_of_Ico_exp_bound
    (c d α : ℝ) {wsrc wdst : ℝ} {qsrc qdst : ℕ}
    (hc : 0 < c) (hd : 0 ≤ d) (hα : 0 ≤ α)
    (hfirst : decayingBernoulliSuccess c d α 0 < 1)
    (hwsrc_nonneg : 0 ≤ wsrc)
    (hqdst_le : qdst ≤ qsrc - 1)
    (hscalar :
      wsrc *
          (decayingBernoulliSuccess c d α (qsrc - 1) *
            Real.exp
              (-(∑ i ∈ Finset.Ico qdst (qsrc - 1),
                decayingBernoulliSuccess c d α i))) <
        wdst * decayingBernoulliSuccess c d α qdst) :
    wsrc *
        (decayingBernoulliSuccess c d α (qsrc - 1) *
          ∏ i ∈ Finset.range (qsrc - 1),
            (1 - decayingBernoulliSuccess c d α i)) <
      wdst *
        (decayingBernoulliSuccess c d α qdst *
          ∏ i ∈ Finset.range qdst,
            (1 - decayingBernoulliSuccess c d α i)) :=
    rankBernoulliTopOne_weighted_marginalCore_lt_of_Ico_exp_bound
      (decayingBernoulliSuccess c d α)
      (decayingBernoulliSuccess_nonneg c d α (le_of_lt hc) hd)
      (decayingBernoulliSuccess_lt_one_of_first_lt_one
        c d α (le_of_lt hc) hd hα hfirst)
      hwsrc_nonneg hqdst_le hscalar

/--
Variant of `decayingBernoulliTopOne_weighted_marginalCore_lt_of_Ico_exp_bound`
that uses only a likelihood-weight exponential bound. Since the decaying
success sequence is antitone, `qdst ≤ qsrc - 1` lets the destination success
probability absorb the source success probability.
-/
theorem decayingBernoulliTopOne_weighted_marginalCore_lt_of_Ico_exp_weight_bound
    (c d α : ℝ) {wsrc wdst : ℝ} {qsrc qdst : ℕ}
    (hc : 0 < c) (hd : 0 ≤ d) (hα : 0 ≤ α)
    (hfirst : decayingBernoulliSuccess c d α 0 < 1)
    (hwsrc_nonneg : 0 ≤ wsrc) (hwdst_pos : 0 < wdst)
    (hqdst_le : qdst ≤ qsrc - 1)
    (hweight :
      wsrc *
          Real.exp
            (-(∑ i ∈ Finset.Ico qdst (qsrc - 1),
              decayingBernoulliSuccess c d α i)) <
        wdst) :
    wsrc *
        (decayingBernoulliSuccess c d α (qsrc - 1) *
          ∏ i ∈ Finset.range (qsrc - 1),
            (1 - decayingBernoulliSuccess c d α i)) <
      wdst *
        (decayingBernoulliSuccess c d α qdst *
          ∏ i ∈ Finset.range qdst,
            (1 - decayingBernoulliSuccess c d α i)) := by
  have hsuccess_src_pos :
      0 < decayingBernoulliSuccess c d α (qsrc - 1) :=
    decayingBernoulliSuccess_pos c d α hc hd (qsrc - 1)
  have hsuccess_le :
      decayingBernoulliSuccess c d α (qsrc - 1) ≤
        decayingBernoulliSuccess c d α qdst :=
    decayingBernoulliSuccess_antitone_of_le
      c d α (le_of_lt hc) hd hα hqdst_le
  have hscalar :
      wsrc *
          (decayingBernoulliSuccess c d α (qsrc - 1) *
            Real.exp
              (-(∑ i ∈ Finset.Ico qdst (qsrc - 1),
                decayingBernoulliSuccess c d α i))) <
        wdst * decayingBernoulliSuccess c d α qdst := by
    calc
      wsrc *
          (decayingBernoulliSuccess c d α (qsrc - 1) *
            Real.exp
              (-(∑ i ∈ Finset.Ico qdst (qsrc - 1),
                decayingBernoulliSuccess c d α i)))
          =
        decayingBernoulliSuccess c d α (qsrc - 1) *
          (wsrc *
            Real.exp
              (-(∑ i ∈ Finset.Ico qdst (qsrc - 1),
                decayingBernoulliSuccess c d α i))) := by
          ring
      _ <
        decayingBernoulliSuccess c d α (qsrc - 1) * wdst :=
          mul_lt_mul_of_pos_left hweight hsuccess_src_pos
      _ ≤ decayingBernoulliSuccess c d α qdst * wdst :=
          mul_le_mul_of_nonneg_right hsuccess_le (le_of_lt hwdst_pos)
      _ = wdst * decayingBernoulliSuccess c d α qdst := by ring
  exact
    decayingBernoulliTopOne_weighted_marginalCore_lt_of_Ico_exp_bound
      c d α hc hd hα hfirst hwsrc_nonneg hqdst_le hscalar

/--
Gap-length version of the exponential product-ratio bridge.

The interval sum in the survival-product ratio is bounded below by the interval
length times the right-end success probability. This is the finite inequality
that the `0 < α < 1` proof will combine with a sublinear-but-super-`N^α` gap
schedule.
-/
theorem decayingBernoulliTopOne_weighted_marginalCore_lt_of_gap_exp_bound
    (c d α : ℝ) {wsrc wdst : ℝ} {qsrc qdst : ℕ}
    (hc : 0 < c) (hd : 0 ≤ d) (hα : 0 ≤ α)
    (hfirst : decayingBernoulliSuccess c d α 0 < 1)
    (hwsrc_nonneg : 0 ≤ wsrc) (hwdst_pos : 0 < wdst)
    (hqdst_le : qdst ≤ qsrc - 1)
    (hweight :
      wsrc *
          Real.exp
            (-(((qsrc - 1 - qdst : ℕ) : ℝ) *
              decayingBernoulliSuccess c d α (qsrc - 1 - 1))) <
        wdst) :
    wsrc *
        (decayingBernoulliSuccess c d α (qsrc - 1) *
          ∏ i ∈ Finset.range (qsrc - 1),
            (1 - decayingBernoulliSuccess c d α i)) <
      wdst *
        (decayingBernoulliSuccess c d α qdst *
          ∏ i ∈ Finset.range qdst,
            (1 - decayingBernoulliSuccess c d α i)) := by
  have hsum_lower :
      ((qsrc - 1 - qdst : ℕ) : ℝ) *
          decayingBernoulliSuccess c d α (qsrc - 1 - 1) ≤
        ∑ i ∈ Finset.Ico qdst (qsrc - 1),
          decayingBernoulliSuccess c d α i :=
    decayingBernoulliSuccess_Ico_sum_lower_by_right
      c d α (le_of_lt hc) hd hα hqdst_le
  have hexp_le :
      Real.exp
          (-(∑ i ∈ Finset.Ico qdst (qsrc - 1),
            decayingBernoulliSuccess c d α i)) ≤
        Real.exp
          (-(((qsrc - 1 - qdst : ℕ) : ℝ) *
            decayingBernoulliSuccess c d α (qsrc - 1 - 1))) :=
    Real.exp_le_exp.mpr (by linarith)
  have hweight_Ico :
      wsrc *
          Real.exp
            (-(∑ i ∈ Finset.Ico qdst (qsrc - 1),
              decayingBernoulliSuccess c d α i)) <
        wdst :=
    lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left hexp_le hwsrc_nonneg) hweight
  exact
    decayingBernoulliTopOne_weighted_marginalCore_lt_of_Ico_exp_weight_bound
      c d α hc hd hα hfirst hwsrc_nonneg hwdst_pos hqdst_le hweight_Ico

/--
Logarithmic version of the finite gap bound. This is the form closest to the
paper proof: a sufficiently large product of gap length and right-end success
probability beats the finite log-likelihood ratio.
-/
theorem decayingBernoulliTopOne_weighted_marginalCore_lt_of_gap_log_bound
    (c d α : ℝ) {wsrc wdst : ℝ} {qsrc qdst : ℕ}
    (hc : 0 < c) (hd : 0 ≤ d) (hα : 0 ≤ α)
    (hfirst : decayingBernoulliSuccess c d α 0 < 1)
    (hwsrc_pos : 0 < wsrc) (hwdst_pos : 0 < wdst)
    (hqdst_le : qdst ≤ qsrc - 1)
    (hlog :
      Real.log (wsrc / wdst) <
        ((qsrc - 1 - qdst : ℕ) : ℝ) *
          decayingBernoulliSuccess c d α (qsrc - 1 - 1)) :
    wsrc *
        (decayingBernoulliSuccess c d α (qsrc - 1) *
          ∏ i ∈ Finset.range (qsrc - 1),
            (1 - decayingBernoulliSuccess c d α i)) <
      wdst *
        (decayingBernoulliSuccess c d α qdst *
          ∏ i ∈ Finset.range qdst,
            (1 - decayingBernoulliSuccess c d α i)) := by
  have hweight :
      wsrc *
          Real.exp
            (-(((qsrc - 1 - qdst : ℕ) : ℝ) *
              decayingBernoulliSuccess c d α (qsrc - 1 - 1))) <
        wdst :=
    mul_exp_neg_lt_of_log_div_lt hwsrc_pos hwdst_pos hlog
  exact
    decayingBernoulliTopOne_weighted_marginalCore_lt_of_gap_exp_bound
      c d α hc hd hα hfirst (le_of_lt hwsrc_pos) hwdst_pos hqdst_le hweight

/--
For positive decay `α`, a sufficiently late top-one marginal of any source type
is smaller than the first marginal of any destination type.

This is the top-one analogue of the eventual-interior step used in the
heterogeneous Bernoulli proof: high source counts eventually have negligible
last-item marginal, so an optimum cannot leave a positive-likelihood
destination at zero once the total size is large enough.
-/
theorem decayingBernoulliTopOne_pair_large_count_dominance_exists
    {T : ℕ} (likelihood : ItemType T → ℝ) (c d α : ℝ)
    (src dst : ItemType T)
    (hα : 0 < α) (hc : 0 < c) (hd : 0 ≤ d)
    (hfirst : decayingBernoulliSuccess c d α 0 ≤ 1)
    (hlike_src : 0 < likelihood src)
    (hlike_dst : 0 < likelihood dst) :
    ∃ K : ℕ, ∀ q, K < q →
      likelihood src *
          (decayingBernoulliSuccess c d α (q - 1) *
            ∏ i ∈ Finset.range (q - 1),
              (1 - decayingBernoulliSuccess c d α i)) <
        likelihood dst *
          (decayingBernoulliSuccess c d α 0 *
            ∏ i ∈ Finset.range 0,
              (1 - decayingBernoulliSuccess c d α i)) := by
  have htarget_pos :
      0 < likelihood dst * decayingBernoulliSuccess c d α 0 :=
    mul_pos hlike_dst
      (decayingBernoulliSuccess_pos c d α hc hd 0)
  have htend :
      Tendsto (fun q => likelihood src * decayingBernoulliSuccess c d α q)
        atTop (nhds 0) := by
    simpa using
      (decayingBernoulliSuccess_tendsto_zero c d α hα).const_mul
        (likelihood src)
  have hevent :
      ∀ᶠ q in atTop,
        likelihood src * decayingBernoulliSuccess c d α q <
          likelihood dst * decayingBernoulliSuccess c d α 0 :=
    htend.eventually (eventually_lt_nhds htarget_pos)
  obtain ⟨K, hK⟩ := eventually_atTop.1 hevent
  refine ⟨K, ?_⟩
  intro q hKq
  have hK_pred : K ≤ q - 1 := Nat.le_sub_one_of_lt hKq
  have hlate :
      likelihood src * decayingBernoulliSuccess c d α (q - 1) <
        likelihood dst * decayingBernoulliSuccess c d α 0 :=
    hK (q - 1) hK_pred
  have hprod_le_one :
      ∏ i ∈ Finset.range (q - 1), (1 - decayingBernoulliSuccess c d α i) ≤ 1 :=
    decayingBernoulliTopOne_survivalProduct_le_one
      c d α (le_of_lt hc) hd (le_of_lt hα) hfirst (q - 1)
  have hsuccess_nonneg : 0 ≤ decayingBernoulliSuccess c d α (q - 1) :=
    decayingBernoulliSuccess_nonneg c d α (le_of_lt hc) hd (q - 1)
  have hcore_le_success :
      decayingBernoulliSuccess c d α (q - 1) *
          ∏ i ∈ Finset.range (q - 1),
            (1 - decayingBernoulliSuccess c d α i) ≤
        decayingBernoulliSuccess c d α (q - 1) := by
    calc
      decayingBernoulliSuccess c d α (q - 1) *
          ∏ i ∈ Finset.range (q - 1),
            (1 - decayingBernoulliSuccess c d α i)
          ≤ decayingBernoulliSuccess c d α (q - 1) * 1 :=
            mul_le_mul_of_nonneg_left hprod_le_one hsuccess_nonneg
      _ = decayingBernoulliSuccess c d α (q - 1) := by ring
  have hleft_le :
      likelihood src *
          (decayingBernoulliSuccess c d α (q - 1) *
            ∏ i ∈ Finset.range (q - 1),
              (1 - decayingBernoulliSuccess c d α i)) ≤
        likelihood src * decayingBernoulliSuccess c d α (q - 1) :=
    mul_le_mul_of_nonneg_left hcore_le_success (le_of_lt hlike_src)
  calc
    likelihood src *
        (decayingBernoulliSuccess c d α (q - 1) *
          ∏ i ∈ Finset.range (q - 1),
            (1 - decayingBernoulliSuccess c d α i))
        ≤ likelihood src * decayingBernoulliSuccess c d α (q - 1) := hleft_le
    _ < likelihood dst * decayingBernoulliSuccess c d α 0 := hlate
    _ =
        likelihood dst *
          (decayingBernoulliSuccess c d α 0 *
            ∏ i ∈ Finset.range 0,
              (1 - decayingBernoulliSuccess c d α i)) := by simp

/--
Fixed-destination-count version of large-count marginal dominance.

For any fixed destination count `qdst`, a sufficiently late source marginal is
smaller than the destination's forward marginal at `qdst`.
-/
theorem decayingBernoulliTopOne_pair_large_count_dominance_exists_at_count
    {T : ℕ} (likelihood : ItemType T → ℝ) (c d α : ℝ)
    (src dst : ItemType T) (qdst : ℕ)
    (hα : 0 < α) (hc : 0 < c) (hd : 0 ≤ d)
    (hfirst : decayingBernoulliSuccess c d α 0 < 1)
    (hlike_src : 0 < likelihood src)
    (hlike_dst : 0 < likelihood dst) :
    ∃ K : ℕ, ∀ q, K < q →
      likelihood src *
          (decayingBernoulliSuccess c d α (q - 1) *
            ∏ i ∈ Finset.range (q - 1),
              (1 - decayingBernoulliSuccess c d α i)) <
        likelihood dst *
          (decayingBernoulliSuccess c d α qdst *
            ∏ i ∈ Finset.range qdst,
              (1 - decayingBernoulliSuccess c d α i)) := by
  have hdst_core_pos :
      0 < decayingBernoulliSuccess c d α qdst *
        ∏ i ∈ Finset.range qdst,
          (1 - decayingBernoulliSuccess c d α i) :=
    decayingBernoulliTopOne_marginalCore_pos
      c d α hc hd (le_of_lt hα) hfirst qdst
  have htarget_pos :
      0 < likelihood dst *
        (decayingBernoulliSuccess c d α qdst *
          ∏ i ∈ Finset.range qdst,
            (1 - decayingBernoulliSuccess c d α i)) :=
    mul_pos hlike_dst hdst_core_pos
  have htend :
      Tendsto (fun q => likelihood src * decayingBernoulliSuccess c d α q)
        atTop (nhds 0) := by
    simpa using
      (decayingBernoulliSuccess_tendsto_zero c d α hα).const_mul
        (likelihood src)
  have hevent :
      ∀ᶠ q in atTop,
        likelihood src * decayingBernoulliSuccess c d α q <
          likelihood dst *
            (decayingBernoulliSuccess c d α qdst *
              ∏ i ∈ Finset.range qdst,
                (1 - decayingBernoulliSuccess c d α i)) :=
    htend.eventually (eventually_lt_nhds htarget_pos)
  obtain ⟨K, hK⟩ := eventually_atTop.1 hevent
  refine ⟨K, ?_⟩
  intro q hKq
  have hK_pred : K ≤ q - 1 := Nat.le_sub_one_of_lt hKq
  have hlate :
      likelihood src * decayingBernoulliSuccess c d α (q - 1) <
        likelihood dst *
          (decayingBernoulliSuccess c d α qdst *
            ∏ i ∈ Finset.range qdst,
              (1 - decayingBernoulliSuccess c d α i)) :=
    hK (q - 1) hK_pred
  have hprod_le_one :
      ∏ i ∈ Finset.range (q - 1), (1 - decayingBernoulliSuccess c d α i) ≤ 1 :=
    decayingBernoulliTopOne_survivalProduct_le_one
      c d α (le_of_lt hc) hd (le_of_lt hα) (le_of_lt hfirst) (q - 1)
  have hsuccess_nonneg : 0 ≤ decayingBernoulliSuccess c d α (q - 1) :=
    decayingBernoulliSuccess_nonneg c d α (le_of_lt hc) hd (q - 1)
  have hcore_le_success :
      decayingBernoulliSuccess c d α (q - 1) *
          ∏ i ∈ Finset.range (q - 1),
            (1 - decayingBernoulliSuccess c d α i) ≤
        decayingBernoulliSuccess c d α (q - 1) := by
    calc
      decayingBernoulliSuccess c d α (q - 1) *
          ∏ i ∈ Finset.range (q - 1),
            (1 - decayingBernoulliSuccess c d α i)
          ≤ decayingBernoulliSuccess c d α (q - 1) * 1 :=
            mul_le_mul_of_nonneg_left hprod_le_one hsuccess_nonneg
      _ = decayingBernoulliSuccess c d α (q - 1) := by ring
  have hleft_le :
      likelihood src *
          (decayingBernoulliSuccess c d α (q - 1) *
            ∏ i ∈ Finset.range (q - 1),
              (1 - decayingBernoulliSuccess c d α i)) ≤
        likelihood src * decayingBernoulliSuccess c d α (q - 1) :=
    mul_le_mul_of_nonneg_left hcore_le_success (le_of_lt hlike_src)
  exact lt_of_le_of_lt hleft_le hlate

/-- Source Theorem 2 `S_{n,1}` count objective. -/
noncomputable def decayingBernoulliTopOneConsumptionModel {T : ℕ}
    (likelihood : ItemType T → ℝ) (c d α : ℝ) :
    ConsumptionModel T :=
  rankBernoulliTopOneConsumptionModel likelihood
    (decayingBernoulliSuccess c d α)

/-- Source Theorem 2 all-consumed count objective. -/
noncomputable def decayingBernoulliAllConsumedConsumptionModel {T : ℕ}
    (likelihood : ItemType T → ℝ) (c d α : ℝ) :
    ConsumptionModel T :=
  rankBernoulliAllConsumedConsumptionModel likelihood
    (decayingBernoulliSuccess c d α)

/--
Primitive positive top-one decaying-Bernoulli parameters imply eventual
interiority of finite optima: after a finite total-size threshold, every
positive-likelihood type receives at least one recommendation.
-/
noncomputable def
    decayingBernoulliTopOne_eventual_positive_counts_of_positive_parameters
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (c d α : ℝ)
    (hα : 0 < α) (hc : 0 < c) (hd : 0 ≤ d)
    (hfirst : decayingBernoulliSuccess c d α 0 ≤ 1)
    (hlike_pos : ∀ t, 0 < likelihood t) :
    ∃ threshold : ℕ,
      ∀ N (a : CountAllocation T), threshold ≤ N →
        (decayingBernoulliTopOneConsumptionModel likelihood c d α).IsOptimalAtTotal
          N a →
        ∀ t, 0 < a.count t := by
  classical
  let pairThreshold : ItemType T × ItemType T → ℕ := fun p =>
    Classical.choose
      (decayingBernoulliTopOne_pair_large_count_dominance_exists
        likelihood c d α p.1 p.2 hα hc hd hfirst
        (hlike_pos p.1) (hlike_pos p.2))
  let K : ℕ :=
    (Finset.univ : Finset (ItemType T × ItemType T)).sup pairThreshold
  refine ⟨T * K + 1, ?_⟩
  intro N a hlarge hopt dst
  by_contra hnot_pos
  have hdst_zero : a.count dst = 0 := Nat.eq_zero_of_not_pos hnot_pos
  have htotal_gt : T * K < AppliedModelingLib.Allocation.total a := by
    rw [hopt.1]
    exact Nat.lt_of_succ_le hlarge
  obtain ⟨src, hsrc_gt⟩ :=
    CountAllocation.exists_count_gt_of_card_mul_lt_total a htotal_gt
  have hcan : AppliedModelingLib.Allocation.CanMoveOne a src :=
    Nat.lt_of_le_of_lt (Nat.zero_le K) hsrc_gt
  have hne : src ≠ dst := by
    intro hsd
    subst dst
    rw [hdst_zero] at hsrc_gt
    exact Nat.not_lt_zero _ hsrc_gt
  have hfoc :=
    ConsumptionModel.weightedForwardMarginal_le_weightedBackwardMarginal_of_optimum
      (M := decayingBernoulliTopOneConsumptionModel likelihood c d α)
      N hopt hne hcan
  change
    (rankBernoulliTopOneConsumptionModel likelihood
        (decayingBernoulliSuccess c d α)).weightedForwardMarginal
        dst (a.count dst) ≤
      (rankBernoulliTopOneConsumptionModel likelihood
        (decayingBernoulliSuccess c d α)).weightedBackwardMarginal
        src (a.count src) at hfoc
  rw [rankBernoulliTopOneConsumptionModel_weightedForwardMarginal,
    rankBernoulliTopOneConsumptionModel_weightedBackwardMarginal
      (hq := hcan)] at hfoc
  rw [hdst_zero] at hfoc
  simp at hfoc
  have hp_le_K : pairThreshold (src, dst) ≤ K := by
    dsimp [K]
    exact Finset.le_sup (by simp : (src, dst) ∈
      (Finset.univ : Finset (ItemType T × ItemType T)))
  have hpq : pairThreshold (src, dst) < a.count src :=
    Nat.lt_of_le_of_lt hp_le_K hsrc_gt
  have hstrict :=
    (Classical.choose_spec
      (decayingBernoulliTopOne_pair_large_count_dominance_exists
        likelihood c d α src dst hα hc hd hfirst
        (hlike_pos src) (hlike_pos dst))) (a.count src) hpq
  have hstrict' :
      likelihood src *
          (decayingBernoulliSuccess c d α (a.count src - 1) *
            ∏ i ∈ Finset.range (a.count src - 1),
              (1 - decayingBernoulliSuccess c d α i)) <
        likelihood dst * decayingBernoulliSuccess c d α 0 := by
    simpa using hstrict
  exact (not_lt_of_ge hfoc) hstrict'

/--
Fixed-floor strengthening of eventual interiority.

For every finite floor, all positive-likelihood types eventually receive more
than that many recommendations in every finite optimum. This is the Lean
version of the first step in Lemma D.1's proof that all type counts diverge.
-/
noncomputable def
    decayingBernoulliTopOne_eventual_count_floor_of_positive_parameters
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (c d α : ℝ) (floor : ℕ)
    (hα : 0 < α) (hc : 0 < c) (hd : 0 ≤ d)
    (hfirst : decayingBernoulliSuccess c d α 0 < 1)
    (hlike_pos : ∀ t, 0 < likelihood t) :
    ∃ threshold : ℕ,
      ∀ N (a : CountAllocation T), threshold ≤ N →
        (decayingBernoulliTopOneConsumptionModel likelihood c d α).IsOptimalAtTotal
          N a →
        ∀ t, floor < a.count t := by
  classical
  let pairThreshold : ItemType T × ItemType T × Fin (floor + 1) → ℕ := fun p =>
    Classical.choose
      (decayingBernoulliTopOne_pair_large_count_dominance_exists_at_count
        likelihood c d α p.1 p.2.1 p.2.2 hα hc hd hfirst
        (hlike_pos p.1) (hlike_pos p.2.1))
  let K₀ : ℕ :=
    (Finset.univ : Finset (ItemType T × ItemType T × Fin (floor + 1))).sup
      pairThreshold
  let K : ℕ := max K₀ floor
  refine ⟨T * K + 1, ?_⟩
  intro N a hlarge hopt dst
  by_contra hnot_floor
  have hdst_le : a.count dst ≤ floor := le_of_not_gt hnot_floor
  let qdst : Fin (floor + 1) :=
    ⟨a.count dst, Nat.lt_succ_of_le hdst_le⟩
  have htotal_gt : T * K < AppliedModelingLib.Allocation.total a := by
    rw [hopt.1]
    exact Nat.lt_of_succ_le hlarge
  obtain ⟨src, hsrc_gt⟩ :=
    CountAllocation.exists_count_gt_of_card_mul_lt_total a htotal_gt
  have hcan : AppliedModelingLib.Allocation.CanMoveOne a src :=
    Nat.lt_of_le_of_lt (Nat.zero_le K) hsrc_gt
  have hfloor_le_K : floor ≤ K := by
    dsimp [K]
    exact le_max_right K₀ floor
  have hne : src ≠ dst := by
    intro hsd
    subst dst
    exact not_lt_of_ge (le_trans hdst_le hfloor_le_K) hsrc_gt
  have hfoc :=
    ConsumptionModel.weightedForwardMarginal_le_weightedBackwardMarginal_of_optimum
      (M := decayingBernoulliTopOneConsumptionModel likelihood c d α)
      N hopt hne hcan
  change
    (rankBernoulliTopOneConsumptionModel likelihood
        (decayingBernoulliSuccess c d α)).weightedForwardMarginal
        dst (a.count dst) ≤
      (rankBernoulliTopOneConsumptionModel likelihood
        (decayingBernoulliSuccess c d α)).weightedBackwardMarginal
        src (a.count src) at hfoc
  rw [rankBernoulliTopOneConsumptionModel_weightedForwardMarginal,
    rankBernoulliTopOneConsumptionModel_weightedBackwardMarginal
      (hq := hcan)] at hfoc
  have hp_le_K₀ : pairThreshold (src, dst, qdst) ≤ K₀ := by
    dsimp [K₀]
    exact Finset.le_sup (by simp : (src, dst, qdst) ∈
      (Finset.univ : Finset (ItemType T × ItemType T × Fin (floor + 1))))
  have hK₀_le_K : K₀ ≤ K := by
    dsimp [K]
    exact le_max_left K₀ floor
  have hpq : pairThreshold (src, dst, qdst) < a.count src :=
    Nat.lt_of_le_of_lt (le_trans hp_le_K₀ hK₀_le_K) hsrc_gt
  have hstrict :=
    (Classical.choose_spec
      (decayingBernoulliTopOne_pair_large_count_dominance_exists_at_count
        likelihood c d α src dst qdst hα hc hd hfirst
        (hlike_pos src) (hlike_pos dst))) (a.count src) hpq
  have hqdst_count : (qdst : ℕ) = a.count dst := rfl
  rw [← hqdst_count] at hfoc
  exact (not_lt_of_ge hfoc) hstrict

theorem decayingBernoulliTopOneConsumptionModel_alpha_zero_eq_bernoulli
    {T : ℕ} (likelihood : ItemType T → ℝ) (c d : ℝ) :
    decayingBernoulliTopOneConsumptionModel likelihood c d 0 =
      (BernoulliSatisfactionModel.mk likelihood (fun _ => c)).toConsumptionModel := by
  unfold decayingBernoulliTopOneConsumptionModel
    rankBernoulliTopOneConsumptionModel
    BernoulliSatisfactionModel.toConsumptionModel
  congr
  funext t q
  have hsuccess : decayingBernoulliSuccess c d 0 = fun _ => c := by
    funext i
    simp
  rw [hsuccess]
  exact rankBernoulliTopOneValue_const c q

/--
At `α = 0`, the all-consumed decaying-Bernoulli model is the linear
all-consumed model with common per-item value `c`.
-/
theorem decayingBernoulliAllConsumedConsumptionModel_alpha_zero_eq_linearized
    {T : ℕ} (likelihood : ItemType T → ℝ) (c d : ℝ) :
    decayingBernoulliAllConsumedConsumptionModel likelihood c d 0 =
      ConsumptionModel.linearized likelihood (fun _ => c) := by
  change
    ConsumptionModel.mk likelihood
        (fun _ q => rankBernoulliAllConsumedValue
          (decayingBernoulliSuccess c d 0) q) =
      ConsumptionModel.mk likelihood
        (ConsumptionModel.linearValueOfCount (fun _ => c))
  congr
  funext t q
  simp [rankBernoulliAllConsumedValue,
    ConsumptionModel.linearValueOfCount]

theorem decayingBernoulliTopOneConsumptionModel_has_nonnegative_marginals {T : ℕ}
    (likelihood : ItemType T → ℝ) (c d α : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hle_one : ∀ i, decayingBernoulliSuccess c d α i ≤ 1) :
    (decayingBernoulliTopOneConsumptionModel likelihood c d α).HasNonnegativeMarginals :=
   rankBernoulliTopOneConsumptionModel_has_nonnegative_marginals
    likelihood (decayingBernoulliSuccess c d α)
    (decayingBernoulliSuccess_nonneg c d α hc hd) hle_one

theorem decayingBernoulliTopOneConsumptionModel_has_nonnegative_marginals_of_first_le_one
    {T : ℕ}
    (likelihood : ItemType T → ℝ) (c d α : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hα : 0 ≤ α)
    (hfirst : decayingBernoulliSuccess c d α 0 ≤ 1) :
    (decayingBernoulliTopOneConsumptionModel likelihood c d α).HasNonnegativeMarginals :=
   decayingBernoulliTopOneConsumptionModel_has_nonnegative_marginals
    likelihood c d α hc hd
    (decayingBernoulliSuccess_le_one_of_first_le_one c d α hc hd hα hfirst)

theorem decayingBernoulliAllConsumedConsumptionModel_has_nonnegative_marginals {T : ℕ}
    (likelihood : ItemType T → ℝ) (c d α : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) :
    (decayingBernoulliAllConsumedConsumptionModel likelihood c d α).HasNonnegativeMarginals :=
   rankBernoulliAllConsumedConsumptionModel_has_nonnegative_marginals
    likelihood (decayingBernoulliSuccess c d α)
    (decayingBernoulliSuccess_nonneg c d α hc hd)

theorem decayingBernoulliTopOneConsumptionModel_has_diminishing_returns {T : ℕ}
    (likelihood : ItemType T → ℝ) (c d α : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hα : 0 ≤ α)
    (hle_one : ∀ i, decayingBernoulliSuccess c d α i ≤ 1) :
    (decayingBernoulliTopOneConsumptionModel likelihood c d α).HasDiminishingReturns :=
   rankBernoulliTopOneConsumptionModel_has_diminishing_returns
    likelihood (decayingBernoulliSuccess c d α)
    (decayingBernoulliSuccess_nonneg c d α hc hd) hle_one
    (decayingBernoulliSuccess_antitone c d α hc hd hα)

theorem decayingBernoulliTopOneConsumptionModel_has_diminishing_returns_of_first_le_one
    {T : ℕ}
    (likelihood : ItemType T → ℝ) (c d α : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hα : 0 ≤ α)
    (hfirst : decayingBernoulliSuccess c d α 0 ≤ 1) :
    (decayingBernoulliTopOneConsumptionModel likelihood c d α).HasDiminishingReturns :=
   decayingBernoulliTopOneConsumptionModel_has_diminishing_returns
    likelihood c d α hc hd hα
    (decayingBernoulliSuccess_le_one_of_first_le_one c d α hc hd hα hfirst)

theorem decayingBernoulliAllConsumedConsumptionModel_has_diminishing_returns {T : ℕ}
    (likelihood : ItemType T → ℝ) (c d α : ℝ)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hα : 0 ≤ α) :
    (decayingBernoulliAllConsumedConsumptionModel likelihood c d α).HasDiminishingReturns :=
   rankBernoulliAllConsumedConsumptionModel_has_diminishing_returns
    likelihood (decayingBernoulliSuccess c d α)
    (decayingBernoulliSuccess_antitone c d α hc hd hα)

/--
Certificate for Theorem 2 parts (i)-(iii), using the actual rank-decay
top-one Bernoulli objective from equation (137).
-/
structure DecayingBernoulliTopOneHomogeneityCertificate {T : ℕ}
    (likelihood : ItemType T → ℝ) (c d α : ℝ)
    (G : GammaHomogeneityProfile T) where
  alpha_nonneg : 0 ≤ α
  c_nonneg : 0 ≤ c
  d_nonneg : 0 ≤ d
  success_le_one : ∀ i, decayingBernoulliSuccess c d α i ≤ 1
  asymptotic_homogeneity :
    ConsumptionModel.AsymptoticHomogeneity
      (fun _ => decayingBernoulliTopOneConsumptionModel likelihood c d α) G

namespace DecayingBernoulliTopOneHomogeneityCertificate

theorem has_nonnegative_marginals {T : ℕ}
    {likelihood : ItemType T → ℝ} {c d α : ℝ}
    {G : GammaHomogeneityProfile T}
    (hcert : DecayingBernoulliTopOneHomogeneityCertificate likelihood c d α G) :
    (decayingBernoulliTopOneConsumptionModel likelihood c d α).HasNonnegativeMarginals :=
  decayingBernoulliTopOneConsumptionModel_has_nonnegative_marginals
    likelihood c d α hcert.c_nonneg hcert.d_nonneg hcert.success_le_one

theorem has_diminishing_returns {T : ℕ}
    {likelihood : ItemType T → ℝ} {c d α : ℝ}
    {G : GammaHomogeneityProfile T}
    (hcert : DecayingBernoulliTopOneHomogeneityCertificate likelihood c d α G) :
    (decayingBernoulliTopOneConsumptionModel likelihood c d α).HasDiminishingReturns :=
  decayingBernoulliTopOneConsumptionModel_has_diminishing_returns
    likelihood c d α hcert.c_nonneg hcert.d_nonneg hcert.alpha_nonneg
    hcert.success_le_one

end DecayingBernoulliTopOneHomogeneityCertificate

/--
Sublinear FOC certificate for Theorem 2's top-one decaying-Bernoulli branch.

The remaining analytic work in parts (i)-(iii) is to prove the
`large_gap_marginal_dominance` field from the relevant product asymptotics:
any scaled-count gap larger than `error N * N` makes the source's last-item
top-one marginal strictly smaller than the destination's next-item marginal.
The reusable FOC bridge then rules out such gaps in finite optima.
-/
structure DecayingBernoulliTopOneSublinearFOCCertificate
    {T : ℕ} [NeZero T] (likelihood : ItemType T → ℝ) (c d α : ℝ)
    (weight : ItemType T → ℝ) (G : GammaHomogeneityProfile T) where
  alpha_nonneg : 0 ≤ α
  c_nonneg : 0 ≤ c
  d_nonneg : 0 ≤ d
  success_le_one : ∀ i, decayingBernoulliSuccess c d α i ≤ 1
  weight_pos : ∀ t, 0 < weight t
  targetShare_eq :
    ∀ t, G.targetShare t = weight t / ∑ i : ItemType T, weight i
  error : ℕ → ℝ
  error_nonneg : ∀ N, 0 ≤ error N
  error_tends_to_zero : AppliedModelingLib.Math.TendsToZero error
  large_gap_marginal_dominance :
    ∀ N (a : CountAllocation T), 0 < N →
      (decayingBernoulliTopOneConsumptionModel likelihood c d α).IsOptimalAtTotal
        N a →
      ∀ src dst,
        error N * (N : ℝ) <
          (a.count src : ℝ) / weight src -
            (a.count dst : ℝ) / weight dst →
        likelihood src *
            (decayingBernoulliSuccess c d α (a.count src - 1) *
              ∏ i ∈ Finset.range (a.count src - 1),
                (1 - decayingBernoulliSuccess c d α i)) <
          likelihood dst *
            (decayingBernoulliSuccess c d α (a.count dst) *
              ∏ i ∈ Finset.range (a.count dst),
                (1 - decayingBernoulliSuccess c d α i))

namespace DecayingBernoulliTopOneSublinearFOCCertificate

noncomputable def toPairwiseScaledSublinearFOCCertificate
    {T : ℕ} [NeZero T] {likelihood : ItemType T → ℝ} {c d α : ℝ}
    {weight : ItemType T → ℝ} {G : GammaHomogeneityProfile T}
    (hcert :
      DecayingBernoulliTopOneSublinearFOCCertificate
        likelihood c d α weight G) :
    PairwiseScaledSublinearFOCCertificate
      (fun _ => decayingBernoulliTopOneConsumptionModel likelihood c d α)
      weight G where
  weight_pos := hcert.weight_pos
  targetShare_eq := hcert.targetShare_eq
  error := hcert.error
  error_nonneg := hcert.error_nonneg
  error_tends_to_zero := hcert.error_tends_to_zero
  large_gap_backward_lt_forward := by
    intro N a hN hopt src dst hgap
    have hC_nonneg : 0 ≤ hcert.error N * (N : ℝ) :=
      mul_nonneg (hcert.error_nonneg N) (Nat.cast_nonneg N)
    have hdiff_pos :
        0 <
          (a.count src : ℝ) / weight src -
            (a.count dst : ℝ) / weight dst :=
      lt_of_le_of_lt hC_nonneg hgap
    have hdst_nonneg :
        0 ≤ (a.count dst : ℝ) / weight dst :=
      div_nonneg (Nat.cast_nonneg _) (le_of_lt (hcert.weight_pos dst))
    have hsrc_div_pos : 0 < (a.count src : ℝ) / weight src := by
      linarith
    have hsrc_pos : 0 < a.count src := by
      by_contra hnot
      have hzero : a.count src = 0 := Nat.eq_zero_of_not_pos hnot
      rw [hzero] at hsrc_div_pos
      simp at hsrc_div_pos
    change
      (rankBernoulliTopOneConsumptionModel likelihood
          (decayingBernoulliSuccess c d α)).weightedBackwardMarginal
          src (a.count src) <
        (rankBernoulliTopOneConsumptionModel likelihood
          (decayingBernoulliSuccess c d α)).weightedForwardMarginal
          dst (a.count dst)
    rw [rankBernoulliTopOneConsumptionModel_weightedBackwardMarginal
        (hq := hsrc_pos),
      rankBernoulliTopOneConsumptionModel_weightedForwardMarginal]
    exact hcert.large_gap_marginal_dominance N a hN hopt src dst hgap

theorem asymptoticHomogeneity
    {T : ℕ} [NeZero T] {likelihood : ItemType T → ℝ} {c d α : ℝ}
    {weight : ItemType T → ℝ} {G : GammaHomogeneityProfile T}
    (hcert :
      DecayingBernoulliTopOneSublinearFOCCertificate
        likelihood c d α weight G) :
    ConsumptionModel.AsymptoticHomogeneity
      (fun _ => decayingBernoulliTopOneConsumptionModel likelihood c d α) G :=
  hcert.toPairwiseScaledSublinearFOCCertificate.asymptoticHomogeneity

noncomputable def toHomogeneityCertificate
    {T : ℕ} [NeZero T] {likelihood : ItemType T → ℝ} {c d α : ℝ}
    {weight : ItemType T → ℝ} {G : GammaHomogeneityProfile T}
    (hcert :
      DecayingBernoulliTopOneSublinearFOCCertificate
        likelihood c d α weight G) :
    DecayingBernoulliTopOneHomogeneityCertificate likelihood c d α G where
  alpha_nonneg := hcert.alpha_nonneg
  c_nonneg := hcert.c_nonneg
  d_nonneg := hcert.d_nonneg
  success_le_one := hcert.success_le_one
  asymptotic_homogeneity := hcert.asymptoticHomogeneity

end DecayingBernoulliTopOneSublinearFOCCertificate

/--
Eventual product-asymptotic certificate for Theorem 2's top-one
decaying-Bernoulli branches.

The analytic product work should prove `large_gap_marginal_dominance_after_floor`:
after a fixed count floor and eventually in the total size, every scaled-count
gap larger than `base_error N * N` makes the source backward marginal smaller
than the destination forward marginal. The finite wrapper below uses the
already-proved count-divergence theorem to supply the floor condition for
finite optima, and protects the finitely many small totals by making their
error large enough that the large-gap hypothesis is impossible.
-/
structure DecayingBernoulliTopOneEventualSublinearFOCCertificate
    {T : ℕ} [NeZero T] (likelihood : ItemType T → ℝ) (c d α : ℝ)
    (weight : ItemType T → ℝ) (G : GammaHomogeneityProfile T) where
  alpha_pos : 0 < α
  c_pos : 0 < c
  d_nonneg : 0 ≤ d
  success_first_lt_one : decayingBernoulliSuccess c d α 0 < 1
  likelihood_pos : ∀ t, 0 < likelihood t
  weight_pos : ∀ t, 0 < weight t
  targetShare_eq :
    ∀ t, G.targetShare t = weight t / ∑ i : ItemType T, weight i
  base_error : ℕ → ℝ
  base_error_nonneg : ∀ N, 0 ≤ base_error N
  base_error_tends_to_zero : AppliedModelingLib.Math.TendsToZero base_error
  floor : ℕ
  large_gap_marginal_dominance_after_floor :
    ∀ᶠ N in atTop,
      ∀ src dst qsrc qdst,
        qsrc ≤ N →
        qdst ≤ N →
        floor < qsrc →
        floor < qdst →
        base_error N * (N : ℝ) <
          (qsrc : ℝ) / weight src - (qdst : ℝ) / weight dst →
        likelihood src *
            (decayingBernoulliSuccess c d α (qsrc - 1) *
              ∏ i ∈ Finset.range (qsrc - 1),
                (1 - decayingBernoulliSuccess c d α i)) <
          likelihood dst *
            (decayingBernoulliSuccess c d α qdst *
              ∏ i ∈ Finset.range qdst,
                (1 - decayingBernoulliSuccess c d α i))

namespace DecayingBernoulliTopOneEventualSublinearFOCCertificate

noncomputable def toSublinearFOCCertificate
    {T : ℕ} [NeZero T] {likelihood : ItemType T → ℝ} {c d α : ℝ}
    {weight : ItemType T → ℝ} {G : GammaHomogeneityProfile T}
    (hcert :
      DecayingBernoulliTopOneEventualSublinearFOCCertificate
        likelihood c d α weight G) :
    DecayingBernoulliTopOneSublinearFOCCertificate
      likelihood c d α weight G := by
  classical
  let floorThreshold : ℕ :=
    Classical.choose
      (decayingBernoulliTopOne_eventual_count_floor_of_positive_parameters
        likelihood c d α hcert.floor hcert.alpha_pos hcert.c_pos
        hcert.d_nonneg hcert.success_first_lt_one hcert.likelihood_pos)
  have hfloorThreshold :
      ∀ N (a : CountAllocation T), floorThreshold ≤ N →
        (decayingBernoulliTopOneConsumptionModel likelihood c d α).IsOptimalAtTotal
          N a →
        ∀ t, hcert.floor < a.count t :=
    Classical.choose_spec
      (decayingBernoulliTopOne_eventual_count_floor_of_positive_parameters
        likelihood c d α hcert.floor hcert.alpha_pos hcert.c_pos
        hcert.d_nonneg hcert.success_first_lt_one hcert.likelihood_pos)
  let asymThreshold : ℕ :=
    Classical.choose
      (eventually_atTop.1 hcert.large_gap_marginal_dominance_after_floor)
  have hasymThreshold :
      ∀ N ≥ asymThreshold,
        ∀ src dst qsrc qdst,
          qsrc ≤ N →
          qdst ≤ N →
          hcert.floor < qsrc →
          hcert.floor < qdst →
          hcert.base_error N * (N : ℝ) <
            (qsrc : ℝ) / weight src - (qdst : ℝ) / weight dst →
          likelihood src *
              (decayingBernoulliSuccess c d α (qsrc - 1) *
                ∏ i ∈ Finset.range (qsrc - 1),
                  (1 - decayingBernoulliSuccess c d α i)) <
            likelihood dst *
              (decayingBernoulliSuccess c d α qdst *
                ∏ i ∈ Finset.range qdst,
                  (1 - decayingBernoulliSuccess c d α i)) :=
    Classical.choose_spec
      (eventually_atTop.1 hcert.large_gap_marginal_dominance_after_floor)
  let threshold : ℕ := max floorThreshold asymThreshold
  let smallGapBound : ℝ := (∑ t : ItemType T, 1 / weight t) + 1
  refine
    { alpha_nonneg := le_of_lt hcert.alpha_pos
      c_nonneg := le_of_lt hcert.c_pos
      d_nonneg := hcert.d_nonneg
      success_le_one := ?_
      weight_pos := hcert.weight_pos
      targetShare_eq := hcert.targetShare_eq
      error := fun N => if N < threshold then smallGapBound else hcert.base_error N
      error_nonneg := ?_
      error_tends_to_zero := ?_
      large_gap_marginal_dominance := ?_ }
  · exact
      decayingBernoulliSuccess_le_one_of_first_le_one
        c d α (le_of_lt hcert.c_pos) hcert.d_nonneg
        (le_of_lt hcert.alpha_pos) (le_of_lt hcert.success_first_lt_one)
  · intro N
    by_cases hN : N < threshold
    · have hsum_nonneg :
          0 ≤ ∑ t : ItemType T, 1 / weight t :=
        Finset.sum_nonneg
          (fun t _ => div_nonneg zero_le_one
            (le_of_lt (hcert.weight_pos t)))
      rw [if_pos hN]
      dsimp [smallGapBound]
      linarith
    · simp [hN, hcert.base_error_nonneg N]
  · exact tendsToZero_if_lt_const
      hcert.base_error_tends_to_zero threshold smallGapBound
  · intro N a hNpos hopt src dst hgap
    by_cases hsmall : N < threshold
    · exfalso
      have hgap_small :
          smallGapBound * (N : ℝ) <
            (a.count src : ℝ) / weight src -
              (a.count dst : ℝ) / weight dst := by
        simpa [hsmall] using hgap
      have hsrc_count_le_total :
          a.count src ≤ N := by
        have hle := AppliedModelingLib.Allocation.count_le_total a src
        rw [hopt.1] at hle
        exact hle
      have hsrc_count_le_total_real :
          (a.count src : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast hsrc_count_le_total
      have hdst_div_nonneg :
          0 ≤ (a.count dst : ℝ) / weight dst :=
        div_nonneg (Nat.cast_nonneg _)
          (le_of_lt (hcert.weight_pos dst))
      have hdiff_le_src_div :
          (a.count src : ℝ) / weight src -
              (a.count dst : ℝ) / weight dst ≤
            (a.count src : ℝ) / weight src := by
        linarith
      have hsrc_div_le_N_inv :
          (a.count src : ℝ) / weight src ≤
            (N : ℝ) * (1 / weight src) := by
        rw [div_eq_mul_inv, one_div]
        exact mul_le_mul_of_nonneg_right hsrc_count_le_total_real
          (inv_nonneg.mpr (le_of_lt (hcert.weight_pos src)))
      have hinv_le_sum :
          1 / weight src ≤ ∑ t : ItemType T, 1 / weight t :=
        Finset.single_le_sum
          (fun t _ => div_nonneg zero_le_one
            (le_of_lt (hcert.weight_pos t)))
          (Finset.mem_univ src)
      have hN_nonneg : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
      have hN_inv_le_sum :
          (N : ℝ) * (1 / weight src) ≤
            (N : ℝ) * ∑ t : ItemType T, 1 / weight t :=
        mul_le_mul_of_nonneg_left hinv_le_sum hN_nonneg
      have hdiff_le_sum :
          (a.count src : ℝ) / weight src -
              (a.count dst : ℝ) / weight dst ≤
            (N : ℝ) * ∑ t : ItemType T, 1 / weight t :=
        le_trans hdiff_le_src_div
          (le_trans hsrc_div_le_N_inv hN_inv_le_sum)
      have hNpos_real : 0 < (N : ℝ) := by
        exact_mod_cast hNpos
      have hsum_lt_small :
          (N : ℝ) * ∑ t : ItemType T, 1 / weight t <
            smallGapBound * (N : ℝ) := by
        have hsum_lt :
            (∑ t : ItemType T, 1 / weight t) < smallGapBound := by
          dsimp [smallGapBound]
          linarith
        calc
          (N : ℝ) * ∑ t : ItemType T, 1 / weight t
              < (N : ℝ) * smallGapBound :=
                mul_lt_mul_of_pos_left hsum_lt hNpos_real
          _ = smallGapBound * (N : ℝ) := by ring
      exact not_lt_of_ge (le_trans hdiff_le_sum (le_of_lt hsum_lt_small))
        hgap_small
    · have hthreshold_le_N : threshold ≤ N := le_of_not_gt hsmall
      have hfloorThreshold_le_threshold : floorThreshold ≤ threshold := by
        dsimp [threshold]
        exact le_max_left floorThreshold asymThreshold
      have hasymThreshold_le_threshold : asymThreshold ≤ threshold := by
        dsimp [threshold]
        exact le_max_right floorThreshold asymThreshold
      have hfloorThreshold_le_N : floorThreshold ≤ N :=
        le_trans hfloorThreshold_le_threshold hthreshold_le_N
      have hasymThreshold_le_N : asymThreshold ≤ N :=
        le_trans hasymThreshold_le_threshold hthreshold_le_N
      have hcounts_floor :
          ∀ t, hcert.floor < a.count t :=
        hfloorThreshold N a hfloorThreshold_le_N hopt
      have hdomN :=
        hasymThreshold N hasymThreshold_le_N
      have hsrc_count_le_N : a.count src ≤ N := by
        have hle := AppliedModelingLib.Allocation.count_le_total a src
        rw [hopt.1] at hle
        exact hle
      have hdst_count_le_N : a.count dst ≤ N := by
        have hle := AppliedModelingLib.Allocation.count_le_total a dst
        rw [hopt.1] at hle
        exact hle
      have hgap_base :
          hcert.base_error N * (N : ℝ) <
            (a.count src : ℝ) / weight src -
              (a.count dst : ℝ) / weight dst := by
        simpa [hsmall] using hgap
      exact hdomN src dst (a.count src) (a.count dst)
        hsrc_count_le_N hdst_count_le_N
        (hcounts_floor src) (hcounts_floor dst) hgap_base

theorem asymptoticHomogeneity
    {T : ℕ} [NeZero T] {likelihood : ItemType T → ℝ} {c d α : ℝ}
    {weight : ItemType T → ℝ} {G : GammaHomogeneityProfile T}
    (hcert :
      DecayingBernoulliTopOneEventualSublinearFOCCertificate
        likelihood c d α weight G) :
    ConsumptionModel.AsymptoticHomogeneity
      (fun _ => decayingBernoulliTopOneConsumptionModel likelihood c d α) G := hcert.toSublinearFOCCertificate.asymptoticHomogeneity

noncomputable def toHomogeneityCertificate
    {T : ℕ} [NeZero T] {likelihood : ItemType T → ℝ} {c d α : ℝ}
    {weight : ItemType T → ℝ} {G : GammaHomogeneityProfile T}
    (hcert :
      DecayingBernoulliTopOneEventualSublinearFOCCertificate
        likelihood c d α weight G) :
    DecayingBernoulliTopOneHomogeneityCertificate likelihood c d α G := hcert.toSublinearFOCCertificate.toHomogeneityCertificate

end DecayingBernoulliTopOneEventualSublinearFOCCertificate

noncomputable def decayingBernoulliTopOneLogRatioBound {T : ℕ}
    (likelihood : ItemType T → ℝ) : ℝ :=
  (∑ p : ItemType T × ItemType T,
    |Real.log (likelihood p.1 / likelihood p.2)|) + 1

theorem decayingBernoulliTopOne_log_likelihood_ratio_lt_bound
    {T : ℕ} (likelihood : ItemType T → ℝ)
    (src dst : ItemType T) :
    Real.log (likelihood src / likelihood dst) <
      decayingBernoulliTopOneLogRatioBound likelihood := by
  let x : ℝ := Real.log (likelihood src / likelihood dst)
  have hx_le_abs : x ≤ |x| := le_abs_self x
  have habs_le_sum :
      |x| ≤
        ∑ p : ItemType T × ItemType T,
          |Real.log (likelihood p.1 / likelihood p.2)| := by
    dsimp [x]
    exact Finset.single_le_sum
      (fun p _ => abs_nonneg (Real.log (likelihood p.1 / likelihood p.2)))
      (Finset.mem_univ (src, dst))
  have hsum_lt :
      (∑ p : ItemType T × ItemType T,
          |Real.log (likelihood p.1 / likelihood p.2)|) <
        decayingBernoulliTopOneLogRatioBound likelihood := by
    dsimp [decayingBernoulliTopOneLogRatioBound]
    linarith
  exact lt_of_le_of_lt (le_trans hx_le_abs habs_le_sum) hsum_lt

noncomputable def decayingBernoulliTopOneSubunitError
    (α : ℝ) (N : ℕ) : ℝ := (((N + 1 : ℕ) : ℝ)) ^ ((α - 1) / 2)

theorem decayingBernoulliTopOneSubunitError_nonneg
    (α : ℝ) (N : ℕ) :
    0 ≤ decayingBernoulliTopOneSubunitError α N := by
  unfold decayingBernoulliTopOneSubunitError
  positivity

theorem decayingBernoulliTopOneSubunitError_tends_to_zero
    {α : ℝ} (hα_lt_one : α < 1) :
    AppliedModelingLib.Math.TendsToZero
      (decayingBernoulliTopOneSubunitError α) := by
  have hβ : 0 < (1 - α) / 2 := by linarith
  have hpow :
      Tendsto
        (fun N : ℕ => (((N + 1 : ℕ) : ℝ)) ^ (-((1 - α) / 2)))
        atTop (nhds 0) :=
    AppliedModelingLib.Math.tendsto_nat_succ_cast_rpow_neg_nhds_zero hβ
  rw [AppliedModelingLib.Math.TendsToZero]
  refine Tendsto.congr' ?_ hpow
  filter_upwards with N
  unfold decayingBernoulliTopOneSubunitError
  congr 1
  ring

theorem decayingBernoulliTopOneSubunitError_mul_nat_lower
    (α : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    (1 / 2 : ℝ) * (((N + 1 : ℕ) : ℝ) ^ ((1 + α) / 2)) ≤
      decayingBernoulliTopOneSubunitError α N * (N : ℝ) := by
  unfold decayingBernoulliTopOneSubunitError
  have hbase_pos : 0 < (((N + 1 : ℕ) : ℝ)) := by positivity
  have hbase_div_le_N :
      (((N + 1 : ℕ) : ℝ)) / 2 ≤ (N : ℝ) := by
    have hN_real : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hbase_eq : (((N + 1 : ℕ) : ℝ)) = (N : ℝ) + 1 := by norm_num
    nlinarith
  have hpow_nonneg :
      0 ≤ (((N + 1 : ℕ) : ℝ) ^ ((α - 1) / 2)) :=
    Real.rpow_nonneg (le_of_lt hbase_pos) _
  calc
    (1 / 2 : ℝ) * (((N + 1 : ℕ) : ℝ) ^ ((1 + α) / 2))
        = ((((N + 1 : ℕ) : ℝ)) / 2) *
            (((N + 1 : ℕ) : ℝ) ^ ((α - 1) / 2)) := by
          rw [show (1 + α) / 2 = 1 + (α - 1) / 2 by ring]
          rw [Real.rpow_add hbase_pos, Real.rpow_one]
          ring
    _ ≤ (N : ℝ) * (((N + 1 : ℕ) : ℝ) ^ ((α - 1) / 2)) :=
          mul_le_mul_of_nonneg_right hbase_div_le_N hpow_nonneg
    _ = (((N + 1 : ℕ) : ℝ) ^ ((α - 1) / 2)) * (N : ℝ) := by
          ring

theorem decayingBernoulliSuccess_lower_by_scaled_power
    (c d α : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) (hα : 0 ≤ α) (N : ℕ) :
    (c * (1 + d) ^ (-α)) * (((N + 1 : ℕ) : ℝ) ^ (-α)) ≤
      decayingBernoulliSuccess c d α N := by
  unfold decayingBernoulliSuccess
  have hbase_pos : 0 < (((N + 1 : ℕ) : ℝ)) := by positivity
  have hbase_d_pos : 0 < (((N + 1 : ℕ) : ℝ) + d) := by positivity
  have hone_d_pos : 0 < 1 + d := by linarith
  have hbase_ge_one : (1 : ℝ) ≤ (((N + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
  have hbase_d_le :
      (((N + 1 : ℕ) : ℝ) + d) ≤ (1 + d) * (((N + 1 : ℕ) : ℝ)) := by
    nlinarith [mul_le_mul_of_nonneg_left hbase_ge_one hd]
  have hpow_le :
      ((1 + d) * (((N + 1 : ℕ) : ℝ))) ^ (-α) ≤
        (((N + 1 : ℕ) : ℝ) + d) ^ (-α) :=
    Real.rpow_le_rpow_of_nonpos hbase_d_pos hbase_d_le (neg_nonpos.mpr hα)
  have hmul_rpow :
      ((1 + d) * (((N + 1 : ℕ) : ℝ))) ^ (-α) =
        (1 + d) ^ (-α) * (((N + 1 : ℕ) : ℝ) ^ (-α)) := by
    rw [Real.mul_rpow (le_of_lt hone_d_pos) (le_of_lt hbase_pos)]
  calc
    (c * (1 + d) ^ (-α)) * (((N + 1 : ℕ) : ℝ) ^ (-α))
        = c * (((1 + d) * (((N + 1 : ℕ) : ℝ))) ^ (-α)) := by
          rw [hmul_rpow]
          ring
    _ ≤ c * ((((N + 1 : ℕ) : ℝ) + d) ^ (-α)) :=         mul_le_mul_of_nonneg_left hpow_le hc

theorem decayingBernoulliTopOneSubunitGrowth_tendsto_atTop
    {c d α : ℝ} (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hc : 0 < c) (hd : 0 ≤ d) :
    Tendsto
      (fun N : ℕ =>
        (decayingBernoulliTopOneSubunitError α N * (N : ℝ) - 1) *
          decayingBernoulliSuccess c d α N)
      atTop atTop := by
  let β : ℝ := (1 - α) / 2
  let γ : ℝ := (1 + α) / 2
  let K : ℝ := (c * (1 + d) ^ (-α)) / 4
  have hβ : 0 < β := by dsimp [β]; linarith
  have hγ : 0 < γ := by dsimp [γ]; linarith
  have hK : 0 < K := by
    have hone_d_pos : 0 < 1 + d := by linarith
    have hpow_pos : 0 < (1 + d) ^ (-α) :=
      Real.rpow_pos_of_pos hone_d_pos (-α)
    dsimp [K]
    positivity
  have hβpow :
      Tendsto (fun N : ℕ => (((N + 1 : ℕ) : ℝ) ^ β)) atTop atTop :=
    AppliedModelingLib.Math.tendsto_nat_succ_cast_rpow_atTop hβ
  have hKβpow :
      Tendsto (fun N : ℕ => K * (((N + 1 : ℕ) : ℝ) ^ β))
        atTop atTop :=
    Filter.Tendsto.const_mul_atTop hK hβpow
  have hγpow :
      Tendsto (fun N : ℕ => (((N + 1 : ℕ) : ℝ) ^ γ)) atTop atTop :=
    AppliedModelingLib.Math.tendsto_nat_succ_cast_rpow_atTop hγ
  have hhalfγpow :
      Tendsto
        (fun N : ℕ => (1 / 2 : ℝ) * (((N + 1 : ℕ) : ℝ) ^ γ))
        atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2) hγpow
  have herror_mul_atTop :
      Tendsto
        (fun N : ℕ => decayingBernoulliTopOneSubunitError α N * (N : ℝ))
        atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ hhalfγpow
    filter_upwards [eventually_ge_atTop 1] with N hN
    simpa [γ] using
      decayingBernoulliTopOneSubunitError_mul_nat_lower α (N := N) hN
  refine tendsto_atTop_mono' atTop ?_ hKβpow
  filter_upwards [eventually_ge_atTop 1,
    herror_mul_atTop.eventually_ge_atTop (2 : ℝ)] with N hN hlarge
  let base : ℝ := (((N + 1 : ℕ) : ℝ))
  let epsN : ℝ := decayingBernoulliTopOneSubunitError α N * (N : ℝ)
  have hbase_pos : 0 < base := by dsimp [base]; positivity
  have hsuccess_nonneg :
      0 ≤ decayingBernoulliSuccess c d α N :=
    decayingBernoulliSuccess_nonneg c d α (le_of_lt hc) hd N
  have hsuccess_lower :
      (c * (1 + d) ^ (-α)) * (base ^ (-α)) ≤
        decayingBernoulliSuccess c d α N := by
    simpa [base] using
      decayingBernoulliSuccess_lower_by_scaled_power
        c d α (le_of_lt hc) hd (le_of_lt hα_pos) N
  have heps_half_le :
      epsN / 2 ≤ epsN - 1 := by linarith
  have hsub_le :
      (epsN / 2) * decayingBernoulliSuccess c d α N ≤
        (epsN - 1) * decayingBernoulliSuccess c d α N :=
    mul_le_mul_of_nonneg_right heps_half_le hsuccess_nonneg
  have heps_lower :
      (1 / 2 : ℝ) * (base ^ γ) ≤ epsN := by
    simpa [base, epsN, γ] using
      decayingBernoulliTopOneSubunitError_mul_nat_lower α (N := N) hN
  have heps_half_lower :
      (1 / 4 : ℝ) * (base ^ γ) ≤ epsN / 2 := by
    linarith
  have hscaled_nonneg :
      0 ≤ (c * (1 + d) ^ (-α)) * (base ^ (-α)) := by
    have hone_d_pos : 0 < 1 + d := by linarith
    positivity
  have heps_half_nonneg : 0 ≤ epsN / 2 := by linarith
  have hprod_scaled_le :
      ((1 / 4 : ℝ) * (base ^ γ)) *
          ((c * (1 + d) ^ (-α)) * (base ^ (-α))) ≤
        (epsN / 2) * decayingBernoulliSuccess c d α N :=
    le_trans
      (mul_le_mul_of_nonneg_right heps_half_lower hscaled_nonneg)
      (mul_le_mul_of_nonneg_left hsuccess_lower heps_half_nonneg)
  have hpow_combine :
      base ^ γ * base ^ (-α) = base ^ β := by
    rw [← Real.rpow_add hbase_pos]
    congr 1
    dsimp [β, γ]
    ring
  have hleft_eq :
      ((1 / 4 : ℝ) * (base ^ γ)) *
          ((c * (1 + d) ^ (-α)) * (base ^ (-α))) =
        K * (base ^ β) := by
    calc
      ((1 / 4 : ℝ) * (base ^ γ)) *
          ((c * (1 + d) ^ (-α)) * (base ^ (-α)))
          = (c * (1 + d) ^ (-α) / 4) *
              (base ^ γ * base ^ (-α)) := by
            ring
      _ = (c * (1 + d) ^ (-α) / 4) * (base ^ β) := by
            rw [hpow_combine]
      _ = K * (base ^ β) := by
            dsimp [K]
  calc
    K * (((N + 1 : ℕ) : ℝ) ^ β)
        = K * (base ^ β) := by simp [base]
    _ =
      ((1 / 4 : ℝ) * (base ^ γ)) *
        ((c * (1 + d) ^ (-α)) * (base ^ (-α))) := hleft_eq.symm
    _ ≤ (epsN / 2) * decayingBernoulliSuccess c d α N := hprod_scaled_le
    _ ≤ (epsN - 1) * decayingBernoulliSuccess c d α N := hsub_le
    _ =
      (decayingBernoulliTopOneSubunitError α N * (N : ℝ) - 1) *
        decayingBernoulliSuccess c d α N := by
        simp [epsN]

theorem decayingBernoulliTopOneSubunitGrowth_eventually
    {c d α B : ℝ} (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hc : 0 < c) (hd : 0 ≤ d) :
    ∀ᶠ N in atTop,
      B <
        (decayingBernoulliTopOneSubunitError α N * (N : ℝ) - 1) *
          decayingBernoulliSuccess c d α N :=
  (decayingBernoulliTopOneSubunitGrowth_tendsto_atTop
    hα_pos hα_lt_one hc hd).eventually_gt_atTop B

noncomputable def decayingBernoulliTopOneInvSqrtError (N : ℕ) : ℝ := 1 / Real.sqrt (((N + 1 : ℕ) : ℝ))

theorem decayingBernoulliTopOneInvSqrtError_nonneg (N : ℕ) :
    0 ≤ decayingBernoulliTopOneInvSqrtError N := by
  unfold decayingBernoulliTopOneInvSqrtError
  positivity

theorem decayingBernoulliTopOneInvSqrtError_tends_to_zero :
    AppliedModelingLib.Math.TendsToZero decayingBernoulliTopOneInvSqrtError := by
  have hsqrt :
      Tendsto (fun N : ℕ => Real.sqrt (((N + 1 : ℕ) : ℝ))) atTop atTop :=
    AppliedModelingLib.Math.tendsto_sqrt_nat_succ_cast_atTop
  rw [AppliedModelingLib.Math.TendsToZero]
  refine Tendsto.congr' ?_ (Filter.Tendsto.const_div_atTop hsqrt (1 : ℝ))
  filter_upwards with N
  simp [decayingBernoulliTopOneInvSqrtError, one_div, Nat.cast_add]

theorem decayingBernoulliTopOneInvSqrtError_mul_nat_tendsto_atTop :
    Tendsto
      (fun N : ℕ => decayingBernoulliTopOneInvSqrtError N * (N : ℝ))
      atTop atTop := by
  have hsqrt :
      Tendsto (fun N : ℕ => Real.sqrt (((N + 1 : ℕ) : ℝ))) atTop atTop :=
    AppliedModelingLib.Math.tendsto_sqrt_nat_succ_cast_atTop
  have hhalf_sqrt :
      Tendsto
        (fun N : ℕ => (1 / 2 : ℝ) * Real.sqrt (((N + 1 : ℕ) : ℝ)))
        atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2) hsqrt
  refine tendsto_atTop_mono' atTop ?_ hhalf_sqrt
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN_real : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hbase_pos : 0 < (((N + 1 : ℕ) : ℝ)) := by positivity
  have hsqrt_pos : 0 < Real.sqrt (((N + 1 : ℕ) : ℝ)) :=
    Real.sqrt_pos.mpr hbase_pos
  have hbase_div_le_N :
      (((N + 1 : ℕ) : ℝ)) / 2 ≤ (N : ℝ) := by
    have hbase_eq : (((N + 1 : ℕ) : ℝ)) = (N : ℝ) + 1 := by norm_num
    nlinarith
  unfold decayingBernoulliTopOneInvSqrtError
  calc
    (1 / 2 : ℝ) * Real.sqrt (((N + 1 : ℕ) : ℝ))
        = (((N + 1 : ℕ) : ℝ) / 2) /
            Real.sqrt (((N + 1 : ℕ) : ℝ)) := by
          field_simp [ne_of_gt hsqrt_pos]
          exact Real.sq_sqrt (le_of_lt hbase_pos)
    _ ≤ (N : ℝ) / Real.sqrt (((N + 1 : ℕ) : ℝ)) :=
          div_le_div_of_nonneg_right hbase_div_le_N (le_of_lt hsqrt_pos)
    _ = (1 / Real.sqrt (((N + 1 : ℕ) : ℝ))) * (N : ℝ) := by
          ring

theorem decayingBernoulliTopOneInvSqrtError_mul_nat_eventually_gt
    (B : ℝ) :
    ∀ᶠ N in atTop,
      B < decayingBernoulliTopOneInvSqrtError N * (N : ℝ) :=
  decayingBernoulliTopOneInvSqrtError_mul_nat_tendsto_atTop.eventually_gt_atTop B

noncomputable def decayingBernoulliTopOneQuarterError (N : ℕ) : ℝ := (((N + 1 : ℕ) : ℝ)) ^ (-(1 / 4 : ℝ))

theorem decayingBernoulliTopOneQuarterError_nonneg (N : ℕ) :
    0 ≤ decayingBernoulliTopOneQuarterError N := by
  unfold decayingBernoulliTopOneQuarterError
  positivity

theorem decayingBernoulliTopOneQuarterError_pos (N : ℕ) :
    0 < decayingBernoulliTopOneQuarterError N := by
  unfold decayingBernoulliTopOneQuarterError
  positivity

theorem decayingBernoulliTopOneQuarterError_le_one (N : ℕ) :
    decayingBernoulliTopOneQuarterError N ≤ 1 := by
  unfold decayingBernoulliTopOneQuarterError
  have hbase_nat : 1 ≤ N + 1 := Nat.succ_le_succ (Nat.zero_le N)
  have hbase : (1 : ℝ) ≤ (((N + 1 : ℕ) : ℝ) : ℝ) := by exact_mod_cast hbase_nat
  exact Real.rpow_le_one_of_one_le_of_nonpos hbase (by norm_num)

theorem decayingBernoulliTopOneQuarterError_tends_to_zero :
    AppliedModelingLib.Math.TendsToZero decayingBernoulliTopOneQuarterError := by
  have hbase :
      Tendsto (fun N : ℕ => (((N + 1 : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hpow :
      Tendsto (fun N : ℕ =>
        (((N + 1 : ℕ) : ℝ)) ^ (-(1 / 4 : ℝ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp hbase
  rw [AppliedModelingLib.Math.TendsToZero]
  refine Tendsto.congr' ?_ hpow
  filter_upwards with N
  simp [decayingBernoulliTopOneQuarterError, Nat.cast_add]

theorem decayingBernoulliTopOneQuarterError_mul_nat_tendsto_atTop :
    Tendsto
      (fun N : ℕ => decayingBernoulliTopOneQuarterError N * (N : ℝ))
      atTop atTop := by
  have hbase :
      Tendsto (fun N : ℕ => (((N + 1 : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hpow :
      Tendsto (fun N : ℕ =>
        (((N + 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ))) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 4)).comp hbase
  have hhalf :
      Tendsto
        (fun N : ℕ => (1 / 2 : ℝ) *
          (((N + 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ)))
        atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2) hpow
  refine tendsto_atTop_mono' atTop ?_ hhalf
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hbase_pos : 0 < (((N + 1 : ℕ) : ℝ)) := by positivity
  have hbase_div_le_N :
      (((N + 1 : ℕ) : ℝ)) / 2 ≤ (N : ℝ) := by
    have hN_real : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hbase_eq : (((N + 1 : ℕ) : ℝ)) = (N : ℝ) + 1 := by norm_num
    nlinarith
  have hpow_nonneg :
      0 ≤ (((N + 1 : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))) :=
    Real.rpow_nonneg (le_of_lt hbase_pos) _
  unfold decayingBernoulliTopOneQuarterError
  calc
    (1 / 2 : ℝ) * (((N + 1 : ℕ) : ℝ) ^ (3 / 4 : ℝ))
        = ((((N + 1 : ℕ) : ℝ)) / 2) *
            (((N + 1 : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))) := by
          rw [show (3 / 4 : ℝ) = 1 + (-(1 / 4 : ℝ)) by norm_num]
          rw [Real.rpow_add hbase_pos, Real.rpow_one]
          ring
    _ ≤ (N : ℝ) * (((N + 1 : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))) :=
          mul_le_mul_of_nonneg_right hbase_div_le_N hpow_nonneg
    _ = (((N + 1 : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))) * (N : ℝ) := by
          ring

theorem decayingBernoulliTopOneQuarterError_mul_nat_eventually_gt
    (B : ℝ) :
    ∀ᶠ N in atTop,
      B < decayingBernoulliTopOneQuarterError N * (N : ℝ) :=
  decayingBernoulliTopOneQuarterError_mul_nat_tendsto_atTop.eventually_gt_atTop B

theorem decayingBernoulliTopOneQuarterError_cube_mul_nat_tendsto_atTop :
    Tendsto
      (fun N : ℕ => (decayingBernoulliTopOneQuarterError N) ^ 3 * (N : ℝ))
      atTop atTop := by
  have hbase :
      Tendsto (fun N : ℕ => (((N + 1 : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hpow :
      Tendsto (fun N : ℕ =>
        (((N + 1 : ℕ) : ℝ) ^ (1 / 4 : ℝ))) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp hbase
  have hhalf :
      Tendsto
        (fun N : ℕ => (1 / 2 : ℝ) *
          (((N + 1 : ℕ) : ℝ) ^ (1 / 4 : ℝ)))
        atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2) hpow
  refine tendsto_atTop_mono' atTop ?_ hhalf
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hbase_pos : 0 < (((N + 1 : ℕ) : ℝ)) := by positivity
  have hbase_div_le_N :
      (((N + 1 : ℕ) : ℝ)) / 2 ≤ (N : ℝ) := by
    have hN_real : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hbase_eq : (((N + 1 : ℕ) : ℝ)) = (N : ℝ) + 1 := by norm_num
    nlinarith
  have hpow_nonneg :
      0 ≤ (((N + 1 : ℕ) : ℝ) ^ (-(3 / 4 : ℝ))) :=
    Real.rpow_nonneg (le_of_lt hbase_pos) _
  unfold decayingBernoulliTopOneQuarterError
  have hcube :
      ((((N + 1 : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))) ^ 3) =
        (((N + 1 : ℕ) : ℝ) ^ (-(3 / 4 : ℝ))) := by
    rw [← Real.rpow_mul_natCast (le_of_lt hbase_pos) (-(1 / 4 : ℝ)) 3]
    norm_num
  rw [hcube]
  calc
    (1 / 2 : ℝ) * (((N + 1 : ℕ) : ℝ) ^ (1 / 4 : ℝ))
        = ((((N + 1 : ℕ) : ℝ)) / 2) *
            (((N + 1 : ℕ) : ℝ) ^ (-(3 / 4 : ℝ))) := by
          rw [show (1 / 4 : ℝ) = 1 + (-(3 / 4 : ℝ)) by norm_num]
          rw [Real.rpow_add hbase_pos, Real.rpow_one]
          ring
    _ ≤ (N : ℝ) * (((N + 1 : ℕ) : ℝ) ^ (-(3 / 4 : ℝ))) :=
          mul_le_mul_of_nonneg_right hbase_div_le_N hpow_nonneg
    _ = (((N + 1 : ℕ) : ℝ) ^ (-(3 / 4 : ℝ))) * (N : ℝ) := by
          ring

theorem decayingBernoulliTopOneQuarterError_cube_mul_nat_eventually_gt
    (B : ℝ) :
    ∀ᶠ N in atTop,
      B < (decayingBernoulliTopOneQuarterError N) ^ 3 * (N : ℝ) :=
  decayingBernoulliTopOneQuarterError_cube_mul_nat_tendsto_atTop.eventually_gt_atTop B

/--
`α = 1` growth certificate for the top-one decaying-Bernoulli branch.

The finite α=1 product work has two scalar obligations. In raw count order,
`ε_N N` must dominate the fixed shifted-count term. In the reverse raw order,
the explicit correction sum must still be small enough that the corrected
shifted-count inequality follows from the same scaled-count gap.
-/
structure DecayingBernoulliTopOneAlphaOneGrowthCertificate
    {T : ℕ} [NeZero T] (likelihood : ItemType T → ℝ) (c d : ℝ) where
  c_pos : 0 < c
  d_nonneg : 0 ≤ d
  success_first_lt_one : decayingBernoulliSuccess c d 1 0 < 1
  likelihood_pos : ∀ t, 0 < likelihood t
  error : ℕ → ℝ
  error_nonneg : ∀ N, 0 ≤ error N
  error_tends_to_zero : AppliedModelingLib.Math.TendsToZero error
  floor : ℕ
  floor_large : 2 * c - d ≤ (floor : ℝ)
  raw_shift_growth :
    ∀ᶠ N in atTop,
      (1 + d) *
          ∑ t : ItemType T,
            1 / decayingBernoulliTopOneAlphaOneTargetWeight likelihood c t <
        error N * (N : ℝ)
  reverse_shift_growth :
    ∀ᶠ N in atTop,
      ∀ src dst qsrc qdst,
        qsrc ≤ N →
        qdst ≤ N →
        floor < qsrc →
        floor < qdst →
        qsrc - 1 ≤ qdst →
        error N * (N : ℝ) <
          (qsrc : ℝ) / decayingBernoulliTopOneAlphaOneTargetWeight likelihood c src -
            (qdst : ℝ) / decayingBernoulliTopOneAlphaOneTargetWeight likelihood c dst →
        (1 + d +
            ((((qdst + 1 : ℕ) : ℝ) + d) *
              (Real.exp
                ((∑ i ∈ Finset.Ico (qsrc - 1) qdst,
                    (c / ((((i + 1 : ℕ) : ℝ) + d) - c) -
                      c * (2 / (2 * (((i + 1 : ℕ) : ℝ) + d) + 1)))) /
                  (1 + c)) - 1))) *
            ∑ t : ItemType T,
              1 / decayingBernoulliTopOneAlphaOneTargetWeight likelihood c t <
          error N * (N : ℝ)

namespace DecayingBernoulliTopOneAlphaOneGrowthCertificate

noncomputable def of_quarter_error
    {T : ℕ} [NeZero T] (likelihood : ItemType T → ℝ) {c d : ℝ}
    (hc : 0 < c) (hd : 0 ≤ d)
    (hfirst : decayingBernoulliSuccess c d 1 0 < 1)
    (hlike_pos : ∀ t, 0 < likelihood t) :
    DecayingBernoulliTopOneAlphaOneGrowthCertificate likelihood c d := by
  classical
  refine
    { c_pos := hc
      d_nonneg := hd
      success_first_lt_one := hfirst
      likelihood_pos := hlike_pos
      error := decayingBernoulliTopOneQuarterError
      error_nonneg := decayingBernoulliTopOneQuarterError_nonneg
      error_tends_to_zero := decayingBernoulliTopOneQuarterError_tends_to_zero
      floor := Nat.ceil (2 * c - d)
      floor_large := ?_
      raw_shift_growth := ?_
      reverse_shift_growth := ?_ }
  · exact Nat.le_ceil (2 * c - d)
  · exact
      decayingBernoulliTopOneQuarterError_mul_nat_eventually_gt
        ((1 + d) *
          ∑ t : ItemType T,
            1 / decayingBernoulliTopOneAlphaOneTargetWeight likelihood c t)
  · let S : ℝ :=
        ∑ t : ItemType T,
          1 / decayingBernoulliTopOneAlphaOneTargetWeight likelihood c t
    let ρ : ℝ := 1 + c
    let K : ℝ := c * (1 + 2 * c)
    let Ccorr : ℝ := ((2 + d) * Real.exp 1 * K * S ^ 3) / ρ
    filter_upwards
      [eventually_ge_atTop 1,
        decayingBernoulliTopOneQuarterError_mul_nat_eventually_gt
          (2 * ((1 + d) * S)),
        decayingBernoulliTopOneQuarterError_cube_mul_nat_eventually_gt
          (K * S ^ 2 / ρ),
        decayingBernoulliTopOneQuarterError_cube_mul_nat_eventually_gt
          (2 * Ccorr)] with
      N hN_ge_one hfixed hsmall_arg hsmall_corr
    intro src dst qsrc qdst _hqsrc_leN hqdst_leN hqsrc_floor _hqdst_floor
      hqsrc_pred_le hgap
    have hN_pos : 0 < N := Nat.lt_of_lt_of_le Nat.zero_lt_one hN_ge_one
    have hlarge :
        ∀ i ∈ Finset.Ico (qsrc - 1) qdst,
          2 * c ≤ (((i + 1 : ℕ) : ℝ) + d) := by
      intro i hi
      exact alpha_one_reverse_large_of_left_floor
        hd (Nat.le_ceil (2 * c - d)) hqsrc_floor hi
    exact
      decayingBernoulliTopOne_alpha_one_reverse_corrected_shift_lt_of_cube_growth
        (T := T) (likelihood := likelihood) (c := c) (d := d)
        (ε := decayingBernoulliTopOneQuarterError N)
        (N := N) (qsrc := qsrc) (qdst := qdst) (src := src) (dst := dst)
        hc hd hlike_pos
        (decayingBernoulliTopOneQuarterError_pos N)
        (decayingBernoulliTopOneQuarterError_le_one N)
        hN_pos hqdst_leN hqsrc_pred_le hlarge hgap
        (by simpa [S] using hfixed)
        (by simpa [S, ρ, K] using hsmall_arg)
        (by simpa [S, ρ, K, Ccorr] using hsmall_corr)

noncomputable def toEventualSublinearFOCCertificate
    {T : ℕ} [NeZero T] {likelihood : ItemType T → ℝ} {c d : ℝ}
    (hcert :
      DecayingBernoulliTopOneAlphaOneGrowthCertificate likelihood c d) :
    DecayingBernoulliTopOneEventualSublinearFOCCertificate likelihood c d 1
      (decayingBernoulliTopOneAlphaOneTargetWeight likelihood c)
      (gammaLikelihoodProfile likelihood (1 / (1 + c))) := by
  classical
  refine
    { alpha_pos := by norm_num
      c_pos := hcert.c_pos
      d_nonneg := hcert.d_nonneg
      success_first_lt_one := hcert.success_first_lt_one
      likelihood_pos := hcert.likelihood_pos
      weight_pos := ?_
      targetShare_eq := ?_
      base_error := hcert.error
      base_error_nonneg := hcert.error_nonneg
      base_error_tends_to_zero := hcert.error_tends_to_zero
      floor := hcert.floor
      large_gap_marginal_dominance_after_floor := ?_ }
  · intro t
    exact decayingBernoulliTopOneAlphaOneTargetWeight_pos
      hcert.likelihood_pos t
  · intro t
    have hnorm_pos :
        0 < (gammaLikelihoodProfile likelihood (1 / (1 + c))).normalizer := by
      unfold GammaHomogeneityProfile.normalizer gammaLikelihoodProfile
      exact Finset.sum_pos
        (fun i _ =>
          decayingBernoulliTopOneAlphaOneTargetWeight_pos hcert.likelihood_pos i)
        Finset.univ_nonempty
    rw [GammaHomogeneityProfile.targetShare_eq_div_of_normalizer_ne_zero
      (G := gammaLikelihoodProfile likelihood (1 / (1 + c))) (t := t)
      (ne_of_gt hnorm_pos)]
    rfl
  · filter_upwards [hcert.raw_shift_growth, hcert.reverse_shift_growth] with
      N hraw hreverse
    intro src dst qsrc qdst hqsrc_leN hqdst_leN hqsrc_floor hqdst_floor hgap
    have hqsrc_pos : 0 < qsrc :=
      Nat.lt_of_le_of_lt (Nat.zero_le hcert.floor) hqsrc_floor
    by_cases hraw_order : qdst ≤ qsrc - 1
    · exact
        decayingBernoulliTopOne_alpha_one_rawOrdered_marginalCore_lt_of_large_gap
          (T := T) (likelihood := likelihood) (c := c) (d := d)
          (Δ := hcert.error N * (N : ℝ))
          hcert.c_pos hcert.d_nonneg hcert.success_first_lt_one
          hcert.likelihood_pos (src := src) (dst := dst)
          (qsrc := qsrc) (qdst := qdst) hqsrc_pos hraw_order hraw hgap
    · have hreverse_order : qsrc - 1 ≤ qdst :=
        le_of_lt (Nat.lt_of_not_ge hraw_order)
      have hlarge :
          ∀ i ∈ Finset.Ico (qsrc - 1) qdst,
            2 * c ≤ (((i + 1 : ℕ) : ℝ) + d) := by
        intro i hi
        exact alpha_one_reverse_large_of_left_floor
          hcert.d_nonneg hcert.floor_large hqsrc_floor hi
      have hE_nonneg :
          0 ≤
            ∑ i ∈ Finset.Ico (qsrc - 1) qdst,
              (c / ((((i + 1 : ℕ) : ℝ) + d) - c) -
                c * (2 / (2 * (((i + 1 : ℕ) : ℝ) + d) + 1))) :=
        alpha_one_reverse_correction_sum_nonneg
          c d hcert.c_pos hcert.d_nonneg hlarge
      exact
        decayingBernoulliTopOne_alpha_one_reverse_marginalCore_lt_of_corrected_large_gap
          (T := T) (likelihood := likelihood) (c := c) (d := d)
          (Δ := hcert.error N * (N : ℝ))
          (E :=
            ∑ i ∈ Finset.Ico (qsrc - 1) qdst,
              (c / ((((i + 1 : ℕ) : ℝ) + d) - c) -
                c * (2 / (2 * (((i + 1 : ℕ) : ℝ) + d) + 1))))
          hcert.c_pos hcert.d_nonneg hcert.success_first_lt_one
          hcert.likelihood_pos (src := src) (dst := dst)
          (qsrc := qsrc) (qdst := qdst) hqsrc_pos hreverse_order hlarge
          hE_nonneg rfl
          (hreverse src dst qsrc qdst hqsrc_leN hqdst_leN
            hqsrc_floor hqdst_floor hreverse_order hgap)
          hgap

theorem asymptoticHomogeneity
    {T : ℕ} [NeZero T] {likelihood : ItemType T → ℝ} {c d : ℝ}
    (hcert :
      DecayingBernoulliTopOneAlphaOneGrowthCertificate likelihood c d) :
    ConsumptionModel.AsymptoticHomogeneity
      (fun _ => decayingBernoulliTopOneConsumptionModel likelihood c d 1)
      (gammaLikelihoodProfile likelihood (1 / (1 + c))) := hcert.toEventualSublinearFOCCertificate.asymptoticHomogeneity

end DecayingBernoulliTopOneAlphaOneGrowthCertificate

noncomputable def decayingBernoulliTopOneSuperunitTargetWeight {T : ℕ}
    (likelihood : ItemType T → ℝ) (α : ℝ) (t : ItemType T) : ℝ := likelihood t ^ (1 / α)

theorem decayingBernoulliTopOneSuperunitTargetWeight_pos
    {T : ℕ} {likelihood : ItemType T → ℝ} {α : ℝ}
    (hlike_pos : ∀ t, 0 < likelihood t) (t : ItemType T) :
    0 < decayingBernoulliTopOneSuperunitTargetWeight likelihood α t := by
  unfold decayingBernoulliTopOneSuperunitTargetWeight
  exact Real.rpow_pos_of_pos (hlike_pos t) (1 / α)

theorem decayingBernoulliTopOne_superunit_reverse_correction_sum_le_scaled_gap_bound
    {T : ℕ} {likelihood : ItemType T → ℝ} {c d α ε : ℝ}
    {N qsrc qdst : ℕ} {src : ItemType T}
    (hc : 0 < c) (hd : 0 ≤ d) (hα_pos : 0 < α)
    (hlike_pos : ∀ t, 0 < likelihood t)
    (hD_pos : 0 < ε * (N : ℝ))
    (hqdst_leN : qdst ≤ N)
    (hgap_src :
      ε * (N : ℝ) <
        (qsrc : ℝ) / decayingBernoulliTopOneSuperunitTargetWeight likelihood α src) :
    2 * ∑ i ∈ Finset.Ico (qsrc - 1) qdst,
          decayingBernoulliSuccess c d α i ≤
      (2 * c *
          ∑ t : ItemType T,
            (decayingBernoulliTopOneSuperunitTargetWeight likelihood α t) ^ (-α)) *
        (N : ℝ) * (ε * (N : ℝ)) ^ (-α) := by
  classical
  let weight : ItemType T → ℝ :=
    decayingBernoulliTopOneSuperunitTargetWeight likelihood α
  let P : ℝ := ∑ t : ItemType T, (weight t) ^ (-α)
  let D : ℝ := ε * (N : ℝ)
  let A : ℝ := (qsrc : ℝ) + d
  have hweight_pos : ∀ t, 0 < weight t := by
    intro t
    exact decayingBernoulliTopOneSuperunitTargetWeight_pos hlike_pos t
  have hqsrc_pos : 0 < qsrc := by
    have hqsrc_div_pos :
        0 < (qsrc : ℝ) / weight src := by
      simpa [weight] using lt_trans hD_pos hgap_src
    by_contra hnot
    have hzero : qsrc = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hzero] at hqsrc_div_pos
    simp at hqsrc_div_pos
  have hA_pos : 0 < A := by
    dsimp [A]
    have hqsrc_real_pos : (0 : ℝ) < qsrc := by exact_mod_cast hqsrc_pos
    linarith
  have hD_weight_lt_qsrc :
      D * weight src < (qsrc : ℝ) := by
    have h := (lt_div_iff₀' (hweight_pos src)).mp hgap_src
    simpa [D, weight, mul_comm, mul_left_comm, mul_assoc] using h
  have hD_weight_lt_A : D * weight src < A := by
    dsimp [A]
    linarith
  have hD_weight_pos : 0 < D * weight src :=
    mul_pos hD_pos (hweight_pos src)
  have hpow_le :
      A ^ (-α) ≤ (D * weight src) ^ (-α) :=
    Real.rpow_le_rpow_of_nonpos hD_weight_pos (le_of_lt hD_weight_lt_A)
      (neg_nonpos.mpr (le_of_lt hα_pos))
  have hmul_rpow :
      (D * weight src) ^ (-α) = D ^ (-α) * (weight src) ^ (-α) := by
    rw [Real.mul_rpow (le_of_lt hD_pos) (le_of_lt (hweight_pos src))]
  have hterm_nonneg :
      ∀ t, 0 ≤ (weight t) ^ (-α) := by
    intro t
    exact Real.rpow_nonneg (le_of_lt (hweight_pos t)) _
  have hsrc_weight_pow_le_P :
      (weight src) ^ (-α) ≤ P := by
    dsimp [P]
    exact Finset.single_le_sum
      (fun t _ => hterm_nonneg t) (Finset.mem_univ src)
  have hD_pow_nonneg : 0 ≤ D ^ (-α) :=
    Real.rpow_nonneg (le_of_lt hD_pos) _
  have hsuccess_left_le :
      decayingBernoulliSuccess c d α (qsrc - 1) ≤ c * D ^ (-α) * P := by
    have hsuccess_eq :
        decayingBernoulliSuccess c d α (qsrc - 1) = c * A ^ (-α) := by
      unfold decayingBernoulliSuccess
      dsimp [A]
      rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hqsrc_pos)]
    rw [hsuccess_eq]
    calc
      c * A ^ (-α) ≤ c * ((D * weight src) ^ (-α)) :=
        mul_le_mul_of_nonneg_left hpow_le (le_of_lt hc)
      _ = c * (D ^ (-α) * (weight src) ^ (-α)) := by rw [hmul_rpow]
      _ ≤ c * (D ^ (-α) * P) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsrc_weight_pow_le_P hD_pow_nonneg)
          (le_of_lt hc)
      _ = c * D ^ (-α) * P := by ring
  have hsum_upper :
      ∑ i ∈ Finset.Ico (qsrc - 1) qdst,
          decayingBernoulliSuccess c d α i ≤
        ((qdst - (qsrc - 1) : ℕ) : ℝ) *
          decayingBernoulliSuccess c d α (qsrc - 1) :=
    decayingBernoulliSuccess_Ico_sum_upper_by_left
      c d α (le_of_lt hc) hd (le_of_lt hα_pos)
  have hlen_le_N :
      ((qdst - (qsrc - 1) : ℕ) : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast le_trans (Nat.sub_le qdst (qsrc - 1)) hqdst_leN
  have hsuccess_nonneg :
      0 ≤ decayingBernoulliSuccess c d α (qsrc - 1) :=
    decayingBernoulliSuccess_nonneg c d α (le_of_lt hc) hd (qsrc - 1)
  have hlength_success_le :
      ((qdst - (qsrc - 1) : ℕ) : ℝ) *
          decayingBernoulliSuccess c d α (qsrc - 1) ≤
        (N : ℝ) * (c * D ^ (-α) * P) :=
    le_trans
      (mul_le_mul_of_nonneg_right hlen_le_N hsuccess_nonneg)
      (mul_le_mul_of_nonneg_left hsuccess_left_le (Nat.cast_nonneg N))
  calc
    2 * ∑ i ∈ Finset.Ico (qsrc - 1) qdst,
          decayingBernoulliSuccess c d α i
        ≤ 2 * (((qdst - (qsrc - 1) : ℕ) : ℝ) *
          decayingBernoulliSuccess c d α (qsrc - 1)) :=
        mul_le_mul_of_nonneg_left hsum_upper (by norm_num)
    _ ≤ 2 * ((N : ℝ) * (c * D ^ (-α) * P)) :=
        mul_le_mul_of_nonneg_left hlength_success_le (by norm_num)
    _ =
      (2 * c *
          ∑ t : ItemType T,
            (decayingBernoulliTopOneSuperunitTargetWeight likelihood α t) ^ (-α)) *
        (N : ℝ) * (ε * (N : ℝ)) ^ (-α) := by
        dsimp [P, D, weight]
        ring

theorem decayingBernoulliTopOne_superunit_shifted_scaled_lt_of_large_gap
    {T : ℕ} {likelihood : ItemType T → ℝ} {d α Δ : ℝ}
    (hd : 0 ≤ d) (hlike_pos : ∀ t, 0 < likelihood t)
    {src dst : ItemType T} {qsrc qdst : ℕ}
    (hshift :
      (1 + d) *
          ∑ t : ItemType T,
            1 / decayingBernoulliTopOneSuperunitTargetWeight likelihood α t <
        Δ)
    (hgap :
      Δ <
        (qsrc : ℝ) / decayingBernoulliTopOneSuperunitTargetWeight likelihood α src -
          (qdst : ℝ) / decayingBernoulliTopOneSuperunitTargetWeight likelihood α dst) :
    ((((qdst + 1 : ℕ) : ℝ) + d) /
          decayingBernoulliTopOneSuperunitTargetWeight likelihood α dst) <
      ((((qsrc : ℕ) : ℝ) + d) /
          decayingBernoulliTopOneSuperunitTargetWeight likelihood α src) := by
  let weight : ItemType T → ℝ :=
    decayingBernoulliTopOneSuperunitTargetWeight likelihood α
  have hsrc_pos : 0 < weight src :=
    decayingBernoulliTopOneSuperunitTargetWeight_pos hlike_pos src
  have hdst_pos : 0 < weight dst :=
    decayingBernoulliTopOneSuperunitTargetWeight_pos hlike_pos dst
  have hsum_bound :
      (1 + d) / weight dst ≤
        (1 + d) * ∑ t : ItemType T, 1 / weight t := by
    have hinv_le_sum :
        1 / weight dst ≤ ∑ t : ItemType T, 1 / weight t :=
      Finset.single_le_sum
        (fun t _ => div_nonneg zero_le_one
          (le_of_lt (decayingBernoulliTopOneSuperunitTargetWeight_pos hlike_pos t)))
        (Finset.mem_univ dst)
    have hshift_nonneg : 0 ≤ 1 + d := by linarith
    simpa [div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left hinv_le_sum hshift_nonneg
  have hdst_shift_lt_src :
      (qdst : ℝ) / weight dst + (1 + d) / weight dst <
        (qsrc : ℝ) / weight src := by
    have hshift_lt : (1 + d) / weight dst < Δ :=
      lt_of_le_of_lt hsum_bound hshift
    linarith
  have hsrc_le_shifted :
      (qsrc : ℝ) / weight src ≤ (((qsrc : ℕ) : ℝ) + d) / weight src := by
    have hd_div_nonneg : 0 ≤ d / weight src :=
      div_nonneg hd (le_of_lt hsrc_pos)
    have hrewrite :
        (((qsrc : ℕ) : ℝ) + d) / weight src =
          (qsrc : ℝ) / weight src + d / weight src := by
      field_simp [ne_of_gt hsrc_pos]
    rw [hrewrite]
    linarith
  have hdst_rewrite :
      ((((qdst + 1 : ℕ) : ℝ) + d) / weight dst) =
        (qdst : ℝ) / weight dst + (1 + d) / weight dst := by
    field_simp [ne_of_gt hdst_pos]
    norm_num
    ring
  calc
    ((((qdst + 1 : ℕ) : ℝ) + d) / weight dst)
        = (qdst : ℝ) / weight dst + (1 + d) / weight dst := hdst_rewrite
    _ < (qsrc : ℝ) / weight src := hdst_shift_lt_src
    _ ≤ (((qsrc : ℕ) : ℝ) + d) / weight src := hsrc_le_shifted

theorem decayingBernoulliTopOne_superunit_rawOrdered_marginalCore_lt_of_large_gap
    {T : ℕ} {likelihood : ItemType T → ℝ} {c d α Δ : ℝ}
    (hc : 0 < c) (hd : 0 ≤ d) (hα_pos : 0 < α)
    (hfirst : decayingBernoulliSuccess c d α 0 < 1)
    (hlike_pos : ∀ t, 0 < likelihood t)
    {src dst : ItemType T} {qsrc qdst : ℕ}
    (hqsrc_pos : 0 < qsrc)
    (hqdst_le : qdst ≤ qsrc - 1)
    (hshift :
      (1 + d) *
          ∑ t : ItemType T,
            1 / decayingBernoulliTopOneSuperunitTargetWeight likelihood α t <
        Δ)
    (hgap :
      Δ <
        (qsrc : ℝ) / decayingBernoulliTopOneSuperunitTargetWeight likelihood α src -
          (qdst : ℝ) / decayingBernoulliTopOneSuperunitTargetWeight likelihood α dst) :
    likelihood src *
        (decayingBernoulliSuccess c d α (qsrc - 1) *
          ∏ i ∈ Finset.range (qsrc - 1),
            (1 - decayingBernoulliSuccess c d α i)) <
      likelihood dst *
        (decayingBernoulliSuccess c d α qdst *
          ∏ i ∈ Finset.range qdst,
            (1 - decayingBernoulliSuccess c d α i)) := by
  let weight : ItemType T → ℝ :=
    decayingBernoulliTopOneSuperunitTargetWeight likelihood α
  have hscaled :=
    decayingBernoulliTopOne_superunit_shifted_scaled_lt_of_large_gap
      (T := T) (likelihood := likelihood) (d := d) (α := α) (Δ := Δ)
      hd hlike_pos (src := src) (dst := dst) (qsrc := qsrc) (qdst := qdst)
      hshift hgap
  have hsrc_weight_pos : 0 < weight src :=
    decayingBernoulliTopOneSuperunitTargetWeight_pos hlike_pos src
  have hdst_weight_pos : 0 < weight dst :=
    decayingBernoulliTopOneSuperunitTargetWeight_pos hlike_pos dst
  have hsrc_base_pos : 0 < (qsrc : ℝ) + d := by
    have hqsrc_real_pos : (0 : ℝ) < qsrc := by exact_mod_cast hqsrc_pos
    linarith
  have hdst_base_pos : 0 < ((qdst + 1 : ℕ) : ℝ) + d := by positivity
  have hscaled_core :
      likelihood src *
          (c * (((qsrc : ℕ) : ℝ) + d) ^ (-α)) <
        likelihood dst *
          (c * ((((qdst + 1 : ℕ) : ℝ) + d) ^ (-α))) :=
          rpow_neg_marginal_lt_of_scaled_lt
        (hp_src := hlike_pos src) (hp_dst := hlike_pos dst)
        (hc := hc) (hα := hα_pos) (hx := hsrc_base_pos) (hy := hdst_base_pos)
        (by
          simpa [weight, decayingBernoulliTopOneSuperunitTargetWeight, one_div]
            using hscaled)
  have hsrc_success :
      decayingBernoulliSuccess c d α (qsrc - 1) =
        c * (((qsrc : ℕ) : ℝ) + d) ^ (-α) := by
    unfold decayingBernoulliSuccess
    rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hqsrc_pos)]
  have hdst_success :
      decayingBernoulliSuccess c d α qdst =
        c * ((((qdst + 1 : ℕ) : ℝ) + d) ^ (-α)) := by
    rfl
  have hprod_le :
      ∏ i ∈ Finset.range (qsrc - 1), (1 - decayingBernoulliSuccess c d α i) ≤
        ∏ i ∈ Finset.range qdst, (1 - decayingBernoulliSuccess c d α i) :=
    decayingBernoulliTopOne_survivalProduct_antitone
      c d α (le_of_lt hc) hd (le_of_lt hα_pos) (le_of_lt hfirst) hqdst_le
  have hsrc_scale_nonneg :
      0 ≤ likelihood src * decayingBernoulliSuccess c d α (qsrc - 1) :=
    mul_nonneg (le_of_lt (hlike_pos src))
      (decayingBernoulliSuccess_nonneg c d α (le_of_lt hc) hd (qsrc - 1))
  have hdst_prod_pos :
      0 < ∏ i ∈ Finset.range qdst, (1 - decayingBernoulliSuccess c d α i) :=
    decayingBernoulliTopOne_survivalProduct_pos
      c d α (le_of_lt hc) hd (le_of_lt hα_pos) hfirst qdst
  calc
    likelihood src *
        (decayingBernoulliSuccess c d α (qsrc - 1) *
          ∏ i ∈ Finset.range (qsrc - 1),
            (1 - decayingBernoulliSuccess c d α i))
        =
      (likelihood src * decayingBernoulliSuccess c d α (qsrc - 1)) *
        ∏ i ∈ Finset.range (qsrc - 1),
          (1 - decayingBernoulliSuccess c d α i) := by ring
    _ ≤
      (likelihood src * decayingBernoulliSuccess c d α (qsrc - 1)) *
        ∏ i ∈ Finset.range qdst,
          (1 - decayingBernoulliSuccess c d α i) :=
        mul_le_mul_of_nonneg_left hprod_le hsrc_scale_nonneg
    _ <
      (likelihood dst * decayingBernoulliSuccess c d α qdst) *
        ∏ i ∈ Finset.range qdst,
          (1 - decayingBernoulliSuccess c d α i) :=
        mul_lt_mul_of_pos_right
          (by simpa [hsrc_success, hdst_success] using hscaled_core)
          hdst_prod_pos
    _ =
      likelihood dst *
        (decayingBernoulliSuccess c d α qdst *
          ∏ i ∈ Finset.range qdst,
            (1 - decayingBernoulliSuccess c d α i)) := by ring

theorem decayingBernoulliTopOne_superunit_corrected_shifted_scaled_lt_of_large_gap
    {T : ℕ} {likelihood : ItemType T → ℝ} {d α Δ E : ℝ}
    (hd : 0 ≤ d) (hα_pos : 0 < α)
    (hlike_pos : ∀ t, 0 < likelihood t)
    {src dst : ItemType T} {qsrc qdst : ℕ}
    (hE_nonneg : 0 ≤ E)
    (hshift :
      (1 + d +
          ((((qdst + 1 : ℕ) : ℝ) + d) *
            (Real.exp (E / α) - 1))) *
          ∑ t : ItemType T,
            1 / decayingBernoulliTopOneSuperunitTargetWeight likelihood α t <
        Δ)
    (hgap :
      Δ <
        (qsrc : ℝ) / decayingBernoulliTopOneSuperunitTargetWeight likelihood α src -
          (qdst : ℝ) / decayingBernoulliTopOneSuperunitTargetWeight likelihood α dst) :
    (((((qdst + 1 : ℕ) : ℝ) + d) * Real.exp (E / α)) /
          decayingBernoulliTopOneSuperunitTargetWeight likelihood α dst) <
      ((((qsrc : ℕ) : ℝ) + d) /
          decayingBernoulliTopOneSuperunitTargetWeight likelihood α src) := by
  let weight : ItemType T → ℝ :=
    decayingBernoulliTopOneSuperunitTargetWeight likelihood α
  let B : ℝ := (((qdst + 1 : ℕ) : ℝ) + d)
  let C : ℝ := 1 + d + B * (Real.exp (E / α) - 1)
  have hsrc_pos : 0 < weight src :=
    decayingBernoulliTopOneSuperunitTargetWeight_pos hlike_pos src
  have hdst_pos : 0 < weight dst :=
    decayingBernoulliTopOneSuperunitTargetWeight_pos hlike_pos dst
  have hEdiv_nonneg : 0 ≤ E / α :=
    div_nonneg hE_nonneg (le_of_lt hα_pos)
  have hexp_shift_nonneg : 0 ≤ Real.exp (E / α) - 1 := by
    have hone_le : 1 ≤ Real.exp (E / α) :=
      Real.one_le_exp_iff.mpr hEdiv_nonneg
    linarith
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    nlinarith
  have hsum_bound :
      C / weight dst ≤ C * ∑ t : ItemType T, 1 / weight t := by
    have hinv_le_sum :
        1 / weight dst ≤ ∑ t : ItemType T, 1 / weight t :=
      Finset.single_le_sum
        (fun t _ => div_nonneg zero_le_one
          (le_of_lt (decayingBernoulliTopOneSuperunitTargetWeight_pos hlike_pos t)))
        (Finset.mem_univ dst)
    simpa [div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left hinv_le_sum hC_nonneg
  have hdst_shift_lt_src :
      (qdst : ℝ) / weight dst + C / weight dst <
        (qsrc : ℝ) / weight src := by
    have hshift_lt : C / weight dst < Δ :=
      lt_of_le_of_lt hsum_bound (by simpa [C, B, weight] using hshift)
    linarith
  have hsrc_le_shifted :
      (qsrc : ℝ) / weight src ≤ (((qsrc : ℕ) : ℝ) + d) / weight src := by
    have hd_div_nonneg : 0 ≤ d / weight src :=
      div_nonneg hd (le_of_lt hsrc_pos)
    have hrewrite :
        (((qsrc : ℕ) : ℝ) + d) / weight src =
          (qsrc : ℝ) / weight src + d / weight src := by
      field_simp [ne_of_gt hsrc_pos]
    rw [hrewrite]
    linarith
  have hdst_rewrite :
      (B * Real.exp (E / α)) / weight dst =
        (qdst : ℝ) / weight dst + C / weight dst := by
    dsimp [B, C]
    field_simp [ne_of_gt hdst_pos]
    norm_num
    ring
  calc
    (((((qdst + 1 : ℕ) : ℝ) + d) * Real.exp (E / α)) / weight dst)
        = (B * Real.exp (E / α)) / weight dst := by
          simp [B]
    _ = (qdst : ℝ) / weight dst + C / weight dst := hdst_rewrite
    _ < (qsrc : ℝ) / weight src := hdst_shift_lt_src
    _ ≤ (((qsrc : ℕ) : ℝ) + d) / weight src := hsrc_le_shifted

theorem decayingBernoulliTopOne_superunit_reverse_marginalCore_lt_of_corrected_large_gap
    {T : ℕ} {likelihood : ItemType T → ℝ} {c d α Δ E : ℝ}
    (hc : 0 < c) (hd : 0 ≤ d) (hα_pos : 0 < α)
    (hfirst : decayingBernoulliSuccess c d α 0 < 1)
    (hlike_pos : ∀ t, 0 < likelihood t)
    {src dst : ItemType T} {qsrc qdst : ℕ}
    (hqsrc_pos : 0 < qsrc)
    (hqsrc_pred_le : qsrc - 1 ≤ qdst)
    (hhalf :
      ∀ i ∈ Finset.Ico (qsrc - 1) qdst,
        decayingBernoulliSuccess c d α i ≤ 1 / 2)
    (hE_nonneg : 0 ≤ E)
    (hE_eq :
      E = 2 * ∑ i ∈ Finset.Ico (qsrc - 1) qdst,
        decayingBernoulliSuccess c d α i)
    (hshift :
      (1 + d +
          ((((qdst + 1 : ℕ) : ℝ) + d) *
            (Real.exp (E / α) - 1))) *
          ∑ t : ItemType T,
            1 / decayingBernoulliTopOneSuperunitTargetWeight likelihood α t <
        Δ)
    (hgap :
      Δ <
        (qsrc : ℝ) / decayingBernoulliTopOneSuperunitTargetWeight likelihood α src -
          (qdst : ℝ) / decayingBernoulliTopOneSuperunitTargetWeight likelihood α dst) :
    likelihood src *
        (decayingBernoulliSuccess c d α (qsrc - 1) *
          ∏ i ∈ Finset.range (qsrc - 1),
            (1 - decayingBernoulliSuccess c d α i)) <
      likelihood dst *
        (decayingBernoulliSuccess c d α qdst *
          ∏ i ∈ Finset.range qdst,
            (1 - decayingBernoulliSuccess c d α i)) := by
  let weight : ItemType T → ℝ :=
    decayingBernoulliTopOneSuperunitTargetWeight likelihood α
  let A : ℝ := (qsrc : ℝ) + d
  let B : ℝ := (((qdst + 1 : ℕ) : ℝ) + d)
  let η : ℝ := Real.exp (E / α)
  have hscaled :=
    decayingBernoulliTopOne_superunit_corrected_shifted_scaled_lt_of_large_gap
      (T := T) (likelihood := likelihood) (d := d) (α := α) (Δ := Δ) (E := E)
      hd hα_pos hlike_pos (src := src) (dst := dst) (qsrc := qsrc) (qdst := qdst)
      hE_nonneg hshift hgap
  have hA_pos : 0 < A := by
    dsimp [A]
    have hqsrc_real_pos : (0 : ℝ) < qsrc := by exact_mod_cast hqsrc_pos
    linarith
  have hB_pos : 0 < B := by
    dsimp [B]
    positivity
  have hη_pos : 0 < η := by
    dsimp [η]
    positivity
  have hBη_pos : 0 < B * η := mul_pos hB_pos hη_pos
  have hη_pow_neg : η ^ (-α) = Real.exp (-E) := by
    dsimp [η]
    rw [Real.rpow_def_of_pos (Real.exp_pos (E / α)), Real.log_exp]
    congr 1
    field_simp [ne_of_gt hα_pos]
  have hBη_pow_neg : (B * η) ^ (-α) = B ^ (-α) * Real.exp (-E) := by
    rw [Real.mul_rpow (le_of_lt hB_pos) (le_of_lt hη_pos), hη_pow_neg]
  have hscaled_core_raw :
      likelihood src * (c * A ^ (-α)) <
        likelihood dst * (c * (B * η) ^ (-α)) :=
          rpow_neg_marginal_lt_of_scaled_lt
        (hp_src := hlike_pos src) (hp_dst := hlike_pos dst)
        (hc := hc) (hα := hα_pos) (hx := hA_pos) (hy := hBη_pos)
        (by
          simpa [weight, A, B, η, decayingBernoulliTopOneSuperunitTargetWeight, one_div]
            using hscaled)
  have hscaled_core_exp :
      likelihood src * (c * A ^ (-α)) * Real.exp E <
        likelihood dst * (c * B ^ (-α)) := by
    calc
      likelihood src * (c * A ^ (-α)) * Real.exp E
          < likelihood dst * (c * (B * η) ^ (-α)) * Real.exp E :=
          mul_lt_mul_of_pos_right hscaled_core_raw (Real.exp_pos E)
      _ = likelihood dst * (c * B ^ (-α)) := by
          rw [hBη_pow_neg, Real.exp_neg]
          field_simp [ne_of_gt (Real.exp_pos E)]
  have hsrc_success :
      decayingBernoulliSuccess c d α (qsrc - 1) =
        c * A ^ (-α) := by
    unfold decayingBernoulliSuccess
    dsimp [A]
    rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hqsrc_pos)]
  have hdst_success :
      decayingBernoulliSuccess c d α qdst =
        c * B ^ (-α) := by
    rfl
  have hsurv :
      ∏ i ∈ Finset.range (qsrc - 1), (1 - decayingBernoulliSuccess c d α i) ≤
        (∏ i ∈ Finset.range qdst, (1 - decayingBernoulliSuccess c d α i)) *
          Real.exp E := by
    have h :=
      rankBernoulliTopOne_survivalProduct_le_mul_exp_sum_Ico_reverse
        (decayingBernoulliSuccess c d α)
        (decayingBernoulliSuccess_nonneg c d α (le_of_lt hc) hd)
        (decayingBernoulliSuccess_le_one_of_first_le_one
          c d α (le_of_lt hc) hd (le_of_lt hα_pos) (le_of_lt hfirst))
        hqsrc_pred_le hhalf
    simpa [hE_eq] using h
  have hsrc_scale_nonneg :
      0 ≤ likelihood src * decayingBernoulliSuccess c d α (qsrc - 1) :=
    mul_nonneg (le_of_lt (hlike_pos src))
      (decayingBernoulliSuccess_nonneg c d α (le_of_lt hc) hd (qsrc - 1))
  have hdst_prod_pos :
      0 < ∏ i ∈ Finset.range qdst, (1 - decayingBernoulliSuccess c d α i) :=
    decayingBernoulliTopOne_survivalProduct_pos
      c d α (le_of_lt hc) hd (le_of_lt hα_pos) hfirst qdst
  calc
    likelihood src *
        (decayingBernoulliSuccess c d α (qsrc - 1) *
          ∏ i ∈ Finset.range (qsrc - 1),
            (1 - decayingBernoulliSuccess c d α i))
        =
      (likelihood src * decayingBernoulliSuccess c d α (qsrc - 1)) *
        ∏ i ∈ Finset.range (qsrc - 1),
          (1 - decayingBernoulliSuccess c d α i) := by ring
    _ ≤
      (likelihood src * decayingBernoulliSuccess c d α (qsrc - 1)) *
        ((∏ i ∈ Finset.range qdst,
          (1 - decayingBernoulliSuccess c d α i)) * Real.exp E) :=
        mul_le_mul_of_nonneg_left hsurv hsrc_scale_nonneg
    _ =
      (likelihood src * (c * A ^ (-α)) * Real.exp E) *
        ∏ i ∈ Finset.range qdst,
          (1 - decayingBernoulliSuccess c d α i) := by
        rw [hsrc_success]
        ring
    _ <
      (likelihood dst * (c * B ^ (-α))) *
        ∏ i ∈ Finset.range qdst,
          (1 - decayingBernoulliSuccess c d α i) :=
        mul_lt_mul_of_pos_right hscaled_core_exp hdst_prod_pos
    _ =
      likelihood dst *
        (decayingBernoulliSuccess c d α qdst *
          ∏ i ∈ Finset.range qdst,
            (1 - decayingBernoulliSuccess c d α i)) := by
        rw [hdst_success]
        ring

theorem decayingBernoulliTopOne_superunit_reverse_corrected_shift_lt_of_growth
    {T : ℕ} {likelihood : ItemType T → ℝ} {c d α ε : ℝ}
    {N qsrc qdst : ℕ} {src dst : ItemType T}
    (hc : 0 < c) (hd : 0 ≤ d) (hα_pos : 0 < α)
    (hlike_pos : ∀ t, 0 < likelihood t)
    (hε_pos : 0 < ε) (hN_pos : 0 < N)
    (hqdst_leN : qdst ≤ N)
    (hgap :
      ε * (N : ℝ) <
        (qsrc : ℝ) / decayingBernoulliTopOneSuperunitTargetWeight likelihood α src -
          (qdst : ℝ) / decayingBernoulliTopOneSuperunitTargetWeight likelihood α dst)
    (hfixed :
      2 * ((1 + d) *
          ∑ t : ItemType T,
            1 / decayingBernoulliTopOneSuperunitTargetWeight likelihood α t) <
        ε * (N : ℝ))
    (hsmall_arg :
      (((2 * c *
          ∑ t : ItemType T,
            (decayingBernoulliTopOneSuperunitTargetWeight likelihood α t) ^ (-α)) / α) *
          (N : ℝ) * (ε * (N : ℝ)) ^ (-α)) < 1)
    (hsmall_corr :
      2 * (((2 + d) * Real.exp 1 *
          (((2 * c *
            ∑ t : ItemType T,
              (decayingBernoulliTopOneSuperunitTargetWeight likelihood α t) ^ (-α)) / α) *
            (∑ t : ItemType T,
              1 / decayingBernoulliTopOneSuperunitTargetWeight likelihood α t))) *
          (N : ℝ) ^ 2 * (ε * (N : ℝ)) ^ (-α)) <
        ε * (N : ℝ)) :
    (1 + d +
        ((((qdst + 1 : ℕ) : ℝ) + d) *
          (Real.exp
            ((2 * ∑ i ∈ Finset.Ico (qsrc - 1) qdst,
                decayingBernoulliSuccess c d α i) / α) - 1))) *
        ∑ t : ItemType T,
          1 / decayingBernoulliTopOneSuperunitTargetWeight likelihood α t <
      ε * (N : ℝ) := by
  classical
  let weight : ItemType T → ℝ :=
    decayingBernoulliTopOneSuperunitTargetWeight likelihood α
  let S : ℝ := ∑ t : ItemType T, 1 / weight t
  let P : ℝ := ∑ t : ItemType T, (weight t) ^ (-α)
  let D : ℝ := ε * (N : ℝ)
  let E : ℝ := 2 * ∑ i ∈ Finset.Ico (qsrc - 1) qdst,
    decayingBernoulliSuccess c d α i
  let B : ℝ := (((qdst + 1 : ℕ) : ℝ) + d)
  let Ccorr : ℝ := (2 + d) * Real.exp 1 * (((2 * c * P) / α) * S)
  have hweight_pos : ∀ t, 0 < weight t := by
    intro t
    exact decayingBernoulliTopOneSuperunitTargetWeight_pos hlike_pos t
  have hS_pos : 0 < S := by
    dsimp [S]
    exact Finset.sum_pos
      (fun t _ => one_div_pos.mpr (hweight_pos t))
      ⟨src, Finset.mem_univ src⟩
  have hS_nonneg : 0 ≤ S := le_of_lt hS_pos
  have hD_pos : 0 < D := by
    dsimp [D]
    positivity
  have hN_real_pos : 0 < (N : ℝ) := by exact_mod_cast hN_pos
  have hα_nonneg : 0 ≤ α := le_of_lt hα_pos
  have hdst_div_nonneg :
      0 ≤ (qdst : ℝ) / weight dst :=
    div_nonneg (Nat.cast_nonneg _) (le_of_lt (hweight_pos dst))
  have hgap_src :
      ε * (N : ℝ) < (qsrc : ℝ) / weight src := by
    dsimp [weight] at hgap ⊢
    linarith
  have hE_nonneg : 0 ≤ E := by
    dsimp [E]
    exact mul_nonneg (by norm_num)
      (Finset.sum_nonneg (fun i _ =>
        decayingBernoulliSuccess_nonneg c d α (le_of_lt hc) hd i))
  have hE_le :
      E ≤ (2 * c * P) * (N : ℝ) * D ^ (-α) := by
    dsimp [E, P, D, weight]
    exact
      decayingBernoulliTopOne_superunit_reverse_correction_sum_le_scaled_gap_bound
        (T := T) (likelihood := likelihood) (c := c) (d := d)
        (α := α) (ε := ε) (N := N) (qsrc := qsrc) (qdst := qdst)
        (src := src) hc hd hα_pos hlike_pos
        (by simpa [D]) hqdst_leN (by simpa [weight] using hgap_src)
  have hE_div_bound :
      E / α ≤ ((2 * c * P) / α) * (N : ℝ) * D ^ (-α) := by
    calc
      E / α ≤ ((2 * c * P) * (N : ℝ) * D ^ (-α)) / α :=
        div_le_div_of_nonneg_right hE_le hα_nonneg
      _ = ((2 * c * P) / α) * (N : ℝ) * D ^ (-α) := by
        field_simp [ne_of_gt hα_pos]
  have hE_div_nonneg : 0 ≤ E / α :=
    div_nonneg hE_nonneg hα_nonneg
  have hE_div_le_one : E / α ≤ 1 :=
    le_of_lt (lt_of_le_of_lt hE_div_bound
      (by simpa [P, D, weight] using hsmall_arg))
  have hexp_sub_bound :
      Real.exp (E / α) - 1 ≤ Real.exp 1 * (E / α) :=
    exp_sub_one_le_exp_one_mul hE_div_nonneg hE_div_le_one
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hB_le : B ≤ (2 + d) * (N : ℝ) := by
    have hqdst_leN_real : (qdst : ℝ) ≤ (N : ℝ) := by exact_mod_cast hqdst_leN
    have hN_ge_one : (1 : ℝ) ≤ N := by exact_mod_cast hN_pos
    have hone_d_nonneg : 0 ≤ 1 + d := by linarith
    have htail_le : 1 + d ≤ (1 + d) * (N : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hN_ge_one hone_d_nonneg
      simpa using h
    dsimp [B]
    calc
      (((qdst + 1 : ℕ) : ℝ) + d) = (qdst : ℝ) + 1 + d := by norm_num
      _ ≤ (N : ℝ) + (1 + d) := by linarith
      _ ≤ (N : ℝ) + (1 + d) * (N : ℝ) := by linarith
      _ = (2 + d) * (N : ℝ) := by ring
  have hcoeff_nonneg : 0 ≤ ((2 * c * P) / α) * (N : ℝ) * D ^ (-α) :=
    le_trans hE_div_nonneg hE_div_bound
  have hcorr_le :
      B * (Real.exp (E / α) - 1) * S ≤
        Ccorr * (N : ℝ) ^ 2 * D ^ (-α) := by
    calc
      B * (Real.exp (E / α) - 1) * S
          ≤ B * (Real.exp 1 * (E / α)) * S :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hexp_sub_bound hB_nonneg) hS_nonneg
      _ ≤ ((2 + d) * (N : ℝ)) *
            (Real.exp 1 * (((2 * c * P) / α) * (N : ℝ) * D ^ (-α))) * S := by
            gcongr
      _ = Ccorr * (N : ℝ) ^ 2 * D ^ (-α) := by
            dsimp [Ccorr]
            ring
  have hfixed_half : (1 + d) * S < D / 2 := by
    dsimp [D, S, weight] at hfixed ⊢
    linarith
  have hcorr_half : Ccorr * (N : ℝ) ^ 2 * D ^ (-α) < D / 2 := by
    have hsmall_corr' :
        2 * (Ccorr * (N : ℝ) ^ 2 * D ^ (-α)) < D := by
      simpa [Ccorr, P, S, D, weight, mul_assoc] using hsmall_corr
    linarith
  have hshift_split :
      (1 + d + B * (Real.exp (E / α) - 1)) * S =
        (1 + d) * S + B * (Real.exp (E / α) - 1) * S := by
    ring
  calc
    (1 + d + B * (Real.exp (E / α) - 1)) * S
        = (1 + d) * S + B * (Real.exp (E / α) - 1) * S := hshift_split
    _ < D / 2 + D / 2 :=
        add_lt_add hfixed_half (lt_of_le_of_lt hcorr_le hcorr_half)
    _ = D := by ring
    _ = ε * (N : ℝ) := by rfl

noncomputable def decayingBernoulliTopOneSuperunitBeta (α : ℝ) : ℝ := (α - 1) / (2 * (α + 1))

theorem decayingBernoulliTopOneSuperunitBeta_pos {α : ℝ} (hα_gt_one : 1 < α) :
    0 < decayingBernoulliTopOneSuperunitBeta α := by
  unfold decayingBernoulliTopOneSuperunitBeta
  have hnum_pos : 0 < α - 1 := by linarith
  have hden_pos : 0 < 2 * (α + 1) := by nlinarith
  exact div_pos hnum_pos hden_pos

theorem decayingBernoulliTopOneSuperunitBeta_lt_one {α : ℝ} (hα_gt_one : 1 < α) :
    decayingBernoulliTopOneSuperunitBeta α < 1 := by
  unfold decayingBernoulliTopOneSuperunitBeta
  have hden_pos : 0 < 2 * (α + 1) := by nlinarith
  rw [div_lt_iff₀ hden_pos]
  nlinarith

noncomputable def decayingBernoulliTopOneSuperunitError
    (α : ℝ) (N : ℕ) : ℝ := (((N + 1 : ℕ) : ℝ)) ^ (-(decayingBernoulliTopOneSuperunitBeta α))

theorem decayingBernoulliTopOneSuperunitError_nonneg
    (α : ℝ) (N : ℕ) :
    0 ≤ decayingBernoulliTopOneSuperunitError α N := by
  unfold decayingBernoulliTopOneSuperunitError
  positivity

theorem decayingBernoulliTopOneSuperunitError_tends_to_zero
    {α : ℝ} (hα_gt_one : 1 < α) :
    AppliedModelingLib.Math.TendsToZero
      (decayingBernoulliTopOneSuperunitError α) := by
  have hβ : 0 < decayingBernoulliTopOneSuperunitBeta α :=
    decayingBernoulliTopOneSuperunitBeta_pos hα_gt_one
  have hpow :
      Tendsto
        (fun N : ℕ =>
          (((N + 1 : ℕ) : ℝ)) ^ (-(decayingBernoulliTopOneSuperunitBeta α)))
        atTop (nhds 0) :=
    AppliedModelingLib.Math.tendsto_nat_succ_cast_rpow_neg_nhds_zero hβ
  rw [AppliedModelingLib.Math.TendsToZero]
  refine Tendsto.congr' ?_ hpow
  filter_upwards with N
  simp [decayingBernoulliTopOneSuperunitError]

theorem decayingBernoulliTopOneSuperunitError_mul_nat_lower
    (α : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    (1 / 2 : ℝ) *
        (((N + 1 : ℕ) : ℝ) ^
          (1 - decayingBernoulliTopOneSuperunitBeta α)) ≤
      decayingBernoulliTopOneSuperunitError α N * (N : ℝ) := by
  let β : ℝ := decayingBernoulliTopOneSuperunitBeta α
  unfold decayingBernoulliTopOneSuperunitError
  have hbase_pos : 0 < (((N + 1 : ℕ) : ℝ)) := by positivity
  have hbase_div_le_N :
      (((N + 1 : ℕ) : ℝ)) / 2 ≤ (N : ℝ) := by
    have hN_real : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hbase_eq : (((N + 1 : ℕ) : ℝ)) = (N : ℝ) + 1 := by norm_num
    nlinarith
  have hpow_nonneg :
      0 ≤ (((N + 1 : ℕ) : ℝ) ^ (-β)) :=
    Real.rpow_nonneg (le_of_lt hbase_pos) _
  calc
    (1 / 2 : ℝ) *
        (((N + 1 : ℕ) : ℝ) ^
          (1 - decayingBernoulliTopOneSuperunitBeta α))
        = ((((N + 1 : ℕ) : ℝ)) / 2) *
            (((N + 1 : ℕ) : ℝ) ^ (-β)) := by
          dsimp [β]
          rw [show 1 - decayingBernoulliTopOneSuperunitBeta α =
            1 + (-(decayingBernoulliTopOneSuperunitBeta α)) by ring]
          rw [Real.rpow_add hbase_pos, Real.rpow_one]
          ring
    _ ≤ (N : ℝ) * (((N + 1 : ℕ) : ℝ) ^ (-β)) :=
          mul_le_mul_of_nonneg_right hbase_div_le_N hpow_nonneg
    _ = (((N + 1 : ℕ) : ℝ) ^ (-(decayingBernoulliTopOneSuperunitBeta α))) *
        (N : ℝ) := by
          dsimp [β]
          ring

theorem decayingBernoulliTopOneSuperunitError_mul_nat_tendsto_atTop
    {α : ℝ} (hα_gt_one : 1 < α) :
    Tendsto
      (fun N : ℕ => decayingBernoulliTopOneSuperunitError α N * (N : ℝ))
      atTop atTop := by
  let β : ℝ := decayingBernoulliTopOneSuperunitBeta α
  let γ : ℝ := 1 - β
  have hβ_pos : 0 < β := by
    dsimp [β]
    exact decayingBernoulliTopOneSuperunitBeta_pos hα_gt_one
  have hβ_lt_one : β < 1 := by
    dsimp [β]
    exact decayingBernoulliTopOneSuperunitBeta_lt_one hα_gt_one
  have hγ_pos : 0 < γ := by
    dsimp [γ]
    linarith
  have hpow :
      Tendsto (fun N : ℕ => (((N + 1 : ℕ) : ℝ) ^ γ)) atTop atTop :=
    AppliedModelingLib.Math.tendsto_nat_succ_cast_rpow_atTop hγ_pos
  have hhalf :
      Tendsto
        (fun N : ℕ => (1 / 2 : ℝ) * (((N + 1 : ℕ) : ℝ) ^ γ))
        atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2) hpow
  refine tendsto_atTop_mono' atTop ?_ hhalf
  filter_upwards [eventually_ge_atTop 1] with N hN
  simpa [γ, β] using
    decayingBernoulliTopOneSuperunitError_mul_nat_lower α hN

theorem decayingBernoulliTopOneSuperunitError_mul_nat_eventually_gt
    {α : ℝ} (hα_gt_one : 1 < α) (B : ℝ) :
    ∀ᶠ N in atTop,
      B < decayingBernoulliTopOneSuperunitError α N * (N : ℝ) :=
  (decayingBernoulliTopOneSuperunitError_mul_nat_tendsto_atTop
    hα_gt_one).eventually_gt_atTop B

theorem decayingBernoulliTopOneSuperunit_arg_tends_to_zero
    {α : ℝ} (hα_gt_one : 1 < α) :
    Tendsto
      (fun N : ℕ =>
        (N : ℝ) *
          (decayingBernoulliTopOneSuperunitError α N * (N : ℝ)) ^ (-α))
      atTop (nhds 0) := by
  let β : ℝ := decayingBernoulliTopOneSuperunitBeta α
  let γ : ℝ := 1 - β
  let δ : ℝ := γ * α - 1
  let K : ℝ := (1 / 2 : ℝ) ^ (-α)
  have hβ_pos : 0 < β := by
    dsimp [β]
    exact decayingBernoulliTopOneSuperunitBeta_pos hα_gt_one
  have hβ_lt_one : β < 1 := by
    dsimp [β]
    exact decayingBernoulliTopOneSuperunitBeta_lt_one hα_gt_one
  have hγ_pos : 0 < γ := by
    dsimp [γ]
    linarith
  have hδ_pos : 0 < δ := by
    dsimp [δ, γ, β, decayingBernoulliTopOneSuperunitBeta]
    have hden_pos : 0 < 2 * (α + 1) := by nlinarith
    field_simp [ne_of_gt hden_pos]
    nlinarith
  have hbound_tendsto :
      Tendsto
        (fun N : ℕ => K * (((N + 1 : ℕ) : ℝ) ^ (-δ)))
        atTop (nhds 0) := by
    have hpow :
        Tendsto (fun N : ℕ => (((N + 1 : ℕ) : ℝ) ^ (-δ)))
          atTop (nhds 0) :=
      AppliedModelingLib.Math.tendsto_nat_succ_cast_rpow_neg_nhds_zero hδ_pos
    simpa using hpow.const_mul K
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound_tendsto ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hD_nonneg :
        0 ≤ decayingBernoulliTopOneSuperunitError α N * (N : ℝ) :=
      mul_nonneg (decayingBernoulliTopOneSuperunitError_nonneg α N)
        (Nat.cast_nonneg N)
    positivity
  · filter_upwards [eventually_ge_atTop 1] with N hN
    let base : ℝ := (((N + 1 : ℕ) : ℝ))
    let D : ℝ := decayingBernoulliTopOneSuperunitError α N * (N : ℝ)
    let L : ℝ := (1 / 2 : ℝ) * base ^ γ
    have hbase_pos : 0 < base := by
      dsimp [base]
      positivity
    have hbase_ge_N : (N : ℝ) ≤ base := by
      dsimp [base]
      norm_num
    have hL_pos : 0 < L := by
      dsimp [L]
      positivity
    have hD_lower : L ≤ D := by
      dsimp [L, D, base, γ, β]
      simpa [sub_eq_add_neg] using
        decayingBernoulliTopOneSuperunitError_mul_nat_lower α hN
    have hD_pow_le : D ^ (-α) ≤ L ^ (-α) :=
      Real.rpow_le_rpow_of_nonpos hL_pos hD_lower
        (neg_nonpos.mpr (le_of_lt (lt_trans zero_lt_one hα_gt_one)))
    have hD_pos : 0 < D := lt_of_lt_of_le hL_pos hD_lower
    have hL_pow :
        L ^ (-α) = K * base ^ (-(γ * α)) := by
      dsimp [L, K]
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (le_of_lt (Real.rpow_pos_of_pos hbase_pos γ))]
      rw [← Real.rpow_mul (le_of_lt hbase_pos) γ (-α)]
      congr 2
      ring
    have hright_nonneg : 0 ≤ L ^ (-α) :=
      Real.rpow_nonneg (le_of_lt hL_pos) _
    calc
      (N : ℝ) * D ^ (-α) ≤ base * L ^ (-α) :=
        mul_le_mul hbase_ge_N hD_pow_le
          (Real.rpow_nonneg (le_of_lt hD_pos) _) (le_of_lt hbase_pos)
      _ = base * (K * base ^ (-(γ * α))) := by rw [hL_pow]
      _ = K * base ^ (-δ) := by
        dsimp [δ]
        rw [show -δ = 1 + (-(γ * α)) by ring]
        rw [Real.rpow_add hbase_pos, Real.rpow_one]
        ring

theorem decayingBernoulliTopOneSuperunit_corr_tends_to_zero
    {α : ℝ} (hα_gt_one : 1 < α) :
    Tendsto
      (fun N : ℕ =>
        (N : ℝ) ^ 2 *
          (decayingBernoulliTopOneSuperunitError α N * (N : ℝ)) ^ (-(α + 1)))
      atTop (nhds 0) := by
  let β : ℝ := decayingBernoulliTopOneSuperunitBeta α
  let γ : ℝ := 1 - β
  let δ : ℝ := γ * (α + 1) - 2
  let K : ℝ := (1 / 2 : ℝ) ^ (-(α + 1))
  have hβ_pos : 0 < β := by
    dsimp [β]
    exact decayingBernoulliTopOneSuperunitBeta_pos hα_gt_one
  have hβ_lt_one : β < 1 := by
    dsimp [β]
    exact decayingBernoulliTopOneSuperunitBeta_lt_one hα_gt_one
  have hγ_pos : 0 < γ := by
    dsimp [γ]
    linarith
  have hδ_pos : 0 < δ := by
    dsimp [δ, γ, β, decayingBernoulliTopOneSuperunitBeta]
    have hden_pos : 0 < 2 * (α + 1) := by nlinarith
    field_simp [ne_of_gt hden_pos]
    nlinarith
  have hbase :
      Tendsto (fun N : ℕ => (((N + 1 : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hbound_tendsto :
      Tendsto
        (fun N : ℕ => K * (((N + 1 : ℕ) : ℝ) ^ (-δ)))
        atTop (nhds 0) := by
    have hpow :
        Tendsto (fun N : ℕ => (((N + 1 : ℕ) : ℝ) ^ (-δ)))
          atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop hδ_pos).comp hbase
    simpa using hpow.const_mul K
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound_tendsto ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hD_nonneg :
        0 ≤ decayingBernoulliTopOneSuperunitError α N * (N : ℝ) :=
      mul_nonneg (decayingBernoulliTopOneSuperunitError_nonneg α N)
        (Nat.cast_nonneg N)
    positivity
  · filter_upwards [eventually_ge_atTop 1] with N hN
    let base : ℝ := (((N + 1 : ℕ) : ℝ))
    let D : ℝ := decayingBernoulliTopOneSuperunitError α N * (N : ℝ)
    let L : ℝ := (1 / 2 : ℝ) * base ^ γ
    have hbase_pos : 0 < base := by
      dsimp [base]
      positivity
    have hbase_ge_N : (N : ℝ) ≤ base := by
      dsimp [base]
      norm_num
    have hbase_sq_ge_N_sq : (N : ℝ) ^ 2 ≤ base ^ 2 := by
      nlinarith
    have hL_pos : 0 < L := by
      dsimp [L]
      positivity
    have hD_lower : L ≤ D := by
      dsimp [L, D, base, γ, β]
      simpa [sub_eq_add_neg] using
        decayingBernoulliTopOneSuperunitError_mul_nat_lower α hN
    have hD_pow_le : D ^ (-(α + 1)) ≤ L ^ (-(α + 1)) :=
      Real.rpow_le_rpow_of_nonpos hL_pos hD_lower
        (by linarith : -(α + 1) ≤ 0)
    have hD_pos : 0 < D := lt_of_lt_of_le hL_pos hD_lower
    have hL_pow :
        L ^ (-(α + 1)) = K * base ^ (-(γ * (α + 1))) := by
      dsimp [L, K]
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (le_of_lt (Real.rpow_pos_of_pos hbase_pos γ))]
      rw [← Real.rpow_mul (le_of_lt hbase_pos) γ (-(α + 1))]
      congr 2
      ring
    calc
      (N : ℝ) ^ 2 * D ^ (-(α + 1)) ≤ base ^ 2 * L ^ (-(α + 1)) :=
        mul_le_mul hbase_sq_ge_N_sq hD_pow_le
          (Real.rpow_nonneg (le_of_lt hD_pos) _) (sq_nonneg base)
      _ = base ^ 2 * (K * base ^ (-(γ * (α + 1)))) := by rw [hL_pow]
      _ = K * base ^ (-δ) := by
        dsimp [δ]
        rw [show -δ = 2 + (-(γ * (α + 1))) by ring]
        rw [Real.rpow_add hbase_pos]
        norm_num
        ring

/--
`α > 1` growth certificate for the top-one decaying-Bernoulli branch.

The finite product layer has the same two-order shape as the `α = 1` branch:
raw count order only needs the fixed shifted-count term, while reverse raw order
needs an explicit inverse-survival-product correction.
-/
structure DecayingBernoulliTopOneSuperunitGrowthCertificate
    {T : ℕ} [NeZero T] (likelihood : ItemType T → ℝ) (c d α : ℝ) where
  alpha_gt_one : 1 < α
  c_pos : 0 < c
  d_nonneg : 0 ≤ d
  success_first_lt_one : decayingBernoulliSuccess c d α 0 < 1
  likelihood_pos : ∀ t, 0 < likelihood t
  error : ℕ → ℝ
  error_nonneg : ∀ N, 0 ≤ error N
  error_tends_to_zero : AppliedModelingLib.Math.TendsToZero error
  floor : ℕ
  floor_half :
    ∀ i, floor ≤ i → decayingBernoulliSuccess c d α i ≤ 1 / 2
  raw_shift_growth :
    ∀ᶠ N in atTop,
      (1 + d) *
          ∑ t : ItemType T,
            1 / decayingBernoulliTopOneSuperunitTargetWeight likelihood α t <
        error N * (N : ℝ)
  reverse_shift_growth :
    ∀ᶠ N in atTop,
      ∀ src dst qsrc qdst,
        qsrc ≤ N →
        qdst ≤ N →
        floor < qsrc →
        floor < qdst →
        qsrc - 1 ≤ qdst →
        error N * (N : ℝ) <
          (qsrc : ℝ) / decayingBernoulliTopOneSuperunitTargetWeight likelihood α src -
            (qdst : ℝ) / decayingBernoulliTopOneSuperunitTargetWeight likelihood α dst →
        (1 + d +
            ((((qdst + 1 : ℕ) : ℝ) + d) *
              (Real.exp
                ((2 * ∑ i ∈ Finset.Ico (qsrc - 1) qdst,
                    decayingBernoulliSuccess c d α i) / α) - 1))) *
            ∑ t : ItemType T,
              1 / decayingBernoulliTopOneSuperunitTargetWeight likelihood α t <
          error N * (N : ℝ)

namespace DecayingBernoulliTopOneSuperunitGrowthCertificate

noncomputable def of_superunit_error
    {T : ℕ} [NeZero T] (likelihood : ItemType T → ℝ) {c d α : ℝ}
    (hα_gt_one : 1 < α) (hc : 0 < c) (hd : 0 ≤ d)
    (hfirst : decayingBernoulliSuccess c d α 0 < 1)
    (hlike_pos : ∀ t, 0 < likelihood t) :
    DecayingBernoulliTopOneSuperunitGrowthCertificate likelihood c d α := by
  classical
  let weight : ItemType T → ℝ :=
    decayingBernoulliTopOneSuperunitTargetWeight likelihood α
  let S : ℝ := ∑ t : ItemType T, 1 / weight t
  let P : ℝ := ∑ t : ItemType T, (weight t) ^ (-α)
  let Carg : ℝ := (2 * c * P) / α
  let Ccorr : ℝ := (2 + d) * Real.exp 1 * (Carg * S)
  have hα_pos : 0 < α := lt_trans zero_lt_one hα_gt_one
  have hevent_half :
      ∀ᶠ i in atTop, decayingBernoulliSuccess c d α i ≤ 1 / 2 := by
    have hlt :
        ∀ᶠ i in atTop, decayingBernoulliSuccess c d α i < 1 / 2 :=
              (decayingBernoulliSuccess_tendsto_zero c d α hα_pos).eventually
          (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    filter_upwards [hlt] with i hi
    exact le_of_lt hi
  let floor : ℕ := Classical.choose (eventually_atTop.1 hevent_half)
  have hfloor :
      ∀ i, floor ≤ i → decayingBernoulliSuccess c d α i ≤ 1 / 2 :=
    Classical.choose_spec (eventually_atTop.1 hevent_half)
  refine
    { alpha_gt_one := hα_gt_one
      c_pos := hc
      d_nonneg := hd
      success_first_lt_one := hfirst
      likelihood_pos := hlike_pos
      error := decayingBernoulliTopOneSuperunitError α
      error_nonneg := decayingBernoulliTopOneSuperunitError_nonneg α
      error_tends_to_zero :=
        decayingBernoulliTopOneSuperunitError_tends_to_zero hα_gt_one
      floor := floor
      floor_half := hfloor
      raw_shift_growth := ?_
      reverse_shift_growth := ?_ }
  · exact
      decayingBernoulliTopOneSuperunitError_mul_nat_eventually_gt
        hα_gt_one ((1 + d) * S)
  · have harg_tendsto :
        Tendsto
          (fun N : ℕ =>
            Carg * ((N : ℝ) *
              (decayingBernoulliTopOneSuperunitError α N * (N : ℝ)) ^ (-α)))
          atTop (nhds 0) := by
      simpa using
        (decayingBernoulliTopOneSuperunit_arg_tends_to_zero
          hα_gt_one).const_mul Carg
    have harg_small :
        ∀ᶠ (N : ℕ) in atTop,
          Carg * ((N : ℝ) *
              (decayingBernoulliTopOneSuperunitError α N * (N : ℝ)) ^ (-α)) <
            1 :=
      harg_tendsto.eventually
        (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
    have hcorr_tendsto :
        Tendsto
          (fun N : ℕ =>
            (2 * Ccorr) * ((N : ℝ) ^ 2 *
              (decayingBernoulliTopOneSuperunitError α N * (N : ℝ)) ^
                (-(α + 1))))
          atTop (nhds 0) := by
      simpa using
        (decayingBernoulliTopOneSuperunit_corr_tends_to_zero
          hα_gt_one).const_mul (2 * Ccorr)
    have hcorr_small :
        ∀ᶠ (N : ℕ) in atTop,
          (2 * Ccorr) * ((N : ℝ) ^ 2 *
              (decayingBernoulliTopOneSuperunitError α N * (N : ℝ)) ^
                (-(α + 1))) <
            1 :=
      hcorr_tendsto.eventually
        (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards
      [eventually_ge_atTop 1,
        decayingBernoulliTopOneSuperunitError_mul_nat_eventually_gt
          hα_gt_one (2 * ((1 + d) * S)),
        harg_small,
        hcorr_small] with
      N hN_ge_one hfixed hsmall_arg hsmall_corr
    intro src dst qsrc qdst _hqsrc_leN hqdst_leN _hqsrc_floor _hqdst_floor
      hqsrc_pred_le hgap
    let ε : ℝ := decayingBernoulliTopOneSuperunitError α N
    let D : ℝ := ε * (N : ℝ)
    have hN_pos : 0 < N := Nat.lt_of_lt_of_le Nat.zero_lt_one hN_ge_one
    have hε_pos : 0 < ε := by
      dsimp [ε, decayingBernoulliTopOneSuperunitError]
      positivity
    have hD_pos : 0 < D := by
      dsimp [D]
      positivity
    have hsmall_arg' :
        Carg * (N : ℝ) * D ^ (-α) < 1 := by
      dsimp [D, ε] at hsmall_arg ⊢
      simpa [mul_assoc] using hsmall_arg
    have hpow_shift :
        D ^ (-α) = D ^ (-(α + 1)) * D := by
      rw [show -α = -(α + 1) + 1 by ring]
      rw [Real.rpow_add hD_pos, Real.rpow_one]
    have hsmall_corr' :
        2 * (Ccorr * (N : ℝ) ^ 2 * D ^ (-α)) < D := by
      have hrewrite :
          2 * (Ccorr * (N : ℝ) ^ 2 * D ^ (-α)) =
            ((2 * Ccorr) * ((N : ℝ) ^ 2 * D ^ (-(α + 1)))) * D := by
        rw [hpow_shift]
        ring
      rw [hrewrite]
      calc
        ((2 * Ccorr) * ((N : ℝ) ^ 2 * D ^ (-(α + 1)))) * D < 1 * D :=
          mul_lt_mul_of_pos_right
            (by
              simpa [D, ε, mul_assoc] using hsmall_corr)
            hD_pos
        _ = D := by ring
    exact
      decayingBernoulliTopOne_superunit_reverse_corrected_shift_lt_of_growth
        (T := T) (likelihood := likelihood) (c := c) (d := d) (α := α)
        (ε := ε) (N := N) (qsrc := qsrc) (qdst := qdst)
        (src := src) (dst := dst)
        hc hd hα_pos hlike_pos hε_pos hN_pos hqdst_leN hgap
        (by simpa [S, D, ε, weight] using hfixed)
        (by simpa [Carg, P, D, ε, weight, mul_assoc] using hsmall_arg')
        (by simpa [Ccorr, Carg, P, S, D, ε, weight, mul_assoc] using
          hsmall_corr')

noncomputable def toEventualSublinearFOCCertificate
    {T : ℕ} [NeZero T] {likelihood : ItemType T → ℝ} {c d α : ℝ}
    (hcert :
      DecayingBernoulliTopOneSuperunitGrowthCertificate likelihood c d α) :
    DecayingBernoulliTopOneEventualSublinearFOCCertificate
      likelihood c d α (decayingBernoulliTopOneSuperunitTargetWeight likelihood α)
      (gammaLikelihoodProfile likelihood (1 / α)) := by
  classical
  refine
    { alpha_pos := lt_trans zero_lt_one hcert.alpha_gt_one
      c_pos := hcert.c_pos
      d_nonneg := hcert.d_nonneg
      success_first_lt_one := hcert.success_first_lt_one
      likelihood_pos := hcert.likelihood_pos
      weight_pos := ?_
      targetShare_eq := ?_
      base_error := hcert.error
      base_error_nonneg := hcert.error_nonneg
      base_error_tends_to_zero := hcert.error_tends_to_zero
      floor := hcert.floor
      large_gap_marginal_dominance_after_floor := ?_ }
  · intro t
    exact decayingBernoulliTopOneSuperunitTargetWeight_pos hcert.likelihood_pos t
  · intro t
    have hnorm_pos :
        0 < (gammaLikelihoodProfile likelihood (1 / α)).normalizer := by
      unfold GammaHomogeneityProfile.normalizer gammaLikelihoodProfile
      exact Finset.sum_pos
        (fun i _ =>
          decayingBernoulliTopOneSuperunitTargetWeight_pos hcert.likelihood_pos i)
        Finset.univ_nonempty
    rw [GammaHomogeneityProfile.targetShare_eq_div_of_normalizer_ne_zero
      (G := gammaLikelihoodProfile likelihood (1 / α)) (t := t)
      (ne_of_gt hnorm_pos)]
    rfl
  · filter_upwards [hcert.raw_shift_growth, hcert.reverse_shift_growth] with
      N hraw hreverse
    intro src dst qsrc qdst hqsrc_leN hqdst_leN hqsrc_floor hqdst_floor hgap
    have hqsrc_pos : 0 < qsrc :=
      Nat.lt_of_le_of_lt (Nat.zero_le hcert.floor) hqsrc_floor
    by_cases hraw_order : qdst ≤ qsrc - 1
    · exact
        decayingBernoulliTopOne_superunit_rawOrdered_marginalCore_lt_of_large_gap
          (T := T) (likelihood := likelihood) (c := c) (d := d) (α := α)
          (Δ := hcert.error N * (N : ℝ))
          hcert.c_pos hcert.d_nonneg (lt_trans zero_lt_one hcert.alpha_gt_one)
          hcert.success_first_lt_one hcert.likelihood_pos
          (src := src) (dst := dst) (qsrc := qsrc) (qdst := qdst)
          hqsrc_pos hraw_order hraw hgap
    · have hreverse_order : qsrc - 1 ≤ qdst :=
        le_of_lt (Nat.lt_of_not_ge hraw_order)
      have hfloor_le_pred : hcert.floor ≤ qsrc - 1 :=
        Nat.le_sub_one_of_lt hqsrc_floor
      have hhalf :
          ∀ i ∈ Finset.Ico (qsrc - 1) qdst,
            decayingBernoulliSuccess c d α i ≤ 1 / 2 := by
        intro i hi
        exact hcert.floor_half i
          (le_trans hfloor_le_pred (Finset.mem_Ico.mp hi).1)
      have hE_nonneg :
          0 ≤
            2 * ∑ i ∈ Finset.Ico (qsrc - 1) qdst,
              decayingBernoulliSuccess c d α i := by
        have hsum_nonneg :
            0 ≤ ∑ i ∈ Finset.Ico (qsrc - 1) qdst,
              decayingBernoulliSuccess c d α i :=
          Finset.sum_nonneg (fun i _ =>
            decayingBernoulliSuccess_nonneg c d α (le_of_lt hcert.c_pos)
              hcert.d_nonneg i)
        nlinarith
      exact
        decayingBernoulliTopOne_superunit_reverse_marginalCore_lt_of_corrected_large_gap
          (T := T) (likelihood := likelihood) (c := c) (d := d) (α := α)
          (Δ := hcert.error N * (N : ℝ))
          (E :=
            2 * ∑ i ∈ Finset.Ico (qsrc - 1) qdst,
              decayingBernoulliSuccess c d α i)
          hcert.c_pos hcert.d_nonneg (lt_trans zero_lt_one hcert.alpha_gt_one)
          hcert.success_first_lt_one hcert.likelihood_pos
          (src := src) (dst := dst) (qsrc := qsrc) (qdst := qdst)
          hqsrc_pos hreverse_order hhalf hE_nonneg rfl
          (hreverse src dst qsrc qdst hqsrc_leN hqdst_leN
            hqsrc_floor hqdst_floor hreverse_order hgap)
          hgap

theorem asymptoticHomogeneity
    {T : ℕ} [NeZero T] {likelihood : ItemType T → ℝ} {c d α : ℝ}
    (hcert :
      DecayingBernoulliTopOneSuperunitGrowthCertificate likelihood c d α) :
    ConsumptionModel.AsymptoticHomogeneity
      (fun _ => decayingBernoulliTopOneConsumptionModel likelihood c d α)
      (gammaLikelihoodProfile likelihood (1 / α)) := hcert.toEventualSublinearFOCCertificate.asymptoticHomogeneity

end DecayingBernoulliTopOneSuperunitGrowthCertificate

/--
`0 < α < 1` growth certificate for the top-one decaying-Bernoulli branch.

The finite product layer reduces the uniform-homogeneity product estimate to a
single growth condition: the selected sublinear gap schedule must make
`(ε_N N - 1) * q_N` eventually dominate all finite log-likelihood ratios.
Proving this field for a concrete schedule is the remaining asymptotic-growth
step for Theorem 2(i).
-/
structure DecayingBernoulliTopOneSubunitGrowthCertificate
    {T : ℕ} [NeZero T] (likelihood : ItemType T → ℝ) (c d α : ℝ) where
  alpha_pos : 0 < α
  alpha_lt_one : α < 1
  c_pos : 0 < c
  d_nonneg : 0 ≤ d
  success_first_lt_one : decayingBernoulliSuccess c d α 0 < 1
  likelihood_pos : ∀ t, 0 < likelihood t
  error : ℕ → ℝ
  error_nonneg : ∀ N, 0 ≤ error N
  error_tends_to_zero : AppliedModelingLib.Math.TendsToZero error
  floor : ℕ
  growth :
    ∀ᶠ N in atTop,
      decayingBernoulliTopOneLogRatioBound likelihood <
        (error N * (N : ℝ) - 1) * decayingBernoulliSuccess c d α N

namespace DecayingBernoulliTopOneSubunitGrowthCertificate

noncomputable def of_subunit_error_growth
    {T : ℕ} [NeZero T] (likelihood : ItemType T → ℝ) (c d α : ℝ)
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hc : 0 < c) (hd : 0 ≤ d)
    (hfirst : decayingBernoulliSuccess c d α 0 < 1)
    (hlike_pos : ∀ t, 0 < likelihood t)
    (floor : ℕ)
    (hgrowth :
      ∀ᶠ N in atTop,
        decayingBernoulliTopOneLogRatioBound likelihood <
          (decayingBernoulliTopOneSubunitError α N * (N : ℝ) - 1) *
            decayingBernoulliSuccess c d α N) :
    DecayingBernoulliTopOneSubunitGrowthCertificate likelihood c d α where
  alpha_pos := hα_pos
  alpha_lt_one := hα_lt_one
  c_pos := hc
  d_nonneg := hd
  success_first_lt_one := hfirst
  likelihood_pos := hlike_pos
  error := decayingBernoulliTopOneSubunitError α
  error_nonneg := decayingBernoulliTopOneSubunitError_nonneg α
  error_tends_to_zero :=
    decayingBernoulliTopOneSubunitError_tends_to_zero hα_lt_one
  floor := floor
  growth := hgrowth

noncomputable def of_positive_subunit_error
    {T : ℕ} [NeZero T] (likelihood : ItemType T → ℝ) (c d α : ℝ)
    (hα_pos : 0 < α) (hα_lt_one : α < 1)
    (hc : 0 < c) (hd : 0 ≤ d)
    (hfirst : decayingBernoulliSuccess c d α 0 < 1)
    (hlike_pos : ∀ t, 0 < likelihood t) :
    DecayingBernoulliTopOneSubunitGrowthCertificate likelihood c d α :=
  of_subunit_error_growth likelihood c d α hα_pos hα_lt_one hc hd
    hfirst hlike_pos 0
    (decayingBernoulliTopOneSubunitGrowth_eventually
      (B := decayingBernoulliTopOneLogRatioBound likelihood)
      hα_pos hα_lt_one hc hd)

noncomputable def toEventualSublinearFOCCertificate
    {T : ℕ} [NeZero T] {likelihood : ItemType T → ℝ} {c d α : ℝ}
    (hcert :
      DecayingBernoulliTopOneSubunitGrowthCertificate likelihood c d α) :
    DecayingBernoulliTopOneEventualSublinearFOCCertificate
      likelihood c d α (fun _ : ItemType T => (1 : ℝ)) (uniformProfile T) where
  alpha_pos := hcert.alpha_pos
  c_pos := hcert.c_pos
  d_nonneg := hcert.d_nonneg
  success_first_lt_one := hcert.success_first_lt_one
  likelihood_pos := hcert.likelihood_pos
  weight_pos := by
    intro t
    norm_num
  targetShare_eq := by
    intro t
    rw [uniformProfile_targetShare]
    simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
  base_error := hcert.error
  base_error_nonneg := hcert.error_nonneg
  base_error_tends_to_zero := hcert.error_tends_to_zero
  floor := hcert.floor
  large_gap_marginal_dominance_after_floor := by
    filter_upwards [hcert.growth] with N hgrowth
    intro src dst qsrc qdst hqsrc_leN _hqdst_leN _hqsrc_floor _hqdst_floor hgap
    simp only [div_one] at hgap
    have hgap_nonneg : 0 ≤ hcert.error N * (N : ℝ) :=
      mul_nonneg (hcert.error_nonneg N) (Nat.cast_nonneg N)
    have hdiff_pos :
        0 < (qsrc : ℝ) - (qdst : ℝ) :=
      lt_of_le_of_lt hgap_nonneg hgap
    have hqdst_lt_qsrc : qdst < qsrc := by
      by_contra hnot
      have hle : qsrc ≤ qdst := le_of_not_gt hnot
      have hdiff_nonpos : (qsrc : ℝ) - (qdst : ℝ) ≤ 0 := by
        have hcast : (qsrc : ℝ) ≤ (qdst : ℝ) := by exact_mod_cast hle
        linarith
      exact not_lt_of_ge hdiff_nonpos hdiff_pos
    have hqdst_le_pred : qdst ≤ qsrc - 1 :=
      Nat.le_sub_one_of_lt hqdst_lt_qsrc
    have hqsrc_pos : 0 < qsrc := Nat.lt_of_le_of_lt (Nat.zero_le qdst) hqdst_lt_qsrc
    have hcast_pred :
        ((qsrc - 1 : ℕ) : ℝ) = (qsrc : ℝ) - 1 := by
      rw [Nat.cast_sub (Nat.succ_le_of_lt hqsrc_pos)]
      norm_num
    have hgap_len_gt :
        hcert.error N * (N : ℝ) - 1 <
          ((qsrc - 1 - qdst : ℕ) : ℝ) := by
      rw [Nat.cast_sub hqdst_le_pred, hcast_pred]
      linarith
    have hsuccess_N_pos :
        0 < decayingBernoulliSuccess c d α N :=
      decayingBernoulliSuccess_pos c d α hcert.c_pos hcert.d_nonneg N
    have hgap_success_gt :
        (hcert.error N * (N : ℝ) - 1) *
            decayingBernoulliSuccess c d α N <
          ((qsrc - 1 - qdst : ℕ) : ℝ) *
            decayingBernoulliSuccess c d α N :=
      mul_lt_mul_of_pos_right hgap_len_gt hsuccess_N_pos
    have hqsrc_pred_pred_le_N : qsrc - 1 - 1 ≤ N :=
      le_trans
        (le_trans (Nat.sub_le (qsrc - 1) 1) (Nat.sub_le qsrc 1))
        hqsrc_leN
    have hsuccess_le :
        decayingBernoulliSuccess c d α N ≤
          decayingBernoulliSuccess c d α (qsrc - 1 - 1) :=
      decayingBernoulliSuccess_antitone_of_le
        c d α (le_of_lt hcert.c_pos) hcert.d_nonneg
        (le_of_lt hcert.alpha_pos) hqsrc_pred_pred_le_N
    have hgap_len_nonneg :
        0 ≤ ((qsrc - 1 - qdst : ℕ) : ℝ) := Nat.cast_nonneg _
    have hright_success_ge :
        ((qsrc - 1 - qdst : ℕ) : ℝ) *
            decayingBernoulliSuccess c d α N ≤
          ((qsrc - 1 - qdst : ℕ) : ℝ) *
            decayingBernoulliSuccess c d α (qsrc - 1 - 1) :=
      mul_le_mul_of_nonneg_left hsuccess_le hgap_len_nonneg
    have hlog_bound :
        Real.log (likelihood src / likelihood dst) <
          ((qsrc - 1 - qdst : ℕ) : ℝ) *
            decayingBernoulliSuccess c d α (qsrc - 1 - 1) := by
      have hpair :=
        decayingBernoulliTopOne_log_likelihood_ratio_lt_bound
          likelihood src dst
      exact lt_of_lt_of_le
        (lt_trans hpair hgrowth)
        (le_trans (le_of_lt hgap_success_gt) hright_success_ge)
    exact
      decayingBernoulliTopOne_weighted_marginalCore_lt_of_gap_log_bound
        c d α hcert.c_pos hcert.d_nonneg (le_of_lt hcert.alpha_pos)
        hcert.success_first_lt_one (hcert.likelihood_pos src)
        (hcert.likelihood_pos dst) hqdst_le_pred hlog_bound

theorem asymptoticHomogeneity
    {T : ℕ} [NeZero T] {likelihood : ItemType T → ℝ} {c d α : ℝ}
    (hcert :
      DecayingBernoulliTopOneSubunitGrowthCertificate likelihood c d α) :
    ConsumptionModel.AsymptoticHomogeneity
      (fun _ => decayingBernoulliTopOneConsumptionModel likelihood c d α)
      (uniformProfile T) := hcert.toEventualSublinearFOCCertificate.asymptoticHomogeneity

end DecayingBernoulliTopOneSubunitGrowthCertificate

/--
Certificate for Theorem 2 part (iv), using the actual all-consumed Bernoulli
objective from equation (177).
-/
structure DecayingBernoulliAllConsumedHomogeneityCertificate {T : ℕ}
    (likelihood : ItemType T → ℝ) (c d α : ℝ)
    (G : GammaHomogeneityProfile T) where
  alpha_nonneg : 0 ≤ α
  c_nonneg : 0 ≤ c
  d_nonneg : 0 ≤ d
  asymptotic_homogeneity :
    ConsumptionModel.AsymptoticHomogeneity
      (fun _ => decayingBernoulliAllConsumedConsumptionModel likelihood c d α) G

namespace DecayingBernoulliAllConsumedHomogeneityCertificate

theorem has_nonnegative_marginals {T : ℕ}
    {likelihood : ItemType T → ℝ} {c d α : ℝ}
    {G : GammaHomogeneityProfile T}
    (hcert : DecayingBernoulliAllConsumedHomogeneityCertificate likelihood c d α G) :
    (decayingBernoulliAllConsumedConsumptionModel likelihood c d α).HasNonnegativeMarginals :=
  decayingBernoulliAllConsumedConsumptionModel_has_nonnegative_marginals
    likelihood c d α hcert.c_nonneg hcert.d_nonneg

theorem has_diminishing_returns {T : ℕ}
    {likelihood : ItemType T → ℝ} {c d α : ℝ}
    {G : GammaHomogeneityProfile T}
    (hcert : DecayingBernoulliAllConsumedHomogeneityCertificate likelihood c d α G) :
    (decayingBernoulliAllConsumedConsumptionModel likelihood c d α).HasDiminishingReturns :=
  decayingBernoulliAllConsumedConsumptionModel_has_diminishing_returns
    likelihood c d α hcert.c_nonneg hcert.d_nonneg hcert.alpha_nonneg

end DecayingBernoulliAllConsumedHomogeneityCertificate

/-- Theorem 2(iv)'s all-consumed target weights, proportional to `p_t^(1/α)`. -/
noncomputable def decayingBernoulliAllConsumedTargetWeight {T : ℕ}
    (likelihood : ItemType T → ℝ) (α : ℝ) (t : ItemType T) : ℝ := likelihood t ^ (1 / α)

/--
Finite pairwise-scaled certificate for the all-consumed branch of Theorem 2.

This is the source Lemma D.1(iv)/(ii)/(iii) seam after the scalar asymptotics
for `h(a) = ∑_{i≤a} c(i+d)^(-α)` have been converted into the finite
first-order statement that `count t / p_t^(1/α)` is pairwise bounded.
-/
structure DecayingBernoulliAllConsumedPairwiseScaledCertificate
    {T : ℕ} [NeZero T] (likelihood : ItemType T → ℝ) (c d α : ℝ) where
  alpha_pos : 0 < α
  c_nonneg : 0 ≤ c
  d_nonneg : 0 ≤ d
  target_weight_pos :
    ∀ t, 0 < decayingBernoulliAllConsumedTargetWeight likelihood α t
  scaled_bound : ℝ
  scaled_bound_pos : 0 < scaled_bound
  pairwise_scaled :
    ∀ N (a : CountAllocation T), 0 < N →
      (decayingBernoulliAllConsumedConsumptionModel likelihood c d α).IsOptimalAtTotal
        N a →
      ∀ i j,
        |(a.count i : ℝ) / decayingBernoulliAllConsumedTargetWeight likelihood α i -
          (a.count j : ℝ) / decayingBernoulliAllConsumedTargetWeight likelihood α j| ≤
            scaled_bound

namespace DecayingBernoulliAllConsumedPairwiseScaledCertificate

noncomputable def toPairwiseScaledHomogeneityCertificate
    {T : ℕ} [NeZero T] {likelihood : ItemType T → ℝ} {c d α : ℝ}
    (hcert :
      DecayingBernoulliAllConsumedPairwiseScaledCertificate likelihood c d α) :
    PairwiseScaledHomogeneityCertificate
      (fun _ => decayingBernoulliAllConsumedConsumptionModel likelihood c d α)
      (decayingBernoulliAllConsumedTargetWeight likelihood α)
      (gammaLikelihoodProfile likelihood (1 / α)) := by
  classical
  refine
    { weight_pos := hcert.target_weight_pos
      targetShare_eq := ?_
      scaled_bound := hcert.scaled_bound
      scaled_bound_pos := hcert.scaled_bound_pos
      pairwise_scaled := hcert.pairwise_scaled }
  intro t
  have hnorm_pos :
      0 < (gammaLikelihoodProfile likelihood (1 / α)).normalizer := by
    unfold GammaHomogeneityProfile.normalizer gammaLikelihoodProfile
    exact Finset.sum_pos
      (fun i _ => hcert.target_weight_pos i) Finset.univ_nonempty
  rw [GammaHomogeneityProfile.targetShare_eq_div_of_normalizer_ne_zero
    (G := gammaLikelihoodProfile likelihood (1 / α)) (t := t)
    (ne_of_gt hnorm_pos)]
  rfl

theorem asymptoticHomogeneityTarget
    {T : ℕ} [NeZero T] {likelihood : ItemType T → ℝ} {c d α : ℝ}
    (hcert :
      DecayingBernoulliAllConsumedPairwiseScaledCertificate likelihood c d α) :
    ConsumptionModel.AsymptoticHomogeneityTarget
      (fun _ => decayingBernoulliAllConsumedConsumptionModel likelihood c d α)
      (gammaLikelihoodProfile likelihood (1 / α)) AppliedModelingLib.Math.ExactInvRate :=
  hcert.toPairwiseScaledHomogeneityCertificate.asymptoticHomogeneityTarget

theorem asymptoticHomogeneity
    {T : ℕ} [NeZero T] {likelihood : ItemType T → ℝ} {c d α : ℝ}
    (hcert :
      DecayingBernoulliAllConsumedPairwiseScaledCertificate likelihood c d α) :
    ConsumptionModel.AsymptoticHomogeneity
      (fun _ => decayingBernoulliAllConsumedConsumptionModel likelihood c d α)
      (gammaLikelihoodProfile likelihood (1 / α)) := hcert.toPairwiseScaledHomogeneityCertificate.asymptoticHomogeneity

noncomputable def toHomogeneityCertificate
    {T : ℕ} [NeZero T] {likelihood : ItemType T → ℝ} {c d α : ℝ}
    (hcert :
      DecayingBernoulliAllConsumedPairwiseScaledCertificate likelihood c d α) :
    DecayingBernoulliAllConsumedHomogeneityCertificate likelihood c d α
      (gammaLikelihoodProfile likelihood (1 / α)) where
  alpha_nonneg := le_of_lt hcert.alpha_pos
  c_nonneg := hcert.c_nonneg
  d_nonneg := hcert.d_nonneg
  asymptotic_homogeneity := hcert.asymptoticHomogeneity

end DecayingBernoulliAllConsumedPairwiseScaledCertificate

theorem decayingBernoulliAllConsumed_positive_alpha_scaled_count_sub_le
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (c d α : ℝ) (N : ℕ)
    {a : CountAllocation T}
    (hopt :
      (decayingBernoulliAllConsumedConsumptionModel likelihood c d α).IsOptimalAtTotal
        N a)
    (hα : 0 < α) (hc : 0 < c) (hd : 0 ≤ d)
    (hlike_pos : ∀ t, 0 < likelihood t)
    (src dst : ItemType T) :
    (a.count src : ℝ) / decayingBernoulliAllConsumedTargetWeight likelihood α src -
        (a.count dst : ℝ) / decayingBernoulliAllConsumedTargetWeight likelihood α dst ≤
      (1 + d) *
        ∑ t : ItemType T, 1 / decayingBernoulliAllConsumedTargetWeight likelihood α t := by
  classical
  let weight : ItemType T → ℝ :=
    decayingBernoulliAllConsumedTargetWeight likelihood α
  let C : ℝ := (1 + d) * ∑ t : ItemType T, 1 / weight t
  have hweight_pos : ∀ t, 0 < weight t := by
    intro t
    exact Real.rpow_pos_of_pos (hlike_pos t) (1 / α)
  have hsum_nonneg : 0 ≤ ∑ t : ItemType T, 1 / weight t :=
    Finset.sum_nonneg (fun t _ => div_nonneg zero_le_one
      (le_of_lt (hweight_pos t)))
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (by linarith : 0 ≤ 1 + d) hsum_nonneg
  by_cases hsame : src = dst
  · subst dst
    dsimp [C, weight] at hC_nonneg ⊢
    linarith
  by_cases hsrc_pos : 0 < a.count src
  · have hfoc :=
      ConsumptionModel.weightedForwardMarginal_le_weightedBackwardMarginal_of_optimum
        (M := decayingBernoulliAllConsumedConsumptionModel likelihood c d α)
        N hopt hsame hsrc_pos
    change
      (rankBernoulliAllConsumedConsumptionModel likelihood
          (decayingBernoulliSuccess c d α)).weightedForwardMarginal
          dst (a.count dst) ≤
        (rankBernoulliAllConsumedConsumptionModel likelihood
          (decayingBernoulliSuccess c d α)).weightedBackwardMarginal
          src (a.count src) at hfoc
    rw [rankBernoulliAllConsumedConsumptionModel_weightedForwardMarginal,
      rankBernoulliAllConsumedConsumptionModel_weightedBackwardMarginal
        (hq := hsrc_pos)] at hfoc
    unfold decayingBernoulliSuccess at hfoc
    have hsrc_cancel : a.count src - 1 + 1 = a.count src :=
      Nat.sub_add_cancel (Nat.succ_le_of_lt hsrc_pos)
    simp [hsrc_cancel] at hfoc
    have hx_pos : 0 < (a.count src : ℝ) + d := by
      positivity
    have hy_pos : 0 < ((a.count dst : ℝ) + 1 + d) := by
      positivity
    have hscaled :
        ((a.count src : ℝ) + d) / weight src ≤
          ((a.count dst : ℝ) + 1 + d) / weight dst := by
      dsimp [weight, decayingBernoulliAllConsumedTargetWeight]
      exact
        scaled_le_of_rpow_neg_marginal_le
          (hp_src := hlike_pos src) (hp_dst := hlike_pos dst)
          (hc := hc) (hα := hα) (hx := hx_pos) (hy := hy_pos) hfoc
    have hscaled' :
        (a.count src : ℝ) / weight src + d / weight src ≤
          (a.count dst : ℝ) / weight dst + (1 + d) / weight dst := by
      convert hscaled using 1 <;> ring_nf
    have hd_div_nonneg : 0 ≤ d / weight src :=
      div_nonneg hd (le_of_lt (hweight_pos src))
    have hupper :
        (a.count src : ℝ) / weight src -
            (a.count dst : ℝ) / weight dst ≤
          (1 + d) / weight dst := by
      linarith
    have hinv_le_sum :
        1 / weight dst ≤ ∑ t : ItemType T, 1 / weight t :=
      Finset.single_le_sum
        (fun t _ => div_nonneg zero_le_one (le_of_lt (hweight_pos t)))
        (Finset.mem_univ dst)
    have htail :
        (1 + d) / weight dst ≤ C := by
      dsimp [C]
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        mul_le_mul_of_nonneg_left hinv_le_sum (by linarith : 0 ≤ 1 + d)
    exact le_trans hupper htail
  · have hsrc_zero : a.count src = 0 := Nat.eq_zero_of_not_pos hsrc_pos
    have hdst_nonneg : 0 ≤ (a.count dst : ℝ) / weight dst :=
      div_nonneg (Nat.cast_nonneg _) (le_of_lt (hweight_pos dst))
    dsimp [C, weight] at hC_nonneg ⊢
    rw [hsrc_zero]
    simp only [Nat.cast_zero, zero_div, zero_sub]
    exact le_trans (neg_nonpos.mpr hdst_nonneg) hC_nonneg

theorem decayingBernoulliAllConsumed_positive_alpha_pairwise_scaled_abs_le
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (c d α : ℝ) (N : ℕ)
    {a : CountAllocation T}
    (hopt :
      (decayingBernoulliAllConsumedConsumptionModel likelihood c d α).IsOptimalAtTotal
        N a)
    (hα : 0 < α) (hc : 0 < c) (hd : 0 ≤ d)
    (hlike_pos : ∀ t, 0 < likelihood t)
    (i j : ItemType T) :
    |(a.count i : ℝ) / decayingBernoulliAllConsumedTargetWeight likelihood α i -
        (a.count j : ℝ) / decayingBernoulliAllConsumedTargetWeight likelihood α j| ≤
      (1 + d) *
        ∑ t : ItemType T, 1 / decayingBernoulliAllConsumedTargetWeight likelihood α t := by
  rw [abs_le]
  constructor
  · have hji :=
      decayingBernoulliAllConsumed_positive_alpha_scaled_count_sub_le
        likelihood c d α N hopt hα hc hd hlike_pos j i
    linarith
  · exact
      decayingBernoulliAllConsumed_positive_alpha_scaled_count_sub_le
        likelihood c d α N hopt hα hc hd hlike_pos i j

noncomputable def
    decayingBernoulliAllConsumedPairwiseScaledCertificate_of_positive_parameters
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (c d α : ℝ)
    (hα : 0 < α) (hc : 0 < c) (hd : 0 ≤ d)
    (hlike_pos : ∀ t, 0 < likelihood t) :
    DecayingBernoulliAllConsumedPairwiseScaledCertificate likelihood c d α where
  alpha_pos := hα
  c_nonneg := le_of_lt hc
  d_nonneg := hd
  target_weight_pos := by
    intro t
    exact Real.rpow_pos_of_pos (hlike_pos t) (1 / α)
  scaled_bound :=
    (1 + d) *
      ∑ t : ItemType T, 1 / decayingBernoulliAllConsumedTargetWeight likelihood α t
  scaled_bound_pos :=
    mul_pos (by linarith : 0 < 1 + d)
      (Finset.sum_pos
        (fun t _ =>
          one_div_pos.mpr
            (Real.rpow_pos_of_pos (hlike_pos t) (1 / α)))
        Finset.univ_nonempty)
  pairwise_scaled := by
    intro N a _hN hopt i j
    exact
      decayingBernoulliAllConsumed_positive_alpha_pairwise_scaled_abs_le
        likelihood c d α N hopt hα hc hd hlike_pos i j

theorem decayingBernoulliAllConsumed_alpha_one_scaled_count_sub_le
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (c d : ℝ) (N : ℕ)
    {a : CountAllocation T}
    (hopt :
      (decayingBernoulliAllConsumedConsumptionModel likelihood c d 1).IsOptimalAtTotal
        N a)
    (hc : 0 < c) (hd : 0 ≤ d)
    (hlike_pos : ∀ t, 0 < likelihood t)
    (src dst : ItemType T) :
    (a.count src : ℝ) / likelihood src -
        (a.count dst : ℝ) / likelihood dst ≤
      (1 + d) * ∑ t : ItemType T, 1 / likelihood t := by
  classical
  let C : ℝ := (1 + d) * ∑ t : ItemType T, 1 / likelihood t
  have hsum_nonneg : 0 ≤ ∑ t : ItemType T, 1 / likelihood t :=
    Finset.sum_nonneg (fun t _ => div_nonneg zero_le_one
      (le_of_lt (hlike_pos t)))
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (by linarith : 0 ≤ 1 + d) hsum_nonneg
  by_cases hsame : src = dst
  · subst dst
    dsimp [C] at hC_nonneg ⊢
    linarith
  by_cases hsrc_pos : 0 < a.count src
  · have hfoc :=
      ConsumptionModel.weightedForwardMarginal_le_weightedBackwardMarginal_of_optimum
        (M := decayingBernoulliAllConsumedConsumptionModel likelihood c d 1)
        N hopt hsame hsrc_pos
    change
      (rankBernoulliAllConsumedConsumptionModel likelihood
          (decayingBernoulliSuccess c d 1)).weightedForwardMarginal
          dst (a.count dst) ≤
        (rankBernoulliAllConsumedConsumptionModel likelihood
          (decayingBernoulliSuccess c d 1)).weightedBackwardMarginal
          src (a.count src) at hfoc
    rw [rankBernoulliAllConsumedConsumptionModel_weightedForwardMarginal,
      rankBernoulliAllConsumedConsumptionModel_weightedBackwardMarginal
        (hq := hsrc_pos)] at hfoc
    rw [decayingBernoulliSuccess_one c d hd,
      decayingBernoulliSuccess_one c d hd] at hfoc
    have hsrc_cancel : a.count src - 1 + 1 = a.count src :=
      Nat.sub_add_cancel (Nat.succ_le_of_lt hsrc_pos)
    simp [hsrc_cancel] at hfoc
    have hx_pos : 0 < (a.count src : ℝ) + d := by
      positivity
    have hy_pos : 0 < ((a.count dst : ℝ) + 1 + d) := by
      positivity
    have hscaled :
        ((a.count src : ℝ) + d) / likelihood src ≤
          ((a.count dst : ℝ) + 1 + d) / likelihood dst :=
      scaled_le_of_inverse_marginal_le
        (hp_src := hlike_pos src) (hp_dst := hlike_pos dst)
        (hc := hc) (hx := hx_pos) (hy := hy_pos) hfoc
    have hscaled' :
        (a.count src : ℝ) / likelihood src + d / likelihood src ≤
          (a.count dst : ℝ) / likelihood dst +
            (1 + d) / likelihood dst := by
      convert hscaled using 1 <;> ring_nf
    have hd_div_nonneg : 0 ≤ d / likelihood src :=
      div_nonneg hd (le_of_lt (hlike_pos src))
    have hupper :
        (a.count src : ℝ) / likelihood src -
            (a.count dst : ℝ) / likelihood dst ≤
          (1 + d) / likelihood dst := by
      linarith
    have hinv_le_sum :
        1 / likelihood dst ≤ ∑ t : ItemType T, 1 / likelihood t :=
      Finset.single_le_sum
        (fun t _ => div_nonneg zero_le_one (le_of_lt (hlike_pos t)))
        (Finset.mem_univ dst)
    have htail :
        (1 + d) / likelihood dst ≤ C := by
      dsimp [C]
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        mul_le_mul_of_nonneg_left hinv_le_sum (by linarith : 0 ≤ 1 + d)
    exact le_trans hupper htail
  · have hsrc_zero : a.count src = 0 := Nat.eq_zero_of_not_pos hsrc_pos
    have hdst_nonneg : 0 ≤ (a.count dst : ℝ) / likelihood dst :=
      div_nonneg (Nat.cast_nonneg _) (le_of_lt (hlike_pos dst))
    dsimp [C] at hC_nonneg ⊢
    rw [hsrc_zero]
    simp only [Nat.cast_zero, zero_div, zero_sub]
    exact le_trans (neg_nonpos.mpr hdst_nonneg) hC_nonneg

theorem decayingBernoulliAllConsumed_alpha_one_pairwise_scaled_abs_le
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (c d : ℝ) (N : ℕ)
    {a : CountAllocation T}
    (hopt :
      (decayingBernoulliAllConsumedConsumptionModel likelihood c d 1).IsOptimalAtTotal
        N a)
    (hc : 0 < c) (hd : 0 ≤ d)
    (hlike_pos : ∀ t, 0 < likelihood t)
    (i j : ItemType T) :
    |(a.count i : ℝ) / likelihood i -
        (a.count j : ℝ) / likelihood j| ≤
      (1 + d) * ∑ t : ItemType T, 1 / likelihood t := by
  rw [abs_le]
  constructor
  · have hji :=
      decayingBernoulliAllConsumed_alpha_one_scaled_count_sub_le
        likelihood c d N hopt hc hd hlike_pos j i
    linarith
  · exact
      decayingBernoulliAllConsumed_alpha_one_scaled_count_sub_le
        likelihood c d N hopt hc hd hlike_pos i j

noncomputable def decayingBernoulliAllConsumedPairwiseScaledCertificate_alpha_one
    {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (c d : ℝ)
    (hc : 0 < c) (hd : 0 ≤ d)
    (hlike_pos : ∀ t, 0 < likelihood t) :
    DecayingBernoulliAllConsumedPairwiseScaledCertificate likelihood c d 1 where
  alpha_pos := by norm_num
  c_nonneg := le_of_lt hc
  d_nonneg := hd
  target_weight_pos := by
    intro t
    simpa [decayingBernoulliAllConsumedTargetWeight] using hlike_pos t
  scaled_bound := (1 + d) * ∑ t : ItemType T, 1 / likelihood t
  scaled_bound_pos :=
    mul_pos (by linarith : 0 < 1 + d)
      (Finset.sum_pos
        (fun t _ => one_div_pos.mpr (hlike_pos t)) Finset.univ_nonempty)
  pairwise_scaled := by
    intro N a _hN hopt i j
    simpa [decayingBernoulliAllConsumedTargetWeight] using
      decayingBernoulliAllConsumed_alpha_one_pairwise_scaled_abs_le
        likelihood c d N hopt hc hd hlike_pos i j

end PRPKG24AccuracyDiversity

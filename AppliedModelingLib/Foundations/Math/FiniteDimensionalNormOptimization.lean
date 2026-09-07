import AppliedModelingLib.Foundations.Math.FiniteDimensionalNorms

/-!
# Finite-Dimensional Norm Optimization

Reusable optimization consequences for the explicit finite-coordinate norm
formulas. Keeping these higher-level power-mean, Lipschitz, compactness, and
AM--GM results outside the foundational norm container prevents a new paper
from changing the import bytes of every existing client of the basic formulas.
-/

open Filter
open scoped BigOperators

namespace AppliedModelingLib
namespace FiniteDimensionalNorms

noncomputable section

/--
Weighted power mean written in the form needed for finite-dimensional `Lp`
convexification: the weights need not be normalized in the definition.
-/
def weightedPowerMean {κ : Type*} [Fintype κ]
    (p : ℝ) (w x : κ → ℝ) : ℝ :=
  (∑ k, w k * (x k) ^ p) ^ p⁻¹

theorem weightedPowerMean_nonneg {κ : Type*} [Fintype κ]
    {p : ℝ} {w x : κ → ℝ}
    (hw : ∀ k, 0 ≤ w k) (hx : ∀ k, 0 ≤ x k) :
    0 ≤ weightedPowerMean p w x := by
  unfold weightedPowerMean
  exact Real.rpow_nonneg
    (Finset.sum_nonneg fun k _ => mul_nonneg (hw k) (Real.rpow_nonneg (hx k) p)) _

/-- Raising a nonnegative weighted power mean back to its nonzero exponent
recovers the weighted power sum. -/
theorem weightedPowerMean_rpow {κ : Type*} [Fintype κ]
    {p : ℝ} {w x : κ → ℝ}
    (hp : p ≠ 0) (hw : ∀ k, 0 ≤ w k) (hx : ∀ k, 0 ≤ x k) :
    (weightedPowerMean p w x) ^ p = ∑ k, w k * (x k) ^ p := by
  unfold weightedPowerMean
  exact Real.rpow_inv_rpow
    (Finset.sum_nonneg fun k _ => mul_nonneg (hw k) (Real.rpow_nonneg (hx k) p)) hp

/--
A weighted power mean is the finite `Lp` norm of the vector obtained by
scaling coordinate `k` by `w(k)^(1/p)`.  This is the finite-dimensional form
of the weighted Minkowski construction.
-/
theorem weightedPowerMean_eq_lp_weighted {κ : Type*} [Fintype κ]
    {p : ℝ} {w x : κ → ℝ}
    (hp : 0 < p) (hw : ∀ k, 0 ≤ w k) (hx : ∀ k, 0 ≤ x k) :
    weightedPowerMean p w x =
      lp p (fun k => (w k) ^ p⁻¹ * x k) := by
  have hp_ne : p ≠ 0 := ne_of_gt hp
  have hsum :
      (∑ k, |(w k) ^ p⁻¹ * x k| ^ p) =
        ∑ k, w k * (x k) ^ p := by
    refine Finset.sum_congr rfl ?_
    intro k _hk
    have hfactor_nonnegative : 0 ≤ (w k) ^ p⁻¹ * x k :=
      mul_nonneg (Real.rpow_nonneg (hw k) _) (hx k)
    rw [abs_of_nonneg hfactor_nonnegative, Real.mul_rpow
      (Real.rpow_nonneg (hw k) _) (hx k),
      Real.rpow_inv_rpow (hw k) hp_ne]
  unfold weightedPowerMean lp lpPower
  rw [hsum, one_div]

/--
The finite-coordinate dot product is Lipschitz in its second input for the
ambient product metric, with the explicit `L1` norm of the first input as
Lipschitz constant.
-/
theorem dot_le_dot_add_l1_mul_dist
    {ι : Type*} [Fintype ι] (u x y : ι → ℝ) :
    dot u x ≤ dot u y + l1 u * dist x y := by
  have hcoord : ∀ i : ι,
      u i * (x i - y i) ≤ |u i| * dist x y := by
    intro i
    calc
      u i * (x i - y i) ≤ |u i * (x i - y i)| := le_abs_self _
      _ = |u i| * |x i - y i| := abs_mul _ _
      _ = |u i| * dist (x i) (y i) := by rw [Real.dist_eq]
      _ ≤ |u i| * dist x y :=
        mul_le_mul_of_nonneg_left (dist_le_pi_dist x y i) (abs_nonneg _)
  have hsum :
      (∑ i : ι, u i * (x i - y i)) ≤
        ∑ i : ι, |u i| * dist x y := by
    apply Finset.sum_le_sum
    intro i _
    exact hcoord i
  calc
    dot u x = dot u y + ∑ i : ι, u i * (x i - y i) := by
      unfold dot
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ dot u y + ∑ i : ι, |u i| * dist x y :=
      add_le_add (le_refl (dot u y)) hsum
    _ = dot u y + l1 u * dist x y := by
      rw [l1, Finset.sum_mul]

/--
The finite-coordinate dot product is Lipschitz in its second input for the
Euclidean `L2` distance.  This is the Cauchy--Schwarz form used when a source
paper specifies the Euclidean rather than the ambient product metric.
-/
theorem dot_le_dot_add_l2_mul_l2_sub
    {ι : Type*} [Fintype ι] (u x y : ι → ℝ) :
    dot u x ≤ dot u y + l2 u * l2 (fun i => x i - y i) := by
  have hdot := abs_dot_le_l2_mul_l2 u (fun i => x i - y i)
  calc
    dot u x = dot u y + dot u (fun i => x i - y i) := by
      unfold dot
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ dot u y + l2 u * l2 (fun i => x i - y i) := by
      apply add_le_add (le_refl _)
      exact (le_abs_self _).trans hdot

/--
The nonnegative finite-coordinate `Lp` unit ball is compact for positive
exponent.  This packages the finite-dimensional compactness needed when a
paper writes a maximum over a nonnegative `Lp` feasible region.
-/
theorem isCompact_nonnegative_lp_closedBall
    {ι : Type*} [Fintype ι] {p : ℝ} (hp : 0 < p) :
    IsCompact {x : ι → ℝ | (∀ i, 0 ≤ x i) ∧ lp p x ≤ 1} := by
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  constructor
  · have hnonnegative : IsClosed {x : ι → ℝ | ∀ i, 0 ≤ x i} := by
      rw [show {x : ι → ℝ | ∀ i, 0 ≤ x i} =
          ⋂ i : ι, (fun x : ι → ℝ => x i) ⁻¹' Set.Ici 0 by
            ext x
            simp]
      exact isClosed_iInter fun i =>
        isClosed_Ici.preimage (continuous_apply i)
    have hball : IsClosed {x : ι → ℝ | lp p x ≤ 1} :=
      isClosed_Iic.preimage (continuous_lp hp.le)
    exact hnonnegative.inter hball
  · rw [Metric.isBounded_iff_subset_closedBall (0 : ι → ℝ)]
    refine ⟨1, ?_⟩
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg (x := x) zero_le_one).mpr
    intro i
    rw [Real.norm_eq_abs]
    exact (abs_le_lp hp x i).trans hx.2

/--
Minkowski's inequality for the explicit finite-coordinate `Lp` quantity at a
real exponent at least one.  The proof transports the finite sum formula to
mathlib's finite `PiLp` norm, so it is usable with real-valued exponents in
source mathematical models.
-/
theorem lp_add_le
    {ι : Type*} [Fintype ι] {p : ℝ} (hp : 1 ≤ p)
    (x y : ι → ℝ) :
    lp p (fun i => x i + y i) ≤ lp p x + lp p y := by
  let pE : ENNReal := ENNReal.ofReal p
  have hp_nonneg : 0 ≤ p := le_trans zero_le_one hp
  have hp_toReal : pE.toReal = p := by
    dsimp [pE]
    exact ENNReal.toReal_ofReal hp_nonneg
  have hpE : (1 : ENNReal) ≤ pE := by
    dsimp [pE]
    simpa using (ENNReal.ofReal_le_ofReal hp)
  letI : Fact ((1 : ENNReal) ≤ pE) := ⟨hpE⟩
  let E : Type _ := @PiLp pE ι (fun _ => ℝ)
  let toE : (ι → ℝ) → E := WithLp.toLp pE
  have hnorm (z : ι → ℝ) : lp p z = ‖toE z‖ := by
    rw [← hp_toReal]
    exact lp_toReal_eq_piLp_norm pE
      (by rw [hp_toReal]; exact lt_of_lt_of_le zero_lt_one hp) z
  calc
    lp p (fun i => x i + y i) = ‖toE (fun i => x i + y i)‖ := hnorm _
    _ = ‖toE x + toE y‖ := by
      change ‖WithLp.toLp pE (fun i => x i + y i)‖ =
        ‖WithLp.toLp pE x + WithLp.toLp pE y‖
      change ‖WithLp.toLp pE (x + y)‖ =
        ‖WithLp.toLp pE x + WithLp.toLp pE y‖
      rw [← WithLp.toLp_add]
    _ ≤ ‖toE x‖ + ‖toE y‖ := norm_add_le _ _
    _ = lp p x + lp p y := by rw [← hnorm x, ← hnorm y]

/-- A finite-coordinate `Lp` norm of a finite vector sum is at most the sum of
the coordinate `Lp` norms, for real exponents at least one. -/
theorem lp_finset_sum_le
    {ι κ : Type*} [Fintype ι] {p : ℝ} (hp : 1 ≤ p)
    (s : Finset κ) (f : κ → ι → ℝ) :
    lp p (fun j => ∑ k ∈ s, f k j) ≤ ∑ k ∈ s, lp p (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [show (fun j : ι => ∑ k ∈ (∅ : Finset κ), f k j) = fun _ => 0 by
        ext j
        simp]
      rw [lp_zero_of_pos (lt_of_lt_of_le zero_lt_one hp)]
      simp
  | insert a s ha ih =>
      calc
        lp p (fun j => ∑ k ∈ insert a s, f k j)
            = lp p (fun j => f a j + ∑ k ∈ s, f k j) := by
                congr 1
                ext j
                simp [ha]
        _ ≤ lp p (f a) + lp p (fun j => ∑ k ∈ s, f k j) :=
          lp_add_le hp _ _
        _ ≤ lp p (f a) + ∑ k ∈ s, lp p (f k) :=
          add_le_add_right ih _
        _ = ∑ k ∈ insert a s, lp p (f k) := by simp [ha]

/-- A finite `Lp` unit-ball bound implies the corresponding power-sum bound. -/
theorem lpPower_le_one_of_lp_le_one
    {ι : Type*} [Fintype ι] {p : ℝ} (hp : 0 < p)
    (x : ι → ℝ) (hx : lp p x ≤ 1) :
    lpPower p x ≤ 1 := by
  have hpower_nonnegative : 0 ≤ lpPower p x := lpPower_nonneg p x
  have hx' : (lpPower p x) ^ p⁻¹ ≤ 1 := by
    simpa [lp, one_div] using hx
  have h :=
    (Real.rpow_inv_le_iff_of_pos hpower_nonnegative zero_le_one hp).mp hx'
  simpa using h

/--
AM--GM product bound for a nonnegative finite `Lp` unit-ball vector.  It is
stated for the `p`th powers because that is the form used by powered-image
optimization problems.
-/
theorem prod_rpow_le_card_inv_rpow_card_of_lp_le_one
    {ι : Type*} [Fintype ι] [Nonempty ι] {p : ℝ}
    (hp : 0 < p) {x : ι → ℝ}
    (hx_nonnegative : ∀ i, 0 ≤ x i) (hx_ball : lp p x ≤ 1) :
    (∏ i, (x i) ^ p) ≤
      (1 / (Fintype.card ι : ℝ)) ^ (Fintype.card ι : ℝ) := by
  let n : ℝ := Fintype.card ι
  let z : ι → ℝ := fun i => (x i) ^ p
  have hn_pos : 0 < n := by
    dsimp [n]
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance)
  have hn_ne : n ≠ 0 := ne_of_gt hn_pos
  have hz_nonnegative : ∀ i, 0 ≤ z i :=
    fun i => Real.rpow_nonneg (hx_nonnegative i) p
  have hsum_eq_power : (∑ i, z i) = lpPower p x := by
    unfold z lpPower
    refine Finset.sum_congr rfl ?_
    intro i _hi
    rw [abs_of_nonneg (hx_nonnegative i)]
  have hsum_le_one : ∑ i, z i ≤ 1 := by
    rw [hsum_eq_power]
    exact lpPower_le_one_of_lp_le_one hp x hx_ball
  have hamgm := Real.geom_mean_le_arith_mean
    (Finset.univ : Finset ι) (fun _ : ι => (1 : ℝ)) z
    (fun _ _ => zero_le_one) (by simpa [n] using hn_pos) (fun i _ => hz_nonnegative i)
  have hgeom : (∏ i, z i) ^ n⁻¹ ≤ (∑ i, z i) / n := by
    simpa [n, Finset.sum_const, nsmul_eq_mul] using hamgm
  have hmean_le : (∑ i, z i) / n ≤ 1 / n :=
    (div_le_div_iff_of_pos_right hn_pos).mpr hsum_le_one
  have hprod_nonnegative : 0 ≤ ∏ i, z i :=
    Finset.prod_nonneg fun i _ => hz_nonnegative i
  have hgeom_nonnegative : 0 ≤ (∏ i, z i) ^ n⁻¹ :=
    Real.rpow_nonneg hprod_nonnegative _
  have hraised := Real.rpow_le_rpow hgeom_nonnegative
    (hgeom.trans hmean_le) hn_pos.le
  have hleft : ((∏ i, z i) ^ n⁻¹) ^ n = ∏ i, z i :=
    Real.rpow_inv_rpow hprod_nonnegative hn_ne
  have hright : ((1 / n) ^ n) =
      (1 / (Fintype.card ι : ℝ)) ^ (Fintype.card ι : ℝ) := by
    rfl
  change (∏ i, z i) ≤
    (1 / (Fintype.card ι : ℝ)) ^ (Fintype.card ι : ℝ)
  rw [← hleft, ← hright]
  exact hraised

/--
Strict powered-product version of the finite `Lp` AM--GM bound.  Once the
power exponent exceeds the `Lp` exponent, every nonnegative unit-ball vector
has product strictly below the coordinate-uniform benchmark.
-/
theorem prod_rpow_lt_card_inv_rpow_card_of_lp_le_one
    {ι : Type*} [Fintype ι] [Nontrivial ι] {p beta : ℝ}
    (hp : 0 < p) (hbeta : p < beta) {x : ι → ℝ}
    (hx_nonnegative : ∀ i, 0 ≤ x i) (hx_ball : lp p x ≤ 1) :
    (∏ i, (x i) ^ beta) <
      (1 / (Fintype.card ι : ℝ)) ^ (Fintype.card ι : ℝ) := by
  let n : ℝ := Fintype.card ι
  let A : ℝ := ∏ i, (x i) ^ p
  let B : ℝ := (1 / n) ^ n
  have hn_pos : 0 < n := by
    dsimp [n]
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance)
  have hn_one_lt : 1 < n := by
    dsimp [n]
    exact_mod_cast (Fintype.one_lt_card_iff_nontrivial.mpr inferInstance)
  have hbase_pos : 0 < 1 / n := one_div_pos.mpr hn_pos
  have hbase_lt_one : 1 / n < 1 := (div_lt_one hn_pos).mpr hn_one_lt
  have hA_nonnegative : 0 ≤ A := by
    dsimp [A]
    exact Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hx_nonnegative i) p
  have hA_le_B : A ≤ B := by
    dsimp [A, B, n]
    exact prod_rpow_le_card_inv_rpow_card_of_lp_le_one hp hx_nonnegative hx_ball
  have hratio_pos : 0 < beta / p := div_pos (lt_trans hp hbeta) hp
  have hratio_gt_one : 1 < beta / p := by
    rw [lt_div_iff₀ hp]
    simpa using hbeta
  have hA_power_le : A ^ (beta / p) ≤ B ^ (beta / p) :=
    Real.rpow_le_rpow hA_nonnegative hA_le_B hratio_pos.le
  have hexponent_lt : n < n * (beta / p) := by
    simpa [one_mul] using mul_lt_mul_of_pos_left hratio_gt_one hn_pos
  have hB_power_lt : B ^ (beta / p) < B := by
    have hB_expand : B ^ (beta / p) =
        (1 / n) ^ (n * (beta / p)) := by
      dsimp [B]
      rw [Real.rpow_mul (le_of_lt hbase_pos)]
    have hB : B = (1 / n) ^ n := rfl
    rw [hB_expand, hB]
    exact Real.rpow_lt_rpow_of_exponent_gt hbase_pos hbase_lt_one hexponent_lt
  have hprod_eq : (∏ i, (x i) ^ beta) = A ^ (beta / p) := by
    calc
      (∏ i, (x i) ^ beta) = ∏ i, ((x i) ^ p) ^ (beta / p) := by
        refine Finset.prod_congr rfl ?_
        intro i _hi
        rw [← Real.rpow_mul (hx_nonnegative i)]
        field_simp [hp.ne']
      _ = A ^ (beta / p) := by
        dsimp [A]
        exact Real.finset_prod_rpow Finset.univ (fun i => (x i) ^ p)
          (fun i _ => Real.rpow_nonneg (hx_nonnegative i) p) _
  calc
    (∏ i, (x i) ^ beta) = A ^ (beta / p) := hprod_eq
    _ ≤ B ^ (beta / p) := hA_power_le
    _ < B := hB_power_lt
    _ = (1 / (Fintype.card ι : ℝ)) ^ (Fintype.card ι : ℝ) := by rfl

end

end FiniteDimensionalNorms
end AppliedModelingLib

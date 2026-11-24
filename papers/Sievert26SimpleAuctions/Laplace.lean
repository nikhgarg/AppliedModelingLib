import Sievert26SimpleAuctions.LayerCake

/-!
Grand-bundle revenue controls the Laplace transform of the total value, hence a linear functional
of the item tails (Giannakopoulos–Hahn, Lemma 4.5).
-/
set_option linter.deprecated false
open Finset MeasureTheory

namespace Sievert26SimpleAuctions
namespace UB

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem integral_exp (lam z : ℝ) :
    ∫ u in (0:ℝ)..z, lam * Real.exp (-(lam * u)) = 1 - Real.exp (-(lam * z)) := by
  have h : ∀ x ∈ Set.uIcc 0 z,
      HasDerivAt (fun u => -Real.exp (-(lam * u))) (lam * Real.exp (-(lam * x))) x := by
    intro x _
    have h1 : HasDerivAt (fun u => -(lam * u)) (-lam) x := by
      have := ((hasDerivAt_id' x).const_mul lam).fun_neg
      rwa [mul_one] at this
    have h2 := (h1.exp).fun_neg
    convert h2 using 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp; ring

/-- the tangent property of one exponential scale -/
def Tangent (kap b : ℝ) : Prop := ∀ y T : ℝ, 0 < y → 1 ≤ T →
  Real.exp (-(kap + b * y)) ≤
    Real.exp (-y) - y * ∫ x in (1:ℝ)..T, Real.exp (-(y * x)) / x

theorem bundle_antitone (D : ι → FinDist) : Antitone (bundleTail D) := by
  intro p q hpq
  unfold bundleTail
  refine sum_le_sum fun ω _ => ?_
  by_cases h : q ≤ ∑ i, value D ω i
  · rw [if_pos h, if_pos (hpq.trans h)]
  · rw [if_neg h]; split_ifs
    · exact prob_nonneg D ω
    · exact le_rfl

theorem bundle_le_one (D : ι → FinDist) (p : ℝ) : bundleTail D p ≤ 1 := by
  unfold bundleTail
  calc _ ≤ ∑ ω : Profile D, prob D ω := by
        refine sum_le_sum fun ω _ => ?_
        split_ifs
        · exact le_rfl
        · exact prob_nonneg D ω
    _ = 1 := prob_sum D

/-- lower bound on the Laplace transform of the total value -/
theorem laplace_lower (D : ι → FinDist) (hB : 0 < BREV D) (lam kap b : ℝ) (hl : 0 < lam)
    (hT : Tangent kap b) :
    Real.exp (-(kap + b * (lam * BREV D))) ≤
      Ex D (fun ω => Real.exp (-(lam * ∑ i, value D ω i))) := by
  set B := BREV D with hBdef
  set K := B + ∑ i, ∑ k, (D i).val k with hK
  have hZ : ∀ ω : Profile D, ∑ i, value D ω i ≤ K := by
    intro ω
    have : ∑ i, value D ω i ≤ ∑ i, ∑ k, (D i).val k :=
      sum_le_sum fun i _ => single_le_sum (f := fun k => (D i).val k)
        (fun k _ => (D i).val_nonneg k) (mem_univ (ω i))
    linarith
  have hZ0 : ∀ ω : Profile D, 0 ≤ ∑ i, value D ω i :=
    fun ω => sum_nonneg fun i _ => value_nonneg D ω i
  have hBK : B ≤ K := by
    have : 0 ≤ ∑ i, ∑ k, (D i).val k :=
      sum_nonneg fun i _ => sum_nonneg fun k _ => (D i).val_nonneg k
    linarith
  have hK0 : 0 ≤ K := hB.le.trans hBK
  set f : ℝ → ℝ := fun u => lam * Real.exp (-(lam * u)) with hf
  have hfc : Continuous f := by rw [hf]; fun_prop
  have hf0 : ∀ u, 0 ≤ f u := fun u => by rw [hf]; positivity
  -- 1 - E e^{-λZ} as an integral
  have h1 : Ex D (fun ω => 1 - Real.exp (-(lam * ∑ i, value D ω i))) =
      ∫ u in (0:ℝ)..K, bundleTail D u * f u := by
    have e1 : ∀ ω : Profile D, 1 - Real.exp (-(lam * ∑ i, value D ω i)) =
        ∫ u in (0:ℝ)..K, ind (∑ i, value D ω i) u * f u := by
      intro ω
      rw [integral_ind_mul _ K hK0 (hZ ω) f (fun p q _ _ => hfc.intervalIntegrable p q),
        max_eq_left (hZ0 ω), hf, integral_exp]
    unfold Ex
    simp_rw [e1]
    have hii : ∀ ω : Profile D, IntervalIntegrable
        (fun u => ind (∑ i, value D ω i) u * f u) volume 0 K :=
      fun ω => ind_integrable _ _ _ f (hfc.intervalIntegrable _ _)
    have e2 : ∀ ω : Profile D, prob D ω * ∫ u in (0:ℝ)..K, ind (∑ i, value D ω i) u * f u =
        ∫ u in (0:ℝ)..K, prob D ω * (ind (∑ i, value D ω i) u * f u) :=
      fun ω => (intervalIntegral.integral_const_mul _ _).symm
    simp_rw [e2]
    rw [← intervalIntegral.integral_finset_sum (fun ω _ => (hii ω).const_mul _)]
    refine intervalIntegral.integral_congr fun u _ => ?_
    rw [bundleTail_eq, Ex, sum_mul]
    refine sum_congr rfl fun ω _ => ?_
    unfold ind; ring
  -- bound the integral
  have hbi : ∀ p q, IntervalIntegrable (fun u => bundleTail D u * f u) volume p q := by
    intro p q
    exact ((bundle_antitone D).intervalIntegrable).mul_continuousOn hfc.continuousOn
  have h2 : ∫ u in (0:ℝ)..B, bundleTail D u * f u ≤ 1 - Real.exp (-(lam * B)) := by
    rw [← integral_exp]
    refine intervalIntegral.integral_mono_on hB.le (hbi _ _) (hfc.intervalIntegrable _ _) ?_
    intro u _
    have := mul_le_mul_of_nonneg_right (bundle_le_one D u) (hf0 u)
    rw [one_mul] at this; exact this
  have h3 : ∫ u in B..K, bundleTail D u * f u ≤ ∫ u in B..K, B / u * f u := by
    refine intervalIntegral.integral_mono_on hBK (hbi _ _) ?_ ?_
    · refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hBK]
      refine ContinuousOn.mul (ContinuousOn.div continuousOn_const continuousOn_id ?_)
        hfc.continuousOn
      intro x hx; exact (lt_of_lt_of_le hB hx.1).ne'
    · intro u hu
      have hu0 : 0 < u := lt_of_lt_of_le hB hu.1
      refine mul_le_mul_of_nonneg_right ?_ (hf0 u)
      rw [le_div_iff₀ hu0, mul_comm]
      exact mul_bundle_le D u hu0.le
  have h4 : ∫ u in B..K, B / u * f u =
      (lam * B) * ∫ x in (1:ℝ)..(K / B), Real.exp (-((lam * B) * x)) / x := by
    have h := intervalIntegral.integral_comp_mul_left (a := 1) (b := K / B)
      (fun u => B / u * f u) hB.ne'
    rw [mul_one, mul_div_cancel₀ K hB.ne', smul_eq_mul] at h
    have h' : ∫ u in B..K, B / u * f u = B * ∫ x in (1:ℝ)..(K/B), B / (B * x) * f (B * x) := by
      rw [h, ← mul_assoc, mul_inv_cancel₀ hB.ne', one_mul]
    rw [h', ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le (by rw [le_div_iff₀ hB]; linarith)] at hx
    have hx0 : 0 < x := lt_of_lt_of_le one_pos hx.1
    simp only [hf]
    rw [show lam * (B * x) = lam * B * x by ring]
    field_simp
  have h5 := hT (lam * B) (K / B) (mul_pos hl hB) (by rw [le_div_iff₀ hB]; linarith)
  have h6 : Ex D (fun ω => 1 - Real.exp (-(lam * ∑ i, value D ω i))) =
      1 - Ex D (fun ω => Real.exp (-(lam * ∑ i, value D ω i))) := by
    rw [Ex_sub, Ex_const]
  rw [h6, ← intervalIntegral.integral_add_adjacent_intervals (hbi 0 B) (hbi B K)] at h1
  linarith

/-- the linear functional of the item values controlled by `BREV` -/
theorem laplace_sum (D : ι → FinDist) (hB : 0 < BREV D) (lam kap b : ℝ) (hl : 0 < lam)
    (hT : Tangent kap b) :
    ∑ j, E1 (D j) (fun x => 1 - Real.exp (-(lam * x))) ≤ kap + b * (lam * BREV D) := by
  have h1 := laplace_lower D hB lam kap b hl hT
  have h2 : Ex D (fun ω => Real.exp (-(lam * ∑ i, value D ω i))) =
      ∏ j, E1 (D j) (fun x => Real.exp (-(lam * x))) := by
    rw [← Ex_prod D (fun _ x => Real.exp (-(lam * x)))]
    unfold Ex
    refine sum_congr rfl fun ω _ => ?_
    congr 1
    change Real.exp (-(lam * ∑ i, value D ω i)) = ∏ i, Real.exp (-(lam * value D ω i))
    rw [← Real.exp_sum, mul_sum, sum_neg_distrib]
  have h3 : ∏ j, E1 (D j) (fun x => Real.exp (-(lam * x))) ≤
      Real.exp (-∑ j, E1 (D j) (fun x => 1 - Real.exp (-(lam * x)))) := by
    rw [← sum_neg_distrib, Real.exp_sum]
    refine Finset.prod_le_prod (fun j _ => E1_nonneg _ fun k => (Real.exp_pos _).le) fun j _ => ?_
    have e : E1 (D j) (fun x => Real.exp (-(lam * x))) =
        1 - E1 (D j) (fun x => 1 - Real.exp (-(lam * x))) := by
      rw [E1_sub, E1_const]; ring
    rw [e]
    exact Real.one_sub_le_exp_neg _
  rw [h2] at h1
  have h4 := Real.exp_le_exp.mp (h1.trans h3)
  linarith

end UB
end Sievert26SimpleAuctions

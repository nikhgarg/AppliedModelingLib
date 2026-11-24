import Sievert26SimpleAuctions.Expect

/-! Layer-cake integrals of indicator functions, the function `ψ`, and the pointwise bound. -/
set_option linter.deprecated false
open Finset MeasureTheory

namespace Sievert26SimpleAuctions
namespace UB

/-- closed indicator -/
noncomputable def ind (a t : ℝ) : ℝ := if t ≤ a then 1 else 0

theorem ind_nonneg (a t : ℝ) : 0 ≤ ind a t := by unfold ind; split_ifs <;> norm_num
theorem ind_le_one (a t : ℝ) : ind a t ≤ 1 := by unfold ind; split_ifs <;> norm_num

theorem ind_integrable (a p q : ℝ) (f : ℝ → ℝ) (hf : IntervalIntegrable f volume p q) :
    IntervalIntegrable (fun t => ind a t * f t) volume p q := by
  have h : (fun t => ind a t * f t) = Set.indicator (Set.Iic a) f := by
    funext t
    unfold ind Set.indicator
    by_cases h : t ≤ a
    · rw [if_pos h, if_pos (show t ∈ Set.Iic a from h), one_mul]
    · rw [if_neg h, if_neg (show t ∉ Set.Iic a from h), zero_mul]
  rw [h]
  exact ⟨hf.1.indicator measurableSet_Iic, hf.2.indicator measurableSet_Iic⟩

theorem ind_integrable' (a p q : ℝ) : IntervalIntegrable (ind a) volume p q := by
  have := ind_integrable a p q (fun _ => (1:ℝ)) intervalIntegrable_const
  simpa using this

/-- `∫_0^K 1{t ≤ a} f = ∫_0^{a⁺} f` -/
theorem integral_ind_mul (a K : ℝ) (hK : 0 ≤ K) (ha : a ≤ K) (f : ℝ → ℝ)
    (hf : ∀ p q, 0 ≤ p → 0 ≤ q → IntervalIntegrable f volume p q) :
    ∫ t in (0:ℝ)..K, ind a t * f t = ∫ t in (0:ℝ)..(max a 0), f t := by
  have hA0 : 0 ≤ max a 0 := le_max_right _ _
  have hAK : max a 0 ≤ K := max_le ha hK
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (ind_integrable a 0 (max a 0) f (hf _ _ le_rfl hA0))
    (ind_integrable a (max a 0) K f (hf _ _ hA0 hK))]
  have h2 : ∫ t in (max a 0)..K, ind a t * f t = 0 := by
    have : ∫ t in (max a 0)..K, ind a t * f t = ∫ t in (max a 0)..K, (0:ℝ) := by
      refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun t ht => ?_)
      rw [Set.uIoc_of_le hAK] at ht
      have : ¬ t ≤ a := not_le.mpr (lt_of_le_of_lt (le_max_left a 0) ht.1)
      unfold ind; rw [if_neg this, zero_mul]
    rw [this]; simp
  have h1 : ∫ t in (0:ℝ)..(max a 0), ind a t * f t = ∫ t in (0:ℝ)..(max a 0), f t := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun t ht => ?_)
    rw [Set.uIoc_of_le hA0] at ht
    have : t ≤ a := by
      rcases le_max_iff.mp ht.2 with h | h
      · exact h
      · exact absurd ht.1 (not_lt.mpr h)
    unfold ind; rw [if_pos this, one_mul]
  rw [h1, h2, add_zero]

theorem integral_ind (a K : ℝ) (hK : 0 ≤ K) (ha : a ≤ K) :
    ∫ t in (0:ℝ)..K, ind a t = max a 0 := by
  have h := integral_ind_mul a K hK ha (fun _ => 1) (fun _ _ _ _ => intervalIntegrable_const)
  simpa using h

/-! ### φ and ψ -/

noncomputable def phi (x : ℝ) : ℝ := x - 1 + Real.exp (-x)
noncomputable def psi (z : ℝ) : ℝ := 1 - (1 - Real.exp (-z)) / z

theorem phi_convex : ConvexOn ℝ Set.univ phi := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have h := convexOn_exp.2 (Set.mem_univ (-x)) (Set.mem_univ (-y)) ha hb hab
  simp only [smul_eq_mul] at h ⊢
  unfold phi
  have e1 : -(a * x + b * y) = a * -x + b * -y := by ring
  rw [e1]
  have : a * x + b * y - 1 = a * (x - 1) + b * (y - 1) := by linear_combination hab
  rw [this]
  nlinarith

theorem phi_zero : phi 0 = 0 := by unfold phi; simp

theorem phi_eq (z : ℝ) (hz : 0 < z) : phi z = z * psi z := by
  unfold phi psi; field_simp; ring

/-- chord bound -/
theorem phi_le_chord (y z : ℝ) (hz : 0 < z) (hy0 : 0 ≤ y) (hyz : y ≤ z) : phi y ≤ y * psi z := by
  have h := phi_convex.2 (Set.mem_univ 0) (Set.mem_univ z)
    (show 0 ≤ 1 - y / z by rw [sub_nonneg, div_le_one hz]; exact hyz)
    (show 0 ≤ y / z by positivity) (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, phi_zero] at h
  rw [div_mul_cancel₀ y hz.ne'] at h
  refine h.trans (le_of_eq ?_)
  rw [phi_eq z hz]; field_simp

variable {ι : Type} [Fintype ι]

/-- `Σx - 1 + Π(1-x) ≤ φ(Σx)` -/
theorem inclusion_le_phi (x : ι → ℝ) (hx1 : ∀ i, x i ≤ 1) :
    ∑ i, x i - 1 + ∏ i, (1 - x i) ≤ phi (∑ i, x i) := by
  unfold phi
  have h : ∏ i, (1 - x i) ≤ ∏ i, Real.exp (-x i) :=
    Finset.prod_le_prod (fun i _ => by have := hx1 i; linarith) (fun i _ => Real.one_sub_le_exp_neg _)
  rw [← Real.exp_sum, sum_neg_distrib] at h
  linarith

/-- Jensen with weights, followed by the chord bound -/
theorem phi_jensen (x lam z : ι → ℝ) (hl : ∀ i, 0 ≤ lam i) (hls : ∑ i, lam i = 1)
    (hz : ∀ i, 0 < z i) (hx0 : ∀ i, 0 ≤ x i) (hx : ∀ i, x i ≤ lam i * z i) :
    phi (∑ i, x i) ≤ ∑ i, x i * psi (z i) := by
  have hxl : ∀ i, x i = lam i * (x i / lam i) := by
    intro i
    rcases eq_or_lt_of_le (hl i) with h | h
    · have h1 := hx i; rw [← h, zero_mul] at h1
      rw [← h, zero_mul]; exact le_antisymm h1 (hx0 i)
    · field_simp
  have h := phi_convex.map_sum_le (t := univ) (w := lam) (p := fun i => x i / lam i)
    (fun i _ => hl i) hls (fun i _ => Set.mem_univ _)
  simp only [smul_eq_mul] at h
  have e : ∑ i, lam i * (x i / lam i) = ∑ i, x i := sum_congr rfl fun i _ => (hxl i).symm
  rw [e] at h
  refine h.trans (sum_le_sum fun i _ => ?_)
  rcases eq_or_lt_of_le (hl i) with h0 | h0
  · have h1 := hx i; rw [← h0, zero_mul] at h1
    have : x i = 0 := le_antisymm h1 (hx0 i)
    rw [← h0, this]; simp
  · have hy : x i / lam i ≤ z i := by rw [div_le_iff₀ h0]; linarith [hx i]
    have h1 := phi_le_chord (x i / lam i) (z i) (hz i) (div_nonneg (hx0 i) h0.le) hy
    calc lam i * phi (x i / lam i) ≤ lam i * (x i / lam i * psi (z i)) :=
          mul_le_mul_of_nonneg_left h1 h0.le
      _ = x i * psi (z i) := by rw [← mul_assoc, ← hxl]

theorem ii_sum {α : Type*} [Fintype α] {p q : ℝ} (f : α → ℝ → ℝ)
    (h : ∀ j, IntervalIntegrable (f j) volume p q) :
    IntervalIntegrable (fun x => ∑ j, f j x) volume p q := by
  have := IntervalIntegrable.sum (univ : Finset α) (f := f) (fun j _ => h j)
  rwa [Finset.sum_fn] at this

/-! ### expectation of the excess -/
variable [DecidableEq ι]

theorem E1_ind (F : FinDist) (c t : ℝ) : E1 F (fun x => ind (x - c) t) = F.tail (c + t) := by
  rw [tail_eq]
  unfold E1
  refine sum_congr rfl fun k _ => ?_
  dsimp only
  unfold ind
  by_cases h : t ≤ F.val k - c
  · rw [if_pos h, if_pos (by linarith)]
  · rw [if_neg h, if_neg (by intro h'; apply h; linarith)]

theorem tail_le_one (F : FinDist) (p : ℝ) : F.tail p ≤ 1 := by
  rw [tail_eq]
  calc E1 F (fun x => if p ≤ x then 1 else 0) ≤ E1 F (fun _ => 1) := by
        refine E1_mono F fun k => ?_
        split_ifs <;> norm_num
    _ = 1 := E1_const F 1

/-- the integrand as an expectation of indicators -/
theorem integrand_eq (D : ι → FinDist) (c : ι → ℝ) (star : Profile D → ι)
    (hstar : ∀ ω j, value D ω j - c j ≤ value D ω (star ω) - c (star ω)) (t : ℝ) :
    (∑ j, (D j).tail (c j + t) - 1 + ∏ j, (1 - (D j).tail (c j + t))) =
      ∑ ω, prob D ω *
        (∑ j, ind (value D ω j - c j) t - ind (value D ω (star ω) - c (star ω)) t) := by
  have h1 : ∀ ω, ∑ j, ind (value D ω j - c j) t - ind (value D ω (star ω) - c (star ω)) t =
      (∑ j, ind (value D ω j - c j) t - 1) + ∏ j, (1 - ind (value D ω j - c j) t) := by
    intro ω
    have : ∏ j, (1 - ind (value D ω j - c j) t) =
        1 - ind (value D ω (star ω) - c (star ω)) t := by
      by_cases h : t ≤ value D ω (star ω) - c (star ω)
      · rw [prod_eq_zero (mem_univ (star ω))]
        · unfold ind; rw [if_pos h]; ring
        · unfold ind; rw [if_pos h]; ring
      · rw [prod_eq_one]
        · unfold ind; rw [if_neg h]; ring
        · intro j _
          unfold ind
          rw [if_neg (fun h' => h (h'.trans (hstar ω j)))]; ring
    rw [this]; ring
  simp_rw [h1]
  change _ = Ex D (fun ω => (∑ j, ind (value D ω j - c j) t - 1) +
    ∏ j, (1 - ind (value D ω j - c j) t))
  rw [Ex_add, Ex_sub, Ex_const, Ex_sum, Ex_prod D (fun j x => 1 - ind (x - c j) t)]
  have e1 : ∑ j, (D j).tail (c j + t) = ∑ j, Ex D (fun ω => ind (value D ω j - c j) t) := by
    refine sum_congr rfl fun j _ => ?_
    rw [← E1_ind, ← Ex_marg D (fun x => ind (x - c j) t) j]
  have e2 : ∏ j, (1 - (D j).tail (c j + t)) = ∏ j, E1 (D j) (fun x => 1 - ind (x - c j) t) := by
    refine prod_congr rfl fun j _ => ?_
    rw [E1_sub, E1_const, E1_ind]
  rw [e1, e2]

theorem integrand_ii (D : ι → FinDist) (c : ι → ℝ) (star : Profile D → ι)
    (hstar : ∀ ω j, value D ω j - c j ≤ value D ω (star ω) - c (star ω)) (p q : ℝ) :
    IntervalIntegrable
      (fun t => ∑ j, (D j).tail (c j + t) - 1 + ∏ j, (1 - (D j).tail (c j + t))) volume p q := by
  have e : (fun t => ∑ j, (D j).tail (c j + t) - 1 + ∏ j, (1 - (D j).tail (c j + t))) =
      fun t => ∑ ω, prob D ω *
        (∑ j, ind (value D ω j - c j) t - ind (value D ω (star ω) - c (star ω)) t) :=
    funext fun t => integrand_eq D c star hstar t
  rw [e]
  exact ii_sum _ fun ω => ((ii_sum _ fun j => ind_integrable' _ _ _).sub
    (ind_integrable' _ _ _)).const_mul _

/-- `E[Σ Y_j - Y_*] = ∫_0^K (Σ_j x_j(t) - 1 + Π(1-x_j(t))) dt`, `x_j(t) = Pr[X_j ≥ c_j + t]`. -/
theorem excess_integral (D : ι → FinDist) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (star : Profile D → ι)
    (hstar : ∀ ω j, value D ω j - c j ≤ value D ω (star ω) - c (star ω))
    (K : ℝ) (hK : 0 ≤ K) (hKv : ∀ i k, (D i).val k ≤ K) :
    Ex D (fun ω => ∑ j, max (value D ω j - c j) 0 - max (value D ω (star ω) - c (star ω)) 0) =
    ∫ t in (0:ℝ)..K, (∑ j, (D j).tail (c j + t) - 1 + ∏ j, (1 - (D j).tail (c j + t))) := by
  have hvK : ∀ ω j, value D ω j - c j ≤ K := fun ω j => by
    have := hKv j (ω j); have := hc j; unfold value; linarith
  simp_rw [integrand_eq D c star hstar]
  unfold Ex
  have hii : ∀ ω, IntervalIntegrable (fun t => ∑ j, ind (value D ω j - c j) t
      - ind (value D ω (star ω) - c (star ω)) t) volume 0 K := fun ω =>
    (ii_sum _ fun j => ind_integrable' _ _ _).sub (ind_integrable' _ _ _)
  rw [intervalIntegral.integral_finset_sum (fun ω _ => (hii ω).const_mul _)]
  refine sum_congr rfl fun ω _ => ?_
  dsimp only
  rw [intervalIntegral.integral_const_mul]
  congr 1
  rw [intervalIntegral.integral_sub (ii_sum _ fun j => ind_integrable' _ _ _)
    (ind_integrable' _ _ _), intervalIntegral.integral_finset_sum (fun j _ => ind_integrable' _ _ _),
    integral_ind _ K hK (hvK ω _)]
  congr 1
  exact sum_congr rfl fun j _ => (integral_ind _ K hK (hvK ω j)).symm

end UB
end Sievert26SimpleAuctions

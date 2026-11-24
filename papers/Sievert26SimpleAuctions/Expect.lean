import Sievert26SimpleAuctions.Basic

/-! Expectations over finite product distributions: factorisation, marginals, resampling. -/
open Finset

namespace Sievert26SimpleAuctions
namespace UB

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- expectation over realisations -/
noncomputable def Ex (D : ι → FinDist) (f : Profile D → ℝ) : ℝ := ∑ ω, prob D ω * f ω

/-- expectation of a function of one item's value -/
noncomputable def E1 (F : FinDist) (f : ℝ → ℝ) : ℝ := ∑ k, F.prob k * f (F.val k)

theorem Ex_mono (D : ι → FinDist) {f g : Profile D → ℝ} (h : ∀ ω, f ω ≤ g ω) :
    Ex D f ≤ Ex D g :=
  sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (prob_nonneg D ω)

theorem Ex_add (D : ι → FinDist) (f g : Profile D → ℝ) :
    Ex D (fun ω => f ω + g ω) = Ex D f + Ex D g := by
  unfold Ex; rw [← sum_add_distrib]; exact sum_congr rfl fun ω _ => by ring

theorem Ex_sub (D : ι → FinDist) (f g : Profile D → ℝ) :
    Ex D (fun ω => f ω - g ω) = Ex D f - Ex D g := by
  unfold Ex; rw [← sum_sub_distrib]; exact sum_congr rfl fun ω _ => by ring

theorem Ex_const (D : ι → FinDist) (c : ℝ) : Ex D (fun _ => c) = c := by
  unfold Ex; rw [← sum_mul, prob_sum, one_mul]

theorem Ex_sum {α : Type*} (s : Finset α) (D : ι → FinDist) (f : α → Profile D → ℝ) :
    Ex D (fun ω => ∑ a ∈ s, f a ω) = ∑ a ∈ s, Ex D (f a) := by
  unfold Ex; simp_rw [mul_sum]; rw [sum_comm]

theorem E1_mono (F : FinDist) {f g : ℝ → ℝ} (h : ∀ k, f (F.val k) ≤ g (F.val k)) :
    E1 F f ≤ E1 F g :=
  sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (h k) (F.prob_nonneg k)

theorem E1_const (F : FinDist) (c : ℝ) : E1 F (fun _ => c) = c := by
  unfold E1; rw [← sum_mul, F.prob_sum, one_mul]

theorem E1_sub (F : FinDist) (f g : ℝ → ℝ) :
    E1 F (fun x => f x - g x) = E1 F f - E1 F g := by
  unfold E1; rw [← sum_sub_distrib]; exact sum_congr rfl fun k _ => by ring

theorem E1_mul (F : FinDist) (c : ℝ) (f : ℝ → ℝ) :
    E1 F (fun x => c * f x) = c * E1 F f := by
  unfold E1; rw [mul_sum]; exact sum_congr rfl fun k _ => by ring

theorem E1_nonneg (F : FinDist) {f : ℝ → ℝ} (h : ∀ k, 0 ≤ f (F.val k)) : 0 ≤ E1 F f :=
  sum_nonneg fun k _ => mul_nonneg (F.prob_nonneg k) (h k)

/-- independence: expectation of a product -/
theorem Ex_prod (D : ι → FinDist) (f : ι → ℝ → ℝ) :
    Ex D (fun ω => ∏ i, f i (value D ω i)) = ∏ i, E1 (D i) (f i) := by
  unfold Ex E1 prob value
  simp_rw [← prod_mul_distrib]
  exact sum_prod_pi (fun i k => (D i).prob k * f i ((D i).val k))

/-- marginal -/
theorem Ex_marg (D : ι → FinDist) (f : ℝ → ℝ) (j : ι) :
    Ex D (fun ω => f (value D ω j)) = E1 (D j) f := by
  have h := Ex_prod D (fun i x => if i = j then f x else 1)
  have h1 : ∀ ω : Profile D, (∏ i, if i = j then f (value D ω i) else 1) = f (value D ω j) := by
    intro ω; rw [prod_ite_eq' univ j]; simp
  simp_rw [h1] at h
  rw [h, ← mul_prod_erase univ _ (mem_univ j)]
  rw [prod_eq_one]
  · simp
  · intro i hi
    simp only [if_neg (ne_of_mem_erase hi)]
    exact E1_const _ 1

/-- replacing coordinate `j` by a fresh independent copy does not change expectations -/
theorem resample (D : ι → FinDist) (j : ι) (f : Profile D → ℝ) :
    Ex D f = Ex D (fun ω => ∑ k, (D j).prob k * f (Function.update ω j k)) := by
  classical
  -- probability without coordinate j
  have hq : ∀ (ω : Profile D) (k : Fin (D j).size),
      prob D (Function.update ω j k) * (D j).prob (ω j) = prob D ω * (D j).prob k := by
    intro ω k
    unfold prob
    rw [← mul_prod_erase univ _ (mem_univ j), ← mul_prod_erase univ _ (mem_univ j)]
    have : ∏ i ∈ univ.erase j, (D i).prob (Function.update ω j k i) =
        ∏ i ∈ univ.erase j, (D i).prob (ω i) :=
      prod_congr rfl fun i hi => by rw [Function.update_of_ne (ne_of_mem_erase hi)]
    rw [this, Function.update_self]; ring
  have hR : Ex D (fun ω => ∑ k, (D j).prob k * f (Function.update ω j k)) =
      ∑ q : Profile D × Fin (D j).size,
        prob D (Function.update q.1 j q.2) * (D j).prob (q.1 j) * f (Function.update q.1 j q.2) := by
    unfold Ex
    rw [Fintype.sum_prod_type]
    refine sum_congr rfl fun ω _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [hq]; ring
  have hL : Ex D f = ∑ q : Profile D × Fin (D j).size,
      prob D q.1 * (D j).prob q.2 * f q.1 := by
    unfold Ex
    rw [Fintype.sum_prod_type]
    refine sum_congr rfl fun ω _ => ?_
    dsimp only
    rw [← sum_mul, ← mul_sum, (D j).prob_sum, mul_one]
  rw [hL, hR]
  let e : Profile D × Fin (D j).size ≃ Profile D × Fin (D j).size :=
    { toFun := fun q => (Function.update q.1 j q.2, q.1 j)
      invFun := fun q => (Function.update q.1 j q.2, q.1 j)
      left_inv := fun q => by
        ext1
        · simp
        · simp
      right_inv := fun q => by
        ext1
        · simp
        · simp }
  refine (Equiv.sum_comp e _).symm.trans ?_
  refine sum_congr rfl fun q _ => ?_
  simp only [e, Equiv.coe_fn_mk]

theorem value_update_self (D : ι → FinDist) (ω : Profile D) (j : ι) (k : Fin (D j).size) :
    value D (Function.update ω j k) j = (D j).val k := by
  unfold value; rw [Function.update_self]

theorem value_update (D : ι → FinDist) (ω : Profile D) (j : ι) (k : Fin (D j).size) :
    value D (Function.update ω j k) = Function.update (value D ω) j ((D j).val k) := by
  funext i
  by_cases h : i = j
  · subst h; rw [value_update_self, Function.update_self]
  · unfold value; rw [Function.update_of_ne h, Function.update_of_ne h]

/-- `p · Pr[X ≥ p] ≤ rev` -/
theorem mul_tail_le (F : FinDist) (p : ℝ) (hp : 0 ≤ p) : p * F.tail p ≤ F.rev :=
  le_ciSup (f := fun p : {p : ℝ // 0 ≤ p} => (p : ℝ) * F.tail p) F.rev_bdd ⟨p, hp⟩

theorem rev_nonneg (F : FinDist) : 0 ≤ F.rev := by
  have := mul_tail_le F 0 le_rfl; simpa using this

theorem mul_bundle_le (D : ι → FinDist) (p : ℝ) (hp : 0 ≤ p) : p * bundleTail D p ≤ BREV D :=
  le_ciSup (f := fun p : {p : ℝ // 0 ≤ p} => (p : ℝ) * bundleTail D p) (BREV_bdd D) ⟨p, hp⟩

theorem BREV_nonneg (D : ι → FinDist) : 0 ≤ BREV D := by
  have := mul_bundle_le D 0 le_rfl; simpa using this

theorem tail_eq (F : FinDist) (p : ℝ) : F.tail p = E1 F (fun x => if p ≤ x then 1 else 0) := by
  unfold FinDist.tail E1
  refine sum_congr rfl fun k _ => ?_
  dsimp only
  split_ifs
  · rw [mul_one]
  · rw [mul_zero]

theorem bundleTail_eq (D : ι → FinDist) (p : ℝ) :
    bundleTail D p = Ex D (fun ω => if p ≤ ∑ i, value D ω i then 1 else 0) := by
  unfold bundleTail Ex
  refine sum_congr rfl fun k _ => ?_
  dsimp only
  split_ifs
  · rw [mul_one]
  · rw [mul_zero]

end UB
end Sievert26SimpleAuctions

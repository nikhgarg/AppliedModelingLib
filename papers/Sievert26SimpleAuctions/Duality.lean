import Sievert26SimpleAuctions.Expect

/-!
# Master inequality (Giannakopoulos–Hahn), for every finite product distribution and every mechanism

`Rev(M) ≤ Σ_j r_j + E[Σ_j Y_j − Y_{j*}]`, `Y_j = (X_j − c_j)^+`, whenever `E[min(X_j,c_j)] ≤ r_j`.
Elementary proof: route the utility term to coordinate `j*`, then bound every coordinate line by
the revenue of a threshold allocation.
-/
open Finset

namespace Sievert26SimpleAuctions
namespace UB

/-- **One coordinate line.**  `x` monotone with values in `[0,1]`, `u ≥ 0` with `u(b)-u(a) ≥ x(a)(b-a)`.
If every threshold price earns at most `R` (with routing weights `a`), so does `x`. -/
theorem line_bound (F : FinDist) (x u : ℝ → ℝ) (a : Fin F.size → ℝ) (R : ℝ)
    (ha0 : ∀ k, 0 ≤ a k) (ha1 : ∀ k, a k ≤ 1)
    (hx1 : ∀ v, 0 ≤ v → x v ≤ 1) (hx0 : ∀ v, 0 ≤ v → 0 ≤ x v)
    (hmono : ∀ v w, 0 ≤ v → v ≤ w → x v ≤ x w)
    (hu0 : ∀ v, 0 ≤ v → 0 ≤ u v)
    (hu : ∀ v w, 0 ≤ v → v ≤ w → x v * (w - v) ≤ u w - u v)
    (hR : ∀ p, 0 ≤ p → ∑ k, (if p ≤ F.val k then F.prob k * (p * a k + F.val k * (1 - a k)) else 0)
      ≤ R) :
    ∑ k, F.prob k * (F.val k * x (F.val k) - a k * u (F.val k)) ≤ R := by
  have hR0 : 0 ≤ R := by
    refine le_trans (sum_nonneg fun k _ => ?_) (hR 0 le_rfl)
    split_ifs
    · have := F.prob_nonneg k; have := F.val_nonneg k; have := ha1 k
      refine mul_nonneg (F.prob_nonneg k) ?_
      rw [zero_mul, zero_add]
      exact mul_nonneg (F.val_nonneg k) (by linarith)
    · exact le_rfl
  -- claim for upper sets, by adding the smallest element
  have key : ∀ s : Finset (Fin F.size), ∀ p, 0 ≤ p → (∀ k ∈ s, p ≤ F.val k) →
      ∑ k ∈ s, F.prob k * (F.val k * x (F.val k) - a k * u (F.val k)) ≤
      (∑ k ∈ s, F.prob k * (p * a k + F.val k * (1 - a k))) * x p
        - (∑ k ∈ s, F.prob k * a k) * u p + R * (1 - x p) := by
    intro s
    induction s using Finset.induction_on_min_value (fun k => F.val k) with
    | empty =>
      intro p hp _
      simp only [sum_empty, zero_mul, sub_zero, zero_add]
      exact mul_nonneg hR0 (by have := hx1 p hp; linarith)
    | insert i s hi hmin ih =>
      intro p hp hps
      have hpi : p ≤ F.val i := hps i (mem_insert_self _ _)
      have hvi := F.val_nonneg i
      have h1 := ih (F.val i) hvi (fun k hk => hmin k hk)
      rw [sum_insert hi, sum_insert hi, sum_insert hi]
      set A := ∑ k ∈ s, F.prob k * a k with hA
      set Q := ∑ k ∈ s, F.prob k * (F.val i * a k + F.val k * (1 - a k)) with hQ
      have hQp : ∑ k ∈ s, F.prob k * (p * a k + F.val k * (1 - a k)) = Q - A * (F.val i - p) := by
        rw [hQ, hA, sum_mul, ← sum_sub_distrib]
        exact sum_congr rfl fun k _ => by ring
      rw [hQp]
      have hA0 : 0 ≤ A := sum_nonneg fun k _ => mul_nonneg (F.prob_nonneg k) (ha0 k)
      -- total at price `val i` is at most R
      have hQR : F.prob i * (F.val i * a i + F.val i * (1 - a i)) + Q ≤ R := by
        refine le_trans ?_ (hR (F.val i) hvi)
        rw [hQ, ← sum_insert (f := fun k => F.prob k * (F.val i * a k + F.val k * (1 - a k))) hi]
        rw [← sum_filter]
        refine sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro k hk
          rw [mem_filter]
          refine ⟨mem_univ _, ?_⟩
          rcases mem_insert.mp hk with h | h
          · rw [h]
          · exact hmin k h
        · intro k hk _
          have := F.val_nonneg k; have := ha1 k; have := ha0 k
          refine mul_nonneg (F.prob_nonneg k) (add_nonneg (mul_nonneg hvi (ha0 k))
            (mul_nonneg (F.val_nonneg k) (by linarith)))
      have hxm := hmono p (F.val i) hp hpi
      have huu := hu p (F.val i) hp hpi
      have hup := hu0 p hp
      have hPa : 0 ≤ F.prob i * a i := mul_nonneg (F.prob_nonneg i) (ha0 i)
      -- combine
      have e1 : F.prob i * (F.val i * a i + F.val i * (1 - a i)) = F.prob i * F.val i := by ring
      rw [e1] at hQR
      have h2 : (F.prob i * F.val i + Q - R) * x (F.val i) ≤ (F.prob i * F.val i + Q - R) * x p :=
        mul_le_mul_of_nonpos_left hxm (by linarith)
      have h3 : (F.prob i * a i + A) * (u p + x p * (F.val i - p)) ≤
          (F.prob i * a i + A) * u (F.val i) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      nlinarith [h1, h2, h3]
  have h := key univ 0 le_rfl (fun k _ => F.val_nonneg k)
  refine le_trans h ?_
  have hA0 : 0 ≤ (∑ k, F.prob k * a k) * u 0 :=
    mul_nonneg (sum_nonneg fun k _ => mul_nonneg (F.prob_nonneg k) (ha0 k)) (hu0 0 le_rfl)
  have hR0' := hR 0 le_rfl
  simp only [F.val_nonneg, ite_true] at hR0'
  have := mul_le_mul_of_nonneg_right hR0' (hx0 0 le_rfl)
  nlinarith

/-- Threshold prices on a line: revenue plus the non-routed excess over the cap. -/
theorem threshold_bound (F : FinDist) (a : Fin F.size → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (ha0 : ∀ k, 0 ≤ a k) (ha1 : ∀ k, a k ≤ 1)
    (hcap : E1 F (fun x => min x c) ≤ F.rev) (p : ℝ) (hp : 0 ≤ p) :
    ∑ k, (if p ≤ F.val k then F.prob k * (p * a k + F.val k * (1 - a k)) else 0) ≤
      F.rev + ∑ k, F.prob k * ((1 - a k) * max (F.val k - c) 0) := by
  rcases le_total c p with h | h
  · have h1 : ∑ k, (if p ≤ F.val k then F.prob k * (p * a k + F.val k * (1 - a k)) else 0) ≤
        ∑ k, (p * (if p ≤ F.val k then F.prob k else 0)
          + F.prob k * ((1 - a k) * max (F.val k - c) 0)) := by
      refine sum_le_sum fun k _ => ?_
      have hP := F.prob_nonneg k
      have h1a : 0 ≤ 1 - a k := by have := ha1 k; linarith
      have hm := le_max_left (F.val k - c) 0
      have hm0 := le_max_right (F.val k - c) 0
      split_ifs with hk
      · have : p * a k + F.val k * (1 - a k) ≤ p + (1 - a k) * max (F.val k - c) 0 := by
          nlinarith
        nlinarith [mul_le_mul_of_nonneg_left this hP]
      · rw [mul_zero, zero_add]; positivity
    refine h1.trans ?_
    rw [sum_add_distrib, ← mul_sum]
    have := mul_tail_le F p hp
    unfold FinDist.tail at this
    linarith
  · have h1 : ∑ k, (if p ≤ F.val k then F.prob k * (p * a k + F.val k * (1 - a k)) else 0) ≤
        ∑ k, (F.prob k * min (F.val k) c + F.prob k * ((1 - a k) * max (F.val k - c) 0)) := by
      refine sum_le_sum fun k _ => ?_
      have hP := F.prob_nonneg k
      have hv := F.val_nonneg k
      have h1a : 0 ≤ 1 - a k := by have := ha1 k; linarith
      have hm0 := le_max_right (F.val k - c) 0
      have hmin0 : 0 ≤ min (F.val k) c := le_min hv hc
      split_ifs with hk
      · have hpm : p ≤ min (F.val k) c := le_min hk h
        have hsplit : F.val k = min (F.val k) c + max (F.val k - c) 0 := by
          rcases le_total (F.val k) c with h' | h'
          · rw [min_eq_left h', max_eq_right (by linarith)]; ring
          · rw [min_eq_right h', max_eq_left (by linarith)]; ring
        have : p * a k + F.val k * (1 - a k) ≤
            min (F.val k) c + (1 - a k) * max (F.val k - c) 0 := by
          have h3 := mul_le_mul_of_nonneg_right hpm (ha0 k)
          have h4 : F.val k * (1 - a k) =
            min (F.val k) c * (1 - a k) + max (F.val k - c) 0 * (1 - a k) := by
            rw [← add_mul, ← hsplit]
          linarith
        nlinarith [mul_le_mul_of_nonneg_left this hP]
      · positivity
    refine h1.trans ?_
    rw [sum_add_distrib]
    unfold E1 at hcap
    linarith

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- utility of a mechanism -/
def util (M : Mechanism ι) (v : ι → ℝ) : ℝ := ∑ i, v i * M.alloc v i - M.pay v

theorem sum_update_mul (v : ι → ℝ) (j : ι) (y : ℝ) (q : ι → ℝ) :
    ∑ i, Function.update v j y i * q i = ∑ i, v i * q i + (y - v j) * q j := by
  rw [← add_sum_erase univ _ (mem_univ j), ← add_sum_erase univ (fun i => v i * q i) (mem_univ j)]
  have : ∑ i ∈ univ.erase j, Function.update v j y i * q i = ∑ i ∈ univ.erase j, v i * q i :=
    sum_congr rfl fun i hi => by rw [Function.update_of_ne (ne_of_mem_erase hi)]
  rw [this, Function.update_self]; ring

theorem line_ic (M : Mechanism ι) (v : ι → ℝ) (hv : ∀ i, 0 ≤ v i) (j : ι) (y z : ℝ)
    (hy : 0 ≤ y) (hz : 0 ≤ z) :
    M.alloc (Function.update v j y) j * (z - y) ≤
      util M (Function.update v j z) - util M (Function.update v j y) := by
  have hvy : ∀ i, 0 ≤ Function.update v j y i := fun i => by
    by_cases h : i = j
    · subst h; rw [Function.update_self]; exact hy
    · rw [Function.update_of_ne h]; exact hv i
  have hvz : ∀ i, 0 ≤ Function.update v j z i := fun i => by
    by_cases h : i = j
    · subst h; rw [Function.update_self]; exact hz
    · rw [Function.update_of_ne h]; exact hv i
  have h := M.ic (Function.update v j z) (Function.update v j y) hvz hvy
  have e1 := sum_update_mul v j z (M.alloc (Function.update v j y))
  have e2 := sum_update_mul v j y (M.alloc (Function.update v j y))
  unfold util
  rw [e1] at h
  rw [e2]
  linarith

/-- **Master inequality.** -/
theorem master (D : ι → FinDist) (M : Mechanism ι) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hcap : ∀ i, E1 (D i) (fun x => min x (c i)) ≤ (D i).rev) (star : Profile D → ι) :
    M.rev D ≤ SREV D + Ex D (fun ω => ∑ j, max (value D ω j - c j) 0
      - max (value D ω (star ω) - c (star ω)) 0) := by
  -- routing indicator
  set f : ι → Profile D → ℝ := fun j ω => if star ω = j then 1 else 0 with hf
  have hf0 : ∀ j ω, 0 ≤ f j ω := fun j ω => by rw [hf]; dsimp; split_ifs <;> norm_num
  have hf1 : ∀ j ω, f j ω ≤ 1 := fun j ω => by rw [hf]; dsimp; split_ifs <;> norm_num
  have hfs : ∀ ω, ∑ j, f j ω = 1 := fun ω => by rw [hf]; simp
  -- decomposition of the revenue
  have h1 : M.rev D = ∑ j, Ex D (fun ω => value D ω j * M.alloc (value D ω) j
      - f j ω * util M (value D ω)) := by
    rw [← Ex_sum]
    unfold Mechanism.rev Ex
    refine sum_congr rfl fun ω _ => ?_
    congr 1
    dsimp only
    rw [sum_sub_distrib, ← sum_mul, hfs, one_mul, util]; ring
  -- every line
  have h2 : ∀ j, Ex D (fun ω => value D ω j * M.alloc (value D ω) j
      - f j ω * util M (value D ω)) ≤
      (D j).rev + Ex D (fun ω => (1 - f j ω) * max (value D ω j - c j) 0) := by
    intro j
    rw [resample D j (fun ω => value D ω j * M.alloc (value D ω) j - f j ω * util M (value D ω)),
      resample D j (fun ω => (1 - f j ω) * max (value D ω j - c j) 0),
      ← Ex_const D (D j).rev, ← Ex_add]
    refine Ex_mono D fun ω => ?_
    simp only [value_update_self]
    simp only [value_update]
    have hv := value_nonneg D ω
    refine line_bound (D j) (fun y => M.alloc (Function.update (value D ω) j y) j)
      (fun y => util M (Function.update (value D ω) j y)) (fun k => f j (Function.update ω j k))
      _ (fun k => hf0 _ _) (fun k => hf1 _ _) (fun y _ => M.alloc_le_one _ _)
      (fun y _ => M.alloc_nonneg _ _) ?_ ?_ ?_ ?_
    · intro y z hy hyz
      rcases eq_or_lt_of_le hyz with h | h
      · rw [h]
      · have a1 := line_ic M (value D ω) hv j y z hy (hy.trans hyz)
        have a2 := line_ic M (value D ω) hv j z y (hy.trans hyz) hy
        nlinarith
    · intro y hy
      refine M.ir _ fun i => ?_
      by_cases h : i = j
      · subst h; rw [Function.update_self]; exact hy
      · rw [Function.update_of_ne h]; exact hv i
    · intro y z hy hyz
      exact line_ic M (value D ω) hv j y z hy (hy.trans hyz)
    · intro p hp
      exact threshold_bound (D j) _ (c j) (hc j) (fun k => hf0 _ _) (fun k => hf1 _ _) (hcap j) p hp
  rw [h1]
  refine (sum_le_sum fun j _ => h2 j).trans ?_
  rw [sum_add_distrib, ← Ex_sum]
  refine add_le_add (le_of_eq rfl) (Ex_mono D fun ω => le_of_eq ?_)
  have : ∀ j, (1 - f j ω) * max (value D ω j - c j) 0 =
      max (value D ω j - c j) 0 - (if star ω = j then max (value D ω j - c j) 0 else 0) := by
    intro j; rw [hf]; dsimp; split_ifs <;> ring
  simp_rw [this]
  rw [sum_sub_distrib, sum_ite_eq univ (star ω)]
  simp

end UB
end Sievert26SimpleAuctions

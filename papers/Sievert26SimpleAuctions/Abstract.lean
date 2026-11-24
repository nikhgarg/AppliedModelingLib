import Sievert26SimpleAuctions.Duality
import Sievert26SimpleAuctions.Laplace

/-!
# From a one-dimensional certificate to a universal upper bound

`UCert` collects the numerical facts (kernel `w(v) = Σ a_i e^{-v/s_i}`, step-function Jensen
weights `1/α(t)`, the one-variable inequality).  From such a certificate we derive
`REV ≤ (1+g)·SREV + b·BREV` for every finite product distribution.
-/
set_option linter.deprecated false
open Finset MeasureTheory

namespace Sievert26SimpleAuctions
namespace UB

section kernel
variable {n : ℕ} (a s : Fin n → ℝ)

/-- the kernel -/
noncomputable def wf (v : ℝ) : ℝ := ∑ i, a i * Real.exp (-(v / s i))
/-- its antiderivative -/
noncomputable def What (v : ℝ) : ℝ := ∑ i, a i * s i * (1 - Real.exp (-(v / s i)))
/-- per-item remainder -/
noncomputable def Rf (al v : ℝ) : ℝ := max (psi (al / v) - wf a s v) 0 / v

theorem wf_continuous : Continuous (wf a s) := by unfold wf; fun_prop

theorem What_hasDeriv (hs : ∀ i, 0 < s i) (v : ℝ) : HasDerivAt (What a s) (wf a s v) v := by
  unfold What wf
  have h : ∀ i ∈ (univ : Finset (Fin n)), HasDerivAt
      (fun v => a i * s i * (1 - Real.exp (-(v / s i)))) (a i * Real.exp (-(v / s i))) v := by
    intro i _
    have h1 : HasDerivAt (fun v => -(v / s i)) (-(1 / s i)) v :=
      ((hasDerivAt_id' v).div_const (s i)).fun_neg
    have h2 := ((h1.exp).const_sub 1).const_mul (a i * s i)
    convert h2 using 1
    have := (hs i).ne'
    field_simp
  have := HasDerivAt.fun_sum h
  exact this

theorem What_zero : What a s 0 = 0 := by unfold What; simp

/-- secant bound: `What` is concave with `What 0 = 0` -/
theorem What_secant (ha : ∀ i, 0 ≤ a i) (hs : ∀ i, 0 < s i) (z c : ℝ) (hc : 0 < c)
    (hz0 : 0 ≤ z) (hzc : z ≤ c) : z / c * What a s c ≤ What a s z := by
  unfold What
  rw [mul_sum]
  refine sum_le_sum fun i _ => ?_
  have hc1 : 0 ≤ 1 - z / c := by rw [sub_nonneg, div_le_one hc]; exact hzc
  have h := convexOn_exp.2 (Set.mem_univ (-(c / s i))) (Set.mem_univ 0)
    (show 0 ≤ z / c by positivity) hc1 (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at h
  have e : z / c * -(c / s i) = -(z / s i) := by field_simp
  rw [e] at h
  have h2 : z / c * (1 - Real.exp (-(c / s i))) ≤ 1 - Real.exp (-(z / s i)) := by linarith
  have := mul_le_mul_of_nonneg_left h2 (mul_nonneg (ha i) (hs i).le)
  linarith

theorem What_nonneg (ha : ∀ i, 0 ≤ a i) (hs : ∀ i, 0 < s i) (v : ℝ) (hv : 0 ≤ v) :
    0 ≤ What a s v := by
  unfold What
  refine sum_nonneg fun i _ => mul_nonneg (mul_nonneg (ha i) (hs i).le) ?_
  rw [sub_nonneg, Real.exp_le_one_iff, neg_nonpos]
  exact div_nonneg hv (hs i).le

theorem Rf_nonneg (al v : ℝ) (hv : 0 ≤ v) : 0 ≤ Rf a s al v :=
  div_nonneg (le_max_right _ _) hv

theorem Rf_contOn (al : ℝ) (hal : 0 < al) : ContinuousOn (Rf a s al) (Set.Ioi 0) := by
  unfold Rf psi
  refine ContinuousOn.div ?_ continuousOn_id fun x hx => (ne_of_gt hx)
  refine (continuous_id.max continuous_const).comp_continuousOn (g := fun z : ℝ => max z 0) ?_
  refine ContinuousOn.sub ?_ (wf_continuous a s).continuousOn
  have h1 : ContinuousOn (fun v => al / v) (Set.Ioi 0) :=
    continuousOn_const.div continuousOn_id fun x hx => (ne_of_gt hx)
  refine continuousOn_const.sub (ContinuousOn.div ?_ h1 fun x hx =>
    (div_pos hal hx).ne')
  exact continuousOn_const.sub (Real.continuous_exp.comp_continuousOn h1.neg)

end kernel

/-- A one-dimensional certificate. -/
structure UCert where
  n : ℕ
  (a s kp bb : Fin n → ℝ)
  (alpha : ℝ → ℝ)
  (A kappa b g : ℝ)
  a_nonneg : ∀ i, 0 ≤ a i
  s_pos : ∀ i, 0 < s i
  alpha_pos : ∀ t, 0 < alpha t
  alpha_mono : Monotone alpha
  alpha_le : ∀ t, alpha t ≤ A
  kappa_nonneg : 0 ≤ kappa
  tan : ∀ i, Tangent (kp i) (bb i)
  kappa_ge : ∑ i, a i * s i * kp i ≤ kappa
  b_ge : ∑ i, a i * bb i ≤ b
  cert : ∀ t T : ℝ, 0 < t → t ≤ T →
    kappa / alpha t + (∫ v in t..T, Rf a s (alpha t) v) - What a s t / t ≤ g

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ### caps -/

theorem rev_le_mean (F : FinDist) : F.rev ≤ E1 F (fun x => x) := by
  refine FinDist.rev_le F _ fun p _ => ?_
  have := mean_bound F.val F.prob F.val_nonneg F.prob_nonneg p
  unfold FinDist.tail E1
  refine this.trans (le_of_eq (sum_congr rfl fun k _ => by ring))

theorem exists_cap (F : FinDist) : ∃ c : ℝ, 0 ≤ c ∧ E1 F (fun x => min x c) = F.rev := by
  set K := ∑ k, F.val k with hK
  have hKv : ∀ k, F.val k ≤ K := fun k =>
    single_le_sum (f := F.val) (fun k _ => F.val_nonneg k) (mem_univ k)
  have hK0 : 0 ≤ K := sum_nonneg fun k _ => F.val_nonneg k
  have hcont : Continuous (fun c => E1 F (fun x => min x c)) := by
    unfold E1; fun_prop
  have h0 : E1 F (fun x => min x 0) = 0 := by
    unfold E1
    refine sum_eq_zero fun k _ => ?_
    change F.prob k * min (F.val k) 0 = 0
    rw [min_eq_right (F.val_nonneg k), mul_zero]
  have h1 : F.rev ≤ E1 F (fun x => min x K) := by
    refine (rev_le_mean F).trans (E1_mono F fun k => ?_)
    rw [min_eq_left (hKv k)]
  obtain ⟨c, hc, hcr⟩ := intermediate_value_Icc hK0 hcont.continuousOn
    (show F.rev ∈ Set.Icc (E1 F (fun x => min x 0)) (E1 F (fun x => min x K)) from
      ⟨by rw [h0]; exact rev_nonneg F, h1⟩)
  exact ⟨c, hc.1, hcr⟩

/-! ### the scale `l` (fixed point of a monotone map) -/

theorem exists_scale (C : UCert) (r c : ι → ℝ) (hr : ∀ j, 0 ≤ r j) (hc : ∀ j, 0 ≤ c j)
    (hS : 0 < ∑ j, r j) : ∃ l : ℝ, 0 < l ∧ ∑ j, r j / C.alpha (c j / l) = l := by
  set f : ℝ → ℝ := fun l => ∑ j, r j / C.alpha (c j / l) with hf
  have hmono : ∀ l l', 0 < l → l ≤ l' → f l ≤ f l' := by
    intro l l' hl hll
    refine sum_le_sum fun j _ => ?_
    refine div_le_div_of_nonneg_left (hr j) (C.alpha_pos _) (C.alpha_mono ?_)
    exact div_le_div_of_nonneg_left (hc j) hl hll
  have hA : 0 < C.A := lt_of_lt_of_le (C.alpha_pos 0) (C.alpha_le 0)
  have hlow : ∀ l, (∑ j, r j) / C.A ≤ f l := by
    intro l
    rw [hf, sum_div]
    exact sum_le_sum fun j _ => div_le_div_of_nonneg_left (hr j) (C.alpha_pos _) (C.alpha_le _)
  have hup : ∀ l, 0 < l → f l ≤ (∑ j, r j) / C.alpha 0 := by
    intro l hl
    rw [hf, sum_div]
    exact sum_le_sum fun j _ => div_le_div_of_nonneg_left (hr j) (C.alpha_pos _)
      (C.alpha_mono (div_nonneg (hc j) hl.le))
  set l0 := (∑ j, r j) / C.A with hl0
  have hl0p : 0 < l0 := div_pos hS hA
  set E : Set ℝ := {l | 0 < l ∧ l ≤ f l} with hE
  have hne : E.Nonempty := ⟨l0, hl0p, hlow l0⟩
  have hbdd : BddAbove E := ⟨(∑ j, r j) / C.alpha 0, fun l hl => hl.2.trans (hup l hl.1)⟩
  have hsup : l0 ≤ sSup E := le_csSup hbdd ⟨hl0p, hlow l0⟩
  have hpos : 0 < sSup E := lt_of_lt_of_le hl0p hsup
  have h1 : sSup E ≤ f (sSup E) :=
    csSup_le hne fun l hl => hl.2.trans (hmono l _ hl.1 (le_csSup hbdd hl))
  have hfp : 0 < f (sSup E) := lt_of_lt_of_le hpos h1
  have h2 : f (sSup E) ≤ sSup E := le_csSup hbdd ⟨hfp, hmono _ _ hpos h1⟩
  exact ⟨sSup E, hpos, le_antisymm h2 h1⟩

/-! ### the main estimate -/

theorem tail_antitone (F : FinDist) : Antitone F.tail := by
  intro p q hpq
  unfold FinDist.tail
  refine sum_le_sum fun k _ => ?_
  by_cases h : q ≤ F.val k
  · rw [if_pos h, if_pos (hpq.trans h)]
  · rw [if_neg h]; split_ifs
    · exact F.prob_nonneg k
    · exact le_rfl

theorem tail_ii (F : FinDist) (c p q : ℝ) (f : ℝ → ℝ) (hf : Continuous f) :
    IntervalIntegrable (fun t => f t * F.tail (c + t)) volume p q := by
  have h : Antitone (fun t => F.tail (c + t)) := fun x y hxy => tail_antitone F (by linarith)
  exact (h.intervalIntegrable).continuousOn_mul hf.continuousOn

/-- the linear part, integrated -/
theorem linear_part (C : UCert) (F : FinDist) (c l K : ℝ) (hc : 0 ≤ c) (hl : 0 < l)
    (hK : 0 ≤ K) (hKv : ∀ k, F.val k ≤ K) :
    ∫ t in (0:ℝ)..K, wf C.a C.s ((c + t) / l) * F.tail (c + t) =
      l * E1 F (fun x => What C.a C.s (x / l)) - l * E1 F (fun x => What C.a C.s (min x c / l)) := by
  have hcont : Continuous (fun t => wf C.a C.s ((c + t) / l)) :=
    (wf_continuous C.a C.s).comp (by fun_prop)
  have e1 : ∀ t, wf C.a C.s ((c + t) / l) * F.tail (c + t) =
      ∑ k, F.prob k * (ind (F.val k - c) t * wf C.a C.s ((c + t) / l)) := by
    intro t
    rw [← E1_ind, E1, mul_sum]
    exact sum_congr rfl fun k _ => by ring
  simp_rw [e1]
  rw [intervalIntegral.integral_finset_sum
    (fun k _ => (ind_integrable _ _ _ _ (hcont.intervalIntegrable _ _)).const_mul _)]
  rw [← mul_sub, ← E1_sub, E1, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_const_mul,
    integral_ind_mul _ K hK (by have := hKv k; linarith) _
      (fun p q _ _ => hcont.intervalIntegrable p q)]
  have hd : ∀ x ∈ Set.uIcc 0 (max (F.val k - c) 0),
      HasDerivAt (fun t => l * What C.a C.s ((c + t) / l)) (wf C.a C.s ((c + x) / l)) x := by
    intro x _
    have h1 : HasDerivAt (fun t => (c + t) / l) (1 / l) x :=
      ((hasDerivAt_id' x).const_add c).div_const l
    have h2 : HasDerivAt (fun t => l * What C.a C.s ((c + t) / l))
        (l * (wf C.a C.s ((c + x) / l) * (1 / l))) x := by
      have h3 : HasDerivAt (What C.a C.s ∘ fun t => (c + t) / l)
          (wf C.a C.s ((c + x) / l) * (1 / l)) x :=
        HasDerivAt.comp x (What_hasDeriv C.a C.s C.s_pos ((c + x) / l)) h1
      exact h3.const_mul l
    have e : l * (wf C.a C.s ((c + x) / l) * (1 / l)) = wf C.a C.s ((c + x) / l) := by
      field_simp
    rwa [e] at h2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable _ _)]
  rcases le_total (F.val k) c with h | h
  · rw [max_eq_right (by linarith), min_eq_left h]; simp
  · rw [max_eq_left (by linarith), min_eq_right h]
    simp only [add_zero, add_sub_cancel]
    ring

theorem main_estimate (C : UCert) (D : ι → FinDist) (hS : 0 < SREV D) (hB : 0 < BREV D)
    (M : Mechanism ι) : M.rev D ≤ (1 + C.g) * SREV D + C.b * BREV D := by
  classical
  -- caps
  choose c hc0 hcap using fun j => exists_cap (D j)
  set r : ι → ℝ := fun j => (D j).rev with hr
  have hr0 : ∀ j, 0 ≤ r j := fun j => rev_nonneg _
  have hcpos : ∀ j, 0 < r j → 0 < c j := by
    intro j hj
    rcases eq_or_lt_of_le (hc0 j) with h | h
    · exfalso
      have h1 := hcap j
      rw [← h] at h1
      have : E1 (D j) (fun x => min x 0) = 0 := by
        unfold E1
        refine sum_eq_zero fun k _ => ?_
        change (D j).prob k * min ((D j).val k) 0 = 0
        rw [min_eq_right ((D j).val_nonneg k), mul_zero]
      rw [this] at h1
      have : r j = 0 := h1.symm
      linarith
    · exact h
  -- scale
  obtain ⟨l, hl, hlsum⟩ := exists_scale C r c hr0 hc0 hS
  -- favourite
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    have : SREV D = 0 := by unfold SREV; simp
    linarith
  have hstar : ∀ ω : Profile D, ∃ i, ∀ j, value D ω j - c j ≤ value D ω i - c i := by
    intro ω
    obtain ⟨i, _, hi⟩ := exists_max_image univ (fun j => value D ω j - c j) univ_nonempty
    exact ⟨i, fun j => hi j (mem_univ j)⟩
  choose star hst using hstar
  have hmaster := master D M c hc0 (fun j => (hcap j).le) star
  -- bound on values
  set K := ∑ i, ∑ k, (D i).val k with hKdef
  have hKv : ∀ i k, (D i).val k ≤ K := fun i k =>
    (single_le_sum (f := fun k => (D i).val k) (fun k _ => (D i).val_nonneg k) (mem_univ k)).trans
      (single_le_sum (f := fun i => ∑ k, (D i).val k)
        (fun i _ => sum_nonneg fun k _ => (D i).val_nonneg k) (mem_univ i))
  have hK : 0 ≤ K := sum_nonneg fun i _ => sum_nonneg fun k _ => (D i).val_nonneg k
  rw [excess_integral D c hc0 star hst K hK hKv] at hmaster
  -- pointwise bound
  set al : ι → ℝ := fun j => C.alpha (c j / l) with hal
  have halp : ∀ j, 0 < al j := fun j => C.alpha_pos _
  set G : ι → ℝ → ℝ := fun j t => wf C.a C.s ((c j + t) / l) * (D j).tail (c j + t)
    + r j / l * Rf C.a C.s (al j) ((c j + t) / l) with hG
  have hpt : ∀ t ∈ Set.Ioo (0:ℝ) K,
      (∑ j, (D j).tail (c j + t) - 1 + ∏ j, (1 - (D j).tail (c j + t))) ≤ ∑ j, G j t := by
    intro t ht
    have hu : ∀ j, 0 < c j + t := fun j => add_pos_of_nonneg_of_pos (hc0 j) ht.1
    have hx0 : ∀ j, 0 ≤ (D j).tail (c j + t) := fun j => FinDist.tail_nonneg _ _
    have hxr : ∀ j, (D j).tail (c j + t) ≤ r j / (c j + t) := fun j => by
      rw [le_div_iff₀ (hu j), mul_comm]; exact mul_tail_le _ _ (hu j).le
    refine (inclusion_le_phi _ (fun j => tail_le_one _ _)).trans ?_
    have hlam : ∑ j, r j / al j / l = 1 := by
      rw [← sum_div, hlsum, div_self hl.ne']
    refine (phi_jensen _ (fun j => r j / al j / l) (fun j => al j / ((c j + t) / l))
      (fun j => div_nonneg (div_nonneg (hr0 j) (halp j).le) hl.le) hlam
      (fun j => div_pos (halp j) (div_pos (hu j) hl)) hx0 ?_).trans ?_
    · intro j
      refine (hxr j).trans (le_of_eq ?_)
      have := (halp j).ne'; have := hl.ne'; have := (hu j).ne'
      field_simp
    · refine sum_le_sum fun j _ => ?_
      rw [hG]
      dsimp only
      set v := (c j + t) / l with hv
      have hvp : 0 < v := div_pos (hu j) hl
      unfold Rf
      set m := max (psi (al j / v) - wf C.a C.s v) 0 with hm
      have h1 : psi (al j / v) ≤ wf C.a C.s v + m := by
        have := le_max_left (psi (al j / v) - wf C.a C.s v) 0; linarith
      have hm0 : 0 ≤ m := le_max_right _ _
      have h2 : r j / l * (m / v) = r j / (c j + t) * m := by
        rw [hv]; have := hl.ne'; have := (hu j).ne'; field_simp
      rw [h2]
      calc (D j).tail (c j + t) * psi (al j / v) ≤
            (D j).tail (c j + t) * (wf C.a C.s v + m) := mul_le_mul_of_nonneg_left h1 (hx0 j)
        _ = wf C.a C.s v * (D j).tail (c j + t) + (D j).tail (c j + t) * m := by ring
        _ ≤ _ := by
            have := mul_le_mul_of_nonneg_right (hxr j) hm0
            linarith
  -- integrability and integrals of the pieces
  have hlin_ii : ∀ j, IntervalIntegrable
      (fun t => wf C.a C.s ((c j + t) / l) * (D j).tail (c j + t)) volume 0 K :=
    fun j => tail_ii (D j) (c j) 0 K _ ((wf_continuous C.a C.s).comp (by fun_prop))
  have hR_ii : ∀ j, IntervalIntegrable
      (fun t => r j / l * Rf C.a C.s (al j) ((c j + t) / l)) volume 0 K := by
    intro j
    rcases eq_or_lt_of_le (hr0 j) with h | h
    · simp [← h]
    · refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hK]
      refine continuousOn_const.mul
        ((Rf_contOn C.a C.s (al j) (halp j)).comp (by fun_prop) ?_)
      intro t ht
      exact div_pos (add_pos_of_pos_of_nonneg (hcpos j h) ht.1) hl
  have hG_ii : ∀ j, IntervalIntegrable (G j) volume 0 K := fun j => (hlin_ii j).add (hR_ii j)
  have hint : ∫ t in (0:ℝ)..K, (∑ j, (D j).tail (c j + t) - 1 + ∏ j, (1 - (D j).tail (c j + t)))
      ≤ ∫ t in (0:ℝ)..K, ∑ j, G j t :=
    intervalIntegral.integral_mono_on_of_le_Ioo hK (integrand_ii D c star hst 0 K)
      (ii_sum _ hG_ii) hpt
  rw [intervalIntegral.integral_finset_sum (fun j _ => hG_ii j)] at hint
  -- each item
  have hitem : ∀ j, ∫ t in (0:ℝ)..K, G j t ≤
      l * E1 (D j) (fun x => What C.a C.s (x / l)) + r j * (C.g - C.kappa / al j) := by
    intro j
    rw [hG]
    dsimp only
    rw [intervalIntegral.integral_add (hlin_ii j) (hR_ii j),
      linear_part C (D j) (c j) l K (hc0 j) hl hK (hKv j)]
    rcases eq_or_lt_of_le (hr0 j) with h | h
    · rw [← h]
      simp only [zero_div, zero_mul, intervalIntegral.integral_zero, add_zero]
      have : 0 ≤ E1 (D j) (fun x => What C.a C.s (min x (c j) / l)) :=
        E1_nonneg _ fun k => What_nonneg C.a C.s C.a_nonneg C.s_pos _
          (div_nonneg (le_min ((D j).val_nonneg k) (hc0 j)) hl.le)
      nlinarith
    · have hcj := hcpos j h
      have ht : 0 < c j / l := div_pos hcj hl
      -- lower part
      have h1 : r j * (What C.a C.s (c j / l) / (c j / l)) ≤
          l * E1 (D j) (fun x => What C.a C.s (min x (c j) / l)) := by
        have h2 : E1 (D j) (fun x => (What C.a C.s (c j / l) / c j) * min x (c j)) ≤
            E1 (D j) (fun x => What C.a C.s (min x (c j) / l)) := by
          refine E1_mono _ fun k => ?_
          have hm0 : 0 ≤ min ((D j).val k) (c j) := le_min ((D j).val_nonneg k) hcj.le
          have h3 := What_secant C.a C.s C.a_nonneg C.s_pos (min ((D j).val k) (c j) / l) (c j / l)
            ht (div_nonneg hm0 hl.le) (div_le_div_of_nonneg_right (min_le_right _ _) hl.le)
          refine le_trans (le_of_eq ?_) h3
          have := hcj.ne'; have := hl.ne'
          field_simp
        rw [E1_mul, hcap j] at h2
        have h4 := mul_le_mul_of_nonneg_left h2 hl.le
        refine le_trans (le_of_eq ?_) h4
        have := hcj.ne'; have := hl.ne'
        change r j * _ = l * (_ * r j)
        field_simp
      -- remainder
      have h5 : ∫ t in (0:ℝ)..K, r j / l * Rf C.a C.s (al j) ((c j + t) / l) =
          r j * ∫ v in (c j / l)..((c j + K) / l), Rf C.a C.s (al j) v := by
        rw [intervalIntegral.integral_const_mul]
        have h6 := intervalIntegral.integral_comp_div_add (a := 0) (b := K)
          (fun v => Rf C.a C.s (al j) v) hl.ne' (c j / l)
        rw [smul_eq_mul, zero_div, zero_add] at h6
        have e : ∀ t, (c j + t) / l = t / l + c j / l := fun t => by ring
        simp_rw [e]
        rw [h6, ← mul_assoc, div_mul_cancel₀ _ hl.ne']
      have h7 := C.cert (c j / l) ((c j + K) / l) ht
        (div_le_div_of_nonneg_right (by linarith) hl.le)
      have h8 := mul_le_mul_of_nonneg_left h7 h.le
      rw [h5]
      have : r j * (C.kappa / C.alpha (c j / l)
          + (∫ v in (c j / l)..((c j + K) / l), Rf C.a C.s (C.alpha (c j / l)) v)
          - What C.a C.s (c j / l) / (c j / l)) =
          r j * (C.kappa / al j) + r j * (∫ v in (c j / l)..((c j + K) / l), Rf C.a C.s (al j) v)
          - r j * (What C.a C.s (c j / l) / (c j / l)) := by rw [hal]; ring
      rw [this] at h8
      linarith
  have hsum := hint.trans (sum_le_sum fun j _ => hitem j)
  rw [sum_add_distrib] at hsum
  -- Laplace part
  have hW : ∑ j, l * E1 (D j) (fun x => What C.a C.s (x / l)) ≤ l * C.kappa + C.b * BREV D := by
    have e1 : ∀ j, E1 (D j) (fun x => What C.a C.s (x / l)) =
        ∑ i, C.a i * C.s i * E1 (D j) (fun x => 1 - Real.exp (-(1 / (l * C.s i) * x))) := by
      intro j
      unfold What E1
      simp_rw [mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun i _ => sum_congr rfl fun k _ => ?_
      have : (D j).val k / l / C.s i = 1 / (l * C.s i) * (D j).val k := by
        have := hl.ne'; have := (C.s_pos i).ne'; field_simp
      rw [this]; ring
    simp_rw [e1, mul_sum]
    rw [sum_comm]
    have h1 : ∀ i, ∑ j, l * (C.a i * C.s i *
        E1 (D j) (fun x => 1 - Real.exp (-(1 / (l * C.s i) * x)))) ≤
        l * (C.a i * C.s i * C.kp i) + C.a i * C.bb i * BREV D := by
      intro i
      have h := laplace_sum D hB (1 / (l * C.s i)) (C.kp i) (C.bb i)
        (div_pos one_pos (mul_pos hl (C.s_pos i))) (C.tan i)
      have h2 := mul_le_mul_of_nonneg_left h
        (mul_nonneg hl.le (mul_nonneg (C.a_nonneg i) (C.s_pos i).le))
      rw [mul_sum] at h2
      refine le_trans (le_of_eq (sum_congr rfl fun j _ => by ring)) (h2.trans (le_of_eq ?_))
      have := hl.ne'; have := (C.s_pos i).ne'
      field_simp
    refine (sum_le_sum fun i _ => h1 i).trans ?_
    rw [sum_add_distrib, ← mul_sum, ← sum_mul]
    have h3 := mul_le_mul_of_nonneg_left C.kappa_ge hl.le
    have h4 := mul_le_mul_of_nonneg_right C.b_ge hB.le
    linarith
  have hk : ∑ j, r j * (C.g - C.kappa / al j) = C.g * SREV D - l * C.kappa := by
    have : ∀ j, r j * (C.g - C.kappa / al j) = C.g * r j - C.kappa * (r j / al j) := by
      intro j; ring
    simp_rw [this]
    rw [sum_sub_distrib, ← mul_sum, ← mul_sum, hlsum]
    change C.g * SREV D - _ = _
    ring
  rw [hk] at hsum
  linarith

end UB
end Sievert26SimpleAuctions

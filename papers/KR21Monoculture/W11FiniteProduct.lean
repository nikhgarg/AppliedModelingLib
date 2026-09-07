import KR21Monoculture.W11ScoreSpace
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open AppliedModelingLib MeasureTheory Filter
open scoped Topology ENNReal

namespace KR21Monoculture

/-!
# Binary `L¹` external products for the corrected Theorem 5 route

The corrected score-space route needs to pass from one translated noise
density to a finite iid product.  This file supplies the binary induction
step: external multiplication of two `L¹` functions on independent spaces is
a bounded bilinear map into `L¹` on their product measure.  Consequently it
obeys the ordinary Banach-space product rule.

The remaining theorem-specific work is to reindex a finite product of copies
of `volume` onto the paper's `Candidate n -> ℝ` space and identify the paper's
ranking cell with a fixed measurable event in that product space.
-/

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β}
variable [SFinite μ] [SFinite ν]

/-- The independent external product of two real `L¹` functions. -/
noncomputable def l1ExternalProduct (f : α →₁[μ] ℝ) (g : β →₁[ν] ℝ) :
    (α × β) →₁[μ.prod ν] ℝ :=
  ((L1.integrable_coeFn f).mul_prod (L1.integrable_coeFn g)).toL1
    (fun z => f z.1 * g z.2)

theorem l1ExternalProduct_ae_eq (f : α →₁[μ] ℝ) (g : β →₁[ν] ℝ) :
    l1ExternalProduct f g =ᵐ[μ.prod ν] fun z => f z.1 * g z.2 :=
  ((L1.integrable_coeFn f).mul_prod (L1.integrable_coeFn g)).coeFn_toL1

theorem l1ExternalProduct_norm (f : α →₁[μ] ℝ) (g : β →₁[ν] ℝ) :
    ‖l1ExternalProduct f g‖ = ‖f‖ * ‖g‖ := by
  rw [l1ExternalProduct, L1.norm_of_fun_eq_integral_norm]
  calc
    (∫ z : α × β, ‖f z.1 * g z.2‖ ∂μ.prod ν) =
        (∫ x : α, ‖f x‖ ∂μ) * ∫ y : β, ‖g y‖ ∂ν := by
      simpa only [norm_mul] using
        (integral_prod_mul (μ := μ) (ν := ν) (fun x : α => ‖f x‖)
          (fun y : β => ‖g y‖))
    _ = ‖f‖ * ‖g‖ := by
      rw [← L1.norm_eq_integral_norm f, ← L1.norm_eq_integral_norm g]

private theorem l1ExternalProduct_add_left (f₁ f₂ : α →₁[μ] ℝ) (g : β →₁[ν] ℝ) :
    l1ExternalProduct (f₁ + f₂) g =
      l1ExternalProduct f₁ g + l1ExternalProduct f₂ g := by
  have hleft :
      (fun z : α × β => (f₁ + f₂) z.1) =ᵐ[μ.prod ν]
        fun z => f₁ z.1 + f₂ z.1 := by
    simpa only [Function.comp_apply] using
      (MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae_eq_comp
        (Lp.coeFn_add f₁ f₂)
  apply Lp.ext
  filter_upwards [l1ExternalProduct_ae_eq (f₁ + f₂) g,
    l1ExternalProduct_ae_eq f₁ g, l1ExternalProduct_ae_eq f₂ g,
    hleft,
    Lp.coeFn_add (l1ExternalProduct f₁ g) (l1ExternalProduct f₂ g)] with z hsum h₁ h₂ hleft hright
  rw [hsum, hright]
  simp only [Pi.add_apply]
  rw [hleft, h₁, h₂]
  ring

private theorem l1ExternalProduct_smul_left (c : ℝ) (f : α →₁[μ] ℝ) (g : β →₁[ν] ℝ) :
    l1ExternalProduct (c • f) g = c • l1ExternalProduct f g := by
  have hf :
      (fun z : α × β => (c • f) z.1) =ᵐ[μ.prod ν]
        fun z => c • f z.1 := by
    simpa only [Function.comp_apply] using
      (MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae_eq_comp
        (Lp.coeFn_smul c f)
  apply Lp.ext
  filter_upwards [l1ExternalProduct_ae_eq (c • f) g,
    l1ExternalProduct_ae_eq f g,
    hf,
    Lp.coeFn_smul c (l1ExternalProduct f g)] with z hleft hprod hf hright
  rw [hleft, hright]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hf, hprod]
  ring

private theorem l1ExternalProduct_add_right (f : α →₁[μ] ℝ) (g₁ g₂ : β →₁[ν] ℝ) :
    l1ExternalProduct f (g₁ + g₂) =
      l1ExternalProduct f g₁ + l1ExternalProduct f g₂ := by
  have hright' :
      (fun z : α × β => (g₁ + g₂) z.2) =ᵐ[μ.prod ν]
        fun z => g₁ z.2 + g₂ z.2 := by
    simpa only [Function.comp_apply] using
      (MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae_eq_comp
        (Lp.coeFn_add g₁ g₂)
  apply Lp.ext
  filter_upwards [l1ExternalProduct_ae_eq f (g₁ + g₂),
    l1ExternalProduct_ae_eq f g₁, l1ExternalProduct_ae_eq f g₂,
    hright',
    Lp.coeFn_add (l1ExternalProduct f g₁) (l1ExternalProduct f g₂)] with z hsum h₁ h₂ hright' hright
  rw [hsum, hright]
  simp only [Pi.add_apply]
  rw [hright', h₁, h₂]
  ring

private theorem l1ExternalProduct_smul_right (c : ℝ) (f : α →₁[μ] ℝ) (g : β →₁[ν] ℝ) :
    l1ExternalProduct f (c • g) = c • l1ExternalProduct f g := by
  have hg :
      (fun z : α × β => (c • g) z.2) =ᵐ[μ.prod ν]
        fun z => c • g z.2 := by
    simpa only [Function.comp_apply] using
      (MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae_eq_comp
        (Lp.coeFn_smul c g)
  apply Lp.ext
  filter_upwards [l1ExternalProduct_ae_eq f (c • g),
    l1ExternalProduct_ae_eq f g,
    hg,
    Lp.coeFn_smul c (l1ExternalProduct f g)] with z hleft hprod hg hright
  rw [hleft, hright]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hg, hprod]
  ring

/-- External multiplication is bounded bilinear with operator bound one. -/
theorem isBoundedBilinearMap_l1ExternalProduct :
    IsBoundedBilinearMap ℝ
      (fun p : (α →₁[μ] ℝ) × (β →₁[ν] ℝ) => l1ExternalProduct p.1 p.2) where
  add_left := l1ExternalProduct_add_left
  smul_left := l1ExternalProduct_smul_left
  add_right := l1ExternalProduct_add_right
  smul_right := l1ExternalProduct_smul_right
  bound := ⟨1, zero_lt_one, by
    intro f g
    rw [l1ExternalProduct_norm]
    simpa only [one_mul] using (le_refl (‖f‖ * ‖g‖))⟩

noncomputable def l1ExternalProductCLM :
    (α →₁[μ] ℝ) →L[ℝ] (β →₁[ν] ℝ) →L[ℝ] ((α × β) →₁[μ.prod ν] ℝ) :=
  (isBoundedBilinearMap_l1ExternalProduct (μ := μ) (ν := ν)).toContinuousLinearMap

theorem l1ExternalProductCLM_apply (f : α →₁[μ] ℝ) (g : β →₁[ν] ℝ) :
    l1ExternalProductCLM f g = l1ExternalProduct f g :=
  rfl

/-- Product rule for two independent `L¹` density curves. -/
theorem l1ExternalProduct_hasDerivAt
    {F : ℝ → α →₁[μ] ℝ} {G : ℝ → β →₁[ν] ℝ}
    {F' : α →₁[μ] ℝ} {G' : β →₁[ν] ℝ} {theta : ℝ}
    (hF : HasDerivAt F F' theta) (hG : HasDerivAt G G' theta) :
    HasDerivAt (fun t => l1ExternalProduct (F t) (G t))
      (l1ExternalProduct F' (G theta) + l1ExternalProduct (F theta) G') theta := by
  simpa only [l1ExternalProductCLM_apply, add_comm] using
    ContinuousLinearMap.hasDerivAt_of_bilinear
      (B := l1ExternalProductCLM (μ := μ) (ν := ν))
      (fun _ => hF) (fun _ => hG)

/-- Integration over a fixed product-space set, bundled as an `L¹` functional. -/
noncomputable def l1ProductSetIntegralCLM (s : Set (α × β)) :
    ((α × β) →₁[μ.prod ν] ℝ) →L[ℝ] ℝ :=
  L1.integralCLM.comp (LpToLpRestrictCLM (α × β) ℝ ℝ (μ.prod ν) 1 s)

theorem l1ProductSetIntegralCLM_apply (s : Set (α × β))
    (z : (α × β) →₁[μ.prod ν] ℝ) :
    l1ProductSetIntegralCLM s z = ∫ x in s, z x ∂μ.prod ν := by
  rw [l1ProductSetIntegralCLM, ContinuousLinearMap.comp_apply, ← L1.integral_eq,
    L1.integral_eq_integral]
  apply integral_congr_ae
  exact LpToLpRestrictCLM_coeFn ℝ s z

/-- A fixed product-space event functional preserves `L¹` derivatives. -/
theorem l1ProductSetIntegralCLM_hasDerivAt
    (s : Set (α × β)) {H : ℝ → (α × β) →₁[μ.prod ν] ℝ}
    {H' : (α × β) →₁[μ.prod ν] ℝ} {theta : ℝ}
    (hH : HasDerivAt H H' theta) :
    HasDerivAt (fun t => l1ProductSetIntegralCLM s (H t))
      (l1ProductSetIntegralCLM s H') theta := by
  simpa only [Function.comp_apply] using
    (l1ProductSetIntegralCLM s).hasFDerivAt.comp_hasDerivAt theta hH

/-- Ordinary set-integral form of the fixed-event `L¹` derivative lift. -/
theorem l1ProductSetIntegral_hasDerivAt
    (s : Set (α × β)) {H : ℝ → (α × β) →₁[μ.prod ν] ℝ}
    {H' : (α × β) →₁[μ.prod ν] ℝ} {theta : ℝ}
    (hH : HasDerivAt H H' theta) :
    HasDerivAt (fun t => ∫ x in s, H t x ∂μ.prod ν)
      (∫ x in s, H' x ∂μ.prod ν) theta := by
  simpa only [l1ProductSetIntegralCLM_apply] using
    l1ProductSetIntegralCLM_hasDerivAt s hH

/-- The two-coordinate iid score-density curve has the expected `L¹` derivative. -/
theorem scoreTranslateL1_pair_hasDerivAt_of_global_W11
    (f derivative : ℝ → ℝ)
    (hf : Integrable f volume) (hderivative : Integrable derivative volume)
    (absolute_continuity : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (derivative_ae_eq : derivative =ᵐ[volume] deriv f)
    (theta coefficient : ℝ) :
    HasDerivAt
      (fun t => l1ExternalProduct
        (scoreTranslateL1 (t * coefficient) (hf.toL1 f))
        (scoreTranslateL1 (t * coefficient) (hf.toL1 f)))
      (l1ExternalProduct
          ((-coefficient) • scoreTranslateL1 (theta * coefficient) (hderivative.toL1 derivative))
          (scoreTranslateL1 (theta * coefficient) (hf.toL1 f)) +
        l1ExternalProduct
          (scoreTranslateL1 (theta * coefficient) (hf.toL1 f))
          ((-coefficient) • scoreTranslateL1 (theta * coefficient) (hderivative.toL1 derivative)))
      theta := by
  apply l1ExternalProduct_hasDerivAt
  · exact scoreTranslateL1_hasDerivAt_of_global_W11 f derivative hf hderivative
      absolute_continuity derivative_ae_eq theta coefficient
  · exact scoreTranslateL1_hasDerivAt_of_global_W11 f derivative hf hderivative
      absolute_continuity derivative_ae_eq theta coefficient

/-- The two-coordinate iid probability of any fixed score event is differentiable. -/
theorem scoreTranslateL1_pair_setIntegral_hasDerivAt_of_global_W11
    (f derivative : ℝ → ℝ)
    (hf : Integrable f volume) (hderivative : Integrable derivative volume)
    (absolute_continuity : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (derivative_ae_eq : derivative =ᵐ[volume] deriv f)
    (s : Set (ℝ × ℝ)) (theta coefficient : ℝ) :
    HasDerivAt
      (fun t => l1ProductSetIntegralCLM s
        (l1ExternalProduct
          (scoreTranslateL1 (t * coefficient) (hf.toL1 f))
          (scoreTranslateL1 (t * coefficient) (hf.toL1 f))))
      (l1ProductSetIntegralCLM s
        (l1ExternalProduct
            ((-coefficient) • scoreTranslateL1 (theta * coefficient)
              (hderivative.toL1 derivative))
            (scoreTranslateL1 (theta * coefficient) (hf.toL1 f)) +
          l1ExternalProduct
            (scoreTranslateL1 (theta * coefficient) (hf.toL1 f))
            ((-coefficient) • scoreTranslateL1 (theta * coefficient)
              (hderivative.toL1 derivative)))) theta := by
  apply l1ProductSetIntegralCLM_hasDerivAt
  exact scoreTranslateL1_pair_hasDerivAt_of_global_W11 f derivative hf hderivative
    absolute_continuity derivative_ae_eq theta coefficient

/-- Ordinary set-integral form of the two-score iid derivative theorem. -/
theorem scoreTranslateL1_pair_integral_hasDerivAt_of_global_W11
    (f derivative : ℝ → ℝ)
    (hf : Integrable f volume) (hderivative : Integrable derivative volume)
    (absolute_continuity : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (derivative_ae_eq : derivative =ᵐ[volume] deriv f)
    (s : Set (ℝ × ℝ)) (theta coefficient : ℝ) :
    HasDerivAt
      (fun t => ∫ z in s,
        l1ExternalProduct
          (scoreTranslateL1 (t * coefficient) (hf.toL1 f))
          (scoreTranslateL1 (t * coefficient) (hf.toL1 f)) z)
      (∫ z in s,
        (l1ExternalProduct
            ((-coefficient) • scoreTranslateL1 (theta * coefficient)
              (hderivative.toL1 derivative))
            (scoreTranslateL1 (theta * coefficient) (hf.toL1 f)) +
          l1ExternalProduct
            (scoreTranslateL1 (theta * coefficient) (hf.toL1 f))
            ((-coefficient) • scoreTranslateL1 (theta * coefficient)
              (hderivative.toL1 derivative))) z) theta := by
  apply l1ProductSetIntegral_hasDerivAt
  exact scoreTranslateL1_pair_hasDerivAt_of_global_W11 f derivative hf hderivative
    absolute_continuity derivative_ae_eq theta coefficient

end KR21Monoculture

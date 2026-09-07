import KR21Monoculture.W11Definition1Correction
import KR21Monoculture.RUM
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Global `W^{1,1}` regularity of the source Laplace noise

The source Laplace density has a kink at zero, so it is not appropriate to
claim pointwise differentiability there.  This module proves the corrected
facts actually needed by the global-`W^{1,1}` route: global absolute
continuity, an integrable weak derivative agreeing with `deriv` almost
everywhere, strict positivity, and normalization.
-/

open AppliedModelingLib MeasureTheory Filter
open scoped ENNReal Topology

namespace KR21Monoculture

/-- The a.e. derivative of the centered Laplace density.  Its value at zero
is immaterial and deliberately not presented as a classical derivative. -/
noncomputable def laplacePDFWeakDerivative (lam : ℝ) (x : ℝ) : ℝ :=
  if x < 0 then lam * theorem7LaplacePDF lam 0 x
  else -lam * theorem7LaplacePDF lam 0 x

/-- On the nonnegative half line, the exponential factor in a Laplace density
is `lam`-Lipschitz; composing it with absolute value gives a global bound. -/
theorem laplace_exp_abs_lipschitz {lam : ℝ} (hlam : 0 < lam) :
    LipschitzWith ⟨lam, hlam.le⟩
      (fun x : ℝ => Real.exp (-lam * |x|)) := by
  let g : ℝ → ℝ := fun t => Real.exp (-lam * t)
  have hdiff : ∀ t ∈ Set.Ici (0 : ℝ), DifferentiableAt ℝ g t := by
    intro t _
    exact (Real.hasDerivAt_exp (-lam * t)).comp t
      ((hasDerivAt_const t (-lam)).mul (hasDerivAt_id t)) |>.differentiableAt
  have hbound : ∀ t ∈ Set.Ici (0 : ℝ), ‖fderiv ℝ g t‖₊ ≤ ⟨lam, hlam.le⟩ := by
    intro t ht
    have hderiv : HasDerivAt g (Real.exp (-lam * t) * (-lam)) t := by
      convert (Real.hasDerivAt_exp (-lam * t)).comp t
        ((hasDerivAt_const t (-lam)).mul (hasDerivAt_id t)) using 1 <;>
        simp [g, Function.comp_def] <;> ring
    apply (NNReal.coe_le_coe).mp
    change ‖fderiv ℝ g t‖ ≤ lam
    rw [← norm_deriv_eq_norm_fderiv, hderiv.deriv]
    have hproduct : 0 ≤ lam * t := mul_nonneg hlam.le ht
    have hexp : Real.exp (-lam * t) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_neg, abs_of_pos hlam]
    exact mul_le_of_le_one_left hlam.le hexp
  have hg : LipschitzOnWith ⟨lam, hlam.le⟩ g (Set.Ici 0) :=
    (convex_Ici 0).lipschitzOnWith_of_nnnorm_fderiv_le hdiff hbound
  have habs : LipschitzOnWith 1 (fun x : ℝ => |x|) Set.univ := by
    simpa only [Real.norm_eq_abs] using
      (lipschitzWith_one_norm (E := ℝ)).lipschitzOnWith
  have hmaps : Set.MapsTo (fun x : ℝ => |x|) Set.univ (Set.Ici 0) := by
    intro x _
    exact abs_nonneg x
  simpa [g, Function.comp_def] using hg.comp habs hmaps

/-- The centered Laplace density is absolutely continuous on every interval,
including intervals crossing its zero kink. -/
theorem laplacePDF_absolutelyContinuousOnInterval
    {lam : ℝ} (hlam : 0 < lam) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (theorem7LaplacePDF lam 0) a b := by
  have hbase : AbsolutelyContinuousOnInterval
      (fun x : ℝ => Real.exp (-lam * |x|)) a b :=
    (laplace_exp_abs_lipschitz hlam).lipschitzOnWith.absolutelyContinuousOnInterval
  convert hbase.const_mul (lam / 2) using 1
  funext x
  simp [theorem7LaplacePDF, sub_zero]

/-- Away from its unique kink, the displayed weak derivative is the genuine
classical derivative of the centered Laplace density. -/
theorem laplacePDF_hasDerivAt_of_ne_zero
    {lam x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (theorem7LaplacePDF lam 0)
      (laplacePDFWeakDerivative lam x) x := by
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · let right : ℝ → ℝ := fun y => lam / 2 * Real.exp (-lam * (0 - y))
    have hright : HasDerivAt right
        (lam * theorem7LaplacePDF lam 0 x) x := by
      have hcalc := (hasDerivAt_const x (lam / 2)).mul
        ((Real.hasDerivAt_exp (-lam * (0 - x))).comp x
          ((hasDerivAt_const x (-lam)).mul
            ((hasDerivAt_const x 0).sub (hasDerivAt_id x))))
      convert hcalc using 1 <;>
        simp [right, theorem7LaplacePDF_of_le_mean (le_of_lt hxneg)] <;> ring
    have heq : theorem7LaplacePDF lam 0 =ᶠ[nhds x] right :=
      Set.EqOn.eventuallyEq_of_mem (fun y hy => theorem7LaplacePDF_of_le_mean (le_of_lt hy))
        (Iio_mem_nhds hxneg)
    rw [laplacePDFWeakDerivative, if_pos hxneg]
    exact hright.congr_of_eventuallyEq heq
  · let right : ℝ → ℝ := fun y => lam / 2 * Real.exp (-lam * (y - 0))
    have hright : HasDerivAt right
        (-lam * theorem7LaplacePDF lam 0 x) x := by
      have hcalc := (hasDerivAt_const x (lam / 2)).mul
        ((Real.hasDerivAt_exp (-lam * (x - 0))).comp x
          ((hasDerivAt_const x (-lam)).mul
            ((hasDerivAt_id x).sub (hasDerivAt_const x 0))))
      convert hcalc using 1 <;>
        simp [right, theorem7LaplacePDF_of_mean_le (le_of_lt hxpos)] <;> ring
    have heq : theorem7LaplacePDF lam 0 =ᶠ[nhds x] right :=
      Set.EqOn.eventuallyEq_of_mem (fun y hy => theorem7LaplacePDF_of_mean_le (le_of_lt hy))
        (Ioi_mem_nhds hxpos)
    rw [laplacePDFWeakDerivative, if_neg (not_lt_of_ge hxpos.le)]
    exact hright.congr_of_eventuallyEq heq

/-- The weak derivative agrees with the classical derivative almost
everywhere; the only omitted point is the source density's kink. -/
theorem laplacePDFWeakDerivative_ae_eq_deriv
    {lam : ℝ} :
    laplacePDFWeakDerivative lam =ᵐ[volume]
      deriv (theorem7LaplacePDF lam 0) := by
  have hne : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
    rw [ae_iff]
    simpa using (show volume ({0} : Set ℝ) = 0 by simp)
  filter_upwards [hne] with x hx
  exact (laplacePDF_hasDerivAt_of_ne_zero hx).deriv.symm

/-- The centered positive-rate Laplace density is integrable. -/
theorem laplacePDF_integrable
    {lam : ℝ} (hlam : 0 < lam) :
    Integrable (theorem7LaplacePDF lam 0) volume := by
  have hleft : IntegrableOn (theorem7LaplacePDF lam 0) (Set.Iic 0) :=
    theorem7LaplacePDF_integrableOn_Iic (lam := lam) (μ := 0) (a := 0) hlam
  have hright_open_exp : IntegrableOn
      (fun x : ℝ => lam / 2 * Real.exp ((-lam) * x)) (Set.Ioi 0) := by
    exact (integrableOn_exp_mul_Ioi (a := -lam) (by linarith) 0).const_mul (lam / 2)
  have hright_open : IntegrableOn (theorem7LaplacePDF lam 0) (Set.Ioi 0) := by
    refine hright_open_exp.congr_fun ?_ measurableSet_Ioi
    intro x hx
    rw [theorem7LaplacePDF_of_mean_le hx.le]
    congr 2
    ring
  have hright : IntegrableOn (theorem7LaplacePDF lam 0) (Set.Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi
      (f := theorem7LaplacePDF lam 0) (b := 0)).mpr hright_open
  have hunion := hleft.union hright
  rw [show Set.Iic (0 : ℝ) ∪ Set.Ici 0 = Set.univ by ext x; simp] at hunion
  exact integrableOn_univ.mp hunion

/-- The weak derivative has the same absolute value as `lam` times the
density. -/
theorem abs_laplacePDFWeakDerivative
    {lam : ℝ} (hlam : 0 < lam) (x : ℝ) :
    |laplacePDFWeakDerivative lam x| =
      lam * theorem7LaplacePDF lam 0 x := by
  rw [laplacePDFWeakDerivative]
  split_ifs with hx
  · rw [abs_mul, abs_of_pos hlam,
      abs_of_nonneg (theorem7LaplacePDF_nonneg (lam := lam) (μ := 0) (x := x) hlam.le)]
  · rw [abs_mul, abs_neg, abs_of_pos hlam,
      abs_of_nonneg (theorem7LaplacePDF_nonneg (lam := lam) (μ := 0) (x := x) hlam.le)]

/-- The a.e. derivative is integrable. -/
theorem laplacePDFWeakDerivative_integrable
    {lam : ℝ} (hlam : 0 < lam) :
    Integrable (laplacePDFWeakDerivative lam) volume := by
  have hf := laplacePDF_integrable hlam
  apply (hf.const_mul lam).mono
  · unfold laplacePDFWeakDerivative
    exact (Measurable.ite measurableSet_Iio
      (measurable_const.mul (theorem7LaplacePDF_continuous lam 0).measurable)
      (measurable_const.mul (theorem7LaplacePDF_continuous lam 0).measurable)).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_laplacePDFWeakDerivative hlam x,
      Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hlam.le
        (theorem7LaplacePDF_nonneg (lam := lam) (μ := 0) (x := x) hlam.le))]

/-- The literal source's unit-variance Laplace base density. -/
noncomputable def sourceUnitVarianceLaplaceBaseDensity : ℝ → ℝ :=
  theorem7LaplacePDF (Real.sqrt 2) 0

/-- Its globally valid `W^{1,1}` weak derivative. -/
noncomputable def sourceUnitVarianceLaplaceBaseWeakDerivative : ℝ → ℝ :=
  laplacePDFWeakDerivative (Real.sqrt 2)

/-- All analytic facts required by the repaired global-`W^{1,1}` Definition-1
route for the source's literal unit-variance Laplace innovations. -/
structure SourceUnitVarianceLaplaceW11Regularity : Prop where
  density_integrable : Integrable sourceUnitVarianceLaplaceBaseDensity volume
  derivative_integrable : Integrable sourceUnitVarianceLaplaceBaseWeakDerivative volume
  density_measurable : Measurable sourceUnitVarianceLaplaceBaseDensity
  density_positive : ∀ x, 0 < sourceUnitVarianceLaplaceBaseDensity x
  absolute_continuity : ∀ a b,
    AbsolutelyContinuousOnInterval sourceUnitVarianceLaplaceBaseDensity a b
  derivative_ae_eq : sourceUnitVarianceLaplaceBaseWeakDerivative =ᵐ[volume]
    deriv sourceUnitVarianceLaplaceBaseDensity
  normalized : ∫⁻ x, ENNReal.ofReal (sourceUnitVarianceLaplaceBaseDensity x) = 1

/-- The source-normalized Laplace base density satisfies the complete repaired
global-`W^{1,1}` hypothesis package. -/
theorem sourceUnitVarianceLaplace_w11Regularity :
    SourceUnitVarianceLaplaceW11Regularity := by
  have hrate : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  exact {
    density_integrable := by
      simpa [sourceUnitVarianceLaplaceBaseDensity] using laplacePDF_integrable hrate
    derivative_integrable := by
      simpa [sourceUnitVarianceLaplaceBaseWeakDerivative] using
        laplacePDFWeakDerivative_integrable hrate
    density_measurable := by
      simpa [sourceUnitVarianceLaplaceBaseDensity] using
        (theorem7LaplacePDF_continuous (Real.sqrt 2) 0).measurable
    density_positive := by
      intro x
      simpa [sourceUnitVarianceLaplaceBaseDensity] using
        theorem7LaplacePDF_pos (lam := Real.sqrt 2) (μ := 0) (x := x) hrate
    absolute_continuity := by
      intro a b
      simpa [sourceUnitVarianceLaplaceBaseDensity] using
        laplacePDF_absolutelyContinuousOnInterval hrate a b
    derivative_ae_eq := by
      simpa [sourceUnitVarianceLaplaceBaseDensity,
        sourceUnitVarianceLaplaceBaseWeakDerivative] using
        (laplacePDFWeakDerivative_ae_eq_deriv (lam := Real.sqrt 2))
    normalized := by
      simpa [sourceUnitVarianceLaplaceBaseDensity] using
        theorem7LaplacePDF_lintegral_eq_one (lam := Real.sqrt 2) (μ := 0) hrate
  }

end KR21Monoculture

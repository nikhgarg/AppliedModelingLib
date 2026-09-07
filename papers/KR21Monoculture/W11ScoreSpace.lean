import KR21Monoculture.Theorem5Differentiability
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Analysis.Convolution

open AppliedModelingLib MeasureTheory Filter
open scoped Topology ENNReal

namespace KR21Monoculture

/-!
# Score-space `L¹` translation kernel for the corrected Theorem 5 route

This file concerns the corrected model only.  It does not assert the archival
Theorem 5, which is false under its printed density hypotheses.

For a density representative `f`, score-space translation is
`x ↦ f (x - a)`.  Mathlib's continuous domain action gives the key `L¹`
continuity fact for every integrable function.  The score-space
`W^{1,1}` derivative is proved below by a scalar fundamental identity,
joint integrability on finite shift intervals, and a Bochner/Fubini lift.
Finite-product and ranking-cell lifts remain separate obligations.
-/

/-- The `L¹` class of the score-space translate `x ↦ f (x - shift)`. -/
noncomputable def scoreTranslateL1 (shift : ℝ) (f : ℝ →₁[volume] ℝ) :
    ℝ →₁[volume] ℝ :=
  DomAddAct.mk (-shift) +ᵥ f

/-- `scoreTranslateL1` has the expected almost-everywhere pointwise representative. -/
theorem scoreTranslateL1_ae_eq (shift : ℝ) (f : ℝ →₁[volume] ℝ) :
    scoreTranslateL1 shift f =ᵐ[volume] fun x => f (x - shift) := by
  simpa [scoreTranslateL1, sub_eq_add_neg, add_comm] using
    (DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk (-shift)) f)

/-- Translation is continuous in `L¹`; no pointwise domination is used here. -/
theorem continuous_scoreTranslateL1 (f : ℝ →₁[volume] ℝ) :
    Continuous (fun shift : ℝ => scoreTranslateL1 shift f) := by
  letI : Fact ((1 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.one_ne_top⟩
  change Continuous (fun shift : ℝ => DomAddAct.mk (-shift) +ᵥ f)
  exact continuous_vadd.comp
    ((DomAddAct.continuous_mk.comp continuous_neg).prodMk continuous_const)

/-- Score translations preserve the `L¹` norm. -/
theorem norm_scoreTranslateL1 (shift : ℝ) (f : ℝ →₁[volume] ℝ) :
    ‖scoreTranslateL1 shift f‖ = ‖f‖ := by
  simp [scoreTranslateL1]

/--
Global absolute continuity and almost-everywhere agreement with the classical
derivative yield the scalar fundamental-theorem identity needed by the
score-space route.
-/
theorem global_fundamental_of_absolute_continuity
    (f derivative : ℝ → ℝ)
    (absolute_continuity : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (derivative_ae_eq : derivative =ᵐ[volume] deriv f)
    (a b : ℝ) :
    f b - f a = ∫ x in a..b, derivative x := by
  rw [← (absolute_continuity a b).integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [derivative_ae_eq.symm] with x hx _
  exact hx

/--
The pointwise score-space fundamental identity obtained from a global
absolutely-continuous representative.  The hypothesis is the fundamental
theorem characterization of that representative, with its `L¹` derivative
written explicitly.
-/
theorem scoreTranslation_pointwise_increment
    (f derivative : ℝ → ℝ)
    (global_fundamental : ∀ a b : ℝ,
      f b - f a = ∫ y in a..b, derivative y)
    (x start finish coefficient : ℝ) :
    f (x - finish * coefficient) - f (x - start * coefficient) =
      ∫ u in start..finish, (-coefficient) * derivative (x - u * coefficient) := by
  calc
    f (x - finish * coefficient) - f (x - start * coefficient) =
        ∫ y in x - start * coefficient..x - finish * coefficient, derivative y :=
      global_fundamental _ _
    _ = (-coefficient) • ∫ u in start..finish,
        derivative ((-coefficient) * u + x) := by
      convert
        (intervalIntegral.smul_integral_comp_mul_add derivative (-coefficient) x).symm using 1 ;
        ring_nf
    _ = ∫ u in start..finish, (-coefficient) * derivative (x - u * coefficient) := by
      rw [← intervalIntegral.integral_smul]
      apply intervalIntegral.integral_congr
      intro u _
      ring_nf

/-- The pointwise score-space identity specialized to an absolutely continuous density. -/
theorem scoreTranslation_pointwise_increment_of_absolute_continuity
    (f derivative : ℝ → ℝ)
    (absolute_continuity : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (derivative_ae_eq : derivative =ᵐ[volume] deriv f)
    (x start finish coefficient : ℝ) :
    f (x - finish * coefficient) - f (x - start * coefficient) =
      ∫ u in start..finish, (-coefficient) * derivative (x - u * coefficient) :=
  scoreTranslation_pointwise_increment f derivative
    (global_fundamental_of_absolute_continuity f derivative absolute_continuity derivative_ae_eq)
    x start finish coefficient

/-- The Banach-space fundamental-theorem step used by the proved W^{1,1} route below. -/
theorem scoreTranslateL1_hasDerivAt_of_fundamental_identity
    (f fderiv : ℝ →₁[volume] ℝ) (theta coefficient : ℝ)
    (fundamental_identity : ∀ t : ℝ,
      scoreTranslateL1 (t * coefficient) f =
        scoreTranslateL1 (theta * coefficient) f +
          ∫ u in theta..t,
            (-coefficient) • scoreTranslateL1 (u * coefficient) fderiv) :
    HasDerivAt
      (fun t : ℝ => scoreTranslateL1 (t * coefficient) f)
      ((-coefficient) • scoreTranslateL1 (theta * coefficient) fderiv) theta := by
  letI : Fact ((1 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.one_ne_top⟩
  have htranslate : Continuous
      (fun u : ℝ => scoreTranslateL1 (u * coefficient) fderiv) :=
    (continuous_scoreTranslateL1 fderiv).comp (continuous_id.mul continuous_const)
  have hintegrand : Continuous
      (fun u : ℝ => (-coefficient) • scoreTranslateL1 (u * coefficient) fderiv) :=
    htranslate.const_smul (-coefficient)
  have hprimitive : HasDerivAt
      (fun t : ℝ => scoreTranslateL1 (theta * coefficient) f +
        ∫ u in theta..t,
          (-coefficient) • scoreTranslateL1 (u * coefficient) fderiv)
      ((-coefficient) • scoreTranslateL1 (theta * coefficient) fderiv) theta :=
    (hintegrand.integral_hasStrictDerivAt theta theta).hasDerivAt.const_add _
  exact hprimitive.congr_of_eventuallyEq (Filter.Eventually.of_forall fundamental_identity)

noncomputable def scoreSetIntegralCLM (s : Set ℝ) :
    (ℝ →₁[volume] ℝ) →L[ℝ] ℝ :=
  L1.integralCLM.comp (LpToLpRestrictCLM ℝ ℝ ℝ volume 1 s)

theorem scoreSetIntegralCLM_apply (s : Set ℝ) (z : ℝ →₁[volume] ℝ) :
    scoreSetIntegralCLM s z = ∫ x in s, z x := by
  rw [scoreSetIntegralCLM, ContinuousLinearMap.comp_apply, ← L1.integral_eq,
    L1.integral_eq_integral]
  apply integral_congr_ae
  exact LpToLpRestrictCLM_coeFn ℝ s z

theorem scoreSetIntegralCLM_toL1 (s : Set ℝ) (f : ℝ → ℝ)
    (hs : MeasurableSet s) (hf : Integrable f volume) :
    scoreSetIntegralCLM s (hf.toL1 f) = ∫ x in s, f x := by
  rw [scoreSetIntegralCLM_apply]
  apply setIntegral_congr_ae
  · exact hs
  · filter_upwards [(memLp_one_iff_integrable.mpr hf).coeFn_toLp] with x hx _
    exact hx

/-- Bochner/Fubini lift from pointwise finite-interval integrals into `L¹`. -/
theorem intervalIntegral_toL1_fubini
    (F : ℝ → ℝ → ℝ) (a b : ℝ)
    (hsec : ∀ t : ℝ, Integrable (F t) volume)
    (houter : IntervalIntegrable (fun t => (hsec t).toL1 (F t)) volume a b)
    (hjoint : Integrable (Function.uncurry F)
      ((volume.restrict (Set.uIoc a b)).prod volume))
    (hpoint : Integrable (fun x => ∫ t in a..b, F t x) volume) :
    (∫ t in a..b, (hsec t).toL1 (F t)) =
      hpoint.toL1 (fun x => ∫ t in a..b, F t x) := by
  apply Lp.ext
  apply Lp.ae_eq_of_forall_setIntegral_eq _ _ one_ne_zero ENNReal.one_ne_top
  · intro s hs hfinite
    exact (memLp_one_iff_integrable.mp (Lp.memLp _)).integrableOn
  · intro s hs hfinite
    exact (memLp_one_iff_integrable.mp (Lp.memLp _)).integrableOn
  · intro s hs hfinite
    have hjoint_s : Integrable (Function.uncurry F)
        ((volume.restrict (Set.uIoc a b)).prod (volume.restrict s)) := by
      have hmeasure :
          (volume.restrict (Set.uIoc a b)).prod (volume.restrict s) =
            ((volume.restrict (Set.uIoc a b)).prod volume).restrict (Set.univ ×ˢ s) := by
        rw [← Measure.prod_restrict (μ := volume.restrict (Set.uIoc a b)) (ν := volume)
          Set.univ s]
        simp
      rw [hmeasure]
      exact hjoint.restrict
    calc
      ∫ x in s, (∫ t in a..b, (hsec t).toL1 (F t)) x =
          scoreSetIntegralCLM s (∫ t in a..b, (hsec t).toL1 (F t)) :=
        (scoreSetIntegralCLM_apply s _).symm
      _ = ∫ t in a..b, scoreSetIntegralCLM s ((hsec t).toL1 (F t)) := by
        rw [← (scoreSetIntegralCLM s).intervalIntegral_comp_comm houter]
      _ = ∫ t in a..b, ∫ x in s, F t x := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact scoreSetIntegralCLM_toL1 s (F t) hs (hsec t)
      _ = ∫ x in s, ∫ t in a..b, F t x := by
        exact intervalIntegral_integral_swap hjoint_s
      _ = ∫ x in s, (hpoint.toL1 fun x => ∫ t in a..b, F t x) x := by
        rw [← scoreSetIntegralCLM_apply s (hpoint.toL1 _)]
        exact (scoreSetIntegralCLM_toL1 s _ hs hpoint).symm

theorem scoreTranslation_base_joint_integrable
    (derivative : ℝ → ℝ) (hderivative : Integrable derivative volume) (a b : ℝ) :
    Integrable (fun p : ℝ × ℝ => -derivative (p.2 - p.1))
      ((volume.restrict (Set.uIoc a b)).prod volume) := by
  let U : Set ℝ := Set.uIoc a b
  have hU : MeasurableSet U := measurableSet_uIoc
  have hU_finite : volume U ≠ ∞ := by
    rw [show U = Set.Ioc (min a b) (max a b) by simp [U, Set.uIoc]]
    exact measure_Ioc_lt_top.ne
  have hindicator : Integrable (U.indicator fun _ : ℝ => (1 : ℝ)) volume :=
    (integrableOn_const hU_finite).integrable_indicator hU
  have hglobal : Integrable
      (fun p : ℝ × ℝ =>
        (ContinuousLinearMap.mul ℝ ℝ) ((U.indicator fun _ : ℝ => (1 : ℝ)) p.2)
          ((fun x => -derivative x) (p.1 - p.2))) (volume.prod volume) :=
    hindicator.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hderivative.neg
  have hswap := hglobal.swap
  rw [Measure.restrict_prod_eq_prod_univ]
  apply (integrable_congr ?_).mp hswap.restrict
  filter_upwards [ae_restrict_mem (hU.prod MeasurableSet.univ)] with p hp
  simp only [Set.mem_prod, Set.mem_univ, and_true] at hp
  have hpU : p.1 ∈ U := hp
  simp [Set.indicator_of_mem hpU]

theorem scoreTranslation_base_point_integrable
    (derivative : ℝ → ℝ) (hderivative : Integrable derivative volume) (a b : ℝ) :
    Integrable (fun x => ∫ u in a..b, -derivative (x - u)) volume := by
  have hjoint := scoreTranslation_base_joint_integrable derivative hderivative a b
  rcases le_total a b with hab | hba
  · simpa only [intervalIntegral.integral_of_le hab, Set.uIoc_of_le hab,
      Function.uncurry_apply_pair] using hjoint.integral_prod_right
  · have h := hjoint.integral_prod_right.neg
    simpa only [intervalIntegral.integral_of_ge hba, Set.uIoc_of_ge hba,
      Function.uncurry_apply_pair, Pi.neg_apply] using h

theorem scoreTranslation_base_section_toL1
    (derivative : ℝ → ℝ) (hderivative : Integrable derivative volume) (u : ℝ)
    (hsection : Integrable (fun x => -derivative (x - u)) volume) :
    hsection.toL1 (fun x => -derivative (x - u)) =
      -scoreTranslateL1 u (hderivative.toL1 derivative) := by
  apply Lp.ext
  change
    ↑↑(hsection.toL1 (fun x => -derivative (x - u))) =ᵐ[volume]
      ↑↑(-scoreTranslateL1 u (hderivative.toL1 derivative))
  have hderivative_shift :
      (fun x => (hderivative.toL1 derivative) (x - u)) =ᵐ[volume]
        fun x => derivative (x - u) := by
    simpa only [Function.comp_apply] using
      (measurePreserving_sub_right volume u).quasiMeasurePreserving.ae_eq_comp
        hderivative.coeFn_toL1
  filter_upwards [hsection.coeFn_toL1,
    Lp.coeFn_neg (scoreTranslateL1 u (hderivative.toL1 derivative)),
    scoreTranslateL1_ae_eq u (hderivative.toL1 derivative),
    hderivative_shift] with x hleft hneg htranslate hderiv
  rw [hleft]
  calc
    -derivative (x - u) = -((↑↑(scoreTranslateL1 u (hderivative.toL1 derivative)) : ℝ → ℝ) x) :=
      congrArg Neg.neg (htranslate.trans hderiv).symm
    _ = (↑↑(-scoreTranslateL1 u (hderivative.toL1 derivative)) : ℝ → ℝ) x := hneg.symm

theorem scoreTranslateL1_base_fundamental_identity
    (f derivative : ℝ → ℝ)
    (hf : Integrable f volume) (hderivative : Integrable derivative volume)
    (absolute_continuity : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (derivative_ae_eq : derivative =ᵐ[volume] deriv f)
    (start finish : ℝ) :
    scoreTranslateL1 finish (hf.toL1 f) =
      scoreTranslateL1 start (hf.toL1 f) +
        ∫ u in start..finish, -scoreTranslateL1 u (hderivative.toL1 derivative) := by
  let hsection : ∀ u : ℝ, Integrable (fun x => -derivative (x - u)) volume := fun u => by
    simpa only [Pi.neg_apply] using (hderivative.comp_sub_right u).neg
  have hsection_eq : ∀ u : ℝ,
      (hsection u).toL1 (fun x => -derivative (x - u)) =
        -scoreTranslateL1 u (hderivative.toL1 derivative) := fun u =>
    scoreTranslation_base_section_toL1 derivative hderivative u (hsection u)
  have hsection_fun_eq :
      (fun u => (hsection u).toL1 (fun x => -derivative (x - u))) =
        fun u => -scoreTranslateL1 u (hderivative.toL1 derivative) :=
    funext hsection_eq
  have houter : IntervalIntegrable
      (fun u => (hsection u).toL1 (fun x => -derivative (x - u))) volume start finish := by
    rw [hsection_fun_eq]
    exact (continuous_scoreTranslateL1 (hderivative.toL1 derivative)).neg.intervalIntegrable _ _
  have hjoint : Integrable (Function.uncurry fun u x => -derivative (x - u))
      ((volume.restrict (Set.uIoc start finish)).prod volume) :=
    scoreTranslation_base_joint_integrable derivative hderivative start finish
  have hpoint : Integrable (fun x => ∫ u in start..finish, -derivative (x - u)) volume :=
    scoreTranslation_base_point_integrable derivative hderivative start finish
  have hfub := intervalIntegral_toL1_fubini
    (fun u x => -derivative (x - u)) start finish hsection houter hjoint hpoint
  have houter_eq :
      (∫ u in start..finish, -scoreTranslateL1 u (hderivative.toL1 derivative)) =
        hpoint.toL1 (fun x => ∫ u in start..finish, -derivative (x - u)) := by
    calc
      (∫ u in start..finish, -scoreTranslateL1 u (hderivative.toL1 derivative)) =
          ∫ u in start..finish, (hsection u).toL1 (fun x => -derivative (x - u)) := by
        apply intervalIntegral.integral_congr
        intro u hu
        exact (hsection_eq u).symm
      _ = hpoint.toL1 (fun x => ∫ u in start..finish, -derivative (x - u)) := hfub
  have hf_shift (u : ℝ) :
      (fun x => (hf.toL1 f) (x - u)) =ᵐ[volume] fun x => f (x - u) := by
    simpa only [Function.comp_apply] using
      (measurePreserving_sub_right volume u).quasiMeasurePreserving.ae_eq_comp hf.coeFn_toL1
  have hdiff :
      scoreTranslateL1 finish (hf.toL1 f) - scoreTranslateL1 start (hf.toL1 f) =
        hpoint.toL1 (fun x => ∫ u in start..finish, -derivative (x - u)) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub (scoreTranslateL1 finish (hf.toL1 f))
        (scoreTranslateL1 start (hf.toL1 f)),
      scoreTranslateL1_ae_eq finish (hf.toL1 f),
      scoreTranslateL1_ae_eq start (hf.toL1 f),
      hf_shift finish, hf_shift start, hpoint.coeFn_toL1] with x hsub hfinish hstart
        hffinish hfstart hpoint_eq
    rw [hsub]
    simp only [Pi.sub_apply]
    rw [hfinish, hstart, hffinish, hfstart, hpoint_eq]
    simpa using
      scoreTranslation_pointwise_increment_of_absolute_continuity f derivative
        absolute_continuity derivative_ae_eq x start finish 1
  calc
    scoreTranslateL1 finish (hf.toL1 f) =
        (scoreTranslateL1 finish (hf.toL1 f) - scoreTranslateL1 start (hf.toL1 f)) +
          scoreTranslateL1 start (hf.toL1 f) := (sub_add_cancel _ _).symm
    _ = hpoint.toL1 (fun x => ∫ u in start..finish, -derivative (x - u)) +
          scoreTranslateL1 start (hf.toL1 f) := by rw [hdiff]
    _ = scoreTranslateL1 start (hf.toL1 f) +
          hpoint.toL1 (fun x => ∫ u in start..finish, -derivative (x - u)) := add_comm _ _
    _ = scoreTranslateL1 start (hf.toL1 f) +
          ∫ u in start..finish, -scoreTranslateL1 u (hderivative.toL1 derivative) := by
      rw [houter_eq]

/-- The actual `W^{1,1}` derivative theorem for score-space translations. -/
theorem scoreTranslateL1_hasDerivAt_of_global_W11
    (f derivative : ℝ → ℝ)
    (hf : Integrable f volume) (hderivative : Integrable derivative volume)
    (absolute_continuity : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (derivative_ae_eq : derivative =ᵐ[volume] deriv f)
    (theta coefficient : ℝ) :
    HasDerivAt
      (fun t : ℝ => scoreTranslateL1 (t * coefficient) (hf.toL1 f))
      ((-coefficient) • scoreTranslateL1 (theta * coefficient) (hderivative.toL1 derivative))
      theta := by
  have hbase (s : ℝ) :
      HasDerivAt (fun t : ℝ => scoreTranslateL1 t (hf.toL1 f))
        (-scoreTranslateL1 s (hderivative.toL1 derivative)) s := by
    simpa only [mul_one, neg_one_smul] using
      scoreTranslateL1_hasDerivAt_of_fundamental_identity
        (hf.toL1 f) (hderivative.toL1 derivative) s 1 (fun t => by
          simpa only [mul_one, neg_one_smul] using
            scoreTranslateL1_base_fundamental_identity f derivative hf hderivative
              absolute_continuity derivative_ae_eq s t)
  have hinner : HasDerivAt (fun t : ℝ => t * coefficient) coefficient theta :=
    hasDerivAt_mul_const coefficient
  simpa only [Function.comp_apply, smul_neg, neg_smul] using
    (hbase (theta * coefficient)).scomp theta hinner

end KR21Monoculture

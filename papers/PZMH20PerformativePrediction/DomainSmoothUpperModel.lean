import AppliedModelingLib.Foundations.Optimization.SmoothStrongConvex

/-!
# Smooth upper models from feasible-direction derivatives

The constrained descent lemma below is the within-derivative counterpart of
`AppliedModelingLib.smooth_upper_model_bound_on_convex`.  Its proof follows the
same one-dimensional quadratic-comparison argument, but the objective is
differentiated only along the feasible segment.  Thus it applies at boundary
points of a convex parameter domain.
-/

namespace PZMH20PerformativePrediction.DomainGradient

open Asymptotics
open scoped InnerProductSpace

variable {Parameter : Type*}
variable [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
  [CompleteSpace Parameter]

/-- A scalar objective with a Lipschitz gradient on a convex domain lies below
its quadratic smoothness model there.  Both differentiability and gradient
Lipschitzness are required only on the domain. -/
theorem smooth_upper_model_bound_within_on_convex
    (f : Parameter → ℝ) (gradient : Parameter → Parameter) (smoothness : ℝ)
    (domain : Set Parameter) (hconvex : Convex ℝ domain)
    (hgradient : ∀ first ∈ domain, ∀ second ∈ domain,
      ‖gradient first - gradient second‖ ≤ smoothness * ‖first - second‖)
    (hgradientWithin : ∀ parameter ∈ domain,
      HasGradientWithinAt f (gradient parameter) domain parameter)
    (first second : Parameter) (hfirst : first ∈ domain) (hsecond : second ∈ domain) :
    f second ≤ f first + ⟪gradient first, second - first⟫_ℝ +
      smoothness / 2 * ‖second - first‖ ^ 2 := by
  let line : ℝ → Parameter := AffineMap.lineMap first second
  have hlineMem : Set.MapsTo line (Set.Icc (0 : ℝ) 1) domain := by
    exact hconvex.mapsTo_lineMap hfirst hsecond
  have hline : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt (f ∘ line) ⟪gradient (line t), second - first⟫_ℝ
        (Set.Icc (0 : ℝ) 1) t := by
    intro t ht
    simpa [line, InnerProductSpace.toDual_apply_apply] using
      (hgradientWithin (line t) (hlineMem ht)).hasFDerivWithinAt.comp_hasDerivWithinAt t
        AffineMap.hasDerivWithinAt_lineMap hlineMem
  let displacement := second - first
  let q : ℝ → ℝ := fun t ↦
    f (line t) - t * ⟪gradient first, displacement⟫_ℝ -
      (smoothness / 2) * t ^ 2 * ‖displacement‖ ^ 2
  have hq : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt q
        (⟪gradient (line t), displacement⟫_ℝ - ⟪gradient first, displacement⟫_ℝ -
          smoothness * t * ‖displacement‖ ^ 2) (Set.Icc (0 : ℝ) 1) t := by
    intro t ht
    have hlinear : HasDerivWithinAt
        (fun t : ℝ ↦ t * ⟪gradient first, displacement⟫_ℝ)
        ⟪gradient first, displacement⟫_ℝ (Set.Icc (0 : ℝ) 1) t := by
      simpa using
        ((hasDerivAt_id t).mul_const ⟪gradient first, displacement⟫_ℝ).hasDerivWithinAt
    have hquadratic : HasDerivWithinAt
        (fun t : ℝ ↦ (smoothness / 2) * t ^ 2 * ‖displacement‖ ^ 2)
        (smoothness * t * ‖displacement‖ ^ 2) (Set.Icc (0 : ℝ) 1) t := by
      have hpow : HasDerivWithinAt
          (fun t : ℝ ↦ (smoothness / 2) * ‖displacement‖ ^ 2 * t ^ 2)
          ((smoothness / 2) * ‖displacement‖ ^ 2 * (2 * t))
          (Set.Icc (0 : ℝ) 1) t := by
        simpa using (((hasDerivAt_id t).pow 2).const_mul
          ((smoothness / 2) * ‖displacement‖ ^ 2)).hasDerivWithinAt
      convert hpow using 1
      · ext y
        change smoothness / 2 * y ^ 2 * ‖displacement‖ ^ 2 =
          smoothness / 2 * ‖displacement‖ ^ 2 * y ^ 2
        ring
      · ring
    simpa only [q, Function.comp_apply, displacement] using
      ((hline t ht).sub hlinear).sub hquadratic
  have hline_sub : ∀ t : ℝ, line t - first = t • displacement := by
    intro t
    simp only [line, displacement, AffineMap.lineMap_apply_module']
    abel
  have hq_deriv_nonpos : ∀ t ∈ interior (Set.Icc (0 : ℝ) 1),
      ⟪gradient (line t), displacement⟫_ℝ - ⟪gradient first, displacement⟫_ℝ -
        smoothness * t * ‖displacement‖ ^ 2 ≤ 0 := by
    intro t ht
    rw [interior_Icc] at ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    have ht_nonneg : 0 ≤ t := ht.1.le
    have hgradient_norm :
        ‖gradient (line t) - gradient first‖ ≤
          smoothness * (t * ‖displacement‖) := by
      calc
        ‖gradient (line t) - gradient first‖ ≤
            smoothness * ‖line t - first‖ :=
          hgradient (line t) (hlineMem htIcc) first hfirst
        _ = smoothness * (t * ‖displacement‖) := by
          rw [hline_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht_nonneg]
    have hinner :
        ⟪gradient (line t) - gradient first, displacement⟫_ℝ ≤
          smoothness * t * ‖displacement‖ ^ 2 := by
      calc
        ⟪gradient (line t) - gradient first, displacement⟫_ℝ ≤
            ‖gradient (line t) - gradient first‖ * ‖displacement‖ :=
          real_inner_le_norm _ _
        _ ≤ (smoothness * (t * ‖displacement‖)) * ‖displacement‖ := by
          exact mul_le_mul_of_nonneg_right hgradient_norm (norm_nonneg _)
        _ = smoothness * t * ‖displacement‖ ^ 2 := by ring
    rw [← inner_sub_left]
    linarith
  have hq_antitone : AntitoneOn q (Set.Icc (0 : ℝ) 1) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (0 : ℝ) 1)
      (fun t ht ↦ (hq t ht).continuousWithinAt)
      (fun t ht ↦ (hq t (interior_subset ht)).mono interior_subset) hq_deriv_nonpos
  have hq01 := hq_antitone
    (show (0 : ℝ) ∈ Set.Icc 0 1 from ⟨le_rfl, zero_le_one⟩)
    (show (1 : ℝ) ∈ Set.Icc 0 1 from ⟨zero_le_one, le_rfl⟩) zero_le_one
  simp only [q, line, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one,
    one_mul, zero_mul, one_pow, sub_zero] at hq01
  linarith

omit [CompleteSpace Parameter] in
/-- A nonnegative quadratic first-order remainder identifies the displayed
Fréchet derivative relative to the feasible domain.  This is useful when the
remainder bounds are obtained after integration, without differentiating the
integral itself. -/
theorem hasFDerivWithinAt_of_nonneg_quadratic_remainder
    (f : Parameter → ℝ) (gradient : Parameter) (domain : Set Parameter)
    (base : Parameter) {smoothness : ℝ} (hsmoothness : 0 ≤ smoothness)
    (hremainder : ∀ candidate ∈ domain,
      0 ≤ f candidate - f base - ⟪gradient, candidate - base⟫_ℝ ∧
      f candidate - f base - ⟪gradient, candidate - base⟫_ℝ ≤
        smoothness / 2 * ‖candidate - base‖ ^ 2) :
    HasFDerivWithinAt f (innerSL ℝ gradient) domain base := by
  apply HasFDerivWithinAt.of_isLittleO
  refine (isBigO_iff.2 ⟨smoothness / 2, ?_⟩).trans_isLittleO
    ((isLittleO_pow_sub_sub base (m := 2) (by norm_num)).mono nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with candidate hcandidate
  have hbounds := hremainder candidate hcandidate
  have hcurvature : 0 ≤ smoothness / 2 := by positivity
  have hlower :
      -(smoothness / 2 * ‖candidate - base‖ ^ 2) ≤
        f candidate - f base - ⟪gradient, candidate - base⟫_ℝ := by
    exact le_trans (neg_nonpos.mpr (mul_nonneg hcurvature (sq_nonneg _))) hbounds.1
  have habs :
      |f candidate - f base - ⟪gradient, candidate - base⟫_ℝ| ≤
        smoothness / 2 * ‖candidate - base‖ ^ 2 :=
    abs_le.2 ⟨hlower, hbounds.2⟩
  simpa only [innerSL_apply_apply, Real.norm_eq_abs, norm_norm,
    abs_of_nonneg (sq_nonneg ‖candidate - base‖)] using habs

end PZMH20PerformativePrediction.DomainGradient

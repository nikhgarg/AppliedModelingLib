import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Convex.Strong

/-!
# Smooth and Strongly Convex Calculus

Reusable first-order inequalities for real Hilbert spaces.  The development
starts from explicit gradients, so downstream optimization libraries do not
need to depend on a particular differentiable-convex-function API.
-/

namespace AppliedModelingLib

open scoped InnerProductSpace

section

variable {Parameter : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
  [CompleteSpace Parameter]

/-- A differentiable scalar function lies below its quadratic smoothness model. -/
theorem smooth_upper_model_bound
    (f : Parameter → ℝ) (gradient : Parameter → Parameter) (smoothness : ℝ)
    (hgradient : ∀ first second,
      ‖gradient first - gradient second‖ ≤ smoothness * ‖first - second‖)
    (hgradientAt : ∀ parameter, HasGradientAt f (gradient parameter) parameter)
    (first second : Parameter) :
    f second ≤ f first + ⟪gradient first, second - first⟫_ℝ +
      smoothness / 2 * ‖second - first‖ ^ 2 := by
  let line : ℝ → Parameter := AffineMap.lineMap first second
  have hline : ∀ t : ℝ,
      HasDerivAt (f ∘ line) ⟪gradient (line t), second - first⟫_ℝ t := by
    intro t
    simpa [line, InnerProductSpace.toDual_apply_apply] using
      HasFDerivAt.comp_hasDerivAt t (hgradientAt (line t)).hasFDerivAt
        (AffineMap.hasDerivAt_lineMap (a := first) (b := second) (x := t))
  let displacement := second - first
  let q : ℝ → ℝ := fun t =>
    f (line t) - t * ⟪gradient first, displacement⟫_ℝ -
      (smoothness / 2) * t ^ 2 * ‖displacement‖ ^ 2
  have hq : ∀ t : ℝ,
      HasDerivAt q
        (⟪gradient (line t), displacement⟫_ℝ - ⟪gradient first, displacement⟫_ℝ -
          smoothness * t * ‖displacement‖ ^ 2) t := by
    intro t
    have hlinear : HasDerivAt (fun t : ℝ => t * ⟪gradient first, displacement⟫_ℝ)
        ⟪gradient first, displacement⟫_ℝ t := by
      simpa using (hasDerivAt_id t).mul_const ⟪gradient first, displacement⟫_ℝ
    have hquadratic : HasDerivAt
        (fun t : ℝ => (smoothness / 2) * t ^ 2 * ‖displacement‖ ^ 2)
        (smoothness * t * ‖displacement‖ ^ 2) t := by
      have hpow := ((hasDerivAt_id t).pow 2).const_mul
        ((smoothness / 2) * ‖displacement‖ ^ 2)
      simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] at hpow
      convert hpow using 1
      · ext y
        change smoothness / 2 * y ^ 2 * ‖displacement‖ ^ 2 =
          smoothness / 2 * ‖displacement‖ ^ 2 * y ^ 2
        ring
      · ring
    simpa only [q, Function.comp_apply, displacement] using ((hline t).sub hlinear).sub hquadratic
  have hline_sub : ∀ t : ℝ, line t - first = t • displacement := by
    intro t
    simp only [line, displacement, AffineMap.lineMap_apply_module']
    abel
  have hq_deriv_nonpos : ∀ t ∈ interior (Set.Icc (0 : ℝ) 1),
      ⟪gradient (line t), displacement⟫_ℝ - ⟪gradient first, displacement⟫_ℝ -
        smoothness * t * ‖displacement‖ ^ 2 ≤ 0 := by
    intro t ht
    rw [interior_Icc] at ht
    have ht_nonneg : 0 ≤ t := ht.1.le
    have hgradient_norm :
        ‖gradient (line t) - gradient first‖ ≤ smoothness * (t * ‖displacement‖) := by
      calc
        ‖gradient (line t) - gradient first‖ ≤ smoothness * ‖line t - first‖ :=
          hgradient (line t) first
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
      (fun t _ => (hq t).continuousAt.continuousWithinAt)
      (fun t _ => (hq t).hasDerivWithinAt) hq_deriv_nonpos
  have hq01 := hq_antitone (show (0 : ℝ) ∈ Set.Icc 0 1 from ⟨le_rfl, zero_le_one⟩)
    (show (1 : ℝ) ∈ Set.Icc 0 1 from ⟨zero_le_one, le_rfl⟩) zero_le_one
  simp only [q, line, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one,
    one_mul, zero_mul, one_pow, sub_zero] at hq01
  linarith

/-- A differentiable scalar objective lies below its quadratic smoothness
model when the gradient hypotheses hold only on a convex feasible region.
This is the constrained descent lemma: the proof uses derivatives only along
the segment from `first` to `second`, which stays feasible by convexity. -/
theorem smooth_upper_model_bound_on_convex
    (f : Parameter → ℝ) (gradient : Parameter → Parameter) (smoothness : ℝ)
    (feasible : Set Parameter) (hfeasible : Convex ℝ feasible)
    (hgradient : ∀ first ∈ feasible, ∀ second ∈ feasible,
      ‖gradient first - gradient second‖ ≤ smoothness * ‖first - second‖)
    (hgradientAt : ∀ parameter ∈ feasible, HasGradientAt f (gradient parameter) parameter)
    (first second : Parameter) (hfirst : first ∈ feasible) (hsecond : second ∈ feasible) :
    f second ≤ f first + ⟪gradient first, second - first⟫_ℝ +
      smoothness / 2 * ‖second - first‖ ^ 2 := by
  let line : ℝ → Parameter := AffineMap.lineMap first second
  have hlineMem : ∀ t ∈ Set.Icc (0 : ℝ) 1, line t ∈ feasible := by
    intro t ht
    exact hfeasible.lineMap_mem hfirst hsecond ht
  have hline : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (f ∘ line) ⟪gradient (line t), second - first⟫_ℝ t := by
    intro t ht
    simpa [line, InnerProductSpace.toDual_apply_apply] using
      HasFDerivAt.comp_hasDerivAt t (hgradientAt (line t) (hlineMem t ht)).hasFDerivAt
        (AffineMap.hasDerivAt_lineMap (a := first) (b := second) (x := t))
  let displacement := second - first
  let q : ℝ → ℝ := fun t =>
    f (line t) - t * ⟪gradient first, displacement⟫_ℝ -
      (smoothness / 2) * t ^ 2 * ‖displacement‖ ^ 2
  have hq : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt q
        (⟪gradient (line t), displacement⟫_ℝ - ⟪gradient first, displacement⟫_ℝ -
          smoothness * t * ‖displacement‖ ^ 2) t := by
    intro t ht
    have hlinear : HasDerivAt (fun t : ℝ => t * ⟪gradient first, displacement⟫_ℝ)
        ⟪gradient first, displacement⟫_ℝ t := by
      simpa using (hasDerivAt_id t).mul_const ⟪gradient first, displacement⟫_ℝ
    have hquadratic : HasDerivAt
        (fun t : ℝ => (smoothness / 2) * t ^ 2 * ‖displacement‖ ^ 2)
        (smoothness * t * ‖displacement‖ ^ 2) t := by
      have hpow := ((hasDerivAt_id t).pow 2).const_mul
        ((smoothness / 2) * ‖displacement‖ ^ 2)
      simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] at hpow
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
        ‖gradient (line t) - gradient first‖ ≤ smoothness * (t * ‖displacement‖) := by
      calc
        ‖gradient (line t) - gradient first‖ ≤ smoothness * ‖line t - first‖ :=
          hgradient (line t) (hlineMem t htIcc) first hfirst
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
      (fun t ht => (hq t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hq t (interior_subset ht)).hasDerivWithinAt) hq_deriv_nonpos
  have hq01 := hq_antitone (show (0 : ℝ) ∈ Set.Icc 0 1 from ⟨le_rfl, zero_le_one⟩)
    (show (1 : ℝ) ∈ Set.Icc 0 1 from ⟨zero_le_one, le_rfl⟩) zero_le_one
  simp only [q, line, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one,
    one_mul, zero_mul, one_pow, sub_zero] at hq01
  linarith

/-- A differentiable objective has a strong-convex quadratic lower model on
a convex feasible region when its gradient is strongly monotone there.  Like
the constrained smoothness lemma, this uses calculus only along the feasible
line segment and therefore applies to boundary minimizers. -/
theorem strong_lower_model_bound_on_convex_of_gradient_strongMonotone
    (f : Parameter → ℝ) (gradient : Parameter → Parameter) (modulus : ℝ)
    (feasible : Set Parameter) (hfeasible : Convex ℝ feasible)
    (hstrong : ∀ first ∈ feasible, ∀ second ∈ feasible,
      modulus * ‖first - second‖ ^ 2 ≤
        ⟪gradient first - gradient second, first - second⟫_ℝ)
    (hgradientAt : ∀ parameter ∈ feasible, HasGradientAt f (gradient parameter) parameter)
    (first second : Parameter) (hfirst : first ∈ feasible) (hsecond : second ∈ feasible) :
    f second ≥ f first + ⟪gradient first, second - first⟫_ℝ +
      modulus / 2 * ‖second - first‖ ^ 2 := by
  let line : ℝ → Parameter := AffineMap.lineMap first second
  have hlineMem : ∀ t ∈ Set.Icc (0 : ℝ) 1, line t ∈ feasible := by
    intro t ht
    exact hfeasible.lineMap_mem hfirst hsecond ht
  have hline : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (f ∘ line) ⟪gradient (line t), second - first⟫_ℝ t := by
    intro t ht
    simpa [line, InnerProductSpace.toDual_apply_apply] using
      HasFDerivAt.comp_hasDerivAt t (hgradientAt (line t) (hlineMem t ht)).hasFDerivAt
        (AffineMap.hasDerivAt_lineMap (a := first) (b := second) (x := t))
  let displacement := second - first
  let q : ℝ → ℝ := fun t =>
    f (line t) - t * ⟪gradient first, displacement⟫_ℝ -
      (modulus / 2) * t ^ 2 * ‖displacement‖ ^ 2
  have hq : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt q
        (⟪gradient (line t), displacement⟫_ℝ - ⟪gradient first, displacement⟫_ℝ -
          modulus * t * ‖displacement‖ ^ 2) t := by
    intro t ht
    have hlinear : HasDerivAt (fun t : ℝ => t * ⟪gradient first, displacement⟫_ℝ)
        ⟪gradient first, displacement⟫_ℝ t := by
      simpa using (hasDerivAt_id t).mul_const ⟪gradient first, displacement⟫_ℝ
    have hquadratic : HasDerivAt
        (fun t : ℝ => (modulus / 2) * t ^ 2 * ‖displacement‖ ^ 2)
        (modulus * t * ‖displacement‖ ^ 2) t := by
      have hpow := ((hasDerivAt_id t).pow 2).const_mul
        ((modulus / 2) * ‖displacement‖ ^ 2)
      simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] at hpow
      convert hpow using 1
      · ext direction
        change modulus / 2 * direction ^ 2 * ‖displacement‖ ^ 2 =
          modulus / 2 * ‖displacement‖ ^ 2 * direction ^ 2
        ring
      · ring
    simpa only [q, Function.comp_apply, displacement] using
      ((hline t ht).sub hlinear).sub hquadratic
  have hline_sub : ∀ t : ℝ, line t - first = t • displacement := by
    intro t
    simp only [line, displacement, AffineMap.lineMap_apply_module']
    abel
  have hq_deriv_nonneg : ∀ t ∈ interior (Set.Icc (0 : ℝ) 1),
      0 ≤ ⟪gradient (line t), displacement⟫_ℝ - ⟪gradient first, displacement⟫_ℝ -
        modulus * t * ‖displacement‖ ^ 2 := by
    intro t ht
    rw [interior_Icc] at ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    have htPos : 0 < t := ht.1
    have hmonotone := hstrong (line t) (hlineMem t htIcc) first hfirst
    have hlineNorm : ‖line t - first‖ = t * ‖displacement‖ := by
      rw [hline_sub, norm_smul, Real.norm_eq_abs, abs_of_pos htPos]
    have hlineInner :
        ⟪gradient (line t) - gradient first, line t - first⟫_ℝ =
          t * ⟪gradient (line t) - gradient first, displacement⟫_ℝ := by
      rw [hline_sub, inner_smul_right]
    rw [hlineNorm, hlineInner] at hmonotone
    have hscaled :
        t * (modulus * t * ‖displacement‖ ^ 2) ≤
          t * ⟪gradient (line t) - gradient first, displacement⟫_ℝ := by
      nlinarith [hmonotone]
    have hpairing : modulus * t * ‖displacement‖ ^ 2 ≤
        ⟪gradient (line t) - gradient first, displacement⟫_ℝ :=
      le_of_mul_le_mul_left hscaled htPos
    rw [← inner_sub_left]
    linarith
  have hqMonotone : MonotoneOn q (Set.Icc (0 : ℝ) 1) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : ℝ) 1)
      (fun t ht => (hq t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hq t (interior_subset ht)).hasDerivWithinAt) hq_deriv_nonneg
  have hq01 := hqMonotone (show (0 : ℝ) ∈ Set.Icc 0 1 from ⟨le_rfl, zero_le_one⟩)
    (show (1 : ℝ) ∈ Set.Icc 0 1 from ⟨zero_le_one, le_rfl⟩) zero_le_one
  simp only [q, line, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one,
    one_mul, zero_mul, one_pow, sub_zero] at hq01
  linarith

/--
A first-order convex function with a quadratic upper model has a cocoercive
gradient.  Stating the result through the upper model makes it applicable to
the shifted function in smooth--strongly-convex interpolation proofs.
-/
theorem gradient_cocoercive_of_upperModel_firstOrder
    (f : Parameter → ℝ) (gradient : Parameter → Parameter) (smoothness : ℝ)
    (hsmooth : 0 < smoothness)
    (hupperModel : ∀ center candidate,
      f candidate ≤ f center + ⟪gradient center, candidate - center⟫_ℝ +
        smoothness / 2 * ‖candidate - center‖ ^ 2)
    (hconvex : ∀ center candidate,
      f candidate ≥ f center + ⟪gradient center, candidate - center⟫_ℝ)
    (first second : Parameter) :
    (1 / smoothness) * ‖gradient first - gradient second‖ ^ 2 ≤
      ⟪gradient first - gradient second, first - second⟫_ℝ := by
  have hsmooth_ne : smoothness ≠ 0 := hsmooth.ne'
  have hhalf : smoothness / 2 * (1 / smoothness) ^ 2 = 1 / (2 * smoothness) := by
    field_simp
  have hstep : ∀ (center base : Parameter),
      f center - f base - ⟪gradient base, center - base⟫_ℝ ≥
        (1 / (2 * smoothness)) * ‖gradient center - gradient base‖ ^ 2 := by
    intro center base
    let difference := gradient center - gradient base
    let trial := center - (1 / smoothness) • difference
    have hupper := hupperModel center trial
    have hlower := hconvex base trial
    have htrial_center : trial - center = (-(1 / smoothness)) • difference := by
      simp [trial]
    have htrial_base : trial - base = (center - base) - (1 / smoothness) • difference := by
      simp only [trial]
      abel
    have hnorm : ‖(-(1 / smoothness)) • difference‖ ^ 2 =
        (1 / smoothness) ^ 2 * ‖difference‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_neg,
        abs_of_nonneg (by positivity : 0 ≤ 1 / smoothness)]
      ring
    have hinnerCenter :
        ⟪gradient center, (-(1 / smoothness)) • difference⟫_ℝ =
          -(1 / smoothness) * ⟪gradient center, difference⟫_ℝ := by
      rw [inner_smul_right]
    have hinnerBase :
        ⟪gradient base, (center - base) - (1 / smoothness) • difference⟫_ℝ =
          ⟪gradient base, center - base⟫_ℝ -
            (1 / smoothness) * ⟪gradient base, difference⟫_ℝ := by
      rw [inner_sub_right, inner_smul_right]
    rw [htrial_center, hnorm, hinnerCenter] at hupper
    rw [htrial_base, hinnerBase] at hlower
    have hdifference : ⟪gradient center, difference⟫_ℝ -
        ⟪gradient base, difference⟫_ℝ = ‖difference‖ ^ 2 := by
      rw [← inner_sub_left]
      simpa only [difference] using
        real_inner_self_eq_norm_sq (gradient center - gradient base)
    simp only [difference] at hupper hlower hdifference ⊢
    have hquadratic : smoothness / 2 *
        ((1 / smoothness) ^ 2 * ‖gradient center - gradient base‖ ^ 2) =
          (1 / (2 * smoothness)) * ‖gradient center - gradient base‖ ^ 2 := by
      rw [← mul_assoc, hhalf]
    rw [hquadratic] at hupper
    have hinvhalf : 1 / smoothness = 2 * (1 / (2 * smoothness)) := by
      field_simp
    rw [hinvhalf] at hupper hlower
    have hscaled :
        2 * (1 / (2 * smoothness)) * ⟪gradient center,
            gradient center - gradient base⟫_ℝ -
          2 * (1 / (2 * smoothness)) * ⟪gradient base,
            gradient center - gradient base⟫_ℝ =
          2 * (1 / (2 * smoothness)) * ‖gradient center - gradient base‖ ^ 2 := by
      calc
        2 * (1 / (2 * smoothness)) * ⟪gradient center,
            gradient center - gradient base⟫_ℝ -
          2 * (1 / (2 * smoothness)) * ⟪gradient base,
            gradient center - gradient base⟫_ℝ =
            2 * (1 / (2 * smoothness)) *
              (⟪gradient center, gradient center - gradient base⟫_ℝ -
                ⟪gradient base, gradient center - gradient base⟫_ℝ) := by ring
        _ = 2 * (1 / (2 * smoothness)) * ‖gradient center - gradient base‖ ^ 2 := by
          rw [hdifference]
    nlinarith [hscaled]
  have hforward := hstep first second
  have hbackward := hstep second first
  rw [norm_sub_rev] at hbackward
  calc
    (1 / smoothness) * ‖gradient first - gradient second‖ ^ 2 =
        (1 / (2 * smoothness)) * ‖gradient first - gradient second‖ ^ 2 +
          (1 / (2 * smoothness)) * ‖gradient first - gradient second‖ ^ 2 := by ring
    _ ≤ (f first - f second - ⟪gradient second, first - second⟫_ℝ) +
          (f second - f first - ⟪gradient first, second - first⟫_ℝ) := by
      linarith
    _ = ⟪gradient first - gradient second, first - second⟫_ℝ := by
      rw [show second - first = -(first - second) by abel, inner_neg_right,
        inner_sub_left]
      ring

/--
For a differentiable convex function with a Lipschitz gradient, the gradient
is cocoercive.  This is the smooth-convex core used in standard
smooth--strongly-convex interpolation arguments.
-/
theorem gradient_cocoercive_of_smooth_firstOrder
    (f : Parameter → ℝ) (gradient : Parameter → Parameter) (smoothness : ℝ)
    (hsmooth : 0 < smoothness)
    (hgradient : ∀ first second,
      ‖gradient first - gradient second‖ ≤ smoothness * ‖first - second‖)
    (hgradientAt : ∀ parameter, HasGradientAt f (gradient parameter) parameter)
    (hconvex : ∀ center candidate,
      f candidate ≥ f center + ⟪gradient center, candidate - center⟫_ℝ)
    (first second : Parameter) :
    (1 / smoothness) * ‖gradient first - gradient second‖ ^ 2 ≤
      ⟪gradient first - gradient second, first - second⟫_ℝ :=
  gradient_cocoercive_of_upperModel_firstOrder f gradient smoothness hsmooth
    (fun center candidate => smooth_upper_model_bound f gradient smoothness hgradient hgradientAt
      center candidate)
    hconvex first second

/--
The smooth--strongly-convex interpolation inequality.  This is the real
Hilbert-space form of the inequality commonly attributed to Bubeck, Lemma
3.11: it follows by applying smooth-convex cocoercivity to the loss after
subtracting its strong-convexity quadratic.

The strict `modulus < smoothness` branch is separated because the shifted
upper-model constant is then positive.
-/
theorem smooth_strong_interpolation_of_firstOrder
    (f : Parameter → ℝ) (gradient : Parameter → Parameter)
    (smoothness modulus : ℝ) (hmodulus : 0 < modulus)
    (hmodulus_lt : modulus < smoothness)
    (hgradient : ∀ first second,
      ‖gradient first - gradient second‖ ≤ smoothness * ‖first - second‖)
    (hgradientAt : ∀ parameter, HasGradientAt f (gradient parameter) parameter)
    (hstrong : ∀ center candidate,
      f candidate ≥ f center + ⟪gradient center, candidate - center⟫_ℝ +
        modulus / 2 * ‖candidate - center‖ ^ 2)
    (first second : Parameter) :
    (modulus * smoothness / (modulus + smoothness)) * ‖first - second‖ ^ 2 +
        (1 / (modulus + smoothness)) * ‖gradient first - gradient second‖ ^ 2 ≤
      ⟪gradient first - gradient second, first - second⟫_ℝ := by
  let shiftedRisk : Parameter → ℝ := fun parameter =>
    f parameter - modulus / 2 * ‖parameter‖ ^ 2
  let shiftedGradient : Parameter → Parameter := fun parameter =>
    gradient parameter - modulus • parameter
  have hsmooth : 0 < smoothness := lt_trans hmodulus hmodulus_lt
  have hupper : ∀ center candidate,
      f candidate ≤ f center + ⟪gradient center, candidate - center⟫_ℝ +
        smoothness / 2 * ‖candidate - center‖ ^ 2 := fun center candidate =>
    smooth_upper_model_bound f gradient smoothness hgradient hgradientAt center candidate
  have hshiftUpper : ∀ center candidate,
      shiftedRisk candidate ≤ shiftedRisk center +
        ⟪shiftedGradient center, candidate - center⟫_ℝ +
          (smoothness - modulus) / 2 * ‖candidate - center‖ ^ 2 := by
    intro center candidate
    have hnorm : ‖candidate‖ ^ 2 = ‖center‖ ^ 2 +
        2 * ⟪center, candidate - center⟫_ℝ + ‖candidate - center‖ ^ 2 := by
      calc
        ‖candidate‖ ^ 2 = ‖center + (candidate - center)‖ ^ 2 := by
          congr 1
          abel_nf
        _ = ‖center‖ ^ 2 + 2 * ⟪center, candidate - center⟫_ℝ +
            ‖candidate - center‖ ^ 2 := by rw [norm_add_sq_real]
    dsimp [shiftedRisk, shiftedGradient]
    rw [hnorm, inner_sub_left, real_inner_smul_left]
    nlinarith [hupper center candidate]
  have hshiftConvex : ∀ center candidate,
      shiftedRisk candidate ≥ shiftedRisk center +
        ⟪shiftedGradient center, candidate - center⟫_ℝ := by
    intro center candidate
    have hnorm : ‖candidate‖ ^ 2 = ‖center‖ ^ 2 +
        2 * ⟪center, candidate - center⟫_ℝ + ‖candidate - center‖ ^ 2 := by
      calc
        ‖candidate‖ ^ 2 = ‖center + (candidate - center)‖ ^ 2 := by
          congr 1
          abel_nf
        _ = ‖center‖ ^ 2 + 2 * ⟪center, candidate - center⟫_ℝ +
            ‖candidate - center‖ ^ 2 := by rw [norm_add_sq_real]
    dsimp [shiftedRisk, shiftedGradient]
    rw [hnorm, inner_sub_left, real_inner_smul_left]
    nlinarith [hstrong center candidate]
  have hshiftCoco := gradient_cocoercive_of_upperModel_firstOrder
    shiftedRisk shiftedGradient (smoothness - modulus) (sub_pos.mpr hmodulus_lt)
    hshiftUpper hshiftConvex first second
  let parameterDifference := first - second
  let gradientDifference := gradient first - gradient second
  have hshiftDifference : shiftedGradient first - shiftedGradient second =
      gradientDifference - modulus • parameterDifference := by
    simp only [shiftedGradient, parameterDifference, gradientDifference, smul_sub]
    abel
  rw [hshiftDifference] at hshiftCoco
  change (1 / (smoothness - modulus)) *
      ‖gradientDifference - modulus • parameterDifference‖ ^ 2 ≤
        ⟪gradientDifference - modulus • parameterDifference, parameterDifference⟫_ℝ at hshiftCoco
  have hshiftCocoMul :
      ‖gradientDifference - modulus • parameterDifference‖ ^ 2 ≤
        (smoothness - modulus) *
          ⟪gradientDifference - modulus • parameterDifference, parameterDifference⟫_ℝ := by
    calc
      ‖gradientDifference - modulus • parameterDifference‖ ^ 2 =
          (smoothness - modulus) *
            ((1 / (smoothness - modulus)) *
              ‖gradientDifference - modulus • parameterDifference‖ ^ 2) := by
        have hproduct : (smoothness - modulus) * (1 / (smoothness - modulus)) = 1 := by
          rw [one_div]
          exact mul_inv_cancel₀ (ne_of_gt (sub_pos.mpr hmodulus_lt))
        rw [← mul_assoc, hproduct, one_mul]
      _ ≤ (smoothness - modulus) *
          ⟪gradientDifference - modulus • parameterDifference, parameterDifference⟫_ℝ := by
        exact mul_le_mul_of_nonneg_left hshiftCoco (sub_nonneg.mpr hmodulus_lt.le)
  have hshiftExpanded :
      ‖gradientDifference‖ ^ 2 - 2 * modulus *
          ⟪gradientDifference, parameterDifference⟫_ℝ +
        modulus ^ 2 * ‖parameterDifference‖ ^ 2 ≤
        (smoothness - modulus) *
          (⟪gradientDifference, parameterDifference⟫_ℝ -
            modulus * ‖parameterDifference‖ ^ 2) := by
    rw [norm_sub_sq_real] at hshiftCocoMul
    simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hmodulus,
      inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at hshiftCocoMul
    nlinarith [hshiftCocoMul]
  have hsum_pos : 0 < modulus + smoothness := by positivity
  have hmain : modulus * smoothness * ‖parameterDifference‖ ^ 2 +
      ‖gradientDifference‖ ^ 2 ≤
        (modulus + smoothness) *
          ⟪gradientDifference, parameterDifference⟫_ℝ := by
    nlinarith [hshiftExpanded]
  calc
    (modulus * smoothness / (modulus + smoothness)) * ‖first - second‖ ^ 2 +
        (1 / (modulus + smoothness)) * ‖gradient first - gradient second‖ ^ 2 =
        (modulus * smoothness * ‖parameterDifference‖ ^ 2 +
          ‖gradientDifference‖ ^ 2) / (modulus + smoothness) := by
      simp only [parameterDifference, gradientDifference]
      field_simp
    _ ≤ ⟪gradientDifference, parameterDifference⟫_ℝ :=
      (div_le_iff₀ hsum_pos).2 (by simpa [mul_comm] using hmain)
    _ = ⟪gradient first - gradient second, first - second⟫_ℝ := by
      simp only [parameterDifference, gradientDifference]

/--
The `modulus = smoothness` boundary of smooth--strongly-convex interpolation.
In this case strong monotonicity and gradient Lipschitzness squeeze the
gradient pairing tightly enough to give the Bubeck inequality directly.
-/
theorem smooth_strong_interpolation_eq_of_firstOrder
    (f : Parameter → ℝ) (gradient : Parameter → Parameter) (smoothness : ℝ)
    (hsmooth : 0 < smoothness)
    (hgradient : ∀ first second,
      ‖gradient first - gradient second‖ ≤ smoothness * ‖first - second‖)
    (hstrong : ∀ center candidate,
      f candidate ≥ f center + ⟪gradient center, candidate - center⟫_ℝ +
        smoothness / 2 * ‖candidate - center‖ ^ 2)
    (first second : Parameter) :
    (smoothness / 2) * ‖first - second‖ ^ 2 +
        (1 / (2 * smoothness)) * ‖gradient first - gradient second‖ ^ 2 ≤
      ⟪gradient first - gradient second, first - second⟫_ℝ := by
  let parameterDifference := first - second
  let gradientDifference := gradient first - gradient second
  have hfirst := hstrong first second
  have hsecond := hstrong second first
  rw [show second - first = -parameterDifference by simp [parameterDifference],
    inner_neg_right] at hfirst
  dsimp only [parameterDifference] at hfirst hsecond
  simp only [norm_neg] at hfirst
  have hmonotone : smoothness * ‖parameterDifference‖ ^ 2 ≤
      ⟪gradientDifference, parameterDifference⟫_ℝ := by
    dsimp only [parameterDifference, gradientDifference]
    rw [inner_sub_left]
    nlinarith [hfirst, hsecond]
  have hgradientNorm := hgradient first second
  have hgradientNorm' : ‖gradientDifference‖ ≤ smoothness * ‖parameterDifference‖ := by
    simpa [gradientDifference, parameterDifference] using hgradientNorm
  have hboundNonneg : 0 ≤ smoothness * ‖parameterDifference‖ := by positivity
  have hgradientSq : ‖gradientDifference‖ ^ 2 ≤
      (smoothness * ‖parameterDifference‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hboundNonneg).mpr hgradientNorm'
  have hgradientTerm : (1 / (2 * smoothness)) * ‖gradientDifference‖ ^ 2 ≤
      (smoothness / 2) * ‖parameterDifference‖ ^ 2 := by
    have hscaled := mul_le_mul_of_nonneg_left hgradientSq (by positivity : 0 ≤ 1 / (2 * smoothness))
    calc
      (1 / (2 * smoothness)) * ‖gradientDifference‖ ^ 2 ≤
          (1 / (2 * smoothness)) * (smoothness * ‖parameterDifference‖) ^ 2 := hscaled
      _ = (smoothness / 2) * ‖parameterDifference‖ ^ 2 := by field_simp
  change (smoothness / 2) * ‖parameterDifference‖ ^ 2 +
      (1 / (2 * smoothness)) * ‖gradientDifference‖ ^ 2 ≤
        ⟪gradientDifference, parameterDifference⟫_ℝ
  nlinarith [hmonotone, hgradientTerm]

end

section

variable {Parameter : Type*} [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]

/-- A minimizer of a strongly convex objective has the standard quadratic
growth bound, including when the minimizer lies on the boundary of its convex
domain. -/
theorem StrongConvexOn.quadratic_gap_le_of_isMinOn
    {domain : Set Parameter} {objective : Parameter → ℝ} {modulus : ℝ}
    (hstrong : StrongConvexOn domain modulus objective)
    {minimizer candidate : Parameter} (hminimizer_mem : minimizer ∈ domain)
    (hcandidate_mem : candidate ∈ domain)
    (hminimizer : ∀ parameter ∈ domain, objective minimizer ≤ objective parameter) :
    modulus / 2 * ‖candidate - minimizer‖ ^ 2 ≤
      objective candidate - objective minimizer := by
  let gap := objective candidate - objective minimizer
  let curvature := modulus / 2 * ‖candidate - minimizer‖ ^ 2
  have hgap_nonneg : 0 ≤ gap :=
    sub_nonneg.mpr (hminimizer candidate hcandidate_mem)
  by_contra hnot
  have hgap_lt : gap < curvature := lt_of_not_ge hnot
  have hcurvature_pos : 0 < curvature := lt_of_le_of_lt hgap_nonneg hgap_lt
  let b := (curvature - gap) / (2 * curvature)
  let a := 1 - b
  have hb_pos : 0 < b := by
    dsimp [b]
    exact div_pos (by linarith) (by positivity)
  have hb_le_half : b ≤ (1 : ℝ) / 2 := by
    dsimp [b]
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * curvature) (by norm_num)).2
    nlinarith
  have hb_nonneg : 0 ≤ b := hb_pos.le
  have hb_le_one : b ≤ 1 := hb_le_half.trans (by norm_num)
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    linarith
  have hab : a + b = 1 := by
    dsimp [a]
    ring
  have hcombination_mem : a • minimizer + b • candidate ∈ domain :=
    hstrong.1 hminimizer_mem hcandidate_mem ha_nonneg hb_nonneg hab
  have hcombination_min :=
    hminimizer (a • minimizer + b • candidate) hcombination_mem
  have hstrong_combination :=
    hstrong.2 hminimizer_mem hcandidate_mem ha_nonneg hb_nonneg hab
  have hweighted :
      objective (a • minimizer + b • candidate) ≤
        a * objective minimizer + b * objective candidate - a * b * curvature := by
    simpa only [smul_eq_mul, curvature, norm_sub_rev] using hstrong_combination
  have hproduct_nonneg : 0 ≤ b * (gap - a * curvature) := by
    dsimp [gap] at hgap_nonneg ⊢
    nlinarith [hcombination_min, hweighted]
  have hb_curvature : b * curvature = (curvature - gap) / 2 := by
    dsimp [b]
    field_simp
  have hfactor_neg : gap - a * curvature < 0 := by
    dsimp [a]
    calc
      gap - (1 - b) * curvature = gap - curvature + b * curvature := by ring
      _ = gap - curvature + (curvature - gap) / 2 := by rw [hb_curvature]
      _ < 0 := by linarith
  exact (not_lt_of_ge hproduct_nonneg) (mul_neg_of_pos_of_neg hb_pos hfactor_neg)

end

section

variable {Parameter : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]

/--
The variational characterization of an orthogonal projection onto a feasible
set in a real Hilbert space.  It is the projection property needed to turn a
fixed point of projected gradient descent into a constrained first-order
condition; nonexpansiveness alone is insufficient for that purpose.
-/
def IsVariationalEuclideanProjectionOn (domain : Set Parameter)
    (project : Parameter → Parameter) : Prop :=
  (∀ input, project input ∈ domain) ∧
    ∀ input candidate, candidate ∈ domain →
      ⟪input - project input, candidate - project input⟫_ℝ ≤ 0

/--
A fixed point of projected gradient descent obeys the feasible variational
first-order inequality, provided the projection has its Euclidean variational
characterization.
-/
theorem projectedGradient_fixedPoint_firstOrder
    (domain : Set Parameter) (project : Parameter → Parameter)
    (hproject : IsVariationalEuclideanProjectionOn domain project)
    (gradient parameter : Parameter) (stepSize : ℝ) (hstepSize : 0 < stepSize)
    (hfixed : project (parameter - stepSize • gradient) = parameter)
    (candidate : Parameter) (hcandidate : candidate ∈ domain) :
    0 ≤ ⟪gradient, candidate - parameter⟫_ℝ := by
  have hvariational := hproject.2 (parameter - stepSize • gradient) candidate hcandidate
  rw [hfixed] at hvariational
  rw [show parameter - stepSize • gradient - parameter = -(stepSize • gradient) by abel,
    inner_neg_left, real_inner_smul_left] at hvariational
  nlinarith

/--
Conversely, a feasible variational first-order condition is a fixed point of
projected gradient descent.  Together with
`projectedGradient_fixedPoint_firstOrder`, this identifies the fixed points of
the projected update with constrained first-order points.
-/
theorem projectedGradient_fixedPoint_of_firstOrder
    (domain : Set Parameter) (project : Parameter → Parameter)
    (hproject : IsVariationalEuclideanProjectionOn domain project)
    (gradient parameter : Parameter) (hparameter : parameter ∈ domain)
    (stepSize : ℝ) (hstepSize : 0 < stepSize)
    (hfirstOrder : ∀ candidate ∈ domain, 0 ≤ ⟪gradient, candidate - parameter⟫_ℝ) :
    project (parameter - stepSize • gradient) = parameter := by
  let projected := project (parameter - stepSize • gradient)
  let displacement := projected - parameter
  have hprojected : projected ∈ domain := hproject.1 _
  have hfirst := hfirstOrder projected hprojected
  have hvariational := hproject.2 (parameter - stepSize • gradient) parameter hparameter
  have hvariational' : ‖displacement‖ ^ 2 +
      stepSize * ⟪gradient, displacement⟫_ℝ ≤ 0 := by
    rw [show parameter - stepSize • gradient - projected =
          -displacement - stepSize • gradient by
            simp only [displacement, projected]
            abel,
      show parameter - projected = -displacement by simp [displacement],
      inner_sub_left, inner_neg_left, inner_neg_right, real_inner_smul_left,
      real_inner_self_eq_norm_sq] at hvariational
    simpa using hvariational
  have hfirst' : 0 ≤ ⟪gradient, displacement⟫_ℝ := by
    simpa [displacement] using hfirst
  have hnorm_zero : ‖displacement‖ = 0 := by
    have hsq : ‖displacement‖ ^ 2 = 0 := by nlinarith
    exact (sq_eq_zero_iff).mp hsq
  simpa [projected, displacement] using sub_eq_zero.mp (norm_eq_zero.mp hnorm_zero)

end

/--
A real quadratic with negative squared coefficient is strictly concave on the
whole real line.  The explicit normal form makes this convenient for concrete
objective calculations without introducing a differentiability API.
-/
theorem strictConcaveOn_real_quadratic_of_neg
    (constant linear quadratic : ℝ) (hquadratic : quadratic < 0) :
    StrictConcaveOn ℝ Set.univ
      (fun theta : ℝ => constant + linear * theta + quadratic * theta ^ 2) := by
  refine ⟨convex_univ, ?_⟩
  intro first _ second _ hdistinct firstWeight secondWeight hfirstWeight hsecondWeight hweights
  have hdifference : first - second ≠ 0 := sub_ne_zero.mpr hdistinct
  have hsq : 0 < (first - second) ^ 2 := sq_pos_of_ne_zero hdifference
  have hcoefficient : 0 < -quadratic := neg_pos.mpr hquadratic
  have hproduct :
      0 < (-quadratic) * firstWeight * secondWeight * (first - second) ^ 2 := by
    positivity
  simp only [smul_eq_mul]
  have hid :
      (constant + linear * (firstWeight * first + secondWeight * second) +
          quadratic * (firstWeight * first + secondWeight * second) ^ 2) -
        (firstWeight * (constant + linear * first + quadratic * first ^ 2) +
          secondWeight * (constant + linear * second + quadratic * second ^ 2)) =
        (-quadratic) * firstWeight * secondWeight * (first - second) ^ 2 := by
    have hsquare :
        (firstWeight * first + secondWeight * second) ^ 2 -
          (firstWeight * first ^ 2 + secondWeight * second ^ 2) =
        -firstWeight * secondWeight * (first - second) ^ 2 := by
      have hzero :
          (firstWeight * first + secondWeight * second) ^ 2 -
              (firstWeight * first ^ 2 + secondWeight * second ^ 2) +
              firstWeight * secondWeight * (first - second) ^ 2 = 0 := by
        calc
          (firstWeight * first + secondWeight * second) ^ 2 -
                (firstWeight * first ^ 2 + secondWeight * second ^ 2) +
                firstWeight * secondWeight * (first - second) ^ 2 =
              (firstWeight * first ^ 2 + secondWeight * second ^ 2) *
                (firstWeight + secondWeight - 1) := by ring
          _ = 0 := by
            have hweightzero : firstWeight + secondWeight - 1 = 0 := by linarith
            rw [hweightzero]
            ring
      linarith
    calc
      (constant + linear * (firstWeight * first + secondWeight * second) +
          quadratic * (firstWeight * first + secondWeight * second) ^ 2) -
        (firstWeight * (constant + linear * first + quadratic * first ^ 2) +
          secondWeight * (constant + linear * second + quadratic * second ^ 2)) =
          constant * (1 - firstWeight - secondWeight) +
            quadratic * ((firstWeight * first + secondWeight * second) ^ 2 -
              (firstWeight * first ^ 2 + secondWeight * second ^ 2)) := by ring
      _ = quadratic * ((firstWeight * first + secondWeight * second) ^ 2 -
          (firstWeight * first ^ 2 + secondWeight * second ^ 2)) := by
            have hweightzero : 1 - firstWeight - secondWeight = 0 := by linarith
            rw [hweightzero]
            ring
      _ = (-quadratic) * firstWeight * secondWeight * (first - second) ^ 2 := by
        rw [hsquare]
        ring
  linarith

/--
A real quadratic with nonpositive squared coefficient is concave on the whole
real line.  This includes the affine boundary case omitted by the strict form.
-/
theorem concaveOn_real_quadratic_of_nonpos
    (constant linear quadratic : ℝ) (hquadratic : quadratic ≤ 0) :
    ConcaveOn ℝ Set.univ
      (fun theta : ℝ => constant + linear * theta + quadratic * theta ^ 2) := by
  refine ⟨convex_univ, ?_⟩
  intro first _ second _ firstWeight secondWeight hfirstWeight hsecondWeight hweights
  have hcoefficient : 0 ≤ -quadratic := neg_nonneg.mpr hquadratic
  have hsq : 0 ≤ (first - second) ^ 2 := sq_nonneg _
  have hproduct :
      0 ≤ (-quadratic) * firstWeight * secondWeight * (first - second) ^ 2 := by
    positivity
  simp only [smul_eq_mul]
  have hid :
      (constant + linear * (firstWeight * first + secondWeight * second) +
          quadratic * (firstWeight * first + secondWeight * second) ^ 2) -
        (firstWeight * (constant + linear * first + quadratic * first ^ 2) +
          secondWeight * (constant + linear * second + quadratic * second ^ 2)) =
        (-quadratic) * firstWeight * secondWeight * (first - second) ^ 2 := by
    have hsquare :
        (firstWeight * first + secondWeight * second) ^ 2 -
          (firstWeight * first ^ 2 + secondWeight * second ^ 2) =
        -firstWeight * secondWeight * (first - second) ^ 2 := by
      have hzero :
          (firstWeight * first + secondWeight * second) ^ 2 -
              (firstWeight * first ^ 2 + secondWeight * second ^ 2) +
              firstWeight * secondWeight * (first - second) ^ 2 = 0 := by
        calc
          (firstWeight * first + secondWeight * second) ^ 2 -
                (firstWeight * first ^ 2 + secondWeight * second ^ 2) +
                firstWeight * secondWeight * (first - second) ^ 2 =
              (firstWeight * first ^ 2 + secondWeight * second ^ 2) *
                (firstWeight + secondWeight - 1) := by ring
          _ = 0 := by
            have hweightzero : firstWeight + secondWeight - 1 = 0 := by linarith
            rw [hweightzero]
            ring
      linarith
    calc
      (constant + linear * (firstWeight * first + secondWeight * second) +
          quadratic * (firstWeight * first + secondWeight * second) ^ 2) -
        (firstWeight * (constant + linear * first + quadratic * first ^ 2) +
          secondWeight * (constant + linear * second + quadratic * second ^ 2)) =
          constant * (1 - firstWeight - secondWeight) +
            quadratic * ((firstWeight * first + secondWeight * second) ^ 2 -
              (firstWeight * first ^ 2 + secondWeight * second ^ 2)) := by ring
      _ = quadratic * ((firstWeight * first + secondWeight * second) ^ 2 -
          (firstWeight * first ^ 2 + secondWeight * second ^ 2)) := by
            have hweightzero : 1 - firstWeight - secondWeight = 0 := by linarith
            rw [hweightzero]
            ring
      _ = (-quadratic) * firstWeight * secondWeight * (first - second) ^ 2 := by
        rw [hsquare]
        ring
  linarith

/--
An affine interpolation stays in an absolute-value interval when both endpoint
values lie in that interval.  This elementary one-dimensional certificate is
useful when a parameter-dependent probability is defined on a closed segment.
-/
theorem abs_affine_parameter_le_of_endpoint_abs_le
    (left right radius parameter : ℝ)
    (hleft : |left| ≤ radius) (hright : |right| ≤ radius)
    (hparameter : parameter ∈ Set.Icc (0 : ℝ) 1) :
    |(1 - parameter) * left + parameter * right| ≤ radius := by
  have hleftWeight : 0 ≤ 1 - parameter := by linarith [hparameter.2]
  have hparameterWeight : 0 ≤ parameter := hparameter.1
  calc
    |(1 - parameter) * left + parameter * right| ≤
        |(1 - parameter) * left| + |parameter * right| := abs_add_le _ _
    _ = (1 - parameter) * |left| + parameter * |right| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hleftWeight, abs_of_nonneg hparameterWeight]
    _ ≤ (1 - parameter) * radius + parameter * radius := by gcongr
    _ = radius := by linarith

end AppliedModelingLib

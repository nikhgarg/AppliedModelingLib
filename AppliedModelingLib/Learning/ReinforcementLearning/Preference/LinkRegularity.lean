import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Derivative-bounded preference links

Preference-feedback analyses often assume a differentiable link with positive
derivative bounds on the range of possible trajectory-reward differences. The
mean-value consequences are recorded here without selecting a particular link.
-/

namespace AppliedModelingLib

namespace PreferenceRL

/--
A preference link has a positive derivative lower bound on the trajectory
reward-difference interval `[-horizon, horizon]`.
-/
structure PositiveLowerDerivativePreferenceLink (link : ℝ → ℝ)
    (horizon lowerSlope : ℝ) : Prop where
  lowerSlope_pos : 0 < lowerSlope
  continuousOn : ContinuousOn link (Set.Icc (-horizon) horizon)
  differentiableOn : DifferentiableOn ℝ link (interior (Set.Icc (-horizon) horizon))
  lowerSlope_le_deriv : ∀ x, x ∈ Set.Icc (-horizon) horizon → lowerSlope ≤ deriv link x

namespace PositiveLowerDerivativePreferenceLink

variable {link : ℝ → ℝ} {horizon lowerSlope : ℝ}

/-- The lower derivative bound gives a lower finite-difference bound. -/
theorem lowerSlope_mul_sub_le_link_sub
    (hlink : PositiveLowerDerivativePreferenceLink link horizon lowerSlope)
    {first second : ℝ}
    (hfirst : first ∈ Set.Icc (-horizon) horizon)
    (hsecond : second ∈ Set.Icc (-horizon) horizon)
    (horder : first ≤ second) :
    lowerSlope * (second - first) ≤ link second - link first := by
  exact (convex_Icc (-horizon) horizon).mul_sub_le_image_sub_of_le_deriv hlink.continuousOn
    hlink.differentiableOn
    (fun x hx => hlink.lowerSlope_le_deriv x (interior_subset hx))
    first hfirst second hsecond horder

/--
The positive lower derivative bound controls reward-difference error by linked
probability error on the valid interval.
-/
theorem abs_sub_le_abs_linkSub_div_lowerSlope
    (hlink : PositiveLowerDerivativePreferenceLink link horizon lowerSlope)
    {first second : ℝ}
    (hfirst : first ∈ Set.Icc (-horizon) horizon)
    (hsecond : second ∈ Set.Icc (-horizon) horizon) :
    |first - second| ≤ |link first - link second| / lowerSlope := by
  rcases le_total first second with horder | horder
  · have hbound := hlink.lowerSlope_mul_sub_le_link_sub hfirst hsecond horder
    have hscaled : lowerSlope * (second - first) ≤ |link second - link first| :=
      hbound.trans (le_abs_self _)
    have hdiv : second - first ≤ |link second - link first| / lowerSlope := by
      apply (le_div_iff₀ hlink.lowerSlope_pos).mpr
      simpa [mul_comm] using hscaled
    calc
      |first - second| = second - first := by
        rw [abs_of_nonpos (sub_nonpos.mpr horder)]
        ring
      _ ≤ |link second - link first| / lowerSlope := hdiv
      _ = |link first - link second| / lowerSlope := by
        rw [show link second - link first = -(link first - link second) by ring, abs_neg]
  · have hbound := hlink.lowerSlope_mul_sub_le_link_sub hsecond hfirst horder
    have hscaled : lowerSlope * (first - second) ≤ |link first - link second| :=
      hbound.trans (le_abs_self _)
    have hdiv : first - second ≤ |link first - link second| / lowerSlope := by
      apply (le_div_iff₀ hlink.lowerSlope_pos).mpr
      simpa [mul_comm] using hscaled
    calc
      |first - second| = first - second := abs_of_nonneg (sub_nonneg.mpr horder)
      _ ≤ |link first - link second| / lowerSlope := hdiv

end PositiveLowerDerivativePreferenceLink

/--
A preference link has lower and upper derivative bounds on the trajectory
reward-difference interval `[-horizon, horizon]`.
-/
structure DerivativeBoundedPreferenceLink (link : ℝ → ℝ)
    (horizon lowerSlope upperSlope : ℝ) : Prop where
  lowerSlope_pos : 0 < lowerSlope
  continuousOn : ContinuousOn link (Set.Icc (-horizon) horizon)
  differentiableOn : DifferentiableOn ℝ link (interior (Set.Icc (-horizon) horizon))
  lowerSlope_le_deriv : ∀ x, x ∈ Set.Icc (-horizon) horizon → lowerSlope ≤ deriv link x
  deriv_le_upperSlope : ∀ x, x ∈ Set.Icc (-horizon) horizon → deriv link x ≤ upperSlope

namespace DerivativeBoundedPreferenceLink

variable {link : ℝ → ℝ} {horizon lowerSlope upperSlope : ℝ}

/-- The lower derivative bound gives a lower finite-difference bound. -/
theorem lowerSlope_mul_sub_le_link_sub
    (hlink : DerivativeBoundedPreferenceLink link horizon lowerSlope upperSlope)
    {first second : ℝ}
    (hfirst : first ∈ Set.Icc (-horizon) horizon)
    (hsecond : second ∈ Set.Icc (-horizon) horizon)
    (horder : first ≤ second) :
    lowerSlope * (second - first) ≤ link second - link first := by
  exact (convex_Icc (-horizon) horizon).mul_sub_le_image_sub_of_le_deriv hlink.continuousOn
    hlink.differentiableOn
    (fun x hx => hlink.lowerSlope_le_deriv x (interior_subset hx))
    first hfirst second hsecond horder

/-- The upper derivative bound gives an upper finite-difference bound. -/
theorem link_sub_le_upperSlope_mul_sub
    (hlink : DerivativeBoundedPreferenceLink link horizon lowerSlope upperSlope)
    {first second : ℝ}
    (hfirst : first ∈ Set.Icc (-horizon) horizon)
    (hsecond : second ∈ Set.Icc (-horizon) horizon)
    (horder : first ≤ second) :
    link second - link first ≤ upperSlope * (second - first) := by
  exact (convex_Icc (-horizon) horizon).image_sub_le_mul_sub_of_deriv_le hlink.continuousOn
    hlink.differentiableOn
    (fun x hx => hlink.deriv_le_upperSlope x (interior_subset hx))
    first hfirst second hsecond horder

/--
The derivative upper bound controls the absolute link difference by the
absolute reward-difference change on the valid interval.
-/
theorem abs_linkSub_le_upperSlope_mul_abs_sub
    (hlink : DerivativeBoundedPreferenceLink link horizon lowerSlope upperSlope)
    {first second : ℝ}
    (hfirst : first ∈ Set.Icc (-horizon) horizon)
    (hsecond : second ∈ Set.Icc (-horizon) horizon) :
    |link first - link second| ≤ upperSlope * |first - second| := by
  rcases le_total first second with horder | horder
  · have hupper := hlink.link_sub_le_upperSlope_mul_sub hfirst hsecond horder
    have hlower := hlink.lowerSlope_mul_sub_le_link_sub hfirst hsecond horder
    have hlinkOrder : 0 ≤ link second - link first := by
      have hscaledNonneg : 0 ≤ lowerSlope * (second - first) :=
        mul_nonneg hlink.lowerSlope_pos.le (sub_nonneg.mpr horder)
      linarith
    calc
      |link first - link second| = link second - link first := by
        rw [abs_of_nonpos (by linarith)]
        ring
      _ ≤ upperSlope * (second - first) := hupper
      _ = upperSlope * |first - second| := by
        rw [abs_of_nonpos (sub_nonpos.mpr horder)]
        ring
  · have hupper := hlink.link_sub_le_upperSlope_mul_sub hsecond hfirst horder
    have hlower := hlink.lowerSlope_mul_sub_le_link_sub hsecond hfirst horder
    have hlinkOrder : 0 ≤ link first - link second := by
      have hscaledNonneg : 0 ≤ lowerSlope * (first - second) :=
        mul_nonneg hlink.lowerSlope_pos.le (sub_nonneg.mpr horder)
      linarith
    calc
      |link first - link second| = link first - link second :=
        abs_of_nonneg hlinkOrder
      _ ≤ upperSlope * (first - second) := hupper
      _ = upperSlope * |first - second| := by
        rw [abs_of_nonneg (sub_nonneg.mpr horder)]

/-- A positive lower derivative bound makes the link strictly increasing on its valid interval. -/
theorem strictMonoOn
    (hlink : DerivativeBoundedPreferenceLink link horizon lowerSlope upperSlope) :
    StrictMonoOn link (Set.Icc (-horizon) horizon) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc (-horizon) horizon) hlink.continuousOn
  intro x hx
  exact lt_of_lt_of_le hlink.lowerSlope_pos
    (hlink.lowerSlope_le_deriv x (interior_subset hx))

end DerivativeBoundedPreferenceLink

end PreferenceRL

end AppliedModelingLib

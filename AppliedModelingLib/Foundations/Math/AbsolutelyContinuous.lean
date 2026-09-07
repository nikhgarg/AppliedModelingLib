import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-!
# Absolutely Continuous Real Functions

Small real-analysis bridges that preserve the almost-everywhere conclusion of
absolute continuity when it is used in an economic or optimization model.
-/

open MeasureTheory
open scoped Topology

namespace AppliedModelingLib
namespace RealAnalysis

/--
Local CDF-transport derivative identity.  If a real function agrees in a
neighborhood with a composition, its derivative is the derivative of the
outer function at the transported point times the derivative of the inner
function.  The statement deliberately uses eventual equality, so it applies
to an explicitly supplied local transport interval rather than assuming a
global identity.
-/
theorem hasDerivAt_eq_mul_of_eventuallyEq_comp
    {F G g : ℝ → ℝ} {x f' G' g' : ℝ}
    (hF : HasDerivAt F f' x)
    (hG : HasDerivAt G G' (g x))
    (hg : HasDerivAt g g' x)
    (heq : F =ᶠ[𝓝 x] fun y => G (g y)) :
    f' = G' * g' := by
  exact hF.unique ((hG.comp x hg).congr_of_eventuallyEq heq)

/--
Converse local chain rule for a scalar inner function.  Suppose `G ∘ g`
agrees locally with a differentiable function `F`, the outer function `G` is
continuously differentiable near `g x`, and its derivative there is nonzero.
Then `g` is differentiable at `x`, with derivative `F' / G'`.

The continuity premise on `g` selects the local inverse branch of `G`.  This
is useful for implicitly represented curves: unlike the forward chain rule,
it does not assume the curve's differentiability in advance.
-/
theorem hasDerivAt_inner_of_contDiffAt_outer_of_eventuallyEq_comp
    {F G g : ℝ → ℝ} {x F' G' : ℝ}
    (hF : HasDerivAt F F' x)
    (hG : HasDerivAt G G' (g x))
    (hG_c1 : ContDiffAt ℝ 1 G (g x))
    (hG_ne : G' ≠ 0)
    (hg : ContinuousAt g x)
    (heq : (fun y => G (g y)) =ᶠ[nhds x] F) :
    HasDerivAt g (G'⁻¹ * F') x := by
  have hG_strict : HasStrictDerivAt G G' (g x) :=
    hG_c1.hasStrictDerivAt' hG one_ne_zero
  let inv : ℝ → ℝ := hG_strict.localInverse G G' (g x) hG_ne
  have heq_at : G (g x) = F x := heq.self_of_nhds
  have hinv_deriv : HasDerivAt inv G'⁻¹ (F x) := by
    simpa only [inv, heq_at] using
      (hG_strict.to_localInverse hG_ne).hasDerivAt
  have hginv : g =ᶠ[nhds x] fun y => inv (F y) := by
    have hinv_g : ∀ᶠ y in nhds x, inv (G (g y)) = g y :=
      hg.tendsto.eventually (hG_strict.eventually_left_inverse hG_ne)
    filter_upwards [heq, hinv_g] with y hy hiy
    rw [← hy]
    exact hiy.symm
  exact (hinv_deriv.comp x hF).congr_of_eventuallyEq hginv

/--
If a differentiable real function is locally constant, its specified
derivative is zero.  The local equality is an explicit premise, so this does
not turn an a.e. density statement into a pointwise one without a chosen
representative.
-/
theorem hasDerivAt_eq_zero_of_eventuallyEq_const
    {F : ℝ → ℝ} {x f' c : ℝ}
    (hF : HasDerivAt F f' x)
    (heq : F =ᶠ[𝓝 x] fun _ => c) :
    f' = 0 := by
  exact hF.unique ((hasDerivAt_const x c).congr_of_eventuallyEq heq)

/--
The totalized derivative of a locally constant real function is zero.  Unlike
the `HasDerivAt` version, this needs no differentiability premise because
`deriv` is defined at every point; it is useful when an a.e. density has been
represented by the canonical `deriv` function.
-/
theorem deriv_eq_zero_of_eventuallyEq_const
    {F : ℝ → ℝ} {x c : ℝ}
    (heq : F =ᶠ[𝓝 x] fun _ => c) :
    deriv F x = 0 := by
  rw [heq.deriv_eq]
  exact deriv_const x c

/-- A positive derivative forces a strict decrease at some nearby point to
the left.  The interval endpoint `a` can be chosen arbitrarily below the
differentiation point, which makes the lemma convenient for support-gap
deviations whose candidate must stay inside a prescribed open gap. -/
theorem exists_left_value_lt_of_hasDerivAt_pos
    {f : ℝ → ℝ} {f' a b : ℝ}
    (hf : HasDerivAt f f' b) (hfpos : 0 < f') (hab : a < b) :
    ∃ x, x ∈ Set.Ioo a b ∧ f x < f b := by
  have hslope_eventually : ∀ᶠ x in 𝓝[<] b, 0 < slope f b x :=
    (hasDerivAt_iff_tendsto_slope_left_right.mp hf).1
      (isOpen_Ioi.mem_nhds hfpos)
  have hboth : ∀ᶠ x in 𝓝[<] b,
      0 < slope f b x ∧ x ∈ Set.Ioo a b :=
    hslope_eventually.and (Ioo_mem_nhdsLT hab)
  rcases hboth.exists with ⟨x, hslope, hx⟩
  refine ⟨x, hx, ?_⟩
  rw [slope_fun_def_field] at hslope
  rcases (div_pos_iff.mp hslope) with hpos | hneg
  · linarith [hpos.2, hx.2]
  · linarith [hneg.1]

/--
Two continuous real functions that have the same specified derivative at
every interior point of a closed interval and agree at the left endpoint
agree throughout the interval.  The endpoint derivatives are deliberately
not required; this is useful for power laws whose derivative formula is only
available at strictly positive arguments.
-/
theorem eqOn_Icc_of_hasDerivAt_eq_of_eq_left
    {f g f' : ℝ → ℝ} {a b : ℝ}
    (hfcont : ContinuousOn f (Set.Icc a b))
    (hgcont : ContinuousOn g (Set.Icc a b))
    (hfderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hgderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt g (f' x) x)
    (hleft : f a = g a) :
    Set.EqOn f g (Set.Icc a b) := by
  intro y hy
  rcases eq_or_lt_of_le hy.1 with hya | hay
  · simpa [hya] using hleft
  · let d : ℝ → ℝ := fun x => f x - g x
    have hdcont : ContinuousOn d (Set.Icc a y) :=
      (hfcont.mono (Set.Icc_subset_Icc_right hy.2)).sub
        (hgcont.mono (Set.Icc_subset_Icc_right hy.2))
    have hdderiv : ∀ x ∈ Set.Ioo a y, HasDerivAt d 0 x := by
      intro x hx
      have hxab : x ∈ Set.Ioo a b := ⟨hx.1, hx.2.trans_le hy.2⟩
      simpa only [d, sub_self] using
        (hfderiv x hxab).sub (hgderiv x hxab)
    obtain ⟨c, hc, hcSlope⟩ :=
      exists_hasDerivAt_eq_slope d (fun _ => 0) hay hdcont hdderiv
    have hya_ne : y - a ≠ 0 := sub_ne_zero.mpr hay.ne'
    have hdiff : d y - d a = 0 := by
      have hzero : (d y - d a) / (y - a) = 0 := hcSlope.symm
      rcases (div_eq_zero_iff.mp hzero) with hdiff | hden
      · exact hdiff
      · exact (hya_ne hden).elim
    dsimp only [d] at hdiff
    linarith

/--
A continuous function with derivative `β * C * x ^ (β - 1)` at every
strictly positive interior point and value zero at the origin is exactly the
power law `C * x ^ β` on the closed interval.  No derivative is required at
zero, so the statement matches the usual endpoint treatment of real powers.
-/
theorem eqOn_const_mul_rpow_of_hasDerivAt
    {f : ℝ → ℝ} {C β B : ℝ}
    (hβ : 0 < β)
    (hfcont : ContinuousOn f (Set.Icc 0 B))
    (hzero : f 0 = 0)
    (hfderiv : ∀ x ∈ Set.Ioo 0 B,
      HasDerivAt f (β * C * x ^ (β - 1)) x) :
    Set.EqOn f (fun x => C * x ^ β) (Set.Icc 0 B) := by
  apply eqOn_Icc_of_hasDerivAt_eq_of_eq_left hfcont
      ((continuous_const.mul (Real.continuous_rpow_const hβ.le)).continuousOn)
      hfderiv
  · intro x hx
    convert
      (Real.hasDerivAt_rpow_const (x := x) (p := β) (Or.inl hx.1.ne')).const_mul C
        using 1 <;> ring
  · simpa [hzero, hβ.ne']

/--
Taking a nonzero natural root of a nonnegative power identity preserves the
usual constant-times-power form.  This packages the conversion from an
order-statistic identity `x^n = C z^β` to the underlying CDF power law.
-/
theorem eq_const_mul_rpow_of_natPow_eq
    {x C z β : ℝ} {n : ℕ}
    (hx : 0 ≤ x) (hC : 0 ≤ C) (hz : 0 ≤ z) (hn : n ≠ 0)
    (hpow : x ^ n = C * z ^ β) :
    x = C ^ ((n : ℝ)⁻¹) * z ^ (β / (n : ℝ)) := by
  have hbase : 0 ≤ C * z ^ β :=
    mul_nonneg hC (Real.rpow_nonneg hz β)
  have hroot_nonneg : 0 ≤ (C * z ^ β) ^ ((n : ℝ)⁻¹) :=
    Real.rpow_nonneg hbase _
  have hroot : x = (C * z ^ β) ^ ((n : ℝ)⁻¹) := by
    apply (pow_left_inj₀ hx hroot_nonneg hn).mp
    rw [hpow, Real.rpow_inv_natCast_pow hbase hn]
  rw [hroot, Real.mul_rpow hC (Real.rpow_nonneg hz β)]
  congr 1
  rw [← Real.rpow_mul hz, div_eq_mul_inv]

/-- An absolutely continuous real function has derivative `deriv f x` at
almost every point of the specified closed interval. -/
theorem ae_hasDerivAt_deriv_of_absolutelyContinuousOnInterval
    {f : ℝ → ℝ} {a b : ℝ} (hAC : AbsolutelyContinuousOnInterval f a b) :
    ∀ᵐ x ∂volume, x ∈ Set.uIcc a b → HasDerivAt f (deriv f x) x := by
  filter_upwards [hAC.ae_differentiableAt] with x hx
  intro hxmem
  exact (hx hxmem).hasDerivAt

/-- Natural powers preserve absolute continuity on a real interval. -/
theorem AbsolutelyContinuousOnInterval.pow
    {f : ℝ → ℝ} {a b : ℝ} (hAC : AbsolutelyContinuousOnInterval f a b)
    (n : ℕ) : AbsolutelyContinuousOnInterval (fun x => f x ^ n) a b := by
  induction n with
  | zero =>
      simpa using
        (LipschitzWith.const (1 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
  | succ n hn =>
      simpa [pow_succ] using hn.mul hAC

end RealAnalysis
end AppliedModelingLib

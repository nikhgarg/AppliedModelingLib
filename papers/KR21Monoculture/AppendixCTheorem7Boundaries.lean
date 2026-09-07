import KR21Monoculture.RUM

open AppliedModelingLib Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace KR21Monoculture

/-!
# Appendix C Theorem 7 Boundary Cutoffs

The original Appendix-C case split proves the strict derivative signs away
from the two cutoff boundaries.  This module differentiates the literal
density/CDF ratio itself, then uses the source formulas on the appropriate
one-sided neighborhoods to discharge `a = x_j` and `a = x_i` without changing
the source quantifiers.
-/

private theorem integral_Iic_hasDerivAt_of_continuous
    (f : ℝ → ℝ) (hcont : Continuous f)
    (hint : ∀ a : ℝ, IntegrableOn f (Set.Iic a)) (a : ℝ) :
    HasDerivAt (fun b : ℝ => ∫ x : ℝ in Set.Iic b, f x) (f a) a := by
  let c : ℝ := ∫ x : ℝ in Set.Iic (0 : ℝ), f x
  have hderiv :
      HasDerivAt (fun b : ℝ => c + ∫ x in (0 : ℝ)..b, f x) (f a) a := by
    simpa [c] using
      (hcont.integral_hasStrictDerivAt (0 : ℝ) a).hasDerivAt.const_add c
  have heq :
      (fun b : ℝ => ∫ x : ℝ in Set.Iic b, f x) =ᶠ[nhds a]
        (fun b : ℝ => c + ∫ x in (0 : ℝ)..b, f x) :=
    Filter.Eventually.of_forall fun b => by
      have hsub := intervalIntegral.integral_Iic_sub_Iic
        (f := f) (a := (0 : ℝ)) (b := b) (hint 0) (hint b)
      dsimp [c]
      linarith
  exact hderiv.congr_of_eventuallyEq heq

private theorem theorem7LaplaceCDFClosedForm_hasDerivAt
    {lam μ a : ℝ} (hlam : 0 < lam) :
    HasDerivAt (fun b : ℝ => theorem7LaplaceCDFClosedForm lam μ b)
      (theorem7LaplacePDF lam μ a) a := by
  have hraw := integral_Iic_hasDerivAt_of_continuous
    (fun x : ℝ => theorem7LaplacePDF lam μ x)
    (theorem7LaplacePDF_continuous lam μ)
    (fun b => theorem7LaplacePDF_integrableOn_Iic
      (lam := lam) (μ := μ) (a := b) hlam) a
  exact hraw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun b =>
      (theorem7LaplaceCDFIntegral_eq_closedForm
        (lam := lam) (μ := μ) (a := b) hlam).symm)

private theorem theorem7LaplacianPairIntegrand_continuous
    {lam xi xj : ℝ} (hlam : 0 < lam) :
    Continuous (fun x : ℝ => theorem7LaplacianPairIntegrand lam xi xj x) := by
  unfold theorem7LaplacianPairIntegrand
  exact (theorem7LaplacePDF_continuous lam xi).mul
    (continuous_iff_continuousAt.mpr fun x =>
      (theorem7LaplaceCDFClosedForm_hasDerivAt
        (lam := lam) (μ := xj) (a := x) hlam).continuousAt)

private theorem theorem7LaplacianPDFCDFRatioAt_hasDerivAt
    {lam xi xj a : ℝ} (hlam : 0 < lam) :
    HasDerivAt
      (fun b : ℝ => theorem7LaplacianPDFCDFRatioAt lam xi xj b)
      ((theorem7LaplacianPairIntegrand lam xi xj a *
          (theorem7LaplaceCDFClosedForm lam xi a *
            theorem7LaplaceCDFClosedForm lam xj a) -
        (∫ x : ℝ in Set.Iic a,
          theorem7LaplacianPairIntegrand lam xi xj x) *
          (theorem7LaplacePDF lam xi a *
              theorem7LaplaceCDFClosedForm lam xj a +
            theorem7LaplaceCDFClosedForm lam xi a *
              theorem7LaplacePDF lam xj a)) /
        (theorem7LaplaceCDFClosedForm lam xi a *
          theorem7LaplaceCDFClosedForm lam xj a) ^ 2)
      a := by
  have hnum :
      HasDerivAt
        (fun b : ℝ => ∫ x : ℝ in Set.Iic b,
          theorem7LaplacianPairIntegrand lam xi xj x)
        (theorem7LaplacianPairIntegrand lam xi xj a) a :=
    integral_Iic_hasDerivAt_of_continuous
      (fun x : ℝ => theorem7LaplacianPairIntegrand lam xi xj x)
      (theorem7LaplacianPairIntegrand_continuous (lam := lam)
        (xi := xi) (xj := xj) hlam)
      (fun b => theorem7LaplacianPairIntegrand_integrableOn_Iic
        (lam := lam) (xi := xi) (xj := xj) (a := b) hlam) a
  have hFi := theorem7LaplaceCDFClosedForm_hasDerivAt
    (lam := lam) (μ := xi) (a := a) hlam
  have hFj := theorem7LaplaceCDFClosedForm_hasDerivAt
    (lam := lam) (μ := xj) (a := a) hlam
  have hden :
      HasDerivAt
        (fun b : ℝ => theorem7LaplaceCDFClosedForm lam xi b *
          theorem7LaplaceCDFClosedForm lam xj b)
        (theorem7LaplacePDF lam xi a *
            theorem7LaplaceCDFClosedForm lam xj a +
          theorem7LaplaceCDFClosedForm lam xi a *
            theorem7LaplacePDF lam xj a) a := by
    simpa using hFi.mul hFj
  have hden_ne :
      theorem7LaplaceCDFClosedForm lam xi a *
          theorem7LaplaceCDFClosedForm lam xj a ≠ 0 := by
    exact mul_ne_zero
      (theorem7LaplaceCDFClosedForm_pos
        (lam := lam) (μ := xi) (a := a) hlam).ne'
      (theorem7LaplaceCDFClosedForm_pos
        (lam := lam) (μ := xj) (a := a) hlam).ne'
  unfold theorem7LaplacianPDFCDFRatioAt
  simpa using hnum.div hden hden_ne

private theorem theorem7LaplacianCase2ConditionalProb_hasDerivAt_zero_at_xj
    {lam xj : ℝ} :
    HasDerivAt
      (fun a : ℝ => 1 - theorem7LaplacianCase2TailRatio lam xj a) 0 xj := by
  have hden : 2 * Real.exp (lam * (xj - xj)) - 1 ≠ 0 := by
    norm_num
  have htail := theorem7LaplacianCase2TailRatio_hasDerivAt
    (lam := lam) (xj := xj) (a := xj) hden
  convert (hasDerivAt_const xj (1 : ℝ)).sub htail using 1
  norm_num
  ring

private theorem theorem7LaplacianPDFCDFRatioAt_eq_case2_on_Icc
    {lam xi xj a : ℝ} (hlam : 0 < lam) (hx : xj < xi)
    (hleft : xj ≤ a) (hright : a ≤ xi) :
    theorem7LaplacianPDFCDFRatioAt lam xi xj a =
      1 - theorem7LaplacianCase2TailRatio lam xj a := by
  rcases hleft.eq_or_lt with rfl | hleft
  · rw [theorem7LaplacianPDFCDFRatioAt_eq_case1]
    unfold theorem7LaplacianCase1IntegralRatio theorem7LaplacianPairIntegrand
    rw [paper_theorem7_laplacian_case1_integral_ratio
      (lam := lam) (xi := xi) (xj := xj) (a := xj) hlam le_rfl hx]
    norm_num [theorem7LaplacianCase2TailRatio]
  · rw [theorem7LaplacianPDFCDFRatioAt_eq_case2 hlam (le_of_lt hleft)]
    unfold theorem7LaplacianCase2IntegralRatio theorem7LaplacianPairIntegrand
    exact paper_theorem7_laplacian_case2_integral_ratio
      (lam := lam) (xi := xi) (xj := xj) (a := a)
      hlam hleft hright hx

/--
The omitted `a = x_j` endpoint in the paper's Theorem 7 / (C.2) case split.
The literal density/CDF conditional ratio is differentiable there with zero
derivative, so the advertised weak derivative inequality holds at the join.
-/
theorem theorem7LaplacianPDFCDFRatioAt_hasDerivAt_zero_at_xj
    {lam xi xj : ℝ} (hlam : 0 < lam) (hx : xj < xi) :
    HasDerivAt
      (fun a : ℝ => theorem7LaplacianPDFCDFRatioAt lam xi xj a) 0 xj := by
  let F : ℝ → ℝ := fun a => theorem7LaplacianPDFCDFRatioAt lam xi xj a
  let G : ℝ → ℝ := fun a => 1 - theorem7LaplacianCase2TailRatio lam xj a
  have hleft_eq : ∀ a ∈ Set.Iic xj, F a = (1 / 2 : ℝ) := by
    intro a ha
    dsimp [F]
    rw [theorem7LaplacianPDFCDFRatioAt_eq_case1]
    unfold theorem7LaplacianCase1IntegralRatio theorem7LaplacianPairIntegrand
    exact paper_theorem7_laplacian_case1_integral_ratio
      (lam := lam) (xi := xi) (xj := xj) (a := a) hlam ha hx
  have hleft : HasDerivWithinAt F 0 (Set.Iic xj) xj := by
    exact (hasDerivAt_const xj (1 / 2 : ℝ)).hasDerivWithinAt.congr_of_mem
      hleft_eq (by simp)
  have hright_eq : ∀ a ∈ Set.Icc xj xi, F a = G a := by
    intro a ha
    dsimp [F, G]
    exact theorem7LaplacianPDFCDFRatioAt_eq_case2_on_Icc
      (lam := lam) (xi := xi) (xj := xj) (a := a) hlam hx ha.1 ha.2
  have hright : HasDerivWithinAt F 0 (Set.Icc xj xi) xj := by
    exact
      (theorem7LaplacianCase2ConditionalProb_hasDerivAt_zero_at_xj
        (lam := lam) (xj := xj)).hasDerivWithinAt.congr_of_mem
        hright_eq (by simp [hx.le])
  have hunion : HasDerivWithinAt F 0 (Set.Iic xi) xj := by
    rw [show Set.Iic xi = Set.Iic xj ∪ Set.Icc xj xi by
      ext a
      simp only [Set.mem_Iic, Set.mem_union, Set.mem_Icc]
      constructor
      · intro ha
        by_cases hax : a ≤ xj
        · exact Or.inl hax
        · exact Or.inr ⟨le_of_not_ge hax, ha⟩
      · intro ha
        rcases ha with ha | ha
        · exact ha.trans hx.le
        · exact ha.2]
    exact hleft.union hright
  exact hunion.hasDerivAt (Iic_mem_nhds hx)

/--
The omitted `a = x_i` endpoint in the paper's Theorem 7 / (C.2) case split.
The literal density/CDF conditional ratio has the positive derivative of the
middle source formula at this join.
-/
theorem theorem7LaplacianPDFCDFRatioAt_hasDerivAt_pos_at_xi
    {lam xi xj : ℝ} (hlam : 0 < lam) (hx : xj < xi) :
    ∃ d,
      HasDerivAt
        (fun a : ℝ => theorem7LaplacianPDFCDFRatioAt lam xi xj a) d xi ∧
      0 < d := by
  let F : ℝ → ℝ := fun a => theorem7LaplacianPDFCDFRatioAt lam xi xj a
  let G : ℝ → ℝ := fun a => 1 - theorem7LaplacianCase2TailRatio lam xj a
  obtain ⟨d, hG, hdpos⟩ :=
    theorem7LaplacianCase2ConditionalProb_hasDerivAt_pos
      (lam := lam) (xj := xj) (a := xi) hlam (sub_pos.mpr hx)
  have hF := theorem7LaplacianPDFCDFRatioAt_hasDerivAt
    (lam := lam) (xi := xi) (xj := xj) (a := xi) hlam
  have hFG : ∀ a ∈ Set.Icc xj xi, F a = G a := by
    intro a ha
    dsimp [F, G]
    exact theorem7LaplacianPDFCDFRatioAt_eq_case2_on_Icc
      (lam := lam) (xi := xi) (xj := xj) (a := a) hlam hx ha.1 ha.2
  have hFwithin : HasDerivWithinAt F _ (Set.Icc xj xi) xi :=
    hF.hasDerivWithinAt
  have hGwithin : HasDerivWithinAt F d (Set.Icc xj xi) xi := by
    exact hG.hasDerivWithinAt.congr_of_mem hFG (by simp [hx.le])
  have hd : _ = d :=
    ((uniqueDiffOn_Icc hx) xi (by simp [hx.le])).eq_deriv _ hFwithin hGwithin
  refine ⟨d, ?_, hdpos⟩
  rwa [hd] at hF

/--
Literal Laplace form of (C.2): every real cutoff has a nonnegative derivative
for the density/CDF conditional probability ratio, and the derivative is
strictly positive at some cutoff.  Unlike the original three-case statement,
this includes both joins `a = x_j` and `a = x_i`.
-/
theorem theorem7LaplacianPDFCDFRatioAt_derivative_nonneg_all_and_pos_some
    {lam xi xj : ℝ} (hlam : 0 < lam) (hx : xj < xi) :
    (∀ a : ℝ, ∃ d,
      HasDerivAt
        (fun u : ℝ => theorem7LaplacianPDFCDFRatioAt lam xi xj u) d a ∧
      0 ≤ d) ∧
    (∃ a d,
      HasDerivAt
        (fun u : ℝ => theorem7LaplacianPDFCDFRatioAt lam xi xj u) d a ∧
      0 < d) := by
  let cases := fun a : ℝ =>
    theorem7LaplacianPDFCDFRatioAt_derivative_cases
      (lam := lam) (xi := xi) (xj := xj) (a := a) hlam hx
  refine ⟨?_, ?_⟩
  · intro a
    rcases lt_trichotomy a xj with ha | rfl | ha
    · obtain ⟨hd, hdnonneg⟩ := (cases a).1 ha
      exact ⟨0, hd, hdnonneg⟩
    · exact ⟨0,
        theorem7LaplacianPDFCDFRatioAt_hasDerivAt_zero_at_xj hlam hx,
        le_rfl⟩
    · rcases lt_trichotomy a xi with hmid | rfl | hright'
      · obtain ⟨d, hd, hdpos⟩ := (cases a).2.1 ha hmid
        exact ⟨d, hd, le_of_lt hdpos⟩
      · obtain ⟨d, hd, hdpos⟩ :=
          theorem7LaplacianPDFCDFRatioAt_hasDerivAt_pos_at_xi hlam hx
        exact ⟨d, hd, le_of_lt hdpos⟩
      · obtain ⟨d, hd, hdpos⟩ := (cases a).2.2.1 hright'
        exact ⟨d, hd, le_of_lt hdpos⟩
  · rcases (cases xi).2.2.2 with ⟨a, d, _hleft, _hright, hd, hdpos⟩
    exact ⟨a, d, hd, hdpos⟩

/--
The same all-cutoff (C.2) conclusion in the paper's strict-event syntax
`Pr[X_i > X_j | X_i < a, X_j < a]`.  The bridge is pointwise equality of the
actual product-probability ratio and the density/CDF ratio, not a naming
identification.
-/
theorem theorem7LaplacianProductStrictConditionalRatioAt_derivative_nonneg_all_and_pos_some
    {lam xi xj : ℝ} (hlam : 0 < lam) (hx : xj < xi) :
    (∀ a : ℝ, ∃ d,
      HasDerivAt
        (fun u : ℝ =>
          theorem7LaplacianProductStrictConditionalRatioAt lam xi xj u) d a ∧
      0 ≤ d) ∧
    (∃ a d,
      HasDerivAt
        (fun u : ℝ =>
          theorem7LaplacianProductStrictConditionalRatioAt lam xi xj u) d a ∧
      0 < d) := by
  obtain ⟨hnonneg, hwitness⟩ :=
    theorem7LaplacianPDFCDFRatioAt_derivative_nonneg_all_and_pos_some
      (lam := lam) (xi := xi) (xj := xj) hlam hx
  refine ⟨?_, ?_⟩
  · intro a
    obtain ⟨d, hd, hdnonneg⟩ := hnonneg a
    refine ⟨d, ?_, hdnonneg⟩
    exact hd.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun u =>
        theorem7LaplacianProductStrictConditionalRatioAt_eq_pdf_cdf
          (lam := lam) (xi := xi) (xj := xj) (a := u) hlam)
  · obtain ⟨a, d, hd, hdpos⟩ := hwitness
    refine ⟨a, d, ?_, hdpos⟩
    exact hd.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun u =>
        theorem7LaplacianProductStrictConditionalRatioAt_eq_pdf_cdf
          (lam := lam) (xi := xi) (xj := xj) (a := u) hlam)

end KR21Monoculture

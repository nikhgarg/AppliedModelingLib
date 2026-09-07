import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

namespace AppliedModelingLib
namespace Optimization

open Filter
open Set
open scoped Topology

/-!
# Endpoint Calculus

Reusable one-dimensional endpoint-move lemmas for continuous optimization
arguments.  These are useful when a paper proves that moving a cutoff or
interval endpoint improves an objective because the derivative has a fixed
sign, or until the first/last zero of a derivative proxy.

## Main declarations

- `endpoint_path_le_of_hasDerivAt_nonneg_on_Icc`
- `endpoint_path_lt_of_hasDerivAt_pos_on_Icc`
- `endpoint_path_ge_of_hasDerivAt_nonpos_on_Icc`
- `endpoint_path_gt_of_hasDerivAt_neg_on_Icc`
- `continuousOn_endpoint_positive_or_first_zero`
- `continuousOn_endpoint_negative_or_last_zero`
- `exists_pos_right_improvement_of_hasDerivAt_pos`
- `exists_pos_right_decrease_of_hasDerivAt_neg`
- `exists_pos_left_improvement_of_hasDerivAt_neg`
- `exists_pos_left_decrease_of_hasDerivAt_pos`
-/

/--
If a path has nonnegative derivative throughout the open interval between two
endpoint positions, moving from the left endpoint to the right endpoint weakly
improves the path value.
-/
theorem endpoint_path_le_of_hasDerivAt_nonneg_on_Icc
    {f f' : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hderiv_nonneg : ∀ x ∈ Ioo a b, 0 ≤ f' x) :
    f a ≤ f b := by
  by_cases hab_eq : a = b
  · simp [hab_eq]
  have hab_lt : a < b := lt_of_le_of_ne hab hab_eq
  have hmono : MonotoneOn f (Icc a b) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg
      (f' := f')
      (convex_Icc a b) hf ?_ ?_
    · intro x hx
      have hxIoo : x ∈ Ioo a b := by
        simpa [interior_Icc] using hx
      exact (hderiv x hxIoo).hasDerivWithinAt
    · intro x hx
      have hxIoo : x ∈ Ioo a b := by
        simpa [interior_Icc] using hx
      exact hderiv_nonneg x hxIoo
  exact hmono (by simp [hab]) (by simp [hab]) hab

/--
If a path has strictly positive derivative throughout the open interval between
two distinct endpoint positions, moving from left to right strictly improves
the path value.
-/
theorem endpoint_path_lt_of_hasDerivAt_pos_on_Icc
    {f f' : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hf : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hderiv_pos : ∀ x ∈ Ioo a b, 0 < f' x) :
    f a < f b := by
  have hmono : StrictMonoOn f (Icc a b) := by
    refine strictMonoOn_of_hasDerivWithinAt_pos
      (f' := f')
      (convex_Icc a b) hf ?_ ?_
    · intro x hx
      have hxIoo : x ∈ Ioo a b := by
        simpa [interior_Icc] using hx
      exact (hderiv x hxIoo).hasDerivWithinAt
    · intro x hx
      have hxIoo : x ∈ Ioo a b := by
        simpa [interior_Icc] using hx
      exact hderiv_pos x hxIoo
  exact hmono (by simp [le_of_lt hab]) (by simp [le_of_lt hab]) hab

/-- Nonpositive derivative version: moving left to right weakly decreases the path value. -/
theorem endpoint_path_ge_of_hasDerivAt_nonpos_on_Icc
    {f f' : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hderiv_nonpos : ∀ x ∈ Ioo a b, f' x ≤ 0) :
    f b ≤ f a := by
  have hle :
      (fun x => -f x) a ≤ (fun x => -f x) b :=
    endpoint_path_le_of_hasDerivAt_nonneg_on_Icc
      (f := fun x => -f x) (f' := fun x => -f' x)
      hab hf.neg
      (by
        intro x hx
        exact (hderiv x hx).neg)
      (by
        intro x hx
        exact neg_nonneg.mpr (hderiv_nonpos x hx))
  linarith

/-- Negative derivative version: moving left to right strictly decreases the path value. -/
theorem endpoint_path_gt_of_hasDerivAt_neg_on_Icc
    {f f' : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hf : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hderiv_neg : ∀ x ∈ Ioo a b, f' x < 0) :
    f b < f a := by
  have hlt :
      (fun x => -f x) a < (fun x => -f x) b :=
    endpoint_path_lt_of_hasDerivAt_pos_on_Icc
      (f := fun x => -f x) (f' := fun x => -f' x)
      hab hf.neg
      (by
        intro x hx
        exact (hderiv x hx).neg)
      (by
        intro x hx
        exact neg_pos.mpr (hderiv_neg x hx))
  linarith

/--
Continuity stopping dichotomy for endpoint moves.  If a derivative proxy is
positive at the left endpoint, then either it stays positive throughout the
interval or it hits zero somewhere.
-/
theorem continuousOn_endpoint_positive_or_exists_zero
    {g : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hg : ContinuousOn g (Icc a b))
    (hga : 0 < g a) :
    (∀ x ∈ Icc a b, 0 < g x) ∨
      ∃ c ∈ Icc a b, g c = 0 := by
  by_cases hpos : ∀ x ∈ Icc a b, 0 < g x
  · exact Or.inl hpos
  · push Not at hpos
    rcases hpos with ⟨x, hx, hx_nonpos⟩
    have hax : a ≤ x := hx.1
    have hg_ax : ContinuousOn g (Icc a x) :=
      hg.mono (Icc_subset_Icc_right hx.2)
    have hzero_between : (0 : ℝ) ∈ Icc (g x) (g a) :=
      ⟨hx_nonpos, le_of_lt hga⟩
    rcases intermediate_value_Icc' hax hg_ax hzero_between with
      ⟨c, hc, hgc⟩
    exact Or.inr ⟨c, ⟨hc.1, hc.2.trans hx.2⟩, hgc⟩

/-- Negative-sign version of `continuousOn_endpoint_positive_or_exists_zero`. -/
theorem continuousOn_endpoint_negative_or_exists_zero
    {g : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hg : ContinuousOn g (Icc a b))
    (hga : g a < 0) :
    (∀ x ∈ Icc a b, g x < 0) ∨
      ∃ c ∈ Icc a b, g c = 0 := by
  have hpos_or_zero :=
    continuousOn_endpoint_positive_or_exists_zero
      (g := fun x => -g x) hab hg.neg (by simpa using neg_pos.mpr hga)
  rcases hpos_or_zero with hneg | hzero
  · exact Or.inl (by
      intro x hx
      have hxneg := hneg x hx
      linarith)
  · rcases hzero with ⟨c, hc, hc_zero⟩
    exact Or.inr ⟨c, hc, by linarith⟩

/--
First-hit version of the positive endpoint stopping dichotomy.  If a continuous
sign proxy is positive at the left endpoint, then either it stays positive on
the whole closed interval or there is a first zero; before that zero, the proxy
is strictly positive.
-/
theorem continuousOn_endpoint_positive_or_first_zero
    {g : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hg : ContinuousOn g (Icc a b))
    (hga : 0 < g a) :
    (∀ x ∈ Icc a b, 0 < g x) ∨
      ∃ c ∈ Ioc a b, g c = 0 ∧
        ∀ x ∈ Ico a c, 0 < g x := by
  by_cases hpos : ∀ x ∈ Icc a b, 0 < g x
  · exact Or.inl hpos
  · refine Or.inr ?_
    have hzero_exists :
        ∃ z ∈ Icc a b, g z = 0 := by
      rcases continuousOn_endpoint_positive_or_exists_zero hab hg hga with hglobal | hzero
      · exact False.elim (hpos hglobal)
      · exact hzero
    let zeroSet : Set ℝ := {z | z ∈ Icc a b ∧ g z = 0}
    have hzeroSet_nonempty : zeroSet.Nonempty := by
      rcases hzero_exists with ⟨z, hz, hgz⟩
      exact ⟨z, ⟨hz, hgz⟩⟩
    have hclosed_pre :
        IsClosed (Icc a b ∩ g ⁻¹' ({0} : Set ℝ)) :=
      hg.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
    have hzeroSet_closed : IsClosed zeroSet := by
      simpa [zeroSet, Set.preimage, Set.inter_def, Set.mem_setOf_eq] using hclosed_pre
    have hzeroSet_bddBelow : BddBelow zeroSet := by
      exact ⟨a, by
        intro z hz
        exact hz.1.1⟩
    let c : ℝ := sInf zeroSet
    have hc_least : IsLeast zeroSet c :=
      hzeroSet_closed.isLeast_csInf hzeroSet_nonempty hzeroSet_bddBelow
    have hc_mem : c ∈ zeroSet := hc_least.1
    have hac : a < c := by
      have hac_le : a ≤ c := hc_mem.1.1
      refine lt_of_le_of_ne hac_le ?_
      intro hac_eq
      have hga_zero : g a = 0 := by
        simpa [hac_eq] using hc_mem.2
      linarith
    have hcb : c ≤ b := hc_mem.1.2
    have hgc : g c = 0 := hc_mem.2
    have hprefix : ∀ x ∈ Ico a c, 0 < g x := by
      intro x hx
      by_contra hx_not_pos
      have hx_nonpos : g x ≤ 0 := le_of_not_gt hx_not_pos
      have hax : a ≤ x := hx.1
      have hxb : x ≤ b := (le_of_lt hx.2).trans hcb
      have hg_ax : ContinuousOn g (Icc a x) :=
        hg.mono (Icc_subset_Icc_right hxb)
      have hzero_between : (0 : ℝ) ∈ Icc (g x) (g a) :=
        ⟨hx_nonpos, le_of_lt hga⟩
      rcases intermediate_value_Icc' hax hg_ax hzero_between with
        ⟨z, hz, hgz⟩
      have hz_mem : z ∈ zeroSet :=
        ⟨⟨hz.1, hz.2.trans hxb⟩, hgz⟩
      have hcz : c ≤ z := hc_least.2 hz_mem
      exact (not_lt_of_ge (hcz.trans hz.2)) hx.2
    exact ⟨c, ⟨hac, hcb⟩, hgc, hprefix⟩

/-- First-hit version of the negative endpoint stopping dichotomy. -/
theorem continuousOn_endpoint_negative_or_first_zero
    {g : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hg : ContinuousOn g (Icc a b))
    (hga : g a < 0) :
    (∀ x ∈ Icc a b, g x < 0) ∨
      ∃ c ∈ Ioc a b, g c = 0 ∧
        ∀ x ∈ Ico a c, g x < 0 := by
  have hpos_or_first :=
    continuousOn_endpoint_positive_or_first_zero
      (g := fun x => -g x) hab hg.neg (by simpa using neg_pos.mpr hga)
  rcases hpos_or_first with hglobal | hfirst
  · exact Or.inl (by
      intro x hx
      have hxneg := hglobal x hx
      linarith)
  · rcases hfirst with ⟨c, hc, hc_zero, hprefix⟩
    exact Or.inr ⟨c, hc, by linarith, by
      intro x hx
      have hxneg := hprefix x hx
      linarith⟩

/--
Endpoint-path stopping lemma for a positive derivative proxy.  If the
derivative is positive at the left endpoint, then either the full endpoint move
strictly improves the path, or the path strictly improves up to the first zero
of the derivative proxy.
-/
theorem endpoint_path_lt_or_first_zero_of_derivative_pos_at_left
    {f f' : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hf : ContinuousOn f (Icc a b))
    (hf' : ContinuousOn f' (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hderiv_a_pos : 0 < f' a) :
    (f a < f b ∧ ∀ x ∈ Icc a b, 0 < f' x) ∨
      ∃ c ∈ Ioc a b, f' c = 0 ∧
        f a < f c ∧ ∀ x ∈ Ico a c, 0 < f' x := by
  rcases continuousOn_endpoint_positive_or_first_zero
      (g := f') hab.le hf' hderiv_a_pos with hglobal | hfirst
  · refine Or.inl ⟨?_, hglobal⟩
    exact
      endpoint_path_lt_of_hasDerivAt_pos_on_Icc hab hf hderiv
        (by
          intro x hx
          exact hglobal x ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
  · rcases hfirst with ⟨c, hc, hfc_zero, hprefix⟩
    refine Or.inr ⟨c, hc, hfc_zero, ?_, hprefix⟩
    have hf_ac : ContinuousOn f (Icc a c) :=
      hf.mono (Icc_subset_Icc_right hc.2)
    have hderiv_ac :
        ∀ x ∈ Ioo a c, HasDerivAt f (f' x) x := by
      intro x hx
      exact hderiv x ⟨hx.1, hx.2.trans_le hc.2⟩
    have hpos_ac : ∀ x ∈ Ioo a c, 0 < f' x := by
      intro x hx
      exact hprefix x ⟨le_of_lt hx.1, hx.2⟩
    exact
      endpoint_path_lt_of_hasDerivAt_pos_on_Icc
        hc.1 hf_ac hderiv_ac hpos_ac

/-- Endpoint-path stopping lemma for a negative derivative proxy. -/
theorem endpoint_path_gt_or_first_zero_of_derivative_neg_at_left
    {f f' : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hf : ContinuousOn f (Icc a b))
    (hf' : ContinuousOn f' (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hderiv_a_neg : f' a < 0) :
    (f b < f a ∧ ∀ x ∈ Icc a b, f' x < 0) ∨
      ∃ c ∈ Ioc a b, f' c = 0 ∧
        f c < f a ∧ ∀ x ∈ Ico a c, f' x < 0 := by
  rcases continuousOn_endpoint_negative_or_first_zero
      (g := f') hab.le hf' hderiv_a_neg with hglobal | hfirst
  · refine Or.inl ⟨?_, hglobal⟩
    exact
      endpoint_path_gt_of_hasDerivAt_neg_on_Icc hab hf hderiv
        (by
          intro x hx
          exact hglobal x ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
  · rcases hfirst with ⟨c, hc, hfc_zero, hprefix⟩
    refine Or.inr ⟨c, hc, hfc_zero, ?_, hprefix⟩
    have hf_ac : ContinuousOn f (Icc a c) :=
      hf.mono (Icc_subset_Icc_right hc.2)
    have hderiv_ac :
        ∀ x ∈ Ioo a c, HasDerivAt f (f' x) x := by
      intro x hx
      exact hderiv x ⟨hx.1, hx.2.trans_le hc.2⟩
    have hneg_ac : ∀ x ∈ Ioo a c, f' x < 0 := by
      intro x hx
      exact hprefix x ⟨le_of_lt hx.1, hx.2⟩
    exact
      endpoint_path_gt_of_hasDerivAt_neg_on_Icc
        hc.1 hf_ac hderiv_ac hneg_ac

/--
Right-endpoint stopping dichotomy for a negative sign proxy.  If the proxy is
negative at the right endpoint, then either it is negative on the whole closed
interval or it has a last zero; after that zero, the proxy is strictly negative.
-/
theorem continuousOn_endpoint_negative_or_last_zero
    {g : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hg : ContinuousOn g (Icc a b))
    (hgb : g b < 0) :
    (∀ x ∈ Icc a b, g x < 0) ∨
      ∃ c ∈ Ico a b, g c = 0 ∧
        ∀ x ∈ Ioc c b, g x < 0 := by
  by_cases hneg : ∀ x ∈ Icc a b, g x < 0
  · exact Or.inl hneg
  · refine Or.inr ?_
    have hzero_exists :
        ∃ z ∈ Icc a b, g z = 0 := by
      push Not at hneg
      rcases hneg with ⟨x, hx, hx_nonneg⟩
      have hg_xb : ContinuousOn g (Icc x b) :=
        hg.mono (Icc_subset_Icc_left hx.1)
      have hzero_between : (0 : ℝ) ∈ Icc (g b) (g x) :=
        ⟨le_of_lt hgb, hx_nonneg⟩
      rcases intermediate_value_Icc' hx.2 hg_xb hzero_between with
        ⟨z, hz, hgz⟩
      exact ⟨z, ⟨hx.1.trans hz.1, hz.2⟩, hgz⟩
    let zeroSet : Set ℝ := {z | z ∈ Icc a b ∧ g z = 0}
    have hzeroSet_nonempty : zeroSet.Nonempty := by
      rcases hzero_exists with ⟨z, hz, hgz⟩
      exact ⟨z, ⟨hz, hgz⟩⟩
    have hclosed_pre :
        IsClosed (Icc a b ∩ g ⁻¹' ({0} : Set ℝ)) :=
      hg.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
    have hzeroSet_closed : IsClosed zeroSet := by
      simpa [zeroSet, Set.preimage, Set.inter_def, Set.mem_setOf_eq] using hclosed_pre
    have hzeroSet_bddAbove : BddAbove zeroSet := by
      exact ⟨b, by
        intro z hz
        exact hz.1.2⟩
    let c : ℝ := sSup zeroSet
    have hc_greatest : IsGreatest zeroSet c :=
      hzeroSet_closed.isGreatest_csSup hzeroSet_nonempty hzeroSet_bddAbove
    have hc_mem : c ∈ zeroSet := hc_greatest.1
    have hac : a ≤ c := hc_mem.1.1
    have hcb : c < b := by
      have hcb_le : c ≤ b := hc_mem.1.2
      refine lt_of_le_of_ne hcb_le ?_
      intro hcb_eq
      have hgb_zero : g b = 0 := by
        simpa [hcb_eq] using hc_mem.2
      linarith
    have hgc : g c = 0 := hc_mem.2
    have hsuffix : ∀ x ∈ Ioc c b, g x < 0 := by
      intro x hx
      by_contra hx_not_neg
      have hx_nonneg : 0 ≤ g x := le_of_not_gt hx_not_neg
      have hxb : x ≤ b := hx.2
      have hax : a ≤ x := hac.trans (le_of_lt hx.1)
      have hg_xb : ContinuousOn g (Icc x b) :=
        hg.mono (Icc_subset_Icc_left hax)
      have hzero_between : (0 : ℝ) ∈ Icc (g b) (g x) :=
        ⟨le_of_lt hgb, hx_nonneg⟩
      rcases intermediate_value_Icc' hxb hg_xb hzero_between with
        ⟨z, hz, hgz⟩
      have hz_mem : z ∈ zeroSet :=
        ⟨⟨hax.trans hz.1, hz.2⟩, hgz⟩
      have hzc : z ≤ c := hc_greatest.2 hz_mem
      exact (not_lt_of_ge (hz.1.trans hzc)) hx.1
    exact ⟨c, ⟨hac, hcb⟩, hgc, hsuffix⟩

/--
Endpoint-path stopping lemma for a negative derivative proxy at the right
endpoint.
-/
theorem endpoint_path_gt_or_last_zero_of_derivative_neg_at_right
    {f f' : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hf : ContinuousOn f (Icc a b))
    (hf' : ContinuousOn f' (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hderiv_b_neg : f' b < 0) :
    (f b < f a ∧ ∀ x ∈ Icc a b, f' x < 0) ∨
      ∃ c ∈ Ico a b, f' c = 0 ∧
        f b < f c ∧ ∀ x ∈ Ioc c b, f' x < 0 := by
  rcases continuousOn_endpoint_negative_or_last_zero
      (g := f') hab.le hf' hderiv_b_neg with hglobal | hlast
  · refine Or.inl ⟨?_, hglobal⟩
    exact
      endpoint_path_gt_of_hasDerivAt_neg_on_Icc hab hf hderiv
        (by
          intro x hx
          exact hglobal x ⟨le_of_lt hx.1, le_of_lt hx.2⟩)
  · rcases hlast with ⟨c, hc, hfc_zero, hsuffix⟩
    refine Or.inr ⟨c, hc, hfc_zero, ?_, hsuffix⟩
    have hf_cb : ContinuousOn f (Icc c b) :=
      hf.mono (Icc_subset_Icc_left hc.1)
    have hderiv_cb :
        ∀ x ∈ Ioo c b, HasDerivAt f (f' x) x := by
      intro x hx
      exact hderiv x ⟨hc.1.trans_lt hx.1, hx.2⟩
    have hneg_cb : ∀ x ∈ Ioo c b, f' x < 0 := by
      intro x hx
      exact hsuffix x ⟨hx.1, le_of_lt hx.2⟩
    exact
      endpoint_path_gt_of_hasDerivAt_neg_on_Icc
        hc.2 hf_cb hderiv_cb hneg_cb

/-- A positive derivative at an endpoint gives a positive right move with larger value. -/
theorem exists_pos_right_improvement_of_hasDerivAt_pos
    {f : ℝ → ℝ} {x derivativeValue : ℝ}
    (hderiv : HasDerivAt f derivativeValue x)
    (hpos : 0 < derivativeValue) :
    ∃ ε : ℝ, 0 < ε ∧ f x < f (x + ε) := by
  have hslope_pos :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        0 < ε⁻¹ * (f (x + ε) - f x) := by
    simpa using
      hderiv.tendsto_slope_zero_right.eventually (Ioi_mem_nhds hpos)
  have hε_pos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε :=
    self_mem_nhdsWithin
  rcases (hε_pos.and hslope_pos).exists with ⟨ε, hε, hslope⟩
  have hdiff_pos : 0 < f (x + ε) - f x := by
    rw [mul_comm] at hslope
    exact pos_of_mul_pos_left hslope (le_of_lt (inv_pos.mpr hε))
  exact ⟨ε, hε, by linarith⟩

/-- Bounded positive right-improvement step. -/
theorem exists_pos_right_improvement_of_hasDerivAt_pos_lt
    {f : ℝ → ℝ} {x derivativeValue δ : ℝ}
    (hderiv : HasDerivAt f derivativeValue x)
    (hpos : 0 < derivativeValue)
    (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ f x < f (x + ε) := by
  have hslope_pos :
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        0 < ε⁻¹ * (f (x + ε) - f x) := by
    simpa using
      hderiv.tendsto_slope_zero_right.eventually (Ioi_mem_nhds hpos)
  have hε_pos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε :=
    self_mem_nhdsWithin
  have hε_lt : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < δ :=
    nhdsWithin_le_nhds (Iio_mem_nhds hδ)
  rcases (hε_pos.and (hε_lt.and hslope_pos)).exists with
    ⟨ε, hε, hε_lt, hslope⟩
  have hdiff_pos : 0 < f (x + ε) - f x := by
    rw [mul_comm] at hslope
    exact pos_of_mul_pos_left hslope (le_of_lt (inv_pos.mpr hε))
  exact ⟨ε, hε, hε_lt, by linarith⟩

/-- A negative derivative at an endpoint gives a positive right move with smaller value. -/
theorem exists_pos_right_decrease_of_hasDerivAt_neg
    {f : ℝ → ℝ} {x derivativeValue : ℝ}
    (hderiv : HasDerivAt f derivativeValue x)
    (hneg : derivativeValue < 0) :
    ∃ ε : ℝ, 0 < ε ∧ f (x + ε) < f x := by
  have hpos : 0 < -derivativeValue := by linarith
  rcases exists_pos_right_improvement_of_hasDerivAt_pos
      (f := fun y => -f y) (x := x) (derivativeValue := -derivativeValue)
      hderiv.neg hpos with
    ⟨ε, hε_pos, hlt⟩
  exact ⟨ε, hε_pos, by linarith⟩

/-- Bounded positive right-decrease step. -/
theorem exists_pos_right_decrease_of_hasDerivAt_neg_lt
    {f : ℝ → ℝ} {x derivativeValue δ : ℝ}
    (hderiv : HasDerivAt f derivativeValue x)
    (hneg : derivativeValue < 0)
    (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ f (x + ε) < f x := by
  have hpos : 0 < -derivativeValue := by linarith
  rcases exists_pos_right_improvement_of_hasDerivAt_pos_lt
      (f := fun y => -f y) (x := x) (derivativeValue := -derivativeValue)
      hderiv.neg hpos hδ with
    ⟨ε, hε_pos, hε_lt, hlt⟩
  exact ⟨ε, hε_pos, hε_lt, by linarith⟩

/--
Left-move improvement step: with a negative derivative, moving a small positive
distance to the left strictly improves the function value.
-/
theorem exists_pos_left_improvement_of_hasDerivAt_neg
    {f : ℝ → ℝ} {x derivativeValue : ℝ}
    (hderiv : HasDerivAt f derivativeValue x)
    (hneg : derivativeValue < 0) :
    ∃ ε : ℝ, 0 < ε ∧ f x < f (x - ε) := by
  have hslope_neg :
      ∀ᶠ t in 𝓝[<] (0 : ℝ),
        t⁻¹ * (f (x + t) - f x) < 0 := by
    simpa using
      hderiv.tendsto_slope_zero_left.eventually (Iio_mem_nhds hneg)
  have ht_neg : ∀ᶠ t in 𝓝[<] (0 : ℝ), t < 0 :=
    self_mem_nhdsWithin
  rcases (ht_neg.and hslope_neg).exists with ⟨t, ht, hslope⟩
  have hε_pos : 0 < -t := by linarith
  have hdiff_pos : 0 < f (x + t) - f x := by
    rw [mul_comm] at hslope
    exact pos_of_mul_neg_left hslope (inv_nonpos.mpr (le_of_lt ht))
  exact ⟨-t, hε_pos, by simpa [sub_eq_add_neg] using hdiff_pos⟩

/-- Bounded left-move improvement step. -/
theorem exists_pos_left_improvement_of_hasDerivAt_neg_lt
    {f : ℝ → ℝ} {x derivativeValue δ : ℝ}
    (hderiv : HasDerivAt f derivativeValue x)
    (hneg : derivativeValue < 0)
    (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ f x < f (x - ε) := by
  have hslope_neg :
      ∀ᶠ t in 𝓝[<] (0 : ℝ),
        t⁻¹ * (f (x + t) - f x) < 0 := by
    simpa using
      hderiv.tendsto_slope_zero_left.eventually (Iio_mem_nhds hneg)
  have ht_neg : ∀ᶠ t in 𝓝[<] (0 : ℝ), t < 0 :=
    self_mem_nhdsWithin
  have ht_gt : ∀ᶠ t in 𝓝[<] (0 : ℝ), -δ < t :=
    nhdsWithin_le_nhds (Ioi_mem_nhds (by linarith))
  rcases (ht_neg.and (ht_gt.and hslope_neg)).exists with
    ⟨t, ht, ht_gt, hslope⟩
  have hε_pos : 0 < -t := by linarith
  have hε_lt : -t < δ := by linarith
  have hdiff_pos : 0 < f (x + t) - f x := by
    rw [mul_comm] at hslope
    exact pos_of_mul_neg_left hslope (inv_nonpos.mpr (le_of_lt ht))
  exact ⟨-t, hε_pos, hε_lt, by simpa [sub_eq_add_neg] using hdiff_pos⟩

/--
Left-move decrease step: with a positive derivative, moving a small positive
distance to the left strictly decreases the function value.
-/
theorem exists_pos_left_decrease_of_hasDerivAt_pos
    {f : ℝ → ℝ} {x derivativeValue : ℝ}
    (hderiv : HasDerivAt f derivativeValue x)
    (hpos : 0 < derivativeValue) :
    ∃ ε : ℝ, 0 < ε ∧ f (x - ε) < f x := by
  have hneg : -derivativeValue < 0 := by linarith
  rcases exists_pos_left_improvement_of_hasDerivAt_neg
      (f := fun y => -f y) (x := x) (derivativeValue := -derivativeValue)
      hderiv.neg hneg with
    ⟨ε, hε_pos, hlt⟩
  exact ⟨ε, hε_pos, by linarith⟩

/-- Bounded left-move decrease step. -/
theorem exists_pos_left_decrease_of_hasDerivAt_pos_lt
    {f : ℝ → ℝ} {x derivativeValue δ : ℝ}
    (hderiv : HasDerivAt f derivativeValue x)
    (hpos : 0 < derivativeValue)
    (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ f (x - ε) < f x := by
  have hneg : -derivativeValue < 0 := by linarith
  rcases exists_pos_left_improvement_of_hasDerivAt_neg_lt
      (f := fun y => -f y) (x := x) (derivativeValue := -derivativeValue)
      hderiv.neg hneg hδ with
    ⟨ε, hε_pos, hε_lt, hlt⟩
  exact ⟨ε, hε_pos, hε_lt, by linarith⟩

/--
A continuous objective on a compact interval has an interior global maximizer
when its derivative is positive at the left endpoint and negative at the right
endpoint.  The endpoint derivative signs provide strict inward improvements,
so neither endpoint can be a maximizer.

Upstream credit: the proof directly uses Mathlib's `isCompact_Icc` and
`IsCompact.exists_isMaxOn` from
[`Topology/Order/Compact.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Topology/Order/Compact.lean),
at the pinned Apache-2.0 Mathlib revision.  No external code is copied or
ported.
-/
theorem exists_interior_maximizer_of_endpoint_derivative_signs
    {f : ℝ → ℝ} {lo hi dLo dHi : ℝ}
    (hlohi : lo < hi)
    (hcont : ContinuousOn f (Icc lo hi))
    (hderiv_lo : HasDerivAt f dLo lo)
    (hdLo_pos : 0 < dLo)
    (hderiv_hi : HasDerivAt f dHi hi)
    (hdHi_neg : dHi < 0) :
    ∃ maximizer ∈ Ioo lo hi,
      ∀ y ∈ Icc lo hi, f y ≤ f maximizer := by
  rcases isCompact_Icc.exists_isMaxOn
      ⟨lo, le_rfl, hlohi.le⟩ hcont with
    ⟨maximizer, hmaximizer, hmax⟩
  have hmaximizer_ne_lo : maximizer ≠ lo := by
    intro heq
    rcases exists_pos_right_improvement_of_hasDerivAt_pos_lt
        (δ := hi - lo) hderiv_lo hdLo_pos (by linarith) with
      ⟨ε, hε_pos, hε_lt, himprove⟩
    have hpoint : lo + ε ∈ Icc lo hi := by
      constructor <;> linarith
    have hbound := hmax hpoint
    rw [heq] at hbound
    exact (not_lt_of_ge hbound) himprove
  have hmaximizer_ne_hi : maximizer ≠ hi := by
    intro heq
    rcases exists_pos_left_improvement_of_hasDerivAt_neg_lt
        (δ := hi - lo) hderiv_hi hdHi_neg (by linarith) with
      ⟨ε, hε_pos, hε_lt, himprove⟩
    have hpoint : hi - ε ∈ Icc lo hi := by
      constructor <;> linarith
    have hbound := hmax hpoint
    rw [heq] at hbound
    exact (not_lt_of_ge hbound) himprove
  refine ⟨maximizer, ?_, ?_⟩
  · exact ⟨lt_of_le_of_ne hmaximizer.1 hmaximizer_ne_lo.symm,
      lt_of_le_of_ne hmaximizer.2 hmaximizer_ne_hi⟩
  · intro y hy
    exact hmax hy

end Optimization
end AppliedModelingLib

/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the repository LICENSE.
Authors: Daniel Lyng

This file is a narrow port of the local integration-by-parts result from
https://github.com/danlyng/Econlib/blob/003655ccf010cdf44c4f67d6675167b54ce0e9df/Econlib/Math/MeasureTheory/StieltjesIBP.lean
(Apache-2.0).  It was adapted to this repository's Lean 4.30.0-rc2 / pinned
Mathlib environment; the upstream project pins Lean 4.29.  The original
copyright and Apache-2.0 notice are retained.  No other Econlib declarations
or dependencies are imported.
-/

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Stieltjes

/-!
# Local Stieltjes integration by parts

For monotone real functions `F` and `u`, their right-continuous Stieltjes
regularizations satisfy an integration-by-parts formula on `(a, b]`.  This is
the measure-theoretic bridge needed to turn a CDF expression into the
derivative/CDF integral used in continuous stochastic-dominance arguments.

Upstream credit and license are recorded in the file header.  The port is
checked in this repository rather than trusted by source inspection alone.
-/

open Set Filter MeasureTheory Function
open scoped Topology

namespace Monotone

/-- The Stieltjes function induced by a monotone function via right limits. -/
noncomputable abbrev stieltjes {f : ℝ → ℝ} (hf : Monotone f) : StieltjesFunction ℝ :=
  hf.stieltjesFunction

/-- The Stieltjes measure induced by a monotone function via right limits. -/
noncomputable abbrev stieltjesMeasure {f : ℝ → ℝ} (hf : Monotone f) : Measure ℝ :=
  hf.stieltjesFunction.measure

end Monotone

namespace MeasureTheory

variable {F u : ℝ → ℝ} (hF : Monotone F) (hu : Monotone u) (a b : ℝ)

/--
Local integration by parts for Stieltjes measures on `(a, b]`.  The CDF-side
integrand is right-continuous, while the cost-side integrand is its left limit,
which accounts correctly for atoms.
-/
theorem stieltjes_ibp_local (hab : a < b) :
    let F_sf := hF.stieltjes
    let u_sf := hu.stieltjes
    let μ_F := hF.stieltjesMeasure
    let μ_u := hu.stieltjesMeasure
    ∫ y in Ioc a b, F_sf y ∂μ_u + ∫ x in Ioc a b, leftLim (⇑u_sf) x ∂μ_F =
    F_sf b * u_sf b - F_sf a * u_sf a := by
  intro F_sf u_sf μ_F μ_u
  have h_fubini_swap : ∫ y in Ioc a b, ∫ x in Ioc a y, (1 : ℝ) ∂μ_F ∂μ_u =
                       ∫ x in Ioc a b, ∫ y in Icc x b, (1 : ℝ) ∂μ_u ∂μ_F := by
    simp_rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
    have h_meas_F : AEMeasurable (fun y => μ_F (Ioc a y)) (μ_u.restrict (Ioc a b)) := by
      rw [show (fun y => μ_F (Ioc a y)) = fun y => ENNReal.ofReal (F_sf y - F_sf a) from
        funext (fun y => F_sf.measure_Ioc a y)]
      exact (F_sf.mono.measurable.sub measurable_const).ennreal_ofReal.aemeasurable
    have h_meas_u : AEMeasurable (fun x => μ_u (Icc x b)) (μ_F.restrict (Ioc a b)) := by
      rw [show (fun x => μ_u (Icc x b)) = fun x => ENNReal.ofReal (u_sf b - leftLim (⇑u_sf) x)
        from funext (fun x => u_sf.measure_Icc x b)]
      exact (measurable_const.sub u_sf.mono.leftLim.measurable).ennreal_ofReal.aemeasurable
    rw [integral_toReal h_meas_F
          (ae_of_all _ fun y => by rw [F_sf.measure_Ioc]; exact ENNReal.ofReal_lt_top),
        integral_toReal h_meas_u
          (ae_of_all _ fun x => by rw [u_sf.measure_Icc]; exact ENNReal.ofReal_lt_top)]
    congr 1
    set T : Set (ℝ × ℝ) := {p | a < p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b}
    have hT : MeasurableSet T :=
      (measurableSet_lt measurable_const measurable_fst).inter
        ((measurableSet_le measurable_fst measurable_snd).inter
          (measurableSet_le measurable_snd measurable_const))
    have sect_x : ∀ x, Prod.mk x ⁻¹' T = if x ∈ Ioc a b then Icc x b else ∅ := by
      intro x
      ext y
      simp only [T, mem_preimage, mem_setOf_eq, mem_Ioc]
      split
      · next h => exact ⟨fun ⟨_, hxy, hyb⟩ => ⟨hxy, hyb⟩,
          fun ⟨hxy, hyb⟩ => ⟨h.1, hxy, hyb⟩⟩
      · next h => exact ⟨fun ⟨hax, hxy, hyb⟩ =>
          absurd ⟨hax, le_trans hxy hyb⟩ h, False.elim⟩
    have sect_y : ∀ y, Prod.mk y ⁻¹' (Prod.swap ⁻¹' T) =
        if y ∈ Ioc a b then Ioc a y else ∅ := by
      intro y
      ext x
      simp only [T, mem_preimage, Prod.swap, mem_setOf_eq, mem_Ioc]
      split
      · next h => exact ⟨fun ⟨hax, hxy, _⟩ => ⟨hax, hxy⟩,
          fun ⟨hax, hxy⟩ => ⟨hax, hxy, h.2⟩⟩
      · next h => exact ⟨fun ⟨hax, hxy, hyb⟩ =>
          absurd ⟨lt_of_lt_of_le hax hxy, hyb⟩ h, False.elim⟩
    have hRHS : (μ_F.prod μ_u) T = ∫⁻ x in Ioc a b, μ_u (Icc x b) ∂μ_F := by
      rw [Measure.prod_apply hT, ← lintegral_indicator measurableSet_Ioc]
      apply lintegral_congr
      intro x
      simp only [sect_x]
      split <;> simp [indicator_of_mem, indicator_of_notMem, *]
    have hLHS : (μ_u.prod μ_F) (Prod.swap ⁻¹' T) =
        ∫⁻ y in Ioc a b, μ_F (Ioc a y) ∂μ_u := by
      rw [Measure.prod_apply (hT.preimage measurable_swap),
          ← lintegral_indicator measurableSet_Ioc]
      apply lintegral_congr
      intro y
      simp only [sect_y]
      split <;> simp [indicator_of_mem, indicator_of_notMem, *]
    have hSwap : (μ_u.prod μ_F) (Prod.swap ⁻¹' T) = (μ_F.prod μ_u) T := by
      rw [show μ_u.prod μ_F = (μ_F.prod μ_u).map Prod.swap from Measure.prod_swap.symm,
          Measure.map_apply measurable_swap (hT.preimage measurable_swap)]
      congr 1
    rw [← hLHS, hSwap, hRHS]
  have h_inner_x : ∀ y ∈ Ioc a b, ∫ x in Ioc a y, (1 : ℝ) ∂μ_F = F_sf y - F_sf a := by
    intro y hy
    rw [setIntegral_const, smul_eq_mul, mul_one]
    change (F_sf.measure (Ioc a y)).toReal = _
    rw [StieltjesFunction.measure_Ioc]
    exact ENNReal.toReal_ofReal (sub_nonneg.mpr (F_sf.mono (le_of_lt hy.1)))
  have h_inner_y : ∀ x ∈ Ioc a b, ∫ y in Icc x b, (1 : ℝ) ∂μ_u =
      u_sf b - leftLim (⇑u_sf) x := by
    intro x hx
    rw [setIntegral_const, smul_eq_mul, mul_one]
    change (u_sf.measure (Icc x b)).toReal = _
    rw [StieltjesFunction.measure_Icc]
    exact ENNReal.toReal_ofReal (sub_nonneg.mpr (Monotone.leftLim_le u_sf.mono hx.2))
  have h_sub : ∫ y in Ioc a b, (F_sf y - F_sf a) ∂μ_u =
      ∫ x in Ioc a b, (u_sf b - leftLim (⇑u_sf) x) ∂μ_F := by
    have lhs_eq : ∫ y in Ioc a b, (F_sf y - F_sf a) ∂μ_u =
        ∫ y in Ioc a b, ∫ x in Ioc a y, (1 : ℝ) ∂μ_F ∂μ_u :=
      setIntegral_congr_fun measurableSet_Ioc (fun y hy => (h_inner_x y hy).symm)
    have rhs_eq : ∫ x in Ioc a b, ∫ y in Icc x b, (1 : ℝ) ∂μ_u ∂μ_F =
        ∫ x in Ioc a b, (u_sf b - leftLim (⇑u_sf) x) ∂μ_F :=
      setIntegral_congr_fun measurableSet_Ioc (fun x hx => h_inner_y x hx)
    exact lhs_eq.trans (h_fubini_swap.trans rhs_eq)
  have h_fin_u : μ_u (Ioc a b) ≠ ⊤ := by
    change u_sf.measure (Ioc a b) ≠ ⊤
    simp [StieltjesFunction.measure_Ioc, ENNReal.ofReal_ne_top]
  have h_fin_F : μ_F (Ioc a b) ≠ ⊤ := by
    change F_sf.measure (Ioc a b) ≠ ⊤
    simp [StieltjesFunction.measure_Ioc, ENNReal.ofReal_ne_top]
  have h_int_const_Fa : IntegrableOn (fun _ => F_sf a) (Ioc a b) μ_u :=
    integrableOn_const h_fin_u
  have h_int_const_ub : IntegrableOn (fun _ => u_sf b) (Ioc a b) μ_F :=
    integrableOn_const h_fin_F
  have h_int_Fsf : IntegrableOn (⇑F_sf) (Ioc a b) μ_u := by
    refine Measure.integrableOn_of_bounded (M := max |F_sf a| |F_sf b|)
      h_fin_u F_sf.mono.measurable.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun x hx => ?_)
    simp only [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [F_sf.mono (le_of_lt hx.1), neg_abs_le (F_sf a),
                         le_max_left |F_sf a| |F_sf b|],
           by linarith [F_sf.mono hx.2, le_abs_self (F_sf b),
                         le_max_right |F_sf a| |F_sf b|]⟩
  have h_int_ulc : IntegrableOn (leftLim (⇑u_sf)) (Ioc a b) μ_F := by
    refine Measure.integrableOn_of_bounded (M := max |u_sf a| |u_sf b|)
      h_fin_F (u_sf.mono.leftLim.measurable.aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun x hx => ?_)
    simp only [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [u_sf.mono.le_leftLim hx.1, neg_abs_le (u_sf a),
                         le_max_left |u_sf a| |u_sf b|],
           by linarith [Monotone.leftLim_le u_sf.mono hx.2, le_abs_self (u_sf b),
                         le_max_right |u_sf a| |u_sf b|]⟩
  have h_measureReal_u : μ_u.real (Ioc a b) = u_sf b - u_sf a := by
    rw [measureReal_def]
    change (u_sf.measure (Ioc a b)).toReal = _
    rw [StieltjesFunction.measure_Ioc]
    exact ENNReal.toReal_ofReal (sub_nonneg.mpr (u_sf.mono (le_of_lt hab)))
  have h_measureReal_F : μ_F.real (Ioc a b) = F_sf b - F_sf a := by
    rw [measureReal_def]
    change (F_sf.measure (Ioc a b)).toReal = _
    rw [StieltjesFunction.measure_Ioc]
    exact ENNReal.toReal_ofReal (sub_nonneg.mpr (F_sf.mono (le_of_lt hab)))
  have h_const_Fa : ∫ y in Ioc a b, (fun _ => F_sf a) y ∂μ_u =
      F_sf a * (u_sf b - u_sf a) := by
    rw [setIntegral_const, smul_eq_mul, mul_comm, h_measureReal_u]
  have h_const_ub : ∫ x in Ioc a b, (fun _ => u_sf b) x ∂μ_F =
      u_sf b * (F_sf b - F_sf a) := by
    rw [setIntegral_const, smul_eq_mul, mul_comm, h_measureReal_F]
  have h_LHS : ∫ y in Ioc a b, (F_sf y - F_sf a) ∂μ_u =
      (∫ y in Ioc a b, F_sf y ∂μ_u) - F_sf a * (u_sf b - u_sf a) := by
    rw [integral_sub h_int_Fsf h_int_const_Fa, h_const_Fa]
  have h_RHS : ∫ x in Ioc a b, (u_sf b - leftLim (⇑u_sf) x) ∂μ_F =
      u_sf b * (F_sf b - F_sf a) - ∫ x in Ioc a b, leftLim (⇑u_sf) x ∂μ_F := by
    rw [integral_sub h_int_const_ub h_int_ulc, h_const_ub]
  linarith

end MeasureTheory

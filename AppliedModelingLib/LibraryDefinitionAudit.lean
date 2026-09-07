import AppliedModelingLib.Applications.RatingSystems.BinaryRating
import AppliedModelingLib.Foundations.Math.QuasiConvex
import Mathlib.Analysis.Convex.Function

namespace AppliedModelingLib
namespace Statistics

/-!
# Reusable Definition Audit

This module contains build-checked equivalence tests for reusable definitions
whose names correspond to standard mathematical notions.  These lemmas are not
paper-facing results; they are audit targets that make definition drift fail at
Lean build time.

## Main declarations

- `jensenConvex_iff_convexOn_univ`
- `jensenConcave_iff_concaveOn_univ`
- `strictQuasiConvexOnPositive_iff_expected`
- `strictQuasiConcaveOnPositive_iff_expected`
-/

theorem jensenConvex_iff_convexOn_univ (f : ℝ → ℝ) :
    JensenConvex f ↔ ConvexOn ℝ Set.univ f := by
  constructor
  · intro hf
    refine ⟨convex_univ, ?_⟩
    intro x _hx y _hy a b ha hb hab
    have hb_eq : b = 1 - a := by linarith
    subst b
    simpa [smul_eq_mul] using hf x y a ha (by linarith)
  · intro hf x y lam hlam_nonneg hlam_le_one
    have h :=
      hf.2 (Set.mem_univ x) (Set.mem_univ y)
        hlam_nonneg (sub_nonneg.mpr hlam_le_one)
        (by ring : lam + (1 - lam) = (1 : ℝ))
    simpa [smul_eq_mul] using h

theorem jensenConcave_iff_concaveOn_univ (f : ℝ → ℝ) :
    JensenConcave f ↔ ConcaveOn ℝ Set.univ f := by
  constructor
  · intro hf
    refine ⟨convex_univ, ?_⟩
    intro x _hx y _hy a b ha hb hab
    have hb_eq : b = 1 - a := by linarith
    subst b
    simpa [smul_eq_mul] using hf x y a ha (by linarith)
  · intro hf x y lam hlam_nonneg hlam_le_one
    have h :=
      hf.2 (Set.mem_univ x) (Set.mem_univ y)
        hlam_nonneg (sub_nonneg.mpr hlam_le_one)
        (by ring : lam + (1 - lam) = (1 : ℝ))
    simpa [smul_eq_mul] using h

end Statistics

theorem strictQuasiConvexOnPositive_iff_expected (f : ℝ → ℝ) :
    StrictQuasiConvexOnPositive f ↔
      ∀ x y θ : ℝ, 0 < x → 0 < y → x ≠ y → 0 < θ → θ < 1 →
        f (θ * x + (1 - θ) * y) < max (f x) (f y) :=
  Iff.rfl

theorem strictQuasiConcaveOnPositive_iff_expected (f : ℝ → ℝ) :
    StrictQuasiConcaveOnPositive f ↔
      ∀ x y θ : ℝ, 0 < x → 0 < y → x ≠ y → 0 < θ → θ < 1 →
        min (f x) (f y) < f (θ * x + (1 - θ) * y) :=
  Iff.rfl

end AppliedModelingLib

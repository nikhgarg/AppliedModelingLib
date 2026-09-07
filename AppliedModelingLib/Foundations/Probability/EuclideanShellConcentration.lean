import AppliedModelingLib.Foundations.Probability.EuclideanDyadicShells
import AppliedModelingLib.Foundations.Probability.EuclideanEmpiricalWasserstein

/-!
# Dyadic-shell probability bounds

This module starts the probability side of the source's noncompact-shell
argument (Fournier--Guillin (2015), Notation 4(b), Lemma 13, and Section 6).
It converts the already proved exponential radial Markov estimate into a
per-shell bound, including the source half-open cube shells. It does not yet
sum shell errors or prove the source's transport/concentration result.

No external Lean source is copied or ported.  The proof reuses the local
checked `measureReal_norm_gt_le_exponentialRadialMoment_div` interface and
Mathlib's `measureReal_mono` from
[`MeasureTheory/Measure/Real.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/MeasureTheory/Measure/Real.lean)
at the pinned Apache-2.0 Mathlib commit
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`.
-/

namespace AppliedModelingLib
namespace Probability

open MeasureTheory

noncomputable section

/--
Every dyadic shell is bounded by the exponential radial Markov tail at its
inner radius.  This is the source's shell-mass entrance estimate before any
transport or concentration allocation is applied.
-/
theorem measureReal_euclideanDyadicShell_le_exponentialRadialMoment_div
    (dimension shell : ℕ)
    (law : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    {alpha gamma : ℝ} (halpha : 0 ≤ alpha) (hgamma : 0 ≤ gamma)
    (hmoment : HasExponentialRadialMoment law alpha gamma) :
    (law : Measure (EuclideanSpace ℝ (Fin dimension))).real
      (euclideanDyadicShell dimension shell) ≤
      ∫ x, Real.exp (gamma * Real.rpow ‖x‖ alpha) /
        Real.exp (gamma * Real.rpow (euclideanDyadicShellInnerRadius shell) alpha) ∂
          (law : Measure (EuclideanSpace ℝ (Fin dimension))) := by
  calc
    (law : Measure (EuclideanSpace ℝ (Fin dimension))).real
        (euclideanDyadicShell dimension shell) ≤
        (law : Measure (EuclideanSpace ℝ (Fin dimension))).real
          {x | euclideanDyadicShellInnerRadius shell < ‖x‖} := by
      exact measureReal_mono (fun x hx ↦ hx.1) (measure_ne_top _ _)
    _ ≤ ∫ x, Real.exp (gamma * Real.rpow ‖x‖ alpha) /
        Real.exp (gamma * Real.rpow (euclideanDyadicShellInnerRadius shell) alpha) ∂
          (law : Measure (EuclideanSpace ℝ (Fin dimension))) :=
      measureReal_norm_gt_le_exponentialRadialMoment_div law halpha hgamma
        (euclideanDyadicShellInnerRadius_pos shell).le hmoment

/--
Every noncentral source cube shell is bounded by the exponential radial
Markov tail at its preceding cube radius. This is the source-faithful shell
mass entrance estimate before shell transport or empirical concentration.
-/
theorem measureReal_euclideanDyadicCubeShell_succ_le_exponentialRadialMoment_div
    (dimension shell : ℕ)
    (law : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    {alpha gamma : ℝ} (halpha : 0 ≤ alpha) (hgamma : 0 ≤ gamma)
    (hmoment : HasExponentialRadialMoment law alpha gamma) :
    (law : Measure (EuclideanSpace ℝ (Fin dimension))).real
      (euclideanDyadicCubeShell dimension (shell + 1)) ≤
      ∫ x, Real.exp (gamma * Real.rpow ‖x‖ alpha) /
        Real.exp (gamma * Real.rpow (euclideanDyadicCubeRadius shell) alpha) ∂
          (law : Measure (EuclideanSpace ℝ (Fin dimension))) := by
  calc
    (law : Measure (EuclideanSpace ℝ (Fin dimension))).real
        (euclideanDyadicCubeShell dimension (shell + 1)) ≤
        (law : Measure (EuclideanSpace ℝ (Fin dimension))).real
          {x | euclideanDyadicCubeRadius shell ≤ ‖x‖} := by
      exact measureReal_mono (euclideanDyadicCubeShell_succ_subset_norm_ge dimension shell)
        (measure_ne_top _ _)
    _ ≤ ∫ x, Real.exp (gamma * Real.rpow ‖x‖ alpha) /
        Real.exp (gamma * Real.rpow (euclideanDyadicCubeRadius shell) alpha) ∂
          (law : Measure (EuclideanSpace ℝ (Fin dimension))) :=
      measureReal_norm_ge_le_exponentialRadialMoment_div law halpha hgamma
        (euclideanDyadicCubeRadius_pos shell).le hmoment

/--
The source cube-shell mass estimate with the recorded exponential moment and
an explicit exponentially decaying radius factor.  This is the form used in
the `z_n` allocation of Fournier--Guillin Section 6.
-/
theorem measureReal_euclideanDyadicCubeShell_succ_le_exponentialRadialMoment
    (dimension shell : ℕ)
    (law : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    {alpha gamma : ℝ} (halpha : 0 ≤ alpha) (hgamma : 0 ≤ gamma)
    (hmoment : HasExponentialRadialMoment law alpha gamma) :
    (law : Measure (EuclideanSpace ℝ (Fin dimension))).real
      (euclideanDyadicCubeShell dimension (shell + 1)) ≤
      Real.exp (-(gamma * Real.rpow (euclideanDyadicCubeRadius shell) alpha)) *
        ∫ x : EuclideanSpace ℝ (Fin dimension),
          Real.exp (gamma * Real.rpow ‖x‖ alpha) ∂
            (law : Measure (EuclideanSpace ℝ (Fin dimension))) := by
  calc
    (law : Measure (EuclideanSpace ℝ (Fin dimension))).real
        (euclideanDyadicCubeShell dimension (shell + 1)) ≤
        (law : Measure (EuclideanSpace ℝ (Fin dimension))).real
          {x | euclideanDyadicCubeRadius shell ≤ ‖x‖} := by
      exact measureReal_mono (euclideanDyadicCubeShell_succ_subset_norm_ge dimension shell)
        (measure_ne_top _ _)
    _ ≤ _ := measureReal_norm_ge_le_exponentialRadialMoment law halpha hgamma
      (euclideanDyadicCubeRadius_pos shell).le hmoment

/--
The source cube-shell exponential-moment estimate implies a fixed fifth-order
geometric shell-mass bound.  This records the `q = 5` polynomial consequence
of the exponential regime used to instantiate the `p = 1` shell allocation;
the sharper exponential form remains available above.
-/
theorem measureReal_euclideanDyadicCubeShell_succ_le_exponentialRadialMoment_fifthOrder
    (dimension shell : ℕ)
    (law : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    {alpha gamma : ℝ} (halpha : 1 ≤ alpha) (hgamma : 0 < gamma)
    (hmoment : HasExponentialRadialMoment law alpha gamma) :
    (law : Measure (EuclideanSpace ℝ (Fin dimension))).real
      (euclideanDyadicCubeShell dimension (shell + 1)) ≤
      (((5 : ℕ).factorial : ℝ) * gamma⁻¹ ^ 5 *
        ∫ x : EuclideanSpace ℝ (Fin dimension),
          Real.exp (gamma * Real.rpow ‖x‖ alpha) ∂
            (law : Measure (EuclideanSpace ℝ (Fin dimension)))) /
        (2 : ℝ) ^ (5 * shell) := by
  have hradius_one : 1 ≤ euclideanDyadicCubeRadius shell := by
    unfold euclideanDyadicCubeRadius
    exact_mod_cast (one_le_pow₀ (show (1 : ℕ) ≤ 2 by norm_num) : 1 ≤ 2 ^ shell)
  have hmoment_nonneg : 0 ≤ ∫ x : EuclideanSpace ℝ (Fin dimension),
      Real.exp (gamma * Real.rpow ‖x‖ alpha) ∂
        (law : Measure (EuclideanSpace ℝ (Fin dimension))) := by
    apply integral_nonneg
    intro x
    exact (Real.exp_pos _).le
  have htail := exp_neg_mul_rpow_le_fifthOrderPolynomial halpha hgamma hradius_one
  have hradius_pos : 0 < euclideanDyadicCubeRadius shell :=
    euclideanDyadicCubeRadius_pos shell
  calc
    (law : Measure (EuclideanSpace ℝ (Fin dimension))).real
        (euclideanDyadicCubeShell dimension (shell + 1)) ≤
        Real.exp (-(gamma * Real.rpow (euclideanDyadicCubeRadius shell) alpha)) *
          ∫ x : EuclideanSpace ℝ (Fin dimension),
            Real.exp (gamma * Real.rpow ‖x‖ alpha) ∂
              (law : Measure (EuclideanSpace ℝ (Fin dimension))) :=
      measureReal_euclideanDyadicCubeShell_succ_le_exponentialRadialMoment
        dimension shell law (zero_le_one.trans halpha) hgamma.le hmoment
    _ ≤ ((((5 : ℕ).factorial : ℝ) * gamma⁻¹ ^ 5 /
        (euclideanDyadicCubeRadius shell) ^ 5) *
        ∫ x : EuclideanSpace ℝ (Fin dimension),
          Real.exp (gamma * Real.rpow ‖x‖ alpha) ∂
            (law : Measure (EuclideanSpace ℝ (Fin dimension)))) := by
      exact mul_le_mul_of_nonneg_right htail hmoment_nonneg
    _ = (((5 : ℕ).factorial : ℝ) * gamma⁻¹ ^ 5 *
        ∫ x : EuclideanSpace ℝ (Fin dimension),
          Real.exp (gamma * Real.rpow ‖x‖ alpha) ∂
            (law : Measure (EuclideanSpace ℝ (Fin dimension)))) /
        (2 : ℝ) ^ (5 * shell) := by
      unfold euclideanDyadicCubeRadius
      rw [Nat.cast_pow, ← pow_mul, Nat.mul_comm]
      field_simp [hradius_pos.ne']
      ring

/--
Named-constant form of the fifth-order source cube-shell estimate.  It is the
direct bridge to the `I_n` numerical allocation in the shell-concentration
module.
-/
theorem measureReal_euclideanDyadicCubeShell_succ_le_fifthOrderExponentialRadialTailConstant
    (dimension shell : ℕ)
    (law : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    {alpha gamma : ℝ} (halpha : 1 ≤ alpha) (hgamma : 0 < gamma)
    (hmoment : HasExponentialRadialMoment law alpha gamma) :
    (law : Measure (EuclideanSpace ℝ (Fin dimension))).real
      (euclideanDyadicCubeShell dimension (shell + 1)) ≤
      fifthOrderExponentialRadialTailConstant law alpha gamma /
        (2 : ℝ) ^ (5 * shell) := by
  simpa [fifthOrderExponentialRadialTailConstant] using
    (measureReal_euclideanDyadicCubeShell_succ_le_exponentialRadialMoment_fifthOrder
      dimension shell law halpha hgamma hmoment)

end
end Probability
end AppliedModelingLib

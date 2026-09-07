import AppliedModelingLib.Foundations.Optimization.NonconvexSmoothDescent
import AppliedModelingLib.Foundations.Probability.FiniteExpectation

/-!
# Finite adaptive stochastic descent

This module turns a one-step conditional expected-descent inequality for a
finite iid trajectory into a finite-horizon expected gradient-sum bound.  A
state at time `t` is allowed to depend on exactly the `t` preceding samples;
the successor-state expectation is decomposed through the new independent
draw by `pmfExp_pmfProduct_finSucc_eq_pairExp`.

It is deliberately independent of a particular gradient estimator or inner
optimization routine.  Those mechanisms need only establish the displayed
one-step conditional inequality.
-/

namespace AppliedModelingLib
namespace Optimization

open scoped BigOperators
open scoped InnerProductSpace

variable {Sample Parameter : Type*}
variable [Fintype Sample] [DecidableEq Sample]

/--
A finite iid adaptive trajectory has one state for every history length.  The
state at time `t` reads only a `Fin t` history, so this representation makes
adaptedness syntactic rather than a separate measurability premise.
-/
abbrev FiniteAdaptiveTrajectory (Sample Parameter : Type*) :=
  (time : ℕ) → (Fin time → Sample) → Parameter

/--
Take the finite expectation of the one-step inexact smooth-descent bound.  An
unbiased sampled-gradient fluctuation cancels in the inner-product term, while
the approximation and variance contributions are retained as separate bounds.
This is the one-step probabilistic calculation used before applying the
adaptive finite-horizon theorem below.
-/
theorem expectedInexactSmoothDescentStep
    {Parameter : Type*} [NormedAddCommGroup Parameter]
    [InnerProductSpace ℝ Parameter] [CompleteSpace Parameter]
    (sampleLaw : PMF Sample)
    (objective : Parameter → ℝ) (gradient : Parameter → Parameter) (smoothness : ℝ)
    (hgradient : ∀ first second,
      ‖gradient first - gradient second‖ ≤ smoothness * ‖first - second‖)
    (hgradientAt : ∀ parameter, HasGradientAt objective (gradient parameter) parameter)
    (point : Parameter) (sampledGradient approximationError : Sample → Parameter)
    (step error variance : ℝ)
    (hsmoothness : 0 ≤ smoothness) (hstep : 0 ≤ step)
    (hstepSmooth : smoothness * step ≤ 1)
    (hunbiasedInner :
      pmfExp sampleLaw (fun sample =>
        ⟪gradient point, gradient point - sampledGradient sample⟫_ℝ) = 0)
    (herrorTerm :
      pmfExp sampleLaw (fun sample =>
        step * (1 + smoothness * step) / 2 * ‖approximationError sample‖ ^ 2) ≤
        step * error)
    (hvariance :
      pmfExp sampleLaw (fun sample =>
        ‖sampledGradient sample - gradient point‖ ^ 2) ≤ variance) :
    pmfExp sampleLaw (fun sample =>
      objective (point - step • (sampledGradient sample + approximationError sample))) ≤
      objective point - step / 2 * ‖gradient point‖ ^ 2 +
        step * error + smoothness * step ^ 2 * variance := by
  calc
    pmfExp sampleLaw (fun sample =>
        objective (point - step • (sampledGradient sample + approximationError sample))) ≤
      pmfExp sampleLaw (fun sample =>
        objective point - step / 2 * ‖gradient point‖ ^ 2 +
          step * (1 - smoothness * step) *
            ⟪gradient point, gradient point - sampledGradient sample⟫_ℝ +
          step * (1 + smoothness * step) / 2 * ‖approximationError sample‖ ^ 2 +
          smoothness * step ^ 2 * ‖sampledGradient sample - gradient point‖ ^ 2) := by
        apply pmfExp_le_pmfExp_of_forall_le
        intro sample
        exact inexactSmoothDescentStep objective gradient smoothness hgradient hgradientAt
          hsmoothness hstep hstepSmooth
    _ = objective point - step / 2 * ‖gradient point‖ ^ 2 +
          step * (1 - smoothness * step) *
            pmfExp sampleLaw (fun sample =>
              ⟪gradient point, gradient point - sampledGradient sample⟫_ℝ) +
          pmfExp sampleLaw (fun sample =>
            step * (1 + smoothness * step) / 2 * ‖approximationError sample‖ ^ 2) +
          smoothness * step ^ 2 *
            pmfExp sampleLaw (fun sample =>
              ‖sampledGradient sample - gradient point‖ ^ 2) := by
        rw [show (fun sample : Sample =>
              objective point - step / 2 * ‖gradient point‖ ^ 2 +
                step * (1 - smoothness * step) *
                  ⟪gradient point, gradient point - sampledGradient sample⟫_ℝ +
                step * (1 + smoothness * step) / 2 * ‖approximationError sample‖ ^ 2 +
                smoothness * step ^ 2 * ‖sampledGradient sample - gradient point‖ ^ 2) =
            (fun sample =>
              (objective point - step / 2 * ‖gradient point‖ ^ 2) +
                (step * (1 - smoothness * step) *
                  ⟪gradient point, gradient point - sampledGradient sample⟫_ℝ +
                  (step * (1 + smoothness * step) / 2 * ‖approximationError sample‖ ^ 2 +
                    (smoothness * step ^ 2) *
                      ‖sampledGradient sample - gradient point‖ ^ 2))) by
              funext sample
              ring]
        rw [pmfExp_add, pmfExp_const, pmfExp_add, pmfExp_const_mul,
          pmfExp_add, pmfExp_const_mul, pmfExp_const_mul]
        ring
    _ ≤ objective point - step / 2 * ‖gradient point‖ ^ 2 +
          step * error + smoothness * step ^ 2 * variance := by
        rw [hunbiasedInner]
        have hcoefficient : 0 ≤ smoothness * step ^ 2 := by positivity
        have hvarianceTerm := mul_le_mul_of_nonneg_left hvariance hcoefficient
        linarith

/--
Finite-horizon expected descent for an adaptive iid trajectory.  `error` and
`variance` retain the two separate terms of a standard inexact nonconvex-SGD
step.  The hypothesis is conditional on each concrete prefix; independence of
the next draw is discharged by the finite product factorization.
-/
theorem finiteHorizon_expectedGradientSum_le_of_adaptiveDescent
    (sampleLaw : PMF Sample)
    (trajectory : FiniteAdaptiveTrajectory Sample Parameter)
    (objective gradientSq : Parameter → ℝ) (horizon : ℕ)
    (step error smoothness variance lowerBound : ℝ)
    (hstep : 0 < step)
    (hlowerBound : ∀ history, lowerBound ≤ objective (trajectory horizon history))
    (hdescent : ∀ time, time < horizon → ∀ history : Fin time → Sample,
      pmfExp sampleLaw (fun fresh =>
        objective (trajectory (time + 1) (extendFinDraw time history fresh))) ≤
        objective (trajectory time history) - step / 2 * gradientSq (trajectory time history) +
          step * error + smoothness * step ^ 2 * variance) :
    (∑ time ∈ Finset.range horizon,
      pmfExp (pmfProduct (Fin time) Sample sampleLaw)
        (fun history => gradientSq (trajectory time history))) ≤
      2 / step *
          (objective (trajectory 0 (fun index => Fin.elim0 index)) - lowerBound) +
        2 * (horizon : ℝ) * error +
        2 * (horizon : ℝ) * smoothness * step * variance := by
  let potential : ℕ → ℝ := fun time =>
    pmfExp (pmfProduct (Fin time) Sample sampleLaw)
      (fun history => objective (trajectory time history))
  let gradientPotential : ℕ → ℝ := fun time =>
    pmfExp (pmfProduct (Fin time) Sample sampleLaw)
      (fun history => gradientSq (trajectory time history))
  have hpotentialZero :
      potential 0 = objective (trajectory 0 (fun index => Fin.elim0 index)) := by
    calc
      potential 0 =
          pmfExp (pmfProduct (Fin 0) Sample sampleLaw)
            (fun _ => objective (trajectory 0 (fun index => Fin.elim0 index))) := by
              apply pmfExp_congr
              intro history
              congr 2
              funext index
              exact Fin.elim0 index
      _ = objective (trajectory 0 (fun index => Fin.elim0 index)) :=
        pmfExp_const _ _
  have hpotentialLower : lowerBound ≤ potential horizon := by
    calc
      lowerBound =
          pmfExp (pmfProduct (Fin horizon) Sample sampleLaw) (fun _ => lowerBound) :=
        (pmfExp_const _ _).symm
      _ ≤ potential horizon := by
        simpa [potential] using
          (pmfExp_le_pmfExp_of_forall_le
            (pmfProduct (Fin horizon) Sample sampleLaw) _ _ hlowerBound)
  have hpotentialStep : ∀ time, time < horizon →
      potential (time + 1) ≤ potential time - step / 2 * gradientPotential time +
        step * error + smoothness * step ^ 2 * variance := by
    intro time htime
    rw [show time + 1 = time.succ by omega]
    rw [show potential time.succ =
      pmfPairExp (pmfProduct (Fin time) Sample sampleLaw) sampleLaw
        (fun history fresh =>
          objective (trajectory (time + 1) (extendFinDraw time history fresh))) by
      simp only [potential, Nat.succ_eq_add_one]
      exact pmfExp_pmfProduct_finSucc_eq_pairExp time sampleLaw _]
    unfold pmfPairExp
    calc
      pmfExp (pmfProduct (Fin time) Sample sampleLaw) (fun history =>
          pmfExp sampleLaw (fun fresh =>
            objective (trajectory (time + 1) (extendFinDraw time history fresh)))) ≤
        pmfExp (pmfProduct (Fin time) Sample sampleLaw) (fun history =>
          objective (trajectory time history) - step / 2 * gradientSq (trajectory time history) +
            step * error + smoothness * step ^ 2 * variance) := by
          apply pmfExp_le_pmfExp_of_forall_le
          intro history
          exact hdescent time htime history
      _ = potential time - step / 2 * gradientPotential time +
            step * error + smoothness * step ^ 2 * variance := by
          rw [show (fun history : Fin time → Sample =>
                objective (trajectory time history) - step / 2 * gradientSq (trajectory time history) +
                  step * error + smoothness * step ^ 2 * variance) =
              (fun history =>
                (objective (trajectory time history) -
                  step / 2 * gradientSq (trajectory time history)) +
                ((step * error) + (smoothness * step ^ 2 * variance))) by
                funext history
                ring]
          rw [pmfExp_add, pmfExp_sub, pmfExp_const_mul, pmfExp_const]
          simp only [potential, gradientPotential]
          ring
  have hsum := finiteHorizon_gradientSum_le_of_expectedDescent
    potential gradientPotential horizon step error smoothness variance lowerBound
    hstep hpotentialLower hpotentialStep
  rw [hpotentialZero] at hsum
  exact hsum

/--
The average-gradient form of `finiteHorizon_expectedGradientSum_le_of_adaptiveDescent`.
This is the conventional presentation for finite-time nonconvex SGD.
-/
theorem finiteHorizon_expectedAverageGradientSq_le_of_adaptiveDescent
    (sampleLaw : PMF Sample)
    (trajectory : FiniteAdaptiveTrajectory Sample Parameter)
    (objective gradientSq : Parameter → ℝ) (horizon : ℕ)
    (step error smoothness variance lowerBound : ℝ)
    (horizon_pos : 0 < horizon) (hstep : 0 < step)
    (hlowerBound : ∀ history, lowerBound ≤ objective (trajectory horizon history))
    (hdescent : ∀ time, time < horizon → ∀ history : Fin time → Sample,
      pmfExp sampleLaw (fun fresh =>
        objective (trajectory (time + 1) (extendFinDraw time history fresh))) ≤
        objective (trajectory time history) - step / 2 * gradientSq (trajectory time history) +
          step * error + smoothness * step ^ 2 * variance) :
    (1 / (horizon : ℝ)) *
        (∑ time ∈ Finset.range horizon,
          pmfExp (pmfProduct (Fin time) Sample sampleLaw)
            (fun history => gradientSq (trajectory time history))) ≤
      2 / ((horizon : ℝ) * step) *
          (objective (trajectory 0 (fun index => Fin.elim0 index)) - lowerBound) +
        2 * error + 2 * smoothness * step * variance := by
  have hsum := finiteHorizon_expectedGradientSum_le_of_adaptiveDescent
    sampleLaw trajectory objective gradientSq horizon step error smoothness variance lowerBound
    hstep hlowerBound hdescent
  have hhorizon : 0 < (horizon : ℝ) := by exact_mod_cast horizon_pos
  have hrewrite :
      2 / step * (objective (trajectory 0 (fun index => Fin.elim0 index)) - lowerBound) +
          2 * (horizon : ℝ) * error +
          2 * (horizon : ℝ) * smoothness * step * variance =
        (horizon : ℝ) *
          (2 / ((horizon : ℝ) * step) *
              (objective (trajectory 0 (fun index => Fin.elim0 index)) - lowerBound) +
            2 * error + 2 * smoothness * step * variance) := by
    field_simp [ne_of_gt hhorizon, ne_of_gt hstep]
  rw [hrewrite] at hsum
  rw [show (1 / (horizon : ℝ)) *
        (∑ time ∈ Finset.range horizon,
          pmfExp (pmfProduct (Fin time) Sample sampleLaw)
            (fun history => gradientSq (trajectory time history))) =
      (∑ time ∈ Finset.range horizon,
          pmfExp (pmfProduct (Fin time) Sample sampleLaw)
            (fun history => gradientSq (trajectory time history))) / (horizon : ℝ) by
      ring]
  apply (div_le_iff₀ hhorizon).mpr
  simpa [mul_comm] using hsum

end Optimization
end AppliedModelingLib

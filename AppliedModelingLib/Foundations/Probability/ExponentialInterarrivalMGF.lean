import AppliedModelingLib.Foundations.Probability.ExponentialInterarrival
import AppliedModelingLib.Foundations.Probability.ExponentialMoments
import Mathlib.Probability.Moments.Basic

/-!
# Exponential moments of finite IID exponential sums

This module records the finite-sum moment-generating function obtained from
the canonical independent exponential-coordinate carrier.  It is independent
of any renewal stopping time or queueing interpretation.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory ProbabilityTheory

noncomputable section

/-- One coordinate of the canonical exponential IID path has the usual
positive exponential moment below the rate boundary. -/
theorem integrable_exp_mul_interarrival {rate tilt : ℝ}
    (hrate : 0 < rate) (htilt : tilt < rate) (n : ℕ) :
    Integrable (fun omega : ℕ → ℝ => Real.exp (tilt * interarrival n omega))
      (exponentialInterarrivalMeasure rate) := by
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  have hcoordinate : MeasurePreserving (interarrival n)
      (exponentialInterarrivalMeasure rate) (ProbabilityTheory.expMeasure rate) :=
    ⟨measurable_interarrival n, (interarrival_hasLaw hrate n).map_eq⟩
  simpa [Function.comp_def] using
    (hcoordinate.integrable_comp
      ((measurable_const.mul measurable_id).exp.aestronglyMeasurable)).mpr
      (AppliedModelingLib.Probability.integrable_exp_mul_id_expMeasure hrate htilt)

/-- The moment-generating function of one canonical exponential coordinate. -/
theorem mgf_interarrival {rate tilt : ℝ}
    (hrate : 0 < rate) (htilt : tilt < rate) (n : ℕ) :
    mgf (interarrival n) (exponentialInterarrivalMeasure rate) tilt =
      rate / (rate - tilt) := by
  unfold mgf
  calc
    ∫ omega, Real.exp (tilt * interarrival n omega)
        ∂exponentialInterarrivalMeasure rate =
        ∫ x, Real.exp (tilt * x) ∂ProbabilityTheory.expMeasure rate := by
          simpa [Function.comp_def] using
            (interarrival_hasLaw hrate n).integral_comp
              (f := fun x : ℝ => Real.exp (tilt * x))
              ((measurable_const.mul measurable_id).exp.aestronglyMeasurable)
    _ = rate / (rate - tilt) :=
      AppliedModelingLib.Probability.integral_exp_mul_id_expMeasure hrate htilt

/-- The square of one canonical exponential coordinate is integrable. -/
theorem integrable_sq_interarrival {rate : ℝ}
    (hrate : 0 < rate) (n : ℕ) :
    Integrable (fun omega : ℕ → ℝ => (interarrival n omega) ^ 2)
      (exponentialInterarrivalMeasure rate) := by
  let X : (ℕ → ℝ) → ℝ := interarrival n
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  have hlaw := interarrival_hasLaw hrate n
  have htarget : Integrable (fun x : ℝ => x ^ 2) (Measure.map X μ) := by
    rw [hlaw.map_eq]
    exact AppliedModelingLib.Probability.integrable_sq_expMeasure hrate
  exact (integrable_map_measure (f := X) (g := fun x : ℝ => x ^ 2)
    (by fun_prop) hlaw.aemeasurable).mp htarget

/-- One canonical exponential coordinate has its usual second raw moment. -/
theorem integral_sq_interarrival {rate : ℝ}
    (hrate : 0 < rate) (n : ℕ) :
    ∫ omega, (interarrival n omega) ^ 2 ∂exponentialInterarrivalMeasure rate =
      2 / rate ^ 2 := by
  calc
    ∫ omega, (interarrival n omega) ^ 2 ∂exponentialInterarrivalMeasure rate =
        ∫ x, x ^ 2 ∂ProbabilityTheory.expMeasure rate := by
          simpa [Function.comp_def] using
            (interarrival_hasLaw hrate n).integral_comp
              (f := fun x : ℝ => x ^ 2) (by fun_prop)
    _ = 2 / rate ^ 2 :=
      AppliedModelingLib.Probability.integral_sq_expMeasure hrate

/-- A finite sum of canonical IID exponential coordinates has a finite
positive exponential moment whenever the tilt is below the coordinate rate. -/
theorem integrable_exp_mul_sum_interarrival {rate tilt : ℝ}
    (hrate : 0 < rate) (htilt : tilt < rate) (indices : Finset ℕ) :
    Integrable (fun omega : ℕ → ℝ =>
      Real.exp (tilt * ∑ n ∈ indices, interarrival n omega))
      (exponentialInterarrivalMeasure rate) := by
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  simpa only [Finset.sum_apply] using
    ((iIndepFun_interarrival hrate).integrable_exp_mul_sum (s := indices)
    (fun n => measurable_interarrival n)
    (fun n _ => integrable_exp_mul_interarrival hrate htilt n))

/-- The moment-generating function of a finite canonical exponential sum is
the corresponding power of the one-coordinate moment. -/
theorem mgf_sum_interarrival {rate tilt : ℝ}
    (hrate : 0 < rate) (htilt : tilt < rate) (indices : Finset ℕ) :
    mgf (fun omega : ℕ → ℝ => ∑ n ∈ indices, interarrival n omega)
      (exponentialInterarrivalMeasure rate) tilt =
      (rate / (rate - tilt)) ^ indices.card := by
  have hsum : (fun omega : ℕ → ℝ => ∑ n ∈ indices, interarrival n omega) =
      ∑ n ∈ indices, interarrival n := by
    funext omega
    simp only [Finset.sum_apply]
  rw [hsum]
  rw [(iIndepFun_interarrival hrate).mgf_sum
    (fun n => measurable_interarrival n) indices]
  simp_rw [mgf_interarrival hrate htilt]
  simp only [Finset.prod_const, div_pow]

end

end AppliedModelingLib.Probability.PoissonProcess

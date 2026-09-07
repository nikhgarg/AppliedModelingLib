import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalRenewalCount

/-!
# Finite exponential-sum convolution laws

This module proves the probabilistic part of the Erlang construction:
each finite canonical arrival time has the law obtained by repeatedly
convolving the exponential measure.  It deliberately does not identify that
convolution measure with Mathlib's `gammaMeasure`; that analytic identity is
the remaining gamma-convolution theorem.
-/

namespace AppliedModelingLib
namespace Probability
namespace PoissonProcess

open MeasureTheory Filter
open scoped ENNReal NNReal ProbabilityTheory

noncomputable section

/-- Repeated additive convolution of the rate-`rate` exponential law. -/
noncomputable def erlangConvolutionMeasure (rate : ℝ) : ℕ → Measure ℝ
  | 0 => ProbabilityTheory.expMeasure rate
  | n + 1 => erlangConvolutionMeasure rate n ∗ ProbabilityTheory.expMeasure rate

/-- The repeated convolution law is a probability measure at positive rate. -/
theorem isProbabilityMeasure_erlangConvolution
    {rate : ℝ} (hrate : 0 < rate) (n : ℕ) :
    IsProbabilityMeasure (erlangConvolutionMeasure rate n) := by
  induction n with
  | zero =>
      simpa [erlangConvolutionMeasure] using
        (ProbabilityTheory.isProbabilityMeasure_expMeasure hrate)
  | succ n ih =>
      letI : IsProbabilityMeasure (erlangConvolutionMeasure rate n) := ih
      letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure rate) :=
        ProbabilityTheory.isProbabilityMeasure_expMeasure hrate
      simpa [erlangConvolutionMeasure] using
        (inferInstance : IsProbabilityMeasure
          (erlangConvolutionMeasure rate n ∗ ProbabilityTheory.expMeasure rate))

/-- Function-level form of the finite arrival-time sum. -/
theorem arrivalTime_eq_sum_range (n : ℕ) :
    arrivalTime n = ∑ i ∈ Finset.range (n + 1), interarrival i := by
  funext ω
  simp [arrivalTime]

/-- The first finite arrival epoch has the one-fold convolution law. -/
theorem arrivalTime_zero_hasLaw_erlangConvolution
    {rate : ℝ} (hrate : 0 < rate) :
    ProbabilityTheory.HasLaw (arrivalTime 0)
      (erlangConvolutionMeasure rate 0) (exponentialInterarrivalMeasure rate) := by
  simpa [erlangConvolutionMeasure, arrivalTime_zero] using
    (interarrival_hasLaw hrate 0)

/--
Every finite canonical arrival epoch has the repeated-convolution law of its
independent exponential gaps.
-/
theorem arrivalTime_hasLaw_erlangConvolution
    {rate : ℝ} (hrate : 0 < rate) (n : ℕ) :
    ProbabilityTheory.HasLaw (arrivalTime n)
      (erlangConvolutionMeasure rate n) (exponentialInterarrivalMeasure rate) := by
  induction n with
  | zero => exact arrivalTime_zero_hasLaw_erlangConvolution hrate
  | succ n ih =>
      have hindep : ProbabilityTheory.IndepFun (arrivalTime n)
          (interarrival (n + 1)) (exponentialInterarrivalMeasure rate) := by
        rw [arrivalTime_eq_sum_range]
        exact (iIndepFun_interarrival hrate).indepFun_sum_range_succ
          (fun i => measurable_interarrival i) (n + 1)
      letI : IsProbabilityMeasure (erlangConvolutionMeasure rate n) :=
        isProbabilityMeasure_erlangConvolution hrate n
      letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure rate) :=
        ProbabilityTheory.isProbabilityMeasure_expMeasure hrate
      have hsum : ProbabilityTheory.HasLaw
          (fun ω => arrivalTime n ω + interarrival (n + 1) ω)
          (erlangConvolutionMeasure rate n ∗ ProbabilityTheory.expMeasure rate)
          (exponentialInterarrivalMeasure rate) :=
        ProbabilityTheory.IndepFun.hasLaw_fun_add ih
          (interarrival_hasLaw hrate (n + 1)) hindep
      refine hsum.congr (Filter.Eventually.of_forall ?_)
      intro ω
      simp [arrivalTime, Finset.sum_range_succ]

/-- The two-gap arrival time is the convolution of two exponential laws. -/
theorem arrivalTime_one_hasLaw_exponential_conv
    {rate : ℝ} (hrate : 0 < rate) :
    ProbabilityTheory.HasLaw (arrivalTime 1)
      (ProbabilityTheory.expMeasure rate ∗ ProbabilityTheory.expMeasure rate)
      (exponentialInterarrivalMeasure rate) := by
  simpa [erlangConvolutionMeasure] using
    (arrivalTime_hasLaw_erlangConvolution hrate 1)

end
end PoissonProcess
end Probability
end AppliedModelingLib

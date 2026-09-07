import AppliedModelingLib.Foundations.Probability.ExponentialInterarrival
import Mathlib.Probability.StrongLaw

/-!
# Nonexplosion of the canonical exponential renewal path

The finite-sum interarrival construction gives a genuine nonexplosion result:
at positive rate its arrival epochs diverge almost surely, so every finite
time sees only finitely many canonical arrivals.  This is still a renewal-path
result; it does not construct the all-times Poisson count process or its
random-index strong Markov property.
-/

namespace AppliedModelingLib
namespace Probability
namespace PoissonProcess

open MeasureTheory Filter Finset
open scoped ENNReal NNReal Topology ProbabilityTheory Function

noncomputable section

/-- The first canonical exponential interarrival coordinate is integrable. -/
theorem integrable_interarrival_zero
    {rate : ℝ} (hrate : 0 < rate) :
    Integrable (interarrival 0) (exponentialInterarrivalMeasure rate) := by
  let M : Exponential.Model := Exponential.Model.mk rate hrate
  have hExp : Integrable (fun x : ℝ => x) (ProbabilityTheory.expMeasure rate) := by
    simpa [Exponential.Model.measure, M] using M.integrable_id
  have hmap : Measure.map (interarrival 0) (exponentialInterarrivalMeasure rate) =
      ProbabilityTheory.expMeasure rate :=
    (interarrival_hasLaw hrate 0).map_eq
  have hmapInt : Integrable (fun x : ℝ => x)
      (Measure.map (interarrival 0) (exponentialInterarrivalMeasure rate)) := by
    rw [hmap]
    exact hExp
  simpa [Function.comp_def] using
    (integrable_map_measure aestronglyMeasurable_id
      (measurable_interarrival 0).aemeasurable).mp hmapInt

/-- The mean of a canonical exponential interarrival is the reciprocal rate. -/
theorem integral_interarrival_zero_eq_inv_rate
    {rate : ℝ} (hrate : 0 < rate) :
    (exponentialInterarrivalMeasure rate)[interarrival 0] = 1 / rate := by
  let M : Exponential.Model := Exponential.Model.mk rate hrate
  calc
    (exponentialInterarrivalMeasure rate)[interarrival 0] =
        ∫ x, x ∂ProbabilityTheory.expMeasure rate :=
      (interarrival_hasLaw hrate 0).integral_eq
    _ = M.expectedMaxValue 1 := by
      simpa [Exponential.Model.measure, M] using M.integral_id_eq_expectedMaxValue_one
    _ = 1 / rate := by
      simp [Exponential.Model.expectedMaxValue,
        Exponential.expectedMaxValueOfRate_one, M]

/-- Every canonical exponential interarrival coordinate is integrable.  The
index is immaterial because each coordinate has the same exponential law. -/
theorem integrable_interarrival
    {rate : ℝ} (hrate : 0 < rate) (n : ℕ) :
    Integrable (interarrival n) (exponentialInterarrivalMeasure rate) := by
  let M : Exponential.Model := Exponential.Model.mk rate hrate
  have hExp : Integrable (fun x : ℝ => x) (ProbabilityTheory.expMeasure rate) := by
    simpa [Exponential.Model.measure, M] using M.integrable_id
  have hmap : Measure.map (interarrival n) (exponentialInterarrivalMeasure rate) =
      ProbabilityTheory.expMeasure rate :=
    (interarrival_hasLaw hrate n).map_eq
  have hmapInt : Integrable (fun x : ℝ => x)
      (Measure.map (interarrival n) (exponentialInterarrivalMeasure rate)) := by
    rw [hmap]
    exact hExp
  simpa [Function.comp_def] using
    (integrable_map_measure aestronglyMeasurable_id
      (measurable_interarrival n).aemeasurable).mp hmapInt

/-- Every canonical exponential interarrival coordinate has mean reciprocal
rate. -/
theorem integral_interarrival_eq_inv_rate
    {rate : ℝ} (hrate : 0 < rate) (n : ℕ) :
    (exponentialInterarrivalMeasure rate)[interarrival n] = 1 / rate := by
  calc
    (exponentialInterarrivalMeasure rate)[interarrival n] =
        ∫ x, x ∂ProbabilityTheory.expMeasure rate :=
      (interarrival_hasLaw hrate n).integral_eq
    _ = (exponentialInterarrivalMeasure rate)[interarrival 0] :=
      (interarrival_hasLaw hrate 0).integral_eq.symm
    _ = 1 / rate := integral_interarrival_zero_eq_inv_rate hrate

/-- At positive rate, the canonical exponential renewal epochs diverge almost surely. -/
theorem ae_arrivalTime_tendsto_atTop
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᵐ ω ∂exponentialInterarrivalMeasure rate,
      Tendsto (fun n : ℕ => arrivalTime n ω) atTop atTop := by
  have hindep : Pairwise ((· ⟂ᵢ[exponentialInterarrivalMeasure rate] ·) on interarrival) := by
    intro i j hij
    exact (iIndepFun_interarrival hrate).indepFun hij
  have hident : ∀ i, ProbabilityTheory.IdentDistrib (interarrival i) (interarrival 0)
      (exponentialInterarrivalMeasure rate) (exponentialInterarrivalMeasure rate) :=
    fun i => (interarrival_hasLaw hrate i).identDistrib (interarrival_hasLaw hrate 0)
  have hmean : (exponentialInterarrivalMeasure rate)[interarrival 0] = 1 / rate :=
    integral_interarrival_zero_eq_inv_rate hrate
  have hmean_pos : 0 < (exponentialInterarrivalMeasure rate)[interarrival 0] := by
    rw [hmean]
    exact one_div_pos.mpr hrate
  filter_upwards [ProbabilityTheory.strong_law_ae_real interarrival
    (integrable_interarrival_zero hrate) hindep hident] with ω hω
  have hshift : Tendsto
      (fun n : ℕ => (∑ i ∈ range (n + 1), interarrival i ω) / ((n + 1 : ℕ) : ℝ)) atTop
      (𝓝 (exponentialInterarrivalMeasure rate)[interarrival 0]) := by
    simpa [Function.comp_def] using hω.comp (tendsto_add_atTop_nat 1)
  have hscale : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    simpa [Function.comp_def] using tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hprod := hshift.pos_mul_atTop hmean_pos hscale
  apply hprod.congr'
  filter_upwards with n
  simp only [arrivalTime]
  field_simp [Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)]

/-- Almost surely, every bounded time interval contains only finitely many canonical arrivals. -/
theorem ae_finite_arrivals_by_time
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᵐ ω ∂exponentialInterarrivalMeasure rate,
      ∀ t : ℝ, Set.Finite {n : ℕ | arrivalTime n ω ≤ t} := by
  filter_upwards [ae_arrivalTime_tendsto_atTop hrate] with ω hω
  intro t
  obtain ⟨N, hN⟩ := (eventually_atTop.1 (hω.eventually_gt_atTop t))
  refine (Set.finite_Iio N).subset ?_
  intro n hn
  by_contra hnot
  have hnN : N ≤ n := Nat.le_of_not_gt hnot
  exact (not_lt_of_ge hn) (hN n hnN)

end
end PoissonProcess
end Probability
end AppliedModelingLib

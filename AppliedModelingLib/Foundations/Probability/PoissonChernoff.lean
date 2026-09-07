import AppliedModelingLib.Foundations.Math.LogQuadraticBounds
import AppliedModelingLib.Foundations.Probability.PoissonMomentGenerating
import Mathlib.Probability.Moments.Basic
import Mathlib.Tactic

/-!
# Chernoff bounds for Poisson counts

Exponential upper-tail bounds for a Poisson count at a larger natural
threshold.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

/-- The moment generating function of the real-valued Poisson count. -/
theorem mgf_natCast_poissonMeasure (mean : ℝ≥0) (t : ℝ) :
    mgf (fun n : ℕ => (n : ℝ)) (poissonMeasure mean) t =
      Real.exp ((mean : ℝ) * (Real.exp t - 1)) := by
  rw [mgf]
  have hrewrite : (fun n : ℕ => Real.exp (t * (n : ℝ))) =
      fun n : ℕ => (Real.exp t) ^ n := by
    funext n
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hrewrite, integral_pow_poissonMeasure]

/-- A Poisson count with mean `servers * trafficIntensity` has the standard
Cramér upper-tail bound at the `servers` threshold. -/
theorem measureReal_poissonMeasure_Ici_servers_le_exp_rate
    (servers : ℕ) (trafficIntensity : ℝ≥0)
    (htraffic_pos : 0 < (trafficIntensity : ℝ))
    (htraffic_le_one : (trafficIntensity : ℝ) ≤ 1) :
    (poissonMeasure (servers * trafficIntensity)).real (Set.Ici servers) ≤
      Real.exp ((servers : ℝ) *
        (Real.log (trafficIntensity : ℝ) - (trafficIntensity : ℝ) + 1)) := by
  let t : ℝ := -Real.log (trafficIntensity : ℝ)
  have ht : 0 ≤ t := by
    dsimp [t]
    exact neg_nonneg.mpr (Real.log_nonpos htraffic_pos.le htraffic_le_one)
  have hint : Integrable
      (fun n : ℕ => Real.exp (t * (n : ℝ)))
      (poissonMeasure (servers * trafficIntensity)) := by
    have hrewrite : (fun n : ℕ => Real.exp (t * (n : ℝ))) =
        fun n : ℕ => (Real.exp t) ^ n := by
      funext n
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hrewrite]
    exact integrable_pow_poissonMeasure _ _
  have hchernoff := measure_ge_le_exp_mul_mgf
    (μ := poissonMeasure (servers * trafficIntensity))
    (X := fun n : ℕ => (n : ℝ)) (servers : ℝ) ht hint
  have hset : {n : ℕ | (servers : ℝ) ≤ (n : ℝ)} = Set.Ici servers := by
    ext n
    simp
  rw [hset, mgf_natCast_poissonMeasure] at hchernoff
  convert hchernoff using 1
  dsimp [t]
  rw [Real.exp_neg, ← Real.exp_add]
  congr 1
  have htraffic_ne : (trafficIntensity : ℝ) ≠ 0 := ne_of_gt htraffic_pos
  rw [Real.exp_log htraffic_pos]
  field_simp [htraffic_ne]
  simp only [NNReal.coe_natCast]
  ring

end AppliedModelingLib.Probability.PoissonProcess

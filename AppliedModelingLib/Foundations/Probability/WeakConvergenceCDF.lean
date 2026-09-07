import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.CDF
import Mathlib.Tactic

/-!
# Weak convergence from real cumulative distribution functions

This module gives a one-dimensional probability-measure convergence criterion.
Pointwise convergence of cumulative distribution functions yields weak
convergence by first obtaining convergence on half-open intervals and then
using the Portmanteau theorem on their local pi-system.
-/

namespace AppliedModelingLib
namespace Probability

open Filter Topology MeasureTheory ProbabilityTheory Set TopologicalSpace

/-- Transport weak convergence of explicitly identified laws to convergence in
distribution of the corresponding random variables. -/
theorem tendstoInDistribution_of_hasLaw_of_tendsto_probabilityMeasure
    {ι E Ω' : Type*} {Ω : ι → Type*}
    {m : ∀ i, MeasurableSpace (Ω i)} {μ : ∀ i, Measure (Ω i)}
    [∀ i, IsProbabilityMeasure (μ i)]
    {m' : MeasurableSpace Ω'} {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {X : (i : ι) → Ω i → E} {Z : Ω' → E}
    {ν : ι → ProbabilityMeasure E} {ν' : ProbabilityMeasure E} {l : Filter ι}
    (hX : ∀ i, HasLaw (X i) (ν i : Measure E) (μ i))
    (hZ : HasLaw Z (ν' : Measure E) μ')
    (hν : Tendsto ν l (𝓝 ν')) :
    TendstoInDistribution X l Z μ μ' := by
  refine ⟨fun i => (hX i).aemeasurable, hZ.aemeasurable, ?_⟩
  let pX : ι → ProbabilityMeasure E := fun i =>
    ⟨(μ i).map (X i), Measure.isProbabilityMeasure_map (hX i).aemeasurable⟩
  let pZ : ProbabilityMeasure E :=
    ⟨μ'.map Z, Measure.isProbabilityMeasure_map hZ.aemeasurable⟩
  change Tendsto pX l (𝓝 pZ)
  have hpX : pX = ν := by
    funext i
    apply Subtype.ext
    exact (hX i).map_eq
  have hpZ : pZ = ν' := by
    apply Subtype.ext
    exact hZ.map_eq
  rw [hpX, hpZ]
  exact hν

/-- Coordinatewise weak convergence of finitely many probability laws yields
weak convergence of their finite product law. -/
theorem tendsto_probabilityMeasure_pi_of_tendsto
    {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ index, TopologicalSpace (α index)]
    [∀ index, MeasurableSpace (α index)]
    [∀ index, SecondCountableTopology (α index)]
    [∀ index, PseudoMetrizableSpace (α index)]
    [∀ index, OpensMeasurableSpace (α index)]
    {laws : ℕ → (index : ι) → ProbabilityMeasure (α index)}
    {limit : (index : ι) → ProbabilityMeasure (α index)}
    (h : ∀ index : ι,
      Tendsto (fun n : ℕ => laws n index) atTop (𝓝 (limit index))) :
    Tendsto (fun n : ℕ => ProbabilityMeasure.pi (laws n)) atTop
      (𝓝 (ProbabilityMeasure.pi limit)) := by
  have hcoordinates : Tendsto (fun n : ℕ => laws n) atTop (𝓝 limit) :=
    tendsto_pi_nhds.mpr h
  exact (ProbabilityMeasure.continuous_pi.tendsto limit).comp hcoordinates

/-- The real mass of a half-open interval is the difference of its endpoint CDF values. -/
theorem measureReal_Ioc_eq_cdf_sub (μ : ProbabilityMeasure ℝ) {a b : ℝ} (hab : a ≤ b) :
    (μ : Measure ℝ).real (Ioc a b) =
      cdf (μ : Measure ℝ) b - cdf (μ : Measure ℝ) a := by
  have hset : Ioc a b = Iic b \ Iic a := by
    ext x
    simp
  rw [hset, MeasureTheory.measureReal_diff (Iic_subset_Iic.mpr hab) measurableSet_Iic]
  simp only [cdf_eq_real]

/-- Pointwise convergence of real CDFs implies weak convergence of probability measures. -/
theorem tendsto_probabilityMeasure_of_tendsto_cdf
    {μ : ℕ → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    (h : ∀ x : ℝ,
      Tendsto (fun n => cdf (μ n : Measure ℝ) x) atTop
        (𝓝 (cdf (ν : Measure ℝ) x))) :
    Tendsto μ atTop (𝓝 ν) := by
  let S : Set (Set ℝ) := {s | ∃ a b : ℝ, a < b ∧ Ioc a b = s}
  have hpi : IsPiSystem S := by
    simpa only [S, id_eq] using (isPiSystem_Ioc (id : ℝ → ℝ) id)
  refine hpi.tendsto_probabilityMeasure_of_tendsto_of_mem ?_ ?_ ?_
  · rintro s ⟨a, b, hab, rfl⟩
    exact measurableSet_Ioc
  · intro u hu x hx
    rcases Metric.isOpen_iff.mp hu x hx with ⟨ε, hε, hball⟩
    refine ⟨Ioc (x - ε / 2) (x + ε / 2), ?_, ?_, ?_⟩
    · refine ⟨x - ε / 2, x + ε / 2, by linarith, rfl⟩
    · exact Filter.mem_of_superset
        (show Ioo (x - ε / 2) (x + ε / 2) ∈ 𝓝 x from
          Ioo_mem_nhds (by linarith) (by linarith))
        Ioo_subset_Ioc_self
    · intro y hy
      apply hball
      change dist y x < ε
      rw [Real.dist_eq]
      rw [abs_lt]
      constructor <;> linarith [hy.1, hy.2]
  · rintro s ⟨a, b, hab, rfl⟩
    have hreal : Tendsto (fun n => (μ n : Measure ℝ).real (Ioc a b)) atTop
        (𝓝 ((ν : Measure ℝ).real (Ioc a b))):= by
      simp_rw [measureReal_Ioc_eq_cdf_sub _ hab.le]
      exact (h b).sub (h a)
    simpa using hreal

end Probability
end AppliedModelingLib

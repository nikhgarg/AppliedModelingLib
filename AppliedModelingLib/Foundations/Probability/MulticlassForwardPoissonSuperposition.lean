import AppliedModelingLib.Foundations.Probability.MulticlassForwardPoisson
import Mathlib.Tactic

/-!
# Fixed-time aggregation of independent forward Poisson inputs

For a finite family of independently carried forward Poisson inputs, this
module identifies the distribution of their total count at one deterministic
time.  It is deliberately a fixed-time statement: obtaining a full
superposed process, or a stopped-arrival compensation formula, additionally
requires a proof about joint increments and the relevant filtration.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory Filter
open scoped NNReal

noncomputable section

variable {Class : Type*} [Fintype Class]

local instance multiclassForwardPoissonSuperpositionDecidableEq : DecidableEq Class :=
  Classical.decEq Class

/-- Total arrivals from all finite classes by a forward horizon. -/
noncomputable def multiclassForwardAggregateCount
    (rate : Class → ℝ) (hrate : ∀ i, 0 < rate i)
    (t : ℝ≥0) (omega : Class → ℕ → ℝ) : ℕ :=
  ∑ i, (multiclassForwardPoissonCountingProcess rate hrate i).count t omega

/-- The finite aggregate count at a deterministic forward horizon is measurable. -/
theorem measurable_multiclassForwardAggregateCount
    (rate : Class → ℝ) (hrate : ∀ i, 0 < rate i) (t : ℝ≥0) :
    Measurable (multiclassForwardAggregateCount rate hrate t) := by
  unfold multiclassForwardAggregateCount
  exact Finset.measurable_sum _ fun i _ =>
    (multiclassForwardPoissonCountingProcess rate hrate i).measurable_count t

/-- At a fixed forward horizon, the class counts are mutually independent. -/
theorem iIndepFun_multiclassForwardClassCount
    (rate : Class → ℝ) (hrate : ∀ i, 0 < rate i) (t : ℝ≥0) :
    ProbabilityTheory.iIndepFun
      (fun i (omega : Class → ℕ → ℝ) =>
        (multiclassForwardPoissonCountingProcess rate hrate i).count t omega)
      (multiclassForwardArrivalMeasure rate) := by
  have hpaths := iIndepFun_multiclassForwardArrivalPaths rate hrate
  have hcounts := hpaths.comp
    (fun _ => canonicalRenewalCount (t : ℝ))
    (fun _ => measurable_canonicalRenewalCount (t : ℝ))
  simpa [multiclassForwardPoissonCountingProcess,
    ForwardHomogeneousPoissonCountingProcessByLaw.compMeasurePreserving,
    canonicalForwardHomogeneousPoissonCountingProcessByLaw,
    Function.comp_def] using hcounts

/-- The aggregate deterministic-time count has the Poisson mass with exposure
equal to the sum of the individual class exposures. -/
theorem multiclassForwardAggregateCount_prob
    (rate : Class → ℝ) (hrate : ∀ i, 0 < rate i)
    (t : ℝ≥0) (count : ℕ) :
    (multiclassForwardArrivalMeasure rate).real
      {omega | multiclassForwardAggregateCount rate hrate t omega = count} =
      countLikelihood 1 (∑ i, rate i * (t : ℝ)) count := by
  let P : Measure (Class → ℕ → ℝ) := multiclassForwardArrivalMeasure rate
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact isProbabilityMeasure_multiclassForwardArrivalMeasure rate hrate
  let X : Class → (Class → ℕ → ℝ) → ℕ := fun i omega =>
    (multiclassForwardPoissonCountingProcess rate hrate i).count t omega
  have hX : ∀ i, AEMeasurable (X i) P := by
    intro i
    exact (multiclassForwardPoissonCountingProcess rate hrate i).measurable_count t |>.aemeasurable
  have hIndep : ProbabilityTheory.iIndepFun X P := by
    simpa [X, P] using iIndepFun_multiclassForwardClassCount rate hrate t
  have hJoint : ∀ k : Class → ℕ,
      P.real (⋂ i ∈ (Finset.univ : Finset Class), {omega | X i omega = k i}) =
        countLikelihoodProduct (Finset.univ : Finset Class) 1
          (fun i => rate i * (t : ℝ)) k := by
    intro k
    have hmeasure := hIndep.meas_iInter (fun i =>
      ⟨{k i}, measurableSet_singleton (k i), rfl⟩)
    rw [Measure.real_def]
    change ENNReal.toReal
        (P (⋂ i ∈ (Finset.univ : Finset Class), {omega | X i omega = k i})) = _
    rw [show (⋂ i ∈ (Finset.univ : Finset Class), {omega | X i omega = k i}) =
        ⋂ i, {omega | X i omega = k i} by simp,
      show (⋂ i, {omega | X i omega = k i}) =
        ⋂ i, X i ⁻¹' {k i} by rfl,
      hmeasure, ENNReal.toReal_prod]
    rw [countLikelihoodProduct]
    refine Finset.prod_congr rfl fun i _ => ?_
    change P.real {omega | (multiclassForwardPoissonCountingProcess rate hrate i).count t omega =
      k i} = _
    exact (multiclassForwardPoissonCountingProcess rate hrate i).count_prob_eq_unit_rate_product
      t (k i)
  change P.real {omega | (∑ i, X i omega) = count} = _
  simpa [P, totalExposure] using
    (finite_count_sum_real_eq_countLikelihood_total hX hJoint count)

/-- The aggregate deterministic-time count has the usual total-rate Poisson
mass. -/
theorem multiclassForwardAggregateCount_prob_eq_totalRate
    (rate : Class → ℝ) (hrate : ∀ i, 0 < rate i)
    (t : ℝ≥0) (count : ℕ) :
    (multiclassForwardArrivalMeasure rate).real
      {omega | multiclassForwardAggregateCount rate hrate t omega = count} =
      countLikelihood 1 ((∑ i, rate i) * (t : ℝ)) count := by
  simpa [Finset.sum_mul] using
    multiclassForwardAggregateCount_prob rate hrate t count

/-- The probability that no class arrives by a deterministic forward horizon
is the exponential survival probability at the total arrival rate. -/
theorem multiclassForwardAggregateCount_zero_prob
    (rate : Class → ℝ) (hrate : ∀ i, 0 < rate i) (t : ℝ≥0) :
    (multiclassForwardArrivalMeasure rate).real
      {omega | multiclassForwardAggregateCount rate hrate t omega = 0} =
      noArrivalProb (∑ i, rate i) (t : ℝ) := by
  simpa [noArrivalProb, countLikelihood] using
    multiclassForwardAggregateCount_prob_eq_totalRate rate hrate t 0

end

end AppliedModelingLib.Probability.PoissonProcess

import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalRenewalCount
import AppliedModelingLib.Foundations.Probability.ExponentialGammaCDF
import AppliedModelingLib.Foundations.Probability.PoissonMoments

/-!
# Canonical renewal-count marginal foundations

This module proves the full fixed-time Poisson PMF for the canonical
exponential renewal count. The proof combines the exact threshold/cardinality
identities with the positive-integer Gamma/Erlang CDF formula for finite sums
of iid exponential interarrivals.
-/

namespace AppliedModelingLib
namespace Probability
namespace PoissonProcess

open MeasureTheory Filter
open scoped ENNReal NNReal ProbabilityTheory

noncomputable section

/--
The `0`-count mass of the canonical exponential renewal count agrees with the
`0`-mass of a Poisson variable of exposure `rate * t`.

This is the zero case of the fixed-time Poisson-marginal proof.
-/
theorem canonicalRenewalCount_zero_pmf_toReal
    {rate t : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t) :
    ((exponentialInterarrivalMeasure rate)
      {ω | canonicalRenewalCount t ω = 0}).toReal =
      Real.exp (-(rate * t)) := by
  have hfuture :
      ∀ᵐ ω ∂exponentialInterarrivalMeasure rate,
        ∃ n : ℕ, t < arrivalTime n ω :=
    (ae_arrivalTime_tendsto_atTop hrate).mono
      (fun ω hω => exists_arrivalTime_gt_of_tendsto_atTop ω hω t)
  have hzero :
      {ω | canonicalRenewalCount t ω = 0} =ᵐ[exponentialInterarrivalMeasure rate]
        {ω | t < interarrival 0 ω} := by
    filter_upwards [hfuture] with ω hω
    apply propext
    change canonicalRenewalCount t ω = 0 ↔ t < interarrival 0 ω
    rw [canonicalRenewalCount_eq_zero_iff]
    simp [hω, arrivalTime_zero]
  let M : Exponential.Model := ⟨rate, hrate⟩
  have hinterarrival := interarrival_hasLaw hrate 0
  calc
    ((exponentialInterarrivalMeasure rate)
        {ω | canonicalRenewalCount t ω = 0}).toReal =
        ((exponentialInterarrivalMeasure rate)
          {ω | t < interarrival 0 ω}).toReal := by
          rw [measure_congr hzero]
    _ = ((exponentialInterarrivalMeasure rate).map (interarrival 0)
          (Set.Ioi t)).toReal := by
          change ((exponentialInterarrivalMeasure rate)
            (interarrival 0 ⁻¹' Set.Ioi t)).toReal = _
          rw [Measure.map_apply_of_aemeasurable hinterarrival.aemeasurable
            measurableSet_Ioi]
    _ = ((ProbabilityTheory.expMeasure rate) (Set.Ioi t)).toReal := by
          rw [hinterarrival.map_eq]
    _ = Real.exp (-(rate * t)) := by
          simpa [M, Exponential.Model.measure] using M.measure_Ioi_toReal ht

/-- The preceding base case stated directly against Mathlib's Poisson measure. -/
theorem canonicalRenewalCount_zero_pmf_eq_poisson
    {rate t : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t) :
    ((exponentialInterarrivalMeasure rate)
      {ω | canonicalRenewalCount t ω = 0}).toReal =
      (ProbabilityTheory.poissonMeasure
        (⟨rate * t, mul_nonneg hrate.le ht⟩ : ℝ≥0)).real {0} := by
  rw [canonicalRenewalCount_zero_pmf_toReal hrate ht,
    ProbabilityTheory.poissonMeasure_real_singleton]
  change Real.exp (-(rate * t)) =
    Real.exp (-(rate * t)) * (rate * t) ^ 0 / ((Nat.factorial 0 : ℕ) : ℝ)
  norm_num

/--
The count-tail event is exactly the CDF event of the corresponding finite
arrival epoch.
-/
theorem canonicalRenewalCount_tail_eq_arrivalTime_toReal
    {rate t : ℝ} (hrate : 0 < rate) (n : ℕ) :
    ((exponentialInterarrivalMeasure rate)
      {ω | n + 1 ≤ canonicalRenewalCount t ω}).toReal =
      ((exponentialInterarrivalMeasure rate)
        {ω | arrivalTime n ω ≤ t}).toReal := by
  have hthreshold := ae_lt_canonicalRenewalCount_iff_arrivalTime_le hrate
  have hset :
      {ω | n + 1 ≤ canonicalRenewalCount t ω} =ᵐ[exponentialInterarrivalMeasure rate]
        {ω | arrivalTime n ω ≤ t} := by
    filter_upwards [hthreshold] with ω hω
    apply propext
    change n + 1 ≤ canonicalRenewalCount t ω ↔ arrivalTime n ω ≤ t
    simpa only [Nat.succ_le_iff] using hω t n
  rw [measure_congr hset]

/--
Every count point mass is the difference of two consecutive count-tail
probabilities. Combined with the finite-arrival Erlang CDF identities below,
this yields the full fixed-time Poisson PMF.
-/
theorem canonicalRenewalCount_pmf_eq_tailDiff
    {rate t : ℝ} (hrate : 0 < rate) (n : ℕ) :
    (exponentialInterarrivalMeasure rate).real
        {ω | canonicalRenewalCount t ω = n} =
      (exponentialInterarrivalMeasure rate).real
        {ω | n ≤ canonicalRenewalCount t ω} -
      (exponentialInterarrivalMeasure rate).real
        {ω | n + 1 ≤ canonicalRenewalCount t ω} := by
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  let A : Set (ℕ → ℝ) := {ω | n ≤ canonicalRenewalCount t ω}
  let B : Set (ℕ → ℝ) := {ω | n + 1 ≤ canonicalRenewalCount t ω}
  have hBsub : B ⊆ A := by
    intro ω hω
    exact Nat.le_trans (Nat.le_succ n) hω
  have hBmeas : MeasurableSet B := by
    exact measurableSet_le measurable_const (measurable_canonicalRenewalCount t)
  have hdiff : {ω | canonicalRenewalCount t ω = n} = A \ B := by
    ext ω
    change canonicalRenewalCount t ω = n ↔
      n ≤ canonicalRenewalCount t ω ∧ ¬ n + 1 ≤ canonicalRenewalCount t ω
    constructor
    · intro h
      constructor
      · simp [h]
      · intro hs
        rw [h] at hs
        exact (Nat.not_succ_le_self n) hs
    · rintro ⟨hlo, hnot⟩
      exact Nat.le_antisymm (Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hnot)) hlo
  rw [hdiff, MeasureTheory.measureReal_diff hBsub hBmeas]

/-- Positive renewal-count masses are consecutive finite-arrival CDF gaps. -/
theorem canonicalRenewalCount_succ_pmf_eq_arrivalCdfDiff
    {rate t : ℝ} (hrate : 0 < rate) (n : ℕ) :
    (exponentialInterarrivalMeasure rate).real
        {ω | canonicalRenewalCount t ω = n + 1} =
      (exponentialInterarrivalMeasure rate).real
        {ω | arrivalTime n ω ≤ t} -
      (exponentialInterarrivalMeasure rate).real
        {ω | arrivalTime (n + 1) ω ≤ t} := by
  rw [canonicalRenewalCount_pmf_eq_tailDiff hrate (n + 1)]
  change ((exponentialInterarrivalMeasure rate)
      {ω | n + 1 ≤ canonicalRenewalCount t ω}).toReal -
      ((exponentialInterarrivalMeasure rate)
        {ω | n + 1 + 1 ≤ canonicalRenewalCount t ω}).toReal =
      ((exponentialInterarrivalMeasure rate)
        {ω | arrivalTime n ω ≤ t}).toReal -
      ((exponentialInterarrivalMeasure rate)
        {ω | arrivalTime (n + 1) ω ≤ t}).toReal
  rw [canonicalRenewalCount_tail_eq_arrivalTime_toReal hrate n]
  rw [canonicalRenewalCount_tail_eq_arrivalTime_toReal (t := t) hrate (n + 1)]

/-- The Erlang CDF formula transported to each canonical finite arrival epoch. -/
theorem arrivalTime_nat_succ_cdf_eq_erlangCDFCandidate
    (n : ℕ) {rate t : ℝ} (hr : 0 < rate) (ht : 0 ≤ t) :
    (exponentialInterarrivalMeasure rate).real
        {ω | arrivalTime n ω ≤ t} =
      erlangCDFCandidate n rate t := by
  let μ := exponentialInterarrivalMeasure rate
  have hLaw := arrivalTime_hasLaw_gammaMeasure_nat_succ hr n
  calc
    μ.real {ω | arrivalTime n ω ≤ t} =
        (Measure.map (arrivalTime n) μ).real (Set.Iic t) := by
      simp only [measureReal_def]
      rw [Measure.map_apply (measurable_arrivalTime n) measurableSet_Iic]
      congr 1
    _ = (ProbabilityTheory.gammaMeasure ((n + 1 : ℕ) : ℝ) rate).real
        (Set.Iic t) := by
      simp only [measureReal_def]
      rw [hLaw.map_eq]
    _ = erlangCDFCandidate n rate t := by
      simp only [measureReal_def]
      rw [gammaMeasure_nat_succ_Iic_eq_erlangCDFCandidate n hr ht,
        ENNReal.toReal_ofReal (erlangCDFCandidate_nonneg n hr.le ht)]

/-- The CDF of each canonical finite arrival epoch in expanded Erlang-series
form. -/
theorem arrivalTime_nat_succ_cdf_eq_erlangCDF
    (n : ℕ) {rate t : ℝ} (hr : 0 < rate) (ht : 0 ≤ t) :
    (exponentialInterarrivalMeasure rate).real
        {ω | arrivalTime n ω ≤ t} =
      1 - Real.exp (-(rate * t)) *
        ∑ k ∈ Finset.range (n + 1), (rate * t) ^ k / (k.factorial : ℝ) := by
  simpa [erlangCDFCandidate, erlangTail, erlangTailPolynomial] using
    arrivalTime_nat_succ_cdf_eq_erlangCDFCandidate n hr ht

/-- Every fixed finite renewal epoch is atomless under the canonical
exponential interarrival product law. -/
theorem arrivalTime_measure_singleton_eq_zero
    {rate : ℝ} (hrate : 0 < rate) (n : ℕ) (z : ℝ) :
    exponentialInterarrivalMeasure rate {ξ | arrivalTime n ξ = z} = 0 := by
  calc
    exponentialInterarrivalMeasure rate {ξ | arrivalTime n ξ = z} =
        (exponentialInterarrivalMeasure rate).map (arrivalTime n) {z} := by
      symm
      rw [Measure.map_apply (measurable_arrivalTime n) (measurableSet_singleton z)]
      rfl
    _ = ProbabilityTheory.gammaMeasure ((n + 1 : ℕ) : ℝ) rate {z} := by
      rw [(arrivalTime_hasLaw_gammaMeasure_nat_succ hrate n).map_eq]
    _ = 0 := by
      change (volume.withDensity
        (ProbabilityTheory.gammaPDF ((n + 1 : ℕ) : ℝ) rate)) {z} = 0
      exact measure_singleton z

/-- The `n + 1` renewal-count tail is the Erlang CDF of its `n`th epoch. -/
theorem canonicalRenewalCount_succ_tail_eq_erlangCDFCandidate
    (n : ℕ) {rate t : ℝ} (hr : 0 < rate) (ht : 0 ≤ t) :
    (exponentialInterarrivalMeasure rate).real
        {ω | n + 1 ≤ canonicalRenewalCount t ω} =
      erlangCDFCandidate n rate t := by
  rw [measureReal_def]
  rw [canonicalRenewalCount_tail_eq_arrivalTime_toReal hr n]
  exact arrivalTime_nat_succ_cdf_eq_erlangCDFCandidate n hr ht

theorem erlangCDFCandidate_sub_succ
    (n : ℕ) (rate t : ℝ) :
    erlangCDFCandidate n rate t - erlangCDFCandidate (n + 1) rate t =
      Real.exp (-(rate * t)) * (rate * t) ^ (n + 1) /
        ((n + 1).factorial : ℝ) := by
  unfold erlangCDFCandidate erlangTail
  rw [erlangTailPolynomial_succ]
  ring

/-- Every positive canonical renewal-count mass has the Poisson/Erlang form. -/
theorem canonicalRenewalCount_succ_pmf_eq_erlang
    (n : ℕ) {rate t : ℝ} (hr : 0 < rate) (ht : 0 ≤ t) :
    (exponentialInterarrivalMeasure rate).real
        {ω | canonicalRenewalCount t ω = n + 1} =
      Real.exp (-(rate * t)) * (rate * t) ^ (n + 1) /
        ((n + 1).factorial : ℝ) := by
  rw [canonicalRenewalCount_succ_pmf_eq_arrivalCdfDiff hr n,
    arrivalTime_nat_succ_cdf_eq_erlangCDFCandidate n hr ht,
    arrivalTime_nat_succ_cdf_eq_erlangCDFCandidate (n + 1) hr ht]
  exact erlangCDFCandidate_sub_succ n rate t

theorem canonicalRenewalCount_succ_pmf_eq_poisson
    (n : ℕ) {rate t : ℝ} (hr : 0 < rate) (ht : 0 ≤ t) :
    (exponentialInterarrivalMeasure rate).real
        {ω | canonicalRenewalCount t ω = n + 1} =
      (ProbabilityTheory.poissonMeasure
        (⟨rate * t, mul_nonneg hr.le ht⟩ : ℝ≥0)).real {n + 1} := by
  rw [canonicalRenewalCount_succ_pmf_eq_erlang n hr ht,
    ProbabilityTheory.poissonMeasure_real_singleton]
  rfl

/-- The canonical exponential renewal count has the fixed-time Poisson PMF. -/
theorem canonicalRenewalCount_pmf_eq_poisson
    (n : ℕ) {rate t : ℝ} (hr : 0 < rate) (ht : 0 ≤ t) :
    (exponentialInterarrivalMeasure rate).real
        {ω | canonicalRenewalCount t ω = n} =
      (ProbabilityTheory.poissonMeasure
        (⟨rate * t, mul_nonneg hr.le ht⟩ : ℝ≥0)).real {n} := by
  cases n with
  | zero =>
      exact canonicalRenewalCount_zero_pmf_eq_poisson hr ht
  | succ n =>
      simpa [Nat.succ_eq_add_one] using
        canonicalRenewalCount_succ_pmf_eq_poisson n hr ht

/-- Equivalently, the fixed-time canonical renewal count has Mathlib's Poisson
law. -/
theorem canonicalRenewalCount_hasLaw_poisson
    {rate t : ℝ} (hr : 0 < rate) (ht : 0 ≤ t) :
    ProbabilityTheory.HasLaw (canonicalRenewalCount t)
      (ProbabilityTheory.poissonMeasure
        (⟨rate * t, mul_nonneg hr.le ht⟩ : ℝ≥0))
      (exponentialInterarrivalMeasure rate) := by
  refine ⟨(measurable_canonicalRenewalCount t).aemeasurable, ?_⟩
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hr
  apply (MeasureTheory.ext_iff_measureReal_singleton).mpr
  intro n
  calc
    (Measure.map (canonicalRenewalCount t)
        (exponentialInterarrivalMeasure rate)).real {n} =
        (exponentialInterarrivalMeasure rate).real
          {ω | canonicalRenewalCount t ω = n} := by
      simp only [measureReal_def]
      rw [Measure.map_apply (measurable_canonicalRenewalCount t)
        (measurableSet_singleton n)]
      congr 1
    _ = (ProbabilityTheory.poissonMeasure
        (⟨rate * t, mul_nonneg hr.le ht⟩ : ℝ≥0)).real {n} :=
      canonicalRenewalCount_pmf_eq_poisson n hr ht

/-- A fixed-time canonical exponential renewal count has a finite real first
moment.  This is transported from its exact Poisson marginal rather than
inferred from an asymptotic rate law. -/
theorem integrable_canonicalRenewalCount
    {rate t : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t) :
    Integrable (fun omega : ℕ → ℝ => (canonicalRenewalCount t omega : ℝ))
      (exponentialInterarrivalMeasure rate) := by
  let r : ℝ≥0 := ⟨rate * t, mul_nonneg hrate.le ht⟩
  have hcount := canonicalRenewalCount_hasLaw_poisson hrate ht
  have htarget : Integrable (fun n : ℕ => (n : ℝ))
      (Measure.map (canonicalRenewalCount t) (exponentialInterarrivalMeasure rate)) := by
    rw [hcount.map_eq]
    exact integrable_natCast_poissonMeasure r
  simpa [Function.comp_def] using
    htarget.comp_aemeasurable hcount.aemeasurable

/-- The expected fixed-time canonical exponential renewal count is its
Poisson exposure `rate * t`. -/
theorem integral_canonicalRenewalCount
    {rate t : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t) :
    ∫ omega : ℕ → ℝ, (canonicalRenewalCount t omega : ℝ)
      ∂exponentialInterarrivalMeasure rate = rate * t := by
  let r : ℝ≥0 := ⟨rate * t, mul_nonneg hrate.le ht⟩
  calc
    ∫ omega : ℕ → ℝ, (canonicalRenewalCount t omega : ℝ)
        ∂exponentialInterarrivalMeasure rate =
        ∫ n : ℕ, (n : ℝ) ∂ProbabilityTheory.poissonMeasure r := by
          simpa [r, Function.comp_def] using
            (canonicalRenewalCount_hasLaw_poisson hrate ht).integral_comp
              (f := fun n : ℕ => (n : ℝ))
              (measurable_of_countable _).aestronglyMeasurable
    _ = r := integral_id_poissonMeasure r
    _ = rate * t := rfl

/-- The squared fixed-time canonical renewal count is integrable. -/
theorem integrable_canonicalRenewalCount_sq
    {rate t : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t) :
    Integrable (fun omega : ℕ → ℝ => (canonicalRenewalCount t omega : ℝ) ^ 2)
      (exponentialInterarrivalMeasure rate) := by
  let r : ℝ≥0 := ⟨rate * t, mul_nonneg hrate.le ht⟩
  have hcount := canonicalRenewalCount_hasLaw_poisson hrate ht
  have htarget : Integrable (fun n : ℕ => (n : ℝ) ^ 2)
      (Measure.map (canonicalRenewalCount t) (exponentialInterarrivalMeasure rate)) := by
    rw [hcount.map_eq]
    exact integrable_natCast_sq_poissonMeasure r
  simpa [Function.comp_def] using htarget.comp_aemeasurable hcount.aemeasurable

/-- The second moment of a fixed-time canonical renewal count is its Poisson
parameter squared plus its parameter. -/
theorem integral_canonicalRenewalCount_sq
    {rate t : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t) :
    ∫ omega : ℕ → ℝ, (canonicalRenewalCount t omega : ℝ) ^ 2
      ∂exponentialInterarrivalMeasure rate = (rate * t) ^ 2 + rate * t := by
  let r : ℝ≥0 := ⟨rate * t, mul_nonneg hrate.le ht⟩
  calc
    ∫ omega : ℕ → ℝ, (canonicalRenewalCount t omega : ℝ) ^ 2
        ∂exponentialInterarrivalMeasure rate =
        ∫ n : ℕ, (n : ℝ) ^ 2 ∂ProbabilityTheory.poissonMeasure r := by
          simpa [r, Function.comp_def] using
            (canonicalRenewalCount_hasLaw_poisson hrate ht).integral_comp
              (f := fun n : ℕ => (n : ℝ) ^ 2)
              (measurable_of_countable _).aestronglyMeasurable
    _ = (r : ℝ) ^ 2 + r := integral_natCast_sq_poissonMeasure r
    _ = (rate * t) ^ 2 + rate * t := rfl

/-- A first-moment tail bound for the canonical Poisson renewal count.  This
is the direct Markov-inequality form used to choose deterministic clock
cutoffs in time-changed queueing paths. -/
theorem real_mul_measure_canonicalRenewalCount_ge_le
    {rate t threshold : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t)
    (hthreshold : 0 ≤ threshold) :
    threshold * (exponentialInterarrivalMeasure rate).real
      {omega | threshold ≤ (canonicalRenewalCount t omega : ℝ)} ≤
      rate * t := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  let count : (ℕ → ℝ) → ℝ := fun omega => (canonicalRenewalCount t omega : ℝ)
  let event : Set (ℕ → ℝ) := {omega | threshold ≤ count omega}
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsFiniteMeasure μ := by infer_instance
  have hcount_meas : Measurable count := by
    dsimp [count]
    exact (measurable_of_countable fun n : ℕ => (n : ℝ)).comp
      (measurable_canonicalRenewalCount t)
  have hevent_meas : MeasurableSet event := by
    dsimp [event]
    exact hcount_meas measurableSet_Ici
  have hcount_int : Integrable count μ := by
    simpa [μ, count] using integrable_canonicalRenewalCount hrate ht
  have hconst_int : Integrable (fun _ : ℕ → ℝ => threshold) (μ.restrict event) := by
    exact integrable_const _
  have hcount_int_restrict : Integrable count (μ.restrict event) := hcount_int.restrict
  have hconst_eq :
      (∫ _ : ℕ → ℝ, threshold ∂μ.restrict event) = threshold * μ.real event := by
    rw [integral_const]
    simp [smul_eq_mul, mul_comm]
  calc
    threshold * μ.real event = ∫ _ : ℕ → ℝ, threshold ∂μ.restrict event := hconst_eq.symm
    _ ≤ ∫ omega, count omega ∂μ.restrict event := by
      apply integral_mono_ae hconst_int hcount_int_restrict
      filter_upwards [ae_restrict_mem hevent_meas] with omega homega
      exact homega
    _ ≤ ∫ omega, count omega ∂μ := by
      exact setIntegral_le_integral hcount_int
        (Filter.Eventually.of_forall fun omega => by
          dsimp [count]
          exact_mod_cast Nat.zero_le (canonicalRenewalCount t omega))
    _ = rate * t := by
      simpa [μ, count] using integral_canonicalRenewalCount hrate ht

end
end PoissonProcess
end Probability
end AppliedModelingLib

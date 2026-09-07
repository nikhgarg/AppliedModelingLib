import AppliedModelingLib.Foundations.Probability.Exponential
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.HasLaw
import Mathlib.Probability.HasLawExists
import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Tactic

namespace AppliedModelingLib
namespace Probability
namespace PoissonProcess

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

/-!
# Poisson Process Likelihood Tools

This module provides reusable Poisson-count likelihood algebra and a narrow
certificate interface for homogeneous Poisson counting processes.  The goal is
to support papers that use Poisson arrivals, queues, reporting processes, and
renewal reductions without forcing every paper to rebuild the same count-PMF
or no-arrival algebra.

The sample-path construction of a Poisson process is intentionally separated
from the algebraic consequences.  A paper or future library module can provide
`HomogeneousCountProcessLaw`; downstream likelihood proofs can then use the
checked formulas below.

## Main declarations

- `rateExposureParam`: nonnegative real rate-exposure product as an `ℝ≥0`.
- `countLikelihood`: real Poisson probability mass at a count.
- `countLikelihood_eq_poissonMeasure_real_singleton`: agreement with mathlib's
  `ProbabilityTheory.poissonMeasure`.
- `countLikelihood_zero`: no-arrival probability.
- `hasSum_countLikelihood`: the count likelihoods sum to one.
- `ObservationWindow`: deterministic start/stop interval with nonnegative
  exposure.
- `IsStoppingTime` and `StoppingObservationWindow`: lightweight continuous-time
  filtration helpers showing that deterministic times, nonnegative shifts, and
  min-censored endpoints form stopping windows.
- `HomogeneousCountProcessLaw`: certificate interface for interval count laws.
- `HomogeneousArrivalDensityLaw` and `HomogeneousPoissonProcessLaw`:
  certificate interfaces for ordered arrival densities and shared-rate
  count/arrival process laws.
- `PoissonLikelihoodFactorization`: reusable statement that a likelihood
  factors into a `λ`-independent residual and a Poisson count likelihood.
- `PoissonThinningCountLaw`: reusable certificate for latent Poisson counts
  thinned by Bernoulli retention.
-/

/-- Nonnegative rate-exposure product as the `ℝ≥0` parameter of a Poisson law. -/
def rateExposureParam (rate exposure : ℝ)
    (h_nonneg : 0 ≤ rate * exposure) : ℝ≥0 :=
  ⟨rate * exposure, h_nonneg⟩

/-- Nonnegative rate-exposure parameter from nonnegative rate and exposure. -/
def rateExposureParamOfNonneg (rate exposure : ℝ)
    (h_rate : 0 ≤ rate) (h_exposure : 0 ≤ exposure) : ℝ≥0 :=
  rateExposureParam rate exposure (mul_nonneg h_rate h_exposure)

/-- Rate-exposure parameters add over adjacent nonnegative exposures. -/
theorem rateExposureParam_add
    (rate firstExposure secondExposure : ℝ)
    (h_rate : 0 ≤ rate) (h_first : 0 ≤ firstExposure) (h_second : 0 ≤ secondExposure) :
    rateExposureParam rate (firstExposure + secondExposure)
      (mul_nonneg h_rate (add_nonneg h_first h_second)) =
      rateExposureParam rate firstExposure (mul_nonneg h_rate h_first) +
        rateExposureParam rate secondExposure (mul_nonneg h_rate h_second) := by
  apply Subtype.ext
  change rate * (firstExposure + secondExposure) =
    rate * firstExposure + rate * secondExposure
  ring

/--
Real-valued Poisson count likelihood for rate `rate`, exposure length
`exposure`, and count `n`.

This is the common real-valued form
`exp (-(rate * exposure)) * (rate * exposure)^n / n!`.
-/
def countLikelihood (rate exposure : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-(rate * exposure)) * (rate * exposure) ^ n /
    (n.factorial : ℝ)

/-- Real-valued mass of a mathlib Poisson measure at count `n`. -/
def countPMF (mean : ℝ≥0) (n : ℕ) : ℝ :=
  (ProbabilityTheory.poissonMeasure mean).real {n}

theorem countPMF_eq (mean : ℝ≥0) (n : ℕ) :
    countPMF mean n =
      Real.exp (-(mean : ℝ)) * (mean : ℝ) ^ n / (n.factorial : ℝ) := by
  simpa [countPMF] using
    (ProbabilityTheory.poissonMeasure_real_singleton mean n)

/-! ## Existence of independent Poisson increments on finite schedules -/

universe u

/--
Existence of independent Poisson random variables with prescribed nonnegative
means.

This is the reusable finite-dimensional construction step for Poisson-process
arguments: a full continuous-time process can later be obtained from a
projective-limit construction, while finite likelihood calculations only need
independent increments on the finite observation schedule.
-/
theorem exists_iIndepFun_poisson_counts
    {ι : Type u} (mean : ι → ℝ≥0) :
    ∃ Ω : Type u, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ X : ι → Ω → ℕ,
        (∀ i, Measurable (X i)) ∧
        (∀ i,
          ProbabilityTheory.HasLaw
            (X i) (ProbabilityTheory.poissonMeasure (mean i)) P) ∧
        ProbabilityTheory.iIndepFun X P ∧ IsProbabilityMeasure P := by
  exact
    ProbabilityTheory.exists_hasLaw_indepFun
      (fun _ : ι => ℕ)
      (fun i => ProbabilityTheory.poissonMeasure (mean i))

/--
Existence of independent Poisson count increments with means `rate * exposure i`.
-/
theorem exists_iIndepFun_poisson_increments
    {ι : Type u} (rate : ℝ) (h_rate : 0 ≤ rate)
    (exposure : ι → ℝ) (h_exposure : ∀ i, 0 ≤ exposure i) :
    ∃ Ω : Type u, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ X : ι → Ω → ℕ,
        (∀ i, Measurable (X i)) ∧
        (∀ i,
          ProbabilityTheory.HasLaw
            (X i)
            (ProbabilityTheory.poissonMeasure
              (rateExposureParam rate (exposure i)
                (mul_nonneg h_rate (h_exposure i)))) P) ∧
        ProbabilityTheory.iIndepFun X P ∧ IsProbabilityMeasure P := by
  exact
    exists_iIndepFun_poisson_counts
      (fun i =>
        rateExposureParam rate (exposure i)
          (mul_nonneg h_rate (h_exposure i)))

/--
Existence of independent Poisson increments on a finite adjacent time schedule.

For a monotone timeline `t : Fin (n+1) → ℝ`, this constructs independent
increment-count random variables for the adjacent windows
`[t i.castSucc, t i.succ]`, each with Poisson mean
`rate * (t i.succ - t i.castSucc)`.
-/
theorem exists_iIndepFun_poisson_adjacent_interval_counts_fin
    (rate : ℝ) (h_rate : 0 ≤ rate)
    {n : ℕ} (t : Fin (n + 1) → ℝ) (ht : Monotone t) :
    ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ X : Fin n → Ω → ℕ,
        (∀ i, Measurable (X i)) ∧
        (∀ i,
          ProbabilityTheory.HasLaw
            (X i)
            (ProbabilityTheory.poissonMeasure
              (rateExposureParam rate (t i.succ - t i.castSucc)
                (mul_nonneg h_rate
                  (sub_nonneg.mpr (ht (Fin.castSucc_le_succ i)))))) P) ∧
        ProbabilityTheory.iIndepFun X P ∧ IsProbabilityMeasure P := by
  exact
    exists_iIndepFun_poisson_increments rate h_rate
      (fun i : Fin n => t i.succ - t i.castSucc)
      (fun i => sub_nonneg.mpr (ht (Fin.castSucc_le_succ i)))

/-- The real count likelihood agrees with mathlib's Poisson measure. -/
theorem countLikelihood_eq_poissonMeasure_real_singleton
    {rate exposure : ℝ} (h_nonneg : 0 ≤ rate * exposure) (n : ℕ) :
    countLikelihood rate exposure n =
      (ProbabilityTheory.poissonMeasure
        (rateExposureParam rate exposure h_nonneg)).real {n} := by
  rw [ProbabilityTheory.poissonMeasure_real_singleton]
  change countLikelihood rate exposure n =
    Real.exp (-(rate * exposure)) * (rate * exposure) ^ n /
      (n.factorial : ℝ)
  rfl

/--
If an integer-valued random variable has a mathlib Poisson law with
rate-exposure parameter, then its real singleton event probability is the
corresponding real Poisson count likelihood.
-/
theorem hasLaw_poissonMeasure_real_singleton_eq_countLikelihood
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℕ} {rate exposure : ℝ}
    (h_nonneg : 0 ≤ rate * exposure)
    (hX : ProbabilityTheory.HasLaw X
      (ProbabilityTheory.poissonMeasure
        (rateExposureParam rate exposure h_nonneg)) P)
    (n : ℕ) :
    P.real {ω : Ω | X ω = n} =
      countLikelihood rate exposure n := by
  rw [Measure.real_def]
  change (P (X ⁻¹' ({n} : Set ℕ))).toReal =
    countLikelihood rate exposure n
  rw [← Measure.map_apply_of_aemeasurable
    hX.aemeasurable (measurableSet_singleton n)]
  change (P.map X).real ({n} : Set ℕ) =
    countLikelihood rate exposure n
  rw [hX.map_eq]
  rw [countLikelihood_eq_poissonMeasure_real_singleton h_nonneg n]

/--
Existence of a single Poisson count with a prescribed nonnegative mean,
together with its real singleton probabilities in `countLikelihood` form.
-/
theorem exists_poisson_count_real_eq_countLikelihood
    (mean : ℝ) (h_mean : 0 ≤ mean) :
    ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ X : Ω → ℕ,
        Measurable X ∧
        ProbabilityTheory.HasLaw X
          (ProbabilityTheory.poissonMeasure
            (rateExposureParam 1 mean (by simpa using h_mean))) P ∧
        IsProbabilityMeasure P ∧
        ∀ n : ℕ, P.real {ω : Ω | X ω = n} =
          countLikelihood 1 mean n := by
  have h_nonneg : 0 ≤ (1 : ℝ) * mean := by
    simpa using h_mean
  rcases exists_iIndepFun_poisson_counts
      (ι := PUnit)
      (fun _ => rateExposureParam 1 mean h_nonneg) with
    ⟨Ω, mΩ, P, X, hmeas, hLaw, _hind, hprob⟩
  refine ⟨Ω, mΩ, P, X PUnit.unit, hmeas PUnit.unit,
    hLaw PUnit.unit, hprob, ?_⟩
  intro n
  exact hasLaw_poissonMeasure_real_singleton_eq_countLikelihood
    h_nonneg (hLaw PUnit.unit) n

/--
Existence of a single Poisson count with mean `rate * exposure`, stated in the
paper-facing rate/exposure likelihood form.
-/
theorem exists_poisson_count_rate_exposure_real_eq_countLikelihood
    (rate exposure : ℝ) (h_nonneg : 0 ≤ rate * exposure) :
    ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ X : Ω → ℕ,
        Measurable X ∧
        ProbabilityTheory.HasLaw X
          (ProbabilityTheory.poissonMeasure
            (rateExposureParam rate exposure h_nonneg)) P ∧
        IsProbabilityMeasure P ∧
        ∀ n : ℕ, P.real {ω : Ω | X ω = n} =
          countLikelihood rate exposure n := by
  rcases exists_iIndepFun_poisson_counts
      (ι := PUnit)
      (fun _ => rateExposureParam rate exposure h_nonneg) with
    ⟨Ω, mΩ, P, X, hmeas, hLaw, _hind, hprob⟩
  refine ⟨Ω, mΩ, P, X PUnit.unit, hmeas PUnit.unit,
    hLaw PUnit.unit, hprob, ?_⟩
  intro n
  exact hasLaw_poissonMeasure_real_singleton_eq_countLikelihood
    h_nonneg (hLaw PUnit.unit) n

/--
Existence of a single Poisson count with rate/exposure parameters supplied as
separate nonnegative quantities.
-/
theorem exists_poisson_count_rate_exposure_of_nonneg
    (rate exposure : ℝ) (h_rate : 0 ≤ rate) (h_exposure : 0 ≤ exposure) :
    ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ X : Ω → ℕ,
        Measurable X ∧
        ProbabilityTheory.HasLaw X
          (ProbabilityTheory.poissonMeasure
            (rateExposureParam rate exposure
              (mul_nonneg h_rate h_exposure))) P ∧
        IsProbabilityMeasure P ∧
        ∀ n : ℕ, P.real {ω : Ω | X ω = n} =
          countLikelihood rate exposure n :=
  exists_poisson_count_rate_exposure_real_eq_countLikelihood
    rate exposure (mul_nonneg h_rate h_exposure)

theorem countLikelihood_eq_countPMF
    {rate exposure : ℝ} (h_nonneg : 0 ≤ rate * exposure) (n : ℕ) :
    countLikelihood rate exposure n =
      countPMF (rateExposureParam rate exposure h_nonneg) n := by
  rw [countLikelihood_eq_poissonMeasure_real_singleton h_nonneg n]
  rfl

/-- Poisson count likelihoods are nonnegative for nonnegative mean. -/
theorem countLikelihood_nonneg
    {rate exposure : ℝ} (h_nonneg : 0 ≤ rate * exposure) (n : ℕ) :
    0 ≤ countLikelihood rate exposure n := by
  rw [countLikelihood_eq_poissonMeasure_real_singleton h_nonneg n]
  exact measureReal_nonneg

/-- Poisson count likelihoods are positive for positive rate and exposure. -/
theorem countLikelihood_pos
    {rate exposure : ℝ} (h_rate : 0 < rate) (h_exposure : 0 < exposure)
    (n : ℕ) :
    0 < countLikelihood rate exposure n := by
  have h_param : 0 < rate * exposure := mul_pos h_rate h_exposure
  rw [countLikelihood_eq_poissonMeasure_real_singleton (le_of_lt h_param) n]
  exact ProbabilityTheory.poissonMeasure_real_singleton_pos n
    (show 0 < rateExposureParam rate exposure (le_of_lt h_param) by
      simpa [rateExposureParam] using h_param)

@[simp] theorem countLikelihood_zero (rate exposure : ℝ) :
    countLikelihood rate exposure 0 =
      Real.exp (-(rate * exposure)) := by
  simp [countLikelihood]

/-- One-arrival likelihood in closed form. -/
theorem countLikelihood_one (rate exposure : ℝ) :
    countLikelihood rate exposure 1 =
      Real.exp (-(rate * exposure)) * (rate * exposure) := by
  simp [countLikelihood]

/--
Finite binomial/factorial split identity behind addition of independent Poisson
counts.
-/
theorem sum_pow_div_factorial_mul_pow_div_factorial
    (x y : ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
        x ^ k / (k.factorial : ℝ) *
          (y ^ (n - k) / ((n - k).factorial : ℝ))) =
      (x + y) ^ n / (n.factorial : ℝ) := by
  rw [add_pow]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hfacn : (n.factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hfack : (k.factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  have hfacnk : ((n - k).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n - k)
  have hchoose_nat :
      n.choose k * k.factorial * (n - k).factorial = n.factorial :=
    Nat.choose_mul_factorial_mul_factorial hk_le
  have hchoose :
      (n.choose k : ℝ) * (k.factorial : ℝ) *
          ((n - k).factorial : ℝ) =
        (n.factorial : ℝ) := by
    exact_mod_cast hchoose_nat
  field_simp [hfacn, hfack, hfacnk]
  rw [← hchoose]
  ring

/--
Binary aggregation of Poisson count likelihoods: summing over all splits of a
total count gives the likelihood for the combined exposure.
-/
theorem sum_countLikelihood_split_eq_countLikelihood_add
    (rate exposure₁ exposure₂ : ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
        countLikelihood rate exposure₁ k *
          countLikelihood rate exposure₂ (n - k)) =
      countLikelihood rate (exposure₁ + exposure₂) n := by
  rw [countLikelihood]
  simp only [countLikelihood]
  have hsum :=
    sum_pow_div_factorial_mul_pow_div_factorial
      (rate * exposure₁) (rate * exposure₂) n
  calc
    (∑ k ∈ Finset.range (n + 1),
        Real.exp (-(rate * exposure₁)) *
            (rate * exposure₁) ^ k / (k.factorial : ℝ) *
          (Real.exp (-(rate * exposure₂)) *
            (rate * exposure₂) ^ (n - k) /
              ((n - k).factorial : ℝ))) =
        Real.exp (-(rate * exposure₁)) *
          Real.exp (-(rate * exposure₂)) *
          (∑ k ∈ Finset.range (n + 1),
              (rate * exposure₁) ^ k / (k.factorial : ℝ) *
                ((rate * exposure₂) ^ (n - k) /
                  ((n - k).factorial : ℝ))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro k _hk
      ring
    _ = Real.exp (-(rate * exposure₁)) *
          Real.exp (-(rate * exposure₂)) *
          ((rate * exposure₁ + rate * exposure₂) ^ n /
            (n.factorial : ℝ)) := by
      rw [hsum]
    _ = Real.exp (-(rate * (exposure₁ + exposure₂))) *
          (rate * (exposure₁ + exposure₂)) ^ n /
            (n.factorial : ℝ) := by
      rw [← Real.exp_add]
      ring_nf

/--
If two natural-valued counts have the product Poisson joint PMF, then their
sum has the Poisson PMF for the combined exposure.

This is the finite event-partition form of the binary Poisson-addition law,
stated without committing to a particular construction of the pair.
-/
theorem pair_count_sum_real_eq_countLikelihood_add
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {X Y : Ω → ℕ} (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    {rate exposure₁ exposure₂ : ℝ}
    (hJoint : ∀ a b : ℕ,
      P.real ({ω : Ω | X ω = a} ∩ {ω : Ω | Y ω = b}) =
        countLikelihood rate exposure₁ a *
          countLikelihood rate exposure₂ b)
    (n : ℕ) :
    P.real {ω : Ω | X ω + Y ω = n} =
      countLikelihood rate (exposure₁ + exposure₂) n := by
  classical
  let A : ℕ → Set Ω := fun k =>
    {ω : Ω | X ω = k} ∩ {ω : Ω | Y ω = n - k}
  have hnull : ∀ k ∈ Finset.range (n + 1), NullMeasurableSet (A k) P := by
    intro k _hk
    exact (hX.nullMeasurableSet_preimage (measurableSet_singleton k)).inter
      (hY.nullMeasurableSet_preimage (measurableSet_singleton (n - k)))
  have hdis :
      Set.Pairwise (↑(Finset.range (n + 1)) : Set ℕ)
        (fun a b => AEDisjoint P (A a) (A b)) := by
    intro a _ha b _hb hab
    have hdisjoint : Disjoint (A a) (A b) := by
      rw [Set.disjoint_left]
      intro ω hωa hωb
      exact hab (hωa.1.symm.trans hωb.1)
    exact hdisjoint.aedisjoint
  have hUnion :
      {ω : Ω | X ω + Y ω = n} =
        ⋃ k ∈ Finset.range (n + 1), A k := by
    ext ω
    constructor
    · intro hsum
      refine Set.mem_iUnion.mpr ⟨X ω, ?_⟩
      refine Set.mem_iUnion.mpr ⟨?_, ?_⟩
      · change X ω + Y ω = n at hsum
        exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (by omega))
      · change X ω + Y ω = n at hsum
        have hYeq : Y ω = n - X ω := by omega
        exact ⟨rfl, hYeq⟩
    · intro hω
      rcases Set.mem_iUnion.mp hω with ⟨k, hk⟩
      rcases Set.mem_iUnion.mp hk with ⟨hk_range, hA⟩
      have hk_le : k ≤ n :=
        Nat.lt_succ_iff.mp (Finset.mem_range.mp hk_range)
      rcases hA with ⟨hXk, hYk⟩
      change X ω = k at hXk
      change Y ω = n - k at hYk
      change X ω + Y ω = n
      omega
  calc
    P.real {ω : Ω | X ω + Y ω = n} =
        P.real (⋃ k ∈ Finset.range (n + 1), A k) := by
      rw [hUnion]
    _ = ∑ k ∈ Finset.range (n + 1), P.real (A k) := by
      exact measureReal_biUnion_finset₀ hdis hnull
    _ = ∑ k ∈ Finset.range (n + 1),
          countLikelihood rate exposure₁ k *
            countLikelihood rate exposure₂ (n - k) := by
      refine Finset.sum_congr rfl ?_
      intro k _hk
      exact hJoint k (n - k)
    _ = countLikelihood rate (exposure₁ + exposure₂) n := by
      exact sum_countLikelihood_split_eq_countLikelihood_add
        rate exposure₁ exposure₂ n

/-- No-arrival survival factor for a homogeneous Poisson interval. -/
def noArrivalProb (rate exposure : ℝ) : ℝ :=
  Real.exp (-(rate * exposure))

/-- Probability of at least one arrival in a homogeneous Poisson interval. -/
def atLeastOneArrivalProb (rate exposure : ℝ) : ℝ :=
  1 - noArrivalProb rate exposure

@[simp] theorem noArrivalProb_eq_countLikelihood_zero
    (rate exposure : ℝ) :
    noArrivalProb rate exposure = countLikelihood rate exposure 0 := by
  simp [noArrivalProb]

theorem atLeastOneArrivalProb_eq_one_sub_countLikelihood_zero
    (rate exposure : ℝ) :
    atLeastOneArrivalProb rate exposure =
      1 - countLikelihood rate exposure 0 := by
  simp [atLeastOneArrivalProb]

theorem noArrivalProb_pos (rate exposure : ℝ) :
    0 < noArrivalProb rate exposure := by
  exact Real.exp_pos _

theorem noArrivalProb_nonneg (rate exposure : ℝ) :
    0 ≤ noArrivalProb rate exposure :=
  le_of_lt (noArrivalProb_pos rate exposure)

theorem noArrivalProb_le_one
    {rate exposure : ℝ} (h_nonneg : 0 ≤ rate * exposure) :
    noArrivalProb rate exposure ≤ 1 := by
  rw [noArrivalProb, Real.exp_le_one_iff]
  linarith

theorem atLeastOneArrivalProb_nonneg
    {rate exposure : ℝ} (h_nonneg : 0 ≤ rate * exposure) :
    0 ≤ atLeastOneArrivalProb rate exposure := by
  unfold atLeastOneArrivalProb
  linarith [noArrivalProb_le_one h_nonneg]

theorem atLeastOneArrivalProb_le_one (rate exposure : ℝ) :
    atLeastOneArrivalProb rate exposure ≤ 1 := by
  unfold atLeastOneArrivalProb
  linarith [noArrivalProb_nonneg rate exposure]

theorem atLeastOneArrivalProb_pos
    {rate exposure : ℝ} (h_rate : 0 < rate) (h_exposure : 0 < exposure) :
    0 < atLeastOneArrivalProb rate exposure := by
  have hpos : 0 < rate * exposure := mul_pos h_rate h_exposure
  have hlt : noArrivalProb rate exposure < 1 := by
    rw [noArrivalProb, Real.exp_lt_one_iff]
    linarith
  unfold atLeastOneArrivalProb
  linarith

theorem noArrivalProb_add_atLeastOneArrivalProb
    (rate exposure : ℝ) :
    noArrivalProb rate exposure +
      atLeastOneArrivalProb rate exposure = 1 := by
  simp [atLeastOneArrivalProb]

/-! ## Interarrival Timelines -/

/--
Endpoint timeline generated by an observation start time and an indexed family
of observed jump times: endpoint `0` is the start, endpoint `i+1` is jump `i`.
-/
def jumpTimelineEndpoint (start : ℝ) (jumpTime : ℕ → ℝ) : ℕ → ℝ
  | 0 => start
  | i + 1 => jumpTime i

/-- The `i`th observed interarrival gap in a jump timeline. -/
def interarrivalGapFromJumpTimes
    (start : ℝ) (jumpTime : ℕ → ℝ) (i : ℕ) : ℝ :=
  jumpTimelineEndpoint start jumpTime (i + 1) -
    jumpTimelineEndpoint start jumpTime i

/-- Terminal no-arrival tail after the last counted jump in a jump timeline. -/
def terminalTailFromJumpTimes
    (start endTime : ℝ) (jumpTime : ℕ → ℝ) (count : ℕ) : ℝ :=
  endTime - jumpTimelineEndpoint start jumpTime count

/--
Interarrival gaps plus the terminal tail telescope to total exposure.  This is
the paper-neutral time-accounting lemma behind Appendix B.2's
`(t_{m+1}-s) + ... + (e-t_{m+M}) = e-s` step.
-/
theorem sum_interarrivalGapFromJumpTimes_add_terminalTail
    (start endTime : ℝ) (jumpTime : ℕ → ℝ) (count : ℕ) :
    (∑ i ∈ Finset.range count,
        interarrivalGapFromJumpTimes start jumpTime i) +
      terminalTailFromJumpTimes start endTime jumpTime count =
        endTime - start := by
  have htel :
      (∑ i ∈ Finset.range count,
          (jumpTimelineEndpoint start jumpTime (i + 1) -
            jumpTimelineEndpoint start jumpTime i)) =
        jumpTimelineEndpoint start jumpTime count -
          jumpTimelineEndpoint start jumpTime 0 := by
    exact Finset.sum_range_sub (jumpTimelineEndpoint start jumpTime) count
  simp only [interarrivalGapFromJumpTimes, terminalTailFromJumpTimes]
  rw [htel]
  simp [jumpTimelineEndpoint]

/--
Finite-index version of `sum_interarrivalGapFromJumpTimes_add_terminalTail`,
matching observation records indexed by `Fin count`.
-/
theorem sum_fin_interarrivalGapFromJumpTimes_add_terminalTail
    (start endTime : ℝ) (jumpTime : ℕ → ℝ) (count : ℕ) :
    (∑ j : Fin count,
        interarrivalGapFromJumpTimes start jumpTime j.val) +
      terminalTailFromJumpTimes start endTime jumpTime count =
        endTime - start := by
  rw [Fin.sum_univ_eq_sum_range]
  exact sum_interarrivalGapFromJumpTimes_add_terminalTail
    start endTime jumpTime count

/-- Interarrival gaps are nonnegative along a monotone jump timeline. -/
theorem interarrivalGapFromJumpTimes_nonneg_of_monotone
    {start : ℝ} {jumpTime : ℕ → ℝ}
    (hmono : Monotone (jumpTimelineEndpoint start jumpTime)) (i : ℕ) :
    0 ≤ interarrivalGapFromJumpTimes start jumpTime i := by
  exact sub_nonneg.mpr (hmono (Nat.le_succ i))

/-- The terminal tail is nonnegative when the last endpoint is before the window end. -/
theorem terminalTailFromJumpTimes_nonneg
    {start endTime : ℝ} {jumpTime : ℕ → ℝ} {count : ℕ}
    (hlast : jumpTimelineEndpoint start jumpTime count ≤ endTime) :
    0 ≤ terminalTailFromJumpTimes start endTime jumpTime count := by
  exact sub_nonneg.mpr hlast

/--
Finite-index interarrival gaps are nonnegative along a monotone jump timeline.
-/
theorem interarrivalGapFromJumpTimes_fin_nonneg_of_monotone
    {start : ℝ} {jumpTime : ℕ → ℝ} {count : ℕ}
    (hmono : Monotone (jumpTimelineEndpoint start jumpTime)) (j : Fin count) :
    0 ≤ interarrivalGapFromJumpTimes start jumpTime j.val :=
  interarrivalGapFromJumpTimes_nonneg_of_monotone hmono j.val

/-- Density kernel for one homogeneous Poisson interarrival gap. -/
def interarrivalDensityKernel (rate gap : ℝ) : ℝ :=
  rate * Real.exp (-(rate * gap))

theorem interarrivalDensityKernel_nonneg
    {rate gap : ℝ} (h_rate : 0 ≤ rate) :
    0 ≤ interarrivalDensityKernel rate gap := by
  exact mul_nonneg h_rate (le_of_lt (Real.exp_pos _))

/--
The interarrival-density kernel agrees with the real PDF of the exponential
waiting-time model on nonnegative gaps.
-/
theorem interarrivalDensityKernel_eq_exponential_pdfReal
    (rate : ℝ) (h_rate : 0 < rate) {gap : ℝ} (h_gap : 0 ≤ gap) :
    interarrivalDensityKernel rate gap =
      (Exponential.Model.mk rate h_rate).pdfReal gap := by
  simp [interarrivalDensityKernel, Exponential.Model.pdfReal,
    ProbabilityTheory.exponentialPDFReal, ProbabilityTheory.gammaPDFReal,
    h_gap]

/--
Product of homogeneous Poisson interarrival density kernels followed by a
terminal no-arrival survival factor.
-/
def interarrivalTailLikelihood
    {ι : Type*} (s : Finset ι) (rate : ℝ)
    (gap : ι → ℝ) (tail : ℝ) : ℝ :=
  (∏ i ∈ s, interarrivalDensityKernel rate (gap i)) *
    noArrivalProb rate tail

theorem interarrivalTailLikelihood_nonneg
    {ι : Type*} (s : Finset ι) {rate : ℝ}
    (gap : ι → ℝ) (tail : ℝ) (h_rate : 0 ≤ rate) :
    0 ≤ interarrivalTailLikelihood s rate gap tail := by
  exact mul_nonneg
    (Finset.prod_nonneg fun i _hi =>
      interarrivalDensityKernel_nonneg (rate := rate) (gap := gap i) h_rate)
    (noArrivalProb_nonneg rate tail)

/--
Measure-facing form of the finite interarrival-product-plus-tail kernel:
product of exponential PDFs for the observed gaps times exponential survival
for the terminal tail.
-/
theorem interarrivalTailLikelihood_eq_exponential_pdfReal_prod_mul_tail
    {ι : Type*} (s : Finset ι) (rate : ℝ) (h_rate : 0 < rate)
    (gap : ι → ℝ) (tail : ℝ)
    (h_gap : ∀ i ∈ s, 0 ≤ gap i) (h_tail : 0 ≤ tail) :
    interarrivalTailLikelihood s rate gap tail =
      (∏ i ∈ s,
          (Exponential.Model.mk rate h_rate).pdfReal (gap i)) *
        ((Exponential.Model.mk rate h_rate).measure
          (Set.Ioi tail)).toReal := by
  rw [interarrivalTailLikelihood]
  congr 1
  · exact Finset.prod_congr rfl fun i hi =>
      interarrivalDensityKernel_eq_exponential_pdfReal
        rate h_rate (h_gap i hi)
  · rw [Exponential.Model.measure_Ioi_toReal
      (M := Exponential.Model.mk rate h_rate) h_tail]
    rfl

theorem prod_interarrivalDensityKernel_eq_rawShape
    {ι : Type*} (s : Finset ι) (rate : ℝ) (gap : ι → ℝ) :
    (∏ i ∈ s, interarrivalDensityKernel rate (gap i)) =
      rate ^ s.card * Real.exp (-(rate * ∑ i ∈ s, gap i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [interarrivalDensityKernel]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, ih]
      simp [interarrivalDensityKernel, Finset.sum_insert ha]
      rw [Finset.card_insert_of_notMem ha, pow_succ]
      rw [show -(rate * (gap a + ∑ i ∈ s, gap i)) =
          -(rate * gap a) + -(rate * ∑ i ∈ s, gap i) by ring,
        Real.exp_add]
      ring_nf

/--
Product of interarrival density kernels followed by a no-arrival tail.  This is
the algebraic collection step used in finite-dimensional Poisson process
likelihood calculations.
-/
theorem prod_interarrivalDensityKernel_mul_noArrivalProb_eq_rawShape
    {ι : Type*} (s : Finset ι) (rate : ℝ) (gap : ι → ℝ) (tail : ℝ) :
    (∏ i ∈ s, interarrivalDensityKernel rate (gap i)) *
        noArrivalProb rate tail =
      rate ^ s.card * Real.exp (-(rate * ((∑ i ∈ s, gap i) + tail))) := by
  rw [prod_interarrivalDensityKernel_eq_rawShape, noArrivalProb]
  rw [show -(rate * ((∑ i ∈ s, gap i) + tail)) =
      -(rate * ∑ i ∈ s, gap i) + -(rate * tail) by ring,
    Real.exp_add]
  ring

theorem interarrivalTailLikelihood_eq_rawShape
    {ι : Type*} (s : Finset ι) (rate : ℝ) (gap : ι → ℝ) (tail : ℝ) :
    interarrivalTailLikelihood s rate gap tail =
      rate ^ s.card * Real.exp (-(rate * ((∑ i ∈ s, gap i) + tail))) := by
  exact prod_interarrivalDensityKernel_mul_noArrivalProb_eq_rawShape
    s rate gap tail

theorem interarrivalTailLikelihood_eq_exposure_rawShape
    {ι : Type*} (s : Finset ι) {rate exposure tail : ℝ}
    (gap : ι → ℝ)
    (hexposure : (∑ i ∈ s, gap i) + tail = exposure) :
    interarrivalTailLikelihood s rate gap tail =
      rate ^ s.card * Real.exp (-(rate * exposure)) := by
  rw [interarrivalTailLikelihood_eq_rawShape, hexposure]

/--
No-arrival probability over an interval agrees with the survival probability of
the exponential waiting-time model with the same positive rate.
-/
theorem noArrivalProb_eq_exponential_tail
    (rate : ℝ) (h_rate : 0 < rate)
    {exposure : ℝ} (h_exposure : 0 ≤ exposure) :
    noArrivalProb rate exposure =
      ((Exponential.Model.mk rate h_rate).measure (Set.Ioi exposure)).toReal := by
  rw [Exponential.Model.measure_Ioi_toReal
    (M := Exponential.Model.mk rate h_rate) h_exposure]
  rfl

/-- No-arrival probabilities multiply across independent rates on the same exposure. -/
theorem noArrivalProb_add_rates (rate₁ rate₂ exposure : ℝ) :
    noArrivalProb (rate₁ + rate₂) exposure =
      noArrivalProb rate₁ exposure * noArrivalProb rate₂ exposure := by
  rw [noArrivalProb, noArrivalProb, noArrivalProb, ← Real.exp_add]
  congr 1
  ring

/-- No-arrival probabilities multiply across adjacent exposures at the same rate. -/
theorem noArrivalProb_add_exposures (rate exposure₁ exposure₂ : ℝ) :
    noArrivalProb rate (exposure₁ + exposure₂) =
      noArrivalProb rate exposure₁ * noArrivalProb rate exposure₂ := by
  rw [noArrivalProb, noArrivalProb, noArrivalProb, ← Real.exp_add]
  congr 1
  ring

/--
Memoryless tail-ratio algebra for a homogeneous no-arrival probability:
conditioning on no arrival through `elapsed` leaves the same no-arrival tail
over an additional `future` interval.
-/
theorem noArrivalProb_add_div_noArrivalProb_left
    (rate elapsed future : ℝ) :
    noArrivalProb rate (elapsed + future) / noArrivalProb rate elapsed =
      noArrivalProb rate future := by
  have hden : Real.exp (-(rate * elapsed)) ≠ 0 :=
    Real.exp_ne_zero _
  rw [noArrivalProb, noArrivalProb, noArrivalProb]
  rw [div_eq_iff hden]
  rw [← Real.exp_add]
  congr 1
  ring

/--
Mixing a no-arrival tail that is independent of the start variable against any
normalized real density leaves the same no-arrival tail.
-/
theorem noArrivalProb_density_mixture_measure_eq_self
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (rate exposure : ℝ) {density : α → ℝ}
    (h_density_mass : ∫ x, density x ∂μ = 1) :
    ∫ x, noArrivalProb rate exposure * density x ∂μ =
      noArrivalProb rate exposure := by
  rw [MeasureTheory.integral_const_mul]
  rw [h_density_mass]
  ring

/--
Mixing a no-arrival tail that is independent of the start time against a
normalized real density leaves the same no-arrival tail.

This is the reusable algebra behind arguments that condition on a random
observation start but use the memoryless property to remove the start time from
the future no-arrival factor.
-/
theorem noArrivalProb_density_mixture_eq_self
    (rate exposure : ℝ) {density : ℝ → ℝ}
    (h_density_mass : ∫ s, density s = 1) :
    ∫ s, noArrivalProb rate exposure * density s =
      noArrivalProb rate exposure := by
  exact noArrivalProb_density_mixture_measure_eq_self
    volume rate exposure h_density_mass

/--
Restricted-start version of `noArrivalProb_density_mixture_eq_self`, for
mixtures that integrate over starts `s ≥ lower`.
-/
theorem noArrivalProb_density_mixture_restrict_Ici_eq_self
    (rate exposure lower : ℝ) {density : ℝ → ℝ}
    (h_density_mass :
      ∫ s, density s ∂(volume.restrict (Set.Ici lower)) = 1) :
    ∫ s, noArrivalProb rate exposure * density s
        ∂(volume.restrict (Set.Ici lower)) =
      noArrivalProb rate exposure := by
  exact noArrivalProb_density_mixture_measure_eq_self
    (volume.restrict (Set.Ici lower)) rate exposure h_density_mass

/--
Finite product of no-arrival probabilities for rates sharing the same exposure.
This is the algebraic core of independent competing Poisson clocks.
-/
theorem prod_noArrivalProb_eq_noArrivalProb_sum_rates
    {ι : Type*} (s : Finset ι) (rate : ι → ℝ) (exposure : ℝ) :
    (∏ i ∈ s, noArrivalProb (rate i) exposure) =
      noArrivalProb (∑ i ∈ s, rate i) exposure := by
  classical
  rw [noArrivalProb]
  simp_rw [noArrivalProb]
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.sum_mul]
  rw [Finset.sum_neg_distrib]

/--
Finite product of no-arrival probabilities for exposures sharing the same rate.
This is the algebraic core of splitting a homogeneous interval into pieces.
-/
theorem prod_noArrivalProb_eq_noArrivalProb_sum_exposures
    {ι : Type*} (s : Finset ι) (rate : ℝ) (exposure : ι → ℝ) :
    (∏ i ∈ s, noArrivalProb rate (exposure i)) =
      noArrivalProb rate (∑ i ∈ s, exposure i) := by
  classical
  rw [noArrivalProb]
  simp_rw [noArrivalProb]
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum]
  rw [Finset.sum_neg_distrib]

/-- The count likelihoods sum to one for nonnegative rate-exposure product. -/
theorem hasSum_countLikelihood
    {rate exposure : ℝ} (h_nonneg : 0 ≤ rate * exposure) :
    HasSum (fun n : ℕ => countLikelihood rate exposure n) 1 := by
  simpa [countLikelihood, rateExposureParam] using
    (ProbabilityTheory.hasSum_one_poissonMeasure
      (rateExposureParam rate exposure h_nonneg))

/-- Tsum form of `hasSum_countLikelihood`: Poisson count probabilities total one. -/
theorem tsum_countLikelihood
    {rate exposure : ℝ} (h_nonneg : 0 ≤ rate * exposure) :
    (∑' n : ℕ, countLikelihood rate exposure n) = 1 :=
  (hasSum_countLikelihood h_nonneg).tsum_eq

/--
Lebesgue volume of the ordered `count`-jump simplex inside a deterministic
window of length `exposure`, in the standard homogeneous Poisson density
normalization.
-/
def orderedJumpSimplexVolume (exposure : ℝ) (count : ℕ) : ℝ :=
  exposure ^ count / (count.factorial : ℝ)

/--
Recursive ordered-simplex volume identity: adding one ordered jump integrates
the previous simplex volume over the last-jump location.
-/
theorem integral_orderedJumpSimplexVolume_eq_succ
    (exposure : ℝ) (count : ℕ) :
    (∫ x in (0 : ℝ)..exposure, orderedJumpSimplexVolume x count) =
      orderedJumpSimplexVolume exposure (count + 1) := by
  simp only [orderedJumpSimplexVolume]
  simp_rw [div_eq_mul_inv]
  rw [intervalIntegral.integral_mul_const]
  rw [integral_pow]
  simp
  have hfac_succ :
      (((count + 1).factorial : ℕ) : ℝ) =
        ((count + 1 : ℕ) : ℝ) * ((count.factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.factorial_succ count
  rw [hfac_succ]
  have hsucc_ne : ((count + 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero count
  have hfac_ne : ((count.factorial : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero count
  field_simp [hsucc_ne, hfac_ne]
  norm_num

/--
Recursive nested integral volume of the ordered jump-time simplex.

`orderedJumpNestedVolume (n + 1) T` integrates the `n`-jump ordered volume up
to the last jump time.  The theorem below identifies this recursive analytic
object with `T^n / n!`.
-/
def orderedJumpNestedVolume : ℕ → ℝ → ℝ
  | 0, _ => 1
  | count + 1, exposure =>
      ∫ x in (0 : ℝ)..exposure, orderedJumpNestedVolume count x

/-- The recursive nested ordered-jump volume equals `exposure^count / count!`. -/
theorem orderedJumpNestedVolume_eq_orderedJumpSimplexVolume
    (count : ℕ) (exposure : ℝ) :
    orderedJumpNestedVolume count exposure =
      orderedJumpSimplexVolume exposure count := by
  induction count generalizing exposure with
  | zero =>
      simp [orderedJumpNestedVolume, orderedJumpSimplexVolume]
  | succ count ih =>
      simp [orderedJumpNestedVolume]
      have hcongr :
          (∫ x in (0 : ℝ)..exposure, orderedJumpNestedVolume count x) =
            ∫ x in (0 : ℝ)..exposure, orderedJumpSimplexVolume x count := by
        refine intervalIntegral.integral_congr ?_
        intro x _hx
        exact ih x
      rw [hcongr]
      exact integral_orderedJumpSimplexVolume_eq_succ exposure count

theorem orderedJumpNestedVolume_continuous (count : ℕ) :
    Continuous fun exposure : ℝ => orderedJumpNestedVolume count exposure := by
  have hfun :
      (fun exposure : ℝ => orderedJumpNestedVolume count exposure) =
        fun exposure : ℝ => orderedJumpSimplexVolume exposure count := by
    funext exposure
    exact orderedJumpNestedVolume_eq_orderedJumpSimplexVolume count exposure
  rw [hfun]
  unfold orderedJumpSimplexVolume
  fun_prop

/--
Recursive ordered jump-time region in shifted coordinates.

For `count + 1`, the last coordinate lies in `[0, exposure]`; the preceding
coordinates form an ordered `count`-jump region below that last coordinate.
This is the product-measure domain whose iterated volume is
`orderedJumpNestedVolume`.
-/
def orderedJumpRegion : (count : ℕ) → ℝ → Set (Fin count → ℝ)
  | 0, _ => Set.univ
  | count + 1, exposure =>
      {x | x (Fin.last count) ∈ Set.Icc (0 : ℝ) exposure ∧
        (fun i : Fin count => x i.castSucc) ∈
          orderedJumpRegion count (x (Fin.last count))}

@[simp] theorem orderedJumpRegion_zero (exposure : ℝ) :
    orderedJumpRegion 0 exposure = Set.univ := by
  rfl

theorem orderedJumpRegion_succ_mem_iff
    (count : ℕ) (exposure : ℝ) (x : Fin (count + 1) → ℝ) :
    x ∈ orderedJumpRegion (count + 1) exposure ↔
      x (Fin.last count) ∈ Set.Icc (0 : ℝ) exposure ∧
        (fun i : Fin count => x i.castSucc) ∈
          orderedJumpRegion count (x (Fin.last count)) := by
  rfl

theorem orderedJumpRegion_one_eq_Icc (exposure : ℝ) :
    orderedJumpRegion 1 exposure =
      {x : Fin 1 → ℝ | x 0 ∈ Set.Icc (0 : ℝ) exposure} := by
  ext x
  simp [orderedJumpRegion]

/--
The one-jump ordered region is the one-dimensional closed box
`[0, exposure]` in `Fin 1` coordinates.
-/
theorem orderedJumpRegion_one_eq_pi_Icc (exposure : ℝ) :
    orderedJumpRegion 1 exposure =
      Set.Icc (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => exposure) := by
  ext x
  simp [orderedJumpRegion, Set.mem_Icc, Pi.le_def, Fin.forall_fin_one]

/--
The Lebesgue volume of the one-jump ordered region is the same normalizing
factor used by the nested ordered-jump integral.
-/
theorem orderedJumpRegion_one_volume_toReal
    {exposure : ℝ} (h_exposure : 0 ≤ exposure) :
    (volume (orderedJumpRegion 1 exposure)).toReal =
      orderedJumpNestedVolume 1 exposure := by
  rw [orderedJumpRegion_one_eq_pi_Icc]
  rw [Real.volume_Icc_pi_toReal]
  · simp [orderedJumpNestedVolume]
  · intro i
    exact h_exposure

/-- The zero-jump ordered region has unit empty-dimensional volume. -/
theorem orderedJumpRegion_zero_volume_toReal (exposure : ℝ) :
    (volume (orderedJumpRegion 0 exposure)).toReal =
      orderedJumpNestedVolume 0 exposure := by
  rw [show orderedJumpRegion 0 exposure =
      Set.Icc (fun _ : Fin 0 => (0 : ℝ))
        (fun _ : Fin 0 => exposure) by
    ext x
    simp [orderedJumpRegion, Set.mem_Icc]]
  rw [Real.volume_Icc_pi_toReal]
  · simp [orderedJumpNestedVolume]
  · intro i
    exact Fin.elim0 i

/--
Closed-inequality presentation of the ordered jump-time region: every shifted
jump time lies in `[0, exposure]` and the coordinates are nondecreasing.
-/
def orderedJumpClosedRegion (count : ℕ) (exposure : ℝ) :
    Set (Fin count → ℝ) :=
  {x | (∀ i : Fin count, x i ∈ Set.Icc (0 : ℝ) exposure) ∧ Monotone x}

@[simp] theorem orderedJumpClosedRegion_zero (exposure : ℝ) :
    orderedJumpClosedRegion 0 exposure = Set.univ := by
  ext x
  simp [orderedJumpClosedRegion]
  intro i j _hij
  exact Fin.elim0 i

/--
The recursive ordered-jump region is exactly the closed ordered simplex
defined by coordinate bounds and monotonicity.
-/
theorem orderedJumpRegion_eq_closedRegion
    (count : ℕ) (exposure : ℝ) :
    orderedJumpRegion count exposure =
      orderedJumpClosedRegion count exposure := by
  induction count generalizing exposure with
  | zero =>
      ext x
      simp [orderedJumpRegion, orderedJumpClosedRegion]
      intro i j _hij
      exact Fin.elim0 i
  | succ count ih =>
      ext x
      rw [orderedJumpRegion_succ_mem_iff]
      rw [ih (x (Fin.last count))]
      constructor
      · intro h
        rcases h with ⟨hlast, hinit⟩
        rcases hinit with ⟨hinit_bounds, hinit_mono⟩
        refine ⟨?_, ?_⟩
        · intro i
          by_cases hi : i = Fin.last count
          · subst hi
            exact hlast
          · have hlelast : i ≤ Fin.last count := Fin.le_last i
            have hltlast : i < Fin.last count :=
              lt_of_le_of_ne hlelast hi
            let j : Fin count := i.castLT hltlast
            have hcast : j.castSucc = i := by
              apply Fin.ext
              simp [j]
            have hj := hinit_bounds j
            constructor
            · simpa [hcast] using hj.1
            · exact le_trans (by simpa [hcast] using hj.2) hlast.2
        · intro i j hij
          by_cases hjlast : j = Fin.last count
          · subst hjlast
            by_cases hilast : i = Fin.last count
            · subst hilast
              rfl
            · have hlelast : i ≤ Fin.last count := Fin.le_last i
              have hltlast : i < Fin.last count :=
                lt_of_le_of_ne hlelast hilast
              let ii : Fin count := i.castLT hltlast
              have hcast : ii.castSucc = i := by
                apply Fin.ext
                simp [ii]
              have hii := hinit_bounds ii
              exact by simpa [hcast] using hii.2
          · have hlelast : j ≤ Fin.last count := Fin.le_last j
            have hjltlast : j < Fin.last count :=
              lt_of_le_of_ne hlelast hjlast
            have hiltlast : i < Fin.last count :=
              lt_of_le_of_lt hij hjltlast
            let ii : Fin count := i.castLT hiltlast
            let jj : Fin count := j.castLT hjltlast
            have hcasti : ii.castSucc = i := by
              apply Fin.ext
              simp [ii]
            have hcastj : jj.castSucc = j := by
              apply Fin.ext
              simp [jj]
            have hiijj : ii ≤ jj := by
              exact Fin.le_def.mpr (by
                simpa [ii, jj] using (Fin.le_def.mp hij))
            simpa [hcasti, hcastj] using hinit_mono hiijj
      · intro h
        rcases h with ⟨hbounds, hmono⟩
        refine ⟨hbounds (Fin.last count), ?_⟩
        constructor
        · intro i
          have hlelast : i.castSucc ≤ Fin.last count :=
            Fin.le_last i.castSucc
          exact ⟨(hbounds i.castSucc).1, hmono hlelast⟩
        · intro i j hij
          exact hmono (Fin.castSucc_le_castSucc_iff.mpr hij)

theorem measurableSet_orderedJumpClosedRegion
    (count : ℕ) (exposure : ℝ) :
    MeasurableSet (orderedJumpClosedRegion count exposure) := by
  classical
  have hbounds :
      MeasurableSet
        {x : Fin count → ℝ |
          ∀ i : Fin count, x i ∈ Set.Icc (0 : ℝ) exposure} := by
    have hcoord :
        ∀ i : Fin count,
          MeasurableSet
            {x : Fin count → ℝ | x i ∈ Set.Icc (0 : ℝ) exposure} := by
      intro i
      exact
        (show Measurable (fun x : Fin count → ℝ => x i) from
          measurable_pi_apply i) measurableSet_Icc
    have hset :
        {x : Fin count → ℝ |
          ∀ i : Fin count, x i ∈ Set.Icc (0 : ℝ) exposure} =
          ⋂ i : Fin count,
            {x : Fin count → ℝ | x i ∈ Set.Icc (0 : ℝ) exposure} := by
      ext x
      simp
    rw [hset]
    exact MeasurableSet.iInter hcoord
  have hmono_eq :
      {x : Fin count → ℝ | Monotone x} =
        ⋂ i : Fin count, ⋂ j : Fin count,
          if i ≤ j then {x : Fin count → ℝ | x i ≤ x j} else Set.univ := by
    ext x
    simp [Monotone]
  have hmono :
      MeasurableSet {x : Fin count → ℝ | Monotone x} := by
    rw [hmono_eq]
    refine MeasurableSet.iInter fun i =>
      MeasurableSet.iInter fun j => ?_
    by_cases hij : i ≤ j
    · rw [if_pos hij]
      exact measurableSet_le
        (show Measurable (fun x : Fin count → ℝ => x i) from
          measurable_pi_apply i)
        (show Measurable (fun x : Fin count → ℝ => x j) from
          measurable_pi_apply j)
    · rw [if_neg hij]
      exact MeasurableSet.univ
  change MeasurableSet
    ({x : Fin count → ℝ |
        ∀ i : Fin count, x i ∈ Set.Icc (0 : ℝ) exposure} ∩
      {x : Fin count → ℝ | Monotone x})
  exact hbounds.inter hmono

/-- The recursive ordered-jump region is measurable. -/
theorem measurableSet_orderedJumpRegion (count : ℕ) (exposure : ℝ) :
    MeasurableSet (orderedJumpRegion count exposure) := by
  rw [orderedJumpRegion_eq_closedRegion]
  exact measurableSet_orderedJumpClosedRegion count exposure

/-- The ordered jump-time region is contained in the ambient closed box. -/
theorem orderedJumpRegion_subset_box
    {count : ℕ} {exposure : ℝ} :
    orderedJumpRegion count exposure ⊆
      Set.Icc (fun _ : Fin count => (0 : ℝ))
        (fun _ : Fin count => exposure) := by
  intro x hx
  rw [orderedJumpRegion_eq_closedRegion] at hx
  exact ⟨fun i => (hx.1 i).1, fun i => (hx.1 i).2⟩

/-- The ordered jump-time region has volume bounded by the ambient box. -/
theorem orderedJumpRegion_volume_le_box
    {count : ℕ} {exposure : ℝ} :
    volume (orderedJumpRegion count exposure) ≤
      volume (Set.Icc (fun _ : Fin count => (0 : ℝ))
        (fun _ : Fin count => exposure)) :=
  measure_mono orderedJumpRegion_subset_box

/-- The ordered jump-time region has finite Lebesgue volume. -/
theorem orderedJumpRegion_volume_ne_top
    {count : ℕ} {exposure : ℝ} :
    volume (orderedJumpRegion count exposure) ≠ ∞ := by
  refine ne_top_of_le_ne_top ?_ orderedJumpRegion_volume_le_box
  rw [Real.volume_Icc_pi]
  simp

theorem orderedJumpRegion_volume_toReal_nonneg
    {count : ℕ} {exposure : ℝ} :
    0 ≤ (volume (orderedJumpRegion count exposure)).toReal :=
  ENNReal.toReal_nonneg

/--
Successor ordered-region shape in product coordinates.  The first component is
the last jump time, and the second component is the ordered prefix below that
last jump time.
-/
def orderedJumpRegionSuccProduct (count : ℕ) (exposure : ℝ) :
    Set (ℝ × (Fin count → ℝ)) :=
  {p | p.1 ∈ Set.Icc (0 : ℝ) exposure ∧
    p.2 ∈ orderedJumpRegion count p.1}

theorem orderedJumpRegionSuccProduct_eq_closed
    (count : ℕ) (exposure : ℝ) :
    orderedJumpRegionSuccProduct count exposure =
      {p : ℝ × (Fin count → ℝ) |
        p.1 ∈ Set.Icc (0 : ℝ) exposure ∧
          (∀ i : Fin count, p.2 i ∈ Set.Icc (0 : ℝ) p.1) ∧
          Monotone p.2} := by
  ext p
  simp [orderedJumpRegionSuccProduct, orderedJumpRegion_eq_closedRegion,
    orderedJumpClosedRegion]

theorem measurableSet_orderedJumpRegionSuccProduct
    (count : ℕ) (exposure : ℝ) :
    MeasurableSet (orderedJumpRegionSuccProduct count exposure) := by
  classical
  rw [orderedJumpRegionSuccProduct_eq_closed]
  have hlast : MeasurableSet
      {p : ℝ × (Fin count → ℝ) | p.1 ∈ Set.Icc (0 : ℝ) exposure} :=
    measurable_fst measurableSet_Icc
  have hbounds : MeasurableSet
      {p : ℝ × (Fin count → ℝ) |
        ∀ i : Fin count, p.2 i ∈ Set.Icc (0 : ℝ) p.1} := by
    have hcoord :
        ∀ i : Fin count, MeasurableSet
          {p : ℝ × (Fin count → ℝ) |
            p.2 i ∈ Set.Icc (0 : ℝ) p.1} := by
      intro i
      exact
        (measurableSet_le measurable_const
          ((show Measurable (fun p : ℝ × (Fin count → ℝ) => p.2 i) from
            (measurable_pi_apply i).comp measurable_snd))).inter
        (measurableSet_le
          (show Measurable (fun p : ℝ × (Fin count → ℝ) => p.2 i) from
            (measurable_pi_apply i).comp measurable_snd)
          measurable_fst)
    have hset :
        {p : ℝ × (Fin count → ℝ) |
          ∀ i : Fin count, p.2 i ∈ Set.Icc (0 : ℝ) p.1} =
          ⋂ i : Fin count,
            {p : ℝ × (Fin count → ℝ) |
              p.2 i ∈ Set.Icc (0 : ℝ) p.1} := by
      ext p
      simp
    rw [hset]
    exact MeasurableSet.iInter hcoord
  have hmono : MeasurableSet
      {p : ℝ × (Fin count → ℝ) | Monotone p.2} := by
    have hmono_eq :
        {p : ℝ × (Fin count → ℝ) | Monotone p.2} =
          ⋂ i : Fin count, ⋂ j : Fin count,
            if i ≤ j then
              {p : ℝ × (Fin count → ℝ) | p.2 i ≤ p.2 j}
            else Set.univ := by
      ext p
      simp [Monotone]
    rw [hmono_eq]
    refine MeasurableSet.iInter fun i =>
      MeasurableSet.iInter fun j => ?_
    by_cases hij : i ≤ j
    · rw [if_pos hij]
      exact measurableSet_le
        (show Measurable (fun p : ℝ × (Fin count → ℝ) => p.2 i) from
          (measurable_pi_apply i).comp measurable_snd)
        (show Measurable (fun p : ℝ × (Fin count → ℝ) => p.2 j) from
          (measurable_pi_apply j).comp measurable_snd)
    · rw [if_neg hij]
      exact MeasurableSet.univ
  exact hlast.inter (hbounds.inter hmono)

theorem piFinSuccAbove_preimage_orderedJumpRegionSuccProduct
    (count : ℕ) (exposure : ℝ) :
    (MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (count + 1) => ℝ) (Fin.last count)) ⁻¹'
        orderedJumpRegionSuccProduct count exposure =
      orderedJumpRegion (count + 1) exposure := by
  ext x
  simp [orderedJumpRegionSuccProduct, orderedJumpRegion,
    MeasurableEquiv.piFinSuccAbove, Fin.init_def]

/--
The recursive successor ordered region has the same volume as its standard
product-coordinate representation.
-/
theorem orderedJumpRegion_succ_measure_eq_product
    (count : ℕ) (exposure : ℝ) :
    volume (orderedJumpRegion (count + 1) exposure) =
      volume (orderedJumpRegionSuccProduct count exposure) := by
  have h :=
    (MeasureTheory.volume_preserving_piFinSuccAbove
      (fun _ : Fin (count + 1) => ℝ) (Fin.last count)).measure_preimage
      (measurableSet_orderedJumpRegionSuccProduct
        count exposure).nullMeasurableSet
  rw [piFinSuccAbove_preimage_orderedJumpRegionSuccProduct] at h
  exact h

/--
The successor product-coordinate ordered region has volume equal to the
last-jump integral of the prefix ordered-region volume.
-/
theorem orderedJumpRegionSuccProduct_volume_eq_lintegral
    (count : ℕ) (exposure : ℝ) :
    volume (orderedJumpRegionSuccProduct count exposure) =
      ∫⁻ y in Set.Icc (0 : ℝ) exposure,
        volume (orderedJumpRegion count y) := by
  rw [MeasureTheory.Measure.volume_eq_prod ℝ (Fin count → ℝ)]
  rw [MeasureTheory.Measure.prod_apply
    (measurableSet_orderedJumpRegionSuccProduct count exposure)]
  rw [← lintegral_indicator measurableSet_Icc
    (fun y : ℝ => volume (orderedJumpRegion count y))]
  apply lintegral_congr_ae
  filter_upwards with y
  by_cases hy : y ∈ Set.Icc (0 : ℝ) exposure
  · rw [show ((fun x : Fin count → ℝ => (y, x)) ⁻¹'
        orderedJumpRegionSuccProduct count exposure) =
          orderedJumpRegion count y by
      ext x
      constructor
      · intro hx
        exact hx.2
      · intro hx
        exact ⟨hy, hx⟩]
    simp [hy, Set.indicator_of_mem]
  · rw [show ((fun x : Fin count → ℝ => (y, x)) ⁻¹'
        orderedJumpRegionSuccProduct count exposure) = ∅ by
      ext x
      constructor
      · intro hx
        exact False.elim (hy hx.1)
      · intro hx
        exact False.elim hx]
    simp [hy, Set.indicator_of_notMem]

/--
Two-jump ordered region in product coordinates `(firstJump, secondJump)`.
-/
def orderedJumpRegionTwoProduct (exposure : ℝ) : Set (ℝ × ℝ) :=
  {p | p.2 ∈ Set.Icc (0 : ℝ) exposure ∧
    p.1 ∈ Set.Icc (0 : ℝ) p.2}

theorem measurableSet_orderedJumpRegionTwoProduct (exposure : ℝ) :
    MeasurableSet (orderedJumpRegionTwoProduct exposure) := by
  unfold orderedJumpRegionTwoProduct
  measurability

theorem finTwoArrow_preimage_orderedJumpRegionTwoProduct (exposure : ℝ) :
    MeasurableEquiv.finTwoArrow ⁻¹'
        orderedJumpRegionTwoProduct exposure =
      orderedJumpRegion 2 exposure := by
  ext x
  simp [orderedJumpRegionTwoProduct, orderedJumpRegion]

/--
The recursive two-jump ordered region has the same Lebesgue measure as its
standard product-coordinate representation.
-/
theorem orderedJumpRegion_two_measure_eq_product (exposure : ℝ) :
    volume (orderedJumpRegion 2 exposure) =
      volume (orderedJumpRegionTwoProduct exposure) := by
  have h :=
    (MeasureTheory.volume_preserving_finTwoArrow ℝ).measure_preimage
      (measurableSet_orderedJumpRegionTwoProduct exposure).nullMeasurableSet
  change volume ((fun f : Fin 2 → ℝ => (f 0, f 1)) ⁻¹'
      orderedJumpRegionTwoProduct exposure) =
    volume (orderedJumpRegionTwoProduct exposure) at h
  rw [show ((fun f : Fin 2 → ℝ => (f 0, f 1)) ⁻¹'
      orderedJumpRegionTwoProduct exposure) =
        orderedJumpRegion 2 exposure by
    ext x
    simp [orderedJumpRegionTwoProduct, orderedJumpRegion]] at h
  exact h

/--
The two-jump product-coordinate ordered region has volume represented by the
one-dimensional integral of the lower-coordinate interval length.
-/
theorem orderedJumpRegionTwoProduct_volume_eq_lintegral (exposure : ℝ) :
    volume (orderedJumpRegionTwoProduct exposure) =
      ∫⁻ y in Set.Icc (0 : ℝ) exposure, ENNReal.ofReal y := by
  rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
  rw [MeasureTheory.Measure.prod_apply_symm
    (measurableSet_orderedJumpRegionTwoProduct exposure)]
  rw [← lintegral_indicator measurableSet_Icc
    (fun y : ℝ => ENNReal.ofReal y)]
  apply lintegral_congr_ae
  filter_upwards with y
  by_cases hy : y ∈ Set.Icc (0 : ℝ) exposure
  · have hy0 : 0 ≤ y := hy.1
    have hyT : y ≤ exposure := hy.2
    rw [show ((fun x : ℝ => (x, y)) ⁻¹'
        orderedJumpRegionTwoProduct exposure) = Set.Icc (0 : ℝ) y by
      ext x
      simp [orderedJumpRegionTwoProduct, hy0, hyT]]
    simp [hy, Set.indicator_of_mem, Real.volume_Icc]
  · have hnot : ¬ (0 ≤ y ∧ y ≤ exposure) := by
      simpa [Set.mem_Icc] using hy
    rw [show ((fun x : ℝ => (x, y)) ⁻¹'
        orderedJumpRegionTwoProduct exposure) = ∅ by
      ext x
      simp [orderedJumpRegionTwoProduct, hnot]]
    simp [hy, Set.indicator_of_notMem]

/--
The Lebesgue volume of the two-jump product-coordinate ordered region is the
same normalizing factor used by the nested ordered-jump integral.
-/
theorem orderedJumpRegionTwoProduct_volume_toReal
    {exposure : ℝ} (h_exposure : 0 ≤ exposure) :
    (volume (orderedJumpRegionTwoProduct exposure)).toReal =
      orderedJumpNestedVolume 2 exposure := by
  rw [orderedJumpRegionTwoProduct_volume_eq_lintegral]
  have h_int :
      Integrable (fun y : ℝ => y)
        (volume.restrict (Set.Icc (0 : ℝ) exposure)) := by
    simpa [IntegrableOn] using
      (continuous_id.integrableOn_Icc (a := (0 : ℝ)) (b := exposure)
        (μ := volume))
  have h_nonneg :
      0 ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) exposure)]
        fun y : ℝ => y := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact hy.1
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int h_nonneg]
  change (ENNReal.ofReal (∫ y in Set.Icc (0 : ℝ) exposure, y)).toReal =
    orderedJumpNestedVolume 2 exposure
  have h_set_integral :
      (∫ y in Set.Icc (0 : ℝ) exposure, y) =
        ∫ y in (0 : ℝ)..exposure, y := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le h_exposure]
  rw [ENNReal.toReal_ofReal]
  · rw [h_set_integral]
    rw [orderedJumpNestedVolume_eq_orderedJumpSimplexVolume]
    have hpow :
        (∫ y in (0 : ℝ)..exposure, y) = exposure ^ 2 / 2 := by
      simpa using (integral_pow (a := (0 : ℝ)) (b := exposure) 1)
    rw [hpow]
    norm_num [orderedJumpSimplexVolume]
  · rw [h_set_integral]
    have hpow :
        (∫ y in (0 : ℝ)..exposure, y) = exposure ^ 2 / 2 := by
      simpa using (integral_pow (a := (0 : ℝ)) (b := exposure) 1)
    rw [hpow]
    positivity

/--
The Lebesgue volume of the recursive two-jump ordered region is the same
normalizing factor used by the nested ordered-jump integral.
-/
theorem orderedJumpRegion_two_volume_toReal
    {exposure : ℝ} (h_exposure : 0 ≤ exposure) :
    (volume (orderedJumpRegion 2 exposure)).toReal =
      orderedJumpNestedVolume 2 exposure := by
  rw [orderedJumpRegion_two_measure_eq_product]
  exact orderedJumpRegionTwoProduct_volume_toReal h_exposure

/-- Ordered-jump simplex volume is nonnegative for nonnegative exposure. -/
theorem orderedJumpSimplexVolume_nonneg
    {exposure : ℝ} (h_exposure : 0 ≤ exposure) (count : ℕ) :
    0 ≤ orderedJumpSimplexVolume exposure count := by
  unfold orderedJumpSimplexVolume
  positivity

/-- Recursive ordered-jump nested volume is nonnegative for nonnegative exposure. -/
theorem orderedJumpNestedVolume_nonneg
    {exposure : ℝ} (h_exposure : 0 ≤ exposure) (count : ℕ) :
    0 ≤ orderedJumpNestedVolume count exposure := by
  rw [orderedJumpNestedVolume_eq_orderedJumpSimplexVolume]
  exact orderedJumpSimplexVolume_nonneg h_exposure count

/--
The Lebesgue volume of the recursive ordered jump-time region is the nested
ordered-simplex volume for every finite count.
-/
theorem orderedJumpRegion_volume_eq_ofReal_nested
    {count : ℕ} {exposure : ℝ} (h_exposure : 0 ≤ exposure) :
    volume (orderedJumpRegion count exposure) =
      ENNReal.ofReal (orderedJumpNestedVolume count exposure) := by
  induction count generalizing exposure with
  | zero =>
      rw [show orderedJumpRegion 0 exposure =
          Set.Icc (fun _ : Fin 0 => (0 : ℝ))
            (fun _ : Fin 0 => exposure) by
        ext x
        simp [orderedJumpRegion, Set.mem_Icc]]
      rw [Real.volume_Icc_pi]
      simp [orderedJumpNestedVolume]
  | succ count ih =>
      rw [orderedJumpRegion_succ_measure_eq_product]
      rw [orderedJumpRegionSuccProduct_volume_eq_lintegral]
      have h_lintegral_congr :
          (∫⁻ y in Set.Icc (0 : ℝ) exposure,
              volume (orderedJumpRegion count y)) =
            ∫⁻ y in Set.Icc (0 : ℝ) exposure,
              ENNReal.ofReal (orderedJumpNestedVolume count y) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
        exact ih hy.1
      rw [h_lintegral_congr]
      have h_int :
          Integrable (fun y : ℝ => orderedJumpNestedVolume count y)
            (volume.restrict (Set.Icc (0 : ℝ) exposure)) := by
        simpa [IntegrableOn] using
          (orderedJumpNestedVolume_continuous count).integrableOn_Icc
            (a := (0 : ℝ)) (b := exposure) (μ := volume)
      have h_nonneg :
          0 ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) exposure)]
            fun y : ℝ => orderedJumpNestedVolume count y := by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
        exact orderedJumpNestedVolume_nonneg hy.1 count
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int h_nonneg]
      congr 1
      have h_set_integral :
          (∫ y in Set.Icc (0 : ℝ) exposure,
              orderedJumpNestedVolume count y) =
            ∫ y in (0 : ℝ)..exposure,
              orderedJumpNestedVolume count y := by
        rw [integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le h_exposure]
      rw [h_set_integral]
      simp [orderedJumpNestedVolume]

/--
`toReal` form of the finite-count ordered-region volume normalization.
-/
theorem orderedJumpRegion_volume_toReal
    {count : ℕ} {exposure : ℝ} (h_exposure : 0 ≤ exposure) :
    (volume (orderedJumpRegion count exposure)).toReal =
      orderedJumpNestedVolume count exposure := by
  rw [orderedJumpRegion_volume_eq_ofReal_nested h_exposure]
  rw [ENNReal.toReal_ofReal (orderedJumpNestedVolume_nonneg h_exposure count)]

/-- Ordered-jump simplex volume is positive for positive exposure. -/
theorem orderedJumpSimplexVolume_pos
    {exposure : ℝ} (h_exposure : 0 < exposure) (count : ℕ) :
    0 < orderedJumpSimplexVolume exposure count := by
  unfold orderedJumpSimplexVolume
  positivity

/-- Recursive ordered-jump nested volume is positive for positive exposure. -/
theorem orderedJumpNestedVolume_pos
    {exposure : ℝ} (h_exposure : 0 < exposure) (count : ℕ) :
    0 < orderedJumpNestedVolume count exposure := by
  rw [orderedJumpNestedVolume_eq_orderedJumpSimplexVolume]
  exact orderedJumpSimplexVolume_pos h_exposure count

/-- The ordered jump-time region has positive volume for positive exposure. -/
theorem orderedJumpRegion_volume_toReal_pos
    {count : ℕ} {exposure : ℝ} (h_exposure : 0 < exposure) :
    0 < (volume (orderedJumpRegion count exposure)).toReal := by
  rw [orderedJumpRegion_volume_toReal (le_of_lt h_exposure)]
  exact orderedJumpNestedVolume_pos h_exposure count

/-! ## Finite Product Likelihood Algebra -/

/-- Total exposure across a finite family of observation rows. -/
def totalExposure {ι : Type*} (s : Finset ι) (exposure : ι → ℝ) : ℝ :=
  ∑ i ∈ s, exposure i

/-- Total exposure is nonnegative when each row exposure is nonnegative. -/
theorem totalExposure_nonneg {ι : Type*} (s : Finset ι)
    (exposure : ι → ℝ)
    (h_nonneg : ∀ i ∈ s, 0 ≤ exposure i) :
    0 ≤ totalExposure s exposure := by
  exact Finset.sum_nonneg h_nonneg

/--
Total exposure is positive when every row exposure is nonnegative and at least
one included row has positive exposure.
-/
theorem totalExposure_pos_of_exists_pos {ι : Type*} (s : Finset ι)
    (exposure : ι → ℝ)
    (h_nonneg : ∀ i ∈ s, 0 ≤ exposure i)
    (h_exists : ∃ i ∈ s, 0 < exposure i) :
    0 < totalExposure s exposure := by
  exact Finset.sum_pos' h_nonneg h_exists

/--
Adjacent increments of a finite endpoint timeline telescope to final minus
initial time.
-/
theorem sum_fin_adjacent_timeline_diffs
    {n : ℕ} (t : Fin (n + 1) → ℝ) :
    (∑ i : Fin n, (t i.succ - t i.castSucc)) =
      t (Fin.last n) - t 0 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      simp_rw [Fin.succ_castSucc]
      have hsub := ih (fun j : Fin (n + 1) => t j.castSucc)
      rw [hsub]
      simp

/--
Total exposure over adjacent increments of a finite endpoint timeline.
-/
theorem totalExposure_fin_adjacent_timeline_diffs
    {n : ℕ} (t : Fin (n + 1) → ℝ) :
    totalExposure (Finset.univ : Finset (Fin n))
        (fun i => t i.succ - t i.castSucc) =
      t (Fin.last n) - t 0 := by
  simpa [totalExposure] using sum_fin_adjacent_timeline_diffs t

/-- Adjacent increments of a monotone finite endpoint timeline are nonnegative. -/
theorem adjacent_timeline_diff_nonneg
    {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : Monotone t)
    (i : Fin n) :
    0 ≤ t i.succ - t i.castSucc :=
  sub_nonneg.mpr (ht (Fin.castSucc_le_succ i))

/--
Total exposure over adjacent increments of a monotone finite endpoint timeline
is nonnegative.
-/
theorem totalExposure_fin_adjacent_timeline_nonneg
    {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : Monotone t) :
    0 ≤ totalExposure (Finset.univ : Finset (Fin n))
        (fun i => t i.succ - t i.castSucc) := by
  rw [totalExposure_fin_adjacent_timeline_diffs]
  exact sub_nonneg.mpr (ht (by simp))

/--
Total exposure over adjacent finite-timeline increments is positive when the
last endpoint is strictly after the first endpoint.
-/
theorem totalExposure_fin_adjacent_timeline_pos
    {n : ℕ} {t : Fin (n + 1) → ℝ}
    (h : t 0 < t (Fin.last n)) :
    0 < totalExposure (Finset.univ : Finset (Fin n))
        (fun i => t i.succ - t i.castSucc) := by
  rw [totalExposure_fin_adjacent_timeline_diffs]
  exact sub_pos.mpr h

/-- Total count across a finite family of observation rows. -/
def totalCount {ι : Type*} (s : Finset ι) (count : ι → ℕ) : ℕ :=
  ∑ i ∈ s, count i

/-- Product of Poisson count likelihoods over a finite family of observation rows. -/
def countLikelihoodProduct {ι : Type*} (s : Finset ι)
    (rate : ℝ) (exposure : ι → ℝ) (count : ι → ℕ) : ℝ :=
  ∏ i ∈ s, countLikelihood rate (exposure i) (count i)

theorem countLikelihoodProduct_nonneg
    {ι : Type*} (s : Finset ι)
    {rate : ℝ} {exposure : ι → ℝ} (count : ι → ℕ)
    (h_mean : ∀ i ∈ s, 0 ≤ rate * exposure i) :
    0 ≤ countLikelihoodProduct s rate exposure count := by
  exact Finset.prod_nonneg fun i hi =>
    countLikelihood_nonneg (h_mean i hi) (count i)

/--
Existence of an independent Poisson count family whose finite subfamily event
likelihoods factor into the product of the corresponding Poisson PMFs.

This is the reusable product-space construction for finite incident families:
the index type may be infinite, but the likelihood statement is for an
arbitrary finite subset `s`.
-/
theorem exists_iIndepFun_poisson_count_joint_real
    {ι : Type u} (rate : ℝ) (h_rate : 0 ≤ rate)
    (exposure : ι → ℝ) (h_exposure : ∀ i, 0 ≤ exposure i)
    (s : Finset ι) :
    ∃ Ω : Type u, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ X : ι → Ω → ℕ,
        (∀ i, Measurable (X i)) ∧
        (∀ i,
          ProbabilityTheory.HasLaw
            (X i)
            (ProbabilityTheory.poissonMeasure
              (rateExposureParam rate (exposure i)
                (mul_nonneg h_rate (h_exposure i)))) P) ∧
        ProbabilityTheory.iIndepFun X P ∧ IsProbabilityMeasure P ∧
        ∀ k : ι → ℕ,
          P.real (⋂ i ∈ s, {ω : Ω | X i ω = k i}) =
            countLikelihoodProduct s rate exposure k := by
  classical
  rcases exists_iIndepFun_poisson_increments
      rate h_rate exposure h_exposure with
    ⟨Ω, mΩ, P, X, hmeas, hLaw, hind, hprob⟩
  refine ⟨Ω, mΩ, P, X, hmeas, hLaw, hind, hprob, ?_⟩
  intro k
  have hmeasure :
      P (⋂ i ∈ s, {ω : Ω | X i ω = k i}) =
        ∏ i ∈ s, P {ω : Ω | X i ω = k i} := by
    have h :=
      hind.measure_inter_preimage_eq_mul
        (S := s)
        (sets := fun i : ι => ({k i} : Set ℕ))
        (by
          intro i _hi
          exact measurableSet_singleton (k i))
    simpa using h
  rw [Measure.real_def, hmeasure]
  simp only [ENNReal.toReal_prod, countLikelihoodProduct]
  refine Finset.prod_congr rfl ?_
  intro i hi
  exact
    hasLaw_poissonMeasure_real_singleton_eq_countLikelihood
      (mul_nonneg h_rate (h_exposure i)) (hLaw i) (k i)

/--
Existence of a finite adjacent-increment Poisson schedule together with its
finite-dimensional joint likelihood formula.

This packages the product-space construction, the independent Poisson
increment laws, and the product-PMF joint event probability for one finite
monotone observation schedule.
-/
theorem exists_iIndepFun_poisson_adjacent_interval_count_joint_real_fin
    (rate : ℝ) (h_rate : 0 ≤ rate)
    {n : ℕ} (t : Fin (n + 1) → ℝ) (ht : Monotone t) :
    ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ X : Fin n → Ω → ℕ,
        (∀ i, Measurable (X i)) ∧
        (∀ i,
          ProbabilityTheory.HasLaw
            (X i)
            (ProbabilityTheory.poissonMeasure
              (rateExposureParam rate (t i.succ - t i.castSucc)
                (mul_nonneg h_rate
                  (sub_nonneg.mpr (ht (Fin.castSucc_le_succ i)))))) P) ∧
        ProbabilityTheory.iIndepFun X P ∧ IsProbabilityMeasure P ∧
        ∀ k : Fin n → ℕ,
          P.real (⋂ i ∈ (Finset.univ : Finset (Fin n)),
              {ω : Ω | X i ω = k i}) =
            countLikelihoodProduct (Finset.univ : Finset (Fin n)) rate
              (fun i => t i.succ - t i.castSucc) k := by
  classical
  rcases exists_iIndepFun_poisson_adjacent_interval_counts_fin
      rate h_rate t ht with
    ⟨Ω, mΩ, P, X, hmeas, hLaw, hind, hprob⟩
  refine ⟨Ω, mΩ, P, X, hmeas, hLaw, hind, hprob, ?_⟩
  intro k
  have hmeasure :
      P (⋂ i ∈ (Finset.univ : Finset (Fin n)),
          {ω : Ω | X i ω = k i}) =
        ∏ i : Fin n, P {ω : Ω | X i ω = k i} := by
    have h :=
      hind.measure_inter_preimage_eq_mul
        (S := (Finset.univ : Finset (Fin n)))
        (sets := fun i : Fin n => ({k i} : Set ℕ))
        (by
          intro i _hi
          exact measurableSet_singleton (k i))
    simpa using h
  rw [Measure.real_def, hmeasure]
  simp only [ENNReal.toReal_prod, countLikelihoodProduct]
  refine Finset.prod_congr rfl ?_
  intro i _hi
  exact
    hasLaw_poissonMeasure_real_singleton_eq_countLikelihood
      (mul_nonneg h_rate
        (sub_nonneg.mpr (ht (Fin.castSucc_le_succ i))))
      (hLaw i) (k i)

/--
Finite-schedule count path generated by adjacent increment counts.

At endpoint `j`, the count is the prefix sum of all increments with index
strictly before `j`.
-/
def finiteScheduleCountFromIncrements
    {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℕ)
    (j : Fin (n + 1)) (ω : Ω) : ℕ :=
  ∑ i ∈ (Finset.univ.filter fun i : Fin n => (i : ℕ) < (j : ℕ)),
    X i ω

@[simp] theorem finiteScheduleCountFromIncrements_zero
    {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℕ) (ω : Ω) :
    finiteScheduleCountFromIncrements X 0 ω = 0 := by
  simp [finiteScheduleCountFromIncrements]

/--
The cumulative finite-schedule count at the next endpoint is the current count
plus the adjacent increment.
-/
theorem finiteScheduleCountFromIncrements_castSucc_add
    {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℕ)
    (i : Fin n) (ω : Ω) :
    finiteScheduleCountFromIncrements X i.castSucc ω + X i ω =
      finiteScheduleCountFromIncrements X i.succ ω := by
  classical
  let s : Finset (Fin n) :=
    Finset.univ.filter fun j : Fin n => (j : ℕ) < (i : ℕ)
  have hnot : i ∉ s := by
    simp [s]
  have hset :
      (Finset.univ.filter fun j : Fin n =>
          (j : ℕ) < ((i.succ : Fin (n + 1)) : ℕ)) =
        insert i s := by
    ext j
    have hsucc : ((i.succ : Fin (n + 1)) : ℕ) = (i : ℕ) + 1 := rfl
    constructor
    · intro hj
      simp at hj
      by_cases hji : j = i
      · subst j
        exact Finset.mem_insert_self i s
      · rw [Finset.mem_insert]
        right
        simp [s]
        exact Fin.lt_def.mp (lt_of_le_of_ne hj hji)
    · intro hj
      rw [Finset.mem_insert] at hj
      rcases hj with rfl | hj
      · simp
      · simp [s] at hj
        rw [hsucc]
        simpa using Nat.lt_trans hj (Nat.lt_succ_self (i : ℕ))
  change (∑ x ∈ s, X x ω) + X i ω =
    ∑ x ∈ (Finset.univ.filter fun j : Fin n =>
      (j : ℕ) < ((i.succ : Fin (n + 1)) : ℕ)), X x ω
  rw [hset]
  rw [Finset.sum_insert hnot]
  exact Nat.add_comm _ _

/-- The adjacent difference of the cumulative finite-schedule count is the increment. -/
theorem finiteScheduleCountFromIncrements_adjacent_sub_eq
    {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℕ)
    (i : Fin n) (ω : Ω) :
    finiteScheduleCountFromIncrements X i.succ ω -
        finiteScheduleCountFromIncrements X i.castSucc ω =
      X i ω := by
  have h := finiteScheduleCountFromIncrements_castSucc_add X i ω
  omega

/-- Finite-schedule counts generated from nonnegative increments are monotone. -/
theorem finiteScheduleCountFromIncrements_mono
    {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℕ) (ω : Ω) :
    Monotone fun j : Fin (n + 1) =>
      finiteScheduleCountFromIncrements X j ω := by
  intro j k hjk
  let s : Finset (Fin n) :=
    Finset.univ.filter fun i : Fin n => (i : ℕ) < (j : ℕ)
  let t : Finset (Fin n) :=
    Finset.univ.filter fun i : Fin n => (i : ℕ) < (k : ℕ)
  change (∑ i ∈ s, X i ω) ≤ ∑ i ∈ t, X i ω
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (s := s) (t := t) (f := fun i : Fin n => X i ω) ?subset ?nonneg
  · intro i hi
    simp [s, t] at hi ⊢
    exact lt_of_lt_of_le hi hjk
  · intro i _hi _hnot
    exact Nat.zero_le _

/--
A monotone finite endpoint count path telescopes into the sum of its adjacent
differences.
-/
theorem endpoint_count_eq_sum_adjacent_diffs
    {n : ℕ} (N : Fin (n + 1) → ℕ)
    (hzero : N 0 = 0) (hmono : Monotone N) :
    N (Fin.last n) =
      ∑ i : Fin n, (N i.succ - N i.castSucc) := by
  induction n with
  | zero =>
      simp [hzero]
  | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      simp_rw [Fin.succ_castSucc]
      have hprefix :
          N (Fin.last n).castSucc =
            ∑ i : Fin n,
              (N i.succ.castSucc - N i.castSucc.castSucc) := by
        have hzero' : (fun j : Fin (n + 1) => N j.castSucc) 0 = 0 := by
          simpa using hzero
        have hmono' : Monotone (fun j : Fin (n + 1) => N j.castSucc) := by
          intro a b hab
          exact hmono (Fin.le_def.mpr (Fin.le_def.mp hab))
        simpa using ih (fun j : Fin (n + 1) => N j.castSucc) hzero' hmono'
      rw [← hprefix]
      have hle : N (Fin.last n).castSucc ≤ N (Fin.last n).succ :=
        hmono (Fin.castSucc_le_succ (Fin.last n))
      change N (Fin.last n).succ =
        N (Fin.last n).castSucc +
          (N (Fin.last n).succ - N (Fin.last n).castSucc)
      exact (Nat.add_sub_of_le hle).symm

/--
Existence of a finite-schedule cumulative Poisson counting process.

The constructed process is indexed by the finite endpoint timeline, starts at
zero, has monotone sample paths, has independent Poisson adjacent increments,
and satisfies the finite-dimensional product likelihood formula for adjacent
increment events.
-/
theorem exists_finiteSchedulePoissonCountingProcess_fin
    (rate : ℝ) (h_rate : 0 ≤ rate)
    {n : ℕ} (t : Fin (n + 1) → ℝ) (ht : Monotone t) :
    ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ N : Fin (n + 1) → Ω → ℕ,
        (∀ ω, N 0 ω = 0) ∧
        (∀ ω, Monotone fun j : Fin (n + 1) => N j ω) ∧
        (∀ i,
          ProbabilityTheory.HasLaw
            (fun ω => N i.succ ω - N i.castSucc ω)
            (ProbabilityTheory.poissonMeasure
              (rateExposureParam rate (t i.succ - t i.castSucc)
                (mul_nonneg h_rate
                  (sub_nonneg.mpr (ht (Fin.castSucc_le_succ i)))))) P) ∧
        ProbabilityTheory.iIndepFun
          (fun i : Fin n => fun ω => N i.succ ω - N i.castSucc ω) P ∧
        IsProbabilityMeasure P ∧
        ∀ k : Fin n → ℕ,
          P.real (⋂ i ∈ (Finset.univ : Finset (Fin n)),
              {ω : Ω | N i.succ ω - N i.castSucc ω = k i}) =
            countLikelihoodProduct (Finset.univ : Finset (Fin n)) rate
              (fun i => t i.succ - t i.castSucc) k := by
  classical
  rcases exists_iIndepFun_poisson_adjacent_interval_count_joint_real_fin
      rate h_rate t ht with
    ⟨Ω, mΩ, P, X, hmeas, hLaw, hind, hprob, hJoint⟩
  let N : Fin (n + 1) → Ω → ℕ := finiteScheduleCountFromIncrements X
  refine ⟨Ω, mΩ, P, N, ?_, ?_, ?_, ?_, hprob, ?_⟩
  · intro ω
    simp [N]
  · intro ω
    exact finiteScheduleCountFromIncrements_mono X ω
  · intro i
    exact (hLaw i).congr
      (Filter.Eventually.of_forall fun ω =>
        finiteScheduleCountFromIncrements_adjacent_sub_eq X i ω)
  · exact hind.congr fun i =>
      Filter.Eventually.of_forall fun ω =>
        (finiteScheduleCountFromIncrements_adjacent_sub_eq X i ω).symm
  · intro k
    simpa [N, finiteScheduleCountFromIncrements_adjacent_sub_eq] using
      hJoint k

/--
Reusable finite-dimensional Poisson counting-process certificate on a monotone
endpoint schedule.

This is intentionally finite-dimensional: it records exactly the data needed
for finite adjacent-increment likelihood arguments without assuming a full
continuous-time path-space construction.
-/
structure FiniteSchedulePoissonCountingProcess
    (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω)
    (n : ℕ) (rate : ℝ) (t : Fin (n + 1) → ℝ) where
  rate_nonneg : 0 ≤ rate
  timeline_mono : Monotone t
  count : Fin (n + 1) → Ω → ℕ
  count_zero : ∀ ω, count 0 ω = 0
  count_mono : ∀ ω, Monotone fun j : Fin (n + 1) => count j ω
  increment_hasLaw :
    ∀ i : Fin n,
      ProbabilityTheory.HasLaw
        (fun ω => count i.succ ω - count i.castSucc ω)
        (ProbabilityTheory.poissonMeasure
          (rateExposureParam rate (t i.succ - t i.castSucc)
            (mul_nonneg rate_nonneg
              (sub_nonneg.mpr (timeline_mono (Fin.castSucc_le_succ i)))))) P
  iIndep_increment :
    ProbabilityTheory.iIndepFun
      (fun i : Fin n => fun ω => count i.succ ω - count i.castSucc ω) P
  isProbabilityMeasure : IsProbabilityMeasure P

namespace FiniteSchedulePoissonCountingProcess

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {n : ℕ} {rate : ℝ} {t : Fin (n + 1) → ℝ}

/-- Adjacent increment of a finite-schedule counting process. -/
def adjacentIncrement
    (H : FiniteSchedulePoissonCountingProcess Ω P n rate t)
    (i : Fin n) (ω : Ω) : ℕ :=
  H.count i.succ ω - H.count i.castSucc ω

theorem adjacentIncrement_hasLaw
    (H : FiniteSchedulePoissonCountingProcess Ω P n rate t)
    (i : Fin n) :
    ProbabilityTheory.HasLaw
      (H.adjacentIncrement i)
      (ProbabilityTheory.poissonMeasure
        (rateExposureParam rate (t i.succ - t i.castSucc)
          (mul_nonneg H.rate_nonneg
            (sub_nonneg.mpr (H.timeline_mono (Fin.castSucc_le_succ i)))))) P := by
  simpa [adjacentIncrement] using H.increment_hasLaw i

theorem iIndepFun_adjacentIncrement
    (H : FiniteSchedulePoissonCountingProcess Ω P n rate t) :
    ProbabilityTheory.iIndepFun H.adjacentIncrement P := by
  simpa [adjacentIncrement] using H.iIndep_increment

/--
Endpoint count plus adjacent increment gives the next endpoint count.

This is the pathwise bridge from the finite-schedule certificate's adjacent
increment variables back to its cumulative count path.
-/
theorem count_castSucc_add_adjacentIncrement
    (H : FiniteSchedulePoissonCountingProcess Ω P n rate t)
    (i : Fin n) (ω : Ω) :
    H.count i.castSucc ω + H.adjacentIncrement i ω =
      H.count i.succ ω := by
  have hle : H.count i.castSucc ω ≤ H.count i.succ ω :=
    H.count_mono ω (Fin.castSucc_le_succ i)
  simp [adjacentIncrement, Nat.add_sub_of_le hle]

/--
The final endpoint count of a finite-schedule process is the sum of all
adjacent increments.
-/
theorem count_last_eq_sum_adjacentIncrement
    (H : FiniteSchedulePoissonCountingProcess Ω P n rate t)
    (ω : Ω) :
    H.count (Fin.last n) ω =
      ∑ i : Fin n, H.adjacentIncrement i ω := by
  simpa [adjacentIncrement] using
    endpoint_count_eq_sum_adjacent_diffs
      (fun j : Fin (n + 1) => H.count j ω)
      (H.count_zero ω) (H.count_mono ω)

/--
For a one-window schedule, the final endpoint count is exactly the sole
adjacent increment.
-/
theorem count_last_eq_adjacentIncrement_one
    {t : Fin 2 → ℝ}
    (H : FiniteSchedulePoissonCountingProcess Ω P 1 rate t)
    (ω : Ω) :
    H.count (Fin.last 1) ω = H.adjacentIncrement (0 : Fin 1) ω := by
  have h :=
    (H.count_castSucc_add_adjacentIncrement (0 : Fin 1) ω).symm
  have hzero : H.count (0 : Fin 2) ω = 0 := H.count_zero ω
  simpa [hzero] using h

/--
For a one-window schedule, the final endpoint count has the same Poisson law
as the sole adjacent increment.
-/
theorem count_last_hasLaw_one
    {t : Fin 2 → ℝ}
    (H : FiniteSchedulePoissonCountingProcess Ω P 1 rate t) :
    ProbabilityTheory.HasLaw
      (fun ω : Ω => H.count (Fin.last 1) ω)
      (ProbabilityTheory.poissonMeasure
        (rateExposureParam rate (t (Fin.last 1) - t 0)
          (mul_nonneg H.rate_nonneg
            (sub_nonneg.mpr
              (H.timeline_mono
                (show (0 : Fin 2) ≤ Fin.last 1 by decide)))))) P := by
  simpa using
    (H.adjacentIncrement_hasLaw (0 : Fin 1)).congr
      (Filter.Eventually.of_forall fun ω =>
        H.count_last_eq_adjacentIncrement_one ω)

/--
For a one-window schedule, the final endpoint-count event probability is the
ordinary Poisson count likelihood for the endpoint exposure.
-/
theorem count_last_prob_one
    {t : Fin 2 → ℝ}
    (H : FiniteSchedulePoissonCountingProcess Ω P 1 rate t)
    (k : ℕ) :
    P.real {ω : Ω | H.count (Fin.last 1) ω = k} =
      countLikelihood rate (t (Fin.last 1) - t 0) k := by
  exact
    hasLaw_poissonMeasure_real_singleton_eq_countLikelihood
      (mul_nonneg H.rate_nonneg
        (sub_nonneg.mpr
          (H.timeline_mono
            (show (0 : Fin 2) ≤ Fin.last 1 by decide))))
      H.count_last_hasLaw_one k

/--
For a two-window schedule, the final endpoint count is the sum of the two
adjacent increments.
-/
theorem count_last_eq_sum_adjacentIncrement_two
    {t : Fin 3 → ℝ}
    (H : FiniteSchedulePoissonCountingProcess Ω P 2 rate t)
    (ω : Ω) :
    H.count (Fin.last 2) ω =
      H.adjacentIncrement (0 : Fin 2) ω +
        H.adjacentIncrement (1 : Fin 2) ω := by
  have h0 := H.count_castSucc_add_adjacentIncrement (0 : Fin 2) ω
  have h1 := H.count_castSucc_add_adjacentIncrement (1 : Fin 2) ω
  have hz := H.count_zero ω
  simp at h0 h1 hz ⊢
  omega

/--
Finite-dimensional joint law for adjacent increments of a finite-schedule
Poisson counting process.
-/
theorem joint_real_eq_countLikelihoodProduct
    (H : FiniteSchedulePoissonCountingProcess Ω P n rate t)
    (k : Fin n → ℕ) :
    P.real (⋂ i ∈ (Finset.univ : Finset (Fin n)),
        {ω : Ω | H.adjacentIncrement i ω = k i}) =
      countLikelihoodProduct (Finset.univ : Finset (Fin n)) rate
        (fun i => t i.succ - t i.castSucc) k := by
  classical
  have hmeasure :
      P (⋂ i ∈ (Finset.univ : Finset (Fin n)),
          {ω : Ω | H.adjacentIncrement i ω = k i}) =
        ∏ i : Fin n,
          P {ω : Ω | H.adjacentIncrement i ω = k i} := by
    have h :=
      H.iIndepFun_adjacentIncrement.measure_inter_preimage_eq_mul
        (S := (Finset.univ : Finset (Fin n)))
        (sets := fun i : Fin n => ({k i} : Set ℕ))
        (by
          intro i _hi
          exact measurableSet_singleton (k i))
    simpa using h
  rw [Measure.real_def, hmeasure]
  simp only [ENNReal.toReal_prod, countLikelihoodProduct]
  refine Finset.prod_congr rfl ?_
  intro i _hi
  exact
    hasLaw_poissonMeasure_real_singleton_eq_countLikelihood
      (mul_nonneg H.rate_nonneg
        (sub_nonneg.mpr (H.timeline_mono (Fin.castSucc_le_succ i))))
      (H.adjacentIncrement_hasLaw i) (k i)

/--
Two-coordinate joint PMF for the adjacent increments of a two-window finite
schedule.
-/
theorem joint_two_real_eq_countLikelihood_mul
    {t : Fin 3 → ℝ}
    (H : FiniteSchedulePoissonCountingProcess Ω P 2 rate t)
    (a b : ℕ) :
    P.real
        ({ω : Ω | H.adjacentIncrement (0 : Fin 2) ω = a} ∩
          {ω : Ω | H.adjacentIncrement (1 : Fin 2) ω = b}) =
      countLikelihood rate
          (t ((0 : Fin 2).succ) - t ((0 : Fin 2).castSucc)) a *
        countLikelihood rate
          (t ((1 : Fin 2).succ) - t ((1 : Fin 2).castSucc)) b := by
  have h :=
    H.joint_real_eq_countLikelihoodProduct
      (fun i : Fin 2 => if i = (0 : Fin 2) then a else b)
  have hset :
      (⋂ i : Fin 2,
          {ω : Ω |
            H.adjacentIncrement i ω =
              if i = (0 : Fin 2) then a else b}) =
        ({ω : Ω | H.adjacentIncrement (0 : Fin 2) ω = a} ∩
          {ω : Ω | H.adjacentIncrement (1 : Fin 2) ω = b}) := by
    ext ω
    constructor
    · intro hω
      exact
        ⟨by simpa using Set.mem_iInter.mp hω (0 : Fin 2),
          by simpa using Set.mem_iInter.mp hω (1 : Fin 2)⟩
    · intro hω
      rw [Set.mem_iInter]
      intro i
      fin_cases i
      · simpa using hω.1
      · simpa using hω.2
  rw [← hset]
  simpa [countLikelihoodProduct] using h

/--
For a two-window schedule, the final endpoint-count event probability is the
ordinary Poisson count likelihood for the total endpoint exposure.
-/
theorem count_last_prob_two
    {t : Fin 3 → ℝ}
    (H : FiniteSchedulePoissonCountingProcess Ω P 2 rate t)
    (k : ℕ) :
    P.real {ω : Ω | H.count (Fin.last 2) ω = k} =
      countLikelihood rate (t (Fin.last 2) - t 0) k := by
  letI : IsProbabilityMeasure P := H.isProbabilityMeasure
  have hsum :
      P.real
          {ω : Ω |
            H.adjacentIncrement (0 : Fin 2) ω +
              H.adjacentIncrement (1 : Fin 2) ω = k} =
        countLikelihood rate
          ((t ((0 : Fin 2).succ) - t ((0 : Fin 2).castSucc)) +
            (t ((1 : Fin 2).succ) - t ((1 : Fin 2).castSucc))) k := by
    exact
      pair_count_sum_real_eq_countLikelihood_add
        ((H.adjacentIncrement_hasLaw (0 : Fin 2)).aemeasurable)
        ((H.adjacentIncrement_hasLaw (1 : Fin 2)).aemeasurable)
        (fun a b => H.joint_two_real_eq_countLikelihood_mul a b) k
  have hset :
      {ω : Ω | H.count (Fin.last 2) ω = k} =
        {ω : Ω |
          H.adjacentIncrement (0 : Fin 2) ω +
            H.adjacentIncrement (1 : Fin 2) ω = k} := by
    ext ω
    change H.count (Fin.last 2) ω = k ↔
      H.adjacentIncrement (0 : Fin 2) ω +
        H.adjacentIncrement (1 : Fin 2) ω = k
    rw [H.count_last_eq_sum_adjacentIncrement_two ω]
  have hexposure :
      (t ((0 : Fin 2).succ) - t ((0 : Fin 2).castSucc)) +
          (t ((1 : Fin 2).succ) - t ((1 : Fin 2).castSucc)) =
        t (Fin.last 2) - t 0 := by
    simp
  rw [hset, hsum, hexposure]

end FiniteSchedulePoissonCountingProcess

/--
Existence of the reusable finite-schedule Poisson counting-process
certificate.
-/
theorem exists_finiteSchedulePoissonCountingProcess
    (rate : ℝ) (h_rate : 0 ≤ rate)
    {n : ℕ} (t : Fin (n + 1) → ℝ) (ht : Monotone t) :
    ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ _H : FiniteSchedulePoissonCountingProcess Ω P n rate t, True := by
  rcases exists_finiteSchedulePoissonCountingProcess_fin rate h_rate t ht with
    ⟨Ω, mΩ, P, N, hzero, hmono, hLaw, hind, hprob, _hJoint⟩
  refine ⟨Ω, mΩ, P, ?_, trivial⟩
  exact
    { rate_nonneg := h_rate
      timeline_mono := ht
      count := N
      count_zero := hzero
      count_mono := hmono
      increment_hasLaw := hLaw
      iIndep_increment := hind
      isProbabilityMeasure := hprob }

/-! ## Poisson Thinning Algebra -/

/--
Real binomial thinning mass: among `trials` Poisson arrivals, exactly `kept`
are retained with success probability `successProb`.
-/
def binomialThinningMass (successProb : ℝ) (trials kept : ℕ) : ℝ :=
  if h : kept ≤ trials then
    (Nat.choose trials kept : ℝ) *
      successProb ^ kept * (1 - successProb) ^ (trials - kept)
  else
    0

theorem binomialThinningMass_eq_of_le
    {successProb : ℝ} {trials kept : ℕ} (h : kept ≤ trials) :
    binomialThinningMass successProb trials kept =
      (Nat.choose trials kept : ℝ) *
        successProb ^ kept * (1 - successProb) ^ (trials - kept) := by
  simp [binomialThinningMass, h]

theorem binomialThinningMass_eq_zero_of_lt
    {successProb : ℝ} {trials kept : ℕ} (h : trials < kept) :
    binomialThinningMass successProb trials kept = 0 := by
  simp [binomialThinningMass, not_le.mpr h]

theorem binomialThinningMass_nonneg
    {successProb : ℝ} (hprob_nonneg : 0 ≤ successProb)
    (hprob_le_one : successProb ≤ 1) (trials kept : ℕ) :
    0 ≤ binomialThinningMass successProb trials kept := by
  unfold binomialThinningMass
  by_cases h : kept ≤ trials
  · simp [h]
    exact mul_nonneg
      (mul_nonneg
        (Nat.cast_nonneg _)
        (pow_nonneg hprob_nonneg kept))
      (pow_nonneg (sub_nonneg.mpr hprob_le_one) (trials - kept))
  · simp [h]

theorem countLikelihood_mul_binomialThinningMass_nonneg
    {rate exposure successProb : ℝ}
    (h_mean : 0 ≤ rate * exposure)
    (hprob_nonneg : 0 ≤ successProb)
    (hprob_le_one : successProb ≤ 1)
    (trials kept : ℕ) :
    0 ≤ countLikelihood rate exposure trials *
      binomialThinningMass successProb trials kept := by
  exact mul_nonneg
    (countLikelihood_nonneg h_mean trials)
    (binomialThinningMass_nonneg hprob_nonneg hprob_le_one trials kept)

/--
Core reindexing identity for Poisson thinning.  The term with `kept + extra`
original arrivals and `kept` retained arrivals splits into a retained Poisson
factor times the `extra`-arrival exponential-series term for discarded arrivals.
-/
theorem countLikelihood_mul_binomialThinningMass_add_eq
    (mean successProb : ℝ) (kept extra : ℕ) :
    countLikelihood 1 mean (kept + extra) *
        binomialThinningMass successProb (kept + extra) kept =
      (Real.exp (-mean) * (mean * successProb) ^ kept /
          (kept.factorial : ℝ)) *
        ((mean * (1 - successProb)) ^ extra /
          (extra.factorial : ℝ)) := by
  have hchoose :
      ((Nat.choose (kept + extra) kept : ℕ) : ℝ) =
        ((kept + extra).factorial : ℝ) /
          ((kept.factorial : ℝ) * (extra.factorial : ℝ)) := by
    simpa using
      (Nat.cast_add_choose (K := ℝ) (a := kept) (b := extra))
  have hkept_fac : ((kept.factorial : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero kept
  have hextra_fac : ((extra.factorial : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero extra
  have htotal_fac : (((kept + extra).factorial : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (kept + extra)
  rw [binomialThinningMass_eq_of_le (Nat.le_add_right kept extra),
    countLikelihood, hchoose]
  field_simp [hkept_fac, hextra_fac, htotal_fac]
  rw [Nat.add_sub_cancel_left]
  rw [pow_add, mul_pow, mul_pow]
  ring_nf

/--
Summed reindexed Poisson-thinning identity.  After conditioning on `kept`
retained arrivals and summing over all possible discarded arrivals, the
reindexed terms have the Poisson likelihood with thinned mean
`mean * successProb`.
-/
theorem hasSum_countLikelihood_mul_binomialThinningMass_add
    (mean successProb : ℝ) (kept : ℕ) :
    HasSum
      (fun extra : ℕ =>
        countLikelihood 1 mean (kept + extra) *
          binomialThinningMass successProb (kept + extra) kept)
      (countLikelihood 1 (mean * successProb) kept) := by
  let retainedFactor : ℝ :=
    Real.exp (-mean) * (mean * successProb) ^ kept /
      (kept.factorial : ℝ)
  have hseries :
      HasSum
        (fun extra : ℕ =>
          (mean * (1 - successProb)) ^ extra /
            (extra.factorial : ℝ))
        (Real.exp (mean * (1 - successProb))) := by
    have hseriesNS :
        HasSum
          (fun extra : ℕ =>
            (mean * (1 - successProb)) ^ extra /
              (extra.factorial : ℝ))
          (NormedSpace.exp (mean * (1 - successProb))) :=
      (NormedSpace.expSeries_div_hasSum_exp (mean * (1 - successProb)) :
        HasSum
          (fun extra : ℕ =>
            (mean * (1 - successProb)) ^ extra /
              (extra.factorial : ℝ))
          (NormedSpace.exp (mean * (1 - successProb))))
    have hexp :
        NormedSpace.exp (mean * (1 - successProb)) =
          Real.exp (mean * (1 - successProb)) := by
      exact (congr_fun Real.exp_eq_exp_ℝ
        (mean * (1 - successProb))).symm
    rwa [← hexp]
  have hsum :
      HasSum
        (fun extra : ℕ =>
          retainedFactor *
            ((mean * (1 - successProb)) ^ extra /
              (extra.factorial : ℝ)))
        (retainedFactor * Real.exp (mean * (1 - successProb))) :=
    hseries.mul_left retainedFactor
  have hcongr :
      (fun extra : ℕ =>
        countLikelihood 1 mean (kept + extra) *
          binomialThinningMass successProb (kept + extra) kept) =
      (fun extra : ℕ =>
        retainedFactor *
          ((mean * (1 - successProb)) ^ extra /
            (extra.factorial : ℝ))) := by
    funext extra
    exact countLikelihood_mul_binomialThinningMass_add_eq
      mean successProb kept extra
  rw [hcongr]
  convert hsum using 1
  · rw [countLikelihood]
    dsimp [retainedFactor]
    rw [show -(1 * (mean * successProb)) =
        -mean + mean * (1 - successProb) by ring, Real.exp_add]
    ring

/-- Tsum form of the reindexed Poisson-thinning identity. -/
theorem tsum_countLikelihood_mul_binomialThinningMass_add
    (mean successProb : ℝ) (kept : ℕ) :
    (∑' extra : ℕ,
        countLikelihood 1 mean (kept + extra) *
          binomialThinningMass successProb (kept + extra) kept) =
      countLikelihood 1 (mean * successProb) kept :=
  (hasSum_countLikelihood_mul_binomialThinningMass_add
    mean successProb kept).tsum_eq

/-
Full Poisson-thinning identity as a `HasSum` over the original arrival count.
The finite prefix below `kept` contributes zero binomial mass; the remaining
tail is the reindexed discarded-arrival sum.
-/
set_option maxHeartbeats 800000 in
-- The shift lemma elaborates a finite-prefix expression for an arbitrary
-- `kept`; the proof is small but needs extra normalization budget.
theorem hasSum_countLikelihood_mul_binomialThinningMass
    (mean successProb : ℝ) (kept : ℕ) :
    HasSum
      (fun trials : ℕ =>
        countLikelihood 1 mean trials *
          binomialThinningMass successProb trials kept)
      (countLikelihood 1 (mean * successProb) kept) := by
  let f : ℕ → ℝ := fun trials =>
    countLikelihood 1 mean trials *
      binomialThinningMass successProb trials kept
  have htail :
      HasSum (fun extra : ℕ => f (extra + kept))
        (countLikelihood 1 (mean * successProb) kept) := by
    simpa [f, Nat.add_comm] using
      hasSum_countLikelihood_mul_binomialThinningMass_add
        mean successProb kept
  have hprefix : (∑ trials ∈ Finset.range kept, f trials) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro trials htrials
    have hlt : trials < kept := Finset.mem_range.mp htrials
    simp [f, binomialThinningMass_eq_zero_of_lt hlt]
  have htail_shift :
      HasSum (fun extra : ℕ => f (extra + kept))
        ((countLikelihood 1 (mean * successProb) kept +
            ∑ trials ∈ Finset.range kept, f trials) -
          ∑ trials ∈ Finset.range kept, f trials) := by
    simpa [hprefix] using htail
  have hfull := (hasSum_nat_add_iff' kept).mp htail_shift
  change HasSum f (countLikelihood 1 (mean * successProb) kept)
  simpa only [hprefix, add_zero] using hfull

/-- Tsum form of the full Poisson-thinning identity. -/
theorem tsum_countLikelihood_mul_binomialThinningMass
    (mean successProb : ℝ) (kept : ℕ) :
    (∑' trials : ℕ,
        countLikelihood 1 mean trials *
          binomialThinningMass successProb trials kept) =
      countLikelihood 1 (mean * successProb) kept :=
  (hasSum_countLikelihood_mul_binomialThinningMass
    mean successProb kept).tsum_eq

/-! ## Poisson Thinning Count Certificates -/

/--
Reusable certificate for a Poisson count thinned by independent Bernoulli
retention.

The field `observedMass_eq_tsum` is the stochastic-model boundary: it says the
observed count mass is obtained by summing the latent Poisson incident count
against the binomial thinning mass.  The theorem below then proves the thinned
count is Poisson with mean `incidentMean * successProb`.
-/
structure PoissonThinningCountLaw where
  incidentMean : ℝ
  successProb : ℝ
  observedMass : ℕ → ℝ
  observedMass_eq_tsum :
    ∀ kept : ℕ,
      observedMass kept =
        ∑' trials : ℕ,
          countLikelihood 1 incidentMean trials *
            binomialThinningMass successProb trials kept

namespace PoissonThinningCountLaw

/--
Canonical thinning certificate whose observed mass is defined by the latent
Poisson count mixture itself.
-/
def ofMixture (incidentMean successProb : ℝ) : PoissonThinningCountLaw where
  incidentMean := incidentMean
  successProb := successProb
  observedMass := fun kept =>
    ∑' trials : ℕ,
      countLikelihood 1 incidentMean trials *
        binomialThinningMass successProb trials kept
  observedMass_eq_tsum := by
    intro kept
    rfl

@[simp] theorem ofMixture_observedMass
    (incidentMean successProb : ℝ) (kept : ℕ) :
    (ofMixture incidentMean successProb).observedMass kept =
      ∑' trials : ℕ,
        countLikelihood 1 incidentMean trials *
          binomialThinningMass successProb trials kept := rfl

/-- The observed thinned count has Poisson mass with thinned mean. -/
theorem observedMass_eq_countLikelihood
    (L : PoissonThinningCountLaw) (kept : ℕ) :
    L.observedMass kept =
      countLikelihood 1 (L.incidentMean * L.successProb) kept := by
  rw [L.observedMass_eq_tsum kept]
  exact tsum_countLikelihood_mul_binomialThinningMass
    L.incidentMean L.successProb kept

/--
The observed thinned count mass is nonnegative under nonnegative incident mean
and Bernoulli-probability bounds.
-/
theorem observedMass_nonneg
    (L : PoissonThinningCountLaw)
    (hincidentMean : 0 ≤ L.incidentMean)
    (hprob_nonneg : 0 ≤ L.successProb)
    (hprob_le_one : L.successProb ≤ 1)
    (kept : ℕ) :
    0 ≤ L.observedMass kept := by
  rw [L.observedMass_eq_countLikelihood kept]
  exact countLikelihood_nonneg
    (by
      have hprod := mul_nonneg hincidentMean hprob_nonneg
      simpa using hprod)
    kept

end PoissonThinningCountLaw

/--
Rate-independent residual in a finite product of Poisson count likelihoods.
The product likelihood equals this residual times
`rate^(total count) * exp (-(rate * total exposure))`.
-/
def countLikelihoodProductResidual {ι : Type*} (s : Finset ι)
    (exposure : ι → ℝ) (count : ι → ℕ) : ℝ :=
  ∏ i ∈ s, exposure i ^ count i / ((count i).factorial : ℝ)

theorem countLikelihoodProduct_eq_residual_rawShape
    {ι : Type*} (s : Finset ι)
    (rate : ℝ) (exposure : ι → ℝ) (count : ι → ℕ) :
    countLikelihoodProduct s rate exposure count =
      countLikelihoodProductResidual s exposure count *
        rate ^ totalCount s count *
          Real.exp (-(rate * totalExposure s exposure)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [countLikelihoodProduct, countLikelihoodProductResidual,
        totalCount, totalExposure]
  | insert a s ha ih =>
      have ih' :
          (∏ i ∈ s, countLikelihood rate (exposure i) (count i)) =
            (∏ i ∈ s, exposure i ^ count i / ((count i).factorial : ℝ)) *
              rate ^ (∑ i ∈ s, count i) *
                Real.exp (-(rate * ∑ i ∈ s, exposure i)) := by
        simpa [countLikelihoodProduct, countLikelihoodProductResidual,
          totalCount, totalExposure] using ih
      rw [countLikelihoodProduct, countLikelihoodProductResidual,
        totalCount, totalExposure]
      simp only [Finset.prod_insert, Finset.sum_insert, ha, not_false_eq_true]
      rw [ih']
      simp [countLikelihood, mul_pow, pow_add]
      rw [show -(rate * (exposure a + ∑ i ∈ s, exposure i)) =
          -(rate * exposure a) + -(rate * ∑ i ∈ s, exposure i) by ring,
        Real.exp_add]
      ring_nf

/--
Finite multinomial convolution for Poisson count likelihood products.

Summing the independent product mass over all count vectors on `s` with total
count `n` gives the single Poisson mass at total exposure.
-/
theorem sum_countLikelihoodProduct_piAntidiag_eq_countLikelihood_total
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (rate : ℝ) (exposure : ι → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.piAntidiag s n,
        countLikelihoodProduct s rate exposure k) =
      countLikelihood rate (totalExposure s exposure) n := by
  classical
  rw [countLikelihood]
  rw [show ∑ k ∈ Finset.piAntidiag s n,
        countLikelihoodProduct s rate exposure k =
      ∑ k ∈ Finset.piAntidiag s n,
        countLikelihoodProductResidual s exposure k *
          rate ^ n * Real.exp (-(rate * totalExposure s exposure)) by
    refine Finset.sum_congr rfl ?_
    intro k hk
    rw [countLikelihoodProduct_eq_residual_rawShape]
    have hk_sum : totalCount s k = n := by
      simpa [totalCount] using (Finset.mem_piAntidiag.mp hk).1
    rw [hk_sum]]
  rw [← Finset.sum_mul]
  rw [← Finset.sum_mul]
  have hres :
      (∑ k ∈ Finset.piAntidiag s n,
          countLikelihoodProductResidual s exposure k) =
        (totalExposure s exposure) ^ n / (n.factorial : ℝ) := by
    rw [totalExposure]
    have hpow :
        (∑ i ∈ s, exposure i) ^ n =
          ∑ k ∈ Finset.piAntidiag s n,
            Nat.multinomial s k *
              ∏ i ∈ s, exposure i ^ k i := by
      exact Finset.sum_pow_eq_sum_piAntidiag s exposure n
    rw [hpow]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl ?_
    intro k hk
    rw [countLikelihoodProductResidual]
    have hspec :
        (∏ i ∈ s, (k i).factorial) * Nat.multinomial s k =
          n.factorial := by
      have hk_sum : ∑ i ∈ s, k i = n :=
        (Finset.mem_piAntidiag.mp hk).1
      simpa [hk_sum] using (Nat.multinomial_spec s k)
    have hfac :
        ((∏ i ∈ s, (k i).factorial : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast
        Finset.prod_ne_zero_iff.mpr
          (by intro i _hi; exact Nat.factorial_ne_zero (k i))
    have hfac' : ((n.factorial : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero n
    have hspecR :
        ((∏ i ∈ s, (k i).factorial : ℕ) : ℝ) *
            (Nat.multinomial s k : ℝ) =
          (n.factorial : ℝ) := by
      exact_mod_cast hspec
    have hprod_cast :
        (∏ i ∈ s, ((k i).factorial : ℝ)) =
          ((∏ i ∈ s, (k i).factorial : ℕ) : ℝ) := by
      norm_cast
    rw [Finset.prod_div_distrib]
    field_simp [hfac, hfac']
    rw [hprod_cast]
    rw [← hspecR]
    ring
  rw [hres]
  ring

/--
Finite total-count event partition for natural-valued coordinates.

The event that a finite family of count variables has total `n` is the
disjoint union over all count vectors in `piAntidiag univ n`.
-/
theorem finite_count_sum_real_eq_sum_joint
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {P : Measure Ω} [IsFiniteMeasure P]
    {X : ι → Ω → ℕ} (hX : ∀ i, AEMeasurable (X i) P)
    (n : ℕ) :
    P.real {ω : Ω | (∑ i : ι, X i ω) = n} =
      ∑ k ∈ Finset.piAntidiag (Finset.univ : Finset ι) n,
        P.real (⋂ i ∈ (Finset.univ : Finset ι),
          {ω : Ω | X i ω = k i}) := by
  classical
  let A : (ι → ℕ) → Set Ω := fun k =>
    ⋂ i ∈ (Finset.univ : Finset ι), {ω : Ω | X i ω = k i}
  have hnull :
      ∀ k ∈ Finset.piAntidiag (Finset.univ : Finset ι) n,
        NullMeasurableSet (A k) P := by
    intro k _hk
    exact (Finset.univ : Finset ι).nullMeasurableSet_biInter
      (fun i _hi =>
        (hX i).nullMeasurableSet_preimage (measurableSet_singleton (k i)))
  have hdis :
      Set.Pairwise
        (↑(Finset.piAntidiag (Finset.univ : Finset ι) n) :
          Set (ι → ℕ))
        (fun k l => AEDisjoint P (A k) (A l)) := by
    intro k _hk l _hl hkl
    have hdisjoint : Disjoint (A k) (A l) := by
      rw [Set.disjoint_left]
      intro ω hωk hωl
      have hexists : ∃ i, k i ≠ l i := by
        by_contra h
        push Not at h
        exact hkl (funext h)
      rcases hexists with ⟨i, hi⟩
      have hk_i : X i ω = k i := by
        simpa [A] using
          Set.mem_iInter₂.mp hωk i (Finset.mem_univ i)
      have hl_i : X i ω = l i := by
        simpa [A] using
          Set.mem_iInter₂.mp hωl i (Finset.mem_univ i)
      exact hi (hk_i.symm.trans hl_i)
    exact hdisjoint.aedisjoint
  have hUnion :
      {ω : Ω | (∑ i : ι, X i ω) = n} =
        ⋃ k ∈ Finset.piAntidiag (Finset.univ : Finset ι) n, A k := by
    ext ω
    constructor
    · intro hsum
      let k : ι → ℕ := fun i => X i ω
      refine Set.mem_iUnion.mpr ⟨k, ?_⟩
      refine Set.mem_iUnion.mpr ⟨?_, ?_⟩
      · rw [Finset.mem_piAntidiag]
        constructor
        · simpa [k] using hsum
        · intro i _hi
          exact Finset.mem_univ i
      · rw [Set.mem_iInter₂]
        intro _i _hi
        rfl
    · intro hω
      rcases Set.mem_iUnion.mp hω with ⟨k, hk⟩
      rcases Set.mem_iUnion.mp hk with ⟨hkanti, hAk⟩
      have hsum_k : ∑ i : ι, k i = n := by
        simpa using (Finset.mem_piAntidiag.mp hkanti).1
      calc
        (∑ i : ι, X i ω) = ∑ i : ι, k i := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          simpa [A] using
            Set.mem_iInter₂.mp hAk i (Finset.mem_univ i)
        _ = n := hsum_k
  calc
    P.real {ω : Ω | (∑ i : ι, X i ω) = n} =
        P.real (⋃ k ∈ Finset.piAntidiag (Finset.univ : Finset ι) n, A k) := by
      rw [hUnion]
    _ = ∑ k ∈ Finset.piAntidiag (Finset.univ : Finset ι) n,
          P.real (A k) := by
      exact measureReal_biUnion_finset₀ hdis hnull
    _ = ∑ k ∈ Finset.piAntidiag (Finset.univ : Finset ι) n,
          P.real (⋂ i ∈ (Finset.univ : Finset ι),
            {ω : Ω | X i ω = k i}) := by
      rfl

/--
Finite convolution theorem at the event level: if a finite family has the
joint independent Poisson product PMF, then its total count has the Poisson
PMF at total exposure.
-/
theorem finite_count_sum_real_eq_countLikelihood_total
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {P : Measure Ω} [IsFiniteMeasure P]
    {X : ι → Ω → ℕ} (hX : ∀ i, AEMeasurable (X i) P)
    {rate : ℝ} {exposure : ι → ℝ}
    (hJoint : ∀ k : ι → ℕ,
      P.real (⋂ i ∈ (Finset.univ : Finset ι),
          {ω : Ω | X i ω = k i}) =
        countLikelihoodProduct (Finset.univ : Finset ι) rate exposure k)
    (n : ℕ) :
    P.real {ω : Ω | (∑ i : ι, X i ω) = n} =
      countLikelihood rate
        (totalExposure (Finset.univ : Finset ι) exposure) n := by
  rw [finite_count_sum_real_eq_sum_joint hX n]
  calc
    (∑ k ∈ Finset.piAntidiag (Finset.univ : Finset ι) n,
        P.real (⋂ i ∈ (Finset.univ : Finset ι),
          {ω : Ω | X i ω = k i})) =
        ∑ k ∈ Finset.piAntidiag (Finset.univ : Finset ι) n,
          countLikelihoodProduct (Finset.univ : Finset ι) rate exposure k := by
      refine Finset.sum_congr rfl ?_
      intro k _hk
      exact hJoint k
    _ = countLikelihood rate
          (totalExposure (Finset.univ : Finset ι) exposure) n := by
      exact sum_countLikelihoodProduct_piAntidiag_eq_countLikelihood_total
        (Finset.univ : Finset ι) rate exposure n

namespace FiniteSchedulePoissonCountingProcess

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {n : ℕ} {rate : ℝ} {t : Fin (n + 1) → ℝ}

/--
For an arbitrary finite schedule, the final endpoint-count event probability
is the ordinary Poisson count likelihood for the total endpoint exposure.
-/
theorem count_last_prob
    (H : FiniteSchedulePoissonCountingProcess Ω P n rate t)
    (k : ℕ) :
    P.real {ω : Ω | H.count (Fin.last n) ω = k} =
      countLikelihood rate (t (Fin.last n) - t 0) k := by
  letI : IsProbabilityMeasure P := H.isProbabilityMeasure
  have hsum :
      P.real {ω : Ω | (∑ i : Fin n, H.adjacentIncrement i ω) = k} =
        countLikelihood rate
          (totalExposure (Finset.univ : Finset (Fin n))
            (fun i => t i.succ - t i.castSucc)) k := by
    exact
      finite_count_sum_real_eq_countLikelihood_total
        (fun i => (H.adjacentIncrement_hasLaw i).aemeasurable)
        (fun kk => H.joint_real_eq_countLikelihoodProduct kk) k
  have hset :
      {ω : Ω | H.count (Fin.last n) ω = k} =
        {ω : Ω | (∑ i : Fin n, H.adjacentIncrement i ω) = k} := by
    ext ω
    change H.count (Fin.last n) ω = k ↔
      (∑ i : Fin n, H.adjacentIncrement i ω) = k
    rw [H.count_last_eq_sum_adjacentIncrement ω]
  rw [hset, hsum, totalExposure_fin_adjacent_timeline_diffs]

end FiniteSchedulePoissonCountingProcess

/--
Existence of the reusable finite-schedule process certificate together with
the final endpoint-count Poisson PMF.
-/
theorem exists_finiteSchedulePoissonCountingProcess_final_endpoint
    (rate : ℝ) (h_rate : 0 ≤ rate)
    {n : ℕ} (t : Fin (n + 1) → ℝ) (ht : Monotone t) :
    ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ H : FiniteSchedulePoissonCountingProcess Ω P n rate t,
        ∀ k : ℕ,
          P.real {ω : Ω | H.count (Fin.last n) ω = k} =
            countLikelihood rate (t (Fin.last n) - t 0) k := by
  rcases exists_finiteSchedulePoissonCountingProcess rate h_rate t ht with
    ⟨Ω, mΩ, P, H, _⟩
  exact ⟨Ω, mΩ, P, H, fun k => H.count_last_prob k⟩

/-! ## Stopping-time and observation-window bookkeeping -/

/--
Lightweight real-valued stopping-time predicate for a continuous-time
filtration.  A random time `τ` is stopping when `{ω | τ ω ≤ t}` is measurable
at time `t`.
-/
def IsStoppingTime
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (𝓕 : Filtration (Ω := Ω) ℝ mΩ) (τ : Ω → ℝ) : Prop :=
  ∀ t : ℝ, MeasurableSet[𝓕 t] {ω | τ ω ≤ t}

namespace IsStoppingTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {𝓕 : Filtration (Ω := Ω) ℝ mΩ}
variable {τ σ ρ : Ω → ℝ}

/-- A deterministic time is a stopping time for every filtration. -/
theorem const (c : ℝ) :
    IsStoppingTime 𝓕 (fun _ : Ω => c) := by
  intro t
  by_cases h : c ≤ t
  · have hset : {ω : Ω | (fun _ : Ω => c) ω ≤ t} = Set.univ := by
      ext ω
      simp [h]
    simpa [hset]
  · have hset : {ω : Ω | (fun _ : Ω => c) ω ≤ t} = ∅ := by
      ext ω
      simp [h]
    simpa [hset]

/--
Adding a nonnegative deterministic delay to a stopping time preserves the
stopping-time property.
-/
theorem add_const_nonneg
    (hτ : IsStoppingTime 𝓕 τ) {c : ℝ} (hc : 0 ≤ c) :
    IsStoppingTime 𝓕 (fun ω => τ ω + c) := by
  intro t
  have hset : {ω : Ω | τ ω + c ≤ t} = {ω : Ω | τ ω ≤ t - c} := by
    ext ω
    constructor
    · intro h
      have h' : τ ω + c ≤ t := by simpa using h
      change τ ω ≤ t - c
      linarith
    · intro h
      have h' : τ ω ≤ t - c := by simpa using h
      change τ ω + c ≤ t
      linarith
  exact (𝓕.mono (by linarith : t - c ≤ t)) _ (by
    simpa [hset] using hτ (t - c))

/-- The pointwise minimum of two stopping times is a stopping time. -/
theorem min
    (hτ : IsStoppingTime 𝓕 τ) (hσ : IsStoppingTime 𝓕 σ) :
    IsStoppingTime 𝓕 (fun ω => @Min.min ℝ _ (τ ω) (σ ω)) := by
  intro t
  simpa [min_le_iff, Set.setOf_or] using (hτ t).union (hσ t)

/-- The pointwise maximum of two stopping times is a stopping time. -/
theorem max
    (hτ : IsStoppingTime 𝓕 τ) (hσ : IsStoppingTime 𝓕 σ) :
    IsStoppingTime 𝓕 (fun ω => @Max.max ℝ _ (τ ω) (σ ω)) := by
  intro t
  simpa [max_le_iff, Set.setOf_and] using (hτ t).inter (hσ t)

/-- The pointwise minimum of three stopping times is a stopping time. -/
theorem min3
    (hτ : IsStoppingTime 𝓕 τ) (hσ : IsStoppingTime 𝓕 σ)
    (hρ : IsStoppingTime 𝓕 ρ) :
    IsStoppingTime 𝓕
      (fun ω => @Min.min ℝ _ (@Min.min ℝ _ (τ ω) (σ ω)) (ρ ω)) :=
  (hτ.min hσ).min hρ

end IsStoppingTime

/--
The count-threshold events of a counting process are adapted to a filtration.

For a first-arrival time at threshold `1`, this says the event "the count has
reached one by time `t`" is observable at time `t`.
-/
def CountThresholdEventAdapted
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (𝓕 : Filtration (Ω := Ω) ℝ mΩ) (count : ℝ → Ω → ℕ)
    (threshold : ℕ) : Prop :=
  ∀ t : ℝ, MeasurableSet[𝓕 t] {ω | threshold ≤ count t ω}

namespace CountThresholdEventAdapted

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {𝓕 : Filtration (Ω := Ω) ℝ mΩ}
variable {count : ℝ → Ω → ℕ} {threshold : ℕ}

/--
Count-threshold events are adapted when each count coordinate is measurable at
its filtration time.
-/
theorem of_measurable_count
    (hcount : ∀ t : ℝ, Measurable[𝓕 t] (count t)) :
    CountThresholdEventAdapted 𝓕 count threshold := by
  intro t
  exact (hcount t) measurableSet_Ici

end CountThresholdEventAdapted

/--
If a random time has the same sublevel events as an adapted count-threshold
event, then it is a stopping time.
-/
theorem isStoppingTime_of_count_threshold_level_sets
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {𝓕 : Filtration (Ω := Ω) ℝ mΩ} {count : ℝ → Ω → ℕ}
    {threshold : ℕ} {τ : Ω → ℝ}
    (hadapted : CountThresholdEventAdapted 𝓕 count threshold)
    (hlevel :
      ∀ t : ℝ, {ω | τ ω ≤ t} = {ω | threshold ≤ count t ω}) :
    IsStoppingTime 𝓕 τ := by
  intro t
  rw [hlevel t]
  exact hadapted t

/--
Certificate that a random time is the first count-arrival time of an adapted
counting process, at threshold one.
-/
structure FirstCountArrivalCertificate
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (𝓕 : Filtration (Ω := Ω) ℝ mΩ) (count : ℝ → Ω → ℕ)
    (arrivalTime : Ω → ℝ) where
  count_event_adapted : CountThresholdEventAdapted 𝓕 count 1
  level_sets :
    ∀ t : ℝ, {ω | arrivalTime ω ≤ t} = {ω | 1 ≤ count t ω}

namespace FirstCountArrivalCertificate

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {𝓕 : Filtration (Ω := Ω) ℝ mΩ}
variable {count : ℝ → Ω → ℕ} {arrivalTime : Ω → ℝ}

/-- A certified first count-arrival time is a stopping time. -/
theorem isStoppingTime
    (C : FirstCountArrivalCertificate 𝓕 count arrivalTime) :
    IsStoppingTime 𝓕 arrivalTime :=
  isStoppingTime_of_count_threshold_level_sets
    C.count_event_adapted C.level_sets

end FirstCountArrivalCertificate

/-- Deterministic observation window with nonnegative exposure. -/
structure ObservationWindow where
  startTime : ℝ
  endTime : ℝ
  start_le_end : startTime ≤ endTime

namespace ObservationWindow

/-- Exposure length of an observation window. -/
def exposure (W : ObservationWindow) : ℝ :=
  W.endTime - W.startTime

theorem exposure_nonneg (W : ObservationWindow) :
    0 ≤ W.exposure := by
  exact sub_nonneg.mpr W.start_le_end

theorem exposure_pos_of_lt (W : ObservationWindow)
    (h_start_lt_end : W.startTime < W.endTime) :
    0 < W.exposure := by
  exact sub_pos.mpr h_start_lt_end

theorem rate_mul_exposure_nonneg (W : ObservationWindow)
    {rate : ℝ} (h_rate : 0 ≤ rate) :
    0 ≤ rate * W.exposure :=
  mul_nonneg h_rate W.exposure_nonneg

/--
Observation window whose end is the earlier of two candidate stopping times.

This is a deterministic bookkeeping helper for papers that construct
observation intervals by censoring at the first of several endpoint rules.
-/
def ofMinEnd (start end₁ end₂ : ℝ)
    (h₁ : start ≤ end₁) (h₂ : start ≤ end₂) : ObservationWindow where
  startTime := start
  endTime := min end₁ end₂
  start_le_end := le_min h₁ h₂

@[simp] theorem ofMinEnd_startTime
    (start end₁ end₂ : ℝ) (h₁ : start ≤ end₁) (h₂ : start ≤ end₂) :
    (ofMinEnd start end₁ end₂ h₁ h₂).startTime = start := rfl

@[simp] theorem ofMinEnd_endTime
    (start end₁ end₂ : ℝ) (h₁ : start ≤ end₁) (h₂ : start ≤ end₂) :
    (ofMinEnd start end₁ end₂ h₁ h₂).endTime = min end₁ end₂ := rfl

theorem ofMinEnd_endTime_le_left
    (start end₁ end₂ : ℝ) (h₁ : start ≤ end₁) (h₂ : start ≤ end₂) :
    (ofMinEnd start end₁ end₂ h₁ h₂).endTime ≤ end₁ :=
  min_le_left end₁ end₂

theorem ofMinEnd_endTime_le_right
    (start end₁ end₂ : ℝ) (h₁ : start ≤ end₁) (h₂ : start ≤ end₂) :
    (ofMinEnd start end₁ end₂ h₁ h₂).endTime ≤ end₂ :=
  min_le_right end₁ end₂

theorem ofMinEnd_exposure_le_left_duration
    (start end₁ end₂ : ℝ) (h₁ : start ≤ end₁) (h₂ : start ≤ end₂) :
    (ofMinEnd start end₁ end₂ h₁ h₂).exposure ≤ end₁ - start := by
  exact sub_le_sub_right
    (ofMinEnd_endTime_le_left start end₁ end₂ h₁ h₂) start

theorem ofMinEnd_exposure_le_right_duration
    (start end₁ end₂ : ℝ) (h₁ : start ≤ end₁) (h₂ : start ≤ end₂) :
    (ofMinEnd start end₁ end₂ h₁ h₂).exposure ≤ end₂ - start := by
  exact sub_le_sub_right
    (ofMinEnd_endTime_le_right start end₁ end₂ h₁ h₂) start

theorem ofMinEnd_start_lt_end
    (start end₁ end₂ : ℝ) (h₁ : start < end₁) (h₂ : start < end₂) :
    start < (ofMinEnd start end₁ end₂ (le_of_lt h₁) (le_of_lt h₂)).endTime :=
  lt_min h₁ h₂

theorem ofMinEnd_exposure_pos
    (start end₁ end₂ : ℝ) (h₁ : start < end₁) (h₂ : start < end₂) :
    0 < (ofMinEnd start end₁ end₂
      (le_of_lt h₁) (le_of_lt h₂)).exposure :=
  exposure_pos_of_lt _
    (ofMinEnd_start_lt_end start end₁ end₂ h₁ h₂)

/--
Observation window whose end is the earliest of three candidate stopping times.
-/
def ofMinEnd3 (start end₁ end₂ end₃ : ℝ)
    (h₁ : start ≤ end₁) (h₂ : start ≤ end₂) (h₃ : start ≤ end₃) :
    ObservationWindow where
  startTime := start
  endTime := min (min end₁ end₂) end₃
  start_le_end := le_min (le_min h₁ h₂) h₃

@[simp] theorem ofMinEnd3_startTime
    (start end₁ end₂ end₃ : ℝ)
    (h₁ : start ≤ end₁) (h₂ : start ≤ end₂) (h₃ : start ≤ end₃) :
    (ofMinEnd3 start end₁ end₂ end₃ h₁ h₂ h₃).startTime = start := rfl

@[simp] theorem ofMinEnd3_endTime
    (start end₁ end₂ end₃ : ℝ)
    (h₁ : start ≤ end₁) (h₂ : start ≤ end₂) (h₃ : start ≤ end₃) :
    (ofMinEnd3 start end₁ end₂ end₃ h₁ h₂ h₃).endTime =
      min (min end₁ end₂) end₃ := rfl

theorem ofMinEnd3_endTime_le_first
    (start end₁ end₂ end₃ : ℝ)
    (h₁ : start ≤ end₁) (h₂ : start ≤ end₂) (h₃ : start ≤ end₃) :
    (ofMinEnd3 start end₁ end₂ end₃ h₁ h₂ h₃).endTime ≤ end₁ :=
  le_trans (min_le_left (min end₁ end₂) end₃) (min_le_left end₁ end₂)

theorem ofMinEnd3_endTime_le_second
    (start end₁ end₂ end₃ : ℝ)
    (h₁ : start ≤ end₁) (h₂ : start ≤ end₂) (h₃ : start ≤ end₃) :
    (ofMinEnd3 start end₁ end₂ end₃ h₁ h₂ h₃).endTime ≤ end₂ :=
  le_trans (min_le_left (min end₁ end₂) end₃) (min_le_right end₁ end₂)

theorem ofMinEnd3_endTime_le_third
    (start end₁ end₂ end₃ : ℝ)
    (h₁ : start ≤ end₁) (h₂ : start ≤ end₂) (h₃ : start ≤ end₃) :
    (ofMinEnd3 start end₁ end₂ end₃ h₁ h₂ h₃).endTime ≤ end₃ :=
  min_le_right (min end₁ end₂) end₃

theorem ofMinEnd3_exposure_le_first_duration
    (start end₁ end₂ end₃ : ℝ)
    (h₁ : start ≤ end₁) (h₂ : start ≤ end₂) (h₃ : start ≤ end₃) :
    (ofMinEnd3 start end₁ end₂ end₃ h₁ h₂ h₃).exposure ≤ end₁ - start := by
  exact sub_le_sub_right
    (ofMinEnd3_endTime_le_first start end₁ end₂ end₃ h₁ h₂ h₃) start

theorem ofMinEnd3_exposure_le_second_duration
    (start end₁ end₂ end₃ : ℝ)
    (h₁ : start ≤ end₁) (h₂ : start ≤ end₂) (h₃ : start ≤ end₃) :
    (ofMinEnd3 start end₁ end₂ end₃ h₁ h₂ h₃).exposure ≤ end₂ - start := by
  exact sub_le_sub_right
    (ofMinEnd3_endTime_le_second start end₁ end₂ end₃ h₁ h₂ h₃) start

theorem ofMinEnd3_exposure_le_third_duration
    (start end₁ end₂ end₃ : ℝ)
    (h₁ : start ≤ end₁) (h₂ : start ≤ end₂) (h₃ : start ≤ end₃) :
    (ofMinEnd3 start end₁ end₂ end₃ h₁ h₂ h₃).exposure ≤ end₃ - start := by
  exact sub_le_sub_right
    (ofMinEnd3_endTime_le_third start end₁ end₂ end₃ h₁ h₂ h₃) start

theorem ofMinEnd3_exposure_le_duration_cap
    (start durationCap end₂ end₃ : ℝ)
    (h_cap : 0 ≤ durationCap)
    (h₂ : start ≤ end₂) (h₃ : start ≤ end₃) :
    (ofMinEnd3 start (start + durationCap) end₂ end₃
      (le_add_of_nonneg_right h_cap) h₂ h₃).exposure ≤ durationCap := by
  have h := ofMinEnd3_exposure_le_first_duration
    start (start + durationCap) end₂ end₃
    (le_add_of_nonneg_right h_cap) h₂ h₃
  have hsub : (start + durationCap) - start = durationCap := by
    ring
  simpa [hsub] using h

theorem ofMinEnd3_start_lt_end
    (start end₁ end₂ end₃ : ℝ)
    (h₁ : start < end₁) (h₂ : start < end₂) (h₃ : start < end₃) :
    start <
      (ofMinEnd3 start end₁ end₂ end₃
        (le_of_lt h₁) (le_of_lt h₂) (le_of_lt h₃)).endTime :=
  lt_min (lt_min h₁ h₂) h₃

theorem ofMinEnd3_exposure_pos
    (start end₁ end₂ end₃ : ℝ)
    (h₁ : start < end₁) (h₂ : start < end₂) (h₃ : start < end₃) :
    0 <
      (ofMinEnd3 start end₁ end₂ end₃
        (le_of_lt h₁) (le_of_lt h₂) (le_of_lt h₃)).exposure :=
  exposure_pos_of_lt _
    (ofMinEnd3_start_lt_end start end₁ end₂ end₃ h₁ h₂ h₃)

end ObservationWindow

/--
Random observation window whose start and end are stopping times for a
filtration and whose exposure is pathwise nonnegative.
-/
structure StoppingObservationWindow
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (𝓕 : Filtration (Ω := Ω) ℝ mΩ) where
  startTime : Ω → ℝ
  endTime : Ω → ℝ
  start_stopping : IsStoppingTime 𝓕 startTime
  end_stopping : IsStoppingTime 𝓕 endTime
  start_le_end : ∀ ω, startTime ω ≤ endTime ω

namespace StoppingObservationWindow

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {𝓕 : Filtration (Ω := Ω) ℝ mΩ}

/-- Pathwise exposure length of a stopping observation window. -/
def exposure (W : StoppingObservationWindow 𝓕) (ω : Ω) : ℝ :=
  W.endTime ω - W.startTime ω

theorem exposure_nonneg (W : StoppingObservationWindow 𝓕) (ω : Ω) :
    0 ≤ W.exposure ω := by
  exact sub_nonneg.mpr (W.start_le_end ω)

/--
The deterministic observation window realized by a stopping observation window
on a single sample path.
-/
def toObservationWindow (W : StoppingObservationWindow 𝓕) (ω : Ω) :
    ObservationWindow where
  startTime := W.startTime ω
  endTime := W.endTime ω
  start_le_end := W.start_le_end ω

@[simp] theorem toObservationWindow_startTime
    (W : StoppingObservationWindow 𝓕) (ω : Ω) :
    (W.toObservationWindow ω).startTime = W.startTime ω := rfl

@[simp] theorem toObservationWindow_endTime
    (W : StoppingObservationWindow 𝓕) (ω : Ω) :
    (W.toObservationWindow ω).endTime = W.endTime ω := rfl

@[simp] theorem toObservationWindow_exposure
    (W : StoppingObservationWindow 𝓕) (ω : Ω) :
    (W.toObservationWindow ω).exposure = W.exposure ω := rfl

/-- A deterministic observation window is a stopping observation window. -/
def ofObservationWindow (W : ObservationWindow) :
    StoppingObservationWindow 𝓕 where
  startTime := fun _ => W.startTime
  endTime := fun _ => W.endTime
  start_stopping := IsStoppingTime.const W.startTime
  end_stopping := IsStoppingTime.const W.endTime
  start_le_end := fun _ => W.start_le_end

@[simp] theorem ofObservationWindow_startTime
    (W : ObservationWindow) :
    (ofObservationWindow (𝓕 := 𝓕) W).startTime =
      fun _ : Ω => W.startTime := rfl

@[simp] theorem ofObservationWindow_endTime
    (W : ObservationWindow) :
    (ofObservationWindow (𝓕 := 𝓕) W).endTime =
      fun _ : Ω => W.endTime := rfl

/--
Stopping observation window whose end is the earlier of two stopping endpoint
rules.
-/
def ofMinEnd
    (start end₁ end₂ : Ω → ℝ)
    (hstart : IsStoppingTime 𝓕 start)
    (h₁ : IsStoppingTime 𝓕 end₁)
    (h₂ : IsStoppingTime 𝓕 end₂)
    (hle₁ : ∀ ω, start ω ≤ end₁ ω)
    (hle₂ : ∀ ω, start ω ≤ end₂ ω) :
    StoppingObservationWindow 𝓕 where
  startTime := start
  endTime := fun ω => min (end₁ ω) (end₂ ω)
  start_stopping := hstart
  end_stopping := h₁.min h₂
  start_le_end := fun ω => le_min (hle₁ ω) (hle₂ ω)

@[simp] theorem ofMinEnd_startTime
    (start end₁ end₂ : Ω → ℝ)
    (hstart : IsStoppingTime 𝓕 start)
    (h₁ : IsStoppingTime 𝓕 end₁)
    (h₂ : IsStoppingTime 𝓕 end₂)
    (hle₁ : ∀ ω, start ω ≤ end₁ ω)
    (hle₂ : ∀ ω, start ω ≤ end₂ ω) :
    (ofMinEnd start end₁ end₂ hstart h₁ h₂ hle₁ hle₂).startTime =
      start := rfl

@[simp] theorem ofMinEnd_endTime
    (start end₁ end₂ : Ω → ℝ)
    (hstart : IsStoppingTime 𝓕 start)
    (h₁ : IsStoppingTime 𝓕 end₁)
    (h₂ : IsStoppingTime 𝓕 end₂)
    (hle₁ : ∀ ω, start ω ≤ end₁ ω)
    (hle₂ : ∀ ω, start ω ≤ end₂ ω) :
    (ofMinEnd start end₁ end₂ hstart h₁ h₂ hle₁ hle₂).endTime =
      fun ω => min (end₁ ω) (end₂ ω) := rfl

/--
Stopping observation window whose end is the earliest of three stopping
endpoint rules.
-/
def ofMinEnd3
    (start end₁ end₂ end₃ : Ω → ℝ)
    (hstart : IsStoppingTime 𝓕 start)
    (h₁ : IsStoppingTime 𝓕 end₁)
    (h₂ : IsStoppingTime 𝓕 end₂)
    (h₃ : IsStoppingTime 𝓕 end₃)
    (hle₁ : ∀ ω, start ω ≤ end₁ ω)
    (hle₂ : ∀ ω, start ω ≤ end₂ ω)
    (hle₃ : ∀ ω, start ω ≤ end₃ ω) :
    StoppingObservationWindow 𝓕 where
  startTime := start
  endTime := fun ω => min (min (end₁ ω) (end₂ ω)) (end₃ ω)
  start_stopping := hstart
  end_stopping := IsStoppingTime.min3 h₁ h₂ h₃
  start_le_end := fun ω => le_min (le_min (hle₁ ω) (hle₂ ω)) (hle₃ ω)

@[simp] theorem ofMinEnd3_startTime
    (start end₁ end₂ end₃ : Ω → ℝ)
    (hstart : IsStoppingTime 𝓕 start)
    (h₁ : IsStoppingTime 𝓕 end₁)
    (h₂ : IsStoppingTime 𝓕 end₂)
    (h₃ : IsStoppingTime 𝓕 end₃)
    (hle₁ : ∀ ω, start ω ≤ end₁ ω)
    (hle₂ : ∀ ω, start ω ≤ end₂ ω)
    (hle₃ : ∀ ω, start ω ≤ end₃ ω) :
    (ofMinEnd3 start end₁ end₂ end₃ hstart h₁ h₂ h₃ hle₁ hle₂ hle₃).startTime =
      start := rfl

@[simp] theorem ofMinEnd3_endTime
    (start end₁ end₂ end₃ : Ω → ℝ)
    (hstart : IsStoppingTime 𝓕 start)
    (h₁ : IsStoppingTime 𝓕 end₁)
    (h₂ : IsStoppingTime 𝓕 end₂)
    (h₃ : IsStoppingTime 𝓕 end₃)
    (hle₁ : ∀ ω, start ω ≤ end₁ ω)
    (hle₂ : ∀ ω, start ω ≤ end₂ ω)
    (hle₃ : ∀ ω, start ω ≤ end₃ ω) :
    (ofMinEnd3 start end₁ end₂ end₃ hstart h₁ h₂ h₃ hle₁ hle₂ hle₃).endTime =
      fun ω => min (min (end₁ ω) (end₂ ω)) (end₃ ω) := rfl

/--
Stopping-window constructor for the common empirical preprocessing rule
`min (start + durationCap) endpoint₁ endpoint₂`, where all three endpoint
rules are stopping times and the cap is nonnegative.
-/
def ofDurationCensoredMinEnd3
    (start endpoint₁ endpoint₂ : Ω → ℝ) (durationCap : ℝ)
    (h_durationCap : 0 ≤ durationCap)
    (hstart : IsStoppingTime 𝓕 start)
    (h_endpoint₁ : IsStoppingTime 𝓕 endpoint₁)
    (h_endpoint₂ : IsStoppingTime 𝓕 endpoint₂)
    (h_start_le_endpoint₁ : ∀ ω, start ω ≤ endpoint₁ ω)
    (h_start_le_endpoint₂ : ∀ ω, start ω ≤ endpoint₂ ω) :
    StoppingObservationWindow 𝓕 :=
  ofMinEnd3 start
    (fun ω => start ω + durationCap) endpoint₁ endpoint₂
    hstart (hstart.add_const_nonneg h_durationCap)
    h_endpoint₁ h_endpoint₂
    (fun ω => by linarith)
    h_start_le_endpoint₁ h_start_le_endpoint₂

@[simp] theorem ofDurationCensoredMinEnd3_endTime
    (start endpoint₁ endpoint₂ : Ω → ℝ) (durationCap : ℝ)
    (h_durationCap : 0 ≤ durationCap)
    (hstart : IsStoppingTime 𝓕 start)
    (h_endpoint₁ : IsStoppingTime 𝓕 endpoint₁)
    (h_endpoint₂ : IsStoppingTime 𝓕 endpoint₂)
    (h_start_le_endpoint₁ : ∀ ω, start ω ≤ endpoint₁ ω)
    (h_start_le_endpoint₂ : ∀ ω, start ω ≤ endpoint₂ ω) :
    (ofDurationCensoredMinEnd3 start endpoint₁ endpoint₂ durationCap
      h_durationCap hstart h_endpoint₁ h_endpoint₂
      h_start_le_endpoint₁ h_start_le_endpoint₂).endTime =
      fun ω => min (min (start ω + durationCap) (endpoint₁ ω)) (endpoint₂ ω) :=
  rfl

end StoppingObservationWindow

/-! ## Local finite-observation stopping certificates -/

/--
Local certificate for the stopping-time part of a finite observation-window
Poisson-process argument.

This deliberately avoids constructing a full path-space Poisson process or its
natural filtration.  It records only the finite/local facts needed by
observation-window likelihood proofs:

* count coordinates are observable at their own times;
* the first report has the same level sets as the count-threshold event
  `{1 ≤ N_t}`;
* the two censoring endpoints are stopping times;
* the endpoints occur after the first report pathwise.

From these fields, Lean derives the first-report stopping time and the
duration-censored stopping observation window.
-/
structure DurationCensoredFirstCountObservationCertificate
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (𝓕 : Filtration (Ω := Ω) ℝ mΩ) where
  count : ℝ → Ω → ℕ
  firstTime : Ω → ℝ
  endpointOne : Ω → ℝ
  endpointTwo : Ω → ℝ
  durationCap : ℝ
  durationCap_nonneg : 0 ≤ durationCap
  count_measurable : ∀ t : ℝ, Measurable[𝓕 t] (count t)
  first_level_sets :
    ∀ t : ℝ, {ω | firstTime ω ≤ t} = {ω | 1 ≤ count t ω}
  endpointOne_stopping : IsStoppingTime 𝓕 endpointOne
  endpointTwo_stopping : IsStoppingTime 𝓕 endpointTwo
  first_le_endpointOne : ∀ ω, firstTime ω ≤ endpointOne ω
  first_le_endpointTwo : ∀ ω, firstTime ω ≤ endpointTwo ω

namespace DurationCensoredFirstCountObservationCertificate

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {𝓕 : Filtration (Ω := Ω) ℝ mΩ}

/--
The first-report component of a local observation certificate as a reusable
first-count-arrival certificate.
-/
def firstCountArrivalCertificate
    (C : DurationCensoredFirstCountObservationCertificate 𝓕) :
    FirstCountArrivalCertificate 𝓕 C.count C.firstTime where
  count_event_adapted :=
    CountThresholdEventAdapted.of_measurable_count C.count_measurable
  level_sets := C.first_level_sets

/-- The certified first-report time is a stopping time. -/
theorem firstTime_stopping
    (C : DurationCensoredFirstCountObservationCertificate 𝓕) :
    IsStoppingTime 𝓕 C.firstTime :=
  C.firstCountArrivalCertificate.isStoppingTime

/-- The duration-censored observation window induced by the local certificate. -/
def stoppingObservationWindow
    (C : DurationCensoredFirstCountObservationCertificate 𝓕) :
    StoppingObservationWindow 𝓕 :=
  StoppingObservationWindow.ofDurationCensoredMinEnd3
    C.firstTime C.endpointOne C.endpointTwo C.durationCap
    C.durationCap_nonneg C.firstTime_stopping
    C.endpointOne_stopping C.endpointTwo_stopping
    C.first_le_endpointOne C.first_le_endpointTwo

@[simp] theorem stoppingObservationWindow_startTime
    (C : DurationCensoredFirstCountObservationCertificate 𝓕) :
    C.stoppingObservationWindow.startTime = C.firstTime := rfl

@[simp] theorem stoppingObservationWindow_endTime
    (C : DurationCensoredFirstCountObservationCertificate 𝓕) :
    C.stoppingObservationWindow.endTime =
      fun ω =>
        min (min (C.firstTime ω + C.durationCap) (C.endpointOne ω))
          (C.endpointTwo ω) := rfl

/--
The induced duration-censored observation window has nonnegative exposure
pathwise.
-/
theorem stoppingObservationWindow_exposure_nonneg
    (C : DurationCensoredFirstCountObservationCertificate 𝓕) (ω : Ω) :
    0 ≤ C.stoppingObservationWindow.exposure ω :=
  C.stoppingObservationWindow.exposure_nonneg ω

/--
The deterministic observation window realized by the local certificate on a
single sample path.
-/
def observationWindow
    (C : DurationCensoredFirstCountObservationCertificate 𝓕) (ω : Ω) :
    ObservationWindow :=
  C.stoppingObservationWindow.toObservationWindow ω

@[simp] theorem observationWindow_startTime
    (C : DurationCensoredFirstCountObservationCertificate 𝓕) (ω : Ω) :
    (C.observationWindow ω).startTime = C.firstTime ω := rfl

@[simp] theorem observationWindow_endTime
    (C : DurationCensoredFirstCountObservationCertificate 𝓕) (ω : Ω) :
    (C.observationWindow ω).endTime =
      min (min (C.firstTime ω + C.durationCap) (C.endpointOne ω))
        (C.endpointTwo ω) := rfl

@[simp] theorem observationWindow_exposure
    (C : DurationCensoredFirstCountObservationCertificate 𝓕) (ω : Ω) :
    (C.observationWindow ω).exposure = C.stoppingObservationWindow.exposure ω :=
  rfl

/--
Constructor from the exact local finite-observation facts needed for the
stopping-window theorem.
-/
def ofStoppingEndpoints
    (count : ℝ → Ω → ℕ) (firstTime endpointOne endpointTwo : Ω → ℝ)
    (durationCap : ℝ)
    (h_durationCap : 0 ≤ durationCap)
    (h_count_measurable : ∀ t : ℝ, Measurable[𝓕 t] (count t))
    (h_first_level_sets :
      ∀ t : ℝ, {ω | firstTime ω ≤ t} = {ω | 1 ≤ count t ω})
    (h_endpointOne_stopping : IsStoppingTime 𝓕 endpointOne)
    (h_endpointTwo_stopping : IsStoppingTime 𝓕 endpointTwo)
    (h_first_le_endpointOne : ∀ ω, firstTime ω ≤ endpointOne ω)
    (h_first_le_endpointTwo : ∀ ω, firstTime ω ≤ endpointTwo ω) :
    DurationCensoredFirstCountObservationCertificate 𝓕 where
  count := count
  firstTime := firstTime
  endpointOne := endpointOne
  endpointTwo := endpointTwo
  durationCap := durationCap
  durationCap_nonneg := h_durationCap
  count_measurable := h_count_measurable
  first_level_sets := h_first_level_sets
  endpointOne_stopping := h_endpointOne_stopping
  endpointTwo_stopping := h_endpointTwo_stopping
  first_le_endpointOne := h_first_le_endpointOne
  first_le_endpointTwo := h_first_le_endpointTwo

/--
Constructor for the common case where the two censoring endpoints are fixed
deterministic times.
-/
def ofDeterministicEndpoints
    (count : ℝ → Ω → ℕ) (firstTime : Ω → ℝ)
    (endpointOne endpointTwo durationCap : ℝ)
    (h_durationCap : 0 ≤ durationCap)
    (h_count_measurable : ∀ t : ℝ, Measurable[𝓕 t] (count t))
    (h_first_level_sets :
      ∀ t : ℝ, {ω | firstTime ω ≤ t} = {ω | 1 ≤ count t ω})
    (h_first_le_endpointOne : ∀ ω, firstTime ω ≤ endpointOne)
    (h_first_le_endpointTwo : ∀ ω, firstTime ω ≤ endpointTwo) :
    DurationCensoredFirstCountObservationCertificate 𝓕 :=
  ofStoppingEndpoints count firstTime (fun _ => endpointOne)
    (fun _ => endpointTwo) durationCap h_durationCap h_count_measurable
    h_first_level_sets (IsStoppingTime.const endpointOne)
    (IsStoppingTime.const endpointTwo)
    h_first_le_endpointOne h_first_le_endpointTwo

@[simp] theorem ofDeterministicEndpoints_endpointOne
    (count : ℝ → Ω → ℕ) (firstTime : Ω → ℝ)
    (endpointOne endpointTwo durationCap : ℝ)
    (h_durationCap : 0 ≤ durationCap)
    (h_count_measurable : ∀ t : ℝ, Measurable[𝓕 t] (count t))
    (h_first_level_sets :
      ∀ t : ℝ, {ω | firstTime ω ≤ t} = {ω | 1 ≤ count t ω})
    (h_first_le_endpointOne : ∀ ω, firstTime ω ≤ endpointOne)
    (h_first_le_endpointTwo : ∀ ω, firstTime ω ≤ endpointTwo) :
    (ofDeterministicEndpoints count firstTime endpointOne endpointTwo
      durationCap h_durationCap h_count_measurable h_first_level_sets
      h_first_le_endpointOne h_first_le_endpointTwo).endpointOne =
      fun _ : Ω => endpointOne := rfl

@[simp] theorem ofDeterministicEndpoints_endpointTwo
    (count : ℝ → Ω → ℕ) (firstTime : Ω → ℝ)
    (endpointOne endpointTwo durationCap : ℝ)
    (h_durationCap : 0 ≤ durationCap)
    (h_count_measurable : ∀ t : ℝ, Measurable[𝓕 t] (count t))
    (h_first_level_sets :
      ∀ t : ℝ, {ω | firstTime ω ≤ t} = {ω | 1 ≤ count t ω})
    (h_first_le_endpointOne : ∀ ω, firstTime ω ≤ endpointOne)
    (h_first_le_endpointTwo : ∀ ω, firstTime ω ≤ endpointTwo) :
    (ofDeterministicEndpoints count firstTime endpointOne endpointTwo
      durationCap h_durationCap h_count_measurable h_first_level_sets
      h_first_le_endpointOne h_first_le_endpointTwo).endpointTwo =
      fun _ : Ω => endpointTwo := rfl

end DurationCensoredFirstCountObservationCertificate

/-! ## Observation-window finite schedules -/

/--
The two-endpoint timeline associated with a deterministic observation window.

Endpoint `0` is the observation start and endpoint `1 = Fin.last 1` is the
observation end.
-/
def observationWindowEndpointTimeline (W : ObservationWindow) : Fin 2 → ℝ :=
  fun j => if j = 0 then W.startTime else W.endTime

@[simp] theorem observationWindowEndpointTimeline_zero
    (W : ObservationWindow) :
    observationWindowEndpointTimeline W 0 = W.startTime := by
  simp [observationWindowEndpointTimeline]

@[simp] theorem observationWindowEndpointTimeline_last
    (W : ObservationWindow) :
    observationWindowEndpointTimeline W (Fin.last 1) = W.endTime := by
  simp [observationWindowEndpointTimeline]

/-- The observation-window two-endpoint timeline is monotone. -/
theorem observationWindowEndpointTimeline_mono
    (W : ObservationWindow) :
    Monotone (observationWindowEndpointTimeline W) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [observationWindowEndpointTimeline] at hij ⊢
  exact W.start_le_end

/--
Construct a reusable one-window finite-schedule Poisson counting process.

The final endpoint-count event probability is derived from the constructed
adjacent Poisson increment law; it is not assumed as a separate field.
-/
theorem exists_finiteSchedulePoissonCountingProcess_observationWindow
    (rate : ℝ) (h_rate : 0 ≤ rate) (W : ObservationWindow) :
    ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ H : FiniteSchedulePoissonCountingProcess Ω P 1 rate
          (observationWindowEndpointTimeline W),
        ∀ k : ℕ,
          P.real {ω : Ω | H.count (Fin.last 1) ω = k} =
            countLikelihood rate W.exposure k := by
  rcases exists_finiteSchedulePoissonCountingProcess rate h_rate
      (observationWindowEndpointTimeline W)
      (observationWindowEndpointTimeline_mono W) with
    ⟨Ω, mΩ, P, H, _⟩
  refine ⟨Ω, mΩ, P, H, ?_⟩
  intro k
  simpa [ObservationWindow.exposure] using H.count_last_prob_one k

/--
Certificate interface for a homogeneous Poisson counting process.

`intervalCount s t ω` is the number of arrivals in `(s,t]` (or any fixed
endpoint convention equivalent for count laws).  The only required field is the
interval-count law.  This keeps sample-path construction and independent-
increment proofs as a reusable library boundary while still allowing
downstream developments to consume a precise checked theorem.
-/
structure HomogeneousCountProcessLaw
    (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) where
  rate : ℝ
  rate_pos : 0 < rate
  intervalCount : ℝ → ℝ → Ω → ℕ
  intervalCount_prob :
    ∀ {s t : ℝ}, s ≤ t → ∀ n : ℕ,
      P.real {ω : Ω | intervalCount s t ω = n} =
        countLikelihood rate (t - s) n

namespace HomogeneousCountProcessLaw

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem rate_nonneg (H : HomogeneousCountProcessLaw Ω P) :
    0 ≤ H.rate :=
  le_of_lt H.rate_pos

theorem intervalCount_prob_eq_countPMF
    (H : HomogeneousCountProcessLaw Ω P)
    {s t : ℝ} (hst : s ≤ t) (n : ℕ) :
    P.real {ω : Ω | H.intervalCount s t ω = n} =
      countPMF
        (rateExposureParam H.rate (t - s)
          (mul_nonneg H.rate_nonneg (sub_nonneg.mpr hst))) n := by
  rw [H.intervalCount_prob hst n]
  rw [countLikelihood_eq_countPMF]

theorem intervalCount_zero_prob
    (H : HomogeneousCountProcessLaw Ω P)
    {s t : ℝ} (hst : s ≤ t) :
    P.real {ω : Ω | H.intervalCount s t ω = 0} =
      noArrivalProb H.rate (t - s) := by
  rw [H.intervalCount_prob hst 0]
  simp [noArrivalProb]

theorem intervalCount_zero_prob_eq_exponential_tail
    (H : HomogeneousCountProcessLaw Ω P)
    {s t : ℝ} (hst : s ≤ t) :
    P.real {ω : Ω | H.intervalCount s t ω = 0} =
      ((Exponential.Model.mk H.rate H.rate_pos).measure
        (Set.Ioi (t - s))).toReal := by
  rw [H.intervalCount_zero_prob hst]
  rw [noArrivalProb_eq_exponential_tail H.rate H.rate_pos
    (sub_nonneg.mpr hst)]

theorem windowCount_prob
    (H : HomogeneousCountProcessLaw Ω P)
    (W : ObservationWindow) (n : ℕ) :
    P.real {ω : Ω | H.intervalCount W.startTime W.endTime ω = n} =
      countLikelihood H.rate W.exposure n := by
  simpa [ObservationWindow.exposure] using
    H.intervalCount_prob W.start_le_end n

theorem windowCount_zero_prob
    (H : HomogeneousCountProcessLaw Ω P)
    (W : ObservationWindow) :
    P.real {ω : Ω | H.intervalCount W.startTime W.endTime ω = 0} =
      noArrivalProb H.rate W.exposure := by
  rw [H.windowCount_prob W 0]
  simp [noArrivalProb]

end HomogeneousCountProcessLaw

/-! ## Homogeneous Poisson Counting Process Semantics -/

/--
Primitive semantics for a homogeneous Poisson counting process.

The process is represented by a count path `count t ω`.  The fields expose the
standard model assumptions: a positive homogeneous rate, zero initial count,
monotone count paths, independent increments in the mathlib process sense, and
stationary Poisson increment marginals.  The reusable
`HomogeneousCountProcessLaw` is then derived from these primitive fields by
taking interval counts as differences of the count path.
-/
structure HomogeneousPoissonCountingProcess
    (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) where
  rate : ℝ
  rate_pos : 0 < rate
  count : ℝ → Ω → ℕ
  count_zero_ae : ∀ᵐ ω ∂P, count 0 ω = 0
  count_mono_ae : ∀ᵐ ω ∂P, Monotone fun t => count t ω
  hasIndepIncrements : ProbabilityTheory.HasIndepIncrements count P
  increment_count_prob :
    ∀ {s t : ℝ}, s ≤ t → ∀ n : ℕ,
      P.real {ω : Ω | count t ω - count s ω = n} =
        countLikelihood rate (t - s) n

namespace HomogeneousPoissonCountingProcess

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Count increment over an interval, derived from the count path. -/
def intervalCount
    (H : HomogeneousPoissonCountingProcess Ω P)
    (s t : ℝ) (ω : Ω) : ℕ :=
  H.count t ω - H.count s ω

theorem rate_nonneg
    (H : HomogeneousPoissonCountingProcess Ω P) :
    0 ≤ H.rate :=
  le_of_lt H.rate_pos

/-- Count paths are almost surely monotone. -/
theorem count_mono
    (H : HomogeneousPoissonCountingProcess Ω P) :
    ∀ᵐ ω ∂P, Monotone fun t => H.count t ω :=
  H.count_mono_ae

/-- Counts are almost surely ordered along ordered times. -/
theorem count_le_ae
    (H : HomogeneousPoissonCountingProcess Ω P)
    {s t : ℝ} (hst : s ≤ t) :
    ∀ᵐ ω ∂P, H.count s ω ≤ H.count t ω := by
  filter_upwards [H.count_mono_ae] with ω hmono
  exact hmono hst

/-- Interval counts add back to endpoint counts almost surely. -/
theorem count_add_intervalCount_eq_ae
    (H : HomogeneousPoissonCountingProcess Ω P)
    {s t : ℝ} (hst : s ≤ t) :
    ∀ᵐ ω ∂P, H.count s ω + H.intervalCount s t ω = H.count t ω := by
  filter_upwards [H.count_le_ae hst] with ω hle
  exact Nat.add_sub_of_le hle

/-- From zero initial count, the interval count from zero is the endpoint count. -/
theorem intervalCount_zero_eq_count_ae
    (H : HomogeneousPoissonCountingProcess Ω P)
    (t : ℝ) :
    ∀ᵐ ω ∂P, H.intervalCount 0 t ω = H.count t ω := by
  filter_upwards [H.count_zero_ae] with ω hzero
  simp [intervalCount, hzero]

/-- Adjacent interval counts add to the combined interval count almost surely. -/
theorem intervalCount_add_adjacent_ae
    (H : HomogeneousPoissonCountingProcess Ω P)
    {r s t : ℝ} (hrs : r ≤ s) (hst : s ≤ t) :
    ∀ᵐ ω ∂P,
      H.intervalCount r s ω + H.intervalCount s t ω =
        H.intervalCount r t ω := by
  filter_upwards [H.count_mono_ae] with ω hmono
  have hrs_count : H.count r ω ≤ H.count s ω := hmono hrs
  have hst_count : H.count s ω ≤ H.count t ω := hmono hst
  simp [intervalCount]
  omega

theorem intervalCount_prob
    (H : HomogeneousPoissonCountingProcess Ω P)
    {s t : ℝ} (hst : s ≤ t) (n : ℕ) :
    P.real {ω : Ω | H.intervalCount s t ω = n} =
      countLikelihood H.rate (t - s) n := by
  simpa [intervalCount] using H.increment_count_prob hst n

/--
Finite families of adjacent interval counts are independent, directly from
mathlib's independent-increment API.
-/
theorem iIndepFun_intervalCount_fin
    (H : HomogeneousPoissonCountingProcess Ω P)
    {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : Monotone t) :
    ProbabilityTheory.iIndepFun
      (fun (i : Fin n) (ω : Ω) =>
        H.intervalCount (t i.castSucc) (t i.succ) ω) P := by
  simpa [intervalCount] using H.hasIndepIncrements n t ht

/--
Count increments along a monotone discrete timeline are independent.
-/
theorem iIndepFun_intervalCount_nat
    (H : HomogeneousPoissonCountingProcess Ω P)
    {t : ℕ → ℝ} (ht : Monotone t) :
    ProbabilityTheory.iIndepFun
      (fun (i : ℕ) (ω : Ω) =>
        H.intervalCount (t i) (t (i + 1)) ω) P := by
  simpa [intervalCount] using H.hasIndepIncrements.nat (t := t) ht

/--
Two adjacent interval counts are independent.
-/
theorem indepFun_intervalCount_adjacent
    (H : HomogeneousPoissonCountingProcess Ω P)
    {r s t : ℝ} (hrs : r ≤ s) (hst : s ≤ t) :
    ProbabilityTheory.IndepFun
      (fun ω : Ω => H.intervalCount r s ω)
      (fun ω : Ω => H.intervalCount s t ω) P := by
  simpa [intervalCount] using
    H.hasIndepIncrements.indepFun_sub_sub hrs hst

/--
Finite-dimensional joint law of adjacent interval-count events, at the
measure level.  The real-valued Poisson marginal formulas are available from
`intervalCount_prob`.
-/
theorem intervalCount_joint_measure_fin
    (H : HomogeneousPoissonCountingProcess Ω P)
    {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : Monotone t)
    (k : Fin n → ℕ) :
    P (⋂ i ∈ (Finset.univ : Finset (Fin n)),
        {ω : Ω | H.intervalCount (t i.castSucc) (t i.succ) ω = k i}) =
      ∏ i : Fin n,
        P {ω : Ω | H.intervalCount (t i.castSucc) (t i.succ) ω = k i} := by
  classical
  have hind := H.iIndepFun_intervalCount_fin ht
  have h :=
    hind.measure_inter_preimage_eq_mul
      (S := (Finset.univ : Finset (Fin n)))
      (sets := fun i : Fin n => ({k i} : Set ℕ))
      (by
        intro i _hi
        exact measurableSet_singleton (k i))
  simpa using h

/--
Finite-dimensional real-valued joint law of adjacent interval-count events.
-/
theorem intervalCount_joint_real_fin
    [IsFiniteMeasure P]
    (H : HomogeneousPoissonCountingProcess Ω P)
    {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : Monotone t)
    (k : Fin n → ℕ) :
    P.real (⋂ i ∈ (Finset.univ : Finset (Fin n)),
        {ω : Ω | H.intervalCount (t i.castSucc) (t i.succ) ω = k i}) =
      ∏ i : Fin n,
        P.real {ω : Ω | H.intervalCount (t i.castSucc) (t i.succ) ω = k i} := by
  rw [Measure.real_def, H.intervalCount_joint_measure_fin ht k]
  simp only [ENNReal.toReal_prod, Measure.real_def]

/--
Finite-dimensional adjacent interval-count laws as a product of Poisson count
likelihoods.
-/
theorem intervalCount_joint_real_eq_countLikelihoodProduct_fin
    [IsFiniteMeasure P]
    (H : HomogeneousPoissonCountingProcess Ω P)
    {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : Monotone t)
    (k : Fin n → ℕ) :
    P.real (⋂ i ∈ (Finset.univ : Finset (Fin n)),
        {ω : Ω | H.intervalCount (t i.castSucc) (t i.succ) ω = k i}) =
      countLikelihoodProduct (Finset.univ : Finset (Fin n)) H.rate
        (fun i => t i.succ - t i.castSucc) k := by
  classical
  rw [H.intervalCount_joint_real_fin ht k, countLikelihoodProduct]
  refine Finset.prod_congr rfl ?_
  intro i _hi
  exact H.intervalCount_prob (ht (Fin.castSucc_le_succ i)) (k i)

/--
The interval-count law induced by primitive homogeneous Poisson counting-process
semantics.
-/
def toHomogeneousCountProcessLaw
    (H : HomogeneousPoissonCountingProcess Ω P) :
    HomogeneousCountProcessLaw Ω P where
  rate := H.rate
  rate_pos := H.rate_pos
  intervalCount := H.intervalCount
  intervalCount_prob := by
    intro s t hst n
    exact H.intervalCount_prob hst n

@[simp] theorem toHomogeneousCountProcessLaw_rate
    (H : HomogeneousPoissonCountingProcess Ω P) :
    H.toHomogeneousCountProcessLaw.rate = H.rate := rfl

@[simp] theorem toHomogeneousCountProcessLaw_intervalCount
    (H : HomogeneousPoissonCountingProcess Ω P) :
    H.toHomogeneousCountProcessLaw.intervalCount = H.intervalCount := rfl

end HomogeneousPoissonCountingProcess

/--
Legacy all-real-time homogeneous Poisson counting-process interface whose
increment marginals are stated as mathlib distribution laws.

Because its natural-valued count is both monotone on all real times and zero
at time zero, the positive-rate version is uninhabited: the interval `[-1, 0]`
must have pathwise zero count, while the increment law requires a nondegenerate
Poisson count.  It is retained for compatibility with older algebraic proof
surfaces only.  New source models must use the forward-time interface in
`ForwardPoisson.lean` (or an explicit stationary/two-sided construction).
-/
structure HomogeneousPoissonCountingProcessByLaw
    (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) where
  rate : ℝ
  rate_pos : 0 < rate
  count : ℝ → Ω → ℕ
  count_zero_ae : ∀ᵐ ω ∂P, count 0 ω = 0
  count_mono_ae : ∀ᵐ ω ∂P, Monotone fun t => count t ω
  hasIndepIncrements : ProbabilityTheory.HasIndepIncrements count P
  increment_hasLaw :
    ∀ {s t : ℝ} (hst : s ≤ t),
      ProbabilityTheory.HasLaw
        (fun ω : Ω => count t ω - count s ω)
        (ProbabilityTheory.poissonMeasure
          (rateExposureParam rate (t - s)
            (mul_nonneg (le_of_lt rate_pos) (sub_nonneg.mpr hst)))) P

namespace HomogeneousPoissonCountingProcessByLaw

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Count increment over an interval, derived from the count path. -/
def intervalCount
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (s t : ℝ) (ω : Ω) : ℕ :=
  H.count t ω - H.count s ω

theorem rate_nonneg
    (H : HomogeneousPoissonCountingProcessByLaw Ω P) :
    0 ≤ H.rate :=
  le_of_lt H.rate_pos

/-- Count paths are almost surely monotone. -/
theorem count_mono
    (H : HomogeneousPoissonCountingProcessByLaw Ω P) :
    ∀ᵐ ω ∂P, Monotone fun t => H.count t ω :=
  H.count_mono_ae

/-- Counts are almost surely ordered along ordered times. -/
theorem count_le_ae
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    {s t : ℝ} (hst : s ≤ t) :
    ∀ᵐ ω ∂P, H.count s ω ≤ H.count t ω := by
  filter_upwards [H.count_mono_ae] with ω hmono
  exact hmono hst

/-- Interval counts add back to endpoint counts almost surely. -/
theorem count_add_intervalCount_eq_ae
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    {s t : ℝ} (hst : s ≤ t) :
    ∀ᵐ ω ∂P, H.count s ω + H.intervalCount s t ω = H.count t ω := by
  filter_upwards [H.count_le_ae hst] with ω hle
  exact Nat.add_sub_of_le hle

/-- From zero initial count, the interval count from zero is the endpoint count. -/
theorem intervalCount_zero_eq_count_ae
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (t : ℝ) :
    ∀ᵐ ω ∂P, H.intervalCount 0 t ω = H.count t ω := by
  filter_upwards [H.count_zero_ae] with ω hzero
  simp [intervalCount, hzero]

/-- Adjacent interval counts add to the combined interval count almost surely. -/
theorem intervalCount_add_adjacent_ae
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    {r s t : ℝ} (hrs : r ≤ s) (hst : s ≤ t) :
    ∀ᵐ ω ∂P,
      H.intervalCount r s ω + H.intervalCount s t ω =
        H.intervalCount r t ω := by
  filter_upwards [H.count_mono_ae] with ω hmono
  have hrs_count : H.count r ω ≤ H.count s ω := hmono hrs
  have hst_count : H.count s ω ≤ H.count t ω := hmono hst
  simp [intervalCount]
  omega

theorem intervalCount_prob
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    {s t : ℝ} (hst : s ≤ t) (n : ℕ) :
    P.real {ω : Ω | H.intervalCount s t ω = n} =
      countLikelihood H.rate (t - s) n := by
  simpa [intervalCount] using
    hasLaw_poissonMeasure_real_singleton_eq_countLikelihood
      (mul_nonneg H.rate_nonneg (sub_nonneg.mpr hst))
      (H.increment_hasLaw hst) n

/-- Interval-count random variable has the mathlib Poisson law. -/
theorem intervalCount_hasLaw
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    {s t : ℝ} (hst : s ≤ t) :
    ProbabilityTheory.HasLaw
      (fun ω : Ω => H.intervalCount s t ω)
      (ProbabilityTheory.poissonMeasure
        (rateExposureParam H.rate (t - s)
          (mul_nonneg H.rate_nonneg (sub_nonneg.mpr hst)))) P := by
  simpa [intervalCount] using H.increment_hasLaw hst

/-- Interval-count event probability in mathlib Poisson-PMF notation. -/
theorem intervalCount_prob_eq_countPMF
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    {s t : ℝ} (hst : s ≤ t) (n : ℕ) :
    P.real {ω : Ω | H.intervalCount s t ω = n} =
      countPMF
        (rateExposureParam H.rate (t - s)
          (mul_nonneg H.rate_nonneg (sub_nonneg.mpr hst))) n := by
  rw [H.intervalCount_prob hst n]
  rw [countLikelihood_eq_countPMF
    (mul_nonneg H.rate_nonneg (sub_nonneg.mpr hst))]

/-- No-arrival interval-count probability. -/
theorem intervalCount_zero_prob
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    {s t : ℝ} (hst : s ≤ t) :
    P.real {ω : Ω | H.intervalCount s t ω = 0} =
      noArrivalProb H.rate (t - s) := by
  rw [H.intervalCount_prob hst 0]
  simp

/-- No-arrival interval-count probability as an exponential waiting-time tail. -/
theorem intervalCount_zero_prob_eq_exponential_tail
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    {s t : ℝ} (hst : s ≤ t) :
    P.real {ω : Ω | H.intervalCount s t ω = 0} =
      ((Exponential.Model.mk H.rate H.rate_pos).measure
        (Set.Ioi (t - s))).toReal := by
  rw [H.intervalCount_zero_prob hst]
  exact noArrivalProb_eq_exponential_tail
    H.rate H.rate_pos (sub_nonneg.mpr hst)

/-- The legacy all-real-time, monotone, zero-start positive-rate interface is
uninhabited.  This rules out treating it as a forward post-arrival process:
on `[-1, 0]`, monotonicity and the zero baseline force a zero increment almost
surely, contradicting the positive-rate Poisson increment law. -/
theorem false
    (H : HomogeneousPoissonCountingProcessByLaw Ω P) : False := by
  have hst : (-1 : ℝ) ≤ 0 := by norm_num
  letI : IsProbabilityMeasure P := (H.increment_hasLaw hst).isProbabilityMeasure
  have hzero : ∀ᵐ ω ∂P, H.intervalCount (-1) 0 ω = 0 := by
    filter_upwards [H.count_mono_ae, H.count_zero_ae] with ω hmono hzero
    have hle : H.count (-1) ω ≤ H.count 0 ω := hmono hst
    have hleft : H.count (-1) ω = 0 := by omega
    simp [intervalCount, hleft, hzero]
  let A : Set Ω := {ω | H.intervalCount (-1) 0 ω = 0}
  have hAuniv : A =ᵐ[P] Set.univ := by
    filter_upwards [hzero] with ω hω
    dsimp only [A]
    apply propext
    change H.intervalCount (-1) 0 ω = 0 ↔ True
    constructor
    · intro _
      trivial
    · intro _
      exact hω
  have hAone : P.real A = 1 := by
    calc
      P.real A = P.real Set.univ := MeasureTheory.measureReal_congr hAuniv
      _ = 1 := by simp [MeasureTheory.Measure.real]
  have hAprob : P.real A = noArrivalProb H.rate (0 - (-1 : ℝ)) := by
    simpa only [A] using H.intervalCount_zero_prob hst
  have htail_lt : noArrivalProb H.rate (0 - (-1 : ℝ)) < 1 := by
    rw [noArrivalProb]
    rw [Real.exp_lt_one_iff]
    nlinarith [H.rate_pos]
  linarith

/-- Window-count event probability for a deterministic observation window. -/
theorem windowCount_prob
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (W : ObservationWindow) (n : ℕ) :
    P.real {ω : Ω | H.intervalCount W.startTime W.endTime ω = n} =
      countLikelihood H.rate W.exposure n := by
  exact H.intervalCount_prob W.start_le_end n

/-- Window-count random variable has the mathlib Poisson law. -/
theorem windowCount_hasLaw
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (W : ObservationWindow) :
    ProbabilityTheory.HasLaw
      (fun ω : Ω => H.intervalCount W.startTime W.endTime ω)
      (ProbabilityTheory.poissonMeasure
        (rateExposureParam H.rate W.exposure
          (mul_nonneg H.rate_nonneg W.exposure_nonneg))) P := by
  simpa [ObservationWindow.exposure] using
    H.intervalCount_hasLaw W.start_le_end

/-- No-arrival probability for a deterministic observation window. -/
theorem windowCount_zero_prob
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (W : ObservationWindow) :
    P.real {ω : Ω | H.intervalCount W.startTime W.endTime ω = 0} =
      noArrivalProb H.rate W.exposure := by
  exact H.intervalCount_zero_prob W.start_le_end

/-- Window no-arrival probability as an exponential waiting-time tail. -/
theorem windowCount_zero_prob_eq_exponential_tail
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (W : ObservationWindow) :
    P.real {ω : Ω | H.intervalCount W.startTime W.endTime ω = 0} =
      ((Exponential.Model.mk H.rate H.rate_pos).measure
        (Set.Ioi W.exposure)).toReal := by
  exact H.intervalCount_zero_prob_eq_exponential_tail W.start_le_end

/--
Formula-facing homogeneous counting process derived from mathlib Poisson
increment laws.
-/
def toHomogeneousPoissonCountingProcess
    (H : HomogeneousPoissonCountingProcessByLaw Ω P) :
    HomogeneousPoissonCountingProcess Ω P where
  rate := H.rate
  rate_pos := H.rate_pos
  count := H.count
  count_zero_ae := H.count_zero_ae
  count_mono_ae := H.count_mono_ae
  hasIndepIncrements := H.hasIndepIncrements
  increment_count_prob := by
    intro s t hst n
    exact H.intervalCount_prob hst n

@[simp] theorem toHomogeneousPoissonCountingProcess_rate
    (H : HomogeneousPoissonCountingProcessByLaw Ω P) :
    H.toHomogeneousPoissonCountingProcess.rate = H.rate := rfl

@[simp] theorem toHomogeneousPoissonCountingProcess_intervalCount
    (H : HomogeneousPoissonCountingProcessByLaw Ω P) :
    H.toHomogeneousPoissonCountingProcess.intervalCount = H.intervalCount := rfl

@[simp] theorem toHomogeneousPoissonCountingProcess_count
    (H : HomogeneousPoissonCountingProcessByLaw Ω P) :
    H.toHomogeneousPoissonCountingProcess.count = H.count := rfl

/--
Count-law interface derived directly from mathlib Poisson increment laws.
-/
def toHomogeneousCountProcessLaw
    (H : HomogeneousPoissonCountingProcessByLaw Ω P) :
    HomogeneousCountProcessLaw Ω P :=
  H.toHomogeneousPoissonCountingProcess.toHomogeneousCountProcessLaw

@[simp] theorem toHomogeneousCountProcessLaw_rate
    (H : HomogeneousPoissonCountingProcessByLaw Ω P) :
    H.toHomogeneousCountProcessLaw.rate = H.rate := rfl

@[simp] theorem toHomogeneousCountProcessLaw_intervalCount
    (H : HomogeneousPoissonCountingProcessByLaw Ω P) :
    H.toHomogeneousCountProcessLaw.intervalCount = H.intervalCount := rfl

/--
Finite families of adjacent interval counts are independent, directly from the
primitive `HasIndepIncrements` field.
-/
theorem iIndepFun_intervalCount_fin
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : Monotone t) :
    ProbabilityTheory.iIndepFun
      (fun (i : Fin n) (ω : Ω) =>
        H.intervalCount (t i.castSucc) (t i.succ) ω) P := by
  simpa using
    H.toHomogeneousPoissonCountingProcess.iIndepFun_intervalCount_fin ht

/--
Count increments along a monotone discrete timeline are independent.
-/
theorem iIndepFun_intervalCount_nat
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    {t : ℕ → ℝ} (ht : Monotone t) :
    ProbabilityTheory.iIndepFun
      (fun (i : ℕ) (ω : Ω) =>
        H.intervalCount (t i) (t (i + 1)) ω) P := by
  simpa using
    H.toHomogeneousPoissonCountingProcess.iIndepFun_intervalCount_nat ht

/-- Two adjacent interval counts are independent. -/
theorem indepFun_intervalCount_adjacent
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    {r s t : ℝ} (hrs : r ≤ s) (hst : s ≤ t) :
    ProbabilityTheory.IndepFun
      (fun ω : Ω => H.intervalCount r s ω)
      (fun ω : Ω => H.intervalCount s t ω) P := by
  simpa using
    H.toHomogeneousPoissonCountingProcess.indepFun_intervalCount_adjacent
      hrs hst

end HomogeneousPoissonCountingProcessByLaw

/-- A function of the Poisson rate that is actually independent of that rate. -/
def RateIndependent (f : ℝ → ℝ) : Prop :=
  ∃ c : ℝ, ∀ rate : ℝ, f rate = c

/--
Reusable likelihood-factorization certificate.

For a fixed observed interval and count, many likelihood proofs need to show that a
full likelihood equals a rate-independent residual factor times the Poisson
count likelihood.  This structure records exactly that claim.
-/
structure PoissonLikelihoodFactorization where
  likelihood : ℝ → ℝ
  residual : ℝ
  exposure : ℝ
  count : ℕ
  factorized :
    ∀ rate : ℝ,
      likelihood rate =
        residual * countLikelihood rate exposure count

namespace PoissonLikelihoodFactorization

theorem residual_factor_rateIndependent
    (F : PoissonLikelihoodFactorization) :
    RateIndependent (fun _rate : ℝ => F.residual) := by
  exact ⟨F.residual, fun _ => rfl⟩

theorem likelihood_eq
    (F : PoissonLikelihoodFactorization) (rate : ℝ) :
    F.likelihood rate =
      F.residual * countLikelihood rate F.exposure F.count :=
  F.factorized rate

theorem likelihood_nonneg
    (F : PoissonLikelihoodFactorization) {rate : ℝ}
    (h_residual : 0 ≤ F.residual)
    (h_mean : 0 ≤ rate * F.exposure) :
    0 ≤ F.likelihood rate := by
  rw [F.likelihood_eq rate]
  exact mul_nonneg h_residual (countLikelihood_nonneg h_mean F.count)

theorem likelihood_eq_commuted
    (F : PoissonLikelihoodFactorization) (rate : ℝ) :
    F.likelihood rate =
      countLikelihood rate F.exposure F.count * F.residual := by
  rw [F.likelihood_eq rate]
  ring

theorem likelihood_zero_count
    (F : PoissonLikelihoodFactorization) (hcount : F.count = 0)
    (rate : ℝ) :
    F.likelihood rate =
      F.residual * noArrivalProb rate F.exposure := by
  rw [F.likelihood_eq rate, hcount]
  simp [noArrivalProb]

end PoissonLikelihoodFactorization

/-! ## Likelihood Algebra Helpers -/

/--
Rewrite a term whose rate dependence is `rate^count * exp (-(rate * exposure))`
as a residual factor times the Poisson count likelihood.

This is useful when a density calculation tracks exact arrival times and then
needs to recover the count-likelihood factor by absorbing
`count! / exposure^count` into the rate-independent residual.
-/
theorem ratePowerExp_factor_countLikelihood
    (residual rate exposure : ℝ) (count : ℕ)
    (h_exposure : exposure ≠ 0) :
    residual * rate ^ count * Real.exp (-(rate * exposure)) =
      (residual * (count.factorial : ℝ) / exposure ^ count) *
        countLikelihood rate exposure count := by
  have hfac : (count.factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero count
  have hpow : exposure ^ count ≠ 0 := pow_ne_zero count h_exposure
  rw [countLikelihood]
  field_simp [hfac, hpow]
  ring

theorem ratePowerExp_factor_countLikelihood_of_pos
    (residual rate exposure : ℝ) (count : ℕ)
    (h_exposure : 0 < exposure) :
    residual * rate ^ count * Real.exp (-(rate * exposure)) =
      (residual * (count.factorial : ℝ) / exposure ^ count) *
        countLikelihood rate exposure count :=
  ratePowerExp_factor_countLikelihood residual rate exposure count h_exposure.ne'

/--
Finite products of Poisson count likelihoods are a rate-independent residual
times a single Poisson count likelihood at total count and total exposure.
-/
theorem countLikelihoodProduct_eq_residual_countLikelihood_total
    {ι : Type*} (s : Finset ι)
    (rate : ℝ) (exposure : ι → ℝ) (count : ι → ℕ)
    (h_totalExposure : totalExposure s exposure ≠ 0) :
    countLikelihoodProduct s rate exposure count =
      (countLikelihoodProductResidual s exposure count *
          ((totalCount s count).factorial : ℝ) /
            (totalExposure s exposure) ^ totalCount s count) *
        countLikelihood rate (totalExposure s exposure) (totalCount s count) := by
  rw [countLikelihoodProduct_eq_residual_rawShape]
  exact ratePowerExp_factor_countLikelihood
    (countLikelihoodProductResidual s exposure count)
    rate (totalExposure s exposure) (totalCount s count) h_totalExposure

/--
Finite products of Poisson count likelihoods collapse to one total-count
likelihood when at least one selected exposure is positive and all selected
exposures are nonnegative.
-/
theorem countLikelihoodProduct_eq_residual_countLikelihood_total_of_exists_pos_exposure
    {ι : Type*} (s : Finset ι)
    (rate : ℝ) (exposure : ι → ℝ) (count : ι → ℕ)
    (h_exposure_nonneg : ∀ i ∈ s, 0 ≤ exposure i)
    (h_exists : ∃ i ∈ s, 0 < exposure i) :
    countLikelihoodProduct s rate exposure count =
      (countLikelihoodProductResidual s exposure count *
          ((totalCount s count).factorial : ℝ) /
            (totalExposure s exposure) ^ totalCount s count) *
        countLikelihood rate (totalExposure s exposure) (totalCount s count) := by
  exact countLikelihoodProduct_eq_residual_countLikelihood_total
    s rate exposure count
    (ne_of_gt
      (totalExposure_pos_of_exists_pos s exposure h_exposure_nonneg h_exists))

/--
Existence of an independent Poisson count family whose finite subfamily event
likelihoods have the collapsed finite-product form: a rate-independent residual
times one Poisson PMF at total exposure and total count.
-/
theorem exists_iIndepFun_poisson_count_joint_residual_real
    {ι : Type u} (rate : ℝ) (h_rate : 0 ≤ rate)
    (exposure : ι → ℝ) (h_exposure : ∀ i, 0 ≤ exposure i)
    (s : Finset ι)
    (h_totalExposure : totalExposure s exposure ≠ 0) :
    ∃ Ω : Type u, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ X : ι → Ω → ℕ,
        (∀ i, Measurable (X i)) ∧
        (∀ i,
          ProbabilityTheory.HasLaw
            (X i)
            (ProbabilityTheory.poissonMeasure
              (rateExposureParam rate (exposure i)
                (mul_nonneg h_rate (h_exposure i)))) P) ∧
        ProbabilityTheory.iIndepFun X P ∧ IsProbabilityMeasure P ∧
        ∀ k : ι → ℕ,
          P.real (⋂ i ∈ s, {ω : Ω | X i ω = k i}) =
            (countLikelihoodProductResidual s exposure k *
                ((totalCount s k).factorial : ℝ) /
                  (totalExposure s exposure) ^ totalCount s k) *
              countLikelihood rate (totalExposure s exposure)
                (totalCount s k) := by
  classical
  rcases exists_iIndepFun_poisson_count_joint_real
      rate h_rate exposure h_exposure s with
    ⟨Ω, mΩ, P, X, hmeas, hLaw, hind, hprob, hJoint⟩
  refine ⟨Ω, mΩ, P, X, hmeas, hLaw, hind, hprob, ?_⟩
  intro k
  rw [hJoint k]
  exact countLikelihoodProduct_eq_residual_countLikelihood_total
    s rate exposure k h_totalExposure

/--
Existence of an independent Poisson count family in collapsed total-count
form, with nonzero total exposure derived from one positive selected exposure.
-/
theorem exists_iIndepFun_poisson_count_joint_residual_real_of_exists_pos_exposure
    {ι : Type u} (rate : ℝ) (h_rate : 0 ≤ rate)
    (exposure : ι → ℝ) (h_exposure : ∀ i, 0 ≤ exposure i)
    (s : Finset ι) (h_exists : ∃ i ∈ s, 0 < exposure i) :
    ∃ Ω : Type u, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ X : ι → Ω → ℕ,
        (∀ i, Measurable (X i)) ∧
        (∀ i,
          ProbabilityTheory.HasLaw
            (X i)
            (ProbabilityTheory.poissonMeasure
              (rateExposureParam rate (exposure i)
                (mul_nonneg h_rate (h_exposure i)))) P) ∧
        ProbabilityTheory.iIndepFun X P ∧ IsProbabilityMeasure P ∧
        ∀ k : ι → ℕ,
          P.real (⋂ i ∈ s, {ω : Ω | X i ω = k i}) =
            (countLikelihoodProductResidual s exposure k *
                ((totalCount s k).factorial : ℝ) /
                  (totalExposure s exposure) ^ totalCount s k) *
              countLikelihood rate (totalExposure s exposure)
                (totalCount s k) := by
  exact
    exists_iIndepFun_poisson_count_joint_residual_real
      rate h_rate exposure h_exposure s
      (ne_of_gt
        (totalExposure_pos_of_exists_pos s exposure
          (fun i _hi => h_exposure i) h_exists))

/--
Reusable finite-dimensional certificate for independent Poisson counts indexed
by an incident family.

The index type may be infinite; finite likelihood statements are obtained by
choosing a `Finset` of observed rows.  This is the proved finite-product
construction needed by incident-level Poisson likelihood arguments, separated
from any continuous-time path-space Poisson-process construction.
-/
structure FinitePoissonCountFamily
    (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω)
    (ι : Type*) (rate : ℝ) (exposure : ι → ℝ) where
  rate_nonneg : 0 ≤ rate
  exposure_nonneg : ∀ i, 0 ≤ exposure i
  count : ι → Ω → ℕ
  count_hasLaw :
    ∀ i,
      ProbabilityTheory.HasLaw
        (count i)
        (ProbabilityTheory.poissonMeasure
          (rateExposureParam rate (exposure i)
            (mul_nonneg rate_nonneg (exposure_nonneg i)))) P
  iIndep_count : ProbabilityTheory.iIndepFun count P
  isProbabilityMeasure : IsProbabilityMeasure P

namespace FinitePoissonCountFamily

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {ι : Type*} {rate : ℝ} {exposure : ι → ℝ}

/-- Single-coordinate event probability for a finite Poisson count family. -/
theorem count_real_eq_countLikelihood
    (H : FinitePoissonCountFamily Ω P ι rate exposure)
    (i : ι) (k : ℕ) :
    P.real {ω : Ω | H.count i ω = k} =
      countLikelihood rate (exposure i) k := by
  exact
    hasLaw_poissonMeasure_real_singleton_eq_countLikelihood
      (mul_nonneg H.rate_nonneg (H.exposure_nonneg i))
      (H.count_hasLaw i) k

/--
Finite-dimensional joint law for a finite subfamily of independent Poisson
incident counts.
-/
theorem joint_real_eq_countLikelihoodProduct
    (H : FinitePoissonCountFamily Ω P ι rate exposure)
    (s : Finset ι) (k : ι → ℕ) :
    P.real (⋂ i ∈ s, {ω : Ω | H.count i ω = k i}) =
      countLikelihoodProduct s rate exposure k := by
  classical
  have hmeasure :
      P (⋂ i ∈ s, {ω : Ω | H.count i ω = k i}) =
        ∏ i ∈ s, P {ω : Ω | H.count i ω = k i} := by
    have h :=
      H.iIndep_count.measure_inter_preimage_eq_mul
        (S := s)
        (sets := fun i : ι => ({k i} : Set ℕ))
        (by
          intro i _hi
          exact measurableSet_singleton (k i))
    simpa using h
  rw [Measure.real_def, hmeasure]
  simp only [ENNReal.toReal_prod, countLikelihoodProduct]
  refine Finset.prod_congr rfl ?_
  intro i _hi
  exact
    hasLaw_poissonMeasure_real_singleton_eq_countLikelihood
      (mul_nonneg H.rate_nonneg (H.exposure_nonneg i))
      (H.count_hasLaw i) (k i)

/--
For a finite independent Poisson count family, the total count has the Poisson
PMF at total exposure.
-/
theorem total_count_real_eq_countLikelihood
    [Fintype ι] [DecidableEq ι]
    (H : FinitePoissonCountFamily Ω P ι rate exposure)
    (n : ℕ) :
    P.real {ω : Ω | (∑ i : ι, H.count i ω) = n} =
      countLikelihood rate
        (totalExposure (Finset.univ : Finset ι) exposure) n := by
  letI : IsProbabilityMeasure P := H.isProbabilityMeasure
  exact
    finite_count_sum_real_eq_countLikelihood_total
      (fun i => (H.count_hasLaw i).aemeasurable)
      (fun k => H.joint_real_eq_countLikelihoodProduct
        (Finset.univ : Finset ι) k) n

/--
For a finite subfamily of an independent Poisson count family, the subfamily
total count has the Poisson PMF at the subfamily's total exposure.
-/
theorem total_count_real_eq_countLikelihood_finset
    [DecidableEq ι]
    (H : FinitePoissonCountFamily Ω P ι rate exposure)
    (s : Finset ι) (n : ℕ) :
    P.real {ω : Ω | (∑ i ∈ s, H.count i ω) = n} =
      countLikelihood rate (totalExposure s exposure) n := by
  classical
  letI : IsProbabilityMeasure P := H.isProbabilityMeasure
  let X : {i // i ∈ s} → Ω → ℕ := fun i => H.count i.1
  let exposureS : {i // i ∈ s} → ℝ := fun i => exposure i.1
  have h :
      P.real {ω : Ω | (∑ i : {i // i ∈ s}, X i ω) = n} =
        countLikelihood rate
          (totalExposure (Finset.univ : Finset {i // i ∈ s}) exposureS) n := by
    refine
      finite_count_sum_real_eq_countLikelihood_total
        (P := P) (X := X)
        (fun i => (H.count_hasLaw i.1).aemeasurable)
        ?_ n
    intro k
    let kExt : ι → ℕ := fun i => if hmem : i ∈ s then k ⟨i, hmem⟩ else 0
    have hset :
        (⋂ i ∈ (Finset.univ : Finset {i // i ∈ s}),
            {ω : Ω | X i ω = k i}) =
          (⋂ i ∈ s, {ω : Ω | H.count i ω = kExt i}) := by
      ext ω
      rw [Set.mem_iInter₂, Set.mem_iInter₂]
      constructor
      · intro hmemAll i hi
        let j : {x // x ∈ s} := ⟨i, hi⟩
        have hsub := hmemAll j (Finset.mem_univ j)
        simpa [X, kExt, hi] using hsub
      · intro hmemAll i _hi
        have hbase := hmemAll i.1 i.2
        simpa [X, kExt, i.2] using hbase
    have hprod :
        countLikelihoodProduct s rate exposure kExt =
          countLikelihoodProduct (Finset.univ : Finset {i // i ∈ s})
            rate exposureS k := by
      rw [countLikelihoodProduct, countLikelihoodProduct]
      rw [← Finset.prod_coe_sort
        (s := s)
        (f := fun i : ι => countLikelihood rate (exposure i) (kExt i))]
      simp [exposureS, kExt]
    rw [hset, H.joint_real_eq_countLikelihoodProduct s kExt, hprod]
  have hset :
      {ω : Ω | (∑ i : {i // i ∈ s}, X i ω) = n} =
        {ω : Ω | (∑ i ∈ s, H.count i ω) = n} := by
    ext ω
    change ((∑ i : {i // i ∈ s}, X i ω) = n) ↔
      ((∑ i ∈ s, H.count i ω) = n)
    have hsum :
        (∑ i : {i // i ∈ s}, X i ω) =
          ∑ i ∈ s, H.count i ω := by
      simpa [X] using
        (Finset.sum_coe_sort
          (s := s) (f := fun i : ι => H.count i ω))
    rw [hsum]
  have hexposure :
      totalExposure (Finset.univ : Finset {i // i ∈ s})
          exposureS =
        totalExposure s exposure := by
    have hsum :
        (∑ i : {i // i ∈ s}, exposure i.1) =
          ∑ i ∈ s, exposure i := by
      simpa using
        (Finset.sum_coe_sort
          (s := s) (f := fun i : ι => exposure i))
    simpa [totalExposure, exposureS] using hsum
  rw [← hset, h, hexposure]

/--
Collapsed total-count form of the finite incident-family joint likelihood.
-/
theorem joint_real_eq_residual_countLikelihood_total
    (H : FinitePoissonCountFamily Ω P ι rate exposure)
    (s : Finset ι) (h_totalExposure : totalExposure s exposure ≠ 0)
    (k : ι → ℕ) :
    P.real (⋂ i ∈ s, {ω : Ω | H.count i ω = k i}) =
      (countLikelihoodProductResidual s exposure k *
          ((totalCount s k).factorial : ℝ) /
            (totalExposure s exposure) ^ totalCount s k) *
        countLikelihood rate (totalExposure s exposure) (totalCount s k) := by
  rw [H.joint_real_eq_countLikelihoodProduct s k]
  exact countLikelihoodProduct_eq_residual_countLikelihood_total
    s rate exposure k h_totalExposure

/--
Collapsed total-count form of the finite incident-family joint likelihood,
deriving the nonzero total exposure from one positive selected exposure.
-/
theorem joint_real_eq_residual_countLikelihood_total_of_exists_pos_exposure
    (H : FinitePoissonCountFamily Ω P ι rate exposure)
    (s : Finset ι) (h_exists : ∃ i ∈ s, 0 < exposure i)
    (k : ι → ℕ) :
    P.real (⋂ i ∈ s, {ω : Ω | H.count i ω = k i}) =
      (countLikelihoodProductResidual s exposure k *
          ((totalCount s k).factorial : ℝ) /
            (totalExposure s exposure) ^ totalCount s k) *
        countLikelihood rate (totalExposure s exposure) (totalCount s k) := by
  rw [H.joint_real_eq_countLikelihoodProduct s k]
  exact countLikelihoodProduct_eq_residual_countLikelihood_total_of_exists_pos_exposure
    s rate exposure k (fun i _hi => H.exposure_nonneg i) h_exists

end FinitePoissonCountFamily

/--
Existence of the reusable finite incident-family Poisson count certificate.
-/
theorem exists_finitePoissonCountFamily
    {ι : Type u} (rate : ℝ) (h_rate : 0 ≤ rate)
    (exposure : ι → ℝ) (h_exposure : ∀ i, 0 ≤ exposure i) :
    ∃ Ω : Type u, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ _H : FinitePoissonCountFamily Ω P ι rate exposure, True := by
  rcases exists_iIndepFun_poisson_increments
      rate h_rate exposure h_exposure with
    ⟨Ω, mΩ, P, X, hmeas, hLaw, hind, hprob⟩
  refine ⟨Ω, mΩ, P, ?_, trivial⟩
  exact
    { rate_nonneg := h_rate
      exposure_nonneg := h_exposure
      count := X
      count_hasLaw := hLaw
      iIndep_count := hind
      isProbabilityMeasure := hprob }

/--
Existence of the finite incident-family certificate together with its product
joint likelihood formula on a chosen finite incident set.
-/
theorem exists_finitePoissonCountFamily_joint_real
    {ι : Type u} (rate : ℝ) (h_rate : 0 ≤ rate)
    (exposure : ι → ℝ) (h_exposure : ∀ i, 0 ≤ exposure i)
    (s : Finset ι) :
    ∃ Ω : Type u, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ H : FinitePoissonCountFamily Ω P ι rate exposure,
        ∀ k : ι → ℕ,
          P.real (⋂ i ∈ s, {ω : Ω | H.count i ω = k i}) =
            countLikelihoodProduct s rate exposure k := by
  rcases exists_finitePoissonCountFamily
      rate h_rate exposure h_exposure with
    ⟨Ω, mΩ, P, H, _⟩
  exact ⟨Ω, mΩ, P, H,
    fun k => H.joint_real_eq_countLikelihoodProduct s k⟩

/--
Existence of the finite incident-family certificate together with its collapsed
total-count joint likelihood formula on a chosen finite incident set.
-/
theorem exists_finitePoissonCountFamily_joint_residual_real
    {ι : Type u} (rate : ℝ) (h_rate : 0 ≤ rate)
    (exposure : ι → ℝ) (h_exposure : ∀ i, 0 ≤ exposure i)
    (s : Finset ι)
    (h_totalExposure : totalExposure s exposure ≠ 0) :
    ∃ Ω : Type u, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ H : FinitePoissonCountFamily Ω P ι rate exposure,
        ∀ k : ι → ℕ,
          P.real (⋂ i ∈ s, {ω : Ω | H.count i ω = k i}) =
            (countLikelihoodProductResidual s exposure k *
                ((totalCount s k).factorial : ℝ) /
                  (totalExposure s exposure) ^ totalCount s k) *
              countLikelihood rate (totalExposure s exposure)
                (totalCount s k) := by
  rcases exists_finitePoissonCountFamily
      rate h_rate exposure h_exposure with
    ⟨Ω, mΩ, P, H, _⟩
  exact ⟨Ω, mΩ, P, H,
    fun k => H.joint_real_eq_residual_countLikelihood_total
      s h_totalExposure k⟩

/--
Existence of the finite incident-family certificate in collapsed total-count
form, with nonzero total exposure derived from one positive selected exposure.
-/
theorem exists_finitePoissonCountFamily_joint_residual_real_of_exists_pos_exposure
    {ι : Type u} (rate : ℝ) (h_rate : 0 ≤ rate)
    (exposure : ι → ℝ) (h_exposure : ∀ i, 0 ≤ exposure i)
    (s : Finset ι) (h_exists : ∃ i ∈ s, 0 < exposure i) :
    ∃ Ω : Type u, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ H : FinitePoissonCountFamily Ω P ι rate exposure,
        ∀ k : ι → ℕ,
          P.real (⋂ i ∈ s, {ω : Ω | H.count i ω = k i}) =
            (countLikelihoodProductResidual s exposure k *
                ((totalCount s k).factorial : ℝ) /
                  (totalExposure s exposure) ^ totalCount s k) *
              countLikelihood rate (totalExposure s exposure)
                (totalCount s k) := by
  exact
    exists_finitePoissonCountFamily_joint_residual_real
      rate h_rate exposure h_exposure s
      (ne_of_gt
        (totalExposure_pos_of_exists_pos s exposure
          (fun i _hi => h_exposure i) h_exists))

/--
Existence of the finite incident-family certificate together with the
collapsed total-count Poisson PMF on a chosen finite index set.
-/
theorem exists_finitePoissonCountFamily_total_count_real
    {ι : Type u} [DecidableEq ι]
    (rate : ℝ) (h_rate : 0 ≤ rate)
    (exposure : ι → ℝ) (h_exposure : ∀ i, 0 ≤ exposure i)
    (s : Finset ι) :
    ∃ Ω : Type u, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ H : FinitePoissonCountFamily Ω P ι rate exposure,
        ∀ n : ℕ,
          P.real {ω : Ω | (∑ i ∈ s, H.count i ω) = n} =
            countLikelihood rate (totalExposure s exposure) n := by
  rcases exists_finitePoissonCountFamily
      rate h_rate exposure h_exposure with
    ⟨Ω, mΩ, P, H, _⟩
  exact ⟨Ω, mΩ, P, H,
    fun n => H.total_count_real_eq_countLikelihood_finset s n⟩

namespace FiniteSchedulePoissonCountingProcess

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {n : ℕ} {rate : ℝ} {t : Fin (n + 1) → ℝ}

/--
Adjacent increments of a finite-schedule Poisson counting process, viewed as a
generic finite independent Poisson count family.
-/
def toFinitePoissonCountFamily
    (H : FiniteSchedulePoissonCountingProcess Ω P n rate t) :
    FinitePoissonCountFamily Ω P (Fin n) rate
      (fun i => t i.succ - t i.castSucc) where
  rate_nonneg := H.rate_nonneg
  exposure_nonneg := fun i =>
    sub_nonneg.mpr (H.timeline_mono (Fin.castSucc_le_succ i))
  count := H.adjacentIncrement
  count_hasLaw := H.adjacentIncrement_hasLaw
  iIndep_count := H.iIndepFun_adjacentIncrement
  isProbabilityMeasure := H.isProbabilityMeasure

@[simp] theorem toFinitePoissonCountFamily_count
    (H : FiniteSchedulePoissonCountingProcess Ω P n rate t) :
    H.toFinitePoissonCountFamily.count = H.adjacentIncrement := rfl

/--
For any finite subset of adjacent increments in a finite schedule, the subset
total has the Poisson PMF at the subset's total exposure.
-/
theorem adjacentIncrement_total_real_eq_countLikelihood_finset
    [DecidableEq (Fin n)]
    (H : FiniteSchedulePoissonCountingProcess Ω P n rate t)
    (s : Finset (Fin n)) (k : ℕ) :
    P.real {ω : Ω | (∑ i ∈ s, H.adjacentIncrement i ω) = k} =
      countLikelihood rate
        (totalExposure s (fun i => t i.succ - t i.castSucc)) k := by
  simpa using
    H.toFinitePoissonCountFamily.total_count_real_eq_countLikelihood_finset
      s k

end FiniteSchedulePoissonCountingProcess

/--
Collapse a finite-schedule adjacent-count joint product law to one total-count
Poisson likelihood with a rate-independent residual.
-/
theorem finiteScheduleAdjacentCount_joint_real_eq_residual_countLikelihood_total
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n : ℕ} (N : Fin (n + 1) → Ω → ℕ)
    (rate : ℝ) (t : Fin (n + 1) → ℝ)
    (hJoint : ∀ k : Fin n → ℕ,
      P.real (⋂ i ∈ (Finset.univ : Finset (Fin n)),
          {ω : Ω | N i.succ ω - N i.castSucc ω = k i}) =
        countLikelihoodProduct (Finset.univ : Finset (Fin n)) rate
          (fun i => t i.succ - t i.castSucc) k)
    (h_totalExposure :
      totalExposure (Finset.univ : Finset (Fin n))
        (fun i => t i.succ - t i.castSucc) ≠ 0)
    (k : Fin n → ℕ) :
    P.real (⋂ i ∈ (Finset.univ : Finset (Fin n)),
        {ω : Ω | N i.succ ω - N i.castSucc ω = k i}) =
      (countLikelihoodProductResidual (Finset.univ : Finset (Fin n))
          (fun i => t i.succ - t i.castSucc) k *
          ((totalCount (Finset.univ : Finset (Fin n)) k).factorial : ℝ) /
            (totalExposure (Finset.univ : Finset (Fin n))
              (fun i => t i.succ - t i.castSucc)) ^
                totalCount (Finset.univ : Finset (Fin n)) k) *
        countLikelihood rate
          (totalExposure (Finset.univ : Finset (Fin n))
            (fun i => t i.succ - t i.castSucc))
          (totalCount (Finset.univ : Finset (Fin n)) k) := by
  rw [hJoint k]
  exact countLikelihoodProduct_eq_residual_countLikelihood_total
    (Finset.univ : Finset (Fin n)) rate
    (fun i => t i.succ - t i.castSucc) k h_totalExposure

/--
Collapse a finite-schedule adjacent-count joint product law to one total-count
Poisson likelihood, deriving the nonzero total exposure from one strictly
positive adjacent schedule interval.
-/
theorem finiteScheduleAdjacentCount_joint_real_eq_residual_countLikelihood_total_of_exists_pos_exposure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n : ℕ} (N : Fin (n + 1) → Ω → ℕ)
    (rate : ℝ) (t : Fin (n + 1) → ℝ) (ht : Monotone t)
    (hJoint : ∀ k : Fin n → ℕ,
      P.real (⋂ i ∈ (Finset.univ : Finset (Fin n)),
          {ω : Ω | N i.succ ω - N i.castSucc ω = k i}) =
        countLikelihoodProduct (Finset.univ : Finset (Fin n)) rate
          (fun i => t i.succ - t i.castSucc) k)
    (h_exists :
      ∃ i ∈ (Finset.univ : Finset (Fin n)),
        0 < t i.succ - t i.castSucc)
    (k : Fin n → ℕ) :
    P.real (⋂ i ∈ (Finset.univ : Finset (Fin n)),
        {ω : Ω | N i.succ ω - N i.castSucc ω = k i}) =
      (countLikelihoodProductResidual (Finset.univ : Finset (Fin n))
          (fun i => t i.succ - t i.castSucc) k *
          ((totalCount (Finset.univ : Finset (Fin n)) k).factorial : ℝ) /
            (totalExposure (Finset.univ : Finset (Fin n))
              (fun i => t i.succ - t i.castSucc)) ^
                totalCount (Finset.univ : Finset (Fin n)) k) *
        countLikelihood rate
          (totalExposure (Finset.univ : Finset (Fin n))
            (fun i => t i.succ - t i.castSucc))
          (totalCount (Finset.univ : Finset (Fin n)) k) := by
  exact
    finiteScheduleAdjacentCount_joint_real_eq_residual_countLikelihood_total
      N rate t hJoint
      (ne_of_gt
        (totalExposure_pos_of_exists_pos
          (Finset.univ : Finset (Fin n))
          (fun i => t i.succ - t i.castSucc)
          (fun i _hi => adjacent_timeline_diff_nonneg ht i)
          h_exists))
      k

/--
Endpoint-exposure form of the finite-schedule adjacent-count joint law
collapse.
-/
theorem finiteScheduleAdjacentCount_joint_real_eq_residual_countLikelihood_endpoint
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n : ℕ} (N : Fin (n + 1) → Ω → ℕ)
    (rate : ℝ) (t : Fin (n + 1) → ℝ)
    (hJoint : ∀ k : Fin n → ℕ,
      P.real (⋂ i ∈ (Finset.univ : Finset (Fin n)),
          {ω : Ω | N i.succ ω - N i.castSucc ω = k i}) =
        countLikelihoodProduct (Finset.univ : Finset (Fin n)) rate
          (fun i => t i.succ - t i.castSucc) k)
    (h_endpoint : t 0 < t (Fin.last n))
    (k : Fin n → ℕ) :
    P.real (⋂ i ∈ (Finset.univ : Finset (Fin n)),
        {ω : Ω | N i.succ ω - N i.castSucc ω = k i}) =
      (countLikelihoodProductResidual (Finset.univ : Finset (Fin n))
          (fun i => t i.succ - t i.castSucc) k *
          ((totalCount (Finset.univ : Finset (Fin n)) k).factorial : ℝ) /
            (t (Fin.last n) - t 0) ^
              totalCount (Finset.univ : Finset (Fin n)) k) *
        countLikelihood rate
          (t (Fin.last n) - t 0)
          (totalCount (Finset.univ : Finset (Fin n)) k) := by
  rw [finiteScheduleAdjacentCount_joint_real_eq_residual_countLikelihood_total
    N rate t hJoint
    (ne_of_gt (totalExposure_fin_adjacent_timeline_pos h_endpoint)) k]
  rw [totalExposure_fin_adjacent_timeline_diffs]

/--
Existence of a finite-schedule cumulative Poisson counting process with the
collapsed endpoint-exposure joint likelihood formula.
-/
theorem exists_finiteSchedulePoissonCountingProcess_endpoint_fin
    (rate : ℝ) (h_rate : 0 ≤ rate)
    {n : ℕ} (t : Fin (n + 1) → ℝ) (ht : Monotone t)
    (h_endpoint : t 0 < t (Fin.last n)) :
    ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ N : Fin (n + 1) → Ω → ℕ,
        (∀ ω, N 0 ω = 0) ∧
        (∀ ω, Monotone fun j : Fin (n + 1) => N j ω) ∧
        (∀ i,
          ProbabilityTheory.HasLaw
            (fun ω => N i.succ ω - N i.castSucc ω)
            (ProbabilityTheory.poissonMeasure
              (rateExposureParam rate (t i.succ - t i.castSucc)
                (mul_nonneg h_rate
                  (sub_nonneg.mpr (ht (Fin.castSucc_le_succ i)))))) P) ∧
        ProbabilityTheory.iIndepFun
          (fun i : Fin n => fun ω => N i.succ ω - N i.castSucc ω) P ∧
        IsProbabilityMeasure P ∧
        ∀ k : Fin n → ℕ,
          P.real (⋂ i ∈ (Finset.univ : Finset (Fin n)),
              {ω : Ω | N i.succ ω - N i.castSucc ω = k i}) =
            (countLikelihoodProductResidual (Finset.univ : Finset (Fin n))
                (fun i => t i.succ - t i.castSucc) k *
                ((totalCount (Finset.univ : Finset (Fin n)) k).factorial : ℝ) /
                  (t (Fin.last n) - t 0) ^
                    totalCount (Finset.univ : Finset (Fin n)) k) *
              countLikelihood rate
                (t (Fin.last n) - t 0)
                (totalCount (Finset.univ : Finset (Fin n)) k) := by
  classical
  rcases exists_finiteSchedulePoissonCountingProcess_fin rate h_rate t ht with
    ⟨Ω, mΩ, P, N, hzero, hmono, hLaw, hind, hprob, hJoint⟩
  refine ⟨Ω, mΩ, P, N, hzero, hmono, hLaw, hind, hprob, ?_⟩
  intro k
  exact
    finiteScheduleAdjacentCount_joint_real_eq_residual_countLikelihood_endpoint
      N rate t hJoint h_endpoint k

/--
Existence of a finite-schedule cumulative Poisson counting process with the
collapsed total-exposure joint likelihood formula, deriving nonzero total
exposure from one strictly positive adjacent schedule interval.
-/
theorem exists_finiteSchedulePoissonCountingProcess_total_fin_of_exists_pos_exposure
    (rate : ℝ) (h_rate : 0 ≤ rate)
    {n : ℕ} (t : Fin (n + 1) → ℝ) (ht : Monotone t)
    (h_exists :
      ∃ i ∈ (Finset.univ : Finset (Fin n)),
        0 < t i.succ - t i.castSucc) :
    ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ N : Fin (n + 1) → Ω → ℕ,
        (∀ ω, N 0 ω = 0) ∧
        (∀ ω, Monotone fun j : Fin (n + 1) => N j ω) ∧
        (∀ i,
          ProbabilityTheory.HasLaw
            (fun ω => N i.succ ω - N i.castSucc ω)
            (ProbabilityTheory.poissonMeasure
              (rateExposureParam rate (t i.succ - t i.castSucc)
                (mul_nonneg h_rate
                  (sub_nonneg.mpr (ht (Fin.castSucc_le_succ i)))))) P) ∧
        ProbabilityTheory.iIndepFun
          (fun i : Fin n => fun ω => N i.succ ω - N i.castSucc ω) P ∧
        IsProbabilityMeasure P ∧
        ∀ k : Fin n → ℕ,
          P.real (⋂ i ∈ (Finset.univ : Finset (Fin n)),
              {ω : Ω | N i.succ ω - N i.castSucc ω = k i}) =
            (countLikelihoodProductResidual (Finset.univ : Finset (Fin n))
                (fun i => t i.succ - t i.castSucc) k *
                ((totalCount (Finset.univ : Finset (Fin n)) k).factorial : ℝ) /
                  (totalExposure (Finset.univ : Finset (Fin n))
                    (fun i => t i.succ - t i.castSucc)) ^
                    totalCount (Finset.univ : Finset (Fin n)) k) *
              countLikelihood rate
                (totalExposure (Finset.univ : Finset (Fin n))
                  (fun i => t i.succ - t i.castSucc))
                (totalCount (Finset.univ : Finset (Fin n)) k) := by
  classical
  rcases exists_finiteSchedulePoissonCountingProcess_fin rate h_rate t ht with
    ⟨Ω, mΩ, P, N, hzero, hmono, hLaw, hind, hprob, hJoint⟩
  refine ⟨Ω, mΩ, P, N, hzero, hmono, hLaw, hind, hprob, ?_⟩
  intro k
  exact
    finiteScheduleAdjacentCount_joint_real_eq_residual_countLikelihood_total_of_exists_pos_exposure
      N rate t ht hJoint h_exists k

namespace FiniteSchedulePoissonCountingProcess

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {n : ℕ} {rate : ℝ} {t : Fin (n + 1) → ℝ}

/--
Endpoint-exposure collapsed joint law for adjacent increments of a
finite-schedule Poisson counting-process certificate.
-/
theorem joint_real_eq_residual_countLikelihood_endpoint
    (H : FiniteSchedulePoissonCountingProcess Ω P n rate t)
    (h_endpoint : t 0 < t (Fin.last n))
    (k : Fin n → ℕ) :
    P.real (⋂ i ∈ (Finset.univ : Finset (Fin n)),
        {ω : Ω | H.adjacentIncrement i ω = k i}) =
      (countLikelihoodProductResidual (Finset.univ : Finset (Fin n))
          (fun i => t i.succ - t i.castSucc) k *
          ((totalCount (Finset.univ : Finset (Fin n)) k).factorial : ℝ) /
            (t (Fin.last n) - t 0) ^
              totalCount (Finset.univ : Finset (Fin n)) k) *
        countLikelihood rate
          (t (Fin.last n) - t 0)
          (totalCount (Finset.univ : Finset (Fin n)) k) := by
  exact
    finiteScheduleAdjacentCount_joint_real_eq_residual_countLikelihood_endpoint
      H.count rate t
      (by
        intro k
        simpa [adjacentIncrement] using H.joint_real_eq_countLikelihoodProduct k)
      h_endpoint k

/--
Total-exposure collapsed joint law for adjacent increments of a finite-schedule
Poisson counting-process certificate, deriving nonzero exposure from one
strictly positive adjacent schedule interval.
-/
theorem joint_real_eq_residual_countLikelihood_total_of_exists_pos_exposure
    (H : FiniteSchedulePoissonCountingProcess Ω P n rate t)
    (h_exists :
      ∃ i ∈ (Finset.univ : Finset (Fin n)),
        0 < t i.succ - t i.castSucc)
    (k : Fin n → ℕ) :
    P.real (⋂ i ∈ (Finset.univ : Finset (Fin n)),
        {ω : Ω | H.adjacentIncrement i ω = k i}) =
      (countLikelihoodProductResidual (Finset.univ : Finset (Fin n))
          (fun i => t i.succ - t i.castSucc) k *
          ((totalCount (Finset.univ : Finset (Fin n)) k).factorial : ℝ) /
            (totalExposure (Finset.univ : Finset (Fin n))
              (fun i => t i.succ - t i.castSucc)) ^
                totalCount (Finset.univ : Finset (Fin n)) k) *
        countLikelihood rate
          (totalExposure (Finset.univ : Finset (Fin n))
            (fun i => t i.succ - t i.castSucc))
          (totalCount (Finset.univ : Finset (Fin n)) k) := by
  exact
    finiteScheduleAdjacentCount_joint_real_eq_residual_countLikelihood_total_of_exists_pos_exposure
      H.count rate t H.timeline_mono
      (by
        intro k
        simpa [adjacentIncrement] using H.joint_real_eq_countLikelihoodProduct k)
      h_exists k

end FiniteSchedulePoissonCountingProcess

/--
Existence of the reusable finite-schedule process certificate with the
collapsed endpoint-exposure joint likelihood formula.
-/
theorem exists_finiteSchedulePoissonCountingProcess_endpoint
    (rate : ℝ) (h_rate : 0 ≤ rate)
    {n : ℕ} (t : Fin (n + 1) → ℝ) (ht : Monotone t)
    (h_endpoint : t 0 < t (Fin.last n)) :
    ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ H : FiniteSchedulePoissonCountingProcess Ω P n rate t,
        ∀ k : Fin n → ℕ,
          P.real (⋂ i ∈ (Finset.univ : Finset (Fin n)),
              {ω : Ω | H.adjacentIncrement i ω = k i}) =
            (countLikelihoodProductResidual (Finset.univ : Finset (Fin n))
                (fun i => t i.succ - t i.castSucc) k *
                ((totalCount (Finset.univ : Finset (Fin n)) k).factorial : ℝ) /
                  (t (Fin.last n) - t 0) ^
                    totalCount (Finset.univ : Finset (Fin n)) k) *
              countLikelihood rate
                (t (Fin.last n) - t 0)
                (totalCount (Finset.univ : Finset (Fin n)) k) := by
  rcases exists_finiteSchedulePoissonCountingProcess
      rate h_rate t ht with
    ⟨Ω, mΩ, P, H, _⟩
  exact ⟨Ω, mΩ, P, H,
    fun k => H.joint_real_eq_residual_countLikelihood_endpoint h_endpoint k⟩

/--
Existence of the reusable finite-schedule process certificate with the
collapsed total-exposure joint likelihood formula, deriving nonzero exposure
from one strictly positive adjacent schedule interval.
-/
theorem exists_finiteSchedulePoissonCountingProcess_total_of_exists_pos_exposure
    (rate : ℝ) (h_rate : 0 ≤ rate)
    {n : ℕ} (t : Fin (n + 1) → ℝ) (ht : Monotone t)
    (h_exists :
      ∃ i ∈ (Finset.univ : Finset (Fin n)),
        0 < t i.succ - t i.castSucc) :
    ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ H : FiniteSchedulePoissonCountingProcess Ω P n rate t,
        ∀ k : Fin n → ℕ,
          P.real (⋂ i ∈ (Finset.univ : Finset (Fin n)),
              {ω : Ω | H.adjacentIncrement i ω = k i}) =
            (countLikelihoodProductResidual (Finset.univ : Finset (Fin n))
                (fun i => t i.succ - t i.castSucc) k *
                ((totalCount (Finset.univ : Finset (Fin n)) k).factorial : ℝ) /
                  (totalExposure (Finset.univ : Finset (Fin n))
                    (fun i => t i.succ - t i.castSucc)) ^
                    totalCount (Finset.univ : Finset (Fin n)) k) *
              countLikelihood rate
                (totalExposure (Finset.univ : Finset (Fin n))
                  (fun i => t i.succ - t i.castSucc))
                (totalCount (Finset.univ : Finset (Fin n)) k) := by
  rcases exists_finiteSchedulePoissonCountingProcess
      rate h_rate t ht with
    ⟨Ω, mΩ, P, H, _⟩
  exact ⟨Ω, mΩ, P, H,
    fun k => H.joint_real_eq_residual_countLikelihood_total_of_exists_pos_exposure
      h_exists k⟩

namespace HomogeneousPoissonCountingProcess

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/--
Finite-dimensional adjacent interval-count laws collapsed to a single total
count likelihood, with the residual independent of the rate.
-/
theorem intervalCount_joint_real_eq_residual_countLikelihood_total_fin
    [IsFiniteMeasure P]
    (H : HomogeneousPoissonCountingProcess Ω P)
    {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : Monotone t)
    (k : Fin n → ℕ)
    (h_totalExposure :
      totalExposure (Finset.univ : Finset (Fin n))
        (fun i => t i.succ - t i.castSucc) ≠ 0) :
    P.real (⋂ i ∈ (Finset.univ : Finset (Fin n)),
        {ω : Ω | H.intervalCount (t i.castSucc) (t i.succ) ω = k i}) =
      (countLikelihoodProductResidual (Finset.univ : Finset (Fin n))
          (fun i => t i.succ - t i.castSucc) k *
          ((totalCount (Finset.univ : Finset (Fin n)) k).factorial : ℝ) /
            (totalExposure (Finset.univ : Finset (Fin n))
              (fun i => t i.succ - t i.castSucc)) ^
                totalCount (Finset.univ : Finset (Fin n)) k) *
        countLikelihood H.rate
          (totalExposure (Finset.univ : Finset (Fin n))
            (fun i => t i.succ - t i.castSucc))
          (totalCount (Finset.univ : Finset (Fin n)) k) := by
  rw [H.intervalCount_joint_real_eq_countLikelihoodProduct_fin ht k]
  exact countLikelihoodProduct_eq_residual_countLikelihood_total
    (Finset.univ : Finset (Fin n)) H.rate
    (fun i => t i.succ - t i.castSucc) k h_totalExposure

/--
Finite-dimensional adjacent interval-count law collapsed to one total-count
likelihood, deriving the nonzero denominator from one strictly positive
adjacent exposure.
-/
theorem intervalCount_joint_real_eq_residual_countLikelihood_total_fin_of_exists_pos_exposure
    [IsFiniteMeasure P]
    (H : HomogeneousPoissonCountingProcess Ω P)
    {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : Monotone t)
    (k : Fin n → ℕ)
    (h_exists :
      ∃ i ∈ (Finset.univ : Finset (Fin n)),
        0 < t i.succ - t i.castSucc) :
    P.real (⋂ i ∈ (Finset.univ : Finset (Fin n)),
        {ω : Ω | H.intervalCount (t i.castSucc) (t i.succ) ω = k i}) =
      (countLikelihoodProductResidual (Finset.univ : Finset (Fin n))
          (fun i => t i.succ - t i.castSucc) k *
          ((totalCount (Finset.univ : Finset (Fin n)) k).factorial : ℝ) /
            (totalExposure (Finset.univ : Finset (Fin n))
              (fun i => t i.succ - t i.castSucc)) ^
                totalCount (Finset.univ : Finset (Fin n)) k) *
        countLikelihood H.rate
          (totalExposure (Finset.univ : Finset (Fin n))
            (fun i => t i.succ - t i.castSucc))
          (totalCount (Finset.univ : Finset (Fin n)) k) := by
  exact H.intervalCount_joint_real_eq_residual_countLikelihood_total_fin
    ht k
    (ne_of_gt
      (totalExposure_pos_of_exists_pos
        (Finset.univ : Finset (Fin n))
        (fun i => t i.succ - t i.castSucc)
        (fun i hi => adjacent_timeline_diff_nonneg ht i)
        h_exists))

/--
Endpoint-exposure form of the finite-dimensional adjacent interval-count law:
the total exposure is `t_last - t_0`.
-/
theorem intervalCount_joint_real_eq_residual_countLikelihood_endpoint_fin
    [IsFiniteMeasure P]
    (H : HomogeneousPoissonCountingProcess Ω P)
    {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : Monotone t)
    (k : Fin n → ℕ)
    (h_endpoint : t 0 < t (Fin.last n)) :
    P.real (⋂ i ∈ (Finset.univ : Finset (Fin n)),
        {ω : Ω | H.intervalCount (t i.castSucc) (t i.succ) ω = k i}) =
      (countLikelihoodProductResidual (Finset.univ : Finset (Fin n))
          (fun i => t i.succ - t i.castSucc) k *
          ((totalCount (Finset.univ : Finset (Fin n)) k).factorial : ℝ) /
            (t (Fin.last n) - t 0) ^
              totalCount (Finset.univ : Finset (Fin n)) k) *
        countLikelihood H.rate
          (t (Fin.last n) - t 0)
          (totalCount (Finset.univ : Finset (Fin n)) k) := by
  have h_totalExposure :
      totalExposure (Finset.univ : Finset (Fin n))
        (fun i => t i.succ - t i.castSucc) ≠ 0 := by
    exact ne_of_gt (totalExposure_fin_adjacent_timeline_pos h_endpoint)
  rw [H.intervalCount_joint_real_eq_residual_countLikelihood_total_fin
    ht k h_totalExposure]
  rw [totalExposure_fin_adjacent_timeline_diffs]

end HomogeneousPoissonCountingProcess

namespace HomogeneousPoissonCountingProcessByLaw

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/--
Finite-dimensional joint law of adjacent interval-count events, at the
measure level, from the primitive mathlib Poisson increment-law interface.
-/
theorem intervalCount_joint_measure_fin
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : Monotone t)
    (k : Fin n → ℕ) :
    P (⋂ i ∈ (Finset.univ : Finset (Fin n)),
        {ω : Ω | H.intervalCount (t i.castSucc) (t i.succ) ω = k i}) =
      ∏ i : Fin n,
        P {ω : Ω | H.intervalCount (t i.castSucc) (t i.succ) ω = k i} := by
  simpa using
    H.toHomogeneousPoissonCountingProcess.intervalCount_joint_measure_fin
      ht k

/--
Finite-dimensional real-valued joint law of adjacent interval-count events,
from the primitive mathlib Poisson increment-law interface.
-/
theorem intervalCount_joint_real_fin
    [IsFiniteMeasure P]
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : Monotone t)
    (k : Fin n → ℕ) :
    P.real (⋂ i ∈ (Finset.univ : Finset (Fin n)),
        {ω : Ω | H.intervalCount (t i.castSucc) (t i.succ) ω = k i}) =
      ∏ i : Fin n,
        P.real {ω : Ω | H.intervalCount (t i.castSucc) (t i.succ) ω = k i} := by
  simpa using
    H.toHomogeneousPoissonCountingProcess.intervalCount_joint_real_fin
      ht k

/--
Finite-dimensional adjacent interval-count laws as a product of Poisson count
likelihoods, from the primitive mathlib Poisson increment-law interface.
-/
theorem intervalCount_joint_real_eq_countLikelihoodProduct_fin
    [IsFiniteMeasure P]
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : Monotone t)
    (k : Fin n → ℕ) :
    P.real (⋂ i ∈ (Finset.univ : Finset (Fin n)),
        {ω : Ω | H.intervalCount (t i.castSucc) (t i.succ) ω = k i}) =
      countLikelihoodProduct (Finset.univ : Finset (Fin n)) H.rate
        (fun i => t i.succ - t i.castSucc) k := by
  simpa using
    (HomogeneousPoissonCountingProcess.intervalCount_joint_real_eq_countLikelihoodProduct_fin
        H.toHomogeneousPoissonCountingProcess ht k)

/--
Finite-dimensional adjacent interval-count laws collapsed to a single total
count likelihood, with the residual independent of the rate, from the
primitive mathlib Poisson increment-law interface.
-/
theorem intervalCount_joint_real_eq_residual_countLikelihood_total_fin
    [IsFiniteMeasure P]
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : Monotone t)
    (k : Fin n → ℕ)
    (h_totalExposure :
      totalExposure (Finset.univ : Finset (Fin n))
        (fun i => t i.succ - t i.castSucc) ≠ 0) :
    P.real (⋂ i ∈ (Finset.univ : Finset (Fin n)),
        {ω : Ω | H.intervalCount (t i.castSucc) (t i.succ) ω = k i}) =
      (countLikelihoodProductResidual (Finset.univ : Finset (Fin n))
          (fun i => t i.succ - t i.castSucc) k *
          ((totalCount (Finset.univ : Finset (Fin n)) k).factorial : ℝ) /
            (totalExposure (Finset.univ : Finset (Fin n))
              (fun i => t i.succ - t i.castSucc)) ^
                totalCount (Finset.univ : Finset (Fin n)) k) *
        countLikelihood H.rate
          (totalExposure (Finset.univ : Finset (Fin n))
            (fun i => t i.succ - t i.castSucc))
          (totalCount (Finset.univ : Finset (Fin n)) k) := by
  simpa using
    (HomogeneousPoissonCountingProcess.intervalCount_joint_real_eq_residual_countLikelihood_total_fin
        H.toHomogeneousPoissonCountingProcess ht k h_totalExposure)

/--
Finite-dimensional adjacent interval-count law collapsed to one total-count
likelihood, deriving the nonzero denominator from one strictly positive
adjacent exposure, from the primitive mathlib Poisson increment-law interface.
-/
theorem intervalCount_joint_real_eq_residual_countLikelihood_total_fin_of_exists_pos_exposure
    [IsFiniteMeasure P]
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : Monotone t)
    (k : Fin n → ℕ)
    (h_exists :
      ∃ i ∈ (Finset.univ : Finset (Fin n)),
        0 < t i.succ - t i.castSucc) :
    P.real (⋂ i ∈ (Finset.univ : Finset (Fin n)),
        {ω : Ω | H.intervalCount (t i.castSucc) (t i.succ) ω = k i}) =
      (countLikelihoodProductResidual (Finset.univ : Finset (Fin n))
          (fun i => t i.succ - t i.castSucc) k *
          ((totalCount (Finset.univ : Finset (Fin n)) k).factorial : ℝ) /
            (totalExposure (Finset.univ : Finset (Fin n))
              (fun i => t i.succ - t i.castSucc)) ^
                totalCount (Finset.univ : Finset (Fin n)) k) *
        countLikelihood H.rate
          (totalExposure (Finset.univ : Finset (Fin n))
            (fun i => t i.succ - t i.castSucc))
          (totalCount (Finset.univ : Finset (Fin n)) k) := by
  simpa using
    (HomogeneousPoissonCountingProcess.intervalCount_joint_real_eq_residual_countLikelihood_total_fin_of_exists_pos_exposure
        H.toHomogeneousPoissonCountingProcess ht k h_exists)

/--
Endpoint-exposure form of the finite-dimensional adjacent interval-count law,
from the primitive mathlib Poisson increment-law interface.
-/
theorem intervalCount_joint_real_eq_residual_countLikelihood_endpoint_fin
    [IsFiniteMeasure P]
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : Monotone t)
    (k : Fin n → ℕ)
    (h_endpoint : t 0 < t (Fin.last n)) :
    P.real (⋂ i ∈ (Finset.univ : Finset (Fin n)),
        {ω : Ω | H.intervalCount (t i.castSucc) (t i.succ) ω = k i}) =
      (countLikelihoodProductResidual (Finset.univ : Finset (Fin n))
          (fun i => t i.succ - t i.castSucc) k *
          ((totalCount (Finset.univ : Finset (Fin n)) k).factorial : ℝ) /
            (t (Fin.last n) - t 0) ^
              totalCount (Finset.univ : Finset (Fin n)) k) *
        countLikelihood H.rate
          (t (Fin.last n) - t 0)
          (totalCount (Finset.univ : Finset (Fin n)) k) := by
  simpa using
    (HomogeneousPoissonCountingProcess.intervalCount_joint_real_eq_residual_countLikelihood_endpoint_fin
        H.toHomogeneousPoissonCountingProcess ht k h_endpoint)

end HomogeneousPoissonCountingProcessByLaw

/--
Rate-independent residual for a finite product of already-factorized Poisson
likelihood certificates, collapsed to one total-count Poisson likelihood.
-/
def poissonLikelihoodFactorizationProductResidual {ι : Type*}
    (s : Finset ι) (F : ι → PoissonLikelihoodFactorization) : ℝ :=
  (∏ i ∈ s, (F i).residual) *
    (countLikelihoodProductResidual s (fun i => (F i).exposure)
        (fun i => (F i).count) *
      ((totalCount s fun i => (F i).count).factorial : ℝ) /
        (totalExposure s fun i => (F i).exposure) ^
          totalCount s (fun i => (F i).count))

/--
Finite products of Poisson likelihood-factorization certificates collapse to a
single total-count Poisson likelihood, with all other factors independent of
the rate.
-/
theorem prod_poissonLikelihoodFactorization_eq_collapsed_countLikelihood
    {ι : Type*} (s : Finset ι) (F : ι → PoissonLikelihoodFactorization)
    (rate : ℝ)
    (h_totalExposure :
      totalExposure s (fun i => (F i).exposure) ≠ 0) :
    (∏ i ∈ s, (F i).likelihood rate) =
      poissonLikelihoodFactorizationProductResidual s F *
        countLikelihood rate
          (totalExposure s fun i => (F i).exposure)
          (totalCount s fun i => (F i).count) := by
  classical
  have hprod :
      (∏ i ∈ s, (F i).likelihood rate) =
        (∏ i ∈ s, (F i).residual) *
          countLikelihoodProduct s rate
            (fun i => (F i).exposure) (fun i => (F i).count) := by
    calc
      (∏ i ∈ s, (F i).likelihood rate)
          = ∏ i ∈ s,
              ((F i).residual *
                countLikelihood rate (F i).exposure (F i).count) := by
              refine Finset.prod_congr rfl ?_
              intro i _hi
              rw [PoissonLikelihoodFactorization.likelihood_eq]
      _ = (∏ i ∈ s, (F i).residual) *
            (∏ i ∈ s,
              countLikelihood rate (F i).exposure (F i).count) := by
              rw [Finset.prod_mul_distrib]
      _ = (∏ i ∈ s, (F i).residual) *
            countLikelihoodProduct s rate
              (fun i => (F i).exposure) (fun i => (F i).count) := by
              rfl
  rw [hprod]
  rw [countLikelihoodProduct_eq_residual_countLikelihood_total
    s rate (fun i => (F i).exposure) (fun i => (F i).count)
    h_totalExposure]
  simp [poissonLikelihoodFactorizationProductResidual]
  ring

/--
Finite products of Poisson likelihood-factorization certificates collapse to
one total-count likelihood when all selected certificate exposures are
nonnegative and at least one selected exposure is positive.
-/
theorem prod_poissonLikelihoodFactorization_eq_collapsed_countLikelihood_of_exists_pos_exposure
    {ι : Type*} (s : Finset ι) (F : ι → PoissonLikelihoodFactorization)
    (rate : ℝ)
    (h_exposure_nonneg : ∀ i ∈ s, 0 ≤ (F i).exposure)
    (h_exists : ∃ i ∈ s, 0 < (F i).exposure) :
    (∏ i ∈ s, (F i).likelihood rate) =
      poissonLikelihoodFactorizationProductResidual s F *
        countLikelihood rate
          (totalExposure s fun i => (F i).exposure)
          (totalCount s fun i => (F i).count) := by
  exact prod_poissonLikelihoodFactorization_eq_collapsed_countLikelihood
    s F rate
    (ne_of_gt
      (totalExposure_pos_of_exists_pos s
        (fun i => (F i).exposure) h_exposure_nonneg h_exists))

/-! ## Poisson Rate MLE Algebra -/

/--
Rate-dependent log-likelihood kernel for Poisson rate estimation, omitting
constants independent of the rate.
-/
def poissonRateLogLikelihoodKernel
    (count : ℕ) (exposure rate : ℝ) : ℝ :=
  (count : ℝ) * Real.log rate - rate * exposure

/--
The Poisson rate log-likelihood kernel is globally maximized at
`count / exposure` over positive rates, for positive count and exposure.
-/
theorem poissonRateLogLikelihoodKernel_le_at_mle
    {count : ℕ} {exposure rate : ℝ}
    (hcount : count ≠ 0) (h_exposure : 0 < exposure)
    (h_rate : 0 < rate) :
    poissonRateLogLikelihoodKernel count exposure rate ≤
      poissonRateLogLikelihoodKernel count exposure
        ((count : ℝ) / exposure) := by
  have hcount_nat_pos : 0 < count := Nat.pos_of_ne_zero hcount
  have hcount_pos : 0 < (count : ℝ) := by
    exact_mod_cast hcount_nat_pos
  let mle : ℝ := (count : ℝ) / exposure
  have hmle_pos : 0 < mle := div_pos hcount_pos h_exposure
  let x : ℝ := rate / mle
  have hx_pos : 0 < x := div_pos h_rate hmle_pos
  have hrate_eq : rate = mle * x := by
    dsimp [x]
    field_simp [hmle_pos.ne']
  have hmle_exposure : mle * exposure = (count : ℝ) := by
    dsimp [mle]
    field_simp [h_exposure.ne']
  have hmle_x_exposure : mle * x * exposure = (count : ℝ) * x := by
    calc
      mle * x * exposure = mle * exposure * x := by ring
      _ = (count : ℝ) * x := by rw [hmle_exposure]
  have hlog_rate : Real.log rate = Real.log mle + Real.log x := by
    rw [hrate_eq]
    exact Real.log_mul hmle_pos.ne' hx_pos.ne'
  have hlog_bound : (count : ℝ) * Real.log x ≤ (count : ℝ) * (x - 1) :=
    mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos hx_pos) hcount_pos.le
  calc
    poissonRateLogLikelihoodKernel count exposure rate
        = ((count : ℝ) * Real.log mle - mle * exposure) +
            ((count : ℝ) * Real.log x - (count : ℝ) * (x - 1)) := by
            rw [poissonRateLogLikelihoodKernel, hlog_rate, hrate_eq,
              hmle_exposure, hmle_x_exposure]
            ring
    _ ≤ ((count : ℝ) * Real.log mle - mle * exposure) + 0 := by
            linarith
    _ = poissonRateLogLikelihoodKernel count exposure mle := by
            rw [poissonRateLogLikelihoodKernel]
            ring
    _ = poissonRateLogLikelihoodKernel count exposure
        ((count : ℝ) / exposure) := by rfl

/--
Certificate for likelihood calculations that first derive the exact
arrival-density shape and only then convert it to a Poisson count likelihood.

The field `raw_factorized` is deliberately weaker than
`PoissonLikelihoodFactorization`: it records the density-like rate dependence
`A * rate^count * exp (-(rate * exposure))`.  The theorem below derives the
Poisson PMF residual from this raw shape.
-/
structure RawPoissonArrivalLikelihood where
  likelihood : ℝ → ℝ
  kernelResidual : ℝ
  exposure : ℝ
  count : ℕ
  exposure_ne_zero : exposure ≠ 0
  raw_factorized :
    ∀ rate : ℝ,
      likelihood rate =
        kernelResidual * rate ^ count * Real.exp (-(rate * exposure))

namespace RawPoissonArrivalLikelihood

/-- Residual after rewriting the raw arrival-density shape as a count PMF. -/
def correctedResidual (R : RawPoissonArrivalLikelihood) : ℝ :=
  R.kernelResidual * (R.count.factorial : ℝ) / R.exposure ^ R.count

theorem likelihood_eq_countLikelihood
    (R : RawPoissonArrivalLikelihood) (rate : ℝ) :
    R.likelihood rate =
      R.correctedResidual * countLikelihood rate R.exposure R.count := by
  rw [R.raw_factorized rate]
  simpa [correctedResidual] using
    ratePowerExp_factor_countLikelihood
      R.kernelResidual rate R.exposure R.count R.exposure_ne_zero

/-- The raw-arrival certificate induces the standard count-likelihood certificate. -/
def toPoissonLikelihoodFactorization
    (R : RawPoissonArrivalLikelihood) :
    PoissonLikelihoodFactorization where
  likelihood := R.likelihood
  residual := R.correctedResidual
  exposure := R.exposure
  count := R.count
  factorized := R.likelihood_eq_countLikelihood

end RawPoissonArrivalLikelihood

/-! ## Interarrival Kernel Certificates -/

/--
No-arrival kernel for a homogeneous Poisson interval.

This is the reusable zero-jump observation object: its likelihood is already
the zero-count Poisson likelihood, with residual one.
-/
structure NoArrivalKernel where
  exposure : ℝ

namespace NoArrivalKernel

def fromWindow (W : ObservationWindow) : NoArrivalKernel where
  exposure := W.exposure

def likelihood (K : NoArrivalKernel) (rate : ℝ) : ℝ :=
  noArrivalProb rate K.exposure

theorem likelihood_eq_countLikelihood_zero
    (K : NoArrivalKernel) (rate : ℝ) :
    K.likelihood rate = countLikelihood rate K.exposure 0 := by
  simp [likelihood, noArrivalProb]

theorem likelihood_nonneg
    (K : NoArrivalKernel) (rate : ℝ) :
    0 ≤ K.likelihood rate :=
  noArrivalProb_nonneg rate K.exposure

def toPoissonLikelihoodFactorization
    (K : NoArrivalKernel) : PoissonLikelihoodFactorization where
  likelihood := K.likelihood
  residual := 1
  exposure := K.exposure
  count := 0
  factorized := by
    intro rate
    simp [likelihood, noArrivalProb]

end NoArrivalKernel

namespace HomogeneousCountProcessLaw

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/--
The no-arrival kernel induced by an observation window agrees with the
zero-count event probability supplied by a homogeneous count-process law.
-/
theorem windowNoArrivalKernel_likelihood_eq_prob
    (H : HomogeneousCountProcessLaw Ω P) (W : ObservationWindow) :
    (NoArrivalKernel.fromWindow W).likelihood H.rate =
      P.real {ω : Ω | H.intervalCount W.startTime W.endTime ω = 0} := by
  rw [H.windowCount_zero_prob W]
  rfl

end HomogeneousCountProcessLaw

/-! ## Ordered One-Jump Windows -/

/--
An observed first jump inside a deterministic observation window.  This stores
the ordering facts needed to turn the first jump and terminal no-arrival tail
into nonnegative durations.
-/
structure OrderedOneJumpWindow where
  window : ObservationWindow
  firstJumpTime : ℝ
  start_le_jump : window.startTime ≤ firstJumpTime
  jump_le_end : firstJumpTime ≤ window.endTime

namespace OrderedOneJumpWindow

def gap (T : OrderedOneJumpWindow) : ℝ :=
  T.firstJumpTime - T.window.startTime

def tail (T : OrderedOneJumpWindow) : ℝ :=
  T.window.endTime - T.firstJumpTime

theorem gap_nonneg (T : OrderedOneJumpWindow) :
    0 ≤ T.gap :=
  sub_nonneg.mpr T.start_le_jump

theorem tail_nonneg (T : OrderedOneJumpWindow) :
    0 ≤ T.tail :=
  sub_nonneg.mpr T.jump_le_end

theorem exposure_eq (T : OrderedOneJumpWindow) :
    T.gap + T.tail = T.window.exposure := by
  change
    T.firstJumpTime - T.window.startTime +
        (T.window.endTime - T.firstJumpTime) =
      T.window.endTime - T.window.startTime
  ring

end OrderedOneJumpWindow

/--
Integrating the one-jump density kernel over a deterministic observation
window recovers the one-count Poisson likelihood.
-/
theorem oneJumpWindowDensityKernel_integral_eq_countLikelihood_one
    (W : ObservationWindow) (rate : ℝ) :
    (∫ x in W.startTime..W.endTime,
        interarrivalDensityKernel rate (x - W.startTime) *
          noArrivalProb rate (W.endTime - x)) =
      countLikelihood rate W.exposure 1 := by
  have hpoint :
      ∀ x : ℝ,
        interarrivalDensityKernel rate (x - W.startTime) *
            noArrivalProb rate (W.endTime - x) =
          rate * Real.exp (-(rate * W.exposure)) := by
    intro x
    rw [interarrivalDensityKernel, noArrivalProb]
    calc
      rate * Real.exp (-(rate * (x - W.startTime))) *
          Real.exp (-(rate * (W.endTime - x))) =
        rate *
          (Real.exp (-(rate * (x - W.startTime))) *
            Real.exp (-(rate * (W.endTime - x)))) := by ring
      _ = rate *
          Real.exp (-(rate * (x - W.startTime)) +
            -(rate * (W.endTime - x))) := by rw [Real.exp_add]
      _ = rate * Real.exp (-(rate * W.exposure)) := by
        rw [show -(rate * (x - W.startTime)) + -(rate * (W.endTime - x)) =
            -(rate * W.exposure) by
              rw [ObservationWindow.exposure]
              ring]
  simp_rw [hpoint]
  rw [intervalIntegral.integral_const]
  rw [countLikelihood_one]
  simp [ObservationWindow.exposure]
  ring

/--
One interarrival-density factor followed by a terminal no-arrival survival.

This captures the paper-neutral rate-dependent kernel
`λ exp(-λ gap) exp(-λ tail)` together with the exposure identity
`gap + tail = exposure`.
-/
structure OneInterarrivalTailKernel where
  gap : ℝ
  tail : ℝ
  exposure : ℝ
  exposure_eq : gap + tail = exposure
  exposure_ne_zero : exposure ≠ 0

namespace OneInterarrivalTailKernel

def fromWindowJump
    (W : ObservationWindow) (firstJumpTime : ℝ)
    (h_exposure : W.exposure ≠ 0) : OneInterarrivalTailKernel where
  gap := firstJumpTime - W.startTime
  tail := W.endTime - firstJumpTime
  exposure := W.exposure
  exposure_eq := by
    change
      firstJumpTime - W.startTime + (W.endTime - firstJumpTime) =
        W.endTime - W.startTime
    ring
  exposure_ne_zero := h_exposure

def fromOrderedWindow
    (T : OrderedOneJumpWindow)
    (h_exposure : T.window.exposure ≠ 0) : OneInterarrivalTailKernel where
  gap := T.gap
  tail := T.tail
  exposure := T.window.exposure
  exposure_eq := T.exposure_eq
  exposure_ne_zero := h_exposure

def likelihood (K : OneInterarrivalTailKernel) (rate : ℝ) : ℝ :=
  interarrivalDensityKernel rate K.gap * noArrivalProb rate K.tail

theorem likelihood_eq_rawShape
    (K : OneInterarrivalTailKernel) (rate : ℝ) :
    K.likelihood rate = rate * Real.exp (-(rate * K.exposure)) := by
  rw [likelihood, interarrivalDensityKernel, noArrivalProb]
  rw [show -(rate * K.exposure) =
      -(rate * K.gap) + -(rate * K.tail) by
        rw [← K.exposure_eq]
        ring,
    Real.exp_add]
  ring

theorem likelihood_nonneg
    (K : OneInterarrivalTailKernel) {rate : ℝ} (h_rate : 0 ≤ rate) :
    0 ≤ K.likelihood rate := by
  exact mul_nonneg
    (interarrivalDensityKernel_nonneg (rate := rate) (gap := K.gap) h_rate)
    (noArrivalProb_nonneg rate K.tail)

/--
Measure-facing form of the one-interarrival-plus-tail kernel: exponential PDF
for the observed gap times exponential survival for the terminal tail.
-/
theorem likelihood_eq_exponential_pdfReal_mul_tail
    (K : OneInterarrivalTailKernel) (rate : ℝ) (h_rate : 0 < rate)
    (h_gap : 0 ≤ K.gap) (h_tail : 0 ≤ K.tail) :
    K.likelihood rate =
      (Exponential.Model.mk rate h_rate).pdfReal K.gap *
        ((Exponential.Model.mk rate h_rate).measure
          (Set.Ioi K.tail)).toReal := by
  rw [likelihood]
  rw [interarrivalDensityKernel_eq_exponential_pdfReal rate h_rate h_gap]
  rw [noArrivalProb_eq_exponential_tail rate h_rate h_tail]

theorem fromOrderedWindow_likelihood_eq_exponential_pdfReal_mul_tail
    (T : OrderedOneJumpWindow) (h_exposure : T.window.exposure ≠ 0)
    (rate : ℝ) (h_rate : 0 < rate) :
    (fromOrderedWindow T h_exposure).likelihood rate =
      (Exponential.Model.mk rate h_rate).pdfReal T.gap *
        ((Exponential.Model.mk rate h_rate).measure
          (Set.Ioi T.tail)).toReal := by
  simpa [fromOrderedWindow] using
    likelihood_eq_exponential_pdfReal_mul_tail
      (fromOrderedWindow T h_exposure) rate h_rate
      T.gap_nonneg T.tail_nonneg

def toRawPoissonArrivalLikelihood
    (K : OneInterarrivalTailKernel) : RawPoissonArrivalLikelihood where
  likelihood := K.likelihood
  kernelResidual := 1
  exposure := K.exposure
  count := 1
  exposure_ne_zero := K.exposure_ne_zero
  raw_factorized := by
    intro rate
    rw [K.likelihood_eq_rawShape rate]
    simp

theorem likelihood_eq_countLikelihood
    (K : OneInterarrivalTailKernel) (rate : ℝ) :
    K.likelihood rate =
      (1 / K.exposure) * countLikelihood rate K.exposure 1 := by
  simpa [toRawPoissonArrivalLikelihood, RawPoissonArrivalLikelihood.correctedResidual]
    using K.toRawPoissonArrivalLikelihood.likelihood_eq_countLikelihood rate

/--
One-arrival density times the one-dimensional ordered-jump volume recovers the
one-count Poisson likelihood.
-/
theorem likelihood_mul_orderedJumpNestedVolume_eq_countLikelihood
    (K : OneInterarrivalTailKernel) (rate : ℝ) :
    K.likelihood rate * orderedJumpNestedVolume 1 K.exposure =
      countLikelihood rate K.exposure 1 := by
  rw [K.likelihood_eq_countLikelihood]
  rw [orderedJumpNestedVolume_eq_orderedJumpSimplexVolume]
  simp [orderedJumpSimplexVolume]
  field_simp [K.exposure_ne_zero]

theorem fromOrderedWindow_likelihood_mul_orderedJumpNestedVolume_eq_countLikelihood
    (T : OrderedOneJumpWindow) (h_exposure : T.window.exposure ≠ 0)
    (rate : ℝ) :
    (fromOrderedWindow T h_exposure).likelihood rate *
        orderedJumpNestedVolume 1 T.window.exposure =
      countLikelihood rate T.window.exposure 1 := by
  simpa [fromOrderedWindow] using
    likelihood_mul_orderedJumpNestedVolume_eq_countLikelihood
      (fromOrderedWindow T h_exposure) rate

end OneInterarrivalTailKernel

/-! ## Ordered Finite Jump Timelines -/

/--
An ordered finite observation timeline inside a deterministic observation
window.  It stores exactly the ordering facts needed to turn observed jump
times into nonnegative interarrival gaps and a nonnegative
terminal no-arrival tail.
-/
structure OrderedFiniteJumpTimeline where
  window : ObservationWindow
  count : ℕ
  jumpTime : ℕ → ℝ
  endpoint_mono : Monotone (jumpTimelineEndpoint window.startTime jumpTime)
  last_le_end :
    jumpTimelineEndpoint window.startTime jumpTime count ≤ window.endTime

namespace OrderedFiniteJumpTimeline

def gap (T : OrderedFiniteJumpTimeline) (j : Fin T.count) : ℝ :=
  interarrivalGapFromJumpTimes T.window.startTime T.jumpTime j.val

def tail (T : OrderedFiniteJumpTimeline) : ℝ :=
  terminalTailFromJumpTimes T.window.startTime T.window.endTime
    T.jumpTime T.count

theorem gap_nonneg (T : OrderedFiniteJumpTimeline) (j : Fin T.count) :
    0 ≤ T.gap j :=
  interarrivalGapFromJumpTimes_fin_nonneg_of_monotone
    T.endpoint_mono j

theorem tail_nonneg (T : OrderedFiniteJumpTimeline) :
    0 ≤ T.tail :=
  terminalTailFromJumpTimes_nonneg T.last_le_end

theorem exposure_eq (T : OrderedFiniteJumpTimeline) :
    (∑ j : Fin T.count, T.gap j) + T.tail = T.window.exposure := by
  simpa [gap, tail, ObservationWindow.exposure] using
    sum_fin_interarrivalGapFromJumpTimes_add_terminalTail
      T.window.startTime T.window.endTime T.jumpTime T.count

theorem exposure_pos_of_ne_zero
    (T : OrderedFiniteJumpTimeline) (h_exposure : T.window.exposure ≠ 0) :
    0 < T.window.exposure :=
  lt_of_le_of_ne T.window.exposure_nonneg (Ne.symm h_exposure)

end OrderedFiniteJumpTimeline

/--
Finite interarrival-density product followed by a terminal no-arrival survival.

This is the reusable observation object for exact jump gaps and then no
further arrivals before the observation window closes.
-/
structure FinInterarrivalTailKernel where
  count : ℕ
  gap : Fin count → ℝ
  tail : ℝ
  exposure : ℝ
  exposure_eq : (∑ j : Fin count, gap j) + tail = exposure
  exposure_ne_zero : exposure ≠ 0

namespace FinInterarrivalTailKernel

def fromOrderedTimeline
    (T : OrderedFiniteJumpTimeline)
    (h_exposure : T.window.exposure ≠ 0) : FinInterarrivalTailKernel where
  count := T.count
  gap := T.gap
  tail := T.tail
  exposure := T.window.exposure
  exposure_eq := T.exposure_eq
  exposure_ne_zero := h_exposure

def fromWindowJumpTimes
    (W : ObservationWindow) (count : ℕ) (jumpTime : ℕ → ℝ)
    (hmono : Monotone (jumpTimelineEndpoint W.startTime jumpTime))
    (hlast : jumpTimelineEndpoint W.startTime jumpTime count ≤ W.endTime)
    (h_exposure : W.exposure ≠ 0) : FinInterarrivalTailKernel :=
  fromOrderedTimeline
    { window := W
      count := count
      jumpTime := jumpTime
      endpoint_mono := hmono
      last_le_end := hlast }
    h_exposure

def likelihood (K : FinInterarrivalTailKernel) (rate : ℝ) : ℝ :=
  interarrivalTailLikelihood (Finset.univ : Finset (Fin K.count))
    rate K.gap K.tail

theorem likelihood_eq_rawShape
    (K : FinInterarrivalTailKernel) (rate : ℝ) :
    K.likelihood rate =
      rate ^ K.count * Real.exp (-(rate * K.exposure)) := by
  have hcard : (Finset.univ : Finset (Fin K.count)).card = K.count := by
    simp
  have hraw :
      interarrivalTailLikelihood (Finset.univ : Finset (Fin K.count))
          rate K.gap K.tail =
        rate ^ (Finset.univ : Finset (Fin K.count)).card *
          Real.exp (-(rate * K.exposure)) := by
    simpa using
      interarrivalTailLikelihood_eq_exposure_rawShape
        (s := (Finset.univ : Finset (Fin K.count)))
        (rate := rate) (exposure := K.exposure) (tail := K.tail)
        K.gap (by simpa using K.exposure_eq)
  simpa [likelihood, hcard] using hraw

theorem likelihood_nonneg
    (K : FinInterarrivalTailKernel) {rate : ℝ} (h_rate : 0 ≤ rate) :
    0 ≤ K.likelihood rate := by
  exact interarrivalTailLikelihood_nonneg
    (Finset.univ : Finset (Fin K.count)) K.gap K.tail h_rate

/--
Measure-facing form of a finite interarrival-tail kernel: product of
exponential PDFs for the observed gaps times exponential survival for the
terminal tail.
-/
theorem likelihood_eq_exponential_pdfReal_prod_mul_tail
    (K : FinInterarrivalTailKernel) (rate : ℝ) (h_rate : 0 < rate)
    (h_gap : ∀ j : Fin K.count, 0 ≤ K.gap j)
    (h_tail : 0 ≤ K.tail) :
    K.likelihood rate =
      (∏ j : Fin K.count,
          (Exponential.Model.mk rate h_rate).pdfReal (K.gap j)) *
        ((Exponential.Model.mk rate h_rate).measure
          (Set.Ioi K.tail)).toReal := by
  simpa [likelihood] using
    interarrivalTailLikelihood_eq_exponential_pdfReal_prod_mul_tail
      (s := (Finset.univ : Finset (Fin K.count)))
      rate h_rate K.gap K.tail
      (by intro j _hj; exact h_gap j) h_tail

theorem fromOrderedTimeline_likelihood_eq_exponential_pdfReal_prod_mul_tail
    (T : OrderedFiniteJumpTimeline)
    (h_exposure : T.window.exposure ≠ 0)
    (rate : ℝ) (h_rate : 0 < rate) :
    (fromOrderedTimeline T h_exposure).likelihood rate =
      (∏ j : Fin T.count,
          (Exponential.Model.mk rate h_rate).pdfReal (T.gap j)) *
        ((Exponential.Model.mk rate h_rate).measure
          (Set.Ioi T.tail)).toReal := by
  simpa [fromOrderedTimeline] using
    likelihood_eq_exponential_pdfReal_prod_mul_tail
      (fromOrderedTimeline T h_exposure) rate h_rate
      (fun j => T.gap_nonneg j) T.tail_nonneg

def toRawPoissonArrivalLikelihood
    (K : FinInterarrivalTailKernel) : RawPoissonArrivalLikelihood where
  likelihood := K.likelihood
  kernelResidual := 1
  exposure := K.exposure
  count := K.count
  exposure_ne_zero := K.exposure_ne_zero
  raw_factorized := by
    intro rate
    simpa using K.likelihood_eq_rawShape rate

theorem likelihood_eq_countLikelihood
    (K : FinInterarrivalTailKernel) (rate : ℝ) :
    K.likelihood rate =
      ((K.count.factorial : ℝ) / K.exposure ^ K.count) *
        countLikelihood rate K.exposure K.count := by
  simpa [toRawPoissonArrivalLikelihood, RawPoissonArrivalLikelihood.correctedResidual]
    using K.toRawPoissonArrivalLikelihood.likelihood_eq_countLikelihood rate

/--
Finite ordered-arrival density times the standard ordered-simplex volume
factor equals the Poisson count likelihood.
-/
theorem likelihood_mul_orderedJumpSimplexVolume_eq_countLikelihood
    (K : FinInterarrivalTailKernel) (rate : ℝ) :
    K.likelihood rate * orderedJumpSimplexVolume K.exposure K.count =
      countLikelihood rate K.exposure K.count := by
  rw [K.likelihood_eq_rawShape]
  rw [orderedJumpSimplexVolume, countLikelihood]
  have hexp_pow_ne : K.exposure ^ K.count ≠ 0 :=
    pow_ne_zero K.count K.exposure_ne_zero
  have hfac_ne : ((K.count.factorial : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero K.count)
  field_simp [hexp_pow_ne, hfac_ne]
  ring

/--
Finite ordered-arrival density times the recursively defined nested ordered
jump-volume integral equals the Poisson count likelihood.
-/
theorem likelihood_mul_orderedJumpNestedVolume_eq_countLikelihood
    (K : FinInterarrivalTailKernel) (rate : ℝ) :
    K.likelihood rate * orderedJumpNestedVolume K.count K.exposure =
      countLikelihood rate K.exposure K.count := by
  rw [orderedJumpNestedVolume_eq_orderedJumpSimplexVolume]
  exact K.likelihood_mul_orderedJumpSimplexVolume_eq_countLikelihood rate

theorem fromOrderedTimeline_likelihood_mul_orderedJumpNestedVolume_eq_countLikelihood
    (T : OrderedFiniteJumpTimeline) (h_exposure : T.window.exposure ≠ 0)
    (rate : ℝ) :
    (fromOrderedTimeline T h_exposure).likelihood rate *
        orderedJumpNestedVolume T.count T.window.exposure =
      countLikelihood rate T.window.exposure T.count := by
  simpa [fromOrderedTimeline] using
    likelihood_mul_orderedJumpNestedVolume_eq_countLikelihood
      (fromOrderedTimeline T h_exposure) rate

end FinInterarrivalTailKernel

/-! ## Generic Arrival Kernel Cases -/

/--
Arrival-kernel cases for homogeneous Poisson observations.

This case split keeps the rate-dependent observation kernels visible while
avoiding application-specific likelihood records: no arrivals, one
interarrival plus a terminal tail, or a finite interarrival product plus a
terminal tail.
-/
inductive ArrivalKernelCase where
  | zero (K : NoArrivalKernel)
  | one (K : OneInterarrivalTailKernel)
  | finite (K : FinInterarrivalTailKernel)

namespace ArrivalKernelCase

/-- Exposure length of a generic arrival-kernel case. -/
def exposure : ArrivalKernelCase → ℝ
  | zero K => K.exposure
  | one K => K.exposure
  | finite K => K.exposure

/-- Number of observed arrivals in a generic arrival-kernel case. -/
def count : ArrivalKernelCase → ℕ
  | zero _ => 0
  | one _ => 1
  | finite K => K.count

/-- Rate-dependent no-arrival/interarrival likelihood for the case. -/
def likelihood : ArrivalKernelCase → ℝ → ℝ
  | zero K, rate => K.likelihood rate
  | one K, rate => K.likelihood rate
  | finite K, rate => K.likelihood rate

/-- Residual needed to rewrite the arrival kernel as a Poisson count PMF. -/
def residual : ArrivalKernelCase → ℝ
  | zero _ => 1
  | one K => 1 / K.exposure
  | finite K => (K.count.factorial : ℝ) / K.exposure ^ K.count

/--
The generic arrival-kernel likelihood factors as an explicit residual times
the Poisson count likelihood for the case's count and exposure.
-/
theorem factorization (C : ArrivalKernelCase) (rate : ℝ) :
    C.likelihood rate =
      C.residual * countLikelihood rate C.exposure C.count := by
  cases C with
  | zero K =>
      change K.likelihood rate = 1 * countLikelihood rate K.exposure 0
      rw [K.likelihood_eq_countLikelihood_zero]
      ring
  | one K =>
      exact K.likelihood_eq_countLikelihood rate
  | finite K =>
      exact K.likelihood_eq_countLikelihood rate

/-- The generic arrival-kernel case as a reusable likelihood certificate. -/
def toPoissonLikelihoodFactorization
    (C : ArrivalKernelCase) : PoissonLikelihoodFactorization where
  likelihood := C.likelihood
  residual := C.residual
  exposure := C.exposure
  count := C.count
  factorized := C.factorization

end ArrivalKernelCase

/-! ## Unified Observed Arrival Cases -/

/--
Observed arrival cases for a homogeneous Poisson observation
window: no arrivals, one ordered arrival, or a finite ordered arrival timeline.

The likelihood stored here is only the rate-dependent arrival/no-arrival
kernel.  Application-specific factors such as start/end densities and condition
functions should multiply this kernel outside the reusable library.
-/
inductive ObservedArrivalCase where
  | zero (W : ObservationWindow)
  | one
      (T : OrderedOneJumpWindow)
      (exposure_ne_zero : T.window.exposure ≠ 0)
  | finite
      (T : OrderedFiniteJumpTimeline)
      (exposure_ne_zero : T.window.exposure ≠ 0)

namespace ObservedArrivalCase

/-- Exposure length of the observed arrival case. -/
def exposure : ObservedArrivalCase → ℝ
  | zero W => W.exposure
  | one T _ => T.window.exposure
  | finite T _ => T.window.exposure

/-- Number of observed arrivals in the case. -/
def count : ObservedArrivalCase → ℕ
  | zero _ => 0
  | one _ _ => 1
  | finite T _ => T.count

/-- Rate-dependent no-arrival/interarrival likelihood for the case. -/
def likelihood (C : ObservedArrivalCase) (rate : ℝ) : ℝ :=
  match C with
  | zero W => (NoArrivalKernel.fromWindow W).likelihood rate
  | one T h_exposure =>
      (OneInterarrivalTailKernel.fromOrderedWindow T h_exposure).likelihood
        rate
  | finite T h_exposure =>
      (FinInterarrivalTailKernel.fromOrderedTimeline T h_exposure).likelihood
        rate

/-- Residual needed to rewrite the arrival kernel as a Poisson count PMF. -/
def residual : ObservedArrivalCase → ℝ
  | zero _ => 1
  | one T _ => 1 / T.window.exposure
  | finite T _ => (T.count.factorial : ℝ) / T.window.exposure ^ T.count

/--
The unified observed-arrival likelihood factors as an explicit residual times
the Poisson count likelihood for the case's count and exposure.
-/
theorem factorization (C : ObservedArrivalCase) (rate : ℝ) :
    C.likelihood rate =
      C.residual * countLikelihood rate C.exposure C.count := by
  cases C with
  | zero W =>
      change (NoArrivalKernel.fromWindow W).likelihood rate =
        1 * countLikelihood rate W.exposure 0
      rw [NoArrivalKernel.likelihood_eq_countLikelihood_zero]
      change countLikelihood rate W.exposure 0 =
        1 * countLikelihood rate W.exposure 0
      ring
  | one T h_exposure =>
      change
        (OneInterarrivalTailKernel.fromOrderedWindow T h_exposure).likelihood
          rate =
          (1 / T.window.exposure) *
            countLikelihood rate T.window.exposure 1
      simpa [OneInterarrivalTailKernel.fromOrderedWindow] using
        OneInterarrivalTailKernel.likelihood_eq_countLikelihood
          (OneInterarrivalTailKernel.fromOrderedWindow T h_exposure) rate
  | finite T h_exposure =>
      change
        (FinInterarrivalTailKernel.fromOrderedTimeline T h_exposure).likelihood
          rate =
          ((T.count.factorial : ℝ) / T.window.exposure ^ T.count) *
            countLikelihood rate T.window.exposure T.count
      simpa [FinInterarrivalTailKernel.fromOrderedTimeline] using
        FinInterarrivalTailKernel.likelihood_eq_countLikelihood
          (FinInterarrivalTailKernel.fromOrderedTimeline T h_exposure) rate

/-- The zero-arrival case induced by a window has nonnegative exposure. -/
theorem zero_exposure_nonneg (W : ObservationWindow) :
    0 ≤ (ObservedArrivalCase.zero W).exposure :=
  W.exposure_nonneg

/-- Every observed-arrival case has nonnegative exposure. -/
theorem exposure_nonneg (C : ObservedArrivalCase) : 0 ≤ C.exposure := by
  cases C with
  | zero W => exact W.exposure_nonneg
  | one T _ => exact T.window.exposure_nonneg
  | finite T _ => exact T.window.exposure_nonneg

/-- Forget the concrete window/timeline wrapper to the generic arrival kernel. -/
def toArrivalKernelCase : ObservedArrivalCase → ArrivalKernelCase
  | zero W => ArrivalKernelCase.zero (NoArrivalKernel.fromWindow W)
  | one T h_exposure =>
      ArrivalKernelCase.one
        (OneInterarrivalTailKernel.fromOrderedWindow T h_exposure)
  | finite T h_exposure =>
      ArrivalKernelCase.finite
        (FinInterarrivalTailKernel.fromOrderedTimeline T h_exposure)

theorem likelihood_eq_toArrivalKernelCase_likelihood
    (C : ObservedArrivalCase) (rate : ℝ) :
    C.likelihood rate = C.toArrivalKernelCase.likelihood rate := by
  cases C <;> rfl

theorem residual_eq_toArrivalKernelCase_residual
    (C : ObservedArrivalCase) :
    C.residual = C.toArrivalKernelCase.residual := by
  cases C <;> rfl

theorem exposure_eq_toArrivalKernelCase_exposure
    (C : ObservedArrivalCase) :
    C.exposure = C.toArrivalKernelCase.exposure := by
  cases C <;> rfl

theorem count_eq_toArrivalKernelCase_count
    (C : ObservedArrivalCase) :
    C.count = C.toArrivalKernelCase.count := by
  cases C <;> rfl

/-- The unified observed-arrival case as a reusable likelihood certificate. -/
def toPoissonLikelihoodFactorization
    (C : ObservedArrivalCase) : PoissonLikelihoodFactorization where
  likelihood := C.likelihood
  residual := C.residual
  exposure := C.exposure
  count := C.count
  factorized := C.factorization

/--
Rate-independent residual for a finite product of observed-arrival cases.

This is the reusable residual after zero/one/finite arrival-window likelihoods
are multiplied and collapsed to one total-count Poisson likelihood.
-/
def productResidual {Incident : Type*}
    (s : Finset Incident) (C : Incident → ObservedArrivalCase) : ℝ :=
  poissonLikelihoodFactorizationProductResidual s
    (fun i => (C i).toPoissonLikelihoodFactorization)

/--
Finite products of observed-arrival likelihoods collapse to a single
total-count Poisson likelihood, with all other factors collected into a
rate-independent residual.
-/
theorem likelihood_product_decomposition
    {Incident : Type*}
    (s : Finset Incident) (C : Incident → ObservedArrivalCase)
    (rate : ℝ)
    (h_totalExposure :
      totalExposure s (fun i => (C i).exposure) ≠ 0) :
    (∏ i ∈ s, (C i).likelihood rate) =
      productResidual s C *
        countLikelihood rate
          (totalExposure s fun i => (C i).exposure)
          (totalCount s fun i => (C i).count) := by
  simpa [productResidual, toPoissonLikelihoodFactorization] using
    prod_poissonLikelihoodFactorization_eq_collapsed_countLikelihood
      s (fun i => (C i).toPoissonLikelihoodFactorization)
      rate h_totalExposure

/--
Finite products of observed-arrival likelihoods collapse to a single
total-count Poisson likelihood when at least one included case has positive
exposure.  This is the paper-facing form; the lower-level algebraic lemma only
needs nonzero total exposure.
-/
theorem likelihood_product_decomposition_of_exists_pos_exposure
    {Incident : Type*}
    (s : Finset Incident) (C : Incident → ObservedArrivalCase)
    (rate : ℝ)
    (h_exists : ∃ i ∈ s, 0 < (C i).exposure) :
    (∏ i ∈ s, (C i).likelihood rate) =
      productResidual s C *
        countLikelihood rate
          (totalExposure s fun i => (C i).exposure)
          (totalCount s fun i => (C i).count) := by
  exact likelihood_product_decomposition s C rate
    (ne_of_gt
      (totalExposure_pos_of_exists_pos s (fun i => (C i).exposure)
        (fun i _hi => ObservedArrivalCase.exposure_nonneg (C i))
        h_exists))

end ObservedArrivalCase

/-! ## Homogeneous Arrival-Density Law -/

/--
Reusable density-law interface for ordered arrivals in a homogeneous Poisson
process.

`HomogeneousCountProcessLaw` records interval-count probabilities.  This
record is the matching density-level consequence needed by models that observe
exact ordered jump times: one first jump and terminal survival, or a finite
ordered jump timeline and terminal survival.  A future first-principles
Poisson-process construction should prove this record; downstream likelihood
arguments should consume this precise interface instead of ad hoc observation
certificates.
-/
structure HomogeneousArrivalDensityLaw where
  rate : ℝ
  rate_pos : 0 < rate
  oneJumpDensity : OrderedOneJumpWindow → ℝ
  finiteJumpDensity : OrderedFiniteJumpTimeline → ℝ
  oneJumpDensity_eq_kernel :
    ∀ T : OrderedOneJumpWindow,
      oneJumpDensity T =
        interarrivalDensityKernel rate T.gap * noArrivalProb rate T.tail
  finiteJumpDensity_eq_kernel :
    ∀ T : OrderedFiniteJumpTimeline,
      finiteJumpDensity T =
        interarrivalTailLikelihood (Finset.univ : Finset (Fin T.count))
          rate T.gap T.tail

namespace HomogeneousArrivalDensityLaw

/--
Canonical ordered-arrival density law generated by exponential interarrival
kernels at a positive homogeneous rate.

This is the paper-neutral constructor for models that have already established
the homogeneous count rate and use the standard exponential interarrival
semantics.  It prevents downstream papers from assuming the one- and
finite-jump density equations as opaque record fields.
-/
def canonical (rate : ℝ) (h_rate : 0 < rate) :
    HomogeneousArrivalDensityLaw where
  rate := rate
  rate_pos := h_rate
  oneJumpDensity := fun T =>
    interarrivalDensityKernel rate T.gap * noArrivalProb rate T.tail
  finiteJumpDensity := fun T =>
    interarrivalTailLikelihood (Finset.univ : Finset (Fin T.count))
      rate T.gap T.tail
  oneJumpDensity_eq_kernel := by
    intro T
    rfl
  finiteJumpDensity_eq_kernel := by
    intro T
    rfl

@[simp] theorem canonical_rate (rate : ℝ) (h_rate : 0 < rate) :
    (canonical rate h_rate).rate = rate := rfl

@[simp] theorem canonical_oneJumpDensity
    (rate : ℝ) (h_rate : 0 < rate) (T : OrderedOneJumpWindow) :
    (canonical rate h_rate).oneJumpDensity T =
      interarrivalDensityKernel rate T.gap * noArrivalProb rate T.tail := rfl

@[simp] theorem canonical_finiteJumpDensity
    (rate : ℝ) (h_rate : 0 < rate) (T : OrderedFiniteJumpTimeline) :
    (canonical rate h_rate).finiteJumpDensity T =
      interarrivalTailLikelihood (Finset.univ : Finset (Fin T.count))
        rate T.gap T.tail := rfl

theorem rate_nonneg (H : HomogeneousArrivalDensityLaw) :
    0 ≤ H.rate :=
  le_of_lt H.rate_pos

/--
The one-jump density law agrees with the reusable one-interarrival-tail kernel.
-/
theorem oneJumpDensity_eq_kernel_likelihood
    (H : HomogeneousArrivalDensityLaw) (T : OrderedOneJumpWindow)
    (h_exposure : T.window.exposure ≠ 0) :
    H.oneJumpDensity T =
      (OneInterarrivalTailKernel.fromOrderedWindow T h_exposure).likelihood
        H.rate := by
  rw [H.oneJumpDensity_eq_kernel T]
  rfl

/--
The finite-jump density law agrees with the reusable finite-interarrival-tail
kernel.
-/
theorem finiteJumpDensity_eq_kernel_likelihood
    (H : HomogeneousArrivalDensityLaw) (T : OrderedFiniteJumpTimeline)
    (h_exposure : T.window.exposure ≠ 0) :
    H.finiteJumpDensity T =
      (FinInterarrivalTailKernel.fromOrderedTimeline T h_exposure).likelihood
        H.rate := by
  rw [H.finiteJumpDensity_eq_kernel T]
  rfl

/--
Measure-facing one-jump form: exponential PDF for the observed gap times the
exponential survival of the terminal tail.
-/
theorem oneJumpDensity_eq_exponential_pdfReal_mul_tail
    (H : HomogeneousArrivalDensityLaw) (T : OrderedOneJumpWindow) :
    H.oneJumpDensity T =
      (Exponential.Model.mk H.rate H.rate_pos).pdfReal T.gap *
        ((Exponential.Model.mk H.rate H.rate_pos).measure
          (Set.Ioi T.tail)).toReal := by
  rw [H.oneJumpDensity_eq_kernel T]
  rw [interarrivalDensityKernel_eq_exponential_pdfReal
    H.rate H.rate_pos T.gap_nonneg]
  rw [noArrivalProb_eq_exponential_tail
    H.rate H.rate_pos T.tail_nonneg]

/--
Measure-facing finite-jump form: product of exponential PDFs for the observed
gaps times exponential survival of the terminal tail.
-/
theorem finiteJumpDensity_eq_exponential_pdfReal_prod_mul_tail
    (H : HomogeneousArrivalDensityLaw) (T : OrderedFiniteJumpTimeline) :
    H.finiteJumpDensity T =
      (∏ j : Fin T.count,
          (Exponential.Model.mk H.rate H.rate_pos).pdfReal (T.gap j)) *
        ((Exponential.Model.mk H.rate H.rate_pos).measure
          (Set.Ioi T.tail)).toReal := by
  rw [H.finiteJumpDensity_eq_kernel T]
  simpa using
    interarrivalTailLikelihood_eq_exponential_pdfReal_prod_mul_tail
      (s := (Finset.univ : Finset (Fin T.count)))
      H.rate H.rate_pos T.gap T.tail
      (by intro j _hj; exact T.gap_nonneg j) T.tail_nonneg

/--
The one-jump density law has the raw Poisson arrival shape
`rate * exp (-(rate * exposure))` on an ordered window.
-/
theorem oneJumpDensity_eq_rawShape
    (H : HomogeneousArrivalDensityLaw) (T : OrderedOneJumpWindow) :
    H.oneJumpDensity T =
      H.rate * Real.exp (-(H.rate * T.window.exposure)) := by
  rw [H.oneJumpDensity_eq_kernel T]
  rw [show -(H.rate * T.window.exposure) =
      -(H.rate * T.gap) + -(H.rate * T.tail) by
        rw [← T.exposure_eq]
        ring,
    Real.exp_add]
  simp [interarrivalDensityKernel, noArrivalProb]
  ring

/--
The finite-jump density law has the raw Poisson arrival shape
`rate^count * exp (-(rate * exposure))` on an ordered timeline.
-/
theorem finiteJumpDensity_eq_rawShape
    (H : HomogeneousArrivalDensityLaw) (T : OrderedFiniteJumpTimeline) :
    H.finiteJumpDensity T =
      H.rate ^ T.count * Real.exp (-(H.rate * T.window.exposure)) := by
  rw [H.finiteJumpDensity_eq_kernel T]
  simpa using
    interarrivalTailLikelihood_eq_exposure_rawShape
      (s := (Finset.univ : Finset (Fin T.count)))
      (rate := H.rate) (exposure := T.window.exposure) (tail := T.tail)
      T.gap (by simpa using T.exposure_eq)

/--
The one-jump density law, normalized by the recursive one-dimensional
ordered-jump volume, agrees with the one-count Poisson likelihood.
-/
theorem oneJumpDensity_mul_orderedJumpNestedVolume_eq_countLikelihood
    (H : HomogeneousArrivalDensityLaw) (T : OrderedOneJumpWindow)
    (h_exposure : T.window.exposure ≠ 0) :
    H.oneJumpDensity T * orderedJumpNestedVolume 1 T.window.exposure =
      countLikelihood H.rate T.window.exposure 1 := by
  rw [H.oneJumpDensity_eq_kernel_likelihood T h_exposure]
  exact
    OneInterarrivalTailKernel.fromOrderedWindow_likelihood_mul_orderedJumpNestedVolume_eq_countLikelihood
      T h_exposure H.rate

/--
The one-jump density law, normalized by the Lebesgue volume of the
one-dimensional ordered jump-time region, agrees with the one-count Poisson
likelihood.
-/
theorem oneJumpDensity_mul_orderedJumpRegionVolume_eq_countLikelihood
    (H : HomogeneousArrivalDensityLaw) (T : OrderedOneJumpWindow)
    (h_exposure : T.window.exposure ≠ 0) :
    H.oneJumpDensity T *
        (volume (orderedJumpRegion 1 T.window.exposure)).toReal =
      countLikelihood H.rate T.window.exposure 1 := by
  rw [orderedJumpRegion_one_volume_toReal T.window.exposure_nonneg]
  exact H.oneJumpDensity_mul_orderedJumpNestedVolume_eq_countLikelihood
    T h_exposure

/--
The one-jump ordered density is the one-count Poisson likelihood divided by
the one-dimensional ordered-region volume.
-/
theorem oneJumpDensity_eq_countLikelihood_div_orderedJumpRegionVolume
    (H : HomogeneousArrivalDensityLaw) (T : OrderedOneJumpWindow)
    (h_exposure_pos : 0 < T.window.exposure) :
    H.oneJumpDensity T =
      countLikelihood H.rate T.window.exposure 1 /
        (volume (orderedJumpRegion 1 T.window.exposure)).toReal := by
  have hvol :
      (volume (orderedJumpRegion 1 T.window.exposure)).toReal ≠ 0 :=
    ne_of_gt (orderedJumpRegion_volume_toReal_pos h_exposure_pos)
  have h :=
    H.oneJumpDensity_mul_orderedJumpRegionVolume_eq_countLikelihood
      T h_exposure_pos.ne'
  exact (eq_div_iff hvol).2 h

/--
The finite ordered-jump density law, normalized by the recursive ordered-jump
volume, agrees with the count Poisson likelihood.
-/
theorem finiteJumpDensity_mul_orderedJumpNestedVolume_eq_countLikelihood
    (H : HomogeneousArrivalDensityLaw) (T : OrderedFiniteJumpTimeline)
    (h_exposure : T.window.exposure ≠ 0) :
    H.finiteJumpDensity T *
        orderedJumpNestedVolume T.count T.window.exposure =
      countLikelihood H.rate T.window.exposure T.count := by
  rw [H.finiteJumpDensity_eq_kernel_likelihood T h_exposure]
  exact
    FinInterarrivalTailKernel.fromOrderedTimeline_likelihood_mul_orderedJumpNestedVolume_eq_countLikelihood
      T h_exposure H.rate

/--
The finite ordered-jump density law, normalized by the actual Lebesgue volume
of the ordered jump-time region, agrees with the count Poisson likelihood.
-/
theorem finiteJumpDensity_mul_orderedJumpRegionVolume_eq_countLikelihood
    (H : HomogeneousArrivalDensityLaw) (T : OrderedFiniteJumpTimeline)
    (h_exposure : T.window.exposure ≠ 0) :
    H.finiteJumpDensity T *
        (volume (orderedJumpRegion T.count T.window.exposure)).toReal =
      countLikelihood H.rate T.window.exposure T.count := by
  rw [orderedJumpRegion_volume_toReal T.window.exposure_nonneg]
  exact H.finiteJumpDensity_mul_orderedJumpNestedVolume_eq_countLikelihood
    T h_exposure

/--
The finite ordered-jump density is the count Poisson likelihood divided by the
finite ordered-region volume.
-/
theorem finiteJumpDensity_eq_countLikelihood_div_orderedJumpRegionVolume
    (H : HomogeneousArrivalDensityLaw) (T : OrderedFiniteJumpTimeline)
    (h_exposure_pos : 0 < T.window.exposure) :
    H.finiteJumpDensity T =
      countLikelihood H.rate T.window.exposure T.count /
        (volume (orderedJumpRegion T.count T.window.exposure)).toReal := by
  have hvol :
      (volume (orderedJumpRegion T.count T.window.exposure)).toReal ≠ 0 :=
    ne_of_gt (orderedJumpRegion_volume_toReal_pos h_exposure_pos)
  have h :=
    H.finiteJumpDensity_mul_orderedJumpRegionVolume_eq_countLikelihood
      T h_exposure_pos.ne'
  exact (eq_div_iff hvol).2 h

end HomogeneousArrivalDensityLaw

/-! ## Combined Homogeneous Poisson Process Law -/

/--
Combined reusable process-law interface for homogeneous Poisson processes.

The count law supplies interval-count probabilities, while the arrival-density
law supplies ordered jump-time densities.  The shared-rate equality prevents
paper proofs from silently combining unrelated count and density certificates.
-/
structure HomogeneousPoissonProcessLaw
    (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) where
  countLaw : HomogeneousCountProcessLaw Ω P
  arrivalLaw : HomogeneousArrivalDensityLaw
  arrival_rate_eq_count_rate : arrivalLaw.rate = countLaw.rate

namespace HomogeneousPoissonProcessLaw

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/--
Build the combined homogeneous process-law interface from a homogeneous count
law by using the canonical exponential interarrival-density law at the same
rate.
-/
def withCanonicalArrivalDensity
    (H : HomogeneousCountProcessLaw Ω P) :
    HomogeneousPoissonProcessLaw Ω P where
  countLaw := H
  arrivalLaw :=
    HomogeneousArrivalDensityLaw.canonical H.rate H.rate_pos
  arrival_rate_eq_count_rate := rfl

@[simp] theorem withCanonicalArrivalDensity_countLaw
    (H : HomogeneousCountProcessLaw Ω P) :
    (withCanonicalArrivalDensity H).countLaw = H := rfl

def rate (H : HomogeneousPoissonProcessLaw Ω P) : ℝ :=
  H.countLaw.rate

@[simp] theorem withCanonicalArrivalDensity_rate
    (H : HomogeneousCountProcessLaw Ω P) :
    (withCanonicalArrivalDensity H).rate = H.rate := rfl

theorem rate_pos (H : HomogeneousPoissonProcessLaw Ω P) :
    0 < H.rate :=
  H.countLaw.rate_pos

theorem arrival_rate_eq_rate (H : HomogeneousPoissonProcessLaw Ω P) :
    H.arrivalLaw.rate = H.rate :=
  H.arrival_rate_eq_count_rate

/--
The combined process law's zero-count window probability is the exponential
waiting-time tail at the shared process rate.
-/
theorem windowCount_zero_prob_eq_exponential_tail
    (H : HomogeneousPoissonProcessLaw Ω P) (W : ObservationWindow) :
    P.real {ω : Ω |
        H.countLaw.intervalCount W.startTime W.endTime ω = 0} =
      ((Exponential.Model.mk H.rate H.rate_pos).measure
        (Set.Ioi W.exposure)).toReal := by
  rw [H.countLaw.windowCount_zero_prob W]
  exact noArrivalProb_eq_exponential_tail H.rate H.rate_pos W.exposure_nonneg

/-- The combined process law's one-jump density has the shared-rate raw shape. -/
theorem oneJumpDensity_eq_rawShape
    (H : HomogeneousPoissonProcessLaw Ω P) (T : OrderedOneJumpWindow) :
    H.arrivalLaw.oneJumpDensity T =
      H.rate * Real.exp (-(H.rate * T.window.exposure)) := by
  rw [← H.arrival_rate_eq_rate]
  exact H.arrivalLaw.oneJumpDensity_eq_rawShape T

/--
The combined process law's one-jump density is the exponential PDF at the
observed gap times the terminal exponential survival at the shared process
rate.
-/
theorem oneJumpDensity_eq_exponential_pdfReal_mul_tail
    (H : HomogeneousPoissonProcessLaw Ω P) (T : OrderedOneJumpWindow) :
    H.arrivalLaw.oneJumpDensity T =
      (Exponential.Model.mk H.rate H.rate_pos).pdfReal T.gap *
        ((Exponential.Model.mk H.rate H.rate_pos).measure
          (Set.Ioi T.tail)).toReal := by
  simpa [HomogeneousPoissonProcessLaw.rate, H.arrival_rate_eq_count_rate] using
    H.arrivalLaw.oneJumpDensity_eq_exponential_pdfReal_mul_tail T

/-- The combined process law's finite-jump density has the shared-rate raw shape. -/
theorem finiteJumpDensity_eq_rawShape
    (H : HomogeneousPoissonProcessLaw Ω P) (T : OrderedFiniteJumpTimeline) :
    H.arrivalLaw.finiteJumpDensity T =
      H.rate ^ T.count * Real.exp (-(H.rate * T.window.exposure)) := by
  rw [← H.arrival_rate_eq_rate]
  exact H.arrivalLaw.finiteJumpDensity_eq_rawShape T

/--
The combined process law's finite-jump density is the product of exponential
PDFs at the observed gaps times terminal exponential survival at the shared
process rate.
-/
theorem finiteJumpDensity_eq_exponential_pdfReal_prod_mul_tail
    (H : HomogeneousPoissonProcessLaw Ω P) (T : OrderedFiniteJumpTimeline) :
    H.arrivalLaw.finiteJumpDensity T =
      (∏ j : Fin T.count,
          (Exponential.Model.mk H.rate H.rate_pos).pdfReal (T.gap j)) *
        ((Exponential.Model.mk H.rate H.rate_pos).measure
          (Set.Ioi T.tail)).toReal := by
  simpa [HomogeneousPoissonProcessLaw.rate, H.arrival_rate_eq_count_rate] using
    H.arrivalLaw.finiteJumpDensity_eq_exponential_pdfReal_prod_mul_tail T

/--
Process-law likelihood of a concrete observed-arrival case: zero cases use the
count law's zero-count probability, while one/finite cases use the ordered
arrival-density law.
-/
def observedArrivalCaseLikelihood
    (H : HomogeneousPoissonProcessLaw Ω P) : ObservedArrivalCase → ℝ
  | ObservedArrivalCase.zero W =>
      P.real {ω : Ω |
        H.countLaw.intervalCount W.startTime W.endTime ω = 0}
  | ObservedArrivalCase.one T _ => H.arrivalLaw.oneJumpDensity T
  | ObservedArrivalCase.finite T _ => H.arrivalLaw.finiteJumpDensity T

/--
The process-law likelihood of an observed-arrival case agrees with the generic
no-arrival/interarrival kernel at the shared process rate.
-/
theorem observedArrivalCaseLikelihood_eq_kernel_likelihood
    (H : HomogeneousPoissonProcessLaw Ω P)
    (C : ObservedArrivalCase) :
    H.observedArrivalCaseLikelihood C = C.likelihood H.rate := by
  cases C with
  | zero W =>
      change
        P.real {ω : Ω |
          H.countLaw.intervalCount W.startTime W.endTime ω = 0} =
          (NoArrivalKernel.fromWindow W).likelihood H.rate
      rw [← H.countLaw.windowNoArrivalKernel_likelihood_eq_prob W]
      rfl
  | one T h_exposure =>
      change H.arrivalLaw.oneJumpDensity T =
        (OneInterarrivalTailKernel.fromOrderedWindow T h_exposure).likelihood
          H.rate
      simpa [HomogeneousPoissonProcessLaw.rate,
        H.arrival_rate_eq_count_rate] using
          H.arrivalLaw.oneJumpDensity_eq_kernel_likelihood T h_exposure
  | finite T h_exposure =>
      change H.arrivalLaw.finiteJumpDensity T =
        (FinInterarrivalTailKernel.fromOrderedTimeline T h_exposure).likelihood
          H.rate
      simpa [HomogeneousPoissonProcessLaw.rate,
        H.arrival_rate_eq_count_rate] using
          H.arrivalLaw.finiteJumpDensity_eq_kernel_likelihood T h_exposure

/--
The process-law likelihood of an observed-arrival case factors through the
Poisson count likelihood at the case's exposure and observed count.
-/
theorem observedArrivalCaseLikelihood_factorization
    (H : HomogeneousPoissonProcessLaw Ω P)
    (C : ObservedArrivalCase) :
    H.observedArrivalCaseLikelihood C =
      C.residual * countLikelihood H.rate C.exposure C.count := by
  rw [H.observedArrivalCaseLikelihood_eq_kernel_likelihood C]
  exact C.factorization H.rate

/--
Finite products of process-law observed-arrival likelihoods collapse to a
single total-count Poisson likelihood, with all non-Poisson factors collected
into a rate-independent residual.
-/
theorem observedArrivalCaseLikelihood_product_decomposition
    {Incident : Type*}
    (H : HomogeneousPoissonProcessLaw Ω P)
    (s : Finset Incident) (C : Incident → ObservedArrivalCase)
    (h_totalExposure :
      totalExposure s (fun i => (C i).exposure) ≠ 0) :
    (∏ i ∈ s, H.observedArrivalCaseLikelihood (C i)) =
      ObservedArrivalCase.productResidual s C *
        countLikelihood H.rate
          (totalExposure s fun i => (C i).exposure)
          (totalCount s fun i => (C i).count) := by
  classical
  calc
    (∏ i ∈ s, H.observedArrivalCaseLikelihood (C i))
        = ∏ i ∈ s, (C i).likelihood H.rate := by
            refine Finset.prod_congr rfl ?_
            intro i _hi
            exact H.observedArrivalCaseLikelihood_eq_kernel_likelihood (C i)
    _ = ObservedArrivalCase.productResidual s C *
          countLikelihood H.rate
            (totalExposure s fun i => (C i).exposure)
            (totalCount s fun i => (C i).count) := by
        exact ObservedArrivalCase.likelihood_product_decomposition
          s C H.rate h_totalExposure

/--
Finite products of process-law observed-arrival likelihoods collapse to a
single total-count Poisson likelihood when at least one observed case has
positive exposure.
-/
theorem observedArrivalCaseLikelihood_product_decomposition_of_exists_pos_exposure
    {Incident : Type*}
    (H : HomogeneousPoissonProcessLaw Ω P)
    (s : Finset Incident) (C : Incident → ObservedArrivalCase)
    (h_exists : ∃ i ∈ s, 0 < (C i).exposure) :
    (∏ i ∈ s, H.observedArrivalCaseLikelihood (C i)) =
      ObservedArrivalCase.productResidual s C *
        countLikelihood H.rate
          (totalExposure s fun i => (C i).exposure)
          (totalCount s fun i => (C i).count) := by
  exact H.observedArrivalCaseLikelihood_product_decomposition s C
    (ne_of_gt
      (totalExposure_pos_of_exists_pos s (fun i => (C i).exposure)
        (fun i _hi => ObservedArrivalCase.exposure_nonneg (C i))
        h_exists))

/--
The combined process law's one-jump density, normalized by the recursive
one-dimensional ordered-jump volume, equals the one-count window probability.
-/
theorem oneJumpDensity_mul_orderedJumpNestedVolume_eq_windowCount_prob
    (H : HomogeneousPoissonProcessLaw Ω P) (T : OrderedOneJumpWindow)
    (h_exposure : T.window.exposure ≠ 0) :
    H.arrivalLaw.oneJumpDensity T *
        orderedJumpNestedVolume 1 T.window.exposure =
      P.real {ω : Ω |
        H.countLaw.intervalCount T.window.startTime T.window.endTime ω = 1} := by
  calc
    H.arrivalLaw.oneJumpDensity T *
        orderedJumpNestedVolume 1 T.window.exposure =
      countLikelihood H.rate T.window.exposure 1 := by
        simpa [HomogeneousPoissonProcessLaw.rate,
          H.arrival_rate_eq_count_rate] using
            H.arrivalLaw.oneJumpDensity_mul_orderedJumpNestedVolume_eq_countLikelihood
              T h_exposure
    _ = P.real {ω : Ω |
        H.countLaw.intervalCount T.window.startTime T.window.endTime ω = 1} := by
        exact (H.countLaw.windowCount_prob T.window 1).symm

/--
The combined process law's one-jump density, normalized by the Lebesgue volume
of the one-dimensional ordered jump-time region, equals the one-count window
probability.
-/
theorem oneJumpDensity_mul_orderedJumpRegionVolume_eq_windowCount_prob
    (H : HomogeneousPoissonProcessLaw Ω P) (T : OrderedOneJumpWindow)
    (h_exposure : T.window.exposure ≠ 0) :
    H.arrivalLaw.oneJumpDensity T *
        (volume (orderedJumpRegion 1 T.window.exposure)).toReal =
      P.real {ω : Ω |
        H.countLaw.intervalCount T.window.startTime T.window.endTime ω = 1} := by
  rw [orderedJumpRegion_one_volume_toReal T.window.exposure_nonneg]
  exact H.oneJumpDensity_mul_orderedJumpNestedVolume_eq_windowCount_prob
    T h_exposure

/--
The combined process law's finite ordered-jump density, normalized by the
recursive ordered-jump volume, equals the matching window-count probability.
-/
theorem finiteJumpDensity_mul_orderedJumpNestedVolume_eq_windowCount_prob
    (H : HomogeneousPoissonProcessLaw Ω P) (T : OrderedFiniteJumpTimeline)
    (h_exposure : T.window.exposure ≠ 0) :
    H.arrivalLaw.finiteJumpDensity T *
        orderedJumpNestedVolume T.count T.window.exposure =
      P.real {ω : Ω |
        H.countLaw.intervalCount T.window.startTime T.window.endTime ω =
          T.count} := by
  calc
    H.arrivalLaw.finiteJumpDensity T *
        orderedJumpNestedVolume T.count T.window.exposure =
      countLikelihood H.rate T.window.exposure T.count := by
        simpa [HomogeneousPoissonProcessLaw.rate,
          H.arrival_rate_eq_count_rate] using
            H.arrivalLaw.finiteJumpDensity_mul_orderedJumpNestedVolume_eq_countLikelihood
              T h_exposure
    _ = P.real {ω : Ω |
        H.countLaw.intervalCount T.window.startTime T.window.endTime ω =
          T.count} := by
        exact (H.countLaw.windowCount_prob T.window T.count).symm

/--
The combined process law's finite ordered-jump density, normalized by the
actual Lebesgue volume of the ordered jump-time region, equals the matching
window-count probability.
-/
theorem finiteJumpDensity_mul_orderedJumpRegionVolume_eq_windowCount_prob
    (H : HomogeneousPoissonProcessLaw Ω P) (T : OrderedFiniteJumpTimeline)
    (h_exposure : T.window.exposure ≠ 0) :
    H.arrivalLaw.finiteJumpDensity T *
        (volume (orderedJumpRegion T.count T.window.exposure)).toReal =
      P.real {ω : Ω |
        H.countLaw.intervalCount T.window.startTime T.window.endTime ω =
          T.count} := by
  rw [orderedJumpRegion_volume_toReal T.window.exposure_nonneg]
  exact H.finiteJumpDensity_mul_orderedJumpNestedVolume_eq_windowCount_prob
    T h_exposure

end HomogeneousPoissonProcessLaw

namespace HomogeneousPoissonCountingProcess

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/--
Canonical combined homogeneous Poisson process law induced by primitive
homogeneous counting-process semantics.

The count law is derived from the count path and stationary Poisson increment
marginals; the ordered-arrival density law is the canonical exponential
interarrival law at the same homogeneous rate.
-/
def toHomogeneousPoissonProcessLaw
    (H : HomogeneousPoissonCountingProcess Ω P) :
    HomogeneousPoissonProcessLaw Ω P :=
  HomogeneousPoissonProcessLaw.withCanonicalArrivalDensity
    H.toHomogeneousCountProcessLaw

@[simp] theorem toHomogeneousPoissonProcessLaw_countLaw
    (H : HomogeneousPoissonCountingProcess Ω P) :
    H.toHomogeneousPoissonProcessLaw.countLaw =
      H.toHomogeneousCountProcessLaw := rfl

@[simp] theorem toHomogeneousPoissonProcessLaw_rate
    (H : HomogeneousPoissonCountingProcess Ω P) :
    H.toHomogeneousPoissonProcessLaw.rate = H.rate := rfl

@[simp] theorem toHomogeneousPoissonProcessLaw_intervalCount
    (H : HomogeneousPoissonCountingProcess Ω P) :
    H.toHomogeneousPoissonProcessLaw.countLaw.intervalCount =
      H.intervalCount := rfl

/--
Process-law likelihood of a concrete observed-arrival case induced by
primitive homogeneous counting-process semantics.
-/
def observedArrivalCaseLikelihood
    (H : HomogeneousPoissonCountingProcess Ω P) : ObservedArrivalCase → ℝ :=
  H.toHomogeneousPoissonProcessLaw.observedArrivalCaseLikelihood

/--
The observed-arrival likelihood induced by primitive homogeneous counting
semantics agrees with the reusable no-arrival/interarrival kernel.
-/
theorem observedArrivalCaseLikelihood_eq_kernel_likelihood
    (H : HomogeneousPoissonCountingProcess Ω P)
    (C : ObservedArrivalCase) :
    H.observedArrivalCaseLikelihood C = C.likelihood H.rate := by
  simpa [observedArrivalCaseLikelihood] using
    H.toHomogeneousPoissonProcessLaw.observedArrivalCaseLikelihood_eq_kernel_likelihood C

/--
The observed-arrival likelihood induced by primitive homogeneous counting
semantics factors through the Poisson count likelihood.
-/
theorem observedArrivalCaseLikelihood_factorization
    (H : HomogeneousPoissonCountingProcess Ω P)
    (C : ObservedArrivalCase) :
    H.observedArrivalCaseLikelihood C =
      C.residual * countLikelihood H.rate C.exposure C.count := by
  rw [H.observedArrivalCaseLikelihood_eq_kernel_likelihood C]
  exact C.factorization H.rate

/--
Finite products of observed-arrival likelihoods induced by primitive
homogeneous counting semantics collapse to a single total-count Poisson
likelihood.
-/
theorem observedArrivalCaseLikelihood_product_decomposition
    {Incident : Type*}
    (H : HomogeneousPoissonCountingProcess Ω P)
    (s : Finset Incident) (C : Incident → ObservedArrivalCase)
    (h_totalExposure :
      totalExposure s (fun i => (C i).exposure) ≠ 0) :
    (∏ i ∈ s, H.observedArrivalCaseLikelihood (C i)) =
      ObservedArrivalCase.productResidual s C *
        countLikelihood H.rate
          (totalExposure s fun i => (C i).exposure)
          (totalCount s fun i => (C i).count) := by
  simpa [observedArrivalCaseLikelihood] using
    H.toHomogeneousPoissonProcessLaw.observedArrivalCaseLikelihood_product_decomposition
      s C h_totalExposure

/--
Finite products of observed-arrival likelihoods induced by primitive
homogeneous counting semantics collapse when at least one observed case has
positive exposure.
-/
theorem observedArrivalCaseLikelihood_product_decomposition_of_exists_pos_exposure
    {Incident : Type*}
    (H : HomogeneousPoissonCountingProcess Ω P)
    (s : Finset Incident) (C : Incident → ObservedArrivalCase)
    (h_exists : ∃ i ∈ s, 0 < (C i).exposure) :
    (∏ i ∈ s, H.observedArrivalCaseLikelihood (C i)) =
      ObservedArrivalCase.productResidual s C *
        countLikelihood H.rate
          (totalExposure s fun i => (C i).exposure)
          (totalCount s fun i => (C i).count) := by
  simpa [observedArrivalCaseLikelihood] using
    HomogeneousPoissonProcessLaw.observedArrivalCaseLikelihood_product_decomposition_of_exists_pos_exposure
      H.toHomogeneousPoissonProcessLaw
      s C h_exists

/--
The canonical one-jump ordered density induced by primitive homogeneous
counting-process semantics, normalized by ordered-region volume, equals the
matching one-count window probability.
-/
theorem oneJumpDensity_mul_orderedJumpRegionVolume_eq_windowCount_prob
    (H : HomogeneousPoissonCountingProcess Ω P)
    (T : OrderedOneJumpWindow) (h_exposure : T.window.exposure ≠ 0) :
    H.toHomogeneousPoissonProcessLaw.arrivalLaw.oneJumpDensity T *
        (volume (orderedJumpRegion 1 T.window.exposure)).toReal =
      P.real {ω : Ω |
        H.intervalCount T.window.startTime T.window.endTime ω = 1} := by
  simpa using
    H.toHomogeneousPoissonProcessLaw.oneJumpDensity_mul_orderedJumpRegionVolume_eq_windowCount_prob
      T h_exposure

/--
The canonical finite ordered-jump density induced by primitive homogeneous
counting-process semantics, normalized by ordered-region volume, equals the
matching count-window probability.
-/
theorem finiteJumpDensity_mul_orderedJumpRegionVolume_eq_windowCount_prob
    (H : HomogeneousPoissonCountingProcess Ω P)
    (T : OrderedFiniteJumpTimeline) (h_exposure : T.window.exposure ≠ 0) :
    H.toHomogeneousPoissonProcessLaw.arrivalLaw.finiteJumpDensity T *
        (volume (orderedJumpRegion T.count T.window.exposure)).toReal =
      P.real {ω : Ω |
        H.intervalCount T.window.startTime T.window.endTime ω =
          T.count} := by
  simpa using
    H.toHomogeneousPoissonProcessLaw.finiteJumpDensity_mul_orderedJumpRegionVolume_eq_windowCount_prob
      T h_exposure

end HomogeneousPoissonCountingProcess

namespace HomogeneousPoissonCountingProcessByLaw

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/--
Canonical combined homogeneous Poisson process law induced by mathlib
Poisson-increment laws.
-/
def toHomogeneousPoissonProcessLaw
    (H : HomogeneousPoissonCountingProcessByLaw Ω P) :
    HomogeneousPoissonProcessLaw Ω P :=
  H.toHomogeneousPoissonCountingProcess.toHomogeneousPoissonProcessLaw

@[simp] theorem toHomogeneousPoissonProcessLaw_countLaw
    (H : HomogeneousPoissonCountingProcessByLaw Ω P) :
    H.toHomogeneousPoissonProcessLaw.countLaw =
      H.toHomogeneousPoissonCountingProcess.toHomogeneousCountProcessLaw := rfl

@[simp] theorem toHomogeneousPoissonProcessLaw_rate
    (H : HomogeneousPoissonCountingProcessByLaw Ω P) :
    H.toHomogeneousPoissonProcessLaw.rate = H.rate := rfl

@[simp] theorem toHomogeneousPoissonProcessLaw_intervalCount
    (H : HomogeneousPoissonCountingProcessByLaw Ω P) :
    H.toHomogeneousPoissonProcessLaw.countLaw.intervalCount =
      H.intervalCount := rfl

/--
Process-law likelihood of a concrete observed-arrival case induced directly by
mathlib Poisson-increment laws.
-/
def observedArrivalCaseLikelihood
    (H : HomogeneousPoissonCountingProcessByLaw Ω P) : ObservedArrivalCase → ℝ :=
  H.toHomogeneousPoissonProcessLaw.observedArrivalCaseLikelihood

/--
The observed-arrival likelihood induced directly by mathlib Poisson-increment
laws agrees with the reusable no-arrival/interarrival kernel.
-/
theorem observedArrivalCaseLikelihood_eq_kernel_likelihood
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (C : ObservedArrivalCase) :
    H.observedArrivalCaseLikelihood C = C.likelihood H.rate := by
  simpa [observedArrivalCaseLikelihood] using
    H.toHomogeneousPoissonProcessLaw.observedArrivalCaseLikelihood_eq_kernel_likelihood C

/--
The observed-arrival likelihood induced directly by mathlib Poisson-increment
laws factors through the Poisson count likelihood.
-/
theorem observedArrivalCaseLikelihood_factorization
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (C : ObservedArrivalCase) :
    H.observedArrivalCaseLikelihood C =
      C.residual * countLikelihood H.rate C.exposure C.count := by
  rw [H.observedArrivalCaseLikelihood_eq_kernel_likelihood C]
  exact C.factorization H.rate

/--
Finite products of observed-arrival likelihoods induced directly by mathlib
Poisson-increment laws collapse to a single total-count Poisson likelihood.
-/
theorem observedArrivalCaseLikelihood_product_decomposition
    {Incident : Type*}
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (s : Finset Incident) (C : Incident → ObservedArrivalCase)
    (h_totalExposure :
      totalExposure s (fun i => (C i).exposure) ≠ 0) :
    (∏ i ∈ s, H.observedArrivalCaseLikelihood (C i)) =
      ObservedArrivalCase.productResidual s C *
        countLikelihood H.rate
          (totalExposure s fun i => (C i).exposure)
          (totalCount s fun i => (C i).count) := by
  simpa [observedArrivalCaseLikelihood] using
    H.toHomogeneousPoissonProcessLaw.observedArrivalCaseLikelihood_product_decomposition
      s C h_totalExposure

/--
Finite products of observed-arrival likelihoods induced directly by mathlib
Poisson-increment laws collapse when at least one observed case has positive
exposure.
-/
theorem observedArrivalCaseLikelihood_product_decomposition_of_exists_pos_exposure
    {Incident : Type*}
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (s : Finset Incident) (C : Incident → ObservedArrivalCase)
    (h_exists : ∃ i ∈ s, 0 < (C i).exposure) :
    (∏ i ∈ s, H.observedArrivalCaseLikelihood (C i)) =
      ObservedArrivalCase.productResidual s C *
        countLikelihood H.rate
          (totalExposure s fun i => (C i).exposure)
          (totalCount s fun i => (C i).count) := by
  simpa [observedArrivalCaseLikelihood] using
    HomogeneousPoissonProcessLaw.observedArrivalCaseLikelihood_product_decomposition_of_exists_pos_exposure
      H.toHomogeneousPoissonProcessLaw
      s C h_exists

/--
The canonical one-jump ordered density induced by mathlib Poisson-increment
laws, normalized by ordered-region volume, equals the matching one-count
window probability.
-/
theorem oneJumpDensity_mul_orderedJumpRegionVolume_eq_windowCount_prob
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (T : OrderedOneJumpWindow) (h_exposure : T.window.exposure ≠ 0) :
    H.toHomogeneousPoissonProcessLaw.arrivalLaw.oneJumpDensity T *
        (volume (orderedJumpRegion 1 T.window.exposure)).toReal =
      P.real {ω : Ω |
        H.intervalCount T.window.startTime T.window.endTime ω = 1} := by
  simpa using
    H.toHomogeneousPoissonProcessLaw.oneJumpDensity_mul_orderedJumpRegionVolume_eq_windowCount_prob
      T h_exposure

/--
The canonical one-jump ordered density induced by mathlib Poisson-increment
laws is the one-count Poisson likelihood divided by ordered-region volume.
-/
theorem oneJumpDensity_eq_countLikelihood_div_orderedJumpRegionVolume
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (T : OrderedOneJumpWindow)
    (h_exposure_pos : 0 < T.window.exposure) :
    H.toHomogeneousPoissonProcessLaw.arrivalLaw.oneJumpDensity T =
      countLikelihood H.rate T.window.exposure 1 /
        (volume (orderedJumpRegion 1 T.window.exposure)).toReal := by
  simpa using
    H.toHomogeneousPoissonProcessLaw.arrivalLaw.oneJumpDensity_eq_countLikelihood_div_orderedJumpRegionVolume
      T h_exposure_pos

/--
The canonical finite ordered-jump density induced by mathlib Poisson-increment
laws, normalized by ordered-region volume, equals the matching count-window
probability.
-/
theorem finiteJumpDensity_mul_orderedJumpRegionVolume_eq_windowCount_prob
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (T : OrderedFiniteJumpTimeline) (h_exposure : T.window.exposure ≠ 0) :
    H.toHomogeneousPoissonProcessLaw.arrivalLaw.finiteJumpDensity T *
        (volume (orderedJumpRegion T.count T.window.exposure)).toReal =
      P.real {ω : Ω |
        H.intervalCount T.window.startTime T.window.endTime ω =
          T.count} := by
  simpa using
    H.toHomogeneousPoissonProcessLaw.finiteJumpDensity_mul_orderedJumpRegionVolume_eq_windowCount_prob
      T h_exposure

/--
The canonical finite ordered-jump density induced by mathlib Poisson-increment
laws is the matching count Poisson likelihood divided by ordered-region
volume.
-/
theorem finiteJumpDensity_eq_countLikelihood_div_orderedJumpRegionVolume
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (T : OrderedFiniteJumpTimeline)
    (h_exposure_pos : 0 < T.window.exposure) :
    H.toHomogeneousPoissonProcessLaw.arrivalLaw.finiteJumpDensity T =
      countLikelihood H.rate T.window.exposure T.count /
        (volume (orderedJumpRegion T.count T.window.exposure)).toReal := by
  simpa using
    H.toHomogeneousPoissonProcessLaw.arrivalLaw.finiteJumpDensity_eq_countLikelihood_div_orderedJumpRegionVolume
      T h_exposure_pos

end HomogeneousPoissonCountingProcessByLaw

/-- Zero-inflated Poisson count likelihood with structural-zero mass `γ`. -/
def zeroInflatedCountLikelihood
    (γ rate exposure : ℝ) (count : ℕ) : ℝ :=
  if count = 0 then
    γ + (1 - γ) * countLikelihood rate exposure 0
  else
    (1 - γ) * countLikelihood rate exposure count

@[simp] theorem zeroInflatedCountLikelihood_zero
    (γ rate exposure : ℝ) :
    zeroInflatedCountLikelihood γ rate exposure 0 =
      γ + (1 - γ) * countLikelihood rate exposure 0 := by
  simp [zeroInflatedCountLikelihood]

theorem zeroInflatedCountLikelihood_of_ne_zero
    {γ rate exposure : ℝ} {count : ℕ} (hcount : count ≠ 0) :
    zeroInflatedCountLikelihood γ rate exposure count =
      (1 - γ) * countLikelihood rate exposure count := by
  simp [zeroInflatedCountLikelihood, hcount]

theorem zeroInflatedCountLikelihood_nonneg
    {γ rate exposure : ℝ} {count : ℕ}
    (hγ_nonneg : 0 ≤ γ) (hγ_le : γ ≤ 1)
    (h_mean : 0 ≤ rate * exposure) :
    0 ≤ zeroInflatedCountLikelihood γ rate exposure count := by
  by_cases hcount : count = 0
  · subst hcount
    simp only [zeroInflatedCountLikelihood_zero]
    exact add_nonneg hγ_nonneg
      (mul_nonneg (sub_nonneg.mpr hγ_le) (countLikelihood_nonneg h_mean 0))
  · rw [zeroInflatedCountLikelihood_of_ne_zero hcount]
    exact mul_nonneg (sub_nonneg.mpr hγ_le)
      (countLikelihood_nonneg h_mean count)

end

end PoissonProcess
end Probability
end AppliedModelingLib

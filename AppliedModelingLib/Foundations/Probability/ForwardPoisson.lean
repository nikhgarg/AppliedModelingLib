import AppliedModelingLib.Foundations.Probability.PoissonProcess
import AppliedModelingLib.Foundations.Probability.PoissonMoments
import AppliedModelingLib.Foundations.Probability.IndependentCenteredSums
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.StrongLaw

namespace AppliedModelingLib
namespace Probability
namespace PoissonProcess

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section

/-!
# Forward post-tag homogeneous Poisson counting processes

This is the future-facing process interface needed after a tagged Palm
arrival: time is indexed by `ℝ≥0`, so no values before the tag are present.
The zero count is merely the baseline for *future* increments.  In particular,
this interface does not assert two-sided stationarity, construct a Palm
measure, or establish independence from a tagged queue state.
-/

/--
A positive-rate homogeneous Poisson counting process on a forward time axis.

The probability-law field deliberately makes this suitable for a
stationary/Palm law once the caller separately constructs that law.  It says
nothing about how that Palm law was obtained.  `HasIndepIncrements` is the
mathlib process predicate, specialized here to `ℝ≥0` time.
-/
structure ForwardHomogeneousPoissonCountingProcessByLaw
    (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) where
  /-- The forward process is carried by a probability law. -/
  isProbability : IsProbabilityMeasure P
  rate : ℝ
  rate_pos : 0 < rate
  count : ℝ≥0 → Ω → ℕ
  count_measurable : ∀ t, Measurable (count t)
  count_zero_ae : ∀ᵐ ω ∂P, count 0 ω = 0
  count_mono_ae : ∀ᵐ ω ∂P, Monotone fun t => count t ω
  hasIndepIncrements : ProbabilityTheory.HasIndepIncrements count P
  increment_hasLaw :
    ∀ {s t : ℝ≥0} (hst : s ≤ t),
      ProbabilityTheory.HasLaw
        (fun ω : Ω => count t ω - count s ω)
        (ProbabilityTheory.poissonMeasure
          (rateExposureParam rate ((t : ℝ) - (s : ℝ))
            (mul_nonneg (le_of_lt rate_pos)
              (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst))))) P

namespace ForwardHomogeneousPoissonCountingProcessByLaw

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The nonnegative forward Poisson rate is nonnegative as a real number. -/
theorem rate_nonneg
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P) :
    0 ≤ H.rate :=
  le_of_lt H.rate_pos

/-- Reparameterize a forward Poisson process by a positive deterministic time scale. -/
def timeScale
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (scale : ℝ≥0) (hscale : 0 < scale) :
    ForwardHomogeneousPoissonCountingProcessByLaw Ω P where
  isProbability := H.isProbability
  rate := H.rate * (scale : ℝ)
  rate_pos := mul_pos H.rate_pos (by exact_mod_cast hscale)
  count := fun t omega => H.count (scale * t) omega
  count_measurable := fun t => H.count_measurable (scale * t)
  count_zero_ae := by
    simpa using H.count_zero_ae
  count_mono_ae := by
    filter_upwards [H.count_mono_ae] with omega hmono
    intro s t hst
    exact hmono (mul_le_mul_right hst scale)
  hasIndepIncrements := by
    intro n t ht
    simpa using H.hasIndepIncrements n (fun i => scale * t i)
      (fun i j hij => mul_le_mul_right (ht hij) scale)
  increment_hasLaw := by
    intro s t hst
    have hscaled : scale * s ≤ scale * t := mul_le_mul_right hst scale
    have hparam :
        rateExposureParam H.rate (((scale * t : ℝ≥0) : ℝ) - (scale * s : ℝ≥0))
          (mul_nonneg H.rate_nonneg
            (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hscaled))) =
        rateExposureParam (H.rate * (scale : ℝ)) ((t : ℝ) - (s : ℝ))
          (mul_nonneg (mul_nonneg H.rate_nonneg (by exact_mod_cast hscale.le))
            (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst))) := by
      ext
      simp only [rateExposureParam, NNReal.coe_mul]
      ring_nf
    rw [← hparam]
    exact H.increment_hasLaw hscaled

/-- Each forward count coordinate is measurable. -/
theorem measurable_count
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (t : ℝ≥0) :
    Measurable (H.count t) :=
  H.count_measurable t

/-- On the discrete count codomain, coordinate measurability gives strong measurability. -/
theorem stronglyMeasurable_count
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (t : ℝ≥0) :
    StronglyMeasurable (H.count t) :=
  (H.measurable_count t).stronglyMeasurable

/--
The count accumulated in the forward interval `[s,t]`.  It is only defined
for forward times, so it cannot accidentally be used to reason about the
pre-tag past.
-/
def intervalCount
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (s t : ℝ≥0) (ω : Ω) : ℕ :=
  H.count t ω - H.count s ω

/-- Forward interval counts are measurable random variables. -/
theorem measurable_intervalCount
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (s t : ℝ≥0) :
    Measurable (H.intervalCount s t) := by
  exact (H.measurable_count t).sub (H.measurable_count s)

/-- Forward count paths are almost surely monotone. -/
theorem count_mono
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P) :
    ∀ᵐ ω ∂P, Monotone fun t => H.count t ω :=
  H.count_mono_ae

/-- Ordered forward-time count coordinates are almost surely ordered. -/
theorem count_le_ae
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    {s t : ℝ≥0} (hst : s ≤ t) :
    ∀ᵐ ω ∂P, H.count s ω ≤ H.count t ω := by
  filter_upwards [H.count_mono_ae] with ω hmono
  exact hmono hst

/-- The forward interval count has its specified Mathlib Poisson law. -/
theorem intervalCount_hasLaw
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    {s t : ℝ≥0} (hst : s ≤ t) :
    ProbabilityTheory.HasLaw
      (fun ω : Ω => H.intervalCount s t ω)
      (ProbabilityTheory.poissonMeasure
        (rateExposureParam H.rate ((t : ℝ) - (s : ℝ))
          (mul_nonneg H.rate_nonneg
            (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst))))) P := by
  simpa [intervalCount] using H.increment_hasLaw hst

/-- Real-valued PMF formula for a forward interval count. -/
theorem intervalCount_prob
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    {s t : ℝ≥0} (hst : s ≤ t) (n : ℕ) :
    P.real {ω : Ω | H.intervalCount s t ω = n} =
      countLikelihood H.rate ((t : ℝ) - (s : ℝ)) n := by
  exact
    hasLaw_poissonMeasure_real_singleton_eq_countLikelihood
      (mul_nonneg H.rate_nonneg
        (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst)))
      (H.intervalCount_hasLaw hst) n

/-- The real-valued count in a forward interval is integrable. -/
theorem intervalCount_real_integrable
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    {s t : ℝ≥0} (hst : s ≤ t) :
    Integrable (fun omega => (H.intervalCount s t omega : ℝ)) P := by
  let r : ℝ≥0 := rateExposureParam H.rate ((t : ℝ) - (s : ℝ))
    (mul_nonneg H.rate_nonneg
      (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst)))
  have hint : Integrable (fun n : ℕ => (n : ℝ))
      (ProbabilityTheory.poissonMeasure r) :=
    integrable_natCast_poissonMeasure r
  have hmap : Integrable (fun n : ℕ => (n : ℝ))
      (Measure.map (H.intervalCount s t) P) := by
    rw [(H.intervalCount_hasLaw hst).map_eq]
    exact hint
  simpa [Function.comp_def] using
    hmap.comp_aemeasurable (H.intervalCount_hasLaw hst).aemeasurable

/-- The expected real-valued count in a forward interval is rate times its length. -/
theorem intervalCount_real_expectation
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    {s t : ℝ≥0} (hst : s ≤ t) :
    ∫ omega, (H.intervalCount s t omega : ℝ) ∂P =
      H.rate * ((t : ℝ) - (s : ℝ)) := by
  let r : ℝ≥0 := rateExposureParam H.rate ((t : ℝ) - (s : ℝ))
    (mul_nonneg H.rate_nonneg
      (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst)))
  calc
    ∫ omega, (H.intervalCount s t omega : ℝ) ∂P =
        ∫ n : ℕ, (n : ℝ) ∂ProbabilityTheory.poissonMeasure r := by
      simpa [r, Function.comp_def] using
        (H.intervalCount_hasLaw hst).integral_comp
          (f := fun n : ℕ => (n : ℝ))
          (measurable_of_countable _).aestronglyMeasurable
    _ = r := integral_id_poissonMeasure r
    _ = H.rate * ((t : ℝ) - (s : ℝ)) := by
      rfl

/-- Two adjacent forward interval counts are independent. -/
theorem indepFun_intervalCount_adjacent
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    {r s t : ℝ≥0} (hrs : r ≤ s) (hst : s ≤ t) :
    ProbabilityTheory.IndepFun
      (fun omega : Ω => H.intervalCount r s omega)
      (fun omega : Ω => H.intervalCount s t omega) P := by
  simpa [intervalCount] using
    H.hasIndepIncrements.indepFun_sub_sub hrs hst

/--
A real-valued observable of one interval factors from the count in the next
adjacent interval.  This is the one-step predictable compensation identity
for a forward Poisson process.
-/
theorem integral_intervalCountSelector_mul_nextIntervalCount
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    {r s t : ℝ≥0} (hrs : r ≤ s) (hst : s ≤ t)
    (f : ℕ → ℝ) (hf : Measurable f) :
    ∫ omega, f (H.intervalCount r s omega) *
        (H.intervalCount s t omega : ℝ) ∂P =
      (∫ omega, f (H.intervalCount r s omega) ∂P) *
        (H.rate * ((t : ℝ) - (s : ℝ))) := by
  have hind : ProbabilityTheory.IndepFun
      (fun omega : Ω => f (H.intervalCount r s omega))
      (fun omega : Ω => (H.intervalCount s t omega : ℝ)) P :=
    (H.indepFun_intervalCount_adjacent hrs hst).comp hf
      (measurable_of_countable fun n : ℕ => (n : ℝ))
  calc
    ∫ omega, f (H.intervalCount r s omega) *
        (H.intervalCount s t omega : ℝ) ∂P =
        (∫ omega, f (H.intervalCount r s omega) ∂P) *
          (∫ omega, (H.intervalCount s t omega : ℝ) ∂P) := by
      simpa using hind.integral_mul_eq_mul_integral
        (hf.comp (H.measurable_intervalCount r s)).aestronglyMeasurable
        ((measurable_of_countable fun n : ℕ => (n : ℝ)).comp
          (H.measurable_intervalCount s t)).aestronglyMeasurable
    _ = _ := by rw [H.intervalCount_real_expectation hst]

/--
At a forward time `t`, the count itself has the Poisson law at exposure `t`.
This uses the forward zero baseline only; it does not promote the model to a
two-sided stationary process.
-/
theorem count_hasLaw
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (t : ℝ≥0) :
    ProbabilityTheory.HasLaw
      (H.count t)
      (ProbabilityTheory.poissonMeasure
        (rateExposureParam H.rate (t : ℝ)
          (mul_nonneg H.rate_nonneg (NNReal.coe_nonneg t)))) P := by
  have hEq :
      (fun ω : Ω => H.count t ω) =ᵐ[P]
        (fun ω : Ω => H.count t ω - H.count 0 ω) := by
    filter_upwards [H.count_zero_ae] with ω hzero
    simp [hzero]
  simpa using (H.increment_hasLaw (s := 0) (t := t) (zero_le t)).congr hEq

/-- Real-valued Poisson PMF for the forward count at time `t`. -/
theorem count_prob
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (t : ℝ≥0) (n : ℕ) :
    P.real {ω : Ω | H.count t ω = n} =
      countLikelihood H.rate (t : ℝ) n := by
  exact
    hasLaw_poissonMeasure_real_singleton_eq_countLikelihood
      (mul_nonneg H.rate_nonneg (NNReal.coe_nonneg t))
      (H.count_hasLaw t) n

/--
The one-time count law in the unit-rate/mean form used by the M/M/1 mixture
calculation.  This is the direct bridge to a future service-count argument.
-/
theorem count_prob_eq_unit_rate_product
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (t : ℝ≥0) (n : ℕ) :
    P.real {ω : Ω | H.count t ω = n} =
      countLikelihood 1 (H.rate * (t : ℝ)) n := by
  rw [H.count_prob t n]
  simp [countLikelihood]

/--
At a real nonnegative horizon, the forward count has exactly the
unit-rate/mean form expected by the stationary M/M/1 mixture theorem.
-/
theorem count_prob_atReal_eq_unit_rate_product
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    {z : ℝ} (hz : 0 ≤ z) (n : ℕ) :
    P.real {ω : Ω | H.count z.toNNReal ω = n} =
      countLikelihood 1 (H.rate * z) n := by
  simpa [Real.coe_toNNReal _ hz] using
    H.count_prob_eq_unit_rate_product z.toNNReal n

/-- Independent forward interval counts along any monotone finite timeline. -/
theorem iIndepFun_intervalCount_fin
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    {n : ℕ} {t : Fin (n + 1) → ℝ≥0} (ht : Monotone t) :
    ProbabilityTheory.iIndepFun
      (fun (i : Fin n) (ω : Ω) =>
        H.intervalCount (t i.castSucc) (t i.succ) ω) P := by
  simpa [intervalCount] using H.hasIndepIncrements n t ht

/-- The count in the forward unit interval `[n,n+1]`. -/
def unitIntervalCount
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (n : ℕ) (omega : Ω) : ℕ :=
  H.intervalCount (n : ℝ≥0) ((n : ℝ≥0) + 1) omega

/-- Unit-width interval counts are measurable random variables. -/
theorem measurable_unitIntervalCount
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (n : ℕ) :
    Measurable (H.unitIntervalCount n) :=
  H.measurable_intervalCount _ _

/-- The vector of forward unit-interval counts strictly before index `n`. -/
def unitIntervalCountPrefix
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (n : ℕ) (omega : Ω) : Finset.range n → ℕ :=
  fun k => H.unitIntervalCount k omega

/-- A finite prefix of forward unit-interval counts is measurable. -/
theorem measurable_unitIntervalCountPrefix
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (n : ℕ) :
    Measurable (H.unitIntervalCountPrefix n) := by
  apply measurable_pi_lambda
  intro k
  exact H.measurable_unitIntervalCount k

/-- Every unit-width forward increment has the same Poisson law. -/
theorem unitIntervalCount_hasLaw
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (n : ℕ) :
    ProbabilityTheory.HasLaw (H.unitIntervalCount n)
      (ProbabilityTheory.poissonMeasure
        (rateExposureParam H.rate 1 (by simpa using H.rate_nonneg))) P := by
  have hle : (n : ℝ≥0) ≤ ((n + 1 : ℕ) : ℝ≥0) := by
    exact_mod_cast Nat.le_succ n
  simpa [unitIntervalCount] using H.intervalCount_hasLaw hle

/-- Every real-valued forward unit-interval count has expectation equal to the rate. -/
theorem unitIntervalCount_real_expectation_at
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (n : ℕ) :
    ∫ omega, (H.unitIntervalCount n omega : ℝ) ∂P = H.rate := by
  have hle : (n : ℝ≥0) ≤ ((n : ℝ≥0) + 1) :=
    le_add_of_nonneg_right zero_le_one
  have hlength : (((n : ℝ≥0) + 1 : ℝ≥0) : ℝ) - (n : ℝ≥0) = 1 := by
    norm_num
  calc
    ∫ omega, (H.unitIntervalCount n omega : ℝ) ∂P =
        H.rate * ((((n : ℝ≥0) + 1 : ℝ≥0) : ℝ) - (n : ℝ≥0)) := by
      simpa [unitIntervalCount] using H.intervalCount_real_expectation hle
    _ = H.rate := by rw [hlength, mul_one]

/-- Every real-valued forward unit-interval count is integrable. -/
theorem unitIntervalCount_real_integrable_at
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (n : ℕ) :
    Integrable (fun omega => (H.unitIntervalCount n omega : ℝ)) P := by
  have hle : (n : ℝ≥0) ≤ ((n : ℝ≥0) + 1) :=
    le_add_of_nonneg_right zero_le_one
  simpa [unitIntervalCount] using H.intervalCount_real_integrable hle

/-- Unit-width forward increments are jointly independent. -/
theorem iIndepFun_unitIntervalCount
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P) :
    ProbabilityTheory.iIndepFun H.unitIntervalCount P := by
  simpa [unitIntervalCount, intervalCount] using
    H.hasIndepIncrements.nat (t := fun n : ℕ => (n : ℝ≥0)) (by
      intro i j hij
      change (i : ℝ≥0) ≤ (j : ℝ≥0)
      exact_mod_cast hij)

/-- The real-valued unit-interval counts remain jointly independent. -/
theorem iIndepFun_unitIntervalCount_real
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P) :
    ProbabilityTheory.iIndepFun
      (fun n omega => (H.unitIntervalCount n omega : ℝ)) P := by
  simpa only [Function.comp_apply] using
    H.iIndepFun_unitIntervalCount.comp
      (fun _ => fun count : ℕ => (count : ℝ))
      (fun _ => measurable_of_countable fun count : ℕ => (count : ℝ))

/-- A unit-interval count after subtracting its common mean. -/
def centeredUnitIntervalCount
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (n : ℕ) (omega : Ω) : ℝ :=
  (H.unitIntervalCount n omega : ℝ) - H.rate

/-- Centered real unit-interval counts remain jointly independent. -/
theorem iIndepFun_centeredUnitIntervalCount
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P) :
    ProbabilityTheory.iIndepFun H.centeredUnitIntervalCount P := by
  simpa only [centeredUnitIntervalCount, Function.comp_apply] using
    H.iIndepFun_unitIntervalCount_real.comp
      (fun _ => fun count : ℝ => count - H.rate)
      (fun _ => measurable_id.sub measurable_const)

/-- Centered unit-interval counts have mean zero. -/
theorem integral_centeredUnitIntervalCount
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (n : ℕ) :
    ∫ omega, H.centeredUnitIntervalCount n omega ∂P = 0 := by
  letI : IsProbabilityMeasure P := H.isProbability
  change ∫ omega, ((H.unitIntervalCount n omega : ℝ) - H.rate) ∂P = 0
  rw [
    integral_sub (H.unitIntervalCount_real_integrable_at n) (integrable_const _),
    H.unitIntervalCount_real_expectation_at n, integral_const]
  simp

/-- Each centered unit-interval count is square integrable. -/
theorem memLp_two_centeredUnitIntervalCount
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (n : ℕ) :
    MemLp (H.centeredUnitIntervalCount n) 2 P := by
  letI : IsProbabilityMeasure P := H.isProbability
  let r : ℝ≥0 := rateExposureParam H.rate 1 (by simpa using H.rate_nonneg)
  refine (memLp_two_iff_integrable_sq ?_).2 ?_
  · apply StronglyMeasurable.aestronglyMeasurable
    change StronglyMeasurable (fun omega =>
      (H.unitIntervalCount n omega : ℝ) - H.rate)
    exact ((measurable_of_countable fun count : ℕ => (count : ℝ)).comp
      (H.measurable_unitIntervalCount n)).stronglyMeasurable.sub stronglyMeasurable_const
  have hmap : Integrable (fun count : ℕ => ((count : ℝ) - r) ^ 2)
      (Measure.map (H.unitIntervalCount n) P) := by
    rw [(H.unitIntervalCount_hasLaw n).map_eq]
    exact integrable_natCast_sub_parameter_sq_poissonMeasure r
  have hcomp : Integrable (fun omega =>
      ((H.unitIntervalCount n omega : ℝ) - r) ^ 2) P := by
    simpa [Function.comp_def] using
      hmap.comp_aemeasurable (H.unitIntervalCount_hasLaw n).aemeasurable
  have hr : (r : ℝ) = H.rate := by
    dsimp [r, rateExposureParam]
    change H.rate * 1 = H.rate
    ring
  simpa [centeredUnitIntervalCount, hr] using hcomp

/-- The squared centered unit-interval count has expectation equal to the rate. -/
theorem integral_sq_centeredUnitIntervalCount
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (n : ℕ) :
    ∫ omega, (H.centeredUnitIntervalCount n omega) ^ 2 ∂P = H.rate := by
  letI : IsProbabilityMeasure P := H.isProbability
  let r : ℝ≥0 := rateExposureParam H.rate 1 (by simpa using H.rate_nonneg)
  calc
    ∫ omega, (H.centeredUnitIntervalCount n omega) ^ 2 ∂P =
        ∫ count : ℕ, ((count : ℝ) - r) ^ 2 ∂ProbabilityTheory.poissonMeasure r := by
      simpa [centeredUnitIntervalCount, r, rateExposureParam, Function.comp_def] using
        (H.unitIntervalCount_hasLaw n).integral_comp
          (f := fun count : ℕ => ((count : ℝ) - r) ^ 2)
          (integrable_natCast_sub_parameter_sq_poissonMeasure r).aestronglyMeasurable
    _ = r := integral_natCast_sub_parameter_sq_poissonMeasure r
    _ = H.rate := by
      dsimp [r, rateExposureParam]
      change H.rate * 1 = H.rate
      ring

/-- The variance of a centered unit-interval count is the process rate. -/
theorem variance_centeredUnitIntervalCount
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (n : ℕ) :
    ProbabilityTheory.variance (H.centeredUnitIntervalCount n) P = H.rate := by
  rw [ProbabilityTheory.variance_of_integral_eq_zero
    (H.memLp_two_centeredUnitIntervalCount n).aemeasurable
    (H.integral_centeredUnitIntervalCount n)]
  exact H.integral_sq_centeredUnitIntervalCount n

/-- The centered sum of unit increments after the initial interval.  This
shifted convention uses the ordinary natural filtration of the complete
unit-increment sequence. -/
def centeredUnitIntervalCountPartialSum
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (steps : ℕ) (omega : Ω) : ℝ :=
  AppliedModelingLib.Probability.shiftedCenteredPartialSum
    (fun n omega => (H.unitIntervalCount n omega : ℝ)) (fun _ => H.rate) steps omega

/-- Expansion of a centered post-initial increment sum into its finite mesh. -/
theorem centeredUnitIntervalCountPartialSum_eq_sum
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (steps : ℕ) :
    H.centeredUnitIntervalCountPartialSum steps =
      fun omega => ∑ index ∈ Finset.range steps,
        H.centeredUnitIntervalCount (index + 1) omega := by
  funext omega
  simp [centeredUnitIntervalCountPartialSum,
    AppliedModelingLib.Probability.shiftedCenteredPartialSum, centeredUnitIntervalCount]

/-- Centered post-initial unit-increment sums are martingales for the natural
unit-increment filtration. -/
theorem centeredUnitIntervalCountPartialSum_martingale
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P) :
    Martingale (H.centeredUnitIntervalCountPartialSum)
      (Filtration.natural (fun n omega => (H.unitIntervalCount n omega : ℝ))
        (fun n => ((measurable_of_countable fun count : ℕ => (count : ℝ)).comp
          (H.measurable_unitIntervalCount n)).stronglyMeasurable)) P := by
  letI : IsProbabilityMeasure P := H.isProbability
  exact AppliedModelingLib.Probability.shiftedCenteredPartialSum_martingale
    (fun n => ((measurable_of_countable fun count : ℕ => (count : ℝ)).comp
      (H.measurable_unitIntervalCount n)).stronglyMeasurable)
    (fun n => H.unitIntervalCount_real_integrable_at n)
    H.iIndepFun_unitIntervalCount_real (fun _ => H.rate)
    (fun n => (H.unitIntervalCount_real_expectation_at (n + 1)).symm)

/-- Every finite centered post-initial increment sum is square integrable. -/
theorem memLp_two_centeredUnitIntervalCountPartialSum
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (steps : ℕ) :
    MemLp (H.centeredUnitIntervalCountPartialSum steps) 2 P := by
  letI : IsProbabilityMeasure P := H.isProbability
  rw [H.centeredUnitIntervalCountPartialSum_eq_sum]
  exact (MeasureTheory.memLp_finset_sum (Finset.range steps) fun index _ =>
    H.memLp_two_centeredUnitIntervalCount (index + 1))

/-- The terminal second moment of a centered post-initial unit-increment sum
is linear in the number of mesh cells. -/
theorem integral_sq_centeredUnitIntervalCountPartialSum
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (steps : ℕ) :
    ∫ omega, (H.centeredUnitIntervalCountPartialSum steps omega) ^ 2 ∂P =
      steps * H.rate := by
  letI : IsProbabilityMeasure P := H.isProbability
  have hmean : ∫ omega, H.centeredUnitIntervalCountPartialSum steps omega ∂P = 0 := by
    rw [H.centeredUnitIntervalCountPartialSum_eq_sum]
    rw [MeasureTheory.integral_finset_sum]
    · exact Finset.sum_eq_zero fun index _ =>
        H.integral_centeredUnitIntervalCount (index + 1)
    · intro index _
      exact (H.memLp_two_centeredUnitIntervalCount (index + 1)).integrable one_le_two
  calc
    ∫ omega, (H.centeredUnitIntervalCountPartialSum steps omega) ^ 2 ∂P =
        ProbabilityTheory.variance (H.centeredUnitIntervalCountPartialSum steps) P := by
      rw [ProbabilityTheory.variance_of_integral_eq_zero
        (H.memLp_two_centeredUnitIntervalCountPartialSum steps).aemeasurable hmean]
    _ = ∑ index ∈ Finset.range steps,
        ProbabilityTheory.variance (H.centeredUnitIntervalCount (index + 1)) P := by
      rw [H.centeredUnitIntervalCountPartialSum_eq_sum]
      have hsum : (fun omega => ∑ index ∈ Finset.range steps,
          H.centeredUnitIntervalCount (index + 1) omega) =
          ∑ index ∈ Finset.range steps,
            H.centeredUnitIntervalCount (index + 1) := by
        ext omega
        simp
      rw [hsum]
      exact ProbabilityTheory.IndepFun.variance_sum
        (fun index _ => H.memLp_two_centeredUnitIntervalCount (index + 1))
        (fun i hi j hj hij => H.iIndepFun_centeredUnitIntervalCount.indepFun (by
          intro hsucc
          exact hij (Nat.succ_injective hsucc)))
    _ = steps * H.rate := by
      simp_rw [H.variance_centeredUnitIntervalCount]
      simp

/-- Doob's inequality for a finite mesh of centered post-initial Poisson
increments, with its exact linear terminal second-moment bound. -/
theorem ennreal_mul_measure_range_sup_sq_le_centeredUnitIntervalCountPartialSum
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (threshold : ℝ≥0) (steps : ℕ) :
    threshold * P {omega | (threshold : ℝ) ≤
      (Finset.range (steps + 1)).sup' Finset.nonempty_range_add_one
        (fun index => (H.centeredUnitIntervalCountPartialSum index omega) ^ 2)} ≤
      ENNReal.ofReal (steps * H.rate) := by
  letI : IsProbabilityMeasure P := H.isProbability
  calc
    threshold * P {omega | (threshold : ℝ) ≤
        (Finset.range (steps + 1)).sup' Finset.nonempty_range_add_one
          (fun index => (H.centeredUnitIntervalCountPartialSum index omega) ^ 2)} ≤
        ENNReal.ofReal (∫ omega,
          (H.centeredUnitIntervalCountPartialSum steps omega) ^ 2 ∂P) :=
      AppliedModelingLib.ennreal_mul_measure_range_sup_sq_le_integral_sq
        H.centeredUnitIntervalCountPartialSum_martingale
        H.memLp_two_centeredUnitIntervalCountPartialSum threshold steps
    _ = ENNReal.ofReal (steps * H.rate) := by
      rw [H.integral_sq_centeredUnitIntervalCountPartialSum steps]

/-- The finite unit-interval count history before `n` is independent of the
count in interval `n`. -/
theorem indepFun_unitIntervalCountPrefix_nextUnitIntervalCount
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (n : ℕ) :
    ProbabilityTheory.IndepFun (H.unitIntervalCountPrefix n)
      (H.unitIntervalCount n) P := by
  have hraw := H.iIndepFun_unitIntervalCount.indepFun_finset
    (Finset.range n) ({n} : Finset ℕ) (by simp)
    (fun k => H.measurable_unitIntervalCount k)
  simpa [unitIntervalCountPrefix, Function.comp_def] using hraw.comp measurable_id
    (measurable_pi_apply ⟨n, Finset.mem_singleton_self n⟩)

/-- An independent external factor together with the count history before
`n` is independent of the next unit-interval count. -/
theorem indepFun_external_unitIntervalCountPrefix_nextUnitIntervalCount
    {σ : Type*} [MeasurableSpace σ]
    (ρ : Measure σ) [IsProbabilityMeasure ρ]
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (n : ℕ) :
    ProbabilityTheory.IndepFun
      (fun z : σ × Ω => (z.1, H.unitIntervalCountPrefix n z.2))
      (fun z : σ × Ω => H.unitIntervalCount n z.2) (ρ.prod P) := by
  letI : IsProbabilityMeasure P := H.isProbability
  let p : Ω → (Finset.range n → ℕ) := H.unitIntervalCountPrefix n
  let b : Ω → ℕ := H.unitIntervalCount n
  let X : σ × Ω → σ × (Finset.range n → ℕ) := fun z => (z.1, p z.2)
  let Y : σ × Ω → ℕ := fun z => b z.2
  let pairPB : Ω → (Finset.range n → ℕ) × ℕ := fun omega => (p omega, b omega)
  have hp : Measurable p := by
    simpa [p] using H.measurable_unitIntervalCountPrefix n
  have hb : Measurable b := by
    simpa [b] using H.measurable_unitIntervalCount n
  have hpairPB : P.map pairPB = (P.map p).prod (P.map b) := by
    have hindep := H.indepFun_unitIntervalCountPrefix_nextUnitIntervalCount n
    exact (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      hp.aemeasurable hb.aemeasurable).mp (by simpa [p, b, pairPB] using hindep)
  have hX : (ρ.prod P).map X = ρ.prod (P.map p) := by
    simpa [X] using (Measure.map_prod_map ρ P measurable_id hp).symm
  have hY : (ρ.prod P).map Y = P.map b := by
    calc
      (ρ.prod P).map Y = (ρ.prod P).map (b ∘ Prod.snd) := by rfl
      _ = ((ρ.prod P).map Prod.snd).map b := by
        rw [Measure.map_map hb measurable_snd]
      _ = P.map b := by
        rw [Measure.map_snd_prod, measure_univ, one_smul]
  apply (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
    ((measurable_fst.prodMk (hp.comp measurable_snd)).aemeasurable)
    (hb.comp measurable_snd).aemeasurable).mpr
  calc
    (ρ.prod P).map (fun z => (X z, Y z)) =
        ((ρ.prod P).map (Prod.map id pairPB)).map
          (MeasurableEquiv.prodAssoc.symm :
            σ × ((Finset.range n → ℕ) × ℕ) →
              (σ × (Finset.range n → ℕ)) × ℕ) := by
          rw [Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
            (measurable_id.prodMap (hp.prodMk hb))]
          rfl
    _ = (ρ.prod (P.map pairPB)).map
          (MeasurableEquiv.prodAssoc.symm :
            σ × ((Finset.range n → ℕ) × ℕ) →
              (σ × (Finset.range n → ℕ)) × ℕ) := by
          rw [← Measure.map_prod_map ρ P measurable_id (hp.prodMk hb)]
          rw [Measure.map_id]
    _ = (ρ.prod ((P.map p).prod (P.map b))).map
          (MeasurableEquiv.prodAssoc.symm :
            σ × ((Finset.range n → ℕ) × ℕ) →
              (σ × (Finset.range n → ℕ)) × ℕ) := by
          rw [hpairPB]
    _ = (ρ.prod (P.map p)).prod (P.map b) := by
          exact (measurePreserving_prodAssoc ρ (P.map p) (P.map b)).symm.map_eq
    _ = ((ρ.prod P).map X).prod ((ρ.prod P).map Y) := by
          rw [hX, hY]

/--
A measurable statistic of an independent external factor and the
unit-interval history before `n` factors from the next unit-interval count.
-/
theorem integral_externalUnitIntervalCountPrefixSelector_mul_nextUnitIntervalCount
    {σ : Type*} [MeasurableSpace σ]
    (ρ : Measure σ) [IsProbabilityMeasure ρ]
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (n : ℕ) (f : σ × (Finset.range n → ℕ) → ℝ) (hf : Measurable f) :
    ∫ z, f (z.1, H.unitIntervalCountPrefix n z.2) *
        (H.unitIntervalCount n z.2 : ℝ) ∂(ρ.prod P) =
      (∫ z, f (z.1, H.unitIntervalCountPrefix n z.2) ∂(ρ.prod P)) * H.rate := by
  letI : IsProbabilityMeasure P := H.isProbability
  have hind : ProbabilityTheory.IndepFun
      (fun z : σ × Ω => f (z.1, H.unitIntervalCountPrefix n z.2))
      (fun z : σ × Ω => (H.unitIntervalCount n z.2 : ℝ)) (ρ.prod P) := by
    exact (H.indepFun_external_unitIntervalCountPrefix_nextUnitIntervalCount ρ n).comp hf
      (measurable_of_countable fun k : ℕ => (k : ℝ))
  calc
    ∫ z, f (z.1, H.unitIntervalCountPrefix n z.2) *
        (H.unitIntervalCount n z.2 : ℝ) ∂(ρ.prod P) =
        (∫ z, f (z.1, H.unitIntervalCountPrefix n z.2) ∂(ρ.prod P)) *
          (∫ z, (H.unitIntervalCount n z.2 : ℝ) ∂(ρ.prod P)) := by
      simpa using hind.integral_mul_eq_mul_integral
        (hf.comp (measurable_fst.prodMk
          ((H.measurable_unitIntervalCountPrefix n).comp measurable_snd))).aestronglyMeasurable
        ((measurable_of_countable fun k : ℕ => (k : ℝ)).comp
          ((H.measurable_unitIntervalCount n).comp measurable_snd)).aestronglyMeasurable
    _ = _ := by
      have hnext :
          (∫ z : σ × Ω, (H.unitIntervalCount n z.2 : ℝ) ∂(ρ.prod P)) =
            ∫ omega, (H.unitIntervalCount n omega : ℝ) ∂P := by
        simpa [Function.comp_def] using
          (measurePreserving_snd : MeasurePreserving Prod.snd (ρ.prod P) P).hasLaw.integral_comp
            (f := fun omega : Ω => (H.unitIntervalCount n omega : ℝ))
            ((measurable_of_countable fun k : ℕ => (k : ℝ)).comp
              (H.measurable_unitIntervalCount n)).aestronglyMeasurable
      rw [hnext, H.unitIntervalCount_real_expectation_at n]

/--
An event determined by an independent external factor and the count history
before `n` factors from the next unit-interval count.  This is the one-step
external predictable-count compensation identity.
-/
theorem integral_externalPredictableEvent_indicator_mul_nextUnitIntervalCount
    {σ : Type*} [MeasurableSpace σ]
    (ρ : Measure σ) [IsProbabilityMeasure ρ]
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (n : ℕ) (A : Set (σ × Ω))
    (hA : MeasurableSet[MeasurableSpace.comap
      (fun z : σ × Ω => (z.1, H.unitIntervalCountPrefix n z.2)) inferInstance] A) :
    ∫ z, A.indicator (fun _ => (1 : ℝ)) z *
        (H.unitIntervalCount n z.2 : ℝ) ∂(ρ.prod P) =
      (ρ.prod P).real A * H.rate := by
  letI : IsProbabilityMeasure P := H.isProbability
  rcases hA with ⟨u, hu, hpre⟩
  have hAmeasurable : MeasurableSet A := by
    rw [← hpre]
    exact hu.preimage (measurable_fst.prodMk
      ((H.measurable_unitIntervalCountPrefix n).comp measurable_snd))
  let f : σ × (Finset.range n → ℕ) → ℝ := u.indicator (fun _ => (1 : ℝ))
  have hf : Measurable f := measurable_const.indicator hu
  have hleft :
      (fun z : σ × Ω => f (z.1, H.unitIntervalCountPrefix n z.2) *
          (H.unitIntervalCount n z.2 : ℝ)) =
        fun z => A.indicator (fun _ => (1 : ℝ)) z *
          (H.unitIntervalCount n z.2 : ℝ) := by
    funext z
    have hmem : (z.1, H.unitIntervalCountPrefix n z.2) ∈ u ↔ z ∈ A := by
      change z ∈ (fun z : σ × Ω => (z.1, H.unitIntervalCountPrefix n z.2)) ⁻¹' u ↔ z ∈ A
      rw [hpre]
    by_cases h : (z.1, H.unitIntervalCountPrefix n z.2) ∈ u
    · have hA' : z ∈ A := hmem.mp h
      simp [f, Set.indicator, h, hA']
    · have hA' : z ∉ A := by
        intro hz
        exact h (hmem.mpr hz)
      simp [f, Set.indicator, h, hA']
  have hprefix :
      (∫ z : σ × Ω, f (z.1, H.unitIntervalCountPrefix n z.2) ∂(ρ.prod P)) =
        (ρ.prod P).real A := by
    calc
      (∫ z : σ × Ω, f (z.1, H.unitIntervalCountPrefix n z.2) ∂(ρ.prod P)) =
          ∫ z : σ × Ω, A.indicator (fun _ => (1 : ℝ)) z ∂(ρ.prod P) := by
        apply integral_congr_ae
        filter_upwards [] with z
        have hmem : (z.1, H.unitIntervalCountPrefix n z.2) ∈ u ↔ z ∈ A := by
          change z ∈ (fun z : σ × Ω => (z.1, H.unitIntervalCountPrefix n z.2)) ⁻¹' u ↔ z ∈ A
          rw [hpre]
        by_cases h : (z.1, H.unitIntervalCountPrefix n z.2) ∈ u
        · have hA' : z ∈ A := hmem.mp h
          simp [f, Set.indicator, h, hA']
        · have hA' : z ∉ A := by
            intro hz
            exact h (hmem.mpr hz)
          simp [f, Set.indicator, h, hA']
      _ = (ρ.prod P).real A := by
        rw [MeasureTheory.integral_indicator hAmeasurable,
          MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
  calc
    ∫ z, A.indicator (fun _ => (1 : ℝ)) z *
        (H.unitIntervalCount n z.2 : ℝ) ∂(ρ.prod P) =
        ∫ z, f (z.1, H.unitIntervalCountPrefix n z.2) *
          (H.unitIntervalCount n z.2 : ℝ) ∂(ρ.prod P) := by rw [hleft]
    _ = (∫ z : σ × Ω, f (z.1, H.unitIntervalCountPrefix n z.2) ∂(ρ.prod P)) * H.rate :=
      H.integral_externalUnitIntervalCountPrefixSelector_mul_nextUnitIntervalCount ρ n f hf
    _ = (ρ.prod P).real A * H.rate := by rw [hprefix]

/--
A measurable statistic of the unit-interval history before `n` factors from
the count in unit interval `n`.  This is the finite-grid predictable
compensation identity for forward Poisson counts.
-/
theorem integral_unitIntervalCountPrefixSelector_mul_nextUnitIntervalCount
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (n : ℕ) (f : (Finset.range n → ℕ) → ℝ) (hf : Measurable f) :
    ∫ omega, f (H.unitIntervalCountPrefix n omega) *
        (H.unitIntervalCount n omega : ℝ) ∂P =
      (∫ omega, f (H.unitIntervalCountPrefix n omega) ∂P) * H.rate := by
  have hraw := H.iIndepFun_unitIntervalCount.indepFun_finset
    (Finset.range n) ({n} : Finset ℕ) (by simp)
    (fun k => H.measurable_unitIntervalCount k)
  have hind : ProbabilityTheory.IndepFun
      (fun omega : Ω => f (H.unitIntervalCountPrefix n omega))
      (fun omega : Ω => (H.unitIntervalCount n omega : ℝ)) P := by
    simpa [unitIntervalCountPrefix, Function.comp_def] using hraw.comp hf
      ((measurable_of_countable fun k : ℕ => (k : ℝ)).comp
        (measurable_pi_apply ⟨n, Finset.mem_singleton_self n⟩))
  calc
    ∫ omega, f (H.unitIntervalCountPrefix n omega) *
        (H.unitIntervalCount n omega : ℝ) ∂P =
        (∫ omega, f (H.unitIntervalCountPrefix n omega) ∂P) *
          (∫ omega, (H.unitIntervalCount n omega : ℝ) ∂P) := by
      simpa using hind.integral_mul_eq_mul_integral
        (hf.comp (H.measurable_unitIntervalCountPrefix n)).aestronglyMeasurable
        ((measurable_of_countable fun k : ℕ => (k : ℝ)).comp
          (H.measurable_unitIntervalCount n)).aestronglyMeasurable
    _ = _ := by rw [H.unitIntervalCount_real_expectation_at n]

/--
A discrete stopping index whose strict-continuation event at unit interval
`n` is determined by the preceding unit-interval count history.
-/
structure UnitIntervalPredictableStoppingIndex
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P) where
  toFun : Ω → ℕ
  continuation_prefix_measurable : ∀ n,
    MeasurableSet[MeasurableSpace.comap (H.unitIntervalCountPrefix n) inferInstance]
      {omega | n < toFun omega}

namespace UnitIntervalPredictableStoppingIndex

instance (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P) :
    CoeFun (UnitIntervalPredictableStoppingIndex H) (fun _ => Ω → ℕ) :=
  ⟨UnitIntervalPredictableStoppingIndex.toFun⟩

/-- The event on which a unit-interval count is accrued before the index. -/
def continuationEvent
    {H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P}
    (tau : UnitIntervalPredictableStoppingIndex H) (n : ℕ) : Set Ω :=
  {omega | n < tau omega}

/-- Every predictable continuation event is Borel measurable. -/
theorem measurableSet_continuationEvent
    {H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P}
    (tau : UnitIntervalPredictableStoppingIndex H) (n : ℕ) :
    MeasurableSet (tau.continuationEvent n) := by
  rcases tau.continuation_prefix_measurable n with ⟨u, hu, hpre⟩
  change MeasurableSet {omega | n < tau omega}
  rw [← hpre]
  exact hu.preimage (H.measurable_unitIntervalCountPrefix n)

/-- The count accumulated strictly before a predictable index, capped at a
deterministic number of unit intervals. -/
def truncatedStrictStoppedUnitIntervalCount
    {H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P}
    (tau : UnitIntervalPredictableStoppingIndex H) (cap : ℕ) : Ω → ℝ :=
  fun omega => ∑ n ∈ Finset.range cap,
    if n < tau omega then (H.unitIntervalCount n omega : ℝ) else 0

/-- One predictable unit-interval count factors into continuation probability
and the Poisson rate. -/
theorem integral_continuationEvent_indicator_mul_unitIntervalCount
    {H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P}
    (tau : UnitIntervalPredictableStoppingIndex H) (n : ℕ) :
    ∫ omega, (tau.continuationEvent n).indicator (fun _ => (1 : ℝ)) omega *
        (H.unitIntervalCount n omega : ℝ) ∂P =
      P.real (tau.continuationEvent n) * H.rate := by
  rcases tau.continuation_prefix_measurable n with ⟨u, hu, hpre⟩
  let f : (Finset.range n → ℕ) → ℝ := u.indicator (fun _ => (1 : ℝ))
  have hf : Measurable f := measurable_const.indicator hu
  have hleft :
      (fun omega : Ω => f (H.unitIntervalCountPrefix n omega) *
          (H.unitIntervalCount n omega : ℝ)) =
        fun omega => (tau.continuationEvent n).indicator (fun _ => (1 : ℝ)) omega *
          (H.unitIntervalCount n omega : ℝ) := by
    funext omega
    have hmem : H.unitIntervalCountPrefix n omega ∈ u ↔
        omega ∈ tau.continuationEvent n := by
      change H.unitIntervalCountPrefix n omega ∈ u ↔ n < tau omega
      rw [← Set.mem_preimage, hpre]
      rfl
    by_cases h : H.unitIntervalCountPrefix n omega ∈ u
    · have hcont : omega ∈ tau.continuationEvent n := hmem.mp h
      simp [f, Set.indicator, h, hcont]
    · have hcont : omega ∉ tau.continuationEvent n := by
        intro h'
        exact h (hmem.mpr h')
      simp [f, Set.indicator, h, hcont]
  have hprefix :
      (∫ omega, f (H.unitIntervalCountPrefix n omega) ∂P) =
        P.real (tau.continuationEvent n) := by
    calc
      (∫ omega, f (H.unitIntervalCountPrefix n omega) ∂P) =
          ∫ omega, (tau.continuationEvent n).indicator (fun _ => (1 : ℝ)) omega ∂P := by
        apply integral_congr_ae
        filter_upwards [] with omega
        have hmem : H.unitIntervalCountPrefix n omega ∈ u ↔
            omega ∈ tau.continuationEvent n := by
          change H.unitIntervalCountPrefix n omega ∈ u ↔ n < tau omega
          rw [← Set.mem_preimage, hpre]
          rfl
        by_cases h : H.unitIntervalCountPrefix n omega ∈ u
        · have hcont : omega ∈ tau.continuationEvent n := hmem.mp h
          simp [f, Set.indicator, h, hcont]
        · have hcont : omega ∉ tau.continuationEvent n := by
            intro h'
            exact h (hmem.mpr h')
          simp [f, Set.indicator, h, hcont]
      _ = P.real (tau.continuationEvent n) := by
        rw [MeasureTheory.integral_indicator (tau.measurableSet_continuationEvent n),
          MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
  calc
    ∫ omega, (tau.continuationEvent n).indicator (fun _ => (1 : ℝ)) omega *
        (H.unitIntervalCount n omega : ℝ) ∂P =
        ∫ omega, f (H.unitIntervalCountPrefix n omega) *
          (H.unitIntervalCount n omega : ℝ) ∂P := by rw [hleft]
    _ = (∫ omega, f (H.unitIntervalCountPrefix n omega) ∂P) * H.rate :=
      H.integral_unitIntervalCountPrefixSelector_mul_nextUnitIntervalCount n f hf
    _ = P.real (tau.continuationEvent n) * H.rate := by rw [hprefix]

/-- Finite predictable compensation for the count accrued before a unit-grid
stopping index. -/
theorem integral_truncatedStrictStoppedUnitIntervalCount
    {H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P}
    (tau : UnitIntervalPredictableStoppingIndex H) (cap : ℕ) :
    ∫ omega, tau.truncatedStrictStoppedUnitIntervalCount cap omega ∂P =
      (∑ n ∈ Finset.range cap, P.real (tau.continuationEvent n)) * H.rate := by
  change ∫ omega, (∑ n ∈ Finset.range cap,
      if n < tau omega then (H.unitIntervalCount n omega : ℝ) else 0) ∂P = _
  have hintegrable : ∀ n ∈ Finset.range cap,
      Integrable (fun omega : Ω =>
        if n < tau omega then (H.unitIntervalCount n omega : ℝ) else 0) P := by
    intro n hn
    have hterm :
        (fun omega : Ω => if n < tau omega then (H.unitIntervalCount n omega : ℝ) else 0) =
          fun omega => (tau.continuationEvent n).indicator (fun _ => (1 : ℝ)) omega *
            (H.unitIntervalCount n omega : ℝ) := by
      funext omega
      by_cases h : n < tau omega
      · simp [continuationEvent, Set.indicator, h]
      · simp [continuationEvent, Set.indicator, h]
    rw [hterm]
    have hindicator :
        (fun omega : Ω => (tau.continuationEvent n).indicator (fun _ => (1 : ℝ)) omega *
          (H.unitIntervalCount n omega : ℝ)) =
          (tau.continuationEvent n).indicator
            (fun omega => (H.unitIntervalCount n omega : ℝ)) := by
      funext omega
      by_cases h : omega ∈ tau.continuationEvent n <;> simp [Set.indicator, h]
    rw [hindicator]
    exact (H.unitIntervalCount_real_integrable_at n).indicator
      (tau.measurableSet_continuationEvent n)
  rw [MeasureTheory.integral_finset_sum (Finset.range cap) hintegrable, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  have hterm :
      (fun omega : Ω => if n < tau omega then (H.unitIntervalCount n omega : ℝ) else 0) =
        fun omega => (tau.continuationEvent n).indicator (fun _ => (1 : ℝ)) omega *
          (H.unitIntervalCount n omega : ℝ) := by
    funext omega
    by_cases h : n < tau omega
    · have hmem : omega ∈ tau.continuationEvent n := h
      simp [continuationEvent, Set.indicator, h]
    · have hmem : omega ∉ tau.continuationEvent n := h
      simp [continuationEvent, Set.indicator, h]
  rw [hterm, tau.integral_continuationEvent_indicator_mul_unitIntervalCount]

end UnitIntervalPredictableStoppingIndex

/-- Pairwise independence form used by the strong-law interface. -/
theorem pairwise_indepFun_unitIntervalCount
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P) :
    Pairwise (fun i j => ProbabilityTheory.IndepFun
      (H.unitIntervalCount i) (H.unitIntervalCount j) P) := by
  intro i j hij
  exact H.iIndepFun_unitIntervalCount.indepFun hij

/-- Unit-width forward increments are identically distributed. -/
theorem unitIntervalCount_identDistrib
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (n : ℕ) :
    ProbabilityTheory.IdentDistrib (H.unitIntervalCount n)
      (H.unitIntervalCount 0) P P :=
  (H.unitIntervalCount_hasLaw n).identDistrib
    (H.unitIntervalCount_hasLaw 0)

/-- The real-valued unit counts retain pairwise independence. -/
theorem pairwise_indepFun_unitIntervalCount_real
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P) :
    Pairwise (fun i j => ProbabilityTheory.IndepFun
      (fun omega => (H.unitIntervalCount i omega : ℝ))
      (fun omega => (H.unitIntervalCount j omega : ℝ)) P) := by
  intro i j hij
  simpa only [Function.comp_apply] using
    (H.pairwise_indepFun_unitIntervalCount hij).comp
      (measurable_of_countable fun n : ℕ => (n : ℝ))
      (measurable_of_countable fun n : ℕ => (n : ℝ))

/-- The real-valued unit counts retain their common distribution. -/
theorem unitIntervalCount_real_identDistrib
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P)
    (n : ℕ) :
    ProbabilityTheory.IdentDistrib
      (fun omega => (H.unitIntervalCount n omega : ℝ))
      (fun omega => (H.unitIntervalCount 0 omega : ℝ)) P P := by
  simpa only [Function.comp_apply] using
    (H.unitIntervalCount_identDistrib n).comp
      (measurable_of_countable fun k : ℕ => (k : ℝ))

/-- The real-valued first unit count is integrable. -/
theorem unitIntervalCount_real_integrable
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P) :
    Integrable (fun omega => (H.unitIntervalCount 0 omega : ℝ)) P := by
  let r : ℝ≥0 := rateExposureParam H.rate 1 (by simpa using H.rate_nonneg)
  have hint : Integrable (fun n : ℕ => (n : ℝ))
      (ProbabilityTheory.poissonMeasure r) :=
    integrable_natCast_poissonMeasure r
  have hmap : Integrable (fun n : ℕ => (n : ℝ))
      (Measure.map (H.unitIntervalCount 0) P) := by
    rw [(H.unitIntervalCount_hasLaw 0).map_eq]
    exact hint
  simpa [Function.comp_def] using
    hmap.comp_aemeasurable (H.unitIntervalCount_hasLaw 0).aemeasurable

/-- The expected count in a unit-width forward interval is the process rate. -/
theorem unitIntervalCount_real_expectation
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P) :
    ∫ omega, (H.unitIntervalCount 0 omega : ℝ) ∂P = H.rate := by
  let r : ℝ≥0 := rateExposureParam H.rate 1 (by simpa using H.rate_nonneg)
  calc
    ∫ omega, (H.unitIntervalCount 0 omega : ℝ) ∂P =
        ∫ n : ℕ, (n : ℝ) ∂ProbabilityTheory.poissonMeasure r := by
      simpa [r, Function.comp_def] using
        (H.unitIntervalCount_hasLaw 0).integral_comp
          (f := fun n : ℕ => (n : ℝ))
          (measurable_of_countable _).aestronglyMeasurable
    _ = r := integral_id_poissonMeasure r
    _ = H.rate := by
      change H.rate * 1 = H.rate
      ring

/-- Forward unit-interval counts obey the almost-sure strong law. -/
theorem unitIntervalCount_real_strongLaw
    (H : ForwardHomogeneousPoissonCountingProcessByLaw Ω P) :
    ∀ᵐ omega ∂P,
      Tendsto (fun n : ℕ =>
        (∑ i ∈ Finset.range n, (H.unitIntervalCount i omega : ℝ)) / n)
        atTop (nhds H.rate) := by
  have hsl := ProbabilityTheory.strong_law_ae_real
    (fun i omega => (H.unitIntervalCount i omega : ℝ))
    H.unitIntervalCount_real_integrable
    H.pairwise_indepFun_unitIntervalCount_real
    H.unitIntervalCount_real_identDistrib
  simpa [H.unitIntervalCount_real_expectation] using hsl

end ForwardHomogeneousPoissonCountingProcessByLaw

end

end PoissonProcess
end Probability
end AppliedModelingLib

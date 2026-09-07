import AppliedModelingLib.Foundations.Probability.PoissonStopping
import Mathlib.Probability.Independence.InfinitePi

/-!
# Canonical exponential-interarrival first-arrival path

This module constructs the first-arrival component of a homogeneous Poisson
process on the countable product of exponential interarrival coordinates.  It
does not yet prove the full all-times renewal count process has independent
Poisson increments; that is a separate nonexplosion/renewal theorem.
-/

namespace AppliedModelingLib
namespace Probability
namespace PoissonProcess

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

/-- Canonical countable product law of iid exponential interarrival coordinates. -/
def exponentialInterarrivalMeasure (rate : ℝ) : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => ProbabilityTheory.expMeasure rate)

/-- The canonical interarrival product law is a probability measure at positive rate. -/
theorem isProbabilityMeasure_exponentialInterarrivalMeasure
    {rate : ℝ} (hrate : 0 < rate) :
    IsProbabilityMeasure (exponentialInterarrivalMeasure rate) := by
  letI : ∀ i : ℕ, IsProbabilityMeasure (ProbabilityTheory.expMeasure rate) :=
    fun _ => ProbabilityTheory.isProbabilityMeasure_expMeasure hrate
  simpa [exponentialInterarrivalMeasure] using
    (inferInstance :
      IsProbabilityMeasure
        (Measure.infinitePi (fun _ : ℕ => ProbabilityTheory.expMeasure rate)))

/-- The `n`th coordinate of a canonical path is its `n`th interarrival time. -/
def interarrival (n : ℕ) : (ℕ → ℝ) → ℝ :=
  fun ω => ω n

/-- Each canonical interarrival coordinate is Borel measurable. -/
theorem measurable_interarrival (n : ℕ) : Measurable (interarrival n) := by
  simpa [interarrival] using
    (measurable_pi_apply n : Measurable (fun ω : ℕ → ℝ => ω n))

/-- Each canonical interarrival coordinate has the stated exponential law. -/
theorem interarrival_hasLaw
    {rate : ℝ} (hrate : 0 < rate) (n : ℕ) :
    ProbabilityTheory.HasLaw (interarrival n)
      (ProbabilityTheory.expMeasure rate) (exponentialInterarrivalMeasure rate) := by
  exact (@measurePreserving_eval_infinitePi ℕ (fun _ : ℕ => ℝ)
    (fun _ => inferInstance)
      (fun _ : ℕ => ProbabilityTheory.expMeasure rate)
      (fun _ => ProbabilityTheory.isProbabilityMeasure_expMeasure hrate) n).hasLaw

/--
For a canonical rate-`rate` exponential interarrival path, converting one time
gap to service units by multiplying by `rate` gives the unit-rate exponential
tail.
-/
theorem interarrival_rate_mul_tail_toReal
    {rate : ℝ} (hrate : 0 < rate) (n : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    (exponentialInterarrivalMeasure rate).real
      {ω | z < rate * interarrival n ω} = Real.exp (-z) := by
  have hmeas : MeasurableSet {x : ℝ | z < rate * x} := by
    exact measurableSet_Ioi.preimage (measurable_const.mul measurable_id)
  let M : Exponential.Model := ⟨rate, hrate⟩
  calc
    (exponentialInterarrivalMeasure rate).real
        {ω | z < rate * interarrival n ω} =
        (Measure.map (interarrival n) (exponentialInterarrivalMeasure rate)).real
          {x : ℝ | z < rate * x} := by
            change ((exponentialInterarrivalMeasure rate)
              ((interarrival n) ⁻¹' {x : ℝ | z < rate * x})).toReal =
              ((Measure.map (interarrival n) (exponentialInterarrivalMeasure rate))
                {x : ℝ | z < rate * x}).toReal
            rw [Measure.map_apply (measurable_interarrival n) hmeas]
    _ = M.measure.real {x : ℝ | z < M.rate * x} := by
          rw [(interarrival_hasLaw hrate n).map_eq]
          simp [M, Exponential.Model.measure]
    _ = Real.exp (-z) := by
          simpa [M] using M.measure_rate_mul_Ioi_toReal hz

/-- The canonical interarrival coordinates are mutually independent. -/
theorem iIndepFun_interarrival
    {rate : ℝ} (hrate : 0 < rate) :
    ProbabilityTheory.iIndepFun interarrival (exponentialInterarrivalMeasure rate) := by
  simpa [interarrival] using
    (@ProbabilityTheory.iIndepFun_infinitePi ℕ (fun _ : ℕ => ℝ)
      (fun _ => inferInstance) (fun _ : ℕ => ℝ) (fun _ => inferInstance)
      (fun _ : ℕ => ProbabilityTheory.expMeasure rate)
      (fun _ => ProbabilityTheory.isProbabilityMeasure_expMeasure hrate)
      (fun _ : ℕ => id) (fun _ => measurable_id))

/-- At positive rate, every canonical interarrival coordinate is nonnegative almost surely. -/
theorem ae_all_interarrival_nonnegative
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᵐ ω ∂exponentialInterarrivalMeasure rate, ∀ n : ℕ, 0 ≤ interarrival n ω := by
  rw [ae_all_iff]
  intro n
  have hp : Measurable (fun x : ℝ => 0 ≤ x) := by fun_prop
  let M : Exponential.Model := Exponential.Model.mk rate hrate
  exact ((interarrival_hasLaw hrate n).ae_iff hp).2 (by
    simpa [Filter.EventuallyLE, M] using M.ae_nonnegative)

/-- At positive rate, every canonical interarrival coordinate is strictly positive almost surely. -/
theorem ae_all_interarrival_positive
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᵐ ω ∂exponentialInterarrivalMeasure rate, ∀ n : ℕ, 0 < interarrival n ω := by
  rw [ae_all_iff]
  intro n
  have hp : Measurable (fun x : ℝ => 0 < x) := by fun_prop
  let M : Exponential.Model := Exponential.Model.mk rate hrate
  exact ((interarrival_hasLaw hrate n).ae_iff hp).2 (by
    rw [MeasureTheory.ae_iff]
    simpa [Set.compl_setOf, M] using M.measure_Iic_zero)

/--
Arrival time of the `(n+1)`st canonical renewal arrival, as a finite sum of
the first `n + 1` interarrival coordinates.  This finite-sum layer does not
yet assert nonexplosion or construct the full all-times renewal count process.
-/
def arrivalTime (n : ℕ) : (ℕ → ℝ) → ℝ :=
  fun ω => ∑ i ∈ Finset.range (n + 1), interarrival i ω

/-- Each finite canonical arrival time is Borel measurable. -/
theorem measurable_arrivalTime (n : ℕ) : Measurable (arrivalTime n) := by
  exact (Finset.range (n + 1)).measurable_sum fun i _ => measurable_interarrival i

/-- The first finite-sum arrival time is the first interarrival coordinate. -/
theorem arrivalTime_zero : arrivalTime 0 = interarrival 0 := by
  funext ω
  simp [arrivalTime]

/-- Nonnegative interarrivals make every finite arrival time nonnegative. -/
theorem arrivalTime_nonnegative_of_interarrival_nonnegative
    (ω : ℕ → ℝ) (hω : ∀ i : ℕ, 0 ≤ interarrival i ω) :
    ∀ n : ℕ, 0 ≤ arrivalTime n ω := by
  intro n
  unfold arrivalTime
  exact Finset.sum_nonneg fun i _ => hω i

/-- Canonical finite arrival times are almost surely nonnegative at positive rate. -/
theorem ae_all_arrivalTime_nonnegative
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᵐ ω ∂exponentialInterarrivalMeasure rate,
      ∀ n : ℕ, 0 ≤ arrivalTime n ω :=
  (ae_all_interarrival_nonnegative hrate).mono
    (fun ω hω => arrivalTime_nonnegative_of_interarrival_nonnegative ω hω)

/-- Nonnegative interarrivals make finite arrival times monotone in the job index. -/
theorem arrivalTime_mono_of_nonnegative
    (ω : ℕ → ℝ) (hω : ∀ i : ℕ, 0 ≤ interarrival i ω) :
    Monotone (fun n : ℕ => arrivalTime n ω) := by
  intro n m hnm
  unfold arrivalTime
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · exact Finset.range_subset_range.mpr (Nat.succ_le_succ hnm)
  · intro i _hi _hnot
    exact hω i

/-- Canonical finite arrival times are almost surely monotone at positive rate. -/
theorem ae_arrivalTime_monotone
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᵐ ω ∂exponentialInterarrivalMeasure rate,
      Monotone (fun n : ℕ => arrivalTime n ω) :=
  (ae_all_interarrival_nonnegative hrate).mono
    (fun ω hω => arrivalTime_mono_of_nonnegative ω hω)

/-- Strictly positive interarrivals make finite arrival times strictly increasing. -/
theorem arrivalTime_strictMono_of_positive
    (ω : ℕ → ℝ) (hω : ∀ i : ℕ, 0 < interarrival i ω) :
    StrictMono (fun n : ℕ => arrivalTime n ω) := by
  intro n m hnm
  have hmono : Monotone (fun j : ℕ => arrivalTime j ω) :=
    arrivalTime_mono_of_nonnegative ω (fun i => (hω i).le)
  calc
    arrivalTime n ω < arrivalTime n ω + interarrival (n + 1) ω :=
      lt_add_of_pos_right _ (hω (n + 1))
    _ = arrivalTime (n + 1) ω := by
      simp [arrivalTime, Finset.sum_range_succ]
    _ ≤ arrivalTime m ω := hmono (Nat.succ_le_iff.mpr hnm)

/-- Strictly positive interarrivals make every finite arrival time positive. -/
theorem arrivalTime_positive_of_interarrival_positive
    (ω : ℕ → ℝ) (hω : ∀ i : ℕ, 0 < interarrival i ω) :
    ∀ n : ℕ, 0 < arrivalTime n ω := by
  intro n
  cases n with
  | zero =>
      simpa [arrivalTime_zero] using hω 0
  | succ n =>
      have hstrict : StrictMono (fun m : ℕ => arrivalTime m ω) :=
        arrivalTime_strictMono_of_positive ω hω
      exact lt_trans (by simpa [arrivalTime_zero] using hω 0)
        (hstrict (Nat.succ_pos n))

/-- Canonical finite arrival times are almost surely positive at positive rate. -/
theorem ae_all_arrivalTime_positive
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᵐ ω ∂exponentialInterarrivalMeasure rate,
      ∀ n : ℕ, 0 < arrivalTime n ω :=
  (ae_all_interarrival_positive hrate).mono
    (fun ω hω => arrivalTime_positive_of_interarrival_positive ω hω)

/-- Canonical finite arrival times are almost surely strictly increasing at positive rate. -/
theorem ae_arrivalTime_strictMono
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᵐ ω ∂exponentialInterarrivalMeasure rate,
      StrictMono (fun n : ℕ => arrivalTime n ω) :=
  (ae_all_interarrival_positive hrate).mono
    (fun ω hω => arrivalTime_strictMono_of_positive ω hω)

/--
One-sided post-tag arrival epochs on the canonical path: index zero is the
tagged arrival at time zero and successors are the finite-sum future arrivals.
This does not provide the negative-time half of a stationary Palm point
configuration.
-/
def postTagArrival : ℕ → (ℕ → ℝ) → ℝ
  | 0, _ => 0
  | m + 1, ω => arrivalTime m ω

/-- The canonical post-tag sequence places the tag exactly at the origin. -/
theorem postTagArrival_zero : postTagArrival 0 = fun _ : ℕ → ℝ => 0 :=
  rfl

/-- Successor post-tag epochs are the corresponding finite-sum future arrivals. -/
theorem postTagArrival_succ (n : ℕ) : postTagArrival (n + 1) = arrivalTime n :=
  rfl

/-- Each one-sided post-tag arrival epoch is Borel measurable. -/
theorem measurable_postTagArrival (n : ℕ) : Measurable (postTagArrival n) := by
  cases n with
  | zero =>
      change Measurable (fun _ : ℕ → ℝ => (0 : ℝ))
      fun_prop
  | succ n => simpa [postTagArrival] using measurable_arrivalTime n

/-- A positive interarrival path gives strictly ordered one-sided post-tag arrivals. -/
theorem postTagArrival_strictMono_of_positive
    (ω : ℕ → ℝ) (hω : ∀ i : ℕ, 0 < interarrival i ω) :
    StrictMono (fun n : ℕ => postTagArrival n ω) := by
  intro n m hnm
  cases n with
  | zero =>
      cases m with
      | zero => exact (Nat.lt_irrefl _ hnm).elim
      | succ m =>
          change 0 < arrivalTime m ω
          have hmono : Monotone (fun j : ℕ => arrivalTime j ω) :=
            arrivalTime_mono_of_nonnegative ω (fun i => (hω i).le)
          calc
            0 < interarrival 0 ω := hω 0
            _ = arrivalTime 0 ω := by simp [arrivalTime]
            _ ≤ arrivalTime m ω := hmono (Nat.zero_le _)
  | succ n =>
      cases m with
      | zero => exact (Nat.not_lt_zero _ hnm).elim
      | succ m =>
          change arrivalTime n ω < arrivalTime m ω
          exact arrivalTime_strictMono_of_positive ω hω (Nat.succ_lt_succ_iff.mp hnm)

/-- One-sided post-tag epochs are almost surely strictly ordered at positive rate. -/
theorem ae_postTagArrival_strictMono
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᵐ ω ∂exponentialInterarrivalMeasure rate,
      StrictMono (fun n : ℕ => postTagArrival n ω) :=
  (ae_all_interarrival_positive hrate).mono
    (fun ω hω => postTagArrival_strictMono_of_positive ω hω)

/-- First arrival time on the canonical interarrival product path. -/
def canonicalFirstArrival : (ℕ → ℝ) → ℝ :=
  interarrival 0

/-- The distinguished first arrival agrees with the finite-sum representation. -/
theorem canonicalFirstArrival_eq_arrivalTime_zero :
    canonicalFirstArrival = arrivalTime 0 := by
  simpa [canonicalFirstArrival] using arrivalTime_zero.symm

/-- The first canonical arrival has the exponential law. -/
theorem canonicalFirstArrival_hasLaw
    {rate : ℝ} (hrate : 0 < rate) :
    ProbabilityTheory.HasLaw canonicalFirstArrival
      (ProbabilityTheory.expMeasure rate) (exponentialInterarrivalMeasure rate) := by
  simpa [canonicalFirstArrival] using interarrival_hasLaw hrate 0

/--
One-jump count process that records whether the canonical first arrival has
occurred by time `t`.  This is intentionally only the first-arrival component,
not the full Poisson renewal count process.
-/
def canonicalFirstArrivalCount (t : ℝ) : (ℕ → ℝ) → ℕ :=
  fun ω => if canonicalFirstArrival ω ≤ t then 1 else 0

/-- Each first-arrival count coordinate is Borel measurable. -/
theorem measurable_canonicalFirstArrivalCount (t : ℝ) :
    Measurable (canonicalFirstArrivalCount t) := by
  unfold canonicalFirstArrivalCount canonicalFirstArrival interarrival
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_le (measurable_pi_apply 0) measurable_const

/-- Natural continuous-time filtration of the first-arrival indicator process. -/
noncomputable def canonicalFirstArrivalFiltration :
    Filtration (Ω := ℕ → ℝ) ℝ inferInstance :=
  Filtration.natural canonicalFirstArrivalCount
    (fun t => (measurable_canonicalFirstArrivalCount t).stronglyMeasurable)

/-- The first-arrival indicator process is adapted to its natural filtration. -/
theorem canonicalFirstArrivalCount_adapted :
    Adapted canonicalFirstArrivalFiltration canonicalFirstArrivalCount := by
  unfold canonicalFirstArrivalFiltration
  exact (Filtration.stronglyAdapted_natural
    (fun t => (measurable_canonicalFirstArrivalCount t).stronglyMeasurable)).adapted

/-- The canonical first arrival has exactly the count-threshold level sets. -/
theorem canonicalFirstArrival_level_sets (t : ℝ) :
    {ω | canonicalFirstArrival ω ≤ t} =
      {ω | 1 ≤ canonicalFirstArrivalCount t ω} := by
  ext ω
  by_cases h : canonicalFirstArrival ω ≤ t
  · simp [canonicalFirstArrivalCount, h]
  · simp [canonicalFirstArrivalCount, h]

/-- Concrete first-arrival stopping certificate on the canonical path space. -/
def canonicalFirstArrivalCertificate :
    FirstCountArrivalCertificate canonicalFirstArrivalFiltration
      canonicalFirstArrivalCount canonicalFirstArrival where
  count_event_adapted :=
    CountThresholdEventAdapted.of_adapted canonicalFirstArrivalCount_adapted
  level_sets := canonicalFirstArrival_level_sets

/-- The concrete canonical first arrival is a native Mathlib stopping time. -/
theorem canonicalFirstArrival_isStoppingTime :
    MeasureTheory.IsStoppingTime canonicalFirstArrivalFiltration
      (toNativeStoppingTime canonicalFirstArrival) :=
  canonicalFirstArrivalCertificate.isStoppingTime_native

/-- The same concrete first arrival viewed as an extended-valued random time. -/
def canonicalFirstArrivalWithTop : (ℕ → ℝ) → WithTop ℝ :=
  toNativeStoppingTime canonicalFirstArrival

/-- The extended-valued first arrival has the same threshold-event semantics. -/
theorem canonicalFirstArrivalWithTop_level_sets (t : ℝ) :
    {ω | canonicalFirstArrivalWithTop ω ≤ t} =
      {ω | 1 ≤ canonicalFirstArrivalCount t ω} := by
  simpa [canonicalFirstArrivalWithTop, toNativeStoppingTime] using
    canonicalFirstArrival_level_sets t

/-- Native `WithTop` certificate for the concrete canonical first arrival. -/
def canonicalFirstArrivalWithTopCertificate :
    FirstCountArrivalWithTopCertificate canonicalFirstArrivalFiltration
      canonicalFirstArrivalCount canonicalFirstArrivalWithTop where
  count_event_adapted :=
    CountThresholdEventAdapted.of_adapted canonicalFirstArrivalCount_adapted
  level_sets := canonicalFirstArrivalWithTop_level_sets

/-- The extended canonical first arrival is a native Mathlib stopping time. -/
theorem canonicalFirstArrivalWithTop_isStoppingTime :
    MeasureTheory.IsStoppingTime canonicalFirstArrivalFiltration
      canonicalFirstArrivalWithTop :=
  canonicalFirstArrivalWithTopCertificate.isStoppingTime

end
end PoissonProcess
end Probability
end AppliedModelingLib

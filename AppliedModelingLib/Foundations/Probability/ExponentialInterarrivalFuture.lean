import AppliedModelingLib.Foundations.Probability.ExponentialInterarrival

/-!
# Deterministic future tails of canonical exponential interarrival paths

This module proves deterministic-index regeneration for the iid exponential
product path and makes each such next-gap time a native stopping time for its
one-jump natural filtration.  It deliberately stops before a random-index
strong-Markov regeneration theorem or nonexplosion proof.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

/-- The deterministic `n`-step future interarrival path. -/
def futureInterarrival (n : ℕ) : (ℕ → ℝ) → ℕ → ℝ :=
  fun ω k => interarrival (n + k) ω

theorem measurable_futureInterarrival (n k : ℕ) :
    Measurable (fun ω : ℕ → ℝ => futureInterarrival n ω k) := by
  simpa [futureInterarrival] using measurable_interarrival (n + k)

theorem futureInterarrival_hasLaw {rate : ℝ} (hrate : 0 < rate)
    (n k : ℕ) :
    ProbabilityTheory.HasLaw (fun ω : ℕ → ℝ => futureInterarrival n ω k)
      (ProbabilityTheory.expMeasure rate) (exponentialInterarrivalMeasure rate) := by
  simpa [futureInterarrival] using interarrival_hasLaw hrate (n + k)

theorem iIndepFun_futureInterarrival {rate : ℝ} (hrate : 0 < rate) (n : ℕ) :
    ProbabilityTheory.iIndepFun (fun k ω => futureInterarrival n ω k)
      (exponentialInterarrivalMeasure rate) := by
  simpa [futureInterarrival] using
    (ProbabilityTheory.iIndepFun.precomp (g := fun k : ℕ => n + k)
      (by intro a b h; exact Nat.add_left_cancel h)
      (iIndepFun_interarrival hrate))

/-- Every deterministic future tail has the same iid exponential product law. -/
theorem futureInterarrival_hasLaw_path {rate : ℝ} (hrate : 0 < rate) (n : ℕ) :
    ProbabilityTheory.HasLaw (futureInterarrival n)
      (exponentialInterarrivalMeasure rate) (exponentialInterarrivalMeasure rate) := by
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  refine ⟨(measurable_pi_iff.2 (fun k => measurable_futureInterarrival n k)).aemeasurable, ?_⟩
  rw [ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun k => measurable_futureInterarrival n k) |>.mp
    (iIndepFun_futureInterarrival hrate n)]
  simp only [exponentialInterarrivalMeasure]
  congr 1
  funext k
  exact (futureInterarrival_hasLaw hrate n k).map_eq

/-- Sum of the first `n` interarrival coordinates, before the `n`th future gap. -/
def arrivalPrefix (n : ℕ) : (ℕ → ℝ) → ℝ :=
  fun ω => ∑ i ∈ Finset.range n, interarrival i ω

/-- Finite arrival time measured from a deterministic future coordinate. -/
def futureArrivalTime (n m : ℕ) : (ℕ → ℝ) → ℝ :=
  fun ω => ∑ i ∈ Finset.range (m + 1), futureInterarrival n ω i

theorem futureArrivalTime_eq_arrivalTime_tail (n m : ℕ) :
    futureArrivalTime n m = fun ω => arrivalTime m (futureInterarrival n ω) := by
  funext ω
  simp [futureArrivalTime, arrivalTime, futureInterarrival, interarrival]

/-- A deterministic cut of the renewal path decomposes the later arrival epoch exactly. -/
theorem arrivalTime_add_eq_arrivalPrefix_add_futureArrivalTime (n m : ℕ) :
    arrivalTime (n + m) =
      fun ω => arrivalPrefix n ω + futureArrivalTime n m ω := by
  funext ω
  simp only [arrivalTime, arrivalPrefix, futureArrivalTime, futureInterarrival]
  rw [show n + m + 1 = n + (m + 1) by omega, Finset.sum_range_add]

/-- A finite future arrival epoch has the same law as the corresponding epoch from a fresh path. -/
theorem futureArrivalTime_hasLaw {rate : ℝ} (hrate : 0 < rate) (n m : ℕ) :
    ProbabilityTheory.HasLaw (futureArrivalTime n m)
      ((exponentialInterarrivalMeasure rate).map (arrivalTime m))
      (exponentialInterarrivalMeasure rate) := by
  have hFresh : ProbabilityTheory.HasLaw (arrivalTime m)
      ((exponentialInterarrivalMeasure rate).map (arrivalTime m))
      (exponentialInterarrivalMeasure rate) := by
    exact ⟨(measurable_arrivalTime m).aemeasurable, rfl⟩
  simpa only [futureArrivalTime_eq_arrivalTime_tail, Function.comp_apply] using
    hFresh.comp (futureInterarrival_hasLaw_path hrate n)

namespace OneJump

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The count process that jumps from zero to one at a given measurable time. -/
def count (X : Ω → ℝ) (t : ℝ) : Ω → ℕ :=
  fun ω => if X ω ≤ t then 1 else 0

theorem measurable_count (X : Ω → ℝ) (hX : Measurable X) (t : ℝ) :
    Measurable (count X t) := by
  unfold count
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_le hX measurable_const

/-- The natural filtration of the one-jump threshold process. -/
noncomputable def filtration (X : Ω → ℝ) (hX : Measurable X) :
    Filtration (Ω := Ω) ℝ inferInstance :=
  Filtration.natural (count X) (fun t => (measurable_count X hX t).stronglyMeasurable)

theorem count_adapted (X : Ω → ℝ) (hX : Measurable X) :
    Adapted (filtration X hX) (count X) := by
  unfold filtration
  exact (Filtration.stronglyAdapted_natural
    (fun t => (measurable_count X hX t).stronglyMeasurable)).adapted

omit [MeasurableSpace Ω] in
theorem level_sets (X : Ω → ℝ) (t : ℝ) :
    {ω | X ω ≤ t} = {ω | 1 ≤ count X t ω} := by
  ext ω
  by_cases h : X ω ≤ t <;> simp [count, h]

def certificate (X : Ω → ℝ) (hX : Measurable X) :
    FirstCountArrivalCertificate (filtration X hX) (count X) X where
  count_event_adapted := CountThresholdEventAdapted.of_adapted (count_adapted X hX)
  level_sets := level_sets X

theorem isStoppingTime (X : Ω → ℝ) (hX : Measurable X) :
    MeasureTheory.IsStoppingTime (filtration X hX) (toNativeStoppingTime X) :=
  (certificate X hX).isStoppingTime_native

end OneJump

/-- The first gap after every deterministic interarrival index is a native stopping time. -/
theorem futureFirstArrival_isStoppingTime (n : ℕ) :
    MeasureTheory.IsStoppingTime
      (OneJump.filtration (futureInterarrival n · 0)
        (measurable_futureInterarrival n 0))
      (toNativeStoppingTime (futureInterarrival n · 0)) :=
  OneJump.isStoppingTime (futureInterarrival n · 0)
    (measurable_futureInterarrival n 0)

end
end AppliedModelingLib.Probability.PoissonProcess

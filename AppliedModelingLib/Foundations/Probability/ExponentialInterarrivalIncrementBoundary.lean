import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalRenewalCountMarginal
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalPostArrival

/-!
# Residual-tail boundary for deterministic renewal-count increments

This module proves the exact path algebra for a deterministic clock-time
increment of the canonical renewal count. The remaining stochastic statement
is isolated to one hypothesis: the residual tail that starts inside the
straddling interarrival gap has the fresh iid-exponential law. Existing
finite-block stopped regeneration starts after that gap and does not prove
this residual-memorylessness fact.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory Filter
open scoped ENNReal NNReal ProbabilityTheory

noncomputable section

/--
Interarrival path seen from deterministic time `s`: its first coordinate is
the residual to the next renewal and later coordinates are the uninspected
interarrivals.
-/
def residualTail (s : ℝ) (ω : ℕ → ℝ) : ℕ → ℝ
  | 0 => arrivalTime (canonicalRenewalCount s ω) ω - s
  | k + 1 => interarrival (canonicalRenewalCount s ω + (k + 1)) ω

/--
The local memoryless calculation for a deterministic straddling gap. A proof
of clock-time residual-tail regeneration must sum this factorization over the
random index of the gap that straddles the clock; this lemma deliberately does
not pretend to handle that random index itself.
-/
theorem interarrival_residual_tail_real
    {rate s h : ℝ} (hrate : 0 < rate) (n : ℕ) (hs : 0 ≤ s) (hh : 0 ≤ h) :
    (exponentialInterarrivalMeasure rate).real
        {ω | s < interarrival n ω ∧ h < interarrival n ω - s} =
      (ProbabilityTheory.expMeasure rate).real (Set.Ioi s) *
        (ProbabilityTheory.expMeasure rate).real (Set.Ioi h) := by
  let M : Exponential.Model := ⟨rate, hrate⟩
  let A : Set ℝ := {x | s < x ∧ h < x - s}
  have hA : MeasurableSet A := by
    exact (measurableSet_lt measurable_const measurable_id).inter
      (measurableSet_lt measurable_const (measurable_id.sub_const s))
  calc
    (exponentialInterarrivalMeasure rate).real
        {ω | s < interarrival n ω ∧ h < interarrival n ω - s} =
        (exponentialInterarrivalMeasure rate).real (interarrival n ⁻¹' A) := by
          rfl
    _ = ((exponentialInterarrivalMeasure rate).map (interarrival n)).real A := by
          symm
          exact congrArg ENNReal.toReal
            (Measure.map_apply (measurable_interarrival n) hA)
    _ = (ProbabilityTheory.expMeasure rate).real A := by
          rw [(interarrival_hasLaw hrate n).map_eq]
    _ = (ProbabilityTheory.expMeasure rate).real (Set.Ioi s) *
          (ProbabilityTheory.expMeasure rate).real (Set.Ioi h) := by
          simpa [A, M, Exponential.Model.measure] using
            M.measure_residual_tail_toReal hs hh

theorem arrivalTime_residualTail
    (s : ℝ) (ω : ℕ → ℝ) (m : ℕ) :
    arrivalTime m (residualTail s ω) =
      arrivalTime (canonicalRenewalCount s ω + m) ω - s := by
  induction m with
  | zero =>
      simp [arrivalTime, residualTail, interarrival]
  | succ m ih =>
      have htail :
          arrivalTime (m + 1) (residualTail s ω) =
            arrivalTime m (residualTail s ω) +
              interarrival (m + 1) (residualTail s ω) := by
        simp [arrivalTime, Finset.sum_range_succ, Nat.add_assoc]
      have horig :
          arrivalTime (canonicalRenewalCount s ω + (m + 1)) ω =
            arrivalTime (canonicalRenewalCount s ω + m) ω +
              interarrival (canonicalRenewalCount s ω + (m + 1)) ω := by
        unfold arrivalTime
        have hidx : canonicalRenewalCount s ω + (m + 1) =
            canonicalRenewalCount s ω + m + 1 := by omega
        rw [hidx, Finset.sum_range_succ]
      rw [htail, ih, horig]
      simp [residualTail, interarrival]
      ring

/--
Pathwise time-shift identity, assuming the original and residual paths have
future arrivals. Thus the remaining stochastic seam is the law of
`residualTail`, not the count algebra.
-/
theorem canonicalRenewalCount_add_eq_residualTailCount
    (s h : ℝ) (hh : 0 ≤ h) (ω : ℕ → ℝ)
    (hS : ∃ n : ℕ, s < arrivalTime n ω)
    (hSH : ∃ n : ℕ, s + h < arrivalTime n ω)
    (hTail : ∃ m : ℕ, h < arrivalTime m (residualTail s ω)) :
    canonicalRenewalCount (s + h) ω =
      canonicalRenewalCount s ω + canonicalRenewalCount h (residualTail s ω) := by
  let a := canonicalRenewalCount s ω
  let b := canonicalRenewalCount h (residualTail s ω)
  have hupper : s + h < arrivalTime (a + b) ω := by
    have htailgt := lt_arrivalTime_canonicalRenewalCount h (residualTail s ω) hTail
    rw [arrivalTime_residualTail] at htailgt
    change h < arrivalTime (canonicalRenewalCount s ω +
      canonicalRenewalCount h (residualTail s ω)) ω - s at htailgt
    linarith
  rw [canonicalRenewalCount_eq_find (s + h) ω hSH]
  apply (Nat.find_eq_iff hSH).mpr
  constructor
  · simpa [a, b] using hupper
  · intro k hk hgt
    by_cases hka : k < a
    · have hle := arrivalTime_le_of_lt_canonicalRenewalCount s ω hS hka
      linarith
    · have hak : a ≤ k := Nat.le_of_not_gt hka
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hak
      have hjb : j < b := by omega
      have hle := arrivalTime_le_of_lt_canonicalRenewalCount h (residualTail s ω)
        hTail hjb
      rw [arrivalTime_residualTail] at hle
      change arrivalTime (canonicalRenewalCount s ω + j) ω - s ≤ h at hle
      linarith

/-- Restarting a deterministic renewal path first at `s` and then after a
further nonnegative duration `h` is exactly the same residual path as
restarting once at `s + h`, whenever the requisite future arrivals exist.
This is deterministic count algebra; no memoryless or fresh-tail assertion
is used here. -/
theorem residualTail_add_eq_residualTail_comp
    (s h : ℝ) (hh : 0 ≤ h) (ω : ℕ → ℝ)
    (hS : ∃ n : ℕ, s < arrivalTime n ω)
    (hSH : ∃ n : ℕ, s + h < arrivalTime n ω)
    (hTail : ∃ m : ℕ, h < arrivalTime m (residualTail s ω)) :
    residualTail (s + h) ω = residualTail h (residualTail s ω) := by
  have hcount := canonicalRenewalCount_add_eq_residualTailCount
    s h hh ω hS hSH hTail
  funext k
  cases k with
  | zero =>
      rw [residualTail, residualTail, hcount, arrivalTime_residualTail]
      ring
  | succ k =>
      simp only [residualTail]
      have hindex : canonicalRenewalCount h (residualTail s ω) + (k + 1) =
          (canonicalRenewalCount h (residualTail s ω) + k) + 1 := by omega
      rw [hindex]
      simp [interarrival, residualTail, hcount, Nat.add_assoc]

theorem exists_residualTail_arrival_gt_of_tendsto
    (s h : ℝ) (ω : ℕ → ℝ)
    (hdiv : Tendsto (fun n : ℕ => arrivalTime n ω) atTop atTop) :
    ∃ m : ℕ, h < arrivalTime m (residualTail s ω) := by
  obtain ⟨N, hN⟩ := (eventually_atTop.1 (hdiv.eventually_gt_atTop (s + h)))
  let a := canonicalRenewalCount s ω
  let p := max N a
  refine ⟨p - a, ?_⟩
  rw [arrivalTime_residualTail]
  have hpa : a ≤ p := le_max_right N a
  have hp : s + h < arrivalTime p ω := hN p (le_max_left N a)
  change h < arrivalTime (canonicalRenewalCount s ω + (p - a)) ω - s
  rw [show canonicalRenewalCount s ω = a by rfl, Nat.add_sub_of_le hpa]
  linarith

/-- The clock-time decomposition holds almost surely under the canonical
exponential product law. -/
theorem ae_canonicalRenewalCount_add_eq_residualTailCount
    {rate : ℝ} (hrate : 0 < rate) (s h : ℝ) (hh : 0 ≤ h) :
    ∀ᵐ ω ∂exponentialInterarrivalMeasure rate,
      canonicalRenewalCount (s + h) ω =
        canonicalRenewalCount s ω + canonicalRenewalCount h (residualTail s ω) := by
  filter_upwards [ae_arrivalTime_tendsto_atTop hrate] with ω hdiv
  apply canonicalRenewalCount_add_eq_residualTailCount s h hh ω
  · exact (hdiv.eventually_gt_atTop s).exists
  · exact (hdiv.eventually_gt_atTop (s + h)).exists
  · exact exists_residualTail_arrival_gt_of_tendsto s h ω hdiv

/-- The canonical deterministic-time count increment is the count of the
residual tail almost surely. -/
theorem ae_canonicalRenewalCount_increment_eq_residualTailCount
    {rate : ℝ} (hrate : 0 < rate) (s h : ℝ) (hh : 0 ≤ h) :
    ∀ᵐ ω ∂exponentialInterarrivalMeasure rate,
      canonicalRenewalCount (s + h) ω - canonicalRenewalCount s ω =
        canonicalRenewalCount h (residualTail s ω) := by
  filter_upwards [ae_canonicalRenewalCount_add_eq_residualTailCount hrate s h hh]
    with ω hω
  rw [hω]
  omega

/--
Once stopped residual-tail regeneration is supplied, the deterministic-time
increment has the Poisson law immediately.
-/
theorem canonicalRenewalCount_increment_hasLaw_poisson_of_residualTail_hasLaw
    {rate : ℝ} (hrate : 0 < rate) (s h : ℝ) (hh : 0 ≤ h)
    (hresidual : ProbabilityTheory.HasLaw (residualTail s)
      (exponentialInterarrivalMeasure rate) (exponentialInterarrivalMeasure rate)) :
    ProbabilityTheory.HasLaw
      (fun ω => canonicalRenewalCount (s + h) ω - canonicalRenewalCount s ω)
      (ProbabilityTheory.poissonMeasure
        (⟨rate * h, mul_nonneg hrate.le hh⟩ : ℝ≥0))
      (exponentialInterarrivalMeasure rate) := by
  have htail : ProbabilityTheory.HasLaw
      (fun ω => canonicalRenewalCount h (residualTail s ω))
      (ProbabilityTheory.poissonMeasure
        (⟨rate * h, mul_nonneg hrate.le hh⟩ : ℝ≥0))
      (exponentialInterarrivalMeasure rate) :=
    (canonicalRenewalCount_hasLaw_poisson hrate hh).comp hresidual
  exact htail.congr
    (ae_canonicalRenewalCount_increment_eq_residualTailCount hrate s h hh)

/-- At a deterministic renewal epoch, the residual-tail path is the ordinary
deterministic-index future interarrival path almost surely. -/
theorem ae_residualTail_arrivalPrefix_eq_futureInterarrival
    {rate : ℝ} (hrate : 0 < rate) (n : ℕ) :
    ∀ᵐ ω ∂exponentialInterarrivalMeasure rate,
      residualTail (arrivalPrefix n ω) ω = futureInterarrival n ω := by
  filter_upwards [ae_canonicalRenewalCount_arrivalPrefix_add hrate n 0 le_rfl,
    ae_all_interarrival_positive hrate] with ω hcount hpos
  have htail_zero : canonicalRenewalCount 0 (futureInterarrival n ω) = 0 := by
    rw [canonicalRenewalCount_eq_zero_iff]
    left
    simpa [arrivalTime, futureInterarrival, interarrival] using hpos n
  have hindex : canonicalRenewalCount (arrivalPrefix n ω) ω = n := by
    simpa [htail_zero] using hcount
  funext k
  cases k with
  | zero =>
      rw [residualTail, hindex]
      simp [arrivalTime, arrivalPrefix, Finset.sum_range_succ, futureInterarrival,
        interarrival]
  | succ k =>
      simp [residualTail, hindex, futureInterarrival, interarrival]

/-- The full iid residual-tail path regenerates at every deterministic renewal
epoch. This is not a residual-memorylessness theorem at an arbitrary clock
time inside a random interarrival gap. -/
theorem residualTail_arrivalPrefix_hasLaw_path
    {rate : ℝ} (hrate : 0 < rate) (n : ℕ) :
    ProbabilityTheory.HasLaw (fun ω : ℕ → ℝ => residualTail (arrivalPrefix n ω) ω)
      (exponentialInterarrivalMeasure rate) (exponentialInterarrivalMeasure rate) := by
  exact (futureInterarrival_hasLaw_path hrate n).congr
    (ae_residualTail_arrivalPrefix_eq_futureInterarrival hrate n)

/-- At the initial renewal epoch, the residual-tail path is a fresh canonical
exponential interarrival path. -/
theorem residualTail_zero_hasLaw_path
    {rate : ℝ} (hrate : 0 < rate) :
    ProbabilityTheory.HasLaw (residualTail 0)
      (exponentialInterarrivalMeasure rate) (exponentialInterarrivalMeasure rate) := by
  simpa [arrivalPrefix] using residualTail_arrivalPrefix_hasLaw_path hrate 0

/-- The deterministic-time increment starting from the tagged origin has the
Poisson law.  Later starting times still require residual memorylessness. -/
theorem canonicalRenewalCount_increment_zero_hasLaw_poisson
    {rate h : ℝ} (hrate : 0 < rate) (hh : 0 ≤ h) :
    ProbabilityTheory.HasLaw
      (fun ω => canonicalRenewalCount (0 + h) ω - canonicalRenewalCount 0 ω)
      (ProbabilityTheory.poissonMeasure
        (⟨rate * h, mul_nonneg hrate.le hh⟩ : ℝ≥0))
      (exponentialInterarrivalMeasure rate) := by
  exact canonicalRenewalCount_increment_hasLaw_poisson_of_residualTail_hasLaw
    hrate 0 h hh (residualTail_zero_hasLaw_path hrate)

end

end AppliedModelingLib.Probability.PoissonProcess

import AppliedModelingLib.Foundations.Probability.StationaryPoissonFutureInputFactors
import AppliedModelingLib.Foundations.Probability.PoissonSuspensionEquilibriumSection
import AppliedModelingLib.Foundations.Probability.PoissonSuspensionDeterministicTimeContinuation
import AppliedModelingLib.Foundations.Probability.StationaryPoissonWorkFutureMarkFactors

/-!
# A measurable section for stationary Poisson deterministic-time factors

The deterministic-time factor of a stationary marked Poisson input retains
all but the fresh residual arrival-gap tail.  This module gives a measurable
reconstruction section from the full factor back to the literal marked input.
On the actual factor image, that section is pointwise exact.
-/

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory

noncomputable section

/-- Reconstruct a stationary marked Poisson input from its deterministic-time
external data and residual arrival-gap tail.  The definition is total; its
arbitrary behavior away from the factor image is confined to the measurable
equilibrium-coordinate section. -/
def stationaryPoissonWorkFromFutureTimeSliceFactors
    (rate : ℝ) (hrate : 0 < rate) (s : ℝ) :
    StationaryPoissonWorkFutureTimeSliceExternal × (ℕ → ℝ) →
      PoissonProcess.GoodSuspensionState × (ℤ → ℝ) :=
  fun x =>
    let future := PoissonProcess.reconstructCanonicalRenewalPath s x.1.2 x.2
    let arrival := PoissonProcess.equilibriumToGoodSuspension rate hrate
      (future, x.1.1.1.1.1)
    stationaryPoissonWorkFromFutureMarkFactors
      (((arrival, x.1.1.1.1.2), x.1.1.1.2), x.1.1.2)

/-- The deterministic-time reconstruction section is Borel measurable. -/
theorem measurable_stationaryPoissonWorkFromFutureTimeSliceFactors
    (rate : ℝ) (hrate : 0 < rate) (s : ℝ) :
    Measurable (stationaryPoissonWorkFromFutureTimeSliceFactors rate hrate s) := by
  let future : StationaryPoissonWorkFutureTimeSliceExternal × (ℕ → ℝ) → ℕ → ℝ :=
    fun x => PoissonProcess.reconstructCanonicalRenewalPath s x.1.2 x.2
  have hfuture : Measurable future := by
    exact PoissonProcess.measurable_reconstructCanonicalRenewalPath s |>.comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  let base : StationaryPoissonWorkFutureTimeSliceExternal × (ℕ → ℝ) →
      (ℕ → ℝ) × (ℕ → ℝ) :=
    fun x => (future x, x.1.1.1.1.1)
  have hbase : Measurable base :=
    hfuture.prodMk (measurable_fst.comp (measurable_fst.comp (measurable_fst.comp
      (measurable_fst.comp measurable_fst))))
  let arrival : StationaryPoissonWorkFutureTimeSliceExternal × (ℕ → ℝ) →
      PoissonProcess.GoodSuspensionState :=
    PoissonProcess.equilibriumToGoodSuspension rate hrate ∘ base
  have harrival : Measurable arrival :=
    (PoissonProcess.measurable_equilibriumToGoodSuspension rate hrate).comp hbase
  let factors : StationaryPoissonWorkFutureTimeSliceExternal × (ℕ → ℝ) →
      ((PoissonProcess.GoodSuspensionState × ℝ) × (ℕ → ℝ)) × (ℕ → ℝ) :=
    fun x => (((arrival x, x.1.1.1.1.2), x.1.1.1.2), x.1.1.2)
  have hfactors : Measurable factors :=
    ((harrival.prodMk
      (measurable_snd.comp (measurable_fst.comp (measurable_fst.comp
        (measurable_fst.comp measurable_fst))))).prodMk
        (measurable_snd.comp (measurable_fst.comp (measurable_fst.comp measurable_fst)))).prodMk
          (measurable_snd.comp (measurable_fst.comp measurable_fst))
  exact measurable_stationaryPoissonWorkFromFutureMarkFactors.comp hfactors

/-- Reconstructing an actual deterministic-time factor recovers the literal
stationary marked Poisson input. -/
theorem stationaryPoissonWorkFromFutureTimeSliceFactors_apply_factors
    (rate : ℝ) (hrate : 0 < rate) (s : ℝ)
    (z : PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) :
    stationaryPoissonWorkFromFutureTimeSliceFactors rate hrate s
      (stationaryPoissonWorkFutureTimeSliceFactors s z) = z := by
  rcases z with ⟨arrival, work⟩
  have harrival : PoissonProcess.equilibriumToGoodSuspension rate hrate
      (PoissonProcess.reconstructCanonicalRenewalPath s
        (stationaryPoissonWorkFutureTimeSliceFactors s (arrival, work)).1.2
        (stationaryPoissonWorkFutureTimeSliceFactors s (arrival, work)).2,
        (stationaryPoissonWorkFutureTimeSliceFactors s (arrival, work)).1.1.1.1.1) = arrival := by
    rw [reconstructCanonicalRenewalPath_stationaryPoissonWorkFutureTimeSliceFactors_eqFuture,
      stationaryPoissonWorkFutureTimeSliceFactors_pastEquilibrium]
    simpa [stationaryPoissonWorkToEquilibrium] using
      (PoissonProcess.equilibriumToGoodSuspension_apply_suspensionToEquilibrium
        rate hrate arrival)
  calc
    stationaryPoissonWorkFromFutureTimeSliceFactors rate hrate s
        (stationaryPoissonWorkFutureTimeSliceFactors s (arrival, work)) =
        stationaryPoissonWorkFromFutureMarkFactors
          (stationaryPoissonWorkFutureMarkFactors (arrival, work)) := by
      apply congrArg stationaryPoissonWorkFromFutureMarkFactors
      rw [harrival]
      rw [stationaryPoissonWorkFutureTimeSliceFactors_originWork,
        stationaryPoissonWorkFutureTimeSliceFactors_pastWork,
        stationaryPoissonWorkFutureTimeSliceFactors_futureWork]
      rfl
    _ = (arrival, work) :=
      stationaryPoissonWorkFromFutureMarkFactors_apply_factors (arrival, work)

/-- A deterministic continuation of a stationary marked input from the data
exposed through a time slice.  Its arrival continuation is obtained from the
exposed backward equilibrium half, so it uses no residual future-gap tail. -/
def stationaryPoissonWorkFromFutureTimeSliceExternalPastTail
    (rate : ℝ) (hrate : 0 < rate) (s : ℝ) :
    StationaryPoissonWorkFutureTimeSliceExternal →
      PoissonProcess.GoodSuspensionState × (ℤ → ℝ) :=
  fun x =>
    let past := x.1.1.1.1
    let future := PoissonProcess.reconstructCanonicalRenewalPath s x.2
      (fun n => past (n + 1))
    let arrival := PoissonProcess.equilibriumToGoodSuspension rate hrate (future, past)
    stationaryPoissonWorkFromFutureMarkFactors
      (((arrival, x.1.1.1.2), x.1.1.2), x.1.2)

/-- The backward-half deterministic continuation is Borel measurable. -/
theorem measurable_stationaryPoissonWorkFromFutureTimeSliceExternalPastTail
    (rate : ℝ) (hrate : 0 < rate) (s : ℝ) :
    Measurable (stationaryPoissonWorkFromFutureTimeSliceExternalPastTail rate hrate s) := by
  let past : StationaryPoissonWorkFutureTimeSliceExternal → ℕ → ℝ :=
    fun x => x.1.1.1.1
  have hpast : Measurable past :=
    (measurable_fst.comp (measurable_fst.comp
      (measurable_fst.comp measurable_fst)))
  let tail : StationaryPoissonWorkFutureTimeSliceExternal → ℕ → ℝ :=
    fun x n => past x (n + 1)
  have htail : Measurable tail := by
    apply measurable_pi_iff.2
    intro n
    exact (measurable_pi_apply (n + 1)).comp hpast
  let future : StationaryPoissonWorkFutureTimeSliceExternal → ℕ → ℝ :=
    fun x => PoissonProcess.reconstructCanonicalRenewalPath s x.2 (tail x)
  have hfuture : Measurable future :=
    PoissonProcess.measurable_reconstructCanonicalRenewalPath s |>.comp
      (measurable_snd.prodMk htail)
  let arrival : StationaryPoissonWorkFutureTimeSliceExternal →
      PoissonProcess.GoodSuspensionState :=
    fun x => PoissonProcess.equilibriumToGoodSuspension rate hrate (future x, past x)
  have harrival : Measurable arrival :=
    (PoissonProcess.measurable_equilibriumToGoodSuspension rate hrate).comp
      (hfuture.prodMk hpast)
  let factors : StationaryPoissonWorkFutureTimeSliceExternal →
      ((PoissonProcess.GoodSuspensionState × ℝ) × (ℕ → ℝ)) × (ℕ → ℝ) :=
    fun x => (((arrival x, x.1.1.1.2), x.1.1.2), x.1.2)
  have hfactors : Measurable factors :=
    ((harrival.prodMk
      (measurable_snd.comp (measurable_fst.comp
        (measurable_fst.comp measurable_fst)))).prodMk
        (measurable_snd.comp (measurable_fst.comp measurable_fst))).prodMk
          (measurable_snd.comp measurable_fst)
  exact measurable_stationaryPoissonWorkFromFutureMarkFactors.comp hfactors

/-- On an actual stationary input, the external-only continuation uses the
literal reconstructed renewal state, rather than the total section's fallback
outside the good carrier. -/
theorem stationaryPoissonWorkFromFutureTimeSliceExternalPastTail_arrival_apply_factors
    (rate : ℝ) (hrate : 0 < rate) (s : ℝ) (hs : 0 ≤ s)
    (z : PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) :
    (stationaryPoissonWorkFromFutureTimeSliceExternalPastTail rate hrate s
      (stationaryPoissonWorkFutureTimeSliceFactors s z).1).1.1 =
      PoissonProcess.equilibriumToSuspension
        (PoissonProcess.reconstructCanonicalRenewalPath s
          (PoissonProcess.canonicalRenewalPastHistory s
            (PoissonProcess.suspensionToEquilibrium z.1.1).1)
          (fun n => (PoissonProcess.suspensionToEquilibrium z.1.1).2 (n + 1)),
        (PoissonProcess.suspensionToEquilibrium z.1.1).2) := by
  rcases z with ⟨arrival, work⟩
  have hmem :=
    PoissonProcess.equilibriumToSuspension_reconstructPastTail_mem_good_of_goodSuspension
      s arrival hs
  have hsection : PoissonProcess.equilibriumToGoodSuspension rate hrate
      (PoissonProcess.reconstructCanonicalRenewalPath s
        (PoissonProcess.canonicalRenewalPastHistory s
          (PoissonProcess.suspensionToEquilibrium arrival.1).1)
        (fun n => (PoissonProcess.suspensionToEquilibrium arrival.1).2 (n + 1)),
      (PoissonProcess.suspensionToEquilibrium arrival.1).2) =
      ⟨PoissonProcess.equilibriumToSuspension
        (PoissonProcess.reconstructCanonicalRenewalPath s
          (PoissonProcess.canonicalRenewalPastHistory s
            (PoissonProcess.suspensionToEquilibrium arrival.1).1)
          (fun n => (PoissonProcess.suspensionToEquilibrium arrival.1).2 (n + 1)),
        (PoissonProcess.suspensionToEquilibrium arrival.1).2), hmem⟩ :=
    PoissonProcess.equilibriumToGoodSuspension_eq_mk_of_mem rate hrate _ hmem
  change (PoissonProcess.equilibriumToGoodSuspension rate hrate
    (PoissonProcess.reconstructCanonicalRenewalPath s
      (PoissonProcess.canonicalRenewalPastHistory s
        (PoissonProcess.suspensionToEquilibrium arrival.1).1)
      (fun n => (PoissonProcess.suspensionToEquilibrium arrival.1).2 (n + 1)),
    (PoissonProcess.suspensionToEquilibrium arrival.1).2)).1 = _
  rw [hsection]

/-- The deterministic arrival continuation retains every stationary work mark
of the original marked input. -/
theorem stationaryPoissonWorkFromFutureTimeSliceExternalPastTail_work_apply_factors
    (rate : ℝ) (hrate : 0 < rate) (s : ℝ)
    (z : PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) :
    (stationaryPoissonWorkFromFutureTimeSliceExternalPastTail rate hrate s
    (stationaryPoissonWorkFutureTimeSliceFactors s z).1).2 = z.2 := by
  rcases z with ⟨arrival, work⟩
  funext k
  cases k with
  | ofNat n =>
      cases n with
      | zero =>
          change (stationaryPoissonWorkFutureTimeSliceFactors s (arrival, work)).1.1.1.1.2 =
            work 0
          rw [stationaryPoissonWorkFutureTimeSliceFactors_originWork]
          simp [PoissonProcess.twoSidedHeadPositiveNegative_apply]
      | succ n =>
          change (stationaryPoissonWorkFutureTimeSliceFactors s (arrival, work)).1.1.2 n =
            work (Int.ofNat (n + 1))
          rw [stationaryPoissonWorkFutureTimeSliceFactors_futureWork]
          rfl
  | negSucc n =>
      change (stationaryPoissonWorkFutureTimeSliceFactors s (arrival, work)).1.1.1.2 n =
        work (Int.negSucc n)
      rw [stationaryPoissonWorkFutureTimeSliceFactors_pastWork]
      simp [PoissonProcess.twoSidedHeadPositiveNegative_apply]

/-- The external-only continuation preserves the complete renewal history
strictly exposed by its deterministic clock. -/
theorem canonicalRenewalPastHistory_stationaryPoissonWorkFromFutureTimeSliceExternalPastTail
    (rate : ℝ) (hrate : 0 < rate) (s : ℝ) (hs : 0 ≤ s)
    (z : PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) :
    PoissonProcess.canonicalRenewalPastHistory s
      ((PoissonProcess.suspensionToEquilibrium
        (stationaryPoissonWorkFromFutureTimeSliceExternalPastTail rate hrate s
          (stationaryPoissonWorkFutureTimeSliceFactors s z).1).1.1).1) =
      PoissonProcess.canonicalRenewalPastHistory s
        ((PoissonProcess.suspensionToEquilibrium z.1.1).1) := by
  rcases z with ⟨arrival, work⟩
  have harrival :=
    stationaryPoissonWorkFromFutureTimeSliceExternalPastTail_arrival_apply_factors
      rate hrate s hs (arrival, work)
  have hsplit : PoissonProcess.suspensionToEquilibrium
      (stationaryPoissonWorkFromFutureTimeSliceExternalPastTail rate hrate s
        (stationaryPoissonWorkFutureTimeSliceFactors s (arrival, work)).1).1.1 =
      (PoissonProcess.reconstructCanonicalRenewalPath s
        (PoissonProcess.canonicalRenewalPastHistory s
          (PoissonProcess.suspensionToEquilibrium arrival.1).1)
        (fun n => (PoissonProcess.suspensionToEquilibrium arrival.1).2 (n + 1)),
      (PoissonProcess.suspensionToEquilibrium arrival.1).2) := by
    rw [harrival, PoissonProcess.suspensionToEquilibrium_equilibriumToSuspension]
  rw [hsplit]
  change PoissonProcess.canonicalRenewalPastHistory s
      (PoissonProcess.reconstructCanonicalRenewalPath s
        (PoissonProcess.canonicalRenewalPastHistory s
          (PoissonProcess.suspensionToEquilibrium arrival.1).1)
        (fun n => (PoissonProcess.suspensionToEquilibrium arrival.1).2 (n + 1))) =
      PoissonProcess.canonicalRenewalPastHistory s
        (PoissonProcess.suspensionToEquilibrium arrival.1).1
  apply PoissonProcess.canonicalRenewalPastHistory_reconstructCanonicalRenewalPath
  · exact PoissonProcess.exists_arrivalTime_gt_suspensionToEquilibrium_future_of_goodSuspension
      s arrival
  · change 0 < PoissonProcess.twoSidedGap (Int.negSucc 0) arrival.1.1
    exact arrival.2.2.1 (Int.negSucc 0)

/-- The external-only continuation has exactly the same number of forward
arrivals through the deterministic clock as the original stationary input. -/
theorem canonicalRenewalCount_stationaryPoissonWorkFromFutureTimeSliceExternalPastTail
    (rate : ℝ) (hrate : 0 < rate) (s : ℝ) (hs : 0 ≤ s)
    (z : PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) :
    PoissonProcess.canonicalRenewalCount s
      ((PoissonProcess.suspensionToEquilibrium
        (stationaryPoissonWorkFromFutureTimeSliceExternalPastTail rate hrate s
          (stationaryPoissonWorkFutureTimeSliceFactors s z).1).1.1).1) =
      PoissonProcess.canonicalRenewalCount s
        ((PoissonProcess.suspensionToEquilibrium z.1.1).1) :=
  congrArg Prod.fst
    (canonicalRenewalPastHistory_stationaryPoissonWorkFromFutureTimeSliceExternalPastTail
      rate hrate s hs z)

/-- Every forward interarrival strictly before the deterministic clock is
unchanged by the external-only stationary continuation. -/
theorem interarrival_stationaryPoissonWorkFromFutureTimeSliceExternalPastTail_of_lt_count
    (rate : ℝ) (hrate : 0 < rate) (s : ℝ) (hs : 0 ≤ s)
    (z : PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) (k : ℕ)
    (hk : k < PoissonProcess.canonicalRenewalCount s
      ((PoissonProcess.suspensionToEquilibrium z.1.1).1)) :
    PoissonProcess.interarrival k
      ((PoissonProcess.suspensionToEquilibrium
        (stationaryPoissonWorkFromFutureTimeSliceExternalPastTail rate hrate s
          (stationaryPoissonWorkFutureTimeSliceFactors s z).1).1.1).1) =
      PoissonProcess.interarrival k
        ((PoissonProcess.suspensionToEquilibrium z.1.1).1) := by
  rcases z with ⟨arrival, work⟩
  have harrival :=
    stationaryPoissonWorkFromFutureTimeSliceExternalPastTail_arrival_apply_factors
      rate hrate s hs (arrival, work)
  have hsplit : PoissonProcess.suspensionToEquilibrium
      (stationaryPoissonWorkFromFutureTimeSliceExternalPastTail rate hrate s
        (stationaryPoissonWorkFutureTimeSliceFactors s (arrival, work)).1).1.1 =
      (PoissonProcess.reconstructCanonicalRenewalPath s
        (PoissonProcess.canonicalRenewalPastHistory s
          (PoissonProcess.suspensionToEquilibrium arrival.1).1)
        (fun n => (PoissonProcess.suspensionToEquilibrium arrival.1).2 (n + 1)),
      (PoissonProcess.suspensionToEquilibrium arrival.1).2) := by
    rw [harrival, PoissonProcess.suspensionToEquilibrium_equilibriumToSuspension]
  rw [hsplit]
  change PoissonProcess.interarrival k
      (PoissonProcess.reconstructCanonicalRenewalPath s
        (PoissonProcess.canonicalRenewalPastHistory s
          (PoissonProcess.suspensionToEquilibrium arrival.1).1)
        (fun n => (PoissonProcess.suspensionToEquilibrium arrival.1).2 (n + 1))) =
      PoissonProcess.interarrival k (PoissonProcess.suspensionToEquilibrium arrival.1).1
  apply PoissonProcess.interarrival_reconstructCanonicalRenewalPath_of_lt_count
  · exact PoissonProcess.exists_arrivalTime_gt_suspensionToEquilibrium_future_of_goodSuspension
      s arrival
  · change 0 < PoissonProcess.twoSidedGap (Int.negSucc 0) arrival.1.1
    exact arrival.2.2.1 (Int.negSucc 0)
  · exact hk

/-- Hence every labelled forward arrival strictly before the deterministic
clock has the same physical epoch under the continuation. -/
theorem arrivalTime_stationaryPoissonWorkFromFutureTimeSliceExternalPastTail_of_lt_count
    (rate : ℝ) (hrate : 0 < rate) (s : ℝ) (hs : 0 ≤ s)
    (z : PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) (k : ℕ)
    (hk : k < PoissonProcess.canonicalRenewalCount s
      ((PoissonProcess.suspensionToEquilibrium z.1.1).1)) :
    PoissonProcess.arrivalTime k
      ((PoissonProcess.suspensionToEquilibrium
        (stationaryPoissonWorkFromFutureTimeSliceExternalPastTail rate hrate s
          (stationaryPoissonWorkFutureTimeSliceFactors s z).1).1.1).1) =
      PoissonProcess.arrivalTime k
        ((PoissonProcess.suspensionToEquilibrium z.1.1).1) := by
  unfold PoissonProcess.arrivalTime
  apply Finset.sum_congr rfl
  intro r hr
  apply interarrival_stationaryPoissonWorkFromFutureTimeSliceExternalPastTail_of_lt_count
    rate hrate s hs z r
  exact lt_of_le_of_lt (Nat.le_of_lt_succ (Finset.mem_range.mp hr)) hk

/-- The external-only deterministic continuation leaves every stationary
arrival epoch at or before its exposing clock unchanged.  This is the
pathwise causal-prefix statement used when a finite queueing trace is replayed
from a deterministic time slice. -/
theorem suspensionBaseArrival_stationaryPoissonWorkFromFutureTimeSliceExternalPastTail_eq_of_le
    (rate : ℝ) (hrate : 0 < rate) (s : ℝ) (hs : 0 ≤ s)
    (z : PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) (i : ℤ)
    (hi : PoissonProcess.suspensionBaseArrival z.1 i ≤ s) :
    PoissonProcess.suspensionBaseArrival
      (stationaryPoissonWorkFromFutureTimeSliceExternalPastTail rate hrate s
        (stationaryPoissonWorkFutureTimeSliceFactors s z).1).1 i =
      PoissonProcess.suspensionBaseArrival z.1 i := by
  rcases z with ⟨arrival, work⟩
  have hraw :=
    stationaryPoissonWorkFromFutureTimeSliceExternalPastTail_arrival_apply_factors
      rate hrate s hs (arrival, work)
  have hsplit : PoissonProcess.suspensionToEquilibrium
      (stationaryPoissonWorkFromFutureTimeSliceExternalPastTail rate hrate s
        (stationaryPoissonWorkFutureTimeSliceFactors s (arrival, work)).1).1.1 =
      (PoissonProcess.reconstructCanonicalRenewalPath s
        (PoissonProcess.canonicalRenewalPastHistory s
          (PoissonProcess.suspensionToEquilibrium arrival.1).1)
        (fun n => (PoissonProcess.suspensionToEquilibrium arrival.1).2 (n + 1)),
      (PoissonProcess.suspensionToEquilibrium arrival.1).2) := by
    rw [hraw, PoissonProcess.suspensionToEquilibrium_equilibriumToSuspension]
  have hi' : PoissonProcess.equilibriumBaseArrival
      (PoissonProcess.suspensionToEquilibrium arrival.1) i ≤ s := by
    rw [PoissonProcess.equilibriumBaseArrival_suspensionToEquilibrium]
    exact hi
  have hbaseLeft : PoissonProcess.suspensionBaseArrival
      (stationaryPoissonWorkFromFutureTimeSliceExternalPastTail rate hrate s
        (stationaryPoissonWorkFutureTimeSliceFactors s (arrival, work)).1).1 i =
      PoissonProcess.equilibriumBaseArrival
        (PoissonProcess.suspensionToEquilibrium
          (stationaryPoissonWorkFromFutureTimeSliceExternalPastTail rate hrate s
            (stationaryPoissonWorkFutureTimeSliceFactors s (arrival, work)).1).1.1) i := by
    simpa [PoissonProcess.suspensionBaseArrival] using
      (PoissonProcess.equilibriumBaseArrival_suspensionToEquilibrium
        (stationaryPoissonWorkFromFutureTimeSliceExternalPastTail rate hrate s
          (stationaryPoissonWorkFutureTimeSliceFactors s (arrival, work)).1).1.1 i).symm
  have hbaseRight : PoissonProcess.suspensionBaseArrival arrival i =
      PoissonProcess.equilibriumBaseArrival
        (PoissonProcess.suspensionToEquilibrium arrival.1) i := by
    simpa [PoissonProcess.suspensionBaseArrival] using
      (PoissonProcess.equilibriumBaseArrival_suspensionToEquilibrium arrival.1 i).symm
  rw [hbaseLeft, hbaseRight, hsplit]
  cases i with
  | ofNat n =>
      cases n with
      | zero =>
          change PoissonProcess.equilibriumBaseArrival
              (PoissonProcess.reconstructCanonicalRenewalPath s
                (PoissonProcess.canonicalRenewalPastHistory s
                  (PoissonProcess.suspensionToEquilibrium arrival.1).1)
                (fun n => (PoissonProcess.suspensionToEquilibrium arrival.1).2 (n + 1)),
              (PoissonProcess.suspensionToEquilibrium arrival.1).2) 0 =
            PoissonProcess.equilibriumBaseArrival
              (PoissonProcess.suspensionToEquilibrium arrival.1) 0
          rw [PoissonProcess.equilibriumBaseArrival_zero,
            PoissonProcess.equilibriumBaseArrival_zero]
          rfl
      | succ n =>
          have htime : PoissonProcess.arrivalTime n
              (PoissonProcess.suspensionToEquilibrium arrival.1).1 ≤ s := by
            rw [PoissonProcess.equilibriumBaseArrival_ofNat_succ] at hi'
            exact hi'
          have hfuture :=
            PoissonProcess.exists_arrivalTime_gt_suspensionToEquilibrium_future_of_goodSuspension
              s arrival
          have hfuturePos : ∀ n, 0 < PoissonProcess.interarrival n
              (PoissonProcess.suspensionToEquilibrium arrival.1).1 := by
            intro k
            cases k with
            | zero =>
                change 0 < PoissonProcess.twoSidedGap 0 arrival.1.1 - arrival.1.2
                linarith [arrival.2.1.2]
            | succ k =>
                simpa [PoissonProcess.interarrival,
                  PoissonProcess.suspensionToEquilibrium,
                  PoissonProcess.twoSidedGap] using
                  arrival.2.2.1 (Int.ofNat (k + 1))
          have hmono : Monotone (fun k : ℕ => PoissonProcess.arrivalTime k
              (PoissonProcess.suspensionToEquilibrium arrival.1).1) :=
            (PoissonProcess.arrivalTime_strictMono_of_positive _ hfuturePos).monotone
          have hk : n < PoissonProcess.canonicalRenewalCount s
              (PoissonProcess.suspensionToEquilibrium arrival.1).1 :=
            (PoissonProcess.lt_canonicalRenewalCount_iff_arrivalTime_le s
              (PoissonProcess.suspensionToEquilibrium arrival.1).1 hfuture hmono n).mpr htime
          rw [PoissonProcess.equilibriumBaseArrival_ofNat_succ,
            PoissonProcess.equilibriumBaseArrival_ofNat_succ]
          have heq := arrivalTime_stationaryPoissonWorkFromFutureTimeSliceExternalPastTail_of_lt_count
            rate hrate s hs (arrival, work) n hk
          rw [hsplit] at heq
          exact heq
  | negSucc n =>
      rw [PoissonProcess.equilibriumBaseArrival_negSucc,
        PoissonProcess.equilibriumBaseArrival_negSucc]
      rfl

/-- The deterministic continuation has the same stationary arrival epoch
whenever either version places that labelled arrival at or before the exposing
clock.  The symmetric form makes the literal pre-clock finite point set
available from either path. -/
theorem suspensionBaseArrival_stationaryPoissonWorkFromFutureTimeSliceExternalPastTail_eq_of_le_or_le
    (rate : ℝ) (hrate : 0 < rate) (s : ℝ) (hs : 0 ≤ s)
    (z : PoissonProcess.GoodSuspensionState × (ℤ → ℝ)) (i : ℤ)
    (hi : PoissonProcess.suspensionBaseArrival z.1 i ≤ s ∨
      PoissonProcess.suspensionBaseArrival
        (stationaryPoissonWorkFromFutureTimeSliceExternalPastTail rate hrate s
          (stationaryPoissonWorkFutureTimeSliceFactors s z).1).1 i ≤ s) :
    PoissonProcess.suspensionBaseArrival
      (stationaryPoissonWorkFromFutureTimeSliceExternalPastTail rate hrate s
        (stationaryPoissonWorkFutureTimeSliceFactors s z).1).1 i =
      PoissonProcess.suspensionBaseArrival z.1 i := by
  rcases hi with hi | hi
  · exact suspensionBaseArrival_stationaryPoissonWorkFromFutureTimeSliceExternalPastTail_eq_of_le
      rate hrate s hs z i hi
  rcases z with ⟨arrival, work⟩
  have hraw :=
    stationaryPoissonWorkFromFutureTimeSliceExternalPastTail_arrival_apply_factors
      rate hrate s hs (arrival, work)
  have hsplit : PoissonProcess.suspensionToEquilibrium
      (stationaryPoissonWorkFromFutureTimeSliceExternalPastTail rate hrate s
        (stationaryPoissonWorkFutureTimeSliceFactors s (arrival, work)).1).1.1 =
      (PoissonProcess.reconstructCanonicalRenewalPath s
        (PoissonProcess.canonicalRenewalPastHistory s
          (PoissonProcess.suspensionToEquilibrium arrival.1).1)
        (fun n => (PoissonProcess.suspensionToEquilibrium arrival.1).2 (n + 1)),
      (PoissonProcess.suspensionToEquilibrium arrival.1).2) := by
    rw [hraw, PoissonProcess.suspensionToEquilibrium_equilibriumToSuspension]
  have hbaseLeft : PoissonProcess.suspensionBaseArrival
      (stationaryPoissonWorkFromFutureTimeSliceExternalPastTail rate hrate s
        (stationaryPoissonWorkFutureTimeSliceFactors s (arrival, work)).1).1 i =
      PoissonProcess.equilibriumBaseArrival
        (PoissonProcess.suspensionToEquilibrium
          (stationaryPoissonWorkFromFutureTimeSliceExternalPastTail rate hrate s
            (stationaryPoissonWorkFutureTimeSliceFactors s (arrival, work)).1).1.1) i := by
    simpa [PoissonProcess.suspensionBaseArrival] using
      (PoissonProcess.equilibriumBaseArrival_suspensionToEquilibrium
        (stationaryPoissonWorkFromFutureTimeSliceExternalPastTail rate hrate s
          (stationaryPoissonWorkFutureTimeSliceFactors s (arrival, work)).1).1.1 i).symm
  have hbaseRight : PoissonProcess.suspensionBaseArrival arrival i =
      PoissonProcess.equilibriumBaseArrival
        (PoissonProcess.suspensionToEquilibrium arrival.1) i := by
    simpa [PoissonProcess.suspensionBaseArrival] using
      (PoissonProcess.equilibriumBaseArrival_suspensionToEquilibrium arrival.1 i).symm
  rw [hbaseLeft, hbaseRight, hsplit]
  cases i with
  | ofNat n =>
      cases n with
      | zero =>
          change PoissonProcess.equilibriumBaseArrival
              (PoissonProcess.reconstructCanonicalRenewalPath s
                (PoissonProcess.canonicalRenewalPastHistory s
                  (PoissonProcess.suspensionToEquilibrium arrival.1).1)
                (fun n => (PoissonProcess.suspensionToEquilibrium arrival.1).2 (n + 1)),
              (PoissonProcess.suspensionToEquilibrium arrival.1).2) 0 =
            PoissonProcess.equilibriumBaseArrival
              (PoissonProcess.suspensionToEquilibrium arrival.1) 0
          rw [PoissonProcess.equilibriumBaseArrival_zero,
            PoissonProcess.equilibriumBaseArrival_zero]
          rfl
      | succ n =>
          have htimeNew : PoissonProcess.arrivalTime n
              (PoissonProcess.suspensionToEquilibrium
                (stationaryPoissonWorkFromFutureTimeSliceExternalPastTail rate hrate s
                  (stationaryPoissonWorkFutureTimeSliceFactors s (arrival, work)).1).1.1).1 ≤ s := by
            rw [hbaseLeft, PoissonProcess.equilibriumBaseArrival_ofNat_succ] at hi
            exact hi
          let continued :=
            stationaryPoissonWorkFromFutureTimeSliceExternalPastTail rate hrate s
              (stationaryPoissonWorkFutureTimeSliceFactors s (arrival, work)).1
          have hfuture :=
            PoissonProcess.exists_arrivalTime_gt_suspensionToEquilibrium_future_of_goodSuspension
              s continued.1
          have hfuturePos : ∀ k, 0 < PoissonProcess.interarrival k
              (PoissonProcess.suspensionToEquilibrium continued.1.1).1 := by
            intro k
            cases k with
            | zero =>
                change 0 < PoissonProcess.twoSidedGap 0 continued.1.1.1 - continued.1.1.2
                linarith [continued.1.2.1.2]
            | succ k =>
                simpa [PoissonProcess.interarrival,
                  PoissonProcess.suspensionToEquilibrium,
                  PoissonProcess.twoSidedGap] using
                  continued.1.2.2.1 (Int.ofNat (k + 1))
          have hmono : Monotone (fun k : ℕ => PoissonProcess.arrivalTime k
              (PoissonProcess.suspensionToEquilibrium continued.1.1).1) :=
            (PoissonProcess.arrivalTime_strictMono_of_positive _ hfuturePos).monotone
          have hkcontinued : n < PoissonProcess.canonicalRenewalCount s
              (PoissonProcess.suspensionToEquilibrium continued.1.1).1 :=
            (PoissonProcess.lt_canonicalRenewalCount_iff_arrivalTime_le s
              (PoissonProcess.suspensionToEquilibrium continued.1.1).1 hfuture hmono n).mpr
              (by simpa [continued] using htimeNew)
          have hcount :=
            canonicalRenewalCount_stationaryPoissonWorkFromFutureTimeSliceExternalPastTail
              rate hrate s hs (arrival, work)
          have hk : n < PoissonProcess.canonicalRenewalCount s
              (PoissonProcess.suspensionToEquilibrium arrival.1).1 := by
            rw [hcount] at hkcontinued
            exact hkcontinued
          rw [PoissonProcess.equilibriumBaseArrival_ofNat_succ,
            PoissonProcess.equilibriumBaseArrival_ofNat_succ]
          have heq := arrivalTime_stationaryPoissonWorkFromFutureTimeSliceExternalPastTail_of_lt_count
            rate hrate s hs (arrival, work) n hk
          rw [hsplit] at heq
          exact heq
  | negSucc n =>
      rw [PoissonProcess.equilibriumBaseArrival_negSucc,
        PoissonProcess.equilibriumBaseArrival_negSucc]
      rfl

end

end AppliedModelingLib.Probability.Queueing

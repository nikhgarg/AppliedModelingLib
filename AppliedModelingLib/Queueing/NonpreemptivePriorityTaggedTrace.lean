import AppliedModelingLib.Foundations.Probability.PalmTaggedArrivalFiniteLedger
import AppliedModelingLib.Queueing.NonpreemptivePriorityArrivalLedger
import AppliedModelingLib.Queueing.NonpreemptivePriorityStationaryTrace
import AppliedModelingLib.Queueing.StationaryPriorityInput

/-!
# Finite selected-arrival traces for nonpreemptive-priority queues

This module turns the genuine multiclass selected-arrival input carrier into
finite chronological priority-job ledgers.  It makes the customer tagged at
time zero an explicit member of each trace window containing zero.  A later
module will take remote-past limits of these finite ledgers to define the
stationary tagged response.
-/

namespace AppliedModelingLib.Queueing

open ProbabilityTheory

noncomputable section

/-- The distinguished class-`i` customer at the Palm origin, represented as
an ordinary priority job with its original class/index identifier. -/
def stationaryPriorityClassTaggedJob
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i) :
    NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n) :=
  { identifier := Sigma.mk i 0
    priority := i
    arrivalTime := stationaryPriorityClassTaggedArrival i z i 0
    serviceWork := stationaryPriorityClassTaggedWorkRequirementAt meanService i z i 0 }

/-- The finite chronological priority-job trace over one physical window of a
multiclass selected-arrival configuration. -/
def stationaryPriorityClassTaggedArrivalWindowJobs
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a b : ℝ) :
    List (NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n)) :=
  chronologicalNonpreemptivePriorityArrivalWindowJobs
    (stationaryPriorityClassTaggedArrivalWindowIndices i z a b)
    (stationaryPriorityClassTaggedArrival i z)
    (stationaryPriorityClassTaggedWorkRequirementAt meanService i z)

/-- Execute the literal finite arrival window of a selected-class Palm input,
starting empty at the left endpoint and serving to the right endpoint.  This
is the concrete finite precursor to the stationary tagged response; it does
not posit a queue state or a waiting-time distribution. -/
def stationaryPriorityClassTaggedFiniteWindowState
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a b : ℝ) :
    NonpreemptivePriorityWorkState n (NonpreemptivePriorityArrivalIndex n) :=
  let initial := emptyNonpreemptivePriorityWorkState
    (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) a
  let afterArrivals := runNonpreemptivePriorityArrivalTrace initial
    (stationaryPriorityClassTaggedArrivalWindowJobs meanService i z a b)
  advanceNonpreemptivePriorityWorkState
    (totalNonpreemptivePriorityWorkJobs afterArrivals) b afterArrivals

/-- At phase zero, the selected/Palm finite input ledger is the literal
stationary input ledger viewed from the same epoch.  This is an input-level
identity; later results may transport it through a chosen finite replay. -/
theorem stationaryPriorityClassTaggedArrivalWindowIndices_view_eq_stationary
    {n : ℕ} (i : Fin n)
    (omega : Fin n → StationaryPoissonWorkPath) (a b : ℝ)
    (hphase : (omega i).1.1.2 = 0) :
    stationaryPriorityClassTaggedArrivalWindowIndices i
      (multiclassStationaryPoissonWorkClassTaggedView i omega) a b =
      stationaryPriorityArrivalWindowIndices omega a b := by
  funext j
  ext k
  by_cases hji : j = i
  · subst j
    have hgood : Probability.PoissonProcess.suspensionGoodGapPath (omega i).1.1.1 :=
      (omega i).1.2.2
    simp only [stationaryPriorityClassTaggedArrivalWindowIndices,
      stationaryPriorityArrivalWindowIndices,
      multiclassStationaryPoissonWorkClassTaggedView]
    simp
    rw [Probability.PoissonProcess.mem_palmTaggedArrivalIndices_iff
      a b (omega i).1.1.1 hgood k,
      Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff
        a b (omega i).1 k]
    simp only [Probability.PoissonProcess.suspensionBaseArrival]
    rw [hphase]
    simp
  · simp [stationaryPriorityClassTaggedArrivalWindowIndices,
      stationaryPriorityArrivalWindowIndices,
      multiclassStationaryPoissonWorkClassTaggedView, hji]

/-- A selected-arrival finite execution retains the class-FIFO invariant. -/
theorem hasClassConsistentWaiting_stationaryPriorityClassTaggedFiniteWindowState
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a b : ℝ) :
    hasClassConsistentWaiting
      (stationaryPriorityClassTaggedFiniteWindowState meanService i z a b) := by
  unfold stationaryPriorityClassTaggedFiniteWindowState
  dsimp only
  apply hasClassConsistentWaiting_advanceNonpreemptivePriorityWorkState
  apply hasClassConsistentWaiting_runNonpreemptivePriorityArrivalTrace
  exact hasClassConsistentWaiting_emptyNonpreemptivePriorityWorkState a

/-- A selected-arrival finite execution is non-idling whenever work is
available, independently of the eventual stationary limiting argument. -/
theorem nonpreemptivePriorityWorkConserving_stationaryPriorityClassTaggedFiniteWindowState
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a b : ℝ) :
    nonpreemptivePriorityWorkConserving
      (stationaryPriorityClassTaggedFiniteWindowState meanService i z a b) := by
  unfold stationaryPriorityClassTaggedFiniteWindowState
  dsimp only
  apply nonpreemptivePriorityWorkConserving_advance
  apply nonpreemptivePriorityWorkConserving_run
  exact nonpreemptivePriorityWorkConserving_emptyNonpreemptivePriorityWorkState a

/-- The tagged job's physical arrival time is zero. -/
theorem stationaryPriorityClassTaggedJob_arrivalTime
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i) :
    (stationaryPriorityClassTaggedJob meanService i z).arrivalTime = 0 := by
  simpa [stationaryPriorityClassTaggedJob] using
    stationaryPriorityClassTaggedArrival_tag_zero i z

/-- The tagged job's service-work field is the existing distinguished-work
observable used by the selected-arrival moment calculations. -/
theorem stationaryPriorityClassTaggedJob_serviceWork
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i) :
    (stationaryPriorityClassTaggedJob meanService i z).serviceWork =
      stationaryPriorityClassTaggedWorkRequirement meanService i z := by
  simpa [stationaryPriorityClassTaggedJob] using
    (stationaryPriorityClassTaggedWorkRequirement_eq_fullCoordinate
      meanService i z).symm

/-- Every job enumerated by a finite selected-arrival ledger lies at or after
its literal left endpoint.  The tagged class uses the Palm good-gap carrier;
the passive classes use their stationary finite-window ledgers. -/
theorem left_le_arrivalTime_stationaryPriorityClassTaggedArrivalWindowJobs
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a b : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (hjob : job ∈ stationaryPriorityClassTaggedArrivalWindowJobs meanService i z a b) :
    a ≤ job.arrivalTime := by
  rcases (mem_chronologicalNonpreemptivePriorityArrivalWindowJobs_iff
    (stationaryPriorityClassTaggedArrivalWindowIndices i z a b)
    (stationaryPriorityClassTaggedArrival i z)
    (stationaryPriorityClassTaggedWorkRequirementAt meanService i z) job).mp hjob with
      ⟨j, k, hindex, rfl⟩
  by_cases hji : j = i
  · subst j
    have hindex' : k ∈ Probability.PoissonProcess.palmTaggedArrivalIndices a b z.1.1 := by
      simpa [stationaryPriorityClassTaggedArrivalWindowIndices] using hindex
    have hinterval := (Probability.PoissonProcess.mem_palmTaggedArrivalIndices_iff
      a b z.1.1 hgood k).mp hindex'
    simpa [stationaryPriorityClassTaggedArrival,
      multiclassStationaryPoissonWorkClassTaggedArrival] using hinterval.1
  · have hindex' : k ∈ Probability.PoissonProcess.suspensionBaseArrivalIndices a b
        (z.2 ⟨j, hji⟩).1 := by
      simpa [stationaryPriorityClassTaggedArrivalWindowIndices, hji] using hindex
    have hinterval := (Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff
      a b (z.2 ⟨j, hji⟩).1 k).mp hindex'
    simpa [stationaryPriorityClassTaggedArrival,
      multiclassStationaryPoissonWorkClassTaggedArrival, hji] using hinterval.1

/-- Every job enumerated by a finite selected-arrival ledger lies strictly
before its literal right endpoint. -/
theorem arrivalTime_lt_stationaryPriorityClassTaggedArrivalWindowJobs_right
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a b : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (hjob : job ∈ stationaryPriorityClassTaggedArrivalWindowJobs meanService i z a b) :
    job.arrivalTime < b := by
  rcases (mem_chronologicalNonpreemptivePriorityArrivalWindowJobs_iff
    (stationaryPriorityClassTaggedArrivalWindowIndices i z a b)
    (stationaryPriorityClassTaggedArrival i z)
    (stationaryPriorityClassTaggedWorkRequirementAt meanService i z) job).mp hjob with
      ⟨j, k, hindex, rfl⟩
  by_cases hji : j = i
  · subst j
    have hindex' : k ∈ Probability.PoissonProcess.palmTaggedArrivalIndices a b z.1.1 := by
      simpa [stationaryPriorityClassTaggedArrivalWindowIndices] using hindex
    have hinterval := (Probability.PoissonProcess.mem_palmTaggedArrivalIndices_iff
      a b z.1.1 hgood k).mp hindex'
    simpa [stationaryPriorityClassTaggedArrival,
      multiclassStationaryPoissonWorkClassTaggedArrival] using hinterval.2
  · have hindex' : k ∈ Probability.PoissonProcess.suspensionBaseArrivalIndices a b
        (z.2 ⟨j, hji⟩).1 := by
      simpa [stationaryPriorityClassTaggedArrivalWindowIndices, hji] using hindex
    have hinterval := (Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff
      a b (z.2 ⟨j, hji⟩).1 k).mp hindex'
    simpa [stationaryPriorityClassTaggedArrival,
      multiclassStationaryPoissonWorkClassTaggedArrival, hji] using hinterval.2

/-- A selected tagged job is present in every finite chronological ledger
whose half-open window contains the Palm origin.  The good tagged-gap premise
is exactly the finite-ledger condition used to identify the selected class's
Palm indices with their physical epochs. -/
theorem stationaryPriorityClassTaggedJob_mem_arrivalWindow
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a b : ℝ)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (ha : a ≤ 0) (hb : 0 < b) :
    stationaryPriorityClassTaggedJob meanService i z ∈
      stationaryPriorityClassTaggedArrivalWindowJobs meanService i z a b := by
  apply (mem_chronologicalNonpreemptivePriorityArrivalWindowJobs_iff
    (stationaryPriorityClassTaggedArrivalWindowIndices i z a b)
    (stationaryPriorityClassTaggedArrival i z)
    (stationaryPriorityClassTaggedWorkRequirementAt meanService i z)
    (stationaryPriorityClassTaggedJob meanService i z)).mpr
  refine ⟨i, 0, ?_, rfl⟩
  change 0 ∈ stationaryPriorityClassTaggedArrivalWindowIndices i z a b i
  rw [show stationaryPriorityClassTaggedArrivalWindowIndices i z a b i =
      Probability.PoissonProcess.palmTaggedArrivalIndices a b z.1.1 by
        simp [stationaryPriorityClassTaggedArrivalWindowIndices]]
  apply (Probability.PoissonProcess.mem_palmTaggedArrivalIndices_iff a b z.1.1
    hgood 0).mpr
  simpa [Probability.PoissonProcess.candidatePalmArrival_zero] using ⟨ha, hb⟩

/-- Under the genuine selected-class multiclass Palm law, the tagged job is
almost surely present in every finite physical-time ledger containing its
arrival epoch.  The only exceptional paths are the null nonexplosive-gap
carrier excluded by the concrete Poisson construction. -/
theorem ae_stationaryPriorityClassTaggedJob_mem_arrivalWindow
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (i : Fin n) (a b : ℝ) (ha : a ≤ 0) (hb : 0 < b) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      stationaryPriorityClassTaggedJob meanService i z ∈
        stationaryPriorityClassTaggedArrivalWindowJobs meanService i z a b := by
  filter_upwards [ae_multiclassStationaryPoissonWorkClassTaggedGapPath_good
    arrivalRate harrivalRate i] with z hgood
  exact stationaryPriorityClassTaggedJob_mem_arrivalWindow meanService i z a b hgood ha hb

/-- Every job in every fixed finite selected-arrival trace has positive
service work almost surely.  This combines the all-class tagged mark carrier
with the literal finite index ledger and is the physical-work hypothesis used
by the deterministic trace accounting lemmas. -/
theorem ae_all_stationaryPriorityClassTaggedArrivalWindowJobs_serviceWork_positive
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (i : Fin n) (a b : ℝ) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      ∀ job ∈ stationaryPriorityClassTaggedArrivalWindowJobs meanService i z a b,
        0 < job.serviceWork := by
  filter_upwards [
    ae_all_stationaryPriorityClassTaggedWorkRequirementAt_positive
      arrivalRate meanService harrivalRate hmeanService i] with z hz
  intro job hjob
  rcases (mem_chronologicalNonpreemptivePriorityArrivalWindowJobs_iff
    (stationaryPriorityClassTaggedArrivalWindowIndices i z a b)
    (stationaryPriorityClassTaggedArrival i z)
    (stationaryPriorityClassTaggedWorkRequirementAt meanService i z) job).mp hjob with
      ⟨j, k, _, hjob⟩
  subst job
  exact hz j k

/-- The selected-arrival ledger is chronological in physical time, including
the distinguished job when its window contains zero. -/
theorem pairwise_arrivalTime_le_stationaryPriorityClassTaggedArrivalWindowJobs
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a b : ℝ) :
    (stationaryPriorityClassTaggedArrivalWindowJobs meanService i z a b).Pairwise
      (fun job other => job.arrivalTime ≤ other.arrivalTime) :=
  pairwise_arrivalTime_le_chronologicalNonpreemptivePriorityJobs _

/-- Total marked work in one literal selected-arrival window.  This is the
finite work ledger underlying the physical finite trace, before any
remote-past limiting argument. -/
def stationaryPriorityClassTaggedArrivalWindowTotalWork
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a b : ℝ) : ℝ :=
  ∑ j, (stationaryPriorityClassTaggedArrivalWindowIndices i z a b j).sum
    (stationaryPriorityClassTaggedWorkRequirementAt meanService i z j)

/-- Sorting the finite selected-arrival ledger does not change its scalar
service-work sum. -/
theorem nonpreemptivePriorityArrivalTraceServiceWork_stationaryPriorityClassTaggedArrivalWindowJobs
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a b : ℝ) :
    nonpreemptivePriorityArrivalTraceServiceWork
      (stationaryPriorityClassTaggedArrivalWindowJobs meanService i z a b) =
      stationaryPriorityClassTaggedArrivalWindowTotalWork meanService i z a b := by
  classical
  let indices := stationaryPriorityClassTaggedArrivalWindowIndices i z a b
  let arrival := stationaryPriorityClassTaggedArrival i z
  let work := stationaryPriorityClassTaggedWorkRequirementAt meanService i z
  let ledger := nonpreemptivePriorityArrivalWindowIndices indices
  have hperm := perm_chronologicalNonpreemptivePriorityArrivalWindowJobs
    indices arrival work
  unfold nonpreemptivePriorityArrivalTraceServiceWork
    stationaryPriorityClassTaggedArrivalWindowJobs
    stationaryPriorityClassTaggedArrivalWindowTotalWork
  calc
    (chronologicalNonpreemptivePriorityArrivalWindowJobs
        (stationaryPriorityClassTaggedArrivalWindowIndices i z a b)
        (stationaryPriorityClassTaggedArrival i z)
        (stationaryPriorityClassTaggedWorkRequirementAt meanService i z) |>.map
          (fun job => job.serviceWork)).sum =
        (nonpreemptivePriorityArrivalWindowJobs
          (stationaryPriorityClassTaggedArrivalWindowIndices i z a b)
          (stationaryPriorityClassTaggedArrival i z)
          (stationaryPriorityClassTaggedWorkRequirementAt meanService i z) |>.map
            (fun job => job.serviceWork)).sum :=
      (hperm.map _).sum_eq
    _ = ∑ q ∈ ledger,
        stationaryPriorityClassTaggedWorkRequirementAt meanService i z q.1 q.2 := by
      unfold nonpreemptivePriorityArrivalWindowJobs
      rw [List.map_map]
      change (ledger.toList.map fun q =>
        stationaryPriorityClassTaggedWorkRequirementAt meanService i z q.1 q.2).sum = _
      simpa only [ledger.toList_toFinset] using
        (List.sum_toFinset
          (fun q => stationaryPriorityClassTaggedWorkRequirementAt meanService i z q.1 q.2)
          ledger.nodup_toList).symm
    _ = ∑ j, (stationaryPriorityClassTaggedArrivalWindowIndices i z a b j).sum
        (stationaryPriorityClassTaggedWorkRequirementAt meanService i z j) := by
      unfold ledger indices nonpreemptivePriorityArrivalWindowIndices
      rw [Finset.sum_sigma]

/-- Selected-arrival index ledgers split exactly across adjacent half-open
physical windows.  The tagged class uses its Palm coordinate, while every
passive class uses its stationary coordinate. -/
theorem stationaryPriorityClassTaggedArrivalWindowIndices_append
    {n : ℕ} (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a c b : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hac : a ≤ c) (hcb : c ≤ b) :
    stationaryPriorityClassTaggedArrivalWindowIndices i z a b =
      fun j => stationaryPriorityClassTaggedArrivalWindowIndices i z a c j ∪
        stationaryPriorityClassTaggedArrivalWindowIndices i z c b j := by
  funext j
  ext k
  by_cases hji : j = i
  · subst j
    simp only [stationaryPriorityClassTaggedArrivalWindowIndices, dif_pos]
    rw [Finset.mem_union,
      Probability.PoissonProcess.mem_palmTaggedArrivalIndices_iff a c z.1.1 hgood,
      Probability.PoissonProcess.mem_palmTaggedArrivalIndices_iff c b z.1.1 hgood,
      Probability.PoissonProcess.mem_palmTaggedArrivalIndices_iff a b z.1.1 hgood]
    constructor
    · rintro ⟨haleft, haright⟩
      by_cases hbefore : Probability.PoissonProcess.candidatePalmArrival z.1.1 k < c
      · exact Or.inl ⟨haleft, hbefore⟩
      · exact Or.inr ⟨le_of_not_gt hbefore, haright⟩
    · rintro (hleft | hright)
      · exact ⟨hleft.1, lt_of_lt_of_le hleft.2 hcb⟩
      · exact ⟨le_trans hac hright.1, hright.2⟩
  · simp only [stationaryPriorityClassTaggedArrivalWindowIndices, dif_neg hji]
    rw [Finset.mem_union,
      Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff a c
        (z.2 ⟨j, hji⟩).1 k,
      Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff c b
        (z.2 ⟨j, hji⟩).1 k,
      Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff a b
        (z.2 ⟨j, hji⟩).1 k]
    constructor
    · rintro ⟨haleft, haright⟩
      by_cases hbefore : Probability.PoissonProcess.suspensionBaseArrival
          (z.2 ⟨j, hji⟩).1 k < c
      · exact Or.inl ⟨haleft, hbefore⟩
      · exact Or.inr ⟨le_of_not_gt hbefore, haright⟩
    · rintro (hleft | hright)
      · exact ⟨hleft.1, lt_of_lt_of_le hleft.2 hcb⟩
      · exact ⟨le_trans hac hright.1, hright.2⟩

/-- The two selected-arrival ledgers on adjacent half-open windows are
disjoint. -/
theorem disjoint_stationaryPriorityClassTaggedArrivalWindowIndices_adjacent
    {n : ℕ} (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a c b : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1) :
    ∀ j, Disjoint (stationaryPriorityClassTaggedArrivalWindowIndices i z a c j)
      (stationaryPriorityClassTaggedArrivalWindowIndices i z c b j) := by
  intro j
  rw [Finset.disjoint_left]
  intro k hkleft hkright
  by_cases hji : j = i
  · subst j
    have hleft := (Probability.PoissonProcess.mem_palmTaggedArrivalIndices_iff
      a c z.1.1 hgood k).mp (by
        simpa [stationaryPriorityClassTaggedArrivalWindowIndices] using hkleft)
    have hright := (Probability.PoissonProcess.mem_palmTaggedArrivalIndices_iff
      c b z.1.1 hgood k).mp (by
        simpa [stationaryPriorityClassTaggedArrivalWindowIndices] using hkright)
    exact (not_le_of_gt hleft.2) hright.1
  · have hleft := (Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff
      a c (z.2 ⟨j, hji⟩).1 k).mp (by
        simpa [stationaryPriorityClassTaggedArrivalWindowIndices, hji] using hkleft)
    have hright := (Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff
      c b (z.2 ⟨j, hji⟩).1 k).mp (by
        simpa [stationaryPriorityClassTaggedArrivalWindowIndices, hji] using hkright)
    exact (not_le_of_gt hleft.2) hright.1

/-- Total selected/Palm marked work is additive across adjacent half-open
physical windows. -/
theorem stationaryPriorityClassTaggedArrivalWindowTotalWork_append
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a c b : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hac : a ≤ c) (hcb : c ≤ b) :
    stationaryPriorityClassTaggedArrivalWindowTotalWork meanService i z a b =
      stationaryPriorityClassTaggedArrivalWindowTotalWork meanService i z a c +
        stationaryPriorityClassTaggedArrivalWindowTotalWork meanService i z c b := by
  unfold stationaryPriorityClassTaggedArrivalWindowTotalWork
  rw [stationaryPriorityClassTaggedArrivalWindowIndices_append i z a c b hgood hac hcb]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_union]
  exact disjoint_stationaryPriorityClassTaggedArrivalWindowIndices_adjacent i z a c b hgood j

/-- Enlarging the right endpoint of a selected-arrival window only adds
literal arrivals. -/
theorem stationaryPriorityClassTaggedArrivalWindowIndices_subset_of_le_right
    {n : ℕ} (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a b c : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hbc : b ≤ c) :
    ∀ j, stationaryPriorityClassTaggedArrivalWindowIndices i z a b j ⊆
      stationaryPriorityClassTaggedArrivalWindowIndices i z a c j := by
  intro j k hk
  by_cases hji : j = i
  · subst j
    have hinterval := (Probability.PoissonProcess.mem_palmTaggedArrivalIndices_iff
      a b z.1.1 hgood k).mp (by
        simpa [stationaryPriorityClassTaggedArrivalWindowIndices] using hk)
    simpa [stationaryPriorityClassTaggedArrivalWindowIndices] using
      (Probability.PoissonProcess.mem_palmTaggedArrivalIndices_iff
        a c z.1.1 hgood k).mpr ⟨hinterval.1, lt_of_lt_of_le hinterval.2 hbc⟩
  · have hinterval :=
      (Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff
        a b (z.2 ⟨j, hji⟩).1 k).mp (by
          simpa [stationaryPriorityClassTaggedArrivalWindowIndices, hji] using hk)
    simpa [stationaryPriorityClassTaggedArrivalWindowIndices, hji] using
      (Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff
        a c (z.2 ⟨j, hji⟩).1 k).mpr ⟨hinterval.1, lt_of_lt_of_le hinterval.2 hbc⟩

/-- Every finite selected-arrival trace embeds in a trace with the same left
endpoint and a later right endpoint. -/
theorem mem_stationaryPriorityClassTaggedArrivalWindowJobs_of_le_right
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a b c : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hbc : b ≤ c)
    (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (hjob : job ∈ stationaryPriorityClassTaggedArrivalWindowJobs meanService i z a b) :
    job ∈ stationaryPriorityClassTaggedArrivalWindowJobs meanService i z a c := by
  rcases (mem_chronologicalNonpreemptivePriorityArrivalWindowJobs_iff
    (stationaryPriorityClassTaggedArrivalWindowIndices i z a b)
    (stationaryPriorityClassTaggedArrival i z)
    (stationaryPriorityClassTaggedWorkRequirementAt meanService i z) job).mp hjob with
      ⟨j, k, hindex, hcoordinate⟩
  apply (mem_chronologicalNonpreemptivePriorityArrivalWindowJobs_iff
    (stationaryPriorityClassTaggedArrivalWindowIndices i z a c)
    (stationaryPriorityClassTaggedArrival i z)
    (stationaryPriorityClassTaggedWorkRequirementAt meanService i z) job).mpr
  exact ⟨j, k,
    stationaryPriorityClassTaggedArrivalWindowIndices_subset_of_le_right
      i z a b c hgood hbc j hindex,
    hcoordinate⟩

/-- Enlarging the left endpoint of a selected-arrival window into the past
only adds literal arrivals. -/
theorem stationaryPriorityClassTaggedArrivalWindowIndices_subset_of_le_left
    {n : ℕ} (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a b c : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hca : c ≤ a) :
    ∀ j, stationaryPriorityClassTaggedArrivalWindowIndices i z a b j ⊆
      stationaryPriorityClassTaggedArrivalWindowIndices i z c b j := by
  intro j k hk
  by_cases hji : j = i
  · subst j
    have hinterval := (Probability.PoissonProcess.mem_palmTaggedArrivalIndices_iff
      a b z.1.1 hgood k).mp (by
        simpa [stationaryPriorityClassTaggedArrivalWindowIndices] using hk)
    simpa [stationaryPriorityClassTaggedArrivalWindowIndices] using
      (Probability.PoissonProcess.mem_palmTaggedArrivalIndices_iff
        c b z.1.1 hgood k).mpr ⟨le_trans hca hinterval.1, hinterval.2⟩
  · have hinterval :=
      (Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff
        a b (z.2 ⟨j, hji⟩).1 k).mp (by
          simpa [stationaryPriorityClassTaggedArrivalWindowIndices, hji] using hk)
    simpa [stationaryPriorityClassTaggedArrivalWindowIndices, hji] using
      (Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff
        c b (z.2 ⟨j, hji⟩).1 k).mpr ⟨le_trans hca hinterval.1, hinterval.2⟩

/-- Every finite selected-arrival trace embeds in a trace with the same right
endpoint and an earlier left endpoint. -/
theorem mem_stationaryPriorityClassTaggedArrivalWindowJobs_of_le_left
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a b c : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hca : c ≤ a)
    (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (hjob : job ∈ stationaryPriorityClassTaggedArrivalWindowJobs meanService i z a b) :
    job ∈ stationaryPriorityClassTaggedArrivalWindowJobs meanService i z c b := by
  rcases (mem_chronologicalNonpreemptivePriorityArrivalWindowJobs_iff
    (stationaryPriorityClassTaggedArrivalWindowIndices i z a b)
    (stationaryPriorityClassTaggedArrival i z)
    (stationaryPriorityClassTaggedWorkRequirementAt meanService i z) job).mp hjob with
      ⟨j, k, hindex, hcoordinate⟩
  apply (mem_chronologicalNonpreemptivePriorityArrivalWindowJobs_iff
    (stationaryPriorityClassTaggedArrivalWindowIndices i z c b)
    (stationaryPriorityClassTaggedArrival i z)
    (stationaryPriorityClassTaggedWorkRequirementAt meanService i z) job).mpr
  exact ⟨j, k,
    stationaryPriorityClassTaggedArrivalWindowIndices_subset_of_le_left
      i z a b c hgood hca j hindex,
    hcoordinate⟩

/-- On a past window ending at the selected Palm arrival, the finite trace
ledger's marked work is exactly the selected/Palm input aggregate. -/
theorem stationaryPriorityClassTaggedArrivalWindowTotalWork_neg_to_zero
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) :
    stationaryPriorityClassTaggedArrivalWindowTotalWork meanService i z (-t) 0 =
      stationaryPriorityTaggedTotalPastWorkAggregate meanService i z t := by
  rfl

/-- The marked work in an older selected/Palm subwindow is the difference of
the two nested literal past-work aggregates. -/
theorem stationaryPriorityClassTaggedArrivalWindowTotalWork_neg_to_neg
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (older newer : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hnewer : 0 ≤ newer) (horizon : newer ≤ older) :
    stationaryPriorityClassTaggedArrivalWindowTotalWork meanService i z (-older) (-newer) =
      stationaryPriorityTaggedTotalPastWorkAggregate meanService i z older -
        stationaryPriorityTaggedTotalPastWorkAggregate meanService i z newer := by
  have happend := stationaryPriorityClassTaggedArrivalWindowTotalWork_append
    meanService i z (-older) (-newer) 0 hgood (neg_le_neg horizon) (neg_nonpos.mpr hnewer)
  rw [stationaryPriorityClassTaggedArrivalWindowTotalWork_neg_to_zero
    meanService i z older,
    stationaryPriorityClassTaggedArrivalWindowTotalWork_neg_to_zero
      meanService i z newer] at happend
  linarith

/-- A backward time horizon is a selected-arrival net-input cutoff when the
cumulative marked work minus elapsed service capacity never exceeds its value
at that horizon. -/
def stationaryPriorityClassTaggedNetPastCutoff
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (cutoff : ℝ) : Prop :=
  ∀ horizon, cutoff ≤ horizon →
    stationaryPriorityTaggedNetPastInput meanService i z horizon ≤
      stationaryPriorityTaggedNetPastInput meanService i z cutoff

/-- A selected-arrival net-input cutoff bounds the total marked work in every
older past interval ending at the cutoff by the available service time. -/
theorem stationaryPriorityClassTaggedArrivalWindowTotalWork_le_elapsed_of_netPastCutoff
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (cutoff older : ℝ)
    (hcutoff : stationaryPriorityClassTaggedNetPastCutoff meanService i z cutoff)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hcutoffNonneg : 0 ≤ cutoff) (horizon : cutoff ≤ older) :
    stationaryPriorityClassTaggedArrivalWindowTotalWork meanService i z (-older) (-cutoff) ≤
      older - cutoff := by
  have hmax := hcutoff older horizon
  unfold stationaryPriorityClassTaggedNetPastCutoff
    stationaryPriorityTaggedNetPastInput at hmax
  rw [stationaryPriorityClassTaggedArrivalWindowTotalWork_neg_to_neg
    meanService i z older cutoff hgood hcutoffNonneg horizon]
  linarith

/-- If a nonempty selected-arrival past-window ledger is written from its
first physical arrival onward, no literal arrival lies strictly between the
window's left endpoint and that first epoch. -/
theorem stationaryPriorityClassTaggedArrivalWindowJobs_left_of_head_eq_nil
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ)
    (head : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (tail : List (NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n)))
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hledger : stationaryPriorityClassTaggedArrivalWindowJobs meanService i z (-t) 0 =
      head :: tail) :
    stationaryPriorityClassTaggedArrivalWindowJobs meanService i z (-t) head.arrivalTime = [] := by
  have hheadMem : head ∈ stationaryPriorityClassTaggedArrivalWindowJobs
      meanService i z (-t) 0 := by
    rw [hledger]
    simp
  have hleft : -t ≤ head.arrivalTime :=
    left_le_arrivalTime_stationaryPriorityClassTaggedArrivalWindowJobs
      meanService i z (-t) 0 hgood head hheadMem
  have hright : head.arrivalTime ≤ 0 :=
    (arrivalTime_lt_stationaryPriorityClassTaggedArrivalWindowJobs_right
      meanService i z (-t) 0 hgood head hheadMem).le
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro job hjob
  have hfull : job ∈ stationaryPriorityClassTaggedArrivalWindowJobs
      meanService i z (-t) 0 :=
    mem_stationaryPriorityClassTaggedArrivalWindowJobs_of_le_right
      meanService i z (-t) head.arrivalTime 0 hgood hright job hjob
  have hfull' : job ∈ head :: tail := by
    rwa [hledger] at hfull
  have hleftRight : job.arrivalTime < head.arrivalTime :=
    arrivalTime_lt_stationaryPriorityClassTaggedArrivalWindowJobs_right
      meanService i z (-t) head.arrivalTime hgood job hjob
  have hnothead : job ≠ head := by
    intro heq
    subst job
    exact (lt_irrefl _ hleftRight).elim
  have htail : job ∈ tail := (List.mem_cons.mp hfull').resolve_left hnothead
  have hsorted := pairwise_arrivalTime_le_stationaryPriorityClassTaggedArrivalWindowJobs
    meanService i z (-t) 0
  rw [hledger] at hsorted
  have hheadLe : head.arrivalTime ≤ job.arrivalTime :=
    (List.pairwise_cons.mp hsorted).1 job htail
  exact (not_le_of_gt hleftRight) hheadLe

/-- At the first selected/Palm arrival in a nonempty past ledger, the net
input weakly dominates its value at the left window horizon. -/
theorem stationaryPriorityTaggedNetPastInput_le_at_firstArrivalAge
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ)
    (head : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (tail : List (NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n)))
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hledger : stationaryPriorityClassTaggedArrivalWindowJobs meanService i z (-t) 0 =
      head :: tail) :
    stationaryPriorityTaggedNetPastInput meanService i z t ≤
      stationaryPriorityTaggedNetPastInput meanService i z (-head.arrivalTime) := by
  have hheadMem : head ∈ stationaryPriorityClassTaggedArrivalWindowJobs
      meanService i z (-t) 0 := by
    rw [hledger]
    simp
  have hleft : -t ≤ head.arrivalTime :=
    left_le_arrivalTime_stationaryPriorityClassTaggedArrivalWindowJobs
      meanService i z (-t) 0 hgood head hheadMem
  have hright : head.arrivalTime ≤ 0 :=
    (arrivalTime_lt_stationaryPriorityClassTaggedArrivalWindowJobs_right
      meanService i z (-t) 0 hgood head hheadMem).le
  have hempty := stationaryPriorityClassTaggedArrivalWindowJobs_left_of_head_eq_nil
    meanService i z t head tail hgood hledger
  have hleftWork : stationaryPriorityClassTaggedArrivalWindowTotalWork
      meanService i z (-t) head.arrivalTime = 0 := by
    calc
      stationaryPriorityClassTaggedArrivalWindowTotalWork
          meanService i z (-t) head.arrivalTime =
          nonpreemptivePriorityArrivalTraceServiceWork
            (stationaryPriorityClassTaggedArrivalWindowJobs
              meanService i z (-t) head.arrivalTime) := by
            exact (nonpreemptivePriorityArrivalTraceServiceWork_stationaryPriorityClassTaggedArrivalWindowJobs
              meanService i z (-t) head.arrivalTime).symm
      _ = 0 := by simp [hempty, nonpreemptivePriorityArrivalTraceServiceWork]
  have happend := stationaryPriorityClassTaggedArrivalWindowTotalWork_append
    meanService i z (-t) head.arrivalTime 0 hgood hleft hright
  have hfull : stationaryPriorityClassTaggedArrivalWindowTotalWork meanService i z (-t) 0 =
      stationaryPriorityTaggedTotalPastWorkAggregate meanService i z t :=
    stationaryPriorityClassTaggedArrivalWindowTotalWork_neg_to_zero meanService i z t
  have htail : stationaryPriorityClassTaggedArrivalWindowTotalWork meanService i z
      head.arrivalTime 0 =
      stationaryPriorityTaggedTotalPastWorkAggregate meanService i z (-head.arrivalTime) := by
    simpa using
      (stationaryPriorityClassTaggedArrivalWindowTotalWork_neg_to_zero
        meanService i z (-head.arrivalTime))
  rw [hfull, htail, hleftWork] at happend
  have hage : -head.arrivalTime ≤ t := by linarith
  unfold stationaryPriorityTaggedNetPastInput
  linarith

/-- At every nonnegative backward horizon, selected/Palm net input is bounded
either by its value at the origin or by its value at the age of a literal
arrival in that finite past window. -/
theorem stationaryPriorityTaggedNetPastInput_le_zero_or_firstArrivalAge
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (ht : 0 ≤ t) :
    stationaryPriorityTaggedNetPastInput meanService i z t ≤ 0 ∨
      ∃ (head : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
        (tail : List (NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))),
        stationaryPriorityClassTaggedArrivalWindowJobs meanService i z (-t) 0 = head :: tail ∧
          0 ≤ -head.arrivalTime ∧ -head.arrivalTime ≤ t ∧
          stationaryPriorityTaggedNetPastInput meanService i z t ≤
            stationaryPriorityTaggedNetPastInput meanService i z (-head.arrivalTime) := by
  cases hledger : stationaryPriorityClassTaggedArrivalWindowJobs meanService i z (-t) 0 with
  | nil =>
      left
      have hwork : stationaryPriorityTaggedTotalPastWorkAggregate meanService i z t = 0 := by
        calc
          stationaryPriorityTaggedTotalPastWorkAggregate meanService i z t =
              stationaryPriorityClassTaggedArrivalWindowTotalWork meanService i z (-t) 0 :=
            (stationaryPriorityClassTaggedArrivalWindowTotalWork_neg_to_zero
              meanService i z t).symm
          _ = nonpreemptivePriorityArrivalTraceServiceWork
                (stationaryPriorityClassTaggedArrivalWindowJobs meanService i z (-t) 0) := by
              exact (nonpreemptivePriorityArrivalTraceServiceWork_stationaryPriorityClassTaggedArrivalWindowJobs
                meanService i z (-t) 0).symm
          _ = 0 := by simp [hledger, nonpreemptivePriorityArrivalTraceServiceWork]
      unfold stationaryPriorityTaggedNetPastInput
      linarith
  | cons head tail =>
      right
      have hheadMem : head ∈ stationaryPriorityClassTaggedArrivalWindowJobs
          meanService i z (-t) 0 := by
        rw [hledger]
        simp
      have hleft := left_le_arrivalTime_stationaryPriorityClassTaggedArrivalWindowJobs
        meanService i z (-t) 0 hgood head hheadMem
      have hright := arrivalTime_lt_stationaryPriorityClassTaggedArrivalWindowJobs_right
        meanService i z (-t) 0 hgood head hheadMem
      refine ⟨head, tail, rfl, ?_, ?_, ?_⟩
      · linarith
      · linarith
      · exact stationaryPriorityTaggedNetPastInput_le_at_firstArrivalAge
          meanService i z t head tail hgood hledger

/-- On every bounded nonnegative backward-time interval, literal selected/Palm
net input attains a maximum at the origin or at the age of a finite-window
arrival. -/
theorem exists_stationaryPriorityTaggedNetPastInput_max_on_compact
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (radius : ℝ) (hradius : 0 ≤ radius) :
    ∃ cutoff : ℝ, 0 ≤ cutoff ∧ cutoff ≤ radius ∧
      ∀ horizon, 0 ≤ horizon → horizon ≤ radius →
        stationaryPriorityTaggedNetPastInput meanService i z horizon ≤
          stationaryPriorityTaggedNetPastInput meanService i z cutoff := by
  let ledger := stationaryPriorityClassTaggedArrivalWindowJobs meanService i z (-radius) 0
  let candidateValues : List ℝ := 0 :: ledger.map fun job =>
    stationaryPriorityTaggedNetPastInput meanService i z (-job.arrivalTime)
  have hlength : 0 < candidateValues.length := by
    simp [candidateValues]
  let maximum : ℝ := candidateValues.maximum_of_length_pos hlength
  have hmaximumMem : maximum ∈ candidateValues :=
    candidateValues.maximum_of_length_pos_mem hlength
  have hleMaximum : ∀ value ∈ candidateValues, value ≤ maximum := by
    intro value hvalue
    exact candidateValues.le_maximum_of_length_pos_of_mem hvalue hlength
  have hzeroMem : (0 : ℝ) ∈ candidateValues := by
    simp [candidateValues]
  have hzeroLe : 0 ≤ maximum := hleMaximum 0 hzeroMem
  have hsplitMaximum : maximum = 0 ∨
      ∃ job ∈ ledger,
        stationaryPriorityTaggedNetPastInput meanService i z (-job.arrivalTime) = maximum := by
    simpa only [candidateValues, List.mem_cons, List.mem_map] using hmaximumMem
  rcases hsplitMaximum with hzero | ⟨cutoffJob, hcutoffMem, hcutoffValue⟩
  · refine ⟨0, le_rfl, hradius, ?_⟩
    intro horizon hnonneg hbound
    rcases stationaryPriorityTaggedNetPastInput_le_zero_or_firstArrivalAge
      meanService i z horizon hgood hnonneg with hinput | ⟨head, tail, hhead, _, _, hheadInput⟩
    · have hnetZero : stationaryPriorityTaggedNetPastInput meanService i z 0 = 0 := by
        simp [stationaryPriorityTaggedNetPastInput,
          stationaryPriorityTaggedTotalPastWorkAggregate_zero]
      exact hinput.trans_eq hnetZero.symm
    · have hheadMem : head ∈ ledger := by
        have hfull : head ∈ stationaryPriorityClassTaggedArrivalWindowJobs
            meanService i z (-radius) 0 :=
          mem_stationaryPriorityClassTaggedArrivalWindowJobs_of_le_left
            meanService i z (-horizon) 0 (-radius) hgood (neg_le_neg hbound) head (by
              rw [hhead]
              simp)
        simpa [ledger] using hfull
      have hheadValue : stationaryPriorityTaggedNetPastInput meanService i z
          (-head.arrivalTime) ∈ candidateValues := by
        apply List.mem_cons.mpr
        right
        exact List.mem_map.mpr ⟨head, hheadMem, rfl⟩
      have hboundHead := hleMaximum _ hheadValue
      rw [hzero] at hboundHead
      have hnetZero : stationaryPriorityTaggedNetPastInput meanService i z 0 = 0 := by
        simp [stationaryPriorityTaggedNetPastInput,
          stationaryPriorityTaggedTotalPastWorkAggregate_zero]
      exact hheadInput.trans (by simpa [hnetZero] using hboundHead)
  · have hcutoffLeft : -radius ≤ cutoffJob.arrivalTime := by
      simpa [ledger] using
        left_le_arrivalTime_stationaryPriorityClassTaggedArrivalWindowJobs
          meanService i z (-radius) 0 hgood cutoffJob hcutoffMem
    have hcutoffRight : cutoffJob.arrivalTime < 0 := by
      simpa [ledger] using
        arrivalTime_lt_stationaryPriorityClassTaggedArrivalWindowJobs_right
          meanService i z (-radius) 0 hgood cutoffJob hcutoffMem
    refine ⟨-cutoffJob.arrivalTime, by linarith, by linarith, ?_⟩
    intro horizon hnonneg hbound
    rcases stationaryPriorityTaggedNetPastInput_le_zero_or_firstArrivalAge
      meanService i z horizon hgood hnonneg with hinput | ⟨head, tail, hhead, _, _, hheadInput⟩
    · calc
        stationaryPriorityTaggedNetPastInput meanService i z horizon ≤ 0 := hinput
        _ ≤ maximum := hzeroLe
        _ = stationaryPriorityTaggedNetPastInput meanService i z (-cutoffJob.arrivalTime) :=
          hcutoffValue.symm
    · have hheadMem : head ∈ ledger := by
        have hfull : head ∈ stationaryPriorityClassTaggedArrivalWindowJobs
            meanService i z (-radius) 0 :=
          mem_stationaryPriorityClassTaggedArrivalWindowJobs_of_le_left
            meanService i z (-horizon) 0 (-radius) hgood (neg_le_neg hbound) head (by
              rw [hhead]
              simp)
        simpa [ledger] using hfull
      have hheadValue : stationaryPriorityTaggedNetPastInput meanService i z
          (-head.arrivalTime) ∈ candidateValues := by
        apply List.mem_cons.mpr
        right
        exact List.mem_map.mpr ⟨head, hheadMem, rfl⟩
      have hboundHead := hleMaximum _ hheadValue
      rw [← hcutoffValue] at hboundHead
      exact hheadInput.trans hboundHead

/-- A selected/Palm backward net-input path tending to `-∞` has a
nonnegative global maximizing horizon at the origin or a literal arrival age. -/
theorem exists_stationaryPriorityClassTaggedNetPastCutoff_of_tendsto_atBot
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hlimit : Filter.Tendsto
      (stationaryPriorityTaggedNetPastInput meanService i z)
      Filter.atTop Filter.atBot) :
    ∃ cutoff : ℝ, 0 ≤ cutoff ∧
      stationaryPriorityClassTaggedNetPastCutoff meanService i z cutoff := by
  have htail : ∀ᶠ horizon : ℝ in Filter.atTop,
      stationaryPriorityTaggedNetPastInput meanService i z horizon ≤ 0 :=
    Filter.tendsto_atBot.1 hlimit 0
  rcases Filter.eventually_atTop.1 htail with ⟨bound, hbound⟩
  let radius : ℝ := max bound 0
  have hradius : 0 ≤ radius := by
    dsimp [radius]
    exact le_max_right _ _
  have hboundRadius : bound ≤ radius := by
    dsimp [radius]
    exact le_max_left _ _
  rcases exists_stationaryPriorityTaggedNetPastInput_max_on_compact
    meanService i z hgood radius hradius with
    ⟨cutoff, hcutoffNonneg, hcutoffRadius, hmaximum⟩
  refine ⟨cutoff, hcutoffNonneg, ?_⟩
  intro horizon _
  by_cases hwithin : horizon ≤ radius
  · exact hmaximum horizon (le_trans hcutoffNonneg (by linarith)) hwithin
  · have htailHorizon : stationaryPriorityTaggedNetPastInput meanService i z horizon ≤ 0 :=
      hbound horizon (le_trans hboundRadius (le_of_not_ge hwithin))
    have hzero : stationaryPriorityTaggedNetPastInput meanService i z 0 = 0 := by
      simp [stationaryPriorityTaggedNetPastInput,
        stationaryPriorityTaggedTotalPastWorkAggregate_zero]
    have hcutoffNonnegative : 0 ≤ stationaryPriorityTaggedNetPastInput meanService i z cutoff := by
      simpa [hzero] using hmaximum 0 le_rfl hradius
    exact htailHorizon.trans hcutoffNonnegative

/-- Strict total load yields almost surely a literal global maximizing horizon
for the selected/Palm net-input path. -/
theorem ae_exists_stationaryPriorityClassTaggedNetPastCutoff
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      ∃ cutoff : ℝ, 0 ≤ cutoff ∧
        stationaryPriorityClassTaggedNetPastCutoff meanService i z cutoff := by
  filter_upwards [
    ae_multiclassStationaryPoissonWorkClassTaggedGapPath_good
      arrivalRate harrivalRate i,
    ae_tendsto_stationaryPriorityTaggedNetPastInput_atBot
      arrivalRate meanService harrivalRate hstable i] with z hgood hlimit
  exact exists_stationaryPriorityClassTaggedNetPastCutoff_of_tendsto_atBot
    meanService i z hgood hlimit

/-- A literal selected-arrival ledger contains each class-indexed job at most
once. -/
theorem nodup_stationaryPriorityClassTaggedArrivalWindowJobs
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a b : ℝ) :
    (stationaryPriorityClassTaggedArrivalWindowJobs meanService i z a b).Nodup := by
  unfold stationaryPriorityClassTaggedArrivalWindowJobs
    chronologicalNonpreemptivePriorityArrivalWindowJobs
    chronologicalNonpreemptivePriorityJobs
    nonpreemptivePriorityArrivalWindowJobs
  apply (List.mergeSort_perm _ _).nodup_iff.mpr
  apply List.Nodup.map
  · intro first second hjob
    simpa using congrArg NonpreemptivePriorityJob.identifier hjob
  · exact (nonpreemptivePriorityArrivalWindowIndices
      (stationaryPriorityClassTaggedArrivalWindowIndices i z a b)).nodup_toList

/-- A tail beginning at a literal arrival in a selected/Palm priority ledger
has no more service work than the complete physical window beginning at that
arrival. -/
theorem nonpreemptivePriorityArrivalTraceServiceWork_suffix_le_stationaryPriorityClassTaggedArrivalWindowTotalWork
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (older cutoff : ℝ)
    (front suffix : List (NonpreemptivePriorityJob n
      (NonpreemptivePriorityArrivalIndex n)))
    (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hpositive : ∀ other ∈ stationaryPriorityClassTaggedArrivalWindowJobs
      meanService i z (-older) (-cutoff), 0 < other.serviceWork)
    (hsplit : stationaryPriorityClassTaggedArrivalWindowJobs meanService i z
      (-older) (-cutoff) = front ++ job :: suffix) :
    nonpreemptivePriorityArrivalTraceServiceWork (job :: suffix) ≤
      stationaryPriorityClassTaggedArrivalWindowTotalWork meanService i z
        job.arrivalTime (-cutoff) := by
  let full := stationaryPriorityClassTaggedArrivalWindowJobs meanService i z (-older) (-cutoff)
  let tailWindow := stationaryPriorityClassTaggedArrivalWindowJobs meanService i z
    job.arrivalTime (-cutoff)
  have hjobFull : job ∈ full := by
    rw [show full = front ++ job :: suffix by exact hsplit]
    simp
  have htimeSorted : full.Pairwise (fun first second =>
      first.arrivalTime ≤ second.arrivalTime) := by
    exact pairwise_arrivalTime_le_stationaryPriorityClassTaggedArrivalWindowJobs
      meanService i z (-older) (-cutoff)
  have htailTime : ∀ other ∈ job :: suffix, job.arrivalTime ≤ other.arrivalTime := by
    have hsplitSorted : (front ++ job :: suffix).Pairwise (fun first second =>
        first.arrivalTime ≤ second.arrivalTime) := by
      rw [show full = front ++ job :: suffix by exact hsplit] at htimeSorted
      exact htimeSorted
    have htailSorted : (job :: suffix).Pairwise (fun first second =>
        first.arrivalTime ≤ second.arrivalTime) :=
      (List.pairwise_append.mp hsplitSorted).2.1
    rcases List.pairwise_cons.mp htailSorted with ⟨hhead, _⟩
    intro other hother
    rcases List.mem_cons.mp hother with rfl | hother
    · exact le_rfl
    · exact hhead other hother
  have htailSubset : (job :: suffix) ⊆ tailWindow := by
    intro other hother
    have hotherFull : other ∈ full := by
      rw [show full = front ++ job :: suffix by exact hsplit]
      exact List.mem_append_right _ hother
    have htime := htailTime other hother
    rcases (mem_chronologicalNonpreemptivePriorityArrivalWindowJobs_iff
      (stationaryPriorityClassTaggedArrivalWindowIndices i z (-older) (-cutoff))
      (stationaryPriorityClassTaggedArrival i z)
      (stationaryPriorityClassTaggedWorkRequirementAt meanService i z) other).mp hotherFull with
        ⟨j, k, hindex, hcoordinate⟩
    subst other
    apply (mem_chronologicalNonpreemptivePriorityArrivalWindowJobs_iff
      (stationaryPriorityClassTaggedArrivalWindowIndices i z job.arrivalTime (-cutoff))
      (stationaryPriorityClassTaggedArrival i z)
      (stationaryPriorityClassTaggedWorkRequirementAt meanService i z) _).mpr
    refine ⟨j, k, ?_, rfl⟩
    by_cases hji : j = i
    · subst j
      have hfullBounds := (Probability.PoissonProcess.mem_palmTaggedArrivalIndices_iff
        (-older) (-cutoff) z.1.1 hgood k).mp (by
          simpa [stationaryPriorityClassTaggedArrivalWindowIndices] using hindex)
      simpa [stationaryPriorityClassTaggedArrivalWindowIndices,
        stationaryPriorityClassTaggedArrival,
        multiclassStationaryPoissonWorkClassTaggedArrival] using
        (Probability.PoissonProcess.mem_palmTaggedArrivalIndices_iff
          job.arrivalTime (-cutoff) z.1.1 hgood k).mpr
          ⟨by simpa [stationaryPriorityClassTaggedArrival,
            multiclassStationaryPoissonWorkClassTaggedArrival] using htime, hfullBounds.2⟩
    · have hfullBounds :=
        (Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff
          (-older) (-cutoff) (z.2 ⟨j, hji⟩).1 k).mp (by
            simpa [stationaryPriorityClassTaggedArrivalWindowIndices, hji] using hindex)
      simpa [stationaryPriorityClassTaggedArrivalWindowIndices, hji,
        stationaryPriorityClassTaggedArrival,
        multiclassStationaryPoissonWorkClassTaggedArrival] using
        (Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff
          job.arrivalTime (-cutoff) (z.2 ⟨j, hji⟩).1 k).mpr
          ⟨by simpa [stationaryPriorityClassTaggedArrival,
            multiclassStationaryPoissonWorkClassTaggedArrival, hji] using htime, hfullBounds.2⟩
  have hjobLeft : -older ≤ job.arrivalTime := by
    exact left_le_arrivalTime_stationaryPriorityClassTaggedArrivalWindowJobs
      meanService i z (-older) (-cutoff) hgood job hjobFull
  have htailWindowSubset : tailWindow ⊆ full := by
    intro other hother
    rcases (mem_chronologicalNonpreemptivePriorityArrivalWindowJobs_iff
      (stationaryPriorityClassTaggedArrivalWindowIndices i z job.arrivalTime (-cutoff))
      (stationaryPriorityClassTaggedArrival i z)
      (stationaryPriorityClassTaggedWorkRequirementAt meanService i z) other).mp hother with
        ⟨j, k, hindex, hcoordinate⟩
    subst other
    apply (mem_chronologicalNonpreemptivePriorityArrivalWindowJobs_iff
      (stationaryPriorityClassTaggedArrivalWindowIndices i z (-older) (-cutoff))
      (stationaryPriorityClassTaggedArrival i z)
      (stationaryPriorityClassTaggedWorkRequirementAt meanService i z) _).mpr
    refine ⟨j, k, ?_, rfl⟩
    by_cases hji : j = i
    · subst j
      have htailBounds := (Probability.PoissonProcess.mem_palmTaggedArrivalIndices_iff
        job.arrivalTime (-cutoff) z.1.1 hgood k).mp (by
          simpa [stationaryPriorityClassTaggedArrivalWindowIndices] using hindex)
      simpa [stationaryPriorityClassTaggedArrivalWindowIndices] using
        (Probability.PoissonProcess.mem_palmTaggedArrivalIndices_iff
          (-older) (-cutoff) z.1.1 hgood k).mpr
          ⟨hjobLeft.trans htailBounds.1, htailBounds.2⟩
    · have htailBounds :=
        (Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff
          job.arrivalTime (-cutoff) (z.2 ⟨j, hji⟩).1 k).mp (by
            simpa [stationaryPriorityClassTaggedArrivalWindowIndices, hji] using hindex)
      simpa [stationaryPriorityClassTaggedArrivalWindowIndices, hji] using
        (Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff
          (-older) (-cutoff) (z.2 ⟨j, hji⟩).1 k).mpr
          ⟨hjobLeft.trans htailBounds.1, htailBounds.2⟩
  have htailNodup : (job :: suffix).Nodup := by
    have hfullNodup := nodup_stationaryPriorityClassTaggedArrivalWindowJobs
      meanService i z (-older) (-cutoff)
    change full.Nodup at hfullNodup
    rw [show full = front ++ job :: suffix by exact hsplit] at hfullNodup
    exact List.Nodup.of_append_right hfullNodup
  have htailSubperm : List.Subperm (job :: suffix) tailWindow :=
    htailNodup.subperm htailSubset
  rcases htailSubperm with ⟨middle, hperm, hsublist⟩
  calc
    nonpreemptivePriorityArrivalTraceServiceWork (job :: suffix) =
        ((job :: suffix).map fun other => other.serviceWork).sum := rfl
    _ = (middle.map fun other => other.serviceWork).sum := (hperm.map _).sum_eq.symm
    _ ≤ (tailWindow.map fun other => other.serviceWork).sum := by
      apply List.Sublist.sum_le_sum (hsublist.map fun other => other.serviceWork)
      intro work hwork
      rcases List.mem_map.mp hwork with ⟨other, hother, rfl⟩
      exact (hpositive other (htailWindowSubset hother)).le
    _ = stationaryPriorityClassTaggedArrivalWindowTotalWork
        meanService i z job.arrivalTime (-cutoff) := by
      exact nonpreemptivePriorityArrivalTraceServiceWork_stationaryPriorityClassTaggedArrivalWindowJobs
        meanService i z job.arrivalTime (-cutoff)

/-- A global selected/Palm net-input cutoff empties the literal reflected
workload at that cutoff for every finite start no later than the cutoff. -/
theorem nonpreemptivePriorityArrivalTraceTerminalResidualWork_eq_zero_of_stationaryPriorityClassTaggedNetPastCutoff
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (cutoff older : ℝ)
    (hcutoff : stationaryPriorityClassTaggedNetPastCutoff meanService i z cutoff)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hcutoffNonneg : 0 ≤ cutoff) (horizon : cutoff ≤ older)
    (hpositive : ∀ job ∈ stationaryPriorityClassTaggedArrivalWindowJobs
      meanService i z (-older) (-cutoff), 0 < job.serviceWork) :
    nonpreemptivePriorityArrivalTraceTerminalResidualWork (-older) 0
      (stationaryPriorityClassTaggedArrivalWindowJobs meanService i z (-older) (-cutoff))
      (-cutoff) = 0 := by
  apply nonpreemptivePriorityArrivalTraceTerminalResidualWork_eq_zero_of_all_suffixes_le
  · rw [show nonpreemptivePriorityArrivalTraceServiceWork
        (stationaryPriorityClassTaggedArrivalWindowJobs meanService i z (-older) (-cutoff)) =
        stationaryPriorityClassTaggedArrivalWindowTotalWork meanService i z
          (-older) (-cutoff) by
      exact nonpreemptivePriorityArrivalTraceServiceWork_stationaryPriorityClassTaggedArrivalWindowJobs
        meanService i z (-older) (-cutoff)]
    have hbound :=
      stationaryPriorityClassTaggedArrivalWindowTotalWork_le_elapsed_of_netPastCutoff
        meanService i z cutoff older hcutoff hgood hcutoffNonneg horizon
    linarith
  · intro front suffix job hsplit
    have hjobMem : job ∈ stationaryPriorityClassTaggedArrivalWindowJobs
        meanService i z (-older) (-cutoff) := by
      rw [hsplit]
      simp
    have hjobBeforeCutoff : job.arrivalTime ≤ -cutoff :=
      (arrivalTime_lt_stationaryPriorityClassTaggedArrivalWindowJobs_right
        meanService i z (-older) (-cutoff) hgood job hjobMem).le
    have hjobHorizon : cutoff ≤ -job.arrivalTime := by
      linarith
    calc
      nonpreemptivePriorityArrivalTraceServiceWork (job :: suffix) ≤
          stationaryPriorityClassTaggedArrivalWindowTotalWork
            meanService i z job.arrivalTime (-cutoff) :=
        nonpreemptivePriorityArrivalTraceServiceWork_suffix_le_stationaryPriorityClassTaggedArrivalWindowTotalWork
          meanService i z older cutoff front suffix job hgood hpositive hsplit
      _ ≤ -job.arrivalTime - cutoff := by
        simpa using
          stationaryPriorityClassTaggedArrivalWindowTotalWork_le_elapsed_of_netPastCutoff
            meanService i z cutoff (-job.arrivalTime) hcutoff hgood hcutoffNonneg hjobHorizon
      _ = -cutoff - job.arrivalTime := by ring

/-- Conditional on positive service marks, executing a finite selected-arrival
ledger has exactly the scalar physical-time workload recursion. -/
theorem totalResidualWork_run_stationaryPriorityClassTaggedArrivalWindowJobs
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a b : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hjobs : ∀ job ∈ stationaryPriorityClassTaggedArrivalWindowJobs meanService i z a b,
      0 < job.serviceWork) :
    let initial := emptyNonpreemptivePriorityWorkState
      (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) a
    let jobs := stationaryPriorityClassTaggedArrivalWindowJobs meanService i z a b
    totalNonpreemptivePriorityResidualWork
        (runNonpreemptivePriorityArrivalTrace initial jobs) =
      nonpreemptivePriorityArrivalTraceResidualWork a 0 jobs := by
  dsimp only
  have htrace := totalNonpreemptivePriorityResidualWork_run_eq_arrivalTraceResidualWork
    (emptyNonpreemptivePriorityWorkState
      (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) a)
    (stationaryPriorityClassTaggedArrivalWindowJobs meanService i z a b)
    (by
      constructor
      · intro active hactive
        simp [emptyNonpreemptivePriorityWorkState] at hactive
      · intro j job hmember
        simp [emptyNonpreemptivePriorityWorkState] at hmember)
    (nonpreemptivePriorityWorkConserving_emptyNonpreemptivePriorityWorkState a)
    (by
      intro job hjob
      exact left_le_arrivalTime_stationaryPriorityClassTaggedArrivalWindowJobs
        meanService i z a b hgood job hjob)
    (pairwise_arrivalTime_le_stationaryPriorityClassTaggedArrivalWindowJobs
      meanService i z a b)
    hjobs
  simpa [emptyNonpreemptivePriorityWorkState,
    totalNonpreemptivePriorityResidualWork,
    activeNonpreemptivePriorityResidualWork, priorityWaitingResidualWork] using htrace

/-- Conditional on positive marks, the final service segment of a finite
selected-arrival execution obeys exact reflected workload accounting. -/
theorem totalResidualWork_stationaryPriorityClassTaggedFiniteWindowState_terminal
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a b : ℝ) (hab : a ≤ b)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hjobs : ∀ job ∈ stationaryPriorityClassTaggedArrivalWindowJobs meanService i z a b,
      0 < job.serviceWork) :
    let initial := emptyNonpreemptivePriorityWorkState
      (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) a
    let afterArrivals := runNonpreemptivePriorityArrivalTrace initial
      (stationaryPriorityClassTaggedArrivalWindowJobs meanService i z a b)
    totalNonpreemptivePriorityResidualWork
        (stationaryPriorityClassTaggedFiniteWindowState meanService i z a b) =
      max 0 (totalNonpreemptivePriorityResidualWork afterArrivals -
        (b - afterArrivals.currentTime)) := by
  dsimp only
  apply totalNonpreemptivePriorityResidualWork_advance_eq_max_sub_of_workConserving
  · apply runNonpreemptivePriorityArrivalTrace_currentTime_le
    · simpa [emptyNonpreemptivePriorityWorkState] using hab
    · intro job hjob
      exact (arrivalTime_lt_stationaryPriorityClassTaggedArrivalWindowJobs_right
        meanService i z a b hgood job hjob).le
  · apply positiveNonpreemptivePriorityResidualWork_run
    · constructor
      · intro active hactive
        simp [emptyNonpreemptivePriorityWorkState] at hactive
      · intro j job hmember
        simp [emptyNonpreemptivePriorityWorkState] at hmember
    · exact hjobs
  · apply nonpreemptivePriorityWorkConserving_run
    exact nonpreemptivePriorityWorkConserving_emptyNonpreemptivePriorityWorkState a
  · exact le_rfl

/-- A finite selected-arrival execution has exactly the terminal physical-time
scalar workload of its literal chronological ledger. -/
theorem totalResidualWork_stationaryPriorityClassTaggedFiniteWindowState_eq_terminalResidualWork
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (a b : ℝ) (hab : a ≤ b)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hjobs : ∀ job ∈ stationaryPriorityClassTaggedArrivalWindowJobs meanService i z a b,
      0 < job.serviceWork) :
    totalNonpreemptivePriorityResidualWork
        (stationaryPriorityClassTaggedFiniteWindowState meanService i z a b) =
      nonpreemptivePriorityArrivalTraceTerminalResidualWork a 0
        (stationaryPriorityClassTaggedArrivalWindowJobs meanService i z a b) b := by
  let initial := emptyNonpreemptivePriorityWorkState
    (n := n) (JobId := NonpreemptivePriorityArrivalIndex n) a
  let jobs := stationaryPriorityClassTaggedArrivalWindowJobs meanService i z a b
  let afterArrivals := runNonpreemptivePriorityArrivalTrace initial jobs
  have hrun : totalNonpreemptivePriorityResidualWork afterArrivals =
      nonpreemptivePriorityArrivalTraceResidualWork a 0 jobs := by
    simpa [initial, jobs, afterArrivals] using
      totalResidualWork_run_stationaryPriorityClassTaggedArrivalWindowJobs
        meanService i z a b hgood hjobs
  have htime : afterArrivals.currentTime =
      nonpreemptivePriorityArrivalTraceEndTime a jobs := by
    apply runNonpreemptivePriorityArrivalTrace_currentTime_eq_endTime
    · intro job hjob
      simpa [initial, jobs] using
        left_le_arrivalTime_stationaryPriorityClassTaggedArrivalWindowJobs
          meanService i z a b hgood job hjob
    · simpa [jobs] using
        pairwise_arrivalTime_le_stationaryPriorityClassTaggedArrivalWindowJobs
          meanService i z a b
  have hterminal := totalResidualWork_stationaryPriorityClassTaggedFiniteWindowState_terminal
    meanService i z a b hab hgood hjobs
  change totalNonpreemptivePriorityResidualWork
      (stationaryPriorityClassTaggedFiniteWindowState meanService i z a b) = _
  rw [hterminal, show totalNonpreemptivePriorityResidualWork afterArrivals =
    nonpreemptivePriorityArrivalTraceResidualWork a 0 jobs from hrun, htime]
  rfl

/-- The exact finite selected-arrival workload identity holds almost surely
under the concrete multiclass Campbell/Palm law. -/
theorem ae_totalResidualWork_stationaryPriorityClassTaggedFiniteWindowState_eq_terminalResidualWork
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (i : Fin n) (a b : ℝ) (hab : a ≤ b) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      totalNonpreemptivePriorityResidualWork
          (stationaryPriorityClassTaggedFiniteWindowState meanService i z a b) =
        nonpreemptivePriorityArrivalTraceTerminalResidualWork a 0
          (stationaryPriorityClassTaggedArrivalWindowJobs meanService i z a b) b := by
  filter_upwards [
    ae_multiclassStationaryPoissonWorkClassTaggedGapPath_good
      arrivalRate harrivalRate i,
    ae_all_stationaryPriorityClassTaggedArrivalWindowJobs_serviceWork_positive
      arrivalRate meanService harrivalRate hmeanService i a b] with z hgood hjobs
  exact totalResidualWork_stationaryPriorityClassTaggedFiniteWindowState_eq_terminalResidualWork
    meanService i z a b hab hgood hjobs

/-- Starting a selected/Palm finite trace before a global net-input cutoff
leaves it empty at the cutoff's physical epoch. -/
theorem totalResidualWork_stationaryPriorityClassTaggedFiniteWindowState_eq_zero_of_netPastCutoff
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (cutoff older : ℝ)
    (hcutoff : stationaryPriorityClassTaggedNetPastCutoff meanService i z cutoff)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hcutoffNonneg : 0 ≤ cutoff) (horizon : cutoff ≤ older)
    (hpositive : ∀ job ∈ stationaryPriorityClassTaggedArrivalWindowJobs
      meanService i z (-older) (-cutoff), 0 < job.serviceWork) :
    totalNonpreemptivePriorityResidualWork
        (stationaryPriorityClassTaggedFiniteWindowState meanService i z
          (-older) (-cutoff)) = 0 := by
  rw [totalResidualWork_stationaryPriorityClassTaggedFiniteWindowState_eq_terminalResidualWork
    meanService i z (-older) (-cutoff) (neg_le_neg horizon) hgood hpositive]
  exact nonpreemptivePriorityArrivalTraceTerminalResidualWork_eq_zero_of_stationaryPriorityClassTaggedNetPastCutoff
    meanService i z cutoff older hcutoff hgood hcutoffNonneg horizon hpositive

/-- Under strict total load, almost every selected/Palm input has a finite
global cutoff such that every earlier finite physical trace is empty there. -/
theorem ae_exists_stationaryPriorityClassTaggedFiniteWindowState_emptyCutoff
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      ∃ cutoff : ℝ, 0 ≤ cutoff ∧
        ∀ older, cutoff ≤ older →
          totalNonpreemptivePriorityResidualWork
            (stationaryPriorityClassTaggedFiniteWindowState meanService i z
              (-older) (-cutoff)) = 0 := by
  filter_upwards [
    ae_exists_stationaryPriorityClassTaggedNetPastCutoff
      arrivalRate meanService harrivalRate hstable i,
    ae_all_stationaryPriorityClassTaggedWorkRequirementAt_positive
      arrivalRate meanService harrivalRate hmeanService i,
    ae_multiclassStationaryPoissonWorkClassTaggedGapPath_good
      arrivalRate harrivalRate i] with z hcutoff hpositive hgood
  rcases hcutoff with ⟨cutoff, hcutoffNonneg, hcutoff⟩
  refine ⟨cutoff, hcutoffNonneg, ?_⟩
  intro older horizon
  apply totalResidualWork_stationaryPriorityClassTaggedFiniteWindowState_eq_zero_of_netPastCutoff
    meanService i z cutoff older hcutoff hgood hcutoffNonneg horizon
  intro job hjob
  rcases (mem_chronologicalNonpreemptivePriorityArrivalWindowJobs_iff
    (stationaryPriorityClassTaggedArrivalWindowIndices i z (-older) (-cutoff))
    (stationaryPriorityClassTaggedArrival i z)
    (stationaryPriorityClassTaggedWorkRequirementAt meanService i z) job).mp hjob with
      ⟨j, k, _, hcoordinate⟩
  subst job
  exact hpositive j k

end

end AppliedModelingLib.Queueing

import AppliedModelingLib.Queueing.GPS.FiniteHorizon.Drain
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.HorizonSegments
import LG24ServiceLevelAgreements.SLA2026StationaryAdmittedPalmInputs
import Mathlib.Tactic

/-!
# Finite GPS execution from stationary admitted SLA input

This module connects the direct stationary admitted Poisson/work input to the
finite executable GPS runner.  It deliberately uses the literal finite source
ledger

`suspensionBaseArrivalIndices start horizon (omega k).1`.

The endpoint convention is `[start, horizon)`: an arrival at `start` is a
source batch applied before any positive-duration service, while an arrival at
`horizon` is excluded.  The requested horizon is instead reached by the
runner's computational zero-work fence.  Thus the input `initialWork` is the
pre-`start` workload, and no source arrival is synthesized by the fence.

This is a finite path adapter only.  It does not construct a stationary GPS
workload, a regeneration, a Palm response path, or a response-time tail.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open MeasureTheory
open scoped BigOperators NNReal

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- The actual untagged stationary epoch of a direct admitted source job. -/
def stationaryAdmittedSourceArrival
    (omega : StationaryAdmittedAllClassInput Category) (k : Category) (n : ℤ) : ℝ :=
  suspensionBaseArrival (omega k).1 n

/-- The exact iid unit-exponential work mark of a direct admitted source job. -/
def stationaryAdmittedSourceWork
    (omega : StationaryAdmittedAllClassInput Category) (k : Category) (n : ℤ) : ℝ :=
  stationaryPoissonWorkRequirement (omega k) n

/-- The finite source-index ledger for one category on `[start, horizon)`. -/
def stationaryAdmittedArrivalIndicesBetween
    (start horizon : ℝ) (omega : StationaryAdmittedAllClassInput Category)
    (k : Category) : Finset ℤ :=
  suspensionBaseArrivalIndices start horizon (omega k).1

/-- The stationary source ledger has exactly the stated half-open interval
semantics on every literal source state. -/
theorem mem_stationaryAdmittedArrivalIndicesBetween_iff
    (start horizon : ℝ) (omega : StationaryAdmittedAllClassInput Category)
    (k : Category) (n : ℤ) :
    n ∈ stationaryAdmittedArrivalIndicesBetween start horizon omega k ↔
      start ≤ stationaryAdmittedSourceArrival omega k n ∧
        stationaryAdmittedSourceArrival omega k n < horizon := by
  exact mem_suspensionBaseArrivalIndices_iff start horizon (omega k).1 n

/-- A source-level identifier is an actual category/raw-index pair, never a
synthetic scheduler index. -/
abbrev StationaryAdmittedSourceJobId (Category : Type*) := Category × ℤ

/-- All exact source job identifiers present on `[start, horizon)`. -/
def stationaryAdmittedSourceJobLedger
    (start horizon : ℝ) (omega : StationaryAdmittedAllClassInput Category) :
    Finset (StationaryAdmittedSourceJobId Category) :=
  (Finset.univ : Finset Category).biUnion fun k =>
    (stationaryAdmittedArrivalIndicesBetween start horizon omega k).image fun n => (k, n)

/-- Membership in the combined finite source ledger is precisely membership in
the corresponding category's literal stationary arrival ledger. -/
theorem mem_stationaryAdmittedSourceJobLedger_iff
    (start horizon : ℝ) (omega : StationaryAdmittedAllClassInput Category)
    (k : Category) (n : ℤ) :
    (k, n) ∈ stationaryAdmittedSourceJobLedger start horizon omega ↔
      n ∈ stationaryAdmittedArrivalIndicesBetween start horizon omega k := by
  constructor
  · intro hmem
    rcases Finset.mem_biUnion.mp hmem with ⟨j, _hj, himage⟩
    rcases Finset.mem_image.mp himage with ⟨m, hm, hpair⟩
    cases hpair
    exact hm
  · intro hmem
    apply Finset.mem_biUnion.mpr
    refine ⟨k, Finset.mem_univ _, ?_⟩
    exact Finset.mem_image.mpr ⟨n, hmem, rfl⟩

/-- The actual stationary source epoch of a finite source-job identifier. -/
def stationaryAdmittedSourceJobArrival
    (omega : StationaryAdmittedAllClassInput Category)
    (job : StationaryAdmittedSourceJobId Category) : ℝ :=
  stationaryAdmittedSourceArrival omega job.1 job.2

/-- The exact stationary work mark of a finite source-job identifier. -/
def stationaryAdmittedSourceJobWork
    (omega : StationaryAdmittedAllClassInput Category)
    (job : StationaryAdmittedSourceJobId Category) : ℝ :=
  stationaryAdmittedSourceWork omega job.1 job.2

/-- All distinct actual source epochs in `[start, horizon)`.  Equal epochs
across categories are intentionally collapsed into one simultaneous batch. -/
def stationaryAdmittedBatchTimes
    (start horizon : ℝ) (omega : StationaryAdmittedAllClassInput Category) : Finset ℝ :=
  (Finset.univ : Finset Category).biUnion fun k =>
    (stationaryAdmittedArrivalIndicesBetween start horizon omega k).image fun n =>
      stationaryAdmittedSourceArrival omega k n

/-- An exact-time source batch.  Work is summed only over literal ledger
indices whose actual stationary epoch equals `eventTime`. -/
def stationaryAdmittedBatchAt
    (start horizon : ℝ) (omega : StationaryAdmittedAllClassInput Category)
    (eventTime : ℝ) : Category → ℝ :=
  fun k => ∑ n ∈ stationaryAdmittedArrivalIndicesBetween start horizon omega k with
    stationaryAdmittedSourceArrival omega k n = eventTime,
    stationaryPoissonWorkRequirement (omega k) n

/-- The chronological duplicate-free list of exact external source batches. -/
def stationaryAdmittedBatchTimeTrace
    (start horizon : ℝ) (omega : StationaryAdmittedAllClassInput Category) : List ℝ :=
  (stationaryAdmittedBatchTimes start horizon omega).sort (fun s t : ℝ => s ≤ t)

/-- A batch-time belongs to the finite stationary source set exactly when it
comes from a literal category/index source arrival. -/
theorem mem_stationaryAdmittedBatchTimes_iff
    (start horizon : ℝ) (omega : StationaryAdmittedAllClassInput Category)
    (eventTime : ℝ) :
    eventTime ∈ stationaryAdmittedBatchTimes start horizon omega ↔
      ∃ k : Category, ∃ n : ℤ,
        n ∈ stationaryAdmittedArrivalIndicesBetween start horizon omega k ∧
          stationaryAdmittedSourceArrival omega k n = eventTime := by
  constructor
  · intro htime
    rcases Finset.mem_biUnion.mp htime with ⟨k, _hk, himage⟩
    rcases Finset.mem_image.mp himage with ⟨n, hn, harrival⟩
    exact ⟨k, n, hn, harrival⟩
  · rintro ⟨k, n, hn, harrival⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨k, Finset.mem_univ _, ?_⟩
    exact Finset.mem_image.mpr ⟨n, hn, harrival⟩

/-- The source-derived batch trace is a valid GPS trace.  It admits events at
the start endpoint, as required by the module's `[start, horizon)` convention. -/
def stationaryAdmittedExternalBatchTrace
    (start horizon : ℝ) (omega : StationaryAdmittedAllClassInput Category) :
    FiniteGPSExternalBatchTrace start where
  times := stationaryAdmittedBatchTimeTrace start horizon omega
  chronological :=
    finiteGPSChronologicalFrom_of_pairwise_le start
      (stationaryAdmittedBatchTimeTrace start horizon omega)
      (by
        intro t ht
        have htime : t ∈ stationaryAdmittedBatchTimes start horizon omega :=
          (Finset.mem_sort (fun s t : ℝ => s ≤ t)).mp ht
        rcases (mem_stationaryAdmittedBatchTimes_iff start horizon omega t).mp htime with
          ⟨k, n, hn, harrival⟩
        rw [← harrival]
        exact (mem_stationaryAdmittedArrivalIndicesBetween_iff
          start horizon omega k n).mp hn |>.1)
      (Finset.pairwise_sort (stationaryAdmittedBatchTimes start horizon omega)
        (fun s t : ℝ => s ≤ t))
  nodup := Finset.sort_nodup (stationaryAdmittedBatchTimes start horizon omega)
    (fun s t : ℝ => s ≤ t)

/-- Every external source batch time is strictly before the requested horizon. -/
theorem stationaryAdmittedExternalBatchTrace_time_lt_horizon
    (start horizon : ℝ) (omega : StationaryAdmittedAllClassInput Category)
    (eventTime : ℝ)
    (heventTime : eventTime ∈
      (stationaryAdmittedExternalBatchTrace start horizon omega).times) :
    eventTime < horizon := by
  have htime : eventTime ∈ stationaryAdmittedBatchTimes start horizon omega :=
    (Finset.mem_sort (fun s t : ℝ => s ≤ t)).mp heventTime
  rcases (mem_stationaryAdmittedBatchTimes_iff start horizon omega eventTime).mp htime with
    ⟨k, n, hn, harrival⟩
  rw [← harrival]
  exact (mem_stationaryAdmittedArrivalIndicesBetween_iff
    start horizon omega k n).mp hn |>.2

/-- Every literal category-index work mark in the finite source ledger is
counted exactly once in the corresponding exact-time batch. -/
theorem sum_stationaryAdmittedBatchAt_eq_totalLedgerWork
    (start horizon : ℝ) (omega : StationaryAdmittedAllClassInput Category)
    (k : Category) :
    ∑ t ∈ stationaryAdmittedBatchTimes start horizon omega,
      stationaryAdmittedBatchAt start horizon omega t k =
      ∑ n ∈ stationaryAdmittedArrivalIndicesBetween start horizon omega k,
        stationaryPoissonWorkRequirement (omega k) n := by
  apply Finset.sum_fiberwise_of_maps_to
  · intro n hn
    apply Finset.mem_biUnion.mpr
    refine ⟨k, Finset.mem_univ _, ?_⟩
    exact Finset.mem_image.mpr ⟨n, hn, rfl⟩

/-- Sorting the finite set of distinct source epochs does not change a finite
sum over the source batches. -/
theorem sum_stationaryAdmittedBatchTimeTrace_eq_sum_batchTimes
    (start horizon : ℝ) (omega : StationaryAdmittedAllClassInput Category)
    (f : ℝ → ℝ) :
    ((stationaryAdmittedBatchTimeTrace start horizon omega).map f).sum =
      ∑ t ∈ stationaryAdmittedBatchTimes start horizon omega, f t := by
  have hnodup : (stationaryAdmittedBatchTimeTrace start horizon omega).Nodup :=
    Finset.sort_nodup (stationaryAdmittedBatchTimes start horizon omega)
      (fun s t : ℝ => s ≤ t)
  have htoFinset : (stationaryAdmittedBatchTimeTrace start horizon omega).toFinset =
      stationaryAdmittedBatchTimes start horizon omega := by
    ext t
    simp [stationaryAdmittedBatchTimeTrace]
  calc
    ((stationaryAdmittedBatchTimeTrace start horizon omega).map f).sum =
        (stationaryAdmittedBatchTimeTrace start horizon omega).toFinset.sum f :=
      (List.sum_toFinset f hnodup).symm
    _ = ∑ t ∈ stationaryAdmittedBatchTimes start horizon omega, f t := by
      rw [htoFinset]

/-- The chronological trace preserves exact per-category source work totals. -/
theorem sum_stationaryAdmittedBatchTimeTrace_batchAt_eq_totalLedgerWork
    (start horizon : ℝ) (omega : StationaryAdmittedAllClassInput Category)
    (k : Category) :
    ((stationaryAdmittedBatchTimeTrace start horizon omega).map
        (fun t => stationaryAdmittedBatchAt start horizon omega t k)).sum =
      ∑ n ∈ stationaryAdmittedArrivalIndicesBetween start horizon omega k,
        stationaryPoissonWorkRequirement (omega k) n := by
  calc
    ((stationaryAdmittedBatchTimeTrace start horizon omega).map
        (fun t => stationaryAdmittedBatchAt start horizon omega t k)).sum =
        ∑ t ∈ stationaryAdmittedBatchTimes start horizon omega,
          stationaryAdmittedBatchAt start horizon omega t k :=
      sum_stationaryAdmittedBatchTimeTrace_eq_sum_batchTimes start horizon omega
        (fun t => stationaryAdmittedBatchAt start horizon omega t k)
    _ = ∑ n ∈ stationaryAdmittedArrivalIndicesBetween start horizon omega k,
        stationaryPoissonWorkRequirement (omega k) n :=
      sum_stationaryAdmittedBatchAt_eq_totalLedgerWork start horizon omega k

/-- Nonnegative source work marks yield nonnegative exact-time batch work. -/
theorem stationaryAdmittedBatchAt_nonneg
    (start horizon : ℝ) (omega : StationaryAdmittedAllClassInput Category)
    (hwork_nonneg : ∀ k n, 0 ≤ stationaryPoissonWorkRequirement (omega k) n)
    (eventTime : ℝ) (k : Category) :
    0 ≤ stationaryAdmittedBatchAt start horizon omega eventTime k := by
  unfold stationaryAdmittedBatchAt
  exact Finset.sum_nonneg fun n _ => hwork_nonneg k n

/-- On the direct stationary admitted-input law, all literal source work marks
are nonnegative almost surely.  This uses only the source's admitted rates. -/
theorem ae_stationaryAdmittedSourceWork_nonneg
    (M : SLA2026BoroughQueueingInput Category) :
    ∀ᵐ omega ∂(M.stationaryAdmittedAllClassBaseLaw).Pbase,
      ∀ k : Category, ∀ n : ℤ,
        0 ≤ stationaryPoissonWorkRequirement (omega k) n := by
  change ∀ᵐ omega ∂multiclassStationaryPoissonWorkMeasure M.admittedRate,
    ∀ k : Category, ∀ n : ℤ,
      0 ≤ stationaryPoissonWorkRequirement (omega k) n
  filter_upwards [ae_all_multiclassStationaryPoissonWorkRequirement_positive
    M.admittedRate M.admittedRate_pos] with omega hpositive
  intro k n
  exact (hpositive k n).le

/-- Batch work is nonnegative almost surely, uniformly over all finite
interval endpoints and exact event times of the direct stationary input. -/
theorem ae_stationaryAdmittedBatchAt_nonneg
    (M : SLA2026BoroughQueueingInput Category) :
    ∀ᵐ omega ∂(M.stationaryAdmittedAllClassBaseLaw).Pbase,
      ∀ start horizon eventTime : ℝ, ∀ k : Category,
        0 ≤ stationaryAdmittedBatchAt start horizon omega eventTime k := by
  filter_upwards [ae_stationaryAdmittedSourceWork_nonneg M] with omega hnonneg
  intro start horizon eventTime k
  exact stationaryAdmittedBatchAt_nonneg start horizon omega hnonneg eventTime k

/-- Execute the literal stationary source batches through the finite GPS
runner.  This pre-terminal result stops after the last actual source batch;
it deliberately does not claim to reach `horizon`. -/
def stationaryAdmittedFiniteGPSPreTerminalRun
    (start horizon : ℝ) (omega : StationaryAdmittedAllClassInput Category)
    (capacity : ℝ) (weight initialWork : Category → ℝ) :
    FiniteGPSBatchTraceResult Category :=
  finiteGPSRunExternalBatchTrace capacity weight
    (stationaryAdmittedBatchAt start horizon omega) start initialWork
    (stationaryAdmittedExternalBatchTrace start horizon omega)

/-- The finite pre-terminal execution preserves nonnegative workload from a
nonnegative initial state and nonnegative literal source work marks. -/
theorem stationaryAdmittedFiniteGPSPreTerminalRun_workload_nonneg
    (start horizon : ℝ) (omega : StationaryAdmittedAllClassInput Category)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (hinit_nonneg : ∀ k, 0 ≤ initialWork k)
    (hwork_nonneg : ∀ k n, 0 ≤ stationaryPoissonWorkRequirement (omega k) n)
    (k : Category) :
    0 ≤ (stationaryAdmittedFiniteGPSPreTerminalRun start horizon omega capacity weight
      initialWork).workload k := by
  unfold stationaryAdmittedFiniteGPSPreTerminalRun finiteGPSRunExternalBatchTrace
  apply finiteGPSRunBatchTrace_workload_nonneg capacity weight initialWork
    (stationaryAdmittedBatchAt start horizon omega) start
    (stationaryAdmittedExternalBatchTrace start horizon omega).times hinit_nonneg
  intro eventTime heventTime j
  exact stationaryAdmittedBatchAt_nonneg start horizon omega hwork_nonneg eventTime j

/-- The pre-terminal finite GPS execution has the exact balance of initial
work, literal stationary source work on `[start,horizon)`, and stored service. -/
theorem stationaryAdmittedFiniteGPSPreTerminalRun_balance
    (start horizon : ℝ) (omega : StationaryAdmittedAllClassInput Category)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinit_nonneg : ∀ k, 0 ≤ initialWork k)
    (hwork_nonneg : ∀ k n, 0 ≤ stationaryPoissonWorkRequirement (omega k) n)
    (k : Category) :
    (stationaryAdmittedFiniteGPSPreTerminalRun start horizon omega capacity weight
      initialWork).workload k =
      initialWork k +
        ∑ n ∈ stationaryAdmittedArrivalIndicesBetween start horizon omega k,
          stationaryPoissonWorkRequirement (omega k) n -
        (stationaryAdmittedFiniteGPSPreTerminalRun start horizon omega capacity weight
          initialWork).service k := by
  have hbatch_nonneg :
      ∀ eventTime ∈ (stationaryAdmittedExternalBatchTrace start horizon omega).times,
        ∀ j, 0 ≤ stationaryAdmittedBatchAt start horizon omega eventTime j := by
    intro eventTime _ j
    exact stationaryAdmittedBatchAt_nonneg start horizon omega hwork_nonneg eventTime j
  have hbalance := finiteGPSRunExternalBatchTrace_balance capacity weight initialWork
    (stationaryAdmittedBatchAt start horizon omega) start
    (stationaryAdmittedExternalBatchTrace start horizon omega)
    hcapacity hweight_pos htotal_weight_le_one hinit_nonneg hbatch_nonneg k
  have hledger :
      ((stationaryAdmittedExternalBatchTrace start horizon omega).times.map
        fun eventTime => stationaryAdmittedBatchAt start horizon omega eventTime k).sum =
        ∑ n ∈ stationaryAdmittedArrivalIndicesBetween start horizon omega k,
          stationaryPoissonWorkRequirement (omega k) n := by
    exact sum_stationaryAdmittedBatchTimeTrace_batchAt_eq_totalLedgerWork
      start horizon omega k
  rw [hledger] at hbalance
  simpa [stationaryAdmittedFiniteGPSPreTerminalRun] using hbalance

/-- The pre-terminal finite runner never advances beyond `horizon` when its
initial clock is at most `horizon`; source events are strictly before the
horizon by construction. -/
theorem stationaryAdmittedFiniteGPSPreTerminalRun_currentTime_le_horizon
    (start horizon : ℝ) (omega : StationaryAdmittedAllClassInput Category)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon) :
    (stationaryAdmittedFiniteGPSPreTerminalRun start horizon omega capacity weight
      initialWork).currentTime ≤ horizon := by
  unfold stationaryAdmittedFiniteGPSPreTerminalRun
  apply finiteGPSRunExternalBatchTrace_currentTime_le
  · exact hstart_le_horizon
  · intro eventTime heventTime
    exact (stationaryAdmittedExternalBatchTrace_time_lt_horizon
      start horizon omega eventTime heventTime).le

/-- Close the finite source execution through the requested horizon with the
existing zero-work computational fence.  The proof argument documents the
needed chronological relationship; it does not turn the fence into a source
arrival. -/
def stationaryAdmittedFiniteGPSRun
    (start horizon : ℝ) (omega : StationaryAdmittedAllClassInput Category)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (_hstart_le_horizon : start ≤ horizon) : FiniteGPSBatchTraceResult Category :=
  finiteGPSCloseAtHorizon capacity weight
    (stationaryAdmittedFiniteGPSPreTerminalRun start horizon omega capacity weight initialWork)
    horizon

/-- Under the explicit finite GPS hypotheses, the terminal zero-work fence
actually reaches the requested horizon. -/
theorem stationaryAdmittedFiniteGPSRun_currentTime
    (start horizon : ℝ) (omega : StationaryAdmittedAllClassInput Category)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinit_nonneg : ∀ k, 0 ≤ initialWork k)
    (hwork_nonneg : ∀ k n, 0 ≤ stationaryPoissonWorkRequirement (omega k) n) :
    (stationaryAdmittedFiniteGPSRun start horizon omega capacity weight initialWork
      hstart_le_horizon).currentTime = horizon := by
  exact finiteGPSCloseAtHorizon_currentTime capacity weight
    (stationaryAdmittedFiniteGPSPreTerminalRun start horizon omega capacity weight initialWork)
    horizon hcapacity hweight_pos htotal_weight_le_one
    (fun j => stationaryAdmittedFiniteGPSPreTerminalRun_workload_nonneg
      start horizon omega capacity weight initialWork hinit_nonneg hwork_nonneg j)
    (stationaryAdmittedFiniteGPSPreTerminalRun_currentTime_le_horizon
      start horizon omega capacity weight initialWork hstart_le_horizon)

/-- Closing the finite execution preserves nonnegative workload. -/
theorem stationaryAdmittedFiniteGPSRun_workload_nonneg
    (start horizon : ℝ) (omega : StationaryAdmittedAllClassInput Category)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon)
    (hinit_nonneg : ∀ k, 0 ≤ initialWork k)
    (hwork_nonneg : ∀ k n, 0 ≤ stationaryPoissonWorkRequirement (omega k) n)
    (k : Category) :
    0 ≤ (stationaryAdmittedFiniteGPSRun start horizon omega capacity weight initialWork
      hstart_le_horizon).workload k := by
  simpa [stationaryAdmittedFiniteGPSRun] using
    (finiteGPSCloseAtHorizon_workload_nonneg capacity weight
      (stationaryAdmittedFiniteGPSPreTerminalRun start horizon omega capacity weight initialWork)
      horizon
      (fun j => stationaryAdmittedFiniteGPSPreTerminalRun_workload_nonneg
        start horizon omega capacity weight initialWork hinit_nonneg hwork_nonneg j) k)

/-- The terminal fence is operationally exhausted under the same explicit
finite GPS assumptions; its batch has zero work by definition. -/
theorem stationaryAdmittedFiniteGPSRun_horizonFence_terminates
    (start horizon : ℝ) (omega : StationaryAdmittedAllClassInput Category)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinit_nonneg : ∀ k, 0 ≤ initialWork k)
    (hwork_nonneg : ∀ k n, 0 ≤ stationaryPoissonWorkRequirement (omega k) n) :
    (finiteGPSHorizonFence capacity weight
      (stationaryAdmittedFiniteGPSPreTerminalRun start horizon omega capacity weight initialWork)
      horizon).batchApplied = true ∧
      (finiteGPSHorizonFence capacity weight
        (stationaryAdmittedFiniteGPSPreTerminalRun start horizon omega capacity weight initialWork)
        horizon).remainingDelay = 0 := by
  apply finiteGPSHorizonFence_terminates capacity weight
  · exact hcapacity
  · exact hweight_pos
  · exact htotal_weight_le_one
  · intro j
    exact stationaryAdmittedFiniteGPSPreTerminalRun_workload_nonneg
      start horizon omega capacity weight initialWork hinit_nonneg hwork_nonneg j
  · exact stationaryAdmittedFiniteGPSPreTerminalRun_currentTime_le_horizon
      start horizon omega capacity weight initialWork hstart_le_horizon

/-- If the actual pre-fence aggregate workload can be covered by the
remaining source-free horizon interval, the literal stationary source run is
empty at the requested horizon.  This is a deterministic finite reset fact;
the stochastic recurrence of such reset opportunities is a separate
obligation. -/
theorem stationaryAdmittedFiniteGPSRun_workload_eq_zero_of_preTerminalAggregate_le
    (start horizon : ℝ) (omega : StationaryAdmittedAllClassInput Category)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinit_nonneg : ∀ k, 0 ≤ initialWork k)
    (hwork_nonneg : ∀ k n, 0 ≤ stationaryPoissonWorkRequirement (omega k) n)
    (haggregate_le : finiteGPSAggregateWork
      (stationaryAdmittedFiniteGPSPreTerminalRun
        start horizon omega capacity weight initialWork).workload ≤
      capacity * (horizon -
        (stationaryAdmittedFiniteGPSPreTerminalRun
          start horizon omega capacity weight initialWork).currentTime)) :
    ∀ k,
      (stationaryAdmittedFiniteGPSRun start horizon omega capacity weight initialWork
        hstart_le_horizon).workload k = 0 := by
  change ∀ k, (finiteGPSHorizonFence capacity weight
    (stationaryAdmittedFiniteGPSPreTerminalRun
      start horizon omega capacity weight initialWork) horizon).workload k = 0
  apply finiteGPSHorizonFence_workload_eq_zero_of_aggregate_le_capacity_mul
  · exact hcapacity
  · exact hweight_pos
  · exact htotal_weight_le_one
  · intro k
    exact stationaryAdmittedFiniteGPSPreTerminalRun_workload_nonneg
      start horizon omega capacity weight initialWork hinit_nonneg hwork_nonneg k
  · exact stationaryAdmittedFiniteGPSPreTerminalRun_currentTime_le_horizon
      start horizon omega capacity weight initialWork hstart_le_horizon
  · exact haggregate_le

/-- The closed finite source run has the exact workload balance.  The terminal
fence contributes no source work and only adds stored service. -/
theorem stationaryAdmittedFiniteGPSRun_balance
    (start horizon : ℝ) (omega : StationaryAdmittedAllClassInput Category)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinit_nonneg : ∀ k, 0 ≤ initialWork k)
    (hwork_nonneg : ∀ k n, 0 ≤ stationaryPoissonWorkRequirement (omega k) n)
    (k : Category) :
    (stationaryAdmittedFiniteGPSRun start horizon omega capacity weight initialWork
      hstart_le_horizon).workload k =
      initialWork k +
        ∑ n ∈ stationaryAdmittedArrivalIndicesBetween start horizon omega k,
          stationaryPoissonWorkRequirement (omega k) n -
        (stationaryAdmittedFiniteGPSRun start horizon omega capacity weight initialWork
          hstart_le_horizon).service k := by
  have hpre_nonneg : ∀ j,
      0 ≤ (stationaryAdmittedFiniteGPSPreTerminalRun
        start horizon omega capacity weight initialWork).workload j := by
    intro j
    exact stationaryAdmittedFiniteGPSPreTerminalRun_workload_nonneg
      start horizon omega capacity weight initialWork hinit_nonneg hwork_nonneg j
  have hpre_time :
      (stationaryAdmittedFiniteGPSPreTerminalRun
        start horizon omega capacity weight initialWork).currentTime ≤ horizon :=
    stationaryAdmittedFiniteGPSPreTerminalRun_currentTime_le_horizon
      start horizon omega capacity weight initialWork hstart_le_horizon
  have hpre_balance := stationaryAdmittedFiniteGPSPreTerminalRun_balance
    start horizon omega capacity weight initialWork hcapacity hweight_pos
    htotal_weight_le_one hinit_nonneg hwork_nonneg k
  have hfinal := finiteGPSCloseAtHorizon_balance capacity weight
    (stationaryAdmittedFiniteGPSPreTerminalRun start horizon omega capacity weight initialWork)
    horizon hcapacity hweight_pos htotal_weight_le_one hpre_nonneg hpre_time
    (initialWork k)
    (∑ n ∈ stationaryAdmittedArrivalIndicesBetween start horizon omega k,
      stationaryPoissonWorkRequirement (omega k) n)
    k hpre_balance
  simpa [stationaryAdmittedFiniteGPSRun] using hfinal

/-- The concrete interval-segment history for the finite stationary source run
with its zero-work terminal fence. -/
def stationaryAdmittedFiniteGPSRunWithSegments
    (start horizon : ℝ) (omega : StationaryAdmittedAllClassInput Category)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (_hstart_le_horizon : start ≤ horizon) : FiniteGPSBatchSegmentHistory Category :=
  finiteGPSCloseAtHorizonWithSegments capacity weight
    (finiteGPSRunExternalBatchTraceWithSegments capacity weight
      (stationaryAdmittedBatchAt start horizon omega) start initialWork
      (stationaryAdmittedExternalBatchTrace start horizon omega)) horizon

/-- The segment history's final runner result is exactly the ordinary finite
zero-fence closure. -/
theorem stationaryAdmittedFiniteGPSRunWithSegments_final
    (start horizon : ℝ) (omega : StationaryAdmittedAllClassInput Category)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon) :
    (stationaryAdmittedFiniteGPSRunWithSegments start horizon omega capacity weight initialWork
      hstart_le_horizon).final =
      stationaryAdmittedFiniteGPSRun start horizon omega capacity weight initialWork
        hstart_le_horizon := rfl

/-- The full interval-segment ledger records exactly the final finite runner's
stored service, including the zero-work terminal fence segments. -/
theorem stationaryAdmittedFiniteGPSRunWithSegments_service
    (start horizon : ℝ) (omega : StationaryAdmittedAllClassInput Category)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon) (k : Category) :
    finiteGPSExecutionSegmentsService
      (stationaryAdmittedFiniteGPSRunWithSegments start horizon omega capacity weight
        initialWork hstart_le_horizon).segments k =
      (stationaryAdmittedFiniteGPSRunWithSegments start horizon omega capacity weight
        initialWork hstart_le_horizon).final.service k := by
  apply finiteGPSCloseAtHorizonWithSegments_segments_service_eq_final
  intro j
  simpa [finiteGPSRunExternalBatchTraceWithSegments] using
    (finiteGPSRunBatchTraceWithSegments_service capacity weight initialWork
      (stationaryAdmittedBatchAt start horizon omega) start
      (stationaryAdmittedExternalBatchTrace start horizon omega).times j)

/-- Every terminal-fence segment carries zero endpoint batch work.  This
separates the computational horizon closure from exact stationary source jobs. -/
theorem stationaryAdmittedFiniteGPSRunWithSegments_fence_endpointBatch_zero
    (start horizon : ℝ) (omega : StationaryAdmittedAllClassInput Category)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon) :
    ∀ segment ∈ finiteGPSHorizonFenceSegments capacity weight
      (stationaryAdmittedFiniteGPSPreTerminalRun start horizon omega capacity weight initialWork)
      horizon, ∀ k, segment.endpointBatch k = 0 := by
  exact finiteGPSHorizonFenceSegments_forall_endpointBatch_eq_zero
    capacity weight
    (stationaryAdmittedFiniteGPSPreTerminalRun start horizon omega capacity weight initialWork)
    horizon

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements

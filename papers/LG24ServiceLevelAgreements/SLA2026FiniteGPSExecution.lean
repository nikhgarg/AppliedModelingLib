import AppliedModelingLib.Queueing.GPS.FiniteHorizon.BatchTrace
import LG24ServiceLevelAgreements.SLA2026StochasticPrimitives
import Mathlib.Tactic

/-!
# Finite batch-event GPS execution for the active SLA input

This module connects the active paper's directly constructed admitted Poisson
streams and exponential work marks to the finite GPS runner. It deliberately
uses `admittedWorkPrimitiveMeasure`, whose raw-arrival coordinate already has
the admitted rate `s`; it does not run the queue on raw arrivals followed by
an unproved pathwise thinning equivalence.

For a fixed finite horizon, each category contributes its finite admitted
arrival ledger. All jobs with the same time are aggregated into one batch
vector, including deterministic cross-category ties. The batch-time list is a
sorted finite set, hence each exact-time fiber is applied exactly once.

No stationary, Palm, infinite-horizon, or response-tail result is claimed.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open scoped BigOperators NNReal

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- The finite ledger of admitted raw indices in the half-open interval
`(start, horizon]`. Work before `start` is represented by the runner's input
state rather than replayed as a new arrival batch. -/
def admittedWorkArrivalIndicesBetween
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (k : Category) : Finset ℕ :=
  (M.admittedWorkArrivalIndices k horizon omega).filter fun n =>
    start < arrivalTime n
      (multiclassForwardQueueingPrimitiveRawInterarrivals k omega) ∧
    arrivalTime n
      (multiclassForwardQueueingPrimitiveRawInterarrivals k omega) ≤ horizon

/-- All distinct admitted-arrival epochs in `(start, horizon]`, read from the
direct admitted-arrival/work carrier. -/
def admittedWorkBatchTimes
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) : Finset ℝ :=
  (Finset.univ : Finset Category).biUnion fun k =>
    (M.admittedWorkArrivalIndicesBetween start horizon omega k).image fun n =>
      arrivalTime n (multiclassForwardQueueingPrimitiveRawInterarrivals k omega)

/-- Chronological, duplicate-free external event times. Duplicate times from
different categories are intentionally collapsed, so their work is handled as
one simultaneous batch. -/
def admittedWorkBatchTimeTrace
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) : List ℝ :=
  (M.admittedWorkBatchTimes start horizon omega).sort (fun s t : ℝ => s ≤ t)

/-- The actual admitted workload arriving to each category at one exact event
time. It is a sum over the finite source ledger, not an abstract batch input. -/
def admittedWorkBatchAt
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (eventTime : ℝ) :
    Category → ℝ :=
  fun k => ∑ n ∈ M.admittedWorkArrivalIndicesBetween start horizon omega k with
    arrivalTime n (multiclassForwardQueueingPrimitiveRawInterarrivals k omega) = eventTime,
    M.admittedWorkRequirement k n omega

/-- A finite source batch trace is a valid GPS trace because the ledger keeps
only epochs in `(start, horizon]`.  The deterministic runner receives both
endpoint bounds as constructed data, rather than relying on an unstated
source-path regularity condition. -/
def admittedWorkExternalBatchTrace
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) :
    FiniteGPSExternalBatchTrace start where
  times := M.admittedWorkBatchTimeTrace start horizon omega
  chronological :=
    finiteGPSChronologicalFrom_of_pairwise_le start
      (M.admittedWorkBatchTimeTrace start horizon omega)
      (by
        intro t ht
        have htime : t ∈ M.admittedWorkBatchTimes start horizon omega :=
          (Finset.mem_sort (fun s t : ℝ => s ≤ t)).mp ht
        rcases Finset.mem_biUnion.mp htime with ⟨k, _hk, himage⟩
        rcases Finset.mem_image.mp himage with ⟨n, hn, rfl⟩
        exact (Finset.mem_filter.mp hn).2.1.le)
      (Finset.pairwise_sort (M.admittedWorkBatchTimes start horizon omega)
        (fun s t : ℝ => s ≤ t))
  nodup := Finset.sort_nodup (M.admittedWorkBatchTimes start horizon omega)
    (fun s t : ℝ => s ≤ t)

omit [DecidableEq Category] in
/-- Every source-derived external batch time is at most the requested finite
horizon, by the ledger's explicit upper-endpoint filter. -/
theorem admittedWorkExternalBatchTrace_time_le_horizon
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (eventTime : ℝ)
    (heventTime : eventTime ∈
      (M.admittedWorkExternalBatchTrace start horizon omega).times) :
    eventTime ≤ horizon := by
  have htime : eventTime ∈ M.admittedWorkBatchTimes start horizon omega :=
    (Finset.mem_sort (fun s t : ℝ => s ≤ t)).mp heventTime
  rcases Finset.mem_biUnion.mp htime with ⟨k, _hk, himage⟩
  rcases Finset.mem_image.mp himage with ⟨n, hn, rfl⟩
  exact (Finset.mem_filter.mp hn).2.2

omit [DecidableEq Category] in
/-- Every per-category admitted work mark in the finite ledger occurs in
exactly one external batch fiber. This is the source-faithful conservation
identity used by the finite trace balance. -/
theorem sum_admittedWorkBatchAt_eq_totalLedgerWork
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (k : Category) :
    ∑ t ∈ M.admittedWorkBatchTimes start horizon omega,
      M.admittedWorkBatchAt start horizon omega t k =
      ∑ n ∈ M.admittedWorkArrivalIndicesBetween start horizon omega k,
        M.admittedWorkRequirement k n omega := by
  apply Finset.sum_fiberwise_of_maps_to
  · intro n hn
    apply Finset.mem_biUnion.mpr
    refine ⟨k, Finset.mem_univ _, ?_⟩
    exact Finset.mem_image.mpr ⟨n, hn, rfl⟩

omit [DecidableEq Category] in
/-- The sorted batch-time trace has the same finite sum as its underlying
finite set. -/
theorem sum_admittedWorkBatchTimeTrace_eq_sum_batchTimes
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (f : ℝ → ℝ) :
    ((M.admittedWorkBatchTimeTrace start horizon omega).map f).sum =
      ∑ t ∈ M.admittedWorkBatchTimes start horizon omega, f t := by
  have hnodup : (M.admittedWorkBatchTimeTrace start horizon omega).Nodup :=
    Finset.sort_nodup (M.admittedWorkBatchTimes start horizon omega)
      (fun s t : ℝ => s ≤ t)
  have htoFinset : (M.admittedWorkBatchTimeTrace start horizon omega).toFinset =
      M.admittedWorkBatchTimes start horizon omega := by
    ext t
    simp [admittedWorkBatchTimeTrace]
  calc
    ((M.admittedWorkBatchTimeTrace start horizon omega).map f).sum =
        (M.admittedWorkBatchTimeTrace start horizon omega).toFinset.sum f :=
      (List.sum_toFinset f hnodup).symm
    _ = ∑ t ∈ M.admittedWorkBatchTimes start horizon omega, f t := by
      rw [htoFinset]

omit [DecidableEq Category] in
/-- The trace's category-wise batch sum preserves every actual admitted work
mark in `(start, horizon]`. -/
theorem sum_admittedWorkBatchTimeTrace_batchAt_eq_totalLedgerWork
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (k : Category) :
    ((M.admittedWorkBatchTimeTrace start horizon omega).map
        (fun t => M.admittedWorkBatchAt start horizon omega t k)).sum =
      ∑ n ∈ M.admittedWorkArrivalIndicesBetween start horizon omega k,
        M.admittedWorkRequirement k n omega := by
  calc
    ((M.admittedWorkBatchTimeTrace start horizon omega).map
        (fun t => M.admittedWorkBatchAt start horizon omega t k)).sum =
        ∑ t ∈ M.admittedWorkBatchTimes start horizon omega,
          M.admittedWorkBatchAt start horizon omega t k :=
      M.sum_admittedWorkBatchTimeTrace_eq_sum_batchTimes start horizon omega
        (fun t => M.admittedWorkBatchAt start horizon omega t k)
    _ = ∑ n ∈ M.admittedWorkArrivalIndicesBetween start horizon omega k,
        M.admittedWorkRequirement k n omega :=
      M.sum_admittedWorkBatchAt_eq_totalLedgerWork start horizon omega k

omit [DecidableEq Category] in
/-- Nonnegative source work marks give nonnegative exact-time batch work. -/
theorem admittedWorkBatchAt_nonneg
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath)
    (hwork_nonneg : ∀ k n, 0 ≤ M.admittedWorkRequirement k n omega)
    (eventTime : ℝ) (k : Category) :
    0 ≤ M.admittedWorkBatchAt start horizon omega eventTime k := by
  unfold admittedWorkBatchAt
  exact Finset.sum_nonneg fun n _ => hwork_nonneg k n

omit [DecidableEq Category] in
/-- The direct admitted-carrier ledger has its intended `(start, horizon]`
semantics simultaneously for all classes and all real interval endpoints. -/
theorem ae_mem_admittedWorkArrivalIndicesBetween_iff
    (M : SLA2026BoroughQueueingInput Category) :
    ∀ᵐ omega ∂M.admittedWorkPrimitiveMeasure,
      ∀ k : Category, ∀ start horizon : ℝ, ∀ n : ℕ,
        n ∈ M.admittedWorkArrivalIndicesBetween start horizon omega k ↔
          start < arrivalTime n
            (multiclassForwardQueueingPrimitiveRawInterarrivals k omega) ∧
          arrivalTime n
            (multiclassForwardQueueingPrimitiveRawInterarrivals k omega) ≤ horizon := by
  filter_upwards [M.ae_mem_admittedWorkArrivalIndices_iff] with omega hledger
  intro k start horizon n
  simp only [admittedWorkArrivalIndicesBetween, Finset.mem_filter]
  rw [hledger k horizon n]
  constructor
  · rintro ⟨_horizon_bound, start_bound, horizon_bound⟩
    exact ⟨start_bound, horizon_bound⟩
  · rintro ⟨start_bound, horizon_bound⟩
    exact ⟨horizon_bound, start_bound, horizon_bound⟩

omit [DecidableEq Category] in
/-- Batch work is nonnegative almost surely on the direct admitted
Poisson/work carrier, uniformly over all finite interval endpoints and event
times. -/
theorem ae_admittedWorkBatchAt_nonneg
    (M : SLA2026BoroughQueueingInput Category) :
    ∀ᵐ omega ∂M.admittedWorkPrimitiveMeasure,
      ∀ start horizon eventTime : ℝ, ∀ k : Category,
        0 ≤ M.admittedWorkBatchAt start horizon omega eventTime k := by
  filter_upwards [M.ae_all_admittedWorkRequirements_positive] with omega hpositive
  intro start horizon eventTime k
  exact M.admittedWorkBatchAt_nonneg start horizon omega
    (fun j n => (hpositive j n).le) eventTime k

/-- Execute the concrete admitted-work batches through the bounded GPS runner.
This helper intentionally stops at the last actual source batch (or `start`
when there is none), so it is useful as the pre-terminal portion of a
finite-horizon execution but is not itself a run through `horizon`. -/
def admittedWorkFiniteGPSPreTerminalRun
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (capacity : ℝ)
    (weight initialWork : Category → ℝ) : FiniteGPSBatchTraceResult Category :=
  finiteGPSRunExternalBatchTrace capacity weight
    (M.admittedWorkBatchAt start horizon omega) start initialWork
    (M.admittedWorkExternalBatchTrace start horizon omega)

/-- The pre-terminal source execution preserves nonnegative workloads when
both its initial state and its actual work marks are nonnegative. -/
theorem admittedWorkFiniteGPSPreTerminalRun_workload_nonneg
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (capacity : ℝ)
    (weight initialWork : Category → ℝ)
    (hinit_nonneg : ∀ k, 0 ≤ initialWork k)
    (hwork_nonneg : ∀ k n, 0 ≤ M.admittedWorkRequirement k n omega)
    (k : Category) :
    0 ≤ (M.admittedWorkFiniteGPSPreTerminalRun start horizon omega capacity weight initialWork).workload k := by
  unfold admittedWorkFiniteGPSPreTerminalRun finiteGPSRunExternalBatchTrace
  apply finiteGPSRunBatchTrace_workload_nonneg capacity weight initialWork
    (M.admittedWorkBatchAt start horizon omega) start
    (M.admittedWorkExternalBatchTrace start horizon omega).times hinit_nonneg
  intro eventTime heventTime j
  exact M.admittedWorkBatchAt_nonneg start horizon omega hwork_nonneg eventTime j

/-- The pre-terminal GPS execution telescopes every actual admitted work increment
from the direct source ledger.  Positive capacity and GPS weights are explicit
because they justify that each external batch is reached after at most one more
than the currently active-class count of internal emptying events. -/
theorem admittedWorkFiniteGPSPreTerminalRun_balance
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (capacity : ℝ)
    (weight initialWork : Category → ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinit_nonneg : ∀ k, 0 ≤ initialWork k)
    (hwork_nonneg : ∀ k n, 0 ≤ M.admittedWorkRequirement k n omega)
    (k : Category) :
    (M.admittedWorkFiniteGPSPreTerminalRun start horizon omega capacity weight initialWork).workload k =
      initialWork k +
        ∑ n ∈ M.admittedWorkArrivalIndicesBetween start horizon omega k,
          M.admittedWorkRequirement k n omega -
        (M.admittedWorkFiniteGPSPreTerminalRun start horizon omega capacity weight initialWork).service k := by
  have hbatch_nonneg :
      ∀ eventTime ∈ (M.admittedWorkExternalBatchTrace start horizon omega).times,
        ∀ j, 0 ≤ M.admittedWorkBatchAt start horizon omega eventTime j := by
    intro eventTime _ j
    exact M.admittedWorkBatchAt_nonneg start horizon omega hwork_nonneg eventTime j
  have hbalance := finiteGPSRunExternalBatchTrace_balance capacity weight initialWork
    (M.admittedWorkBatchAt start horizon omega) start
    (M.admittedWorkExternalBatchTrace start horizon omega)
    hcapacity hweight_pos htotal_weight_le_one hinit_nonneg hbatch_nonneg k
  have hledger :
      ((M.admittedWorkExternalBatchTrace start horizon omega).times.map
        fun eventTime => M.admittedWorkBatchAt start horizon omega eventTime k).sum =
        ∑ n ∈ M.admittedWorkArrivalIndicesBetween start horizon omega k,
          M.admittedWorkRequirement k n omega := by
    exact M.sum_admittedWorkBatchTimeTrace_batchAt_eq_totalLedgerWork
      start horizon omega k
  rw [hledger] at hbalance
  simpa [admittedWorkFiniteGPSPreTerminalRun] using hbalance

/-- The pre-terminal runner's clock cannot exceed the requested horizon when
`start ≤ horizon`: every actual source batch is explicitly filtered into
`(start, horizon]`. -/
theorem admittedWorkFiniteGPSPreTerminalRun_currentTime_le_horizon
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (capacity : ℝ)
    (weight initialWork : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon) :
    (M.admittedWorkFiniteGPSPreTerminalRun start horizon omega capacity weight initialWork).currentTime ≤
      horizon := by
  unfold admittedWorkFiniteGPSPreTerminalRun
  apply finiteGPSRunExternalBatchTrace_currentTime_le
  · exact hstart_le_horizon
  · intro eventTime heventTime
    exact M.admittedWorkExternalBatchTrace_time_le_horizon
      start horizon omega eventTime heventTime

/-- Execute the admitted source ledger through the requested finite horizon.
After the final actual source batch, `finiteGPSCloseAtHorizon` inserts a
computational terminal horizon fence carrying the zero workload vector.  That
fence is not an external arrival and has no source-event metadata.  The
explicit `start ≤ horizon` condition makes its service duration nonnegative;
the termination theorem below supplies the additional GPS conditions under
which this bounded fence computation operationally reaches that endpoint. -/
def admittedWorkFiniteGPSRun
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (capacity : ℝ)
    (weight initialWork : Category → ℝ)
    (_hstart_le_horizon : start ≤ horizon) : FiniteGPSBatchTraceResult Category :=
  finiteGPSCloseAtHorizon capacity weight
    (M.admittedWorkFiniteGPSPreTerminalRun start horizon omega capacity weight initialWork)
    horizon

/-- Under the explicit GPS conditions, the source-facing finite-horizon
execution reaches the requested clock endpoint, including service after the
last admitted arrival.  Without these conditions the underlying closure keeps
its actual partially reached clock instead. -/
theorem admittedWorkFiniteGPSRun_currentTime
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (capacity : ℝ)
    (weight initialWork : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinit_nonneg : ∀ k, 0 ≤ initialWork k)
    (hwork_nonneg : ∀ k n, 0 ≤ M.admittedWorkRequirement k n omega) :
    (M.admittedWorkFiniteGPSRun start horizon omega capacity weight initialWork
      hstart_le_horizon).currentTime = horizon := by
  exact finiteGPSCloseAtHorizon_currentTime capacity weight
    (M.admittedWorkFiniteGPSPreTerminalRun start horizon omega capacity weight initialWork)
    horizon hcapacity hweight_pos htotal_weight_le_one
    (fun j => M.admittedWorkFiniteGPSPreTerminalRun_workload_nonneg
      start horizon omega capacity weight initialWork hinit_nonneg hwork_nonneg j)
    (M.admittedWorkFiniteGPSPreTerminalRun_currentTime_le_horizon
      start horizon omega capacity weight initialWork hstart_le_horizon)

/-- The full finite-horizon source execution preserves nonnegative workloads
when both the initial state and all actual admitted work marks are
nonnegative. -/
theorem admittedWorkFiniteGPSRun_workload_nonneg
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (capacity : ℝ)
    (weight initialWork : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon)
    (hinit_nonneg : ∀ k, 0 ≤ initialWork k)
    (hwork_nonneg : ∀ k n, 0 ≤ M.admittedWorkRequirement k n omega)
    (k : Category) :
    0 ≤ (M.admittedWorkFiniteGPSRun start horizon omega capacity weight initialWork
      hstart_le_horizon).workload k := by
  simpa [admittedWorkFiniteGPSRun] using
    (finiteGPSCloseAtHorizon_workload_nonneg capacity weight
      (M.admittedWorkFiniteGPSPreTerminalRun start horizon omega capacity weight initialWork)
      horizon
      (fun j => M.admittedWorkFiniteGPSPreTerminalRun_workload_nonneg
        start horizon omega capacity weight initialWork hinit_nonneg hwork_nonneg j) k)

/-- Under the ordinary positive-GPS hypotheses, the computational terminal
horizon fence is actually reached after its bounded internal emptying steps.
Together with `admittedWorkFiniteGPSRun_currentTime`, this makes the recorded
endpoint operational rather than merely a field assignment. -/
theorem admittedWorkFiniteGPSRun_horizonFence_terminates
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (capacity : ℝ)
    (weight initialWork : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinit_nonneg : ∀ k, 0 ≤ initialWork k)
    (hwork_nonneg : ∀ k n, 0 ≤ M.admittedWorkRequirement k n omega) :
    (finiteGPSHorizonFence capacity weight
      (M.admittedWorkFiniteGPSPreTerminalRun start horizon omega capacity weight initialWork)
      horizon).batchApplied = true ∧
      (finiteGPSHorizonFence capacity weight
        (M.admittedWorkFiniteGPSPreTerminalRun start horizon omega capacity weight initialWork)
        horizon).remainingDelay = 0 := by
  apply finiteGPSHorizonFence_terminates capacity weight
  · exact hcapacity
  · exact hweight_pos
  · exact htotal_weight_le_one
  · intro j
    exact M.admittedWorkFiniteGPSPreTerminalRun_workload_nonneg
      start horizon omega capacity weight initialWork hinit_nonneg hwork_nonneg j
  · exact M.admittedWorkFiniteGPSPreTerminalRun_currentTime_le_horizon
      start horizon omega capacity weight initialWork hstart_le_horizon

/-- The horizon-closing source run both records and operationally reaches the
requested finite endpoint. -/
theorem admittedWorkFiniteGPSRun_reaches_horizon
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (capacity : ℝ)
    (weight initialWork : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinit_nonneg : ∀ k, 0 ≤ initialWork k)
    (hwork_nonneg : ∀ k n, 0 ≤ M.admittedWorkRequirement k n omega) :
    (M.admittedWorkFiniteGPSRun start horizon omega capacity weight initialWork
      hstart_le_horizon).currentTime = horizon ∧
      (finiteGPSHorizonFence capacity weight
        (M.admittedWorkFiniteGPSPreTerminalRun start horizon omega capacity weight initialWork)
        horizon).batchApplied = true ∧
        (finiteGPSHorizonFence capacity weight
          (M.admittedWorkFiniteGPSPreTerminalRun start horizon omega capacity weight initialWork)
          horizon).remainingDelay = 0 := by
  constructor
  · exact M.admittedWorkFiniteGPSRun_currentTime
      start horizon omega capacity weight initialWork hstart_le_horizon
      hcapacity hweight_pos htotal_weight_le_one hinit_nonneg hwork_nonneg
  · exact M.admittedWorkFiniteGPSRun_horizonFence_terminates
      start horizon omega capacity weight initialWork hstart_le_horizon
      hcapacity hweight_pos htotal_weight_le_one hinit_nonneg hwork_nonneg

/-- The full finite-horizon execution has the exact source-work balance.  The
terminal horizon fence contributes zero work and only adds its accrued GPS
service to the cumulative service ledger. -/
theorem admittedWorkFiniteGPSRun_balance
    (M : SLA2026BoroughQueueingInput Category) (start horizon : ℝ)
    (omega : Category → ForwardQueueingPrimitivePath) (capacity : ℝ)
    (weight initialWork : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinit_nonneg : ∀ k, 0 ≤ initialWork k)
    (hwork_nonneg : ∀ k n, 0 ≤ M.admittedWorkRequirement k n omega)
    (k : Category) :
    (M.admittedWorkFiniteGPSRun start horizon omega capacity weight initialWork
      hstart_le_horizon).workload k =
      initialWork k +
        ∑ n ∈ M.admittedWorkArrivalIndicesBetween start horizon omega k,
          M.admittedWorkRequirement k n omega -
        (M.admittedWorkFiniteGPSRun start horizon omega capacity weight initialWork
          hstart_le_horizon).service k := by
  have hpre_nonneg : ∀ j,
      0 ≤ (M.admittedWorkFiniteGPSPreTerminalRun
        start horizon omega capacity weight initialWork).workload j := by
    intro j
    exact M.admittedWorkFiniteGPSPreTerminalRun_workload_nonneg
      start horizon omega capacity weight initialWork hinit_nonneg hwork_nonneg j
  have hpre_time :
      (M.admittedWorkFiniteGPSPreTerminalRun
        start horizon omega capacity weight initialWork).currentTime ≤ horizon :=
    M.admittedWorkFiniteGPSPreTerminalRun_currentTime_le_horizon
      start horizon omega capacity weight initialWork hstart_le_horizon
  have hpre_balance := M.admittedWorkFiniteGPSPreTerminalRun_balance
    start horizon omega capacity weight initialWork hcapacity hweight_pos
    htotal_weight_le_one hinit_nonneg hwork_nonneg k
  have hfinal := finiteGPSCloseAtHorizon_balance capacity weight
    (M.admittedWorkFiniteGPSPreTerminalRun start horizon omega capacity weight initialWork)
    horizon hcapacity hweight_pos htotal_weight_le_one hpre_nonneg hpre_time
    (initialWork k)
    (∑ n ∈ M.admittedWorkArrivalIndicesBetween start horizon omega k,
      M.admittedWorkRequirement k n omega)
    k hpre_balance
  simpa [admittedWorkFiniteGPSRun] using hfinal

/-- On the directly constructed admitted Poisson/work carrier, the full
finite-horizon execution's exact balance holds almost surely. -/
theorem ae_admittedWorkFiniteGPSRun_balance
    (M : SLA2026BoroughQueueingInput Category) (start horizon capacity : ℝ)
    (weight initialWork : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinit_nonneg : ∀ k, 0 ≤ initialWork k) :
    ∀ᵐ omega ∂M.admittedWorkPrimitiveMeasure,
      ∀ k : Category,
        (M.admittedWorkFiniteGPSRun start horizon omega capacity weight initialWork
          hstart_le_horizon).workload k =
          initialWork k +
            ∑ n ∈ M.admittedWorkArrivalIndicesBetween start horizon omega k,
              M.admittedWorkRequirement k n omega -
            (M.admittedWorkFiniteGPSRun start horizon omega capacity weight initialWork
              hstart_le_horizon).service k := by
  filter_upwards [M.ae_all_admittedWorkRequirements_positive] with omega hpositive
  intro k
  exact M.admittedWorkFiniteGPSRun_balance start horizon omega capacity weight initialWork
    hstart_le_horizon hcapacity hweight_pos htotal_weight_le_one hinit_nonneg
    (fun j n => (hpositive j n).le) k

/-- On the direct admitted carrier, the finite-horizon runner operationally
reaches its terminal horizon fence almost surely. -/
theorem ae_admittedWorkFiniteGPSRun_reaches_horizon
    (M : SLA2026BoroughQueueingInput Category) (start horizon capacity : ℝ)
    (weight initialWork : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinit_nonneg : ∀ k, 0 ≤ initialWork k) :
    ∀ᵐ omega ∂M.admittedWorkPrimitiveMeasure,
      (M.admittedWorkFiniteGPSRun start horizon omega capacity weight initialWork
        hstart_le_horizon).currentTime = horizon ∧
        (finiteGPSHorizonFence capacity weight
          (M.admittedWorkFiniteGPSPreTerminalRun
            start horizon omega capacity weight initialWork)
          horizon).batchApplied = true ∧
          (finiteGPSHorizonFence capacity weight
            (M.admittedWorkFiniteGPSPreTerminalRun
              start horizon omega capacity weight initialWork)
            horizon).remainingDelay = 0 := by
  filter_upwards [M.ae_all_admittedWorkRequirements_positive] with omega hpositive
  exact M.admittedWorkFiniteGPSRun_reaches_horizon
    start horizon omega capacity weight initialWork hstart_le_horizon
    hcapacity hweight_pos htotal_weight_le_one hinit_nonneg
    (fun j n => (hpositive j n).le)

/-- On the direct admitted carrier, the full finite-horizon execution keeps
every category workload nonnegative almost surely. -/
theorem ae_admittedWorkFiniteGPSRun_workload_nonneg
    (M : SLA2026BoroughQueueingInput Category) (start horizon capacity : ℝ)
    (weight initialWork : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon)
    (hinit_nonneg : ∀ k, 0 ≤ initialWork k) :
    ∀ᵐ omega ∂M.admittedWorkPrimitiveMeasure,
      ∀ k : Category,
        0 ≤ (M.admittedWorkFiniteGPSRun start horizon omega capacity weight initialWork
          hstart_le_horizon).workload k := by
  filter_upwards [M.ae_all_admittedWorkRequirements_positive] with omega hpositive
  intro k
  exact M.admittedWorkFiniteGPSRun_workload_nonneg
    start horizon omega capacity weight initialWork hstart_le_horizon hinit_nonneg
    (fun j n => (hpositive j n).le) k

/-- On the directly constructed admitted Poisson/work carrier, the
pre-terminal execution balance holds almost surely, simultaneously for all
finite interval endpoints and all categories. -/
theorem ae_admittedWorkFiniteGPSPreTerminalRun_balance
    (M : SLA2026BoroughQueueingInput Category) (start horizon capacity : ℝ)
    (weight initialWork : Category → ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinit_nonneg : ∀ k, 0 ≤ initialWork k) :
    ∀ᵐ omega ∂M.admittedWorkPrimitiveMeasure,
      ∀ k : Category,
        (M.admittedWorkFiniteGPSPreTerminalRun start horizon omega capacity weight initialWork).workload k =
          initialWork k +
            ∑ n ∈ M.admittedWorkArrivalIndicesBetween start horizon omega k,
              M.admittedWorkRequirement k n omega -
            (M.admittedWorkFiniteGPSPreTerminalRun start horizon omega capacity weight initialWork).service k := by
  filter_upwards [M.ae_all_admittedWorkRequirements_positive] with omega hpositive
  intro k
  exact M.admittedWorkFiniteGPSPreTerminalRun_balance start horizon omega capacity weight initialWork
    hcapacity hweight_pos htotal_weight_le_one hinit_nonneg
    (fun j n => (hpositive j n).le) k

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements

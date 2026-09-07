import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedPastNetCandidates
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedResetPartition
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.LateBatchTrace
import Mathlib.Tactic

/-!
# A literal global past cutoff for the SLA aggregate input

This module turns the source-only aggregate negative-drift fact into a finite
physical-time maximizer.  The selected lower endpoint is either an actual
source batch epoch in one finite past window or the terminal boundary `0`.
It maximizes the literal half-open source net-work ledger over *all* past
lower endpoints.  In particular, this is not a virtual endpoint batch, a
queue state, or a claimed GPS reset: relating this scalar cutoff to the real
chronological GPS execution remains a separate obligation.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability
open AppliedModelingLib.Probability.Palm
open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ProbabilityTheory BigOperators

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- Membership in the finite cutoff candidate list is exactly either a
literal source batch boundary or its separately recorded terminal boundary.
The second disjunct is not a source-event assertion. -/
theorem mem_taggedAdmittedPastBoundaryCandidates_iff
    (start horizon r : Real) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) :
    r ∈ taggedAdmittedPastBoundaryCandidates start horizon target z ↔
      r ∈ taggedAdmittedBatchTimeTrace start horizon target z ∨ r = horizon := by
  simp [taggedAdmittedPastBoundaryCandidates]

/-- Exact additivity of the literal aggregate source ledger across a half-open
physical-time split.  In particular, a source batch exactly at `resetTime`
belongs only to the right summand. -/
theorem taggedAdmittedSourceAggregateLedgerWork_reset_partition
    (start resetTime horizon : Real) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hstart_reset : start ≤ resetTime) (hreset_horizon : resetTime ≤ horizon) :
    taggedAdmittedSourceAggregateLedgerWork start horizon target z =
      taggedAdmittedSourceAggregateLedgerWork start resetTime target z +
        taggedAdmittedSourceAggregateLedgerWork resetTime horizon target z := by
  unfold taggedAdmittedSourceAggregateLedgerWork
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.sum_union
    (taggedAdmittedArrivalIndicesBetween_reset_disjoint
      start resetTime horizon target z htarget_good k),
    ← taggedAdmittedArrivalIndicesBetween_reset_partition
      start resetTime horizon target z htarget_good hstart_reset hreset_horizon k]

/-- The corresponding source net-work ledger is exactly additive across a
half-open split.  This is an accounting identity only; it does not invoke a
queue recursion or silently treat the right endpoint as a batch. -/
theorem taggedAdmittedSourceNetWork_reset_partition
    (start resetTime horizon : Real) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (capacity : Real)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hstart_reset : start ≤ resetTime) (hreset_horizon : resetTime ≤ horizon) :
    taggedAdmittedSourceNetWork start horizon target z capacity =
      taggedAdmittedSourceNetWork start resetTime target z capacity +
        taggedAdmittedSourceNetWork resetTime horizon target z capacity := by
  unfold taggedAdmittedSourceNetWork
  rw [taggedAdmittedSourceAggregateLedgerWork_reset_partition
    start resetTime horizon target z htarget_good hstart_reset hreset_horizon]
  ring

/-- If the literal aggregate input net work over `[-t, 0)` tends to `-∞`,
then some finite source boundary globally maximizes the same net work viewed
as a function of its physical lower endpoint.  The selected boundary belongs
to the actual chronological source trace in `[start, 0)`, or is the terminal
boundary `0`; no synthetic arrival is inserted at either endpoint.

This is a scalar source-ledger theorem only.  It makes no claim that the GPS
workload is zero at the selected boundary. -/
theorem exists_taggedAdmittedPastGlobalNetCutoff_of_tendsto_atBot
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (capacity : Real)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hcapacity_nonneg : 0 ≤ capacity)
    (hlim : Tendsto
      (fun t : Real =>
        stationaryAdmittedTargetPassivePastAggregateWork target z t - capacity * t)
      atTop atBot) :
    ∃ start r,
      start ≤ 0 ∧
      r ∈ taggedAdmittedPastBoundaryCandidates start 0 target z ∧
      start ≤ r ∧ r ≤ 0 ∧
      ∀ u : Real, u ≤ 0 →
        stationaryAdmittedTargetPassivePastAggregateWork target z (-u) -
            capacity * (-u) ≤
          stationaryAdmittedTargetPassivePastAggregateWork target z (-r) -
            capacity * (-r) := by
  let net : Real → Real := fun u =>
    stationaryAdmittedTargetPassivePastAggregateWork target z (-u) - capacity * (-u)
  have hlim_net : Tendsto (fun t : Real => net (-t)) atTop atBot := by
    simpa [net] using hlim
  have htail_eventually : ∀ᶠ t : Real in atTop, net (-t) ≤ net 0 :=
    Filter.tendsto_atBot.1 hlim_net (net 0)
  rcases Filter.eventually_atTop.mp htail_eventually with ⟨R, hR⟩
  let T : Real := max 0 R
  have hT_nonneg : 0 ≤ T := by
    exact le_max_left _ _
  have htail : ∀ t : Real, T ≤ t → net (-t) ≤ net 0 := by
    intro t ht
    exact hR t ((le_max_right _ _).trans ht)
  let start : Real := -T
  let candidates : Finset Real :=
    (taggedAdmittedPastBoundaryCandidates start 0 target z).toFinset
  let values : Finset Real := candidates.image net
  have hzero_candidate : (0 : Real) ∈ candidates := by
    simp [candidates, taggedAdmittedPastBoundaryCandidates]
  have hvalues_nonempty : values.Nonempty := by
    refine ⟨net 0, ?_⟩
    exact Finset.mem_image.mpr ⟨0, hzero_candidate, rfl⟩
  let maximum : Real := values.max' hvalues_nonempty
  have hmaximum_mem : maximum ∈ values := by
    exact Finset.max'_mem values hvalues_nonempty
  rcases Finset.mem_image.mp hmaximum_mem with ⟨r, hr_candidate, hr_maximum⟩
  have hr_candidate_list : r ∈ taggedAdmittedPastBoundaryCandidates start 0 target z := by
    simpa [candidates] using hr_candidate
  have hr_boundary :
      r ∈ taggedAdmittedBatchTimeTrace start 0 target z ∨ r = 0 := by
    exact (mem_taggedAdmittedPastBoundaryCandidates_iff start 0 r target z).mp
      hr_candidate_list
  have hr_start : start ≤ r := by
    rcases hr_boundary with hr_trace | rfl
    · exact finiteGPSChronologicalFrom_start_le start
        (taggedAdmittedBatchTimeTrace start 0 target z)
        (taggedAdmittedExternalBatchTrace start 0 target z htarget_good).chronological
        r hr_trace
    · simp [start, hT_nonneg]
  have hr_zero : r ≤ 0 := by
    rcases hr_boundary with hr_trace | rfl
    · exact (taggedAdmittedExternalBatchTrace_time_lt_horizon
        start 0 target z htarget_good r (by
          simpa [taggedAdmittedExternalBatchTrace] using hr_trace)).le
    · rfl
  refine ⟨start, r, ?_, hr_candidate_list, hr_start, hr_zero, ?_⟩
  · simp [start, hT_nonneg]
  intro u hu_zero
  by_cases hstart_u : start ≤ u
  · rcases exists_taggedAdmittedPastBoundaryCandidate_net_dominating
      start u target z capacity htarget_good hcapacity_nonneg hstart_u hu_zero with
        ⟨q, hq_candidate_list, hu_q, hq_zero, hq_net⟩
    have hq_candidate : q ∈ candidates := by
      simpa [candidates] using hq_candidate_list
    have hq_value : net q ∈ values :=
      Finset.mem_image.mpr ⟨q, hq_candidate, rfl⟩
    have hq_le_maximum : net q ≤ maximum :=
      Finset.le_max' values (net q) hq_value
    have hq_le_r : net q ≤ net r := by
      calc
        net q ≤ maximum := hq_le_maximum
        _ = net r := hr_maximum.symm
    simpa [net] using hq_net.trans hq_le_r
  · have hu_start : u < start := lt_of_not_ge hstart_u
    have hT_le_neg_u : T ≤ -u := by
      dsimp [start] at hu_start
      linarith
    have hu_le_zero_value : net u ≤ net 0 := by
      simpa using htail (-u) hT_le_neg_u
    have hzero_value : net 0 ∈ values :=
      Finset.mem_image.mpr ⟨0, hzero_candidate, rfl⟩
    have hzero_le_maximum : net 0 ≤ maximum :=
      Finset.le_max' values (net 0) hzero_value
    have hu_le_r : net u ≤ net r := by
      calc
        net u ≤ net 0 := hu_le_zero_value
        _ ≤ maximum := hzero_le_maximum
        _ = net r := hr_maximum.symm
    simpa [net] using hu_le_r

/-- Under the paper's literal aggregate slack assumptions, the direct
target-Palm source carrier almost surely has a finite global physical-time
aggregate net-work cutoff of the preceding form.  The conclusion remains
source-only and does not turn the cutoff into a GPS reset. -/
theorem ae_exists_taggedAdmittedPastGlobalNetCutoff
    (M : SLA2026BoroughQueueingInput Category)
    (G : SLA2026BoroughGPSParameters M) (target : Category) :
    ∀ᵐ z ∂(M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      ∃ start r,
        start ≤ 0 ∧
        r ∈ taggedAdmittedPastBoundaryCandidates start 0 target z ∧
        start ≤ r ∧ r ≤ 0 ∧
        ∀ u : Real, u ≤ 0 →
          stationaryAdmittedTargetPassivePastAggregateWork target z (-u) -
              G.capacity * (-u) ≤
            stationaryAdmittedTargetPassivePastAggregateWork target z (-r) -
              G.capacity * (-r) := by
  filter_upwards [
    M.ae_taggedAdmittedFiniteExecutionInputGood target,
    M.ae_tendsto_stationaryAdmittedTargetPassivePastAggregateNetWork_atBot G target]
    with z hgood hlim
  exact exists_taggedAdmittedPastGlobalNetCutoff_of_tendsto_atBot target z G.capacity
    hgood.1 G.capacity_nonneg hlim

/-- A global physical-time lower-boundary maximizer certifies nonpositive
aggregate source net input on every earlier half-open prefix ending at that
boundary.  If `r` is an actual source batch time, this is specifically the
interval *before that same batch*: `[u, r)`.  This is the physical interval
whose scalar reflected state is the pre-batch state at `r`; the lemma makes
that endpoint convention explicit rather than smuggling it into a reset
claim.

No scheduler state or reset conclusion is made here. -/
theorem taggedAdmittedSourceNetWork_prefix_le_zero_of_pastGlobalMax
    (r u : Real) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (capacity : Real)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hu_r : u ≤ r) (hr_zero : r ≤ 0)
    (hglobal : ∀ v : Real, v ≤ 0 →
      stationaryAdmittedTargetPassivePastAggregateWork target z (-v) -
          capacity * (-v) ≤
        stationaryAdmittedTargetPassivePastAggregateWork target z (-r) -
          capacity * (-r)) :
    taggedAdmittedSourceNetWork u r target z capacity ≤ 0 := by
  have hu_zero : u ≤ 0 := hu_r.trans hr_zero
  have hglobal_ledger :
      taggedAdmittedSourceNetWork u 0 target z capacity ≤
        taggedAdmittedSourceNetWork r 0 target z capacity := by
    calc
      taggedAdmittedSourceNetWork u 0 target z capacity =
          stationaryAdmittedTargetPassivePastAggregateWork target z (-u) -
            capacity * (-u) :=
        (stationaryAdmittedTargetPassivePastAggregateNetWork_eq_taggedNetWork
          u target z capacity).symm
      _ ≤ stationaryAdmittedTargetPassivePastAggregateWork target z (-r) -
            capacity * (-r) := hglobal u hu_zero
      _ = taggedAdmittedSourceNetWork r 0 target z capacity :=
        stationaryAdmittedTargetPassivePastAggregateNetWork_eq_taggedNetWork
          r target z capacity
  have hpartition := taggedAdmittedSourceNetWork_reset_partition
    u r 0 target z capacity htarget_good hu_r hr_zero
  rw [hpartition] at hglobal_ledger
  linarith

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements

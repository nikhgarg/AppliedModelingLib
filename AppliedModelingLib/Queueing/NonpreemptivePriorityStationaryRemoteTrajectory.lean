import AppliedModelingLib.Queueing.NonpreemptivePriorityStationaryTimeTranslation
import AppliedModelingLib.Queueing.NonpreemptivePriorityStationaryStateComponents
import AppliedModelingLib.Queueing.NonpreemptivePriorityStationaryPathMeasurability
import AppliedModelingLib.Foundations.Probability.EventuallyStableFiniteReplay

/-!
# Original-coordinate trajectory of a stationary priority queue

The stationary input flow represents a physical observation at time `t` by a
shifted input whose queue state is recorded at coordinate zero.  This module
restores both the original arrival identifiers and the original time
coordinate.  It is a generic state-transport API; no Palm or paper-specific
claim is made here.
-/

namespace AppliedModelingLib.Queueing

open MeasureTheory ProbabilityTheory

noncomputable section

/-- Relabelling both states preserves live-equivalence. -/
theorem liveEquivalentNonpreemptivePriorityWorkState_mapIdentifier
    {n : ℕ} {JobId JobId' : Type*} (f : JobId → JobId')
    {first second : NonpreemptivePriorityWorkState n JobId}
    (hequivalent : liveEquivalentNonpreemptivePriorityWorkState first second) :
    liveEquivalentNonpreemptivePriorityWorkState
      (nonpreemptivePriorityWorkStateMapIdentifier f first)
      (nonpreemptivePriorityWorkStateMapIdentifier f second) := by
  rcases hequivalent with ⟨hcurrent, hactive, hwaiting⟩
  constructor
  · exact hcurrent
  constructor
  · exact congrArg (Option.map fun entry =>
      (nonpreemptivePriorityJobMapIdentifier f entry.1, entry.2)) hactive
  · funext i
    exact congrArg (List.map (nonpreemptivePriorityJobMapIdentifier f))
      (congrFun hwaiting i)

/-- Re-expressing both states at the same time origin preserves their live
queue equivalence. -/
theorem liveEquivalentNonpreemptivePriorityWorkState_translate
    {n : ℕ} {JobId : Type*} (offset : ℝ)
    {first second : NonpreemptivePriorityWorkState n JobId}
    (hequivalent : liveEquivalentNonpreemptivePriorityWorkState first second) :
    liveEquivalentNonpreemptivePriorityWorkState
      (translateNonpreemptivePriorityWorkState offset first)
      (translateNonpreemptivePriorityWorkState offset second) := by
  rcases hequivalent with ⟨hcurrent, hactive, hwaiting⟩
  constructor
  · exact congrArg (fun current : ℝ => current - offset) hcurrent
  constructor
  · exact congrArg (Option.map fun entry =>
      (translateNonpreemptivePriorityJob offset entry.1, entry.2)) hactive
  · funext i
    exact congrArg (List.map (translateNonpreemptivePriorityJob offset))
      (congrFun hwaiting i)

/-- The literal remote-past priority state at physical time `time`, expressed
in the original input's arrival labels and time coordinate. -/
noncomputable def stationaryPriorityRemotePastStateAt
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → StationaryPoissonWorkPath) (time : ℝ) :
    NonpreemptivePriorityWorkState n (NonpreemptivePriorityArrivalIndex n) :=
  translateNonpreemptivePriorityWorkState (-time)
    (nonpreemptivePriorityWorkStateMapIdentifier
      (stationaryPriorityFlowRestoreEmbedding omega time)
      (stationaryPriorityRemotePastState meanService
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow time omega)))

/-- A restored label is waiting in the original-coordinate remote trajectory
exactly when its shifted counterpart is waiting at coordinate zero. -/
theorem nonpreemptivePriorityWaitingIdentifier_stationaryPriorityRemotePastStateAt_restore_iff
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → StationaryPoissonWorkPath) (time : ℝ)
    (q : NonpreemptivePriorityArrivalIndex n) :
    nonpreemptivePriorityWaitingIdentifier
      (stationaryPriorityFlowRestoreIndex omega time q)
      (stationaryPriorityRemotePastStateAt meanService omega time) ↔
      nonpreemptivePriorityWaitingIdentifier q
        (stationaryPriorityRemotePastState meanService
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow time omega)) := by
  unfold stationaryPriorityRemotePastStateAt
  rw [nonpreemptivePriorityWaitingIdentifier_translate_iff]
  exact nonpreemptivePriorityWaitingIdentifier_mapIdentifier_iff
    (stationaryPriorityFlowRestoreEmbedding omega time)
    (Function.Injective.stationaryPriorityFlowRestoreIndex omega time) q
    (stationaryPriorityRemotePastState meanService
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow time omega))

/-- The original-coordinate trajectory preserves the priority-filtered
waiting workload of the flow-coordinate remote state. -/
theorem priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityRemotePastStateAt
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → StationaryPoissonWorkPath) (time : ℝ) (priority : Fin n) :
    priorityWaitingResidualWorkAtLeastAsUrgent
      (stationaryPriorityRemotePastStateAt meanService omega time) priority =
      priorityWaitingResidualWorkAtLeastAsUrgent
        (stationaryPriorityRemotePastState meanService
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow time omega))
        priority := by
  unfold stationaryPriorityRemotePastStateAt
  rw [priorityWaitingResidualWorkAtLeastAsUrgent_translate,
    priorityWaitingResidualWorkAtLeastAsUrgent_mapIdentifier]

/-- If a finite replay has already coalesced to the remote state after
viewing its terminal epoch through the stationary flow, then its
original-coordinate live queue agrees with the restored remote trajectory at
that epoch.  The only additional hypothesis is the finite-window no-ties
condition required to restore the integer labels. -/
theorem liveEquivalent_stationaryPriorityFiniteWindowState_stationaryPriorityRemotePastStateAt_of_flow_coalescence
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → StationaryPoissonWorkPath) (left time : ℝ)
    (hnoTies : ∀ first ∈
        nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityArrivalWindowIndices omega left time),
      ∀ second ∈
        nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityArrivalWindowIndices omega left time),
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival first.1 omega first.2 =
          Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
            second.1 omega second.2 → first = second)
    (hcoalescence : liveEquivalentNonpreemptivePriorityWorkState
      (stationaryPriorityFiniteWindowState meanService
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow time omega)
        (left - time) 0)
      (stationaryPriorityRemotePastState meanService
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow time omega))) :
    liveEquivalentNonpreemptivePriorityWorkState
      (stationaryPriorityFiniteWindowState meanService omega left time)
      (stationaryPriorityRemotePastStateAt meanService omega time) := by
  let flow := Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow time omega
  let restore := stationaryPriorityFlowRestoreEmbedding omega time
  let shifted := stationaryPriorityFiniteWindowState meanService flow (left - time) 0
  let remote := stationaryPriorityRemotePastState meanService flow
  let original := stationaryPriorityFiniteWindowState meanService omega left time
  have htransport : nonpreemptivePriorityWorkStateMapIdentifier restore shifted =
      translateNonpreemptivePriorityWorkState time original := by
    simpa [flow, restore, shifted, original] using
      (stationaryPriorityFiniteWindowState_flow_restore_of_noArrivalTies
        meanService omega time left time hnoTies)
  have hmap : liveEquivalentNonpreemptivePriorityWorkState
      (nonpreemptivePriorityWorkStateMapIdentifier restore shifted)
      (nonpreemptivePriorityWorkStateMapIdentifier restore remote) := by
    exact liveEquivalentNonpreemptivePriorityWorkState_mapIdentifier restore
      (by simpa [flow, shifted, remote] using hcoalescence)
  have htranslated :=
    liveEquivalentNonpreemptivePriorityWorkState_translate (-time) hmap
  have hinverse : liveEquivalentNonpreemptivePriorityWorkState original
      (translateNonpreemptivePriorityWorkState (-time)
        (nonpreemptivePriorityWorkStateMapIdentifier restore shifted)) := by
    rw [htransport]
    have hjob : ∀ job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n),
        translateNonpreemptivePriorityJob (-time)
          (translateNonpreemptivePriorityJob time job) = job := by
      intro job
      rw [translateNonpreemptivePriorityJob_translate]
      simpa using translateNonpreemptivePriorityJob_zero job
    constructor
    · simp [translateNonpreemptivePriorityWorkState]
    constructor
    · change original.active =
        (translateNonpreemptivePriorityWorkState (-time)
          (translateNonpreemptivePriorityWorkState time original)).active
      simp only [translateNonpreemptivePriorityWorkState, Option.map_map]
      have hentry : (fun entry : NonpreemptivePriorityJob n
          (NonpreemptivePriorityArrivalIndex n) × ℝ =>
          (translateNonpreemptivePriorityJob (-time) entry.1, entry.2)) ∘
          (fun entry : NonpreemptivePriorityJob n
          (NonpreemptivePriorityArrivalIndex n) × ℝ =>
          (translateNonpreemptivePriorityJob time entry.1, entry.2)) = id := by
        funext entry
        simp only [Function.comp_apply, id_eq]
        exact Prod.ext (hjob entry.1) rfl
      rw [hentry]
      simp only [Option.map_id]
      rfl
    · funext i
      change original.waiting i =
        (translateNonpreemptivePriorityWorkState (-time)
          (translateNonpreemptivePriorityWorkState time original)).waiting i
      simp only [translateNonpreemptivePriorityWorkState, List.map_map]
      have hfun :
          (fun job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n) =>
            translateNonpreemptivePriorityJob (-time) job) ∘
          (fun job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n) =>
            translateNonpreemptivePriorityJob time job) = id := by
        funext job
        simp only [Function.comp_apply, id_eq]
        exact hjob job
      rw [hfun]
      simp only [List.map_id]
  exact liveEquivalentNonpreemptivePriorityWorkState_trans hinverse
    (by simpa [stationaryPriorityRemotePastStateAt, flow, restore, remote] using htranslated)

/-- A deterministic, cutoff-based form of the finite-to-remote trajectory
convergence.  It is useful when the observation epoch is subsequently tied to
a random arrival: the hypotheses describe one whole path rather than a
fixed-time almost-everywhere statement. -/
theorem eventually_liveEquivalent_stationaryPriorityFiniteWindowState_stationaryPriorityRemotePastStateAt_of_exists_cutoff
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → StationaryPoissonWorkPath) (time : ℝ)
    (hnoTies : ∀ first second : NonpreemptivePriorityArrivalIndex n,
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival first.1 omega first.2 =
        Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival second.1 omega second.2 →
          first = second)
    (hcutoff : ∃ cutoff : ℝ, 0 ≤ cutoff ∧
      stationaryPriorityNetPastCutoff meanService
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow time omega) cutoff)
    (hpositive : ∀ j : Fin n, ∀ k : ℤ,
      0 < stationaryPriorityWorkRequirement meanService j
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow time omega) k) :
    ∀ᶠ horizon : ℕ in Filter.atTop,
      liveEquivalentNonpreemptivePriorityWorkState
        (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) time)
        (stationaryPriorityRemotePastStateAt meanService omega time) := by
  let flow := Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow time omega
  let cutoff := hcutoff.choose
  have hcutoffNonneg : 0 ≤ cutoff := hcutoff.choose_spec.1
  have hcutoffValid : stationaryPriorityNetPastCutoff meanService flow cutoff := by
    simpa [flow, cutoff] using hcutoff.choose_spec.2
  apply Filter.eventually_atTop.2
  refine ⟨Nat.ceil (cutoff - time), ?_⟩
  intro horizon hhorizon
  have hceil : cutoff - time ≤ (Nat.ceil (cutoff - time) : ℝ) := Nat.le_ceil _
  have hcast : (Nat.ceil (cutoff - time) : ℝ) ≤ (horizon : ℝ) := by
    exact_mod_cast hhorizon
  have holder : cutoff ≤ (horizon : ℝ) + time := by linarith
  apply liveEquivalent_stationaryPriorityFiniteWindowState_stationaryPriorityRemotePastStateAt_of_flow_coalescence
    meanService omega (-(horizon : ℝ)) time
  · intro first _ second _ heq
    exact hnoTies first second heq
  · rw [stationaryPriorityRemotePastState_eq_finiteWindowState_of_exists_cutoff
      meanService flow hcutoff]
    have hleft : -(horizon : ℝ) - time = -((horizon : ℝ) + time) := by ring
    rw [hleft]
    have hmarks : ∀ job ∈ stationaryPriorityArrivalWindowJobs meanService flow
        (-((horizon : ℝ) + time)) 0, 0 < job.serviceWork := by
      intro job hjob
      rcases (mem_stationaryPriorityArrivalWindowJobs_iff
        meanService flow (-((horizon : ℝ) + time)) 0 job).mp hjob with
        ⟨j, k, _, hcoordinate⟩
      subst job
      exact hpositive j k
    simpa [flow, cutoff] using
      (liveEquivalent_stationaryPriorityFiniteWindowState_of_netPastCutoff
        meanService flow cutoff ((horizon : ℝ) + time)
        hcutoffValid hcutoffNonneg holder hmarks)

/-- At every fixed physical epoch, sufficiently remote empty-start finite
replays coalesce almost surely with the original-coordinate remote trajectory.
This is the state-level strengthening of the existing workload-only
coalescence statements. -/
theorem ae_eventually_liveEquivalent_stationaryPriorityFiniteWindowState_stationaryPriorityRemotePastStateAt
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) (time : ℝ) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      ∀ᶠ horizon : ℕ in Filter.atTop,
        liveEquivalentNonpreemptivePriorityWorkState
          (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) time)
          (stationaryPriorityRemotePastStateAt meanService omega time) := by
  let P := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact Probability.PoissonProcess.isProbabilityMeasure_multiclassStationaryPoissonWorkMeasure
      arrivalRate harrivalRate
  letI : SFinite P := by infer_instance
  let flow := Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow (Class := Fin n)
  have hflow : MeasurePreserving (flow time) P P := by
    exact Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow_measurePreserving
      arrivalRate harrivalRate time
  have hcoalesces : ∀ᵐ omega ∂P,
      ∃ cutoff : ℝ, 0 ≤ cutoff ∧ ∀ older : ℝ, cutoff ≤ older →
        liveEquivalentNonpreemptivePriorityWorkState
          (stationaryPriorityFiniteWindowState meanService (flow time omega) (-older) 0)
          (stationaryPriorityRemotePastState meanService (flow time omega)) := by
    refine MeasureTheory.ae_of_ae_map (μ := P) (f := flow time) (p := fun eta =>
      ∃ cutoff : ℝ, 0 ≤ cutoff ∧ ∀ older : ℝ, cutoff ≤ older →
        liveEquivalentNonpreemptivePriorityWorkState
          (stationaryPriorityFiniteWindowState meanService eta (-older) 0)
          (stationaryPriorityRemotePastState meanService eta)) hflow.measurable.aemeasurable ?_
    rw [hflow.map_eq]
    exact ae_exists_stationaryPriorityRemotePastState_liveCoalescence
      arrivalRate meanService harrivalRate hmeanService hstable
  filter_upwards [hcoalesces, ae_stationaryPriorityArrival_noArrivalTies_all
    arrivalRate harrivalRate] with omega hcoalescesOmega hnoTies
  rcases hcoalescesOmega with ⟨cutoff, _hcutoffNonneg, hcoalescesOmega⟩
  apply Filter.eventually_atTop.2
  refine ⟨Nat.ceil (cutoff - time), ?_⟩
  intro horizon hhorizon
  have hceil : cutoff - time ≤ (Nat.ceil (cutoff - time) : ℝ) := Nat.le_ceil _
  have hcast : (Nat.ceil (cutoff - time) : ℝ) ≤ (horizon : ℝ) := by
    exact_mod_cast hhorizon
  have holder : cutoff ≤ (horizon : ℝ) + time := by linarith
  apply liveEquivalent_stationaryPriorityFiniteWindowState_stationaryPriorityRemotePastStateAt_of_flow_coalescence
    meanService omega (-(horizon : ℝ)) time
  · intro first _ second _ heq
    exact hnoTies first second heq
  · have hleft : -(horizon : ℝ) - time = -((horizon : ℝ) + time) := by ring
    simpa [flow, hleft] using hcoalescesOmega ((horizon : ℝ) + time) holder

/-- At a fixed physical epoch, the work-weighted FIFO contribution of any
fixed arrival label in a finite replay eventually equals that label's
contribution to the original-coordinate remote trajectory. -/
theorem ae_eventually_stationaryPriorityFiniteWindowWaitingIdentifierContribution_eq_remotePastStateAt
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (time : ℝ) (q : NonpreemptivePriorityArrivalIndex n) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      ∀ᶠ horizon : ℕ in Filter.atTop,
        stationaryPriorityWorkRequirement meanService q.1 omega q.2 *
          nonpreemptivePriorityWaitingIdentifierIndicator q
            (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) time) =
        stationaryPriorityWorkRequirement meanService q.1 omega q.2 *
          nonpreemptivePriorityWaitingIdentifierIndicator q
            (stationaryPriorityRemotePastStateAt meanService omega time) := by
  filter_upwards [
    ae_eventually_liveEquivalent_stationaryPriorityFiniteWindowState_stationaryPriorityRemotePastStateAt
      arrivalRate meanService harrivalRate hmeanService hstable time] with omega hcoalesces
  exact hcoalesces.mono fun horizon hequivalent => by
    rw [nonpreemptivePriorityWaitingIdentifierIndicator_eq_of_liveEquivalent q hequivalent]

/-- The fixed-label remote customer contribution is almost-everywhere
measurable at each physical epoch, using the canonical measurable eventual
value of its finite replay sequence. -/
theorem aemeasurable_stationaryPriorityRemotePastWaitingIdentifierContributionAt
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (time : ℝ) (q : NonpreemptivePriorityArrivalIndex n) :
    AEMeasurable (fun omega : Fin n → StationaryPoissonWorkPath =>
      stationaryPriorityWorkRequirement meanService q.1 omega q.2 *
        nonpreemptivePriorityWaitingIdentifierIndicator q
          (stationaryPriorityRemotePastStateAt meanService omega time))
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate) := by
  let P := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate
  let F : ℕ → (Fin n → StationaryPoissonWorkPath) → ℝ := fun horizon omega =>
    stationaryPriorityWorkRequirement meanService q.1 omega q.2 *
      nonpreemptivePriorityWaitingIdentifierIndicator q
        (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) time)
  let G : (Fin n → StationaryPoissonWorkPath) → ℝ := fun omega =>
    stationaryPriorityWorkRequirement meanService q.1 omega q.2 *
      nonpreemptivePriorityWaitingIdentifierIndicator q
        (stationaryPriorityRemotePastStateAt meanService omega time)
  apply AppliedModelingLib.Probability.aemeasurable_response_of_ae_eventually_eq P F G
  · intro horizon
    simpa [F] using
      (measurable_uncurry_stationaryPriorityFiniteWindowWaitingIdentifierContribution
        meanService (-(horizon : ℝ)) q).comp
          (measurable_const.prodMk measurable_id)
  · simpa [P, F, G] using
      (ae_eventually_stationaryPriorityFiniteWindowWaitingIdentifierContribution_eq_remotePastStateAt
        arrivalRate meanService harrivalRate hmeanService hstable time q)

/-- The canonical measurable product-time version of one labelled customer's
waiting-work contribution.  It is the eventual finite-replay value, so the
definition is meaningful before any particular remote-state representative is
chosen on a null set. -/
noncomputable def stationaryPriorityRemotePastWaitingIdentifierContributionCanonical
    {n : ℕ} (meanService : Fin n → ℝ)
    (q : NonpreemptivePriorityArrivalIndex n) :
    ℝ × (Fin n → StationaryPoissonWorkPath) → ℝ :=
  AppliedModelingLib.Probability.stabilizedFiniteReplayResponse fun horizon p =>
    stationaryPriorityWorkRequirement meanService q.1 p.2 q.2 *
      nonpreemptivePriorityWaitingIdentifierIndicator q
        (stationaryPriorityFiniteWindowState meanService p.2
          (-(horizon : ℝ)) p.1)

/-- The canonical product-time labelled-customer contribution is Borel. -/
theorem measurable_uncurry_stationaryPriorityRemotePastWaitingIdentifierContributionCanonical
    {n : ℕ} (meanService : Fin n → ℝ)
    (q : NonpreemptivePriorityArrivalIndex n) :
    Measurable
      (stationaryPriorityRemotePastWaitingIdentifierContributionCanonical
        meanService q) := by
  apply AppliedModelingLib.Probability.measurable_stabilizedFiniteReplayResponse
  intro horizon
  exact measurable_uncurry_stationaryPriorityFiniteWindowWaitingIdentifierContribution
    meanService (-(horizon : ℝ)) q

/-- On a path with a cutoff and positive marks after the observation-time
flow, the Borel canonical finite-replay representative of one labelled
customer equals its literal remote-past contribution. -/
theorem stationaryPriorityRemotePastWaitingIdentifierContributionCanonical_eq_remotePastStateAt_of_exists_cutoff
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → StationaryPoissonWorkPath) (time : ℝ)
    (q : NonpreemptivePriorityArrivalIndex n)
    (hnoTies : ∀ first second : NonpreemptivePriorityArrivalIndex n,
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival first.1 omega first.2 =
        Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival second.1 omega second.2 →
          first = second)
    (hcutoff : ∃ cutoff : ℝ, 0 ≤ cutoff ∧
      stationaryPriorityNetPastCutoff meanService
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow time omega) cutoff)
    (hpositive : ∀ j : Fin n, ∀ k : ℤ,
      0 < stationaryPriorityWorkRequirement meanService j
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow time omega) k) :
    stationaryPriorityRemotePastWaitingIdentifierContributionCanonical
      meanService q (time, omega) =
      stationaryPriorityWorkRequirement meanService q.1 omega q.2 *
        nonpreemptivePriorityWaitingIdentifierIndicator q
          (stationaryPriorityRemotePastStateAt meanService omega time) := by
  apply AppliedModelingLib.Probability.stabilizedFiniteReplayResponse_eq_of_eventually_eq
    (fun horizon (p : ℝ × (Fin n → StationaryPoissonWorkPath)) =>
      stationaryPriorityWorkRequirement meanService q.1 p.2 q.2 *
        nonpreemptivePriorityWaitingIdentifierIndicator q
          (stationaryPriorityFiniteWindowState meanService p.2
            (-(horizon : ℝ)) p.1))
    (fun p : ℝ × (Fin n → StationaryPoissonWorkPath) =>
      stationaryPriorityWorkRequirement meanService q.1 p.2 q.2 *
        nonpreemptivePriorityWaitingIdentifierIndicator q
          (stationaryPriorityRemotePastStateAt meanService p.2 p.1))
    (time, omega)
  refine (eventually_liveEquivalent_stationaryPriorityFiniteWindowState_stationaryPriorityRemotePastStateAt_of_exists_cutoff
    meanService omega time hnoTies hcutoff hpositive).mono fun horizon hequivalent => by
      change stationaryPriorityWorkRequirement meanService q.1 omega q.2 *
          nonpreemptivePriorityWaitingIdentifierIndicator q
            (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) time) =
        stationaryPriorityWorkRequirement meanService q.1 omega q.2 *
          nonpreemptivePriorityWaitingIdentifierIndicator q
            (stationaryPriorityRemotePastStateAt meanService omega time)
      exact congrArg
        (fun waiting => stationaryPriorityWorkRequirement meanService q.1 omega q.2 * waiting)
        (nonpreemptivePriorityWaitingIdentifierIndicator_eq_of_liveEquivalent q hequivalent)

/-- At each physical epoch, the canonical product-time version agrees almost
surely with the literal remote-trajectory contribution. -/
theorem ae_stationaryPriorityRemotePastWaitingIdentifierContributionCanonical_eq_remotePastStateAt
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (time : ℝ) (q : NonpreemptivePriorityArrivalIndex n) :
    (fun omega : Fin n → StationaryPoissonWorkPath =>
      stationaryPriorityRemotePastWaitingIdentifierContributionCanonical
        meanService q (time, omega)) =ᵐ[
      Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate]
      (fun omega : Fin n → StationaryPoissonWorkPath =>
        stationaryPriorityWorkRequirement meanService q.1 omega q.2 *
          nonpreemptivePriorityWaitingIdentifierIndicator q
            (stationaryPriorityRemotePastStateAt meanService omega time)) := by
  apply AppliedModelingLib.Probability.ae_stabilizedFiniteReplayResponse_eq_of_ae_eventually_eq
  simpa [stationaryPriorityRemotePastWaitingIdentifierContributionCanonical] using
    (ae_eventually_stationaryPriorityFiniteWindowWaitingIdentifierContribution_eq_remotePastStateAt
      arrivalRate meanService harrivalRate hmeanService hstable time q)

/-- On the full physical-time/input product, the finite contribution of one
fixed customer eventually agrees with its canonical remote-past version.
This is the measurable customer-level counterpart of the existing aggregate
finite-to-remote trajectory convergence. -/
theorem ae_eventually_uncurry_stationaryPriorityFiniteWindowWaitingIdentifierContribution_eq_canonical
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (q : NonpreemptivePriorityArrivalIndex n) :
    ∀ᵐ p : ℝ × (Fin n → StationaryPoissonWorkPath) ∂
      (MeasureTheory.volume.prod
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate)),
      ∀ᶠ horizon : ℕ in Filter.atTop,
        stationaryPriorityWorkRequirement meanService q.1 p.2 q.2 *
          nonpreemptivePriorityWaitingIdentifierIndicator q
            (stationaryPriorityFiniteWindowState meanService p.2
              (-(horizon : ℝ)) p.1) =
        stationaryPriorityRemotePastWaitingIdentifierContributionCanonical
          meanService q p := by
  let P := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact Probability.PoissonProcess.isProbabilityMeasure_multiclassStationaryPoissonWorkMeasure
      arrivalRate harrivalRate
  letI : SFinite P := by infer_instance
  let F : ℕ → ℝ × (Fin n → StationaryPoissonWorkPath) → ℝ := fun horizon p =>
    stationaryPriorityWorkRequirement meanService q.1 p.2 q.2 *
      nonpreemptivePriorityWaitingIdentifierIndicator q
        (stationaryPriorityFiniteWindowState meanService p.2
          (-(horizon : ℝ)) p.1)
  let G := stationaryPriorityRemotePastWaitingIdentifierContributionCanonical
    meanService q
  have hFmeas : ∀ horizon : ℕ, Measurable (F horizon) := by
    intro horizon
    simpa [F] using
      (measurable_uncurry_stationaryPriorityFiniteWindowWaitingIdentifierContribution
        meanService (-(horizon : ℝ)) q)
  have hGmeas : Measurable G := by
    simpa [G] using
      (measurable_uncurry_stationaryPriorityRemotePastWaitingIdentifierContributionCanonical
        meanService q)
  have hslice : ∀ time : ℝ, ∀ᵐ omega ∂P,
      ∀ᶠ horizon : ℕ in Filter.atTop, F horizon (time, omega) = G (time, omega) := by
    intro time
    filter_upwards [
      ae_eventually_stationaryPriorityFiniteWindowWaitingIdentifierContribution_eq_remotePastStateAt
        arrivalRate meanService harrivalRate hmeanService hstable time q] with omega hfinite
    have hcanonical : G (time, omega) =
        stationaryPriorityWorkRequirement meanService q.1 omega q.2 *
          nonpreemptivePriorityWaitingIdentifierIndicator q
            (stationaryPriorityRemotePastStateAt meanService omega time) := by
      simpa [F, G, stationaryPriorityRemotePastWaitingIdentifierContributionCanonical] using
        (AppliedModelingLib.Probability.stabilizedFiniteReplayResponse_eq_of_eventually_eq
          (fun (horizon : ℕ) (p : ℝ × (Fin n → StationaryPoissonWorkPath)) =>
            stationaryPriorityWorkRequirement meanService q.1 p.2 q.2 *
              nonpreemptivePriorityWaitingIdentifierIndicator q
                (stationaryPriorityFiniteWindowState meanService p.2
                  (-(horizon : ℝ)) p.1))
          (fun p : ℝ × (Fin n → StationaryPoissonWorkPath) =>
            stationaryPriorityWorkRequirement meanService q.1 p.2 q.2 *
              nonpreemptivePriorityWaitingIdentifierIndicator q
                (stationaryPriorityRemotePastStateAt meanService p.2 p.1))
          (time, omega)
          (by simpa [F] using hfinite))
    exact hfinite.mono fun horizon hEq => hEq.trans hcanonical.symm
  have heventually_meas : MeasurableSet {p : ℝ × (Fin n → StationaryPoissonWorkPath) |
      ∀ᶠ horizon : ℕ in Filter.atTop, F horizon p = G p} := by
    rw [show {p : ℝ × (Fin n → StationaryPoissonWorkPath) |
        ∀ᶠ horizon : ℕ in Filter.atTop, F horizon p = G p} =
        ⋃ threshold : ℕ, ⋂ horizon : ℕ, ⋂ (_ : threshold ≤ horizon),
          {p | F horizon p = G p} by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter,
        Filter.eventually_atTop]]
    apply MeasurableSet.iUnion
    intro threshold
    apply MeasurableSet.iInter
    intro horizon
    apply MeasurableSet.iInter
    intro _
    exact measurableSet_eq_fun (hFmeas horizon) hGmeas
  have hsliceM : ∀ᵐ time ∂MeasureTheory.volume, ∀ᵐ omega ∂P,
      ∀ᶠ horizon : ℕ in Filter.atTop, F horizon (time, omega) = G (time, omega) := by
    filter_upwards with time
    exact hslice time
  have hproduct : ∀ᵐ p : ℝ × (Fin n → StationaryPoissonWorkPath) ∂
      (MeasureTheory.volume.prod P),
      ∀ᶠ horizon : ℕ in Filter.atTop, F horizon p = G p :=
    (MeasureTheory.Measure.ae_prod_iff_ae_ae heventually_meas).2 hsliceM
  simpa [F, G, P] using hproduct

/-- The nonnegative countable customer sum built from the canonical
product-time contributions.  This is the measurable Tonelli surface for a
priority-filtered stationary waiting workload; its identification with the
literal remote state is established separately. -/
noncomputable def stationaryPriorityRemotePastAtLeastAsUrgentWaitingWorkCanonicalNN
    {n : ℕ} (meanService : Fin n → ℝ) (priority : Fin n) :
    ℝ × (Fin n → StationaryPoissonWorkPath) → ENNReal :=
  fun p => ∑' q : NonpreemptivePriorityArrivalIndex n,
    if q.1 ≤ priority then
      ENNReal.ofReal
        (stationaryPriorityRemotePastWaitingIdentifierContributionCanonical
          meanService q p)
    else 0

/-- The canonical priority-filtered customer sum is Borel on the full
physical-time/input product. -/
theorem measurable_uncurry_stationaryPriorityRemotePastAtLeastAsUrgentWaitingWorkCanonicalNN
    {n : ℕ} (meanService : Fin n → ℝ) (priority : Fin n) :
    Measurable
      (stationaryPriorityRemotePastAtLeastAsUrgentWaitingWorkCanonicalNN
        meanService priority) := by
  apply Measurable.ennreal_tsum
  intro q
  by_cases hpriority : q.1 ≤ priority
  · simpa [stationaryPriorityRemotePastAtLeastAsUrgentWaitingWorkCanonicalNN,
      hpriority] using
      (measurable_uncurry_stationaryPriorityRemotePastWaitingIdentifierContributionCanonical
        meanService q).ennreal_ofReal
  · simp [hpriority]

/-- The priority-filtered waiting work of empty-start finite replays converges
almost everywhere on the full physical-time/input product to the stationary
remote trajectory.  The proof upgrades fixed-time state coalescence by first
replacing the remote observable with a measurable product representative and
then applying Fubini to the measurable eventual-equality event. -/
theorem ae_eventually_uncurry_priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityFiniteWindow_eq_remotePast_flow
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (priority : Fin n) :
    ∀ᵐ p : ℝ × (Fin n → StationaryPoissonWorkPath) ∂
      (MeasureTheory.volume.prod
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate)),
      ∀ᶠ horizon : ℕ in Filter.atTop,
        priorityWaitingResidualWorkAtLeastAsUrgent
          (stationaryPriorityFiniteWindowState meanService p.2 (-(horizon : ℝ)) p.1)
          priority =
        stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork meanService priority
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow p.1 p.2) := by
  let P := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact Probability.PoissonProcess.isProbabilityMeasure_multiclassStationaryPoissonWorkMeasure
      arrivalRate harrivalRate
  letI : SFinite P := by infer_instance
  let F : ℕ → ℝ × (Fin n → StationaryPoissonWorkPath) → ℝ := fun horizon p =>
    priorityWaitingResidualWorkAtLeastAsUrgent
      (stationaryPriorityFiniteWindowState meanService p.2 (-(horizon : ℝ)) p.1)
      priority
  let G : ℝ × (Fin n → StationaryPoissonWorkPath) → ℝ := fun p =>
    stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork meanService priority
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow p.1 p.2)
  have hFmeas : ∀ horizon : ℕ, Measurable (F horizon) := by
    intro horizon
    simpa [F] using
      (measurable_uncurry_stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingWork
        meanService (-(horizon : ℝ)) priority)
  have hGmeas : AEMeasurable G (MeasureTheory.volume.prod P) := by
    simpa [G, P] using
      (aemeasurable_uncurry_stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork_flow
        arrivalRate meanService harrivalRate hmeanService hstable priority)
  let Gm := hGmeas.mk G
  have hGm_meas : Measurable Gm := hGmeas.measurable_mk
  have hG_eq : G =ᵐ[MeasureTheory.volume.prod P] Gm := hGmeas.ae_eq_mk
  have hslice : ∀ time : ℝ, ∀ᵐ omega ∂P,
      ∀ᶠ horizon : ℕ in Filter.atTop,
        F horizon (time, omega) = G (time, omega) := by
    intro time
    filter_upwards [
      ae_eventually_liveEquivalent_stationaryPriorityFiniteWindowState_stationaryPriorityRemotePastStateAt
        arrivalRate meanService harrivalRate hmeanService hstable time] with omega hcoalesces
    filter_upwards [hcoalesces] with horizon hequivalent
    calc
      F horizon (time, omega) =
          priorityWaitingResidualWorkAtLeastAsUrgent
            (stationaryPriorityRemotePastStateAt meanService omega time) priority := by
              simpa [F] using
                (priorityWaitingResidualWorkAtLeastAsUrgent_eq_of_liveEquivalent
                  hequivalent priority)
      _ = G (time, omega) := by
        simpa [G, stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork] using
          (priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityRemotePastStateAt
            meanService omega time priority)
  have hsliceM : ∀ᵐ time ∂MeasureTheory.volume, ∀ᵐ omega ∂P,
      ∀ᶠ horizon : ℕ in Filter.atTop,
        F horizon (time, omega) = Gm (time, omega) := by
    filter_upwards [MeasureTheory.Measure.ae_ae_of_ae_prod hG_eq] with time hGtime
    filter_upwards [hslice time, hGtime] with omega hsliceOmega hGtimeOmega
    exact hsliceOmega.mono fun horizon hhorizon => hhorizon.trans hGtimeOmega
  have heventually_meas : MeasurableSet {p : ℝ × (Fin n → StationaryPoissonWorkPath) |
      ∀ᶠ horizon : ℕ in Filter.atTop, F horizon p = Gm p} := by
    rw [show {p : ℝ × (Fin n → StationaryPoissonWorkPath) |
        ∀ᶠ horizon : ℕ in Filter.atTop, F horizon p = Gm p} =
        ⋃ threshold : ℕ, ⋂ horizon : ℕ, ⋂ (_ : threshold ≤ horizon),
          {p | F horizon p = Gm p} by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter,
        Filter.eventually_atTop]
      ]
    apply MeasurableSet.iUnion
    intro threshold
    apply MeasurableSet.iInter
    intro horizon
    apply MeasurableSet.iInter
    intro _
    exact measurableSet_eq_fun (hFmeas horizon) hGm_meas
  have hproductM : ∀ᵐ p : ℝ × (Fin n → StationaryPoissonWorkPath) ∂
      (MeasureTheory.volume.prod P),
      ∀ᶠ horizon : ℕ in Filter.atTop, F horizon p = Gm p :=
    (MeasureTheory.Measure.ae_prod_iff_ae_ae heventually_meas).2 hsliceM
  filter_upwards [hproductM, hG_eq] with p hp hG
  exact hp.mono fun horizon hhorizon => by
    simpa [F, G, P] using hhorizon.trans hG.symm

/-- Pull the product-time finite-to-remote workload convergence back to one
fixed labelled class arrival and an elapsed-time coordinate.  This is the
measure-theoretically exact form needed when Campbell occupation integrals
are compared with the stationary queue trajectory. -/
theorem ae_eventually_priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityFiniteWindow_at_classArrival_add_elapsed_eq_remotePast
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (arrivalClass priority : Fin n) (label : ℤ) :
    ∀ᵐ p :
      (StationaryPoissonWorkPath ×
        ({j : Fin n // j ≠ arrivalClass} → StationaryPoissonWorkPath)) × ℝ ∂
      ((((Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw
          (harrivalRate arrivalClass)).Pbase).prod
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate arrivalClass).Pbase).prod
          MeasureTheory.volume),
      ∀ᶠ horizon : ℕ in Filter.atTop,
        priorityWaitingResidualWorkAtLeastAsUrgent
          (stationaryPriorityFiniteWindowState meanService
            (multiclassStationaryPoissonWorkClassAssemble arrivalClass p.1)
            (-(horizon : ℝ))
            (Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival arrivalClass
              (multiclassStationaryPoissonWorkClassAssemble arrivalClass p.1) label + p.2))
          priority =
        stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork meanService priority
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
            (Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival arrivalClass
              (multiclassStationaryPoissonWorkClassAssemble arrivalClass p.1) label + p.2)
            (multiclassStationaryPoissonWorkClassAssemble arrivalClass p.1)) := by
  let source : Measure
      ((StationaryPoissonWorkPath ×
        ({j : Fin n // j ≠ arrivalClass} → StationaryPoissonWorkPath)) × ℝ) :=
    (((Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw
      (harrivalRate arrivalClass)).Pbase).prod
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate arrivalClass).Pbase).prod
        MeasureTheory.volume
  let P := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate
  let physical :
      (StationaryPoissonWorkPath ×
        ({j : Fin n // j ≠ arrivalClass} → StationaryPoissonWorkPath)) × ℝ →
        ℝ × (Fin n → StationaryPoissonWorkPath) := fun p =>
    (Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival arrivalClass
        (multiclassStationaryPoissonWorkClassAssemble arrivalClass p.1) label + p.2,
      multiclassStationaryPoissonWorkClassAssemble arrivalClass p.1)
  have hphysical : MeasurePreserving physical source (MeasureTheory.volume.prod P) := by
    simpa [physical, source, P] using
      (measurePreserving_multiclassStationaryPoissonWorkClassAssemble_add_arrival
        arrivalRate harrivalRate arrivalClass label)
  have hpull : ∀ᵐ p ∂source,
      ∀ᶠ horizon : ℕ in Filter.atTop,
        priorityWaitingResidualWorkAtLeastAsUrgent
          (stationaryPriorityFiniteWindowState meanService (physical p).2
            (-(horizon : ℝ)) (physical p).1) priority =
        stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork meanService priority
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
            (physical p).1 (physical p).2) := by
    refine MeasureTheory.ae_of_ae_map (μ := source) (f := physical)
      (p := fun q => ∀ᶠ horizon : ℕ in Filter.atTop,
        priorityWaitingResidualWorkAtLeastAsUrgent
          (stationaryPriorityFiniteWindowState meanService q.2
            (-(horizon : ℝ)) q.1) priority =
        stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork meanService priority
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow q.1 q.2))
      hphysical.measurable.aemeasurable ?_
    rw [hphysical.map_eq]
    exact ae_eventually_uncurry_priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityFiniteWindow_eq_remotePast_flow
      arrivalRate meanService harrivalRate hmeanService hstable priority
  simpa [source, physical] using hpull

end

end AppliedModelingLib.Queueing

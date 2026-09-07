import AppliedModelingLib.Queueing.NonpreemptivePriorityClassTaggedFixedReplayMeasurability
import AppliedModelingLib.Queueing.NonpreemptivePriorityWaitingOccupation
import AppliedModelingLib.Queueing.NonpreemptivePriorityStationaryRemoteTrajectory
import AppliedModelingLib.Queueing.NonpreemptivePriorityClassTaggedSelectedRewardIntegrability
import Mathlib.Tactic

/-!
# Finite customer occupations for stationary priority queues

This module joins the deterministic finite waiting ledger with the Campbell
recentring bridge.  Its results remain finite-window, pathwise identities;
the later expectation and remote-past limits are stated separately.
-/

namespace AppliedModelingLib.Queueing

open MeasureTheory ProbabilityTheory

noncomputable section

/-- A canonical labelled-customer contribution vanishes strictly before that
customer's literal arrival epoch.  The proof stays at finite replay level and
therefore needs no remote-state measurability choice. -/
theorem stationaryPriorityRemotePastWaitingIdentifierContributionCanonical_eq_zero_of_time_lt_arrival
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → StationaryPoissonWorkPath) (time : ℝ)
    (q : NonpreemptivePriorityArrivalIndex n)
    (htime : time < Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
      q.1 omega q.2) :
    stationaryPriorityRemotePastWaitingIdentifierContributionCanonical
      meanService q (time, omega) = 0 := by
  let arrival := Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
    q.1 omega q.2
  apply AppliedModelingLib.Probability.stabilizedFiniteReplayResponse_eq_of_eventually_eq
    (fun horizon (p : ℝ × (Fin n → StationaryPoissonWorkPath)) =>
      stationaryPriorityWorkRequirement meanService q.1 p.2 q.2 *
        nonpreemptivePriorityWaitingIdentifierIndicator q
          (stationaryPriorityFiniteWindowState meanService p.2
            (-(horizon : ℝ)) p.1))
    (fun _ => 0) (time, omega)
  apply Filter.eventually_atTop.2
  refine ⟨Nat.ceil (-time), ?_⟩
  intro horizon hhorizon
  have hceil : -time ≤ (Nat.ceil (-time) : ℝ) := Nat.le_ceil _
  have hcast : (Nat.ceil (-time) : ℝ) ≤ (horizon : ℝ) := by
    exact_mod_cast hhorizon
  have hleftTime : -(horizon : ℝ) ≤ time := by linarith
  have hleftArrival : -(horizon : ℝ) ≤ arrival :=
    hleftTime.trans htime.le
  let job := stationaryPriorityArrivalJobCoordinate meanService q omega
  have hjob : job ∈ stationaryPriorityArrivalWindowJobs meanService omega
      (-(horizon : ℝ)) (arrival + 1) := by
    apply (mem_stationaryPriorityArrivalWindowJobs_iff
      meanService omega (-(horizon : ℝ)) (arrival + 1) job).mpr
    refine ⟨q.1, q.2, ?_, ?_⟩
    · apply (Probability.PoissonProcess.mem_suspensionBaseArrivalIndices_iff
        (-(horizon : ℝ)) (arrival + 1) (omega q.1).1 q.2).mpr
      simpa [arrival, Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival,
        Probability.Queueing.stationaryPoissonWorkArrival,
        Probability.Queueing.timedEmbeddedArrival] using
        And.intro hleftArrival (by linarith : arrival < arrival + 1)
    · rfl
  have hzero : nonpreemptivePriorityWaitingIdentifierIndicator q
      (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) time) = 0 := by
    simpa [job] using
      (nonpreemptivePriorityWaitingIdentifierIndicator_eq_zero_of_time_le_arrival
        meanService omega (-(horizon : ℝ)) time (arrival + 1)
        hleftTime (by linarith) job hjob htime.le)
  change stationaryPriorityWorkRequirement meanService q.1 omega q.2 *
      nonpreemptivePriorityWaitingIdentifierIndicator q
        (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) time) = 0
  rw [hzero, mul_zero]

/-- On a path with collision-free arrivals, positive marks, and a net-input
cutoff after every time shift, the Borel selected finite-replay response at a
recentered customer equals that customer's Borel original-label canonical
contribution.  The elapsed-time origin is the selected arrival; the singleton
at elapsed time zero is deliberately excluded because it is immaterial to
Lebesgue/Campbell occupation. -/
theorem stationaryPriorityClassTaggedStabilizedWaitingWorkResponse_campbellRecenter_eq_remoteCanonical_of_baseGood
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j) (i : Fin n)
    (x : StationaryPoissonWorkPath ×
      ({j : Fin n // j ≠ i} → StationaryPoissonWorkPath))
    (k : ℤ) (t : ℝ) (ht : t ≠ 0)
    (hnoTies : ∀ first second : NonpreemptivePriorityArrivalIndex n,
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival first.1
          (multiclassStationaryPoissonWorkClassAssemble i x) first.2 =
        Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival second.1
          (multiclassStationaryPoissonWorkClassAssemble i x) second.2 → first = second)
    (hcutoffs : ∀ offset : ℝ, ∃ cutoff : ℝ, 0 ≤ cutoff ∧
      stationaryPriorityNetPastCutoff meanService
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow offset
          (multiclassStationaryPoissonWorkClassAssemble i x)) cutoff)
    (hpositive : ∀ j : Fin n, ∀ m : ℤ,
      0 < stationaryPriorityWorkRequirement meanService j
        (multiclassStationaryPoissonWorkClassAssemble i x) m) :
    stationaryPriorityClassTaggedStabilizedWaitingWorkResponse meanService i
      ((multiclassStationaryPoissonWorkClassCampbellCertificate
        arrivalRate harrivalRate i).recenterAt x k, t) =
      stationaryPriorityRemotePastWaitingIdentifierContributionCanonical meanService
        (Sigma.mk i k)
        (Probability.Queueing.timedEmbeddedArrival x.1 k + t,
          multiclassStationaryPoissonWorkClassAssemble i x) := by
  let omega := multiclassStationaryPoissonWorkClassAssemble i x
  let arrival := Probability.Queueing.timedEmbeddedArrival x.1 k
  let physicalTime := arrival + t
  let recentered := (multiclassStationaryPoissonWorkClassCampbellCertificate
    arrivalRate harrivalRate i).recenterAt x k
  by_cases htneg : t < 0
  · have hselected : stationaryPriorityClassTaggedStabilizedWaitingWorkResponse
        meanService i (recentered, t) = 0 := by
      unfold stationaryPriorityClassTaggedStabilizedWaitingWorkResponse
      apply AppliedModelingLib.Probability.stabilizedFiniteReplayResponse_eq_of_eventually_eq
        (stationaryPriorityClassTaggedFiniteReplayWaitingWorkResponse meanService i)
        (fun _ => 0) (recentered, t)
      exact Filter.Eventually.of_forall fun horizon => by
        simp [stationaryPriorityClassTaggedFiniteReplayWaitingWorkResponse,
          not_le_of_gt htneg]
    calc
      stationaryPriorityClassTaggedStabilizedWaitingWorkResponse meanService i
          ((multiclassStationaryPoissonWorkClassCampbellCertificate
            arrivalRate harrivalRate i).recenterAt x k, t) = 0 := by
              simpa [recentered] using hselected
      _ = stationaryPriorityRemotePastWaitingIdentifierContributionCanonical meanService
          (Sigma.mk i k)
          (Probability.Queueing.timedEmbeddedArrival x.1 k + t,
            multiclassStationaryPoissonWorkClassAssemble i x) := by
              symm
              apply stationaryPriorityRemotePastWaitingIdentifierContributionCanonical_eq_zero_of_time_lt_arrival
              have harrival :
                  Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival i
                    (multiclassStationaryPoissonWorkClassAssemble i x) k = arrival := by
                simp [arrival,
                  Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival,
                  Probability.Queueing.stationaryPoissonWorkArrival]
              calc
                Probability.Queueing.timedEmbeddedArrival x.1 k + t = physicalTime := rfl
                _ < arrival := by linarith
                _ = Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival i
                    (multiclassStationaryPoissonWorkClassAssemble i x) k := harrival.symm
  · have htpos : 0 < t := lt_of_le_of_ne (le_of_not_gt htneg) (Ne.symm ht)
    have hcutoff : ∃ cutoff : ℝ, 0 ≤ cutoff ∧
        stationaryPriorityNetPastCutoff meanService
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
            physicalTime omega) cutoff := by
      simpa [omega, physicalTime] using hcutoffs physicalTime
    have hpositiveFlow : ∀ j : Fin n, ∀ m : ℤ,
        0 < stationaryPriorityWorkRequirement meanService j
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
            physicalTime omega) m := by
      intro j m
      rw [stationaryPriorityWorkRequirement_flow_restore meanService omega physicalTime ⟨j, m⟩]
      exact hpositive
        (stationaryPriorityFlowRestoreIndex omega physicalTime (Sigma.mk j m)).1
        (stationaryPriorityFlowRestoreIndex omega physicalTime (Sigma.mk j m)).2
    have hselected : stationaryPriorityClassTaggedStabilizedWaitingWorkResponse
        meanService i (recentered, t) =
        stationaryPriorityWorkRequirement meanService i omega k *
          nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i k)
            (stationaryPriorityRemotePastStateAt meanService omega physicalTime) := by
      unfold stationaryPriorityClassTaggedStabilizedWaitingWorkResponse
      apply AppliedModelingLib.Probability.stabilizedFiniteReplayResponse_eq_of_eventually_eq
        (stationaryPriorityClassTaggedFiniteReplayWaitingWorkResponse meanService i)
        (fun _ => stationaryPriorityWorkRequirement meanService i omega k *
          nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i k)
            (stationaryPriorityRemotePastStateAt meanService omega physicalTime))
        (recentered, t)
      let cutoff := hcutoff.choose
      have hcutoffNonneg : 0 ≤ cutoff := hcutoff.choose_spec.1
      have hcutoffValid : stationaryPriorityNetPastCutoff meanService
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
            physicalTime omega) cutoff := by
        simpa [cutoff] using hcutoff.choose_spec.2
      apply Filter.eventually_atTop.2
      refine ⟨Nat.ceil (cutoff - t), ?_⟩
      intro horizon hhorizon
      have hceil : cutoff - t ≤ (Nat.ceil (cutoff - t) : ℝ) := Nat.le_ceil _
      have hcast : (Nat.ceil (cutoff - t) : ℝ) ≤ (horizon : ℝ) := by
        exact_mod_cast hhorizon
      have hlarge : cutoff ≤ (horizon : ℝ) + t := by linarith
      have hmarks : ∀ job ∈ stationaryPriorityArrivalWindowJobs meanService
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
            physicalTime omega) (-((horizon : ℝ) + t)) 0, 0 < job.serviceWork := by
        intro job hjob
        rcases (mem_stationaryPriorityArrivalWindowJobs_iff meanService
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
            physicalTime omega) (-((horizon : ℝ) + t)) 0 job).mp hjob with
          ⟨j, m, _, hcoordinate⟩
        subst job
        exact hpositiveFlow j m
      have hglobal : liveEquivalentNonpreemptivePriorityWorkState
          (stationaryPriorityFiniteWindowState meanService
            (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
              physicalTime omega) (-((horizon : ℝ) + t)) 0)
          (stationaryPriorityRemotePastState meanService
            (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
              physicalTime omega)) := by
        rw [stationaryPriorityRemotePastState_eq_finiteWindowState_of_exists_cutoff
          meanService
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
            physicalTime omega) hcutoff]
        simpa [cutoff] using
          (liveEquivalent_stationaryPriorityFiniteWindowState_of_netPastCutoff
            meanService
            (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
              physicalTime omega) cutoff ((horizon : ℝ) + t)
            hcutoffValid hcutoffNonneg hlarge hmarks)
      change (if 0 ≤ t then
        stationaryPriorityClassTaggedWorkRequirement meanService i recentered *
          stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
            meanService i recentered (horizon : ℝ) t
        else 0) = _
      rw [if_pos htpos.le]
      have hfinite : nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0)
          (stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
            meanService i recentered (horizon : ℝ) t) =
          nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i k)
            (stationaryPriorityFiniteWindowState meanService omega
              (arrival - (horizon : ℝ)) (arrival + t)) := by
        simpa [omega, arrival, recentered] using
          (stationaryPriorityClassTaggedStrictReplayWaitingIndicator_eq_originalFiniteWindow_of_noArrivalTies_all
            arrivalRate meanService harrivalRate i x k (horizon : ℝ) t
            (Nat.cast_nonneg horizon) htpos hnoTies)
      have htrajectory : liveEquivalentNonpreemptivePriorityWorkState
          (stationaryPriorityFiniteWindowState meanService omega
            (arrival - (horizon : ℝ)) (arrival + t))
          (stationaryPriorityRemotePastStateAt meanService omega (arrival + t)) := by
        apply liveEquivalent_stationaryPriorityFiniteWindowState_stationaryPriorityRemotePastStateAt_of_flow_coalescence
          meanService omega (arrival - (horizon : ℝ)) (arrival + t)
        · intro first _ second _ heq
          exact hnoTies first second heq
        · have hleft : arrival - (horizon : ℝ) - (arrival + t) = -((horizon : ℝ) + t) := by
            ring
          simpa [omega, physicalTime, arrival, hleft] using hglobal
      have hindicator : nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0)
          (stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
            meanService i recentered (horizon : ℝ) t) =
          nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i k)
            (stationaryPriorityRemotePastStateAt meanService omega (arrival + t)) :=
        hfinite.trans
          (nonpreemptivePriorityWaitingIdentifierIndicator_eq_of_liveEquivalent
            (Sigma.mk i k) htrajectory)
      have hwork : stationaryPriorityClassTaggedWorkRequirement meanService i recentered =
          stationaryPriorityWorkRequirement meanService i omega k := by
        simpa [omega, recentered] using
          (stationaryPriorityClassTaggedWorkRequirement_campbellRecenter_eq_original
            arrivalRate meanService harrivalRate i x k)
      exact congrArg₂ (· * ·) hwork hindicator
    calc
      stationaryPriorityClassTaggedStabilizedWaitingWorkResponse meanService i
          ((multiclassStationaryPoissonWorkClassCampbellCertificate
            arrivalRate harrivalRate i).recenterAt x k, t) =
          stationaryPriorityWorkRequirement meanService i
            (multiclassStationaryPoissonWorkClassAssemble i x) k *
            nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i k)
              (stationaryPriorityRemotePastStateAt meanService
                (multiclassStationaryPoissonWorkClassAssemble i x)
                (Probability.Queueing.timedEmbeddedArrival x.1 k + t)) := by
                  simpa [omega, physicalTime, arrival, recentered] using hselected
      _ = stationaryPriorityRemotePastWaitingIdentifierContributionCanonical meanService
          (Sigma.mk i k)
          (Probability.Queueing.timedEmbeddedArrival x.1 k + t,
            multiclassStationaryPoissonWorkClassAssemble i x) := by
              symm
              apply stationaryPriorityRemotePastWaitingIdentifierContributionCanonical_eq_remotePastStateAt_of_exists_cutoff
              · exact hnoTies
              · simpa [omega, physicalTime, arrival] using hcutoff
              · simpa [omega, physicalTime, arrival] using hpositiveFlow

/-- The deterministic recentering transport holds simultaneously for every
selected label and every nonzero elapsed time on one Campbell-base full
measure event. -/
theorem ae_forall_stationaryPriorityClassTaggedStabilizedWaitingWorkResponse_campbellRecenter_eq_remoteCanonical
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∀ᵐ x ∂(Probability.Palm.targetPassiveProductBaseLaw
      (Probability.Queueing.stationaryPoissonWorkShiftInvariantLaw (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Pbase,
      ∀ k : ℤ, ∀ t : ℝ, t ≠ 0 →
        stationaryPriorityClassTaggedStabilizedWaitingWorkResponse meanService i
          ((multiclassStationaryPoissonWorkClassCampbellCertificate
            arrivalRate harrivalRate i).recenterAt x k, t) =
          stationaryPriorityRemotePastWaitingIdentifierContributionCanonical meanService
            (Sigma.mk i k)
            (Probability.Queueing.timedEmbeddedArrival x.1 k + t,
              multiclassStationaryPoissonWorkClassAssemble i x) := by
  filter_upwards [
    ae_stationaryPriorityArrival_noArrivalTies_all_campbellBase
      arrivalRate harrivalRate i,
    ae_all_exists_stationaryPriorityNetPastCutoff_campbellBaseFlow
      arrivalRate meanService harrivalRate hstable i,
    ae_all_stationaryPriorityWorkRequirement_positive_campbellBase
      arrivalRate meanService harrivalRate hmeanService i] with x hnoTies hcutoffs hpositive
  intro k t ht
  exact stationaryPriorityClassTaggedStabilizedWaitingWorkResponse_campbellRecenter_eq_remoteCanonical_of_baseGood
    arrivalRate meanService harrivalRate i x k t ht hnoTies hcutoffs hpositive

/-- Summing any real-valued customer statistic over the chronological finite
stationary ledger is the same as summing it class by class over the literal
labelled arrival windows.  This is a finite reindexing fact; it has no
probabilistic content. -/
theorem sum_map_stationaryPriorityArrivalWindowJobs_eq_sum_classwise
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n →
      (Probability.PoissonProcess.GoodSuspensionState × (ℤ → ℝ)))
    (left right : ℝ)
    (reward : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n) → ℝ) :
    ((stationaryPriorityArrivalWindowJobs meanService omega left right).map reward).sum =
      ∑ i, ∑ k ∈ stationaryPriorityArrivalWindowIndices omega left right i,
        reward (stationaryPriorityArrivalJobCoordinate meanService (Sigma.mk i k) omega) := by
  classical
  letI : DecidableRel (stationaryPriorityArrivalIndexLE omega) := Classical.decRel _
  letI : IsTrans (NonpreemptivePriorityArrivalIndex n)
      (stationaryPriorityArrivalIndexLE omega) :=
    ⟨fun _ _ _ => stationaryPriorityArrivalIndexLE_trans omega⟩
  letI : Std.Antisymm (stationaryPriorityArrivalIndexLE omega) :=
    ⟨fun _ _ => stationaryPriorityArrivalIndexLE_antisymm omega⟩
  letI : Std.Total (stationaryPriorityArrivalIndexLE omega) :=
    ⟨stationaryPriorityArrivalIndexLE_total omega⟩
  let ledger := nonpreemptivePriorityArrivalWindowIndices
    (stationaryPriorityArrivalWindowIndices omega left right)
  unfold stationaryPriorityArrivalWindowJobs
    canonicalStationaryPriorityArrivalWindowJobs
    canonicalStationaryPriorityArrivalWindowIndices
  simp only [List.map_map]
  change (ledger.sort (stationaryPriorityArrivalIndexLE omega) |>.map
      (fun q => reward (stationaryPriorityArrivalJobCoordinate meanService q omega))).sum = _
  calc
    (ledger.sort (stationaryPriorityArrivalIndexLE omega) |>.map
        (fun q => reward (stationaryPriorityArrivalJobCoordinate meanService q omega))).sum =
        (ledger.toList.map fun q =>
          reward (stationaryPriorityArrivalJobCoordinate meanService q omega)).sum :=
      ((Finset.sort_perm_toList ledger (stationaryPriorityArrivalIndexLE omega)).map _).sum_eq
    _ = ∑ q ∈ ledger, reward (stationaryPriorityArrivalJobCoordinate meanService q omega) := by
      simpa only [ledger.toList_toFinset] using
        (List.sum_toFinset
          (fun q => reward (stationaryPriorityArrivalJobCoordinate meanService q omega))
          ledger.nodup_toList).symm
    _ = ∑ i, ∑ k ∈ stationaryPriorityArrivalWindowIndices omega left right i,
        reward (stationaryPriorityArrivalJobCoordinate meanService (Sigma.mk i k) omega) := by
      unfold ledger nonpreemptivePriorityArrivalWindowIndices
      rw [Finset.sum_sigma]

/-- The classwise enumeration in the concrete Campbell certificate is the
corresponding literal stationary arrival window after the base input is
reassembled. -/
theorem multiclassStationaryPoissonWorkClassCampbell_arrivalsIn_eq_stationaryPriorityWindow
    {n : ℕ} (arrivalRate : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j) (i : Fin n)
    (x : StationaryPoissonWorkPath ×
      ({j : Fin n // j ≠ i} → StationaryPoissonWorkPath))
    (left right : ℝ) :
    (multiclassStationaryPoissonWorkClassCampbellCertificate
      arrivalRate harrivalRate i).arrivalsIn left right x =
      stationaryPriorityArrivalWindowIndices
        (multiclassStationaryPoissonWorkClassAssemble i x) left right i := by
  change Probability.Queueing.timedEmbeddedArrivalIndices left right x.1 =
    Probability.PoissonProcess.suspensionBaseArrivalIndices left right
      ((multiclassStationaryPoissonWorkClassAssemble i x) i).1
  rw [multiclassStationaryPoissonWorkClassAssemble_apply_eq]
  rfl

/-- On a globally collision-free Campbell base input, the elapsed-time
work-weighted occupation of a selected strict replay is the literal
original-time occupation of the corresponding finite-window customer. -/
theorem intervalIntegral_stationaryPriorityClassTaggedStrictReplayWorkWaiting_eq_originalFiniteCustomerOccupation_of_noArrivalTies_all
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j) (i : Fin n)
    (x : StationaryPoissonWorkPath ×
      ({j : Fin n // j ≠ i} → StationaryPoissonWorkPath))
    (k : ℤ) (left right : ℝ)
    (hleft : left ≤ Probability.Queueing.timedEmbeddedArrival x.1 k)
    (hright : Probability.Queueing.timedEmbeddedArrival x.1 k < right)
    (hnoTies : ∀ first second : NonpreemptivePriorityArrivalIndex n,
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival first.1
          (multiclassStationaryPoissonWorkClassAssemble i x) first.2 =
        Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival second.1
          (multiclassStationaryPoissonWorkClassAssemble i x) second.2 → first = second) :
    (∫ elapsed in 0..(right - Probability.Queueing.timedEmbeddedArrival x.1 k),
      stationaryPriorityClassTaggedWorkRequirement meanService i
        ((multiclassStationaryPoissonWorkClassCampbellCertificate
          arrivalRate harrivalRate i).recenterAt x k) *
        nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0)
          (stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
            meanService i
            ((multiclassStationaryPoissonWorkClassCampbellCertificate
              arrivalRate harrivalRate i).recenterAt x k)
            (Probability.Queueing.timedEmbeddedArrival x.1 k - left) elapsed)) =
      ∫ time in Probability.Queueing.timedEmbeddedArrival x.1 k..right,
        stationaryPriorityWorkRequirement meanService i
          (multiclassStationaryPoissonWorkClassAssemble i x) k *
        nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i k)
          (stationaryPriorityFiniteWindowState meanService
            (multiclassStationaryPoissonWorkClassAssemble i x) left time) := by
  let arrival := Probability.Queueing.timedEmbeddedArrival x.1 k
  let selected :=
    (multiclassStationaryPoissonWorkClassCampbellCertificate
      arrivalRate harrivalRate i).recenterAt x k
  let original : ℝ → ℝ := fun time =>
    stationaryPriorityWorkRequirement meanService i
      (multiclassStationaryPoissonWorkClassAssemble i x) k *
      nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i k)
        (stationaryPriorityFiniteWindowState meanService
          (multiclassStationaryPoissonWorkClassAssemble i x) left time)
  have hduration : 0 ≤ right - arrival := (sub_nonneg.mpr hright.le)
  have hpoint : ∀ elapsed : ℝ, 0 < elapsed →
      stationaryPriorityClassTaggedWorkRequirement meanService i selected *
        nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0)
          (stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
            meanService i selected (arrival - left) elapsed) =
        original (arrival + elapsed) := by
    intro elapsed helapsed
    have hwaiting :=
      stationaryPriorityClassTaggedStrictReplayWaitingIndicator_eq_originalFiniteWindow_of_noArrivalTies_all
        arrivalRate meanService harrivalRate i x k (arrival - left) elapsed
        (sub_nonneg.mpr hleft) helapsed hnoTies
    rw [stationaryPriorityClassTaggedWorkRequirement_campbellRecenter_eq_original
      arrivalRate meanService harrivalRate i x k, hwaiting]
    dsimp [original]
    congr 3; ring
  calc
    (∫ elapsed in 0..(right - arrival),
      stationaryPriorityClassTaggedWorkRequirement meanService i selected *
        nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0)
          (stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
            meanService i selected (arrival - left) elapsed)) =
        ∫ elapsed in 0..(right - arrival), original (arrival + elapsed) := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards with elapsed helapsed
          rw [Set.uIoc_of_le hduration] at helapsed
          exact hpoint elapsed helapsed.1
    _ = ∫ time in arrival..right, original time := by
          have hendpoint : arrival + (right - arrival) = right := by ring
          conv_rhs => rw [← hendpoint]
          simpa only [add_zero] using
            (intervalIntegral.integral_comp_add_left original arrival
              (a := 0) (b := right - arrival))
    _ = ∫ time in Probability.Queueing.timedEmbeddedArrival x.1 k..right,
        stationaryPriorityWorkRequirement meanService i
          (multiclassStationaryPoissonWorkClassAssemble i x) k *
        nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i k)
          (stationaryPriorityFiniteWindowState meanService
            (multiclassStationaryPoissonWorkClassAssemble i x) left time) := by
          rfl

/-- Once the finite global replay at a selected customer's observation epoch
has coalesced in the stationary-flow frame, the strict selected replay records
that customer's literal membership in the original-coordinate remote queue.
This is a deterministic finite-to-remote transport; it makes no almost-sure
or Campbell assertion. -/
theorem stationaryPriorityClassTaggedStrictReplayWaitingIndicator_eq_remotePastStateAt_of_noArrivalTies_all_of_flow_coalescence
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j) (i : Fin n)
    (x : StationaryPoissonWorkPath ×
      ({j : Fin n // j ≠ i} → StationaryPoissonWorkPath))
    (k : ℤ) (older t : ℝ) (holder : 0 ≤ older) (ht : 0 < t)
    (hnoTies : ∀ first second : NonpreemptivePriorityArrivalIndex n,
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival first.1
          (multiclassStationaryPoissonWorkClassAssemble i x) first.2 =
        Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival second.1
          (multiclassStationaryPoissonWorkClassAssemble i x) second.2 → first = second)
    (hcoalescence : liveEquivalentNonpreemptivePriorityWorkState
      (stationaryPriorityFiniteWindowState meanService
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
          (Probability.Queueing.timedEmbeddedArrival x.1 k + t)
          (multiclassStationaryPoissonWorkClassAssemble i x)) (-(older + t)) 0)
      (stationaryPriorityRemotePastState meanService
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
          (Probability.Queueing.timedEmbeddedArrival x.1 k + t)
          (multiclassStationaryPoissonWorkClassAssemble i x))) ) :
    nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0)
      (stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
        meanService i
        ((multiclassStationaryPoissonWorkClassCampbellCertificate
          arrivalRate harrivalRate i).recenterAt x k) older t) =
      nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i k)
        (stationaryPriorityRemotePastStateAt meanService
          (multiclassStationaryPoissonWorkClassAssemble i x)
          (Probability.Queueing.timedEmbeddedArrival x.1 k + t)) := by
  let omega := multiclassStationaryPoissonWorkClassAssemble i x
  let arrival := Probability.Queueing.timedEmbeddedArrival x.1 k
  have hfinite : nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0)
      (stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
        meanService i
        ((multiclassStationaryPoissonWorkClassCampbellCertificate
          arrivalRate harrivalRate i).recenterAt x k) older t) =
      nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i k)
        (stationaryPriorityFiniteWindowState meanService omega (arrival - older)
          (arrival + t)) := by
    simpa [omega, arrival] using
      (stationaryPriorityClassTaggedStrictReplayWaitingIndicator_eq_originalFiniteWindow_of_noArrivalTies_all
        arrivalRate meanService harrivalRate i x k older t holder ht hnoTies)
  have htrajectory : liveEquivalentNonpreemptivePriorityWorkState
      (stationaryPriorityFiniteWindowState meanService omega (arrival - older)
        (arrival + t))
      (stationaryPriorityRemotePastStateAt meanService omega (arrival + t)) := by
    apply liveEquivalent_stationaryPriorityFiniteWindowState_stationaryPriorityRemotePastStateAt_of_flow_coalescence
      meanService omega (arrival - older) (arrival + t)
    · intro first _ second _ heq
      exact hnoTies first second heq
    · have hleft : arrival - older - (arrival + t) = -(older + t) := by ring
      simpa [omega, arrival, hleft] using hcoalescence
  calc
    nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0)
        (stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
          meanService i
          ((multiclassStationaryPoissonWorkClassCampbellCertificate
            arrivalRate harrivalRate i).recenterAt x k) older t) =
        nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i k)
          (stationaryPriorityFiniteWindowState meanService omega (arrival - older)
            (arrival + t)) := hfinite
    _ = nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i k)
          (stationaryPriorityRemotePastStateAt meanService omega (arrival + t)) :=
      nonpreemptivePriorityWaitingIdentifierIndicator_eq_of_liveEquivalent
        (Sigma.mk i k) htrajectory

/-- The preceding finite-to-remote membership transport also preserves the
selected customer's work-weighted contribution. -/
theorem stationaryPriorityClassTaggedStrictReplayWorkWaitingIndicator_eq_remotePastStateAt_of_noArrivalTies_all_of_flow_coalescence
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j) (i : Fin n)
    (x : StationaryPoissonWorkPath ×
      ({j : Fin n // j ≠ i} → StationaryPoissonWorkPath))
    (k : ℤ) (older t : ℝ) (holder : 0 ≤ older) (ht : 0 < t)
    (hnoTies : ∀ first second : NonpreemptivePriorityArrivalIndex n,
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival first.1
          (multiclassStationaryPoissonWorkClassAssemble i x) first.2 =
        Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival second.1
          (multiclassStationaryPoissonWorkClassAssemble i x) second.2 → first = second)
    (hcoalescence : liveEquivalentNonpreemptivePriorityWorkState
      (stationaryPriorityFiniteWindowState meanService
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
          (Probability.Queueing.timedEmbeddedArrival x.1 k + t)
          (multiclassStationaryPoissonWorkClassAssemble i x)) (-(older + t)) 0)
      (stationaryPriorityRemotePastState meanService
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
          (Probability.Queueing.timedEmbeddedArrival x.1 k + t)
          (multiclassStationaryPoissonWorkClassAssemble i x))) ) :
    stationaryPriorityClassTaggedWorkRequirement meanService i
      ((multiclassStationaryPoissonWorkClassCampbellCertificate
        arrivalRate harrivalRate i).recenterAt x k) *
        nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0)
          (stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
            meanService i
            ((multiclassStationaryPoissonWorkClassCampbellCertificate
              arrivalRate harrivalRate i).recenterAt x k) older t) =
      stationaryPriorityWorkRequirement meanService i
        (multiclassStationaryPoissonWorkClassAssemble i x) k *
        nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i k)
          (stationaryPriorityRemotePastStateAt meanService
            (multiclassStationaryPoissonWorkClassAssemble i x)
            (Probability.Queueing.timedEmbeddedArrival x.1 k + t)) := by
  rw [stationaryPriorityClassTaggedWorkRequirement_campbellRecenter_eq_original
    arrivalRate meanService harrivalRate i x k,
    stationaryPriorityClassTaggedStrictReplayWaitingIndicator_eq_remotePastStateAt_of_noArrivalTies_all_of_flow_coalescence
      arrivalRate meanService harrivalRate i x k older t holder ht hnoTies hcoalescence]

/-- On a collision-free finite stationary window, the priority-filtered
waiting-work occupation is the classwise sum of the corresponding selected
strict-replay occupations.  This is still a finite pathwise equality: the
Campbell expectation and remote-past limit are deliberately separate. -/
theorem intervalIntegral_priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityFiniteWindowState_eq_sum_classwiseStrictReplayOccupations_of_noArrivalTies_all
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (omega : Fin n → StationaryPoissonWorkPath)
    (left right : ℝ) (hwindow : left ≤ right) (priority : Fin n)
    (hnoTies : ∀ first second : NonpreemptivePriorityArrivalIndex n,
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival first.1 omega first.2 =
        Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival second.1 omega second.2 →
      first = second) :
    (∫ time in left..right,
      priorityWaitingResidualWorkAtLeastAsUrgent
        (stationaryPriorityFiniteWindowState meanService omega left time) priority) =
      ∑ level, ∑ k ∈
        (multiclassStationaryPoissonWorkClassCampbellCertificate
          arrivalRate harrivalRate level).arrivalsIn left right
          (multiclassStationaryPoissonWorkClassSplit level omega),
        if level ≤ priority then
          ∫ elapsed in 0..(right - Probability.Queueing.timedEmbeddedArrival
            (multiclassStationaryPoissonWorkClassSplit level omega).1 k),
            stationaryPriorityClassTaggedWorkRequirement meanService level
              ((multiclassStationaryPoissonWorkClassCampbellCertificate
                arrivalRate harrivalRate level).recenterAt
                (multiclassStationaryPoissonWorkClassSplit level omega) k) *
              nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk level 0)
                (stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
                  meanService level
                  ((multiclassStationaryPoissonWorkClassCampbellCertificate
                    arrivalRate harrivalRate level).recenterAt
                    (multiclassStationaryPoissonWorkClassSplit level omega) k)
                  (Probability.Queueing.timedEmbeddedArrival
                    (multiclassStationaryPoissonWorkClassSplit level omega).1 k - left)
                  elapsed)
        else 0 := by
  rw [intervalIntegral_priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityFiniteWindowState_eq_sum_postArrivalCustomerOccupations
    meanService omega left right hwindow priority]
  rw [sum_map_stationaryPriorityArrivalWindowJobs_eq_sum_classwise
    meanService omega left right (fun job =>
      ∫ time in job.arrivalTime..right,
        stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingContribution
          meanService omega left time priority job)]
  apply Finset.sum_congr rfl
  intro level _
  have hindices :
      (multiclassStationaryPoissonWorkClassCampbellCertificate
        arrivalRate harrivalRate level).arrivalsIn left right
        (multiclassStationaryPoissonWorkClassSplit level omega) =
        stationaryPriorityArrivalWindowIndices omega left right level := by
    simpa only [multiclassStationaryPoissonWorkClassAssemble_split] using
      (multiclassStationaryPoissonWorkClassCampbell_arrivalsIn_eq_stationaryPriorityWindow
        arrivalRate harrivalRate level
        (multiclassStationaryPoissonWorkClassSplit level omega) left right)
  rw [← hindices]
  apply Finset.sum_congr rfl
  intro k hk
  have htime : left ≤ Probability.Queueing.timedEmbeddedArrival
      (multiclassStationaryPoissonWorkClassSplit level omega).1 k ∧
      Probability.Queueing.timedEmbeddedArrival
        (multiclassStationaryPoissonWorkClassSplit level omega).1 k < right := by
    change k ∈ Probability.Queueing.timedEmbeddedArrivalIndices left right
      (multiclassStationaryPoissonWorkClassSplit level omega).1 at hk
    exact Probability.Queueing.mem_timedEmbeddedArrivalIndices_iff left right
      (multiclassStationaryPoissonWorkClassSplit level omega).1 k |>.mp hk
  have hassemble : multiclassStationaryPoissonWorkClassAssemble level
      (multiclassStationaryPoissonWorkClassSplit level omega) = omega :=
    multiclassStationaryPoissonWorkClassAssemble_split level omega
  by_cases hpriority : level ≤ priority
  · have hnoTies' : ∀ first second : NonpreemptivePriorityArrivalIndex n,
        Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival first.1
            (multiclassStationaryPoissonWorkClassAssemble level
              (multiclassStationaryPoissonWorkClassSplit level omega)) first.2 =
          Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival second.1
            (multiclassStationaryPoissonWorkClassAssemble level
              (multiclassStationaryPoissonWorkClassSplit level omega)) second.2 →
          first = second := by
      simpa only [hassemble] using hnoTies
    have hbridge :=
      intervalIntegral_stationaryPriorityClassTaggedStrictReplayWorkWaiting_eq_originalFiniteCustomerOccupation_of_noArrivalTies_all
        arrivalRate meanService harrivalRate level
        (multiclassStationaryPoissonWorkClassSplit level omega) k left right
        htime.1 htime.2 hnoTies'
    simpa only [hpriority, if_pos, hassemble,
      stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingContribution,
      stationaryPriorityArrivalJobCoordinate] using hbridge.symm
  · simp [hpriority, stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingContribution,
      stationaryPriorityArrivalJobCoordinate]

/-- A literal remote-past waiting workload has a finite customer ledger on
every path on which the net-input cutoff exists.  This is a state-provenance
identity only: it does not yet identify the ledger's customer occupations
with a Palm expectation. -/
theorem priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityRemotePastState_eq_fixedLedgerAtLeastAsUrgentSum_of_exists_cutoff
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → StationaryPoissonWorkPath)
    (hcutoff : ∃ cutoff : ℝ, 0 ≤ cutoff ∧
      stationaryPriorityNetPastCutoff meanService omega cutoff)
    (priority : Fin n) :
    priorityWaitingResidualWorkAtLeastAsUrgent
      (stationaryPriorityRemotePastState meanService omega) priority =
      ((stationaryPriorityArrivalWindowJobs meanService omega (-hcutoff.choose) 0).map
        (stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingContribution
          meanService omega (-hcutoff.choose) 0 priority)).sum := by
  rw [stationaryPriorityRemotePastState_eq_finiteWindowState_of_exists_cutoff
    meanService omega hcutoff]
  exact priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityFiniteWindowState_eq_fixedLedgerAtLeastAsUrgentSum
    meanService omega (-hcutoff.choose) 0 0 (neg_nonpos.mpr hcutoff.choose_spec.1) le_rfl priority

/-- The cutoff-selected remote waiting workload is a finite labelled-arrival
sum.  Unlike the chronological-list form, this coordinate form is aligned
with the classwise Campbell enumerators and is therefore the state-side input
to a future stationary customer-coverage theorem. -/
theorem priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityRemotePastState_eq_sum_classwise_of_exists_cutoff
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → StationaryPoissonWorkPath)
    (hcutoff : ∃ cutoff : ℝ, 0 ≤ cutoff ∧
      stationaryPriorityNetPastCutoff meanService omega cutoff)
    (priority : Fin n) :
    priorityWaitingResidualWorkAtLeastAsUrgent
      (stationaryPriorityRemotePastState meanService omega) priority =
      ∑ level, ∑ k ∈ stationaryPriorityArrivalWindowIndices omega (-hcutoff.choose) 0 level,
        if level ≤ priority then
          stationaryPriorityWorkRequirement meanService level omega k *
            nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk level k)
              (stationaryPriorityRemotePastState meanService omega)
        else 0 := by
  let cutoff := hcutoff.choose
  have hstate : stationaryPriorityRemotePastState meanService omega =
      stationaryPriorityFiniteWindowState meanService omega (-cutoff) 0 := by
    simpa only [cutoff] using
      (stationaryPriorityRemotePastState_eq_finiteWindowState_of_exists_cutoff
        meanService omega hcutoff)
  rw [hstate]
  rw [priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityFiniteWindowState_eq_fixedLedgerAtLeastAsUrgentSum
    meanService omega (-cutoff) 0 0 (neg_nonpos.mpr hcutoff.choose_spec.1) le_rfl priority]
  rw [sum_map_stationaryPriorityArrivalWindowJobs_eq_sum_classwise
    meanService omega (-cutoff) 0
    (stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingContribution
      meanService omega (-cutoff) 0 priority)]
  apply Finset.sum_congr rfl
  intro level _
  apply Finset.sum_congr rfl
  intro k _
  by_cases hpriority : level ≤ priority
  · simp [stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingContribution,
      stationaryPriorityArrivalJobCoordinate, hpriority]
  · simp [stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingContribution,
      stationaryPriorityArrivalJobCoordinate, hpriority]

/-- Every identifier waiting in a cutoff-selected remote state occurs in the
finite stationary input ledger begun at that cutoff.  This is the finite
support fact needed to express a remote state as a countable customer sum. -/
theorem mem_stationaryPriorityArrivalWindowIndices_of_nonpreemptivePriorityWaitingIdentifier_stationaryPriorityRemotePastState_of_exists_cutoff
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → StationaryPoissonWorkPath)
    (hcutoff : ∃ cutoff : ℝ, 0 ≤ cutoff ∧
      stationaryPriorityNetPastCutoff meanService omega cutoff)
    (q : NonpreemptivePriorityArrivalIndex n)
    (hwaiting : nonpreemptivePriorityWaitingIdentifier q
      (stationaryPriorityRemotePastState meanService omega)) :
    q.2 ∈ stationaryPriorityArrivalWindowIndices omega (-hcutoff.choose) 0 q.1 := by
  let cutoff := hcutoff.choose
  have hstate : stationaryPriorityRemotePastState meanService omega =
      stationaryPriorityFiniteWindowState meanService omega (-cutoff) 0 := by
    simpa only [cutoff] using
      (stationaryPriorityRemotePastState_eq_finiteWindowState_of_exists_cutoff
        meanService omega hcutoff)
  rw [hstate] at hwaiting
  rcases hwaiting with ⟨level, job, hmember, hidentifier⟩
  have hledger : job ∈ stationaryPriorityArrivalWindowJobs meanService omega (-cutoff) 0 := by
    exact nonpreemptivePriorityWorkStateContainsJob_stationaryPriorityFiniteWindowState_of_le
      meanService omega (-cutoff) 0 0 (neg_nonpos.mpr hcutoff.choose_spec.1) le_rfl job
      (Or.inr (Or.inl ⟨level, hmember⟩))
  rcases (mem_stationaryPriorityArrivalWindowJobs_iff meanService omega (-cutoff) 0 job).mp
      hledger with ⟨jobClass, jobIndex, hindex, hjob⟩
  subst job
  rcases q with ⟨qClass, qIndex⟩
  change (Sigma.mk jobClass jobIndex : NonpreemptivePriorityArrivalIndex n) =
    Sigma.mk qClass qIndex at hidentifier
  injection hidentifier with hclass hindex'
  subst qClass
  subst qIndex
  simpa only [cutoff] using hindex

/-- The remote priority-filtered waiting workload is the countable sum of its
labelled customers' work contributions.  The sum has finite support on every
path with a net-input cutoff; writing it as a `tsum` makes the customer index
explicit for later Palm transport. -/
theorem priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityRemotePastState_eq_tsum_of_exists_cutoff
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → StationaryPoissonWorkPath)
    (hcutoff : ∃ cutoff : ℝ, 0 ≤ cutoff ∧
      stationaryPriorityNetPastCutoff meanService omega cutoff)
    (priority : Fin n) :
    priorityWaitingResidualWorkAtLeastAsUrgent
      (stationaryPriorityRemotePastState meanService omega) priority =
      ∑' q : NonpreemptivePriorityArrivalIndex n,
        if q.1 ≤ priority then
          stationaryPriorityWorkRequirement meanService q.1 omega q.2 *
            nonpreemptivePriorityWaitingIdentifierIndicator q
              (stationaryPriorityRemotePastState meanService omega)
        else 0 := by
  classical
  let cutoff := hcutoff.choose
  let state := stationaryPriorityRemotePastState meanService omega
  let f : NonpreemptivePriorityArrivalIndex n → ℝ := fun q =>
    if q.1 ≤ priority then
      stationaryPriorityWorkRequirement meanService q.1 omega q.2 *
        nonpreemptivePriorityWaitingIdentifierIndicator q state
    else 0
  let ledger := nonpreemptivePriorityArrivalWindowIndices
    (stationaryPriorityArrivalWindowIndices omega (-cutoff) 0)
  have hfinite : ∀ q ∉ ledger, f q = 0 := by
    intro q hq
    by_cases hpriority : q.1 ≤ priority
    · simp only [f, hpriority, if_pos]
      unfold nonpreemptivePriorityWaitingIdentifierIndicator
      by_cases hwaiting : nonpreemptivePriorityWaitingIdentifier q state
      · exfalso
        apply hq
        rcases q with ⟨qClass, qIndex⟩
        change Sigma.mk qClass qIndex ∈ ledger
        simpa [ledger, cutoff, state, nonpreemptivePriorityArrivalWindowIndices] using
          (mem_stationaryPriorityArrivalWindowIndices_of_nonpreemptivePriorityWaitingIdentifier_stationaryPriorityRemotePastState_of_exists_cutoff
            meanService omega hcutoff (Sigma.mk qClass qIndex) hwaiting)
      · simp [hwaiting]
    · simp [f, hpriority]
  calc
    priorityWaitingResidualWorkAtLeastAsUrgent state priority =
        ∑ q ∈ ledger, f q := by
      rw [priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityRemotePastState_eq_sum_classwise_of_exists_cutoff
        meanService omega hcutoff priority]
      unfold ledger nonpreemptivePriorityArrivalWindowIndices
      rw [Finset.sum_sigma]
    _ = ∑' q : NonpreemptivePriorityArrivalIndex n, f q :=
      (tsum_eq_sum hfinite).symm
    _ = ∑' q : NonpreemptivePriorityArrivalIndex n,
        if q.1 ≤ priority then
          stationaryPriorityWorkRequirement meanService q.1 omega q.2 *
            nonpreemptivePriorityWaitingIdentifierIndicator q
              (stationaryPriorityRemotePastState meanService omega)
        else 0 := by
      rfl

/-- At an arbitrary physical epoch, the remote priority-filtered waiting
work is the countable sum of the original-coordinate customer contributions.
The stationary flow's temporary integer labels are reindexed through the
explicit restoration equivalence, so this statement has the same literal
customer indices as a Campbell occupation calculation. -/
theorem priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityRemotePastStateAt_eq_tsum_of_exists_cutoff
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → StationaryPoissonWorkPath) (time : ℝ)
    (hcutoff : ∃ cutoff : ℝ, 0 ≤ cutoff ∧
      stationaryPriorityNetPastCutoff meanService
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow time omega) cutoff)
    (priority : Fin n) :
    priorityWaitingResidualWorkAtLeastAsUrgent
      (stationaryPriorityRemotePastStateAt meanService omega time) priority =
      ∑' q : NonpreemptivePriorityArrivalIndex n,
        if q.1 ≤ priority then
          stationaryPriorityWorkRequirement meanService q.1 omega q.2 *
            nonpreemptivePriorityWaitingIdentifierIndicator q
              (stationaryPriorityRemotePastStateAt meanService omega time)
        else 0 := by
  let flow := Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow time omega
  let state := stationaryPriorityRemotePastState meanService flow
  let restore := stationaryPriorityFlowRestoreEquiv omega time
  let f : NonpreemptivePriorityArrivalIndex n → ℝ := fun q =>
    if q.1 ≤ priority then
      stationaryPriorityWorkRequirement meanService q.1 omega q.2 *
        nonpreemptivePriorityWaitingIdentifierIndicator q
          (stationaryPriorityRemotePastStateAt meanService omega time)
    else 0
  calc
    priorityWaitingResidualWorkAtLeastAsUrgent
        (stationaryPriorityRemotePastStateAt meanService omega time) priority =
        priorityWaitingResidualWorkAtLeastAsUrgent state priority := by
          simpa [state, flow] using
            (priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityRemotePastStateAt
              meanService omega time priority)
    _ = ∑' r : NonpreemptivePriorityArrivalIndex n,
        if r.1 ≤ priority then
          stationaryPriorityWorkRequirement meanService r.1 flow r.2 *
            nonpreemptivePriorityWaitingIdentifierIndicator r state
        else 0 := by
          simpa [state, flow] using
            (priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityRemotePastState_eq_tsum_of_exists_cutoff
              meanService flow hcutoff priority)
    _ = ∑' r : NonpreemptivePriorityArrivalIndex n, f (restore r) := by
          apply tsum_congr
          intro r
          by_cases hr : r.1 ≤ priority
          · simp only [hr, if_pos]
            dsimp only [f]
            rw [show (restore r).1 = r.1 by rfl, if_pos hr]
            have hwork : stationaryPriorityWorkRequirement meanService r.1 flow r.2 =
                stationaryPriorityWorkRequirement meanService (restore r).1 omega
                  (restore r).2 := by
              simpa [flow, restore] using
                (stationaryPriorityWorkRequirement_flow_restore
                  meanService omega time r)
            have hwaiting :
                nonpreemptivePriorityWaitingIdentifierIndicator r state =
                  nonpreemptivePriorityWaitingIdentifierIndicator (restore r)
                    (stationaryPriorityRemotePastStateAt meanService omega time) := by
              have hiff : nonpreemptivePriorityWaitingIdentifier (restore r)
                  (stationaryPriorityRemotePastStateAt meanService omega time) ↔
                  nonpreemptivePriorityWaitingIdentifier r state := by
                simpa [state, flow, restore] using
                  (nonpreemptivePriorityWaitingIdentifier_stationaryPriorityRemotePastStateAt_restore_iff
                    meanService omega time r)
              unfold nonpreemptivePriorityWaitingIdentifierIndicator
              by_cases hwaiting : nonpreemptivePriorityWaitingIdentifier r state
              · simp [hwaiting, hiff.mpr hwaiting]
              · have hnot : ¬ nonpreemptivePriorityWaitingIdentifier (restore r)
                    (stationaryPriorityRemotePastStateAt meanService omega time) :=
                    fun h => hwaiting (hiff.mp h)
                simp [hwaiting, hnot]
            rw [hwork, hwaiting]
            rw [show (restore r).1 = r.1 by rfl]
          · dsimp only [f]
            rw [show (restore r).1 = r.1 by rfl, if_neg hr]
            rw [if_neg hr]
    _ = ∑' q : NonpreemptivePriorityArrivalIndex n, f q :=
          (restore.tsum_eq f)
    _ = ∑' q : NonpreemptivePriorityArrivalIndex n,
        if q.1 ≤ priority then
          stationaryPriorityWorkRequirement meanService q.1 omega q.2 *
            nonpreemptivePriorityWaitingIdentifierIndicator q
              (stationaryPriorityRemotePastStateAt meanService omega time)
        else 0 := by
          rfl

/-- The original-coordinate remote customer series has finite support
whenever the shifted remote state has a net-input cutoff.  This is the
summability form of the finite-ledger fact used by the remote state
representation. -/
theorem summable_stationaryPriorityRemotePastStateAtWaitingIdentifierContribution_of_exists_cutoff
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → StationaryPoissonWorkPath) (time : ℝ)
    (hcutoff : ∃ cutoff : ℝ, 0 ≤ cutoff ∧
      stationaryPriorityNetPastCutoff meanService
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow time omega) cutoff)
    (priority : Fin n) :
    Summable (fun q : NonpreemptivePriorityArrivalIndex n =>
      if q.1 ≤ priority then
        stationaryPriorityWorkRequirement meanService q.1 omega q.2 *
          nonpreemptivePriorityWaitingIdentifierIndicator q
            (stationaryPriorityRemotePastStateAt meanService omega time)
      else 0) := by
  classical
  let flow := Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow time omega
  let state := stationaryPriorityRemotePastState meanService flow
  let restore := stationaryPriorityFlowRestoreEquiv omega time
  let f : NonpreemptivePriorityArrivalIndex n → ℝ := fun q =>
    if q.1 ≤ priority then
      stationaryPriorityWorkRequirement meanService q.1 omega q.2 *
        nonpreemptivePriorityWaitingIdentifierIndicator q
          (stationaryPriorityRemotePastStateAt meanService omega time)
    else 0
  let g : NonpreemptivePriorityArrivalIndex n → ℝ := fun r =>
    if r.1 ≤ priority then
      stationaryPriorityWorkRequirement meanService r.1 flow r.2 *
        nonpreemptivePriorityWaitingIdentifierIndicator r state
    else 0
  let ledger := nonpreemptivePriorityArrivalWindowIndices
    (stationaryPriorityArrivalWindowIndices flow (-hcutoff.choose) 0)
  have hfinite : ∀ r ∉ ledger, g r = 0 := by
    intro r hr
    by_cases hpriority : r.1 ≤ priority
    · simp only [g, hpriority, if_pos]
      unfold nonpreemptivePriorityWaitingIdentifierIndicator
      by_cases hwaiting : nonpreemptivePriorityWaitingIdentifier r state
      · exfalso
        apply hr
        rcases r with ⟨rClass, rIndex⟩
        change Sigma.mk rClass rIndex ∈ ledger
        simpa [ledger, flow, state, nonpreemptivePriorityArrivalWindowIndices] using
          (mem_stationaryPriorityArrivalWindowIndices_of_nonpreemptivePriorityWaitingIdentifier_stationaryPriorityRemotePastState_of_exists_cutoff
            meanService flow hcutoff (Sigma.mk rClass rIndex) hwaiting)
      · simp [hwaiting]
    · simp [g, hpriority]
  have hsupport : Function.HasFiniteSupport g := by
    change Set.Finite (Function.support g)
    refine ledger.finite_toSet.subset ?_
    intro r hr
    by_contra hnotledger
    exact hr (hfinite r (by simpa [ledger] using hnotledger))
  have hgsummable : Summable g := summable_of_hasFiniteSupport hsupport
  have htransport : ∀ r, g r = f (restore r) := by
    intro r
    by_cases hr : r.1 ≤ priority
    · simp only [g, hr, if_pos]
      dsimp only [f]
      rw [show (restore r).1 = r.1 by rfl, if_pos hr]
      have hwork : stationaryPriorityWorkRequirement meanService r.1 flow r.2 =
          stationaryPriorityWorkRequirement meanService (restore r).1 omega
            (restore r).2 := by
        simpa [flow, restore] using
          (stationaryPriorityWorkRequirement_flow_restore meanService omega time r)
      have hwaiting :
          nonpreemptivePriorityWaitingIdentifierIndicator r state =
            nonpreemptivePriorityWaitingIdentifierIndicator (restore r)
              (stationaryPriorityRemotePastStateAt meanService omega time) := by
        have hiff : nonpreemptivePriorityWaitingIdentifier (restore r)
            (stationaryPriorityRemotePastStateAt meanService omega time) ↔
            nonpreemptivePriorityWaitingIdentifier r state := by
          simpa [state, flow, restore] using
            (nonpreemptivePriorityWaitingIdentifier_stationaryPriorityRemotePastStateAt_restore_iff
              meanService omega time r)
        unfold nonpreemptivePriorityWaitingIdentifierIndicator
        by_cases hwaiting : nonpreemptivePriorityWaitingIdentifier r state
        · simp [hwaiting, hiff.mpr hwaiting]
        · have hnot : ¬ nonpreemptivePriorityWaitingIdentifier (restore r)
              (stationaryPriorityRemotePastStateAt meanService omega time) :=
              fun h => hwaiting (hiff.mp h)
          simp [hwaiting, hnot]
      rw [hwork, hwaiting]
      rw [show (restore r).1 = r.1 by rfl]
    · dsimp only [f]
      rw [show (restore r).1 = r.1 by rfl, if_neg hr]
      simp [g, hr]
  have hfg : f = g ∘ restore.symm := by
    funext q
    calc
      f q = f (restore (restore.symm q)) := by
        rw [restore.apply_symm_apply]
      _ = g (restore.symm q) := (htransport (restore.symm q)).symm
      _ = (g ∘ restore.symm) q := rfl
  change Summable f
  rw [hfg]
  exact (restore.symm.summable_iff).2 hgsummable

/-- At every fixed physical epoch, the measurable nonnegative sum of
canonical customer contributions agrees almost surely with the literal
priority-filtered remote waiting workload.  Finite support of the literal
remote state makes the real-to-extended-real series conversion exact. -/
theorem ae_stationaryPriorityRemotePastAtLeastAsUrgentWaitingWorkCanonicalNN_eq_remotePastStateAt
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (time : ℝ) (priority : Fin n) :
    (fun omega : Fin n → StationaryPoissonWorkPath =>
      stationaryPriorityRemotePastAtLeastAsUrgentWaitingWorkCanonicalNN
        meanService priority (time, omega)) =ᵐ[
      Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate]
      (fun omega : Fin n → StationaryPoissonWorkPath =>
        ENNReal.ofReal
          (priorityWaitingResidualWorkAtLeastAsUrgent
            (stationaryPriorityRemotePastStateAt meanService omega time) priority)) := by
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
  have hcutoff : ∀ᵐ omega ∂P, ∃ cutoff : ℝ, 0 ≤ cutoff ∧
      stationaryPriorityNetPastCutoff meanService (flow time omega) cutoff := by
    refine MeasureTheory.ae_of_ae_map (μ := P) (f := flow time) (p := fun eta =>
      ∃ cutoff : ℝ, 0 ≤ cutoff ∧ stationaryPriorityNetPastCutoff meanService eta cutoff)
      hflow.measurable.aemeasurable ?_
    rw [hflow.map_eq]
    exact ae_exists_stationaryPriorityNetPastCutoff
      arrivalRate meanService harrivalRate hstable
  have hcontribution : ∀ᵐ omega ∂P, ∀ q : NonpreemptivePriorityArrivalIndex n,
      stationaryPriorityRemotePastWaitingIdentifierContributionCanonical
        meanService q (time, omega) =
        stationaryPriorityWorkRequirement meanService q.1 omega q.2 *
          nonpreemptivePriorityWaitingIdentifierIndicator q
            (stationaryPriorityRemotePastStateAt meanService omega time) := by
    rw [MeasureTheory.ae_all_iff]
    intro q
    exact ae_stationaryPriorityRemotePastWaitingIdentifierContributionCanonical_eq_remotePastStateAt
      arrivalRate meanService harrivalRate hmeanService hstable time q
  filter_upwards [hcutoff, hcontribution,
    ae_all_stationaryPriorityWorkRequirement_positive
      arrivalRate meanService harrivalRate hmeanService] with omega hcutoff hcontribution hpositive
  let f : NonpreemptivePriorityArrivalIndex n → ℝ := fun q =>
    if q.1 ≤ priority then
      stationaryPriorityWorkRequirement meanService q.1 omega q.2 *
        nonpreemptivePriorityWaitingIdentifierIndicator q
          (stationaryPriorityRemotePastStateAt meanService omega time)
    else 0
  have hnonnegative : ∀ q, 0 ≤ f q := by
    intro q
    by_cases hpriority : q.1 ≤ priority
    · simp only [f, hpriority, if_pos]
      unfold nonpreemptivePriorityWaitingIdentifierIndicator
      by_cases hwaiting : nonpreemptivePriorityWaitingIdentifier q
          (stationaryPriorityRemotePastStateAt meanService omega time)
      · simpa [hwaiting] using (hpositive q.1 q.2).le
      · simp [hwaiting]
    · simp [f, hpriority]
  have hsummable : Summable f := by
    simpa [f, flow] using
      (summable_stationaryPriorityRemotePastStateAtWaitingIdentifierContribution_of_exists_cutoff
        meanService omega time (by simpa [flow] using hcutoff) priority)
  have hremote :
      priorityWaitingResidualWorkAtLeastAsUrgent
        (stationaryPriorityRemotePastStateAt meanService omega time) priority =
      ∑' q : NonpreemptivePriorityArrivalIndex n, f q := by
    simpa [f, flow] using
      (priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityRemotePastStateAt_eq_tsum_of_exists_cutoff
        meanService omega time (by simpa [flow] using hcutoff) priority)
  calc
    stationaryPriorityRemotePastAtLeastAsUrgentWaitingWorkCanonicalNN
        meanService priority (time, omega) =
        ∑' q : NonpreemptivePriorityArrivalIndex n, ENNReal.ofReal (f q) := by
          unfold stationaryPriorityRemotePastAtLeastAsUrgentWaitingWorkCanonicalNN
          apply tsum_congr
          intro q
          by_cases hpriority : q.1 ≤ priority
          · simp [f, hpriority, hcontribution q]
          · simp [f, hpriority]
    _ = ENNReal.ofReal (∑' q : NonpreemptivePriorityArrivalIndex n, f q) := by
          exact (ENNReal.ofReal_tsum_of_nonneg hnonnegative hsummable).symm
    _ = ENNReal.ofReal
        (priorityWaitingResidualWorkAtLeastAsUrgent
          (stationaryPriorityRemotePastStateAt meanService omega time) priority) := by
          rw [hremote]

/-- The canonical nonnegative customer sum agrees almost everywhere on the
full physical-time/input product with the stationary remote priority-filtered
waiting workload.  The proof uses the fixed-time customer-sum identity and a
measurable representative of the remote observable before applying Fubini. -/
theorem ae_uncurry_stationaryPriorityRemotePastAtLeastAsUrgentWaitingWorkCanonicalNN_eq_remotePast_flow
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (priority : Fin n) :
    (stationaryPriorityRemotePastAtLeastAsUrgentWaitingWorkCanonicalNN
      meanService priority) =ᵐ[
      MeasureTheory.volume.prod
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate)]
      (fun p : ℝ × (Fin n → StationaryPoissonWorkPath) =>
        ENNReal.ofReal
          (stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork meanService priority
            (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow p.1 p.2))) := by
  let P := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact Probability.PoissonProcess.isProbabilityMeasure_multiclassStationaryPoissonWorkMeasure
      arrivalRate harrivalRate
  letI : SFinite P := by infer_instance
  let C := stationaryPriorityRemotePastAtLeastAsUrgentWaitingWorkCanonicalNN
    meanService priority
  let G : ℝ × (Fin n → StationaryPoissonWorkPath) → ENNReal := fun p =>
    ENNReal.ofReal
      (stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork meanService priority
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow p.1 p.2))
  have hCmeas : Measurable C := by
    simpa [C] using
      (measurable_uncurry_stationaryPriorityRemotePastAtLeastAsUrgentWaitingWorkCanonicalNN
        meanService priority)
  have hGmeas : AEMeasurable G (MeasureTheory.volume.prod P) := by
    simpa [G, P] using
      (aemeasurable_uncurry_stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork_flow
        arrivalRate meanService harrivalRate hmeanService hstable priority).ennreal_ofReal
  let Gm := hGmeas.mk G
  have hGm_meas : Measurable Gm := hGmeas.measurable_mk
  have hG_eq : G =ᵐ[MeasureTheory.volume.prod P] Gm := hGmeas.ae_eq_mk
  have hslice : ∀ time : ℝ, ∀ᵐ omega ∂P,
      C (time, omega) = G (time, omega) := by
    intro time
    filter_upwards [
      ae_stationaryPriorityRemotePastAtLeastAsUrgentWaitingWorkCanonicalNN_eq_remotePastStateAt
        arrivalRate meanService harrivalRate hmeanService hstable time priority] with omega hcanonical
    rw [priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityRemotePastStateAt
      meanService omega time priority] at hcanonical
    simpa [C, G, stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork] using hcanonical
  have hsliceM : ∀ᵐ time ∂MeasureTheory.volume, ∀ᵐ omega ∂P,
      C (time, omega) = Gm (time, omega) := by
    filter_upwards [MeasureTheory.Measure.ae_ae_of_ae_prod hG_eq] with time hGtime
    filter_upwards [hslice time, hGtime] with omega hsliceOmega hGtimeOmega
    exact hsliceOmega.trans hGtimeOmega
  have heqmeas : MeasurableSet {p : ℝ × (Fin n → StationaryPoissonWorkPath) |
      C p = Gm p} :=
    measurableSet_eq_fun hCmeas hGm_meas
  have hproduct : C =ᵐ[MeasureTheory.volume.prod P] Gm :=
    (MeasureTheory.Measure.ae_prod_iff_ae_ae heqmeas).2 hsliceM
  filter_upwards [hproduct, hG_eq] with p hp hG
  exact hp.trans hG.symm

/-- A selected customer's remote-initialized strict post-arrival execution
agrees with its literal original-coordinate stationary trajectory whenever
the selected pre-arrival state and the global finite replay have both
coalesced.  This is a deterministic transport statement: the selected
post-arrival construction starts from the same remote past, while the global
finite replay supplies the original arrival labels at the later physical
epoch. -/
theorem stationaryPriorityClassTaggedPostArrivalWaitingIndicator_eq_remotePastStateAt_of_coalescence
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j) (i : Fin n)
    (x : StationaryPoissonWorkPath ×
      ({j : Fin n // j ≠ i} → StationaryPoissonWorkPath))
    (k : ℤ) (older t : ℝ) (holder : 0 ≤ older) (ht : 0 < t)
    (hnoTies : ∀ first second : NonpreemptivePriorityArrivalIndex n,
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival first.1
          (multiclassStationaryPoissonWorkClassAssemble i x) first.2 =
        Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival second.1
          (multiclassStationaryPoissonWorkClassAssemble i x) second.2 → first = second)
    (hselected : liveEquivalentNonpreemptivePriorityWorkState
      (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i
        ((multiclassStationaryPoissonWorkClassCampbellCertificate
          arrivalRate harrivalRate i).recenterAt x k) (-older) 0)
      (stationaryPriorityClassTaggedRemotePastState meanService i
        ((multiclassStationaryPoissonWorkClassCampbellCertificate
          arrivalRate harrivalRate i).recenterAt x k)))
    (hglobal : liveEquivalentNonpreemptivePriorityWorkState
      (stationaryPriorityFiniteWindowState meanService
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
          (Probability.Queueing.timedEmbeddedArrival x.1 k + t)
          (multiclassStationaryPoissonWorkClassAssemble i x)) (-(older + t)) 0)
      (stationaryPriorityRemotePastState meanService
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
          (Probability.Queueing.timedEmbeddedArrival x.1 k + t)
          (multiclassStationaryPoissonWorkClassAssemble i x))) ) :
    nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0)
      (stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
        meanService i
        ((multiclassStationaryPoissonWorkClassCampbellCertificate
          arrivalRate harrivalRate i).recenterAt x k) t) =
      nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i k)
        (stationaryPriorityRemotePastStateAt meanService
          (multiclassStationaryPoissonWorkClassAssemble i x)
          (Probability.Queueing.timedEmbeddedArrival x.1 k + t)) := by
  let z := (multiclassStationaryPoissonWorkClassCampbellCertificate
    arrivalRate harrivalRate i).recenterAt x k
  have hselectedReplay :
      stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
        meanService i z older t =
        nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0)
          (stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
            meanService i z t) := by
    exact stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon_eq_of_liveEquivalent
      meanService i z older t (by simpa [z] using hselected)
  have hglobalReplay :
      stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
        meanService i z older t =
        nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i k)
          (stationaryPriorityRemotePastStateAt meanService
            (multiclassStationaryPoissonWorkClassAssemble i x)
            (Probability.Queueing.timedEmbeddedArrival x.1 k + t)) := by
    simpa [z] using
      (stationaryPriorityClassTaggedStrictReplayWaitingIndicator_eq_remotePastStateAt_of_noArrivalTies_all_of_flow_coalescence
        arrivalRate meanService harrivalRate i x k older t holder ht hnoTies hglobal)
  exact hselectedReplay.symm.trans hglobalReplay

/-- The deterministic post-arrival/remote-trajectory bridge also transports
the selected service-work contribution.  This is the exact customer summand
that will be integrated by the final Campbell occupation argument. -/
theorem stationaryPriorityClassTaggedPostArrivalWorkWaitingIndicator_eq_remotePastStateAt_of_coalescence
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j) (i : Fin n)
    (x : StationaryPoissonWorkPath ×
      ({j : Fin n // j ≠ i} → StationaryPoissonWorkPath))
    (k : ℤ) (older t : ℝ) (holder : 0 ≤ older) (ht : 0 < t)
    (hnoTies : ∀ first second : NonpreemptivePriorityArrivalIndex n,
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival first.1
          (multiclassStationaryPoissonWorkClassAssemble i x) first.2 =
        Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival second.1
          (multiclassStationaryPoissonWorkClassAssemble i x) second.2 → first = second)
    (hselected : liveEquivalentNonpreemptivePriorityWorkState
      (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i
        ((multiclassStationaryPoissonWorkClassCampbellCertificate
          arrivalRate harrivalRate i).recenterAt x k) (-older) 0)
      (stationaryPriorityClassTaggedRemotePastState meanService i
        ((multiclassStationaryPoissonWorkClassCampbellCertificate
          arrivalRate harrivalRate i).recenterAt x k)))
    (hglobal : liveEquivalentNonpreemptivePriorityWorkState
      (stationaryPriorityFiniteWindowState meanService
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
          (Probability.Queueing.timedEmbeddedArrival x.1 k + t)
          (multiclassStationaryPoissonWorkClassAssemble i x)) (-(older + t)) 0)
      (stationaryPriorityRemotePastState meanService
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
          (Probability.Queueing.timedEmbeddedArrival x.1 k + t)
          (multiclassStationaryPoissonWorkClassAssemble i x))) ) :
    stationaryPriorityClassTaggedWorkRequirement meanService i
        ((multiclassStationaryPoissonWorkClassCampbellCertificate
          arrivalRate harrivalRate i).recenterAt x k) *
      nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0)
        (stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
          meanService i
          ((multiclassStationaryPoissonWorkClassCampbellCertificate
            arrivalRate harrivalRate i).recenterAt x k) t) =
      stationaryPriorityWorkRequirement meanService i
        (multiclassStationaryPoissonWorkClassAssemble i x) k *
      nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i k)
        (stationaryPriorityRemotePastStateAt meanService
          (multiclassStationaryPoissonWorkClassAssemble i x)
          (Probability.Queueing.timedEmbeddedArrival x.1 k + t)) := by
  rw [stationaryPriorityClassTaggedWorkRequirement_campbellRecenter_eq_original
    arrivalRate meanService harrivalRate i x k,
    stationaryPriorityClassTaggedPostArrivalWaitingIndicator_eq_remotePastStateAt_of_coalescence
      arrivalRate meanService harrivalRate i x k older t holder ht hnoTies hselected hglobal]

/-- The nonnegative selected-Palm waiting-work coverage summand is exactly
the corresponding original-label customer contribution to the remote
trajectory, once the selected and global remote-past coalescences are in
place.  This is the pointwise summand needed by the final Tonelli/Campbell
comparison; its hypotheses are deterministic and contain no compensation
claim. -/
theorem stationaryPriorityClassTaggedWaitingWorkCoverageNN_eq_remotePastStateAtContribution_of_coalescence
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j) (i : Fin n)
    (x : StationaryPoissonWorkPath ×
      ({j : Fin n // j ≠ i} → StationaryPoissonWorkPath))
    (k : ℤ) (older t : ℝ) (holder : 0 ≤ older) (ht : 0 < t)
    (hnoTies : ∀ first second : NonpreemptivePriorityArrivalIndex n,
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival first.1
          (multiclassStationaryPoissonWorkClassAssemble i x) first.2 =
        Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival second.1
          (multiclassStationaryPoissonWorkClassAssemble i x) second.2 → first = second)
    (hselected : liveEquivalentNonpreemptivePriorityWorkState
      (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i
        ((multiclassStationaryPoissonWorkClassCampbellCertificate
          arrivalRate harrivalRate i).recenterAt x k) (-older) 0)
      (stationaryPriorityClassTaggedRemotePastState meanService i
        ((multiclassStationaryPoissonWorkClassCampbellCertificate
          arrivalRate harrivalRate i).recenterAt x k)))
    (hglobal : liveEquivalentNonpreemptivePriorityWorkState
      (stationaryPriorityFiniteWindowState meanService
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
          (Probability.Queueing.timedEmbeddedArrival x.1 k + t)
          (multiclassStationaryPoissonWorkClassAssemble i x)) (-(older + t)) 0)
      (stationaryPriorityRemotePastState meanService
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
          (Probability.Queueing.timedEmbeddedArrival x.1 k + t)
          (multiclassStationaryPoissonWorkClassAssemble i x))) )
    (hwaiting : nonpreemptivePriorityWaitingIdentifier (Sigma.mk i 0)
      (stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon meanService i
        ((multiclassStationaryPoissonWorkClassCampbellCertificate
          arrivalRate harrivalRate i).recenterAt x k) t) ↔
        t < stationaryPriorityClassTaggedQueueWait meanService i
          ((multiclassStationaryPoissonWorkClassCampbellCertificate
            arrivalRate harrivalRate i).recenterAt x k)) :
    stationaryPriorityClassTaggedWaitingWorkCoverageNN meanService i
      ((multiclassStationaryPoissonWorkClassCampbellCertificate
        arrivalRate harrivalRate i).recenterAt x k) t =
      ENNReal.ofReal
        (stationaryPriorityWorkRequirement meanService i
          (multiclassStationaryPoissonWorkClassAssemble i x) k *
          nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i k)
            (stationaryPriorityRemotePastStateAt meanService
              (multiclassStationaryPoissonWorkClassAssemble i x)
              (Probability.Queueing.timedEmbeddedArrival x.1 k + t))) := by
  let z := (multiclassStationaryPoissonWorkClassCampbellCertificate
    arrivalRate harrivalRate i).recenterAt x k
  let post := stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
    meanService i z t
  let remote := stationaryPriorityRemotePastStateAt meanService
    (multiclassStationaryPoissonWorkClassAssemble i x)
    (Probability.Queueing.timedEmbeddedArrival x.1 k + t)
  have hwork :=
    stationaryPriorityClassTaggedPostArrivalWorkWaitingIndicator_eq_remotePastStateAt_of_coalescence
      arrivalRate meanService harrivalRate i x k older t holder ht hnoTies hselected hglobal
  by_cases hwait : t < stationaryPriorityClassTaggedQueueWait meanService i z
  · have hpost : nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0) post = 1 := by
      have hpostWaiting : nonpreemptivePriorityWaitingIdentifier (Sigma.mk i 0) post := by
        dsimp [post, z]
        exact hwaiting.mpr (by simpa [z] using hwait)
      unfold nonpreemptivePriorityWaitingIdentifierIndicator
      simp [hpostWaiting]
    have hreal : stationaryPriorityClassTaggedWorkRequirement meanService i z =
        stationaryPriorityWorkRequirement meanService i
          (multiclassStationaryPoissonWorkClassAssemble i x) k *
          nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i k) remote := by
      simpa [z, post, remote, hpost] using hwork
    change (if 0 ≤ t ∧ t < stationaryPriorityClassTaggedQueueWait meanService i z then
      ENNReal.ofReal (stationaryPriorityClassTaggedWorkRequirement meanService i z) else 0) = _
    rw [if_pos ⟨ht.le, hwait⟩, hreal]
  · have hpost : nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0) post = 0 := by
      unfold nonpreemptivePriorityWaitingIdentifierIndicator
      have hnot : ¬ nonpreemptivePriorityWaitingIdentifier (Sigma.mk i 0) post := by
        intro h
        exact hwait (by simpa [z, post] using (hwaiting.mp h))
      simp [hnot]
    have hreal : 0 = stationaryPriorityWorkRequirement meanService i
        (multiclassStationaryPoissonWorkClassAssemble i x) k *
        nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i k) remote := by
      simpa [z, post, remote, hpost] using hwork
    change (if 0 ≤ t ∧ t < stationaryPriorityClassTaggedQueueWait meanService i z then
      ENNReal.ofReal (stationaryPriorityClassTaggedWorkRequirement meanService i z) else 0) = _
    rw [if_neg (by exact fun h => hwait h.2), ← hreal]
    simp

/-- An existential-cutoff version of the waiting-work contribution identity.
It chooses one finite history long enough for both selected and global
remote-past representatives, so no arbitrary cutoff witness is built into the
statement. -/
theorem stationaryPriorityClassTaggedWaitingWorkCoverageNN_eq_remotePastStateAtContribution_of_exists_cutoffs
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j) (i : Fin n)
    (x : StationaryPoissonWorkPath ×
      ({j : Fin n // j ≠ i} → StationaryPoissonWorkPath))
    (k : ℤ) (t : ℝ) (ht : 0 < t)
    (hnoTies : ∀ first second : NonpreemptivePriorityArrivalIndex n,
      Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival first.1
          (multiclassStationaryPoissonWorkClassAssemble i x) first.2 =
        Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival second.1
          (multiclassStationaryPoissonWorkClassAssemble i x) second.2 → first = second)
    (hselectedCutoff : ∃ cutoff : ℝ, 0 ≤ cutoff ∧
      stationaryPriorityClassTaggedNetPastCutoff meanService i
        ((multiclassStationaryPoissonWorkClassCampbellCertificate
          arrivalRate harrivalRate i).recenterAt x k) cutoff)
    (hglobalCutoff : ∃ cutoff : ℝ, 0 ≤ cutoff ∧
      stationaryPriorityNetPastCutoff meanService
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
          (Probability.Queueing.timedEmbeddedArrival x.1 k + t)
          (multiclassStationaryPoissonWorkClassAssemble i x)) cutoff)
    (hselectedPositive : ∀ j : Fin n, ∀ m : ℤ,
      0 < stationaryPriorityClassTaggedWorkRequirementAt meanService i
        ((multiclassStationaryPoissonWorkClassCampbellCertificate
          arrivalRate harrivalRate i).recenterAt x k) j m)
    (hglobalPositive : ∀ j : Fin n, ∀ m : ℤ,
      0 < stationaryPriorityWorkRequirement meanService j
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
          (Probability.Queueing.timedEmbeddedArrival x.1 k + t)
          (multiclassStationaryPoissonWorkClassAssemble i x)) m)
    (hwaiting : nonpreemptivePriorityWaitingIdentifier (Sigma.mk i 0)
      (stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon meanService i
        ((multiclassStationaryPoissonWorkClassCampbellCertificate
          arrivalRate harrivalRate i).recenterAt x k) t) ↔
        t < stationaryPriorityClassTaggedQueueWait meanService i
          ((multiclassStationaryPoissonWorkClassCampbellCertificate
            arrivalRate harrivalRate i).recenterAt x k)) :
    stationaryPriorityClassTaggedWaitingWorkCoverageNN meanService i
      ((multiclassStationaryPoissonWorkClassCampbellCertificate
        arrivalRate harrivalRate i).recenterAt x k) t =
      ENNReal.ofReal
        (stationaryPriorityWorkRequirement meanService i
          (multiclassStationaryPoissonWorkClassAssemble i x) k *
          nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i k)
            (stationaryPriorityRemotePastStateAt meanService
              (multiclassStationaryPoissonWorkClassAssemble i x)
              (Probability.Queueing.timedEmbeddedArrival x.1 k + t))) := by
  let older := max hselectedCutoff.choose (hglobalCutoff.choose - t)
  have holder : 0 ≤ older := by
    dsimp [older]
    exact le_max_of_le_left hselectedCutoff.choose_spec.1
  have hselectedOlder : hselectedCutoff.choose ≤ older := by
    dsimp [older]
    exact le_max_left _ _
  have hglobalOlder : hglobalCutoff.choose ≤ older + t := by
    dsimp [older]
    have hmax : hglobalCutoff.choose - t ≤ max hselectedCutoff.choose
        (hglobalCutoff.choose - t) := le_max_right _ _
    linarith
  have hselected : liveEquivalentNonpreemptivePriorityWorkState
      (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i
        ((multiclassStationaryPoissonWorkClassCampbellCertificate
          arrivalRate harrivalRate i).recenterAt x k) (-older) 0)
      (stationaryPriorityClassTaggedRemotePastState meanService i
        ((multiclassStationaryPoissonWorkClassCampbellCertificate
          arrivalRate harrivalRate i).recenterAt x k)) := by
    rw [stationaryPriorityClassTaggedRemotePastState_eq_finiteWindowState_of_exists_cutoff
      meanService i _ hselectedCutoff]
    apply liveEquivalent_canonicalStationaryPriorityClassTaggedFiniteWindowState_of_netPastCutoff
      meanService i _ hselectedCutoff.choose older hselectedCutoff.choose_spec.2
      (multiclassStationaryPoissonWorkClassCampbellRecenter_gapPath_good
        arrivalRate harrivalRate i x k)
      hselectedCutoff.choose_spec.1 hselectedOlder
    intro job hjob
    rcases (mem_canonicalStationaryPriorityClassTaggedArrivalWindowJobs_iff
      meanService i _ (-older) 0 job).mp hjob with ⟨j, m, _, hcoordinate⟩
    subst job
    exact hselectedPositive j m
  have hglobal : liveEquivalentNonpreemptivePriorityWorkState
      (stationaryPriorityFiniteWindowState meanService
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
          (Probability.Queueing.timedEmbeddedArrival x.1 k + t)
          (multiclassStationaryPoissonWorkClassAssemble i x)) (-(older + t)) 0)
      (stationaryPriorityRemotePastState meanService
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow
          (Probability.Queueing.timedEmbeddedArrival x.1 k + t)
          (multiclassStationaryPoissonWorkClassAssemble i x))) := by
    rw [stationaryPriorityRemotePastState_eq_finiteWindowState_of_exists_cutoff
      meanService _ hglobalCutoff]
    apply liveEquivalent_stationaryPriorityFiniteWindowState_of_netPastCutoff
      meanService _ hglobalCutoff.choose (older + t) hglobalCutoff.choose_spec.2
      hglobalCutoff.choose_spec.1 hglobalOlder
    intro job hjob
    rcases (mem_stationaryPriorityArrivalWindowJobs_iff
      meanService _ (-(older + t)) 0 job).mp hjob with ⟨j, m, _, hcoordinate⟩
    subst job
    exact hglobalPositive j m
  exact stationaryPriorityClassTaggedWaitingWorkCoverageNN_eq_remotePastStateAtContribution_of_coalescence
    arrivalRate meanService harrivalRate i x k older t holder ht hnoTies hselected hglobal hwaiting

end

end AppliedModelingLib.Queueing

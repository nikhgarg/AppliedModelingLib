import GHKR22BiasBounties.MeasureFalsifyAndUpdate
import GHKR22BiasBounties.MonotoneBounty

/-!
# Monotone bias bounties on arbitrary measurable populations

This file gives the arbitrary-distribution form of corrected Algorithm 4 and
Theorem 14.  It reuses the executable state machine and its exact combinatorial
query accounting, while interpreting every population loss and repair score
as an integral under a general probability measure.
-/

namespace GHKR22BiasBounties

noncomputable section

open MeasureTheory ProbabilityTheory
open AppliedModelingLib Probability

/-! ## Measurability invariant -/

/-- Every model and group that can be selected by the global state machine is
measurable. -/
def MeasureMonotoneBountyStateMeasurable
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (state : MonotoneBountyState X Y) : Prop :=
  MeasurableModel state.current ∧
    (∀ group ∈ state.protectedGroups, MeasurableGroup group) ∧
    (∀ model ∈ state.publicModels, MeasurableModel model) ∧
    (∀ proposal ∈ state.remainingRepairs, MeasureProposalMeasurable proposal)

/-- The repair grid consists of measurable proposals when both axes are
measurable. -/
theorem measureProposalMeasurable_mem_repairCandidates
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {groups : List (Group X)} {models : List (Model X Y)}
    (hgroups : ∀ group ∈ groups, MeasurableGroup group)
    (hmodels : ∀ model ∈ models, MeasurableModel model) :
    ∀ proposal ∈ repairCandidates groups models,
      MeasureProposalMeasurable proposal := by
  intro proposal hproposal
  rw [repairCandidates] at hproposal
  rcases List.mem_flatMap.mp hproposal with ⟨group, hgroup, hproposal⟩
  rcases List.mem_map.mp hproposal with ⟨model, hmodel, rfl⟩
  exact ⟨hgroups group hgroup, hmodels model hmodel⟩

/-- Publishing preserves the measurable-state invariant. -/
theorem publishMonotoneBountyState_measurable
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {state : MonotoneBountyState X Y}
    (hstate : MeasureMonotoneBountyStateMeasurable state) :
    MeasureMonotoneBountyStateMeasurable (publishMonotoneBountyState state) := by
  unfold MeasureMonotoneBountyStateMeasurable at hstate ⊢
  rcases hstate with ⟨hcurrent, hgroups, hmodels, _⟩
  refine ⟨hcurrent, ?_, ?_, ?_⟩
  · simpa [publishMonotoneBountyState] using hgroups
  · intro model hmodel
    simp only [publishMonotoneBountyState, List.mem_cons] at hmodel
    rcases hmodel with rfl | hmodel
    · exact hcurrent
    · exact hmodels model hmodel
  · simp [publishMonotoneBountyState]

/-- Starting or restarting a repair scan preserves measurability. -/
theorem restartMonotoneRepairScan_measurable
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {state : MonotoneBountyState X Y}
    (hstate : MeasureMonotoneBountyStateMeasurable state) :
    MeasureMonotoneBountyStateMeasurable (restartMonotoneRepairScan state) := by
  rcases hstate with ⟨hcurrent, hgroups, hmodels, hremaining⟩
  cases hcandidates : repairCandidates state.protectedGroups state.publicModels with
  | nil =>
      simpa [restartMonotoneRepairScan, hcandidates] using
        publishMonotoneBountyState_measurable
          (show MeasureMonotoneBountyStateMeasurable state from
            ⟨hcurrent, hgroups, hmodels, hremaining⟩)
  | cons candidate rest =>
      simp only [restartMonotoneRepairScan, hcandidates]
      refine ⟨hcurrent, hgroups, hmodels, ?_⟩
      intro proposal hproposal
      apply measureProposalMeasurable_mem_repairCandidates hgroups hmodels proposal
      simpa [hcandidates] using hproposal

/-- One explicit global transition preserves the measurable-state invariant. -/
theorem monotoneBountyStepFromDecision_measurable
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (U : ℕ) (strategy : AdaptiveMonotoneProposalStrategy X Y)
    (hstrategy : ∀ transcript, MeasureProposalMeasurable (strategy transcript))
    (state : MonotoneBountyState X Y)
    (hstate : MeasureMonotoneBountyStateMeasurable state)
    (decision : CertificateDecision) :
    MeasureMonotoneBountyStateMeasurable
      (monotoneBountyStepFromDecision U strategy state decision) := by
  unfold MeasureMonotoneBountyStateMeasurable at hstate ⊢
  rcases hstate with ⟨hcurrent, hgroups, hmodels, hremainingMeasurable⟩
  cases hremaining : state.remainingRepairs with
  | nil =>
      by_cases hmore : state.externalProcessed < U
      · let proposal := strategy state.reverseTranscript.reverse
        have hproposal := hstrategy state.reverseTranscript.reverse
        cases decision with
        | rejected =>
            simpa [monotoneBountyStepFromDecision, monotoneBountyStepCore,
              hremaining, hmore] using
                (show MeasurableModel state.current ∧
                    (∀ group ∈ state.protectedGroups, MeasurableGroup group) ∧
                    (∀ model ∈ state.publicModels, MeasurableModel model) ∧
                    (∀ p ∈ ([] : List (ProposedUpdate X Y)),
                      MeasureProposalMeasurable p) from
                  ⟨hcurrent, hgroups, hmodels, by simp⟩)
        | accepted =>
            have hupdated : MeasureMonotoneBountyStateMeasurable
                { state with
                  current := listUpdate state.current proposal.group proposal.replacement
                  accepted := state.accepted + 1
                  externalProcessed := state.externalProcessed + 1
                  protectedGroups := proposal.group :: state.protectedGroups } := by
              refine ⟨measurableModel_listUpdate hcurrent hproposal.2 hproposal.1,
                ?_, hmodels, ?_⟩
              · intro group hgroup
                simp only [List.mem_cons] at hgroup
                rcases hgroup with rfl | hgroup
                · exact hproposal.1
                · exact hgroups group hgroup
              · simpa [hremaining] using hremainingMeasurable
            simpa [MeasureMonotoneBountyStateMeasurable,
              monotoneBountyStepFromDecision, monotoneBountyStepCore,
              hremaining, hmore, proposal] using
                restartMonotoneRepairScan_measurable hupdated
      · cases decision with
        | rejected =>
            simp only [monotoneBountyStepFromDecision, monotoneBountyStepCore,
              hremaining, if_neg hmore]
            exact ⟨hcurrent, hgroups, hmodels, by simp⟩
        | accepted =>
            simp only [monotoneBountyStepFromDecision, monotoneBountyStepCore,
              hremaining, if_neg hmore]
            exact ⟨hcurrent, hgroups, hmodels, by simp⟩
  | cons candidate rest =>
      have hcandidate : MeasureProposalMeasurable candidate :=
        hremainingMeasurable candidate (by simp [hremaining])
      cases decision with
      | accepted =>
          have hupdated : MeasureMonotoneBountyStateMeasurable
              { state with
                current := listUpdate state.current candidate.group candidate.replacement
                accepted := state.accepted + 1 } := by
            exact ⟨measurableModel_listUpdate hcurrent hcandidate.2 hcandidate.1,
              hgroups, hmodels, hremainingMeasurable⟩
          simpa [MeasureMonotoneBountyStateMeasurable,
            monotoneBountyStepFromDecision, monotoneBountyStepCore,
            hremaining] using restartMonotoneRepairScan_measurable hupdated
      | rejected =>
          cases rest with
          | nil =>
              let advanced : MonotoneBountyState X Y :=
                { state with
                  remainingRepairs := []
                  rejectedRepairsReverse := candidate :: state.rejectedRepairsReverse }
              have hadvanced : MeasureMonotoneBountyStateMeasurable advanced := by
                exact ⟨hcurrent, hgroups, hmodels, by simp [advanced]⟩
              simpa [MeasureMonotoneBountyStateMeasurable, advanced,
                monotoneBountyStepFromDecision,
                monotoneBountyStepCore, hremaining] using
                  publishMonotoneBountyState_measurable hadvanced
          | cons next tail =>
              simp only [monotoneBountyStepFromDecision,
                monotoneBountyStepCore, hremaining]
              refine ⟨hcurrent, hgroups, hmodels, ?_⟩
              intro proposal hproposal
              apply hremainingMeasurable proposal
              simp only [List.mem_cons] at hproposal
              rw [hremaining]
              simp only [List.mem_cons]
              exact Or.inr hproposal

/-- Every transcript-reconstructed global state is measurable. -/
theorem monotoneBountyStateFromTranscript_measurable
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {initial : Model X Y} (hinitial : MeasurableModel initial)
    (U : ℕ) (strategy : AdaptiveMonotoneProposalStrategy X Y)
    (hstrategy : ∀ transcript, MeasureProposalMeasurable (strategy transcript)) :
    ∀ transcript,
      MeasureMonotoneBountyStateMeasurable
        (monotoneBountyStateFromTranscript initial U strategy transcript) := by
  intro transcript
  induction transcript using List.reverseRecOn with
  | nil =>
      simp only [monotoneBountyStateFromTranscript, monotoneBountyReplayAux,
        MeasureMonotoneBountyStateMeasurable, initialMonotoneBountyState,
        List.mem_singleton, List.not_mem_nil, forall_const]
      exact ⟨hinitial, by simp, fun model hmodel => hmodel ▸ hinitial, by simp⟩
  | append_singleton transcript decision ih =>
      rw [monotoneBountyStateFromTranscript_append_singleton]
      exact monotoneBountyStepFromDecision_measurable U strategy hstrategy _ ih decision

/-- Every query in the induced shared checker stream is measurable. -/
theorem measureSubmissionMeasurable_monotoneBountySubmissionStrategy
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {initial : Model X Y} (hinitial : MeasurableModel initial)
    (U : ℕ) (strategy : AdaptiveMonotoneProposalStrategy X Y)
    (hstrategy : ∀ transcript, MeasureProposalMeasurable (strategy transcript)) :
    ∀ transcript,
      MeasureSubmissionMeasurable
        (monotoneBountySubmissionStrategy initial U strategy transcript) := by
  intro transcript
  let state := monotoneBountyStateFromTranscript initial U strategy transcript
  have hstate := monotoneBountyStateFromTranscript_measurable hinitial U strategy
    hstrategy transcript
  rcases hstate with ⟨hcurrent, hgroups, hmodels, hremainingMeasurable⟩
  change MeasureSubmissionMeasurable (monotoneBountySubmission U strategy state)
  cases hremaining : state.remainingRepairs with
  | nil =>
      by_cases hmore : state.externalProcessed < U
      · have hproposal := hstrategy state.reverseTranscript.reverse
        simpa [MeasureSubmissionMeasurable, monotoneBountySubmission,
          hremaining, hmore] using
            (show MeasurableModel state.current ∧ MeasurableGroup
                (strategy state.reverseTranscript.reverse).group ∧
                MeasurableModel (strategy state.reverseTranscript.reverse).replacement from
              ⟨hcurrent, hproposal.1, hproposal.2⟩)
      · simpa [MeasureSubmissionMeasurable, monotoneBountySubmission,
          hremaining, hmore, repairNoopSubmission] using
            (show MeasurableModel state.current ∧
                MeasurableGroup (fun _ : X => false) ∧ MeasurableModel state.current from
              ⟨hcurrent, measurable_const, hcurrent⟩)
  | cons candidate rest =>
      have hcandidate := hremainingMeasurable candidate (by
        rw [hremaining]
        exact List.mem_cons_self)
      simpa [MeasureSubmissionMeasurable, monotoneBountySubmission, hremaining] using
        (show MeasurableModel state.current ∧ MeasurableGroup candidate.group ∧
            MeasurableModel candidate.replacement from
          ⟨hcurrent, hcandidate.1, hcandidate.2⟩)

/-! ## General-population potential and publication semantics -/

/-- Population loss plus `epsilon/2` per accepted update. -/
def measureMonotoneBountyPotential
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) (loss : BoundedLoss Y) (epsilon : ℝ)
    (state : MonotoneBountyState X Y) : ℝ :=
  measureModelLoss law loss state.current +
    (state.accepted : ℝ) * (epsilon / 2)

/-- The history-form protected-group guarantee under a general law. -/
def MeasureApproxGroupwiseMonotoneOnHistory
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) (loss : BoundedLoss Y) (epsilon : ℝ)
    (current : Model X Y) (groups : List (Group X))
    (pastModels : List (Model X Y)) : Prop :=
  ∀ group ∈ groups, ∀ past ∈ pastModels, 0 < measureGroupMass law group →
    measureGroupLoss law loss current group ≤
      measureGroupLoss law loss past group + epsilon / measureGroupMass law group

/-- All completed publications have the paper's history guarantee. -/
def MeasureMonotonePublicationsSound
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) (loss : BoundedLoss Y) (epsilon : ℝ)
    (state : MonotoneBountyState X Y) : Prop :=
  ∀ publication ∈ state.publicationsReverse,
    MeasureApproxGroupwiseMonotoneOnHistory law loss epsilon publication.output
      publication.protectedGroups publication.pastModels

/-- Rejections accumulated in the active scan are population-sound. -/
def MeasureMonotoneRejectedRepairsSound
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) (loss : BoundedLoss Y) (epsilon : ℝ)
    (state : MonotoneBountyState X Y) : Prop :=
  ∀ candidate ∈ state.rejectedRepairsReverse,
    measureCertificateImprovementScore law loss state.current candidate.group
      candidate.replacement ≤ epsilon

/-- One good global query cannot increase the general-population potential. -/
theorem measureMonotoneBountyActualStep_potential_le
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) {n : ℕ}
    (sample : Fin n → X × Y) (U : ℕ)
    (strategy : AdaptiveMonotoneProposalStrategy X Y)
    (hstrategy : ∀ transcript, MeasureProposalMeasurable (strategy transcript))
    (state : MonotoneBountyState X Y)
    (hstate : MeasureMonotoneBountyStateMeasurable state)
    (hchecker : MeasureCheckerDecisionGuaranteed law loss epsilon
      (monotoneBountySubmission U strategy state)
      (certificateCheckerDecision epsilon loss sample
        (monotoneBountySubmission U strategy state))) :
    measureMonotoneBountyPotential law loss epsilon
        (monotoneBountyStepFromDecision U strategy state
          (certificateCheckerDecision epsilon loss sample
            (monotoneBountySubmission U strategy state))) ≤
      measureMonotoneBountyPotential law loss epsilon state := by
  rcases hstate with ⟨hcurrent, hgroups, hmodels, hremainingMeasurable⟩
  cases hremaining : state.remainingRepairs with
  | nil =>
      by_cases hmore : state.externalProcessed < U
      · let proposal := strategy state.reverseTranscript.reverse
        have hproposal := hstrategy state.reverseTranscript.reverse
        cases hdecision : certificateCheckerDecision epsilon loss sample
            (monotoneBountySubmission U strategy state) with
        | rejected =>
            simp [measureMonotoneBountyPotential, monotoneBountyStepFromDecision,
              monotoneBountyStepCore, hremaining, hmore, hdecision]
        | accepted =>
            obtain ⟨mu, Delta, hcert, hlarge⟩ := hchecker.2 hdecision
            have hcert' : MeasureCertificateOfSuboptimality law loss state.current
                proposal.group proposal.replacement mu Delta := by
              simpa [monotoneBountySubmission, hremaining, hmore, proposal] using hcert
            have hprogress :=
              (theorem9_measure_listUpdate_progress (law := law) hloss hcurrent
                hproposal.2 hproposal.1 hcert').2
            have hdecrease : measureModelLoss law loss
                  (listUpdate state.current proposal.group proposal.replacement) ≤
                measureModelLoss law loss state.current - epsilon / 2 :=
              hprogress.trans (by linarith)
            simp only [monotoneBountyStepFromDecision, monotoneBountyStepCore,
              hremaining, if_pos hmore, hdecision, measureMonotoneBountyPotential,
              restartMonotoneRepairScan_current,
              restartMonotoneRepairScan_accepted]
            push_cast
            nlinarith
      · have hrejected := repairNoopSubmission_rejected epsilon hepsilon loss
          sample state.current
        have hdecision : certificateCheckerDecision epsilon loss sample
            (monotoneBountySubmission U strategy state) = .rejected := by
          simpa [monotoneBountySubmission, hremaining, hmore] using hrejected
        simp [measureMonotoneBountyPotential, monotoneBountyStepFromDecision,
          monotoneBountyStepCore, hremaining, hmore, hdecision]
  | cons candidate rest =>
      have hcandidate := hremainingMeasurable candidate (by simp [hremaining])
      cases hdecision : certificateCheckerDecision epsilon loss sample
          (monotoneBountySubmission U strategy state) with
      | rejected =>
          cases rest <;>
            simp [measureMonotoneBountyPotential, monotoneBountyStepFromDecision,
              monotoneBountyStepCore, hremaining, hdecision]
      | accepted =>
          obtain ⟨mu, Delta, hcert, hlarge⟩ := hchecker.2 hdecision
          have hcert' : MeasureCertificateOfSuboptimality law loss state.current
              candidate.group candidate.replacement mu Delta := by
            simpa [monotoneBountySubmission, hremaining] using hcert
          have hprogress :=
            (theorem9_measure_listUpdate_progress (law := law) hloss hcurrent
              hcandidate.2 hcandidate.1 hcert').2
          have hdecrease : measureModelLoss law loss
                (listUpdate state.current candidate.group candidate.replacement) ≤
              measureModelLoss law loss state.current - epsilon / 2 :=
            hprogress.trans (by linarith)
          simp only [monotoneBountyStepFromDecision, monotoneBountyStepCore,
            hremaining, hdecision, measureMonotoneBountyPotential,
            restartMonotoneRepairScan_current,
            restartMonotoneRepairScan_accepted]
          push_cast
          nlinarith

/-- A sound checker rejection bounds the exact general-population score. -/
theorem measureImprovementScore_le_of_checker_rejected
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    (loss : BoundedLoss Y) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (submission : Submission X Y) (hgroup : MeasurableGroup submission.group)
    (hchecker : MeasureCheckerDecisionGuaranteed law loss epsilon submission .rejected) :
    measureCertificateImprovementScore law loss submission.current submission.group
        submission.replacement ≤ epsilon := by
  by_contra hnot
  have hlarge : epsilon < measureCertificateImprovementScore law loss
      submission.current submission.group submission.replacement := lt_of_not_ge hnot
  have hpositive : 0 < measureCertificateImprovementScore law loss
      submission.current submission.group submission.replacement := hepsilon.trans hlarge
  have hcert := measureCanonical_certificate_of_positive_score law hgroup hpositive
  have hproduct : epsilon ≤ measureGroupMass law submission.group *
      (measureGroupLoss law loss submission.current submission.group -
        measureGroupLoss law loss submission.replacement submission.group) := by
    simpa [measureCertificateImprovementScore] using hlarge.le
  exact (hchecker.1 rfl _ _ hproduct) hcert

/-- Closure of the complete repair grid implies the displayed history form. -/
theorem measureScores_le_imply_groupwiseMonotoneOnHistory
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) (loss : BoundedLoss Y) (epsilon : ℝ)
    (current : Model X Y) (groups : List (Group X))
    (pastModels : List (Model X Y))
    (hscores : ∀ candidate ∈ repairCandidates groups pastModels,
      measureCertificateImprovementScore law loss current candidate.group
        candidate.replacement ≤ epsilon) :
    MeasureApproxGroupwiseMonotoneOnHistory law loss epsilon current groups
      pastModels := by
  intro group hgroup past hpast hmass
  have hscore := hscores { group := group, replacement := past }
    (by simp [repairCandidates, hgroup, hpast])
  exact (measureApproxBayesOptimal_pair_iff_source law loss epsilon current past group
    hmass).1 hscore

/-- Publishing one newly certified model preserves all publication guarantees. -/
theorem publishMonotoneBountyState_preserves_measurePublicationsSound
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) (loss : BoundedLoss Y) (epsilon : ℝ)
    (state : MonotoneBountyState X Y)
    (hprevious : MeasureMonotonePublicationsSound law loss epsilon state)
    (hcurrent : MeasureApproxGroupwiseMonotoneOnHistory law loss epsilon state.current
      state.protectedGroups state.publicModels) :
    MeasureMonotonePublicationsSound law loss epsilon
      (publishMonotoneBountyState state) := by
  intro publication hpublication
  simp only [publishMonotoneBountyState, List.mem_cons] at hpublication
  rcases hpublication with rfl | hpublication
  · exact hcurrent
  · exact hprevious publication hpublication

/-- Restarting a scan clears its rejected-prefix obligation. -/
theorem restartMonotoneRepairScan_measureRejectedSound
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) (loss : BoundedLoss Y) (epsilon : ℝ)
    (state : MonotoneBountyState X Y) :
    MeasureMonotoneRejectedRepairsSound law loss epsilon
      (restartMonotoneRepairScan state) := by
  cases hcandidates : repairCandidates state.protectedGroups state.publicModels <;>
    simp [restartMonotoneRepairScan, hcandidates, publishMonotoneBountyState,
      MeasureMonotoneRejectedRepairsSound]

/-- One actual query preserves soundness of the rejected repair prefix. -/
theorem measureMonotoneBountyActualStep_preserves_rejectedSound
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    (loss : BoundedLoss Y) (epsilon : ℝ) (hepsilon : 0 < epsilon) {n : ℕ}
    (sample : Fin n → X × Y) (U : ℕ)
    (strategy : AdaptiveMonotoneProposalStrategy X Y)
    (state : MonotoneBountyState X Y)
    (hstate : MeasureMonotoneBountyStateMeasurable state)
    (hstructural : MonotoneBountyStructuralInvariant U state)
    (hprevious : MeasureMonotoneRejectedRepairsSound law loss epsilon state)
    (hchecker : MeasureCheckerDecisionGuaranteed law loss epsilon
      (monotoneBountySubmission U strategy state)
      (certificateCheckerDecision epsilon loss sample
        (monotoneBountySubmission U strategy state))) :
    MeasureMonotoneRejectedRepairsSound law loss epsilon
      (monotoneBountyStepFromDecision U strategy state
        (certificateCheckerDecision epsilon loss sample
          (monotoneBountySubmission U strategy state))) := by
  rcases hstructural with ⟨_, _, _, _, _, hrejectedClosed, _⟩
  rcases hstate with ⟨hcurrent, hgroups, hmodels, hremainingMeasurable⟩
  cases hremaining : state.remainingRepairs with
  | nil =>
      have hrejected : state.rejectedRepairsReverse = [] := hrejectedClosed hremaining
      by_cases hmore : state.externalProcessed < U
      · cases hdecision : certificateCheckerDecision epsilon loss sample
            (monotoneBountySubmission U strategy state) with
        | rejected =>
            simp [MeasureMonotoneRejectedRepairsSound,
              monotoneBountyStepFromDecision, monotoneBountyStepCore,
              hremaining, hmore, hdecision, hrejected]
        | accepted =>
            simp only [monotoneBountyStepFromDecision, monotoneBountyStepCore,
              hremaining, if_pos hmore, hdecision]
            exact restartMonotoneRepairScan_measureRejectedSound law loss epsilon _
      · have hrejectedDecision := repairNoopSubmission_rejected epsilon hepsilon
          loss sample state.current
        have hdecision : certificateCheckerDecision epsilon loss sample
            (monotoneBountySubmission U strategy state) = .rejected := by
          simpa [monotoneBountySubmission, hremaining, hmore] using hrejectedDecision
        simpa [MeasureMonotoneRejectedRepairsSound,
          monotoneBountyStepFromDecision, monotoneBountyStepCore, hremaining,
          hmore, hdecision] using hprevious
  | cons candidate rest =>
      have hcandidate := hremainingMeasurable candidate (by simp [hremaining])
      cases hdecision : certificateCheckerDecision epsilon loss sample
          (monotoneBountySubmission U strategy state) with
      | accepted =>
          simp only [monotoneBountyStepFromDecision, monotoneBountyStepCore,
            hremaining, hdecision]
          exact restartMonotoneRepairScan_measureRejectedSound law loss epsilon _
      | rejected =>
          cases rest with
          | nil =>
              simp [MeasureMonotoneRejectedRepairsSound,
                monotoneBountyStepFromDecision, monotoneBountyStepCore,
                hremaining, hdecision, publishMonotoneBountyState]
          | cons next tail =>
              have hscore : measureCertificateImprovementScore law loss state.current
                  candidate.group candidate.replacement ≤ epsilon := by
                rw [hdecision] at hchecker
                refine measureImprovementScore_le_of_checker_rejected law loss epsilon
                  hepsilon
                  { current := state.current, group := candidate.group,
                    replacement := candidate.replacement } hcandidate.1 ?_
                simpa [monotoneBountySubmission, hremaining, hdecision] using hchecker
              simp only [MeasureMonotoneRejectedRepairsSound,
                monotoneBountyStepFromDecision, monotoneBountyStepCore,
                hremaining, hdecision, List.mem_cons]
              intro tested htested
              rcases htested with rfl | htested
              · exact hscore
              · exact hprevious tested htested

/-- One actual query preserves every completed publication guarantee. -/
theorem measureMonotoneBountyActualStep_preserves_publicationsSound
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    (loss : BoundedLoss Y) (epsilon : ℝ) (hepsilon : 0 < epsilon) {n : ℕ}
    (sample : Fin n → X × Y) (U : ℕ)
    (strategy : AdaptiveMonotoneProposalStrategy X Y)
    (state : MonotoneBountyState X Y)
    (hstate : MeasureMonotoneBountyStateMeasurable state)
    (hstructural : MonotoneBountyStructuralInvariant U state)
    (hpreviousPublications : MeasureMonotonePublicationsSound law loss epsilon state)
    (hpreviousRejected : MeasureMonotoneRejectedRepairsSound law loss epsilon state)
    (hchecker : MeasureCheckerDecisionGuaranteed law loss epsilon
      (monotoneBountySubmission U strategy state)
      (certificateCheckerDecision epsilon loss sample
        (monotoneBountySubmission U strategy state))) :
    MeasureMonotonePublicationsSound law loss epsilon
      (monotoneBountyStepFromDecision U strategy state
        (certificateCheckerDecision epsilon loss sample
          (monotoneBountySubmission U strategy state))) := by
  rcases hstructural with ⟨_, hpublic, _, _, hpublicActive, _, hpartition⟩
  rcases hstate with ⟨hcurrent, hgroupsMeasurable, hmodelsMeasurable,
    hremainingMeasurable⟩
  cases hremaining : state.remainingRepairs with
  | nil =>
      by_cases hmore : state.externalProcessed < U
      · cases hdecision : certificateCheckerDecision epsilon loss sample
            (monotoneBountySubmission U strategy state) with
        | rejected =>
            simpa [MeasureMonotonePublicationsSound,
              monotoneBountyStepFromDecision, monotoneBountyStepCore,
              hremaining, hmore, hdecision] using hpreviousPublications
        | accepted =>
            let proposal := strategy state.reverseTranscript.reverse
            have hcandidates : repairCandidates
                (proposal.group :: state.protectedGroups) state.publicModels ≠ [] :=
              repairCandidates_ne_nil_of_ne_nil (by simp) hpublic
            cases hcandEq : repairCandidates
                (proposal.group :: state.protectedGroups) state.publicModels with
            | nil => exact (hcandidates hcandEq).elim
            | cons candidate rest =>
                simpa [MeasureMonotonePublicationsSound,
                  monotoneBountyStepFromDecision, monotoneBountyStepCore,
                  hremaining, hmore, hdecision, proposal,
                  restartMonotoneRepairScan, hcandEq] using hpreviousPublications
      · have hrejectedDecision := repairNoopSubmission_rejected epsilon hepsilon
          loss sample state.current
        have hdecision : certificateCheckerDecision epsilon loss sample
            (monotoneBountySubmission U strategy state) = .rejected := by
          simpa [monotoneBountySubmission, hremaining, hmore] using hrejectedDecision
        simpa [MeasureMonotonePublicationsSound,
          monotoneBountyStepFromDecision, monotoneBountyStepCore,
          hremaining, hmore, hdecision] using hpreviousPublications
  | cons candidate rest =>
      have hcandidate := hremainingMeasurable candidate (by simp [hremaining])
      have hpublicGroups : state.publicModels.length ≤ state.protectedGroups.length :=
        hpublicActive (by simp [hremaining])
      have hgroups : state.protectedGroups ≠ [] := by
        intro hnil
        rw [hnil] at hpublicGroups
        simp at hpublicGroups
        exact hpublic hpublicGroups
      cases hdecision : certificateCheckerDecision epsilon loss sample
          (monotoneBountySubmission U strategy state) with
      | accepted =>
          have hcandidates : repairCandidates state.protectedGroups
              state.publicModels ≠ [] :=
            repairCandidates_ne_nil_of_ne_nil hgroups hpublic
          cases hcandEq : repairCandidates state.protectedGroups state.publicModels with
          | nil => exact (hcandidates hcandEq).elim
          | cons next tail =>
              simpa [MeasureMonotonePublicationsSound,
                monotoneBountyStepFromDecision, monotoneBountyStepCore,
                hremaining, hdecision, restartMonotoneRepairScan, hcandEq]
                using hpreviousPublications
      | rejected =>
          have hscore : measureCertificateImprovementScore law loss state.current
              candidate.group candidate.replacement ≤ epsilon := by
            rw [hdecision] at hchecker
            refine measureImprovementScore_le_of_checker_rejected law loss epsilon
              hepsilon
              { current := state.current, group := candidate.group,
                replacement := candidate.replacement } hcandidate.1 ?_
            simpa [monotoneBountySubmission, hremaining, hdecision] using hchecker
          cases rest with
          | cons next tail =>
              simpa [MeasureMonotonePublicationsSound,
                monotoneBountyStepFromDecision, monotoneBountyStepCore,
                hremaining, hdecision] using hpreviousPublications
          | nil =>
              have hpartitionState := hpartition (by simp [hremaining])
              rw [hremaining] at hpartitionState
              have hallScores : ∀ tested ∈ repairCandidates
                  state.protectedGroups state.publicModels,
                  measureCertificateImprovementScore law loss state.current tested.group
                    tested.replacement ≤ epsilon := by
                intro tested htested
                rw [← hpartitionState] at htested
                simp only [List.mem_append, List.mem_singleton] at htested
                rcases htested with htested | rfl
                · have htestedReverse : tested ∈ state.rejectedRepairsReverse := by
                    simpa using htested
                  exact hpreviousRejected tested htestedReverse
                · exact hscore
              have hcurrentSound := measureScores_le_imply_groupwiseMonotoneOnHistory
                law loss epsilon state.current state.protectedGroups
                state.publicModels hallScores
              let advanced : MonotoneBountyState X Y :=
                { state with
                  remainingRepairs := []
                  rejectedRepairsReverse := candidate :: state.rejectedRepairsReverse }
              have hpublish :=
                publishMonotoneBountyState_preserves_measurePublicationsSound
                  law loss epsilon advanced
                  (by simpa [advanced, MeasureMonotonePublicationsSound] using
                    hpreviousPublications)
                  (by simpa [advanced] using hcurrentSound)
              simpa [advanced, monotoneBountyStepFromDecision,
                monotoneBountyStepCore, hremaining, hdecision] using hpublish

/-! ## Whole-run guarantees -/

/-- General-population good-event predicate for the shared checker stream. -/
def MeasureMonotoneBountyRunGuaranteed
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) (loss : BoundedLoss Y) (epsilon : ℝ)
    {n : ℕ} (sample : Fin n → X × Y) (Q U : ℕ)
    (initial : Model X Y) (strategy : AdaptiveMonotoneProposalStrategy X Y) : Prop :=
  MeasureCheckerRunAuxGuaranteed law loss epsilon sample
    (monotoneBountySubmissionStrategy initial U strategy) Q []

/-- The global general-population potential is nonincreasing on the good event. -/
theorem measureMonotoneBountyRunAux_potential_le
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) {n : ℕ}
    (sample : Fin n → X × Y) (initial : Model X Y)
    (hinitial : MeasurableModel initial) (U : ℕ)
    (strategy : AdaptiveMonotoneProposalStrategy X Y)
    (hstrategy : ∀ transcript, MeasureProposalMeasurable (strategy transcript)) :
    ∀ (remaining : ℕ) (reverseTranscript : List CertificateDecision),
      MeasureCheckerRunAuxGuaranteed law loss epsilon sample
          (monotoneBountySubmissionStrategy initial U strategy)
          remaining reverseTranscript →
      let start := monotoneBountyStateFromTranscript initial U strategy
        reverseTranscript.reverse
      let finalTranscript := certificateCheckerRunAux epsilon loss sample
        (monotoneBountySubmissionStrategy initial U strategy)
        remaining reverseTranscript
      let final := monotoneBountyStateFromTranscript initial U strategy finalTranscript
      measureMonotoneBountyPotential law loss epsilon final ≤
        measureMonotoneBountyPotential law loss epsilon start := by
  intro remaining
  induction remaining with
  | zero => intro reverseTranscript _; simp [certificateCheckerRunAux]
  | succ remaining ih =>
      intro reverseTranscript hguaranteed
      by_cases hguard : (numberAccepted reverseTranscript : ℝ) ≤ 2 / epsilon
      · let publicTranscript := reverseTranscript.reverse
        let state := monotoneBountyStateFromTranscript initial U strategy publicTranscript
        let submission := monotoneBountySubmission U strategy state
        let decision := certificateCheckerDecision epsilon loss sample submission
        have hparts : MeasureCheckerDecisionGuaranteed law loss epsilon
              submission decision ∧
            MeasureCheckerRunAuxGuaranteed law loss epsilon sample
              (monotoneBountySubmissionStrategy initial U strategy)
              remaining (decision :: reverseTranscript) := by
          simpa [MeasureCheckerRunAuxGuaranteed, hguard,
            monotoneBountySubmissionStrategy, publicTranscript, state,
            submission, decision] using hguaranteed
        have hstate := monotoneBountyStateFromTranscript_measurable hinitial U strategy
          hstrategy publicTranscript
        have hstep := measureMonotoneBountyActualStep_potential_le law hloss epsilon
          hepsilon sample U strategy hstrategy state hstate
            (by simpa [submission, decision] using hparts.1)
        have hnextState :
            monotoneBountyStateFromTranscript initial U strategy
                (decision :: reverseTranscript).reverse =
              monotoneBountyStepFromDecision U strategy state decision := by
          simp only [List.reverse_cons]
          simpa [state, publicTranscript] using
            monotoneBountyStateFromTranscript_append_singleton initial U strategy
              publicTranscript decision
        have htail := ih (decision :: reverseTranscript) hparts.2
        have hstep' : measureMonotoneBountyPotential law loss epsilon
              (monotoneBountyStateFromTranscript initial U strategy
                (decision :: reverseTranscript).reverse) ≤
            measureMonotoneBountyPotential law loss epsilon
              (monotoneBountyStateFromTranscript initial U strategy
                reverseTranscript.reverse) := by
          rw [hnextState]
          simpa [state, publicTranscript] using hstep
        simp only [certificateCheckerRunAux, hguard, if_pos]
        exact htail.trans hstep'
      · simp [certificateCheckerRunAux, hguard]

/-- The general-population loss budget implies the rounded acceptance budget. -/
theorem measureMonotoneBountyState_accepted_le_budget
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (initial : Model X Y)
    (hinitial : MeasurableModel initial) (state : MonotoneBountyState X Y)
    (hstate : MeasurableModel state.current)
    (hpotential : measureMonotoneBountyPotential law loss epsilon state ≤
      measureModelLoss law loss initial) :
    state.accepted ≤ checkerAcceptanceBudget epsilon := by
  have hstateNonneg := measureModelLoss_nonneg law hloss hstate
  have hinitialOne := measureModelLoss_le_one law hloss hinitial
  have hmul : (state.accepted : ℝ) * epsilon ≤ 2 := by
    unfold measureMonotoneBountyPotential at hpotential
    nlinarith
  have hreal : (state.accepted : ℝ) ≤ 2 / epsilon :=
    (le_div_iff₀ hepsilon).2 hmul
  unfold checkerAcceptanceBudget
  exact Nat.le_floor hreal

/-- The loss budget keeps the source guard open throughout the declared
shared-checker horizon. -/
theorem measureMonotoneBountyRunAux_length_eq
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) {n : ℕ}
    (sample : Fin n → X × Y) (initial : Model X Y)
    (hinitial : MeasurableModel initial) (U : ℕ)
    (strategy : AdaptiveMonotoneProposalStrategy X Y)
    (hstrategy : ∀ transcript, MeasureProposalMeasurable (strategy transcript)) :
    ∀ (remaining : ℕ) (reverseTranscript : List CertificateDecision),
      MeasureCheckerRunAuxGuaranteed law loss epsilon sample
          (monotoneBountySubmissionStrategy initial U strategy)
          remaining reverseTranscript →
      measureMonotoneBountyPotential law loss epsilon
          (monotoneBountyStateFromTranscript initial U strategy
            reverseTranscript.reverse) ≤ measureModelLoss law loss initial →
      (certificateCheckerRunAux epsilon loss sample
          (monotoneBountySubmissionStrategy initial U strategy)
          remaining reverseTranscript).length =
        reverseTranscript.length + remaining := by
  intro remaining
  induction remaining with
  | zero => intro reverseTranscript _ _; simp [certificateCheckerRunAux]
  | succ remaining ih =>
      intro reverseTranscript hguaranteed hpotential
      let publicTranscript := reverseTranscript.reverse
      let state := monotoneBountyStateFromTranscript initial U strategy publicTranscript
      have hstateAccepted : state.accepted = numberAccepted reverseTranscript := by
        dsimp [state, publicTranscript]
        rw [monotoneBountyStateFromTranscript_accepted, numberAccepted_reverse]
      have hstate := monotoneBountyStateFromTranscript_measurable hinitial U strategy
        hstrategy publicTranscript
      have hstateNonneg : 0 ≤ measureModelLoss law loss state.current :=
        measureModelLoss_nonneg law hloss hstate.1
      have hinitialOne : measureModelLoss law loss initial ≤ 1 :=
        measureModelLoss_le_one law hloss hinitial
      have hacceptedMul : (state.accepted : ℝ) * epsilon ≤ 2 := by
        unfold measureMonotoneBountyPotential at hpotential
        nlinarith
      have hguard : (numberAccepted reverseTranscript : ℝ) ≤ 2 / epsilon := by
        apply (le_div_iff₀ hepsilon).2
        simpa [hstateAccepted] using hacceptedMul
      let submission := monotoneBountySubmission U strategy state
      let decision := certificateCheckerDecision epsilon loss sample submission
      have hparts : MeasureCheckerDecisionGuaranteed law loss epsilon submission
            decision ∧
          MeasureCheckerRunAuxGuaranteed law loss epsilon sample
            (monotoneBountySubmissionStrategy initial U strategy)
            remaining (decision :: reverseTranscript) := by
        simpa [MeasureCheckerRunAuxGuaranteed, hguard,
          monotoneBountySubmissionStrategy, publicTranscript, state,
          submission, decision] using hguaranteed
      have hstep := measureMonotoneBountyActualStep_potential_le law hloss epsilon
        hepsilon sample U strategy hstrategy state hstate
          (by simpa [submission, decision] using hparts.1)
      have hnextState :
          monotoneBountyStateFromTranscript initial U strategy
              (decision :: reverseTranscript).reverse =
            monotoneBountyStepFromDecision U strategy state decision := by
        simp only [List.reverse_cons]
        simpa [state, publicTranscript] using
          monotoneBountyStateFromTranscript_append_singleton initial U strategy
            publicTranscript decision
      have hnextPotential : measureMonotoneBountyPotential law loss epsilon
            (monotoneBountyStateFromTranscript initial U strategy
              (decision :: reverseTranscript).reverse) ≤
          measureModelLoss law loss initial := by
        rw [hnextState]
        exact hstep.trans (by simpa [state, publicTranscript] using hpotential)
      have htail := ih (decision :: reverseTranscript) hparts.2 hnextPotential
      simp only [certificateCheckerRunAux, hguard, if_pos]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

/-- Publication and active-rejection soundness propagate together. -/
theorem measureMonotoneBountyRunAux_preserves_soundness
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    (loss : BoundedLoss Y) (epsilon : ℝ) (hepsilon : 0 < epsilon) {n : ℕ}
    (sample : Fin n → X × Y) (initial : Model X Y)
    (hinitial : MeasurableModel initial) (U : ℕ)
    (strategy : AdaptiveMonotoneProposalStrategy X Y)
    (hstrategy : ∀ transcript, MeasureProposalMeasurable (strategy transcript)) :
    ∀ (remaining : ℕ) (reverseTranscript : List CertificateDecision),
      MeasureCheckerRunAuxGuaranteed law loss epsilon sample
          (monotoneBountySubmissionStrategy initial U strategy)
          remaining reverseTranscript →
      MeasureMonotonePublicationsSound law loss epsilon
        (monotoneBountyStateFromTranscript initial U strategy
          reverseTranscript.reverse) →
      MeasureMonotoneRejectedRepairsSound law loss epsilon
        (monotoneBountyStateFromTranscript initial U strategy
          reverseTranscript.reverse) →
      let finalTranscript := certificateCheckerRunAux epsilon loss sample
        (monotoneBountySubmissionStrategy initial U strategy)
        remaining reverseTranscript
      let final := monotoneBountyStateFromTranscript initial U strategy finalTranscript
      MeasureMonotonePublicationsSound law loss epsilon final ∧
        MeasureMonotoneRejectedRepairsSound law loss epsilon final := by
  intro remaining
  induction remaining with
  | zero =>
      intro reverseTranscript _ hpublic hrejected
      simpa [certificateCheckerRunAux] using And.intro hpublic hrejected
  | succ remaining ih =>
      intro reverseTranscript hguaranteed hpublic hrejected
      by_cases hguard : (numberAccepted reverseTranscript : ℝ) ≤ 2 / epsilon
      · let publicTranscript := reverseTranscript.reverse
        let state := monotoneBountyStateFromTranscript initial U strategy publicTranscript
        let submission := monotoneBountySubmission U strategy state
        let decision := certificateCheckerDecision epsilon loss sample submission
        have hparts : MeasureCheckerDecisionGuaranteed law loss epsilon submission
              decision ∧
            MeasureCheckerRunAuxGuaranteed law loss epsilon sample
              (monotoneBountySubmissionStrategy initial U strategy)
              remaining (decision :: reverseTranscript) := by
          simpa [MeasureCheckerRunAuxGuaranteed, hguard,
            monotoneBountySubmissionStrategy, publicTranscript, state,
            submission, decision] using hguaranteed
        have hstructural : MonotoneBountyStructuralInvariant U state := by
          simpa [state, publicTranscript] using
            monotoneBountyReplayAux_structural initial U strategy publicTranscript
        have hstateMeasurable := monotoneBountyStateFromTranscript_measurable
          hinitial U strategy hstrategy publicTranscript
        have hpublicState : MeasureMonotonePublicationsSound law loss epsilon state := by
          simpa [state, publicTranscript] using hpublic
        have hrejectedState : MeasureMonotoneRejectedRepairsSound law loss epsilon state := by
          simpa [state, publicTranscript] using hrejected
        have hpublicNext :=
          measureMonotoneBountyActualStep_preserves_publicationsSound law loss epsilon
            hepsilon sample U strategy state hstateMeasurable hstructural
            hpublicState hrejectedState
            (by simpa [submission, decision] using hparts.1)
        have hrejectedNext :=
          measureMonotoneBountyActualStep_preserves_rejectedSound law loss epsilon
            hepsilon sample U strategy state hstateMeasurable hstructural
            hrejectedState (by simpa [submission, decision] using hparts.1)
        have hnextState :
            monotoneBountyStateFromTranscript initial U strategy
                (decision :: reverseTranscript).reverse =
              monotoneBountyStepFromDecision U strategy state decision := by
          simp only [List.reverse_cons]
          simpa [state, publicTranscript] using
            monotoneBountyStateFromTranscript_append_singleton initial U strategy
              publicTranscript decision
        have htail := ih (decision :: reverseTranscript) hparts.2
          (by rw [hnextState]; exact hpublicNext)
          (by rw [hnextState]; exact hrejectedNext)
        simp only [certificateCheckerRunAux, hguard, if_pos]
        exact htail
      · simpa [certificateCheckerRunAux, hguard] using
          And.intro hpublic hrejected

/-- A metric-sized good horizon completes all external submissions and the
last restart-until-closed repair scan. -/
theorem measureMonotoneBountyRunAux_completes
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) {n : ℕ}
    (sample : Fin n → X × Y) (initial : Model X Y)
    (hinitial : MeasurableModel initial) (U : ℕ)
    (strategy : AdaptiveMonotoneProposalStrategy X Y)
    (hstrategy : ∀ transcript, MeasureProposalMeasurable (strategy transcript)) :
    ∀ (remaining : ℕ) (reverseTranscript : List CertificateDecision),
      MeasureCheckerRunAuxGuaranteed law loss epsilon sample
          (monotoneBountySubmissionStrategy initial U strategy)
          remaining reverseTranscript →
      measureMonotoneBountyPotential law loss epsilon
          (monotoneBountyStateFromTranscript initial U strategy
            reverseTranscript.reverse) ≤ measureModelLoss law loss initial →
      monotoneBountyMetric U (checkerAcceptanceBudget epsilon)
          (monotoneBountyStateFromTranscript initial U strategy
            reverseTranscript.reverse) ≤ remaining →
      MonotoneBountyComplete U
        (monotoneBountyStateFromTranscript initial U strategy
          (certificateCheckerRunAux epsilon loss sample
            (monotoneBountySubmissionStrategy initial U strategy)
            remaining reverseTranscript)) := by
  intro remaining
  induction remaining with
  | zero =>
      intro reverseTranscript _ _ hmetric
      let state := monotoneBountyStateFromTranscript initial U strategy
        reverseTranscript.reverse
      by_cases hcomplete : MonotoneBountyComplete U state
      · simpa [certificateCheckerRunAux, state] using hcomplete
      · have hstructural : MonotoneBountyStructuralInvariant U state := by
          simpa [state] using
            monotoneBountyReplayAux_structural initial U strategy
              reverseTranscript.reverse
        rcases hstructural with ⟨hexternal, _, _, _, _, _, _⟩
        have hpositive : 0 < monotoneBountyMetric U
            (checkerAcceptanceBudget epsilon) state := by
          cases hremaining : state.remainingRepairs with
          | nil =>
              have hmore : state.externalProcessed < U := by
                by_contra hnot
                have heq : state.externalProcessed = U := by omega
                exact hcomplete ⟨heq, hremaining⟩
              unfold monotoneBountyMetric
              omega
          | cons candidate rest =>
              unfold monotoneBountyMetric
              simp [hremaining]
        have hzero : monotoneBountyMetric U
            (checkerAcceptanceBudget epsilon) state ≤ 0 := by
          simpa [state] using hmetric
        omega
  | succ remaining ih =>
      intro reverseTranscript hguaranteed hpotential hmetric
      let publicTranscript := reverseTranscript.reverse
      let state := monotoneBountyStateFromTranscript initial U strategy publicTranscript
      have hstructural : MonotoneBountyStructuralInvariant U state := by
        simpa [state, publicTranscript] using
          monotoneBountyReplayAux_structural initial U strategy publicTranscript
      by_cases hcomplete : MonotoneBountyComplete U state
      · exact monotoneBountyRunAux_preserves_complete epsilon hepsilon loss
          sample initial U strategy (remaining + 1) reverseTranscript
          (by simpa [state, publicTranscript] using hcomplete)
      · have hstateAccepted : state.accepted = numberAccepted reverseTranscript := by
          dsimp [state, publicTranscript]
          rw [monotoneBountyStateFromTranscript_accepted, numberAccepted_reverse]
        have hstateMeasurable := monotoneBountyStateFromTranscript_measurable
          hinitial U strategy hstrategy publicTranscript
        have hstateNonneg : 0 ≤ measureModelLoss law loss state.current :=
          measureModelLoss_nonneg law hloss hstateMeasurable.1
        have hinitialOne : measureModelLoss law loss initial ≤ 1 :=
          measureModelLoss_le_one law hloss hinitial
        have hacceptedMul : (state.accepted : ℝ) * epsilon ≤ 2 := by
          have hp : measureMonotoneBountyPotential law loss epsilon state ≤
              measureModelLoss law loss initial := by
            simpa [state, publicTranscript] using hpotential
          unfold measureMonotoneBountyPotential at hp
          nlinarith
        have hguard : (numberAccepted reverseTranscript : ℝ) ≤ 2 / epsilon := by
          apply (le_div_iff₀ hepsilon).2
          simpa [hstateAccepted] using hacceptedMul
        let submission := monotoneBountySubmission U strategy state
        let decision := certificateCheckerDecision epsilon loss sample submission
        have hparts : MeasureCheckerDecisionGuaranteed law loss epsilon submission
              decision ∧
            MeasureCheckerRunAuxGuaranteed law loss epsilon sample
              (monotoneBountySubmissionStrategy initial U strategy)
              remaining (decision :: reverseTranscript) := by
          simpa [MeasureCheckerRunAuxGuaranteed, hguard,
            monotoneBountySubmissionStrategy, publicTranscript, state,
            submission, decision] using hguaranteed
        have hstep := measureMonotoneBountyActualStep_potential_le law hloss epsilon
          hepsilon sample U strategy hstrategy state hstateMeasurable
            (by simpa [submission, decision] using hparts.1)
        have hnextState :
            monotoneBountyStateFromTranscript initial U strategy
                (decision :: reverseTranscript).reverse =
              monotoneBountyStepFromDecision U strategy state decision := by
          simp only [List.reverse_cons]
          simpa [state, publicTranscript] using
            monotoneBountyStateFromTranscript_append_singleton initial U strategy
              publicTranscript decision
        have hnextPotential : measureMonotoneBountyPotential law loss epsilon
              (monotoneBountyStateFromTranscript initial U strategy
                (decision :: reverseTranscript).reverse) ≤
            measureModelLoss law loss initial := by
          rw [hnextState]
          exact hstep.trans (by simpa [state, publicTranscript] using hpotential)
        have hnextMeasurable := monotoneBountyStepFromDecision_measurable U strategy
          hstrategy state hstateMeasurable decision
        have hnextCap :
            (monotoneBountyStepFromDecision U strategy state decision).accepted ≤
              checkerAcceptanceBudget epsilon :=
          measureMonotoneBountyState_accepted_le_budget law hloss epsilon hepsilon
            initial hinitial _ hnextMeasurable.1
              (by rw [← hnextState]; exact hnextPotential)
        have hmetricStrict := monotoneBountyStep_metric_lt U
          (checkerAcceptanceBudget epsilon) strategy state decision hstructural
          hcomplete hnextCap
        have hmetricState : monotoneBountyMetric U
            (checkerAcceptanceBudget epsilon) state ≤ remaining + 1 := by
          simpa [state, publicTranscript] using hmetric
        have hnextMetric : monotoneBountyMetric U
              (checkerAcceptanceBudget epsilon)
              (monotoneBountyStateFromTranscript initial U strategy
                (decision :: reverseTranscript).reverse) ≤ remaining := by
          rw [hnextState]
          omega
        simp only [certificateCheckerRunAux, hguard, if_pos]
        exact ih (decision :: reverseTranscript) hparts.2 hnextPotential hnextMetric

/-- The exact rounded cubic horizon completes corrected Algorithm 4. -/
theorem measureMonotoneBountyOutput_complete
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) {n : ℕ}
    (sample : Fin n → X × Y) (U : ℕ) (initial : Model X Y)
    (hinitial : MeasurableModel initial)
    (strategy : AdaptiveMonotoneProposalStrategy X Y)
    (hstrategy : ∀ transcript, MeasureProposalMeasurable (strategy transcript))
    (hguaranteed : MeasureMonotoneBountyRunGuaranteed law loss epsilon sample
      (monotoneBountyQueryBudget epsilon U) U initial strategy) :
    MonotoneBountyComplete U
      (monotoneBountyOutput epsilon loss sample U initial strategy) := by
  have hpotential : measureMonotoneBountyPotential law loss epsilon
      (monotoneBountyStateFromTranscript initial U strategy [].reverse) ≤
        measureModelLoss law loss initial := by
    simp [measureMonotoneBountyPotential, monotoneBountyStateFromTranscript,
      monotoneBountyReplayAux, initialMonotoneBountyState]
  have hmetric : monotoneBountyMetric U (checkerAcceptanceBudget epsilon)
      (monotoneBountyStateFromTranscript initial U strategy [].reverse) ≤
        monotoneBountyQueryBudget epsilon U := by
    simp [monotoneBountyStateFromTranscript, monotoneBountyReplayAux,
      monotoneBountyQueryBudget, initialMonotoneBountyState_metric]
  have hcomplete := measureMonotoneBountyRunAux_completes law hloss epsilon hepsilon
    sample initial hinitial U strategy hstrategy
      (monotoneBountyQueryBudget epsilon U) [] hguaranteed hpotential hmetric
  simpa [monotoneBountyOutput, monotoneBountyTranscript,
    certificateCheckerRun] using hcomplete

/-- A good run uses the full declared horizon; post-completion slots are
deterministic rejected no-ops. -/
theorem measureMonotoneBountyTranscript_length
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) {n : ℕ}
    (sample : Fin n → X × Y) (U : ℕ) (initial : Model X Y)
    (hinitial : MeasurableModel initial)
    (strategy : AdaptiveMonotoneProposalStrategy X Y)
    (hstrategy : ∀ transcript, MeasureProposalMeasurable (strategy transcript))
    (hguaranteed : MeasureMonotoneBountyRunGuaranteed law loss epsilon sample
      (monotoneBountyQueryBudget epsilon U) U initial strategy) :
    (monotoneBountyTranscript epsilon loss sample U initial strategy).length =
      monotoneBountyQueryBudget epsilon U := by
  have hpotential : measureMonotoneBountyPotential law loss epsilon
      (monotoneBountyStateFromTranscript initial U strategy [].reverse) ≤
        measureModelLoss law loss initial := by
    simp [measureMonotoneBountyPotential, monotoneBountyStateFromTranscript,
      monotoneBountyReplayAux, initialMonotoneBountyState]
  have hlength := measureMonotoneBountyRunAux_length_eq law hloss epsilon hepsilon
    sample initial hinitial U strategy hstrategy
      (monotoneBountyQueryBudget epsilon U) [] hguaranteed hpotential
  simpa [monotoneBountyTranscript, certificateCheckerRun] using hlength

/-- The final output retains the initial general-population potential bound. -/
theorem measureMonotoneBountyOutput_potential_le
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) {n : ℕ}
    (sample : Fin n → X × Y) (U : ℕ) (initial : Model X Y)
    (hinitial : MeasurableModel initial)
    (strategy : AdaptiveMonotoneProposalStrategy X Y)
    (hstrategy : ∀ transcript, MeasureProposalMeasurable (strategy transcript))
    (hguaranteed : MeasureMonotoneBountyRunGuaranteed law loss epsilon sample
      (monotoneBountyQueryBudget epsilon U) U initial strategy) :
    measureMonotoneBountyPotential law loss epsilon
        (monotoneBountyOutput epsilon loss sample U initial strategy) ≤
      measureModelLoss law loss initial := by
  have hpotential := measureMonotoneBountyRunAux_potential_le law hloss epsilon
    hepsilon sample initial hinitial U strategy hstrategy
      (monotoneBountyQueryBudget epsilon U) [] hguaranteed
  simpa [monotoneBountyOutput, monotoneBountyTranscript,
    certificateCheckerRun, measureMonotoneBountyPotential,
    monotoneBountyStateFromTranscript, monotoneBountyReplayAux,
    initialMonotoneBountyState] using hpotential

/-- The whole general-population process accepts at most
`floor (2 / epsilon)` external or repair updates. -/
theorem measureMonotoneBountyOutput_accepted_le_budget
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) {n : ℕ}
    (sample : Fin n → X × Y) (U : ℕ) (initial : Model X Y)
    (hinitial : MeasurableModel initial)
    (strategy : AdaptiveMonotoneProposalStrategy X Y)
    (hstrategy : ∀ transcript, MeasureProposalMeasurable (strategy transcript))
    (hguaranteed : MeasureMonotoneBountyRunGuaranteed law loss epsilon sample
      (monotoneBountyQueryBudget epsilon U) U initial strategy) :
    (monotoneBountyOutput epsilon loss sample U initial strategy).accepted ≤
      checkerAcceptanceBudget epsilon := by
  have houtputMeasurable : MeasurableModel
      (monotoneBountyOutput epsilon loss sample U initial strategy).current := by
    apply (monotoneBountyStateFromTranscript_measurable hinitial U strategy
      hstrategy _).1
  exact measureMonotoneBountyState_accepted_le_budget law hloss epsilon hepsilon
    initial hinitial _ houtputMeasurable
      (measureMonotoneBountyOutput_potential_le law hloss epsilon hepsilon sample U
        initial hinitial strategy hstrategy hguaranteed)

/-- Every model published by a good execution satisfies protected-group
history monotonicity under the arbitrary population law. -/
theorem measureMonotoneBountyOutput_publicationsSound
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    (loss : BoundedLoss Y) (epsilon : ℝ) (hepsilon : 0 < epsilon) {n : ℕ}
    (sample : Fin n → X × Y) (U : ℕ) (initial : Model X Y)
    (hinitial : MeasurableModel initial)
    (strategy : AdaptiveMonotoneProposalStrategy X Y)
    (hstrategy : ∀ transcript, MeasureProposalMeasurable (strategy transcript))
    (hguaranteed : MeasureMonotoneBountyRunGuaranteed law loss epsilon sample
      (monotoneBountyQueryBudget epsilon U) U initial strategy) :
    MeasureMonotonePublicationsSound law loss epsilon
      (monotoneBountyOutput epsilon loss sample U initial strategy) := by
  have hinitialPublic : MeasureMonotonePublicationsSound law loss epsilon
      (monotoneBountyStateFromTranscript initial U strategy [].reverse) := by
    simp [MeasureMonotonePublicationsSound, monotoneBountyStateFromTranscript,
      monotoneBountyReplayAux, initialMonotoneBountyState]
  have hinitialRejected : MeasureMonotoneRejectedRepairsSound law loss epsilon
      (monotoneBountyStateFromTranscript initial U strategy [].reverse) := by
    simp [MeasureMonotoneRejectedRepairsSound, monotoneBountyStateFromTranscript,
      monotoneBountyReplayAux, initialMonotoneBountyState]
  have hsound := measureMonotoneBountyRunAux_preserves_soundness law loss epsilon
    hepsilon sample initial hinitial U strategy hstrategy
      (monotoneBountyQueryBudget epsilon U) [] hguaranteed
      hinitialPublic hinitialRejected
  simpa [monotoneBountyOutput, monotoneBountyTranscript,
    certificateCheckerRun] using hsound.1

/-- Complete deterministic conclusion of corrected Algorithm 4 under the
paper's arbitrary-distribution semantics. -/
def MeasureMonotoneBountyConclusion
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) (loss : BoundedLoss Y) (epsilon : ℝ)
    {n : ℕ} (sample : Fin n → X × Y) (U : ℕ)
    (initial : Model X Y) (strategy : AdaptiveMonotoneProposalStrategy X Y) : Prop :=
  let Q := monotoneBountyQueryBudget epsilon U
  let transcript := monotoneBountyTranscript epsilon loss sample U initial strategy
  let output := monotoneBountyOutput epsilon loss sample U initial strategy
  MeasureMonotoneBountyRunGuaranteed law loss epsilon sample Q U initial strategy ∧
    transcript.length = Q ∧
    output.externalProcessed = U ∧
    output.remainingRepairs = [] ∧
    output.accepted ≤ checkerAcceptanceBudget epsilon ∧
    MeasureMonotonePublicationsSound law loss epsilon output

/-- The shared-checker good event implies the full general-population result. -/
theorem measureMonotoneBountyConclusion_of_runGuaranteed
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) {n : ℕ}
    (sample : Fin n → X × Y) (U : ℕ) (initial : Model X Y)
    (hinitial : MeasurableModel initial)
    (strategy : AdaptiveMonotoneProposalStrategy X Y)
    (hstrategy : ∀ transcript, MeasureProposalMeasurable (strategy transcript))
    (hguaranteed : MeasureMonotoneBountyRunGuaranteed law loss epsilon sample
      (monotoneBountyQueryBudget epsilon U) U initial strategy) :
    MeasureMonotoneBountyConclusion law loss epsilon sample U initial strategy := by
  have hcomplete := measureMonotoneBountyOutput_complete law hloss epsilon hepsilon
    sample U initial hinitial strategy hstrategy hguaranteed
  refine ⟨hguaranteed,
    measureMonotoneBountyTranscript_length law hloss epsilon hepsilon sample U
      initial hinitial strategy hstrategy hguaranteed,
    hcomplete.1, hcomplete.2,
    measureMonotoneBountyOutput_accepted_le_budget law hloss epsilon hepsilon sample U
      initial hinitial strategy hstrategy hguaranteed,
    measureMonotoneBountyOutput_publicationsSound law loss epsilon hepsilon sample U
      initial hinitial strategy hstrategy hguaranteed⟩

/-- Failure probability for the full general-population conclusion. -/
def measureMonotoneBountyFailure
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) (loss : BoundedLoss Y)
    (epsilon : ℝ) (n U : ℕ) (initial : Model X Y)
    (strategy : AdaptiveMonotoneProposalStrategy X Y) : ℝ :=
  (finiteIIDSampleLaw law n).real {sample |
    ¬ MeasureMonotoneBountyConclusion law loss epsilon sample U initial strategy}

/-- A bad whole-process execution is a bad induced Algorithm 2 execution. -/
theorem measureMonotoneBountyFailure_le_checkerFailure
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (n U : ℕ)
    (initial : Model X Y) (hinitial : MeasurableModel initial)
    (strategy : AdaptiveMonotoneProposalStrategy X Y)
    (hstrategy : ∀ transcript, MeasureProposalMeasurable (strategy transcript)) :
    measureMonotoneBountyFailure law loss epsilon n U initial strategy ≤
      measureCertificateCheckerRunGuaranteeFailure law loss epsilon n
        (monotoneBountyQueryBudget epsilon U)
        (monotoneBountySubmissionStrategy initial U strategy) := by
  letI : IsProbabilityMeasure (finiteIIDSampleLaw law n) := by
    dsimp [finiteIIDSampleLaw]
    infer_instance
  unfold measureMonotoneBountyFailure measureCertificateCheckerRunGuaranteeFailure
  refine measureReal_mono ?_ (measure_ne_top (finiteIIDSampleLaw law n) _)
  intro sample hbad hchecker
  exact hbad (measureMonotoneBountyConclusion_of_runGuaranteed law hloss epsilon
    hepsilon sample U initial hinitial strategy hstrategy hchecker)

/-- Corrected Theorem 14 for an arbitrary measurable population, with exact
rounded cubic query horizon and explicit sparse-transcript failure bound. -/
theorem theorem14_measure_monotoneBounty
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (n U : ℕ)
    (hcount : 0 < n) (initial : Model X Y) (hinitial : MeasurableModel initial)
    (strategy : AdaptiveMonotoneProposalStrategy X Y)
    (hstrategy : ∀ transcript, MeasureProposalMeasurable (strategy transcript)) :
    let Q := monotoneBountyQueryBudget epsilon U
    measureMonotoneBountyFailure law loss epsilon n U initial strategy ≤
      (Q * (Q + 1) ^ checkerAcceptanceBudget epsilon : ℕ) * 2 *
        Real.exp (-(n : ℝ) * epsilon ^ 2 / 32) := by
  let Q := monotoneBountyQueryBudget epsilon U
  calc
    measureMonotoneBountyFailure law loss epsilon n U initial strategy ≤
        measureCertificateCheckerRunGuaranteeFailure law loss epsilon n Q
          (monotoneBountySubmissionStrategy initial U strategy) :=
      measureMonotoneBountyFailure_le_checkerFailure law hloss epsilon hepsilon
        n U initial hinitial strategy hstrategy
    _ ≤ (Q * (Q + 1) ^ checkerAcceptanceBudget epsilon : ℕ) * 2 *
          Real.exp (-(n : ℝ) * epsilon ^ 2 / 32) :=
      theorem11_measure_adaptive_certificateCheckerRun law hloss epsilon hepsilon
        n Q hcount (monotoneBountySubmissionStrategy initial U strategy)
          (measureSubmissionMeasurable_monotoneBountySubmissionStrategy
            hinitial U strategy hstrategy)

end

end GHKR22BiasBounties

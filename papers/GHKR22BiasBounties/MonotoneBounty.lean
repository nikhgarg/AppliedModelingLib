import GHKR22BiasBounties.FalsifyAndUpdate

/-!
# Whole-process semantics for MonotoneFalsifyAndUpdate

The source Algorithm 4 is a whole bias-bounty process, not merely one repair
scan.  This file gives the corrected global state machine.  External proposals
and internally generated repairs share one instance of `CertificateChecker`.
After every accepted external proposal, every protected-group/past-public-model
pair is scanned against the new current model.  An accepted repair installs its
list update and restarts the scan; a fully rejected scan publishes the repaired
model.  Thus each published model is checked against every earlier published
model on every protected group.

The printed pseudocode uses the stale symbol `f_t` inside its repair scan and
does not say explicitly that an accepted repair restarts the scan.  The state
machine below makes both intended operations literal.
-/

namespace GHKR22BiasBounties

noncomputable section

open AppliedModelingLib Probability

/-- One public model emitted after a repair phase, together with the exact
group/history grid against which its closing scan was performed. -/
structure MonotonePublication (X Y : Type*) where
  output : Model X Y
  protectedGroups : List (Group X)
  pastModels : List (Model X Y)

/-- Global state of corrected Algorithm 4.  Lists are newest-first except for
`remainingRepairs`, which follows the scan order. -/
structure MonotoneBountyState (X Y : Type*) where
  current : Model X Y
  accepted : ℕ
  externalProcessed : ℕ
  protectedGroups : List (Group X)
  publicModels : List (Model X Y)
  remainingRepairs : List (ProposedUpdate X Y)
  rejectedRepairsReverse : List (ProposedUpdate X Y)
  publicationsReverse : List (MonotonePublication X Y)
  reverseTranscript : List CertificateDecision

/-- Initial state: the initial model is already public, but no proposal has
been processed and no group is protected. -/
def initialMonotoneBountyState {X Y : Type*}
    (initial : Model X Y) : MonotoneBountyState X Y :=
  { current := initial
    accepted := 0
    externalProcessed := 0
    protectedGroups := []
    publicModels := [initial]
    remainingRepairs := []
    rejectedRepairsReverse := []
    publicationsReverse := []
    reverseTranscript := [] }

/-- Publish a repair-closed current model and clear the scan bookkeeping. -/
def publishMonotoneBountyState {X Y : Type*}
    (state : MonotoneBountyState X Y) : MonotoneBountyState X Y :=
  let publication : MonotonePublication X Y :=
    { output := state.current
      protectedGroups := state.protectedGroups
      pastModels := state.publicModels }
  { state with
    publicModels := state.current :: state.publicModels
    remainingRepairs := []
    rejectedRepairsReverse := []
    publicationsReverse := publication :: state.publicationsReverse }

/-- Start (or restart) the complete repair grid.  The empty-grid branch is
total; on reachable accepted states it is ruled out by the nonempty public
history invariant. -/
def restartMonotoneRepairScan {X Y : Type*}
    (state : MonotoneBountyState X Y) : MonotoneBountyState X Y :=
  let candidates := repairCandidates state.protectedGroups state.publicModels
  match candidates with
  | [] => publishMonotoneBountyState state
  | _ :: _ =>
      { state with
        remainingRepairs := candidates
        rejectedRepairsReverse := [] }

@[simp] theorem publishMonotoneBountyState_accepted {X Y : Type*}
    (state : MonotoneBountyState X Y) :
    (publishMonotoneBountyState state).accepted = state.accepted := by
  rfl

@[simp] theorem publishMonotoneBountyState_current {X Y : Type*}
    (state : MonotoneBountyState X Y) :
    (publishMonotoneBountyState state).current = state.current := by
  rfl

@[simp] theorem publishMonotoneBountyState_externalProcessed {X Y : Type*}
    (state : MonotoneBountyState X Y) :
    (publishMonotoneBountyState state).externalProcessed =
      state.externalProcessed := by
  rfl

@[simp] theorem publishMonotoneBountyState_remainingRepairs {X Y : Type*}
    (state : MonotoneBountyState X Y) :
    (publishMonotoneBountyState state).remainingRepairs = [] := by
  rfl

@[simp] theorem restartMonotoneRepairScan_accepted {X Y : Type*}
    (state : MonotoneBountyState X Y) :
    (restartMonotoneRepairScan state).accepted = state.accepted := by
  cases h : repairCandidates state.protectedGroups state.publicModels <;>
    simp [restartMonotoneRepairScan, h]

@[simp] theorem restartMonotoneRepairScan_current {X Y : Type*}
    (state : MonotoneBountyState X Y) :
    (restartMonotoneRepairScan state).current = state.current := by
  cases h : repairCandidates state.protectedGroups state.publicModels <;>
    simp [restartMonotoneRepairScan, h]

@[simp] theorem restartMonotoneRepairScan_externalProcessed {X Y : Type*}
    (state : MonotoneBountyState X Y) :
    (restartMonotoneRepairScan state).externalProcessed =
      state.externalProcessed := by
  cases h : repairCandidates state.protectedGroups state.publicModels <;>
    simp [restartMonotoneRepairScan, h]

/-- An external submitter may adapt to the entire public checker transcript,
including the outcomes of internal repair queries. -/
abbrev AdaptiveMonotoneProposalStrategy (X Y : Type*) :=
  List CertificateDecision → ProposedUpdate X Y

/-- Submission selected by the global state machine: the next repair while a
scan is active, the next external proposal while fewer than `U` have been
processed, and a zero-score no-op after completion. -/
def monotoneBountySubmission {X Y : Type*}
    (U : ℕ) (strategy : AdaptiveMonotoneProposalStrategy X Y)
    (state : MonotoneBountyState X Y) : Submission X Y :=
  match state.remainingRepairs with
  | candidate :: _ =>
      { current := state.current
        group := candidate.group
        replacement := candidate.replacement }
  | [] =>
      if state.externalProcessed < U then
        let proposal := strategy state.reverseTranscript.reverse
        { current := state.current
          group := proposal.group
          replacement := proposal.replacement }
      else
        repairNoopSubmission state.current

/-- Core state transition before recording the latest checker decision. -/
def monotoneBountyStepCore {X Y : Type*}
    (U : ℕ) (strategy : AdaptiveMonotoneProposalStrategy X Y)
    (state : MonotoneBountyState X Y)
    (decision : CertificateDecision) : MonotoneBountyState X Y :=
  match state.remainingRepairs with
  | candidate :: rest =>
      match decision with
      | .rejected =>
          let advanced :=
            { state with
              remainingRepairs := rest
              rejectedRepairsReverse :=
                candidate :: state.rejectedRepairsReverse }
          match rest with
          | [] => publishMonotoneBountyState advanced
          | _ :: _ => advanced
      | .accepted =>
          restartMonotoneRepairScan
            { state with
              current := listUpdate state.current candidate.group
                candidate.replacement
              accepted := state.accepted + 1 }
  | [] =>
      if state.externalProcessed < U then
        let proposal := strategy state.reverseTranscript.reverse
        match decision with
        | .rejected =>
            { state with externalProcessed := state.externalProcessed + 1 }
        | .accepted =>
            restartMonotoneRepairScan
              { state with
                current := listUpdate state.current proposal.group
                  proposal.replacement
                accepted := state.accepted + 1
                externalProcessed := state.externalProcessed + 1
                protectedGroups := proposal.group :: state.protectedGroups }
      else
        match decision with
        | .rejected => state
        | .accepted => { state with accepted := state.accepted + 1 }

/-- One global transition, including public-transcript bookkeeping. -/
def monotoneBountyStepFromDecision {X Y : Type*}
    (U : ℕ) (strategy : AdaptiveMonotoneProposalStrategy X Y)
    (state : MonotoneBountyState X Y)
    (decision : CertificateDecision) : MonotoneBountyState X Y :=
  { monotoneBountyStepCore U strategy state decision with
    reverseTranscript := decision :: state.reverseTranscript }

/-- Replay a chronological checker transcript through corrected Algorithm 4. -/
def monotoneBountyReplayAux {X Y : Type*}
    (U : ℕ) (strategy : AdaptiveMonotoneProposalStrategy X Y) :
    MonotoneBountyState X Y → List CertificateDecision → MonotoneBountyState X Y
  | state, [] => state
  | state, decision :: rest =>
      monotoneBountyReplayAux U strategy
        (monotoneBountyStepFromDecision U strategy state decision) rest

/-- Global state reconstructed only from the initial model and public checker
transcript. -/
def monotoneBountyStateFromTranscript {X Y : Type*}
    (initial : Model X Y) (U : ℕ)
    (strategy : AdaptiveMonotoneProposalStrategy X Y)
    (transcript : List CertificateDecision) : MonotoneBountyState X Y :=
  monotoneBountyReplayAux U strategy (initialMonotoneBountyState initial) transcript

/-- The whole corrected algorithm is one transcript-adaptive Algorithm 2
strategy; external and repair queries therefore share one privacy/generalization
budget exactly as in the paper. -/
def monotoneBountySubmissionStrategy {X Y : Type*}
    (initial : Model X Y) (U : ℕ)
    (strategy : AdaptiveMonotoneProposalStrategy X Y) :
    AdaptiveSubmissionStrategy X Y :=
  fun transcript => monotoneBountySubmission U strategy
    (monotoneBountyStateFromTranscript initial U strategy transcript)

/-- Rounded exact query horizon corresponding to the source's
`U + 8 / epsilon^3`: at most `U` external queries and `K^3` repair queries,
where `K=floor(2/epsilon)`. -/
noncomputable def monotoneBountyQueryBudget (epsilon : ℝ) (U : ℕ) : ℕ :=
  U + checkerAcceptanceBudget epsilon ^ 3

/-- Literal shared-checker transcript of corrected Algorithm 4. -/
def monotoneBountyTranscript {X Y : Type*} {n : ℕ}
    (epsilon : ℝ) (loss : BoundedLoss Y) (sample : Fin n → X × Y)
    (U : ℕ) (initial : Model X Y)
    (strategy : AdaptiveMonotoneProposalStrategy X Y) :
    List CertificateDecision :=
  certificateCheckerRun epsilon loss sample
    (monotoneBountyQueryBudget epsilon U)
    (monotoneBountySubmissionStrategy initial U strategy)

/-- Replayed output of the whole corrected Algorithm 4 execution. -/
def monotoneBountyOutput {X Y : Type*} {n : ℕ}
    (epsilon : ℝ) (loss : BoundedLoss Y) (sample : Fin n → X × Y)
    (U : ℕ) (initial : Model X Y)
    (strategy : AdaptiveMonotoneProposalStrategy X Y) : MonotoneBountyState X Y :=
  monotoneBountyStateFromTranscript initial U strategy
    (monotoneBountyTranscript epsilon loss sample U initial strategy)

/-- Replay of consecutive transcript pieces is associative. -/
theorem monotoneBountyReplayAux_append {X Y : Type*}
    (U : ℕ) (strategy : AdaptiveMonotoneProposalStrategy X Y)
    (state : MonotoneBountyState X Y) (first second : List CertificateDecision) :
    monotoneBountyReplayAux U strategy state (first ++ second) =
      monotoneBountyReplayAux U strategy
        (monotoneBountyReplayAux U strategy state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons decision rest ih =>
      simp only [List.cons_append, monotoneBountyReplayAux]
      exact ih _

/-- Appending one public decision performs exactly one global transition. -/
theorem monotoneBountyStateFromTranscript_append_singleton {X Y : Type*}
    (initial : Model X Y) (U : ℕ)
    (strategy : AdaptiveMonotoneProposalStrategy X Y)
    (transcript : List CertificateDecision) (decision : CertificateDecision) :
    monotoneBountyStateFromTranscript initial U strategy
        (transcript ++ [decision]) =
      monotoneBountyStepFromDecision U strategy
        (monotoneBountyStateFromTranscript initial U strategy transcript) decision := by
  rw [monotoneBountyStateFromTranscript, monotoneBountyReplayAux_append]
  rfl

/-- A state's stored transcript is exactly the reverse of the transcript that
constructed it. -/
theorem monotoneBountyReplayAux_reverseTranscript {X Y : Type*}
    (U : ℕ) (strategy : AdaptiveMonotoneProposalStrategy X Y)
    (state : MonotoneBountyState X Y) (transcript : List CertificateDecision) :
    (monotoneBountyReplayAux U strategy state transcript).reverseTranscript =
      transcript.reverse ++ state.reverseTranscript := by
  induction transcript generalizing state with
  | nil => simp [monotoneBountyReplayAux]
  | cons decision rest ih =>
      simp only [monotoneBountyReplayAux]
      rw [ih]
      simp [monotoneBountyStepFromDecision, List.reverse_cons, List.append_assoc]

@[simp] theorem monotoneBountyStateFromTranscript_reverseTranscript
    {X Y : Type*} (initial : Model X Y) (U : ℕ)
    (strategy : AdaptiveMonotoneProposalStrategy X Y)
    (transcript : List CertificateDecision) :
    (monotoneBountyStateFromTranscript initial U strategy transcript).reverseTranscript =
      transcript.reverse := by
  simp [monotoneBountyStateFromTranscript,
    monotoneBountyReplayAux_reverseTranscript, initialMonotoneBountyState]

/-- Every accepted checker decision increments the global counter once, and a
rejection leaves it unchanged. -/
theorem monotoneBountyStepFromDecision_accepted {X Y : Type*}
    (U : ℕ) (strategy : AdaptiveMonotoneProposalStrategy X Y)
    (state : MonotoneBountyState X Y) (decision : CertificateDecision) :
    (monotoneBountyStepFromDecision U strategy state decision).accepted =
      state.accepted + if decision = .accepted then 1 else 0 := by
  cases hremaining : state.remainingRepairs with
  | nil =>
      by_cases hexternal : state.externalProcessed < U
      · cases decision <;>
          simp [monotoneBountyStepFromDecision, monotoneBountyStepCore,
            hremaining, hexternal]
      · cases decision <;>
          simp [monotoneBountyStepFromDecision, monotoneBountyStepCore,
            hremaining, hexternal]
  | cons candidate rest =>
      cases decision with
      | rejected =>
          cases rest <;>
            simp [monotoneBountyStepFromDecision, monotoneBountyStepCore,
              hremaining]
      | accepted =>
          simp [monotoneBountyStepFromDecision, monotoneBountyStepCore,
            hremaining]

/-- Operational accepted counter agrees exactly with the shared checker
transcript. -/
theorem monotoneBountyReplayAux_accepted {X Y : Type*}
    (U : ℕ) (strategy : AdaptiveMonotoneProposalStrategy X Y)
    (state : MonotoneBountyState X Y) (transcript : List CertificateDecision) :
    (monotoneBountyReplayAux U strategy state transcript).accepted =
      state.accepted + numberAccepted transcript := by
  induction transcript generalizing state with
  | nil => simp [monotoneBountyReplayAux, numberAccepted]
  | cons decision rest ih =>
      simp only [monotoneBountyReplayAux]
      rw [ih]
      rw [monotoneBountyStepFromDecision_accepted]
      cases decision <;>
        simp [numberAccepted, Nat.add_comm, Nat.add_left_comm]

@[simp] theorem monotoneBountyStateFromTranscript_accepted {X Y : Type*}
    (initial : Model X Y) (U : ℕ)
    (strategy : AdaptiveMonotoneProposalStrategy X Y)
    (transcript : List CertificateDecision) :
    (monotoneBountyStateFromTranscript initial U strategy transcript).accepted =
      numberAccepted transcript := by
  simp [monotoneBountyStateFromTranscript, monotoneBountyReplayAux_accepted,
    initialMonotoneBountyState]

/-- All published models satisfy the source's groupwise history guarantee. -/
def MonotonePublicationsSound {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y) (epsilon : ℝ)
    (state : MonotoneBountyState X Y) : Prop :=
  ∀ publication ∈ state.publicationsReverse,
    ApproxGroupwiseMonotoneOnHistory law loss epsilon publication.output
      publication.protectedGroups publication.pastModels

/-- Rejections accumulated in the current scan are population-sound for the
current model. -/
def MonotoneRejectedRepairsSound {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y) (epsilon : ℝ)
    (state : MonotoneBountyState X Y) : Prop :=
  ∀ candidate ∈ state.rejectedRepairsReverse,
    certificateImprovementScore law loss state.current candidate.group
      candidate.replacement ≤ epsilon

/-- While a repair phase is active, rejected and unscanned pieces partition
the exact protected-group/past-model grid. -/
def MonotoneRepairScanPartition {X Y : Type*}
    (state : MonotoneBountyState X Y) : Prop :=
  state.remainingRepairs ≠ [] →
    state.rejectedRepairsReverse.reverse ++ state.remainingRepairs =
      repairCandidates state.protectedGroups state.publicModels

/-- Structural invariants used by the global query-accounting proof. -/
def MonotoneBountyStructuralInvariant {X Y : Type*}
    (U : ℕ) (state : MonotoneBountyState X Y) : Prop :=
  state.externalProcessed ≤ U ∧
    state.publicModels ≠ [] ∧
    state.protectedGroups.length ≤ state.accepted ∧
    state.publicModels.length ≤ state.protectedGroups.length + 1 ∧
    (state.remainingRepairs ≠ [] →
      state.publicModels.length ≤ state.protectedGroups.length) ∧
    (state.remainingRepairs = [] → state.rejectedRepairsReverse = []) ∧
    MonotoneRepairScanPartition state

/-- The initial global state satisfies every structural invariant. -/
theorem initialMonotoneBountyState_structural {X Y : Type*}
    (initial : Model X Y) (U : ℕ) :
    MonotoneBountyStructuralInvariant U (initialMonotoneBountyState initial) := by
  simp [MonotoneBountyStructuralInvariant, MonotoneRepairScanPartition,
    initialMonotoneBountyState]

/-- A nonempty group list and nonempty public history produce a nonempty repair
grid. -/
theorem repairCandidates_ne_nil_of_ne_nil {X Y : Type*}
    {groups : List (Group X)} {pastModels : List (Model X Y)}
    (hgroups : groups ≠ []) (hpast : pastModels ≠ []) :
    repairCandidates groups pastModels ≠ [] := by
  cases groups with
  | nil => contradiction
  | cons group groups =>
      cases pastModels with
      | nil => contradiction
      | cons past pastModels => simp [repairCandidates]

/-- Restarting a nonempty repair grid establishes all structural invariants. -/
theorem restartMonotoneRepairScan_structural {X Y : Type*}
    (U : ℕ) (state : MonotoneBountyState X Y)
    (hexternal : state.externalProcessed ≤ U)
    (hpublic : state.publicModels ≠ [])
    (hgroups : state.protectedGroups ≠ [])
    (hgroupAccepted : state.protectedGroups.length ≤ state.accepted)
    (hpublicGroups : state.publicModels.length ≤ state.protectedGroups.length) :
    MonotoneBountyStructuralInvariant U (restartMonotoneRepairScan state) := by
  have hcandidates := repairCandidates_ne_nil_of_ne_nil hgroups hpublic
  cases hcandidateEq : repairCandidates state.protectedGroups state.publicModels with
  | nil => exact (hcandidates hcandidateEq).elim
  | cons candidate rest =>
      simp only [restartMonotoneRepairScan, hcandidateEq]
      refine ⟨hexternal, hpublic, hgroupAccepted, ?_, ?_, ?_, ?_⟩
      · change state.publicModels.length ≤ state.protectedGroups.length + 1
        omega
      · intro _
        exact hpublicGroups
      · simp
      · intro _
        simp [MonotoneRepairScanPartition, hcandidateEq]

/-- Publishing a completed scan preserves the structural invariants. -/
theorem publishMonotoneBountyState_structural {X Y : Type*}
    (U : ℕ) (state : MonotoneBountyState X Y)
    (hexternal : state.externalProcessed ≤ U)
    (hpublic : state.publicModels ≠ [])
    (hgroupAccepted : state.protectedGroups.length ≤ state.accepted)
    (hpublicGroups : state.publicModels.length ≤ state.protectedGroups.length) :
    MonotoneBountyStructuralInvariant U (publishMonotoneBountyState state) := by
  refine ⟨hexternal, ?_, hgroupAccepted, ?_, ?_, ?_, ?_⟩
  · simp [publishMonotoneBountyState]
  · simp only [publishMonotoneBountyState, List.length_cons]
    omega
  · simp [publishMonotoneBountyState]
  · simp [publishMonotoneBountyState]
  · simp [MonotoneRepairScanPartition, publishMonotoneBountyState]

/-- Every replay transition preserves the global structural invariants. -/
theorem monotoneBountyStep_preserves_structural {X Y : Type*}
    (U : ℕ) (strategy : AdaptiveMonotoneProposalStrategy X Y)
    (state : MonotoneBountyState X Y) (decision : CertificateDecision)
    (hinvariant : MonotoneBountyStructuralInvariant U state) :
    MonotoneBountyStructuralInvariant U
      (monotoneBountyStepFromDecision U strategy state decision) := by
  rcases hinvariant with
    ⟨hexternal, hpublic, hgroupAccepted, hpublicGroupSucc,
      hpublicGroupActive, hrejectedClosed, hpartition⟩
  cases hremaining : state.remainingRepairs with
  | nil =>
      have hrejected : state.rejectedRepairsReverse = [] :=
        hrejectedClosed hremaining
      by_cases hmore : state.externalProcessed < U
      · let proposal := strategy state.reverseTranscript.reverse
        cases decision with
        | rejected =>
            simp only [monotoneBountyStepFromDecision, monotoneBountyStepCore,
              hremaining, if_pos hmore]
            refine ⟨by
                change state.externalProcessed + 1 ≤ U
                omega,
              hpublic, hgroupAccepted, hpublicGroupSucc,
              ?_, ?_, ?_⟩
            · simp
            · simpa [hrejected]
            · simp [MonotoneRepairScanPartition]
        | accepted =>
            have hgroupsNew :
                proposal.group :: state.protectedGroups ≠ [] := by simp
            have hgroupAcceptedNew :
                (proposal.group :: state.protectedGroups).length ≤
                  state.accepted + 1 := by
              simp only [List.length_cons]
              omega
            have hpublicGroupsNew : state.publicModels.length ≤
                (proposal.group :: state.protectedGroups).length := by
              simpa only [List.length_cons] using hpublicGroupSucc
            have hrestart := restartMonotoneRepairScan_structural U
              { state with
                current := listUpdate state.current proposal.group proposal.replacement
                accepted := state.accepted + 1
                externalProcessed := state.externalProcessed + 1
                protectedGroups := proposal.group :: state.protectedGroups }
              (by simp only; omega) hpublic hgroupsNew hgroupAcceptedNew
              hpublicGroupsNew
            simp only [monotoneBountyStepFromDecision, monotoneBountyStepCore,
              hremaining, if_pos hmore]
            change MonotoneBountyStructuralInvariant U
              (restartMonotoneRepairScan
                { state with
                  current := listUpdate state.current proposal.group
                    proposal.replacement
                  accepted := state.accepted + 1
                  externalProcessed := state.externalProcessed + 1
                  protectedGroups := proposal.group :: state.protectedGroups })
            exact hrestart
      · cases decision with
        | rejected =>
            simp only [monotoneBountyStepFromDecision, monotoneBountyStepCore,
              hremaining, if_neg hmore]
            refine ⟨hexternal, hpublic, hgroupAccepted, hpublicGroupSucc,
              ?_, ?_, ?_⟩
            · simpa using hpublicGroupActive
            · simpa using hrejected
            · simpa [MonotoneRepairScanPartition] using hpartition
        | accepted =>
            simp only [monotoneBountyStepFromDecision, monotoneBountyStepCore,
              hremaining, if_neg hmore]
            refine ⟨hexternal, hpublic, ?_, hpublicGroupSucc,
              ?_, ?_, ?_⟩
            · change state.protectedGroups.length ≤ state.accepted + 1
              omega
            · simpa using hpublicGroupActive
            · simpa [hrejected]
            · simpa [MonotoneRepairScanPartition] using hpartition
  | cons candidate rest =>
      have hpublicGroups : state.publicModels.length ≤
          state.protectedGroups.length := hpublicGroupActive (by simp [hremaining])
      have hgroups : state.protectedGroups ≠ [] := by
        intro hnil
        rw [hnil] at hpublicGroups
        simp at hpublicGroups
        exact hpublic hpublicGroups
      cases decision with
      | accepted =>
          have hrestart := restartMonotoneRepairScan_structural U
            { state with
              current := listUpdate state.current candidate.group candidate.replacement
              accepted := state.accepted + 1 }
            hexternal hpublic hgroups (by simp only; omega) hpublicGroups
          simp only [monotoneBountyStepFromDecision, monotoneBountyStepCore,
            hremaining]
          change MonotoneBountyStructuralInvariant U
            (restartMonotoneRepairScan
              { state with
                current := listUpdate state.current candidate.group
                  candidate.replacement
                accepted := state.accepted + 1 })
          exact hrestart
      | rejected =>
          cases rest with
          | nil =>
              let advanced : MonotoneBountyState X Y :=
                { state with
                  remainingRepairs := []
                  rejectedRepairsReverse :=
                    candidate :: state.rejectedRepairsReverse }
              have hpublish := publishMonotoneBountyState_structural U advanced
                hexternal hpublic hgroupAccepted hpublicGroups
              simpa [advanced, monotoneBountyStepFromDecision,
                monotoneBountyStepCore, hremaining] using hpublish
          | cons next tail =>
              simp only [monotoneBountyStepFromDecision,
                monotoneBountyStepCore, hremaining]
              refine ⟨hexternal, hpublic, hgroupAccepted, hpublicGroupSucc,
                ?_, ?_, ?_⟩
              · intro _
                exact hpublicGroups
              · simp
              · intro _
                have hpartitionState := hpartition (by simp [hremaining])
                rw [hremaining] at hpartitionState
                change
                  (candidate :: state.rejectedRepairsReverse).reverse ++
                      next :: tail =
                    repairCandidates state.protectedGroups state.publicModels
                simpa [List.reverse_cons, List.append_assoc] using hpartitionState

/-- Structural invariants hold for every transcript, independently of checker
accuracy. -/
theorem monotoneBountyReplayAux_structural {X Y : Type*}
    (initial : Model X Y) (U : ℕ)
    (strategy : AdaptiveMonotoneProposalStrategy X Y) :
    ∀ (transcript : List CertificateDecision),
      MonotoneBountyStructuralInvariant U
        (monotoneBountyStateFromTranscript initial U strategy transcript) := by
  intro transcript
  induction transcript using List.reverseRecOn with
  | nil => exact initialMonotoneBountyState_structural initial U
  | append_singleton transcript decision ih =>
      rw [monotoneBountyStateFromTranscript_append_singleton]
      exact monotoneBountyStep_preserves_structural U strategy _ decision ih

/-- Population loss plus `epsilon/2` per accepted update is the global
Algorithm 4 potential. -/
def monotoneBountyPotential {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y) (epsilon : ℝ)
    (state : MonotoneBountyState X Y) : ℝ :=
  modelLoss law loss state.current + (state.accepted : ℝ) * (epsilon / 2)

/-- On the Algorithm 2 good event, one actual global query cannot increase
population loss plus the accepted-update charge. -/
theorem monotoneBountyActualStep_potential_le
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) {n : ℕ}
    (sample : Fin n → X × Y) (U : ℕ)
    (strategy : AdaptiveMonotoneProposalStrategy X Y)
    (state : MonotoneBountyState X Y)
    (hchecker : CheckerDecisionGuaranteed law loss epsilon
      (monotoneBountySubmission U strategy state)
      (certificateCheckerDecision epsilon loss sample
        (monotoneBountySubmission U strategy state))) :
    monotoneBountyPotential law loss epsilon
        (monotoneBountyStepFromDecision U strategy state
          (certificateCheckerDecision epsilon loss sample
            (monotoneBountySubmission U strategy state))) ≤
      monotoneBountyPotential law loss epsilon state := by
  cases hremaining : state.remainingRepairs with
  | nil =>
      by_cases hmore : state.externalProcessed < U
      · let proposal := strategy state.reverseTranscript.reverse
        cases hdecision : certificateCheckerDecision epsilon loss sample
            (monotoneBountySubmission U strategy state) with
        | rejected =>
            simp [monotoneBountyPotential, monotoneBountyStepFromDecision,
              monotoneBountyStepCore, hremaining, hmore, hdecision]
        | accepted =>
            obtain ⟨mu, Delta, hcert, hlarge⟩ := hchecker.2 hdecision
            have hcert' : CertificateOfSuboptimality law loss state.current
                proposal.group proposal.replacement mu Delta := by
              simpa [monotoneBountySubmission, hremaining, hmore, proposal]
                using hcert
            have hprogress := (theorem9_listUpdate_progress hcert').2
            have hloss : modelLoss law loss
                  (listUpdate state.current proposal.group proposal.replacement) ≤
                modelLoss law loss state.current - epsilon / 2 :=
              hprogress.trans (by linarith)
            simp only [monotoneBountyStepFromDecision, monotoneBountyStepCore,
              hremaining, if_pos hmore, hdecision, monotoneBountyPotential,
              restartMonotoneRepairScan_current,
              restartMonotoneRepairScan_accepted]
            push_cast
            nlinarith
      · have hrejected := repairNoopSubmission_rejected epsilon hepsilon loss
          sample state.current
        have hdecision : certificateCheckerDecision epsilon loss sample
            (monotoneBountySubmission U strategy state) = .rejected := by
          simpa [monotoneBountySubmission, hremaining, hmore] using hrejected
        simp [monotoneBountyPotential, monotoneBountyStepFromDecision,
          monotoneBountyStepCore, hremaining, hmore, hdecision]
  | cons candidate rest =>
      cases hdecision : certificateCheckerDecision epsilon loss sample
          (monotoneBountySubmission U strategy state) with
      | rejected =>
          cases rest <;>
            simp [monotoneBountyPotential, monotoneBountyStepFromDecision,
              monotoneBountyStepCore, hremaining, hdecision]
      | accepted =>
          obtain ⟨mu, Delta, hcert, hlarge⟩ := hchecker.2 hdecision
          have hcert' : CertificateOfSuboptimality law loss state.current
              candidate.group candidate.replacement mu Delta := by
            simpa [monotoneBountySubmission, hremaining] using hcert
          have hprogress := (theorem9_listUpdate_progress hcert').2
          have hloss : modelLoss law loss
                (listUpdate state.current candidate.group candidate.replacement) ≤
              modelLoss law loss state.current - epsilon / 2 :=
            hprogress.trans (by linarith)
          simp only [monotoneBountyStepFromDecision, monotoneBountyStepCore,
            hremaining, hdecision, monotoneBountyPotential,
            restartMonotoneRepairScan_current,
            restartMonotoneRepairScan_accepted]
          push_cast
          nlinarith

/-- A checker rejection on the good event bounds the exact population
improvement score by `epsilon`. -/
theorem improvementScore_le_of_checker_rejected
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (submission : Submission X Y)
    (hchecker : CheckerDecisionGuaranteed law loss epsilon submission .rejected) :
    certificateImprovementScore law loss submission.current submission.group
        submission.replacement ≤ epsilon := by
  by_contra hnot
  have hlarge : epsilon < certificateImprovementScore law loss
      submission.current submission.group submission.replacement := lt_of_not_ge hnot
  have hpositive : 0 < certificateImprovementScore law loss
      submission.current submission.group submission.replacement :=
    hepsilon.trans hlarge
  have hcert := canonical_certificate_of_positive_score
    (law := law) (loss := loss) (f := submission.current)
    (g := submission.group) (h := submission.replacement) hpositive
  have hproduct : epsilon ≤ groupMass law submission.group *
      (groupLoss law loss submission.current submission.group -
        groupLoss law loss submission.replacement submission.group) := by
    simpa [certificateImprovementScore] using hlarge.le
  exact (hchecker.1 rfl _ _ hproduct) hcert

/-- Population-score closure of a complete repair grid implies the history
form of approximate groupwise monotonicity used in Theorem 14. -/
theorem scores_le_imply_groupwiseMonotoneOnHistory
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y) (epsilon : ℝ)
    (current : Model X Y) (groups : List (Group X))
    (pastModels : List (Model X Y))
    (hscores : ∀ candidate ∈ repairCandidates groups pastModels,
      certificateImprovementScore law loss current candidate.group
        candidate.replacement ≤ epsilon) :
    ApproxGroupwiseMonotoneOnHistory law loss epsilon current groups pastModels := by
  apply approxGroupwiseMonotone_repairCandidates_history
  intro candidate hcandidate hmass
  exact (approxBayesOptimal_pair_iff_source law loss epsilon current
    candidate.replacement candidate.group hmass).1 (hscores candidate hcandidate)

/-- Publishing a model whose closing grid is population-sound preserves the
soundness of every earlier publication and adds the new one. -/
theorem publishMonotoneBountyState_preserves_publicationsSound
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y) (epsilon : ℝ)
    (state : MonotoneBountyState X Y)
    (hprevious : MonotonePublicationsSound law loss epsilon state)
    (hcurrent : ApproxGroupwiseMonotoneOnHistory law loss epsilon state.current
      state.protectedGroups state.publicModels) :
    MonotonePublicationsSound law loss epsilon
      (publishMonotoneBountyState state) := by
  intro publication hpublication
  simp only [publishMonotoneBountyState, List.mem_cons] at hpublication
  rcases hpublication with rfl | hpublication
  · exact hcurrent
  · exact hprevious publication hpublication

/-- A restart always clears the current rejected-prefix bookkeeping, including
the totalized empty-grid branch. -/
theorem restartMonotoneRepairScan_rejectedSound
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y) (epsilon : ℝ)
    (state : MonotoneBountyState X Y) :
    MonotoneRejectedRepairsSound law loss epsilon
      (restartMonotoneRepairScan state) := by
  cases hcandidates : repairCandidates state.protectedGroups state.publicModels <;>
    simp [restartMonotoneRepairScan, hcandidates,
      publishMonotoneBountyState, MonotoneRejectedRepairsSound]

/-- One actual global query preserves the soundness of the rejected prefix of
the active repair scan.  Acceptance restarts with an empty rejected prefix. -/
theorem monotoneBountyActualStep_preserves_rejectedSound
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) {n : ℕ}
    (sample : Fin n → X × Y) (U : ℕ)
    (strategy : AdaptiveMonotoneProposalStrategy X Y)
    (state : MonotoneBountyState X Y)
    (hstructural : MonotoneBountyStructuralInvariant U state)
    (hprevious : MonotoneRejectedRepairsSound law loss epsilon state)
    (hchecker : CheckerDecisionGuaranteed law loss epsilon
      (monotoneBountySubmission U strategy state)
      (certificateCheckerDecision epsilon loss sample
        (monotoneBountySubmission U strategy state))) :
    MonotoneRejectedRepairsSound law loss epsilon
      (monotoneBountyStepFromDecision U strategy state
        (certificateCheckerDecision epsilon loss sample
          (monotoneBountySubmission U strategy state))) := by
  rcases hstructural with
    ⟨_, _, _, _, _, hrejectedClosed, _⟩
  cases hremaining : state.remainingRepairs with
  | nil =>
      have hrejected : state.rejectedRepairsReverse = [] :=
        hrejectedClosed hremaining
      by_cases hmore : state.externalProcessed < U
      · cases hdecision : certificateCheckerDecision epsilon loss sample
            (monotoneBountySubmission U strategy state) with
        | rejected =>
            simp [MonotoneRejectedRepairsSound,
              monotoneBountyStepFromDecision, monotoneBountyStepCore,
              hremaining, hmore, hdecision, hrejected]
        | accepted =>
            simp only [monotoneBountyStepFromDecision,
              monotoneBountyStepCore, hremaining, if_pos hmore, hdecision]
            change MonotoneRejectedRepairsSound law loss epsilon
              (restartMonotoneRepairScan
                { state with
                  current := listUpdate state.current
                    (strategy state.reverseTranscript.reverse).group
                    (strategy state.reverseTranscript.reverse).replacement
                  accepted := state.accepted + 1
                  externalProcessed := state.externalProcessed + 1
                  protectedGroups :=
                    (strategy state.reverseTranscript.reverse).group ::
                      state.protectedGroups })
            exact restartMonotoneRepairScan_rejectedSound law loss epsilon _
      · have hrejectedDecision := repairNoopSubmission_rejected epsilon hepsilon
          loss sample state.current
        have hdecision : certificateCheckerDecision epsilon loss sample
            (monotoneBountySubmission U strategy state) = .rejected := by
          simpa [monotoneBountySubmission, hremaining, hmore] using
            hrejectedDecision
        simpa [MonotoneRejectedRepairsSound,
          monotoneBountyStepFromDecision, monotoneBountyStepCore, hremaining,
          hmore, hdecision] using hprevious
  | cons candidate rest =>
      cases hdecision : certificateCheckerDecision epsilon loss sample
          (monotoneBountySubmission U strategy state) with
      | accepted =>
          simp only [monotoneBountyStepFromDecision, monotoneBountyStepCore,
            hremaining, hdecision]
          change MonotoneRejectedRepairsSound law loss epsilon
            (restartMonotoneRepairScan
              { state with
                current := listUpdate state.current candidate.group
                  candidate.replacement
                accepted := state.accepted + 1 })
          exact restartMonotoneRepairScan_rejectedSound law loss epsilon _
      | rejected =>
          cases rest with
          | nil =>
              simp [MonotoneRejectedRepairsSound,
                monotoneBountyStepFromDecision, monotoneBountyStepCore,
                hremaining, hdecision, publishMonotoneBountyState]
          | cons next tail =>
              have hscore : certificateImprovementScore law loss state.current
                  candidate.group candidate.replacement ≤ epsilon := by
                rw [hdecision] at hchecker
                refine improvementScore_le_of_checker_rejected law loss epsilon
                  hepsilon
                  { current := state.current, group := candidate.group,
                    replacement := candidate.replacement } ?_
                simpa [monotoneBountySubmission, hremaining, hdecision] using
                  hchecker
              simp only [MonotoneRejectedRepairsSound,
                monotoneBountyStepFromDecision, monotoneBountyStepCore,
                hremaining, hdecision, List.mem_cons]
              intro tested htested
              rcases htested with rfl | htested
              · exact hscore
              · exact hprevious tested htested

/-- One actual global query preserves every completed publication guarantee.
The only nontrivial branch is the last rejection of a repair scan, which turns
the scan partition into the new publication certificate. -/
theorem monotoneBountyActualStep_preserves_publicationsSound
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) {n : ℕ}
    (sample : Fin n → X × Y) (U : ℕ)
    (strategy : AdaptiveMonotoneProposalStrategy X Y)
    (state : MonotoneBountyState X Y)
    (hstructural : MonotoneBountyStructuralInvariant U state)
    (hpreviousPublications : MonotonePublicationsSound law loss epsilon state)
    (hpreviousRejected : MonotoneRejectedRepairsSound law loss epsilon state)
    (hchecker : CheckerDecisionGuaranteed law loss epsilon
      (monotoneBountySubmission U strategy state)
      (certificateCheckerDecision epsilon loss sample
        (monotoneBountySubmission U strategy state))) :
    MonotonePublicationsSound law loss epsilon
      (monotoneBountyStepFromDecision U strategy state
        (certificateCheckerDecision epsilon loss sample
          (monotoneBountySubmission U strategy state))) := by
  rcases hstructural with
    ⟨_, hpublic, _, _, hpublicActive, _, hpartition⟩
  cases hremaining : state.remainingRepairs with
  | nil =>
      by_cases hmore : state.externalProcessed < U
      · cases hdecision : certificateCheckerDecision epsilon loss sample
            (monotoneBountySubmission U strategy state) with
        | rejected =>
            simpa [MonotonePublicationsSound,
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
                simpa [MonotonePublicationsSound,
                  monotoneBountyStepFromDecision, monotoneBountyStepCore,
                  hremaining, hmore, hdecision, proposal,
                  restartMonotoneRepairScan, hcandEq] using hpreviousPublications
      · have hrejectedDecision := repairNoopSubmission_rejected epsilon hepsilon
          loss sample state.current
        have hdecision : certificateCheckerDecision epsilon loss sample
            (monotoneBountySubmission U strategy state) = .rejected := by
          simpa [monotoneBountySubmission, hremaining, hmore] using
            hrejectedDecision
        simpa [MonotonePublicationsSound,
          monotoneBountyStepFromDecision, monotoneBountyStepCore,
          hremaining, hmore, hdecision] using hpreviousPublications
  | cons candidate rest =>
      have hpublicGroups : state.publicModels.length ≤
          state.protectedGroups.length := hpublicActive (by simp [hremaining])
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
          cases hcandEq : repairCandidates state.protectedGroups
              state.publicModels with
          | nil => exact (hcandidates hcandEq).elim
          | cons next tail =>
              simpa [MonotonePublicationsSound,
                monotoneBountyStepFromDecision, monotoneBountyStepCore,
                hremaining, hdecision, restartMonotoneRepairScan, hcandEq]
                using hpreviousPublications
      | rejected =>
          have hscore : certificateImprovementScore law loss state.current
              candidate.group candidate.replacement ≤ epsilon := by
            rw [hdecision] at hchecker
            refine improvementScore_le_of_checker_rejected law loss epsilon
              hepsilon
              { current := state.current, group := candidate.group,
                replacement := candidate.replacement } ?_
            simpa [monotoneBountySubmission, hremaining, hdecision] using hchecker
          cases rest with
          | cons next tail =>
              simpa [MonotonePublicationsSound,
                monotoneBountyStepFromDecision, monotoneBountyStepCore,
                hremaining, hdecision] using hpreviousPublications
          | nil =>
              have hpartitionState := hpartition (by simp [hremaining])
              rw [hremaining] at hpartitionState
              have hallScores : ∀ tested ∈ repairCandidates
                  state.protectedGroups state.publicModels,
                  certificateImprovementScore law loss state.current tested.group
                    tested.replacement ≤ epsilon := by
                intro tested htested
                rw [← hpartitionState] at htested
                simp only [List.mem_append, List.mem_singleton] at htested
                rcases htested with htested | rfl
                · have htestedReverse : tested ∈ state.rejectedRepairsReverse := by
                    simpa using htested
                  exact hpreviousRejected tested htestedReverse
                · exact hscore
              have hcurrent := scores_le_imply_groupwiseMonotoneOnHistory
                law loss epsilon state.current state.protectedGroups
                state.publicModels hallScores
              let advanced : MonotoneBountyState X Y :=
                { state with
                  remainingRepairs := []
                  rejectedRepairsReverse :=
                    candidate :: state.rejectedRepairsReverse }
              have hpublish :=
                publishMonotoneBountyState_preserves_publicationsSound
                  law loss epsilon advanced
                  (by simpa [advanced, MonotonePublicationsSound] using
                    hpreviousPublications)
                  (by simpa [advanced] using hcurrent)
              simpa [advanced, monotoneBountyStepFromDecision,
                monotoneBountyStepCore, hremaining, hdecision] using hpublish

/-- Good-event predicate for the literal shared-checker execution of the whole
corrected Algorithm 4 process. -/
def MonotoneBountyRunGuaranteed {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y) (epsilon : ℝ)
    {n : ℕ} (sample : Fin n → X × Y) (Q U : ℕ)
    (initial : Model X Y)
    (strategy : AdaptiveMonotoneProposalStrategy X Y) : Prop :=
  CheckerRunAuxGuaranteed law loss epsilon sample
    (monotoneBountySubmissionStrategy initial U strategy) Q []

/-- The global loss potential is nonincreasing along every good shared-checker
execution. -/
theorem monotoneBountyRunAux_potential_le
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) {n : ℕ}
    (sample : Fin n → X × Y) (initial : Model X Y) (U : ℕ)
    (strategy : AdaptiveMonotoneProposalStrategy X Y) :
    ∀ (remaining : ℕ) (reverseTranscript : List CertificateDecision),
      CheckerRunAuxGuaranteed law loss epsilon sample
          (monotoneBountySubmissionStrategy initial U strategy)
          remaining reverseTranscript →
      let start := monotoneBountyStateFromTranscript initial U strategy
        reverseTranscript.reverse
      let finalTranscript := certificateCheckerRunAux epsilon loss sample
        (monotoneBountySubmissionStrategy initial U strategy)
        remaining reverseTranscript
      let final := monotoneBountyStateFromTranscript initial U strategy
        finalTranscript
      monotoneBountyPotential law loss epsilon final ≤
        monotoneBountyPotential law loss epsilon start := by
  intro remaining
  induction remaining with
  | zero =>
      intro reverseTranscript _
      simp [certificateCheckerRunAux]
  | succ remaining ih =>
      intro reverseTranscript hguaranteed
      by_cases hguard :
          (numberAccepted reverseTranscript : ℝ) ≤ 2 / epsilon
      · let publicTranscript := reverseTranscript.reverse
        let state := monotoneBountyStateFromTranscript initial U strategy
          publicTranscript
        let submission := monotoneBountySubmission U strategy state
        let decision := certificateCheckerDecision epsilon loss sample submission
        have hparts : CheckerDecisionGuaranteed law loss epsilon submission decision ∧
            CheckerRunAuxGuaranteed law loss epsilon sample
              (monotoneBountySubmissionStrategy initial U strategy)
              remaining (decision :: reverseTranscript) := by
          simpa [CheckerRunAuxGuaranteed, hguard,
            monotoneBountySubmissionStrategy, publicTranscript, state,
            submission, decision] using hguaranteed
        have hstep : monotoneBountyPotential law loss epsilon
              (monotoneBountyStepFromDecision U strategy state decision) ≤
            monotoneBountyPotential law loss epsilon state :=
          monotoneBountyActualStep_potential_le law loss epsilon hepsilon sample
            U strategy state (by simpa [submission, decision] using hparts.1)
        have hnextState :
            monotoneBountyStateFromTranscript initial U strategy
                (decision :: reverseTranscript).reverse =
              monotoneBountyStepFromDecision U strategy state decision := by
          simp only [List.reverse_cons]
          simpa [state, publicTranscript] using
            (monotoneBountyStateFromTranscript_append_singleton initial U
              strategy publicTranscript decision)
        have htail := ih (decision :: reverseTranscript) hparts.2
        have hstep' : monotoneBountyPotential law loss epsilon
              (monotoneBountyStateFromTranscript initial U strategy
                (decision :: reverseTranscript).reverse) ≤
            monotoneBountyPotential law loss epsilon
              (monotoneBountyStateFromTranscript initial U strategy
                reverseTranscript.reverse) := by
          rw [hnextState]
          simpa [state, publicTranscript] using hstep
        simp only [certificateCheckerRunAux, hguard, if_pos]
        exact htail.trans hstep'
      · simp [certificateCheckerRunAux, hguard]

/-- The global potential converts the paper's real loss bound into the exact
rounded acceptance budget. -/
theorem monotoneBountyState_accepted_le_budget
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (initial : Model X Y)
    (state : MonotoneBountyState X Y)
    (hpotential : monotoneBountyPotential law loss epsilon state ≤
      modelLoss law loss initial) :
    state.accepted ≤ checkerAcceptanceBudget epsilon := by
  have hstateNonneg : 0 ≤ modelLoss law loss state.current :=
    modelLoss_nonneg law loss state.current
  have hinitialOne : modelLoss law loss initial ≤ 1 :=
    modelLoss_le_one law loss initial
  have hmul : (state.accepted : ℝ) * epsilon ≤ 2 := by
    unfold monotoneBountyPotential at hpotential
    nlinarith
  have hreal : (state.accepted : ℝ) ≤ 2 / epsilon :=
    (le_div_iff₀ hepsilon).2 hmul
  unfold checkerAcceptanceBudget
  exact Nat.le_floor hreal

/-- The loss budget keeps the source guard open, so a good global execution
processes its entire declared horizon. -/
theorem monotoneBountyRunAux_length_eq
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) {n : ℕ}
    (sample : Fin n → X × Y) (initial : Model X Y) (U : ℕ)
    (strategy : AdaptiveMonotoneProposalStrategy X Y) :
    ∀ (remaining : ℕ) (reverseTranscript : List CertificateDecision),
      CheckerRunAuxGuaranteed law loss epsilon sample
          (monotoneBountySubmissionStrategy initial U strategy)
          remaining reverseTranscript →
      monotoneBountyPotential law loss epsilon
          (monotoneBountyStateFromTranscript initial U strategy
            reverseTranscript.reverse) ≤ modelLoss law loss initial →
      (certificateCheckerRunAux epsilon loss sample
          (monotoneBountySubmissionStrategy initial U strategy)
          remaining reverseTranscript).length =
        reverseTranscript.length + remaining := by
  intro remaining
  induction remaining with
  | zero =>
      intro reverseTranscript _ _
      simp [certificateCheckerRunAux]
  | succ remaining ih =>
      intro reverseTranscript hguaranteed hpotential
      let publicTranscript := reverseTranscript.reverse
      let state := monotoneBountyStateFromTranscript initial U strategy
        publicTranscript
      have hstateAccepted : state.accepted = numberAccepted reverseTranscript := by
        dsimp [state, publicTranscript]
        rw [monotoneBountyStateFromTranscript_accepted, numberAccepted_reverse]
      have hstateNonneg : 0 ≤ modelLoss law loss state.current :=
        modelLoss_nonneg law loss state.current
      have hinitialOne : modelLoss law loss initial ≤ 1 :=
        modelLoss_le_one law loss initial
      have hacceptedMul : (state.accepted : ℝ) * epsilon ≤ 2 := by
        unfold monotoneBountyPotential at hpotential
        nlinarith
      have hguard : (numberAccepted reverseTranscript : ℝ) ≤ 2 / epsilon := by
        apply (le_div_iff₀ hepsilon).2
        simpa [hstateAccepted] using hacceptedMul
      let submission := monotoneBountySubmission U strategy state
      let decision := certificateCheckerDecision epsilon loss sample submission
      have hparts : CheckerDecisionGuaranteed law loss epsilon submission decision ∧
          CheckerRunAuxGuaranteed law loss epsilon sample
            (monotoneBountySubmissionStrategy initial U strategy)
            remaining (decision :: reverseTranscript) := by
        simpa [CheckerRunAuxGuaranteed, hguard,
          monotoneBountySubmissionStrategy, publicTranscript, state, submission,
          decision] using hguaranteed
      have hstep : monotoneBountyPotential law loss epsilon
            (monotoneBountyStepFromDecision U strategy state decision) ≤
          monotoneBountyPotential law loss epsilon state :=
        monotoneBountyActualStep_potential_le law loss epsilon hepsilon sample U
          strategy state (by simpa [submission, decision] using hparts.1)
      have hnextState :
          monotoneBountyStateFromTranscript initial U strategy
              (decision :: reverseTranscript).reverse =
            monotoneBountyStepFromDecision U strategy state decision := by
        simp only [List.reverse_cons]
        simpa [state, publicTranscript] using
          (monotoneBountyStateFromTranscript_append_singleton initial U strategy
            publicTranscript decision)
      have hnextPotential : monotoneBountyPotential law loss epsilon
            (monotoneBountyStateFromTranscript initial U strategy
              (decision :: reverseTranscript).reverse) ≤
          modelLoss law loss initial := by
        rw [hnextState]
        exact hstep.trans (by simpa [state, publicTranscript] using hpotential)
      have htail := ih (decision :: reverseTranscript) hparts.2 hnextPotential
      simp only [certificateCheckerRunAux, hguard, if_pos]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

/-- Publication and active-rejection soundness propagate together through the
entire good shared-checker execution. -/
theorem monotoneBountyRunAux_preserves_soundness
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) {n : ℕ}
    (sample : Fin n → X × Y) (initial : Model X Y) (U : ℕ)
    (strategy : AdaptiveMonotoneProposalStrategy X Y) :
    ∀ (remaining : ℕ) (reverseTranscript : List CertificateDecision),
      CheckerRunAuxGuaranteed law loss epsilon sample
          (monotoneBountySubmissionStrategy initial U strategy)
          remaining reverseTranscript →
      MonotonePublicationsSound law loss epsilon
        (monotoneBountyStateFromTranscript initial U strategy
          reverseTranscript.reverse) →
      MonotoneRejectedRepairsSound law loss epsilon
        (monotoneBountyStateFromTranscript initial U strategy
          reverseTranscript.reverse) →
      let finalTranscript := certificateCheckerRunAux epsilon loss sample
        (monotoneBountySubmissionStrategy initial U strategy)
        remaining reverseTranscript
      let final := monotoneBountyStateFromTranscript initial U strategy
        finalTranscript
      MonotonePublicationsSound law loss epsilon final ∧
        MonotoneRejectedRepairsSound law loss epsilon final := by
  intro remaining
  induction remaining with
  | zero =>
      intro reverseTranscript _ hpublic hrejected
      simpa [certificateCheckerRunAux] using And.intro hpublic hrejected
  | succ remaining ih =>
      intro reverseTranscript hguaranteed hpublic hrejected
      by_cases hguard :
          (numberAccepted reverseTranscript : ℝ) ≤ 2 / epsilon
      · let publicTranscript := reverseTranscript.reverse
        let state := monotoneBountyStateFromTranscript initial U strategy
          publicTranscript
        let submission := monotoneBountySubmission U strategy state
        let decision := certificateCheckerDecision epsilon loss sample submission
        have hparts : CheckerDecisionGuaranteed law loss epsilon submission decision ∧
            CheckerRunAuxGuaranteed law loss epsilon sample
              (monotoneBountySubmissionStrategy initial U strategy)
              remaining (decision :: reverseTranscript) := by
          simpa [CheckerRunAuxGuaranteed, hguard,
            monotoneBountySubmissionStrategy, publicTranscript, state,
            submission, decision] using hguaranteed
        have hstructural : MonotoneBountyStructuralInvariant U state := by
          simpa [state, publicTranscript] using
            (monotoneBountyReplayAux_structural initial U strategy
              publicTranscript)
        have hpublicState : MonotonePublicationsSound law loss epsilon state := by
          simpa [state, publicTranscript] using hpublic
        have hrejectedState : MonotoneRejectedRepairsSound law loss epsilon state := by
          simpa [state, publicTranscript] using hrejected
        have hpublicNext :=
          monotoneBountyActualStep_preserves_publicationsSound law loss epsilon
            hepsilon sample U strategy state hstructural hpublicState
            hrejectedState (by simpa [submission, decision] using hparts.1)
        have hrejectedNext :=
          monotoneBountyActualStep_preserves_rejectedSound law loss epsilon
            hepsilon sample U strategy state hstructural hrejectedState
            (by simpa [submission, decision] using hparts.1)
        have hnextState :
            monotoneBountyStateFromTranscript initial U strategy
                (decision :: reverseTranscript).reverse =
              monotoneBountyStepFromDecision U strategy state decision := by
          simp only [List.reverse_cons]
          simpa [state, publicTranscript] using
            (monotoneBountyStateFromTranscript_append_singleton initial U strategy
              publicTranscript decision)
        have htail := ih (decision :: reverseTranscript) hparts.2
          (by rw [hnextState]; exact hpublicNext)
          (by rw [hnextState]; exact hrejectedNext)
        simp only [certificateCheckerRunAux, hguard, if_pos]
        exact htail
      · simpa [certificateCheckerRunAux, hguard] using
          And.intro hpublic hrejected

/-- The whole process is complete once all external submissions have been
processed and no repair scan remains active. -/
def MonotoneBountyComplete {X Y : Type*} (U : ℕ)
    (state : MonotoneBountyState X Y) : Prop :=
  state.externalProcessed = U ∧ state.remainingRepairs = []

/-- Remaining global combinatorial work.  Each still-available acceptance can
start at most one grid of size `K²`; external rejections consume the first term
and repair rejections consume the last. -/
def monotoneBountyMetric {X Y : Type*} (U K : ℕ)
    (state : MonotoneBountyState X Y) : ℕ :=
  U - state.externalProcessed +
    (K - state.accepted) * K ^ 2 + state.remainingRepairs.length

/-- A restarted grid has at most `K²` entries when its two axes have length at
most `K`. -/
theorem restartMonotoneRepairScan_remaining_length_le_square
    {X Y : Type*} (K : ℕ) (state : MonotoneBountyState X Y)
    (hgroups : state.protectedGroups.length ≤ K)
    (hpublic : state.publicModels.length ≤ K) :
    (restartMonotoneRepairScan state).remainingRepairs.length ≤ K ^ 2 := by
  cases hcandidates : repairCandidates state.protectedGroups state.publicModels with
  | nil =>
      simp [restartMonotoneRepairScan, hcandidates,
        publishMonotoneBountyState]
  | cons candidate rest =>
      simp only [restartMonotoneRepairScan, hcandidates]
      have hlen : (repairCandidates state.protectedGroups
          state.publicModels).length ≤ K ^ 2 := by
        rw [repairCandidates_length]
        have hmul := Nat.mul_le_mul hgroups hpublic
        simpa [pow_two] using hmul
      rw [hcandidates] at hlen
      exact hlen

/-- Every noncomplete transition strictly decreases the global work metric,
provided the post-transition accepted count remains in the checker budget. -/
theorem monotoneBountyStep_metric_lt
    {X Y : Type*} (U K : ℕ)
    (strategy : AdaptiveMonotoneProposalStrategy X Y)
    (state : MonotoneBountyState X Y) (decision : CertificateDecision)
    (hstructural : MonotoneBountyStructuralInvariant U state)
    (hincomplete : ¬ MonotoneBountyComplete U state)
    (hnextCap :
      (monotoneBountyStepFromDecision U strategy state decision).accepted ≤ K) :
    monotoneBountyMetric U K
        (monotoneBountyStepFromDecision U strategy state decision) <
      monotoneBountyMetric U K state := by
  rcases hstructural with
    ⟨hexternal, _, hgroupAccepted, hpublicGroupSucc,
      hpublicGroupActive, _, _⟩
  have hacceptedMono : state.accepted ≤
      (monotoneBountyStepFromDecision U strategy state decision).accepted := by
    rw [monotoneBountyStepFromDecision_accepted]
    omega
  have hcurrentCap : state.accepted ≤ K := hacceptedMono.trans hnextCap
  cases hremaining : state.remainingRepairs with
  | nil =>
      have hmore : state.externalProcessed < U := by
        by_contra hnot
        have heq : state.externalProcessed = U := by omega
        exact hincomplete ⟨heq, hremaining⟩
      cases decision with
      | rejected =>
          simp only [monotoneBountyMetric, monotoneBountyStepFromDecision,
            monotoneBountyStepCore, hremaining, if_pos hmore,
            List.length_nil]
          change U - (state.externalProcessed + 1) +
              (K - state.accepted) * K ^ 2 <
            U - state.externalProcessed + (K - state.accepted) * K ^ 2
          omega
      | accepted =>
          let proposal := strategy state.reverseTranscript.reverse
          let updated : MonotoneBountyState X Y :=
            { state with
              current := listUpdate state.current proposal.group
                proposal.replacement
              accepted := state.accepted + 1
              externalProcessed := state.externalProcessed + 1
              protectedGroups := proposal.group :: state.protectedGroups }
          have hacceptedNext : state.accepted + 1 ≤ K := by
            simpa [monotoneBountyStepFromDecision, monotoneBountyStepCore,
              hremaining, hmore] using hnextCap
          have hgroupsUpdated : updated.protectedGroups.length ≤ K := by
            dsimp [updated]
            omega
          have hpublicUpdated : updated.publicModels.length ≤ K := by
            dsimp [updated]
            omega
          have hremainingBound :=
            restartMonotoneRepairScan_remaining_length_le_square K updated
              hgroupsUpdated hpublicUpdated
          have hsub : K - state.accepted = K - (state.accepted + 1) + 1 := by
            omega
          simp only [monotoneBountyMetric, monotoneBountyStepFromDecision,
            monotoneBountyStepCore, hremaining, if_pos hmore,
            restartMonotoneRepairScan_externalProcessed,
            restartMonotoneRepairScan_accepted, List.length_nil]
          change U - (state.externalProcessed + 1) +
                (K - (state.accepted + 1)) * K ^ 2 +
                (restartMonotoneRepairScan updated).remainingRepairs.length <
              U - state.externalProcessed +
                (K - state.accepted) * K ^ 2
          rw [hsub, Nat.add_mul]
          omega
  | cons candidate rest =>
      have hpublicGroups : state.publicModels.length ≤
          state.protectedGroups.length :=
        hpublicGroupActive (by simp [hremaining])
      have hgroupsCap : state.protectedGroups.length ≤ K :=
        hgroupAccepted.trans hcurrentCap
      have hpublicCap : state.publicModels.length ≤ K :=
        hpublicGroups.trans hgroupsCap
      cases decision with
      | rejected =>
          cases rest <;>
            simp [monotoneBountyMetric, monotoneBountyStepFromDecision,
              monotoneBountyStepCore, hremaining,
              publishMonotoneBountyState]
      | accepted =>
          let updated : MonotoneBountyState X Y :=
            { state with
              current := listUpdate state.current candidate.group
                candidate.replacement
              accepted := state.accepted + 1 }
          have hacceptedNext : state.accepted + 1 ≤ K := by
            simpa [monotoneBountyStepFromDecision, monotoneBountyStepCore,
              hremaining] using hnextCap
          have hremainingBound :=
            restartMonotoneRepairScan_remaining_length_le_square K updated
              (by simpa [updated] using hgroupsCap)
              (by simpa [updated] using hpublicCap)
          have hsub : K - state.accepted = K - (state.accepted + 1) + 1 := by
            omega
          simp only [monotoneBountyMetric, monotoneBountyStepFromDecision,
            monotoneBountyStepCore, hremaining,
            restartMonotoneRepairScan_externalProcessed,
            restartMonotoneRepairScan_accepted, List.length_cons]
          change U - state.externalProcessed +
                (K - (state.accepted + 1)) * K ^ 2 +
                (restartMonotoneRepairScan updated).remainingRepairs.length <
              U - state.externalProcessed +
                (K - state.accepted) * K ^ 2 + (rest.length + 1)
          rw [hsub, Nat.add_mul]
          omega

/-- The initial metric is exactly the paper's rounded cubic horizon. -/
theorem initialMonotoneBountyState_metric {X Y : Type*}
    (initial : Model X Y) (U K : ℕ) :
    monotoneBountyMetric U K (initialMonotoneBountyState initial) =
      U + K ^ 3 := by
  simp [monotoneBountyMetric, initialMonotoneBountyState]
  ring

/-- Once complete, the actual totalized global transition remains complete:
the only possible query is the deterministic rejected no-op. -/
theorem monotoneBountyActualStep_preserves_complete
    {X Y : Type*} {n : ℕ}
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (loss : BoundedLoss Y) (sample : Fin n → X × Y) (U : ℕ)
    (strategy : AdaptiveMonotoneProposalStrategy X Y)
    (state : MonotoneBountyState X Y)
    (hcomplete : MonotoneBountyComplete U state) :
    MonotoneBountyComplete U
      (monotoneBountyStepFromDecision U strategy state
        (certificateCheckerDecision epsilon loss sample
          (monotoneBountySubmission U strategy state))) := by
  rcases hcomplete with ⟨hexternal, hremaining⟩
  have hmore : ¬ state.externalProcessed < U := by omega
  have hrejected := repairNoopSubmission_rejected epsilon hepsilon loss sample
    state.current
  have hdecision : certificateCheckerDecision epsilon loss sample
      (monotoneBountySubmission U strategy state) = .rejected := by
    simpa [monotoneBountySubmission, hremaining, hmore] using hrejected
  simp [MonotoneBountyComplete, monotoneBountyStepFromDecision,
    monotoneBountyStepCore, hremaining, hmore, hdecision, hexternal]

/-- Completion is preserved through any remaining totalized checker horizon. -/
theorem monotoneBountyRunAux_preserves_complete
    {X Y : Type*} {n : ℕ}
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (loss : BoundedLoss Y) (sample : Fin n → X × Y)
    (initial : Model X Y) (U : ℕ)
    (strategy : AdaptiveMonotoneProposalStrategy X Y) :
    ∀ (remaining : ℕ) (reverseTranscript : List CertificateDecision),
      MonotoneBountyComplete U
        (monotoneBountyStateFromTranscript initial U strategy
          reverseTranscript.reverse) →
      MonotoneBountyComplete U
        (monotoneBountyStateFromTranscript initial U strategy
          (certificateCheckerRunAux epsilon loss sample
            (monotoneBountySubmissionStrategy initial U strategy)
            remaining reverseTranscript)) := by
  intro remaining
  induction remaining with
  | zero =>
      intro reverseTranscript hcomplete
      simpa [certificateCheckerRunAux] using hcomplete
  | succ remaining ih =>
      intro reverseTranscript hcomplete
      by_cases hguard :
          (numberAccepted reverseTranscript : ℝ) ≤ 2 / epsilon
      · let publicTranscript := reverseTranscript.reverse
        let state := monotoneBountyStateFromTranscript initial U strategy
          publicTranscript
        let decision := certificateCheckerDecision epsilon loss sample
          (monotoneBountySubmission U strategy state)
        have hstateComplete : MonotoneBountyComplete U state := by
          simpa [state, publicTranscript] using hcomplete
        have hnextComplete := monotoneBountyActualStep_preserves_complete
          epsilon hepsilon loss sample U strategy state hstateComplete
        have hnextState :
            monotoneBountyStateFromTranscript initial U strategy
                (decision :: reverseTranscript).reverse =
              monotoneBountyStepFromDecision U strategy state decision := by
          simp only [List.reverse_cons]
          simpa [state, publicTranscript] using
            (monotoneBountyStateFromTranscript_append_singleton initial U strategy
              publicTranscript decision)
        simp only [certificateCheckerRunAux, hguard, if_pos]
        apply ih (decision :: reverseTranscript)
        rw [hnextState]
        exact hnextComplete
      · simpa [certificateCheckerRunAux, hguard] using hcomplete

/-- If the remaining horizon dominates the global metric, every good execution
finishes all external proposals and the last repair scan. -/
theorem monotoneBountyRunAux_completes
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) {n : ℕ}
    (sample : Fin n → X × Y) (initial : Model X Y) (U : ℕ)
    (strategy : AdaptiveMonotoneProposalStrategy X Y) :
    ∀ (remaining : ℕ) (reverseTranscript : List CertificateDecision),
      CheckerRunAuxGuaranteed law loss epsilon sample
          (monotoneBountySubmissionStrategy initial U strategy)
          remaining reverseTranscript →
      monotoneBountyPotential law loss epsilon
          (monotoneBountyStateFromTranscript initial U strategy
            reverseTranscript.reverse) ≤ modelLoss law loss initial →
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
            (monotoneBountyReplayAux_structural initial U strategy
              reverseTranscript.reverse)
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
      let state := monotoneBountyStateFromTranscript initial U strategy
        publicTranscript
      have hstructural : MonotoneBountyStructuralInvariant U state := by
        simpa [state, publicTranscript] using
          (monotoneBountyReplayAux_structural initial U strategy publicTranscript)
      by_cases hcomplete : MonotoneBountyComplete U state
      · exact monotoneBountyRunAux_preserves_complete epsilon hepsilon loss
          sample initial U strategy (remaining + 1) reverseTranscript
          (by simpa [state, publicTranscript] using hcomplete)
      · have hstateAccepted : state.accepted =
            numberAccepted reverseTranscript := by
          dsimp [state, publicTranscript]
          rw [monotoneBountyStateFromTranscript_accepted,
            numberAccepted_reverse]
        have hstateNonneg : 0 ≤ modelLoss law loss state.current :=
          modelLoss_nonneg law loss state.current
        have hinitialOne : modelLoss law loss initial ≤ 1 :=
          modelLoss_le_one law loss initial
        have hacceptedMul : (state.accepted : ℝ) * epsilon ≤ 2 := by
          have hp : monotoneBountyPotential law loss epsilon state ≤
              modelLoss law loss initial := by
            simpa [state, publicTranscript] using hpotential
          unfold monotoneBountyPotential at hp
          nlinarith
        have hguard : (numberAccepted reverseTranscript : ℝ) ≤
            2 / epsilon := by
          apply (le_div_iff₀ hepsilon).2
          simpa [hstateAccepted] using hacceptedMul
        let submission := monotoneBountySubmission U strategy state
        let decision := certificateCheckerDecision epsilon loss sample submission
        have hparts : CheckerDecisionGuaranteed law loss epsilon submission decision ∧
            CheckerRunAuxGuaranteed law loss epsilon sample
              (monotoneBountySubmissionStrategy initial U strategy)
              remaining (decision :: reverseTranscript) := by
          simpa [CheckerRunAuxGuaranteed, hguard,
            monotoneBountySubmissionStrategy, publicTranscript, state,
            submission, decision] using hguaranteed
        have hstep : monotoneBountyPotential law loss epsilon
              (monotoneBountyStepFromDecision U strategy state decision) ≤
            monotoneBountyPotential law loss epsilon state :=
          monotoneBountyActualStep_potential_le law loss epsilon hepsilon sample
            U strategy state (by simpa [submission, decision] using hparts.1)
        have hnextState :
            monotoneBountyStateFromTranscript initial U strategy
                (decision :: reverseTranscript).reverse =
              monotoneBountyStepFromDecision U strategy state decision := by
          simp only [List.reverse_cons]
          simpa [state, publicTranscript] using
            (monotoneBountyStateFromTranscript_append_singleton initial U strategy
              publicTranscript decision)
        have hnextPotential : monotoneBountyPotential law loss epsilon
              (monotoneBountyStateFromTranscript initial U strategy
                (decision :: reverseTranscript).reverse) ≤
            modelLoss law loss initial := by
          rw [hnextState]
          exact hstep.trans (by simpa [state, publicTranscript] using hpotential)
        have hnextCap :
            (monotoneBountyStepFromDecision U strategy state decision).accepted ≤
              checkerAcceptanceBudget epsilon :=
          monotoneBountyState_accepted_le_budget law loss epsilon hepsilon
            initial _ (by rw [← hnextState]; exact hnextPotential)
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
        exact ih (decision :: reverseTranscript) hparts.2 hnextPotential
          hnextMetric

/-- The rounded cubic horizon suffices for whole-process completion on the
shared checker good event. -/
theorem monotoneBountyOutput_complete
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) {n : ℕ}
    (sample : Fin n → X × Y) (U : ℕ) (initial : Model X Y)
    (strategy : AdaptiveMonotoneProposalStrategy X Y)
    (hguaranteed : MonotoneBountyRunGuaranteed law loss epsilon sample
      (monotoneBountyQueryBudget epsilon U) U initial strategy) :
    MonotoneBountyComplete U
      (monotoneBountyOutput epsilon loss sample U initial strategy) := by
  have hpotential : monotoneBountyPotential law loss epsilon
      (monotoneBountyStateFromTranscript initial U strategy [].reverse) ≤
        modelLoss law loss initial := by
    simp [monotoneBountyPotential, monotoneBountyStateFromTranscript,
      monotoneBountyReplayAux, initialMonotoneBountyState]
  have hmetric : monotoneBountyMetric U (checkerAcceptanceBudget epsilon)
      (monotoneBountyStateFromTranscript initial U strategy [].reverse) ≤
        monotoneBountyQueryBudget epsilon U := by
    simp [monotoneBountyStateFromTranscript, monotoneBountyReplayAux,
      monotoneBountyQueryBudget, initialMonotoneBountyState_metric]
  have hcomplete := monotoneBountyRunAux_completes law loss epsilon hepsilon
    sample initial U strategy (monotoneBountyQueryBudget epsilon U) []
    hguaranteed hpotential hmetric
  simpa [monotoneBountyOutput, monotoneBountyTranscript,
    certificateCheckerRun] using hcomplete

/-- A good whole-process run uses every slot in its declared (at-most) query
horizon; slots after semantic completion are deterministic rejected no-ops. -/
theorem monotoneBountyTranscript_length
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) {n : ℕ}
    (sample : Fin n → X × Y) (U : ℕ) (initial : Model X Y)
    (strategy : AdaptiveMonotoneProposalStrategy X Y)
    (hguaranteed : MonotoneBountyRunGuaranteed law loss epsilon sample
      (monotoneBountyQueryBudget epsilon U) U initial strategy) :
    (monotoneBountyTranscript epsilon loss sample U initial strategy).length =
      monotoneBountyQueryBudget epsilon U := by
  have hpotential : monotoneBountyPotential law loss epsilon
      (monotoneBountyStateFromTranscript initial U strategy [].reverse) ≤
        modelLoss law loss initial := by
    simp [monotoneBountyPotential, monotoneBountyStateFromTranscript,
      monotoneBountyReplayAux, initialMonotoneBountyState]
  have hlength := monotoneBountyRunAux_length_eq law loss epsilon hepsilon
    sample initial U strategy (monotoneBountyQueryBudget epsilon U) []
    hguaranteed hpotential
  simpa [monotoneBountyTranscript, certificateCheckerRun] using hlength

/-- The good-run output retains the initial global potential bound. -/
theorem monotoneBountyOutput_potential_le
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) {n : ℕ}
    (sample : Fin n → X × Y) (U : ℕ) (initial : Model X Y)
    (strategy : AdaptiveMonotoneProposalStrategy X Y)
    (hguaranteed : MonotoneBountyRunGuaranteed law loss epsilon sample
      (monotoneBountyQueryBudget epsilon U) U initial strategy) :
    monotoneBountyPotential law loss epsilon
        (monotoneBountyOutput epsilon loss sample U initial strategy) ≤
      modelLoss law loss initial := by
  have hpotential := monotoneBountyRunAux_potential_le law loss epsilon
    hepsilon sample initial U strategy (monotoneBountyQueryBudget epsilon U) []
    hguaranteed
  simpa [monotoneBountyOutput, monotoneBountyTranscript,
    certificateCheckerRun, monotoneBountyPotential,
    monotoneBountyStateFromTranscript, monotoneBountyReplayAux,
    initialMonotoneBountyState] using hpotential

/-- The whole process admits at most `floor (2/epsilon)` accepted external or
repair updates in total. -/
theorem monotoneBountyOutput_accepted_le_budget
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) {n : ℕ}
    (sample : Fin n → X × Y) (U : ℕ) (initial : Model X Y)
    (strategy : AdaptiveMonotoneProposalStrategy X Y)
    (hguaranteed : MonotoneBountyRunGuaranteed law loss epsilon sample
      (monotoneBountyQueryBudget epsilon U) U initial strategy) :
    (monotoneBountyOutput epsilon loss sample U initial strategy).accepted ≤
      checkerAcceptanceBudget epsilon :=
  monotoneBountyState_accepted_le_budget law loss epsilon hepsilon initial _
    (monotoneBountyOutput_potential_le law loss epsilon hepsilon sample U
      initial strategy hguaranteed)

/-- Every model actually published by a good whole-process run satisfies the
paper's protected-group history inequality. -/
theorem monotoneBountyOutput_publicationsSound
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) {n : ℕ}
    (sample : Fin n → X × Y) (U : ℕ) (initial : Model X Y)
    (strategy : AdaptiveMonotoneProposalStrategy X Y)
    (hguaranteed : MonotoneBountyRunGuaranteed law loss epsilon sample
      (monotoneBountyQueryBudget epsilon U) U initial strategy) :
    MonotonePublicationsSound law loss epsilon
      (monotoneBountyOutput epsilon loss sample U initial strategy) := by
  have hinitialPublic : MonotonePublicationsSound law loss epsilon
      (monotoneBountyStateFromTranscript initial U strategy [].reverse) := by
    simp [MonotonePublicationsSound, monotoneBountyStateFromTranscript,
      monotoneBountyReplayAux, initialMonotoneBountyState]
  have hinitialRejected : MonotoneRejectedRepairsSound law loss epsilon
      (monotoneBountyStateFromTranscript initial U strategy [].reverse) := by
    simp [MonotoneRejectedRepairsSound, monotoneBountyStateFromTranscript,
      monotoneBountyReplayAux, initialMonotoneBountyState]
  have hsound := monotoneBountyRunAux_preserves_soundness law loss epsilon
    hepsilon sample initial U strategy (monotoneBountyQueryBudget epsilon U) []
    hguaranteed hinitialPublic hinitialRejected
  simpa [monotoneBountyOutput, monotoneBountyTranscript,
    certificateCheckerRun] using hsound.1

/-- Complete deterministic conclusion of corrected whole-process Algorithm 4.
The first conjunct retains all Theorem 11 decision semantics for external and
internal queries on their single shared checker stream. -/
def MonotoneBountyConclusion {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y) (epsilon : ℝ)
    {n : ℕ} (sample : Fin n → X × Y) (U : ℕ)
    (initial : Model X Y)
    (strategy : AdaptiveMonotoneProposalStrategy X Y) : Prop :=
  let Q := monotoneBountyQueryBudget epsilon U
  let transcript := monotoneBountyTranscript epsilon loss sample U initial strategy
  let output := monotoneBountyOutput epsilon loss sample U initial strategy
  MonotoneBountyRunGuaranteed law loss epsilon sample Q U initial strategy ∧
    transcript.length = Q ∧
    output.externalProcessed = U ∧
    output.remainingRepairs = [] ∧
    output.accepted ≤ checkerAcceptanceBudget epsilon ∧
    MonotonePublicationsSound law loss epsilon output

/-- The shared-checker good event implies every whole-process conclusion. -/
theorem monotoneBountyConclusion_of_runGuaranteed
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) {n : ℕ}
    (sample : Fin n → X × Y) (U : ℕ) (initial : Model X Y)
    (strategy : AdaptiveMonotoneProposalStrategy X Y)
    (hguaranteed : MonotoneBountyRunGuaranteed law loss epsilon sample
      (monotoneBountyQueryBudget epsilon U) U initial strategy) :
    MonotoneBountyConclusion law loss epsilon sample U initial strategy := by
  have hcomplete := monotoneBountyOutput_complete law loss epsilon hepsilon
    sample U initial strategy hguaranteed
  refine ⟨hguaranteed,
    monotoneBountyTranscript_length law loss epsilon hepsilon sample U initial
      strategy hguaranteed,
    hcomplete.1, hcomplete.2,
    monotoneBountyOutput_accepted_le_budget law loss epsilon hepsilon sample U
      initial strategy hguaranteed,
    monotoneBountyOutput_publicationsSound law loss epsilon hepsilon sample U
      initial strategy hguaranteed⟩

/-- Probability that corrected whole-process Algorithm 4 violates any local
checker, completion, acceptance-budget, or publication conclusion. -/
noncomputable def monotoneBountyFailure
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (n U : ℕ) (initial : Model X Y)
    (strategy : AdaptiveMonotoneProposalStrategy X Y) : ℝ := by
  classical
  exact pmfProb (pmfProduct (Fin n) (X × Y) law) (fun sample =>
    ¬ MonotoneBountyConclusion law loss epsilon sample U initial strategy)

/-- A bad whole-process execution is a bad execution of the induced shared
Algorithm 2 checker stream. -/
theorem monotoneBountyFailure_le_checkerFailure
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (n U : ℕ)
    (initial : Model X Y)
    (strategy : AdaptiveMonotoneProposalStrategy X Y) :
    monotoneBountyFailure law loss epsilon n U initial strategy ≤
      certificateCheckerRunGuaranteeFailure law loss epsilon n
        (monotoneBountyQueryBudget epsilon U)
        (monotoneBountySubmissionStrategy initial U strategy) := by
  classical
  unfold monotoneBountyFailure certificateCheckerRunGuaranteeFailure
  apply pmfProb_le_of_imp
  intro sample hbad
  intro hchecker
  exact hbad (monotoneBountyConclusion_of_runGuaranteed law loss epsilon
    hepsilon sample U initial strategy hchecker)

/-- Corrected whole-process Theorem 14 with explicit sparse-transcript failure
probability and the exact rounded cubic query horizon. -/
theorem theorem14_monotoneBounty
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (n U : ℕ)
    (hcount : 0 < n) (initial : Model X Y)
    (strategy : AdaptiveMonotoneProposalStrategy X Y) :
    let Q := monotoneBountyQueryBudget epsilon U
    monotoneBountyFailure law loss epsilon n U initial strategy ≤
      (Q * (Q + 1) ^ checkerAcceptanceBudget epsilon : ℕ) * 2 *
        Real.exp (-(n : ℝ) * epsilon ^ 2 / 32) := by
  let Q := monotoneBountyQueryBudget epsilon U
  calc
    monotoneBountyFailure law loss epsilon n U initial strategy ≤
        certificateCheckerRunGuaranteeFailure law loss epsilon n Q
          (monotoneBountySubmissionStrategy initial U strategy) :=
      monotoneBountyFailure_le_checkerFailure law loss epsilon hepsilon n U
        initial strategy
    _ ≤ (Q * (Q + 1) ^ checkerAcceptanceBudget epsilon : ℕ) * 2 *
          Real.exp (-(n : ℝ) * epsilon ^ 2 / 32) :=
      theorem11_adaptive_certificateCheckerRun law loss epsilon hepsilon n Q
        hcount (monotoneBountySubmissionStrategy initial U strategy)
end

end GHKR22BiasBounties

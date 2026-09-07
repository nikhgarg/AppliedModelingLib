import GHKR22BiasBounties.AdaptiveChecker
import Mathlib.Data.List.MinMax
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Falsify-and-update and monotone repair

This file formalizes Algorithms 3--4 and Theorems 12 and 14.  In addition to
the local deterministic update lemmas, it gives literal transcript-adaptive
executions and finite-sample failure probabilities.  Thus the paper-facing
theorems do not assume as a premise that the realized holdout queries happened
to be accurate: that event is derived from the sparse-transcript concentration
theorem proved for Algorithm 2.

For Algorithm 4 we give the intended restart-until-closed semantics: after an
accepted repair, the algorithm scans the repair candidates again against the
new current model.  This makes explicit a detail that the printed pseudocode
obscures and is exactly the invariant used in the source proof.
-/

namespace GHKR22BiasBounties

noncomputable section

open AppliedModelingLib Probability

/-- A public `(group, replacement)` proposal. -/
structure ProposedUpdate (X Y : Type*) where
  group : Group X
  replacement : Model X Y

/-- Algorithm 3 state.  The transcript is stored newest-first. -/
structure FalsifyState (X Y : Type*) where
  current : Model X Y
  accepted : ℕ
  reverseTranscript : List CertificateDecision

/-- Population-loss accounting potential used in Theorems 12 and 14. -/
def falsifyPotential {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y) (epsilon : ℝ)
    (state : FalsifyState X Y) : ℝ :=
  modelLoss law loss state.current + (state.accepted : ℝ) * (epsilon / 2)

/-- Initial Algorithm 3 state. -/
def initialFalsifyState {X Y : Type*} (f : Model X Y) : FalsifyState X Y :=
  { current := f, accepted := 0, reverseTranscript := [] }

/-- Convert a proposal at a state into the checker triple. -/
def proposalSubmission {X Y : Type*} (state : FalsifyState X Y)
    (proposal : ProposedUpdate X Y) : Submission X Y :=
  { current := state.current
    group := proposal.group
    replacement := proposal.replacement }

/-- One transition of Algorithm 3. -/
def falsifyAndUpdateStep {X Y : Type*} {n : ℕ}
    (epsilon : ℝ) (loss : BoundedLoss Y) (sample : Fin n → X × Y)
    (state : FalsifyState X Y) (proposal : ProposedUpdate X Y) :
    FalsifyState X Y :=
  let decision := certificateCheckerDecision epsilon loss sample
    (proposalSubmission state proposal)
  match decision with
  | .rejected =>
      { state with reverseTranscript := decision :: state.reverseTranscript }
  | .accepted =>
      { current := listUpdate state.current proposal.group proposal.replacement
        accepted := state.accepted + 1
        reverseTranscript := decision :: state.reverseTranscript }

/-- Algorithm 3 on one realized (possibly adaptively generated) proposal list. -/
def falsifyAndUpdateRun {X Y : Type*} {n : ℕ}
    (epsilon : ℝ) (loss : BoundedLoss Y) (sample : Fin n → X × Y) :
    FalsifyState X Y → List (ProposedUpdate X Y) → FalsifyState X Y
  | state, [] => state
  | state, proposal :: rest =>
      falsifyAndUpdateRun epsilon loss sample
        (falsifyAndUpdateStep epsilon loss sample state proposal) rest

/-! ## Literal transcript-adaptive Algorithm 3 semantics -/

/-- A submitter may choose the next proposed `(group, replacement)` from the
entire public accept/reject transcript. -/
abbrev AdaptiveProposalStrategy (X Y : Type*) :=
  List CertificateDecision → ProposedUpdate X Y

/-- State transition when the checker decision is supplied explicitly.  This
is used to replay a public transcript without consulting the private holdout. -/
def falsifyStepFromDecision {X Y : Type*}
    (state : FalsifyState X Y) (proposal : ProposedUpdate X Y)
    (decision : CertificateDecision) : FalsifyState X Y :=
  match decision with
  | .rejected =>
      { state with reverseTranscript := decision :: state.reverseTranscript }
  | .accepted =>
      { current := listUpdate state.current proposal.group proposal.replacement
        accepted := state.accepted + 1
        reverseTranscript := decision :: state.reverseTranscript }

/-- The executable holdout transition is the explicit-decision transition at
the decision actually returned by Algorithm 2. -/
theorem falsifyAndUpdateStep_eq_fromDecision {X Y : Type*} {n : ℕ}
    (epsilon : ℝ) (loss : BoundedLoss Y) (sample : Fin n → X × Y)
    (state : FalsifyState X Y) (proposal : ProposedUpdate X Y) :
    falsifyAndUpdateStep epsilon loss sample state proposal =
      falsifyStepFromDecision state proposal
        (certificateCheckerDecision epsilon loss sample
          (proposalSubmission state proposal)) := by
  unfold falsifyAndUpdateStep
  cases certificateCheckerDecision epsilon loss sample
      (proposalSubmission state proposal) <;> rfl

/-- Replay a chronological public transcript from a supplied Algorithm 3
state.  The strategy sees only the already-consumed prefix. -/
def falsifyReplayAux {X Y : Type*} (strategy : AdaptiveProposalStrategy X Y) :
    FalsifyState X Y → List CertificateDecision → FalsifyState X Y
  | state, [] => state
  | state, decision :: rest =>
      let proposal := strategy state.reverseTranscript.reverse
      falsifyReplayAux strategy
        (falsifyStepFromDecision state proposal decision) rest

/-- Public state determined by an initial model, a proposal strategy, and a
public transcript. -/
def falsifyStateFromTranscript {X Y : Type*} (initial : Model X Y)
    (strategy : AdaptiveProposalStrategy X Y)
    (transcript : List CertificateDecision) : FalsifyState X Y :=
  falsifyReplayAux strategy (initialFalsifyState initial) transcript

/-- Replaying two consecutive transcript pieces is associative. -/
theorem falsifyReplayAux_append {X Y : Type*}
    (strategy : AdaptiveProposalStrategy X Y)
    (state : FalsifyState X Y) (first second : List CertificateDecision) :
    falsifyReplayAux strategy state (first ++ second) =
      falsifyReplayAux strategy (falsifyReplayAux strategy state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons decision rest ih =>
      simp only [List.cons_append, falsifyReplayAux]
      exact ih _

/-- Replay records exactly the decisions it consumed, newest first. -/
theorem falsifyReplayAux_reverseTranscript {X Y : Type*}
    (strategy : AdaptiveProposalStrategy X Y)
    (state : FalsifyState X Y) (transcript : List CertificateDecision) :
    (falsifyReplayAux strategy state transcript).reverseTranscript =
      transcript.reverse ++ state.reverseTranscript := by
  induction transcript generalizing state with
  | nil => simp [falsifyReplayAux]
  | cons decision rest ih =>
      simp only [falsifyReplayAux]
      rw [ih]
      rw [List.reverse_cons, List.append_assoc]
      congr 1
      cases decision <;> rfl

/-- Starting from the empty transcript, replay exposes exactly its input as
the public chronological transcript. -/
@[simp] theorem falsifyStateFromTranscript_publicTranscript {X Y : Type*}
    (initial : Model X Y) (strategy : AdaptiveProposalStrategy X Y)
    (transcript : List CertificateDecision) :
    (falsifyStateFromTranscript initial strategy transcript).reverseTranscript.reverse =
      transcript := by
  rw [falsifyStateFromTranscript, falsifyReplayAux_reverseTranscript]
  simp [initialFalsifyState]

/-- Replaying one further public decision performs exactly one explicit
Algorithm 3 transition at the proposal selected from the old transcript. -/
theorem falsifyStateFromTranscript_append_singleton {X Y : Type*}
    (initial : Model X Y) (strategy : AdaptiveProposalStrategy X Y)
    (transcript : List CertificateDecision) (decision : CertificateDecision) :
    falsifyStateFromTranscript initial strategy (transcript ++ [decision]) =
      falsifyStepFromDecision
        (falsifyStateFromTranscript initial strategy transcript)
        (strategy transcript) decision := by
  rw [falsifyStateFromTranscript, falsifyReplayAux_append]
  simp only [falsifyReplayAux]
  change falsifyStepFromDecision
      (falsifyStateFromTranscript initial strategy transcript)
      (strategy
        (falsifyStateFromTranscript initial strategy transcript).reverseTranscript.reverse)
      decision = _
  rw [falsifyStateFromTranscript_publicTranscript]

/-- Replay's accepted counter is the literal number of accepted public
decisions, plus the counter already present in its starting state. -/
theorem falsifyReplayAux_accepted {X Y : Type*}
    (strategy : AdaptiveProposalStrategy X Y)
    (state : FalsifyState X Y) (transcript : List CertificateDecision) :
    (falsifyReplayAux strategy state transcript).accepted =
      state.accepted + numberAccepted transcript := by
  induction transcript generalizing state with
  | nil => simp [falsifyReplayAux, numberAccepted]
  | cons decision rest ih =>
      simp only [falsifyReplayAux]
      rw [ih]
      cases decision <;>
        simp [falsifyStepFromDecision, numberAccepted, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm]

/-- The replayed state counts exactly the accepted decisions in its public
transcript. -/
@[simp] theorem falsifyStateFromTranscript_accepted {X Y : Type*}
    (initial : Model X Y) (strategy : AdaptiveProposalStrategy X Y)
    (transcript : List CertificateDecision) :
    (falsifyStateFromTranscript initial strategy transcript).accepted =
      numberAccepted transcript := by
  simp [falsifyStateFromTranscript, falsifyReplayAux_accepted,
    initialFalsifyState]

/-- The Algorithm 2 submission stream induced by Algorithm 3.  The current
model is reconstructed solely from the public transcript, which is the key
description-length observation in the proof of Theorem 12. -/
def falsifySubmissionStrategy {X Y : Type*} (initial : Model X Y)
    (strategy : AdaptiveProposalStrategy X Y) :
    AdaptiveSubmissionStrategy X Y :=
  fun transcript => proposalSubmission
    (falsifyStateFromTranscript initial strategy transcript)
    (strategy transcript)

/-- Literal adaptive Algorithm 3 transcript: run Algorithm 2 on the induced
submission stream. -/
def adaptiveFalsifyTranscript {X Y : Type*} {n : ℕ}
    (epsilon : ℝ) (loss : BoundedLoss Y) (sample : Fin n → X × Y)
    (U : ℕ) (initial : Model X Y) (strategy : AdaptiveProposalStrategy X Y) :
    List CertificateDecision :=
  certificateCheckerRun epsilon loss sample U
    (falsifySubmissionStrategy initial strategy)

/-- Literal adaptive Algorithm 3 output state. -/
def adaptiveFalsifyAndUpdate {X Y : Type*} {n : ℕ}
    (epsilon : ℝ) (loss : BoundedLoss Y) (sample : Fin n → X × Y)
    (U : ℕ) (initial : Model X Y) (strategy : AdaptiveProposalStrategy X Y) :
    FalsifyState X Y :=
  falsifyStateFromTranscript initial strategy
    (adaptiveFalsifyTranscript epsilon loss sample U initial strategy)

/-- Checker accuracy at one reached Algorithm 3 state. -/
def FalsifyStepAccurate {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y) (epsilon : ℝ)
    {n : ℕ} (sample : Fin n → X × Y)
    (state : FalsifyState X Y) (proposal : ProposedUpdate X Y) : Prop :=
  |empiricalSubmissionScore loss sample (proposalSubmission state proposal) -
    certificateImprovementScore law loss state.current proposal.group
      proposal.replacement| ≤ epsilon / 4

/-- The good-event predicate along the entire realized Algorithm 3 run. -/
def AccurateFalsifyRun {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y) (epsilon : ℝ)
    {n : ℕ} (sample : Fin n → X × Y) :
    FalsifyState X Y → List (ProposedUpdate X Y) → Prop
  | _, [] => True
  | state, proposal :: rest =>
      FalsifyStepAccurate law loss epsilon sample state proposal ∧
        AccurateFalsifyRun law loss epsilon sample
          (falsifyAndUpdateStep epsilon loss sample state proposal) rest

/-- Source conclusions attached to one Algorithm 3 transition. -/
def FalsifyStepGuarantee {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y) (epsilon : ℝ)
    {n : ℕ} (sample : Fin n → X × Y)
    (state : FalsifyState X Y) (proposal : ProposedUpdate X Y) : Prop :=
  let submission := proposalSubmission state proposal
  let decision := certificateCheckerDecision epsilon loss sample submission
  let next := falsifyAndUpdateStep epsilon loss sample state proposal
  (decision = .rejected →
      ∀ mu Delta, epsilon ≤ mu * Delta →
        ¬ CertificateOfSuboptimality law loss state.current proposal.group
          proposal.replacement mu Delta) ∧
    (decision = .accepted →
      ∃ mu Delta,
        CertificateOfSuboptimality law loss state.current proposal.group
          proposal.replacement mu Delta ∧
        epsilon / 2 ≤ mu * Delta ∧
        groupLoss law loss next.current proposal.group =
          groupLoss law loss proposal.replacement proposal.group ∧
        modelLoss law loss next.current ≤
          modelLoss law loss state.current - epsilon / 2)

/-- Theorem 12's accept/reject/update conclusions for one reached step. -/
theorem theorem12_falsifyAndUpdate_step
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    {n : ℕ} (sample : Fin n → X × Y)
    (state : FalsifyState X Y) (proposal : ProposedUpdate X Y)
    (haccurate : FalsifyStepAccurate law loss epsilon sample state proposal) :
    FalsifyStepGuarantee law loss epsilon sample state proposal := by
  unfold FalsifyStepGuarantee
  dsimp only
  constructor
  · intro hrejected mu Delta hlarge
    exact certificateChecker_rejected_sound haccurate hrejected mu Delta hlarge
  · intro haccepted
    obtain ⟨mu, Delta, hcert, hlarge⟩ :=
      certificateChecker_accepted_complete hepsilon haccurate haccepted
    have hcert' : CertificateOfSuboptimality law loss state.current
        proposal.group proposal.replacement mu Delta := by
      simpa [proposalSubmission] using hcert
    refine ⟨mu, Delta, hcert', hlarge, ?_, ?_⟩
    · simp [falsifyAndUpdateStep, haccepted, listUpdate_groupLoss_eq]
    · have hprogress := (theorem9_listUpdate_progress hcert').2
      have htarget :
          modelLoss law loss
              (listUpdate state.current proposal.group proposal.replacement) ≤
            modelLoss law loss state.current - epsilon / 2 := by
        exact le_trans hprogress (by linarith)
      simpa [falsifyAndUpdateStep, haccepted] using htarget

/-- Theorem 12's local conclusions when the public decision is supplied
explicitly.  This is the form used by transcript replay. -/
def FalsifyDecisionGuarantee {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y) (epsilon : ℝ)
    (state : FalsifyState X Y) (proposal : ProposedUpdate X Y)
    (decision : CertificateDecision) : Prop :=
  let next := falsifyStepFromDecision state proposal decision
  (decision = .rejected →
      ∀ mu Delta, epsilon ≤ mu * Delta →
        ¬ CertificateOfSuboptimality law loss state.current proposal.group
          proposal.replacement mu Delta) ∧
    (decision = .accepted →
      ∃ mu Delta,
        CertificateOfSuboptimality law loss state.current proposal.group
          proposal.replacement mu Delta ∧
        epsilon / 2 ≤ mu * Delta ∧
        groupLoss law loss next.current proposal.group =
          groupLoss law loss proposal.replacement proposal.group ∧
        modelLoss law loss next.current ≤
          modelLoss law loss state.current - epsilon / 2)

/-- Algorithm 2's population semantics, plus ListUpdate, imply all local
Algorithm 3 conclusions. -/
theorem falsifyDecisionGuarantee_of_checkerDecisionGuaranteed
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (state : FalsifyState X Y)
    (proposal : ProposedUpdate X Y) (decision : CertificateDecision)
    (hchecker : CheckerDecisionGuaranteed law loss epsilon
      (proposalSubmission state proposal) decision) :
    FalsifyDecisionGuarantee law loss epsilon state proposal decision := by
  unfold FalsifyDecisionGuarantee
  dsimp only
  constructor
  · intro hrejected mu Delta hlarge
    simpa [proposalSubmission] using hchecker.1 hrejected mu Delta hlarge
  · intro haccepted
    obtain ⟨mu, Delta, hcert, hlarge⟩ := hchecker.2 haccepted
    have hcert' : CertificateOfSuboptimality law loss state.current
        proposal.group proposal.replacement mu Delta := by
      simpa [proposalSubmission] using hcert
    refine ⟨mu, Delta, hcert', hlarge, ?_, ?_⟩
    · simp [falsifyStepFromDecision, haccepted, listUpdate_groupLoss_eq]
    · have hprogress := (theorem9_listUpdate_progress hcert').2
      have htarget :
          modelLoss law loss
              (listUpdate state.current proposal.group proposal.replacement) ≤
            modelLoss law loss state.current - epsilon / 2 :=
        hprogress.trans (by linarith)
      simpa [falsifyStepFromDecision, haccepted] using htarget

/-- A locally guaranteed decision cannot increase population loss plus the
accepted-update potential. -/
theorem falsifyStepFromDecision_potential_le
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (state : FalsifyState X Y)
    (proposal : ProposedUpdate X Y) (decision : CertificateDecision)
    (hguarantee : FalsifyDecisionGuarantee law loss epsilon state proposal decision) :
    let next := falsifyStepFromDecision state proposal decision
    modelLoss law loss next.current + (next.accepted : ℝ) * (epsilon / 2) ≤
      modelLoss law loss state.current + (state.accepted : ℝ) * (epsilon / 2) := by
  dsimp only
  cases decision with
  | rejected =>
      simp [falsifyStepFromDecision]
  | accepted =>
      obtain ⟨mu, Delta, _, _, _, hloss⟩ := hguarantee.2 rfl
      simp only [falsifyStepFromDecision] at hloss ⊢
      push_cast
      nlinarith

/-- Every realized step enjoys Theorem 12's local guarantee. -/
def AllFalsifyStepsGuaranteed {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y) (epsilon : ℝ)
    {n : ℕ} (sample : Fin n → X × Y) :
    FalsifyState X Y → List (ProposedUpdate X Y) → Prop
  | _, [] => True
  | state, proposal :: rest =>
      FalsifyStepGuarantee law loss epsilon sample state proposal ∧
        AllFalsifyStepsGuaranteed law loss epsilon sample
          (falsifyAndUpdateStep epsilon loss sample state proposal) rest

/-- Accuracy along a run implies all per-submission conclusions. -/
theorem allFalsifyStepsGuaranteed_of_accurate
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    {n : ℕ} (sample : Fin n → X × Y)
    (state : FalsifyState X Y) (proposals : List (ProposedUpdate X Y))
    (haccurate : AccurateFalsifyRun law loss epsilon sample state proposals) :
    AllFalsifyStepsGuaranteed law loss epsilon sample state proposals := by
  induction proposals generalizing state with
  | nil => trivial
  | cons proposal rest ih =>
      exact ⟨theorem12_falsifyAndUpdate_step law loss epsilon hepsilon sample
          state proposal haccurate.1,
        ih _ haccurate.2⟩

/-- One accurate step cannot increase loss plus accepted-count potential. -/
theorem falsifyAndUpdateStep_potential_le
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    {n : ℕ} (sample : Fin n → X × Y)
    (state : FalsifyState X Y) (proposal : ProposedUpdate X Y)
    (haccurate : FalsifyStepAccurate law loss epsilon sample state proposal) :
    let next := falsifyAndUpdateStep epsilon loss sample state proposal
    modelLoss law loss next.current + (next.accepted : ℝ) * (epsilon / 2) ≤
      modelLoss law loss state.current + (state.accepted : ℝ) * (epsilon / 2) := by
  dsimp only
  have hstep := theorem12_falsifyAndUpdate_step law loss epsilon hepsilon sample
    state proposal haccurate
  unfold FalsifyStepGuarantee at hstep
  dsimp only at hstep
  cases hdecision : certificateCheckerDecision epsilon loss sample
      (proposalSubmission state proposal) with
  | rejected =>
      simp [falsifyAndUpdateStep, hdecision]
  | accepted =>
      obtain ⟨mu, Delta, _, _, _, hloss⟩ := hstep.2 hdecision
      have hcount :
          ((falsifyAndUpdateStep epsilon loss sample state proposal).accepted : ℝ) =
            (state.accepted : ℝ) + 1 := by
        simp [falsifyAndUpdateStep, hdecision]
      rw [hcount]
      nlinarith

/-- The Algorithm 3 potential is nonincreasing over an accurate run. -/
theorem falsifyAndUpdateRun_potential_le
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    {n : ℕ} (sample : Fin n → X × Y)
    (state : FalsifyState X Y) (proposals : List (ProposedUpdate X Y))
    (haccurate : AccurateFalsifyRun law loss epsilon sample state proposals) :
    let final := falsifyAndUpdateRun epsilon loss sample state proposals
    modelLoss law loss final.current + (final.accepted : ℝ) * (epsilon / 2) ≤
      modelLoss law loss state.current + (state.accepted : ℝ) * (epsilon / 2) := by
  induction proposals generalizing state with
  | nil => simp [falsifyAndUpdateRun]
  | cons proposal rest ih =>
      let next := falsifyAndUpdateStep epsilon loss sample state proposal
      let final := falsifyAndUpdateRun epsilon loss sample next rest
      have hone := falsifyAndUpdateStep_potential_le law loss epsilon hepsilon sample
        state proposal haccurate.1
      have htail := ih next haccurate.2
      exact le_trans htail hone

/-- Theorem 12's accepted-update and no-early-halt budget. -/
theorem theorem12_falsifyAndUpdate_run
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    {n : ℕ} (sample : Fin n → X × Y)
    (initial : Model X Y) (proposals : List (ProposedUpdate X Y))
    (haccurate : AccurateFalsifyRun law loss epsilon sample
      (initialFalsifyState initial) proposals) :
    AllFalsifyStepsGuaranteed law loss epsilon sample
        (initialFalsifyState initial) proposals ∧
      let final := falsifyAndUpdateRun epsilon loss sample
        (initialFalsifyState initial) proposals
      (final.accepted : ℝ) ≤ 2 / epsilon := by
  refine ⟨allFalsifyStepsGuaranteed_of_accurate law loss epsilon hepsilon sample
    _ _ haccurate, ?_⟩
  let final := falsifyAndUpdateRun epsilon loss sample
    (initialFalsifyState initial) proposals
  have hpotential := falsifyAndUpdateRun_potential_le law loss epsilon hepsilon
    sample (initialFalsifyState initial) proposals haccurate
  have hfinal_nonneg := modelLoss_nonneg law loss final.current
  have hinitial_one := modelLoss_le_one law loss initial
  have hpotential' : modelLoss law loss final.current +
      (final.accepted : ℝ) * (epsilon / 2) ≤ modelLoss law loss initial := by
    simpa [final, initialFalsifyState] using hpotential
  have hmul : (final.accepted : ℝ) * epsilon ≤ 2 := by
    nlinarith [hpotential']
  exact (le_div_iff₀ hepsilon).2 hmul

/-! ## Complete adaptive and high-probability Theorem 12 -/

/-- All local source guarantees along the literal Algorithm 3/Algorithm 2
execution, indexed by the checker's private newest-first accumulator. -/
def AdaptiveFalsifyRunAuxGuaranteed {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y) (epsilon : ℝ)
    {n : ℕ} (sample : Fin n → X × Y) (initial : Model X Y)
    (strategy : AdaptiveProposalStrategy X Y) :
    ℕ → List CertificateDecision → Prop
  | 0, _ => True
  | remaining + 1, reverseTranscript =>
      if (numberAccepted reverseTranscript : ℝ) ≤ 2 / epsilon then
        let publicTranscript := reverseTranscript.reverse
        let state := falsifyStateFromTranscript initial strategy publicTranscript
        let proposal := strategy publicTranscript
        let decision := certificateCheckerDecision epsilon loss sample
          (proposalSubmission state proposal)
        FalsifyDecisionGuarantee law loss epsilon state proposal decision ∧
          AdaptiveFalsifyRunAuxGuaranteed law loss epsilon sample initial strategy
            remaining (decision :: reverseTranscript)
      else
        True

/-- The complete deterministic good-run predicate for adaptive Algorithm 3. -/
def AdaptiveFalsifyRunGuaranteed {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y) (epsilon : ℝ)
    {n : ℕ} (sample : Fin n → X × Y) (U : ℕ) (initial : Model X Y)
    (strategy : AdaptiveProposalStrategy X Y) : Prop :=
  AdaptiveFalsifyRunAuxGuaranteed law loss epsilon sample initial strategy U []

/-- Algorithm 2's actual-run guarantee transfers to every actual Algorithm 3
decision, including the ListUpdate conclusions. -/
theorem adaptiveFalsifyRunAuxGuaranteed_of_checkerRunAuxGuaranteed
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y) (epsilon : ℝ)
    {n : ℕ} (sample : Fin n → X × Y) (initial : Model X Y)
    (strategy : AdaptiveProposalStrategy X Y) :
    ∀ (remaining : ℕ) (reverseTranscript : List CertificateDecision),
      CheckerRunAuxGuaranteed law loss epsilon sample
          (falsifySubmissionStrategy initial strategy)
          remaining reverseTranscript →
        AdaptiveFalsifyRunAuxGuaranteed law loss epsilon sample initial strategy
          remaining reverseTranscript := by
  intro remaining
  induction remaining with
  | zero =>
      intro reverseTranscript _
      trivial
  | succ remaining ih =>
      intro reverseTranscript hchecker
      by_cases hguard :
          (numberAccepted reverseTranscript : ℝ) ≤ 2 / epsilon
      · simp only [CheckerRunAuxGuaranteed, AdaptiveFalsifyRunAuxGuaranteed,
          hguard, if_pos] at hchecker ⊢
        let publicTranscript := reverseTranscript.reverse
        let state := falsifyStateFromTranscript initial strategy publicTranscript
        let proposal := strategy publicTranscript
        let decision := certificateCheckerDecision epsilon loss sample
          (proposalSubmission state proposal)
        have hcheckerLocal : CheckerDecisionGuaranteed law loss epsilon
            (proposalSubmission state proposal) decision := by
          simpa [falsifySubmissionStrategy, publicTranscript, state, proposal,
            decision] using hchecker.1
        refine ⟨falsifyDecisionGuarantee_of_checkerDecisionGuaranteed
            law loss epsilon state proposal decision hcheckerLocal, ?_⟩
        exact ih _ hchecker.2
      · simp [CheckerRunAuxGuaranteed, AdaptiveFalsifyRunAuxGuaranteed, hguard]

/-- Along every good actual run, the replayed population-loss potential never
increases, even if the literal checker guard stops the run. -/
theorem adaptiveFalsifyRunAux_potential_le
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y) (epsilon : ℝ)
    {n : ℕ} (sample : Fin n → X × Y) (initial : Model X Y)
    (strategy : AdaptiveProposalStrategy X Y) :
    ∀ (remaining : ℕ) (reverseTranscript : List CertificateDecision),
      AdaptiveFalsifyRunAuxGuaranteed law loss epsilon sample initial strategy
          remaining reverseTranscript →
      let start := falsifyStateFromTranscript initial strategy
        reverseTranscript.reverse
      let finalTranscript := certificateCheckerRunAux epsilon loss sample
        (falsifySubmissionStrategy initial strategy) remaining reverseTranscript
      let final := falsifyStateFromTranscript initial strategy finalTranscript
      falsifyPotential law loss epsilon final ≤
        falsifyPotential law loss epsilon start := by
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
        let state := falsifyStateFromTranscript initial strategy publicTranscript
        let proposal := strategy publicTranscript
        let decision := certificateCheckerDecision epsilon loss sample
          (proposalSubmission state proposal)
        have hparts :
            FalsifyDecisionGuarantee law loss epsilon state proposal decision ∧
              AdaptiveFalsifyRunAuxGuaranteed law loss epsilon sample initial strategy
                remaining (decision :: reverseTranscript) := by
          simpa [AdaptiveFalsifyRunAuxGuaranteed, hguard, publicTranscript,
            state, proposal, decision] using hguaranteed
        have hstep : falsifyPotential law loss epsilon
              (falsifyStepFromDecision state proposal decision) ≤
            falsifyPotential law loss epsilon state := by
          simpa [falsifyPotential] using
            (falsifyStepFromDecision_potential_le law loss epsilon state proposal
              decision hparts.1)
        have hnextState :
            falsifyStateFromTranscript initial strategy
                (decision :: reverseTranscript).reverse =
              falsifyStepFromDecision state proposal decision := by
          simp only [List.reverse_cons]
          simpa [state, proposal, publicTranscript] using
            (falsifyStateFromTranscript_append_singleton initial strategy
              publicTranscript decision)
        have htail := ih (decision :: reverseTranscript) hparts.2
        have hstep' : falsifyPotential law loss epsilon
              (falsifyStateFromTranscript initial strategy
                (decision :: reverseTranscript).reverse) ≤
            falsifyPotential law loss epsilon
              (falsifyStateFromTranscript initial strategy reverseTranscript.reverse) := by
          rw [hnextState]
          simpa [state, publicTranscript] using hstep
        simp only [certificateCheckerRunAux, hguard, if_pos]
        exact htail.trans hstep'
      · simp [certificateCheckerRunAux, hguard]

/-- Under the good-run guarantees, the population-loss budget forces the
literal checker guard to remain open.  Hence every one of the requested
`remaining` submissions is processed. -/
theorem adaptiveFalsifyRunAux_length_eq
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    {n : ℕ} (sample : Fin n → X × Y) (initial : Model X Y)
    (strategy : AdaptiveProposalStrategy X Y) :
    ∀ (remaining : ℕ) (reverseTranscript : List CertificateDecision),
      AdaptiveFalsifyRunAuxGuaranteed law loss epsilon sample initial strategy
          remaining reverseTranscript →
      falsifyPotential law loss epsilon
          (falsifyStateFromTranscript initial strategy reverseTranscript.reverse) ≤
        modelLoss law loss initial →
      (certificateCheckerRunAux epsilon loss sample
          (falsifySubmissionStrategy initial strategy)
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
      let state := falsifyStateFromTranscript initial strategy publicTranscript
      have hstateAccepted : state.accepted = numberAccepted reverseTranscript := by
        dsimp [state, publicTranscript]
        rw [falsifyStateFromTranscript_accepted, numberAccepted_reverse]
      have hstateNonneg : 0 ≤ modelLoss law loss state.current :=
        modelLoss_nonneg law loss state.current
      have hinitialOne : modelLoss law loss initial ≤ 1 :=
        modelLoss_le_one law loss initial
      have hacceptedMul : (state.accepted : ℝ) * epsilon ≤ 2 := by
        unfold falsifyPotential at hpotential
        nlinarith
      have hguard : (numberAccepted reverseTranscript : ℝ) ≤ 2 / epsilon := by
        apply (le_div_iff₀ hepsilon).2
        simpa [hstateAccepted] using hacceptedMul
      let proposal := strategy publicTranscript
      let decision := certificateCheckerDecision epsilon loss sample
        (proposalSubmission state proposal)
      have hparts :
          FalsifyDecisionGuarantee law loss epsilon state proposal decision ∧
            AdaptiveFalsifyRunAuxGuaranteed law loss epsilon sample initial strategy
              remaining (decision :: reverseTranscript) := by
        simpa [AdaptiveFalsifyRunAuxGuaranteed, hguard, publicTranscript,
          state, proposal, decision] using hguaranteed
      have hstep : falsifyPotential law loss epsilon
            (falsifyStepFromDecision state proposal decision) ≤
          falsifyPotential law loss epsilon state := by
        simpa [falsifyPotential] using
          (falsifyStepFromDecision_potential_le law loss epsilon state proposal
            decision hparts.1)
      have hnextState :
          falsifyStateFromTranscript initial strategy
              (decision :: reverseTranscript).reverse =
            falsifyStepFromDecision state proposal decision := by
        simp only [List.reverse_cons]
        simpa [state, proposal, publicTranscript] using
          (falsifyStateFromTranscript_append_singleton initial strategy
            publicTranscript decision)
      have hnextPotential :
          falsifyPotential law loss epsilon
              (falsifyStateFromTranscript initial strategy
                (decision :: reverseTranscript).reverse) ≤
            modelLoss law loss initial := by
        rw [hnextState]
        exact hstep.trans (by simpa [state, publicTranscript] using hpotential)
      have htail := ih (decision :: reverseTranscript) hparts.2 hnextPotential
      simp only [certificateCheckerRunAux, hguard, if_pos]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

/-- Good Algorithm 3 executions process the full requested horizon. -/
theorem adaptiveFalsifyTranscript_length_eq
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    {n : ℕ} (sample : Fin n → X × Y) (U : ℕ)
    (initial : Model X Y) (strategy : AdaptiveProposalStrategy X Y)
    (hguaranteed : AdaptiveFalsifyRunGuaranteed law loss epsilon sample U
      initial strategy) :
    (adaptiveFalsifyTranscript epsilon loss sample U initial strategy).length = U := by
  have hpotential : falsifyPotential law loss epsilon
      (falsifyStateFromTranscript initial strategy [].reverse) ≤
      modelLoss law loss initial := by
    simp [falsifyPotential, falsifyStateFromTranscript, falsifyReplayAux,
      initialFalsifyState]
  have hlength := adaptiveFalsifyRunAux_length_eq law loss epsilon hepsilon
    sample initial strategy U [] hguaranteed hpotential
  simpa [adaptiveFalsifyTranscript, certificateCheckerRun] using hlength

/-- A good adaptive Algorithm 3 execution accepts at most `2 / epsilon`
updates. -/
theorem adaptiveFalsifyAndUpdate_accepted_le
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    {n : ℕ} (sample : Fin n → X × Y) (U : ℕ)
    (initial : Model X Y) (strategy : AdaptiveProposalStrategy X Y)
    (hguaranteed : AdaptiveFalsifyRunGuaranteed law loss epsilon sample U
      initial strategy) :
    ((adaptiveFalsifyAndUpdate epsilon loss sample U initial strategy).accepted : ℝ) ≤
      2 / epsilon := by
  have hpotential := adaptiveFalsifyRunAux_potential_le law loss epsilon sample
    initial strategy U [] hguaranteed
  have hfinalNonneg : 0 ≤ modelLoss law loss
      (adaptiveFalsifyAndUpdate epsilon loss sample U initial strategy).current :=
    modelLoss_nonneg law loss _
  have hinitialOne : modelLoss law loss initial ≤ 1 :=
    modelLoss_le_one law loss initial
  have hpotential' : falsifyPotential law loss epsilon
      (adaptiveFalsifyAndUpdate epsilon loss sample U initial strategy) ≤
      modelLoss law loss initial := by
    simpa [adaptiveFalsifyAndUpdate, adaptiveFalsifyTranscript,
      certificateCheckerRun, falsifyPotential, falsifyStateFromTranscript,
      falsifyReplayAux, initialFalsifyState] using hpotential
  have hmul :
      ((adaptiveFalsifyAndUpdate epsilon loss sample U initial strategy).accepted : ℝ) *
        epsilon ≤ 2 := by
    unfold falsifyPotential at hpotential'
    nlinarith
  exact (le_div_iff₀ hepsilon).2 hmul

/-- The three advertised parts of Theorem 12: every issued decision has the
local source semantics, the checker processes all `U` submissions, and no more
than `2 / epsilon` updates are accepted. -/
def AdaptiveFalsifyRunConclusion {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y) (epsilon : ℝ)
    {n : ℕ} (sample : Fin n → X × Y) (U : ℕ) (initial : Model X Y)
    (strategy : AdaptiveProposalStrategy X Y) : Prop :=
  AdaptiveFalsifyRunGuaranteed law loss epsilon sample U initial strategy ∧
    (adaptiveFalsifyTranscript epsilon loss sample U initial strategy).length = U ∧
    ((adaptiveFalsifyAndUpdate epsilon loss sample U initial strategy).accepted : ℝ) ≤
      2 / epsilon

/-- Theorem 11's actual adaptive checker event implies the complete Theorem 12
conclusion for the induced FalsifyAndUpdate execution. -/
theorem adaptiveFalsifyRunConclusion_of_checkerRunGuaranteed
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    {n : ℕ} (sample : Fin n → X × Y) (U : ℕ)
    (initial : Model X Y) (strategy : AdaptiveProposalStrategy X Y)
    (hchecker : CheckerRunAuxGuaranteed law loss epsilon sample
      (falsifySubmissionStrategy initial strategy) U []) :
    AdaptiveFalsifyRunConclusion law loss epsilon sample U initial strategy := by
  have hrun : AdaptiveFalsifyRunGuaranteed law loss epsilon sample U initial strategy :=
    adaptiveFalsifyRunAuxGuaranteed_of_checkerRunAuxGuaranteed law loss epsilon
      sample initial strategy U [] hchecker
  exact ⟨hrun,
    adaptiveFalsifyTranscript_length_eq law loss epsilon hepsilon sample U initial
      strategy hrun,
    adaptiveFalsifyAndUpdate_accepted_le law loss epsilon hepsilon sample U initial
      strategy hrun⟩

/-- Probability that literal adaptive Algorithm 3 violates any conclusion of
Theorem 12. -/
noncomputable def adaptiveFalsifyAndUpdateFailure
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (n U : ℕ) (initial : Model X Y)
    (strategy : AdaptiveProposalStrategy X Y) : ℝ := by
  classical
  exact pmfProb (pmfProduct (Fin n) (X × Y) law) (fun sample =>
    ¬ AdaptiveFalsifyRunConclusion law loss epsilon sample U initial strategy)

/-- A bad Algorithm 3 execution is a bad execution of its induced Algorithm 2
checker stream. -/
theorem adaptiveFalsifyAndUpdateFailure_le_checkerFailure
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (n U : ℕ)
    (initial : Model X Y) (strategy : AdaptiveProposalStrategy X Y) :
    adaptiveFalsifyAndUpdateFailure law loss epsilon n U initial strategy ≤
      certificateCheckerRunGuaranteeFailure law loss epsilon n U
        (falsifySubmissionStrategy initial strategy) := by
  classical
  unfold adaptiveFalsifyAndUpdateFailure certificateCheckerRunGuaranteeFailure
  apply pmfProb_le_of_imp
  intro sample hbad
  intro hchecker
  exact hbad (adaptiveFalsifyRunConclusion_of_checkerRunGuaranteed
    law loss epsilon hepsilon sample U initial strategy hchecker)

/-- Theorem 12 in complete finite-sample form for every transcript-adaptive
proposal process.  This corrects the source's undefined `delta'` by displaying
the exact failure bound inherited from Theorem 11. -/
theorem theorem12_adaptive_falsifyAndUpdate
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (n U : ℕ)
    (hcount : 0 < n) (initial : Model X Y)
    (strategy : AdaptiveProposalStrategy X Y) :
    adaptiveFalsifyAndUpdateFailure law loss epsilon n U initial strategy ≤
      (U * (U + 1) ^ checkerAcceptanceBudget epsilon : ℕ) * 2 *
        Real.exp (-(n : ℝ) * epsilon ^ 2 / 32) := by
  calc
    adaptiveFalsifyAndUpdateFailure law loss epsilon n U initial strategy ≤
        certificateCheckerRunGuaranteeFailure law loss epsilon n U
          (falsifySubmissionStrategy initial strategy) :=
      adaptiveFalsifyAndUpdateFailure_le_checkerFailure law loss epsilon
        hepsilon n U initial strategy
    _ ≤ (U * (U + 1) ^ checkerAcceptanceBudget epsilon : ℕ) * 2 *
          Real.exp (-(n : ℝ) * epsilon ^ 2 / 32) :=
      theorem11_adaptive_certificateCheckerRun law loss epsilon hepsilon n U
        hcount (falsifySubmissionStrategy initial strategy)

/-!
## Algorithm 4: restart-until-closed monotone repair
-/

/-- All repair candidates formed from protected groups and earlier models. -/
def repairCandidates {X Y : Type*} (groups : List (Group X))
    (pastModels : List (Model X Y)) : List (ProposedUpdate X Y) :=
  groups.flatMap fun g => pastModels.map fun f =>
    { group := g, replacement := f }

/-- First repair candidate accepted against the current model, if any. -/
def firstAcceptedRepair {X Y : Type*} {n : ℕ}
    (epsilon : ℝ) (loss : BoundedLoss Y) (sample : Fin n → X × Y)
    (current : Model X Y) (candidates : List (ProposedUpdate X Y)) :
    Option (ProposedUpdate X Y) :=
  candidates.find? fun candidate =>
    certificateCheckerDecision epsilon loss sample
      { current := current, group := candidate.group,
        replacement := candidate.replacement } = .accepted

/--
Corrected Algorithm 4 repair loop.  `some output` means the scan reached
closure; `none` means the supplied fuel was exhausted before closure.
-/
def monotoneRepairLoop {X Y : Type*} {n : ℕ}
    (epsilon : ℝ) (loss : BoundedLoss Y) (sample : Fin n → X × Y)
    (candidates : List (ProposedUpdate X Y)) :
    ℕ → Model X Y → Option (Model X Y)
  | 0, current =>
      match firstAcceptedRepair epsilon loss sample current candidates with
      | none => some current
      | some _ => none
  | fuel + 1, current =>
      match firstAcceptedRepair epsilon loss sample current candidates with
      | none => some current
      | some repair =>
          monotoneRepairLoop epsilon loss sample candidates fuel
            (listUpdate current repair.group repair.replacement)

/-- The final repair scan rejects every protected group/past-model pair. -/
def RepairClosed {X Y : Type*} {n : ℕ}
    (epsilon : ℝ) (loss : BoundedLoss Y) (sample : Fin n → X × Y)
    (current : Model X Y) (candidates : List (ProposedUpdate X Y)) : Prop :=
  ∀ candidate ∈ candidates,
    certificateCheckerDecision epsilon loss sample
      { current := current, group := candidate.group,
        replacement := candidate.replacement } = .rejected

/-- A failed `find?` scan is exactly repair closure. -/
theorem repairClosed_of_firstAcceptedRepair_eq_none
    {X Y : Type*} {n : ℕ}
    (epsilon : ℝ) (loss : BoundedLoss Y) (sample : Fin n → X × Y)
    (current : Model X Y) (candidates : List (ProposedUpdate X Y))
    (hnone : firstAcceptedRepair epsilon loss sample current candidates = none) :
    RepairClosed epsilon loss sample current candidates := by
  intro candidate hmem
  have hfindNone :
      candidates.find? (fun candidate =>
        certificateCheckerDecision epsilon loss sample
          { current := current, group := candidate.group,
            replacement := candidate.replacement } = .accepted) = none := by
    simpa [firstAcceptedRepair] using hnone
  have hnot : ¬ certificateCheckerDecision epsilon loss sample
      { current := current, group := candidate.group,
        replacement := candidate.replacement } = .accepted := by
    have hp := (List.find?_eq_none.mp hfindNone) candidate hmem
    simpa using hp
  cases hdecision : certificateCheckerDecision epsilon loss sample
      { current := current, group := candidate.group,
        replacement := candidate.replacement }
  · rfl
  · exact False.elim (hnot hdecision)

/-- Every successful Algorithm 4 repair-loop result is genuinely closed. -/
theorem monotoneRepairLoop_some_repairClosed
    {X Y : Type*} {n : ℕ}
    (epsilon : ℝ) (loss : BoundedLoss Y) (sample : Fin n → X × Y)
    (candidates : List (ProposedUpdate X Y))
    (fuel : ℕ) (current output : Model X Y)
    (houtput : monotoneRepairLoop epsilon loss sample candidates fuel current =
      some output) :
    RepairClosed epsilon loss sample output candidates := by
  induction fuel generalizing current with
  | zero =>
      unfold monotoneRepairLoop at houtput
      cases hfind : firstAcceptedRepair epsilon loss sample current candidates with
      | none =>
          simp [hfind] at houtput
          subst output
          exact repairClosed_of_firstAcceptedRepair_eq_none epsilon loss sample
            current candidates hfind
      | some repair => simp [hfind] at houtput
  | succ fuel ih =>
      unfold monotoneRepairLoop at houtput
      cases hfind : firstAcceptedRepair epsilon loss sample current candidates with
      | none =>
          simp [hfind] at houtput
          subst output
          exact repairClosed_of_firstAcceptedRepair_eq_none epsilon loss sample
            current candidates hfind
      | some repair =>
          simp only [hfind] at houtput
          exact ih _ houtput

/-- Uniform accuracy for every candidate in the final repair scan. -/
def RepairCandidatesAccurate {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y) (epsilon : ℝ)
    {n : ℕ} (sample : Fin n → X × Y)
    (current : Model X Y) (candidates : List (ProposedUpdate X Y)) : Prop :=
  ∀ candidate ∈ candidates,
    |empiricalSubmissionScore loss sample
        { current := current, group := candidate.group,
          replacement := candidate.replacement } -
      certificateImprovementScore law loss current candidate.group
        candidate.replacement| ≤ epsilon / 4

/-- The holdout event needed for the whole restart-until-closed repair loop.
It is uniform over both the finite repair-candidate list and every model that
can become current.  The adaptive-checker transcript construction is the
source mechanism that supplies this event. -/
def RepairCandidatesUniformlyAccurate {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y) (epsilon : ℝ)
    {n : ℕ} (sample : Fin n → X × Y)
    (candidates : List (ProposedUpdate X Y)) : Prop :=
  ∀ current candidate, candidate ∈ candidates →
    |empiricalSubmissionScore loss sample
        { current := current, group := candidate.group,
          replacement := candidate.replacement } -
      certificateImprovementScore law loss current candidate.group
        candidate.replacement| ≤ epsilon / 4

/-- A selected repair is a member of the scanned candidate list. -/
theorem firstAcceptedRepair_mem
    {X Y : Type*} {n : ℕ}
    (epsilon : ℝ) (loss : BoundedLoss Y) (sample : Fin n → X × Y)
    (current : Model X Y) (candidates : List (ProposedUpdate X Y))
    (repair : ProposedUpdate X Y)
    (hfind : firstAcceptedRepair epsilon loss sample current candidates =
      some repair) :
    repair ∈ candidates := by
  unfold firstAcceptedRepair at hfind
  exact List.mem_of_find?_eq_some hfind

/-- A selected repair was accepted by the checker against the current model. -/
theorem firstAcceptedRepair_accepted
    {X Y : Type*} {n : ℕ}
    (epsilon : ℝ) (loss : BoundedLoss Y) (sample : Fin n → X × Y)
    (current : Model X Y) (candidates : List (ProposedUpdate X Y))
    (repair : ProposedUpdate X Y)
    (hfind : firstAcceptedRepair epsilon loss sample current candidates =
      some repair) :
    certificateCheckerDecision epsilon loss sample
      { current := current, group := repair.group,
        replacement := repair.replacement } = .accepted := by
  unfold firstAcceptedRepair at hfind
  have hselected := List.find?_some hfind
  simpa using hselected

/-- On the uniform checker event, every selected repair lowers population
loss by at least `epsilon / 2`. -/
theorem firstAcceptedRepair_loss_drop
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    {n : ℕ} (sample : Fin n → X × Y)
    (current : Model X Y) (candidates : List (ProposedUpdate X Y))
    (repair : ProposedUpdate X Y)
    (haccurate : RepairCandidatesUniformlyAccurate
      law loss epsilon sample candidates)
    (hfind : firstAcceptedRepair epsilon loss sample current candidates =
      some repair) :
    modelLoss law loss
        (listUpdate current repair.group repair.replacement) ≤
      modelLoss law loss current - epsilon / 2 := by
  have hmem := firstAcceptedRepair_mem epsilon loss sample current candidates
    repair hfind
  have hdecision := firstAcceptedRepair_accepted epsilon loss sample current
    candidates repair hfind
  obtain ⟨mu, Delta, hcert, hlarge⟩ :=
    certificateChecker_accepted_complete hepsilon
      (haccurate current repair hmem) hdecision
  have hprogress := (theorem9_listUpdate_progress hcert).2
  exact hprogress.trans (by linarith)

/-- If the supplied fuel is exhausted, there is a chain of `fuel + 1`
accepted repairs and hence a corresponding population-loss decrease. -/
theorem monotoneRepairLoop_none_loss_budget
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    {n : ℕ} (sample : Fin n → X × Y)
    (candidates : List (ProposedUpdate X Y))
    (haccurate : RepairCandidatesUniformlyAccurate
      law loss epsilon sample candidates)
    (fuel : ℕ) (current : Model X Y)
    (hexhausted : monotoneRepairLoop epsilon loss sample candidates fuel current =
      none) :
    ∃ final : Model X Y,
      modelLoss law loss final ≤
        modelLoss law loss current - ((fuel : ℝ) + 1) * (epsilon / 2) := by
  induction fuel generalizing current with
  | zero =>
      unfold monotoneRepairLoop at hexhausted
      cases hfind : firstAcceptedRepair epsilon loss sample current candidates with
      | none => simp [hfind] at hexhausted
      | some repair =>
          refine ⟨listUpdate current repair.group repair.replacement, ?_⟩
          have hdrop := firstAcceptedRepair_loss_drop law loss epsilon hepsilon
            sample current candidates repair haccurate hfind
          simpa using hdrop
  | succ fuel ih =>
      unfold monotoneRepairLoop at hexhausted
      cases hfind : firstAcceptedRepair epsilon loss sample current candidates with
      | none => simp [hfind] at hexhausted
      | some repair =>
          simp only [hfind] at hexhausted
          obtain ⟨final, htail⟩ := ih
            (listUpdate current repair.group repair.replacement) hexhausted
          have hdrop := firstAcceptedRepair_loss_drop law loss epsilon hepsilon
            sample current candidates repair haccurate hfind
          refine ⟨final, ?_⟩
          calc
            modelLoss law loss final ≤
                modelLoss law loss
                    (listUpdate current repair.group repair.replacement) -
                  ((fuel : ℝ) + 1) * (epsilon / 2) := htail
            _ ≤ (modelLoss law loss current - epsilon / 2) -
                  ((fuel : ℝ) + 1) * (epsilon / 2) :=
              sub_le_sub_right hdrop _
            _ = modelLoss law loss current -
                  (((fuel + 1 : ℕ) : ℝ) + 1) * (epsilon / 2) := by
              push_cast
              ring

/-- Sufficient fuel turns corrected Algorithm 4 into a total terminating
procedure.  The source's `2 / epsilon` loss budget is expressed without a
rounding convention by the exact real inequality below. -/
theorem monotoneRepairLoop_terminates_of_budget
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    {n : ℕ} (sample : Fin n → X × Y)
    (candidates : List (ProposedUpdate X Y))
    (haccurate : RepairCandidatesUniformlyAccurate
      law loss epsilon sample candidates)
    (fuel : ℕ) (hbudget : 1 < ((fuel : ℝ) + 1) * (epsilon / 2))
    (current : Model X Y) :
    ∃ output,
      monotoneRepairLoop epsilon loss sample candidates fuel current = some output := by
  cases hresult : monotoneRepairLoop epsilon loss sample candidates fuel current with
  | some output => exact ⟨output, rfl⟩
  | none =>
      obtain ⟨final, hdrop⟩ := monotoneRepairLoop_none_loss_budget
        law loss epsilon hepsilon sample candidates haccurate fuel current hresult
      have hnonneg := modelLoss_nonneg law loss final
      have hinitial := modelLoss_le_one law loss current
      exfalso
      linarith

/-- Approximate groupwise monotonicity against every protected past model. -/
def ApproxGroupwiseMonotone {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y) (epsilon : ℝ)
    (current : Model X Y) (candidates : List (ProposedUpdate X Y)) : Prop :=
  ∀ candidate ∈ candidates, 0 < groupMass law candidate.group →
    groupLoss law loss current candidate.group ≤
      groupLoss law loss candidate.replacement candidate.group +
        epsilon / groupMass law candidate.group

/--
Theorem 14's new conclusion: closure of the corrected repair loop gives the
displayed `epsilon / groupMass` monotonicity guarantee.
-/
theorem theorem14_repairClosed_groupwiseMonotone
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) {n : ℕ} (sample : Fin n → X × Y)
    (current : Model X Y) (candidates : List (ProposedUpdate X Y))
    (hclosed : RepairClosed epsilon loss sample current candidates)
    (haccurate : RepairCandidatesAccurate law loss epsilon sample current candidates) :
    ApproxGroupwiseMonotone law loss epsilon current candidates := by
  intro candidate hmem hmass
  let submission : Submission X Y :=
    { current := current, group := candidate.group,
      replacement := candidate.replacement }
  have hrejected := hclosed candidate hmem
  have hempirical :=
    (certificateCheckerDecision_eq_rejected_iff epsilon loss sample submission).mp hrejected
  have hpopulation : certificateImprovementScore law loss current
      candidate.group candidate.replacement < epsilon := by
    rcases abs_le.mp (haccurate candidate hmem) with ⟨hlower, hupper⟩
    linarith
  exact (approxBayesOptimal_pair_iff_source law loss epsilon current
    candidate.replacement candidate.group hmass).1 (le_of_lt hpopulation)

/-- Successful Algorithm 4 execution therefore has Theorem 14's guarantee. -/
theorem theorem14_monotoneRepairLoop
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) {n : ℕ} (sample : Fin n → X × Y)
    (candidates : List (ProposedUpdate X Y)) (fuel : ℕ)
    (current output : Model X Y)
    (houtput : monotoneRepairLoop epsilon loss sample candidates fuel current =
      some output)
    (haccurate : RepairCandidatesAccurate law loss epsilon sample output candidates) :
    ApproxGroupwiseMonotone law loss epsilon output candidates := by
  exact theorem14_repairClosed_groupwiseMonotone law loss epsilon sample output
    candidates
    (monotoneRepairLoop_some_repairClosed epsilon loss sample candidates fuel
      current output houtput)
    haccurate

/-- Corrected Theorem 14 with termination included: uniform checker accuracy
and a strict loss-budget fuel bound produce a closed, approximately monotone
output. -/
theorem theorem14_monotoneRepairLoop_total
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    {n : ℕ} (sample : Fin n → X × Y)
    (candidates : List (ProposedUpdate X Y))
    (haccurate : RepairCandidatesUniformlyAccurate
      law loss epsilon sample candidates)
    (fuel : ℕ) (hbudget : 1 < ((fuel : ℝ) + 1) * (epsilon / 2))
    (current : Model X Y) :
    ∃ output,
      monotoneRepairLoop epsilon loss sample candidates fuel current = some output ∧
        ApproxGroupwiseMonotone law loss epsilon output candidates := by
  obtain ⟨output, houtput⟩ := monotoneRepairLoop_terminates_of_budget
    law loss epsilon hepsilon sample candidates haccurate fuel hbudget current
  refine ⟨output, houtput, theorem14_monotoneRepairLoop law loss epsilon sample
    candidates fuel current output houtput ?_⟩
  intro candidate hmem
  exact haccurate output candidate hmem

/-- The source's cubic repair-query accounting, in exact natural arithmetic. -/
theorem repair_query_count_le_cube (updates maxUpdates : ℕ)
    (hupdates : updates ≤ maxUpdates)
    (queriesPerUpdate : ℕ) (hqueries : queriesPerUpdate ≤ maxUpdates ^ 2) :
    updates * queriesPerUpdate ≤ maxUpdates ^ 3 := by
  calc
    updates * queriesPerUpdate ≤ maxUpdates * (maxUpdates ^ 2) :=
      Nat.mul_le_mul hupdates hqueries
    _ = maxUpdates ^ 3 := by ring

/-! ## Complete adaptive repair phase for Algorithm 4 -/

/-- Public state of the corrected restart-until-closed repair phase.  Rejected
candidates from the current scan are stored newest-first. -/
structure AdaptiveRepairState (X Y : Type*) where
  current : Model X Y
  accepted : ℕ
  remaining : List (ProposedUpdate X Y)
  rejectedReverse : List (ProposedUpdate X Y)

/-- Initial state of a repair phase. -/
def initialAdaptiveRepairState {X Y : Type*} (current : Model X Y)
    (candidates : List (ProposedUpdate X Y)) : AdaptiveRepairState X Y :=
  { current := current
    accepted := 0
    remaining := candidates
    rejectedReverse := [] }

/-- A zero-score submission used only after the repair scan has reached
closure.  The executable repair phase itself then has no further meaningful
queries, but a total adaptive strategy is convenient for Algorithm 2. -/
def repairNoopSubmission {X Y : Type*} (current : Model X Y) : Submission X Y :=
  { current := current
    group := fun _ => false
    replacement := current }

/-- Submission at the head of the current repair scan, or the total no-op
submission once the scan is closed. -/
def adaptiveRepairSubmission {X Y : Type*} (state : AdaptiveRepairState X Y) :
    Submission X Y :=
  match state.remaining with
  | [] => repairNoopSubmission state.current
  | candidate :: _ =>
      { current := state.current
        group := candidate.group
        replacement := candidate.replacement }

/-- Replay transition for one public checker decision.  Acceptance restarts
the scan against the updated current model; rejection advances one candidate.
The empty-scan branch only keeps the operational acceptance counter aligned
with an arbitrary supplied transcript.  Actual no-op decisions are proved to
be rejected. -/
def adaptiveRepairStepFromDecision {X Y : Type*}
    (candidates : List (ProposedUpdate X Y)) (state : AdaptiveRepairState X Y)
    (decision : CertificateDecision) : AdaptiveRepairState X Y :=
  match state.remaining with
  | [] =>
      match decision with
      | .rejected => state
      | .accepted => { state with accepted := state.accepted + 1 }
  | candidate :: rest =>
      match decision with
      | .rejected =>
          { state with
            remaining := rest
            rejectedReverse := candidate :: state.rejectedReverse }
      | .accepted =>
          { current := listUpdate state.current candidate.group candidate.replacement
            accepted := state.accepted + 1
            remaining := candidates
            rejectedReverse := [] }

/-- Replay a chronological checker transcript through the corrected repair
state machine. -/
def adaptiveRepairReplayAux {X Y : Type*}
    (candidates : List (ProposedUpdate X Y)) :
    AdaptiveRepairState X Y → List CertificateDecision → AdaptiveRepairState X Y
  | state, [] => state
  | state, decision :: rest =>
      adaptiveRepairReplayAux candidates
        (adaptiveRepairStepFromDecision candidates state decision) rest

/-- Repair state reconstructed solely from the initial model and public
transcript. -/
def adaptiveRepairStateFromTranscript {X Y : Type*}
    (initial : Model X Y) (candidates : List (ProposedUpdate X Y))
    (transcript : List CertificateDecision) : AdaptiveRepairState X Y :=
  adaptiveRepairReplayAux candidates
    (initialAdaptiveRepairState initial candidates) transcript

/-- Replay of consecutive transcript pieces is associative. -/
theorem adaptiveRepairReplayAux_append {X Y : Type*}
    (candidates : List (ProposedUpdate X Y)) (state : AdaptiveRepairState X Y)
    (first second : List CertificateDecision) :
    adaptiveRepairReplayAux candidates state (first ++ second) =
      adaptiveRepairReplayAux candidates
        (adaptiveRepairReplayAux candidates state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons decision rest ih =>
      simp only [List.cons_append, adaptiveRepairReplayAux]
      exact ih _

/-- One further public decision performs one repair transition. -/
theorem adaptiveRepairStateFromTranscript_append_singleton {X Y : Type*}
    (initial : Model X Y) (candidates : List (ProposedUpdate X Y))
    (transcript : List CertificateDecision) (decision : CertificateDecision) :
    adaptiveRepairStateFromTranscript initial candidates (transcript ++ [decision]) =
      adaptiveRepairStepFromDecision candidates
        (adaptiveRepairStateFromTranscript initial candidates transcript) decision := by
  rw [adaptiveRepairStateFromTranscript, adaptiveRepairReplayAux_append]
  rfl

/-- Replay's operational counter equals the number of supplied acceptances. -/
theorem adaptiveRepairReplayAux_accepted {X Y : Type*}
    (candidates : List (ProposedUpdate X Y)) (state : AdaptiveRepairState X Y)
    (transcript : List CertificateDecision) :
    (adaptiveRepairReplayAux candidates state transcript).accepted =
      state.accepted + numberAccepted transcript := by
  induction transcript generalizing state with
  | nil => simp [adaptiveRepairReplayAux, numberAccepted]
  | cons decision rest ih =>
      simp only [adaptiveRepairReplayAux]
      rw [ih]
      cases hremaining : state.remaining with
      | nil =>
          cases decision <;>
            simp [adaptiveRepairStepFromDecision, hremaining, numberAccepted,
              Nat.add_comm, Nat.add_left_comm]
      | cons candidate tail =>
          cases decision <;>
            simp [adaptiveRepairStepFromDecision, hremaining, numberAccepted,
              Nat.add_comm, Nat.add_left_comm]

/-- The reconstructed repair state counts exactly the accepted public
decisions. -/
@[simp] theorem adaptiveRepairStateFromTranscript_accepted {X Y : Type*}
    (initial : Model X Y) (candidates : List (ProposedUpdate X Y))
    (transcript : List CertificateDecision) :
    (adaptiveRepairStateFromTranscript initial candidates transcript).accepted =
      numberAccepted transcript := by
  simp [adaptiveRepairStateFromTranscript, adaptiveRepairReplayAux_accepted,
    initialAdaptiveRepairState]

/-- The total transcript-adaptive submission strategy for a repair phase. -/
def adaptiveRepairSubmissionStrategy {X Y : Type*}
    (initial : Model X Y) (candidates : List (ProposedUpdate X Y)) :
    AdaptiveSubmissionStrategy X Y :=
  fun transcript => adaptiveRepairSubmission
    (adaptiveRepairStateFromTranscript initial candidates transcript)

/-- Literal public transcript of a repair phase run through Algorithm 2. -/
def adaptiveRepairTranscript {X Y : Type*} {n : ℕ}
    (epsilon : ℝ) (loss : BoundedLoss Y) (sample : Fin n → X × Y)
    (Q : ℕ) (initial : Model X Y)
    (candidates : List (ProposedUpdate X Y)) : List CertificateDecision :=
  certificateCheckerRun epsilon loss sample Q
    (adaptiveRepairSubmissionStrategy initial candidates)

/-- Replayed output of a repair phase. -/
def adaptiveRepairOutput {X Y : Type*} {n : ℕ}
    (epsilon : ℝ) (loss : BoundedLoss Y) (sample : Fin n → X × Y)
    (Q : ℕ) (initial : Model X Y)
    (candidates : List (ProposedUpdate X Y)) : AdaptiveRepairState X Y :=
  adaptiveRepairStateFromTranscript initial candidates
    (adaptiveRepairTranscript epsilon loss sample Q initial candidates)

/-- The total no-op query is deterministically rejected at every positive
target, independently of the sample. -/
theorem repairNoopSubmission_rejected {X Y : Type*} {n : ℕ}
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (loss : BoundedLoss Y)
    (sample : Fin n → X × Y) (current : Model X Y) :
    certificateCheckerDecision epsilon loss sample
      (repairNoopSubmission current) = .rejected := by
  rw [certificateCheckerDecision_eq_rejected_iff]
  have hzero : empiricalSubmissionScore loss sample
      (repairNoopSubmission current) = 0 := by
    simp [empiricalSubmissionScore, finiteIidScoreSum, submissionScore,
      repairNoopSubmission, groupIndicator]
  rw [hzero]
  linarith

/-- The rejected prefix followed by the unscanned suffix is always exactly the
fixed repair-candidate list. -/
def RepairScanPartition {X Y : Type*}
    (candidates : List (ProposedUpdate X Y)) (state : AdaptiveRepairState X Y) : Prop :=
  state.rejectedReverse.reverse ++ state.remaining = candidates

/-- One repair transition preserves the scan partition. -/
theorem adaptiveRepairStep_preserves_partition {X Y : Type*}
    (candidates : List (ProposedUpdate X Y)) (state : AdaptiveRepairState X Y)
    (decision : CertificateDecision)
    (hpartition : RepairScanPartition candidates state) :
    RepairScanPartition candidates
      (adaptiveRepairStepFromDecision candidates state decision) := by
  unfold RepairScanPartition at hpartition ⊢
  cases hremaining : state.remaining with
  | nil =>
      cases decision <;>
        simpa [adaptiveRepairStepFromDecision, hremaining] using hpartition
  | cons candidate rest =>
      cases decision with
      | rejected =>
          simpa [adaptiveRepairStepFromDecision, hremaining, List.reverse_cons,
            List.append_assoc] using hpartition
      | accepted =>
          simp [adaptiveRepairStepFromDecision, hremaining]

/-- Replay preserves the scan partition from any state satisfying it. -/
theorem adaptiveRepairReplayAux_preserves_partition {X Y : Type*}
    (candidates : List (ProposedUpdate X Y)) (state : AdaptiveRepairState X Y)
    (transcript : List CertificateDecision)
    (hpartition : RepairScanPartition candidates state) :
    RepairScanPartition candidates
      (adaptiveRepairReplayAux candidates state transcript) := by
  induction transcript generalizing state with
  | nil => simpa [adaptiveRepairReplayAux] using hpartition
  | cons decision rest ih =>
      simp only [adaptiveRepairReplayAux]
      exact ih _ (adaptiveRepairStep_preserves_partition candidates state decision
        hpartition)

/-- Every replayed repair state satisfies the scan-partition invariant. -/
theorem adaptiveRepairStateFromTranscript_partition {X Y : Type*}
    (initial : Model X Y) (candidates : List (ProposedUpdate X Y))
    (transcript : List CertificateDecision) :
    RepairScanPartition candidates
      (adaptiveRepairStateFromTranscript initial candidates transcript) := by
  apply adaptiveRepairReplayAux_preserves_partition
  simp [RepairScanPartition, initialAdaptiveRepairState]

/-- Population-loss accounting potential for a repair phase. -/
def adaptiveRepairPotential {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y) (epsilon : ℝ)
    (state : AdaptiveRepairState X Y) : ℝ :=
  modelLoss law loss state.current + (state.accepted : ℝ) * (epsilon / 2)

/-- Sound rejection semantics accumulated during the current scan. -/
def RejectedRepairsSound {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y) (epsilon : ℝ)
    (state : AdaptiveRepairState X Y) : Prop :=
  ∀ candidate ∈ state.rejectedReverse, ∀ mu Delta,
    epsilon ≤ mu * Delta →
      ¬ CertificateOfSuboptimality law loss state.current candidate.group
        candidate.replacement mu Delta

/-- One actual repair query cannot increase the repair potential on the
Algorithm 2 good event. -/
theorem adaptiveRepairActualStep_potential_le
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) {n : ℕ}
    (sample : Fin n → X × Y) (candidates : List (ProposedUpdate X Y))
    (state : AdaptiveRepairState X Y)
    (hchecker : CheckerDecisionGuaranteed law loss epsilon
      (adaptiveRepairSubmission state)
      (certificateCheckerDecision epsilon loss sample
        (adaptiveRepairSubmission state))) :
    adaptiveRepairPotential law loss epsilon
        (adaptiveRepairStepFromDecision candidates state
          (certificateCheckerDecision epsilon loss sample
            (adaptiveRepairSubmission state))) ≤
      adaptiveRepairPotential law loss epsilon state := by
  cases hremaining : state.remaining with
  | nil =>
      have hrejected := repairNoopSubmission_rejected epsilon hepsilon loss sample
        state.current
      have hdecision : certificateCheckerDecision epsilon loss sample
          (adaptiveRepairSubmission state) = .rejected := by
        simpa [adaptiveRepairSubmission, hremaining] using hrejected
      simp [adaptiveRepairStepFromDecision, hremaining, hdecision]
  | cons candidate rest =>
      cases hdecision : certificateCheckerDecision epsilon loss sample
          (adaptiveRepairSubmission state) with
      | rejected =>
          simp [adaptiveRepairStepFromDecision, hremaining, hdecision,
            adaptiveRepairPotential]
      | accepted =>
          obtain ⟨mu, Delta, hcert, hlarge⟩ := hchecker.2 hdecision
          have hcert' : CertificateOfSuboptimality law loss state.current
              candidate.group candidate.replacement mu Delta := by
            simpa [adaptiveRepairSubmission, hremaining] using hcert
          have hprogress := (theorem9_listUpdate_progress hcert').2
          have hloss : modelLoss law loss
                (listUpdate state.current candidate.group candidate.replacement) ≤
              modelLoss law loss state.current - epsilon / 2 :=
            hprogress.trans (by linarith)
          simp only [adaptiveRepairStepFromDecision, hremaining, hdecision,
            adaptiveRepairPotential]
          push_cast
          nlinarith

/-- One actual query preserves the soundness of every rejection accumulated in
the current scan; acceptance resets that scan. -/
theorem adaptiveRepairActualStep_preserves_rejectedSound
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) {n : ℕ}
    (sample : Fin n → X × Y) (candidates : List (ProposedUpdate X Y))
    (state : AdaptiveRepairState X Y)
    (hprevious : RejectedRepairsSound law loss epsilon state)
    (hchecker : CheckerDecisionGuaranteed law loss epsilon
      (adaptiveRepairSubmission state)
      (certificateCheckerDecision epsilon loss sample
        (adaptiveRepairSubmission state))) :
    RejectedRepairsSound law loss epsilon
      (adaptiveRepairStepFromDecision candidates state
        (certificateCheckerDecision epsilon loss sample
          (adaptiveRepairSubmission state))) := by
  cases hremaining : state.remaining with
  | nil =>
      have hrejected := repairNoopSubmission_rejected epsilon hepsilon loss sample
        state.current
      have hdecision : certificateCheckerDecision epsilon loss sample
          (adaptiveRepairSubmission state) = .rejected := by
        simpa [adaptiveRepairSubmission, hremaining] using hrejected
      simpa [adaptiveRepairStepFromDecision, hremaining, hdecision] using hprevious
  | cons candidate rest =>
      cases hdecision : certificateCheckerDecision epsilon loss sample
          (adaptiveRepairSubmission state) with
      | accepted =>
          simp [RejectedRepairsSound, adaptiveRepairStepFromDecision, hremaining,
            hdecision]
      | rejected =>
          simp only [hdecision, RejectedRepairsSound,
            adaptiveRepairStepFromDecision, hremaining, List.mem_cons]
          intro tested htested mu Delta hlarge
          rcases htested with heq | htested
          · subst tested
            have hsound := hchecker.1 hdecision mu Delta hlarge
            simpa [adaptiveRepairSubmission, hremaining] using hsound
          · exact hprevious tested htested mu Delta hlarge

/-- Good-event predicate for the literal Algorithm 2 execution driving one
corrected repair phase. -/
def AdaptiveRepairRunGuaranteed {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y) (epsilon : ℝ)
    {n : ℕ} (sample : Fin n → X × Y) (Q : ℕ) (initial : Model X Y)
    (candidates : List (ProposedUpdate X Y)) : Prop :=
  CheckerRunAuxGuaranteed law loss epsilon sample
    (adaptiveRepairSubmissionStrategy initial candidates) Q []

/-- Population-loss potential is nonincreasing along every good literal repair
execution. -/
theorem adaptiveRepairRunAux_potential_le
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) {n : ℕ}
    (sample : Fin n → X × Y) (initial : Model X Y)
    (candidates : List (ProposedUpdate X Y)) :
    ∀ (remaining : ℕ) (reverseTranscript : List CertificateDecision),
      CheckerRunAuxGuaranteed law loss epsilon sample
          (adaptiveRepairSubmissionStrategy initial candidates)
          remaining reverseTranscript →
      let start := adaptiveRepairStateFromTranscript initial candidates
        reverseTranscript.reverse
      let finalTranscript := certificateCheckerRunAux epsilon loss sample
        (adaptiveRepairSubmissionStrategy initial candidates)
        remaining reverseTranscript
      let final := adaptiveRepairStateFromTranscript initial candidates finalTranscript
      adaptiveRepairPotential law loss epsilon final ≤
        adaptiveRepairPotential law loss epsilon start := by
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
        let state := adaptiveRepairStateFromTranscript initial candidates
          publicTranscript
        let submission := adaptiveRepairSubmission state
        let decision := certificateCheckerDecision epsilon loss sample submission
        have hparts : CheckerDecisionGuaranteed law loss epsilon submission decision ∧
            CheckerRunAuxGuaranteed law loss epsilon sample
              (adaptiveRepairSubmissionStrategy initial candidates)
              remaining (decision :: reverseTranscript) := by
          simpa [CheckerRunAuxGuaranteed, hguard,
            adaptiveRepairSubmissionStrategy, publicTranscript, state, submission,
            decision] using hguaranteed
        have hstep : adaptiveRepairPotential law loss epsilon
              (adaptiveRepairStepFromDecision candidates state decision) ≤
            adaptiveRepairPotential law loss epsilon state := by
          exact adaptiveRepairActualStep_potential_le law loss epsilon hepsilon
            sample candidates state (by simpa [submission, decision] using hparts.1)
        have hnextState :
            adaptiveRepairStateFromTranscript initial candidates
                (decision :: reverseTranscript).reverse =
              adaptiveRepairStepFromDecision candidates state decision := by
          simp only [List.reverse_cons]
          simpa [state, publicTranscript] using
            (adaptiveRepairStateFromTranscript_append_singleton initial candidates
              publicTranscript decision)
        have htail := ih (decision :: reverseTranscript) hparts.2
        have hstep' : adaptiveRepairPotential law loss epsilon
              (adaptiveRepairStateFromTranscript initial candidates
                (decision :: reverseTranscript).reverse) ≤
            adaptiveRepairPotential law loss epsilon
              (adaptiveRepairStateFromTranscript initial candidates
                reverseTranscript.reverse) := by
          rw [hnextState]
          simpa [state, publicTranscript] using hstep
        simp only [certificateCheckerRunAux, hguard, if_pos]
        exact htail.trans hstep'
      · simp [certificateCheckerRunAux, hguard]

/-- The literal repair checker processes its entire query horizon on the good
event; the loss budget prevents Algorithm 2's acceptance guard from closing. -/
theorem adaptiveRepairRunAux_length_eq
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) {n : ℕ}
    (sample : Fin n → X × Y) (initial : Model X Y)
    (candidates : List (ProposedUpdate X Y)) :
    ∀ (remaining : ℕ) (reverseTranscript : List CertificateDecision),
      CheckerRunAuxGuaranteed law loss epsilon sample
          (adaptiveRepairSubmissionStrategy initial candidates)
          remaining reverseTranscript →
      adaptiveRepairPotential law loss epsilon
          (adaptiveRepairStateFromTranscript initial candidates
            reverseTranscript.reverse) ≤ modelLoss law loss initial →
      (certificateCheckerRunAux epsilon loss sample
          (adaptiveRepairSubmissionStrategy initial candidates)
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
      let state := adaptiveRepairStateFromTranscript initial candidates
        publicTranscript
      have hstateAccepted : state.accepted = numberAccepted reverseTranscript := by
        dsimp [state, publicTranscript]
        rw [adaptiveRepairStateFromTranscript_accepted, numberAccepted_reverse]
      have hstateNonneg : 0 ≤ modelLoss law loss state.current :=
        modelLoss_nonneg law loss state.current
      have hinitialOne : modelLoss law loss initial ≤ 1 :=
        modelLoss_le_one law loss initial
      have hacceptedMul : (state.accepted : ℝ) * epsilon ≤ 2 := by
        unfold adaptiveRepairPotential at hpotential
        nlinarith
      have hguard : (numberAccepted reverseTranscript : ℝ) ≤ 2 / epsilon := by
        apply (le_div_iff₀ hepsilon).2
        simpa [hstateAccepted] using hacceptedMul
      let submission := adaptiveRepairSubmission state
      let decision := certificateCheckerDecision epsilon loss sample submission
      have hparts : CheckerDecisionGuaranteed law loss epsilon submission decision ∧
          CheckerRunAuxGuaranteed law loss epsilon sample
            (adaptiveRepairSubmissionStrategy initial candidates)
            remaining (decision :: reverseTranscript) := by
        simpa [CheckerRunAuxGuaranteed, hguard,
          adaptiveRepairSubmissionStrategy, publicTranscript, state, submission,
          decision] using hguaranteed
      have hstep : adaptiveRepairPotential law loss epsilon
            (adaptiveRepairStepFromDecision candidates state decision) ≤
          adaptiveRepairPotential law loss epsilon state :=
        adaptiveRepairActualStep_potential_le law loss epsilon hepsilon sample
          candidates state (by simpa [submission, decision] using hparts.1)
      have hnextState :
          adaptiveRepairStateFromTranscript initial candidates
              (decision :: reverseTranscript).reverse =
            adaptiveRepairStepFromDecision candidates state decision := by
        simp only [List.reverse_cons]
        simpa [state, publicTranscript] using
          (adaptiveRepairStateFromTranscript_append_singleton initial candidates
            publicTranscript decision)
      have hnextPotential : adaptiveRepairPotential law loss epsilon
            (adaptiveRepairStateFromTranscript initial candidates
              (decision :: reverseTranscript).reverse) ≤
          modelLoss law loss initial := by
        rw [hnextState]
        exact hstep.trans (by simpa [state, publicTranscript] using hpotential)
      have htail := ih (decision :: reverseTranscript) hparts.2 hnextPotential
      simp only [certificateCheckerRunAux, hguard, if_pos]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

/-- Soundness of the rejected portion of the current scan propagates through
the complete actual repair execution. -/
theorem adaptiveRepairRunAux_rejectedSound
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) {n : ℕ}
    (sample : Fin n → X × Y) (initial : Model X Y)
    (candidates : List (ProposedUpdate X Y)) :
    ∀ (remaining : ℕ) (reverseTranscript : List CertificateDecision),
      CheckerRunAuxGuaranteed law loss epsilon sample
          (adaptiveRepairSubmissionStrategy initial candidates)
          remaining reverseTranscript →
      RejectedRepairsSound law loss epsilon
        (adaptiveRepairStateFromTranscript initial candidates
          reverseTranscript.reverse) →
      RejectedRepairsSound law loss epsilon
        (adaptiveRepairStateFromTranscript initial candidates
          (certificateCheckerRunAux epsilon loss sample
            (adaptiveRepairSubmissionStrategy initial candidates)
            remaining reverseTranscript)) := by
  intro remaining
  induction remaining with
  | zero =>
      intro reverseTranscript _ hsound
      simpa [certificateCheckerRunAux] using hsound
  | succ remaining ih =>
      intro reverseTranscript hguaranteed hsound
      by_cases hguard :
          (numberAccepted reverseTranscript : ℝ) ≤ 2 / epsilon
      · let publicTranscript := reverseTranscript.reverse
        let state := adaptiveRepairStateFromTranscript initial candidates
          publicTranscript
        let submission := adaptiveRepairSubmission state
        let decision := certificateCheckerDecision epsilon loss sample submission
        have hparts : CheckerDecisionGuaranteed law loss epsilon submission decision ∧
            CheckerRunAuxGuaranteed law loss epsilon sample
              (adaptiveRepairSubmissionStrategy initial candidates)
              remaining (decision :: reverseTranscript) := by
          simpa [CheckerRunAuxGuaranteed, hguard,
            adaptiveRepairSubmissionStrategy, publicTranscript, state, submission,
            decision] using hguaranteed
        have hsoundState : RejectedRepairsSound law loss epsilon state := by
          simpa [state, publicTranscript] using hsound
        have hsoundNext := adaptiveRepairActualStep_preserves_rejectedSound
          law loss epsilon hepsilon sample candidates state hsoundState
          (by simpa [submission, decision] using hparts.1)
        have hnextState :
            adaptiveRepairStateFromTranscript initial candidates
                (decision :: reverseTranscript).reverse =
              adaptiveRepairStepFromDecision candidates state decision := by
          simp only [List.reverse_cons]
          simpa [state, publicTranscript] using
            (adaptiveRepairStateFromTranscript_append_singleton initial candidates
              publicTranscript decision)
        simp only [certificateCheckerRunAux, hguard, if_pos]
        apply ih (decision :: reverseTranscript) hparts.2
        rw [hnextState]
        exact hsoundNext
      · simpa [certificateCheckerRunAux, hguard] using hsound

/-- Remaining combinatorial work in a repair phase.  A rejection consumes one
candidate; an acceptance consumes the rest of the current scan and one unit of
the remaining acceptance budget before restarting. -/
def adaptiveRepairMetric {X Y : Type*} (K : ℕ)
    (candidates : List (ProposedUpdate X Y)) (state : AdaptiveRepairState X Y) : ℕ :=
  (K - state.accepted) * candidates.length + state.remaining.length

/-- A nonclosed repair transition strictly decreases the combinatorial work
metric whenever the post-transition acceptance count remains within budget. -/
theorem adaptiveRepairStep_metric_lt {X Y : Type*}
    (K : ℕ) (candidates : List (ProposedUpdate X Y))
    (state : AdaptiveRepairState X Y) (decision : CertificateDecision)
    (hopen : state.remaining ≠ [])
    (hnextCap :
      (adaptiveRepairStepFromDecision candidates state decision).accepted ≤ K) :
    adaptiveRepairMetric K candidates
        (adaptiveRepairStepFromDecision candidates state decision) <
      adaptiveRepairMetric K candidates state := by
  cases hremaining : state.remaining with
  | nil => exact False.elim (hopen hremaining)
  | cons candidate rest =>
      cases decision with
      | rejected =>
          simp [adaptiveRepairMetric, adaptiveRepairStepFromDecision, hremaining]
      | accepted =>
          have hcap : state.accepted + 1 ≤ K := by
            simpa [adaptiveRepairStepFromDecision, hremaining] using hnextCap
          have hsub : K - state.accepted = K - (state.accepted + 1) + 1 := by
            omega
          simp only [adaptiveRepairMetric, adaptiveRepairStepFromDecision, hremaining,
            List.length_cons]
          rw [hsub, Nat.add_mul]
          omega

/-- The loss potential converts the real source bound into the exact rounded
natural acceptance budget. -/
theorem adaptiveRepairState_accepted_le_budget
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (initial : Model X Y)
    (state : AdaptiveRepairState X Y)
    (hpotential : adaptiveRepairPotential law loss epsilon state ≤
      modelLoss law loss initial) :
    state.accepted ≤ checkerAcceptanceBudget epsilon := by
  have hstateNonneg : 0 ≤ modelLoss law loss state.current :=
    modelLoss_nonneg law loss state.current
  have hinitialOne : modelLoss law loss initial ≤ 1 :=
    modelLoss_le_one law loss initial
  have hmul : (state.accepted : ℝ) * epsilon ≤ 2 := by
    unfold adaptiveRepairPotential at hpotential
    nlinarith
  have hreal : (state.accepted : ℝ) ≤ 2 / epsilon :=
    (le_div_iff₀ hepsilon).2 hmul
  unfold checkerAcceptanceBudget
  exact Nat.le_floor hreal

/-- Once a repair scan is closed, replay remains closed through any remaining
totalized Algorithm 2 queries. -/
theorem adaptiveRepairRunAux_preserves_closed
    {X Y : Type*} {n : ℕ}
    (epsilon : ℝ) (loss : BoundedLoss Y) (sample : Fin n → X × Y)
    (initial : Model X Y) (candidates : List (ProposedUpdate X Y)) :
    ∀ (remaining : ℕ) (reverseTranscript : List CertificateDecision),
      (adaptiveRepairStateFromTranscript initial candidates
        reverseTranscript.reverse).remaining = [] →
      (adaptiveRepairStateFromTranscript initial candidates
        (certificateCheckerRunAux epsilon loss sample
          (adaptiveRepairSubmissionStrategy initial candidates)
          remaining reverseTranscript)).remaining = [] := by
  intro remaining
  induction remaining with
  | zero =>
      intro reverseTranscript hclosed
      simpa [certificateCheckerRunAux] using hclosed
  | succ remaining ih =>
      intro reverseTranscript hclosed
      by_cases hguard :
          (numberAccepted reverseTranscript : ℝ) ≤ 2 / epsilon
      · let publicTranscript := reverseTranscript.reverse
        let state := adaptiveRepairStateFromTranscript initial candidates
          publicTranscript
        let decision := certificateCheckerDecision epsilon loss sample
          (adaptiveRepairSubmission state)
        have hnextState :
            adaptiveRepairStateFromTranscript initial candidates
                (decision :: reverseTranscript).reverse =
              adaptiveRepairStepFromDecision candidates state decision := by
          simp only [List.reverse_cons]
          simpa [state, publicTranscript] using
            (adaptiveRepairStateFromTranscript_append_singleton initial candidates
              publicTranscript decision)
        have hstateClosed : state.remaining = [] := by
          simpa [state, publicTranscript] using hclosed
        have hnextClosed :
            (adaptiveRepairStateFromTranscript initial candidates
              (decision :: reverseTranscript).reverse).remaining = [] := by
          rw [hnextState]
          cases decision <;>
            simp [adaptiveRepairStepFromDecision, hstateClosed]
        simp only [certificateCheckerRunAux, hguard, if_pos]
        exact ih (decision :: reverseTranscript) hnextClosed
      · simpa [certificateCheckerRunAux, hguard] using hclosed

/-- If the remaining query horizon dominates the repair metric, every good
execution reaches a complete rejected scan. -/
theorem adaptiveRepairRunAux_closes
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) {n : ℕ}
    (sample : Fin n → X × Y) (initial : Model X Y)
    (candidates : List (ProposedUpdate X Y)) :
    ∀ (remaining : ℕ) (reverseTranscript : List CertificateDecision),
      CheckerRunAuxGuaranteed law loss epsilon sample
          (adaptiveRepairSubmissionStrategy initial candidates)
          remaining reverseTranscript →
      adaptiveRepairPotential law loss epsilon
          (adaptiveRepairStateFromTranscript initial candidates
            reverseTranscript.reverse) ≤ modelLoss law loss initial →
      adaptiveRepairMetric (checkerAcceptanceBudget epsilon) candidates
          (adaptiveRepairStateFromTranscript initial candidates
            reverseTranscript.reverse) ≤ remaining →
      (adaptiveRepairStateFromTranscript initial candidates
        (certificateCheckerRunAux epsilon loss sample
          (adaptiveRepairSubmissionStrategy initial candidates)
          remaining reverseTranscript)).remaining = [] := by
  intro remaining
  induction remaining with
  | zero =>
      intro reverseTranscript _ _ hmetric
      let state := adaptiveRepairStateFromTranscript initial candidates
        reverseTranscript.reverse
      cases hremaining : state.remaining with
      | nil =>
          simpa [certificateCheckerRunAux, state] using hremaining
      | cons candidate rest =>
          have hpositive : 0 < adaptiveRepairMetric
              (checkerAcceptanceBudget epsilon) candidates state := by
            unfold adaptiveRepairMetric
            simp [hremaining]
          have hzero : adaptiveRepairMetric
              (checkerAcceptanceBudget epsilon) candidates state ≤ 0 := by
            simpa [state] using hmetric
          omega
  | succ remaining ih =>
      intro reverseTranscript hguaranteed hpotential hmetric
      let publicTranscript := reverseTranscript.reverse
      let state := adaptiveRepairStateFromTranscript initial candidates
        publicTranscript
      have hstateAccepted : state.accepted = numberAccepted reverseTranscript := by
        dsimp [state, publicTranscript]
        rw [adaptiveRepairStateFromTranscript_accepted, numberAccepted_reverse]
      have hacceptedCap : state.accepted ≤ checkerAcceptanceBudget epsilon :=
        adaptiveRepairState_accepted_le_budget law loss epsilon hepsilon initial state
          (by simpa [state, publicTranscript] using hpotential)
      have hguard : (numberAccepted reverseTranscript : ℝ) ≤ 2 / epsilon := by
        have hstateNonneg : 0 ≤ modelLoss law loss state.current :=
          modelLoss_nonneg law loss state.current
        have hinitialOne : modelLoss law loss initial ≤ 1 :=
          modelLoss_le_one law loss initial
        have hacceptedMul : (state.accepted : ℝ) * epsilon ≤ 2 := by
          have hp : adaptiveRepairPotential law loss epsilon state ≤
              modelLoss law loss initial := by
            simpa [state, publicTranscript] using hpotential
          unfold adaptiveRepairPotential at hp
          nlinarith
        apply (le_div_iff₀ hepsilon).2
        simpa [hstateAccepted] using hacceptedMul
      let submission := adaptiveRepairSubmission state
      let decision := certificateCheckerDecision epsilon loss sample submission
      have hparts : CheckerDecisionGuaranteed law loss epsilon submission decision ∧
          CheckerRunAuxGuaranteed law loss epsilon sample
            (adaptiveRepairSubmissionStrategy initial candidates)
            remaining (decision :: reverseTranscript) := by
        simpa [CheckerRunAuxGuaranteed, hguard,
          adaptiveRepairSubmissionStrategy, publicTranscript, state, submission,
          decision] using hguaranteed
      cases hremaining : state.remaining with
      | nil =>
          have hclosed :
              (adaptiveRepairStateFromTranscript initial candidates
                reverseTranscript.reverse).remaining = [] := by
            simpa [state, publicTranscript] using hremaining
          exact adaptiveRepairRunAux_preserves_closed epsilon loss sample initial
            candidates (remaining + 1) reverseTranscript hclosed
      | cons candidate rest =>
          have hstep : adaptiveRepairPotential law loss epsilon
                (adaptiveRepairStepFromDecision candidates state decision) ≤
              adaptiveRepairPotential law loss epsilon state :=
            adaptiveRepairActualStep_potential_le law loss epsilon hepsilon sample
              candidates state (by simpa [submission, decision] using hparts.1)
          have hnextState :
              adaptiveRepairStateFromTranscript initial candidates
                  (decision :: reverseTranscript).reverse =
                adaptiveRepairStepFromDecision candidates state decision := by
            simp only [List.reverse_cons]
            simpa [state, publicTranscript] using
              (adaptiveRepairStateFromTranscript_append_singleton initial candidates
                publicTranscript decision)
          have hnextPotential : adaptiveRepairPotential law loss epsilon
                (adaptiveRepairStateFromTranscript initial candidates
                  (decision :: reverseTranscript).reverse) ≤
              modelLoss law loss initial := by
            rw [hnextState]
            exact hstep.trans (by simpa [state, publicTranscript] using hpotential)
          have hnextCap :
              (adaptiveRepairStepFromDecision candidates state decision).accepted ≤
                checkerAcceptanceBudget epsilon :=
            adaptiveRepairState_accepted_le_budget law loss epsilon hepsilon initial
              _ (by
                rw [← hnextState]
                exact hnextPotential)
          have hmetricStrict := adaptiveRepairStep_metric_lt
            (checkerAcceptanceBudget epsilon) candidates state decision
            (by simp [hremaining]) hnextCap
          have hmetricState : adaptiveRepairMetric
              (checkerAcceptanceBudget epsilon) candidates state ≤ remaining + 1 := by
            simpa [state, publicTranscript] using hmetric
          have hnextMetric : adaptiveRepairMetric
                (checkerAcceptanceBudget epsilon) candidates
                (adaptiveRepairStateFromTranscript initial candidates
                  (decision :: reverseTranscript).reverse) ≤ remaining := by
            rw [hnextState]
            omega
          simp only [certificateCheckerRunAux, hguard, if_pos]
          exact ih (decision :: reverseTranscript) hparts.2 hnextPotential hnextMetric

/-- Exact sufficient repair-query horizon: at most `K` accepted restarts and
one final rejected scan, each containing at most `candidates.length` queries. -/
noncomputable def adaptiveRepairQueryBudget {X Y : Type*} (epsilon : ℝ)
    (candidates : List (ProposedUpdate X Y)) : ℕ :=
  (checkerAcceptanceBudget epsilon + 1) * candidates.length

/-- Exact cardinality of the protected-group/past-model repair grid. -/
@[simp] theorem repairCandidates_length {X Y : Type*}
    (groups : List (Group X)) (pastModels : List (Model X Y)) :
    (repairCandidates groups pastModels).length = groups.length * pastModels.length := by
  simp [repairCandidates, List.length_flatMap]

/-- Rounded query accounting for a protected history.  The `K + 1` factor is
the exact final rejected scan required to certify closure; the source's cubic
display suppresses this additive scan/rounding term. -/
theorem adaptiveRepairQueryBudget_history_le {X Y : Type*}
    (epsilon : ℝ) (K : ℕ) (groups : List (Group X))
    (pastModels : List (Model X Y))
    (hbudget : checkerAcceptanceBudget epsilon ≤ K)
    (hgroups : groups.length ≤ K) (hpast : pastModels.length ≤ K) :
    adaptiveRepairQueryBudget epsilon (repairCandidates groups pastModels) ≤
      (K + 1) * K ^ 2 := by
  unfold adaptiveRepairQueryBudget
  rw [repairCandidates_length]
  have hleft : checkerAcceptanceBudget epsilon + 1 ≤ K + 1 := Nat.add_le_add_right hbudget 1
  have hright : groups.length * pastModels.length ≤ K * K :=
    Nat.mul_le_mul hgroups hpast
  calc
    (checkerAcceptanceBudget epsilon + 1) *
        (groups.length * pastModels.length) ≤ (K + 1) * (K * K) :=
      Nat.mul_le_mul hleft hright
    _ = (K + 1) * K ^ 2 := by ring

/-- The initial repair metric is exactly the declared query budget. -/
theorem initialAdaptiveRepairState_metric {X Y : Type*} (epsilon : ℝ)
    (initial : Model X Y) (candidates : List (ProposedUpdate X Y)) :
    adaptiveRepairMetric (checkerAcceptanceBudget epsilon) candidates
        (initialAdaptiveRepairState initial candidates) =
      adaptiveRepairQueryBudget epsilon candidates := by
  simp [adaptiveRepairMetric, adaptiveRepairQueryBudget,
    initialAdaptiveRepairState, Nat.add_mul]

/-- The good Algorithm 2 event forces the bounded repair phase to reach
restart-until-closed termination. -/
theorem adaptiveRepairOutput_closed
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) {n : ℕ}
    (sample : Fin n → X × Y) (initial : Model X Y)
    (candidates : List (ProposedUpdate X Y))
    (hguaranteed : AdaptiveRepairRunGuaranteed law loss epsilon sample
      (adaptiveRepairQueryBudget epsilon candidates) initial candidates) :
    (adaptiveRepairOutput epsilon loss sample
      (adaptiveRepairQueryBudget epsilon candidates) initial candidates).remaining = [] := by
  have hpotential : adaptiveRepairPotential law loss epsilon
      (adaptiveRepairStateFromTranscript initial candidates [].reverse) ≤
        modelLoss law loss initial := by
    simp [adaptiveRepairPotential, adaptiveRepairStateFromTranscript,
      adaptiveRepairReplayAux, initialAdaptiveRepairState]
  have hmetric : adaptiveRepairMetric (checkerAcceptanceBudget epsilon) candidates
      (adaptiveRepairStateFromTranscript initial candidates [].reverse) ≤
        adaptiveRepairQueryBudget epsilon candidates := by
    simp [adaptiveRepairStateFromTranscript, adaptiveRepairReplayAux,
      initialAdaptiveRepairState_metric]
  have hclosed := adaptiveRepairRunAux_closes law loss epsilon hepsilon sample
    initial candidates (adaptiveRepairQueryBudget epsilon candidates) []
    hguaranteed hpotential hmetric
  simpa [adaptiveRepairOutput, adaptiveRepairTranscript, certificateCheckerRun]
    using hclosed

/-- The final closed scan contains only population-sound rejections. -/
theorem adaptiveRepairOutput_rejectedSound
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) {n : ℕ}
    (sample : Fin n → X × Y) (initial : Model X Y)
    (candidates : List (ProposedUpdate X Y))
    (hguaranteed : AdaptiveRepairRunGuaranteed law loss epsilon sample
      (adaptiveRepairQueryBudget epsilon candidates) initial candidates) :
    RejectedRepairsSound law loss epsilon
      (adaptiveRepairOutput epsilon loss sample
        (adaptiveRepairQueryBudget epsilon candidates) initial candidates) := by
  have hinitial : RejectedRepairsSound law loss epsilon
      (adaptiveRepairStateFromTranscript initial candidates [].reverse) := by
    simp [RejectedRepairsSound, adaptiveRepairStateFromTranscript,
      adaptiveRepairReplayAux, initialAdaptiveRepairState]
  have hsound := adaptiveRepairRunAux_rejectedSound law loss epsilon hepsilon
    sample initial candidates (adaptiveRepairQueryBudget epsilon candidates) []
    hguaranteed hinitial
  simpa [adaptiveRepairOutput, adaptiveRepairTranscript, certificateCheckerRun]
    using hsound

/-- Closure plus the soundness of the final rejected scan gives the source's
approximate groupwise monotonicity conclusion. -/
theorem adaptiveRepairOutput_groupwiseMonotone
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) {n : ℕ}
    (sample : Fin n → X × Y) (initial : Model X Y)
    (candidates : List (ProposedUpdate X Y))
    (hguaranteed : AdaptiveRepairRunGuaranteed law loss epsilon sample
      (adaptiveRepairQueryBudget epsilon candidates) initial candidates) :
    let output := adaptiveRepairOutput epsilon loss sample
      (adaptiveRepairQueryBudget epsilon candidates) initial candidates
    ApproxGroupwiseMonotone law loss epsilon output.current candidates := by
  let output := adaptiveRepairOutput epsilon loss sample
    (adaptiveRepairQueryBudget epsilon candidates) initial candidates
  change ApproxGroupwiseMonotone law loss epsilon output.current candidates
  have hclosed : output.remaining = [] := by
    exact adaptiveRepairOutput_closed law loss epsilon hepsilon sample initial
      candidates hguaranteed
  have hpartition := adaptiveRepairStateFromTranscript_partition initial candidates
    (adaptiveRepairTranscript epsilon loss sample
      (adaptiveRepairQueryBudget epsilon candidates) initial candidates)
  have hpartitionOutput : RepairScanPartition candidates output := by
    simpa [output, adaptiveRepairOutput] using hpartition
  have hrejectedAll : output.rejectedReverse.reverse = candidates := by
    unfold RepairScanPartition at hpartitionOutput
    simpa [hclosed] using hpartitionOutput
  have hsound : RejectedRepairsSound law loss epsilon output := by
    exact adaptiveRepairOutput_rejectedSound law loss epsilon hepsilon sample
      initial candidates hguaranteed
  intro candidate hmem hmass
  have hmemReverse : candidate ∈ output.rejectedReverse := by
    have : candidate ∈ output.rejectedReverse.reverse := by
      rw [hrejectedAll]
      exact hmem
    simpa using this
  have hscore : certificateImprovementScore law loss output.current
      candidate.group candidate.replacement ≤ epsilon := by
    by_contra hnot
    have hscoreLarge : epsilon < certificateImprovementScore law loss output.current
        candidate.group candidate.replacement := lt_of_not_ge hnot
    have hscorePositive : 0 < certificateImprovementScore law loss output.current
        candidate.group candidate.replacement := hepsilon.trans hscoreLarge
    have hcert := canonical_certificate_of_positive_score
      (law := law) (loss := loss) (f := output.current)
      (g := candidate.group) (h := candidate.replacement) hscorePositive
    have hlarge : epsilon ≤ groupMass law candidate.group *
        (groupLoss law loss output.current candidate.group -
          groupLoss law loss candidate.replacement candidate.group) := by
      simpa [certificateImprovementScore] using hscoreLarge.le
    exact (hsound candidate hmemReverse _ _ hlarge) hcert
  exact (approxBayesOptimal_pair_iff_source law loss epsilon output.current
    candidate.replacement candidate.group hmass).1 hscore

/-- Theorem 14's displayed history form: every protected group is within
`epsilon / mass` of every protected past model, hence of their minimum whenever
that finite minimum is defined. -/
def ApproxGroupwiseMonotoneOnHistory {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y) (epsilon : ℝ)
    (current : Model X Y) (groups : List (Group X))
    (pastModels : List (Model X Y)) : Prop :=
  ∀ group ∈ groups, ∀ past ∈ pastModels, 0 < groupMass law group →
    groupLoss law loss current group ≤
      groupLoss law loss past group + epsilon / groupMass law group

/-- The candidate-pair formulation specializes exactly to the source's
protected-group/past-model formulation. -/
theorem approxGroupwiseMonotone_repairCandidates_history
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y) (epsilon : ℝ)
    (current : Model X Y) (groups : List (Group X))
    (pastModels : List (Model X Y))
    (hmonotone : ApproxGroupwiseMonotone law loss epsilon current
      (repairCandidates groups pastModels)) :
    ApproxGroupwiseMonotoneOnHistory law loss epsilon current groups pastModels := by
  intro group hgroup past hpast hmass
  apply hmonotone { group := group, replacement := past }
  · simp [repairCandidates, hgroup, hpast]
  · exact hmass

/-- High-probability repair output in the exact history form displayed in
Theorem 14. -/
theorem adaptiveRepairOutput_groupwiseMonotoneOnHistory
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) {n : ℕ}
    (sample : Fin n → X × Y) (initial : Model X Y)
    (groups : List (Group X)) (pastModels : List (Model X Y))
    (hguaranteed : AdaptiveRepairRunGuaranteed law loss epsilon sample
      (adaptiveRepairQueryBudget epsilon (repairCandidates groups pastModels)) initial
      (repairCandidates groups pastModels)) :
    let output := adaptiveRepairOutput epsilon loss sample
      (adaptiveRepairQueryBudget epsilon (repairCandidates groups pastModels)) initial
      (repairCandidates groups pastModels)
    ApproxGroupwiseMonotoneOnHistory law loss epsilon output.current groups
      pastModels := by
  let output := adaptiveRepairOutput epsilon loss sample
    (adaptiveRepairQueryBudget epsilon (repairCandidates groups pastModels)) initial
    (repairCandidates groups pastModels)
  change ApproxGroupwiseMonotoneOnHistory law loss epsilon output.current groups pastModels
  apply approxGroupwiseMonotone_repairCandidates_history
  exact adaptiveRepairOutput_groupwiseMonotone law loss epsilon hepsilon sample initial
    (repairCandidates groups pastModels) hguaranteed

/-- Complete deterministic conclusion of the corrected adaptive repair phase. -/
def AdaptiveRepairConclusion {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y) (epsilon : ℝ)
    {n : ℕ} (sample : Fin n → X × Y) (initial : Model X Y)
    (candidates : List (ProposedUpdate X Y)) : Prop :=
  let Q := adaptiveRepairQueryBudget epsilon candidates
  let output := adaptiveRepairOutput epsilon loss sample Q initial candidates
  AdaptiveRepairRunGuaranteed law loss epsilon sample Q initial candidates ∧
    output.remaining = [] ∧
    ApproxGroupwiseMonotone law loss epsilon output.current candidates

/-- On Algorithm 2's good event, the corrected repair phase terminates and has
the advertised monotonicity guarantee. -/
theorem adaptiveRepairConclusion_of_checkerRunGuaranteed
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) {n : ℕ}
    (sample : Fin n → X × Y) (initial : Model X Y)
    (candidates : List (ProposedUpdate X Y))
    (hguaranteed : AdaptiveRepairRunGuaranteed law loss epsilon sample
      (adaptiveRepairQueryBudget epsilon candidates) initial candidates) :
    AdaptiveRepairConclusion law loss epsilon sample initial candidates := by
  exact ⟨hguaranteed,
    adaptiveRepairOutput_closed law loss epsilon hepsilon sample initial candidates
      hguaranteed,
    adaptiveRepairOutput_groupwiseMonotone law loss epsilon hepsilon sample initial
      candidates hguaranteed⟩

/-- Failure probability for the complete corrected adaptive repair phase. -/
noncomputable def adaptiveRepairFailure
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (n : ℕ) (initial : Model X Y)
    (candidates : List (ProposedUpdate X Y)) : ℝ := by
  classical
  exact pmfProb (pmfProduct (Fin n) (X × Y) law) (fun sample =>
    ¬ AdaptiveRepairConclusion law loss epsilon sample initial candidates)

/-- A bad corrected repair execution is contained in the bad event for its
literal transcript-adaptive Algorithm 2 stream. -/
theorem adaptiveRepairFailure_le_checkerFailure
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (n : ℕ)
    (initial : Model X Y) (candidates : List (ProposedUpdate X Y)) :
    adaptiveRepairFailure law loss epsilon n initial candidates ≤
      certificateCheckerRunGuaranteeFailure law loss epsilon n
        (adaptiveRepairQueryBudget epsilon candidates)
        (adaptiveRepairSubmissionStrategy initial candidates) := by
  classical
  unfold adaptiveRepairFailure certificateCheckerRunGuaranteeFailure
  apply pmfProb_le_of_imp
  intro sample hbad hgood
  exact hbad (adaptiveRepairConclusion_of_checkerRunGuaranteed
    law loss epsilon hepsilon sample initial candidates hgood)

/-- Corrected Theorem 14 in complete finite-sample form for one arbitrary
restart-until-closed repair phase. -/
theorem theorem14_adaptive_monotoneRepair
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (law : Distribution X Y) (loss : BoundedLoss Y)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (n : ℕ)
    (hcount : 0 < n) (initial : Model X Y)
    (candidates : List (ProposedUpdate X Y)) :
    adaptiveRepairFailure law loss epsilon n initial candidates ≤
      let Q := adaptiveRepairQueryBudget epsilon candidates
      (Q * (Q + 1) ^ checkerAcceptanceBudget epsilon : ℕ) * 2 *
        Real.exp (-(n : ℝ) * epsilon ^ 2 / 32) := by
  let Q := adaptiveRepairQueryBudget epsilon candidates
  calc
    adaptiveRepairFailure law loss epsilon n initial candidates ≤
        certificateCheckerRunGuaranteeFailure law loss epsilon n Q
          (adaptiveRepairSubmissionStrategy initial candidates) := by
      simpa [Q] using adaptiveRepairFailure_le_checkerFailure law loss epsilon
        hepsilon n initial candidates
    _ ≤ (Q * (Q + 1) ^ checkerAcceptanceBudget epsilon : ℕ) * 2 *
          Real.exp (-(n : ℝ) * epsilon ^ 2 / 32) :=
      theorem11_adaptive_certificateCheckerRun law loss epsilon hepsilon n Q
        hcount (adaptiveRepairSubmissionStrategy initial candidates)

end

end GHKR22BiasBounties

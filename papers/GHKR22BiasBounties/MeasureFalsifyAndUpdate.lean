import GHKR22BiasBounties.MeasureAdaptiveChecker
import GHKR22BiasBounties.FalsifyAndUpdate

/-!
# Falsify-and-update on arbitrary measurable populations

This file lifts Algorithm 3 and Theorem 12 from the executable finite-PMF
specialization to the population model actually stated in the paper.  The
algorithm itself is unchanged: it runs on a finite holdout sample.  Only its
population loss and certificate semantics are interpreted as integrals under
an arbitrary probability measure.

Measurability is propagated through every accepted `ListUpdate`.  Thus the
high-probability theorem assumes measurability only of the initial model, the
bounded loss, and every proposal the adaptive submitter may make.
-/

namespace GHKR22BiasBounties

noncomputable section

open MeasureTheory ProbabilityTheory
open AppliedModelingLib Probability

/-- Both functions supplied by one Algorithm 3 proposal are measurable. -/
def MeasureProposalMeasurable
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (proposal : ProposedUpdate X Y) : Prop :=
  MeasurableGroup proposal.group ∧ MeasurableModel proposal.replacement

/-- Supplying an explicit checker decision preserves model measurability. -/
theorem measurableModel_falsifyStepFromDecision
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {state : FalsifyState X Y} (hstate : MeasurableModel state.current)
    {proposal : ProposedUpdate X Y} (hproposal : MeasureProposalMeasurable proposal)
    (decision : CertificateDecision) :
    MeasurableModel (falsifyStepFromDecision state proposal decision).current := by
  cases decision with
  | rejected => simpa [falsifyStepFromDecision] using hstate
  | accepted =>
      simpa [falsifyStepFromDecision] using
        measurableModel_listUpdate hstate hproposal.2 hproposal.1

/-- Transcript replay preserves measurability of the current public model. -/
theorem measurableModel_falsifyReplayAux
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (strategy : AdaptiveProposalStrategy X Y)
    (hstrategy : ∀ transcript, MeasureProposalMeasurable (strategy transcript)) :
    ∀ (state : FalsifyState X Y), MeasurableModel state.current →
      ∀ transcript,
        MeasurableModel (falsifyReplayAux strategy state transcript).current := by
  intro state hstate transcript
  induction transcript generalizing state with
  | nil => simpa [falsifyReplayAux] using hstate
  | cons decision rest ih =>
      simp only [falsifyReplayAux]
      apply ih
      exact measurableModel_falsifyStepFromDecision hstate (hstrategy _) decision

/-- Every public model reconstructed by Algorithm 3 is measurable. -/
theorem measurableModel_falsifyStateFromTranscript
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {initial : Model X Y} (hinitial : MeasurableModel initial)
    {strategy : AdaptiveProposalStrategy X Y}
    (hstrategy : ∀ transcript, MeasureProposalMeasurable (strategy transcript))
    (transcript : List CertificateDecision) :
    MeasurableModel (falsifyStateFromTranscript initial strategy transcript).current := by
  unfold falsifyStateFromTranscript
  apply measurableModel_falsifyReplayAux strategy hstrategy
  simpa [initialFalsifyState] using hinitial

/-- The induced Algorithm 2 stream consists only of measurable submissions. -/
theorem measureSubmissionMeasurable_falsifySubmissionStrategy
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {initial : Model X Y} (hinitial : MeasurableModel initial)
    {strategy : AdaptiveProposalStrategy X Y}
    (hstrategy : ∀ transcript, MeasureProposalMeasurable (strategy transcript)) :
    ∀ transcript,
      MeasureSubmissionMeasurable
        (falsifySubmissionStrategy initial strategy transcript) := by
  intro transcript
  exact ⟨measurableModel_falsifyStateFromTranscript hinitial hstrategy transcript,
    (hstrategy transcript).1, (hstrategy transcript).2⟩

/-- Population-loss accounting potential for a general population law. -/
def measureFalsifyPotential
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) (loss : BoundedLoss Y) (epsilon : ℝ)
    (state : FalsifyState X Y) : ℝ :=
  measureModelLoss law loss state.current +
    (state.accepted : ℝ) * (epsilon / 2)

/-- Theorem 12's local conclusions under general population semantics. -/
def MeasureFalsifyDecisionGuarantee
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) (loss : BoundedLoss Y) (epsilon : ℝ)
    (state : FalsifyState X Y) (proposal : ProposedUpdate X Y)
    (decision : CertificateDecision) : Prop :=
  let next := falsifyStepFromDecision state proposal decision
  (decision = .rejected →
      ∀ mu Delta, epsilon ≤ mu * Delta →
        ¬ MeasureCertificateOfSuboptimality law loss state.current proposal.group
          proposal.replacement mu Delta) ∧
    (decision = .accepted →
      ∃ mu Delta,
        MeasureCertificateOfSuboptimality law loss state.current proposal.group
          proposal.replacement mu Delta ∧
        epsilon / 2 ≤ mu * Delta ∧
        measureGroupLoss law loss next.current proposal.group =
          measureGroupLoss law loss proposal.replacement proposal.group ∧
        measureModelLoss law loss next.current ≤
          measureModelLoss law loss state.current - epsilon / 2)

/-- Algorithm 2 semantics plus general-population `ListUpdate` calculus give
all local Algorithm 3 conclusions. -/
theorem measureFalsifyDecisionGuarantee_of_checkerDecisionGuaranteed
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    (epsilon : ℝ) (state : FalsifyState X Y)
    (hstate : MeasurableModel state.current)
    (proposal : ProposedUpdate X Y)
    (hproposal : MeasureProposalMeasurable proposal)
    (decision : CertificateDecision)
    (hchecker : MeasureCheckerDecisionGuaranteed law loss epsilon
      (proposalSubmission state proposal) decision) :
    MeasureFalsifyDecisionGuarantee law loss epsilon state proposal decision := by
  unfold MeasureFalsifyDecisionGuarantee
  dsimp only
  constructor
  · intro hrejected mu Delta hlarge
    simpa [proposalSubmission] using hchecker.1 hrejected mu Delta hlarge
  · intro haccepted
    obtain ⟨mu, Delta, hcert, hlarge⟩ := hchecker.2 haccepted
    have hcert' : MeasureCertificateOfSuboptimality law loss state.current
        proposal.group proposal.replacement mu Delta := by
      simpa [proposalSubmission] using hcert
    refine ⟨mu, Delta, hcert', hlarge, ?_, ?_⟩
    · simp [falsifyStepFromDecision, haccepted,
        measureListUpdate_groupLoss_eq]
    · have hprogress :=
        (theorem9_measure_listUpdate_progress (law := law) hloss hstate
          hproposal.2 hproposal.1 hcert').2
      have htarget :
          measureModelLoss law loss
              (listUpdate state.current proposal.group proposal.replacement) ≤
            measureModelLoss law loss state.current - epsilon / 2 :=
        hprogress.trans (by linarith)
      simpa [falsifyStepFromDecision, haccepted] using htarget

/-- A locally guaranteed decision cannot increase population loss plus the
accepted-update accounting term. -/
theorem measureFalsifyStepFromDecision_potential_le
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) (loss : BoundedLoss Y)
    (epsilon : ℝ) (state : FalsifyState X Y)
    (proposal : ProposedUpdate X Y) (decision : CertificateDecision)
    (hguarantee : MeasureFalsifyDecisionGuarantee law loss epsilon
      state proposal decision) :
    measureFalsifyPotential law loss epsilon
        (falsifyStepFromDecision state proposal decision) ≤
      measureFalsifyPotential law loss epsilon state := by
  unfold measureFalsifyPotential
  cases decision with
  | rejected => simp [falsifyStepFromDecision]
  | accepted =>
      obtain ⟨mu, Delta, _, _, _, hloss⟩ := hguarantee.2 rfl
      simp only [falsifyStepFromDecision] at hloss ⊢
      push_cast
      nlinarith

/-! ## Complete adaptive and high-probability general Theorem 12 -/

/-- All local source guarantees along the literal adaptive execution. -/
def MeasureAdaptiveFalsifyRunAuxGuaranteed
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) (loss : BoundedLoss Y) (epsilon : ℝ)
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
        MeasureFalsifyDecisionGuarantee law loss epsilon state proposal decision ∧
          MeasureAdaptiveFalsifyRunAuxGuaranteed law loss epsilon sample initial strategy
            remaining (decision :: reverseTranscript)
      else True

/-- Deterministic good-run predicate for general-population Algorithm 3. -/
def MeasureAdaptiveFalsifyRunGuaranteed
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) (loss : BoundedLoss Y) (epsilon : ℝ)
    {n : ℕ} (sample : Fin n → X × Y) (U : ℕ) (initial : Model X Y)
    (strategy : AdaptiveProposalStrategy X Y) : Prop :=
  MeasureAdaptiveFalsifyRunAuxGuaranteed law loss epsilon sample initial strategy U []

/-- Algorithm 2's actual-run guarantee transfers to every reached Algorithm 3
decision under the arbitrary population law. -/
theorem measureAdaptiveFalsifyRunAuxGuaranteed_of_checkerRunAuxGuaranteed
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    (epsilon : ℝ) {n : ℕ} (sample : Fin n → X × Y)
    (initial : Model X Y) (hinitial : MeasurableModel initial)
    (strategy : AdaptiveProposalStrategy X Y)
    (hstrategy : ∀ transcript, MeasureProposalMeasurable (strategy transcript)) :
    ∀ (remaining : ℕ) (reverseTranscript : List CertificateDecision),
      MeasureCheckerRunAuxGuaranteed law loss epsilon sample
          (falsifySubmissionStrategy initial strategy)
          remaining reverseTranscript →
        MeasureAdaptiveFalsifyRunAuxGuaranteed law loss epsilon sample initial strategy
          remaining reverseTranscript := by
  intro remaining
  induction remaining with
  | zero => intro reverseTranscript _; trivial
  | succ remaining ih =>
      intro reverseTranscript hchecker
      by_cases hguard : (numberAccepted reverseTranscript : ℝ) ≤ 2 / epsilon
      · simp only [MeasureCheckerRunAuxGuaranteed,
          MeasureAdaptiveFalsifyRunAuxGuaranteed, hguard, if_pos] at hchecker ⊢
        let publicTranscript := reverseTranscript.reverse
        let state := falsifyStateFromTranscript initial strategy publicTranscript
        let proposal := strategy publicTranscript
        let decision := certificateCheckerDecision epsilon loss sample
          (proposalSubmission state proposal)
        have hcheckerLocal : MeasureCheckerDecisionGuaranteed law loss epsilon
            (proposalSubmission state proposal) decision := by
          simpa [falsifySubmissionStrategy, publicTranscript, state, proposal,
            decision] using hchecker.1
        have hstate : MeasurableModel state.current :=
          measurableModel_falsifyStateFromTranscript hinitial hstrategy publicTranscript
        refine ⟨measureFalsifyDecisionGuarantee_of_checkerDecisionGuaranteed
            law hloss epsilon state hstate proposal (hstrategy publicTranscript)
              decision hcheckerLocal, ?_⟩
        exact ih _ hchecker.2
      · simp [MeasureCheckerRunAuxGuaranteed,
          MeasureAdaptiveFalsifyRunAuxGuaranteed, hguard]

/-- The general-population potential never increases along a good run. -/
theorem measureAdaptiveFalsifyRunAux_potential_le
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) (loss : BoundedLoss Y) (epsilon : ℝ)
    {n : ℕ} (sample : Fin n → X × Y) (initial : Model X Y)
    (strategy : AdaptiveProposalStrategy X Y) :
    ∀ (remaining : ℕ) (reverseTranscript : List CertificateDecision),
      MeasureAdaptiveFalsifyRunAuxGuaranteed law loss epsilon sample initial strategy
          remaining reverseTranscript →
      let start := falsifyStateFromTranscript initial strategy
        reverseTranscript.reverse
      let finalTranscript := certificateCheckerRunAux epsilon loss sample
        (falsifySubmissionStrategy initial strategy) remaining reverseTranscript
      let final := falsifyStateFromTranscript initial strategy finalTranscript
      measureFalsifyPotential law loss epsilon final ≤
        measureFalsifyPotential law loss epsilon start := by
  intro remaining
  induction remaining with
  | zero => intro reverseTranscript _; simp [certificateCheckerRunAux]
  | succ remaining ih =>
      intro reverseTranscript hguaranteed
      by_cases hguard : (numberAccepted reverseTranscript : ℝ) ≤ 2 / epsilon
      · let publicTranscript := reverseTranscript.reverse
        let state := falsifyStateFromTranscript initial strategy publicTranscript
        let proposal := strategy publicTranscript
        let decision := certificateCheckerDecision epsilon loss sample
          (proposalSubmission state proposal)
        have hparts :
            MeasureFalsifyDecisionGuarantee law loss epsilon state proposal decision ∧
              MeasureAdaptiveFalsifyRunAuxGuaranteed law loss epsilon sample initial
                strategy remaining (decision :: reverseTranscript) := by
          simpa [MeasureAdaptiveFalsifyRunAuxGuaranteed, hguard, publicTranscript,
            state, proposal, decision] using hguaranteed
        have hstep := measureFalsifyStepFromDecision_potential_le law loss epsilon
          state proposal decision hparts.1
        have hnextState :
            falsifyStateFromTranscript initial strategy
                (decision :: reverseTranscript).reverse =
              falsifyStepFromDecision state proposal decision := by
          simp only [List.reverse_cons]
          simpa [state, proposal, publicTranscript] using
            falsifyStateFromTranscript_append_singleton initial strategy
              publicTranscript decision
        have htail := ih (decision :: reverseTranscript) hparts.2
        have hstep' : measureFalsifyPotential law loss epsilon
              (falsifyStateFromTranscript initial strategy
                (decision :: reverseTranscript).reverse) ≤
            measureFalsifyPotential law loss epsilon
              (falsifyStateFromTranscript initial strategy reverseTranscript.reverse) := by
          rw [hnextState]
          simpa [state, publicTranscript] using hstep
        simp only [certificateCheckerRunAux, hguard, if_pos]
        exact htail.trans hstep'
      · simp [certificateCheckerRunAux, hguard]

/-- The loss budget forces the literal checker guard to remain open. -/
theorem measureAdaptiveFalsifyRunAux_length_eq
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    {n : ℕ} (sample : Fin n → X × Y) (initial : Model X Y)
    (hinitial : MeasurableModel initial)
    (strategy : AdaptiveProposalStrategy X Y)
    (hstrategy : ∀ transcript, MeasureProposalMeasurable (strategy transcript)) :
    ∀ (remaining : ℕ) (reverseTranscript : List CertificateDecision),
      MeasureAdaptiveFalsifyRunAuxGuaranteed law loss epsilon sample initial strategy
          remaining reverseTranscript →
      measureFalsifyPotential law loss epsilon
          (falsifyStateFromTranscript initial strategy reverseTranscript.reverse) ≤
        measureModelLoss law loss initial →
      (certificateCheckerRunAux epsilon loss sample
          (falsifySubmissionStrategy initial strategy)
          remaining reverseTranscript).length =
        reverseTranscript.length + remaining := by
  intro remaining
  induction remaining with
  | zero => intro reverseTranscript _ _; simp [certificateCheckerRunAux]
  | succ remaining ih =>
      intro reverseTranscript hguaranteed hpotential
      let publicTranscript := reverseTranscript.reverse
      let state := falsifyStateFromTranscript initial strategy publicTranscript
      have hstateAccepted : state.accepted = numberAccepted reverseTranscript := by
        dsimp [state, publicTranscript]
        rw [falsifyStateFromTranscript_accepted, numberAccepted_reverse]
      have hstateMeasurable : MeasurableModel state.current :=
        measurableModel_falsifyStateFromTranscript hinitial hstrategy publicTranscript
      have hstateNonneg : 0 ≤ measureModelLoss law loss state.current :=
        measureModelLoss_nonneg law hloss hstateMeasurable
      have hinitialOne : measureModelLoss law loss initial ≤ 1 :=
        measureModelLoss_le_one law hloss hinitial
      have hacceptedMul : (state.accepted : ℝ) * epsilon ≤ 2 := by
        unfold measureFalsifyPotential at hpotential
        nlinarith
      have hguard : (numberAccepted reverseTranscript : ℝ) ≤ 2 / epsilon := by
        apply (le_div_iff₀ hepsilon).2
        simpa [hstateAccepted] using hacceptedMul
      let proposal := strategy publicTranscript
      let decision := certificateCheckerDecision epsilon loss sample
        (proposalSubmission state proposal)
      have hparts :
          MeasureFalsifyDecisionGuarantee law loss epsilon state proposal decision ∧
            MeasureAdaptiveFalsifyRunAuxGuaranteed law loss epsilon sample initial strategy
              remaining (decision :: reverseTranscript) := by
        simpa [MeasureAdaptiveFalsifyRunAuxGuaranteed, hguard, publicTranscript,
          state, proposal, decision] using hguaranteed
      have hstep := measureFalsifyStepFromDecision_potential_le law loss epsilon
        state proposal decision hparts.1
      have hnextState :
          falsifyStateFromTranscript initial strategy
              (decision :: reverseTranscript).reverse =
            falsifyStepFromDecision state proposal decision := by
        simp only [List.reverse_cons]
        simpa [state, proposal, publicTranscript] using
          falsifyStateFromTranscript_append_singleton initial strategy
            publicTranscript decision
      have hnextPotential :
          measureFalsifyPotential law loss epsilon
              (falsifyStateFromTranscript initial strategy
                (decision :: reverseTranscript).reverse) ≤
            measureModelLoss law loss initial := by
        rw [hnextState]
        exact hstep.trans (by simpa [state, publicTranscript] using hpotential)
      have htail := ih (decision :: reverseTranscript) hparts.2 hnextPotential
      simp only [certificateCheckerRunAux, hguard, if_pos]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

/-- Good executions process all requested submissions. -/
theorem measureAdaptiveFalsifyTranscript_length_eq
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    {n : ℕ} (sample : Fin n → X × Y) (U : ℕ)
    (initial : Model X Y) (hinitial : MeasurableModel initial)
    (strategy : AdaptiveProposalStrategy X Y)
    (hstrategy : ∀ transcript, MeasureProposalMeasurable (strategy transcript))
    (hguaranteed : MeasureAdaptiveFalsifyRunGuaranteed law loss epsilon sample U
      initial strategy) :
    (adaptiveFalsifyTranscript epsilon loss sample U initial strategy).length = U := by
  have hpotential : measureFalsifyPotential law loss epsilon
      (falsifyStateFromTranscript initial strategy [].reverse) ≤
      measureModelLoss law loss initial := by
    simp [measureFalsifyPotential, falsifyStateFromTranscript, falsifyReplayAux,
      initialFalsifyState]
  have hlength := measureAdaptiveFalsifyRunAux_length_eq law hloss epsilon hepsilon
    sample initial hinitial strategy hstrategy U [] hguaranteed hpotential
  simpa [adaptiveFalsifyTranscript, certificateCheckerRun] using hlength

/-- Good executions accept at most `2 / epsilon` updates. -/
theorem measureAdaptiveFalsifyAndUpdate_accepted_le
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    {n : ℕ} (sample : Fin n → X × Y) (U : ℕ)
    (initial : Model X Y) (hinitial : MeasurableModel initial)
    (strategy : AdaptiveProposalStrategy X Y)
    (hstrategy : ∀ transcript, MeasureProposalMeasurable (strategy transcript))
    (hguaranteed : MeasureAdaptiveFalsifyRunGuaranteed law loss epsilon sample U
      initial strategy) :
    ((adaptiveFalsifyAndUpdate epsilon loss sample U initial strategy).accepted : ℝ) ≤
      2 / epsilon := by
  have hpotential := measureAdaptiveFalsifyRunAux_potential_le law loss epsilon sample
    initial strategy U [] hguaranteed
  have hfinalMeasurable : MeasurableModel
      (adaptiveFalsifyAndUpdate epsilon loss sample U initial strategy).current := by
    apply measurableModel_falsifyStateFromTranscript hinitial hstrategy
  have hfinalNonneg : 0 ≤ measureModelLoss law loss
      (adaptiveFalsifyAndUpdate epsilon loss sample U initial strategy).current :=
    measureModelLoss_nonneg law hloss hfinalMeasurable
  have hinitialOne : measureModelLoss law loss initial ≤ 1 :=
    measureModelLoss_le_one law hloss hinitial
  have hpotential' : measureFalsifyPotential law loss epsilon
      (adaptiveFalsifyAndUpdate epsilon loss sample U initial strategy) ≤
      measureModelLoss law loss initial := by
    simpa [adaptiveFalsifyAndUpdate, adaptiveFalsifyTranscript,
      certificateCheckerRun, measureFalsifyPotential, falsifyStateFromTranscript,
      falsifyReplayAux, initialFalsifyState] using hpotential
  have hmul :
      ((adaptiveFalsifyAndUpdate epsilon loss sample U initial strategy).accepted : ℝ) *
        epsilon ≤ 2 := by
    unfold measureFalsifyPotential at hpotential'
    nlinarith
  exact (le_div_iff₀ hepsilon).2 hmul

/-- The complete deterministic conclusion of general-population Theorem 12. -/
def MeasureAdaptiveFalsifyRunConclusion
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) (loss : BoundedLoss Y) (epsilon : ℝ)
    {n : ℕ} (sample : Fin n → X × Y) (U : ℕ) (initial : Model X Y)
    (strategy : AdaptiveProposalStrategy X Y) : Prop :=
  MeasureAdaptiveFalsifyRunGuaranteed law loss epsilon sample U initial strategy ∧
    (adaptiveFalsifyTranscript epsilon loss sample U initial strategy).length = U ∧
    ((adaptiveFalsifyAndUpdate epsilon loss sample U initial strategy).accepted : ℝ) ≤
      2 / epsilon

/-- A good induced checker execution gives the full Algorithm 3 conclusion. -/
theorem measureAdaptiveFalsifyRunConclusion_of_checkerRunGuaranteed
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    {n : ℕ} (sample : Fin n → X × Y) (U : ℕ)
    (initial : Model X Y) (hinitial : MeasurableModel initial)
    (strategy : AdaptiveProposalStrategy X Y)
    (hstrategy : ∀ transcript, MeasureProposalMeasurable (strategy transcript))
    (hchecker : MeasureCheckerRunAuxGuaranteed law loss epsilon sample
      (falsifySubmissionStrategy initial strategy) U []) :
    MeasureAdaptiveFalsifyRunConclusion law loss epsilon sample U initial strategy := by
  have hrun : MeasureAdaptiveFalsifyRunGuaranteed law loss epsilon sample U
      initial strategy :=
    measureAdaptiveFalsifyRunAuxGuaranteed_of_checkerRunAuxGuaranteed law hloss epsilon
      sample initial hinitial strategy hstrategy U [] hchecker
  exact ⟨hrun,
    measureAdaptiveFalsifyTranscript_length_eq law hloss epsilon hepsilon sample U
      initial hinitial strategy hstrategy hrun,
    measureAdaptiveFalsifyAndUpdate_accepted_le law hloss epsilon hepsilon sample U
      initial hinitial strategy hstrategy hrun⟩

/-- Probability that general-population Algorithm 3 violates Theorem 12. -/
def measureAdaptiveFalsifyAndUpdateFailure
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) (loss : BoundedLoss Y)
    (epsilon : ℝ) (n U : ℕ) (initial : Model X Y)
    (strategy : AdaptiveProposalStrategy X Y) : ℝ :=
  (finiteIIDSampleLaw law n).real {sample |
    ¬ MeasureAdaptiveFalsifyRunConclusion law loss epsilon sample U initial strategy}

/-- A bad Algorithm 3 execution is a bad execution of its induced checker. -/
theorem measureAdaptiveFalsifyAndUpdateFailure_le_checkerFailure
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (n U : ℕ)
    (initial : Model X Y) (hinitial : MeasurableModel initial)
    (strategy : AdaptiveProposalStrategy X Y)
    (hstrategy : ∀ transcript, MeasureProposalMeasurable (strategy transcript)) :
    measureAdaptiveFalsifyAndUpdateFailure law loss epsilon n U initial strategy ≤
      measureCertificateCheckerRunGuaranteeFailure law loss epsilon n U
        (falsifySubmissionStrategy initial strategy) := by
  letI : IsProbabilityMeasure (finiteIIDSampleLaw law n) := by
    dsimp [finiteIIDSampleLaw]
    infer_instance
  unfold measureAdaptiveFalsifyAndUpdateFailure
    measureCertificateCheckerRunGuaranteeFailure
  refine measureReal_mono ?_ (measure_ne_top (finiteIIDSampleLaw law n) _)
  intro sample hbad
  intro hchecker
  exact hbad (measureAdaptiveFalsifyRunConclusion_of_checkerRunGuaranteed
    law hloss epsilon hepsilon sample U initial hinitial strategy hstrategy hchecker)

/-- Theorem 12 for an arbitrary measurable population and every adaptive
proposal strategy.  The exact sparse-transcript failure bound also repairs the
undefined `delta'` in the printed theorem. -/
theorem theorem12_measure_adaptive_falsifyAndUpdate
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (n U : ℕ)
    (hcount : 0 < n) (initial : Model X Y) (hinitial : MeasurableModel initial)
    (strategy : AdaptiveProposalStrategy X Y)
    (hstrategy : ∀ transcript, MeasureProposalMeasurable (strategy transcript)) :
    measureAdaptiveFalsifyAndUpdateFailure law loss epsilon n U initial strategy ≤
      (U * (U + 1) ^ checkerAcceptanceBudget epsilon : ℕ) * 2 *
        Real.exp (-(n : ℝ) * epsilon ^ 2 / 32) := by
  calc
    measureAdaptiveFalsifyAndUpdateFailure law loss epsilon n U initial strategy ≤
        measureCertificateCheckerRunGuaranteeFailure law loss epsilon n U
          (falsifySubmissionStrategy initial strategy) :=
      measureAdaptiveFalsifyAndUpdateFailure_le_checkerFailure law hloss epsilon
        hepsilon n U initial hinitial strategy hstrategy
    _ ≤ (U * (U + 1) ^ checkerAcceptanceBudget epsilon : ℕ) * 2 *
          Real.exp (-(n : ℝ) * epsilon ^ 2 / 32) :=
      theorem11_measure_adaptive_certificateCheckerRun law hloss epsilon hepsilon n U
        hcount (falsifySubmissionStrategy initial strategy)
          (measureSubmissionMeasurable_falsifySubmissionStrategy hinitial hstrategy)

end

end GHKR22BiasBounties

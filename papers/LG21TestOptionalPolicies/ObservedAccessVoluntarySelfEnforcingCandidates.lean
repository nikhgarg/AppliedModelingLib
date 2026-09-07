import LG21TestOptionalPolicies.SourceTimedTwoSidedCandidateAdapter
import LG21TestOptionalPolicies.ObservedAccessReportRequiredPositiveMassAllTakeWitness

/-!
# Source-timed self-enforcing positive-mass candidates for observed access

The generic `TwoSidedPositiveMassClosedCandidateProfile` is useful when both
candidate branches carry an output function.  A Section 4 boundary profile,
however, can have only one attained branch.  This module therefore records the
same semantic obligations directly at the source action timing, with every
cross-branch comparison guarded by positive mass of the alternative branch.

This is important for the voluntary protocols.  At an all-active profile, the
unattained branch has neither a PBO identity nor a best-response comparison.
Instead, a proposed positive-mass departure must supply its own attained PBOs
and satisfy the same member-response and outsider-closure tests.  The carrier
below does not assert that no such departure exists; it only makes explicit
what a source-timed positive-mass candidate must prove.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib MeasureTheory ProbabilityTheory Set
open AppliedModelingLib.Probability
open scoped ENNReal NNReal ProbabilityTheory

/-! ## Optional testing -/

/-- The literal source-law event for the optional full action `take &&
report`.  The definition retains the two decision times rather than treating
the observed report bit as a score-only action. -/
abbrev lg21OptionalCandidateReportBranch
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (A : LG21OptionalSourceTimedActions Base) : Set Omega :=
  lg21OptionalSourceReportEvent base score skill A.takeDecision A.reportDecision

/-- The literal complement of the optional full action.  It includes both a
post-score withholding history and a pre-score no-take history. -/
abbrev lg21OptionalCandidateNoReportBranch
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (A : LG21OptionalSourceTimedActions Base) : Set Omega :=
  lg21OptionalSourceNoReportEvent base score skill A.takeDecision A.reportDecision

/-- The best feasible post-score continuation for a student who has taken the
optional test.  This is only used inside obligations guarded by a positive
no-report branch, so the definition never turns a value at an unattained branch
into a PBO assertion. -/
def lg21OptionalSourceTimedBestContinuationPayoff
    {Base : Type*} [MeasurableSpace Base]
    (A : LG21OptionalSourceTimedActions Base)
    (publicBase : Base) (observedScore : ℝ) : ℝ :=
  max (A.reportedPayoff publicBase observedScore) (A.noReportPayoff publicBase)

/-- Ex-ante payoff from taking the optional test and then choosing the better
of reporting and withholding after the score is observed. -/
def lg21OptionalSourceTimedBestContinuationExpectedPayoff
    {Base : Type*} [MeasurableSpace Base]
    (A : LG21OptionalSourceTimedActions Base)
    (latentSkill : ℝ) (publicBase : Base) : ℝ :=
  ∫ observedScore,
    lg21OptionalSourceTimedBestContinuationPayoff A publicBase observedScore
      ∂A.testLaw latentSkill publicBase

/-- A self-enforcing optional candidate at the source action timing.

`source_timed` supplies measurability, literal public channels, and PBO
identities only for attained positive branches.  The response/closure fields
are deliberately guarded by positive no-report mass.  Thus they use a
no-report PBO only after that action is actually present in the candidate;
they cannot turn an arbitrary value at a null branch into a best-response
assumption.

The score-stage response fields are separate from both pre-score taking
responses.  The latter compare against the best post-score continuation, not
merely against the candidate's prescribed report rule, so a no-taker is not
silently prevented from choosing a different feasible score-stage action after
testing.
-/
structure LG21OptionalSourceTimedPositiveMassSelfEnforcingCandidate
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature) where
  source_timed : LG21ObservedAccessOptionalPositiveMassRefinedEquilibrium
    M haccess testFeature
  active_report_positive : 0 <
    (lg21ContinuousGaussianAccessPopulationLaw M)
      (lg21OptionalCandidateReportBranch
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) source_timed.actions)
  /-- If a no-report branch is attained, the best post-score continuation is
  integrable under every literal Gaussian test law.  This makes the ex-ante
  taking comparisons below a genuine source payoff. -/
  best_continuation_integrable_if_noReport_positive : ∀ hnoReport : 0 <
      (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21OptionalCandidateNoReportBranch
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature)) source_timed.actions),
    ∀ latentSkill publicBase,
      Integrable
        (fun observedScore =>
          lg21OptionalSourceTimedBestContinuationPayoff source_timed.actions
            publicBase observedScore)
        (source_timed.actions.testLaw latentSkill publicBase)
  /-- On two attained action branches, actual reporters weakly prefer their
  post-score reporting action to the candidate's attained no-report action. -/
  report_members_weakly_respond_if_noReport_positive : ∀ hnoReport : 0 <
      (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21OptionalCandidateNoReportBranch
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature)) source_timed.actions),
    ∀ᵐ student ∂(lg21ContinuousGaussianAccessPopulationLaw M).restrict
      (lg21OptionalCandidateReportBranch
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) source_timed.actions),
      source_timed.actions.noReportPayoff
        (lg21ContinuousPopulationBase testFeature student) ≤
      source_timed.actions.reportedPayoff
        (lg21ContinuousPopulationBase testFeature student)
        (lg21ContinuousPopulationFeature testFeature student)
  /-- A no-report member who took the test weakly prefers withholding to
  reporting at the realized score, whenever the no-report branch is attained. -/
  withholding_members_weakly_respond_if_positive : ∀ hnoReport : 0 <
      (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21OptionalCandidateNoReportBranch
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature)) source_timed.actions),
    ∀ᵐ student ∂(lg21ContinuousGaussianAccessPopulationLaw M).restrict
      {student |
        source_timed.actions.takeDecision
          (lg21ContinuousPopulationSkill student)
          (lg21ContinuousPopulationBase testFeature student) = true ∧
        source_timed.actions.reportDecision
          (lg21ContinuousPopulationBase testFeature student)
          (lg21ContinuousPopulationFeature testFeature student) = false},
      source_timed.actions.reportedPayoff
        (lg21ContinuousPopulationBase testFeature student)
        (lg21ContinuousPopulationFeature testFeature student) ≤
      source_timed.actions.noReportPayoff
        (lg21ContinuousPopulationBase testFeature student)
  /-- A taker weakly prefers the best feasible ex-ante continuation from
  taking to the attained no-report action. -/
  take_members_weakly_respond_if_noReport_positive : ∀ hnoReport : 0 <
      (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21OptionalCandidateNoReportBranch
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature)) source_timed.actions),
    ∀ᵐ student ∂(lg21ContinuousGaussianAccessPopulationLaw M).restrict
      {student | source_timed.actions.takeDecision
        (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student) = true},
      source_timed.actions.noReportPayoff
        (lg21ContinuousPopulationBase testFeature student) ≤
      lg21OptionalSourceTimedBestContinuationExpectedPayoff source_timed.actions
        (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student)
  /-- A no-take member weakly prefers not taking to the best feasible ex-ante
  continuation from taking, whenever the no-report branch is attained. -/
  noTake_members_weakly_respond_if_positive : ∀ hnoReport : 0 <
      (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21OptionalCandidateNoReportBranch
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature)) source_timed.actions),
    ∀ᵐ student ∂(lg21ContinuousGaussianAccessPopulationLaw M).restrict
      {student | source_timed.actions.takeDecision
        (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student) = false},
      lg21OptionalSourceTimedBestContinuationExpectedPayoff source_timed.actions
        (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student) ≤
      source_timed.actions.noReportPayoff
        (lg21ContinuousPopulationBase testFeature student)
  /-- Eligible outsiders to the report branch have no strict score-stage or
  pre-score gain from entering it.  The source histories are stated
  separately, so the closure test respects the information available when
  each decision is made. -/
  report_outsiders_closed_under_strict_gain_if_noReport_positive : ∀ hnoReport : 0 <
      (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21OptionalCandidateNoReportBranch
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature)) source_timed.actions),
    (∀ᵐ student ∂(lg21ContinuousGaussianAccessPopulationLaw M).restrict
      {student |
        source_timed.actions.takeDecision
          (lg21ContinuousPopulationSkill student)
          (lg21ContinuousPopulationBase testFeature student) = true ∧
        source_timed.actions.reportDecision
          (lg21ContinuousPopulationBase testFeature student)
          (lg21ContinuousPopulationFeature testFeature student) = false},
      source_timed.actions.reportedPayoff
        (lg21ContinuousPopulationBase testFeature student)
        (lg21ContinuousPopulationFeature testFeature student) ≤
      source_timed.actions.noReportPayoff
        (lg21ContinuousPopulationBase testFeature student)) ∧
    (∀ᵐ student ∂(lg21ContinuousGaussianAccessPopulationLaw M).restrict
      {student | source_timed.actions.takeDecision
        (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student) = false},
      lg21OptionalSourceTimedBestContinuationExpectedPayoff source_timed.actions
        (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student) ≤
      source_timed.actions.noReportPayoff
        (lg21ContinuousPopulationBase testFeature student))
  /-- Takers have no strict gain from leaving for an attained no-report branch
  at the pre-score decision time. -/
  noReport_outsiders_closed_under_strict_gain_if_positive : ∀ hnoReport : 0 <
      (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21OptionalCandidateNoReportBranch
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature)) source_timed.actions),
    ∀ᵐ student ∂(lg21ContinuousGaussianAccessPopulationLaw M).restrict
      {student | source_timed.actions.takeDecision
        (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student) = true},
      source_timed.actions.noReportPayoff
        (lg21ContinuousPopulationBase testFeature student) ≤
      lg21OptionalSourceTimedBestContinuationExpectedPayoff source_timed.actions
        (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student)

/-! ## Report-required testing -/

/-- A self-enforcing positive-mass candidate for the report-required
protocol.  `source_timed` records the literal pre-score take action and its
two public channels.  The cross-branch comparisons are required only when the
no-take branch has positive mass, at which point `source_timed` also supplies
its PBO. -/
structure LG21ReportRequiredSourceTimedPositiveMassSelfEnforcingCandidate
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature) where
  selected : LG21ReportRequiredSequentialEquilibriumData ℝ
    (LG21NonTestFeature Feature testFeature -> ℝ) ℝ
  source_timed :
    letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
    LG21ReportRequiredPositiveMassRefinedSourceEquilibrium
      (lg21ContinuousGaussianAccessPopulationLaw M)
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) selected
      (M.noiseVariance testFeature)
  active_take_positive : 0 < (lg21ContinuousGaussianAccessPopulationLaw M)
    {student | selected.takeDecision
      (lg21ContinuousPopulationSkill student)
      (lg21ContinuousPopulationBase testFeature student) = true}
  /-- Actual takers weakly prefer taking whenever the candidate also has an
  attained no-take branch. -/
  take_members_weakly_respond_if_noTake_positive : ∀ hnoTake : 0 <
      (lg21ContinuousGaussianAccessPopulationLaw M)
        {student | selected.takeDecision
          (lg21ContinuousPopulationSkill student)
          (lg21ContinuousPopulationBase testFeature student) = false},
    ∀ᵐ student ∂(lg21ContinuousGaussianAccessPopulationLaw M).restrict
      {student | selected.takeDecision
        (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student) = true},
      selected.noReportPayoff
        (lg21ContinuousPopulationBase testFeature student) ≤
      lg21ReportRequiredSequentialTakeExpectedPayoff selected
        (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student)
  /-- Actual no-takers weakly prefer no-taking whenever their branch is
  attained and hence has its own candidate PBO. -/
  noTake_members_weakly_respond_if_positive : ∀ hnoTake : 0 <
      (lg21ContinuousGaussianAccessPopulationLaw M)
        {student | selected.takeDecision
          (lg21ContinuousPopulationSkill student)
          (lg21ContinuousPopulationBase testFeature student) = false},
    ∀ᵐ student ∂(lg21ContinuousGaussianAccessPopulationLaw M).restrict
      {student | selected.takeDecision
        (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student) = false},
      lg21ReportRequiredSequentialTakeExpectedPayoff selected
        (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student) ≤
      selected.noReportPayoff
        (lg21ContinuousPopulationBase testFeature student)
  /-- No no-taker has a strict gain from the attained taking branch. -/
  take_outsiders_closed_under_strict_gain_if_noTake_positive : ∀ hnoTake : 0 <
      (lg21ContinuousGaussianAccessPopulationLaw M)
        {student | selected.takeDecision
          (lg21ContinuousPopulationSkill student)
          (lg21ContinuousPopulationBase testFeature student) = false},
    ∀ᵐ student ∂(lg21ContinuousGaussianAccessPopulationLaw M).restrict
      {student | selected.takeDecision
        (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student) = false},
      lg21ReportRequiredSequentialTakeExpectedPayoff selected
        (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student) ≤
      selected.noReportPayoff
        (lg21ContinuousPopulationBase testFeature student)
  /-- No taker has a strict gain from an attained no-take branch. -/
  noTake_outsiders_closed_under_strict_gain_if_positive : ∀ hnoTake : 0 <
      (lg21ContinuousGaussianAccessPopulationLaw M)
        {student | selected.takeDecision
          (lg21ContinuousPopulationSkill student)
          (lg21ContinuousPopulationBase testFeature student) = false},
    ∀ᵐ student ∂(lg21ContinuousGaussianAccessPopulationLaw M).restrict
      {student | selected.takeDecision
        (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student) = true},
      selected.noReportPayoff
        (lg21ContinuousPopulationBase testFeature student) ≤
      lg21ReportRequiredSequentialTakeExpectedPayoff selected
        (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student)

/-! ## Boundary constructors -/

/-- Turn an all-take/all-report optional source profile into a self-enforcing
positive-mass candidate.  The proof does not select an output at the empty
no-report branch: every field that would compare against that branch first
receives a positive-mass proof, which contradicts the displayed action law. -/
def lg21OptionalSourceTimedPositiveMassSelfEnforcingCandidate_of_allTakeAllReport
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (E : LG21ObservedAccessOptionalPositiveMassRefinedEquilibrium
      M haccess testFeature)
    (hallTake : ∀ latentSkill publicBase,
      E.actions.takeDecision latentSkill publicBase = true)
    (hallReport : ∀ publicBase observedScore,
      E.actions.reportDecision publicBase observedScore = true) :
    LG21OptionalSourceTimedPositiveMassSelfEnforcingCandidate
      M haccess testFeature := by
  let law := lg21ContinuousGaussianAccessPopulationLaw M
  let base := lg21ContinuousPopulationBase testFeature
  let score := lg21ContinuousPopulationFeature testFeature
  let skill := lg21ContinuousPopulationSkill (Feature := Feature)
  letI : IsProbabilityMeasure law :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  have hreportEvent :
      lg21OptionalCandidateReportBranch base score skill E.actions = Set.univ := by
    ext student
    simp [lg21OptionalCandidateReportBranch, lg21OptionalSourceReportEvent,
      hallTake, hallReport]
  have hnoReportEvent :
      lg21OptionalCandidateNoReportBranch base score skill E.actions = ∅ := by
    ext student
    simp [lg21OptionalCandidateNoReportBranch, lg21OptionalSourceNoReportEvent,
      hallTake, hallReport]
  have hreportPositive : 0 < law
      (lg21OptionalCandidateReportBranch base score skill E.actions) := by
    rw [hreportEvent]
    simp
  have hnoReportNotPositive : ¬ 0 < law
      (lg21OptionalCandidateNoReportBranch base score skill E.actions) := by
    rw [hnoReportEvent]
    simp
  refine
    { source_timed := E
      active_report_positive := by
        simpa [law, base, score, skill] using hreportPositive
      best_continuation_integrable_if_noReport_positive := by
        intro hnoReport
        exfalso
        apply hnoReportNotPositive
        simpa [law, base, score, skill] using hnoReport
      report_members_weakly_respond_if_noReport_positive := by
        intro hnoReport
        exfalso
        apply hnoReportNotPositive
        simpa [law, base, score, skill] using hnoReport
      withholding_members_weakly_respond_if_positive := by
        intro hnoReport
        exfalso
        apply hnoReportNotPositive
        simpa [law, base, score, skill] using hnoReport
      take_members_weakly_respond_if_noReport_positive := by
        intro hnoReport
        exfalso
        apply hnoReportNotPositive
        simpa [law, base, score, skill] using hnoReport
      noTake_members_weakly_respond_if_positive := by
        intro hnoReport
        exfalso
        apply hnoReportNotPositive
        simpa [law, base, score, skill] using hnoReport
      report_outsiders_closed_under_strict_gain_if_noReport_positive := by
        intro hnoReport
        exfalso
        apply hnoReportNotPositive
        simpa [law, base, score, skill] using hnoReport
      noReport_outsiders_closed_under_strict_gain_if_positive := by
        intro hnoReport
        exfalso
        apply hnoReportNotPositive
        simpa [law, base, score, skill] using hnoReport }

/-- The literal finite-coordinate Gaussian source has an all-active optional
self-enforcing positive-mass candidate.  This establishes the candidate
carrier only; it is not a theorem excluding every separately recalibrated
positive-mass departure. -/
theorem lg21ContinuousGaussianAccessPopulation_exists_optionalSelfEnforcing_allTakeAllReport
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ)) :
    ∃ C : LG21OptionalSourceTimedPositiveMassSelfEnforcingCandidate
        M haccess testFeature,
      (∀ latentSkill publicBase,
        C.source_timed.actions.takeDecision latentSkill publicBase = true) ∧
      (∀ publicBase observedScore,
        C.source_timed.actions.reportDecision publicBase observedScore = true) := by
  rcases
      lg21ContinuousGaussianAccessPopulation_exists_optionalPositiveMassRefined_allTakeAllReport
        M haccess testFeature hpriorVariance hnonTestNoiseVariance
          htestNoiseVariance with
    ⟨E, hallTake, hallReport⟩
  refine ⟨
    lg21OptionalSourceTimedPositiveMassSelfEnforcingCandidate_of_allTakeAllReport
      M haccess testFeature E hallTake hallReport,
    ?_, ?_⟩
  · exact hallTake
  · exact hallReport

/-- Turn a source-timed all-take report-required profile into a self-enforcing
positive-mass candidate.  As in the optional constructor, a hypothetical
positive no-take branch contradicts the actual all-take action law before any
null-branch PBO or best-response value can be used. -/
def lg21ReportRequiredSourceTimedPositiveMassSelfEnforcingCandidate_of_allTake
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (E : LG21ReportRequiredSequentialEquilibriumData ℝ
      (LG21NonTestFeature Feature testFeature -> ℝ) ℝ)
    (hsource :
      letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
        lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
      LG21ReportRequiredPositiveMassRefinedSourceEquilibrium
        (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) E
        (M.noiseVariance testFeature))
    (hallTake : ∀ latentSkill publicBase,
      E.takeDecision latentSkill publicBase = true) :
    LG21ReportRequiredSourceTimedPositiveMassSelfEnforcingCandidate
      M haccess testFeature := by
  let law := lg21ContinuousGaussianAccessPopulationLaw M
  let base := lg21ContinuousPopulationBase testFeature
  let skill := lg21ContinuousPopulationSkill (Feature := Feature)
  letI : IsProbabilityMeasure law :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  have htakeEvent : {student |
      E.takeDecision (skill student) (base student) = true} = Set.univ := by
    ext student
    simp [hallTake]
  have hnoTakeEvent : {student |
      E.takeDecision (skill student) (base student) = false} = ∅ := by
    ext student
    simp [hallTake]
  have htakePositive : 0 < law {student |
      E.takeDecision (skill student) (base student) = true} := by
    rw [htakeEvent]
    simp
  have hnoTakeNotPositive : ¬ 0 < law {student |
      E.takeDecision (skill student) (base student) = false} := by
    rw [hnoTakeEvent]
    simp
  refine
    { selected := E
      source_timed := by
        simpa [law, base, skill] using hsource
      active_take_positive := by
        simpa [law, base, skill] using htakePositive
      take_members_weakly_respond_if_noTake_positive := by
        intro hnoTake
        exfalso
        apply hnoTakeNotPositive
        simpa [law, base, skill] using hnoTake
      noTake_members_weakly_respond_if_positive := by
        intro hnoTake
        exfalso
        apply hnoTakeNotPositive
        simpa [law, base, skill] using hnoTake
      take_outsiders_closed_under_strict_gain_if_noTake_positive := by
        intro hnoTake
        exfalso
        apply hnoTakeNotPositive
        simpa [law, base, skill] using hnoTake
      noTake_outsiders_closed_under_strict_gain_if_positive := by
        intro hnoTake
        exfalso
        apply hnoTakeNotPositive
        simpa [law, base, skill] using hnoTake }

/-- The literal finite-coordinate Gaussian source has an all-active
report-required self-enforcing positive-mass candidate.  This result leaves
the no-take branch entirely unattained. -/
theorem lg21ContinuousGaussianAccessPopulation_exists_reportRequiredSelfEnforcing_allTake
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ)) :
    ∃ C : LG21ReportRequiredSourceTimedPositiveMassSelfEnforcingCandidate
        M haccess testFeature,
      ∀ latentSkill publicBase,
        C.selected.takeDecision latentSkill publicBase = true := by
  rcases
      lg21ContinuousGaussianAccessPopulation_exists_reportRequiredPositiveMassRefined_allTake
        M haccess testFeature hpriorVariance hnonTestNoiseVariance
          htestNoiseVariance with
    ⟨E, hsource, hallTake⟩
  refine ⟨
    lg21ReportRequiredSourceTimedPositiveMassSelfEnforcingCandidate_of_allTake
      M haccess testFeature E hsource hallTake,
    hallTake⟩
end

end LG21TestOptionalPolicies

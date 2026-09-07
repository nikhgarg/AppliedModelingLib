import LG21TestOptionalPolicies.SelectedConditionalExpectation
import AppliedModelingLib.GameTheory.Choice.Binary

/-!
# Positive-mass PBO refinement interface

This module records the semantic objects needed to state a positive-mass
refinement of LG21's equilibrium concept without assigning an arbitrary
off-path PBO to a null action branch.

The intended use is source-facing.  A candidate action profile carries its
own PBOs, and a PBO is constrained to be the conditional expectation under
the population selected by that *candidate* whenever that branch has positive
mass.  Thus a later proof may evaluate a positive-mass entry candidate using
the PBO it would actually induce.  Values assigned to null branches are not
used by this interface.

This is the candidate-PBO component of a possible source-faithful repair: the
school knows the decision functions and PBO follows those functions on an
attained positive branch. Ordinary unilateral best responses alone do not
assign a value to a null branch. The active-entry closure below evaluates a
positive-mass candidate under its own induced PBO, but it is one-directional
and is not a whole-profile equilibrium condition. Action timing, feasibility,
outsider closure, the source population, and individual best responses remain
separate obligations for a source-facing bridge.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set
open AppliedModelingLib

/--
An estimate is a PBO for `branch` only when that branch has positive mass.

The conditional expectation is taken under the restricted candidate
population.  Conditioning on the branch in this way is equivalent to
including the branch action in the information set, while making explicit
that the PBO must be recomputed when the candidate action profile changes.
-/
structure PositiveBranchPBO
    {Ω Info : Type*} [MeasurableSpace Ω] [MeasurableSpace Info]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (skill : Ω → ℝ) (branch : Set Ω) (observation : Ω → Info) where
  branch_measurable : MeasurableSet branch
  observation_measurable : Measurable observation
  estimate : Info → ℝ
  consistent_if_positive :
    0 < μ branch →
      Integrable skill (μ.restrict branch) ∧
        (fun ω => estimate (observation ω)) =ᵐ[μ.restrict branch]
          (μ.restrict branch)[skill |
            MeasurableSpace.comap observation inferInstance]

/--
A binary report/no-report candidate profile with branch-specific PBOs.

`reports` may represent the observed report action directly.  In a
report-required protocol it can also represent the pre-score take action;
the source-facing bridge is responsible for proving the timing/action
identification.  This carrier deliberately does not make either branch
positive by definition.
-/
structure PositiveMassPBOCandidateProfile
    {Ω : Type*} (ReportInfo NoReportInfo : Type*)
    [MeasurableSpace Ω] [MeasurableSpace ReportInfo]
    [MeasurableSpace NoReportInfo]
    (μ : Measure Ω) [IsFiniteMeasure μ] (skill : Ω → ℝ) where
  reports : Ω → Bool
  reports_measurable : Measurable reports
  reportObservation : Ω → ReportInfo
  noReportObservation : Ω → NoReportInfo
  reportPBO :
    PositiveBranchPBO μ skill {ω | reports ω = true} reportObservation
  noReportPBO :
    PositiveBranchPBO μ skill {ω | reports ω = false} noReportObservation

namespace PositiveMassPBOCandidateProfile

variable
    {Ω ReportInfo NoReportInfo : Type*}
    [MeasurableSpace Ω] [MeasurableSpace ReportInfo]
    [MeasurableSpace NoReportInfo]
    {μ : Measure Ω} [IsFiniteMeasure μ] {skill : Ω → ℝ}

abbrev Candidate : Type _ :=
  PositiveMassPBOCandidateProfile ReportInfo NoReportInfo μ skill

/-- The candidate's selected reporter population. -/
def reportBranch
    (P : Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (μ := μ) (skill := skill)) : Set Ω :=
  {ω | P.reports ω = true}

/-- The candidate's selected no-report population. -/
def noReportBranch
    (P : Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (μ := μ) (skill := skill)) : Set Ω :=
  {ω | P.reports ω = false}

/-- The actual candidate mass of the report branch. -/
def reportMass
    (P : Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (μ := μ) (skill := skill)) : ENNReal :=
  μ P.reportBranch

/-- The actual candidate mass of the no-report branch. -/
def noReportMass
    (P : Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (μ := μ) (skill := skill)) : ENNReal :=
  μ P.noReportBranch

theorem reportBranch_measurable
    (P : Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (μ := μ) (skill := skill)) :
    MeasurableSet P.reportBranch := by
  simpa [reportBranch] using P.reportPBO.branch_measurable

theorem noReportBranch_measurable
    (P : Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (μ := μ) (skill := skill)) :
    MeasurableSet P.noReportBranch := by
  simpa [noReportBranch] using P.noReportPBO.branch_measurable

/--
On a positive report branch, the profile's report estimate is the selected
conditional expectation.  No conclusion is exposed at report mass zero.
-/
theorem reportPBO_consistent_if_positive
    (P : Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (μ := μ) (skill := skill))
    (hpositive : 0 < P.reportMass) :
    Integrable skill (μ.restrict P.reportBranch) ∧
      (fun ω => P.reportPBO.estimate (P.reportObservation ω)) =ᵐ[
        μ.restrict P.reportBranch]
        (μ.restrict P.reportBranch)[skill |
          MeasurableSpace.comap P.reportObservation inferInstance] := by
  simpa [reportMass, reportBranch] using
    P.reportPBO.consistent_if_positive hpositive

/--
On a positive no-report branch, the profile's no-report estimate is the
selected conditional expectation.  No conclusion is exposed at no-report
mass zero.
-/
theorem noReportPBO_consistent_if_positive
    (P : Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (μ := μ) (skill := skill))
    (hpositive : 0 < P.noReportMass) :
    Integrable skill (μ.restrict P.noReportBranch) ∧
      (fun ω => P.noReportPBO.estimate (P.noReportObservation ω)) =ᵐ[
        μ.restrict P.noReportBranch]
        (μ.restrict P.noReportBranch)[skill |
          MeasurableSpace.comap P.noReportObservation inferInstance] := by
  simpa [noReportMass, noReportBranch] using
    P.noReportPBO.consistent_if_positive hpositive

/--
The source-faithful witness that a null report branch admits positive-mass
entry. `canEnter current candidate` keeps the population and feasible actions
fixed, recomputes the PBO from `candidate`, and then checks the supplied
Definition-1 individual best-response predicate on that candidate.  This
operationalizes the source's statement that the school knows the decision
functions and PBO follows them.  Because `candidate` contains its PBO fields,
this relation cannot reuse a PBO from `current` without proving the relevant
equality.  In particular, an entering individual's alternative is evaluated
against the candidate's recomputed PBO, not against the predecessor profile's
payoff.

Ordinary unilateral BR alone does not supply a numerical value at a null
branch. A later LG21 theorem proves this witness from a positive high-skill
seed and individual best responses, rather than assigning an off-path value.
-/
def NullReportBranchHasActiveEntry
    (current : Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (μ := μ) (skill := skill))
    (canEnter :
      Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
        (μ := μ) (skill := skill) →
      Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
        (μ := μ) (skill := skill) → Prop)
    (individualBestResponse :
      Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
        (μ := μ) (skill := skill) → Prop) : Prop :=
  current.reportMass = 0 →
    ∃ candidate,
      canEnter current candidate ∧
        0 < candidate.reportMass ∧
          individualBestResponse candidate

/--
A null report branch is stable against positive-mass entry exactly when no
candidate with recomputed positive-branch PBOs is a feasible individual-
best-response entry. This is kept separate from
`NullReportBranchHasActiveEntry`: the former is a stability predicate, while
the latter is its explicitly witnessed failure.
-/
def NullReportBranchStableAgainstActiveEntry
    (current : Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (μ := μ) (skill := skill))
    (canEnter :
      Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
        (μ := μ) (skill := skill) →
      Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
        (μ := μ) (skill := skill) → Prop)
    (individualBestResponse :
      Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
        (μ := μ) (skill := skill) → Prop) : Prop :=
  current.reportMass = 0 →
    ¬ ∃ candidate,
      canEnter current candidate ∧
        0 < candidate.reportMass ∧
          individualBestResponse candidate

/-- A concrete active-entry witness refutes stability at the null branch. -/
theorem nullReportBranch_not_stable_of_hasActiveEntry
    (current : Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
      (μ := μ) (skill := skill))
    (canEnter :
      Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
        (μ := μ) (skill := skill) →
      Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
        (μ := μ) (skill := skill) → Prop)
    (individualBestResponse :
      Candidate (ReportInfo := ReportInfo) (NoReportInfo := NoReportInfo)
        (μ := μ) (skill := skill) → Prop)
    (hnull : current.reportMass = 0)
    (hentry : NullReportBranchHasActiveEntry current canEnter
      individualBestResponse) :
    ¬ NullReportBranchStableAgainstActiveEntry current canEnter
      individualBestResponse := by
  intro hstable
  exact hstable hnull (hentry hnull)

end PositiveMassPBOCandidateProfile

/-!
## Strictly monotone binary best responses

The following lemmas are independent of LG21 terminology.  They make the
only order-theoretic inference needed by the report-required repair explicit:
when the payoff from the active action is strictly increasing in type and the
outside payoff is constant, every pointwise binary best response chooses an
upper set.  An a.e. source model still needs a separate null-tie or
representative-selection bridge before using this pointwise result.
-/

/-- A binary choice set is upper closed in the real type order. -/
def UpperClosedChoice (chooses : ℝ → Prop) : Prop :=
  ∀ ⦃low high : ℝ⦄, low ≤ high → chooses low → chooses high

/--
A pointwise binary best response to a strictly increasing active payoff and a
constant outside payoff chooses an upper-closed set of types.
-/
theorem upperClosedChoice_of_noProfitableBinaryChoiceDeviation_strictMono
    {chooses : ℝ → Prop} {choosePayoff : ℝ → ℝ} {outside : ℝ}
    (hbest :
      NoProfitableBinaryChoiceDeviation chooses choosePayoff
        (fun _ => outside))
    (hmono : StrictMono choosePayoff) :
    UpperClosedChoice chooses := by
  intro low high hle hlow
  by_contra hnotChoose
  have hne : low ≠ high := by
    intro hEq
    apply hnotChoose
    simpa [hEq] using hlow
  have hlt : low < high := lt_of_le_of_ne hle hne
  have hnotHigh : ¬ chooses high := hnotChoose
  have hlowPayoff : outside ≤ choosePayoff low := hbest.1 low hlow
  have hhighPayoff : choosePayoff high ≤ outside := hbest.2 high hnotHigh
  exact (not_le_of_gt (hmono hlt)) (hhighPayoff.trans hlowPayoff)

/--
Boolean form of the upper-set conclusion, convenient for source action
functions represented by `Bool`.
-/
theorem bool_choice_upperClosed_of_noProfitableBinaryChoiceDeviation_strictMono
    (chooses : ℝ → Bool) {choosePayoff : ℝ → ℝ} {outside : ℝ}
    (hbest :
      NoProfitableBinaryChoiceDeviation (fun q => chooses q = true)
        choosePayoff (fun _ => outside))
    (hmono : StrictMono choosePayoff) :
    ∀ ⦃low high : ℝ⦄,
      low ≤ high → chooses low = true → chooses high = true := by
  exact upperClosedChoice_of_noProfitableBinaryChoiceDeviation_strictMono
    hbest hmono

end

end LG21TestOptionalPolicies

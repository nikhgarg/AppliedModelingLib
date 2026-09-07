import LG21TestOptionalPolicies.ObservedAccessVoluntarySelfEnforcingCandidates

/-!
# Explicit active-branch selection for voluntary observed-access protocols

The paper's Section 4 prose uses an unraveling argument after the school has
learned the decision rule. A bare static RCD does not implement that
selection: it can leave a null action branch with an arbitrary value. The
definitions here make the needed convention visible.

On each measurable positive public-base region, the selected voluntary
profile is maximal almost everywhere under extension of its full source action
branch by source-timed, self-enforcing positive-branch candidates. The
candidate carries PBO and response evidence only on attained branches, plus
closure against profitable entry into any attained branch. This is an explicit
active-branch/unravelling selection, not an inference from a declaration name
or from an off-path numerical PBO. It is deliberately stated separately from
the literal conditional-mean obligations.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib MeasureTheory ProbabilityTheory Set
open AppliedModelingLib.Probability
open scoped ENNReal NNReal ProbabilityTheory

/-- The optional protocol's explicit source-level active-branch selection.
The selected profile is itself required to be represented by a source-timed
self-enforcing positive-mass candidate. On every positive measurable public
base region, its full action branch is maximal almost everywhere among such
candidates. -/
structure LG21OptionalFibrewiseActiveBranchSelection
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (selected : LG21ObservedAccessOptionalPositiveMassRefinedEquilibrium
      M haccess testFeature) : Prop where
  /-- The selected action/PBO record has the candidate-side response and
  closure obligations required by this voluntary refinement. -/
  selected_self_enforcing : ∃ candidate :
      LG21OptionalSourceTimedPositiveMassSelfEnforcingCandidate
        M haccess testFeature,
    candidate.source_timed = selected
  /-- No source-timed self-enforcing candidate can strictly extend the
  selected full action branch almost everywhere on a positive public-base
  region.  The two implications express maximality in the branch-extension
  order without referring to a particular outcome profile. -/
  maximal_active_branch_ae :
    let law := lg21ContinuousGaussianAccessPopulationLaw M
    let base := lg21ContinuousPopulationBase testFeature
    let score := lg21ContinuousPopulationFeature testFeature
    let skill := lg21ContinuousPopulationSkill (Feature := Feature)
    ∀ (candidate : LG21OptionalSourceTimedPositiveMassSelfEnforcingCandidate
        M haccess testFeature) (region : Set
          (LG21NonTestFeature Feature testFeature -> ℝ)),
    MeasurableSet region ->
    0 < law (base ⁻¹' region) ->
    (∀ᵐ student ∂law.restrict (base ⁻¹' region),
      selected.actions.takeDecision
          (skill student) (base student) = true ∧
        selected.actions.reportDecision
          (base student) (score student) = true ->
      candidate.source_timed.actions.takeDecision
          (skill student) (base student) = true ∧
        candidate.source_timed.actions.reportDecision
          (base student) (score student) = true) ->
    ∀ᵐ student ∂law.restrict (base ⁻¹' region),
      candidate.source_timed.actions.takeDecision
          (skill student) (base student) = true ∧
        candidate.source_timed.actions.reportDecision
          (base student) (score student) = true ->
      selected.actions.takeDecision (skill student) (base student) = true ∧
        selected.actions.reportDecision (base student) (score student) = true

/-- The report-required protocol's explicit source-level active-branch
selection. The selected profile and every candidate are paired with literal
positive-branch PBO, timing-specific response, and outsider-closure evidence;
on each positive public-base region the selected taking branch is maximal
almost everywhere in the same candidate order. -/
structure LG21ReportRequiredFibrewiseActiveBranchSelection
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (selected : LG21ReportRequiredSequentialEquilibriumData ℝ
      (LG21NonTestFeature Feature testFeature -> ℝ) ℝ)
    (selectedSource :
      letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
        lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
      LG21ReportRequiredPositiveMassRefinedSourceEquilibrium
        (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) selected
        (M.noiseVariance testFeature)) : Prop where
  /-- The selected action/PBO record is itself represented by a source-timed
  self-enforcing positive-mass candidate. -/
  selected_self_enforcing : ∃ candidate :
      LG21ReportRequiredSourceTimedPositiveMassSelfEnforcingCandidate
        M haccess testFeature,
    candidate.selected = selected
  /-- No source-timed self-enforcing candidate can strictly extend the
  selected taking branch almost everywhere on a positive public-base region.
  This is the report-required instance of the generic branch-extension order. -/
  maximal_active_branch_ae :
    let law := lg21ContinuousGaussianAccessPopulationLaw M
    let base := lg21ContinuousPopulationBase testFeature
    let skill := lg21ContinuousPopulationSkill (Feature := Feature)
    letI : IsProbabilityMeasure law :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
    ∀ (candidate : LG21ReportRequiredSourceTimedPositiveMassSelfEnforcingCandidate
        M haccess testFeature) (region : Set
          (LG21NonTestFeature Feature testFeature -> ℝ)),
      MeasurableSet region ->
      0 < law (base ⁻¹' region) ->
      (∀ᵐ student ∂law.restrict (base ⁻¹' region),
        selected.takeDecision (skill student) (base student) = true ->
        candidate.selected.takeDecision (skill student) (base student) = true) ->
      ∀ᵐ student ∂law.restrict (base ⁻¹' region),
        candidate.selected.takeDecision (skill student) (base student) = true ->
        selected.takeDecision (skill student) (base student) = true

/-- Under the explicit optional active-branch selection, the source-derived
all-take/all-report candidate forces the selected profile to take and report
almost everywhere. The proof supplies neither a cutoff nor a value on a null
no-report branch. -/
theorem lg21ContinuousGaussianAccessPopulation_optional_allTakeAllReport_of_fibrewiseActiveBranchSelection
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (selected : LG21ObservedAccessOptionalPositiveMassRefinedEquilibrium
      M haccess testFeature)
    (hselection : LG21OptionalFibrewiseActiveBranchSelection
      M haccess testFeature selected) :
    ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw M,
      selected.actions.takeDecision
        (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student) = true ∧
      selected.actions.reportDecision
        (lg21ContinuousPopulationBase testFeature student)
        (lg21ContinuousPopulationFeature testFeature student) = true := by
  let law := lg21ContinuousGaussianAccessPopulationLaw M
  let base := lg21ContinuousPopulationBase testFeature
  let score := lg21ContinuousPopulationFeature testFeature
  let skill := lg21ContinuousPopulationSkill (Feature := Feature)
  let fullBase : Set (LG21NonTestFeature Feature testFeature -> ℝ) := Set.univ
  letI : IsProbabilityMeasure law :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  rcases
      lg21ContinuousGaussianAccessPopulation_exists_optionalSelfEnforcing_allTakeAllReport
        M haccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance with
    ⟨candidate, hcandidateTake, hcandidateReport⟩
  have hpositive : 0 < law (base ⁻¹' fullBase) := by
    simp [law, fullBase]
  have hselectedContainsCandidate := hselection.maximal_active_branch_ae
    candidate fullBase (by simp [fullBase]) hpositive
    (Filter.Eventually.of_forall fun student _ =>
      ⟨hcandidateTake (skill student) (base student),
        hcandidateReport (base student) (score student)⟩)
  have hselectedActive : ∀ᵐ student ∂(law.restrict (base ⁻¹' fullBase)),
      selected.actions.takeDecision (skill student) (base student) = true ∧
        selected.actions.reportDecision (base student) (score student) = true := by
    filter_upwards [hselectedContainsCandidate] with student hcontains
    exact hcontains
      ⟨hcandidateTake (skill student) (base student),
        hcandidateReport (base student) (score student)⟩
  simpa [law, base, score, skill, fullBase] using hselectedActive

/-- Under the explicit report-required active-branch selection, the
source-derived all-take candidate forces the selected profile to take almost
everywhere. The candidate's report PBO is derived on its actual full branch;
the proof never evaluates its empty no-take branch. -/
theorem lg21ContinuousGaussianAccessPopulation_reportRequired_allTake_of_fibrewiseActiveBranchSelection
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (selected : LG21ReportRequiredSequentialEquilibriumData ℝ
      (LG21NonTestFeature Feature testFeature -> ℝ) ℝ)
    (hselectedSource :
      letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
        lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
      LG21ReportRequiredPositiveMassRefinedSourceEquilibrium
        (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) selected
        (M.noiseVariance testFeature))
    (hselection : LG21ReportRequiredFibrewiseActiveBranchSelection
      M haccess testFeature selected hselectedSource) :
    ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw M,
      selected.takeDecision (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student) = true := by
  let law := lg21ContinuousGaussianAccessPopulationLaw M
  let base := lg21ContinuousPopulationBase testFeature
  let score := lg21ContinuousPopulationFeature testFeature
  let skill := lg21ContinuousPopulationSkill (Feature := Feature)
  let fullBase : Set (LG21NonTestFeature Feature testFeature -> ℝ) := Set.univ
  letI : IsProbabilityMeasure law :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  rcases
      lg21ContinuousGaussianAccessPopulation_exists_reportRequiredSelfEnforcing_allTake
        M haccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance with
    ⟨candidate, hcandidateTake⟩
  have hpositive : 0 < law (base ⁻¹' fullBase) := by
    simp [law, fullBase]
  have hselectedContainsCandidate := hselection.maximal_active_branch_ae
    candidate fullBase (by simp [fullBase]) hpositive
    (Filter.Eventually.of_forall fun student _ =>
      hcandidateTake (skill student) (base student))
  have hselectedActive : ∀ᵐ student ∂(law.restrict (base ⁻¹' fullBase)),
      selected.takeDecision (skill student) (base student) = true := by
    filter_upwards [hselectedContainsCandidate] with student hcontains
    exact hcontains (hcandidateTake (skill student) (base student))
  simpa [law, base, score, skill, fullBase] using hselectedActive

end

end LG21TestOptionalPolicies

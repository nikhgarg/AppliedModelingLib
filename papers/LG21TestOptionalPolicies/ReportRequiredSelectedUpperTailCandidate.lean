import LG21TestOptionalPolicies.RecalibratedCandidateBranchClosure
import LG21TestOptionalPolicies.SelectedGaussianCutoffBoundary

/-!
# Report-required selected-upper-tail candidates

This module packages the payoff side of the hidden-access report-required
candidate.  The candidate reports exactly after taking, and its reported value
is the literal posterior mean conditional on the candidate's selected upper
tail.  The no-report value is an explicit parameter: a source bridge must
identify it with the conditional mean on the raw `X = 0` population, which
contains the no-access component.

The resulting closure theorem is stated in payoff space.  It therefore rules
out an isolated high-band action without relying on a strategy-function name.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory
open AppliedModelingLib Probability

/--
The report-required candidate with an upper-tail latent taking rule.  Its
reported payoff is the actual selected Gaussian posterior formula; its
no-report value is deliberately supplied separately so that it can later be
proved equal to the literal raw hidden-access `X = 0` conditional mean.
-/
noncomputable def lg21ReportRequiredSelectedUpperTailCandidate
    {Base : Type*}
    (baseMean cutoff noReportValue : Base -> ℝ)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance) :
    LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ where
  testLaw := fun latentSkill _publicBase =>
    gaussianReal latentSkill noiseVariance.toNNReal
  testLaw_isProbability := by
    intro latentSkill publicBase
    infer_instance
  takeDecision := fun latentSkill publicBase =>
    decide (cutoff publicBase <= latentSkill)
  reportedPayoff := fun publicBase observedScore =>
    lg21SelectedGaussianUpperTailReporterPBO
      (baseMean publicBase) priorVariance noiseVariance
      (cutoff publicBase) observedScore
  noReportPayoff := noReportValue
  reportedPayoff_integrable := by
    intro latentSkill publicBase
    exact lg21SelectedGaussianUpperTailReporterPBO_integrable
      (baseMean publicBase) priorVariance noiseVariance
      (cutoff publicBase) latentSkill hpriorVariance hnoiseVariance
  estimationConsistent := True

/-- The candidate takes precisely on its declared latent upper tail. -/
theorem lg21ReportRequiredSelectedUpperTailCandidate_takeDecision_eq_true_iff
    {Base : Type*}
    (baseMean cutoff noReportValue : Base -> ℝ)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (latentSkill : ℝ) (publicBase : Base) :
    (lg21ReportRequiredSelectedUpperTailCandidate
      baseMean cutoff noReportValue priorVariance noiseVariance
      hpriorVariance hnoiseVariance).takeDecision latentSkill publicBase = true ↔
      cutoff publicBase ≤ latentSkill := by
  simp [lg21ReportRequiredSelectedUpperTailCandidate]

/-- The candidate's reported payoff is the literal normalized selected posterior mean. -/
theorem lg21ReportRequiredSelectedUpperTailCandidate_reportedPayoff_eq_selectedMean
    {Base : Type*}
    (baseMean cutoff noReportValue : Base -> ℝ)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (publicBase : Base) (observedScore : ℝ) :
    (lg21ReportRequiredSelectedUpperTailCandidate
      baseMean cutoff noReportValue priorVariance noiseVariance
      hpriorVariance hnoiseVariance).reportedPayoff publicBase observedScore =
      ∫ latentSkill, latentSkill ∂
        lg21NormalizedRestriction
          (gaussianSignalPosteriorKernel
            (baseMean publicBase) priorVariance noiseVariance observedScore)
          (Set.Ici (cutoff publicBase)) := by
  simpa [lg21ReportRequiredSelectedUpperTailCandidate] using
    (lg21_gaussianSignalPosterior_selectedUpperTailMean_eq_explicit
      (baseMean publicBase) priorVariance noiseVariance observedScore
      (cutoff publicBase) hpriorVariance hnoiseVariance).symm

/-- The candidate's pre-score taking payoff is strictly increasing in skill. -/
theorem lg21ReportRequiredSelectedUpperTailCandidate_takeExpectedPayoff_strictMono
    {Base : Type*}
    (baseMean cutoff noReportValue : Base -> ℝ)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (publicBase : Base) :
    StrictMono (fun latentSkill =>
      lg21ReportRequiredSequentialTakeExpectedPayoff
        (lg21ReportRequiredSelectedUpperTailCandidate
          baseMean cutoff noReportValue priorVariance noiseVariance
          hpriorVariance hnoiseVariance)
        latentSkill publicBase) := by
  apply lg21_reportRequired_takeExpectedPayoff_strictMono_of_literalSelectedUpperTailPBO
    (lg21ReportRequiredSelectedUpperTailCandidate
      baseMean cutoff noReportValue priorVariance noiseVariance
      hpriorVariance hnoiseVariance)
    publicBase (baseMean publicBase) priorVariance noiseVariance
    (cutoff publicBase) hpriorVariance hnoiseVariance
  · intro latentSkill
    rfl
  · intro observedScore
    rfl

/--
At its cutoff, the candidate's literal expected report payoff is the selected
Gaussian boundary payoff.
-/
theorem lg21ReportRequiredSelectedUpperTailCandidate_takeExpectedPayoff_at_cutoff_eq_boundary
    {Base : Type*}
    (baseMean cutoff noReportValue : Base -> ℝ)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (publicBase : Base) :
    lg21ReportRequiredSequentialTakeExpectedPayoff
      (lg21ReportRequiredSelectedUpperTailCandidate
        baseMean cutoff noReportValue priorVariance noiseVariance
        hpriorVariance hnoiseVariance)
      (cutoff publicBase) publicBase =
      lg21SelectedGaussianCutoffBoundaryPayoff
        (baseMean publicBase) priorVariance noiseVariance
        (cutoff publicBase) := by
  change (∫ observedScore,
      lg21SelectedGaussianUpperTailReporterPBO
        (baseMean publicBase) priorVariance noiseVariance
        (cutoff publicBase) observedScore
      ∂gaussianReal (cutoff publicBase) noiseVariance.toNNReal) = _
  calc
    (∫ observedScore,
      lg21SelectedGaussianUpperTailReporterPBO
        (baseMean publicBase) priorVariance noiseVariance
        (cutoff publicBase) observedScore
      ∂gaussianReal (cutoff publicBase) noiseVariance.toNNReal) =
        ∫ observedScore,
          ∫ latentSkill, latentSkill ∂
            lg21NormalizedRestriction
              (gaussianSignalPosteriorKernel
                (baseMean publicBase) priorVariance noiseVariance observedScore)
              (Set.Ici (cutoff publicBase))
          ∂gaussianReal (cutoff publicBase) noiseVariance.toNNReal := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun observedScore =>
              (lg21_gaussianSignalPosterior_selectedUpperTailMean_eq_explicit
                (baseMean publicBase) priorVariance noiseVariance observedScore
                (cutoff publicBase) hpriorVariance hnoiseVariance).symm
    _ = lg21SelectedGaussianCutoffBoundaryPayoff
          (baseMean publicBase) priorVariance noiseVariance
          (cutoff publicBase) :=
      lg21SelectedGaussianCutoffBoundaryPayoff_eq_actual
        (baseMean publicBase) priorVariance noiseVariance
        (cutoff publicBase) hpriorVariance hnoiseVariance

/--
The raw hidden-access source bridge must prove this equality from the actual
candidate `X = 0` law.  Given that literal root, the candidate's full upper
tail is closed under its own recalibrated strict-gain comparison.
-/
theorem lg21ReportRequiredSelectedUpperTailCandidate_upperTailClosedUnderGain_of_root
    {Base : Type*}
    (baseMean cutoff noReportValue : Base -> ℝ)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hroot : ∀ publicBase,
      lg21SelectedGaussianCutoffBoundaryPayoff
        (baseMean publicBase) priorVariance noiseVariance
        (cutoff publicBase) = noReportValue publicBase)
    (publicBase : Base) :
    ScalarUpperTailClosedUnderGain
      (fun latentSkill =>
        lg21ReportRequiredSequentialTakeExpectedPayoff
          (lg21ReportRequiredSelectedUpperTailCandidate
            baseMean cutoff noReportValue priorVariance noiseVariance
            hpriorVariance hnoiseVariance)
          latentSkill publicBase - noReportValue publicBase)
      (cutoff publicBase) := by
  have hstrict :=
    lg21ReportRequiredSelectedUpperTailCandidate_takeExpectedPayoff_strictMono
      baseMean cutoff noReportValue priorVariance noiseVariance
      hpriorVariance hnoiseVariance publicBase
  have hgainStrict : StrictMono (fun latentSkill =>
      lg21ReportRequiredSequentialTakeExpectedPayoff
        (lg21ReportRequiredSelectedUpperTailCandidate
          baseMean cutoff noReportValue priorVariance noiseVariance
          hpriorVariance hnoiseVariance)
        latentSkill publicBase - noReportValue publicBase) := by
    intro lowSkill highSkill hlowHigh
    exact sub_lt_sub_right (hstrict hlowHigh) _
  have hgainRoot :
      lg21ReportRequiredSequentialTakeExpectedPayoff
        (lg21ReportRequiredSelectedUpperTailCandidate
          baseMean cutoff noReportValue priorVariance noiseVariance
          hpriorVariance hnoiseVariance)
        (cutoff publicBase) publicBase - noReportValue publicBase = 0 := by
    rw [lg21ReportRequiredSelectedUpperTailCandidate_takeExpectedPayoff_at_cutoff_eq_boundary
      baseMean cutoff noReportValue priorVariance noiseVariance
      hpriorVariance hnoiseVariance publicBase,
      hroot publicBase]
    ring
  exact scalarUpperTailClosedUnderGain_of_strictMono_root _ _ hgainStrict hgainRoot

/--
At a literal raw-mixture root, the candidate's declared taking rule is exactly
the Definition-1 weak best response.  The proof uses the selected-posterior
payoff, so it does not replace the reporter PBO by an unselected affine law.
-/
theorem lg21ReportRequiredSelectedUpperTailCandidate_takeDecision_iff_bestResponse_of_root
    {Base : Type*}
    (baseMean cutoff noReportValue : Base -> ℝ)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hroot : ∀ publicBase,
      lg21SelectedGaussianCutoffBoundaryPayoff
        (baseMean publicBase) priorVariance noiseVariance
        (cutoff publicBase) = noReportValue publicBase)
    (latentSkill : ℝ) (publicBase : Base) :
    (lg21ReportRequiredSelectedUpperTailCandidate
      baseMean cutoff noReportValue priorVariance noiseVariance
      hpriorVariance hnoiseVariance).takeDecision latentSkill publicBase = true ↔
      noReportValue publicBase ≤
        lg21ReportRequiredSequentialTakeExpectedPayoff
          (lg21ReportRequiredSelectedUpperTailCandidate
            baseMean cutoff noReportValue priorVariance noiseVariance
            hpriorVariance hnoiseVariance)
          latentSkill publicBase := by
  let candidate := lg21ReportRequiredSelectedUpperTailCandidate
    baseMean cutoff noReportValue priorVariance noiseVariance
    hpriorVariance hnoiseVariance
  have hstrict :=
    lg21ReportRequiredSelectedUpperTailCandidate_takeExpectedPayoff_strictMono
      baseMean cutoff noReportValue priorVariance noiseVariance
      hpriorVariance hnoiseVariance publicBase
  have hcutoffValue :
      lg21ReportRequiredSequentialTakeExpectedPayoff candidate
        (cutoff publicBase) publicBase = noReportValue publicBase := by
    rw [lg21ReportRequiredSelectedUpperTailCandidate_takeExpectedPayoff_at_cutoff_eq_boundary
      baseMean cutoff noReportValue priorVariance noiseVariance
      hpriorVariance hnoiseVariance publicBase,
      hroot publicBase]
  constructor
  · intro htake
    have hcutoff : cutoff publicBase ≤ latentSkill := by
      simpa [candidate] using
        (lg21ReportRequiredSelectedUpperTailCandidate_takeDecision_eq_true_iff
          baseMean cutoff noReportValue priorVariance noiseVariance
          hpriorVariance hnoiseVariance latentSkill publicBase).1 htake
    have hmono := hstrict.monotone hcutoff
    rw [hcutoffValue] at hmono
    exact hmono
  · intro hbest
    apply
      (lg21ReportRequiredSelectedUpperTailCandidate_takeDecision_eq_true_iff
        baseMean cutoff noReportValue priorVariance noiseVariance
        hpriorVariance hnoiseVariance latentSkill publicBase).2
    by_contra hnotCutoff
    have hbelow : latentSkill < cutoff publicBase := lt_of_not_ge hnotCutoff
    have hless := hstrict hbelow
    change lg21ReportRequiredSequentialTakeExpectedPayoff candidate
        latentSkill publicBase <
      lg21ReportRequiredSequentialTakeExpectedPayoff candidate
        (cutoff publicBase) publicBase at hless
    rw [hcutoffValue] at hless
    exact (not_lt_of_ge hbest) hless

/--
The selected-upper-tail candidate is a report-required sequential equilibrium
once the raw hidden-access no-report conditional mean supplies the displayed
root at every public base.
-/
theorem lg21ReportRequiredSelectedUpperTailCandidate_sequentialEquilibrium_of_roots
    {Base : Type*}
    (baseMean cutoff noReportValue : Base -> ℝ)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hroot : ∀ publicBase,
      lg21SelectedGaussianCutoffBoundaryPayoff
        (baseMean publicBase) priorVariance noiseVariance
        (cutoff publicBase) = noReportValue publicBase) :
    lg21ReportRequiredSequentialEquilibrium
      (lg21ReportRequiredSelectedUpperTailCandidate
        baseMean cutoff noReportValue priorVariance noiseVariance
        hpriorVariance hnoiseVariance) := by
  constructor
  · intro publicBase
    exact AppliedModelingLib.noProfitableBinaryChoiceDeviation_of_choice_iff_payoff_le
      (fun latentSkill =>
        lg21ReportRequiredSelectedUpperTailCandidate_takeDecision_iff_bestResponse_of_root
          baseMean cutoff noReportValue priorVariance noiseVariance
          hpriorVariance hnoiseVariance hroot latentSkill publicBase)
  · trivial

end

end LG21TestOptionalPolicies

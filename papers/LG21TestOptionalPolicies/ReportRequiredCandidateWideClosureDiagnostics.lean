import LG21TestOptionalPolicies.ReportRequiredLocalGaussianCandidate

/-!
# Candidate no-take branch-response diagnostic for report-required LG21 testing

The former zero-taker entry route checked only whether members selected into a
candidate taking branch weakly preferred taking. This file records the
separate response condition for members of a candidate's positive no-take
branch.

This file states that requirement directly in payoff space and proves that the
existing Gaussian upper-tail entry candidate fails it. The result is a
diagnostic, not a replacement equilibrium theorem.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib Probability MeasureTheory ProbabilityTheory Set

/-- A report-required candidate's no-take branch satisfies the literal
best-response condition only when almost every member of that positive branch
does not strictly gain from switching to the candidate's own expected taking
payoff. -/
def LG21ReportRequiredCandidateNoTakeMembersBestRespond
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) (base : Omega -> Base) (skill : Omega -> ℝ)
    (candidate : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ) : Prop :=
  ∀ᵐ omega ∂sourceLaw.restrict
      (lg21ReportRequiredCandidateSourceNoTakeEvent base skill candidate),
    lg21ReportRequiredSequentialTakeExpectedPayoff candidate
      (skill omega) (base omega) ≤ candidate.noReportPayoff (base omega)

/-- A positive no-take branch with strict candidate-side taking gain everywhere
cannot satisfy no-take branch response. This is independent of how the
candidate action function happens to be implemented. -/
theorem not_lg21ReportRequiredCandidateNoTakeMembersBestRespond_of_positive_strict_gain
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) (base : Omega -> Base) (skill : Omega -> ℝ)
    (candidate : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ)
    (hpositive : 0 < sourceLaw
      (lg21ReportRequiredCandidateSourceNoTakeEvent base skill candidate))
    (hgain : ∀ omega,
      candidate.noReportPayoff (base omega) <
        lg21ReportRequiredSequentialTakeExpectedPayoff candidate
          (skill omega) (base omega)) :
    ¬ LG21ReportRequiredCandidateNoTakeMembersBestRespond
      sourceLaw base skill candidate := by
  intro hclosed
  have hfalse : ∀ᵐ omega ∂sourceLaw.restrict
      (lg21ReportRequiredCandidateSourceNoTakeEvent base skill candidate), False := by
    filter_upwards [hclosed] with omega hclosed
    exact (not_le_of_gt (hgain omega)) hclosed
  have hzeroRestrict : sourceLaw.restrict
      (lg21ReportRequiredCandidateSourceNoTakeEvent base skill candidate) Set.univ = 0 := by
    rw [ae_iff] at hfalse
    simpa using hfalse
  have hzero : sourceLaw
      (lg21ReportRequiredCandidateSourceNoTakeEvent base skill candidate) = 0 := by
    simpa using hzeroRestrict
  exact (ne_of_gt hpositive) hzero

/-- The Gaussian upper-tail candidate gives every source type a strict gain
from its own expected taking payoff. Thus its no-take members do not satisfy
the required response condition, despite the old report-branch certificate. -/
theorem lg21_reportRequiredGaussianUpperTailCandidate_allTypes_strict_take_gain
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (base : Omega -> Base) (skill : Omega -> ℝ)
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance) :
    ∀ omega,
      (lg21ReportRequiredGaussianUpperTailCandidate
        baseMean hbaseMean priorVariance noiseVariance
        hpriorVariance hnoiseVariance).noReportPayoff (base omega) <
        lg21ReportRequiredSequentialTakeExpectedPayoff
          (lg21ReportRequiredGaussianUpperTailCandidate
            baseMean hbaseMean priorVariance noiseVariance
            hpriorVariance hnoiseVariance)
          (skill omega) (base omega) := by
  intro omega
  let candidate := lg21ReportRequiredGaussianUpperTailCandidate
    baseMean hbaseMean priorVariance noiseVariance hpriorVariance hnoiseVariance
  letI : IsProbabilityMeasure (candidate.testLaw (skill omega) (base omega)) :=
    candidate.testLaw_isProbability (skill omega) (base omega)
  have hpoint : ∀ observedScore,
      candidate.noReportPayoff (base omega) <
        candidate.reportedPayoff (base omega) observedScore := by
    intro observedScore
    exact lg21_reportRequiredGaussianUpperTailCandidate_noReportPayoff_lt_reportedPayoff
      baseMean hbaseMean priorVariance noiseVariance
      hpriorVariance hnoiseVariance (base omega) observedScore
  have hintegral := lg21_integral_lt_integral_of_ae_lt_probability
    (candidate.testLaw (skill omega) (base omega))
    (integrable_const (candidate.noReportPayoff (base omega)))
    (candidate.reportedPayoff_integrable (skill omega) (base omega))
    (Filter.Eventually.of_forall hpoint)
  change candidate.noReportPayoff (base omega) <
    ∫ observedScore, candidate.reportedPayoff (base omega) observedScore ∂
      candidate.testLaw (skill omega) (base omega)
  simpa [lg21ReportRequiredSequentialTakeExpectedPayoff] using hintegral

/-- Under the literal Gaussian source factorization, the existing upper-tail
candidate has a positive no-take branch and therefore fails the no-take
branch-response condition. -/
theorem not_lg21ReportRequiredGaussianUpperTailCandidate_noTakeMembersBestRespond_of_factorization
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega)
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (hbase : Measurable base) (hscore : Measurable score) (hskill : Measurable skill)
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hsourceFactor :
      sourceLaw.map (fun omega => (base omega, (score omega, skill omega))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean priorVariance noiseVariance) :
    ¬ LG21ReportRequiredCandidateNoTakeMembersBestRespond sourceLaw base skill
      (lg21ReportRequiredGaussianUpperTailCandidate
        baseMean hbaseMean priorVariance noiseVariance
        hpriorVariance hnoiseVariance) := by
  apply not_lg21ReportRequiredCandidateNoTakeMembersBestRespond_of_positive_strict_gain
  · exact lg21_reportRequiredGaussianUpperTailCandidate_sourceNoTake_positive_of_factorization
      sourceLaw base score skill hbase hscore hskill baseLaw
      baseMean hbaseMean priorVariance noiseVariance
      hpriorVariance hnoiseVariance hsourceFactor
  · exact lg21_reportRequiredGaussianUpperTailCandidate_allTypes_strict_take_gain
      base skill baseMean hbaseMean priorVariance noiseVariance
      hpriorVariance hnoiseVariance

end

end LG21TestOptionalPolicies

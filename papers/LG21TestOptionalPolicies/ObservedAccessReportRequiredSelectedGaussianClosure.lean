import LG21TestOptionalPolicies.ReportRequiredPositiveMassUnraveling
import LG21TestOptionalPolicies.SelectedGaussianSignalPosteriorBridge

/-!
# On-path Gaussian closure for observed-access report-required testing

This is the fixed-public-base source-facing endpoint.  Its PBO premise is an
almost-everywhere identity under the literal attained reporter score law; the
Gaussian absolute-continuity bridge transports that identity to each
student's pre-test score law.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open AppliedModelingLib Probability

/-- At one observed public base, a positive literal Gaussian reporter branch
rules out a positive literal Gaussian no-take branch.  The displayed PBO
identity is exactly the conditional mean on the attained reporter score law,
so no cutoff representation, off-path value, or function-name convention is
used. -/
theorem lg21_observedAccess_reportRequired_selectedGaussianPBO_ae_no_positiveMass_noTake
    {Base : Type*}
    {E : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ}
    (base : Base)
    (hbest : NoProfitableBinaryChoiceDeviation
      (fun skill ↦ E.takeDecision skill base = true)
      (fun skill ↦ lg21ReportRequiredSequentialTakeExpectedPayoff E skill base)
      (fun _skill ↦ E.noReportPayoff base))
    (priorMean priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (htakeMeasurable : Measurable (E.takeDecision · base))
    (hreporterPositive : 0 < gaussianReal priorMean priorVariance.toNNReal
      {skill | E.takeDecision skill base = true})
    (hnoTakePBO : ∀ hpositive : 0 < gaussianReal priorMean priorVariance.toNNReal
      {skill | E.takeDecision skill base = false},
      E.noReportPayoff base = ∫ skill, skill ∂lg21NormalizedRestriction
        (gaussianReal priorMean priorVariance.toNNReal)
        {skill | E.takeDecision skill base = false})
    (hreportedPBO : E.reportedPayoff base =ᵐ[
      normalizedSelectedBase
        (gaussianReal priorMean (priorVariance + noiseVariance).toNNReal)
        (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)
        (Set.univ ×ˢ {skill | E.takeDecision skill base = true})]
      fun score => ∫ latentSkill, latentSkill ∂lg21NormalizedRestriction
        (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance score)
        {skill | E.takeDecision skill base = true})
    (htestLaw : ∀ skill,
      E.testLaw skill base = gaussianReal skill noiseVariance.toNNReal) :
    ¬ 0 < gaussianReal priorMean priorVariance.toNNReal
      {skill | E.takeDecision skill base = false} := by
  intro hnoTakePositive
  let priorLaw : Measure ℝ := gaussianReal priorMean priorVariance.toNNReal
  let takeSet : Set ℝ := {skill | E.takeDecision skill base = true}
  let noTakeSet : Set ℝ := {skill | E.takeDecision skill base = false}
  have hpriorIntegrable : Integrable (fun skill : ℝ => skill) priorLaw := by
    dsimp [priorLaw]
    exact (memLp_id_gaussianReal' (p := 1) (by norm_num)).integrable le_rfl
  have htakeMeasurableSet : MeasurableSet takeSet := by
    change MeasurableSet ((E.takeDecision · base) ⁻¹' ({true} : Set Bool))
    exact (measurableSet_singleton true).preimage htakeMeasurable
  have hnoTakeMeasurableSet : MeasurableSet noTakeSet := by
    change MeasurableSet ((E.takeDecision · base) ⁻¹' ({false} : Set Bool))
    exact (measurableSet_singleton false).preimage htakeMeasurable
  have hreporterPositive' : 0 < priorLaw takeSet := by
    simpa [priorLaw, takeSet] using hreporterPositive
  have hnoTakePositive' : 0 < priorLaw noTakeSet := by
    simpa [priorLaw, noTakeSet] using hnoTakePositive
  have hnoTakeIntegrable : Integrable (fun skill : ℝ => skill)
      (lg21NormalizedRestriction priorLaw noTakeSet) := by
    unfold lg21NormalizedRestriction
    exact hpriorIntegrable.restrict.smul_measure
      (ENNReal.inv_ne_top.mpr (ne_of_gt hnoTakePositive'))
  have hreportedIntegrable : ∀ skill,
      Integrable (E.reportedPayoff base)
        (gaussianReal skill noiseVariance.toNNReal) := by
    intro skill
    rw [← htestLaw skill]
    exact E.reportedPayoff_integrable skill base
  have hstrictGaussian : StrictMono (fun skill =>
      ∫ score, E.reportedPayoff base score ∂
        gaussianReal skill noiseVariance.toNNReal) := by
    apply lg21_selectedGaussianSignal_expectedPBO_strictMono_of_ae
      priorMean priorVariance noiseVariance takeSet hpriorVariance hnoiseVariance
      htakeMeasurableSet hreporterPositive'
    · simpa [takeSet] using hreportedPBO
    · exact hreportedIntegrable
  have hstrictExpected : StrictMono
      (fun skill => lg21ReportRequiredSequentialTakeExpectedPayoff E skill base) := by
    intro lowSkill highSkill hlowHigh
    change (∫ score, E.reportedPayoff base score ∂E.testLaw lowSkill base) <
      ∫ score, E.reportedPayoff base score ∂E.testLaw highSkill base
    rw [htestLaw lowSkill, htestLaw highSkill]
    exact hstrictGaussian hlowHigh
  have horder : ∀ noTake take,
      noTake ∈ noTakeSet -> take ∈ takeSet -> noTake < take := by
    intro noTake take hnoTake htake
    exact lg21_reportRequired_noTake_lt_take_of_strictExpectedPayoff_of_bestResponse
      base hbest hstrictExpected hnoTake htake
  have hnoTakeMean_lt_take : ∀ take, take ∈ takeSet ->
      E.noReportPayoff base < take := by
    intro take htake
    rw [hnoTakePBO hnoTakePositive]
    exact lg21NormalizedRestriction_mean_lt_upper
      priorLaw noTakeSet (fun skill : ℝ => skill) take
      hnoTakeMeasurableSet hnoTakePositive' hnoTakeIntegrable
      (fun noTake hnoTake => horder noTake take hnoTake htake)
  let canonicalPBO : ℝ → ℝ := fun score =>
    ∫ latentSkill, latentSkill ∂lg21NormalizedRestriction
      (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance score)
      takeSet
  have hcanonicalAbove : ∀ score,
      E.noReportPayoff base < canonicalPBO score := by
    intro score
    have hselectedPosteriorPositive : 0 <
        gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance score
          takeSet := by
      simpa [takeSet] using
        (lg21_gaussianSignalPosterior_selected_pos
          priorMean priorVariance noiseVariance
          {skill | E.takeDecision skill base = true}
          hpriorVariance hnoiseVariance hreporterPositive score)
    letI : IsFiniteMeasure
        (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance score) := by
      rw [gaussianSignalPosteriorKernel_apply]
      infer_instance
    apply lg21NormalizedRestriction_mean_gt_lower
      (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance score)
      takeSet (fun skill : ℝ => skill) (E.noReportPayoff base)
      htakeMeasurableSet
    · exact hselectedPosteriorPositive
    · rw [gaussianSignalPosteriorKernel_apply]
      have hposteriorIntegrable : Integrable (fun skill : ℝ => skill)
          (gaussianReal
            (gaussianSignalWeight priorVariance noiseVariance * score +
              gaussianSignalPriorWeight priorVariance noiseVariance * priorMean)
            (gaussianSignalPosteriorVariance priorVariance noiseVariance)) := by
        exact (memLp_id_gaussianReal' (p := 1) (by norm_num)).integrable le_rfl
      exact hposteriorIntegrable.restrict.smul_measure
        (ENNReal.inv_ne_top.mpr (ne_of_gt (by
          simpa [gaussianSignalPosteriorKernel_apply] using
            hselectedPosteriorPositive)))
    · intro skill htake
      exact hnoTakeMean_lt_take skill htake
  have hreportedTransport : ∀ skill,
      E.reportedPayoff base =ᵐ[gaussianReal skill noiseVariance.toNNReal]
        canonicalPBO := by
    intro skill
    exact
      (lg21_gaussianTestLaw_absolutelyContinuous_selectedScoreLaw
        priorMean priorVariance noiseVariance takeSet hpriorVariance hnoiseVariance
        htakeMeasurableSet hreporterPositive' skill).ae_eq (by
          simpa [takeSet, canonicalPBO] using hreportedPBO)
  have htakeAboveNoTake : ∀ skill,
      E.noReportPayoff base <
        lg21ReportRequiredSequentialTakeExpectedPayoff E skill base := by
    intro skill
    letI : IsProbabilityMeasure (E.testLaw skill base) :=
      E.testLaw_isProbability skill base
    have hpoint : ∀ᵐ score ∂E.testLaw skill base,
        E.noReportPayoff base < E.reportedPayoff base score := by
      rw [htestLaw skill]
      filter_upwards [hreportedTransport skill] with score hPBO
      rw [hPBO]
      exact hcanonicalAbove score
    have hstrict := lg21_integral_lt_integral_of_ae_lt_probability
      (E.testLaw skill base)
      (integrable_const (E.noReportPayoff base))
      (E.reportedPayoff_integrable skill base) hpoint
    simpa [lg21ReportRequiredSequentialTakeExpectedPayoff] using hstrict
  have hnoTakeNonempty : noTakeSet.Nonempty := by
    by_contra hempty
    have hempty' : noTakeSet = ∅ := not_nonempty_iff_eq_empty.mp hempty
    have hzero : priorLaw noTakeSet = 0 := by simp [hempty']
    exact (ne_of_gt hnoTakePositive') hzero
  rcases hnoTakeNonempty with ⟨skill, hnoTake⟩
  have hnoTakeBR := hbest.2 skill (by simpa [noTakeSet] using hnoTake)
  exact (not_le_of_gt (htakeAboveNoTake skill)) hnoTakeBR

end

end LG21TestOptionalPolicies

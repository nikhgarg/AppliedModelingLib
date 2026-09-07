import LG21TestOptionalPolicies.SelectedGaussianSignalPosteriorBridge

/-!
# Positive reporter branches yield strict test gains

This is the narrow Section 3 semantic step used after a literal reporter
branch has been reached.  It does not calibrate the hidden-access no-report
branch, whose public law also contains students without access.  Instead it
shows that an attained reporter branch with a strictly ordered conditional
mean contains positive mass of scores at which reporting is strictly better
than the literal no-report payoff.  Absolute-continuity transport then makes
that set reachable by a specified Gaussian test law.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open AppliedModelingLib Probability

/--
An attained reporter law whose PBO is a strictly increasing conditional
mean has positive mass of strict report gains.  The conclusion is transported
only along explicit measure domination arrows; it does not evaluate the PBO
off the attained reporter branch.
-/
theorem lg21_positive_reporter_strict_gain_of_pbo
    {Score : Type*} [MeasurableSpace Score] [LinearOrder Score]
    (testLaw takerScoreLaw reporterLaw : Measure Score)
    [IsProbabilityMeasure reporterLaw]
    (report : Score -> Bool)
    (reportedPayoff posterior : Score -> ℝ) (noReportPayoff : ℝ)
    (hreporter_ac_taker : reporterLaw ≪ takerScoreLaw)
    (htaker_ac_test : takerScoreLaw ≪ testLaw)
    (hreporter_action : ∀ᵐ score ∂reporterLaw, report score = true)
    (hreportedPBO : reportedPayoff =ᵐ[reporterLaw] posterior)
    (hposterior_strict : StrictMono posterior)
    (hreporter_singleton : ∀ score, reporterLaw {score} = 0)
    (hreportBestResponse : ∀ᵐ score ∂reporterLaw,
      noReportPayoff ≤ reportedPayoff score) :
    0 < testLaw {score | report score = true ∧
      noReportPayoff < reportedPayoff score} := by
  let strictGain : Set Score := {score | report score = true ∧
    noReportPayoff < reportedPayoff score}
  let posteriorLevel : Set Score := {score | posterior score = noReportPayoff}
  have hlevelSubsingleton : posteriorLevel.Subsingleton := by
    intro left hleft right hright
    apply hposterior_strict.injective
    exact hleft.trans hright.symm
  have hlevelNull : reporterLaw posteriorLevel = 0 := by
    by_cases hempty : posteriorLevel = ∅
    · simp [hempty]
    · obtain ⟨score, hscore⟩ := Set.nonempty_iff_ne_empty.mpr hempty
      apply measure_mono_null
        (fun candidate hcandidate =>
          Set.mem_singleton_iff.mpr (hlevelSubsingleton hcandidate hscore))
      exact hreporter_singleton score
  have hstrictGainAE : ∀ᵐ score ∂reporterLaw, score ∈ strictGain := by
    have hnotLevel : ∀ᵐ score ∂reporterLaw, score ∉ posteriorLevel := by
      rw [ae_iff]
      simpa [posteriorLevel] using hlevelNull
    filter_upwards [hreporter_action, hreportedPBO, hreportBestResponse,
      hnotLevel] with score hreport hPBO hbest hnotLevel
    refine ⟨hreport, ?_⟩
    have hbest' : noReportPayoff ≤ posterior score := by
      rw [← hPBO]
      exact hbest
    rw [hPBO]
    apply lt_of_le_of_ne hbest'
    intro heq
    apply hnotLevel
    simpa [posteriorLevel] using heq.symm
  have hstrictGainPositiveReporter : 0 < reporterLaw strictGain := by
    by_contra hnotPositive
    have hzero : reporterLaw strictGain = 0 := bot_unique (le_of_not_gt hnotPositive)
    have hnotAE : ∀ᵐ score ∂reporterLaw, score ∉ strictGain := by
      rw [ae_iff]
      simpa only [Set.mem_setOf_eq, not_not] using hzero
    have hfalse : (∀ᵐ _ ∂reporterLaw, False) :=
      (hstrictGainAE.and hnotAE).mono fun _ h => h.2 h.1
    rw [ae_iff] at hfalse
    have honeZero : (1 : ℝ≥0∞) = 0 := by
      simpa using hfalse
    exact one_ne_zero honeZero
  have hstrictGainPositiveTaker : 0 < takerScoreLaw strictGain := by
    by_contra hnotPositive
    have hzero : takerScoreLaw strictGain = 0 :=
      bot_unique (le_of_not_gt hnotPositive)
    exact (ne_of_gt hstrictGainPositiveReporter)
      (hreporter_ac_taker hzero)
  have hstrictGainPositiveTest : 0 < testLaw strictGain := by
    by_contra hnotPositive
    have hzero : testLaw strictGain = 0 :=
      bot_unique (le_of_not_gt hnotPositive)
    exact (ne_of_gt hstrictGainPositiveTaker) (htaker_ac_test hzero)
  simpa [strictGain] using hstrictGainPositiveTest

/--
The score marginal generated after an arbitrary positive latent selection is
dominated by every nondegenerate individual Gaussian test law.  This is the
direction needed to carry positive reporter mass back to a hypothetical
no-taker's score draw.  It follows from the literal selected-score density,
not from a value assigned on a null action history.
-/
theorem lg21_selectedGaussianSignal_selectedScoreLaw_absolutelyContinuous_testLaw
    (priorMean priorVariance noiseVariance : ℝ) (selected : Set ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (skill : ℝ) :
    letI : IsMarkovKernel
        (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance) :=
      lg21_gaussianSignalPosteriorKernel_isMarkov
        priorMean priorVariance noiseVariance
    normalizedSelectedBase
      (gaussianReal priorMean (priorVariance + noiseVariance).toNNReal)
      (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)
      (Set.univ ×ˢ selected) ≪
      gaussianReal skill noiseVariance.toNNReal := by
  letI : IsMarkovKernel
      (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance) :=
    lg21_gaussianSignalPosteriorKernel_isMarkov
      priorMean priorVariance noiseVariance
  let scoreLaw : Measure ℝ :=
    gaussianReal priorMean (priorVariance + noiseVariance).toNNReal
  let posterior : Kernel ℝ ℝ :=
    gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance
  let event : Set (ℝ × ℝ) := Set.univ ×ˢ selected
  have hnoiseNN : 0 < noiseVariance.toNNReal :=
    Real.toNNReal_pos.mpr hnoiseVariance
  have hscoreNN : 0 < (priorVariance + noiseVariance).toNNReal :=
    Real.toNNReal_pos.mpr (add_pos hpriorVariance hnoiseVariance)
  change ((scoreLaw ⊗ₘ posterior) event)⁻¹ •
      scoreLaw.withDensity (selectionMass posterior event) ≪
        gaussianReal skill noiseVariance.toNNReal
  exact Measure.smul_absolutelyContinuous.trans
    ((withDensity_absolutelyContinuous scoreLaw
      (selectionMass posterior event)).trans
      (AppliedModelingLib.Probability.gaussianReal_absolutelyContinuous_of_positive_variances
        priorMean skill hscoreNN hnoiseNN))

/-- The observed-score marginal of a positive selected Gaussian experiment is
a probability law.  This is obtained by mapping the normalized selected joint
law, rather than by treating a density normalizer as an informal convention. -/
theorem lg21_selectedGaussianSignal_selectedScoreLaw_isProbability
    (priorMean priorVariance noiseVariance : ℝ) (selected : Set ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hselectedMeasurable : MeasurableSet selected)
    (hselected : 0 < gaussianReal priorMean priorVariance.toNNReal selected) :
    letI : IsMarkovKernel
        (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance) :=
      lg21_gaussianSignalPosteriorKernel_isMarkov
        priorMean priorVariance noiseVariance
    IsProbabilityMeasure
      (normalizedSelectedBase
        (gaussianReal priorMean (priorVariance + noiseVariance).toNNReal)
        (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)
        (Set.univ ×ˢ selected)) := by
  letI : IsMarkovKernel
      (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance) :=
    lg21_gaussianSignalPosteriorKernel_isMarkov
      priorMean priorVariance noiseVariance
  let scoreLaw : Measure ℝ :=
    gaussianReal priorMean (priorVariance + noiseVariance).toNNReal
  let posterior : Kernel ℝ ℝ :=
    gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance
  let event : Set (ℝ × ℝ) := Set.univ ×ˢ selected
  let selectedJoint : Measure (ℝ × ℝ) :=
    lg21NormalizedRestriction (scoreLaw ⊗ₘ posterior) event
  have hselection : (scoreLaw ⊗ₘ posterior) event ≠ 0 := by
    simpa [scoreLaw, posterior, event] using
      (lg21_gaussianSignal_selected_event_ne_zero
        priorMean priorVariance noiseVariance selected hpriorVariance hnoiseVariance
        hselectedMeasurable hselected)
  letI : IsProbabilityMeasure selectedJoint :=
    lg21NormalizedRestriction_isProbability (scoreLaw ⊗ₘ posterior) event hselection
      (measure_ne_top _ _)
  have hpositive : ∀ score, selectionMass posterior event score ≠ 0 := by
    simpa [posterior, event] using
      (lg21_gaussianSignalPosterior_selectionMass_ne_zero
        priorMean priorVariance noiseVariance selected hpriorVariance hnoiseVariance
        hselected)
  have hevent : MeasurableSet event := by
    exact MeasurableSet.univ.prod hselectedMeasurable
  letI : SFinite (selectedBase scoreLaw posterior event) := by
    unfold selectedBase
    infer_instance
  letI : SFinite (normalizedSelectedBase scoreLaw posterior event) := by
    unfold normalizedSelectedBase
    infer_instance
  letI : IsMarkovKernel (selectedNormalizedKernel posterior event) :=
    selectedNormalizedKernel_isMarkov hevent hpositive
  have hfactor : selectedJoint =
      normalizedSelectedBase scoreLaw posterior event ⊗ₘ
        selectedNormalizedKernel posterior event := by
    exact normalizedRestriction_compProd_selectedNormalizedKernel
      (μ := scoreLaw) (κ := posterior) hevent hpositive
  have hfirst : selectedJoint.map Prod.fst =
      normalizedSelectedBase scoreLaw posterior event := by
    calc
      selectedJoint.map Prod.fst =
          (normalizedSelectedBase scoreLaw posterior event ⊗ₘ
            selectedNormalizedKernel posterior event).map Prod.fst := by
            rw [hfactor]
      _ = (normalizedSelectedBase scoreLaw posterior event ⊗ₘ
            selectedNormalizedKernel posterior event).fst := rfl
      _ = normalizedSelectedBase scoreLaw posterior event :=
        Measure.fst_compProd _ _
  have hmapProbability : IsProbabilityMeasure (selectedJoint.map Prod.fst) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  simpa [scoreLaw, posterior, event] using hfirst ▸ hmapProbability

/--
Fixed-base source-facing closure for the positive-reporter branch.  `selected`
is the literal measurable set of latent skills that take the test at this
base; `report` is the literal post-score action.  No cutoff or global
all-taking conclusion is assumed.  The sole PBO input is its a.e. identity on
the attained reporter law.
-/
theorem lg21_positive_reporter_selectedGaussian_strict_test_gain
    (priorMean priorVariance noiseVariance : ℝ)
    (selected : Set ℝ) (report : ℝ -> Bool)
    [IsMarkovKernel
      (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)]
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hselectedMeasurable : MeasurableSet selected)
    (hselected : 0 < gaussianReal priorMean priorVariance.toNNReal selected)
    (hreportMeasurable : MeasurableSet {score | report score = true})
    (hreporterPositive :
      0 < normalizedSelectedBase
        (gaussianReal priorMean (priorVariance + noiseVariance).toNNReal)
        (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)
        (Set.univ ×ˢ selected)
        {score | report score = true})
    (reportedPayoff : ℝ -> ℝ) (noReportPayoff : ℝ)
    (hreportedPBO :
      reportedPayoff =ᵐ[
        lg21NormalizedRestriction
          (normalizedSelectedBase
            (gaussianReal priorMean (priorVariance + noiseVariance).toNNReal)
            (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)
            (Set.univ ×ˢ selected))
          {score | report score = true}]
        fun score => ∫ latentSkill, latentSkill ∂selectedNormalizedKernel
          (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)
          (Set.univ ×ˢ selected) score)
    (hreportBestResponse : ∀ᵐ score ∂
      lg21NormalizedRestriction
        (normalizedSelectedBase
          (gaussianReal priorMean (priorVariance + noiseVariance).toNNReal)
          (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)
          (Set.univ ×ˢ selected))
        {score | report score = true},
      noReportPayoff ≤ reportedPayoff score) :
    ∀ skill,
      0 < gaussianReal skill noiseVariance.toNNReal
        {score | report score = true ∧ noReportPayoff < reportedPayoff score} := by
  let rawScoreLaw : Measure ℝ :=
    gaussianReal priorMean (priorVariance + noiseVariance).toNNReal
  let posterior : Kernel ℝ ℝ :=
    gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance
  let selectedEvent : Set (ℝ × ℝ) := Set.univ ×ˢ selected
  let takerScoreLaw : Measure ℝ :=
    normalizedSelectedBase rawScoreLaw posterior selectedEvent
  let reportSet : Set ℝ := {score | report score = true}
  let reporterLaw : Measure ℝ :=
    lg21NormalizedRestriction takerScoreLaw reportSet
  letI : IsProbabilityMeasure takerScoreLaw := by
    simpa [takerScoreLaw, rawScoreLaw, posterior, selectedEvent] using
      (lg21_selectedGaussianSignal_selectedScoreLaw_isProbability
        priorMean priorVariance noiseVariance selected hpriorVariance hnoiseVariance
        hselectedMeasurable hselected)
  letI : IsFiniteMeasure takerScoreLaw := ⟨by simp⟩
  have hreporterLawProbability : IsProbabilityMeasure reporterLaw := by
    dsimp [reporterLaw]
    apply lg21NormalizedRestriction_isProbability
    · simpa [takerScoreLaw, rawScoreLaw, posterior, selectedEvent, reportSet]
        using ne_of_gt hreporterPositive
    · exact measure_ne_top _ _
  letI : IsProbabilityMeasure reporterLaw := hreporterLawProbability
  have hreporter_ac_taker : reporterLaw ≪ takerScoreLaw := by
    dsimp [reporterLaw]
    exact Measure.smul_absolutelyContinuous.trans
      Measure.restrict_le_self.absolutelyContinuous
  have htaker_ac_test : ∀ skill,
      takerScoreLaw ≪ gaussianReal skill noiseVariance.toNNReal := by
    intro skill
    simpa [takerScoreLaw, rawScoreLaw, posterior, selectedEvent] using
      (lg21_selectedGaussianSignal_selectedScoreLaw_absolutelyContinuous_testLaw
        priorMean priorVariance noiseVariance selected hpriorVariance hnoiseVariance skill)
  have hreporter_action : ∀ᵐ score ∂reporterLaw, report score = true := by
    change ∀ᵐ score ∂(takerScoreLaw reportSet)⁻¹ •
        takerScoreLaw.restrict reportSet, report score = true
    apply Measure.ae_smul_measure
    rw [ae_restrict_iff' hreportMeasurable]
    exact Filter.Eventually.of_forall fun score hscore => hscore
  have hposterior_strict : StrictMono (fun score =>
      ∫ latentSkill, latentSkill ∂selectedNormalizedKernel posterior
        selectedEvent score) := by
    simpa [posterior, selectedEvent] using
      (lg21_selectedGaussianSignal_posteriorMean_strictMono
        priorMean priorVariance noiseVariance selected hpriorVariance hnoiseVariance
        hselectedMeasurable hselected)
  have hreporter_singleton : ∀ score, reporterLaw {score} = 0 := by
    intro score
    apply hreporter_ac_taker
    apply htaker_ac_test score
    letI : NoAtoms (gaussianReal score noiseVariance.toNNReal) :=
      noAtoms_gaussianReal (ne_of_gt (Real.toNNReal_pos.mpr hnoiseVariance))
    exact measure_singleton score
  have hreportedPBO' : reportedPayoff =ᵐ[reporterLaw] fun score =>
      ∫ latentSkill, latentSkill ∂selectedNormalizedKernel posterior
        selectedEvent score := by
    simpa [reporterLaw, takerScoreLaw, rawScoreLaw, posterior, selectedEvent,
      reportSet] using hreportedPBO
  have hreportBestResponse' : ∀ᵐ score ∂reporterLaw,
      noReportPayoff ≤ reportedPayoff score := by
    simpa [reporterLaw, takerScoreLaw, rawScoreLaw, posterior, selectedEvent,
      reportSet] using hreportBestResponse
  intro skill
  exact lg21_positive_reporter_strict_gain_of_pbo
    (gaussianReal skill noiseVariance.toNNReal) takerScoreLaw reporterLaw
    report reportedPayoff
    (fun score => ∫ latentSkill, latentSkill ∂selectedNormalizedKernel posterior
      selectedEvent score)
    noReportPayoff hreporter_ac_taker (htaker_ac_test skill)
    hreporter_action hreportedPBO' hposterior_strict hreporter_singleton
    hreportBestResponse'

/--
At one public-base fibre, the preceding attained-reporter calculation rules
out no-takers under Definition 1's actual pre-score best response.  The
caller must derive `hreportedPBO` using the literal action-selected population
for the same `selected` set; this theorem neither substitutes an unselected
posterior nor assumes a reporting or taking cutoff.
-/
theorem lg21_positive_reporter_selectedGaussian_all_take_at_base
    {Base : Type*}
    (E : LG21OptionalSequentialEquilibriumData ℝ Base ℝ)
    (hEq : lg21OptionalSequentialEquilibrium E) (base : Base)
    (priorMean priorVariance noiseVariance : ℝ)
    (selected : Set ℝ)
    [IsMarkovKernel
      (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)]
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hselectedMeasurable : MeasurableSet selected)
    (hselected : 0 < gaussianReal priorMean priorVariance.toNNReal selected)
    (hreportMeasurable : MeasurableSet
      {score | E.reportDecision base score = true})
    (hreporterPositive :
      0 < normalizedSelectedBase
        (gaussianReal priorMean (priorVariance + noiseVariance).toNNReal)
        (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)
        (Set.univ ×ˢ selected)
        {score | E.reportDecision base score = true})
    (htestLaw : ∀ skill,
      E.testLaw skill base = gaussianReal skill noiseVariance.toNNReal)
    (hreportedPBO :
      E.reportedPayoff base =ᵐ[
        lg21NormalizedRestriction
          (normalizedSelectedBase
            (gaussianReal priorMean (priorVariance + noiseVariance).toNNReal)
            (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)
            (Set.univ ×ˢ selected))
          {score | E.reportDecision base score = true}]
        fun score => ∫ latentSkill, latentSkill ∂selectedNormalizedKernel
          (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)
          (Set.univ ×ˢ selected) score)
    (hreportBestResponse : ∀ᵐ score ∂
      lg21NormalizedRestriction
        (normalizedSelectedBase
          (gaussianReal priorMean (priorVariance + noiseVariance).toNNReal)
          (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)
          (Set.univ ×ˢ selected))
        {score | E.reportDecision base score = true},
      E.noReportPayoff base ≤ E.reportedPayoff base score) :
    ∀ skill, E.takeDecision skill base = true := by
  have hstrictGain : ∀ skill,
      0 < gaussianReal skill noiseVariance.toNNReal
        {score | E.reportDecision base score = true ∧
          E.noReportPayoff base < E.reportedPayoff base score} := by
    exact lg21_positive_reporter_selectedGaussian_strict_test_gain
      priorMean priorVariance noiseVariance selected (E.reportDecision base)
      hpriorVariance hnoiseVariance hselectedMeasurable hselected hreportMeasurable
      hreporterPositive (E.reportedPayoff base) (E.noReportPayoff base)
      hreportedPBO hreportBestResponse
  intro skill
  by_contra hnotTake
  have hbest :=
    (lg21OptionalSequentialEquilibrium_take_bestResponse hEq base).2 skill hnotTake
  have hstrict : E.noReportPayoff base <
      lg21OptionalSequentialTakeExpectedPayoff E skill base := by
    apply lg21OptionalSequentialTakeExpectedPayoff_gt_noReport_of_positive_strict_gain
      E hEq skill base
    rw [htestLaw skill]
    exact hstrictGain skill
  exact (not_le_of_gt hstrict) hbest

/-- Source-facing version of the positive-reporter closure.  It requires the
two literal sequential best-response implications directly, so callers do
not have to package them through a legacy equilibrium-consistency predicate. -/
theorem lg21_positive_reporter_selectedGaussian_all_take_at_base_of_bestResponses
    {Base : Type*}
    (E : LG21OptionalSequentialEquilibriumData ℝ Base ℝ) (base : Base)
    (priorMean priorVariance noiseVariance : ℝ)
    (selected : Set ℝ)
    [IsMarkovKernel
      (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)]
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hselectedMeasurable : MeasurableSet selected)
    (hselected : 0 < gaussianReal priorMean priorVariance.toNNReal selected)
    (hreportMeasurable : MeasurableSet
      {score | E.reportDecision base score = true})
    (hreporterPositive :
      0 < normalizedSelectedBase
        (gaussianReal priorMean (priorVariance + noiseVariance).toNNReal)
        (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)
        (Set.univ ×ˢ selected)
        {score | E.reportDecision base score = true})
    (htestLaw : ∀ skill,
      E.testLaw skill base = gaussianReal skill noiseVariance.toNNReal)
    (hreportedPBO :
      E.reportedPayoff base =ᵐ[
        lg21NormalizedRestriction
          (normalizedSelectedBase
            (gaussianReal priorMean (priorVariance + noiseVariance).toNNReal)
            (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)
            (Set.univ ×ˢ selected))
          {score | E.reportDecision base score = true}]
        fun score => ∫ latentSkill, latentSkill ∂selectedNormalizedKernel
          (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)
          (Set.univ ×ˢ selected) score)
    (hreportBestResponse : ∀ score,
      E.reportDecision base score = true ->
        E.noReportPayoff base ≤ E.reportedPayoff base score)
    (htakeBestResponse : ∀ skill,
      E.takeDecision skill base = false ->
        lg21OptionalSequentialTakeExpectedPayoff E skill base ≤
          E.noReportPayoff base) :
    ∀ skill, E.takeDecision skill base = true := by
  have hstrictGain : ∀ skill,
      0 < gaussianReal skill noiseVariance.toNNReal
        {score | E.reportDecision base score = true ∧
          E.noReportPayoff base < E.reportedPayoff base score} := by
    apply lg21_positive_reporter_selectedGaussian_strict_test_gain
      priorMean priorVariance noiseVariance selected (E.reportDecision base)
      hpriorVariance hnoiseVariance hselectedMeasurable hselected hreportMeasurable
      hreporterPositive (E.reportedPayoff base) (E.noReportPayoff base)
      hreportedPBO
    let reportLaw : Measure ℝ :=
      lg21NormalizedRestriction
        (normalizedSelectedBase
          (gaussianReal priorMean (priorVariance + noiseVariance).toNNReal)
          (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)
          (Set.univ ×ˢ selected))
        {score | E.reportDecision base score = true}
    have hreportAction : ∀ᵐ score ∂reportLaw,
        E.reportDecision base score = true := by
      change ∀ᵐ score ∂
          (normalizedSelectedBase
            (gaussianReal priorMean (priorVariance + noiseVariance).toNNReal)
            (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)
            (Set.univ ×ˢ selected)
            {score | E.reportDecision base score = true})⁻¹ •
            (normalizedSelectedBase
              (gaussianReal priorMean (priorVariance + noiseVariance).toNNReal)
              (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)
              (Set.univ ×ˢ selected)).restrict
              {score | E.reportDecision base score = true},
          E.reportDecision base score = true
      apply Measure.ae_smul_measure
      rw [ae_restrict_iff' hreportMeasurable]
      exact Filter.Eventually.of_forall fun score hscore => hscore
    filter_upwards [hreportAction] with score hreport
    exact hreportBestResponse score hreport
  intro skill
  by_contra hnotTake
  have hnotTake' : E.takeDecision skill base = false := by
    cases hdecision : E.takeDecision skill base <;> simp_all
  have hbest := htakeBestResponse skill hnotTake'
  have hstrict : E.noReportPayoff base <
      lg21OptionalSequentialTakeExpectedPayoff E skill base := by
    apply lg21OptionalSequentialTakeExpectedPayoff_gt_noReport_of_positive_strict_gain_of_reportBR
      E skill base hreportBestResponse
    rw [htestLaw skill]
    exact hstrictGain skill
  exact (not_le_of_gt hstrict) hbest

end

end LG21TestOptionalPolicies

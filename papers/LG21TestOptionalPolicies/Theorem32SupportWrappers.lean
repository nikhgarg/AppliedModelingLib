import LG21TestOptionalPolicies.MainTheorems

/-!
# Theorem 3.2 Support-Conversion Wrappers

Small wrappers that sit on top of `MainTheorems.lean`.  They are kept in a
separate module so future support-conversion endpoints can compile without
re-elaborating the main LG21 proof file.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib
open AppliedModelingLib.Probability

/--
Full-support value-level optional-reporting Gaussian `P_BO` endpoint with the
source equilibrium's reporting decision stated literally as the Gaussian
`P_BO` threshold comparison.
-/
theorem paper_theorem3_2_section3_optional_reporting_value_no_test_relevance_of_gaussian_pbo_literal_decision_supported_finite_test_full_support
    {Feature Skill Base Test Actor Equilibrium : Type*}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    [Fintype Test] [DecidableEq Test]
    [Fintype Actor] [DecidableEq Actor]
    (PBO : Base → (Feature → ℝ) → ℝ)
    (M : Base → GaussianOffsetSignalFamily Feature)
    (theta : Base → Feature → ℝ) (k : Feature)
    (skillGivenBase : Base → PMF Skill)
    (demographicAccessEstimate demographicNoAccessEstimate :
      Equilibrium → PMF ℝ)
    (takeDecision : Equilibrium → Skill → Base → Bool)
    (estimationConsistent : Equilibrium → Prop)
    (referenceSkill : Equilibrium → Base → Skill)
    (reporterPMF noReporterPMF : Equilibrium → Base → PMF ℝ)
    (testLaw : Equilibrium → Base → PMF Test)
    (scoreOfTest : Equilibrium → Base → Test → ℝ)
    (actorValue : Equilibrium → Base → Actor → ℝ)
    (actorOfScore : Equilibrium → Base → ℝ → Actor)
    (pboThreshold : Equilibrium → Base → ℝ)
    (hPBO : ∀ base obs, PBO base obs = (M base).posteriorMean obs)
    (hsupport_abovePBO :
      ∀ e base test, 0 < (testLaw e base test).toReal →
        pboThreshold e base ≤
          PBO base
            (Function.update (theta base) k
              (actorValue e base
                (actorOfScore e base (scoreOfTest e base test)))))
    (hfull_support : ∀ e base test, 0 < (testLaw e base test).toReal)
    (baseTerm signalWeight denom : Equilibrium → Base → ℝ)
    (hEq :
      ∀ e,
        lg21SourceEquilibrium
          (lg21OptionalReportingBaseSourceEquilibriumData
            (takeDecision e)
            (fun base actor =>
              if pboThreshold e base ≤
                  PBO base (Function.update (theta base) k actor) then
                true
              else
                false)
            (fun base actor =>
              (baseTerm e base + signalWeight e base * actor) / denom e base)
            (fun base =>
              (baseTerm e base +
                  signalWeight e base *
                    pmfExp (((testLaw e base).map (scoreOfTest e base)).map
                      (actorOfScore e base)) (actorValue e base)) /
                denom e base)
            (estimationConsistent e)))
    (hweight : ∀ e base, 0 < signalWeight e base)
    (hdenom : ∀ e base, 0 < denom e base)
    (hfair :
      let decisionThreshold : Equilibrium → Base → ℝ :=
        lg21GaussianPosteriorMeanPBOCutoff M theta k pboThreshold
      let reportDecision : Equilibrium → Base → ℝ → Bool :=
        fun e base actor =>
          if decisionThreshold e base ≤ actor then true else false
      let reporterEvent : Equilibrium → Base → Test → Prop :=
        fun e base test =>
          reportDecision e base
              (actorValue e base
                (actorOfScore e base (scoreOfTest e base test))) =
            true
      let decReporterEvent : ∀ e base, DecidablePred (reporterEvent e base) :=
        fun _e _base _test => inferInstance
      let positiveShare :=
        lg21PMFEventShareFn testLaw reporterEvent decReporterEvent
      let hpositiveShare_le_one :=
        lg21PMFEventShareFn_le_one testLaw reporterEvent decReporterEvent
      let latentAccessEstimate : Equilibrium → Skill → Base → PMF ℝ :=
        fun e _ base =>
          lg21BinaryMixturePMF
            (positiveShare e base) (hpositiveShare_le_one e base)
            (reporterPMF e base) (noReporterPMF e base)
      let latentNoAccessEstimate : Equilibrium → Skill → Base → PMF ℝ :=
        fun e _ base => noReporterPMF e base
      let actorLaw : Equilibrium → Base → PMF Actor :=
        fun e base =>
          ((testLaw e base).map (scoreOfTest e base)).map
            (actorOfScore e base)
      let S :=
        lg21BinaryMixturePointEstimateSurface
          (Skill := Skill) (Base := Base) (Test := ℝ) (Actor := Actor)
          Equilibrium latentAccessEstimate latentNoAccessEstimate
          demographicAccessEstimate demographicNoAccessEstimate positiveShare
          hpositiveShare_le_one reporterPMF noReporterPMF actorLaw actorValue
          actorOfScore
      lg21SourceLatentSkillFair S ∨ lg21SourceObservablyFair S) :
    let decisionThreshold : Equilibrium → Base → ℝ :=
      lg21GaussianPosteriorMeanPBOCutoff M theta k pboThreshold
    lg21GaussianPosteriorMeanPBOFormula PBO M ∧
      (∀ e base score,
        pboThreshold e base ≤
            PBO base (Function.update (theta base) k score) ↔
          decisionThreshold e base ≤ score) ∧
        ¬ ∃ e base test,
          pmfExp (((testLaw e base).map (scoreOfTest e base)).map
            (actorOfScore e base)) (actorValue e base) ≠
            actorValue e base
              (actorOfScore e base (scoreOfTest e base test)) := by
  have hsupport :=
    paper_theorem3_2_section3_optional_reporting_no_positive_mass_test_relevance_of_gaussian_pbo_literal_decision_supported_finite_test_cutoff
      PBO M theta k skillGivenBase demographicAccessEstimate
      demographicNoAccessEstimate takeDecision estimationConsistent
      referenceSkill reporterPMF noReporterPMF testLaw scoreOfTest actorValue
      actorOfScore pboThreshold hPBO hsupport_abovePBO baseTerm signalWeight
      denom hEq hweight hdenom hfair
  refine ⟨hsupport.1, hsupport.2.1, ?_⟩
  exact
    lg21NoValueRelevance_of_noPositiveMassPointMassRelevance_of_fullSupport
      testLaw
      (fun e base =>
        pmfExp (((testLaw e base).map (scoreOfTest e base)).map
          (actorOfScore e base)) (actorValue e base))
      (fun e base test =>
        actorValue e base
          (actorOfScore e base (scoreOfTest e base test)))
      hfull_support hsupport.2.2

/--
Full-support value-level optional-reporting Gaussian `P_BO` endpoint with
direct binary report/withhold best response and direct finite-test threshold
support.
-/
theorem paper_theorem3_2_section3_optional_reporting_value_no_test_relevance_of_gaussian_pbo_binary_choice_literal_decision_supported_finite_test_full_support
    {Feature Skill Base Test Actor Equilibrium : Type*}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    [Fintype Test] [DecidableEq Test]
    [Fintype Actor] [DecidableEq Actor]
    (PBO : Base → (Feature → ℝ) → ℝ)
    (M : Base → GaussianOffsetSignalFamily Feature)
    (theta : Base → Feature → ℝ) (k : Feature)
    (skillGivenBase : Base → PMF Skill)
    (demographicAccessEstimate demographicNoAccessEstimate :
      Equilibrium → PMF ℝ)
    (estimationConsistent : Equilibrium → Prop)
    (referenceSkill : Equilibrium → Base → Skill)
    (reporterPMF noReporterPMF : Equilibrium → Base → PMF ℝ)
    (testLaw : Equilibrium → Base → PMF Test)
    (scoreOfTest : Equilibrium → Base → Test → ℝ)
    (actorValue : Equilibrium → Base → Actor → ℝ)
    (actorOfScore : Equilibrium → Base → ℝ → Actor)
    (pboThreshold : Equilibrium → Base → ℝ)
    (hPBO : ∀ base obs, PBO base obs = (M base).posteriorMean obs)
    (hsupport_abovePBO :
      ∀ e base test, 0 < (testLaw e base test).toReal →
        pboThreshold e base ≤
          PBO base
            (Function.update (theta base) k
              (actorValue e base
                (actorOfScore e base (scoreOfTest e base test)))))
    (hfull_support : ∀ e base test, 0 < (testLaw e base test).toReal)
    (baseTerm signalWeight denom : Equilibrium → Base → ℝ)
    (hbest :
      ∀ e base,
        lg21NoProfitableBinaryChoiceDeviation
          (fun score : ℝ =>
            (if pboThreshold e base ≤
                PBO base (Function.update (theta base) k score) then
              true
            else
              false) =
              true)
          (fun score : ℝ =>
            (baseTerm e base + signalWeight e base * score) / denom e base)
          (fun _score : ℝ =>
            (baseTerm e base +
                signalWeight e base *
                  pmfExp (((testLaw e base).map (scoreOfTest e base)).map
                    (actorOfScore e base)) (actorValue e base)) /
              denom e base))
    (hconsistent : ∀ e, estimationConsistent e)
    (hweight : ∀ e base, 0 < signalWeight e base)
    (hdenom : ∀ e base, 0 < denom e base)
    (hfair :
      let decisionThreshold : Equilibrium → Base → ℝ :=
        lg21GaussianPosteriorMeanPBOCutoff M theta k pboThreshold
      let reportDecision : Equilibrium → Base → ℝ → Bool :=
        fun e base actor =>
          if decisionThreshold e base ≤ actor then true else false
      let reporterEvent : Equilibrium → Base → Test → Prop :=
        fun e base test =>
          reportDecision e base
              (actorValue e base
                (actorOfScore e base (scoreOfTest e base test))) =
            true
      let decReporterEvent : ∀ e base, DecidablePred (reporterEvent e base) :=
        fun _e _base _test => inferInstance
      let positiveShare :=
        lg21PMFEventShareFn testLaw reporterEvent decReporterEvent
      let hpositiveShare_le_one :=
        lg21PMFEventShareFn_le_one testLaw reporterEvent decReporterEvent
      let latentAccessEstimate : Equilibrium → Skill → Base → PMF ℝ :=
        fun e _ base =>
          lg21BinaryMixturePMF
            (positiveShare e base) (hpositiveShare_le_one e base)
            (reporterPMF e base) (noReporterPMF e base)
      let latentNoAccessEstimate : Equilibrium → Skill → Base → PMF ℝ :=
        fun e _ base => noReporterPMF e base
      let actorLaw : Equilibrium → Base → PMF Actor :=
        fun e base =>
          ((testLaw e base).map (scoreOfTest e base)).map
            (actorOfScore e base)
      let S :=
        lg21BinaryMixturePointEstimateSurface
          (Skill := Skill) (Base := Base) (Test := ℝ) (Actor := Actor)
          Equilibrium latentAccessEstimate latentNoAccessEstimate
          demographicAccessEstimate demographicNoAccessEstimate positiveShare
          hpositiveShare_le_one reporterPMF noReporterPMF actorLaw actorValue
          actorOfScore
      lg21SourceLatentSkillFair S ∨ lg21SourceObservablyFair S) :
    let decisionThreshold : Equilibrium → Base → ℝ :=
      lg21GaussianPosteriorMeanPBOCutoff M theta k pboThreshold
    lg21GaussianPosteriorMeanPBOFormula PBO M ∧
      (∀ e base score,
        pboThreshold e base ≤
            PBO base (Function.update (theta base) k score) ↔
          decisionThreshold e base ≤ score) ∧
        ¬ ∃ e base test,
          pmfExp (((testLaw e base).map (scoreOfTest e base)).map
            (actorOfScore e base)) (actorValue e base) ≠
            actorValue e base
              (actorOfScore e base (scoreOfTest e base test)) := by
  have hsupport :=
    paper_theorem3_2_section3_optional_reporting_no_positive_mass_test_relevance_of_gaussian_pbo_binary_choice_literal_decision_supported_finite_test_cutoff
      PBO M theta k skillGivenBase demographicAccessEstimate
      demographicNoAccessEstimate estimationConsistent referenceSkill
      reporterPMF noReporterPMF testLaw scoreOfTest actorValue actorOfScore
      pboThreshold hPBO hsupport_abovePBO baseTerm signalWeight denom
      hbest hconsistent hweight hdenom hfair
  refine ⟨hsupport.1, hsupport.2.1, ?_⟩
  exact
    lg21NoValueRelevance_of_noPositiveMassPointMassRelevance_of_fullSupport
      testLaw
      (fun e base =>
        pmfExp (((testLaw e base).map (scoreOfTest e base)).map
          (actorOfScore e base)) (actorValue e base))
      (fun e base test =>
        actorValue e base
          (actorOfScore e base (scoreOfTest e base test)))
      hfull_support hsupport.2.2

/--
Gaussian cutoff support implies literal Gaussian `P_BO` actor support.  This is
the converse packaging to the cutoff-support bridge in `MainTheorems`.
-/
theorem lg21_gaussian_pbo_literal_decision_actor_support_of_cutoff_support
    {Feature Base Actor Equilibrium : Type*}
    [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
    (PBO : Base → (Feature → ℝ) → ℝ)
    (M : Base → GaussianOffsetSignalFamily Feature)
    (theta : Base → Feature → ℝ) (k : Feature)
    (pboThreshold : Equilibrium → Base → ℝ)
    (hPBO : ∀ base obs, PBO base obs = (M base).posteriorMean obs)
    (actorLaw : Equilibrium → Base → PMF Actor)
    (actorValue : Equilibrium → Base → Actor → ℝ)
    (hactorCutoff :
      ∀ e base actor, 0 < (actorLaw e base actor).toReal →
        lg21GaussianPosteriorMeanPBOCutoff M theta k pboThreshold e base ≤
          actorValue e base actor) :
    ∀ e base actor, 0 < (actorLaw e base actor).toReal →
      (if pboThreshold e base ≤
          PBO base
            (Function.update (theta base) k (actorValue e base actor)) then
        true
      else
        false) =
        true := by
  intro e base actor hmass
  have hpbo :
      pboThreshold e base ≤
        PBO base
          (Function.update (theta base) k (actorValue e base actor)) :=
          (lg21GaussianPosteriorMeanPBO_threshold_iff_cutoff
        PBO M theta k pboThreshold hPBO e base
        (actorValue e base actor)).mpr
        (hactorCutoff e base actor hmass)
  simp [hpbo]

/--
Full support of the acting law supplies the point-mass support hypothesis needed
when a proof later evaluates the actor selected by a concrete test.
-/
theorem lg21_actor_of_test_mass_of_full_actor_support
    {Base Test Actor Equilibrium : Type*}
    (actorLaw : Equilibrium → Base → PMF Actor)
    (actorOfTest : Equilibrium → Base → Test → Actor)
    (hfullActorSupport :
      ∀ e base actor, 0 < (actorLaw e base actor).toReal) :
    ∀ e base test, 0 < (actorLaw e base (actorOfTest e base test)).toReal := by
  intro e base test
  exact hfullActorSupport e base (actorOfTest e base test)

/--
Canonical-base-point optional-reporting Gaussian `P_BO` endpoint with Boolean
actor support and full actor-law support, replacing the pointwise `actorOfTest`
mass premise.
-/
noncomputable abbrev paper_theorem3_2_section3_optional_reporting_skill_mixture_raw_mixture_canonical_base_point_estimate_fairness_iff_no_test_relevance_of_gaussian_pbo_base_source_model_literal_decision_event_latent_kernels_actor_support_full_actor_support_affine_noReportPayoff_self_law_classical_decidable :=
  fun {Feature Skill Base Student Equilibrium Actor : Type*}
      [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
      [Fintype Student] [DecidableEq Student]
      [Fintype Actor] [DecidableEq Actor]
      (PBO : Base → (Feature → ℝ) → ℝ)
      (M : Base → GaussianOffsetSignalFamily Feature)
      (theta : Base → Feature → ℝ) (k : Feature)
      (skillGivenBase : Base → PMF Skill)
      (demographicAccessEstimate demographicNoAccessEstimate :
        Equilibrium → PMF ℝ)
      (studentLaw : Equilibrium → Base → PMF Student)
      (studentScore : Equilibrium → Base → Student → ℝ)
      (pboThreshold : Equilibrium → Base → ℝ)
      (reporterPMF : Equilibrium → Base → PMF ℝ)
      (testOf : Equilibrium → Base → ℝ)
      (takeDecision : Equilibrium → Skill → Base → Bool)
      (estimationConsistent : Equilibrium → Prop)
      (referenceSkill : Equilibrium → Base → Skill)
      (actorLaw : Equilibrium → Base → PMF Actor)
      (actorValue : Equilibrium → Base → Actor → ℝ)
      (actorOfTest : Equilibrium → Base → ℝ → Actor)
      (baseTerm signalWeight denom : Equilibrium → Base → ℝ)
      hPBO hEq hactorSupport hweight hdenom hfullPoint
      hfullActorSupport =>
    paper_theorem3_2_section3_optional_reporting_skill_mixture_raw_mixture_canonical_base_point_estimate_fairness_iff_no_test_relevance_of_gaussian_pbo_base_source_model_literal_decision_event_latent_kernels_actor_support_affine_noReportPayoff_self_law_classical_decidable
      PBO M theta k skillGivenBase demographicAccessEstimate
      demographicNoAccessEstimate studentLaw studentScore pboThreshold
      reporterPMF testOf takeDecision estimationConsistent referenceSkill
      actorLaw actorValue actorOfTest baseTerm signalWeight denom hPBO hEq
      hactorSupport hweight hdenom hfullPoint
      (lg21_actor_of_test_mass_of_full_actor_support actorLaw actorOfTest
        hfullActorSupport)

/--
Value-level optional-reporting canonical binary-choice endpoint with Boolean
actor support and full actor-law support.
-/
noncomputable abbrev paper_theorem3_2_section3_optional_reporting_skill_mixture_raw_mixture_canonical_base_point_estimate_fairness_iff_value_no_test_relevance_of_gaussian_pbo_binary_choice_literal_decision_event_latent_kernels_actor_support_full_actor_support_affine_noReportPayoff_self_law_classical_decidable :=
  fun {Feature Skill Base Student Equilibrium Actor : Type*}
      [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
      [Fintype Student] [DecidableEq Student]
      [Fintype Actor] [DecidableEq Actor]
      (PBO : Base → (Feature → ℝ) → ℝ)
      (M : Base → GaussianOffsetSignalFamily Feature)
      (theta : Base → Feature → ℝ) (k : Feature)
      (skillGivenBase : Base → PMF Skill)
      (demographicAccessEstimate demographicNoAccessEstimate :
        Equilibrium → PMF ℝ)
      (studentLaw : Equilibrium → Base → PMF Student)
      (studentScore : Equilibrium → Base → Student → ℝ)
      (pboThreshold : Equilibrium → Base → ℝ)
      (reporterPMF : Equilibrium → Base → PMF ℝ)
      (testOf : Equilibrium → Base → ℝ)
      (estimationConsistent : Equilibrium → Prop)
      (referenceSkill : Equilibrium → Base → Skill)
      (actorLaw : Equilibrium → Base → PMF Actor)
      (actorValue : Equilibrium → Base → Actor → ℝ)
      (actorOfTest : Equilibrium → Base → ℝ → Actor)
      (baseTerm signalWeight denom : Equilibrium → Base → ℝ)
      hPBO hbest hconsistent hactorSupport hweight hdenom hfullPoint
      hfullActorSupport =>
    paper_theorem3_2_section3_optional_reporting_skill_mixture_raw_mixture_canonical_base_point_estimate_fairness_iff_value_no_test_relevance_of_gaussian_pbo_binary_choice_literal_decision_event_latent_kernels_actor_support_affine_noReportPayoff_self_law_classical_decidable
      PBO M theta k skillGivenBase demographicAccessEstimate
      demographicNoAccessEstimate studentLaw studentScore pboThreshold
      reporterPMF testOf estimationConsistent referenceSkill actorLaw
      actorValue actorOfTest baseTerm signalWeight denom hPBO hbest
      hconsistent hactorSupport hweight hdenom hfullPoint
      (lg21_actor_of_test_mass_of_full_actor_support actorLaw actorOfTest
        hfullActorSupport)

/--
Value-level optional-reporting canonical payoff-threshold endpoint with Boolean
actor support and full actor-law support.
-/
noncomputable abbrev paper_theorem3_2_section3_optional_reporting_skill_mixture_raw_mixture_canonical_base_point_estimate_fairness_iff_value_no_test_relevance_of_gaussian_pbo_payoff_threshold_literal_decision_event_latent_kernels_actor_support_full_actor_support_affine_noReportPayoff_self_law_classical_decidable :=
  fun {Feature Skill Base Student Equilibrium Actor : Type*}
      [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
      [Fintype Student] [DecidableEq Student]
      [Fintype Actor] [DecidableEq Actor]
      (PBO : Base → (Feature → ℝ) → ℝ)
      (M : Base → GaussianOffsetSignalFamily Feature)
      (theta : Base → Feature → ℝ) (k : Feature)
      (skillGivenBase : Base → PMF Skill)
      (demographicAccessEstimate demographicNoAccessEstimate :
        Equilibrium → PMF ℝ)
      (studentLaw : Equilibrium → Base → PMF Student)
      (studentScore : Equilibrium → Base → Student → ℝ)
      (pboThreshold : Equilibrium → Base → ℝ)
      (reporterPMF : Equilibrium → Base → PMF ℝ)
      (testOf : Equilibrium → Base → ℝ)
      (estimationConsistent : Equilibrium → Prop)
      (referenceSkill : Equilibrium → Base → Skill)
      (actorLaw : Equilibrium → Base → PMF Actor)
      (actorValue : Equilibrium → Base → Actor → ℝ)
      (actorOfTest : Equilibrium → Base → ℝ → Actor)
      (baseTerm signalWeight denom : Equilibrium → Base → ℝ)
      hPBO hchoice hconsistent hactorSupport hweight hdenom hfullPoint
      hfullActorSupport =>
    paper_theorem3_2_section3_optional_reporting_skill_mixture_raw_mixture_canonical_base_point_estimate_fairness_iff_value_no_test_relevance_of_gaussian_pbo_payoff_threshold_literal_decision_event_latent_kernels_actor_support_affine_noReportPayoff_self_law_classical_decidable
      PBO M theta k skillGivenBase demographicAccessEstimate
      demographicNoAccessEstimate studentLaw studentScore pboThreshold
      reporterPMF testOf estimationConsistent referenceSkill actorLaw
      actorValue actorOfTest baseTerm signalWeight denom hPBO hchoice
      hconsistent hactorSupport hweight hdenom hfullPoint
      (lg21_actor_of_test_mass_of_full_actor_support actorLaw actorOfTest
        hfullActorSupport)

/--
Value-level optional-reporting canonical indifference-cutoff endpoint with
Boolean actor support and full actor-law support.
-/
noncomputable abbrev paper_theorem3_2_section3_optional_reporting_skill_mixture_raw_mixture_canonical_base_point_estimate_fairness_iff_value_no_test_relevance_of_gaussian_pbo_indifference_cutoff_literal_decision_event_latent_kernels_actor_support_full_actor_support_affine_noReportPayoff_self_law_classical_decidable :=
  fun {Feature Skill Base Student Equilibrium Actor : Type*}
      [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
      [Fintype Student] [DecidableEq Student]
      [Fintype Actor] [DecidableEq Actor]
      (PBO : Base → (Feature → ℝ) → ℝ)
      (M : Base → GaussianOffsetSignalFamily Feature)
      (theta : Base → Feature → ℝ) (k : Feature)
      (skillGivenBase : Base → PMF Skill)
      (demographicAccessEstimate demographicNoAccessEstimate :
        Equilibrium → PMF ℝ)
      (studentLaw : Equilibrium → Base → PMF Student)
      (studentScore : Equilibrium → Base → Student → ℝ)
      (pboThreshold : Equilibrium → Base → ℝ)
      (reporterPMF : Equilibrium → Base → PMF ℝ)
      (testOf : Equilibrium → Base → ℝ)
      (estimationConsistent : Equilibrium → Prop)
      (referenceSkill : Equilibrium → Base → Skill)
      (actorLaw : Equilibrium → Base → PMF Actor)
      (actorValue : Equilibrium → Base → Actor → ℝ)
      (actorOfTest : Equilibrium → Base → ℝ → Actor)
      (baseTerm signalWeight denom : Equilibrium → Base → ℝ)
      hPBO hcutoff_eq_mean hconsistent hactorSupport hweight hdenom
      hfullPoint hfullActorSupport =>
    paper_theorem3_2_section3_optional_reporting_skill_mixture_raw_mixture_canonical_base_point_estimate_fairness_iff_value_no_test_relevance_of_gaussian_pbo_indifference_cutoff_literal_decision_event_latent_kernels_actor_support_affine_noReportPayoff_self_law_classical_decidable
      PBO M theta k skillGivenBase demographicAccessEstimate
      demographicNoAccessEstimate studentLaw studentScore pboThreshold
      reporterPMF testOf estimationConsistent referenceSkill actorLaw
      actorValue actorOfTest baseTerm signalWeight denom hPBO hcutoff_eq_mean
      hconsistent hactorSupport hweight hdenom hfullPoint
      (lg21_actor_of_test_mass_of_full_actor_support actorLaw actorOfTest
        hfullActorSupport)

/--
Canonical-base-point optional-reporting Gaussian `P_BO` endpoint with lower
cutoff support stated directly rather than through the Boolean literal
reporting decision.
-/
noncomputable abbrev paper_theorem3_2_section3_optional_reporting_skill_mixture_raw_mixture_canonical_base_point_estimate_fairness_iff_no_test_relevance_of_gaussian_pbo_base_source_model_literal_decision_event_latent_kernels_threshold_support_affine_noReportPayoff_self_law_classical_decidable :=
  fun {Feature Skill Base Student Equilibrium Actor : Type*}
      [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
      [Fintype Student] [DecidableEq Student]
      [Fintype Actor] [DecidableEq Actor]
      (PBO : Base → (Feature → ℝ) → ℝ)
      (M : Base → GaussianOffsetSignalFamily Feature)
      (theta : Base → Feature → ℝ) (k : Feature)
      (skillGivenBase : Base → PMF Skill)
      (demographicAccessEstimate demographicNoAccessEstimate :
        Equilibrium → PMF ℝ)
      (studentLaw : Equilibrium → Base → PMF Student)
      (studentScore : Equilibrium → Base → Student → ℝ)
      (pboThreshold : Equilibrium → Base → ℝ)
      (reporterPMF : Equilibrium → Base → PMF ℝ)
      (testOf : Equilibrium → Base → ℝ)
      (takeDecision : Equilibrium → Skill → Base → Bool)
      (estimationConsistent : Equilibrium → Prop)
      (referenceSkill : Equilibrium → Base → Skill)
      (actorLaw : Equilibrium → Base → PMF Actor)
      (actorValue : Equilibrium → Base → Actor → ℝ)
      (actorOfTest : Equilibrium → Base → ℝ → Actor)
      (baseTerm signalWeight denom : Equilibrium → Base → ℝ)
      hPBO hEq
      (hactorCutoff :
        ∀ e base actor, 0 < (actorLaw e base actor).toReal →
          lg21GaussianPosteriorMeanPBOCutoff M theta k pboThreshold e base ≤
            actorValue e base actor)
      hweight hdenom hfullPoint hmass =>
    paper_theorem3_2_section3_optional_reporting_skill_mixture_raw_mixture_canonical_base_point_estimate_fairness_iff_no_test_relevance_of_gaussian_pbo_base_source_model_literal_decision_event_latent_kernels_actor_support_affine_noReportPayoff_self_law_classical_decidable
      PBO M theta k skillGivenBase demographicAccessEstimate
      demographicNoAccessEstimate studentLaw studentScore pboThreshold
      reporterPMF testOf takeDecision estimationConsistent referenceSkill
      actorLaw actorValue actorOfTest baseTerm signalWeight denom hPBO hEq
      (lg21_gaussian_pbo_literal_decision_actor_support_of_cutoff_support
        PBO M theta k pboThreshold hPBO actorLaw actorValue hactorCutoff)
      hweight hdenom hfullPoint hmass

/--
Value-level optional-reporting canonical binary-choice endpoint with lower
cutoff support in place of Boolean actor support.
-/
noncomputable abbrev paper_theorem3_2_section3_optional_reporting_skill_mixture_raw_mixture_canonical_base_point_estimate_fairness_iff_value_no_test_relevance_of_gaussian_pbo_binary_choice_literal_decision_event_latent_kernels_threshold_support_affine_noReportPayoff_self_law_classical_decidable :=
  fun {Feature Skill Base Student Equilibrium Actor : Type*}
      [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
      [Fintype Student] [DecidableEq Student]
      [Fintype Actor] [DecidableEq Actor]
      (PBO : Base → (Feature → ℝ) → ℝ)
      (M : Base → GaussianOffsetSignalFamily Feature)
      (theta : Base → Feature → ℝ) (k : Feature)
      (skillGivenBase : Base → PMF Skill)
      (demographicAccessEstimate demographicNoAccessEstimate :
        Equilibrium → PMF ℝ)
      (studentLaw : Equilibrium → Base → PMF Student)
      (studentScore : Equilibrium → Base → Student → ℝ)
      (pboThreshold : Equilibrium → Base → ℝ)
      (reporterPMF : Equilibrium → Base → PMF ℝ)
      (testOf : Equilibrium → Base → ℝ)
      (estimationConsistent : Equilibrium → Prop)
      (referenceSkill : Equilibrium → Base → Skill)
      (actorLaw : Equilibrium → Base → PMF Actor)
      (actorValue : Equilibrium → Base → Actor → ℝ)
      (actorOfTest : Equilibrium → Base → ℝ → Actor)
      (baseTerm signalWeight denom : Equilibrium → Base → ℝ)
      (hPBO : ∀ base obs, PBO base obs = (M base).posteriorMean obs)
      (hbest :
        ∀ e base,
          lg21NoProfitableBinaryChoiceDeviation
            (fun score : ℝ =>
              (if pboThreshold e base ≤
                    PBO base (Function.update (theta base) k score) then
                  true
                else
                  false) = true)
            (fun score : ℝ =>
              (baseTerm e base + signalWeight e base * score) /
                denom e base)
            (fun _score : ℝ =>
              (baseTerm e base +
                  signalWeight e base *
                    pmfExp (actorLaw e base) (actorValue e base)) /
                denom e base))
      (hconsistent : ∀ e, estimationConsistent e)
      (hactorCutoff :
        ∀ e base actor, 0 < (actorLaw e base actor).toReal →
          lg21GaussianPosteriorMeanPBOCutoff M theta k pboThreshold e base ≤
            actorValue e base actor)
      hweight hdenom hfullPoint hmass =>
    paper_theorem3_2_section3_optional_reporting_skill_mixture_raw_mixture_canonical_base_point_estimate_fairness_iff_value_no_test_relevance_of_gaussian_pbo_binary_choice_literal_decision_event_latent_kernels_actor_support_affine_noReportPayoff_self_law_classical_decidable
      PBO M theta k skillGivenBase demographicAccessEstimate
      demographicNoAccessEstimate studentLaw studentScore pboThreshold
      reporterPMF testOf estimationConsistent referenceSkill actorLaw
      actorValue actorOfTest baseTerm signalWeight denom hPBO hbest
      hconsistent
      (lg21_gaussian_pbo_literal_decision_actor_support_of_cutoff_support
        PBO M theta k pboThreshold hPBO actorLaw actorValue hactorCutoff)
      hweight hdenom hfullPoint hmass

/--
Value-level optional-reporting canonical payoff-threshold endpoint with lower
cutoff support in place of Boolean actor support.
-/
noncomputable abbrev paper_theorem3_2_section3_optional_reporting_skill_mixture_raw_mixture_canonical_base_point_estimate_fairness_iff_value_no_test_relevance_of_gaussian_pbo_payoff_threshold_literal_decision_event_latent_kernels_threshold_support_affine_noReportPayoff_self_law_classical_decidable :=
  fun {Feature Skill Base Student Equilibrium Actor : Type*}
      [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
      [Fintype Student] [DecidableEq Student]
      [Fintype Actor] [DecidableEq Actor]
      (PBO : Base → (Feature → ℝ) → ℝ)
      (M : Base → GaussianOffsetSignalFamily Feature)
      (theta : Base → Feature → ℝ) (k : Feature)
      (skillGivenBase : Base → PMF Skill)
      (demographicAccessEstimate demographicNoAccessEstimate :
        Equilibrium → PMF ℝ)
      (studentLaw : Equilibrium → Base → PMF Student)
      (studentScore : Equilibrium → Base → Student → ℝ)
      (pboThreshold : Equilibrium → Base → ℝ)
      (reporterPMF : Equilibrium → Base → PMF ℝ)
      (testOf : Equilibrium → Base → ℝ)
      (estimationConsistent : Equilibrium → Prop)
      (referenceSkill : Equilibrium → Base → Skill)
      (actorLaw : Equilibrium → Base → PMF Actor)
      (actorValue : Equilibrium → Base → Actor → ℝ)
      (actorOfTest : Equilibrium → Base → ℝ → Actor)
      (baseTerm signalWeight denom : Equilibrium → Base → ℝ)
      (hPBO : ∀ base obs, PBO base obs = (M base).posteriorMean obs)
      (hchoice :
        ∀ e base score,
          ((if pboThreshold e base ≤
                PBO base (Function.update (theta base) k score) then
              true
            else
              false) =
              true) ↔
            (baseTerm e base +
                signalWeight e base *
                  pmfExp (actorLaw e base) (actorValue e base)) /
              denom e base ≤
                (baseTerm e base + signalWeight e base * score) /
                  denom e base)
      (hconsistent : ∀ e, estimationConsistent e)
      (hactorCutoff :
        ∀ e base actor, 0 < (actorLaw e base actor).toReal →
          lg21GaussianPosteriorMeanPBOCutoff M theta k pboThreshold e base ≤
            actorValue e base actor)
      hweight hdenom hfullPoint hmass =>
    paper_theorem3_2_section3_optional_reporting_skill_mixture_raw_mixture_canonical_base_point_estimate_fairness_iff_value_no_test_relevance_of_gaussian_pbo_payoff_threshold_literal_decision_event_latent_kernels_actor_support_affine_noReportPayoff_self_law_classical_decidable
      PBO M theta k skillGivenBase demographicAccessEstimate
      demographicNoAccessEstimate studentLaw studentScore pboThreshold
      reporterPMF testOf estimationConsistent referenceSkill actorLaw
      actorValue actorOfTest baseTerm signalWeight denom hPBO hchoice
      hconsistent
      (lg21_gaussian_pbo_literal_decision_actor_support_of_cutoff_support
        PBO M theta k pboThreshold hPBO actorLaw actorValue hactorCutoff)
      hweight hdenom hfullPoint hmass

/--
Value-level optional-reporting canonical indifference-cutoff endpoint with
lower cutoff support in place of Boolean actor support.
-/
noncomputable abbrev paper_theorem3_2_section3_optional_reporting_skill_mixture_raw_mixture_canonical_base_point_estimate_fairness_iff_value_no_test_relevance_of_gaussian_pbo_indifference_cutoff_literal_decision_event_latent_kernels_threshold_support_affine_noReportPayoff_self_law_classical_decidable :=
  fun {Feature Skill Base Student Equilibrium Actor : Type*}
      [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
      [Fintype Student] [DecidableEq Student]
      [Fintype Actor] [DecidableEq Actor]
      (PBO : Base → (Feature → ℝ) → ℝ)
      (M : Base → GaussianOffsetSignalFamily Feature)
      (theta : Base → Feature → ℝ) (k : Feature)
      (skillGivenBase : Base → PMF Skill)
      (demographicAccessEstimate demographicNoAccessEstimate :
        Equilibrium → PMF ℝ)
      (studentLaw : Equilibrium → Base → PMF Student)
      (studentScore : Equilibrium → Base → Student → ℝ)
      (pboThreshold : Equilibrium → Base → ℝ)
      (reporterPMF : Equilibrium → Base → PMF ℝ)
      (testOf : Equilibrium → Base → ℝ)
      (estimationConsistent : Equilibrium → Prop)
      (referenceSkill : Equilibrium → Base → Skill)
      (actorLaw : Equilibrium → Base → PMF Actor)
      (actorValue : Equilibrium → Base → Actor → ℝ)
      (actorOfTest : Equilibrium → Base → ℝ → Actor)
      (baseTerm signalWeight denom : Equilibrium → Base → ℝ)
      (hPBO : ∀ base obs, PBO base obs = (M base).posteriorMean obs)
      (hcutoff_eq_mean :
        ∀ e base,
          affineCutoff
              ((M base).posteriorMean (Function.update (theta base) k 0))
              ((M base).centeredFamily.signalWeight k)
              (pboThreshold e base) =
            pmfExp (actorLaw e base) (actorValue e base))
      (hconsistent : ∀ e, estimationConsistent e)
      (hactorCutoff :
        ∀ e base actor, 0 < (actorLaw e base actor).toReal →
          lg21GaussianPosteriorMeanPBOCutoff M theta k pboThreshold e base ≤
            actorValue e base actor)
      hweight hdenom hfullPoint hmass =>
    paper_theorem3_2_section3_optional_reporting_skill_mixture_raw_mixture_canonical_base_point_estimate_fairness_iff_value_no_test_relevance_of_gaussian_pbo_indifference_cutoff_literal_decision_event_latent_kernels_actor_support_affine_noReportPayoff_self_law_classical_decidable
      PBO M theta k skillGivenBase demographicAccessEstimate
      demographicNoAccessEstimate studentLaw studentScore pboThreshold
      reporterPMF testOf estimationConsistent referenceSkill actorLaw
      actorValue actorOfTest baseTerm signalWeight denom hPBO hcutoff_eq_mean
      hconsistent
      (lg21_gaussian_pbo_literal_decision_actor_support_of_cutoff_support
        PBO M theta k pboThreshold hPBO actorLaw actorValue hactorCutoff)
      hweight hdenom hfullPoint hmass

/--
Canonical-base-point optional-reporting Gaussian `P_BO` endpoint with lower
cutoff support and full actor-law support, replacing the pointwise
`actorOfTest` mass premise.
-/
noncomputable abbrev paper_theorem3_2_section3_optional_reporting_skill_mixture_raw_mixture_canonical_base_point_estimate_fairness_iff_no_test_relevance_of_gaussian_pbo_base_source_model_literal_decision_event_latent_kernels_threshold_support_full_actor_support_affine_noReportPayoff_self_law_classical_decidable :=
  fun {Feature Skill Base Student Equilibrium Actor : Type*}
      [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
      [Fintype Student] [DecidableEq Student]
      [Fintype Actor] [DecidableEq Actor]
      (PBO : Base → (Feature → ℝ) → ℝ)
      (M : Base → GaussianOffsetSignalFamily Feature)
      (theta : Base → Feature → ℝ) (k : Feature)
      (skillGivenBase : Base → PMF Skill)
      (demographicAccessEstimate demographicNoAccessEstimate :
        Equilibrium → PMF ℝ)
      (studentLaw : Equilibrium → Base → PMF Student)
      (studentScore : Equilibrium → Base → Student → ℝ)
      (pboThreshold : Equilibrium → Base → ℝ)
      (reporterPMF : Equilibrium → Base → PMF ℝ)
      (testOf : Equilibrium → Base → ℝ)
      (takeDecision : Equilibrium → Skill → Base → Bool)
      (estimationConsistent : Equilibrium → Prop)
      (referenceSkill : Equilibrium → Base → Skill)
      (actorLaw : Equilibrium → Base → PMF Actor)
      (actorValue : Equilibrium → Base → Actor → ℝ)
      (actorOfTest : Equilibrium → Base → ℝ → Actor)
      (baseTerm signalWeight denom : Equilibrium → Base → ℝ)
      hPBO hEq hactorCutoff hweight hdenom hfullPoint hfullActorSupport =>
    paper_theorem3_2_section3_optional_reporting_skill_mixture_raw_mixture_canonical_base_point_estimate_fairness_iff_no_test_relevance_of_gaussian_pbo_base_source_model_literal_decision_event_latent_kernels_threshold_support_affine_noReportPayoff_self_law_classical_decidable
      PBO M theta k skillGivenBase demographicAccessEstimate
      demographicNoAccessEstimate studentLaw studentScore pboThreshold
      reporterPMF testOf takeDecision estimationConsistent referenceSkill
      actorLaw actorValue actorOfTest baseTerm signalWeight denom hPBO hEq
      hactorCutoff hweight hdenom hfullPoint
      (lg21_actor_of_test_mass_of_full_actor_support actorLaw actorOfTest
        hfullActorSupport)

/--
Value-level optional-reporting canonical binary-choice endpoint with lower
cutoff support and full actor-law support.
-/
noncomputable abbrev paper_theorem3_2_section3_optional_reporting_skill_mixture_raw_mixture_canonical_base_point_estimate_fairness_iff_value_no_test_relevance_of_gaussian_pbo_binary_choice_literal_decision_event_latent_kernels_threshold_support_full_actor_support_affine_noReportPayoff_self_law_classical_decidable :=
  fun {Feature Skill Base Student Equilibrium Actor : Type*}
      [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
      [Fintype Student] [DecidableEq Student]
      [Fintype Actor] [DecidableEq Actor]
      (PBO : Base → (Feature → ℝ) → ℝ)
      (M : Base → GaussianOffsetSignalFamily Feature)
      (theta : Base → Feature → ℝ) (k : Feature)
      (skillGivenBase : Base → PMF Skill)
      (demographicAccessEstimate demographicNoAccessEstimate :
        Equilibrium → PMF ℝ)
      (studentLaw : Equilibrium → Base → PMF Student)
      (studentScore : Equilibrium → Base → Student → ℝ)
      (pboThreshold : Equilibrium → Base → ℝ)
      (reporterPMF : Equilibrium → Base → PMF ℝ)
      (testOf : Equilibrium → Base → ℝ)
      (estimationConsistent : Equilibrium → Prop)
      (referenceSkill : Equilibrium → Base → Skill)
      (actorLaw : Equilibrium → Base → PMF Actor)
      (actorValue : Equilibrium → Base → Actor → ℝ)
      (actorOfTest : Equilibrium → Base → ℝ → Actor)
      (baseTerm signalWeight denom : Equilibrium → Base → ℝ)
      hPBO hbest hconsistent hactorCutoff hweight hdenom hfullPoint
      hfullActorSupport =>
    paper_theorem3_2_section3_optional_reporting_skill_mixture_raw_mixture_canonical_base_point_estimate_fairness_iff_value_no_test_relevance_of_gaussian_pbo_binary_choice_literal_decision_event_latent_kernels_threshold_support_affine_noReportPayoff_self_law_classical_decidable
      PBO M theta k skillGivenBase demographicAccessEstimate
      demographicNoAccessEstimate studentLaw studentScore pboThreshold
      reporterPMF testOf estimationConsistent referenceSkill actorLaw
      actorValue actorOfTest baseTerm signalWeight denom hPBO hbest
      hconsistent hactorCutoff hweight hdenom hfullPoint
      (lg21_actor_of_test_mass_of_full_actor_support actorLaw actorOfTest
        hfullActorSupport)

/--
Value-level optional-reporting canonical payoff-threshold endpoint with lower
cutoff support and full actor-law support.
-/
noncomputable abbrev paper_theorem3_2_section3_optional_reporting_skill_mixture_raw_mixture_canonical_base_point_estimate_fairness_iff_value_no_test_relevance_of_gaussian_pbo_payoff_threshold_literal_decision_event_latent_kernels_threshold_support_full_actor_support_affine_noReportPayoff_self_law_classical_decidable :=
  fun {Feature Skill Base Student Equilibrium Actor : Type*}
      [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
      [Fintype Student] [DecidableEq Student]
      [Fintype Actor] [DecidableEq Actor]
      (PBO : Base → (Feature → ℝ) → ℝ)
      (M : Base → GaussianOffsetSignalFamily Feature)
      (theta : Base → Feature → ℝ) (k : Feature)
      (skillGivenBase : Base → PMF Skill)
      (demographicAccessEstimate demographicNoAccessEstimate :
        Equilibrium → PMF ℝ)
      (studentLaw : Equilibrium → Base → PMF Student)
      (studentScore : Equilibrium → Base → Student → ℝ)
      (pboThreshold : Equilibrium → Base → ℝ)
      (reporterPMF : Equilibrium → Base → PMF ℝ)
      (testOf : Equilibrium → Base → ℝ)
      (estimationConsistent : Equilibrium → Prop)
      (referenceSkill : Equilibrium → Base → Skill)
      (actorLaw : Equilibrium → Base → PMF Actor)
      (actorValue : Equilibrium → Base → Actor → ℝ)
      (actorOfTest : Equilibrium → Base → ℝ → Actor)
      (baseTerm signalWeight denom : Equilibrium → Base → ℝ)
      hPBO hchoice hconsistent hactorCutoff hweight hdenom hfullPoint
      hfullActorSupport =>
    paper_theorem3_2_section3_optional_reporting_skill_mixture_raw_mixture_canonical_base_point_estimate_fairness_iff_value_no_test_relevance_of_gaussian_pbo_payoff_threshold_literal_decision_event_latent_kernels_threshold_support_affine_noReportPayoff_self_law_classical_decidable
      PBO M theta k skillGivenBase demographicAccessEstimate
      demographicNoAccessEstimate studentLaw studentScore pboThreshold
      reporterPMF testOf estimationConsistent referenceSkill actorLaw
      actorValue actorOfTest baseTerm signalWeight denom hPBO hchoice
      hconsistent hactorCutoff hweight hdenom hfullPoint
      (lg21_actor_of_test_mass_of_full_actor_support actorLaw actorOfTest
        hfullActorSupport)

/--
Value-level optional-reporting canonical indifference-cutoff endpoint with
lower cutoff support and full actor-law support.
-/
noncomputable abbrev paper_theorem3_2_section3_optional_reporting_skill_mixture_raw_mixture_canonical_base_point_estimate_fairness_iff_value_no_test_relevance_of_gaussian_pbo_indifference_cutoff_literal_decision_event_latent_kernels_threshold_support_full_actor_support_affine_noReportPayoff_self_law_classical_decidable :=
  fun {Feature Skill Base Student Equilibrium Actor : Type*}
      [Fintype Feature] [DecidableEq Feature] [Nonempty Feature]
      [Fintype Student] [DecidableEq Student]
      [Fintype Actor] [DecidableEq Actor]
      (PBO : Base → (Feature → ℝ) → ℝ)
      (M : Base → GaussianOffsetSignalFamily Feature)
      (theta : Base → Feature → ℝ) (k : Feature)
      (skillGivenBase : Base → PMF Skill)
      (demographicAccessEstimate demographicNoAccessEstimate :
        Equilibrium → PMF ℝ)
      (studentLaw : Equilibrium → Base → PMF Student)
      (studentScore : Equilibrium → Base → Student → ℝ)
      (pboThreshold : Equilibrium → Base → ℝ)
      (reporterPMF : Equilibrium → Base → PMF ℝ)
      (testOf : Equilibrium → Base → ℝ)
      (estimationConsistent : Equilibrium → Prop)
      (referenceSkill : Equilibrium → Base → Skill)
      (actorLaw : Equilibrium → Base → PMF Actor)
      (actorValue : Equilibrium → Base → Actor → ℝ)
      (actorOfTest : Equilibrium → Base → ℝ → Actor)
      (baseTerm signalWeight denom : Equilibrium → Base → ℝ)
      hPBO hcutoff_eq_mean hconsistent hactorCutoff hweight hdenom
      hfullPoint hfullActorSupport =>
    paper_theorem3_2_section3_optional_reporting_skill_mixture_raw_mixture_canonical_base_point_estimate_fairness_iff_value_no_test_relevance_of_gaussian_pbo_indifference_cutoff_literal_decision_event_latent_kernels_threshold_support_affine_noReportPayoff_self_law_classical_decidable
      PBO M theta k skillGivenBase demographicAccessEstimate
      demographicNoAccessEstimate studentLaw studentScore pboThreshold
      reporterPMF testOf estimationConsistent referenceSkill actorLaw
      actorValue actorOfTest baseTerm signalWeight denom hPBO hcutoff_eq_mean
      hconsistent hactorCutoff hweight hdenom hfullPoint
      (lg21_actor_of_test_mass_of_full_actor_support actorLaw actorOfTest
        hfullActorSupport)

/--
Finite-test threshold support implies literal `P_BO` actor support for the
pushforward acting law.
-/
theorem lg21_affine_pbo_literal_decision_actor_support_of_finite_test_threshold_support
    {Base Test Actor Equilibrium : Type*}
    (PBO : Equilibrium → Base → ℝ → ℝ)
    (testLaw : Equilibrium → Base → PMF Test)
    (actorValue : Equilibrium → Base → Actor → ℝ)
    (actorOfTest : Equilibrium → Base → Test → Actor)
    (pboThreshold : Equilibrium → Base → ℝ)
    (hsupport_abovePBO :
      ∀ e base test, 0 < (testLaw e base test).toReal →
        pboThreshold e base ≤
          PBO e base (actorValue e base (actorOfTest e base test))) :
    ∀ e base actor,
      0 < (((testLaw e base).map (actorOfTest e base)) actor).toReal →
        (if pboThreshold e base ≤ PBO e base (actorValue e base actor) then
          true
        else
          false) =
          true := by
  intro e base actor hactorMass
  rcases lg21_pmf_map_pos_exists_preimage
      (testLaw e base) (actorOfTest e base) actor hactorMass with
    ⟨test, htest_eq, htestMass⟩
  have hpbo :
      pboThreshold e base ≤ PBO e base (actorValue e base actor) := by
    simpa [htest_eq] using hsupport_abovePBO e base test htestMass
  simp [hpbo]

/--
Finite-test full-support report-required canonical-base-point affine `P_BO`
endpoint with the source-equilibrium premise retained and support stated
directly as finite-test threshold support.
-/
noncomputable abbrev paper_theorem3_2_section3_report_required_skill_mixture_raw_mixture_canonical_base_point_estimate_fairness_iff_no_test_relevance_of_affine_pbo_base_source_model_literal_decision_event_latent_kernels_finite_test_threshold_support_full_test_support_centered_baseTerm_self_law_classical_decidable :=
  fun {Base Test Student Equilibrium Actor : Type*}
      [Fintype Student] [DecidableEq Student]
      [Fintype Test] [DecidableEq Test]
      [Fintype Actor] [DecidableEq Actor]
      (PBO : Equilibrium → Base → ℝ → ℝ)
      (skillGivenBase : Base → PMF ℝ)
      (demographicAccessEstimate demographicNoAccessEstimate :
        Equilibrium → PMF ℝ)
      (studentLaw : Equilibrium → Base → PMF Student)
      (studentSkill : Equilibrium → Base → Student → ℝ)
      (pboThreshold : Equilibrium → Base → ℝ)
      (reporterPMF : Equilibrium → Base → PMF ℝ)
      (testOf : Equilibrium → Base → Test)
      (reportDecision : Equilibrium → Base → Test → Bool)
      (estimationConsistent : Equilibrium → Prop)
      (referenceTest : Equilibrium → Base → Test)
      (testLaw : Equilibrium → Base → PMF Test)
      (actorValue : Equilibrium → Base → Actor → ℝ)
      (actorOfTest : Equilibrium → Base → Test → Actor)
      (signalWeight denom : Equilibrium → Base → ℝ)
      (intercept slope : Equilibrium → Base → ℝ)
      hslope hPBO hEq
      (hsupport_abovePBO :
        ∀ e base test, 0 < (testLaw e base test).toReal →
          pboThreshold e base ≤
            PBO e base (actorValue e base (actorOfTest e base test)))
      (hfull_support : ∀ e base test, 0 < (testLaw e base test).toReal)
      hweight hdenom hfullPoint =>
    paper_theorem3_2_section3_report_required_skill_mixture_raw_mixture_canonical_base_point_estimate_fairness_iff_no_test_relevance_of_affine_pbo_base_source_model_literal_decision_event_latent_kernels_finite_test_actor_support_full_test_support_centered_baseTerm_self_law_classical_decidable
      PBO skillGivenBase demographicAccessEstimate demographicNoAccessEstimate
      studentLaw studentSkill pboThreshold reporterPMF testOf reportDecision
      estimationConsistent referenceTest testLaw actorValue actorOfTest
      signalWeight denom intercept slope hslope hPBO hEq
      (lg21_affine_pbo_literal_decision_actor_support_of_finite_test_threshold_support
        PBO testLaw actorValue actorOfTest pboThreshold hsupport_abovePBO)
      hfull_support hweight hdenom hfullPoint

/--
Finite-test full-support value-level report-required affine `P_BO` endpoint
with direct binary best response and direct finite-test threshold support.
-/
noncomputable abbrev paper_theorem3_2_section3_report_required_skill_mixture_raw_mixture_canonical_base_point_estimate_fairness_iff_value_no_test_relevance_of_affine_pbo_binary_choice_literal_decision_event_latent_kernels_finite_test_threshold_support_full_test_support_centered_baseTerm_self_law_classical_decidable :=
  fun {Base Test Student Equilibrium Actor : Type*}
      [Fintype Student] [DecidableEq Student]
      [Fintype Test] [DecidableEq Test]
      [Fintype Actor] [DecidableEq Actor]
      (PBO : Equilibrium → Base → ℝ → ℝ)
      (skillGivenBase : Base → PMF ℝ)
      (demographicAccessEstimate demographicNoAccessEstimate :
        Equilibrium → PMF ℝ)
      (studentLaw : Equilibrium → Base → PMF Student)
      (studentSkill : Equilibrium → Base → Student → ℝ)
      (pboThreshold : Equilibrium → Base → ℝ)
      (reporterPMF : Equilibrium → Base → PMF ℝ)
      (testOf : Equilibrium → Base → Test)
      (testLaw : Equilibrium → Base → PMF Test)
      (actorValue : Equilibrium → Base → Actor → ℝ)
      (actorOfTest : Equilibrium → Base → Test → Actor)
      (signalWeight denom : Equilibrium → Base → ℝ)
      (intercept slope : Equilibrium → Base → ℝ)
      hslope hPBO hbest
      (hsupport_abovePBO :
        ∀ e base test, 0 < (testLaw e base test).toReal →
          pboThreshold e base ≤
            PBO e base (actorValue e base (actorOfTest e base test)))
      (hfull_support : ∀ e base test, 0 < (testLaw e base test).toReal)
      hweight hdenom hfullPoint =>
    paper_theorem3_2_section3_report_required_skill_mixture_raw_mixture_canonical_base_point_estimate_fairness_iff_value_no_test_relevance_of_affine_pbo_binary_choice_literal_decision_event_latent_kernels_finite_test_actor_support_full_test_support_centered_baseTerm_self_law_classical_decidable
      PBO skillGivenBase demographicAccessEstimate demographicNoAccessEstimate
      studentLaw studentSkill pboThreshold reporterPMF testOf testLaw
      actorValue actorOfTest signalWeight denom intercept slope hslope hPBO
      hbest
      (lg21_affine_pbo_literal_decision_actor_support_of_finite_test_threshold_support
        PBO testLaw actorValue actorOfTest pboThreshold hsupport_abovePBO)
      hfull_support hweight hdenom hfullPoint

/--
Finite-test full-support value-level report-required affine `P_BO` endpoint
from an exact payoff-threshold taking rule and direct finite-test threshold
support.
-/
noncomputable abbrev paper_theorem3_2_section3_report_required_skill_mixture_raw_mixture_canonical_base_point_estimate_fairness_iff_value_no_test_relevance_of_affine_pbo_payoff_threshold_literal_decision_event_latent_kernels_finite_test_threshold_support_full_test_support_centered_baseTerm_self_law_classical_decidable :=
  fun {Base Test Student Equilibrium Actor : Type*}
      [Fintype Student] [DecidableEq Student]
      [Fintype Test] [DecidableEq Test]
      [Fintype Actor] [DecidableEq Actor]
      (PBO : Equilibrium → Base → ℝ → ℝ)
      (skillGivenBase : Base → PMF ℝ)
      (demographicAccessEstimate demographicNoAccessEstimate :
        Equilibrium → PMF ℝ)
      (studentLaw : Equilibrium → Base → PMF Student)
      (studentSkill : Equilibrium → Base → Student → ℝ)
      (pboThreshold : Equilibrium → Base → ℝ)
      (reporterPMF : Equilibrium → Base → PMF ℝ)
      (testOf : Equilibrium → Base → Test)
      (testLaw : Equilibrium → Base → PMF Test)
      (actorValue : Equilibrium → Base → Actor → ℝ)
      (actorOfTest : Equilibrium → Base → Test → Actor)
      (signalWeight denom : Equilibrium → Base → ℝ)
      (intercept slope : Equilibrium → Base → ℝ)
      hslope hPBO
      (hchoice :
        ∀ e base skill,
          ((if pboThreshold e base ≤ PBO e base skill then true else false) =
              true) ↔
            (1 / 2 : ℝ) ≤
              ((denom e base / 2 -
                    signalWeight e base *
                      pmfExp ((testLaw e base).map (actorOfTest e base))
                        (actorValue e base)) +
                  signalWeight e base * skill) /
                denom e base)
      (hsupport_abovePBO :
        ∀ e base test, 0 < (testLaw e base test).toReal →
          pboThreshold e base ≤
            PBO e base (actorValue e base (actorOfTest e base test)))
      (hfull_support : ∀ e base test, 0 < (testLaw e base test).toReal)
      hweight hdenom hfullPoint =>
    paper_theorem3_2_section3_report_required_skill_mixture_raw_mixture_canonical_base_point_estimate_fairness_iff_value_no_test_relevance_of_affine_pbo_payoff_threshold_literal_decision_event_latent_kernels_finite_test_actor_support_full_test_support_centered_baseTerm_self_law_classical_decidable
      PBO skillGivenBase demographicAccessEstimate demographicNoAccessEstimate
      studentLaw studentSkill pboThreshold reporterPMF testOf testLaw
      actorValue actorOfTest signalWeight denom intercept slope hslope hPBO
      hchoice
      (lg21_affine_pbo_literal_decision_actor_support_of_finite_test_threshold_support
        PBO testLaw actorValue actorOfTest pboThreshold hsupport_abovePBO)
      hfull_support hweight hdenom hfullPoint

/--
Finite-test full-support value-level report-required affine `P_BO` endpoint
from an indifference cutoff and direct finite-test threshold support.
-/
noncomputable abbrev paper_theorem3_2_section3_report_required_skill_mixture_raw_mixture_canonical_base_point_estimate_fairness_iff_value_no_test_relevance_of_affine_pbo_indifference_cutoff_literal_decision_event_latent_kernels_finite_test_threshold_support_full_test_support_centered_baseTerm_self_law_classical_decidable :=
  fun {Base Test Student Equilibrium Actor : Type*}
      [Fintype Student] [DecidableEq Student]
      [Fintype Test] [DecidableEq Test]
      [Fintype Actor] [DecidableEq Actor]
      (PBO : Equilibrium → Base → ℝ → ℝ)
      (skillGivenBase : Base → PMF ℝ)
      (demographicAccessEstimate demographicNoAccessEstimate :
        Equilibrium → PMF ℝ)
      (studentLaw : Equilibrium → Base → PMF Student)
      (studentSkill : Equilibrium → Base → Student → ℝ)
      (pboThreshold : Equilibrium → Base → ℝ)
      (reporterPMF : Equilibrium → Base → PMF ℝ)
      (testOf : Equilibrium → Base → Test)
      (testLaw : Equilibrium → Base → PMF Test)
      (actorValue : Equilibrium → Base → Actor → ℝ)
      (actorOfTest : Equilibrium → Base → Test → Actor)
      (signalWeight denom : Equilibrium → Base → ℝ)
      (intercept slope : Equilibrium → Base → ℝ)
      hslope hPBO
      (hcutoff_eq_mean :
        ∀ e base,
          affineCutoff (intercept e base) (slope e base) (pboThreshold e base) =
            pmfExp ((testLaw e base).map (actorOfTest e base))
              (actorValue e base))
      (hsupport_abovePBO :
        ∀ e base test, 0 < (testLaw e base test).toReal →
          pboThreshold e base ≤
            PBO e base (actorValue e base (actorOfTest e base test)))
      (hfull_support : ∀ e base test, 0 < (testLaw e base test).toReal)
      hweight hdenom hfullPoint =>
    paper_theorem3_2_section3_report_required_skill_mixture_raw_mixture_canonical_base_point_estimate_fairness_iff_value_no_test_relevance_of_affine_pbo_indifference_cutoff_literal_decision_event_latent_kernels_finite_test_actor_support_full_test_support_centered_baseTerm_self_law_classical_decidable
      PBO skillGivenBase demographicAccessEstimate demographicNoAccessEstimate
      studentLaw studentSkill pboThreshold reporterPMF testOf testLaw
      actorValue actorOfTest signalWeight denom intercept slope hslope hPBO
      hcutoff_eq_mean
      (lg21_affine_pbo_literal_decision_actor_support_of_finite_test_threshold_support
        PBO testLaw actorValue actorOfTest pboThreshold hsupport_abovePBO)
      hfull_support hweight hdenom hfullPoint

end

end LG21TestOptionalPolicies

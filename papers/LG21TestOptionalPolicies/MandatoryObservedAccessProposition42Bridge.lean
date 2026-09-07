import LG21TestOptionalPolicies.Proposition42CanonicalPolicySourceLaw
import LG21TestOptionalPolicies.ObservedAccessAllProtocolD6OutputBridge
import LG21TestOptionalPolicies.MandatoryObservedAccessProposition43Nonvacuity
import LG21TestOptionalPolicies.ObservedAccessVoluntaryActiveBranchModels

/-!
# Mandatory observed-access Proposition 4.2 bridge for LG21

This module is the mandatory-given-access counterpart of the two voluntary
Proposition 4.2 source bridges.  It uses the literal continuous Gaussian
population rather than the reduced posterior-summary diagnostic model.

The source condition for Proposition 4.2 concerns only the access branch:
the reported-score estimate is a Bayesian posterior mean.  The no-access
policy is therefore an arbitrary base-indexed Markov kernel.  The bridge keeps
the actual source PBO realization almost everywhere separate from the total
fixed-fibre Gaussian representative used by Definition 2.  In particular, it
does not accept an access/output law equality as an input.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib AppliedModelingLib.Probability MeasureTheory ProbabilityTheory

/-- A mandatory-given-access source policy for Proposition 4.2.  The only
PBO premise concerns the observed reported-score branch; Proposition 4.2 does
not restrict the no-access policy. -/
structure LG21P42MandatoryGivenAccessPBOProfile
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature) where
  mandatory : LG21MandatoryGivenAccessLiteralSourceEquilibrium source.population
  reportedPayoff :
    (LG21NonTestFeature Feature source.test_feature -> ℝ) -> ℝ -> ℝ
  reportedPBO : LG21ObservedAccessAllReportPBO
    (lg21ContinuousGaussianAccessPopulationLaw source.population)
    (lg21ContinuousPopulationBase source.test_feature)
    (lg21ContinuousPopulationFeature source.test_feature)
    (lg21ContinuousPopulationSkill (Feature := Feature)) reportedPayoff

/-- The total fixed-fibre policy-law representative for a mandatory source
profile.  Its access conditional laws are the actual Gaussian score experiment
and its no-access law is the caller's arbitrary base-only policy. -/
def lg21P42MandatoryGivenAccessPolicyLawSurface
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (S : LG21GaussianPBOResamplingSource
      (LG21NonTestFeature Feature source.test_feature -> ℝ))
    (noAccessEstimateKernel : Kernel
      (LG21NonTestFeature Feature source.test_feature -> ℝ) ℝ)
    [IsMarkovKernel noAccessEstimateKernel] :
    LG21SourceLawPolicySurface ℝ
      (LG21NonTestFeature Feature source.test_feature -> ℝ) ℝ (Measure ℝ) :=
  lg21P42CanonicalPBOPolicySourceLawSurfaceAt
    (LG21P42MandatoryGivenAccessPBOProfile source) S noAccessEstimateKernel

/-- The literal mandatory source profile realizes the canonical observed-score
PBO on the actual access population.  The action and PBO facts remain visible:
there is no value or comparison for an unattained access/no-report branch. -/
structure LG21P42MandatoryGivenAccessSourcePBO
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (profile : LG21P42MandatoryGivenAccessPBOProfile source)
    (S : LG21GaussianPBOResamplingSource
      (LG21NonTestFeature Feature source.test_feature -> ℝ))
    (noAccessEstimateKernel : Kernel
      (LG21NonTestFeature Feature source.test_feature -> ℝ) ℝ)
    [IsMarkovKernel noAccessEstimateKernel] : Prop where
  all_take_and_report_ae :
    ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw source.population,
      profile.mandatory.action student = LG21AccessAction.takeAndReport
  reported_output_eq_canonical_ae :
    (fun student =>
      profile.reportedPayoff
        (lg21ContinuousPopulationBase source.test_feature student)
        (lg21ContinuousPopulationFeature source.test_feature student)) =ᵐ[
          lg21ContinuousGaussianAccessPopulationLaw source.population]
      fun student =>
        lg21P42GaussianPBOEstimate
          (lg21P42ObservedScoreModelOfD6Source S noAccessEstimateKernel)
          (lg21ContinuousPopulationBase source.test_feature student)
          (lg21ContinuousPopulationFeature source.test_feature student)

/-- A source-faithful Proposition 4.2 witness for mandatory-given-access
testing.  The full-base Gaussian factorization is derived from the actual
source population; the final negation is the paper's fixed-fibre Definition 2
conclusion for the corresponding total representative. -/
def LG21P42MandatoryGivenAccessCanonicalPolicyWitness
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (profile : LG21P42MandatoryGivenAccessPBOProfile source)
    (noAccessEstimateKernel : Kernel
      (LG21NonTestFeature Feature source.test_feature -> ℝ) ℝ)
    [IsMarkovKernel noAccessEstimateKernel] : Prop :=
  ∃ (baseLaw : Measure (LG21NonTestFeature Feature source.test_feature -> ℝ))
    (baseMean : (LG21NonTestFeature Feature source.test_feature -> ℝ) -> ℝ)
    (baseVariance : ℝ) (hbaseMean : Measurable baseMean)
    (hbaseLaw : IsProbabilityMeasure baseLaw) (hbaseVariance : 0 < baseVariance)
    (hfullBaseFactorization :
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw source.population
          source.test_feature =
        baseLaw ⊗ₘ gaussianLocationKernel
          baseMean hbaseMean baseVariance.toNNReal),
    letI : IsProbabilityMeasure baseLaw := hbaseLaw
    let S : LG21GaussianPBOResamplingSource
        (LG21NonTestFeature Feature source.test_feature -> ℝ) :=
      { baseLaw := baseLaw
        baseLaw_isProbability := inferInstance
        posteriorBaseMean := baseMean
        posteriorBaseMean_measurable := hbaseMean
        posteriorBaseVariance := baseVariance.toNNReal
        posteriorBaseVariance_pos := by
          rw [NNReal.coe_pos, Real.toNNReal_pos]
          exact hbaseVariance
        testNoiseVariance := source.population.noiseVariance source.test_feature
        testNoiseVariance_pos := source.test_noise_variance_positive }
    LG21P42MandatoryGivenAccessSourcePBO source profile S noAccessEstimateKernel ∧
      ¬ lg21SourceLawLatentSkillFair
        (lg21P42MandatoryGivenAccessPolicyLawSurface source S
          noAccessEstimateKernel)

/-- The literal continuous Gaussian source admits a mandatory observed-score
PBO profile.  This establishes nonvacuity without constraining the arbitrary
no-access kernel quantified by Proposition 4.2. -/
theorem lg21P42MandatoryGivenAccessPBOProfile_nonempty
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature) :
    Nonempty (LG21P42MandatoryGivenAccessPBOProfile source) := by
  let mandatory : LG21MandatoryGivenAccessLiteralSourceEquilibrium
      source.population :=
    { action := lg21MandatoryGivenAccessLiteralAction
      feasible := fun student => lg21MandatoryGivenAccessLiteralAction_feasible student }
  let reportedPayoff :
      (LG21NonTestFeature Feature source.test_feature -> ℝ) -> ℝ -> ℝ :=
    lg21ContinuousObservedAccessUnselectedPBO source.population
      source.access_positive source.test_feature
  have hreportedPBO : LG21ObservedAccessAllReportPBO
      (lg21ContinuousGaussianAccessPopulationLaw source.population)
      (lg21ContinuousPopulationBase source.test_feature)
      (lg21ContinuousPopulationFeature source.test_feature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) reportedPayoff := by
    simpa [LG21ObservedAccessAllReportPBO, reportedPayoff] using
      (lg21ContinuousObservedAccess_unselectedPBO_eq_condExp_ae
        source.population source.access_positive source.test_feature).symm
  refine ⟨?_⟩
  exact
    { mandatory := mandatory
      reportedPayoff := reportedPayoff
      reportedPBO := hreportedPBO }

/-- Proposition 4.2 for the actual mandatory-given-access Gaussian source.
The proof derives both the all-report action and the Gaussian PBO realization
from source primitives, then applies the four-group fixed-fibre argument to
the same canonical policy. -/
theorem lg21P42_mandatoryGivenAccessCanonicalPolicy_not_latent_skill_fair
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (profile : LG21P42MandatoryGivenAccessPBOProfile source)
    (noAccessEstimateKernel : Kernel
      (LG21NonTestFeature Feature source.test_feature -> ℝ) ℝ)
    [IsMarkovKernel noAccessEstimateKernel] :
    LG21P42MandatoryGivenAccessCanonicalPolicyWitness source profile
      noAccessEstimateKernel := by
  rcases
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw_exists_gaussianLocationFactorization
        source.population source.test_feature source.prior_variance_positive
        source.non_test_noise_variance_positive with
      ⟨baseLaw, baseMean, baseVariance, hbaseMean, hbaseLaw, hbaseVariance,
        hfullBaseFactorization⟩
  letI : IsProbabilityMeasure baseLaw := hbaseLaw
  let S : LG21GaussianPBOResamplingSource
      (LG21NonTestFeature Feature source.test_feature -> ℝ) :=
    { baseLaw := baseLaw
      baseLaw_isProbability := hbaseLaw
      posteriorBaseMean := baseMean
      posteriorBaseMean_measurable := hbaseMean
      posteriorBaseVariance := baseVariance.toNNReal
      posteriorBaseVariance_pos := by
        rw [NNReal.coe_pos, Real.toNNReal_pos]
        exact hbaseVariance
      testNoiseVariance := source.population.noiseVariance source.test_feature
      testNoiseVariance_pos := source.test_noise_variance_positive }
  let law := lg21ContinuousGaussianAccessPopulationLaw source.population
  let observation : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature source.test_feature -> ℝ) × ℝ :=
    fun student =>
      (lg21ContinuousPopulationBase source.test_feature student,
        lg21ContinuousPopulationFeature source.test_feature student)
  letI : IsProbabilityMeasure law :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability source.population
      source.access_positive
  letI : IsFiniteMeasure law := ⟨by simp⟩
  refine ⟨baseLaw, baseMean, baseVariance, hbaseMean, hbaseLaw, hbaseVariance,
    hfullBaseFactorization, ?_⟩
  have hall : ∀ᵐ student ∂law,
      profile.mandatory.action student = LG21AccessAction.takeAndReport :=
    lg21MandatoryGivenAccess_accessPopulation_ae_takeAndReport
      source.population source.access_positive profile.mandatory.action
      profile.mandatory.feasible
  have hbase : Measurable (lg21ContinuousPopulationBase source.test_feature) :=
    lg21ContinuousPopulationBase_measurable source.test_feature
  have hskill : Measurable
      (lg21ContinuousPopulationSkill (Feature := Feature)) := by
    change Measurable fun student : Bool × (ℝ × (Feature -> ℝ)) => student.2.1
    exact measurable_fst.comp measurable_snd
  have hscore : Measurable (lg21ContinuousPopulationFeature source.test_feature) := by
    change Measurable fun student : Bool × (ℝ × (Feature -> ℝ)) =>
      student.2.1 + student.2.2 source.test_feature
    exact hskill.add ((measurable_pi_apply source.test_feature).comp
      (measurable_snd.comp measurable_snd))
  have hobservation : Measurable observation := hbase.prodMk hscore
  have hreportedPBO :
      (fun student =>
        profile.reportedPayoff
          (lg21ContinuousPopulationBase source.test_feature student)
          (lg21ContinuousPopulationFeature source.test_feature student)) =ᵐ[law]
        law[lg21ContinuousPopulationSkill |
          MeasurableSpace.comap observation inferInstance] := by
    simpa [LG21ObservedAccessAllReportPBO, law, observation] using
      profile.reportedPBO
  have hcondExp :
      law[lg21ContinuousPopulationSkill |
        MeasurableSpace.comap observation inferInstance] =ᵐ[law]
        fun student =>
          ∫ latentSkill, latentSkill ∂condDistrib
            lg21ContinuousPopulationSkill observation law (observation student) := by
    exact condExp_ae_eq_integral_condDistrib' hobservation
      (lg21ContinuousGaussianAccessPopulation_skill_integrable source.population
        source.access_positive)
  have hd6Observation :=
    lg21ContinuousGaussianAccessPopulation_d6Estimate_eq_condDistribMean_ae
      source.population source.access_positive source.test_feature baseLaw baseMean
      hbaseMean baseVariance hbaseVariance source.test_noise_variance_positive
      hfullBaseFactorization
  have hd6Pullback : ∀ᵐ student ∂law,
      lg21D6GaussianPBOEstimate S (observation student) =
        ∫ latentSkill, latentSkill ∂condDistrib
          lg21ContinuousPopulationSkill observation law (observation student) := by
    exact ae_of_ae_map hobservation.aemeasurable hd6Observation
  have hcanonical : ∀ᵐ student ∂law,
      lg21P42GaussianPBOEstimate
          (lg21P42ObservedScoreModelOfD6Source S noAccessEstimateKernel)
          (lg21ContinuousPopulationBase source.test_feature student)
          (lg21ContinuousPopulationFeature source.test_feature student) =
        lg21D6GaussianPBOEstimate S (observation student) :=
    Filter.Eventually.of_forall fun student =>
      lg21P42ObservedScoreModelOfD6Source_estimate_eq_d6 S noAccessEstimateKernel
        (lg21ContinuousPopulationBase source.test_feature student)
        (lg21ContinuousPopulationFeature source.test_feature student)
  have hsource : LG21P42MandatoryGivenAccessSourcePBO source profile S
      noAccessEstimateKernel := by
    refine ⟨hall, ?_⟩
    filter_upwards [hreportedPBO, hcondExp, hd6Pullback, hcanonical] with
        student hpbo hmean hd6 hcanonical
    calc
      profile.reportedPayoff
          (lg21ContinuousPopulationBase source.test_feature student)
          (lg21ContinuousPopulationFeature source.test_feature student) =
          law[lg21ContinuousPopulationSkill |
            MeasurableSpace.comap observation inferInstance] student := hpbo
      _ = ∫ latentSkill, latentSkill ∂condDistrib
          lg21ContinuousPopulationSkill observation law (observation student) := hmean
      _ = lg21D6GaussianPBOEstimate S (observation student) := hd6.symm
      _ = lg21P42GaussianPBOEstimate
          (lg21P42ObservedScoreModelOfD6Source S noAccessEstimateKernel)
          (lg21ContinuousPopulationBase source.test_feature student)
          (lg21ContinuousPopulationFeature source.test_feature student) :=
        hcanonical.symm
  have hnotFair : ¬ lg21SourceLawLatentSkillFair
      (lg21P42MandatoryGivenAccessPolicyLawSurface source S
        noAccessEstimateKernel) :=
    lg21P42CanonicalPBOPolicyLaw_not_latent_skill_fair_of_state profile S
      noAccessEstimateKernel (fun _ => (0 : ℝ))
      (skillLow := (0 : ℝ)) (skillHigh := (1 : ℝ)) (by norm_num)
  exact ⟨hsource, hnotFair⟩

end

end LG21TestOptionalPolicies

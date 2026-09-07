import LG21TestOptionalPolicies.Definition1LiteralPBOContract
import LG21TestOptionalPolicies.MandatoryObservedAccessProposition42Bridge
import LG21TestOptionalPolicies.ObservedAccessPolicyTheorem44Endpoints

/-!
# Direct mandatory Section 4 policy endpoints for LG21

The mandatory-given-access protocol has no voluntary access-side action: source
feasibility fixes `Z = Y = X`.  These endpoints expose the two Section 4
claims over the actual continuous Gaussian population rather than through the
reduced Gaussian diagnostic source.

For Proposition 4.3, a source PBO includes both realized deterministic
branches.  The total value assigned to the impossible access/no-report branch
is universally quantified below, because it is not a source PBO obligation and
cannot affect either attained population.  For Theorem 4.4, Definition 6
replaces the no-access branch by its derived randomized resampling kernel.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib AppliedModelingLib.Probability MeasureTheory ProbabilityTheory

/-- A source-derived Definition 6 experiment.  The witness keeps the
full-base Gaussian factorization, the actual positive-access base/score law,
the conditional synthetic-score pushforward, and both fairness-law identities
together. -/
def LG21Definition6ObservedAccessSourceWitness
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (hnoAccess : 0 < source.population.accessLaw {false}) : Prop :=
  ∃ (baseLaw : Measure (LG21NonTestFeature Feature source.test_feature -> ℝ))
      (baseMean : (LG21NonTestFeature Feature source.test_feature -> ℝ) -> ℝ)
      (baseVariance : ℝ) (hbaseMean : Measurable baseMean)
      (hbaseLaw : IsProbabilityMeasure baseLaw)
      (hbaseVariance : 0 < baseVariance),
    lg21ContinuousGaussianFullBaseLatentPrimitiveLaw source.population
        source.test_feature =
      baseLaw ⊗ₘ gaussianLocationKernel
        baseMean hbaseMean baseVariance.toNNReal ∧
    (letI : IsProbabilityMeasure baseLaw := hbaseLaw
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
     let accessLaw := lg21ContinuousGaussianAccessPopulationLaw source.population
     let noAccessLaw := lg21ContinuousGaussianNoAccessPopulationLaw source.population
     let observation : Bool × (ℝ × (Feature -> ℝ)) ->
        (LG21NonTestFeature Feature source.test_feature -> ℝ) × ℝ :=
      fun student =>
        (lg21ContinuousPopulationBase source.test_feature student,
          lg21ContinuousPopulationFeature source.test_feature student)
     accessLaw.map observation = lg21D6ActualAccessTestLaw S ∧
       (∀ publicBase,
         lg21D6NoAccessResamplingEstimateKernel S publicBase =
           (lg21D6ConditionalGaussianTestKernel S publicBase).map
             (fun score => lg21D6GaussianPBOEstimate S (publicBase, score))) ∧
       (∀ publicBase,
         lg21D6ActualAccessEstimateKernel S publicBase =
           lg21D6NoAccessResamplingEstimateKernel S publicBase) ∧
       (accessLaw.map observation).map (lg21D6GaussianPBOEstimate S) =
         Measure.bind
           (noAccessLaw.map
             (lg21ContinuousPopulationBase source.test_feature))
           (lg21D6NoAccessResamplingEstimateKernel S))

/-- Definition 6's no-access resampling experiment is constructed directly
from the literal continuous Gaussian population.  In particular, neither a
conditional test kernel nor an output-law equality is accepted as a premise. -/
theorem lg21Definition6_observedAccess_source_witness
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (hnoAccess : 0 < source.population.accessLaw {false}) :
    LG21Definition6ObservedAccessSourceWitness source hnoAccess := by
  rcases lg21ContinuousGaussianPopulation_exists_d6ResamplingSource
      source.population source.test_feature source.prior_variance_positive
      source.non_test_noise_variance_positive
      source.test_noise_variance_positive with
    ⟨baseLaw, baseMean, baseVariance, hbaseMean, hbaseLaw, hbaseVariance,
      hfactorization, _S, _hbaseLaw, _hbaseMean, _hbaseVariance,
      _htestNoiseVariance⟩
  letI : IsProbabilityMeasure baseLaw := hbaseLaw
  refine ⟨baseLaw, baseMean, baseVariance, hbaseMean, hbaseLaw, hbaseVariance,
    hfactorization, ?_⟩
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
  let accessLaw := lg21ContinuousGaussianAccessPopulationLaw source.population
  let noAccessLaw := lg21ContinuousGaussianNoAccessPopulationLaw source.population
  let observation : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature source.test_feature -> ℝ) × ℝ :=
    fun student =>
      (lg21ContinuousPopulationBase source.test_feature student,
        lg21ContinuousPopulationFeature source.test_feature student)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [S, accessLaw, observation] using
      (lg21ContinuousGaussianAccessPopulation_fullBaseScoreLaw_eq_d6
        source.population source.access_positive source.test_feature baseLaw
        baseMean hbaseMean baseVariance hbaseVariance
        source.test_noise_variance_positive hfactorization)
  · intro publicBase
    exact lg21D6NoAccessResamplingEstimateKernel_apply S publicBase
  · exact lg21D6GaussianPBOResampling_observably_fair S
  · simpa [S, accessLaw, noAccessLaw, observation] using
      (lg21ContinuousGaussianPopulation_d6AccessOutput_eq_noAccessResampling
        source.population source.access_positive hnoAccess source.test_feature
        baseLaw baseMean hbaseMean baseVariance hbaseVariance
        source.test_noise_variance_positive hfactorization)

/-- A full source PBO profile for the mandatory-given-access protocol.  Unlike
the Proposition 4.2 profile, this also carries the actual no-access PBO used by
Proposition 4.3. -/
structure LG21P43MandatoryGivenAccessPBOProfile
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (hnoAccess : 0 < source.population.accessLaw {false}) where
  mandatory : LG21MandatoryGivenAccessLiteralSourceEquilibrium source.population
  reportedPayoff :
    (LG21NonTestFeature Feature source.test_feature -> ℝ) -> ℝ -> ℝ
  noAccessOutput : Bool × (ℝ × (Feature -> ℝ)) -> ℝ
  pbo : LG21ObservedAccessMandatoryPBODefinition1 source.population
    source.access_positive hnoAccess source.test_feature mandatory reportedPayoff
    noAccessOutput

/-- The continuous Gaussian source supplies a genuine mandatory Definition 1
PBO profile. -/
theorem lg21P43MandatoryGivenAccessPBOProfile_nonempty
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (hnoAccess : 0 < source.population.accessLaw {false}) :
    Nonempty (LG21P43MandatoryGivenAccessPBOProfile source hnoAccess) := by
  rcases lg21ContinuousGaussianPopulation_exists_mandatoryDefinition1PBO
      source.population source.access_positive hnoAccess source.test_feature with
    ⟨mandatory, reportedPayoff, noAccessOutput, hpbo⟩
  exact ⟨{ mandatory := mandatory
           reportedPayoff := reportedPayoff
           noAccessOutput := noAccessOutput
           pbo := hpbo }⟩

/-- The exact two-branch Proposition 4.3 fairness failure for one mandatory
source PBO profile.  `noReportPayoff` is an arbitrary totalization of the
unattained access/no-report branch, not an assumption about school beliefs or
student behavior. -/
def LG21P43MandatoryGivenAccessFairnessFailure
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (hnoAccess : 0 < source.population.accessLaw {false})
    (profile : LG21P43MandatoryGivenAccessPBOProfile source hnoAccess)
    (noReportPayoff :
      (LG21NonTestFeature Feature source.test_feature -> ℝ) -> ℝ) : Prop :=
  letI : IsProbabilityMeasure
      (lg21ContinuousGaussianAccessPopulationLaw source.population) :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability source.population
      source.access_positive
  letI : IsFiniteMeasure
      (lg21ContinuousGaussianAccessPopulationLaw source.population) := ⟨by simp⟩
  letI : IsProbabilityMeasure
      (lg21ContinuousGaussianNoAccessPopulationLaw source.population) :=
    lg21ContinuousGaussianNoAccessPopulationLaw_isProbability source.population
      hnoAccess
  letI : IsFiniteMeasure
      (lg21ContinuousGaussianNoAccessPopulationLaw source.population) := ⟨by simp⟩
  ∃ (baseLaw : Measure (LG21NonTestFeature Feature source.test_feature -> ℝ))
      (baseMean : (LG21NonTestFeature Feature source.test_feature -> ℝ) -> ℝ)
      (baseVariance baseMeanVariance : ℝ)
      (hbaseLaw : IsProbabilityMeasure baseLaw)
      (hbaseMean : Measurable baseMean)
      (hbaseVariance : 0 < baseVariance),
    lg21ContinuousGaussianFullBaseLatentPrimitiveLaw source.population
        source.test_feature =
        baseLaw ⊗ₘ gaussianLocationKernel
          baseMean hbaseMean baseVariance.toNNReal ∧
      0 ≤ baseMeanVariance ∧
      (¬ LG21ObservedAccessDeterministicObservableFairAE baseLaw
        (lg21ContinuousPopulationBase source.test_feature)
        (lg21ContinuousGaussianAccessPopulationLaw source.population)
        (lg21ContinuousGaussianNoAccessPopulationLaw source.population)
        (lg21ObservedAccessDeterministicTwoBranchOutput
          lg21ContinuousPopulationAccess
          (lg21ObservedAccessActualOutput
            (lg21ContinuousPopulationBase source.test_feature)
            (lg21ContinuousPopulationFeature source.test_feature)
            profile.mandatory.action profile.reportedPayoff noReportPayoff)
          profile.noAccessOutput)) ∧
      (¬ LG21ObservedAccessDeterministicDemographicallyFair
        (lg21ContinuousGaussianAccessPopulationLaw source.population)
        (lg21ContinuousGaussianNoAccessPopulationLaw source.population)
        (lg21ObservedAccessDeterministicTwoBranchOutput
          lg21ContinuousPopulationAccess
          (lg21ObservedAccessActualOutput
            (lg21ContinuousPopulationBase source.test_feature)
            (lg21ContinuousPopulationFeature source.test_feature)
            profile.mandatory.action profile.reportedPayoff noReportPayoff)
          profile.noAccessOutput))

/-- Proposition 4.3 for every actual mandatory-given-access source PBO.  The
source derives the Gaussian factorization and both fairness failures; callers
do not supply a comparison law or a posterior identity. -/
theorem lg21P43_mandatoryGivenAccess_actualPBO_not_fair
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (hnoAccess : 0 < source.population.accessLaw {false})
    (profile : LG21P43MandatoryGivenAccessPBOProfile source hnoAccess)
    (noReportPayoff :
      (LG21NonTestFeature Feature source.test_feature -> ℝ) -> ℝ) :
    LG21P43MandatoryGivenAccessFairnessFailure source hnoAccess profile
      noReportPayoff := by
  rcases profile.pbo with
    ⟨_hfeasible, _hforced, _hall, hreportedPBO, hnoAccessPBO⟩
  exact
    lg21ContinuousGaussianPopulation_mandatory_actualPBO_not_fair
      source.population source.access_positive hnoAccess source.test_feature
      source.prior_variance_positive source.non_test_noise_variance_positive
      source.test_noise_variance_positive profile.mandatory profile.reportedPayoff
      noReportPayoff hreportedPBO profile.noAccessOutput hnoAccessPBO

/-- The paper-facing Proposition 4.3 mandatory branch is nonvacuous and
universal over the actual source PBO profiles. -/
theorem lg21P43_mandatoryGivenAccess_actualPBO_nonempty_and_not_fair
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (hnoAccess : 0 < source.population.accessLaw {false}) :
    Nonempty (LG21P43MandatoryGivenAccessPBOProfile source hnoAccess) ∧
      ∀ (profile : LG21P43MandatoryGivenAccessPBOProfile source hnoAccess)
        (noReportPayoff :
          (LG21NonTestFeature Feature source.test_feature -> ℝ) -> ℝ),
        LG21P43MandatoryGivenAccessFairnessFailure source hnoAccess profile
          noReportPayoff := by
  exact ⟨lg21P43MandatoryGivenAccessPBOProfile_nonempty source hnoAccess,
    fun profile noReportPayoff =>
      lg21P43_mandatoryGivenAccess_actualPBO_not_fair source hnoAccess profile
        noReportPayoff⟩

/-- The exact Definition 6 fairness certificate for one mandatory source PBO
profile.  The no-access output is the resampling kernel constructed from the
same continuous Gaussian source. -/
def LG21T44MandatoryGivenAccessResamplingFairnessCertificate
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (hnoAccess : 0 < source.population.accessLaw {false})
    (profile : LG21P42MandatoryGivenAccessPBOProfile source)
    (noReportPayoff :
      (LG21NonTestFeature Feature source.test_feature -> ℝ) -> ℝ) : Prop :=
  ∃ (baseLaw : Measure (LG21NonTestFeature Feature source.test_feature -> ℝ))
      (baseMean : (LG21NonTestFeature Feature source.test_feature -> ℝ) -> ℝ)
      (baseVariance : ℝ) (hbaseMean : Measurable baseMean)
      (hbaseLaw : IsProbabilityMeasure baseLaw)
      (hbaseVariance : 0 < baseVariance),
    lg21ContinuousGaussianFullBaseLatentPrimitiveLaw source.population
        source.test_feature =
      baseLaw ⊗ₘ gaussianLocationKernel
        baseMean hbaseMean baseVariance.toNNReal ∧
    (letI : IsProbabilityMeasure baseLaw := hbaseLaw
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
     letI : IsProbabilityMeasure
        (lg21ContinuousGaussianAccessPopulationLaw source.population) :=
        lg21ContinuousGaussianAccessPopulationLaw_isProbability source.population
          source.access_positive
     letI : IsFiniteMeasure
        (lg21ContinuousGaussianAccessPopulationLaw source.population) := ⟨by simp⟩
     LG21ObservedAccessFair source.population source.test_feature
      { accessOutput := lg21ObservedAccessActualOutput
          (lg21ContinuousPopulationBase source.test_feature)
          (lg21ContinuousPopulationFeature source.test_feature)
          profile.mandatory.action profile.reportedPayoff noReportPayoff
        noAccessKernel := lg21D6NoAccessResamplingEstimateKernel S
        noAccessKernel_isMarkov := inferInstance })

/-- Theorem 4.4 for every actual mandatory-given-access all-report PBO.  The
no-access resampling kernel and its fairness comparison are derived from the
source rather than assumed as an equality of output laws. -/
theorem lg21T44_mandatoryGivenAccess_resampling_observedAccessFair
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (hnoAccess : 0 < source.population.accessLaw {false})
    (profile : LG21P42MandatoryGivenAccessPBOProfile source)
    (noReportPayoff :
      (LG21NonTestFeature Feature source.test_feature -> ℝ) -> ℝ) :
    LG21T44MandatoryGivenAccessResamplingFairnessCertificate source hnoAccess
      profile noReportPayoff := by
  exact
    lg21ContinuousGaussianPopulation_mandatory_resampling_observedAccessFair
      source.population source.access_positive hnoAccess source.test_feature
      source.prior_variance_positive source.non_test_noise_variance_positive
      source.test_noise_variance_positive profile.mandatory profile.reportedPayoff
      noReportPayoff profile.reportedPBO

/-- The paper-facing Theorem 4.4 mandatory branch is nonvacuous and universal
over the all-report PBO profile; totalizations of the unreachable no-report
branch do not enter any source PBO premise. -/
theorem lg21T44_mandatoryGivenAccess_resampling_nonempty_and_fair
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (hnoAccess : 0 < source.population.accessLaw {false}) :
    Nonempty (LG21P42MandatoryGivenAccessPBOProfile source) ∧
      ∀ (profile : LG21P42MandatoryGivenAccessPBOProfile source)
        (noReportPayoff :
          (LG21NonTestFeature Feature source.test_feature -> ℝ) -> ℝ),
        LG21T44MandatoryGivenAccessResamplingFairnessCertificate source hnoAccess
          profile noReportPayoff := by
  exact ⟨lg21P42MandatoryGivenAccessPBOProfile_nonempty source,
    fun profile noReportPayoff =>
      lg21T44_mandatoryGivenAccess_resampling_observedAccessFair source hnoAccess
        profile noReportPayoff⟩

end

end LG21TestOptionalPolicies

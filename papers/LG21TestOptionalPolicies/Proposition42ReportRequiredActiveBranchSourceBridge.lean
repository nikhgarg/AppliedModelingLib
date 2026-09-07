import LG21TestOptionalPolicies.Proposition42CanonicalPolicySourceLaw
import LG21TestOptionalPolicies.ObservedAccessReportRequiredPositiveMassRefinedOutputBridge
import LG21TestOptionalPolicies.ObservedAccessVoluntaryActiveBranchModels

/-!
# Report-required active-branch source realization for LG21 Proposition 4.2

This is the report-required counterpart of
`Proposition42ActiveBranchSourceBridge`.  It keeps the total fixed-fibre
Gaussian PBO representative distinct from its almost-everywhere realization by
the selected source profile.  The latter is only an RCD-a.e. identity, so this
module does not claim a pointwise off-path PBO version.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib AppliedModelingLib.Probability MeasureTheory ProbabilityTheory

/-- The total fixed-fibre PBO policy-law representative for a report-required
selected profile.  The index is the actual selected profile type, never a
synthetic singleton. -/
def lg21P42ReportRequiredActiveBranchPolicyLawSurface
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
    (LG21ReportRequiredActiveBranchProfile source) S noAccessEstimateKernel

/-- The selected report-required source output is the literal conditional mean
of skill after the full observed `(base, score)` record, almost everywhere. -/
def LG21P42ReportRequiredActiveBranchSourcePBO
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (profile : LG21ReportRequiredActiveBranchProfile source)
    (baseLaw : Measure (LG21NonTestFeature Feature source.test_feature -> ℝ))
    (baseMean : (LG21NonTestFeature Feature source.test_feature -> ℝ) -> ℝ)
    (baseVariance : ℝ) (hbaseMean : Measurable baseMean)
    (hbaseLaw : IsProbabilityMeasure baseLaw)
    (hbaseVariance : 0 < baseVariance)
    (hfullBaseFactorization :
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw source.population
          source.test_feature =
        baseLaw ⊗ₘ gaussianLocationKernel
          baseMean hbaseMean baseVariance.toNNReal) : Prop :=
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
  lg21ReportRequiredSequentialActualOutput
      (lg21ContinuousPopulationBase source.test_feature)
      (lg21ContinuousPopulationFeature source.test_feature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) profile.selected =ᵐ[law]
    fun student =>
      ∫ latentSkill, latentSkill ∂condDistrib
        (lg21ContinuousPopulationSkill (Feature := Feature)) observation law
        (observation student)

/-- The source profile's attained output is the literal Gaussian conditional
mean.  The proof derives the selected-action output and then transports the
literal posterior identity through the measurable full observation. -/
theorem lg21P42ReportRequiredActiveBranchSourcePBO_of_source
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (profile : LG21ReportRequiredActiveBranchProfile source)
    (baseLaw : Measure (LG21NonTestFeature Feature source.test_feature -> ℝ))
    (baseMean : (LG21NonTestFeature Feature source.test_feature -> ℝ) -> ℝ)
    (baseVariance : ℝ) (hbaseMean : Measurable baseMean)
    (hbaseLaw : IsProbabilityMeasure baseLaw)
    (hbaseVariance : 0 < baseVariance)
    (hfullBaseFactorization :
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw source.population
          source.test_feature =
        baseLaw ⊗ₘ gaussianLocationKernel
          baseMean hbaseMean baseVariance.toNNReal) :
    LG21P42ReportRequiredActiveBranchSourcePBO source profile baseLaw baseMean
      baseVariance hbaseMean hbaseLaw hbaseVariance hfullBaseFactorization := by
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
  have hactual :=
    lg21ContinuousGaussianAccessPopulation_reportRequired_positiveMassRefined_actualOutput_eq_d6_ae_of_fibrewiseActiveBranchSelection
      source.population source.access_positive source.test_feature
      source.prior_variance_positive source.non_test_noise_variance_positive
      source.test_noise_variance_positive profile.selected profile.positive_branch_pbo
      profile.active_branch_selection baseLaw baseMean hbaseMean baseVariance
      hbaseVariance hfullBaseFactorization
  have hd6 :=
    lg21ContinuousGaussianAccessPopulation_d6Estimate_eq_condDistribMean_ae
      source.population source.access_positive source.test_feature baseLaw baseMean
      hbaseMean baseVariance hbaseVariance source.test_noise_variance_positive
      hfullBaseFactorization
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
  have hd6Pullback : ∀ᵐ student ∂law,
      lg21D6GaussianPBOEstimate S (observation student) =
        ∫ latentSkill, latentSkill ∂condDistrib
          (lg21ContinuousPopulationSkill (Feature := Feature)) observation law
          (observation student) := by
    exact ae_of_ae_map hobservation.aemeasurable hd6
  exact hactual.trans hd6Pullback

/-- The report-required canonical PBO witness separates the total
fixed-fibre representative from its RCD-a.e. selected-profile realization. -/
def LG21P42ReportRequiredActiveBranchCanonicalPolicyWitness
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (profile : LG21ReportRequiredActiveBranchProfile source)
    (noAccessEstimateKernel : Kernel
      (LG21NonTestFeature Feature source.test_feature -> ℝ) ℝ)
    [IsMarkovKernel noAccessEstimateKernel] : Prop :=
  ∃ (baseLaw : Measure (LG21NonTestFeature Feature source.test_feature -> ℝ))
    (baseMean : (LG21NonTestFeature Feature source.test_feature -> ℝ) -> ℝ)
    (baseVariance : ℝ) (hbaseMean : Measurable baseMean)
    (hbaseLaw : IsProbabilityMeasure baseLaw)
    (hbaseVariance : 0 < baseVariance)
    (hfullBaseFactorization :
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw source.population
          source.test_feature =
        baseLaw ⊗ₘ gaussianLocationKernel
          baseMean hbaseMean baseVariance.toNNReal),
    LG21P42ReportRequiredActiveBranchSourcePBO source profile baseLaw baseMean
      baseVariance hbaseMean hbaseLaw hbaseVariance hfullBaseFactorization ∧
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
     ¬ lg21SourceLawLatentSkillFair
       (lg21P42ReportRequiredActiveBranchPolicyLawSurface source S
         noAccessEstimateKernel))

/-- Proposition 4.2 for report-required-after-taking under the declared
active-branch convention. -/
theorem lg21P42_reportRequiredActiveBranchCanonicalPolicy_not_latent_skill_fair
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (profile : LG21ReportRequiredActiveBranchProfile source)
    (noAccessEstimateKernel : Kernel
      (LG21NonTestFeature Feature source.test_feature -> ℝ) ℝ)
    [IsMarkovKernel noAccessEstimateKernel] :
    LG21P42ReportRequiredActiveBranchCanonicalPolicyWitness source profile
      noAccessEstimateKernel := by
  rcases
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw_exists_gaussianLocationFactorization
        source.population source.test_feature source.prior_variance_positive
        source.non_test_noise_variance_positive with
    ⟨baseLaw, baseMean, baseVariance, hbaseMean, hbaseLaw, hbaseVariance,
      hfullBaseFactorization⟩
  letI : IsProbabilityMeasure baseLaw := hbaseLaw
  refine ⟨baseLaw, baseMean, baseVariance, hbaseMean, hbaseLaw, hbaseVariance,
    hfullBaseFactorization, ?_, ?_⟩
  · exact lg21P42ReportRequiredActiveBranchSourcePBO_of_source source profile
      baseLaw baseMean baseVariance hbaseMean hbaseLaw hbaseVariance
      hfullBaseFactorization
  · let S : LG21GaussianPBOResamplingSource
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
    exact
      lg21P42CanonicalPBOPolicyLaw_not_latent_skill_fair_of_state profile S
        noAccessEstimateKernel (fun _ => (0 : ℝ))
        (skillLow := (0 : ℝ)) (skillHigh := (1 : ℝ)) (by norm_num)

/-- The report-required convention is nonvacuous for the literal Gaussian
source, so the Proposition 4.2 policy witness has an actual selected profile. -/
theorem lg21P42_reportRequiredActiveBranchCanonicalPolicy_not_latent_skill_fair_exists
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (noAccessEstimateKernel : Kernel
      (LG21NonTestFeature Feature source.test_feature -> ℝ) ℝ)
    [IsMarkovKernel noAccessEstimateKernel] :
    ∃ profile : LG21ReportRequiredActiveBranchProfile source,
      LG21P42ReportRequiredActiveBranchCanonicalPolicyWitness source profile
        noAccessEstimateKernel := by
  rcases
      lg21ObservedAccessGaussianSource_reportRequiredActiveBranchProfile_nonempty
        source with ⟨profile⟩
  exact ⟨profile,
    lg21P42_reportRequiredActiveBranchCanonicalPolicy_not_latent_skill_fair
      source profile noAccessEstimateKernel⟩

end

end LG21TestOptionalPolicies

import LG21TestOptionalPolicies.Proposition42CanonicalPolicySourceLaw
import LG21TestOptionalPolicies.ObservedAccessOptionalActiveBranchD6OutputBridge
import LG21TestOptionalPolicies.ObservedAccessVoluntaryActiveBranchModels

/-!
# Active-branch source realization for LG21 Proposition 4.2

The fixed-fibre Gaussian calculation in `Proposition42CanonicalPolicySourceLaw`
is not by itself an equilibrium theorem.  This module supplies the missing
source-facing bridge under the declared Section 4 active-branch convention:

* the equilibrium index is an actual selected optional source profile, never
  `Unit`;
* the selected profile's realized access output is the literal conditional
  mean of skill given the full observed `(base, score)` record almost
  everywhere; and
* the fixed-fibre policy representative uses the same Gaussian conditional
  experiment, while the no-access policy remains an arbitrary base-only
  Markov kernel.

The a.e. representative is the approved continuous/RCD convention.  This
does not assert that the refinement follows from the paper's bare static RCD
definition.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib AppliedModelingLib.Probability MeasureTheory ProbabilityTheory

/-- The total fixed-fibre policy-law representative for a voluntary
active-branch source profile.  Its equilibrium index is the actual selected
profile type; the companion source-PBO predicate below establishes the
connection between this representative and each selected profile's realized
output. -/
def lg21P42OptionalActiveBranchPolicyLawSurface
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
    (LG21OptionalActiveBranchProfile source) S noAccessEstimateKernel

/-- The source-PBO realization obligation for the total conditional-law
representative.  It is stated directly in terms of the literal access
population, source action output, and conditional expectation, rather than a
field or helper name. -/
def LG21P42OptionalActiveBranchSourcePBO
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (profile : LG21OptionalActiveBranchProfile source)
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
  lg21OptionalSourceTimedActualOutput
      (lg21ContinuousPopulationBase source.test_feature)
      (lg21ContinuousPopulationFeature source.test_feature)
      (lg21ContinuousPopulationSkill (Feature := Feature))
      profile.selected.actions =ᵐ[law]
    fun student =>
      ∫ latentSkill, latentSkill ∂condDistrib
        (lg21ContinuousPopulationSkill (Feature := Feature)) observation law
        (observation student)

/-- Under the declared active-branch selection, the selected optional source
output is the literal source conditional mean used by Proposition 4.2.  The
proof first derives the selected all-report output from the source PBO, then
uses the literal Gaussian posterior bridge; it does not assume either fact. -/
theorem lg21P42OptionalActiveBranchSourcePBO_of_source
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (profile : LG21OptionalActiveBranchProfile source)
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
    LG21P42OptionalActiveBranchSourcePBO source profile baseLaw baseMean
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
    lg21_optional_positiveMassRefined_actualOutput_eq_d6_ae_of_fibrewiseActiveBranchSelection
      source.population source.access_positive source.test_feature
      source.prior_variance_positive source.non_test_noise_variance_positive
      source.test_noise_variance_positive baseLaw baseMean hbaseMean baseVariance
      hbaseVariance hfullBaseFactorization profile.selected
      profile.active_branch_selection
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

/-- A source realization of Proposition 4.2 under the declared voluntary
active-branch convention.  The total canonical PBO representative supplies
the fixed-fibre conditional laws used in the source statement.  The selected
profile realizes that representative almost everywhere; this is deliberately
kept separate because conditional distributions are only fixed up to null
sets. -/
def LG21P42OptionalActiveBranchCanonicalPolicyWitness
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (profile : LG21OptionalActiveBranchProfile source)
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
    LG21P42OptionalActiveBranchSourcePBO source profile baseLaw baseMean
      baseVariance hbaseMean hbaseLaw hbaseVariance
      hfullBaseFactorization ∧
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
       (lg21P42OptionalActiveBranchPolicyLawSurface source S
         noAccessEstimateKernel))

/-- Proposition 4.2 under the declared voluntary active-branch convention.
For every arbitrary base-only no-access policy, the literal source supplies a
canonical total Gaussian-PBO representative that is realized by the selected
profile almost everywhere, and the representative fails the paper's
fixed-fibre latent-skill equality.  The total representative handles the
source's conditional laws at null fibres; the profile realization is only
almost everywhere, as appropriate for the recorded RCD convention. -/
theorem lg21P42_optionalActiveBranchCanonicalPolicy_not_latent_skill_fair
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (profile : LG21OptionalActiveBranchProfile source)
    (noAccessEstimateKernel : Kernel
      (LG21NonTestFeature Feature source.test_feature -> ℝ) ℝ)
    [IsMarkovKernel noAccessEstimateKernel] :
    LG21P42OptionalActiveBranchCanonicalPolicyWitness source profile
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
  · exact lg21P42OptionalActiveBranchSourcePBO_of_source source profile baseLaw
      baseMean baseVariance hbaseMean hbaseLaw hbaseVariance
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

/-- The declared optional active-branch convention is nonvacuous for the
literal Gaussian source, so the Proposition 4.2 witness does not obtain its
fairness refutation from an empty equilibrium carrier. -/
theorem lg21P42_optionalActiveBranchCanonicalPolicy_not_latent_skill_fair_exists
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (noAccessEstimateKernel : Kernel
      (LG21NonTestFeature Feature source.test_feature -> ℝ) ℝ)
    [IsMarkovKernel noAccessEstimateKernel] :
    ∃ profile : LG21OptionalActiveBranchProfile source,
      LG21P42OptionalActiveBranchCanonicalPolicyWitness source profile
        noAccessEstimateKernel := by
  rcases
      lg21ObservedAccessGaussianSource_optionalActiveBranchProfile_nonempty
        source with ⟨profile⟩
  exact ⟨profile,
    lg21P42_optionalActiveBranchCanonicalPolicy_not_latent_skill_fair
      source profile noAccessEstimateKernel⟩

end

end LG21TestOptionalPolicies

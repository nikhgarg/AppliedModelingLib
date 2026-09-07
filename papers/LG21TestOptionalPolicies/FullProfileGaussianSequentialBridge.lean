import AppliedModelingLib.Foundations.Probability.FiniteGaussianSignalKernelRCD
import LG21TestOptionalPolicies.ContinuousGaussianFullProfileSourceLaw

/-!
# Full-profile sequential Gaussian update bridge for LG21

The literal LG21 source law already separates every non-test noise coordinate
from the test noise.  This module wires that exact separation into the generic
one-step Gaussian RCD transition.  It does not posit a posterior formula: the
remaining premise is precisely a proved factorization of the full non-test
profile and latent skill.  A finite-coordinate induction can discharge that
premise without changing the theorem below.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

/-- The primitive full non-test profile and latent skill, before drawing the
designated test-noise coordinate. -/
def lg21ContinuousGaussianFullBaseLatentPrimitiveLaw
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature) :
    Measure ((LG21NonTestFeature Feature testFeature → ℝ) × ℝ) :=
  ((gaussianReal M.priorMean M.priorVariance).prod
    (lg21ContinuousGaussianNonTestNoiseLaw M testFeature)).map
    (fun primitive =>
      ((fun feature => primitive.1 + primitive.2 feature), primitive.1))

private theorem measurable_lg21ContinuousGaussianFullBaseLatentPrimitiveMap
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature) :
    Measurable (fun primitive : ℝ × (LG21NonTestFeature Feature testFeature → ℝ) =>
      ((fun feature => primitive.1 + primitive.2 feature), primitive.1)) := by
  exact (measurable_pi_lambda _ fun feature =>
    measurable_fst.add ((measurable_pi_apply feature).comp measurable_snd)).prodMk
      measurable_fst

/-- Under the literal product source law, adjoining the designated independent
test noise to the full non-test profile/skill law is exactly the generic
one-step extended source law. -/
theorem lg21ContinuousGaussianFullProfilePrimitiveLaw_eq_extend_fullBaseLatent
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature) :
    (lg21ContinuousGaussianFullProfilePrimitiveLaw M testFeature).map
      (fun primitive =>
        (lg21ContinuousGaussianFullProfileObservation testFeature primitive,
          primitive.1)) =
      AppliedModelingLib.Probability.gaussianSignalExtendBaseLatentLaw
        (lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature)
        (M.noiseVariance testFeature : ℝ) := by
  let prior : Measure ℝ := gaussianReal M.priorMean M.priorVariance
  let nonTestNoise : Measure (LG21NonTestFeature Feature testFeature → ℝ) :=
    lg21ContinuousGaussianNonTestNoiseLaw M testFeature
  let testNoise : Measure ℝ := gaussianReal 0 (M.noiseVariance testFeature)
  let baseMap : ℝ × (LG21NonTestFeature Feature testFeature → ℝ) →
      (LG21NonTestFeature Feature testFeature → ℝ) × ℝ :=
    fun primitive =>
      ((fun feature => primitive.1 + primitive.2 feature), primitive.1)
  let fullMap : ℝ × ((LG21NonTestFeature Feature testFeature → ℝ) × ℝ) →
      ((LG21NonTestFeature Feature testFeature → ℝ) × ℝ) × ℝ :=
    fun primitive =>
      (((fun feature => primitive.1 + primitive.2.1 feature),
          primitive.1 + primitive.2.2), primitive.1)
  let follow : ((LG21NonTestFeature Feature testFeature → ℝ) × ℝ) × ℝ →
      ((LG21NonTestFeature Feature testFeature → ℝ) × ℝ) × ℝ :=
    fun primitive =>
      ((primitive.1.1, primitive.1.2 + primitive.2), primitive.1.2)
  have hbaseMap : Measurable baseMap := by
    exact measurable_lg21ContinuousGaussianFullBaseLatentPrimitiveMap testFeature
  have hfullMap : Measurable fullMap := by
    exact (measurable_pi_lambda _ fun feature =>
      measurable_fst.add
        ((measurable_pi_apply feature).comp (measurable_fst.comp measurable_snd))).prodMk
      (measurable_fst.add (measurable_snd.comp measurable_snd)) |>.prodMk measurable_fst
  have hfollow : Measurable follow := by fun_prop
  have hassoc : Measurable
      (MeasurableEquiv.prodAssoc :
        (ℝ × (LG21NonTestFeature Feature testFeature → ℝ)) × ℝ ≃ᵐ
          ℝ × ((LG21NonTestFeature Feature testFeature → ℝ) × ℝ)) := by
    fun_prop
  letI : IsProbabilityMeasure prior := by
    dsimp [prior]
    infer_instance
  letI : IsProbabilityMeasure nonTestNoise := by
    dsimp [nonTestNoise, lg21ContinuousGaussianNonTestNoiseLaw]
    infer_instance
  letI : IsProbabilityMeasure testNoise := by
    dsimp [testNoise]
    infer_instance
  dsimp [lg21ContinuousGaussianFullProfilePrimitiveLaw,
    lg21ContinuousGaussianFullBaseLatentPrimitiveLaw,
    lg21ContinuousGaussianFullProfileObservation,
    AppliedModelingLib.Probability.gaussianSignalExtendBaseLatentLaw]
  simp only [Real.toNNReal_coe]
  change (prior.prod (nonTestNoise.prod testNoise)).map fullMap =
    (((prior.prod nonTestNoise).map baseMap).prod testNoise).map follow
  calc
    (prior.prod (nonTestNoise.prod testNoise)).map fullMap =
        (((prior.prod nonTestNoise).prod testNoise).map
          MeasurableEquiv.prodAssoc).map fullMap := by
          rw [Measure.prodAssoc_prod]
    _ = ((prior.prod nonTestNoise).prod testNoise).map
        (fullMap ∘ MeasurableEquiv.prodAssoc) := by
          rw [Measure.map_map hfullMap hassoc]
    _ = ((prior.prod nonTestNoise).prod testNoise).map
        (follow ∘ Prod.map baseMap id) := by
          rfl
    _ = (((prior.prod nonTestNoise).map baseMap).prod
          (testNoise.map id)).map follow := by
          rw [Measure.map_prod_map (prior.prod nonTestNoise) testNoise
            hbaseMap measurable_id]
          rw [Measure.map_map hfollow (by fun_prop)]
    _ = (((prior.prod nonTestNoise).map baseMap).prod testNoise).map follow := by
          simp

/-- The literal full non-test LG21 source profile has a derived Gaussian
latent-skill factorization.  This instantiates the generic finite-coordinate
induction with every actual non-test source feature; it neither names nor
assumes a posterior formula. -/
theorem lg21ContinuousGaussianFullBaseLatentPrimitiveLaw_exists_gaussianLocationFactorization
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ)) :
    ∃ (baseLaw : Measure (LG21NonTestFeature Feature testFeature → ℝ))
        (baseMean : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ)
        (baseVariance : ℝ) (hbaseMean : Measurable baseMean),
      IsProbabilityMeasure baseLaw ∧ 0 < baseVariance ∧
        lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
          baseLaw ⊗ₘ AppliedModelingLib.Probability.gaussianLocationKernel
            baseMean hbaseMean baseVariance.toNNReal := by
  rcases AppliedModelingLib.Probability.gaussianFiniteProfileLatentLaw_exists_gaussianLocationFactorization
        M.priorMean (M.priorVariance : ℝ) hpriorVariance
        (fun feature : LG21NonTestFeature Feature testFeature =>
          (M.noiseVariance feature.1 : ℝ)) hnonTestNoiseVariance with
      ⟨baseLaw, baseMean, baseVariance, hbaseMean,
        hbaseLaw, hbaseVariance, hfactorization⟩
  refine ⟨baseLaw, baseMean, baseVariance, hbaseMean,
    hbaseLaw, hbaseVariance, ?_⟩
  simpa [lg21ContinuousGaussianFullBaseLatentPrimitiveLaw,
    AppliedModelingLib.Probability.gaussianFiniteProfileLatentLaw,
    lg21ContinuousGaussianNonTestNoiseLaw, Real.toNNReal_coe] using
    hfactorization

/-- The actual positive-access LG21 conditional skill law after the full
non-test profile and the designated test score.  The only premise is the
finite-profile Gaussian factorization of the literal non-test source law;
the test-score update and the access-population transport are proved here.

The equality is almost everywhere in the actual full public-observation
marginal, as required for a regular conditional distribution. -/
theorem lg21ContinuousGaussianAccessPopulation_condDistrib_skill_given_full_base_score_of_fullBaseGaussianFactorization_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature → ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (hfullBaseFactorization :
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
        baseLaw ⊗ₘ AppliedModelingLib.Probability.gaussianLocationKernel
          baseMean hbaseMean baseVariance.toNNReal) :
    let law := lg21ContinuousGaussianAccessPopulationLaw M
    let observation : Bool × (ℝ × (Feature → ℝ)) →
        (LG21NonTestFeature Feature testFeature → ℝ) × ℝ :=
      fun student =>
        (lg21ContinuousPopulationBase testFeature student,
          lg21ContinuousPopulationFeature testFeature student)
    letI : IsProbabilityMeasure law :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
    letI : IsFiniteMeasure law := ⟨by simp⟩
    condDistrib lg21ContinuousPopulationSkill observation law =ᵐ[
        law.map observation]
      AppliedModelingLib.Probability.gaussianSignalPosteriorBaseKernel
        baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ) := by
  intro law observation
  letI : IsProbabilityMeasure law :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  letI : IsFiniteMeasure law := ⟨by simp⟩
  have hskill : Measurable (lg21ContinuousPopulationSkill (Feature := Feature)) := by
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) => student.2.1
    exact measurable_fst.comp measurable_snd
  have hnoise : Measurable
      (lg21ContinuousPopulationNoise (Feature := Feature) testFeature) := by
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) =>
      student.2.2 testFeature
    exact (measurable_pi_apply testFeature).comp
      (measurable_snd.comp measurable_snd)
  have hscore : Measurable
      (lg21ContinuousPopulationFeature (Feature := Feature) testFeature) := by
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) =>
      student.2.1 + student.2.2 testFeature
    exact hskill.add hnoise
  have hobservation : Measurable observation := by
    exact (lg21ContinuousPopulationBase_measurable testFeature).prodMk hscore
  let scoreKernel : Kernel (LG21NonTestFeature Feature testFeature → ℝ) ℝ :=
    AppliedModelingLib.Probability.gaussianLocationKernel baseMean hbaseMean
      (baseVariance + (M.noiseVariance testFeature : ℝ)).toNNReal
  let posteriorKernel : Kernel
      ((LG21NonTestFeature Feature testFeature → ℝ) × ℝ) ℝ :=
    AppliedModelingLib.Probability.gaussianSignalPosteriorBaseKernel
      baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)
  letI : IsMarkovKernel scoreKernel :=
    AppliedModelingLib.Probability.gaussianLocationKernel_isMarkov baseMean hbaseMean
      (baseVariance + (M.noiseVariance testFeature : ℝ)).toNNReal
  letI : IsMarkovKernel posteriorKernel :=
    AppliedModelingLib.Probability.gaussianSignalPosteriorBaseKernel_isMarkov
      baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)
  have hprimitiveExtend :
      (lg21ContinuousGaussianFullProfilePrimitiveLaw M testFeature).map
        (fun primitive =>
          (lg21ContinuousGaussianFullProfileObservation testFeature primitive,
            primitive.1)) =
        AppliedModelingLib.Probability.gaussianSignalExtendBaseLatentLaw
          (lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature)
          (M.noiseVariance testFeature : ℝ) :=
    lg21ContinuousGaussianFullProfilePrimitiveLaw_eq_extend_fullBaseLatent
      M testFeature
  have hupdate :
      AppliedModelingLib.Probability.gaussianSignalExtendBaseLatentLaw
          (lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature)
          (M.noiseVariance testFeature : ℝ) =
        AppliedModelingLib.Probability.gaussianSignalBaseScoreLatentLaw
          baseLaw baseMean hbaseMean baseVariance
          (M.noiseVariance testFeature : ℝ) :=
    AppliedModelingLib.Probability.gaussianSignalExtendBaseLatentLaw_eq_baseScoreLatentLaw
      baseLaw baseMean hbaseMean baseVariance
      (M.noiseVariance testFeature : ℝ)
      (lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature)
      hfullBaseFactorization
  have hfactor : law.map (fun student =>
      (observation student, lg21ContinuousPopulationSkill student)) =
        baseLaw ⊗ₘ scoreKernel ⊗ₘ posteriorKernel := by
    calc
      law.map (fun student =>
          (observation student, lg21ContinuousPopulationSkill student)) =
          (lg21ContinuousGaussianFullProfilePrimitiveLaw M testFeature).map
            (fun primitive =>
              (lg21ContinuousGaussianFullProfileObservation testFeature primitive,
                primitive.1)) := by
            simpa [law, observation] using
              (lg21ContinuousGaussianAccessPopulation_full_base_score_skill_law
                M haccess testFeature)
      _ = AppliedModelingLib.Probability.gaussianSignalExtendBaseLatentLaw
          (lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature)
          (M.noiseVariance testFeature : ℝ) := hprimitiveExtend
      _ = AppliedModelingLib.Probability.gaussianSignalBaseScoreLatentLaw
          baseLaw baseMean hbaseMean baseVariance
          (M.noiseVariance testFeature : ℝ) := hupdate
      _ = baseLaw ⊗ₘ scoreKernel ⊗ₘ posteriorKernel := by
        exact AppliedModelingLib.Probability.gaussianSignalBaseScoreLatentLaw_factorization
          baseLaw baseMean hbaseMean baseVariance
          (M.noiseVariance testFeature : ℝ)
          hbaseVariance htestNoiseVariance
  have hbaseScore : law.map observation = baseLaw ⊗ₘ scoreKernel := by
    calc
      law.map observation =
          (law.map (fun student =>
            (observation student, lg21ContinuousPopulationSkill student))).map Prod.fst := by
            rw [Measure.map_map measurable_fst (hobservation.prodMk hskill)]
            rfl
      _ = (baseLaw ⊗ₘ scoreKernel ⊗ₘ posteriorKernel).map Prod.fst := by
            rw [hfactor]
      _ = baseLaw ⊗ₘ scoreKernel := by
            exact Measure.fst_compProd _ _
  apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (μ := law) (X := observation) (Y := lg21ContinuousPopulationSkill)
    (κ := posteriorKernel) hobservation hskill
  calc
    law.map (fun student =>
        (observation student, lg21ContinuousPopulationSkill student)) =
        baseLaw ⊗ₘ scoreKernel ⊗ₘ posteriorKernel := hfactor
    _ = law.map observation ⊗ₘ posteriorKernel := by rw [hbaseScore]

/-- Fully source-derived full-profile conditional Gaussian law for LG21.
The non-test-profile factorization is produced by the generic finite
induction above, and the test-score update is the literal independent-noise
transition.  The posterior kernel equality is therefore only a.e. in the
actual public-observation marginal, not an off-path or named-PBO convention. -/
theorem lg21ContinuousGaussianAccessPopulation_exists_condDistrib_skill_given_full_base_score_gaussian_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ)) :
    ∃ (baseLaw : Measure (LG21NonTestFeature Feature testFeature → ℝ))
        (baseMean : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ)
        (baseVariance : ℝ) (hbaseMean : Measurable baseMean),
      IsProbabilityMeasure baseLaw ∧ 0 < baseVariance ∧
        let law := lg21ContinuousGaussianAccessPopulationLaw M
        let observation : Bool × (ℝ × (Feature → ℝ)) →
            (LG21NonTestFeature Feature testFeature → ℝ) × ℝ :=
          fun student =>
            (lg21ContinuousPopulationBase testFeature student,
              lg21ContinuousPopulationFeature testFeature student)
        letI : IsProbabilityMeasure law :=
          lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
        letI : IsFiniteMeasure law := ⟨by simp⟩
        condDistrib lg21ContinuousPopulationSkill observation law =ᵐ[
            law.map observation]
          AppliedModelingLib.Probability.gaussianSignalPosteriorBaseKernel
            baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ) := by
  rcases
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw_exists_gaussianLocationFactorization
        M testFeature hpriorVariance hnonTestNoiseVariance with
      ⟨baseLaw, baseMean, baseVariance, hbaseMean,
        hbaseLaw, hbaseVariance, hfactorization⟩
  refine ⟨baseLaw, baseMean, baseVariance, hbaseMean,
    hbaseLaw, hbaseVariance, ?_⟩
  exact
    lg21ContinuousGaussianAccessPopulation_condDistrib_skill_given_full_base_score_of_fullBaseGaussianFactorization_ae
      M haccess testFeature baseLaw baseMean hbaseMean baseVariance
      hbaseVariance htestNoiseVariance hfactorization

/-- Source-facing Section 4 bridge: the literal positive-access population
has an a.e. Gaussian latent-skill conditional law after every non-test feature
and the designated test score.  The remaining Lemma 4.1 work is only the
action-selected public-belief bridge. -/
abbrev lg21_source_full_profile_gaussian_conditional_law :=
  @lg21ContinuousGaussianAccessPopulation_exists_condDistrib_skill_given_full_base_score_gaussian_ae

end

end LG21TestOptionalPolicies

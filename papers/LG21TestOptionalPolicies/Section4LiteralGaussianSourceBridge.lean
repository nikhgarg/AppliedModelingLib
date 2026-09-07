import LG21TestOptionalPolicies.FullProfileGaussianSequentialBridge
import LG21TestOptionalPolicies.Theorem44SourceGaussianResamplingRepair

/-!
# Literal Section 4 Gaussian source bridge for LG21

This module derives the Gaussian resampling input used by Definition 6 from
the paper's literal finite-profile population.  It keeps the full non-test
profile as the base observation, rather than replacing it by a named
posterior formula.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

/-- The literal source population conditional on not having test access. -/
def lg21ContinuousGaussianNoAccessPopulationLaw
    {Feature : Type*} [Fintype Feature]
    (M : LG21ContinuousGaussianPopulation Feature) :
    Measure (Bool × (ℝ × (Feature → ℝ))) :=
  lg21NormalizedRestriction (lg21ContinuousGaussianPopulationLaw M)
    {student | lg21ContinuousPopulationAccess student = false}

/-- The no-access conditional population is a probability law whenever that
source population has positive mass. -/
theorem lg21ContinuousGaussianNoAccessPopulationLaw_isProbability
    {Feature : Type*} [Fintype Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (hnoAccess : 0 < M.accessLaw {false}) :
    IsProbabilityMeasure (lg21ContinuousGaussianNoAccessPopulationLaw M) := by
  letI : IsProbabilityMeasure M.accessLaw := M.accessLaw_isProbability
  letI : IsProbabilityMeasure (lg21ContinuousGaussianNoiseLaw M) := by
    unfold lg21ContinuousGaussianNoiseLaw
    infer_instance
  letI : IsProbabilityMeasure
      (lg21ContinuousGaussianStudentPrimitiveLaw M) := by
    unfold lg21ContinuousGaussianStudentPrimitiveLaw
    infer_instance
  letI : IsProbabilityMeasure (lg21ContinuousGaussianPopulationLaw M) :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  apply lg21NormalizedRestriction_isProbability
  · change lg21ContinuousGaussianPopulationLaw M
      {student | lg21ContinuousPopulationAccess student = false} ≠ 0
    rw [show {student : Bool × (ℝ × (Feature → ℝ)) |
        lg21ContinuousPopulationAccess student = false} =
        ({false} : Set Bool) ×ˢ Set.univ by
          ext student
          change student.1 = false ↔ student.1 = false ∧ student.2 ∈ Set.univ
          simp,
      lg21ContinuousGaussianPopulation_access_student_factorization]
    simpa using ne_of_gt hnoAccess
  · exact measure_ne_top _ _

/-- Conditioning the literal product source population on `Z = 0` leaves the
student block unchanged, just as it does for `Z = 1`. -/
theorem lg21ContinuousGaussianNoAccessPopulation_map_student_eq
    {Feature : Type*} [Fintype Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (hnoAccess : 0 < M.accessLaw {false}) :
    (lg21ContinuousGaussianNoAccessPopulationLaw M).map Prod.snd =
      lg21ContinuousGaussianStudentPrimitiveLaw M := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let studentLaw := lg21ContinuousGaussianStudentPrimitiveLaw M
  let accessEvent : Set (Bool × (ℝ × (Feature → ℝ))) :=
    {student | lg21ContinuousPopulationAccess student = false}
  letI : IsProbabilityMeasure rawLaw := by
    simpa [rawLaw] using lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsProbabilityMeasure M.accessLaw := M.accessLaw_isProbability
  letI : IsProbabilityMeasure studentLaw := by
    unfold studentLaw lg21ContinuousGaussianStudentPrimitiveLaw
    unfold lg21ContinuousGaussianNoiseLaw
    infer_instance
  have haccessEvent : accessEvent = ({false} : Set Bool) ×ˢ Set.univ := by
    ext student
    change student.1 = false ↔ student.1 = false ∧ student.2 ∈ Set.univ
    simp
  have hraw_access : rawLaw accessEvent = M.accessLaw {false} := by
    rw [haccessEvent, lg21ContinuousGaussianPopulation_access_student_factorization]
    simp [studentLaw]
  have haccess_ne_zero : rawLaw accessEvent ≠ 0 := by
    rw [hraw_access]
    exact ne_of_gt hnoAccess
  ext target htarget
  rw [Measure.map_apply measurable_snd htarget]
  change lg21NormalizedRestriction rawLaw accessEvent (Prod.snd ⁻¹' target) =
    studentLaw target
  rw [lg21NormalizedRestriction_apply rawLaw (measurable_snd htarget)]
  have hpreimage :
      Prod.snd ⁻¹' target ∩ accessEvent = ({false} : Set Bool) ×ˢ target := by
    rw [haccessEvent]
    ext student
    simp [and_comm]
  rw [hpreimage]
  rw [show rawLaw = lg21ContinuousGaussianPopulationLaw M by rfl,
    lg21ContinuousGaussianPopulation_access_student_factorization]
  rw [hraw_access]
  rw [← mul_assoc,
    ENNReal.inv_mul_cancel (ne_of_gt hnoAccess) (measure_ne_top _ _), one_mul]

/-- Access and no-access populations have exactly the same literal non-test
base-profile law; the equality follows from the source's product population,
not from a fairness condition. -/
theorem lg21ContinuousGaussianAccess_noAccess_baseLaw_eq
    {Feature : Type*} [Fintype Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature) :
    (lg21ContinuousGaussianAccessPopulationLaw M).map
      (lg21ContinuousPopulationBase testFeature) =
      (lg21ContinuousGaussianNoAccessPopulationLaw M).map
        (lg21ContinuousPopulationBase testFeature) := by
  let studentBase : ℝ × (Feature → ℝ) →
      LG21NonTestFeature Feature testFeature → ℝ :=
    fun primitive feature => primitive.1 + primitive.2 feature.1
  have hstudentBase : Measurable studentBase := by
    apply measurable_pi_lambda
    intro feature
    exact measurable_fst.add
      ((measurable_pi_apply feature.1).comp measurable_snd)
  calc
    (lg21ContinuousGaussianAccessPopulationLaw M).map
        (lg21ContinuousPopulationBase testFeature) =
      ((lg21ContinuousGaussianAccessPopulationLaw M).map Prod.snd).map
        studentBase := by
          rw [Measure.map_map hstudentBase measurable_snd]
          rfl
    _ = (lg21ContinuousGaussianStudentPrimitiveLaw M).map studentBase := by
          rw [lg21ContinuousGaussianAccessPopulation_map_student_eq M haccess]
    _ = ((lg21ContinuousGaussianNoAccessPopulationLaw M).map Prod.snd).map
        studentBase := by
          rw [lg21ContinuousGaussianNoAccessPopulation_map_student_eq M hnoAccess]
    _ = (lg21ContinuousGaussianNoAccessPopulationLaw M).map
        (lg21ContinuousPopulationBase testFeature) := by
          rw [Measure.map_map hstudentBase measurable_snd]
          rfl

/--
The literal finite Gaussian source supplies the base law and the positive
Gaussian posterior variance needed by the Definition 6 resampling experiment.
The statement exposes the factorization too, because it is the source-law
link used for the actual access score distribution below.
-/
theorem lg21ContinuousGaussianPopulation_exists_d6ResamplingSource
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ)) :
    ∃ (baseLaw : Measure (LG21NonTestFeature Feature testFeature → ℝ))
        (baseMean : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ)
        (baseVariance : ℝ) (hbaseMean : Measurable baseMean),
      IsProbabilityMeasure baseLaw ∧ 0 < baseVariance ∧
        lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
          baseLaw ⊗ₘ AppliedModelingLib.Probability.gaussianLocationKernel
            baseMean hbaseMean baseVariance.toNNReal ∧
        ∃ S : LG21GaussianPBOResamplingSource
            (LG21NonTestFeature Feature testFeature → ℝ),
          S.baseLaw = baseLaw ∧
          S.posteriorBaseMean = baseMean ∧
          S.posteriorBaseVariance = baseVariance.toNNReal ∧
          S.testNoiseVariance = M.noiseVariance testFeature := by
  rcases
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw_exists_gaussianLocationFactorization
        M testFeature hpriorVariance hnonTestNoiseVariance with
      ⟨baseLaw, baseMean, baseVariance, hbaseMean,
        hbaseLaw, hbaseVariance, hfactorization⟩
  letI : IsProbabilityMeasure baseLaw := hbaseLaw
  let S : LG21GaussianPBOResamplingSource
      (LG21NonTestFeature Feature testFeature → ℝ) :=
    { baseLaw := baseLaw
      baseLaw_isProbability := hbaseLaw
      posteriorBaseMean := baseMean
      posteriorBaseMean_measurable := hbaseMean
      posteriorBaseVariance := baseVariance.toNNReal
      posteriorBaseVariance_pos := by
        rw [NNReal.coe_pos, Real.toNNReal_pos]
        exact hbaseVariance
      testNoiseVariance := M.noiseVariance testFeature
      testNoiseVariance_pos := htestNoiseVariance }
  refine ⟨baseLaw, baseMean, baseVariance, hbaseMean,
    hbaseLaw, hbaseVariance, hfactorization, S, rfl, rfl, rfl, rfl⟩

/--
Under a literal finite-profile Gaussian factorization, the positive-access
population's actual full-base/score law is precisely the Definition 6
Gaussian experiment.  This is an equality of source measures, not a supplied
conditional-score kernel.
-/
theorem lg21ContinuousGaussianAccessPopulation_fullBaseScoreLaw_eq_d6
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
    let S : LG21GaussianPBOResamplingSource
        (LG21NonTestFeature Feature testFeature → ℝ) :=
      { baseLaw := baseLaw
        baseLaw_isProbability := inferInstance
        posteriorBaseMean := baseMean
        posteriorBaseMean_measurable := hbaseMean
        posteriorBaseVariance := baseVariance.toNNReal
        posteriorBaseVariance_pos := by
          rw [NNReal.coe_pos, Real.toNNReal_pos]
          exact hbaseVariance
        testNoiseVariance := M.noiseVariance testFeature
        testNoiseVariance_pos := htestNoiseVariance }
    let law := lg21ContinuousGaussianAccessPopulationLaw M
    let observation : Bool × (ℝ × (Feature → ℝ)) →
        (LG21NonTestFeature Feature testFeature → ℝ) × ℝ :=
      fun student =>
        (lg21ContinuousPopulationBase testFeature student,
          lg21ContinuousPopulationFeature testFeature student)
    law.map observation = lg21D6ActualAccessTestLaw S := by
  intro S law observation
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
  have hskill : Measurable (lg21ContinuousPopulationSkill (Feature := Feature)) := by
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) => student.2.1
    exact measurable_fst.comp measurable_snd
  have hscore : Measurable
      (lg21ContinuousPopulationFeature (Feature := Feature) testFeature) := by
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) =>
      student.2.1 + student.2.2 testFeature
    exact hskill.add ((measurable_pi_apply testFeature).comp
      (measurable_snd.comp measurable_snd))
  have hobservation : Measurable observation := by
    exact (lg21ContinuousPopulationBase_measurable testFeature).prodMk hscore
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
  have hvariance :
      baseVariance.toNNReal + M.noiseVariance testFeature =
        (baseVariance + (M.noiseVariance testFeature : ℝ)).toNNReal := by
    simpa using
      (Real.toNNReal_add hbaseVariance.le
        (M.noiseVariance testFeature).coe_nonneg).symm
  have hkernel : scoreKernel = lg21D6ConditionalGaussianTestKernel S := by
    ext base target htarget
    rw [show scoreKernel base = gaussianReal (baseMean base)
      (baseVariance + (M.noiseVariance testFeature : ℝ)).toNNReal by
        exact AppliedModelingLib.Probability.gaussianLocationKernel_apply _ _ _ _]
    rw [lg21D6ConditionalGaussianTestKernel_apply]
    change
      gaussianReal (baseMean base)
          (baseVariance + (M.noiseVariance testFeature : ℝ)).toNNReal target =
        gaussianReal (baseMean base)
          (baseVariance.toNNReal + M.noiseVariance testFeature) target
    rw [hvariance]
  calc
    law.map observation = baseLaw ⊗ₘ scoreKernel := hbaseScore
    _ = baseLaw ⊗ₘ lg21D6ConditionalGaussianTestKernel S := by rw [hkernel]
    _ = lg21D6ActualAccessTestLaw S := rfl

/-
The Definition 6 affine estimator has the same formula as the mean of its
one-step Gaussian posterior.  This is kept separate from the source-law
transport so the latter can use a literal `condDistrib` equality.
-/
theorem lg21D6GaussianPBOEstimate_eq_gaussianPosteriorMean
    {Base : Type*} [MeasurableSpace Base]
    (S : LG21GaussianPBOResamplingSource Base) (observation : Base × ℝ) :
    lg21D6GaussianPBOEstimate S observation =
      ∫ skill, skill ∂AppliedModelingLib.Probability.gaussianSignalPosteriorBaseKernel
        S.posteriorBaseMean S.posteriorBaseMean_measurable
        (S.posteriorBaseVariance : ℝ) (S.testNoiseVariance : ℝ) observation := by
  rw [AppliedModelingLib.Probability.gaussianSignalPosteriorBaseKernel_integral_id]
  dsimp [lg21D6GaussianPBOEstimate, lg21D6PosteriorTestWeight,
    AppliedModelingLib.Probability.gaussianSignalWeight,
    AppliedModelingLib.Probability.gaussianSignalPriorWeight]
  have hsum : (S.posteriorBaseVariance : ℝ) + (S.testNoiseVariance : ℝ) ≠ 0 :=
    ne_of_gt (lg21D6PosteriorVarianceSum_pos S)
  field_simp
  ring

/--
The Definition 6 affine estimate induced by the literal finite-profile source
is the actual conditional mean of skill after the complete non-test profile
and the observed test score, almost everywhere in the source observation
law.  The a.e. scope is the natural one for a regular conditional
distribution; no off-path PBO value is chosen here.
-/
theorem lg21ContinuousGaussianAccessPopulation_d6Estimate_eq_condDistribMean_ae
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
    let S : LG21GaussianPBOResamplingSource
        (LG21NonTestFeature Feature testFeature → ℝ) :=
      { baseLaw := baseLaw
        baseLaw_isProbability := inferInstance
        posteriorBaseMean := baseMean
        posteriorBaseMean_measurable := hbaseMean
        posteriorBaseVariance := baseVariance.toNNReal
        posteriorBaseVariance_pos := by
          rw [NNReal.coe_pos, Real.toNNReal_pos]
          exact hbaseVariance
        testNoiseVariance := M.noiseVariance testFeature
        testNoiseVariance_pos := htestNoiseVariance }
    let law := lg21ContinuousGaussianAccessPopulationLaw M
    let observation : Bool × (ℝ × (Feature → ℝ)) →
        (LG21NonTestFeature Feature testFeature → ℝ) × ℝ :=
      fun student =>
        (lg21ContinuousPopulationBase testFeature student,
          lg21ContinuousPopulationFeature testFeature student)
    letI : IsProbabilityMeasure law :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
    letI : IsFiniteMeasure law := ⟨by simp⟩
    (fun publicObservation => lg21D6GaussianPBOEstimate S publicObservation) =ᵐ[
        law.map observation]
      fun publicObservation =>
        ∫ skill, skill ∂condDistrib
          lg21ContinuousPopulationSkill observation law publicObservation := by
  intro S law observation
  letI : IsProbabilityMeasure law :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  letI : IsFiniteMeasure law := ⟨by simp⟩
  have hrcd :=
    lg21ContinuousGaussianAccessPopulation_condDistrib_skill_given_full_base_score_of_fullBaseGaussianFactorization_ae
      M haccess testFeature baseLaw baseMean hbaseMean baseVariance
      hbaseVariance htestNoiseVariance hfullBaseFactorization
  filter_upwards [hrcd] with publicObservation hrcdAt
  rw [hrcdAt]
  simpa [S, max_eq_left hbaseVariance.le] using
    (lg21D6GaussianPBOEstimate_eq_gaussianPosteriorMean S publicObservation)

/--
The actual positive-access output law generated from the literal source
profile equals the Definition 6 no-access resampling output law.  The first
equality below is the source transport; the second is the already-proved
same-experiment resampling identity.  Thus no matching access kernel is
assumed as an interface premise.
-/
theorem lg21ContinuousGaussianAccessPopulation_d6OutputLaw_eq_resampling
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
    let S : LG21GaussianPBOResamplingSource
        (LG21NonTestFeature Feature testFeature → ℝ) :=
      { baseLaw := baseLaw
        baseLaw_isProbability := inferInstance
        posteriorBaseMean := baseMean
        posteriorBaseMean_measurable := hbaseMean
        posteriorBaseVariance := baseVariance.toNNReal
        posteriorBaseVariance_pos := by
          rw [NNReal.coe_pos, Real.toNNReal_pos]
          exact hbaseVariance
        testNoiseVariance := M.noiseVariance testFeature
        testNoiseVariance_pos := htestNoiseVariance }
    let law := lg21ContinuousGaussianAccessPopulationLaw M
    let observation : Bool × (ℝ × (Feature → ℝ)) →
        (LG21NonTestFeature Feature testFeature → ℝ) × ℝ :=
      fun student =>
        (lg21ContinuousPopulationBase testFeature student,
          lg21ContinuousPopulationFeature testFeature student)
    (law.map observation).map (lg21D6GaussianPBOEstimate S) =
      lg21D6NoAccessResamplingEstimateLaw S := by
  intro S law observation
  have htestLaw :=
    lg21ContinuousGaussianAccessPopulation_fullBaseScoreLaw_eq_d6
      M haccess testFeature baseLaw baseMean hbaseMean baseVariance
      hbaseVariance htestNoiseVariance hfullBaseFactorization
  have hsourceOutput :
      (law.map observation).map (lg21D6GaussianPBOEstimate S) =
        lg21D6ActualAccessEstimateLaw S := by
    rw [htestLaw]
    rfl
  calc
    (law.map observation).map (lg21D6GaussianPBOEstimate S) =
      lg21D6ActualAccessEstimateLaw S := hsourceOutput
    _ = lg21D6NoAccessResamplingEstimateLaw S :=
      lg21D6ActualAccessEstimateLaw_eq_noAccessResamplingEstimateLaw S

/-- The base law recovered by the finite-profile Gaussian factorization is
the actual positive-access base marginal of the literal source population. -/
theorem lg21ContinuousGaussianAccessPopulation_baseLaw_eq_of_factorization
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
    (lg21ContinuousGaussianAccessPopulationLaw M).map
      (lg21ContinuousPopulationBase testFeature) = baseLaw := by
  let S : LG21GaussianPBOResamplingSource
      (LG21NonTestFeature Feature testFeature → ℝ) :=
    { baseLaw := baseLaw
      baseLaw_isProbability := inferInstance
      posteriorBaseMean := baseMean
      posteriorBaseMean_measurable := hbaseMean
      posteriorBaseVariance := baseVariance.toNNReal
      posteriorBaseVariance_pos := by
        rw [NNReal.coe_pos, Real.toNNReal_pos]
        exact hbaseVariance
      testNoiseVariance := M.noiseVariance testFeature
      testNoiseVariance_pos := htestNoiseVariance }
  let law := lg21ContinuousGaussianAccessPopulationLaw M
  let observation : Bool × (ℝ × (Feature → ℝ)) →
      (LG21NonTestFeature Feature testFeature → ℝ) × ℝ :=
    fun student =>
      (lg21ContinuousPopulationBase testFeature student,
        lg21ContinuousPopulationFeature testFeature student)
  have hbase : Measurable (lg21ContinuousPopulationBase testFeature) :=
    lg21ContinuousPopulationBase_measurable testFeature
  letI : IsMarkovKernel (lg21D6ConditionalGaussianTestKernel S) :=
    lg21D6ConditionalGaussianTestKernel_isMarkov S
  have hskill : Measurable (lg21ContinuousPopulationSkill (Feature := Feature)) := by
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) => student.2.1
    exact measurable_fst.comp measurable_snd
  have hscore : Measurable
      (lg21ContinuousPopulationFeature (Feature := Feature) testFeature) := by
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) =>
      student.2.1 + student.2.2 testFeature
    exact hskill.add ((measurable_pi_apply testFeature).comp
      (measurable_snd.comp measurable_snd))
  have hobservation : Measurable observation := hbase.prodMk hscore
  have hsource :=
    lg21ContinuousGaussianAccessPopulation_fullBaseScoreLaw_eq_d6
      M haccess testFeature baseLaw baseMean hbaseMean baseVariance
      hbaseVariance htestNoiseVariance hfullBaseFactorization
  calc
    (lg21ContinuousGaussianAccessPopulationLaw M).map
        (lg21ContinuousPopulationBase testFeature) =
      (law.map observation).map Prod.fst := by
        rw [Measure.map_map measurable_fst hobservation]
        rfl
    _ = (lg21D6ActualAccessTestLaw S).map Prod.fst := by
        rw [hsource]
    _ = baseLaw := by
        exact Measure.fst_compProd _ _

/--
The literal access output and literal no-access resampling output agree as
population measures.  The no-access base marginal is derived from the same
independent-access source population, so this is the demographic law bridge
needed by Theorem 4.4 once its behavioral premise makes actual access scores
available.
-/
theorem lg21ContinuousGaussianPopulation_d6AccessOutput_eq_noAccessResampling
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
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
    let S : LG21GaussianPBOResamplingSource
        (LG21NonTestFeature Feature testFeature → ℝ) :=
      { baseLaw := baseLaw
        baseLaw_isProbability := inferInstance
        posteriorBaseMean := baseMean
        posteriorBaseMean_measurable := hbaseMean
        posteriorBaseVariance := baseVariance.toNNReal
        posteriorBaseVariance_pos := by
          rw [NNReal.coe_pos, Real.toNNReal_pos]
          exact hbaseVariance
        testNoiseVariance := M.noiseVariance testFeature
        testNoiseVariance_pos := htestNoiseVariance }
    let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
    let noAccessLaw := lg21ContinuousGaussianNoAccessPopulationLaw M
    let observation : Bool × (ℝ × (Feature → ℝ)) →
        (LG21NonTestFeature Feature testFeature → ℝ) × ℝ :=
      fun student =>
        (lg21ContinuousPopulationBase testFeature student,
          lg21ContinuousPopulationFeature testFeature student)
    (accessLaw.map observation).map (lg21D6GaussianPBOEstimate S) =
      Measure.bind (noAccessLaw.map (lg21ContinuousPopulationBase testFeature))
        (lg21D6NoAccessResamplingEstimateKernel S) := by
  intro S accessLaw noAccessLaw observation
  have houtput :=
    lg21ContinuousGaussianAccessPopulation_d6OutputLaw_eq_resampling
      M haccess testFeature baseLaw baseMean hbaseMean baseVariance
      hbaseVariance htestNoiseVariance hfullBaseFactorization
  have hbaseAccess :=
    lg21ContinuousGaussianAccessPopulation_baseLaw_eq_of_factorization
      M haccess testFeature baseLaw baseMean hbaseMean baseVariance
      hbaseVariance htestNoiseVariance hfullBaseFactorization
  have hbaseNoAccess : noAccessLaw.map (lg21ContinuousPopulationBase testFeature) = baseLaw := by
    calc
      noAccessLaw.map (lg21ContinuousPopulationBase testFeature) =
          accessLaw.map (lg21ContinuousPopulationBase testFeature) := by
            simpa [accessLaw, noAccessLaw] using
              (lg21ContinuousGaussianAccess_noAccess_baseLaw_eq
                M haccess hnoAccess testFeature).symm
      _ = baseLaw := by simpa [accessLaw] using hbaseAccess
  calc
    (accessLaw.map observation).map (lg21D6GaussianPBOEstimate S) =
      lg21D6NoAccessResamplingEstimateLaw S := houtput
    _ = Measure.bind baseLaw (lg21D6NoAccessResamplingEstimateKernel S) := rfl
    _ = Measure.bind (noAccessLaw.map (lg21ContinuousPopulationBase testFeature))
        (lg21D6NoAccessResamplingEstimateKernel S) := by rw [hbaseNoAccess]

/--
Complete law-level fairness of the source-generated Definition 6 experiment:
the conditional access and resampling kernels agree at every full base, and
the literal access and no-access population output laws agree.  This theorem
is deliberately stated for the experiment after access scores are available;
the separate Lemma 4.1 route supplies that behavioral fact.
-/
theorem lg21ContinuousGaussianPopulation_d6SourceExperiment_fair
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
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
    let S : LG21GaussianPBOResamplingSource
        (LG21NonTestFeature Feature testFeature → ℝ) :=
      { baseLaw := baseLaw
        baseLaw_isProbability := inferInstance
        posteriorBaseMean := baseMean
        posteriorBaseMean_measurable := hbaseMean
        posteriorBaseVariance := baseVariance.toNNReal
        posteriorBaseVariance_pos := by
          rw [NNReal.coe_pos, Real.toNNReal_pos]
          exact hbaseVariance
        testNoiseVariance := M.noiseVariance testFeature
        testNoiseVariance_pos := htestNoiseVariance }
    let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
    let noAccessLaw := lg21ContinuousGaussianNoAccessPopulationLaw M
    let observation : Bool × (ℝ × (Feature → ℝ)) →
        (LG21NonTestFeature Feature testFeature → ℝ) × ℝ :=
      fun student =>
        (lg21ContinuousPopulationBase testFeature student,
          lg21ContinuousPopulationFeature testFeature student)
    (∀ publicBase,
      lg21D6ActualAccessEstimateKernel S publicBase =
        lg21D6NoAccessResamplingEstimateKernel S publicBase) ∧
      (accessLaw.map observation).map (lg21D6GaussianPBOEstimate S) =
        Measure.bind (noAccessLaw.map (lg21ContinuousPopulationBase testFeature))
          (lg21D6NoAccessResamplingEstimateKernel S) := by
  intro S accessLaw noAccessLaw observation
  refine ⟨lg21D6GaussianPBOResampling_observably_fair S, ?_⟩
  exact lg21ContinuousGaussianPopulation_d6AccessOutput_eq_noAccessResampling
    M haccess hnoAccess testFeature baseLaw baseMean hbaseMean baseVariance
    hbaseVariance htestNoiseVariance hfullBaseFactorization

end

end LG21TestOptionalPolicies

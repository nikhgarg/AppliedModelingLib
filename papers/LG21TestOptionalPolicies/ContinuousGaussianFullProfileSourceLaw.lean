import LG21TestOptionalPolicies.ContinuousAccessConditionedPopulation

/-!
# Literal full-profile Gaussian source law for LG21

The source model gives one latent Gaussian skill and an independent Gaussian
noise coordinate for every finite feature.  This module separates the test
noise from the entire non-test noise profile, then carries that literal
finite-product law through the positive-access population.

It deliberately stops before asserting a closed-form posterior for an
arbitrary finite profile.  The final multivariate Gaussian update is a
separate induction obligation.  What is proved here is the exact source law
to which that induction must apply, and the fact that the actual full-profile
conditional distribution is the RCD of that source-derived law.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

/-- The literal product law of all source noises except the designated test
coordinate. -/
def lg21ContinuousGaussianNonTestNoiseLaw
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature) :
    Measure (LG21NonTestFeature Feature testFeature → ℝ) :=
  Measure.pi (fun feature => gaussianReal 0 (M.noiseVariance feature.1))

/-- The measurable coordinate split that keeps every non-test noise coordinate
and separates the designated test-noise coordinate. -/
def lg21ContinuousGaussianNoiseSplit
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature) :
    (Feature → ℝ) ≃ᵐ
      (LG21NonTestFeature Feature testFeature → ℝ) × ℝ :=
  (MeasurableEquiv.piCongrLeft (fun _ : Feature => ℝ)
      (Equiv.optionSubtypeNe testFeature)).symm.trans
    (MeasurableEquiv.piOptionEquivProd
      (fun _ : Option (LG21NonTestFeature Feature testFeature) => ℝ))

theorem lg21ContinuousGaussianNoiseSplit_apply
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature) (noise : Feature → ℝ) :
    lg21ContinuousGaussianNoiseSplit testFeature noise =
      ((fun feature => noise feature.1), noise testFeature) := by
  rfl

/-- The source product measure splits exactly into all non-test noise
coordinates and the designated independent test noise. -/
theorem lg21ContinuousGaussianNoiseLaw_map_nonTest_test_eq
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature) :
    (lg21ContinuousGaussianNoiseLaw M).map
      (lg21ContinuousGaussianNoiseSplit testFeature) =
      (lg21ContinuousGaussianNonTestNoiseLaw M testFeature).prod
        (gaussianReal 0 (M.noiseVariance testFeature)) := by
  let NonTest := LG21NonTestFeature Feature testFeature
  let e : Option NonTest ≃ Feature := Equiv.optionSubtypeNe testFeature
  let optionLaw : Option NonTest → Measure ℝ :=
    fun feature => gaussianReal 0 (M.noiseVariance (e feature))
  let ePi : (Option NonTest → ℝ) ≃ᵐ (Feature → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : Feature => ℝ) e
  let optionSplit : (Option NonTest → ℝ) ≃ᵐ (NonTest → ℝ) × ℝ :=
    MeasurableEquiv.piOptionEquivProd (fun _ : Option NonTest => ℝ)
  let split : (Feature → ℝ) ≃ᵐ (NonTest → ℝ) × ℝ :=
    ePi.symm.trans optionSplit
  have hpi : (Measure.pi optionLaw).map ePi = lg21ContinuousGaussianNoiseLaw M := by
    simpa [optionLaw, ePi, e, lg21ContinuousGaussianNoiseLaw] using
      (Measure.pi_map_piCongrLeft e
        (fun feature : Feature => gaussianReal 0 (M.noiseVariance feature)))
  have hoption :
      ((lg21ContinuousGaussianNonTestNoiseLaw M testFeature).prod
        (gaussianReal 0 (M.noiseVariance testFeature))).map optionSplit.symm =
        Measure.pi optionLaw := by
    simpa [lg21ContinuousGaussianNonTestNoiseLaw, optionLaw, e] using
      (Measure.pi_map_piOptionEquivProd optionLaw)
  change (lg21ContinuousGaussianNoiseLaw M).map split =
    (lg21ContinuousGaussianNonTestNoiseLaw M testFeature).prod
      (gaussianReal 0 (M.noiseVariance testFeature))
  apply (split.map_apply_eq_iff_map_symm_apply_eq).2
  calc
    lg21ContinuousGaussianNoiseLaw M = (Measure.pi optionLaw).map ePi := hpi.symm
    _ = (((lg21ContinuousGaussianNonTestNoiseLaw M testFeature).prod
        (gaussianReal 0 (M.noiseVariance testFeature))).map optionSplit.symm).map ePi := by
      rw [hoption]
    _ = ((lg21ContinuousGaussianNonTestNoiseLaw M testFeature).prod
        (gaussianReal 0 (M.noiseVariance testFeature))).map split.symm := by
      rw [Measure.map_map ePi.measurable optionSplit.symm.measurable]
      rfl

/-- The literal primitive law after separating the complete non-test noise
profile from the designated test noise. -/
def lg21ContinuousGaussianFullProfilePrimitiveLaw
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature) :
    Measure (ℝ × ((LG21NonTestFeature Feature testFeature → ℝ) × ℝ)) :=
  (gaussianReal M.priorMean M.priorVariance).prod
    ((lg21ContinuousGaussianNonTestNoiseLaw M testFeature).prod
      (gaussianReal 0 (M.noiseVariance testFeature)))

/-- The source population's latent skill and split literal noise coordinates. -/
def lg21ContinuousPopulationFullPrimitive
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature) :
    Bool × (ℝ × (Feature → ℝ)) →
      ℝ × ((LG21NonTestFeature Feature testFeature → ℝ) × ℝ) :=
  fun student =>
    (lg21ContinuousPopulationSkill student,
      ((fun feature => lg21ContinuousPopulationNoise feature.1 student),
        lg21ContinuousPopulationNoise testFeature student))

/-- Reconstruct the full observed non-test profile and test score from the
latent skill plus the literal split noise vector. -/
def lg21ContinuousGaussianFullProfileObservation
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature) :
    ℝ × ((LG21NonTestFeature Feature testFeature → ℝ) × ℝ) →
      (LG21NonTestFeature Feature testFeature → ℝ) × ℝ :=
  fun primitive =>
    ((fun feature => primitive.1 + primitive.2.1 feature),
      primitive.1 + primitive.2.2)

private theorem measurable_lg21ContinuousPopulationFullPrimitive
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature) :
    Measurable (lg21ContinuousPopulationFullPrimitive (Feature := Feature) testFeature) := by
  have hskill : Measurable (lg21ContinuousPopulationSkill (Feature := Feature)) := by
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) => student.2.1
    exact measurable_fst.comp measurable_snd
  have hnonTest : Measurable
      (fun student : Bool × (ℝ × (Feature → ℝ)) =>
        fun feature : LG21NonTestFeature Feature testFeature =>
          lg21ContinuousPopulationNoise feature.1 student) := by
    apply measurable_pi_lambda
    intro feature
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) => student.2.2 feature.1
    exact (measurable_pi_apply feature.1).comp
      (measurable_snd.comp measurable_snd)
  have htest : Measurable
      (lg21ContinuousPopulationNoise (Feature := Feature) testFeature) := by
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) => student.2.2 testFeature
    exact (measurable_pi_apply testFeature).comp
      (measurable_snd.comp measurable_snd)
  exact hskill.prodMk (hnonTest.prodMk htest)

private theorem measurable_lg21ContinuousGaussianFullProfileObservation
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature) :
    Measurable (lg21ContinuousGaussianFullProfileObservation (Feature := Feature) testFeature) := by
  have hskill : Measurable
      (fun primitive : ℝ × ((LG21NonTestFeature Feature testFeature → ℝ) × ℝ) =>
        primitive.1) := measurable_fst
  have hnonTest : Measurable
      (fun primitive : ℝ × ((LG21NonTestFeature Feature testFeature → ℝ) × ℝ) =>
        primitive.2.1) := measurable_fst.comp measurable_snd
  have htest : Measurable
      (fun primitive : ℝ × ((LG21NonTestFeature Feature testFeature → ℝ) × ℝ) =>
        primitive.2.2) := measurable_snd.comp measurable_snd
  exact (measurable_pi_lambda _ fun feature =>
      hskill.add ((measurable_pi_apply feature).comp hnonTest)).prodMk
    (hskill.add htest)

/-- Positive-access sampling preserves the literal full primitive Gaussian law.
This is the source-model bridge for every finite non-test feature coordinate,
not only one selected coordinate. -/
theorem lg21ContinuousGaussianAccessPopulation_full_primitive_law
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature) :
    (lg21ContinuousGaussianAccessPopulationLaw M).map
      (lg21ContinuousPopulationFullPrimitive testFeature) =
      lg21ContinuousGaussianFullProfilePrimitiveLaw M testFeature := by
  let sourcePrimitiveLaw := lg21ContinuousGaussianStudentPrimitiveLaw M
  let splitPrimitive : ℝ × (Feature → ℝ) →
      ℝ × ((LG21NonTestFeature Feature testFeature → ℝ) × ℝ) :=
    fun primitive => (primitive.1,
      lg21ContinuousGaussianNoiseSplit testFeature primitive.2)
  have hsplitPrimitive : Measurable splitPrimitive := by
    exact measurable_fst.prodMk
      ((lg21ContinuousGaussianNoiseSplit testFeature).measurable.comp measurable_snd)
  letI : IsProbabilityMeasure (lg21ContinuousGaussianNoiseLaw M) := by
    unfold lg21ContinuousGaussianNoiseLaw
    infer_instance
  have hprimitive : sourcePrimitiveLaw.map splitPrimitive =
      lg21ContinuousGaussianFullProfilePrimitiveLaw M testFeature := by
    change Measure.map (Prod.map id (lg21ContinuousGaussianNoiseSplit testFeature))
      ((gaussianReal M.priorMean M.priorVariance).prod
        (lg21ContinuousGaussianNoiseLaw M)) = _
    rw [← Measure.map_prod_map (gaussianReal M.priorMean M.priorVariance)
      (lg21ContinuousGaussianNoiseLaw M) measurable_id
      (lg21ContinuousGaussianNoiseSplit testFeature).measurable]
    rw [lg21ContinuousGaussianNoiseLaw_map_nonTest_test_eq]
    simp [lg21ContinuousGaussianFullProfilePrimitiveLaw]
  calc
    (lg21ContinuousGaussianAccessPopulationLaw M).map
        (lg21ContinuousPopulationFullPrimitive testFeature) =
      ((lg21ContinuousGaussianAccessPopulationLaw M).map Prod.snd).map
        splitPrimitive := by
          rw [Measure.map_map hsplitPrimitive measurable_snd]
          rfl
    _ = sourcePrimitiveLaw.map splitPrimitive := by
      rw [lg21ContinuousGaussianAccessPopulation_map_student_eq M haccess]
    _ = lg21ContinuousGaussianFullProfilePrimitiveLaw M testFeature := hprimitive

/-- The exact literal joint law of the full non-test observed profile, the
test score, and latent skill in the positive-access population.  This is the
finite-product source law that the remaining multivariate posterior induction
must disintegrate. -/
theorem lg21ContinuousGaussianAccessPopulation_full_base_score_skill_law
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature) :
    (lg21ContinuousGaussianAccessPopulationLaw M).map
      (fun student =>
        ((lg21ContinuousPopulationBase testFeature student,
          lg21ContinuousPopulationFeature testFeature student),
          lg21ContinuousPopulationSkill student)) =
      (lg21ContinuousGaussianFullProfilePrimitiveLaw M testFeature).map
        (fun primitive =>
          (lg21ContinuousGaussianFullProfileObservation testFeature primitive,
            primitive.1)) := by
  have hprimitive := lg21ContinuousGaussianAccessPopulation_full_primitive_law
    M haccess testFeature
  have hpair : Measurable
      (fun primitive : ℝ × ((LG21NonTestFeature Feature testFeature → ℝ) × ℝ) =>
        (lg21ContinuousGaussianFullProfileObservation testFeature primitive,
          primitive.1)) :=
    (measurable_lg21ContinuousGaussianFullProfileObservation testFeature).prodMk measurable_fst
  calc
    (lg21ContinuousGaussianAccessPopulationLaw M).map
        (fun student =>
          ((lg21ContinuousPopulationBase testFeature student,
            lg21ContinuousPopulationFeature testFeature student),
            lg21ContinuousPopulationSkill student)) =
      ((lg21ContinuousGaussianAccessPopulationLaw M).map
        (lg21ContinuousPopulationFullPrimitive testFeature)).map
        (fun primitive =>
          (lg21ContinuousGaussianFullProfileObservation testFeature primitive,
            primitive.1)) := by
          rw [Measure.map_map hpair
            (measurable_lg21ContinuousPopulationFullPrimitive testFeature)]
          rfl
    _ = (lg21ContinuousGaussianFullProfilePrimitiveLaw M testFeature).map
        (fun primitive =>
          (lg21ContinuousGaussianFullProfileObservation testFeature primitive,
            primitive.1)) := by rw [hprimitive]

/-- The actual conditional latent-skill law given the full non-test profile
and test score is the RCD of the explicit finite-product source law.  This
does not yet simplify that RCD to the paper's precision-weighted Gaussian
formula; doing so requires the remaining finite Gaussian update induction. -/
theorem lg21ContinuousGaussianAccessPopulation_condDistrib_skill_given_full_base_score_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature) :
    let law := lg21ContinuousGaussianAccessPopulationLaw M
    let primitiveLaw := lg21ContinuousGaussianFullProfilePrimitiveLaw M testFeature
    let sourceObservation : Bool × (ℝ × (Feature → ℝ)) →
        (LG21NonTestFeature Feature testFeature → ℝ) × ℝ :=
      fun student =>
        (lg21ContinuousPopulationBase testFeature student,
          lg21ContinuousPopulationFeature testFeature student)
    let primitiveObservation :=
      lg21ContinuousGaussianFullProfileObservation (Feature := Feature) testFeature
    letI : IsProbabilityMeasure law :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
    letI : IsFiniteMeasure law := ⟨by simp⟩
    letI : IsProbabilityMeasure primitiveLaw := by
      unfold primitiveLaw lg21ContinuousGaussianFullProfilePrimitiveLaw
        lg21ContinuousGaussianNonTestNoiseLaw
      infer_instance
    letI : IsFiniteMeasure primitiveLaw := ⟨by simp⟩
    condDistrib lg21ContinuousPopulationSkill sourceObservation law =ᵐ[
        law.map sourceObservation]
      condDistrib Prod.fst primitiveObservation primitiveLaw := by
  intro law primitiveLaw sourceObservation primitiveObservation
  letI : IsProbabilityMeasure law := by
    dsimp [law]
    exact lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  letI : IsFiniteMeasure law := ⟨by simp⟩
  letI : IsProbabilityMeasure primitiveLaw := by
    dsimp [primitiveLaw, lg21ContinuousGaussianFullProfilePrimitiveLaw,
      lg21ContinuousGaussianNonTestNoiseLaw]
    infer_instance
  letI : IsFiniteMeasure primitiveLaw := ⟨by simp⟩
  have hskill : Measurable (lg21ContinuousPopulationSkill (Feature := Feature)) := by
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) => student.2.1
    exact measurable_fst.comp measurable_snd
  have hscore : Measurable
      (lg21ContinuousPopulationFeature (Feature := Feature) testFeature) := by
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) =>
      student.2.1 + student.2.2 testFeature
    exact hskill.add ((measurable_pi_apply testFeature).comp
      (measurable_snd.comp measurable_snd))
  have hsourceObservation : Measurable sourceObservation := by
    exact (lg21ContinuousPopulationBase_measurable testFeature).prodMk hscore
  have hprimitiveObservation : Measurable primitiveObservation := by
    exact measurable_lg21ContinuousGaussianFullProfileObservation testFeature
  have hprimitivePair : Measurable
      (fun primitive : ℝ × ((LG21NonTestFeature Feature testFeature → ℝ) × ℝ) =>
        (primitiveObservation primitive, primitive.1)) :=
    hprimitiveObservation.prodMk measurable_fst
  have hsourcePair : Measurable
      (fun student : Bool × (ℝ × (Feature → ℝ)) =>
        (sourceObservation student, lg21ContinuousPopulationSkill student)) :=
    hsourceObservation.prodMk hskill
  have hpair : law.map
      (fun student => (sourceObservation student,
        lg21ContinuousPopulationSkill student)) =
      primitiveLaw.map
        (fun primitive : ℝ × ((LG21NonTestFeature Feature testFeature → ℝ) × ℝ) =>
          (primitiveObservation primitive, primitive.1)) := by
    simpa [law, primitiveLaw, sourceObservation, primitiveObservation] using
      (lg21ContinuousGaussianAccessPopulation_full_base_score_skill_law
        M haccess testFeature)
  have hobservation : law.map sourceObservation =
      primitiveLaw.map primitiveObservation := by
    calc
      law.map sourceObservation = (law.map
          (fun student => (sourceObservation student,
            lg21ContinuousPopulationSkill student))).map Prod.fst := by
        rw [Measure.map_map measurable_fst hsourcePair]
        rfl
      _ = (primitiveLaw.map
          (fun primitive : ℝ × ((LG21NonTestFeature Feature testFeature → ℝ) × ℝ) =>
            (primitiveObservation primitive, primitive.1))).map Prod.fst := by
        rw [hpair]
      _ = primitiveLaw.map primitiveObservation := by
        rw [Measure.map_map measurable_fst hprimitivePair]
        rfl
  apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    hsourceObservation hskill
  calc
    law.map (fun student => (sourceObservation student,
        lg21ContinuousPopulationSkill student)) =
      primitiveLaw.map
        (fun primitive : ℝ × ((LG21NonTestFeature Feature testFeature → ℝ) × ℝ) =>
          (primitiveObservation primitive, primitive.1)) := hpair
    _ = primitiveLaw.map primitiveObservation ⊗ₘ
        condDistrib Prod.fst primitiveObservation primitiveLaw := by
      rw [compProd_map_condDistrib measurable_fst.aemeasurable]
    _ = law.map sourceObservation ⊗ₘ
        condDistrib Prod.fst primitiveObservation primitiveLaw := by
      rw [hobservation]

end

end LG21TestOptionalPolicies

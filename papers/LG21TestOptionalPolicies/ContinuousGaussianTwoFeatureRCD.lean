import AppliedModelingLib.Foundations.Probability.GaussianSignalKernelRCD
import LG21TestOptionalPolicies.ContinuousAccessConditionedPopulation

/-!
# Literal two-feature Gaussian conditional distribution for LG21

This module proves an actual conditional-distribution result for the literal
continuous source population, with one specified non-test feature and the test
score observed.  It is intentionally not a claim about the entire non-test
profile when that profile has more than one coordinate.  The general
finite-profile result needs an induction over the remaining independent
Gaussian coordinates.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

/-- The literal independent noise vector has the expected joint law at any two
distinct feature coordinates. -/
theorem lg21ContinuousGaussianNoiseLaw_two_coordinate_joint
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (baseFeature testFeature : Feature) (hne : baseFeature ≠ testFeature) :
    (lg21ContinuousGaussianNoiseLaw M).map
      (fun noise => (noise baseFeature, noise testFeature)) =
      (gaussianReal 0 (M.noiseVariance baseFeature)).prod
        (gaussianReal 0 (M.noiseVariance testFeature)) := by
  let noiseLaw := lg21ContinuousGaussianNoiseLaw M
  letI : IsProbabilityMeasure noiseLaw := by
    unfold noiseLaw lg21ContinuousGaussianNoiseLaw
    infer_instance
  have hbase : Measurable (Function.eval baseFeature : (Feature → ℝ) → ℝ) :=
    measurable_pi_apply baseFeature
  have htest : Measurable (Function.eval testFeature : (Feature → ℝ) → ℝ) :=
    measurable_pi_apply testFeature
  have hindep : (Function.eval baseFeature : (Feature → ℝ) → ℝ) ⟂ᵢ[noiseLaw]
      (Function.eval testFeature : (Feature → ℝ) → ℝ) := by
    exact (ProbabilityTheory.iIndepFun_pi
      (μ := fun feature => gaussianReal 0 (M.noiseVariance feature))
      (X := fun _ (noise : ℝ) => noise)
      (fun _ => measurable_id.aemeasurable)).indepFun hne
  have hpair : noiseLaw.map
      (fun noise => (noise baseFeature, noise testFeature)) =
      (noiseLaw.map (Function.eval baseFeature)).prod
        (noiseLaw.map (Function.eval testFeature)) := by
    exact (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      hbase.aemeasurable htest.aemeasurable).mp hindep
  change noiseLaw.map
      (fun noise => (noise baseFeature, noise testFeature)) = _
  rw [hpair, lg21ContinuousGaussianNoiseLaw_map_eval_eq M baseFeature,
    lg21ContinuousGaussianNoiseLaw_map_eval_eq M testFeature]

/-- The primitive source population has the product law of latent skill and
two specified independent feature noises. -/
theorem lg21ContinuousGaussianStudentPrimitiveLaw_two_coordinate_joint
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (baseFeature testFeature : Feature) (hne : baseFeature ≠ testFeature) :
    (lg21ContinuousGaussianStudentPrimitiveLaw M).map
      (fun primitive => ((primitive.1, primitive.2 baseFeature), primitive.2 testFeature)) =
      ((gaussianReal M.priorMean M.priorVariance).prod
        (gaussianReal 0 (M.noiseVariance baseFeature))).prod
        (gaussianReal 0 (M.noiseVariance testFeature)) := by
  let prior := gaussianReal M.priorMean M.priorVariance
  let noiseLaw := lg21ContinuousGaussianNoiseLaw M
  let baseNoise := gaussianReal 0 (M.noiseVariance baseFeature)
  let testNoise := gaussianReal 0 (M.noiseVariance testFeature)
  letI : IsProbabilityMeasure noiseLaw := by
    unfold noiseLaw lg21ContinuousGaussianNoiseLaw
    infer_instance
  have hnoise := lg21ContinuousGaussianNoiseLaw_two_coordinate_joint
    M baseFeature testFeature hne
  have hright : (lg21ContinuousGaussianStudentPrimitiveLaw M).map
      (fun primitive => (primitive.1,
        (primitive.2 baseFeature, primitive.2 testFeature))) =
      prior.prod (baseNoise.prod testNoise) := by
    change Measure.map
        (Prod.map id (fun noise => (noise baseFeature, noise testFeature)))
        (prior.prod noiseLaw) = _
    rw [← Measure.map_prod_map prior noiseLaw measurable_id (by fun_prop)]
    rw [hnoise]
    simp [baseNoise, testNoise]
  have hrightMap : Measurable
      (fun primitive : ℝ × (Feature → ℝ) => (primitive.1,
        (primitive.2 baseFeature, primitive.2 testFeature))) := by
    exact measurable_fst.prodMk
      (((measurable_pi_apply baseFeature).comp measurable_snd).prodMk
        ((measurable_pi_apply testFeature).comp measurable_snd))
  calc
    (lg21ContinuousGaussianStudentPrimitiveLaw M).map
        (fun primitive => ((primitive.1, primitive.2 baseFeature), primitive.2 testFeature)) =
      ((lg21ContinuousGaussianStudentPrimitiveLaw M).map
        (fun primitive => (primitive.1,
          (primitive.2 baseFeature, primitive.2 testFeature)))).map
        MeasurableEquiv.prodAssoc.symm := by
          rw [Measure.map_map (MeasurableEquiv.measurable _) hrightMap]
          rfl
    _ = (prior.prod (baseNoise.prod testNoise)).map
        MeasurableEquiv.prodAssoc.symm := by rw [hright]
    _ = (prior.prod baseNoise).prod testNoise := by
      rw [← Measure.prodAssoc_prod]
      simp

/-- Conditioning on positive access does not change the literal joint law of
latent skill and two feature noises. -/
theorem lg21ContinuousGaussianAccessPopulation_two_coordinate_joint
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (baseFeature testFeature : Feature) (hne : baseFeature ≠ testFeature) :
    (lg21ContinuousGaussianAccessPopulationLaw M).map
      (fun student =>
        ((lg21ContinuousPopulationSkill student,
          lg21ContinuousPopulationNoise baseFeature student),
          lg21ContinuousPopulationNoise testFeature student)) =
      ((gaussianReal M.priorMean M.priorVariance).prod
        (gaussianReal 0 (M.noiseVariance baseFeature))).prod
        (gaussianReal 0 (M.noiseVariance testFeature)) := by
  let primitiveMap : ℝ × (Feature → ℝ) → (ℝ × ℝ) × ℝ :=
    fun primitive => ((primitive.1, primitive.2 baseFeature), primitive.2 testFeature)
  have hprimitiveMap : Measurable primitiveMap := by
    change Measurable
      (fun primitive : ℝ × (Feature → ℝ) => ((primitive.1,
        primitive.2 baseFeature), primitive.2 testFeature))
    have hbaseNoise : Measurable
        (fun primitive : ℝ × (Feature → ℝ) => primitive.2 baseFeature) :=
      (measurable_pi_apply baseFeature).comp measurable_snd
    have htestNoise : Measurable
        (fun primitive : ℝ × (Feature → ℝ) => primitive.2 testFeature) :=
      (measurable_pi_apply testFeature).comp measurable_snd
    exact (measurable_fst.prodMk hbaseNoise).prodMk htestNoise
  have hprimitive :=
    lg21ContinuousGaussianStudentPrimitiveLaw_two_coordinate_joint
      M baseFeature testFeature hne
  calc
    (lg21ContinuousGaussianAccessPopulationLaw M).map
        (fun student =>
          ((lg21ContinuousPopulationSkill student,
            lg21ContinuousPopulationNoise baseFeature student),
            lg21ContinuousPopulationNoise testFeature student)) =
      (lg21ContinuousGaussianAccessPopulationLaw M).map
        (primitiveMap ∘ Prod.snd) := by rfl
    _ = ((lg21ContinuousGaussianAccessPopulationLaw M).map Prod.snd).map
        primitiveMap := (Measure.map_map hprimitiveMap measurable_snd).symm
    _ = (lg21ContinuousGaussianStudentPrimitiveLaw M).map primitiveMap := by
      rw [lg21ContinuousGaussianAccessPopulation_map_student_eq M haccess]
    _ = _ := hprimitive

private theorem gaussian_two_signal_sequential_law
    (priorMean priorVariance baseNoiseVariance scoreNoiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hbaseNoiseVariance : 0 < baseNoiseVariance) :
    let baseLaw := gaussianReal priorMean (priorVariance + baseNoiseVariance).toNNReal
    let posteriorMean : ℝ → ℝ := fun base =>
      AppliedModelingLib.Probability.gaussianSignalWeight priorVariance baseNoiseVariance * base +
        AppliedModelingLib.Probability.gaussianSignalPriorWeight priorVariance baseNoiseVariance * priorMean
    let posteriorVariance : ℝ :=
      priorVariance * baseNoiseVariance / (priorVariance + baseNoiseVariance)
    ((AppliedModelingLib.Probability.gaussianSignalPair priorMean priorVariance baseNoiseVariance).prod
      (gaussianReal 0 scoreNoiseVariance.toNNReal)).map
        (fun primitive : (ℝ × ℝ) × ℝ =>
          ((primitive.1.1 + primitive.1.2,
            primitive.1.1 + primitive.2), primitive.1.1)) =
      AppliedModelingLib.Probability.gaussianSignalBaseScoreLatentLaw
        baseLaw posteriorMean (by fun_prop)
        posteriorVariance scoreNoiseVariance := by
  intro baseLaw posteriorMean posteriorVariance
  have hposteriorMean : Measurable posteriorMean := by
    dsimp [posteriorMean]
    fun_prop
  let firstPosterior : Kernel ℝ ℝ :=
    AppliedModelingLib.Probability.gaussianSignalPosteriorKernel
      priorMean priorVariance baseNoiseVariance
  let posteriorLocation : Kernel ℝ ℝ :=
    AppliedModelingLib.Probability.gaussianLocationKernel
      posteriorMean hposteriorMean posteriorVariance.toNNReal
  letI : IsMarkovKernel posteriorLocation :=
    AppliedModelingLib.Probability.gaussianLocationKernel_isMarkov
      posteriorMean hposteriorMean posteriorVariance.toNNReal
  let firstScoreLatent : ℝ × ℝ → ℝ × ℝ :=
    fun pair => (pair.1 + pair.2, pair.1)
  let scoreLatent : ℝ × ℝ → ℝ × ℝ :=
    fun pair => (pair.1 + pair.2, pair.1)
  let repackage : ((ℝ × ℝ) × ℝ) → ((ℝ × ℝ) × ℝ) :=
    fun primitive => ((primitive.1.1 + primitive.1.2,
      primitive.1.1 + primitive.2), primitive.1.1)
  have hfirstScoreLatent : Measurable firstScoreLatent := by
    dsimp [firstScoreLatent]
    fun_prop
  have hscoreLatent : Measurable scoreLatent := by
    dsimp [scoreLatent]
    fun_prop
  have hfirstPosterior : firstPosterior = posteriorLocation := by
    ext base event hevent
    rw [AppliedModelingLib.Probability.gaussianSignalPosteriorKernel_apply,
      AppliedModelingLib.Probability.gaussianLocationKernel_apply]
  have hfirst :
      (AppliedModelingLib.Probability.gaussianSignalPair
        priorMean priorVariance baseNoiseVariance).map firstScoreLatent =
        baseLaw ⊗ₘ posteriorLocation := by
    calc
      (AppliedModelingLib.Probability.gaussianSignalPair
        priorMean priorVariance baseNoiseVariance).map firstScoreLatent =
          baseLaw ⊗ₘ firstPosterior := by
            change (AppliedModelingLib.Probability.gaussianSignalPair
              priorMean priorVariance baseNoiseVariance).map
              (fun pair : ℝ × ℝ => (pair.1 + pair.2, pair.1)) =
              baseLaw ⊗ₘ AppliedModelingLib.Probability.gaussianSignalPosteriorKernel
                priorMean priorVariance baseNoiseVariance
            exact AppliedModelingLib.Probability.gaussianSignalPair_score_latent_joint_factorization
              priorMean priorVariance baseNoiseVariance hpriorVariance hbaseNoiseVariance
      _ = baseLaw ⊗ₘ posteriorLocation := by rw [hfirstPosterior]
  let firstJoint := AppliedModelingLib.Probability.gaussianSignalPair
    priorMean priorVariance baseNoiseVariance
  let scoreNoise := gaussianReal 0 scoreNoiseVariance.toNNReal
  have hfirstJointScoreNoise :
      (firstJoint.prod scoreNoise).map repackage =
        ((firstJoint.map firstScoreLatent).prod scoreNoise).map
          (fun primitive : (ℝ × ℝ) × ℝ =>
            ((primitive.1.1, primitive.1.2 + primitive.2), primitive.1.2)) := by
    let follow : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ :=
      fun primitive => ((primitive.1.1, primitive.1.2 + primitive.2), primitive.1.2)
    have hfollow : Measurable follow := by
      dsimp [follow]
      fun_prop
    calc
      (firstJoint.prod scoreNoise).map repackage =
          ((firstJoint.prod scoreNoise).map
            (Prod.map firstScoreLatent id)).map follow := by
              rw [Measure.map_map hfollow (by fun_prop)]
              rfl
      _ = ((firstJoint.map firstScoreLatent).prod
          (scoreNoise.map id)).map follow := by
            rw [← Measure.map_prod_map firstJoint scoreNoise
              hfirstScoreLatent measurable_id]
      _ = ((firstJoint.map firstScoreLatent).prod scoreNoise).map follow := by simp
  have hsequential :
      ((baseLaw ⊗ₘ posteriorLocation).prod scoreNoise).map
        (fun primitive : (ℝ × ℝ) × ℝ =>
          ((primitive.1.1, primitive.1.2 + primitive.2), primitive.1.2)) =
        AppliedModelingLib.Probability.gaussianSignalBaseScoreLatentLaw
          baseLaw posteriorMean hposteriorMean
          posteriorVariance scoreNoiseVariance := by
    let follow : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ :=
      fun primitive => ((primitive.1.1, primitive.1.2 + primitive.2), primitive.1.2)
    have hfollow : Measurable follow := by
      dsimp [follow]
      fun_prop
    let stage : ℝ × ℝ → ℝ × ℝ := scoreLatent
    have hstage : Measurable stage := hscoreLatent
    change ((baseLaw ⊗ₘ posteriorLocation).prod scoreNoise).map follow = _
    unfold AppliedModelingLib.Probability.gaussianSignalBaseScoreLatentLaw
    unfold AppliedModelingLib.Probability.gaussianSignalJointKernel
    rw [← Measure.compProd_const]
    rw [← Measure.compProd_assoc]
    rw [Measure.map_map hfollow (MeasurableEquiv.measurable _)]
    have hfun : follow ∘ MeasurableEquiv.prodAssoc.symm =
        MeasurableEquiv.prodAssoc.symm ∘ Prod.map id stage := by
      funext primitive
      rfl
    rw [hfun]
    rw [← Measure.map_map (MeasurableEquiv.measurable _) (by fun_prop)]
    rw [← Measure.compProd_map hstage]
    have hkernel :
        posteriorLocation ⊗ₖ Kernel.const (ℝ × ℝ) scoreNoise =
          posteriorLocation ×ₖ Kernel.const ℝ scoreNoise := by
      ext base event hevent
      rw [Kernel.compProd_apply hevent, Kernel.prod_apply,
        Measure.prod_apply hevent]
      simp only [Kernel.const_apply]
    rw [hkernel]
  change (firstJoint.prod scoreNoise).map repackage = _
  rw [hfirstJointScoreNoise, hfirst]
  exact hsequential

/-- The source's exact joint law for one specified non-test feature, the test
score, and latent skill.  This is the literal two-observation instance of the
source model, not an assertion about all non-test features at once. -/
theorem lg21ContinuousGaussianAccessPopulation_single_base_score_skill_law
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (baseFeature testFeature : Feature) (hne : baseFeature ≠ testFeature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hbaseNoiseVariance : 0 < (M.noiseVariance baseFeature : ℝ)) :
    let baseLaw := gaussianReal M.priorMean
      ((M.priorVariance : ℝ) + (M.noiseVariance baseFeature : ℝ)).toNNReal
    let posteriorMean : ℝ → ℝ := fun base =>
      AppliedModelingLib.Probability.gaussianSignalWeight
          (M.priorVariance : ℝ) (M.noiseVariance baseFeature : ℝ) * base +
        AppliedModelingLib.Probability.gaussianSignalPriorWeight
          (M.priorVariance : ℝ) (M.noiseVariance baseFeature : ℝ) * M.priorMean
    let posteriorVariance : ℝ :=
      (M.priorVariance : ℝ) * (M.noiseVariance baseFeature : ℝ) /
        ((M.priorVariance : ℝ) + (M.noiseVariance baseFeature : ℝ))
    (lg21ContinuousGaussianAccessPopulationLaw M).map
      (fun student =>
        ((lg21ContinuousPopulationFeature baseFeature student,
          lg21ContinuousPopulationFeature testFeature student),
          lg21ContinuousPopulationSkill student)) =
      AppliedModelingLib.Probability.gaussianSignalBaseScoreLatentLaw
        baseLaw posteriorMean (by fun_prop)
        posteriorVariance (M.noiseVariance testFeature : ℝ) := by
  intro baseLaw posteriorMean posteriorVariance
  let primitiveTriple : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ :=
    fun primitive => ((primitive.1.1 + primitive.1.2,
      primitive.1.1 + primitive.2), primitive.1.1)
  have hprimitiveTriple : Measurable primitiveTriple := by
    dsimp [primitiveTriple]
    fun_prop
  have hraw := lg21ContinuousGaussianAccessPopulation_two_coordinate_joint
    M haccess baseFeature testFeature hne
  have hskill : Measurable (lg21ContinuousPopulationSkill (Feature := Feature)) := by
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) => student.2.1
    exact measurable_fst.comp measurable_snd
  have hbaseNoise : Measurable
      (lg21ContinuousPopulationNoise (Feature := Feature) baseFeature) := by
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) => student.2.2 baseFeature
    exact (measurable_pi_apply baseFeature).comp (measurable_snd.comp measurable_snd)
  have htestNoise : Measurable
      (lg21ContinuousPopulationNoise (Feature := Feature) testFeature) := by
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) => student.2.2 testFeature
    exact (measurable_pi_apply testFeature).comp (measurable_snd.comp measurable_snd)
  have hrawMap : Measurable
      (fun student : Bool × (ℝ × (Feature → ℝ)) =>
        ((lg21ContinuousPopulationSkill student,
          lg21ContinuousPopulationNoise baseFeature student),
          lg21ContinuousPopulationNoise testFeature student)) :=
    (hskill.prodMk hbaseNoise).prodMk htestNoise
  calc
    (lg21ContinuousGaussianAccessPopulationLaw M).map
        (fun student =>
          ((lg21ContinuousPopulationFeature baseFeature student,
            lg21ContinuousPopulationFeature testFeature student),
            lg21ContinuousPopulationSkill student)) =
      ((lg21ContinuousGaussianAccessPopulationLaw M).map
        (fun student =>
          ((lg21ContinuousPopulationSkill student,
            lg21ContinuousPopulationNoise baseFeature student),
            lg21ContinuousPopulationNoise testFeature student))).map
        primitiveTriple := by
          rw [Measure.map_map hprimitiveTriple hrawMap]
          rfl
    _ = (((gaussianReal M.priorMean M.priorVariance).prod
        (gaussianReal 0 (M.noiseVariance baseFeature))).prod
        (gaussianReal 0 (M.noiseVariance testFeature))).map
        primitiveTriple := by rw [hraw]
    _ = AppliedModelingLib.Probability.gaussianSignalBaseScoreLatentLaw
        baseLaw posteriorMean (by fun_prop)
        posteriorVariance (M.noiseVariance testFeature : ℝ) := by
      dsimp [baseLaw, posteriorMean, posteriorVariance]
      simpa [AppliedModelingLib.Probability.gaussianSignalPair, primitiveTriple,
        Real.toNNReal_coe] using
        gaussian_two_signal_sequential_law M.priorMean
          (M.priorVariance : ℝ) (M.noiseVariance baseFeature : ℝ)
          (M.noiseVariance testFeature : ℝ)
          hpriorVariance hbaseNoiseVariance

/--
For the literal access-conditioned source population, the conditional latent
skill law given one named non-test feature and the test score is the sequential
Gaussian posterior, almost everywhere in the actual two-coordinate observation
marginal.  This is deliberately narrower than conditioning on the full
non-test feature profile in the paper when that profile has multiple
coordinates.
-/
theorem lg21ContinuousGaussianAccessPopulation_condDistrib_skill_given_single_base_score_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (baseFeature testFeature : Feature) (hne : baseFeature ≠ testFeature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hbaseNoiseVariance : 0 < (M.noiseVariance baseFeature : ℝ))
    (hscoreNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ)) :
    let law := lg21ContinuousGaussianAccessPopulationLaw M
    let posteriorMean : ℝ → ℝ := fun base =>
      AppliedModelingLib.Probability.gaussianSignalWeight
          (M.priorVariance : ℝ) (M.noiseVariance baseFeature : ℝ) * base +
        AppliedModelingLib.Probability.gaussianSignalPriorWeight
          (M.priorVariance : ℝ) (M.noiseVariance baseFeature : ℝ) * M.priorMean
    let posteriorVariance : ℝ :=
      (M.priorVariance : ℝ) * (M.noiseVariance baseFeature : ℝ) /
        ((M.priorVariance : ℝ) + (M.noiseVariance baseFeature : ℝ))
    let posteriorKernel := AppliedModelingLib.Probability.gaussianSignalPosteriorBaseKernel
      posteriorMean (by fun_prop)
      posteriorVariance (M.noiseVariance testFeature : ℝ)
    letI : IsProbabilityMeasure law :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
    letI : IsFiniteMeasure law := ⟨by simp⟩
    condDistrib lg21ContinuousPopulationSkill
      (fun student =>
        (lg21ContinuousPopulationFeature baseFeature student,
          lg21ContinuousPopulationFeature testFeature student)) law =ᵐ[
        law.map (fun student =>
          (lg21ContinuousPopulationFeature baseFeature student,
            lg21ContinuousPopulationFeature testFeature student))]
      posteriorKernel := by
  intro law posteriorMean posteriorVariance posteriorKernel
  letI : IsProbabilityMeasure law :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  letI : IsFiniteMeasure law := ⟨by simp⟩
  let baseLaw := gaussianReal M.priorMean
    ((M.priorVariance : ℝ) + (M.noiseVariance baseFeature : ℝ)).toNNReal
  have hskill : Measurable (lg21ContinuousPopulationSkill (Feature := Feature)) := by
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) => student.2.1
    exact measurable_fst.comp measurable_snd
  have hbase : Measurable
      (lg21ContinuousPopulationFeature (Feature := Feature) baseFeature) := by
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) =>
      student.2.1 + student.2.2 baseFeature
    exact hskill.add ((measurable_pi_apply baseFeature).comp
      (measurable_snd.comp measurable_snd))
  have hscore : Measurable
      (lg21ContinuousPopulationFeature (Feature := Feature) testFeature) := by
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) =>
      student.2.1 + student.2.2 testFeature
    exact hskill.add ((measurable_pi_apply testFeature).comp
      (measurable_snd.comp measurable_snd))
  let observation : Bool × (ℝ × (Feature → ℝ)) → ℝ × ℝ :=
    fun student =>
      (lg21ContinuousPopulationFeature baseFeature student,
        lg21ContinuousPopulationFeature testFeature student)
  have hobservation : Measurable observation := hbase.prodMk hscore
  have hposteriorMean : Measurable posteriorMean := by
    dsimp [posteriorMean]
    fun_prop
  letI : IsMarkovKernel posteriorKernel := by
    dsimp [posteriorKernel]
    exact AppliedModelingLib.Probability.gaussianSignalPosteriorBaseKernel_isMarkov
      posteriorMean hposteriorMean posteriorVariance
        (M.noiseVariance testFeature : ℝ)
  let scoreKernel : Kernel ℝ ℝ :=
    AppliedModelingLib.Probability.gaussianLocationKernel posteriorMean hposteriorMean
      (posteriorVariance + (M.noiseVariance testFeature : ℝ)).toNNReal
  letI : IsMarkovKernel scoreKernel :=
    AppliedModelingLib.Probability.gaussianLocationKernel_isMarkov posteriorMean hposteriorMean
      (posteriorVariance + (M.noiseVariance testFeature : ℝ)).toNNReal
  have hposteriorVariance : 0 < posteriorVariance := by
    dsimp [posteriorVariance]
    exact div_pos (mul_pos hpriorVariance hbaseNoiseVariance)
      (add_pos hpriorVariance hbaseNoiseVariance)
  have hsource : law.map
      (fun student =>
        ((lg21ContinuousPopulationFeature baseFeature student,
          lg21ContinuousPopulationFeature testFeature student),
          lg21ContinuousPopulationSkill student)) =
      AppliedModelingLib.Probability.gaussianSignalBaseScoreLatentLaw
        baseLaw posteriorMean hposteriorMean
        posteriorVariance (M.noiseVariance testFeature : ℝ) := by
    simpa [law, baseLaw, posteriorMean, posteriorVariance] using
      (lg21ContinuousGaussianAccessPopulation_single_base_score_skill_law
        M haccess baseFeature testFeature hne hpriorVariance hbaseNoiseVariance)
  have hfactor := AppliedModelingLib.Probability.gaussianSignalBaseScoreLatentLaw_factorization
    baseLaw posteriorMean hposteriorMean posteriorVariance
      (M.noiseVariance testFeature : ℝ)
      hposteriorVariance hscoreNoiseVariance
  have hscoreKernel : scoreKernel =
      AppliedModelingLib.Probability.gaussianLocationKernel posteriorMean hposteriorMean
        (posteriorVariance + (M.noiseVariance testFeature : ℝ)).toNNReal := rfl
  have hposteriorKernel : posteriorKernel =
      AppliedModelingLib.Probability.gaussianSignalPosteriorBaseKernel
        posteriorMean hposteriorMean
        posteriorVariance (M.noiseVariance testFeature : ℝ) := by
    rfl
  have hobsMarginal : law.map observation = baseLaw ⊗ₘ scoreKernel := by
    calc
      law.map observation = (law.map
          (fun student => (observation student,
            lg21ContinuousPopulationSkill student))).map Prod.fst := by
              rw [Measure.map_map measurable_fst (hobservation.prodMk hskill)]
              rfl
      _ = (AppliedModelingLib.Probability.gaussianSignalBaseScoreLatentLaw
          baseLaw posteriorMean hposteriorMean posteriorVariance
            (M.noiseVariance testFeature : ℝ)).map Prod.fst := by
              rw [show (fun student : Bool × (ℝ × (Feature → ℝ)) =>
                (observation student, lg21ContinuousPopulationSkill student)) =
                (fun student =>
                  ((lg21ContinuousPopulationFeature baseFeature student,
                    lg21ContinuousPopulationFeature testFeature student),
                    lg21ContinuousPopulationSkill student)) by rfl,
                hsource]
      _ = (baseLaw ⊗ₘ scoreKernel) := by
              rw [hfactor, hscoreKernel]
              exact Measure.fst_compProd _ _
  have hjoint : law.map
      (fun student => (observation student,
        lg21ContinuousPopulationSkill student)) =
      law.map observation ⊗ₘ posteriorKernel := by
    calc
      law.map (fun student => (observation student,
          lg21ContinuousPopulationSkill student)) =
        AppliedModelingLib.Probability.gaussianSignalBaseScoreLatentLaw
          baseLaw posteriorMean hposteriorMean posteriorVariance
            (M.noiseVariance testFeature : ℝ) := by
              rw [show (fun student : Bool × (ℝ × (Feature → ℝ)) =>
                (observation student, lg21ContinuousPopulationSkill student)) =
                (fun student =>
                  ((lg21ContinuousPopulationFeature baseFeature student,
                    lg21ContinuousPopulationFeature testFeature student),
                    lg21ContinuousPopulationSkill student)) by rfl,
                hsource]
      _ = baseLaw ⊗ₘ scoreKernel ⊗ₘ posteriorKernel := by
              rw [hfactor, hscoreKernel, hposteriorKernel]
      _ = law.map observation ⊗ₘ posteriorKernel := by rw [hobsMarginal]
  change condDistrib lg21ContinuousPopulationSkill observation law =ᵐ[
    law.map observation] posteriorKernel
  exact condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    hobservation hskill hjoint

end

end LG21TestOptionalPolicies

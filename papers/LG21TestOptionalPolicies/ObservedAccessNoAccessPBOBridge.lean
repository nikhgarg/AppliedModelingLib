import LG21TestOptionalPolicies.HiddenAccessTheorem31ComponentConditionalBridge
import LG21TestOptionalPolicies.Section4LiteralGaussianSourceBridge

/-!
# Literal no-access PBO bridge for LG21 observed access

This module records the no-access side of Proposition 4.3 at its natural
measure-theoretic scope.  A no-access PBO is an a.e. conditional mean of
latent skill given the public non-test base profile.  The resulting equality
with the Gaussian base mean is derived from the literal base/skill source
factorization, rather than assumed as an output-law or fairness conclusion.

Regular conditional distributions are only canonical almost everywhere in the
base marginal, so no statement here assigns a value to a null base fibre.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib AppliedModelingLib.Probability MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

/-- An RCD-mean no-access output equals the base-indexed Gaussian mean whenever
the actual base/skill law has the displayed source-derived factorization. -/
theorem lg21ObservedAccess_noAccessPBO_eq_baseMean_ae_of_joint_factorization
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (law : Measure Omega) [IsFiniteMeasure law]
    (base : Omega -> Base) (skill noAccessOutput : Omega -> ℝ)
    (hbase : Measurable base) (hskill : Measurable skill)
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance : NNReal)
    (hfactor : law.map (fun omega => (base omega, skill omega)) =
      law.map base ⊗ₘ gaussianLocationKernel baseMean hbaseMean baseVariance)
    (hpbo : noAccessOutput =ᵐ[law]
      fun omega => ∫ latentSkill, latentSkill ∂
        condDistrib skill base law (base omega)) :
    noAccessOutput =ᵐ[law] fun omega => baseMean (base omega) := by
  let skillKernel : Kernel Base ℝ :=
    gaussianLocationKernel baseMean hbaseMean baseVariance
  letI : IsMarkovKernel skillKernel :=
    gaussianLocationKernel_isMarkov baseMean hbaseMean baseVariance
  have hcondDistrib : condDistrib skill base law =ᵐ[law.map base] skillKernel := by
    exact condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
      hbase hskill (by simpa [skillKernel] using hfactor)
  have hcondAt : ∀ᵐ omega ∂law,
      condDistrib skill base law (base omega) = skillKernel (base omega) := by
    exact ae_of_ae_map hbase.aemeasurable hcondDistrib
  filter_upwards [hpbo, hcondAt] with omega hpboAt hcondAt
  rw [hpboAt, hcondAt]
  change (∫ latentSkill, latentSkill ∂
      gaussianLocationKernel baseMean hbaseMean baseVariance (base omega)) =
    baseMean (base omega)
  rw [gaussianLocationKernel_apply]
  exact integral_id_gaussianReal

/-- An output that is almost everywhere a deterministic function of the
public base profile has that deterministic regular conditional output kernel.
This is a generic RCD transport, independent of any paper-specific function
name. -/
theorem conditional_output_kernel_eq_deterministic_of_ae_baseMean
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (law : Measure Omega) [IsFiniteMeasure law]
    (base : Omega -> Base) (output : Omega -> ℝ)
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (houtput : output =ᵐ[law] fun omega => baseMean (base omega)) :
    condDistrib output base law =ᵐ[law.map base]
      Kernel.deterministic baseMean hbaseMean := by
  rw [condDistrib_congr_left houtput]
  simpa [Function.comp_def] using
    (condDistrib_comp_self (μ := law) base hbaseMean)

/-- The literal no-access component has the raw base/skill factorization
needed by the semantic PBO bridge.  This is a source-population calculation;
it does not assume any policy output equality. -/
theorem lg21ContinuousGaussianNoAccessPopulation_base_skill_factorization
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ)
    (hfullBaseFactorization :
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
        baseLaw ⊗ₘ gaussianLocationKernel
          baseMean hbaseMean baseVariance.toNNReal) :
    (lg21ContinuousGaussianNoAccessPopulationLaw M).map
        (fun student =>
          (lg21ContinuousPopulationBase testFeature student,
            lg21ContinuousPopulationSkill student)) =
      baseLaw ⊗ₘ gaussianLocationKernel
        baseMean hbaseMean baseVariance.toNNReal := by
  calc
    (lg21ContinuousGaussianNoAccessPopulationLaw M).map
        (fun student =>
          (lg21ContinuousPopulationBase testFeature student,
            lg21ContinuousPopulationSkill student)) =
        lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature := by
          simpa [lg21ContinuousGaussianNoAccessPopulationLaw,
            lg21HiddenAccessNoAccessLaw, lg21HiddenAccessNoAccessEvent,
            lg21HiddenAccessBaseSkillObservation,
            lg21ContinuousPopulationBase] using
          (lg21HiddenAccessNoAccessLaw_base_skill_law M hnoAccess testFeature)
    _ = baseLaw ⊗ₘ gaussianLocationKernel
        baseMean hbaseMean baseVariance.toNNReal := hfullBaseFactorization

/-- A semantic no-access PBO for the literal observed-access source: the
realized output is the regular conditional mean of latent skill given exactly
the school's public non-test base profile.  The finite/probability instances
come from the positive literal no-access source population, not from an
additional model assumption. -/
def LG21ContinuousGaussianNoAccessPopulationPBO
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (noAccessOutput : Bool × (ℝ × (Feature -> ℝ)) -> ℝ) : Prop :=
  let law := lg21ContinuousGaussianNoAccessPopulationLaw M
  let base := lg21ContinuousPopulationBase testFeature
  let skill : Bool × (ℝ × (Feature -> ℝ)) -> ℝ :=
    lg21ContinuousPopulationSkill
  letI : IsProbabilityMeasure law :=
    lg21ContinuousGaussianNoAccessPopulationLaw_isProbability M hnoAccess
  letI : IsFiniteMeasure law := ⟨by simp⟩
  noAccessOutput =ᵐ[law]
    fun student => ∫ latentSkill, latentSkill ∂
      condDistrib skill base law (base student)

/-- Under the literal finite Gaussian source factorization, any semantic
no-access PBO is almost everywhere the posterior base mean. -/
theorem lg21ContinuousGaussianNoAccessPopulation_pbo_eq_baseMean_ae_of_literalFactorization
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ)
    (hfullBaseFactorization :
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
        baseLaw ⊗ₘ gaussianLocationKernel
          baseMean hbaseMean baseVariance.toNNReal)
    (noAccessOutput : Bool × (ℝ × (Feature -> ℝ)) -> ℝ)
    (hpbo : LG21ContinuousGaussianNoAccessPopulationPBO
      M hnoAccess testFeature noAccessOutput) :
    noAccessOutput =ᵐ[lg21ContinuousGaussianNoAccessPopulationLaw M]
      fun student => baseMean (lg21ContinuousPopulationBase testFeature student) := by
  let law := lg21ContinuousGaussianNoAccessPopulationLaw M
  let base := lg21ContinuousPopulationBase testFeature
  let skill : Bool × (ℝ × (Feature -> ℝ)) -> ℝ :=
    lg21ContinuousPopulationSkill
  letI : IsProbabilityMeasure law :=
    lg21ContinuousGaussianNoAccessPopulationLaw_isProbability M hnoAccess
  letI : IsFiniteMeasure law := ⟨by simp⟩
  letI : IsMarkovKernel (gaussianLocationKernel
      baseMean hbaseMean baseVariance.toNNReal) :=
    gaussianLocationKernel_isMarkov baseMean hbaseMean baseVariance.toNNReal
  have hbase : Measurable base :=
    lg21ContinuousPopulationBase_measurable testFeature
  have hskill : Measurable skill := by
    change Measurable fun student : Bool × (ℝ × (Feature -> ℝ)) => student.2.1
    exact measurable_fst.comp measurable_snd
  have hfactor : law.map (fun student => (base student, skill student)) =
      law.map base ⊗ₘ gaussianLocationKernel
        baseMean hbaseMean baseVariance.toNNReal := by
    have hpair := lg21ContinuousGaussianNoAccessPopulation_base_skill_factorization
      M hnoAccess testFeature baseLaw baseMean hbaseMean baseVariance
      hfullBaseFactorization
    have hbaseLaw : law.map base = baseLaw := by
      calc
        law.map base = (law.map (fun student =>
            (base student, skill student))).map Prod.fst := by
              rw [Measure.map_map measurable_fst (hbase.prodMk hskill)]
              rfl
        _ = (baseLaw ⊗ₘ gaussianLocationKernel
            baseMean hbaseMean baseVariance.toNNReal).map Prod.fst := by
              simpa [law, base, skill] using congrArg (fun measure =>
                measure.map Prod.fst) hpair
        _ = baseLaw := Measure.fst_compProd _ _
    rw [hbaseLaw]
    simpa [law, base, skill] using hpair
  change noAccessOutput =ᵐ[law]
    fun student => ∫ latentSkill, latentSkill ∂
      condDistrib skill base law (base student) at hpbo
  simpa [law, base] using
    (lg21ObservedAccess_noAccessPBO_eq_baseMean_ae_of_joint_factorization
      law base skill noAccessOutput hbase hskill baseMean hbaseMean
      baseVariance.toNNReal hfactor hpbo)

/-- The semantic no-access PBO has the deterministic base-mean conditional
output kernel under the literal source factorization.  Equality is only
almost everywhere in the actual no-access base marginal. -/
theorem lg21ContinuousGaussianNoAccessPopulation_pbo_conditionalKernel_eq_baseMean
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ)
    (hfullBaseFactorization :
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
        baseLaw ⊗ₘ gaussianLocationKernel
          baseMean hbaseMean baseVariance.toNNReal)
    (noAccessOutput : Bool × (ℝ × (Feature -> ℝ)) -> ℝ)
    (hpbo : LG21ContinuousGaussianNoAccessPopulationPBO
      M hnoAccess testFeature noAccessOutput) :
    let law := lg21ContinuousGaussianNoAccessPopulationLaw M
    let base := lg21ContinuousPopulationBase testFeature
    letI : IsProbabilityMeasure law :=
      lg21ContinuousGaussianNoAccessPopulationLaw_isProbability M hnoAccess
    letI : IsFiniteMeasure law := ⟨by simp⟩
    condDistrib noAccessOutput base law =ᵐ[law.map base]
      Kernel.deterministic baseMean hbaseMean := by
  intro law base
  letI : IsProbabilityMeasure law :=
    lg21ContinuousGaussianNoAccessPopulationLaw_isProbability M hnoAccess
  letI : IsFiniteMeasure law := ⟨by simp⟩
  have hbase : Measurable base :=
    lg21ContinuousPopulationBase_measurable testFeature
  have houtput : noAccessOutput =ᵐ[law]
      fun student => baseMean (base student) := by
    simpa [law, base] using
      (lg21ContinuousGaussianNoAccessPopulation_pbo_eq_baseMean_ae_of_literalFactorization
        M hnoAccess testFeature baseLaw baseMean hbaseMean baseVariance
        hfullBaseFactorization noAccessOutput hpbo)
  simpa [law, base] using
    (conditional_output_kernel_eq_deterministic_of_ae_baseMean
      law base noAccessOutput baseMean hbaseMean houtput)

end

end LG21TestOptionalPolicies

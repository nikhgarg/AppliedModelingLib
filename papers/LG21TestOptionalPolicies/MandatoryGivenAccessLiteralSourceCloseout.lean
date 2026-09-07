import LG21TestOptionalPolicies.MandatoryGivenAccessPopulationBehavior
import LG21TestOptionalPolicies.Section4LiteralGaussianSourceBridge

/-!
# Literal mandatory-given-access source endpoint for LG21

The mandatory protocol does not need an off-path PBO argument: source
feasibility itself fixes each access student's action.  This module records
that behavioral fact alongside the Gaussian source experiment used by
Definition 6 and Theorem 4.4.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

/-- The direct literal-source endpoint for the mandatory-given-access
protocol.  The Gaussian experiment is derived from the same finite source
population; it is not supplied as an unrelated policy kernel. -/
def LG21MandatoryGivenAccessLiteralSourceCloseout
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (testFeature : Feature)
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (action : Bool × (ℝ × (Feature → ℝ)) → LG21AccessAction) : Prop :=
  (∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw M,
      action student = LG21AccessAction.takeAndReport) ∧
  ∃ (baseLaw : Measure (LG21NonTestFeature Feature testFeature → ℝ))
    (baseMean : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ)
    (baseVariance : ℝ) (baseMean_measurable : Measurable baseMean)
    (baseLaw_isProbability : IsProbabilityMeasure baseLaw)
    (baseVariance_pos : 0 < baseVariance),
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
        baseLaw ⊗ₘ AppliedModelingLib.Probability.gaussianLocationKernel
          baseMean baseMean_measurable baseVariance.toNNReal ∧
      (letI : IsProbabilityMeasure baseLaw := baseLaw_isProbability
       let S : LG21GaussianPBOResamplingSource
          (LG21NonTestFeature Feature testFeature → ℝ) :=
        { baseLaw := baseLaw
          baseLaw_isProbability := baseLaw_isProbability
          posteriorBaseMean := baseMean
          posteriorBaseMean_measurable := baseMean_measurable
          posteriorBaseVariance := baseVariance.toNNReal
          posteriorBaseVariance_pos := by
            rw [NNReal.coe_pos, Real.toNNReal_pos]
            exact baseVariance_pos
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
            Measure.bind (noAccessLaw.map
              (lg21ContinuousPopulationBase testFeature))
              (lg21D6NoAccessResamplingEstimateKernel S))

/-- Source feasibility and the finite Gaussian product model give the full
mandatory protocol endpoint.  No equilibrium-consistency placeholder or
off-path action value appears in the statement. -/
theorem lg21_mandatoryGivenAccess_literal_source_closeout
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false})
    (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (action : Bool × (ℝ × (Feature → ℝ)) → LG21AccessAction)
    (hfeasible : ∀ student,
      LG21RequirementPolicy.feasibleAction
        LG21RequirementPolicy.reportRequiredGivenAccess
        (lg21ContinuousPopulationAccessStatus student) (action student)) :
    LG21MandatoryGivenAccessLiteralSourceCloseout M testFeature
      htestNoiseVariance action := by
  rcases lg21ContinuousGaussianPopulation_exists_d6ResamplingSource
      M testFeature hpriorVariance hnonTestNoiseVariance htestNoiseVariance with
      ⟨baseLaw, baseMean, baseVariance, hbaseMean, hbaseLaw, hbaseVariance,
        hfactorization, _source, _hbaseLaw, _hbaseMean, _hbaseVariance,
        _htestNoiseVariance⟩
  letI : IsProbabilityMeasure baseLaw := hbaseLaw
  refine ⟨lg21MandatoryGivenAccess_accessPopulation_ae_takeAndReport
    M haccess action hfeasible, baseLaw, baseMean, baseVariance, hbaseMean,
    hbaseLaw, hbaseVariance, hfactorization, ?_⟩
  exact lg21ContinuousGaussianPopulation_d6SourceExperiment_fair
    M haccess hnoAccess testFeature baseLaw baseMean hbaseMean baseVariance
    hbaseVariance htestNoiseVariance hfactorization

end

end LG21TestOptionalPolicies

import LG21TestOptionalPolicies.ContinuousAccessConditionedPopulation
import LG21TestOptionalPolicies.Theorem44SourceGaussianResamplingRepair

/-!
# Literal one-score Gaussian parameter bridge for LG21

This module connects a small, genuinely derivable part of the existing
Gaussian posterior/resampling library to `LG21ContinuousGaussianPopulation`.

Starting only from the literal prior/noise product population, it proves the
unconditional raw-score law for one positive-access population and constructs
the corresponding one-score conjugate parameter record and resampling source.
The construction has no supplied posterior, PBO, action, or equilibrium field.

Its scope is intentionally narrow.  In particular, it does **not** prove that
`GaussianPriorSignal.posteriorMean` is a version of `E[q | score]`; that would
require an almost-everywhere conditional-kernel factorization of the displayed
joint law.  It also does not condition on the non-test feature profile or on a
selection event.  Those are separate source-model obligations.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory
open ProbabilityTheory
open AppliedModelingLib.Probability

/--
The one-score conjugate-Gaussian parameter record constructed directly from a
literal source prior and one literal centered test-noise coordinate.

This is only a parameter adapter.  The accompanying theorems below make its
measure-level scope explicit rather than treating the record as a conditional
posterior theorem.
-/
def lg21ContinuousGaussianOneScorePriorSignal
    {Feature : Type*} [Fintype Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    (hprior : 0 < (M.priorVariance : ℝ))
    (hnoise : 0 < (M.noiseVariance testFeature : ℝ)) : GaussianPriorSignal where
  priorMean := M.priorMean
  priorVar := M.priorVariance
  noiseVar := M.noiseVariance testFeature
  priorVar_pos := hprior
  noiseVar_pos := hnoise

/--
The source-generated no-base resampling experiment.  Its base carrier is a
singleton because this bridge treats only the literal unconditional one-score
law, not conditioning on a non-test feature profile.
-/
def lg21ContinuousGaussianOneScoreResamplingSource
    {Feature : Type*} [Fintype Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    (hprior : 0 < (M.priorVariance : ℝ))
    (hnoise : 0 < (M.noiseVariance testFeature : ℝ)) :
    LG21GaussianPBOResamplingSource PUnit where
  baseLaw := Measure.dirac PUnit.unit
  baseLaw_isProbability := by infer_instance
  posteriorBaseMean := fun _ => M.priorMean
  posteriorBaseMean_measurable := measurable_const
  posteriorBaseVariance := M.priorVariance
  posteriorBaseVariance_pos := hprior
  testNoiseVariance := M.noiseVariance testFeature
  testNoiseVariance_pos := hnoise

/--
The literal positive-access raw test-score marginal is Gaussian with exactly
the source prior mean and the sum of the source prior and test-noise variances.
No posterior or conditional-expectation assertion is used here.
-/
theorem lg21ContinuousGaussianAccessPopulation_oneScore_marginal
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature) :
    (lg21ContinuousGaussianAccessPopulationLaw M).map
        (lg21ContinuousPopulationFeature testFeature) =
      gaussianReal M.priorMean
        (M.priorVariance + M.noiseVariance testFeature) := by
  let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
  let priorLaw := gaussianReal M.priorMean M.priorVariance
  let noiseLaw := gaussianReal 0 (M.noiseVariance testFeature)
  let skillNoise : Bool × (ℝ × (Feature → ℝ)) → ℝ × ℝ :=
    fun student =>
      (lg21ContinuousPopulationSkill student,
        lg21ContinuousPopulationNoise testFeature student)
  let addScore : ℝ × ℝ → ℝ := fun pair => pair.1 + pair.2
  have hskillNoise_measurable : Measurable skillNoise := by
    exact (measurable_fst.comp measurable_snd).prodMk
      ((measurable_pi_apply testFeature).comp
        (measurable_snd.comp measurable_snd))
  have haddScore_measurable : Measurable addScore :=
    measurable_fst.add measurable_snd
  have hproduct_sum :
      (priorLaw.prod noiseLaw).map addScore =
        gaussianReal M.priorMean
          (M.priorVariance + M.noiseVariance testFeature) := by
    change Measure.map
      ((fun pair : ℝ × ℝ => pair.1) + (fun pair : ℝ × ℝ => pair.2))
      (priorLaw.prod noiseLaw) =
        gaussianReal M.priorMean
          (M.priorVariance + M.noiseVariance testFeature)
    have hindep :
        IndepFun (fun pair : ℝ × ℝ => pair.1)
          (fun pair : ℝ × ℝ => pair.2) (priorLaw.prod noiseLaw) := by
      exact ProbabilityTheory.indepFun_prod
        (μ := priorLaw) (ν := noiseLaw)
        (X := fun skill : ℝ => skill) (Y := fun noise : ℝ => noise)
        measurable_id measurable_id
    have hskill :
        Measure.map (fun pair : ℝ × ℝ => pair.1) (priorLaw.prod noiseLaw) =
          gaussianReal M.priorMean M.priorVariance := by
      rw [Measure.map_fst_prod]
      simp [priorLaw]
    have hnoise :
        Measure.map (fun pair : ℝ × ℝ => pair.2) (priorLaw.prod noiseLaw) =
          gaussianReal 0 (M.noiseVariance testFeature) := by
      rw [Measure.map_snd_prod]
      simp [noiseLaw]
    have hsum :=
      ProbabilityTheory.gaussianReal_add_gaussianReal_of_indepFun
        (m₁ := M.priorMean) (m₂ := (0 : ℝ))
        (v₁ := M.priorVariance) (v₂ := M.noiseVariance testFeature)
        (X := fun pair : ℝ × ℝ => pair.1)
        (Y := fun pair : ℝ × ℝ => pair.2)
        hindep hskill hnoise
    simpa using hsum
  calc
    accessLaw.map (lg21ContinuousPopulationFeature testFeature) =
        accessLaw.map (addScore ∘ skillNoise) := by rfl
    _ = (accessLaw.map skillNoise).map addScore :=
      (Measure.map_map haddScore_measurable hskillNoise_measurable).symm
    _ = (priorLaw.prod noiseLaw).map addScore := by
      rw [show accessLaw = lg21ContinuousGaussianAccessPopulationLaw M by rfl,
        show skillNoise = fun student =>
          (lg21ContinuousPopulationSkill student,
            lg21ContinuousPopulationNoise testFeature student) by rfl,
        lg21ContinuousGaussianAccessPopulation_skill_noise_joint M haccess testFeature]
    _ = gaussianReal M.priorMean
        (M.priorVariance + M.noiseVariance testFeature) := hproduct_sum

/--
At the no-base scope, the resampling module's generated conditional test kernel
is exactly the literal positive-access raw-score marginal.  This is a law
identity, not a claim that a posterior formula is a regular conditional law.
-/
theorem lg21ContinuousGaussianAccessPopulation_oneScore_marginal_eq_resampling_test
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (hprior : 0 < (M.priorVariance : ℝ))
    (hnoise : 0 < (M.noiseVariance testFeature : ℝ)) :
    (lg21ContinuousGaussianAccessPopulationLaw M).map
        (lg21ContinuousPopulationFeature testFeature) =
      lg21D6ConditionalGaussianTestKernel
        (lg21ContinuousGaussianOneScoreResamplingSource
          M testFeature hprior hnoise) PUnit.unit := by
  rw [lg21ContinuousGaussianAccessPopulation_oneScore_marginal M haccess]
  rw [lg21D6ConditionalGaussianTestKernel_apply]
  rfl

/--
The existing conjugate formula and the resampling estimator have the same
literal one-score parameter expression.  This deliberately establishes only
formula agreement; it does not identify either side with an RCD or a PBO.
-/
theorem lg21ContinuousGaussianOneScore_resamplingEstimate_eq_conjugateFormula
    {Feature : Type*} [Fintype Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    (hprior : 0 < (M.priorVariance : ℝ))
    (hnoise : 0 < (M.noiseVariance testFeature : ℝ)) (score : ℝ) :
    lg21D6GaussianPBOEstimate
        (lg21ContinuousGaussianOneScoreResamplingSource
          M testFeature hprior hnoise) (PUnit.unit, score) =
      (lg21ContinuousGaussianOneScorePriorSignal
        M testFeature hprior hnoise).posteriorMean score := by
  rw [GaussianPriorSignal.posteriorMean_eq_priorMean_add_signalWeight_mul]
  rfl

end

end LG21TestOptionalPolicies

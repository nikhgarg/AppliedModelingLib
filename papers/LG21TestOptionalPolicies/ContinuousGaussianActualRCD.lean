import AppliedModelingLib.Foundations.Probability.GaussianSignalRCD
import LG21TestOptionalPolicies.ContinuousAccessConditionedPopulation

/-!
# LG21 raw Gaussian score conditional distribution

This module specializes the proved additive-Gaussian regular conditional
distribution to LG21's literal positive-access population. The proof starts
from the population's actual `(skill, score)` joint law and transports the
generic disintegration through the coordinate order; it does not assume a
posterior kernel, a PBO, or an action-conditioned law.

In particular, the theorem below is only about the raw population before any
take or report selection. Optional and report-required action paths require
their own selected-population conditional-law bridge.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

/--
For the literal LG21 positive-access population, the conditional latent-skill
law given the raw test score is the affine Gaussian posterior, almost
everywhere in the actual raw score marginal.

This is an RCD fact about `Z = 1` before actions. It does not identify a
belief after optional reporting or report-required take selection.
-/
theorem lg21ContinuousGaussianAccessPopulation_condDistrib_skill_given_score_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnoiseVariance : 0 < (M.noiseVariance testFeature : ℝ)) :
    letI : IsProbabilityMeasure
        (lg21ContinuousGaussianAccessPopulationLaw M) :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
    letI : IsFiniteMeasure
        (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
    ⇑(condDistrib lg21ContinuousPopulationSkill
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousGaussianAccessPopulationLaw M)) =ᶠ[
        ae ((lg21ContinuousGaussianAccessPopulationLaw M).map
          (lg21ContinuousPopulationFeature testFeature))]
      (fun score : ℝ =>
        gaussianReal
          (AppliedModelingLib.Probability.gaussianSignalWeight
            (M.priorVariance : ℝ) (M.noiseVariance testFeature : ℝ) * score +
            AppliedModelingLib.Probability.gaussianSignalPriorWeight
              (M.priorVariance : ℝ) (M.noiseVariance testFeature : ℝ) * M.priorMean)
          (AppliedModelingLib.Probability.gaussianSignalPosteriorVariance
            (M.priorVariance : ℝ) (M.noiseVariance testFeature : ℝ))) := by
  let law := lg21ContinuousGaussianAccessPopulationLaw M
  letI : IsProbabilityMeasure law := by
    exact lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  letI : IsFiniteMeasure law := ⟨by simp⟩
  let skill : Bool × (ℝ × (Feature → ℝ)) → ℝ :=
    lg21ContinuousPopulationSkill
  let score : Bool × (ℝ × (Feature → ℝ)) → ℝ :=
    lg21ContinuousPopulationFeature testFeature
  let pairLaw : Measure (ℝ × ℝ) :=
    AppliedModelingLib.Probability.gaussianSignalPair M.priorMean
      (M.priorVariance : ℝ) (M.noiseVariance testFeature : ℝ)
  let posteriorKernel : Kernel ℝ ℝ :=
    AppliedModelingLib.Probability.gaussianSignalPosteriorKernel M.priorMean
      (M.priorVariance : ℝ) (M.noiseVariance testFeature : ℝ)
  have hskill : Measurable skill := by
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) => student.2.1
    exact measurable_fst.comp measurable_snd
  have hnoise : Measurable
      (lg21ContinuousPopulationNoise (Feature := Feature) testFeature) := by
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) => student.2.2 testFeature
    exact (measurable_pi_apply testFeature).comp
      (measurable_snd.comp measurable_snd)
  have hscore : Measurable score := by
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) =>
      student.2.1 + student.2.2 testFeature
    exact hskill.add hnoise
  have hraw : law.map (fun student => (skill student, score student)) =
      pairLaw.map (fun pair => (pair.1, pair.1 + pair.2)) := by
    simpa only [law, skill, score, pairLaw,
      AppliedModelingLib.Probability.gaussianSignalPair,
      Real.toNNReal_coe] using
      lg21ContinuousGaussianAccessPopulation_skill_score_joint M haccess testFeature
  have hsourceJoint : law.map (fun student => (score student, skill student)) =
      gaussianReal M.priorMean
          ((M.priorVariance : ℝ) + (M.noiseVariance testFeature : ℝ)).toNNReal ⊗ₘ
        posteriorKernel := by
    calc
      law.map (fun student => (score student, skill student)) =
          (law.map (fun student => (skill student, score student))).map Prod.swap := by
        simpa only [Function.comp_apply] using
          (Measure.map_map (μ := law) (g := Prod.swap)
            (f := fun student => (skill student, score student))
            (by fun_prop) (hskill.prodMk hscore)).symm
      _ = (pairLaw.map (fun pair => (pair.1, pair.1 + pair.2))).map Prod.swap := by
        rw [hraw]
      _ = pairLaw.map (fun pair => (pair.1 + pair.2, pair.1)) := by
        simpa only [Function.comp_apply] using
          (Measure.map_map (μ := pairLaw) (g := Prod.swap)
            (f := fun pair => (pair.1, pair.1 + pair.2))
            (by fun_prop) (by fun_prop))
      _ = gaussianReal M.priorMean
            ((M.priorVariance : ℝ) + (M.noiseVariance testFeature : ℝ)).toNNReal ⊗ₘ
          posteriorKernel := by
        exact AppliedModelingLib.Probability.gaussianSignalPair_score_latent_joint_factorization
          M.priorMean (M.priorVariance : ℝ) (M.noiseVariance testFeature : ℝ)
          hpriorVariance hnoiseVariance
  have hsourceScore : law.map score =
      gaussianReal M.priorMean
        ((M.priorVariance : ℝ) + (M.noiseVariance testFeature : ℝ)).toNNReal := by
    calc
      law.map score =
          (law.map (fun student => (skill student, score student))).map Prod.snd := by
        simpa only [Function.comp_apply] using
          (Measure.map_map (μ := law) (g := Prod.snd)
            (f := fun student => (skill student, score student))
            measurable_snd (hskill.prodMk hscore)).symm
      _ = (pairLaw.map (fun pair => (pair.1, pair.1 + pair.2))).map Prod.snd := by
        rw [hraw]
      _ = pairLaw.map (fun pair => pair.1 + pair.2) := by
        simpa only [Function.comp_apply] using
          (Measure.map_map (μ := pairLaw) (g := Prod.snd)
            (f := fun pair => (pair.1, pair.1 + pair.2))
            measurable_snd (by fun_prop))
      _ = gaussianReal M.priorMean
          ((M.priorVariance : ℝ) + (M.noiseVariance testFeature : ℝ)).toNNReal := by
        simpa only [pairLaw, AppliedModelingLib.Probability.gaussianSignalPair,
          AppliedModelingLib.Probability.gaussianSignalScore, Real.toNNReal_coe] using
          AppliedModelingLib.Probability.gaussianSignalPair_score_marginal
            M.priorMean (M.priorVariance : ℝ) (M.noiseVariance testFeature : ℝ)
            hpriorVariance hnoiseVariance
  have hjoint : law.map (fun student => (score student, skill student)) =
      law.map score ⊗ₘ posteriorKernel := by
    rw [hsourceScore]
    exact hsourceJoint
  letI : IsFiniteKernel posteriorKernel := by
    unfold posteriorKernel AppliedModelingLib.Probability.gaussianSignalPosteriorKernel
    infer_instance
  have hcond := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (μ := law) (X := score) (Y := skill) (κ := posteriorKernel)
    hscore hskill hjoint
  filter_upwards [hcond] with observed hobserved
  simpa only [law, skill, score, posteriorKernel,
    AppliedModelingLib.Probability.gaussianSignalPosteriorKernel_apply] using hobserved

end

end LG21TestOptionalPolicies

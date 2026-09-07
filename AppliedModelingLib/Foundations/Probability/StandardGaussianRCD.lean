import AppliedModelingLib.Foundations.Probability.BivariateGaussian
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# Standard Gaussian Conditional Distribution

This module proves the regular conditional distribution of the first coordinate
given the sum of two independent standard Gaussian coordinates.  The result is
stated almost everywhere in the sum marginal, which is the natural uniqueness
notion for `condDistrib`.

It is deliberately a standardized, nondegenerate one-dimensional result:
if `X` and `Z` are independent `N(0, 1)` variables, then the conditional law
of `X` given `X + Z = s` is `N(s / 2, 1 / 2)`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace AppliedModelingLib
namespace Probability

noncomputable section

/-- The joint law of two independent standard real Gaussians. -/
abbrev standardGaussianPair : Measure (ℝ × ℝ) :=
  (gaussianReal 0 (1 : ℝ≥0)).prod (gaussianReal 0 (1 : ℝ≥0))

/-- The observed sum in the standardized Gaussian signal model. -/
abbrev standardGaussianSum : ℝ × ℝ → ℝ := fun pair => pair.1 + pair.2

/-- The latent coordinate in the standardized Gaussian signal model. -/
abbrev standardGaussianFirst : ℝ × ℝ → ℝ := fun pair => pair.1

/-- The affine Gaussian posterior kernel for `X` given `X + Z`. -/
abbrev standardGaussianPosteriorKernel : Kernel ℝ ℝ :=
  ((Kernel.id : Kernel ℝ ℝ) ×ₖ Kernel.const ℝ
    (gaussianReal 0 (1 / 2 : ℝ≥0))).map
    (fun pair : ℝ × ℝ => pair.1 / 2 + pair.2)

theorem standardGaussianPosteriorKernel_apply (score : ℝ) :
    standardGaussianPosteriorKernel score =
      gaussianReal (score / 2) (1 / 2 : ℝ≥0) := by
  unfold standardGaussianPosteriorKernel
  rw [Kernel.map_apply _ (by fun_prop), Kernel.prod_apply, Kernel.id_apply,
    Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (by fun_prop) measurable_prodMk_left]
  rw [show ((fun pair : ℝ × ℝ => pair.1 / 2 + pair.2) ∘ Prod.mk score) =
        (fun residual : ℝ => residual + score / 2) by
          funext residual
          simp only [Function.comp_apply]
          ring]
  rw [ProbabilityTheory.gaussianReal_map_add_const]
  ring_nf

private theorem compProd_standardGaussianPosteriorKernel_base :
    gaussianReal 0 (2 : ℝ≥0) ⊗ₘ
        ((Kernel.id : Kernel ℝ ℝ) ×ₖ
          Kernel.const ℝ (gaussianReal 0 (1 / 2 : ℝ≥0))) =
      ((gaussianReal 0 (2 : ℝ≥0)).prod
        (gaussianReal 0 (1 / 2 : ℝ≥0))).map
          (fun pair : ℝ × ℝ => (pair.1, (pair.1, pair.2))) := by
  let μ : Measure ℝ := gaussianReal 0 (2 : ℝ≥0)
  let ν : Measure ℝ := gaussianReal 0 (1 / 2 : ℝ≥0)
  let F : ℝ × ℝ → ℝ × (ℝ × ℝ) :=
    fun pair => (pair.1, (pair.1, pair.2))
  have hF : Measurable F := by
    dsimp [F]
    fun_prop
  change μ ⊗ₘ ((Kernel.id : Kernel ℝ ℝ) ×ₖ Kernel.const ℝ ν) =
    (μ.prod ν).map F
  ext target htarget
  rw [Measure.compProd_apply htarget,
    Measure.map_apply hF htarget,
    Measure.prod_apply (hF htarget)]
  congr with score
  rw [Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply,
    Measure.dirac_prod, Measure.map_apply measurable_prodMk_left
      (measurable_prodMk_left htarget)]
  rfl

private theorem compProd_standardGaussianPosteriorKernel :
    gaussianReal 0 (2 : ℝ≥0) ⊗ₘ standardGaussianPosteriorKernel =
      ((gaussianReal 0 (2 : ℝ≥0)).prod
        (gaussianReal 0 (1 / 2 : ℝ≥0))).map
          (fun pair : ℝ × ℝ => (pair.1, pair.1 / 2 + pair.2)) := by
  unfold standardGaussianPosteriorKernel
  have hfun :
      (Prod.map id (fun pair : ℝ × ℝ => pair.1 / 2 + pair.2)) ∘
          (fun pair : ℝ × ℝ => (pair.1, (pair.1, pair.2))) =
        (fun pair : ℝ × ℝ => (pair.1, pair.1 / 2 + pair.2)) := by
    rfl
  rw [Measure.compProd_map (by fun_prop),
    compProd_standardGaussianPosteriorKernel_base,
    Measure.map_map (by fun_prop) (by fun_prop), hfun]

private theorem standardGaussianPair_fst_gaussian :
    HasGaussianLaw (fun pair : ℝ × ℝ => pair.1) standardGaussianPair := by
  constructor
  rw [Measure.map_fst_prod]
  simp
  infer_instance

private theorem standardGaussianPair_snd_gaussian :
    HasGaussianLaw (fun pair : ℝ × ℝ => pair.2) standardGaussianPair := by
  constructor
  rw [Measure.map_snd_prod]
  simp
  infer_instance

private theorem standardGaussianPair_sum_law :
    standardGaussianPair.map (fun pair : ℝ × ℝ => pair.1 + pair.2) =
      gaussianReal 0 (2 : ℝ≥0) := by
  have h := ProbabilityTheory.gaussianReal_add_gaussianReal_of_indepFun
      (P := standardGaussianPair)
      (X := fun pair : ℝ × ℝ => pair.1)
      (Y := fun pair : ℝ × ℝ => pair.2)
      (m₁ := 0) (m₂ := 0) (v₁ := (1 : ℝ≥0)) (v₂ := (1 : ℝ≥0))
      (ProbabilityTheory.indepFun_prod measurable_id measurable_id)
      (by rw [Measure.map_fst_prod]; simp)
      (by rw [Measure.map_snd_prod]; simp)
  convert h using 1
  all_goals norm_num

private theorem standardGaussianPair_neg_snd_law :
    standardGaussianPair.map (fun pair : ℝ × ℝ => -pair.2) =
      gaussianReal 0 (1 : ℝ≥0) := by
  calc
    standardGaussianPair.map (fun pair : ℝ × ℝ => -pair.2) =
        standardGaussianPair.map (Neg.neg ∘ Prod.snd) := by rfl
    _ = (standardGaussianPair.map (fun pair : ℝ × ℝ => pair.2)).map Neg.neg := by
          exact (Measure.map_map measurable_neg measurable_snd).symm
    _ = (gaussianReal 0 (1 : ℝ≥0)).map Neg.neg := by
          rw [Measure.map_snd_prod]
          simp
    _ = gaussianReal 0 (1 : ℝ≥0) := by
          simpa using
            (ProbabilityTheory.gaussianReal_map_neg (μ := (0 : ℝ))
              (v := (1 : ℝ≥0)))

private theorem standardGaussianPair_difference_law :
    standardGaussianPair.map (fun pair : ℝ × ℝ => pair.1 - pair.2) =
      gaussianReal 0 (2 : ℝ≥0) := by
  have h := ProbabilityTheory.gaussianReal_add_gaussianReal_of_indepFun
    (P := standardGaussianPair)
    (X := fun pair : ℝ × ℝ => pair.1)
    (Y := fun pair : ℝ × ℝ => -pair.2)
    (m₁ := 0) (m₂ := 0) (v₁ := (1 : ℝ≥0)) (v₂ := (1 : ℝ≥0))
    (ProbabilityTheory.indepFun_prod measurable_id measurable_id).neg_right
    (by rw [Measure.map_fst_prod]; simp)
    (by simpa using standardGaussianPair_neg_snd_law)
  convert h using 1
  all_goals norm_num

private theorem standardGaussianPair_residual_law :
    standardGaussianPair.map
        (fun pair : ℝ × ℝ => (pair.1 - pair.2) / 2) =
      gaussianReal 0 (1 / 2 : ℝ≥0) := by
  calc
    standardGaussianPair.map
        (fun pair : ℝ × ℝ => (pair.1 - pair.2) / 2) =
        standardGaussianPair.map
          ((fun x : ℝ => x / 2) ∘ (fun pair : ℝ × ℝ => pair.1 - pair.2)) := by
            rfl
    _ = (standardGaussianPair.map
        (fun pair : ℝ × ℝ => pair.1 - pair.2)).map (fun x : ℝ => x / 2) := by
          exact (Measure.map_map (by fun_prop) (by fun_prop)).symm
    _ = (gaussianReal 0 (2 : ℝ≥0)).map (fun x : ℝ => x / 2) := by
          rw [standardGaussianPair_difference_law]
    _ = gaussianReal 0 (1 / 2 : ℝ≥0) := by
          rw [ProbabilityTheory.gaussianReal_map_div_const]
          have hvar :
              (2 : ℝ≥0) /
                NNReal.mk ((2 : ℝ) ^ 2) (sq_nonneg (2 : ℝ)) =
              (1 / 2 : ℝ≥0) := by
            ext
            norm_num
          rw [hvar]
          norm_num

private def standardGaussianSumResidualCLM : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    ((1 / 2 : ℝ) •
      (ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ))

@[simp] private theorem standardGaussianSumResidualCLM_apply (pair : ℝ × ℝ) :
    standardGaussianSumResidualCLM pair =
      (pair.1 + pair.2, (pair.1 - pair.2) / 2) := by
  simp [standardGaussianSumResidualCLM]
  ring

private theorem standardGaussianPair_sum_residual_gaussian :
    HasGaussianLaw
      (fun pair : ℝ × ℝ => (pair.1 + pair.2, (pair.1 - pair.2) / 2))
      standardGaussianPair := by
  have hQE := (ProbabilityTheory.indepFun_prod measurable_id measurable_id).hasGaussianLaw
    standardGaussianPair_fst_gaussian standardGaussianPair_snd_gaussian
  have hmap := hQE.map standardGaussianSumResidualCLM
  have hfun :
      (fun pair : ℝ × ℝ => (pair.1 + pair.2, (pair.1 - pair.2) / 2)) =
        standardGaussianSumResidualCLM ∘
          (fun pair : ℝ × ℝ => (pair.1, pair.2)) := by
    funext pair
    simp [standardGaussianSumResidualCLM, Function.comp_apply]
    ring
  rw [hfun]
  exact hmap

private theorem standardGaussianPair_coordinate_covariance :
    cov[fun pair : ℝ × ℝ => pair.1, fun pair : ℝ × ℝ => pair.2;
      standardGaussianPair] = 0 := by
  exact ProbabilityTheory.covariance_fst_snd_prod
    (X := id) (Y := id)
    (ProbabilityTheory.memLp_id_gaussianReal (2 : ℝ≥0))
    (ProbabilityTheory.memLp_id_gaussianReal (2 : ℝ≥0))

private theorem standardGaussianPair_fst_covariance_self :
    cov[fun pair : ℝ × ℝ => pair.1, fun pair : ℝ × ℝ => pair.1;
      standardGaussianPair] = 1 := by
  calc
    cov[fun pair : ℝ × ℝ => pair.1, fun pair : ℝ × ℝ => pair.1;
        standardGaussianPair] =
        Var[fun pair : ℝ × ℝ => pair.1; standardGaussianPair] :=
      ProbabilityTheory.covariance_self (by fun_prop)
    _ = Var[id; standardGaussianPair.map (fun pair : ℝ × ℝ => pair.1)] := by
      rw [ProbabilityTheory.variance_map (X := id)
        (Y := fun pair : ℝ × ℝ => pair.1) (by fun_prop) (by fun_prop)]
      rfl
    _ = Var[id; gaussianReal 0 (1 : ℝ≥0)] := by
      rw [Measure.map_fst_prod]
      simp
    _ = 1 := by
      rw [ProbabilityTheory.variance_id_gaussianReal]
      norm_num

private theorem standardGaussianPair_snd_covariance_self :
    cov[fun pair : ℝ × ℝ => pair.2, fun pair : ℝ × ℝ => pair.2;
      standardGaussianPair] = 1 := by
  calc
    cov[fun pair : ℝ × ℝ => pair.2, fun pair : ℝ × ℝ => pair.2;
        standardGaussianPair] =
        Var[fun pair : ℝ × ℝ => pair.2; standardGaussianPair] :=
      ProbabilityTheory.covariance_self (by fun_prop)
    _ = Var[id; standardGaussianPair.map (fun pair : ℝ × ℝ => pair.2)] := by
      rw [ProbabilityTheory.variance_map (X := id)
        (Y := fun pair : ℝ × ℝ => pair.2) (by fun_prop) (by fun_prop)]
      rfl
    _ = Var[id; gaussianReal 0 (1 : ℝ≥0)] := by
      rw [Measure.map_snd_prod]
      simp
    _ = 1 := by
      rw [ProbabilityTheory.variance_id_gaussianReal]
      norm_num

private theorem standardGaussianPair_sum_residual_covariance :
    cov[fun pair : ℝ × ℝ => pair.1 + pair.2,
      fun pair : ℝ × ℝ => (pair.1 - pair.2) / 2;
      standardGaussianPair] = 0 := by
  let Q : ℝ × ℝ → ℝ := fun pair => pair.1
  let E : ℝ × ℝ → ℝ := fun pair => pair.2
  have hQ : MemLp Q 2 standardGaussianPair := by
    simpa [Q] using standardGaussianPair_fst_gaussian.memLp_two
  have hE : MemLp E 2 standardGaussianPair := by
    simpa [E] using standardGaussianPair_snd_gaussian.memLp_two
  have hQE : cov[Q, E; standardGaussianPair] = 0 := by
    simpa [Q, E] using standardGaussianPair_coordinate_covariance
  have hQQ : cov[Q, Q; standardGaussianPair] = 1 := by
    simpa [Q] using standardGaussianPair_fst_covariance_self
  have hEE : cov[E, E; standardGaussianPair] = 1 := by
    simpa [E] using standardGaussianPair_snd_covariance_self
  change cov[Q + E, fun pair => (Q pair - E pair) / 2;
    standardGaussianPair] = 0
  rw [ProbabilityTheory.covariance_fun_div_right]
  change cov[Q + E, Q - E; standardGaussianPair] / 2 = 0
  rw [ProbabilityTheory.covariance_add_left hQ hE (hQ.sub hE)]
  rw [ProbabilityTheory.covariance_sub_right hQ hQ hE]
  rw [ProbabilityTheory.covariance_sub_right hE hQ hE]
  rw [hQQ, hQE, ProbabilityTheory.covariance_comm E Q, hQE, hEE]
  norm_num

private theorem standardGaussianPair_sum_residual_indep :
    (fun pair : ℝ × ℝ => pair.1 + pair.2) ⟂ᵢ[standardGaussianPair]
      (fun pair : ℝ × ℝ => (pair.1 - pair.2) / 2) := by
  exact standardGaussianPair_sum_residual_gaussian.indepFun_of_covariance_eq_zero
    standardGaussianPair_sum_residual_covariance

private theorem standardGaussianPair_sum_residual_joint_law :
    standardGaussianPair.map
        (fun pair : ℝ × ℝ =>
          (pair.1 + pair.2, (pair.1 - pair.2) / 2)) =
      (gaussianReal 0 (2 : ℝ≥0)).prod
        (gaussianReal 0 (1 / 2 : ℝ≥0)) := by
  rw [(ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
    (f := fun pair : ℝ × ℝ => pair.1 + pair.2)
    (g := fun pair : ℝ × ℝ => (pair.1 - pair.2) / 2)
    (by fun_prop) (by fun_prop)).mp standardGaussianPair_sum_residual_indep]
  rw [standardGaussianPair_sum_law, standardGaussianPair_residual_law]

private theorem standardGaussianPair_sum_first_joint_law :
    standardGaussianPair.map
        (fun pair : ℝ × ℝ => (pair.1 + pair.2, pair.1)) =
      gaussianReal 0 (2 : ℝ≥0) ⊗ₘ standardGaussianPosteriorKernel := by
  let B : ℝ × ℝ → ℝ × ℝ :=
    fun pair => (pair.1 + pair.2, (pair.1 - pair.2) / 2)
  let A : ℝ × ℝ → ℝ × ℝ :=
    fun pair => (pair.1, pair.1 / 2 + pair.2)
  let C : ℝ × ℝ → ℝ × ℝ :=
    fun pair => (pair.1 + pair.2, pair.1)
  have hcomp : A ∘ B = C := by
    funext pair
    simp [A, B, C, Function.comp_apply]
    ring
  change standardGaussianPair.map C =
    gaussianReal 0 (2 : ℝ≥0) ⊗ₘ standardGaussianPosteriorKernel
  calc
    standardGaussianPair.map C = standardGaussianPair.map (A ∘ B) := by rw [hcomp]
    _ = (standardGaussianPair.map B).map A := by
      exact (Measure.map_map (by fun_prop) (by fun_prop)).symm
    _ = ((gaussianReal 0 (2 : ℝ≥0)).prod
        (gaussianReal 0 (1 / 2 : ℝ≥0))).map A := by
      rw [show standardGaussianPair.map B =
          (gaussianReal 0 (2 : ℝ≥0)).prod
            (gaussianReal 0 (1 / 2 : ℝ≥0)) by
        simpa [B] using standardGaussianPair_sum_residual_joint_law]
    _ = gaussianReal 0 (2 : ℝ≥0) ⊗ₘ standardGaussianPosteriorKernel := by
      simpa [A] using compProd_standardGaussianPosteriorKernel.symm

/--
For two independent standard real Gaussians, the regular conditional law of
the first coordinate given their sum is the affine Gaussian posterior kernel.
-/
theorem standardGaussianPair_condDistrib_fst_given_sum :
    ⇑(condDistrib standardGaussianFirst standardGaussianSum standardGaussianPair) =ᶠ[
        ae (standardGaussianPair.map standardGaussianSum)]
      (fun score : ℝ => gaussianReal (score / 2) (1 / 2 : ℝ≥0)) := by
  have hjoint : standardGaussianPair.map
      (fun pair => (standardGaussianSum pair, standardGaussianFirst pair)) =
        standardGaussianPair.map standardGaussianSum ⊗ₘ
          standardGaussianPosteriorKernel := by
    rw [show standardGaussianPair.map standardGaussianSum =
        gaussianReal 0 (2 : ℝ≥0) by
      simpa [standardGaussianSum] using standardGaussianPair_sum_law]
    simpa [standardGaussianSum, standardGaussianFirst] using
      standardGaussianPair_sum_first_joint_law
  letI : IsFiniteKernel standardGaussianPosteriorKernel := by
    unfold standardGaussianPosteriorKernel
    infer_instance
  have hcond := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (μ := standardGaussianPair) (X := standardGaussianSum)
    (Y := standardGaussianFirst) (κ := standardGaussianPosteriorKernel)
    (by fun_prop) (by fun_prop) hjoint
  filter_upwards [hcond] with score hscore
  simpa only [standardGaussianPosteriorKernel_apply] using hscore

end

end Probability
end AppliedModelingLib

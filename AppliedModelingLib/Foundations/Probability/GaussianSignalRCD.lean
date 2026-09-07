import AppliedModelingLib.Foundations.Probability.BivariateGaussian
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# Gaussian Signal Conditional Distribution

This module proves the regular conditional distribution of a latent real
Gaussian variable given an independent-noise additive Gaussian signal.  It is
stated almost everywhere in the signal marginal, the natural uniqueness scope
of `condDistrib`.

For a latent law `N(mean, priorVariance)` and independent noise law
`N(0, noiseVariance)`, both with strictly positive real variances, the
conditional latent law given score `s` is Gaussian with mean
`priorWeight * s + noiseWeight * mean` and variance
`priorVariance * noiseVariance / (priorVariance + noiseVariance)`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace AppliedModelingLib
namespace Probability

noncomputable section

/-- The independent latent/noise product law for one additive Gaussian signal. -/
abbrev gaussianSignalPair (mean priorVariance noiseVariance : ℝ) :
    Measure (ℝ × ℝ) :=
  (gaussianReal mean priorVariance.toNNReal).prod
    (gaussianReal 0 noiseVariance.toNNReal)

/-- The raw additive signal formed from a latent coordinate and its noise. -/
abbrev gaussianSignalScore : ℝ × ℝ → ℝ := fun pair => pair.1 + pair.2

/-- The coefficient on the observed signal in the Gaussian posterior mean. -/
abbrev gaussianSignalWeight (priorVariance noiseVariance : ℝ) : ℝ :=
  priorVariance / (priorVariance + noiseVariance)

/-- The coefficient on the prior mean in the Gaussian posterior mean. -/
abbrev gaussianSignalPriorWeight (priorVariance noiseVariance : ℝ) : ℝ :=
  noiseVariance / (priorVariance + noiseVariance)

/-- The centered residual independent of the score in the Gaussian signal model. -/
abbrev gaussianSignalResidual (priorVariance noiseVariance : ℝ) : ℝ × ℝ → ℝ :=
  fun pair =>
    gaussianSignalPriorWeight priorVariance noiseVariance * pair.1 -
      gaussianSignalWeight priorVariance noiseVariance * pair.2

/-- The posterior variance in the one-dimensional additive Gaussian signal model. -/
abbrev gaussianSignalPosteriorVariance (priorVariance noiseVariance : ℝ) : ℝ≥0 :=
  (priorVariance * noiseVariance / (priorVariance + noiseVariance)).toNNReal

/-- The explicit affine posterior kernel for the additive Gaussian signal model. -/
def gaussianSignalPosteriorKernel
    (mean priorVariance noiseVariance : ℝ) : Kernel ℝ ℝ :=
  ((Kernel.id : Kernel ℝ ℝ) ×ₖ
    Kernel.const ℝ
      (gaussianReal
        (gaussianSignalPriorWeight priorVariance noiseVariance * mean)
        (gaussianSignalPosteriorVariance priorVariance noiseVariance))).map
    (fun pair : ℝ × ℝ =>
      gaussianSignalWeight priorVariance noiseVariance * pair.1 + pair.2)

theorem gaussianSignalPosteriorKernel_apply
    (mean priorVariance noiseVariance score : ℝ) :
    gaussianSignalPosteriorKernel mean priorVariance noiseVariance score =
      gaussianReal
        (gaussianSignalWeight priorVariance noiseVariance * score +
          gaussianSignalPriorWeight priorVariance noiseVariance * mean)
        (gaussianSignalPosteriorVariance priorVariance noiseVariance) := by
  unfold gaussianSignalPosteriorKernel
  rw [Kernel.map_apply _ (by fun_prop), Kernel.prod_apply, Kernel.id_apply,
    Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (by fun_prop) measurable_prodMk_left]
  rw [show
      ((fun pair : ℝ × ℝ =>
        gaussianSignalWeight priorVariance noiseVariance * pair.1 + pair.2) ∘
          Prod.mk score) =
        (fun residual : ℝ => residual +
          gaussianSignalWeight priorVariance noiseVariance * score) by
          funext residual
          simp only [Function.comp_apply]
          ring]
  rw [ProbabilityTheory.gaussianReal_map_add_const]
  congr 1
  ring

private theorem compProd_gaussianSignalPosteriorKernel_base
    (mean priorVariance noiseVariance : ℝ) :
    gaussianReal mean (priorVariance + noiseVariance).toNNReal ⊗ₘ
        ((Kernel.id : Kernel ℝ ℝ) ×ₖ
          Kernel.const ℝ
            (gaussianReal
              (gaussianSignalPriorWeight priorVariance noiseVariance * mean)
              (gaussianSignalPosteriorVariance priorVariance noiseVariance))) =
      ((gaussianReal mean (priorVariance + noiseVariance).toNNReal).prod
        (gaussianReal
          (gaussianSignalPriorWeight priorVariance noiseVariance * mean)
          (gaussianSignalPosteriorVariance priorVariance noiseVariance))).map
          (fun pair : ℝ × ℝ => (pair.1, (pair.1, pair.2))) := by
  let μ : Measure ℝ := gaussianReal mean (priorVariance + noiseVariance).toNNReal
  let ν : Measure ℝ := gaussianReal
    (gaussianSignalPriorWeight priorVariance noiseVariance * mean)
    (gaussianSignalPosteriorVariance priorVariance noiseVariance)
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

private theorem compProd_gaussianSignalPosteriorKernel
    (mean priorVariance noiseVariance : ℝ) :
    gaussianReal mean (priorVariance + noiseVariance).toNNReal ⊗ₘ
        gaussianSignalPosteriorKernel mean priorVariance noiseVariance =
      ((gaussianReal mean (priorVariance + noiseVariance).toNNReal).prod
        (gaussianReal
          (gaussianSignalPriorWeight priorVariance noiseVariance * mean)
          (gaussianSignalPosteriorVariance priorVariance noiseVariance))).map
          (fun pair : ℝ × ℝ =>
            (pair.1,
              gaussianSignalWeight priorVariance noiseVariance * pair.1 + pair.2)) := by
  unfold gaussianSignalPosteriorKernel
  have hfun :
      (Prod.map id (fun pair : ℝ × ℝ =>
        gaussianSignalWeight priorVariance noiseVariance * pair.1 + pair.2)) ∘
          (fun pair : ℝ × ℝ => (pair.1, (pair.1, pair.2))) =
        (fun pair : ℝ × ℝ =>
          (pair.1,
            gaussianSignalWeight priorVariance noiseVariance * pair.1 + pair.2)) := by
    rfl
  rw [Measure.compProd_map (by fun_prop),
    compProd_gaussianSignalPosteriorKernel_base,
    Measure.map_map (by fun_prop) (by fun_prop), hfun]

private theorem gaussianSignalPair_fst_gaussian
    (mean priorVariance noiseVariance : ℝ) :
    HasGaussianLaw (fun pair : ℝ × ℝ => pair.1)
      (gaussianSignalPair mean priorVariance noiseVariance) := by
  constructor
  rw [Measure.map_fst_prod]
  simp
  infer_instance

private theorem gaussianSignalPair_snd_gaussian
    (mean priorVariance noiseVariance : ℝ) :
    HasGaussianLaw (fun pair : ℝ × ℝ => pair.2)
      (gaussianSignalPair mean priorVariance noiseVariance) := by
  constructor
  rw [Measure.map_snd_prod]
  simp
  infer_instance

/-- The exact Gaussian marginal law of the additive score. -/
theorem gaussianSignalPair_score_marginal
    (mean priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance) :
    (gaussianSignalPair mean priorVariance noiseVariance).map gaussianSignalScore =
      gaussianReal mean (priorVariance + noiseVariance).toNNReal := by
  have h := ProbabilityTheory.gaussianReal_add_gaussianReal_of_indepFun
      (P := gaussianSignalPair mean priorVariance noiseVariance)
      (X := fun pair : ℝ × ℝ => pair.1)
      (Y := fun pair : ℝ × ℝ => pair.2)
      (m₁ := mean) (m₂ := 0)
      (v₁ := priorVariance.toNNReal) (v₂ := noiseVariance.toNNReal)
      (ProbabilityTheory.indepFun_prod measurable_id measurable_id)
      (by rw [Measure.map_fst_prod]; simp)
      (by rw [Measure.map_snd_prod]; simp)
  simpa [gaussianSignalScore,
    Real.toNNReal_add_toNNReal hpriorVariance.le hnoiseVariance.le] using h

private def gaussianSignalScoreResidualCLM
    (priorVariance noiseVariance : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    (gaussianSignalPriorWeight priorVariance noiseVariance •
      (ContinuousLinearMap.fst ℝ ℝ ℝ) -
      gaussianSignalWeight priorVariance noiseVariance •
        (ContinuousLinearMap.snd ℝ ℝ ℝ))

@[simp] private theorem gaussianSignalScoreResidualCLM_apply
    (priorVariance noiseVariance : ℝ) (pair : ℝ × ℝ) :
    gaussianSignalScoreResidualCLM priorVariance noiseVariance pair =
      (gaussianSignalScore pair,
        gaussianSignalResidual priorVariance noiseVariance pair) := by
  simp [gaussianSignalScoreResidualCLM, gaussianSignalScore,
    gaussianSignalResidual]

private theorem gaussianSignalPair_score_residual_gaussian
    (mean priorVariance noiseVariance : ℝ) :
    HasGaussianLaw
      (fun pair : ℝ × ℝ =>
        (gaussianSignalScore pair,
          gaussianSignalResidual priorVariance noiseVariance pair))
      (gaussianSignalPair mean priorVariance noiseVariance) := by
  have hQE := (ProbabilityTheory.indepFun_prod measurable_id measurable_id).hasGaussianLaw
    (gaussianSignalPair_fst_gaussian mean priorVariance noiseVariance)
    (gaussianSignalPair_snd_gaussian mean priorVariance noiseVariance)
  have hmap := hQE.map
    (gaussianSignalScoreResidualCLM priorVariance noiseVariance)
  have hfun :
      (fun pair : ℝ × ℝ =>
        (gaussianSignalScore pair,
          gaussianSignalResidual priorVariance noiseVariance pair)) =
        gaussianSignalScoreResidualCLM priorVariance noiseVariance ∘
          (fun pair : ℝ × ℝ => (pair.1, pair.2)) := by
    funext pair
    simp [gaussianSignalScoreResidualCLM, gaussianSignalScore,
      gaussianSignalResidual, Function.comp_apply]
  rw [hfun]
  exact hmap

private theorem gaussianSignalPair_scaled_fst_law
    (mean priorVariance noiseVariance coefficient : ℝ) :
    (gaussianSignalPair mean priorVariance noiseVariance).map
        (fun pair : ℝ × ℝ => coefficient * pair.1) =
      gaussianReal (coefficient * mean)
        (NNReal.mk (coefficient ^ 2) (sq_nonneg coefficient) *
          priorVariance.toNNReal) := by
  calc
    (gaussianSignalPair mean priorVariance noiseVariance).map
        (fun pair : ℝ × ℝ => coefficient * pair.1) =
        ((gaussianSignalPair mean priorVariance noiseVariance).map
          (fun pair : ℝ × ℝ => pair.1)).map (fun x : ℝ => coefficient * x) := by
          exact (Measure.map_map (by fun_prop) measurable_fst).symm
    _ = (gaussianReal mean priorVariance.toNNReal).map
        (fun x : ℝ => coefficient * x) := by
      rw [Measure.map_fst_prod]
      simp
    _ = gaussianReal (coefficient * mean)
        (NNReal.mk (coefficient ^ 2) (sq_nonneg coefficient) *
          priorVariance.toNNReal) := by
      rw [ProbabilityTheory.gaussianReal_map_const_mul]

private theorem gaussianSignalPair_scaled_snd_law
    (mean priorVariance noiseVariance coefficient : ℝ) :
    (gaussianSignalPair mean priorVariance noiseVariance).map
        (fun pair : ℝ × ℝ => coefficient * pair.2) =
      gaussianReal 0
        (NNReal.mk (coefficient ^ 2) (sq_nonneg coefficient) *
          noiseVariance.toNNReal) := by
  calc
    (gaussianSignalPair mean priorVariance noiseVariance).map
        (fun pair : ℝ × ℝ => coefficient * pair.2) =
        ((gaussianSignalPair mean priorVariance noiseVariance).map
          (fun pair : ℝ × ℝ => pair.2)).map (fun x : ℝ => coefficient * x) := by
          exact (Measure.map_map (by fun_prop) measurable_snd).symm
    _ = (gaussianReal 0 noiseVariance.toNNReal).map
        (fun x : ℝ => coefficient * x) := by
      rw [Measure.map_snd_prod]
      simp
    _ = gaussianReal 0
        (NNReal.mk (coefficient ^ 2) (sq_nonneg coefficient) *
          noiseVariance.toNNReal) := by
      simpa using
        (ProbabilityTheory.gaussianReal_map_const_mul
          (μ := (0 : ℝ)) (v := noiseVariance.toNNReal) coefficient)

private theorem gaussianSignalPair_residual_law
    (mean priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance) :
    (gaussianSignalPair mean priorVariance noiseVariance).map
        (gaussianSignalResidual priorVariance noiseVariance) =
      gaussianReal
        (gaussianSignalPriorWeight priorVariance noiseVariance * mean)
        (gaussianSignalPosteriorVariance priorVariance noiseVariance) := by
  let signalWeight : ℝ := gaussianSignalWeight priorVariance noiseVariance
  let priorWeight : ℝ := gaussianSignalPriorWeight priorVariance noiseVariance
  have hindep :
      (fun pair : ℝ × ℝ => priorWeight * pair.1) ⟂ᵢ[
        gaussianSignalPair mean priorVariance noiseVariance]
        (fun pair : ℝ × ℝ => (-signalWeight) * pair.2) := by
    have h := (ProbabilityTheory.indepFun_prod
      (μ := gaussianReal mean priorVariance.toNNReal)
      (ν := gaussianReal 0 noiseVariance.toNNReal)
      (X := fun x : ℝ => x) (Y := fun x : ℝ => x)
      measurable_id measurable_id).comp
      (φ := fun x : ℝ => priorWeight * x)
      (ψ := fun x : ℝ => (-signalWeight) * x)
      (by fun_prop) (by fun_prop)
    simpa [Function.comp_apply] using h
  have hsum := ProbabilityTheory.gaussianReal_add_gaussianReal_of_indepFun
      (P := gaussianSignalPair mean priorVariance noiseVariance)
      (X := fun pair : ℝ × ℝ => priorWeight * pair.1)
      (Y := fun pair : ℝ × ℝ => (-signalWeight) * pair.2)
      (m₁ := priorWeight * mean) (m₂ := 0)
      (v₁ := NNReal.mk (priorWeight ^ 2) (sq_nonneg priorWeight) *
        priorVariance.toNNReal)
      (v₂ := NNReal.mk ((-signalWeight) ^ 2) (sq_nonneg (-signalWeight)) *
        noiseVariance.toNNReal)
      hindep
      (gaussianSignalPair_scaled_fst_law
        mean priorVariance noiseVariance priorWeight)
      (gaussianSignalPair_scaled_snd_law
        mean priorVariance noiseVariance (-signalWeight))
  have htotal_pos : 0 < priorVariance + noiseVariance :=
    add_pos hpriorVariance hnoiseVariance
  have hvariance :
      NNReal.mk (priorWeight ^ 2) (sq_nonneg priorWeight) *
          priorVariance.toNNReal +
        NNReal.mk ((-signalWeight) ^ 2) (sq_nonneg (-signalWeight)) *
          noiseVariance.toNNReal =
        gaussianSignalPosteriorVariance priorVariance noiseVariance := by
    ext
    simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mk,
      Real.coe_toNNReal _ hpriorVariance.le,
      Real.coe_toNNReal _ hnoiseVariance.le]
    rw [Real.coe_toNNReal _
      (div_nonneg (mul_nonneg hpriorVariance.le hnoiseVariance.le) htotal_pos.le)]
    dsimp [signalWeight, priorWeight, gaussianSignalWeight,
      gaussianSignalPriorWeight, gaussianSignalPosteriorVariance]
    field_simp [ne_of_gt htotal_pos]
    ring
  have hfun :
      (fun pair : ℝ × ℝ =>
        priorWeight * pair.1 + (-signalWeight) * pair.2) =
        gaussianSignalResidual priorVariance noiseVariance := by
    funext pair
    simp [signalWeight, priorWeight, gaussianSignalResidual]
    ring
  rw [hvariance] at hsum
  simpa [hfun, signalWeight, priorWeight] using hsum

private theorem gaussianSignalPair_coordinate_covariance
    (mean priorVariance noiseVariance : ℝ) :
    cov[fun pair : ℝ × ℝ => pair.1, fun pair : ℝ × ℝ => pair.2;
      gaussianSignalPair mean priorVariance noiseVariance] = 0 := by
  exact ProbabilityTheory.covariance_fst_snd_prod
    (X := id) (Y := id)
    (ProbabilityTheory.memLp_id_gaussianReal (2 : ℝ≥0))
    (ProbabilityTheory.memLp_id_gaussianReal (2 : ℝ≥0))

private theorem gaussianSignalPair_fst_covariance_self
    (mean priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance) :
    cov[fun pair : ℝ × ℝ => pair.1, fun pair : ℝ × ℝ => pair.1;
      gaussianSignalPair mean priorVariance noiseVariance] = priorVariance := by
  calc
    cov[fun pair : ℝ × ℝ => pair.1, fun pair : ℝ × ℝ => pair.1;
        gaussianSignalPair mean priorVariance noiseVariance] =
        Var[fun pair : ℝ × ℝ => pair.1;
          gaussianSignalPair mean priorVariance noiseVariance] :=
      ProbabilityTheory.covariance_self (by fun_prop)
    _ = Var[id; (gaussianSignalPair mean priorVariance noiseVariance).map
        (fun pair : ℝ × ℝ => pair.1)] := by
      rw [ProbabilityTheory.variance_map (X := id)
        (Y := fun pair : ℝ × ℝ => pair.1) (by fun_prop) (by fun_prop)]
      rfl
    _ = Var[id; gaussianReal mean priorVariance.toNNReal] := by
      rw [Measure.map_fst_prod]
      simp
    _ = priorVariance := by
      rw [ProbabilityTheory.variance_id_gaussianReal]
      exact Real.coe_toNNReal _ hpriorVariance.le

private theorem gaussianSignalPair_snd_covariance_self
    (mean priorVariance noiseVariance : ℝ)
    (hnoiseVariance : 0 < noiseVariance) :
    cov[fun pair : ℝ × ℝ => pair.2, fun pair : ℝ × ℝ => pair.2;
      gaussianSignalPair mean priorVariance noiseVariance] = noiseVariance := by
  calc
    cov[fun pair : ℝ × ℝ => pair.2, fun pair : ℝ × ℝ => pair.2;
        gaussianSignalPair mean priorVariance noiseVariance] =
        Var[fun pair : ℝ × ℝ => pair.2;
          gaussianSignalPair mean priorVariance noiseVariance] :=
      ProbabilityTheory.covariance_self (by fun_prop)
    _ = Var[id; (gaussianSignalPair mean priorVariance noiseVariance).map
        (fun pair : ℝ × ℝ => pair.2)] := by
      rw [ProbabilityTheory.variance_map (X := id)
        (Y := fun pair : ℝ × ℝ => pair.2) (by fun_prop) (by fun_prop)]
      rfl
    _ = Var[id; gaussianReal 0 noiseVariance.toNNReal] := by
      rw [Measure.map_snd_prod]
      simp
    _ = noiseVariance := by
      rw [ProbabilityTheory.variance_id_gaussianReal]
      exact Real.coe_toNNReal _ hnoiseVariance.le

private theorem gaussianSignalPair_score_residual_covariance
    (mean priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance) :
    cov[gaussianSignalScore,
      gaussianSignalResidual priorVariance noiseVariance;
      gaussianSignalPair mean priorVariance noiseVariance] = 0 := by
  let Q : ℝ × ℝ → ℝ := fun pair => pair.1
  let E : ℝ × ℝ → ℝ := fun pair => pair.2
  let signalWeight : ℝ := gaussianSignalWeight priorVariance noiseVariance
  let priorWeight : ℝ := gaussianSignalPriorWeight priorVariance noiseVariance
  have hQ : MemLp Q 2 (gaussianSignalPair mean priorVariance noiseVariance) := by
    simpa [Q] using
      (gaussianSignalPair_fst_gaussian mean priorVariance noiseVariance).memLp_two
  have hE : MemLp E 2 (gaussianSignalPair mean priorVariance noiseVariance) := by
    simpa [E] using
      (gaussianSignalPair_snd_gaussian mean priorVariance noiseVariance).memLp_two
  have hQE : cov[Q, E; gaussianSignalPair mean priorVariance noiseVariance] = 0 := by
    simpa [Q, E] using
      gaussianSignalPair_coordinate_covariance mean priorVariance noiseVariance
  have hQQ : cov[Q, Q; gaussianSignalPair mean priorVariance noiseVariance] =
      priorVariance := by
    simpa [Q] using
      gaussianSignalPair_fst_covariance_self
        mean priorVariance noiseVariance hpriorVariance
  have hEE : cov[E, E; gaussianSignalPair mean priorVariance noiseVariance] =
      noiseVariance := by
    simpa [E] using
      gaussianSignalPair_snd_covariance_self
        mean priorVariance noiseVariance hnoiseVariance
  have htotal_pos : 0 < priorVariance + noiseVariance :=
    add_pos hpriorVariance hnoiseVariance
  change cov[Q + E, priorWeight • Q - signalWeight • E;
    gaussianSignalPair mean priorVariance noiseVariance] = 0
  rw [ProbabilityTheory.covariance_add_left hQ hE
    ((hQ.const_smul priorWeight).sub (hE.const_smul signalWeight))]
  rw [ProbabilityTheory.covariance_sub_right
    hQ (hQ.const_smul priorWeight) (hE.const_smul signalWeight)]
  rw [ProbabilityTheory.covariance_sub_right
    hE (hQ.const_smul priorWeight) (hE.const_smul signalWeight)]
  rw [ProbabilityTheory.covariance_smul_right]
  rw [ProbabilityTheory.covariance_smul_right]
  rw [ProbabilityTheory.covariance_smul_right]
  rw [ProbabilityTheory.covariance_smul_right]
  rw [hQQ, hQE, ProbabilityTheory.covariance_comm E Q, hQE, hEE]
  dsimp [signalWeight, priorWeight, gaussianSignalWeight,
    gaussianSignalPriorWeight]
  field_simp [ne_of_gt htotal_pos]
  ring

private theorem gaussianSignalPair_score_residual_indep
    (mean priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance) :
    gaussianSignalScore ⟂ᵢ[
      gaussianSignalPair mean priorVariance noiseVariance]
      gaussianSignalResidual priorVariance noiseVariance := by
  exact (gaussianSignalPair_score_residual_gaussian
    mean priorVariance noiseVariance).indepFun_of_covariance_eq_zero
      (gaussianSignalPair_score_residual_covariance
        mean priorVariance noiseVariance hpriorVariance hnoiseVariance)

private theorem gaussianSignalPair_score_residual_joint_law
    (mean priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance) :
    (gaussianSignalPair mean priorVariance noiseVariance).map
        (fun pair : ℝ × ℝ =>
          (gaussianSignalScore pair,
            gaussianSignalResidual priorVariance noiseVariance pair)) =
      (gaussianReal mean (priorVariance + noiseVariance).toNNReal).prod
        (gaussianReal
          (gaussianSignalPriorWeight priorVariance noiseVariance * mean)
          (gaussianSignalPosteriorVariance priorVariance noiseVariance)) := by
  rw [(ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
    (f := gaussianSignalScore)
    (g := gaussianSignalResidual priorVariance noiseVariance)
    (by fun_prop) (by fun_prop)).mp
      (gaussianSignalPair_score_residual_indep
        mean priorVariance noiseVariance hpriorVariance hnoiseVariance)]
  rw [gaussianSignalPair_score_marginal
    mean priorVariance noiseVariance hpriorVariance hnoiseVariance,
    gaussianSignalPair_residual_law
      mean priorVariance noiseVariance hpriorVariance hnoiseVariance]

/--
The exact score/latent joint-law factorization through the explicit posterior
kernel.  This is the transport-ready form of the Gaussian conditioning result.
-/
theorem gaussianSignalPair_score_latent_joint_factorization
    (mean priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance) :
    (gaussianSignalPair mean priorVariance noiseVariance).map
        (fun pair : ℝ × ℝ => (gaussianSignalScore pair, pair.1)) =
      gaussianReal mean (priorVariance + noiseVariance).toNNReal ⊗ₘ
        gaussianSignalPosteriorKernel mean priorVariance noiseVariance := by
  let A : ℝ × ℝ → ℝ × ℝ :=
    fun pair =>
      (pair.1,
        gaussianSignalWeight priorVariance noiseVariance * pair.1 + pair.2)
  let B : ℝ × ℝ → ℝ × ℝ :=
    fun pair =>
      (gaussianSignalScore pair,
        gaussianSignalResidual priorVariance noiseVariance pair)
  let C : ℝ × ℝ → ℝ × ℝ :=
    fun pair => (gaussianSignalScore pair, pair.1)
  have htotal_pos : 0 < priorVariance + noiseVariance :=
    add_pos hpriorVariance hnoiseVariance
  have hcomp : A ∘ B = C := by
    funext pair
    simp [A, B, C, gaussianSignalScore, gaussianSignalResidual,
      gaussianSignalWeight, gaussianSignalPriorWeight, Function.comp_apply]
    field_simp [ne_of_gt htotal_pos]
    ring
  change (gaussianSignalPair mean priorVariance noiseVariance).map C =
    gaussianReal mean (priorVariance + noiseVariance).toNNReal ⊗ₘ
      gaussianSignalPosteriorKernel mean priorVariance noiseVariance
  calc
    (gaussianSignalPair mean priorVariance noiseVariance).map C =
        (gaussianSignalPair mean priorVariance noiseVariance).map (A ∘ B) := by
          rw [hcomp]
    _ = ((gaussianSignalPair mean priorVariance noiseVariance).map B).map A := by
      exact (Measure.map_map (by fun_prop) (by fun_prop)).symm
    _ = ((gaussianReal mean (priorVariance + noiseVariance).toNNReal).prod
        (gaussianReal
          (gaussianSignalPriorWeight priorVariance noiseVariance * mean)
          (gaussianSignalPosteriorVariance priorVariance noiseVariance))).map A := by
      rw [show (gaussianSignalPair mean priorVariance noiseVariance).map B =
          (gaussianReal mean (priorVariance + noiseVariance).toNNReal).prod
            (gaussianReal
              (gaussianSignalPriorWeight priorVariance noiseVariance * mean)
              (gaussianSignalPosteriorVariance priorVariance noiseVariance)) by
        simpa [B] using gaussianSignalPair_score_residual_joint_law
          mean priorVariance noiseVariance hpriorVariance hnoiseVariance]
    _ = gaussianReal mean (priorVariance + noiseVariance).toNNReal ⊗ₘ
        gaussianSignalPosteriorKernel mean priorVariance noiseVariance := by
      simpa [A] using
        (compProd_gaussianSignalPosteriorKernel
          mean priorVariance noiseVariance).symm

/--
The a.e. regular conditional law of an arbitrary-location latent Gaussian
given an independent additive Gaussian signal with positive variances.
-/
theorem gaussianSignal_condDistrib_latent_given_score
    (mean priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance) :
    ⇑(condDistrib (fun pair : ℝ × ℝ => pair.1)
      gaussianSignalScore
      (gaussianSignalPair mean priorVariance noiseVariance)) =ᶠ[
        ae ((gaussianSignalPair mean priorVariance noiseVariance).map
          gaussianSignalScore)]
      (fun score : ℝ =>
        gaussianReal
          (gaussianSignalWeight priorVariance noiseVariance * score +
            gaussianSignalPriorWeight priorVariance noiseVariance * mean)
          (gaussianSignalPosteriorVariance priorVariance noiseVariance)) := by
  have hjoint : (gaussianSignalPair mean priorVariance noiseVariance).map
      (fun pair => (gaussianSignalScore pair, pair.1)) =
        (gaussianSignalPair mean priorVariance noiseVariance).map
          gaussianSignalScore ⊗ₘ
            gaussianSignalPosteriorKernel mean priorVariance noiseVariance := by
    rw [show (gaussianSignalPair mean priorVariance noiseVariance).map
        gaussianSignalScore =
        gaussianReal mean (priorVariance + noiseVariance).toNNReal by
      exact gaussianSignalPair_score_marginal
        mean priorVariance noiseVariance hpriorVariance hnoiseVariance]
    exact gaussianSignalPair_score_latent_joint_factorization
      mean priorVariance noiseVariance hpriorVariance hnoiseVariance
  letI : IsFiniteKernel
      (gaussianSignalPosteriorKernel mean priorVariance noiseVariance) := by
    unfold gaussianSignalPosteriorKernel
    infer_instance
  have hcond := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (μ := gaussianSignalPair mean priorVariance noiseVariance)
    (X := gaussianSignalScore) (Y := fun pair : ℝ × ℝ => pair.1)
    (κ := gaussianSignalPosteriorKernel mean priorVariance noiseVariance)
    (by fun_prop) (by fun_prop) hjoint
  filter_upwards [hcond] with score hscore
  simpa only [gaussianSignalPosteriorKernel_apply] using hscore

end

end Probability
end AppliedModelingLib

import AppliedModelingLib.Foundations.Probability.FiniteGaussianSignalKernelRCD

/-!
# Marginal laws of finite Gaussian posterior means

This module complements the source-law finite Gaussian conditioning induction.
It exposes the independent residual noise in a base-indexed Gaussian kernel
and uses that transport to track the marginal law of each constructed
conditional mean.  The results are source-law statements: no posterior-mean
law is supplied as a model field or as an equality premise.
-/

namespace AppliedModelingLib
namespace Probability

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

private theorem gaussianLocationKernel_prod_eq_compProd
    {α : Type*} [MeasurableSpace α]
    (mean : α → ℝ) (hmean : Measurable mean) (ν : Measure ℝ) [SFinite ν] :
    (Kernel.deterministic mean hmean ×ₖ Kernel.const α ν) =
      Kernel.deterministic mean hmean ⊗ₖ Kernel.const (α × ℝ) ν := by
  ext a target htarget
  rw [Kernel.prod_apply, Kernel.compProd_apply htarget,
    Kernel.deterministic_apply]
  simp only [Kernel.const_apply]
  rw [lintegral_dirac, Measure.dirac_prod,
    Measure.map_apply measurable_prodMk_left htarget]

/-- A base-indexed Gaussian kernel can be recentered at its measurable mean.
The resulting mean/residual pair is exactly a product measure: this makes the
independence used by the finite posterior-mean induction explicit. -/
theorem gaussianLocationKernel_map_mean_residual
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (mean : α → ℝ) (hmean : Measurable mean) (variance : ℝ≥0) :
    (μ ⊗ₘ gaussianLocationKernel mean hmean variance).map
        (fun pair => (mean pair.1, pair.2 - mean pair.1)) =
      (μ.map mean).prod (gaussianReal 0 variance) := by
  let ν : Measure ℝ := gaussianReal 0 variance
  let κ : Kernel α ℝ := Kernel.deterministic mean hmean
  let η : Kernel (α × ℝ) ℝ := Kernel.const (α × ℝ) ν
  have hκ : IsMarkovKernel κ := by
    dsimp [κ]
    infer_instance
  have hν : IsProbabilityMeasure ν := by
    dsimp [ν]
    infer_instance
  have hη : IsMarkovKernel η := by
    dsimp [η]
    infer_instance
  have hprod : κ ×ₖ Kernel.const α ν = κ ⊗ₖ η := by
    dsimp [κ, η]
    exact gaussianLocationKernel_prod_eq_compProd mean hmean ν
  have hloc : gaussianLocationKernel mean hmean variance =
      (κ ⊗ₖ η).map (fun pair : ℝ × ℝ => pair.1 + pair.2) := by
    simp only [gaussianLocationKernel, κ, η, ν]
    rw [← hprod]
  have hassoc :
      (μ ⊗ₘ (κ ⊗ₖ η)).map MeasurableEquiv.prodAssoc.symm = μ ⊗ₘ κ ⊗ₘ η :=
    Measure.compProd_assoc
  let pairMean : α → α × ℝ := fun a => (a, mean a)
  have hpairMean : Measurable pairMean := by
    dsimp [pairMean]
    fun_prop
  calc
    (μ ⊗ₘ gaussianLocationKernel mean hmean variance).map
        (fun pair => (mean pair.1, pair.2 - mean pair.1)) =
        (μ ⊗ₘ (κ ⊗ₖ η)).map
          (fun pair : α × (ℝ × ℝ) =>
            (mean pair.1, (pair.2.1 + pair.2.2) - mean pair.1)) := by
          rw [hloc, Measure.compProd_map (by fun_prop)]
          rw [Measure.map_map (by fun_prop) (by fun_prop)]
          rfl
    _ = (μ ⊗ₘ κ ⊗ₘ η).map
          (fun triple : (α × ℝ) × ℝ =>
            (mean triple.1.1, (triple.1.2 + triple.2) - mean triple.1.1)) := by
          rw [← hassoc]
          rw [Measure.map_map (by fun_prop) (by fun_prop)]
          rfl
    _ = ((μ ⊗ₘ κ).prod ν).map
          (fun triple : (α × ℝ) × ℝ =>
            (mean triple.1.1, (triple.1.2 + triple.2) - mean triple.1.1)) := by
          change (μ ⊗ₘ κ ⊗ₘ Kernel.const (α × ℝ) ν).map _ = _
          rw [Measure.compProd_const]
    _ = ((μ.map pairMean).prod ν).map
          (fun triple : (α × ℝ) × ℝ =>
            (mean triple.1.1, (triple.1.2 + triple.2) - mean triple.1.1)) := by
          rw [Measure.compProd_deterministic hmean]
    _ = ((μ.prod ν).map (Prod.map pairMean id)).map
          (fun triple : (α × ℝ) × ℝ =>
            (mean triple.1.1, (triple.1.2 + triple.2) - mean triple.1.1)) := by
          rw [← Measure.map_prod_map μ ν hpairMean measurable_id]
          simp
    _ = (μ.prod ν).map (Prod.map mean id) := by
          rw [Measure.map_map (by fun_prop) (by fun_prop)]
          congr 1
          funext primitive
          rcases primitive with ⟨a, z⟩
          simp [pairMean]
    _ = (μ.map mean).prod (ν.map id) := by
          rw [Measure.map_prod_map μ ν hmean measurable_id]
    _ = (μ.map mean).prod (gaussianReal 0 variance) := by
          simp [ν]

/-- If the current conditional mean is Gaussian, then updating a literal
Gaussian base factorization by one independent additive score has a Gaussian
new conditional mean.  The variance increment is displayed explicitly and
is positive whenever both the residual and score-noise variances are positive.
-/
theorem gaussianLocationKernel_update_mean_map
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (mean : α → ℝ) (hmean : Measurable mean)
    (priorMean meanVariance residualVariance noiseVariance : ℝ)
    (hmeanVariance : 0 ≤ meanVariance)
    (hresidualVariance : 0 < residualVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hmeanLaw : μ.map mean = gaussianReal priorMean meanVariance.toNNReal) :
    let newBaseLaw := μ ⊗ₘ gaussianLocationKernel mean hmean
      (residualVariance + noiseVariance).toNNReal
    let newMean : α × ℝ → ℝ := fun baseScore =>
      gaussianSignalWeight residualVariance noiseVariance * baseScore.2 +
        gaussianSignalPriorWeight residualVariance noiseVariance * mean baseScore.1
    newBaseLaw.map newMean =
      gaussianReal priorMean
        (meanVariance +
          (gaussianSignalWeight residualVariance noiseVariance)^2 *
            (residualVariance + noiseVariance)).toNNReal := by
  intro newBaseLaw newMean
  let w : ℝ := gaussianSignalWeight residualVariance noiseVariance
  let p : ℝ := gaussianSignalPriorWeight residualVariance noiseVariance
  let scoreVariance : ℝ := residualVariance + noiseVariance
  have hscoreVariance : 0 < scoreVariance := by
    dsimp [scoreVariance]
    linarith
  have hweightSum : w + p = 1 := by
    dsimp [w, p, gaussianSignalWeight, gaussianSignalPriorWeight]
    field_simp [ne_of_gt hscoreVariance]
  have htransport := gaussianLocationKernel_map_mean_residual
    μ mean hmean scoreVariance.toNNReal
  letI : IsProbabilityMeasure (μ.map mean) :=
    Measure.isProbabilityMeasure_map hmean.aemeasurable
  letI : IsProbabilityMeasure (gaussianReal 0 scoreVariance.toNNReal) := by
    infer_instance
  let P : Measure (ℝ × ℝ) :=
    (μ.map mean).prod (gaussianReal 0 scoreVariance.toNNReal)
  have hX : P.map (fun pair : ℝ × ℝ => pair.1) =
      gaussianReal priorMean meanVariance.toNNReal := by
    dsimp [P]
    rw [Measure.map_fst_prod]
    simp [hmeanLaw]
  have hY : P.map (fun pair : ℝ × ℝ => w * pair.2) =
      gaussianReal 0 ((w ^ 2).toNNReal * scoreVariance.toNNReal) := by
    calc
      P.map (fun pair : ℝ × ℝ => w * pair.2) =
          (P.map Prod.snd).map (fun value : ℝ => w * value) := by
            rw [Measure.map_map (by fun_prop) measurable_snd]
            rfl
      _ = (gaussianReal 0 scoreVariance.toNNReal).map
          (fun value : ℝ => w * value) := by
            dsimp [P]
            rw [Measure.map_snd_prod]
            simp
      _ = gaussianReal 0 ((w ^ 2).toNNReal * scoreVariance.toNNReal) := by
            convert gaussianReal_map_const_mul
              (μ := (0 : ℝ)) (v := scoreVariance.toNNReal) w using 1
            apply (gaussianReal_ext_iff).2
            constructor
            · ring
            · apply Subtype.ext
              simp [Real.toNNReal_of_nonneg (sq_nonneg w)]
  have hXY : IndepFun (fun pair : ℝ × ℝ => pair.1)
      (fun pair : ℝ × ℝ => w * pair.2) P := by
    dsimp [P]
    exact ProbabilityTheory.indepFun_prod
      (μ := μ.map mean) (ν := gaussianReal 0 scoreVariance.toNNReal)
      (X := fun value : ℝ => value) (Y := fun value : ℝ => w * value)
      measurable_id (by fun_prop)
  have hsum := ProbabilityTheory.gaussianReal_add_gaussianReal_of_indepFun
    hXY hX hY
  have hvar :
      meanVariance.toNNReal + (w ^ 2).toNNReal * scoreVariance.toNNReal =
        (meanVariance + w ^ 2 * scoreVariance).toNNReal := by
    have htotal : 0 ≤ meanVariance + w ^ 2 * scoreVariance :=
      add_nonneg hmeanVariance
        (mul_nonneg (sq_nonneg w) hscoreVariance.le)
    apply Subtype.ext
    change (meanVariance.toNNReal : ℝ) +
        ((w ^ 2).toNNReal : ℝ) * (scoreVariance.toNNReal : ℝ) =
      ((meanVariance + w ^ 2 * scoreVariance).toNNReal : ℝ)
    rw [Real.coe_toNNReal meanVariance hmeanVariance,
      Real.coe_toNNReal (w ^ 2) (sq_nonneg w),
      Real.coe_toNNReal scoreVariance hscoreVariance.le,
      Real.coe_toNNReal (meanVariance + w ^ 2 * scoreVariance) htotal]
  calc
    newBaseLaw.map newMean =
        newBaseLaw.map (fun baseScore =>
          mean baseScore.1 + w * (baseScore.2 - mean baseScore.1)) := by
          congr 1
          funext baseScore
          change w * baseScore.2 + p * mean baseScore.1 =
            mean baseScore.1 + w * (baseScore.2 - mean baseScore.1)
          have hp : p = 1 - w := by linarith [hweightSum]
          rw [hp]
          ring
    _ = (newBaseLaw.map (fun baseScore =>
          (mean baseScore.1, baseScore.2 - mean baseScore.1))).map
          (fun pair : ℝ × ℝ => pair.1 + w * pair.2) := by
          rw [Measure.map_map (by fun_prop) (by fun_prop)]
          rfl
    _ = P.map (fun pair : ℝ × ℝ => pair.1 + w * pair.2) := by
          rw [show newBaseLaw = μ ⊗ₘ gaussianLocationKernel mean hmean
            scoreVariance.toNNReal by rfl]
          rw [htransport]
    _ = gaussianReal priorMean
        (meanVariance + w ^ 2 * scoreVariance).toNNReal := by
          simpa only [Pi.add_apply, add_zero, hvar] using hsum
    _ = gaussianReal priorMean
        (meanVariance +
          (gaussianSignalWeight residualVariance noiseVariance)^2 *
            (residualVariance + noiseVariance)).toNNReal := by
          rfl

/-- One finite-profile induction step that carries both the actual Gaussian
conditional-law factorization and the marginal law of its constructed
conditional mean. -/
theorem gaussianFiniteProfileLatentLaw_option_exists_gaussianLocationFactorization_with_meanLaw
    {Index : Type*} [Fintype Index]
    (priorMean priorVariance : ℝ) (noiseVariance : Option Index → ℝ)
    (hheadNoiseVariance : 0 < noiseVariance none)
    (htail : ∃ (baseLaw : Measure (Index → ℝ)) (mean : (Index → ℝ) → ℝ)
        (variance meanVariance : ℝ) (hmean : Measurable mean),
        IsProbabilityMeasure baseLaw ∧ 0 < variance ∧ 0 ≤ meanVariance ∧
          gaussianFiniteProfileLatentLaw priorMean priorVariance
            (fun index => noiseVariance (some index)) =
            baseLaw ⊗ₘ gaussianLocationKernel mean hmean variance.toNNReal ∧
          baseLaw.map mean = gaussianReal priorMean meanVariance.toNNReal) :
    ∃ (baseLaw : Measure (Option Index → ℝ))
        (mean : (Option Index → ℝ) → ℝ) (variance meanVariance : ℝ)
        (hmean : Measurable mean),
      IsProbabilityMeasure baseLaw ∧ 0 < variance ∧ 0 ≤ meanVariance ∧
        gaussianFiniteProfileLatentLaw priorMean priorVariance noiseVariance =
          baseLaw ⊗ₘ gaussianLocationKernel mean hmean variance.toNNReal ∧
        baseLaw.map mean = gaussianReal priorMean meanVariance.toNNReal := by
  rcases htail with ⟨tailBaseLaw, tailMean, tailVariance, tailMeanVariance,
    htailMean, htailBaseLaw, htailVariance, htailMeanVariance,
    htailFactorization, htailMeanLaw⟩
  letI : IsProbabilityMeasure tailBaseLaw := htailBaseLaw
  let scoreKernel : Kernel (Index → ℝ) ℝ :=
    gaussianLocationKernel tailMean htailMean
      (tailVariance + noiseVariance none).toNNReal
  let posteriorKernel : Kernel ((Index → ℝ) × ℝ) ℝ :=
    gaussianSignalPosteriorBaseKernel tailMean htailMean tailVariance
      (noiseVariance none)
  let newBaseLaw : Measure ((Index → ℝ) × ℝ) :=
    tailBaseLaw ⊗ₘ scoreKernel
  let newMean : (Index → ℝ) × ℝ → ℝ := fun profileScore =>
    gaussianSignalWeight tailVariance (noiseVariance none) * profileScore.2 +
      gaussianSignalPriorWeight tailVariance (noiseVariance none) *
        tailMean profileScore.1
  let newVariance : ℝ :=
    tailVariance * noiseVariance none /
      (tailVariance + noiseVariance none)
  let newMeanVariance : ℝ := tailMeanVariance +
    (gaussianSignalWeight tailVariance (noiseVariance none)) ^ 2 *
      (tailVariance + noiseVariance none)
  let profileSplit : (Option Index → ℝ) ≃ᵐ (Index → ℝ) × ℝ :=
    gaussianFiniteProfileOptionSplit Index
  have hnewMean : Measurable newMean := by
    dsimp [newMean]
    fun_prop
  have hnewVariance : 0 < newVariance := by
    dsimp [newVariance]
    exact div_pos (mul_pos htailVariance hheadNoiseVariance)
      (add_pos htailVariance hheadNoiseVariance)
  have hnewMeanVariance : 0 ≤ newMeanVariance := by
    dsimp [newMeanVariance]
    exact add_nonneg htailMeanVariance
      (mul_nonneg (sq_nonneg _) (add_nonneg htailVariance.le hheadNoiseVariance.le))
  letI : IsMarkovKernel scoreKernel :=
    gaussianLocationKernel_isMarkov tailMean htailMean
      (tailVariance + noiseVariance none).toNNReal
  letI : IsMarkovKernel posteriorKernel :=
    gaussianSignalPosteriorBaseKernel_isMarkov tailMean htailMean tailVariance
      (noiseVariance none)
  have hupdate :
      gaussianSignalExtendBaseLatentLaw
          (gaussianFiniteProfileLatentLaw priorMean priorVariance
            (fun index => noiseVariance (some index)))
          (noiseVariance none) =
        gaussianSignalBaseScoreLatentLaw tailBaseLaw tailMean htailMean
          tailVariance (noiseVariance none) :=
    gaussianSignalExtendBaseLatentLaw_eq_baseScoreLatentLaw
      tailBaseLaw tailMean htailMean tailVariance (noiseVariance none)
      (gaussianFiniteProfileLatentLaw priorMean priorVariance
        (fun index => noiseVariance (some index))) htailFactorization
  have hnewFactorization :
      gaussianSignalExtendBaseLatentLaw
          (gaussianFiniteProfileLatentLaw priorMean priorVariance
            (fun index => noiseVariance (some index)))
          (noiseVariance none) =
        newBaseLaw ⊗ₘ gaussianLocationKernel newMean hnewMean
          newVariance.toNNReal := by
    calc
      gaussianSignalExtendBaseLatentLaw
          (gaussianFiniteProfileLatentLaw priorMean priorVariance
            (fun index => noiseVariance (some index)))
          (noiseVariance none) =
          gaussianSignalBaseScoreLatentLaw tailBaseLaw tailMean htailMean
            tailVariance (noiseVariance none) := hupdate
      _ = tailBaseLaw ⊗ₘ scoreKernel ⊗ₘ posteriorKernel := by
        exact gaussianSignalBaseScoreLatentLaw_factorization
          tailBaseLaw tailMean htailMean tailVariance (noiseVariance none)
          htailVariance hheadNoiseVariance
      _ = newBaseLaw ⊗ₘ gaussianLocationKernel newMean hnewMean
          newVariance.toNNReal := by
        dsimp [newBaseLaw, posteriorKernel, newMean, newVariance]
        rfl
  have hnewBaseLaw : IsProbabilityMeasure newBaseLaw := by
    dsimp [newBaseLaw]
    infer_instance
  letI : IsProbabilityMeasure newBaseLaw := hnewBaseLaw
  have hnewMeanLaw : newBaseLaw.map newMean =
      gaussianReal priorMean newMeanVariance.toNNReal := by
    simpa [newBaseLaw, scoreKernel, newMean, newMeanVariance] using
      (gaussianLocationKernel_update_mean_map tailBaseLaw tailMean htailMean
        priorMean tailMeanVariance tailVariance (noiseVariance none)
        htailMeanVariance htailVariance hheadNoiseVariance htailMeanLaw)
  refine ⟨newBaseLaw.map profileSplit.symm, newMean ∘ profileSplit,
    newVariance, newMeanVariance, hnewMean.comp profileSplit.measurable, ?_,
    hnewVariance, hnewMeanVariance, ?_, ?_⟩
  · exact Measure.isProbabilityMeasure_map profileSplit.symm.measurable.aemeasurable
  · have hround :
      ((gaussianFiniteProfileLatentLaw priorMean priorVariance noiseVariance).map
          (Prod.map profileSplit id)).map (Prod.map profileSplit.symm id) =
        gaussianFiniteProfileLatentLaw priorMean priorVariance noiseVariance := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      have hfun :
          (Prod.map
            (profileSplit.symm : ((Index → ℝ) × ℝ) → (Option Index → ℝ))
            (id : ℝ → ℝ)) ∘
            (Prod.map
              (profileSplit : (Option Index → ℝ) → (Index → ℝ) × ℝ)
              (id : ℝ → ℝ)) =
            (id : ((Option Index → ℝ) × ℝ) → (Option Index → ℝ) × ℝ) := by
        funext profileSkill
        rcases profileSkill with ⟨profile, skill⟩
        change (profileSplit.symm (profileSplit profile), skill) = (profile, skill)
        simp
      rw [hfun, Measure.map_id]
    have hoptionStep :
        (gaussianFiniteProfileLatentLaw priorMean priorVariance noiseVariance).map
            (Prod.map profileSplit id) =
          gaussianSignalExtendBaseLatentLaw
            (gaussianFiniteProfileLatentLaw priorMean priorVariance
              (fun index => noiseVariance (some index)))
            (noiseVariance none) := by
      simpa [profileSplit] using
        (gaussianFiniteProfileLatentLaw_option_eq_extend
          priorMean priorVariance noiseVariance)
    calc
      gaussianFiniteProfileLatentLaw priorMean priorVariance noiseVariance =
          ((gaussianFiniteProfileLatentLaw priorMean priorVariance noiseVariance).map
            (Prod.map profileSplit id)).map (Prod.map profileSplit.symm id) :=
            hround.symm
      _ = (gaussianSignalExtendBaseLatentLaw
            (gaussianFiniteProfileLatentLaw priorMean priorVariance
              (fun index => noiseVariance (some index)))
            (noiseVariance none)).map (Prod.map profileSplit.symm id) := by
            rw [hoptionStep]
      _ = (newBaseLaw ⊗ₘ gaussianLocationKernel newMean hnewMean
            newVariance.toNNReal).map (Prod.map profileSplit.symm id) := by
            rw [hnewFactorization]
      _ = newBaseLaw.map profileSplit.symm ⊗ₘ
          gaussianLocationKernel (newMean ∘ profileSplit)
            (hnewMean.comp profileSplit.measurable) newVariance.toNNReal := by
            exact gaussianLocationFactorization_map_measurableEquiv
              profileSplit.symm newBaseLaw newMean hnewMean newVariance.toNNReal
  · calc
      (newBaseLaw.map profileSplit.symm).map (newMean ∘ profileSplit) =
          newBaseLaw.map ((newMean ∘ profileSplit) ∘ profileSplit.symm) := by
            rw [Measure.map_map (hnewMean.comp profileSplit.measurable)
              profileSplit.symm.measurable]
      _ = newBaseLaw.map newMean := by
            rw [show ((newMean ∘ profileSplit) ∘ profileSplit.symm) = newMean by
              funext profileScore
              simp]
      _ = gaussianReal priorMean newMeanVariance.toNNReal := hnewMeanLaw

/-- Every finite literal Gaussian profile has a source-derived conditional
Gaussian factorization whose conditional-mean pushforward is itself Gaussian.
The conclusion includes no assumed posterior formula or named model law. -/
theorem gaussianFiniteProfileLatentLaw_exists_gaussianLocationFactorization_with_meanLaw
    {Index : Type u} [Fintype Index]
    (priorMean priorVariance : ℝ) (hpriorVariance : 0 < priorVariance)
    (noiseVariance : Index → ℝ)
    (hnoiseVariance : ∀ index, 0 < noiseVariance index) :
    ∃ (baseLaw : Measure (Index → ℝ)) (mean : (Index → ℝ) → ℝ)
        (variance meanVariance : ℝ) (hmean : Measurable mean),
      IsProbabilityMeasure baseLaw ∧ 0 < variance ∧ 0 ≤ meanVariance ∧
        gaussianFiniteProfileLatentLaw priorMean priorVariance noiseVariance =
          baseLaw ⊗ₘ gaussianLocationKernel mean hmean variance.toNNReal ∧
        baseLaw.map mean = gaussianReal priorMean meanVariance.toNNReal := by
  classical
  let P : ∀ (Index : Type u) [Fintype Index], Prop :=
    fun Index _ => ∀ (noise : Index → ℝ), (∀ index, 0 < noise index) →
      ∃ (baseLaw : Measure (Index → ℝ)) (mean : (Index → ℝ) → ℝ)
          (variance meanVariance : ℝ) (hmean : Measurable mean),
        IsProbabilityMeasure baseLaw ∧ 0 < variance ∧ 0 ≤ meanVariance ∧
          gaussianFiniteProfileLatentLaw priorMean priorVariance noise =
            baseLaw ⊗ₘ gaussianLocationKernel mean hmean variance.toNNReal ∧
          baseLaw.map mean = gaussianReal priorMean meanVariance.toNNReal
  refine Fintype.induction_empty_option (P := P) ?_ ?_ ?_ Index
    noiseVariance hnoiseVariance
  · intro α β instβ e ih noise hnoise
    letI : Fintype α := Fintype.ofEquiv β e.symm
    let profileReindex : (α → ℝ) ≃ᵐ (β → ℝ) :=
      gaussianFiniteProfileReindex e
    have hsourceNoise : ∀ index : α, 0 < noise (e index) := by
      intro index
      exact hnoise (e index)
    rcases ih (fun index => noise (e index)) hsourceNoise with
      ⟨sourceBaseLaw, sourceMean, sourceVariance, sourceMeanVariance,
        hsourceMean, hsourceBaseLaw, hsourceVariance, hsourceMeanVariance,
        hsourceFactorization, hsourceMeanLaw⟩
    letI : IsProbabilityMeasure sourceBaseLaw := hsourceBaseLaw
    refine ⟨sourceBaseLaw.map profileReindex,
      sourceMean ∘ profileReindex.symm, sourceVariance, sourceMeanVariance,
      hsourceMean.comp profileReindex.symm.measurable,
      Measure.isProbabilityMeasure_map profileReindex.measurable.aemeasurable,
      hsourceVariance, hsourceMeanVariance, ?_, ?_⟩
    · calc
        gaussianFiniteProfileLatentLaw priorMean priorVariance noise =
            (gaussianFiniteProfileLatentLaw priorMean priorVariance
              (fun index => noise (e index))).map
                (Prod.map profileReindex id) := by
                  simpa [profileReindex] using
                    (gaussianFiniteProfileLatentLaw_reindex
                      e priorMean priorVariance noise).symm
        _ = (sourceBaseLaw ⊗ₘ gaussianLocationKernel sourceMean
            hsourceMean sourceVariance.toNNReal).map
              (Prod.map profileReindex id) := by
                rw [hsourceFactorization]
        _ = sourceBaseLaw.map profileReindex ⊗ₘ
            gaussianLocationKernel (sourceMean ∘ profileReindex.symm)
              (hsourceMean.comp profileReindex.symm.measurable)
              sourceVariance.toNNReal := by
                exact gaussianLocationFactorization_map_measurableEquiv
                  profileReindex sourceBaseLaw sourceMean hsourceMean
                  sourceVariance.toNNReal
    · calc
        (sourceBaseLaw.map profileReindex).map
            (sourceMean ∘ profileReindex.symm) =
            sourceBaseLaw.map ((sourceMean ∘ profileReindex.symm) ∘ profileReindex) := by
              rw [Measure.map_map
                (hsourceMean.comp profileReindex.symm.measurable)
                profileReindex.measurable]
        _ = sourceBaseLaw.map sourceMean := by
              congr 1
              funext profile
              simp
        _ = gaussianReal priorMean sourceMeanVariance.toNNReal := hsourceMeanLaw
  · intro noise hnoise
    let emptyProfile : PEmpty → ℝ := fun index => nomatch index
    have hnoiseEq : noise = (fun index : PEmpty => nomatch index) :=
      Subsingleton.elim _ _
    let prior : Measure ℝ := gaussianReal priorMean priorVariance.toNNReal
    have hprior : IsProbabilityMeasure prior := by
      dsimp [prior]
      infer_instance
    refine ⟨Measure.dirac emptyProfile, (fun _ => priorMean), priorVariance, 0,
      measurable_const, Measure.dirac.isProbabilityMeasure, hpriorVariance,
      le_rfl, ?_, ?_⟩
    · have hleft :
        gaussianFiniteProfileLatentLaw priorMean priorVariance
            (fun index : PEmpty => nomatch index) =
          (Measure.dirac emptyProfile).prod prior := by
          unfold gaussianFiniteProfileLatentLaw
          rw [Measure.pi_of_empty]
          rw [Measure.prod_dirac]
          rw [Measure.map_map (by fun_prop) (by fun_prop)]
          rw [Measure.dirac_prod]
          congr 1
          funext skill
          apply Prod.ext
          · exact Subsingleton.elim _ _
          · rfl
      letI : IsMarkovKernel
          (gaussianLocationKernel (fun _ : PEmpty → ℝ => priorMean)
            measurable_const priorVariance.toNNReal) :=
        gaussianLocationKernel_isMarkov (fun _ : PEmpty → ℝ => priorMean)
          measurable_const priorVariance.toNNReal
      rw [hnoiseEq]
      rw [hleft]
      symm
      ext target htarget
      rw [Measure.compProd_apply htarget, lintegral_dirac,
        gaussianLocationKernel_apply, Measure.dirac_prod,
        Measure.map_apply measurable_prodMk_left htarget]
    · simp [gaussianReal_zero_var]
  · intro α instα ih noise hnoise
    exact gaussianFiniteProfileLatentLaw_option_exists_gaussianLocationFactorization_with_meanLaw
      priorMean priorVariance noise (hnoise none)
      (ih (fun index => noise (some index)) (fun index => hnoise (some index)))

end

end Probability
end AppliedModelingLib

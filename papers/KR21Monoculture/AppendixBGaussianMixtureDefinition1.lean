import KR21Monoculture.AppendixBSourceScaledSmoothing
import KR21Monoculture.W11Definition1Correction
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Appendix B Gaussian-mixture Definition 1 bridge

This module develops the analytic facts needed to certify the paper's finite
Gaussian-mixture smoothings through the corrected Appendix A `W^{1,1}` route.
It is intentionally separate from the Appendix B payoff and source-scaling
modules, so every density and source-law bridge remains individually reviewable.
-/

open AppliedModelingLib MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace KR21Monoculture

noncomputable section

local instance : MeasurableSpace AppendixB1NoiseAtom := ⊤
local instance : DiscreteMeasurableSpace AppendixB1NoiseAtom :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

local instance : MeasurableSpace AppendixB2NoiseAtom := ⊤
local instance : DiscreteMeasurableSpace AppendixB2NoiseAtom :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- The variance of `s * Z` for a standard Gaussian `Z`. -/
def appendixBGaussianVariance (s : ℝ) : ℝ≥0 :=
  ⟨s ^ 2, sq_nonneg s⟩

theorem appendixBGaussianVariance_ne_zero {s : ℝ} (hs : 0 < s) :
    appendixBGaussianVariance s ≠ 0 := by
  dsimp [appendixBGaussianVariance]
  apply ne_of_gt
  exact sq_pos_of_pos hs

/-- The derivative of a nondegenerate real Gaussian density. -/
noncomputable def appendixBGaussianPDFDerivative
    (mean : ℝ) (variance : ℝ≥0) (x : ℝ) : ℝ :=
  -((x - mean) / variance) * ProbabilityTheory.gaussianPDFReal mean variance x

theorem gaussianPDFReal_contDiff
    (mean : ℝ) (variance : ℝ≥0) :
    ContDiff ℝ ⊤ (ProbabilityTheory.gaussianPDFReal mean variance) := by
  rw [ProbabilityTheory.gaussianPDFReal_def]
  fun_prop

theorem gaussianPDFReal_absolutelyContinuousOnInterval
    (mean : ℝ) (variance : ℝ≥0) (a b : ℝ) :
    AbsolutelyContinuousOnInterval
      (ProbabilityTheory.gaussianPDFReal mean variance) a b := by
  have hdiff : ContDiff ℝ 1 (ProbabilityTheory.gaussianPDFReal mean variance) :=
    (gaussianPDFReal_contDiff mean variance).of_le (by simp)
  exact hdiff.contDiffOn.absolutelyContinuousOnInterval

theorem gaussianPDFReal_hasDerivAt
    (mean : ℝ) (variance : ℝ≥0) (hvariance : variance ≠ 0) (x : ℝ) :
    HasDerivAt (ProbabilityTheory.gaussianPDFReal mean variance)
      (appendixBGaussianPDFDerivative mean variance x) x := by
  rw [ProbabilityTheory.gaussianPDFReal_def]
  have hinner : HasDerivAt
      (fun y : ℝ => -(y - mean) ^ 2 / (2 * (variance : ℝ)))
      (-(2 * (x - mean)) / (2 * (variance : ℝ))) x := by
    convert (((hasDerivAt_id x).sub_const mean).pow 2).neg.div_const
      (2 * (variance : ℝ)) using 1 <;> simp only [id_eq] <;> ring
  have hexp := (Real.hasDerivAt_exp (-(x - mean) ^ 2 / (2 * (variance : ℝ)))).comp
    x hinner
  have hsqrt : Real.sqrt (2 * Real.pi * (variance : ℝ)) ≠ 0 := by
    apply ne_of_gt
    positivity
  let c : ℝ := (Real.sqrt (2 * Real.pi * (variance : ℝ)))⁻¹
  have houter : HasDerivAt
      (fun y : ℝ => c * Real.exp (-(y - mean) ^ 2 / (2 * (variance : ℝ))))
      (c * (Real.exp (-(x - mean) ^ 2 / (2 * (variance : ℝ))) *
        (-(2 * (x - mean)) / (2 * (variance : ℝ))))) x :=
    (hasDerivAt_const_mul c).comp x hexp
  change HasDerivAt
    (fun y : ℝ => c * Real.exp (-(y - mean) ^ 2 / (2 * (variance : ℝ))) )
    (appendixBGaussianPDFDerivative mean variance x) x
  convert houter using 1
  simp only [appendixBGaussianPDFDerivative, ProbabilityTheory.gaussianPDFReal, c]
  field_simp [hvariance, hsqrt]

/-- The real density of a finite mixture of equally scaled Gaussian components. -/
noncomputable def finiteGaussianMixtureDensity
    {α : Type*} [Fintype α] (law : PMF α) (center : α → ℝ) (s : ℝ) (x : ℝ) : ℝ :=
  ∑ a, (law a).toReal * ProbabilityTheory.gaussianPDFReal
    (center a) (appendixBGaussianVariance s) x

theorem finiteGaussianMixtureDensity_nonneg
    {α : Type*} [Fintype α] (law : PMF α) (center : α → ℝ) (s x : ℝ) :
    0 ≤ finiteGaussianMixtureDensity law center s x := by
  unfold finiteGaussianMixtureDensity
  apply Finset.sum_nonneg
  intro a _
  exact mul_nonneg ENNReal.toReal_nonneg
    (ProbabilityTheory.gaussianPDFReal_nonneg _ _ _)

theorem measurable_finiteGaussianMixtureDensity
    {α : Type*} [Fintype α] (law : PMF α) (center : α → ℝ) (s : ℝ) :
    Measurable (finiteGaussianMixtureDensity law center s) := by
  unfold finiteGaussianMixtureDensity
  fun_prop

/-- An affine image of a standard Gaussian has the expected component law. -/
theorem gaussianReal_map_center_add_scaled_standard
    (center s : ℝ) :
    (ProbabilityTheory.gaussianReal 0 1).map (fun z : ℝ => center + s * z) =
      ProbabilityTheory.gaussianReal center (appendixBGaussianVariance s) := by
  calc
    (ProbabilityTheory.gaussianReal 0 1).map (fun z : ℝ => center + s * z) =
        ((ProbabilityTheory.gaussianReal 0 1).map (fun z : ℝ => s * z)).map
          (fun y : ℝ => center + y) := by
      symm
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = ProbabilityTheory.gaussianReal center (appendixBGaussianVariance s) := by
      rw [ProbabilityTheory.gaussianReal_map_const_mul,
        ProbabilityTheory.gaussianReal_map_const_add]
      simp only [mul_zero, zero_add]
      apply congrArg (ProbabilityTheory.gaussianReal center)
      apply Subtype.ext
      dsimp [appendixBGaussianVariance]
      change s ^ 2 * 1 = NNReal.toReal (⟨s ^ 2, _⟩ : ℝ≥0)
      change s ^ 2 * 1 = s ^ 2
      ring

/-- A selected component and an independent standard Gaussian induce its Gaussian law. -/
theorem finiteGaussianMixture_component_law
    {α : Type*} [MeasurableSpace α] (a : α) (center : α → ℝ)
    (hcenter : Measurable center) (s : ℝ) :
    ((Measure.dirac a).prod (ProbabilityTheory.gaussianReal 0 1)).map
        (fun z : α × ℝ => center z.1 + s * z.2) =
      ProbabilityTheory.gaussianReal (center a) (appendixBGaussianVariance s) := by
  have hscore : Measurable (fun z : α × ℝ => center z.1 + s * z.2) :=
    (hcenter.comp measurable_fst).add (measurable_const.mul measurable_snd)
  rw [Measure.dirac_prod, Measure.map_map hscore (by fun_prop)]
  exact gaussianReal_map_center_add_scaled_standard (center a) s

/-- Expanding a finite latent component draw yields the corresponding finite Gaussian mixture. -/
theorem finiteGaussianMixture_latentLaw_eq_sum_components
    {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (law : PMF α) (center : α → ℝ) (hcenter : Measurable center) (s : ℝ) :
    (law.toMeasure.prod (ProbabilityTheory.gaussianReal 0 1)).map
        (fun z : α × ℝ => center z.1 + s * z.2) =
      ∑ a, law a • ProbabilityTheory.gaussianReal (center a)
        (appendixBGaussianVariance s) := by
  have hscore : Measurable (fun z : α × ℝ => center z.1 + s * z.2) :=
    (hcenter.comp measurable_fst).add (measurable_const.mul measurable_snd)
  rw [← Measure.sum_smul_dirac law.toMeasure, Measure.prod_sum_left,
    Measure.map_sum hscore.aemeasurable]
  simp_rw [Measure.prod_smul_left, Measure.map_smul]
  rw [Measure.sum_fintype]
  apply Finset.sum_congr rfl
  intro a _
  rw [PMF.toMeasure_apply_singleton law a (measurableSet_singleton a)]
  exact congrArg (law a • ·)
    (finiteGaussianMixture_component_law a center hcenter s)

/-- The ENNReal density of the finite mixture is the weighted sum of component densities. -/
theorem ennreal_finiteGaussianMixtureDensity
    {α : Type*} [Fintype α] (law : PMF α) (center : α → ℝ) (s x : ℝ) :
    ENNReal.ofReal (finiteGaussianMixtureDensity law center s x) =
      ∑ a, law a * ProbabilityTheory.gaussianPDF
        (center a) (appendixBGaussianVariance s) x := by
  unfold finiteGaussianMixtureDensity
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro a _
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (law.apply_ne_top a)]
    rfl
  · intro a _
    exact mul_nonneg ENNReal.toReal_nonneg
      (ProbabilityTheory.gaussianPDFReal_nonneg _ _ _)

/-- A weighted positive-variance Gaussian component is its displayed density law. -/
theorem finiteGaussianMixture_weighted_component_eq_withDensity
    {α : Type*} (law : PMF α) (center : α → ℝ) (s : ℝ)
    (hs : 0 < s) (a : α) :
    law a • ProbabilityTheory.gaussianReal (center a) (appendixBGaussianVariance s) =
      volume.withDensity (fun x => law a * ProbabilityTheory.gaussianPDF
        (center a) (appendixBGaussianVariance s) x) := by
  rw [ProbabilityTheory.gaussianReal_of_var_ne_zero _
    (appendixBGaussianVariance_ne_zero hs)]
  symm
  simpa only [Pi.smul_apply, smul_eq_mul] using
    (withDensity_smul (μ := volume) (law a)
      (ProbabilityTheory.measurable_gaussianPDF _ _))

/-- The finite weighted Gaussian component sum is the source density law. -/
theorem finiteGaussianMixture_sum_components_eq_baseNoiseLaw
    {α : Type*} [Fintype α] (law : PMF α) (center : α → ℝ) (s : ℝ)
    (hs : 0 < s) :
    (∑ a, law a • ProbabilityTheory.gaussianReal (center a)
      (appendixBGaussianVariance s)) =
      w11BaseNoiseLaw (finiteGaussianMixtureDensity law center s) := by
  calc
    (∑ a, law a • ProbabilityTheory.gaussianReal (center a)
        (appendixBGaussianVariance s)) =
        ∑ a, volume.withDensity (fun x => law a * ProbabilityTheory.gaussianPDF
          (center a) (appendixBGaussianVariance s) x) := by
      apply Finset.sum_congr rfl
      intro a _
      exact finiteGaussianMixture_weighted_component_eq_withDensity law center s hs a
    _ = Measure.sum (fun a => volume.withDensity
        (fun x => law a * ProbabilityTheory.gaussianPDF
          (center a) (appendixBGaussianVariance s) x)) := by
      symm
      exact Measure.sum_fintype _
    _ = volume.withDensity (∑' a, fun x => law a * ProbabilityTheory.gaussianPDF
        (center a) (appendixBGaussianVariance s) x) := by
      symm
      apply withDensity_tsum
      intro a
      exact measurable_const.mul (ProbabilityTheory.measurable_gaussianPDF _ _)
    _ = volume.withDensity (fun x => ∑ a, law a * ProbabilityTheory.gaussianPDF
        (center a) (appendixBGaussianVariance s) x) := by
      congr 1
      funext x
      rw [tsum_fintype]
      simp only [Finset.sum_apply]
    _ = w11BaseNoiseLaw (finiteGaussianMixtureDensity law center s) := by
      unfold w11BaseNoiseLaw
      congr 1
      funext x
      symm
      exact ennreal_finiteGaussianMixtureDensity law center s x

/-- The latent finite-component-plus-Gaussian experiment is exactly the mixture density law. -/
theorem finiteGaussianMixture_latentLaw_eq_baseNoiseLaw
    {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (law : PMF α) (center : α → ℝ) (hcenter : Measurable center) (s : ℝ)
    (hs : 0 < s) :
    (law.toMeasure.prod (ProbabilityTheory.gaussianReal 0 1)).map
        (fun z : α × ℝ => center z.1 + s * z.2) =
      w11BaseNoiseLaw (finiteGaussianMixtureDensity law center s) := by
  calc
    (law.toMeasure.prod (ProbabilityTheory.gaussianReal 0 1)).map
        (fun z : α × ℝ => center z.1 + s * z.2) =
        ∑ a, law a • ProbabilityTheory.gaussianReal (center a)
          (appendixBGaussianVariance s) :=
      finiteGaussianMixture_latentLaw_eq_sum_components law center hcenter s
    _ = w11BaseNoiseLaw (finiteGaussianMixtureDensity law center s) :=
      finiteGaussianMixture_sum_components_eq_baseNoiseLaw law center s hs

/-- The library finite-PMF product has the literal product measure as its law. -/
theorem pmfProd_toMeasure_eq_prod
    {α β : Type*} [Fintype α] [Fintype β]
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (μ : PMF α) (ν : PMF β) :
    (AppliedModelingLib.pmfProd μ ν).toMeasure = μ.toMeasure.prod ν.toMeasure := by
  apply Measure.ext_iff_singleton.mpr
  intro p
  rcases p with ⟨a, b⟩
  rw [PMF.toMeasure_apply_singleton (AppliedModelingLib.pmfProd μ ν) (a, b)
      (measurableSet_singleton _), AppliedModelingLib.pmfProd_apply,
    ← Set.singleton_prod_singleton, Measure.prod_prod,
    PMF.toMeasure_apply_singleton μ a (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton ν b (measurableSet_singleton _)]

/-- Reindex the explicit three-coordinate product carrier as `Candidate 1 → α`. -/
noncomputable def tripleToCandidateMeasurableEquiv
    (α : Type*) [MeasurableSpace α] :
    ((α × α) × α) ≃ᵐ (Candidate 1 → α) :=
  (MeasurableEquiv.prodAssoc : ((α × α) × α) ≃ᵐ α × (α × α)).trans
    ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl α)
      (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => α)).symm).trans
      (MeasurableEquiv.piFinSuccAbove (fun _ : Candidate 1 => α) 0).symm)

/-- The literal coordinate map behind `tripleToCandidateMeasurableEquiv`. -/
def tripleToCandidateFunction {α : Type*} (z : (α × α) × α) : Candidate 1 → α
  | 0 => z.1.1
  | 1 => z.1.2
  | _ => z.2

@[simp] theorem tripleToCandidateFunction_zero {α : Type*} (z : (α × α) × α) :
    tripleToCandidateFunction z 0 = z.1.1 := rfl

@[simp] theorem tripleToCandidateFunction_one {α : Type*} (z : (α × α) × α) :
    tripleToCandidateFunction z 1 = z.1.2 := rfl

@[simp] theorem tripleToCandidateFunction_two {α : Type*} (z : (α × α) × α) :
    tripleToCandidateFunction z 2 = z.2 := rfl

theorem tripleToCandidateMeasurableEquiv_apply_eq_function
    {α : Type*} [MeasurableSpace α] (z : (α × α) × α) :
    tripleToCandidateMeasurableEquiv α z = tripleToCandidateFunction z := by
  funext i
  fin_cases i <;>
    simp [tripleToCandidateMeasurableEquiv, tripleToCandidateFunction,
      MeasurableEquiv.piFinTwo, MeasurableEquiv.piFinSuccAbove,
      MeasurableEquiv.prodCongr, MeasurableEquiv.prodAssoc,
      MeasurableEquiv.refl, Equiv.prodCongr, Equiv.prodAssoc,
      piFinTwoEquiv, Fin.insertNthEquiv]
  all_goals rfl

/-- The displayed triple reindexing preserves an iid three-coordinate product law. -/
theorem measurePreserving_tripleToCandidateMeasurableEquiv
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] :
    MeasurePreserving (tripleToCandidateMeasurableEquiv α)
      ((μ.prod μ).prod μ) (Measure.pi (fun _ : Candidate 1 => μ)) := by
  letI : ∀ _ : Fin 2, SigmaFinite μ := fun _ => inferInstance
  letI : ∀ _ : Candidate 1, SigmaFinite μ := fun _ => inferInstance
  let eAssoc : ((α × α) × α) ≃ᵐ α × (α × α) := MeasurableEquiv.prodAssoc
  let eTwo : (Fin 2 → α) ≃ᵐ α × α :=
    MeasurableEquiv.piFinTwo (fun _ : Fin 2 => α)
  let eMiddle : α × (α × α) ≃ᵐ α × (Fin 2 → α) :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.refl α) eTwo.symm
  let eLast : (Candidate 1 → α) ≃ᵐ α × (Fin 2 → α) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Candidate 1 => α) 0
  have hAssoc : MeasurePreserving eAssoc ((μ.prod μ).prod μ)
      (μ.prod (μ.prod μ)) :=
    measurePreserving_prodAssoc μ μ μ
  have hTwo : MeasurePreserving eTwo
      (Measure.pi (fun _ : Fin 2 => μ)) (μ.prod μ) :=
    measurePreserving_piFinTwo (fun _ : Fin 2 => μ)
  have hMiddle : MeasurePreserving eMiddle (μ.prod (μ.prod μ))
      (μ.prod (Measure.pi (fun _ : Fin 2 => μ))) := by
    simpa [eMiddle, eTwo] using
      (MeasurePreserving.id μ).prod (MeasurePreserving.symm eTwo hTwo)
  have hLast : MeasurePreserving eLast
      (Measure.pi (fun _ : Candidate 1 => μ))
      (μ.prod (Measure.pi (fun _ : Fin 2 => μ))) :=
    measurePreserving_piFinSuccAbove (fun _ : Candidate 1 => μ) 0
  simpa [tripleToCandidateMeasurableEquiv, eAssoc, eMiddle, eLast] using
    hAssoc.trans (hMiddle.trans (MeasurePreserving.symm eLast hLast))

/-- The B.1 one-coordinate Gaussian-mixture density. -/
noncomputable def appendixB1GaussianMixtureDensity (s : ℝ) : ℝ → ℝ :=
  finiteGaussianMixtureDensity appendixB1NoisePMF appendixB1NoiseValue s

/-- The B.2 one-coordinate Gaussian-mixture density for the fixed source noise. -/
noncomputable def appendixB2GaussianMixtureDensity (s : ℝ) : ℝ → ℝ :=
  finiteGaussianMixtureDensity appendixB2NoisePMF appendixB2NoiseValue s

theorem appendixB1GaussianMixture_scalar_latentLaw_eq_densityLaw
    (s : ℝ) (hs : 0 < s) :
    (appendixB1NoisePMF.toMeasure.prod (ProbabilityTheory.gaussianReal 0 1)).map
        (fun z : AppendixB1NoiseAtom × ℝ => appendixB1NoiseValue z.1 + s * z.2) =
      w11BaseNoiseLaw (appendixB1GaussianMixtureDensity s) := by
  exact finiteGaussianMixture_latentLaw_eq_baseNoiseLaw appendixB1NoisePMF
    appendixB1NoiseValue (measurable_of_finite _) s hs

theorem appendixB2GaussianMixture_scalar_latentLaw_eq_densityLaw
    (s : ℝ) (hs : 0 < s) :
    (appendixB2NoisePMF.toMeasure.prod (ProbabilityTheory.gaussianReal 0 1)).map
        (fun z : AppendixB2NoiseAtom × ℝ => appendixB2NoiseValue z.1 + s * z.2) =
      w11BaseNoiseLaw (appendixB2GaussianMixtureDensity s) := by
  exact finiteGaussianMixture_latentLaw_eq_baseNoiseLaw appendixB2NoisePMF
    appendixB2NoiseValue (measurable_of_finite _) s hs

/-- Apply the finite-mixture affine score construction independently at every candidate. -/
noncomputable def finiteGaussianMixtureCandidateCoordinateMap
    {α : Type*} (center : α → ℝ) (s : ℝ) :
    (Candidate 1 → α × ℝ) → Candidate 1 → ℝ :=
  fun z i => center (z i).1 + s * (z i).2

theorem measurable_finiteGaussianMixtureCandidateCoordinateMap
    {α : Type*} [MeasurableSpace α] (center : α → ℝ)
    (hcenter : Measurable center) (s : ℝ) :
    Measurable (finiteGaussianMixtureCandidateCoordinateMap center s) := by
  apply measurable_pi_lambda
  intro i
  exact (hcenter.comp (measurable_pi_apply i).fst).add
    (measurable_const.mul ((measurable_pi_apply i).snd))

/-- Iid finite latent component draws and Gaussians induce the iid density source law. -/
theorem finiteGaussianMixture_pi_latentLaw_eq_candidateNoiseLaw
    {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (law : PMF α) (center : α → ℝ) (hcenter : Measurable center) (s : ℝ)
    (hs : 0 < s) :
    (Measure.pi (fun _ : Candidate 1 =>
      law.toMeasure.prod (ProbabilityTheory.gaussianReal 0 1))).map
        (finiteGaussianMixtureCandidateCoordinateMap center s) =
      w11CandidateNoiseLaw (finiteGaussianMixtureDensity law center s) := by
  let componentMeasure : Measure (α × ℝ) :=
    law.toMeasure.prod (ProbabilityTheory.gaussianReal 0 1)
  let componentMap : α × ℝ → ℝ :=
    fun z => center z.1 + s * z.2
  have hcomponentMap : Measurable componentMap :=
    (hcenter.comp measurable_fst).add (measurable_const.mul measurable_snd)
  have hcomponentLaw : componentMeasure.map componentMap =
      w11BaseNoiseLaw (finiteGaussianMixtureDensity law center s) := by
    exact finiteGaussianMixture_latentLaw_eq_baseNoiseLaw law center hcenter s hs
  letI : ∀ _ : Candidate 1, SigmaFinite (componentMeasure.map componentMap) :=
    fun _ => inferInstance
  calc
    (Measure.pi (fun _ : Candidate 1 =>
      law.toMeasure.prod (ProbabilityTheory.gaussianReal 0 1))).map
        (finiteGaussianMixtureCandidateCoordinateMap center s) =
        Measure.pi (fun _ : Candidate 1 => componentMeasure.map componentMap) := by
      change (Measure.pi (fun _ : Candidate 1 => componentMeasure)).map
          (fun z i => componentMap (z i)) = _
      exact Measure.pi_map_pi fun _ => hcomponentMap.aemeasurable
    _ = w11CandidateNoiseLaw (finiteGaussianMixtureDensity law center s) := by
      rw [hcomponentLaw]
      rfl

/-- Reindex the right-associated Gaussian triple used by the Appendix-B model. -/
noncomputable def rightTripleToCandidateMeasurableEquiv
    (α : Type*) [MeasurableSpace α] :
    (α × (α × α)) ≃ᵐ (Candidate 1 → α) :=
  (MeasurableEquiv.prodAssoc : ((α × α) × α) ≃ᵐ α × (α × α)).symm.trans
    (tripleToCandidateMeasurableEquiv α)

/-- The literal coordinate interpretation of a right-associated triple. -/
def rightTripleToCandidateFunction {α : Type*} (z : α × (α × α)) : Candidate 1 → α
  | 0 => z.1
  | 1 => z.2.1
  | _ => z.2.2

@[simp] theorem rightTripleToCandidateFunction_zero {α : Type*} (z : α × (α × α)) :
    rightTripleToCandidateFunction z 0 = z.1 := rfl

@[simp] theorem rightTripleToCandidateFunction_one {α : Type*} (z : α × (α × α)) :
    rightTripleToCandidateFunction z 1 = z.2.1 := rfl

@[simp] theorem rightTripleToCandidateFunction_two {α : Type*} (z : α × (α × α)) :
    rightTripleToCandidateFunction z 2 = z.2.2 := rfl

theorem rightTripleToCandidateMeasurableEquiv_apply_eq_function
    {α : Type*} [MeasurableSpace α] (z : α × (α × α)) :
    rightTripleToCandidateMeasurableEquiv α z = rightTripleToCandidateFunction z := by
  rw [rightTripleToCandidateMeasurableEquiv]
  change tripleToCandidateMeasurableEquiv α ((z.1, z.2.1), z.2.2) = _
  rw [tripleToCandidateMeasurableEquiv_apply_eq_function]
  rfl

/-- The right-associated triple reindexing preserves an iid product law. -/
theorem measurePreserving_rightTripleToCandidateMeasurableEquiv
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] :
    MeasurePreserving (rightTripleToCandidateMeasurableEquiv α)
      (μ.prod (μ.prod μ)) (Measure.pi (fun _ : Candidate 1 => μ)) := by
  letI : ∀ _ : Fin 2, SigmaFinite μ := fun _ => inferInstance
  letI : ∀ _ : Candidate 1, SigmaFinite μ := fun _ => inferInstance
  let eAssoc : ((α × α) × α) ≃ᵐ α × (α × α) := MeasurableEquiv.prodAssoc
  have hAssoc : MeasurePreserving eAssoc ((μ.prod μ).prod μ)
      (μ.prod (μ.prod μ)) :=
    measurePreserving_prodAssoc μ μ μ
  have hTriple : MeasurePreserving (tripleToCandidateMeasurableEquiv α)
      ((μ.prod μ).prod μ) (Measure.pi (fun _ : Candidate 1 => μ)) :=
    measurePreserving_tripleToCandidateMeasurableEquiv μ
  simpa [rightTripleToCandidateMeasurableEquiv, eAssoc] using
    (MeasurePreserving.symm eAssoc hAssoc).trans hTriple

/-- The candidate-indexed component pairs obtained from the literal Appendix-B triples. -/
noncomputable def finiteGaussianMixtureTripleToCandidateComponents
    {α : Type*} [MeasurableSpace α] :
    ((α × α) × α) × (ℝ × (ℝ × ℝ)) → Candidate 1 → α × ℝ :=
  (MeasurableEquiv.arrowProdEquivProdArrow α ℝ (Candidate 1)).symm ∘
    Prod.map (tripleToCandidateMeasurableEquiv α)
      (rightTripleToCandidateMeasurableEquiv ℝ)

theorem finiteGaussianMixtureTripleToCandidateComponents_apply
    {α : Type*} [MeasurableSpace α]
    (omega : ((α × α) × α) × (ℝ × (ℝ × ℝ))) (i : Candidate 1) :
    finiteGaussianMixtureTripleToCandidateComponents omega i =
      (tripleToCandidateFunction omega.1 i, rightTripleToCandidateFunction omega.2 i) := by
  change (tripleToCandidateMeasurableEquiv α omega.1 i,
    rightTripleToCandidateMeasurableEquiv ℝ omega.2 i) = _
  rw [
    tripleToCandidateMeasurableEquiv_apply_eq_function,
    rightTripleToCandidateMeasurableEquiv_apply_eq_function]

/-- The literal independent three-label/three-Gaussian experiment becomes iid component pairs. -/
theorem measurePreserving_finiteGaussianMixtureTripleToCandidateComponents
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (ν : Measure ℝ)
    [SigmaFinite μ] [SigmaFinite ν] :
    MeasurePreserving finiteGaussianMixtureTripleToCandidateComponents
      (((μ.prod μ).prod μ).prod (ν.prod (ν.prod ν)))
      (Measure.pi (fun _ : Candidate 1 => μ.prod ν)) := by
  letI : ∀ _ : Candidate 1, SigmaFinite μ := fun _ => inferInstance
  letI : ∀ _ : Candidate 1, SigmaFinite ν := fun _ => inferInstance
  let hLabel : MeasurePreserving (tripleToCandidateMeasurableEquiv α)
      ((μ.prod μ).prod μ) (Measure.pi (fun _ : Candidate 1 => μ)) :=
    measurePreserving_tripleToCandidateMeasurableEquiv μ
  let hGaussian : MeasurePreserving (rightTripleToCandidateMeasurableEquiv ℝ)
      (ν.prod (ν.prod ν)) (Measure.pi (fun _ : Candidate 1 => ν)) :=
    measurePreserving_rightTripleToCandidateMeasurableEquiv ν
  let hPairs : MeasurePreserving
      (MeasurableEquiv.arrowProdEquivProdArrow α ℝ (Candidate 1)).symm
      ((Measure.pi (fun _ : Candidate 1 => μ)).prod
        (Measure.pi (fun _ : Candidate 1 => ν)))
      (Measure.pi (fun _ : Candidate 1 => μ.prod ν)) :=
    MeasurePreserving.symm _
      (measurePreserving_arrowProdEquivProdArrow α ℝ (Candidate 1)
        (fun _ : Candidate 1 => μ) (fun _ : Candidate 1 => ν))
  simpa [finiteGaussianMixtureTripleToCandidateComponents, Function.comp_def,
    hLabel, hGaussian, hPairs] using hPairs.comp (hLabel.prod hGaussian)

/-- The literal three-label/three-Gaussian source has the iid finite-mixture density law. -/
theorem finiteGaussianMixture_triple_latentLaw_eq_candidateNoiseLaw
    {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (law : PMF α) (center : α → ℝ) (hcenter : Measurable center) (s : ℝ)
    (hs : 0 < s) :
    ((((law.toMeasure.prod law.toMeasure).prod law.toMeasure).prod
      ((ProbabilityTheory.gaussianReal 0 1).prod
        ((ProbabilityTheory.gaussianReal 0 1).prod
          (ProbabilityTheory.gaussianReal 0 1)))).map
        (fun omega i => center (tripleToCandidateFunction omega.1 i) +
          s * rightTripleToCandidateFunction omega.2 i)) =
      w11CandidateNoiseLaw (finiteGaussianMixtureDensity law center s) := by
  let sourceMeasure : Measure (((α × α) × α) × (ℝ × (ℝ × ℝ))) :=
    ((law.toMeasure.prod law.toMeasure).prod law.toMeasure).prod
      ((ProbabilityTheory.gaussianReal 0 1).prod
        ((ProbabilityTheory.gaussianReal 0 1).prod
          (ProbabilityTheory.gaussianReal 0 1)))
  let transport := finiteGaussianMixtureTripleToCandidateComponents (α := α)
  let coordinateMap := finiteGaussianMixtureCandidateCoordinateMap center s
  have htransport : MeasurePreserving transport sourceMeasure
      (Measure.pi (fun _ : Candidate 1 =>
        law.toMeasure.prod (ProbabilityTheory.gaussianReal 0 1))) := by
    exact measurePreserving_finiteGaussianMixtureTripleToCandidateComponents
      law.toMeasure (ProbabilityTheory.gaussianReal 0 1)
  have hcoordinate : Measurable coordinateMap :=
    measurable_finiteGaussianMixtureCandidateCoordinateMap center hcenter s
  have hmap : (fun omega i => center (tripleToCandidateFunction omega.1 i) +
      s * rightTripleToCandidateFunction omega.2 i) = coordinateMap ∘ transport := by
    funext omega i
    change center (tripleToCandidateFunction omega.1 i) +
        s * rightTripleToCandidateFunction omega.2 i =
      center ((finiteGaussianMixtureTripleToCandidateComponents omega i).1) +
        s * (finiteGaussianMixtureTripleToCandidateComponents omega i).2
    rw [finiteGaussianMixtureTripleToCandidateComponents_apply]
  change sourceMeasure.map _ = _
  rw [hmap, ← Measure.map_map hcoordinate htransport.measurable, htransport.map_eq]
  exact finiteGaussianMixture_pi_latentLaw_eq_candidateNoiseLaw
    law center hcenter s hs

/-- The B.1 label-triple decoder is the displayed three-coordinate reindexing. -/
theorem appendixB1NoiseTripleFunction_eq_tripleToCandidateFunction :
    appendixB1NoiseTripleFunction = tripleToCandidateFunction := by
  funext noise i
  fin_cases i <;> rfl

/-- The B.2 label-triple decoder is the displayed three-coordinate reindexing. -/
theorem appendixB2NoiseTripleFunction_eq_tripleToCandidateFunction :
    appendixB2NoiseTripleFunction = tripleToCandidateFunction := by
  funext noise i
  fin_cases i <;> rfl

/-- The model's Gaussian-triple decoder is the right-associated coordinate reindexing. -/
theorem appendixBGaussianTripleFunction_eq_rightTripleToCandidateFunction :
    appendixBGaussianTripleFunction = rightTripleToCandidateFunction := by
  funext z i
  fin_cases i <;> rfl

/-- The B.1 product PMF has the literal iid product measure. -/
theorem appendixB1NoiseTriplePMF_toMeasure_eq_iid :
    appendixB1NoiseTriplePMF.toMeasure =
      ((appendixB1NoisePMF.toMeasure.prod appendixB1NoisePMF.toMeasure).prod
        appendixB1NoisePMF.toMeasure) := by
  unfold appendixB1NoiseTriplePMF
  rw [pmfProd_toMeasure_eq_prod, pmfProd_toMeasure_eq_prod]

/-- The B.2 product PMF has the literal iid product measure. -/
theorem appendixB2NoiseTriplePMF_toMeasure_eq_iid :
    appendixB2NoiseTriplePMF.toMeasure =
      ((appendixB2NoisePMF.toMeasure.prod appendixB2NoisePMF.toMeasure).prod
        appendixB2NoisePMF.toMeasure) := by
  unfold appendixB2NoiseTriplePMF
  rw [pmfProd_toMeasure_eq_prod, pmfProd_toMeasure_eq_prod]

/-- B.1's literal latent source, mapped to its source-noise vector, is the iid density law. -/
theorem appendixB1GaussianLatentMeasure_map_sourceNoise_eq_candidateNoiseLaw
    (s : ℝ) (hs : 0 < s) :
    appendixB1GaussianLatentMeasure.map
      (fun omega i => appendixB1NoiseValue (appendixB1NoiseTripleFunction omega.1 i) +
        s * appendixBGaussianTripleFunction omega.2 i) =
      w11CandidateNoiseLaw (appendixB1GaussianMixtureDensity s) := by
  unfold appendixB1GaussianLatentMeasure appendixBStandardGaussianTripleMeasure
  rw [appendixB1NoiseTriplePMF_toMeasure_eq_iid,
    appendixB1NoiseTripleFunction_eq_tripleToCandidateFunction,
    appendixBGaussianTripleFunction_eq_rightTripleToCandidateFunction]
  exact finiteGaussianMixture_triple_latentLaw_eq_candidateNoiseLaw
    appendixB1NoisePMF appendixB1NoiseValue (measurable_of_finite _) s hs

/-- B.2's literal common source-noise vector is the iid density law. -/
theorem appendixB2GaussianLatentMeasure_map_sourceNoise_eq_candidateNoiseLaw
    (s : ℝ) (hs : 0 < s) :
    appendixB2GaussianLatentMeasure.map
      (fun omega i => appendixB2SourceGaussianMixtureNoise s omega i) =
      w11CandidateNoiseLaw (appendixB2GaussianMixtureDensity s) := by
  unfold appendixB2GaussianLatentMeasure appendixBStandardGaussianTripleMeasure
    appendixB2SourceGaussianMixtureNoise
  rw [appendixB2NoiseTriplePMF_toMeasure_eq_iid,
    appendixB2NoiseTripleFunction_eq_tripleToCandidateFunction,
    appendixBGaussianTripleFunction_eq_rightTripleToCandidateFunction]
  exact finiteGaussianMixture_triple_latentLaw_eq_candidateNoiseLaw
    appendixB2NoisePMF appendixB2NoiseValue (measurable_of_finite _) s hs

end

end KR21Monoculture

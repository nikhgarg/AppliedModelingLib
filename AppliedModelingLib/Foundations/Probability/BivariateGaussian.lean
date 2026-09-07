import AppliedModelingLib.Foundations.Probability.GaussianMathlib
import AppliedModelingLib.Foundations.Probability.MeasureInequalities

/-!
# Bivariate Gaussian Source Laws

Reusable correlated standard-Gaussian laws for two-dimensional probability
bookkeeping.

## Main declarations

- `correlatedStandardGaussianLaw`
- `standardBivariateGaussianCDF`
- `owenAffineUpperSelectionMass`
- `correlatedStandardGaussianLaw_map_fst`
- `correlatedStandardGaussianLaw_map_snd`
- `correlatedStandardGaussianLaw_noAtoms_map_fst`
- `correlatedStandardGaussianLaw_noAtoms_map_snd`
- `correlatedStandardGaussianLaw_isOpenPosMeasure`
- `standardBivariateGaussianCDF_continuous_of_rho_sq_le_one`
- `correlatedStandardGaussianLaw_firstCoordinateLowerMass`
- `correlatedStandardGaussianLaw_verticalUpperStripMass_pos`
- `owenAffineUpperSelectionMass_eq_correlatedStandardGaussian_verticalUpperStripMass`
- `correlatedStandardGaussianLaw_verticalBoundaryLeft_real_eq_zero`
- `correlatedStandardGaussianLaw_horizontalBoundaryLeft_real_eq_zero`
- `gaussianVarianceFromStd`
- `canonicalHalfVarianceScale`
- `independentGaussianPairMeasureWithStd`
- `independentGaussianPairMeasureHalf`
- `independentGaussianStrictConditionalWinnerRatioWithStd_eq_scaled`
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Real

namespace AppliedModelingLib
namespace Probability

noncomputable section

/--
The measurable map sending independent standard normals `(U,V)` to the
correlated standard-normal pair `(U, rho * U + sqrt(1-rho^2) * V)`.
-/
def correlatedStandardGaussianMap (rho : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1, rho * p.1 + Real.sqrt (1 - rho ^ 2) * p.2)

/--
Continuous-linear version of `correlatedStandardGaussianMap`.

This is useful for characteristic-function proofs, while the function-valued
map remains the public definition used by existing paper files.
-/
noncomputable def correlatedStandardGaussianCLM (rho : ℝ) :
    (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    (rho • (ContinuousLinearMap.fst ℝ ℝ ℝ) +
      Real.sqrt (1 - rho ^ 2) • (ContinuousLinearMap.snd ℝ ℝ ℝ))

@[simp]
theorem correlatedStandardGaussianCLM_apply (rho : ℝ) (p : ℝ × ℝ) :
    correlatedStandardGaussianCLM rho p =
      correlatedStandardGaussianMap rho p := by
  simp [correlatedStandardGaussianCLM, correlatedStandardGaussianMap]

/--
Owen's affine standardization map.  For independent standard normals `(X,Z)`,
this sends `(X,Z)` to `((X - c Z)/sqrt(1+c^2), Z)`.
-/
noncomputable def owenStandardizingGaussianCLM (c : ℝ) :
    (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  let denom := Real.sqrt (1 + c ^ 2)
  ((denom⁻¹) • (ContinuousLinearMap.fst ℝ ℝ ℝ) -
      (c / denom) • (ContinuousLinearMap.snd ℝ ℝ ℝ)).prod
    (ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp]
theorem owenStandardizingGaussianCLM_apply (c : ℝ) (p : ℝ × ℝ) :
    owenStandardizingGaussianCLM c p =
      ((p.1 - c * p.2) / Real.sqrt (1 + c ^ 2), p.2) := by
  simp [owenStandardizingGaussianCLM]
  ring

theorem measurable_correlatedStandardGaussianMap (rho : ℝ) :
    Measurable (correlatedStandardGaussianMap rho) := by
  unfold correlatedStandardGaussianMap
  fun_prop

/-- The correlated standard-Gaussian source map is continuous. -/
theorem continuous_correlatedStandardGaussianMap (rho : ℝ) :
    Continuous (correlatedStandardGaussianMap rho) := by
  unfold correlatedStandardGaussianMap
  fun_prop

/-- For `rho^2 < 1`, the correlated standard-Gaussian source map is onto. -/
theorem correlatedStandardGaussianMap_surjective_of_rho_sq_lt_one
    {rho : ℝ} (hrho : rho ^ 2 < 1) :
    Function.Surjective (correlatedStandardGaussianMap rho) := by
  intro z
  let scale : ℝ := Real.sqrt (1 - rho ^ 2)
  have hscale_pos : 0 < scale := by
    dsimp [scale]
    exact Real.sqrt_pos.2 (sub_pos.mpr hrho)
  have hscale_ne : scale ≠ 0 := ne_of_gt hscale_pos
  refine ⟨(z.1, (z.2 - rho * z.1) / scale), ?_⟩
  ext
  · simp [correlatedStandardGaussianMap]
  · simp [correlatedStandardGaussianMap]
    field_simp [hscale_ne]
    ring

/--
The standard bivariate normal law with correlation parameter `rho`, constructed
as `(U, rho * U + sqrt(1-rho^2) * V)` for independent standard normals `U,V`.

When `rho^2 < 1`, this is the usual nondegenerate correlated standard-normal
law.  The definition is still meaningful at degenerate parameters; lemmas that
need a nonzero second-coordinate noise scale assume `rho^2 < 1`.
-/
def correlatedStandardGaussianLaw (rho : ℝ) : Measure (ℝ × ℝ) :=
  (standardGaussianMeasure.prod standardGaussianMeasure).map
    (correlatedStandardGaussianMap rho)

instance correlatedStandardGaussianLaw_isProbabilityMeasure (rho : ℝ) :
    IsProbabilityMeasure (correlatedStandardGaussianLaw rho) := by
  unfold correlatedStandardGaussianLaw
  exact Measure.isProbabilityMeasure_map
    (measurable_correlatedStandardGaussianMap rho).aemeasurable

/-- The function-valued and continuous-linear definitions induce the same correlated law. -/
theorem correlatedStandardGaussianLaw_eq_map_correlatedStandardGaussianCLM (rho : ℝ) :
    correlatedStandardGaussianLaw rho =
      (standardGaussianMeasure.prod standardGaussianMeasure).map
        (correlatedStandardGaussianCLM rho) := by
  rw [correlatedStandardGaussianLaw]
  congr 1

/-- Characteristic function of a standard normal against an arbitrary continuous linear form. -/
theorem charFunDual_standardGaussianMeasure (L : StrongDual ℝ ℝ) :
    charFunDual standardGaussianMeasure L =
      Complex.exp (-((L 1 : ℝ) ^ 2) / 2) := by
  rw [charFunDual_eq_charFun_map_one]
  rw [standardGaussianMeasure]
  rw [ProbabilityTheory.gaussianReal_map_continuousLinearMap]
  rw [ProbabilityTheory.charFun_gaussianReal]
  simp [Real.toNNReal_of_nonneg (sq_nonneg (L 1))]
  ring_nf

/--
Characteristic function of independent standard normals in coordinates.  This
small lemma keeps later bivariate Gaussian map-identification proofs from
repeating product-measure bookkeeping.
-/
theorem charFunDual_standardGaussianProduct (L : StrongDual ℝ (ℝ × ℝ)) :
    charFunDual (standardGaussianMeasure.prod standardGaussianMeasure) L =
      Complex.exp
        (-(((L (1, 0) : ℝ) ^ 2 + (L (0, 1) : ℝ) ^ 2) / 2)) := by
  rw [charFunDual_prod]
  rw [charFunDual_standardGaussianMeasure
    (L.comp (ContinuousLinearMap.inl ℝ ℝ ℝ))]
  rw [charFunDual_standardGaussianMeasure
    (L.comp (ContinuousLinearMap.inr ℝ ℝ ℝ))]
  simp
  rw [← Complex.exp_add]
  congr
  ring

/-- Algebra for the Owen correlation scale. -/
theorem sqrt_one_sub_neg_div_sqrt_one_add_sq_sq (c : ℝ) :
    Real.sqrt (1 - ((-c) / Real.sqrt (1 + c ^ 2)) ^ 2) =
      (Real.sqrt (1 + c ^ 2))⁻¹ := by
  let denom : ℝ := Real.sqrt (1 + c ^ 2)
  have hpos : 0 < 1 + c ^ 2 := by nlinarith [sq_nonneg c]
  have hdenom_pos : 0 < denom := by
    dsimp [denom]
    exact Real.sqrt_pos.2 hpos
  have hdenom_ne : denom ≠ 0 := ne_of_gt hdenom_pos
  have hdenom_sq : denom ^ 2 = 1 + c ^ 2 := by
    dsimp [denom]
    exact Real.sq_sqrt (by positivity)
  have hinside :
      1 - ((-c) / denom) ^ 2 = denom⁻¹ ^ 2 := by
    field_simp [hdenom_ne]
    rw [hdenom_sq]
    ring
  rw [show Real.sqrt (1 - ((-c) / Real.sqrt (1 + c ^ 2)) ^ 2) =
      Real.sqrt (1 - ((-c) / denom) ^ 2) by rfl]
  rw [hinside]
  exact Real.sqrt_sq_eq_abs (denom⁻¹) |>.trans (abs_of_pos (inv_pos.mpr hdenom_pos))

/--
The Owen standardization map has the same law as the correlated
standard-Gaussian map with `rho = -c/sqrt(1+c^2)`.

This is the probabilistic content behind the bivariate-normal/Owen
admissions papers.
-/
theorem owenStandardizingGaussianLaw_eq_correlatedStandardGaussianLaw (c : ℝ) :
    (standardGaussianMeasure.prod standardGaussianMeasure).map
        (owenStandardizingGaussianCLM c) =
      correlatedStandardGaussianLaw ((-c) / Real.sqrt (1 + c ^ 2)) := by
  let base : Measure (ℝ × ℝ) :=
    standardGaussianMeasure.prod standardGaussianMeasure
  let denom : ℝ := Real.sqrt (1 + c ^ 2)
  let rho : ℝ := (-c) / denom
  have hpos : 0 < 1 + c ^ 2 := by nlinarith [sq_nonneg c]
  have hdenom_pos : 0 < denom := by
    dsimp [denom]
    exact Real.sqrt_pos.2 hpos
  have hdenom_ne : denom ≠ 0 := ne_of_gt hdenom_pos
  have hscale :
      Real.sqrt (1 - rho ^ 2) = denom⁻¹ := by
    simpa [rho, denom] using sqrt_one_sub_neg_div_sqrt_one_add_sq_sq c
  rw [correlatedStandardGaussianLaw_eq_map_correlatedStandardGaussianCLM rho]
  refine Measure.ext_of_charFunDual (funext fun L => ?_)
  rw [charFunDual_map (owenStandardizingGaussianCLM c) L]
  rw [charFunDual_map (correlatedStandardGaussianCLM rho) L]
  rw [charFunDual_standardGaussianProduct]
  rw [charFunDual_standardGaussianProduct]
  congr 1
  have hsum :
      (((L.comp (owenStandardizingGaussianCLM c)) (1, 0) : ℝ) ^ 2 +
          ((L.comp (owenStandardizingGaussianCLM c)) (0, 1) : ℝ) ^ 2) =
        (((L.comp (correlatedStandardGaussianCLM rho)) (1, 0) : ℝ) ^ 2 +
          ((L.comp (correlatedStandardGaussianCLM rho)) (0, 1) : ℝ) ^ 2) := by
    have hdenom_sq : denom ^ 2 = 1 + c ^ 2 := by
      dsimp [denom]
      exact Real.sq_sqrt (by positivity)
    have hLpair :
        ∀ x y : ℝ, L (x, y) = x * L (1, 0) + y * L (0, 1) := by
      intro x y
      have hdecomp : (x, y) =
          x • ((1 : ℝ), (0 : ℝ)) + y • ((0 : ℝ), (1 : ℝ)) := by
        ext <;> simp
      rw [hdecomp, map_add, map_smul, map_smul]
      ring
    have hO1 :
        ((L.comp (owenStandardizingGaussianCLM c)) (1, 0) : ℝ) =
          denom⁻¹ * L (1, 0) := by
      change L (owenStandardizingGaussianCLM c (1, 0)) = denom⁻¹ * L (1, 0)
      have harg :
          owenStandardizingGaussianCLM c (1, 0) = (denom⁻¹, 0) := by
        simp [owenStandardizingGaussianCLM_apply, denom]
      rw [harg, hLpair denom⁻¹ 0]
      ring
    have hO2 :
        ((L.comp (owenStandardizingGaussianCLM c)) (0, 1) : ℝ) =
          (-c / denom) * L (1, 0) + L (0, 1) := by
      change L (owenStandardizingGaussianCLM c (0, 1)) =
        (-c / denom) * L (1, 0) + L (0, 1)
      have harg :
          owenStandardizingGaussianCLM c (0, 1) = (-c / denom, 1) := by
        simp [owenStandardizingGaussianCLM_apply, denom]
      rw [harg, hLpair (-c / denom) 1]
      ring
    have hC1 :
        ((L.comp (correlatedStandardGaussianCLM rho)) (1, 0) : ℝ) =
          L (1, 0) + rho * L (0, 1) := by
      change L (correlatedStandardGaussianCLM rho (1, 0)) =
        L (1, 0) + rho * L (0, 1)
      have harg :
          correlatedStandardGaussianCLM rho (1, 0) = (1, rho) := by
        simp [correlatedStandardGaussianCLM_apply, correlatedStandardGaussianMap]
      rw [harg, hLpair 1 rho]
      ring
    have hC2 :
        ((L.comp (correlatedStandardGaussianCLM rho)) (0, 1) : ℝ) =
          denom⁻¹ * L (0, 1) := by
      change L (correlatedStandardGaussianCLM rho (0, 1)) =
        denom⁻¹ * L (0, 1)
      have harg :
          correlatedStandardGaussianCLM rho (0, 1) = (0, denom⁻¹) := by
        simp [correlatedStandardGaussianCLM_apply, correlatedStandardGaussianMap, hscale]
      rw [harg, hLpair 0 denom⁻¹]
      ring
    rw [hO1, hO2, hC1, hC2]
    dsimp [rho]
    field_simp [hdenom_ne]
    nlinarith [hdenom_sq]
  exact_mod_cast
    (by
      simpa [ContinuousLinearMap.comp_apply, correlatedStandardGaussianCLM_apply]
        using hsum)

/--
Source-side affine selection mass behind Owen's formula:
`P(X <= A * sqrt(1+c^2) + c Z, B <= Z)` for independent standard normals.
-/
noncomputable def owenAffineUpperSelectionMass (c A B : ℝ) : ℝ :=
  (standardGaussianMeasure.prod standardGaussianMeasure).real
    {p : ℝ × ℝ | p.1 ≤ A * Real.sqrt (1 + c ^ 2) + c * p.2 ∧ B ≤ p.2}

/--
Owen affine upper-selection mass equals the correlated-Gaussian vertical strip.

This is a measure-theoretic replacement for repeatedly invoking Owen's
tabulated integral identity: standardize the affine half-space, identify the
resulting bivariate Gaussian law by characteristic functions, and then read off
the vertical strip.
-/
theorem owenAffineUpperSelectionMass_eq_correlatedStandardGaussian_verticalUpperStripMass
    (c A B : ℝ) :
    owenAffineUpperSelectionMass c A B =
      verticalUpperStripMass
        (correlatedStandardGaussianLaw ((-c) / Real.sqrt (1 + c ^ 2))) A B := by
  let base : Measure (ℝ × ℝ) :=
    standardGaussianMeasure.prod standardGaussianMeasure
  let denom : ℝ := Real.sqrt (1 + c ^ 2)
  have hpos : 0 < 1 + c ^ 2 := by nlinarith [sq_nonneg c]
  have hdenom_pos : 0 < denom := by
    dsimp [denom]
    exact Real.sqrt_pos.2 hpos
  have hdenom_ne : denom ≠ 0 := ne_of_gt hdenom_pos
  have hpre :
      (owenStandardizingGaussianCLM c) ⁻¹'
          {p : ℝ × ℝ | p.1 ≤ A ∧ B ≤ p.2} =
        {p : ℝ × ℝ | p.1 ≤ A * denom + c * p.2 ∧ B ≤ p.2} := by
    ext p
    constructor
    · intro hp
      constructor
      · have hle : (p.1 - c * p.2) / denom ≤ A := by
          simpa [denom] using hp.1
        have hle' : p.1 - c * p.2 ≤ A * denom := by
          exact (div_le_iff₀ hdenom_pos).mp hle
        linarith
      · simpa using hp.2
    · intro hp
      constructor
      · have hp1 : p.1 ≤ A * denom + c * p.2 := hp.1
        have hle' : p.1 - c * p.2 ≤ A * denom := by linarith
        have hle : (p.1 - c * p.2) / denom ≤ A :=
          (div_le_iff₀ hdenom_pos).mpr hle'
        simpa [denom] using hle
      · simpa using hp.2
  calc
    owenAffineUpperSelectionMass c A B
        =
          (base.map (owenStandardizingGaussianCLM c)).real
            {p : ℝ × ℝ | p.1 ≤ A ∧ B ≤ p.2} := by
          rw [owenAffineUpperSelectionMass, measureReal_def, measureReal_def,
            Measure.map_apply (by fun_prop) (measurableSet_verticalUpperStrip A B),
            hpre]
    _ =
          (correlatedStandardGaussianLaw ((-c) / Real.sqrt (1 + c ^ 2))).real
            {p : ℝ × ℝ | p.1 ≤ A ∧ B ≤ p.2} := by
          rw [owenStandardizingGaussianLaw_eq_correlatedStandardGaussianLaw c]
    _ =
          verticalUpperStripMass
            (correlatedStandardGaussianLaw ((-c) / Real.sqrt (1 + c ^ 2))) A B := rfl

/--
For `rho^2 < 1`, the correlated standard-Gaussian law gives positive mass to
every nonempty open set.
-/
theorem correlatedStandardGaussianLaw_isOpenPosMeasure
    {rho : ℝ} (hrho : rho ^ 2 < 1) :
    Measure.IsOpenPosMeasure (correlatedStandardGaussianLaw rho) := by
  unfold correlatedStandardGaussianLaw
  exact
    (continuous_correlatedStandardGaussianMap rho).isOpenPosMeasure_map
      (correlatedStandardGaussianMap_surjective_of_rho_sq_lt_one hrho)

/--
The bivariate standard-normal CDF `Phi_2(x,y;rho)`, defined as the lower-left
rectangle mass of the correlated standard-Gaussian law.
-/
def standardBivariateGaussianCDF (x y rho : ℝ) : ℝ :=
  AppliedModelingLib.lowerLeftRectangleMass (correlatedStandardGaussianLaw rho) x y

/-- The canonical correlation transform `-z / sqrt(1+z^2)` lies in `(-1,1)`. -/
theorem neg_div_sqrt_one_add_sq_sq_lt_one (z : ℝ) :
    ((-z) / Real.sqrt (1 + z ^ 2)) ^ 2 < 1 := by
  have hnonneg : 0 ≤ 1 + z ^ 2 := by positivity
  have hpos : 0 < 1 + z ^ 2 := by nlinarith [sq_nonneg z]
  have hsqrt_sq : (Real.sqrt (1 + z ^ 2)) ^ 2 = 1 + z ^ 2 := by
    exact Real.sq_sqrt hnonneg
  have hsqrt_ne : Real.sqrt (1 + z ^ 2) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 hpos)
  calc
    ((-z) / Real.sqrt (1 + z ^ 2)) ^ 2 =
        z ^ 2 / (1 + z ^ 2) := by
          field_simp [hsqrt_ne]
          rw [hsqrt_sq]
    _ < 1 := by
      rw [div_lt_one hpos]
      linarith

/-- The first-coordinate marginal of `correlatedStandardGaussianLaw rho` is standard normal. -/
theorem correlatedStandardGaussianLaw_map_fst (rho : ℝ) :
    (correlatedStandardGaussianLaw rho).map Prod.fst =
      standardGaussianMeasure := by
  rw [correlatedStandardGaussianLaw, Measure.map_map measurable_fst
    (measurable_correlatedStandardGaussianMap rho)]
  have hcomp :
      Prod.fst ∘ correlatedStandardGaussianMap rho =
        (fun p : ℝ × ℝ => p.1) := by
    funext p
    simp [correlatedStandardGaussianMap]
  rw [hcomp]
  rw [Measure.map_fst_prod]
  simp [standardGaussianMeasure]

/--
If `rho` is a valid correlation parameter, the second-coordinate marginal of
`correlatedStandardGaussianLaw rho` is also standard normal.
-/
theorem correlatedStandardGaussianLaw_map_snd {rho : ℝ} (hrho : rho ^ 2 ≤ 1) :
    (correlatedStandardGaussianLaw rho).map Prod.snd =
      standardGaussianMeasure := by
  let scale : ℝ := Real.sqrt (1 - rho ^ 2)
  let base : Measure (ℝ × ℝ) :=
    standardGaussianMeasure.prod standardGaussianMeasure
  let vRho : ℝ≥0 := ⟨rho ^ 2, sq_nonneg rho⟩
  let vScale : ℝ≥0 := ⟨scale ^ 2, sq_nonneg scale⟩
  have hscale_sq : scale ^ 2 = 1 - rho ^ 2 := by
    dsimp [scale]
    exact Real.sq_sqrt (sub_nonneg.mpr hrho)
  have hvar : vRho + vScale = (1 : ℝ≥0) := by
    ext
    change rho ^ 2 + scale ^ 2 = (1 : ℝ)
    rw [hscale_sq]
    linarith
  have hX :
      base.map (fun p : ℝ × ℝ => rho * p.1) =
        ProbabilityTheory.gaussianReal 0 vRho := by
    calc
      base.map (fun p : ℝ × ℝ => rho * p.1)
          = (base.map Prod.fst).map (fun u : ℝ => rho * u) := by
              rw [← Function.comp_def,
                ← Measure.map_map (measurable_const_mul rho) measurable_fst]
      _ = standardGaussianMeasure.map (fun u : ℝ => rho * u) := by
              rw [Measure.map_fst_prod]
              simp [standardGaussianMeasure]
      _ = ProbabilityTheory.gaussianReal 0 vRho := by
              simpa [standardGaussianMeasure, vRho] using
                (ProbabilityTheory.gaussianReal_map_const_mul
                  (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) rho)
  have hY :
      base.map (fun p : ℝ × ℝ => scale * p.2) =
        ProbabilityTheory.gaussianReal 0 vScale := by
    calc
      base.map (fun p : ℝ × ℝ => scale * p.2)
          = (base.map Prod.snd).map (fun u : ℝ => scale * u) := by
              rw [← Function.comp_def,
                ← Measure.map_map (measurable_const_mul scale) measurable_snd]
      _ = standardGaussianMeasure.map (fun u : ℝ => scale * u) := by
              rw [Measure.map_snd_prod]
              simp [standardGaussianMeasure]
      _ = ProbabilityTheory.gaussianReal 0 vScale := by
              simpa [standardGaussianMeasure, vScale] using
                (ProbabilityTheory.gaussianReal_map_const_mul
                  (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) scale)
  have hindep :
      IndepFun (fun p : ℝ × ℝ => rho * p.1)
        (fun p : ℝ × ℝ => scale * p.2) base := by
    dsimp [base]
    exact ProbabilityTheory.indepFun_prod
      (μ := standardGaussianMeasure) (ν := standardGaussianMeasure)
      (X := fun u : ℝ => rho * u) (Y := fun u : ℝ => scale * u)
      (by fun_prop) (by fun_prop)
  have hsum :
      base.map
          ((fun p : ℝ × ℝ => rho * p.1) +
            (fun p : ℝ × ℝ => scale * p.2)) =
        ProbabilityTheory.gaussianReal 0 1 := by
    have hraw :=
      ProbabilityTheory.gaussianReal_add_gaussianReal_of_indepFun
        (P := base)
        (X := fun p : ℝ × ℝ => rho * p.1)
        (Y := fun p : ℝ × ℝ => scale * p.2)
        (m₁ := (0 : ℝ)) (m₂ := (0 : ℝ))
        (v₁ := vRho) (v₂ := vScale)
        hindep hX hY
    simpa [hvar] using hraw
  rw [correlatedStandardGaussianLaw, Measure.map_map measurable_snd
    (measurable_correlatedStandardGaussianMap rho)]
  change
    base.map
        (Prod.snd ∘ correlatedStandardGaussianMap rho) =
      standardGaussianMeasure
  simpa [base, standardGaussianMeasure, correlatedStandardGaussianMap, scale]
    using hsum

/-- The first-coordinate marginal of the correlated standard-Gaussian law is nonatomic. -/
theorem correlatedStandardGaussianLaw_noAtoms_map_fst (rho : ℝ) :
    NoAtoms ((correlatedStandardGaussianLaw rho).map Prod.fst) := by
  rw [correlatedStandardGaussianLaw_map_fst rho]
  infer_instance

/-- The second-coordinate marginal of a nondegenerate correlated standard-Gaussian law is nonatomic. -/
theorem correlatedStandardGaussianLaw_noAtoms_map_snd
    {rho : ℝ} (hrho : rho ^ 2 ≤ 1) :
    NoAtoms ((correlatedStandardGaussianLaw rho).map Prod.snd) := by
  rw [correlatedStandardGaussianLaw_map_snd hrho]
  infer_instance

/--
Moving upper-orthant masses under a correlated standard-Gaussian law are
continuous along the diagonal once `rho` is a valid correlation parameter.
-/
theorem correlatedStandardGaussianLaw_upperOrthantMass_diagonal_continuous
    {rho : ℝ} (hrho : rho ^ 2 ≤ 1) (offset : ℝ) :
    Continuous fun q : ℝ =>
      AppliedModelingLib.upperOrthantMass (correlatedStandardGaussianLaw rho)
        (q - offset) q := by
  letI : NoAtoms ((correlatedStandardGaussianLaw rho).map Prod.fst) :=
    correlatedStandardGaussianLaw_noAtoms_map_fst rho
  letI : NoAtoms ((correlatedStandardGaussianLaw rho).map Prod.snd) :=
    correlatedStandardGaussianLaw_noAtoms_map_snd hrho
  exact
    AppliedModelingLib.upperOrthantMass_diagonal_continuous_of_noAtoms_marginals
      (correlatedStandardGaussianLaw rho) offset

/--
For every valid correlation parameter, the concrete bivariate Gaussian CDF is
continuous in its two threshold coordinates.
-/
theorem standardBivariateGaussianCDF_continuous_of_rho_sq_le_one
    {rho : ℝ} (hrho : rho ^ 2 ≤ 1) :
    Continuous fun p : ℝ × ℝ =>
      standardBivariateGaussianCDF p.1 p.2 rho := by
  letI : NoAtoms ((correlatedStandardGaussianLaw rho).map Prod.fst) :=
    correlatedStandardGaussianLaw_noAtoms_map_fst rho
  letI : NoAtoms ((correlatedStandardGaussianLaw rho).map Prod.snd) :=
    correlatedStandardGaussianLaw_noAtoms_map_snd hrho
  simpa [standardBivariateGaussianCDF] using
    AppliedModelingLib.lowerLeftRectangleMass_continuous_of_noAtoms_marginals
      (correlatedStandardGaussianLaw rho)

/-- The first coordinate of `correlatedStandardGaussianLaw rho` is standard normal. -/
theorem correlatedStandardGaussianLaw_firstCoordinateLowerMass
    (rho x : ℝ) :
    AppliedModelingLib.firstCoordinateLowerMass
        (correlatedStandardGaussianLaw rho) x =
      standardGaussianCDF x := by
  have hpre :
      (correlatedStandardGaussianMap rho) ⁻¹'
          {p : ℝ × ℝ | p.1 ≤ x} =
        (Set.Iic x) ×ˢ (Set.univ : Set ℝ) := by
    ext p
    simp [correlatedStandardGaussianMap]
  rw [AppliedModelingLib.firstCoordinateLowerMass, correlatedStandardGaussianLaw,
    measureReal_def, Measure.map_apply
      (measurable_correlatedStandardGaussianMap rho)
      (AppliedModelingLib.measurableSet_firstCoordinateLower x),
    hpre, Measure.prod_prod, standardGaussianCDF,
    ProbabilityTheory.cdf_eq_real]
  simp [measureReal_def]

/-- Nondegenerate correlated standard-Gaussian laws give positive mass to every vertical upper strip. -/
theorem correlatedStandardGaussianLaw_verticalUpperStripMass_pos
    {rho : ℝ} (hrho : rho ^ 2 < 1) (x y : ℝ) :
    0 < AppliedModelingLib.verticalUpperStripMass
      (correlatedStandardGaussianLaw rho) x y := by
  letI : Measure.IsOpenPosMeasure (correlatedStandardGaussianLaw rho) :=
    correlatedStandardGaussianLaw_isOpenPosMeasure hrho
  exact
    AppliedModelingLib.verticalUpperStripMass_pos_of_isOpenPosMeasure
      (correlatedStandardGaussianLaw rho) x y

/--
The correlated standard-Gaussian law assigns zero mass to every vertical
boundary clipped by a lower half-space.
-/
theorem correlatedStandardGaussianLaw_verticalBoundaryLeft_real_eq_zero
    (rho x y : ℝ) :
    (correlatedStandardGaussianLaw rho).real
        {p : ℝ × ℝ | p.1 = x ∧ p.2 ≤ y} = 0 := by
  have hline :
      correlatedStandardGaussianLaw rho
          {p : ℝ × ℝ | p.1 = x} = 0 := by
    calc
      correlatedStandardGaussianLaw rho {p : ℝ × ℝ | p.1 = x}
          =
            (correlatedStandardGaussianLaw rho).map Prod.fst
              ({x} : Set ℝ) := by
              rw [Measure.map_apply measurable_fst (measurableSet_singleton x)]
              rfl
      _ = standardGaussianMeasure ({x} : Set ℝ) := by
              rw [correlatedStandardGaussianLaw_map_fst rho]
      _ = 0 := by
              haveI : NoAtoms standardGaussianMeasure := by
                unfold standardGaussianMeasure
                exact ProbabilityTheory.noAtoms_gaussianReal
                  (by norm_num : (1 : ℝ≥0) ≠ 0)
              exact measure_singleton x
  have hclip :
      correlatedStandardGaussianLaw rho
          {p : ℝ × ℝ | p.1 = x ∧ p.2 ≤ y} = 0 := by
    exact measure_mono_null (by intro p hp; exact hp.1) hline
  simp [measureReal_def, hclip]

/--
For `rho^2 < 1`, the correlated standard-Gaussian law assigns zero mass to
every horizontal boundary clipped by a left half-space.
-/
theorem correlatedStandardGaussianLaw_horizontalBoundaryLeft_real_eq_zero
    {rho : ℝ} (hrho : rho ^ 2 < 1) (x y : ℝ) :
    (correlatedStandardGaussianLaw rho).real
        {p : ℝ × ℝ | p.1 ≤ x ∧ p.2 = y} = 0 := by
  let scale := Real.sqrt (1 - rho ^ 2)
  have hscale_pos : 0 < scale := by
    dsimp [scale]
    exact Real.sqrt_pos.2 (sub_pos.mpr hrho)
  have hscale_ne : scale ≠ 0 := ne_of_gt hscale_pos
  haveI : NoAtoms standardGaussianMeasure := by
    unfold standardGaussianMeasure
    exact ProbabilityTheory.noAtoms_gaussianReal (by norm_num : (1 : ℝ≥0) ≠ 0)
  let boundary : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 ≤ x ∧ p.2 = y}
  have hboundary_meas : MeasurableSet boundary := by
    simpa [boundary] using AppliedModelingLib.measurableSet_horizontalBoundaryLeft x y
  have hpre_meas :
      MeasurableSet ((correlatedStandardGaussianMap rho) ⁻¹' boundary) :=
    hboundary_meas.preimage (measurable_correlatedStandardGaussianMap rho)
  have hsection :
      ∀ u : ℝ,
        standardGaussianMeasure
            {v : ℝ |
              (u, v) ∈
                (correlatedStandardGaussianMap rho) ⁻¹' boundary} = 0 := by
    intro u
    by_cases hu : u ≤ x
    · have hset :
          {v : ℝ |
              (u, v) ∈
                (correlatedStandardGaussianMap rho) ⁻¹' boundary} =
            {((y - rho * u) / scale)} := by
        ext v
        constructor
        · intro hv
          have heq : rho * u + scale * v = y := by
            simpa [boundary, correlatedStandardGaussianMap, scale, hu] using hv.2
          have hv_eq : v = (y - rho * u) / scale := by
            field_simp [hscale_ne] at heq ⊢
            linarith
          simpa [hv_eq]
        · intro hv
          have hv_eq : v = (y - rho * u) / scale := by simpa using hv
          refine ⟨hu, ?_⟩
          calc
            (correlatedStandardGaussianMap rho (u, v)).2 =
                rho * u + scale * v := by
                  simp [correlatedStandardGaussianMap, scale]
            _ = rho * u + scale * ((y - rho * u) / scale) := by
                  rw [hv_eq]
            _ = y := by
                  field_simp [hscale_ne]
                  ring_nf
      rw [hset]
      exact measure_singleton ((y - rho * u) / scale)
    · have hset :
          {v : ℝ |
              (u, v) ∈
                (correlatedStandardGaussianMap rho) ⁻¹' boundary} =
            (∅ : Set ℝ) := by
        ext v
        simp [boundary, correlatedStandardGaussianMap, hu]
      rw [hset]
      simp
  have hmass :
      (standardGaussianMeasure.prod standardGaussianMeasure)
          ((correlatedStandardGaussianMap rho) ⁻¹' boundary) = 0 := by
    rw [Measure.prod_apply hpre_meas]
    change
      (∫⁻ u : ℝ,
          standardGaussianMeasure
            (Prod.mk u ⁻¹'
              ((correlatedStandardGaussianMap rho) ⁻¹' boundary))
          ∂standardGaussianMeasure) = 0
    have hfun :
        (fun u : ℝ =>
          standardGaussianMeasure
            (Prod.mk u ⁻¹'
              ((correlatedStandardGaussianMap rho) ⁻¹' boundary))) =
          fun _ : ℝ => 0 := by
      funext u
      simpa [Set.preimage] using hsection u
    rw [hfun]
    exact lintegral_zero
  rw [correlatedStandardGaussianLaw, measureReal_def,
    Measure.map_apply (measurable_correlatedStandardGaussianMap rho) hboundary_meas,
    hmass]
  simp

/-! ## Independent Gaussian products and canonical variance scaling -/

/--
Encode a real standard deviation as Mathlib's nonnegative variance parameter.

Many EconCS papers state Gaussian primitives by standard deviation `σ`, while
`ProbabilityTheory.gaussianReal` is parameterized by variance.
-/
def gaussianVarianceFromStd (σ : ℝ) : ℝ≥0 :=
  NNReal.mk (σ ^ 2) (sq_nonneg σ)

/--
Positive scaling that sends a variance-`σ^2` Gaussian to the canonical
variance `1 / 2` law used by several random-utility normalizations.
-/
noncomputable def canonicalHalfVarianceScale (σ : ℝ) : ℝ :=
  (Real.sqrt 2 * σ)⁻¹

theorem canonicalHalfVarianceScale_pos {σ : ℝ} (hσ : 0 < σ) :
    0 < canonicalHalfVarianceScale σ := by
  unfold canonicalHalfVarianceScale
  exact inv_pos.mpr (mul_pos (Real.sqrt_pos.2 (by norm_num)) hσ)

theorem canonicalHalfVarianceScale_ne_zero {σ : ℝ} (hσ : 0 < σ) :
    canonicalHalfVarianceScale σ ≠ 0 :=
  ne_of_gt (canonicalHalfVarianceScale_pos hσ)

theorem canonicalHalfVarianceScale_sq_mul_gaussianVarianceFromStd
    {σ : ℝ} (hσ : 0 < σ) :
    NNReal.mk ((canonicalHalfVarianceScale σ) ^ 2)
        (sq_nonneg (canonicalHalfVarianceScale σ)) *
      gaussianVarianceFromStd σ =
        (1 / 2 : ℝ≥0) := by
  ext
  unfold canonicalHalfVarianceScale gaussianVarianceFromStd
  simp only [NNReal.coe_mul, NNReal.coe_mk]
  have hsqrt_sq : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := by
    rw [Real.sq_sqrt (by norm_num)]
  have hsqrt_ne : Real.sqrt (2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hσ_ne : σ ≠ 0 := ne_of_gt hσ
  have hden_ne : Real.sqrt (2 : ℝ) * σ ≠ 0 :=
    mul_ne_zero hsqrt_ne hσ_ne
  field_simp [hden_ne, hσ_ne, hsqrt_ne]
  simp [hsqrt_sq] at *

/--
Scaling a one-dimensional Gaussian with standard deviation `σ` by
`canonicalHalfVarianceScale σ` gives the canonical variance-`1/2` Gaussian.
-/
theorem gaussianReal_map_canonicalHalfVarianceScale
    {σ μ : ℝ} (hσ : 0 < σ) :
    (ProbabilityTheory.gaussianReal μ (gaussianVarianceFromStd σ)).map
        (fun x => canonicalHalfVarianceScale σ * x) =
      ProbabilityTheory.gaussianReal
        (canonicalHalfVarianceScale σ * μ) (1 / 2 : ℝ≥0) := by
  rw [ProbabilityTheory.gaussianReal_map_const_mul]
  rw [canonicalHalfVarianceScale_sq_mul_gaussianVarianceFromStd hσ]

/-- Product law for two independent Gaussians with standard deviation `σ`. -/
noncomputable def independentGaussianPairMeasureWithStd
    (σ xi xj : ℝ) : Measure (ℝ × ℝ) :=
  (ProbabilityTheory.gaussianReal xi (gaussianVarianceFromStd σ)).prod
    (ProbabilityTheory.gaussianReal xj (gaussianVarianceFromStd σ))

/-- Product law for two independent canonical variance-`1/2` Gaussians. -/
noncomputable def independentGaussianPairMeasureHalf
    (xi xj : ℝ) : Measure (ℝ × ℝ) :=
  (ProbabilityTheory.gaussianReal xi (1 / 2 : ℝ≥0)).prod
    (ProbabilityTheory.gaussianReal xj (1 / 2 : ℝ≥0))

/-- Scale both coordinates of an independent Gaussian pair by the same factor. -/
noncomputable def pairCanonicalHalfVarianceScaleMap
    (σ : ℝ) : ℝ × ℝ → ℝ × ℝ :=
  Prod.map
    (fun x => canonicalHalfVarianceScale σ * x)
    (fun x => canonicalHalfVarianceScale σ * x)

/--
Strict event that the first coordinate is below cutoff `a` and beats the
second coordinate.
-/
def pairStrictWinnerBelowEvent (a : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 < a ∧ p.2 < p.1}

/-- Strict event that both coordinates are below cutoff `a`. -/
def pairStrictBothBelowEvent (a : ℝ) : Set (ℝ × ℝ) :=
  Set.Iio a ×ˢ Set.Iio a

theorem pairStrictWinnerBelowEvent_measurable (a : ℝ) :
    MeasurableSet (pairStrictWinnerBelowEvent a) := by
  unfold pairStrictWinnerBelowEvent
  exact (measurableSet_lt measurable_fst measurable_const).inter
    (measurableSet_lt measurable_snd measurable_fst)

theorem pairStrictBothBelowEvent_measurable (a : ℝ) :
    MeasurableSet (pairStrictBothBelowEvent a) := by
  unfold pairStrictBothBelowEvent
  exact measurableSet_Iio.prod measurableSet_Iio

/--
The arbitrary-`σ` product law maps to the canonical variance-`1/2` product law
under coordinatewise canonical scaling.
-/
theorem independentGaussianPairMeasureWithStd_map_canonicalHalfVarianceScale
    {σ xi xj : ℝ} (hσ : 0 < σ) :
    (independentGaussianPairMeasureWithStd σ xi xj).map
        (pairCanonicalHalfVarianceScaleMap σ) =
      independentGaussianPairMeasureHalf
        (canonicalHalfVarianceScale σ * xi)
        (canonicalHalfVarianceScale σ * xj) := by
  unfold independentGaussianPairMeasureWithStd pairCanonicalHalfVarianceScaleMap
    independentGaussianPairMeasureHalf
  rw [← Measure.map_prod_map
    (ProbabilityTheory.gaussianReal xi (gaussianVarianceFromStd σ))
    (ProbabilityTheory.gaussianReal xj (gaussianVarianceFromStd σ))
    (by fun_prop) (by fun_prop)]
  rw [gaussianReal_map_canonicalHalfVarianceScale (σ := σ) (μ := xi) hσ,
    gaussianReal_map_canonicalHalfVarianceScale (σ := σ) (μ := xj) hσ]

theorem pairCanonicalHalfVarianceScaleMap_preimage_strictWinnerBelow
    {σ a : ℝ} (hσ : 0 < σ) :
    (pairCanonicalHalfVarianceScaleMap σ) ⁻¹'
        pairStrictWinnerBelowEvent
          (canonicalHalfVarianceScale σ * a) =
      pairStrictWinnerBelowEvent a := by
  have hc : 0 < canonicalHalfVarianceScale σ :=
    canonicalHalfVarianceScale_pos hσ
  ext p
  simp [pairCanonicalHalfVarianceScaleMap, pairStrictWinnerBelowEvent]
  constructor
  · intro h
    exact ⟨(mul_lt_mul_iff_right₀ hc).mp h.1,
      (mul_lt_mul_iff_right₀ hc).mp h.2⟩
  · intro h
    exact ⟨(mul_lt_mul_iff_right₀ hc).mpr h.1,
      (mul_lt_mul_iff_right₀ hc).mpr h.2⟩

theorem pairCanonicalHalfVarianceScaleMap_preimage_strictBothBelow
    {σ a : ℝ} (hσ : 0 < σ) :
    (pairCanonicalHalfVarianceScaleMap σ) ⁻¹'
        pairStrictBothBelowEvent
          (canonicalHalfVarianceScale σ * a) =
      pairStrictBothBelowEvent a := by
  have hc : 0 < canonicalHalfVarianceScale σ :=
    canonicalHalfVarianceScale_pos hσ
  ext p
  simp [pairCanonicalHalfVarianceScaleMap, pairStrictBothBelowEvent]
  constructor
  · intro h
    exact ⟨(mul_lt_mul_iff_right₀ hc).mp h.1,
      (mul_lt_mul_iff_right₀ hc).mp h.2⟩
  · intro h
    exact ⟨(mul_lt_mul_iff_right₀ hc).mpr h.1,
      (mul_lt_mul_iff_right₀ hc).mpr h.2⟩

theorem independentGaussianPairMeasureWithStd_strictWinnerBelow_eq_scaled
    {σ xi xj a : ℝ} (hσ : 0 < σ) :
    independentGaussianPairMeasureWithStd σ xi xj
        (pairStrictWinnerBelowEvent a) =
      independentGaussianPairMeasureHalf
        (canonicalHalfVarianceScale σ * xi)
        (canonicalHalfVarianceScale σ * xj)
        (pairStrictWinnerBelowEvent
          (canonicalHalfVarianceScale σ * a)) := by
  have hmap :=
    independentGaussianPairMeasureWithStd_map_canonicalHalfVarianceScale
      (σ := σ) (xi := xi) (xj := xj) hσ
  calc
    independentGaussianPairMeasureWithStd σ xi xj
        (pairStrictWinnerBelowEvent a)
        = independentGaussianPairMeasureWithStd σ xi xj
            ((pairCanonicalHalfVarianceScaleMap σ) ⁻¹'
              pairStrictWinnerBelowEvent
                (canonicalHalfVarianceScale σ * a)) := by
          rw [pairCanonicalHalfVarianceScaleMap_preimage_strictWinnerBelow hσ]
    _ = (independentGaussianPairMeasureWithStd σ xi xj).map
          (pairCanonicalHalfVarianceScaleMap σ)
          (pairStrictWinnerBelowEvent
            (canonicalHalfVarianceScale σ * a)) := by
          exact (Measure.map_apply
            (μ := independentGaussianPairMeasureWithStd σ xi xj)
            (f := pairCanonicalHalfVarianceScaleMap σ)
            (by unfold pairCanonicalHalfVarianceScaleMap; fun_prop)
            (pairStrictWinnerBelowEvent_measurable
              (canonicalHalfVarianceScale σ * a))).symm
    _ = independentGaussianPairMeasureHalf
          (canonicalHalfVarianceScale σ * xi)
          (canonicalHalfVarianceScale σ * xj)
          (pairStrictWinnerBelowEvent
            (canonicalHalfVarianceScale σ * a)) := by
          rw [hmap]

theorem independentGaussianPairMeasureWithStd_strictBothBelow_eq_scaled
    {σ xi xj a : ℝ} (hσ : 0 < σ) :
    independentGaussianPairMeasureWithStd σ xi xj
        (pairStrictBothBelowEvent a) =
      independentGaussianPairMeasureHalf
        (canonicalHalfVarianceScale σ * xi)
        (canonicalHalfVarianceScale σ * xj)
        (pairStrictBothBelowEvent
          (canonicalHalfVarianceScale σ * a)) := by
  have hmap :=
    independentGaussianPairMeasureWithStd_map_canonicalHalfVarianceScale
      (σ := σ) (xi := xi) (xj := xj) hσ
  calc
    independentGaussianPairMeasureWithStd σ xi xj
        (pairStrictBothBelowEvent a)
        = independentGaussianPairMeasureWithStd σ xi xj
            ((pairCanonicalHalfVarianceScaleMap σ) ⁻¹'
              pairStrictBothBelowEvent
                (canonicalHalfVarianceScale σ * a)) := by
          rw [pairCanonicalHalfVarianceScaleMap_preimage_strictBothBelow hσ]
    _ = (independentGaussianPairMeasureWithStd σ xi xj).map
          (pairCanonicalHalfVarianceScaleMap σ)
          (pairStrictBothBelowEvent
            (canonicalHalfVarianceScale σ * a)) := by
          exact (Measure.map_apply
            (μ := independentGaussianPairMeasureWithStd σ xi xj)
            (f := pairCanonicalHalfVarianceScaleMap σ)
            (by unfold pairCanonicalHalfVarianceScaleMap; fun_prop)
            (pairStrictBothBelowEvent_measurable
              (canonicalHalfVarianceScale σ * a))).symm
    _ = independentGaussianPairMeasureHalf
          (canonicalHalfVarianceScale σ * xi)
          (canonicalHalfVarianceScale σ * xj)
          (pairStrictBothBelowEvent
            (canonicalHalfVarianceScale σ * a)) := by
          rw [hmap]

/--
Strict conditional ratio
`Pr[X_i < a and X_j < X_i] / Pr[X_i < a and X_j < a]` for independent
canonical variance-`1/2` Gaussians.
-/
noncomputable def independentGaussianStrictConditionalWinnerRatioHalf
    (xi xj a : ℝ) : ℝ :=
  (independentGaussianPairMeasureHalf xi xj
      (pairStrictWinnerBelowEvent a)).toReal /
    (independentGaussianPairMeasureHalf xi xj
      (pairStrictBothBelowEvent a)).toReal

/--
Strict conditional winner ratio for independent Gaussians with standard
deviation `σ`.
-/
noncomputable def independentGaussianStrictConditionalWinnerRatioWithStd
    (σ xi xj a : ℝ) : ℝ :=
  (independentGaussianPairMeasureWithStd σ xi xj
      (pairStrictWinnerBelowEvent a)).toReal /
    (independentGaussianPairMeasureWithStd σ xi xj
      (pairStrictBothBelowEvent a)).toReal

/--
The arbitrary-`σ` strict conditional ratio is the canonical variance-`1/2`
ratio after positive scaling of scores, means, and cutoff.
-/
theorem independentGaussianStrictConditionalWinnerRatioWithStd_eq_scaled
    {σ xi xj a : ℝ} (hσ : 0 < σ) :
    independentGaussianStrictConditionalWinnerRatioWithStd σ xi xj a =
      independentGaussianStrictConditionalWinnerRatioHalf
        (canonicalHalfVarianceScale σ * xi)
        (canonicalHalfVarianceScale σ * xj)
        (canonicalHalfVarianceScale σ * a) := by
  unfold independentGaussianStrictConditionalWinnerRatioWithStd
    independentGaussianStrictConditionalWinnerRatioHalf
  rw [independentGaussianPairMeasureWithStd_strictWinnerBelow_eq_scaled hσ,
    independentGaussianPairMeasureWithStd_strictBothBelow_eq_scaled hσ]

end

end Probability
end AppliedModelingLib

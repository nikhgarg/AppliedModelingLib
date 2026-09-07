import AppliedModelingLib.Foundations.Probability.GaussianSignalKernelRCD
import LG21TestOptionalPolicies.ContinuousGaussianFullProfileSourceLaw
import LG21TestOptionalPolicies.ContinuousGaussianTwoFeatureRCD

/-!
# Finite sequential Gaussian posterior arithmetic for LG21

The literal LG21 source law has one latent Gaussian skill and finitely many
independent additive Gaussian feature noises.  The measure-theoretic
full-profile transport is kept separate from this file.  Here we prove the
finite algebraic induction which identifies the posterior parameters once that
transport presents the observations one at a time.

The general peel and parameter declarations introduce no conditional-law,
posterior, or source-process hypothesis: they are identities in the positive
Gaussian variances and observed real values.  The final two-coordinate bridge
explicitly invokes the already proved literal source-RCD theorem.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory BigOperators

/-- The indices left after exposing one coordinate of a finite noise family. -/
abbrev LG21RemainingNoiseIndex (Index : Type*) (chosen : Index) :=
  {index : Index // index ≠ chosen}

/-- The literal product law of every noise coordinate except one chosen
coordinate. -/
def lg21GaussianNoiseWithout
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (noiseVariance : Index → ℝ≥0) (chosen : Index) :
    Measure (LG21RemainingNoiseIndex Index chosen → ℝ) :=
  Measure.pi (fun index => gaussianReal 0 (noiseVariance index.1))

/-- A measurable coordinate split exposing one chosen coordinate of a finite
product noise vector. -/
def lg21GaussianNoisePeel
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (chosen : Index) :
    (Index → ℝ) ≃ᵐ (LG21RemainingNoiseIndex Index chosen → ℝ) × ℝ :=
  (MeasurableEquiv.piCongrLeft (fun _ : Index => ℝ)
      (Equiv.optionSubtypeNe chosen)).symm.trans
    (MeasurableEquiv.piOptionEquivProd
      (fun _ : Option (LG21RemainingNoiseIndex Index chosen) => ℝ))

/-- The literal finite product law can expose any one noise coordinate.  This
is the source-law peel needed by the eventual finite-profile RCD induction;
it does not introduce a posterior or a conditional-law hypothesis. -/
theorem lg21GaussianPiNoiseLaw_map_peel_eq
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (noiseVariance : Index → ℝ≥0) (chosen : Index) :
    (Measure.pi (fun index => gaussianReal 0 (noiseVariance index))).map
        (lg21GaussianNoisePeel chosen) =
      (lg21GaussianNoiseWithout noiseVariance chosen).prod
        (gaussianReal 0 (noiseVariance chosen)) := by
  let Remaining := LG21RemainingNoiseIndex Index chosen
  let e : Option Remaining ≃ Index := Equiv.optionSubtypeNe chosen
  let optionLaw : Option Remaining → Measure ℝ :=
    fun index => gaussianReal 0 (noiseVariance (e index))
  let ePi : (Option Remaining → ℝ) ≃ᵐ (Index → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : Index => ℝ) e
  let optionSplit : (Option Remaining → ℝ) ≃ᵐ (Remaining → ℝ) × ℝ :=
    MeasurableEquiv.piOptionEquivProd (fun _ : Option Remaining => ℝ)
  let split : (Index → ℝ) ≃ᵐ (Remaining → ℝ) × ℝ :=
    ePi.symm.trans optionSplit
  have hpi : (Measure.pi optionLaw).map ePi =
      Measure.pi (fun index => gaussianReal 0 (noiseVariance index)) := by
    simpa [optionLaw, ePi, e] using
      (Measure.pi_map_piCongrLeft e
        (fun index : Index => gaussianReal 0 (noiseVariance index)))
  have hoption :
      ((lg21GaussianNoiseWithout noiseVariance chosen).prod
        (gaussianReal 0 (noiseVariance chosen))).map optionSplit.symm =
        Measure.pi optionLaw := by
    simpa [lg21GaussianNoiseWithout, optionLaw, e] using
      (Measure.pi_map_piOptionEquivProd optionLaw)
  change (Measure.pi (fun index => gaussianReal 0 (noiseVariance index))).map split =
    (lg21GaussianNoiseWithout noiseVariance chosen).prod
      (gaussianReal 0 (noiseVariance chosen))
  apply (split.map_apply_eq_iff_map_symm_apply_eq).2
  calc
    Measure.pi (fun index => gaussianReal 0 (noiseVariance index)) =
        (Measure.pi optionLaw).map ePi := hpi.symm
    _ = (((lg21GaussianNoiseWithout noiseVariance chosen).prod
        (gaussianReal 0 (noiseVariance chosen))).map optionSplit.symm).map ePi := by
          rw [hoption]
    _ = ((lg21GaussianNoiseWithout noiseVariance chosen).prod
        (gaussianReal 0 (noiseVariance chosen))).map split.symm := by
          rw [Measure.map_map ePi.measurable optionSplit.symm.measurable]
          rfl

/-- Instantiation of the generic peel for the non-test noise profile in the
literal LG21 source population. -/
theorem lg21ContinuousGaussianNonTestNoiseLaw_map_peel_eq
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    (baseFeature : LG21NonTestFeature Feature testFeature) :
    (lg21ContinuousGaussianNonTestNoiseLaw M testFeature).map
        (lg21GaussianNoisePeel baseFeature) =
      (lg21GaussianNoiseWithout
        (fun nonTest : LG21NonTestFeature Feature testFeature =>
          M.noiseVariance nonTest.1)
        baseFeature).prod
        (gaussianReal 0 (M.noiseVariance baseFeature.1)) := by
  exact lg21GaussianPiNoiseLaw_map_peel_eq
    (fun nonTest : LG21NonTestFeature Feature testFeature =>
      M.noiseVariance nonTest.1)
    baseFeature

/-- The variance after one additive Gaussian observation. -/
def lg21GaussianPosteriorVariance (priorVariance noiseVariance : ℝ) : ℝ :=
  priorVariance * noiseVariance / (priorVariance + noiseVariance)

/-- The mean after one additive Gaussian observation. -/
def lg21GaussianPosteriorMean
    (priorMean priorVariance observation noiseVariance : ℝ) : ℝ :=
  priorVariance / (priorVariance + noiseVariance) * observation +
    noiseVariance / (priorVariance + noiseVariance) * priorMean

/-- Starting from a Gaussian prior, update its mean and variance successively
for a finite list of `(observation, noiseVariance)` pairs.  The recursive
orientation is chosen so the head is the final update; the closed-form
theorems below reduce ordering questions to finite sums.
-/
def lg21GaussianSequentialPosteriorParameters
    (priorMean priorVariance : ℝ) : List (ℝ × ℝ) → ℝ × ℝ
  | [] => (priorMean, priorVariance)
  | observation :: remaining =>
      let previous :=
        lg21GaussianSequentialPosteriorParameters priorMean priorVariance remaining
      (lg21GaussianPosteriorMean previous.1 previous.2 observation.1 observation.2,
        lg21GaussianPosteriorVariance previous.2 observation.2)

/-- The posterior mean after a specified first signal, expressed through the
same sequential parameter construction used for arbitrary finite profiles. -/
def lg21GaussianOneBasePosteriorMean
    (priorMean priorVariance baseNoiseVariance : ℝ) : ℝ → ℝ :=
  fun base =>
    (lg21GaussianSequentialPosteriorParameters priorMean priorVariance
      [(base, baseNoiseVariance)]).1

/-- The variance after a specified first signal.  It is written through a
dummy observation because Gaussian posterior variance is data-independent. -/
def lg21GaussianOneBasePosteriorVariance
    (priorMean priorVariance baseNoiseVariance : ℝ) : ℝ :=
  (lg21GaussianSequentialPosteriorParameters priorMean priorVariance
    [(0, baseNoiseVariance)]).2

/-- The sequential first-signal posterior mean is an affine measurable
function of the observed first signal. -/
theorem measurable_lg21GaussianOneBasePosteriorMean
    (priorMean priorVariance baseNoiseVariance : ℝ) :
    Measurable
      (lg21GaussianOneBasePosteriorMean
        priorMean priorVariance baseNoiseVariance) := by
  change Measurable fun base : ℝ =>
    priorVariance / (priorVariance + baseNoiseVariance) * base +
      baseNoiseVariance / (priorVariance + baseNoiseVariance) * priorMean
  fun_prop

/-- The sequential two-signal parameters expand to the two nested Gaussian
updates used by the existing actual source-RCD theorem. -/
theorem lg21GaussianTwoSignalParameters_eq_sequential
    (priorMean priorVariance base baseNoiseVariance score scoreNoiseVariance : ℝ) :
    lg21GaussianSequentialPosteriorParameters priorMean priorVariance
      [(score, scoreNoiseVariance), (base, baseNoiseVariance)] =
      (lg21GaussianPosteriorMean
          (lg21GaussianPosteriorMean priorMean priorVariance base baseNoiseVariance)
          (lg21GaussianPosteriorVariance priorVariance baseNoiseVariance)
          score scoreNoiseVariance,
        lg21GaussianPosteriorVariance
          (lg21GaussianPosteriorVariance priorVariance baseNoiseVariance)
          scoreNoiseVariance) := by
  rfl

/-- The sequential first-signal parameters are definitionally the standard
one-step Gaussian posterior parameters. -/
theorem lg21GaussianOneBaseParameters_eq_sequential
    (priorMean priorVariance base baseNoiseVariance : ℝ) :
    lg21GaussianSequentialPosteriorParameters priorMean priorVariance
      [(base, baseNoiseVariance)] =
      (lg21GaussianPosteriorMean priorMean priorVariance base baseNoiseVariance,
        lg21GaussianPosteriorVariance priorVariance baseNoiseVariance) := by
  rfl

/-- A single Gaussian update preserves strict positivity of variance. -/
theorem lg21GaussianPosteriorVariance_pos
    {priorVariance noiseVariance : ℝ}
    (hpriorVariance : 0 < priorVariance) (hnoiseVariance : 0 < noiseVariance) :
    0 < lg21GaussianPosteriorVariance priorVariance noiseVariance := by
  unfold lg21GaussianPosteriorVariance
  exact div_pos (mul_pos hpriorVariance hnoiseVariance)
    (add_pos hpriorVariance hnoiseVariance)

/-- One Gaussian update adds the new signal precision to the old precision. -/
theorem lg21GaussianPosteriorVariance_inv
    {priorVariance noiseVariance : ℝ}
    (hpriorVariance : 0 < priorVariance) (hnoiseVariance : 0 < noiseVariance) :
    (lg21GaussianPosteriorVariance priorVariance noiseVariance)⁻¹ =
      priorVariance⁻¹ + noiseVariance⁻¹ := by
  unfold lg21GaussianPosteriorVariance
  field_simp [ne_of_gt hpriorVariance, ne_of_gt hnoiseVariance,
    ne_of_gt (add_pos hpriorVariance hnoiseVariance)]
  ring

/-- One Gaussian update adds the new observation's precision-weighted value to
the old natural mean parameter. -/
theorem lg21GaussianPosteriorMean_div_variance
    {priorMean priorVariance observation noiseVariance : ℝ}
    (hpriorVariance : 0 < priorVariance) (hnoiseVariance : 0 < noiseVariance) :
    lg21GaussianPosteriorMean priorMean priorVariance observation noiseVariance /
        lg21GaussianPosteriorVariance priorVariance noiseVariance =
      priorMean / priorVariance + observation / noiseVariance := by
  unfold lg21GaussianPosteriorMean lg21GaussianPosteriorVariance
  field_simp [ne_of_gt hpriorVariance, ne_of_gt hnoiseVariance,
    ne_of_gt (add_pos hpriorVariance hnoiseVariance)]
  ring

/-- Every variance in a finite sequence of positive-noise Gaussian updates is
strictly positive. -/
theorem lg21GaussianSequentialPosteriorVariance_pos
    (priorMean priorVariance : ℝ) (observations : List (ℝ × ℝ))
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : ∀ observation ∈ observations, 0 < observation.2) :
    0 < (lg21GaussianSequentialPosteriorParameters
      priorMean priorVariance observations).2 := by
  induction observations with
  | nil =>
      simpa [lg21GaussianSequentialPosteriorParameters]
  | cons observation remaining ih =>
      have hnoise : 0 < observation.2 := hnoiseVariance observation (by simp)
      have hremaining : ∀ next ∈ remaining, 0 < next.2 := by
        intro next hnext
        exact hnoiseVariance next (by simp [hnext])
      simp only [lg21GaussianSequentialPosteriorParameters]
      exact lg21GaussianPosteriorVariance_pos
        (ih hremaining) hnoise

/-- The posterior precision after any finite sequence is the prior precision
plus the sum of all signal precisions. -/
theorem lg21GaussianSequentialPosteriorVariance_inv
    (priorMean priorVariance : ℝ) (observations : List (ℝ × ℝ))
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : ∀ observation ∈ observations, 0 < observation.2) :
    (lg21GaussianSequentialPosteriorParameters
      priorMean priorVariance observations).2⁻¹ =
      priorVariance⁻¹ + (observations.map fun observation => observation.2⁻¹).sum := by
  induction observations with
  | nil =>
      simp [lg21GaussianSequentialPosteriorParameters]
  | cons observation remaining ih =>
      have hnoise : 0 < observation.2 := hnoiseVariance observation (by simp)
      have hremaining : ∀ next ∈ remaining, 0 < next.2 := by
        intro next hnext
        exact hnoiseVariance next (by simp [hnext])
      have hpreviousPos : 0 <
          (lg21GaussianSequentialPosteriorParameters
            priorMean priorVariance remaining).2 :=
        lg21GaussianSequentialPosteriorVariance_pos
          priorMean priorVariance remaining hpriorVariance hremaining
      rw [show (lg21GaussianSequentialPosteriorParameters
          priorMean priorVariance (observation :: remaining)).2 =
          lg21GaussianPosteriorVariance
            (lg21GaussianSequentialPosteriorParameters
              priorMean priorVariance remaining).2 observation.2 by rfl]
      rw [lg21GaussianPosteriorVariance_inv hpreviousPos hnoise, ih hremaining]
      simp only [List.map_cons, List.sum_cons]
      ring

/-- The posterior natural mean parameter after any finite sequence is the
prior natural mean parameter plus the sum of precision-weighted observations.
-/
theorem lg21GaussianSequentialPosteriorMean_div_variance
    (priorMean priorVariance : ℝ) (observations : List (ℝ × ℝ))
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : ∀ observation ∈ observations, 0 < observation.2) :
    (lg21GaussianSequentialPosteriorParameters
      priorMean priorVariance observations).1 /
        (lg21GaussianSequentialPosteriorParameters
          priorMean priorVariance observations).2 =
      priorMean / priorVariance +
        (observations.map fun observation => observation.1 / observation.2).sum := by
  induction observations with
  | nil =>
      simp [lg21GaussianSequentialPosteriorParameters]
  | cons observation remaining ih =>
      have hnoise : 0 < observation.2 := hnoiseVariance observation (by simp)
      have hremaining : ∀ next ∈ remaining, 0 < next.2 := by
        intro next hnext
        exact hnoiseVariance next (by simp [hnext])
      have hpreviousPos : 0 <
          (lg21GaussianSequentialPosteriorParameters
            priorMean priorVariance remaining).2 :=
        lg21GaussianSequentialPosteriorVariance_pos
          priorMean priorVariance remaining hpriorVariance hremaining
      rw [show (lg21GaussianSequentialPosteriorParameters
          priorMean priorVariance (observation :: remaining)).1 =
          lg21GaussianPosteriorMean
            (lg21GaussianSequentialPosteriorParameters
              priorMean priorVariance remaining).1
            (lg21GaussianSequentialPosteriorParameters
              priorMean priorVariance remaining).2
            observation.1 observation.2 by rfl]
      rw [show (lg21GaussianSequentialPosteriorParameters
          priorMean priorVariance (observation :: remaining)).2 =
          lg21GaussianPosteriorVariance
            (lg21GaussianSequentialPosteriorParameters
              priorMean priorVariance remaining).2 observation.2 by rfl]
      rw [lg21GaussianPosteriorMean_div_variance hpreviousPos hnoise,
        ih hremaining]
      simp only [List.map_cons, List.sum_cons]
      ring

/-- The finite sequential posterior variance has the usual reciprocal of the
sum-of-precisions form. -/
theorem lg21GaussianSequentialPosteriorVariance_eq_precision_inverse
    (priorMean priorVariance : ℝ) (observations : List (ℝ × ℝ))
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : ∀ observation ∈ observations, 0 < observation.2) :
    (lg21GaussianSequentialPosteriorParameters
      priorMean priorVariance observations).2 =
      (priorVariance⁻¹ +
        (observations.map fun observation => observation.2⁻¹).sum)⁻¹ := by
  calc
    (lg21GaussianSequentialPosteriorParameters
      priorMean priorVariance observations).2 =
        ((lg21GaussianSequentialPosteriorParameters
          priorMean priorVariance observations).2⁻¹)⁻¹ := by
            rw [inv_inv]
    _ = (priorVariance⁻¹ +
        (observations.map fun observation => observation.2⁻¹).sum)⁻¹ := by
          rw [lg21GaussianSequentialPosteriorVariance_inv
            priorMean priorVariance observations hpriorVariance hnoiseVariance]

/-- The finite sequential posterior mean is its variance times the prior
natural mean plus all precision-weighted observations. -/
theorem lg21GaussianSequentialPosteriorMean_eq_variance_mul_natural
    (priorMean priorVariance : ℝ) (observations : List (ℝ × ℝ))
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : ∀ observation ∈ observations, 0 < observation.2) :
    (lg21GaussianSequentialPosteriorParameters
      priorMean priorVariance observations).1 =
      (lg21GaussianSequentialPosteriorParameters
        priorMean priorVariance observations).2 *
        (priorMean / priorVariance +
          (observations.map fun observation => observation.1 / observation.2).sum) := by
  let parameters :=
    lg21GaussianSequentialPosteriorParameters priorMean priorVariance observations
  have hvariancePos : 0 < parameters.2 := by
    exact lg21GaussianSequentialPosteriorVariance_pos
      priorMean priorVariance observations hpriorVariance hnoiseVariance
  have hnatural : parameters.1 / parameters.2 =
      priorMean / priorVariance +
        (observations.map fun observation => observation.1 / observation.2).sum := by
    exact lg21GaussianSequentialPosteriorMean_div_variance
      priorMean priorVariance observations hpriorVariance hnoiseVariance
  have hmul : parameters.1 =
      (priorMean / priorVariance +
        (observations.map fun observation => observation.1 / observation.2).sum) *
        parameters.2 :=
    (div_eq_iff (ne_of_gt hvariancePos)).mp hnatural
  change parameters.1 = parameters.2 *
    (priorMean / priorVariance +
      (observations.map fun observation => observation.1 / observation.2).sum)
  rw [hmul]
  ring

/-- Closed-form finite posterior mean.  This is the algebraic target for the
remaining product-law-to-sequential-kernel transport in the LG21 full-profile
source model. -/
theorem lg21GaussianSequentialPosteriorMean_eq_precision_weighted
    (priorMean priorVariance : ℝ) (observations : List (ℝ × ℝ))
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : ∀ observation ∈ observations, 0 < observation.2) :
    (lg21GaussianSequentialPosteriorParameters
      priorMean priorVariance observations).1 =
      (priorVariance⁻¹ +
        (observations.map fun observation => observation.2⁻¹).sum)⁻¹ *
        (priorMean / priorVariance +
          (observations.map fun observation => observation.1 / observation.2).sum) := by
  rw [lg21GaussianSequentialPosteriorMean_eq_variance_mul_natural
    priorMean priorVariance observations hpriorVariance hnoiseVariance,
    lg21GaussianSequentialPosteriorVariance_eq_precision_inverse
      priorMean priorVariance observations hpriorVariance hnoiseVariance]

/-- The existing literal two-coordinate LG21 source-RCD theorem expressed with
the reusable sequential first-signal parameters.  This is a proved source-law
base case for the eventual finite-profile induction, not a supplied posterior
assumption. -/
theorem lg21ContinuousGaussianAccessPopulation_condDistrib_skill_given_single_base_score_sequential_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (baseFeature testFeature : Feature) (hne : baseFeature ≠ testFeature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hbaseNoiseVariance : 0 < (M.noiseVariance baseFeature : ℝ))
    (hscoreNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ)) :
    let law := lg21ContinuousGaussianAccessPopulationLaw M
    let posteriorMean := lg21GaussianOneBasePosteriorMean M.priorMean
      (M.priorVariance : ℝ) (M.noiseVariance baseFeature : ℝ)
    let posteriorVariance := lg21GaussianOneBasePosteriorVariance M.priorMean
      (M.priorVariance : ℝ) (M.noiseVariance baseFeature : ℝ)
    let posteriorKernel := AppliedModelingLib.Probability.gaussianSignalPosteriorBaseKernel
      posteriorMean (by
        simpa [posteriorMean] using
          (measurable_lg21GaussianOneBasePosteriorMean M.priorMean
            (M.priorVariance : ℝ) (M.noiseVariance baseFeature : ℝ))) posteriorVariance
      (M.noiseVariance testFeature : ℝ)
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
  simpa [lg21GaussianOneBasePosteriorMean,
    lg21GaussianOneBasePosteriorVariance,
    lg21GaussianSequentialPosteriorParameters,
    lg21GaussianPosteriorMean,
    lg21GaussianPosteriorVariance] using
    (lg21ContinuousGaussianAccessPopulation_condDistrib_skill_given_single_base_score_ae
      M haccess baseFeature testFeature hne hpriorVariance hbaseNoiseVariance
      hscoreNoiseVariance)

/-- Evaluating the two-signal source posterior kernel gives exactly the
sequential finite-parameter Gaussian. -/
theorem lg21GaussianTwoSignalSequentialPosteriorKernel_apply
    (priorMean priorVariance baseNoiseVariance scoreNoiseVariance base score : ℝ) :
    AppliedModelingLib.Probability.gaussianSignalPosteriorBaseKernel
      (lg21GaussianOneBasePosteriorMean priorMean priorVariance baseNoiseVariance)
      (measurable_lg21GaussianOneBasePosteriorMean
        priorMean priorVariance baseNoiseVariance)
      (lg21GaussianOneBasePosteriorVariance
        priorMean priorVariance baseNoiseVariance)
      scoreNoiseVariance
      (base, score) =
      gaussianReal
        (lg21GaussianSequentialPosteriorParameters priorMean priorVariance
          [(score, scoreNoiseVariance), (base, baseNoiseVariance)]).1
        ((lg21GaussianSequentialPosteriorParameters priorMean priorVariance
          [(0, scoreNoiseVariance), (0, baseNoiseVariance)]).2).toNNReal := by
  rw [AppliedModelingLib.Probability.gaussianSignalPosteriorBaseKernel_apply]
  rfl

end

end LG21TestOptionalPolicies
